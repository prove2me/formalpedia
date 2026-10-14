-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3672
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:20:44.87698+00:00
-- url     : https://prove2.me/submissions/5c281eea-9a24-4955-bf44-7406c5be6c16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 660251798 ≤ n < 660431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 660253048 1250 660251798 660251819
    0x6040b0f0409060b0706140601080a0230010518160806040e0a0c03120201020720010e120114010e0f060d0206040b1201050a052403041a0103061a0603070219140304 72
    0x42170241c0301242090103483d82c0400701221148185416103c0540c03d49131150800c000390006c126080d600140b05035000da0030300503206920110204003003a840d140d8148001d1090184084940040c800098010b008150340c01e404111081c42d407628040e1040d940d100000380242600d0380ca61001801941402400d00c2019041c0809913405211102c50460100d48102d080703110700c0c1c0d4090001024402004150040f240c800018003a0502d04016103194103c00920090303d43c02411901c1d070740d0381030049041d405044003140107000d5409004860315290041d40010900144254807491084961408651f104001d50300039200d01c50200d0740f00c02c504821800442c03828003440e40325030740c008070010b69031405d9030303101d08040c0c00c001c82a0600d0310503090402040d0000346c402c60340c02145420075441500101c0469000b58081d800206490710a1511007200380800c00c0c91350301880c020010005840d80008000744600710300d8400303008a650034180914100d2140800c428140000200000c18948a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 660254298 1250 660253048 660253057
    0x2f0a02090a0207020103150b16061b09060e0d0f0809010c08130e0105031606080703020702030109080d050f040c27021801020d0201020a0e0607020310290f06040b0f0409060b 76
    0x1b03803002c000419051420710755042c464403882d0031060742045015030000500700f0b80c0324a944942d0b0086190a1001130300040c2240e1080d8440008920b64030801c01164024208200c070341c41911903058150868a40c15010005064040e041c1c04000580d41e0190340300d49402054560050612074903007070300d2122140038a50510802c03660b60164400411030b80303004030380c00c850b009601a0801c1d00c0c2d45000c1c0d059640000c000c3c050814964248070f00c50140c0c07400c2c0140b0403c0fa215400c00f958070541070801c4d01c100c40003e0b20400d4071801d02c1c42008001038460710440103a41c043d2200e85000001d10125070a65090380007414015800480c10410250f140c0a203216405030036000d0b90751711894100200d080b801284038160000d900c02c0104001401d2400050112a001400f03031040200744000c0c1601b686d5504c0024400014a484000580c110248200f42d004604540964180ea07200e0000f81e100d000c3c42c01509803a0381c00149002804c1100c1b01200c00030294020184000c5548280c5003a03140c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 660255548 1250 660254298 660254303
    0x1201060f0503010606082401020a140a120507120302030603030d0f020a09150e150c060421020a0213020d020919060206060a060f12110c0705040b012f0a02090a0207 72
    0xf01070011401d24000c20409228500400c440310311f40303000b40d020780c1e01c07603848454441c1035005a207142404541100690924240c0650040182e2205032800e682c120314815109401c00c5428080040041e80b400c0401c840001130346000758882d21480c0010b4214499034480030040d51800125490702900c5401400070030b100c070780360035000f20380e1129040301000010381480c00040c002e20202c0001c2c84d05480383c074082540b0104907801d03e061561280d141000546003034a9045002a051107056a444603555031012288084c1c540e20456030301290303001c030b4241d00706642c041d0046003078001200e40364141d600040e0014282c02c8116005622540d82056901920006000d4071001405c1c80c00c02640500844072a6540c21480d00030507101160f0807840300c3c035048825074480700c0d076000440100000c0c00c5011140310140042a261404010480b08113070102e505000b5000010114494560491401c401c1e0745180007214194034075080341003d220b8000258400200410711030000d00c0c59015011240c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 660256798 1250 660255548 660255551
    0x402091b0c0c090a020f040306090f080c06040210020d120543030603020f0409140318090a09030f11070504020a031d070f050409030e0306090a0221060103020f1201060f050301 77
    0x200c501d44ca0800b40d04c103085070724844040c10001003001602d561b000c50812170260000314400907007640c80300510392041d002c05071a988150203000c1549014100509113600382d0004241c4110314030342c05020702e100d900c0c05000080d500c200044140c04c1e41807134504e0349040101c030f560001000d14041c0e40710314004141441d05158034802401194064410b040c26660000c2c4050b544016000801000d03100500007295034200c04081c00ca0495001c02c00390080c0c2c000d6140d01c000780d040b41c1040c884842da00610a4502906151640c00400d07001510b10241e402185082c10054105041035490300b0b1596100580040c8000f544010090345a07010620f40d01c50720500703c0308075005921241e65121540100050340c105254108294909688003901d55031103070500c0701c03c1503400e0000030b0501004603004200340d000071442c001103181c01120103c00e560158803c0e04060120ba120560355841400000c0c092148020820f110740e403102d01040c0140c96a100910805884031090851048079114181c02507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 660258048 1250 660256798 660256801
    0x42c030c0f0109050c0906031e060712050c03040f02061303050709050612070b090a030803040b0405150403020c01051e0c070305071208092e030c090f0e0402091b0c0c09 74
    0x4107040c019220602d400c10020300216403900c4c00c05c503d044020382910382c18400e00320f40541201c00c1030140441011980e01500452514120191107440842e1a40e03052625180402c45d941c80d0380340550740c000f0f0b0407640d008101400b61012881c6442000e0390300d8411000d134240003081140000c3c5000c15107844a01c1441691115000c2c4103001954a40406054110030021310403a60b84101400030b042004005000c015aaa00d41a11310741c82550151421840700081200340281000703a4001655601c0f10240c5515054800a4403442d41202e02810814006040c8038800c0780c803210240305804400c40160740754240c0388669900c0e9410b100885003402045400035038a5140344121440613001070501d0b1070f048a0204103d8203840301e816040c3c83d0762422003901c1844210480130b200c44003179518001841d520361440030704000e080f82d00c1030700c1000304500d05208191407960110382040d415903144036030340c44007035600b1008030222089000384080441c01160f50100061a41c0060809941d0145076 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 660259298 1250 660258048 660258073
    0xc02030403020909062a0d0c1b11030c06040e0a0b0102032a0f010218192403050c040b18031011070209090d0e011b02190509090615042c030c 62
    0x5100c151b9505041c1d00500150f510010607411080c01110603142c04050701d10049008031121403c80b02c150f80c00b10322041d0b01c0030503040800400554190442e00c003821f1a251250050032440010b00040246c0d0715140d840c00c448e402001a03c4046240c843d0700020300d40d001e103941c0c09103c08418000305c20300c40e100c03030201030307200600c02c82e01142d84c0c06c6400034900b904070083c004080c1314a1030a40302c190040300002200b041d0901444d0905848404031021b80c2e9003400000e064410103440954031020410080002007001401c40d0400e2181c101c40440d16451031000908001228148055007400c2c0554030b06044003603401004803d2088854400301d480c0c9082c01030b52603441c034464401050006050304145d60041d5201d0781c0602045484803007280c910350108062509084c48042c503001e0142081c0b05074501501c0059104040c10000d100919100300c8003400040013084041c015507407107548451030919128140b0292481803895184144c0303c0070510344d40e9000141c0e2611a0040007103071100d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 660260548 1250 660259298 660259351
    0xf151b0803010b0c150609062407030e0a080f10110c06010303080109110309070605030405101407171b0f2503030b0d0f0312020c0d02010906061a07060c0203040302090906 75
    0x521b1000d862100300d0340c0c0d580244100e0204100d03180d601c8483c0030f21003c240030600300c02041c171075119a49884100008605000200c80260440c1c0ad4030b4000000b05a200d00c400149840d51300d041d13210209429071121013080c00c0e44201c5003010340310b029010020092642000c909070490791030702020804846071b5091141c0030f00040d180c40c500e540010b94100142441180596000350207901901d4902c03c0b054a03100844a50b00004200010000100301c03486030011a4268500c8540b12401070500d4205003184c820525401000b0100c0408a0708443c0750000c207065516064002c01c00c0b400c000701c2200d40020b1000c510701d0403400a400c000c80500c40c0d04101c000c1c50310150b40702d0024030841d200c0ba032f010355030880b540d500022245e60910030070813040400c10801ca1080120740000031001c005003028400d540968200015403405140703001d030b5138130341d1604444070507410910026030702038510301c00c80c00c52041e47d001075400140e450034401540c50200e800d90141700d40120050007045112135810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 660261798 1250 660260548 660260551
    0x1f02060106020c060f18032a0306010b03072708070801061809080a0c051612060507180b091206010618060e1008040303092a0f151b0803010b0c15 64
    0x80d5414080c0440c2c2c5484c14090000782c0003040040540d01402448d40ba8102c00480c94141a00d070031489550101d010b060901c0b189015003a0030402c5459840c000e00003401c5411182503410085110a1301418031803030558034000503007050001e6408080e59002183d005c0d01a6004440c0d461600152103c400c1d00148100340005900030007050600a0f00b000036a40750b0f1001a00350303a180200325040c0c28440902588402415500c02002130700c2e02c09082c0310007202d0b8020b01d05da0a1040e000c034040203880c8100490022501000804d0341e4036110030317010540d201c0200051380f2040c481d000011418903000100d544654000074040b054082d55403408540000d210788034135070840c15440c03020f062544a205400d51040c000d0401044005980c1e9550400c0d800d0381945011104803030060740e1100c00b0403111040200302c50402c0c40e005070f0800c21001c406003c15041202440400893b40d80d0204100118500d015003108032103440307680d1045401c40307907480041030075101d000d251600c081d120b1020151030b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 660263048 1250 660261798 660261817
    0xf08060f0d0b071211210a0209090403030c0e0102010510050d020301020f130302030d210b040e060a05180a08030109020309120706090c09090f081b160f2702091f02060106020c06 78
    0x1c80006c00704d200443c20100c405400c070740503290200008011500e6400486024134840e603400628444407010051940d80c407000c080f41164140000c1c07091001c4030503002c40640d2803c58079000c61310748a00c0003900a100e05820300f20310801c003143c90050344824500038000c40303000341c05940304007030203c2041b0b9842e410410114035010040400f182c0012040d4400900c44901400000d842600d0404031851b2480c222204c0d54031545075010040003280d001c4100151542d41c00c01401503d10641d516600c60005000f40401994007200240e030030350742000300c1c1d2150040c1c20b07241d0b540c8a032039080c10400f4042410090301c405101c2c28000801801034841c040d50590845804108a90f480e42d408280380d02414410390b42d1321706805881c85100742400f601050701c1d6454000c0f00c00c0c1d41717040b45151100c20150b00c400394035004018440301c42001c2c103103885c0c2141554200140e640d1241c000084043c0d00420060400aa078a128407801c00d400148140c140c4081d6022102220030640400440d0f20903203c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 660264298 1250 660263048 660263077
    0x32a010804150f1806060618030209161b120201050c09030c1009050a0f150f080c031f15020106090203060114030604090807051c0f08060f0d0b071211 66
    0x2c807100710140d401406446072000c00801c01c20144280c9081c1900021030030b660070b640e200c0c000c00089800150610941030440540704205266400040c0303088001030100e858031700d65a055400452055030655200e4002d2080b500748030007981028184020103464840140d071030500440e0f006000740007902c1d20560300400800c203900400c0705000700003000c0200601840b075aa6408102c0c0c1d600c0840c80340103080c07400340c800c1c0c003107150005035a01401000001e03010300c00c2c42e040315003283d075008000c280d100c4a0000b0f11583e0351500801c1240851080d04c0540310718640030382c00b244000c0c4601e841d0450540d240d0091007042c3c6c5800c2188200c2c80192030281c041000c035400d2200110b00540907543c0300c03100420006081000d51603900c1c0c294488a421940c0e43c00007000b000b48212055402880392840340b07840c0304c841c0f140c450003400c20032001e0001d91003945c02e40000314040c1e4420442c1540241d00c034030010300341d091040b809010506c1851035414600d081400e03a14400d11101d095a0030701080b4800c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 660265548 1250 660264298 660264323
    0x2071202011101090b090a15060605030103030809030c0d0c0b0f0108061602070e0a020417010c170a0b041b030c05090307090c0219080a200a11030c032a010804 70
    0x1510750a821201004280d500e504c0341c3d10214003608500e91080c1a050042c1c06000740030301e0a94902c4003503108800004e45010000c2c002154041c0550741525450b003003980407a12100303140b5241d40600105521988655644081c0c215070040b042604c1c280710700f4504007a0b8641d24074644c4058002d0198040356800000000d4605824800600040845005442000341c4841d1345942d000c10442c2e08840c0a13800250420050403003c55078061529104020080c448801d0001000d94001d120f03a01e02889802010544440441d404903101d40c20051042182031034400c00030804203030030000000841d24103035170403018601460885200d408014040c00c2c0680c1001101401002e0041070b1600b1403292040d440c0045504843c9039140030b001d02051612100d0340500184480c070581c0e80035106036002601d240e1036580006142d07a82d95442140c030540e0307004071400301e49042004042c082c2e25124a110414205a040641030890750f1015020002401181c005480d002e4040d01d008040510310038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 660266798 1250 660265548 660265553
    0x9020a0509090607031104051215070203040b0306010c0602090d0b1f0b0f0304050c22050703110a2318090a090f03030509070f0603050a06051f0c080c01020f07050d020712 75
    0x610503886044081446ea0400c0c0d15400401c804543c10060507047d035100c0303001004004200c22019501012a00c001c40ca0a42009500b0400e40000703041c5a0621564400240c10000c2030f4050f036500010180007a288055641000a0784540a8076005c1c00e020b51900c0c4400d0f6040d456805805445203240c50514002d104003000821b5400144190b4076402140602c084555400d544010490f0306250f01c0b94030000f5900c0e2050032594007070a010245490915a0100d2444000548940d05c0103410710380b0802406240083d807c0380030041e011200d08002810300c1d00c210301c04120f982059402d03249128540c0d501450441182d03002c82d40500418415044140024425002070760710503002014ac40326107648481c07191035000e40d9080600483c1e142c004115031085a48074020007020121a13401c0d40e4030b80750743c13507007000d20b4020820001c001c01356804106004d4010122608490680021907552000e40160000e0b9000110112013500030081e0502c0e8081c40029008151252000c042080840aa = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 660268048 1250 660266798 660266801
    0x1805010c080c0c040e0604110f0a0605070c0f06051312170d0f020a03090b090c013603050d020d050906090405041b0303021e01110904020307180909020a050909060703 73
    0x958440b4120b22502c030400125894900030708450388480c030004d0043e404d0600e0406d00a4030704400c018050300198071002241e40c2c079020808101d03146410600d66039403031f50070700e0700c81d100154000f100c084110f600b000910551003001409001e104c07941420300d07240c860f01d6180300141d0001c4060074080a04003402c54909100d40204010f209220300042c01ca17422000640690308014000004070341d841d4440c5c810b02106440180d070100100c0d0107850303906407240000c3d0604503941118072144412a1030040c03030b401d600c841da2006140c0380d00c40b0704405540707280c000d9503000410142c000501466400400d090f001d5010344d40542e00050002d820712240006100c000d00c0001c2c01942c004820200404200d241d40301c040b40618003a5001e0b02032000c2c3c591071015420102c140c065072980c50070840d078040742c0d09030041e40d02007401142d016a07240c13907003401211807844818007001141c4103075000140c005003642c0860b604900c02d54107a03602c0c40d5600108000700700116403050f02600b180000079140c0d0701c203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 660269298 1250 660268048 660268057
    0x1151107241106010e0f0903030708070e040e0303010e0403020708030a1b060f18020a1203080a092f15090105072a090e190221120d0c1805010c08 64
    0xa0b142070100d541084052525041e001c1e0f105070b19100a00085c0000804089502c55201e605280194610b09058500504100d0000c003034004101c0410f030250410780c0d81c0e4206443d0561b9580072030746ca07540c4469a044060307a0a0300c045000d445403001c0080e8211001c01524800d000301e4031000003a078081b040c002c02003030500c1002c032550759a50801c02030944161069000d000c4c4c010700c00707221138031080c41404569600c40e000120b01e03405003420403000903840b000150780510114008280c4540034503011b0840400e0601c94038400f80880ca004440c2c0c10000d41070001e6140c00c5400101e01054000b01c00c18a10401207030341d0000b06c00300141d001003400408603070001e6100551811203a00041610052802ca13034114070086602c5600c4140200b100700100e403480c072103265010740e04c408260300140b080c1929643e807003081629101240c01011040c01000d4a003820480030301d80d50803040740c00710018a044140c10001c02d81d8000e1801c000051581050142d580c10707100d201d000381c4140c13948a4150032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 660270548 1250 660269298 660269369
    0x50c010c080103081917151503060a051309080f0a17061f0c05011b021b09280504030c02030609011b0c0f0c030b0105090c0313030f1701151107 63
    0x43c0100550b694039012646e28812585c1c003182d401203010031020451007542c0c0f032104048200040c070621202e03540c1c00403483c0448000301c1e0342400c0c00d030480000703102a0029403806400d00c68080b41d200c10383c0c2e16850082003001074958600c030b80e000504440e4000306c00251038a503080541c12140c1c0305a940722021040b250042c130704091382d080c103a99503407601b07480c1e1080d2510801c000080b945a40700e40c0405c0502e610941d00c40d40b8a02c101041c0020811310b00d0020094105600703c9106440b1507c11a948041d04030418074080c80f02d1301c3c290501402000019404901a105d460005000500184204035503000d03074a241c3c2d40c4404a503401291906003a4105890f1481080714641c002055184000001d610940d0044200d601d000304010004000901581003410b0030001c03c16004041c0c490424400c3d03260030071015400194504842200c0c039003104c050707401d0b44840003250180f201d0280e042d00d59a02d95440804202c00d00700262102c01138820503421807a00b41d0305111300140c1040c94003480c1d9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 660271798 1250 660270548 660270557
    0x2120a0c200d0914030c0904021903111302031302091b03040c150237060f1406010306140d0602120c0306010e010908031c0f0c050c010c0801030819 65
    0xc0001c04203200c03841101c9158106a00960314410459007140d40c0c40c0051640390b045058460345072003c00e4075080141c5010307110f50555030020f0115660b5440091070808075508840445407a80b4220300c15408000c440c51185400409698032123005008880c413504a441c10f042c5800016424003050040103002e0004030315554503042d40280c45000903511460041c40c03d280501d141c21030240f140ea0030754481208640201004000904d5205600041c000030141c42d40c50605900210070a0f0000d0000014181800e180103004480d1040e0045000c101c03070920500c003240c0f213820040d002c452184c07040c8290700d0083c400c40c640910b80072407100d44407030080f2005842d184e5210341c0000f15141c03c454190030040040240302d03095034488000503443c2002e01f0302280c0141424106950380c010b241e04900f110407499014008082260001e80311540c03d18014070003509411000f038029003200c02c801510b50318200c2030000051141c002207048a410140192400200c0191032070081e009000c083c2c10700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 660273048 1250 660271798 660271817
    0x5100c1709101206050a05030319090b0c061006051c051b0703080711030322050c0613050906100c12090e0708090d09050306070309050c06040e04021302120a0c 70
    0x685698100c9181000240d541d00e0f01603114801c0b2000300d60403500241c3c010642c00341c00b4006a01d00104803420503044000f0203004181e520340880703103141d058204621011003c80d0f0203120380c20000c0d903e40582084d5a03000c3c040c0c0d0b2a080c0c100c4030f502540042c004921980350a40c00c07906e22990005810010101d041d4809c0d000490309441c1a038403081044000494040412601030750001003c50100590b1018503c1c0d800d10b595800ccc80b100c0c0d112000103003502c3e941c0114040010030854940d01c204060101500c880c549861802c44c03d513140f10752030017000c0d50030000c1e8103840e1840301c1d8110400ca07603c0350f4440050035103950507026480580142840184100442c007983e0311141d040c8101070660350b081581c40e00761b0840b4203103814502000c00780040c2c490144a80e80d40464041d601ca02a440c0012f4021610300300546809009501c240c0c00c8040003e020405001e28040c891003030b4000c0e02c0364461007410710b420030120f00ca0141c1e10300c40c010300c06c03012540d0401da42c4c1026504a00515041c1b403103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 660274298 1250 660273048 660273067
    0x1c0b04091e1b0806010e0a1803081e190c0905090406020702280315090b06092d09010c0c1101080c0c030d0c02010c02190f140609100605100c17 63
    0x251a070780e0f08290020341c0484010402c601480c03000c20703482038013401c0501c0362559840c4241500060030900400b4030000800045030941003a401007080d212000130580c82d03003004a041000f80c4d40000d0900013140c140f011446200740540041c1040b100f028210b08225591611150000d400c2404c0072a4004084011030041007480d041d00341203c0148050b84640c1031451402101e5020100f0344451000d04140c100004a420880d013a5032041d000c0d643c02c00240c4d907c80703d40c103c0d1800300203080d00324035003004000200351512030304910031803c8ad4020041d03400001d4007620754010454006081c0790700c40d10488640d51140b48610341001e15001241e041a09049605046d13130441d604407000f2660f55102c3d103450741da0900949901c901d007800a03021002092441c00c0c0700f10b00e0400090800041c1644800c00c00c0080e02000e6004a100c0c800e40f51036080442178640c842c810b4483c010100c40c2014004a094a4201981d40d0108000c1d110340118520b03941c1d42a0000b4034041034411100742c00c0c041c8848 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 660275548 1250 660274298 660274343
    0x201210b1203041509032003030c0106090b10030e100207030c0b130209060402041206050c0403020415080609030906090d06060906090b0307080307080921031c0b04091e 74
    0x180c05403402840c2c440741841070300c000b00b45400c4070132400c0041c03840003003012a02c1e103008000c0f01845000a680340703481040210b80341d4850600384c8425503180c15800a0403130300590105613213070001c0b100b148044142060450503500c0c5204a415a50084000c501d0030702295401000003070321905055001500300d86403000004800c40b008504900210700c07074011442c06525095101604803801c600b42800c2a000100c10211a1001052182c0d10b0022906007142001520002c50380100203102050201842d040124030ba40301d41217442c451b00d40460441003010051b02c48529000c5d05483c1004401c0d020003003200040541030741c1c0e099441c04040743e0070000b406910003504401c41c010841ca0300d18000e1614064490341710074019041441900005000b440c02c4a0740150103d840654408900e1091415800580c280c4010342c84006020111368080d18005052004021400c0111035007880030308c000d0700c40b02640281410b45031004008ad007440d210401403d2802801800c40300082c07400c01c00c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 660276798 1250 660275548 660275569
    0xc03021c030f0c0c08030106230403080a0f030501031a0c0d0c050c1204181d01060e0a050105040b01091a0c0106030602070b010506161101171503060c070201210b 71
    0x10009448404400d04812070780075400b804251450032011384506602e5060283c041030140104001c0c50f480302940380048032034032810002d1a141c115a48540d40e25000110703502506130240810103103045020418001c3c410035040b2034018044600344400c0000c22141544002e10b5040c010206022124807492030f84580c0d18028440e4441e82d580304a00d003aa146450300a00e4001080f00c0d0801080c0440b5a0750340a085074035620301c001043e500c03a6200000120301805420310071540c40e044000420b021408a030901605014408100603603c810900c0207403017182e601c05000c5030003d041000101c0700411031103618543c0890003428401604282030945500358404c2ea03c10340c01084c5502031141c00b000321401410201c800318904085a0304240410f48451360162484848880040c2141d00800140c1f4541036943d461402ca8506440c1c80750080c07d0504003503029224060010f00014405002c071420743c5d40507191030100450664200d001807100c285070443c002c2c2c81d808421025203800342480c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 660278048 1250 660276798 660276853
    0x3140f01180603170a02070b0313060f11030402011409180402040c0504060c0314090405130b09010608030d0b04090f0c061403061e041d0c0f100504060c0302 69
    0x2555240c00e000320740d007040400c02114035529101d01000052943c0c0007000c0071400c0f58801d591140c40c0e03c20283e04019942e030013100d1307141c2c0000c00c22460150010f03054040d00e00c12074041000947c50001d0f10300700d580000507203d00380c0003040410013543c01031080b402c4d900c2d0764450441c6004074040205404618021460860a030300400740811403905001d048481c42c01480c0586c1410311703204005060400c02d0340090144560b0503003022182451000300c800aa4000c1d00500141c06c01803c00f1044801d100c4d425030781d015205000c19400756041c0070344802c03074405800560602c2c0016070602c000306500c08080364025594141680020b2120152600447c025250110820319000000c4e08035000c01c610f0383c015950400801c5a15030340e0401c0c400c0042c0039001d1011007020080045001009941e0414110300e2007082a4048071a0010709101141d0041e101c50b07a612900c00b05120803800032001c454046a400c0c00b00744111481002c0c4140c505000748100d40319484004040540b16241040030b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 660279298 1250 660278048 660278071
    0x60605030106050315031c02100b180406022106030c15041a04090f0e160506073e040f0b060304060c05120412030c0f140a181202190819030314 63
    0x4400164041c031540b40d49e0715901000380071182d101000a203002d20303042480105c030001030022405001c0700c2d0341036580d000c5402903e0b43c0341d1502240191130000c001c46032140f1074400e612411410303041c01400d844166008441c2e06082504103c1c0003400c0d0384081c01c3c4140203a500340000035480309a40542c84010a04002c0080c1c050740c0c02a510b410f15032603060000966410718020462511080219444180c220640c5041030a03c0c82c540401424107201080c08401c1d1aa4441c486d0300da140320f5420512001c84080000c80c04002c80c00c0e040d50405034009c4c0e400700051001034085030341ca41102c01c4400080c40e0552802e10b15203480442072105650503920201a41d26802d02a034051184c81c260042c50304218144004281b0001c1c00105002ca071b507800da030404550361000300d008001240310b42c0c4440980036072454880c0c00306030110784101d005030300c54100ca01c04a00506001c40c0024182c590320406440c040d000300341030390743e68509903100f10105644c42040c44004050311158602070b4203030903a07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 660280548 1250 660279298 660279343
    0x6120f060c07141603060906090f12080114030705040906110406051801080105030d200a1a10030c272c06061e0d050a030216080106060503010605031503 67
    0x2880443c83c60b1049220000d9403000442080c9101c03c03c8071042207030390281012405640d81d24004002d400300c480010003a940e1001030804000c200c0198051100f02c59450f12026a81e9080500e25022003002480d0103410500c1c0070b000d00c0c24a0341011400c5405603a01044080c4018602a008d5200340c1c8114001031001c02c1815550041c0780d02e4500c83c520902c0c14104550410340066150b03a01912540180091856041124000b40b4014406200f0341010764040c003009042c014a001503412001000810503000a84c01e101080d40301d1003070301c2e0080d107a80401410304036881901a408520000c071031080c691105030500706070107100244036212048045100c01016110700b24204a48411100e07000300c400c20180c1d4a4401e00090b003550340f141054007181c81203020540e20910680040c2c07482c02904040d006040d00040d1824844141c103468010203a43c5600450899615000f51000150200010011a485000503507000380702141c0084402079240b000030314000d0301d8525204600c0c1d4046 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 660281798 1250 660280548 660280553
    0x121060b0f1c1103060d02040f0e010e010e0708150c0408070f0302040c0806150708040806090102040e01080705030735071508010e06091e0405160b1206120f060c07 72
    0x40710161210070241041c4083c501c5003045001500000f400d05003e20902c4032488290b44d00d540220110302d40e01c0101b0000c0d4489a40c1076800f801c583d000d02c405070b6090501c405120748000854030115411580580302c0028880c1c40300b0701c043c101030a80404400c062001040016003072009000a240c11080840300340c2ca540306201c207903841d0035180b000b4810903c0070400644c891083e00c07107141009844190340c42040346000d584900445c0c2040e2914400c880c1000920344055004205503564011a00f140f03aa0310309030190b50703262600a498040c2c0100104000400303d004450000480b0081e401001190100d0003180240007844000302c903504c150400c00c101406000d10180d0060f192514058960411010348181032002e003000d4003503403044000a01a04c14101912400f410240c818146814142803183d6603130701c016850000c5200360000019044a00401c840001d8500c0d405890035940300010001c0c8600c1c0200c035a0614080c1180440c41d1080602555110b54074400300341c3d0b107605060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 660283048 1250 660281798 660281827
    0x501060e0a0c0f23040f09020705280303020d09020613030605060301150e1e0c0703081302011e051306030203090709020724110a03050603060a0501050121060b0f 71
    0x200b01e00c05100741e91201002003603025405488109803e2002c2c8119155910009424800c9a101c24a8902620008680300009070020100d8600403c110340b010b2082e0340c02451030001c9001d8440710a82c980e071000740004d0094029103407090300710070001400d1034140c001c203000b0ba122103112184803140910510401005200303490300f01100350000c00403070b102d01c040c1d500b07021064021882004d52001c00280e00c1000d074100041108000c82504140b4104080d9000031500454022004a00440001150114400341040c4465016940c0740e903e100541c01001405454065140400ca002c000561045205d0714222000b05050b940050740c0303180204481e82040b031150440300c55280100000c43c0420702c0980c20324588061034440003041341d0710881c10780c01001aa00c003040e0741400880e81d4031213550903500181c420081602924400c1c1d40301d80c072070811a5000d000322400302d02c1d40076090030503507001c46200040003910080018803c0c1c40f9100081d4942007900540b111500000e0071032805c4109 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 660284298 1250 660283048 660283061
    0x1903020d0206091c03390e0103050f0f060a211103030c06280908040e07030e0d0c030e0a12020330071e080406030605030313060315030501060e0a 64
    0x34800540b00c84511460b00700b03220221441c2d107038101070319a18844030900b05008558601040000c500d000e1141340a401c0442d414510001400307d00002c0450015500900401d80310715400840d10900f56500603540c0f00c0b541c40a0822500148a100040f40d1005803803445ca0380090340d880b51045183d070724a41007000038002e0314014000d80041c800070910001c00a05950031907080201131f034051062045c041d19090107980a610a03504019107441401010300040c000c3d1341e0102401d40711940c441409a081d110a00e503440d015070b020200b2080b45903c115848881e01e803092601100c415a0b080c00114419070b01c1d003140158603095079010702103207401c10201c00e103484154484921807002005500c905481d0105404540400203106001c10042d028403203a560343c0040d603004980000e0402c1c98140d0054000c00b00400d01d00540440e6500e070010a44a40d160803e01109401e13003003d0b42100600040d0040e040f0700444031402000183c0d080c065080513014491180080385800390041c2c0c240e441 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 660285548 1250 660284298 660284311
    0x316030b04090c174216031b090b090411030901050919210c050607020705010e180408090f03100f0b1e0d0c1d090709020f120402031903020d0206 64
    0x300039113001940e481841e810030708880921041074100525a8034451000503440180d000c01d1204020121b03640001c1e00540320210783e400c1004074011001c1c1d502c1da5104102c6000802d42c0c084040200000c00c0e00240354101d03000c1d0000c515804100a6056990003e03180600c41c2c0c2d444000300004c0c1c0504008145200165a0f20300c1d00460840c1c8403428051600600f92104804164116031041d02660746900501d602c030040340c02c10710705210700944501e01405601e0020f00c00e0030a2845900d0000d901c144080c10b207510112407030f00c0d182e07038200a40d400102c081d90030a01d20340103c4120b079828400c600c02001c3e4000301044c00782c00e8403050f200312a10740d24030340d208010303a2503031045085004100a000e000103640100c0350159905104002180680c000b14103c0700100a20751140800c402c07031801007050500301e4059644881550041e406107866014654a080c044030506030418280c00d500203001070180e408040c084002020030710440d400950150340040111840c00e0742c101300280e8002c6c2c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 660286798 1250 660285548 660285553
    0x5010605130605181b0f07030f2c030a0512030a050f15090901150f03020f0321030a06080706260405120702030705041419110316030b04090c17 63
    0x41c10440026008041d00c104c00c1c07190007402c0b00184060107003099111000300d40071a196240c45e040e00005103e50f1020b00c00300d00007550001c806c0b0955010b0b1b408410a07030501d00c043ca03c0524600b10200c0003810304000b6a5040c480c0468100100e5030a00213910000603002007155280f0b4149030140a4940207458451403032505020484c2c40001072401e641c0107001150656030540ba1880ea06000d80340d03503803013407006031101e02e400151000a019160101d07442607030000081d0074001c00b059200e803642c9859409903000e01700500a1041401e0044d580001c80d42000100984c80f004100c0c030306400398001401040072880e544010300d503405008074101564610760710051030103030740c2c80d502c42e240c4204020500c44040740040843d5401e0244a010340b03005001040300d00c4200500740750780382060f00c101c0e00223007100600000707a22a034054840f1001411134494510748a0903004030390510605c072480209690b80350b0345580d0341d07030320700600303101d07500824200721a035003000101d85170380c2114001103c469 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 660288048 1250 660286798 660286811
    0x603320f0706030e210309010b061602041d060a06061202160b070302040b162108071404081504020a080c130e01140106030507020610180c020f07030501060513 70
    0x400260380e0082e225076190100745842d001140c149044002d807902c0030241d441c50701da2450b5031580406076100b80c641030000e20408100c8401d0042c07034406c1401c2c50015100714020a009401c1c01c1c3c00c80c6e01642030013004080f5103044284241e0400c0390550300c202025446e40020050300da4010118143d551002d40114070344140d54240f4044000e09400c01000e004620000070a01ea0003a41614000d0845845c0c3c15a540d90309518940320300f036248001c8900c11603102c41c1002c1000d01c901800c08200c10303a25a041562079001d000d59030341d2007182c136142d1054030822001c18101030a100c192407560f0b9185030f04695003090310400c010315000b50486802540038070f408001d20303944c60002400c03281d2821400a04039405142ca24050b20603882031245c2031103458000030f00540d26a000c180702d11001c1e82550480d440c2d0201c0c0d000340d00d109110784215189a42054660410168071003c55455103004840001c000b0301c2d420b60611620781d005072400c3e5501c0b0000c1005044c0701000c040c210701041400c0085 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 660289298 1250 660288048 660288073
    0xa0b040506120d0806011103040b1e070203073320012016020d0302030307030f0203040308060603131e0b0c121803090a24030506030c010c030201060332 67
    0x1595211030043c42080503e4020800e5a4007075101c0b22008600f1300c058a41da90b4644030100410790100000d01020051a0888482407520364107440c083c40d0300401500a0343d141c444112000f0310a1401002041124400080100c4040d001c04c41e000c0c4040e1190007940344003002c5205200d040710b49410f07269042035120004030b0200c030f06040d00110980c4040c1c2d219681c25640c07100164100100a4010740100d41c500103054000000d18458901c41d40c06115188130220f0540680c0001c0d107004010415a0003c1000c80c90301e2405190700184000e002c0401c2e00039a1039821810609450121070f07245020b108030203100c9454456a404011100444d141811440c00040c0840c0d005000340c442400503502940c0c00f0409004450f50f8002c020100b0342c0c0b1369101d5695001d0507001c030301d494910106d00c11421101d05c0c041d0003040c0c42268020043c2ca002e1002e0707001910f00b2a820340045003103550710340010002031500c07900820b070318a41000d0300306c0041000791380c0c0c4c0400c5092103210300b4560080075005403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 660290548 1250 660289298 660289303
    0x111072d020a05010c0809040c030212311e060507020c0118050d031106010e06010f020a03020a03110304030821060d0b04080a1e0e0f010f050403060b0d0b0a0b04050612 74
    0x1120f20a107080c0c1340d400a903003070103183c601a52203440e40c81820440c41141003549034014004065840207410584d484000301c0c6100120900c02c84195070590340c0b244d20390303100c0442411104030701031071030901150900f40c14420788011202084400a0781c0d6000d00c1800c641c1041070180c3c5980a003060500100c0d074042900710490503101e554824050310300d4900801d4440d1040010960b100801c65040d0758649040043c035020480b41c0600142d1000c00c85102641f0000c2c01c65400c44e0142c0103401c413100a500c0888481704203240030340a80c481040300100040c408401020034240c0300c190b125101d981000103c01c130750009014144030707500b0046600042460a104682c00961204c100c070750382c1c03407807010079a0101301c1c1c1001c2c50000c0742c110000d03250694000302d13214031401003110101c0800c0d1070400150381c00b8011103510000184c080c08280000368030b540c17000c00c6200b00140a1560400316070f58144c4a090b040f10110716060f03c0d2038540407181020b01540b0740201007228088203200b518044181e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 660291798 1250 660290548 660290569
    0xf090a020c010b0303032d0c1207050c12030a110301152601120209010f060f0507050102301302090705130803030703060f051009050d050111072d02 65
    0x88903800034040c41001001d600107026284054140c0ba1a4904610840100c100f140404041007804141241e680c81020320075522800080070200d080a90020340c1c10080c02c00100300d0001c0c00400c10080c600d2a60400c1000f09070129508096034a242070306e080d005496020381c400c0c0c40c9440501c0140b0100c00c154000b243c90f12010325012620b4441c0090210010b00009144003240282c400041110000e0319280c007140da009170b90405607641d03111650500c4050a100d0903001454940800b200c143c420360051000c54000d000260415904480c0c048c414541011040c40c00b40103c124441086443c6401a9012844a2021502c2d01c1c0c2a004104540d074024100d604000b00002c03800c485030485040301c80544110000c5985a01d42240081d0043c9198040ca24400c50180c00000341803030f10903400101690944e4580d07482e01d240c0810f0220101ca80364085450b5529036100700e42105081c4003400300c1500400018041482d440c5080c040c0012044001924032404803190300541c913070000f041d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 660293048 1250 660291798 660291811
    0xf050d0213020706181b060e010e01170901020c1b01050a120e070803130e01050303092101020c07050f01022e0f1404050712030c08031302060d09110f09 67
    0xca049400c04a07610020b2107900340c001d00440c0f4294404104c0d40611000d4840144660a00040d00030b01d41480480081e26104202c00540c40d48403020140d4803c20710050a81418100841d04110000c40030502c0e4508562a02aa130350100e201d40c0c0d0110200581d80c0699a20403104c0784040802000920522a003840541840310010402648100c1c03507100342051070300c10302500c10054960000a0320b03940601e444a83e4040001d102152040031415001d040740d00c01801185001d01d070781c003807221520855a890f48a07141b120424410040280010100300f40300d040a04241810a41004030072886400c40c4c1d411580a20f42054501d0807508170110040503448140c1c50100b80110400c0c05000305508604c40103003132602c150110551681102c0c0110321400c1501d4a840d220000d200702100010f0740038002800e410000c00100703414100850b00065100541d2400e5102c5401041295020355000e10480da44c54144030140503548040024019048418424503208a03002038a00300340a42003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 660294298 1250 660293048 660293059
    0x50405060f0405060a020114100e04060c0e0a0f0815070e0f043908070c11030705100c120201110a030b030c0a080f0c0f130c0c050111040602070f050d02 67
    0x5540440c241d06054070020070008040a940342031041d0000c0c080c00048890392246040000494400c0b040729914809a4200c11680d108554036910707104040d064204c00c03035081c041c0c8003103080303442c0d00c4404940c0c3c0070346a191040f1061700d2521038254a0301500040326594941070070b003800030b503030b5100b500a0810351080704c1000c01d071074041000a0042c1010082c0c1c42c40703100783d0482204d149060a00c4128800b4962498400d90403554000b6103181c0c0c411100c810000d1140208100040c183c5e9403000d8001d00040c0485030070548400c041640c0c0c1c800a580b0701d01069030080403400b00481044614071421703083c0b000b03008440340b503102d541d018002d01d0030b2442415202c41c0100310070385003040b150342d00e890020900002a95241441d903140c0b120480102d9644c01101c8042c422803c00580e0041354100103070695680d600904c81090040410442e0082040340130480e0b48013140c001d001e07581c441803a80a0a82d5510315183c40a841c1001c540e00030100710b0400325040102c0c2c0d45074801051200e8050300e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 660295548 1250 660294298 660294307
    0x11404020d150e0705011706061611040204091b030b060a2a0f14060f0a09020d0b10170601051005130f060c060b0915010e0103020708070b06010f08040305040506 71
    0x40032602d100c0d480810880c09840d298102031010800201502118403c1e20741d4030340c0c00880c0380d0007004218100c5025400402c00c000d2891084292200c01c107429000310400c0c0f00455604c4002404d036809a4060410aa210b41c0030010f019070b4500e1491005919042c1040202c0c02c1c7d038041412400b400754801c0c14820501b250b005000d801f00003034414034244c0d600b605245207003880e246544240c900015201d402108548040c8040006006030090340d0203004500e06075a843d0f04030010304a042c108a81000d181041000041c150b11078650203440420140380b5040e0501412008403442c0746081d510703a6210300c004110a8940314111518881c2c0e03454055500c11103808030550704440c41e40b010307201030120768000442030f034001130403816140705180c24051241c3c15010040302d030005903008416000e940c1c100060b01e40c0203600d00c2004c448181009428991142c45a0f0320541000c0342c2a078100070808100700d42076031702002c4120f821a02c0e0811440500702914014034502907170091502481c40001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 660296798 1250 660295548 660295553
    0x171801030b0310140106082208090109030b0411040f061802070507080a062702030c0f04062c090d05120705070f060f0605030c15071b0f0806060102011404020d 70
    0x400c031609010901030034080f80184840005145600f4032400c00010036000101c0d00c21a801c1075401e2424101408c0405000d034185c840c12440d50011085c40e040c464001400800a000300c0c80c402d05c242d000386001c164007070541e01403105403800d180c51845c005180040030f0091103400d09040d0382e07850b894900161a54020b00e0160b1501d101908110071510803071100c8030800849400c00741d90030b910392050076041d00c0401c01c030002030b250211000354141c04c20303030780d00d0240e007011044000d00240041010440304d03940e050080f411145400450140c02c000302d40301d0340407004680f0303940d0401d26800c0186420750070840010840d0040050606a100703494012904052150013500c0c2d1054014a4041c1608400d2501030001c02814006600c0181092400100c610307000c07405003000640a0880402d030b002041074004603500c847c804580c1e1402c1e1250b04190140c82e210110702811001c140c044802d814014514a00500117005504581c101107840406c2007000a8180c1c210398180c8114003600001d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 660298048 1250 660296798 660296803
    0x60305091009020f060f0c0d2109030e15090108060d110d03021c110613080d0b040e010603030905280311030a021008070e030a050c010e06040e0a0603171801030b03 72
    0x510003541e00000101d40e45400740c99150081c400d240302c800423200c1c01780c5014004d980c0d01c0c0381c0304078001d070309090b0920f0940303000000c0d00003000c0584603103458407a25101c00e00081640c0e4180f068440e02482c0800d4075545941c00c001031136008541181e580c622407883d42d031942481f01002500343d0040d01409850010580200000c6502c1000341807180842580003000070002d0340003d020565511881011402e22403003034031842d10719900000c4051904040c0b41c2008068032504030f1035a00300740d485041d814500c8081c490200030794420395501c21054903000400c440c492030030012854a03982180c005810300e12104140c02140c1d84050040c0d021840d801c002402d00e0380060700070350080b240c5103202d5013950340800480e204614a071940c8240881400500d550b83c9402c81000f00594080340c10310f90f42d0740c05000e4a0350117140040c0000e1520b5105d001181c10280140d4152542c00e031500801c1c001c2011924100d2503070040380d4503081c1030030045511409080031104c0d0842c1030581d00e800b684403540b0306 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 660299298 1250 660298048 660298069
    0x13050703061103040b070c021f0c050a05150705040b04050103110d0e0a0506010b0a1b0807170c100212040b07110d0207030b0609060d08030a060e070c05010606030509100902 76
    0x1103030082041520511041d85075070f1045800300c0d0010001000124258010360250b2401c940207001242c0c01441e1001000080d082c5250343c0d002e00061180c4400090010880b0751a1640b084001d0001e0400600e21450301079006805182441000c0c0030034000e07e0f40b400103441c00c44109180c00300340c03130784003000ba004a44107807200250360034140070004149400000c1c5c10b8500500c42c204445550381c2c0c8081c4401036000d41084040012103000701701c215185079290a0000354041c14120703151114030381e40c1d4020b12620400c160740400c4041400c4140342020b014981040941e05419890180c112100d03034501c00e00204000c140600306804148c10301d10500e28114212003000803101c0c608074811019513180300510044800042410004011303003840f1300324502549001e054151880c29680e58924550001400d1264459644000085c111448241140038142d40d4890300101040b81c203101d42503804640001f02854100303000d00c01c071031000058407529040f94500024052070f0b548005412000d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 660300548 1250 660299298 660299303
    0x18010e1008100e040809030d0e06071401060b07050d090e0103021008101e0513020f0703050309033a050906150109051002031312051507181e1d13050703 67
    0x100c10041204003d2017070003d01101c0412000c44441a00466048581000c040e200d5038100130240101000504c07030300b00345980030840000106190f91a258800c2c0d0940245c1c9003070b255940071032010107a02d500705080801a24028034950740641c119004a800c2024460701c4504100366007001400585502aa4002611a2450805580c800010003c07841d07002401014442d02000342c030480100094802c5642c4400040d807403500780709554030b06a5107504000d2848030640803c021150007001c03070800e4038030b029103040d042d00d50038001651010017180000008141a620340000d0140c50b140000d80e460b4041c81c00d1169a81d24403c180048904504584c007454004140c9803520b45115004030207496024200c84000b9200c80e5617486d2080b024000c210040c0807500001003c0c00480401640a9400086401c100c18584030b462814010314030303281e102e40360703204450781c03040c050f408200001d000500042c52415600c1c80410440b09460b80f0180c052180c5140c4e641d0003808010701489007400840c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 660301798 1250 660300548 660300569
    0x30a05180a150f02010504050c280308030a050a0b01090e060319050c0f0109030c0303120e0d02070602060916151e05180105041203031d0d0518010e100810 68
    0x20394441c40104004000c0b20008085910354407290041441449070303512480d00702005004803202c0800b402442120042011012646103100701c2c51012076548284c01903215a103090b0f660300c4c2c0701c0902e00c00c440c03019010201d164207000310f0503403983c2d019400320140ca00140d0780b06069201c6200082c80d0481ca040070000120103004210107100010840148401c019280c9400713140c202c0d17004440143d02400004d0100303110407002d1010a1003008004e2010b1404880094040306a00b5100e1501d0580070100005030300c280c00500c040b6a0511105030031003942c2004011242104490040303c2c2c185000d40d112051100500815175403186020f400683c511181f050b514940051009000c2c0c2e1240030351500d80344104007003110315482030003121f0454106e2aa10540708800350b90480181c0b511010500c101c6001c283c4868000d50184554034402155441d01035494084010500340c0381790316201a414030801000c0001507844030200c01c0c501020032b20300702e800e075a604000700c040082140c10120408 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 660303048 1250 660301798 660301819
    0x10e0f0a0515090f0303120a0e0c0418020a090e03090d05030d050108160803030c030720070906030605150102210c0a030e0102161809031202160212060603030a0518 72
    0x601000100020741c004c2c2c0d60f1440032200b42081c10340e2885410014503401035075100040242110364031044084d6000c0d015034102c8403480000405959100031540040504031254208519000b85050010540d420301480880440350302c079500c0e4003030744403031034000e80c81410104200203080c8125400e05d4046030003005256120f0242940cbc501e983d044154484054400114640c0c1c000001d4a2081015561072499903503a11021100045054001d003030408908070300c01c400c18028006180603140c9038000203180c1786103003480000c0d035501800220300030a01c2e5581c0c2020381d9012030031142100c1442e895400002e8680e520121900c5003005003825406091031490415620060007002c895090342141e042070401d0460580c001c0c0c00d48255a00502040360030200c050443e04506c80301406400c25400b810801803914041c3d030b00c000703104502502004681c40c01c40c602403c07a42e81140c008802046075244c0359000c6913403441003194000512101042806900c48241500801402e0140030520503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 660304298 1250 660303048 660303079
    0x27100222090605210a031103070209070e01020706090806071b170702091f06121e020702041b0504090207020a0902071401060812040e0a06050a081501050103020405010e0f0a05 77
    0x50000340500c912032114103000134407041c40f29014003900b0789100d01900030034a043d50300352030340940c13080110440e000501228026981d015203052284000341c03a4409200010000281000303030341c0e0400800d000030104144100b441c00140c0076481707245030030030f414000e8000c4203034245400100b00040102c2e000c440c49080d0440070201a00304940300380c5e000c1e44251500a55140640b4082200d405002103012040180310720800c0300c1003029201d4900014140229544404a00d10080386100103036000141c00b400c40c142071051045254507058134006607503042c0c8009107148124400d6110a50b000b00f080010365031240000350061000c82011076aa108501e40b0f51004400340d411b15030203528140c4001000040803460380d007403280e1070001a2900381000b080c20881c08014045c1443d003945c3c2c003800b0409840700100000a01190780040400708600300d6001c5c03074144140c01031410180140001c001036600501d80300c11100c03003250202c000d00d20b0031b00460b08106003540034552061141c00003843c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 660305548 1250 660304298 660304301
    0x10c02030a030309020f12150a0b100201330b0a050909041a1605040506030910090506040507081902010e0111100e010f180213060803122710022209 65
    0x1881442603818600106d558020084036400b50031207406e142e080661454040503941e5a440da001e001e1603000182c0807001e002090018075805243d901503036681d610241d2605030075089031889070a1036006100d000c8a044050071020b5244214900d084010074214812030040c0b0640e030100c030000c2c041d1990791510f07060204003008000300100f644e125070400718000d10082c4024800b03c214a48800e4a06417410040c081503510040003031101c1d0007918204030a911080c040c09080038000d5000309454103084c249a428032009910030410780e0302c41e030212011140c944941c40030345c940908001a07241040c0c0010303205120003444002c820301030719140481c10003d96004003030a00341c0c030700200440007080088800b00ea80c450148020240f040341540010315068032108040302a812002c5100707583c4012203840d40d04801300220030583c42008000906109100c0ba00040700c0e09100301c40703088210884152200e0000443e1255282c00003041a0980d00e200c1810700303101c141605e90011965510007890 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 660306798 1250 660305548 660305561
    0x602121302030601181512030f020a03091505120106080a060801050906131a01121101031407140f030a090308010527060406090911040b0102030c030315010c02030a0303 74
    0x11000011404600140d03000d0508040c0303554060001d100690a00403040703040b102801c401020b5640b6100c401880284000a10000340b40f0902401b021300824a0090904030b0380d65040011035200380400004640d0181d011401c07141880f0345180c0c0c02c1100f0404071010311900c408000d03901b905030000222254040403113407050700045400c0080a40700d240b4035007683d0056400420030f52000c000328003000c0c00180e82c40947c0e03100c1c0204100c13041c0c1000140300600c03800d0340300c84100f40b000381680040c009000110138030102d007481e00300314408080e94144040c6001a200318101f0084114480d801c00f55041182d07040380d01c8800e580e03100c2ca0f01c508400060700c03a4400440c00201c22000000d61414801c02c00a010541200800309444002c0044010850020581c550040d01e030a40042c1d14410303881000c2305180150200c00d03825071110305020581e02051031050440d4800c00a807107c071040442541d40088402460b80301e40300c003880c0104e9034480c010700080d515002e105202001c25400d5070050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 660308048 1250 660306798 660306817
    0x9060a081f060504090c050415210908160c0f0321021207060b04021312020328060b040603080301080f0c040b01090b07051f021e13061b0506040602 65
    0x481d4080102420100070300390314400e880200f1400c0c44103000740d505a401c001e01c50015031508a0400c0e5a51058041002c1c030b40101c84041100e5902a128006048210b41c003000240c1c2800c0c00b40c0001651000700c80c0c45600e20f1000c0d4038400040341020000e603915030a0042803141104002c19443e07040280e400c5a03c41c0399088101c2c000d820340d0070b407280041000b41040c00c00090140c240035098440d1005090510110781c0d005070b00308842c15a03420502406006041001203480c2c0e00720f001d00c14980f0749226104510301e0b104201034040300e00b82c2d480d40041c410741e81c402008191421040042800340016410081111b403001c030011403e08800500321602c54480d904076034401c3e04035400d001c2101c1d00b00447c82c1c0014090036080c01141962401010203520801c111040400610f0b00701c081041c0302c1e400340d440c075500051458007606c0540000c0c80d90314112401d441c0b5102c140310943d0ba101c01144120003d020088900c00105400031a1141c0901d8000301521110316091400703030003d60111070320 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 660309298 1250 660308048 660308071
    0x120d020f010e0606010807032007061a0306190e0f0c0a060807090e250905040b0105041214030d02030708071403040201020a0803060411040e0924010902030c09060a08 73
    0x2400c0100005008080c2860911400741200f074450707600448803504011300c0c1000381603c2d8a960f401c42a60354107900390b0016201d601c1ca442d1743c1145011000d46005600b8228030001c9440c203c41243c0d40403540a420026a03081003045824520464001d4845400582e406000d4414018441c540118070341000103030485407014444c0c4c4440703080d9901401a078428002807003100090142007540c1c0301240d00942080441d014402c0c3c10b01e0340041043e12001010000f8980d254108924205400303038610b10742e02420560305040c1000e00c45200030210380c00c060300c03510707103505085d49909003030040b544500b5031501c0656480c603007508081c0030b0140c00d8400400007284607811202c0e00341404140d034002c583c164042c0c00d0300c10142d212000107410280c80141c3c40750703880406401c4038259000910040c586c21910f07070b1340e52400810607410801c4c011080180c2a4034103910150031169100100d0644456080041c0c81e0740310024162611700a50700030a42100000070303440070301074000e402d55102d450558070303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 660310548 1250 660309298 660309313
    0x8060f06300c280e0108030405010c0f02030a030c14070806040f030c05060a06030c0617070f0e120a0c09061d1005040f050406060501030e0c220c05180a03150c0905120d02 75
    0x1300701d44450001d03c110760090300144410b0110b588134100c0040d4150080e861000f01801a80020342405015103003140401c03403074840303a410000302c21501d507c8040f10320701070300d00c50b45400c81807030f29900010001800303002e100031081e04140c0030720445000da6030410104c80d50b40c0360017003018000700707034600054071100c0c0303640380000d0260300c00c62805403a002c1c0c040350040c013500d402000340c4416412403510020b1005410007000d031912342020b103e5040c01e40c80b00500c003004c0c1030300703009030480c4680e003140c520701c5c0c2000703814896048010202a14549100008072259940c1c202d23000e4000d0f469008198046e0402284440c044070f40d410441c0114010355040125a95800040d02200c1c04426042507030b070405800c0c0f40031450305d4500c60500e420151129012014408004021a04415a4140850000304592601b00640c1d03400301d09880007030300e001c000e0500f0354407903001508108501c94285074941000d0500c0358415442400140b2014000b124800c0405400710780700c0c402901c0c0413006121f901d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 660311798 1250 660310548 660310559
    0x1403070602121005060a050a0e1318030305090d0c030c1a0421020601032307051206100609051e04020d1b12050f0a0209010c0c08060f06300c28 63
    0x1280c00700c242c036451f00303403410000e00c04c1a45c0b078043c001d0805901c150444492000203459010f01414604000004c480042040c038020382201e102a001000315840011080c1e03100303801507428903040e6094204509024140e00e4004c2030855503071004240343c40001c1c1440308010705000d00c0c3d0403c140626601c0042c0703005000481e0b840209100241c00d0a00c03040002080d51004a810342c0c49580c06425545510b4031000417680d04628007110564541c44502007116001c0c0107004000a4007003460f2000f515880c0000203039552031400f150080410300840c810005a51300e5040b50218003101c54180422901d40c1002c09400c4c2c203400b003c00c0401e00c3e00760303c05c4060000d0710071306c0d200f108001110b0391540c56030004040250070441740c3e41e0611a03007009080104401001d00b40080c9540b00c014003031880c00d885842010840a40414081c07400041140880107161518002405502241c0021a50121319007803070544001b0203650000e0801111150740c522404820b4a940301d402110a030b00c03030b42c61 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 660313048 1250 660311798 660311809
    0x6010609170a0201030e0c0d0c090c05040b0d0228030e1e03250c0e01140609010815011209081201170a030503070302040b0f0a08160c1403070602121005 67
    0x110780064030354104014040044d8020f034043e0030030341840c200f140e041d0480500851103421441e941502d011710944002c004001c51350090b00c503612030b9464075a0410f03203445940380301e9004110042d0307a0150017150050f02c504946030103120010b40c041f0b81d4a0b49000851019008050b000305800d001e000c0e10710b944101d000c0c60800710005010040040d454200386107e401c0c0c913150031401003e00c449001140300c0109620580d003c01801d9607440d0090154900095007000551444c0c031580070319028803603400e040e80c101002961002110100002e003402090041b650301010708400520203203010518414000004040c1003080440507490205076265610035040103402001082150b10803510100024400c00265400181c582000350405454440b198015004440000001003010818a1505900c04005900942e500d884810741c450341c2e00c801810005c0214015101003110082154000010030881d241175800030002c40d118031110007180c441450a0301c0004801a2912000c6601d2410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 660314298 1250 660313048 660313079
    0xb0d05060a06051c0b06031e0a050609060f03070312050a0809070b3106050a0221090607050f01091a091f0506180405010c031404120c05030408070806010609 69
    0xb54455500b0550f021580c42c121980308600348043c66203485c2e4911381d41d1036601c0514050f40c070030701c04003045242c0c0607640304103130303000900d022002400d00d418003060391200c1ea46290040c0c01501c00750760701d400c00d4010030f15000d81603100801500c12001d0b04140154031101400a5007c50303500c068181d2209440d213a80d410741340c042c2001c819010014608418032a80101400054400d40e00e0a4400d0100e0070f003c070202240c1c0000301203107000581c01c8099506022444400725000005404500320400d01e01450181e822201c0c01000002a0001880703c1044000d0a602c030603c020f01c07925005107002481c06640308200e42c094010880400c4030060007265650001524000344149255041114806010082c02040c7c019000780306100039071400d00360b05882213024000119070b103580e20000600312418072224400c410194008e020000d5038440341c08813b003003d0316002d5694412400c1144c15407142c1d90100c0c05501c1003030300000c0d100c103001c5031407412182d9649800140d2552514408030103c1d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 660315548 1250 660314298 660314309
    0x2403030304121b050303040c1818020f04020f180312310e0702150c040b0403020607061410050f01110c01210f09290f0402030a0c0b0d05060a 62
    0x59400d02d00002901c00d190702c3c0184210141050019146612a41d0070740d84256019200106611810b00c00032401001d003125881c80b0400c10003095000a9013010030300007140c002840380c0c10300300110742c00740d8894041e0303240d03e00e200b070b603e03079035038003102e42003401010f42030651406809100145c04c42002214180e610380001d100d26143c1c3c4042280b0b0100c540564418408080402d046010807041d0800c0303416803155115400070a010b0120340311116018000a15007012400c04000038440f00340c0e0f0030141c604480d4141e0391107880b40308030724011015040041c85244040c000102304045289140800d0b0704031b074400e507100524110303c84011101210100011401c41c1e1040381c80d2a625445410300501d0401d50041d00510800c0d071000c20400d60f406164881e40c41d5446406c040e0500940030031031003062050682404110000c1c444000400400a1042c4d4050b03506000080c01d64400380409000d040e400445240342c0341d21003481a01c2e507007107c102c01c4031031440d0200003502030a0040e8040306859 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 660316798 1250 660315548 660315563
    0x1605041b0804060c0915050705010b060f04090b060408010e030d0b09040c0e060409140f06101a0c0109050304060c140a0201140a0e030604080a080a110723062403030304 74
    0x252203445880113014904140c10030031001030800103460010040140c0400016a00d455548049003042c5081d585002c0445208042c20003148031319203401004c642c03c0341c61070000403804000c004000340c06805181c0c0300102d903500f80100903e080d0400b000921100d50b209604000c540c200c0300900c00050022240241142c074480760900c040c035446d5041c0380d40508010000300310b180c81c1d42d440e01c82d046094402c04156a000852140c403040f07040c012250300c64200030196010030300c0c00500290070100301a0380d01c0c080c440003481989072503003900701042468000d011a541d842d03840300018590301d1121010f81c1e5a40c1c0e4100460700da54404907032810f40e01d40595804070b044241010444960b0b1041081c0014082c46d2081c900c925201405080e1060b80038035035150300d0700e010b558040c20802c030042c400385946180c800418400340d01c110035a0f00c5030b074000d0012002400e61002d0303588a020140c1885400e4800c500802c08046d500c00e41d41408500401441280d01803948141640d034081510002e0129 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 660318048 1250 660316798 660316801
    0x8070c0906320406090618050f060d030c080403030203190c120e01030e010501030b0f06060301240c0819030e030702030c06070819112e0504060b031605041b08 70
    0x124240007088400c02d000303582110212081c20000301164016444541019181c2c8000c0103512501e4003810007111082c0700a00403841e00d40300807010814028091445031101c146a041454422280111529884803034507a6498403401d01a48d80d4010500c1100c09466603c7d011107c85d01c0f40c42d0100304164003109291419182403c1031b40c001076880441c50400d46d4a40402141d0301007401400c0c002c502910001c01c0501341550060035a1100601050150f031007080104008405681d11412480540250107200c2d50300e4002180c41031403402d8003421a04001c05d0204612021070800741030090162420040c0d820000d103c0c3e0b8680c090b0403006941504040015151070400c0da00500501e48920403180c0303040b042e002610048490b20140400207440c3c4000400b03e12002c002518007201e01031022a0240b90309074000010401840f5a114001d40300c01c045810000030f074000c1420004000c0907500242040f5056222585252041d00d128500f800f000c003942c05502c1041604e140b1242c0d0341d40c50103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 660319298 1250 660318048 660318089
    0x1908030315031b1008090c13051b090a0b07020d0b010e1e0115050702130c0c0c0b121f0e090c1e01022e0213030b15130f061208070c0906 60
    0x41c101c0046ca035070124003401c0a603894569640f07410000c11810404006900e00300f9079140303420b1000c0c41021001c0301004105081c1140e888034075030003ca551404026503110b40c98404220b410b50050001011081c52a00204d807000203d091184902d1341d14104400010503203001080f051000c1c401c814400041481d10992a40301c0d200400c0c04a00140c1404502c5610704e502c9004c6450300302c04000040c2014001004101150300c0e00401840035110180c14601564000090ba080103451641440441d03044070078111200070b001001011003211041041c500b0000281c0c44408a2007058072401c003146900f01744290504e03c1e454110011390081a901403005a041800c00265001d545203200c90060202500c50034002802d0072075080c820b003080c041ca1490074110944020740302145081c0500e2841c03030b5030f0b00c81107000600d9142081002c107541d040800600700500841d0880010305e0358111049003403180384001083c02c3d038070900c114003500b541c1d040c040c0119005802680031000d0f103e88007401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 660320548 1250 660319298 660319307
    0xc030f03093f030903120207060b0a080303090f0601083d0903031107020d0602130b04080c18090a080d06050303030a09051c0c021908030315031b10 65
    0x10142c1c89401d80101d04602c0340009080031940307126641c8a000c400c6201d040003005031084071003584072814284074034500c55402070652034881e0807440c081540420b12005001540c2c01078074900c2c4002c5d2040040684400c82207481c2d41c000c9501c06403601c40c0e948102c0c0341480004015040714800800340c520040740c421100c01d449030821003c00e544242406040d080c40603140c200004000b9202c00040f80c83c442c1c81c001e015102451980743c0400006d212030700160b151162540002c03a030181c00142d458003843d5020f446901d607038019005070b44004c6000b0400210010b100e00410100311381100043c3c1c3c03000c00040034020200d4480455400c0102440009014000501820201b0840224a140c0c44030003291071501304440088146490b40e211109101003070061880310541da105404e410780c4c0203100035004030024000280034904c000841a18410b011340110081c0400c04142d070703901e08140c0307080300d0a00d2603090307101e21a000301246002c0005200d0403044c81038034050b00302c030b40d6a44812020b44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 660321798 1250 660320548 660320561
    0x210203060402120112031b20060c1002120606040501090e06132c01050709050f03120a0809060106020d17040f020604060c0c090501051c0f081602030606010c030f03 72
    0x503002502407100780321112602c41e4050103880d0441c040d40c03044005003401401f10001413407170f20300d1011400c9a000810a141281c14403a5003800207509440c440e10080b41d4181b080d40f03c1400c00d801550802c90b051000c46d00280080c070144000411561149001c004d424480c601c25035000c250090000c004d0365250040250b80709000030302e55041d00c201d403c0c100c01921b2800d500c040d240746800d07141d491182c1c10030b08455008503c2000800040c9060080506a00054000c0d68411150304c0241145950204000304480b0307180e6445680b038030003001c806481040c007965032255601071f840010480700c0c400109650340c00099601e032080b03655140000205a40003610548160030b5042c001c0700076072034400081008103076603582d05c896841182004280340742540c1203840c0c11410034004020580d20300e00010f05c100425400c017031020201d03141090490b00c80ca1002000c020003c5881034031789040080c2401e669009400307803101662a05c0045450459503040280891900c12446c80500c0c030990091 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 660323048 1250 660321798 660321811
    0x90f030a0f0509040c0f0f030911130f0e01020306270f04080c060c0903070905040803040201080916060905091f0e070507050a120e03070b07060b0622080d210203 71
    0x62515041c10b02090030786005c9072007000403c40050b188007000794005060950291316147c100000c50040d0754810460302d81c2e102e0a80326001141e840441c0700413542c0100d9401103540001c0003c4e00361809824017035001110124891500d07442800c4200c0070088407440920700002c2d260760182c4c0c801a1292105c034001e001030301c2c1d452091012940071b11040142c1d80c01200e1a080417522065040201407801003140c01151959052505101c002000f010640e90050750901740440d0303a65a80070a103151400b582e4020203001507003480054190f0704045c0800c1519020f484626159564500301e41003c2e4054021120b03940c0c801000f0410b492001c10015000800c1d0300d04a8500045074030380d10f242540500c3c0c19070350351010641c05e211f0380307400500c041c613103a0065020340500c2d03140c0340b010000781c0200302014190b217441d0341924040c0d580344c2c0100e0300c00341d500080d8030481900c90fa616018070b0025005a401d50b10450842c219007901070040700d2620524001503901080e9074440d00c102a40018245 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 660324298 1250 660323048 660323057
    0x3030c03130614010f0b09010c060f0905070e010603050a020f070f0201050405040c050d1404050a12090b120906060316030f0213050c0706140f01090e070503160905090f030a0f 77
    0x41001a40074043c105602400e90810001541020f40041c0c01c007400d9440840603450811040205980018851203000d81140c00011190301400c800005456212002041d0340240e4001060a181d000301550580d03c2e15502005955100d040d94801c91103940d41031124100d05003c5200007410b00c01a0f44440c91062400300e05265441011034155003002d1140f8010540c0419150051012845071004800c15409440800d007043d80b1220340300c00c0e01031406003407003d602d0984245580502c031a60700a08203088030380c1d56101028103d548443c42038824403030074022407000c94000d1070006481050f14020b00c0009410a00d1681c0301b080317040e2880b004a030080c00360084c40107403480354860113100f112541403203940c940e114a440400c90304280d004203504140502030202e201808020141558404400000e040200301001443c04406038465503251040792200d02c01c4440d84840e05040703496402c800d012030786440e0305441c0c954081090540702e1381d00c144401e81380c0910540c00c05030f000003076061 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 660325548 1250 660324298 660324331
    0x204060b03070903050f1902060310030507140910060e060d0612030c1e1a0403030212160201140609041b08030c010c090905060a0504020901050d0203040f02190803030c03 75
    0x38400c040e08200c03a01c00100d1140501041482070038015242480d40500c040c182162945800c00040d5461a6004c0c0c024980400000c080c400551a16001b80d900801290009643d8402c03004a0821185016014101c0031010903040b0110150350380036a242a125102c807485010144034035a0041d64070b6903135251701c2d504000359240b00040e00c081141d009540d007205046960803c2401c020f8408a10000326040b20340d4800441d80b0200700f18039002c0761030001101c40d1202e09080b00030f0300901000401840c030110610042002c00d1036540b0031903205400a1164600c0d6111949201e00c0445032140c002c41135000280004a08031001440700840803030b603c40d070540760742840345182c000c1025010b2580d0340f00003000c403091f0803e90700c0c00241001d000500c51803801c2c5020419210b49849800c0c05540c0104081e6260380c021000d9810342c0380512021500c074a4503080a0f000e007040401d05074041d01d001490004420789595510302541d0101008618540721000036140c2030340024002c0d20184600403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 660326798 1250 660325548 660325559
    0x1a1c14190c0e0108061306110702090a090b010f2601140412140702101d0d08040302040b030109020612131a060102010b030706022806050106080906070206150d020406 73
    0x440d404203a901a01803104214102a0414802c1906070824009507004d40104015194040d1070364400d5503000c800415500d40c10060241c42c0d000d4454025480861f442c1081900392256001c0c690150041d00400c2c003690340c80409212141c11030191800d810220b904030f0f1103844080280b074a005078050700006151103030005006034103405481c01c4a8a01e0a00000507101c0e90005208030b0001001c90304600d000416070004115462200c4503e05010506400e01201103851043c1340d15201e01130202d541d00341c03241c5014400f6511502007207101e40d19200b50206181070502c00d40c2045540501a94981350142c02a801074030b80c02060302009030291200900007448080305603840891100c0310040908000e400642074880803050079020b540442020003060350b00007030000d542c000c5141c00c80e400c0444d400c003200124110b400040c01140c00c041c00010340e9540f01003000d11444403201960015200c1880132600d40c3d500303a0318016120321540c01912186401c0c0400c0508900c02000040c60ba0fa460 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 660328048 1250 660326798 660326833
    0x106090519080118150b0a092003010f030515010302152d091e01021f0b040c05030130032a060b10030207081209100e011a1c14 56
    0x4100c582a0100184815410420180c030011350321280f07040c082c4401d0440201160b094002807280408c0a030b2201036403030007181c01700902d070b0305460141c40c200d07a00e6071031b100d4090081c20305110403540c42c41288d036881862400381c0705440c181c0764001c00c41c022090741030340100703030316086602c412a110266010206001c04085110340700c0300d20204907540c4910a20302008654541281e0340e1484213040d48048216170b03404513031003803205155900b0400555409201c44010300c020b98030180c100e40ba25401d00401038004000d14100c861142d0400c0034200742e0f807030b9400070351003201e0201d54000342d000901c00064002e005d0801072120040081c0900381d4003855688c41c20a1f07042080e10605e6540700c0101d403d00b0051101d91800d00c031820203601d85407003a52090410310841c520b80d00c0c41070906001c01d01a035800d020020702840c040704244100014001120700074003a10450941c02e940400c030380202070030802245001c0781c020f100078484440c0d4036126410780e806410b14490030741c042c51107010413083d2403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 660329298 1250 660328048 660328061
    0x20f130e0f070516080c01060b0705010f0e07060906050a0c0b1003110f090402090402030a051506130c0e0d031e020601050411160f02040906060b2101060905190801 72
    0x9495030329020341070018440509480c003400200800c0003c00901c0c1400301400b070000d07902a844101d0030380d00c0c0c030300059090052a654208080c060310020700c01e002d1280541110702c1c0703840c4010301045180d2000300603ea0300c101d0380c80b0310400308011030801c02200e0300400150014204600701500c0c045019a11000e01c3e55044800b4090f660340c0400500902c0f8003009408c5000c1000c0c2c0d5604224141e190014024080c0100001d1143d40c0703440000302192030612041c9002ea503c10201c544400c804130203e4040d81040301c145029504c81628404030031614020320403071014503200e0340260f00e8107500b4000028400c02d825810322401041540030500e140000c12002e00865010303024550410302004242d0f04045035210303075240e061116020040101100a0740e00c4c0e840340c44c81050402920224000e000b800c1000760005280c075a00144810b9900010407100220513100b8030080583d075046102c140080c060f92001612034003050205052100078400341c0406c108904503480d650307001070350a541c1c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 660330548 1250 660329298 660329309
    0x110f0301060c0b061005070b1308030403090306140403090603052809050c060f092806091401110613020102010207060213030b012306090105090406030c150302031306020f13 76
    0x80c0504102c20701503c0c5502c25002075003120000c0201c12501c900514501403040054110b00300000410342012a0201001c0101c0d444070070203450f071070300d828054086101480b040d030300d46081c008800e42040c0344042e00f621540c5c0c145c070b03078031501414800300320300400c4000d1401d505107105550760100d60b03184500d10080b140d28100d01003003071522884d20504185440707a451b40920803d01882488140e2b03c03041d2112840c0c03c1d500d0381c5442d1100407002001140c0d800c20000d01d42c40303200b030108001c0e07402115071059511203950034001c101a4401120348038210000d002d070a030440c402085440c98680600000140148009801e0a00700e4641000301d90103040840e01015a0150030420003256030055401010f81d030b00041004205003001000c0c0031103030180148598000200c04000c1d0307000d50f060300e040341005402000b0302c4d601d83c035000c02c0e000030324002d12489141e0300041c0c400461280c004c60f80302d50300e03c00c1d1050005800d55121000b83d0022220070250110600408000d403100010941c000d10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 660331798 1250 660330548 660330557
    0x503012912040f23010b040203100b0a1803060f1404050d14040e010e07080c0403050d1b05010509010c1806090b0c210a090909030f181a0c0f06011503110f030106 71
    0x4d01c840f0b851421920010946c1e40114010b00800004d0482007806408480c0c2104400760740342c11100b4100c401042d103550003c03000c010203d000c001d202899002041c4200410b900708802400981d10484045085a0040103648804481181280b042c103545400072000015281020342300c0441c03ca000c07100360004002e501e605020440c20b1a4050030403a08808942d6000349458115282d081d1112940444401444041c401e0b01304a083c5e1122400c40c210b030440001c2200b0f00748801054007812484017444000707582e810182030100c1031140f2140480b03515480307024045151000c4400305070813400312120b0300e01881c1c420740d0b40e40b041e10720300490190313001880b96541d541449014258000750b030072051500340317003500b142e002a4004902c0c40480186041c01c1c00ba450384802400c042c4190ba8202c400388041150b007502ca40e40401000e4200207540c407007070f600f002e024010314603179555091194040c1081d040c201145d07654001c1d405180f0420190340c4480ca4580c0140003402690f1080e484040081d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 660333048 1250 660331798 660331853
    0xb0d080712090e070809030405150304050c0415050f030c0409050d020709021314041d03250201080105120307020a0b04090f0501081b010908010c0503012912040f 71
    0x20040511040d5041c4508240c1c0032282424003042d002c102c004c0c130490034091004040340d03841c0010801e8038000d060041c02d00c84030030f65440002e45030b0f401c00e4a0803507443c80b034418241c845160034003030590803500031201e80080328500b50402c8807101e60301e180c85405010744000016241c8980c0180c0081c207024074010070030100e5950000f860f00040e64050b1110038414403c184140e042803020404440003480f4045400a030440010003d1038440c000c1c60b805644185207002d1444084054800b03038400400540c1c1d246012610101340090800c802400200c8101c0140b1641c501103d45600c10804441180d080607481c0d404a004030045030042c3c800c0c0d403c0406e0401c11044140900302c41c118003c0c44c05e00c059458001d000740c0d145496244100b00780185202820b185c4d20840a44005040800090000d0084010003500960085c06068483d124449404400c41d80544070356032000c2e81603030180d1070030f1500801701d00c45880c064030840d054801a01c100e0003040e540c02c2c0303003030703079401035140300d100c2c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 660334298 1250 660333048 660333053
    0x2041e02091003020f04030b092b14090307030b2503090209090d0804080306011427010c0305040509040809030d0e040b0118150201020c100b0f0603010311130b0d0807 73
    0x42d00b1000260200301401000b0640444540f00207441c116544064400d81c15210988090b003060000c3c01003040d003554200c0903d800003110b40f000355000c400e540301e250000194811000c1d043c851407625a405501c5080100000f81c6490300071544a0f004110980300b804d038181c900d0754509a80c500c0c540c0022b0301c4d1003441c000d6281091002d60000707000340c0246803607290904040c200f080002d2010f00808070120010752039900032000c818107003407900c09a40ea264000001c0706008078505c00d4401c04032100421000c0c4039405541c4c0008074982644038941414540020049031200040c01100d5102043c0030002d065103080000201c00a034a48032803460048020501c000c0b1225006413034100180d96640c030001d03446440c0ca88040c0c0721510800f8121109035070069029115040c2000e000c0c0c8128121341d4145500c075805006005001c442070308051400f00c0c200a0741d80401e010180c64406003013104461481c188510500f40b155039600031408100b5140051f252507a50783e02518040000203c00d000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 660335548 1250 660334298 660334309
    0x70806100605210403030b210d2c220903030e16060c051504140628020d060b180a090203041e050a1b18060302030309010c02041e0209 59
    0x34001624166082c5503c1c2244080d403400100c40c19003c0105542c00308062610a40007851541c002520034103010710f5035951146030405540040b072030b070b001f02c000c0090310a1003160a5800c0500c2801013032103400942c2e440d65002c5110508041e846a1002c0490b10b070541e4081c21032070701c0c0485900c0080c0300c2006003005420344541082050700c607000301c03d400341a011031600000c00c0d1160f07458100d400840741c1c506039250480c1c00000c8541d950a8804110820070030318804004040c50f02c0944036607460342602c8030490003c0344480208898546081100c000740c40d40a80351a6280c0c5502192807644c810003401550300141601800c88211207071085942032051100740102440e0700c0031407640c5415110240e48010584806400c40c0e00046854103120301000031820160b004a150684200b0700681136010340d2403442000e9003089082506a0710161301c0c407602c800c90350042d0185d07207000e000707800444403401c45140480e0701c9036640c1074240b048a00d2510304000810760340c10060796130210104004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 660336798 1250 660335548 660335581
    0x11010201150f0b1c09080703120903020a08070218090318010905090c0f0f0f031909110105030c1e090906090408040911040504020a030b1f0914060c070806 68
    0x6244280c41082005103070030454040040f61520010540c0321000b0311820901803e5203520b81d100305080213142c60501c40118001c0004034800e441f45241c43c620840da0034140c84461401801580041d515480840c0020000b8023116100810441c40c060400d50142202e040a0792080b8080e070010074110101c1c083c0501c202103007103007400d014048a203090001842d030300000301039260782103000ca503422001e5080003c0d146d503030700398a00458451407804540e0055400c2120103900c165030a9864144940b6548a414242600b02403040c4d0b19281160055482c1d0b0300142021440900030050300c0c2a550948004107000ba0b20b881e20166180d80900410501a4000e4003241c07140040300280800180c0800c00c8404445142d480481c8480001c0700345100d078081d50340400c2e007040c0002140c4182e0ba030b00d03502082301228111031803044d48071016150a80c101b0117140400224610350000d1103150440e000300081d00b140240781615040795034040303504110035a0b01c05d4134070b075010600340907402c941d842129 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 660338048 1250 660336798 660336821
    0x604020d1e0e1614040c031b031a0a030203100c0504090e07050301060f060903110a03020d060516030b0d1e1b08010c020309060906130509010b0c01110c0703140f070311010201 77
    0x1035903c50501e107001e500001c1c480c104c984250303a1240c3ca512203c0c029044101840c401e81c524002c00900c1001c003030064091000450f6a44070210600c203032618100007030711f0559401800910001d202c0e00c0000c1d000301000c070340c01c506026050000103001003240c02000a45585070020703009047c41e003010f25094407407641203110741d008507100920207240d1109072402180c0d007007a041e0200300c0c5100086140e03007280c0e03003002c1c0d000180c04100d94140700841d00810b0052000002d60441114150703c114100e1769180d03001540680c046e0b00c400041444445604080000181030900ca41c001c0d41d5020181a94041481819500c859003003088082c02c6c0f2981c09a1021030000e90b2426505c1d000058140c4503c0551911801c404104c0c006c8071440d10744048080c00c0d0140001c4950351311058161000e801c035104142441d030810f02d980c40500800c406591502c10740400400c14141144c1d10400200c03010059507025102d400c0c040080b4401c10803a0b00021070051550207081202140020709592051404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 660339298 1250 660338048 660338083
    0x90503070f031e0314030a020d020d1b0e031e070801140402030f07030206090d140109200a030b1b0c030a05070b0106020c100f050d0f060f1208030604020d1e0e 70
    0xc43c000c6a0048107000d6188910650300395a581c3d441d00e40b100a00829028240b071074030100c0c203d6040041ca9120400d0590189031058040055000480d24044d40c80d4000d42c2503001032168001c10181c90034100550203e0300c0c00c0d070740003d07101c01d82a421145503280d04045015488240000e40c10280440605c5000e003001a042d807904503000700b1170303612400181601070b03803450300040300b4009554505022100710100030301654889041460801d104080380042101e0400510072492501030f002d0320485e90300c0700c00c105860340d80141580400502014011490804000e00c2000325010300060800130b00c10b0b211903480744407a051000c050340e016003145081d580200388400481d40c451000c410440c009140070042d200b000c1908442c0c3d4000d202200201c582031244803417500466421500580e104070140302c101c103950340c82c0c64200015000e000791010804001066450901d9001892420511035020940d14061503560f103260305640c125110080e40e5000d04180030005025018111102d40c41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 660340548 1250 660339298 660339353
    0xc060c03040927230105070c03120212010b070201050c150a0c11060609061212030417070309030605090a02060d1d0c06091221030709050103110d0c090503070f03 71
    0x2039a041c10300f2200750180031071540800100078181080c020980c6003012900a20050601c090054410301c02c201c409c5010804006080d13054100c184241c0e03551005503107110b11940d1809048035a26400580141c1c1041802c01850152107400c00c00214510342070107000c8900d00d8045881c004580b04240c414080205441070598228000940540c01c42411220940306842c1e000c00034103040d0042c0d20104c468000d19004050040302c0c00c024603c142e001d500b41c9540c0c1c000f001da0030013a81c0314141000340490401ca0085c404140d1070790003079a200c030344e207000c85911040c07580015106800019000c4c038086d40710700c650000034000c00f000c403d8621000c4001d0001c0510840010618001c1a540500403a005000001955000c01ca00d440341c0030000050180c04502e103050b1b0b0100d500403219080800d00134800011594483c2c81045044020111203600307042c680c000c2040640144e018081c2001144400418203580600004c0002c0060488404081d45140b40610f140c100302c6400744030078003c0c6034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 660341798 1250 660340548 660340601
    0x160e1912150903050306060c010b120a060e0d0807140c0a08041706190c0921031d060307030e0c18070e01111b01020a0602030109050117030a02100e0c060c030409 71
    0x10140e0f504201c08441f89501c8122000b1041e0050107026403040d480300c0075000003d01a0380104030b0700c0480e07008240c02e000c03111421520b1540c45c0950903184001812040c002842c152042c4200c0841500301c200342407418100c007001920300000700f50259020340e0000340410115010a0405901707000090103040e00345069801407075031150b040e80180d11240c0745c080980f0150f10411225002e020409a401001a140403642101d01400c8030100c012840120f520000008584104409810010007240c650798400f20100c02610942c589a045c40c41010010f4625030348201c0000d1000c10303450300c0d00300e061400520091607810101030351418411040c0c001031000d03001150303100f50f10f00c00c1d000520344003425500403841e10401280144c080c510220011500074001d40115049840340f00c008020000d019050707544901c2501700340005648003075400d582c1c0742400c2c0c103c000d10086030029522100040301c00304409034407454100185070000502801a48540c1c40f8500c1e1440803074030548480e0f034580 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 660343048 1250 660341798 660341807
    0xc080304050a2909030c04050a0e01050f01030f0305070c0503031207020d0c0201050912070506040b0c010c031a0f1c05031c020f120a29030f0303160e1912150903 71
    0x800c0c403c81e4100003502e001a4804205040b0f4401c0f018100f00320501d0026510001041b680e10040c89035405c0c440424003909130180713601c0c1a2a0895680203040c9156642070301e29500c0504125940e41001c0300c00905541d0a0025009400d1800d210f00c181d031030011002410804180d0040050195509041d400b50760300c1015a611207030290340140c0515108110a46040d0303066100c0350307108070b0003c0c2c0071405520104c060300e15240581c0080c0280041d400003a000c0e2400b16200c0c0071800070801c1218068680000c22502502002e80b255200c6000a80750740c00b8042c1d10082660168000940001200d202064103420b413001c0050450030401c00c604036500c240b00d81c0501782451006600400d42d4480c0c03551000d54065146c54000354070070f40035280e081038862801500e510a005400614080300004000c891050302610a03c03507804005100030b07204803641740c800641141d1202082081c1d4a071106a490142100c1d51903940080428600f148000259610310004141041964000039400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 660344298 1250 660343048 660343109
    0x105090106020a0f064206080a090f0203030f121003080a21090609110405040510091a09010618020a08010902031f060e1c12030b0604030c080304050a 66
    0x1154074131030907451604000001d0f00c0908401c041c0d0702051a00b1039400341d21028040003040c001c140769139440e0703040b59000828405174454900802c40d03180c006182c1030340690012141511510702d415030f406294000c6891074000d5030301c840c3c460304005078100004e6001405940e120302c1442c1404400790550352555441e000e54600c001c244000d1451080c1c0312003190304500e0003c0e2001c102007201402a003841006405030800546003002c04001c4140d0380e0500d030040798821078000004195404032001a50000c0c4045c031425900c502c0c1e60381030b4201c03c00e410083c86014140ca41c0010401c581020303000d941aa440d0740310400710a00c1000b00450700d5420001d064110f070128400103807a0703690f10707110501030341800040038610f50000d4808103a494005200f95120309082d180342c1c125070349502003001401000c40c8090840450360032003400746072007900004084e08000d4811750403c0c0c0d50b0303905c0002d0413038030350486159504040b03014801070030310441800040c040c2c50000c4085141e0030003c200500355 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 660345548 1250 660344298 660344303
    0x9151109030c15090f0a03151d0a2006070b0f0f06090f072a03030c030b012303150d0302030a021014040311011b02011b05090618131805060105090106020a 68
    0x891001181c203507551b0303411079030013560010801c103401802024200020401c41c200544060346038940241c15034800108180c1c015070205404d84000c03c20300910205031240451640d0000040080200240140e6000e40c00b40848400f2145982006800420148401007510380181d1003441044050400038554907004401c40c103001e880c125000b40c000c500003070404441ca080c180400b5601040603456400700b4100b00703440ea400c000074024440116995800702c2d103100300c0d0580d420450915000300d180199007207207080840c401c0703504040f00410110780d640034040e80503803c00726004000b0b83d018401d441021420140800061203d0301c00c040d10304401030030203420040000300800d010742c4c00754051000e12130044888031003030000c448024080c0a20281900307180100e00d40c00d80c605c0e400303031083d207005140061059080c5030f50720000d08000c0074038207540c40d8051406a44d040684071035202c1c00035070211b1841e00800320740c1941051441d252040e480360703000b10b240b000104445a80031401c14484c0360b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 660346798 1250 660345548 660345559
    0x120f0903052506020a18140102030409020f1603110d08040c12060905010609150f0806010b0d0b0a0b07061a06030c0702181005030706031e09151109030c1509 69
    0x554259605102d12001c94000b0625032002604a6800360032030344c0d5040c400c00a204091000761565448201880c0580b11180968000e210600003070010703402618809008016680c1003c40280e0111813030002c1a10039008515150a030800400c401e0041c1d41c840141030030240407a0425644140c422100742c03013820006c0c0c107168408010011903421030a443c5800c90024406940c440f10440001c000201c84007410011154000811138041100e4034221464200681401ea02c0c000c01e000d00e80e40070400610b043e0f617813003c0e001126a24036142501409440d9a480c4e03c0f242c80c0d1502000f294020b852407481001801e40c040e40c00d076203c404595000b0031819105840e040c540c800315071030b00118940081050010303810080b1680c460b074502d2040b51011001c40707090680e0f03108160200d900065845000c0c11442e1031140c0d0008050700300d4003006210b00142034840e036000800c0c104540d0170b10b2070340218101c0040c6001140c5000c109841c1c001000310b52090006020b02c03003101c02440340400050281 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 660348048 1250 660346798 660346837
    0x3090d08040503070609060524100e06040f0f092301030201030c1209050f01052202010c080d1a01020d0504080318031906050f100815091606120f090305 67
    0x106051081c1d6046503417001c801c0c48296418502a0081d1104580030104440e120f0b140714102c204003030402c008641d000c1c01400c8259815171003100e86116003041183c104000708000150100801441c0b4000d010064100303404a060031001010342d503089030455072415426500c3c109500c1c2155103641100d9090900103a00c0c0d1802e20255a0760101041c941d2036945042d0300303801881000f06040e642121414002c000d07035510041c181060003a4180c3c50000a4032581410300103500036047c103139040340910b18982c100381501c4e48501c00d580c102c81e0600090550a6035102440d601009104043c0e0100d00b0000d0415050003005a902d004202c491000d00750619005601c6403003e0110303001d200b200700b00e802c4280d042401d00e44003030501603845022031a038400003d40b2080d04400050305498000c0040c0c05222016100c0044111004c0c10414031402401040c208481c03035030682d0f1000f4980390312a1805085440441e10480e290404401025410001c0d00f10004c1c2c0d00608890940318550525040c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 660349298 1250 660348048 660348053
    0x60603020d0c051c05101a03010e06062407030309170408010c080f01082a09010b0301140f0109060c02040e3301080307031b080a0905031c1407020d020d0303060806090303090d0804 79
    0x2000926001d00350527510740700241e4181c20000c00c440f03220b071000f034a14510036140c101c18948014030301c044025020b4030600100000074403d4100c002c1d5079020b08104549000c006d40d500010340d20603845004140c3d500c03441c5042d0340340c00912003035000d070000321810401e41c50708040710384418111540300d1030400c0c2c82226000b040da004200034442031020f017502401d580c66881e554851384c401c0c00307004941069024100c206241030301800203900303010380d160b801181c603001003030752448110902280d2064849408080e441d00400242030203400d0400f141250389410540c01458010340d061400c1040700390780050044032000012035500e07641c507140142daa4841c081943c3c4000401d000c0013400020001000c0c5040380e481060401501c900b02d00341d031002038000500600410101e10a00301213544c44200d08150341301ea101810f02c0314000b038440c1003c0f11051340000c00c41c02d800041100425507900060080351010400680d000744403100451031410b1011059035141840c100503400c01c0455070003d000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 660350548 1250 660349298 660349331
    0xb0a0903081b0d0e1501150809070807091805060907380a023f09030d03050a020c0f0d08100602030f03040c051309030809010212060d060603020d0c051c0510 69
    0x1003240c00c890210741656161f5007401c040603100c001c240b00064140c000716099000104812040f54900001010380620380b40c409409000e402c015400d0b21a00c0b4191000440c009006040c40307628480050034049042030001c8a00b15014000d0442d013881104490f41c141d484003d030030400455a07058540c80e09402c803c12842d02031040d1440c039205c4106140c1c02c41c95200400508851311026440c2c07010074400042c1c007003443c0511000564945c0c020b040b0144142e0080e40000c0c2c1200c100000985400e0840a0081c0b402642c408408800d40c0700b81509809075500100c815048000c81c26180030151030700c2c0d4025901d0040700e400b070b000650008085410000003402d500f0060402426111500192140403c024881014158003080350715000504a000603c21a01100c00e60280d580303454603002c044c00a900e107070b01411205a0f07030300c1b680030001d643c620181c060700c1c611803074841510038140000c3c804114580310742040c0c10981c004000f4001080851100526042102c0025402000b10074241 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 660351798 1250 660350548 660350563
    0xe030301090e1c0f021e030a030b04020904091104050108160b090f09040302030a0215101712070803151e010503040c17011d2b05070b0a0903081b0d0e 66
    0x4403481c05010191000b0380201d03264005885079006d5443c80304505040c0025440b4424103400560410010264028000d901210030386a000d8801410301c020240810200d400c000001e07101d41d092040e0590080c60103000d8240036000c90f07005000c1c9490846c85c0285810014080c401b00c00702b0101c0da20300300e51100c11502031108030080030740340b041c1411708020b900c0364005030102005001e0b07114502c2031a007080c080d00d40503400102c0540e004510703107070700098900054001e99005018071080d400e400894800075190300c0f801126146d17030b41d0400112541d1102c685007030980c0900c01c7d03800b481003210303440035482c0300e8002d00b03003001940c9a4861511408142d4140c10981c1d010030701c4403403401c00400c1507002115030384d440145102c40e06038140d01542d075541c2490b4070700f04070684e400122140c0000d5491515081880d41080c070308044d070030383d1148409002100c1c044000703a0344000c0301003410b9101380e0b11a0072000800c0d01418003075041d40120b160b44101000202c105d03481b4138150480340703820402c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 660353048 1250 660351798 660351823
    0x7080a0b36010b010c0c051c06020414010f090b030601031a090c0d0b1503060d0302070f1d01090902240702190602010b1206010e0703060801020a030c09090e030301090e 74
    0x40c0010241c00d0310680000480050a080c15881d1040e120499402418001003054010900e103418030310302001c001c182d50541390440030407140c11041e5000100c4034005480600344540f9881342c2a00075a00041002c510018081c08000140200708400c5c00004101d980010080c64081414016180c0030a210151a40c04e5130b00800c800003049100d40a1a0141030140414901844222000c0040003140c0e0820440d01c0c01c0c4a0341040414203d1a10b59054981644240142c1d0f819956409901255180d0360f48030200054404181100c40c0c4404203900c0d0242820000070400b40d40650080361808288000e01c0021805032a1b04081d940540c5040c0c50036298000e00640704007030204928148540f00c0c0c80742d0b84c090760030311965200a2074404165801060740f10002d240700d03032a024848044d410f01818900506940e140d0109440c03600380020503500d1580d440c045200c14801100900308412a8442c0810f145812502030081c070020049a044540107880414841c1c1d4a251250502c0a0110070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 660354298 1250 660353048 660353101
    0x31a040201170708011403030a02030405042c0c10091404240f0e090105070c060c090b0f1903060b090609130e1f0504020f121e010e010e07080a0b 64
    0x401103151342c031000007030588412107403540e032250006003456940d000c0e640341c0102580041c0401c0c8443d042035400110800441c0301c00c0c00c00e210044103800008551020b440c41c1c01c2c0c01401081644e400d0650010303914188500c5d140b60410302d00781c0701c0e6424260708400300307100d10f4444c0340140e00203034032500f2424010031100306100010b65400c2d405a01912512030f45c082d0034407490000ba440801031050610540d5252141000c1c1c0302c95a0f560310042988140c030708180036405030081940543d14020308088800740c50015a03807120550045c00701208050000d00701230503c0780078004080c03801c4c15903040000640e0880e4680031560000744401038142d0702c45100c0c9207040400001800001750304c5000e4110460522010035005e211001941c2085902079002201d0f0000030744582884440143c0c0d0242280035165101003c521b11201c15500c0d0540030042da458039800c001c804002c0c420500c40c140c1c40001080041d241c00c44541d141d8084150241c4803401640004040d40c1c81c100310800056400c3c243d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 660355548 1250 660354298 660354301
    0x9070e1207060e150f2a0706080f16051e120408070c060e0a0506180d1b05011b03030209210604030e0d0f0b09010f18120801031a04020117 61
    0x400501c0d0801100083d4401d0b84071212400d034542582c0229411013845450203450003500003a00d054010304500614800003540454400c481c0090044d1409058a590f90241504000030080c00c00d82d4007800d081290003500e400602480d030407408403002c0c0c404a060410111001030912001c60043c40840402051403404010410511304010b180c402c1c442c0c84418900c0c3d459250840e192181c010030310350000e203c000705100a00c2c1c203801400070005180f02e407c3c120500600400c00540b0210000c4619003c0480340e00440405425210302500b030038a8903049039640511380c80795000101c00d014060660000700c08040340c6503400e01c651100ba00201d03500c40707101204a20340d900d82d000c40d000d40c002441c0c03940c0803009103000100514019089500c0d082e26242c641c46009104c44080c10110081d0b5035a849104954080d000307514401da4810b10b100401c0c031142c00c002038211500f400c01c1040181d03680048c00010055180c240c104d003d010b064a106581d60f20051312520002494400c00d040d03100c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 660356798 1250 660355548 660355559
    0xd1d0103060305071403120c10020724050402040b1e0d0614010b0a03054606030c05120109210e09011e0f12031407080309060414070509070e1207 64
    0x41e24985d8104041e001c076038032648414420f1590780500342d1061050f400c030381c1311045584c107107130094210580144014802d1040004e016886409a1401086001c0e140c4e810131084d4a401d00c205142900280c90f20002202c00c5415446d01151402d2024803407290070b0554411b0106035400b00125942d032008000040d6100d41a10f10030f5000600c1c1070b4000f90030200000c0360808240c035002102d0516100b13416101d0703500c3d000315250a00020f040d0103012118400281c0e9120203004410085008019211030282001c0900035510341030b841494040e81006d0070034000441840c2044d00072030003258040010110682c0c00c43e24460700b1030080b580109980d00110710090440c01c1c0150110000b451007124035506e22010104407224071070b803080f080b1030a40c0c031008603018001d80910ba29825406610b4210191786400c105e800940d0460596440082040100144101d4044614101700e0003012100c0c90000041d80050b0010084810408114148501a26a00480c1c4000d6903080c066401d00368444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 660358048 1250 660356798 660356819
    0x30c0606081e070f0b0301030818220f18080309071d06030c03070303050406050a14040602010608100b060a031d0d031e1514010c0602030705030a0e0d1d010306030507 73
    0x100b800c08035900410714002108014240c0340b200f00c2d40e120030301ca41541e2a5031103080b96070700105003203a08007140619003c0613a940e24600031001402c1c50040908040e0440740d44211b0b500e060710191443d00d01070840c007110110401d80305200b607001800b240c1c0c070380d90b00f2030309400e000c01c582c440661220344a40300c12036102c041130580e1299201350120761100801e441016078a0006e4800a0045201084280810380c0310320002d103032107034003070a00409000c0d140b062442903901990203000143d40d603500900c0b031208288481e000c001846001882001c0390f900010340648180762055040c0b40e0740304444c40c071059600c01c03143e0b00d161003c41a10701103800e012002e8007070014000c0413810900504081d85400c0c00078414441d1007030326905200249401c0c00171500340926417500482c18000b81d00d450f400083d40301d00080d44a444075641d00c07500c074100884107506035014401c042e413070380d000306129a0702d866100c01c50400c038241040345c0c00c141000c40e000603801002c0c19080540350780149000460ba15070312 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 660359298 1250 660358048 660358093
    0x1e06020a031b052107020a0b0406020c07320f0915010f0c0b04060b220c1206060203091e0d030201060302030d050306011e18090510080102090d030c060608 68
    0x240c80c10422040c503002c0c12200c6104d50385001c1203c002c0c110107078000f8101615003980c059400e00417541109030075100c07034210080c111011200c0c5500082c10764440002031103241c1c0100150307094040f290b60030703042d9800050992500184041140000a185980e0391110048116005400c401480c10f142d410691905401c99100303000c1902d0b4102c1c1801d107403081242e150030b5600450325110b2a2502da4881d0003404000c00701543c4600c00100010510102c40c4200741004003c03400014400c10242004d0200c0c05400c1e207822104d07290107010000c1c2074002c400c80d2500701085518200074082e2010b0318801824000c55142c204100ad0494010580c05501c11020b4900803400c03102a254041d9044400313101c00c50381640000d0350301c921012000510030a40d425a0fa840c104208116803040307a40015200381d5205c02d154070740711000d2010b44203a0342c182030050f0250b08001e40c5805603000101e0010358401100500304802650507400344054ad40c03280004d0300305541030310340600712044144072200e071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 660360548 1250 660359298 660359321
    0x150306050405090c03070e060609061b0f0a0c0605310801020427050402210c0613030312050702060705070c05031b0a0906050901030303020c210417030c0a1e06020a03 73
    0x102c070004a002c0901f011814842c6400501180c40c108180050100a421045210200a00c4030403150b442e40401c2c480082404600002400052b2090800042c20226a0f01c2541881010007000b2031011280506007891111510740c0c04504402c0c261480a0030669071140c10194800305e40443c030382c84146418010b0480030300640c0050880c008201040b00c406807802540803c02c1040f40102014001c80f80c1c11b405000ca0580d4903009404001c0f40d01940b0031444400400300c0400c0c10310405402600160320701641c0703a1304000b54a8202c02c0656a800058089400d019003c60307c00100104c015519000d01000380a40d101c460200d0b6060000c03484020b8403520541200300302040416442c4194422540b0041508130264a1900c0036802544491b5800d101401810905040c0c011000c071401c1008608120311642d0750b190070b20744081030410013032084058100b008501d4040700000380b0094426002105115110b18102c01c1501603084840010411400400d4882006815601c4000b6240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 660361798 1250 660360548 660360553
    0x5070e150405060f0114040b0c0307230d140d0603050714010513090f020405120c0102010e010e06010b03061206071d150d050a11040308070c060e0307150306050405090c03 75
    0x40000c400c0100342c0b401203c4040d044200c030300b45040e003503101e0751070880c1c0058001d101d58a40b13621521131400aa11a00755422603600019501c003c0080c81090242e001503030030f01004051121140e2980c40702c4c03460124408000400c510302080300882001c803044000a0f001c1003100c2584c07403a02c185c80d00006d1054001c0c844550015140d55402841101c082c030b07540310014240310341000d00d030310002c2c402445082c0c980342d800c3c13001107840d898190302c900340022480010210013590600090030368152040030b00090f4104004103038440c030001444c0c0e044d507495441c4941c4030b07030704d040c007088824800d694041c1c0c261140005210a803900310806094914081c42052141d036084002e201824901c40401d02c1c0c200c0c0b0810440c00410410fa129031340001a100000c103190554007040120764000390019110f40000240c410f040189625244d0010b040d582071001076140082c00103910703140e4a1068002c41011410450340041c881e078441c8001c0d02000b80204044e0510491850703464039035004140c004e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 660363048 1250 660361798 660361831
    0xc0c132a020c040e1024090f1b0c050c0a1d13020901120c05090106051803011506020d09050907080121020301150611010b1c1704171e06150d05070e 65
    0x1140c20308286c540901404003825200f03481c1000d414000c10a80c1095030322a5920b01c0071440274050b002680200f095155031714602c030b00950510506105d540320394503200d20a241010000f0120501c031036848501c80003503031010f565460300d0014403070504560003940501140008240c500100900c200e813030f4052406080380795141c0c41402030f800802e00840f00400c0303041c0880c651105507041072101c988800350010814040d10307079140f003500042c1c0d004031015030089810f2001d0241c0c000300203001000111041d0041c2c0c20480d8003d80500c03418018501070385190101605040100c081e8049400c0d4049d0003004601c4031106201c8480c511405800d0014400e00342c0303d10004c50500410b0400f0800070504c42c54089440b41c400420402100100c2d005a0290082a0909108800740008100b0180c0f01d81d240710040f001c0e1030804c00b2851030030040c1240b0039909012010000750341d541c0b2014051041c04098096400507001244034031000b0000e201340340c00860160281000c2d070b40a00d01130204840c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 660364298 1250 660363048 660363071
    0xe070e0c0a051801021606030f0c03090b060d030903240b06031b031003050f160803250c050603180601080a02090415060b0c0c132a020c040e10 63
    0x40d4800d5046080025800384280000c141080101e0310103003c0c14011600310080c644071000307001c0d0303955000c40042645c88098001038040c5010307a1104002502d42003081c5096a03075901502c401c0a030082d03000303924800c80c0200301801282c120300956080809500000c5544500c4001e00e6015100c03001c2c00d50400341910524280750040c0ca0154070700005000e1510503280952108e500b004017000280c00b800e03000040481d00601c40d084c83d40044134054041c2040514545c0b400a44a42c40710301141c1c0104142d0788141880640c5038180103c025a02c4002c41c407030b040200b41c4205036000340d0b501070030000030301c050f6400c40154011054034030b409440080c0c2e60f42c0181038940083c131002a410483c40380015000420301040322004410442c4c00081c410344600c1910b402d43c128400c40009540725841e86107240c40c0261104255100041c4107010f44010038000c03040b2010403000d080329084007490394038501c900a200161449401410400440d8032208c80c060381c0b40040550444d02c146043c204003c2c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 660365548 1250 660364298 660364321
    0x10b01090e150f0604030302010506030c0306070f110307150b040e0d020c280e0109050906012115020a0507060b040608030901111510030318050109270e070e 69
    0x4440a11148410325600c07401c0114492442c0c45100c0d5001218007070461031a5548005840134501990000915280030400e2614069802440521036405a0200035007580d11110f020a0803080c0d251409031b544102e0ac0340313455400748480040c00307450014042780440e42c89510103988c1c42c900b11401d20040e4a0140300b96295054040c000006810514000441d82041d108842c84000041c0700c0200316081c42c404000f44140a4000e2640203c950f40100808149405881e401002d04000b52805526211401d4200c00a01075100c440c80300c402d10010500c055000c4111100c03000c510190768a0040702d00080c4243d200702001c17582c1c41e180c04022035141c1494807412040d00c20a400851030035114000556a82540341a4100e5030303c24050700000b1519843c43d0340340075002c1d6440441000d41149000b92142c603111855055110250300e0070440c580e1b110840c501200c2a00c82030150700d00300b20b1130752160007441d1043d412840d41000c8101c0c400c4900014280112810740c5481e00050310703000d0002d01d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 660366798 1250 660365548 660365567
    0xa080d0f1a04021803011103041208060108060f18070519180302010c0203030d02210106170c13050a080703050d231309050f0708070f050d0e0111070803010503010b01 73
    0x1e00340c06880c50101800d10354002c021420340441c450b0602c0c1c0d8507000085c207588050490032107141c00401484200042c40404001140b0300f8209121207146c0103000818688000f01142d20a0194610241040c0c5914035409001c00803044548500e1400075805051548102c0d04004203210f045210841d61b4401c83d4809880744d416a04200d100786181c0045441014240c1c003682d05000c200a2401c2c0210140300070100b910008001024020050290521102050307004030244401000c40401c2070300c5880340b01d54400a080c082c20742390084a2450100021260092600107022003000301d901c1c4000140c42d03044a02c40c008648a0038000d8404a800e201e00241c0428015a011004100f82e190f07800030b00141820003080b070000703966a0780d6030026a0420f0340e01c600b10709504014081c02c1980f01c1d44841d03002c0c456013002d444195012200404078801c400c00c0301030080c5d60b003900080b04d8500b90041d1050f58044e541c416201d134068104400303264070a100e0a44250b203801410b04c05540200c5150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 660368048 1250 660366798 660366821
    0x70903030801050f0301060816030b36030c120903060c040803030c07060f090807050114070c08071a01030506100609031505100302092802191b050a080d0f 68
    0x10101c5034a00741c14080c2000c5200d80303044c0d155482d01c3c00032a03010803c100c20284449145406910107144d410800c1a9640207847d07085807594502d03c020704603a020318013108118241140010700702c9141c0801d030450041c081e44d81c040d40170300802c440840711410060211901c00314160f620f0313a12040c407004400d11491054030700c0d03a041400084c3d1840306800c00303040064010040820382080c000c110303c084800519040342c004401082440c05d02c402441864482c0404000bc940783d8103100b40701400c02c40c4400001440c540000135440d041041a0138041a40c0d408024546002d5840f8074100742c0360354085407007d0f0a000005000640580b2811405085a40054038109107807440b1464401400f001006400c45020409000005803110301180d44600441801c2407903138003820580d600c0600f41c4403c04019a8014801131080a403408040e00509130941041daa00890080304c0e10051240d00d42c1c0a0541e001c1d032400b40d02408840030060015800c610010443c0004800c816000c891130810034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 660369298 1250 660368048 660368057
    0x60c050f19030f02070e161805090105040b27071d0906010309110310020a0f090b0f2104060506090f07080103060b061b0a0506060d1110030e01090c0e07090303 70
    0x5200801d0040d00f2040e12402d16105841146803501a400070300701c4150f84100f40300501d029442c0d00150b002c4540c0e01d02600721000200c60341d152500080d41c400781802a0b80c802c1d0355030700341d030a950364502c18102c462010346e101030302c4404a00d060300600008115945008152000e44828072044c1150080c2180d0a0080103402c0360381791000110700031702d200001100c0c0d401c010020b15040381e0702041800d0f40000f44180240c1d8903641044014000c044003847c900920800c00000e001080402080c0da11411035080c000b6101d000c1007006801c0100f96801d0107012404800901c8140401c50308014401c040030348001c0c11544501c50900007424040714400000f0381e0361001071000520790781296003e004010302c0c20303040c00131803421280d814a103866003206690002041508100050002c1e5900110445415401c44090b4843c035407222101480188070326040d03c80700d01c42a010350b008990f10b004060003004018954a4066035500380c5002d000303480e44503040014890b5106a07494020743ea4150346 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 660370548 1250 660369298 660369343
    0x9130b09030a020d0c020604090e0705150a020a1106120a0f060b030f040b07260a181211070b0412020117070203121b070b0a05220209180304060c050f 66
    0xc048501c035a00d9141240c7c880010400050b000c440c80c05680c1d02c08012101900030145030104202070141c401340011410300c001d00004084c075401184038a0059000100305101d0740045000800ca841200500b034000702900d01803148030245035116501d02142d01c24204005030300da065200e03042c0403c9804401400107400007034000340003180065045803c034241281001c50f2200342030300d155405022413813487d400404010b00004140950207406003a1003040100f4682c03502c2c0c6400c10740f100b454010902c10503000038050107000700405001031203415800354a46443d0500b0510070703408180107900040840400585c982502e00c451800b40c00203800452808074000015001c81d90000c101000b0351080784211000d45500000911310381d0b1041e20030406505d011880801215000b9104100b0900e524050f200c400d03d80000c4100d0340da804442200072645c0e01c4003d402c117039000480d2030049000204000400c23039000451410154416000d030380c42000c0800a86070380f2088501491010000100b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 660371798 1250 660370548 660370573
    0x15081504021c1808041e0510080402060a020c040501091b0f0801090c0c08070c08060106020727090203120a090b090913150603120905030a0b0105040f090209130b09030a02 75
    0xa2002e81e0760b00203c81e030f440b5840c010b511891882e40180d4446204010300c0618420384030284244203020340740454032510554a01d510090902c0001040240070f4800000c5500304240204071032154100014410301c02980c48854000240080f1000b00102c43c45011440150706c5c05a00030241d1140207036980720190f840d0400600280000f00d4145040c40031120107a0007046107070004091aa000d140803080356450131000c1ca1400c03405910410864000000c1841118984955401d0009952140544012120340920024288034500030340c58403403c8000713140c132507c541c081d01100741603444d28240c00740d0b54140058184140e042c0d25034089030180000f0f0030380c04074904221405002d000c201c0030301d9030340120030400c1b02c0d050340080c0e80c560b02c441c510004955000c1180805080300390040d020310442940c0355464000103000c1d05225035219042541040c103e540001c22058000f0880041810300c00003c0305600d10100c02a92100c0c1c15030001183c03501c00104880030442c2c2c035401490b0003000b14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 660373048 1250 660371798 660371801
    0x2402060a0f0b090c070b0603060912091203222108070609140303040501050618040201030917042d0b03040b280c0f031b0e030715081504021c 62
    0x44455036100780c1d0360790500201c1e84640e04014452401c0300701655641c103c40c01c0c08442840000c000038483d521039001c0004540c00814400021203540910b6030710b6685480008002d00300021840c80d8a00c404103500198110500c4d101918860351400303905134580382e00500500e40183c1c4030086881c0c0000c02c0405c0061040d0000342007890064a000800300000c5e03580c4a2480240111942240e10100c00e12003400400e100e100d8000c401242c501121301000800c40040075802800030381410780d030740194000d02007072039030501206509245082d83c076074483c856051480c118204540d1000b81803245220001012080101a41c054004190075030f130321a80e47e121070303200052668010318959050303100484990740200208806010011510240c02400100240481b000d000101400c00c0c03503080440109540c44a240c56241c6400b4160000d01804240b501c1c45560100400292550165440715844807c080c01030108884400e400402e65003003000313900070711500e840481c01001c2069a1840310307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 660374298 1250 660373048 660373061
    0x10207170111030403020d0e030a02090402100c140106210807080f070816030221090d08091804050f01051b070f060501080304090e0609150c04030f0c2402060a 70
    0x2240c002080320b102000c02e01800f900b0940d012405640b0002c5522480b541122450882c07031302c01d030001d140401c0300340c0000341c4014028002a01940d080c000e13012509108130920b8a145400c00c0308400500c1c00c04441710f000b8401d91041801c944550381c014070801c0e10300f84001c07443c3c3d6081400f45050401302d444015403684041c01d9040600d00070003400c00090405400f800031030f8401c8482200e1303c015820041d06040700940d01e06000315941c204481120b4500040d50096041034803804004400c0b460202c419101e03891540740d00035640b050b0300100f0003414402911841c803550907a281c0c40c0e00c1d0500d260a851082d01c2001034002c950b5640b81050300103001800c00d080c09050b452451131503986542c0d0840d402a00040c1543d000000d0a04c55460240200710f00c00745804001d041605d4aa4507190b200c5000c00e4090300c00b401c04501290000c00300c0c00640d40599002900700c028004c0d60310700304c807040300c4900c2144644682007210400b08040580780385030965107500a4000d42c0d480c005507074001d064 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 660375548 1250 660374298 660374339
    0xb0609040228020102031005102106120b04031e05030106030902010e040518010b010c08030f130c0e0f07170f0402040f02120603071e03060f1805010903120b010207 72
    0x3564220020b440a503040c00603207050154000696078100301c5982c0300c00b5004c3da0040b6029080100781768070665400183c140b03080d404802801b1007545d0717070100c000280c04980e20803c2d07840040704c3e400301480012107d142c0110b2194031203000c0c9101440610b814480c3d1101aa4003007403040c8010071030725010750050b6103418414502407202c00e600c400020111501540c1d0720784404680b104241800009104d41e004849003400c011904207040d40e1501c3c0280300040200501c1803404001c02c5103020007070b0801003019131054289804c240c581c0c0054158220403200d540e17100000f0004594242c0c02000c0903844c00580c181602003030790750944c15950715100688126000b60740d940ca510030040341c0344050111a840020310444ca41001c20426140a4854001e003182103802c03031034800c0c207182c1002d02e2000c403035000c00302107101c104400d515030003450410007407649600300c240480300308041940310200d200d04c646c0354001c0e080300940b1081c04903410941c00c507016a000c14428401070300b07401e030007820080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 660376798 1250 660375548 660375577
    0x60901180b011b121d060a1b050a030507060b0f06070303020304151506140c2d011a12060f150307031e050f06160e180c1c0b06090402 59
    0xb070020300982c5008001100555940342c401a140405945c84818100200c20220140991207040000907046200d01400c0c1001d0004450290300600c03c00300d2501007446c3c1104c1a624072000e1814050055840003104880c681e2a12014540c1c0340b8120407501007110014140a05242a86e9000d0f0000d40c8050320648040c0703240d180840b04908140942c040840e84038001c030444504d030400c044c01482c0350b0301a14241c0c0b82d00307100f5040d80302000a030644018441034540c1d12134002d0700071017200c1c255140c2d083c000f441d400c0032000c0075040c036145985811044113592450083e510607980c20b480e980c054500c0c858612004000c64080740d030950403103110030401000e903001d40d9500d507605800000c0c840081006410241a000c2c24040b00780028801003020502600c407515028855804058800c10400240040c840004403070b0b803240c640030155a8000400348040b0306080c06051126008906215105134105002001481c007a01841203219009044203040458440800020f5007140c0001003040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 660378048 1250 660376798 660376817
    0x901180f110904200402120609040311011422050c0603060f1903060e0d0e0d06020705010f050a0b010207030c0e0c0c03120402130e150702030f130e060901180b01 71
    0x1542c820b410a4090b41c40307004c1d00c22440c000c05000115500e00c4c04101d0b44124410311086080706090800282d2180e03048444036913a6039549002e491803e14440c04d06015841c00f104100c100174038030403582c01500752008115100c1821b00190740580c41313a00c401099034100c2c21034450039041503400755400036001000104100311003404244040146444070015240c0c0315010024070000d48910b4080500b164040e11200d0320750321007d8241500034003c00d02800000b5080428841207031f050352900c41d4081c00070310400000603800e1014060a44008803203034076103481c0020640c000111032084951106010b0250b51400c83c00520044c0020301814107100d0802840601c1d200070310041c564000c11507101d01940c1407a0060040c811300d0340385658140c074641366100d81c83e40c1c0006905600007a1315902004195140c000890031805040c100c8030784058007280300c070107100307170564541d040d02c1d405031102c1010340d680b00c10010504401e00c542c4c4c0724003038812540c103685e18481c2c211040307150b4181080440c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 660379298 1250 660378048 660378083
    0x210110c010c080a0c0507020607030c0609140607110d2f1c090f0b0d1a04381c0f0206071110020106062a1a040b0901180f 54
    0x250703502c030840b44002032201c00401c000340000c0c5c45141a000741a00e0401c3c205201035000c60403510075140b000e01840b04100d001c00400c030098001d0201507500030f4542c40c84808500381180d0f100006d6901901103400c60141c0d10480c100000e107610103070b0550b662289903107444106c581140c40003000c0200f0080a01c3ca82e085048020840c00e051034042d01c0210310303250207107000209064900c1d04002c1d103030714070030350300300300e02030501c1d01390f0703415401c025000a4200f036001101d50001d40c0c80d2a19540050034110000011010b0341101c281180c2c0510b240c5010380704101101429200e510338466100c2540c0c81d08044605108401d0002e1030320805001088842c240c00164550304542c00484009100c2c1030b0302140c81c1080032586401d581c0a0000340700e281e0030040d020f00b500f4142070507102403106442c00c0328011142170040c251385036003144021480460b100381d060b1010204541c251100003000010990000381403080308645941c4640d00c400c24412603a6100c0b6034a0a428182e8001c1c0004c40403001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 660380548 1250 660379298 660379301
    0x11118031c0e13060605040b03060105071a010501020f06060a030b181c0e0603060d03050903101103070306060903050d031a040c0306050a080102070f1407080d030207060605100210110c01 82
    0x414604a480d19030b007520040e01000703646003900701664912804c000d010000203400c002a01c003583c83e5a0704540c2c07242d40724801290300d40107100700a859241854071113514441400e40281c103940d001c0e0709854803003000e8110340b699030342c00343c50081c1c00500100c020004140e18910f000c0d00283e83c0440160b00341001c0e800f00c2c0c90040d4030001080e00740c4400c0004400d698000c500c04404800c10782d2b10501350b08e4070074002540007c1c2240003400b4030600003030401c01e642d4280170100d0503183d228001c010030b0020703460b010b1a64000310341c0500070a01d49a03010903030070b0040d20440116035000c00248140da00c6600102d01401822512054440c10301c120ba001720b5556000b14070030070800c1c0c1e400042007071802c4100031410920f5030010b80640d10422148002c506081c003100040f981020030140340032a041d0a462070b10103140d0015603140243c050101001e5416001806483c0c0034090034000e660300d83c420050154548000680968010700c1d156a8050380d907080302c1c40c242000007000b03041c007005070785150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 660381798 1250 660380548 660380593
    0xa0b070f08070c0809100311070615080a0c061d0901080a050d032c0a0203160e07020318100207030503210c0304030c0f0503040b0f0306011101111803 66
    0x840e140300d4040c00c8490340440e03501e51003051031501c510302c0403c1e40ca030380106124044085000b4001103003107030503075030281e0404484111120b1115036101d00d5820010010440041100b42944100302c00180580c0e00160f50340c82560461805150b440c90030b11b050b2986100c0c040d403088200805194001165108080c3e01e00034100c00300500800d240720b01e4103600b094241e20b10716040c14500b030010b0035001e0009048943c800d010070306042d0100d226210742c80c41c0a1142d8030080d0700d07100e44000f5000d0074041045001c110340c82c4807a8003000303031074044042e40c0740c0c01082d204648810064014034071515000403d0300c3e0300c0c649030043c0c617003194807600d45505591002d08507142d04070b03000001401000f1701000e01644400310020090841c1496500104402803941c4003410b183ea60a000c03400b4410f041c0100c0300180410010a03540d50008595030781650412a54a8046491404080c4060720107000c0c14015040520340186080303400303c43c010164014100300b9800d445030304400c0052555008820 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 660383048 1250 660381798 660381811
    0x50304031113091e0201020f0f0309100306030f03030515040c1d19060302130b03070314010801180b09100203090303040c050d0c090f090503070b0a06140f120a0b 71
    0x49502400c024280981c0428007815641c00030700d003101c2640824030014218044e6800051040c2e0801102c1c00100d01d00034441001d15007502401c4039018185500100400b04404203803842018480681d40035811100613100203801c151500c0c2600b40000d120360701c19a80140b400c20b044d007001e100700700801c048590843d2141d0200d03018810f001001c41a2180c612502c074012900303902412991b0b55400c000c120f5601c15032051640210f4076000300541c40c82540080d110401815440e443c3c8908000c001c0c5c95007290816542c8003d00003c942c2c4841805034041c80425013a450240501d0f960b111404030070018441507160040b4241d0f00e045608a000850081e07074802e004546904240c1880500010b03070b80c1c001c902c1260102c40f40d500151580c010001101c103030890004003440b0500f90302c4050151400003d100d408001000404c01c01070110f0750b800f80d0321047d4108541c03a2504801c2c00000d415198103688088a582280800e02c1c0c403181044450503004203035001e004003603807000c0030301c4001e032802c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 660384298 1250 660383048 660383063
    0xd0b0a0504031412100b090303120a0b0d03051e251b030606090608190602130509040b150901050609040b03010b0402040b04031707201807020312010b040609150c05030403 75
    0xe00900742c60440e40407006e0700503816807500e46214100001c1d600c0c40341c0420840d5070500d1700700080d00168150f01001500801508050090b08240307001020755110402200109640c0c03c6c046101d107920ba002c0e2642242e010342e0740c01d80c007143c450b1164071b40c800c0c18408444405d1690600110710f08050080d40041d8880e01c808100541000d200405503155034229000961144100600c410641507456100d00d802050043c0d6603949010014002826600915046600e0000b03000401141142c41403180d50845400c0f440d16000d8030422940e07580a02c6010f5000d0070a01c83d0144a1402c1e5110b20b820400c003c0000603002d03907503030206050341c01c00e500800d00030001040800520020b55013600c00181012880e5141420698a1a011504a000c080c0d144007135403410b4103003600c070741055141d85a82041241d003d403810400007950395004850b2204171840107800000c03c10070410540f4240c455549a540d80c007410b10400b105020b000c03094030400c001e8083c90140102e031082c8014030255016001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 660385548 1250 660384298 660384301
    0x150d06020a111203070807110109080301140306060915130b040603061b082502031204051b0a080a060c140708030403030b0f0904112b0c050d0b0a0504031412 69
    0x10700720b05000c9660b2100110303070020001c0245c41540a800d856104100f81441024404990300250040003107410040003600f0000001c190020f080d091002400022411100c10f9a02d0406000f200b02043d60001c4c17841c1c8030442e0041c014500602e800da507070b100304140000c4a081a400103025116135900c10b0780c0507549d03141d2030751501d07072503200140200c0841d09000109003800040c10a1100110072041c1c140700300240c6505003140b0038411502820780f5041080000c0c1001d091044d2100342c1c08034600d94264400c0c6610000e0b0402e48041c2045a904502030241003085032540000f030b0107014060800c203c1c0844192411902180240c194580580c3c812500c0703242500c4d000d01259262944903101380030b40c0ca001c49441d0340c0c00b000b0941c4140e100d190943c1c07815044010400c10340c510300c1188468140d01c3d40300c003024482c0a2110303481c030340510490600103540d0350510150f2501e00c000604103032800d40002e80400e60303540289801500c203160540c0c1001160415000a401018a80c20400c0300ca80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 660386798 1250 660385548 660385577
    0x1030f110a18060903060c030b04140114030d050d091e0f0614010b0a12150e0a050c0c03040e0c070803040515070e0a09110403021809061e150d06020a 66
    0x2c80c0c0c500240030003005048494184040a05003c03040c0c03000802140c0c0300c007038000415100382c1000e4811342020b4014000810299a0350f5044d410901411100310964103142c1110300d0300295030f66080c0e106868240c070707004443c3c050b100030385001c54081c1c07a0303a1000f12042d83c200b89000b0711444100c2c0103484203440c0341c03094a441026124039282550401d201080140700088072042207500302100da081c883c40344080a0300c200f003e02108922110264030b80710b0300250307000ca241500c07031107080302ca0000c01252f602d521034072829000311848083c40380d105000500c00c04080303099580e00114600c8910b81002940c2d40c6140340c1c1e42c0304960071138460f00032516074440f1060024200750443c440c3c2c02d04803210110380000c500044014800e1135043d544484007e074111401c0000c0300c0c0559009041c0801030a04801289000030301541c4e010858071030781c0005042907500c1c9031070524030540b00650200e55202c541c0020f8860f25184000341e80a10013401e0340000030000c0c40100324624243e01e520044841c0071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 660388048 1250 660386798 660386807
    0x92101051e012c07030b19120b090a020405040609140706020d03020a0e030d0e100c02100302031f060905010f081e0714030411090c210601030f110a 65
    0xe0300a103012000703540e030760048844441aa5040d62006544082803120b01c1c0d4a01c12040a41c001e21001d000e046000e01c8415985504480081c01058801540351001a00680c107100b450388102900f44035400741c0e07900005d0b188144180c0040040c001c841ea454503039000103040b80c0f02543c08442e2590358501000070407010302d46c0083c0084501c40035111240c40e0450194132601550300c59000c0550025006040fa40156041008064080c0884401559070f841c040c20381b40e102011240b10715000ca078412840382c41002d0440e04140d0180bd40740c11041100001d074040d400180455020101e452004104e04606480c80b100a102a40d2070214044ca0704001604902c2c10440f400304103c80c00c81003000c2c56980d101c0c0c6e01d466828a1240000b5540d903650300303c510070050480c0e0880344000105001c2070061300341003860905011101b46005441d900c620110310710558403400721044900c034100402c50140148107600c44018100030400c4180b40d40d01d501210410740c0503d14540002c1000310105610 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 660389298 1250 660388048 660388051
    0x5030301121205160227090706080906010803040303080a09060e0115080a020904020904081201090e1002190f0905040908040e07051e0702030a06110304170306010c060e010209210105 80
    0x50809601d0b00200a10116012429000c0a17008850144081c4008400440441c65020981a0346c82603820103d04c0b1039191492403080300d0001d001100480c0b000d45021898504840440000b5803505113107590130340380381100801c200300d0240e4036800c4401041d018003a450361540c1d070b84000144052560090400011320307030841c621036805070000e034005803241143c854000b40c0407150751060b50307524944a0102d00ca03075180070500030400f90000403940700079044003c2c002240c034143c03008110f40171410412800f03a04403240940c1548401452080e014060b00d9054400919000021a440300c01040c165800444111103066001030304104402c00080d03030a800c10064030b0074038a000011030403113018101800c1858060040092000c04658040042030f0180c0d0b032041d014400030402c0c801c3d00400303402c200c50590310031620290302c1440307405d10800c503032040b00141c442410190160711036a008106030441e01c4000c7d036003000542280d0f5501e0000b00200d0240440a01040001080c400e081d0b880 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 660390548 1250 660389298 660389333
    0xc030902010216060c061a192103080f0921090406050406260f0d03090b0901060e0a020c070e010e10270203060616050309190b0906160503030112 64
    0x10007182400328a902c0f640041c007581d00f00310045000140a051444035043c50041c0ca03500401900606140523445480d110840304a003a46907064403c480c03100501406015004000400c800000703003401342c0500e002900712604904441c40d40b1009442a1240780c2c00c0c03402c40b1000040807405542602d028000c0e50050a000d940c240001407a005200d99801440ca512414521b04008550380080003004144402c001e0101152070aa004020107001001044003e644880c21b040001c2c80e6030b074050040d88d080b00c0a0051003603c5a40d0005110001d402102c2c480c42d5030b003d049000036285070499103280c042c0c26201d08220481c180094400d5600409078440d10f0258281d6516a101c2000c15600b888226004800943d036503541e080010305c184a04100c5914818102400c0b005025000006e044910f82c183d540301350724080004002c020060740d00c10902140b004002e01c803000d040100c050540c03290850840080c484003030382c4060458000f40c0025466199518801003400f122840e441d01030320 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 660391798 1250 660390548 660390583
    0x20114040803162a050307170a080a05040f061d060c0a1b110603060d05011b0f030608070b0f210714090306060d0203070513020d0f0b060409050403030f0c0309020102 73
    0x911319080300c014031030700c2c00f0340c07008a4100401641403081c14401c840135140c0c00806c2001560342d941d40025990440703500d00380020045030000e088401e0a11a042c00b81c2d81084060480300095961309010b07040c83c8000d503011542c0112034044c003a000b080054012440c4488076a150880034200400c2e40c540d901c2800c064042c601d07002808684c07051a140000c00c001d85030103980390f4800010485c41000804020419846d01480b03150b02c400c800e2140d02117031000d0b55120420304000c1e4046082d12014060280b558205250400c02c800d4850020703e15850700023542030034103440109143c00c030701c03940302c0c1300d884940080e040045099001d411840140da1042c1081e0902d0a4600407981c0c40b41c0040030a405002d0404c00c20341513550421010008000081490440941140043c0c0c0a504580c0707040e80c02c0c074140b2000a0110f845401800c0c1c01043c050a190f040c9860143d1107406040040e0042d0141036842440040d481110f0091070016840b94034049984500c901c002440d01c16090003002004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 660393048 1250 660391798 660391817
    0x4151d1510172203030f0c0503010b0d0518060721021312020111011a010801050f030c3601030212070503060c0c0106081b100f020c1002011404080316 66
    0x9030426000100c2c0e0902d1000e01d00035a495a042e11283c0500040c00600300e6400d030000b108042d41604440100361007000e052110010004054506010a01800b03041c100c040c003030210002c4155100580c40303101c500c2200c07038038041c04000307034240701c8261904000074009505030300c1c03000c0082c41030450f60010301c0811490145040c00b004102c00990040c101c0c21040381d06843e095a20582d030403e0342c00420b00007000b900c0c40c0108850f0844110207c0d503030108421100010320740c544440f1812524501901418000c1541000c1022030342c40801060805400304006e030401c002503810800c591101284c18408650444c0104140003103140000045540804024420741d2408030354540c100c0700005007242c5403680040840c2c050401e50700082c00500c948220040300001c401c510304004c80c4181c07040d80301c1c030b151110300b120062282a03001c409a8440e04102d0741a0a0400895000540c144000610b0a03000011552000019101503c20320350210512907562110000960010b1741800c2c04ca248 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 660394298 1250 660393048 660393079
    0x280b0708070f020f0909010506010f0905090c030c0712030f0f0203042409080c07090b0306011a03061804050c0405061206040b04170a0203070b06100e04151d15 70
    0x5101e07045000700744000711006107085448440d48a610318000a004000a107882c6240394001d14003200c0190005404211124a45004901c80340c1a60070150a0603125a5040c00185043d84082c0c035803043c4060400060000c2650700e801192001e01503131780032468060580c0b481c0d041e0780303010802c00d541c50310400500c4001040c1c10700100003840c0841201748054030088521000300030900003d02114800540d4500e0140081500016100340c0c3c5c00c1004a141070005140d650710090248004c0c8020403581d0f030383c0e407000e80c07002303560301200040043c058000f01d8048000d80d520140e60440702a40a10b1900340e584c074050081943c482001d8074a00c00c10040c0007040b03541ca0340c0245c070281565042002180a000484841075061411407060982d12004031100961704d0340030920541e282201c03140411a07514100007049400c0d041a99560030102d110400c00000300402e03411007201000701c02c000612440d01040c0c0c6404084100c0d8160300c00d00e45030f600c500032603020074907039403281640503060180c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 660395548 1250 660394298 660394313
    0x50c0c0309130e01060e010e010b03040804060e0402070c06021e01110d0504140a0807060f2a09030203300406050f13050603040b070e03010507020c120102040302280b07 74
    0x304501c21605994041d41481c00e8a0050140c141c00c01d030194241440032404841c4628800e0403a003101d8407008440c1e0b0b0300c9840c01d250340001e0360003d050440800040010718890140f000311150010401071800c0419600c0701e240ca4280d600607005608144000d000c1004480481051449680009d100d42e800001850322544140b4403070000c042e1f56080494280200c002c403111850004030704444205155040052440d0401c0c42c04407882ca003050705202001307025002c3c14081414a04450b25081e64050300e0654a58211012504011000c0720000250303404001640f500c2107244845412004200c0062613494041e10404100100421041000a60007001c039a1a01002c00341540c50f918440d19031518070a650748403030307849840442840700340310080c40d60038002c264a03252018042c0402040c1802d8807130864400c07002d82c0080002c5081820612000211402c04800040c545a00d82c2e00050b143c003c8024415040d5247c00c8841d1315100c0907503100070241c00c0381030310139040031134540c0c8144 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 660396798 1250 660395548 660395557
    0x91e090a06150e0916030603080705010506101704030c1a18070b070218100f14010305070e090609090708010f0b18040b0402040b010c021f0306120302030f0c0c03070303020f01050c0c03 81
    0x182500103c1c0c4005c803414843d81c440005190b0209030719568100078240140079003001e40700c0c0e5214200011060343d0700d5020380107280120b03141030040740840c0d485440a0740d004903040000e5801c814150040070194ad000f42d0b403c0d12031054170f0782503520304034800301d402d1801c000e035008540c1521080180d100503a8840c2440c80340320380c13007544035099581d40200d890141e00c82030f88003064104990401140741d050110380c1c01030044c000c3c7e90403c002d0780c9203002205c0000b0000c0d4803a03002400440450000c1c2008500250701542020031a60001d590b041303a582111a640700c1c0d801080c2c1c0d1041c4e295850318011a030036034041e0328003882020505094440804e15880a4002407081ea40c8140d500c0160f40142d1141c0201c640041908514000c60031001d14150201d0f18400c2c0003a140450201e8005016001c500800d03401d030740114101110b4964000c4150300000780082e0a11a603503044080e960100058030180d440380d03000d040500d0040b035440307096800140c03141c1c8050400f4800010411000001d0781c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 660398048 1250 660396798 660396811
    0x3070516120c050907170c0901080f061e0609120a02030d0f0f0c03020a020a0e060a0b0a0f1112070305070c053c130b010206090a0305091e090a06150e09 67
    0x481300c98413416810745e0640d5240c0341e400745101d6900200014051507101400a9203400c3c1c8400c45590798030050341c69540f004a64241c5d20041106030444060746ca10301c0062540340141216181040c1076000450701194500002003603405000c1503c00c5040c1400310903048107040c180b2642155654802034940a100c103080810001c01003030001c02e06108000b403030500754003d4004690a511640b90310b0343ca0004607403850040b884800300103284109401154404501980d90b0000d113101228200d41c050030f075004401c2540b14000c00305060212000061194a1007030300c8044c0d8411861601d401810f1403548180d00c1009082c10b440380d0040e0360502ca40080015400150791044400000840e121103a0135898100c04026085031140f8520b5000d502565030903002c540c0b041c1d850b010a03950b0380912401c0140042c00a00c054400d03810121591120260790b80300380c2003a1951800440c2100c0c50444420201544428040140700b1800412008034445c900d081486440c0e00b0000c516841d0019204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 660399298 1250 660398048 660398059
    0x1c05010e062a041a0d0c0e0105030c0903010f0f050709170709020705011515030e0601050d020f03120a02030301061d0307140f0a03080d061e18020c03070516120c05 72
    0xc0c8124281c1c074011200030b001c103581d2103888802d5080b00d03290180c03c1743d1020000725142140141605020b10a070302c1d51000c05954076851940c520300d1088058006010164044d905c03000250360b840e6460007400c50400318a0b40000d03891078144402400504203501410a03d40e1484040a8201c800f0840f4801d842980c000903030380e05c1452030110700408040301c001140d05128240070606e400700d0303115040401003e59003805540d0141c100e19445100c01c0c40380541c03101d030f080340540040c00e007001c500141000c01002e40f0308102c422030103124543d100c400040010b81000006100107908032162841c0084c8030010307040340d2604a000310b45d0b01c40342401806483d8bda8803524445540d2228585c2c1f04d62038004d000c03a03800755030b40d103002000390300030b10441c0e94801d0030302801040b17205415110a00106012070040c1c8a54034044c40201c3c10f400c0780c018038044030340802a841d48020108000d1051600c120024402d41c00800041120002d560308220b51000351301d601c003070216010481940039100111340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 660400548 1250 660399298 660399361
    0x40b1c0f021f540305030301030b042d11030712080d0609050402030a080304080403020603040b090d1107032a1509081609020a0e1c05010e06 62
    0x501c00b21044441d0750301c4040110420b041d89034000141000030401d41a0100701483e006141c41c00071003501c1044280c098500d400316503240060700d003d40220380340300018a00e6500c9803074180c1176920076041030318a614a081070200b0004d45800011414050810018014869000082d84141c0004014200c2a1380c50a20021a0f801f44560401003440d19048400b620341440d003030450340c205404009103a8641400020702020b00d004082c81035a0003070142485400540d22012140c10141056034555030501000c40107031070b42001540928003824904400b8135119801a20b820002c041180800040000380b50024900240038000e0340d502c500c1d007520410444002c181e0030014400f0f540a1240f0b44540080d03400380304141c110300b0030030310f80d100ca41094459207150765a04448040605921481400b0004858154084c10103222945030000341403145500180b000e41c49504c00301d00c10300c0510003110400900340b10303880508111101800ca0361905020106003001c0302c94204500e440303d10b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 660401798 1250 660400548 660400553
    0x42c0a0911060301091505030a03140a02010f050106030614010f090b0a030f050a1508070617060105090a080706261506070c0303020a1118070f09170309040b1c0f 71
    0xc100050300c030060182c0c2e8482da03407180510064440141c5802c0b585005260202d40303402c0c049000a003164141c3c81e090314090311805003000f5075010707000d25011035580750150b0b40a01c8560241078024151079402003500c600340321120742c1c464101c00c000750601034211031010b000340d0032070040b44c11500d07030300c503450344603d4000426005030429045800307a1078945810814456001d034896015180d03076006840d441500c400c40c0650f503c0041c044c810220300324050b89508421214070300f5a03c5101807511030708208640d0042000800a604100351310380040a003407103800d078040c503e0301c01181c4a000c3c1c180d424112070f201c0701c6109805401f030b07002061820b84d0160540c89800880d031f03c40354855007039018207940c0d040c029258210484112802905200703190444d180010a94000c10381004140d2069190a901944c0d002114a00785042c80000c0302c0000e16010312040c80d4025030304103000b1b181d6442200040200700c031b00130706981d0720502c00c1840105500804c9580201d1141d44031103002100308090 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 660403048 1250 660401798 660401813
    0x20901050408030d050a060f030327050907110f0307020d06150e0109090b0a0e0c0409050f010608030c2b0318060c05091002030301120b100308030903042c0a09 70
    0x5030401d101030b1200090010340103840345e00c00d034843ca040480c20030403036448003260510340e07040c2d20020b000941c18030101c6902e010900203801514621203a60203826540b50086a00d09c002210042c01017103038590285140c950a01904400c030040001441c50010260f002502c8100003200c080d20b11580c40640045001110560802424840303501c4121503130f640064001910344d00c4804c4855020142c0422088940381c00f4803100108410060a20f0100d410107100041c4030000007543d4910503400c138503084031401c0c444e00000c3c01924000d550340c0c9040c45500c0d8688249090300320300000b00240c004402104220185064400d2441e02013003400d50b8080050032842c6c4120040c0101e40352080c03005501d500400185400350003a0b810141181e50124180d0710cc0c0400d20820482c00000310304580041c500c100000e9024000c10040840b0329100d46500d081904216801c40455000190900c04815000310544070720144c00642001c880c001c0c0c0700380300702d00b03c007400140c1010703110114541040000d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 660404298 1250 660403048 660403057
    0x8130510031b08010f092304081b030406120e011b02070501020c030a0506010b0d0906140403020606040b0913020d0507030b09160303020304060311160605010f08060f06010e13090f02090919020402090105 89
    0x240d40c2001607808c1c18140303080b00781e0000e0051385a8021a050038180101c0110684084401d2622050680384480034640302505526426245556850b0207441d503601186031110000f203c55801804e0083c2000c0c00a80752440030035009202c0d84c0100f18884c0064170004039181500d0b030702c848a82c0c5a5603040c80c480084d000324000140708a003001c030b01c1901e860000c41c00520a5001c1d07801c8901c96194081400110ba803000c1146400c01d001c0742c0003846400900d00d0f00d8515a00c0030304884000c00c03050311041d00f0715090350001c844900080050041c0c00d50100807002c4d520841c01c4811a00d0380c6540c1e8003a6581c49948100414541c440c281102c0c81c0030140190307200d111039a02603191140185c9070000081409004455212020080104440b00e000481c0ba204241420106030281c44030001502d00707640d00c2040503485111996042c0c3c101440707004401c04248242401c110036043e0b88100004004010b040810540c8214100c42504000c2801c4003640c540540e401a03649802c8801211648074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 660405548 1250 660404298 660404351
    0x6090102120406030921020d05210117070605030c0414060f120702010507030614040209040e120d0b060a0e010f02031b070f0806010e010308130510031b08010f09 71
    0x200e0002049505500800b180a06c1940d100403141c0700c000112410700600302c40c01e801a400724080c6901c060181c2e000700040c1411842c010f20030050b00d8880821440c0076007083c01e148420340041e81d21542c040003a24041e01560402d5400c52406100000036801940b04481d40d4040c821224089a16000c04488203001d8401742c442d035a4804000001c006407081e504280190310384000901c603079100f0700c1824265400c140740c98003c40c840a0410001e90400b01006074011750399081102209803c10040c4800c5083d9281c0b2500c4040d017503907080c00c0700c94260f00740c1c4c0036400030030404040e26401800454960000d0810408840c0c0c8028102d1542c012440c4101032041041c11a0300000d200060410803552005900e803012078442c40c0d420780b107440a2040340031000300341e001400041c908001808002d10214506c0f00c8103a90355000610b1036008c3c561810102e03642d210f090007ca504498403250076070442c00e200e0255490f001005950310317040e108002e1203607961014040840741c0200d0180b0303c0ba2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 660406798 1250 660405548 660405583
    0x11403060a09090809030d020705060d02030c0408030c0601080c0415062303011d060a0602150a02090d0c06030f061503241715010b040302010f0c02150913060e0606090102 75
    0xf103c0d04d00b00ea59540040c100e980309200d03031500040310078800103d50094407005000241040d2481030548041e400240001c0d1589000340800310f194802003000d0601c22110400802c01540b4103561075042c2100264824007442c10088000d58000d000b000003811200d417450400d040ea98a4009034601841c9610300154800c000800000d44441c0602c2010b40382c044a800c44d581c0da1034a00400034a039072244101000340c0c01c000310000140540c4180d00b0b500c5441d20601524003020b880000c0d010003034820084911900303016040c011540e0600c14001c41e40c0030785c0c03810006a0b05201490b400751032a0b0030f2130f00401d41c0b00c110660a858058401582c4c200f80e0400d0742c044030307232100c8991070000a20407000c0018031524030840d40b020f4000c1c56181c1204d2070500034600c0c040c11074004568203c0c00034400003c0c0400f0355100c000507102ea000d03c00308913100086587e2281d582c00f0070040119074429404c400d807410242e0911030b55000c1102e5941008045500c0c1c2d40e940110350051b4280b01484a05c1d49040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 660408048 1250 660406798 660406811
    0x10e151c061e05100501020f06061203070501050703061a12010e150406140111161404020c0d090819110d0c03050601171e0a030804140307060e070b09011403060a09 72
    0x449600f103d03008211009030085000d40310401280d81e43d44510000c1429846440405c503603003060300300c00201550150940c0d00e000201d880c3d8a0035070f00159100d40c002035542c58100011542c40508025046001c2c01131031074005920940010300f070040c000c0420401a11010a6014440842140701c0b401c000c0d009125403030740c0e450724100464070240c1140c00320740c2d903581c1c000b46008045828024841d4802050b600141031030018140d00d58180b140b242c0003a420040c00d42a01d20811041c0620034881d50745010850401002c0d0f42056143d080c05000160a5403000000401603541085400750030303036420662020341e0403c1c0e00c0b035a05690000d0224002c081c004100401c00d0818802c81c030960904482a0302c101222000c7c2090a800d101092078010640c0400000c2c8528190358103d4000c400d5180360342c100d8001641594060b800031152140e6814410040e00c006024400040c07030500d50480c1042d5590001070f04051555001840306600040000e04c00d076140b41e00c03003000d410008410801c0d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 660409298 1250 660408048 660408101
    0x90302070302090105010813030e010203070c14100201051e0a02040308040609060e030a020609010c0f0b16110d020d050703030e030703050309011503030e060d110c0303010e151c06 79
    0x554950740002d03405035014100114155008540090080e081320310395015000c200c0e14111001c4a20143c82c1d070440c042040f442020418154484014090304000590010041c204203c10203141418104c19a41441c0800c41c48568070b8801e02c0e901e1415101c0d449240d0b407101582e030001d00c0789400082800720301250205105078041005000d450a40c1c841012003c41c64040598408040724009e51218080000240d1544181041c00d0164410808004454000d07551b0b442c0c140030840781d0000f0704860b1003911401503440641511001d500700050400840d003108000d4450380214030030303000d0200014804c5e04061095002c51124400c18050302e0f100d41c420b1038000d00ca0350003a2444407aa60901603403085000c1d415541104036545a2121012103000e40c051141e142c024001902c009941e4072054000c03e443c200092994010074005541e0303d41c14a0f901a01d051400340018500354144119900e29031207403d01e01c234224039a803040031344800407071034642c0107807500c1009444442c8078111903406 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 660410548 1250 660409298 660409303
    0xa050f03091002010b0a050625120210090c050f063f15040f0b18100608090a0807150e0a060f0b1c031403070503040303060e0115080c0904090302 64
    0x71244002c842d0009040400b9030100e0030ba400c41242507034003984111040095242c180010041803211069440c4640f002c02144c1010718043d640a4031703042080200d0b5400e0035410300c003106a421000804025000081d06c85a511801a01600740280186010306071079503920415901e6901c2244d000002c00440d01c00c4111b40034440c1c0318070092040f40700a08552080040c40303c40e00c00d205444040c01040700b00005c10003c2c00e00e1415801a09a0303641035a00b6035150301e400b10f0a500005108047d03241840c80c40c400d600461584040e04000000003840544480442c200c641c054000803c95120388240c20840b011308010004401e00724035115280c41d41301c50104040d43d586000d044100f02600c15038454006603120143c090b13601c601135190280c0c1004c0d05003848072815029140072540760b220104e044c400c55005880210100340044100420140d15015810150000880560141d40340080701583c030164400ba220602c0070481c00241b03d05000300a0741c521803c028814440c04c1e426003806074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 660411798 1250 660410548 660410557
    0x408090d061e0c050d0507050913021e0f0f0a0203040e01030311060c0a050d0f091a0412050406050a26010f06081f060503070905041103162d020a050f03 67
    0x11042c021265401c10005603034440c00b00745007403a40f03509140001ea0340c0500001c1c44d004103688103010050080320801c0d150300b9180c1f204d0040e0b80e0780050380c13040d01d030113850200403118107036459000041140091034019101598003071101c001f0850340b9004480c4080e82180100d401480c0c1c100070503000003041c1a40b0040003076444201c94203031040c0340c9600c10803c00c40c1c410f40800101140080120a0103417416910030038840255040000e40284181d65440078040303a44001c0c232091101006100c18001c1a01201c0f00858003410480d15052510700701a18a004407280b001c144040e07882e0080e8001d1b601240e918094240340c864451030340c0c5918001e5003810240c0078903000647c24a00003554000c18083d200c19011600d02490040c2c1e18090040b5505ea00003000d510410200b07120001d8a600d650250604c2d003003182c2491612450700c0800070301e40d4807005440e01c003045038504400d03486110000231190b444a1400d10031a00e100c2e1170720103078504008074000800341c0c8101410468109008030160 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 660413048 1250 660411798 660411821
    0xa1b080d09030b0f01050a15230406020f2a040e0604060e010b04181217130b0601030203040c0506030901060e10090c02120f0307030615030605010801061b0206030408090d06 76
    0x1d40c1651513901010f02d00c0182405003035007001d52103a0074840d4841c040041d8440301d40d2440c142260350f10350301180f03000f0b50021040c98920708001c10140b11268061216800d40b50b0240c00600c1000e100300480405007400e11603070903500c692a220714845440d070750000955005100220741742810246030000c02000c585845980951078010002698903181c01801003036100074100c03610174030705038643c1c204a0a1040049007804001500006100c1c0d004100c2e500c00c0b5001c01c9680e0912446042030070741504010642810184100100310010f90100018000d50b02c0030345800f601d0340d41d025007031401800c1503040780d080140c444040068160850f8004015140400414800e001c1c070440d060340da40d6443c00783c0b240b5600081c84200c4000304047c01940e84200d4914010828a95440c54007459021a01070080007a44818050040d075810001c218010406031420703200070100f18040498a0790b560400901c80d03000000410180701c2d00006844001200402d02e2140d031a062900400400468119 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 660414298 1250 660413048 660413063
    0x70506072f0a0f06080402100e030a0804060f09150c05010e030f030405070902041d100f0e09010b0901080c1203121810020a170621030405210a1b080d0903 68
    0x3c154030b10266114421a01c09444d691982e03142c0f68208000c10640d0403204041140503445082996001c0080b0600103024680c00766465081c0781d8010720540400f92030406000c400c0e04100454103000044403480409850024a100d40d180303080c83c00f40050082e08001c521012070100ea944065100541c0030303074440c0d01103070705080d134038440c40082e40643c0c8a20010038034407407000c4e5031000e4081d40540d881041100400010787c0c03140c4803810440c003681c100308804440103042101035442441001c07882d450881e1004800d40c07504802d1940ca80201c0e851501804501c04080f483e85420000d035944201c0b000b2000580b854400260903100240c000364101611802c8000d64484980b4801c44104500325030f01d517000c0800c540f010380c018003409044503801c070801c200c083c401740c02e01d2071040303400c28240e1000d181d90b1460300c0100080444030301e048800c0303440154071140300e1007000214006201d03405000d000d0a80151660b0b90078a8045070b1081506014007518842d4441d03200c0051000daa00c0f40d00c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 660415548 1250 660414298 660414319
    0x6030f0b15032502101d070302060f0c010f0504020f1807050703050409020a050c10050c030103060902010e0d052a060a11071205010c0f1b030e03010e0106030c0302010e01020609070506072f 83
    0xc20304050304080c520f041b507504003a0080c00541081d400070702b0102d41040e4441e02e000311082d80b250855844106d00d9158a96030400d000031840d16100c2260070071821504da841e00d52800c2441d600040018041c6800c2c0080002e482e81054003d03000d50700104508001152101e501c0c00d0094002e5000140200e02e501850700040030050f8248181d6024944485460741144e08598540008002848059040c407440c02024441d941e070300f400a05d20380d0300c030320050803003581c402010401c1d681c0c2d00146061211810115014503468401c240c81b5106040e21300741f4010801c013201d2a0800b070075608208005c2031514114824080c0540106841c03842c1c41d5220b061924010404031803400d1010310384a0808070180c010800f09108003c584005000100001280303551019051b084551130740c02141d89140200d020400c4d503030010207500d1203410a0025042c24549500001e8541c07500b4040c00f84695404204a0184944c00720b0300301c2c11081000306025408401c080c05143e4000c4811500d00c01e034140807 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 660416798 1250 660415548 660415571
    0x80a1d1b0409140a23030913061e0f08030a0503040f061407050703020c06090315070311070f060c02010506090a20180307080c010c03050912030a050406030f0b1503250210 75
    0x1105c503801c07103540303001450514000c0c00412010032069507000f50502c0d00c0300c40200754810b1903110910695103a0350180200b40c81c102608004c10101e91010500d0342082c003000f2549078000045941c4641d000b40c83d01e0000b41c00346060001045c3e82010801c941e843d440030440950b812030010314030203000c2d4003160b0294150071308001d801d01c9066001a0540c0141d101602001310322421690408040e09010030b02515a001a1116030080041a43d2400301c00301101d00340500c0784907801055200344000d10491a003000820701d02c43c4040c3c9407120003560703002c1c602d000342c041310140850300c1c00c0700c4100750340d4050014200784030034101c0070350310702c0390050340b0300040e10f03500016680c10114010307142d64480d0001c0303842c2550355800c0120b05507081000c0086e00391904505000822404070b0700e484d420b4a82e4203100008007103402041d0201c040c646000080c440507511b10010f0140c0c00701180020b940c4c1d07561510000c842010041980c00140c80c042e4841c1c1f559030700030404640d0034150001c200704101d03405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 660418048 1250 660416798 660416843
    0x1507080a0603020a030f0311030d1a0a0b09220f020d050f160e010e13090c0603090f0f0303090b090105090f301306080a1d1b0409140a 59
    0xa2200a5010101800810005d4601c0c09001031490023410303c60280a50080c0c62070642c0d00c80444100b10a5a510300448a02c3c00b0f074890380451541610b003854094204030000b00380f8401c542000703105251034400042c82d101101c0050039061045442400031407000059a0043d4001411100710242880300113a006c5001407080c07449045410719003001104c0c0040207807104283c484019042001285d9510740326192032811002c060700145001411841504100d080300c02541c01040c105402c2441d208040340d00003145114a03034210b2404408075640b45015030040203030940c0180b1009400c03041101c52030041d4081d5100300864015909a0440554901d40f0f40c159042c445914a030184410580e60a41603176040e0001e00c1c2640d01441c020400c0c00b5281c4812555101c40000b071042810007264070300b50300030a0503c555404250501c1803104007119140d0301d0300010642c640c507180084900603074843e004803e5080c0c00401c000a00106501460380f2541e00c9002950003408104050703d9401d4407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 660419298 1250 660418048 660418061
    0xc0304020f1908071205070f030510020a0c020d2015040e1302130b0102010c05070b04240c020a12020d020d0809070306050916050102010209030a140f1507080a 70
    0x109410a0035a01004000c00c0c11440d01080003601c0140c0b50114012000700f1141026181c41c1504080780e9405141032440c00000c0d0700301c90900030240f481000090b01c0001d56410503420100701588640d080203044440b8032034000040d41c0139082072002810700010300c100310710303150160001c5030000540c1400d01104c00c0004908042d05002080304010025840d0301042d0002c0e001d0103141c070031402070b400054000c00e0310301c80b0100701c556860703002c0380d20740c6c0920856006540034244181841020f403036000b22181d0090014154004840200b0207003c8403240f204a4884842c2c1c0421803007075500300003560341005040440d00e000c140034145404a00005010316034006507401001c080341744c10011500c1d40406002c420f807900c665040032000883c280641c45c031921201000f0100e4000606800308000c2c950f1744900c0c15644100a00710190700c000c600032010941000c50541c0c00302c1d0ac441d90602d0845904980d10850040e2610040841c1c0c030300591030300800c1595140c25050711a600340e070703045541 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 660420548 1250 660419298 660419303
    0x31020a0c060e0106060e0d020301110c1b0907050714012a170411120a021314071d01031508100228020706030b010203070c0f05040f050c0304080708130605030f0c0304 73
    0x22010a0000c0790307d0042e4030000840d00c042c00214000e00f02c9842800d094000f6000244c1c540c104001500f8a43c0c92010203030443d5404031a0300d100f070300b86080041c0080c40741e42c501418071104c0d04040d40c2d08030000d41211200e00c00028000c01902c0002e40404000310703940d10100001022002c200c161094422a41802150031400b1418400024001c102400007840c1c8000c10901a0700a00030150b0b452011528210449186c00300d4244c45030389481d5903152004181e01d0a01a01510344450310714038440c0c415499200303080000300c03054000d003c284610960b80c40510144503030440182c040721039402600103030101c0c01c00121038000c41059580103e4800d1a4600140e00c4003008000645c829042141a40810300543e403401120b5240d0000e00d0400d900000c01064500608000c0d81c1050310445c94482003002c1304006c20304046450250500c8090005824a000400e841d814001c01070201c9142c180c00342c8015071010f5031000c0203441504104d55034521040c60780005002101300108403403064fd0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 660421798 1250 660420548 660420557
    0x2011214091b01210c1809062c06090c0405040203090708010b0a210602070f0b0f150a050f01140c01051909030e04150b0f030a0e07030231020a0c060e010606 69
    0x10350b44113070300184001036003c410080721902494580c003031984002c0c003404a00e400403c10a0920300300074140b000c0c41c0300b00e8220211022092100b91042407203690000d01c00c4408203030980307401004040c1030042c1e40003598442c2c400009d10103180b0f80011850111281c0a00901c510503802c2e04000788140c0c0b51154407440c1c10a5407401c070050b0b4050442a41c41441000c00500704080d84c2c455054028204404903003a1110100740b00e44c0f00320b032403182d951102d01c0d002407820218070f0a007c20041401486414081e180c130001080c01d40e8003408244030200f4080850549030f40e6041c0724903002e4030040da80d50381903c030845c0320b109800c4c2280c0140040103802d40c4480d8400446001444014031142096038043c00c91030b070001c039080300d4a400031b08000309403d210f01e45030b08003454104102e0f904c00c15445215031162004000684406691101060003580c0d8a1004581d0162042da0f20034060082d0b03201610000d00e0f420001e0f04140042016802030030104101c415149106080710b400d400342c000801c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 660423048 1250 660421798 660421847
    0x6390a020d060b0406210204050109150527070f081f061209050304120b09010203101e030c262802010c0b01061e02070e0402011214091b01 61
    0xb5081d4001202c02000500006013407591101043c000d07001c09207a406010503a10380080661616000f0f00780507040408080100c90b00725117543e80c2c1440540300c2c031801110540c81642442e40132846004404600c52480c48551400d640010000d4180c0c0690710f005c15401c0c1c01103081c100d0860345070140c4c0d01d0b1911640c40003500f004025240c851400300d5041c401502c403500400011301c10b0010300700400b607a40800e940702c1c490f490414031544000302502800ea1051003009180c8901c03203903030003c0343e00c44080c001300348643c0078040d2003140c03641c1c101a24920401e034002400d0b0480e81741c0d00d42c01105608050b040c0c20041d034a0300381c40d40401103c840038013090751110101c10030343d10420000944141408034001700c0da0381d100c2c1c1c03117644c0c264000030124202024401008140c0c224003444510035201515005040c00d000082c007040103007020f410440c400c550303401040001d50001980c4030408401c10ba061910b000e40a945000c0481041415000980c0510702940145011292180500e0303050180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 660424298 1250 660423048 660423053
    0xd0e030c0405090307050115090f02090303070b0402011103120601111615090f0b030a0c020f060a05040c0b070b06010306080f030f2203050a0c05010e0d060b06390a020d 74
    0x1030b04020b8441070460001300118000103c0922528442c01140000d0102d45c902c3c0c10741c02802c5811340003120203400d004002c9800b895401100301d03482d003640100040c44a803213600048410312955440c001641c0300000b40c500e07004444a2400e84580401d81c1c1d807000058241c45116100c00e007040740c0075070810640c8814400342820709042c00100c5a240361010945a0300c010b108800400c90b480b024030781c40000140038940049000385000d036901c41c001030509203490100745540e44001032041441e583d691010800300458020940c00406a04101ca5220b02050610303440040b01503e519012a24107070001800c2880403640f0b00d816040d11000d90300b0600e100c8035000d8dc55100d0300c200344108403165906240d540000b075804002c0c50040c1c2c02864085e00514200c91890980d42105052100c0115201e00d1962000358002c44681d0007400421707103042000200b1201d006440d6101041a49441c0800362010180c2d40000d131120620005150b149200c15010707124101903002030b40290b551800e4001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 660425548 1250 660424298 660424301
    0x1e03080711040b041d0f03040305030415090b0f09240d0203061f171b0405060703020a020306190624050a0c0f0b0a0f0b0102031c0b1302040501020d0e030c04 69
    0x507250050030128503440e81d400020129007088510029246420810002c80c540400c400382c00c0c110f01c42c00861074a81581c80b0700c2d80d80e000b0f6104502184014140101346588941030100007040f000c01c00c01d0310707221095605500b41e00040840e50050803008172824980e68940d008800619240b00e00030324202d6030108003001b03944001c1c941508080034030015103200410385c9800c924a807490741c501c0400007420300c040c5176042c0054a44a10040c0d410701d629003c610b0481164100d0300c00b00e80186d030b294000e00e001e90400040850283d03150140c00200400d11501b00340039000741820000410246440d0310568130540c811401d4541d030301c0310b030305a4401a207001b007008180509082c20410000c5613075503540d600c4130b0805401182c8135640383d070074400559598052400e18454401e4103000e030410110000b07590703009000b48140c40c460012255028000c3c41d42c040c0c00841c0300580140050304448050320301961041c49404c0c0180306201d81c108400313220740c0c00c1d41d840a80042c00f80c501c2240b280d04100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 660426798 1250 660425548 660425573
    0x40f1413110d05150a02030f180f0d050405010221040b130b03040305120708040b0403140d06090603020a0807120204110c1f05010f0e0103140a050d091e030807 70
    0x2140011000103014081d82c1e4038010900c5244070750700905400e00107050503c00518080c03c8004c40034014814040d1840000c1c606640c081c507039600340c11411a065602a191102c03580d04540113010301515210440d40c480001d2007911000c0e0212440c5518900c126620b403000c40010030b5101b0014482800071301165001041d1205281c0c1051213881d0f00c03800389060f958000c0d60100d0224a0000e103604d808082112400e40c000b20904086a10303240c15142d11802d081c00510081c200300d500d0b18181510000302e0191802e0b14103503102000101e8a6060200081c10580020381c0700d140710a2000400442c0014880169441d91001a0071980300b6400e00005d07080b14031000e2510041844548040003041161124030b1202c5090004480d04d407090704000c50f241a003203007030b01c1d8034400f2060020401e0740c0659030460b680049009048140b12100500704141e480e002441802220f8525285030350000f40300c07003034a5440e00704824403e28404480f4003000140710080101c0800e01c00c0c0004550b1241954 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 660428048 1250 660426798 660426803
    0x906021216080f030604063510061e09050601020d030b030a0b0a1406030106060f0509041d0f06060405040f020108190f090b0108012304080706050a0605040f1413 71
    0x1000384501c0c69682c40c0e12600880d2071042862004020006039180c2800348078000e045002c84088440011480c0d410312940361031020443c000c16850541841e282004640240300c0d8810040042c60f4448800c0c400c0c500d207410540303c9410b01d040012440e1901d0f0b108450180e00140c0040104401c1010b0580c0a4000e0320440c9a2500580c04441d0101c3d520b103e103a40714100c03000b0001000c0300c80354100e43c00894060141802a8903120003844020707080300c054420740c049400d005032500007850018015010741010110300f000e0b0070402c1c1c0e002980000f41e03a40d10f001a142910166603e20040c00b003124812507016010780c014410f2800554012802c060b0003100911142045620294a12041d01d100a044020786961000103005004203114442c1c003601c0d90034000d01c6042c03002118103000301ca100b4825015408440041400c01800ba0100c0700c400c2d901020920403481e00384070207030003008175104a6020f40e09000c01c5000717481907445954108101d803a6900c0a548403118444c80c5000021800c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 660429298 1250 660428048 660428077
    0x40e0c0d05030c011a040e0106060e010e0609100c030f0309030c030822080a1d0a050f060412050703020f091b03060307051201051b0f1912020304051c09060212 70
    0x5003e640e003c280241010526001c1c0705041c171280c820240000c41310f046010380e41d41d03403608105100d250f41c0056031104101c424600720b807440841c2c10005040f0312401c2120343d400004603480c01e1203a070308403c0b84881e480c003d42b100c40c0420310302d180640945000c44401000220074180100000340a681066040800c80d02205e014480d400400024005440030598801c039011030008644ca6000f5a02051a0005241c41d00b1820501c0d000c60941d58450060300e101d0f604100e8a408203803039002c00d41d03006066110b8070903050501030500e907450f545c01d0f010581c01182c244034000385904041c08282d0003040341c3c7e50302074001c880f400030200842d040681010b07031500910100107459030320340082150144650300009040e050004c00b184640c00203c10480c0741210030b2000700d4010b4403140c1030f1000c09030310501d03000301d902c241402102c03100c0150310030340c403110300c08800c3c4802d100c0b0001c2c0200e9229a410105040041846401d498800c5c05120700001640078400c00d160031350708400a403100c250000342 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 660430548 1250 660429298 660429307
    0x6030f0412050909090a1401140c0c03090a06030f05160f110f030a180602010c020304091109060c0102070c050306060f0f0f0931030e04020a090306060b18040e0c0d0503 74
    0x9142c9032400d40d4031a901ba8011440e9000344000280381400d000707115402000100611449108403040040040e0400c0c1d201003924107012106104582a040005015203041621404003400400c66600300e00c001c5842d22002899486180c0c091124140d10b940704c46040c405210350071505000c0c0320743e40f04200e002e5414a010150340c200042c200e451119140c6c036100026022003d20348105c2540032508581c1000480325416030040210f074207982e00814045002034640104c20110301c52440041d80040001030003c41421065000d003d03005e00c1084018100d540d20801c00d5912441510b44da54828204008a4100c0c5040c505076650800050b25a1122a488000140038038104440009221f15440804410340c01c420f036207240c0961056041381200c4100d91002000c0104002c1014002d550001d0004041c42c003c0c50030200455208506110658550003110050b801c01d40901c1c03000311340440c6515031840c3ca40144915070f8003400c020701c194800041000b91198034030ba801e6545000802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 660431654 1106 660430548 660430567
    0x40f1125032309030a060204031103060c0d0f060801050f3108031302032e0e03070816051c092418051f03050606030f041205 55
    0x502d42d0300c1003400640207030340e4451501401c1e030602c940801d040800c941c5070020030a4038402c292509501c84907006040d511001a28002160001031001c880020782c41c2d4054120035204200200b001c43c0d890b00003908454041e00e81c000e0400d00c0404110342c100a580c000c54440c1c5800701803241d40707042d138289181c050310f0680008100c110004085244507864180301141d141d0000c0a5442c0300c0b00c40850131030702074110f8155421450384844460840d40d110300c100411203242da40a1031810241c0d07512101c0551111343d4040c2c2a6a12010035404a441002110f01101084020514001100c2ea0240034014180d0059200d081c05c591745818501c4407555501d90200d240c2420000e50010054030f5081610305c2e0082900040080d60035200d90000c140840d0461415407001c01c0349807211400d0201030b2004481800d4456030103004503002800c1c1440f051440c550600e003503810205c845 = true := by decide +kernel

theorem cover : BRFrame.Cov 660251798 660431654 := by
  have h0 := BRFrame.cov_init 660251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 660251798 ≤ n) (h2 : n < 660431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
