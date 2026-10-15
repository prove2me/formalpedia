-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4278
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:06:16.380989+00:00
-- url     : https://prove2.me/submissions/e892710f-6e98-463a-85c4-cca0bd204a88

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 769244604 ≤ n < 769424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 769245854 1250 769244604 769244617
    0xc1206041101110304120b0f0f040f0b090a060e1509030a050a120b040207060b10050702030a1e0804030b150901140909030f1201030210141611040504060507140f0f 72
    0x409036070402c0d40300d904150342509548000c2c7c66000e96070086c012001141c440498106a0245400c2c12038600741d110307401303481106031340245145035000005100b104140002e04c0c80d15441402030008180144c06507603204261842d004036280c2c01e00200700d046200008a0b1001c80e010340310f4500f04550500d017641c84014884000a000b52200017510a590300c0c0d100a0290511840001644010348024820703085040d20b00c4105101042041c140960340000d611103440c1e5101140e0a41408c0b401c3c1c15903080d1200300301c018810078021402004000109110612035001c1c1070301130180a4900f410090041070a1140c401e1101c0d2402481000e41842001d2a50164801c41103902e0a10208140052030340b001c2c2a909400a6445c014021031a0281c02c0209941903860700420044008050f0312642c8210a0b0700b124042d4505c5800c000c011001c00c1901000c0001442000f4070300d003505140025040480d003c0001030248070500740e44c0700c650740550701c441ca5980026030600f13000c1016480507500c0103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 769247104 1250 769245854 769245887
    0x3191401090c0509630705090907121712070201050a06060e0d051606090501120207080405091503160e07080103150e0703331406011b140c1206041101 66
    0x11030602c0c10102c0385d41d4031040800c404110789801148042c01074142407480d00f0547c07080e40e003803050060300200050583d0903220a6000360f1852916843c08030007a0b100351032841c1e42000c010512007148020400c11900c80c0110740c00900c0395545070101d00046825600a01e4049450b0000022550400d20954100d00c1d100d04115221910740030881103a1b0313034056002400180e0107920920140d40e004c02180c0010301994000e41c10040283e407080c0c0035016901505006034100e41c0090081d40c42e01088445540780039082c0c885145241d021b2228400c8140100d00d42d0545000c0841c10322440351030541e04998010b01c01d1149485402d04000181032100c0000341a40303e41e039404000719030089a0388901a40d80c2041c036001030101d1400c2203403600c0c1400d83c207041a180038401c99420b42c2182040c3d5000000746030101c41064815031456640200e480042c3c6608000351a82c4074080340007680002046040303407202080207100e04120f68a40301120010128001102401c402c0e50151410301500401d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 769248354 1250 769247104 769247221
    0x209181005180601030b0105040f11070f020d08040e0a06050105071212090203190c0b0313020d0309090f0e0c0f0604031707080a02150c0903191401090c0509 69
    0x2c689249103810003c0c2c01c26940552600010071151406200b000500c81d90760714107004250501d000038689005003c000360003c03000078500710440d580e07603e00c501115804400700d5281c1e92940c407801c91120040368014681841c20801080d150f02941c182c94105500c500310207100c1500d00403c94104402c460310098040e150840030005075001e0050b8180480d00340d50844c212041d504005d040c100300c903800304079804800c10501c603120500810342c00070f00b90192504041050985401c690180b02540801d0402d454001c02c0c07140c1e4041e60308090085945141211000b140340010010880c051044480d4800410003082002800e015941c100c0c400c003010a181c204542c0b41c65460199000454180050704070b00701d60400035130380f5064150003106480c0d80904150328000840e5440c16142003001d244402d00c0c4002d401c000c0c808a0790101d80300e000d402403145000c1c52602111080050140900c101d800a0019400701015000e0141441030440c0820302707072504402d20381500b000e5071080108200b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 769249604 1250 769248354 769248391
    0x30913060b160203070e0903030a05041509203c0d080c01050c0f030727090207050c040905120313022e020a170a02010f05130209181005 60
    0x203400c800b418429440740d0003002c44040920405080001da42c001c101902214001e10500b01000016281d100082e0301c400a050b44903414251043c080440c8000a8141414405410007900d070001e00001c0c1d01e0801c001c001501121304018161240ca0800c402d41d0140d0040105030901000b004808240c0f6882c400f01460510300c0425a00c00c824501a10b508a000071b0345403215034240705007584640e507843c1450a05213201d2600d2030760b1202415100c1007040300a4491140703680e8030325034520324042c070110300300640d03845c1e031804046d400c440d0f015162802508588085820140036245616500201414110101800c41c060340c1d00060000c1c0485010295903d0058030303040450300900061409001c1c84490003600e620600c840340c120f2604541101503502c001440d83c40004c100e402500281c3d503180e00c01008100d00501129001008690810061000c0c464101a10118a034025144d40003a075941259100707a16918912f0450682d01c9004c0755140307403150390b01c8117030480c49046081c031910701c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 769250854 1250 769249604 769249619
    0x31122030203030f0403140705030309040f140a0e01270206070305120f040b010801020a0e100c0c1409132a0806181b0901030b062103090a0f030503091306 68
    0x2001130040d03000084d00018148107010001114491940c4984018114107007402c002c80d440f8000d4550843c0525101e80d000c1403501210f0b007041707030703204408001118640b50280c284409040300600c0c1000c90f528124810703c042e000714441c102002d010180a5180c070300c096003400004d0b0701c00c3d14280c0410405000741c2802d00c0c0141e0007140102c4020f94070350002e040c00d0074030003640c50041e40001166841085219822a000360f4001340340001100c0b146410420b6540a0710301c0359688800600008000001041c3c10302c01c003d10349424502595076200380d41d222604043c9800e1f03400006450707100c7c00d0f07040d941120107021401000c0c1d403141c003c207080d00390345800c000c0c40c092041e9050044100d4441c04540403800410004544501c03801104020b00c6020021500b81881030001a002d10505000039505844e100541100e040d07080e84190602d0781300940e00c6480c4e40103101d10324450380c040c130300018151000540349000e40350050041d601e00403100d8100841854108807081210361034400000700d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 769252104 1250 769250854 769250857
    0x13050a06020706031401060e1203041a0d0e1f0b0d140102030a141303030f020c0a140d0c081c1d0d110d0906110a0219090c03112203020303 61
    0xd100c01c0d0002c00d030b11820148090142d03080300940c48400700c20100100030321903220a121503c800b054440200714001c95400904500c0356070400103421845840003410440b2500c000c0640389810801002100c4242c40115100e0010f092440f003c0101035400300d0140c1165400f0034040d40c1d0041c6200061074090340ca51041120400412459035800f00810000301030b80c1c05001c451a4040c020b0340302d0391400200ca12000398410001508240da42d84006111800c545e04a8100309805011101c45000901e81070b05003440117420000e00b40a0001392000c01402240c4145240b5845001a820311200e10200045200784000400d00c207603c80580b040703084041e08030b401c04d4010301c41c0034142d01c00342480040d00c1103030786a0100c1002c4c3d01100300c0500c000e034490121819203005c2d1825002401041402030310300242d40c140070358018006081c116180b81216042d00445444035014444582640700a80403105050812411840104007000d0a551505200d07030305c40c8203c101101461ba140c3d00841d00d076 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 769253354 1250 769252104 769252109
    0x60d0b1f030c060e01021f0f14040c0302120c030d0e030309090108330f040f06020a0206070f0c05060c0c01060e0a0914070303020a080306060705100c0e0f031213050a 73
    0x460080e5005202d004d9101295401807002070008018002d680104a02100d24001103aa6000c2e50b0343c3c1c1804902009800a1140c0d0811180444003400c00342031810f802e02c0d80b884102e00c00c09520b80350111441c00451404504000103000c0e1030b01e141c000b0740a0b08c20b00034050203954103010030045e007000356450804c0b0a000c3c1080c00010a900000b82810080110a110059031407080c49100c1e003e000c101002e101ea880300c20441030010742d4a4034603103080b0709040c04000a00d014004140030242d164000341043c0305180941d80c1c0341d8400c041c0813041d10304100103200544960410400648a4444100100040030140c00000b40717559492801c0004d0302800d4500d4038074030b61140d0b4920140181c0d060750080e41e40941c00074144040c034607940039603a000907107001004104044001a441c0d580d98040e2481250020305980b000c07805d00c044200281540420b8101041c0303520128039807418110b81c00c003c0020050000c0c207854101e0020001560081398400551b0f1078000c2011500340c66000c0d04000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 769254604 1250 769253354 769253363
    0x150b0a030e01060515030412030e0703080c01110f1e09040e07030b010b131a0702040c0e010314070903060207051c091a03070806190f060905030c0603060d0b1f03 71
    0x1901d84680d00d1840c00c0d00c8440d48000d02c103004825243c0240c130410000c0300e40150380010748500ca4820700000b0b9025040282c0c003907400b409501400010b002c0400d000742925140312000b0080440f000e410542d09000d036548507019844144050000768a01d10703043c0201c0e83e264a80d19041c045210300140c1540d0900e1041c1c1425007000e041041084044521180075041c1d490080d8200907500500c5002c00c00c8520440652605685a054602181604580987da00540b06012030358080e00302800c0c01003980d41ca80e002901e4240f004204c444104031050040a10343e0302c0040943c510740301c92020790403501041c1ca50b0f014540d0700340d0942c80b0100000c200c0c1c07001d646a04a0345407034104d81035464600801095550081082048441644820318660007a802c4840a503001d2105620a5031640d2540002c0000388241c5008181e00390408442c9045450480440d40107210980502416010a558164001c205078041c00005214400d02590200c4c1000000340c142c400241174041c4e500941c1c0c13041c1ea = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 769255854 1250 769254604 769254611
    0x603150f110a050a210903050306190510030b130203090c01170103020d02100c0c0b04091104050a03030e1302070b07030c0c12110709060f06021c0909150b0a03 70
    0x490110190260715140780c5144040c0c2e00380203403240b02419070311807000a80208180b1006007540010705004900f201807200400700710109852501601c0341d80103480e000c0c824a48449100d003007003612160801920809800e105aa0151442c140d02900390030440360340c0404040444c1604540700d01c0910303c66088003005200c48002080054000c103a040000001c2d125810014009615014886201158180d40340c61318419030001c06c0b5034801c802c070402441c2030400c07000028060712101c090400c0e54040d400410210310165000c10141c800da11501d42c00c000c080c030007000440c1c044c06203112501c001038080c00c1c41e00d00700484c2100326440010111540c03680c1400307024003190305224090f07851007203040868a900c0e0944815084c60810400e04040002288111002ea8000d00c03507040284070700441803000903114101a545420b030745c0100c400600c24108485169100300001040700e520940f00c4001450805201c03801074103030b02030f43c0c6081d00e1040000240c0340c40030000500701000c4039500003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 769257104 1250 769255854 769255871
    0x7021c06050c031e0a11030f0f060103091a0703110406030c12141f0f080705090f01050d11010c02060a1106070e030c0906041104031b0503030a050f0d060315 69
    0x100211071000c0d0040d030000c90300f0301c1009510650150004a10203056400c41d4041d5590074001c0007070042e0444502c40e0440100070300c411203043e83c0802c0c1c0107103010b19403100c89a031603a004404403035150710090301c1ca044806411a100500c0b11940340c20003100e10380481c800700800c038880f102d540107500090010f0b9031030405404099200708040a2a03540b00c0041c01142c8a04892907113819003d0400c01c1c0440c000550340300c80815500625004200846240c0341003941c0f5107815840c0c0c0010311459024410140c000794480306030f01c07202416640014012041112103803110f12110401401090500c1100c225900159841d94040c1076a030303510b80d8851803200540b290301d1b81422006410001802425103c0080c65034000c680460411300585030121070341e44901c0064041c22007420100078001c0001804001c0c0211280d04031500c1e054503040c511403650320401c0c16036034400c9001031000144240611613811644100400720120044400301c2c0244d00d9031603502205040c08070104d652a40c2d07200c030307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 769258354 1250 769257104 769257113
    0x11091609080309010804081303020901080708061602070e0403120f0203180106050f0d02060d0f0b0102070f050102120304050f12180a050a1401120207200904050a140307021c 76
    0x40c80207481814081d43c1458007400020704840c101400080c0502004541d2403c0503006541c80002150024800305442d40d5500c202a04c1c0d07070043c014030110b03001d160001950214007403941021a21154000d00340719141c8a00c4242c10640540110300304450001c100381c0b410814040c6101c914840d244c0142e60381810080710002d041d03840340c6044c1c180d06242d01008259103040d2080d5200006030b41c900e8000c011880013400a00c03901c015511514544144125030800039801202d001800b070b001c07500300544500070041c141c940d5100326401644144a82180c0b20010000745800a03c500100c4815120000c20035080141c42c851241c88102c1c04603600c3c900008009540104c039130141c449444a604003408110048841c1c01002e24121100d82c1c85a03660b407107001c9051301e01c1c0740050119218010f5191030008403a00300d40b005480e079840d000c41082441c1c400d8240b0b000300d60000040c08041101d03507030000c0b911028803080c9502d000601c00f60000d17803074159801c121003000074410b070030381d6045140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 769259604 1250 769258354 769258367
    0x306011e180e1b2109160b030405030d0f0e0f100f020a020616051606150501140315031c020f060903250501020f12070801050105031012110916 63
    0x6003800300d504014000c0a000c0552125103411002815a0340c0d500040340c1c4110141039030385100200200d01c000c00c64092804075480c041601801286e0200c2c0766203040002942c0001da07409000e030341007001030031500c00c0c85900002480013519004103481c20109500d90501300f2400b504c104c6604010150801c804e118031803041800c1070b0000440c00e055482d00300965428008103071698801601300e21110a0740144e003660201520342189100304419490490080c10300f004403a095008442c502003503030340c00f55a0340307503544600c01042410740e0f441b0006850001c0e490300805406008444010300340c1c800d6450b00710020341080d0010b000441c400b4a02c546025030042c00da01c040d40050150280d40d5403569500050f440701d10700c2c039180010450400c2d500a00c0b55405000c1d07495000140c0256004040340035601c03c2c0465168030201d41c1e0395200541e42d910046400b0b02d540104000148100900f00215005541c003849116440d403903004003084201d0002d4400a1003807142001c0c0c0f40c6440d0f401074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 769260854 1250 769259604 769259609
    0x6010c08190e0a1409100f062003030c030f060f040608030723030712111e0607020c06030c1b010513120c0206030103030f030b04090b19020f09060306011e18 69
    0x20f4200340082e182c51864801c0b59000c0011503c41c0e0010700c0402c01100340301c5507000140a10003060300da5a640d4210261040c0b810f101c1d420110380c03500e01d08030540304020050b6882a6002410181340d0b80c0c590307400c64040600103003042e40c001c01d030101c0040c49031118810302d409803a000c0011551a001070030030b07000c440400d00c4107811800f0368442c000c0301074401006071242e8540c464203100c1c0348a0004001c0e55001b00b2984400401d100b90391b003000e0040b4007603007108880490030b002d0340c040c3d07100c8500407615518409600c58201c031080002c690380072400d43c001c1c03102101c01c0c201d440790700459903081401e451081d0f90410b0b403c0c888800b0b410034012540c041070503000700c50a141604e405640e012441a0105100140510250030044500e19000c0d40000c905094010401c10102031039182c960001242592406a40645091b240601010610131110303045008071155041103001410030800c2e510046c41c040c100b11001b03071084040c80001a41002060036a00d90203140010744c03c6420801003541e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 769262104 1250 769260854 769260859
    0xa03060b040807090b03032503090b1603050a03390203070b190605062113030c060c03021209010621031205041b0603060801151a0306010c08190e 64
    0x812041120040c0014600210ba000304004a684100702c4000f034118050366424444801072a500314050380342c43d0284003c020309ca91103440c501511408100403a01840c103010840c4101c68150002183c0248064110742c04c00c0e01c0c010403011700303900e1451410880700c0c17040c89259840712254030080c403451040003011800e510040d401c20312a03840300a170854024280381403418410200300c0101400360031160240c040980266910010300383e13644911019042c1b0a15400141c0c000b282c0c00400214088403c3d580550304e00300b405050361100030080145805110915508111001001c00504440c62040403070200014119142400f103400038a4003e180c0d80b006030b1100b18100000390001003490030326601003030010300c5680e646060754010311542e020380c158411008000807032a2f8940c01c50343c2031f141180000d210b1100c8404d4403c0d4540494018855030410500d5865410488000a164020b105142000b40d0600c580c0300e9032443e9220318481511010003007101c0c1245501b005240781d642005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 769263354 1250 769262104 769262107
    0x60801110c0f0109020109030803040501150b130f050a0e2e06090803030103020a0e13140a0224190e0d080910210903030f0c080906010603051e06130504080a03060b 72
    0x325030009102c881035003c01003122601101141c0cc0c0582588400d0703090790800f042c001c4030f03625110000c4080c0c01003a00f100018808075004521b003402c40b00c003001113840280071011128284003103000c01000061220b4008144500c400d000c11400c21000e5500140c2104070440760782c1040302c028102e40305508501d081c0d5104000400042e1030f0555840c0445a0b00e48140c0c5207a00c41208482d07a5209040c2d000d081d8961038031940d05e140c030012815590141c4200c1d0248990311000349112030185002d0880c49018405204c003404100841454902c0b4161a10f0032140502c4100002280e5004486c82a0f6400364041072002e85800d06140c880360707203a10f5060010000703080200080d02c02400395010913400c6c0e292611401014026003000c010300000b48020311038034041200003005910702b211410b001e440740400001c0c00500a105180c05048800380042940000e0421a11f50040143c61640c10243d003408520b005101440340c14000d41c4a0070040b5955202248000c3c2a00e844e07411021910b0320 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 769264604 1250 769263354 769263371
    0x1803080124090506070807051f0e010e2d07090c03050f061e06070c030f030201110c0606091305011b09050a080604230618120a21060801110c0f01 64
    0xc1241810b02241c0007200d01e5070340c851080c54410a58010908000c01d6480345601840303c1d000f91503492015044194010800308140c03076801c40c241c8070b040c0040c0c25140c00049121030a0442c100e02c00c8020031200395110392140030103880515004695104409240c0c2d40c0140410307141e0b060245035004040c40d0f100540608000d1700082c1c4200c449002d900b030704a05882070204c641c80c2c00c400e55010740e030000c0390703120f085980303080c000007450100c6401c900551a00130300d0a010400380b41500c44040d40f8a00401c05681ca02c0240080c4a002624100b451240603d4450011b9000d0150080381400102c00400d103000038200501035048a03044144103d440701001c0c008130400144c46da50054102c0f01c50b3350f07a02c080b107840c0c035819400c00c98140858010601004850021018000f01d558280412261440c2c210070303442403240103880b0b003140041c0c840034a0102c003c0703500100002e40c9403018030000c0d00c3c907592002103003101c14021601075010070128140580d40c1d014441d1141800e0400000d110100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 769265854 1250 769264604 769264607
    0x10f060e040c0306080316110301060e0103060911042a0f050a080c07050f061e060a03060c02010b0907200303100b0309030f1305040b120613061803080124 68
    0x659080d114000c03603442207440000b6110380c000900a10b600020b5a54130b0000600300ba0306040444030640c1e0381118131100f01018101449514100d500350b0311070301c800c3e03401c0d03030b48150162020020940b01d06401c04000203481d96113200307640e91900c103c003450b0710012441d0741c0201c04c031010107040024000c59400e90b10810383c000040310020307441c526020090341d550034004203c41c01000805003d03442107144000701c404000641c0d074000c1c500b40c2d1050140c030b902000c0001801004940030780e00601d80c1c46080000070100d412001c40110320b0300000c102c02d05210040b80c04600100c0300c00c400205c1d8000705001001303100e85813584aa801c2c0000e1491407401044030014501c00340304840040400100041f8100c03024401d94416140310b03080c039551183e68500c0000c11240034001d080c866031401c004007840d490084a080400c0d031120000d0001c1e0b0783c0705042c030515a80001c0069464681314140c11000a5000c510320031414400c1d116440c1950402040390307901300c444a0b025070012ba1900030100c240303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 769267104 1250 769265854 769265867
    0x90b0906030d030f1104030813080106030c0b0304051e0c0a05030c0306131b240216061803020402030906010603050c1e030402010c1e020112061404022b02030f010f06 73
    0x104607509002c00e2184142c00c100d4005e0102c9540300f501404041000b204110601e4014000031050702303004000e40f0b4075414414200c4806100003400341c81120000c00c4400c0c1a000511b5226001d0001d4079004c2001c9114a20b0645210064182d280c001601664080c13030420f13030303900143c80b003070f030040071490b05c84c60100e951504054804a500200c910040c020415801d2020044045407d03c60118a0b610b400e000c2d150650401c00840c04900340048041041c80080c00d40c0442c2880441c80c0e030418a0320b030050b00e00001e2740c0c40c1801c101c02d00c601d002c400340c5c039030f40015801804c0400041000c0d41c5010401400c542001d8042d00c0c18803030030800b01800c03040031000c0c09040c58544110594a441e1480162080c107450343d00201314564a8020006140401c6c511242140c002c1e01c44c0140118031104182c1218070350b02420005c1900580d91a00c9410702e607020700501c23400c0c481601400900e0203098070100c0211950f0009081d000010440410b0341901c2e01c42c0102009910003140a040c94800380c8803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 769268354 1250 769267104 769267123
    0x1005040501140d090533042f0415030c0608130611090d0609020117010f0e091005090604151506050a12110705060f011410030e0d09090b090603 63
    0x100c820100d280e0342c550001d984001481e540c440110345031500760b1040041c6410060602e40200b249058800031240c00c01017210348110b6024204149682d0000e23842980c1000d07028411115115104000816490724840c2a002d64401c044103c00305103140b42020024000381c10010811949100f4003240b03148003c0c600b10040e9120364041142c0c5600aa0400a40240c5180c2036003d030b2058820002d0096036400a01010b000b070340c940c06a8110000000c1804400b071041e1009030880500400c1a51a07140c0b00ca03411000300c200b60794006c80d005021009a480c05e84d60900150041010b100400441d028004131080c495201400301c1c041040100f03006d40000d1041030140440040c40c446280c0c0700d05c841e001d9584c0c2c9481c003000720f04c165001c001c40c0c54100381011074082c49040080b51688107a407031020f040311904100c0500c01c000301000e206255a8200c07004060548840b03019602070342c02e110803a044101d590700d010403985800c400c0b07010b65103801c100c10b0180070303504140706440c1c40c003040b107820 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 769269604 1250 769268354 769268387
    0x705030a120f050a0608010c020a0804050d14030705010621080d050c13031218081b01020307050601060e041406030c01031a04111201080d1e030b100e1005040501 71
    0x445080215940001d070202c4601c0140e8546000300700030602d020390340060f007950142002042680f0b028442039030b99040361403025240c50004e000801c12450031a040160151113004200d8540e404401120301d1600180e100302c6080c0d46032802841024142180001c1c1514210b51544c8146007a8481c400c0600c108140c0040c00c40e198400504c1541c03c1808071390b040e401031640c5c560340381d949050000070400408045000140307001010f90025680380610300565440d03502412100c0d24100c5509000600ca410040c1540410300c1040c010801c2402500d0003030500d0b80702c941d001c0106c01c0401007206c004a200145442f0a03909004994034000341c1c40001c0402800d000402d0340003c00c3c0b8000300303142490000e0740b040c01d0800706000380344075034080d1815112400000c0140d03600c82d400d403a19222560040e00c0040c40c640b2031203504904d0680f01f035840101ca070a0000d020483c08002c0303800318929041c9003000c21075000803006103080c9944d0b026444141850300c0d50605042c00e0000300164100004d089 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 769270854 1250 769269604 769269617
    0x60809070f03260705060910060f0b090f0303030a0519090b0601120e01241202060d090f020405010e090d020c0f0402132601050106020d0e01180503060109200705030a 73
    0x380d00030f0480d8a60070300e508428000c2d07900d50381c092a18554521040701c50107000d0190085130340039110310b402800203880040486903900c50034a11100380d030750001080c2e1030f4070032031000210f20b5a403001d01c001c60241c440c0441c0811245000010300c590043c0d0700c60703030300c5000c1d2901070f07040045614503003070381d0b0000000d281c0488440420062403000d8130103032450f01d0165182c125a00034540c0c44d0540064105801405003545a41c3c0d501c0300e0146200c00e90010350020420040c4d811201a181d10080d1801c0c800e50005007000b1203600880d0884c0c0090304410020000b803818010a84410010b02c210f0092510080980880ca00003107010901c0ba401c01c1e5006603008100f41080c2c03e41c4141d01c40c0600902c18100100002c8000304414a1040c0c912404442d468500041512803001c03400001c1d6800e20341300d00e034005a80600440b45030144550b401a800041030020840341e4007801414002d124050300807820041c01501b001490900c1e545400b2180d03010440f80c0f00041000c405c0e98000a202d04086 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 769272104 1250 769270854 769270883
    0x10f0e040b0307090c030e1b030601030b04060e010f0207051b0109150207031406060109120309060507081b0f0c0301060e18070f0927020a0302060904020d02070b01060809070f03 78
    0x2902e00820f5801480c01541007014030f0385003aa040c0e2080480e0200f06084460101103414200c400301789008546815030001d00040c4049048640d403c0d0300107104101c002500710840318590f003150b5000c00300e5448141c000400ca028001d041103000550500c4840c1d00041c00780c0c0500107084001b49100704407158505102d2044030700c0c001e0001a005540140455401c007038162003c036180c4004507030030350205084500116112241c40c00500c140c0e945500c6c2ca0b0031050500600b0341d829002840110f41590040107078100d0801c1c0b00012402c0d028101005196144880d4402410810711a050781e000344c6c50003070100701c0b141d000944550420b80d92445054108903848c4040e0030000b02c0e4011460300120980300007275981c0d0690000441e0540300c01d4078a007480003540c040c00c4034504e07144042e43c4501400b00502c050f240000c0202603800d00148014130749007440c4444000c0c2d800c404001e4a24918603401040503a070000c1e04558400e81030006040f45d5810503500920225003808094140074110341c1c003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 769273354 1250 769272104 769272109
    0x230604150e01090605011505030118023004031412010905091c050c1516111903050403050d09080303070e030111220b0c0309040b1824010f0e040b 64
    0xc0d001d03805984000c1c4010034040c1445406010301b0f00c9641d00b0102c1c89544d540341b083c4a101943d05980c1800e01d495448081c10000f03c010b50011410090f146084409070041ea50340d1034007460b426240704000d141c2928040c1070182c8004866140d4001c010b000304540d0325284040301c02c41d410b4031101c01c0e000171561078000e411403801d8141c030310030b90400759050f03030950040350010040c20421200300222502d25418100d09080d050040d1044c0c1150400040310003000345c02410000c140e0741d1780404482d826405d2001d100b01c50f003240e200c1940480c0c800681403040c80410712275000c05004500b0103c010a02d4105031710380c0d91200808400800c2014003081d01181c0c0d0a40080b00405005040350b5154085031110b080b8035080050802c1ca050003200001500c0030028007076580e4100440040d508180d00807041c4005031582d19029540210720103500f0251034106160240a540c1d444500c16841040024190203039501110a40c10712003180c4002d101903078446c0c2e28009004d001d850108803803452502 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 769274604 1250 769273354 769273361
    0x60c1f020c06070804300e011e0302040f1d0c03090102122e0602030906070606050405010311010f080112020d080c0109051c05030c0409181e23060415 66
    0x421061070090000b4003c08070703801003059000300c0c05140f001c54005d07403000c008280038078002040c0082503641c03008180402c2c05044000240b817070604144131850241d521000300120090010004070b540070800b444406940200f80b405400864110380c00e200495800107c2044001c001468030b580007c001039001d40e00f90140c030008862442405854207240c0001a5a00c90540e001c2454009000c0c088a6580428200900b01e4443c0e03009145060740100500c41c40740d2004500b03490b00c0c2e4550000040e0750700c440c82003900035400340743d030680c0344044038000501e00f60440769840e0801110000603c008041c0c07210f100c441540c101c0f80100d403940c40e4540720105005a0361182c00c04c1d46030000003000c0c4000401d4100707551049048075000000f00010568140c041030710050b901400501c01402980100e1b4040003d00f01e040007002070003141643c4548481c0c1000c00500b480607104842d5908020400d48020302c650401d000517261007000d20002039075100300600c09000441200302042c0303040032030361 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 769275854 1250 769274604 769274617
    0x609211911120403210c03030c030e0f030405030114010806060609120d080a0f4b020a080c07150902011b080415030209060414030c100e030705060c1f02 67
    0xc0a03550a42910102d0207900d401522050356041c00a0f019501000078110f003080d01c1c3e10f4691500e641040c5152422801010280c0c12030090580e02c68802002030810004240b000420400859846041406050a6070303400b500e91500700a1020040c0014600490320942c0807400741d441507101c01c0418005964981c0c0d40b0441034060141e80007040b0794070340c00400e0070305c18007650206008650b00007141e1011107500b10400080040d29041354444928205113005040c0c072107802d400412402c442c55148020200c0000384203680d40028800080354011741800d0340809a141d4260900f03a041c1c1341c2c0350814282c006500d0780c070b941e1a800c2600316070051070403c1c1c11128030200000d400c4034a113409000c552080c060040c0000d000064030b104540701e4003c80354010b0016054078141440c00b6018811b8030b00c41c403041540340c000c8014124081e210200110030003000c03a62040500f00e02d000902d81040d1054000d14003800d802c1100442441340000d81401060101c0e011400f50108440c03034500902900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 769277104 1250 769275854 769275887
    0x610230c071706041a190906090204060e0f01210206072102010c2307020d0303020f0304062702060f2209090213020322020303071406092119 62
    0x80ba00d1400d00000007490300e01c00c81c41603a40300703003070707a1030030880096080101c400100d0160764220401d00c100c040d800c84425248a1000810300c24001d6000030296074154014026038001c013010050b000d0b04006400b40182140140700302104c580d00892a07d080902d240640603860009c0c0001c204410084181c0c0c0030301d40f0b54a04088a10458002800303030440c003080b900020b20032110b80c0300044020b6041c00b1191424407081d0301e08880c40e400d002c82c00c3d070951015400c0c55030920801488015450080d0b210710b2080d0301c00031b6105048400b05030a103102046d04200c00b4800020710380144c55100460382e464001c201466290150518401403e0059213050713034507170382c84110014034071005410103140284221030000690801000500403400704480d103610400f00c2c61440d2400032085000001100d0014043c3ca190071800d4a5080810181900340f04085c0c0c44001008a00f2070b050103d451315403165901c4406403815440212035500440c41c1c00d005014840e80152a4103018a481400302800f8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 769278354 1250 769277104 769277129
    0xf061e0c1112040806040201110703050601091401060c0308070810030507033f0e011412160c030c02091510030b130606020303040b04150608060610230c07 68
    0x1040d0010040032103880c00e001c8600c104a142011072a8080c00d440c141d4401c00f00800c090b6595400449409036240b03141c030001d01031000c010021030001c0c0312240c0a0140c504002c190110f01210010040701c0592081041001ca0050800002e60081689401484c64030701018140c58002405100d58117aa0006059210b407150010801400101e01601600711482d4200c50358595880c0703001000420f00300e81c84c4082e03e5001c0c441940d000c0d0140c00141e41043c98480d100c18038031207000070360343e0009201a105500c1c180030090048034030541c101d0810b04903c0c2100c4201419074000c0c000340c1e00440000c0c0b2507145040021003a00b611040d103000440300400303000c011544104090020501e840c0e48a0080445002c801c0d0440ea4034021882103c90907801580703990b4450301d80502c100b001800c202c42a42c51032888406400f10341c01858040d001c5600605210708022080181200c4003600c09803d0101208041812504134110380c03001621000700039544d02e50320078026003024607980110403111070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 769279604 1250 769278354 769278371
    0xf07120e03071a07030b0607060c02031e0c010b0a06120f0b151803031327020a030c410c102301030c06050f120a0b090c03040f061e 58
    0x221500003600343c24200c0080e6103408004130306503000d954090303810410400504001400903805800080424810350f400e00f85884410001781201d00049503610740d0104940003800c10030f00c2000000d00c0c1c01c07075100d480c003480d01c400908000c0c4c0c0449405200e9980328402080e4100d25080380c0440d07600281500c000c043d51901000b400c3e0019240c1d107c2c850342140c0c1414a6040000880f07080c2c10041da0400b50032840c02c50a81044076102d55006100202168040103340460029210a82c17590310042813000d152623008228199070780b18440a40b820101000c003e0030b000700404420303102c00300003074040300380400b1810940c4100c050003406031082d400c60304001d44c0e0aa00c8110700103010030781d6010241d100400c1505c0000280800750952041103410011a409a0300030401c0c01020002d181c18004a81c101a104040840340303194281e842e000020594a06410300e02c0c4e00200c0c10b812036085061036115121a29008880142507580d69030761301c95040307d16103036500c02202c0d05105210080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 769280854 1250 769279604 769279613
    0x702040b13020c150702060c0706140f010812070f0b040201020a0803131703091b0a1707080c06070302030715061e080f070e06090403050708030c0408070603050f07120e0307 76
    0x5000103140310f0365000f01091020703046681510107010705550750041038513840d40b50390504c8030350120724201d591a030b036a103218100700300c040c403440c0c0700c0c42d4080210a19989041d468a080c2080404003035441982004000c002030102803401c00c20b103801003414805a510b500c0184c2c5010954800074114400100c104410785000c2000044e90301d10400d070f020342c0a0240007401805010a680001080d0400d17180030b0705084166210008080b0010b0024a00c0ca68549001d400018080300d078007015045802d0601441004004070382080000b80d0b01c0e50301e001d2558a009450707015080d0001e0146400b1444003e8450041e003000002d09206140c0e8085802c410b00100002d01c00d0b0712600324140201c81800d9015200031034000304680d01e000030b0449603501d200401500300700044c0302b20180710b420301110300030031105009107201c1c0b03003c0c4e0b0700550b03500e00f820320700d5191040175400f40c0704050070070040014600b42c001e003c681207122420450710a0341012800c001800c201d5450307900742c1c0b2001c0750007002c2c003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 769282104 1250 769280854 769280857
    0x20f120405030c010905090a05060307090c1106060f130c180905061e060a12090c0609030c120804060305131403040509010b0a0801120c05030a030c03020d08060306010b0702040b1302 80
    0x1180300320308568003d0380860065903407410314441e940d84100200700007640003500b504003a40c030000042c156006a07841c0e0351290121281003540f0380009121588001c0c502d502007281c50381110007100d103810460300b00d6002810b0b50001480b0241501d80343e074031508509009400103003c4e0b003154165030441d10340b6600c01e5402003001b129140d1140449440d007a801c81c0c400003a45038508000f03845103192592502060303c00b61020000310b2401c9a407245140d002ca0901034444015001503a1a02e90480c6542130070440400950000409441118000ea0000b80004103c4040782d104d81800b0840ba558002044240ea4095401810b60700c034620344011188400702c010410388000301c9500c0d1050340c0782c1341041003038040c0004107800314000d000144002200720342900c0b10b49214031026103445464001180c10a411000c1c102c0220703401085004c02c040e018098510010514642399416140200020741d842c0c4e010301c5211341d85480051501c003503441c1c6401455194502a0280080381d80343c0c41c03118003e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 769283354 1250 769282104 769282109
    0x2030f1303031517060f01050312091903060b090702031801030e0a0f080c010e03070804030f080f1c0513023114060109050303121f091a0907020a03050d0c020f1204 72
    0x2c0c0d01580000408528014006c0c0f03043e05c0001e4010010440c0e000c3c04075180c1d91005400c164850321084040031006850b140040c042c0d44541c0000c01c000c51110180698000b001d00040290340080c80000180c1560621041c40f0b4182481d01141000c4100c0010b1300b001460000a80040c00004d80c003c01c1c0411340c07004180d20b880182c02040304104100c0f419841340169030b03004050801c10401080460001c18560f076036580070704039a0b440d01074141044c1100d903115002c03080182114058040701c00881d80325080d403210482c82c40c00034500c0070b0303070001322510900b8008540006000500b401521143c9040c0885844107403001c018046140407007904019003258101d0001c0c121003004112030a0100581307001c1032507150401041d4032003045d00b84204c10360940d8401104020000042c144d022402442e0001050005d03080403e4801c100f0300c4600b0200130820710955114250450029038810115000003c0d110000101c8100303c003c02c82c1000c14211040d0301d10310410340c0700c000f054a200d00401c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 769284604 1250 769283354 769283399
    0x13020d0c08060d081231050c152703070e061201140a0f11071b0f06050d0209030319050406090e01050603060f011e050d060902030f13030315 62
    0x1119981d2104100484600f1000105030b40c4050080703082240c240b0460306d030426841400c00180720b00300440002c1390313540d0010140d928400801150288001400320841d0b0ba4001d50f6542858001750016241d00d00c07038480c512101d140c01a5448402815805c4000d0140380002c6c00d03942d801c0d0350b51201d182c030390324107481d01486050500081d40c4842814447c8241200c050340e860705c199955810510018a40e1200040030a6120841100120722800060a51901ca1011805641d115183d00b542c1c0c0b10490f0044281e078031000304240311094102c000c0d160510318805000d80c3c0d80c0b40b61000b190860041d24401c00030161001944e40c1c841d600100a401078900a945605045964588101040e0400e214494010300d040000c2020760400d60300c5091802c0040c100201c0e8918490311450f400b41828000308002500410100141992400340100801c084070b0190b0450030320518210030380030007801c4803420012480c28403041502a401044046881c03000103034110381d603540c008016180c01843c502 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 769285854 1250 769284604 769284617
    0xb010206010519030308040f02040f1b140d020d06180b120109201914130b0f0103020304050a080301122f10020f070f082107080913020d0c 61
    0x350340c1446100400e200c07255800020700c0c50b00c4c607181912a06030207030040d24082400300020000d40c03201d000340407d4414500f40058011041d1480180d0545080c1c0303000200b2035500d980120303241940c001c0c1c4800d0b80e400301340141e03030300d443c0c641c024001c140360f03440002c0859100761107411754202035204440105081e1141d103503001140241600f02c60075131000600e0007000c440b41c0c0135070340012000181d8040c80540140b80000c400c0c442e403c031880d0280d212a042e0340c0e102201c48880e040c000c1d940c40f1244c1d0107410500c450148039001420031800303c00000e04056003c400201440710401c0f45981e402e800c1100143e036035856500c03014590b410568140c40070b8a01c0b0300701140c103184103a85030a01002c900e045c085844186410050241c0741181a0001c51050f02c041110000c01844080c00070b00011110381880e9240c051018145540150101c1d100d41c41c54100f00c2011110500311034a00d54400045176542c2c01d03c00014a03000100c2150b254514030104050319000319a5004142507421900ca01c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 769287104 1250 769285854 769285859
    0x10f0c090b0c06040816150608073503090a1221210b040c080a0f05060d03030c090b07030c021206220618080703090503010b0a140d14010b01020601 65
    0x1a0380d503200c0e0055980490f40704400080103c0e083d5000b8000240502078a50310103920f41d19010004850200e1309099150340384401c104100341040001d000344041c07110210117a02d02040251410510508403584c10103142105200250038401ca841e5241c1c000c0c05c0c0020030341c03119550f0000d00c0128004844d80c181220f14a00074065845980408060603a41c22600d8089600c2c6040b00c140b600c40509403c544403002c4440941d07980c05401407009440d40d81151078a0004074030b00943c0c59407402207030320900d070800344405622100e190180c00c0303405003400f090f6145000000c441c0c0440560020f10741090210326a000c0540c130041400341c1d14000c41e203055404084000c0180c940c00107a43e03190080c107a22250343c49184a102c40f44100602503540001d00040e050356556101d11000c50880340c4841c006526820513400542c1032024180a400801c403a20800c00030a146e408030340615210314112043c407030a81d5940c0700400c48003641c03041413400034110011582d070280001d01c0e4080c1c0540101c0c03001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 769288354 1250 769287104 769287119
    0x910090c140f0d110c010c020c0a0e06240f07120905011209050a050106030f0c090501050f06180d06060f0b030c03040807020604080303070c0303180b0f0c0903010f0c09 74
    0x1965005410304525242ca074400c45005507101a2810442c0d5450311a8101200e0001d40540413500080001240721211404000d0501c40701055841c4128070f508810b007c44000821001e5110a0548600700c507000003030aa4140d10010082c1e01c200400009510860410b20502070604548202c0801c8400308880c10103840180c0c3c5406114001200c0200c98119492160400e182041c010310071b0714215540b50310b8090a517543ca0700140d408010f01810303001084900542c3c0d0004210591041002c0d504202c0040c103c0700c682050301f0700c120340108a000c401c00d007459140a041200030148481c140041c500030700649094803c170000d01c0310ba0ba0002030b0060440085a105007034002040b441e50740c9990722207070240c01c40703c0c040c1c1c0c11410a01c4089201171081006600a580d00e0303c0300c00f4555200c2c64001c090764800146500071006100010300000c024091180c0c010528680c0d04031140d448046075041c034090004990b90660801d1810483e01c41280d000803c20003855441480c4a43c03103c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 769289604 1250 769288354 769288367
    0x260f0109030f350c0f041e0f0f050d11040c080a0e010b0922150b0a05060f122d090606030c0102030708030703021e0d060509070f08090703020910090c 66
    0x103142003203e90070036100900000f40000f16a116001e40141c604020340071915001a4020382c20003050035100b10f0380320312030b0455080290018140c0c0581007498600f050318010b08100248201da028108000f44035003044042541c500b19560040c0c82001280030b1284018052417058618218040c07820081020441060041c83d00c08840502107940e55164000c6000d41903035488400c2d88041e6480c03c215001400c00c0b941c0f07000310202c100021421554a40801c1044600303580154440c00c4200881c6550300301003000d9030f5401c0c4907020040e01641d2880c004804c150760b074625000d00e80c0000325080c40e0400c0d07141e88050148a40c1811151182c0d150f009140d41c904c4014401c40c0513034020300520300026000307001035901011525003d803d00c1c0c0780e840368549050100100441404000c2601c40c1003401c0c0d44220030003080112518805414681c40c0a4100c41205103440e00704056500061028401007003c2401140c1c0036040c04001e10b041e01c50601c00c0b844901030308010904010155009520544 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 769290854 1250 769289604 769289657
    0xf040b0a0c020a0f141203181501090b130f0f06051219030302041806030b0a1e09020402041d070912150c12110c011401260f0109030f 59
    0x30014801e60000340c0b2241030703100d50b982003203820002019010004a0f82801008140c1460b100001d0300c904155083c408c0c0c600328480080c105500c21a410030001882e0064941181c01c100000104842c1c40d4002c2840104211704103803100342012003400584545074000014240c140030200a0306440750701704490070025403042c0c441c1e9030214980c248d21003004040c1d001c2c518030906006103407d40c0e491144003107203f0700180d4154165500c0042043c41808441740303034001035809007008013030401c446402104440303000c002416503881401d00b045450f40d0f4100c0e80a81322030307003410082d0011000001c2005404685d030200181c81144001010108a880f40b01d1241d4000c41e442070500c00042400020715440700c501d01048100c2c488140d60110b075220306440c185080b990281d07594000c00340c0c58255074141100a000000510040042c00c06110606400700c100c05d801304410b070701c90702c8601e190a5052030092441e5181c03c1401080640040440c4010122500c54020280c048402010b442d10b001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 769292104 1250 769290854 769290857
    0x1a03061003050c040305070b03100602030310031209030507030f061401080303060f010e09090610050109080c0d06021b0c011704020603180f010f050a06050a0303021f060308030f040b0a0c 82
    0x5915032681034000e40141c1c0e449641c000b005070425035130b921014580704281e44904035610000003070000200039a0116005801c00380000c52031400d00c80d91640d4098018800504990140b00d207000019225031405030007160044101d42009480b0300f4608150710152070b044030120b10b007006c02a1483e0704100060b04950024000c1d40c11a41e0350303000d000c500a8482c4d42d460402c180d40408103495950044c0c0d10f4065010140180b005103000f21800540506540165040c001da4103402c02405d00005000c1c40500c5003a540650070280500e00f04000e40142c2c2294000c0518141c81601c05120006e04480d44081c240e813521800a1440102800b503002a00c019401071410800a181803001d0341c1e08000d06000d0f50100c0b030f5003c4400540d6400c56160600c0d10581940310b40920450040070301440c0e01820045400e00d003494a1960065174800101c1c6540440f03110024660b155003019071704c00350045401140541c0d41c2e2500c0009800d600b041150b0031a2030f080715402040c00c2400c3d42c4140381c1c10b400c49 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 769293354 1250 769292104 769292119
    0xb030a032001150b2106060405150405060406050a1205010e01173306151e040b040303080a0f060e0106110a0c03050f060703091a0705221a0306 63
    0x1500000403450030180601c280796481d0302898500400c000c01e014000c2181815454403044071001107001c024810380210320b0210080140440380d62030100316401c4400882c1c00000181d51400c0c8203040740903950100344e20020101d000144c0b103804c4002410950129a140c4141c80040c400d0a0211402801038907680c5800e01e0052140a0801c40042200a90407003110661802d0041c480740d0300902c81c52000c16500005420a00a11280602a00311404440406240201406000b00c500a4442c03051810f10b006040e1489100840102c901820320300c10a1035503140c0700d08011342024029541a0310320b034503200200700d20405038482c1c1030a489001e6407800c9540d10707001c000c8442400e010803580c1c0e05e0060700141e90008440c02100c0000718828409000148070301c1c10250300348035001b07228205041c1401d550364009a0540745d040d100f02585455804c5984500c035089443e4000c507860082440940a5540d00c05e8408005200443e1260f40c1c4040881750f0400c4100c2d224001a03410741c1d00840c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 769294604 1250 769293354 769293377
    0x509030912030904060b18030606090a2003040302070617060f040c020c06070507081c090e0c0c061503012f090f0310020702010f0305040302191b090e010b030a03 71
    0x80841072034240a2508007141c1c1030480101c009821501c50b40d001100c05203002072180a500c20004100c43c40c0d80080b4003801e05071a00310b0100da80340700000c101c0d82505030340d940001d9130300c0040042d4a80c2c00c000c09900c1038591410b45001ba41e42c103e1802071102041c0003c088410640301e45c02028814000900440c1016010001380005029980759400c2540190014000d0380d4403080054043c003801800148a02d81c5080c907894145017021a03890700890518000b891500e8110b00043c3c102c68040d5a0030382d19030354280c0c100e005806070200b00c1015001c1d290500444001c02c0c00d01d4038100004030b0080100da0840d000c40340b05000c0000340500140e030003000f000b035540240e4019004810000c1d003032280c01c0d02c0110000c6c1c01d0041c20f890403280940c0c04176060040d940d0001082d80c0421041c01c2c1000103050503103010390350320380700a6100c0400100e40b1a00c0b00f04004803182c412044010303007240f5401521201083d000d071541e00070000880d8a010028045890f00184108156802d0780740c0c0200d400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 769295854 1250 769294604 769294609
    0x103050a06050a0e120d11040b07080901030603020405090105060405011e140d0606060c0b010603110f0711030f0c01022b0c0503160308040b1b030c071109100303110105090309 77
    0x40001c10343c1140940d1451078500c056000d103d04410803013110303c2140c0c1d0345982800d8204603070b8070f4141e428000c10180030601030803a004048848543d0420102500c4400e52001200500002e42000f500542064244804440150013860003080215002e1005a80b140380d91400d001c81c2c1e170824600c480900704204480740484000c0c8030344043c0600000340c00403550300c64200f034032501d134030440c0020b40000340c0c41c0500c40c0c2c50304c003180903168034070f400e00220280d07603003642c454014024114040440003d100003000110840e5410b84000079040d5148480000a1a40c95020451180e80540682050058101c444088980004d07014003030000180e0b40a004c01c403848810f01200319203506c020010074240211442840c20300ca0300c03070f944070301c0a07240500e00440c0601010700040000001c80244407414051002980d82c0000030f40c00c1c80d0f4031600701d81003c0700b020100c08030311a007200ca0002800490b90201c459901078902a4640d991070411540b012402c0710012569200d0300c0d00203200f204903d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 769297104 1250 769295854 769295861
    0xf060904031e021203010803041a16031b0b010f06120902550803070f020f0a03020901030f020909030c0a030e28050f060901140310080703060c090e0103050a06 70
    0x38003240f04071410031a0082c02480c0c103500c00e800043c0300b9030000c02c08015040e1003000c070301040300132910550b0800129000004e80d000210b5001000d01c4040914a02c0d0078294401c0350f04040e0b000540328100e07580d507241403c0d103031080c0c0c0110b500044a80d03640c1c60100c150717400703030600c03141e40641308404c501a0003c09900100480100c880090780030181080f08038801c1c00001c3c00358401e4443d1741b03614000e0046040035816168440c1000d908203010820105050303101300100942c0507901c10707010740da02c000028882c0381c45410081d07003d00d500c40084140440d4102e004c41652080c3d990216a84612940b180c0d00d0051103c042c1d456031000440c01c1c00039114803221504000050800011110003132200300c3e2500d02300d22514020f00084008100c285460200e940c6500c5041c1c98080c500a0300c0c0e40000c110003444000101c60304030000106d1118020000c2e114018607262080c4ca501c0d42e1603250a4014240b016004000a10039080c0820348052400b0070034101c9030b1041c0200301d44034643d47e40310042d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 769298354 1250 769297104 769297157
    0x2030403030902182502100c020c1201050919080a030b010c23060a111b030f04060215010504140406050a06080f0f151623040308030f06090403 63
    0x30540c40e400c0d00c10041c1c0b2650303d030303079118a207540b4015a240b8101c61031000881030300c01003180d014115140c1c3d04041b41c000c5100c0703014030700c1813001061036080d003d400e900d4403040b0003142d1b41103a1060520460313400706500107409043d00505a80e244c1005004100c22030881480242001408000d80c2110500036030004202c10010b0628842c606260b4550304103c585241c030640315407108002c880e8003004240089035000520307600400100301e410301418818060015003007407103102c9500c0e0b4070716130008205440c0602188140141e0795a00d5050094941d01c50703a1140c040ca10199001203294500350182e20040c4045c1700c0740090558803501c891010305006044401c01a030344090105110707005010006125402400508143c50303524a15840c04c1402c1d140c0390403003100c170014803500801c0d100114600074414a04035074990f0724200c2000310000341c0c451200e882600010000104145000914400c55156100380402d588150500c6800a000c44000b0000b407401c2030707032842c00e03004448108007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 769299604 1250 769298354 769298357
    0x3040608090709050c042405031b04080115050a12031d0f12070501020f07050d0318080316021e01020a230102030103060e1606050d0c0516030c06050901180602030403 73
    0x403aa943c0c043c440c1140c0c1c050b120840c405070009000d100070481c006141e1004407125584a490800c0410002e1860001500071140300d000940340307207000c2031450250f0f4003411409000b000110611564000008990720982d0b0040d8088100019414400f24000000a825032100345c140b0f4140082c010303000440111680d40400144040e01060711404d181d80c0040300600010681103003044000781c907005007800d080038254428401844252503020020407540c0c4d050400c90203402541110700d07084010341d003105400d0300c408075003c0d240d54503800311803014034000e0712a070094610b016242d00f4544507007203900c0d0250b80301c010740c40c001543e45441d8511b491705003004038482800c074529081c207a0740207900a4510720340340d000b0b10581503c10301540c025408500090001076180c00c4000e410350041080c0d1014030b55440c3e88141c545070281c070440c1e13102c054595402049000a103000740a50708020019200e030391401d40019a0300f20144294202c004962010140799007a40d074840c2d0203540000c00480 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 769300854 1250 769299604 769299613
    0x40603050d08070801120f140c060a0c020108100621020c0a050115050a0f03150f0603240203010f140604080105040309150905061c11030106020304180e0304060809 72
    0x800c0041c059029449501d80d20910725007448040104088410303040000d01d00401034042002030411250700c800c2d69031041a45540c001c1c0d100308c10f400c26401001594021400050000c0c031640c1c06540384807400c0c400d8071440c5454641403401c0031407041e60301401001c0f826140501c0c40c80c1c1d44210b4581e080151500e00503140401000d012400c00300d0841c0c1c12215a91134113860148000181c00c2c50000c0d250695810101074900002e00e44100090b20016011064400d401051507103a5002560f620000030414892595285001c1c2d017501a5001c22058540025110100d004803034002c413030403100c2c03680014803007a0801e82e003c4260280b600d004e0b644160104000240c0e03030707000c0c0119441140651101417901d442e0108141005150909240410031015018402d540d92781c420b13201d07650705500d035600843da901c84107000100781d02e005142e000395010000083c0b03164000024401c1e03613092540c0260031a12101c42d90159500c690b41d4403501d030001d020034001d00f07200303104041d03010300104101d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 769302104 1250 769300854 769300859
    0x604030f0809101112010801090210080c04030506272e0f0e010501031b060503070c081c1a010206010e01090e190804050108090c131503080309060f060d050304140406 73
    0x810440341c80d92900380c1090710118140c01030f0703d8074040d8103005221001c0240427164040d40040e0740304030403400d200e0034130120b400030031201c204980a54000d1540502101c0141c10228204503050010684444401c0c02410400c45442c1c030100f82d0158001104203032103196401c002c1081d01d807000301c8001100c01650b42400c0038000c2440d020303c2072041c00d0900002019419428110481007e001402240f000c206100b000b41c1c5502170201c0350b000c1c0451500326005003151419000700e20170350741000c2050f111540b1815a0b0a9190f02038085243c151007100e030a102c40740010380c0c40341000d00c1201d640d10071710001041600c120b600f058107907401c2401580c03200c1144556149614108040c15030b0921b01c081421310265070030094294200401c0801000501160f0f80015000079600070344200e06612070101c015440c408400e03003400341d540241e8890316031900c8450941e07254401c032481e071641d6032000042003080c185031015010722504240510320b0306090a0400d0b04281c04040c0300c2c0d420a6858000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 769303354 1250 769302104 769302133
    0x10080d3f0b0d0b15010e0105040b03011a1b01050f0a150b1602090c03091501150e011803080c060a0902010206150f090703050907060503072109080f1b0604030f0809 72
    0x2202d2044c007078003006092400e5000001020400032600103818030070200001d0008031500010344e41111180f44665495440791020b001d40c038016011080288017041619002c2c007081034100504c14005400c560404da03a506c0202c800b0384250303940b90f0fa80000814028802c0040050090030000c01c1c404200c40000c030b0581c041200caa0044034203101203200401800340b106403d008080c500c0109420b2125554103020700189516076040c014424408003009141c51640281e15007800e50000c2024503200359036a04110042d9031020a401e0220f000d08000500040c1c41031051241a6406078000d0a5035554084142c400384481c4001c5540003200c2158181c4503500d40408521030003960b82d011407281829010189071000582090040c85418030400a40315848018a00c100094600652241407400901d40050100c02405031000200103010450704d505a0010309070441c2c0b40707201000300c66035a0100d80d21143d090f107009001500e888280071039030744a034400340d40014150090311306802c1c810b0032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 769304604 1250 769303354 769303373
    0x30305251e0203030f060904030c0611180301020406020a02150909161d090613140a0e0f0a081206041e0c0e011e030510080d3f0b0d 58
    0x110000000c41e404203004144829040c0030004850500041d0306500f401c0c0208170b020304000b000c0c54010481c0e08001018580318044001181303030090003c011402200103680e00c19802a82d2464900c2c04040e2506400d0405100300d500322461070340a0180203e0507420040c0800f80d0382e44039100802c0c2840412002d5941c440101d006903c0610340003000345038200060324071480301c410038115030400c003000d10554455010341d80e403042e001c0325091401e40000344a0b10050400007203018180b00204100041003eaa50018140c1402a000c41d80020110203400350b0307403501a400241605014040700d220403d0624489030002c100820100d94000038000c0c030f205800524507008042d40d104c0319804031458020f800510310010a10301003045504124400da04240304810200030156200000b62000120945d0707440503107144d03020399034081d4811000500d491000d40000d62810041d206803040f030904148140c0506501150300814080c107100000e009200d880c07450364006001500080001c0c54209 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 769305854 1250 769304604 769304671
    0xf0f040f080105190b090106050f0706110903060906070e15040e100e06040b010e210303070c0c05040501030201120c091205030309060708040f060e10291507030305 72
    0x10002407503140034144d14280c4003400c00320f05200352038080076950310344415400d58103581040c00c04036070320669104a94424440e40341c01400c0c0d107180508030807441110314000c01d0b00b003030b003202110300703a844490845841d100159050004100c8916440c1d160b410400c1d1800d01160482d580141444e0307642c5030300415104115425005600c8140c01480000b48500200da00302400365000c03c81c1019110001c1d00420000c41c0b0340d44219584503000c00121031103225466000010000d0700c1d2a42414a405404010720820803100b18460b464046000d0915220b001d0407290141c1d16014591881c1041400828003c41980c4c1000042c0341c010821090141100108520610042d0b5403441d090115a091940146c050020012a0000d0002040d00305004105960b00400001100229a22501c3c0742c041d4541034102e81d1801e2107041000c0350382d0743c200043c900d0b480c6160720401e07100c03c0082000f2100048900200705106011200c0400d10940c4a43d9001a5030021400c41607180c200d9288040c0811 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 769307104 1250 769305854 769305869
    0x1101020d0c0f022103030601020d09050109050402092b03020f241e0c1206090f1602010f1e0c0f12021803102306100e0d020414090c03070305030f0f040f 67
    0x82c081f06590400c81c94071810054504010150f05180000384407840b50b2040c58411500414480043d59544203906103001c41002900010750300c18081061441c041304081d4054029400f56a4030100081224001d00b07a0959086070517840031502ea40140501800c0d50318000b449800071550680301914841c0600404100d054403002c400c01e50448009004005500079400017061105c040e0a610440e6086005220050500d003c51001203004080e81282c1c40c1c511800e04050214000380300c0341c0344202c66032a003420f20040c1c1c45550140c0300204296810340009048030010100048154060041090740303100c40b44c50803620700c00103032a015201e24228034003030399001c85072520002d03529090100c2c045058148040d14040000071880e0300e018030b12506104401841109541c3c404081100250340241300308405040000450381d0305200700c1d040342062281c114040c01a1900007502c80450341e0103001545441d01559000d0780d941c10041003080c030f91200340000705e83d402d103069088026107200c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 769308354 1250 769307104 769307107
    0xc06050903010f0b0307030618050d1d03030a02060403050a02120f031806091009150e010b030f191e080a05030609060a050f040c09080312041101020d0c0f022103 71
    0x2039030030142142d409043c040c000502d004425203403900e02080600032686c0041000850070b074158600d9058010003400100300340107201700340038616001100e28181003c96010300386030000c0d42007030542c0d070300c580c444180150380154001b60029120740c00030403440e1540d1060319080d41c03003114040c503181c20504c0346134220342d801300c20040d00c8005690043c014003465002011141000d603001501c4000c00c2203001b24840e100c106c0c500500c0b0000705200301c0450401c0c0c04020b15140850000e00a091201d010391080c01541065800001c0000300d11507001d00101801050b07841071b50b1344c2c4d418005024a1184a20390f040c1e050302c04100104007800307c8140a07282d09550b441c2c040308114140b80000c0003a81700e860b41c9070717041c8513a494041da400305100d81a01c001a844159207001d46030104140d110105510000034441000c1c0c0071210320701d020b244903e441030300d40d00700c85c0010398071080700c5c0d0500400160031100240c0494401c5945c0000d060010f01451041e00c4141541c9034400940301d03030700000c0d600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 769309604 1250 769308354 769308367
    0x705060706050f060315010902030a0b060a0c030f0e1c05010b27070c0f06050a061a09180f06100315060906020c0301060b030a0c03140a060509090102030f01060503130c0605 76
    0x2c0b400c40c0c0d60300c500300305c0c080e0401441e5401c0515200d0018011200381d00e9002c000100307650740c1a8400404094000c0403992074a542800040410102d450704030001460310803210111801055620400c1030010310300d0b502e080d512034901504018a00081c0c805640701c9181071815280d103080521842002c482182e075080d0320140da01c010b840b01900b0700c1e08006000c68000085290071015807010f5610280126841c4c5408401002a004c150004401095044074100c4d80070429002003c0900d0282c0707048c803400d1080e10002c1c130b07095021104040da0558900000720107240218030068018040d04001611000c07403810400900455044030000c02c59440d400c0c48410340401c008891000c08400031701c0103038200780401155001c0a08004951170b01c400141400324060b4200c0300e03125804090b03000782440c1824482c0c02916040c41001d02895192000c81d00b5144107000312442426480c00801843e460810120754585c0001c1542003680315101c854000202c04a071410014106035407590344805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 769310854 1250 769309604 769309621
    0x60302070b070903050303070f020f0607030507020c0d020f01050c031b0601051509010905040506150d02040e160c021003020d150509070e03060636240918070506070605 74
    0x304080d155905000c0494820000117100100300ca920103500d00d800c2e03200c1c61800100ba807034070865404848460055004019590ba45a0b00561044c0b005900700e516070b0003081c003844205650700c000a07400005d1a6141c84007035006400609000549200701d9140600010035928602ca095401005a80000d80104101e25260142d0200c06040e164064a0450840000780840c0b100d07202da40e0040b515480040c0d01e80d640c00018030fa119070002c480c281c0d2401c0c02c4001c81c00940c0680100120b40c0904070205a8904220444108811712034855154a090a408110207042da0740f011500b015000c0107414140f0459005080112810494141c4198180800c0040c0d00000511070004c2207941120f690850340c00081c00c0c1d40003031003952080e1980c0c3c04801c0c52203000200000104000c3c00081542e1850010f148825114403211449006507403036000e1000c520440200c045c03130b404050040440c1d81c120001c01e070009810f24190842c0c1005a5038800301c5c1a9400c40c80301511001e84c1c90301042002c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 769312104 1250 769310854 769310873
    0x41a090d0c030506061e0f010509030f030403173408070f020406090b030c010305180105100305064516030611030103030813060b04091515150f0903080406030207 71
    0x5104481c0e40c245108241d010400d100101b002591050303025844166445c0d0089040b6036004074044c0944d0030089102008980e03035030043c40201e900a003810480c030b04c0c1c0003240c42650340f4070324a60340300b00303000301001190442200d91090040030140b18a007070744000344500c4004c1548a108e08200d9500c1580c81c01040f04490749a0701000e000741c14000e0380101507602098070311348140e00b400c00040700c0c0c64120f503d240c080500010f0044540c81c200c2400b01500101213120110b038415422120190368903039108580e40c01b00c400c0c410701350389400b01900a451030228800e407421201c40184100c1040003031110b117800c171501801d0038440c01c0d9410502c14402c260007034800035111085041c3c0b0319451a5002810000010040c00504080781c03550000c0201f1a00052805040248240301e546110f040080f00e00e030314400e5100c0030078500107a998442c14111204411250350b156102510070200c50107690400510300c8000030000b0302c0ad00071002420040151000d0503c9940040c0c94004900c0c1c0800807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 769313354 1250 769312104 769312111
    0x1106090609032b0e06160512160c0b010f050a05010207030803070c1a160f08070815010201020d0f0914060919060609050711100c05041a090d0c030506 66
    0x240d000001000204400001125100c003070700070200c0d46003050070701d064040f5405400481410744c2402d041c0d03052843c1c001006030082e000c42c0c5001d001c00220b030320250781c1403203580710302108a1001c100055001c2034240c04c9a0386134102d0b0a0143d552205980c4030071940900b42c0104580e01c190410a1000c0c1c1070840c07860707020b00001c0c001004068115200e01625000c001c01072070421a940301100104050341e204002011782d10216a41c550408680c070f240d4a0a02e0b0440c01e00040d03d048040038294881d82050340110502d80b201070701502c5608914444460a50030386066640030020815600780c035102d144004440004001150329007468000113080207109131080c640e001c6001d020901c1404102c0060301c2d80344080850190900713103450303005020300d584040d0443e4900030802600680080e81070040f2546d200650310341e01d0400d1204d01c2201d00c207c904100040b01031200780403900c0c80e40d0040c401216480b051600341181c10000500b032581944d01106c2c5a400300302c04204002c0c041020507003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 769314604 1250 769313354 769313371
    0x90a0c020115050d080a05091203040504051b030a270b0f0a09051b031203160909020a050f030a0f06240f140a030923071706040f0c12031106 62
    0x40b075281c503000901800100b00d018210f10303000101509403c0c0114100d17101c1c00e1010702490381b84055490503986a820610559004508100008600710041c00701811000341c2c0b80d0b1010b040da00c9004d0b0150003041507442e180940b15500852840d60184000c1d07034001e05114004003d80d03494048181c2d45030150140a041200b0304080074003001550101e07041424802c800d58482c55651141c0c00a4a80380304190a0110458004140203040c030008240311039150760340d215102c5842c3e41d0802d0404a204a040403800600c0600c1000b03000300c80100210707001503184138082001c000b07102000b402c48109a008e54582429901e6851603000c42c1c20801c0e000f000303d400d0906041a4801d005060744081e80c8030b000c1c203184005100c07000c15019034005055075070490b00d04154a810024800c8400d1304480c5400214400c940d00011404148451414589440d0001e02a903031982c2d500e10314038150032039003103940c5003240c41301191501103400b00307414841c02640c886110721443c40c421810008007401080c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 769315854 1250 769314604 769314641
    0x303020f0c06071403071a06010e1504050d0309030b070e030d0e0d0b0612070f08010608030c030d09050f01020a0e0f100f050a0e0a03140705010207030c0b030c09090a0c0201 76
    0x401c035680311010b031034080c3d400c9148a91902c400e80612401d40c80351500040006103100d6141000743e040940c0c040c400e000a8030f4034803031085030f10104008800000003400424000304420301c1f03641800c0443e21542d41c800e0420450280d00d80c2d8860600351000c0301c0c0480060141d504050341cae40350070084c1d000420740a00b402c290701c1000f40042003442a0240300501200002c801103102c070b4544c1a00301c41403808503020b440340781d503c5020810040545100351906076007006000f145402c40030040701d443e0f24007070f00218504404101c80c41c02900301202c003a03d01d801141d00f40e0002c204280004c01e8820714a54811b411040c51000f04101154054011405241a01c9081001035005602c0f90680724440c28906e4480a01540c2200e0b05c0c41111403043e0084d240050001c1045401c80483d0f15648001c81030341c0300142c40d40700499440c100703848080c1010b5640001080f0044103617009581000e80c000d01c2502c4c103131000c0c0c042030362000c0568034a04007607a00d03440c401c0703400c0d42032040000604551030a00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 769317104 1250 769315854 769315873
    0x1b050a08032a0a0f110303040506090d0908030306130905100b0112050103050615040612050304150f1b08090402070305031b1908090a140607080903030408040b0c010618060303020f 79
    0x1900c0f80242101003040c8003112021071840c40c06115000c948461650450360380e07161611707000e07488403000c1e41d40003c039200d08510300a06502490300b40c01a111480011411340d61950100400705c2c280c940d100c42415903410803140031400600c01c483c02000000804241001e1040c001040f0f03a4a104040d0f640510f000d00600004001098030740d00400100c0c4041404400c0c2d00020f4001c01080e8886001e503042080240b08020012000d0f204942c1070f9031010600d0300344440240d0b19045180300041c0040c052405070418501d0400650500501403a1941d041180c0c401c0407070308a0f448590254042000032081004120300d9189029072680e6940d40c580c1000c4800d0400c003000120059408140201030300021484041084204000b640040102106940056a454440300305a650a0010b80e60a001610101c4000122401194440d40080c9441c0ca40070110003c2e40181415424554958200140500c40306035a1241c00400d4440022218650700c1c010741351202003080035110b80c0080000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 769318354 1250 769317104 769317181
    0x301090812331305010609060219020f120a081810090b030a020913050a1d0c0a05041a0d0606080d0c0c090e07080a03030c0f1b031b050a0803 62
    0x20030410300c8062160300315000c400c0001c3c0e800501154a02c202880d2900004416a0000f85442168402e80036600145200000d10b480005110000703500a03d010400c649141020203049021094103c10b690080070141d84038840d40d030040850030704004071041c2c46041071500500d44944004141003000e2482e140800a01c00c1d400001c0c400c0080795404a40e04070f894a846019800b1000c500000700007a107851030078100204018541281401151407080003da0701c00112540075020040520740302c240707441b0800c000381c51042801000550701c03444138540398444125101645101e690702180c1d0394104504145172403070301c01a6030100080d040e401000314414020440503510198000305900300030fa02c0251a00074907034840003143c03040450710006c3c036606510114003640150398010856901603401c6801e0960322800300f00350680090100d002a004503804281009402e0f050307120404c00ea103d040c200010020103a5020ba400010080d040800011a4004501c01c2d07451201d50a54000c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 769319604 1250 769318354 769318411
    0x1050c06061002150a0204031718040504060204120311010c02030909160309021915030209030d0806032d06010603020a0914013b060c030717090301090812 68
    0x8014001c0c00d1015001110610038440444a40701d000013600450400c60074402c02503100d8172040e04c5102c044500740484c0c40c09001101c0352030821009034803110800d00104401484050422903c00354200070000300510102085d1441c10300a494003114029800b001e18207441e0000d11001c11034004100b07641103640c078800b400f50411103c0185444000c5c2c04102640201b00e9204082e520078801d0641e003a03f908400154401e59008400d411203454015000303034280e0054054180c0e258100701c07140c0c221244180700e41580803900401b03c80f204035a0301500740c4021142d061f60a032400140c1c0b0001441ca0b02000a9401400c980c5011450b002c0c0701440108031018601560390028000c1c0c005c511142e10500101002000d441206071012102c0200c01d500c40c0c1400c0c10940214000301c0145080d4a0301c0c2c0c0c10703614407081c010065480c1429640d9580b40800d500042c1c0c00c00070600340000d8869880910a54184500c0740000c15034414080b00000c83d915001044595800a1003110032402e807110107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 769320854 1250 769319604 769319611
    0x901060510050706060306060e04060612110f0f06040801020a08130308010e04060b0301020a120e34030803040c0501180b040902030703020c010c08011d01120b090a08031302010e01050c06 82
    0x3500700e8480065181000150045601c081c2c0902d05050010400107800c0c9c2500303008070b124407030400005907078281e8213100e01986503004d80008608840305101e0f01304418005045031004041c402e100c20351000043c0b45030000d40101105a40c045641800c43d0313000910550003c0c9200d4002100751a1a50300800000c0c1c14003803042e041601001080c10881e050700500740301c40c0c0003402075494086400005180d00c02501c001416203042075059940c1c00c0700400c88030814035103908044004e03051801c84d2400c411017190440c143c034030011400004901444080c1d03005a104e00060440141b4010004241174000b41c0a080888551241004031503024400c03201129409031003d03880750740345182078000340600450941594281044502a1540040040d050700c641c001040b8825843c126200d007080e40902600241c0c00b070684200e00443d00905440380d0205a0301d00301c4280320b069540d03840281c0c00030782d002440b030070b2111403220441d07030850702c11100d4240a1038294107152080700d24035a01c00e40507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 769322104 1250 769320854 769320857
    0x40602030a0e0604150c11070e040b011706070e030f100b03010608190b07032403030216180209190909060506090408070605090c0a0b0d1805030d111b0a05060901060510 74
    0x80f0f02c03941d403050085000c00c10410308002230320501580e6140e6000c030490115070864200c000c0740000318007042041d80508a0580b0200200040e40d900382040c1d40c5d0400c20780c0d8a95040c42004505d45e44914100031b0940d00c0d442c440004601341158005050a450041d0032281e1b164200d00c0d00154a46030b520710071480311307812040d8100503880e00c107010b81c01404078043c8110007241c0d403090022100401581581140e200e0740c00c0354484101000c806100c03541c0f50060450318004511341840100d2990042c04040c180100488074038003101c08542c007100242e511013140b25490f42009170500001e1321419910440a49401c14a4507055030351414038851201c0040c413040d40c50f000305400701c10030454106007030700c00b4107440503003034843e00ca5030704641280f140354960724202925044201684800940c4e0140d20074001e605028940740e2045c043c2680600d11f15400c00244600125051200f4a217100b4490301c9011700140c49590030020b081c940d00524030401a8180941007010f078550a10074000b480c0207 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 769323354 1250 769322104 769322111
    0x3a090204060f0e040c1520100c09090614090a051e1e0c0c0d050a05090607060e010b0406050604141207091d0607090b0f0c06040602030a0e060415 64
    0x6200080040c01c09030000059000d110001040e4050040d9941c2e004901071800c810301c00d9a54441d281005081608040000daa12604400f620b1481054807860307a000c0405c1d02d040301c02080780001114009400c850000d900480100034014091007102d01030503c086915645e03031a00004104c460401034180140c0d10f5568000805003021003600b2074800407404d03135502035401c00300c45a140380c041c1c0d0b007001d42c01503403c072020603007000042085903502071155000d400c0503001550152281d4000c00310303200a2060401074214180e03154002068030320310034500021341c48041da40b00da0848022110240c0514a049410701865451100f82d03000c80340e441c00c0074014914000d000ca07680c2000b8040852652064107408a005806608804445d414541200d01c8200c40701588658440064441da8086002002c00380820f88205d4010200508600325803803070300380d850384034501d002c90849050710880e41c00700034444005101d0040b07072103108030380000740101d0074103485000c031159020407061300300303541c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 769324604 1250 769323354 769323371
    0x1706061201150e0603161a0705070f0f092405040e030f21070c08160f080721090506030604020714070801060501120c210608030f3a 58
    0xc00d40009030405904542124026070310220940421410340f05103100e03028440c00c8148503088100b580084504e02c11114241014119640704240e0205400381e4490054150202e0059184001c00c40100340010046010600e4003c5c040d04884e24160460810380c00201c0301c203412070b418a00503040e54400ca5002420040301c851141c51171040c2034030422441000700e0300705160000201c1c0700c0e018070f081c0304401900d90307207060f811140e56150310230041c1140d600380700500c55030311100400280180f18401403200078800e42c90746d07492030308018401c842848212000c1140c08040b0b030503c25000f259030903e4a01541004000f03031450000a0940c0d00031680400e10b0800d00141c4c60580501186a60903540c4042d150200740380a001c2901449010614480351400300000900c9460380102c442d0f07a441d41c001b07500f140904503582150307803d660301036141c40340818440030900080c040301d601e46240139510b0408101404008011654482d10100320204015060024298088103018640c200003041070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 769325854 1250 769324604 769324639
    0xf0e030a0809011506030207051203040c0b031b0f09010905030c0102120904180813050d020d020d02010e03030a18080715140408060f060405060d110621160801170606 73
    0xc8415407642684c507603030f100003600300c1d0550b0040029074001c03403d8480ca055468450b1803d44401d407002400030792000c804008100050000d036030410f01551400d50f480d640711480d019681c000345c8500200080003c0c021169681143c2d03c00020002580034005522072200041e40310580175038145001040003070040f001c3e0783e55500426940300d040c28035280760076207401d02c003030290806002e01100c051a41d0000c2040d1900884114083d64020141c02190381154244000c00c0060702c2d00301d0600144180008445e54140301034903030310302c2c5039880100303045000c0c0d00401c0c64079035644080303810b0300300c07960500c0718040c402c10014100e503c3d820200089803580c0111442441141d205115038002e22040c420081c81c508042030140804550503c11074984c98200045505e030b00c040100803000401e842c802504040d0041c1c00d021100303000020700001d40c000e0b00541c0010403640ca0801c002140480000b0030b40114409003d03003100c2e1130702140700088411060b66000043c003814030450031032500210700d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 769327104 1250 769325854 769325861
    0xd0c0e0607050d020d050412060e100504060519090f031827050a0c0801060e04060801020d0e01050c190e0a0b0c0d0f110604110406080307150f0e030a080901 69
    0x660054942a41c510301c40c1007080e200c150030342c4001c0040c0079804480340300c1c43c42102506c05442011a21000d40e1000e5030f1100010042840c40407011701a02c03405201081e640d01c240342c0f24034002c0348086528500503082e4410f030004000200201c500e401240c4011800c15110200007582c07508007009615071a102521002c400e5034082c000f403c00345a9003c0c1d06161042c05084001c0700324030140100e465810394042500e59080c96040065444070041103554850032a0321464400a400080c140792146a038500307a038000d518010f4100c1e02c81440400e850800d10469500c20120303c52582403100068101c01c01240c88000300c4200240303505105200e60714000d551000b44100da01c029a5078005e1400d45884030624904a004610044030b480c1d4000c0c0a85043c0c01c0f00114000030708615030f030390307034170840c245009120317194220395940c4000c2903041c0100001c1254a00400a10070f81c00c10103003482d41550f80404170b80301800d050007148411000000196507544801d41082c004503903401400d035006 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 769328354 1250 769327104 769327127
    0x204030f0807110919110408030a1202040f090605031504120c170d05150a182307020303181203040f02030a050d0e04060e070206060d0807080f0408010e010e030d0c 72
    0x701340050103100c09203034071900c0703003811440b240418010b6020003140011240034901ca45043ca03002003241d81403142c4607100c1e070400309280090043c00c2c241c99982900031440c481d0001203800b542e60505008602e010480119414a020302031030305460160b5880800c2c1d55294001c105100e411180042004005e014940c00d4211410f170300b40d01c0e6140d5000c02000f500701501c2c40c048400d0119007038034203818002c0618003901e01e99036000e251040444a1480100342810340d04c04100248000000e1008410b8a03980c015440c5a005544030f080084201100e04a07241020341ca40d844035500420744142c16060300d9100d90002d010101810071070002c00d04001ea5044010854018980450515a0441c021048541003a0b808100c1551210303240110b440042d682240542c2c4200d0016001d480d03c3c500e4084a14400c01080c2d0a0200c240e817400c04c2504003281001c0142000b0806004001091160103188070028000780401003030a40c0040c0c907480358a48074504291240c010b03601c01405110584030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 769329604 1250 769328354 769328359
    0x70c061a1f0207030f06060e07022d210c0601120c150513090c0e03150115050f0d0b01030e031c0515130f05010f030b0f070912050d020609010204030f080711 69
    0xb1105c1151401c0b00050180e40a044960b111040100d101944005074604800da26054024003110721400d144a0f0601c001203001c0c030030700c50751800c146510010448000d4000048255580b01c00c683c17143c840c18074030142c101c181003902d20940030000c25000560101100c010005030303003182c19540f40440b040c1c4030f07820540c290304044107800200b0010990040b014100710b5560b10f0030195080f0201364580b00180b41f13210005139010010b2018440c0d800d00d118148000d401c0140c5002001c05403000e15401050800c405140d45280c001180d503010700030040d440700b00d48061481d1140c21107a504800c08044d03c5014455690340000c1d42c010107900c03602d40c110340003c000c05a450800940311000d04174903042150f4503802c01000044101840c5003040590313900000c5a00079a40350140d204c540d40e4001c014104000c04007000250901207151035449440c0524040d10030381186000103884c081001c1c00c2a0344c2a8410481013010918010028940583c820502c81e52084541412040310850000300c66 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 769330854 1250 769329604 769329623
    0x6081308090d053f0f0a021c08040b060904051e03040503030d0225050304150c0c2c1911120c13060c0206121806070c061a1f020703 58
    0x3a010f0644902402602c440107032220184036124011103002544c100840741640401d00c00103107110640b0000d0321065500384115082c045c1d205070042305a86e114100710000c02c101318240814014018042c0d641301d08141c0d405002c42c207282d558903503602200710f01d044a003041c64007547d16500c000d0040350000c100c01030489403a5060b000d0502c000354401d00c0c0f20042e100c0c120150a0800d41000030a040c800d8105c03001c0c5040600c2d166142d90010000204241000031000c400c0c0001100d0b0b8a9803805042520f59250049614802c048140703c0c4c081d80700120102e10070100a04000310054906000141c24004200c02494103407401d05805103003624110051107104102c12000302c4e00113400090000c0318020865503445c00d0581c1d10305a0400040e400c04010001190341004d402101303900a184a00099904a45135100a00f010004d503032800020f0b07a01014002417014a0240e24120707021a0444040728802c40006181010002c1c001400d0141c10482080c66900030302c15000196000344506c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 769332104 1250 769330854 769330873
    0x120207080f0718090b0f130804030602040e060f031f021306080402030d090509130f141029040903020f03040f05010311030f0c09030724030606081308090d05 69
    0x307a1102e40a02030300300c2c0200440c0d40220304801c0c80c000c1d6020190440108240c2d52144403c50401201c024900e020805036210321a0010301d54400500046001d2070380140c85500f042d400019088002e00014800c44100508000320342c0c0104000c40100006c0400c1d0183c858183d50035400b074007402d401491a440038500001f034403a044804584654400c9042d81d0191007910340550301c0715034038001c0a420003444400200078018003c0c0e0810303400c2c0920f24206180c81da030307502c40c28a40100d2403050820703001305840030074420762030240c8190f040c90101d00038000c140004000b98000134040c0840c0c030450701d45000a0515000348182c1403001170400960343c2d2561116849038688025100f41400240340255941c6142d0141c1d003943c1c01030b075400d00c9a0341162121030203002c00741c0210000301d0307050103200c00002e0310fa9a0883d1152031212000e05000c0c20700460030002d0103d03403007031380300ca07003031005a90070007140c6003001302e11640e204c1d403004140c1d490b24071103008246030302c082210080052107584c405 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 769333354 1250 769332104 769332133
    0xd200304121403030124170405010902040605041806020307051306050304050d0921080c160819122601030501020c0c061305060c030702041e1803050712020708 70
    0x400d0850094031842d400c0c002c50342c00680d90f4842440790504107440002914400c4526148030940b1208501d0714090405884003042100007098900311410ba540c0c0710740c0f50850074035018902c002c10046a0401c010500c000c070444c00d118058400601c1d040d400400a03141a00801c15202011400318002c01c81c00e8407404040c02c84c1e40240d40030385007131050751480f00136548109014003d40301000e41e41120b0010001e07800760744040030300c3e08541e07c420610104000082c200160014050401c03c9070180e9840c10700b1007400d00d0402002c03c1d449213442c0e2101008200b00c03010708110350b40b8a140c640804100c40840d626004103c2c07400d03004c204844d10000080c42015006081482c11b5075040d02c0c1c1500c20b000c1080614414107400306414074a49108101d40c1c54544041c00307200d07d03060181ca05d07048440d800070342201d441d02070021050074041d801c2c0101d4030701340c4a0040102107441003406140e001780c0380584103009141c4002c210b94121700b408120503100748916002000c10b90304079044811581c51 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 769334604 1250 769333354 769333379
    0x307030c17121905060a05060702131a0a0e060a050112060504060605030402010f02011b12060504020d02040609091116030309060e061f03080304030e0a1208130b0c0d200304 76
    0x1a08031510f10386550001e0041d071240305580c0910b0780109810002890300e001d01c8416001703510300703a91000e1849001c2043d00e40c03074010320500591090b000d0a4284407035042060801040e0000d005503032505003003014035240c8241d0082500c0c0e09082084200b00800110b2015002d06d0300090341140c1401c1c2c1c0028059000000381d40103d00c00d880c3c0600c1f005841034124226240070f1844d4015418041c6070040395070040d1074810303402211076070100d481c03502c03100443c091f603000130200c80508c0e41c005070401802e64401c0c0b69102901e05000c0c140030006030041e1004c1c072b5000f8544a04281e1601010480801d40640e0005001c0b6070701001c14040d914907a50016201d140850310501c004848012128103a02d05250505c2a2640b240d840d50854441e51000c950104486001c2c581000000d240410350b0010800220705691081482c10754031005a44105070003001030f03110740740c00c1e0002c1c400303034070200c8020a2581305036030341d450101d04010340e040301644204004801c5140c50b000005011801425a04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 769335854 1250 769334604 769334611
    0x3120109053c01080f0705040b060c060103050a050d080f150a151d0a08030f090406120b10050a03020102100e19080c0d050c0a0308100317120c0405030307030c1712 72
    0x8482c9503560b0740c4100d026214141c2c034194202c140c20001d018007152070542d1080c0c5610b1300181c0124100000d641e2002e103040000c1e001903480b0b46c042a00704040010130440a20004100d00d410078007410448600c03820180080e191071030000e0341c900700300403549460f9060b07001051440b4240d03141e0740d440c180280c0051039aa80c15026200040018a038608100c2c503140d0485164000a51500f581d400c985022504161101c0b5841030b160348001a0714040d186840c0e101c1c40c01604101641d0520080c0e21015904550280e8011a5000402c201503a0041707040300c0c0e00701070500081000c3d03001e911154103200b42207a0300002d15020404a50034042020080c02d86441400b0466602d280700340340682c2d0501400140c144203074402040000003a110301d01841e045480040412042a100daa5484a00781c410480749000c46020410b801c0032144203074003542100c4503540640c58242420f0200c6d03100d2191a2003c1c060010001508040111b4100d180c5001024416415117a21700c03080b00e01c0e82804280d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 769337104 1250 769335854 769335961
    0x2c1c05070309063b010e06090307030f080f040314060901051e1b0408280816080904020d05060102011404170a0509060a0203071b05220207060c0807020f0312010905 72
    0x401e90201b090500390704540074440020010300c035440c596500c0852035803481c8012160518140a90461206900c02400203184a20251501c9000c030301710712842d040c8000c2020190741c0c10035040c0b10340c202c0038184a001c104280141c07200306036202c91a102c400410710100080c280000100090460004a11b0600c1f080c8910000d41480303600b000120302e601d0b8401e002800d01c400030441d4410b0010489680c8800718817801289007815240750018041b07801c00103010035036a031200208880e80da07080c031840d244182d001086907031504003904c48030840900c001a040840c1c9000912550460082c0c2c10744894590003058aa40c031b07000f01c0002900c0341c201900031502c1c03807455404040490700090400b010303204003034002080445908411882d10701940c290b459501d608021403004a1100d006a80d481741150315514541e0410410007072070319956560380343c0c05070001e0140307004021401c081281100c0d003100001c5043d842d80c0007400c00d68160420b03201c615440c08020000d20014046009d890780c0e20340b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 769338354 1250 769337104 769337117
    0x209061e13090b060921010c0e1201021206190e0c04061112120406090605090f0c0d03050304020415080604120906050a02060a2c1c05070309063b01 65
    0x842240c0015500c0c02d100f0554443c805015005203400c0445e18501e1041507040031101c808a100f0b00f1a0842e0701c814800d000050044001407240e090a48120804080d5007000f14505105900604030424024000e184030700411407011140f85000211440541128030744141c45081541e0b40410302c0c0e1051103180003044615a2884040c840803a415074610040500d0510381140080e6101e0001001482261141d40e41c0126030049102481900c1c0300d0806000101508600c55030018504800b110403a03109000c0b60101a00103640501070f640c02541c15076020070f8196009011100d903c0841c3c01220b9240308000c20401031104201c0e144490102c0790300e4a1040b01d0300e401d4200c0d0070b03100e44c0303088001680c0000c0204903403100550011450180382a42c02c081050320300e240001025110740d010001d03900210754a00d524140903403140308060681086481c00c49556005007409041d0300c42c00c8144190481540390180c0007840d00301c5101813006140341c80c41e04410a29102214400a5030b000852 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 769339604 1250 769338354 769338359
    0x20a0c050c03070e0a020d1d01090203010b0415030f050307390308030133090e0a09050616120203281103130507031221050412030209061e13 62
    0x40102d1143e0680c1e0340c0e1000d480d2143e581c074410002962282c0c0710042016540d980908904810164141440e1404000030840ba121801010300b540d13a0850241d10492900e04000b03101c0b00c6026078907003140c6e0302a080314601801c42c10401d0550180010280807400c10189440c03491866a040145d694190bc901240d5000740b03d4020f0107241c1280070040c0301c01c1c41000144040c181542d400244844911803c021600350242c050005c10b0070b4a041e40b0124901c00424000e42c00c9104d0104d0b4010103245040007502d5240e101c01d13a942c00f01500c94280c890032004030240b10b511030814205003500c142410f40d500e040684e502d0b070300303550140c4241056500000c8150800300b41401040c0b210401c8000090840c0c9902807100c0c1c1c0120000c2048030399101702000000019113400c6840180c4a00391141100b50240c400200c820302c02061b911a0801d00d000c080000081c0c99a5604480b000940380040e198031510f0049140752080c080203094070800d1f508231480b0401c80c640100740c9600a4141b0785030300340d03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 769340854 1250 769339604 769339609
    0x1528180504050d0e1c02030c12010e07090b060a03020f0403060510030b0106050c060106200a14010b0d0c060813080d0e1015050d05120406030501080705090411040e10020a0c050c 78
    0x184c03001d050743e01032600c05405071300680b07140444011500041c150389101c890780000031060b800d0f5081c03608559460b001400000c20007480510000c208064050012001050009500d03103d4000044241580890740c001c2d1008904151800f85070301107020040742c188420080c00714895131004440c080400800481d401b881142640d2209403040021302d000d900300b040a5442e01d615107608032100c5004848886407590030403640a031640200790400c00054042d120b6425600ca4039042d6000e000c038103c0010004000a8041088444a14000b8025118030780000c03e201d910302006018800003061841c0d210110340d1003017540120080440d440074002408440540385d130606160442c0201c10401c1042c1e080c0351445504a503c98407d46442d910b89000811403600725400010000c1e42e508010301101008221000207440100c6805195162540e60302031003240c1c0280017401140c42e130340e201e001c1c4101006000b104001c0140c040d074440c200984014a81d01c03840070180d896211f0015040041d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 769342104 1250 769340854 769340867
    0x7030b0f04050403020118060501210c0b130306091b06091805041e03110c0103090b060103090c03051c0e040c02033001030b010501081528180504050d 66
    0x8000035100d54000458401080000c040c02001034096549441c0030501c200360540d100c5110510030300b40050a541041150300126a030f042000450038003a052400106040400581c1100c4d6506685641d480a0040d074800400131b541c0f00804160501e80c5c034108100d80d0f030486a0050704a4495403601540c0d0380d41c11500c0040b5885168030301e5480e150011403078400da400c5941c0c031900660350200c5061284c42c2010b00b0110091065002451030210a0b49a000c00e000510038008240ba040c4030000c1c0b1350310348505030400a0803003418151f80f410f0000801c00c0d1140c07070384000c0d038010b030070784100484410104c40000d5240840c00d002809a00e48202285821301c5100d00340c054542c0210b00b012284581d81480400569138800195100b0b4403001c149175000302000e01035407003038880082d554074001c000b40604001500c11080700e40e17040781a90268450390410111201201e001d200040c6003a0340a490140c01500149441802407501803801c1c02660000c60080e4450070407180540010300381200c12 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 769343354 1250 769342104 769342121
    0xa261c08070314070f11031317250e04050a051203010503010608190209071b081c02160b060604091104050f0a08060403030b040e03030403030c090501030e070e1b0c070801050703 78
    0x829040e2032040340d483d00c100e00d81c81d001e49171202220b1418503c0e90100203854941e0b4094016444500c01c5480250070521002c1081d40b48003142b105c02d1200c0408844035055a130240d5107003483c02c1000101409010004040c1c40394118003621550984a043c4220b036500074020507029608001000441400010701444a406000342c51030500b10990300708281c29001410600030070103c03996114940d0210b000610742c0030321030441d560303813140d031484106251380810b207035401500d1040c00041e103103900101c62420310359841910081a691940c000800e10700807038008028561503c206030340d00c071404000410036074800b01c2e14060006141400c10280c0e03485402428080e401000100b40002c1c001e8019240c2250000c01c0452000c05280c0b10b945503401c202d80070b600080e2200c1119440d00e801c403003100c0190500f031909001c0f0b20385586100c1c4d682c1c1510f1041207250448600010b451044c401101c1880b20820425565256548402039645500900920005529000100c2e07034003402889800703076 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 769344604 1250 769343354 769343357
    0xd0510090e07050d11010c1401020301031214090d02061c090c05030105010807060516020603041a220803041a040b04030f0e0f06070f0204021b07050a261c0807031407 73
    0xc125480b551703400b4064a03a084c926060250705440e00001581e008003000503220210b000503240d40c5981003541108001c800e84009100d017a0503003000b10b0441d501140d800607425a07603480354034072b10b1020821510581800d4210f0048418a2071150107458200f240d00500031aa1107622036112003c060880e1001e201e078410551000b80b00300100b43c041c0020300032b41408035071010b05400c2513802164850f807040f501250b00803242002056128a00301250b0307001a10036400c100390354a02803030720861080499010b44680d001000180410815203904203101040320007030303001403c2030325090a514006503004c501103580c08410315580d5108888011902c000100901255003506060010661100c10b060b5071000311010848056290f80c0010890700c0888100e6a150004502d5154207080c05031b008a485000001c804000c1040c02c0001c00c81da02d91640200100c9000d02c61010780b03811592941d821402c03100134641a49039030080403492080308540c9007031100180d0802c1650349844119030910 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 769345854 1250 769344604 769344619
    0x1090518180c030d0327170f040506040b030610020a0b01050906030114072102090306040204180506041209050420030a0e06391606020d0510090e0705 66
    0x106a00c0c2030603a04010100c080099501c14203030540030034208021a10741d94003103a1144000101c075426105190484560710b03c1e450492421030b035541c91f10200001300907108590205185041c241120112402880010940d6950325076914018603036410884809209900b48001e5071141e030f001103000002c95a1202c00414107a0900f01000040900600150f4040d941c2d2414450084007840312a8014851501ea402c18101c0510341e4002000d20b88a0106c00540188042006501c1c00038085070401d604842c0810081c004004030081e00b4983c540291682c42608244014031140c1e40940815036040c0d42d40040494035a018007007590900181b8540707110f8400164400c030100030707028607007210a442d00440e040070740c4134003240740040580c1e84821801150400014580c80704258502c40c4c0c403071000202101c1c2d01c4007103000c21401400d81c184022010090407000b04012581210b01c4070b81800300400450414a2060b158407000380a21700b545481d1910100c2c00311000540201242d00041c4a10f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 769347104 1250 769345854 769345861
    0x50d050309150a0e010f06140604080c0d1a130201080a020f0d0b0105040f030b09070905091207031707030f0509030903100f1b1812080712091e0501090518 68
    0x1024402c01001920782c142d94082c03d180542c401c0c05020042003106001241d014284000500e9160038842041e20580d0708000402c0900b5010071311840c074482c1119650309030540c0741042c5041480100d14003502141d0349080080392243e60000100c400d000785d8803070846075680c00d000c200b24400c50010010340c1c481805080401b446641049030740c00018501181040ea42c0da2200d8202c00a80e0400c4800058050402404440c1080440e0080c0f030b00385000d2140c1e0030003070405c1d519000244144004071500094800901d4016400300825404a0ba5002c00c24544840001c00400300b101d1001807250500340802d1030701e803000094640c80c46008002c1d0610f5800c01882c1001441c041c10301501c01da4848451070721050f4010020312130f41d8801d031078aa0310003407455840000000190440700003860a0345114011407030440907201c1040d44507001036070103254001c00740d421800c680d10a10f0000502004841001c90359000340c02224400e8955a070007680303540411401102601d141c2602e108000e000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 769348354 1250 769347104 769347133
    0x608060612060910091107020f03010b0a0b0d060e18190209130f05031b0607020f060c0c1501180b010528110d0305040b0708160806042304050d050309 66
    0x806030494118100814500e5070307001175800ba6054412850740c5640d02085600660034542c0102d080c009048008002088140700003074041c0350705009071183c10401044140f0040c5041d400710024010080d80b143c01132800307102d001c0d500100004020a540156102e20003c0071001522100c51940204202c84583d2010080e401041c0d100f070042c3c0358501040380c00070200b0800c3c03005114003640f003080c1b1070b07542d0710381080e00e842d0034005041c10302150301c0440200301c12100031910a801c51041816140d86103c82c4039010b240c108081c0c120509181f410000041a0641c01240030360300c000101d040c03010310319010041d68a4001c80c1213802d4041508141820555039652962519001c241054a001020031b86440d1411568000003804250340301c0601040c4007140c4030080c2c0c00f61440c504018540b50000e03940186100141490007030041000102d180c6070340701e810800b52195402e6012140c000c59075114a2000d409070303016038107405502c0550b03003080d2184044074840d54040008010701c0318076080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 769349604 1250 769348354 769348369
    0xc0317070306030b01120b0115020a0303051e100f090b0306060f040e06040602090a0b0414010c05010e0a032006100b07060b0a15030b030f0d0c0c03020d0c060806061206 74
    0x320800d80d90711408000101c051103418003804004850340c0c0c04404c0c43c42c21240401040c1c02080800d480c1064080010740d00242d01510a940340c80c02182d90703100e2441c41d11407a11030459142007500b0880c01c0001c0344039a004c3c440101c5809004449020380d84036171600c2180c000200c0242c2603040b203000245c190a004501c004d45980c00380c00041c4082203100c61604024081d24221641034001801d82e089280541c071040162061646a81c5002e140c6144060003244460351941440700ca00c42c14400e01500b94001d035950601a800d80e840081a07250040502c4103160805544828000c1011010309001603014821444226214409420210304100302d80100004482c80c2d0b494151402054030f07884441c01c000c0c6504254082c078007609040140540e9425070256000703512581b14480e40d02e400041d0b1903115901d505142441141d01d0418111602040d08060341010405a0f07403400c0010300c003800f604841d4030f5900c1c1c3c41c031601c44c40308110f00b512440205680100e42000441c0b80c0380703050003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 769350854 1250 769349604 769349611
    0x140304050a05060f0114030601061d030708100902040e060702070b18100c020906181303140a0807080f0108060106050a1b0804050f040204080d03050c0d051f05010c0317 74
    0x10101c451640160b50b81500e0101c040390001c5108407102c004120304c0320b0700740601102400490140c0415810041c000301030b1640d00b840c203090f145241d200b40040e52824050040a084c00703005803030052008500c0e15014212160080340290f2a14154151402012a4046c01002941e000c1c10f844c52078004031144e80d400174501d800d6600c544616901d666940d49000d1448400c168888001e00200c50042000381003000340300c00d0003021020800030b84501c01c0d03c851944443c3c2601280090302c080e050444007007500400c0d10745000400140201c0b00d54211501038456062503031800500c2d5607084810008c030710213118600301ea520410060003060301910141402551070300d00581c0914240015100c00c04a000041d140a40e000501303014608100801008066080d203083d0f00e00751070b1012850342c1e0b02c0e03a69210405c1541d1003002c1807150969108480707050312400e1041c40b80b8180004d44079000c0d03031400d0f4241d464545580e400034165025548448500340c141d1103410301042205c98090036500020f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 769352104 1250 769350854 769350863
    0xa09061520150402040c05120a0c03060504050c120c0c03030402010e010c1208040c05010e0109170a140102040f061d04050402061608040504061d0112020604050d051b0907140304 78
    0x911441d00c480d902005030780450b07600c818518800d410140180011601044014030802404000200245925603a04c5400c800d0346c410004504120400440003030445802003940581030200340908030700b81c8409411200380c4114684c49030b88480ca9640024480d8411a1a05400910006000d58000c0307000d4201e40d201818411020819642c8007070701d81d8400090f04001c5050041070106100d844803450f40a0102820240c82e2200a500041e0040410340300e405c111070040781c003551803141c040c00354041499001012040900c06509128040d4015020f00c06000b280d2120000d20070f40b04076a0224444050003158031000c02d61000e000140c107006105a03002541041090f18204d034a13145030105a000d8824291154100f00400c4142c0310550b028100c543c08000c28426051003c028480c111510560120150209840401c5003401140c1c040380e440b00745401208103000300404e02c4852030090540d00190350060004111030020103484840020b85412042a01c288a00c4011500980078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 769353354 1250 769352104 769352147
    0x12090904030e060d050405030a1206122603070c031d010801031202070e0a150b0310380406081008030a0c020102100207050f241306090f0503090a090615 67
    0x613a28010b00740e54044d141107a00b5800002d00c003060b0b0b60710000c41ca00c255880c0c40c05003d21407504503240d001024518010340300504000408500c9080c00012401e1801e40320303120364891a200b0400340600c402d011095011414020241c3e240500607801c1005209050b100c001d4582d00f95107075820258101400f80d001d5108284004c2035030001c955406205068070030340895491044607442d1008803441e0300c0a002c1010600a0103001c42e0a109094180d402c41514404800a41c20750300d00c031420f5062544a222510a248141d003014036030003441a10015182d4003182d88808410740805a2207101e40f5800c1c1d0814411081c4181c400c030243c01c1400c0c014411120314030034034020031040340e01440f8200c8035640b000301d543c418800103000000e40c204008000003042100c00f108840e038035500038603440c910701405002c0700c1003290a501c0075403450b030823040482058040f0b15080c1d6490307102001e03580c8907070b46040001a00304500c2c01b032202511403c07462a0404000c1c0c0070185c0d0099404040c0600c1c1204 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 769354604 1250 769353354 769353367
    0x1121410051b0913020c1612030314090d081b04080a020301062301030c1b0525180510030210020d0e18040b09030d11040812090904030e06 61
    0x6040011a9000388416000140c0341000a00d19452141240041c03500d104244220503640d5295085150a221340080250b80c0c0d4455628140c241070243d100e1015914000001042809960401031600c078420b071000c0091028022a12005000850f40a0415409450054442c511400c00140c00200300d4410302c110b0b8011020030840c0e9001030300015195032118030344105510302401001c00501ea034040145201c184400e2408840f151072290b98141074a410b1703040c1c11244600902c01400d544500680c0118000340b810329280c048008a464100401d521540c070f20a64204600b811200c5001c0e4200c2c02c81001c5100c0c1c00a010000c01d0041518601000000580c5800041041c8442154003800050009541c050001c00c00300f010240501c20b41c154040f1200c4815185a4100c4d030010b45d24030556840c54130702e0303145100d0381c03060070440e500b001a05050814210301500c140c1e9601804c0e9a0b8840100340d03951514051100c0d01d5a2092040002c500070a00405502707a4040e000740c03c3da0b00c1c002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 769355854 1250 769354604 769354643
    0x1a0f091f0f1712040326040b070819020c011205060d17030f010605030c0306041d0d0f09080f0c100201060306090b01062706030b010201091e020a0801140112 69
    0x80e01e03409081c16a000b0352034500721900500800c003811000000082c00c00c0c1c03d41e2101d02d548401c0c0b404403a001c10060001c41085140501502e000348454542d048c0c2d55451031415105540042c00904800da4440c2d603e140c07050300204031a54020410f9407901c400c0e0b0340c031b007100c00c0c003600024045c6030f0462005402c201c0810782c84441d0032004049280480e83d0b0342482a1001c100d200140d00040c02c0202c00d02c1406034041c50b040450360406d0003103074082441c180d103204014040a200507007124511944040140103500f0a801c0027090910b40c40b10741205940c1d00720652940e24064062a10f03800c0048500c4041c9814246030008007014400002c880c0c3e2030b5030322441100c8401a080e190b4200740801007050f95485a4807200d801da50894101602d003c600c580e0b070400c1154040d01061540b90031194050303903c00d42c020800f454101c104120b900d02c0740050500301780c0030034000307a010380044040410421814028030600001c02c8090090603844e04c0d0448987c0c01c00c050f81201c000d00b4140c20891100d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 769357104 1250 769355854 769355879
    0xe011b140105010e0c090117090102090a0f050f0d080901080c0706050a0501050a05010c03080705090127031704030c030b04060207080a0816020c0303040b03130f061a0f091f 76
    0x40325400000c495061107034000401d10000c0119169103010061884180da000c00750080b040c9401b042e0420648400301b0640c06801103015294214a001000042509821102070b044401c20f4802114510035039080c33120440c001c82019128150400003804107501c2091178030703401414001c0d07941c14104640e40d0a020743e002541c204107100e807544010700417440c08a2180006080908144100c040c05aa002c0c040041c01071a500c107014010500d00b499034082e0200c0e14040815a1516121034008070701c146800020380410380b241803078081300c025030490070f804980a803034100c5101d00400d80340d903a94001950b002001110406d0302030041200207110340002c0d090f414a10b1303c0300155407419000002d14071803000ca600003194020010344a0310744001c4121010f4468054010707075070345d03141c0300b0884e40344492a4008110f420680e812130180440c13a1b0107513441302000ca580c0c0528011004c00c115a01d40311490744e1383e00a0703000e80412400b44080e40c10007600008205064180e543c4c0e01100d4401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 769358354 1250 769357104 769357133
    0x1110030b0303070c030501110306010c030e19061106220f030309081b0f030a0e060325120b03060f06040c030b100509090a0c090b070602160606051f0e011b 68
    0x74440300013050003088401e001c1d08140c0707800100c2d500e0031454600c00003804607611f154041c00780001001200c8460b00e5148011015500701c20796515450f50302c200c000c02d1340b010400d4801140c01080d0200c1c1c0400071010090501a244400701070b815405a02d40442c0c401e0b010a0031414182d54052800c002070502c00039003450750001115640103d41480c0c040d042c8232540c2030040b1160800c002e00c24610383c1104010006850560b402c903200d6403018440300041d0101583c442071030302c1001c800540070380e1103906160407215008052104214420034190340b0b0409950f24107002010364001201ea0801e503101c480c004d0744a2901080c0b40100b80003140c00d28a141d00741700002880040d500146040c060906900160b4840d410421022401d10003840c141850140c031207520702c00581c000a200803a01900e0300c0710401c03044144d0f0304200d8030703004000300210f1181c00d0040c14032100300391500c040f0086110607210140c59004000d010301004455460068905400603500164a0804a101012150072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 769359604 1250 769358354 769358363
    0x3020405040b18010b0112150320030717030d092a090e0a0f02090601050c100204060e04021c0e010608060c0c07300c0b03040309140604031110030b030307 68
    0x5541030070b80f41c03101c02510706500e90100e0703030400c0184002039030f110000c019810300121000400b01d0b0040c1c400c01c41328400754000b07099201c1103440c0c0b600c00041c14440c5d003000c40c0d013182110b080d03c2d96070420165004001407201f810380c105110701e0000302040d0304500c0c4054400c5601243c603911021401000001d8041c0c968031001203000180301c40f6245114003a40031584100070412012241d55440101d5001d410080c0502c180c1d0b4041101c50340110709481e150221542a140c11803502241c0368002d402a2140030005400f183c4540f0b420b090500c200c0d0302c0f811001c030759022030803055004000500140d040c0c8844c150340e6460001103030302e02401458020b2803031050481ea038041c0212040d113030400b2500903003220600b15102001c91403150101600150400382d111034144601d042000c2c5100ea0365010017640500041003108160344026200e00b51611000000c02403c0320200344011030203a40401012801c008060101c140381a0718100344400d814a8007080c903144001c046070440e00501400c85 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 769360854 1250 769359604 769359623
    0x203070905030d02060601030f1806020903030c06150108070f050a0309020303160b04060b040e031803072d1505180d050a1a0a18020d02031219080c030402011707090302040504 77
    0x1281d81e041c0035075a039900502d8012b00028003108111511a050624018640b980c00655000c040d203041c030a036258100700304240d40b000d03c0c00e072041c84c2c41980000303000340c00550700b940010602c030300421208903421003e40c0c8850401c2c6032072500360001c0c00031820507a410f00c0140f103103000b000c0f080590184614410b061012650520f4030303003403054890142c0d98a1155003070130a032180580300002690b4181016441e4908840b82610101c2d0502c85160031017010360300b840048900d0744490301d104000781600254210045030742c9079a280184401103092a0005004100522503070031502e83c6001d141070010001441b0070025030f501460178042c80c104841561107580c02a402d1b00001003202d82c0400c405209100c8882450b070865082021084000e101d440c588149105640b0100815080c00b40b0004080c1c1d51041003950302c80e20f06038202c4400c000034062400250641c041da1003564050303641a160400304540d400c0580348a840b0046c4080200b0174500c2000000d40d445024083c091030182c030b14103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 769362104 1250 769360854 769360861
    0x3030a0f031a030a03080a1806020a08070905150c0312091f050c090603150306010303031b0c02030703020909030d06120606080c180601021e0d1701060903060203070905030d0206 78
    0x5002d58204121455400b24040003818032618042009006a40c0c10320380220075580341c03a02070004064804428041e40e41c001d0600041096550007041301e48165120f441700750f96858000c8800050b64003d05401041030500c511b081001c12000c3d00210380c442003624201005844a080c2c1510125054191584035070340400c441003460022494400707004109011a146c81e0440c2d048500c2411100c501540e00000091072043c11815034441d002c0004050365000d50703503400c0043c00341414079203010305c0c1405001103003549802600c14030246070780035000d00482480c64003003000384100101180314a0204009c44050301109104a2000c0d101504082c0c42008071810f2030022180c0070741205e2840d521031440c01d03c0301d640f5006040301e4400c001f628a1040d66a43d00101d09150072503103100000e420070103c2d41c003407200200d00450a40c0480c0c0d1403c030300c03130140d0304e12440c1a1401c1c82000e0108030800350a0003c112650011507208402e0b00300000107640e05c0f40824500b805503c005001a00401e050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 769363354 1250 769362104 769362107
    0x20150c0a02043b0715030608061e1315020304020402160b01180515042f0903010b0a0501080f070e0d050d08010e1605130506030906160201140402090403090503030a0f 73
    0x16200700f10b16120300704000b481d040d2500d41c0d46604c1401811481c1c0810030310988541d2007504110080c2c84c440b41a94400e04100201a03032019110030741501000c2d448000a01140140d440100c1c1c103074116600300520f01008a03035138001d600181059811540070420104020000184011041d01c201c034080490361425450700e01482d450107150300c9450a01061209000a003042d0b91f030b403000122000140305100402d13502c1494030043d06511084030720240b0b143d0341d0381c03205c0180c9501030064000744400303c0110104010011a0702a01d4040380c4400041124131814411050344071401341400c45080758202d002803014080480115017940c4015455101c0d103038048080760041050010b58280d5050948121400b038154a003000100311340031400e4840800480f004100800c0050049541ea0604901054480703408a5101114085418542401c544144100318506080a120320855152a42001010400a401a806c0000b40301002c1899074050000b01498802d0f911000804043c2003030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 769364604 1250 769363354 769363421
    0xa080702061014280b13120308010e18060138040504200d0b0306070504030f080c01020c0d081501110616020a1e20150c0a0204 56
    0x10040c1d2282c00c040003080f14514800c4200800c4104844104609000e00c1c910700c0071409241c0101483c0349041c80000f412111a0028072003480d40303070b507402e80494503100340120035030f0220001000074032602c1c0100215a43c11035125005020140c5460074010324081c091b240420a800140110b0000d029038841c4280c000c2d000c42c09801d03c00b106c0c2c03501c042661688101809280b00d028000d54984a1803014000f040e0b122489420003d022507846040318094880100502c481450091044a01041040b03024005503012603034442d0050101d90116a220450b940003100c401c64a9902440360180071042445407081e000c3c610764a030003240c54289080549843c4110b269414072010240c90301d001400410101d86c014008490345581d40c1049400f01d2801d400107001409880340484810b0380c08441c45008440c4a0081c500441902c032080c5034501100c0240480c1d662000750a4065440410040d0142543c4140801514511409600070400ba18035800b8a444800c001350f07074032100441001c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 769365854 1250 769364604 769364611
    0x1006030f0b0a0501031e1b030507051e0a05040e132303031515040306150509060102030a080a0f0f0204290d0908090607140105071b02010e040b060a08070206 69
    0xd40c1404000703800e102041c0c2004039809a54101512004c1103500b14801000c91081a00000c90400840006c0307201c0c103800e20040302200b07001a0074200414006445901624a00407032100040040301c0c00440031007440d80703c2c52010701408018003001503580d100402c210300c1140444840080c1201074600305802034403000c5110031a14000368000b00100000054170344c00220142550090741c500800039101c078407000502840144002400320801101e40c100c180840d0160140030b100310340311801c0107a0b0034011602039005900034440304d1800c5108116190301315000300800a082104110148291100408080304507500081d0801420b88070303841c040e46166038440f1044407180074061510061050100f0f6011042e02e60050f001803088038405c40f1209003000784241d5a80310300d032800f00d282010700c501084043d441e15001807216805000503c195031540121025000607950054402001910325143c101d1303540c001c03c5086440d007600078603006a40d5100d1002628003070400034540040103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 769367104 1250 769365854 769365881
    0x60b0a0b04030807050c030a0311070e0412050a170109020a11070b34110301140f0a0e160f081e100f140a050118050412051c0203100603 60
    0x56004100948040d8195400eaa9020300f00955a98072420800d00e418001c2c0c081583c5801a1114802055003150303c0c2c04144110314269404250f45115a10844070102c030064003500c504801d900b00241708070020500c540c454100340719280b20308603030302103080d100360440f00c404ca07070026502500d5508550400610001000106251760400090183e2405841ca001c0611450640b0f650580844440044241000e203003c800c2e000c1c4043c1441484400d12240f00da02a520300100521401d8411910902c240003407440a681600c1d200c030035074005c10280c88414000c1c024080f040c1c1905a4880740d14004201c000c07031502c244d0741491001070400e20b0581d0381c55004000d0030b0400200003001f15807c02100150800000c040a800b0b4101c0301400358101c12062010802081000c000c080f81c1c0030718180c44100c100014451403515001086940c1550003509250441d0320300d030302c1c4510500060034000242c04041c4c960310b00c07441044090340c20589404c100100c000d030050212590600c230340701a600b0702 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 769368354 1250 769367104 769367119
    0x40507061404150c03050c0303070323270f030d1d070303020a0605130f0b04051216021923040b010509010c060b0109080d0914010f301404060b 63
    0x410010206036181d040e00748003809034001c1c56009042c040e41c140e40c10041c7c48001d590782e92400000050040944031401141c0d00100164a250508130b00304091140c483d00416801c21000c0b1448581a4a2191070010350340c811142a8100c80d242030019255014940d00080b03501e00d0341c16403625101e601c403040b84845901450381040407a0f80041c4014406410140c00035103511814040010300c0351080700641b07404d000da800e200c20800c0b04a04148210b004030f0584e01c40341c02e009607124540c0700da00380d40001e000003030002102500d05015203100750b03801e69070484d809035540e0160201c81111150034020018840b0540125418540245811b00380246000d500e042d14bc1c00c00a09104420000905043e60f111031248499024049a2020b0001281200c0c4011441900201500c5a5000d40d8014000c0b4550820040d4000c1505407498140d0340c948200c03001282c00d1050710054102e4042c503901010b07100c004d40681c0c003442071000c20b000d0440301d44564030301420403406a0701d062504500030180c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 769369604 1250 769368354 769368359
    0x61005030705070302010605100c03120605130518011104081207020a03320c0a0f0e0403143601020f0606130912080105091005010c0210020312040507061404 69
    0xa200044a40c406081d041554481c149070408a0040400b13800150300f08081110860010707401844942800c0d02c640e480708941400308524805483d85032180580048443c901282c0c0c1312000d400c001e90054007907610344010180d0003001425101c0d00d5100380780242001800303001810044c09400d0144900f16030052070020a41c1c04a102040f07035110203003491800f41d040d41d107485500c2119081103640d4140940c40e10608140c6140c4904c1145507552141110f500005000580350314510210f0700e540c0082c6c1c007035580c0c1e070301e003540e100311b0b03000ba03d210303900c020810700c0348000e0f02d4031212100042401a8224102940d0718076007804404014842c190b6011482601a035100004c87c150f10960907580c40c0030f40569140341001802c14400300601d01c0fa04964014555a40306450380e040342d1044540b0201c0e81c0304c00b218580e104803580282c5000070641041d0101606118544404004640c07045914220300e01488100d040c0d01590119440c2c3c010b02d00c04c010440e80300c1101507071640214207051a03e032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 769370854 1250 769369604 769369607
    0x6090f221514220b0d031d010305060a1203020a170901033b1905060f16093003021c02010606090e040305040e090a0312060506030a0f0b0a090906050610 67
    0x8107004929841c0800c03c0030007008464540c1c0000e038130040c02820f20603c070502450040c041102c50b0b40d105420110082c402c9480b90310900500d4051940941038507580e50810700f10348420303465044158154483d0940c0c1000041c94820510040040903c0054503030384010001825286044000c40c211400740c0c104035030044182011b07402c0700a001100010a443c021007160801e031000f13440d1241124041c08030014030502140c031078803601000741030006540e22a00c03e20302d5814260911300001d00d4420003441220341c02c0c8501082c000003040d00400c0100140842e00d10204072180440c010381200e41c0039400d5500c56207803100c21101c9400203000c9981481070041c045c01c2d0314072400798901c60b41030204090501070800c440c0a083d01d449205128500b5020269417408107000850009117401291501c4c1d074114480c00041d01c600800c608c0c915180c000400020340903000304044103542d15501c1940c1030707072000c1d9a00000c21b501c00c07012541d0009420070b10100d8400500050151907000c051503200c6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 769372104 1250 769370854 769370869
    0x3021222090b01120507030e0a0c05040506010503040308070815060408010c0206100518061c0c0602070605040e06060714010f0b0f09040803040b0a090f0c15020c06090f221514 77
    0x130481d9100080d2540d403250f00720060042c1080d420000e00400103040140440600d80c070080e2001920288400e450319001181e046c0b108a0303000d00003032990800304070510700c038015680c0c0003070b01c03001060070542080d0001051540309a100c0748560b95a002001a0103805211032503002030000800c800c101c0c40c2c500482c41c1701d03401200044240d20b0713070000a42c1d5a5039105074812680405036060f1a120307903624100d1800d0015019440261140c01800500c0510a504079000e554500645070081d4540c1410300c88aa040440204c805114288441c21700840901c40e00b2030500d801a004138107c0e40700001d00c43c1d412918092240280c40304001c000100380104212078000342d1000c0c1102c13690351882d00840040840240c0200f41090f40c81c09032092007540700208007a528000d81a401c2d07540b49050170781c3c2d6040c1c00c940c60354000d2014444000d1600e0110740070100480060007220102c1503040d0804603004504044088156613252544000104480910083c02000c0c0329440010020400907070b20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 769373354 1250 769372104 769372127
    0x30020c060a050723071d04212615041b14040305030a0504050405060910050910210507050a18090f020603070206060405090a0c1203021222090b01 64
    0xa0000000b0b51800f0403808081d140000d07104c10504813100c1d0030f128003498451210784150410002145100d0106a1805045c68061540560a041c0740e5401080f0210083c1c47c2680c41c4084c0051451700c00036400c00b4102c0310807480c18104280c0c04625200c4010969411144000c5000320300d49800d0208036400101c41c01400045070908030360703c103501c143c10900d0b440b840d00b00804600010491200342c85d0040701400039100c0450b024042d41e03441c1024040150806c403201e0a0403c88a40c0401c92810044203198001102d0011101c4458990710b03918203201a003c41c152101035503582c0501800340501c2558058042150b4103444035160581ca441c02c860080304100c0030558030701c03002040058000e88500000d41c081c0c001e545902d819007000c0c0d1070348c00450350b05000b6402e040c0010542c401c0410814407080d03002c14507111071820400c0090f13070240710a10480c2580b03c1d20765030311126401180908845234070300450020700c510b00c134000c1040b1400d03540040c004c5404e040b078004950380c00410020304d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 769374604 1250 769373354 769373357
    0xf10150c0c21080c070b04060f02070e09060a090813030f051905070614090904030503102408060f0a2405090112020702180109021e071e05070330020c060a 68
    0x2281c00011600c1d45c180801c903401080400b40004002400c203400c102e01c0030074414540c00784c580455131807074107000220f8201c85114003034100700c00103441003519074000082d0718002c04e0b030301e401c2407021001c01030001c0311a0010350b801859000402c04000b001c024580766412415060740709125154bc509640c1c00041c080c00d018003509041501800c1c3c81c80c1c1c00d4401082000305500d40034105070138003614079032064035502d59400050704081020489000240c501c06650002d440751800207200860715000f010b0031080d4050002072440c8056035494900c540503100c0c1c41c400141d5035440b602d05910b240342d40d034100401d0080a004416040c0e80106202000c42c1600c080941d58030003600c0007908d441202103a51025079080701c0003140ba414203901904219804900302d00c01a82c400304640064060200004c001c0d445485940c010700c40300345040c4d518a80316108170f60710180c803507440a0800501c40190101d044d080100d1b00c0d10312801c00310a01203400c05c2c0c00074000400c040c03000b01d85640720301d420110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 769375854 1250 769374604 769374607
    0x27150906090b1f1d0307030309090e07050a09020703030b0307030b071e0e010e01032406020118020d031103130806060405070f020a02040203180a11270f10150c0c2108 73
    0x3d0445039131202c4001c5003001000d58108940303a180140c00105140509030b100b0b481c1100d0940e82da04001411070503500024941d464943c5000030204c082e50105504030105a201c99001c242d41d18100802c40185204070254038803480c204400520340348000407080080000d07445645101030b004400032030310050a18003010460360440c016409400c600c0a01c200e01034407411358640780b6400e52544015030340070743e0003407147c0358400d0503440caa050403000196100c0742444c0007a00003030040840f41a0850100140d904004000d66080080c2c81198000301040c1c00c0324040040310b02d06032148561081035030a0010041e0221000290744201c000e100070700841d800000b2603a002000741c0602c03001103001c8100c1c1c001a40d14900b1201441c0f01001d1980600c1c180c0a40c0c200405400d8001881d80000c503c1d00b0801c0d5650442c141c0c54040040d0000c0002d500c40e013400701d00662002004a2448501c0d01c1c4c90b1840e9802d850000c00030403840e403200c00100c603203141042100c241c5c41e001111b10380c2c205803401e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 769377104 1250 769375854 769375877
    0x30f0804121b20150403050309060703110a06050109201804020c0106081509120d0b0d0f0605042d020120031611010927150906090b1f 59
    0x2505601c01c202c02a02c14250100c00c3c81c04082c20f550884181642960014042e80c001c0d0400d800c180182c0c0402003107904107000d003001d5420070902400c106030184c03400c3c0d0f00303001c0011030450910580420070351380c480d1140014040f200d4a40240050207000f00c004444944200a01e54858010300702e07022460503c03070b43c5000d21a0b6407501a40c040c0c600c0300f0000c100d116a03a88580c0da8584054a240d00d140c005a80094040710300440d03a11b43c42020110100e10b001c003c1c20f5014001c06559440a80c810881055040419008101e1500d0f0b107204004c005264105400c100d40504040f40d5080c9050b040d903030b0002c0750710200041081e450380c0e080c2000010181c0749481e1008a43c076180b01c0742d000c1c0c40081348008200340b840a845c00310b2405052600036130100040112031680c614040e01d240d190000b00c182800300c86068820403a4a08101d000400202c1c030313003090080e031026a000342c21017529100b00b0300c4281c0c220300c616044e808003210300c082c0140b1117101c40001c546e107003d409014000300c21400e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 769378354 1250 769377104 769377137
    0x510092903190f0f060602011b0c0201120912050a021009030906030b12010f09150e120f12090d12060509130309080d0314010b09010801030b060d140307030f080412 72
    0x1502c0304221801092041c1143c0c941400024202d038483d11b00151300704607010001c905101c030b4400c0c82d15442d42c0d0f01d0100000540042d6002d0a050b8000380318a60746251100100e05401c02d5840b12428130350b07d1a40c2e40307807500c40080c64000c103d001d02400320b14100300500003980044c0c10700100c0c1c1f028180420310982580c002095000203000e00c142d99400c0460240a5011551050180509c10340c4c04c8407410164105200c1180c100e00c00081c55540501c0020a04004000181c1048002e0f014010720b88040c0000c1da025890040e903000102d41d00c1451200d012a03009165220103181110341007181920704000030326211006090315941c40044032181c03003031501c18194140038040300c100301c400c04880500300500606421a1064a82000c500007158600c00c03c82100d4034440160344002080e400c64403400c0c00d0681c041c02c11644020740603100c5c40010881e80f0f001080d40e1591014549841c018200508107031240544541048000c504000016401e1220004195442d01e4842c40c404e41c03c40300b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 769379604 1250 769378354 769378361
    0x100b010309050f0d030e030a0507030305060f040c0c0215090a051302040f0b03040c0f050f121606170a06050a1806050d060b010f020f07060c0c051009290319 69
    0x6000c0c00b00d0241100d40d1210b400001149000081580e5082160100f10011292240100890180028001c008500100f48aa0820b50b04120700500e1103a2000056000604503034030f400051003c10901e2480000b540380c2004503c0403802038402c403078504010080050b0490034035000f02485880440741103051190141d0649018003101c0e900402001e859070442071141c0c008130303070403101014900400b01d005201d0f910460210707240034141d0102150a82c0402c8504022081045858031500e002142c1d01d82d100c0312400010035280c0c40f45501048a60203a4403018002848546280d00380401000651550a24030048034805260b01b9202d81e84041100040c00c103d500c0039502404807070345c0340709004c0154801e070806103090300d0b80c118080c022003090740c07038001c1400c2508241d003103008104141400b400c0710b8182107100740d01c0c5920141e243d1000520001c4480b00c2600044c1c04d805050064444401103d54007444014104000a01c02d41d031841c2c02d4800240300351034030b030001c000c0460782056640 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 769380854 1250 769379604 769379621
    0x40f1a0f1e1506030c040e100305010c052a010b150a02060105150702281401030b0a0303050315060d020a03020c0d020a0c06031a040c0819050412030e0f030301030c0f0611100b0103 79
    0x43c40c03d1071f207080560500b100c0d185680010364680d4070300308001c40c0c6075015008840011b0603000302d08003117000301074000c102c3c0b00e0396070f84501c0d4035521340d65500c4050340c0b20380c0f801300600c1c00d590341261034000b0300e00001c0c076152058000c0350107a446182c00c00085569001515591030381101c1041201c11003d000d64844800d41c1c0031105601100c00000c5000c0805c1c8821100d00d80c0e0070303641003014010070300c2000300500c1c43c1c0c030024011074020800305044c040d440b07001054000c000b40019180240000714101281c1c85032403a840007c1c0d01282c00c040c820b8050001c11b403002c025200400d4640c0027600e52010480e228810310041c9a580e800f1502d820200340300e01403020070000d0040040300c0024038003415528080300c8840141c00d20072036000c040329071489210b0040b600119205144548580c00303500900382d006000c0c0492080c0714520440400410045018502c1050b000780c00318900b421400c50b44541d90802814031000903004a951100041c0100f00c040d510080400c401c0190801a070013411a0b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 769382104 1250 769380854 769380869
    0x408030408220e01090e06071d04110d090c0807031104020904062d060309080f0d180c03021525020f040e07230306040f1a0f1e1506030c04 61
    0x4607000212040f42d030030030f941201c0312140b05024034148044110b84540c03048810b5800b207000d08138041200101140c108402c1d0501501c001507107a082c4900c00070b95080b4450307501c12203440f412a601041900040c81c4024118070300208a0343d4119914028000e8100c2e154902075640400c07000600d03500c94202000800c2d10340444860a96121800001d4684103004140e82c884036030b0002503654441e02c00e5040d103d40140300c260a003105600b01010503804040c16480c8035865204044c0400f0322a400144003a2089440030300c9149144140485540380740703041801c004003880030b910300791001107250280010340050105d031a4054400070b030440c43c1c0708140981140c41c10b610030680c4040000d152040e81c504805403c030480040080210a002c0e15401a0b0980c0220300402d000030b8515003501e01d440d21450107184100d020700c0f20380341c194400b2220803020b00b0360382c0103000102c4815010320b0016544080840c2c594546080c60b070725100c04051013203021300c0f00040000c1c5049180000d440140544 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 769383354 1250 769382104 769382167
    0x90a062307030b0a0e01050604032613180b0603010b0717180a0506041a03100504020d05071d090c18031e150708010b0c21210408030408 60
    0x101c10010024400c190985006400c4610081400d584000e00c080c12901c0040c0200d00d000d0665441030b0b42c80200d811085901d1841c10302c42c0910303150703290251020b034810302d41e0701c07500b10b00d841d000b00c00c5841c198810ba1900c0d441e007118211759841d1a0100d9043d100e500043d80d541d021549007060102c01e212403140c02e07900000c1002400c41e0100322058605030002c4075001d0b00c42e80c0300d0003049040d10440c4950300c01c0038180c518424244100d50042c43e4842d0491100e03002c243d9130ba00104042c0d078011021031080c150b84104100700d00342c10200c1e08040103954410030b00010382200100380f03007010281034603100c410301103040b000c4049522946045020050183d40503800c3c4403801000903800380080c0700c1d06000e2346d20070550b00200080100d103d0f42280e651110a0307403821180050320341c0805902e01e00c60043e0f00d00303907031115485000760158400c038450700c0d41d07100b40d00340307103818000464054450040030000c01d00c0b0214200009580c2c101e604a90510f58800021520f60203000c81002007080c662070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 769384604 1250 769383354 769383361
    0x10021c0503090f010e032d040909150c09050603190e0601080c010c080a03050c0c0102032403070e0a0c110d08090c0d02010f080405120c0304150206090a0623 69
    0x6001000d14010401c1400321240c02142000e0b2a0070717100304131134807800d65009000f4000c14900b02c420909224503001480140701040f400054620b6219412041101743c5800710b4008004210300301210300d40d10400708001402c0c1269000741409940e1150780d10610010002c0307211800b551100420401c162700c3c04120411140c43d10f99100c11f400d200d200d105000d465422449940110f10114940d5801840b040c580306000105030020040900003002120701805021400b8000348011409030014140d040c000007200c074801200c0002c00043c1034040e4100702401c01c01d40d075120303409903040b009407a00031810400381c02003101c0c6502c0e898040a07281c41182000701d045604040d840b4095a0601c003660458000c000501007083c4c01c194009002844108480880d01e11070031070307076800c14401c4041c0d40100502a0310b506e0303030350413001100e500340d003000904000f2480318850614866070750b40003610251400fa0115500e031f81e00020081c15031600c540100042c01100081041c1d04140540f5141c602d09 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 769385854 1250 769384604 769384607
    0x30e0316030203010b0301020a05040b0a170c071101021c05030a090f030c030e041b110f030c07050307080d051207031b0e040b0a080c010311130806060a06030e03030610021c 76
    0x1400d120070381c081c0d4a081d031205c00700c0c1018002c44200d0969038907401e140034a840c119030403d9000707584040070042c00c13100350000107609184080c003a4905011403911104503080081c007000c0e9031008241550f1040c154940400059100c50740c3e00b01040c1040b580701c3e5180901e03400a000e200c84020305100a00914008043c5c01c28040d10000e8060342d1042e5035040c410051200b280c071031039400d440803c440010341c50b23481e1050210709250301d04401030b03440541c1ca0320303002440c540004c200e80029030405881444182410003140b0010800403000f094a00141c0794050081d21031440c0d813043c00c00c14140092000c50180d00301d544282c0050f280039040541520004008090008100b8496030074411241050320b486112581035440e0322014120301d062a0b40154000c1c1600c0c80c0441d51032a0502059550b42c415162100081c0001d4000d0681407030440304111700c0c854940c00c1107060501e060f8002010300030000981c0c0d4810303015a251501b1011541045c2d1410780070f403030701c41a54468200c0500034107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 769387104 1250 769385854 769385893
    0xd080f070c060507050a06020a0302070219080c091303180f03150c03090c150e0406150e09090c2101020313030f0c0b0402040f0213060c031218030c030e03 68
    0x1580a031503840a1191030b14402c440c40c0c82107142c068000e40c062041d54001c0ba005a00400810896040c010700d4041950701240b08002100762100040c0410401000038400c14003d444060404032444402e40c94281b46c1d00e40010002c0c078026041110041942a0000810f44290050044450303503282c06643c03460401800e240f40040714018509102500100074040d005900240d54412100c040e8142000b4404603112035114601e0200704410111080030346491003500302600e020000b100c21742c844020f01400e002c01e117120b0980a41089010800204000701d1103200c8001e0443d100644c600340c01d101036040908520940303085520020074012080d224080391900c962103502c0f00da442d504c1c920707410344e070198108e0342c0546558588000200146400c3e40600c1c52499035202c01420325408110440150155810030004a113a0f0011f83d010315400220100805a00c1542800002c1c0120060310604104510083c28172003070302d40d600704141c02146d03402e840c84c00180c100d8503203010750b80d0300355602c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 769388354 1250 769387104 769387117
    0xd02070f08031b03130b07031d0604020a050f0a03060b180702010b03100c090504410f13020405060a08061603060b03010b030c070609050d270608150d080f 68
    0x3c0c15022a54044010004810780384240c44188103850741c1c0442e92034202c0740817402000780c020581e90701c28030815041d000500b8002c0e1108000200114a002d2040c041c40c820701340c100318807440e481212a01c007540c81c0c0d5030000590780c0c0f03c4000708501c6800e4004c1000e1040c14980b031202c5845407030800c404a41e0541c400c0129890440c103c4450042c201d079820121029480e0050000e8180c5000f0b00142c01c15400c600303000c140304241e0390305402502450b00030707000b9a08041120600c040309581e588490682c9880e4005989a0b40c60040f420950342210303c0102c1000d00174081c0c0d0300c4100040180e0b40743c10f8102d0041884e5400e540a614040c404182118049104000803a10344000071501c0007084060300e06030741600841510b59180d212409603150032910080300c00580b122003031030000e0028071040140300c41ca03441d206043c0319502607541180c4503c4910081400c2c42c80c4003003020641c0000341d6508158a607103244207807074443c00400d804002011010342014400201c242c00c45100b08024a80f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 769389604 1250 769388354 769388371
    0x1e060a02010213030f0b1f170f0106060806010f030c050d090f060905010605030f0109020a05220606030204170d080105060313140f0d090e0703510302150d02070f0803 73
    0x2282d0b5034040003070350004050740c0f0304401047c8007a050045c285000807414aa55040307084506a2080003011825100207410800000e00110140612540c00203031400940c42907042c1400840009140248540103407044030401c84d881c1c0701c60f00140f20002c91825001508030005004401c900c0c1031a81c040e2000f842124000c0c17244a009003038540043c45610004c0c0e03070003010340c1031451a103020401c0f841561101900440e000c0d58455413451030902c903490080260351009a2514940740c04141171158200c04d01c2055041041c01c071503c1980981c00030f054440c21501640c9945582c81100c0c220141c4010050030340d20381c40c120044c1d4880c002050700f50702800000329001039076078510880704804a44541011010001d01059806029800403403024218803101c08602000005418282e21001c5d845c880101c00b007941d04074504034044001d1522524400b8050200346194045942ca4900c8480060000030204125100c004150102d420964000345000c0302c440160500303e01c0d0b540300b07581c50034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 769390854 1250 769389604 769389623
    0x4081018050d03151d13030509100906080606070b13081b0a0b0604182904030e0a060f27080601031406010e01142701080d0206061e060a02010213030f 66
    0x505d50b200c0322840114003144901104094652101c580780c000f0909008071b0600a0511400b01280c0394410404003281c400eaa541e000e031882c011018240c944044d1007203005420070042100419404900c3d560010320202508211400b04d0a04544902800341c040714070740095800c11035a081e0000d2551803082c0181c03203406640e184e1204000451700c04090764409140c3e0315a801c0d010407480c03410b4804030150300768000c880c1140003030710043e4a082103404402040d03c03d145000030782010720400e0050501801c02d0025070341a080e018109090607840681e68030070384000221480440417400c0c009022400480f140f40d6140d1605065217444d2404c1205984074a500000e084000e8a51050485d050381c907800c00c1202c1440309000380b14030185d0b030000841490508041d02601a086618003d1071080080d080c4d65241c480c00a08200000c0d202920600107580e1844995040b03039924048041d0403111641d5a01c600b441c242c2c0a80142000e640152101e00c1c030020911504050341e091692090002e907 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 769392104 1250 769390854 769390859
    0xa0228050a03020a0e0709080304180c0305070813020102120f03070f05040e061302190809010c02010e10051b0a180909030804080901030e03210105010504081018050d0315 75
    0x428621240b002039030044a880c4200441503262503043d41141461414540054071748200f14595072055104150710700350444c111500751002d21690807086514a000d02c0142000039004090520180c1442c0284070134442110842e030007001245580f070304410980351030f010070b10300c049800c0e0001c58192001c41c41030348030301c0307a802e208101312800d55040006008068540c0c0c2c051000741d06030491004a00c1d6404c120b0416407d402644641ea82c01407580c82d80003d00c2e0480d000d50944140c05285400e5a0602a909000c0340c404210f840d4001010f41c1c0008076070307481c48910104080c05101000d01a000050030207003180e4004030680c2503500c1d09003000744d0580e58011400880707180301f0026000074000b0000c200010340c824024070b0340180514010a00c094621710070b50651384042041c1c1c6200346410002e9115a41f0b10351081d0050509003400e1341800d140403044c60300c0d10070029031903000b01d0b541d4412362110946490810502604a011511007040082e0040c008003000c03a00d100c0f80c0380300803200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 769393354 1250 769392104 769392109
    0x708060606040f060305060d0b100302040b2b0305070c030f29070f2606120a05030a030e120301060804060615020c040e1e28030801060c050a022805 65
    0x46404848602e05183d001920340340f021402820003520305640403440e04d240d0004204c2c0104e91702d004080942d40c20412a20710704c100800c403500004494041c0c0c030000244d0155072078007928400302921580101440e80d074a4502141c1a1040d00c0c4020b000c064a10800320910440505a02941c0c1c410220003001080900340b6608101f100141d0781303044003400c4009500d082c840c240075004407074141400103980d40400b4001c8000d0289121035000000000c080065610b4158403810070340c10740e280078219140700382d00c0352074507481208802d00a0503202d070410710035000d041242c0d0309280000c01c3e0071781d10307941c40d400010014ac8058400795900c50901d6804550310340c208210213072091042d0002e058250300c540c10300002e810852404640750280c601040721040c1400285442c00c42000058440003551040070000100c10004c60007149010441080c0040d13040b402c0da505641c0e00d820b0080c03c2c12500e1074220316000c68a88025080000201710204000d4550030780b5000c5401030500f032040c245c95009 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 769394604 1250 769393354 769393357
    0xb0d0b0307050d0f0c0947120f010f0c0e010e06090d03052502101418032b031a0310020f0403050a080d050c1306030f15080708060606 59
    0x5400d9103c0040e52030301c4000b51210030f441c03844a1044140c0d1940d580da8104040840701400c1b1132462225000228016007108061014040100c01580104ca15021301c01f402020360486449405003c1803000c40d41121005c102c00705c10b5010700c0c0000d01041c1061601040603200d29400c0301d0118841a000c60980d602512008102104c05403401d030810b000d400c100070150340350880c140c042c0a020410000d03000e200e845400b65a042281d01c0c0c0c1403c000d1481401141e0050340201c00400100a00c1c846110716800200c41c00321040c0310107010300c00110380019042c1260240440c0c4100600c3c04800345808503880201803d5076661400c00c5403212189500c08500745500d1880e9241d0052800084401050b60150038070f103041c030350751130709185d140e640303640c64803c0881d815200b1041c0400c0003030b0324045600400360720006d8548000c0c180810071116540320507a90103503006040d29040c1c007424030525503200924143c0c101c040040d1440d502c485152f251031183c058440140180c0c1c0004a071800c0040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 769395854 1250 769394604 769394609
    0xa120207050d08090d02060705030606090406030f1a010b0a0e0a1d01150f08040803101d0a0f090f0b0714070c0f050102010207020109150516030215060a05030a030c02040e0102040b0d0b0307 83
    0xc004d80843d83c8d5500c030446540d48020581c941c000c00c02d004000d010380700ca103d010050f52090f0080f0f1503103101428000e94144d000502c0c1058001d012006122a00381ca206440e451000c3c1d0030301280c601400000580c84c40b480c0d4204481510b0074000e040b06040074541003e049500f500c50781d00145024010444412001860307090200303910001003070014442c44000c2da0301201d0009000d1085803920945030704492888104140e41d0200f409010b501c0c00684100d81c0045000c060400944c00d107940e070403d1010300c800d0b001e00003100b0780c00010840c901917000d030281d203806151041e58504031841c00345001e480d24090100410340c032040101e415401403080f0f0b04101d0301615010300e03003407812a295000300001c5a0110800c0028003818251280c1c14600d40104e510a0f000381072044424410010760110052041d4469200d080e002c100719100441c19400c002c1d01858007444c058802c0c0086030282c6085000502590f10006000820b01c031100e014080400014a00344103254403001011303070701c10450 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 769397104 1250 769395854 769395857
    0x2010209180604142508160c06140c070506010b070b0402130b210f060103121116030803041b0b040509090a0605010e09121e0a120207050d08090d 64
    0x610710003a030a1460003961018000700040340002d0640300d010b0111105899500404001d0320704a14000d200049a84082d80d5603d0610582c3c070b80002c0b2202c120100b00c41100501125640c418140318054002c1c94007040f0302030502165080c0124544820b03440550305840c680222400480c40c80da000086800c40381c2c220290782100c0d12a41c00b0411140d203031001b2090501c2d42c1e41d035101416254000043c20700c2c0c0b94082c1000780c210031030403c90b04201c2070b1103214242d0b41007c0300500024150b03103000b8210181518041d190f0520000e0b6a500c6c0024100b580c501c18142d07000700104021040d0001c61086100e0213241c0520456614076038201c003020b009a0040b0002408180440c1c10200b48150780601d21104403008802c2d65112003044810a0300300542c5140050100106410100102d00b00b9601141646142600a1290951420100c036550700309071000200121080e100d2200701c41082c101c0c010440d51910b8915140f6580e000350070755000030030f03d0b02e00090030152022903110b010440c030b03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 769398354 1250 769397104 769397119
    0x1060809010f450b152d010e0307090501030c0806040c050f060f07050a05010b010e0a14030a0b0118360c0b040303020114060d0c0e100b031f0602010209 67
    0x1041c0b2a18045103c280ca45200003441074078296284000d109a540911300681106906040014200c1c0d04030100c4032840e03000386002124030300600540180f4038034240e101d1316180106240440100e41c2c1e00c59000a4a034036116005004c240c2c2c102c0741e448181264441c4a5118940b0f035286052034035624103e4002e4500e101c1c61000304042e046c80052580c4d0650028503541c030304040078011402641003100245d481b43d00c580300072000c0200900c286c108551302401c22107140c3c1d403240c0001e201c0700c816000303440390901803092185464504004d20824241e000a01ca4080e40c1c6902c4440c01810b1482c00d403011541c10107614410341031000c9441900c0d299090b211080010381d03180103900f14440400c00301c941050a01000550144450107400a94400ea0012031403166800002008040c0a0030542c4500e030200050340015810f5614907084481c279041c203000310703a1891806032074001e4607440032880403000420810182801100c00c994400c200b1184070b13909032038400480c00c0707005100f007050b0050134 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 769399604 1250 769398354 769398401
    0x30403030509030f030108160801060b18040902040903021014160305190627020c0a12020109120f17040b0118020f0a05090114190804050f0601060809010f 68
    0x480d400c242d6000b2000c2048070302c3d082c95200c0e03000c0c050f0f02c241d000210b1a002000f20b00310014848400c040200550b038020b00000341050180d00c000d128613208440140d0310700300c1e148215112a0040010340307400400401c20b030420390401a442c1c030302002c02000c110303250039041020141f01e010110302509461101c03030980c004085c8203a004042c05081d0309204510786907204040c4c1030500400c000740075103a107060340d0b22820320300d480340060440c1c020360710850041c4917124071b541c3d000811300b07113403904040303035411b40390000100b40c1c010845294081c0c0000708424a040e882034002140d12501c0b1807984e0f60b0400031544202241d010182a01c0061414114070010400060b986d01d0300240040702d40401031501855514503a502d501483c100300104401240c400025a004660000314080c1d0750300541c5440d448840d07554440c00d252042c042409030305004541449403c001e00c14a440b04002103409558440c50054695841140e00d01420342c2001c00760300303551a03c0c0c050403250001d48100085202c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 769400854 1250 769399604 769399607
    0x30c0603020c1f09020d060e1504050a0803100f0902040509070f0e040509031b0607091208040b03190f0b03010c09081209121603120804020303031b0405040603060e0c0f06030403 78
    0x2244104600c03d8640c0762282440135940704c0300160f12152140c0b10004100307001c0d0003a1414030460b20380d44642c5400d1142000086080402c29054496000740016a07076900e230805603102000c036803c10458212001408143c0103c154024001c1e550100e4404405a0b40c0312421503504144848140000362030304c0e03150700c00d030810750004c642086c502c006a900f030122200c48001e02e484004c82c545507550281c8103000d88140c0010114010340418003859145402503103509a00307100f24403407a0021100040020803001e030380780c0c5106035030b1030100c2e00340005100403421038040c140b00d0314480d200e546480074200c11140140c51070011543c019010f0201103034264011781c0b46400056003290044040c0346080038412060009120f14031203201040581419030612902c40600c0d054110188a0060705210160340c001060f0395103c184641c90303420485003100030700c3c100d0140d82d120075001342c100500442080810b0300316580d01c2100100325041d1060102c100031a688c001c4001d03507080501000800c3c04079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 769402104 1250 769400854 769400893
    0x80d211a090a11070b010e090a0320070b07080306090703060f1205151611061009050402031e071701020301291201240e030d0e01020a0813030c0603020c 67
    0x40b0602d0b00005514400c43c1600c0319a0b8401030048030b880045d28010710500003241440707500a050a401030042c088a0b80e07000c7c01c298422140d10500615004110f1180d000400c106030140624450481d241c01075840c1001c0a6042918143e00c02c4d02d1020000e4200c034442c0c40b890f4202ca068958106440f40f50504480808038030502c107031028090b1400d216884024841814028008030130400030304075000c60000e1400c01c800080f000b5540204041c40783c03040e0184c60440644032480f00004007034a903440040c4c80c00c0d441c20801046400c411032090800c81002c030b01c003011a1002c2020103454030340d0360099405c0b0f200901034481210090031841c4190141e4004100103401544502460215000070f0ba0380000c409900c0080b60b00640070803015160007000e2804004035042c1003a1144151181c0000d88900034900b0400c00c1080515180310a41e2081004080c07041c0c200589650720740600701d80305012002400300b9070780d1004014001a00d070384079100300c601e000118800750203c100b0103e09401c20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 769403354 1250 769402104 769402111
    0x2202070204090f0f0308070c02030c01082505040510020f210f0d06140904050606060a0207180507030e340b0c06151c06020d06080d211a09 61
    0x82d500d104000c00941c41c8806010100c0c002e0500d1800a903852a0041c03944400903c40010080c21014410043e2030000f82d50040580c242003901b49a41c07006414400904086050042200c0510780068840d403c0402807007542c2040c0c0e03c64411401015003a645c51000b011041d4199024221601041004c2014190b0441c038224140345044a0060750190542204a0282a0070b6880c03200300050341e003c01c20843d038036809032000e60040c0341c02d8071020340300d0b14010702060041d0400690369104030720902c03c6001620500004100700c210f407000c82d0005003c02c44500300403e1030080e0b00703004540001a00c0800084501215282640c6a01414004001c24040b40d0f018101c1c08008508200a08080c0252000500c000d00032480e11001001c4c61070a00400350b8000c103a46000e105503081500c940c2036000c0e0304000b0244e48d4244001c3e549000f42925880b805060055400c000005603006208030344070515001c0d81e041c1c5414050341c0804503188601314003600401e18403400b00d9070405000e135960 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 769404604 1250 769403354 769403359
    0xf07060209030c030718050a0915090203030d180515100b0a0e040603031d09060a0b0c031315080f06090106032d060e090a0320070f180b22020702 64
    0x1080c3c85403401084c41e00c5100c0c1c101642c40280b0b004016000584ca11800d03600005c2e80d8018020b040d0325444054581c040e1681e030b04000e0b40c48001e007006644007002150415070801c84104030f80c2800c005140d440081a2204480718002c400045400795030351800c240c015521000f142a1561802c1c244102d0360340040044400e0005c0c2d0958180141d90764480d80c801180284c8618a5240c00d0108003101e040c46c0640c0940302c0c00840c001d101d056214030143c0010b03100ba01800c50343c1c8188000c50145103024800042c55640f410403008640c030711018401e0840751216458014841d159400400390010045031060b800200007001000740510a0300640c0320940120340700300510094884070f9109601c4580c1800f02e6648810b001c002c14502e445481d51301035070090180180c1d12184d50000e01000f07a403c00083c18032080d602494951000303201d40340050101202c5c103e003042d0b842000440d00c10610500c0010140f03407401200301414800c00040f009201c040e21000d8455509103100025009103d050382c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 769405854 1250 769404604 769404613
    0xe0c0108010e0411130204092d09031124070201020306180703021e1b070506090415090203131101020c01020a2603041a07230a0507080d0605090702030f0706020903 72
    0x19442c0c558a5060020b9494880007682d80c5041c0300c800d00588180d070144003c80c4010b49c0d040032032031034000440290000350700f10100380c04066050403101b080500581903164060040f46030304000c02141c5d2080c0512002c50984215912420160300b00d0008480c519004030303a05654080941d000b01400b40e1003005800c0050401814003074031030100000c1012a400301c1000110a400a0200d00d49001e411600d04002c1c2a202d04000c003080b00350085d1010305001d60703140e06030205116821411403015002100045403286003a0031072484580c035001003903d4460486400000c00d51020403003241902040e001080c0d110010b0781c1d2070750781d08207003417142200811040619801d50382e0f00005602880c01400320201e80b25868404041e001405004101440452042030a5142e00160300c1e894860098184540714058107500351524440c5c068024000a0300040c0000610107a5001da402d4a5050b50000304c0c1d9903400310241c2c0d9920503070910b001d000304203220120004079150000c0180250140566 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 769407104 1250 769405854 769405883
    0x2070201120c0c0b1003110405130212060a050105060c0a0311010204090903180e010602100b010e130207060506060a05070f050f060c0a08090102190507111201020901030e0c0108010e04 81
    0xa504950304039500c80001542c030b0055205020850540b1354012041c078004c0c03c402440d55441901c801c240320074082c003d64850340050b43c841e03192808050015005080301c004526070307242081c1c486400b220000203843c901000410682015815103c4841740c0780300903d0303000c6c45903d054882d92810089840690740800003c80c0381040d90050044282c400d444102c015081c200705411681801e40041c06800c045000410001d5400182c040428a0342400000e032003030818012910000d000301c1954106090582d401100725242e0300622549011303020400c065203038401084254810f40c42002c002900501510011548003500140d01601c00d4045a004080c400c1e074413414100102c0301c803803131144045040c0c0f55998001c5102c41d07015092070021403078520340c5118004903818040d221410054007054941c104045014a26080600113000c0c2189480e41b200c010701079809500d0300303400a803c04035103180e028000640d680a05605859100c0705038244524402e00e40f100520a0b2803445030101007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 769408354 1250 769407104 769407137
    0xf0902061c0914100e01021e0d020f1b0c032109030106030b13030f02010507120c0e12030406181d0c120c04092f18031606090501050f070602070201 65
    0x443c03600140d0240034000b034101051000c803980c2407040700c0f40364010005401040403c25850241d0080c040c012034984480302c0082d0300a005010201c5488070b00002d0388081003a4100d1180c0020402c0011140c400043c0700038191a240c0c802803114954007000020103940001201608030340c2c1c405400098041d075642c0b50030443c1a020b4924031504000c0c41c090b0002c0c154050f021214a8200703000078070890512000050100c104280c03540440b51360740140c202810310801d151442904020612008040da5852840c0c4075400b40c86042c000c101c10a01c800000d1400c0303a0007000b19618001480e0b000b002036420108240c50081c02c41c82000e504000010020b078840c00e840303001790810380c001915107041031044800c031910040d0a100c009000340083c07418440e407255011259400107030840c1c80d00a00d03c900d11100884c44402c542c5405080b44001001440c056008111b031041da8604101c982e9440c010360302880f500200e02003000c010040702010410b40e070010001503206160100174100341c00c00c1e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 769409604 1250 769408354 769408373
    0x181a011d03070b12010e071209082106011e021f0b0a140306130803060d03140403050102070c0501030504150c052115010201020913050c0f0f0307030f0902061c09 71
    0x400101100400c2c04c1d41030f003808120b0a40500350f10040d01100742002c0e403018020195003482d41841585900800e010041800260740450300d007212842e0000140c0385042c1031500044581038005001e0310070306015401d41044600300c20409401824040040b1250070019541e9818601080c0e0346400840c4141d40b21b40070054020101f807903c20100401001c00c1601b009800744c4006c03645003010070f48501003143c440441e500228200d51344031440c88036107002d07128000311002038454000c000c20000b06202c410b4001f042601d01c1009414420350b2103a0054084410946000e85003128650032040551016800244115020300307019040010900100b00440183c2e0005403549203002c0911640f034102001071462940240001e508101041006c0781c0b2010101c0614000d4944400120b00c55110180071101c070307010075580040e40d5689a0078412a11341c016103541c000a86001080d600b22010391051207007003a8018003051402c0e0b414101644c2c1464920444100c1d00e5480d8403500004081c9030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 769410854 1250 769409604 769409609
    0x2a0d2102031e04031e0507081002092707082806030203010e0a02010522080a1407060e060d020a050c0f0f010f061809031103030907181a011d0307 64
    0xd004607511201e00207041d410542a98848540d02002e201c1440000d0324680c00818181a806100e81210b4a90800c4c41c40c1c440194003801c468020840c0d002220b103803d800526840c4001d403000c00c00c0a81144820b23554000c03185601c989200c900c800724660390b00c142903043c0c0141041e10407031451100880350f90301540c480380c0b0003403685a03111030400031400c4c00c0c0604000c20f43c892003c0c2c803500c0e40755000030300540320740c4100c1844c00029104c0703440b00400000300712018002c1001101d1000701c03640350400700d0300c21410035450180b0375807000061040c424005400b5a04016258504040140f886540650040b002100078401d0074000019080e10821102c081c10300500024404042e00d0460542103c00042c20691442e05081c01400403c486400003102140820700000c1c0303040340390801300d0341d80c1c0e003000150405000010030f00c8221080001c2d810192114055641040394840929004a4100248901600f51351120011140d8022a4481c9041c1101042000f20000403c002810640d958 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 769412104 1250 769410854 769410857
    0x1081b0105040312090e24040c14070f0512040803190905060a18050f010504050607020f09042609010c020d1401090c080c0a06080411130c0e032a0d21 66
    0x103081041211b45914003540c0000400c9119200300c290842c0e51003818104640c114091900c981ca4084214440d0120400640a901d0f4158481905203058856085c01003000d458a115000c0911050240c1d54111400c1b10300520045151003102e0001d0071341211041181001e10a4403a000940c5464100c018041e44019645200e8a036404291012511081ea00a1801801641d2501d01035982000445081c1c46044600076190308032440040d99003000031002e01d401c514100180010031442d805090000c20212000d2100b0950a600c00c80143c0510301c0201d000452403010f036409414450541003200c2e002d844100fa00d8803600242c6400c0d40c112640860b044488400200000141400311410403c01151100f0320320349825401051074402420103090080054000c880382d07038507285900c2103a803041030188200701901c00050800c50030803407018064007448003030030403c910710140c0310303002d000f40d40c2107401c03107041c0b501401646142000304494a10030400240c44181c0d0b0007a40c2c00c4100c00a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 769413354 1250 769412104 769412117
    0x7150203030708011e03021e1c050613110d030e1c14060403051c060531051902070312022a012c010b090126030301081b0105040312 58
    0x5602e0050114405900841030883c0155200b8200140030038180100c90b0103d032400c40300c680f100841500400341500700c6034040c4282c1410b1051410700e9210115940c014001d407246a918100e0071128201130402c000c00400380010031244915180f090161074901a103020b9101d4030400300070819002800318600884000e60040c07400f005110340c84030016054803400b03050103007419035020346203011b2610b04030700d100400740c203015280b1f0070713a40b01d80001d05000307214041c60402c400c00346600d17400c0d186800403016581a003c000402d054001c00b80981e5070a0102c281c5c40c5802440d180094001a20440c100400c26134a40940c005900180c1440b40d0440350380a409400003610b80f10f2020b240301103a00d0f99050040114001c5040050b0545411f41c6022580456209240d06401840800205544048404000f00b124200003a0b201d6400f00d1000b80c00a40b51403000096940f0b0200f40300d0980f260340300117150f20b090031004150059584040c10002d00706a140d9803000040710460071001e000804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 769414604 1250 769413354 769413361
    0x70204150f090902060a03051f06030903200709240902030603010c02120909040c12120206070518150c07090c0206060a03021c0c09060e090d0e060301170715020303 72
    0x20300318154030040042d008100542c00d6254041021405120402c5051541e82c1c2d00180103e031552002c803002e087c922020f01c1c56903031601d801400902040c0b8065000030a080072510700e11403210038151940c84e491004015a0b80f4114821020704070100e011044910342031080308081f4460b5000b040605280c400160702da1904070281400c68a20204043c01c44d4048040002076103608000c60740d080c84103607065011580c90f420314008414040d0300040c10940f404000c4014024407014030310107c038066003651269100c01204550a016481400c400c0c1300000c0b02090351403804036a20100c42e809600e4503802e055201100c242040030942c42400825140c3c0034150000744d05001c0c0681c8a03c0440d0003160241c11a004031b41e10b1400801c04a00f840700c481615802d01200740340c0c1400a04000748144007d541b02c02110070b5003c070903120b02e8000d20491030303010240c5004205003c620100541010f042da031810360300d944e500551000c0c0303a041e0300809001007100e807031498400c003d0400c1500155524107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 769415854 1250 769414604 769414619
    0x61b010c030209060712032304050706090f0e22080a030609060b04090e0111030a0e070e0702060f0709081c08063f010c020606030f060910090807020415 67
    0x2410a0000e204161040210101d00c0e81c0e20001d031440307660840448451060070f41803e40c010701d1030108003500c460a50821464500301c1c12861480355206070306503080a43d8070541510500c000340580c86030456902814081c00440c190600e5108664001003d8007548890801c480a000c041e02900c8440001407281c070031070341500071400107220300c980402c812440d10410005c0c60090b40100d041454503000c41d81007503c400d4020002043c80b440c40f596803030400d408008010242c3c903404041d20b0013074a00c00283d0104440602c0e01c039100b190040c0032195205c1043c1e011500008000005108600c000810840c0c0e04101144040705101030303244180c4070808000d803650400402252240c09a80c45191312801b091010001021000039400e42c681031501f4031080c195103a40180307040d503180a0703409203100e500148442c0203050a406070381e12100c2c40d55000d80c4034a41118000e0150307006580c004c0040080c1d9000d40c504a01400c1c0c07030b900300655540081d0985004029a0890070421002401a036 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 769417104 1250 769415854 769415861
    0x204061a041505070c0905040809040f020d110702030a022701080114010b3c0d05060f0a1a1c050f040c0906030f15090f050105040b06010305060d14010b061b01 70
    0xb4502c904201d0f0401c10180c1c0c4080389a00140a0030344000d445002060400a006055a2500c0801841071028403403102c207080c025040ba140f0b2040103420007a9241c071180c1075804540741ca40d0040e01401c0d05112030307000d100103840340e06c00c2d0543c084082c81c800e001030031444a03501e0203040ba503000410082c4201701401485c0c01c046c1c0040042d14020000c3d041307080c4419492030000f8104ca4070035a82c00c021011814488890204140c2c15040001042c6030295819403001e40b10b0307802141e03556216403181042c84928481c0303001d0103210000c410480980c14a2400240142c40c0f4520621001c003401102d43e14150344040c2e07560071552100400344810000644a100d000d07181e4000c042150700d2450f02c5022903084c0401d8003a1003940700315285030081d0040c1c1c00c110000c61300071070711b50382c1384a0038a4194020300703041750243c0d40c003520311001c9001c1f58841e010f068040c0d00010700c2c14480c0c000036115200c00c01c1c46820450155940c4569404072621480040d1081c0b281d212000321102d41c3c05010070b801e6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 769418354 1250 769417104 769417139
    0x4051f0b040b06090102060a0e030d0e01060807090908040603180c030501050403172a0912100b0411040501051821010e03040b04062007121a070509010c0204061a04 72
    0x7852013070104800c1c1e03076400640c07070781e202050031b40108000103607450950461241050242c4c2e00e505010182106c010150001c2c8102c81580d021140e000e940ca056840840751040001072001c00c0c01c21041000602c01d411456612a03d14460f8103108060350f101400c14619600444031079440720100700504d078108801d11403c14000da8014000c0c6440700303c0b03c1c0d001342d225400e0a80d0083c041c0c0007005001c900c10503501120805807000172a25010103590b40d07500180103944007454285100d102c1c6908040c0554440d900142e643c8a081505080055607190499180034841c1020707280144d5007a130350b190400700408074010801078105610700c001401d441c19200d000240fa80100003c0044078050310440d002c03218140381c140440201c40a44619009030a4001025485998000701d003010301c2807440301c0b2182c820880b41e4065070b111440d070040071000320790707820114005020300182940a11140c03074416200610000c0c15039110000a003039801c050103001c40d00c0a012805005154090404454 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 769419604 1250 769418354 769418359
    0x140703180507060c0302070e0117100c090603051503150703180f08030402030a0b0c0405010f0206071706060c1f06050102060411150c0d0309061a0a03060504051f0b040b 74
    0x140c6480548605581e8000d0740700e060200019421900103040c800d02c0711402801e5501030f480c1d030b6035a441000a92038400946070b481c00d4010000080700108007846400300c00c000940b618407081f450603400f40d0089c40020809009d81c529403080b68129a01408003512180c022890700d85a8205140300408980100b05815104d4541004110129801c4501c0d070780195404140c1690300c0d510751021a0a00282240051598014600f403121403a2080e01030819a00d0a0707030de5000a4111170744c100d0f13030b51606a0303e0001003000b4020f0304200c0790451441c9035200a000d81090300d0304541820544c6041c0340b080c44160881c440c2c9001120b07070201c40c080d402c010642403000301010300b401c0d10f44600c09402c0c01d4415103d94801d00c645052004820113407004450721102b500c4a028a000018002e00a00281247c000d89405501162415016030800c011a8058070440c1d586003943e0b9114018400900151a50f1081d8141c05071408640142b9a42d030240c05580851440c1d4400e05020030f40b100c1d400b0891 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 769420854 1250 769419604 769419641
    0xf05160506010f230607050a080309070503210d051510090905130b0c0a020a06090515090118020607020f0306070504090b1509010825171003031407030909140703 71
    0xd04d030002c090052040280221102662444a40f034210715207144540018408030b40070041082c0d010780030620310300b114001c0d01554803800d1075114101045481c1e48010700c00090900080318070350759551101c6da101a54195005d180c240e0500009c0c160302c480d04a020009266100038003150105008050b0050510309461284995980c2c6080d4461001031450903031040100c1c4210f1403c1c800c2114401040d00700d4800c1140000906003280c44d62624022609600034840200740240414440c003420340c1c00d00500105141007070360801400b640803100507079200c000448a901c0954040c81458014006503c0f0103580f540741c03204003000d543c070203900c451150002800c090000c28000f411201010424640420983d407400c2119203e0030516504c05460441c0c0310141d2340b040c1d04161810400003840d400d1800c03c8d0b030f4110240c6110080c074040100040c0c030801c8040c0394903c0006c00750030254440d003001004030b80c42c0c4030741101312600c1141d40c02e0740713201040600200703641601c100000707070071545080c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 769422104 1250 769420854 769420889
    0x3010f08072309280207030f0809071503020d02030f060310110906161202060a0b190e040c17010b090f040b1801110d0b011103190f05160506010f 64
    0x11404540d61100e2580641c050380e0010f0000741d45404400508841c00e0104601c000e4085503000080d000508200d0202c0c083c41c800c000c0e114001c04440f072250707110300020030bc82801c04030b14041d10b0118030101001d254007072004100d60155030000d10722990320003498001c075142c003070101450800340030301e80521240b608802401040340d078402c48032541829a400f03990b480d17896062104400c60b941026000c0048500c2200456901103541800380c1360003c4140300c0710220800304038828080400309541d04000000401c201d1520005c2c090f80907005540942c9080d565981d200e00000c180b425040d03140e55503459542e140c2c5403054000c0d411556625203100140781595401e01d21840103420310741000380c00148940d44403c25000010442284440f00d41c179045414058805811402c0c3d000d40440c08803103000580c40000410b81d941c00000701000e00841038819800d039010b2100007250010060100000e00c14980349003207607114148128000c2041d50b1410b000c0392034556903508180c0107503800c240c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 769423354 1250 769422104 769422149
    0x4020c0d0f140f03101d06042003042a0803030a0f02030c0717191110022a0109021c03030c0206060a031e0c0e0912070206030411120303010f0807 64
    0x96a10303040a240f0441d0b640d40316600c129090030300d1540030420f000002019051800d20300645d0038001c24060700c05201c001652001c6c2c06003003150f00a1080800c2d403d000160100700c200d4140303000c1814000e5092009600140056035181c869044031406500c0001440b003401403500c41d00da0128a101007c6003903090840f19400d840c401c2e80c9010f050a51020004a40c80f684d26040315001440200030340b186a05a80c009047c040b134508a9502a004031482e10b51200c846000b118180d40ca441a1100011a03044403003038402441d1104400f207660360701f9681c1c0184c541c44111170b403040783c041c25102d00030300c2440c005040e603070b20080080c01c540080c030a00a45480f20038540e026280e0241c9600c0c442584e1209c5094018542c060251003030742070706000504890b407011961b01a11096042d6402400201607005491003030050094100c2c0080000401044014801903d12100200b50185141e00c0e4a000c41c80c0d0b40003a0031840580702c034000c0400182908020543c02409a45841c03442006000350 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 769424460 1106 769423354 769423357
    0xe0d1107080106030201080402150d050a0b0f0a06080615121e10030305040e06120a03030c030c0806062508121605030411041a04020c0d0f14 62
    0x801040c10320301806004243d0740c042e19031f11841c2e100ca23070a10007100c03102c2110044804082c000c04841c030170103008240c0144132051003c6074000d207103020450300c200780382400c2d48200740700c42e001c001440c0c00c4011030303902541c201d80008800c02d00302e03804100f03440380160103005400a00e0420850f001d154090344906040e05448007440ea0314000c00304040c40c2640000380200e40e05100030450207210080041d4080d4010341070a180030070440d0340c2882d0203038640c4c04502190b2208003007550150301d8030400d1510718072403034514010f00f802001f00300540318955496044ca6131006944400102e41c5480404140d804003120755590b401c14208822a075058030b030f8101d50501d00c515201a644510141d90007203400c081c11501076070300350381004002c180d41c648044d141504031049984994132440900b840366420300240044416012009250b081081e150000f0300200864024144c9000d40 = true := by decide +kernel

theorem cover : BRFrame.Cov 769244604 769424460 := by
  have h0 := BRFrame.cov_init 769244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 769244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 769244604 ≤ n) (h2 : n < 769424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
