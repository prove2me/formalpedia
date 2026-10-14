-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1244
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:57:28.870099+00:00
-- url     : https://prove2.me/submissions/d68f652e-85a3-4122-8720-3358afe1d82c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 223561151 ≤ n < 223741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 223562401 1250 223561151 223561159
    0xf070c05060316030207020a150e012c060f090409030305090d08010612020703020c0312040305160302030c06030613051f0b090906090c0d020406020106050906040c120222091a 77
    0x1403800c039a49200243d0480100d42c03c15034002008030441d03a580901030b000d0281c840c22180e004211281c003600300340e095205580842d441c2c0000c41d4000341d00c4028a5101440b00c528002140619014010160484a42914551814441e554043d2a107104e9414018040e5901240900304402441d04110018007014100849000180240c940004000c01c02480300d4800603510ba400d410200c1c10408081d00f0107a06001e40e41281d008150740304080e0003607a000e41d0568584a03900d1104503411ba03440d200003900368206140420341464060003542e0322070006413000e508100c13582c804004840e01214030010341388808140d50703490019886d09101402000b0720303c40c41e0005410000d001101c0061025100e0043d003c00108000c1143e002e450681c201075100755150f940b80c00b0081e020b040b541c01030501404c02d046c0094414070700b0340201a52030345c0c5620707244000412802d20802035407040640c0300b10f03c106008030a90006400c032540f802040014000140510807400900ba06d11000300f1391441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 223563651 1250 223562401 223562407
    0x315070228061a0a050f0612010b0307110f070b0307030f02160b060612040206072a030201080601082403010e070e090106061115130b070f080c041a070f02060f070c0506 74
    0x89a00c401000d1805c2e11000c41d0250b003e490039200250b56031103079580b84d034200e01c2d401c3c000041074202c2001a601801b4a500d640c44162440c42c581652034000d0310368207207036500c4080c007000500000d800860300b2101616011900d81d032901500f2060368130000c2c20101c80400707058040140030040403202c1d080301080352131510303050700302c2c41100c01c2c0c10000e04041d210740f00000e100001c000040000c1007244041a40d080400c2401c00e85c14008009a80702c2640802c218400091941d0303c82e0030010701c5000c1c02c5004402410713299035901b10081c152240c05e078140d0340c0c0340340d100d0f2194010040c0b04004c20305503507e090986024985135003503074501d0307014000b8401c148001404024010580784501c0c0c04184c54508107507549200710036140040d10018160305034900602000f00c5e8405801c0c80540c016407100ca10544604518621a110710700c10780f1039400c051003c0c0c03210000d80c03800505451b4000c0e41d92810001035500041c1c080c0c0d00070701503603980e04800101c4904124859904000802e821681141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 223564901 1250 223563651 223563701
    0x702010c05070201050c07050d030809010f0605060a030b040b0604180b0a14010f032c0c09040506011205120d0204051302070c180207051029031507022806 68
    0x414003942ca0002e0500501050146003003070100a07001c0100030041200c8008481c6040c003030808201503440760450750914240000f110050700800044810180600340f13000c001d00d40c02c034000c02d0103051071980103848021a1700542d44c1c0c4006000903086101502030400403420b070700b104803a0712036501805001590410880c05459190700008090282041c0c490710003000800c5008081204003800e9041800c402d40602d1610200050442912641101e003985c00c0c00e401c0280205040318000e055500c17010040c440c43d11100710011009110f9011078100c441e030401c0b01d03011a0409144595069408074081081b440c19a10031107449400e104111310385103054451505032011402003890760001d01048481103411681202c40854101007510000d00c1c4628009010b0448129940c0d07d4420364900303200100922441c00600050080042050210145000f052140010059401c1d8000d0400741d108030040800c41074034610b4600c800c818007026034501007084610030b00242407051500a0014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 223566151 1250 223564901 223564907
    0x60b18060f03280c0b0a09030b010816140109080609060f0c0708030a0c05091e041a06070b04140703052b1706060c1b040516091502030915090103050702010c 69
    0x40c3d14185903001402c2a1a160800021400361540034641c81a80018030600443d40f1030354900c26684604c81c65102e690342c0d1035156030348117041503c01c8081010880c0411140f03490310743d80c80d00c8200604000c0e0311180c1e50012581401c1c0101c0d1803e081d40c111804000030900c0540b11a0380c0001000105400c042c500d0b01d600c106400010080c0985996030156000c02d2030188080d40c0d1240d4008001c2844103890204030503164100f500b41034003442c1040c00d0501e80c1d2984002c1b017201c10f40e010f410700742041c40c11b480f85001410050425114507810b009034586424051241c00055401440240300261035810f159042c400d60354206985030f0501d1402d00105035101008900c8404404400d00c5903840c1c400010740c1501c208903104090380b02e9140c088400f41d4050002c003076000750854080019603680d5034a4440740c03140c0a8402c00140c110101440300c084070052a2502a00728070440781860f0105c0e000c1002071588010b000c1034a400459841c020b03680c1402096030201c440d10003880403680004000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 223567401 1250 223566151 223566193
    0x1302092b030c0218040311150106020c040b04060e090d020c04330b190201050a0902010206070503040c0503010906060302040f0e191b06090f0902030601020303070c060b18060f03 78
    0x41c10401d40c5800e503000c1d562041403e0740c4c1c9a22508900406081528000e4401e401c1103041041074041c40500d8860310b100954031b68129001c90b0083c01c000300c2d800007040300070070010042e04c0e4040d6070703a00003044200050302c03054461500074004241c401c0000c00c0c00f82c540000c5031790a621950421403c00a012140008460303228907035080880c0010502641a6040e54075410903818a040801c9058070001c42e035000d903200c1c3c0031301d800030805611244c840c01c0507940c640002a026a000b0004141058429402903a1041c01100d400c044251240d0000c1c0c00c1d929035460070764510362a00c50a0003546880d200d0030080150f01503040118420070f9400380e4990108864012b1034074041c52003481401048100740010480307130310300504501d8940350003400031450f6006486003528480404a004030b44c41c400c0b0703802003005030019030942c0d07503c02c01210078111410b012100310392209941200c503202d5207041ca03d05410f40b00503000501d0070809000e9200309070708006209a000007c41e81800c2500404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 223568651 1250 223567401 223567403
    0x615081b0d0807150605010e0109080d050307120c0903020f010305040b06060906160606081c120b040603122c06071106040512150f0610110c1302092b 66
    0x2050398035218240b040c140d00500e44080c1c074030025004058810340f840d901000544074242c8901c0e030788181440045030a00d4160155609561004c1e07205d40040340108051548826240b8200f0301d5000d03020140780c2685e22400d007440124001580a01c00c61501c9181080c04800030b00e010040b030728154484240100c006000c2030f004180c00a04460a900e40204466032050481082d540d8900e1500e4204010300e41486060103500a441548203910516441d050080340340d81d440c08204000400c40b00010320104403071030361103584d0f4140000000e2304404038941d414200e45030703030800c1c0d04800c1681d131110a004501e55402d00007900480072550b02c1c641542c5105401c01d0100c0c1d0b0100408012400c2449a034000d1540a40305030b07e1103690640004445031400c403202c074440321544807412a0ba00d8410700341d411703540c49424841002c5a0b10b104d015031130783d007a04100840c1d42603521000820741c0c0d020314025042c01640c0002e00d0640c00d00b8014900b4648119041c4400480e4040150264140d411400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 223569901 1250 223568651 223568659
    0xc060e060a08070203160503040f060512010614090a030602280909020706063302031312020406031203090303140105011b06020c01050a0506011d01092904030615081b 73
    0x3c201294804c10a0700c9041c02206002800f8055604216540f50080c2c450890fa1a05180020440a1180d000d840d500c4808200302c4603d6400c0c402c0031342d130320b0408c04810741c00b4140900015240d50340301030a0b10010340c00342500507a01c51900a00305000d44c0e40c050110800c1e50000a0114415444200481141e110420052701e482151800d280945000c2e400710917a5040d40024185070385000c5804036401d41c100f90100c1c03502d4142441a6120701a200c69200403488600d0100f08002c00e91429204143c8000d000007001d0b0340384d40c0d0360b007800d4038030b0800100001e584586047c00c0540510480c5807031648001c202001e585800002022283c100314540e1110200d1804442000840d80641d07008114007c02444146010b034038540040c13400301d0355280090b12a08561101c0032000c000f00c002c0482c103035980e030340079803c3ca14265104c80220001c0807801602c046004d034581e2104014002440c825500030442c8042c8146c1d82e03000030800e0b0044d142e01e070050503014503400c00030305075407580e40803e0b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 223571151 1250 223569901 223569917
    0x307050903010906020a091806030f020f030a051005090c01050705062e0e040c0b070b010b0a051b0609012304030c0c1d061219020f04090210020a0c060e060a 69
    0x40c000c603001d8040c002d80200141c1c000302d1190015500040c041c02a101c0040d0601d00e07010410301540c2c140d030554407000e000c441203400c02e0405402c1844000506400242c11280b000640f9034500b4a031807030190003030307031800e40c0c440c180586a2000c2c008042c1c1c00509281a509002d002c1e299541c076140701034040400903806482c00c840240b022070200d00383d0005a80205459907681c000d0392031443c4115011100301501c000040368012404065541070398002c41d0000190b8203108041402e5400103600f9401c0c0a0300b44803803030b040602c90402070746454030301c0080c0a01d400c040302401c2c29101040d9540d201d40794079100c80012400520122a409a0540b40400b8140103d05011410500790b400020100a0300c0303000da0b079251013480c0482e000e21403d4642d0b000400340c2103155600e1340000c0c00020028469440e500380545050003036456070b260f000f440003455004581c00100500c07240881980503800400e1580f050104840802c2c004112604018185001c90750000f9518401d580c01e0005205042c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 223572401 1250 223571151 223571167
    0x90105030a020f0f0d140c0108060a030809012001020403060204080115030f0308060105191d010203031e0c0f0a1709070605040b031f0f0f091a0d1104230f010803030705 74
    0xd8118081400c0c1c01c1b04480c00d000c000404140d4035980c95061940c0850940c9c0013046840c00c15400441c2100d401c8003480303040000f40b400446a402c0040e40d9080d0b00c46182440c004c82c07410070710040c40214032a030001070b5507a180003074003806e64005000d40040d019000f803040010502240c80d00d02d00c964540b404146940d030300c20041e9503502880548000d5904001d0b42d90080681100c004940031455000d40f051202e00b1a0049070340f40b008584034480108408588100044880074040d007116900e04400d0501740c0301c03482c20303040c1d80080480500040c1e04528450141801e41902500014100e01500d506030800c00058551700c11482104c2c103001e00000000c5854024041a4100b03525000c06403010941d620090355040f0090701034019441515107000070070303004900c0f4030090001880d0203051280d010b0360422101c1d907100c0f002034605180c005d14580056486210304a51504a1002003504032249043e0443c0c107000140071001c44050080140070303140d40082681d078090354a00e400350340c0d1641 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 223573651 1250 223572401 223572409
    0xb040204030809060a05120f1504270807050303040507030318050a0329040c081015060c0f0807060f0e01050910050714070819050f041203090b1602090105030a020f0f 73
    0x20740b607900111130858405000780040c6098149004800c02c1d40c14240d9180b03040304101c22039800c0038003802e14a41c00c4050440b4a00d48bd81d041c0b4900340034004545c285040c1d52038075401e40d07008440445442d000028140300301074114a410010a4180003c440381906050210300c8110071400090042d00b2400e804100c2c0b0006100c0342c522890700900500447e0038646803c0131480030900038010a40122504a11249003600c261141c44a07800002c11155207020300035202101513900c141c85254082e0210300115408800405d201e134450100000e985c0c211200b0031086495051540d58140d042100707010181d280001d003202da0001032040001c1c16201d2600c203640403d8404200348000101089580030301c800301c005030103045481d80c80c0c2c0041c0aa0000b04440510030401103003200c1201384030a01c00d40c007201001d02d4540d403003418000001c54542c079441c00d5607003102d112009805010700c805411030809105590042000f6001080301406076800218541d03403081b11180100d0413014203181d9695 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 223574901 1250 223573651 223573657
    0xe0112020406080a0605150103091112032119060e07200a03020f0f0105040b0a0f060902030a0207020111010203060109120f020405040b0108011505060a0e030f100606030b040204030809060a05 84
    0x1100104444034103c0c02e05d0f0400180c44200c80604129004215000541d40280115014990f21004e0014000090020440343c01c5c081c0494a07000d200074010100c000305140780814011021780725011052400c10f440701c07200302c8110709884078581040000c0112504403850703650082e075681000e091403810400b41c840c403500d0050410940744985030b54503040c9500410395041119588043e45d249050305511542628800d5400030580590000029400400b070750080002c04134685010072183d5540a081003070740c00903121098404d42c002041030456030011402c101c81203c0400071342c1146030800019000e0f4440d0321506105410101c000d508020501c105803200715801042040076081900742131101d032009008e42c820544c40c0555400c2c0061170550f0100c100e4200900c260b2400c076603080c04841c41d11005864035050700c00c881000200380740a1010b45442c841e03110300000c80030b1030094018103684c510b01c81e9a0107244100310510126510004507800b0000030342c0d2040d60703814070110454080c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 223576151 1250 223574901 223574909
    0x809011103190b0d0f1203020702190e1f050d020307150809060f0108030706020a21020d1a031009050721021f120b0a0b0705030309070f0e0112020406 66
    0x4000000300661458040c1e07030030090085a10b0108120001c030001d0040090700110041e010020a001000005207108160000601c5a1a000d4100031403603003c1403140c2014039041d031310a4440c800510646040c040f01a90241d10f28007442094002d00d40c29421801c1c040c005c2d01d00a2801c42c2250303040d52420080c1100800d860f85040c010321044410040c190101912040c00741d001d4800460720080000d070754181039501e030340080c40c91f2181c07640da1000290f01800101e8140898156481c0e4151095800728184811078000580c0d90b42644001a0807104c039a40080c1c035800f000d02d0f55408a403000a5011154442e649001600c0ad0442c103000d441c0280c1c036442910012500300607031010030810401200d02e0b51003611030081408040800200411214424000103482c1c0d1406040c5159143c03c485502c3c40090804050103448282a140c90303030004909032416400002440044c0402300700f000000d1441e030901040b002d003031408108400d04107210f96080b075016202e19070150342d0780c2e41c8000010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 223577401 1250 223576151 223576181
    0xc060a020a0e09040308010b07060f0f14010602010606080f1e0903090118050d02040c1e17090c0d0b06061b010509060106030e100218040c09080708011a01080901 71
    0x1864084104006503005007144800078006032032046141c1000e0190500a550503210f08003541c0c01c02100500d15089082c050300c1003511950f150711491102d00c02c0c01c91036216104082110290b254280a4001040c1d1100e001c5a1506c1c001700003060740401c000b41c1040400460418988465074501c2c0c210f0303078102d840721900d00d56806100a0003130000040000c00c0b82a207491a2032442488014a030355007a1194a80200303290640c0d0005240552180307403680c000741400c090290300c440304003060001c1d603c902c4000c04c69030b803881012402082e9055500c491000010801000384002241d0036aa0184004041c84007102c0805c00e9a51203005540940700c3c1604060840c4005c070868a000e00030030307100d8050038000c0fa000400c50358841e01420035220803a900a0005181d0200080c0c02540016989039040e82c0744c140d0062030703070707624003404443c210540d03298903009003414825821700b81c450b0300c42441a0b01d07080712000c80402c2401c0380e4000e100b090030714240e00d035100801c2c0e6000d00002e840780025 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 223578651 1250 223577401 223577413
    0x120a0507061106010e060112020a1116050405130206191725020f0736021b0a0b01050d030e030708010606020708030405060405151e0730140c 62
    0x2450380101c2c802904a226011503019903a500710400c0b41d210306840180c00a4074403e506004400160020640b074442407601c030303600c08400c014003401c203c045202d401c1501d540a900300440d00d0301d4016075810410b43c80440070052116030000300c880c0f10b9200b541040c04007100318221445c0c01400da00d072415035070a1110255182080306042446422190884544850348044442c148005081c1c002e41c011200104031440c2007401d5100400014455090407a00c0c041c6087c0d0002c0916004041c501081c51016032526003000f0301e0760200c0007006510f8060392103440041c0115496001c11411144180c9142800e41d00d03c0c242101d4950300100d0f0180c151240d52000110340905504c18000c40342c5035401e96a0403626a1200d9490388124402c8981c8031030144418490761514840346001c80081d030418500d0b10b407510080740685103022035a440640c0020404c10700740944445d02c0d010022944079001003582c80f0380a4025aa081400040708010400030b022800340744e03510454202428403004c8540c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 223579901 1250 223578651 223578659
    0x403030507080a181b0503070b040e0702060f040b0402060705010518011b08191811010905040618090201110a05060603100203010b0409090c1d060a080d020a02120a0507 74
    0x506010384075900051012000104845028480d62124413200c00c0138201c03d40309038640c0c8442004592500310104010400041c0b655820080c00000700301408441d5203032032070701238200140b450003013010095401110402c15400c1c2041c44065001d90320089007022038680b8000701d411f0340100213000b4402d40c03a141c140002c02000c400d0b240c985101d9080240b182000d0300294282ca803005000c007101181407070020501121011902e000d6422241800007421080c1a00d44907445c142d0b44000d40d0103035280321182d46c141d60701110f180041c1c601603600744100f80c500155466142e1421102c030f0303011540d4080d910216031240d00c0c01005c4000510440e02c0504941c14050b441e4001501c80500c6031103008000c541d4842c05000b40c82c1240d04000050382040d140c410840090980070600b1030321081001c20102d00c40003a80008901001c1c0702c0d580100700c0c60321005100410f21a5041800168403400d87c0307182095000884c7e400c03442c0d059484d408007202c0300e03502d54544050400014564015080007007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 223581151 1250 223579901 223579907
    0x1b0c0603010b070c050a05060706181a0f090601030807020d05070b040b040e060405040b0115020a052a010e13151203050a02150f040821070908121303061d01050403 72
    0x101c00d543c0104e0041c401c40e40d8400c200701d481011031240c03d40005061040a000c80c46c1a40007460150030200c0049082c40142c2d59041c10b4400c00d03040c00505130240c014006011744070340446a1165111004020035415601c40101a0050420013440b54412540c0c500030040c0c1804041c009210807800c0c540c8030350720b5140802d00f64106028041b0b420420500149040c9054041d46000c1c41d0040c07900d6480381d0901ca050811030070003410704030562141000070400203000b040020280c1c4100380409084504800c2106003400503088001d04100c40c03204580300644d91200c4103910300d88120800500441c80c0800c1c614550b0207035000c0f1401c40000c03900d810074160807034002d0120301e07419800c2d903041d140454403211200f10701356103802c03c0000c2074001400155000004100848084051811020100101e101300b85401c07104900010078028040280400422501c1038442940781c5660920150a8190408440900c400b40c1041c5c0ca07258032030601d21a03030a00032940c1611000074071061606080213 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 223582401 1250 223581151 223581157
    0x70506030406111b0c030c03010b150c1e0a331a060c01060f0605070c0308070f020402130f060f080c03071709010203060108010e01060813080c070f05120303010b1b0c0603010b 77
    0x701b4000d018040741a0b01c00d01c0c0600c10a80049801031103004d10300000110b20301c0e80e030800305240b40c0f80d11901c50a1700f003003e4014011008400301781c0040647c1c00d0a460020420403d401c00001c1004445c0760300320032102000c3c10302c05030391525500014020381c81c13140d0100607440c6203140d40d002040000c0d9841004410341021043c0e812140091a0b42076440c141100e0501c101000a40080007100003407002921640041c0800ca0150421a2012215030009812684030710a100031101c040c0c0301c100301c215140800c2030003c007600c0c10903402d000c0101d0806840d41030010050545217a0000c0040e1007140168844800c812010000003a2480d04002c2c81307000390b000b550028040380400000084101e064400c00341030303d400790f40e030f2000b64903468040240400346034001c03a1120f8040c0300c0f00c0449881003040310000c22005101e0700c403480c41c00d4144031710a129406c244809400400c014404101c0c002d00700c0e41c0e41c01941c0900b101e200110304a00d810a41d10007a010f40c08800000009002c005513000703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 223583651 1250 223582401 223582423
    0x1805060f01050d05070303030216080d020714011517240714090112050a090501020a0903060b0a0609050603040c03151e05090601120c0e04030302071202070506030406111b 75
    0x4402240e0b40c0396010000c1d1502c51450080182e0b103d03480510000f4840d8020300f0b102c0e40d80341c10f8251b001e000c5940b0a90180c214000342d5030a0783c0e0102d080010f00c00441021501c40c1d89520013001640140740301c030940c0d020103000d0540010258200c04a150504000c03440602001041000070400410588a4034000546420b000203810b80780340e00c046400b08013121000141611034003402c144000303404001d4100109895110742d80d0b4000403010440070b000921149096a950003060303800c5150840455288084641c090070085406100003500a80c05000782c844c11504141c80390344a203840d850010840d0001480201c0680c4441c600c0c1100ba0070159452071030b4640c01c1c1e415903820a402049035800c46480b44c007a4403100041180f40c0c00c0c08000403c442c000c460843d400c43c0c50700c4410301a24400c0c0d4007200000c0e80000c0b10010300111715040d002407034680c130150121a1030031000031320328000644040d10055a842141100c805004100c5858040d10380e80070003c0c9566005007501e039100589 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 223584901 1250 223583651 223583671
    0x90a02010f020303010503030a140c0a03050a030c0302030c0d0b120312010608011d180109320d0c030e0409231e0703080a0201150311040f050106080712180506 70
    0x100c41c00e0114008020b89050740c6d0082c00035414210303455800c90304010080d01058444100b0000c0160302030b8203105510501e4045c0d21503d940340c00c0e085008040b50254081138042602c184144000d5580d02011150a100700640103e2140110400a9250300d122007022034207110004000c0303200703514101c5e581d0480f60f060300c801c21180c1ea560301031111000040d00c0280103006040000e0507441030249003100440c0400c00010f001e180039a00d0003400d4021078503a0f510500b83c084444030541401810403101000340000e00304242d00700401600e0500540070040600010040c014215103803030388092802c580045070404160200208142981c610a554030b1007806080c0c00c080000000c06921500c429501300117080035855616071641c42e400c8000758100f155201c0e00140185201d28024002a500071541901483c00010400081b5880d05610151031418003004100103a008040a035029132a418075801603806510041d0007800102c41e0485228444000320050000000d0903d1041011130703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 223586151 1250 223584901 223584917
    0x50d0e0609060706110f0c07091d030d020a03020d02070803060f030c010f050304020d06060602030c10050f0403120609060602030c061308031305010608060c0d18030905150d0203090a0201 82
    0x280403861003090031042e040304080155000141c03040d03015400c80802945241d04000e03282c1c0c40e01ea0381c0e6000c403003020010f07800114103220b0b0405034401c40301ca1601441490410721500440140c507401203062520b01c1d1a408118a801603000783c04a4a00c0464144110354412080c90000b40f10b030001e031903050003200c0004d481039140c200082c00c43c0399007805842d00c01c1c0240910344100c13000c3d400104100c0c0c0007840303d11100006a064000e180241500c1d0b00a1030311f888594001603d070159403803006090909080c01c3c00306521900003103d0704190107180c84601f0500340220000a8060703503000c98191850410000b41041e0b003c40501840b042c03c80c252040e039180d881e2100c20030302221402a080960030000700300306051000003800054410400841d04a650f18480d81c1016412207402420707020004910142000c1440b035498940c5114100a4101c001c0e900d0040a0011034002c0030b0140b00d0f24000a440b0041c1da030f0039100d60720311181040d076907407070801c9040d41c60b140d050710304034007045d145 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 223587401 1250 223586151 223586177
    0xa050c070611160513090f080307030e0607030510050904331a032d010c080f010b0c07060509041509021201120803071b050f070303120621051504050d 66
    0x103c1180c00854000030030014103c0d0701401c194000b8101d4601c1120001c16103c00240040c00c000e024601c01c44c2030340c0300000e01c03804c1500310b0b505141000b00840101031401040241191601c2440c10903100c05440c074500380c2c0c3d100d192404942d020b00d1b80400c12000c210520b001d914040d0100ca03c559903001c00c007030110411018103a00c02000181c48294140c010b040c0c00341c042c5c080306519418075000d0300c0b545803464500300581f03801c5070081d0b802c101c0020011804c02800f0001c4040c02c40c018040b2501180c94990014110350320303440705020319020000c000607052030f2550341e40c020600703800e40031400100180c0c2c0d03240d110300250f00501c075a40c40d41c0d400000000744200120442c41003a5000000300d841c3d942da50600b181c240e0180310007404528250131440f40401c00403c00d01d180340f00301d0390080c01c62a06500300902007403d041e440345003490504c002072101d95524000d6001d002c5082c4030740b80002070b140c600a82000e48100c0c03074000780c6a16004010034030400140d2101c00024a4440b00401049 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 223588651 1250 223587401 223587433
    0x9060216030602180603010b09030c09091f0609020a02030c010e030708070b13060e0307061a0d080f0f0310031406010302010c11040e01020a0216080708070b0a050c070611 75
    0x6040c000e40040d08985010030108206070000c1240710480c4000313207190142e02d07001480981082e0081c02100c0c1d40400c0b038845908041041d48841c6030700300c54a100d1031401a150f2640e0361540f940600c212a981c0120702401c10183c2c024902501c90303940203544407982c0c100c00035901e030040603203410650300700103020a0a031008000c0b91901038101607000cac6400240d40b41c4080c3c0d20800740ca200d24040741e001102c5c001c594103100712003209000c1d80140d96104c1036400c0923000c0c1e0b0704040d0a040e50178441c111b0b6050554884070401c420302e900084007a110b0715600510b9405000303400c42c2244a0500004000040458059460070740784a9940e0369180300b42a0821692103030240030082c0810310150707040010035502602c1095040d0001c10100d0001e488420b035600ba40c101d840d148000d039005040185000083c1790b2000007030203a00c001002071600e003d030655510082da2042c050342107400602c50300018421001c8950700d24481c1d081b01c0001340d0b1004001c1c4003018460700840a030003501840300c10341e58 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 223589901 1250 223588651 223588663
    0x21903030207150903050a060204050f0f2b06090f02010206090102133305190804050c01050c0a080a0903060605010c111003140f06040c0206070203040e040c05090f0601090602 77
    0x601079005118040c107210411000044010102007400b0038800700000040082000051191241c00050303280c074a4182071041070120690364501c81c1c48680310780e410b00e4841a51480d0554814000d003503502a401c80c1a007052801c400026025504140512080c0b100b088509a1114802c3e070840c0c00395990790317808600b00e01600000d2802c80120040801c501150403d08004407080c51200c01000c404081e00703641070b4054640c1440206901048070382c540000e1389010084280c0c00d060030b44040c5843c0e0748490f110401c8080450600c4400308645040c080308002c07042c1540d5201e113402e0364920050201030710346880e61100f100c40c80d041010102d038039441048040c0d417440d44501c02610503540e00c4c0801090f5000020800c4c20955640c900000342e02c40e2405c0c1ea4000c0000f009115001c0c00c10709c0078001601c1c402c03c003034000e541c0030506010784107900004950440700503911075012620b41d46440351051081e6031101c0d600410f032000748441d882616013414006d140903218056800e80c3d40e07005a841d10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 223591151 1250 223589901 223589903
    0x3180b0403020624060a111f0b010906120f020c0708060907050d03020606040507020f01020a05190801030c121e0515060910030311012304200907120902030316021903 73
    0x1340d000d0b4040c403110f05005015118a182c6810801809885002103610b0081d10344072051a040c0244035582e0010710300d20803c0400359003031034044141400c0140103010481c1101412030f03101c0e51004904880039560f8140c0d074103d008442074a01490341c0d04940c2c3e0f07580c1401d0342c00d0701b1940a01c02c0d00056902e00038410300038840d4550082c110365690041080001c11000341110158002d1444410300d83ca0284000c185264507500c590b41c480e107869a011100e034080344080d50501c1214070052010403c14201001103584504c1c0d007503000025407400341c00c4c00070328040e5802d0071000b852054003000408101c1294080e100c45240303209507104c80070000145c20a45981d512900e8660041c40403a200d45000810005003800108500c88240380310783d056411010180300307640150003804100112052041510900311080040200b00c0b200080c8840c0b030701800d01404d00a08002d651010341c2141c109100c15030300201541e07107070300c45441c4214000d01c01700c0c41244112407000c9824841404110f44009072 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 223592401 1250 223591151 223591201
    0x150d0f0c080f0921070b011e03080d02040e01060903050c0904030e011b05030a080118020c0c0f0315250513090b01050c07080d0e010f0806040c03180b04030206 70
    0x40c2d110a0715200940b640604018414020400e140a40ca880072500e803000b910414000c80e80e1705001e0410f049050b9068000d04446407141038000c0740907079200803030b00940380c020b2110f40da10b40f4100807103c000e220340d038044040e212200d00009404ca400c0b00c07005045a0044c000d0310010038900c0d0402017850b004640090100303080043c0304446520030b24104c0c010651060150900840c1511203a107190400c0040c030001440d800010300c000c034000c0e582c425414400f00780560614120400348e645410300144098000e001c840700d0b0203019901000341010003043c2c9030740031003079040102d610024030807070f102000300903402c1c2001446041d04c120102d0f1004403580e10b102c2a018141018440900726907a1010304110040c8440e075103000c0305004e0308005101c00700042402c60752584010700000204078455050017041c0c1c80c1d00040940181031315a0000d011900054440b03032115042d00100f4a45240750441600700081d40c00300b1400100c6a401076000380c0032034915903242e0240c800140c803d40800b120b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 223593651 1250 223592401 223592417
    0x1807030203090106091b1b0c0603020a0924020d0207030c09020c0c09091b100c14011104030309030c0905040210080705070b0703052e06110705150d0f0c 67
    0x15052195000d103030440103a00000c94566039070b0a050050f18070320500120300280000c0868602c1e5008910821605400b0b0500e4550340b003c0d40f640c50b841400b903c01d01c0245500050600805440b0300c0200001d05401d00144524030b895203480b0794034002444001d4054851100d290020307a000055800032a0b83c8031003d900c5550a04481101a40049192a00d01d2160302c4500c2c41580c0c600341c0d050322844880000b4820742541800c4803400e0204c481009000d4042c1505041085078045842002560480c0340322000d040d940f01d0f014014072a0804610344003001103004402c15074403040440840f8002d00075540025110030030082100c20a5400035841002038200c103103410f00480c1707001d07448082424001d0400301c1c10344503c0d8139010201d4240d80086d940f00f040121280220b2002d0380702d42e90b01540ca80000c03100f42c00103109000680100d1091100d0720789900880d013010440d40d00905400360140c1c1d41c0034140e05d10031016800c400c0030a10807a081580c1e00c101c0040c584500d1041840b2a0b0310302c80d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 223594901 1250 223593651 223593661
    0x131403040b1b010204090c2118020105070309050303040b0a03060801050907150e060706052202060a030e0f0a080901020706111504021c030f0212090f0f13110304030e18 74
    0x2d0001900c040460b0307555003e00002a80c02643c2c81241c41d0380b00a51900d9950a00c6501e00e940c0e18402c0540703480049181c0b08409001c2e0003400741c242c20381d990a00340785a0700c8450382802e03284c880541e8402d0754544000500440c4081250001c0c003491301c0b29440620486481c1d4505030f0070f80c0c0c0102c4070001c0784d5100c0e19041208110f1030f40e0300d20b402001801d100d08401248000308020350f100d45070a440d045e0b03c51052010315210202070301903140100103c80040319841c0d000814512640e00110109911420041140c85041c0800700c0c00155500448421040c0740c035280b0321903085044180d002d402829000a46240507480000403260380c00060104100c2d4212511610301000d041660410824140c0b51480c043c07010061500368000c1d103480594191f44d04000740362410b114030001c5440000c2c400c1c0080c9448010990001003411a01d0030404c246100209480c0140c82086107030b00c904001d044107003213030100300550145001e6529242c0342210002405080c031460000c026a44400e000020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 223596151 1250 223594901 223594927
    0xf0d29150a21051e0a09023001180b0c120a020f07080d05090c060c030d0e0a0c030309050f150307030b0301060506270406030507120204020d05131403040b 68
    0x2030095950b0041c02d6014286000b846803c441d8201e4000072503480b00e00d800c440c0c04000841190f8491780040050218001643c00701c5d0190a03501600c0c1ca00014251007000c6901580d0000c9200c500c06070000c01c142c800099403400e10381400c00007590501c440d18040707804806160110303250303416900304001c50360710750b120404025171098281c10701d0312205010341070008007114010014100a8640410181461255281007070341d1000414402e0508116003041e2010101c01d5841e56440c503040025112007410f05141054040d20005041940e0403801000b0560031015410a0f0342d001d031441d45104009005105030b51a0a00300440075120610024902500c02d40000c901c051015001140c01595200400ca064002c40d080c0079140070662580d49514450890b020f00481c821603081c031006195880e90f6444440311b004005210000b01101002d5444640488200b9607952008100d03a11b02180c1d0001c1c071040640302122454a003210560b4003410010590327080e1034409072682d18003020f0030405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 223597401 1250 223596151 223596167
    0xd0e090105010f08130203120301090c120b0d06050405010b1207090b031203010e06010c0203010c0207090e0a030c02060d060b0f070302010b0a081e0708060a0603020307150c080f0d29150a 82
    0x49a0500c030b00c08d401c542c1061443c01440c000c1400407404280012095005021824071904181036185840004802680d9014022504503001000014251114105240074082a60ae0150001d4400d070380d60b1f03007100c0001069000c87e4100c100811054240c80e0806407100c03a20130030202c01000034401800621006207580360000d40504100800900550109083d22889142080560801c50003000301c070959001c0d10841a0030000039098010302030790060300502c85404080e002d10800314018a02040307a41c040b801400a503400075440740c88010100d1055440a0401c90042d42054500000b600b000d600a0081d100d00201402c410b642c1141041185680a12883c256100c0c1180004034082c0601c2010300620000001094450035030051512b81007243d442038035003800902c02da006080d40842d8184d03070240d00c01c1d1015659185060b441d202030056204440c4020701d080140c0d0240302100c4100410768102c3c66034001032000141c1001800c85158980020340f2030100040c0b00918070450f91 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 223598651 1250 223597401 223597403
    0x20109051003090611040f05030a021f09030f12030b04050402030604060b19030c062003040b18091005090c07030203030402040c020708120319020c1c110d0e090105010f0813 76
    0x30000c0d4071101d40e00c4513400d40d000701401140c40d01001405000c0b80d0030756204c050240c03005800034900442d469000c907050710003041200c55120100c400002ca02c1d031160414100940d0030401c101340c03000c903d0911086a0340e884001c4030210f454400c61030913038205401680d1080345c00070041c00321951161100005040995001940080c00d101c0c2c1000c0c0076400800075018600501201e9059418110064500c2039019002c014100740d804142903c8080081110207940b6414884c9132102c011800e10038000404450070b50307110f5034200402101246c00340c2c0a034104d40044500d800c80d9100d0034105240c40c030810b14081c0044c2c000300001070243c1020340000310510701e20320440b541170b9681c5807401c0c20400c0c200a00d581300315000042c490440354900c40c440c20090802c500714549071011030815994200f16110301100765010544074289809121170103c80741080c800d59004880c1003200030540d800400c00a8850f980000020a25510035030100c0c600001c0ca80307a1120f1034a95596002c490f01d180d00c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 223599901 1250 223598651 223598657
    0x1e1511032d0c0109020906041103011a09040e0102030f22020d141905010b0f0108060d020d0503030702030d060b072402040b070305090301050601080903030c1b0307080a08010603090201090510 84
    0x10504101d6101e0000400800c1d04107000090710042602c1001201c1d1400385c5841e102c1e48c00d00c44141d154800c1d0b241120304688140032100d0070f0210096581c0c2580c05070a0349158000e203004131086100c48190003d40c818071122001c1d0f200f0742e0b2078000c0c03280d6055811200c0d04480802c0c011500c010704001006840541c000d440c082d0321580340001c064031f814240c2c44c0c0406c000115000300310420409004520a042089407640c2800e029080001d00000004000c540325402000c03030b075400e40d01c4580c1c01c1c10740c603600070059a46d20301d0041e0f8080c0d81d030341c0048100003400c1c4c80c11400003500c0c2502019911050b0384084502d58500300d42d00d60950b1241d03c03111604605500300000205803a4000040010b0340c802d449254403102070104050840710004c0803141403200c1c95042045544011040f00d5000303000203a6552600782d071900d1442d090401c8104c0c1170440c0f0000992006100510015080c25011552000200d0382ca484040b015035070042e030024049151518107001c41c0c6005500c640710208170385 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 223601151 1250 223599901 223599967
    0x3120b130e010902030706080103051c03020d14070905030a0b071107150c0204050604050f0f15120309041d06060609060f0714060a1a10091e151103 65
    0x411038412a810035901400d02e81d0f44500000c00c50409000b01c60051041e410244841c6d07141d41ca0302502e4400c0700c44580295039040b2541d2042078020707070580380d07410b20905041214400038201c0094103003080e0380c49000b00d035501d01c0010300c80c500000e64041269201d8102800f40d11000d034113507081d240440391408280075089010410080600c030783d4a06106540d104c4041850341d00500045450103003856001c0c0c3e040800700300c00800003800300c07a0070a0b00c1d03690794541940d621b8400355121822012030390b4000d08250302c003101c0d07100001c090007854404441c1040801c000c402c41d01011078803842c1c008059004540042c1d20b6141440c05403580e004007800e03992400c034030340d51009034030b902c9100220382c0d074000f041d105c508548007040041d40c0103d181c002005121219000380105444107540c0610034060b001000002920070720004000f0024007681022200c18900f030544c0e4851180206c01290140300328035401b40f0700c600e0000f4076000304007028501c0c0440801c03121a03103200ca80f8460301c0c002091 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 223602401 1250 223601151 223601179
    0x908180f220605060412110f06040603020c060603280201050415030c17090a0204021c051603150f0605030735090313150e0301051302010e0d03120b 65
    0x210780c54aa12070000680a034412030040ca04004a603140c1d0080c41c0a003200780014000307003e8520201240f55045122003000810740400181400640f074422600420046000602a60144c010744100000d40c030507158650782d410b0505a50742a10304120881500354000c101e030030340c004c4010119490041c54000e182079101d15101d20b0841d9100110030009640d4503061521b02da1120307128600e00042a54000242000304405a8440781260080d10071680001e00102d1180d04106003425800003440038851860012403c01c032a002220600f8080b0341045051800d00d5000c1190005030703120718800000407410100102c50070703000200030b0800d020450000201000c60300c011020f03a590301c0441404804180c0013004030040014104003a164014003070b8240b0b54105400010039a480d07a00010100e8500d210704694404034403810b150035521705400d2107401810391203c00c018a000fa01c40030016481e107028008d0840c1d03203100c007070005182040082d00c05c440d55000043c140c1e10042c00d1200407040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 223603651 1250 223602401 223602409
    0x61b080403120e03060103030509150912160e0c1605190b09010f05220302070b0a0519050a080f060a0305030c030d06050607050c04020703091d04020901090908180f 72
    0x100e50425103140522000880b245a40620356905a14054028041551440d5009083c1c0c0c014608100e1103201c400400d2884001c0c14000d075401d205e0000c00460454099020a9850350a144c8502d120080300d05400f2400700715486500c0c1c02820801403141c078203402d05010580310840350404070780e680100c10195101c0507500002d1b03900d950007250f50b440a818202e41060860709120700c0080c0d85410801002652400346104200c41103102c0c1d600010f603402491700700d0130100c03103400c60f01098402290451704036034003801404048120308010411888100f100b0340d0b05000d602c245200141d0319200249054481007a0781d13410a102034170385103540c1d84070b50b5010b0a580200507141c40e141c5c4081100c910f4100180a030701e004003401d4400c24604546519601c0d240d000c034405440c0256000105901014460700129006050840422444840300c0c0000c070400303201a107099206904150020849480600c200300c441980404010300e0003440c3c0c407042c009100007244860340325100010750703081c0b41c131 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 223604901 1250 223603651 223603657
    0x50d050615130e130309050d0c0b030c040311060702031009050f3901050706050c1b15011505070b1503120d052503021c0e0a02040f0209030304061b08 66
    0x1800754061101e042c10f0044880c03a42000620510207813055140d900c0c0469080822002941d00c1034403c0800c1d41884d003459040f1051960040190440010420101400140140c41540e200d481c0a40006441d40304101142c01800030196140d0030001d2250340c5640c1039401314080c688500103403441c010302e610b4518201100c5090103490071000810b40340c4611341e0200442c1540c03800390f00401510f201840024040d010340c1400030003c998a40116a0001103007083d10007500324007a0300c0c007008894948464a039092010a46080a0b0b00c10010034a0081c0031102c05100815546070390500c0520703120200303524009444c91404102c242001d41d456181881401e810100f4048400e81d074200e250040070803648024001d000208902050742c1000e111006030840c002d030140760160311620f090b244840c0d1885086200c3e0300640c80d051031500d05440200300301c1c0c074842c0219410401e14200700861401e901c1000d8415525030800c1200b03004082c010603d4a00340d118801a80d116030b4100d90ba0000c5642c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 223606151 1250 223604901 223604917
    0xc1509062d120e0118020d08040306091101170c09010c03090e010b070b100b160203010b030a060f14060d0602130f09061403030c061b0f031e0610050d050615 69
    0x103016035800b4400c10080e030003103403034803465071008014880043c0f1600c0d01a038040c540091080c050720300d0060511007684240c8001e103400c4081005004802d2402005105030708201d203010800d15010070b404c0c05080c12805110f50200f60103545085500001103444880d80e05048081c0100c840000c1010007078403049902800e4088221541c0390304500f0300c00400030000b84820f032995840c4000344016000030080d1040c09202d0340c86c0001110043c800280500701180c045a054425050282d050010f0343d0400d540c0007448420402c04075640c580d80228800c0119940b682100d14003c2c0b15000444982c001c0c081c0c04a6800401404da84401c0103506a4040340e01c02d1080940720398080c005101d00701c000c1e009161048004510f4010a0008981c0b00d1100804840c1608007a00c10039129100310403c070b5800c2010083ca1603580d16102404036541c240e441d2642680c1040c040000e081c9040c000015403840e0301a84030721b4107005d9940103003030150500505298000b10251405403403503203400c010348081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 223607401 1250 223606151 223606157
    0x303070b0906040302070f082e0e01090b1803031b121302030105010e13200607030818060108060408180d060e0d091206091416030c1509062d 62
    0x7900f400e09000740381c80c2c803541120801c288024001c02860000280ca448180712811604241200102c0300710346546201025034201404e080c4800e68060066000b845c0d59841160500055100c481103880c0314414600000d035158010000b00700403104603a84080007010b6081300918100306101c81c2c503070101c0d050b107035502ea1100280000013140350a01a150140000c2c07081d2180901d88140c01e0600c1544a41010340342c3e190682c01d548403e01d510032041503a11004d4030702561992103203401003155000700c0c0c018410107141211554040c45c0803d8480c1245c40c4100144029201c41d11030354426442042071464040c466080300c001511a9400d142259005990004891742d214411600b00204080c1d40803c1200342441401416105514000710035040000040c40f030580d480c004006600b5005da41c1101d00c580220140c803096401d411409a070701c10b84151000503a20f240182c1c080c4403100e0340c4e102181d00060107020080c801c1c0300e070340714001d550095902d0128915442088003081d01c5191000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 223608651 1250 223607401 223607413
    0x50a0c090c1d040b04060302100507050601090605060a05031f0303030c0305070f0221070b0c03091002070f0303050606160605090c03070e13140607030f0c0804050601140303070b09 79
    0x19045034807a180003480c80341000400c076911480381c1001c0711000c40406100d59500d043c1074145864603884000610b90180c072064030842c0b2454007910035044844102c0c2d07240318139400807074195281d01400d03080b40c0c7d001c0c01603404c19071b089001745c03407a0300000c00e12042c40c001507a501c002c0452101240c00114021340380040e4010301c08030005c0075104018107410920600707404040ca2140d0004200c03864105d442c0c50343c10140740140d9454040c5c41030700000b40c94200c100080c440d92540020081d4040c100c404100c941502c00605940141d0091003405468180d65101c0c40b00464020340155501c000014280da03d4000340302700b110135559006000341d503003682d078100b00f03c0c94010420201510b0305003200105000c0c2d103420840985004000c0030104203060006103441041072071612950300402d810b09440c101d01e0170000060040c101d011940c121130742008040504140a014900d0091f60880050714090b820030900f034400c0d000125106815100411420b004103c10074003040c01202c03540301a0003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 223609901 1250 223608651 223608659
    0x181b0d050406050a06080105060a0501030e01060f1e0609061b11120105060108070e09150f0a080d080c070506040605042a050a1d011205010908070602130e0105150705010603050a0c 79
    0x421607172150024009a80343c11705000da00c0d07a07401d003032800f202d409180101c0c266889541300e0340907241641c44200314501000000c00e840f009801e42503041c00e82071340219480703542d0b14400c88802c0001c0c401c200100302d1585641008070000c00c0451f600c2c501945038003010fa0340e0f410110306525100d041e140e507140d65410078404c0c650381c00303071069402c0201803070041c0d0300071040d10000b40e20943c0500085508045203041111385d44411401010648000300740b038004940e83c810303142d200c9000404640006112a0002d05140980d0081d03030929038000c8000c1c001031742c0b0707680c0d00c40042c030001d403090b94812195044040c0c0701d200d110010505046403103c20401602e4401400840340702d9800c81c0080821181c5d046800b450b038040c0603811940c0c80064a000c00340d6504103107004110700500035241540004400040c40401d03001044506c1ca918041e00707025545110440d0314400c2802019030011040212100e078903030f020068940240200e000040442e40c1c1d580b01031074003210394021121388509280c200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 223611151 1250 223609901 223609921
    0x30d0f11030a1812080a0b1e011224030b06030a170d090c080d08090105040515070c0606140906010c050706050a09090203091f0501060801031211010c030209030c181b0d05040605 78
    0x10021103010352320a001c0c028018404441402d41d00903490420980180c04248070156400821100001038940844880c5002103c150030109000c10355040c10320401046260600040c88584181c01c854450b080303102d22480c2c030400340d1002101d218140e80344c02522010804102e800c0c002446210014001801034000141c030b404001000601c460340740000708008680c011802c10460120f181d80700b8100d40c1e071040709a900f010105c40c003800181c603244022690805007403d114a4a90880d0445211395822004480845030120700a00303940000c10300300121806a0050720015840e81485a00181c03515429001c0303820840721000103030b007d420880e1407040c44284441c00e1000105091066604140005e4074166041c80000c103800c0e90484150516440b032641108601c603000000d012030310308020000d000c5e40198013139034424050b49440c20020700c5d1441280d2401e194a040345200c0340c2d103a000c0008413048a41c00500f41800c1008001c14007403061146501c101e101d60350014072810518020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 223612401 1250 223611151 223611161
    0xc09040501080c0a0515071205040e0a050a0b2d13150504110c0309131103160e0d030905060306041d07140a03020904060b01050405030f030d0f11030a1812080a 70
    0x10b030302400f4110341500c11404400b044490340368005100076104c180703008e400c840511407075104034080c50105040c0401c03a07109030000d5014801c0d8410a2020600c80020040c0f9104068900c0303103150707044500921a208031014101680074003d15410403440e812540406940c4605c1c142c5414001550003440580f400703101d2200d5154416291500b4001400d030f140795280708400155200d4024441144684006034100f0302071020303a046e242c0c2c0c0f00c1c00c190030111000c400640d05000816011100c000a50404100c00c10640b505951a600c449103000d05002e0180d0001c4e1195070002d40314506204060030048010a00c0c902210050100c9460704c41000c0704003d81e002480e200d0300c0340030410005a56901e1507540c005030090400109002c0c1c4400603170b242c3c8101e502054150140d000c94103001071003c0090840134507000014007100e54601e18000844803404001500c044091011900d017611a500c0401100c4400240d00c26000583e10795204003e9400801800200c9903800c2000b0581302e8003803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 223613651 1250 223612401 223612409
    0x20319020c2109040e030703030e030307051b0c1008100906050105030402220608030403060f09050a12031e0504030f080907051302041206020909220201080c09040501080c0a 76
    0x1046051207018159551620300346858104901406800c1040284032070080b01c0f42c0b0070000300200030600c030300144c1e40c0d280e40026000380c2c0824a0304610042034400401180d10070711090f500d11f8a0721170780b9449500d00c00e00040402110b4400c01c10f2984058a0f4103000c0d2035051402d0712503200a240c00c5000007900700946d0081803da40c03c1ca081001356903000016a0f401607411580010344018080c0d00c0c02c002100b2440c040003040c00e1000009500c1404401001600e0242c00d081c403111621180250030707182d12480082199111010550106240e0441291004c486280c08103c20442d40b554109a868900d907404000e07946d401801b0825070802808844003201e0708045e034840c40c0c011001074890000b4464107018000b11481031a8000c0e10381d04450141100c801c2c0401e4440345800c140d4004d400000005001d4109840451041300c8009101d0f40d40119000d0306400b2801c03c0c0d401125120005840705000d001c0074441024142c0e5a0302501d40030f05410801000c00340b070703d501001145180c1c0c9d40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 223614901 1250 223613651 223613701
    0xd0309090c0c1b06050706020c0327040f05010f090533120d021b01050705010603050102130f0b030c0f040e0f091c05030a02090d0803010b0309011505030a0f060605060d0203 76
    0x80000c01e4104041e20000361f0489070068840500d0700400e4114818010f00c41401c0d4140010055079400c0f011070204803c0b8259001c1186c09000e01005003251001e00a039406e0940d0002c00b01b0102d410380d00071543c4072010816414044c920040b46521754500b0526070501003043d68040c480701d06100c01003140a500d600001e003129645c0d10340181d1101091000255000c6015400c4074503640607070111100150b1040c0200105546c07400c10038002d401c03010041c20400041e110001c0d81880480302c0340c0903600c00c202e8040c6540c54510007403540703600c01212465002c1c0240400541803001141d01d80c821442e070108042e080c1b4142081e1802d200d42460031004400141c2000080107030f10a09480c0d03c000305440c01661184850000783c54100c1d1303001d000b005004004000300b01c0c101c84d4030143d0b0250085034001c1c0035410074100c0c686002e8045029507070b0164810403400c004100590380e500c00c09401560300045d4540c56070003150085d44040314188030950000140100300c002d44c5040134445500e28 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 223616151 1250 223614901 223614953
    0xb06011214130201090503030c010e0d03060503150a06030c090c12020a0906051608042402031c02070c0906080d0908071d090c1f020105160e0d0309090c0c 68
    0x41e8000e468200641041c034000c0390190810300716401100c001028000080407a9180c00c1d0305800c0501805540308041c0c002d008891041c0880c0380a4003501c0c064580c001c002d45000300186920b40031601c001001d00c810340340c44500010100b654aa0030321b0203002c0103c07000ca01150030010141500080c0c21850050910400000c626254410045010380701685002541c2e003c1990620000c0413042d800a090144000340c0000d14446030305c8030001681003010b40840250341290140d032a030164200381c0d2422030300b003490070224446a07402081a85c6c422910350b40c2c051303107814100040300c08680000c4042d61100b4000203100d6000303018140104803130b000400c0e0740350801c1e00c00442d034140722400c0617010030180b01080001c0024410000000400390840100e00e02c0d403441e0303598a650020010015510380004500d0704007882e481d5020244558540c0440b040d507400038400b0340400c0610a4041119070807001c074a107101c0b030141d0400180c0507520460322102d80d0500341803003207000400c006406ca0341 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 223617401 1250 223616151 223616171
    0x30c090f050f03010b03100e060709060203161406010303020c010908060c04050d08120f01090507030203070206061203070c030c03020906010801030506071b08030a0e190f0605090111070b060112 85
    0xd024144159201590400440000c4801080c00341c401d107480d0942c580070b030011a21242d50164414440d218030b40e006c0390b8070303074603a101c0903121411039003c0c880050f0400c00000889541c1c1c1400b0460082c0b00d59107140788030300c0c00309070942014420b8108030700503041004181032070340c0c0c0501d120001d41030110140841d41003026030104a80700d41e00c81c0314010410304031004280800c0300d041d00c601703c02c450599902860065465180c1c60024010a00050b25020216042512920a41c0d1140e03203503800811154072038604001c0780d000d0854105160348800c218441c005a158114203008512030b18640031110b041d4410003506400042c01c0504200f004001000032500002d0059000303c0203040c0341c400c3c041003030341d807900081c540e04c405400f1500010a0040c80d114507801003000401e0201550030400070000f190340c1d00e809030720020f090700241d0012100890074a90040390046408400061500c80724800701c2d0640c3c103c681c007a15400e60203400c100c444d58001224100d0740015071000c0080d100c0b1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 223618651 1250 223617401 223617419
    0x110c060901082202030a060605031e19141002070203010e030306090a2403350a0305180109051f0b0a030605040c081222030201090b0325030c030c09 65
    0xb0300c41c4080d000507095400d14040118001c20030f058002e000c1d01d034007144504128000e050140700d00c40c0a4070803201c51000070f080d03039004031000384202d0008d8005502079907050911140c01c0c8105594402001c206e2501c800000c02c11209030b1106500090b1301c4481500400d0300f15081c0d4020744044e40c10400411100e035407645111130348481c1d030340000100c41c15070405c40540e039141c0c0310101d0343e0940681800710074800003143d04071b08510344081ca01c1c20203100c01c003a00803540300c1e14079520031104140031a202440c042d0300f04c96130006035242c05003c611040000d581c2034405c40310081e569904046207910b800c500140c4003080341400101c0510014041d5008203c0c14405c512001e414260b884020270100004014260000d12050341120080e1810300183d50059100402c80503900102e581344900d200300451941085070340584900e02c0301454522071032002d500042540a000700018800540760296400d402d408ca51943d40015800051a501904480c08547c85038144010f4003420489244 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 223619901 1250 223618651 223618667
    0x12030103081e0d05070305190b0f010c1a070c05071502030318030702032b0806060912071a0403060506010c0c030311010f021204021005131203140a110c060901 70
    0x4640409280b09880150300018000d48806102590034242848000c4c0e605030030242c000d9617041154030f0803020041042c41280e03c0015080d40080045034002110b60041d42d82d11855401151044100380310403030740f000c400108982d84e20200b5140c0340c0c03600a00800f000f180004c2c000c0c004914901c4000342a000c0e503a804018a940319000c07040e00c010302c503d402482640c0805a02900300ea903500010108241c2c0e003481284030b50440b043c108101d0b0943c9105e11070140c010103015001078501111481480000004d00d08110f2091055a9001651283d01030040301c40030060001a5111421403815100380d80340500b6507410450b442801c1c5c0e010400b4910743e04116a0f040c00e080c1d0b9112410301030345000d0600d185a102d055803000c6403804d070469184c01c5061040c0c4c8202c45424050200010540e6140940d520002c1c14420b40c11090059050501450160358000c0c207001e0031b02a07101d00704100f194071100b614800510500f00f511501d81040010016540b02113403a641000707405c03c00240b10351 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 223621151 1250 223619901 223619917
    0x206040b03160c2a2301031104060504030f051501060e04050a050103080910110d0903022809020c0102120c0c010e120d0203060a1a1305060f0711011416051203010308 73
    0x18140d1651400414008071960700519503400d15504c4119601c0c400c3c041700b40c8004801317011906010241c00d01003070540440d804c0e10040d4888501701800c41e01c1d820100400c821040720140b00c2c00c0c2e1604190076000f000c50f030080102e9a80c103401c1c03103064000e11099510140c6a05101420301d0010b10020b20084203403014a10306a640078840b014032082140c03000c4a00c18080e50780d000321409100100e6003e1220000d907402607400311440c40c466685410722031170740780380c021031101550800d01010041707400800e01c0c0c0070a0400507080c5032012180e13602c14103081e00d454001080020302882d0512003801a402125030701c60203003031020a0103140b5070043c441c2c1162100318950010006006555808848026100064801003031907081e00303401c00d56a01403041c200820001880020700d40c641041212403481d150321495041403151381d94414000114450740d414488210240701060603d0000340010041030141a1242d00311410102c1c00c151145110b040c59940410040c0301041d0b544080b92000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 223622401 1250 223621151 223621193
    0x31e0f0a020a1215060305161b0501110412050f0105040803070f1107060906020f01060b0d0e0c091f06020a050303010509181510060c020108010e0a0204030206040b03160c 75
    0x103141d1445003200e40c940318603c1c0f003072a603161500940784404200c1905041c1d03221610b0030440341d00d400f034020302e020b81601c02100c002950301610310101ea910052030256070740301e54008580350301c0100d040c1d440f680181d08001000c400c24211901405020024940c90301201d85c0204490708298403466210f1000034440014400109242c10701580703da41f085000520345019941c0082c3c494030001c004490600c5441c0c010300c194120003181c540180310700400c46458001c0549004088041400540035503035242c410350140d0420303c05651516248280701391440c1207070308100b0007410002d550ba41c400350002030031944100c0414000840000489040d60002c9841807060750b0390001101c0e0703001d8420b2842c040342c010203020508428076800f826000b015603021040501c3d440312403c1b2000202c4030400780c00262428010042000b514510a400069a99000d4036041e05c83d0081030007607000e5400120401c10000070012a80c504000a14682c0071901c1e01d2400010715454450300006403142150300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 223623651 1250 223622401 223622407
    0x6040c0e01080402120c120312011d06040504110402030a0c030608010b06120a06030203100b011e02030a1413060e09010e100e0a151403060106030618090614010308031e0f0a02 77
    0x41780340420903400240d00c010702c00240700031861081501da42005e071203100712092800011820b907080c07107400414909071803291200d0366102c10800001d07003000340c010f94940242035008803064035207000a601c0f0311020100850b9540719078a00a08488039070707109400c9030745050540c500c5552980c00701e82c0000d0290600c410705865a50b5440000d20039a40b0003545803244850f2031400c000c1d560450312581109895000b910950100c80c0d44c0600e040408920050300200700c21500b16006400e4007694013000040d49003010700c60321410071303551080c2c0c0241d004203860014061040c6051406d0501510026083c03521034204268071110442080c0110a0701d00c04400003d50075a4481e44000503c660341012500c1c025924480c890400429240d51402402204000301e85d0034085c2c06942c0c2203034440444007003004503440619008000c148411100c0382d40351458640c0c110794070684d140c0614021081917659040460050750340c48216208072a503400d0550800140601200f07409901402e109409a9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 223624901 1250 223623651 223623679
    0x1003230d020c0a030f1b0608040c050105090d0807030908031c050a02130e070c08041403011d060a0b01090306020403030302130602010615050a050705010c0203030a0c0302040305120a0207090501080606040c0e01080402 95
    0x1031b00600e00c0d00d582e8440e0000050316681c4404014000c40c0030700b0000d884030380c442004440a1041d115100d07040080d49030385500060740c600080071000c0c007030b1138040c00103500c0b04070443c11607009211b215220600c000c80e030ba49648451050076003103d81e141045143c641140d07010150550144201c07040122050001144c02c2d0081401c1d190071a841010107580d980c0703403c3c4034501407400c02c402900940c40d000022004108140350406d0303a2180c07100410990340c0d4800500050041c21000c141003104242c00000060020700192016612030744015032500d9018031080d0308002580c0c4103004580c1094001c000742e5a09482d80c03c035a4500789409680c0f1500c010090712144551540100590310700a0b406d4001580800614007401c4080424440414a210700f1070036030145000c00b900f00c1c2c11030080d980890070840000c2c03100e4061070041e251100c0e0303070712010001c03584241e00103400c0707401400c20031007240b44c40d10421040140c00e050280d0300200100008060001c010002400b5640d1811044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 223626151 1250 223624901 223624913
    0x50c010f171014180103060b060c1c1b150b04020c03070f1104060e010902030915090109050c01050304080306090417040909020a0803040803030f1003230d020c0a030f 73
    0x34044050010305220306041030054039070b082549100b840d442140511541d181d602d404140101009902820034001c1e90a50716010018480c101c00c041e800041001660601c02c0e05002d8200a00b4001800c041480a030749000703042280000d405c0f00340c0b940100e048100190142d0092640c2c1070310040001541403100000c10002d1007007920307203241072101090040030051000010740180d48501713680c549440c4010180030590304580505010811400d0050118020542c043c5a001e001c46045901403610401c1c0da0280e131405455181d0541d44031005482481007c01c140e0702d003040280f070b000b85180360070780750098103001c042e100314400c2100c000801d06003c15428464a0710b14031045240d07850350749000840090100c40c1c002c0b40a03410341080001e201001009484c21120301c4405503103195580311480b2000d01e0018500e1601030805900800441c22200c5c070740b0f4040b41c41542c40c01940300a1718400f4a0845070302d48440c1103601403101402c040e00e07001b04000403280d00c10707802030605007289441 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 223627401 1250 223626151 223626167
    0x2070612020a09050a03120e090601090303050c10050c0307030b0d08040e040c090e030408010b062b020f0d06091a010912050312100611030909040b060607020918100504050c010f 78
    0x31584030a5240d404414404007580b10441041f107612079001d141c14440522059400c12036480d400b04021142c1040464001d400038081c403000782e025030304c401d40e580003410220b41d426208608240e00100803c11880c0d010700c14207280c8841203c2c41d003000f24003551104458440c40c007a007e507000141000c181003019400031a03000d0704200c0400e100d0342650490241d501d400500c0748203102d41c2070031104959802d01c14110b40b00c000d00400111302d0000080020040034064000316852641d0820031228035807004d401400503408058000301d601883c0c54071490030744490402075202c0c00154591303400c2c40da0304075241701c04580c3d103503100180d070410906156003140184107a50302e190b82c03071504001004004440d100140e814a8441007409000041e115913280070707403594070390013401c1b910100700407030304140c0d0302c40d030085005101c039250032840d0703000c0781400f06d0688880030481c58492031000c00800502c001c1c6c100206084041080b86000d4888640d500ea141925505100c003042d10f06455038440e02c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 223628651 1250 223627401 223627409
    0x403140a050a0803100515042108040f030b07030506030c040506030c0d06060608010f0308090f0d050a111c11060901030b090103050a03030c0e09180102040503010c0504030b0702070612020a09 84
    0x341c5101d0b0700789040c000030321382c0704a4920300d40c1c9a075000042030915240548111a20108100c281002d05025100c6d50710181050f03c172011500c0242c0050005071418010006809002100c03180246035183c40380d19844042c1c10b0307905260074481008100d0310001000141000c04071008503150b160a0042810408030b1810550410303407914807882031189941005c000c44034240d54803850fa0303985000d4107422a10070701000b00881003c00c943c513a40d01e054203100030a80401030003c4080f0f01140d485a2030070800040450382c2c80301150403074000b89010207410350880b100c007644201c0074a082d50b490130003903000c01410340f080702d01089210040c0d01c254415188650301030031010a9507104e050013070361030307038130300b004030002400d016094480910030624100c0c200c02c00f40143e40f480d100d0b051205503e100c07401248c40250740c203200001d4260b60034000d002442409803600d0340c4d07842c1542080400c200e4000c0c10401594882042040990703880017106242680c060f10040c6c0f5080d1854045903181007030b0384 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 223629901 1250 223628651 223628653
    0x320030307201c0b01090c05070303381018180f0606200102090901050d06151403121905070c0f1401030507030507020d0c06021303050a0c1202060403140a05 69
    0x25402c0c1c55140d40b400c4203400034080e031002c4d000eaa0b40e4500306000d403071042d411400082d000b804104000f074000d80207100000c4a4000c100c2941d03825401302c0c44151400802030b51008081201e029150a100c2c0c1c291250121134503049c1004070220342034038880d642c1480b5105039404012480c07501070030107034170024003100200c40a100250303940708000c064034850707242d0501180e5134480201101405100326460782d10081d1401005a18000810801402240080d5143d9403946400c404460400d04150301034010148103000714540300090510f41101214a880c60182c100508511844841305014101c0640d10300180d88100c1490a036446030082c1d817000101001446010031300700204141064003d03401c0c3e80811856607800c2040b01910300544240c1c0242c0c0040340b051401c603100e16001d110842c068440580782826041c80c0005440150b402528031303401440d444002c0100402c032040040030340314030b0380e0345c004a15000130302c0354400d901c0010302007000c0000c1140d5030315052080816964101e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 223631151 1250 223629901 223629919
    0x3060207030806030717150606070614070e0307180b0303070507060201140a151401111204050907090b033103030e010e010c020a0f0c0803070c032003030720 69
    0x49005804010292811482402001c5000c1407442e4000a1001124240e00040c000b414440e40314011144001d0002c1d278100c0010000400400e00380e018450b80e00081040100341031a25045c01083c03812200007151080e04100e20400180c0c0b80e084203100c00303602c171000000700c90b40c000000903c1c611402000030428010355400040854040d4401c003044901d10710011003540d9003000d508100d40e0030362500c0441c440c54031418045803080c0382205d1200c44040c100b621b0754110b90510980b07000700740c2c2c0400026540000f4180094101620065000452070030310481d02400c0004211507400005c1a0500040e40d007802c040726144075082c411804402e501d50384000028606000b0044e182c03c0444151a41c2080010700b000c0105204d65005407501ea4003405035070026954444003000303e820190740d0002190302c00b00348804140014052144654800c40100e4958a0407000c0021038003000f001c0402c681400d241652004021615069170182c58850f001c8490030b66280e015415880d0240c11203400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 223632401 1250 223631151 223631153
    0x30219031203050106021903020615130608031b070305060c0702030a2a0e070c150212090607030f09020a05060307120e0a050c060304020a120c03020409030c021014040b1303060207 79
    0x50b0f020906803242d81c1d0070790f2100000c4004540c600051114020300503404280091070f466840c40c10001c05420041c0350740e500c059180c146009441c001c1c0c00418454000041016a0700c2c0351440140d00c0e0094900904000d924648030b00351103041c0100840f0a582001400100715a001d10945070750581c440017200d07000e107840410302000362804e0101598010801c40105240070680314030b0348240404e50f51a0800302035699800300d42d80698008404180d02405002070310604142081c0c480d03a0410000c0041c3d15051a0003001e5500d032082066005142603503101c01f40e00d0710740400c0151042511165920307201c80c941250720038082480048214500700d00c0185e542000714085242f04e0040084401c281104070400484e40300542d4000d52100480000b0408005200c5c01280c1e100e00074009444401e039a03070040b07015140849011800940304000000031031505a02200c0135852a14007400404410040480c007480740340110920244042448402e0040c65030006001c1c50f4818000d41d100d40d00c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 223633651 1250 223632401 223632407
    0xf15020c03071d0702010e0606010f050d0f0c090b0702010507060207020102100504050f241503030c010c050403020405090105040b0a0e0c0a080a0c050d0c05010f1b050a0506070e0603010302190312 86
    0xf514035101c6500e00400003144000e8414054240c80000d00c0c000740c5156112400103460080819107213400b445400e1120071160b9055215808503050012804210080f500500904e1034002d500030340ba0480d024001600540da21905440c070003a0b0081c030050741c0e032100c0c0c00140c3c548502209641c2e45a42890100020010041440803c01003c18102c400c80b168114001040d00c840c2d0620514909a0000040d641c480240441012210280940385030180c80c1c00010f083d500c540220001013280042c0401c1103080911403203502c503100800800035414940c0d152403000c02c01134aa50103c5455000860b1000c00500c41080710400041c96051030035600e00351551540c4510006860100300c24034002103905107207054024080d442043d6080e0141404015104504841f60b203000308a100d4400016501c1c0c01d0303140e131003002d0064000f00111042450032903c0c12030014101790800006040f881100c2d2681130640c0c6c19640c3c1110121142d1010360384054940404d644007070310140300e10042805d4150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 223634901 1250 223633651 223633679
    0x50a09121e051206091f060f0207060c02130509030d060e0a0c030b0105160c051210050603070b070f05031e03070801050102031201091806060b04061205010f15020c0307 74
    0x80c0a40050341c403044404001d950a01803825010705a002c500f00040f054905041140d620690448508803081201c07420039400054a40012011880c00220414419010807542c001420a807a00410b01001d0790301241c022007030186160032594680f00440c45d0070006005031650200b85ca00100a456a00d0515405400046c1c0780210603926000e0420010351090095008151041c1c486600e4007480088540f20503000d40d40980b0311600d40000400d0300c0c1c1e01c03800001d2034001040c004207600000500201c6c00c1303404c00f0b41411302c00c1d40b00305000c001c2c2403e40425183c0540d046400d440161143c2d0502c107066124a210200c803280010b03100e48500344000c0040c5004580c0b03581c1e0311b82561b072500c0040e039070f078440d08495031140452400108192a1140c220f41070b1540c0010010303c00c203146036a410250b0b092038100070000080406c2c180841d9a12180400d40c000361480b00740301d1545400303070500c5a0155405813200e01c0d440c45002050440c003c110000d07030004090110303a900b5079071b001e11030b103104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 223636151 1250 223634901 223634927
    0x314071406031006110c0a0b0301170706120c11191a06090c070f050a14012d050903130b03060a06050a0207051e030f0d02190510050a0912 61
    0x1828400350030141801402c1d284a02d820309505109030b4240482695202c2074509514914842d1380b1902885465201400c0010028941600e0300c3e94180515800311540c00501d84515902030a410045e9941c00021000c85000440d0f00040100d0b10030411520b0000d40e012600f0a840b5401f5103007102e543c8201208580e42c00f0301501c0010660700701404445840580d4030503448200c1a001c0703404103444400501519114210703110b940b009a03542d00d1700300426034130284c5031041c1180210f030700c4074000e001d010200c02c21448601d515000c2503041c8074181d42c5660000e1403450b61440000c54480301001160018038142c488805980d6540100c592a076004440660056901d5500028200d014400b80ea8855485402502001e41031400713021400f0841169120b89098045039480e668400380710350700da49c42180000c0c210600301d0b40700292415040140c0800340c2e06400842c08003050020030500c2d1007043e840c40224039900e41d44240da02420300e210000e0545000d0f5108640d02540060b8018040307 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 223637401 1250 223636151 223636169
    0x30b010b0a022104031b230a06020f121e0f0703020c0a051e01051b0102030105090c090a090c0c021f080f011a0d0e0d020d0905030718020a0207031407 66
    0x43d20320440c1c40c5400e001c46118802403c01c00b40000c2c00080c0040040311440e0000241e00d58180350390340070b0701000040c84601c664202401701c0b00c0d07030b8690600f0301500c0040c1c92540020315a40700780d00c8900c0c0d0703280003c0d10410030032a07000c1005a0300c11000d2030f416440232203c0784000e07140c0b0107500074042c0c0c07580716060440c054480c081c50108107040151a0100300e541c010134102e081800070342d000075000d001e800d00c10b04000382004000c3c0801200481080040015000141c8035030600c030030f020040c03101902c5411064028049800e181c0d450341d0203007003a1100d90101240141d041d8009407403040542c10b00030340c040543d01d0646481883c100710315041e142903964541c0d0303e0311100c050008107072007802020364000c04080100060000a001012550031440c0c00203140e8103055001410240850280c00050b0030403200310703205a51103c3d40601a000443c05400c0c030780c3c13038040ca004c0303a40005c55000d42130517004540b0101c0f1078028401d105c02181c1040041010382240704000340c607080240500444 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 223638651 1250 223637401 223637413
    0x9010b10020d08011509031b0302090c07020f180c1305060301060f03050609011a0a05090a14130c0f0e0612070203031909020904030318080705060a0f0207021018030b010b0a02 77
    0x110009004440440b683d0310b4030781c000440d003180c43d81238100c19019041c2c2d082c2c980081c00000142c0f50300302c41c1c0788100218a000f0751544034034810000c00082c88080300740b2980342c82552541107001641c00c0c0e0b0b00228503026081d500c40881c96510741003400341c0d021903813140c004400050000d40001103007003500005c0e036080015a84e004100588000c080c000c0500d01e03402d00041c00e00e4a011000101402d100d1350411605040d43c6c000020307281202a00024240c0300c6001c842c4445041c5054100281c2080480c00d100d0f410415800508012400c1c102e0010031601c500140d0842d00d903030045801400301c1e0405c2c0714241c946010081c3d60b030741c42078501c6d00820b40490f031030200410582c4100501c0c2a40242513940a8685460132005440d1406000700542000b504101c00200d076203006080d8a84907038080d040030f1900d08210021070721030421b803003c0240100b281a0060341c401035401c50b4800c0f68101200740704103d890362688103a50390401049a800b80d4008120705514201604801c03a41e9821100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 223639901 1250 223638651 223638659
    0x52a071d01060e03100e0c21120a02190c080c03060c070204020306150a08011707052101111201081b100804060b10110c04090308070e0103091a1b041d09010b10020d0801 74
    0xa4404c505080c032a4004094003110204c04000620f9007038114070465020cc41400401c901ca05403811085079410444101008909410311111002900c1100a03088920309030158040030311070190000d108560000008400390740d80142800b542103c1c42200d62100e08950700a080d03044203020ba40c40f86046081440c540700b000003161415190301410800b841522111180395070f90b421200c0c981c07a03549074041001c1b0b4103429006806452040c801c0c1100651410b0302280c01c2c1441c01992500214100c0c00811154840950860020140c0d191a41ea07541d41ca0034218001d0031032140303071988010120b03091011140d1024040280c0740442e0141e400f40c1c000c1100304421201410b0340200400c0d01100001c1c4514002c4440c0c0302443d006040125004146640d1030780100074004100314620010018448003e4070007c01020032285c140030145003a003040c0384070105110740e4040850f00c110b141c00240e0035207400c1d001088889400f0700000c0d5460381c0944065140d007400c07044900043d00c1d01000003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 223641151 1250 223639901 223639939
    0x12070507051e0a08030405010605031204091104050607030e150309011508010207030c0b070c0b160305090106180f02090a080105010503061003021e01052a071d01060e03100e0c 77
    0x10b80a041d1040203001d1921507030358802564000400a039201c0d540c0b213800250b0345d00d0602030480c1404000c0c0e0096602c2c2d080540300421202800d100050303100c420f210910668690f1802c0f00d180c1601410044941010800010888000c0e031120707040080021007032200085054008241c2d007061402150036003519400c21030f00700c0c003070104042e0005422800000220f0000d1107100e80050071840c20032401c0a080d281c00c5030300308081d65040c503008aa4141c0001e155071501c103854029040200078480d031480d040b00d100f659011419081850b42c3d880e52003100c04642a8121030320080302070b00d5040e010b0780d10810640203200c01d1107042e01a010b4080020710003445444041c0030b40ea4003c00c1c6400702c041000b144040e0f44110308055041c0541003118000c4a08040304107208001c400d07054552840d8510b034104d00340801940a010754154181e1035406407a240728019040d00c0c228509074032a860b41f140042c1c6000000b10011014a1420303816444982e404261060341810503076080d42d180780490014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 223642401 1250 223641151 223641193
    0x503010e06220311060c0a0806030c01090902090a1805060a0608040510180b090604020109060309050613060b09010902030402040b0a080d140409140f011d1303051207050705 76
    0x5000c036500307038011112407400c1802d0000c9910300030300e040300310f52018603401d5240600c151403444a420000c10914030341075001c41c446610100c1600584a40f400d8440041e014825600456070b4164000c00e03107061035102c00142c0c0d0020b141107051210720b140ca860000b03008007400d88105024040543c07002c00c0090160106c540925402001001c822000704814401481d00410741c610106081181c00b0114080000c03690107240201c028100070b007401d00c005400c25500c1e600c202c040c517007440c0883d0041800400c00d10b92007004549002c540c988146480001001c7c0034141b154050308440c0040303a40b02031580030f94445c510903a000c0060301c100320104040c5038043c0c440c800c00c0c0c1e4401446508a20f01c01d450902040c0c0f000c0b00214109500c034003401d8191400c2c41009607040549008006034003c66185082c0102011045032568801651043c251034030000d11040d203001401600c442054071540031501c401c004c4850849042c14a40c100415681c08410150342e03034840c0c03c51a4210001c01c1040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 223643651 1250 223642401 223642411
    0x3091406010f060f23191b17070c0f080d17010513090b070509040f090210111218014505030a0b09060703060609050d2a0503010e06 58
    0x84918030f480d068080b110060080044070421081000b48036400341e01581030b902d0005050f410540350845d85840c1c406000c244500c94041013060310f044d1002100c0079200200d0300f0741007a941040aa42140072000d14450010700410b0034851580005110107511484403e86544034103031100031165200885000494802101c400007086004210500d41460301482d2003003402408296045117840b0148070311011202040400c00004861050380350a120328040f014400314204150031140e00480e01d270000c898010818410000142000c40d503080103040441c00751a207056985840c0381c01d42d1511107000603541c1d0302085441310480c61552810b0308200b901a580349407440103801c1300c1d010b030340f102000300f01d50199100100008501500c0038060740d0582401a22480c01c642041c4940600d0800001c02c0e10042600d820004d1100b50b134040c84507400c070360b170850b542d0340c0018130350030f01000c82001070001241408400c0031510040400f6240702c2e04458045000f00010005d03070340d0281e04c980c01158 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 223644901 1250 223643651 223643669
    0x8060711030a1218050c01090906080304090207051515010f03051b180307080109290a0504062405030105010801060f0b1e27100c020f12030a0309140601 67
    0x1089024603841624103800d00c02001c0701c0429903104130b0860300f0b29060302c250b003900c054002c05019022560006004002480005402c000440c03400b0078198680c0600d00420030700c035400044100a00408110240c182c00d440219010b05090105000400101e07454003240800c110011004101e80030f8880d1031320480700840c65a21207100a00c0c800c205034081c2080100d51003070210941550b8404006041c007800d410400000c0846c0c80d410694140240110400100b15219002c0150710303071040201034001c0444640030640740c6503440c200014010762080c0d60042c50f040300d150744d140c92800248000719041500200700d0307641c0303460b043c609032812409000c0c00b401c1c10a504001300c0c4055002001120483c41a01d44506510342d805842540100c5504075600c040310b0322540140300210149400030022690300c1e10001701580c1c0500b0284540b413001c0c0c8070300844003031100e00d501c403814000c0ea000a070740c1c00e4a40e204d44d070714409002012810720a60b000c4003061240f5410000c001031213030603220100c0d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 223646151 1250 223644901 223644907
    0xc09010804020f010203041d01170111120402040b06030721050601090b030a060801020f0406090b041a0c0109050f03070b010806040819020c040f060e0703050c04180605060c03040806071103 83
    0x6003e2000400d40030106904510080100145c50380c0d08802c1898111482c220b4182154034141d89081c400300c1e43c80d44030036203916000f0a0f80c4c000351150308861040c50007010800d45c595550001500502c41d401d00150015800000c00c11210b03800000d803070407418001c214059468400e01080116030007194500e0110b21214000d001c1381c240480919800200c0c5800070ae0050b03200d201d0700c1c0c00d981058141000010b80404d06124407600003079000081c100c0c141d4124241803408040e03c2000c010a0141940c14600007102d10040000790450708916400801f01d5005001d01c0340481c0d0b0b0b0342d111040a583e0052000c0c004943c02d00d000ca0740500541d0080703a501d0074942c20000d0041e1210507074450f801907108040e41120740391202c1c0240d480499091000054003850544075681609000740035108142ca030200f04441d401c1c08400791001e8803a0209188488042c3c900100c00034000d540089503c00c8000c160355052070720000041c016910302805075503180d11003010540358080c41c4841454207400c14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 223647401 1250 223646151 223646153
    0x9030b07180b07020d1211071d0a02070501090501140601090e010308180102070e0702060f070e0d11030a0c17010b12060a150e0f0103030e2b02060909010801140c09010804 75
    0x229000d00f5078a4002829508200c0740c3e40e41d4048071240354446940802c0600d4580355802c40c0034007108001380307103608203840924074040e000700b04084000c002d0041c069001c0b4041c4240305096102c03140b4154400000c00044813006480010342c50220340340c90011b0080c0e1008618122000c00b5541200d45c001c0205081035804140004c8495060340740c941184107480001507c1314028440c103020300d00b1074010345024100741c40303071148505005059405100c0c40160181664440b080d0a1003d682c020b0324022250192000203030810903e48405080c0002031100810440001401c00d02c00f002c500008010003055802803014555040c900144150480c0000400307880403500400018a1903520040a050300c2e9170481c01100d07415280d407080d51003400014410103070480e920b0b200b07181d800c460080800031000100900113a892403d002c000010490b00c07411501c402c000d488200000030a400d50170743e1101c0c411402800c5090100c2c0c4901c2118010446440c20903049405c21041a984e514031941c035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 223648651 1250 223647401 223647419
    0x302060f12010f0e06010813030c020102031c0501090e0a050322030804090c030606180b07081201060c060c03150b0309150a090201020f1204180e070609030b0718 71
    0x20088200d403041080126907605200004070034007800100d20f94498560070070101d1009904d00500385c1e418843c0500c2484041070100340c1d111000355144c5007044d544012480101d0440c007568000c45c07058041c007110300c500013040341c02c4141600d0b181581042120a0010051b580704040040680700703400421840032451004c034103400f0940c982412405040390b885d900d51580382d000d40d1000300f1059071500c149902950601805005080501d402c2d07141123031010350345203d00d0043c0304940720900002010000c00003d0000d943c0e0044410340912803640c3c2d9034a001d84003560000e8103c4205182c0641100f0440c041d204074490484404103460a260814425030595407001e4078004a42c17061000303c2222420f084941446100c050388007050240040c40060b1900350440000300882d00010005a0720041d0301e001c2d642140c1603a20343c5a10501031010300c1c0b000b000d0754811281c07280a0900081020358121a02000f22442080300405581c0d60901c12504403d0340480b419030100151001c002c6512 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 223649901 1250 223648651 223648657
    0xc0916050318070306050402041401031e020307031704060f020102040b03010501110c041a040f18020603040f050a030507030f03090c05090a1107140f03070305070204180501140a110c0304030206 85
    0x3045501080b0400020403c1c50810b442d407044600584400c04c0208504060080186662014948140c55415580c803501c20b4001c05544c001c0da43c5540180d24251341d001c001c0d480042d50010311120351501c505550001541c40343c0290b0f00402e21805a400c3d9a81c0305100306c800305c8111441c92400d59003030800443e13072003d01d26840d1006101300d1005032515583c0d0721a03412118443c1040c0101d0302c840344140320559411030140f0360114a01003000e60306080882c154078409a044841668950f1689010901021a4039000d045440350142050070142c100004084c0d0b00e0003519043c0741011a504202c041d03450b43d00c0b00501d402d01d035210400050410208440d0000d00300711003c02c90004110190b0200d0300210000d40321410810400c8170400d1040c030292060610840c0554903094203601c4c054540d01c80d80078028000c560300c14640080c01090103003103094550020081c4440d61442201f5283c1010070788202544500d0030000e030300310805c240119a07070201585e014504092640d001c02c40150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 223651151 1250 223649901 223649911
    0x21503011422050702010e0c1c0b0414030403050d02070905010302013c02010b190614090109050904080717131703090d03170105061812010e0d09080c09160503 70
    0x41d880d00003611060b14a00443c0c2c466500e40d400002c0245030650898944048551800d000e028031000d80394040c4e4141c2d0341008101c2c0c100150b00c8680c2c540e49402d00c040009500c0d07940841c000414040304001e030214201440480b15421140c800713849121a10880740d081c0b2000b408a610880a604003d034202012100640030080d4265402d190804590804146442400060350b42c0c145c05811441e08103044e00804544580c903040583c14400c0142c0740801d0114012803003440410304000c0c2d82e2051109001034040070303141e01a10306061404904541092804440750200c0c00e15601031007210f034060b5110100158180890b0a10b4440d545c00401c40840300032001d0b002c104131600071500c0308071200114a01c41e13503c0a03070320031000d60300d1070f08044103801c200e00c01d481c1000300c07800c410802a04502c44d0101200ea04500d01c2c210580e05005000c140c034295440e005412444501903080f0303089000b01c4203a1030545031042585810400189009c540c81d110340d181107142803a1035442640615445 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 223652401 1250 223651151 223651189
    0xb28090c1a041d06100c050a080d050f090a03020c0d1106071b06020102040b07020f03030d0e100b0114030f061207090501090c0e0a030305030c090405010f030215030114 74
    0x100381c4402406100c484600301071000180001010405106500c031080e0742420b9088100503d07041050005807094144000e000070480141110010301c003051114450307407640001d80590ba80d0030088000040c2c2011070faa10012421000000d81c82da4021500900d8950302d039001e40743d203070039040c01c000e0580c04410007600c1c542c200649070003054036840c1c003d0001130301410308100c00903002ca000011040542e0810f03c210390043c00200b01007070902042e01c5605a04076400507040b044e00c2301003440c2d8041c0c40703c001c0344207040c01c015511812021850041302401d0000a00002c4d80080043d100d902080052401c030b100c0c1040003a0b0800e03240b4002d50f4101100501c05d5415824005600d403a101958216022841d911001000070314080c1c4a50221880141014196040120000f410060840c80060141300002000501050035603080780e4807018000c20810041d40c484403101c1c011401c50200f04e00984140c0c892200c10103250068a0403154440c000780c1102001c10240080030800044000b1b01c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 223653651 1250 223652401 223652423
    0x50907080303011e150f120f050415180f0f02011b0b0f0106080705030720030703020a1203020f0304331e02210c07020613030b2809 58
    0x100c005100031030080800344040511420302d4145071804c40b0683d400a030541c2c40715040c1040064110130494075428190504180301c0c0c2080140c24060182c0d2088030488034940400c1104012186500110a80341400c0030000d144035200340e1003c00f400308001600b84140030092100007071115070000c271050302c107140c002c0a4404c550b481c080d055034112000c48031540203c08001e2078884040c00ba03401801c1c90b1034045020304140300050f025101c0a000a0b081151901d90303070100b14500c191034006641d4203c1140e03562a0b090a00070b442e840071150450320301c0b005c0c080c0101003c0c400e0094034404102c420100703241d41c40381e603141c0c62110762109140082d40d0242001c1e2034650000301c07020f88000c40c80440824442c0f007030400360805045240e05055000c1c4148405609252000b0760309a2944514403461000c0d1038102d0a40004d014081c03009602c504000344e640144c005151f60402101e21940000e600d944800b00c2c0c0002202c3d10f500811903909520540094111054002c0700c4011302491101780 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 223654901 1250 223653651 223653659
    0x90705060f07061416020307030c11010207080304060f02070f05011407030e06040b030103060b031621060204031b0f0308090114160302010218040902030703110a0b030a090c090915050907 82
    0x50390080e0146800141e04d000401140c412201508464482c0c0d51025500d0003510740e4002e0b040307001c120009020740340b0504d94014564004c0045a002d420b2800c200c2e074030b40d652504020300341054040d2810043c01038190000e5442c000240c00815147c0503112a4440c2c9030701003d500711500078000950400c50380f501c542415882c0d01008201406034035002c40d03603a6040d410700708141d40c00002880d01035400001c070310004860b820629003e6032040e000c1100301c41001d410b540100b00d00c804010b0001ca00c001800010018943e16a0358030070500312031840190303590324202030030300c2c01840098640d0b507080122000321361107948246000c0c03051510060808043e1004200445420001103003d031394001036804200c0c800d0362540401490484080c03001060720380c0400c0d1100b08a210003010742611441042d010340c0c0d99569500038010fa0141f640c0c4030f203031031070540d406480d0501003075400d5580c01e04045900c260b40d010702c400184d0002809007102500301800d2004144c01001011140541c0340c3c042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 223656151 1250 223654901 223654913
    0x1b030d05070c170703140a030b090f0103020f09070f0f121803030518102a03150b0726090301020706090606050303131205070510180608090705060f07 66
    0x40c0c0115503540e0741c00a6012580f412030075108010207801d428210900c80b010019600c511904c004482645805e0384590044406501400b1144215640a142c120811168529025a05049070700841d4009802440501400031480741a20600005116459000303009070280c4210301d80c50100c0e1401e980101410240c2808507417a5801100340801a10760280c02d1542c107000303050300303d03680f03014110017a25035034540c42e0b4449101d003042c1120307034503144007840340001d051000c2802e10000e429414141240e0000600429941c010b16100904440e000300300c2ca80442d0564486540c004030301da00c00b1038032915076200d1443c89020191014010420000b203a1020700141c02c01601c140c001107801421440c0801c20395205801881c0030382c0c010f00c841e2040003121400c07001120003041951032080824102141050400c0c3c2166801409801c8240411035004660144845a80c19041c400703a0315440102c89800041d600340c0c1c02a408010184540d00d400700060821410700841c0d146402d18959480c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 223657401 1250 223656151 223656161
    0x10f12020711090a09050c04180303050a0f0204080304031505040305070209040f05011d0601050d0b011214120a08150102070605280809070b030105061c3c111b030d 72
    0x454603d0717850b05110003c00108000c3d281da8813004072010301c0454103105400c142da803450400501015129004201c058205078000814540c04800641d9141d480340b8280e40c0e0b0390301920003110b89180d079800caa0106ca0480c41a64060350303050741c0f0b1300d00d4181d10381c003000340d80d0001901c19105045800071003000500248590503046034403590035071000385416911414140141c0c0400c2c02008856041e10000d00400402810340c3c03d00300750030001207514102001d901048c0c004803400d5100740d030b507141d1150300c41c01d0145c50100007964031404e031a80c907580d2140715420300c9050740c1d0160303125580a21109004801404041000d40c1012a40e014194060010900c07400308a201069416080c404440c506000d09406054003040e458a12752411002c9a464414504c03007246030760002e0a164100c0c520360308131000c401d41d1046c00e007021084030428500c00240107914103483c804a8110240080b09501441c002c183c4400e0b1000c0c02d10030007084031401c8040c046010100ca000c1041a01100680b501c15 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 223658651 1250 223657401 223657411
    0x10e0f010609110705071a040803070605061e210f070905040201090e0f010504021b030d0b1e0a050d030516080c10110712090503100b040b010f1202071109 68
    0x41203981c03030848080c045503d00f03001c0d80c1041104000c4000030810004000007200c48980286842c60284d6583c0b035a540102c1e0044c081500000a03813000340a082e41046006c0d003002c60303484540c20384440100c00c082a54180307a030742004641041d040c40c24914043c40004122210a440d948240d01c1011403c123a1140c0040142981d14824041956880400040a01684c02c440350180c10080404180c100d81482414810f80d0001040c8203c07006401440c0e0b44101a50b04507a254a100c40da601c000d000f84049160080c400301b4104a00d058400030040942240640742c860b5142c00c0609010900d40c00c80c0040d01440410090780030390b4440f4001e420849409500d00c0e585600001d840c0c20300f422a20342c04a40e00c5030410b0b00400151082d8001c507040e4a0340080c0342a03d00104205c141c40000c80b40d802503600d40500c000c80900100217420101c010442214108000c1c01000f00540e0440d410820290000d0400441582c0300ca62540c02451014068800e04208007104000607089802c102e403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 223659901 1250 223658651 223658653
    0x7170a0204092f07082203020904030f08160e0607020d0f050604060c020309010818011b090801150f061206080105040305070b060f0f040c03021b0304050a06020606090c0c010e0f 78
    0x1030180d10000786803040d201c81c03101d060300342844c0c40402c1d141c40149002d41d0f0381070307501050000c00c180d84050564420800440d030281c4a07607003070302d45814058044940144000040359040c000a82c803c032104003001542400c03a241c1120b145821020b1021a41211138102d0308588074001d8080810904505026461f1041004110307500e8035250903010f88206c100300d08255401030200ba803980c2c1e0000126940407480c2d05241d4051290f000c80316024201c066056071408000c041304001827a031290742031054601080003408141030b003101044400c142403007190740100c40c810041c4415841540e070305500340f80408010441e00d8540c0c51190864105440031804a000000c04c4403c00c801014500d41c0040119042202d075178030b1f0808904038501d5100824400d5640d08040c8281500a5055130000c4803a04806070900001103940b950760f510500895120758900f5200007040d910018a0601c04d010140118000f03403074540314109603070014004450700355201e0510010a01c0c00704081d00c4a00ea40074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 223661151 1250 223659901 223659941
    0x14071b05031603020303030604091505010306150503030403080306040c0c0c090606200607030203220507082e0209040603050d200c0612060411030a020304110907170a020409 76
    0x10080500e415500103400b41c40031200346040015035400300c1626442001554041031005c070700d15090401c82140c490826005203448004000d120070369020401e443c148101c00e0091684a00c01c050340d81c00703144802052403900b000051501d09064010040c03030685410060403601156880c245030212036013120071806d9840c0010464541e1099800c0704510f00c0c04542803089026440340707a105c0354001d00c00414140c0020108034001100ca502c01090f22410000903140c54503403800319103c480c2403207003d0b058400c0350340c4925450383d09044110f44820400c00c5004002590306644080c0d0804000107130300642c0d41f4070020200358240820982209141d451603a402d242104610003102402402040d640c040c404429054541d0700c119544044009030502d081d0f81c409001070b0240081d000c1c003802841000c414010520703006e40265000758490529103070380c034443d0400c0c40102041100c801c1c001459580380444100b96640c01d07a03811113000300c409031602c0d46941d000c0050b01c40b850a5001100984 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 223662401 1250 223661151 223661159
    0x1020313140901090b010c030e15070b01090b060c060114040f02040608060a0b0a0c082203080d0606080f0403030c030b03120a080a14010e10030213020307180b0a14071b 74
    0x1602c035a01611208404102c1c40c840712000030800f400c0a9801400d021140000040b01d5030f400d0a44124140e0ba9107440d0750700c184624200d000c0e48400e11071030040900b07000c22002d407490510b003544c240340e00c107400400d0968a403841340314038034906c0ea600c1c94009036a01a03c0210100e030b40020706c0900003a45810f4801c1c20700b20f00b8005c5426042c0d00c02e000d070b0402800701c80d9806501442403201c2d513400c0564142c230b17440da511030360110403c04481c603a03448107113150000070002c1c0280601000c000c0b1000810082d80c0c0d0301404e641c1c1d5801118103003c002826000039000130702a5000c80b411814a29002030b540030072201023441c1040d40c2c466103007045804a0b12400341544400465405100f100e400e121440900001c03240044060242c02c1d81c20030078100003001503c01c02070140c011600102405820140320081e0b030003c1d8000c1d03915500203245603001c11030410940c2071620458803078207000f034a00303a8081c2d0103c1d40f0101100c04092044800c0080b900803070008c2000007813800da130f4072050760941c0c90 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 223663651 1250 223662401 223662409
    0x1b0102040e15240d02040506030423030304030503060904050f0105150a06020705100309051018171206060901030608072d03050c0910051206150607200102031314 71
    0x840c4001845003000c1c100010b400f924051855450b8442c0c611010f85500201c20004040d0141d80c10958202201002704814842140100e010b121881d0f080030b070740303980c00e00c0c0c1c00c0d13450303110449014000c250100007050700c0d81404120250b115010700309548840c119a5101400e444007918110060041c0041c420490b281c4004040001c0016000070400c0610300004151138100c01c1100005050f910b11348401406000d0040c049815500f40040103061003c0c0c000d208100786500c0b056813074858049500818180c584200c8003618a039850302d01c03896540000708030f95980440340031030415490f00c0300003401c1d100400100006c3c107000c51045000400c0070240b064049286c0c091b10030b5602c038110080010650200746861446c1c1d080d13503070f6031255071356002c049514a07041c1c0c025a00418a140450500302c0007203411070242d015038840b0800034090404002c0340d801b514001801401c180281c0c899000a11071208200740f4040c01a83c0c140344907096001c5102d15284e104441c40001c00c43c500e00e031071074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 223664901 1250 223663651 223663681
    0xf0607050d0309030e01020d02150718060503160c2a0b04060201020306100c02060a050c15090a0209010602062205010f02070c031a0f1503070512250302030c01051b0102040e 76
    0x100030707c001e0507554000b800080d1380d4170491000e403012034150004104c0480c45402c0703002c10f100105098030700807379603200014129802280e82c0380c240c01c07440450040ea0b5216030b488010040d045209030b000030390040c12145c103100e40c1000d908155050508001178242d0904082c1c00249499000141c49141503800d0215003652400c0705410440946103000059445100b62510480703641342150701c6044980d4240d207412120003190303114001400411036079641c001070041091788250f40d030900590381d89105036522001960b0170003480b10700302c2c0e0340c100c107824071042c0000c01d0380180c001151409a500d0b0020072641f08100c00d851100c0074060900034071500c154914004000c00c0b03101841864940c00480502c80d001e0046c9140700e115851009407542d007004900c0140c500201070a510807800108299600c1d9990300c441d007a1060705d205820142e90340b03d0030310126600900031b00700104031400111840c0c0c1c4041e01c6040c003010215410169890309101074009850045021400b03400e20213809103400e8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 223666151 1250 223664901 223664927
    0x6020f162c191406030d12020d091101020f060705032a0a0905030601060f0c03050a020a0c0e010602010b0604050a05040c090e040803250903060c17040c06080105060708090f0607050d030903 83
    0x81882c1c42800881e40f000190351003007070f401d89040840003803502543d401030b2003a270300000e41c850700303000c0582c0620140a401c4e04602c0c00c00d0f000c40d90a45803805039140c8403002110703148007080302800007070000140700c401000b01d0710702c1d58818243c6038040388810741c4e035400281c0d401c0005015028140900e04082068070702400382750600f04240d000040e001400310280101c0101040380101d45141d0082c020800d040501d0b612440c10300e2082c3d118040714030514824401c042c0107600741071050740700d0306220044a0541c1c42c0a0308103001c550810040c00040c0c420340390f00c17800b00b10794083c001071502d42c0c00304041e0055104201040c0e0300e0500c1030a20700c4406120081651a100381702400802c0794004d100803041348e91250000c150b4202068003580c80c1d101e00105242c5003034504040008000c003041c0508103488403516003910991700c913001c3c81810b00031050002c1c41104100900c509c1840e2529902d421600014480d9140460719521030381460070b400041c0300460788402e0804205034000a04031582 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 223667401 1250 223666151 223666181
    0x60f0301091b11030304020609120102070311160506031f08060406020a09090204210501020f1c060f0605030f0a0605040e100b061314030f0105070906020f162c19 71
    0x3c40c0c040c8803041d8036444058802841907200180c484441c0e02c0d0038410141d0440c03030720021502e90307200e42409800241e0031420302185028440407422707103048242400c030544202501070b0341140d4803160071010f8808000b10700d1007024240e5500241342c1e4810064035218611410000d44c460b031211402904602083d00315442842c018082407041c00c8144944200e408100d448aa803d10258146180244101000d4607081c032400100501180e200c0c0a56002810318910100320b460f68170440e120347c00c01540904000134a042010030b2001d4040c1c2c0d04c40c1d80200c145100041c41c141c1c0d070000582100c0306040c4031011500030805545881c40319202e001b50090301a18510b1400c0110341500e00c040b00d150207103503003ea103148200c40d1182c4080140702c6e0444800c400800603400d04690103000300c02c0600c280c01c01441815410311071500003260b4442500b29058107544410b041043c401403001135404100080c00c1d01c26648115880c440329240c0c0035502181501c41481c0e000c400c030206840c051104c1c2c0c0d400d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 223668651 1250 223667401 223667417
    0xd050f0f0408071b09150b0705060f07022401080d032007050a14060103050601060507050604021c06110910030e0706050f0c010c0305191a0f060f0301091b 68
    0x903100c0d294041e4001e07030044003a9910091403901d244084c42d03011079020002400d0b01d01080601d01a40103038031301342e461030140803519502d0041480038403c0c0d030001000c542000001c2040005c206440c0e0360000c0085c01910300c8000103c03d04982d4007410281c0c0d80410b08240010448180300780300c0102c6c02c544900e0706000d441089841c0702c601c450391501036940c40d03000040b074009104090040a2a0642c82085074051100300101d00742c3e40d00007070005903000c6c05418000a1802d004100b1504501d81c4400a0710346503440340c0821401000144032800c03104805880000040c09520603a402101541c120f5910341c1a90f00502c01c2c0e00241c2c03407110091502d000da001001401c0001e4403000c40324035290840e5151043e41c44200340340156603144a51751b08029140e013101c2d41680100d84110700c541000c1582c0301c490050b400650b0840648184094881c004800f0036041240000143c00c034082c000500d809131211005206900c00d0b44007c0402c1e41c0c03122244007400725440051161202450b0100b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 223669901 1250 223668651 223668661
    0x60c0209010e101707030c0f0f03080702060c0a05010e01150e010e0601020c030d0c03030c050f03040b0a02250b090d050d02130e04053403060b0d020a08030d050f 71
    0x34965a040c0110036045407148000303450030354082d4006000d0700001d006a9503000c5400a03070f40c0d8448407804120380c030f010f0348100400d0b404011030b40e038008c0310500036404007000d04c0c544664404e5800850180d030010420000451041c1e07040001c880c5142c492000000e480341120b0b5080d00315003031181620b80a0301e1144040050302c40014000381518000b8103903141076151200140e02d0b1510038111075405002d040a40021941c00400b0103021a003c0e403810b10129441c0c030740440d940d10443c80c41d85680003003407001c2804100c121480950003200321000600c1c182c85c0d1420107040d884240340c0605a17096885036030b81003220141280d5001402d003002054013610542002e03100303002d502c51102d42d4943c0456401a50301407106a400142507001d4001034504250514a840b0202203034030f0000011964440ea0f080040c1458038180b10f80390303a0050f61490704550720100940a60a903643e0300002342000d42000d641c41640e0280103040c03c40045658002175482c40c01070740c400421151010303802d501008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 223671151 1250 223669901 223669909
    0x15060b190302031015020d02120403170901030f06080a0c080a0302031603050906040f2103120216021e01020f01050702062805090106050a050411090d02120f0a0c060c02 74
    0x6080034a15007405030b107a41d1260b04c1c800c41415641c4c05259201c4050503081307141a000318402d070321003003141d013560340c81101c05c028481c0302c0c40b4a02c8000c149a928110f0a2401003e80d03002d0507070108145000303d0242d1406ca4044281d81680d00725030b549030072540c480800c200a40203504010010307040581400344843c0c034003944030b0080c0d190080075401c0140c01c10341014820000c0b18400e0000506841d101c5440d030854046079050390041a05500707600c00800c03001303000010310f0b0f8400c55269407041e12040e075500600e0040d401500d6400ca10552028200005a64540921890303603030180d8075442000c0c1d07010009241144000c01340380c4030f906d05810320a4441d0f0100e1155070110030f00144036268609412409800212000512002e0345000140a510f0406400410451b241111001008c5441d08100011524540e400285c407550800881009040444e4500040d50000f03244414031801c0b45402d5040c030441e4a80803200d608081c50740802c002c503000006001d0000d1b0718041b81c4180255002c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 223672401 1250 223671151 223671187
    0x7060f020714060318030307020606040b2d031002071b0509090c0603070c0b040501060e0612100b03151006030f0606020c01030b061603080412110d030e071215060b 72
    0x55406100e0000000305a88141d21703415010f07100000c212540c03072034038060003902c1e180c00340d8800703204a09100e0400c100b072900781c2e40092000d072000c0315600f50308100401140c6007091656100c2d0540103107000c84030115024070107403011500072560f040100c540c0520003282d0701e8054114500c1080344a0510180200000c2c43c603201d41c005070303100c59898403246001e440e210b511541c002d11002c101030070402088019002501114014240740c829510f80350200042e00701500f01c2e580701b90703020801a00002e1782a4200c0810440b000d0140c500240c3d02e0b0f00300c2e100c0142c045031182c5100344482810480f00b5070502c02d008140010780400c0280c10b0178020025141c14407401110304058550b01c010000d03944460407903891004603140300c1c02002c0c040c03030b002c2e041e850300b04ca080d9a03a00e1081140c000305800f41012a00c1755080c403000d4010411441ca00703400902c0c020f40d01541a2140e4000402c5c0010440880c0041c1801494898022010481d12000342c0f005900702c2160910240101880c40a06041e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 223673651 1250 223672401 223672439
    0x60206040f0f080405042a02030a050a03180605040317010504090c0506071505070e0f030721080c06270c060a030b030c060a0309151a01030e03130807060f0207 70
    0x4070b00c0c014040d50420301103a000d10303041668031900d01f0782d5403090110060846066580310301c400d0f15008280c40303004d0341c81c0d005441c2c80c040800d80030000c401003a407003a440700c880c40c10b82c11111400f1580030f443e030300c00310b540c00c90342140400d200c3d0800130040710341040d6035030040504076011701020703c060303a900c92003803018424503000b8400407441008005500030040c480e2550800200a180b4140301c0050410f44a03143d201d00810101c000d00100381804266507042d52151040c0280302d00740411840700d072640e90380055448060034026006491414028140a21440d00301014640e0140303807103c0d1548501805070703000e680326403850600e07510340c04145c542c805c0c2d42c0d0900140401e491130120b82058415850039601c5a80000d08500f040d4140d800350840e5402030f640b0100e800348003040700046407480d2350b6400d07541c01102c1111101d503100350002490210018207990500c0410507000103040704907080f031440c07500204d00500100340c0c045d01c0e078101140a480105103042ca0400d0700c00c818400881 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 223674901 1250 223673651 223673663
    0x60203071101110319060b07110d0507080706090b0307080f070201090209240d0b0f060d060c020c040f27110d0c08010f110a0f0e030a08030a0501060206040f 69
    0x5604030780201007080208540354020300070500c4220003614940d10444080d1940417840b09840851055485008155070700300385101e1a110340c0340c42c0c090b024904d103c1d038154049412080e02000078414071090000b80a8440284640303418550080c15500840e04803a403405070a10820800980c802d0170130740c100c0c0c03844510f440507841d1313048100d015191002010717400413144c50074004a5141e42c90301c0c52105000102c1040b00e1802c40003000aa5000c4035400b606000e240f40100b00d55803d003818003900440000c2450803030205a1b9924419107024039841005030b04105200c454a040038080c900b4009000d9038104a803010843c80e409014610401050401c3d01d081307800010020b100210501030b840c01005004442028030b00400701d02ea072405803410079401c00284030b445110130b001e580c500c2542405141c0c28035508080031250300d002000d4400410800d064102c41d6620280302c242e40142c014040c841e501e1030004802010790300103901010455001070304000104200401101c110b5921034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 223676151 1250 223674901 223674907
    0x8090d080418020c0d082512020703050301090509030a021f0f05070201050603120405241b06011a030420030a060e0a06140708040201050d021309060302011101060e180a06090311071a070602 83
    0x400300301d032032902302003013074014902c0003a051301415000b90245040308c618410a11265a80a5407207469006528803a000f50b4003070740c600c0180441041000300c0021051f2000103052400f0483c50082d14810740f201c002503552441070004604050040403442c01c00c1081c0342e8034140c80c0102090104440d04400781c2062000c001d040d40c01d80d16a07045460812611049001102c52490f00c07c0c2c507101c00307210340241c2e031001e4910b8101c901c1c402410740e031059400c2108140c0703811544000300e00b1803507500003841e45406241d0089001070740070312512054510a000400c14080039203401c1d0304a400c200d1045503600c04050800828941c05103041c0e038005e50a103045c544548840030000080d0040b14220107040c501002c0109130230000e68800e20490b8002d0703960301100c210807070303c00d4200c510314060181c8981c68400010418000c0c078610000d0007114000f100c04100c20ba803551801c4610340d040c01c07000900c000310421141003007002440d0140c440000a083d030410105189411440361120007000c0507004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 223677401 1250 223676151 223676221
    0x110a0b090d030c050724091401121b0201020a11010203060306150a081209011202090a14011202030c040e060102190f031103030414061308090d080418020c0d08 70
    0x840c0c00400c0103501c8412035585c0d54803117040621a612422100e041c20726030203203807920503100324040003c850703007259a6000f110080c0d004440d100048025962025228001c2c1455441441d02841082e0401c2e800182c917090004401495140e0030aa503440a030700501c24091039640202c6c40c103400c44d03940110801240130300c4011030544001079004400a0040124881d410303040c0c1b00040801587c00d0ba1050f41c00c51001ca02d0310101d018a001042c0c0181103401c042c0300140c0e105079503c0251030705040a00d2494150307030414042e0790084440c1c0e070801380c011600300081a210620b1a0b01310381c090003d4403000344d501c54000409000c03000040c0010800d40e040070180340c085c41d05e50047d00410410f072586c92030513040103034109001c9210741e034507840303200c00058248840d502a681c83d550b0043c015403500b85128104031070207000210a5814800404c00021240c607040d040303003010562002c0240e10390703405000c0103040007150304d16442400022000c200492081441d4a070000900c203203504000c070030f9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 223678651 1250 223677401 223677407
    0x9060d05060a0f09021809220203120a05070c0b0301061407020a050618090a0b0a05011206080d110105070503060609040218212b080a09050307080403110a0b090d03 72
    0x15a448a0003160350000c0c01300d580484e540007040d014401d400f00f2030b011190802448407032a41210015035143c03044013407814031042c0d9450210f0140c0001c04584000d0948642c5114941c130100242000c200c001030b442c420407216440314030090405410766401c661412401038400070444040080329680056203c04642c0c2d1118008003800740500aa80c03a06064044000c40070040d4410340c1c0b0890808001030010380d1342d0f00483c40301c104083c0900d80340da403034540191105a000010882e0003502c55001240c0241c0c00c001d404441c00300d035620030101032900700700076003126005850325082010800403c20103440300400c40d07101700016200140d407200080e98031447c140040c0c0344640e02c201126034040c11040b00080c803c6044c10090107882d2440c82d000d644c001c60802c51044640c82d0a004090f60b400d984c001c1180d994000380c0b1400201e440d9403581c4d10f13941194170414040b115400c0110b014010b00c402514103d501c1d420942d03000603854100410707040076001e5203d00034485c44140c801d00f000c0502c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 223679901 1250 223678651 223678669
    0x30f13050a0c140906040504020109061101321510120b0901030803010807050904020f06030403020f1501150f020a0b09100504080a0f05030c0702091e16080601030209060d0506 77
    0x9007010a004070561921910f601e40144881440d00c2810014042090f500d003521415001c1c0342c0c16110f074141c4030710f420025100140682401611950780b0945800c000d9065402c1c12590541840015007c9000100381220240c0103043d21510181c180706240c040c0e181c2030a07021000d80941004030b03182c0c1d51611000003500041d0401904081b03040c00003c104003e2038041c0d07041c0c0d469602503450040d1a241440f001180840d000f07036128840d20f40c3e031013240c18400000d541041c01391041d55070320740340d0010440c58154103201e980001d1540200400c13a803040300d408180c0c1c0c51810324003c0598245aa0000d40e6800c40c2d4a02400459902010501841040008020b51070781c0d018288241d1070700d410112401e030040d400d4280491100005200b00c00c2c4a401101e20514114202604287c400d03000d10950890007000f9041e43c0000e54080420107000c110300311311440d0195000e011084a030140100300300e4014021300c0c141070052081e50820ba8030312055906000c0d410b0750001d8182d48800004068107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 223681151 1250 223679901 223679903
    0x203030f07082d0103050705030102071106130b0301081f0c0c06110c07080318010302090a09200d02031e09071404020702100f0201050106080c0a0e01180602010b0901050303030f13050a 81
    0xb40703c260001c08a40c18001c00103040364080d8040e90943c907682d00501d42030340301d00d541c0100344c80c1520b22a03000924014025081104042210000319034440306850340a900a0b04984110740c00f00c0b10368407920305400406440500700c1c1c1414800501545800340c608004524001d1005e911002c07442020008042034400c3da00c2110f08a900050b0f03580e0015132a640b01c203610300c4070301111403402c107401c1d4024000c590354207001070700c42d50825141003012401407411441c0046c07500f60328040c1c074021210400203040003502c002e800507900d040c2217a026583e5a01141100d107c10327603400810a08900201e0042c046811400e4814614031a01c00090300030304c204a17000754458400462401c00030703408641c0c1da92a01ba5034008001c1c0ba600c4080540320100101c03a000306200d01080181c1040344100300d0003601c03c6060405d079844241034071901c44000c0c1d240d08a080181c0d906d4180c002c0078a400c0d072403203006207002e5003e035146003005441341c2030f0135800070320a1203441c90001c50302c0d042000412402d4892 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 223682401 1250 223681151 223681201
    0x303120203062b0312060608041407150518040e030d0902030c03030a0201060f0b030c040303050d090606080102030a0c110703020907022407081609090c0516210203030f0708 76
    0x481c3d28415201110055110b0940c00985003000c01c01401c40503119081c1620010388502042d66940e41d40d8980b80382031010400c1d0b550107540c00005240c50046100e0311607000540318143ca039084084841c0808000b40480342c829410300005482d03054011085a0001040307034004200c048060010a10f00384138140e8035030300342c4000120030703c00650650280040d200c5030901d241c2410750319000605680415610340102c0b4400704410000280104010b2003400300f0316001050300030702e0380c03140b030100c0c2c51581c482c01c00c43e500042003010304003051068114240e054100740c40710f800302d5401159203a40d28080280101c50f140d002c9280f0a008002d240c1c4909090a03c0c5200307810b82a5000601003c10b880700000300b07a204001c1104001c203914550007a800700d95505140a10b1b000700c2038081c0c81198140030510004011201c0c0c10f4171380100c0c100c501030291680c0c103105042c15446420f91040c00440c00115001072083c808843caa040b41180c024146140940c202d403140040700c0c110500100016500c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 223683651 1250 223682401 223682449
    0x1003021b0604050a1e05060601030207060b0d060c0e0d1505060103020c0d091e05030a11041b050304020906040b0901030b0603030f040320031f0203040510062706030312020306 77
    0x400900140a080300c82c0315405c0c600350041c4140091080285840006005800410020342107502c29806400214014480800c0100e03825000c50200c002c21081514001d0f220501c15114a801c0788541c4081603040d80c102441a05640315004c0070702c102c00e4031000c0d05440ea13000c500360360320030340580e80084007400944015480c003e40203055850f0a10a0059418111035842010300041203d042100c0002d4094441c010b9156103841a17031403a0b44101d5031082ea12000303020b00401d0707002c4414102c07a46031507040d03485c20180108010341900401143c49241000e00c001043d8895680c00350440307030b1042000f0360300d844d01c1e0000303810340c0a1004001d000030404a0000184002c000700e0400e451800c40d04043d000303200307005150329806031a2100b441c01c0b9503149400d50890711030b8001c690041c0130f20300b91a210b01d020440c000641c1c40c0e69003c1000c4010310800380c1511079031090810602042d0701e504208083c85c40c1e80140c900d501c50900d070940180c0c04000181141c030b501268402444070711a400c0c0c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 223684901 1250 223683651 223683653
    0xf051302090418140309011e110f1006120f02060c0a02060f040e060d0b060f15040801051f0602060f0c07020d0501020c010c1b080901110102180f0306061003021b0604 73
    0x38090303c020340c0a80700014442c240c00640e0b5404821a2031650040e540c883ca4040380a1589404030025525482040181c0b03168130f40002c4140241d09209820101505031506c240c0f01000683d0166000800340700d18140c60400020040c4684240855040c0c0754140c030386900320442420b01e040c828002c1c0d001280050501e1600c1c040c030b8014030a1715400c001e0120b483e200c4c02d083c49007203201c645000f40701d1f041c0034002c90035a04d0401e201c900d07044401410000c407400080755881071600603070302207001d40e9141c4050002d5400d0740f540342a1204e92142d0040c0b06685031040003903445901521161608141002040c081d10b894412501300c0307038003c0c00901031a905454081e000f540a03030011030040d46410003410a0340c2c41400e803000d40c611680003000204c10142c8a2603003607403100310b4480c180b1840d42070780810140280060309100b886004e07500181c40f041c0c0103000c81c0d401ca03898464440e8100034100304d4990b03255481080a04402e14780180c0300e00792498100203c11070000404401d00ca1001040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 223686151 1250 223684901 223684931
    0xf02030d0509010c172a1e03010e06150316090909050a03120605090a1d06040b060f0402070302030a0804081c020d1b08011404090b011409100f0513020904 68
    0x10702c3c2400070781e0b03001918a210007204d42040c40a507020b005106070550740600391302148806c1000100013004062500e03640b26810400d0a45245001c0c007903203070210040061500d0110801c1d03001c6800e803640c4c6c40c100c000710000100c510000f0603c040e08846908410b400301e00c20300302000900f00320407081091040c1828055561181300b80c0480000e103d0302014010340b00180140c2045480242c42c0d1200340e103400400e04003401100882140110500b0000d03400300804018407405680140d40006080c104102071019014000c83c0c5240954010803d94001070360000495161120500e049002c1c2d40b501d241c800254415906038032441c0c1d040300d52140c00806260700030596500505402c1199030202c0f410450b401943c841d1600102e20324500400801050303203000151454000c2c40002c45002542d901c0d030540600ba04040d100c07080510402c0c4440c200658201d40003409254404401c0d40f500440e1007924409004c2e8a008001603000b0003410307030807601503a0310900300400600c94040703c603102c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 223687401 1250 223686151 223686161
    0x31e0703090b010305011406030d05040608092b0905030111090d0c03121106060f061608041a0408010c0206040506012112030c120504020a050103020c1c081618060f02030d050901 78
    0xd490b85003150220b00507140009021002c10f40542f10b0303c2c1070519008082d248140018003482e01406401c480107803c007010343c0004031701d00360310380c041d55901c1180b03000030310580254208500a030314102c9880920708188050f11a0b005040700c010000c0c40e8645031003c0e103100907a1005008182c400448920369800000c140340c918958001c85030643c0d568020040e2400c110340e07599812440400060140e103000041015015000c1c030b049a280c07554800258503020250b903003034105402c0120302448142403c0c010050300108520080406003015103c10383c0302c500c184036213554550449040b0401d04030000c14400386175000b030100c144e4402801c0024000d840f4021140000450140012840c091180324036030085070041c03c0a01114100341c0150001d502c803000b00341c564403c00180b41c030801c07900050000c00e00190394414200f070030b0281c10701d45000342521420302808001c40d000c150310a41103e401c41150241c0c504030f8140c004214050382544609885820345c1820725003003009425054000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 223688651 1250 223687401 223687421
    0x9020301050a2009060d050c0c1f11070209070f030f02160b0601080403050919030204020c07060e0a030519060b030601170709050c07110303040503030a091505031e0703090b01030501 80
    0x1c2e00064914514240c0501c50801340552040301405080f91140d80c035400254007055940c42123180c0810719000625010f03000941c110030240d50f8020340505074a60183c903520503841807410b070030b001450b0700050100c00002c01c0101007060088002c0c00f098400d40141070ba00038505801c660306c61007604c020071048840e50080c1c807114a00c2001c00c0ca1035102c1c45145114907013554070702d402c0002941c10030a4902c40002d0808286024403c0400566100d200030b1034200070300304c01807021f10314140018028040703031014148507441041c070030404030350003140610010b0010703610140c114007240740c400010480c1409184c0c1611403480007041c0c0c40d041d8415407446454800894100d181e45000903425260101c60f402003802c4203005440004000e80d802400d0b6010050a0303a0401e0f80383d0011a10719040100c00d400094120b0504009402d80c20341c18880d003035050b240051035071400702c08080c0032403141c0401c00100307110b01c4009600b80b440f907409403a50348d600440404107560b681c109513000e4841c5c00d00b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 223689901 1250 223688651 223688681
    0x71101020c0a0b04140324190c111e030f09060d0905030c011a0a0e1008061f0e01050f060c030d18110d020109062d0f082d040609020301050a 62
    0x300e18200c5d8940026201400780314403007207480d80d4056000c5a1071105000d04004c1100300b06102180014900c1e00680144005a644070030b035820303042031080e183c070050592100f2744011420030f0b00020000801141e2440351218801c0703a8902c80c0c00c000c9111403040b00708821320749150000d1001000b00100003042e03030b1003010000b840880108082c0628003005d40d50526070101211800f001803c10740501150b100890a8029000c5a1b42d12901410101d0071141c04409040112155035085003056000c0c018080b030002007081507062101290490800172829441600085120540b28504204071280d042c1040307003c0c0b01d1074840e0114460907400d249012501c05400e07044880380c6050039008250392540503510340b11007510f403000035180301c1d1801004960402c615444405a100460108150884165555003552115000080c6a904060441d03089001c8142681d02280d080008034040c0700348803031a1510319225498003100130325070300c1d100a401d94241005c02880c07620a40c0010501c01c3c0850b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 223691151 1250 223689901 223689929
    0x70305030615090a05130b191e150c02060f0a09030201080610020601031707050a111503092509050a1a06040e16020c030a0f0c09050408071101020c0a0b04 68
    0x800d146803540501d01c4415041309561808102510308080c00d0405c800c0c3c0c0017000a16503d5000114801d850401c21501c40316200c000f0070000f8401000c03c1910012500e00c0240e031481c10594030300c18085902c4000700401418284000543d519042121064503022000c5030b955a0141c00240c540011840f0a90110f00c069000411600785081540110300c032941c06420315170700310366508002c1000d19022001e0f5810502078403000460800100100c18060180304610303200806c10401c000e0018512503807040c0052042c00300c8590006070b0f0380355031146041000e0b020240c912140844412582c8648200760810303060141da00c4a9a000c0030030b0311000c4940d5001c4001110a1107243d20542c4601c0913409201400503080304900d400030f040340003982c41510724a20403140000c1c6000a00f110640314421284074000400440c1b10115005000d0003905100c1c0c0d00c1c19855001d8140103020b40907202075880301c0713100040d0b8070030b010038401700400410aa036a181c03510030f50a810f800c1070203001c110150700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 223692401 1250 223691151 223691179
    0x606050112020412030804210804021003140408070303020d060905060a05010201050c0f0c030405030303010b12100b0a11010f15091503170703020709020d05071805010504090c02120703050306 84
    0x50b0003282d058400d0303100c0300c40c541c4400707940465401c1d80007007054465801461120301d40305606800302d415401169500b843c6804c10303004010741c1001840101c1c0130305241140072403013800d640c46900d6206030040120340c2c031213440303040a0b4043e100b000781382103281c0d29112010441c0b000302d900103030240320243c40c8020f070035460b00016822514141c0e881480320105000c0051480b42c500020440c8903406000e4030304050baa00007003851a00300707130006010b400c008155134110350f15407041140d2052a40c500c40140c0e03460070a008055100b258200c00400051001140040509400513007a020340540c1c10014080c00c084c51240b00c900c14040d152a03541002c141d6110103114440460650341c1150a980603003107004c072803440e50360068400f2410b60054060010701801d9510290140c00481c9202203018a40014002c000b08610040500d0b940c408102c00d000c0d503688078040d1015030720754040c0010590503c00d000d902d0001c80707a240a09012300064030300b0030540d02c00c000d50300541d001e0f6294110400d1b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 223693651 1250 223692401 223692437
    0xf03252103020d32100b0c03070602040801020717070c091d120a02011505060a0e0a0909080304171c0f060b07050d2a150b06032802280e0603010306060501 68
    0x30f5510510101c0040d20600070302519500070f042c42020102200c0c0340c50300794ae0754a400da0300319074480900d595004c5419414001e10400c0c0411b2640105201c41c60b088a55488542100080c002e44401565900c3c81c0c0103107070721899626a45071007850031140c6000c00c1044180295010180a400650030622410704410140102500351a0020155820302c000c1000859140c01394444103039019640f00c40004425184d0700c00d0803201c2c0d00071000b40d0364070b28181c14030031a180c002862180001c6420080200d19240450009007205106440400c1203c04000b00317070040c000d103400c8408090b0000a192080000008070b000c4d15152580302d08225000305003800802400c11005144840c00b04102c450028100600d07403c8601600c0304c001804030100303004501c0c00c0d00110b0b13800c000c40800488112035422892200c125a800c0c80764150300e0b09000349060310242e00411000c0c00c060704c0c00d1102136006401140c46c442c0581d0068a015160342e501c2c144080a0000e074031076035011800e20304440c030203522 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 223694901 1250 223693651 223693751
    0x10504030e0d0b0f07140c07150c1a091204061d1009030308040305040f0909050106080303130b06030a0b10030b060303040302010c030e0109080f03252103020d 70
    0x1800210b150f60680c0d450000f19035690000b0035030010440326100c3c1020513080f07440a024005100c00041c5003d6081c1a501344850719004034840c01d0010140440b0b00184029101d80c0000782c0800c04641036031500240c1ca413502407180f5102c0700300c1e007012402050701640300d00202d1068808010b00568035070780100f070280781c2849038081e03800680170680a002290164141d944c11612a161840c5442d0341c1e120350801c1c8080303c2e00440d43c402e4982c0701480502109000b19006004a0b0000c0c61440c00c00c0e0200707038248016210001d0500b4100c400103003150f50b007488680c3d1130030307002003021f00c20f85054840c1002901e014002180e40c502800085411410000f0a41d0290ba6040c0c5945a940440361026540000c181035100c0c1001444d200100b5607001c1840b51140e00c2c403561004544802d0614038400e6120341d40c40c401c02903044020040d2021581d21a010a048900c1b0600303a41103000035402107019216005054052038182450b403031925041c81d417418554100c0d00080c8a418404204d900381c6c01c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 223696151 1250 223694901 223694903
    0x1021216020a1e02100806030d0807020c0111070305070e0405160518150307031202010c0309020a05010809210706050c0a17070207030506090d14130303180314010504030e0d 76
    0xe44100c11950014036000b84401c0402c0543da50403080e03a20550001c0c10300f41e110803038000082d00c1901400024142041700c19442880307030030070041078980484003d41c3c44000d509982e040095609000314285018000c2e4000345802c50141c410864540720100ca201d4019101110184a81c2c1c079510305405a440d0060182c6000919401205942030368000c1c40c40c0300500304801186801001c800309a0702080b41c1d000461241510054259040c80003900712028624100c017418282030300500165038105801080e21001d08011030a42c4542c2e03005880e02e0050380104000d80c481845010024002001810685220320024002070b40e40795103038070841c00f070b02c2c001c4070200b003c2ca0700310b41c2d110343c802401c542e1100c1588100d4844964903216030f0f280c031405031001034081d04440e0542e08040c0c3c1c0002c080d9065004003445074582038002170500c1c002402d610016041069402e01541c03078081c41c980007130041da0081e09009008289411040c001c0c07000b0f0782c04070040f813409850480a41081c0714403410803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 223697401 1250 223696151 223696153
    0xd020706080a050402041b11210306040f0e0f0a110103290f040f060e0702060c03040b09121804060614041802070519050f1501090c020f030c0102121602 67
    0x80c0e202c00c4041c0014200140049920940f01d1030f080344400040d01c01c14404011a95036005200e510520050400640380c0c84c02c3c80345002c10003800c4c1d402d46801e01b2a500440141c50005101512055042c0100080c0e0044209805040401d41401c00d0000b40e21740b0060041080b082c00c0c4e0380480043d41111000302c002000000030f1a0b24045802036540e0703410f54942e0280c8241850040340001a0860301c030001c006078440d565020500c042d0f08501151980108c3c5030001344658141900c1c840030074000103000070710084490000480442052102000304920f8403003482e210b40719a40c1d05c4041a842c4407420380290315000c800103032680b0a00321490200c9503450303964600360400603011034280c40f921841780440e808005640014078104813044100040300c51400700d41006140190404044101060082d48124a6140342c0e601b00f02d8000c0c1198024140000c1444007d5400d90410070044030540c0140004110110100c00640003896031840003030820013107940340445601c04000c0c00c0115001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 223698651 1250 223697401 223697417
    0x3010906080c090a0b0f0a0609180504020306130606031b1401080c0a27030609150b01121a0d05010b010e120a02010318060c210b1e13050a0506030d020706 68
    0x44c2da4540e80c088145800068040b40b0400804408945140e40d59072201e8002100800104a61b9000303004c050036050f0341a03014803090610b500001d0340c030040500000308100c82c125120341000500d0b8450001140c0c4461072480201e511451480400040d08c00c1d030b2030407038000d034400b00f1661085501d98481c00b0100d9010b03003492040c51040303d00d01c9000b07815240219086000d6a10401d070001d4010045100f0307480072800c3c44107031402c62482806940c66081c4203007011120003490717800c00c071100d1503220100400580301400984200765544030107811a00000145803801c03c1c0607040d040140218401e03281c9100b10b210754001d11000010301803265509400c0420300c00700640c0310b9003245000359882c41841c580000b59444d0707001220307500000c0c400412140c1d20180c941d010041d003800014103001e00e08001c01c90100c8045040b00092142c4407502a040b01021002c43c1d44170410040a191043c00801c051f25004420900502e010703250540b0900c100729803403462520024001313080c0c5a160fa59890 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 223699901 1250 223698651 223698661
    0x1103011b0f02030405040f02040807061b02310b030118020a0308130503150a110405031009031e020105090f060c16051e031e03010501051608041a03010906080c09 71
    0x1c90440c400381034400c5000801c0005039980e00d50041035800001900016500e130300d861401031604505500c50001d0100b04100765560324582a900900d0310b4068415102043c2d003490108441005070246a4010700140425000415075a201d041060f0056000b0004002000c014000e18040800000c0d4410360b00c24040c00000c50710005401341544c0f03450902000d9440e00e001900b03051035070034021061079019042028031640c50140d450400c00590742245424100400b10b034a40c000a60898071560b207900f407400030140b10307850b4039001c40f842c00d040c010032400c2c604c002030107000244c41044951190031038201040c0b00114000c3e00405035640401d180448014180a0410341c803181542c250140010f8407400205902840100ca1140c4c405169104001d01444034104c0109002d14450704042c07006004590300725041f02c01c103202800c0407800c2000d05262100f41d612807900b0a8440c203100161168002c00d100d07001d507060b149003810070b200c020f40351130400e0740e540310030400194450381c0300c00030030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 223701151 1250 223699901 223699907
    0x91a1008011211040e0307082203030c060207050c06030c04090e1504030f051e0405040c02070623091305041403070515130c14040c0e100e030307150203041103011b 72
    0x80fa074002c00340000c5110000f0400150443c2c0201c06c081c0c070801000a18000d0803a915034140e00c8540790f181700d00c4011811500e008110000d0054010f2010b0750016244050000400c941046c0840041010341d0b24500000071900681091040048090405040e09900100496480d0501500d035030480c20a541d503460403a0301d10030343d922407014030204000e0b00389641d00a98403825001d11080d05c0035a0345180000740012200030950500464001701c0042c81001d43c081d105400f20808000d80b007242e200c001890100b40d01c914800d0f10b42c044420180c0c44442c2d40f00390440743c0b040f07000b404d11056500e9881110f9440e807060f0344000786103400041041e05400940c0c420150804001c2840348083c01044c1d50b18144244540c00074001380d019032034565001e18041c002c011540d1a50b1414032a6101c6480203d0608a20303901030340140320041180745441d0300c0030801e940f48540c0026a00d000103024480c5040294820781c0c041d180c1040d5007141e05044d0078140603102198103580850114050b1401c011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 223702401 1250 223701151 223701173
    0x1c030c0503041e08040b031f140a17030d2f0301080d0311121e13150f0e030301030317010b0903100f18050606040608010c0516020109091a10080112 65
    0x111343d43d0505010128199115101a510a403107001d985124580241d8030b03144c640245902040c200140b58001002549031100e440c0201c5000968480a0410503442c040c254003400605104461402003002e034030005102c2045101d81d00742c002c04586503480000290070744070902a00039035034800390300e151020703120fa4464080005603003071b0036060041d807031504c1340c035902d042e218030803014070f030410405607008d4800d4181d4001101702ca0244440d00f1581c3d540551003030b0400901701c01a52031141c007802100b00c0c0c10002140c440d00d02035968030f41c0c40e450040c0c10a0035803030281d0b14665985001040e00d60f494421280c0300d080c01001000700b4416a905c20020303058101660060545a14114040c00e4009402d003038014812000f400702032030200203100c100c4000ba030190180307a0606078080c00090700728046a50710740e00ca04204020b080c640c00107944002c0302c1d5001340103162400380c80c2140d610300141c2406058030204c43c0c042010700c6500300bc5440050a010b00280d8605900e0305c81d001406450750 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 223703651 1250 223702401 223702403
    0x10207170c030711060d090f050c090709030b130605010b22050f090601090305120c1002031e13080d050403020c0a080601050609040e07030803061201050906010b030411031c030c0503041e 82
    0x5c1e8502d01038280122005540002c0c0c0100c0b9999400400302e02000300c144800401e10302c0c2500c1440c02494011002000c1616074031020380350540000108101c141000c2c030070140107412072018001940d4070540e00c7c3c1a544110418601180c50301107928441100b18040700454000070b001c1c62001c0140c0d0308100511070080c1103039050126400000000138003d202d003903071910300f614080d07803521022840e0341d0500c01c40d9980c1c5001c05204204202905003402200880c00c400d0406c1d20070680e845002c110680c41c800388024040502c0450322150b00e25154100500c114423070b80c20740c0d581218039070038001c060000e40117aa001e60050001070180d402c1c0100505858180180301183c164810604242058000e400036a00c0d610008200020fa080c50f400030103503010084020442807500031905a02c8074010700412007800300c0000840c0910242c1b2448418504006064800d02e014103440a07507003510101c1e401001c80d05140b04822a41d0041094920903600125240c01b01d9080142c00d50b2512071100c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 223704901 1250 223703651 223703659
    0x305030c18130b01020d11030a030b01111c110607080105060307021f0203040b090307150504060608010c080103060c11060406090f1e020310020a20070b0c010207170c030711 76
    0x8071048140d84010924228110b003003000110301006000081c146400c0f0302e542000c1c45030304d42801503c0e91000044600c1203c1610780000d00441c620012030700b40018440b9440d02e4482c4078000241040240c0300c5025403419900e548008801c0307030140a490307803821524030300490341243c0100001d0406a00450744030080344113490390b84502c0210a00034003c3e22060740c1b030060303002c0100800c2002001c55a0b42001081d03000310308100e01b135543c04901c0d0606039030110350280c8420105007040a540c1043e406418503038001e000c80d2907040c0300200141401d200507914181000c000e080f4860180d0011104203075242d018010b141d8864070740d00081c00a4020407540c1d1010081c514000c1103a16030300210a90455482d902040c08600401d85807042c0600031001c601d08c10882c1070016074001c6410f030100030b407600000c0d000d15042c0d90307000c1c2020103990048002038000294041c0005040d4010b0412500c1402c2c8590b02e802c241d501d070b200300d004401c6a290300b68030400c030401c00f05903801624240260014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 223706151 1250 223704901 223704937
    0x71a190905030f0c0a32011206080105040210050c0c0d08070506010f090c08010e040312060305100b0102070f0e060d0c080d030b01030e010b01080c130e0906070207120305030c 77
    0x100881e10340f801001c100e05503a00003404549942c549108504014445000c2c80704070074100704481090341d000410411030f031007201d4181d91126401820788140d100c03d518001c0188650b00c000c0c0d40e01902080340c040f440303402144280c0d81c3d0540a81c00351081c11192030002d0124550709000d1081b000044601a258414184140d0001600400c98a40031341900489070340000c2c508810720080e90841420703201840310080050105800600c011039020360180383c4a460020700c0200310005003a980c02c0079005000300c2d400006010003582081c1403076842a402c44001a40c0c036841241445482d0107061f500045200c0840c20914141c600c02c44070500070200301c0102ca680d15141460f05810580d994003080e107400c10a0760b19030701762040303000070000c58009116802040c00000d084e41030050194004040210350701c641c1801060191000d41801900e115182c123040b05115a152007c548660061041f582c02081203100e0030101001d46505031241e90442d1507914040702e1903000520b00d8981300110b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 223707401 1250 223706151 223706159
    0x60311030c181305010f061d1003050303070305070314010b040f0801050f01090b0a08063301020a0303020a0311040e09120a02031204111f120207020a09090f2003071a1909 75
    0x5e03c47c0c0320040c18540180701d0b0b40c1d8841000d2a2850a00130242500780050107000c0012410110452b64450021b113000501a540d00d1026030003401411400110586c40348000300c0c008134500d00420580b29104500f001c503a85c0d0f000c6c0c00d400d07548100e801c00104013002004100f98885500f00010a080c01030450f0317142a1580c02e160b14100302203c42503a0a20550a91241c65042b03019040310000b60303506522100101c140041e50303c2c84502001070802d0b500041064903d842540036156003006044240d40c0daa035640012803040205803800c2d85103000350800700d55401d881c0b80c100e80401603660051070400f02151203c1c01240001041a10340200e08a000502c50f5138080417001c0f040c08c0e40c01c010384140b0720000f004280c01c60503142c40c4c020740e204000400160b681d0200008c125811400007240e01c0440c2d1500055030000080c0050250074644405414010000e907010417000b003e801329080a541c41c0f510340140e400c918a010034442007003000d00c1d5524440c0303c220142010b02d0404401d07580d41e03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 223708651 1250 223707401 223707431
    0x10c0b04141501060f0302071208090f1006080d020109050a1113020c100b10020c04090813180506060406050306061b030c0a06050f0405121606060311030c18130501 72
    0x140050302c0d2546540c0b903005010440d0090401c00c00c0c00140d150440c00c0003180e42d18040103182040040701800300304400074034041810400a0342840c1000159420300b400341002c0c00140400303028032001c0f40503261001912038070510a403400660407400400180c1c1c1c881d120203070042c2140204641000c5880d010304040305050004043c1c92902c0402803208820b000809011643c0071604284645e15024101c07903c1940065240c0140c0422180014401c40502e1304840a00c183c0b50458600611210005440702402000c0c0f83d06040302c00d4103004c1076403080200542e43c030542c025040840d1082c00400d0762170406101403c0107050b600d408003103485c42104254690f4100c60700c801c12590004411100b00041130003129001380d00d60000501c281020764078180ca900c40208802c1845101064449002025002c03074425150816402c001051701c90400c07880001d440d16000d4001c0c03055001c00d03181030500d10344c0340e090703460356400c004600e40b641c40900c90070303008014058a90350b4039881c81d0385014130 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 223709901 1250 223708651 223708663
    0x70804091a040e010905071a04050306101719080702010516060204090b0406050913031707120506010203130612020f03090d170c09010e0a0305030703030b01090503010b010c0b0414 79
    0x10035a036032071500141c100104019190038200d50310380b076418104080009070300000c640c01a1a440d481e0b038501b01e01a802e203580c460149502540e41480750390140054010061100000d075460b4821a15115280244560342c40b00512048560040c0b8030901e070012884101c0644400351052400a282c070045110b40544203194200c10b4801590014040103600b0440c403403411000d00661301844107915090000d0960320006142c14111007601c0440d0080610600403542a40f08242c1002c03010b040000d0014001c50002455215144c6008085002c0e9800002920700e00e02490240000241c18440229400440203607003184d07a5400740702c0d501c596044400903500c01c08001c0010203080d441004010921031502c1a40041034041000b84200c80b1860800c845d0310340400c0c288881d04462060200302c0160107a400900140008211103040561640150000c00c400f60f981d01c400a48540c101344c00c071107911901c14082041440ca03a0005003000146030f5010733010b1041c07840c5200c007203000c0341e040c00c4e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 223711151 1250 223709901 223709921
    0x8010e100e090d030e070e010311150a1805011704060c020106091d0705010306050a03110126090714030a0312020d0c050307020d05120f06030c040f0c0e0d0302070b07080409 76
    0x5080095550790f01903141c0b040040e680c203d82c000740400d83c80c11102806624043c00054000300505244041503140c01303c100c03000580140300243d81c2d40b044500100740c1100000340b2114041c61282c001001c0d84111f80c03140c03011135009000d407000c0c4c0315a501c3d40007c001c2d900d805800c0d5500c03090002485206407184010307032a05032510704862500b070030301103052113815080103050600d488428041c0b0b0700d0310902c2d14143d90340700078040e042d034800c1c0c00107036824843c0307103100c0c1c0300a5400000d58002202401d0a80d0240700d428040741d40a5884101c490304000000000603010b5010441c3c450110380b145c05185000001070f40c00614284088618200b550059480d0344007140c000000d0204281e4100010702c40d64001c3e16001b03060551b00c54445030f40d074078054041780715a100400803840d260f4003802420a050b40040c000c12a40510081000c05450f50140c9280443c00c10410040d060510020545010754550f0103801041e04003062004903401040081e180d00c41c09010100f81c81030140724a02c850 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 223712401 1250 223711151 223711153
    0x50108100509010803070b09120403080d110406030e0c090c18040b060f03011509061b030e04150503010e0f070e0c070606060e04110a140f070f0b04030206060603010608010e100e09 79
    0x140c1c1031820030010300d020141034404681e01c0b100508509c01c0c8460146c60075240d108034a10354a486039114074015040036102c481995500090001d00a90560306c40c10f582803161082d40e44847c0d1039000c1002140f4104e0b14078a0241c010803050341e11030b0b090403480d054440b00420004460070020b01040359a0040c1c984600c8080000005001c4618001d8a03090518110f203040a0b443c0e040c00c1700242081e4071140d1210155045010701c10805000e4046044c0e41c901c041c00411034060b5030900e90154481c00c1c030609020354a00405404400c00c045050012040c0319001070031820310f00804a982104010b0a002a0b003d003840b003440000c81c94022640145440e942d0510341c90150000c200803601c54040c1c1c91240c0804001c800e10458202d4454003404040800c100d8480da41c0c0c43e520002886240c00052580181114010802c8010300d4101c2c0142e010781d00f03d880030380d01c20b020f00c00280710078058003000ca0b40072801044111148103809a10409440c01d00700141e540d0984255250f205644030402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 223713651 1250 223712401 223712407
    0x3090604050f061905070306050301090501060302041505091602070302090702030310050105030f160e04060905010e011421010b0a091406010f0504060e0d050a0308151801050108100509010803 84
    0x41c410100594101105078501070b20040c01c0502d0500d0212003000d150794040c80c2c03200001440b050090380400d0082030f000d0001c0c0202d0b80300d840e1080c001e01490001305d01c55890310030b520103c84034151400c01601e6001e004280240c841c451400d07403a04282d8010003c510030031030044010b885410805001b4001e5030025522800c04564003004444140c1042d41082002c1c410000d50104445105820a40602241e40e55501401c81202c0e40620300071015002401c065002610940c15030066040314401030140c02140d0f02d4000455040c413401e0340440c2e00c52130100c001e103007449110700f80801c207000c4c24000191020003800852051042640048036241d0b4035003055141d0440e080340c0c1340c2d2002091826410525441030003509038051030042c0010000481c4e8003000c0382e11210410018280c00408484c01c01043c3d190060401504840402d880c840800c03612105082400905070505016900c004a40c2c0c01c100c01100c41081c0246520a02d41e0703c0d800c0010143c44041040380030b0080840030b15a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 223714901 1250 223713651 223713653
    0x6120f2310090c05030a23071d031605060d0207021915020a0323130b280c030e010e09070e19080703020111100f0c140307140d1103090604 61
    0x200041c9694410b95045040c8005400c0d240e03802030072250f22080410740020012001c14840d49900c800c00150741100c0345c05e005210750b2075005048220001180b0210b9804160724070103058499268002c1003080025004c800c0c071040c03819001074081c025aa0750018100400b0780c000400c2050080201820005611014050700704003d1a00040410b05e00052009140c0c1d81d034004d02c0e00102484003162005c0e51005d010b41541480100c2d0000e002e04202c4400d0340d920381a60882590050f11484000804005a102c9201851286002800383d075119200319620940341601c0300015803201604010130062381148a5943c9422240154074550740c015460500d1000d020300c851421401400e0f040c604242009214400602c440035680d080c41c001040c078851a0f102c0f4604210411101115824500c1c010f0940c0042d030b004480706a039903030f940f5403962410a02e40f4500e20060341e0704000540c2408104060413801d0f0000d2140900d41e640c00911075802c0000c845041c1c205550030103190700040c0a00c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 223716151 1250 223714901 223714921
    0x30c0303070c0b0601020a0b040213060e0408040608010501021204062a0c05030c0f0607170c0a030e090a020a050a0e06040b0705010504060b27040323130f06120f23 72
    0x40c0c4c0442c00b800101000c1a043d10f5007a1400801400240320381f84801074800c1d4080940c0004005103002580011542040c0c03030070024a13006801248000759500000107030702d40c80011500210701d0814550303807401781841d070100c0c0d40c1244050820664a414203040d01003252610030301d00e21a004000c0700041c90300f0b1908040c2402c3c0c04171000361140d14040307004c040300da6030781003260151680a200e003800060380e14101c0800d070191112009450040910000915410085140109500f02c0d81c20810760340300d4001c2d0f42240654001a40015410300009101ba40a500c2c51008a07400401d40760800c1e503600041c80d40b0b80e115076011141651544244802c01040f8001c0780454030049500e281040031740c0ca01c4000c8481c694028011071061400400e09040c00742010700440c0d900301020801586154a050140c3c3c0d0005a01e440501403140000540381003083d9040c0070344407503a40303405010480c041c007a8003401101541c0e408182d52080c006170307070841e0310b091082240c0e0a0304454146281541c280 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 223717401 1250 223716151 223716173
    0x3030c03140f1b090105040b070c03061b0206061009050f0a0b03071808010b06030c03040611190f031a1201112d04080622050607120c020a08030103020d0302030c0303070c 75
    0x40c0a502c2040c0010502171385c00c40d06880c19a4010600c4135110842414901e12140701d990001e8080c0e440e100a948010401410210140d100c2c0d03000c0b02c0700b540b0b9080520403070307484034038020700081c44e2441b00303000c54031b480303056a207102e00003c00c201d524946860b44030045034030565108000c210300707100700180c80100c0242007008061120007006161a00d0000c10014030000300039104110f40000002c2c10481142d10481110002645040e2180c140c4038500179002140e20a41c1c002c101c0d100b0301a60918403d000da42482c910302800144000c0c0c00e04148010080205289440344d521007504c200000c900c03102404c0010f6141d222000f120a90b00c0704400001c3d8484021601c41c50104070a1011400001c0c007a40c10111400800b15000004038064040d072a594000902a0041d8014031698990005010140081010080140e440072410507a500d201514000740761070001d00040000d40b4088240c0040035000380162031a110440c010b0307500b15482121000049070501444106000e921717070103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 223718651 1250 223717401 223717441
    0x30c07050d05090a080a0803010b030709090e0d03111c0c1b0b0402090609040507060c240501170a02010804020f010201201201090b0f0d110d151503020d03030c03140f 73
    0x648030079051502d41341c4082c40305000d007d030a05030000210b140ccd01d00c03841c1c0420092040301da0401030382084801194480c403003202924002030130103028901c01c2602724200c821071152110003840c040e103042200400703410030071010310920101e844c411002d1101c405580d041940311b444807101c1403415104100044401a00441c0900c4e0303910100701c000384001825009990150905807483d0b401c61506006510040d4100d200361044800145640180c5400c6541030703800f036000c881e40c2d440e01803112030395602000d0303030281c0024041004a4090300744800b10510036101840042900b6a5900440340b04003405007a010030140005020385104940010583c094202e6542c240160300080e0300040791640210300b00e61289a5108220042140369503140c0b0400c440506243d00403040c41c1001041c0c80041c0e542d022002e410144030a10f2103003554084810746c0c3e4000c10000828000303850460007025640490800d1507690180050400c0c2d072030150600c9800394801038131562400d05400302c0e500801a20f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 223719901 1250 223718651 223718653
    0x3010b060d15080f1e1f150512030a032309150a0506090106080703090506011e05030d0c0305070807060603081c0e0706031a040905010e0d05040509040602030c07050d05090a08 77
    0x54103d01d411808180d056005051048140030b405c880074140d41000d92407802600780900805402400100300d0304407000c4c4200c00008104035941c1d92042c410715200e0111459990b40003000040c50040c003951020f5810050720f80701720b54000b0a07614102441206076440161036010300c41d03c102c130344c1c00c5807005513011090081c24006d604100d4082034050b14180150b20078440380c1000100440d110707601002c0c540e0340190485200d03582d42c00d031417440c0002c842d01320700078400500d00114185c10001200d0000800507503d606240ba8280c0301102c05402150049a400f60b041001c032000c28a03900400020310f00600f011540d4000040786401c0c002000901d080b0200d04050b0011850038021514070204c031781504000c10346080845241c4498418100781c0d544c031925201052091000c154031048171000e6030b40032207140c41541c1c0b405480c02d016a114090b03101940c4800100002d4494002d5604202d98118140c10180d29503129401d19001c02e100c5400500082464045882d10f020090700401c6460 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 223721151 1250 223719901 223719913
    0x30302091306030f03030506010509030d09180203010308030f060d171b010506010e0907110f06070f170a1523030c0402041a09030f03040b0a17190b03010b060d1508 72
    0x1358400e50910760300e050182c141079403080014182c0c2d01620842c7c80c0150024103542150440030b0018210300c0d150300032500800c03400b05a500100c100c52084a0590307800c600420f055a8075580c0c238003040c05c1c000b403c0d01d8005400120500021b819842403480d00103010722142c1c0c999541c450503891041c08052030400b42d178182814130640741d801003110802004190340c4005540d946440558089000c0852490f00d80718800e812420581b010035018041c58080d0b40c1d1450b591000318044071007982c0741c00208000198074011400d0740300d20307034031000c40c85580b205142c2c0441e9513600e0080d0980f403801a04a8590040400003031903240c00e1006408513001203d0450403d81400d64002a5800640009203a07400000e40d150203130307404104920b0410208003c0341d07541c0b52107410540141d00805040008500c60400581c100034143e04c034984a0803600c0b0700c1031482052054600050003580c150507800d55070707d4415948940b03810005200e103500c001000b040c0381d1207251011080e0902e60340700340880d8020b2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 223722401 1250 223721151 223721153
    0x90302010c0201080408160b040b06030102071e0f2012010501080307061a0a030f03080f0415050406110c0a020102070801061d0901060b0706090201020d0906140f070f03030209130603 80
    0x70700300d0a41d0760302840d010082c0e40e11454104000c0c810072000101c02c140e60100d00003007003282c00019224520500c3c03030040c0c1da1100c10905090303004400c00242480503d401e15809410321140140c0302034050000e429081e521601d505c90020100501590300c0c48200008440c94242200961054545540200819890003c0140d160302541800503c000d40350440203195001c403080d81040914010a0b003210305941c1e05d444001113052a1084000c25404c0740000d032410300b00003400c0d104076000241d465401d002001d2034001490b00801c11162a6600c5c002c40340030351a00700161a00c04014401001c0d980701ca80000b91422000d40d0152500d0307030410a050008a80f0000c142c00c100d40f0b00f41c02186c1e59210281c81130702404a0f0f403c040598080400c080080c04019007000c40f02078002e03001c5d02d40c1b0f480039200445244915009180201c1c14a00e81c5c1c0d0f10340030095000f46030300f51703071102c000d400c24001c0d5560888042143c041500065000f1aa42c4a00c0c6407074400d40c02641d80a210070090a031075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 223723651 1250 223722401 223722407
    0x6051e0412030b01050c16030b0f04020a1401030e0f0d0311041206021c093206040b130f0f0b07081302101b0c08010605010c0206120705040506040e0106080709030201 73
    0x1c1c00e507200d020941c403000b40c110284d00407416070f60101ca0b458141c4001d8048012050240f203403600c41514085d00325000b1030f050b5031045840b980181e80150281200d241000d4801c2d9202600f46103082c10581c1d140e180d17070050030052207c920000321075006020040e410040040a41302044003202000c94100410813440b48100002569141d01150150310360007061281151000c1c0d0f0054421010304181d21076040240c005031007005c0b80c1080e03590811884036490a800c5a140c014050580356200c0008280820000d4490784d9000c1404c83c00c032030407c0850b5884404000188000b146c0b203030010781005003046080162194400da03d4940a441840c00c4000703040d40041031100179014074040c2d808554040c0c030591070580400503040041769040950700e01854003410f2486006042d500c1e2404c040360b00d43c4903d11b43e5a110350011b14240c28007840c804504840c00c1d015150b40240b05003084006416161140500010134845c0031406180d071410b0b0005c5c06c0c40400510305010043d08034000e03c011707a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 223724901 1250 223723651 223723673
    0x6050108061504080f0a2006030f04060e070824040b0f0403140a020a06060618050f0a05031507020f07060f1121090f090f06010c030e040906051e04 65
    0x41c084501c00c0302031805081c010700318400c0790441100c40c0241e10220003c4100000c010031500d101d29117000c80c941000001c800c5044101c1d000e658885c600300003081e11002c19004c0203402034010040056010055820f1900d85940741c1d0004000340c209022501400000800708041500603c0d80b036091441d00d69201989050000c241c803c13007214500c0070a0038141700307800f0b4407000d822216020740d94510741f00d0042d595105240302140d00340e04020012407120720401590f100307c5020803c5000c4d55042c2005c0080c2c83c40c6640348260418601c100000e101e80e420440c1020300d41012040d5445401c0c0000002c2c1402c18890351206540d02c4900100200b40e40105140310711f1000b03152071003036100d4a0080381e042c40c40e22241d4041c50040c048508000c800172500600740c46500321045c1d8085e07929031080c810313440d50440d030300c0e0105541000040d4165014203900c5034030510030314003540d0f800c05240014088440161082c2c502030359801c1040002002c0c000e03c58140080424a0511407a20b6950005481 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 223726151 1250 223724901 223724911
    0x30601050f03040309120305040e100e1801110301090204030b010b1204060f0915022110171006080307020f01030920061309050901061d0403080606040801020a020c0f01020106050108 80
    0x1c0d00000007010304d0310907103010001e4010048246d03903504c11418000c0140d0458018194124040008500b6240d146001001214011228240d42e551030000d224501051b0709518450f0303540302e045285064828100a42c00380c018a140141c1321821402d050680481c142c2010307955603000c11070f900d0b038102c01c06c03109580181c1c015404103240520820406c0500900c10f0020044a14a9141c2e151a80300741c01615145110041e01c0d1200d2800c06141c0c0c5a011054602145071181c541050180c1490b10501d95010348035801100c0c483c6130001c40010440d220760b0701a410070b03040451483e04619040508941c6541c09103014410002e2545610700f40144401562201c01d6050860080e1522400242c800070488100b15040450307440414501401084031942055460020302007100d107100103000005000c00c0c0d540c081035035650b0707406a440590141130260700150a01000445103001d00060010b81d0085d4094101120414140807405000300700c01815a4101002404130740d03440b0307101607413003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 223727401 1250 223726151 223726177
    0x9010b061c050408040b16060b0f0a0314070f290f030a0e071208130501050c060f060616030c05010501050111120f2115030d1403100b0a09051503060105 67
    0x5034481e40391682c1c085c41a03520044904901040a4100c07034072020344000c1c4540240c000b0302a00440d00c08011a640464044581c000c10360b54062000c0340202007607401d11550364044469160b12032114855121840d40002208200c10b01036415100145804071102062040318078101840c001c004e1515010042c040481c07269240d40f55030404504004402c02020503550300e1076600d80906050841d9802020a034580c14100c04000500d5485001200c1600ea0311790082c1c2003541b501d1a207400483e4010b45070f264000c03410b011101d0300c1c2c54210480c022440c07194440c200b17001c8061038441d0075600d050b4803107410b05c44d020030307507450895000c50245115890b882c1600d9a410000c03040c12018060021a00300603140d9034102c0701d001000b1036506008501194660320400400d0042659860740c485200d0f000551a4405400038000a4007442d04000e202c0102d4100b540c803080703c21480d80100c84103000040c0d030310004021030f0070b200b00740c0309400b580b040d012455840d02000103007c03480b0b140000310724 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 223728651 1250 223727401 223727411
    0xe01030213090816021804020d0b040311060c071b140f01050f03010801050108060a05090309010e010e040f021c06030f0f0f0503030108010b150c0c01230c0609010b061c 74
    0x8050381c242e00201c00c40c2d42c00303002c95403030f21598291078840324080c00c0201e014035000c0c1810b40b04a103c0040c045d03c43d5500401202906d981aa40e100440101510840a000480d504440d03145c4c010311a151007035103000c0c07030107860340c41038107010507100208500b0403440303038001206001d0b12640d0400700d0111403040e10722088044001004a40d40c1c8550711900505800c00300000c80d81708410b4104504940003582100c0c1283c5800520000b11401a80d06803015071042169031519405402e4071b8420b60014101050684032000118041d2a0900d44141d0010740c0068850403840030200011901d44003103108001c01070031940d03443c0e540030141002501c0f0541600052082007c410100c1c1d8015501c041580d4803540c0d01c000c81400b0300240490184141640101c4001c4502c03060280c0310300c002d0a6000704002e240d01c07401520241c51599030344058001140c28035003415248001409040401ca00804503860b1108081d42151301c00d0307000703912a00e010040f134014100045604032030005d18420000c0c3c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 223729901 1250 223728651 223728679
    0x140f0a0f0e090702070515360613120c0503060403081b0a1d040b031006060201050105040b0616021c2315071809060608040b0603030901021207050a0b0c0415090e010302 74
    0xc96000381c5840c007483c012354601b1b51179000c104a425009a40001074202c003d451800100681401380d045101411321402c0c0f0304000d03008a40c10200e10781c501810a000b503064130b65000c40d043c80d80844098001c80c0d21081440f442c0e81140d0304c0c04140c00d2080c02070074101030500c4802003003060000034600703e01d100c100c07400c90141c0d603030350082c46c1004005003140d1040c1c5481c170114004d03042c0c42c85000c1c0075510340030002030a42400c0c06940300000d00240030390300d01041a0348c00c0c0300c00030440105a80000980420300700311501c3c1c0c50081c500c5405403041d80c0c10b28000c07245006003407443d00508607880d002821035a103c02002c038109500300c5510704001495440e544803902111005074055213505041c51000a429908111168012401410808402c2d1b0302e44060603900d2040c80303455401a88642403030f013103181c5440081d0150030f1052080d20b03144400f54a861516400c1034506605401c000a001c1211486048903130b0380c200880c0c01d0280e010342c5031400302000c0c03150501c0064003d51034810020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 223731151 1250 223729901 223729939
    0x7060206070e19210312020306010e06071104020f121807060c050a06050115080603070e15130c1e020109050a022e0f12020316140f0a0f0e0907020705 66
    0x24041c0000040c01340030308910101c02521007948550035004161100d84020b6461454001c482c402c80b07040e111b24903806410814003150b5840060155181903a0003c0001c0c1d690351400100444a0001c18840c0c48004811440401d035202508101c481a50071600e030710310b000007042d41c1e4102c40761303402c0c0050220903e0402c60b0a000b9140c41c01024249040004640b10300001031554141c200c2c2d0f0b96503241640d459040c541c0d5140b45000e510070651402c1c0028000400020f03040800002c0900b14180c15203d404c4040243c801d00b0380084041180c5c05080c0303038051816168a80301c0769040c40281704a8129071034681d01c403203015901900586a601148503070a001c00351401e03011102e03807507110903040b1080e0010481c2550303408000000d0b039100c581c0d14035180c00b4000c2c0c81c0034113020802c0348908030780c2e40c00549015190000130400e500e000c1c41b00b010350104040250800210301c3d00d400fa18064003150080406d0b480b0340883c1c0c444c41540c4288100540d00040140548005407195401e05104041030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 223732401 1250 223731151 223731199
    0x31c030b0306060d1b03080f03010603060b0c060f0603010204090608060906060d08030f0a021908040b10080606091003051f1404030f0807090f080a17090d1e15090507060206070e 78
    0x51f05902000a0b04011403042d03100a5040342e40595080229603220b0740f0366003040c402d004210016902210214031040d2411f000941c115400030001071400d9034038408141583c5840e400940640c20020421051860903c60740340d002404442c2102c0c041150380d142c2184e07000180c00341c800c01c1d01000010701c54040315411145291405480b150704400c4250004000072001c82e03007100c1e00d00c100c1c0c01040d540e41032881c0c28025182c9080c0986125910642804089840201030422401420342c00001095082c0480c040907000482030410b505507000b09070017520140c2d600d5002c8101c01004000220303902075030000009c620392030700010584602d002200c0502d22078104510010b40318000003004800003504140701032149440446046802c2901d50141c0141007013160020040c0c0c0309040003c0903d1030004a50440a505811418080c0c6419070030040c400341d09540300740c0c2c511591050060030020000284600d1000b0700d81442c0003e4000c113030114142056024003800c080300e9510841c8c464503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 223733651 1250 223732401 223732403
    0xa0627061a0c010c0f02070b090414041103011d07170a0602070c090b0f01090b0a03060f141206040c0308070501020d0c031a040b010e0d02030703050d02011b0206161d031c030b0306060d1b03 83
    0x8440be8106402e000d822808440400740c803075840e20421310b6003052039542e031095800e02d4102070314000303280c411311004103901000c040c50f85002d080303800070020300c81d0320140080034027402c505c0c4941410100390004850512011500c560441c0031000c05a03a40091200140c4000c40ca000d0b88842e90800e00341c010f0800d982121b0f007000d00c2041c012581000d01c164a2a01010071520007602c0007002802544406080d0b074058003c8050701d01c24404a0070200052100ea8070410006291081c50714000c81100c8113901041d0000c0d403128031808051120301c00b034501c1404120380400410340072600281596401007030060003144202d1083c4103540d4244241402140c00c02c007600d0094640040c000d009010308150001503410131508121b40301d00c0018000d2184041c141c940410340c400704c030151071070021102060400006442c0344080ca803014041d00d013408800c800041100200080084c007541c1098502901a501ca00100030031540e0f01444428200e0300700d2035181c070000040e195101c0140440e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 223734901 1250 223733651 223733681
    0x102c0f040c0509040b09010506040e09030706090b010501080a0203071d13091a0915060f04062112021207110102030f130305060a0627061a0c010c0f02070b0904 70
    0x20780c140468100d0700401d007041c021502004000e219100304601d1050a00400f900322009100034007112642c0308a0302d8101011300304403400c00d4070f20303076a90064549403501258545c04040041080e1358109a03a540c011210340d4042d0b05524110400a1041020600d032200054004412258a8807138400c0402c94a000840c1407281224a04040c009004805103201e1044440c00c0042c1000901044c114410f42152804070849d032180c40030800c1402c280821141d1082e41c1c3c0320000340c403404d903900d20780e132401c0590b5440302e070442075090030304000e03081c0c1c410704c0d0030b540040380308601011103d01252440340d44804500005020a030040b8a1400b4144000c0850100001d456a02c0c0390076191540c1182e01c10300464400e50f480c0070b40481514060310404805603551112080342d40c116805440034080c010800083c40c13599541501d500802d0040c48002c01440010421400744085c01880200e06940c100084682410003000303588920a1050300c55040001c9100845966150814948440084 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 223736151 1250 223734901 223734911
    0x1107110f06090a08010e0606040605030a0818100c05010507032031141903030305130203010c030b0f040605060901050c010e011104080d02070509281406102c0f04 71
    0x40000d0081a110603a1000c47c0b20b01000140c40f0700e05401294186e0300060082c1c40e0364a555074403820b2640160040b08011404d0611035a401d88802d24501d68004140e903075a0000300c4541481030031114058152000c05061402d0000303c44043c00031505034003281c5004580d035114105001441050039800c40c60b0141198030000d02d080d140c2500c080075110880c5401010307071020310800c04204bc41980c00010803c40c8101000441c5c0641d005c241d20110b05101d240d0300101d29400642100c01000244011070b0361412141100c0c2844284209965001c0d00d0411520f414075001540a004a461050411400151084250000707400050040201e040203002e034518500600010b900140580341c07040c81000c0702c002c041d900c0044e844084560152881206440f55081001107282090a03581003880b83c0c0d544d00717282c159a110f903005000c0300c40616482420b1400c2044603210f1801c1c28941049240c19910380c0310001c00c1481010743e070301c541e19030324100036040211307102c0070b1413011140e481032900c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 223737401 1250 223736151 223736159
    0x30203090901030f0201090902120a0221070807030b04140411010c1a0708151302090a05031006030605070801030b130201170403120b0307032a2103031107110f06090a 73
    0x1c600c4e2040e070303100f603d800c50314580701c082400c03c0740540700c0d110281c0c40c074507000b04664620b65401002910200c1494071902c20f0403001c4400c0c014025900c500010390b09004002d4130991510070444843c10880d030500840410900c880320051010740042c102c07030300d441622001603000d02120031800d035002c000c13604401d0001140c0b04001804071143e00c0072600c06400901401c010303407000e0000060007421410f4a40032072000a000350800032019800145d2003602203540d40e810403440c0001824508046100c60840c9050010303140b000d0842400d01041800501c0041d00018201c1c1d071003030600e110020b0204807400126030300001e104031340310030b54900c80501090541c0182800085103c0146c10f00c1181a0b03e8203055980c01c00344070141410000c41c801110880c0007006400c01c105405500001f1a42c56400142c910007492030b589131010101d070603000806801d8080c1c28030b401c0c3c10401190a000941d1115100c06100d8800b046c864030749901000c0c865904c3e0300584100200c05405d2000c40ba451b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 223738651 1250 223737401 223737413
    0x30827120a02010507050901021f060f0803210403020d05210f07020f0607050d021c05010f0f0e06010c1202150a0207140a03050712090306090605071d060a0c03020309090103 76
    0x20101c44a80154202000100c002d40a103003100c0300010183e000349030b000c4081002008200c0813204c894020340d21043c00250b9010080204409400540043e550f550b40550203005036010601c84408904521001c00010070740216564814a9441c1030a554079001140a100300c2014940b0a03a012070b409420320407182c0e030305041c6c20b21400403a0211544030503400750f0f455540500b182d1ba000055010046490485504d030090110003180031480400c0144203100c4500740d4109070459000d10010401c208501004034511400608050f0010011403c0c0440000c080340700106000d81000800e10340d0844c2c0902c01c10107503001075002601c403034150030300200d01c5000c0e5022207010384240d04209880140f0960214a420060f585501c41c030740ba19000740d4607512140f2040c801c07001442950071001000c42d2950003590341d903074030410001510740307046540270384204407444105803c1240c900003100c458548a040700c51484035070404d10001c005500d01245540310f111402e035001314600000008200c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 223739901 1250 223738651 223738657
    0x120614132901030b040e030405010c02030f060414100c09061409100e040f06121211060a06150c03021005090307080f030108010c0810120c030503030f0609010b0703082712 75
    0x200340c0e020300c03001c1c4e050f00c00c0105540d0313181c10b400366542040004101710b6019000d243c0407144041c05480d042c800ca032034a00d003481d600721802e850003402040040a962000d02120032031030f5004604000c503195012006092403058001e220a10400e88002d140f02c5020390251808464000c000403010301c1d200400030008094001e1150242d4100005282206058041c1000340e42d10307072603401c02d00d10703554036101104002004100c040c8410394520034080308090029a101e403030840d001140d02e82c40c1030381541507081c500400038100900140c060f40020b82c01b10350048003880200001c1480d0321403e00e294290301c40c900c0010180840001d50120b520251000366040703d809100030040ba91600300d00b03848680007140d940b00035000103c2d00303104003150214074402250040344000ca002d5103c4e6a201d10315403090743e014020400410800c0f00e40d10700041e2075405020500c8490b400c111250350050300105000e0108801d044c0d000b0014600d007a80440e25840001c908411151f44620b00300007840c6980c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 223741007 1106 223739901 223739981
    0x31b030911181b1b010c0906080618040809060406020109120302070308240d06050a05010506040501050a141317010c0c020d08030402010e190612061413 67
    0x5400071004c654080c03450000240f144c3e00c1c101d026090005d690301840070454210100f000d1070705d62005152811408070000401500c480c0740030b240a0066031101038000101160002d000c0741d0540100d03503018050605001c50607402e1000714241c0c030900d4006004107030034501103903000e0203200031110020511440c2e5411811142c0c006a00021004070a0f10840c0c0c40e00280103140032544100c0340117050441d8950301e05454400041d00030701030040540705211b0320104150480c81c14204030f40c0d083c0905803480c0325054899510182001c5c80c0359417407202e586002c0c0b245036058010340c017081403160020000b0a507241c1c0ba40c0c942d00369600c0240124100444000a10150b8a6040b604590b95001d8840400d0590400744c0060207503044420900b041d03030a02e0020450207070109600c0c407070f0384015a080c029031040742d6a49400740552821812400500b070044904200802000300505e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 223561151 223741007 := by
  have h0 := BRFrame.cov_init 223561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 223561151 ≤ n) (h2 : n < 223741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
