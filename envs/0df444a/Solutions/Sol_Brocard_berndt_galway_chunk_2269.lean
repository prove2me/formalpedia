-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2269
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:11:34.926824+00:00
-- url     : https://prove2.me/submissions/b2c4e709-5c29-4741-9e23-2b95bdc3c24c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 407913669 ≤ n < 408093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 407914919 1250 407913669 407913719
    0x1120201030606090302011704030306151e03140f070311030c0c0c030606100305150d050604060b06070b01060c0f05101a03160510020f1f051302131104080106 70
    0x1515283c003266031001900c80640011041348440e50030103484940340741c200c3e000349404101c1c0c0f80ca40410b1410020b00080500010744046569200303010000c940305054503491406010001058100340350080d0080e003403401090ac0c00d00450203041c001d034004012581c0c0c56014075107030f06d4811100700064010200a04060003030b103400820780e1034003182c1d25100d054000e03e0b001c5501c451510840c01054000c04010b85034140014950403a903035072502854462080d03008254920b090302c0c00c202911049940c1c10b0213100240548000680040b05040c155002c2d031500f5400f8521905045c80c1c0301c5a00c1102514500444104281210641d0070a0301d07110441d0345029100c0724044141075031280ba1000c1e2892003204000103215605c6e11812442e040700c1603204032a16400e007601000d00b401080b010f0f104140100c00c400058542081c040c2a070b000c06650100c035048442c0b60042014800c1001d44006007503903903060040380000000c02d517406010404000c000443c2c0310b003017604070440294050404c82c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 407916169 1250 407914919 407914931
    0x9060609141518011b051e0f07090504020d0605272b0c060c020607091202180a1104030501050912040602071806090c09050a090209061204020d0503030112020103 71
    0x40c00c1c5052650340c055050300c0780b58a810718950640710407240c1e5188140c108050700d00721114400404400d030348a50301800113030507a001e050420031840712001c030302c02e056900180070402c9203c4021510900f102c3e007003003001c2010b964610014000e001e00d111f000307048500c0d04040c85040394007981003040345000c050646000d10814170500740c0c0c0b000c183c14003121820092101c040040d00f01110b90110f0b02c0d03a8102000103c00d1a5940426201d11101e035100503808401005490380e805900c0c08020180001d102003000c0c900d0700441d42d0b110030700e0705080700500350f00042aa4080c160380461007600700940c00c240c6440c3c4030714103907000e40016626100303035200b10501c000d001c40d5040122012550180c005000e43d6241c5095100c0a586a05017903c2550380e8081c00a4034000a0245070540000ca9a91403c420305240400c000b414054000d601094410b022003070392511a5812580c06801010488199658610005005100c241d0004009002c00300c00042c1950005524901c90384c800d1704d0502c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 407917419 1250 407916169 407916209
    0x30204120c0f0501021203011205070b1603090608010b070b100807120b01050103020f031b07020a090c09081f0203060a24270e13020a060216081603030f0909060609 72
    0x34426031b020919070724075802c00c010804034265800c22100390b44140140c0714100da85815081182d003105210030000b20b1903200c800b04056100983d0760161030a42413240955051050301034a0b80900c0d070000781002448404510320302c42c02400071004010704400c0f0b42074680c450b0460100ca0620303040c1150311061040001c6410741c02802034609007100070b50b089040d81e4801c80c03150400ba001d940c4100c0001d90803c007074000340e20303030810000151003c203c0200d0020140c0c50010600c8000e82d0000702542c0000e080755103121410351561525804421004d81c880d210100020743e510050b03806180590f01000c4050035070409111290081e80b50754690015001d103070409860180d2002c50720504c1044095000d00a4098002c0c08039000420038400500368a01c1c0d178040b40f100002174200f84096030000e50342080c40031680e0742e036002904c2600043c11303100500d100b071030ac0e8822044c00000c09000803d10b6449441c3d00c140701110007090700c3c160611015030b440101400c0d0443e2805650342c1c2c4000c0c820a030007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 407918669 1250 407917419 407917423
    0x2060d02040905130503091309151a01080702370302070810060b04060c060f0c02030408121e030601021213061e0c020f04060504020d0c031503030e040c030204120c0f050102 76
    0x500140c00c5400743d1f2510100300d041041460b1f19440241c02ca41d41c859544000c505154200c42c4020140f00b80041c5419628141d01e1014078008030580c1002901410040c074654041050340b1112100000c007010344410403a2500410107801000000f0008241c504081c981d0000c1c92a00700d8080100303a88400c405082c00c0b800380c030418040c0e020410003c2004004003885454211103c901440700095030407010740945003070381c01c5441ca0000690010509100c0040180540f0307100740c0f080c2e884180b92200700c581000d0209041c3c111014040000300014056900a01800300141e031540710155442c0e1031144120900381080c010320b0000f5141000c0e008003440058a02c00f20914540c5540c80104003a5080050107000c0d0a40b01c2d42090315801c0c002095115400500b604580580700450b1007030781030000400312080c02d4180341d0751514010042021035081030b00c2450b50310381540d001c200780c4c01c0102d041e030281c8030350f500042c2124012922123041c4400c03c0c80390300541d0380c46008039605a6903180120b03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 407919919 1250 407918669 407918701
    0x3030d020406140f07081c1404030f05040e01050405060111060403020a0b070804030e040f11041409100302060703050c011b02150f0606250b07120606050a05030610090302060d02040905 81
    0xf940000c11405d0085100c0c0809050407412250220a0380d140302d06820003900c0d00e00318140d048150b40c00600040503040700010081c56070700d1801a04152034501403c08072001031140e44c2c0100e0f41c030004200346922130700b400c05118103880201d448a080901d4025507480381e100082e100e812460000c555428802c0030014016909035a0f40d030301b800034410070000200301c0c0000809040c0da588544091070b00310f0030081c10051610310000300c4000d40c000140701c0c04510003040d001d1000a5644140010ba54030803d854104d5014641191110320030030a0600500040140c0f00b1601040b54603000c1d46907000541c4542035a80c02c2c070305035070307a00c60704050040e8210554034203500000600c09450341240042c1d074020b81039451781044e04079148a4903800954002a030324800010410481d4044084840c004c1400803e4946441480c0c0280c506000f0071500020702410702c62107041040d1900c0300d10601440c006940c004003000d40d512001d0508400039406841620003c80c142400174030010100c250032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 407921169 1250 407919919 407919937
    0x20f032e0504180506090d03060812040b0d02040315060602010e01050f0c0d090818010f02150a09050a02090a0506010e030c0d1b0906030c1a03070909051503030d02040614 75
    0x4190369401c120402028145032241c2002181074014a0703404580f0800c069401040d01e600a402c0d4840e0342207004056a24681000000c1d5120b072880c040c110220204035021945000f020580710b18005032000003a109540c000307400089110f0b03580303500d81c01c0b07680200111802a00200b085000040001e804c0c0c80c0102c0781d007101610200009000104113400902d40398201b8000007801c117505580e91203154000c0d1901d4819151060082146560054200c4041d40a01e00007402100c031301500c0d1841040000b0100e1300070703d440700010340411004205000e2290b9006154030700d1880c0c0f0700c0c510b02c0202801c0302c080d0b000a0002200c5461400c021030070141d402c4000d001c0c000d141312262144007401a803035079582d081510820000820078460b11800307000e107104070041c41229140c891500c9894100811104602e9010005d014031a0b07000240001101c040141c04511356a40c0a0a01c007216104211150140000100c880c00607540394024401d68840751201303480300781c100040600c41d00034000a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 407922419 1250 407921169 407921251
    0x405060414150423060114071e1e03021513151d0610080d050a050313060f060e0406110a080708090a15050a060605030603030901031509020f03 63
    0x8195003004807048002c82034000340011a00e184200c01e030b8540909004001c0010780e4480003802070310340c2e015000260800809511030306000b50351b00e40d03540010500c943d8919180c3d102c101c880800c15601c03140980d80d01c0e050800700445940d820041c0d112454403c031002401c20030400180d0b610079150009200d1500711070b0900d001088400407000404003140d8220403451650602c04a01c1d000b0070070725208500301e03d10a425140742896440c40c05052003080818010103005854205c2e60010079698402a40340902d40c035101a0b0034800c0c0145690b00c00044c0040c28401c1c00720b450030b0144009400b42c0d02c102010054202415044081c6000b0303840314100240300c1101184285114580103038000a0071801da404152040e80d41001503141e00c055121090344a01c00c00c46c06940038401c03403005060604000345149003c03000607032284504070030136040c1507451040210f6140020505030203081180000c55540c0707110302050389aa0801c4a44007001d0104070320030110300e40640e020110700401c45034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 407923669 1250 407922419 407922421
    0x6090807060c02060d09050307111e090402011827020a02070501050f0903010f0e151909110d051c050708190c170301141c0303020307050d020c03090405060414 70
    0x4011941c80c0c400c0c2ca42642d020b00148080425400c071403156140c030b0751041d00215610801c40c54065100800c02e540d6600c5072607100b001d0341e20000118005443e0040132544040079584a10060714240c0c8586403402001e110f15002040300103102404980030343c083ca40c400c81c0e101c5040703168000d92144140c0d90005030040f010401ca00e5000c0c40c0a014000010302809040400090210342124a1a00341e0403119407030300ca424400c032000303101084941060344800451340c0380c01c1c48541e40c00d41c400b0b40b1a008155903101e0b40380502111808500011400170100c10a030f1515041c119555550584100603428080d000e81c1c1c0018002c504450305958880b0320b8a042c5091241100e021850010310310017844000d01400340000d80c244142b03040403210361481600d070b50402140c4c943e41628200400e000b1400801d0400c1c540812200d0013180c154949005640c90741e58040444040c0240c204400c00741d800851074401c2c100c0c012003e0241c0c440252001c1056540700c01c00c01044d20168901c3e11480d20141c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 407924919 1250 407923669 407923679
    0xa0b0904090302030c01020a05040611010c0e01120b04090b070305090708060406150e0403210228140d0903020d050910030b011b0f0c15171515030f0106090807 70
    0x5000072030214040d005413420085403912990980e44100b616100084d0f00103001c1c000560001203940d42d01c84084020003051003998000340984003549140750602ca20750900d1101b10b8140e812101c1c540318042c009000308001403400912052080c1d030080c010905040014015080004060080358000d0005000b992034a490f1000201410100310047d40c0142c800407032000d05400c1050700591081c0d4410380003c3c5401502085040210101c4030158010448211140d44040031112400209044c09d420482501021f5801039003c00075200e0045021a250f214240345074030020b07100e4007075001c1c0c0311000c02c40711045070f40e4420365007110740c41240719000f003180c40e101e64481004000107040420060410380100d21241c514448100c0d001c150022002e010040f0040f2920001d1400700301c203a0f0340b40c85d0b24502402d2100c20241c00d01c80700009000042c01004140340c81019924040e01d00c0122090b01d25030010203600460768130001c0c100c10740001480c42d00c80e1010034111061100904821030030700c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 407926169 1250 407924919 407924921
    0x41a040b040b09150f1509070e060f070c0e0f1b03010e100b04120318240309020d0303020c011b12021305031b0108100506030703020f0705010603110a050a0b0904 71
    0x90140040f41c402c06000c042c49501030b81545001d00d0404ea00c103080c1e03182904005030307404440e4501d0303805080d0f080d080c80690354000d101384514a6040720315548501d940400b800d140d0241d06c03c0030744407840d0000e00156104c03460040502805504880c0d4003580d03070b00b05c40a40c010300c8144c10310041c040100b004100d41c2c0148407a981d0080d40c0303400d842c1c89440d6220407043c12a00300d40c100381c074400845a040760815400240381c0c40c50448050002d075400386400c44080d681621322161090640a070100c1141c4644254020b000b103a030b004001001c3d0007610b04006009402c1444850001c0d0710300091141600c501c04c0b4003a0030405980c0d21300300101024a0f003034000e5089101004000c00c81a9008034803641c007840f1051074001c0702000740154031900b0b000185209406007620440c014015414041030322500100c076406581401d0150361040e448244019610500401034015481c0c0080071040007483d440460f4401d100316560000030b1f880d0010441d51005034410103900c0c11040006408034146 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 407927419 1250 407926169 407926171
    0x108031602040e1005040506011508010806040623130212031206100318080d0606050c0c010305040c030f0605010501120e0c0f19080d020601120b0402150d090b041a040b040b 76
    0x3003109641602c800c18a42e40306071402654200c0f1a038024230014444008004100312902040b17180901b071551412501075103e000c0908003810f202e4070b0703d0210f103501c542c10040003281d01504079541018941414104540003032844202d104040d500c81c00c200184000007a2021b41141902d00030702c9490340740800c800c01c880c15410805250700d4032520311615919070301c4100e20341e00035402e066070385a1107600e01c0d04482c110313004201402814456030802100010700204a20420b08000509403206e003070000c40c0204a0b8401800c0c6440c0c85442c84c00c11410ba04000e040301d07000e8850004801d90710843d001076500c020310000d0241d2003c000342c000c526000c20740352243c41000c2c101c0d01c84500c400b9804991b40400c1d81240301540c1c880882e04402c6036040000f240101207403862030f01d0003c41550b03000e2420202420180c0300303100e58030f040341100240d4001c03500d0444400d41c0802071181c1501d0088142c410886041c1c0c2e5020b010308240313422090407401141b15aa2102c1c01d03407819644c5a07101031008030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 407928669 1250 407927419 407927441
    0xc040902030f010f0f05060a08060403210c02030703020f0106051309150203040305190512010b0a111606090b0c060c0d022203021f0807050903011b0f08010803160204 73
    0x20802d0b00150402038284208240322400003c0811007030044903a0505655001d0915070141c203a07179004004200010849a030416814900000c0701c1c110480070b5202032024141c1d42440900d000d000300d05c181c3e000002440114401c0d029110f0806207116a182281c0d03091103500d4004d031270503111000d0003141d03610030780c056031240d0708803600c1c00e01d01160303042260400c44080700491000100c3c6640c130100641000d085010501d41545081501c4803140744909061090001a88021840841c40ba0241d2091614284220116000c80e40c202000381c215030844e114890120b0b03403010010a01d8110403041701e0380c9507488001003da540b205005602c0541c0a152007000751603080c00150a100b85040442803201083c5075240e8040d4250300400240d50b06d000b83d2141a070302d51a07060484190000103d80d070007112030a05c2e076203410004000c80d0142003c880c03894802c641080080c804250055603541d00900d0995031503020740c4c1c90700c441665911900071251900c1d07240c040b141e401454550404d001081c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 407929919 1250 407928669 407928673
    0x402152a061524120403030e0f060105030a0201030b01032004140d020d0201050f070b0103060c03060e100e10080a051006050d03080103080702041127030c180405070b0a0504060207060804050c04090203 88
    0x544502c1300400180c00546003140041d40740c1d80007202840c000c221304034480704004003030203003549050002690b41c40522402810305441d04880c0d105a8000da009414035203c9a003215a01c881d26003116803035074840c2c003540c100381880da08189801d04140b102c0207826503019050100d5000a600103643e65002211504403006041100000003100c888600340214403411000c03a480080510240680e60725801140c0e002003801c040001c121900d00580d4200c81100c81d07a955981c445002e0f0500760341c001d4209103000c0c4103074041e0710200000003850a80c20300b0702c100104655031b160010070224527030000002d00090141c80044c0042441a4020b0035071500c010000908500d80304e01c02c0b045c680040c142410302d13910030b990b0601c101030240d1a901802c00110003400c842203420300001c1244140b00c114402c2d500b00c40000604000c010007a19000d0b04000c425291140c2d02c0f008010041da1150042c0c01c0180200440040c4a0740910017031030096074400090001d80e070111051100406544009036814 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 407931169 1250 407929919 407929927
    0x1080612160603020a120504020105160809060a020303041202030a0206161e0305040c05041803030b030f031314040903050307050c0c100c170c060402152a061524 71
    0x40c8122a00c1d41005020b03d44000d44c84ea0000c140142881004001c400e41044c240010000141e034003070120756180c0c0c141c20a00d00360f0029070030300710118082d403c44140c100d00002600e43c110307500080a10300c038174442c0c404030388506e641d0038041380c41c0d000740c00031180540d115002003070b0450031152a102c0924a03907e04980c1c03a14207200d2148101c02d0141c4240c010a50314414082440a0340307100e0000f401e410b4134240041c40e0340c051000c4a4038503018010301015511a150314480e90305010f685400d503100c808030380c0c90304400c105169400d41148550081c40d118000302800a00f0107000d207070000380d05522228217582e16800b050300d096200c52401c24460180c0c2100381364560b50340910a0702040d0f140d58000090410703142a030403030390030401d02800301a002e02855845020015001d54400d17415180c038001d602d100d04218115000300701c40c0a4040e10305220390b40c409004140c00360400a501c008850007601c800034100c1704030b03983c00015a0451500a100070030780d400030b0b0343c402e404002c25070001e04e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 407932419 1250 407931169 407931193
    0xf0e030d05120f0105010f0c240c090e0f0114060c0709021306030204050a03032f0312060d0210080c0d050901090303140106050307081b0c0a020a1401080612 69
    0x18031040100a0011920201d18504000e18103010b042e40720305516103040c10f55042c00e001030410002502e0383c40030014181882420080b08903902d54200c8138000683c560409168140b07006000d0800301d00c2c0c001421100c2c000384880c01620524054130508034040301c5d5900f49103202d403580840c034264581000042080c402448802c00c89600145043d000041e110701800b4216075807a5101d6000d50105030050006000341c0c2c1c0d0f60103034441183c2c1d050500511140e12000304010218625078541481030480307410246039a0003100a1111500f0f0003c0002ea595511003080420682c404020390080003038040c26000764013804060303412071040c0780321700c0c18448901107030303c142c48088540619903515070445608054140c060840300c1390115400710b03c1036051100082a80c00014032490800c09404003103180b1001a100310701d00f0b042502a020354480640ba100b40c1e5400c000007089001c0c1d51444000035100ad01e0804c0100c101c00160354450385910b900c0108134000c4001c80414801d4011301c2d0b04406 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 407933669 1250 407932419 407932423
    0xb06071506080c030703030801090b150c061603110306040b03100e0f070509090d0509041803021e0606030316060612031214070801180f06060c1e03020303070f0e03 72
    0x2110031000c031010034a107040162090030504200e42d254001c4d401010144002604640200d05450300003500003016198140000c81010b04850041312000c40041ca01150f120b01042c8280302d003294030a1417004080c80300080301251031400b0740c454405000d00225a40346006d4005644da98001003c481c201d10301204480200d0710f281108030515441000ba0b40c1c0408000c0c0004030052a04491461035450222090390712400650041020080c00180901d40d96442e94031007029590b0291845c003840281745030182d0354061030901c2c2c0b241d0001c99041c3d4030124400043c0a8401d4101901440c10030055041901e4241e1201600329446500c440c808202c80c00e0480c1c002011500aa5641d62002c400c2184501240c01d6001c0310408590344004100c0503503045018581158130745000342e0108080342c03058400402a01005141d11410098002411648405005510f902424400d41301c01d0494078000c88501c425000100580c00070b00000300007600980441030410100e0802c03458826408000034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 407934919 1250 407933669 407933693
    0xa0c0b062101090201090b070c12050316060236040c030e1902010810050d1202030d0e031804020304170313062c0d0c2a03050f0c0d08030103060b0607 66
    0x1180c0daa64540c0000309541e4005a0b03039004100c047c0120345005440d0311204000e83c07442c0a114030f0103c0303c4201c0d800300f00f030400860390349038100184107001c21880c0c0b900201035070210304945544250a440d05088901580341d4a02e0060036100d018500d802c41428880a00315031007001c014140d88400301d040020b81484003d0743e030381d090003900b0080c5501e807002400c81d00001d081002880c805803000c0c003490f03d80300c01d1160810340000c207460340082680f90481c518842c3c029003c1c1001d0a00a200d20111000009081d026076240c04042103030b03a507030003440b0480c0030448016081c00074030b0120f401d5a900c403100440c0c110900300e18403960004c2c0f5888403426a0110b140200c40c0c0401840044400181a1000a901100d03074014050700120142300400c0740d00030100140c00b211111141e00e14208010000080c034424a0320001211650303030901c16150001924107180c607000f007840d50f01c000e2030300501200e0080d6002c00040d003941d08603180c94004061001c80e00b50002c104004c080c0104118a0a00c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 407936169 1250 407934919 407934979
    0x1e032412010204080d022a09040609060e060907150512061215010524030a0f0b03070e040b0a0605010906030f020418050610030218120109020604060f0905060a0c0b06 73
    0x605c16400d04510003468645200d00900c1d12960a1054840c5600e1410f0000c03030354401122071507855111401d00e68000d00c0c0400004040c0c6160505001e112040410700c00d110340d108100340c0b02d82c00d0b51410201004926480c040001482c20440d80341c4c3d240315824456080070000d0003d188400980403150300d8541501041035242600900401c04c43c50700180c1c080401107031004c802d01600040700c900800303000142240034650b071204502500304000d80d00c840200030004045450456482c044040e10000545042d169107100200040301d489190007120f0407103006941d0340e00d0b9a860103500720010003036800c00740300c1d0607000c000010b00c1d40b8004881c40d00d104840c107030020303441c18803804009008072403002c50400c4c107006000358840c0090762040040150070554004c0c80750500c1e128824014440303540c0080d40034030302042c040380c1154030800040741300e401a241d42d070000780c440701000950f01a40903000001164103126400143c0e45012298202c0380142a4034801c00307015106440240b200040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 407937419 1250 407936169 407936173
    0x302060114010e010507060207151503020102120406080c0a090305011b020d0f120f06081e0613050a062a050a090f0506030c0306120d02031e03241201020408 69
    0x1802180300c02441c0c080d041d0350900705000b01d07611140c0060410700803403602034002c0384d001c900d020030302641004201040144900400210080704010951685140403c0e40148114000e80c403842ca0243c0071601604c9481d150589955640b0b5144803050b400180345008109400300c1c000002403090161640c0e400d0602411452198540002407402c5910544181004081c60802101c240c00c081584030a0b295114081264620000c0060140400c0e9003c45c80c01d200d1500a8092005415071090301d03814000190b4030f283d110113150b4901c000f6940806000c982200c9070720f000141da90740c050004081e01c031042002f51110321404903000d40d042c00d100c3d00416400546a4905079100124102400414038141190703424240801c4003800002d000900384c510000104180f5660b02006590b00403160003229a8a82c0b1150025100d421400d86808800303680050465103d0f40c2034180c0b4458904100110b101c018020521254207140d2a00308d0b410180302d02080d0040358081c0001c0c8098101080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 407938669 1250 407937419 407937421
    0x30c010c0e01031b0f0207050a0906052d01030c090914160306140f03010e03040b3402040f1506020a3008060303094204030f1a04030206 60
    0x406020750301800c8040b4101881c00484203060403042581c1000d24080c0d00d0b00c241341e40c400003406c5c1e160450540040e6400b18105100190b21200d0f03800441c00d072241038440301c0103e003004840300c0d0448290b0001012520314158409131a5210b640f02804140c2980380102c1d00342c1d0703100450000c4580d02c0344141140080c0c0d40400801c00c2c2441020f46c0024210300c1c0403c0917a10340362404001e1010100715a01c20aa048040002030b60250032101d002142d4006480d40c4907550441400c05501200528010300c640c4041c4102042c41d184c416105462184480003003420f041e400c0100400c000300a070310f4015503640031010b600c01d01c07003925030160403140c008110100c024101000c51013000080d814041c1200c0c1d465600390b4003a00050f455012050400e0354441d204c100010b4254012414950740080002110400b642c2c0c0314616500c841c0404040d040c2d050b4148001030010040010002c80d1245040000f000042c49142215101501645140e00188012000e20350020010344058006034020742c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 407939919 1250 407938669 407938691
    0x30307110c010212030612030f04090f0204030b28110c0c0a05150309070905040606171b0d0812070c0308010605031e0c07021021151502030705030c01 66
    0x40d8456103110300d200800120701030800003035880860700c000b486400c00120100d04036403590000750074013440810949032035405030801d0407203030381161048110345800c054100b18803944c40c2c402c83c0c0a40b5040203001d1043d43c2c5030a400b94120a8800208010100d00c007054503a41c84648620962034a4004c0c0c8159103044618500e461304440000c0c0c0782c031810043d5000c200542e11020440624943c00107465165a104400d850410340c0542c84041854100010072041000d103500500654012031400c1d0920b02c1c807081c03040d03602c2940c1280200c0501e2080c0301b968491400341902c02d641d0380700ba9210b82c0350401c1920503a0404c54165840d2000c2562080180c1c101600540d2080c003500c00b5140003030441c6000b81c060342d40c1604003080d22101c8c11100002c101e040f007110080719261a000b0f408004811010000280070700104542010354030078214030703401410344c28000d5154141d91444d406000508002101001c4201034035000290b100c200100b400092092014140c40c035500000094111009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 407941169 1250 407939919 407939927
    0xf021302041811040e0403021c02071d09061801061a03010503010c0c051513080a090806160215130212070509011a030a090c051305010504181e030e0909030307 70
    0x12091000c0d660306044070511000c3e626815507044403009072020216132a142010f174106400985580c80740964036080004450300040e03050200e91042c09a00031681c04c0c101d02c125801016500a007543d08081c01140000d00003415099180304c4540001a0165550b5125811000420800003000d00003000401140c0f03003c1c03107801c0e20303040e10341402d040c810f40035509c403511509804c86200c400c12080e404100c45034119150fa640c00c4c1e503c600e1180d130f20f580ca0840a00f40c0c08162080103450f2203280b0009141d50121344982d5000f07134903500105070702c00348101480d14078100101150f0240b04400f041701c0c003590b10100c1400100746518040c0404904040512070700e044140c100070f01d048080d0210314000c600010450303038080700186002914001c10718018107401519800141d0100e649000000942c8003548514100d602c12241009101c16104594052000c580409031001d605d002650002504036000c3c100f40318840c0c98028807a100101c0068888400bd8910204d20340c40030041015050300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 407942419 1250 407941169 407941199
    0x8271e0106051302031306020c0307050105060a0b2a060112140d2a0206030709051906051b0c03030403060606172401110105040b190c050301050d0f02130204 69
    0x100900c4164103203070205403205400f160100c0c0c120360020020758035910028144003441e5111005668801e42d84600680d20380000b8801d8995506c2c0001180c039070301e0100c9940b0201d811108a09050841d030804c4600c0580103800c061061406080c24061031703000c1031241d50b002e800c0702c03001500c0b040541d0901e902d01e51511088070402d039004444249001c2d8100034240e031001700c0004014040c1d02c4041c2c609004011001000f034110401005000385190000c4e0718030107544086d070f00d01503003040204250314941a01c0c415140071541c104080d020030b0101d0240340c412090500c0031100c448a81c880446d10b15803040c2e00946400d03035260000d0041e25485882401040c82c1042d6065141c04e10652000e1088004580d0741d00d00d85429600540030390191343d10000c44550000208014a06414201d0380024211911041307650000c030141c03401d101611a013140200d02e82d4135203003940c3c00d00041c400548034140703007a9034019620801c0d40c0182e03030720000307064000c1403c18003503295071410f0801594024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 407943669 1250 407942419 407942473
    0x60801053606012c0c03060f01030204030f08090a0e0103050304030c050303070302100f06030605040c0f0605030403051617030a1406011719060b0313110609100827 72
    0x204028071400c160400203035507044d1020003005400100c00c04079401c1140b41800703540e4038020524000c02044a604001640c4200360940b5002a20000390004400f01e20641c08000c000341c80000400c0040360301d201c090704407000701410308070905d503c44000000026090b8021107660388002014410090b02100354402020250019410308071140d0380030b5126905107614000d400c2e030714416000e031740710607401941c011a00306404010a082ca401c2482c0d040d5020b02405c01515240b4a00044851283c030449201300c2e015074031030b4240340017400c0314101d5140c4142e09684045a0401d482140c501410083d400b030751500b8400640301520b180d208501140041249051041c40144030b140040c0400c401c4e85d0104202203d521480d5100d41e001c0c0040c050f6030811421040003004000c0d000a201509400240c0202d1041c0403100b103000c1044402d100d16083c09420410b401c54044505000303110380703134224409011081304960100e041c984410031050041040354048020f8900a022580c089491a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 407944919 1250 407943669 407943751
    0x5120309011a0105090d0c0902041e05010228020a03060f0b150f0703030b0307030606030807030201061e0b0c010e0102030718091b0c0c0e040308040b1003020307060f0306080105 78
    0x515100010f07000d400f5a65109010b02c008008006c10030a004440314040c0030b082e0011526a904e55490031034060541d460855103c0c0710190200301980002a024000c400801700c02088400000d009031481051050483e0000c0c5269000b2001a41c1c600a040064000200001c0d0150310a030400c680050041024009640200f12282c95218441c04558155426050115010b03040c1d0021910b400303815400604024640b641c088200842d20004000c07642c06a0300900c201601c401e800320403003040c4501d00b106030080010030080c0012460140510700c603c0400012080b401a116600303a0307204481c4000040c105000c50413001d010702c800c24000d0802c02d0404c000039071403040080b0400c10a40c000d0014486454141320410903843c140d0b0028103103c1041104505051401401ca84019207080b210079600c540000d010a682680380300459400400a089251a050041e1600100e0100443c101a00c810000c1200c0d8400d008082c080d82941c07100c010f1000d985a0700101b03203414844030305208 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 407946169 1250 407944919 407944961
    0x2f090405030306010c02010c0b100f0b09100e0402072102011a0306370c0f05090102070b130b1c0b010809070501050306041b030b0f0105130308030408070512030901 72
    0x20400c00825030358024020b00389900d909405000580b408000f018000700516480b10401c0001c181c0c03056000c003100e034011040480300340c4a402070740542c046c1410851b040000c040c0c0034074201c0e00c05d0301e0032019000d0240c0014505003c40d22501401e5605c02c0300580c40150011885481550901c81c15501b107600c8000304140f42032910000c1d807640c101a0401c3d407401c5c050165a400c181c20702090100e00c07074081000440c5203403003001e140042d041d001540c002003000d002d10300303100e2070080741100c0041030160f010b0807000b81050104440f507084007040e00305850b0b0140011034151111001814143e00c44c8108280c041c0d58000300c04282c5500090f920304100c111024021000b60014000054500c2420401d480f82e030380c80d010500424083d81a1482051040d000200c0160141c1c000745c8900c2058510f510070341c001a0040d2214443d2a148494820504c9001c00104401801841e009449580c0c910f10f000c20b140c5900c1c1c64041010340a031754100000040c0805c030b6100b40f08024141220304698084 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 407947419 1250 407946169 407946173
    0x22104050a0504090201030b030a05010b0108070c02033c010f05010506040815130606030b190203070e15070803010608152b06090203010e0a0308092d07032f0904 71
    0x90385041e48140d9000d84d403258240ba04580c0a5044540c0916018007282c00700314045c01c1150203800381c5030320a4081a40d0704003084241384248100ca9801f41c0140007019080c0c0c0311610410070711040003000581c6003001c04880c19004840d8103451240300103400201e4811080d20400c0100d40301a40101d1051070100810007070190086141c00b50390007400000c008a9449102c036007601c8900d0b850041400e46440da0210030081c5e036000c00c0d40203042e2140c2801036140520b11600c07c9110954650000c15050314000d8460315106420311030080c0c00144c05800d01c4010780c0c0d0089140c100307070000400f00f4070041c100300d0001c01c2001d50344c00f5040100d03215034204000c940c402c5003c0d13840c0b40484500c0c9040109580900c4600d80201e421154080c00800c400003100201c151a201e17000d0b8102c00003800200070403000030740040e040c107445424240140303080254048814514565080d41e030000c5c002c403500040403480c181000b510248004a25001c0900c04070309040d1300c0301120403000e100c5c180302018000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 407948669 1250 407947419 407947429
    0x41b110c0609030d0804030309061e0e0d1e0519110f011a0423010b0301081002071a06150a020307031e0804020609030703080f130f06080a020a03060e0702210405 71
    0x16860361356040041c00d984640c101140039000600010b41030300d080048034500072018544c000d8a076601200100f200000c10741b02561038015050704040001c0d140300c10b880e903c00c3c43c9c12220058441e50304201e440d01141d88660804194254000c4021489000100c40e443c0d400703001600424200c1030080021708055081c000800c0340b00040c8900640e80c4801d0800304003540c0c03400d0040000b001018001e02d40c0d4a03044113074603900c2402034005900900080e207114000d81c0c001c1e07408013503200c000c05021519608510700d48480050100364400d20781100140341d42c8a000091007480d1460340650341c0c503542403d010b403125200d43e8a5600134201c03080c0200d0141d604c444481c0d0441d40c100c3d102a9a0f20030400005d151200d203030400760650000041c001444884000105940c480044126600c0ca98072a20a80d20b401c0350710521001c960b100c8001039003541c2d60b41c02808108400c0c00e0028a42ea110000300030f02001c00c880481c0568846024800780319518480b0840350a01100024605400c00700856 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 407949919 1250 407948669 407948683
    0x151d1b03060702250503030d09030201321302060d0c09050a0e0609090c100315151d030715020c0a15090501110a060507170a0b1c02041b110c060903 65
    0x94013409150181c002981090b42100000e241c0103049a0301e030001c4004980042c101030504401640c40e009141034501036a40c2c908001f281e030b00840b84840c03440c1a0326081c40d07010061900c103112403903038a40030060361007402408070401411000100604c40c40000b600540b4a070308207605c80c906000c01000380d0240071900700d81c091001d803508500c50302c92000aa01e8070890303614241d405010488524280d5500d607201c40c644044d0b06119003a0540d07144404290380c00494240c1002490142d4054261071140c05007034a100d40c0030b011a02c9850340d070564031a10146454130380c401078200c0c201856040c6040410f69024240c0c880b44185450201030020b0186505031045505020b206502410380100c103114143c411504000280061b2921042c0146500b0f035165003c1d40c50090b0030041001030545200b82d140b8031101400820b030761a030030b03640100410750312402240e1040d02c07009000c184031001d401043e00b492940e1180c54610039035110b00741c140380007915070f64041e010500581d9000d0364001040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 407951169 1250 407949919 407949943
    0x607020103090c180213050f01020a17120103080909180c01110708060c070c09050415020304020f0414180a0b0c07030215040809010e01080f04151d1b03060702 70
    0x194044140341c041140d0f140760340a442401d00c03200010740588426001094124980c038609801130f41c50f0020012491a40440103006034401000e41d0005051000d602182202c01072240c0c4c10030b10201b00d0300452004c00d8004443c3c0b680d000ca4450140e083c40224a5080148058192032816201d00380070740d54414502c0080c108403150507807805e0200f00b4131401019181e17240540e003e0b45400310700303251070f6403011000702c80c02c01f0a01c01c00900c1c105640306560150ba0700c04803401d0314503454011000a0740001e07205030380c0709401c002503420f9661144980c5941070001081d401c1d66141695050122156030b404810060700a00d074920001001d803050311703500c600078655207a141c4506040032440e0040305802004400451028041072041a00c0a0500003400740c0e92216000e048500442c5c10041c01e590500c00c50240d80003243c00543c09061000700040001000501014010b40030440340e250340304401c280c1d4120084200340400c07000086008000194018411404c014a00950382c45203e83c1d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 407952419 1250 407951169 407951171
    0x3120c051203071809050609010815010b09011b12030f0b0603191503050609010f06060f030b0303091903051209060a08090c0d050607030c020d050a05030613060b0301030309060e0607020103 83
    0xe942c10701034422290842c0d011000c880440b80c551005e040102801d503030452103900030400014901c4070019400750003e0228030300b80b800740d107031039944100c07500450710142c1400307a500303000c20044110b0080503500324014481080c1590705c03454013a04803500039a214807080d040c00d404903482d84403007044035000740b500e10101d44c01102c0d00d016500181681c4004d00405a008000001449030004066014214240081040c1e003290000c090449400d8860341c00440e400c0c004d0101070b1406a81b103610a0038028064a142c040003800180004185c0b124000001d80c520310244240300080100c10941d142c005040781c6088259000102c4034000c080c0c03a1001c1121030300c0005e40c10704040c40000c00f0315401038140c281210f81e510b00542c64441c01c6402c4400245070205d1940801e200081c9509a46010f0b280c81c2e00e040b04209044800f40c0c001064580c00c04480107180d060301c1410b200b100c3c018007080301450b480b541140303001420031703039580e000c038041280c00d4040100a07031b40c1d541140c07460340c1c1c2420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 407953669 1250 407952419 407952421
    0x10b0f010e0f0a08030a26073c02010f02360603070e0306060a030c06050703020717031201060212030c0315030d2003070c0902031b0f0403120c051203 66
    0x1400c00c2c8814014a0341000354500e00041499000010f001900e203240c07151f2080510340010080c02c081800b4000310303030750f00020201d42818016481d40c080fa0b450a0010710714034030001d0850307805044104100384040c0c85625000500c66082c030841000c04444201545080700010700e81508031900ba01e4691961501100c100c0600380d1016100170360b440c0503140c980c0700e14042380c0c09032210400c040d02e80d0007400354000252440c6000c4c8070450590707510222031454141810422100303070f000501c04070150301c40c0d041c011030925a080c200b90400ba801c000259610114003909000204069009005541c00902c0c01c110b50000402900e40c00000d4619070f035143c0c1c1e51030b11075607410086030040b01d40501890245c400448c1d80400401004851010402c0340c9026035010a683d03441032090103010345916540510071501d40303400541c1c115200040e00480e0201a214038502c0e54011721208400c2d05000404008016104222444204440c20000c540354119200d10341c82c1e074282040305005000000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 407954919 1250 407953669 407953697
    0x110f06070609050c0108060907020a290c0c151506160803151207120b15060406020d0f090b070f030302130305070f0504050c040e07020a1a18010b0f01 66
    0x4050380c10441e00560140721101190408a4503481d5064030b40b4002800b10000501504285a07002d0007419594024022503030192181141e62420448034811070700c6005100c0c00b00c010720030b203d5000d42c801c11103140d82e030f40c50300754030518008100720040c0842c0b1200c0c041140741080b211290054980c00d94540b0361300e04101c452808280c1100e032000345410000b1003440144001d05000340711600040d203003149115000c112166071809144590155103544109540029900c00c20013500038500001c0001c4c2c1208060024016400582201005901500e81c621109078409400d8000e89058200045210b0400780411400d00c1170340f60103040c4608150186041501c00d038100d419442400d03682d00d404640360302d415900c1d488180304015030800300b030b0000310f614905441450300419a541e4010729244c94910581070904008200c64107602071448400003040c41040413402c60a0035100c0d00c0018581003208a01001e6449580500b40c1c3c540031401c40c075921803580e40e0014041c2400d085c0c484094071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 407956169 1250 407954919 407954929
    0xc01020d050703050720071e05040203040327030b0105240d09020406050402181c02041803110a0308011e090606051908040804030215070f03021b010309110f 69
    0x415010340006240c0001c00018035407541c806405058555915880c40c20303a104460000f64503040400342a411600040002c1640710340c590301b42180c4210302921407076440740040d0880c0c00448098010600c03890400301e004003200d40c0440c004c2c03403c1e8000c100c0c04c4c1c00d603290048600310501900780150008600c1180c11340c0001413140c0c004d02108900c50703039425504d010a01801061800328015400c085012505141078025189a69090000500610f0814040055161403c00546540004c114045015071500c2c00761503402481c040a0180d010b946180040007591780284035886500810142c40000758017451090440c1c4003610028079041a00c2107240c02005a5849a00554941480002c5171600940030740a1840525446074118010b20000d595480003200c1c01003042c001003205000500d8943c0c2210217086400c07808d5401c1c964150340e00c04081107048416005a404244071540c02900701c20440036200c800c0c070302400706007001d9858050550440b07403494814a400711402d4083d45031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 407957419 1250 407956169 407956177
    0x702040903120c08090a02100c0b0f1009020316050d140112030212180d061805010b10031401123003110a02030d0506010908030c060604050f0f010303050c0102 70
    0x284100008101440e01620042d007150b021207099090207030004205004000280c454800301014003c1071072540d00700602425204800307428029015041e002089040302c640348100444a810b80e03550906011f036241b0412130780e00c91440140100104264000d218071420658030036400c105032030f0100c1c40e1015002e41141c89030540012103504c000541e0208185030b1440650080d02641c9116405c1c3d10b030204544521f0400b0038004c0760404c0d5642c11401c08408149035035009140004410f04c02e0581c440010b800003205846682d12035580c215580350040a400205003681001c000c11080100010034021052140034100c8411001050500c030191000c0150398680468011103080c80e910381c0c0d40b030100792852080000e45090241c09682104000700c48203e22142c0045041210300c00e0f07002c016001c001c0070360341000300c0301c1e81c00142c40c40e04001500603095400c01600c0549480310030700045540040002c40c04c92045030900000364901c0584505582d01450010359464102c14501d019101f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 407958669 1250 407957419 407957423
    0x160503190314011a030403050d0609050901090219050f060d06150801030b1b180d02030d03020903010f050606070b1302030d0c030216081009110a08061b040308030711010207 76
    0x1501510900409074141d000d03080000303007102c4800d02c690300c802c0d10086103070b5016044074200b68200302240100b4040d4014111400c1e0404010072003039101c880d032500360788098076190080d80d1681307100d00840c82d0850021512645200b00300f0b4101740b50100140d0440c07101081c4034040e8100290394003841c60b2640004002c2c1100540d50207006545800080980000748000c0d212860608086103040c9586114620482c070440340e4a400d00b0218201294600b60001c2303120341c460500880400103840c140020900881c091320010780744d000c990141400e40e00904510070761039240004101c03550b6211800d51343d111341c011100000e142e03112450031000403504040a540f622503100f451248941c85903503c80c51034465800c1d2001d810800d8030005102c2114095082103402504501011200c43e52000740030500640c100e007040c1c945400440c19401d4140c10010003a0011410440c074244012018aa0038404d1000301e8070b4a803868554038828040a014041008200f280200e02908250140c0305031039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 407959919 1250 407958669 407958697
    0xc0f0703030209270c030f04020906010e0d120e010309020a0b030601021f0b04111201050111150f090610060e0105030606040801020a021b0604030c031e0515010614070305160503 78
    0x4c8483d5001080f588101020030204c088490f00051101800400382ca025900c000d01882040e2107507800c100307410034000c003814108404604100318a903620030700ca0340110b014400d40800a4154a001017100d00c800040c0ca0600d402d01c50450300503140c1007440780c2103135071400300c1a4681d00c800300103d08010015410380440140c0117400301400d0216404030f00d54840464040000d44a5001c00910502035409504017040c0144010006540100c111065002d02002507407080102410414084039060380d039003402c101e410f02000540039082080c0c4d03400c4807000d84c60a68451030034100a25402c2c1004400d4104030020020546940741c040c250381c058100b8000135501c96610500003996140c03e00c0300d01c1c440d02d807080200c085034241401114181d0381c112591400c4e03503043da01d81100400c0c007016805e00040030f013032140000c00e500340080d000d0141f20040c041c840c0e515003e401409500c81e82695541500100101030010b60440101c0e1454028203001ca444001c250030114250302400000c11180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 407961169 1250 407959919 407959939
    0x10f02010e0a060f1d24010303230c0a151103010b07060b01020313080d03060b0c07090b0609040516080a0c080708090a0204020c0304051503040c030f1407060915080c0f0703030209 79
    0x1600108111a100c818089a010248801d80440c019440284806000302c0c1e4481701c01c07442b940d00e229214482104888200c1d00c0c090190382240d14000a1000c19500c413600054801000c4265002d007248540d155400182154100fa500c02c1c0300784110940103122995176600440315900910942e05d42d882085c4500c0720301c640d50303100592100110218100024030306040841c10600c0c1505070340c02207100c18014071249007003854010052248401c0c0c0755100340240002d00700342d62030340140ca218404403c4045800a0640c074060041d210141003102c6003410242c561800507803201080307503c03541c5840d00000e030b5240c1409039410079003907002c06034110303000003400c5c41d51140000052003180e0003900c00388049000518107031014007040d100103000d5140351504001040b4184590744416010b44a05105810b50b0f5541c28500b8509600c0303880070407003811007007080200481e03250820301c1c03490a010a0741e15080283d4400f52141311012960742d103000c1840c07000d151089c0e041da600118080c000210b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 407962419 1250 407961169 407961221
    0x1a070c18021809070f2a050a03020d0f05090f130c2c0d080307050c03040806160305070206011a0408010203100f0f0b03061e0603070c02010f02010e0a060f 68
    0xe5070140c42d103182200401448008142811501c0511130b404c3d665880050714507950044501c001c400710003000d100300030001c03030004160074141116007911600080079101c00514000e82401c0c2802606010311602055128102d5004004c80e2a81201200c8100214040000103020f5000040040012074a4800c1d04401503800500c00080d42091529018440c0811003c0d00382c507182a4140d144c0183c4019070060024142d0005150031103803074203085041410703580200e443e5400a0348260b40c0c03a444001130000b0000f402c00124010980380c81c00340003504d041400a559030354184a94005250114240895114604240e9019040300c8000751341c1d80c01c00d00018400e40585010300c400620f12518000b81c10b1100c00c0c60801112100044141550740d031208100b00c011140207081000840c5010007903a80d07541c1401140300300c0d9243c071403112829a60000515082407a00c45c0d40c01d6a04d8405209403000740012040340081d0b00041c0401c00d15440d0711400040c03e0203000010f552aa10700380040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 407963669 1250 407962419 407962421
    0x121806030a11180909030a090e0705160f0201090603090b040201110c0301240e09121c0203040503070c1707090905190b010303260a02220b07020411041a070c18 70
    0x41c0e02c5404c4465440341c0c1c80b59121a500d070322611a00c0300c00f050390303050100102811140c1c5140e0201090820078101055010ba5600ca6144044201d072180071043c086400c568001640c00042d00041c0303030411080d00c451b03130764002d040e8010744042d040c006080c0420784003240c01c1058181f0068094000e1000c0003503201c46101120078802c04000b1188103c50201d0f00d00c0103020300a00c2003551100410241100c10006442d40e4403c1280844004001d0405402840640011806544100011959032102d0700b8000c038440541d821840c1140700900703441d1354000d0009031410a9039005400010001c0b44c40c50003524011030900040300003c658a1208140003c100e0038038101d0307000b40c462011061100965116011104180d07511102844010800c140a40d90103403402d007540c01460091011003812001000600358040218074100042c400118101801002a0001d6032080b140c20b0074209022075103070020450324444c605401040403002e000c21340c10b0001c0100048400380505051030740c1404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 407964919 1250 407963669 407963707
    0x14041e030c1e0b03040c120f060204060f0f09050928110909092107020d0c09020901030e06040210031e0c050d06080604020d02010810080303150102121806030a11 71
    0xc00034841a10000f4150203400226441103601c154406480c4d410f0040d10100d034581c003203041c0c03841c260b00307101e42e0300007081440100041c0c411501e4484560100c04002440b0181d0603409104000c4c400b038080116441d0b40504075040000c2306010704166040007100309078500c840d0446008603007400a8145a2500c0000614541c50165a407483c60307501c441c040c1e5510920707040d44e401d5140e4104040300b0761058a50191660900c000e1024a0012140c0c544c01c00352200c50b0040940c1990028441502d0342e0184202904090f00740003411003072406800080c070300e8021f50b0384002816190110310405c0480d04003401000d4400f0902003000040b41c410081c0550800741c2c0148110745841d4001c11100d40001c0c400d441185d008000c0400c0860b1580112101180503010035001c05404001142c001000c0c030185108807500c6007045000c0c00754900083c5020750b41c0c280840c4290741040034407084140340f10100d6a843d8160340c240e40c1c0741c0f10070f180300740200120740c24080c16210204081d00c603900006025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 407966169 1250 407964919 407964959
    0x1509030206130f081c1401180c09090b03030f070c0302091503060a0c1209030512150607060b1903110301060e090c04090c03050619050714041e030c 65
    0x44072aa528400410800355680750058006001c008100c000524040001c00c2c01c440860390000b84031060300201010345003c40311036036034918050010312085030610300e149004056034001307018165602038045e104c62440e000d44120390740ca643c940c42d5143c6007003007250060004c80e903400d6641c606074205a80810a2800101c2c070400400c4c0200c2c10328011601258014072009028295a0b203075105071600910414800c0818007003008044684071541d0b1041d0744103107000740c60b1240e43d10801e48d02c185214400401131300c141c8100c980e100c40c00d61211780a540301c03181c0c88000050708a10000014a500b506c40e941c0e40a60700f041c2c072000c010803541c0010700750302500c140c1c020710007261202d0000800f4002201c042005610000d0945c10f80d03d003503000340f802039020b11201e04120303899840715070070050211075a0211815040c10034284510600c101ca9100c0124908041e0500081c0b031091050701c0381d48900e9200b6520030b00b100410015500d8004015580460840d031807032b5440c000303140a100c0c80944 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 407967419 1250 407966169 407966173
    0x2030a02010606170c07031404060504030311060f010e040c030b010f151418040905070603290d03050f16140c010203041805280213120f11030a15090302 67
    0x10005105010b0303031020200301144d00d4652040d940d5190152501c0d01700c02c0c416801c2002c82d417030003201f03450f000e001040501141c1d51020f5480313045040203464034001e500320700460b9002c030040101d0440001580380c150b91007242607615036191407c01200701200c81c2c101a10322401c80300005500309044810104403005d41051039400b0410030000c1c1c4102001c0528694203410800484000780399008910b41d006500400c00a00d049003901c4052130001144c00035400710750340c2d108500801109880034520701030414114050380200c880850721070306028074000c062040c081081083d000c0e0107415101c415500030342c85682c0c0700d0182002402042808803c64480c0100300000103503505c0032003241e041d106460100f00340207602100110050000904500081256900702d8003c80107234148400d080801301c6d005601c07441c1d104100081f010140d8010302c030131034042c4400800100b201241d283c10725001020341c880d0514580100703007813000c4a4401030041040015441d2040f0840e030061170228004c0d13013 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 407968669 1250 407967419 407967431
    0x30f0d06150c0b0609100306050a05070305102301050c01140612030a050418020c0a0f05070e15040903030e070308040e090c1c050c040204081f1b080c091002030a0201 73
    0x5040c1c62258140201400820103c4000b841a06000c0f107141e801c0a00105006012035072615000d040390b50658060040680718400d01070340a515000302c0760040080399080c0042c1d0b140c1a101955600c46c80b8080104400320184210941e02509c251503d50b207002d402408510018000c040002e0000c0b100e09105a02c0c5503140c10008200100382c40d00c9a4044d100d0604d018140039000b002811064102a811a001c01800d110083c040c4070004045201b00c4008403000813918000e400d26240360031038204000030714200849802c0000c040301103a501500d0009000c1030740c0c02c04401508203984003111900c0349a500204008160740100100c490102d4400a26101c1d45040754480b001c0c48000d5130b00203008401c10102001c4d4443c80321074a480380003101c2103000040b010600707070b0b00f19901c82c0840d42c103d1098408181c5000d440e03007113402003851b401c004600b4801380c000c95010304034141404015420000901c0032505500b2a400341500400c0803408110301a0001d55039888144414015400c0030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 407969919 1250 407968669 407968709
    0xd06091b050a0308090d120801090f09080307211805011409070314010605150a020c010f051b07030605160f090303050a2114090c0906130509030f0d06 66
    0x10300025500001e211258492840c0c54000c0c8581040c0032096100045900700c0c030001780000c100000b082e095072240d584070b61405c1c10700400c8580c41d0044172485414142c80c1c0c00010b685408a81d4008000d0900c840074041440819840100e0301070b072526190b00c1c081d00301140003203c41600c0080e80c0302e0402407016804154420f044100103440c10a1298040b540c20720000300c540c0c00ca0140d50303600c0303800001e190fa507480000f80c00030b03500b094000300301c0000110203c00b503074103000d041e0310000b080c280748413034040700305006046105040a60b50100480f40280c80c250310240245d00003190001418012070619051000321511500191400300e2451301c041c0000e02e001e4101203007182d4145e2220707410000c0740b58090391109804812000100410241c4111059040c8540d8070440e540046640b01858004061890401383c0c4034030700d00c02d84c40801008110750f2500d05410694204100104403900c406071054650701807038400e2551800b0201f03041050aa05900100894940c5070f0541c010441c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 407971169 1250 407969919 407969963
    0xe030c062a0403050d030902030f0d050703032921060408042903070804030306080d030912111209010903020a12201e0f040e030409150e0121020d0609 66
    0x2c1d20004203160450920f01401071701981c0318101c218009001d480011860950041c00e03d031004910001140021448000780b50303051040c549511092944000d0b8049015101d40b0600b148070103441c4121940701c400040000200c20510f256010f21048441d00d05051800b052150050300403011000905110035969084048800c2d03202a0000b16007890b54850300401c86424000030000d800740341d115031001408401c10400017181c111030f5980007e19100a1070903c6007103d0b088180c108014007000c5c28003021401140c03442d00081d04c02183c0d42e070f601d041c10060382d07440c13040c2d40042c3d48540c8624000403145940c4000c059002d2040c225005412004d8050300030800031400101e40200302404008240c2040140c2900420801054440f0a80c61080001c041c0d80210007528030a410101d020008003181e4050035802400282800070791900b07001e914070f250b44c41441001108030440c914400290000c404d030102c41500904001d03c500d0741d90600304085c200048040f661003c9181c20000141a8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 407972419 1250 407971169 407971177
    0xd020315040c0813021504080309090a05072f0a050d080108010522060b13020d060b0c120318070e1f0e0c090118030506040212150106030e030c062a 65
    0x1030340c94034070140d21002c1c41e5102001c44d1a900300e81100901003101e09050b0540040c5c401080314400442c3d80e020507005020710404050001080315042c4414803800d190800034103100c00104000905007081500000b81500100d00c0005516004404400d400e025010480c040c8254080d106c0001607640c0d041903908031042169072940248200001c07440500c16840c0035140107025100108649907a1000221640881a018a8040c0c0e00207038a4000802a000302c038014482000654185042441441e885195050b04903800d80400070008030000b200701c034981040c45141c01250001522519982e22000c81554005007240740044042c03241442c401c3c242080c1c8045886200c0d40f500c8100ca03d460315080749050a062000d60001406400110000384009501540c002d0906090600600810210a105030011900803100707506181c010805d40d03604458143c0350010b0150b0074003040314154010704001703601341d02a5405000e002c0c100c0103801b0f034558a0100c0d5a42000d0354403040c5120b43d100d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 407973669 1250 407972419 407972441
    0x80c0405090106030911090f01090b090f04020f2202030a0b041814100e0c010807050a08072102070b010602010506010c0f0209061f09060806010f1b06110d02031504 72
    0x2041c0c1c005021061298001c43c4280e40310300701401c42980c00400041031114111038000442100d0401003210f048203004001910703500382c40302c083e2403c10352105202d1a0005001a000c0d880c6010000c43e00d45170040d440c24024400c5400d01e45800044841001079030040d6101010075040403040203107480c0520440e4000c00241099251400c07081e0783d00701203400286c11918041c01920fa404001c4407450281a40c0c0e8921107001d01304052200001410141c1d0103403003030b41040814401c4a4800307400c074404540150306800d0000215100c030180c1c02004285810781400c450002c81d4542c00c12800401440c181c84041d0000d02c03040d41e60000440b80b080340b151029280c84003a510403c00b41c2040840350b038204101802c1121119a0902c40300b015030410305214000402074441042aa544043d83c01d4000800346800c4515440b58180100300d4040c494968100da0324201241e070402c4250f038030568100a886490b29110845041c42e07800a4201b10341010501000c28680340f12443c242c4100e0300000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 407974919 1250 407973669 407973679
    0xc040f0507020c0d05120406031b03060501051c091709040c0e030304090506060717071124181c020a05040507140a03090f0b0a1404150e15070f080c0405 67
    0x50f0f6080104400702c2c84160007a038a03400b980079420384103212400204041c00082e00e001c5241e0070038a4022074907400d21508282018508402442180e82c000100d44000190010714082c60358280c0d405001031080220050403025103d00350401203007543c000d003440a00c2283d0801201c0000380c02920128071404449500d6001004144500c2030568003580d008030004c1d100506142542d40d540350320300f030145510b841140000c0b41007420000c00c0321602d20f5568080c0c03071f00b03600c1c4c00c03412811824104011207085904000031900900304503030030341a1520324030700130700700f2895032628540c1c20070242c60103406034000c500002d00860796040c81cac0226409960241e4682c3c420428652004d009070300009807141c205502c800310790012461042c1c00043d000c1c01341c0220841c0e801c142c003d501c11240c0d4010505000308400080102046112030040d494a01c101d401048844003205290f041c12441d880520503668102e007400341040d803240c00d842d445078850700c41c140d054440603d072010324000d522502e6400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 407976169 1250 407974919 407974933
    0x19090506070309050c030d0305040507060c020d030806040b0a090509010c0206040f0209040516180c030e150c090a0306020702030c090412142a121e0304020319050c040f050702 77
    0x74030711030703401a00e50b80e01903010740b0310b4040c41d08002804c04000c007100c00c00090704ca109100c240502401500001c1405e030509100e016441c0c1e0104c1c2e00d21040c0791014040c42500000a03010781c44a0308940c4110324020142c07130500784c482d01458000c2c141650406825882d046608030464000604a80540e81054084600b440711f6030800c001c980008000b16000d0003034900c14035011050044401c00707020031032031003481c00c00e4009486c0111141080032504060600c07480f441800e03000700d58081c204001003040c2c24543c1d82d56180540520642040580080d22010000709000b496400f030500c0314030803070030789852600e4602008090701c01600c0140080030000d5100380700301d008000084c808003400d941d05080800c04c11040202c91010564509240301000355442168400d0164000085c901400142460140800540c40a04084690b0521070000000c0380035503804108200c0912804002e624003005140b0f03241d521000c004840e0382c0901d060480e0340c84990628054a0712440c4591700400d02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 407977419 1250 407976169 407976181
    0x60f14070201211b08010e040b06042310050609130e0115080a05060a02040609091a0d050d080603010513080310090626120318070e010e19090506 64
    0x41a404920100d0600050081842c3c102c4400d50004841405201c030019444401d40304240140c08210210003c00000b100103001c080c1a410340e254209800a000c0340c1e0326a03900000c41c00030481c00c038041c100d40c010646400316564070903a0710351280b03034000a0a0221507607402880424060801d100f0340c8a014009010903e5896620003000015104004a1403609080c0c0d8064030b100c46030006140d5410030f80360141440f00c2080210f4020907140d20451826251100080601c0001c1c054020002e4455110b412102c0c0d6034003061810480c002c000703182e0504203240181c7c0d20030043c040748001c02d82e4103001a54034601032041706e22920f03030365000ba070f02c900c410b80e00c01e84554401410000c6040f040b08010450126500c07402e400ba00d000701c5020a03035108550001302c0c03002041d0328105250b01900c1c000c260b100010083c2d98119111610b9044000802600941006810b810078514141c2c120000103148000ca0061400b86001c10b0100c0f444140005070320050b81e10050001d03000c2d41c818404551307 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 407978669 1250 407977419 407977457
    0x10020c1201060506130e0906060307170307080409050f13020105190c060911190f03030c0c1a091201020a0f051803030d0903020f06091207060b0d03090f060f 69
    0x600d56808000168258807000081d449801482e284085410400c00c180244400541020342050343c1a000340075901e00000003130303070b140c9581c051040782104200316012501d000708180c8048a41c44403d40782c4445d111403103800103000486000c490b8001e0880406c84800d400041442003e0701039480c80c0c0b410744103509821030701d414a460720301003284500000011803024410f00003030758400e150444815028a01308107610340703120004050300c103400380100807501040d82c0050071243e050500c0000308a05040110442004e40c2c002e01096500c1101c0c884c50320107040003440003000c01c0b00c0b0f05200d2000120724a00300e019090f1100d010810045801d4002402000904150b41c0d440304400c40d50300392500442e0135a0000544821050f07280c1c0c10300c008068040c440740d1045c0904c000140460701d09041c11a0303039881c1a403918158500005042e1091043c580c11980e581400a86201c4d801543d40c80c004000103014403514030115030003003010070018456245003141c07900f603a0320701d0740100000380004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 407979919 1250 407978669 407978689
    0x10e060a1d0604030f0302060906180309100e0307140310020703050313060b0a030605060909150103080c070e0c070c06050a0e0f06040302092401020d051b010e0f0a060b10020c 77
    0x782e000310144000000540394645a50205200354050300702414801c00b82032600c0f0014004140c101c0340741403407181018000040d5a1551412901c0c014940ca906000781e0302424a60b01940d0540100800442d191417000c4103083c000d00207800b1945c9080164001070204d00650a0080005078200302090b120010640c551481034081c3c1c00003d00c000c030100010320b1420f450385c81140d00340d0b01c50040241070f240035044568032050100103440390b8155802c06080c6000e0502000f0705a46011961540110b400c20540020b0a0880c601d00c02a050882d185101600010406c0306d100e0200c40d804140a48641c0030340d160704125440f01d08111110300200a00e44910021168000c101800000003682e15145020302070502441e503192002c1c2072920074980b5003012107030b4605540c0116280c0100c80d5000c8110765a090072000c001c5d1035040c041d14982d002d04612911807440d0300c94000c01204030000401d41c6036460344035100c100403143c2010148104140c0c02e001d031038090717080303003008070070604200d1050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 407981169 1250 407979919 407979977
    0x1005040209100c0312051006180b0a0c0314041410020a02011b0302012301050118050d0602090d0203100e0d0c08070f030908010515120c0906060f09090f06010e060a 72
    0x19171744103008000c104403031085910995040c0144c1c802c01646030000d02c4c48408414075100c1e400820b0074012511520312550040320200b05411403100181841070001155801c201c010082d9601d030380300c03540320700c0c0c0f0145a8400c0c42016240781085a01f40006490100c440d07040e19a81400940040703948020041d0240660555407500e8103002c0f80c503480039201400307040103500d0b0101c41d41010001066666000c0c401d07140782105420922032965103080300c08003594002c8025035a0404800424405103a04200940501c1900e080224807503403a0132040c0c03003000c014129515980d2080c401c44410000a00144c180710302003180d6000308040c80080b0180354002d04007414406c0e039620b0360781d08650003207822100b80802c0520400c498549408595040c48a0354010000c3c00d1300d40c0002940c2034009801584038090006070f4483c41c0c000b20041c0c403c4c03001c005045240e240340107179100c002d610701150000d0006085c2204c4006e24500b10007903418110071665012510382c41480d080c801500e5070020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 407982419 1250 407981169 407981177
    0x607081806010f08160b160804050418260301031103010b092a1911010f0c090509060102030316030e070e04080a0207080c0d060906090b09061005040209100c03 70
    0x1240c0c020305820000d9a00828500c1035003030b42c0d241341041045c1025031070040300742c0241c08040c0404c44480302009454500c040f64400000142c003a141110043c882c0d0740c80b036500281010740070401c1540500100642d180108101080328400c00502d0b42a02000c070000d0180803818001840850315541c482001e031500980002590f003d03010004500810440704019501e200400c14070103024078001e002200303601010f00c141000605e0310600940fa4401d54100100300c81d425900c180f214094201241c5a42c003000308010403440003c000341109610700079a40a510b52101250280d440081124840c0b03c2d4640e900346c401841d02000c80140170161001045403107074202c081881062003901a005910074582150303200055040a03042c200541d0010010b90805440c2003225215034103460880c80e03000c00c0010340c0c08070034136050004004c04d401c0a41307100c0c107100070031020460009005d03010701c0c01d4203040c0c0d249941d100c007000103030320840800c25008008240796030b0760740d8015442800707034500c0f03418 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 407983669 1250 407982419 407982451
    0x80a0902060f0a020d0e090f090a060609020903070812070b04170d1a09010f1814070908120901170a09020d050c1801050a3012090512060708 62
    0x5407031034000704004840000c0c001007500c0702c40d804000020010200c1c0c24040c0342900008001841c1c900020481002e00044000003100d0034001d01402da2074039408042001400d880d8031008000750031180e0154060310442e58041001c4d000014031030081300c1107004091400d40a507940e0500588040d004481c0c0148010b00700c0c40e81c00e52031010300304510031424006424070203d801391300d10303101601180e40203032444001030101d0301c3c0034410b660a03190740180501c42843c251040b880101219002c9010b0001c2d5001030000a84d48a0070440171a145901101e41c01074140c500361200f48121014540420001c0f000c9520b104000100301341d00c404034410004407910280c0100309070b0029a00c2c21a00c50304032440d0b400d59403411681540c4c3e00907400343c09800543c100b0010866040550080182003141e20200850134840c40c2d0b0529580c840c88010200c070200c991510550308060300d20540c01151300c0d2500440c050030500350425203815008010400360b142c1d4003094818040140080140003a021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 407984919 1250 407983669 407983673
    0x70603150b0315041103072a0c0e07030e031602010311090301090605063f0a0c08010204030b0c0703051603120207050a05010501120c090b0d0c1412070602070303080a09 74
    0x2a018612441d03c1003800803c2c1e42c103c500300000c4410304003004114460170704c2801a100e502c0041440d9100c08080d0210101d00e03224044440d032203d4080040002030074a0780414810018801203004e0b07011502d0500a810805d1069a20703402181311001d1401541d03400710b0301640c866041540b45000e6501100c0c40d10030072801180c2550b24440040e600540c81320140100f07402d1240030b01c0c4d06a5139500c480034989184107004480c20313043d5201140401381d1203c84d140308184c00e0101c400b00d40d9009142e214920350b9852164042c5d0031510054a803803000f070300003948e05900481140d01d803e81c155070340b030700d00b021031210901481c015070070550800c0200e82040210b0503c510040c241c807030244000f4150950545445821b6480503003221072661090b6115000180402003268241c0b4500000401c501405101007940e0141c22000609a5188070030700182030060f44881015003441501c83c80d191000900d01c01c0e581c0d110920076140140d018a80804c08248280d01030b0390050040100400c2c40c4410b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 407986169 1250 407984919 407984939
    0x81302010302190e0a060305010609180e06090609070503060114010518121e01090b06061b010c0c0302010b030d120c020109120906021b0612040f02030604030f020c011107060315 78
    0x43c0c2c0c0408041180116080c2651a00d407514400802203441c05000c5981030400081c0712034041c0c810046081c54128007203858a03403541100020031905412180c051512005169461805440200d0107004200e008641030601103a07481c181e0b8511010420072100c4000110b541d680272440a201c003c04031a485410395603540580180032120000130b103481280c0e1155101c00f044d1640c640e044903850050004000740d1202020340d8040301c21100c01c1d4680c64000e0b41c5031031480012140362802e510f4008460313512508100811440e60281d8001c100d041204e030300b816510707411403c4075404211800380d580d041984980107419008814030000c2110308803942d0740380072440c1e4603180c08045151382c503040c00501da04001e0000080c09804507481c00d409480e0114480340700e101404507001c000c09001800303218440c9007140c40303140c0c01340446102c0c0c540343c01e0080c105188036900700014002c40b40c07001c29a40c031400009080e1a100005003401a14002c0150000c2101081e1042d82c840c041d4130000e00d003051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 407987419 1250 407986169 407986207
    0xf073b0c0d05070f021204050a0501050705030d0203010e1501020d0e09060a0e1003050d080c0904051e09010b090a0e06060d0c0f060e030111040b2a07080c030f0d081302010302 77
    0x210340c49600c1c0241c5551300113418004004c2900703401e940c062004100541e500304880007120420b080c20790b40e68090781042c506602c1400c554502e2140004000180000101070180c0310302d41ca50700710900720041000490712010f160144100080c509002d102d00d529096104a800210060410603403d80d02d101b4619481412545072180d011042d00c200309001060140008000452030a40c510746402c000c0084c85000742301c600350183d941d401c0003401c480349010340304603c4402545040c4052a00c8981107010300f051030171540c00b82c10644041340300350500d0300680d104c080e011b0380900141d0361210244000c030b00809500340c4000303101000004085c2040681e0390082d0041d0b039100c40d18414618103160a460200d4014800c80d00c003000100141a280702c1691000070220362540155a4105107000b00e022590700080081d000d01c0c0000078841c0c80000f0786940c04581a826a0007900c2644051500c40140b017802e0340206000740006001c40e98140900d8a5441c0305040040c101240c5550f440c84c543c0c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 407988669 1250 407987419 407987431
    0xd0f0b040e16090b01023007110102010608010c05180f0402071b1a0a030f0f020c07030302120702090402010c08130906030209100312050a050c0f073b0c0d05 69
    0x41542c004500640d480a0024006a2606220110703942d00004d54035034100034010865410350440d00d042038104840070102d8161580100e8980846060442c0f0020500032110301540c030b440c8001903008010300414201314616120542046102420b4080744203004440302d9010300d002410f011325170766500c003511555006118500013401411403007002501d0a070064420200203200d1b03154250b4240c42241c842c06a03078540400c010001c00d4011020b0410708140e05c4820b8004074100c505840c0016031103040340e0017a0300700c9030080c10f00d040c40600d51265000c06500003424000090165028000c44144544075441d45442c0020100300c09911000c0c075045424801d0b00d0304410800d5113020b044c101d4000c5500320a1039141171951b40d55500050000b000201800701c08503030400e61502031029a0b0360b0944503425101012100c1a03103d0310b43c4074a01903840292038201040302c04200c21610380c201800c0b401000e0300c250349004d1001a0030440104001c503641c03010003481d07880000307078019503014903 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 407989919 1250 407988669 407988673
    0x120e010f0510060e030c0621071115012402030f03040f0b0919031112030c09040c0207080a110d240c0e0307050f01032409060b0f0d0f0b040e 62
    0x81410202480b8605042e8070080030040700036402c10665501090b001101c05040780d00b280e6a100700c1e040702440c0110f801d183e80124000804003d11150801201c0549003000403c0d104004411240702002c200e0130302036040c1400134040440e980300c0104082203c010700a004503410040405820545c030350080381d0464140c5110f00100081100004181d600018190302400028a020004024090400001404000401a02d4400860309100075007030300c5003010a5542d40c6c900700f00c01c20b070382c0d40c03200c0203040c0a00d24007001048040e2020070301c0025a10700f41c0c0503180310511a140c4003101d0640782085540803024085034000134003444400700f1166606611041116007944011003180d103445006020b100394200c07e030565640100c0c0e14810340e201120022200389190004800034400794034020f0034151040111a0020074103403d810880300d080000340103039525008401d520340611614851449014048980402e40c05c0c0c00c2106140c50a0030002221542071000809940300744540014903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 407991169 1250 407989919 407989921
    0x50d0c0303080604020f090405100510030e160308030a1a060c060a1508030d05090109050f061906180b0d020613030c09060303020307021302190908010f140601120e010f05 75
    0x142c02501869200348102d41c00c500f00302c1c404542c0035a9101d90700500780300f0791351407001580c0d20405211040181001901803c02a6a030f0080a4000d068200042e44580b00340181c0142100c4aa030808059a920212503802c685a508166010f49255441510310481005601540781c40707007000750000c0c103800c00003404035040a500d0282255222400040000394803841070007259130020450f14010002c00002131144d03a40160301d801000003c070000c15074018200307000c2240b440080c4850040300942201c1c01d04421003c0c0513001c85d855841071034501e501d0685400801310039a032102e0280c21000c4d0140b4203100c002d178005110355001c480350207050f42c104c441c01c0c018822140c44550241900c410100300d41d90441c0c07806541c9000e800802403007940150f00e224440c01054050300e00d2141440040f41c10341c402c442000d06130b48014003486100398030b0400320105c04001400740844031555003003d101e29864100044038620007103101c0000035600c485a1030820682441030703204030381840c9400905 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 407992419 1250 407991169 407991173
    0x1a070605060f0a060e060f0409090b090c030a060e0f0618010c0311040902071a010f0905090d1d270106020c0303043b0f0901150303050304120207050d0c03 68
    0x100d51000e00114000c280c0b1244003940b0740c4480d5507000c25a1011306241078002c890100050031481204400c0f81410004038001403202400e8220007955841028100c5003552000c607825035465081100e194183c0c4500c1060000c90318580c4403500b4040c5070019100780200c040211880c1c0350f0240d8446600e1040e101040581c51400e00c40e50340f1818992605011074500c50030344500d14000e82c007401807020350000e003410400c015068080702d0f01310400344050300c0c1d40e950082100d00318407500c1081d40850811000a09444010078080350300182605e070040000c42c0085030311540b11203500c0c1c094004000c04039511181611743c20116155401c4e40300c491072907041c80300081c03c01003220385080c001d0740140b009100402c1140005201103d0310b1014610501da1418851952500781c215031060400e031505026a0040e41907410380324000700030082c001200c2404a50300c8000042c031015002550500100380007540000e1020b100d504a071044450342c54407040000d1148000d207104036105c1d00702c2001041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 407993669 1250 407992419 407992421
    0x512090c12070602060c0a021903050309161d0402010e0607060504020f060c07090504050705041a0f060322050a05070b0301171501090903030908040f140402032e1a0706 74
    0x840441c0d110041d11810340361500103982c3d050040c0c10740964920200b800d51900d4420040e200040000081070f00e491116030402420b50741c401e42d85040a4019100f001300c0c55502080d26904858018492090500c1d520001c40d40c548005001241041124008031b5011350b69100900b50060245000003010306140c41000740c004020f52015003d90401d00821403174880c0413030001c00301d8405e00c80c04142c6580c2c40c9801810075865410241d4031518003401c4101e10402c0b2020400032010940f24002103220311001c00c0b404e4002200da00c07500d11150002034a81c10641c0011030301542c41502110f4a26000e540e9040c100440d0340c11012038000007100400c80000072811606076412110090a0018400000490254414015940c8250b1102d410b0010035102e980a07162a54000d90081d490315210014046440d105103d0f641e4110300c5441800030750f00c0c0c0340c0308490103082500b10303d08410441d201c0f0b452610501c0400d071032a44008203400151696000b000c0000400e81c03810881e907624581c5032142c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 407994919 1250 407993669 407993689
    0x60507111e03011b050304030c0f080a031d12160c0e01030803061009081b180a020309010c02010e0a02040b1309050a0c0608090d2f150f190c0512090c 66
    0x160b002e02030780703442000e903000001c81f5041601481c2010302144541801400501207600040440400003011030106034035501414480c0552001000c0e001c81488000d59940c13044180d01c42c0007901080020480314032110420a524410480d04180541e00e071031480c2141c0090780151018a4000204425440c14410410100896003080d2001505000010780d50f034181c0071100610041e0705503070700d8159036495000b55040103d5507a9408070302d0040280000303501700340c0c2c0581407582000d840115050040c0107940300001070100501b040d00c4150208006844180702d00741d00801102c80c203040e00800d50081204407402a002440080400d00c0d16042040c0d0f1603204504010210702802514140404c03900041c1c02c041c60490120b40c2884c01d0303c20741003008051031829424118011110100c0031074504418124402d110015646031748484500307280071103401c400484035003110003c8140650000d10b45e00c0180c80c00c0340c00d214004219090000c02982d00781d04582c0000c14040d2245820080301e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 407996169 1250 407994919 407994941
    0x60f0210021c0b06040b03011221021c0c0506060d1103120a080c1204140c1c14010c0f0f181205062401030f0e07030c081203040c060507111e0301 64
    0x31442e15140c0380c00c43c941d50106001c2e224010010801900500c807030141c0703903000d50190600c030489c030070ac0e0700401a41d0350012030700c4201820031911040020728010f10860038030a1f080780103807490b5941c0300104001c81107102d4040707036103940c00c003403d0b01035450421081c0f1903680e66801c156519044454054490900140b102d80706400c1006072050b00143c3c07400043d041503014004480c0710444001050070200e42c08002070304800602001440d0045113400460000c0c001da043c0701b081104441400c0c26100e14403590804100c400001d07001c060f220340c0301c180f00d01d00549868410049808900c0340c030401b803503001c80c001c105000c0624040c05402c0c06020341110103c8007030740440e1503030704c940111008004503c605141e9603041103040702c1120b4010018610603d410f5881035030b00c0789005110700705107000b4243d2511072803c2c00f54104400360200c034062034019001d0703850780d850008100c03016400b11000b20b81200801c1c0d4510314a0703c40500003d041c418510504440480400c28142168119007007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 407997419 1250 407996169 407996179
    0x15060604030c03021017090d030f020301080604151b05030405190b0604021e0415020d0807200f0d090611010501050916110312070305010816060f0210021c0b 69
    0x2040000402001c040b500300d9074145e4040791841841031040da00310507611401ca8200c0060820070000040110301d040214100307840c1003005d0409810f48500b02d0100b4025081140c1c0010040b4002c500380301032020001d0010440811400c940d0315002007040351803620b0b1008a48003100b4001041420b01519484149861520005840c141c4402c40c40c00d0000d4107180c0626400074030034aa1940304100c2c9128811070381c002c580e403250b6030347d007813601840d16118400c0180102c00a00324000d204d4400c040c010f00d1203984004c0da58001802100d2040d15450040410b44200e001c580e01c0c0c00824010000718500c00d44415864030f107420710140840d1100c2d038001b0140c1e4075210045c00aa83c801c140541c010251510f030781e5258a94900c166800306400c000c2981030710020403404050350300f2480440c8112400e0f902401240d036a0b98001c0d941750f003a204180003d54454a00f0322450b88a0440c0e9203000400b40304940c2d1480216100a00b00da10910000c0c4030807981c46540403000c1c003540901c81c141a4207441c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 407998669 1250 407997419 407997427
    0xc0e030318040c0e0a080a0b090a0b0f07030e1c030e010c021b0f0d0605011d01150e03011e09120c03020715030204090609140a0b0f01030506060d02040602150606 71
    0x1d9162000403603090303548141e80e255500f00c0c41070f2064560402c03101011307140900c0e0680755074a00795034007500300c0304541807074480c4002042024081007174090703640c1c000f0541800c2c0c5c41c0c0541012001c000142884109681c034500b0258200003040040d040e00c29035640010140d02ca120000c06450720200410910383c10002000b0b00182e0008130340a110030483c6074001681d2081e0001489038110700041071b8800342d0000180d0901001d43d0101d8101d941e4030301a05c880717800b4040f0401040c282440340300c1d403140b07014030f03065001c500943c050703030b20140c005000041d000f00c49a1441059603d01b41c0d400c40443d41c0340c0120080119810902030145d629081440e020741c9180d80c020b554101c24040d00c0c5884080020311003810f4040c4d01528080e00310150207209854840c1600c0009201507120400c95100c44408a101d00d42d55110b41d441c03040d0090502c10000324020019009400d01400340e58000500300238040601440c0c0c400740015100940c0600130303c56140711048490440505250304c03442c0100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 407999919 1250 407998669 407998687
    0xf030b030712080403120203030a0609060308040302042d2403050705100905030a030f27090c0203163002060103150e01150503010c08271603060c0e0303 67
    0x3034000845840340300b0405419202c0c90511420301a96000401301c0701d0f0100c00141c042c0d0088003070740c8908146001040355594440300c800590325244009003091508100c00d0016040c250000c2d411507420801207210700441000c030205d03840349015203210b4103540e100d2424034282c9000088841011090304160000d0861700c40c59116040d52140ca8071034002510501d03010307030284140500074000141550320340c00c000d08018140100c00d0424800041e251035000d03203c10040d01150f201900b051207030200183c14801a40001e107140ca081c0800d6100902c42c042810500501401544e80305580f00c18003902d0401221900c5c10b40c50086044282c81900c5000c0b030280d00007082ea045a4000c110b9500c1802040c0110004120b20601c01c54194244045c1c9032070802c0d0006c03d042103440c140c00800801c0780780c440032900401d0030741e2401d400503100303141c19500b14136800254401071440400c0c3c7e0507486454000398244502a4803c030f4000d0f40303440b5000c0c4074542010210940d03400075406075280000b80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 408001169 1250 407999919 407999923
    0x1308010b0a14090604020313050a030503042d11060c120408060112051c0903050d02150108070302010c02040f020f03100503010c03020c030a0305090f0a1a06060406050304030e01050904090b070f030b03 88
    0x40c440c600986e404400030b1503007001c00b400302101d25000b9080da00e00c06824100244035501c1210300362040c0702800407040c030703c0d81140826445800f1541d815901c04c541030703070303400003c1c05088501c1b5807021090242c170030b07000c80501070303440306580403004150740e58941500141403800591243d0201d90030280034001188003c50300104140c1c2c5804501ca804000e0001682d41c40a2500050114454401441c414a4001a5010000c036a6a208100b56a40c030241c85035241c03010f0000a000441c0101080010b00303154004500b01d180282c0c000d030030a18019030003100c0d500200c1d643c115208065408001c2800c0a124000085100e407406520f409900721100e91f8078428090000200769803080082d0b0140c0c001c0c041e0441c6412003809807090325040d4103004071400c108100300c180c0c0d4218800482d6213407910404031000c0f40c0c25900c0d00b03402c5644503181a0340180011040b241400300030003000185540358030402111510542c80c8004a0404040050419405402c000c05041c604405004c0780d60700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 408002419 1250 408001169 408001171
    0x2109031509070b0304060f0e0606040e0708120c1c0c0c0b070b01050607020102011b020a0204060807030302070605250c08063313061511121801051308010b0a1409 71
    0x4400f82403a40e9440340d28141000f015844841101701c0d01e004c80c8a41c1e00315012840320700460049030103001001004500684440c0c1c14032408105902060000c94000d1021020381154041c200c1070310b030321040e041700d07a510402c42c8145500000e94021710000400c0000d05400e4080c0c200040c650781071190b940d4443d1045003040c020315105603004101c41003168400d41000c0c508036030f170b07207400c030401d0b840400e011b07690b20101e40c030407031046041140210304000005401012260980c0c003e0451070724101007503ea81e0702c542c4100056800429800f220303c405a28440c40b0300d44581d221a080b6850049103030b042c00805401200d075501c44020302100007500e009007600c4103140800c59154101c3c843c2c00500e801d1501d04641d0a52828018009007d03103850401c520a0340c041e03141d01c11603e00039840151201d0ba40900721100d024207001c00101e00c400741400d0043c100303040c10114500200005006c4010300e199002c0e041580d1036000152150170204944c80003040201c2d01c907100ca42d62040007803a2100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 408003669 1250 408002419 408002429
    0xc1a07180e06151c1118061206042a1e0c0c060e030a02040906050103020f03030f030406050606091905030709020f070b0402040212040302010b01080f0720210903150907 74
    0x5003c9103400b141c2039050307407209011826000800080e55a54045880f5800c03046c1c80940301c0300c5443c0c509009007041d4040b144170904280c00315400c0e54624003080000c0805407810b00d40401846060015a4000400c842d8000351701d4545c910221080380e15050380300c540942801c100070100480c8400950395002403402d64096040852203000b01c04040307450260f98040280d88982401d103c0310901c4681d503c494146c1e80240c403801c840241c52418190389228158502100b040100000781c0414580c0e845141c0100000703040030300d00459000015000d0056500740e0004401c0384504000d58a0b0400080000709a0054198181118031148145500444e0700252101c100707840010210740e07a9a0403030303501c01c02c10f00c1100300c01c0c202420024000c140da090b1950204411202042c1383c1103650004030300c6600256a80c0ca186e01e509007401c5040d0790400c0c00c0c0b00329440752110040300c0f40004c00305442020f40e02105151900150000c0524104a44508100c0111101c0c20301040d05030105806d41524 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 408004919 1250 408003669 408003709
    0x90f1b02060f39160c05131e050402040207120201051e1608090f0a0c0e010e040c0303050c2a0a0e150d03090b0a030b01030f05070207060c1a07180e06 66
    0x461203803c08141d4859008001c900030340c01e0005078100b0462510380030a9a00580788441c140740e607141a10b04844005610f401d00365140600112145040c3d000181d02a101820150820702daa0ba01c6c0519540060b4400300580d4544082003070201c241c000c034200b51180e0300841c2c849410601d0703145c103c0444250090b0100000600050b40c04801003110215082000e070882e0040c1c1a542410002000e140c020f0101407034110000254459440303a0b82d5024640007001440722615664059132a82d200003145a16400f90310a81c0b003044a14015048401004a540d00e21190f9034000b0050701000030b0f0000c0480000b04814412018081031a80000c21320990b140340c0b00c11014101600c201900750f1011258540006a501c0c4807581038206c03800d180400e80f0b040c031096143d400d41e0401e450040324101c0050b88035001c02c1101e184950000404680141101481d28485803c19400c0800c100d81c82c0011a00c201440b91858580488550050281c060a0240fa0900e10001000b001003101030218031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 408006169 1250 408004919 408005011
    0xe0d030212040e01030b09070f0e0a150306060503011413030e060d02070510050a020712080a0207080409020703080601020d020a0807140d210c0207090f1b02060f 71
    0x140c000c0103040340040c041028103440b40e030388410305030011409000c11a558140180420010000002c400d0b06443d1106d68002000e82800050282041c00800d15031604c0c1d1107d440c0c204a82c122000b0b07901a6001d001c000c070760b0318140403c0c1802c0d100b401d1245103038100c00c0e000b007080250408024080759985443c0c000610b0011000042d0786020304543c1c03480311b40c030016103a0100103000a03100740d031500544003400386649050441b4101c0c09400d00c0904100c00d5180d0003040c080c4540740c50b40d1300000c00c0000604003480c0e5182c3c0409904035410407011340c0d40c006818428590081c1000340d00000c24401070951004002c0020344a85031000e00910b5440045215070030085034100d0b10401114900031610040c181c140002c02552a14600c0c58031280d00a000c0380050b03040380101804440c070b580041c9a4185000c8a8400428100c3d8401400c543d449034110010094059a0f5a100344554004c2c61241041c0d1607004000c500541041c0c0c00d00306024018400110602d01c0400b0317520700e2420341c480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 408007419 1250 408006169 408006173
    0x3010b071a07020a02041109090703050705040801092a0f060c02060d1b090f08031608090303070b01060306050f09060603270d1101050108190501140a0f0f0506010e0d 73
    0x144070621410340040c03140401050950003e040a43c40d40200c070284019845040300c07558500c188110745420098940000f003245010740c2000740c02c0f01c00c43c43d1651030141d40720003441c2140c118107030440c0c500f200c15900811860000d01c03081c1c80b620300d402c00111100d1074400d080040e400188900e00502c000900d116080d540c8020070350324030802c0c0d00000e1040c0038201e420412107407044810074022401c9004042800054942c1160540e40100300551400b0001403e11101d01403030001140c0100e010002000322752020b1025000b0f09204951011040d410103401a00703440c90f80e0000d6005009010081c10180c1c0c50551550300601c00b5200c00b03507203488060220500031040c442c1c0450303804028042402164000400c050780546590f01c814000300310320b41c060300ba1242031080d90069480340e40c080c198028000c6060243c43d11410001614810789503088002a0080701e52a6413242d5031200d45881102c28040d07151a9801404200028a04540003130942104000a0b034001c100c00c84440c42 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 408008669 1250 408007419 408007433
    0x10020f041a2209050703090b01092a030209030f0d080703180203010c020304081203060a0618091a01090b160b190203040f02040e15010e04081c06050301060b07020603010b07 76
    0x16035010600051824034514100c0754405040b207120340c040e19454600000d01c020301c00e00c80c1842c0180d115402c960301da46014900c202602840000d8001008100700111441c020800441500500340e00c003d0780720359881003011304110307000041d030038140c100c461041c1c03920307074800344240d4010864100080e07840d444076400142521031000080d0190702c0c1281201c2000c1d000400b40c02142d03003950442d001d114500c401040b4900055a54a800501da140306002e50b034014290aa4210303040e80c0300c0e841103559221400c00380d800b480c84140e89180000045070565a0154040020700501c0c0b038900d150644003102c42c060000202c20160030460f007800458a254400c071102c0d0001c0c0301c1d006007507417a82007a05080e102a264031a08a1145d450210764031038556010903404178140450b802011640e191030b4190140d49d40c024412140c01e5420040d03100c1803415070100605c016030012000442900b007406141c2181e585801000103048103004000042ea1140101d0307042d07c09030441240c42e10b01c1e61800038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 408009919 1250 408008669 408008677
    0x1807081b071a01080d0309050c09060303070206120601120905030d1d030403052a0109030308060d0605090c0103150b09010c26180402041d130c060f0210020f041a 71
    0x426a18031080700780d4491848501140c16604110117485d01c03140300c20010b4044503c042e070014401d803c88040745100c7d02d81034900e0707540107101600380c91070040c0a42c0094026440750f5600401c01a41506101040d40d1101020219040542c020800c1585c192a850303503a0265010120107e80c8403080420b0030480b051842d4100f40c055011283c0700c60316850040c0e102c1140e0083c4807150a1440c40c80302c680080d126000030140010307101c19040d5411501c044613003600c000c2003540c000a40003500720001300c42c2c0c800c45104000001c007401030902500c00060607650050440d024417001c02c1c0041c002c2110840407144045424200800c1030b0603640f038070b0209001c80044c5a844442155040220f1603444c1009003150317007a5003441d10000d85002c0400c8201e000d030340500707506c0200b03100c40705100e1016070b205550880300001d42da04007403542d0798a030b8814044d03c0e0080800110320b0250009401d80421003624100c0e501c050544c01c0520010594109010301c2c413519400046500c0d4220001104900315 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 408011169 1250 408009919 408009923
    0x30b011d0112050a0e0f03040e06090a02040503070b04170a02100c06150b03070f090308070816052509050c0724020c1609050402130507120e07051807081b07 69
    0x3e000c00c3c03800020000c001d04c07500860030341070300803d0381c417141a05010040b04c054030104403001c0403585544003805250707480201407818042d803c01010801e41d40c100000d40003002843d161594560403d404c540340c8140e0032031170301c0842d40260b9142e00140e85103010f150340004a442d094440301c8032814840041c08038080311004082d13413400c6c04030740701044400861091350f1680300da003498552000100c402c5109403001030701460003880b04600154030080280f00b1030000c2c801d20940d000c031945403241485032035140010b0709258001c00d5109414800008002042d1200382008640340242500d035680c811220000d052540c43c0f41040f401080701c000390740301242ea00c3c608540b9039120000c0300b5610003104040c428109400040000c01151701e000c0c15200320f502130055003040f280c003110316000d010f01500c62018400c0005101d648070030a0b1065900d440b090344000e141d014900400c3c440c0c9040d46140e9440202e505000b04503405410104864011802000b00c58181500f00c03581e40c2c86020346180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 408012419 1250 408011169 408011171
    0x40510020a0509210c03060f0f060a0314060a0b03010603080304080c010e061503060f06010519050f07060506040f02070317070e09010e09060a0204140d02032b02070501030b011d0112 80
    0x601c00500c15124100000d0a13040c0d01100c00360f0380007204255031590100e85211040b011480040c016003185041a500042c02420400c5400e84075a5450994148058900d005900c10000c011203082c2c83d020b42105200c05030002c00104c1d0642d100c1d00c0c0345100040c000350071550000340ca100c41c04000d5100f40e001040780b1094840e1400c00a032400c21000c68002c52510074856400412020094881c2050140304143c458500d000400d4030000d155100c5400e0140601c001030180d030000841010040030105e100f00380004051a1100420048400681e2041c0586105101c100b00290300131101032000c00030020b0784000381d40c40c0d2808030b490425400c1900d4200d031491000191080005000b2800f4000305019940700b0390b1450130718000c03402180701b018802c5c80d040751040303c503040200c1c0c49a4064000340940d180078916081c022364000c900c510b88812907180d000d122500359814060703640648824070f000c0c0009141c0c040005c11a455825442c60440218481c07030303160380e0203211603407010652014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 408013669 1250 408012419 408012439
    0x71e031508191101030605090106110a0b090f1c09030b040503130b0a020d14044a160c1401200a03180c17070909050115050405040510020a0509 63
    0x42c1207400c0040304104892200e000408000310350301038065801a02d401500592080c0c0c41c060040300c0482d0b003607010824174055141040041540031582d83d10403a40200104010700c4080800c51a292414124000e9041014144c9403426440040c45c1c040f02e4200c51b9142581d196810038909510480c10982d801210600001949280c1140900f221144030380988034010501071042ea0f40401c9044e4402100908100900a000f014403e4052201d500203806040c0c0c43c2240395030030749003411040142008410803d210300454a80042c66110204124a50552008000182021080c104d005242244a402904107504258015003440010f54140c14004083c20700d2900d2a9105c088103d001a042c40c041450041ba0801c1c102e101d1903101c18422071580c034040448040c696420318001e0b0600a0315000665120b56010f1442101e00a10000801806201484196044c0d960100340102c1c04c2400300030119030089620314035001e242c07101680c0c414481c20101c820703101c0c03050803a9122103800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 408014919 1250 408013669 408013693
    0xf010603050c0913030c15020c0111030109061e052403130b01050d02033c070e071b060b010905130501080c0102161203140a080906071e031508 63
    0x814044509054800d6100c9413109040c01440206811020b004140607601000000b600003500d0b2001c1d03e105480103045c59001d4407680c2c00d54002604404200002200500040c880c0b4441c10b8000d042110580781032800e60503a004100645e8031589100340c0f80c2645502d040c01c0d5410945131151940c2501a41e6860070411800c1005042071054899042504c00400c45091080920102c40c2e001001401c4103255940141c03202da100c0c00c001c5144220024000249114980d0104040c0041c2e1001d484502e04000d4458803030000180f81508104007074021050110380c8441d40c10b02c40d60880000b181030342e903540040e15080d150754401a0801c90204007030f20055aa82d0020b8180c3c3c1300c9500f40d40191a0341801241c0c0e66003108000718107603a00103020460740844420000001c1d2107400d0070900241803803074042042d00420000300c08541d0303071802c015403d00c051110550162103805d05080c00c41030081d61344c00801c0350100000c1403658405421070040d480054400042c0b00300022034400611079 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 408016169 1250 408014919 408014923
    0x2070314100e030a1d0a0f123305101e030b010f050f09070c060207120f09080607030b040605040905031309020403021302090103090b040506010501270e04050f01060305 74
    0x601d80c140c540d1840e0500e140041d40c000701c116000c0305900c1e41c0d100e82d1010500700c5034039543c0c491500164414900b400000b980d15070301603c2c600600c0c1c5c1c480703402c046400c681403941c056a2600c103d010107500d040a1981d50300030700340075a104400f403448000307401d940b01c48040c240031b462604154104275140c594104c00300c116108110a4900c920b17600001a41d07500310a84072072442c0e00815600500c00d8120700b01609010308115807090141c0782440d02901192900c1080b68008442602c40380c0d81c3e590301c107607013076042442200300e542c917850514a121325192240740c0311b0303e000e400b60301051348801e034400300340d03460360011409072800070001c1180e8415441c0c03180ea2035000c0101c041e04200020000a4031164a2090b5400c42c0c2d000340a841120380070076601c0c0001e42c8089445418142c2e1003000c2e0002c222a81c0940d48594480c500074545941480005000241c043d40302180c042482008000e2540344500c58070105c3d10400300c080c60544691800508043e01064002850361a00b8000410300c100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 408017419 1250 408016169 408016183
    0x5011d0c0d18170a021509030316050d0c0e040b0f1302030601030b0306130302010b01050a021009030c1b0f1e03060e190501020909010b040302012c0406030b0901050a0b18040302070314 81
    0x20940031180c2d0b00c1400b42c200706c6000c108039003041031904240001842800055000703200720440e0307d4603c0c9480040c50031641200c0081c00704000007000d83c01480300c43c2c1054070031415003041c02c0360354444d440104030009115800c0341e80e442d0001500400801d40c0e03a40039801680103500002c0a035901e0303241a04401840c1800c0c001c05900560814185d46155402a4110b51289030207501a24840c01040b040002800414604400700145200c59002181440c01c1540d8103002e00307408010103500c1c0401078104030002c1e41211414075840d902e5400030441e034512130011a41e11400100b01c0c0c11440032040e090910b07281c104c00c02a004000302c0010088107600410141c1c0e07080b901400f4070303601c8900700740c282e02403804001c0c00300744032000c065070f98024581640e06d41012030352500c000c8010702000c2429111310347d004480c00d1040c9800d104d0743c2d01082c02400d61201c0388132010440b5a480310001040c2210030f407405060442c3e1000440c00381882440014040c5412210f07030410307042c0b210750342c60391050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 408018669 1250 408017419 408017437
    0x110312090a09060503030307050717040801090c0f0b090d1703100f24030e07050a0b0a03202a012901020a030509010509030f1005011d0c0d1817 63
    0x6140710011582c01e24501c590340948001800660841d56800019203242e130005a00756119112240c1e807070140007881c402040a8408040040365144442c540052040030740d40290000b910204402c0c80850f071028142c40d280001200e100c0c883c0ca20b641862b04040c040b400c07520300640340001c2080f05800d00020b500b0b0450384e076000d51143c1c042d40c2d0300b42c4801d034005690414440e64044400004100c2c800d40140f94403000820540b089280c0c0d4070300180c001001039000c21000000882d84000386078251160001390150046c81001d41d8003070b040b6010085c41410140b09840b0f0020b0020140f0380c99103d264482003600c00001c00014407000c1c5840146113651188224800c1c140d101c50840354404201d009020780e142d00c4d220309261303030100103407040d402456800d0f03090320036403206441a01d41000b01c1071184103400030005895042c40e00c400307610410900b10803180c5030114244521900e4280445080c0000c81e500019044030301e203a101e000c02e00540c406060b0500341e1003040c540c203c60078000c0840704 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 408019919 1250 408018669 408018679
    0xa032303130305221707060305010b04060813060f020912030901020601051e450105040c09120c2c0c07061b030e0c040908090d11031209 60
    0x18510404204491008490018515181e55000000280520090100e05400d0a03d8481c3c2c1c0300046014081c1c0d51042e4800c501400420020441c0644c09008600160060f86401d10481d070420010380c0403489a03115010810400c080007411000059907020181544220140814080c0501c0701e07000c0e41140b1a030511820640200c540c15800000072504403802c1070300a846168601410401c404c1c0c0300701c446103102400d00301d8407070495480c1108200d102d201600910b030340004014540541d14849958615a0107a001c01904104541050181103403030464001c1402015042c08541022040d4080c00c40907050010b8681001502c0304104195468003094aa0901d4074403103455150446d10010200e0301d2084011814543c4100010300c0114043e05021a000c125880c5080d444a044000c240000307a440030310030840041401141407601d000c8500b4000c0762441e4945000c41d01c2041205885050464940c074100803520070108131130103005040d2242d210304032030008141d074040c42140e0712071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 408021169 1250 408019919 408019967
    0x60c0314040e1503010f02120103050706090b04031e08040803071a10030b0a151706060301140c0c01111606060902070f0308041406010b040305060f01060807031d0a03 73
    0xc16403100039a02111240d00580820751614030001d0403400010590760b406540716100407600c410640028114170301a090b0341030f05580f442c1421810401e0540080041150070707101000000c01c08803d403000d498000411440c1c1381c80826400803040701220b03005144e2100410000f90115012010300b000038080c88500908070401280150101411103194500500800050010556030400564881c0c0c071070a00045078407280214030900d111380d502c020b00d100da941c2c40544440302e040c0102d0b50000c005900074484000380420040c64a8002000c00015041c0415842c9002c10250002044041000641c0e1344d07900c1c80aa503d10130a110300c4040c0c80d00d031304240303000400c44460b108403203141e030304140300d07540e100305030369048492b00c4010703005640d1a03860700d1001034255010b000460084c8044030545595610754a80b160600d030004140000d04000e002c010003103160800300550f480040d40ca000a9121480725140e882420319419408051092500500406800403000031540704800c0c089400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 408022419 1250 408021169 408021197
    0xf080901090f0b09060f090d0c020f0603010b03071b02030d0c031209050f0c030307050601050f1311180f011e05041d0103061803050a140912010507090815040206180a060c03 76
    0x241c0d04094507c0c40241d400715145a00d41480350583d40e00b0688002c01c0061900f41c410002412a04203800614203200000244030199400002000e1008508156078000b04070300e8000a0302d481c4600349c1c600c24490010241801c06100d60281548241420404c00c40070026040c030540e076565124900c6040e101d04501000c542c035001055510706070f8014010f04042c0c0c01c00b028860703a00c80310012680c1000300c00c240c41000000601403070000c0484600e143d41c45048121880071000b00070561340780201c04044025140386d07032042020109035000d00c0d5100052550213000c4806100e16070000c0d4410720b501e110102820303240c035038041c1280e01500f814031800c0401080a41d980c212a0b0005010070400c0201c0c6212070b003d0540142441c00001c08030381400300c2ca00c04510b0b4040c4c07003200012103035500c5003004903043e08024400003811200c00104007861104001045000e006070000c1d03c00c06022920b091a21131140000d01a0700c0090a28510943c0d1400302801000c129030381100451070307111659035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 408023669 1250 408022419 408022441
    0x70207030f080906070c031208010906180b060d06090509060115090905100e010303030504021806060406050708071b03050706030c050702010e03010920120606010f080901090f0b0906 80
    0x3501d8024040da003000318181d40700c0419034010461550800d600b441508041800c3c40e05038002140500c01410300880f0840300148212030507085401c4240c98000e0510074004140c2d0b040c4101d94080b207001801e4240d050018ad41030083c2d980c5034591034141080403d050310160400350240400000b102c110381d81715400101c81115203036600c4001030480204100e10b0107584c118942241e1800c1d41c00d600340d5115038444107141c03426001900841d80354400d000c1181084110f0521404104041030064100500021850720a600c100070400c00c01040480511035420125001c503503000d0103c142140003100b4030045000b1911058407240540c2c01d002415501074020005446150b40e41c662910115a005442000c3c0e80840c1e9034040d9131711808000041d4660741e034140c51714076503403040c00c1c00c0c4480802c02440c40c2d07403480c082d4010f400c00070034800a660010202c048407001d070f007403038511503862034032007070040c40a660702800601c200780401060140b1240d41701d009203040710581da9566a0a0381d05a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 408024919 1250 408023669 408023683
    0x2306041406010f090b030c0a0e01030e071401050405030312070206090a0b06010c0f06050c1e041a0f0c070303080f090f100c030b04021c050105010f05160606090c02010e01050702 78
    0xc0119100040003074855885000d080301112001d050020620342c440030034402c0b540086071140c2c000c4100203002d9211a40000461a15000910303060103c50003866150b030300e6110078407031340395941052150456160f01074815503000c0c060180460751a0009140a80e0110a0941d441009402840041249160080760030b501a0303810084a4007551075010044560683d0303554140c8006400541060000740c0a01a45018041240640d600c804c0410381505040500e86501c25580b00e00308001c018401c580455000c0c1940b0440400d078988254030800340072403150000d112514008e0317850120425070442e060b24024a5072540000c05a030b64030ba803240c0e0701c00714840728000e40d5112114074410748401d504400d01d0407145140114198201001190a90700418148207070b4495440c491440c140701440b4140c0107100918110500b0101c8140240040c440d00b03828443c2c42010040c05400e21070035410050040004c000d08000008102400900a1440d40080c000315420840490070a52000840d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 408026169 1250 408024919 408024941
    0x8010b0702010e0f0405040605010315060602070b09040209030f030d060b03130210030b040903020a02150901080c092407050f0c06250b01080709060b03010b0a080910230604 76
    0x840c5000314940041d60411030301030800d94007000e1406030041c292910301400b401548258004078940d41186010b600c208590303230058502c9403411408202e415070010341002220b44901c00c00d030b9071f240c14001003030191080d0b01c00346415210f855841d102103600000185581d01c02c1460130043c2e1a21083d64803040e01c8140c87c9a14000796a03411500980341022060901c90024140041c110004c00042000c0e50704c050800e41c0582c011115039010360402c55100310000020103030b00c5140c240c035600060520722000c0d14460b07425001055030b4140d52200300b01c40390741801e00045150b601807001c4503461698004402169540144902604030316000102208006401000750f070070040020803440c24100a01c003c02c0e0b00304080c00f50305010910b880081c078040c02850001d000c3c164145822030b4190b928582c0310310300d43d610400040008480450544131540f0703003481c141e0119107a506d0030b5442c0c035031a581d520088510342001030601c802140d441da0381d502036002244543c2e569180c100000c0391809011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 408027419 1250 408026169 408026189
    0x9050a0c0e01051305030601060215150108013c1805010303051803070b0403080702100c050303040308071e091d0c2203170421120302030901230402010f0801 69
    0x14001e9030003400985030040d06281c1402d12550350300002440c156003a484000503800034a003600122059120060748050041ca40a00311a00b52000070100c0005215107203051008241560082600d181e14880302c441c446a60043c104511040010001c030510a41400c000c0340e0f01207040c00c912074080d05040707940545490f800d260860701c040001c0e045182d100c646c18050594042030340389084018001441c090404a0384410070752041c402e000b840101c503042485440403d201c0000c84c000212a032180d032518007541d81351a030603401d448021040100c1c805240304110003000315135012401d04116400513401482c1c2c511076241c8004030003410ba5458106181c2040344d030188140765440c640241c801640d50400031030307482d210000c0050207039800605500c03000400b0445001c3c1100c01e501200c04c0c1214940d04071400c0d03038a50000894100340ea00c1895004000a8000d60080d03011001b6001144595148840e032818013801c0080c007100c01b01c1c04190346800002e500c501c200c2d2164142c2e200540c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 408028669 1250 408027419 408027437
    0x8131104050c04030c03060c0e0d0b010b0a0c0605071701140a030f020a0b07080301031505130228080304240903030c0206070f0f0b07030203060303040302011119080409050a0c 77
    0x20901000d004010800420b1590800c07000000840882c400f20095002d000000754240d64210010701610b00540440d100301501c201010100e0040a140c60454034050041990781d44090403c0e98440c0c581c882c0a42214645410880e07550b421181301c0e4031a4110781c551805603a01e50081203010140d40c1d00c90760700004103034410b02c0040d00c04106150180c0c0000e00754020f566451850301015841071134110394113040800100100240c0a0301801d07000351001090101d8501219a41c4040d8454000a0706c0340e03002050240d40904030030180b045910700791070804542c4c1d07182c907862680c03a4843c0c41550302142588040240600d0303081c01d106403003032050303480341d484d603285840840d441c003401c0c2c000340c2c0c3c0400c0410030400040d061156601460b80f05020f100522200d0341840d40c00c0e03c800800e44824140104200102c07650f000c011074080d82d07824205805240400344089107845508510000120b81211020040c0f00ca101c012304125035811200f07015035a544450784050720200038104021610502d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 408029919 1250 408028669 408028703
    0x90605030903040305070f0f091107111203030a09050c0409081605030409020316020f120f071a070509030f0f1209040e1605100305010803030a0225030f0813 69
    0x20004681040c4a60201e9003030540ba034071001c1c2007150940c030450100310030031000c0100100c0078011400404031070742c003001079108024902a0502c10860300030031038030102186699a90b5204000041d603004403003102e4880c90146e02e1a002001e041c80103441e18440c400c11314105190070b00402c030206a002c4005410300e06101d07010f0b100220003080c11510b50200384004100740b00d903071000e035108151590020300c644a01d010003a081450024907040d0740c4d001900403c8500004404444610300c400801d0b9598000340e061100003400085a428891814030007800b1030903a2000250200d50801c0701599442c12095101541c6c401030004004401e402100014804030348c0c00000e400f89100191001caa062050750400f818a12102032891414071012024003444c00e000d0000c40c1d06d1411402c08001d02d50420183c030790349010040c840100c03681c00107400c8424182d0114440000b051520f01e0810701c0d01c142c80e0140003410742c03044070b0b400680c030320b00003400482480d200a40343d543c01c6000c48845212007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 408031169 1250 408029919 408029927
    0xe01270305070f030e1201020a0207051207052107171f0e060708010f05040b0f1e13090302010513080702040e03091011010e0a031202090a03150b040f0c0906 69
    0x208405400744203090196102280004241204491003591840c50180390002003110820b80070b030025015a02c140051134626400007413190036a001290a11004480042d07410315040858100c1b54004048030103009200305400c038104035808211095803003050300c030600c2100c1c96030b0700e07180280207a020010000c0004035100103c00c030001c1c01c6801249078012500c40318039204082d180000000d0f5288010400f01d00c0b030100703420282030103c1d009d200445e002c0000071f04002004440b140b0503030006400900c14426180008220940501807440311032070345105100a0003405030590145d400d160020368000385504000030301d1f0742d120400c03030b081c0340650302440f008151000e007455440c0710400154449076207035a0b50320b10414040e40ca8403101040e68044509481000c070300d00c809684841460381c0029042454a03d0703200b001d4000580702d41d1440001250821580e20280082114910b00c5c1882c002d0794005120030881a45d040c0300003007040b10f050044465098650380025021203003130082c0792007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 408032419 1250 408031169 408031241
    0xf1e12050c1e01030b0a060f0819090c1d010605160201030b12010207030e10091a09040c0509030105100302030717280c08010c02030f09190e0a0e01 65
    0x5942262022034040c404101c041410301410184066030440c0c0b0302456a250103100f041000070340315051503514028000d800350704c052020780203221041000644808030030048060280c18400240041710311b03070400d034020345820f01032009140741c290000b410b220592180c2c0c0b41241c659581e4146007420762070000f2080340300020200e04058407404501243d54501811041c84803058000580d02c054030726000d4006040c1042283c000c1212003041d85072140c02140d001c0441e103008403000d10034818202d00e442a8840d40402503405803a00491500c0181c2c040043d141e4160203030020802500c4441501d8007400484c0320081d410351000c0001c1c440c0c112180c6c040c00384400c2c0c000071601c00c404010004400c220320480840408001c40101e0800d00c2203141c2c20800401800c0f008020380010000c009440c2c0c898a154108007960010720003040c2d480b40c0e0384000c0e06110001c0740d0f84000d40c4400c40d018015105991004400341001c424842e00e40040c828054040200380150144015000f03005150310300c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 408033669 1250 408032419 408032423
    0xe07051614010f0527150708090708060a02030103141b0f0402040905091c170103061808070c060909230a1d060a0f0e0a0215040911040f1e12 62
    0x503c8824440009140f4080e840c0100c560122916000d810b040048124140448250b113140c0c0c06035160140f41041c0b000e05507003200f13143c07900200c9503842c0b180315880d104860740164424411b0302d080011490740b039805541a24410490550052541004a0b55410307080e88504400301c100403030241c5e1464441d1021034069800341015040c01d9807410910220b03542103950f040030350484529240300e2810103900c1514035030241083e890700d00b00b1040c120054981400010300d2183d5071901c40d181c4068a070350a508855001c0a0140c3c4d0703481038a0322489140703541c4154804150780400c00710f0702010300e00955010031004c80c0242003070210004c0c01c41950002030051514141e0301c540d440b0742d840080384140b0300030421200801003414000c5001d0226000e2040d90301d101407402e0341080200c2008a0036500443d01250030180d521030b480c0c01c50806100356406650030078174110704190781400072805030040790080302220403440c0e95100081d2070100c4141c1880300c2d51007112002c0c003803003020300c0010070414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 408034919 1250 408033669 408033671
    0x50c21030703200a12050601050307210902040203071d0f01050a14040f06080714031302040902040b040c03060303171509070905040204030312051b18010507020d03090e0705161401 79
    0x1080380802c1030f680c0292003031000504041484000c10041d4014103030004000e1800ca0316600d4048001805010349030000440100c80c0901d8009144898224100c6903400410440da6801d0030040641951207000e0110524010940300301030524180400503100c0c003040c3c60740f81c508100444119490826010b0301103c1070420701010420300c0d1000a0711000d461142c95214190415140c003618a84a0301c2c218058604100204006102900a41404203906440204d03030040c0360b20004015007981d0f40103d82091400010541d000d43c0b43d0040400c40380241c071040c40300c450014140c6503404003160869020200c0e0780c00e801003400c1c0b892025a208003a85401405507441c3c0c00002d050340d01c1903101b5400540346195640c0042e401e0300c589600b140c0c4854001c529005403050852440c0a02050402241e44e54182c42001d81d02030022502140d500800d549044801807134007030160106805102029000100080c2185024500705d800000d02141080c007500020742d91146000704214000d1215 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 408036169 1250 408034919 408034961
    0xb060d0e0f12180d0507030501020c070902182209110a060201091214041a03010f08030a0c02061606050a02030106080603030a1e03140a0c030e210d090b010303050c21030703 76
    0xc2101401b015019521600002d40e5410900c081d191074100c2e260001c4034120b10401001c202520620300c085041c1c081900c6809490000102e08005080c50301c0030803a0043c14015004c0030451064010341120f181260b0000c28a91524012070132124020350041807400b082243c001c0d118001c0c1007003060300f0100380b4030310315140c1c40e00e000c024051003040d01c54a40842c04070041c041c110442c0005005421074100131030402e00845001060800b004001070b0141900240c40304451903050400095185c20600c00e0005003030198110000303500900c0f40c000055021808143c240c80c0200840383c110380e01d555420140c000e10300100104042201a80043c19951441c10b10040123044000d8031450003100c000411409200b80641aa0706200b00100c541d002042c1c520881c0c000440710301c895844071300d0305944842140401800611031420301801480848000204155000c8000c01c40e070041441940d0780c401da0101507402d51001c480341440c0429007400041d8996210340c2c01140c1120b4414109a45 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 408037419 1250 408036169 408036173
    0xb060604080a06050420012705102705090106030507121d16150c06090c230d021c02010216150305010b120601050d0b060d0e0f12180d 59
    0x1a01901440031214541c4450401c010711440105294040d140c41046e1480c15280500007001c2c0020540942c1c0164009841c3d411541c0c2603116130006800040c1000341580100c00001d03000c2550020380c0b0809030141302c0303e19103a02880d02a01d0456070003601c008100e900345030007503000d048000c1c000c2d01003044071607142e0b810795040c2c00b502215805a020a03007501c0c00074a5a41d040030016030000c1c01e500c0d5005001c222410b4200d10519840d8072a140c62000d445140c82e00c000a13003071504002d42224400b00f4040f86803200021860032901c4d035003102d02c040c0c4c509101070180001020f803000c2e41c0f02c100102408100d0400d4041c1d1811244148113450641c04100b5500b0b40080c03041e0041191030301c00b4444004074036050320943d80500a0070700300605200703146c0141c03010b1250050070700c0c0c10030201140030051091550000c2c60160002842d00791114000c043c00f00c01012043c002c00c1c8544a59040c141800c0c1d804245101f40401c4c070000e4601c1c00030351000b59488106004481d42c2c00204603948200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 408038669 1250 408037419 408037423
    0xf0b03030a081b0d060e0708061f0908070f05030d0c050316080c01060603021c0e0c010c0305040b040902090a120b0f0c0f041d16090e0c0c011503020108100e040b06060408 75
    0x14048010081c0017031024249030884901c1000103007440144004030702400503d0b6610b043c24001c514002d003a51211030200041124201b11542c040380c00c901c504000490a03281d002d10701c00554105408075090a40d082d8000c030b440d110366100c0a8442e810170000c1d010a601d22044180200303005003003003071030300349881001421640d960f8048000a0390106001001c10001400f4103d18a003010051046e02200302070300ea10390203078800490510052b08441420180039800b59001004100b00040d143c640d105c075414041e600280540348600c074006000310348041c48040041105400010003140e5580740d054035801068003038500d5603851300c207210980903014520300910203841107600c6402c0c1c1094288150b002840701901c210a40301c401c24001c80200e90180c0400300b22561026501829140c5404000c40303803081d50109080c0b542000c4004c081e40030f07180312001c21070b0b200ba0381c7c0e80c4103030347e0310f40c2102d002e01e00710300070304c92031501540200340460308402c001604008020b00c41403506548030442c85c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 408039919 1250 408038669 408038677
    0x507062a032a031101110708040506030703090506010e0405070902030906130c05060408030403020901080708031602010c061113080316060b06040506041d10060c0209100503060a0207060f0b03030a081b 88
    0x8000598580c81e131030b2004000e010f560080300641a215040100a0f650218140564022180941008000074100310320a800400d01c0c40c0d006001e94180307503101c0c010002d002c0400c40b8152503901c1905c1002904650328030880b44610b1f04c0030003405140c0c50300c4042e9891449900000c0c0c3d00c00c1165403021400e0f51b41c88000304001c1030b001008658561542c0706202400740141d01160b0603400c0744804008002c7c01108503002c0c0140030800540049032880180c0b840f0001c164042c00c01454190642e0000395040c006041c140c06c248507580d5003999901d00f5a680e4450a25224000081c0c0b00c4402d0000d10070b500145410301307008158500f40754441010403040c0d00030760b10050300c000c081244904085040d038126500030742c40b1402491401e04040b400b525180040d00b009001e4010070300010b054a0141c0f425070041c040003030031303a20b140c105084848041c1d001020300351250b40c58000301094005040c03182000801c03002c1d0185051400d011000e843c2a580146242d00403580c1140c0c982c10400110014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 408041169 1250 408039919 408039923
    0x21020109050f0a0503011109040e07150810180204180507090b07061407180b092101090609080a020c0d05070512070807030c030b07080601080c0a050c06040507062a032a 74
    0x7076403905148c0c4108426901300050845103900f000f081803042c1104204c2c0d0380c1d421140c9007080030709501c070b1041101c00b601043d0304c1001451004003010b00d4080c1c07a0b0700100120303a5032a00303190056001c0c64559040320001e4940714041422503004000301d4114001401c1800d000b041c0014100c14910300c0000c000300704481250005861440304030a81100c400d5200107070820448890400760203102246410300844054000c5481c80b0b4801e842c1c0544c00d420101d80c09a1050090154801c40e1810310300c01d40000403411301500801816a0382c0c0c1c1800f8000b8050907811100510031145044241b04440d04040703090496400394007004602e207002081100021407107192044030711441e50038030402d03aa00180ca401e040080010901005a0b401081240c01401440c07030560b559800c0c0b8425140c501c691484128a0301461041009018021880c50101c1710651074540c4251940c010060441100c1c50070034610002075007004001c207216000b00d0000038100c84030724824001b14901c1140300801e400f41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 408042419 1250 408041169 408041201
    0x1707050a0c050324130c24030b2202090a0f0303080a060e070c11060c01060b07051009080d0209041116030e01020c01020d11121321020109050f0a050301 67
    0x400c1101d403e04000510404407007050021071220120b442c0070b02004090a91000303026245182424443d500c2090401416081310003c024822885e441d0908030260038600d0101749440e407006420b0401904c00c00e028500c042592207840c09104004009400224280350001001c600200d002090410914059802919050340502d0000c6400303003501c20036080442011001c4090000840d04110b8404030356a01c0440480000c030305034041140c0c0c1c0100c2c00c01410941c2402d50011300d4414083c02450b0f92801841661401c0c041c3c808441c3c190b400300396008001072010005421114a56800f40039402401000440d440009500c128441e400804210219101504c5000304140d001020701c40c14200a001070040d00f032840d00040c3d20344404204010501c8014034501060341e8043c41880d49100313085221a0300e034103501800904004050145410600002c038010390b069000d07044004a09505a4446034014105010300540c003020801c07150300440080c8000c02c0070b95082c020010074030701c0030300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 408043669 1250 408042419 408042443
    0x1104090603050f0f0102120403081807090207020f0a0506032403010f0515090f1303030b03060c070521090d061415010e060f0414030a210e1801031707050a 68
    0x3c40d460900c00d010855a2103a84100101031000c2155001640d206401d4184100b550f40c0b10164049a1203d04c00d01400e58080c000300400c81c20125409056440e00940f0071034981500c0e00c082c80f0850f06da60107074603440001800042c50b581100c90301007003105203401c1150002c0303c010011a080d54988003002d110720b510b600401552000d56050b0b04410401100c910026042026058406840c0604003250000c0440d559200381400394110708403010010b4100d5400d0701e0300307e4690398ae6400562080f10280504000103204000b80204400c5101003505100d11b40404035040102002409808851564030345051007204180403031341500c00e07402d102840b411217441c00001400c110340e040009225150a026512030490aa42a1010343d10484440c1c01001f0030f000000b03260185058005010ba00c8000b0034802e4041030340500120405503464402c00c07107211900f00200040100c8904059581c49030042002c00d180d0a501070700c68003100c41e802c0c03900d64152a5981020300b031a00c1580c0010b2044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 408044919 1250 408043669 408043693
    0x30a050706170108061513020724020909070e03210405040606180506070c080a140c01050711040e0a08070609060f33170618010c08070c05031201091509020a0909110409060305 77
    0x4071a04885032b000540071460013880100090b80000050140d5081004030b4820020355201040402800700d041c0f2003048010003141c80c5c80342c442d400303400380381d0103103062960010b01140220801c0303206c03a07400b061010040c0c1c21308091100d15000305030191580050184009100c0c0e1003030051248040c0205640c40343c0350b40203022145402c1c901c42e800350400030100401404030300010706003480d0a00c12100807400288000d038151600107402405025881c00240103020480d441d8881d1328a00e1017813030148801c18486032843d040359110000e0700e0524200e41d40915001900b60844800e800b114509415010b8440006420440e4641d940054584c440d1060006000020b104000110400300007403046c0d01050a00400b400d1028040300c1c1407005000c0140204a01031040c1c514450510352454610b40e51220480c024092000d003900c001e4044510105c2e141741c042c0200c0e0b030107a0300d40c7c42d150116882c20300510000c0c409040f84110751032040c0804144800b40b0300403840114095002450098586 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 408046169 1250 408044919 408044963
    0x1306060306020a2d02150a14070809160b09130f1a03070509060d08031803030a0902010815010519020307060207032714060c010209030a0507061701080615130207 71
    0x1131040701040003005192001035030340c00a0001c0c10301d9000c05003603202c0d0b201c6d000d008000e02034440d0010401d072511410052040d5110032032501c16903e00c2c00321070580a213110403000b0b070141401144211102007201b540703a410302004801810034905000a0450a10010071080341c5c00d12003134420184900c0d10340c195524081007400e010b08000c5555001900b0b002d80012114402d424006004e044d02100080440918041040c00248808150307640c070318013085c001008203441d100403804aa60740d07010410410415400815905040e1501490700c1c5440c08e41c00c550400e84d035909021031104001d80000034030a80054142c03244262504030440d5140314180c1c807048204210707a00ca4000c1001d040000d20b84604103201220020b58445030744102c8104858003a12441a500e07826102d50444201000310005000048030fa80d5540d10b003d280c00402c0040c403180081c0316000d155030100c1c0100d01181190030343c00208440007002d030070001c00b0b07528220050741c115900c15034006030000300c020b410f03080f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 408047419 1250 408046169 408046217
    0x50f01090f060807061809090b0f070c030815030705030312041106070312020f160507050a06020a05060a051f1d0604090302061306020c030c0a1205030108061306060306020a 76
    0x19080240015030a11502554504c1036216040800c04a00703004040705194545050240440a5040c0000c080906104001520541d854a0110b510b14002001c2c41d02c1180440314440c0c0c1982c2e100010740307a001170304030441c04080403e070703150144540028039554108010b03d044440704d04c9105181c6000e0621030f402035445c00e8864051701d01013014500003a88004a000400c0000d400103885581c0085201000c0c080c1e00f0901c0219180c104031402881030004941c0c080f52411900032000949404040b602d50300300100041041c2c0c040d402160321382016412082e40311885a612000060503038080c510501190345c80b400d000002c0642300d004050310300b03c080380e12060944003031203818980c0d5002540c0c1e000041070420806040c0ea900010007000b03804a501c000c40440442e6201c0005a41d859201c030714402e003c40c0d071126116455243c5074043c40549040303c5d04280603104542e43c40803102410030b031b40c94044ae1b07801c0c0c0e42d20b0080000307881403015100c031164968601600d007084c50304412800c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 408048669 1250 408047419 408047441
    0xc02060a0b1c0b04080d0c05090901090c0903060e0f0d0c0606050d0803010303031e0608030c0c12070506071703011d130803061005070605040f0b010e010803090105030c0c01050f0109 80
    0x400c9000090800307008401c0702c4400c1c1e1241000071039a03540d0620203d10b00450179054801030600b0800c2c00181c0c2d00c80701601045e201100c44040a9a03508c80100c11109460346500c0444e501d00420404601554400000310007410269010740401d42061400c0c1081d500108001c6505050010207100881c8228005000306036150004071140751160308a9000500c4024100758440c500700d030b10301955072072900008607110303400d10446445010194694004180c22042c0c3d1145001d50211482c1c02000c80301041005c1002e400c4c0c031401c24040c0b0030309038040303003040c1e600f0300c440c0140c0080ca0055800035402402001a809455616541500714100020304168980341281600c2e20109042c80201d0ba0003c0c400c0300d1014241090321819900303400f4045025100c1490030080006100d840441f0184151166004034004e030380702c400201031404280504102c50307206010000e550750040006641003440908880d0800002c08002800d490040703a001d1a200300f0000104014112401b03490800a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 408049919 1250 408048669 408048679
    0x1b091b0206090604021e1005041d0c090f1804050a03030e010509071401020c06030a0c020705060f041401090b030406060501032304020f3c040b0303090f03010f0c02060a0b 75
    0x104015400d6943c1d10700c06000a40300d140c80600c0c80c2c80c03e031541001c5500c40310000c1c1141020402089000c0c1c42a0041e100d80310301c05025901880300081c0540c45a032242546050060900d40c0d01824041e03429074006806801c066004008541003c01030035961007284500d0043c54405102c1c680201a0b440a00b61403010380e040c581803021403800402c4d81d10035500842172040440401c403004030300c1c1500480c00c0d1500050300100740200480d0a0b003207414405159000c0305c5a4507540d0040c040240305010410180c00c00c140400d0010401c5a16442d1801790145081c0c0d000301d4454109202c1503005a43c21921503031b40c1c000420095805d4081e50b10b00c0a951140d1079505000ca200e007514460004100a204409030b4061100581d1151289501c0c0800342c150f01c580d02c100b502006039003911031a12a20300d0068850303c6c01c403a14160013020119940a000b45003804040803c0c020b0701002140101d9065403245090a2048264480c40600d42e072154010072440c28902d6641003111000c10031b10f8011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 408051169 1250 408049919 408049921
    0x5240105090a090305041706011406070b0703020d20130b03011203110f010203090a0b1f151e020318060c0303070f03020d05010f0312090806070c1b091b0206 69
    0x3a80c500c000160b010802002c040f81651040c941212a48216009454503945103404010405000224035069514503070454111412071000c00c203650140d004d00500c02001c50000401140c0300c1c2e000b5082c99042e028020070490310058074a5a10080d0309040c0030942000300300c1144210407801001c00030081176840a10f1541443c2c2035010030384420b080681406241d40441b4407403041040051441150240219120700b840100961501d44c050310507030b000c080d80e80c00f052280e510094500b90005c6c501c140c0100c403d01d41080c103034641c22000340c410140101500480b984949284030541c8070b21003076020707513941d8020441e46004107500c10281d5000c0c0b0001d0112030010100041100d4021110341004130100b01102400c0b0080d00c102c100041c50541400c0001844589602c46002a41c1c4035507a1542020181d4204603040e05a51160104a0f8400004103130100d0240f43d19191860003042d100c0024600a1340342c6440c3d241e1075100800c0556a84101245e60341e4600c150086940c02c3d01c041c00031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 408052419 1250 408051169 408051179
    0x702060f01051e010509090c040501090b090d0618020904050d020f0309131e0903030203010302010305061002060f0709030b1003050d09080a2d060e0d02011103010b03070207080a052401 81
    0x402c2420486101c00401c1150003c0141e0190041e240c40300c04c02414001b05e8500301a02c482d440d001071091a01060070b4050100c3d41c0840300c1d0a0310b00c1e4010140c0074114034201503c844000e001032031007070504500c03c031103084003685078096410b21944c000c0703000b0803161a171400002d2908504a5050109400038000301a6643d600d00520b541001c440c0e402043c00011a12401021000b443da840c2210789407503420360030550140c004c0c2d4126030003601e003040142d840c8400d0115504900d0084030040c2c2040f030001c0d48000b0180320321508817400f81307000d2243c641c4030355805040c20410755101d8110219a01c040041020402983c3c00220715494408002444c100103076a41e2195408010000f010303080d403031282d040c402075070801d030003040c040e110794091107504080d00101017841141045000c0c400c0c03500807450050099071003410004142c01d1440e803a18041000c2074200bd0180b0046000d00c10000440401c200010044c081c0188050844040c40410280115400e08803080c1d062580c1001040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 408053669 1250 408052419 408052429
    0x9010908061e04060f050907031110051921050708070e0303070201030f11160c0614030f06010215130c0801020f0d05060a080a080c1006180b0406081e0708010e0303060d06110d02030702060f0105 85
    0x1500598206240d00d4043c88040c03e8400594400a1141e41c03033b103007440300f101075000b43c00c16401400b09032184102500c0b034401c00c030b80c4d03140d001401680541c02041180019480307035102440561040000095850400456100a0340003090207500d91250008010501c01c2000c0004020080380c18041c51903200d0003441521800011314040c0003420000005070765074000d0000c2a180c5a180b10a00400e25105400a140e41c100010560380b4100080d4045a4000140f0807690b40740400005182428040c40c400000f61500820490b00420070641c0068580400c10402c1006446a00e5890319683d442c0443c52405d082011400c180d113041c504100003d0303144090501240b840758401181c0c0d29604004217000d0720070380c0d100c42e0301071003001c16014462041a05000081008105440025135504661402c0e40c0b1480210031042d0010004524603190a03280b0703080040c41072802149078402c08040c0b0006d50000548801055000002c11802a50500519500440c0303161405000d50400b00420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 408054919 1250 408053669 408053677
    0xf040b0a06080c12010b12060406050901090c050d060308031b04030b0c0318060124030207020f06132d060305090a020603100b0304060209010908061e04060f05090703111005 76
    0xd024040b80001240a020300c4808590300c0f5042c4041c1558256910744441d017403640020000303942d160310040400d00c545064000c01c01100d0006010320050790910382d4003001441d404500f0400d02c4000c0261020904460041c20300450017124450f4482c031f03204070301c4038400f0346070301c1d040d020b50034100414400504400051500207801c00d912541b04c1d075585240d4813500105030043d0030341c0d2081c00c0001078581c1c6098030341d10044c5640c0b200d14150006c403000c25030a901581d00020f501100903944080141011409800a81d001c1e0b00c205039116500c20001c80700c444010284400061100740c05420002d00350000001004546400c0000b4078180c14207d4885840890003807058100001042d0360300207010342e50340035100844240c1e9490a051400f50000c1d44010110390210301c07800c07000202400003003a007520801c0452107200700f00d490710096000800d0f00410444040c0ea031041968514602803142c2c2d44070702da00900401d605801c0d818100f0422075402055403103213080f07415188416074031005403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 408056169 1250 408054919 408054929
    0x50a06170c0724151a0418060f06030b0901051c060b120f0f06090105010b040303030903211a040c05160c0e091c0206040f080304110402030a0603020f040b0a 69
    0x164450740d040c681049402800040c032525451190114110a04264402040e010f00c1c155131203c0c0c581e482e17154840c41500040130240b1524140010400c140c0884640c1002d00c0300c0c5400040d100340c4543d420600300b0b04a400400c000303035460300d80ea031450030040b20550146c40222100314507216040c0da00000c1001c0c54000800c0700307032110002540b41c4c40300007201c08801480d6044d14246a0381c441810303030b42c000b0440f061580f48240300114200300010711445059410120310903280c20b056880607401f82880354001c504000d0803200300c06840000070300d600741000341c412000c2442c07041c0e960800103490105802c01d2089290002c1220000c0e088011a03031a44052910600744070010b06010329841815403001030140840c10802c00f50080c0841e40c02281040038403415204a0480707812640c40f801224002d05d040120682503003c0341c0c01001541e4418800e000100000356450301180131390704141d583c80c80c3c81e43c8400091045140914100e4000d1000307a404021402d6124000788601802e8807034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 408057419 1250 408056169 408056191
    0x60b030c0a0c0b090a0b0c09100c08270103230112050a0203030a02030705160609062001110a090821070503070501020703120e0607020a0b0606040519050a0617 70
    0x2001601c0c601520508110981080030007421340340c503403511a1030391181c84040342e0154165000440c0390041c0b0064030604030008d40f200140b0800c007042540c03a00d4000304280d80ca13070000d100c95502d0400308031003542c0ca501e820403603042d0340c40080009025030740034030745003114a08450804002006007954442c1141c14402c0107101e2810707142812410b0501615019405000000c0c11041044d000401030031503074491811100b24a8102c22180c4640626000e00d000041218004001c8503202c0c0010000c10580f402d150011505070840503800c5a00310500040010f5002c07038001d0909070003070001d100402c031040203444401c605040c5040191608807070400f46d090b01144403030038824200b0507a0200c981c000000c40d40e856071030a003d80514843d001445030207080515098002c100803401d50301078000e075001002951860340d1041d440a2008141c0f0303030440c509110008155403510001c010224101c104442084e0400c0140f10b0b1284d80c030740148041c05500c1d04410440741e80340c050a0f5220800e500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 408058669 1250 408057419 408057427
    0x507061205090c011202131203080c1e03071e080103020108011a03060d050a0b07030608070906050f040e0c060a0809060c070f082209050609090105070e1c0501060806010612060b030c 80
    0x20020f001f01c080303d5011a5584e000486c4280d808032031010305c51b000b91504c40d5a40d5480c01500d001c0e116a61008001c8000080d400b030740b454602028540000d1603050079011005440010070031003c41201c82c400044191004100b55608185d804e405002c02c0b80403000c0c0380c110b545207500103220291105002ea40071851a00a00400b8495004215480803c0e0215400c04901c024050845406540028010000005080c50882c4240000c80d200904110002a514004c01004140d0301c1c1100c01c090182014200141d9142c5004099030241a01c419080c2c3c01c4c2000340c24a0000001d080c061061801c00c0044007140942d20380fa075400d0f900440150769680e0440c1c400c1c1801c068a500d500f01071324810008a0001c4a80d00305d64840d00d000c0d08c40f58282c4c2d81d0410014241c2d039060b02c040000c102e51020444481c104050f4a4031100c0b003a01003980140b00550340c4900b1110b0941c08107032150440360052110f5948080c01100c1c403050740809108090034801140c410303100c050f21440d0610000a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 408059919 1250 408058669 408058697
    0x60522080f0f0a120c0215070324090c120e1f0e0105040809090709060e0d081b030702120a230f0d020304140105190e06160507061205090c01 62
    0x180481d12404818078a041c2c90b0361281d6400707428200d801150382004c1d800c2444108140340b001860174000080c80000102c0350b00c031000c0c2a001042041c00c0c070080c02c030003000c5600181e54520801402442a000300042a050040004014039210901c40c10918209841c50b19500310004106e10b02e40c0c2070340c0102680f010702c2c0440784010404803114841075401d2804000c1070010504c0078201e001015907440d600340d036882000700c03007101681c010301d001b1400034240714402e0305080e160100c903144030b24041441c022030600c000e491050000086d114036400003584104604150400c1054154100010600b02081d541ca0b201982040703c21000b0500d040d00c0c2c040d40c0510100403401981e517608065074040c0c000d40800a489030301034042d180503840e071030f0240c07940c40d48590204c81480710761100400035440c07440b000f1100d40082d4125560320240a0048420786002c1030344c1a411140f0850040c403200d1324010b070280c405000a04450182e41c901030400050500114440c012120309184c03d1408ac9004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 408061169 1250 408059919 408059947
    0x2060a0c0c0e180309010906050a0e0402031510051206040903030617060a05160504030f110a09020a08012c18030f0c1e0304031205040504020d0906052208 68
    0x8403000d40405041c900010798030010401d03240c05010108190f404514030791004666a214200800d40010310803041044a18821005070a2101d0039290100c83c3e0807001000405a820548855030200b00e609001c86940c0307450040c8858602e50782c01c1c800e0030180800000348a09000801d540d024944071212441018842d80c09100580408242000030303002c40030207240e83c0e6904482078141c4d64904008030b941d0203405d01900304100c4580d80d45510701070456440c0c103003103280908101c485c2401d1500880c003541e01e4825060181071640300040c0c80343c0620b0030041030110107a2040c0049440c5004a80c2d03885424480348486103e0700c4d043c20596202c0c07a4000d00c15811030b105240c00f0740004241c0d91f14003030300710b8000c100907030044046501101105041e4030290b00c1e4124602c03034540c402c01081000880c103c030303a1680107034282000c070b05107550745001c02c0c142c0c0c0c8035840b0f000c6440c0c0d44414070000c10281d4070903280c000d02c2c08075140c1300400100c502120345000c400c2001c3c10160001c68030010000301 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 408062419 1250 408061169 408061187
    0x10e0604060e031308030901030507111207110402031f06030b01050909060a0314031b0628150b040302033c010213030b18030a090b07020d1202280f02060a 68
    0x1041313510000050b5125001500c80d080b9000c0c2d180000c1c2007402207010203116164808140d00c22002514031000c401c070300e01c0522b92011004032084020200071002a64440c409513119020040700440350b10b001e007000160022107a08902c0c245440c0c07800002d0306d0f0f64031000f0f446040905841c05085030b15400005451103c2985c401800311038440c042031050b50340800500007100c0c130400c502c440c40c0c01c1d804a00f902c0e107004841c0100b16882e4040c66007420141c060780c000c2405047c10002074100c24070490320b0f2215019800521003028001010400c5040800002d0310380401c03044800f9a031401c0d41072190301c050036240b1407907140d0780c4030041d404401000c0d03046500c0c941280e80000922a6a40303003259550314201e03065040803100e11500c800c007034404021140c2002140e075450348001d05010000303085820695040c0d81009003070040800080d1701e1414024184595001404452201020f0107070940211904c012344450301c00420001850544030307a0b500d154122091603e40703165501c2141c640350 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 408063669 1250 408062419 408062437
    0xc061b02040c180b09030f07180b18010f0303110309010909020d141f05011b0609080904091406220b3304050c0306101110020f0318010e0604060e03 65
    0x44030f080012040038403001881402c400340e00b518445032000e03011036103641d003a10605100d4064540410348142285d403040000c82c030028004800c400031112500042c5d075090304188840440300406006164000b5030040e40c64101c00700441c07802d8055000200500e000b8850441c4e045e8011440300301034185500300c0d00801036800808401407070b09661028100c1142d05200b800418007850106036944191081c10942c40450350205540c10a6601c2c0c0e80180062841903e07800704c140404030040c0d60b24040d61144a0186005502030100d0310811070800c0006041c800c0c2c010b40c1164600d0300c3e48018024881003a0300184441a0380d960300d40b0000040001011454000c201019802080040e5050f050707460038003500c0400c040d40d03a298022100707100a42d07080341c0c0090210360305201c40e481741c074182ca0301842da40b003aa0015002480c1750000da810503160b002c00802c010040022421700040360003220010040244500406039884503100c02001d0005840300b51683c081c0c440c0300c90104100d8075502 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 408064919 1250 408063669 408063707
    0x303092209061b05090a03170d09051c051c05100312080a0b0109031a0711010203010f061101020a051927031a0705180f0909030301030c061b02040c 65
    0x81d81e1801500030110000c0c803241410103403120b0b42e410351040c82540e544180107890290300b2400c6d03883d800c05100c54030130f0441c09003034100107080070801180610b0440034443d000a2071804903555186a20010b29070f9000d003000018070002c01e03c007884907140b00c1e00c1c214000d40007c5944584c91060b0745000d603030300060a8041d00c000802c0c2001e500c115120321030f640200d0200030a0131600011180c090f207502c409002002c00c0f030f944903000d4a030b100c41103070440c1182c00d02c92000d0b60484e45040c00e90704241d0005c8030f640440d0004100158120500b4446110a1002140381120040000c0c01c00d02685079001c040101946483c989140220b10214842501c0203002a04a0f00d01a1021456440740000c03280da406803440d804600c81d40c0d01c2d9160191246448290400301c50161000074546402d251680c8400030043e410700c1030b2500b40c0c62a0007288805c0103540d80350b0440c00c081000b5800ca5100d14100301030340c1661030141501c816184810b42e412030300460540c40d00c1a08039030200128407801005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 408066169 1250 408064919 408064931
    0x320280b1603090e0106020c0f030a06060305030c210304032601030c141e010819020706050711061311040e03120406181a0a0204080a0302030c01060f0503030922 71
    0xc426441c405030005109564107442d00b52610f048401c501028440c06001da4003100c030381c00c15441c0040c0920aa444054119144aa0241c0b03912050300c0d07080d40107607082d070000602002d80902c2401800506626040040304144070500501c0c3c2d6480000c2003e01008014007064280785450116403030040240d2070512442d513128249407080c004984501d200e810801c00038181c0c2810841d03464507550381d1098a90000000d400015101400700405500402c49840c401400106540c409002e034140100400101c07481d08150245c511050803c1901c10741e40900100058000345580e50049075034044106034035210002c010801238419030211280030b0001003901c840c130307405030151075110b1805080c046c800542e10100e190300e0203806800280010b1460255154084240e0261580049a940c0018903050b680d501c1306041c1130b4804811001a040080c541116520034003a0002512440500c3d40b80c043c0f60100103590f034070914044da03000b40360b9840c500c480180f00051001240070903507024425 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 408067419 1250 408066169 408066187
    0x21030118140f0907240e031c020c1005121b160b15060f040b030c040b07030c031805060a0804060b030607051201080705030c010507050a0503070c0320280b 68
    0x1103901d0072070303440506114042000900290401c0b4030303940171590801040c000118014210342507403065070340c1ca4141c411810742119504c100c0c0381034007139511180d003d407007001c041c44c0810404168520940c020040144940500c200100d07038119048840c40545070004010002031601c203000b000b01401844107031901c070710b0500600d4000f4034440c0c210706011100e11541501000340f00d011b1100f88201c001c109020610005c0b41410003075030000f00002d806428184c0c0c0f010741d211540d20a1800b02c000500d44c0081c2d5040540045c0038078442007038260121340260509000c58810302802030003100300107425003c2418052039900c01549080060152001071800c0080036080b135110800f495448607042c000081d101030081242c909a0345d0040103080342c01c604200455544e0070051040c1c1d503d000305a884000103c00700001c003001489031205c1d0310b26a29504004406021510740c50841c0c5807034070740c80c0c0343e01e0f614504c00a0030001411045c8442d89181d00d2102d030803840075000707501c100720700140901c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 408068669 1250 408067419 408067441
    0x1201120305120a060f030c171b0d02030a02100f02061810020702191413020309120f0409050106120608060f0c0f0c060109020304020405012412020f0d0c022103011814 73
    0x944420032446403400038000030785992101800301c1d27002440307035940e100c025503e05106071951140c0001c2c01c840301c820042e00007650b21917551a0810104503005d200128003901800a0f550001c911709141da0001402881d8580f41c0d804024086480d035400100c4108640d102218000043c011510905060362240304041c20a00e8548113a40f20358500310120200c3c01c0d290086a22807050322000c1c0c001113441c1c01303007a23005030000c40c0c00440e00c0300240800702d200c2c0800d1144500901da10340d140c8a070010300c0f6040b1130443d4130070b8001452642101042110320440d5050103600308a00c00a025981c1c0010044e1805a0003a00b802031114017400000084144041c1c02540c01580200d504000990780e1368201102800002c2d02070f01e07070100d011640000740703000304516031454507002d4000d03103440c038080d00321000c507488003c8140441d42c2e1307842d0750304120303904001440c1c5c500490b0048182c0129214803851407400140b02c0c2c0d40043c81da021225840002c15000003040350424030a01d4400e04107048111 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 408069919 1250 408068669 408068693
    0x40f0207060b0a0506210405010207050312040c0e0103080a140c100b0411030105010807030e01140c0309010507050406022d03042c0f06040e071a1201120305120a060f03 74
    0x140300f0705541d034001c41c0602c0d011081701c0f40a0460000b00003012003e0000c2101001c004005944c0c8e95402c0c0b00e4080030850900041058000c0d410308002c2d01d00d0149880910356001c3e400c920221000c0c0702c01400003c4a003021120034030300740d0410500040c54600510294483c080138182107000320b072169030611015030000c0070090400c66051114182155035445203000900c038050000e0500070110382501c0c000d511500704541c2c0c000002c64001c04000b1254640207090b00c4000c41080000200214500d00384941500301c041c1e4a42030b40b0b89860414002c0d42d5003550032004052041c50750700e100004800404004110b40c8980690740c0b02d90350b5400c01d4044202040c910b9480c0310745141c003650096440c047d403d104001c50390b00c5107450744608081c000182a140b00d4024603100d0801c000c100c001c600103000512504250141d941c2d248246030815840ea0180d0000000c1c035041450400000e030024169403080d00c0c0502d180e445030791f41e440d00c84007410040d8441e0b000440302a02c04000e002d078441c804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 408071169 1250 408069919 408069941
    0xc240e031f1512080307120e0102070308040b1f140a080106080102090102070b040501080708040615081b0d0503070f05160b120f04020f060c01022118070806070806040f020706 77
    0x303011083c1d59106104151001d86100802c00c900030400190750718050f6880d205106551000018044201420303142264412542900406c9100c000c2004000e800001e45900c50303004d82c128007408806070500740352180d040c0241005c1c04904008034143c0d407540c1c1c103c03030f006090070402440035590301d8040c07500030f6201900303060050148000c00320701614900102e03412202e042c1e48058690356000411528a10058402c6600a4462048010303903a220800c05024041e02c82c090071030f48003100d6441c1100c54074110008d004140342d110100100300040280c1d02015001500a00f808005192050508402d00c075250f0750a2441f150105840b03012902a1420360708900217118a41c0707a00e070700c0f40c070090001c460003540075141914014640c24842d01034141302c0900303800542040100e0308110202c030821005100a510b11104100c40505101d200c079000102d02ca001d03000d0b03507082085c400d495400040441080c0801c14000c1109910b5aa106013808142c1d0f683c2152140910314000c0d000c2c111043d60 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 408072419 1250 408071169 408071201
    0x50307060809060a020703260f0a060e0f06030a12020c031204240509030a03050309120705030a180512030703021006060e040f0204050a0803070c240e031f 68
    0xc10000d02900109001d11606001401c0c1651940080d90203035105101c110100f00030300340303203e688450415182058025080c1ea4502c02d140c01c0d400481c20401c001c0040a802d030070300303c0400c20700104008458112200d100742e0042a80c690f000320707180c4009914020449081d2000650429501043e014494882181130b0380049005110281182c012805a200048290310b401d0603400d684840200e03800615042c50780c2802010310000e810003050a44c01d1b80460f00001c1000700503001070000d5411080e0207041c0e14240061394032800c1d0340303000b4445a107083c000d2240c07126807580e0303804120348002d00004240e45801024030003d00e440b60032681d070450143c895007003000d080188500566003503c0c080d03510010844691404c1102505600d240302c00090741c2000089400e4032040c9001001c2d2541c100210380d17030380040c94010407032203040d8010100340d003060748407088087d40030600343c414a01d10701d8503058100c0c0400000e410484c09220340d01020a8080d041c1e40c0f030403280d070051a04840500c103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 408073669 1250 408072419 408072433
    0x5030313090b011d01121b02010911030a08040308030a0207080a110d08160c1b08070303021005221a090706020706112d030a0c020a1707030803060d0c0306060503 71
    0x20064aa910f60840b1101a038a000680b00344c2c036501c07448a892003101d4400c80807807540755020512004080d0680d5003401070751160701143c2400a00102892083c030241e000781014012500e5090307081c0110300004020460000100e034002c00c16406640540781c000500076070302d603a035400c043e0065000a0440c4018052140600483c034010302c4098460041c8410803100303514988e030112003000c131180c1c0403115078208100c00b500c01207140c241c1c0000740411030014150b13142103040191408540c03521000840e8280ba00304086083c2080d20001d42004c1e041034061000000e00d080446070206161119032042c01e80b00f0441d8200000800361700320382c0030ba000e41e03056035110b440880c1c201e400071100c40c40e5a80a036030031030503401032071400b03084000e108000002d2106d60400d08070f007143c1c00350380c1c0c0f600062115030300f080541c940904007200411342c1645d082219040290f134a0344135404c42c800a172030350704080000b03084c40c0c40d01a0703915120350b4002e04480f0740da034407480c00b20001c1c03200b0300856010f485402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 408074919 1250 408073669 408073691
    0x608031809090c01031104080105010f0816080c01201006032006090d051203070906030f06150e0f190305100c1205040c09050705030a1113030f06060503031309 70
    0x6840d406202ca02c4081d0503103010440054014010310906000394820070400011080800c0c4140c0340a407a0400742c217811103142c200b100d45440301ca04040c5903607454038201040f00c0d180000d480d00250344c00307080590080003d001401015001030000c540c2a009440c1495a88905940050140c070700c100000207400d03401901c40c4599840c80f2200a80180c1c0c01c003e40e40d070a02e042c0701000c0c090344c401c1d0101c480c960402074511460343c00035118400401c03940074050001c1c03509802803d50310032610b00104100c51510310f03010180405043c946060004002201c0340640398944408510040130304030300500f22421030000076108261100340d8050050440803907114005004884011303000c0e0b540c000c1014141042d50008140151040b9a450510700780011403604170300500340705140c0e40d101c040d246d281114108042c0d41d0059640c01c400c0c0e0703082041e09044031400c0001002d07240c000c0d00c4800200c1503031420a0051905170042a498400401c1c10302491030302000c00d1065402c03a2505004c550b00e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 408076169 1250 408074919 408074929
    0xd0f230a020708071a03040203161205190c060f0e03161a030c1c0b0306040803040228140f03030d091211060a0207050331050904110609120106080318 66
    0x901451083d01c035a025940c10750302c5d00780003035a0440d000900b61000c0842140c21074030341e40069409810329185c409001400e002052180040d11002e6400c002c00c0d41d10300d580d80000180481c007a241c180030002000c00f0700c840c410007d0482e450700160840c0c85000c14030321960362028280c0703c0c0000c1c007003440301407030304090080301501c1c019800700c440282800092505005d442500d07009121540c2e588804422050703504200440c061409040015540d00f014014408480450041a14401104203a920750040c000410500700e0741c070a07411b038003550300c50300000d10081e01d12140390798144000301c0c0c046040d16040c2d1110005c503101381300c10740c02c0404c41071098501c521042c1503502c50750040800200c030444a50024002e171442401600c0c0392072241c5404a002009441c0400040031605410001c0d600a486042c1c0c05000100e8250071540743ca51340720b038000b0001c20b1a10b4061000401c81d0710369a1a4040c00c0f01b000a07000c402070008a0f220080d450340d80e0041114154007920318225040c4038107003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 408077419 1250 408076169 408076183
    0x30f0b19150302090303070f1406010306020d0c0804030e0618030f2b0e100903021207060e01111e03070b040b07030506060a12090c0b0403050106080606030f0d0f230a020708 76
    0xe40903504100707041e00c90308c1c0401d80024042e140d0880750382104049002c00d228050285226990060310785010310340c940110f03810980d401040c40132100601010070f80000d114002c8400403a8210307a10b0001590751b02489000c46640d58241c801c80c04e11058012011500000307082800701e60070f44c00c032001d1507070400c003244840901d404030b03504803d8580d090910f84459144400319041400c51941c4d01e074042105152840386a078000c2e0007955041c06090f6209030811103800e000d207400140e66005031170b4940c440504d0a000c0309070100000d086680c40000384181d501040e00400064914034242c10310520f0040300b1030f540c80c000380c0791400017503d42c64003809a82e6180b240f40d80d01c2d04081c000c0101d450040c11000f5040e20303030400043e80014003800000040020314499400032a880340303003130340d028a42038000c0c00c01d0b80b003a040140d10300110783c1c0004d558044210346241243c1980c0540700c00b5165000380e8001056200d40b1000c10f0303950000c00c1801404500b0540e401c44491603a03510080345c41d060303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 408078669 1250 408077419 408077437
    0x70203062d0405120301080a060c090609170c0316061b0c171c03060f0e0f060904030c080310030b0f07021b22140115020a03030f0b19150302 62
    0x20701011a840c4030011950810b91141c4910b0440c3c0c2114407200ca40d1265400907030200c001c0c2d41c00a9210301c20400302e400707448244252410040701030b50502d080a05030b4106800b070041485030b017440010b04880100489580d05401a0548400004501441b001180c50b401200003003141c1c910700b14080b0b0300c540507411030582c000850100359824410f4080520030040303429510b41c417810760380d1802c501691407010807a405a450008650703281c001680524019580a200c508415074100880044200b040941c0294111989403540c2d0721890143c42c2200841009400e0840102c1080741d003074109101c0205580c0206107090445d9543d04580d007c50804445c030b0030050b0040e4007c0000d40e494440071018940e001031103d0140d405910521000000c900d000b0b240c406d4440c001c141648404e042214003404001182c4c011203608104040c1da100040e0000904240d5505e060901546182c1e0094004d01d200410111140c07403080c02003003088250b80a11042180c0204e00465001d00900c03c9824800d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 408079919 1250 408078669 408078721
    0xa080d080a0b041b030618050402030c060304021302030f061f17090a060f0b09070c051f0b1f020c03012a0c1718040209240d020a0507020306 62
    0x2540d01d1005a000e8654a030280e508651550301c000300046000920071444101c41e540029810b140c8075034296004030000480045500d0b000500c80542c801146000031380c04280c510503a60384451011481e03c41c06401100b20301031011041c04440049035400074040c90086840041101540000a20351201e0700c1211000c521141c0254135412240164070368002010002d544801c03045031a000203030340106800e2440f241d500e1000c5101860400d6903a60050400d20741002e10103816510641d80f030003190644036224403003152254041c1829048020303500405892081c0118040d43e183e60300c8400045c50708058010000340310904c0c21b05101d1005241111006911300c8480c40c841c0c000020420790140301009560042c0401154000000b006200310054040d5951010324404650b14880032100c94412030041004042c0c640d59182c0d40300442c401800c0001002803101c1140016100d500d218900c2140041540080c031600000a045a580240c0c1a2520342d03851500600c906034540040011030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 408081169 1250 408079919 408079921
    0x705030a0b03010f020721080115230705010e0601360906020c150606030103080f0a0e0a140a0503151f050d080c0f2a0a050604030c03020a080d08 64
    0x10405908481c803089005400050416404003e101c10f82c0c0c4920820f80f403020b030404081c142d1030207007103081c03000b0141031500c2d10055040070356031100420318008010801c1807003100380710411405d480d030b0178000b4030011a440c0d6440807450941d0107040a114082c0e42c9000707520001440704410850080782c0500b45134121402c00d000710212a64943c0003000d261065035605607140010038610081044511160052a100000303603020340751114010701543c040c82051004000150020701940c40c100b02e41c0d50b0013038a49100280480b0038a4403c401d19600668010002490b0341c075044031400c3c2e000003500c126000c0360701d5000340350352200c0d043c01908011714014001000428102800064103d080d108201c2d2582c0c2c400c00030300f075a030a0403800d66460078000340c02809040c007084607516042c0c01601a020540108550010400c1980c6503403261a01c42c94a428450b698420180d010300002080241c9a54590a1000300d0065a00040303009802607035010500320320010b4104007042d026615038210b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 408082419 1250 408081169 408081181
    0x3040504020a020a0c030f0507060212270915041802060304060c09030c08061503060f01030b0a0f020c030309011410360b0108060103060513240306060305070b03070503 74
    0x294404a001403c6020300c2c21540c0001e000b20540000450141003074111002e614281503007488040e0380154155806049104005903a04054a400b00c2840354484c01186190031030956407209141e1080c0e02220319810402d07410f03500c0b070280841c10002d6500304000b100b4600f40c95a00701200201031741c0701c0c0d010b000040020301180c114000b61555071800c880c03116529a00c0b2007199002e900841c0c1990004020040b00c0300c0401d204200c0c008040740104018101001d010307030401018000603141d080c540e0f002903640e4441d40c0080c040f806802d0400c5549440f5092a107450b03800581c0e03e50029400c008940440c00c403403106840c0500c1e003200744103446620313060000c0380c041c211f500c0002c0360100c1c45a80308400c0003401c2803000c90304a4940049040d10403000010300c444c3e001082c40e810b0510f0180705000726100c180300310700d5000c2c03c84000945540d980300c501d150100a44d40a00c08050007080210800801d41c00903411070748a041220704803601c0b00f0702c1103030780c0c08110b45200015000340f0000303070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 408083669 1250 408082419 408082421
    0x30513020a0b16020a090609180f021201020c250603060f0e04020102151f1a040302010507050a0507062102030f0606070f080f13090216021e030316030f0c020303040504 74
    0x11620801090f201d840031907000c641300000700c1e48808482ca41e2030504000d504800d001d03503541d0802c2d03142c081950104a81c2e0320048c80c0c0c0c4520f03010b030107800440300c0440414425811035a2101c02c3c2c87c200c808800512100b10059100c801c40c56082c803200340ca0001e11140240a0501510f441a08075425981403144ca45801d2100a2044e0704620451441c9814100d80c1c034211401442103410a84114221910300c06d405080c0740e00a44d58420507061360600689142c080d50103803035092802c2a0382d098282007081c41c100254a02410a00840400043e034682014007940c607050100420440440d100c0d04c010100d01044421034410010040041c3d41440c2040041488074415003040d0860000741d10342201c6e81d0002c80d06a014442c000404031450000744034828020401243c05515150012000808251001100034003034091680062040000030ba10901905000303011661100000390701c10141009820095005c11040304100c1103192050220130440ca030050015464030f854071013404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 408084919 1250 408083669 408083677
    0x1f050609060a1d0d03030b030c150d0b1504060c0b070c050715050c100606140304020310020304020d0b2409060d080a050d022106030a0f02040207080c010c0807030513020a0b 76
    0x1049403680c220540c00c83d0b98910448591150099900007008030b0143d0526140c8000d02c41e22500c212802e022903a01c40b100c0d0f0040f01d0318590f8018001c42ca4030360420100c3c8070b550034485981032000c80420301084440c0d01c0308540303055038010302e0200c1130307500d42840030745100c120b00702c01504a4100540c1441390520b2034144844ca03080741e2901c54501503051498509044599500550031034841c203040006e142d0111140741c059a0507202031f8610b081c00d50000e5503440340030303c1c91070b442500407000805540e60f0f0090582100c0e000080b03200a4604642881c007501a8020302e94203007800001481600d090003400644a10406018000348000b6925146a43d8005102c1d0201700300081042c40581c18007170024148041207c40c00b01c0c045070f00c01c00001200d038001040a4081d0b403041c00088042240c840c11040515016200113943ea452400c0040c824866814043e4166090142c00c44405038083c803030138801c00890380e0400103600c07800214600e070520b10401a5210002803c1800b500310800010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 408086169 1250 408084919 408084947
    0x12090c091b05040e0f130203010203100602240a0509010b0907090501031107080a0810050312040306060b1c150e13060b0405070203090f0d0b090604050601050604050a120c030b1f050609060a 83
    0x80d00e06d001260340061700ba84d00c2180d0320401816004410404d048d0100716100c00d00c4440030401400190080208ac00288000c1803001d1080d195008128120002e44c001c2496580140c0220b010b4604001301030501c0c3d24031300c40c0e213001929101101d8000080e8038242c1d800d00e40c0c400e00251420a285c00100d41151000d00781c0e00c00002420b40000d02503408020310081148030b100c03000d0b2918039500700401200c400d5441000c01c00000c00c8558515050b20000310324a4041d80c8002550b03050000440c908800c0540020240f82440018890840b42c44080061075600c100024086c6c03080b41c0c0300740420f5580507611580980d00500c201012403038410071042a020700640300c4012110f158442c00e45101081c1e134440c1040d04904188010302c4014441c142c05407400f5185645041d1074000800c42d4000588a54129a01c00480700002c00c1400703518600103681140440e1070a00700800710002d020032030a81e03100f00502102c400201420a00140c41107481c005200c0f50800c10401c40548502c4032001d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 408087419 1250 408086169 408086191
    0x906180b070321060603050901060e0f0405010f29100509061e0d0e061e0c0f0c0f010222050604030b04020114070302150c03040f0312090c091b05040e0f 67
    0xe06210081e0031526105190f0500341c00304281749451400f6080303d4000e040c03c8210f0341000c0081c01806da41400301500b00c2c090800c108000c1c0d031103040c9140100290700c003006815050988610042101504241120951007100c0c255503810204000300031340d05c004464041a0b0a11100d10396190000151644950b044d420a007079030311030b81c0040d20b154422112611aa80e49541447c02c0c8503042204c0c8c0c0d4000940894494840070118841c02004001800780001681c001009900e0300c48c00c005407140c5180c080211000e080050814074040d401580a40014100c4680c1046c01804100e4601d011600090000c1c0d152a0450312084850300e00100700b0b074140302001840351007103d554401407403028041ea0140800c00b6644414034112074000d07017070144001d400d00c10b1002040349045020010359050078200582c8180c056a20041c1c06640c001401c21405000001028002a0000e20350820000258040030350154000d5407903014502400b90b640070140300141c4001d40e040c005981110810308 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 408088669 1250 408087419 408087437
    0x910050105090a0f0b120105060c0304150c050f06060103230c070203070503030a1e050301150f180602010204080f0703030909020901020c0603011503061a0904090c050a0b0a0906180b0703 82
    0x200383c94002030b130b980070300c840020000d1203e07205040c28100a0150000300d41d05890104a000059903d01450240c007402082541c9405c102c5405400e8105541d58845d064450ba00c40c15041161646000c4078414080703810b02004003170070300c5481d40c407000c4040921070101d120307100c03c0c1003c902a00003100407a018480c0140c00b28540c1c0d02000904440801070340c8038032103480891001c9080240100c00b10082c0a4280014401d161180170340c40070018040c9080c00703031a01d180c1000c4490321811000c12104d2442802e01080c29031b410340061082ea00114204d03001c81486c0090156500006e20019000074841601070090350400e4004080046052040b9268002007200140b920f90007a80400340c0c0c5034483c1c40381c403402d9406015203c010314209010094030443d00140711224840c1c0741e0702600c03e80c2d0754075500c070402c496a85064080c09000d418400702c9030321501d00c0409a4082c482c2000801d0754500005604c41c4200599a000300d2800e215000041c0750941403060b54122030001c4041c0481e1032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 408089919 1250 408088669 408088679
    0xf11120c011119090e010e19061a13080703050d05030a06051e01122d06080102030a0c140304050a031202070203010c03061e050904031b0f03020703110910050105090a 73
    0x3504001000018286820384040070150550480303500c844c1340c05c20003900400000c451034501690068605000450a419090241c0e0080003940c20000d0480890004030000f1020301015100318000d0302002d4426a0711241401e42d224001d2000501c243c2c4a0750030010141d1040c00a181c000c1111000480c21503140c0740058408500302400903540c0101581c055055a0300551002040101c540200f0441c1d201031840075440501e02c1c28001d101d10309122090320342140398801030092402e14000c40d00c0f801c00350340c445c01420203034840a0019a1014106031411780890450340105d50142c002c0c0055246558150340e81c5213104000c18607158240b00ca80c0260f10f003805610305080b0a41d9002460500308000d0b00d404030b101c044040c01000c0d502c5401e00507900c03402151908140c02d030501d00d500c1d0882c030080d5a000200304100400c0c5912500081c002c241d00059603c2c10b49100d1580d80c0c60100c4440e040c004034035401c4509580c0300d80383c468108010350151000304401030001d0004001c8a490b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 408091169 1250 408089919 408089951
    0x603080307051621141305120c0a12121b06180f0501150b0a020a060e03070c031a0601030c1e090b0a02030d0b1503010e0a1d0d0f11120c01 61
    0xf008213404407503503205000301c0c255008011042c20140402040d0500318140d0800b000c15a003400340a00414180f00300e40320300e580800a0003a400001081d500206466603550070500c5801c080c101c030503101c9440d404103041d0190305140f801e02e05104001e121403504c1d4540e60050105405c10259003500d600303c070701c04551041d070f03035089a6024a002240c0b00469080b160280c0b515980201084002070090300100781c0d02040c0c0410160300010080707822807400800e42e00710703c40c02000510000842400208220040d48000c200e0405006408420743e540e000540c1952004054040066045078285140304450a551084810546400700c0c1c0f09445102841065000d0120300000d030b80041900c0c907101d215400740c840a0b8005643e040e0310749900072204885404180908080e0014000008448640c0c580c0090f10325440d0002c0078205607603a080341500d0f20a1f1060000002d0500000c1d14a854080c1000350340040d08400103044210341401c0d14511038020748140c816035522031004800304419 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 408092419 1250 408091169 408091193
    0x61b0d110a080105031908070c080304060c0b0603030f03040605040512031009050c07021525080703020c120c0f01030b040204090605010906080403140a17040804060e0406030803070516 81
    0x150030440e035458022070700182c4141030581c460362007a4441188a011004900340780480315a00c90717203141e101c0403145095405003d0a4121401c14030002c6000100d403544288074040306070140c5081ca50648036181419140e00c51807400014078001000843d00148690340055801809081039540c00f400043c1440c0c000d80c410b076118103010f851050240540c2e10300b40308142c2c02c0200f01c4400380c42c189413540172800c003000e040396204070311401055005200342442120300d41c50b41220101c058540c02d916024020742c1000000758010b02c10407440030740303900300009041840c03180305000b400394004500c10401d10000c013075051810035450726950203031a241c0e40007600180220090105050341490001090114142c1c042803c01504c5414080030035049150280701c0c002c0191032a56550f18250161165040d9002e50040c0c500e01070108024020720f00d01803c2550780303980d030f04c10030807010104000903a1098000500184420000314a080780100300801142d881d034a41880046600d807151142e03209 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 408093525 1106 408092419 408092441
    0x603051b0903071502060a05060f0a0311040f0f050a0c05070c1a0c150910020408030d18170301031b0311010f110d09030c050f0102061b0d 61
    0x1030500c402c01c0a804a40c1c8102009281d44c0c0b00256908400c441c00f0103518900741c0454164504451100001c803c0186004900d9041d034458100e00c00201d5030f01e0354803d0391201d640c4140710150042e050b06840c1440d00140c180380545070a0240d80e0395240550411104000c8180016140218a010342e00d0380030b07001901e19403900d030101403880313401540c11451050300d02c4a180840c240c8805481526000c00391070303240c0d2072400d00c030050b40101e0049040030303007040c0149080180030707a10900c481d103a00e2a900d002a00103448800195507400550311712210004014000e101c0c90400d0512107031004806c160750a842c0d44c8465403011031031803210b4100024800403030b880718800c5180f503001c1420070301a0f982c102d1400c1070240c1052000e100c12189610314243c00551032a200c1c00f221182041030300641069614900c95000b881031443c06180081014825990220154800d1b001280 = true := by decide +kernel

theorem cover : BRFrame.Cov 407913669 408093525 := by
  have h0 := BRFrame.cov_init 407913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 407913669 ≤ n) (h2 : n < 408093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
