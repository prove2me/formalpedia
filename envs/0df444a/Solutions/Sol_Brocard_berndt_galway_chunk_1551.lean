-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1551
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:32:20.438921+00:00
-- url     : https://prove2.me/submissions/0e19e2d1-14bb-41e8-9928-9d96ef5d2af9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 278776978 ≤ n < 278956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 278778228 1250 278776978 278777071
    0x50903181c0602030c090405060f0d121206090204140907050f09030a020301050106030912030506030703060f140a0f0c1d120f0a0503300406050c0405060403050a020117 74
    0x3121401c0381e01c05c640e0060249030125800f002401c1901c1116401641603038504080166000001c0b18580c081c2d800400c2d0521601d084003110b44980c48201584041a0083c0b052030b407038a0401000e9000f030b00035a0100502c0b140e01129500e8560b2149014040315207c840ca04003005503440c00b2a40710f440000e425200c0d074080303000140c0702486154001c002c0356030f00040080181c6030a450007079142540311f040604003010b001040c2c2e004203500080f40d500c25000181c0e200780f50301ca00c002e0404102c2e4102403500308801c004c1fa00070990042100542001c0b010450803460705c0c400d481154104030611915503051644503100c0c00e000c85201401c2000c00c046070052001c000c14185415805801100d10341c20124de910b800032081081c0a0f29010700030500100e03410039040c4c0300c042002c010800780607941c840340442c00b9218101c00320350107048050000b030382c3e4640b01e040059490494079400c90000b040c50840c0341c801800315959502170800c000036100c075410a03800c9050901000e08140b420f1045030704 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 278779478 1250 278778228 278778233
    0x16080718090f061a0a05070204090f0f1407180908190c0203060f010e07031a0d1b0f03020a060f02010f0207150b04020c0c01140412030203040801050903181c 69
    0xd06440080101c5480440c421140802e0300c000d60b00c1c20350001e004119800210001804202d003a1240b1000740e140060300c410441c000640a05980070003c1c100100c40d888640134004682c0c1c0f0a40307490b0151810f560b00c021030310b010980d1848148542d80c00e01c18482c1c0700034104007441e002602000e024442c400c0c14082c4146247c82001019180c2e034000c00c4801c1405811800d043c0030866120b41d028507201055807400481c1160810018401020582c1e980f50254100c00942446444180d0140030303100e601c4460700c1c203801c1c40300840e280180c20600f40c5d07200181d00300611003403000360f907130203050b100580745000d405644400d0304184002c199500d50264103004080c51001d01862401550310000c182d004000e01001c441401000e50301079401001f82002501c000500e075114600c0a2030080c2c941310a4116100c094010be40059520114222101050603400000f60003170f00d218100800843d141d121085603a1701c5040040340b40d9484803118441145040e40e1000b240d0300c003c00d0390803000010740d03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 278780728 1250 278779478 278779517
    0xe06061207090609060c02060306120a080f09030c0409020f0105130503010f091a04020a210b070201050403090b030403080403030b01021e2a0604030807021206090a140105160807 78
    0x4503503000018114202c02c001e56076000384010018846410885290751168010820520005001c1ca018001c1501c60b00c01072141000420303142900444002d03160f14102e06180301c2c0d54810b0243c14424072400ca01442c43d841c2c14400c85800b280c0c020aa50403884480b8019660360700904070702040048451000203091f107080c040c490030101c0301c11001545a0351454142103003100c409000348070318a4a4100401611b03510408002e070740030326070500d440030446a40001e40c1d480408c0c00502a62560062240658054201302c0c00742d031203600c0b501038081d102d080344887c87c0422034000e000071700f83c03c0202e00840c0c000e910070b103144401841602c503070281e640342401401f41d030b1029128540e40603202001454001181040200d0283d03100103c2180030100090000d01071800f015011500c00200601103684100341840656070740740a6035054a401a00c040d01c41c2103481c8140c03a0708018429a0441d12010300c90948104c034071851480c100b0b0000750080b00e002d10000d01c3d1400740603541d5462040c07110310 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 278781978 1250 278780728 278780731
    0x2030412080702090a0e06060609040b1309021507112103070b07080703090201051b01060e0c0717030601080714130305010204090e0304050a0e04021302270a06090e060612 75
    0x352400560710350140c4148003041400500030140641b030b010070519400400702e956a000942140c40917140c142500014004087c88110168003010b801507140310310900f80c00c03c0d0456070088034451040341252441e10414030803041c0040510015030507400540c0740100319a03020001c10b1460345c00c451041400c091555000c04400c0c0d071034604a90030081015849882c05910021914080c0603030308059002922a000c1c10139200c0d41601442c01040344a0025404a0000d25400c1c09441c09410650708041203035104a506030f41101d00726045010811441080324000c5d501a965072007240d4a007282180c040e1500c041104039070b08204403482289174007245050165000c2c030001a5100d2414240300112410032400915a4209100401c0b59a07142906c4000710b03000f40c1204400d940e20b80c8001f568035400400800082e500c04205000d840606030900000072408a8100c0c48102503002000513820403449400001209041c081c80b0024510400d16004403000d07203842d040c120100198550f5210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 278783228 1250 278781978 278781983
    0xc0111191e110a0f0b120c0c07030c0e09010507080609090a050303150a12030f2d03050402210601050105070809060a0e0312070b0106031107020301060b0a1106091c02030412 76
    0x1104182c040ea0380341100d8140002c10544003a20710043c604096107442d80220660300442800100c0002e8007000d030340080310289030313880302921802601d9213021041c0c00068029203003030707120110002c0c40282c0b052150a00804440e1aa1081541d400041141c001030091000f055070151282000000d4030400185000e211000c40041d190904001480300d03c2c0040c1d48413042c0b02c0800d103180c102090b0451040c0300000c1c1103150451403841c2c40e0b03010480400d00b8450b60b441040200a000724030070b6040e0b00440c0034503c202d81d100c40d0185181401090501070003d080719903040751004010039070040c8010042d4522684440341440d00c120005640d42d00310903440b0021607811a4480b1292074140000850044480c080c1820110542c03980321003140140a010103069845c25031408500daa9015641140d41c000c009004071511100300729a9504010708100c0032034020040c18180d05004221603104400d1480140182101005c040d903090780e010001b50f0540c0400c100200b6824001011301d40c1050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 278784478 1250 278783228 278783243
    0x1202010c0f06021b030306090c090109030510020a03060b0a2c040216020a0e04030f2115090b0d030203030c0d02070b0c0403120309050d080601030204260c0111191e 72
    0x1007004d500c2020103d0050811858100700104076150f500c000115802149071466240c50b000e42da40180d801141c0c580000d0400d1240406480180e01903400600b645c1403640c0c0c0c00d10400c1d03178409440c541400323886070703000200c0d104442d60101c80c848103101102c03d4084000d20ba03a01c5034074401040c2240c0c4000c40015a01404c1102e8030705601b40700003031100030827601000c0e0849190a443c010400b5080d4a61081040b2107144411a0b0884440e41c1e0650001e6164041045c072204001e107038181c900505c5a00c811f07038100101581c45141c1009005101e90301500510315658038040c5d501d20991100d20041c10300c036403d000000110f111514500e2003031104204180d0f07502c1c19400d0402c1041c0315825074804141c18041b100300090b1020800c0c590010041c10004003070380f034060059000c2d014a4120100e441c0c1c60003203c2c000394a9811250b0001c10380c990656640c200ca4100441e42c039004003032458501d50040760100f040c0c090105000041602a01c40c2c207a032018507104454200921500a89040703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 278785728 1250 278784478 278784487
    0x609180f031e0c060501081f02030702100f0c020d020303161107030c120302010612020a060f0c060c020a0309090c050909070905040f050402040f06060906030e010609060b040f060e0a1202010c0f0602 87
    0x4ca07078400c55014129100042804514580241c1c203110350944507510b440e500031004c959228002c05c400140650b4182d018411040120348182c001c0c2a0900c4444c014410300c080100c02d640040103ea000300c445002600516502c0d18041c0d80e202d0050030088668825104000301207850344500382c001d401040d2410310540680e0400900303540d4150040d910030544035507a0801070399074000b1082140c02e1410701c1c0c001245446410340b50680c0581015185904020100064541c08600300060602c242c48086c14192619600e500310765250710703080c000c10010440040c1c54030b8500a0141c2c003685920f456910076031140b01060541d40b1510b8140c0700340e61540c3c05d00c400c615207030150800005541f035082110340d01d088401885000e5621078641455030314520181210350a4100340080c01c06000300b80900c641d294000742403070b407042c40ba403c0399584112003c07400c0c5100307510760b1030135240043c01c1e85100c60500300d021001c0010180120306004c4200000300004290100c0c3c496940d028100050b04c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 278786978 1250 278785728 278785733
    0x1b0f05030c0a030927111b01020a031d19022205070801080a0b0f133008040c03030e1f0201050a15050d081e04080c03010609180f031e0c 60
    0x1204030b0340c0105c241c0741c5407016103d040c01c4044002c0940d201c41d02202240d1000d0342044014548501c440e06111580407052140b14440150014888a000c907a001c010b280030036510303580001ea002c0142099a00f02124a03010758200311a200c090760300080c00003840c3e104900d00c0c80d40012150803040791054031001003005081e00a9a100d0040102c00c0c00b4140c8260965144c900c5040010320324551450200f02042e00c50840b0103a00d001164001c05407000c00a0506100c010030103064614111080415605400180b00e40c00c1c26010300c1c3e0028a00c4a824210741d410b40d61a0594401150412203400c0f002c005030b1110200306034940c0c49038000080f1414404031020030f5030500d18909116007828841004691914980c00ea01c040c0c005c10580e885590980038010514003003280e08407001c0c40481d000c10f0f90f00c0082103840710781030f08400803c80b0a80c0c400c0030703100b85e5804100c600d803010030000d0308401003904410129011442840e112604010608100d61500040312407100010603000d601000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 278788228 1250 278786978 278786987
    0x30403030b09250804020108161103040306020d05060402040302060d0c1209030309020f030d020327040912080109050606030a0f141905091c05070501060f2709031b0f05030c0a03 78
    0x2e00f4030603807400b40c613585082d0700083c07c03114000d4000000580305107100420310b1b119400d100c0c1d80310448010303640e50390381d80d04040e00690007100f49082024079000c04100689010300c203c4084a41c098a41c50134030a003d141500107100507105c25080c00700c6000115501021486400e04040c407030340300001d103e241401400320740c0a04d04209400799024031b10850f5080c1d00041038681451114024101c80140c403003d0034914410503a1158105041110881c10460140c07030103031a0349032513a20040e05a0ba205500000c0d41e9064404a4200310b003000844c00001e400e80113002ca400044601090714486c0843d60003003404121008280c2c4647d003030112205445a009040c0c0200a0900401c214001000002000c0f0b450500410074054000b401d6020031000b904020014900c0d0700404e00380319603805078100d041642c201c1d4000d0725a014210018048000d10481600b9501079555220744142d000b10030306812024181581d04c0c6d1126014000009d00c100014014030110001400b10241c052902a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 278789478 1250 278788228 278788291
    0x30305090606130c0c0204020f0a1e080a020a1704050c010e01051206012d03020306040f020a080105060309010609050412090f0308161119050901050604050d0206030403030b09 77
    0x35081e4100c142031029503642c00014004a0285290000304140300704410703510b041100400a400c81c0c008180b4140280281700178054400702501c03110001b040c00180500004642515007012406180101c0c008440507409441d8050050408441803d45400d10030700d0709a0854080303405a111540224903560f10230040c07041c055003030074800e05007580f40c0008041c100000b0705090401c108044c4540b5008080c40030003080c5204850544848004110b005029600071110507004904051007249800341d240700f219665059943c50070b08507420001006a40d034009001844590340301c5202040d0030700640b04440c0200e21070f10585044451021000d440207030305501000d888448030000b0800316028200f1038400f515040c0c9080b080707091606e0816400e61803c030f480c54000780e0034500150150720003403206040c0c407021a10220580c1e652410008184124003a0755040001950b140c0c005041c0040955001407080c20003151141c4900089100c07100e08650441c0024440000c00680c10224150503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 278790728 1250 278789478 278789491
    0x6030b060c030711010519020105060925030e070b04080a0209010b210c041d090609010e0c12030f03070c060606020712020112240305010b0a141302090a0f03030305 72
    0x1a081c412003421490300e030300035550013500c003584007804810940c1c40350040390100c8150b96180340c62a00565802402460101d507200d01584182012032580b81401480910451131800081c502e03840800003140502110752044946202e142004100810750002074005400d0450040035902d1442c0104041020b041c0e1003940300348030030400c041d00c504007078500f01110700004010040035140d075102510b9601c00d640c4071600c00700e07500307070340c2a040d041400010703004000c2c40080710030546078224000e080740c0207500d084690340d2005904800c0d509081d08900a00050502a0307401d00048c05540030b0207610403540310000800d41c6041a0800c4814850040070388a14401468014113020482d019201e908070f000c0d0520601001c0d07000081c21a0304480f181c414118181d01c04001c64903964180401d540c0000c88295090001014043c00c1c007118210444e44d12100d604044074644d81030165103140c02049440940e020044c0c1c0a181e02d401442d60000d010f841c204410711032440c280201103d4014246 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 278791978 1250 278790728 278790739
    0x18060105040b01050304021905060a051b150106121e0b130b010507020d060b1201020c010608161e150203120604020901080609090a050109050303040c0b04180b0f03031306030b 77
    0x85103a070f990010550380e00603415590b00807106079180712040c0c040310607801141e014200141ca00b80b0b035039002d009401e10907819070307040000c2e00b00005215140c2100d4088000d842500c10010003400e88602003102803803403401d00006400d40d407410104070401c48009850303445d1351115241c03001414088a40220003003080420000380191030300013801c62003400006445259045000e109009255006058841005140d0030312103005252040c040c2d00101d0f54140154685400025080c0000c210044d06e501c081c0e20441c2c0d42410024186103d004004030003070110300c12a004140001d000300b144000074466001117440b4503000c0c51001c4146002800c090149005000b42c9400b40d03041001d550300b180c0200d4113100159244580d1505d00251160041c240790700741580c401c1444070100c0118080c40c005c0003c03515942d200c5040e00c1c0b0502c118840d0200d4804cc0e95103000300181150300408140c4d030010700c84d85481342d00100080c82c68000c481c0c2c80361103000340001000b49a4052103016036101045d1103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 278793228 1250 278791978 278791991
    0x11b02030a021005040303110a0c0201120605180702190f210815120106120512040506030f060a030f061407021b04020f0d0929250905091806010504 65
    0x35110492983c0c010700b0542c40308003013003c150094128000341c0b240c080a0f961103849100008106d500001000e03400f00704e1220030f540002d4114066481a0380001d08900e040750b42031003111507031002c01009041180929071440300440d588410001076140640c1100550302c605041ca0301044e588842810b60441c00581d061103080d40080c45540c0c09004812959040180c1c4400702d00d0080c01c15020080035481c041021403c842c6281062420a002d20102c0700e20004c0d80070654407a10850050951144046c000030f4010700103041030703d602c440007801412040d95660780b5800c1000c0c07144400c8681e03d40380e1400d614040c40011030140d009415200400f04200203860b40e10101841d00b5885000d279400080d0036680c1c02883c001c6440400101c0d4041103440e545090421001c81e1fa016444059440d00140b2000c0d02d4001303d42ea40038010042ca02e00314041c901c8911003c0310502c1c1d46410a015004800254960355900454030070101c030040b58185640b140354040c10014141c000c00d00c00d52a021 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 278794478 1250 278793228 278793247
    0x12060a050c09102601171b06091302070203011107060f1a040e0309090403030e0f030f03011401021c030506040b15120603120703030911060306031002030a1508011b0203 74
    0x204508a1240d1420400d80d040f842c0c0440c01a0140c1d007400d139600303241001c800059070303003041800100309800c88000d0340e20411100311030703c40c1c484071200b0b000c2d40301ca030601512840d03140c1415a014041000303540103180042d90b90102c2d0949010300038015101001058041c14449240541154031a905004014944014103040350051810200600070355440b1202d15810b4010401c403400319100a102490074540ba103801806841e0400074030000740104c4400c2101e51070b0001c151000071402085150840c0c0c204410004001c0c0b04480c15411031051001001c203044250643c3c09821072255004078292800a05210550314980b19080c00341c940c03090000b4040a034a003d40722100741a810321159a11920000f03450120440c0a85500d070200117004010075816500456030b042c41107801140f00c0e2120070404c003103030004031103a80e0980c00580d001d101407081580110fa0040e91400006004d400c0c2111107200520260498000c9079954004ca192030364600e50200c022003581d1000b5850000540e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 278795728 1250 278794478 278794489
    0x609140a12081302120601051809030d090204060914061905011e02010902030d050a0305010f03240f090b01180203040201050a1d121b01020304050f090c070212060a050c09 75
    0x11401d80c400c11015201003140804000d40d40600b498000b801021450303a09441d09480703071420701c00c00d0b00c20010115074000c10280c40c0030840c40f951072840654180301d00d541c88807026002c0d2050403644140d50300f0700801c20381e149105c2e0071003e000c0c031021480300d4034040040c405c145041c1e501199040c0000700d410400c0d030703a001c100b142c1190180c2070282d110340c00785c001c2039000d448031035002941030083d01d0b040a0313a25840300c0a40b80c4103802d56030900440c0d07030350030b00340300e80d18800d001c0600003a03004080352003081443d440d001911440c0110015601c00f21840100c00c0b01c1d01404100d4128100342c0041002c9079606207031055038841008210700d5400d0580c006030a40c8107c107400405d204150200a0003101800b2862103180c070042c181302c0340c01418242c0145c0710301224030300700003e0382e01100b001e0155100000751001d641c2c0190048401c60500002c00010b101c0c010010840d41c03008001410051301c600c000a980c07281c0040040072913041490130744054807001004031502040034441e10501d80e454 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 278796978 1250 278795728 278795753
    0x414010302090310090b040506071b08071401020a020f1c05030609100504020a0504060807020f070605090f0d06050f18030a03020c0a0204050f0702160b19050c0a0609140a 75
    0x2400c0040e42e80701207202081c1032014414101c2c11503417501480750144000604040e114510030b01c2911683e81d80c4850503601010081c00308401403030000c4003040010009002403140a00903a08482d9400301d0001090076a8070041803080140c110300541c03d00320504000300d0100c8880c240d03440c0c40c0e850045c10004c041e400020246403148038800701181d0b02c05c0c01058140044e000180c01559a2440303c0d06c040d041d0f6100c2e1180302c0004a1820020343c1040c400b14030030801c0c6882c80c0190a02500e051707003c80340794200c4102140c4c4084008242a0b503641e56480fa688024850070b00800c26142200180d0840540102a070307000c620101c0340000502c6001c002c8401102140c10b0040e01c0b0000c00d44080d14050b40034034025000303442c000500c4515485076102500c20000e41c0d080b120301e42d84210361500c404c0d12503c40c000410006000002c005030710040e0003005c1041c1440c00a05000840645c00c0ca0b0404072207040d1241c07607030740c000c02051085620b00d5180518200e401400301400b0343d511003d90014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 278798228 1250 278796978 278797019
    0x30606040207030c081210061d01030e071707060206100f0501181706010311011d09060117070f030c030209011e0905131b0804020904030c03091d040203010e0304 71
    0x140042e0a404060041c030248403910f8200c0e03621350b110501e00911940c080c03c1035074422982c00700c0d5400081d15520400c241058030340d405070380d4100c083c078020040d40504214940707400310303000c0da00010610030034100b1942c1c00c160902008081e4a40f601801a0a041019285141040014005001350040c90f100301d002c0307550031300c0e1206aa0003501e148000c4000560444000c550541c04154030340c074030004403241620b000e140d00b065048504401580c884003140c42400a42200b03103000380d02da10b44110410342c400c00c181000c544945c010540754101c00d4040b142c81020600d1182110007465041c4202104101c16040851400d0030800011340b01c8480500d00a442c0308900b1856107006100e00d01c13540003003202070580001d4220559045019088814035034a0582d600701004140030b1044100e1380c061900070f4400c0c000c0b5181c40d00d080300d03e01c06a05064080c801c20000c0081c103807152107040510341d03101080000c8142400d10406080d01e420b03003115005544240000c0c0102090039480303020b07412 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 278799478 1250 278798228 278798231
    0x1b0807060504031b0e130201110d090b160b0405160e010e1f0513020406230a12090819170403051602041404082a120c2a13020903060604 60
    0x8141c815401c1e041150304100180410172061026842c0c030030781c00c0800c5c41c3c402d8940b000c0c042c40400059a65800561010000483c0c0202c2004003268403002807030500620258850f2003c3c190b00c0b045002d0700203071001c81d500e50125200c0d200e030705001061900980003200d034012a5500d42100201480400341401400e00c080340700c01c03030302c0c880c00c800848000c1030050910005007840c01c0c5103600a40040c4524404140f118240c51441107640f02c07106007000c0340030462420700c04040300480300a0090414101d00c0303a41c0d0584c5c9000319000d9805400912440e90302d4065091440d000203045000714039141d100b16040030180030004e50810151841c4030f502e001c034551260341c5400050046c04000710001500107140c01400140714040c801001000070420045041d000b00602e00e884010000d940c40c585504403034120001c0038900802003100907540c200700c40501800704410403c1c600307041c1a10081c1c00081ca1180c0702410403600e40b0103090f90108007141040c05040c0070940b40c4100070031241c0310700d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 278800728 1250 278799478 278799503
    0x506010e060a1803030908010c02030412081c110a1b03020606010318060f0506040506060a0503010306090c17060a0b04021303020d2a0503100203071205041e1b080706050403 76
    0x7841868201c203001d545550450883d40c1e203080240101c5010b0145268a500b01807062850600010031034088800c8d40560f1020030041e5290b0245980060401c140d401c40010768031f44078840c3c207004080d0000c0300a02c001e6a618161180a00180d1101074011a2441e010303d000c0701003a000300361164050000e0070301152040d085014481d0202c1e03801c2005010520700ba910324040081a800b092007204203441c2000280c03a040100300742401500c0c4451700166080005100250454121108203403041156042c40ca0710707820f00c402c0c85045c0d051000c0d41a4880010400d0414050240c465130207001e03502149000601034540c9018125400f019010b0005144480c04010030401759848911312592411003d00711040005c540e503165205040c881d102d41e55110b941d04049100f100e0003468a515030140c0d80d209040104003600009105542502d00c0380d07100002c440d0040360320321105214400c0184103000c603400c1080f0100c05ca8005000c141e0240b2000d100c915040700464043d00d41146c25610803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 278801978 1250 278800728 278800747
    0x20c030c0a0605030a2f0c0c01020303040f170405040609051b03310b13030210061d1312050a090e0105032802100507060e010b0a15090b160210030506010e06 69
    0x84140c1d2800c0d807511003404a568001160811014180800347d8000f9103071224800c2004a9880c00165005055440032401c81e01c0010079580362142055095401c0c00c0c10142e0f140c0c00202184c4c9075500600e0203d85075800c02c0182100800301c50040132010003e2815410601440340b8010607140054203842c1810034540c0241411600d60000c0641c003d0728146c1502d480001003401e40c10500d82140984511b81144903900c0b407500940058030200485010f601c125094142101e04000c0d0112009034800c0e400c10003c18000601e40d07140400c80d4591640c0c8070100c41005002c0c1d10160701a4a8580054006100c103590105e2404041e90b10100d4107801030200705a0103c0c400d8503131400a5000d610381703070001885904903010740602d50181d8010851141c14403916400e032004501103070ba015241441c24032260b4420b0780c809440180924050070303159182e81c4601119032100385030a000101d0358003640d0440c9040404c0d0203001a45103828001401d0081c00a000e0314000e1180d6072081c4008a02c5201 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 278803228 1250 278801978 278802011
    0x6031e0809040e16090c080403080606160804060f11030906071403040303090e0a0b030a120c0b0a0222080a0807060e0a06050a0c0212032e06020c030c0a0605030a 71
    0xc1c2418028010400740700900c02803556680c1c200403c0c078140e8400f09000583d41010701c03d1400ba0000c41d01c030720050b6038803603038215030300c15000300741950081082c00f0001c07a03030204844c00c403000c0b4411031903250f903141000000390404100c0c00d14001044400c4552440302003011040d1030303022105440d42c039250001860205000c0b4000c101d0841b052101080001c11b050b40b210700901103504142c5035100d10f494590011058071400f00241c2e80542c40840200c1c0040ea080440f03091000d000c0ca40001c0c079a0701603031058000e500942c2c01c1101150007051841d841c078001402460b090f85091243704a0034600182181c5441648802400250002c504102407103c25000002360349404010b59004007010b24084005043c151040c03c5614580044a800180000303170078440a462880c000d42940d840486542070616003080483d51031600440c0c0c1e41080004a020402411068002d40441c502c00402d144c0b9000916a500e4812449503204200a54101c0126600002000808512915201b0140d035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 278804478 1250 278803228 278803237
    0x6020a02071d010e010902070b040b1906171207050d18120f03110c0a03060f020909011701051608040f02010c0206131a07121b0c170d020106031e08 65
    0x4040e801c0c1c0740002c0744861003020759069802c04004205280d8a035030b0524202e0207030840080c118504040864080340c006c5403810f5102c24010802c003030b210102000082a076000d540080f08603c20b4032850300303400301c0c14003a1412a40401c08d10f141801100e840c4c4075135030140c20307907514140000e004035040710142c0c0340642000360454443c80d91046005281145030f0313201000b015800211508441c09407000c003c520641c00c2031000302180002415908e51100920282c43c40c0d510543d4200b150703850035120b5100c124024088281641d0341e200c21a211a404e640e070042c0022038010200c0300e0010030b250010790b86500035801c24843c412a90142c801030700d00c5010101e000c3d44c00340000c070782001d003209001107903026a445015500c00a01524841382a20701820700c00600b42c0d6011030000303444511a0003221032440850710840c5031480700b500c0d1000d09004603003186106400c41c0046603400c190030002149010028070080059a156071982500f503602d0851120b8141415014803061013000780954 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 278805728 1250 278804478 278804489
    0x1e03021908060c18220213080115081b010212030c0c121b0f0607030b03030403080412030e0f090601110705120a03020c090408030105040207080408010e0d09051c06020a0207 76
    0x480322414031110051480c1c02c0391030700080428940210704131505042104032050750b841c20703009041c4568454130401a4104290110342c00f40c1044001424103024000e0f000c0d5101d21600f800c8180703050010f0142001c3c148800c0641012a9160792150761741c2c0091400027840d40d05540a49030340340c2c42403104007031003440c0050010340708042d50030711003c18030001440b58080d001c20300e00c0e500c0720350a00d040e00d07007001c89000442a0050400504241c0c02500a485100401000d60786019100e50311011540c00580010522210b000403000406400000d035041c20142111920460f060040c00282441d000400490400144582c011352130301e0104250405044014100fa46810209c45000d0703580d20840d100b45c2c0144201c00709c01c0414140040050701441d08501c04501c2c1d07030700b481c0900020b54880c0404691300c1c0400c04c80000c1d4150300788a044460b40c0e1032400b030400c0c0602014010106100d80d00094030841c1403900c0100c1442c0340183d000e00329648090056140d8025540590038543e05a109 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 278806978 1250 278805728 278805733
    0x105160201212306180112210306030309050607020607021018060203070b0a05060109120807080406030504020405011a0a110a02060c060a051014010503042f0a1e03021908 75
    0x80d00012250b20060b401c500c0d43c0396682a8030b44d41c84c0410480a02c0e030b01106182404c417200014804110100b24801020b40110b403e40300407600a200f10300c010b0801c040390700010f030b0348400505c01c059000c8070640c01020b00700d4070349080007208d400244503031081d038400038418440100406040d501407004500070b044d420550b05000380e03441b44080d403250301c40351048031440305000015507524500d10030030b4021203040e510f036502039086c81d100c2083e0a10454081d05c1c1004240003d60000e40c6201c02800906066a40400c2a00309071041c00103a41c0180c1044103035107103000800d80382840c0b4000b0746810403003d1030b10404641c02d92008500300021810045e400210018030950350110004410b0700412041908000d242e480d24034018280340d0b0350050a4100351041040c10666229074040c0d90003d01803510201d11361a001c011000c0d00e03060003400410503042e203c039075103140380c090101001015042d0b807604c4c4c14a940c0f20a0b03106c83d410703408000d00c0754a180b20b100714201c2c031220100b03003e0901ca804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 278808228 1250 278806978 278806991
    0x30603210305060405010e0f181b18060105032706040b040b070804120c0602090301050406151d01030b1305010e01020306120a0b0a0c032a0905010516020121 69
    0x103440c050485440d8600464185800300d0428102885841e040750030000e101c141c1500c030042d07480326504015000710215140e40002e51501d200078001100c00d4007a25502c007c412040005220103180051130054007100d49030208900341e608481260340c040369054031140c40140034183d2003400c544511081c040392041c00100310402101c6c0010301d000c0c1d8050300c140d45c036580e59103a08840a5800311002400e840340c2812007c00c19020f00c0031501520b1040c000035003400c14103c046070845104035401c0e1070580d1111143e02c800714103044524040d0900c0c4c1c1e00064400e80642d91040000170601c8000c20718181080058030165000d800180711a600c04e00034090340800102c142c3c040c2d00196074491064112440d050300c41c0000042c1c0740b00560740f0905440136950707080c0d2020000c1c0313140c4500505240d144c1d42c071100f1070b10f810442e000203070079a00300c3e42c0c001010f01d100080ca006c400c1d402c801d05205040291503010f021225a05800545c240f03000c0750700c0003d466609403401c0100390414500e038100340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 278809478 1250 278808228 278808263
    0x90507022509020d0c0e150f0a1b0c0f08030c071509050d0305090a091e09030e0d05010204030c12021309030c0b010e04060b1e09041103030705030409050c1306030c030603 75
    0x100a45403203c6207550700442d4211110407c0717209a80801c1d0326580b00c0b070030420070807050080d101606a000b1981408080d90001010f10070f0040201d034011030b104c010404040c0000717240060b502c4040c01d0607030010750610f2600d40040b661540b00e0b02404c101c203001031202107029442450401c020705006080d910350308000b40341c041c0c00c580003421003d100b0500b2200100315843c2e288500200c0c000c41600d01c1038440038015510b4020105010700380c04000c00040820701b140c4a601055040d1803081d4001607035140f03117042c0b4004013082034015203590040d10456102698402084a0380d00085c09e0001910201d5407909844c00080c10030007c00010010000181000e2404400c0788641d010302810300080c5200b10411040003110000c40040c0c401503228425181482400240e00511072a09a00183c581d200081d146802802080358227500c00201800100900d0140701c1d00412503240071410050000200854030026010b00010141e480802945c054405d0300046c0c011504680d12107018103c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 278810728 1250 278809478 278809481
    0xb0a020a0302011b05090d260d0b040902010c020105032203050c0c04090c090e010905030d05010f060e030604030f05070c0f092307080705191701090507022509020d 72
    0x41001e601651803c91031810605113000c2103480011580e44042c6409880310400082041c5d80c08240c0c0d100c00103450b0348003688401c4100d4042010443c9a8540342d25150088005840002440c14041c0c0e060041450045c0d0b04a5034000c40c02e642400c01a499540321009403201c00d800300f2015003c1c00024200e030003815001130082c03038500315940036a80500700d8442800142d0341442c1c401031030349072003140410003031304036034029010400392000215040316070752601480c1da006071000d49070841d622001007002112600303aa400030030041c20710101d109000800241c0340c4030018006020b01201c0c0060000c5039110340b040320f1032260303c600844842c0d61100100507086110b401902c4010b40391004116564404465203448002c0b0003068402c140d0390040101e4003110054044001d1120501c003282584111915602c100400c0f6501c100740d50081604002c40301c2e1041c0d0004008500d0031041c0000a640400c8040c1c6510051505414402084105105180340c3e41e006000b290b00c00f14003003c0e0242d01707 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 278811978 1250 278810728 278810743
    0x270715030903111b0411090306150a090603080c0601050306091002300117030f0418090804090b0901050409030e0409020f0d0b0a050907050901060c08090409030c0201080a020307090b0f040b0a02 85
    0x156020458003090072521b400c0ca104001031280d0560000c1d000403401c1000d0440da0701c45e100080c12502640e44d0740e0044a003038507035a8004550540b400302d0010001a001c2140c9401040100d000b0186810f11451b404d442d0b05c41800003548541d00007414001e0241c0314142011150003024501206041500b1614905402270241c1d00d0300912080030304061090000940b6548030806003683d140c146000902d140040d18150650701c40c50310742c04d00c80049519007014200400e6000c501084440c0c41208100302c035070050700024800c3d40f81481540100e40d01c0b800c138200365101030702c0000d0181c5590000078020000c617030200c2ea03c001c0c0404030300c041008481c200c078080c000c4100c0c01d0105445d030a03203541d01c66002c8d000d01500202c40c1001041202e1144000010403030044400601c1d1451410102c2c2c01d075540000c058003c11520441482156407041c00c40e580240007800850650402131001031064a40e8407400c8410303003000c22007036030584494046600400c03420701200d03624485060b0180d00c1d6040c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 278813228 1250 278811978 278812033
    0x2090403081e1e04050c03010c02160801021e03100b030901020c070e1b030a200702030d030504080306040e0f071e060c0b070c081227071503090311 65
    0x1c03544101e03034082060000c600518103414550aa46480c084501580f48010402c1d1024802d082600030551028402d502c0c1c014001d9001d460360900d000030240301800c00c0c0d0720040803a881049a22808090101e126050f032160a034100d40c0ca44800704010154803460308108115540001030061005056008014181c500d200381c0d092140c0c0d41c0755000c1002c10440710340c002031803105420402c28210394000d5a20150510380021102c009881808200400b00f41c200b909040001d100030540c9410000b00506203460300e000d001c0303440c1980c0d0340e0100c0d0001421450003103440e080a50196481801412400074020b0205d541c101c0e9500d0210114103802814529011400c400103c0d001d0301c11515980d516030081044d01c034a448000d07003200c501034004030642e1403410074803118400841001a0394040c000076140701c0e03811002089689081c0d003078a03140900a5021a01c2042440c0c1d0303000080b5000c41c4c050400007200b01903400d054420003004030381903001d0300408002c1c2c3c0c400c46601e600c4958810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 278814478 1250 278813228 278813251
    0x913060207020301151a071e0c0b0d02030a0f020316030e03121905160215060a0312030b09070f020c06090d0b04201c15420b07140106030209040308 65
    0x480300d01c6c04200ca20602801810b00112003056900404203c00741c1c2d01a14400c0038680000c99944003e42c2d05134004500f1f83d8003468000091209026040c090b140c000607040c80c0441c40c0d07003005c40d40030840416003090102415151a01201d14040500c00d070b03803c81c0c131908410019072800092120401600c203030344803446440c1c0004501c0381c29207403501003108003240e0010f0010250490014243c070724010003840d4070a065160200c00190382c8580b8440c038007850b441c04038013050040e00700301c51240003c090f8000c01c032a141c0c00500785640052a5008203200781c803100d0381e920041e0040b80e1404400113000d03080b04261010b110400020720484a0018034103200302c2070300584c1d501005030b00711310340d0700c0390043c0300d0020f03148004102080c1c004036075009840c01c00034000380c400348600750803180c814603042c050146000401d036102c0641c00d023621101034032169003000d03810001d40010314050307002c005d00704940805030142040400d6011001540d00184072005510b030503c0e005100b130504480503481301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 278815728 1250 278814478 278814509
    0x2070c0902090901090b04020d0e0d08010b03100308091201060f09150b03011419080d0206060612010b0f0403050109121b02030c0607061b110f0705091306020702030115 74
    0x4020300c2a40c0020b000100075074966440d200301a001b6007410403203254459820044007100d1800ba100c0c549550701804040c02c00711030181005400e5000507400001d00c00403c00c1003181088511190000340e07540800865260324011003c103143c1100ca0b84104600d41c40d210001c1400d5802d00d20140c01c60700144014480880f08000f81e51801210740b00d011000c000c02d00c0180841032400307007087d88854016000400d009036006515507081c2165100c6440c94221002802e1501d90500029500c59002c0c1c624604e070010a812904049005100307108000b20b01160303104859000c8401c0b640250342020007401210303100d0508840e0380c0ba1031290600424000010905400d1190050341341c082e8000300a1b2050030360500170301c125a1712402d811102e16030b03140c481d1410000d005489980d40a00760717036000202c65119800910b0880360f002c0d2010a0341c8030400c200942d03600c0e20012607110a215125042d10b1456181000180c080c00100030340c10750800c2c1c030b40c1403906000c465040449070f101044041c507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 278816978 1250 278815728 278815739
    0x110d080306120f060108030c1b03100e010b0411090102011409190f0606060807080105010f0210050a0e030f030603190b0c16050607080411040606120b060405033301050303071202030c030d02070c 85
    0x100d4542d1115010b8000c940440c00bc0c100580c441c10b82404014000b05540111400042c2111120020720080120108400d000740d41c3c24851284181600c8145030800e00348413131503607510b10080d0340c0b4121305944c100303811041181c103102d00750301e083e88144c051184a40b140303005441c1d200308841410008141a00000e100d40c85685c0e510303010249a005814904184402040a0030004080d81d04441c2c1b41c040b5484d00280400080c41d072800003402107902c80c02c20b0300802d41881081f000c0b02103041c1d40030a518002c82c072500d00080d0003080b80c040c0c040d0303070320414031100c000c55810960242043c01070000700b120070754020581500c214032810402071a02d60b07282c100022120076000303000c0000c0840b41103422200041e84030b0308846000914140c00d299407900081d140008002c04407640086000268203086025030941f15030800e01340300c40200e9810721001c640e8a0203401405405401c0c0c2c2610104036500a00c101ea49001100c03050300c0e55050f00d09854000303540b112034101c039403842100c0001003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 278818228 1250 278816978 278817013
    0x702010e1902040b2d012109021e06160203011104121a162105100e090106030f030806040b211006080303060622030609110d080306120f060108030c 65
    0x4105e000000141902c04e14140070f14a460404071540d0305114814181403042c0c00f0b0909a251074180e150301c0401d111001c3d106002036035681042140c1c0350180411130442943d00c0d007081c1d50440113041c03001c01001c10300e400028050b1441030442c0b207501c0b400040c0800d00003112550000854003506074021199001c6034100442e0204039178803030180117900e0710340c50700c41c3c800c00c0020001d14184000384085041034100f00100c400c1560401030184444404000200d03000310003e5000911400800034140395455145005100c8403005003082594000580380d40c0e20340d404058104006044210340c0b00800c8140c15016034000e00c84840d52017202080d0350349031900d000740401c0c2c44425001d54210744aa005210300c81c0c12000c0030035060403030314008001451102012000075800f4070300105840b103c41c107204d4120508a05518083d002d821202404a0560011203800003800d03107501403203807080c2c0c0c1c1407410411207541070300d00d600446000048004000020b81418000081a101a0f200c202440c0d903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 278819478 1250 278818228 278818249
    0x6030a0b18060f01030c0e060d0203160201061811070f140c0603010f060c0f1506030c06031407140c0604111008160819020d1505010203040b120702010e1902040b 71
    0x281d212082c08a8003d581d4801d421040100c0f10b00d0034045010180d03200000c820350802e40c01e29000c01d501008100e14800e40c0108510b07280c2980c0000c210090912180d2070144240c00449101c042d101d240900c0510101002c070740c6200d40201004100841034901049040c01e24601e00c0254401d40300c40d074420386480406c80b0b04994404083c65001c914180066a245150034410b42c0c07212004008140405d007241c00007401102c090030b000a200c1e05520b08030303c1541e1550440740406180244800c04110120011500100907050103a02c0c01da8a02c041c070054400c1512181080c0929810300041002d4070344a40b841920448038a14400114881100e914000f120000e040780398243c0740301c407070902840f085600454114040050889551405004d99015255840c14550340300d00040810003204a6580500000d102070f5280a103083d500040c6401020f000c3d241440c00c0c1c0d170206422a0003548100030b8030b5416816502d034459101100d2680039034018080e80258100b41540102d450640180d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 278820728 1250 278819478 278819491
    0x601090f150201021b0a150905150406020f0d0209120105070f1d04060b071202070b0717090301060b0301081915022208070609050603071704060b06030a0b18 69
    0x3815410300d0030361603110145280e5040800d65508020120500d2503818139940c51054040c010b02c201181031030a0a1301420076451005084e1408400d1000100302107402211103c42e0b03161124161142d0030103200920500113032010092000522190410181c1c016011030f00303040360004205404141d895080c4c5d00200c640f10f000a0103500205030799030044e4610341e01c214018140c2c9040b82c02c0840400c04803045500b01416220001c20700500b082845c4c00701110508507803020308856890004d00d40d88600822400070441c2c1c808400040200c0c1054050316420f05004000b480842c3d03445540011aa000f03000d001a14003840706009031075a003101208a0b5142d200104400360009494030303100a410181e00d080d0b10380f56900c1d4444103482000c5500e0041c3c0020300c06401a186014406804c2c8071180c0d000500800c0140704001001d0b4004000070102e03d080d04000304140d4403850210018080707040144d83c0503074044144041400c0302e501c40074440f1019105181c00001c5a20b04414a036030480d9072 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 278821978 1250 278820728 278820749
    0xb040f0603080f0d0f0c030203010519032102030d050a0608070e0712020c0c031b01030c090312050705030409060807150206132d060b100f09060f14130e060109 70
    0x40042c15403083c0061104500c0194006840c0d114107802100b920641d0313102d880002e80100050107985400341c03001c52a041002a0b00c100c540c07071640c0b61100c05080b000488808803881c0c03003000c40140240100d50b904e00340204100603d180484584009001c0d60084040c64841d60320701045808480040754019030f140c0e210460350650103904c45020398071464982285000d150101005c80d00c0800c2145040c26038142209107405080c000102140c0341c0d031124104111200c8401c20100311502411960120b10b407a085585d00b5541c1803440c50343c407499200c2ca204c01d24202c3d000440401c041440070607103017042446070354104101d10883e510b05050f80c0901e1034400c0a58500c001030300440035522005c60351300c000c0ca03c0301203c3c0c0d50a400d2101890094850580b1019541a18902201d146122400074108504144c400c0b1000070480481c0340201c83c20701c04005041c44189015416091a5a83c40c0407801c1c0e8414209080f84910000c03072141010355040d1001240c600c0d03005820b4442500c0400f1030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 278823228 1250 278821978 278821987
    0xa140d0e090a0207020d0b07140403080409090804030c120b150f0415050d112b0b0402030c060a0f09060305010815130b040b010e0108060411100909020a030b040f060308 74
    0x104020001c0281c48982d0b8181e0810100005172900c0c1700142180e8011100303030016180c090300c084c1801c005030b0b18419101c83d0030002440005c40700010780d016a1509000041c45002500d481480b610aa0304040c0c403038040d01d80d00040d0141c02034412801a40700c0c0c40d11407143d441d80c010b2500316504038101c10b58080083c0028070070f2400c4c680c0c01000c10302c4034a01a00390386a074a0300410100301507018240c0303404c540640c1c0c0b0703905070030303c14192860365079041c18660f11801001c070382d0070f501088401e0041c1603d40610200b010f55504000315441c80e58004c046c07030380d00c0c80500d101620350040f002000703010030545030f000600f5034000d02c00c2904075030315640a403541c40701023100041e44c00001010506821018010040411a0040014442d85c411038220300c0650501c1c20303441203c54140d2119284d41d0145080100040c001501c81205820944054085d02c2c0846800d40d81c608444e0805011702e0301c00704c0c410541c590305070041a05484140d6042000262480648094451501015111100801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 278824478 1250 278823228 278823257
    0x20304050109150c1202010608070509150d080d0c050903100507090b1309060807050108010807140d11040903030c14070503040e0c0708070506040606120c09050c12090a140d 76
    0x1103032207440800d40c2c03900018140c000c1d45c0740c429940c080500f000c0181c0d50f60405218000003000380750f024140031102d08400d45803140c07410740b1282c212001c0602601303102040303504021220068604058400b0414010100c1441000306150800079416100f0711960760840c2000245200386801800e850707803400030550900c1c3e245000c070b5204500500e52140700100c0040c2c2888078ac424030000c1c0c041d420182010510b0b01000505052060b0000150f5401610080110b19201c0140751645981a552500c1061441c20101400251400455082030401d4662820554540d028030071401c6142c590341c5070080b417652610310034083c00d5801010795004120a20041e410034450a42c0843c01c18040303403414506c0d0742d0b88559500714013021149903218605110402200e0701940018280720460354040c054952946403074495a4811810f05640d683c0c0030a988505210483d050070303d05000084040c00c01d03004259442000f08000d40d0040e020118044001d1400314650035140307880d5450010044110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 278825728 1250 278824478 278824499
    0x307020a0809030f070308030a391e080603010e0705131802030d0201150b0a0e0f062106040608060c0304031d040504140c04022104020a090e0d0f020304050109 70
    0x2e0b40999140c410071103000c3c21014100524800b8512884166442c4d003030101081c2c080d00e41c2545042d1059001400311100f80c0e141e00c107480400d101c0c0150281d51400d001c40b05686424103001001010b04c07a031a854440306400049660003000264002c02216107c400969240e4005018503039002c8070000404d581614aa00190b00a81c01010030300b00380012540007928000200040274090303510b6400c1c840d9031401100404004215002081d0315207090081d0003000e10030854000b03403040141c4403d0308495107543c0e0a85002c0e000d03180700b201402c10804c441950a070807c03210284601d0a007080820070f0354000c1401800703a400f41c0d254a0440c3c8a41c0d905a40c4500c012107000100111166074040c250303aa4080c0c0d80c0201c2c002c03004400100c0120240314101062103a40c3c9000c5c50040140490682e5205200e504180c00604944025101c605c0040c03043c0741c203a03001c40011401c00e00040034800001c00c60809100e00e0342c40e00761122111800690300c80c0203e1180501040341c02c1c00c1002840801d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 278826978 1250 278825728 278825737
    0x307030603061a0f1e04050a0f140403020c09040317091e0a110301090b130f02030d0909050f07050d18140c100c0804030308130203060108011d010501080318150a0201050a0605060307020a08 83
    0x18a001040c0d0302c0080301e270a400c840013030001d00c0e001002c041c240428950107118a01a0031020f0340d0702040ca2410b91070182c19010242003240c803c00c7e000340000c58561040c030800304080d0b40c3d440c540c2003110520902c1079485501c4102a62003001d00004204980b4052040701e4941c1d91042c400506541c0e040d5140034028501d1400f07958040c0111001390050741d003484405602c0c6501d4450400c0907003400e00e59003c0340d80003803984030017541440621100302e81220035220078426076540464241244a424001102d01d4400148052074005840c1c140980103e01e0702ca0749141900d07010704034550b40b1000c03113100c02054000f07400e600b4208410310100344510440c40d405502804c8100300b1445139804246800c1c402d900105140c1d54910000b0641114850180e0404816000a1100c3d50400c03132103684a10442020000e06034050305c03601a6925541c1d03400480c0422001850384a52181102a018000c216200d1a56618100c008940c0c4d1400e80252400703607031035038010b007202a500d030382e1030265502 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 278828228 1250 278826978 278826991
    0x20c03041206050a05090a212307050f0d0f030c09180b09060d0c0e18060907050108011d0f06040e0709020702091005150307030603061a0f1e0405 64
    0x8108000720300381d0a03600c00c8844151141c0070028040c0707021402201211800b0f020002d042e049010344001158000700720329240080300025074010840c88038290383c103000d81e200340404101c0340103058010203501c2c009404010f00500a4401d6056451030349070b265031604120078045000303003815a520314071a0388032000784140f074109804017a40740c490701441d00b15070711080e101d82602c6000c102964140b0400045c0c2020042c0c4d40340c0403010a0b5610121110301c14080d0010386000390300042e2114600380c03550040780c0c07255000d50f046030070305900217510342403075015071408111040c00004440c40c0140007008403000e03c030341150381622100c81d41404210050708603503001d515a00d0b020228001400408010304180c20010381d94000352040c8400d03a08010155800d04004400800c420b4031010400d0500d07100341020755a40399203a020540040400b90000b50840d440c044203840450440c2d11440b10801085450001080417041000040000e0540d10307158254030a0100e2003e0030560041508040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 278829478 1250 278828228 278828233
    0x409060b13090c09151b050c131a04020702040f110403060c091503051f0909060b12070605070f0b0703050619060f03020a0504230a09020307020304030803090a0c0e011d0906010504020c 81
    0x40613042059880301c6c2c0c895040c0c690350006032040c8080d2920b01078a481142c1a0380e824020f200c18030032032601140480082500030345d00000e51008540e526031251203800c2480d04100076424000742e018005070001d000c201c8030145421441c41001d80034165000449030314003001c030004600c1e808220090304025000382c0041c0f607010154a4554088207100d00074050080740095203000904040003950703200740441d40110f44007440c107812042c0c086000d00075166281045583c030202407070030081c2c03101025005811410b00c201801003556041d00441d024840882c3d240c2040c0c100e0400204410072503200c1d4802040d42c500c854001c4ca4001e4005c0e090101c2941001d0307060681d944000e10020076001e00380200070140715029003007480c002c2038001c050200302e41c04508500e412540070b581c91203140070143c005171000c0005060204208801956a640802d42c465032035a640354050b2614000c1c0602d00c10303034840c0742c04051800e054801c403503c10410a001000305901c2c0c007041c08000e501c400c04524450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 278830728 1250 278829478 278829497
    0xa0908090d141c02010b0d020604061103130f060905061815090310020904051308090f040f150305060a0c0c020d0812100602010b01080405030a080c0409060b13090c0915 74
    0x10b0824411034069100080c0b9160301030b0403002000713084841d45501c05200e26002101d040150303d0319000c0d10107039041418007100a034284180c680ca5030052011520040b910081c000c6031810007685000200e80260312110859a00d4408200c102d0042e0400c511b5400464812015245400a612486280d003d40d54518202c10788001c00d013003070800c00042e0109034000402482e141014404d855111a03841c101c00144086540c9994403440f44400581c404e00c42c02d030002045030703903035809201c828039250010001508003592808140e001341c0300c1079a0307601507000000c4c441c14983c007a45081a1060349c4002c0f601401d9420441d050510308070a48501e10280a010641ba04050801e40500d98001c000f082c1e071898041e0007170070754021616490410104c007060000052001055515504803818242e10b0f65580003a030000342d0080e03501894696050510000f084884c49000380f0300c0c2c044240910400d01d0300c3e40d0840041d501620303034003030024010318020002078254040c28841070880340f42010b1031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 278831978 1250 278830728 278830763
    0x5040812070b060901030201080114030c040e0f010c050910140c01020a0206100602150601030c030e06010f0e06040905070501080702011811030607030b0609011b12080402090a0908090d 81
    0x10000c400c2881001a00d00007000070502c100e04048641c009030444840003a0360440e80000d010b0700061181c4030750a0000d10150220f07079400e1040149922003c0e00c10400825000074581c0d4500c050003064025519040100d502c461060b4100d0b0040c45010b0207582c21420305503000c840b0040d00b80154040c0340c000303005030b20324140300b800206400403c56004140390304040ca5802689000c591019065501841002c100300122000c1d0b075074400c000b401d0003d00441c4244050380649141e1a20382128003c074000414809417403019541502c280c07402400c6a96210004e02080350036036240581107a00c040310400c402d41c4240e8095034846054400882c8803189000c002e07a50595400d001c4890b07001c640744c1242941801c105440d40724105140a201e2050505c001c6429032140c0322006040140c80c528001040e12200d41e1150030719440321800200d1901860010107110050342c00700e1042d00d1150200e4452003140c0030304440740790007021303180c1390180400400c2070a02c960070302180c1d44021181036400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 278833228 1250 278831978 278831983
    0x10b0f0d0201020c04060801020c06090c030601030308070c0507060818030f03010302040b120a03081b0a0e060d1512031e1d0d02060a0f090f031a0c04120606050405011d1303050408 79
    0x20214a40096100c0d80122b5034141060001845040181c0c410704e203905481d900092400d04480e01401c040110343ca402404480d8082024000350491281c2c180c0040c000340d00010452203403801190101150510b901526200d202d603050501820701c042c00144054681a4400181e00310002c1c04010540e01e00b9210500b0300455441c15404200100c04004ca081c1440001c1c8600301c0d501400e41d45000c00d4800c01404d01034090795802c0c01b0354008202c5e4800420180c0c00384102c42c807107000c0b900c1d000e0b65881d5144516491494101c3c00030300700c400d1803403214054030031015800d606070b219502000c0000100942c5032050410f070365840b41c517012907070300941c4038040249048032140ea640c040c415048603000d080100d9030fa005c000200c80c840d104001045c10b0700540360700044602c124031940d84400c00c0c0104a070060744c0021881c86011021a1b04010b096032100d030032514182e405002903a078581a00c10f412000c0c0780e11000d500d00501c0000d203030781300904250100520908200d410103460390041c92 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 278834478 1250 278833228 278833241
    0x12260114031e06190e100c030b0d0506060f27070507080f0a030501051215040507171c0302120c0a020a0b0112060e01060506270603040606031202010b0f0d0201020c04 73
    0x801d03000141030018465100c50301c08100c51900300284043e1804000d410307902c0301c1c0c0100c0841255641c2c0000d0041c0c608c660003190041e24000c0c0010800c040d02e0414946881c3c0598800e44500b040143e00f0240c0e0601407c40420501030a00014550001e200c0e0512001c400501000070444104007403400601e0342c0010300150803203005025102e0f0604030300035084500680060303110300308440342c0c00c04010000440180c22049012014042e0300c441c0b03420380c82c0207855001140c12185885107611590070014028642c041440ca50075511201d40006034120301c51840c1806610240400044100c0c2c0000c004244050f41403040358010b0071907072270760801c202c030a810110001d1481400002880224004d164003054828000c002140c034000004040784562441d82280c2114480c4c481c1964220103d20b40480f940902100d0303503440d0900c0c0140040400d800111a000315218442c3d034003510501c40d01808441c080c1c54000000285d0040003004034000034100e0440c401c0925281080c1c5450150301c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 278835728 1250 278834478 278834533
    0x804151103120106120e031e0403020d0803070f0801061409030a1b06022109010e0604180c0f0f0c15021b1b1008011e0902071226011403 60
    0x902d01c650603d00003d003a044100d64540c4440c1c10011802c41c0d825001c8101d440f5400100420880048910341450f468011540081d5004080100000500c404d0900a40c400d00c81651482c2c0f840302c0c0a0000d8170b0301c0b60f080c080c540000d500e45030480781d0108501c0c000c00c001d03180102206d619030368a42c2d582c801850aa0b1404a04401c000360410002c0d404000f4420090316002510300d003044481441c40c444d00410840d2410040400c0490b5400e494800888000c1c119425502020348940b840d40005040481c0d01030b07000840320710f0803000003403059070101007288090f5039142000c8890380740c1210b480310081810511980c20010708200703000d1840c0c15502e21410b50301410061100360f106039180e141c248080c1c0c5c01200142c45024087c0d5002c04400d05585402d0070a610b150740d402d11014103c9426080110203d100240f24810302c1043c201058508581341e541c03030917401040118072101c0f0300180e514440c80c02c8500050051411004a4450307401e0f01404484510303443c1c0c00d0b602500309480c401c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 278836978 1250 278835728 278835757
    0x4050405010e0c041e0b040608030304052b02150a0608070e061e0112150504020f0c0105090f0c090604110a09031209180902210304090b030a0804151103 67
    0x140c20081d080c401d08038a040102c800300002003e804c1210341e075000c3c445580320307a17075955441c05409940d90f51110f00607080b420304581c2c0f00d14040c60b1050b81c810620010007115002840740f00080c0e407088010102401c0702c2ea0203822050104800d450307441d00d0160581009039120040881c00200030001e19005008182c0c10480c142440000d0002c1142c40500b01003280e030f510410079040d40d8100f140300388011826100055a969003200c42051101b081d0442940540002040064000d03000060060b07004042c000300815121410040d648003424200000280c02c43e2000d08101e25004c1000b59001402900120b1008204000e601c10381d48000120000b013130040000b0b0003030181110b00074070303c81c44c6800e01910a80c1030a041807040000319441e42d001680780c01e00d800440d111401041c8050403100454086602100005612a0024015901054070b01440d1001b03d20380011040e803e6504015101d1a150515107140314010844c0170030b00034404003d00c4803907884000c20081850030702c1e0001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 278838228 1250 278836978 278836991
    0x10e0613050907410a14040605090102010b091b0702040906050f18070605120703021204200109050f0906010903080313030e0105120c0d0902120607020d0507050601061d0405040501 79
    0x551386464000c8240c920726440e10b80f0580850a42c00346601c1a52045004200e8030b030a2021422681071520071100d81c4e03142004603000401c070b03411501804940c0c130240c00a0164003080c130140107c03c1001c0341c01400c80340d40e980301030700e016403204010511140040e1021803540295116801500c07400d0780c0b100e1032166541c0400c400c00201c000e5645000065902401d905454494000c0c02c2d070140f940b031800710288280101b1041400307981118944d00745184c0010ba90310301030900c01214206500201e041075041140742403075611035000302090340d40050070803c0b001028810701c10621401483e440c140304d450400800801e0080000d14460062580c0b201c0102440d842c0080082004e150120305001d03090041101c9440c0c14001603503c0310403500d01d1a2107079404065440a4100400007a40000f070700c2c040141c1850011641503c00c2d2029002c170b510a9880d081c00711154420500080d1507a003043c001880b1a0703110380328401d01501c8802241300c00101c654001405c85a0688049070280e64410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 278839478 1250 278838228 278838257
    0x6140f120a0509060c040b030a060302030f0a0501050a151412120903010b0105031302040f062c091c14070c080a0309051909050c0d050408131202010e0613050907 71
    0xd460b90002800c0d01400203420071085c1d00440d0300407402808403650740400020742842050380a8402590000c044442c440001031009480701d103460015070703442d42400c0006561100324003a4504406500808810b41450684c0a0310240341c9601110303405120740210081c110700401410010903284d00580c0d43c0c401e1888105802c4440c44c801da1814040180700704444104140c410603041078041c2e4012484220201d041c0e4000e19940d0081d8883c0c5142f042042115121407483c024410740072000c28a181c0c0b185070960383d0b00c411034a111468041c80100400215200e0302c5100b1b441c4071031204044c1401190350714489a404203800511240e0f10007041c4905146c1c0c040070080c010700007075821900f9000000c260301045401303801410b03221078035480825200d9200001301c0d028040c50b100304001504082c544240710340e0120b4202c84000e80a0000440c0010341ca002c21301c10741e0f030705840b400c0e00050210144070329904000184510b200d03800ca40052141c440603100c0e80f050389640d07a607400143c80b08 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 278840728 1250 278839478 278839481
    0x1201110c0d0e040c0c020108130503160605150901051201020903030a0e030c010f120b1804031106010812030406110702040f020c190c0512160e070809150106140f120a 73
    0x540c4200d02c207500700041d084d04190020358200c001d40d02031030079070456500c1e417199254883c0c1810001344544400250300c00782240342500c494411744900c0d01806107071078820300d8400c034140d1030200f00c2d8021484e03001004145840345c52040307200c0500c00003608208007480041c1c00c640140c8421004101015801912442d0a0000d180154400d081c090502c0341e10002c010201d108440c1350480701a582c0340c421a00f9602c09070051034405c400745030f124861030b042c5402402c0c14038800442943e13100c6c10002241d402070114030b400f44001d10390400c0707042d036445456400140c0500d141404c6289420442e440c05070b12240540500c00d9194800035a840d0000070641d8030301000110480c1c060203003c480440019120b6002200319001266001146801132100d9800c200c1603814220540200d081d00090100d05450140d01c03c5496444e014550313582c1001087d00e42194202981c660200c030001400f080340135001001c00030401c42c0382241041191060702010f58402c0000b00700c1070b44500b040280c602c10b103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 278841978 1250 278840728 278840747
    0x30090108042109053d1704080d1404052a09040b04120e03120904020405090a0501030218060102031b0f01020c1005010b07150c0c020409060203041109060d021201110c0d 74
    0x8458480d43c0c00c0b0b08044a0307007201c0e00110300d007042d10611030304c00900541b00d0002d00c0c003e004241c8017080c450070249401c004540c0000743c9090142d080c400c018500121058101e0303c1190000b000c2c0c8824094008806450360300c005090b1004010034001403926141c0043c042d100b0782c4a210010030a04180c100040c0300099803203004c08002100340089120344000c00c81b41c11a2a850351082d80b2010701d280018040d0040350080c07508901020208020740001d07070070244c100c074025500c200c40c40f200421912000c01040315842c2c0540c1c8200a0300140c51a203032640000d0302025816100ca0b151404d68150a980c004c582c0b200150b0b115080001d606c030141c0c820613005000040c0640c0c504501c1e503030350f44800a14030040f00c5405580700c00300b1a115001e15508200c8540c0104100400c6490346032220082d001a24250343e000c214003800009400d19000030360080e6070007490313604110600c0c0d007000358400c01019026055500c0e00540302c4e901d901c10018211b080c0144014158403009548014a010301 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 278843228 1250 278841978 278842009
    0x26010b070b060f0a0b1b0f1b1512040f06020a020102070203190506010e0903040f0b0403030e0f0a09110f07061e060308041802070f053009010804210905 67
    0x20300f00103001550310080c89500303e07800201ca1513140c0ea00c1d03c00c010503411114184076000d02541e40c0720480210007048603c09980d900c4500f404031507203d810302151802d13002d41c40d0384c1044200100c4000c0d14565010035403052240150103506100e5030348a4003a0307000fa10700003026039004200002145018405c508a483c22411810f01d0101591034080d694881031240320301c65a24880811a032850900803100074108085841070020f507a86035140881d4403d100940c0040c3c040407071000700d482c1c402d0b290001e443c4014945103000b418000e860004214000342402d80682c104003900d070445404010b807205c00d0094a00040c02d182000d12084520385c0c8004000d100c1d4984141800010060426102603560308003a5400000800a00c0002485801e17806840050032003030742000c005001800210003450b200c801d05201040c1c0003c5070013100c890794000403140c41808285019441000703000d80c0903001d00c40c003842c0d0b0428043e14426004850800c40000350114106100324103008030303500710f0102c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 278844478 1250 278843228 278843239
    0x200f160f0501051806070c150f030f0506030a0b0c090d0c06020c030f0312070e0303030a1509020906030a20030403080105030d05031302010e04061d0a0e06040c030326010b070b06 78
    0x403076141310802c0c4a030700c50300c40d900c52100801c81e803003403242500350100501038141a1941a81e620b01c805007510029a48040001c0d0800e180c03c402e0030700307601444d40200405001884054410b0381d03002c1104000038901d400d00c14040c4600303511986d40d40c0c1000d2110f40a81181e801c45401e290f4003d08060303080e19003d000341d02c8003905c201c1402002040380d140c403a1003e26021103482d0948200c406001d5840070b9585032201100717211120456034424a03ca9031101d005a096964444800d0142e00414201a0b070141042c00081c801810315000b5001a0313070801d4010380a248607810b190001d0304103441c1500011040d10050009080c02c1040c2058540c003428850305624201ca40f112603a0342c00400241000b003018054055910380b0f4005034040d20b29103400482181c42c80803004040d8030121144c05049080c1040750b2542500450351034040c54124107060413040c02c540b42034440c0c03901d0400c2c0103a90310074035000450010048241c24064200c8217459a515086030615140740c1001030b00c0d8a103c7c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 278845728 1250 278844478 278844487
    0x903220f09060f0b0304080405040203070302030a060f0501050f0903010204050a06170a11180117090a0c0e1e04030c02060409061d07080106110a1a0910020a200f160f050105 76
    0x104201c1c0f0b40011074224100c456501d0344e0720314001c1494080e81d40910f030000c0c0080240000640c00da000341d441071008400821555645810f0034110000501c1014042503040002990f8085204020a40f41e080600090b11b0556100f0108a90032003e03071050001840340088520070000b1416055040032040030140700c80c5580455503101441804007512008140d6012900a64001c031050905002428194041c91502d04141d54441c60541401c850502c1e1400d4003103200340105c40220700820b030340d21006281c1d01e885440b8001000c0068030070340600410521180069171010f000304060b0030032940c01700b500b901e0035414201c21040c210308c0c82610b2011034100403e1b50344c800100b504403030040c502800d61640c0303080d2a9081225048014040e5108600044152010440a14020715001c0202d0b1880d400c10640c0c941240a007242c8000003444036801c090714040c0c0130041000000300742c0d00742d60f03202c43c1c00c038075507481d02e00c40e404c5220040c040380c40200445003040e104180140801c0c04d2842c0b42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 278846978 1250 278845728 278845739
    0x206060a091a1513060c0b0a0e030d0e071406090d0b1801060b0304021207080d05130e071d120a1b051509030d0c1a0903220f0906 57
    0x40c0e00c414041c281d51182c0d54a50100b40301042032480308810703005058980c0c2c45005141c00400d55108440c04413403001c2c84100040e19520401d001968140c020304101d0710350300e0300c0c111030000e4441012507011601c07040c081c01120804034032030134011010880090a02c285083d83d002c544c1c907054418588074280510050307559807281031850001c035a010b80310710382c9641c0759040d4004043c0c0e070710700d004915031801c1000f20f1110603c0c0c0055004600071240300c5010f014045143c2d0765040c0500070551680c110b1a16a1a03050040707020313101500c04d9100c0400d04940300c030042402c401013155030341c00052005c6641c0707100f1601c002000d8603110058031103e0030b60f031503650400d60f01c903400c0100405d81403185004030170680340e00b54900041d0800503e1052500d04a409111554000e40d501a1003805107080c0c550f54107006095503040706038000c03c08a411030300041406d0400380010135080712800f0400c6490b4407804600ca060440803d2005008061810142c0c961515011500441c06d0145069001e004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 278848228 1250 278846978 278846989
    0xb06161101050d0609050a15031502090102100e01050f0108060108030a2f15010b18010c0c03060e030a030f020307210204030b040c0905070e09070f210207030807020606 74
    0x2005904005401441012000121040d114990040246a1514501096104007138001030700402c0703d5034041c4071b00b080d000900c0c40710250318400200015000602e2801070905034014114040050040d2840001242014002d44011800c104820307551101007040501c0a25219070241c490b04008010035030404000079560300c5525600024130580700100e9400032403451501c095046100e2042d41581a074070055556840b445403002100301c14100080369005220b01901c1060030715000580d100900760005440c0050684425100306902e080c000c8085081c1d4003950008070000030080d80d4a60980c10b0082c101c0e041c0c01200a056070040044c0400c1940c02006412000912002d550010104c00c1d4824001c1c0305542c070041028806408010521a440368040f0407618441c1c02845240d031589421035514110582075540042c10001081846110f80955208020182088c0700c4040d08120300d001d150780e4400d00c200c2c9854000503c2c0303007050307404045150011400c7c0000c1c010350031310600040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 278849478 1250 278848228 278848267
    0x312020a053a1707030b030d080a090209010e1b120103080f071202010b0a1508151507080a02010b090c030105091e160306050a03081204080c0f100b06 66
    0xd0004282400d1880600c0b11001d00126540e4420742248040c000202c0980074aa00090484048500c10b0001d0581d0307000303014101e911a00100608007024034028155403048000e040d2000455071024a0b00050311580c10a50103012400c8070120701c0c0c50004001001d214082d1a1101c80220a02c2004281c400201405055030f920601ea95101c6120b0072642c03405000745000505070100c021000c5403200d03019800171444d4102a42c041a0f219100c1942140b5100604228030016210800268501c00c00100c40303508514024100f141300011044020456042010191510304c0c002a00345c0c8950f40900c07421100c404103403810002860880c000d00701da800140300e040e01880c5944000b4050500200107002c0314140490b03020990704025805042d2030110b00d00d80301c0403d02e4200081120314103220768000700c0c0e034055001441c001d0718074880d40720450003a000300c03408842030103e40c00c82182441080500c80340e40d001003812900500f100700540798800c40e41070082c6000c000f0203100015200108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 278850728 1250 278849478 278849503
    0x1209060306040203041119150c11010e030c121005090706120906181203060801180818041d1501060806040203090a121d10020a03080903070b01030b010312020a05 71
    0x144c40340d5031800c165401c200400d010592111241002c0a51166111100703020f0340d0300400282c44003040c1c03080540d0328400c04000542100d031048011000b82d0300c00c000441d041c40bc0038042d01d880c00c0d96940810811503c6082e541180d8104083c8284c5040c0759202d40d66105081c10014011a403601d00082e00c0c10740320781c00704481c01d522241080144030244e00402c60252a140310318880440c0c80c00e103c5008200e1440c1030000a00f440d0002401420501507212000043c0e4090340c41d096195445007815444050107c900070f464110103813040e5502c4c801d013001c0d4420030025014408951002508001004511508404141005000c4260300115095100b00103903801603030303130b1034180741d89292200341309004011161035a04038000d13951160101114004c05c18485904481c84010020802100940e102c01640085202030200b4403c102440d0040641c030240c2c2e207800515241c4050200342600b00383c50518919004208001141c124420410450b10242240e001e50b50b41d41d46e04d070207580c0000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 278851978 1250 278850728 278850731
    0x110f160e040311150105030f010b1c050f0609010203040309060804080403021e1f030f05010305060a150b070602090a06020c0906060c0f01180218190507140a020f120906030604 77
    0x7804160103a00031400b901c2c60750088501902141421103400c0d00c0c24003a55001e4098080b800f440b26505014100c04505c005111101480d1441c0c0b00c88107507480c0b0f200503959880781000c6410842400c0c450113003e115100000b680d2864181000340044005510140403c250b580170400810554016101520360495915000b032195001c080d0b00141d48010b444ea0060b807045e201001c090f00c131001055448103540b000c0c00203c01c1401800c00b00c4009100151058011600040002030350f5804440400d80d074540e603004c00d90b110502d10382c050304808001c540c520b0b40080d126480d40b4000c0d41100c0148400d10040660041070700200e41d1b81000a8a100e0103500b000c1039142d100d100600c002005060714200810404c9845081b6220050b11120184e01605903079500009041300c2041c0c043c07254860781c82c50240c03072515041030002804000e1202c41000840d000806030201d18030002d010320b02d01e96008010b0001d070451010b0520b04000500b00511008108265154691030240d0741c0c8040708440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 278853228 1250 278851978 278851981
    0x60f07030207170c01060f080307020102060604020310030b01060503091b010f0c0606180504060506010801050306040b060406030f120306060e1e04180b090601080d0824040507110f160e 81
    0x10521940032022038064980800851104d200060540c030480803210b142c502e643c0100da4030420191a403086540203801a00000000340390740c14260011908168840b900351841d965039250542c91201c2030300300c040010300c000103108040200700303d981d2041c000c41c265000340c04480c2c40040c110147c041d80c0c0b4424000014090018007405a1082c401040c00c0303e406607000b02941d81c200f004000c00c960444050b4a0400800c001c2d5106845684c16103002800070032054842d034550000c8920300610b101d9010b41c0311131001c000144c0001c0b801ca241b1b441042d07107907000300d00104064140c40203604080c2c1081180b000e409030555a110380183d50400d0440040442c011250109000c0c2c500c1455000402c4170010840301008038018016100320650410b071146070b42c0ba14141a00d6010094042c400110100e0114034102e20070940d01c0070b0f00c2030301c14044209902020200d003c0d949c0813130725000032480d140c0c25004510b0040c49144002c01407000900030a030681008007101007050b0098240031980c100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 278854478 1250 278853228 278853233
    0xe0a030b040501110c010b2812050106210b0601030b220e07060f0215040201080609060616060b0a080a0b0f0c0706020c030405210705010302030601021609061502060f07030207 77
    0x522403421445122809036541308221707402800303040c4556449004410011400109400c46550080c107403101c0c0302c0d2500c0e00703840c0c03601081140142d0300003034415550b00c0000060b0035501c00140c01100060261001c143c4082e4284003481c1c9400811150515050103156010740ea41c0d0f1210445d00003108081182d030100b002c441400525150458000510810300c0c0480d845030894403c6203142c910758200c1c0c010b885581020101c446081d10000e01203950540411070780d00e04840c0e29a400f4801601d000e0502190800303c1036414901c501c15164143d5421051203181044a15072019010f600d00500c0584030315a28070304c16000040640c01d0301e44400011500d201584c004503603100b41c00a00640d00d8044420145480b54070901c2840d22a030007400c056210851016115072142c40e1031700c040c0807010715182c01900603520081c8058114041c40150071901c1c80750741c0380d000261102c00b0000400380d05000c01a06c3c14288412407000713661205c010000300b41c0c55000d045c7c5d03000440c4c1c0f80c0561101e1003032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 278855728 1250 278854478 278854481
    0x20315090c011119151d071a0c030307210911031b030a020907030e03030c04060801050a2403020d111201060513090902010507080a0e03060106030209060f0f040504021c0c0e0a030b040501 82
    0xc4694005d1410f03c0140100c000c1e000840301c00323a07641026404044484042c40e80d10f20b21900c00c201c07209410510002e0085030249103814840d044580b50a030910303a22221850484182c42012224110f040580e101c4500f41040b05601d105c03503160700034078042919400a682c3c0c0c00359000081c491007500000a800510a801c0840c0c140d0070441200d840c0e08004a08403400e8000e40143d000013185038000040c540713448a81481111403440c1c1e0422030030702c00110a080300b00d001000d441803540030084a0001103652080c20701d4186c904d060326841d2200e55011071089403069100008100c0140900c1c1e2107844001e2110040b1083d8442c0010080c10b90310059816001d1010040d14040300441c07005446030700a01e41900d134017803c4050322056a01d03a10150101e0140329030716500001e06000101c40000d40c4c4004000c045101007685080034bd5482c0003030103aa000d4641c05601143da0b95403040703030340b40b00d001d107444028241c10701441262026021500700d0f80d551001812141f0840c0104051050a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 278856978 1250 278855728 278855741
    0x130206070f020a0e0702010b0108070801170c100e011b030e12100c110c030a171803030f0405030601140d0b04030e0a260319050304020315090c01111915 67
    0x141c912030f0595a078103141d8052000c05c550050255003419141e000c00d40c0324001e83c1c4e00c10822900e425103580d00b8002c8155884038407000c2d4000600c0b50310b619010940e10f0100c24041c10019545140d00c1480480004022030b0314035000e891070040800945000035040707581e00242040a84890800004400701d15140041100c20416040e1400301811003080e8000400c800218981044a1550b02d40f402410365818075a903000c3c261380c5d82c5801d100e081110300300080031690b400e107081c00c6005010500290442d800a802845442000202000f1a0a0911195006140200160201c401003030041030003000c0001d802072011254000040405008803016034550038040c00e19980e441d00d5106062446290380031880c40505420200048a00000b044074004a0030ba101401c40312400941070b5000e40020f0b004a0381405000e4081c0010100e41c0040e0384260709a0005000130517640e00050508802c0444804940d00810002c100c0c245900740c0c039520440d0712030300b01d41a20340600c40c6007008041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 278858228 1250 278856978 278856983
    0xf060203030c0d0e030f0f1b03120a02090d0813030b01170c010e0a0b0706090309080307051b0307080d02061015210e01060806060301111303033510060206130206070f 73
    0x4011a41540f00c1900b04c3c040c116078800c8c41490f0801c12480d0f00400c0e6079014031124104110140f0f030000c1c18805094020b4041d0180241c00c8180e0460300e5a252a05500003082c115030001603107004005002103809054010b103c55200030b1322200340e0f0711180b030326010300427101414844181d40f00d003165120301199000508003901c42d01d0b1901850700c1d00700c010b00000031041d40015080030300402c07580d40200440d4803541d4814005c01511010349040615040701d0407405a143c014918005102001448405c403d090705a024002c1450100000300030000542c003d1540320090350901c0c0c618036000110200d06100c2089a01003c46028003008080d00990038100313010350034248000340400001403564011072084000344588810745550940354095100350b64084020004d003040400c0c000e2800803a50514606010000708000c0302032550046129410702800c03035082d0810101403901076402026007402c0c03015101c01e041c96640d0340c20005601c580a84601c400042040401c0b1480720302018007503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 278859478 1250 278858228 278858257
    0x708100e04050102190203030c04050d0c0504140a060b04030c180f1b0318120f050c060f070f02060903030606090f0301051f090b1e0d0501150f060203030c0d0e03 71
    0x140c10b1a25a01075040f42c146000c140b064410003003c65800801500e01c1803411408150078503103040c2c00c20410420700ca9096580030b01082d00400c0c503880760700a0000003172200c44140201d0030300f110700c2c81c1103a896500004564409200a00000721601d4040e4110344481070311403501c042d0101110700403c030240c503402c00640340100200110075640d031b01c40152150703500d0800110b180a07031900494500c0030401031402c200148100741c4607015514500307880d5281d241a605002c50821750900d801d00030344680210959000c06c000c0000d500910b01c0c00361902c180b010b021942410142c03582d40707000241030355108800c00314001440340c4441300300d02d0110800800a00280c144190801c40700001e0505040748400d0052010420071860b0203005c180010151001c03002e02e0021200d5219848544410b50b4050340c01c6500c031000c0740090050155859144159481da28900085614014295030154007035420520810550030010810703906495110407000c034032902240c9800b0704500c141c101d080c8480c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 278860728 1250 278859478 278859481
    0x50301180c050910020f150114010c080f03070c1e060b010e0d060e100906052203090618030b15030f160e04020109081207150b0f0d05030415050c0607030c080708100e 73
    0x2081070720185048510511842c089d2001c01401160200c5250070040c180c9181088215620946000110740c040c502d40b500b04000330040d030341d54410081c1100c1c40010041303d08500001d00c2103500c01e40041c401c0c00d0900ca03050b088610041000d84040000281c0f00300c0e602c00503120400301c03e0080100701c08940b90200b20f5001c0c50325024005010a4034140100d1003502002c0e1800075035142420401601500d80c0c0c0c051518003030b000c540840d01c4003600304c0101205480040013031410040280904c0c07805e00100040f5481d401414a40117510441c03c1e402e0b4406405102a1082e410000054031800e054400181d66140010394031040300c0c0c1d1107135544e072190410047c42c1d107640102503c035407446080c0300322180800b0182d00058580d101d4507140d02c00d40c040740c80107417440e001004c200040c0c810b001f564145a6502c40301e2240c60856500c11020840c00144011002010b110382c9070b0140550400f048240700c1c1410040030080001c00150a102d0402c2c00b007016050034541c080c000b4000001440703202d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 278861978 1250 278860728 278860753
    0x8010e0411150c191109040510051b07110108100b070f06020f070b040c050607080d050a1509140a060b0901080901021213120905030c0d030c06020a050301180c050910020f 75
    0x2404d1910740c1600d0301d101480340c043c810b182514015006540010052a1001d05103186800910b400303055094052102000b200c4041154805840703603500070070300e00b01c1d2100b920001521480e001060048519100b0300d051081c90340e064103803521540c00c8521070f1854100e51510500900c10b00c0054480c038000402d029042048091415104a1061758031504596440741030112030701400074014800c0c00700b8080000800300f154030255218441d40004200c200d00c5400c40080300e00990019010380340c90b00a1100801070b810042500214002c03801c200d090701d0690f0108180c020749030030328108526840031415510094058581c80b800b2030028411a08000c4010001800240002c1324198407010b84150500c8c0110968801c650004e0040c0600c6c1c40848100004001409401c45c144943d040011002c02d4072403000d07098501c9a5101e43d40c1d80c2d4100402c8880090101c1066850310f4141345d41003000a170b0100a071f4081038800e50707601c0c4690401440aa04012401140344001c0c440c40224041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 278863228 1250 278861978 278862013
    0x106051305011505070b132105090301060803070b040b040206120c0403020f040c0e131401080a0c050a031509150207050a0c150917070e011508010e0411150c 69
    0x1282c0f0310100f00061250140c2080e00c890040301000351200840800050008070b00c00744010790310b0b1241c010201080c80d03003000102c5d0202d41501c0c1380c00080e004030741c00309541000d100e80805405600c000b1410151559102c1c0324021000b800140105040404542151903034030554880494160307003184140f0700250406c05507009440160303c1504402807032165030400f03124880340145165203550303400d400d6070140100790001c94680480c0d41c0e600d2000c00c0c51418130b910102e028105800c080c1001110b00c2c102821100d441f03820080c13040511000800004510a410a8030201c2030030703010403104154201107110b20010802288120300000d00341e4100180070461a0146114030781503040d058490f15014240745401300520041807a00d0340c144101e4a40d5030892021860b000200c0300c0b0161032781e00a0712041070a83c40380c0841c901c400707060206140c2010505000d4008174903e045149425100e03024800884500107001d5400e1000c142440c41040c801c80c1c5d0000041c100304c450f0300860038510b88 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 278864478 1250 278863228 278863231
    0xd062a0807081b09040b031606020610050108010e07030e03130306020a03050c04060207121b0303020a060608030f03043011060105030a0206070803150d06060905070c150b01020106051305 82
    0x100060410000030f180c03210b01030b908500e000c0d40c070343d0b105040c03000f07480c18000200901c0115607410f00c200e042807034411250648180240005601604042c10011700c0c07aa01030311950040c0d8180840d00700148040b000864034a0380c131890074500400c00c400080303041030861198420300300300c01c001240301009019140d001010403078410b80d82000706030380d140501225030065000d403500503000705204000300c0c200314915514641c0074807400c6003641d900c0c410740c0c00f0f8114079074012809070700b080b541d02c01400000d10400c0010034408000d10300c2c21810b1040c2c0032145c07100920051800000000d21982180d11018000c082c002c400c1c4541c8010006c24006481003540c203500c440340e440b50500100d46410041620340312564007030031040c1080e000390b8503508941c00c01045a00001c1b5110454056580e49200810501d030181c40002a26401c06d0701c44030075207100a0400050082e503038000c40000d0721034103e4000c078249514002804084560040340500521740c40301e82d004011102d0701c82960819407155 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 278865728 1250 278864478 278864491
    0x61317120f0907080601050d020f03060f04021c050a080c010e0601090f0b01020705031b1206251806030c090b03160906090b18180702010504030905060403020d062a08 73
    0x145003030350300c00c1c510b02d580310990b00030740c01c65800c054010802030501e4035101203100d2008008030102032184012a18100f021210740640d0b4003c201480103504000328444614462200c502001d0800303a1101030b17442494040081902070300185480107800d00394001c008601c640c2c02606d405594501101d400703840c14020350007107a45030141c0b104583d8000183c4004a40d40500604002c050002c120720a048000d812940c1080f0007203030903103859406100d043d110f501600100074115802c4100c0400f001d44d1101c04009000182d00c1900101c69990380e80012070310645000314405080c148110b51081050344610036400011040c80030401d01040040c010301318070f5403020f4000e41e40b80001c0300c03001d2a07442001c0909004012003103c4848808145030703c80e1003c1d05003440c0f0802d404003841c100c0d00440301d140c0141d40d200280401c041d40005e94100810007241c1f40c608090841d000140c00c0c08007040002c2c1410354480100b0845188041c000b40035a2048401340d103103041000c0043c10440049511 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 278866978 1250 278865728 278865751
    0x1b05010b100314060409020d082d0309150a180809040f0507080103120e060a3c0c0c0e0103080301030b0a1b0c020d0804151d0306131712 60
    0x31001860710038403e5035010100104210426111041030100070559a0016030f04100d2104045010070314010042c8009641c0741c102d1102000e4010030b0b5003114551008841a8640c01c0040c800d91400c009501c0c0800460034169080c0e41d10740708042e0005090340400360415001c0072014400703220b8a1000740201c06005e0350103100e0042a00c00c1e500c1152002c031138181c08141a4401400030071440e80074039000f0081800c0405640744d031440041c4c0c00da0841c65080d000204d440050b81158a2401c2075071460052501604020301001040c00c031040c020114039400308221280c011003440a907694080003084025080e1070301d541c580c1041c81c85584240030645004541c50007064840c1c803103100b0851880c141f59540305c000300f00401e00f102c1c801140c28050f070f400400810a07801295421000f0300052940c941ca0310300c8500c00030400b4003040150440300c400303075492040c0c1e42000d88000ca14142d000d004240740321141c0c803840c50452032984d60511170003500080403c8080350102180c640d01e0052070006070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 278868228 1250 278866978 278866999
    0x1803070f06080f16081b1912091502090f040e0a050708160b0a020313081e0303060a270c0206100b0c0d0302030601200d081308030c09011b05010b 64
    0x1901400e12400350313440e021407040700844140f101d00c0f50803084c0e0090500c9050811000d1610b003030000c141c104800e03100d02a034a0402d04c0c1105504000c880410400624041c0b00401e039a88131803040c0903054035a0b08201d500010503d51968807070250394042d02c0000e10801ca1000b840380c8031959010040000c030307800d101d00e00010550b583d001900700c011a00c0f045c161202c40d42045988250f5410960507030081d88401d11036140e055041044a6002c0e055080003044286142c4428101c0001074140e5603603990000c1045c4070701c540b664905201521641314003400004143d4001c4550140c1640060110a1070303d040c02c0402503002c00d00324003d0b070030745142c403841c5503c40707101c4016481901011610365111408440714903000360042d6600c039405041c0600041c2c1c0c1d00031034074040e401880350300c035642d00b007412142581b5400c0b144c42c50304004401250480900b03a0ba5440703101c0c1c40040c212600742e410220340e102c41c0781c0c85502007822400590340706441811061030140c2c06080d4441e0f2403813240d003c851 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 278869478 1250 278868228 278868241
    0x6080a080d0518100b0604030605130501290d110310060e060618010c1106070303060314060705040b161e02010801060e0a060e0d08040605030114040204050a0b1803070f0608 76
    0x2503071a00c0103c4803102401a02c222a81030a00404107041a140c016505000000219130f441c410313103200304000e03620106003441c980340403030854041c468031940075045100c1e5040d4509040700d20010051040d240300c0125081410140c000d0891105035079498882c1000300c1c440482c468001408440c0007898403005900d0f01d0081122a01070410321a981802e5007501956640c440c4222160140c01440c1500495403040b010078041c1e4094403041e0042500c4170070400420001180340c0e142032283e2030140540d401d02c8140185203120350b10910ba6803200110720f01004041844036070310000c1d1705c80750101a03001000134103201c501701544e069000ca80c207140001a03a9010b02282140880c00404040005003005010b0700c400d442295800e41096401000e81d001600e440000e0000c0d29064a8281d202d41c5000b000d9180c03403038000c11042c0a68014001041951508000c0f01d05480d22690011789807000c9601c0d4408840c031011000b41c0c544504600000d003140c61807200c60545a141d80c9050707080d035030744 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 278870728 1250 278869478 278869501
    0x20709060506030c0304020f03030c0f06060f01020303040f11060d0c081302010e0607061805010506100203040506030406050a0f0c03061404090837170906150f030106080a080d05 78
    0x14840c0740e400500400015660030189401140e02a00c000d003030f106a5148040840d140d070b0400c0c02041d40f9584089000076401c442000001d0b840741c0201c4245400224240000791203000c0540014211003040324518200f110382c0d2a24428008050400c60b00c401c01d8411807005000e18020b042c010903a5580801c4120344010721500101e50103840d00210340b0302c40c1007072042aa21030300c004d0f103886a90f15800720410016203120b520182c080c00022800e800d1074403c0201d0910540084015940200002c00c0b4645420382a241d000e500100001002d0b52000e40e600081c182c4084154106850300020049003074141d40f00c4404d0711800c245d094190042c00052204071206190080c0c00b540e0140203442410345a01507401d0740e03101a48003118041c007440b02c40d81c48828401ca91401140603195141c20414540c3d00c043e612540120060545007406e440d00f0345e1103103217034a4a40c040c0c034014070515095202508000c00a0201204440c059021410259202c1e00a1791000e59800d0034030003c206102e60a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 278871978 1250 278870728 278870741
    0xa0b060a06022a2206050306160210200c0a150207080f0702011808010504151b0c030e03070f08010c050703050d0b0f1002010c18141302040306020c0d020709 69
    0x2100790442c01c0d14120704060904902c1c190343d15840140c8024054640f18010b0300e4043c0d08101000c0495580e04084c109820100000c0ca0103004000380c10441e011203a00088554080d8109140011865500340581044500d024004400300c040011402040d030310005540311124060030a1114103a20310340d801040e0b1140c004082c01c1c003841801001e403408640f4008280d000d105061200d002c424203030002d15000e0b003035400a07880b80d54420070071051025140001fa8490411031040140d02140c03c1c1e1225540800d0207140d08000c100c0000d2010107002e20414042140000d0803030325210f589110103141f0486a026020180d400d10007c115810f01a0069684055140e180c103030900c2c40f004009001403600c40d0400703600c125031b0800321003503407600c501c05048100039900108140096290252010044258101c071510f0000340801c5058001c00c0c0709c134074507403013243e0340d0034002ba01c080840061300640d000545224400a81003407074010000d070007020490a902503600c00c540e0b451044040340c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 278873228 1250 278871978 278872003
    0x2060f0907080d03020f0d05040c0e162a080d021305090f0414210d0b0a0b0904020c0a0813060210020c2d1c091205071e080a0b060a0602 60
    0x11120f618805402900030389808540c20300d5250038402003941c3e0300c0940d04240e038280c422500004040c000e40900401c00c6900400354824840030002c2c03400c00034410284a21034141041c41d50701c0d40c008880d07100146911443c0c0058006483e07481180e202c200940c03080d030320a0f002035450703000002e0b5030030002c0f04540300d1041c0708051001c0b5511511030000414086080d6103032406454814500704c0d0700140d015801b00c1180001035114180b0b449602d084a400600161017000000401c00584034410202d409007003060b140561154000c4210501d480860340c0c2c0180702c040007103140c24003200e880400c0001c4402c558200c1e4001e003200300740481207101c1c0c0340d0525010f8000d980e03205440c0b031554060511008814403d9901c09820411950500b40f146c1c7c511985424030345801101260b020b402100a0001d882074004000c0c55035a4543d5640d01c03920540060441c4030721403159021001c2c1116000f030944034182d8640e1101880c1003100380c0d0046860911400640c400451a61302c00205c0b4000d07a903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 278874478 1250 278873228 278873233
    0x6050319061d0d080f060d051e070315020c010617071401050f03090723010503040b071b0501051e01030506060918070e01050f030a1211070e0702060f090708 69
    0x1140d48821002e8403959001d400c2a2074001d4804503004030421540214804135a56440f00c0e0500c4500c018081030040e00040c425040305501c07102181006c20b003080f10030a000b401c1030140c41d0210b83c903810f0400e00d60010300a103084440040d480c44880c3c005020241c8030358000c011494451142c685501c030040d0340400300d6400841c00780110000d105941c001744005041040c1081d484100844455008a842d0301ca035802c48041081005421880142e864035000540718120850f000024524000200007400d0411050040380c0340c640a020180b04000002100030f1f0380304120708003d40682415203040404c1070704650981103062411810358142c9500c030b0081c008a0701e45d0020060f44690281c244c1d401140340d000e42c1010305400b00440380042c8a000540c078040d6240c54104001d450032042c0702030198200d04440800142185809841000c407414001046010303d18510715080c8150050510f81c0f040700140401ca03500002d1280c0301d480c003500d9020b20303a0303100c0c90300d55203e1850344203880072030303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 278875728 1250 278874478 278874523
    0xa050301030f021305070c030f020d0c2a0b21040b04020609030c03060a0608060c04061e0c052e0606080a02160b0c03011719020114090d110301060503 66
    0x303640b0201d90155036000408008095211543e5001160416503900001c03c0e41207031000101500324003e200d03000c40600107429031030071a400c040c1181d0501071000740a000c055400410b0724002c0f44003400c624203080d5450703070342070f0702c83c030012406900844c640c042000311864074203045c80000c1c0c56603108a5000c900414543c4481d400d1001d5030f000190841c0d0b141c004c0701c3e40d0942c152000c000c1248248030a00c0c1c045102480c1c101d5260034010080c00346801c0e80f07010041844040d4203c2c003c411144020039400c50340f04c001410444103104a04001031850040a02c2c41040c08203561550343d800d001c0b0001010004091006030b07089404600c2500049241940080c1c1131004c01e90107412890b1441c240211248590340c1c078840c42d846c0443c0c2d1003444000100045c4502803840000390260a1104020604410841000c0d003a4968818009040046d280e00f002c40070804601540c1c1d90a0000d015580c1d0200e6a140080900d41c42c07000a6000750300c1e000c00000d052400080100d490f840082154844 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 278876978 1250 278875728 278875733
    0x9051b03120f0d1b09081203070c02011b0803010e0106171911040b1908040309051306091b020d0903020904020f2407020a06031413052a0a05060a05030103 68
    0x36000b03050240140c2c002401074860718401c50113091507680070301d00c0603121300400c1c510103000060640c005a00326403104a224840e800c41c6411a50080d030750303040c0443c000081d840101e541030020f10701c90302025a11100c6a04010302230002d0341c140d840c00304402d8034680e03c0d10070172280b2a840003002044004424003182d0100003103000c3c01415280c241c40480c00e100c0d407600010709940103611090a0f0b0340300040a0701c07911f2524000e420f079074205241c50340190505d610000d11038101c03801500d1160aa28511040400380c0358021001001408401c1c040140d4042c810040b00e14240c0c61b42025002d0a5008072055100f81c0181302030b680d00400f0030606440d642c00740043c02c2c42c03408500b44c005005c080d04010000c014a403072401c0e052544a9160785003864414810500c01c0b943c080d41c1810300b8200007e100302c1c0e00c00c441c1c680c407005d098a81c0740380000350b041152500e0a030300c800c0c3c201c250000708003840e00c013254030000c030401106070b41d00c80b02c2580e1072080c81524850342d01c220b0001001440180300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 278878228 1250 278876978 278877013
    0xd140c0703081021060c090b030106260915060a081b04110301121e120e1305070207050301061e06050a090e01180b09010b091c050304030609051b03 65
    0x10050002c003140d01d0503a131501809020154103800280d00e42001c61a0340c001c100c2140981001c0d03143d40d00c0e000e80000c2c64040d00c131450b4007041c0101c80500074803040000c040030141070346800105000303034800c0003030030702210031074858400f0002d500c1082030150010f54a0305082c980b03582142c9551004000d0111050f04440d001c1e00d020074540c0d03201c0c1d241c0000d000030300380030f0380603502030501d0540582050049141c1801550580f0460082e0b2594040ca04004114098454400c24a49003028480d07103500701c000800c80a01484902e886a25210600226030b80c0010000e003511410fa00800c00c1e10b845e03000c1c0c080c9084401a00c0903103802190002d201d40382c8030300c000d020001542c2c08d240c2100b940341d000e40741c00840c090300420382c602c0d05102c80b4842d64260740550982c07110140c40700005941007040c0e9040394801c0c449024020f00f4036544100480c40304c2c0b04481003080c1c002050f6070715541c4900e0580044d2400c480142c80c144209028902c2a080d100112064140d00400405058812448004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 278879478 1250 278878228 278878231
    0xb100f02060106032304050f071e03020d1406150f190b070804080105150f0123030c12161812060908091c060c051c0b12120d140c070308 60
    0x94001400d040c0b10001052000c000c170f40210b102e90302500f206a400c0384454604041580320308a110611001c03c0440310b40d01400b01c0c15a50151001d100d8600f141c104401000e0200903024080d00c81c41080000602440380c2102d004801107903151210030f402401c0003400e4600c90b500c0d440560b40014100720003218031008145461082000f41d00b0f0a036034801c15400c58004031020782c480c1c060700054808600d04036500448411013401d01c500485004421560600d20000030443c16107000008500c80003141c00503030700b105202c00c005140c0ca1811079012800e2500030404000810300790030b0740031600c2c1c13180811003054072106070804000710259103818014244040080c3d941c280100940140c0d9100c020b1004428a45c00308400300f100030606c2e0440031182001002c07010842c02348115800c03400d5180f0b100740c90f88424000810114810310002d200069011440301d00d5220b40c04000404908500140400d598000380c2008011280c481c001c0507a0821102e55052040c03c02034100040d0045c104107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 278880728 1250 278879478 278879501
    0x105040b0f0306040f020a090c0522090207050c091302030a080708040302122407020a0620130305060a050f040b040512030702101a0a05060a210b100f0206010603 71
    0x4569000030000300f070908400780c03000d0b200650100c00500a5060002c696002000c4900b0100515000302c58001c05038000e014405400e50000d0f24034010f96444401d680380a4030000b0b000319500c040d240341c4a80e0320700c0f0000120b030191106200213803802d1003d140e644109500078001e0195400682c0d5039411079441403c1c200c0344407205120200250f1079582e501d203945d50854009003c00c400b891a0802401c5110481c41010020f40003008000390380450341c1c2081b01c0d0307c990007041d50280c011860100045034820520910804180b1034070084080c45010102d0b80110151010398841c002d040b410743d0b901300c5050003d0304040e004240043d85110840c0d41c058001c0066540d441508102d92a10764400d80d91040140d100401404103030210707105102c00341c01d0803070111406030358010200d104298140320700d6125140100320002514021250b040c5a020b40120f007001d4001c0800f24207005182e00c220301802802c0070070205006a0060150441c039802d5030f00180780c16031800504401501040030b45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 278881978 1250 278880728 278880739
    0x3050703110d0302120a2c0a0803070503060a080307030807080604091202011b0c05100c14040f09051302010903060b010203070203031c1503081c09021305190209090105040b 76
    0xc25108181800142d807042e45540d000b5075650011400d084100f0006444107038558a0240c824501d89000f08500190381e41c000307441c03404801c0b140320701c9080c000f0348a009001950000200400d29620800851003000200c0700c0d16903080e1194031a176540c0c00782c2c010007000b103013114010800305402078550950100d801800461120a0390742c4410f0096101c1d0f480740c2c0941c0d1185d40c0000c00000b001603415024501e4686862000315588a03d56201d005a08024000d81c0d6110501205403069442d000d440400c014640d0342d42c1c2d55040342d030340b02070f03580d2003103440046c5880081603a0b01c078240c0c03c03420402d130140e6070019140d0460700c07804002c016005c1d00300c0c150f210402a603c0180c400380003900b06240880c01038a030a8004000035803e5a03510300b40903c600902000c1400000c52120944801d4803104c1901501d0345042c5a0072401000c111b140a980039180d01c1c1640001d40d500e4020b83d100d800030140401c440b41007404e648040e402007102c9940c0c0504440300510003030405500c84143c0540003040c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 278883228 1250 278881978 278881997
    0xf0c22090207120e060c1e01140708040b070e0108070e04020c0d030b10090302060d051e1f05033f031303170f043302040614040305070303050703 64
    0x200304200e03070007118122a14800368800d0540d0503040b4511400c0d14100f911894a410b4107000c0301500d0704c59401b80c1e0b5585441106034080c443c0c2c000d50144080d400c03036181107182820604005042c403402241c04803101c214400004040c07070701c80c0f550070030b0760001078580110a483c0c2034400d1302d00400c00800503821a0782480078191005007080005945116910001003404502d001d200e8101c0b640800f04c07003804181c100810040c0c80710000c541c2070124502000405440700007150300711865400d05c1c1c482005201c410300280d20220041d2b448524030a9941c4a40281e41d40140360701d94016548003c0302d142c22915132885520030801e0310050400d050301600310803124400b080140c0d0001d5400c01140f1507691084010140c002c46141103903800414045214548204103103001c0300c000308028040b0154201e08589201d0400e20601c2041000052042081d80c1040b180029002407103030000190b000368074500303e0010902164140c81e004006031200740e04548007500c20350312209040b010442e0414 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 278884478 1250 278883228 278883239
    0xc04051f1713050f0109240204051e120601051c050f010c0f020706080c0f1c1e060509090d0f090b0406020a030e040b09040201080a0f0213050102060f0c22 68
    0x3140304080030242c0901100319800c240e8a010313119515503945a140c4410304020a02c801c0282c030351240203000880081d0a1030040384080d000b50380c4450303040414100c4520000d80301081084807098140e80398609048107807005980d4110070301c00c450300070300031a0894060b003038400c510540c420301030340481e8910041840345a017140d80640c501ea00248480840050310b55040c04204000c048501d0304110504061407202c2d614400c0d02c00360010414001601141d46001d550407041741981980100054982d0340c88024100b00700e4040c210a85151100c04102c47c68050034072809004404014444650304031020317a90250108048428410035201c00122005d13000020809080594043c01100205103009807280850f10300c0148958241262070640d40c07506a83c56610640920b01025213403500001c0d074006100d843d500a00f85400051a02411405a40c221702102c10a034202c42c3c459503041d0321030038100c0050760300d07010368103040103101440d83c0b510700c10408201c1500f0500c050156031700e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 278885728 1250 278884478 278884517
    0xb06040e16030507050a1e0501051c05130210050c031206030a0f0510051003020d060507231209060705070b0c0409061403010f0b010203070204090f060c12050c04051f 73
    0x1079104a483e50b102c01410f106a00301295a00000e00c000e000c01200302d490700740c05005410b045d000341810020040303412201c6c04c185400003000070007029004c101905042c20841104001011f00307a01a04c0312240d504250751042045501d05918803020b1401c3c401100c1d5007000d500d502802c032903854850385020401041000b400181c00d02e110304002d0002c0410b405000082e40c40080440c6500038140c0b00400c0584c41e000d2a07018000d9100700c0c00625656141030944030003400d04002c40415001c2203021001ca00140002e0202443e80340c001e4900b50f0740c4141d8030f6078070b240c22100e4200288003405404006241c28480a42162641b000203041035100c100020448026500560391061410207900e44e0742400c0c0304a010003400f080d010300420300c0740070020b5540c3c840c000f402805940e176460181c040c0101c01d0902e032102503016100344464070702004001c103d01d2120500c010101e140c0350120b0f4040303a4020448080f10009840c680c554203811001c0341941420b144081d0510880004811f55030000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 278886978 1250 278885728 278885773
    0x30105070507060b010315060302130f09060e0a020906040e04170711040c08040302030a0f03020715020306100305060d0b1e09071401450e040209130b06040e 69
    0x140da9940d0311140302d82002c2090b2000c804920341494604082d5590716084002503038180c0300a130130056034418400805540c0713100158400b01e124001c14102250341030311900a88101d41400f85519515220414240101d115800301e0030307400035007000100701c402c0804038000d0b80603004903804580c012000581c04550303441401c00310f0b82c002d03980c1c440407120310303080c17041104082c4c0b103180a0125151a50b4044c2d0f0781e105070001d14061045003a052104c0a1081d0102e5003550347c00090024030484e80643d01c40a5002980c0180c4a00e40c2e81307500310f0040d4440d00c40c6038072034840213010704c2854246498016100d01c0180421654a419445601d41d034101c145101c0c3c080c5401070300400d40c10b0701e400c08041c866840c00b241c090400c81a0030a0b10712407040340c8050f0b00d00d100d075100d022110003504203804060201c05910781d000848007060022f2030040722500d440c4121300956000456540381a00310f0308050200303c004000d0942c4001088060400380c0c881121620810101c0d81400c54028925554504 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 278888228 1250 278886978 278886991
    0x7050a32240409110c0a08030604060b0403060f060803250c050405100807080a0c17070f140307120305120c0903030c01050414031612020a06060b0d1a011d060702030105 74
    0xc00160030440200d452181803c40c00413942501d0130f014a620010351100070048000d000c2c24004004901c0542c0c030366002d10300902c4444111903460341e0b240f800c400a0b000001025652610b4a44005042413000c0201c4003103080716206480300140d600c02d200c07000001054183d404201d850004505a00c561003403030f00507180580001c0146160166081c50f10b90150000b107690b81044030400300207000310030902d01761504000710003904031380340e00141c0c9006215884000f04031b1102c0d8000854410441700400001c50540c261001c0c5e644403100880e00882044008001800800074101508801d06025400c40e250152a034640029440000e1071a00800480c500a0359681c00340800c01c0007040118020000c44c0c0040c40c1884003000900080d8002c2000241c9444000b0102c0c03071f403561090010b54021a4455420810141c45c0c05440902e508a10079541456180c0f0310044038249202c1d210912501050b0f550404503072103050362105a8030f8401a080d00920f05100f0703440183d4003805a10311500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 278889478 1250 278888228 278888299
    0x307050c060a0c0c060f0908130e0c1603030b010e030106060201020408060f0f06010804060207060606080402010216150e0a090903260105091501110105040507050a32 73
    0x1081000001e040c6003026140300700d014901081040c5940d00250444510341c2c0285c000143d29160580000c09411020720040c20440001510400c03c80310300c0d800d03401d95003441040c410564454160b0005d42c4078a007052003c945903421304c0c1c0300080c42074209081110061400481c0600307403101007802e4401580202000d43d4002c2024400c40100300700083c1c2c00300e80c1e09501041420724005940c44030801400c007504015540300000c0512507190101c80c6d1a65002030200102d42d622000102010310650741240140130b040c5803100104d0310100041c06803005811481c440c1c948131101a07407444140e6001e140c00c0455003000086000051040c18801e500a0302c4888805000542a44a01c030a042d68900c521841c4801401292251030380c0685c88410f01c1c0140c0c0d0414080d60052317030401c54a000d07a10007582403404000c10048080f0303603242120b1055911a40b40354031220046080410000c1d0950071012000d1880b40c03540030111201c0c00d001d8007070142c003042d2440d101c010a84004583c2c2204401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 278890728 1250 278889478 278889487
    0x40b010905070c4e020102030606070303090f1e0309170d030c021e0d09171f02070b090a02010e01030b0306130f08040905010302011e0f030b040f02040e0f010f1d04031202030705 78
    0x4030407001da800910203580b0086148d49007283c0002e10b14040c0c60009401c25030b95224000401c11001000c00d0025045000000f00c5455800140c0305c4000b030301822400a9040c1c030b00016001000d0b042004031541d0300b00907003100c4a1501d011001000d0103401d9208500c58049400d80310a42c034441400385c0091500a400c0e690044107003e8481d0907a58066100b10302c9004030202d4407007000c91400b40e0300400401108945000c150142c01a000e55100508441d01c2082444800d0304002820a02c0c1032003a00c5110000003503400640482e03600301d20058060704500001250404400c20740001c1c03a11400040307d81c80004c0e10781c04400e070001e8000100c5240e031000103105542e00505030481c4101410394006800c110100018840000b144444041c1a10f030b46a0078041d980d95000300080c052820811506c0e01d40d6a0f64110340d404095400070401c680b2000045030044085020741e05844800802401d9452510703207884007000b004105034100580d5100100c0c602d00c00740000c1d802642c55a46290b00c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 278891978 1250 278890728 278890853
    0x18060801050f0603070b0a0e040e010e0106140d11150a11070506270409021e0a1401050307050705030c060f0708070f0e060d1e0203040b010905070c 65
    0x1c4070300c09000e0441c0124035000700500c40d50300184c0780c402c0d588a401d0f81600e564200358151180c1840d0781d13407030307034003174149545600006015804810340102090081c41415030307070040300c00da150b4015805908901485041004a5207042c0080c0172000c010b0500204603148002180b000d03000a100407000603500c4020b25480c4008200181c0a000226039075460005040581441c2106d400340074031890401024407003040ea0380340c1c0010364550300a05201c050311540b6695050300c1250245c41480744802e4240418405d480b6404004200b0042e181d880c5140c8a43c0c07019502034008850441c0c840c40100082e8115540c10311510307004d1034540c2c420000c64200282d000d0002d400040101c0300300280030281c140e58503841060440210020703a031556580c441c402c0190b000d009070b0301c80940c020004208020484042d6402503214900071624040e40341d8032000307008150380090740c22600040c08110b804020841c1401848501c0c031045030075600c4010100e10301c030050f88030b2094061400059504075580c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 278893228 1250 278891978 278891981
    0x130501080c0108150109060c02030a060606020303180a0206030c030c070c0603020315060a020a030503070c172104080d0225050c130603020a03060c022b0f03090b0414030418060801 79
    0x2c0061311801150130f00000c610000307280c180b01d48502070812030b4052862056403011b0119080b0260003000c140400703034841102940d04c0c0d000742d40310010100020700492604d10007156a80e0080e600030718152842d1141801840503400180008508007001c0228030300058403203a066009118580b00980c0301d143c0791521005134036131081110301401d01040617580c0039501003100039180b541402c1554072a00c5000c801c442c007440504004208654a00680b151310a0302c4c40586010060100155615004213200c1d10703c85000303a07402072401c0c005005420400d8030f1a005003200300720503805210031170710340340d0142d28000c001c1d10103aa4580240008242c5400c160311280030201c03240c0001d0101c240345602044101c0c5c400e1001400495858041107a964424014100120456281640002003101c11040c090031600d2004000c02e48201a180f003550003401000d4019802401400040d500c03600c1c2c00003400100e000f0740c4064042004003041c025003142030403c1e08246460006406420b1466250 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 278894478 1250 278893228 278893231
    0x60f091407030902031c11030423041401060815060d09060b060f0a03020306190602070f2103030c0c0206030106122304080703020c031002030a0b120c0f130501080c0108 74
    0x100305030600310301c3c0003d40c0300020240002400041d8010310882900b20440c1c50601d803008800090000040000d41300c8094240445060250896001d0708000c007000c01c01102d03049030114948000c2034004011290281d00d01c6a80030341d40000da2078045400400140c000d80c070440700080c0483c0d481d800036040c0241c41c40785402d41030090395103e107841e801d03140303055260181d4030780c0702c08141c0c00000051860300c030524502d00780c1e840c1c9142c0890950b110079010352502428040c100001c0c261310303030000c0c0140c1c00441080828000c189400c2144505450440141000c40d2440e028015840c1f00400161079080040d0300901131690b03003004411040d61240241d80ea820100011088180010a4910001c0c00b086401552004d443c680c0c80070f0520302a801e020780495059410702460121103c610040e400843c400c03d400242001107009045c1000b04550030115800516071040d0b00c2c6811604262100c40d610800090030041c2a650440d00882a580c00740c02c20001500040307684580365801041c1079 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 278895728 1250 278894478 278894491
    0xf110a0321090c0504110d0e0705271504020c0601080607030606030905070b03091018060507020109050c040518010501030609020307060206220611070309030506090c13050a060f0914 80
    0x14004500d254483d022418014080c0c80e100c1d954851504050140e203100302d640242d0486070034030204100199143c4c480d2424801c2d940a15640b400692006501c80707014005502040321007900c80c1c80710210302c0c20141c1a11505074000c2d50801c80c59a401000700308960003000200b0007404c0500e070000c0300074140d40280c2d02071000e06080002400000710040f42c120140c40316190815140e5039076800711807501c01c1c40710300c480b1010b02e00340c4000700d00c8580200e000c0b05070b4010b0700c003070280b5181e1020403070032190003030030146c4240c020b00115070300391405801550300306071138003204140211400600703030840d0002c0e03000b01c5103580d40e0800c0c03104500341402003130000d18860020b40003510b09580400c02d40da400000c071444403c50807428104000f240d5100c0c0d010107002d000000e844050618028042ca883c40c001960b80d445000e0000710007400001b2558800d02c0040c0400750200380003c2070801504001c0c00000c181c4d40c403140d000c40e24145003291903000b0007111001041c8000c001c1078440e0fa6040c0039201 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 278896978 1250 278895728 278895731
    0x50c010908100b1c0b04060b060a0e0405180111220b030408090303131409010906060512061c08030708060105090a140409022d0409030f0f110a0321 65
    0x208190700010560312032101c0240004920b00c1c00240004a00c0318009002c4629181000004401d025000c114280300300d105150401c850b01d00c810400980780900405800024420745120341075084c190882a0041e800c8100381d240c119490800909660501e145810441c2000c68142d54080d1450b401000e54010f00d1784200c0410f003020101e150500c00104040d00302d0000117000c0076161020402c039141403055010040f00d0b50b84800c4494001c40d912110103108071a11000441c84010900c2504100c80c40341e03d646141c1102901c24001404001344141e51092a400308101c4100741103c903205107a100d01207850742c81c90301982c050f26420001e0304031810071500340b14080c220380b5000b555809070b43e030702c6d005010b180034054006009000c4245001f034000c40f030001c01351071807201c01545000c0440803c00500000c24102c09100440d8034240d4042e0028000d4003403800d5442c0200008220007141d031504401003408000d4a903d8000051401c400240900310103050780450310000d84980b2a48200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 278898228 1250 278896978 278896997
    0xc062f0a0b130b07050f041806090b1503070c060b0301050f160e0303030a11091f0905030a0b010530071410090608151e01020c060f1204022b050c01 65
    0x202c0c0000b0b0f03400141008244800007a4051035481c080341510003d09003003481d00c030020f034044101c4014000700c0c420300001900b000290061460401c50b5a1500c0038a04003140c01d503603070000b04880e0031107420016075800d5903c807443c008688081c0074a40c0716440c0140e1200250401d04a00410403041c2058401000014940b440999034080222034020b991030101040b4080409803141e0a4803030362441c3d0303602c11202400c02d244c51002c00f041030f0369400340d5100c01620035034900625403101c0c000d803001401000500c0c014031040c5002c0b02658515042850b6244140c008000d0b985026508800c4290b400d038024101048980c00c0074003505102030b8140c82c0e0000741480c40300003508502e102c1c0680414803e100c1c0000d01c10381d080c0304001c01c1244004184407005401c101c4c407091801d410b55281401401001c0160105080032000c6600d90300100d08810b290001000000724420400742c0101c1c0d1003110301c450f00c7c004c0882d0345d02e015910040780c03060102920580c6803071485d01d807004032440d041c48030410b07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 278899478 1250 278898228 278898233
    0x4052e021329071101050d0c0f0f0f05070f03020309030a0f0209100302060a0804060b131d010c09030312060b040308121f03020906150318070803070c062f0a0b13 71
    0x1a10011035000d224101071320302d484010b0718180200520100c21601d002d07030700d0003010350001c2d43d001440700ca40c8809100b9002c100e000c84078404040760400200d082003200c0030015400c2c1d446c8031142d50107071069908001c40c0f03400090502c0d4990350f05540c0041000407550035031401f81c01107504200030400407600a0300c1d40d4003081c110b0164000920501880000007418058990071114a01c08000c0030000582c010390301c100001d01400c10b070b82c03001d0441a014044010014420114900c2c1541c8803a5861491070382e044488015400640c0e01d419142c000000b6501804005840554450301249440e1900041e0b1400010801000c041203500b5a0514401580c2e559001c2c100b560303019140d10840f0783d1a080031803820b4424012214401c400017080004002c0c18680703011441908d001070360f0717030706656841c81c9560303000b4458082c1c9811194141040254082d6904064481004a2100581d0f00403140d0040784504c250325038425401000c07800e410080c0d40d82a040e84001d50380c003091031615068 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 278900728 1250 278899478 278899559
    0x72a05040c17100308030a0905011a06071218060f030b09060a05100201090f080a080906061807022104150c0b0109020c0f06010906051804052e0213 65
    0x100070a0214648080410924000c100e03c2001845e00840900da80c1d06144003003800501c03403504192100e500c0c00b150030b4411070507071466620603900103000c2424a4196119100c40e482c6e40aa13000a001c1c007250350142031100111014010138050b01c5610944080b4040034055440661146100300800c07000c224080c2c3c1c540500c001642d40035907450504120340b0710b082c2e00401d803141c4033801074699423212104000c0284018101d60341541e0340c080094036141d001598449003528050ba200ca0315680c0c2e081c84402c58240d01d0362051013841228100d02c00c10690480180008030303c0c5440101c001030510608015488903030000540e40f6000843c0091910b91200e80103042c010102040d40002d226107005030100005425005814203807001540c0d2500100c00505c16031091900441d032400d02e100c80164408041c81c403458002d0081c01d10410229004004c46080c511095210304100280c00301014591028090721880600010051070a0150039014101c0c0520202041c41e40c030307548a0f000c190071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 278901978 1250 278900728 278900747
    0xb030106120516180504021206030114012103170f0406060b0a0e100504050a080f0607030c05070627050601090e070b0f030618090322050d0314072a05040c 68
    0x58a8072801301030000c1030308821480344e9440684e101740042038201e003241c10304640350b0013281d0880007041543c03542c9000040b808030074402c151403a000046d58101c404003d01103120380c10f10a103407403884080c909988400580c41940c0d86401140300c401008208207880c40b0b0310f000b034448105170604221250500034809408004018011402d010041c048140941e040d58003418000f48541886503d990f4100e0b920750f0a9590302d50940702d0781c40810080e90192090f202c29003031070b40d142c0d03150a82c076890703400c05400041d0880e0240800b001000000b841285c040c6a40c1900c070380c0103040b05500d00620a400d481e01d0600c80403154010607010003e48540e01308851012070002d0525071240c0e520000607060500300b403500d10f00102e180c0300304500200044001d01030004240d00c90046890303003a0214038901c0450146d550001c40070b800c82d10210340940c00134407510800c80c581510f0040c40e9616078a0541d0800301004241544c282c00501015a00e9080307400b410701a0b0302042003844006004228070318 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 278903228 1250 278901978 278902021
    0x3110f0c220207080c070609050105040e101701020702030c03060601050717070f03050702030d0801030c05130b0a03050c090702030a020705010c0203010b0411090a08150a0c05130b0301061205 84
    0x95101c1040810101d0181d000340c0d003111011525a0028102a441644800400b55150041c0c01e804950039000d000d144042c0d840c180d441504050400c00340c0084544040c080301300d10040c503100010803483d40038100d90b15a40c110005a01c81c102841490720b80480307500f00740c0c8240c101d5002c110b6181d0307110040d16142a08046129101c10100c0b42008441c0b0a0450181c02c402590213a0310038540c0010044c100075200394115840071241c1d40e405c440c002400e002c020010705524104001d9441c0182c10011204039228002603402d80d41800100541e507980d000b00c5444c0c000c80025410b5240c4140c43c130b42d016090b40003031450901c03c540d0003501e6030024014941800461600d00e01951425403180b4949203005d8010011b4501001c0f0f15030003500a01038242c495183c824000c2601c01005c01c030504501d0300c401c0b86404644800d0403404c0030380003c210400800c5410f1100c0744c5900c2c80c0c420400000c00380050000d0ba42d504002c8024001e502c415142c513076850500090150040940d01848100c41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 278904478 1250 278903228 278903239
    0x30c030a020a090305071e05040e0705120c040f0b040c021b042d0b040501050d0308010b07080c060103120311190f02100c0809010b090c070615050901090903110f0c 72
    0x140c0b40e0010388121100e9040503050740302e01c000c00f043c048800c18111000fa02242c41c4603118a80d203400300016a01c1041b02c5110580107114100524200800c410001b4003c4009480d40d151040001c203086071034200401102d59110310070021507003007603c10501419070910151000d403517411886103003003682d070480d00c0c001c542e0341e0718030000140c1100218020960750ba160b079510400941005014250080c0158861460080001010700d0710002c0c607440b450b07250f150400c29038a410070020541d00480000d03550000100603002e110207092040d503010310310403041c548046154110050803201c1c0c500c0341c0300b1540380410480c0d80119910110503440c1c041c40c50900200800310004a0400a014510701102404d0440810700b00b600446100e1254403102c000700a41c9001404003c8918000d450030090392008120790b1011800a800c00940c1d4900f00071100f500c241d80e0f00100c0d00d225803d0303001d07401047e40c4440e10001c165104501007082d00c4030a004080c0041c3c04c52140303803180002c001480c41039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 278905728 1250 278904478 278904487
    0x103050c0f0a12180303110a0f140f1b0c04050402150d0b09090106050108061503060607080702100306030308060a080613020102100924020f0f0d0e0d03060504060506030c030a02 78
    0x542c03003204400310200e40d0b65030600000d120000502c4c206284403408401003400c01950348440c040d25400e8030700c040030541d1603032101c16521206440e40c0314950044d0038451410400702c605a00140001d008520030708603000c1c81880340b80c0c3c0e414244100c81a440d44542e00740014400941e80e00c11400200f80304d113030445e0f5600c0c5c000d00c108000a00c000408241c03c8407041c010802d07a40c3d019440301d41158001c1c1c0b203c07111a501c03641046140411300030b0306408128203201190301070400001500c0030701d10802e1210715103040c94000907032401c01e188038003001030380f15002401050343c000c4150390000c0c415100780703040600b4081c2c51501d981c001018020b020103080780308005d680c420044840604060074040013200842d0506007418201001f030b102409014940801e0ba40702548200c4540d00c0c01011040d041807941c13001d1403259400403202d805025100c0040501081c070a028128040000d602c00140c070754501024031082d906241c0c421441a00c09000f001341000480003200d502c240d01c0e020041c2d84 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 278906978 1250 278905728 278905747
    0x7060f0e0f0d02040f020a0e0607080703030509070e0a02090a080a0302070b130f0b041502070e0f0c0f0c16060f050301260f0102030a14040206070b1b0d020d05060103050c0f 76
    0x20080c500b00c060752150038404403100d4007100754014034081e4055603d802c4009614810703c00349224120000700316a00420462020034882e500507500b003030801080d5081c0c2641c3d0346008582050580b50a1100741e400140c1c0c6d0b4040c41d24808a4005040803401b92a0300e1443c0d8801a454000c40d104603080740c14000b07401d1030000b1140c486103010303001c160040d003002501d8201241c2ca9410501800904400c011034484220340001092011a0f550365903220181d03554116902d541000545454801001800b0704030031a4602c80242030341c0e0003c08000c109501519205800608880e413101c001e02c500250171095490340241168152804482031070800d8100c0c500d0f80a400d01211244c490a00500e4042c0c0000481900214080c000440042c440780d5040301001e02e4006040e0b078020f5011401f0031811000420145c102a071002681c42041c2d07680a088180061f20ba00200702c5441d81c55001605011003052446003d070400c00a1038200103600d0704e550b080d8010711078840c1c0d400d00b890020600070403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 278908228 1250 278906978 278906989
    0x10b1206011b030306090c1b0303020a020307080301061d060336010501030f0606091803030f0e0f03121602070521011517060705090f0409020d0c0807060f0e0f 70
    0x5842c0c1c0c01c03503810110b107011418020002c01c003c0c05201505810b040000b0000340c458600b595078140c0300d03940340303000c05c1c16590154029800581410103500003440038801007441007025500800840d10351201040103e628131401c4502c585210b80300d2302052050003d0b83ca495a1050000d034900c0015011050602c0c03c41d0034003140303091100c0c000e0340c00c2400200801c00c6034400c070580e07688521402e0100580f50358018090b62141c0344071028100200c030401d00030920030303080920405500e00340028610404a2840e0a014011200808540c0005407000031a0a010015648880489000c14400015142c000c2d2281d2040c410f00b44107040708680100381400c10f45090000802010003009124100c80c80401e20048522828540f07142040480b4244e90001c00c2c40342c0f0403081561a0780c036080250040000408840a855800c40da40b09100c00060712007000046541d801455501001071400c86c04a24180c0d040e00301c40c0c2000b088465070481640c000d00e5140c61101c0071121602551520070210704d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 278909478 1250 278908228 278908247
    0x301140316030809030f0a0f06020d020706060303080603100608191407080604061107050a03140d05190605010f090b07030e1314010909080301290309160509010b120601 74
    0x48010301c4688000003002050001800c0040c1c080e4151455104a900025200c0c02c1d15078010700808030364800040002c409034003e054440140c4801801c0007a0348e03d0712011103144c0d8100318045142c001c1400440d2600300103001c0645101e002c10f004032030510361071a480d5010059031440044e0700945680801c2509403440c2c10341c40f4800221010507a440c44540d50f91202900c0039213010780340146019104c1800800c656680d6004001070403510f40d10350f0222440b803099000e04050960501110514400a000e000d0040c2e0400c2e070041d194002c3d107603604044403050b500190501481403103030301c2080d401800a40854101c2564651607034407a0406031980040043c050b60b00241a22042c0c28154240d071082d030aa0100121940440c2e8995072030004403455982c02a201e41011b100400203076185c9503c2c00ca28200a03c2402101050040c0514040d0400c2d5210102034004801106840ca5108289401028102d60102c0254904800c0c2e80e098070a013402408448840720001c6c0c1d031a4020310f8041d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 278910728 1250 278909478 278909503
    0x9110711060702030d02061e0408030f060f040c020a0b0a06060c110f0d0b0412091a0f04150801080c090402060f130b030703020d0617032502090c0a121103011403 71
    0x5c0780e000c0c001110003034440204450800480070162044401c4800ca13240480c03045500c444030610f5520740400d4031000c0b850003084179a100566018022040c0c5070f42c001d5941081483d001401012003e290118842000500c81d098007494242c00300801684541c0c1e9080b81da0b080420308003101c14100101e600a405040500d0308101036032807081c10403c4031600c071703031060b4002c1540407405506c4510840c0d00004074420004024402c1408414070000d0400500b5111404454280b825648a4903035000c003025540001c041400b200041200364400c0c03008840c1c202007141c0000c82440c0c0341d8002411030141001010310b000d0046014002410241c28090242080e0f0202d540c0b00d15104e0700041c0658450880041c0107800c1a0000031400368040f5003000c801080d60245043c600540d24850b60400e0001c0c2000b54014068511030140e142c0d12980c6000742c5100c50286e51340c0740c030100c0240c24155000060095145080540320440d0301002c241c1c2d054030f4003c0d1641c01a40740c0d0000203894420303d450031b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 278911978 1250 278910728 278910733
    0x215130b070c0b060103050907060509010207090e07030311070501140702030f1b01030c0c050c010302071509121106040f020f180c03010302010809150f0606071505060108010911071106070203 84
    0x51200168100d6120b41200b845400c1d01c40e016550341004400381c481c2030342c0175940c2c0e910400307003444414058000740c028240d0601c122080281d80700514425034080414a83e4030760018042401803550108001a0034542500140441031401c40001d1020f40d2845c150307003c4080c003050303250855038103000710522840c0f54000c543c10449010356501a00307130580720711404a0300d8902c64201c00c40c02002d842d40355070b4119020b8960f00c412540150080d5100b203804a4503000c580b0ae039441a180d0300e206a503c4680280300d280425404000007500000345501e8007041c0703070301c6001000700140c0c031520000c65940e81078a580d030a0f400c80c840811400314901086880310703c4403008225510b40c410b80074604a0b8002d0342e4a900c1520385826003a12403980d1070403403503000d41c40e000044040258105040d04864007502852030800d05498141c8200c4488106c40d0b603140d1184184003003581e1111006001d04612801000795002c41a410a801d1041100090143c22600b00700a02c543e2180c055400d01030b0003406 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 278913228 1250 278911978 278911981
    0x1051303020301021812070303020307020f0117042a0e0a0b0112181b0b190912030507050d0806010e09060301020f040b030121030804061a0301020c01020414030a030215130b 76
    0x24645118100207501714040c0184481c048445140059544210794058006d14508001502804807602e160420745050200300707002035021400e406c0c5c1440c4128094000c9000200c5424000e09092050461404550940e65424400c4180c0e0070b0195801025605002800c40d410350b0040c2c5445061180712410075180c5003001c040c0c0040040c44590051003400b881c49540b1215402d0705240c500c502807d8640801881a0b024071b007884098a5141002404c000c183d6a5558440c1044204071139800c40c0000c5000c140102004010071105440c1034442c100302e242460050b0000700080700c200700c02d900c1842600c01080003a2420340c129401090000ca506541c1c58540c500d116190f0f00078401e142d542c000170707140795100305920110110b07a180c1c1030740c3e03031243c50721280c58540181003442c51a00d002c40791040c00010700d41d800d100901000ba01d00002580700c0d8908244801d4030040c1c421058000d41041d008140000e9002c2481900002801d0011400d0703152104001e4180c010b605008240500900 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 278914478 1250 278913228 278913247
    0x160f08091006060e01030e150612100603060903030509060403020d0302210403031b03020304110d08091810051f0807201501052409012a050c0a080c0105130302030102 73
    0x2d90700ca140b10130a0720103202c5602501080b82e0b6540d248002644803004060114290346000b403400c401084940c0704581d00e0322007404003e021900c15500840c0c03555075903c40b410815416002d00faa04c1501000902114501900c010b500c0d0152007462104140d070009401c41d20000c40110039000e803140424414803450300c0e140280051003104940c01c46c01d030008a400b0315541c82802200c4c85940e101440380c00d206618020701100710b41d10007007107816540038040c4030035a880c0d084207050301c42c50000c41a1600e081c20350b10044d0944c1160403084c096101c5a0b01d41403a02c880c4108080160a180350680903907441c102c0444115604016041144402032a009810f5100081c0340c5d0700880030450310809640d0356401c100c0600504071203881d41ea400071444482690000000c1e11004006040041c2e03100c00c000300c00e50400361040d0000548110410881091200810070b00009100c10354807120800d0810b10f0741640c9080e980e88040c10130900013000720f0307070625502c010f500955014009544440c00c45 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 278915728 1250 278914478 278914487
    0x1e06042402060f0108032703032101091a10030608030307050a020105181009020a0b0d0504120c1a040503040905040305090108150a060c060b0604031a160f0809100606 73
    0x200c440e000148211000f090100c10300c80e0074030341201c3d005001186030525a00705400c0e00094900e0b00101e02141c0f071001980c5441c14401440320750084031a0320b4119804030b107401564007060701700801051030300848911003041c40d410058401c0c000c82d500025602e41c2c00044000d1700007030700440214003021050018084d041000f0f0207040d003035a00280b01c5a503c0041d0004c0c0f131542d1007440e0300c143d84030042c000d07036100702c1358480040c50740064480007416440d0101c4140a51221855160181c0d0700c50070002408030300f0001589450903490803038045c1005032034203180035000341095811040b4020120301089003c004035001082c403e0814007a62070b1034100503280e034200b50520742c08205000c00040e01c4083c210214030044078010075989025084c83c0c01100c03c9034a400040350115a038803400030b483d99030000a40002c62050a2111102350a208000900c0e84050b00500390300307280f01c00d6030707640c1c03a00600e2001c07100303106241c65250340c1d507050115840d01050340008080903182400210380551721 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 278916978 1250 278915728 278915789
    0x50f0303100e0408120403030f021b070f0501080c03070207150e040b0a0803180d0c030c052409040504050a020d050f070b03010e0a0b130218040f0207021e0604 70
    0x400410100d2540d42d500501c0c042da0003214010544101041042100480814241d40103806450f00017890308417a61001d049900241144e485420a0b109051441d0030030408400a44805060441c04170320b820000303803000034043c000c1040d544002c400070780801c2c401c1015000402c0c800384240703d00076200340c0141005d050403200c3d5000d18202801d866890070202c94034411240140004d614014103034006401991042c19100e0303014141c00071b04c4001c9030000d45008003844c05039244081042c0703000200643c1610703148603014a00c448807100040910440f055661828055030041410b80e03980c6060f909003060382100960007030041c40e030403040c40800592078941c086900c04948283c0e8640e8a2000940070074801c0d004550407c0380014407110a0340c010b01200c1c41e02600050018240f4026030090303070008900c0204a03d81115185000c0c5014080e460380e000b40070008618014060300800c210040e01f0300e0f40030102c00e040c2014005d64907984100d9000f88007403100c800b0b00c00c0100d170406400b03011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 278918228 1250 278916978 278916991
    0x40909060506010e010c0308070c0f050f010509061e040807080c01050907080a0506131e0812070507081204081909090e03090a0e0709090204080607020f0d0c0308040807050f0303 78
    0x1c1c110000310203500070810b6040c082016154000320a1031613800301c0e080b01c001010482004540f660b2500014403c001e00c000701d510800c060000740e80d84407a6903084840050102c2071590280e800e10103c007078131180d14440100100c0030150555514107001e0418030032200001c0480c2e40006801480b10410f500442c0540380000580340030303d40c1c410075940c0d502c00110300a0525001314000c10610488100d981840c00c0c4245504401659003140c64010007000c0141501e5038000010301164000000b502e05a125603039042c0300c1c0c14604291a0800c0b1130055060002014603d103002c5030030b000ca0501a25103203400702440e001201900e42004011030319600c160000d4604064001d0541d54011082d00c003000740282907a00543c2c5441c4040113141400303400a01130110a07500410080c007030340000c10162006100030030150800c6100240341c401000b40d418034076042001820b10360780d4808070b03e0240e55010315010015440e18184810302d8030400c40001d16074494a800205040c070044080c40c402e80c1d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 278919478 1250 278918228 278918231
    0x302130b180301110906130801050702060a0e0303010e16020c03120702190b09060d181101080a2007060204180b120111070308180a03050c010c0329030f0304090906 72
    0x8001080c5400d881220004089841042c4525405402c000c400386c405003087c00c0711651007607601c549a80c00c54006646510060300700c4400c00c5038a07542070060009551804005620f9980340c031107115041c46003d405400b07a440105440c54006208019031203030001d006040e18443c080c5140c601116070b00c43c1400303c4c0905056a01104402c50b402d00340001c0721200800b803803411100004129599005045200120380d5130408024880c410b4446184294800d40000443e480075100240007018014442444c687c1010b080c0c030444010810240050805040d83e40c0d110303d954504000603000740d4021000c15510740b6062844083c082c1c000d4400004196030401580448005003800c1e80c492002001800004224807000244215641c81c0c0c400c05030705561200540340071461742403d03440d03c0c00f0380003d0340110326200042c80038491a046955a42402c00070300d02c0c0c0c4c18a0b0f94807140c01d40a039030512541000d034011a6102403106100c8180c1c04016a0741d100d4948110f000245005002540e009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 278920728 1250 278919478 278919517
    0x70e0109080a0305070c030b040507050f091527040c060f02030a080114040e010f050f060613141f052104030203220f0e180c0112020a0302130b 63
    0x1540200c0d2008181ca04040c0034040d902580c0d2001da800d40c1c0301070380c1141e450301ca044002000c520b003103007524080c0740310b00042c0c818145804e0800c910308150003400b92191080d1020b000400351080f41c6d0b030a0520060724254104410501e103504010382c00710300e07580328102d10401c102c01c200e0011411400e9410f85d480340d210f02c40104204a0740c038001c0703000e214003080b150710040c0a400c4601c1c200ba92901001440480c068440322401825aa012251001c020f0385030024040200c00321f414107548200e064500508002400c90b10702249070b0340344100341d05250754080000700350b180c0520825940b02c0038600d41e0000c01355040c000380141c0c0308402400111640d2410b00202e20b4403481100e0241c0d826034025410f0007100e4080344103c07210308441991009981d84c001401807928009400240140c3e0760707110b024580010900303070600c44030f4000c443e10340041c00b10a415030b80180e844e0050042401300142c44030200c8200740d00910469044d40720203400c031500000d56031041402018000555141f80150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 278921978 1250 278920728 278920757
    0xd03030e0105150a090b0f04110a02070608190b0609100906080105060324042405090c0406020a170403020d1113060506040501140d02070f0c120b040204020306180c0307 74
    0x19000483c0d4800d5000e540305104100322051a0018151520024400c00b44120710303800043c100d40881c1c0c0c2d4010b21310700101319020b1568050060703034002c051a003040c030103902e88104220003a03104c01c0c0c20007071001d555010f02112902c480c02074940b803541c040c10800d141d00915101904408052045c10700080b070110000c640342c01d081e41a40d0041c2ca0b11040c4107100030b00c2500340c450220a4010b06038100e40d8400c03410400009681041e200e111300341058090031810002404a204401025000103400c00c000c100726a50340059544946900451090488071024110100a100d1a8400b03580000074608680500c0f11a2080c2441c04200311780d0b40f51401c801c80c0800050701d17014400e43d6408501880200510b50051540202c140f080034050707454209041d1240c812a0405242613414000d251140d10030462001100c00142501c95110361140265036104042400010300080c05541c020020a0864135401020304820b80c0d0842c0c00e54a61401c2000707090160821605100029081d1010151 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 278923228 1250 278921978 278922001
    0x70c0b0705120702060304030309020105070606030606090b0a18020a05040e0a32070f110313081e0a150b04090f0b0a0e0601091a1c122604110d03030e0105 68
    0xd1099000e00086c1c02c641d600e445c250010114010701781d0602008111850004110b172107001c02552040b000016868140b009500480d6580d20701076000381c8031032034140010b00d401c0f442040960201c200260740d4210500c0110f5107170040e5840664640f04c0752080c4641200c0640182d103c2403841068001c1c00c01e080300c010010842551800260048200c2c00700d40564450100348211400508003400b245400641152841e0320080202504111a042c01d020301c0600f800175a9004550040e10140c404071000090384800c4500b43c001c0c0070606804080351004480e0700003000603d030044c4104044a42410084000c1403104c0d030440e204514440040e030840128441d400d07010140d58000c0c8035980c2400954001040702085000035106d0303c2101d600140c1d01c000d50121070f60500715010340c0041451506000c0d40b42a072102d0810b102a00c1248240020700e08040c408441101d580d0300a261640c0c108021030021046096422001d0020205c003896090b40142c212100e004000704070b2030750b0303001003840b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 278924478 1250 278923228 278923237
    0x50a09080c0102191d0f040e0a0c03050c01020f03030c03060d15020918090d05090a09062d060503070f2a05060606030903091905031009031709030f070305070c0b070512 74
    0x31701e840d44000c20341100d810b002c3d120000c444000f420010f5954016030aa902e004010807080321421302558090040141c1032000300c2070080d0a00080c500c2e000001082da03100e010040c03801041c80400f10000702155a01400951880d40001d07010061094201f901c00103540891049800340c04111581c17000380f4145110548180000ca011300030000740400d0483c0d840e40300c007035490b51003d1007034070115680e0a9841068001d20040040544144081c0315082030030001c95007980380c00804020400000c0e81010840703900140da85481c001002000c0d00540f50091180ca402009070550a04401c018454002114845d0300078411141e007036940c2401c2059602c0100c900511640060011031440d040c6041041c090440c00207884001c1d0340c0b00d00c0880e00e4005104003220100d030301c0346044410715410115641c1c0400025202c40c005141c02500d82ea51b034810fa03c000310505500103030503c00e15110300c003034414050740400460f1100b95140d42500b21500010b100781d62038058244003c80900f034840480c4c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 278925728 1250 278924478 278924507
    0x90b010c02010f0e011206060f1e140702040219050d0b0f030705040509030708030a052202010e01051e130303080c030f06040506060903191101090f0306050a09080c010219 75
    0x107404a419020013102c400b044140400d0601032009401031503e2501d004007805805140d54200341d104980d44000c01c20540444101042e07018200d00c2a0030b5607000030101565003d8650a903503404052020400a20803025802002c0c414030721100d0f200f0f40e0020003400d079031103a910709200148180301080305c3c050a40d0000d130390607070154200700f1543c14070b60802075010f01c8001c10784e0b0800c8042d86503002a0380c0704503070198900b80c2d640b00b0011844024169a681e410001c041201144a80d60019080f124900e00e0541809000f1031484a01fa46c01001550544031451405856a2129042035540d16242c00100c001c2095000020300c0782d1003400c2564032940c0f0401e81c6403007130f0302c540341840f00501018041d20b80201c0100320008d000c0e02e081103001c1c61032159032040e2502102c40e00349410403080150400341049407000b001c200c180e450b4503242c07007626046503000030980c440c14400300041c5100300c0000c01c0c091003c19040f4000704107502524504610001c8480220b450000485450b010840003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 278926978 1250 278925728 278925737
    0x705030c07140307061209030504030c0602030307180b030402130b0301060311120606130b030a02090c181e120a0f1a0109180f03020a0c080d030605041b110c1009090b010c0201 77
    0x80e46c10001d60081c01c19540a41061071a0640f2922a019805100d07003018001d6403000050003400c9034441c07003040104034040c85842c11581005402e83c02d81c4000380c07010f07204082c6000403580c29403d0343e229901c1d111001f8002c1040596074a803484800c003c604400d40316090500700301e0003100d008101240300d5070009280d280041451174411004010b140800d41d01442291213040040e2154004103002d010100e00541d100d58038088000d80c841201c1600c5402600000180c980c00070f5028610248807004951032542d20652008581c80c10402a8002d001040d032059030b04144040f041030b6420b90001c243e506105603894480b0881a01c000351041030300c001d001500c030f01c0420003400f03041245500c284155010b12006807039201203241f4035040b002c01d58004101c000e42064041c0300b1040140030a40e000d20005a40c58620300303800c00003900303400c180220841d40c000c81000900c0000c0503520000e00494041c80d581c00008e20b0301100b8003c480345241b400c1544d0700e0640c01030720b0078200e983d416900c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 278928228 1250 278926978 278926997
    0x301030f0803090106090f0f0f090b060609060c1b130903090e091006031b050a0b070f020604080105070306090608030c12090d060204030f06050f1003080703050705030c0714030706 79
    0x25900c1c0c5651004000c24465543c0707000102c1c1401c07080c0a0b00302d8a0520740000b1503800e0100120104840001800d13032041880c0c824000002041c61141960206041b59401d0303d0b60404000700d4064400d410307614440c2c1c02012040c4031400e10091000790400c00c141d4201505c0d03c01c1d041d1072812104450000340105448150030001e142c00d2405143d440003e02d400d41368141b445100b00c0e0306854181d0012110940e00380b0801c08609071034007030b640c001c0408a400c00740e000d24005405842d84104803005d40b203003030799108103c103540340c500c1104c00404c10003000f081a883c00b04c1004008100c2401500d0f841c604000000814180001c152414010f0010280c130710070407003981d4800560312a00041c2e030801c40c01410500403c680b17102500045010701d50a180d00d00a40c6480c50481c1c038020441150015220f05225031441c0c41c81254069030ba2101c02c1c503a541c0800c1c20191344900840c2c0c1c0041c00c0f44400210a410f1001c0414800c04030b4401242c002c0310440d0321010907840d000f540c0200800192801c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 278929478 1250 278928228 278928233
    0x6080d080c0d06051908011a010c1103030c031305090c280e1801030501110705100207050c0607060911040b010507020f0a05120d020712080304060207031116030201020f030301030f 79
    0x400415035484548800030b0500c4c1e5a1001c00c541ca80c800d640c42030035044040c0c2c108855002030240a005035451400d80100c0051000068032043c84400050074059588104500f261420001c0f109003440c50011a621a105045201c07200561030240501640806c0b002c5031001014074240c80c00c0c2003480180c684150f03101c20144100140340d0a03c44200494a0440d0749039490381302241840d407c1070001c0c12480c1d0705600b02103080d038110030000b043c4003008001d828080345000c2110760700450005000f42e81ca8000707040c454900701d50f542d502d5901c039030005403101c104629544070300e51040c802c211b61054405d09004000c100c0c0e41000d181c50202c0c4041014100501e018260100550030003805001d0098030f0701c000c136625041c45000344480d94049403001000640410840c8000c140841400300c066401e1342d100d210901024100521a5801040d0700c2d0425000f011140494040c41007220b4a14035541c80c2c0015041461005a026018072101924480c1703000c000c50741640e811003001c00a10f1000e5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 278930728 1250 278929478 278929501
    0x21206090d0f0905090f060d06020d02070318060504060c06150b0405010e1e0d0303021204050604020a0b04080703080d0912020304061403040b15010c061b091d070e0117040c060306080d08 82
    0x810180e2310200304204030b0009030061028224646401000603100c0da031600d40508142241d0100c16000c900713051040003416800000c4800781ca50500e130015407814280b134084094442951446c2d01e070710f42404046003001070070008d403080700e0302660f0b6030f01c5100710035051082c400543c9111184208003108040444d040c5103001c110854803074a801840d100700c0601c00361001e28280c0341152241c11080c144419440e200041078003519450240c145414504001650707280300a10004240100105001d001320480354001031079950070401101c040c07845c20707000a460350b200c0d00405020559118070107080f1141c03002500d00c2990306c44107052241e01c903180c92180c02d2401e01c008a04007c1c17005c81e074400044450007038400284503040c1c10006021400e01c0030f42224900d40008407400506515000c11901403036844e50440c0d4142004401c86400c2401214006802030031540a45c1e030440520041103a503040d020b0464006582c10491251642501601c4403015180000003941e8040410038901c105d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 278931978 1250 278930728 278930731
    0xd06060f08071701150207033f020d1b080c010504030908031c11040b070b04020907030c0e090c040504020a09150c0b0106050a0c0c0e19022104021206090d0f0905090f 73
    0x40c0d0040340c81035aaaa601d010500c8051800c606a90510201c600c403100215a40c1015100c1c40c271a15000342c690307000c0000e6941c2086440c030303020028000c94010141c0c0c070b51800350340c1940d0840c032600d40c0c40310700140700e6000c1c100540e400c9002a90005000035a8100401a2540341c00840030301e142e00c030b1031110400c018260703620103070040c0c0c7d100300000145c0001210081034050302c07a455040042c80c3c14010803d15030b0380100300005060610b1420840c590340700d444141c0c1d82100302c50100b0300b51212400c442c0d040c021504044e03005480040c000c0320460b0030440c07070340490b00d15008030911402c101c803040369203000c030078001401803000800500941d4051130182640c904140340051850240b500c170032483c024160f1050050f449601d040c0100d2203440e5507546000c1b1002c550540c0740652603100403480340c0f01400b10b01d01142c644800300e002c6540e103420f51090002000203c1d482414040020fa468004551044012500d14000301d20b59500410481c07003180d1000300100b60581c2c5005051519910 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 278933228 1250 278931978 278932019
    0x30f01050108150a0f02041502010f0c09030f03020a0b10170a02010f0809160b030702010f06050a09020d0b030f060f01060c0507060e010201020d0507020c04060b030f04020d080d06060f08071701 85
    0x882e09064806461071b880640010701004400e01001462070501900b1a4800a6050003460034092800141034000c48440100c0782d00101c040b4850003541001c034100429000300a10415091052100454445201105132002d440000702e2074603c1070022030303a450103020003e002c00d82c1c150f01603071100d0180071407952010000b030943c1c90f05011100701024486694002c0e4070780100200070701042542c24400c01425440079101006840d00300350010309861158400c40c2e61491f0001000304403000981c0141504110140449036101d21110a007078484008903401301103803c3d0040005205072190360806a040d8100001d41500c81c107103402100d001c090048441d040d9902044042800c0c01ba500c41c183c8075040c4c65020303091100e14a82007006980036640030b200c0c608018424031a90700d144098040c2c1041d41260031031401065850180c4103402062000540c007860210001081900706544004c9140306a4419601d41e884000695191015100b60032a440f10b5000500141c2d2014065511032034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 278934478 1250 278933228 278933231
    0x4080618070b0703020109060c0309051c030b0607080304060b1f032a02070504060503010911040504020d02061206010810231f030e0709111206040603060e0309030f01050108150a 78
    0x42c1c03200210541684440c400302c0040c1c0d55400d03000180817441c4123082c2c8151841c80c042c8000b49441d2a415903070f1004000d5068981c040b102103490183c000ea00109080102404040c1c0b900c076107040c0710a140d0000c030b40658442c0c2c101100312019240070415118620413000603c00c5601404204074028030406201202c00d8003c9051603140040310300e030041035800d00d94020079040b0f05041c184810381361a90701881c0681e04000300400003c1182c40f600c4099035040d107001a007075469000090250341c600c1c0000c0d401c9200013034145100450303400891710a990070780750aa9640c90741030390758120001c01d1203564a00c00f0102d030224440b243c020340f00001040c0c0207006201513004454031200c013140d03405007440403940d51407840324044814402c000041c5540d00081146d02c000d00f040600903c00c040b40d2218001c100c2c1d00082c021790b1185d016001443d045807081154600f003c041969a50002c80341a200788502140b401700300b1030501801d4160740d4440b000c0d050b41b5154402c00202200f004e424007a106 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 278935728 1250 278934478 278934493
    0x60f0b0307060c121b29010b0703050f1902030d050c070b24060307020d021c0801060503090f01050a0506131b120605120c0a09020f0f09130906020910020304080618 72
    0x1500280c1408282406017002c24102021140c0711b1080100c0400300503480044103004011608110040c5d07180ea030b416051459641c00c1d410359502403441614910b045170001030101d10b54a5a000000d410340749507404c0100090344411b20285c10602540740c0080c41400683d00103480c0c22103520500c07884100d03136400402d940f901800051002d40049403010010307485007004018070342d810824032031988901041d0251400c4c1c0b4a030010405141401407109202e400404918000c02c02c0080c1c441240120b4001c2005040220810018250583d0304030700c2009540b122001c480c080c0d1180342c07041644946624000f9070000c00c207884040040f407049600c26079a4030300107800c0d15140c05d41c200324428000606500303a0410104101c940c850340201a03600d20510140083c404032600301c42400c49000d0850361100c04503400141001c4200c9114010f05040540900030820315030041c08140f0341c00c4484c0f0005c500718800490307403405680300e24000c6921041c08610070800c9245500b070340c100c0d60350a840c2030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 278936978 1250 278935728 278935757
    0x4050f01050913051e040c051005070c031b08161e08031308060f040f030c02040603050d0e121906020c070503030c030306091003030c02040c05090409060f0b0307060c12 74
    0x643e040285a0020f070342c80360304000700c0c014a03410101c0301a400c1c16a250190900740c440d98007000090140034000c00e1064404036240b40101c0c283c0365503581c400c080140d402d413a49841c50084240c0c00040c4184002c030140456120000b1a00381d014414000700b403e146880c1c0310440b080143c29400c031862a070842940400d8424060000b0881c0401d0300b40c604a8030b030319044015140c120004c15491118007101c040c80300003031a14407802c0c0100d82600c0c014000d901507000250041c9401c1e4001000c0344030351105074072942d8104050001c0c00d0003c40f40341c00d030481c481d1101c036215207a482c034040d00200d0000100d170000b90b8543c00340011190355801c50b62502e0700d0341c0100b49554050910380310664008002c00003a031921500065014002075031711070f40c0914590300035010700d0704000000c1c8103e4644030803a5aa030304c03c9060b600709440040c01400109003905042008005503a82c80202e03508280f1801c896003070000c4c90400301d401c1d0b643c0b16503400c815a1a204030104040b400d0404200030b40070350605 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 278938228 1250 278936978 278936989
    0x4030f120e1b10080903040303050a030b0907030e0c03011a040218040e1b030a030503070309030201090b0c07020307090614190803041d090a0210050d0e06131208040804050f010509 79
    0x4141c96150703001506002901d040008824031500f400c03041020743c01c2088080780000c016581101d0781810407944518005030b0a402900b9030100700360b0030103c0c407010085550340c1600440300c5480f2840650b115070021005241c00c1e95040c0c5000030810200d403180520341e00380356004180040c095100c02d5090b41c89640003c00b80d071000300200001d540030780d10b01c081500c03a110780c405c3c41c198101c0c010419030127103540203003041c00000c20b0003050668403c101e03410706d4002c0d0041d4040c16488441c4c2801c0b45403180c0c503110300782c1118030168088e105581d40483d602400340304010035501c0c1d0402880314824020100f04c4940d9a007005c3c22035024014500040c1c1610402c0540702502c100884a0070b003030304810900701d0300d9000400244039584000802005a20307150328035032040040f0f21300b4558a990224403e4061b061000c4a6a101d200c1c00c41003240e0702081c106480840341c40b030320a000038038001c0e00d0110f508000079a80070700160020442004145856410f20100c5c00041c10860f0801e01d42d5000280c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 278939478 1250 278938228 278938243
    0x7050f010203090a0b09120c010c03080c0702032d0a0b060603040206040e0c0d0b0102011a130b0901030b04060e070b0316030f020d06030b0a0c080c0c070b03070e040506010804030f120e 81
    0x841041c0110345056585045140c40301c91f54501401440c42d880ca0400080c420341c079180c0050309104d1518045410410341304211022107030042c01300c40c1d0f0790710b80f4000d000d0030302e40500c44200a038510300c1c1c2ca40e60f0200d01190300d20010380c103d121001c8a03110042008255400a0b10490f0b03c80010130002615907040e41242d4424868040c071207481d03400803000c843c262904805043c2c11a4900584030010700c81c00d0aa9a0200340d0540715114903140320307510100100500c0d05c0c4075600502c004e0000040095000d071aa10451080006000d101d60100d41aa540c1c40207024241e8014002c0c40002d059401000410121401a14010910030901d40c4e041e0202e90060090306070b8035499010500600007010403068000300050000c00207070401410040032100050196107029100150201a00800700042c1001d007004524003640c1c3c0c107004101411051170624024000c605280003d0a10740c081c01c1c40358425030701070303c41081071802150200e4a1001681200035455520441010035403410450b08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 278940728 1250 278939478 278939489
    0x90702060103050c0a0b160c050312040515070210030b041d0c030d110a0602130b13091103060d060207021203040b0703021507170c04090f050a0e0d0207050f010203090a 74
    0x614081d4150306010707080c940c00c84a00b60007410120010000103074007104071400d03940714860a800d00d0700d16140c840221015640469414800c400000c031071925414014012501e0440b0040e03070310030740c19000c4140c50043d00c401950088850804505070340c0250402c614501d0000c0000504241045000c01000c41410042803254000e14038018641010014403841c600e00d414503801d40701032010701036a900b4026000038252900402c00b141005040381c030310380241c0b0111002640784e41010b000002c000c1098450001214107000034250b100120b20308480c0542006001352440d901180c489070040c3d0f0000b40304076081002411402107640003400a0301c0034200c030191030355955050b401c1c0203180000c1c454a8451031000b010074042c0c1e40d90812030620002c40c020481a0341540da80d4801d130b400d806a588080c003140c1c140f9058400540c5980d100c54801d0710582c01c20004c29605a121707950760310601041d40090b902c40c0000b40035610f402e106141e45803d0510480e4a000050008030b880e811065012 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 278941978 1250 278940728 278940733
    0x102060c0313080d0f051e0601050c01140108012a020a03080415060e07020f1615051c1b18090203090106080f060403020d1110020d020c010e210405030c0f010509090702 74
    0x2c17141400b206004083c0c021b44a034081c2544035100400903d0500c101922540c1800000070f9012000303a400c0d045a4076025120007200d5840d80d60300a4280a0050b61490182003015064880d0891280014802c031941955000705211a0141d805440a000c042e1050b50b20744540031041c03e02d0f608901450029040301b000440c918104103002a00c0c0403003820b1303c1011a048601846c81c00002c0840540c102c80f0502e40500c0d6000501000781ca042c42690a02d034594200c0050394040200d0340c0d009040740480700728881002a503a0101143c40340048603a00c003105c86102010400001c098002e9134000c017100000081955485000a19281070345000b445103030000300400c424150180b110001144a030f081012400300c08412554844540609400d0a294041152502d1902990544550303e01400c020496074500750450b6a4a09005004542911035a1024011846000f066a0845034060f0040030680704040420034180c03259940c80381000303014010000c403a41d8203060b580c05503200d03401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 278943228 1250 278941978 278941991
    0x6090a110f061c0c0822020f0f180712020405060d0902060d0911040605010201020313030305090c100528020a0b0406020d0603211d0f0d122106050102060c0313080d 72
    0x4060224a80103180322500b00301d20880c115031840490f43c46c00300d2a070403280744000c03804660016480e160a89403143d00012103146040c481c81400c0400c1d4082d09454403a190b20b281030080101c1a48070b0b60240301c1d0403030004d0101e200e1900700b603044072a40701e00c01003c0350f0a140c1c1c50000074003116401c110a8488010464514245080c14840c40700500002e01c000d514500e40000f4441107660711340e900408059640002071079080e41440340d01d0301a08020700d80f040400610718000c2051b0041d245030400c001a00060402c0d0344015002201c0c1d642e00ea40207003000c80d4058075400004800140181e50564080000150120032441400301a5105a1001209075002905061919500c0001d0000d00401d200010b903442091118903012407000c5403001d03030340c0340d110010452401c4090802071000c021031020058450708130350001c2c0c120000c40c0d00d40f130551400515010a41d1a5072050740d01580080002c01d0803441c0100080d50b1146840720450408807255075400300c0303640300a401244080e505c61 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 278944478 1250 278943228 278943251
    0xb09010b010311030402010912050307050706111c1e030f0903020102040e0a02121b1204030f020c2d0102120a0e0103140603070611010b041d06090a110f061c 69
    0x203e00c502da0609a15501d0035450320340e001170712030036041c05040120134030141e014003003010800465000b207910100351008075645000250080c600c00c200001e6601840c00d82104241035800c64007450303402981d4603580543d441c0440c3d80e81c0e42941000c5001c1503218004400414000c1c050208210300c65400183c5d541d1070030680708841d43d0302600c4480800d00400034882c200021015180c1c000c24060280c800e145040c004103643c0b84101000c4500c4030500b80d040000f4160083d0b0b40b55049103c54003514114100c0500b00214294010882c40340e0125095050380c0846000c2d42000b0540410f00468101e09602c0111460720b801007500c0320002461001d041c0140d50b4140a02c0303042401c4003211440c907051400000751614824010700080041001c2c400400074000d42000c84001c501400411043c003800f080341c50003c242000307a0045110f0080854100c1c040080c0c5081040e07005003504409000138410000170b10350840b49281d2041060003681da4064108446d40d484000106e0b0000e45a09042d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 278945728 1250 278944478 278944481
    0x190201090f0b030a0f18030903120f0225030f0501151202010e0907021603050a06180309030605041109010e090706020c0f060310030f120e0321090307030b09010b0103 73
    0x94100501d41555400200881010703042604d402540303c100100c0c042e01c1400e0220028414080740504400c032807404c41b0103158000b200d50054034015030f41c0300040200003400b51803143c1c960b180840141e111994403504031a052103031201050480792050800ca540b910780c6080c46002a9044da10340e5521054005c2c1d10421251100003402400300c110414104d03600040c19207050042d149000703907030550000d83d80e01d200b849114136566a400743d42e42010380301d05004d5039400041e8070445203641340040c4441d0095400e020b901417940d040e516080c41604542e50000903000141080760031140c83c00f00030070142c2c0c81e513003014060070038070010081d0385c0f03401d494644c5800141e42c85241990002d0800c0a40c41d03c44245222684400faa01c05540b0348500718040501d00d0a0b601c090940c01b0036480d9501041412000251200d800c0d9a074001d15542c12400c0680b1000d010b4108201c45244284c034607252401d4001600725910300405548600f0781d2906d42101d011000c036402d02481c1d564080880c8950f806 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 278946978 1250 278945728 278945747
    0xa0b04060324111c1d0a02030c0d170a02011107030c1a0606030a02090f0a060507050618070905090a050607030605100302030903160f150203040314090a030b0c0705190201 75
    0x14100c01d10003144240058401c0c1d11800e94000420b40080400e401d000026801410505e40c550421030740502c80b4500d515110030812008900c0b0f80940b04450041c1e2a055003266006078100c01c2c02d07010303810066100005039005d04c0c0c006042d55210100102d000b82e010b4042c0803824080d0311406900300b040d05d030401003001700e92a0043c040104400380402d9880e040c003a00c1c1d101c8100c4000503525400e0f00300003030030380f410b00e048181c0c000c5080390701107429a80100038040b83c41c400c4044074110780780d00349150304a810a000d681c6581e0301c1440c007004803022540285400020240c1074654103603250311810305040e001ca80040100341c0720002000707981040c40003018942d5043c034045045043c43e0949540320b2045801101000c90b05407000001e101c070b0540c40ca074076140d00002160310b1440361140580a5001190150f02003130541d0815886a1022801c442e8800c0700180f091000c3c5086940d40641610040c1024846003414052070b070008030300b0411a1200d1902c0c04071950030070b900341300041c1980007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 278948228 1250 278946978 278947043
    0xc18010201090b0402040222030503281d130f05090f0c01021506011709060108011808030403030f0e0a050304050f04020c1b0402250c061b0305030a0b040603 69
    0xd8a0302c000085004950496000742e81210f025035034461076000b41011800c15080c01040c50080d11001041050000c028a60050040101d0001c2408400010178010303000f074502010900543c00a1049100c205c451100d213500140070070100001219400101c072006407014401d680d4030424000400c40c02c102214101040c00010a00040c1c0c0500007511044843d050401000d841d20110303006a000f07210075070355140600151000c0e4505500907a5480f6001c1c07061105035480e01c1c0e8035206800c407c2d090003004035048450145543c6490394200c00405c800341002c83c0260361000d0040d4a00401c0c4540b4030424000e030011a110b03400c10040000003050240080c1c813030340c410001e6003407140002c25107289011a0152a156890300180400c020348500124146000e002c1d0413181c1c0742402840b44103040b91b00448030a40300c80c3d1200d6058403000030f500c072002d44821102642d540003d1084005540c0303c071412030041455120640460140d500b943c00c100e81080b00314101498184082c00e005c1c40401c0e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 278949478 1250 278948228 278948231
    0x20406050711030703050a080301030b130218180d09030b0f01031703092b0f0f1d01020106030c141905010c0b041109090c040f020f09100c0602030c18010201 69
    0x2854110050001d10650800034800101440445007a580030b201c2e020040d40c200303041c3e4260320030614010703090b5071090004641c009100004130f010910030000380300788242d005e401440e14124421256440d100c0050050114204000c45180d5804090008da00250b50340e8031040d1103541903107054484038a00900d409070032041e2000410100302120380700040007803440e110a650382c03070300d40c001c0d420110710559581149090902070b503081025000a00e40d50300c055602e0072915452444201c031051520181c0000140b014400754001c280c806030b40c448034610500000400d1031392030b81c84000e20744050b40650607028104000d902d10782030490005007400c4c20303549012072480c10000040e280b81108003028000741c14220000307080004040c084c0e49041c80007030030051907240c003c1205507200000c088440c0280e050142144221119000381d0b4194214011440d01302810306045c4610340101050240c2008040c01854001c260076100030344c0074088600d247c940e40c0e0290005c0101c40a00c90b556541103a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 278950728 1250 278949478 278949487
    0x301020f09040b0a091103040b010504020c0d200111040e060a1805060103020706021321020f060a020a0c080313060903050c0f0310110c060702010b090a0e01021c090209090102 77
    0x4649503411030307078100801c58000500003c600f0200341c0036000742e00640c3c1e91600c0d142905000f2070381c82001c3c5225610400e20380c00107a0701c1d1010700041c0c0c000c0c519010349560000ca81814864001c000c0c410545101801c017401051802c0030644c2510041055031545402c000b0b01402858034162408ad4000000e41d4041c035118548203448103503040e041ca02e102d499175100003050071a8425011100441c2d04240c0554a92103000c880c0440c0c18801d1007905605c42021801c001c100070011509115075070014400c210094101c0140041540304900e01421400b0742c00340080002d00d0303448900c01070a185002076440d1642202d55a2120242e03030000f030107000011004100040700012030b80e903202d50035211000c0484e01000031070701e031118085042006500b002c80024004005801a03e15110710300308a070010703260700c10180d01b00c584130403006810848203400191185101e8010f0741c140c1140030001880c00d4102c4e12001c142180b800380c114000b0f40c80d550a50254900076074002d801c0f640c210021481c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 278951978 1250 278950728 278950747
    0x30c07210609030e09060a0506270a0f140306010308040605070312020c030a080f060607020108040c08150711072909060f091002030913020313052a030102 68
    0x220402441041851110103510368a01080001248809684128184240001d918000e0105040802010702490303a0700c00140c00c0b840c00046850450318090501454081c017607990fa90f0501c00c9092030f011460220981c40d00a4903541c1003100245a82120a0103180c02c003405044046030400015100f54002c00040c13021903441401c6030225251401d040780e035a4014a000d03240c1e400707180c40b44035520b44041107445080074048003c101906107595010656503500c03242084140e81a16a076800440c00e001500065000b0002c0c1c0381c0050040003032056040e52070072103610300f0228680d41407440c503039201441b8010b500300840840f00351240f00600003090070070000d02601381d040305c440c612a543e000715282e01a902c1c401107900e5640007900f015582e00d900301c462022a8041100980980e00c1c148102440c10310100075a090f4003001801c0130080310392507062001941000e00712108044400185e0740000d0010070800000a4036504d00c105245044203607008913200302c2c00307401c0c042c0e4010889900d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 278953228 1250 278951978 278951983
    0x50403020c0433050f0a0f0311011205160e0f0904031404171c0801060e060304060b0301020a0f02070603150b1e030903070b0c040b0d0926031602030c 66
    0x40300303001540c00003803203001204100341101c07070100c4600320783c1c910300c900290b4244005589415650240c454070549040e48061084952152089840703000c00103406000280340d00005078000241450255211030b100341c2600200d13502a62100603a4035503d900810494105100c1513540d60100c6d080f01d1415803010218400500c0104000d08011900e140580f084a070481690064001c00078414920f900036901103031b03038601e002005801641c00d0701a10b044240b14403500c906070783e00740d0b80304121450303a07005106294101070300480b81c0036290350444500761024409401180556550315418000c0c075480a420a1090f411441c1050305004003402c0c0038420503c84000c640c11418220b50b9000d4661030381402c12980d00d07034003480301400010710484060002c0641001801611440390540ba40f03200845244564411030384c098005010380c1e03061003100d40c4030100c414010f480c0080307021314580c02d00400381882d00701040070410100034003400e0310f410151101c4400042c001149003458885100d507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 278954478 1250 278953228 278953243
    0x1a070b06090c0d0f020f0a0201090c051906030506060f16060f060803040b070c170d030501141c0615060504032006031602070b04091a01030c05040b0c0c1507140105040302 75
    0xd88442d01c1e9440c0e0624a44c03a81d04458881e0031012049883c1d04503000028043c0400e10400d580f12048054003281c40d180600314291502910344039542d800d80341c03800c00c1c0e010f802c00070103180d8084000c0c01031807900d1400d1801070070000c83c8a2110200c4640314038003042141c10b5200840034540c5815030500842c0000412281600d4070f5207040e6403104928034002413441c246800070600a02c990000030018180004d020701d0700c807080d807000d022507a00ca4482c0f102c1d05a441ca0b5465005400c808902c2041c0b0030443c400e00d915015100c0172404803000001454040200d60041000941c006010003d010b0014804011100b8544003113000d42c0f00d050002c2d58600002d4403400305888020001007406000700442401840341c011040e4580d5914000c1d41c0040159000e503403c03841e428031861000d90701c64403602c01030714a1078440504040c2411071442c865000b005100c103041c41981d01c401d1550b56903407161290126602d0307040b960313410b0914200c0300b900440042800c1a81c14102030100080c0c0104840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 278955728 1250 278954478 278954497
    0xa0e0f120d090c080a05071701090b010b0a20070503070b070f031404090e010c0306060806090703020f090301060b0403030201180b0f0a09020904030314060607020a18061a070b06090c 80
    0x4079440041c3d040400403e81c01340d120b14101d105071001c060801c800031510000b00d81c484e507128082d6058503400503080e540000d100a0844913140018450304116501400010300c0d54907110075a01c05684000743c2180000c6d84080d00d9a114110070080c80c034040019201422810700064100000395440304488040c0b040003c00740243c0340c0c030000e501344520060b50010729502006000020410907290f000704a01201c020009041003000300754503000304a107070b001d4000949105a196a140c034114003d42001a40034120081045559925a82401103802400740c2201c00d9903590f286d49001781c21140e100b40740500020182c002e40001c1072500d01001d07400481c04c1022151503507500445001801c0240000350f01c0b140b00401d01040c544e00d68011b03142001d03105448029900c500c001c211460140710402544400c9020f400d200840c44944900100c1c20b8032070022a0207620340e220f842400820000071102c0e900d002c5181424052440e0390300da000380c0e048d11b9a1a07107092a903102081c0d4421140c06 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 278956834 1106 278955728 278955731
    0x902030f07151b050a02010c050c0a0f0510170103060209040f09030c11010809030a030b0d050f030304060f0603080d0c0207090e0c01080901020901021c0905090a0e0f120d 75
    0x141600d03e600003004041d000c3d41c550046403c600050310441d80341c069100110455281e005018001e04441c030800c058035030903d401d011503201503103c49400c000303e0081e2000d104031341c0e015003410340741c10900c056a101000c00210340134100c3c000800344c000703140c0001d000034194861800c103c80f612420031250405107170001180c0280040d903d200703140d0010008046918040e034044690703480041c0c82800b01040c242c945605100980003c440e00d81c000004001c2040064807502e410034040d4034040164600755142c0d803900e8094506100c1080b5581d0059500490013000100700078545c02e00188a451040c19000d034070f425100e10443c5c0440c038044089006501c060007a50b0a448060b0300a109000c2003010244c03926080c00327952000c1c040c004c1808038940d214132110324490a05014080343c4401e58200700d0f45402d221301c1940e50340350403401c40724600319041c604407010607152110 = true := by decide +kernel

theorem cover : BRFrame.Cov 278776978 278956834 := by
  have h0 := BRFrame.cov_init 278776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 278776978 ≤ n) (h2 : n < 278956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
