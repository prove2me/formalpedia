-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2694
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:28:14.810981+00:00
-- url     : https://prove2.me/submissions/06ad8bfd-39ad-4f54-86cc-26772d40e3f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 484352517 ≤ n < 484532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 484353767 1250 484352517 484352521
    0x1104080303041b084c150e060f030a060606050702120a03020604060b0a03050709143904051c05101416110303150307090b010507060c0e10050c0d0c020901060503 71
    0x80f2041001507401e000608045c03403a550048642c103000f092040007114801d04003400c1c0b10f0008101003609003112201c008204403034448408000f0301c41c10200307d05500d4850a502800850b405103c3d0200401c0d00d900c5455807000315205001903280910040c01c116005001401c01090700841d443d50304c150f00050024001c0041c40018407080d0450b000a80a442803a4011542e43d42e00d0340000103940d42c10010310f036603a44034010180e0820f02c15800d006000c5050304003880590a40e80110848982c08d01543e04154646001c2480700e4035030299000c015000d070b0780348801d10002740160302465100400a10103071414132686107008001410030f00c4103a000507400c0104511500c285040c0c02c4480054a9490030001c070039603041135603003100740d100340145035002500c00a1841120358109043c0c540c581011080d4807504010b084089c0a90244040c0106030212030380d8814441140c81c059440301c64a030400f07000c169180a2107081d80c1400e21582c3d0300d5980140e501d282115044840310b151013507984d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 484355017 1250 484353767 484353823
    0x204090203070f0801020c06010807081c0e0d060c080f1b0f0f16060c020724020106050604090608210417011103040b0f070207030309090f1104080303041b08 69
    0x11065590120980f984620400b14452006400506c41010b0b00b0048941da039132581413298071111544100d04c800da01c28041d1b010700002e469584800301d030050501003500c008180106000c81803c080c01c9404503a2441c0204d0055044000d5603008840c2210786a0301c4d103800412110090804144081498004500c0680c1321120008a4500c44107100c01981c80e000c2104e0300100c884190341c4200c804502307041080f4049803000580c1c83c1120800100c00c107841c0c0d59500941c499050100302c0400b10354949901080313548440000f04010038189000003041d519112001c0d09001c0340e042c060100c1030002039900c580752070b500f050350207441c0c014020040495465852074010816525105040300020003000148103d0701e050a10401800c0c072034909540d030706201261a20042d010080c04101c0c02d42007440703130403490752205800038114400051a24040300e41d45e0015041584a100c0552000081100b044145051440132035140010b24401c142064030058130782248403421070090030012181c8000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 484356267 1250 484355017 484355023
    0x6090613060503101b0c03050909060418120201061a0405010f09090f090b0c0901172a130b0708030a0c050708031302010806031b0907051b06010303030c030203060d0204090203 77
    0x80c580241210002a0000003800252a11030003003280784008280e10003049000d0900c40f6620765041e96101c0c58049c40344200b1004017405890b06400c2070b91a01440c07100e65645015030601401004e05e0348440d01d595030b000f400c1d00c82c81e1f0856050401c203010060003901e01d031001e90b82a902c090a004141c8480164200c4025a1561213219400d050842c0c0c0040310588d948108640c44c001c001100e0b49645040c2041007a10070600151300081d5680004050303d07000c02c7e00c40b80c00c090811000c05190070316200420600840103220100e030000003520034030240508404800030f140a0709403c4c100b10190300c0340c0d0782c140002000444055240c03860385000c540f2550480d15001d0723201303013169240c2c141051070303100c0d0810b403440c101c1c0420b86000c04200d44e4a40011020070201ca102801c240001d20103040c40000040030b002c85082c000306024035000381111a61102000b4202c00003001c040d851070030000c3c00c1e604031000c0c10042c14810020700c4400d8035082d4020b9401a010754000c40d00c40d482e840800d213 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 484357517 1250 484356267 484356269
    0x51f05040e010212010f050405010e0f0f06040e0a0507050a050f01090b0a0207031709090c030c07060b0d0203010903110c150d02070515010801061410020d08130b010303091701050609061306 83
    0x81c2d556a04c030004205800102c111905130f83c02540c0800140c0c0e283ca4003010103a0041d24081c00100e070790f2001800200340d901200b81d0003100600082400500344092a14107002c0034803c4843e608043c13020320144c10001c82e4100144812945002009001070010702058054060184401c0700094004200da0007004518011544080240c0c0c928080301d0303014425410011005200d4174070700d0045942c50344503a00383c9000300c07907101e480c83c0341090507640c0c80700508100c100f058000150340201c0001d030f5405e1190815040c020b4860803c807200310203400c0c0c2001060380380c01d4882c0280c0343ca0b48007248025419103c0c104001000140d44010700e04146160004070415282219480c0001103500b10040d00404119410b41d1650000760340d44500700100c0921014030440140d1040c440480b0003440b0700f0003d6000b80c100c110080303103620a52100f61528209070010b4011440d0140b080005002010f913110030b04150303800030096404e010740050445880901034138800e180e01c0340824542c10003980100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 484358767 1250 484357517 484357537
    0x1308070302120301090f0b01030c0905010f140408010e06090d020304090b032515020f030a0c0f060e0114070807020a29150a15090b0337051f05040e0102 67
    0x1c1c0c83c0e603555000d400142503500741000a26040c1580030b480c5500030b00070b50403003080a8a400c0a03107400d1078011107000d642d150b4107008010343d008100b80c0150b005d500900c0582180303000402c810152040041c907210018001014561100c0036214085902106940c103a81c0c01080101c1d4102c20f42c80044d28001041200b074031012445611403480030301d42c0e0b451008598280c100e503a01511440f00c2030340c8821001011a03a03c1e0003c01110808910444142c40a544241c900035025130ba81c6d02c51108075140b4800188190303540b01210303101404820880e507404402c81c60030382c100d03180c00c0390002d40380e640781c400046c0340018251440d20f00c0340030141f03d8000c4060307480e80280f192828030050501942d180f201e00703004544038040801c03d80c1c00c4a5800c0031764055500d5824000d81b402d600d82d02203505c024602205040c1c0d001c80100c10f5440b0410018400c845d010f100d41d03500042d40d218100301c0d080507004170b005940c94107480d0720342d40c0218803032400c55008590026528101900e40c0380a84200f0b4203030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 484360017 1250 484358767 484358803
    0x60609050603370614060f0a06050304120221030f0f010302100e03011b021f2d0902060d15080c0d3002030c100b090a020d0b0a0f05181308070302 64
    0x14005940d1403900c0580325090484034520901d07020024408952350341e000d4000041c500300009400b15460304022080100e00788100d601480380e44001421000e000012003050750000000d001c09030522076400780c0c00c407a40000c088819491540040c1085100c0305940302030100e0100003900c40c0e6020b42c0218890117521803005100c0b0400c0a0003520399034503540200312080c0443d00d2100c02034030f07481901c03910010001110302a9021420180b01503101000d40c004403511100e036840140c503404050504043c2103a0080f500145001c0d01040811180d00400c459034441100307003a82c1d690f8520900b24217600020003d440e41c10407204280c0d000c0065203401491044e0301302244506074004014030316a00840240e4104000a0f42d5034030594600c0040103900001110101c3e091175a603500410b042c181e4048000340c01881c1c1c2c804a001010a544000e0a08981e003030200b000d0308102c1184191401c018441c0501840d1003111610240030400010708098070100c1c507002014020040310207008040104e1f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 484361267 1250 484360017 484360031
    0xb040507090b09072001062610021617090a03030e100216090b010c020904030c0215160809060c0d09060f081e04081b0105071b0b0117070504090606090506033706 71
    0x108230240b8941c41c40091103803080d01c03810151343d107003031090750144901ea29200b003003000f00d5110a40c038030414406904c1c1004c401c0080485644c0c402d11020002d601c661200c02d03610010030300f0405513000d82111031086d904030080060842c0400390f400e2080d984514400504481c0440040703d0110354084000e4000b0500801e1005050701310040d05641d510864084d882c070b0000c0440001070b401039040e15440c1812140000c00026091000350806880141c801070501990151880c40c0c480c00304042c0300421620034040c04034503400b803984054001c460034040441c0c20200c600071003030301c1e11074062981c0740c0d68003010900b000341c0c1000f100d4000780c000306170b9000881c849680c17a0080205840c2c0c076003c1803084100d9a14074040e07070500e090440d04107017129216841c14031011304129201b8555040c90207044030115995940b0f104107a600c0c0d003c2c2d00000380c10b50074440344d10111180582018441ea118007081002841d180c5100076001c6804025804804080c81205521500f0400010203803810404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 484362517 1250 484361267 484361309
    0x20904060b090f060c0d0807031404060603031808030405100504050306070807081008060a0506030316030801081b06030a0b0a090c110105060a121e0b040507090b0907200106 76
    0x201514540004403502407500840e0b0013046920700c0b4940303480000d9004801c85000a601640b521941b110031420041440e0845080c1100c07141000c4400300e4041e0382c5c820080c001e156100d01e803c00c0503030190941c0003049051920f0b2543e207021b9131049912900200a00c8a8214481e4007601c0040ca4054100d901e203061a40c000307032401004070780140c0090340d120000f521111611000c00e0440c0e5002014109603140c1503d40c41c041e200040c54250584010003c03611902d007403400e820b04050181c3d548280c2075040180030381c140203508101000c0720b100116201c02d5a600d000889400c52601400042c4086100e00440c0150399a90f101010481c039040c1041409508084401c44810105008000c1603803031808000e520301c110b0003640561090b0303108040025400505484e45284043c1460400642e19903030003841800469040703945030042082040812020b010340040300c4012540c0584600c4d102074001c0c40220074885140d8098a80c40481c4a040d20a5201030003a0080030760394202c140d5004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 484363767 1250 484362517 484362539
    0x913080406171f030803060a0305070909020f09041a1810020306041b05041809080403081207090b0f07030e10020d11070302060910050409020c0106030c0602210d02090406 75
    0x56400940141603100062403181100240060440e003416083d191a040da03e0312041908001c0185030401c0d4140b9012000c6441003009800070501c881c808a0110261710501005035444100c01d4020003480d0b01b4000010016501101d048425048145a55441020041d040640682305803124000c000fa5504013800c40e400440c404e84040c0c41c28072800d000301144580d0b043c0c2035078242d000582e00384400e000b00060340e043d030035140c83c15843c0407030303030044540342d8000b07962003035104030781100300080c0b070854542d040c10700c4603403052460509820301d920384040070f551485416180c4140c110005242d0f800c050203100034420101c0042c0900d1182c14a9410107552402d0f01d40b180c401140c418a87c1c40050240099100f0030340c1d60180481d4142580282801200c4c0380941114083c44010702001c00c0d500011310141011005040000c15590f280d4101941140640e800901c215003101d5600c01d040c204c3c0c204030809010800021555803004c46540c00024086c02080c5d6030701600b4984002801d02c118 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 484365017 1250 484363767 484363787
    0x4060509070f052503110d12020f0d060f1406040f030206250c03030212090a1404110f04030c141e0114040305030c0705030109150509070302040509150708060105090913080406 77
    0xb43c40c2d41c40b144000502da5070340c2c0c2001c0c00021000074046211580302300e00c660050140211080c4149080070200260102a100190800500c080c00d0003401c01828003025143e140800064032042d140c141001d000c0c01840f0314a00010b4094840001e102c2d0201c1c204643c0b051079089586100207040c0604e107054540c0c03a82a10040e401481040318400144c0703003510031603002250040c00da00f000c0c5d14088446101042840c005640680da034458006501c00d81001068001c03080e13245199101e0861428202001c0c07582c01c04c1c2c100f0b404400c1c076600151140010030404031000760111074622100701c0101c51030550f0140015605002040000422100102424004200e08140d0314a99140c00c203240c22644803860280000300280000052884158415a00915800d090362445520303a0086002e03070384244c1e401c04041e40201e0b244000b078a100d881725500704003035182105060901b00f00085c00c50092040d1540b0840c8144003040c070031030303c982d42043c02aa01c00a619202c56903184058102124 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 484366267 1250 484365017 484365023
    0x70c0302150622060806250c0f0807050f0304080a061407050f0a0e03010216060b0411190306120b100608010b120601050c072304060509070f0525 64
    0x26041c2401a2480400e0341e8a20035800030785001e0043d09400c022402d0071004800c0c2100040e503071403001c6444d05007400703964425001c507030703410380448142c40312050406160242201008200c2c001000003849155022140c1c64001c000b03a80c69601d1414001d0800513454500c0314148000240010508030100d01d200e40d11303020340d50070030180c14032200c50103400c14100c4202000a10410410520351108030181003c50502d15118881850b584042401ca9000c80200d11507102d180e2078043c100000c5002d005601e00c2c0a85007440014150748501c01c207806004028420100c0c01c40b903541c81e051182e8000c100a240c1d07400000340c1346100d81003100100006a61000d810301070114085070460040118070f040301c181d441410b00e801d0b1101e0003440b550a000c3c05c1039040190800414482040c00c00c030351405040d150b0455000b8001c000e0648142d5140020000d0095040100410403a9200c01e1034550005050070211642c41c0d65900403117076403081e000c49011407101580c1120303128500d0110052500c2c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 484367517 1250 484366267 484366273
    0x6070905120319082505030609071d040e01140f040c0501021b0402281e0c2003010603020a0b0301082122050a0b0c100207030c081809070c0302 63
    0x25091a145031644928424210300d4003441d086a801940325084203541320b0b0010110105c245400c0618001400042d08040001000030051010a180c0450081e82207003a604045500280c84c003182403070303c4080c000f072902c19980e400c40000b0b1031000303401050604412074402e1140d898500c10515484400b514191000c40e966000401d0301d5000094404078040d04000e3b0071588a50001000082e40c000100e0b95803103141d0300a1039040c0301080101c12440410f07900c032500b00e101000361010111041d820140c0401c40405903078004181001d11030004134a200404086e03003001480440e000d810940e100940002c0740c00c2c00002c52503803000145040e2501042500d41060b109204000000c202c141802400c12041015680e00c0f0311410310071542481d40a40380031203a65450000380302d04074903032110154031000501c240071401d0a0091108048040808600704006524024a03641c15680001c0c820f90000035074010341c070041c80d1500c2c41860001d203403107544c3c5001c06006156092990302200984 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 484368767 1250 484367517 484367539
    0x30b0f061516060e0105091207050309090403030504062d090804120c17030a09050402070302010e030c0109140f06071d1e0103050f06060d0c050c15061003060303090506030c0c06070905 81
    0x2c40706010b11b90055204100400041c07078402e035100c0175035000e84030440c1d091000b004140d440303440b01c0d44071520a90080c0ca000503a4a03290901c0c206031100c0f8840e6001d0890307015005c0c2000b11408074022a6110031a4000508040601c3d240c1554461a0051440505002465410403520540c1503041d80c001130f40421032000100800d030f543e17000302c008100204e8070f982c10070b0140c0d0801781c2c0646921030181c030010508840c030384030650856012082c0f9062594440d80c21500b40400f002245c07040c0c0c2c6001c0d00419512031031003800340d115176010b0114000c10223541000500d120301908010144d0700003c202c0e103104a180f81450703401d00d1071524614003290916000030007a0911081d01449801c02600c0c0b1803400306400b074120010880f80001106211080c814841c0300201000002902800e01350f9000143c1002c1041010340b51207a1100020582880d4061000943c040340c00d0b070858070161400c0b9100e486005241c0d011b0300a034000e030a01361280808104102d03501092200c1240c4042c0e441c54010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 484370017 1250 484368767 484368791
    0x9090a0323040b07080d0501091b020601181d0d020a120309050c060a17090c1507051b060f0a0305011a070f020f0f060708180109030b0f06151606 64
    0x18403030314001d409412040c0810800c0c8040c02000380314a500c20441c0d20314003949040f40600b1500207070005540d590303403040a4a15140c100c2c0744400011040d0000300700310761400300a112141900c01c1c43d0a1940d44030b031401205240c0d400d40c0240501111810780b8041c4207050301c000d50340d00d05e003003044e10b0141100c568800b02c0c2d4000d208411540390040702424016038900144102948040000d104210114220441400c000e0031907602694005001c1c104200c0d0810400642e1205002d240d14403010401920000910018407810040c070802c0a0b00f4416246400080e41c070300a0038281c03100072b06c000400322803032903150303001d18140c0d55800c1c4150b00708080542900b416005840c03006104203400c4180a02514040d00311520f900e43c000d0601e00650a50360100d64190450a4122180c5002041d141d26002c05070b440c0103224203080c68021101480c1d5251005003600103440c83c26444244000b0404980b10710203210b880ca407403002d02a036a520040307166854240900c0f0252112450000800303d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 484371267 1250 484370017 484370057
    0x24070210080c070209090c031204030b07031401140301020409020d0e0706020d020d0e0316030c180908040b07150e0a0203070e010305070b0f09180a1b050a0c02010e09090a03 76
    0xa02403005450f050071183d60a002d694100500352a26901c0340208103a42603808012807800081004030154540d451807400c0c624010000d80030710245414841d80100c1c04922042c0c681c1118540c0100c0350550070f61501003070092040390014580a4000039000540d00d2058011180c1c511421003200c01240e41d511080b61202d40400d401070040e044245503c5d03c0f0751041c10a51080c44006068030394071415500400e2190035564412075048407035003820001c54010840c85c4407401c0158900b07101007905030b510584603124902450a0024001c1421428018580c9100003016907840080040b0150840c03141c1d030300c51041074228424424100d011800f24815000e25049a034000010140b0320705200b0841d00304e800040140d801078501740031000c0c0399501c01c0120119a48900480316007414140010420754841c00420501e605e0f0f0402d10101059112048400184443c03400040690140c40100c0381d180c0c4502d1540c0e403016503241071009507030012580840851003a01d41801c00c00189050080c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 484372517 1250 484371267 484371271
    0x10806060405060907120e0304060224060a0608090a020d0b06041805070e040302030c010f0c0f021b040f0605030321060306070c03051e0a090501120212060409022407021008 76
    0x500300504c040030800316409000c40e841046503401000c00d010300303801ca146265030401e42c0308500591000e4640f0504400b01c0300790781c031440a6194081d04600c0c00401040201e80d031841214104504200011030260043c8114901260b00411014800101c1d0130a1143d8801c01d440c1c00748a1860f1118410009c00c04135100a48603034094094420345281400044845400034825401c5d0b0004000780030f0051001e00c00d80c118070010400c0060820350300030000b04001c0c0c95a10301d0055601c0203010074030070300e8401040c101d03400b0b0440b00410600492064600501015841030344c1510011134080c450928032544900c1c0714802e07680b6504030b65108020555210015034048021620000c62500071a10034401020021140ea51404403c41e42c41d480c11410341c4268046030014024440c14001503030711010a59240f52000300950038215140d00600c40d2180203404030744910b42e5400000215265250160f80300c00919044002002c1f00701d062603420f80c0421400c0344103030740e0780555a00c0b003400303071107858 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 484373767 1250 484372517 484372519
    0x1a1015020d0c0c231906091404090816030e3313030c1503020f1b01151502062802030a06050a0f0e060411030c1606110d050a0c02030306010c11030d030501080606040506 74
    0x1e13813146070a5232540c0c4001d500169070740280d00e895441012900c203000405482d200794030383c50f12a0055081c02410480100e004c184182e01400c82c1c010b5070251074810031209500000c421038104030400070b802040c400c200802c009140d070f524000082c42003415a12003128111000c0c800b403580d17070400071400c03482051080e14120405011001d071008071506000d21340c4408a00001d110075110100c43d078150125800342c15141c0c1c0182000213100d605009041c2c006002c51000b0149901d9052034070004204141c10728001a4003200080241e00d440d00f0690090502809a89882c0c1d00e03149581d02c174038050300522140c800c45401090450829205200c5024100400d05045460341d50b255000740c1d210751410203541c07041000c207801203426442040300004403509a9540e032000810590f068603001030004100d0f80c0760607166940c0c1900801100c4d8810001d1800c0d40e001c41d078518082000034041c210807a0940b151350031054103d034043c0d00280c10384004008482d01955000c0421042e40c504031102 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 484375017 1250 484373767 484373777
    0x2070807030f031e0605030d080f06011803140c011b08040b0f0d0c09180204050d0b1008010501121110021e0a1a1015020d0c0c231906 59
    0x1a0340801e110b40100440c1100701d10f404151014a1807010004408a03000c1c91045540d0395001c100a00e02040500e4140107541040102e03850880c440e061036040c014441814004404521003c2e0140c2240310000786501c1240e01541600d4266260780d21309804c1d4103103000c11103001c01c103220700130107441c60030034160301005043c40e090070010002c1094100d140c028040440520006c1c0e0114032501822a15100390740d1140080c0c2c2c81e000d5824420030b11070000d42c0315544104414821501d82c0c032240085190490000c03481d40d225400300da160380c0540e0348501d010307521b00000440c59454900c8528102030261100c0118084100308000344a20884101c0015921420418201a550001c410384d080c15a0302a113540810b02d803152000c2c04601280100c184050f0010844806169408580a00714410059400a038900b00184d80c8142e07000c414000d10801c401e000d000c00c0b04070a414000341240880c0c00c42207952120880c00c6401d0580400c900c5118902201c0c0ca0b500c400714500030480e511aa10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 484376267 1250 484375017 484375027
    0x1a0c0106120f150f02120a0b010e0906060912060112050c01082202040b030f15010b0a09030303020f090406031b1401020304180b0603070513080c01080a020c0a141e01020708 76
    0x10340d152a051842d10310040c3c0d5124011914442c810384040c007403089008028400324641140301800b2298800040307030601c040d41842042d5500e851101d180d0281c01a51165a202400b40005407050090911038900e80703d500000300f25008150b080300f4903244141c0c2102c0e42c610b07000d8010344583c1e1040351001c514413000c80600351030b40d01501544581e58000780000032954808008a801c1011140700d421444c3e100d62140703460b0901206107140100b40e150005070030300d440840000c0000c011031101404141c3c01003035203a1360b82000411031310043d1004000300551503582c07500d10a1684400350b0b80c00380000da000001200031142c81d020212010580c00b0314038042c107280c0609008208001c0d10301d02d03207030341d20030500e01916920002c500030907540d250725403900c0d421260280000c0c4150080440364000061306c11892360000303499500110410030250300c1c0c441c80000c0303a14091003100098645031000b1350541030302201040407001819002d912801d600304e140d0300903081c1d00c0782d42e000034820042000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 484377517 1250 484376267 484376273
    0x3090a0b01240c031101022101080c0a0b0307031e050604050a050f0622060902190e210f070303050901030f0902030d21020f04170a0b040204151a0c0106120f 69
    0x18408203080c131900340460031500c00ca40301801ca030440d040c800c4003803408020820022010b00c048a00518240d00109201c03034240000c1092f20220384103100f0300720710110120ba5414041d030403006441d56001c07001e103c80b0049050441c090203040da04d80c0d004a191402040e869455800340f944180f008081410042d01e071101400a0f51224160440c541d465171840c41080c01d0041c02450b00070b20901d0000b50712500400007503000307507111500d4030040c070101d5201040c054543d12044584240c50300100311151118154150074003014072000c40b100d0140700008000c041e0400c0260010314402c0c1da0030441d4401d081551000c40301c5282001e9415800040e082544900c41c0d604030181044541036402a07940c0c0d90003090517600540d00d401b022400100b0188800c182c0c68030069a0555160700130110b1001c26154801546805072000e409030b5150045617040000240c3c815008000728500c4043d80c0040300c11546003500026445016075080c8072001a0074252400c80c840b1031900800d802c43d5080c010b41e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 484378767 1250 484377517 484377527
    0xc063c0c0708041e0518010b07020103060801090f0c09020c0a080306120a03080901050708010b0304030e150403030801090b0d080f091903030522080c010804020f0603090a0b0124 78
    0x6250316420841004003100246000d80900000c15008501240311000e00690001441041d005907000300c00c001d510880f8080540d564034115a0180400c642d60b01c8a0f0004030080c2c0f203203070810150744d0b080800c04403c0086503503000d511140184c0448100540312540030040c4d2255048142d2103a100f050031b040410703811001140c000000030300f070000301a85082510b00313150002100340d0109411104000b6603000c20b00405a100c422450540220740c1040342081050002a00140402510900c010305c507807541810100c80c2c00c00c1c0c5080a890700e51700c2ca030007000032500b40100c05855041840c0d0b0161814114450001c1c15032080301c0c43d040c01a4070f07000b015076801c1011555400500091500c24002c0d502131080080c40c001d43c0c8441da9000702c4e00c0908840410002c01c1041c081403407900304000b510214981030104000d00c4c01751815195030001030b42003080c05452550021001050056503d00001d15200052080d441e0020581c9e8800c1940000c02c5880082600003444051040c52540300c0c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 484380017 1250 484378767 484378771
    0xf050f061306050c010b040513110a09050c070212070807031401020909131103070501050a03110c061e0708070806040c0c210e09100614040b0c063c 65
    0x904410308000a600a407000c100040e44100045400050103804080c0203000e48001c2140a49061000e03090030301074080590158080501140002004121180ea40d002e0700d400900c0d16132414015800c203910315040d1540444e074120301c6611840282e503404c0d6001304e25072044406410103407440901d10b88803c91100542c40141c1a555402c2050854582d500c2c0c50701802611401c00911640c850741c940080100705200c10144660720051042010303a030702c001256050120b9240c0840d644844044002190050280b620700b14007a081c00c00012500010400516540c0403400c8941600c40401c2030f280d00006441c21800200300c50001201c3d814550480c03044042d80c0c2c94200ca0b090340700e0f19200d044921100b8081315017403402030b000700e000364002404c031401013040f02d040a003030501c040030b4044510148240804e100c41041001c4142017088140c0d00100044450309603100d589008150700c2e8901280c1103081c070007820300030801d02110307845080c509088421034801198101da50303091942d580 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 484381267 1250 484380017 484380019
    0xf030614042a030f111617040e01140907140a0f1202070609050c0a08033408040f0b191809020c0a02130b09070f0203070f050619060f050f 61
    0x41d1540901c0700c550b14040d03071111450380c0c0e40003a030400c0d500c5100003501c1700e404400c901001c042c004404a500321000761002640d22200e84200c818110841a0311401241e10802c03151282000002d0400619007001031000c100302c520f0807465540b004103803403103040501001c088803070510041c489213020311225040d031402800e140e400903428820306d0040e07a01020080300c0158030b03040d116042003810414203d000508a1741c188082c6e080c20222a40c81c00f6000007800141034040f150174480c020248182100710f16000000c10040d05814110703019402031080804000107044001a803040c1d0600362427462243c1d240d4002003188084088448140a41c042c40e071618043c0b400042c80e45c070030f200410b450b400c14005880803850702d00400003940a403c54404c170701818400521100d5852100303099000c06c060910000f1401c149c00100d1950044800c020401c1d48a100c400d0240302c8000340e1940320301c10302165416004010300c00b682c01c1d600d1500c1141094510510144020318000c0c07a1070340040c1d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 484382517 1250 484381267 484381301
    0x102071d06041512061d0c091503010612031209080a05030a0f150611070b1e04050306070306080f07060503012106090605040b0a060b0708160606080705010f03061404 73
    0xc500708440e1100b0f0b405503c8041d4107103d800042e01000304601075081c55420011403890000d0a01d02c1c09521000040001ea00c9042140300051081050358410307014024050001c10040346c0760b809040000d0700c40b6205402080034900d0101681c9114081c0915456000d21041e040140c02c15003078a2a400281c40550030585509082c060030b90f0510503d10b4074088007000f1301d469460104040c111114600840c6056000000140b1501e100c100480d00c82600850354600b0025800c45c41c90250700468100c0c0b64540910b100707100241c1d901d50404010349a5100a80e011200b1a46203103641d0380746481141c3c0071480c103200421001032815119101d6030100c1c0414001101c0942e00c042c12074842c050101c40d0135640744148024407585000450340700020307003030400095050603042c0206010300030340208041e00002d50b0441c1c00c40c80031031041810381d0081d81809402c0c1c0715003075070752109241c0c018240000d0342d8010381c0c1e03500c034800d000790401c8a11400089803403201d80420300000c1d2211402c8003007511 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 484383767 1250 484382517 484382531
    0x3050c090904050d12060b0306010c1a070504140f0907200307060603030f0206010f030602030703141501030e0102091309030903051b0306160503070c15020d0207110102071d0604 78
    0x41c4070101d400307101e148900701606808250502c090040c44036040b90b04109490a88240907082c400c40440c7d80060b424208030400340c800345882d641d9540480440341c2ca40718841c00740034200d0340203c058410f48039080c1c20714503144888002d0001600d091000540e10000b6100071070b006c9c500400344543d07090809004041240020b020780d510310380c0003e07012150513603651b0040080c181d11503402640c3c01e04c030784042d10295142c8050702030400841d00025002d40d60000100750315038005e6004050218030440100064a04100c2d80c5501c52051070303510740800e0a10b030100301028410301c00c0700c0788220024864414415014485002413180301411000d004500c000400403032420048815840c420b41115000040c104081c103080c4200644140e00324041c035081c40004941100030303241c0c000e403589800018100241003500e49015080c109a42c41307407000400f64015501600185022401018200f031106000d400482c0d41c1c5520f4400c55204424007404500c2c01d06401d1619174000c540204081580 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 484385017 1250 484383767 484383769
    0xc010e0310020a0507020f0108160f02070e0103110301061a070807050309040e1612030f05130306020a050c070f0b030c1602091003050d090e06040c09080d020c150a050a03050c09 78
    0x3e9114a5400002c500d003c01c2040441c501180b200003520f0080c6050922070604410840d5681e00b07645041c01444014000d049030309100308854002405400311003242540c2d03030301701821020b80403985207000307500b000e40c00f040d00a04104204982c0d00c0d0509081d01d041c959841792021904525400c480ca40410000142c8640d038600600b40c0d402060805010300040761900c4c45900240740c0d00c2400e046600c11044004260020420750020000b8240389607500403400b024021031040f504000c00503440450380700810382d405406410b0740101c2c90304841c0762130340b200561070882d8a944110b03500d61800b000041c09101c600009460f001403100b200e034400180681c000741180804542002c9000c091100c10028031004100011043c40c0c075050031804207003000081310246800418480c02503032540c48200d2803074426003042d001410602c0580ba1888084000291207210b90040d05d40300322178000b4101c68480000b001c442240c02c058031003d251816025041c0c001d0040213156108107482400003001c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 484386267 1250 484385017 484385021
    0xd110c0a090b030d020a020d06020304050c0a090c09082a06070605040b06040b0405060a091e0e01022a150c0c1501080105090127051213091d0c010e0310 67
    0x2910101c8404540308440c001407614120440040c1c070308540c0700180600c0561510707a5440100741d00190007594a582c1c9080c501d00c0d024410a405400000415001522000940c040364071a1543d907101c02d22660303208001e503034030002006550070642d800f01910702c54407010b40c400810030034007500c00c505110080c1c64060031104125000e076140500202042030b1440c00e88241880100c00b11000c01641c00c0000c046513240d00f0030300074451117964500d080b201006614164840c5041026001d0100366202c03031826010b074009070b803000c40911034095440d00b22040c0174211620412418000d0944048020150001c50f030b01400007450000d04220a2034141030a0100da0100c030030a03648103140c1c1d450f200c41242110b500800780035861340340280511292103000d8283d8000e00b40200d0402c0400c0c814105241001c1082c124021284400201c11740d44585084580381200c03e18601003013140e00030140388446180c0540c60400580000ea200903456006504184030b4050150447c1c104511032070306001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 484387517 1250 484386267 484386269
    0x1260601060f02010501050103020f030406050703020c1009020a06081b0d02071202060f010b03100501121d0d0906032706060b0d0204090506190b0a030e0607200f0d110c0a 75
    0x142c4126240c40d55540900030700e4014031003031a04502e0003401010b030803064080544020a840d48603008594030380d00c65010385508210381000d540252185030200c0005002079802203015036060303000010764600562030148105126203002d543c461841000705420390141009014103582401500302084d410820240c441120790020f208508010b035400002d40710503030040c3d00d200b50400800112401849240d411180d00b824101840e050048152000d8084500f006154010560f05a210120001410032101c0100d0701c0d003522694aa660441c16074000190040c003481c5581d010900c11408400d001840b140101c2000075502d84481d43d0045603403240300355000da181c02181c180004141403090903081501100c1e035010015680d8009004006244500320b020200403a50391083d5010381c1191180040e980c4c00d8849500d00180d001d808110080811034010808102100000c40001001d404c00d100150040c000c0f24000356040317807520001b581d03040c0c0310b0245500c10171054403101e40d040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 484388767 1250 484387517 484387529
    0x30f2d0109090605100302030705010302090301110d020403020a09050708010302090601171009182105280f2606010c150b04151d10051809160305030301260601 70
    0xb1805040508248098070406000322040e1150803500700b0069138006507090881d00d00b0308000d0380750a8050000380c01050513010220104c0e0b0006a0340903101030b141e000f4810351b4030031031305001400e0700d400900c801c403031003120754801003123a1a00520151800c50646603002c1c2052401070300909282844510141c416541501a20123004060100c00443d005440c04049041d0940f0b2259800d074448060a030400c55403590520209400601c0132840f0304100c07452901560100310002808502c01c825002001c000710002400d9030030709190051080b555018105550500c07400d600c40701c10701000d1841c070040c0929040c0540030303201400040105048a01041040034001070b528820310502054507074802800010500d8000700380038030301c5848020030809440e482c155030715960341800b030040c04e515500900d80c0f00f80490825100c1d412103200852140e110724090342d407048031040c1d204945500701d0100428540062005000444241d002886104840d50700e11200c0301d501005941054400e030408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 484390017 1250 484388767 484388771
    0x2030a0b010f050d03140306040e0d0905041d0307060515030d030e0625030203070314090607090b030105061b010f0603031701441605031002030f2d0109 67
    0x1003000300295802c90004280039544e00090080b02c1d600240403c00703003240889611008400300e111900c45902c14400c80c0040800c581001c1c0141c00080c044184505c15180700d14104200c040149001014000462a1081c015400c0082c10740c1d86c00041d080c020b115001840070402e107151076a400704070719258904640c03000112100d44030361003410700300300911920802c0f00420350402380b840b003480d141d500701c450342c60b006031640c441d807400724050028903498110f64000d05007401500d03907000c40c41c0e6005030b0103034448802c0c1c6c41d030340c80300400140800d20070650301202c2800805682c01c10f001d007101214204000000b9075080b8031151004441e400d4000380c001407084130000742d0340c03400241e1450140900445040b5407207407280040f841b1210100580c003046100360148508200c0e50000c1840590101c02514001c50340130240306450790080c4912407213481181e2106101c520301d03100b03e038001e924042d4041500d0352007640c280d08a0718064000e8000d910111b800300e104208904005010f80703101040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 484391267 1250 484390017 484390019
    0x50a09021e0a0b0c0322030b041a15030d120605040e010204062c0607050a120305100b03100311030703061a1813020405070203090d1218060c11060702030a0b01 70
    0x184901c8200036000b180b010f080c104001c00d0030303000000035980c20160b4034003007100014441c3c40c1082944181d0380000d080185582c02e01080144031444541c00c03d41c2100d00401030303a150b02d1404007819a080140c0e402d9081f00c03651348015882203000341c604144110000c2035990f699004603040b2951500d01401030b9501160a100b040e6104c00b0701c0740d490504103ca02d0182103261070104551a00007100e07846558005480801c0240038019605040c3d04001d400c50f49520360703800980a40412111b10103211203490012901002002c2960f0241e002d149294040c0c43c21651480140d03420b21001a52511603148004005105406401032089a015078030000c0b0200c1c4090000008101e43d8070034120f08004e00308502a1140310380c3c402825011107000c01e850310389201c213a041d84174103c10207070030508040e030030000e000c282100c407681102503a650404c0800500d00c103801d4456207015440008511806075400320794551381c901e14095008102915004003540080d25015050304111180709102d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 484392517 1250 484391267 484391269
    0x1030818030f01140c0711040203040609080706090507080708031b0307150207020913051f060801091110080708150112050403210e1f060317070507050f13050a09021e 73
    0xd501750048088502c6038188000381c1c2c0c5aa00c00c9100720b074214056a07000c000181070220315001212040e80181d00301e9500c980600b4a6005000f0703030403040c0e0b0144a40c1c0800103051300001584030840d001c40700514100440f100c00510341000007842e640c001e2005000030008282020b45800703214215440c01030f664800c510502010500c010b1507122400c204485800c0030400114000490352030800c0e014030343c1c031a6151800c0c001c1c2034603008014298070b0712880008000c01c81001c0b00302e00c131041380c44810300703400748508407001071044408000181591011900c00f2000704c50202001c00141050b0308840c02010380a0110f0340116002d800203200c810b410b00c0b0000f075407031088004141001081c40003811018040b60ba5a060081140b11001e04403416810b195266020002440d8061a240360386261500c0d07940568104d00b0701a5031a0003a114009028034202d0206010450043c0104181e0401c80190900503c402850300c6a85903c07103000e00b00680d52909041d80560401e0710004051407084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 484393767 1250 484392517 484392551
    0x30309110909071a0918040f08130501030f02090a1e03120c020f04090206090609030c1003050f09060105010801180f0f020d230f0711010c0302181801030818030f01 72
    0x130541542142c002c0105116030340300d500c1c80e0702c24030040701245091901c6038988940051080440030b000c800c00440d800e05001400748110703045a809980034800e643e56001d80c807080744220885198001d221950400003000001074000c09070303881d12031000c03409540b0b8448004401340d81120302d0010f07011074100001c6140404034503009000581b4100221042640070072414800e10362132910601c2c0115000b5100d070b400b000110098000541000e00900081c1c0014000d0321301903500343d42038803545000070075203c40055218101d0ba8141d4480b48140d00c0c02c40307202c42d48440ca09030012641e80360550351040c00120300070140d40407000301c0016038900003400000115484101d40003030f20700e450341044808034600e00900e500722031621080c1c1c3d0a6103611100b59032071010b2041c81651542004a40c41942e03800d0b5000c2c1202408080c4d003c02d2203005041040b00d00300380300340000075a17000c0b5001403000c20440c602401000201c40b096407407200ea5440000d29045c03142400d00701603034595440001603440c0c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 484395017 1250 484393767 484393799
    0x11030409090308010e0f190905070b040303110a050c15160b16020f06060f0d200a06090501020a030e031e011e090203030d050403051b0d1d06040303030911090907 71
    0x101150750410304003503a121075101c10192180003400c0820904026500d2588d0003d185250301c10200c543e15a590040c00c040e170340182c4001c0d000718040110020112a000c50008031030740d440000b6000440103442003001c032200b000e00c0c10824103824440300c01c01c800f020070400300e014060300c5042d00740e103404043c9941510141d407583c1c085411507000110441c44c0050070b26081003080390034901402c05000410462284040007900b012503100c0100b10310102200301d8083c1603810b5810410440c0c0319401620419180d204540c01a484001440c011034450741f002491420014203907005e01c1320000d01200788040d036130702441d220303551400030b00c080721b0f4403440e4840c0f00d80403803000348107040c050f800090700e038000c8912404c181500c800019003050302c954112110150000c06400301e442284600315039400303405080c40046440c401951030500c0e440300c101c01d4010b500500880c0351a04603901280549001c1b002200e00302490491f110555a950116030302c035a0700e1400409500d464110800f40103140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 484396267 1250 484395017 484395029
    0x412031205070914060903030c06190b03030f0a0e130f0b0a09090201090501201009150b0a0504020d020904231005030601060e1314011a090d020108071103040909030801 74
    0x1240f80100b01300c00e00300d02d9000007103c2c00c40312140c0b0f032031107140440e0452081584030740700350158000b00441d04074200c100a080c50710081c000c0001ea1403c03c141a80c0748224140c00341449024001d070440d0314424100c0031900d01014050424200c0da80c1415815207a01c0c0f4045030f490b5031121000441c904250b400340c001001541c905000301c45940e000030704402c85074010641005150810700c0b00c44000149104a500788002c2120221080c81002d00d0041003c484210f031210740d0909080b5940b1020700070100307a180e000340b0b072585c0107280c0000c1000a600440312074015640a1108240f00e983e60700c12901505103113074540320140f003440c1c0c58520710f6000410341071180c49100c60503c00350720000f4041b41541c0090900b00084110b500001d000c00e40c00c0350107900e4160801d8281d500e03104003941098100c485198051102102100815485000d121481500542230034100d101662045103200c1c0c2204c0d00303090181c3c43c03100d180c0a081c150340c801e40102c120252101201010903503c4400c039401442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 484397517 1250 484396267 484396277
    0x90b04060302060901080903161a070201020901022a0d0b0a0e0a0b070e0a121208070302070203100c050f040b180603190e0c040204030c0e01090207020a0317041203120507 75
    0x4210b5000400d580100c40c031150402c40030b4000110301050400c01c44485050441c14445460210b1802c000314045d85c038102c11042406c1004140300c940140203442c00e448050700a004490000303001e18400b401184501a210007800711114801e80301d0315120340d8414043d503401c0c0c0715840d0402c45803085e5204070340d8210041d4410031041000c0b910706804990003c00343c1c9401c3e011000c1020000700c3c2d188003a00041d5840400c0c02a001c2081415410324801c3da40c0c1e911180300c81d9541190940803801418800b0303405070442c2c0703145807081c01c0ca90710a00b00d1460380c1c20301d036050030307014000b40240303800580000d516145c0004410200202020400d0b007102801c65809246140811500c0c41024041000ea140c0c80d440d641c01c41c0461100b80450202040c0c003070b20840d280e581d281084c141c0603205204019130070035002c0010440b030ba00d43c001c43e90655000740c501c1440a15559808481d210b4407140403004c0f5105000118210700c060644940003170003035940d00a0320058000400c200d4001038070380000c0c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 484398767 1250 484397517 484397519
    0x5041d0a0c0f0516050709060b030403090614040b030a0609111b03090a0e07020c06030720060c070b070210090b010303170609150102030c070807061205100909050a0f030306090b0406 80
    0xa900c40d0480303440d66404561a560f5203000d00c0c00f140b400106c3c0e00b2000115081c110003040c851074607805144154029030365600d9550740c07000700783d83e61159400002c00c6414204010300c62000b040300250380140e1921000959580d480f0160300854003081c1c81000c0d44040021200d080e2502e220380e010017500741a02551402d4150030001e07103041c4c0180700e8100039842e00c0000401050007881245001c40b8041c050303540c0c915211200601810560355900e2040c5c10984100c03505101c0054000c2c0701c2c450014030607107800c0a91b1500c2c0d188a600604030030071442480d403034000c403030903c1c003ca201c04c0d8802d01c00c450706941507141c050510800350341c5c008074205036241085002e6071660b00198201c0c001c924510350313001c0c03810b00407070641c410b86000448902c1440350001e041c80000480c0b0048550360b030740d583d5070300880e20951030a8880540714444016004241808201c0c995071211110901c100212110300915075039034400d42c2001482036001c00d81c0d0301030800c071442441c0245181c01c81c04403020801c0ca = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 484400017 1250 484398767 484398797
    0x60109020a0912141203091204030b0a0518070801330612061a040801180809010806060c06040605150a050102120f07021203041e050d030f05041d0a0c 66
    0x4041880b585001420700c1c1000740078001a044460103142c4e1002c159000c0906410600e403065000307445419261040c610703480c003150b58042c10350342680e6000050b50104e484800800c03010304806024640034040c4c540300140480307002c012a0000b4034146c3e0002c5a0350161034005115808010036200742c0d520005480e0003000400c549420a442c2203082c09a40000c80d4002c2c2d20040c030795034001030301c2c03c1081060030f000c509094000c2c0007107038084002440038450b2070f1203401e0f85140700340c1c008150030014040318903958025695683d2000024001c181003a90b03961000d0b1600b40113807000d891032a510414410b0814504296040c00041035401010540c649070000b03584000120201c0c8401d11b0201f0711095402c0014112280e0307540040c540040450700c003194a840c0d901c9885404903040c0e44500b80d6010380034200e103d40480c1c034020f00318070b0f03254920344052b10a0140980b401040000c10003000c40e980c1c0041241c407501c6100e03104507205610b046031881d400c45504801071000d000240d5030701040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 484401267 1250 484400017 484400027
    0xf090709051909060209060703020102090f01021612050a02040504060f05091914070314071404140a0209151803120f0f07110a09020a26060d020607050a0b0702060109020a 75
    0x1182c40b1100e40016248034034100000240603501040703901c4440002d400c41450380c15006040204c03030480301c1041008a980040e6687c580190449080d0b04240c00d042011030100b03880301c0070250050b010340c1d003e54460350000b012104212421182551b4910880d0340c0d4a01c40c0c8074555101241e00001e15019a44104003895804654001020840d000802c105004402c0c4901c01c0210343c04404655618000c00c14140c950304180908940000c80d075239146d141d03241c64080d9844d45000002200240c0d22204a4080030f54403228031300380c21190364100c200700070303030240c00400042d560044a4107990b400142018180242d0102a91161000340500e0842c9106441142e060400e600c0e040c564031841850140443c454180158ae40311401c42400503140e1400e4005144408030381c0d48449090395030905201510b502a4000d041f492940030005140e4181280f081c1e40090005114070700340301036a44c8840c9482c0b03038601d007222920980024412040e804001e16800340c00380b98801d605180f18140c0c0205 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 484402517 1250 484401267 484401301
    0x504151b08150109050303030a1e09020a05010e0102241803072a03060510090e0f0705100c051b030c06041406030415051f14010c02040b03070e0f09070905 68
    0xc01030b40c078205103405030b0042c0d241d1402080040e042d65140c1c94440350303400040c001d2420342004510703015420031201c500340c401c80001e16802003e908a803420800111549500d030740c0c1c1079040d4441c001002c030300745c014105080310404202810034003510707081d02221408480c0c16210a403562040c4010342c00548030b080074402002e241c5c0c402c90702c0d00e030802c00e600c1c41000d01648080c111601c0c001c148040780d5103200c80306e03041e13548844050041d0300e00c00c00c400e940c51400400c2d410340f64108850522840c5040e070b150414012291501840d045110b846141c2046115510f1260626400041c06110b00301480081c4820504541480c03d10b49010107909645050b41802445950700000180400c0030303984541c601c4640e08423040040d49010301c03280c0d007a1000465148000246408001038242e00c040149100c1c55060791607001b00049a03003448040c02d00003400d42d60500817541e0100703042d80c40190300c3c3c1c40f038040b005451401e07041240f969800c1a50a0f00700010490030042041750303000840700042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 484403767 1250 484402517 484402531
    0xc050f030c0d0506041b0608070e03010b030d05090f12030a0309021801060c022e03390e040911011b060c050a02100b012304090504151b08 61
    0x109496100000181c140300c0301c1044960701c001c1081c00d800601000141080c440d605c00d1919000302c500301d02440e01d071103444e40b00d0400040c0220300040c500e80d12945101c0006100640081100c060120000381030010222034040050300100e001c04080c500003811407000d00003500d04800d20300001007119124030400003130b03100b03141d141e403030401c11500e0b00d186035410010360720741c0c1060950311000b006000440101c0181e04c0341c012000303400a585ca095030b00c03d00c1d02720b98407950030207005654410b90250405144e1003250500f003081d800840c051a000340b1010f54282000d00402d08076042c00030f491409841004c6018602d05880c2200055111544003100e031024241049505c00d103903402c079407001403088001d01d06410040320100c00f64100c07001d030003400740d11307000d1b194030085c0c40601c942210401190180010070080c0d0200c501e0607c400e20000c841c840d043c80303900d065100c1e455003054807000e807402c41c1c2c0c00e0003140d0360030356481c4036100d48003010030940c8030f04000400e00d60009000e01c002030120 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 484405017 1250 484403767 484403779
    0x150f011a070302160b030403080f2403120304051e070e2403010603050d031d0a1209030c060c06060602060702070315020403050106030809090136020409052a070c05 72
    0x1c1e60905008202c1403128000200220807241d40328440c3c402c4580040d030782140032034a00008103071a100070000c150301c14a8041a03600c1030100c0551030046102c59181c115030580194030340d108810000200551281d40518018a0069075062a01c041c014240301000301c550842c02003446101c001d030001a400c1000100d844001c0c1d410b40c40d200018441000e504c981c5503107040800000c100011030125100c501c1341c0c5081119078580c85140a441c0000d2414401a80140780110001560029030400d160518a0048921500da0352080c2c0c0ca0f440302c0c0c0082c008a28180110740401406d801b83e403024052610185c10142402c13800030750b480145000c01070240088040c5840c1d1102168184c400450300f00c4c00a2007019a6030501c001140d11154909008940c0c04002003194202122010004040001d03800401d00c00e400c0038aa4840c000c8a2002060784c080000041c5c83c405402070f240940d420689480440e09407000240b2912003200501e141c0103414030100c804076250384181411030b001a5a8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 484406267 1250 484405017 484405027
    0x50a030b0a09090302071401030e07090216021003141b03070f030f0f021e21060a0518060301140c0912030706021b060a05010b03040809150c150f011a 66
    0x956041e540b41c021006051400070044280340c2d00086860449444900b080e40700c0b00d20800441c00d452034501c20701040d40c4408400c0045030042e43c0104204992140e080802240710743c005140304140321040b4001a40301c01c080d0741400c00f0b20329a5504000d08a03506c0b4032581e07410300b10070603500000b820f480030310960845041d003081c040d8018000d00713044500200645401c0304884402034011105100c1c5100d40701c402d00700300d4180303081150b9450002c1c50b80703501c50350400300042d0301100300100095000684840000340503280c4150800201c00f0582e501d24041ca0f080040c903003120803000150390f500e6606d5090004110240044405000d402e840040c400758010803814554030808000170305962000407a41c010302c040e007010310b841a20340c1c3d05859094840b42101d8090322801c1c06060600882040850001202d981c002c0c20050009409444110403405000f02541c10040c04a861500018032150a8191f11050540d01c9085a9605009035051461024903541300c610b6407200c0b1440011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 484407517 1250 484406267 484406269
    0xc0e071803020d110406090e0c0a050102060103150f020a2127050708120c0708060103080406320315010201050f04020d1b080d0e06070321021c0e0c0d03050a030b 71
    0xf04d900c1c2e0001e009001031042a0351450400024641c3c24819039450054074900141440c101c4220300403100705a000307001e01d07400c58aa451015401c3c0c260701200b260341d007002080e141c8440c0083d0040c2902c3c1e03200c1c00b4404416032408001c20030908841c0348030340d107080c1c0f030703035410000d410780c400c190480c00580c481002c062464440d00e00603003904141a64800d0709501c1e18500790782c0c0300802003402c0c1c01e02a6090b05648150760303903481500b800024003500b23041c041803100500c41c6100c8030410b4654800c130000b2140701c038105da032810000700f00c1940400000040000f205480e0950440c064000c3c0b008009038030348544600303152a80134000a1142c0d40113541a41480580c0020300c404000682040c140540d0710320803250b86040e5081c01c000490200c400780b44051500e541590505501a01d41c2c401580c0b6034180000200b000c0310265610301ea0a0011141e40c0c160b202c4001400018150001500c00030071050500d08207881d144a4070a4a02591110002e5440b405569103154241030203d42030603a54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 484408767 1250 484407517 484407533
    0xe061c020c190516051002030306060904060b03071701120201050301140d02030f0303010e0c04080319111209030c04020a050a030b0a051206160e010507021207120c0e071803020d 78
    0x422040ca05101002034824403c000c0342c2e2a030140b00f400b200000242d6a0b200380090104a140da00b00035800c203000050755414070b0340003800c2d4400024030008009403a40c0c10054683c102b502c640780001d010600c1080d660595482050140014139200c4014a413260f000800912050040e807000088034060326450340c45000e08016610b44c02000c1c1c81001060058031541d0303420912500d11b02e6400ea102003900651004211001c3d40e4a0310041c2d8a0700e10100c1c0c010ba4035248002c245070402c80e4000d10030094810610030a888a1003029010740c0d07503010396040604e41445420024403071441000940c5141d5042000c80b09482203c1c1808141c04e2208070008030300460f254820307900240400002614040081402c61061039500c08000d80d20580042c1200d0000009802078041030b0304000780c2000d407810002180b8005d446008403469592140c0e101d4070301001441048490510b00f17401400a01c0490505a42c042603d00d000072540c142102c5080d8070b445140b20107802645980340d002c1c140110382d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 484410017 1250 484408767 484408783
    0x20101107060903080f0f04020a03111504082b270330030903020705011110020c0a1707030512060105091f110312010603020a0219080702010e061c020c 66
    0x700c84100040b000c1d03410040c1c00d50808035407156004200500080c40041050202806160060203040f207407411541c8401d03801d089858159401040040c09a407000ea42c0380c01080a0083c0307101411408000c2ca0b00c030040c0b40203656030782c0f4400b038401161012b0306500010340b02e80b840e4810101102080d42c01c0c8080f100d4201600045d1201d2100070114544e500c0f444400c595a1200114880101d45c0c2c00f41e0440440c0c9158400900681041c032040107107601ca417200f0502140b5500170703036a40308542c11043d001c0742d00c6000307041d0f403542240d110b40741400904c2e109281b2120f07020035010b1510340d031940c00920700d1044c1000c5998100c400c10101d00c1c0c0364401c1082c0c42c540c10000e001e0001040c5884501100b00865803c04000074645421041d158030002c0107442802c00c0040c111410760f4206030781900690801c0f1500b004501c514208044050481401c1c04482030107803a02c241d0384c00850000400c8803403800f101c01c3c01504104420210300b052001088026404481d0060322445400c0800b4205020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 484411267 1250 484410017 484410023
    0x914090408090127030602031005030c030a03050f12090a020406061707122c1006050618010c020612090709060321020309041a0306060904020102151003060f0b0120101107 75
    0x14880017008216043d8003d41c001c1c1d02549800f91250750300d008042d07550082c0008a50160085105c07440064014001b03080891881c6c41d0700e5082400159603541401821509110f2a03440401d018041d41842c1c42000c1c0a002035140c4620721000b40700380321038503680c060146001c00c91342081d061403e804950140c1d0f16042c03240800010680090313044020400070f2604200c2c980203d03910035484074014402e40049460240c1003600b440700c2c00242c50030b0b03240d8007459541800000c1e01d0070001a0b40d540b00078200d005080c5074113086414000e02c1039103031045981084c1c000740d15024041c00441c072100c0b1101803c0100c2c502e00403090f500c200c4128103500800c86019002400c0c00208400700403000d42d1100420340540480d5200d5540710200103003214162006800350b008000a00b002d1400605516800f15400c0b1035561800d41d01c1d80c40c10201c500748404480456039680d0811015030f44150b40706805c0070f40c100d0a0803494403400d041a15981102280c0b500c003a80d501070f4610b1164144c0540b414a50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 484412517 1250 484411267 484411337
    0x20102120705180405090a030302070f0609081b0a030915030b031e12090a170316030e0405070903080f1305030d030902100314010e04020303070b0709140904080901 72
    0x52018020b4860740124070002c425107808507000446007004c0c41000c0c810b03020103000b003001c0740700740c0c60642c0258041182030f10221481440040031402c903006e00a825072150504c5542c5505601d2010003488072041c2e10405a008440c0c903a010950101000e019190004001c141d160495030090b401026443d40e959014001c00d03481d40000362010300c144d2200300900c0c05464050000b0b100034003080c41040400d40e8418000403042c8140600c40d8400501660200103c0389026a0307045103156007107080d0001c40c00290041c01e9030302c00d07081600070541c1005190400346815411a0b8030074409020360f4142000811004c034010040903400d010600046c030014040d514020710500001300508042c0c241031740100105901c05425600c00e115400030204072020340e0009909010407231580b804054420381c1d00d84001e01a01c00407400000240380100380c2919850b104510301182c102c031030314001c945188107540758407c000100f004002200c460b0340003481c210040201000c1c0c00c40c107108901c2c1400603082 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 484413767 1250 484412517 484412521
    0x12140a090b0c2b020d050c0604060e070e0411100f0f0f02120f070b1311040207030c080d0f29100c080301061d10121109120703112b0302010212 63
    0x1500d00807a0b82d00c03c1441c0c1c03e85e0820840f0642c240c4140c801d03440785900561047c0c3c0010086030f110751040010322101c0d402e031015103a50300700d895400c02d010f460a80f40f03000f00c8200c03c881d0349000801c1070034400160401d0710300e032400c0110140903151350341c0180c400e00c400c103450841c001d8400d024038108000388009941d10713100c1d071140d1007005800a4000307e450241d024041240d09549490400d1107680c0084010300d5094a0418400a504110011014404580000800504540d000d40044880d0b001e00140d403ca0f001100d00a68842400e802040c0303a540082d030146100e941516645291300359041d41d4641c00000044034040442e40d00640503030800300010580319484440103a080a1001000a404c030080d400c22048040b020301c0400810403184a2514083d880e40280e021514000d10f014104030204011486205074408120002d4000340400c0c800c001d40d046540380007403001d446c5d86803105580c601152500d80900d504601e4082c0201c141c1c2d08151007501280c40d04424240249054 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 484415017 1250 484413767 484413823
    0x130c02101a1c0c06020105160c05030f03130c0f1a070215070b0708010806102d1205010f1a060c010b06070606050f010c050c011107090912140a090b0c 66
    0x94059030001c80c0d601c3c1c8000d000140c0716205006041c040d680c00c02c01c071000072030001002c1d1500c80b000070046941d40414410310b0802c41c41540514462205210150b078900280e1a00f0520260590005515007032010000d01c1701c0e942c90725844070344107100c840c8240d44800c1d0b400003587c2804105540001803c0000d00f143c20002020031590187c01c980e103818001c0e03600e800c2c0082c5c4860040f1000d8004c0c010991040094003c0c1c03c581e1551031960303481490360f224000e4051000c0038115007040344001c1c0c00d15591800c00c00240b2400c045040e507500e0402c080590b80c0070300d04511034140e0400e0702c1103001107420389200300c00b0740c45402c07990401001c0036555101490150080c00c11881428450a1985081c81c265409104840600c40d802009440842c40a80c0103540c0014240381c1001d003071041400105d4030301d801c0e00c111800903000d004000e512480b046401007044103003c052180902c41400441c4203190080703508000d82d4811007101c0e44034041d5480f00d610385030900c01c0c485a9002c00c48403141c0c103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 484416267 1250 484415017 484415059
    0xe07050f19031407080f030a031a030604050d1206030203190206040e040b100e1003120e060c15090f0316020409020409060b1002031810140301060905130c02101a 71
    0x20f540382c1c0801c2c0c0c0c0c4250fa45e51444c94a0b130001c039a15040c2600108500050184070313500c0410355400242c900c0c09401c485030082450070000300e504a0707140d84400a0026100c1d000f24006110b03a0304600180901800d540c0401d0311360070003074000e50001010640040c1150343d01c005480152405405c4c0702e46502d89030034000380382e00003542c0f00031003040108008103a04130001c20040c0b00390100c81d040c45100d40b440d521000309580d16450301080200108001031240da070700b0000c0c858042480021324100404600401c0d101001904140d048d070b001700c0404186850220683d20b20307519080801e074081a043c00810041e01c3c500e03400a60042c9002000d00800c01c0c140d0000c60a80030544444980210880043e6a41d02c192440303948282c00c40f00201700d25203071011444402031404d00d401112400524580c240b60741003a0000310204964010900040c10041007849a420b0b011005114007203030400c01a468160101919008070b480d046d241d050800b480008040b901006031100c0755802e100300101076 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 484417517 1250 484416267 484416293
    0xd0207030201180e061207091e0501060e0a0b030714220e090a06090f121706010314010627090621020f060714120c010c030e07050f1903 60
    0x2c08a030b9441062036190002c41e4105090341c1007422007000e151180e00801c1404644c2100c800c08902c103025000c0b86521040c002c1590701240180c40c14072080c0d002d400d1805890050700504c040208000400e4000c1e501c4410380400c40c0c50740c0f1080343e030700d40b600c00b401c4401840c409620301000e280092219030030410744981c04841c0001103003d14100d61500b50f0100c44c1c44080d03d2040455000310001404603401c1d900c00c46105110b4000c0741d4000c100359440ca15121551011480400c900300c0d410030102c0841c02500303a1205091804200712000d850170b4094492060140d07108004580310400b05a0440d0002c21b14110842080403d040b907403540010017505450040e80c500d840000f00e61001107203e044114001c03680201b515501680400911415412845096038034a0720314580b4070035082c0905c40c0b000d007038150304580e40e6207440e200c801d6030a50703002c400c14004040c80d0001060480394081840419180704841084980201c8030005a400e040039802210081074010008108040792038160 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 484418767 1250 484417517 484417519
    0x807030e060c0408010b010f0f12021201090914031327050c0309010b01020705030a0201390311060402220f020301150314041106030c0706020730051b07080d02070302 73
    0x112204000d000115823142040c60b0a0f000318100c00c41450f003d50050001c00701c0340d06600c0300142010306408441c030104800ba4040000c05070307109409801e010101e0040000d0200c038500461501030141076604884615214035009102c02506000501101022900880c2a00d8405000c00d06003030111080c20750058800582540c604509201c455001003040b101300c0b000140988075402041d00151045890308410085000048103070f070206c483c0c24074144402a5803801c4c0c21208100610300a817440707140a400b441140d00503401c0000690701c004041c0c0382d00905051104182e07048595a01c040c140140c80000c1240c0003000120700241d00d0380000703510b40d6256800340610800100c501c9005107040d54042e0080c46155400703100f60922100958004222120b840d04e4640a5190ba4040743c0115074122003243c49440c074502054084446c02a6024511140b85454210440003500d540b007000180c031013620124028110404c020b03c4510010328024050340d61840c0907000094640700180001c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 484420017 1250 484418767 484418771
    0xf02010c02130e07151205070513080102070201090b030c0a030903020c06041409010e011802090a0906090c0816050901110f010c170c0a090918121101050f04050a02010807030e060c040801 82
    0x1485490385c21400e0124009403036005640c010312101d0000b6100040c21041489070420880d0002450400c00c900281110000141c80300214400140002c2050f031080e41c46181c00d01c240b02c2d8a2108800711000740400d81800500c00d8032514041e424a81044c51055119401041c005520142203184074520b0004588030409a03880c0d020080d1480000c3c025108401d119000e2480c195071140e0040004502c01800304c1e815039550350b01c0c03030140e81c20340c0c1201c0200e0361514450140103030081d076815002500700d52444080c1d40550001001ca000704101c0e04c4c1005616840074013214024090242e80e02041301c002e0245c4080711101034130b150074010301c8402140300b810000c0c400c0818081a0b591180300b5036916160300345010300200140001101101034401c13415090400980c40c2601601210207035110f282d8000018000c850860300000c04503840174801d1002c1000040001c00c09100c4203609090a1035162682501180241140544041c1070300c580802d03c448041c415000c3d00407500c0d03103030003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 484421267 1250 484420017 484420019
    0x13060206090604030e1216140108131515090908040608070c02150306133803101d010e1506010c0506071d030a121e0c0f02010c02130e07 60
    0x8a41c0c2c0e00d0380220340140c001122548915600e2801303840300d500e140180d00840f80301c5801d2020f4024030f482d2540c400316013050320000c59512940c01104095014904e446880c220f855581c03280201510102c0a000b40c43c1d5940d100020f04c058082d000c50007600840c0e100b00001c00700c0c0d180600c0d5a52240c0a044041040c01c00083c0c08144201c003001d000c984c3c060080701d56a035200d0117000040d0005081c080e80100c49103807034a0501c019109800c081c00002038410010110b50f280c182c07290380c0640c041e4183c04d0500d0118601178600140710503044540c05400501032000103003182c40764241c1031041d9a55400c210f0a110718000c001000c0c0340c440441048030308284c6803900195603d90200c1801822900301c0e07000150001d01400000082c1c0548a041c0302c90b0756040b0000a040140b280400c40d403051525006101a5500c400111292079036070b001c0700300403400c410303014014a003800c0300203000078108a644800c5905c5180c0302d0390441c0c1d01405003201e01421000302c102408540e840c01d00c582c464020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 484422517 1250 484421267 484421281
    0xa08120702120310050609010318030306030b0109022a010204030506090a02040b0d020d060908090301060f090507020c03030f0a02120f031608070e0d140a12080c03040c0509091213060206 82
    0x41103e002e40c45803000b02c4c3d0510310b000e0a00046030020041a03040c1665907451f944544060410204030511a5400040d054294941001c0310501038028609081c1b0500950807608064412500180010b09401503c00f42d07004600c0e0191007541c2004180d40144024403040050000e08000000d00c221428000021782c1d100303012500d0001e040181d80300c1c0800e032900c00030401d142c3c4000005405040074600e040900000300b400d42c4d40079800341d082c003006400c3c2004030038001d204107034211103540b001d02000c1c0c2a14001075564010b240c1c040010601c00600100c040313000304114541c10058210031a01c0b20103010315070f807580d00202c850b0003501102c1822100070910032601d0500c1040e550315181d044c8400c00b414030094410481080703c411140144000c0f09040070002c448000780b02c0c650b140d203e4090108014004000a004c0000f500014410f00c00010224480c2c2d406442c070958400c105030b51208c410503e17001807201c000001c410000b90110b003140590140c00280c034826022501103031a218 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 484423767 1250 484422517 484422553
    0x8040c081507030c0e09070c030c0c121106120c1303150615020111042c0c0910020712030507030302090d05101514060c0708060a0501140102190b090a08120702 70
    0x346485600c0b00181c00003580080c025624001652700904e0808607a120720790383d50300503480f0350700035120407031601c51420108440c880e8240d10200090790242c1c01c29043c00c034482040840940031814048000c20620409400e4015040045130003090720402d0000050004c80100514051100300b00c0322402c000c41c0450050045401005102c0c0f4280c0c98146080800860303000603120b80d85850119030303058984000f0420300340307004400480d101562800004e0401400303481e00c0e84560700390b4003c20800c001c42c4c3c0306000c0c0d14040b01d402d03040c440e5959125140484c0203210744882e071399014923000520420b11000180715001d4540550003003200e80c1405850095100d0148980704603800181c0d100c030454142180504400c0d505841140d03242629a20680d0600c902114800306440d0340e080100401c01d0a441003d1040c1c20038000703084181d0710300900710b03d402c24171840944621042800310300540030400801807101c2d0000320b070a40300c50140c0078215036990259003000040c412984e62800c0342001d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 484425017 1250 484423767 484423787
    0x9010c0905040c090f090c091706040818040c090305010509011401120503090901120c09020f090f0a1d0405060a0e031611120f011109060a08040c081507030c 69
    0x59190060068a0038041101900c41d10f9040000c0001d0b280380084c1c1010200144e202402e20041e0129004480c1034004081c0e01c203da10a051210442078489200e50020460360741080c0c004504958803405c1b110121304000c1c040c010684c106d131414607901d10840c0e028500742c09503881a402401151035928200d0300341c0b040c0031009158401e1000040214000284035807402e83e100e2001e581c2414610000a41068400da003e100c01e040058003500c02c025034800d8003400741c003440000710b042007015005810b072805940c04080c09008101210509030f071340d81e42c8400060285600c0f41901c41d000c003000740301020741a0740c110360520501011841150322400741003c0007030120011810308068540e003034100000d1001c01d90380020751000c0904140c0b02d0402442000700b081d00245012500c80c5074990846032a04000c01c54940705111440c443c0d03071403800712a0b1070b082c2803a119030703a5151800e003180d40c802260b104000d5841034580110b00b19011824051064005880401801031420025038042d460 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 484426267 1250 484425017 484425041
    0x1d0105010501211407022413081b03030c07064a0a0f1a0601050301140f13060305160302060730110c0109030f060203090f0a0b0f0901 59
    0x5800f007968074441040000e2001d00c2d08140022a603800f0261000403090401d07209040103030010b2140c000c6a5903c2c2030b490101540c07010102c0454a08001b0717240d0841070032039006042020010b0210981c070070143d00c010341c50304044140ea47d203003090900b91082d68001c81c01151000e0605078100400d800b480b0b0100b82c0c140905135038000030403159002007002c842483c200c40c01001c40007240103101d10300704505103c5910442d41d1407812200b81c100313841d406403a421650202c04204c1c041000c03590b80304c0213503811640705a0001c460801100300180e0a20350802c2d01c542c000404d40b8141042c410b6640144089038014010340340c000070000c910303010422040c080a034002c0300400000740080c0181c980310000aa01844200017030304005090b128081002e8040700020740d89803481a02c40c081800240c43c841000d080c550140c5103180c0d40c2e0412842c40f0480035280d190301200080d04440300340304a50000f18130100f910584031040c50f010090300c0c0240c9500e803071615078200151700a80705104998403500d0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 484427517 1250 484426267 484426277
    0x60f01180b06250501060f0f140307032306040609120207060215071403160e0a03020a0902030912130311040506060d1a040603060203160c0f121709011d0105010501 72
    0x5030341c2c0c603d1060f201d010302c0d00400300101c20b41e41c0c1c04208203102d4800600562403103200a10b00d450045050300501b6040702c2e002403891080b00105650010b18401104c1c2d1107004641801084070784900704544851201e211406803404200402907140d1001a00c244500d100c030305088011003040760341d608540070303e20150b0b008148541c1c2003041e0051180c0d1041e098a4175010004499110300306a800945520384400030780704e5a0480e40d038011610090781c400c00e41d15400d400d880c0d40c0004800d900c1900c103070141c15034000701065400e00103000300c5050030114100c196407080c841071042441081440140c0f02065513010000c0c43e0314003402064000c1c00b000340410700b4189088816001442c502d0140d145062982030b1424190301c403400b80030020350103404016144d01e4511010408100010080401c100c903d071640310000b0440406404082d8011302000721074100032400b554210203681100c5645145001004140001500f0141e03194001a071410717801e09851007054242c48080c051640418 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 484428767 1250 484427517 484427527
    0x30200d02150603031e0a0909051003140102040909050a0501230a020a170703020904110307020d050f0d0614190e060f031c0f0906090609090b12060f01180b06 69
    0x38102400c2d4100000400307813807a021400c420250100c070000e201002ca40c0d4080345080e0310a0b0401c5c0c1842c000d1410580503c480c0c07403c1c5103c4060014103020040c0f0900780711504e0a006e1800b58140d4014180c24002002070003120f0500644d0703102d00b01001c94282d800c1010b21140306215006001c80e281c1404610900c9840d110000000382d0820b480c500f041044091001104460442d200350041409440c01a51501d20350b0a11007902c021001c885000740041050000a80d0b0004051860714010325040b0b80300e900350780014405100d003031004002d883c00e0840c046203468100440f960221412107540b6a0682180c02c1c155002000d44511402d001d0490000b07035403070034501780c0b400185500405580706145000140040c40d440b01c079908000031064402201d1441c2c005080b20301070040703800c1c4282954a0306d50000e0030b01c1518020084902c0d1038140316821600c0d1f500c4a004a42490416034043d0301d810303500800080c10074441c0350183c4d401c0b840924516040c81c17146968401d0050300481c984 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 484430017 1250 484428767 484428793
    0x90a0b01030906050c0301080d05030105090a090f0506040302010501090f0b0a140a05040207050f073014061e011e0e0408040302150901181230200d02 66
    0x10442028124189030b1580600da0000b091031160703622660406400b291213504000701d45140c00c21180c5032105000d01000180942c4e50b40b01001d6030b00c02e032810300100321140c4611b4940c6000030f20b1613000b0b1440c4218020701042640640240e4142d404400d803c0221074140e14403031040d505003130700d0a07400c8148020309114100d0580303851070303580d10b01070503001c801540c030f102040403030340035000c1641d45800c080f84080c581c00003405140002d00c0211203e03000c0c1581034801c040000b890780c60042101c2400c0020804104180f08800801c84540003903901c03619250404418030480407483c615107100010021450310b00d0104110b10f007620b141240c0500b03a040c0100b0440240010300b003940d00300c07400d100c000016a03078031aa1005618900600b81d07103c0c81e490002400541480c04654010614103034184114810701014000058100002c01c5203842072100c410300181c8144198201e900700003690090094119403900e04131201030341d00d2080301104070030460f01d0b03403100100714005800c9183c2148075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 484431267 1250 484430017 484430021
    0x9031733030d12060603020a080f0405070b0c030c12160b060f03070612050105010c0f020f130e07030309080607080705030703020c0601060903021801061413030b2a0405090a 76
    0x8280d0403061024015800c0c0c000003850400c4402030880001c408140906020041c3e0080300c0052245007000d50411907030b00400340c103017640280b916103940c07107240c0000c003402802c000200045c002c800509960725103a600a540b02c0d40a0480c0f0352036031080032130049071808038000310385580f0315a80764820703200819511a5185400a404280c0c49424246540d41d260380c18012000180a2501d4215103141500024404c0d50310503406281481748103017220004c640c000c01e1a51181da41154103012401c92100080c01c550100d02c0c500b0348d414500180c084480e40001651025240207071500b1051340e6550940564070841104d5400c009610400070400c03081c001c00c09150000c40d1400d003d411301701800522072809809900030300c00281d00050400c2542414000003070801240c0035440925810140054425605134a00f20700c80c1d0400500b0406e0b101c001008007001e142c1c440007501082c1007002c9820f80591030b28280e1349441c584550f002c2840607162080328102e54014205800781e81e60051f44c080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 484432517 1250 484431267 484431331
    0x11030c030a120c0204110307030606090803071e1e060213080a020a0501080402120f06070305070201020c0c0f010512040f12180e0c1c050709080307030804020603090f0304030303090317 81
    0x80c015461b10401d0004148545c065840f5058a54002a013076280103801050810154091440e0741c0007000440f01180b09481c1e0185480200500c1c520148114a00400180501106124982800d005000400c55250002d14440c4d1401c5500a01f0355180e075540c9440d0381c80348a009510940e01c5ca020040c65025001c81a4404c3c0018694801311068042d20f90501400d80f0015018ad00401c040100080e0544100b40d004400303803000318100302c0c1545031290380340d424840c400d00c42e9941c0c0c0007041e50380e0311803000c07958a03040b51100c00305141800e19002003c3d0b102c020307080341c2207001d400035007442d64851465080d283c0240e10034410342c076192203a00c02d0b0034a4040c0c200e0080700d80410200703c40001c3c0c0100b100c51400d01c51400902490070841c0206108803d4000310b6058004000d0000401e030b111015541194044a44941d203445a040440c544468840040c1c01da00022400209050f05540f10681e01400303a280e076458010441e40040004070200c50384558210406040060400c80105e030758 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 484433767 1250 484432517 484432519
    0xe0c0f040504050c120a0303060b0901020d230d1a090c19020111270109080c04050603030d09051f06061209050a020a0f0f0905060a0611030f03010311030c030a120c02 73
    0x810001d4040c011850142d1719034000c1940d0b600900c0d815003010381c14803680b80200345100c400c904002031f940000391900550400d100403c03180c104d1008503080050110310a8486071040b0603a82d440e07891003072004c1c4c03604902c0c24200b031000c1d22418003103003495600c2602c034811055543c0d1504a954180060003450f0150380da08640d81c130440c0400c1890f21134020102081400d142d1a00c02031440d0445468100c401d403054104800039104000c0d4030000640c41c400001c046801090b00c0c1d031810b02182c650b00442034100841d03810000389405000f40480c070302c2e001a60810841d0080e24810303414405650440c4a0300f4009821107210306d003003450030f61129811601c07403800c0e1340381070900c0d8000680350112504901000c20580d1010400700a900c1ca034940141681d840c1404a03250040000b1880d091512454003401190002071961400620850701610010342d1520745030758590502c0020415503448180c020300c1480302000e154600010300c0b01306203034400700c00d2102d40d901c088100c81e075660b0085c1c22 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 484435017 1250 484433767 484433773
    0x2805040e07061b0c0320042702060d06060929090f130e06060111190b0405100c050315010309151e090b0411090c1e090603190e0c0f04050405 62
    0x82d0001910440d49000a5020300d00710107585441b841281e10103440304106038481e034a4010020500404044044400307580303400f02e5400c142050010401d030307100d000225070180c1d20b13220010800c260000310900070380d05441840d08000c3c0078103403000c0e003408903541c0e094030010b014000c2c26031a280c0320f030118100850192861146403c0706000034103070340c0030703101450280e0801c10800c80c00c0d5a000501060034120840100210b45030003801804201c019000900303420070410005003440410032440c000c013804400b0420814405610041654100b036541203043c40c1481116411503210740952503602e504440c00e601788107400501e880c020b040e400805c80c2d13051680d00030310b03a42c0e092501c40d010155001310701d514450300d481d18255a2183d0107900c1c071072142515105000030401c03180107986050604403485c00312a001c1801c0c14045001c4c2084095100c00004108070b09411441004003c14044130814014a039140d0081900c50004141d181e0f08030101202c2444545010341140c2e80040c043c0090b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 484436267 1250 484435017 484435067
    0x206010902160501020d0c02010c1d060a170a050105010f210c02010f0e060414030403120c1b080a0210050f07080f090a0308040e09032109010b2805040e0706 69
    0x419085e07822504500e030b08259101590b070001502801b89225101c802c0c6003031110b42000c20f0700c03088406814042d00303008420106640c2d40d80b0380505110010180e1607034001070726182c5203610b00f010b000240980c0d4001640b54400008041c081c1100540a004480042c43d804a404008100808982ca0801e04540d00c800a44080103501c0c0718000090344110080c04007450076040840e81c6c0507852480e07402c1540108010070116000000c0c1810402d69860829100f480b6410f02580700030200d191700c00d080c0d040d0100064141400074050220381d100759480e109441c000d1a0070744082c0560340440542120400040c0c00203020b040040c10b1007003485421a040140b440c010170391008007504201c0c1d1a030700001301801840341c0301740310710b030b00520aa00451400303240c07107801090b40120b41a060700f80f400b01e001081001c1c0080d0446070064801078002550314030490f115000920b681c9003c2c24042c01d81d90b80c0803c1c0c504041c00ba81d2401c1d40b1010051081501d030080854600803101c0e000c000001c0c2100d9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 484437517 1250 484436267 484436273
    0x61409130509120f09040b1005160309270c02060103030905060912070602070f0b07051005090309090c0a170c040b031008010e03040302011d0a2c0f2203020601090216 73
    0x301811110135032441550729905120705110445035020080d0b0b12600080d442c62181d41c1e03116040702c400c3c085810b0781d5070703a83c02c0d94030b400e80d403ea406820804109442200c0c0b0400790200243d4120601c80ca920140849141520141e84410081c040540000c21800b418055400c10000400700130001810300340380000030b000c480f802c29019421420050308141d004002d002130500d02003018102001c4007d141010550354960384000c0420441085034a550029060700ca0500694070680c001800c0c42081d442e060f9440b04136940960740180204407038111001813440544c8180b07119070980d00c0e505190a04040241920340c1004100c0120321006481c08a5608001c0c026801c0114103840295240ca086100140c80c070440007107030034420034040b0000d003601c2d40d808140001312010a038500b11130550601d01c6102100500e0580d40c05440d00170103106e04074441e9521a445000800c101c240c0203403c61409a004e024000c10240040c4e0100d0018828000645e0040442410303080a034000c0b980315039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 484438767 1250 484437517 484437553
    0xe041509110405090c180708091506090705040308120103031107030f020d020f0d030c120e101202090d0b0a110306010804080903010605100503240109120f020a0b04061409130509 78
    0x2031114068440c06c4001d00015503002051076400c850100c01529400700103802c1105041801800f09108070700c1da201240c0f0305401101110050754001e41101d585000c40500d0001403402844101d0000e1160890105041008900a02030300d42c0460035418104464007003114050341d5050a9a10000c0c100090019a4803101ca000c1c1642c401c0e1104000024141032072010427080141c4d800520504624001d00d5640309150540701500074141003066080204651000380907015000da00054100b03502c0c0c3c18000d0011480c0d100d0710001109101b0203000c2c040e5144580415aa1603002c15541808100021a440d001c0c0551003c05000020ac0c01d42d52000640101d503902d0342400428400018484104d03d00c5c500000c07001c000c0c00420316149802c5000822816880c425108200421503e1104102e41d80c50004c0004d0740051680c4c400035280d0f0b8861000754088e02c14000410303a4061821507440a41e010398440c1d40c0c1c024001d2500741d0340300d05218007900c00285031200354000c002c0c107490304101b40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 484440017 1250 484438767 484438789
    0x14060c0616080601020a0c0611100c110f0106050604052101110307080610020c041e060306150806040b060913021203041406040315110c070e041509110405090c 70
    0x140203414403520a81c0c1d001d090324001401c894110f4001400c041c012803c0da103a200304403050303854607402c0301c580c015a00c1d04004c0d089028460a80c05d00c0100c03601c80ea0301565000d41c3d25080d8080c0c58400b0409a640ca0032501e6074800c03035404c91030920040145140044200401c0e19068081b5001e0003000600b550031181d40e4140040310f01408000e10102c207503c0001030740d214409a40c69880c00c1c904007030107076070b49460b01c00c214071481d125200d000c00200b004121760314200184800303204082e1649407217006402140c078507400e11070b0800c000040da4200020064050f541051081c069500c03910140080040000c0507415000441c4040c200141c40b000790b10744107620190041c40e126420444030a0050841000381c9205107420700c401d10204480710003000da0b81c0c01000e00010103e01e80c0c500440302e0301880012418600920600081d0041e003280e181d13114074410445a418101307414041422078034141800b8000c05000e000d18100380c102503001c144c10040c1201103461640d85100015020b03000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 484441267 1250 484440017 484440031
    0x71e03050f03093909070c020301140a0c1d010e0a1e090f0902030325050609160b0f09040e071802040e070804051504030c02060d1e1514060c06 63
    0xf00341e000c50b0340c04040c0c07554004c1e000c00c6190030385401120545490300d000b03070101c0c10701c2400c241010810150084481e2480554040d00038025107894103006802140304070781e400b48580c206075171080b001e4440c02c2c4148600036065005407224880c1700045a4003400782c0340c0b80d900010b8550022540d40111180c00400525407046045410304000048065452a50b11042c80720f041c081c00d24010b1307801009540003d00b405c6441a481826000d0300e6202400c903460240145c0610400d00c008080c1c040740302d9003822541a05048c50340e660760000b04042c1b0a03040c00d040202c600740090b00b0249803d4216201103d5080c00701d40b440c645a210382e5107149038001c01c141460b940000d042003600d01d132030703100e940c003480c1402e00c40030501e4241c58198560480c991a0540784240c0c40003c1c1c00c042c0190241424150043c0103e920740c805000c0c0b1030b0050003070510040980401c050a00c000780024040d1504040a94140c070b401145018800480c40ca00449440d80c085001d20002000c18800c001b842e00c01c1e20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 484442517 1250 484441267 484441273
    0xe221a0601030b0301020406050a140d050106180f12061d1006060e100c0b070203041d0a15080319090915050a090e0309010c063e071e03050f0309 64
    0x14000009000c99020703c000724002e9005000c200901c44d003200a44c1c00040003428216410420041c84540c18802d01801c4015940b070a000031400c20351026401005c0c00e00d9400c412909521050114502221486a045e0304c1411404100004849800407601031311070b20003c041103070220f1680c0d401c1c40d0004002c180c1142c3daa20040202a40c0004441c080d001d060307550001101108100510910903590060448055180820303000340c400c004a030f0007442401c02e008088045002d404c0d0403a242980e2030704004c0c0c208500c41c090400c101e000081191061002145084803500d03c10070603101e11101e2a0034030200aa00080d1407400d4081e10141000300c0d40322902071800c2c1420401101440d41006500e40c5c40c1c002075442d2a180001110548002402e00032140d02d01458540c0123486002440d280f1090103110240040300c018480b110000000196200440c40139903a6a44a0287c0080036090000c44c070f101080d00b416074190b101d187c60003842c0c07041ca0b0995030072000d4610340c400d80d0030705070942c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 484443767 1250 484442517 484442521
    0x307020d050f280f02011403011e05100804030810050904080705012403061a120a020418050c0d08130303050a090909120315050a090b0f0a0e221a 64
    0x40c2c0144581c40000301000d900380180044038000041c650b8200000502507486011410b040d68000d00004006000b40c45800c4e549684a08040d0200707a401d942c002400c1c1d03424040860136181403420030429101c10f03070f980752851307485803012125418040c080350112445941c012502e41c030b4041710117208a007e5400d0701e03507407003a601d0800c1c02c503034103040400e004000254035164151003070480c030030031a81c00070404115031004401107806e20b0111440d05038000c0c0c81c102100d800b900081000d5114030b008581c108107800cec0600100103042140e4000500740d4118020030301007441c202e00d51110355405000d00328205040282a0a00c032500d0390415004506c0100e1b001550903407044482d4040e0080c40000c0c00904c585070342d00c5a82c0c60103040390f00141616130095041d0003182100e00307001804024954074055550b60b103040010b1142c08040c0e401410103d1012009040103100d0000712410f07856100340c3d07903139007401c100311651424201395400c114811400e0013151444402d15032105004c10254024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 484445017 1250 484443767 484443793
    0x18040e101b020109020a0902030c160f1b06120908210901051b0a110f372105070614090f120406180b030f0f01080102040e0601030c020307020d05 64
    0x1d00d454a903050841e070601e8103010050320b8140c0100c0c01c5920f0302c1005a165160316401c0c04550040202a0b03034074402140c00b48062002883c0440345090040e18400301001e5100c10012081c0300d140102000b00e01607480c0c04443d07102c0d61703100d229028001d400e203500301491510030350380100c041085801e0946515040c003820060a2040c5034000303002ea5885041c0f48010b130680d0040307008081134a4244548940b15800b040c1c0180824040903042c181a078041703c030703490509034402c50440f0360700c00d981559404802c2c03030307103052400211002e0704031202c3c0e0196121540030340c94000305507485100300081841400d000600501524000b070480d0f0034054810720701b100026180541c00c10801e40c0c10791003000c1903c2e500c0407000841c0e094842c0d81c681201d8850340c3c0c60025004d518560b01c0344110800c00030806c1704020404400c0d074091115581d002e040d41e41c0c2c50303501c0c6080c1c0c0518000c00c00c3c00320751000070909a42c000d512501c0791000500550b800c04982c2c2c4c00150f10031071481700a44564100310110054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 484446267 1250 484445017 484445051
    0x6110d05040b18120307020c030f0d030c02120909090304170102030106031109010f0806030a0803090303010602240604020703030905010e06060f01090f0e070c080408100c050a0518040e10 82
    0x100c0203c0407514001104000c201c1941d50109412240c559800000803403030640c0700b0322804400700c002500b15051b41c001d40c03440a40d29a41c40380004000707071501000d240b19a00c0401e1b803000201034148494100041c2c0010401c0402c0003a09080c00c610080000140c00e82d81040c00f03445401101e0001030700d030340c50000c028090b02c0c104500700380c0519040000150b944e0304051550000d0440c0d15010700c070f5558000109107030101d0450090310140004c01004000c020020045050781c1c0103509598001155501c0d4481083d00000320840241c2c03131400159550074a50301415410380246404280d00718a43c41c2d150840790103a01c1904180c0014041004604002c010003042c0300d03080ca040c00b8401c0c0741138144074104910307004105145082e0004500100e1041201c400c40c1a000200300340c1d5641e98405c9159190b100c2044034904505044461166901545c11b4070300d006003a4545d1840c00030f696030241d40e006507041407107900607902c8144660003071080042003c1c06501d4000010742e000d0030590841 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 484447517 1250 484446267 484446271
    0x12071d0d08070f02030f0a06021b0c012a0f06051506090a0605180a0e09070f24090e09010f0b3003160f022d060706110d05040b 56
    0x10049a044105000050003903040b40e00560308600c00c01a0002d244c030000341054085c0402984621501c040c038810300c8101d600800c20441e1580084020b0102c015143c1e0b121a00c00c4c07502400719440c010040c0301d144c14100302c40d005609045d420034000c03403550354072144900092000d0b51007079034031342c104800801c90404100100d10100e131070604200340c1100041038200c3c2401040100300000c00c1420702c00c00210f030080c105c4907000f8506c2c1070281d200c24400c5482c520440340201c05d40f0070000d0000740a451044110301b91560510038510f0b22010144a03503000f80005210400c005a01c03900090b040c82040515019141d490004524124182142001d80b1400b41e9442d100e1020184640c1e1000124040fa0a444104d491491803c88102c1c138202d046000728001ca02d0b40c10300454040c0d0402402d81d03490b40381e01740708462109034064080d0074030014026481d844458228000050001844d024001d000c004c0e00c68140400d40c0c0c4081103030341200c1d41090103001700544c1c4800a0204010104607800d03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 484448767 1250 484447517 484447519
    0x150902030121120e13091a0a020f1801260709050f09010509041e030905010f0e01020c090603011e0c030c0c0512070f0b1f0f0b0409050a0212071d 64
    0x12240402511801c10000443c80c0600c00e21410941d241401d850350030303044109001d0008100041074150034002d2945030130110b004000d07414100040c030041c500b8400d44090305400c0741c009080580d01c0100e5108086018002418808440c400b0031600d83d040701d00d0b0b4038460300d644414440d4103201001516803003454200a21940c0b251008605948924a0890454804a401605545960800340c1028800c040882c0207108080003800038950000c00741001c461307080c4ea41054809540c4c00485a0800e5021418010b07002210030010f2071414120450704060018000541040031007185240040204002045141c503503900075443c54240c8100e0041904600300800c00c41561303900c0e85d8036103c40c9001d002a07070902003000d030103110405e00310000071a803001818440d42800302d1621803c94001c001003260090040b80895100c1d04040190101c0b9138045065041c14201011240507240c010701c3c1d13040c895400c3c41418440e01c038000c201c0f80201c82c540caa0542c41009481014062a0806401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 484450017 1250 484448767 484448819
    0xb010201110418020306040605060406050a02060c0c0a060515040603061d0d0f030509070506120402091b0a031806061e060905010804150e0d2712020907031509020301 73
    0x100040c040038040b031402010b241d43d0040c0e4036902c03440001c0040045400a036041000402c0210f0400d40110051000b00c0640e0200d0740c580d50f0300e6405a8091250307d60f13060082e00404000700000300a07400590b0401e401c034401041410042000c0342c22034041ba0300648080761114000032000010645034035a00c150748010740b03108100c4120240480079080309440404d0340c0c40c000646009000d0190074003030840202556900d81380150311101806080d5020383c800c00440011a900318601c00d11041c6144664210b207042601c00c1000750000d010460580408541c004c1c0c0c0740b40000ca031841100b0240480c41544401710a18009054040c4c200b0340000d02484822801401941e80001803e0b030b00c141d100d1100076000c08010f010b04054403c00c08140000d1241621101d18950003007404036203500030011154002d01729500c5035542001d2881580c8044160660301d80140c28214292030340200341d07060114268802d20312401c291180c0d644040321180d80440140150740780304101420358410703a0706c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 484451267 1250 484450017 484450019
    0xf281a0d1b0f0c140a0b18070503120d14180f06130809040e0d350406050606070b04060507090602160b03070216030c0807080604031d04020c0f010b0102011104 70
    0x604020040c216031400d000c2c00d82071840c100031520f04c40310f80d0a0400d5080d03400c100d5585c5001ea010300c001341c80020302a10b000030607030701a00b40014644200c0c2c000800621210050b01d00d82d40c590750104d00c441100d80c2d120100d01000a040441050254400d0300700103d0407041503410504041503031141c0b00f8150002014016070310300010700c443d00f450b0001c0303046558840da0400a40100707182e0441d041680a20700801c0540e0340c111081801003240c030002019a2010361450500702031421507140642060500400d0200c0c00c5a071089a204201a10326850f050858848503507403041118201c2c1d545440d00100142c469000c00303160020070050006042c40f00c04400744804da000140542c01980c100400000c107540d1080011465403c6108140c0111315180d04014a241c402c50107001c80c00c1c41054030001d07108a000a850344a65015600c00120b42d102c001c0c607030041070840303a03000c4e402502400603003038011003806018400103400c0000641e0801c0d44001a0942e946c0500100c401c080c1444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 484452517 1250 484451267 484451321
    0x100512030919081c0e120705090702010c0912020406050d0f200102101e060b0316090503030307030915050f0405060105030102090616020a0806091501050f281a0d 71
    0x134000024224610040801d2442407000300d9100c01d0100c2d00a03070010300450650009440802c0900c141c4405840c40c4000f90ba0700c070400d1342030700c20190454000a02c0200c00b00300900180d48201160b6200400205580780e807900020a600c007202d509484407181000d100d410004404e000b00c500c04011610540c076003040d040040d4807580c64078480c081094a40f015543e00b0510145105801e4110510401010b51940d0070340c103103034000710340311480342c0680c00b904400c0078090400042115001001545544d80f42d80d01207014040281080742ca1460340b45200c4000109070082600c500701c0b46801b130b0800c1c80c26080241c500401070380014066441001a55040c1d160310085a092481403920000110018404940900700d5035028004030f024000920022050103e8078500c202c0f154040071130140d80310800c01859046040646900217401280e94818544041002e01a00116016010b01c503a903002c1400141d00c01a41d510300c2040c7c000344241108060b0b11840c400d017402da04070058000ea002d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 484453767 1250 484452517 484452523
    0x5070219030c060b061902010e010513140a170a020d11031803071703091207050102101a10110d0314150307090f140603060601020706050310051203091908 68
    0x80203410002c0c8180000c052107036075003028040100240c5125528000808400e03d86c5002210090055003000586d50318080305001c1c55000c0d9407850101e0f803040c010340c0d03144000e01400c4004200c0074045d014810740070450700400c03015885910800950703200341d0018006d007000d5941c1c449005201d80c0c0c080001c0e03074000000503140703100314005110000106400009151055550001c120180c0401820301116404400340869000c01c0c5c410900719034a00c898242c45000c40d00402c0d0040e808402e0240300303907525030042c0c2102c4140405107140c002e820b00120b56446a0640c03881c5c00f103001c81d1b028040c15030081200031003014880c60100914035014601d0250382c1c40181000e0307260a010a4240400d69042c48400001d01ca21101084444461804103000d000a1580242c80c10b004d40c000403000e04020800034810f034416400fa02020b400c10b9015a910f03040949002c9950b03139003035408100b5460b804018070040c005280155207540e001010811140310741d1402c424809028030040000c10000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 484455017 1250 484453767 484453813
    0x4140f1b1206070f35061f0c061d0a051018120302040506040f0e0106141c180f050106170a031b081204050c04021809040507090501030b0a050702 64
    0x94500780107144011541150a2280d407201c07106803c842e01004410b9415100e00443e03018588000f1103015a504010800445405807c44400d10b403420750f8031103514824440855480e1080c1c9000410756404912102c0d10100a0390b01000c1e40d0104200d041407141c10030130700e4880c01000e0340c07e02007036584401c507081e64a029040141407510040c4401c20a90094055401805c405046183c0703807590748a51007913014072071090065403042e600010684502c60000c02c421307801c2c1d02041034a8001009540c140f640d10300084080c000355100380a448420491101081d594054809860009a44d051180c00c4440d01d1b0f002c0955000c003081a44815803011070084921074050400d0201440b0501d0300300640150840000c0640b9800a1400300b120703107262110340114090402c48911300b030301d42e0500c03080740316440045c000071680c244410000c4c54074940c2c2580c060710900540b201c00c0d9a0783c031044180c52080c1c1080340d17003089020410880f5005072060540c010801e1008281100700c49800811078829 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 484456267 1250 484455017 484455031
    0x2070311210304081e030a11030105060f0915040b0912150601050a03060503072301020c130b0103020403050f0c03120327011b0513050901080d0804140f1b1206 70
    0x1c000142403191345415034030b101c404200e80c03415600da08651400c081d40101e13034002e03809140014051600c05424141e905883c4041c01592030500200e0a803902070304810521640034408c036015100d00e4007400003130b0000b0b03d10b516815403100305400400640861882c0303111590743c480d040c05484000407003a1213030804c1c001c0c20820b958040c00d50003180602043d07040326405205200300001c1c01400e010540700111502c0c02e292070b52800003c012a101c10441e00c180d40c2c4692000b504402c00c0781c0c154809200d43d04141070041c03404c0d50381c0e42c130642030036280980d8208030340003030000e6220f07070405014000820900030007951461400d0604402103010019544445c0100c4001c1601d401c0c00075446804a00701d40380c0e22112070054844000c0043c2c0c488102e25510b107108040000329030908110080c143e40c3c218001d0001c2c8038442400b1036900400a00503110000144070983d010581800380c440640d524001901001d54100c00c454ec02c0c000700c0f03c000c0d0140b044011400c44400010034081c1d00429 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 484457517 1250 484456267 484456333
    0x8012607030308100806070f080708071d01020114180f060f04060b01110a0c0f05061c180218060906090702032205040c0206060f060f0a050a1404030602070311 70
    0x41e501200d411003079040c5c0095001d88035600c140315025400c140b0205003c6d43d80d9032030203074039a500d5400312800c10050742c049002c170740201540244131042c9000e0042804043c8000116501d81c1c0203641d0a001094405400d40139003404500f02602c018400782640301d450f20010269030411035081c4da500f0b08020700145c103507503aa8040203078982c422500c0c001c1e064400d0003102c1703100c0146d0400740c0c41c3d000c407032249880e15020301500007024148541540e100f00b101c00141034001c4140e10b0703040041e1040300c0341c401501c002c404200d00141da920003070310183e84680360b0a1703400b49041d03024051800d034081c05051040071100204120141d000045900444180b80356400100203002044400e5a90b074001c1a4000d0800c01107500c2c0960028040f480b90000700d43c00c42d0903442040902509100d50300c01300084050030860031807083e010304000c110112807480c0100342e9003c08403040700c550700b040d002100e0325a00000c0724828594049050000b00003080b000e0030800c902840700e2110407018020707400d1142c2c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 484458767 1250 484457517 484457521
    0x50402040e182109041508100e0309061303050c030a0c03020f31050f010305250302060a09030b070e061608120f040507170304050d050a020d0308012607030308 70
    0x420030b02110609041e401410400c0f400040102929500300a4503580243e1034803110300446a0981e46210071a60004003402800501a0b248800381500030051241840308001d40010354503220010130a40260502d191016815845c140c0d050032500c0524621a41c000c101400201d82c52071280801c403541250203107002d29000010407800043ca0b146c0d8400500340c54254000c0d200301c42d031002040e034085101081603589290140803150310030b020290565111804030707410960320f0f04c0101030901d0a1301ca0445215560380c002503196004041c81c00000701c02110400c20011010780303980d0020b942d03003403c51310302c040480803418a00038130410050600001c0d20200522280c4001c4070441c10038807a0780100362400240f14040b00805507030440d42c92040010004910b0100a40c0e26804100100a0340c07a00340b401003000b00c0750f07400b408140c41c14001c44c1c5051005a98600b2400d00940c0300e504c40105c5985041c448106440403120362124004000b00c288007902c2c404180b9400380c2c0e5050030190301035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 484460017 1250 484458767 484458811
    0x20c0303011820040f0f08060f071e020102071a0402010f0522141512060f150703020f060601030207050703020409081e18010c0201081b130e0907050402040e 69
    0xc0d080103070b8100700440c880c0760b000605041500c0204150381d04c0c1c1095105096030b940b81d04410891a1142d4103031900024007080d014127180c030140e50003007001e10342207034a22a5002001200000941410f015070342c0000c50381c3c104084041080b102c00713001c45051038180b0301500040d007010345030b104090810000007010307079080307040844106581c02e0915031122082e842d80d08100c01001c200014902c00c00c000340b00c0d100e8504c0460308550160840f0341219100c2c2c0c5440042c840309945035041f0315070100750b216103d00c6400d61500036040d214020b0b0f0040007980c4013501c013a401c14801410b0300d81010300400c110b070041000011030b24210383e419640040d0904440c00c1100f030f103010703032249404281c0114442c0040c1d450b28402420744213040c180c42c00e10080c000c070010340701c1d034030002c43c0240428013800c00a8800c1c803a110301c4942c010303200a5103d250400192124021088a030460302e1480c3d010014400014010042c00c0c014110503a8210f150034100545408510001083c0344000341d000a00e2220b2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 484461267 1250 484460017 484460021
    0x4050606120a0204051b0f07050c060901050715020405043216080a090602160c0f0e040605070e04061707080d1e1101090f11030c01090902070f020a060e090a020c03030118 75
    0x10794241b004034a61200204415540b4aa0001c0002e65051140103503850032807030a9003c0f9204028140c444c40d24200727141d078031500c040901c0c0e1040c080c031f9542440000f5250b121806000c2824296019000c98658185215200c118045e01c050702003e108100700078034181d0f441d08201e25610582024110b03a0381340b5000c20050000800010b0825002103211207440803d0340f2281d5007a8850b02c01c4a4805441d4a0f07015400c642078403901484141c2d0302e002c01e010441c11b41c066608080c4a1a224441040c04000b00d42650030a40c4001004d004200010044040902c004c03005480c405000d000041e01011005000451403914824185e140003601e0a01c0c0c3e0081010300740014404000b403000724207500f05840c40070010003041d6000d02c1d0f90b2620b40c119180105c7e690041c50f605131920201c941c00c20107020000d401401049486e540843c1c840805a55100c001000030101903a41058008200d02800031000f00581407100c528010311143c98505030101c1981d0554000034805501d0040c80070302600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 484462517 1250 484461267 484461301
    0xf06051306030b400b010e070c0f03030b0a03080306120c0a143c010c0c0e0a0618020304230c090604060b0307090f050604060504030f06090203030c0604050606120a020405 75
    0xc04d41d64007a1200d0708083c10341206201d038040c0090707140d00e07a80d50041ca44004012106940040c50460754107001a1010214114050007490006070300022407020178120001600181c0c1d11007404020804945071910200801c0c070840000303014000000d07000303d000d108441c0110076074030005003601030030358035120030701d640c030021420040b4002000c0380c150100f21107070950001c3d01d0b95010841a000c40d400b42294401280d40602241c0f0450319040340c2040b00303038000d09801d03ea103440c0c5400061454081f0804403d60016560050f944d0a041c83d0a158081003240c6601040e11650f0209006000204180766004030582d407040345982e4541c0000c004000e030b50400280300f08080b040c85251584034801c0010368401c1c0480103001501c5804200841c015481031a0002d20200800e000040400420054052081c4001300b084c451513400242150810000da0300b040e4400c904010600504000d0f442d0481d6041d100142140f0703400c1c1240740c9882400402a001ea07488101080303042c400426051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 484463767 1250 484462517 484462591
    0x3061507120302030703060b070209040b090f070303090510081009201b0d08010b09010e060c030406050d0f02030c09211b04060801020906031303120f06051306030b 72
    0x2201c0e2030303030305801030000e402c19200c00300081d2a1000204510914008803840340b03800401c40d40e031607652070703175400c012010040c08000c0d42c0c0510030350842d03402d5080215a020750301ca1780f10f03051503504000901c41c1e15402c00d2014820004543c0500044000305006c80043d1038008001103401e4481010081031480c02c3d905148201500242a044246c5c8031a8070f10908074060080c0c440c00ca9102d14226070481080c01124464001005008425805801c10124810700034064a051074075038080603055421a07481030000c640c000804c0ca0542c1c5a6100c0d80810305c4c0722170000c40c1542400c030030565041c001c42d0500d500501141c3d0f05100280d0349415200701013841402201c3c11050a001940301c0c1030411206203018605003140480c0c00a0103000341c8641c0480a0305460465851408540304480c0200040d000e00c9840303001c0c4035001c60903000c1c01d8003458540d080411301074540300c1800003100c2ca00649902040c41d2107030074400260b410030010b4010100c0071141c404040c0440c1241d05201802d0014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 484465017 1250 484463767 484463783
    0xf011e05070c09050a0e0c01120c09080105011413110a3c020f060603120a18090b0f0303090f061308150402010206010e0103120c0c081e061b03061507 66
    0xba54034103500420305c240128003051201c0c17a071a000725070340c0e801c10501041c041041c0d101144803c0c0300550054000616900e05481c1d8990748440701d82c215102a0898000c441c201804d880c014245514034100c031071400c010030080031868115140e068041c480c0c10307400300154030304040d0042d8424910410b400c0c8417540150002d200c07051000d001124025803010150007101100c107252080840e05501c0f80c0005406440e0301d00f40c0d04103140c01940070040c4842400740644410344907034003000c0d141d0f0207403401c540c0000b00c0032603080800004103042c4005501c00e60040040d107202e516101c1074110304c11030503a616520b03010743c06451420140280c000191500c00d8026203101011061703a0715000e64001e030207558007a40c0f02d04884590400901000c2c000c100e4000e0009201441501401d04080c001d43c01c4405507034071808050304180c088a00c812468080000c816045501802640d400001d903009200b81c031607640048482a010040c0031612a84400c25040c03040c00d41e4800326405141c2c40303850707 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 484466267 1250 484465017 484465019
    0x17010b070b070306081b04060609080c06030a020708070507050102100207080d15050d08071403040b0a1409041407030c09050a090f09020411030411060306090c1303230c0f011e05070c 80
    0x20346941d06c0b4840c0c0007148114141080068040c3c040c2210009880c03003007028090102c584410310500c2d520280511640c650300b04600004108020301920006109101a10442e85024002890014880c25034036991703204208010000d04407008450f00b00c00442004039480d04450414104891642d000b0360b000110081506c040050010040550503c034061541c1c1400c241d40c3c40b43d0362400749000340080c9401c10002c404015000c3d4403280510719600c5000762404002d00003050507138080c00205132000b5982c0c400d0150040d0503000d0b5041a91007490080000b80c0361900161700b0384160700c0780130700b40c5640b10002c074102c0717900e904481710b000d0b00680b0602000c8112140305055034812034041c1c8072504007413140d035454035140f01200c0c00b8110003083c280064030b070100742448551207070301c56000d00c0018440000000f0b45c505105001891034a07145401d180d80764070b8803410704410003d00b51080e0320407598030107143e80024103000c850160307007030b440c0d1101769210701600e0b94426804064110002604 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 484467517 1250 484466267 484466293
    0x90c0a06020d12090503070f06020d02131502010c2a0b090303040201170609010620061504061403190302030c070b040603060e040b0408090409061a0117010b070b07030608 75
    0x30b900d005169007650303203455556900b40204200c40d040080141180c004008400c00b00701d056043c031810345e019100062070075040d00350072012a4096020031181050404c01003240001c01034040200840600003400203190b003641c02061420200c0310200c4480172100c0e08441913014201b0030b81d6040c4d010302d0350005810000c0081c0d607290000c840803400944500703040c012084418000500810029244e0030240c1d003482030694070f100c0000318540e1401d104004580f5840030400003e40203a10030348564440044039002e0001340c407030640050707500c07103424110310ba01a28005020400351954680c0300840d50601c1c07078224114854031180302c103144500d00010515140d000002c208a5001d07072410040b490741c421615003c2072080360302410348010040014081000781c80180b11001004000149640090743d07072008840090040561442e040035484425581040003198145101c10881c4401d61400d50b641846228115008000b080c5e1407011030302d424020742100000c0e02c0403400f0303101c400410303031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 484468767 1250 484467517 484467523
    0x11202090f01271707050105040f0b0708070203190b150a05040f060f0609060801090c02250801090305030115090509150f0909030d11130b0705070314150a050c030f090c0a0602 77
    0x60045001170150758000601c543c00f41003160222070f0f107080221092480c107884032a490300300b90000e0700c041a08112010041e80c0510039003d000490100315482000e40d4148200740f0880181f01e0f401c03812040c09802d000f5516400c440d0202e84048402007481080500b08030301420f140e0741300e45041c00c3c4400010481a812028000503951181e0380c11903c1c0e030346c40b0403032425118150800e0b8096006904414002003110b03030880c95100b4000030100c4499503403103440b801c4403032000040d40003030000720040c003e000000c2003200c800345591809200c401d040c040042d680b0900503250034203400400c0090449a1108803104410341c00c0100b45031141c1c40e06032840381e1291700c80582045139901d02202161043c1004003664420148180f00300940781c140b41e40c0e895030307a100c24421348241c41180d0340000001d02501308040e90b1105107002e05850a01e01c401d1001908001d401510024145800c205030307441c01d01c1c2965031121450703000305919120500094145030580c480c050700070b40d8000c0d005c5a42a000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 484470017 1250 484468767 484468799
    0x6020a03020c0d02011b170a1101060509090706180302040203130203161a0d0608010e0a03080a0b0d0210110f0607020c1225180b011202090f0127 64
    0xe60256140b000007181000205103140500030302088005194220369090102e29090301e6104108510301010300c15100400d6801c842185070005034038020300d03040880c0070701410004000030b0301e1210082c20141c00c0181c4410480c0610000c06c0303901c40500c010215100d025400958026104540c1e90070180054004542500c605900a20807180560b400420408640c011103400c02c05030041e1101154000045030300109025280c1038442d58049017038282842441d03c140b558500503d1608000c0c5009011100000c01e24045c0c0b80c98861076011303503102c0e4a40d505100c2d6040341d441240841070b0000f42d88155100024051900c11038202004000f80001e07498004c0506400b16018180a4420021022909800d8543c5a0444c0c10100caa00300c1c62845507034200c42c540c101d40c00d001d40f6110706040000c17140d100c034002192100d0341c0344a00c1d44c100d01c0c0849250302d219400d5285c0722415020401e100341c42d01c0840d040201d01000008110703000c40d014142199103680440c401651401d04a0000000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 484471267 1250 484470017 484470023
    0x7060c080c0a0806150705010e070e09060108060402010c06090b07230702130c11060903030f0a06050612040201020309120309040b04020703080f041505010612060f05062b0606020a 79
    0xa0008034501c903035840141e03580b000c1d031951425016690b842c184200040803044181480800307000c02e42c0002d1080c0036820180340f4038001404a5464240c0303110011001038664005501b1074801401540c80200e04180c0c002d80a0030009261152031410b20014940300300060180c821100600001070707840044080030b000300b6201c8881030950203121000358411608002d62041129008103004c094a03080a0340380c810505180301d070800e142e041141001011510407010303400c00030170003140010580daa560050200341c02085040d041502140a42c0304046070b101c040b81c44900094110383c801c000301d921900e00a0443e181c84041c3c0050070b42d580c0c0100101506c510f05140c1a4111414213209841c41590503581d25007036a15940d03901d41824201030020b6585000c00c1070000042002802104d0003402d440e80c6031a02c074408548403004943d03143d0841036800002580800003595040140c50510003000c102c4c502184492340491207044019000c003c00c142000c1c00051045e401103080c0900c140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 484472517 1250 484471267 484471277
    0x5030f18010905090114190f030f060c02120301060503041110020c1c08030c030a0e0102120609070918020906040f0306020c060c09102a0b07020712110409020a090207060c 75
    0x51224100300c8901d04c24001c03031160341c411806140003858100541404550351540009209442e660140031120030fa8200391000d036009910308041000078403c070383d00c08400e88040c21001c080764603041e805210600ca49401c2000c00f0010030240440b2041c02c01c09110014072110480b02e00910280d142d500d41d43c0d40c42e1144502e01c0c022600d02194100a50342581e001d502d003881d69885d140070048941000d012101066910001000d40040c00d00c024462100c41d40c00740c13207003480e2001c108200d00c00c0082c42001088440281000003166882400301c02b8408106c016859401340c20100da000e01841d80700d9110301e0791580e000000e000d0309500038400380c82818146d603280c0c0d4402c0c654041903c554210160400703101150780c03c9140c4a5840c4000b030164046000c01e828001c6180214450000320054420480f0039041c030840c02d170100007407001003062100001c4c4261191321500c0e0300140c00c222003030280d0303203904e030030011941d41c02200000791009034011910b50566060174070043c001c235004071012034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 484473767 1250 484472517 484472519
    0x90102030c061f0b0f09012d0c141f051302131b050307020712060f1b082d130f0506011a09031b060903070b030a0c0c0b1305030f180109 60
    0xa14020215082503910300743d49403828044500440d441000c400f00c0c0301c84002da4541c0f02a4903001c00101c401c0c241c1190b0703504810200d103814440d29012b90008100c416505c4564000c2903d6140700b003c3c0399103880482c000079075a0b505030081c851180c0b4408025400f900b51051088500034075444410011001074041d0425141d412080e6418803080e5a45000350344000d1041240b040058002c44200340300342408a030801e403051210302944c1c280c1190980d00c1e102060410310465100d1100383d400350b40d0a52500d201051075541c0d20124000c0d2111030009002c0d10001a0001c4016501350101caa00000c00503540505082440e01c0740d0080c0100740a00c05042860100e801040090300c0c4a00c03c01009006a000308031031440311080c0400803143c01000512040b000f5550031b01484004090314640c4550781e14118003403404440c0c010151030140002e044640001c00c6100006503802401009489500c60042c2060307884c40c02101e408074410000050340c100480c0c0f0301e200c0080d21101c04e0f26280a86 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 484475017 1250 484473767 484473779
    0x31e0f0515040b180405030f040303020f060f0112060504020604030209092a010503191509022a0a021003020705031303050607020d0f0e0a0e0103030201090218060a03020402090102030c061f 83
    0x80c4109000c0340768007a51000c4c0308503844020790700858100303214104992070312903030188620280c0c00c164010740158014106000e50f5020910400da440003010f9100191366041c8001c02d2000ea40b041000b0301025503030f0303000404548850040701c000d150020710b00312031850050909507950f0b00c00310302881c140c01a4040d1481c0e8002ca214045813000058640c1415982c07007009410b080c006110361031581b5519040c242e099070003051140c001800b00300c0409669071820107070b2881600d1050040780e84a8070f051403007117030800300400d65814040e41150b0400c020449601c080b00a4003440c1c0c000382450100091000389030481402c4442183d1050080e031381c150344ca00a042c0d03210504180c5c407034041507000603480803080c4100e02c0425105001485100211788a201c20a0394820903001107000d42c4d0350b80d414405501e03010311810140120288108581c0c603206000c03410a01c8507120003400390b03402207007424070b83c3e0090042c0e4a013529140c0c12203a0910f4440348c3c00c460060326400e14622294410004186 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 484476267 1250 484475017 484475021
    0x510180f1221080a090f0210090f06021207110315091506060c07060305090304170607140a120207020a0306021911010e15100f0909030306050a0312031e0f051504 71
    0x11601c05a00d40f0700c182e035242c0c01c83c1800f605010208496100c002c15600c00165150b1558040a80e040e50342d560207070f070920600c914001c0898011f00c0555100504200c0c200b1000802c0344c0402e41d00c080b1100c40c00c41c8440101e441d1056040004550f0315001c2c0800c0569440040c03580c8d801440044000c049490710414441e07644a191511910b9422525040c030026009401040d0805009021280b9090340c42e10f852030307800c0781c40b0002c1c4482d81207007060000d0154007024a5039840500855076141031342d5003202030002c9801902d41d003581600820751006666031805c8240c003c541001081d5a2041030a0210110b00704c0d000448000c909200c0119210f02814411220310181c18401400d0903140181102d001c468014006015181c0c41100071031542104078001000707105000d00030603039103103c3c9405411303100582c01c00741c090f40034020308202241d001d6000303065102c2c16080000352500c40f800681560115500c40c03456003424107640208200503980103520400d49860749440280d801020002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 484477517 1250 484476267 484476323
    0x304090e0706030513200d0803160906020639090102060703060807050607061119020d031b030510030623090a0f03050a050903070308120f010510180f12 67
    0x4035006007507802c1002401885c50320303401d10780c80d00906d4160f0394190b002031020620b401c400c603070100000c000d008a90509005261841203203050140d5400c0c10070200a40c0d0303a070010310700328080b100b040100d420010080258000c40e0301d907841c0140a0b0b10720381074501290f444656482e005100b010005505541b00e849a9001d0340c603848082d003603140c034000400c4041c0d04031034005c1c1c4446644005540b031030002c5400a042414031148a000850315050010f810b2070307401c20b44a024942040c481d10310007400210a01c49001c00340c10005601d4960400003500c54003607400041140386081081c5060072510300c010640a131000180e85603594481c52010788030400d80780c0040c40940110b59000029006001a0585c40f181d403030040c3c10708124200182c07518000340d106a0358a140086c11488130900513240d076902040f46420101594074100c041611918480204400c004081d001c3c5c500a2402c41094001013030807a0190510584503c5012030580b03003520304452540580502800003420460b00203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 484478767 1250 484477517 484477531
    0x305031018140907360f0e0f060c120712091b050415050105031f03060609270318090518012d23070f020f28050f0304090e07060305 58
    0x3c8030007090b00320a50740c1e801307200c08540c0e200c40e0140700300345c00c0410f00c10840094203128000c02d104400080f020305040211113580100d400c8401001356444a41085921003840c0e0038030310810381d44500d001c41c1c08641400401281a0416452400740104200034104128509000c25071155a81c401c0004655101008031104254071004000c103601800203582d00048010304408600b452100a044c0c540d040d4000f1548250f40c0d142c18410b09490381714203408240001c038421200c03408404078031004d100000000b4208000e110401191803400319081c8002c001c0b1607018480c41c20401240c8515500121030720845600c0e200d21140140e68040b89a001140010f920748400045003e040c005000d803d10300204c4400e804d61141d03907022201d07200511519a96403000030032417400500a06280400c09600c20650240761809640341d12411703c900a208039148851103040140b03080ca080c4803042412407800e000105000075001060303041b542039140401c00751a8003075100e040681c126601a00d42c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 484480017 1250 484478767 484478789
    0x2030118230601090c14160b0a0e0309040b01020f0d0c02241b03070c0b0a080108030c03040b030a0e0703030f0906020d0504050f040e0102162d0305031018140907 71
    0x10411454203501030842c0728a2490000c04100483d00d0506d100e6000001502015032004204028000d032103451540101140d0001d111030301080c034480f5541e004070400c0714801c81da82c14411810380e0080214414414040d010703102e400040082c042c00c00c1602038400ea020700c109105042062407410102d40140300e514080b035061800a4010054241d50040d023010f40303101c02c11582e00852407602005004084c620340b100c1e030780e00100000800609041c1c1c001c20450f0b00600900c000ca04011055509070782007050011b80b40d5070b84c0b44164003e80a0164404464021039002005240c5e018040c1090311135070342c0314180c0e562350383c0c0070807a6610304007007104001030018403092011307260485200250030320003440403030741c02080c00000d400ca030b0203c041d410f00700f000d60b00b0320420405100090b14080e9100c80c1c44851864091001030100d40724070100074100b0500100040200e419154004003400c01c260400c60070040d2211403100a09141c0b40c030aa0101c451000a4898180001c00d0800d580a000e41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 484481267 1250 484480017 484480019
    0x8070518221a010510030e03041503020d020a090608070801030f03080702150a0b1008090601030b180f0a02010318020121021605070504050c07080f0307030902030118230601 76
    0x10001062252280d01ea046445141088011464888518542105507219811154545000c000264030744044040501d030801301e84c040545c00200c252411079400d02c00004540440140c200c0003440368107a0768030014030102d24520701c50750082c0d4401c1611620b480d10349194568007000c1d507910400340b00081c41c80304c81e030001d1800248504038050f00308820f401151400c00107441c09110701c4004440c01051145c2c0c650780e54800c2d00c2d21b00526124100c050420490728145403d0140d19000c1c140000f83c418000080401c80b03002201d60b5840c00b00300020b080d5034928988040c15a00c0301e041180c06da001078104004c803000488507000c1107110560507103459804405600320740786080403e92007801070302d43c20f001074200c1c038104c050444c400611801c040d085042c10002004203d03500030301981c8100030180090000252210708446900e101000d401c0e4582e03503099012405071070280002500365003881103441031031603c2207140f0f6100740f0031003030301d40984030300b40a0f00c1394035220345045403080c1d00041c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 484482517 1250 484481267 484481281
    0x30f0307090f0b1606110c0604030e012c01021c03290d060f020d06030c0e100608010605161211010515030c0f0409081b0c06180609010210050a0608070518 68
    0x210005242e0310030301012401d1014950314100d01d4014042051f45504600c5c10001015485940603c48120034204030104c0d0100030b0040580854172104404282001101c00c081030f0300801030001205000c284150f421013140034010042c20a00c950380c2030b02c1d0b01d903811000070b41501c0682910440c90140102c3c00080f030b50b8440c2c0c80540b0061202e000b1540e800c108032600c020180c06002c01950054284c101114039001342c040d68941c00500045130306002e60070500525500003002030464000c2c0c54145d8a54024080101074030002c0d440003000c01090b0041c40300f200b03070000103c4c0c3da0840c0c610002c2141e1799500481300f51151100c0405649034001140040051820b101c2c020350a4402600c00500d01c40a582c503803407a94003002d0700d00c004043d40341d42015818010020040e401405560060504403100c030000c1500006403441d610462002c6824890340e4030030410b0720030544000a00380424140840d0200007000140200342c01800380e0390000c030f064180913145110960204c14560700c0c5a851030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 484483767 1250 484482517 484482547
    0xf0a090b09100c14061618060c02011112030f16020c0303030a0f020d020a022a09010e041109100501030b01090b0409050705040b0705060a0b031906020a0c05030f0307090f0b 76
    0x340d044844041101100d21340200401c0a58440c1c1c0c031030303403440540000020001e05580344506080b14803012004d000d20200354007034a995520781d07080c00c240120303241004010b4108118082d00402580c00402088418410300f01120300800c900591034492204002080361039803400d4040c00d4066208101080402042d81c4c440821408140001401c003165070341444240e074492074446005a010700613201e80c4124000e0030782082c0409940740e410720f0100710081015100144543c20050040600180620a40200d60642150000c14030000392500440450f1503400074004d140c0003a151a0100a0550182c15004240c480403580c10382000e107081c80d60300141c10010302c00e4080101c2804001520000c9802521036640300c0c0010300160708d0040020400c80e1541030901e880b90340404c5c220b0500740c5a01c84400503803a04280e0142c1e807803154044c2a500802c85000050881c40f0004a14103035100c4040038501408403542d030220b2150f40e40748001840013803401060200c2d0001c02060380540e41071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 484485017 1250 484483767 484483787
    0x604020703140f0c1b0f030601030507060305060d050d1806030e06270a0b010819030c0f11060408100506030102090a15030b04060810060905090309190b0f0a090b0910 73
    0x60307040d9494200c0340038800d42024a1781002500c020340c00060613000e85003000c04400e210b0310990042c10a580b443d08c409a81c0c072894882c5c14103059960b03000c43c0d5984c55515040200f203402c0411500300d00342441c001000e500801b0007640801000060106209100f40501082209000d00515039078454040400d004840d001ca00095580c11252440d6075810610021212038017541c041b0310207601d009a030340c0c2801e40c0010203a0240d031070380022000180c1c0101000207041d42019611000340c10034030f0b1403407407403ca104c040c69108501240000e242d04c4001004000c2c4000740409010a80300d00040c5400d07030242044c859445503c6a1041c4000c11282c0d00d010b1407181c4901d03000c02d1450310390000c034040f240260001c941da9000f041503100701c19228003584000f00843c0300100140d24240c00c515841c0c0c080c420090b48680484076000b4242c14024a021000d0880001016518421000408941d80c4010495004151b03c1500042d8035400302c0c0641e60100409004d60b60006100c1c0c00485407070081d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 484486267 1250 484485017 484485037
    0x10050f03010e01050f15030606180a0b120a02120a051e15070302181504050d0201030207050f011506020d020303071b060f0f0f0509030403061e05100509060402070314 73
    0x30b6202c0c0911410000d00070640130750b942808000b0700d42440c222100d101e800c040100c1d40207902400c14441c141d2140d03054461041265080707080941c031810b0340740e0040c02502c1e401507404101c41c18800c0c4400400b007413144909100b1201035050700260310f0020f032545800040901617401c00880022a0119209050b4081401405079030001229406000c4480015030300031780041e90104902d4204450785449504000c03040b02d5042e010458032424050314425030203101d01038412480320508690003501940c400591101c01c0c0c8541c24038007220a4004c1c01d404c140184503003401c7c036000030150300100d0740301800fa5982d805585560750341101540c00a444070003420160b07a10011410111309180f094000316840c41e600800c1d045100300800d01501c040c0304041000c140340200f80b1195401c00821501181e80c0400003140303240f044144104020032003c10150700f181004100044544060700c0101519000c4030085801e44035039061100b2406402c00040108000d085801d48100701c00011f0084541 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 484487517 1250 484486267 484486271
    0x280504140f0712050705070c0602010b21031201032006070f0f1415040b0c0412060509150a06030b07170f040c0b0a11100e03030403180f06080405120310050f0301 71
    0x1c0720707002c2034104c9904880c5000020404181c034410444607400a4000b40514030091102491640000d02041208280141c0002000620411a103018025070304174040380200340d1060360352403c10280c081e0a00c00d100c6102c5036400203003400e9140080075500020340005c05889070b800c0654031540d509100f10300a4131001980d415000c8400001c01c4154000200130003190114205841c0c08001e100f40503007208083c803020f01050000c28084080315000d650050310101c0c09845402c0100c2c1806600103044510740c099008001071440590840f81c11684a080940c02507079980344203c03956105501d2090340305041101041405083c829034a801074020107100701c05555805000c5070a500c81f0621401185560b1803c0c1d926250520003003201ca0f00700b40f402d00c003a034410320392141c480c40001c00050500050140307000b0b07042000350807840501000d041000d841c503219000546206001c0718100c0f014032451030001002403c146c20780c0e025440300d26200b81c5440c10001085501d18003e00341c180c243d9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 484488767 1250 484487517 484487537
    0xd090303030b03121c27080f0f1b0c04060b041202010215150405010b030601050a120605060a050c010515031207020103111615060e010b0711280504140f07 68
    0x2c00200001c0040d02c0d02c0d245040d0b0204040200d5070251b0340035201c4100b107001d02e0b810300c00d40000e600d030803403d115902017244d50f40c804824120103407074041c201d51000030700c00105400401003000e00d082d0900030601d10496507009004806c0109a440758010702071402c2007413004202201c404440d0b40c0406205006171004081c09000c48401640101d5886050001d40c41591002d81010b1086501602c00c050004c0d00d0340c9060800030f009885078260102c10020300000c4941003444681c0200c002c0e15005140c81d030389111249004003140c002c075403030900651925000c1b441c203040001c27120a40ca5800740c050000f9203030315000300c00d0a1f040001c0c182d040c1522004c00c031068540ca10000e000c003030108020581101080e051044c0d42e5064260000001454a801400315201c0700100078111030151000755900c000a10b4481e100d00b106451650300840301d040c1300c0044103050320b00703210102f00044580100320354400800040c2c4c0c051b217126080c00d02e4032601246104990406003640a032042c20b00c9034103a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 484490017 1250 484488767 484488793
    0x40b070314120a050a0c02030702031203040f0c09020706060608040302070303260a0603030e0102062413090b0708061c0b07091205030304050c0409110f130f020d0b01020d090303030b03 81
    0x205011140501c400341c1e91303010040d00c00d08502c2071a00c001340074802141446d0140d40829600c5e0380e4114010b0100001000182c1000099010820003e501140001100340e0320302036003001c0e4100719000c64116007030a0000c10124414002e15106030b0309a4000d040091540d00c0543d041091800c51841c2481005940c861f0400214800d03406221510f0000400c3d0b032440c1002404090281140c504641010702801404610a40740314040101d41503c007001e901c0d560001101800780448545195040008903c1444111102c02c0d1090800ea2075081060f80d44070104800713035901004001d04c0c5c5a51036103603c00305800700c0506500036154144400c065454080d851010340c46018115007541c0000104400c01c40184a444d8143c01e00f51020700940312260380b064003210188035644c0c001c11420414061981c2d035061000390359030340e82c0400c00030321b4000900700010b54032002004049904054800e401c075440050300134811500742d522200143d007165000c50241c00c0444d11242d04d0f11582840ba004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 484491267 1250 484490017 484490047
    0x150e03090d0804050d050a063902010b12030a1808100203090a050307050607030f021305010c110405181e1f0b040f05062d060706020409060b070215040b070314 70
    0x5000380007c00241005141000a40d040c5450000c030000d0220300b55800e0500707040c082c01d0340e0402c21618070860446840200c0c01015041205035220004462004003070802100a241c40c51803590f40d400b01c030741003039011781c50780d40940b284407034170780c800c15100829a00303e07406190403c03801002c1d1aa00e8601e070700d6292030758105500940b400c2d00801c0500c05141d41600ca9207000102e514020340c18401d031a10901051601845422306110490702c8940402420460080310ba09008008105c0c074181200c0e0240d454043c0100c11090703110b40c03d114603111007040490b10389990908028030303101c00b010303801206c1c900b44401010007050300d550080f5825507a6025418114005510000e52454448204280e01c0503170b02030a0f02110001c5171100c0d400c025446401900b04040d1000d50b6281c40d9890410020b10031684035003030780742c6409400304500c0080c0d8000c00210740200d030140460310351111000340b0342c0721320b01c02e1500000302003200200281c00b607031400e1801c21a48201500340a050030400c2c003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 484492517 1250 484491267 484491289
    0x3020a0602030307080906190902041d030405010e030c03030426030d15120b0402010f090305070b030a1b08060108060103090b07030e0d1403040b0a06120609150e03090d080405 77
    0x400742e00302004102c5501c0d8001440782d0f1051040000703110302d0800c11803010340300207130015007081c568076001c090041d9100c68010901160407440008550040002403980340d80080c0592400501040e90030241031400007407440340c0d41d0004016500d0140f801820051101080c8411003040c65030482c1c9103140c0000384094a95030102540204450041651150100851f504003460b648100144ea0010451480f8400d42c0a682803c281c401500c0030303902a1290314155100614030f05c1018070101d030700c2d04c071540558000c103072608061241c0d88001d00441c2c61032445402080c0015a4540011181e603c15011300b5000041810002104c100a0b15001385c5507000b02c0340382012070b40b611514654618100a84040c0203c246403101100b2141e00d5070461610025202801800c9104080741d48100305601c280028043c1da03800700312480c840c2c94920050701e0004030548042010350151020b0750000d02038030020700035550145240103951000c101d802c440b80c02d416602010203000100b03039501c4512100c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 484493767 1250 484492517 484492529
    0x90b0304030f020715080f0901060b0a031a12030a030b15031e07030c0f03110f04030507030b010509040b060909010f1d060a020a0f1d03030729070807051303020a 71
    0x10107025503000e000c0e240840682c00f00000c0c00c0d01c00c0119020315404106d82d50000c00311415200540c88a10f00c10340980781c80e401402d000400000c1e58800241c2651144003900e019401120000b40144104030035031027140d1088005410070403108950b54400d520a04003032100821110700241141c8008000d600110b0b40c42c40f1114000540110603905442d6840d840085440c05015140758040014110840c0e01c030114141925241d9200314042107000b91104102c10181407034981e0f03501e0401d2a680d00d010b22040e80c01410000011445080079600a032003150080090003407a00e4035400c1c80100400204031808656075010400034030040c90040607802c00c05594007035901c030414100c05041040c05800151014410003600e005070b0340150107001200350134103060000301c280005944132101303c415250f60501000440408104040c8100703442203038002c00201c052501c0750000c101280c029112280072904140c0014009803144005182d80d00c41080380b02c1c25503653342d0115040080304e80001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 484495017 1250 484493767 484493777
    0x3031e0515030d02190c080a0813080705090601140c011a01020c09220c0f0f17010203090a02060906072301050f01060c032d0c110103021201090c090b030403 69
    0x801007440301c00e440c000107800200d014080c00701c011080603607104000c0c4460741c111541035640314103000751001860000c00340e4105481c0005c2c6079143c02c0e81c03540e1202841d17107143c0100c440c000c1440000042d044060310300161a44150b62a900e0054440703039455a5618102ca03020407440551402c00c1c01000f402d90b06440b0000c00d1000303040006800d0260f003443d0140100702c84e204010303030100ca15066a1031462a02d1030650f0140d00303810865601001600b0119520840f500e0000384040700c2c00415044590300d00c0c4400901c0d503050b09450030b0340b0041d900d0041d0703940301001041c094507000300100b0510340c00500c05032074a0156924044540351000c03000d070114290140000340d2031002c1c060140d0114500101009035810003002405082c00100b0103010050780103268071030344005500208441100d404e1500c8928480e0000a1410082040c2101d00107190340c030405071540a4000c1e200c500c60042ca0700c00c41a030a104180009140c021000000c00960b0440020400701a000a5018901079507070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 484496267 1250 484495017 484495021
    0x61a060d050402090c070c2105151b0406080612030d090f0605150303040e191802010f09121704120819080606030402040203180601090c1407020a0e0403031e05 70
    0x1004103420000703000302d81c140c40030817001c0b00180814a06009903442c03c511807502390580ea61412200d4070040c0c00030b00d1882150624003182204060451061b50303072180912068003a2040300709280240e200d1000820704050205080c0e24012884403c1082c074081180c1c2420401c01e5034000b070383c842000a0751000c244a480009100080c06100c0d440404807103160001d4600b40d011903070320311075482a641140c02e400003094101d107141c1d00e29625804480d005105441820801c0c0e005621340c00c0049001c200311801d441c0c0301c03a000c1c1d02614100d690906c54003100241540300c00d03100800320480351510103402c000104203104100c40400d48039001c5c144464480040c0410742d40d5011002540f0000d00c0600c004200c141d64843d81200c1e482541620090307202d485086642c0e031f486510040002041c0920400440d9901c0700d60b10541c00e40035240e444030500f801c0030303003c4940d81c401d03440c0194010718100f4042c445a800e13003072a950458031a02d070024050041404000c20702d404c1418a403809915101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 484497517 1250 484496267 484496269
    0x2b02090c0a090b0c031207140d0c020c24090604030503030708071101020306090103020d15090602030a0b3003130609090605091e06010219050d030510030807061a060d050402 76
    0x2000c0d02c0a8030064003168a40b02d00c007460030703590340240007040310b1581070a4001000e50303200303035080d010120151190a840301110710130100a01200309804005114250400c45c1901d440c512584480d00012a079403446803038800010341e41c1d0311846266030818070030000040000c40820055120b03016540c0e5110850808110042502074154a4210aa070050003400080c1c0d80b591903041c1181e03812030b6030440060191401e00704101e40003002c00d4110380b9005052040c44071035001584031350a0000101b1803400c088003004208403810000d014090031038001c803441c14061211002072443c4a800703c80c200713a01d0300c807503c0c840341c41600001300081d0407210802c801c20040c0225006410300321000413a505d4000c01101c007098480d200940451440000314016900a01040c584884030909000040309241006991480b070903040c540001c0c0780c000062127481800c240e000079281d020605030700c2c180244c0c4032017000d0030030700016010702c07180ca1560307102c1a0b0340d02c4000c03e8220321441000c2030916181c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 484498767 1250 484497517 484497527
    0x70f05120303010f060f14190908011a0402070309030c080c0102120408031e0c0d20030a020d0f090b030906070e03060c0702060711090907081b2b02090c0a 68
    0x550003840d0391060005200c42042503088405031186450200003d2981500c1141c1011403216250322032400020f14004401d00710388030f0b00601040343c0303d40a580fa40d6107985403c0b608600c400c000300420b007201019013840e10303400074072005000f0f00e404031405480f070712400714108456205040380e9001506401c42e41d41c0501000c4541d401404002e0b0915181421164481c410703030280391105184248214001480c000c244c4032140e280c802110780c80480018040e001603900181c010b9040016128040d0f40d1100001b01ca180d007140e07a01400041c94020002d440440110382c3d0b0009204400d03101050155005024601c05c00c4c0d40801440c95042454010702207402c90440c2c03500a0300000c0c20000c400114908507a0020780c1600ca9070b80d58811400d0200d550101c00300c159511146400600c4030a660018595064400101c00c0c3c81d4840c0325605101d040b803007200f01642d000190404c41201c1c410701041c46c80401c82080e80c564840711143d0740020001d4008850700307803903400003140740b0b4400350344a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 484500017 1250 484498767 484498789
    0x50910050c03010608130609080d0e010e0f030906030c0705060c0a08090a032007090501080304080607030204030f1112160815040f11030a06090b0604050703140f0702010b03070f05 79
    0x1c00304586194100701004101440003813a20b0b80118070310308190b04202d619403296a0007900701240503120303c0041c040d00b01a04205000d20155800c12481d015018404201c20107440c807070000446c60041c200041c040e0b03540005010608446c07040c02041d010480501425108004035148599664651070029000c40e0019242070200d0340910030542c0003a40018100c0c404c2ca1102c2c0e40b00300c1c001140c5404900d400703070a400c42030500b8248000015448400000360040c2d541c1c11069819a90325140c0481c1203010314480034080209090316000401c00c07140040e204100d015100103002900b26004520f0a03411303a24803500991152410001c1400074840c2680721005105403540600702a2541e1202c0d9003a0900604480801d065090744e9940805c50140c080c1c2d03002c142801610041d050100c0101e6089405500540c109800901847d11078030403e103001c85429144070194541445000c2c0c1d0480043c0b0304405c0d5035890101071031954007005414010649070543e0b45241d81031030b082c055040700c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 484501267 1250 484500017 484500031
    0x50a1202030709090b030a1e0606061d040911061c0e011806020d0b030a060c0305070c0317060f0a1e0b09010f140405101106070203090307050405061305091005 70
    0x3062060021495020400204035040c0c1c040c0400c0345201000041c0c200350401d0401450348245010911002800711968056180100010042a070303aa00d02074813a01c500740c0d0070b09000b40d4060380301d40952030b01c0c1e80042030302401348080721501c00e64032012032920b50005201c0200e07031980c98242d02c815030281c0100503007182a00c00034400041c3c0d0060002040f000e44c0002406107401182c05407030300d042644124901d4400070100d513130141e0982000002021450320035000281044c00180400d8010342003280103690564903101c128100da02c000400110140c09950700013180c0b010b0100179607070b0b00c1e8000050030300800c4584042c50f400999040e0f03064940d0000005100074803000045a070400443d0100340068100341e0b20070490504404002d20968008542c00300c8001110416990702104c0c10010075103200032541652a81041a6501d000c0d40c0001b55140e03015041c184160305290304036a42001019203e44281c4102c2d0641c4015140202d41d4280142e1201c0c03c00515004903000d410b4021030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 484502517 1250 484501267 484501271
    0x509010504120914150702041b030e122d0408010b0307090b0d080f0903030703080a0c08010e07050a050903390906040b0d0b0916091a1915050a12 64
    0xf1504281d00420180c0c4081c5a1007148441c400b411005d004904035600158010b0080001c107004500001c80c42841010050001c0e00c1e0046030a401e550010f02d5420042d500c000321401c001e01d03078440c1c501018210a004074a00e02003100f044886005c0809007010b462504004501c011218003418602241907101000650401011480644403094607200c5990014031050366451506402016071140030003158140c400040d4820a00d580302174583e00038000b1000c180081d0b02d220404a409600c00c2c05201c804941d0b240100d4405070041009049900c41803c05906091564000a04000c02d40c4001207910076a00c0303405090034100d203004558440301c1d03c01e41c00c6011a01000c54030300e100007018103005036a00c2419140c240e07541182030a4440c0d00500c140080d02d45000016142c08075035144458040c2c41a5000c100401365018403880d0440a00308114400c00000401c4900c64071414580b0480c00c03010004600214840914030030501c140e11810303500e400b0210f00615600c0c3c03003440c880d0401c1c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 484503767 1250 484502517 484502519
    0x90312111b030d1e0c021c0305071707170901111005070e0316030b04020a0905151c0302030706092303130f0303020a02012d020f0d2a05030d05090105041209 69
    0xa941140d501d8413462802200b088482d1000c621a20104140b0f902c40d5042c2143c0c010030035512900416180b441401c50a5010800b0f01c000174660203410401004aa95400c1501040740010060002c0701030504d41000e010304541c6c0c1031402d114a2a900005158450040003009034208070000090a001e8000b415800c04a03940c8586000c5c0c41e000003487c5001020100e400d41d501c2c0c0062070003412051760104505c1c00e091a201c440c5d4009003034006d009103c024443d080c0e91207a5501001d0b0260150080c2d480c011441d55400c0090440c850100c80c480f264940c030880c501c40f41c0c03903600c403d0b5040780000c6541d00040b52000304800019408440c0d002c0003064144000395010400001f003d50a08018080080231038213021001c00d41d0a070314090960f00c4e44414241540060300c0c2000340e001d074054034200107900100b10707540c440c1c540c030f03030660b000451322880744030170007686c1500c0040d00030014ac90a01c85040e4a207015100f068420172410b80d194030910040c1322010036940302800d12810324103411 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 484505017 1250 484503767 484503797
    0xf0414100903050a080a050d0204180c02010b01090311030a06140f13020d06021605010e030405011805061c0209090109050105030c04090507210b0106050714030703090312111b030d 79
    0x40c0c1302c03410002c5c40d91030f021603401a880c0c0120151070b4030803240002551102c0e05c4000c050441000340e840e04590701d0410b0f05c0e00804c58010700c01c1030500d00c0b06070348680180d400d60300e880034408000f90780a81c2512410140001041251261404000c1c0003550752000b0705003070070426900301000e00010840da0220306114010398548520304101944180f0145e21546030070000c0503c09103456000d00340e542080c050306030240e400301c002e00039035400340c8402071030001252844080014034041d49810070420083d4001090408100c1001016103000140c0340269900108440520a9003c041c60b04d0b2542c00500c40d5103014015640c3c03001c0203807020044404240c5510750364802da40b040c4601c0d003c444658201010116880342900354000e002110196516440100113078010b19007521620207418a240d220318010040b0b0f00102d4260f44c50007802425500c2e0190700308002c0301d407501401041d009240c400301040c0704407651064203003200400011030105241c2030691401c1ba0404124210f1220f401b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 484506267 1250 484505017 484505023
    0x10021504030c0f0b0906100b3414060a1a01200c03070e0a0e071404023018010b01171008030f03061302120406050c0f041410090305 58
    0x4841d03014030303004491030302e28105005039811504020b0328403100340c07041188424001071010302910039a40909a61030361442e03aa041070140d40e83c8204c3c5821444030305600050f4143e074105959488001c01c2e40341d079800780d489003045201c81a0350f00303481d0000302c100101d8114500c40c4d510750b00c01412120040d0340d241000205032142d4800f00d14103001c1e00451458441780f04000031101c5040150032212126190714040c074003403c003103c001c0c0409050508603081031b50045100303021100c8010307000d402a4101c60420000c0c1d0011503241040078440b08940d4011a603c40d03034416603400c010426411400e00d88107034249a2132010300b050f4260705003044543c260340d11040000422403048801d100b1603d80e41043c030000404c992020206100110752030000d40c28420003140950f20031200d101000400c040c90704203078080c11034100d01680d10741c0c0001d004108d081d00710315840020301f050f05243c0a15040a40c001da00300790040a032442c0d000030030000030f080c4049500074a2003241403007515a403840e924a50303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 484507517 1250 484506267 484506271
    0x130308011401120f0b03030a090521070603021c1d070f05060a08060409020303070b0106080708070e09040c05090a14060306090304050d0807020411030a200a030b0102071e0302100215 80
    0x401e0781e444d14541c003404810750045a0190004081e01d58844d10070740000c0204405015180c2f103450400c0310b00e4040d404d001c00e00046841d03c4000740220518107682a4000d4220f000380482e4904d8200d00303006003030510720503030040700da0f0440c04000c000c0b81200e5191612825800c81d040b00d4140c0c400600455580c641500c14540451034100c1155480c0c1001c200541114a4025010305c070100d40c445c108111020401d041c1e404c00e5681ea40d041c1d590080c00c40e07101078195000b10120b0b450780400e6442d410710700c0440f40c0c058020302080200958070b20100342d1092040382c1d02c211059440b04943c04600701c000419402c808110300a11050511220464881c40b46100c0c1ea441403404681d04020408410180c81450b50001c1042280409208021002c1c1d40205c4152a40510f401e284405000541c80101102d0401c440c500341820300140301070700100000e03c05d05040d441800000100c21703d170340d80c1e00c64903004a000c00c0d20b0454518410722410304030000c1d00d04250341184015001701061086516 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 484508767 1250 484507517 484507547
    0xe01030b0f0d020301020d020d022d0a030c020a0203060f0108010b0402040e161101020706051b0c0c0105030c0f04092004080303070e0f0603040605070207090b060316020114130308011401 82
    0x1001c0c9507840000d0082c400d070364900c9520303400455240010409c540c00380181503110b500660f468113116100700d045001d40d100c103008a03201408215038280c443e41c004080707520b650044070000c002680019203000400c0390714850b0940c809006004000b401c0c055200580400d8606509060030201007414014000305151801481803e01d0001d80d031240a224980d003491000031546c4141505004003c0e00048540c49054142c84102403e0340f90300f00101c800400c818000380001ca00040c00454a56002402d0602d4414080c45910040c41001c0010401083d80180c0002d00c1068a41800b411402a041c2c8583e8500c0601c000c000d0b0380c00100480c0c0e80980c10b0715010060510b10400a03104140802c00030340c000c8ea000c804c110400c642980424000c20303040d000c56405998811803001900e50551019412600c1440490345880b403c400c100017162070745c00045001e80a26900e1203201c081140d0480f043c64070080090700703045d0080d0322180074000b0f050f902c4034423000210000e400030b00560781c91 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 484510017 1250 484508767 484508779
    0x81f0315090c050d171e040f1e0b0d0f0b0a06090305060106080408120a020409020d0b01110607020d08090703050d170708101202010903121101060b0a08060603040507080a030f0e01030b0f 82
    0x710380c00c038803064403191508452046d03960300c99440b402419018880d074001c7d45644509500000c40700703846400b0761000c441c2c1846803e407810a00b20209000b0b8445817515030f0344103803140c0c5031a205a880900c0300002d0003040c1d4503114941e103141009440d100040e4443e8080c40268400c1c4004500c480d021104070a400091800b09034560300c101e04000e200300da100d445868070100303c6500c0211950400300c0007601c241c0c0c80003800d101d5041859102c64080e0b5919026a004405d013481c5035025680c41d80e881240e480c00c3c5c1d811190780e511682e081148c025001000180030030441e05800b0f042e280280d8002040e40340c06003491804100c000311942d2580508039400040705014011a0322440c2c03040040e40e48514240302196070200060504039580108209550910001041045001081da000c0a0495a4104080d202d8000388081a030024005641e280241074000c1045a401c0140251940c8299140c1d4018a0038040003800c1c01190400da81c105030500a4044656417400c2c00b00d000c5120442e04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 484511267 1250 484510017 484510027
    0x100203060603060919051501080a0605130f140405011407020706020703020d140d0e0411030f01060503090a0c0815090d0c03050a12050a09020f060307081f0315090c050d17 75
    0x308609845d0003101802d4994188130400010018882d1010a0500e082e25a00060b48900340d04d42d0a9403414083c1e6900140380c04105080d5806942240c0801900c200b00000e1080031501d100d00702100882d01603809a4449407262604c0c4007044030181d010495201410a55040810094842d0554030001e4411401401070105000041c0240480d401904045518510400710080c1640580c5010540b02d50b2070459080301c0d10701c0000c201d9105042c019a400041d0382804000c2d030300303230304003a0074040a0320500c4241030000750000c850001502450004241c0d07140c115030990703001c1e00000d10016080d00650092120a81c0000d0b59121855150411545490300508110b95612156010341c40f102d003014244010700b140340d401500345c2402521607084664420043c0042e6100036101080040c0103480014190100500a00d001d0072020800d004032580d40e450315152a1182050000029561907100c0108203a04094400502050380c81d0509201c8a444e04001401c490480c040c1604001031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 484512517 1250 484511267 484511281
    0xc0606031118040b072d0f0806030318100315081605041a010e04020c150a05010608010b03041b03020d08030609070905130504020307031e060c0503010b0403030c0c051c02031002030606030609 84
    0x2480034030001600941b8040000200002043c400c0c08240060102d008003011426904000c412110301c4c0700550812000e040c289414008503205203030009040568407200290700c14070039162100100104001403201d4050a51801d0300314225901440c8a02d00e8440308220000d407001180c07048140c2400c080300000c00080110313010b88908003100c1d030b89018920440701040e03480084d80b80035420040d001c0000c1d0f83c981d402500e0302070f828001d10810322030500010740020883d0700703982c5c1c0103240307003002044203513a80e408a82d00c0c1d0490030b42103400003004420070140f410000900c96214001c1c0c034119110916140100321101c03d110350400740681c40d080003a0540d10200482001035074040079003c11140d030b8004105000e80209c204882c01810182501000e074800d070b040e03d060351002100d0303a250a14695040e6091020b1100c1160094020180000c443e51010440c41d6030000c54904403511a1142c4101401c2100b84c400d1880203078814001e100d107584581e020b40740d2107030082d941c050150326440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 484513767 1250 484512517 484512557
    0x717040602030406110d02040303020c0f22150b071202010c051605192904030206060904050f0601060e0a0b040b030f090703060c120507020f1005070c0606031118040b07 74
    0x710300744442c04001b68654114900fa4010811240039609482144500c101048105850001030a0380518200c9130b03106a1603100922040c00c1414070b4001076044558143d404041c403080d844449111004154501405101203941c1c043d04068402003001008840c0b001c0c00a0089241e03650300f170040c0782d5072007080000c100901c03004803007490000d00d41d4044602c1c020450070034070801d0300301c02003280d543c036010100c0c41030469010382d9054001c0c0c010351781c8150501141e0b4600501c03e5030796110b00040d00e200d014050200601800080d601d0801d206115414003203240015800f41d180058200001c002c0c8034a03040503030b038009044082c1107582d0344035036052502e42a41074001401d00c42c5401d0040b0b002640040d500404010000c4050100ea43d4a45040c0d03182d990701048080190044846801c05c4102c560066600c105941403806a000c055120003007100d005070000c0300c24218403950401e481ca040720083c7c0c4502e200c11000c2280d45010703502e038411840d0141c030540500a040011011241c004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 484515017 1250 484513767 484513781
    0x91506010c0b040b0106170906070f26010501022116061e09020f09070e0427030309050c040624030f020c0109020901060f0e150c060106090602060717040602030406 72
    0x403920141c0c02e07080a090100c2c41840c288107000204140c500041d2404078000400391042e4044805003255640703800050317070f0300c3d110340551208000c414881194102c2c02040d11301610b0316012140f028a6040000280c0f502221b2054459444100918841030030f40c0c00c011030b007420011207803100c0f109809180c180040d10000d44160000c010594014414802c268000c1d0050742c002c64510044540d10340511900003c281e6600c0000b4400b824407036010b062035044015181110040034150700005114480d200720080350440000307880e12001828808100050520924122400c0241614018030100e00f0071503003440000150014a424a449000360300806072070800c00029540c0350b00d203948a40c02001041e4007280304003186000450340c1b51060002880110349520f540c0390810300001007110b2007412219400145c002001214881101401010300a01d100e0303d54020b25414000c000c1d0410000070404d03000c1121a041034805040b00011140e04150081c8005030f50345c03250709056002d00340b8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 484516267 1250 484515017 484515023
    0x206041511010c0806010f03020714060c0d050109050c07030c060b030709021c140c0d2304050712080711061605070807090501030b041e15060303110303091506010c 72
    0x4010080c26416003004221511020000c000c02c4103144070030007680c40b6071043d650a0f000580b00025003920724080d600508186000d001b280006442960425223005421541040c0d80a004200c41c541e00d803c50007601d015004059090101d4940154550128024040043d0400c034404180205100c0c640d4000c503000c42014042c0c0318402c0d21401e07600040c1d07000e50200c2c1c40c0405102000460ba211610441c0340c422441031841441ea10b1340c5000990780e820500c0b52607051540e8844603244108182c0e0400081e08680d40034405900c0c0c181080e03420311041c1d9208088810b124923900c4002341a03e0201c6500c640c0c0120440d40141e03002000c034003e40139904038005c40c140d9060644060080008115040343d03014412285426101c4004c40f0130b440c42884010490101400400c0001c2c100c5d881c031100b0200358001007902d0681079126a210145190046080d1a42c2c411040c428103a200381c1c05d1507081081001075207181401c4500c079075a020f6404491320070b80c20500c003152503a03218014903114560 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 484517517 1250 484516267 484516289
    0x30b0603010e04060c17010e0412031b0e03150f0a0516020c0402032d090f0a0f0b041e0b06100e1807110d1106070207080a08070c0b1c1104080a020607020604 69
    0x2e1200c100c00000c413000c0d80d0a80340b007200d04504000c00d620038001e0301d800391003040b0700d441c0e4044403380a40c0c07202c01036048503a060144664940b40b05282e000d00c0c502c03822249402c580c440c01c4c03194400003114000b601c0901b084101105e06181c5d26000140050140d03026503006990390307a650880100f031101c005501c81c5040868042c10100c0706d002c40064000c0c09044240c820607858605a43e030303110140d107001001c1b41d080100b18004904600f0074141c0c09401501e41c2c0f09480200c1c8059400c0b850310b8201298902c041c0400d000081c1818004400f0524940c1454261000c4030701c005100120261905e42d020456440000c04045c0305000c00e8800d10340000403907851524a03080a040d03030b01188034030180c40c0302d228000351000d840000c4070b10440d011900508203100382500c50840c0c0e46d00100d02901c00c08864800021103540c11801802415425200c1e00c0781610824500d0b0161fa15106194003030420174002031000e030101003940b4211590485040c3d68072587c0d480410b00c18003aa9001041d082 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 484518767 1250 484517517 484517519
    0xa08040603020712020f25150c050706080f0a021303061104140d030c080309030412032c0a05040e0a020307030308092b030f1806020a030b0603010e04060c1701 70
    0x690140c029012a1307100c0d03226103e40040c95402265140c04464102200b85d0000e6a00f5181e61703445510280a2106070441c800380c1c0d0388030101a600c006d80c7d03000102c00510011025400d203c800c3c0306d214080c0c4002c1c41e1002a5080032200300781d02500c00780048803680c2e40040c000d43d14611a2411a00541c0e004405201d0f074002c00c40080080d0b0864401c0c0ca52500c883c108000b02e0389440114405440c0d4907172569482d59085883c1c44c45507070401040101ca80c40100310200d80742c1100425010450b21a656040307200c0c140c020801d030203440003848441c80082c5040c041c0000d82c2e130f00c01d002050710800e0f17900003210540c001045160884d03c441c0690036004a10000c401d0552040219204038045401c41c1d40715030f145150030b42065030103a4907680050982950841e0980f1030f400401c4410b0348180d010030445480c56080c036148640035411a61580c2c005020800e05c0d415015101d021881121440d0030b56240c031641e4646040c00401c01801c15a4810b40d4001e12030240260705c01180c4012110301042d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 484520017 1250 484518767 484518779
    0x6090d12030e0706050319090f05060a090c0b09100521090a121b030f05040801020c07050a06030606140d020c0d0228050d0806270a0b0604030c060503090a0804 70
    0x2040e034042d071000c40340250369020603544c2c014000c6902030703451084040748800b0030f510a007005100c610b1045035007000c00c818400c086a02000304600801c66440c00066000c2907140c034004030740c15984002c0300e843e01441070320700701d80d0b820941c003a11a8081c1005c5950300c10b000d48080c0c02300c94884044070070000c0c080612210344800101246514400c4d24a003001d1428600c0594001c450202814a00b1340d0342d4900b0800644900d048020400e0300b81440ba007084e40740c149e241e007a0380001c5034204442c0d0112900300503d24118010074001c0c90641000c200035814140010981e110040d0401c1502e00b0000780a007440d2056411100f51a40d0307081030f900e80301c00c3c10000a450b045420403107198044101680204201e10f02c41c1c1d925443e6001e002446c4203140c0d00320079241104000c00a07940302150480e9248030341d070a41401050b4410388100d02c002c3d442c108840200311550001614001c00042c0702c00d00005c0d035151070540594007036042c808c0d1640d0326156414944400321034014541d81c0f0200f000960 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 484521267 1250 484520017 484520021
    0x610020c0d0602041e030f060e190f030f080105063702030301060f090e060103180b0a1d010603050d05030c09100309020f0d03050301060c1406010e060306010e060f06090d1203 77
    0x60350301c4c2041041c10090705c6481c0321a802e005000241c010b102184009000135002c0c1d01c560000f615030b100303030303180c9442400b401c800003d07007880141c9032059807121032400c156006000e0038051455041607a583c0d4109008240f0030f01034480524112030190444034a8031915013104070000c45403201b817001802c40d40b20000c1d100e80081c425080440e0301c40018502850050005d90203540c0c082d95164200d0351140f00440162900450303840580b00301064503004950305030f0046d48140307003000c404a98140d40083c0600c1070080c801309112140d25150041c00090030100e101e485a00d1a49041512503c6030300d00c0d5005441000d000a501aa0030702003041255050f8201502e4903008552808640c1420300030b0110400440c0c2000340010010401440454020444442e80f140902c0152001d542005c940c145410003c0e013103450200000c0007046400e240c100185809003070007000d1a0424184000800c0f1001842070700548a554003040020f4140c880b250041211504010143c00d218030800010300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 484522517 1250 484521267 484521269
    0x61014010f09180213060309050d030507050d1109030c04050f01060f02031b07050f030d090b161b05040b0d0f33050a0e0d120504060b1002010b13140610020c0d060204 73
    0x5c660340304903000040d424041d00c82d440255401c0b801070070104c014107000300c008100c0207162a05015060100c0c1d89800407034861241c0107002003040c90b0340c1e0300c0030718100341c509000441068451401c0c5010032845454903d0079904454450a0441c1c00d180155816030840c010902020952900207071040d046610000781c6008a400540f684001e941e030380424591620640700380c1c00c1c08241740d014104614000c00008143c0c0050740d00c00300c200c7d00c50595500300c1c0380700511140390070704240c5907042c0b0135882e062150781c8800000710b8440845040568942c510369096910107002d210308100342d40480d40c2c107000b06039027525510032044002640608803a00909040d680001b0241c0b40c2000c4030103000000810180300c0c02680c98980f50400043c0700d10f4041c00c40200100d40298507840071038003644030301c41c0022800040360000700350003510105100081200c1c2c65481280e90400d1030074445190752014564100ba0244d03400e044030500c0b44420f078a030982c007003207068124034a083c0400900920341c0c0948 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 484523767 1250 484522517 484522537
    0x602030a060b04240e100201090b0709030b04060506060f0d051602030309120c16080a030815210c19030b090706080705070501060810020408061014010f091802 70
    0x700302600c40001903054000c90003600680e10052000003040000c690081414465a1500c2d8000796032400104035400e600c1a8400c0140c1c0d1550002c00c2044440c00c91285d010515141071201c2e035241d510703170a03407440015101a10b0715548001049858840500312038100c90000e0999545507092540f1800401044801340c02c8148603805d0103107403e10101c00c480c0907441000081500213407503607401c030f01c991021034060202d03c221030041e8840c0f03c5000c100f50080440402070110700080341406040ca60000300306240a0f803201250f8000c41e614101c604410380740150b00417040c0b4400d480114580b0300c4d400b919a070f0046622602d48034403c407820769442901e2003403401d400c079a1a458000c0f41d07128a14040c002c0400e0400000a5280d4400c0b000f03060400d0184001140d0640d40301c50302070504010441e01015140c00103414801c4c00390401555804c42562404100c9103490183d2176001c0c002c03401444c1c5d0412103051859100180300b0a9500e014280b41c1c1e8072a0100c00e0001256002907200d000741c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 484525017 1250 484523767 484523771
    0x504031a0601140337180b0117030702030a0305090a212a2705040b04080c160605040911090d0221030c03030709060206090303040803100e04052512080a020c09040602030a 75
    0x1c446d481900c902494490342c080d0f40700e603003642000c140007030f80c090145e442a4548000d010400150303408102d14102540241c0707c0075500d4034120240403035004c0a4204030303180341c0f0b420410920018032140f010400c1da00812500c80e03440615201c0f4640050b091507440150b010841c0100ba1504100c0018400802c421000b200129150000c00b083d603070100c0e0302614000e01000040c010940b000e000f482941900300035500c0301c40440d541ea0ba56002990446400214042010710000c43c0d41d11441c41c0704e00007602003500b400c00c45000501c000803940002800f40989407400610b4448403d4400100c1d0441c2c01a81d8840d0540c01d0700a65940040321203000040c20a440000e10500209402e4018001080654655a030300e880d1054940e0026144129480307109000003170701450360b00d006020300d11510150481a540c20f52565400031100c1d465518200030303003020080001c030b0341c43c0c030352500780d1000141e612400703c1c5000f070b400c0c40c42510406410400b070710108020000703a07500843c0f14000d69a41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 484526267 1250 484525017 484525031
    0xa290901120c120f2c030c1501030b0a1a040c050c0304031a0f01060807051303020918011a1e0a05150c010f0513020904210504031a0601140337 63
    0x80c9400d039175801c04400907803051242c4242404155101c03680d0301540c0c150407603240510f5140f1142c40c0210b0810301468000e11080140200310745e0002440e00710035000414803506083d090f005404004502d41984590780d90fa101c00091402102590049503480082d00e481c0c982d20b08001c0e0b501c499400d80254080101d20010780002c070f441e0201e5040c3c6400f540c0c3c1612a40d103546082c0c1d0a68000c096101414803600070001c0140d40d440c245511440d0300610000d90410580c44079800c1d602c2c041c03491210702000000b03080158541c0c100071181030f80080c0c0c007a1111007841c8081040e0910a4002c00c0e04440b2030080461410301e00401007107013064141c001c200da03054404d000fa04603031050369401401c01546d1600c0c409460a48409500326002c0d150300c0c0740e03c0044078603000c03845100d1502e010119201241c1001406010307401d0a200c9200450398840d00e01d40200000c1c8851901c85001d41144001300106202d00010348411400b6014010f00f00c200d46003001c0d5a500003014510052111414214 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 484527517 1250 484526267 484526291
    0x6130608031c021926070e030f15130627140105040302032b0606120b0301090c090207080c030301060c020913020f1005070218060a290901120c12 64
    0x42290510b581d1003180045681c000da0040300c5c2a0700c06a02554060840071031101048002c440c42401103c01e41c81d41e4018440e03140905051050102c01000c407600003004400c1c51725061424268042c40d1640302c0a011610307840c00d440244684030301d0460403600000c1c0320482d1401d04d9a1005a180210303103034080c1051010102e4240c3d0402c17100100140c006000a00400c541080107018a004980c14090300116100170041111400d602c40800604140800c030854903544c800c1e8207a24800360024085c800c03a41d1a0190340d54154400c1009060f4001400d105000d450000e80e044901c2d18030540c1d580e0f59548900406050002509074480c4603070300c002c10310008060071039840b41d070350103000b40e805142d4030000c001010400780051000d0100400070307500165a03078500040c1d800a01945507e803070420701c090041071501600310303248201d4101581100041c841d0141140d8010042025070f0351030441004030340c1c100c010340c039401d880c40c00c01c500c00300043d40104c034500c2021010442000b581d61040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 484528767 1250 484527517 484527521
    0xe0f0705150406021002030a0b03010f051801060605030c090a0302030d02030d0f0501080a060e0322090c030216060213120b0403020f07060c020105091503041a0a1e0506130608031c 79
    0xc41140301603402071034545c405e000c5503000707558008610080016804400004a403c0d01c021800304403459030340308100b20101724605100031400d081c4500820984d070030003a001d0224400501414003480010901e6241c990300c0050880155902809803a962200c00e900079699411101b02c41044509000080b01c0101e4030303210705e40c106e50b1828010f14200c080c5440c1c6034018440310300002c2c082e000c10051081c000e0002d00d031440c44404800e54030320307506150404090071110142601d00c20580104810b012001820782c41d8018140c01841c011398aa200400d007065102c0c1e00c2e4440c0d05034011500740b0300f09000142141c0380c0300700d0184d000d9480c2620b91084090f11240c49018031404241e80b0032500016502c1140034011000000d440c100c480d00e00c0c9030b03100c006902700302c504681c3c0e440d1807003902e002d800c4084400c0f50010b04a010074425107800b190103030b0002c0c08203505244019a100c00103100380da58812000d070002144482003240342c0c6c40e1210b240d141c4d403040703031140740216940490780e022810078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 484530017 1250 484528767 484528769
    0x60b0303160318031e060e061e0a0e0d1706180a020a0905190602150717040515040507060e090903040303030e03070606060e010806010c0f14010e0f07051504 69
    0x481e0400000d800c140c0d030507160321010004800c4603074440040131000811020f1122a00752501c180d14002c100d41c1e240200030380c0c10300f00d0180783c00e41102c0705202d030142e00700c000500400c8000f01d0900d00c070354590501d20000c0100c5003085a15200b8608021441c9411051000e80001d0b804030b50f10032a80c86c5001c0c44044840448107206030a000000645c2d070300c2007a4003400c5a08043e10741105650750300d10004510b142020007408507883c441c0d1040205640400446ea600307441800d03d180945840701c0054001c0130307680051150000d100700090100720061104010401002d4003d1540342803908081d80e50f0741c200d010780004a41403521201032490001120303841201184000e40c549030542e5800ca008c1d04000c11800c5082c442881050700040e01070141001900709959486803038082c0c4030004100c0c942c0070b0305481c144200d0041c880003069481503036030003542d00929030802c00c881c4449100d0040020f180c00070120300170000b0040104801040c0f8004544045805006c41c8152880c02002c0b03201c0d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 484531267 1250 484530017 484530037
    0x90a0506010e060c012c060f0c04090c03020c030d1b022b02010902061c0506040603210e06040b0d0b09090303130f0b07020d02120a210902180103060b0303 68
    0x500d00b108401d403518074020031324030662100101d00058900c40080183e800700b0390307000c00b107000e003181d42c080520704100c6d440d0701c000b089200c0d818a05200c0e6481050703124600611410503220740c4070300a214000d8045820101800341220b80c0c84e2002c000c444010026003011020300b0080c4407043c2002d03440059000c55050b508214440c500c1140e09607210803001d0a01c1801c10365403911000405030380c0700e4003e0003140810701280540304078080010b0085030001080c60340b0852800f103052010480c01104944406480303c440341c08800c011809890b41c80e1040045a8010b40000c2c0207d00d802801000e0101661001b400380300d00c412010801601010498000c00c45d5442400016050a08141096002401034134405852625030700c80c11020034085844001591103d20742d00819039040021a030b10b143c0c02104c190610001e0a0014400c0c10842021400040251000c917690700c0540d12407584540d0041c030b521b90b00e08850040400f0071f2800d100070740318249400d00c0005503060202c110b60083c16 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 484532374 1107 484531267 484531277
    0xe040c1706030f060f1f060801032405070c0209090c060313170703080105180106050d02180307030b010e0a021306030e031201030302010b0a092901140d0506090a050601 74
    0x3c21009800c01d40300c40c5000407c00282e22074629410f50394409440000078101041980c401c0a103408101c3e00d6a113020240000d10350084480180548246c610410950b2000400b9031a90f61101c240c0b908003104000080c2d106018241d42040540300d4003400940800d5080c0c907400c1c2d034000420850208030400c005000f24175203800c41d0010b50300400b4001c9241d40c144000108180140c6803103c06c1c09401244106104c4d06000d603409221401504544500303a1380c3c00c0c2400303020020310490a50786108800314910b800940229161000c003400c13070502c8640b4080c4124018407004030601031300e01042c400701028054001840703000314001d030300203e6001003a10030442070342940e5211800c400d1516600c2d20180090301c1070840110080c0400c100a902402c0059401d400d094000100880c000a41103040d915a0380c80f840c055070056404000303562722000f684044a1040d074206004c60 = true := by decide +kernel

theorem cover : BRFrame.Cov 484352517 484532374 := by
  have h0 := BRFrame.cov_init 484352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 484352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 484352517 ≤ n) (h2 : n < 484532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
