-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4268
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:03:48.110137+00:00
-- url     : https://prove2.me/submissions/f628d61b-0240-48ee-a32e-1d1560e1f5e9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 767446043 ≤ n < 767625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 767447293 1250 767446043 767446061
    0xd0f080307111c0534061119141312151506030c030603050102030a06030c14060a0c08070c081014010b0a030e0f0105010f15020a2409050f010c03 64
    0x28100100300122030b02050f490360012002409004a142c0381084182541c0c45011081c864400c441c84d01030703410042c00041e210343d003103d43c10300780b48100348503688500903591214070034100900c0c8806150819150359013402120201030741c05102c03003a08110100c7e50f100061000a044294018513424458032016108916840f0750381040ca1010040081d12801c00803904503241c0082d0103a80c8903012409812958400f074081e60020003440403196466122400b141c0c401c0c44003000f041d903604500b991050700c101015a2105060126049003402034010381d40d42c500c583c03402c9281400c0c564540c1c0c2d50740c2c01c0341c2101c4c4142d40152840e0900d1441403180d40e007504a05000c80900358503250000300c151148090750301c00c040d25031656008451040004101c1502c00900900442d81c5034154010485035600c15880002c08882d20401c1a43c0081081c1c0403c5403c019801a00140d01d6413441e0442288061a04c0c415a21110381c2d000c6a400c2c0b000c1d00d640380c0b1301800404c0891490070001d0903608018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 767448543 1250 767447293 767447327
    0x30c0302190606030c0e0603071502030903060108010605040b010f0c030c060b120f060604090c050d30030c0509061602060915030906090609060115031b180b03100e060d0f080307 78
    0x1b018010785540000b52581101d046004c6401146c41580c030403803c5000303019603e0b40501c00c900010a014006411520503a40240c500b0403441d0482c000440360401c81e03540b8600480d08604c0004d011910030300100900361302540001ca01001800302080c080c5001003840303078058002000c0c420300000c1c14000160411411101030101f040070380c40b280b1042500303105003840303151200c0b250410070001000c4540c00c01c401c403070941300509000400000c407590714404c0e03400107480c0840100c009401141a01d690036400b4011a0405907100a00000310702c02850036a4080c0080c89001e4281c0ea401d4545030040342200e0343c4036128240000c00300d00c0c00350b0242c5010103035003000d001c00031408000a001703811110008030854540040440580080171aa40790500640c8101e05240701c0030b40001010700c5c1030b03076201341c09101d5550701c51044083c3d0009035004080c01c030312075208010408c0004c0b1000e81051004052500c4500c00b031380c40015104034640e044803203400100402224a4000030341c480304030514 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 767449793 1250 767448543 767448569
    0x20d030f053607030302151014040203061908031803010903020c0904030513060c0b09060f0606070203190f1202030306130e01090b091f18030c0302190606030c 70
    0x24095640e00301e80c0b4045100c140e4841201d888003841c1c41c00c80303948000b000060550380c80035100d080003520b07001032004205100000c3c0300840c0a01c0d0402c18034200303c0380d00c40e4201c02c2c0e6000c084104406540042c2810750320000001546102c4c0320411000c10007451810700a556800075188040014a0b801c0303c483c0c0702c0e900d003034031030000700350003013407034114200102c0700505141d40e1441c06a81074080d1002c1c1c010042207a1202003080d58200304210b0502c1e008011405060b50341a0100d41e03a20000c4800b02c1001d01410085109070400201400905d8801010b944600c031705450f07610034030344456600b6910214000058020301c401001403040848092010b14a5490428003040403070350002d1001c1c144541d527000c46c10212400b980301034a402d602c000c1c1070426041c001305081d40c400544103d03942148000340d010407012000c1c441e05000071050f4811308003c4d42c0c0740d00c068414802f105030039015401400d200295a124000d11240307403c1c03080000041e00c82c00c40c00c0a0b076066005c2c3d0031101040d920 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 767451043 1250 767449793 767449801
    0x1f0609020708070b040309030c06020a1505041208070203121924061206120506040203240402060d18030c0b01050405040b060d06020910031a1c060e031603020d030f05 73
    0x5201c2180e0285070440b004d80825211468102e8041009a101030214191780c000800c08076404500954860700512500d03100300a510b98901c201c0b01c0c1514003d005040e01c905569000b03028426055000d542d500542e400c19144022041c14400102d606e40110304821900d0200040a8443d074418100d034003814841444044001d010f46039800e01a98041c00800010941c0b0301d01c803604180e02034200004202920b005519009580b1f00b0182c40482c428003801068003040c040d4910780c3c01c40014592045d0b03486490715024000c40303a0094400b8101c071500d902d051000805507940021546203c0e03a140551044141030030947c0000c10f03003119120314200030611003c583d01c2c141461b0419011190007200910b80d2800d04001c0c072400d8800c82d0840700303000d44040d403150168000044945c0c4030340b14001c07402c0140b003084486540380d42d030346907070300c1d91846c8901c00301d040c1e68003001b400c100510489183c40c20207004609008488042100140d0200c07249a0340c2d6030f03160140c51030f240b14598042c4860300b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 767452293 1250 767451043 767451053
    0x91707081b040603020d06020306091f09150306050106050d05010b130314010b1e040509030316050711060d05090c0102060403050a0507081608070203060c03061e010e031f06090207 79
    0x16815441400420307404a08509669642d00003001941d000344140c15400e514a8005c01a400c110f031541e00c1075256400203844d088035000c00720158003012402e40351050818410320000c16850381d0020100681e003030044009200380c4606400307040e1b2070b01c55030b03202c0054090a4081e142d05810032140c28406000410158502e03005040949a00c5210309080c420201c421394010000b08405a07800300c80003400851160501c01041c440740700a480c00c0c810395903040046035682c402998803807440c00340a511200003610543c0a0400e081c850401d1842010181001400310340010849103083d03591603043c8104084204400c4010643c2030001e0000340c501510b000d41a40074071501a821320000103604810002d009048504150b8603052801c032540c907a00f04013009800a80c4106e01034806c502c0807400000c0c092058034400c503c01024401e04410b01c0c83c1010100d030511740402c0c18441921494002981c090100305898140007121401c0c0c4601e00c0901400e650040d0700c10400244100402000301d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 767453543 1250 767452293 767452303
    0xd0c05070303050d0e06192f03060a0f090f06090c140a050d18050705220f0204170c15072003031308010516140d0f020d0c09170708 58
    0x2501810301079103640411400381302074004118003000d00d0055404000da40c0031180c280300c1283e548103400f000307000c20b061448502e810f207051f1109104550000c03400d4007100c1400095a0024002d408a41050398450310707544c0104403034124000c3e46840703416155050115104840c010f1001000c20b0000034056907014203074218200c0d40e40d040d0440041c1d8515003600590458503800070b0340c0340c10003001000001c10040030700c05d01021909401542000161071070000c10304100100112a6a0309100b581c1d001c60005094428295140d26000d0000081e242000d03030042c041c0000b88005041800d5521003081a07500a000c1101c1c00074a062001d1808121085900c40086180c0c05001c000c1d2284100064a10700071000050009000c101012070040e0781074020601400f03c5403100c058101009000391030405012135500d550100920044c543c0004540060000018640d030040c5001c00d44200582522104440034000c0b440d510400c110303850552210074000c01c80345c006001c01a0600c4040d54503a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 767454793 1250 767453543 767453549
    0x109060501033e1e0d360222090b0a1a0409021c2003030f0904020918010f0807050f09060114120103230715051605070806090d0c0507 59
    0x1608810f454501040d1801c030858030400100c4055103400300b13034100101119484821003040e82c1d428442131915a992000c261030035101c0000440560350600c9200c4001c518500350f0a07a880700c288a40241090202007036529030280898001c150382146003800c0020308030107800a80580d03c0c00030204071840d50fa0300c0300e0306040e204450105900146000040e1408103690f80301d200c410340c00030208104183d55209641c08003409255800745038080081540701e018001000d084100208900095840c1c0f03075004144401004260201030700460840340301d400302c260020b50030384407411410b2013200400c202c1ca0000b000101c4002040c0e074108000700385495406007100b414022040c1072080501c24440076240d100e2000014501c903584d60f414503031514566045400420035403c0101030714540702040e0b51040e62996001c503040c48104401c00c892991104c0302c0005a6110140c1c2c80000820502c0128014111000204001c0c100031441c81e0410910911000502903184005800100041841412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 767456043 1250 767454793 767454881
    0x4020a09150306060605030708070905060301092d0b01090b090a090b030f0109061a06120c0f130e07031d0705101b0c0e0603010e03091504080303010906050103 70
    0x284028074294a00c1405800082100e4241000811480d5220300078503c1034842d44c3d00c90110351074840003610300300401d00540b500444101b00620000240d070f00300e20b40d0440b000c1540c0388640c80310209555589000402958180e45644c0c5039000385d0380c810752400241000301c481d1851b041d1910002002d001c1580b0410b6182c617204c034404503c942d400d200c41902c0111100003408881003a1901c40b00818032501032008050443c4012182810008156000d901c41c4040b00718246c0c0b1010482c40c501d4100708003000303540d5410000302d0000300440310900300501c60818041200d00303080340040c081e945036101c507454001c02e04542c052041e2000649204850050352001d0300c0c00480a82203907014100c2e2000381408a40c2c81d80282040600a0804226180010481d540e0744992040600b43c1710f60040c80412903000703010300003052801a10042610060b15041442c00d5500e55480d411a08240d124003120343d61000c0811580d6054015040441002100d105580c010200070144c07a980340941080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 767457293 1250 767456043 767456051
    0xb21090f0f0129030115030303060302090a0c0e010c021c0b1e1b09040f0911040c0f05040e130506161b0206040e070c0203010e07030302010b040204080a1401060b131d04020a09 77
    0xf142c0e0b01c0a501214862040c000f10384130081e00c0b401c0c041c0c054031051004901440d41480020f5030031100c1e11905003101040d542c1d00703801250f031000441310f40d9140081681e00190441c514095080451a0392940360311903140c4600d0340c40c207551550841200c2e00f891102d401da4130742c1008024003511000300341481a41c802a46c4500d0a000841d0041101d080c454015519084403401031241581143c1c1d1104000ca0b020711042c40192022a20f1420f4180c0380070101d9000d002c280442c1c4001c0c0a0f80d40c1c402580603904031022980d80780c01381380032016141141d4186a00c1643e08010350310103e03160300c24400e050030844242103580030a00a1003a031240554403034030140803076011442210082502038005000780400804500e00644409561108070003640ca085914402070405000b502c1c201c8060341c000c0c21b00da442586070b140120717281080e2102a55621640420380f442ea01b4080c002da03960200c0745030221070030104402240024400c0d1100c2c500c03034034820000142e40d51a42c2602342c8040c104081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 767458543 1250 767457293 767457371
    0x100b0a05010804050f0105191505090c0702040207020415060206010b07030903081c0e0309010318051e030c010e0c10051206120a0b010801090201091e0b21090f0f01 72
    0x40c1440ca112170f905130154288020302c44500c015050b4059480b0031003100300645591101c812035000c101c0d22600340c02001d00300000b6441108480a0104a40040e1000d03180010550000d811500c1d41c041a40021060083c1809650b0381001490b014180181200c3d28100607500d02030440500d5100007042c0190000780d10a8102461038101245622a02c042c0044220307841c0180c1c40c0d800410009002925140d072041c5029813102d8070221154100014103500c502d0b61840c04031400c0000113600c0c26100822a02030b118800344120348429907090040d0000c03420b2601042a60068200c202d401c1220a20140030040550010540c000f0303812100002e1704e03402c401301c035800c002c44190094a0314a0072400068140c6041d004000482d00c01d0b0f0f81c0c80f800c20b45906a4942004040b8401916401b68000520890220780010103100c4c107034466003060740c2d000c1a588a01d61404590803401500159141038140904005100300c03494100c0c02801140c906c0c805018654a544190140c9120802800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 767459793 1250 767458543 767458553
    0x70b090d0230192a06020c0a170307080a0908180102070b07200406080d0e1507050c1008061c0c03050d090623040902090f061b100b0a05010804 63
    0x50000d02c01d07801c40e9141c403001d0303140e8000888643e600c0c002003901a00c11540054400c210030007401e84410b00b0201c038101c01d0310f51382c009401490400c601803141c0071100d80411003130900100b00ca52050a015520f1400034001000400058810711805003003402d1900040d11a07016035035000300c0b041c82d4810944456004030b1400705a070380105602c010001d040001e11162034a1844c1013001400941001440d0382c2c10b2000b1117070b031032140110a81141c2803120f400c0b0300c500e10000070003000900100031000d002c02440c02c103901c185000c840a51060a17004802d040c18a5104054041400d2407402443c00101103003401d02d80b4100040d5080342d1001c000c003040716848502001d0b40d00328084469007008000068507e0b03400b130090001013034003142c6400a4031003100b03c808058110304043c03418a450300d0250300107900400386a40d48480001600041030300c4401c0501420411402400342d40c4a42a15150800f01d00c1e1101c484a13605044001c80c441d16407044c0201100c0083c81d104619590364140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 767461043 1250 767459793 767459863
    0x1a0d060e07050414100212030a020d1d06151c02010314040b01170f0c060705150903090a090b0901120c0306140604110a020d110f070b070b090d02 64
    0x20200410006001c212a404000741042d0b500c0b10700d0010050390054100100049103030341000059211407500301c1d101c132449020b141c00c0f8441400144c00c0411200b0150f060711032010a100800c2855145481c2001c3e0412510380c000c0654096681180c18240100745813600014249030b080b0640100c41c1c086900c01d0b40808030b070f0341130b0001c000254141842e09403c882028030420055041c0d14007405c402d40404036284030020104002407503032200c1c030400d111103a00402801c2d0307854040c050031300049038001c1d540181316901c024040d40da540c1804d07003040101d0000307812884000d89071030310a0300c068440113107250549907a41140c0b0341c00000c80c580504620240d400081031b550422220340200c0b0008440c0034000d51003146c00380820083c02d400318400c9c0c001e00100710b005a001403404021140910340034204c0145203019902c950f201c01020904c2c040745540450448400024100c0030f000380c010300990011440b10140024031074080c0c0c002d41c0c9800056002c0019113100420322019400c07201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 767462293 1250 767461043 767461049
    0x80f0405040501170c030f1504140f010e0f0d2a12020102431415010305070e040b151807030c0e040b03120d020f040f090b03071a0d06 59
    0x400d0001d5a12851691326074001c0d100301414520892020044601d00070542410510740900100694176506083ca11515000f41040e11482101200d451044100f4884448003580130800415103011002d001e40c50503040c018942d240c1d4100c0410600b00c40d5211400340c0899a030f00d6000c00e02c2a0b58406c01181c40001700340c00400b42c03a854100319440c02e8041d00904203491801803400080b10134101a842010b482d400c2150b020b55400b03c14445e40310940244000700c90142c01e404000703030070340e9070143e1030600000442000006001c0040040003410006130015104100d500800b0782815620240c2e000405440c00344040c080620101c640c0d00c0752400b0841c82c0000d424004400d040c8403c015000b0030984443e0b40004850b0521001c55050a0281070034a07940500100002c0040c0d0307035030468940042c051041c1d4541c08008c0b591410910700003410142208100144d0761500e07100c010b60440d048100707024081c0c0c101480420840500f070054032040f2580800c010b50300c020b1140640024405d0b50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 767463543 1250 767462293 767462299
    0x715090b033705060f18041a10030b060607033f090308060906010207090915050709050102060106031503020609010e0910080d0504051302070c0e01090906050f13080f0405 75
    0x510030a0900390944090000b480c0c1c03080146481e0041070114660140140d179411407103400070000b00d00031b80c0742d205502500400c21000192418813010758010300a0b9440340d10406440021b1003485207220b86030343c0252089510500e4940c1681d805000d11448060099055249500c001300040700401e11100102d09070880c180328641098815004007003180f82a0300081c680400240242003d8040c1e600502c0305800808038580340a4800e00580141e040407990b03c41007000c214481442c0340100c07409000e9503203d11902504060009141520507804036040508066000200400c649108002d0360380644e48290f80e01010300058a400786408071140e005580ea4003000841c0800302072030415640e4070820f0f54590709201c10f00b01c600340a18001c1c03a600410307201407035900d07070050b500904171580704214601c0ca50740c0d150b604c603400002c00d07480800c40700c0c0c44105d44401c000740340c0301d415840781640d070f101d40e800d09000c0094a2100b400f01c000610313035600003803661202c0000c0016140104001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 767464793 1250 767463543 767463601
    0x60b0f030a02101b300201091505070513080f0d090311090a061805010503070f05060f0d090b161e0806120f01020a0e040b030a08031909080f0c0715090b03 68
    0x112826051021891250a03a52405d038208869041d1041c0568040140c0209450940c08400c52841c002000301508a005101003044121090101c01d805400100011000f4120741940c0720720709800d1441c071610b00030400c1a000b8007440012490b0590603181c03c03040d0381d43d00280c0d0f102c5100c000180592b4110b490280750030100c01403a040350b0b07041a816190280c083d030305c9403030b0b0f200c11130780c4482c1c03007030045d00e5000b07000340314041d032052410b00500721020f0521008202094141c54042403142c0980d00e400e0000c049500310403c464125100010482d80d214541d10135040d02c91000300076107400b600d100c1c40b131603258081f0f400049040100c5040441003000031035a0b6400803c1c040c00c0b0712600c4003071078026803c081c04150342d483d0208603e010309401405591071903850140c0206603c80c5104880440c540d202540301c00310311040003811801200c100e07110741d101c3c074440740c2d02c0c82d00c40198048020014001d2141d0303011f0740d0244000c42201c0314025069100d85518003850503090024140c2c1d0030940e80c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 767466043 1250 767464793 767464823
    0x702060f0403050c0a0801051512101b03060e010b07080711030607022103010521010207050102030705030108061b0d0b0a050d03050415020d0504060822060b0f030a02101b 75
    0x80401c020181050484e110360031704d07946202040c02e955048808442c0b02180e44255017844c24244869040800d14105032410142c1c2e6504480c112202c0c00101180300000e2a2202c0505030503218800252900101440c015890021080028418020014002e160100c1c2500c00c002d6100c0800440d01c8004094821a1a048100950b241007449641050300245103c0d1009003a042d02224162140504007180302880a504e8201030321920048000c0740d90308000c2d140100c0c10038806940106000d590b029929454056058509240a00710400c04614010211002400d24040305c0703010f0540032010803c002c034400000c031030b980f40341c0c040da40200d100200502090f07840001081910096075246c00c0b9201540310499841c0c00140a8001040003000309000403401003410581c0702d2550700b02441d521403900200307105928500d00488840c1c0e10384184089918124000410000d0180c00601410b01603400040310030354000311441c1807062102c40001c032450940205c031a102d80018034080c2c440c075 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 767467293 1250 767466043 767466053
    0x6020102220807380714031804050604020d06030807031710060507060204170d1214010909020604030b0702032502221803020c0907080c070303020702060f0403 70
    0xc050039208441a814801c8100d104168891a1064400300401808098100120898003107104004075058090794590003100021848101d041d41900501c210f85441c9686021403c6460302480c1d120a13400500c031840310b41610034144000f242c0c00b11400300e4580c83c0c0c2c901080091007101a6100350701d00f0306201006009040c80206020b510940d074400e95500344c2a01e4041103030050f948000c40104880e42000524461005005140d0150300b005280c03079614424605107104e20040914650001e200110700b1a401c402c040e8001d9403c1038040c01200c101041082040005014280909982e1541801075403503903c01c0da0080c5038805464030090070990806541d0f40c0040c10131a0382003021001d544218842100d040c0384117980900065685100700c00c0f403621481c80d6003208a4803580c2c0307021000b848051845803c0426029401404141c1d290320309114903c00020129414440303034409105a1408200032548510380501c1c00588915403840011658810010010b441000102d00841404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 767468543 1250 767467293 767467297
    0x908031206130f092010050304020301060e04030e01030e010209150c01060e040b0108071508040602070303090b2809021c0809190e0702011b0f020a12200a020a120f0b0106020102 78
    0xa0081203201141c10414498521003206044141d0700b1048600d0284082d1f402100a0761308144024000700d00b140d21140c0101c1410380485066000454203503240440d540c0602c501c590000c11900207502d00440344010a071403000350800700c4e00342d102c00035004807091000c1d1302c000e0140008101081c00c5003082c2c1084501180d080c042c01505004030b2400003003140040d001e1064084580c0c5641a182d9183c3d1200402500814415000d25407030351a582c3c0010000c130700d1709116400120101920b2105504400400c660030b100c010f44480c034203100c0d1400350355240c224038410310b481244082143c1136803800841b035018030444103420404421100901c2c060200180c011b44042080b600c03110340d0740800480c01e0742c60011a0004400740300035443c800c1481041554520300e481d00440d9030039040340d03448000300300c10030b021240082c0000032070001000d09005d4422004031800300400144441c0d80000744010a240710310250480030002d01c2040056107014000982d4000300c584071a507a4070f4202a02035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 767469793 1250 767468543 767468561
    0x190c03090603050106120e1912114c0b1c020d1106092701120b0f13060f0f110723011b1e0908031206130f 47
    0x464280140031a01a2082c03088074100d8259a644896075043c086410b0f0003488803101a142c1f50241100500c3c1c80010303e05551101c0c1d1081000c54580b0030000001003184920148000058000c0f68122802d005240c0c03030101c045580e00142d02c1c049512070b100701c3e0030541e03000c124040400b406044d4082c221080d0700010040c1001d4a5141c0b00d0b24280c116001d8003203c050000750b002030401000e030082000e00324826041c1101810242c604884140003680c45642c4000c0d000c001a01d400c40281c0007140701c017005005101181980c0407160140e034510803403100c02030410360300031100130000350500d101c000c1c4605502c1d0880401c2114041c20100000580b0011410400e01e60034564104002d2081000300e43c0c00c2a0040c500109600300511981c42ca05405441c01c1e840b50740703034400c03211042d800e1003e00d0b540d155640c90b0484c80700c0710705180d04600303c1d01481d1740c01800b241c81e100300b010380d001208071010b8100c02c1401018650300d4100280c009424000a420b10b98540480454145c5e00c40d03210b2424 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 767471043 1250 767469793 767469797
    0xf0301060e1305430f27110f181215070f020c06070206090406150305010803030c031302030a0b0115110f030406210c0e040e06041e0602190c03 63
    0x41c00c240c1c09410b0804d4162040108424040c0002c3d49120032a50301696400c203040c60f0403d10900d5403440504150b0055070002d241c20130100e108450902412800000b40d00d0100c1c2c0e05000d64042141c0c503402d240240000a42486030020ba000400c02d0110007440181000520f140c0603c40080c40c402d41d203590150700d02c040044031401043c0301c68010000d6001d8000140d005100700401001800000e4002100482c0c201a041c41035030f82580d202e004940152088004021600c0b440080040c2030310410b0b405640542c10070014440140b04501c2107a512200c080c810390a14106440842c1c5044900403001c0c2c90000007200100782c10300c50300540711030101141d84680480f811860010b40350a4944a40451640200f00c00c01646006d0b4200c42021100c14103d6517511035510310030000d072480c00740040001001140d1481a40c58240f10b00301a0013291401003003940b40c150344680351025500b9040d8100b0010b03608401c204001038040303a9402e010030521220407030079548040c000310020441200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 767472293 1250 767471043 767471053
    0x2040e0402040e1f020c0f0607020109030f0503130605040f06090803010801061409011a0d020a09181a010e031002042c0c0a03020901090522060f03020901050f0301060e1305 76
    0x9071100b00081031241442d43c504000d000d044d20040c280d00a60240380d4905140c080d100015105407824841940300c2d13465a000414440300c0d40c9001071583c2d06080860040c840240140315442c18007aa50420041e800400068680c0300c40c140b00190700c82012000b8441d908124004040008240c00343d812180c0e0503000b80020b50b1640030403540d13542041c0301d0680144081c80100614503c5d0110301c1c0769510716103401d03440c2c668141c0c0e13200c050340d10041d4800007090442800300b000d80c15452290050074180d000c10894070301d10030f0783d8091080522883d2810800c031100380300744aa406021040c3c0080441000311342d12503541c201c485465076a45c0c111803120845501c1805207925440342d4600c503a1100310114600501404194000d420200340c00c3d04100551001047c2a1102241d14040d00104810608650403503c000c2054030f206811054912054810810050326081035050540300100c0d5002404020080401d0040481354040d518100740d2078103210200c02e61480d046005409241950 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 767473543 1250 767472293 767472311
    0x9111c020a0f0506070209041406070903050c1c1203110d051608040507060f051306080a06050f01050d020d110423011e05030613061e050d0206030f0c0d02040e040204 73
    0x40d0400c0c540d100343e503005801000090300602c2e2904e2000d41c0944522549600006034404c8240350541c100c40e01320216a0440f001e10603c08200b0070701ca845001198440c10380f10060924100c11420508020608980d01032007180090098102e40511850303031310904e4649804c1c09010740a0101a1010204400ea02a620a5407441400120310a541140c000c284003817400508035090b180ca4582e000070024140030201d24118507803040310060080d0360703a45c01c050410b00301c41d0003203450341d0780583d1003414440b60502c0141d0308030040d206000748040740161a02c1c0440610000b030895014102d00c3c1d50000100811020f5007400c0c1c900c44900c0502070404139180e00801134840144244450712100d00e1404941c0170284030700d0003564804d41c042c00b080038488910031044261032480d0030041440c03c4a07180b41f03006107502000d400c024581191110704040e02a00401d4042c480076013042040388021b800070b09202076210840f040508a0304d402c40d903443e039416040081000c1901c040b48554140300000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 767474793 1250 767473543 767473559
    0x18020d080d0b063103020904120903060203040b070e030c240702120a051203060f0904030e03060103030807111b0d050a140c010e0316170a05061e1f060309111c020a 72
    0x541b54080c08000c86a103a46e16951144c2d09448900c1d8104015030300c0c0880005c440e4005180130702c0c0304401c00d61701810101e0020b41a1a032400c0101c1c000d500404030141c1c203030389010800c29016000c4181985082d00071071104068403e44101030f410a401100603503280d440052180c240754055000e070f84000381504018851440140c3d81d841e030101503108000020b140441000340c004d4840c0c10446080c6024002290030700300709a0080d0045240e00040150f0190080c406500008041005d0034400c0c0e02c0b21009240908201c000500400e05818090704100c400c1100d80030464201402c0200014281e030a940d03504e881003030f07050004041c000003d9090600044040c43c43e81902c00c80c414175420030500707400407818403180c051284200c03228000400c078107000c1a40280f003a007d01522548035199410500400139200716600300000a45195000d1b02810007400c1e1744940c500821561041d00f4849450034000c4003950b0301c107200311103202d08400f50110b202e48291007034622a00d0140e584c020b0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 767476043 1250 767474793 767474887
    0x1205070311030c030a05010b03073e07030c06020307051c0c050a06020a0f0504050f040f0f060f0e13050703081303060c0e03150603071e12031218020d080d0b06 70
    0x515404108101000c68585c00078003045000700f801e60111800d107860801288bc0100c0c61442c041d2000d4000c1041401407044480c8620050500c9000561601d0402c0e503440390b83e080f9000043d010618640c18590340e0b244194940c019031900a800ca83c8190054200b0000a44c07200c03440c503000c11a103107002c0440b580108240d90131200010320035039404144000348005000b5041640701d08660fa000001101c81541c40b4040c043d00e08991035866542c01c03c01c1c0603114190107405005901310100b10000000c100040803019241c1c400102c0340c4501442d10340310600c072071640005140034100040000e24560017001c5000d10401101100c0310001034035940500d0300025500c440d05a0403100d0148045000329080701400101445070b408210307982c10400401d26213403a0214009603440c15a16001c080901a800207410746440084410f1042e60000e54031007c0c0e12001420814049803110404016500280061034090f00c4140e032000f070802d0b2510000c07003260310412540c03100107000301e0142c0324a107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 767477293 1250 767476043 767476051
    0x150f010f03022805060a09180908070215070807061b23090f131d03090d111201090c170f031614120315010f1205070311030c030a05010b03 61
    0x10b40041c03400202e580d160040d1150f81400348030350320000240c1d64541a00800400340710759160b041d03103400d0500c2c1325909019551100f0b00c45050000c46000701703690008940c200341d4100d130000084034422800ca071041c040e11001602c0c01801040d5101404801c0e041004200c03003920310161011012801a540d07419100c0942854a104420031000000050003c0c400120000c243d903460b40c03040c00000b10340e98004101c0c01a455101c1c54081104032041c20b0001e007200186020750f00b042d940c440410f0004100e090301038100c03881d01720384503416203441e094020b00e1180c1000034070001e20306007005400944903210740b03600141c0101c0d01e110003c9012914000362024800a1071070300101e02e5444003060b0202b401500d40c0804840108203004082003a0701125000c5101161203162031107040030109030040201d1b050102c0400545240c5501c02c540308031203201888001515100e8080c200e0052003404011160040000b00f800f070740c0b41519010710310031f403070403002400642e890700134180d0140816a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 767478543 1250 767477293 767477299
    0xb031f0f240e060303130b09030106080d05030c070303060e07020d020f0d090b09120d0e01020d050306060319110715050601020c06191b06090308013203010b03150f010f0302 76
    0x807414030460000004094120354010105c906000340c004040d00b42c5902c913404680d45560004040c0c503142002e00801c8002c1841c413002e092000b01e40c110144c840c0c40014082c0c1071852001400c1c82c10180241d000300041d06001a00e0710707a91400c8a406551307081052800c001600ca4011a00e2100000082d0441d407000282e4407450420720b000030303c14503600240f440c0b43c0e201e07206c0c0080c154080341c100b01d00d035041c08450b60380c603001040c8803001908002e00282aa000c00c0304c20410086140c450000301c9400c10001111b00c01c029076828103030f8006101504005680c0600028400e00780204410f0600ca03080b01400100201c0e19980016a074404100e900950410030034008191407202012a5801e1003540d81055010003281c29804000d50006880c00c444444d52120300708249075020307890398007500011600c221226a480c0c0a021031003080c21080045078031030000c0c800d80f40c03829000030a0b400c0b800f50891700c2103c2d00c52202a1103034011103500960240201c000503004001600c0030040700c0e009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 767479793 1250 767478543 767478611
    0x3050327031504050f01090b0708100f05090403120c05093f0a06050f010905091b0d0804050406060824010503060108130507030602220b0d0b031f0f 65
    0x1014181840b0000d0091300c05024806042c5060300d401e02500c48460710070805900d6903c0c00c0e82007e072007414042d02680c85241c0210090280d200b0f08205007065842c1151500c580340d40f64a001c9401c07100c454064214203040040c0c1382d0310741e50040082c080140c401c5074181c5015025203404200f107040f83c03a540350007015400390780e407011500da41d4403020001c07003005446600070b941d02d80c6001da42c1e099440c1491140138400412028105106d1560030460007070150074545a2250f115206800c42c42d2141d100d084d180903402c040001c920125402004045d0040c4985640c55601407d101001c5410720400f042100c0c0c0032000454800c0c190280c448142c58be10305548440004503082c0500500404141c6040101c10000c41c0301000100000c2d03110701000769860011155074401240c006501c19000c1c58404424400c84541405494109082c143c0000f400987c6500081c41d056a50b90b2154880c1c0d0501c82080b011039190b004407402100101082c0500d0300e071a40c481c10b0300c1110440100c549805 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 767481043 1250 767479793 767479813
    0x605040f270201050415051902030a0f11011409011a0102070812160807051c02161509050909160605210402120d120b0105070201120f020409060305032703 68
    0x79100212484078010f03d452030800c2c1d2035000c1810081300601d58500400c070042041001c02d410f40c3d00851880b4400c0c800b40d030600c0d4a040026105041c030b5141c01d800e00040c0d208101440c4800d50001888a49032442e003c40f90510740012402072004036402d01207100c403142c0400d815400022a00221078011008141d60350410142c200203400101503121603543d8211000042030451010b8110305009401415580d05003084001918060602c1401550851201c41090000c030038060000c81c0c098400001180141941c2180d4109440d000035620440d00c0060109403800094403c011100e40c1d40084e5040b52500d006440500550007030342c0000a840c0740c0d8100ca82c03107140499810070f2000e015100c00c603140c0c1103203a0502654042e0760000803801d2081d00280081402182c29100c003c0c24034a10b02034560300020b18040b850501902010344a04588c40742c40002d9046800406055101300049500c81c54244d4680c1c0c0320070f007141c015500044111744a601a851784e000ba0520040041c450340031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 767482293 1250 767481043 767481101
    0x1306240c030f080a0605120114010e070504050405040804080d05130b120103020d030c052e0501060503040206160f06020301090e120a120f050c0406081302060a08090307060f0605040f 80
    0x103801010713a50301c59151040040c250b1103d4509281c2d1030000341c008911050341407054181c04e0300513404440440b8980040c00b84054100040310705882c41610041010340c1c1da42041d4815100e283d001c41428071402010742c85487e0f002020308804c4800c0359030350380760965032200c12001d4021292440034072100702004000600c3c10280818440b407103400c04084414498440d981404130078005003251112200f602c9c094016000c11318801402c1d1680300b00000d5042c000000d00e1070100170402806020009000300c0608240b1140d1201e50394044281504516503260840103034000707104e1024010f04001c039842c4800008982c3c40e10a8580a000909083c030300441181c000454411070382c00c02d642d802c20084025598011248600e400301460fa6855103060b00040201e5001820001e03424411110310b80141c1c3c40c00c0459035515486e00c1c20034025124801010b00307601c40c0200042802c0c0c9400408140d0390340c95008201110700031030b405c1040305e82c400410400c0c1c480390182c4503ca00404d03040074120390 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 767483543 1250 767482293 767482307
    0x121020f27070f0306050102150103110303270f03010c140a11030c03120106080c070204021809040b01061124130212030304020a090b100e1306240c030f 67
    0x108018000082080e080c8504115948082d80c0810004540625082403d80c240c001c2000602080c0300074151600d040c284420f00e5941804010001192040c003130381256000c00c02d460014548140c0900b0243c00c4038581d042c44018184410300480390301c6280c08042c60b0611030240c03850b10130b444251320390240403c5414182d010740c0c0b0881c00d03c40300c2d20314410482010009032200b110342c0d800541e0f0701c0079400d42002c14071205034409010081b86800b0042c00c03140c1c1c1001da900942d81500c0258495a480c000c920022084c0450103800c18001c034100014800e088915504840c82034503040061802c881342240c540c3c0c10408103000d407000754071f101c0f002ca48a1100311940040c00d090f00320724188065002902c1d103615007090726400da101106120552410b903641000070000079104000040080f0045143c90060308800014031a11114008244c1c8940003c2058000050f20801030603071901240c1c1d80d038950442540e582224144041841c0e14020700c020051145c0548940e48901d007100e000f15051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 767484793 1250 767483543 767483569
    0x90203010b1b01240513060b040b0706140703290f010c050c0607050a03030f02160206030a0b090c0a080a0c0219080c0303040b0f070e0109150c12080121020f 69
    0xe40d0f0f01c003290040c85113070900381a1082c006460904195203040100702c0c1d00030205041005103841d10a040080141c05400c0f1030899a401c584580c640c155824910000c2210091a001141c80402046171035070b45503000905181821450356581d0516031540524202141440c0d9001015450305107444e601889009546034443c2c411a4011042840400d046401019080320307154030221180d810103406000c3e40c0c1213204503041c21401c1616010487e85201c40020010740070714800004602d00038031980085101359406046c0019a0410502d0700c120355001e0b0011000103482e110110702e03040898094191841915401003005554001108980206c0c1910885241004102c0314040712003d1020b144698040d03e09800a40750440803401c1c02c690040600e02042080301d0007001c16a00000c407a070503904c83d42882c8210360814a400d440f05104904041c00a00b903078001d2000b040c1e4064103c60580e02030200e190501c19411205208083d05c26038000d6204091081e030024508241c1141441 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 767486043 1250 767484793 767484847
    0xe010207080c03090117061804050309100e0f0f0607021516030e01081e04200406090e0c2e0c02091611240703091208010e01090203010b 60
    0x28111450766880d409a000c0c4010070340542002c600d01c009580c005071051130441c0421400246858504000341007100c003d004100c1420126011900380b0504100380c036a03480c00600343e0010584002030182079035803400c1c0040e101d0160303080000320a0411105110b00724401400303143c10542e40b07900f00500045006a003845500c0c080c4180750803080a5a4008003d600076100e5030395114250b0f00040c407100009144403460000c41310b142c00142403814410344d1203500901910110b1944181c5220110314505805511500781031001c100c48100f03030310201005101c1d000301d4000c002040144502400844081940ca000100721564040654190740742072024074946461000202da000035001041a14040c1c3c814603d11003110984d9080280949048840f0006101a400c1c42c040c1c07122410707100c2d50110001c616a400f0031340302c600a40007450041e0b404040d03140400d001260040c00b8007002d104442c80e0300ca8410002801e0380e240e10881e4181ca0300e8024403071510112090081c0c0401e05020803e103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 767487293 1250 767486043 767486047
    0x6090b03210f03070914040209010f0e0f0d03050301080d020c03070e070c020d1401051b070201181a0309190b0609040c0807080d080901022b091725030e01030e0102 72
    0x2502d945003000318440c19107a00c031200c8081c00c0a60211282c00c2c00e4180354040c520400120105a0700046040c0610f041c5280500307031500d12402241c03a81e00c5491807030790401d840c2d03c010402c00d42c0000c0175505840418048840c80c0017681c4089a9507a40c1c01002d5401d40c2154005000d481000341d0115809030b510704100d80703640b02545c042010100640b40649021548452038901d20760300b8042d017508051511200030a0070001e1090040500c00e50f68024180702c42000f08005c0085a0380542d0b009200c04081c02e000020a8084604c0e59441168800d0b500d002d00c01d641c0881c51a101c40724804141c208280064039540e00d000d2201224018000b43c551880301d80300080d22010401c4004058003011028152200301008003500ba024007a109100a0f40103000b004243c41c02e0444400c691101000740784140150f07125101c000f40031458024090001882c08101845d510000420301500e0400c0300740284180d041114004085003c00100094041c0c107844505d90320031303001505a01c0f241d100040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 767488543 1250 767487293 767487307
    0x1303020c03070b0415090e0a02090109050405040507051002030a020714130e03180a1d04021201091a0105061e0d0605030a060f14090d0516021806030106090b0321 71
    0x640742415650101c22003d100190500900030f0070410311441035a242040c0ea41c0c9420118445244034000700000c20840d4046111005a8070030782c0504018900540208041d04041c1081c0b5102c1e203e41c00342074040c0381e1442014580510020071214800d10380ea01074912641003064034056a49000349087c3d210381641c5088043c80c1492003206a18200074000703598605c2840041a10080d000c00198401e01c1c284d441007041524101c62540d40c00ea0b04c0340b400100c0d0740e0b80d100151080102040d1140650300e0a4ad045081049450140c030030b50144820699150713981d80c0030020944601051286031041501a034200031035610041c04001000c00c001140e219198000301c0d292120603a019541d00b611480e288192a05c80e100f02e2a00c0380c3e91005101042c904414a543d40b007001210b084200200001c2d105e4803807106000e120343e0981c9c01000b080d1302d154000c0d03401040507002e84100d44254030317218000688115a10801d10003e0015001d4070a49055001c0c41120804500d9181c0c00810104219 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 767489793 1250 767488543 767488549
    0x703021b1503070215010906030305091014030405010509071410080c0f0a05091e0d1e0b090102093a17040b130b03040f0809040e01061202030f06010308031303020c 72
    0x9140f2400c00390380102100e040000007030300e0042060b80507179101031030082d040c00426400003c80b0100c07035003540c40b1280c413400c1140031109400b84d402c803100300c42c1001c0306000810006402041c01941440100c0e0642d42c1c6440c0d40c202010044200164845204298951014081d078415a4072804040c007060405040c1d07007001140d50320580c100c1c0000380c800291800306d450100d11403440c89040d110600102e030007100106002340d09a2002818a008042c0c1140b2a100710f100d0344d00c000f83e4001e0000b142810301f84106d0b8040c0d00020f03005e6210302c00c60021421170340e043d00d1911604a640c42c0000d4001000d403207001c81c0048109000317039507458898840c409028143c100a01c010141500c51076910510070740c100c800c0164a41006280c410208217000c0842e412440308440c041c0c126924656034815140041d005000d0706a06500c40d50a001000880c2e581c03503140d10410030300a409480b900f2062101440d107c4009020003402c0d1002400418003001042d1041441036100b4011102d414201c0800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 767491043 1250 767489793 767489797
    0x604171e0c0406080a02060403150e0a0803040312090203030f0a0210020c06011a0720060c0109030e0117040b010b130914010617190e16030f0b0c0703021b15 69
    0x808161684031601a00700750034680b18200060403a0409000303007600f15400504035100d284006032002004081d201c249800c168810302c1101c0000003207400e10380315840c00402c00d400c121001d40c08506006070004040100707000710300319154018040d503c4c1c2240078070b4800842c2c000f02c95600842c441c102500740300920501c004c0210119020051009600d04030303400c0204018600711846540081c860350000400e4603980700302850502e59420000954100071400c14005c2d01111069503081c01d8001c001e040c0c008440c3d0051800a98902c02c0c446c12003090301c0d1081409840060040d401030004100301140080079111103200d00c0410004240d85250050545007140c5e41c030b4031141103500040240701d0300180c010303442d0b0030303105242d5001e854040502101c00704004014818107494041c0c10a0540040c06071030203205608002c0f107803131616410003803003001c05408111810404100407680c807064007011b40c2ca85582c5a802803100101d2810510302c00181c404901b03410012a6480c03114800344400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 767492293 1250 767491043 767491093
    0xb18060c0a020301061a03070c1403030f0105090109060317090a08060114190509060f031609021b0606031f02091f03270605090c04050c040609090605060417 69
    0x6040c00c0520b80101401c5440c954401040c50742c502d040d4003200070180b030039654800e00600340085441c6c0e803410b28404685054411040600002003008000808840024140c41e81540e800c1c0503a071722440603104070b03501c1e400054190302003140284c0d0780c1a1800024200c102018180c80c116690390090710345020000c4c0c100905207034076610b442c201414401001151401c448250044607403500c800f00f09121805840203000300018542c00369039171010814807120020060800b10070558850000e0000c1d0085207240c03000d01c855840315411004001440c40c01154010060500d445686020303554040a000032000c08940a0015024641d11b50742c000782585600e210030040000c1001008040311741c0201c071000030340c1d8113003800040220034044d14041194000310003d5a9100d50929070301c1c0034000c50241d617000d0308000c01c000c00380044030040d004440d5961030b10007071292101c3d03e0390f00343c980500815400038020b010404c0340c40c5c0101c80e812181e101a07820f07108003c00650003a0903c0d99025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 767493543 1250 767492293 767492317
    0xd05130f0f03080a0b090c03040f0b01061706121e15040c031a07051803030702040509070e010b031b1602090f0618010e040305070c08030a0201050a14060a0b1806 71
    0x20707402109060300001c100741d02c0f1699031410030228041e4000a030310700300e004d0150001c41c0302c0840000c0c108181c0c036120b8401c07550448010b03c2950380d0303040014966280c0110040014000101042c0503041c071101001c02c04403442c01411401d14075041850046805000b90001ca1152610b030524a5040040e010b0059004070f01c41070199081d0300b41a9800d03501d0001d241c4600c1c240f00100540681e002c0240e0749200c03c011501c1008040b234000007441d40c00745d140060f602a2604c0706000085d00e000400e0300031581800002011a80d850712145941c0c00f040350110410714021620442c2d041c0e07140020030110070045c400c8040c06c84550041144a05d04139040134100b04000244640d510b130050031560901001c0c0c10100480d0f040041d1084c5c00080504018140000498180b0405c5079010981000d001020110707070303c03146040e600034040c04003542e405403440e15125000b40a80400200b29204030800f0b020b00c2045032405452404a44c400703014811035025001e448102d40d42d6550040000201070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 767494793 1250 767493543 767493563
    0x5040f080c071a09090106030506040b0315040605160206010509040212011a13020a090308030a021c020304030f0c051905010213030c03020901050a12060902030109060e06070e01050a050d05130f 85
    0x49000703040c014400b40480e00102c400c1c4140c4d11550365000c41c0e141074902510f404201526002c010401070050141000d516004211701b40e0442e4001c1c26030369200e14020714052100f41c50341800c0400700d003199190580140c000c0801032200782031294100ba00184080d000404621003041d5080c2181c0b42085812507002481020040e03d02d01103080044510a2810031032038856511001360000c0410310006140001c08000030360200d2140d41a5480c0300c9030103c403104403086103032081c002907104503400c5011411304054072120b1840780e0301e03c4d60010b1b400002800305004a0120010341520700808850039902000620035121a48010307a0080d03114031126088035080d441000b210707500580000e0b00600761100100140201801002c213869007000740014480098000302c0d0261030b41e1346003e00110b00b040005681074000040140c0b280790a5034550003440e20400044910348611895000002c400740000010f044050348003a4004824402740500900f0540e41c4042c12420140c003611840c80c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 767496043 1250 767494793 767494799
    0x70308190c0c1703010803121806010f030c0b03010b0d0f15060905040501080c030a030c0503070204141608010e0c09031f0204180606020a06110912010203010f080f03040905040f080c07 81
    0x6180e075018503002400600318110760400040503900c0c013900310704234621240b410108035150341d01c40f0b48240c407107920740580711a0b40e102d04800da03051385607200c11034801e0050b10002615200b02400d89068414981e0901d140400000195000c5c1048210581605995070340d8244c02041c0024601c0007001251900906c1c1c2d460325003040308403141640825019008494460100d590200e80c1050040d4103090200b91204103003000c0e80703036000e4514001d40152609103120182560728111900c6102501c00d8401c5013095804103c60703c100a120303142d103800c1c42d0408103c0180d44800a404950009011141c02c0c128501150071914140041c40c503001e68001402d000d10b000d0050001c0c40700500f10010b008040ca8800029075a01620382c0c0074001c00c0d9914451404100d00c11304035211600010108116203a80c80710080c005d42c02841034030110081914001012100030803440800d03401c0c00d01460400707140400c03803005044002c00c12501802410352040c0007a031081f020b06402c151003801080c4581c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 767497293 1250 767496043 767496053
    0x130c0509030f0c0f010224091509010504230c06030c070f080306041b02030f031b07140c0f0a1203091205070801051302030604060b01090f140a09060803070308190c0c 73
    0x640b0504c15045400200581d20404140091b4400d00001e250880049a544800c846d0504c8100400300e4109080c2d2400d0041d0301070150061130003139000308090007064801c001e000841c00034956000c03210b030304100107072003c61810102841e404510021040e2030400160703103c40a020706400100d4600f0004010b111480c180742c4511080f50050001c502c50711341301400041e6a03400381c202060f90341c10300000002d0085021114075864094400c811640350961460540b507654044212901076204d4221030b14054500080c400b690034030082d02c00300907241003040c440c4207080382d000d041d07060184802000a821400416030203180340604c007e00400c50803e958182540c0000e00740c0c1400e01002d503500b82c0907076804110544c01a5000b0070006220155100680706582141c1c42502c0700d52501c0c4000810000e00b14bc0030603112422102c40340d040703403554286e200325070050150304890790060120b400003074080d42d59203130041120080710b5042030150860f2010703502012030000016030310204580c1001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 767498543 1250 767497293 767497309
    0x111120d09140f0304090b041506021c0e0d0f020409080301030b010e07050901051204020d080406030c021207051f021309140f190c140c0624130c0509030f0c 69
    0x1602c0342e030150081d155280801a913a0142d0f02540d01d00507658084034000c2e5030ba40c0d1145c1880c82c000303014004030540c0c41c00065100c150640d070054110b8a40c01340d480d41d051203290103509002008012089102c49a15810707000400c480d002c90304540c6c2c412521000c1400c61000d1802188680b524444a40c1403107061a41c00034081d054800303108050081d1100c9030b80250594440aa1a40c0040424ae03202e00000311902c5c043c60000d4002c5800080100e82c0c298150001084010300d41c003114044500b905050f07080784a40030001d0090f4002c41107680840d940601e6004000084007001341c201048455001d008807855440951511303502d4844030252440301e105154070403d000003101c49845e005480c0f104004460000b041525510420601d41902804c0c1c491650385850440640b41d501110703030325a44e0007060307462603407503100100e80100302041c88500c60200b0f10007510415072a0305100c1c55101402441068009000c0144100301c9140c508004481a0000c494003c040d11800350381072003600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 767499793 1250 767498543 767498573
    0x61008070e0108120304021c08030a1401050d062d0f0b451f1a1e0c0f070603060603020c03030412050f03010f03050d030204140111120d09 61
    0x100c03461401084040008100e82100300300781d420713207580c966680c4006a403200d100d00d00c1095910b13008040906000d40311018521502e103204c410080558685049440c8501c02d1082907880b080486481d00000c16079000601e0303101c0060501298401440c5401c214058130781d00921701c40e0342e200f00f000f130344000328012101f001c4007e8901d90160119002101d284101088021402140e03010b14010101c0341a1031200a4800b059051803040c01c01c8103180c86241c6c400111514001c103a5000401d140542d0300142610104040e4864540600c0b00101d040040b0343c0c868002111509210900c207801c0180314208581e5005c01c0035044080c14888080d00302c2d100c980102d010180f05112620009000104494100380c118282d04005442030030125954412803000c0740d18a400480002000702c0c404044100362032081e01540c94406080c80300314124000c0b4414003000181c20907605d03440c2e500600c80500c0010705041595a111500301c2c0030b100c20f41c0311024085d40165901074000500444481c2010781e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 767501043 1250 767499793 767499809
    0x5010213080a151a0d0c081e0c03070602030703031a0d0501090506070915030b030102041d0108011b08040b1801051014180601050d0b040504110906040c02190c0806100807 75
    0x648000c075402050b2030018040c2c00b4005c140001001083c4000105101c1c010030300c010880e90803208000d20507280e0001130061000d140700701ca05030541850082000000e890103580118107040c4076840444c050900415003844c6502c4903a0280c100da101d80e080035500501580c0041418041b51614900e880d400404840410200031003e00c50400c402c62440085816481c01150407444800000c2c02441070364400c100d40d15607a1240ba501c5030451158504a600d00c1c2d008100f0030308488200010009081660000102d40c4000a8005001e00700865000b0024448000072144801c0c041c50071650b00303039801080349102c0b40041001d40011b00160045a03421f40f040503843c0c0c3c0f0140c0710408010041c081a05001b0301240b114004d440540c01600e040c40d00030010f2059003094241000c6564040c043d65009038100c40004025084ca07009101d0180c285600400b122006030301d5000d0400b07140e400840f0396500081300016101001c103c0c142c0a941c40d013402000c5c443c03402230118544441c540c00301503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 767502293 1250 767501043 767501051
    0x60608090c04060e060111010b0607030225120213020d05270f0312130c030605010f0e06032d0a0606060e03060c04090207020103060b18041d0a02060705010213080a15 73
    0x881007908180c03058100c0405c1c02c0c8100d0941f00204c600b40900201d41740c10707422400225224050541c00038500301c0c80304207440024200f0109082c2c40c050800c82e40a6030b211801d1600c1044c2c010b08103200da0305c2000802c5800142000100442e0305c050701e800703640c1213012903002240440e000e68600360003840200c01500414001404890b540e46a000304043c41d501e280492000070f003420800300c0f03220007444e407011100c68000e444e80fa2842c0201420b004240c0d504405080c0420500d03041642c86011b0382000b0700070058101c1410503254200815405c081601000d211000715403d020020030fa08948141c9021894500740f500c000d01d540b2416801c10f110b54000c0f07090104402c0000d08480503900380d001d02582d0b072905c900040c0c0280c4000d9000e84d0008070001242c01e880c0501070b440c0c10100c9011101030048425550030810084003072407030f03114241c1003006054018501000100340e0f1074030600016007018a014441301a011055000501750340240c0c0e07640f030411010036003c240d08481044100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 767503543 1250 767502293 767502299
    0x2070b0f06011d0409050109020a09060f0f241b08030f090102091e1504080c0f030d1704140d080f09030703080718080102031005120312060105160204060608090c0406 73
    0x200302e48090440060044e5070311609882070010179009025500e070080d1100d00102d079150070110050000c1d00c20600403840162002c40c4000c40c0414500807140f02030308140300d0001c20460500f034020480c1d8000280000c42c10b408180032000301e41c1d6003650703005101e03990b00c0c0c0c40d054680c40342c5250000c0103c0482d034030411145006503581c882440c00e4074507012800d603840450301c005c5000204604118075507034001103000a03820800092003401c2c50025924808140b0b00074083c15a1450b880e2803440104d003941100c8504540d2501041d039110f40904c0f055441d04000012090904c4410521580056682c40030044980045452103400c140c10000562809410351001070880d00003400c51810054082d03890350310315404140c0880034090000017159a0f041840c07441c1600f030a17902c2828002c01d4841e01d010350700400802581e000d040e05414410943d40c03114011142c27503004482c190428192041c0360385c05600d442c8240c1000d07100b5900c40c420300d41840c0c460180f80155008941d88641c0c1044014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 767504793 1250 767503543 767503577
    0xd0b041104050a0503210d1e1a090601050a0509060415050703180f090506011728060b0307030203040c03062405100c020f014b0206040f03110102070b0f0601 69
    0x91914006105031507201c909894407e40038058122800c40010028480d5240348111644506502510340d88003c0c21401c03d4014040c5030380d803c9481c540462000e01c460510300c1c0c0038030020010110001c18951401c1e88442d2000480329811010070001003011400ca0704142c1c0103501801580103c40c195105a40340c4645428801154000c1000d46515540410074590284800000399405001c05818a16101a990a4850320307080803406403d40c02c28020a00c81300c611a801c1914001001145075a440040070340180d03001401c21101c0002020002002c910f00d40300346124054501811210001001413087d215255a00903a104a034440c82c1c3e9140990406600d41d03015a0683e5000c1079a80c10f800181e510250440001d205500ba49034074044400700300c1401d00000308680440c0d2011031400d0064010360803110242030243e4001808580882d440b60060031416200b841c2299a07091407120850070b80e00309188c1160002810700c14070404410a241d603a900c40d8080c40d101c01c411494000d6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 767506043 1250 767504793 767504833
    0x130c0810030c0902130302121501050105070201021009030e090403050901030b040b0d0308070e03030c03120c040812031b0a0c031218080c07030206120702010501050102210d0b041104050a0503 84
    0x2050503c560019400c803900703003e0010100115002414a021207140801090300c40a04138411800380f82c2403c008200b541c000e8060383c11940c2c060b4010040900403068010091100103015070610079400c280c5000340d80c60b010030a2003607120b542c0d4035454920820026058651080200c0d1040c2d05141c0ca083c00b43c0c451014509505405142c141c0041d120b40405464100240c40342c1030b09400002511032545c04000004c001e10b1000030032200c400c1c0c0e16510b04483e5402680214840d541007141100d107032080100143d40c00c00d80b401d170030759000c0c000c00382c01c5000c3d41e00c52042c84001c0344032194011300703140d004900000070b03083c100000e101d111402070701070520f0b60100030014200900483d10b18207402080043c240519030207030045075a00d4400c1240c2080d903400b20344203001507003440004103a652002c28022071120303090890402800004561500603000204103080c19a07079060b035034281e03503214016000810666110380e80ea45007014180a0b01706842c0e007086001ea8000100b1190140950031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 767507293 1250 767506043 767506049
    0xe03131e0510051813021305091303272709170d0f05040303140c07080405060904020c0105150a06021216051011030f0105010819050603010b130c0810030c 68
    0x141840d901d001c0540f100342d0341808412115041706040c8000da6404119a00406924400b51720740c150a035900c2d000c011013070350b040700d00b10b80000803c0341603000a030040c8801029808883c01c0e05c00c42444480c104039001c42560301080460100c0f004031038001050007444e14200540700018000c1d0340b03440e1601501541070390700314035140000003844181080700d540320354074140d41c065090100e81850700f0010042c003000d0403448501a03180e00850b142a52140407540c28552082d50a41080e10701810010a50480074a064200e6000c00809078440428401d803440380001c0394103213070300c6942c0f81c00307106007040c2c290015015541b240044010482c0c0e13010a8038640383c1c038501e60600200c0030b840c0c4140be0a25203c0e50b1060f0905000307407558200302440140d442900c2c40e40303000000e82c0e61103004440210b010ba885c07003003401c208040380c4190100368000580c000400350007c03a408a0303010105500201411383c0c0503905940d034115100c0c2c0d9600040b169001500003d132034407401e0464582d0b004c00d6403544 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 767508543 1250 767507293 767507297
    0x601050304020f01260c0307032a0305060d08030f07021614060a1e03050403031104060531030321060506040927120206060301150e0a0e03131e0510 65
    0x900120000c0c44a003545d0000500180d2964110b401d04030742c0408580c00940355007001c0b0b400c000003070159900c644180e040c000b0302880c07185d01c8407006082c10750003060f000d05207a82146d416030040d000301d485071000707500800034103101300d40c7c030b291050340242420b5514800c0f240036000d14004010100c5180c0c4100e030061021070f48959200c010315003d03242001c0c2c003c0c0c40e01c002c966500300d0459681e010741c060392046000380c6060102c020f001508140e03510650103280e0104009010341507030800b039410a1202180080790036a0007204003603208040501e81e900c1200064043d03000c08459039070781c40380c82523004109a42841298280030006210340610300443c10401d55035595104100e00f03000c00c0d405170048a410440305000141011582c40075210341900243c0f20300804110756043c144991328000652500401c9618213206508070441350240450224a880d0200c600c50b804041c80140b01c0e00c0100300f0034110135480c09085011203a0003008101c90074448400c1008561240982801c800840b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 767509793 1250 767508543 767508557
    0x3051006092c03070b01151b030909020d06030b0901021b0604020a050d03090519060807110c060c1c0c050d031b0e0103090b07180e0402130b03030d05040c030b0601050304020f01 78
    0x181e9881d40f450144078805009051040000a0346031584044203081d024030399902c001000540c54406044405043e0040c00212030101c01c1010072031540c0906954010114089040c03a42d944490088810035104102240d50019003040030301c03200141c42030030b082c4000c043d0030302d40b40c29000100d00c01c003507108044c0174160002d402000c05104065850240c11700070004d403205d80d034502d42560501200c1c02214003040946021401c02070094a044200d01981c100a0041d00c02810030f10076182c01c85042403050f88500300d030201803855425209210711019030b0720310ba9400c4950800c145411a20b070052001d02d4a80483c446003c40342c019405034034001414095039800301c0e00700485c010311402c9800b41c4920011410322a00e1940100c220100d51400040ca045c0c040c0c662404464049055a00a5003d0b40c0002d000e12030a80782c0c1c008262a42004059034286024000c0003415120211000c40704d4000110003402045032030304034981c024800386403480c11031902d51701144582e040100038a043c8000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 767511043 1250 767509793 767509871
    0x1e0b0f01140d0207050a02130935040e100b030705040509040c0902031f08070605222103090b16020f0a0b0708130506120c0310030c0305100609 63
    0x2040c0100c40070b82c86400402c564946850030600e4803004403030700891080703020812040c0003000038001c910716982c0005a4681600d8010014030942c03400700c80310480c11103500070759000108182d014000034014001040001e18104a501c0c941e251540c03c00340d4240020b1040c40304a82e4020b05a5058a00640310076005885500f00007914110b03d42c003030703403640e40000100310035034001c0d02c20010f8007000e10301c140d00d1079074544a5664440d6624015000080c42c10312483c0280d001210100d2280310030221000c0c40303541c5420388848440110a280c80c01c60300b2182103d07040581c4054141d0013401400e0b0581c0c2040701a01d4400c00d50105c1c4c00000c0c1c42142c912070008225506c1c1c010b040014506650030b2603a4645629119610703400c0b644025548140c030900015280c108402220203485101c40f1882c0c0341d80c1d640c0f803203c0d9903400290002014510342040440001c0203e00e02c10045d501030b00080580c0001c001564080e217a850300b100c039025041010041111402e080324028402e01054010841d0003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 767512293 1250 767511043 767511077
    0x204241d0708160e041b0306051002100b120d0c03090b0307121e021305040609050705030c031003080a030e0610060e0d0203151005031002090907080402030309131e0b0f01 75
    0x1000700c1116900a02d00990720b0720144440c13120141101b030301d440c11f000141c2d42e00100b220303a540100300003003d0b8002104150842400f6448241c4050b801011380c0446103154405034134001d044041c0b200440c9800980c4003e05801038090341c0100f0410711014910326106000501d09a80d0341c0c5414400380e16045244141999900210102501d00742c046484200e940c055141e210040e02c5091300452910801003109201400744a115043d152030340c40c55078640c180320b00c0455000401c0340030b1000c8040b00200001b0300580c02421a0806e99501089000c042064a41400d40140c5015000e4150501c100a040e40141c8203201750070702140e890302e9521160002c01e04045c00720a5074110b0100007010845c0003000449600103492083e8200c4201100d94503a00c0300f02e116601c1e00c16408810000014203061080786d100d82d1052015082c7c81c244040c0b200424082111208950002900c03120b900b0021014590044e6504604080c240704070300d4964082101049031440140c10004011400d1801c48 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 767513543 1250 767512293 767512307
    0x2010f050d02071b150504050906010809030c07080309040609090210030c12020c0106140102030406051c11070302010906200d0507020c06270109080312040204241d070816 75
    0x150000c100184440b240d9421113150116030041c02d082d15441210080c0140c80762003a10b054400103005962541c481400641d81c8100c0284403441c070740303c204260000c038001844010001d000160085480d611114200b1084d82c900303812000e0318900d01900359015136554200f1110300f07140b50800080c408406d4404950341c1150b01003895803103000107070140c0107074415404081100d50800300b6044c1e07203403000300490b00c85c0720701d20174080080d005000c0304418010526103200308070b0007110005145a055024a8a1500a540140d016035944c242c104240b100300c0c0500c3c585480140b0240006001e0a4141d851502030b1040c003041c0d281c1e17a0070020722624000c00148810440c0201055222044a0140010740381d244000d403250201304983c852003540110303880d0741500c0f600409503003004440c00d040d04ca8000001c00580e400364503020300489000151040e001d82c066150003040e540703401d00781d04008012881c4480c401c803d541d00304110840354055196900548040e102a80041d1410001c80b80b003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 767514793 1250 767513543 767513557
    0x182728152102030f1501090c05071a040b0135070e1f050901050a030602030a09061a01080f040f0b090708030406110c0406030507090c030212010b0703170402010f050d02 74
    0x40001d03140701d48002919069400c61062003102128000742280e45140c0d210000301684c6246403040400520000203a0342040901c0c01061034240e01300a1a03880c0c084411016402003076440d03200b141840207000703400180b43d02400c0d003c0701d40c50854852a207800412070042102c040c0c21589400c0168141c1814042140203005801c03504809044c142001e1401a0084204402481c82a0303400035030360408056443c101c41d40100101d03281031454450348007030360000f0440c444140c0d680b2201400154584204400c0c11b12544914010325045000501003000203407992500d22040c0c0c04020000d00768200c8108848c0d80700b094404207841d1b03503030380701d00c1c5c0036850304030302c0f00f0740004117001c507941c1c1d84061000c000308882c1080300e0090700f440040c80308481e00b900016101c1d80102da400d00041c04aa00142d08019081c68010300d00a00180718100f84d400070382184241c8600050060203241d4070041003a2100300040d106c07005800d2990019210191001c48a814410040360700c00d843c03030f0554113507140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 767516043 1250 767514793 767514809
    0x21b0a090f0e06181510050909011b050c160b07020f150a05090405070f1d0d022215232b020102120c1218272815 50
    0xc2400d104c00025075507503404100b00182d00c244000b000c03080005170307203e42c05021005c003081115420a001e009030444d0003400071842e9900c5604121aa80740364440c200d58100c16a11140c843c416152541d042203110501e82c400503c0002052100440c60740488602c03948c1211692030a45018020909405031003c42c0441e0a00c0401c4980811343c2003c01030840030001c036410402c40c2c0d604a0291860719490500c040001c41141d15500000a02060400b1040000785242340c000350320f034000f45504804050b07243e05450154500e42000e0a18090500d2071101c80030703040149400c100000c0c501c2d4035100410002081420400c03d01900d50160300000301c10034001d10006000e051050030500f11103000224010b00c03401c0001d044101e40d40080e201302c2541c0300064007440391451075190341500b00010a02c6500044145c01090b40c0e948151098208401c644807581101d03034109590f00c020000304280c0080c000e00c0b000700034001001003110314110b2841030005450050040d002d002581035000710701 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 767517293 1250 767516043 767516053
    0x14040803031518011e121208040507120f0b09120f0a030f29040e0304060311040503010204081f18020d171308010510050306061507081801021b0a090f0e 67
    0x1c1000c030f1001d03804100203400030b1780d41e8529540c10741c100c50b905004102a05d143e101450504000e4030502000703400c54091400c03242a661141400d05e0510480d0008944d0640500c143d42c041046110748030740d10008a001420f81039600c114003c003603204210301c030340d00c034607000604100c2c040c06640814404280b00703100b00034100300004610b0b0070001842003042d00703403041c3c1000d43c0c00f480c05000b0000302100400c051400c084c98202c0903030140c2194038100d051814103202c086884e840c240b02910040800340000e0601c844400c40b00b00006c10030852090020303091031482c011a1040100c01c041d4540d05031005180425141844240030b2440d081d58100407800291180300002130040300420348185070700800280c0c4440f18625070a03242880341d545c01d40c000c640080d006152118191500700101c0ea043c52034490035a40b0b46005601176404156400c60700d42c0035140c80d5904108009401d880084040780003d290400074001d00f01d180300c1d03000c0f0715440b04c0b0740f45200f403859042285040d02c040202c035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 767518543 1250 767517293 767517299
    0xf06010906060e0d0206160203011b020a14030702090721110c0d170105010309020d0c06021605060c210c061009140f0708040311060403020d1404080303151801 70
    0x80103005540b0502c00001c00441c0320704550320300960201c0406031700805903840c1200a51b50440c03a1184004280e0f419541e81c07003454001031111a41d01c2c9889115405800c101400d841e01403024031089680315905e9100f44040c1d00107031161221141c001105082c4100165000007850303d01c81d61126001710024108444c3ea000035150002034000e883c0d4036001e580a0f0607a03a04110b40003415114002660070100c2c00400041d4001d41c8020348a50006d00200c05a130340c40d4550b10000c04a590082006030301130403d2854a04003600c80c2c0001c1c0c00e0072a540f91800329911340660b40d41e40000510001501d02013405080780256100725a01c2102c01c101381c804610380815280c01003d1039210b0074400c941080d8034081c8800ca0300741c2c0d440c803030311420076103450a443c0c1000880d030701080144218140180307818207800e00801040b10b06d214520940c018114100002401009500b1020080b910f50304244010300240c140481a0b03944522102481da420b800840001a4400400e14a504007080b0b204004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 767519793 1250 767518543 767518559
    0x190e030c07031511160615030c05101e0315050a0f0906060203160605150d080a11030a0c02060d0f1803030e1b010818030a11060109090f0b0403020f0601 67
    0x328044902a03000c3c1e804051100c0d0080c416030f90b0007220f0440429041005000c0000c08102d111101c502940c2d00040303840032035035040e800307a107990029650640024820040c51400304000103541242c1d15240e2042c500c004032034800107001d040304c0c80500d07440d040c4c1100a5400359680d4002444020401d04030389035100c404c0300c4440d0343c50080f96116403c01a01041440c00081241c04940c0701700f407809076a1280d512060014600501a498040b60b8060405003a40d074615846440034000d94a9070b030740b40c801f44009007400030344090b160820740060001c000740a03040068060140c2c1c05a0b03002c0d13503039250050007038010b001c2e42c5040c64409107440190409104801d05600303020784030f902c00704400a100540c83d40d581c201600040343c1410751502e00904ea500c9014181d820041101c00c203400ca0681014850858101c201c070100000d40004204254503c02c014850040000708420400000d184e01c1d032050072501d402028085440e0341c00454200761080041c1039844030a1001c2d208656160024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 767521043 1250 767519793 767519803
    0x603010f0c0e0901151413081506100309111003090c080a12110303060d060e011103100b0405060403022101140703110a0c030e03010b0303130503010c0c0b190e030c 72
    0x540c502900b540750021580d107140248044617904a80c0b1941d8203d000d4203041c11043e40310002e201e13041400c240000901400070011005c01e00c15403a2050441e20b001b20600900300c1131040490101070401160f10042071003114006d248001c282d604c15908414aa0700741c002c0c11001000030308480000200040194000c600c4400480c03080306919080c2c0e2028600316411000d40582040542081000c02c0070703464a4010310460303e100e40408103d0400901e5810b013121141042001c01d400c0010420000314110030814001e807101180e00c80c2401e05200102d5814000c034003009009060781a62400e54042c8144c614a00110a1000f8401b441044900a19094040c0c80410210b810030b0700f86001e1084440603035170000301135580d0b4844ca82003910110350100e04804901e405559407251090140c900b8002840b04e00c2c20380c01c0901080d071400040c1400c4500c030549080c204040703100d048000485c001c100740d8100d0340342e030080034100c1800354100c4c004221904a4049621000801c000030101c007181d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 767522293 1250 767521043 767521067
    0xe060a03020d0803040605060603040b3111090603240a02070c0b0403051002091806041506020102090f0904030207030609230105040b070e0f060d111c05071706090603010f0c 76
    0x240826160301c0c003271111501050f039004005011035400901c180301e042c00a10311283c0040300c003890302072081e03902c11234210884200f0b0300ca0305108003158019062811119400c00e4099000300010036000440215040d0441441c01d021404980400c1c02d9914035010703111443e07000201e8812481d513996807e0000c1d4028881261a03000c0c4e00802500000144281c5036000380180030001c1302c10241154202050000301447d91082d5108840341d0700703403880b100700405043c0355000184e031140c0100811040050385d002c0741f80304401010030070000030f40c0424640c080701d500c65004035140b03643e072070f21602440810100c4171202d0070007081040e440714150001d5000d20b0080710891481e4031195000c4503241d40d0085802d80080c2c20300310f20034582c03c2c190010412098800000610070020801004440d8070504c07090407000e44000211100010310312400b03400c0a000d007410200c8e02c044912200c4441e400800c26842808410005080ca4800303410100c1d410300c88890410140390404005000c40c072100c0c0b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 767523543 1250 767522293 767522303
    0x10090602010c030204030b1602120d060303020c0303131a04051f0e0d08030c07060e07030804180209030d20010501180c0905030604020609011704081c02130e060a03020d080304 77
    0x3082c50016503020b03200300c509490708002c0c050115a108c09081b100c4202090001c8110720500c0002e00c441c0c00c04001030041403101d40404549146181002480c028110140340d1013500200800072400401c00300e150308030b031000104011388900d0500261094001c03603108039084410040e158100e0080c1d10303014860030500380c90310303902c0d5144201840140c0c201c03d01c0007080c40d0000c1011421000c2e1400150a040b481260041030000c80184000d05049050b40b0440c1e011074041410311070f2103d50304074002401150803045050080180c0060740d01c0c1d0700400031f0010700400c1c14019221107080e508081c00107515800921503565107950308030f605090781101c04015031030817452004980c0f01e07401000031218000c00509440d100ca40800c50140c0c01450198180142450380950204030180313150701c01c500400505456481c03070100303c00308260540e400c11003a481000300c61007051340030706540d0544003400500c1d40c0e26035500010070091511500041c7d40f128481d0884070030007400c04019442603120b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 767524793 1250 767523543 767523551
    0x91e070906060f0c03231b0f0d090b0f0c030313030f05070b06040509070f0b0705070f06170709170304031109010302060d150e16020c010905210c1009060201 69
    0x511003143c502d002e4403507040000b42c0d1801c4c3d003030119100321445d07126140045a400705085010490b1041c0717a100b08810441c2810211040401400c140b20040c03c0b111142d02a000e52003501c0c00040c006100c0b4010880000c1c004191309109417080e4054400ca032010004480d07803810100c03107003800324a0a072000c0307000038945120508032600c218250fa00050340080c81c1202600c81104100180030024219002c81c4100d4000240c2080c1c282c01110081031022081a51040503042890a01e032280d00881c0a1a107013480400c00700307a0240242201040c800440401c030749070725404030341c140c440d5031001e01e5900d0f24510441c0102408001002180d103e41051110b91000c0300038000c0c10102440040d600c50b40504c400c0e44103003006c0c1c00c03800d644c00003560105201911540701010200f4207960603a080c110b1040c03a150360a404102c141d4210209091022540e490117000038103a40071542e98075102e252488400d41021800c03c0381d541c207910001e020805004030200010711601c0e40348660710042d0300b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 767526043 1250 767524793 767524799
    0x30f04090e0609031c050613060b041806180914121b0705010903021314070509240901110a05190c12030f08150901090204050301061715091e070906 65
    0x4200c50b0345c1c00407145610070f0090244a804000c2400900040d0810613210301c43c0584006403049074090038954903015140c906008503e60000c904d070b40c0f1a00c082d07281090500c03111000319a04840d000c511603001c00c054140c0d103040300351540801c056803420301c00c0791041d581d8602d241001e005002d070a4a0500f41d40d80302d01d00465a210100e00c10325011a441100a102505040003420404198010f001c6100703000384407072080c0402e040f00c00500080c0301058010f054608030390740c9164914004241d1920400a03440a031540c4a0202d0150501c807100380c0c240400d803010700ca40c1c0b209035004000c1d100038410a10180780181d456100464008425200203d490441c1c41004550260076648068001c0628941600c3c0c000000c0c1685120540c4040004110340d5000940c0380601180d100142e00ca510300028142902c3d2580c01c03603000b030310150311074031000d407000904c100821b0200c4a1003962900c40400d10f5042c0341c02c0c0e219000a0030080b2000000181d00040d2200444048030810402996 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 767527293 1250 767526043 767526061
    0x6110c100e0d02071d0702030f0c010501090b040e060105061c0615030606230a110a0c030c0605180d02010306050303070606141f0e030f01090f02030714090f040302030f04090e06 78
    0x4d25800750001050b0b044040110340d0090b04001e65205242d401102e1400041c0386011b42c1c15003000e070801c112a911240140000401c0340a01651030b0010f031400d0003402c2c07100f02247d440e58014001c5c580511008a0000c2110b9880119810420911303d030030444551100840008a00600b0715130020038100b00000611920800340c81382001e072500b600c050448640c00c1c0da00e002c0da202103441400c00242211a801058041c821250218810640504200d140d49811002103000394001403e0120030b01040603100c008401500d502d0301c0840300501c000d9907520040e4010040ca0704001d0705444045544010005180e00440c166200c50701004c85160000c410000d041045880d20324840d100000000c184502800c94114181001001d40c1c8501c4143c3c0c40a50854032201030540e45101e6440c120700942c10300b4042100507100e00c0e101c4140500c0e4120100d21038500241228014040400004060601c240161180c601109a00303950381d41d0b0310044240503041443c2450254081d43c004542d141c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 767528543 1250 767527293 767527303
    0x510110d0b0301020f2d04050a0905060109050a0e07032403020d050a06060b030a0b0303091c030e121b0f0f010809191110030e0c041d071e080304030302060406110c100e0d02 76
    0xd64009d1269054a00f000b460720003900014194070305120080744c02040c0c0340d80e40f4400303070094000342205005074078000300c0040984c0d402d814a1120540c081a404112000c008400c2060b25015102c100300504107181003403820740c5040018080f50710308100450005c080100560040c09100760a1205c9181702d020152039218010510381d01006920394507540c040c42401001002e800390070041a4542c2d44030100d920460121445010340e0001e40c6010740d103851141d2604010f20040d200700c4d101c0100b000100751180241c0401c1414480c802c40022402c40c000c0000b60400c408407110b2103682c2c4207614000e2494130582d202c15110f4a1351071140c2e50001d02c40d1041e40f0100c0c5213130b0700800c881c180c81c009002c010080d010040107100c0150301d40e8001888100505801854599007201103003100c444490f45041c2c40d5040542742d900b0411003000400d0340061503980041d0006400998614165601e0701c45226101d85600180034902c02402d2030902644840313601314072481518182d81c16018226290 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 767529793 1250 767528543 767528549
    0x80d050a080402010c110d060b0a0911030103020613080d030c0e0603131b0e1005330d021b0f0606150403080d11040306090510110d0b0301020f2d04 65
    0x961101c000501540c8201c01422200c0d00900c1c003c20041d02c00301c042140c2ca000e418069880c562690320f410020b00307000f04144000e0149203000c02c445001d52503101914401848082d1181d031021840345004100e0050f03101c010324a810440394581d100307480240c00f41503907524140114085219138a040d050900860340704040b1081504000351180d52004040000c02d007020b07013061004040494400d01c4001e12034000c5401c00f07000d43c01145054100318a2035210304d89040304841c4403526080032074a00100d90b00815441a02d40d41b91401c141003a0028010100c5041c0c03180d402c010718403458013010645558841041090701d030780c0d80d658414070820161380c00782c000c0b48100c00c110030400700364444003400102c2070b03d41c0c012a0650385030401c810b032a0890340064440a627074059680c10060100701e0219001c01a10041c00b201882c0e90b01714816025050a400103551200e9001c90169000e5044038644404502083d8958500f0702c2900b183c039020b6007000c0038411103569036170b288001110950b012 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 767531043 1250 767529793 767529797
    0x1f020c0901030b40060b0604060c06060605210406110d020a0f051c050c0909010803040825062f012f09101103030c07030e0405060a0611030c03030907080d050a 70
    0x100d80d810300f0750964410078404d02501e0700da90b01c4070b440100356104070080c0001c2409a40d9442ea500d06c03800c0c036100f185c455522407800d11078200181d51024580354007648144203039240c281c83c245d40303508002c00074110b0995084100d81d4001200794500d1125405055800f41d10b54a41500420300c08069031745219010035800905d2004045240900d11a0001507012088a42d16070034044070001141039039000303070450702d1550404102400581000c10901e021000710752144d00c00440541041098007440b80140410003a060a8503100c0240c40d01c1000d0f0b4940c0181000c156024880b20160700816156202002c070b80c48000c00304014000d82d2823900d000b9595a414035162116a030f0800c055407180000402c00d200700da1608140034201803000d94440d00700540040d54429143c07900521544210070018422494001449419100c1c01d102c1e009844250515030016054111854918041d641140800707100010800c26460008a61002141c02c80404c070380000040510075542806503288001c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 767532293 1250 767531043 767531131
    0x203090d020604050c131103010303091e050604090b0f100519050f180109091a0405070c0b2a0d0b010905010c050d0c062a0813021f020c0901030b 64
    0x30051400242c6c07400b40082450b0300241542c1da54180c4201038100368403e40c082011104208483c03042181c400940003d05c2031213410282c1040d000426502a90040c0720703505a4079078003591143c48098800b104090018030481c040c040b0315800905a900450440340408101c04004414030700613020b0390301d601c0c0440b4055042a115200e540b140c1d5021070091070400580e6100003500a5032845044038403d201045040e089100c1c405000a0700c2d0701615040810031610b002101040c220580540c00000703c6080020000e6581140f80a000d11003200075000300001407003000448103648883c503440420f8907446400c0b542c810041d1411f0f0304001024025402185040029900c10807005e00094441c00001603030342506410f0f20001d8000c0f000c0300f012031458907480d8080c0b82d00025040ea011200d218148648205907020a0410440762000084000d20311a6008598002d02100d40701840241121519695030300700300b489800182d0700801081e40e459420074101034070081070310100e011322130404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 767533543 1250 767532293 767532313
    0xb030a02033a050c0106050604150c15021303060609090206070f05120c0303090609071220100503010e070f090e06130e07090e07030c0e100308030a0203090d02060405 73
    0x241444050070b000d01d003844081d5005011894100058106609241d9681500c40c040801d07000d08455094010500c101e500f0320080203202298103008440045034500b0500314165480e0141c5404036000c00c0c0c241345400854a80303988030344005007408507409000144205560340c5000c80813074900c020042d4200804000003004117999021a03001d07144120215070030341200c44685032407500310850701402c68100005100400c40200261500001804040c185052074110f1802c101015480010609240e10840703428500b59201080d44036403002d4840c800030048200020001c2c1d000f40038050b200940078002c0360b81c0c5407042168290040c005d450740790350a414000d0003071030103c004200540c071020139080380c803d034241ca0003100701070300840c0020400c6a050100150035a82a040c103110303a030784400c0c2c007000868100e0000800b203402d0103412a180c0e455200121404440076040917048240010034801c1c40d5100784e009610a15005081c0c40e00307030140368002c80e10352200350f80103049984018041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 767534793 1250 767533543 767533573
    0x6060c172113020306040b040218012301140f040f090603081c020705010c02062e0b030408040308030423010c020a14010603140a020909060c0403060f0b030a150b030a0203 75
    0x70a4100c4405000203102c1c0076241c0c0001e14044003110104c48400c6058140421414501e12210500c40c4050a0b000303290306104005004c20b072a0311822200e00c20b03a01d4a5034059000741e040c40c8032280048622030392168900c000c80b00c2540302d8401c4051300a0318480000b41c840082c03040c10140e96005550300c0c0707001d1140500700544000d84002c001000c0d0300b0000b820002e00300b441030140340186500a884903291103881103910b012001c4158224881e0010000c0d000c00c5110a0002514503549003e41c0700e48542c180510b50f4062034100900145001007440f05010020b40354460ce00c0f041403c40d050010062005400d82d0700d51900e0b000544d102d42c49003c0010144145040c100081d40d00010b040f540d00d8a80070f0356403030050308200713964101030240c0f803c0d4103040b00141c0d84000183c005001034100442c400c075040c0b06070700c00500941e130758104a003100e480b03503004603090b6900201141c00c1400c0604003e01e688a02029401c903807031424507180054240450074881064004014041c0642c119800b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 767536043 1250 767534793 767534857
    0x30f04031113021909171c02071a27030a121806030e0f03091c0c3501051306021c051807080a0b16030f06060c17 50
    0x2142d072000c0495019070405040384041e00da4482c010b0100e0801030440000034240c2c10880d00082e001c0c01c4910710001d2403110002e0070900700400700f60401c0e003080800d0310403803d0102c2038100c021710284c0000366420b402d8100703029011011500c214000c913500c80125941840e42500380007505a0880d00c0500003003504401c90b03518166090401c2108000708402d0615508040d4001c0800300360348102d0b42030075100421100c080b4240c9080114546400f40c5d001400b103110380002d40c41d0020b2902030180c2000440c1100c00c0082c0106a140803070320380705240203c05e00400340310740c45400c144003104145122050103546d0190359040c0741d1914103074094031100c0195001c80980040c200d01c0d0300d800c00070703544948942489107046070070700c0c0d0303854405c0361b9000d081240da584040086d40c000070a88000c40c0c07040b802e1640092010034214200c1290b01001c0e005450420880c14240340303025800545181c04c40440d0071081c1c82558808445682040c05540a0051103c169903043d40c2030003100516200000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 767537293 1250 767536043 767536073
    0x6060509190c030902030706031410120b041b060908060f040c0b0c160914160e04050a0b0d0507061112030c070302030408010903030f0c0206040b151809010608070503030f0403 77
    0x103404609a08280c0100e0b140000d08e520440001ea41d030040e444400c0e0361f50500c642c01105e044646000e02d4a45240000080004403000d490300c0580c0c0c02040c1008982c114402108807160030040f5a5661184090003081c205e2140346403d018220001d50600c1540d221180300300d40c0040d181510500304040031a040d000207181c0e0b5a1442a410a014030007034011100005204e01500481d14040c07400103800c82c0000034040d030300b0702010041d101030201d4019003804004a005e840000f000d9030381c0c441c001d000e0300b0300d41011034210400ca015501400302c0800c240c019241a911110482c06640c85800c1d83c0d00494030a8802000051012170441e40f21b0394000c12400d402403046904051302c0d003c8050841d00c1140084001c01c0d40c60503030780d42001b05070055041411542c00075114500d0f21351a40010307590001c111b115043c04c00c0407c07020315074581a040712004100281c886e4207140550701603000708201e002d00c02d100d10424800140d80d1800100320780048498007003290400c1d2030750717403014000d00c9249 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 767538543 1250 767537293 767537297
    0x40f06020625110a0c0f050105070308060402030c0d140609060d02280308030906040c06050304080a031518090209091204060c0302030f0c1b01140f031302120a06060509190c 76
    0x5002403810180c100000d0310130314000c0e0120741041d46001d03004841008168000340c14040c05118890102e5041075420394400e105503000344e80c980d01c3c600c1c13101d5148900d0896011440c03416076004280329070703003845a1151405407040c642586907101003112024907400000d6004108488401c8003840c4c0d4004541100c44290321411916200e603262421a0800c40302c4404a0740604100410301140c0d115800c01403600381045481c40c00d00703468401d60352082d65804001c0c5074803071414001c54818221000010401c4240c808402880780c41000c02800e402e580c1a031180e4460340218030002008924411003404541c1514941032425005544108402a0640070742c0001c0c0700114000c008070000b0528030b0300540103002070048003c5545507420303540c00164100030003c503041c06241911012203802c51440303103d076501c07551005a110b0201504d200000d42124014911007103481c40020805011480b480301482410784404c00e0041c4c8940071507150002252903180c250106495900c410400240d034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 767539793 1250 767538543 767538557
    0x80a0615141209160b0406080c092409010914011e0c060504080720031e03090d0803060a120302060c2203082703070905100317040f06020625 62
    0x10314042d00300c01074100c44001d2650056001c120b8124501c900c2800500360020210f8100f60403c20000d00b500c00c000d00600ca0700c00001407115080d81c46814046e01000c00c0c1d0000c80c2800d10720003641046400001603180410101e44005c90228210340020030b9603941a510703075582d51821701e00c203821084038251041c144445412400040f429501480344983d000d02e9200e5500c02c4146070148550008a40d4440a80621030b001491035401003004c5901e0303400030b020850103614a1100608500c18540f810794400c3c0580300360b60030013680c03802651003108203c4070700030f9060f80c0303040883c1011147d600c001e0060b000600061542d400b550041c0000a141480035800c000f1b032a407140c0145201c980040e290400042080044604449075203101c0301c2c401c0800880000640000c69a101c80b64021032140703545810010301854041c0c1d14250017113811450909000395100003000303481d032041c0a05100b1035402d20340442c1041c000566a07008200011203200b034042032040d444603440c01c015440d0304024007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 767541043 1250 767539793 767539807
    0x907050d0e0f030a0f1e080615070c0e091203010f0302031510052b2a03020f06071707120221030a0504030302040503011505030c150d020306030c040912080a061514 72
    0x1c890b06c40010140d43d266006079051540801c52155403040c20b1a0302d002c000c000c00e5001904030003070041282c242e0b10204680307480d0300070098185541e03910003600c500c501200020780e040c58007003a05c1c1100e00079003d4404d800100c01141c1d641520880d806101c0c040c11020030002410b0900c00030014403449000030039103100e65144036070b100000d07940680785900c260f041010380c045070b00c1402e00c0309200000c6841d42c00c1e2030341d80481c04c0143c0e0f0070346181c03007140b0218140d0284040406c1c00e80d8281c0c0203060342a504d81e03041c68041c018907004100c000040c4031b4110f00d424101c0803940603542c2440c1d00b560560440c0e0b05c078803200303000d0007000704100c040580074000002d4984090040b040300c20180041c00d02400d091505044c0340c1201506a01c0c442c01c007219040300c11a0351501150300c400b007503040250381c9940d900040303890701134990760494003e441e0001103c14083c2c80940c0840c20940355a8010082d11601501d81c1690000c0c01032844d2440700088261003240103524102c030000c00c040d03186080c128 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 767542293 1250 767541043 767541077
    0x40f09020a05181b070b04080306010306050613061101140403021608010b060304061e02270904020108043903060f0c050a0f17090703050f01020f07030c030e0907050d0e0f030a0f 78
    0x1b0f001c1d101100c46c0c00000c814010300750b070580191405410103889041c00c0c646900c06441e900c800d24810502404007000da40240103100b90800c40c407a04609202949074107242c50000d42c0c0d400004503060304c088200c0000b28002406005215092400605079819500c03151581c400425403410308060812004000c5d4210f20500d002030081360000600030b940610784d0410780c680801d00640400d114a0a550410006030703004030314540c200c0c1d00100c3e8441a54041c080246403a1403114040c0c80c44805515001e00c2c0800c007030b4801003039910400007484134020740b0006034165001c0314849800300c0c0080c00340100540c41124584240c00c42840d0000d01e60211381481220140180c130304003019000340d00103105103c820004180044401f40c02140b42030020502d1204900a507100241000101d4810409252064004038080c09009017084014123181c0c01c0500640e115801404800d41000603002c0c102c40046101d4400740d0350032024501e0664042021203500044021110038000040105603040c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 767543543 1250 767542293 767542313
    0x100f270e01050a0e01050f0c031315020316020d0207090c021005040c0e131e06020405030f0703120c080409020d110c0708060a0509030a0e0f040f09020a05181b07 71
    0x5081000080c45040c600888404c4d9007006040071107036810002400002130901d810b080e4071405410300607880e0b4560304c1e90720700c11001481002e4000148601210f001074955070045005829141d10481e0120045005986031420130b030080d00503070800d15040120301c495801413202c01143d481551402c00846203140c0c101c43c0151000c2d200703503105d04014498400c02000954200c0204040007901d600c103950303001410440e15122100d000810310301d0600300300c07850301504c01810b4001c06403504008000c110304c0c1d4403081444190350307d20034480c941681c1401b5128924610b0741003907404c1d1a140c02d14404c0d8010754000d400d0b001c2c01030b50303c01d03841c0240340d032420140441802001c064002c8034a0810041d11f00500035100d900003a1030101270103450703007001040319100d0311581818082c901501001825101c43e405020340c001c1d04060358481f001341907511008109108551482415440340240020402c01032088503144070380502052100807201c43e0503101d0800781410926007801070382e07440d0409c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 767544793 1250 767543543 767543561
    0x20907050d0b1e09190e1c08061e030307150e100c020d0c0c0f060f1d010e09060f0a080d110c0a050913150b131b0e011103070b040209100f27 62
    0x84c2d000321f0a001011507108000c9000c04400f0714007900a401c003000000c039142041c2d45802000510700c0261801510180103892305a41c01038114110054000028000ba0040020074070782c9005000c1d20001c0b203080c9100c3c40c0c01001059004000c0c200003148103440321208100c09440801a40d14001070807c982c100006c050007881c3e458040d10091440003074200d40c0c281400c03070f008107041c118030500c50364800703138003403074100c0480c1c00f484181c86241c007240c1000c65503c80d058006001c0c2e80702080c1d1800000300c203001c95400b590781522040032511400d1711030044c810f000f90f0103609000c0c10809442e05408843d00a298102c41d407036240b069580398450380d030a06444114803a2104200000c6280246c075070081d0804800d001c1c41840c1c9103190420a09818040110610551002442c02e90f4490400002c54036881e6084a41d5410b1504140030004004c03034049100302c0d07100300041e0080341c0c400d400008650803940f81108560402849c0d21100f00c1e043ea441c10135002041c1800240007140c000d00ca04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 767546043 1250 767544793 767544821
    0xf270212060c07031101060501120504081b03090112020f0d09150905060109060b0702150d0902120a1106070804050103110c01020a18050a180507020109020907050d0b1e0919 76
    0x60f4002a2a010388103170000b41070700c010f80c0d00d020003c01c451790308a00c04012107282c0c5040000c0300d0744c81c0d2911045074000c0007540c951104003c42e150807200800030040c0000b040c242c8821252041080c003180030780c8501c1805120350303042444002c1d05288683c102042e0030f0712070700400080900000090f0112a0100000d8840341d010000400503c038591003900c01038405091940e02c1e006480d00458603000c4450001c407070041c40098840203514607a84690701c00b03a8014100a00b2803904404c06075540d401c080d0680314220000301c0d183e4240341c10400c0701c8182d640321041c80e06007480c220040d0002c0c030081c0142c0e00f40903400c003e468a2001e00388010501c01c01503464809202e01410540d001d900d1054020a001c8c40d1aa9010301180d05035100700e4050280605000c90141c0d2200002c901500003040000e400c1030184041c42103a54000c0c01800d4420703100502000050110300810043c90b803100c5085041020000c416403490034620ba2f410303408000c081c0e20450304103480104008991703c0c500b480726 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 767547293 1250 767546043 767546047
    0xf170c060d0219090b2205150d0f02040609032004090f1112031210120c180c0504050405040f0c0f0503010b101b0302010e120d0f270212060c 62
    0x1210f103e400014204520346022254030782410304074101c5110340001403110200ea40c10502541c40100101e5000d082d020301141e9414848135010300c040d4000d00012030450341000f41000c01c4000610903541162929624514058036607200d9042c211000035000c01041c840840d1900759031544d00030700340554420441e18450310150b0a00324091480d550300948143c0e0b0f00c050000002e04004240d0740300c21452100c0851685840c00d404484c0c18087d406200c83d440d031404414244400900d0002c00c482c04d036401c000d0184100d110003800c48442c0c910480114205000c1805582001c3c0d11003070703000380310382c0c448210308101e80c96400040d10164010516039020318001c0c00303981401e01401000700c0741035a86084d2113102d04000f0780140d40310a04002e0410300304032190103251007508075a041520900543d101180c0f4001100e8079640402c070840c2c0c03c0781c200110290092894803565111041c2c00d440075080302c184200144005d00c440400780c1c1e1200c503450110003651000d01466000d60b5001c04043c1e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 767548543 1250 767547293 767547307
    0x20907050d231b0d02092e080c0a02030a3e0d180b070f080a08071e0e01030b0301020d1b0e091b03071e091a040f170c060d02 55
    0x5140548020301d21030000380351030203440c003d0981005035010b5030f00300400580c40f81400400300e400c2c040424140c3c840441c0e1455081c3d07922180c5060801300c83c0c400d995071309160ba0348c2c170b900c41d079240700c0c211600005900c108501c0c1e240740e1103010160141d610b00c484440541c021500c0400c0c0c0e24000c00304c0c8200c80b81806001e030100342d504000000940c049800c0144190194002404141d43c1a200d400c069500019819081050303030b4040201d19a4424803580e00c40d004460000c0c8071400c01c4401d000440c85c211120711491440c0c2030120144113455641e9035009800c100110007074900340d48c1d602c0d0199002c5c0908181c0c840c141c00b0b4140d40914422a440948002e0040140481d00400d0910700401d0f00c0d0703091240e4402031250201410311b80105056903900d40345021181b4120352010401200131580780c030000d80e43d0083c041800c440c2d807070040498000d144040c1020a1059105001e800000f061041001300c5060b40452158183c40060b0380c0c0d4080c1c24400b0036030b50360140034104140c6074006054 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 767549793 1250 767548543 767548601
    0x8031b070317130201051b0c060403050a0303050105061606200a03020309070501050f030a02030c0909070809010506040c1b060603080c0a0303150f030f110a0b1b06070c020907050d 79
    0x6940c001500f2595003140009500060080e00c00c248010901510035007401d0100c070003c1025048041e4003804680d81c0c2e41e80ea042842d1907c4190400703e00080c109000080c00e840c055080d29a0108000040c40c41c8000036079408009040b500c510300c503801c0e0581406419480c2c0c01c800740000840c2131300d000d41c0c0e0b0310b031041d101c82c200300c815040a4180141072100034403426034642a02da006252140041e5070382c07a2249002035034083e03034003960b030311054440401400c50750108003180580c0c5a030b0004e21164030303040100f00a65120808000004103401c2200f8410741d0902903080940340035540004056440381c6603140160b101241d164503d80c00076070303100c0800d5410b22990502c044a85100908a41804104074008a2904c0003a180b40d81030300d81081800030440346101d1000e0020124205a42d032407a400c1030325080f107000300c60551807490000c0c1903203401294040c484d2103140c1d10105a00d010354200702000313402410000c01c1140a12035a084920244a1682c90442e40041510a05080209 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 767551043 1250 767549793 767549837
    0x3070302011b08180c061c0c0815060a0c12110616050a11031c06051c02060307030c020f0a05030316020c220207050106290408030708031b0703 63
    0x8058810004040312070010baa018101e0784c0c115024082c0f03100311a2990070441d103490321000390103900007000034401c200c1c519a140501c988800b82c98081c4010b58019000f51243e11003115486000306002c000d06c0014a8540000c1c00241d40d10700780301c01c1902c5161914400140089000c40c085203081004544034142080b40f298001615030445042c5c13501400000d2044c0655200a010312140300c0c111031511a05100b42c486800c08142c0301d6414a0052010102400340c030704c100b81c06007000c181c011a10758804200311170700e80d0f005445189151035003a8103c0080c2501002041140542980d4078020f65090180d44150383c0500d00640d1a8101032a07090f60b02e118144804042d5809a17000d08650b442d04502d4420080700c4840034200641003009040103440f95030310007022946044004602000052a1200d00001c01d2007280d00e01902e4000310100c9101c0c0f4011203459600c14408103000034620b000965001401606840090081010455041d045080c003240400d0f01551040e024100c4a08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 767552293 1250 767551043 767551061
    0x90d0b0a05040b180d080402130905060a060807080c062d040603050c0c0d08040c0b0406260603030d0b0f0409030e01030c02010b13020705030f0423030601180e0a080307020307030201 80
    0x1310079400a04019041c1d6607850118202024002c2c1d40000605565034420002420b91058009103d0013069240071900c1700411506007100070303d130070408180c540c4001201d00595404e080100034200f00c410802c01ca03900022140e0240100700e070f0780b0700c0d083d100f201100c0024a11b0026460740780c0c0d040981c05015224020000c2c040f00c1410320411080380f50004040a1234481810700203019216410314400885468000408000000500151a079405101d4290003241040522000e800740002140001000d0320802d902d58814445520041081d5005c050030610017801260b00e29801e40105090320000001038000c20084143d081a40d44c01d401403180d084001d100130041e0030030203c00103010a0510411030042c0b64042901001c01c0400c1080701c0d00707020718251081e1269600c080441e10a82d1018020301e014501d600161410304001543da130503514403450140b41e41d00507c040700001c00c00d0104c0107610380b0501c0104004171310440002c5000e0300b001d42c040c69856616050103829510700c15 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 767553543 1250 767552293 767552311
    0x207050d110d0804080307060c031503021314090705120f07211a0a1a01080c0a0c060504080a090b04080d32031f120204021308060f0f07110a08090d0b0a05040b 70
    0xa8007800d80c09014050300cbd420b480c1e04032465030100d080224920000c01c5920b00c1100008451001d200381c0b5240003507168100c49003128166411400012515101c1400d482010a00e501407201444200410008140d0078402000b807061242c0043e1036515180400b2546540305400342014403283c01014090b811010400c01105c1d00c403e805040020541200241458515500892a0b240c070b0f80c031a61600000301e820510a01a5041600704030f006c2c0da2001c240307440070680c1c0900028984803440255402c95044a004c4c11300c050b1a114141c9150490740c0390042e001000da12602d15403000c100d000d122207078072601655180e2400c070a1002140743d0203026580005003d550420220001c403040c0c42c1e0040e4151000342c4c0303031422017403109510b412541110500d0301402d410401d030344c041c0d46510792164005070070007040341d00c030500184c440003e03c00640300b094004044200106030407030000c0c03111243c090602245201143c44000481c0750075500301c00180e4940d42807105005000e51f000d13410010340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 767554793 1250 767553543 767553551
    0x30f0501060c0b01210605010b12130c060e060417070317071e050708060c03091603120c05101514190315060e090a050601060207050d110d0804080307060c03 69
    0x181d210860100300501c1000300750300790545035032010340d40c00d1800d420041e4801b04c203101d6961100c0e030400181c0c01445c0c6019000c0e03c40380008803040010020f2185260300410052041410032a044403115044014160490b07010400007071100c04040c0c2d110b4459074101c002c0d0040d1030035407820340207802d5543c59070620020184070301d0001c5141610b0000d00d6262614132802c0b000031501c0c1550801c070745070340001210b0003524104a40d50008400441c40380c0080340650b10306071a030034807000a400c1c050001502c09400c002c9641c0940340141c6d921401d05006038200d0305851040e460743d000741c42d400d4a4020100c40e020400b000300180028642c43e800f00201d80e005025040c0b60322590042000b0711014019020807001c40c0e29103e1194064800350030074440a80062904000e0595a5203142100f150f1390322071a4000101103201161300c5007600d4005201c030f0780c29145038440740229008140740d683e21194a030404800143d80300000e00040031404d0142d03464026a080860444032001c814405050030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 767556043 1250 767554793 767554817
    0xb1309020a0f0b0d02090a17160e01060e010804051c050c1005090303061306120c150e030d051806030a0509060f191a1e0307050f061801050d0903030f050106 69
    0x3e450a0300d403402d9030010010307180c5101d500080e608070059440420303d100303143c500b0070213150b0110300000b1002260300d8540e1030503030b0703910745146046007441200700144505500035269842100e0140c0c0060060086694400880c0009481c400c10951042c01003400003d40042c080000c0c821400003128800e0300304200d14201e42c900341c49200c0205014424003411841100e03070a0391364080b802401440307040428140140c506180e000246001d0034080540403807500c80c005105005c00381c031030880a0060403603010000c105480e16000100b0701c0800340315161f040002c9071030f070070081c0d88200c3c00b800d000b00d03c40c104003c0717450030940050711a251408180042201c01e00d48506010804503001c00001888060308460030f00c1141580d80442c3e21681030440800400a60308c000c0000301402c40a0b41c28055455042003400003019001c0c58005030b00f4040d0343e14003e020040140841c1060418514008490400340700310b65416074204c0100c0d60f56a030303d020200301445814051300c070504007a104000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 767557293 1250 767556043 767556059
    0x21504110906060c010230060f040b03100504210906050708030711030304050c030c03030a0e0f010c021002101103190f1506080405060708061509040b1309020a0f 71
    0x20040e858024650301001c5060b5480780800c644580d8030b980021902e404c0d00d4110071001d141d2581e041188104855580000703c1d024035403460103800001d003007402c0412001c05002c09051400c0400d03a0500940072a41455603860007031900c1503101e048000164296400e28441803c6420300b00300420548540900851350090100c80300e0a80280669450740e84a140c129000c040119045002d400003100b0b101c10014002000d12105070210203882d108010401807545e28007134005210b00040703401001d12024103014000541401041c50001c3c91444143c001ca0f1401c2c010300d40010040e4000500c070712061b040c0d03101d0030740ac05245005062950400078018240003525058180e5202c0c1c0d944503070b112010700365100350703401c401e0341c1419105590343d8580503042800849081d51036000d01c42c0040c400314850b0b8a690b21402c0b00070015003401c204946029400e4200a0760b250704a999050941e10702e5881c8401420051910200491020a184180006a41260300c01022117a03404020b1200d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 767558543 1250 767557293 767557313
    0x3030609151a0405010f050c0c0a08100c1e120912050309011a0907050a02070f0b070c09150308031306090809010314041104090206070204141006110a08300601021504 73
    0x3a03078619140c0d80308d41c7c84061050400009090003540b0074107a20307000910314004135180c00400c222202c200150909030000340c0d00d0120500e00034200e10b140118606101b07010703020702c81c0c1001d00c41e00300141d0045581d0360400c80d00c1c099511403012a10220401510b86824010594072000011401ca0141c07060700215806040140c02d5005000740410340e140c130030b40700b0840d810003060b1025010502d29030b01c1135403403841e5102e49819a294004900003160b601c0032400f5034041080343e4101c0c0359400d403541e1180152500080c101e0040d41241d00520408901c2d54001c00600500800485945012400001d0b040f030700d0307004400404040100401000c5440f0b400760f009040410750f008110044984000341c000d11070000029485803400300100d010b294030007403040c0310781441d0b180b03081b4541d01c4075000d0300c20510b540800032895000310b041c1030000300d602000e010114081c0300b01c20718070417240a400f0717000340f10002c42e80d510a0000b01013007480c2d030341005480300208022140068905054840b0b94003c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 767559793 1250 767558543 767558567
    0x140303070b060d060912031d0604080703051308100e011806150e0c31140121292134060302120a0903030609151a040501 53
    0x300240740005000390700d41c200c038003c010b60301c01c50801c1050460314118088071420048200007915001400c0004041c019440000d403920b18018030707941e0341da6038984921f940b180100704c04010082c82401c1801c41e05000c0e14025100040140443c140c0b940d81039800c40314414903901d130076030510b0702c8043d07880c0c03c05d08280c14286d04501e0200e08001d0084070020a400705a2189105d84103070410040071244c0c400c003401c4075442c2514500d983c0354070003140c11440744000078040e00319070703544204128054040700b01118012042c18510ba40c078242d0545000055015001e0002941c0c640c1e43d041e58807000c00301e020803200410901050b001481c01d0115045d2603043c20591001c0204000030410300000b00440748456110b00d4070382207060041b003281409107072450943c1e01e0401c4100c4020034240c3c020300a4480114880100b008241e03a01c0e0001d4010309902c07201503040c107aa404000c21145003a004064804495010911040e4941070301041c4c01f007046400c07011210000c3c402400160380c80300d440050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 767561043 1250 767559793 767559803
    0x50d03061202012712021c050322050a080f12040807050609040b1906081302010f1b020901260c01080c031b030a05010303030b01030507080601051b030a08090714030307 74
    0xc1d44c100c04d801d03507410820386544d140e05602480d00066030090620000d01c000d8400c0d179a803444210b0840b02224240c1c14407074003c0181c1c0041c81018000c424000181115400d00b880840100d9030742d001140c4050303010740000c0c2c0039411841d0801480c070010881d0f0504507015044a03403405c2e10b40015075841d0744850180034410440000c1f030304c9055445802c40038400000905200e1f8506104451280c0343c14940701313900110b80b0000000b03035041ca010f1041c140640d010b0319030000b1900d84100c2185c0781d1104408100c010400301c80300c040981c641011081c0600950007441c02000742030b0704e0115402a06210030031840c1d000d11018200e42e43e00400c0950880c8002002988a458201c00d01e20100da40c40d66040400801102300164901c0580040b8101ca000e600e0410110b510440110300f9100e04035044c002107641d05000c1803440d40310f07500410140d845e080000a4002070002c010703065a1000c2c6a5100160b0801e050251011080c48008020007102009110fa4500d00d40032035107a01070501c020341 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 767562293 1250 767561043 767561057
    0x6150f010c030302090a1401020609030f071401180305040609123212040905060d0c050f010e0a14100810050118050310092901090203090307140a050d0306120201 71
    0x4100b500940545040090082216420a8882420f01098000002240d006105203804102e1b00c800100403036818041804c0303041d01c2c0c4107098a880e5544400d00050000943d03950180038048840070107034410140c4240e6505954618050b0014021080703074000241d41d10b103103040702c00000c1480c8400120111b2909409e900041e141054510f0f680d8803280700711017401032140c01e05800305000018000d42e807080004104030f0300c3e0101071124814060600030800b0400b081c0a03c0340d86001030001c0c01a01052400342ea40340381ca580406d80041403640030700001080100c00811038a0700031001448501035180403012460b00800500040603648140c5042c09000d0016440c508001103440000d03000c094119102ca011700c0203d44001d002d1108140e030400140010956821600c0484024028040e01e00c0366550342880c000000a41c0b025241d15a184410072010000070054000160640030718809800440e01078145039007001a040103000c00c0515001c0305008501c20401040c00701602860300368 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 767563543 1250 767562293 767562317
    0x509130603170301091b020c010e0a0504150510050f03010306180b270c010e01030f140906010303080601032702010908010f0b12010203090303180106121406150f01 72
    0x100003840160400380004201c010490700d400c01d8500214101e401017241084402c1c102d0311682540480314120a006030071102c1120f40310340c400c0056007002100203066403c00d5075541e00007001c44040da88041046801d900d002c00581c0b4011080e07400d0301185091140c07824400c1040d070030292105000003400346644100701b24074951030902145131035510840049450030008030142c0c0321544451035554500c10400d0f56a11a000880c09003141101a1101c000201e00b0030015409800e0b4180c0800d02d00f0341c0c0c0c90b880c0d400c032a40090824007500b8460040c28007541542001014008020031b41c6040c9403c016240b402c02900c4001c0c02c01000c80c0702004020480d80784012691001e8030b50000c503141d800e00f01302c2400e035212607100954401040b21030207a0125049121401c1c3d000c102c4001c03038240c10600000d00304031a03080020007610100e03800000d80030344030300758056080c0347c488082d544480a20b440c1721070b00000b00100c41e0001300c0003025148191110001484101202001ca410003070148010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 767564793 1250 767563543 767563579
    0x2d01060902070f0b070f0f0f0516030e1801150806010c020306010e150d08030105060a1115060103060b0306030618071d04020301110a08010902090a12030804140c010509 74
    0x11401901100c8019959030049040550706510308610954200d0100c0c0c0200e54024001d03207521349089066112007180030814801607130320020450048050201c02c00c00d0350b011042e070740d03107100e0103501c240c4a0b0b2804086100038414019007001740020300d41c2202d001030151300301c444018140c03039a0b2807400c022181d4403440101ca0700403102400039054030800001007014010440e14030310503100b1201c540031a220b260200004074180800280c104481080140070a0404000802e04800c060500880e40114213030320600d0712405182d1100c2c448901000c0c003c196a040c0620740090104500c0e203401d5041c00d200003a00c4071409403250381140504444c80a00c03410500c0303a00c00030030001c00e00650001090005004020003103400324031a52030103404070401d0341544241c45100c0400e41d1601210f81c204000403000394021007080d517100c1701041e00090940300e01d142d20412988281d407000d45c0da04091400e5601000c150380214200d0b0011190b5144a9a0140c15210480b5080321041d030b0420080e503207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 767566043 1250 767564793 767564801
    0x31912090b030411030f0c01050405151c0218010c0819030b060a020a1106040303020a082206030902190b1e0c1507090509160810050a0603060e092d01 66
    0x1140c0d07a004410807044c803c03040c0c51440d00c00010740564000319840c6072519100c088112060340030520a11040c022400d14480030b08044810f1040c0615020381040c90f11b1f100d0403650800b00314545c00060000705c1c80540d20113150b0901e03084c205200d2040b41a40d409039503000d00a0690301da00c4007103102c01109842a004001c1c10381d0050037265480e41c9800300292074100b50700c1b0580c0c980e00611400c1120741000d5080300c0031250568041d290400440d900d0b20101d6111001c3c3c12004101e041d40c0b80074503105811184000c01070b540f00081c00e600c991050090782605002424504c2c00b1070081004001c601000311441c038075041042c10500c020800d02c0780da0030b00907048083e4051040404d403846407002e503400c203070042110343c948401c0e540e99001000b01190080310b2000c0e0030842401568441409107103d29007212602e0134802015440700041113140c0740c9580481c00194444104008040182d26283e4000c20403202a19a030b50701e11403000040503c010031640100c0030a0250791001c002940 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 767567293 1250 767566043 767566049
    0x1030f061e1e150503120a3e06010605030c0912060a0c09080316080a17070210060b030112110d06050a050a0e0109050d0e010c240b03191209 62
    0x1d41008070000c0300c1405420120700d9841011038030726040c1c42da0310a5059919034000c54800400a203a0300d03941460000303050300030040380801e000a81c80300440081c1080c2083c405400007001c1e0707802c1d490b01300a5240390200030b1501040d50350091801400000d034001e04495100045404196540709890301040d07020b03d15404550072402900240110002140c2110b0100309c06a13a980354078980b00c3c1240c6858dc030500b06200d01ca1000078105500207031000700a890281500e00342030404a4403140a041051f00c00ca5002c00183c2042041040900e0075109a202604002d00c0d05070035523060000c1c0510300307a0400305c090214001211a100b581d5580010b41e5805a8000703001d2006061503503115011741825246030300c180d800c111540b0400b80c414800d64555642107030040400c801c03100800d5a801d2070000305103041003040c2100358007240c40300d0f080c40c1101e00c44403503190344084400c2210b01110b4481600718400e410801c04502e040300d501c00c005000c99041180c070f20480e211700320180c486841a038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 767568543 1250 767567293 767567351
    0xf0d0c09112206230702091003061d060c0c060402090a110a090303020c180609040203100c020a060c0c02100809101a0301050c0a140702040b03150a06080601030f06 72
    0x41d01210b448801025480460740300b0b881c3e1046001400031800c403801801c052440711000284400000b62501b010165044108204008817040c4caa444180c2503844100880e0303c081c05c046008c5480720010006160302004881e9003500705040018561348401300500301a02c103020001c049007561009034000704501149102d1030356103400c5008040c103481d90f1440213030058080c440216039541002403106003020204001d5008503a5810200180130704050000c1c0e0300b40c801d10002c5664425036200b50035040f05140c004041030704040c0790810035600990249000c02c600c00c03002c100103031501c1c20b005c0941c40b910b041c0403007140d46d590191494101c0b9032240d07900c16410309205844403200303d410b42d800e01005900030720555440032400807003841402c00010001380540400444400c00d807004d450000e10092000c9500c43c14807000030300d0301d015000c0c03a03180e00c515681800141e60981c410b85004004141c0504001c1d803640e25240c41203040c40001500c181e8491030f0701009903c03800e44a40c03400c0904 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 767569793 1250 767568543 767568577
    0x604020d06030c080c031c0f030e0f010626070b0304050309090c03010305060a0e0c01050c07080d0513150c0305090d14071e120f0215070803060f0d0c0911 68
    0xd082a50b1407942c680704e01c0076980580c0410300744c1d60901141c0e5175614201c0c0340c1c080c080500c0b82403045582441410075070080555481001c0040c0d00148050701d840d507001e4002184613070400309007001501c01180c005140c03104411080c54100c05c08203e0904075545e9000315a101c0d91281030180c110700c10102d0301548a003503101001015602480036505030307405503085501035512200300f8021218800443c10700e40c0e02282c200c0200b176200e00010721200c0032003015941c50540c0c80316801c2c0340c200c1d901110400b281021500c01c04911030700c0103450013002034001c2901c4042075000301a014225601e0090100140090700c9201ca48690a8580381240d0004408480d086007140c00f03501c82c1460f00440e1448500010f403040c0202541ca1450309031001c0c4008080220081d540c0e459560343d002c08101d0304100b50700405440b00c8464809480c3c2070340503401c4990369180050410182180646903140b245620000d20008100e44150030800d1301c00c414800981d00c20300341b00178016406019110050000c031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 767571043 1250 767569793 767569799
    0x240106081008120a08220210030f05090105070e06030c030a050a09021002061603061d15120109030e01032711030f15010518150a051005090a09021801080604020d06 72
    0x440e0740107160071884e540c0e482c01580c441c040b03030540341990410070000c4511510030340340151400100e03e03880004a0b0800140e40580007459106840040f01d10084a0b5502e400b0031400b140c2000381070180c000c045850178598901041085000c1c0005062600d109a84100040d82042d00380d201c07650450300109003c0204140008c029940c0e40221021801c840c940009424218002e026000584080001c07014000d85800705001106000a00d4110385039652244414981c17901140001028000800480c900c0b041d41405402002d044403c2c5041501d40208000340d0101c084210748943e002450000807900c40742071203030a00340b0803c21294103020319101400010b000142d00c106403400040b640c4d20b07a0382e0341d10410030301c12444a403040380701041000040750a2141c21010928101c02130190314001d4841000c00c1d03158403685101000b1940c0028041d02a16080031440028010030509629000a441d00c0710b00d12462441c8603810702a50381c0104031996140d805840706c41901031010045555 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 767572293 1250 767571043 767571073
    0x411120607030605060a0504060507051e07090c0504050108010611100f0e0106051206160306080d0c03110109050309040b04090206071b120b0105100e09100602240106081008 76
    0xa026a80000403d2400f0000200341c1000310035100035038015107419040c10b1503c0e40c140c605501c001c20840d42d500034820212400403200c10f040c01c030101908010200c26041c0904d4208507941c403c10002444014001040280c0c3d118410034192074107403400c0c9002240d102d4840d0320b425030340c0361a50003140c2000e0640b210a50317144c1c0300300803003501c1000a000c61a0f940080c000300d02074240901080d60401400640c2d4104010741e5103101030554500005d00950781c1a0031401c0c4100300401ba00000c41c0180302c03200b4558401d03001040c0010b0f10703008211101290344d031143c0d03034440c0890f000e014980300d80b01c450559a655110609164020b0f00c0150b441180d4a00516101d407003840c7c2116641c21060041002110b41e000100d6031039010342104243e03401d11040080301c40d00e80d4005401c06c20360135400b8036591102d004d09402644003142d20170f421801c0c124003a00b010081d128800e82c240541151022070038403603040038111503660600c035a19491b030486840c0901000c0c3c1241d05107100e401055000b02c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 767573543 1250 767572293 767572303
    0x10203120703020310210618080c030a4122030b0112080d0203040602091008060a05060a090312111f050606160b0a021603090e0604110a08041112 64
    0xb001c070200b520f811a128201020408904c10100301e48207414050400051f031241d001d000c8442c45d135403044520300540c1d96034941c181c1c0070b018540d2346a0030218910702090b40100c103408101c3d80c1103507240f01d0f00e0403000c03112003480c0c518079041e00101001000d02d41a45a6001100ca030220a03403107145009524400b01c07107001003903100484100306480000500c801e46003410b5003400d54040c04262502d101ea45804011790006401030f18566820000002603a032011701300b4108840c0c1d078646c8060303442c02104211a114169110a0244608100300308410754071081e0302042d41c1c0d12990307040f600014000101c5060880c8540500c50344100d0003040003602101c81000ca030007003e0441070240b5a1600144140c9010f8074000c02d50131001c01840b200040c40000d100d5034001d81d01000141411b10382e1100212149103004141c0208120710003d001100009504607448032065405000e80c00610303a0055031881100070340000c212001d000310382044030510922003160030003081018003000c1404401d80714 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 767574793 1250 767573543 767573551
    0x4030e01110a0c171c0c020a0e070315061412040f080412051b42091201020a050307270b1b1f0f0e0706031d06061e0102031207030203 59
    0x4007030340c151900400d030b20024811701c2c4180d402d690031000702e43d22842910302555038001207901c510f4004001c1100c00c40c80c1c00180c462840d0fa41c005c40d0b10b010f540321a09488030580c00c680300300f040420132a9000e901c60012292405d440c1c07640c001590f03a82e81800801484040401400c446002900042e01200c40002407000c5000d04240e482c941124421050114002041d098000d54044444201880002a01d00384030151300420038100b00b007040c0d8140d24120310300b01c0890038600030445107450706003030382d60b1005952888002c52402c004914003600c1404001e11800403c07401520490000c8500701c0154010071051400000709520b80d072220585400c0000d400c400621484a020640800000c040d100054005150503d04402e00d0614026103001d821700580e60f40c8880021080d03950820801000700421360300010404503210b8038100a411b4004000c031554844428003100382c0d07035122050070306e00c0c520031007244110718040143c0c1540130766803040c00303019404007c200300d0729090b03001103110b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 767576043 1250 767574793 767574809
    0xf020604090c09080106050109050603071e052d0702060c0a120914010e010914030c1503090601050d0c0501122418060308030c030c040e07090f090e030304030e01110a0c 74
    0x83c0d498068003801c8031880c2c428a070014807004402c00182c2014401160014080e141c0704001c00030b1140c81c40100307072014003008006040050b614000d9100c50030460010003070040c411002c00713003600501900b40200c1728040d11034400050740344003146041100c034500383c1d84403480050004000750041d00019282c0b18811020b02e400034644011340c451078202c81141c505031034040d005c90a2180e00d1000d941c12345c5100c0d0305407007100c448500030340c3c80d01030102071500c200c032050343da80c90300d140154101007040e44928080d0000d902d500d0300003502c40c034a0000340d40080c40c0001b10b0700300c00e0072940040c050500f8114003600c451001010320740b407010003010648954050054100380d1209070350341141d255210251100d0410700c0820b40c01180d5000840d040001144c6060525868100c2405d60600548895000c215a02c030100480400c406510f4000c1030041c2c000c001125814002d55201d2000800017402c205074a8840c240310380c0503441540c580d00c0f80c2422120101d02130b1801702e541d00464010301c44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 767577293 1250 767576043 767576057
    0xa02030f070305040b0f100b0d02030901060e0118020a0203070f080c01061e06080c0f03070801080c0102011515090f0909020117070c02100201241d0906060d0f020604090c 75
    0x5a002e40941070207180e1082403040c1e55540c0341546200501d0245c0000d0358a64140d00001e109225000580541600e00da030040e42c2e410090201c81c00c40741c0d2640403c45460441d00100200c400491582c40e842c5145140544d6420300340d20301b2410362003001c9005102000000c402c0c13042c460014050141c0c1403030349008204141d100e001c4802e504041c0101040b00f0242c2c101d0622402e071284202540006100c0442e5080103d68903852003144c00071201b03440041c500c81d00400c48094104400224048280000c1003010038100100a0281280c060117641907104080e400009101d04822001000402420600240c4070884000a0a2015070070ba000501c80c44c001d00400c03d0800195009038510303110741c0744d03541080d42071058400c51184150b0541d580c0d0502c403140442d5480a059406896610701e154050034001090980605403850140f82c24200e8100709020030b000425a42015049034a140d5403543c030301d80399a03441d0822030000d4100c40041400506001560455600d0b40c0d01610b0b420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 767578543 1250 767577293 767577301
    0xe100219030902152505061014210f0106060f0207061403151906020a12031407140903070308070c0819031409270a02040f05040e07030b0a02030f 64
    0x5042c1d40301d80c40069808014110040c9442d4040401801d1a003003035003400002c4003080c00c01c072a60700c00c074050a4501c1d170001010042403c82c2030100c030020700000481122540c04100100d000300480603940c15000d01906101e08180c0d070200806071040c20260001d12a864076400014210440d858139400541f00d41040403855900a8240c06043ea5502300c1c0f541c15036440300640070400148980c250740200043c1c030706140e10403251259202524443d0002d01807410707a4505491111140107142d41018540340b0302c0742e054050b020003203802240d10310b0828854003048440380b085104480f00d203070341407103107600010810199070301a009840c012081c004c2442d69501c840790701e55a0310101c140d5034501c1540c2503c0043d006060440010144c0306005040c864410041803680005035400f00c4a041c010b01c440140015640002e50f010b018204c0950400345080390810764010540206407040392992200280d80b1001c20aa10003540c112001a0380e605103803560340001e50094606a1038505000001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 767579793 1250 767578543 767578547
    0x50d060f1104030f06050619030b0402090f131b05030106090518460809090c1905031e010b0406120218060d0f0f1a120307030507060e100219 62
    0xe02c0490b44c1001007040c0078010b6035100001414002c040a500400c03030000d019810b0300709038070040a54454810184075050a0040000c442401802410524600e000b00816240f07010345d10817200e03600840103590401110b504070031800d0240c02158040d0b01c0c04500040710126034201c01d00400c100406003420390301c1c2074042d03030b143c01000324411014060380360392603608504c410040006140080c0c0000340b20110500041c03201c2107030030050b601c64401040c0300800f807825152281d00903051101c89440d002e4495082c032550418000240c0500c0f0020001400010040a03040241c000c601800350b40756850f420501da180d0094001c0500050a011403080464040d108071040c0c03040d100c102d032000074074078800c0094581c4698654002140c65200212800c006400741c900c5003080e05d030010400b01c00321308840c00c40c81080c030201441a50041c1400c0b0411002000b15602540c00d86049030b03449210b414018003500b4050031001e200d1041e40c0c107640d084a100c1c1c1c042c02d0340c00c1401a43d41c0d1101d55083d41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 767581043 1250 767579793 767579797
    0x510061106040f15060302060f0a020c01171b0c01020703020a140610140d05072d0510030b0a120b010e0705090f0103020901030908040e090f06130b0a06050d060f11 72
    0x1c020f2440900c10680303400314000b12104192101004008210140c0740d5010641c50707040045079101c0103401103400d03801c154040c8504420b0395400c2c41d01d6440040d005040701400300001d4040248403152035101110300130048112042280144001d540e5070ba8240340003503980d1210113040e5000c1c81b86000440030220042a01d9001e0204002040d50207800d0036000d039102d4194150f916805001e4280030b10000d0340a000d400c000740404640d43e03120380341d2907114140412008e6110008912107101c180000d070740d00d0803030001c001020302d8000b40c2411540c0c00b003184d41e281c2d0703080540e0307240c0144100740030080d55408a50580d03500400d1441c1e15125084103039002d0007083c42c0c082d8002040007004001703510a074081c121001c8145004110100786855580041e84507401c510300c1070305103030104550950200110a12180180c004004c280f80401c0740f240300c100c11410041c14017030a000402c81600140d04150080c0400400c0709801303007164940035004158000640b080b042c1000c034142450004402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 767582293 1250 767581043 767581051
    0x31e01083009041802040903031a0a0501051804060509041214030610111c0315050a0612050618010b2d090918030a1106010b07020607020918010510061106 68
    0x480c0350304040e003840401000d401c1300c85071a80038041424107000581c0c0d0380d025030030b6200c0c0070ba00d0005130500a1000c4030401c5d4401c032102d900942c5075550070402170360300000321841c54400900c0d11221420031000036002d040b00e03621003a44143c082703090000b0f000c41c1d500044c000b070101d51134000004a07010711a00b000d0108440c20703a8481c07003500100003018081c0f800c0d000d4180c034060542e0b01d10705010986204500721013407400c2c00a56a6066604000c070311149010143c201203aaa0048520b445002042c4040380e2a25000c0c00ba1a04013081d100c2e25400c9060401d1820380c000404150384070310311001d8540040354a003106004072382c0c28460012800040000e60295140b64900c1c101654040c42820640540b40260310b00c007800a0702c090398000d002500c07858040d5900c0880c040407100444c0c0c81c0c01c10680000c180ca02040103a0401650740e4021905215410b8034220442c1d900c076008405aa0b03804000c5001e203500f0715081000c0d05100c5201740e42919010f403942410b1200490200766a040c0840b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 767583543 1250 767582293 767582383
    0xb040b03090d140d020903120c010b0f091b07031e03050402182401020f010603080304020111010c0206130321050603100209030a11150a030f06080a050c06031e0108 72
    0x4641c1e41c00502e17400504d80d014000e8100c0e11800c904410141c040e07401180c030388071181d650345d208003e0b9241104810401a500b03c424800900303254002c003691210040300d940c1c0c3c42d400004c9207002c16010f034158140700100c0c1041440703000340496001d4040d2004960483c4510030a20380890004030020301280102d0403e0031091075070003c01c00d01600e80086441450542c41401d0101002d11000d01848000c0c41c41003411b00d032a0f0030184005007805080d800d0b80601641011007080109034005a615400105400079003241030403801d080d9140c1101a4030821104404c0e0072090340d2102075005640903100070380444404052202c1070004038040d109016900d03402c85603001d400f00da0002e0802001503402042003c9219100c085a900d95000c0038018010039215012554a03642c1449a0402003865a01402801040e540e8050b251b1104144039885480d0200118001d072540180328240782c2d4070031010f940b0070358440c001c403903403428014100e0700201c1c0341e44030b012010f028503a03000d21074074400303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 767584793 1250 767583543 767583547
    0xe070801240230030c04050405060303191b06020c01061502010e060112060b06030f09060106090b030403120f09080408010605010509400c030b060c030409020d02040b040b03090d14 79
    0x140101c90f501440c10545802800025400742076441d00f5001075008811501009503140c1c501001e21040d100014204c0c3d219410600900c548142c40080685c014109450240401135100d0105900105181c00c043c020300e1020403000e915031015400041030300c1e1507240841e0354005025049083e20502105840c5a801080040101e40c4010580c0604284500c0d40400c189424201050154008940c1111480401001e0048821003808014007400c45031070030307021140c100441c1076994071000d00010208108041041601c0b481540051511610204144994055400d044200341c2140c040c00c465546040b0b40040c1a60040c412103180400241c02c224184485d1701ea80347d2186c0c0d2402c11204e411000c00c0541c04001c0c1d81c0b040710183c906264900080d05408050001c080720400030352140214403c0280200301c06001058604a607031290015136215030808583c40070b40150740c8110030310f00c00817030045000d000c0400030b076110700401c000300ca01403a00940101c440d1b2816071141400303c141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 767586043 1250 767584793 767584813
    0x41104060f0506160501020309240103020a06052d0c10020313030f1112040e0a0b0306130f140f16030804050f01181707060c02090a0c090e0708012402 66
    0x110070080c000110300c3c2c0d109004c42070f016840d29400e9a10441d02c0407480c0d04040c100301580381c04031072441e245403d0100681d105606503800301d041101c00e4010b0344217200d00442c1d484d521035020b041c101907008400c1c416000d601e000801c034185640110318006010300992020740c0c0d005a175032080d40d12808c00315241c031000082c81e84013603642840240d040810008401441c44001000704500c03108212a200915070f601c0c54480104035024001c1c00592400c0d0810100071141d9400042107a0000101c103005090b480580c5080c1a442001150042030440c0581d07018202c0f50000c0744002d42e840741541070342c1611a244254844412490000518640052001b40000c1c148600301c1d20842c081810f280324162002c902140c124903690b404001d40d0a401481205140000d1100b03c0c000c02d454105048542850390011307002d210010080390b21190b03260940708000b881000c41100900d03800703043d241d50342480c81c801052f01c0d200f401024141c0d0300a51030405111921694200050f000c1c1e4050301200b09 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 767587293 1250 767586043 767586049
    0xa0b0d0b07110f15150103050402030a060515040501031b050a080627010516020f0a021f0c140304060801060c08070b07050912060405060a062115090605041104060f05 73
    0x3800d4402d4248542c14511081e810308001820f01401301500fa0484e0f440c2065441c00c400180082c201d04042c2010705000050310001540103940b940300e103000c107030303641c828080624415215510369446414180000705000c011b040c20214080300c41d0081c40c1d5076031513000740041200584504041c0c0e83c00003000443d2105040643c4a0b550b210040d4074800390480c011283c2524001c0d59220b43d1402c0070300320410010703010800d01607150800f4002d07011202040d0002082c1c1ca000d00203003a442140c02d05c1442d0078600c50b41241100560040b00d500e143c06c94466441e50b203411501a80011862190000ca107003401500440401a444040c440c58004555110401001d001c0c0001060200c144607001d442d546810504800d807240400a01052416040c01850308402800b540c000e41d00d0a0b070305210440d4101c3c00d4116541c0081c0b040004030480d03240c0301c1da051581c03400c031b42640e9207812402e50412225401c218095030284a000c401199104c0030032088036214824882a200d02400800c07440c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 767588543 1250 767587293 767587307
    0x2181603020c150906070815030a02041a04051e0105060343050d0f0e0322090203040609110405100501030c02100608150c0a0203040b090616030201050a0b0d0b07 71
    0xa401c050559100300610540c116001800395507160b950b40017802000b01ba254011460799224440c8000c1d02260441c1a000c07035182c0d84404406801191102e85040c160304044074000758201000e4030402580c0740c00e51041212142c0d10130400003107207210300000f603589001001c1d01d000e42c0385400e20350b500300d0402442d00d146451b070802e400900c0d0b035041501030740a1300c41561000300a000c0e480c3c440d030304e4030101ca1040807101d03101d00c2c460100d4601005407101d06c400100b03607910701005004503940003d4031040f80d0001b01040c1c0c414400c4500000c1004200300c0160820040580304810341070649110030100001d81c0c0048445036044443c0c600d0810580d80b2a03080081c900701c80c0d00584007907a06116640003690140d8009017030603070001e0b447c51407031500050001e03800303035a2409907030800d003100100a440340f00e1072055028031040480c7c6540d442e902c0c2c800f03c459052403c100b0006144407890080c2c081d00701241c1204c1b800d4a1314815203424107000e821004402d03802040140240c0d50400196100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 767589793 1250 767588543 767588557
    0x317041509030e0102241810050403030603030906211a190806070809070e1902120702060a1a06160209090f0607030207211101180218160302 62
    0x6003254480ea0340d0564429045024000c1d541ca02112414100181c50171030b1000d100b45200c04405200ca05154010042d103800c460040c40442515014404a511b00b2450007134030346406203000c1c148010160943d00001c1241c0c0b00340c03112070545d50b9951040c2d65113090480ca2000e000100f80341d1701396007940c1b544404401c0441003401d4030511517000110304200c400d00302240d00d8000554041c030480c03104001c0d01c0e80c8480c0c02d2070403800c40d2420400740c680700c045074850b8101140f80314010482401d842200c6d02e04207480d2260454440010200700500085d095501ca0051300030341002c250240c01600031081d900c0300c0001c1003910012143d0030b0001a0b8070460820540310280080000140d0311030350000c1c050080034004003071480800004606140b80035000005140c41048190000b943c0568078002c0340168089003402d40b040300d1416106030000d4000350485504e4010201e446c0489a241c0680441c000d030f40003145c840c60301d10b90303110240702900c03583d400b14500b03224035080c107200b82c00504032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 767591043 1250 767589793 767589803
    0x60503100b0613350a0f0c1a0a03110a05090906060412150c0509010801050409020d052401080309091603020d0606050d0c03050115050a200607020f0604031704 70
    0x604824031041d40e4a07a90780d500b00c00700150700300000d071340050154a5003862414111030700007545244000300f2551951030030f200600c0c8021424040c81407080000000703000344994000344005a01c1440803186a070702c8600c0c00c0f400309240140d900420b0348040b0036100f080f4010340b50185002d03460402c00001c0d0b14010051584048100404604016110144030f8080c0c4214501070b9a03500e11944001030f0f6803e07142132010800c0c240840805a81d000100c5411203605590002d06071a450001c1041d0744444074000e000741c800e0f45140b0034018440c42900e00c2444001c02e1074000351740c0fa524035503246d00c01c1402e0075500541710400716614041c1040c42e020f54003181d0034014540030040c404001a104075911003004210301003038a18500e42a8000c242d06404e140c64204901e40c101300301e40081d41c1c1d1202100e41080310118007080d845000b400740f42a6070b66000200c00303424001c15000e540d522800c4a03404018040c030455144401000100580a03d070b00d1707203130a0307006001c42ca581d17940e00c2c00050054038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 767592293 1250 767591043 767591047
    0xf0c010e0d170a020a031103071716060e06061002060609070f0207170a02040b04021611041425050301030b010905060105071b0519030b0115032a12060503100b06 71
    0xb0403044100101012189a006131010101a04001c1c0c81c0e1500760200b0710682e002044000009000c008156114990024a0648031201000405840c3c100400c1c0140140c0c03410340a000602400a0050301c203a00c200c450035281030410204a8a03183c1c00e5841640060403034010441c01c60080d13052400c2c0c60318901c122903c1941d9001c00b61446c1030004502071054000c005001c1c19800e060141c51007280007600c0c25890304d00d00c025800d202d80e070008400f802c040c229803090816a521178003d450301e8064450201410305102000c09440613000740c150580743ca250703400f801001e004805580c1240d07000b6002280c00da02e000c01c2c503000382100a0285041010070804400051110201005521340e100c480710311103800d0005100c1058054540e00500001c0d00300200000340e507440380c6a064989400344400d5a14190300700b0f8000c2d10702140e848112151a076031541c0c0c840180302050704075840c41d03681c21801c414145d662200300c075a0740c0505034268010341e42e0702484d00d0300c41d00186001d10014210074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 767593543 1250 767592293 767592323
    0x30608060621060106170705070305070201080c130b09040c0e10030e1606020303090c12101505040204030f0515010e06060915220b03010b0702130608100506030f0c010e0d 75
    0x74100f40098100d41c01180b0b40d44c07900b0483d5040f4200c001c2c0d1000c03041c10024034000d150b450140c0b0342e00465000030304009102d400102170410380410b844424600c107060b114240d81f5501044044e070000030f10f45001e00d28010000018030321400743c000702c0340005012514107203c8200100c0140060b4680360100b40704030980114182100720705580200301c1a40695103a0910102c4a4244003000302814840c407802c3c01304504101012038a155509aa40320005002107216441c0044000550105510620104000082c424a0301440c02000d100d4400d0710018074410118801110b070a0007182c0343e024800d00081d03940d040c000c00802410034000c100d61500d6181b1450b101e510f600019103038915400b90744000e800d0010345031081001d841310007101d600719810180d00c03c0306070042c5c100103442000b1030000030582c01200c1e40890040d045500c207581030f03181c4442d01c3d0300203094203403143c0e40a4030400f0321915004102207214030152105a46510b90103040d00e08001204400081c1628410310544481d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 767594793 1250 767593543 767593609
    0x51513051e010e01110d23120f0106080408030414030c0a21050c0c01032403082809030201030f0212041a0c0a090909060204030807030c0209070306080606 68
    0x908500001c0040700c0d10301c51040700062140200d00215418411180d1a5502a500c0402c206c8803010491070404a92005005a010510315a070710065441c2d40016424031404c0008886038401c001c281c00c90301c0a030360380301c2d41124040c9040760f02a0112405002040019036540044600b1802480c1140e0412000c181c3c4141070010501040381c1648405001000010400510807503814150034201c3c24054485400d58940d101c500045040590390382c0c1c0d92035102c558880c20301445802001d017030801074903407921441c240d000b0701d01e040a401249150310303005240e003c0000408219541d6a0b1480382c55680154058080500f1a450464007881207100c14001034586a2056009030350700c0b84542c021285242e91094050700d28218080104503090906070455800c40468041100c001801ca82605000000380215000142000e0000540c0030078154803a0030300c203002c0d0084a030104903403101c2000382e048541900c02d0440c15000800003450368078016440d1031519078410113128a13045901c0603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 767596043 1250 767594793 767594809
    0x6010b0a0815090a0905100e2d0d0e01031a1008180f0303041506030302190201050708180a0f0f1412120705061e0103140705030f01060303030e030405151305 69
    0x1845130010303605c1c0c9414041c001d00f0001e01580034022001040321801008446480326455021340c0540070300c10028020040c540000d0a41c0036803140d054802c03031034440700010040c15080c0314081c00217050031f80100c11032400d55540c100203003004084030014510100e058030640d40090038501400e090200c0d655000c0340621201c03e607034030400040c551364a805e24200f0301e00380b001160b0030354443c502201400000d130001440f01000e50340120500c4140b8141c40101c6061140841c000e12034000468800c0909200e442e2840908004441180b80e031500d440c81482015058410364003443c5c04100c08201e1b000c0342402e0b0400c60f40c40606030030610006119070600d042c4000e00c0c030512f8071400003104030501071305014090300404800c0621088461000c51702e03a140f941030202620188815827180c800001c2000701030004c00e005015034026906075500a4000c000a02c025000305e42088410240854080200c90a42300c1c02020319040200011942d030160300b10328051050b20424030008078480d0b4541c20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 767597293 1250 767596043 767596051
    0x312060302280f030c030305031305100c020606030a0b07180b070320011a0609060714030408070806060303040317121014040504020d140a0b090706090806010b0a081509 74
    0x41c09545801011000c40326002c002d5200301400320890005000040c0309402e800212a010314103d0346039215244003a090031681000100944240004d90501010b2a040306010481c540c0989a541d503d034018151142e10401d0018102140440080d02090051101c3c0d0401c1c40d0200041030519124036041d929580402002d90128a10800607000c0c00001380080f006254130034028026090700f45480780c410198281b0a40c4503610100e4603130761380d4440384c007a00c042c281c0101090b2180032944040507200e0b8028010680b15026043c0f000c1401c03c400907500c1c2c0100b6010f4000e510b007500c4d64864065807800300409009030602082400002c041160b50540506940c50f0480e84103840d20400c081340e07080c80441d00d4021405d013801c00c009a929450f4410055400010881c0c44462a0120034240700610000412000c045c0082c48006000000e20800f0781d075a035254900c2c0790f5114141786603030702e00034881c20408900420210603414810089140c00454040070b48010750400c02c001044508111 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 767598543 1250 767597293 767597329
    0xc090501031e05091c110a020d0602090310060303122013030c06030509010b100e010809010f0c050711240d020f0f0706060608100e04110913061a0d0312060302 70
    0x114030170940f40c00e002d28071031149040d05010300114005200fa5845100c01c0b9030280c0b02d010fa400b100000d0103055011201d8a08004003520700c440070305441c00c00103101a000c150000740d40340d00e60080480070740c411500c680f1858481441d80c00034850410f1203070b500031602c8034448a42103000000044160800c00050480c0703480124051030301a8005003100e03d000c400c039105031145094a1404c6401c0440b01c0300c801c50a107032520f11544e402c4511030240c803240d490800301500d0301010303860b4280d015000d030125500c00e028110842a4420802241e0080355a01e80e1080041c05809082d0b04481002050301d11195503025082900355241504030350807048441307542a00000701e07142081740f14030582e000340460f0700b05040641050140e04d003101c94203000b9400c46200d440b010905000c544a110001c1d0070000f407015019217400d824004002000c010f040382c4c41030808040100002e0360314801c01c1e500c5000307003060b5000c03102d41d00c085541490115090090307540c1e4020200c09a110340d00d04143d482211 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 767599793 1250 767598543 767598553
    0x31014030a11180f1b0403030509090720030a0311090102062206090804090c032c010204030f030c0b0106050412030e1c0506220f060b060f040f03060e010c090501031e0509 75
    0x94004e5185d02c05401011101c1d20008000c103000080d00702007522200c1c202521707070000710ba0b20500c090fa0782c8400c8a0884442c0380103000c050154840020052090b510156014402041010783c99a440d014071803046025810035000110342301d4280034100d4003c064001e03598116034081d00c0e0202299100c03542a6010407001909001004031402085a501268a420854240700245d200700500811010302c504182040d01100059030940540d80550b400100c50a504103413860b0140a09254a5049a0380035501c030000507030500490a5408551400030005001d204691741214403040004d240c95000468420f4a0012910181c0c1c201d002032040d0001c040a040141d640480803c4442110a818101d1a04d003c0014081d8110624150303020030081000c02c0c50000160050046900700b00c203004000c240003032000882c1c4502d008490054504008911403080550300342c0b800d801c1000c020501c05c54041010703500c2540400201815451240f88600358820200c041d51019242c1e00306070744c00303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 767601043 1250 767599793 767599801
    0x1f0231052701060c0209061c020603060607060f1b080708130c030b090a021315030204020d11031006030c0905090f09010e030705010203040507171011040b0f031014030a11180f 77
    0x41854101d0f0007e00440359042901c0c0740842c040103207100f0f128024042e400c0800411020f8035600103496120b98814000d01c0009000400c000046c010380c0141c0900030740040442060304d02540a075805845544d642150650303030b000c02c2c5440744110390700440d03011007503110000102c0c0f5808c0800380281c0c00100500001e49040c01007000e0801070f09004000c1c1ca10740450a10800303120707000101103d5040d2409a240c10019903604001c9c40c20003090f5083c1100001088818205a03d00506a48081d00c04000d00700e030700d41044654140324007440d60001001c02c04204c4002d0005e0310f0344e60040b50100003149005030348441a056421802017210580c0d008024401003250510055020b40403c4c141c28000511101140307035208107480e01040d1040d40c824411880490510850700a44000500680e0303c501d1407020080c0783d8000c6500441c4000645030102d88030b003841401d0355151400034020220a82c058888070751484440c0b010700d500210b890180b13500400a289654411a100c0c29903182900e4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 767602293 1250 767601043 767601049
    0x6080705491109060a120906091b0e0c04030206070611040b071421130803030712200a1b0204050f060907021204030b091f0231052701060c02 62
    0x55103212420003a01c00740f000d854281c6035801aa154207034140303404800584151421402014110800342480e0b0420340090b0a0201c0000080d44401d6211081c8020b07030764034034100d4800c0c00300360388503074000b442000100701500e00070024203000c40c020500014000240c4400b0104c0307078015840a10300e40c20200f0f40600740f15040708594400020540507000704483c140720700588101b401c10100e4030135004034800d03a12032030017500d1501070301754181102c1d42da00300324401901d214091007104403080d04140280040d0f031100c49a10104e500700d100e5040c242404103030240da59030014107401c85480c1c0f4014110700541e44d0340c014213000e0b40c0c030b00f84c2051460a046080c4003c150380100814107640c84140425204011107007100e084a03003046641000d0344541102d5420002c142c182180d2000480591048140c4203600400102e140c404213480016045140c5040c02c0382450344108546108007010010782c00c0c8007041202e014103c5600200b060b80d0f03030740414007110083e00883d0001d209107a084045013 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 767603543 1250 767602293 767602301
    0x40f080c1e07090203010503030306040203190c020c1216030b1503120904060509040f0f02010903050a050601090b0d02211c050904060e06031f0e15040c0608070549 72
    0x481c000074190315540c11f10303000c41d940e4070028208600540d070000014510020300005505510305d2010203101c50032030400d000355111540100c40b8428bc0c2103888009001500140c00300a585180c0d0f01c2110b00d51458031010908000100300030502480464441060394003840419078950800700b000d500c400310345080c40111565600318501400d200e00c03d00021519903a0002e25031680107494070131071301e41c41c80106da2802803603000070101d20587c100c400030071402250241c1618a44901040302000f5041080148451444081c0d048900c0313444a4180c01d00300040d81c062400c00e6411619003200400306584100395051003100010004600c0203074a282c503008030f90080541a500c0742035420094002901d840c0308044c001920b0700e4a1800141a09054000c50001a600e100b44e0710081005100c0e0112010211411a2a884c1102000c00d8450141145a003e40d10795520b0030704010702982d002143d0342d100090b99401071200c92041c000072001c038035030910307030059110740b42c0d50102080242010f80d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 767604793 1250 767603543 767603549
    0xb030a0e070602070b07082a0c040227030c06070302060906060102010c0f0e18131a0c041211090103061a121b0409060c11061e040f080c1e07 62
    0xd6045504100011030b400a480b03410303102c20301150746d924030301d0b450300550503c0381c0c84004815900944411821020250000d03041c1144081a0382d0401400001c00c0228410302d802c10540805291100707180744810203015100314409800c0311038998002e800166141c00c0400c007200140c0c0722004114101005105640c2c21600c20300003071280d82000740025140d1042c001d0301d18100301c120740140101d59114000000e0760715920382001070b41e080c6105c3c0c04541c8540240c0c142c0e42d120b5580151400240c1249035180b15168140000341020700b07000078400c08210040e020340f41c0b0340710300401041a50722405001c1c02507108000010745c4035112021000c5140c0480726091280340d94941490540300c011a9215001c002080d6007140d0540032400240207201080c4094625403804545100407030308000102d58123a062422076066036603240f040e10b00c07424041c8080b071300e0341c00c20300c0490f00081c100d40f48101f040b0300c1160741a0078507405541043c90411000c00012140719001c040e640b810106000032409 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 767606043 1250 767604793 767604821
    0x7050708061e01060e012f161e0302041112070921150b010302160c031703010b121803070b070f111c0c0203030f0301060905091608070909060b030a 65
    0x1903250a0015000c000040000c0b81881490390512100111800c43d001102440000a42844142c44003450341d03400309148580304252612000304480002c1080110745049d05114180302500b5642400042c2c00c05400c2c1201421081c01641074004021071441e104208540c0c41944071440c14041204c12810040a0044804049030182c040350111182420300c01c1d14400104a205810700124000c0c803c2d101d01c1e200092456141d1030400800120103401c03a0f0044514035440c0c0038442c04103405200031301c515a5291401c0001141c3d035200800d007542d0081003403503000f41600b00d0188441c1103510840d012103001009a080100c0e9941100c1100040c1185182a10082e1382c803040956a401c114101d040c19104600c10411002c1d00c500e03021500c1a50250950792140d8058a0b1800960800e0045101003450700d84045075500345001510705c03030305511010407511316003c0826070b04c008014050108010004801040031003140c040d00000b00321500b01d1030380d84d10b4540f810b030080720011844511 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 767607293 1250 767606043 767606101
    0x32a120921100522061b0503070207030605060a03020603160908010b0a060c1b0e2d01090b120f0304051507030818071a0a020d020a080a0c06020705070806 68
    0xc0c00c21030025060b6810710007204006029200d210712011800d4141c04010020880000c0d00020030a040c0c2100c1c0c0207458000c04280301c401c004c90162014001203490000591060f40e08101058031604140e410403000742c00352007040c0d240d40210f00e07264001c07502d000d451207000c0101d0503160b5100381040300402c20320300200210071460300041c4031098544110000c00502c103e901050003101a04c0b00078070242400a03400c1d041da030710380c03a58495100300c032090b04074219545007031002c02d450b009807851a124210003005507070903c800c00000384402407c02d40c010402410500750500308100508a03103020b6002961214601010010251052441c81c1521001400740d50006600b002d0140e0300300307810b8210708031b42040850a03246000b126500c40052980820461009602c2400090510354455030030b4a242807032102d400d0740d46800242000340348410401c80022a14070031080c080c9094800c1e01d01514001c0e603521228507005040d0040c400f50341080007885000034154032480c80c000001c04010f4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 767608543 1250 767607293 767607349
    0x18030a110606151b150a0905190210080a0e16140d08090418050a120f020102180108091e0c0405060907020604020402071505040c03030f0908032a1209 66
    0x400c0c0e40903111a00b0503058214070680d03200d0b1307000e1040341038240aa00040643d884c1840100001d00f0005138181c0311409880e4140c64030000c0d48030a040d54a40140c400d00121811800c03c9079801c0c001008018190341d5007807104400c2006207e60706840c44c0f104003c0d810241400d100071a2003100c1d0181e01c0c8612040d4000c030002031141820b0b11000750040b00d00041038a40354060045d82a4003420040c40c2c0c0c09425801001c000404c0010f4010420750ba41e211008000402c1c00e90803440f52031005028052411000022588229045644a40b055040d204a1515500c2d811001c4001205c2c05500c0e40243c8024005410a4414a540f052003143c2540d110704020384080d49500018001034001c980001d03d803024090702d541c0044030011002c1f4104840e20340b5040001000c0d8182c041200001d00c004020140036108101e0308040d01c68240c081c6140c202c80c110000c0303174010f45c0000c0d00c08001c08000701c0d900c40141808030b0070b2011825082d45550f0381c024001c00070085641d08034800881c6a00710720f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 767609793 1250 767608543 767608579
    0xa050f0c030a021203070b09010c09050402030c0d0b01020c120312150105032a030a0b0301050a0b151309021b0c0109150305060a0e150a0503150f18030a110606 70
    0x6642c8960140c1c4d03141c0804009888050a5124002c0094000403140050080d28041580b05501c800c2007a92900030560712101007000340d100c26580070400e490180141c00448915510212002e081401100c58001c05600030405600801d980403525400208a140c00c0c0f0090350140366100704800781c200480302d0f107240081e00f10701020f4003680000b45a03000d0b4080004410725082ea491a0145803140c60740b600070220000f6040c1c81d01018025400c1070f01141c60344216004001c90701c0001002040380401515a03001282c07c03c0b8541014040d01d450000f807110482e00c0100403202200352000c04403080010828030f03000050f4041410009050340810404801c1034010044850350f19010a0b82d07210500069100708280d0403001d000044c1005200400605038461008030200340c59003140655940d0800d521844604012041c0102002c0065080300f0309144550b4890ba0030074041340350408007003100e803554000c00c2502c4003061861492015885040211a40c0108120b445030341040e00b00e507807 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 767611043 1250 767609793 767609803
    0x50604030c1a0403050a0c03230c0402070203121b120a08060d0809030111041d0f01050d0c0801050c0a080108210a110604060b1002031905160803090a050f0c03 70
    0x542c2030203050300e0310055400c95040c0c111001076800c241160440501401e01500da085c171481300300d618200e01142e401500c21000341c50000442440068a1840d00440501001e5031144004030b0389800384400d0141410b03540740c040c0502c08103034401c0003000b20000c2203551801d0751f828051001ca010620540b61b21a6015082c5a803001040d500155004c03458601503026000c2c181500783d155007458110b030a06400032015208444400d258405c04144680d1141e01110065901403c641d903503000501c510300740f0450100c0e4251086131000d444599030445a0300715002a0788a4001550025603200c0c00765104c242c550240c0440805440d0804200512074101840100c0300040c7c2d203c04500c0c030000303501450014405064000586006141034a4404001d0002e4881345200704540c03034920003280d10000c2034440d0800303000c0340c0c3c00c404d030309928043e07510390490b881090040c1d0382d00b501180010321480146020b241080002d0180c001c251520030704200d42c0c841640e9007070703002032220b0714035540004e1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 767612293 1250 767611043 767611049
    0x3100e0714091e100305070306050a180902120303070f0e01090509040f03020f12071b05180c1306020c0301050a050910090507080f0d030e072d240801050604030c 71
    0xa07010019680c900910300f14202c8052805078840c0c0c03040c3c0070044258264000621401c4640d80800090b82c81d01c0401844400300e008105518025421400d240701c840e40c03280d00c450740001c0c00501c0b00d5007001481442e642c000c5400380d00251140941441071508940c01e080d00b06d6003401d1040000b418903000c205540760082c00541402802e03000d0300241402840807080d21402003080d5040b0030045101220a03a01040c03048400403d00301c9441d0510340e40c0c510744820f071003000b445070707242c9428251140b0b1804005025918002c1d0108440c088020040040710010002900605600f028041c100f6084a80080c54032207030508250070814006008115080d2070300800e200010a4460b0b410010718201c1542c0001e20380d0300c1001d40c0c10201d82400200d15202c890710b503509204542c00140e10646940040c443d0004a408540301040c26120301841c1041c4085805100c031115655080c40e19043d08119000c0c11681294800c08a80315a10403e13083c050501513400916041c919603601d0f0f14802248 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 767613543 1250 767612293 767612299
    0x120703030b043606020a0f080603060702030a11190606090b0a0302060f0f1b0a050d020f06060f01020a1505011707150e0d0506090312060405101707050603100e071409 73
    0x210032002c2c8600d101d00c2c1c0d00f01c09a00403004644501d050341c80505502d0f50f1409840202e5009400142e00780740000d403032403048200380d0155003400700c8640162126070280500c401e00380941064014041c400c142c1e46042c47e8000c2c1720100c0d00341c0c80c200020084681c8245d40901440a108090015803100390481c0c220031150300c4090750702c4541141100b442d02801856103d510700c5030b2010041184000754a40c54140101e09a038042140500d081e07944003910124200a904901d00061003403620300c01c280c03008401801513594007000c665a1a01c4055001c0952080941d1400180300c07043c40780320300c031007003d11040080000d641000c165441d80c4404522810800c48803a1200c0d089407104504401c0e95a07103c4120b80c101c0c1808000b49881303030844000f0000503000400002c03a10716013805000d00601d0403400e8100c0711410030766244268419240b125407940715421000442c0c0e280c1750300071071056181607190319038107041000d41401c0d4035014255004001250700450500140441212001c0c0011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 767614793 1250 767613543 767613611
    0x2030619060b0c060702120c0a020613170f0f150f09010b030a0f020301051e0a15080a030e0405070327020a0e0901050714030907030b1503120703030b04 67
    0x168100c030000d840260003080b0340b604080340d4002590400039505006206540a8070070800c244040b0050700d008000720651154000c032140009420518011b02c094071102041005103504c880d4880304c540a95a00000d1a0b031200c011060400c5c1c09000000c0000c80e803801034202c201e416490248410006000d510054180c007007ca100c0c40b00950048100310000b8098408118050408451a04002e00b003a4080e500b40000600b001c505818084801802641d5400e5181c581e6103c01d00180301d445a40300141700c0c08000824451800c00082080c20320036070f01c600080d25084c1c00e010549002034400400d040c28004a140301d0254481d2003640c0315610341420040d00e1160000030000005680305503503c20a86085c004607000c1900020b1040c501510391200d80b102c02d00b9100810710040710000f009420008043c0002070351950126008041c40d1030030320b035002a100001e0300f0315280500750204010002803113030406405000c0c0c04521042140e00300003a2416014440000c0480c0e1030006d034590f60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 767616043 1250 767614793 767614831
    0x6230a121119020706111c1d0312040513050601020304030305070317040b0405010c02060f0c07020d1502031e01062001180602090f06460201020901110a020306 70
    0x482429600c444100b540000300c000c0b40554082e440b0b0050307003c0d0000240340b01c2c0308500c01d0354000130f03644143c800c1d8107128651440c07101002c40704800010013500e000c1555546080750760754208150005078806403481652207203801c040106100440c007490401508280401001d42c3e004400e0341c0032a901400c2003035841400745000c4484030b00b5003850301d100c00444401d0205100c0007032400351041d44100700030814412819400d980e03c4008942c101640c4400d407000030000720312200909507103407000d08122641d800e9a0b8464903034401e42108844201e6022041014090f80d55200303040c001501e030b8081e1030f15410300800030511480710a443d0601d20000140c1f0303010700401d40c070582000c020102c12500103500c5140c01401b80d84842c040b07903c05c40c0c030080d510300ca070324005080780e60781c20031061003414080c158140a44c1c031303090301044000410164005220910b140c01c82a0341c02c6803659000503039800080002514427542c01a1180d500c0d8800d811210041c3c40000d09942c1100540350055803140c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 767617293 1250 767616043 767616071
    0x207050d020d14030d0203070f02010b092706010e07080f0c09010f051c0609051e150307180603120903020117150d031220040902030a0f02030106230a12 67
    0xd001480410a03200000b207604c1d10703170b04981c007030340c080c02c042d0b69001d0500c034910780c089003a40c0700711488551010003040840c1048601100c0148010142003c003015449180400c90800400745d004480b232110040c1000f03841644000802d5104482c0d01e10400b180c21b00b4000008540910030314036050100f2014180542030045003a542441512494050980c0c500007182001c0c01443c49804a81e03410000400c074605402400c540c58074040c1000c2008070b079501e03182c2000c8456110b507402c0c1c050041c01e0020a000ba2141c1c043d81040810000210b2100e240d884d002e0041403c8140c200e00300110302c00240f0060ba8044c07005441006d0080301c910450b00d5849500c1194035060312200e60101080302020f04260300000c8000d07581c48084030801c481045001c0820b90b0107040258100340b403e0810081c45007006645c003454000e620254000303495100900400200e03842070f0409000b0954400302010809550314030040840000744907581000303130140300980400200a075030035034551280150a0110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 767618543 1250 767617293 767617313
    0x2070b0703090f03031205150f060f07020d1a07050406080606370801052e0201090c090e0d0f0906030b031c03021e0910080402130905010507030b010207050d020d 71
    0x4880c01c0ca005512130b55900d00508001c840c00300180096017400000707080b03828101e95413001c0344406445e90031001d001c6402c0154a03442028401c08101d018000712000d07844a885051403213116260780000712500aa0b0245d200e0401804401003060410092010990260b80540c000c0b005031605034032542d1603c2c40d9940d64040510300342c9052458031078400c4444038401d0342003201800d52a14070b440d98881c01804564481b01c030300000c0c103028000c88424420341a5035024440010743c4000507500d03e0ba81e0b45c0814003002c81d44803443c0aa05c50561089802003032120140c041880d007801300070b9040d100c1e4090141c0c8064031810040c140d030342c2d03400c0505440a00400884a40e4401070b1401245894000381c000d40040000486041e010f0039000e040c42c40c50380c116500040010300c02c280b0022282c83c1202d8844008100b280c010b000402c41611202c076074001d0410981c442c90011691746041c110007001c840c0d101000743d0440d0b201d807600b00019180c4541194a41e5010399940c001d007516400d102d0a01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 767619793 1250 767618543 767618549
    0x4051305060d06021b063606010b130819170313020405070207031a010608070503040c030b0a0f0c0f0806010e0901032604060c0b1006080a090203070b040609051f02070b070309 77
    0x503004030800c0201d0946090503210002c680052401f100c4406060010815140c810501c03146900010040c00007807941405442036541d00030420420a48402d0f59509000038007139607030035150031754200004101043c2144005a036031186180c2c01c5207000c00a080803a01340ea00c2c0a400740e503482001c10742192090010078040d50300507000d50154030b00c60080c004449c20921070180082d141c10080341d24140b181c42103900603038004002090399419500c4480300000080c0c5800719403039484025070711000e40c5001f41c0640500c0c07600e0380c600d0640818009000e00c40000c04c4281040340c650494140c036504c0401e5281035a0704100034020b010150303911302d1700c42d0002d101d40c049032110110740092101d03403211013080c0d5948203100088050700c0b480340d0541c1200c0140150004179844030001044441258800308000340001d00310b440007960741445020950141c1c120310000703040e0030021310813070410068902525001080c0601ca40b5503040c0300070340307880300c034056801c2804002070282c00b0f041c0301e03207282006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 767621043 1250 767619793 767619847
    0x30a02100210020a050d0605090603030f0a030617011b02010203090d050715090c030c0e060f0913080c0705010e030708071e03051212131101200d02010204051305060d0602 75
    0x1440000d054045d03d180c02007048405070904184010505082c020031050047e41c0240095040212214810581e500300c48074201c105a91820000f5814003c0c2c46101c0c0300402c0100001b401c03102d10f030380c948801307000c4000c2c41d029a03004200f03015031503100041c1c40b21952003d160590f11030002e846c050100d10030f0b5000005690342062b00000c10300c8241440c900449205000b1a401c6030f5030340000c1d283e00d140403503842d540322100070710105c12402c0010245600040304100d82450520341c2c0d5513030f007050f0418411074a0740d074000003041c421541c100c03060400c100c4088009000240c5801070103a0f403106207000749807030303103903a440c850b6a050342c3c200314080034540c404243c0d540c11001d0401401305400034042c10602000e8031012412000e4250b2040d04540e41051341c0da10114119001502c2450600c5c0c0c10412908200702c1680c00340c2003d1000403240c0d0450b60003d60364625140810442d400c04054080c0641d241505006150f5a00c10510f504d15a01c0300c03000da2946407000d81d0913821032049451000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 767622293 1250 767621043 767621047
    0x905060c03090a030c320d05030715020a030b06071203020c0a060c0e0906010509030a0b0915090c1801082107151e09030818010b030f03040504050f06030a0210021002 73
    0xc00120118501c1030703810f006e420304807035010030241c0f4070940b00c06095000911104c1d8280030481c20000c0c40350480380d00803003ca91414105d5610f6241403d0000301801030564003284844401c0d034940151081104200c4216040c40c042d40c0303550380f00c04005440034041c5980001d841d688000c0c1400158000d90b0005420412000111030142c0058100071f8014425000da500040a660160080d9404d1060147c02010713a0307280c99a405c40000c0c2c0141140b0750754883c4943c03503803200741c00a100034810300d92003003e0700710b056980c1d041c0007007001c0600c405410703104e1540c01404030540004807845905100100410901721651503d0420704c14054043e00c1041070b082a0070154983d038112009401c5200e4404a01300c5805650408a9103102d034002c00094190010a000542201d003007604400d039400002084680d400019141c24a0814401c03502c0d000460104031070700d083c0c400c2c280e00c11082e90810095160070700000380c0340d90400d64003e204803a4410344410651007000400141010920b00b19 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 767623543 1250 767622293 767622299
    0x108060f0a0b070b0f0f0c090d02044107120c0c020901030b0f1501050406051e160501050a06060912150c0306051e01090605070f0b0703090201021504030905060c03090a 74
    0x10344c80c0c141120701c2100303008410702041d40c0400703032401c80303101710030301c1100c28108560030040000c0744041001c240c1c1d00513280d04070700e400186084c01c000544468912001d0f090000c1400714004643e000f224485040080301c02c100c61580c01030545c0c0d8991503903000c0010034482c01d403400d0383c1d2041c0450300650086440b04c00401002024422036001d42d070084a842000d5445243c61078a00354130880450000f0700900c0108940350051024241000c0c5104e008605180320380182407013600102041e030750b840c02684450090007000c0c45810340291a03104248280303803c00784094102d07a454450001c140f0300f081c07801030600c82a04002c0d020b05060540920000082080003809820203000b01c900c90160700c0482c0031080f40c42000030000a0b070684034510307041e280450588090f04610010b44a0700c079000d4480002546440400d8850540e544000480103150f0000924101814049202e110b8000342408040381d0800802401c41c0c2007218500c1c2d0714001c14480c541180143c000164111b2441c01003c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 767624793 1250 767623543 767623553
    0xc0905070e0d171b01240605090406080307030e13050907030210030e07030b07020f24040503040f060c2d080307021603150e1b0103020d0608031308070f03020108060f0a0b07 76
    0xc14411074401c00901c0711602411a0b441070303446c0b64910070249640808200051030140001d021745038001800040c509644001d0141540d2100304210002100340381c01e01428070f0f00f00398804140b00802010030252609464031a5200c60a010191060282c3d054500360a803103500551040c1c0c2c03e070415102d9040d500e1030120b1079010b041e203045016008603464141d5052000030903070020140400d1001c50030715507000c03010301050060b20a03106800100800706200b451080001c004004030b40d1000c0d0318009500740711011404880407a19000b94000c0220101172100480c2e8880c6504005019941c2d21040000c4c2c4c40e02c200440e039021140b89220000050040349401e40f4050b29400b10140904688140d499441d058800c0b020000f014228241c03d105520076409010b41d50042e090000c4c1c801e46810f600c62441e0412032820301c00510a000510400c40207010440003044402c02c000541e13400c50b0300191001c2030050150f4040d000b4001107200d20340d80c20807590010404c050780c05640e100c4500780 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 767625899 1106 767624793 767624827
    0x102030c0715140c0a0b1801090c08060604050709030b0a110301080309041d0a1403071217150a05040f0b030601080106030c0905070e0d17 61
    0x14014040d041000010050b2000d000c1c102958603140d14018402c1008000f0f8204041c000d0100c0d01e82d442001070000350165000c1c5c0382008a5032285103020a5000400050056608020b010014070125101d01026078035010107071a65941d840c2c0520007500c809840c00000540101c40030000300d90b1081e40365400000300c01d00070541000d52441344075290020b0300980d00d01c0c4c000040641d820b01d00f41c4625a00d20408664281c0001030003170496484041104016080c108404004078410a051088866031640306080c00c05505071044010807148402681c0f1550140300000308101d0070139040c5001003180018040307140c0e50f0400d8244800341114901041402d91514a100b20079541402074501800701f10300005000c62a50406080d03440c8198800010140b505090100e00c0b540801c0f26004404142c960740e1a80c03801c1c0c5421404506010700c1c08014000100e4140e0001d010215 = true := by decide +kernel

theorem cover : BRFrame.Cov 767446043 767625899 := by
  have h0 := BRFrame.cov_init 767446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 767446043 ≤ n) (h2 : n < 767625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
