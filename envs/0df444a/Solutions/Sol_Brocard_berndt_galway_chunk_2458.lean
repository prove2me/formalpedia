-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2458
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:46:46.140316+00:00
-- url     : https://prove2.me/submissions/bc0d39bc-8fae-493e-8135-ea5f1afebc1d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 441906474 ≤ n < 442086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 441907724 1250 441906474 441906497
    0x302070b0706061d07090f180e1c03020415020705061204020d080304030504360b012d11031819080307060609050c16060b0103150f0501021e060601 65
    0x1140c2d0016402801d10520707030b41200c81986013808091400311520000315105030400941c0d11510ba00d003a044500a0010002114400c5441c0c00644066035031901603201e55481d054075000400c240d00c10800c6c0b951030047c3c4d5940f034440d076107500e491483d562400b03540100c101081603444c1d80b01110090b1101e281c003282d9942e2a0710000e00920074249014114001c08801c100c20190824000c000303a07034103501060258400c00b05100700304a200340c00c500e4080304094001c10004501d401c01d210410050416900201c08640c4c061804076148560395100c030100440d0b41d1b40503412620303255034071941e00061450984003803410002c59908007091409400d000d1880e035050540c10059070090300743e0070203699070b40c0c2d050f060080142c0043d0140ca62010320707010108580709074080c21100c10042241610500034100e03200c03c03000740050014981490340f100405600400f1a044903001f4002072030080440e02e080c50002498100f401d561030360baa8004850780300c21070600044056100100b407070720800c0340c207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 441908974 1250 441907724 441907733
    0x70f030506180a0f05010228020c040c020708010c20011808030403030b040c0518030d021b0d0501090f0501060501080c031812180f040c0806090406060806010f0504050a090302070b07 80
    0x3103000c0003034904c200d00c1d0b40080070000190000c04444100c0c100050700d80060028806124603d004448003503800405c03090b0702811320750040e429503000350060701c405030340d5106150f00b9228004041000030f41c115070250782c50800b602140d0700c5294884000c01c170b42e5100c03030b520070342404440360003501d201000700000701098442d400445956002800a11001040000240050300081100c01080340b642c500b600c1c41e401c000a460900d4052039009240007400c2140c050312400d6072440712500000d02800440105009004440b0902d11410240c00b0782d0f00380c0c4c00d207a402c44905822483c100100003007445110b0254505894019804c4180415105c50750a00d40745000840d0260881d108000f00b04400c0071110319064594848050b0b40c01a205581501000215110490550007041000c4003203010ba08060b21107503031180c030076580025015201d0301d806103861026070041c41c5840c2800360600c4030381003e001e90ba8200d80b01810512600740300c2c0d54044e45607008c83c020140c0341c50300407450704240b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 441910224 1250 441908974 441908983
    0x2130b071103100e0d0c0b0a02070228080f06100303030b01030b120c042409050705040e09010204060e061204080d0b090108010c0813031d01091706040203070f03050618 74
    0x10307001001c071210b0b19040c154442c054807030006401642e02074110400c4c4c80710701418600d1661a40700707170180d5041e51035030740e690b00940001e230301682c0060115240921a82560300185641038103c0c800c407100d1460540c419182c40c0c40000824074540041040c00003007c4507100301c0c0240c942c9400c02140c8000100012001000c1072070300d559120111100c0b6014180c0c001c582d454101e403042d01c0c01d02075206040304801403102d0510141c58070780345000c0100000e50003540700d0f5800130305920303140d8500b83d5640340c00300412005590035009a5030001d420446240c0060508100c407200723554440c14040b40c040130000009000704081c10307200d00010942288a09540848007a20300207041e1001941c4031a80d00e070080c60148060030200709280d0201c1e03125003048580d0582c240c4d0513650011203920040001c9900c4c0c140800241c14002a20408500c0301d0040ea0030410060300c1c50024003443c64039004040c034003502688403100291070481d0074001b095000c2416a8440150b80d022420301c5100640c55240 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 441911474 1250 441910224 441910253
    0x160602060c0a050d090c0e010906030b0a11040503031207090f08030703030f0e03070b06240f090105070807060b0307153501120b0a0c05090913170d0f02130b07 70
    0x1a586801640400c0013100c0c0c10900c140c403031041861f8404e0b031300c0321041c0d011a842400058246480100040c101c429681c00c040c10f85040c8202c600e092940d681d022a145400600c24084815031110400c54003541c00f44689000385880d65030310807864504a0110303200d128401001e4101622440e018001040641184401e0320b1020b00726952010749040c014004a4259212440764003084460f8100b500c030100f00c1380008000c2e0502520340810784940400a82c000b80d1140d040c02818030080c070100c2d01c11806810325601810300883c4400c480004c02d400c7c00f1082e040724502c0500c0030f001c5921260300400c1907400401c07280d911300b1100315a0710303522510307100e0501c04941810b0706030000c00c069007464a009000e9206da00240240c0d2101c100d01030627105500b6103000010400d000c025003600c0d000b010150403815802235681d24491584901c04651a021800881c0400020791401000c50300d01c207151101c96409000c504184282080a00c44030a500c0740700915500800c000b82400b0030100003181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 441912724 1250 441911474 441911497
    0x2702010e04063b04050706050703030b0a0f2111040e030409061401090b04050108070f0309020d030206060f040207050a02090601050d0612020f03010903091a0906120603160602060c0a05 81
    0x300840a5801e80c00b14050390840c043c01e400c01200c0280a07502440b102e03901403030f03201000d8094141001d800311420f4000c01c3c429820192103642c400038a481d052601400b92603440c0d0401d10340c605001e1312200c0b01c40004032040c103241601001001003100070000078080f0a0032a0046203004507140c241e80b450181c0c2c1c11084e0154900600050141851500c200b4490720070780342c1030010340c0d64620100690040303104503400310388c8850000d042684103101600313481845050000302d040d000c0c0c000c1200302c030382c3c818110050380c040d4085c415035107006100240401e804603130561901240e40c0d500e42d103902000c54001c2c040d08150001c150140c3c0036805403540900180c0b41001059a80c030318801444d05e5a002c260700480c00c115004400c0d007410b0190a1405801d5240c410170030f803a00c1c0f112402c2c1c109a6121660040051102040f55600d60009008500201da80030299061050405013850305603121806002c5051400b0080030307402060003580000000155034407107950340d80c262100d1290903034098 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 441913974 1250 441912724 441912749
    0x10509150f0f060d020c01140403020706120e0d0806042d0207110909010b01090b190c05070b04080a02180912030c041a0c0d02060903070f0c03081204062702010e0406 73
    0x3c49440481d0302170180801c444000b88003214502a802300307440d00588010300181c225260621a250003070f940c046406c440c5500c0082c014403081107542c00c0c0b100035070f070901c0047c00500c1800060702d01401680d0010100c0b0616640100c2a04140078080d01925402e103031440d0082078003010310000ca040f2240364007010708102410702e801d544103030091451540d83c1d0b0203d4940a00070440c00c000301c058401c80e0950400c090307440d4204150031b540710017840d02c0465281c400c040d004900780c001030025000428030b11005084900d4184101311022800d810034038408000780040045491002401e0042c4c0245680c0380c030340d42d403643c02400106100301d40083d0b041a000030300d03546a00c0380081c001c18480500105541310b8406211080361111820307034000c811a841070041d00c010407540156501421311688582d101c2c2d0396039585440580e044001151181d0030404100000d100c0c940c056901c4000c05c09000c145d03a5642c40c140450144582a00641000121280c000d819207807680114041e205504104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 441915224 1250 441913974 441913987
    0x11b051e070218370e101a0a050316030f0c0302100507140705030616021509061f0f0b0714070b1305040b1f09150f08010509150f0f06 59
    0x401285070241c03601c5404150b8401c0c040d010303401c0411141e1365508195101c00018054404d40006040c1003141d2000c507000c0c8901c0049403c07010303c1441030084041502c94510349241c4c0c1080108036940d40424081e4100a0125030300d641840650000e40e80d00407214401d5120350f08201704000e66680000b90000221400c0c2e160942c0c1140c060b048051040c40c1c68460441580003240d02e900d080c0c4144c03601079210b4400b1500500c403e24520341c55600d41d204039403070f502201c6952806440184d0b1400c0d819040784060108100c044500d030000c00100c03104260100381342c0721104460036040e208065403114081100010480f03043c21a401c184e038400102d810494035030720f0801040d0b03c204074a4507217540821380055242440c0c054121100c0c802012018140303802842295502c100c1c6900408009003154045000d009000074440d21030510341e140d0b8400c0d6080c0c10302601c1c020040e0030240c400d003038440c20004081c9400401011220043e101c03181105183c0f07000c1801c6000b840725903640204c011441 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 441916474 1250 441915224 441915259
    0xf0c1903020403061a03060a1d01050f2e1214030c06060906040e10090203190c0e07050909060d020109120809030706030b031002030402010e0a0e0702011b051e0702 72
    0x350082d41c0c014503042100100e176101e0340003203a0f004600190160800d5000920f4014181c0c0126014400184042105801c0317150707140c2100c808680c20303507041c0d03201024806071484001c0300c1c6074a51103184503507940307404401645809c112144a065a8241c0c00201c000030003801d03180c0e00a4002040302140e40302d01c05501603648820084070781314000c0b41100c1c0003414a26042c000e207a145455500907044103041c40c0d18800c06441d0011042ea054498410f00380010812030312401101070254040402c20f9080840281d407582001e8548420024148441c80c4e06545040c002900b00000322680700c0412614401a42c40c44043d42c040c2040144120124081c449210018446c021044099441c1213848103000d0b01140e081d94440340c3c02d40e101c59801e00d0840900e0740250382060050400c0080795882c0e0000400c000310a4110118071003030340c01401926a024003514080e1a009250300c034583e442c12200400e9030055118907080e48011407182d100d011250412521050f4025100c1030007552a00031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 441917724 1250 441916474 441916477
    0x9050601051209150919150b030d0f0810050a0e1b0c03040501030b030601030b0c031b03150301151406070311190c0807030807080903030d050a05010812040302090f0c190302 76
    0x1e1003995244c0c584d0002d00040004541c0c0740b114810b90b60b54988038040760b10740307100040d844107070380c2c1c2050382d03d40b442e001507941003140040349100d0303644003600d01020f100b0080003800090645614030780b1158041c00075548bc6a400810b40b20180c803102030903503030601d0815903040c14040902c2c1c8040001aa03da001801000410540c0c0007a02c061244000107400c1c1030342e5110900c0040c0054000c034000c11600c03580c0c90021500400350b10303104540f0400c00e0300c00310354542c01540e01d01410040b01c108980d0900702802a50030035504103401564840c0741000c4020000c2a40701440d104800003e030842c03c0500401000e8101c00f00c0381c048607555100034811070300a540800e0190385601000c0d100141d070400024080095982c881d54860404406c0e075074000450f048060419490f0105120b14090301d0030314071030540b044121060100e0b0302d524001000d400c1600b444201d0180341e908020500240e141d9080c0942c00c40818070780329643d942c03132100800c1c0328000c0281d2902900c41108808114560640 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 441918974 1250 441917724 441917743
    0x904050a06141e3601030317070c020910080f03040f0f080d050f3007020c010507020904050a050a05010204030c0b04050315090304090f151d0109050601051209 70
    0x44801c00d02d05202c00800200e41e60107491103007081840701030344925041a02c0d6090200d1000c005880e80c4811100001c2e01441103040c5095203004818010400e0680c04400c0d9002c1c0200c1210150103410258001003072800410f81c0603004141180c0401ca034641e004a400300241000c900f40c4a204058014440e00d950240c400c0005050454101049001c401d100c401e00f1180d266000701039422a02e40305580503001000e40f803c40030300601a00da90916989034000d4000e01403d0381072060010545001070f4040c1c0138000f501103600000140d4001d903040400c1300c8400e41c048501310850368407442d02d58904050f05100821314061000040d0403c001500500103582c8180b51030380342c07180c840d0404100c41c0190700c00d840d41a400807a014504100081800d81c0001e519001d403490251540e0084050f1494104086680c0e0765a00c41d041260b495142c20b1005441d29042d1070038400c82c0f010031505096410b01a411045681d540461250383c0158119071014078450010102450045d1005881d0303803128 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 441920224 1250 441918974 441918989
    0xb03060411030121051002030705090415050607020108091204060503070206160c060203070212040f1a03040c050909010f1506170c031602070b0d020a1b020604090c03020904050a06 79
    0x592207500050303488007903a0603a802c0c550112185252030101c0410381c05407013810390b2240070740017000391010014001035109451039185e070356881c0082c2d0706020450716480c40540660a5041081c0101c0d981c0b801192101502441c01010070346504c041c190522051048104800c1e0000400107861900140a1486200f240c0c00351034882e9541c000c24824000e80c40c510748005400340382c41c000058540d902841d0890400d1040310507204c55941070040603449a0000c003084040214100320200f00c4002e103d040c4500f03842e41c1401c41c102540c1b0f5150240c280d0007000d1056401100190f000328095000b14405200e80000b8000302000d445155000000707070007001e000440c244903c00815051103405030141d2207007040319203103980d9602c1000301c5100c954030030000c46c0078660340020055221405443c038501e82440050f6141c1150310045c5c40f12041c031100310903064902481002580d207182c151401c40302105400300302d801e8540012002071040150140e4400d14010a00641201e0390f403040c4143c5080c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 441921474 1250 441920224 441920231
    0x90804150e12030c0a0b04060b09070206060310140c0a0210050a02190201050915071103040e09060619060f20010504110d02090117120d1a0d080702040c0909060b030604 74
    0x80842c603141d100c0e07518406090703480505080c002039031864140e030380f0034040c000000383c5c0c00c84100050b00f400710aa41102c0107174041000d1002c14942841000203607510b040040241410000280d2403101008250340707078030390000c650450214002d105906801038000800c00040c50411940e8009400ca02842031040740301c0400c0b0300341d89005101c0c03a8055442c0500401441803d14400f5203130316001481c0008000c0c14100c2021107040070800f601c060f0205070307086a4140343c1907107000c0c03610340020802c0303214807005520820042103c400f20002d85605107403c018030f400c1018160b55904140d4a0809440c246c0000d1b10500d1038194440d80c001c41c81014000d04c0000407008010b01441c01c48000381d4060524401040000602002d8030103129008041e24800e208040740d500582d0800e58180c0d001c10744500d0241c0c4046224210038100d00e1003141da200300e225894070341a4240c06607040c003d01560f41c80d510f000c03070035006028550080c4007282041c0301290311007025000981050701d40c603003d2410b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 441922724 1250 441921474 441921499
    0x30f0d0f0903020c040504060b120f0d031407080a0b0904080a020d0207050f041805121213081c060503030f0414120c0904080d09030801031208010315090804150e 71
    0xd041c09001d41241d01540100808004501003000a02c005032045030250b46c0e036500f074100e50b12504145008886201c0c060002d4030700c41c03814030342400c240e08a00402c25290510241d803448031401e4650b000812071904601c41d540f54030700383c0000c0422445856115540381c0070802041281c1d0002d040e6121141e0036950861603070182682c3d500241d026241d8003003940328201d031080c01c2c258040e03150440c51010045443c030703440c3c550034100071542e4004412150001140b041420701c80968541010f103a00041c2030a440b16120441a0b000f00c04148219050340d141201804100c0c0e04484040c2400038260f99981401074444001a40244914442c10380d58901004480c60010181002c41001d03c01410312140c1c07000c20070041a070300034030460321740c2c106010039800e1100500c644440c0324400c1d103c5403110350440c1001d620b90300700040010100b280440c014400281c112601e40e030052107660380400c180c0d001e89810442801130790000d0704182c8802c1d001c00c0815030300c901d038010380b03520644010313100c02c0c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 441923974 1250 441922724 441922751
    0x503120702030d03110a26040b040b15031b03160e0109150f05060c0709110405120109200102101a0f150a0f0e03010f1b0203070c050907030905030f0d 66
    0x914181d0851702140050007251042809150103424818400c0d0b6804178911580d0729030400020280c5050301d10032150800c010070004811901500a04a0581c00c4241c03025400042d645030344040c988200401032030a55143d0307403810088009803910700f51990052a850b81c2220b61440001d210f02c00c103182c14509010800d240c0c08401c181622001c01045404500303140030b1001039480140d10262030310a00c00001a003294610078401800b034448600c55440b4540810418a056214402d4002da403506883c6400101143c050300d0545c6e10402102003503400540c0142c1c1010100951805540c1c00c100007001380541204000661520440d0310168246803e01808200e41c050310102229031010040340641d24090b0a1542c420130051034400040440d01d00443d0944440104201e280b40c2c81d040040035011183c000200682428801507081c0102522110105101d40c07140c14082c82c07020000c900640e00c00d030000d403500c0d87c019007100c0c0d5410200a105907980d10034004011400c1c17400a00545a5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 441925224 1250 441923974 441923981
    0x61406010e040b0904082503020703170313121b0f0203010507080c0409020306030102041212021005101a0d0603030206100b181c050607050a11060c0a180503120702030d03 75
    0x420f01910704152540c03680d070b0b001e4403540147c00c0e40003802d184003140d40902c0581d031030b02105e140c0f0030345c00362010616501d040b0301440068409604c010000388200100409503090040006411034190ba0290b10112015500d01042050581403910410301a101744103140350102c1e801813098001b044640e8580a0480d0000c006a0b071a900b040700810003045a501c0f9034000e143c0041009000519180e5a0786610340071076081c0a048441c2850b04038041451a01840070040c60b40c8510320610507071400c01c2c41d807001810039001e00513804113030104980580540d40700743c80320380303000b91400c008664076410702a549020480300c042c00224583c502003041c040030416a0314440850485c2d0042030440d000b000340c80348408040881020240d145c00c0041481044210b004e40c00c141c907010303a0340000c00030091461001c0c031003a070f01b00d030b101c0b0050009c1d0700401421942050058940100c501712030760801400142a5030210394584281070030095038500307400060000502c01c80481300c284201c0c1c20103070213a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 441926474 1250 441925224 441925241
    0x6090102181003060f0323120d0f09140105224404170c09040f0206160c06030f050f0414010e0712060b030708061b07061406010e04 58
    0x166900c01d6401c1c0c41c509203942d068403600464200442e003103894040701c5440d02d00c507510a542c0303403e09180c03480030710500c0445485141c014202a1820208280c0c1d00c6841e8031604540c1c41e403056944440d64800b94440d401100080d44c010709a0145000c4541900d02034842035a0300c400700c803035040d50200c95441c40e005416a655109001e2070001d0701511950b0260440c000d02400089008412110041408060303406548100506035413a9030078800c1c0c0b01102000380520564a601191a03146555203020000b6809075200300041c0208580b480403407418001c449001104070340303410311242040f103150000170a032100c1d0754080094040b0340c3c4403142030310302c152240d4400f2140d60f004540440c1464070a8002d2110070000070880e500700c4041c0500d040410750202101440c0341a441c02000030340e0140c0840788808400421000d070501e1609912540040d19000c1ca0016070136000035100000b9040c0c0d0300303464000204001400013514100e0740c01400710345481c0010301c0748011000c10714091046214 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 441927724 1250 441926474 441926497
    0x3030f04020609010309290106020a0c03080a020a02130501050310060506030f0943030c09151701090b01090e0a06050414073305030a0c120213050306090102 69
    0x1000d8489400307101c216889052100c0c10580c54a1440d008600e420300f4906813070103402d208031484a0701c1ca002d6000302006800035011500b00715a541d0210324540e05250646e90800c9280e07a0700d201c0d9100070781c030700468208003d401138103800d03d00c00c1204495106a0407214107030241d82501030545000c2044461602501d5446078041c808952080420300790035500500304822110070f008224600110881c030141d00001c1042d103101d10b802d4a0740064081003418003041d00c100849030840d6292840d00d0200d02070144035a81c3c44210116052400a610005100f40018015203034003011005001e000703501801c2c0e40c0340c003a0f580001031400c1107125019010402c60060091303099540d0741d1202401000e401030701d4a40c541001b16042d07420500c00c003001000445072092401104041e42c8407407901680c84122407500c1401c070f41c2c442130340100031240c3c8510740b03d0000580d121260401d4851084e051a68017002d0710100d00d040c2030700030b0416520103030b42c000c030100c881656403800365500383d101c2c0d41103900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 441928974 1250 441927724 441927751
    0x61a040e010509070f0c0f0813030203010f02030402100807120c170610090909020109030b0702060403110a20010c0b07050c070b090604260105040605070e0909070b03090f01051302120303 82
    0x242d100c0c2c4500c1c1c901b103000e84115211003144c1e6103511a9192500100300c41d00c0e1040081200304110320b02481894880d400300b020642c11b501d800e40000c4d0705585000c00e00b90502c6405000209818800c410045a100062100300541c0e040308100500764420100b13000c1d0100d1030a4081502440c0800000d0702e00c0d0305583e110f51003942000e000c0006031541c0441203042c020480b001000242540c40c1080c0302e03114541c000d0a15150604004200d03041d01c4004009582201c52040013044058250208160145000144010f03504004803007000090b000039100c03a80000c20300030110380c08002407070740140303200451795007030745074181d0041c3c1d03214000c0b1295000f04100720401030400d0006031085c031003203503c0c00ca881d20501d1440d07880c00e49000311404c440481e80c8000300044140c0100441c0000902651240d855141c40c041c0b0b941d403040356018003a09600003100013101e03a002004420410600000280002d0901d00700510015081040491240c190b60b02146031201000080c4e900c550401f05103003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 441930224 1250 441928974 441928997
    0xf10050c011a101806110708070801020a08130b060618130b010f11100c030b0315190b01021e031911010f021e0c010605090c12100b070201050c01061a040e01050907 72
    0x9a400e0100400201d1150140711f80c009a003a01c20300100d0001c000403c0050780d940441c1000410000d4000c02000ac800e0360404c034000410300100d2540e03445a010fa5035541c3d514400041da41c1682e5029914607888186844030072842c02c511b41040c8103100302070b02d8408080d5a220019604402502140180c6602240a01658113070b55008104000032030700740020b4103407190010a080609142000c0403601050080c0134803503400d41141d212010f48442c0030405104c071940000d40703515501324080c80150a040152050700c20600845418848103502c0c00e0224100c2c6c0c50107050114132040e0081d295180a403020a5a0328a000722801d800100741c80b002c48060340742283c5c0041e0030040c21000340390b5031441c0c0840c4640780c01e42e449001d00307001e95409440354424007102d0071441000788440300c3d510384e405c41004049805010303900031990900f42281c4400b070008006e4010700c9240d224440d0160141941c0e00820341c00d000500a4801c940400070040e0f0300c034030600000c501c0541d460300c009983c03404403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 441931474 1250 441930224 441930227
    0x21c141219034101120201050307200f0d03050a06030f030f02030409050f010302031009020102030409020f131d24090a020c0604060c020c030c0f10050c011a101806 72
    0xb41c84000e040310314119194a24516800a0b419143d01401c0c0c0640c4004112140c2406207100760040c11908800c0000c9550355000030118000034250304c0c01d00040b20020502e85000e042c00c0103005480f44101c402c01805904025614106100c07148046031509010504011003401450292600048451002c8245903070841381c80d0280a601021808140130214a0311741a0003032900500035400a0152075055004050424005100d6040c4540c80c103080070006036000b0054a048507004840142ca809404202d01568070030b958582d211103840b4000030030842d451030240c084001d50b40d01001001e50314142c80c400c180b008040c90250301244d5028803121451b00084c81680301180000150070442401c0c000352400d1000d40c0c04444d03d0391540118108580c2c10800030706508000c0300103041c060014800309140188208601d80501101c014580c00035018a0840b0845075001c4020451040e498040907a500140300303425124980750746400c04054410f1042c95550011440144500b5140100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 441932724 1250 441931474 441931481
    0x18011a070c17031c1a04050411040c02010905030c0d03050603030f030a09080c010c0207030201020d0504060c0f030e03030d050405060a09030e040b040e0703150f02070305070f021c14121903 83
    0x8810200e03100c1000044041284c06851242403080d030180821030410f100301110060078803005582c0614584420000071a2071000941c1d00300f0301c207440000d003034007249008034050128904041c00c035100001d00d08584050000e00f021000220b035504010726282d0004040c0c4a1007842080000c402003880400c03041e0344194085a00c441c45181070b249401c1c440078915081d00ca0704003030000560012c0000b0400c0d9601800304101140a520b4800e00d064180f60010705841d26031000503080582c6008482c080601850000100320401001c40e0f0710381d28000c020758050041107401720703840d0054401007055007905000c1d014016503d40c13200c403501c41c080c07010301009000d085001d9a02035118104081000414404100a1070143c0c468050990354402c8900c196203036522004d80b03161042000030042a07001c4180d4082035402038101c480700707500d4000100e40300d150480d40d405101c042e070828020044040036240f02030810406950000003150703041c8040303010b0f80e0a40400e071000015040c0e1070511a51 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 441933974 1250 441932724 441932759
    0x20406020303060a06032d0b040c031b08091504140105010e01090e06040308010e1005090702030702010216030206030118020d020d09051618150b03070e120d05120705070218011a070c 80
    0x500092105404800241034074021041d080100342e130cc40e031b20304255148007040340c1d01e4900340c100f5050a05011007595aa0408400380040607884040030078204420403516452921409001380711a503154103040303038082002c3c031401211a240481d200e4980c1c00100d00c5c01d2046800d52030340700700c2d603180050320020440f006003019003030440c00c80b02041d140e88000d48940501225402942c42c0e540900c0060300d03046490750407442c5418000d0003040165604011a0306655950030f680c0034520905002e50041d010b000e101800050011981c08402550303a84a500c01e2402081100c41c0c00e5180c03024015560502d01030200e059140134a0b00f0180801f0340c008241d800101c10880007140e90300d804181a0b90070a07074140d00098801c072802e00303641c542100301e60003100b10310000e0640c5200c1c0403000703025846070400c0c00540d99440300002e403585001d5020341d44410b802500b1070340c182000300c1448044281c01d0007400803003690040030449107810201524030b03580d07000c0801000300782048445c241251140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 441935224 1250 441933974 441934061
    0x6030509190602180a030f06020715060617160f0509011b0c03170408060708130f12110706090e060a051210270b1801020406020303060a0603 62
    0x194031004079014041400301120b00070740c0c0c01a154520360300350407111045002d1051040c01c40c40d9080c004152030301b00d1307900500e0b070002c07005a1303036001c902e00151820100744001d201c8514002000448a802410000442d444140c034411540c3d281d10301b2165103011780302c00b040041c5c074080d001c03030003031340614000c0000c440c0504000007142a01203259002007200001118400d070f840c0020810018284004440c1c091a601f4107820b180c100840301d613407514020300032020424000c02040ca40e0321020248503820340c20190494402c0f0321750030031003512407120400d000001c0c0c10560044450402080000565880381e07544075440b40b411800803c003000151400380d03c02c0340d41100007699a81c01300886010408940640720003c009224001140c981c151054400e840092101d03400c914241460800b40354000d0042070140c45001e60306881c40015840001c10758400600801c00390380001c0070318412a812100d80c0341b0291104002c4050310b1525078000b0b2816071101204483c505601c3e02d0180c4445032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 441936474 1250 441935224 441935233
    0xd03050c030408011506111009020a150807020c0103050606040509042307060f050f0904020c010f020c0c030106050f220b190501030b010c1110111516090f06030509 72
    0x100d0040303504581c03040d40100c1040e90742d9400140b144490300300d80c400a140c03904001c140c8094800b8141c2e00d0b03041c00c14041c15000d561725401800c6668854180024040303071250301004841004009c0d00b034407815a113050162041d820b400b1b800c2d42c03003070040d640700c0c06025111a080c1440d26050029550010340100c2d401900081d51104001404102c4600d2120942c01040c096140c01d2000d8844080452520b040040030018080101c22100032911000e0094500582d16180c160a85005145102e0701800c56400041c3d901c4d11410000749403500040114002c10a465890f0108180100320350012a041600010105403841e80e214810b0003c210300f40e000308801c081000092455442030401c00044000e000c0c003030200307503850f102d00c030300f098028206160105025100c6810401d08945518855503200f01c05069240c4108070030640304201078200c400c02d02205031601c1a4400c04c85904091301c41c0b206980d01d490313204114040842d030402d151110414100007044015040007800e940c0369200c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 441937724 1250 441936474 441936487
    0x90201090911250c0602010c020303060111010e06040605010503010b0f030c100c051c090905091c020a0606080307060c1b0b04020d08070507090c03060609180e030304121b030206060d0305 82
    0xf07043c620314006544041c1d402c082824a0f00d09012486803d4001d40c0442e890a17031050b4042d5000002c49030055801d003440307100301e0f413000541805071982d00b840c610a40504014082001866000a8140c07071b4205c0082c06203940d21002d1105a000c88a4243d6040e40034540717650031400c0148429148454a02d000900031010f915040c1c9020300c549030141c0d500314050a282c03401e59201ca844805003429000a11a5007031540d2a140e407440455591841c44400b0280802e816000700040c501890f40050103111036540ea540300c507181d4010070030503a070030350600003521002c13807244418060b9455030303101c1481105034a0301c40400150000b44101c1e04654001e640101261580d0090041944070b0b00081403d00c0c2048401e0090b1955840ca2a091504103202880381c19007000069098590301d400b0884404440039010000e0a92400700d061107000020910050121000304c05400001c00d84550a8030006505020581c0b07074855006001608480085841407800c010001d4503213020b890700505004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 441938974 1250 441937724 441937747
    0x90b09040e0d0e030606010804022d030a030c0c06020703021806011407050102030403022b030b0406050a15080708130206030402030c10170f0c0906032208040e0a090201090911 77
    0x3520b007542080851202c4092800d40d02e030812030700307502c81000c1c80c01d08860f0600350701250b14941048113100d0b40569800081c040c00440250510b00354000504441000105040292840301c0580042d1130801a605002c0380503400061144101c0364080d0602e5070000b20301002e00703c5410084c1c0b041d410061600d001c280751111100c042c18480b4080e03000166642007504c0c002e03142c0700c075080280e19008402505114840c6003058450408102d60902003444940203001a00419294000b03544c444007920000c148462418058121143c1c99202c0759244c1e195204d041e1004082220b400c2100603032411180014100b1001550708148040c00b15648401140300051100c40d842e4181c20009190b40134003040360f40181300e07098100c50014030303040d81402e004186500070711079615100d01803800040850400100003450741312000244600c2001d0b0449440c041c0e1b0254490301c034a80e040d080e6003010a0130720607540b1a100400340c1c144c51301c1074640e2404154401600f186a1003038003007030051109a8120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 441940224 1250 441938974 441938983
    0x80303010b19140f09030a0b10060906090308070303090206070c080f0c1804020907020a0f030504090506041401030303110705070b0705011d070b1e0c010b0a08010c090b09040e 77
    0x811003410001c0d01c03034400b0305458108841035940a001c0181880280303111103107050480b400111020a07260780c4804030008a8a1b01d111090014800e418000c02c1102081c0904490015515240d4404190640c0c0e0351085500704500c0c00f028094440c1004100c1c0002d0080c1d00c05e080c103d1000e81300c50709004c9a621404900c54060b400700e80160843c00a08220b45804d008465240104846030038110440451100204900500003801461603001082c0c000e030007007003104100c40d4031000951402c0403a2800030a070783c00c0f620503244200e041c40d02048140c580b90041c2c05120240503c00c00c0f0076807843e14104c01030200c10060b544d041000f0815807020074024000b00d009080305613226541c603542483d00303a08485140f084101e101e402030401c144041400300e881c00482e80340f0b0601940341c40580c103000300c105010342d039062001d0f90001072400360b018040d045501c41d03000440703100140996841816081e18030480e000000514004028020480f441c03015000f104c01c054000580c144445404c01c0ca171 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 441941474 1250 441940224 441940229
    0x718080d0315050603040309030203120f040b0f040308030703061d0c070b0703060f0e0906100f030311011d0f060f0106050a050c0709061d0a060e040209040224040f0806100b0c0708030301 82
    0x2802208c402c0c000d40c1010040808030a41c104191458901c0e038a002c118603000300d001300e4100340000118445c2900404058030082c1d5001880070f544d0781045c6102034010302181c07060860350400c080c00d0800e00c0b805001024421250b0076981032500ca4103940705141c0300b100500d49814156038640204e640c4070a0007a007006400d0410358030a032414802c15035490204000d118545104442c031003440154000b100a0040300d603d400c003200501140e911050241c0b4103e401c114040c40305074004428080002201c410011045081c0c0b0703083d03140d29541d020807250234010301c00410010040100201d210303c00802440710f44c01b0a41e000c0396298100c0c0c60650300e20754040b0309401c00010314086c244034407065440d044003201c0c81c10001c05151040c51411b004c40148068850341d0401c00003000d5460b180000c91803822020010381490b0500e13449a07590307401a010320f00a95030b106802007040400000d1050246807000400700c1001e10b00301c0050100c0c1e102118544180c01031050000e4280c0381040518007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 441942724 1250 441941474 441941477
    0x50c030c1e0a020d2309060d270303051303050a110c0301050106020105060909031813140a0c1205011a090a180903140a1d1210050718080d03150506030403 68
    0x161980c0101c0024409000c984500d50b00003000140704600c00c08007811921030480507030303065888010400300940200780c5101d49c40301203800d4811f10004860b401400c0c019aa110b501c0c100300070b0312900403c20071a800c2000043c0495402c0140942d40350061070805800b21640c0e00716100e144034107001c00d0940c0e001307a1003100540e4440003072011516110300701590001c40c040080d4204540c02c0d1804034601406000d60380504006550411000c4494114907a40244803d09103120300708602d0000c020035001052400150a40002c1100021640a03c50480341c84800200e1107203100c00e20510341e544102c212982c05003840350000b801d2100e649400c440141915400519800907042c05004031a51801c1038144d80000c0001d0040e6a8110180003060107000c481d42103000703102c20114417000b0a50b4008a02c81c41801c40300200310490b03420052003181240d50314040f6114030fa0b0402c050f9403440c003a1107500d801072081607103540c0c4250300c444940e2103000c407142e0740ea694600215141e544261021360 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 441943974 1250 441942724 441942733
    0x3141b090a1206022109070620010e06010806010909111e031b0a0501050309100e1014040c12020934020d17060604030f05030d02040b040315050c030c1e0a02 69
    0x40301d100c4a10034428005d110340c920700d4041d18100715030b1600ca000c280030b81403d0106003100540e80300030443e960040c4100040007040480d10003403905c2e6a0305024170403808141b29410000c215025603003e8240d04c0e03680000c00080114001041201102c54100c0140c4004890100b01205a80420400e000741440018042c1c10122403028002c1820180e04a00d0511504209006200d0301c0000e0080171300e140b0343d2000603100007a444650a1005555110013901d080c00e41c580c5000c881013030014003841c0700e41c60f0300e10940d640304d90b18400d100c4807030000717940b124124000801f803080b03080c50340c842060320703d601e41c0c0d50141da83e41c821201030307454141c0401279101425615a642e0010301034882004a1030103054a0f1920300005444c034400e0b80002044400d40383c0300c0900f0843d040003511200d178a43d203c1035403903c2d242c450301c02c180e0b006440b0581c0e041e0b511052034400c0305000c1c0304290044040b84c0c1540c0c955582c050850301c06c0e9000c170070305e070582010707403100c81030721408807805003150750035950241 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 441945224 1250 441943974 441943987
    0x601082a24030a1a0d24020a0201060603061508061909110403110a03050727020301060309051c05030106080c0c072c090712031b050c0103141b090a120602 68
    0x412903810b20380c41c00c4c000c1d42da41144420784ea0b81c841c00405150703101d0308400740c1520b00070661000410030384d01e005080d8004100c3c0c3c144150103400c81800d5030195a010408159100f0381e501c40103908000c0b10002c103282a01180181c01d00c0708444c168501c441c00055a8039a8607280c000803a88101d01540d076038080420700340304000c4e00003d4680140003c85e0111051411070300c071252100072910400309000301a080100c20790018900301501c142c0d909030219107960b900c080240142c10055021036860298aa8885404900c01078403514001ca035540c0b54103503801c0000031342d04008058400400318805100805c1c0101080040340e0181c001144a0f50b9800c180f01c011440422581140120507000181086174019000505c503045550f4075619405603000c506064030b81d401240040041c401d001d8078413400f40400002c04c0041c480081ea001c01030601c00c214141040da200f07540340f0b500fa04102c1f548901d9200848042d228484004013650082caa60300f10034907080030030500443d05030390041520f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 441946474 1250 441945224 441945241
    0x40b0406111b031215030d1209051b1203070b06010c0c09050709061409011b08120103111824191e09090f03030c03060f090e0601082a2403 61
    0x80030f1700300503180c1d0756052455215002903100e0714181d0300c510401802442084802170150005403d45400006540210701c1510018884806c0800c0341800b40768007422075840c1c50000021104400d410902411940d22000c00448298180702010365641003060004150740545220b05030180c003031030715003841d41490010003402c14600300e000303041b9160007813002c03600c10790b0030044c82415604211445840e882152900782c402e4024a6443e5505200010010040200780004107458580032a243e11011140b0702d500c2c40c00300c2d0220303a02000c1442010074040c00100400380f601c02c60100401c0e84001c18421000b1132000512984020f604404002202d103031490440440d8010740410701c0d084c45408156120031210340b0b2100f100804169880b0341c20b10b08284070b5800400070300394112208101350740d290580e4000e0411100184d14038003410000060306c5d04000b0f02d480c4081044c00301c04540f04ea1000341c20b2203003645000c40a4010b41610460070301c02022030f0140d12001111004185c803400c02c1d002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 441947724 1250 441946474 441946507
    0x61c0318170d0201060f030b100f0e0a0b030601050f0105030a090506101805040519080f16031d010f03112a0f0c0a030b06012c0315040b0406111b03 65
    0x1882c00a69140039400d03c88900541600b00580307810021880030f40e1034a0080c1c400c120030030390001c02d400421035004610700309042c60183c001c0f400c07000b01b4003003d4014410903440b500c0c20310415500020701d100411f05540100c0156500090751f00000030790350ba0588407d0b0a01204445c0c0c00c000c900401810b22402c040c01109680c40b0600c06001c01003807a040e0354042e81d5030044240c004d100ca0f01d84903003004100200701210b8580c403845280586030128100c05c00302e0584040c0e821800315000410303207104094013400c11107500c40c05955550103180c4210040c0d00600d600800c2c10b114040402600d004c280c400716441039080c6840b5082100a160007040360f080103110684400340350040810b0864558580c05810242c0381c10204686507034441d0301c01601c000704800301e4801940c0360b00c0d80141810369045001d44494009900380c500d40042c4610390044140d08a034024401c00591001c103010494962040d9103640b84400054a0190323202c00048bd110401c0c04110684d0b40b00041920620020381c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 441948974 1250 441947724 441947743
    0x204092901030c14120a032a020d06110d09050a0605071701090b120d031410060c200303040b030a0f0c1e1b0602090405010b03061c031817 61
    0x84102606505564880410b4541403140b90a1311500c10801c8030a0b41e100c2c500c0c0307802e58403240c1c116507030000c4034900503002004610550001021104003820b600054031400d4440d60b600030100500d000381d40da035a40041c4011000755800840c1800508843e00c5184941c54407a400390340244034103159880c0040c1038440040994080048035076840d4103c48880d25200e0550700e502d031010400c0110b10340844c0c2410f0014240c001d46214441070f0007445038040c1d00005001e0040540000c16659030700b10340703601806c2481400c000591091101c0085200d500b0f030042c421600f46450000c0440c2000040d20319082a0048110150008284078408840f40b041d203400b40e02c0010b09000c3c0c008441405490502c080b801d0b20b028014040304014100c3c0725a0f05500c0c001d802c0b842d01c032182c1000e820484003d400c81201180503034030b8a000826988017405c2500e00c280c4008002e03026081d03c0d440f42c3c0042c803804030812800e0003a01942c102c45001c0e00705034100a40884e489102984c1d82030340305503260030b40c0d04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 441950224 1250 441948974 441949043
    0xe06190605180402010201020f03011512060810051302030607020d08090d08010e07020f0610030303110702060412030e0618101e0e060705010e0703031d0f0d02010c020409 75
    0x240c080100351120540341c601c5107802003010116965500050303001e44202100c9842100c00000085440703001801c400215592543e51360100b0300f000415001111040c2c003030108581d1080107a028401c0d041d4220541c000c880b0514055100255404245404030581700c441c0503030070050310840341c0c40e0302001183d031150030003005120410078582e02400016040c011404e801100f0070020382850b000304100841020900c0072200f6518000c2d602113030350b00c604d0108400290138210303100b07007880340d08050b0351034240c000f0902483c051030140128090314800004800303100041c0700c082c01036a9201e000d00007219071141c0680e03185004004211400d400008403c0602c021070454001c002c8540702000c0c0681d1131030070100702c2d03500103200064a80c080c101004005600704080100c110001185050460340300341c8810403e00d454002030380c000c0d0405404a82c110203030352044400c5180504c54071440f42c0c0181040c4418010380e802240c2916103840098986a40c0346580c2851a10003140035903d09019 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 441951474 1250 441950224 441950231
    0xf05061504060c020d05010902090408090301060b0c12210708101d070f0905031c080903070f02090415050901060e011d01051002031b0105090c22050c09040e0619 71
    0x3400009048083c95200103805408459407103070800c4001d60018403c150002c051244900c1d00e4508940180c0c08003041c2e074040d50030300c01c0000d00060f0044c156000d0021031800703404101014201860345070440c4900289035581624507074140c01d480500e176030198a05680301d0752145450316120513400314070781c00100d130b00d40501030b03050040e0051a0810303045002d07807820301885100d05000302c49210f005d42056500d03002d004501c84800d404003495060340e11203a00c2d000d0141d51501501074aa014259010301840303c208003050040c81e100c5520341d030051190030302c807201c181c89002e1242251422100c4c00a903030354512043c00894044001a40103207445c115014203205480c1c10f100c404441071150390301583c80340c60714440c1d143c006d05c2960412010103000018032028149518040c10003030302c2c0c1e840a4028514024120f05040b42030038855040c0d01c0803a00030300380301001036004020040881007469014008070301c05540301d02440051178022001002d4504082c682d514450003620007800c0800e01e07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 441952724 1250 441951474 441951479
    0x20c120307140303250e01081009060806060906030106080601060302030405033f13060203060a0515220e04080a030615030e0c0405090c1003090803040311300d0608010f05061504 78
    0x203018041071501b10003132800c244a602c3d1003110784c04005064124468950814001144104c00010681e1003802c0446100c40c1645440c0241404c0301c100c0d00a05109070411070040c09010701a40046401078400c07000c40c0e00c2e008580318228120000340e1800a5901d88845804d954400340080e01114020350369030710781d09418080144400380100d184020a9079401000245680e9203000e0808002d0101401201c5140e0310010301c1c0200350303c00065130038400c482c01010211060440380d0f81d011390313652010000454030390380c48401c410b8009410813420552659004075118150082c00402100152000300304160b04028060a25001c038140f103000d02c1c40c01042007280c1100240700d0154030829038000c0c00104504900b1000b40c00001c401801d081e80000500080550180c04080401009025074045c0000c040c0b0000c40f020038101c94103d000d030403028512002d00d42d04009c000762040d0200004d0026074424140e402d6440d00386041ca0290358074410416241000d0041620b9004904e00c10380c507090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 441953974 1250 441952724 441952727
    0x801050c19020d090909020301090f0303020405101106070809010e0a030201020a03060503120a141b060f070503100311060d0f0c03061a0a0806010509040534020c12030714030325 78
    0x1d440348180b134045d07501d62070b400081d51400c0d8000003940740c002041d01c44110181c20003401a6005210782400b428810100c0d100082c03142c3d1228102c1d0420102030701c081e03260140111100d0401801c966850b540c1d4002c014081d400c100400c40245220307400250b100c40807000043c0c00c441260f0f0026009130000130300403070b804071a40f044582c45021401d101c0048088120003008a00558155000000300c446c50243c5040700000d01c00d00c00e5540007182c052660710020229800d0100741e4a4292200c1c14480a00000d08284801402c1b960050701c3d850070160a0314001040c0d94a1030700c45000c05507100c010558664bc54000c6102410000c41415152b1035205080e007154410102c805040024150114605a21030400c640c092100201306008500300005000c0c0fa200c0030081100b01c03125400050604940c41c0e894100540b4115000350031070a1030790782401011030341580d9038645400308110940009612581040343c9100c5c50000b1030301c0f480c0804424182c2081040e0440179207a5608130b003045c15 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 441955224 1250 441953974 441953987
    0x1a040c0506310e011208040509040c0f0b090916140a030e060106020c03100f060f0e0a24090f02070803100612140601030b0a050a12031416021002070801050c19020d 72
    0x1031324580142018211541040141b500454211a600c2017040081c0418442c0401ca640107070b6214070344802089075900e0b0a140707103100703000f011500b002041c000207049400450081207010054188508280c02c0620002a154400700d00d80000c80c3d90742c00d544504400c10007540d4003514250004108031500b503000250b50350b54051a0f41c80803601c60f511400a00314603048100145941c1101c02d294980710908200d881000712640c0c00c1051034a48445410103000d000000d5890301d540031984018140401040904032901701c6206094080181e9000110040002d61081611488a00d0a241489001001c05091000081c081030034a6154070300b03030115080d495088142403d00180000002002c41d4100409901c200e43c00700b2130300c0000480540580781002e41600c80e580b900589228400040750070300805513800112400401c00c8001800c00795101c103100d2050b0300488070750079078072a00c143c2500c0084500d2190101c01140030550311900020152001103240040c0448035a14680106032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 441956474 1250 441955224 441955229
    0xf031a04021b010b120c2704030f030b150a14090a030503030601091d061c120206060103110c030a080402060d02031510032f130b03061c1a040c0506310e01 68
    0x50300c41c8074001c12400301e2402c00f520025070700070a03a141f03441c00741005480303046850680c1011030f0a041141400f45018071400384140c00c52000c150508400d80c40844451400c2c0c201e461400b4070400c00b00d45903540726240c2c00f0046100703e00070355880c507048000400004080c0d10a00058040020035403201e0070018041d90700941c02c2d110240c5840001000c80103504040710054180010500c201c0803903a400324905200704400e0720148401c1d104002ca0741042c0c440c2144a002d5500140512030703016118420f0b1a800078001069039041c14803540c408001c036803080c1d8544a01c0005058080e40c60305000c030f030609454030385007020020754800d41c401d500419002c9441549c003001c046000800d60310100150381b56003000c0b03c1081c002c00c0d01c0c1c0c508610f440c0e000b0b07940d103485003800010000192640800c03c03031480340d22070440145261104142e25202d28003030800c48248022060106e441c3d2280c1c4084c0200f8000d003ca079071003d840040500007448450441d08132411042d0400380000304e04210030904 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 441957724 1250 441956474 441956479
    0x9060f1f09060f0501170415020706020a0807031d06010320060c03070c0909050618010e01020a030b0f09011a0309150a09140610030f0f0b0709031407060f031a04021b010b120c 77
    0x403509501c12340b00038400d00c4402013000f071012030403156040c0e011080360301c100719588042101c034102c580c903030314003041071019000f155104d1001840050003282522000c00c4a20315032961003400380001610f070f0f42080803800b0540e84003141c26024048075120810041c00741e00010004d030314003500da541d100c08005042c41000200021021103841096000b074105038045c0d80215101d10400c5801405071070020041407084011495540440ca010150b0504036043c081d0b010003801e10040f40d114840e00000c1010f0928081c00b110b60741d0804015143340d00c1090f11000004000710345261104400c10001c1c4148281c3d03104071300b084900f0001c0448041500e4004d8644410501d030786c500b401c0c4006154400030a650489802d010487c0e0b00242003100307032482169200103200d10060100d82e111040c1c0b051000141c1c00c0145101ca8034001e601c40600d00004a8492417451040000f090907031740502c2c1d0b00c03501c413003481080480c100428441c443c1103107804c481d2070040c0d81c20300010b0360340c0d014188002031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 441958974 1250 441957724 441957743
    0x709180609050705120f060c090a05091e0109050601020f070608150d02030a111507030e060f120f0a0b0102060402060901181d0f06040509060f1f09060f05011704 71
    0x141441010800350740107180062507141d40341031180170343da101c4c213404060900350b1281c4004241003046031020341e101510094a1070040c02d10b42000c00c03000980c0a040c46030340003212011203030313004003503044680604100100403a05050070800245030131414001003050340c001c0c00043c0260750b03004c41d000d45c1051644140040201c1c104000030400340013640021341c144603180010080110010b49015454000ca6a61501d48110b02c1c000e000c07446413a000400141c2d260f04811454646003001e081a88071341c010850038007124034003a400c0c905090751a80c120400c00c00400c1000030a600a280412600388068007490038503901003070960207407030840c50500030545460803807580b951304494001c040c50f80462886082020a072805d40b50700740d0b00c000040190000203007140c1002d0081078020341c00c82c8020103142d0780b4048010000103000e006401ca643c4250401211902031000c803401424000c4000501d580c540400124400d5683c0e00c0355050101c4244100c109a1240f1811944143c2009a01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 441960224 1250 441958974 441958991
    0xd050d111803010b01090e010b0714010c0c02090c040e0a051b1c1107030503060d030509030a050705091e0408130518040c0602010e030a03240b0a0207091806 69
    0x600180480c81000a034044000c6002141901034984403404804141c00800c074040c2c0040044038854a98011245803412030300042000c2c4503440c0040020300c0c0030302201c00303c2d900004441420f540644c0c0580c800200f011510b01c05600c3c2086e907a83d081240810883e1034640362080407600040b000301080d00d0306642da000a41a28048034408040c590000403040d9186d4852101c05000800000c13034000f151325052060809004e248211035100e0340640385d4505594810040081141000c0d070201c040080c240802070441d1010004224400d1155000d03018ac607003450b00380013503030a00400e8807810031145035090401440142d0083d4205405c0f003800e40d03490140030441e80050030580d108070b4000b4041c84002c80041c0100b00000d001c1c520030484194001e644031003c90070381e0044407252500e50400c004030f81c0303c13500951101c0051b09100c40505000030a00d0748100c1c40312500c0c1c0c04441c410358009020541c0c6641400030301e0160041440c00c00c50f204a007007a0b0341c2110602d00300103100c43d0703540081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 441961474 1250 441960224 441960247
    0x3110307022e05091c0c050a06021f09020d0314120a0c110105160c020d02030d0201091208090307172206020c0105030421090306050a06030c12050d05 66
    0x4541403550054910604902d0300d01c40704910003890351050281407010618041d541e40b0070801c07100b0b4210300a101d0000980d44146007408000c40f840200c8210f1600340c00015103440da80551402005980c024184031846056071086104500c080c06142a250041300b0300160354940c58003400715010b00e44281443c071022a00308451180c00c4403402e10b21229820010f00301a5034004902d0101280e0b2842c1d0250503100925003619415150000058102c00b10b00c0b0f031161042c03030440c6490780000c0031084080c8140c3c01003802c2c81c103031200200050351500c003c002445581e41550f160980f035403030030000d5031500d00c1c41241c90380210301c8005c1212a02500f484200e1a00b02c09564030011003411302c403028032803030942d040050458400d10f40540208041500e1540c01501943e10450b00134042c40140e101c800410350391a54040501414003106032804404568903202e4103110f941c04003c0018810308504021000302c900340d020030010300c0511020b030009400401c1c0d4140d00303040381c28040d483c0c0720841c0c41e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 441962724 1250 441961474 441961477
    0x60501030b060a030c120e0604151e0b040b09010e040605100305070b0d060e0708061002191401060317070224090409020f060a0210060b0703051615020f03070327031103 74
    0x100c0311b040e1030601640401080001c42c1150060780b0601341400e2103050b101a4200b5140242140c0725403a07802c109003a501c0c5803903040710b82e48601c01030002849003504400200401020707048500c0f40c50200081008008852140540040940f100c2084480c07442c0d44159a43c8524041e064815501003019914403500d504400302800085004491901d024803000b0070030310080703404a21503503942c2c03503140f00c5600100c0c2000350490402651100d000c01c54541a940ba18100944901c565840380b00001083c2d035168445402d464040e451a5248a036004000c28a0302151840407040d41800c00d03080000c600e10101c0310310407400d480c003080034011800082c00d42c400802e01d0a0f005200021000c019950126103016a2075411804000b89030700d626801e1201c2c043c40c41c000f80812800c008258507021580400700f41d0034803603002013200f03040600079207050b0f07080000407103500c0c180032044c00500758250280100c40052290584203140a0582c8004043d68040f006000c0c000b2098510a03659400d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 441963974 1250 441962724 441962747
    0x6040b070201140a0e010314060a05210303090a1407120f0501090501020a031e09031403041e03090602240a0b011e0e090c09010210020f190e04060501030b060a030c 72
    0x35507111a81e1140c080c02c0c5d00e20801d00b003400030303240031a0420000444d4800070300460f0301412042440f4145010300c034800100480c1c54490700c00f80300d004003c034041000118030884040020300b01c809514546400e1f0302400d42a00320b19500401320601003050031803420b001c1c06400c8000554002000e040041c010001040f02902950000404486c01c2c2d405401900c0780264283c050400c00034076484410445801c14001000a98a01c110b26010420305000c1d64000b4050010021051100c80301d89521244201c41100421408802044080d405100f03842081c240c0c4d4501c0e80351100e404038003801903e002041d0318010340d604c070100149a44600c90240f2500c603040950300c0422103160000e00380341903a070341c41442041342c80b0000eaa060700305400d80b501c048068006201400c85244158003940200b0f0402d180c0080c02e2000c000c820291910a0140c40c6554549a862254039000d110a560b00d0f9040b2a0506080100180c82034032078400b2503e400d14640790003e200703a41418115000700800707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 441965224 1250 441963974 441964007
    0xd1a0405010803090a050f0603042414010303030507050309120d0209090a0e010b030d0c06050601271509030c0b03061804140705121b0118030b060f01050906040b070201 74
    0x40300119015000100416401400300e030101e07801031759002081140256000da00303410100c1480400c000a103c4074020b01411201107048100708450f045001c100c0d00802c0c0700070340d0840c1c0d070300041007899054400d4a800c5101d500e4040c0c41c5107094010f803607440c2d1840060980070350300098009a00180341d81643d402910080c040200da0800a4207080a80348140a0820a51800106084a01d000140740c0125000d81d19049920006900c81d1001000e004005034140001e035041c43c0c6101d00d036041100a5a080981c1ca08400790910314500e050003168040c0780107005604500380003080815940c10201c403034850300305a40c0e540d680c011031113605140002c05105e060355010b020400c44002400340a4071004801c43e1581c554501c01c12080b000760000360300040d000004440c0480320594010070000300c06050080d009001900120302ca08040d500984902c1c04d00710501406150903011094818002d06e022420241c0050001d4158071681c450382d8508000010030504590040542450380c4001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 441966474 1250 441965224 441965231
    0x140f100902040b040503010606020309090c0306030304090e250f0b03100b04171b090a0b0a1806061403161119030804061401180f02090603070905030f030408030d1a04 73
    0x43d0090b41c042d9402c107014603442942059000300e019880002030751003420005007450200c0c3c8410b691807a0360740c8044e01e140c2e0540410000441e041000740078880300302242000410b0b00120040d01e030a00b240d071038210200b1001074801e041083c0803801c664072040d03030207000103a654ae458011803201e03007900591040d410010302180c0010100045400516480345038020340c0c0707801d811400c90410190807890920392110b10f0b60085180c1c1c65440c2c0c8503101e0b120010b1b00c05480591120020305031110040d101401151700c4030014400c2942c00400c0d80c1c086003101107054150b044c4800c0d00c0002e146140848800c0020002d86080010400c100c845695401c0340418401414907041c01009507038100c40503507000f42040d42e12403072406080e03919030484613036410031609403109040b040c01510004208075a516024881a0625900c150003140940c040752910441d081c50001891b0510314140b40014164000344030030869103001004450038030107942e0000421410391400c0301e019a03024042e50780c02074034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 441967724 1250 441966474 441966479
    0x2102070c03050703050f0c090a0b03030c070f0f121a060a0e0a1b05191112030a020d06080307030c0f150f0509010b040c0203040905040305070f030305040213140f10090204 75
    0x8902da80a03a4040c0c015541a008403d06c10f680d500c100442c4990051034100c0010501c0c8c21650166170030b91802400e503490032648d0145980390284640050341e01c0019a0030420100e5155000d0400902403108805403091481e121054440005074607103c8403080030380001c159941d154080f00103407840c01c0040945041030498580100300c44d01c4031880c3c0000c0d905180e1040c6000e072090340d50007014640c0d03e12110030141401c44241d424031000e00e1861081919001e81c10f090180554440d5600030030041e22038036407111420503650503601c200200d4008012010220364030141820040e038003c40e100255415070b1130105541c4888111541015260200d10611249260032107401002900020700480504a041100310361003041d198015a10070031081040e50300f241c0080364400c0c0207085c5170f407c10515848800c03100c1500c0c0340c218002a030791010082103290552919400340c00340d8404005880800b58107000c01c2034050825a20600200005540402c0200c040f401401d00c0070380542d01c1c0c55 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 441968974 1250 441967724 441967733
    0x1504060e0103081809090303060112020c010216150203010501050f090d1a0406050702070602030a11070f0b031b04030f02040f090206131412030405090a0b03060c040302130c2102070c03 81
    0xc212810b140f403013004101c40c0e00d407680340c056542d82c040c180840145185442d020019218283c2441ca0710303400d90307024000c90000c05028809003d50843e4138004e03481c4041c186c03508202240d410600c0d07024440c41440180420b0b680030090324170940486d464680c0e00d03124200007504140007210010010070b1002d10600102c150303026514080c0e03215140074401a1120001079849140c1406175600680c428403d0841c05c03849084003d0701c41000c40d0981d4101525454104075540843d0411440c1003000000c0c0081c07003614a800c40e0300c01c907015598508007402c1d903841c421480d41162019100380d40381e0740c0030580040150703c5400000d500405007940e815a1100c41d9450310300d148200c001f83d405800c00864541498400c00302103400c5400a107151508000410400d00c402824860003281c0d5030081e80c0d141e4508000450290322004402510389180d0301c100880c401c035246038191007504181661030341540028041c1e40303094214008500e6417030306900400c024000d00c000603160b450b0030a030000900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 441970224 1250 441968974 441968977
    0x20c030105040f140604030509190e2818020103020f1612020f0a15090f0501060810050106050a090605030c0705030415170f1611010c0e030d090e1504060e010308 71
    0x551089804d84080440382d5403954460004680150215104125800301c0d89040484015010344019008034190b032100702065254004851845d0b545044580300c3d11b00c403400030b603510f0000060440a00c02d030b1000442c18514951401c1c3c0003410b064000c03c02640c2c0742200701c15181d4040c40444d80c2400c0091780c0c00e00720311b9042603040362805806029010160350318007046400406411103010740d404c80c12140b000c00241b05440e01611780388408404440080d8081c000d50700108072100050014491103422003040f83c8041e0b0114040c04020001c1c070148581000f0300c182181c4803803d00a40f40d550750315580c3c50b144030701040208640400140803a06403107003c9401a503807141c0e90ba00401440350340c0e0210270213030140c0365140340b00c1ea2400040c080504005122004038075514018407800882c00c200da00b0368110700b02002c045030703c6031001c504070309040125080d155010703c1d02c003001c189070070078820b49404054200d0345260b403004180c0000e51590b400070001440304038020840d560392810a500780707 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 441971474 1250 441970224 441970253
    0x70e03030a0f0905030304061d0111160503061303020d0e030f0a0c08070506040b07061a040606020a03080c1905030406150806100803070b060904141902010915140703020c03010504 79
    0x822100700004c10a401c00000303aa0a460b00d5407030742e03020215040d8a801c03010440081042c10842e01c000100140d803028030058040d001c02100d00c50310141010f041505101c80207180c030982c600c11143c81c0001c41e9002440d8000d4403d10f051400004c1c043c440464248105d04580a40c03500c10192079504200c0314144200440c2e00003001d84030042c2c4c552003004400e01c103601c250412050244159070121b295a80045000b00081f000c0d0102d8000031b50104060742c40f682d2040c4090303004810352801745500607103200d0b8025241d1491524018ad20b4041041030701d0b0081c40c500400c01e01100240400c00c2680c4102920411001d1080e02c240c1c2c1e4084c05c1d50348007821554007018240c001d1000540ca040001500c50702071b40140200b0469072440c0502002500080065034140307510356504959050030700ca8014070801c04200f41010003080e0001408031091548150741020000008800715507100c00003100b5901200162035845016007002c070718046011f0691641940782506100401030150f001d03290 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 441972724 1250 441971474 441971477
    0x314040b18030f1e1e21040b010602011d060a09030e0406080d09080d08070503060105160b01090b01180b090315070305150904050c010318170c1501030c0e070e03030a0f 74
    0x211855420008641d07008244c510184041821104180c0c00003840c0904554a092400c0b800000e10808000b612520147c2d4161181e0005130014008030b80d080c015052030800d183c2c580740c500b00c61210690340d1003000031310810045a82c3c4500c2c0041610403c00040c01c048000c10500070f140e11000c0440d207824404a1080110354070303d800103805240484c10344c050881c0c1e80c0b2451110f9030780890a032600e52004203d00e04000003000104ea10b4410005000ea08501070b4160230f00c80d40c10214400100c40011200b10b0500007210748800c125600042960240c55188603155110454500800c3c0b52070048a420b4420442046c10031865a80c10741c80184100304110b259a014190242480321301d41081c1c1c0c02030825040700e91448001e501940010071072894005001d540d4144544441e03224925004100c50403480001c0e034032900c0341c42041410f003920700c40b0310410810f51460b5550900e191840c403e4000007280c08002400344c0740140c11002c180d41d0081d06503581c1d070101d200d0050680100828810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 441973974 1250 441972724 441972757
    0xc0c0d05011a01110d300c0807050903070515071a07080c04060206061203041a031807080d0f030f1e060e01080c01030b0604030204020f0c06070314040b18030f 70
    0x1030ba65031090b000130090001000180c00da50200d440c040740d00d04140040b402941d4480d0711a4035805820304006240041032107800070b0402e0a90780020011240607040f0f0082000030f0081d00d004d40e8010030b07100b0407218125840480103044080e010030034040d031500075200005618103000d00c13407041500c161041041d40d5620a460350b4140021803a4001da000d01401640004001030310340c10002504801482c41c40d00312402c065a848150b010780d0300201d156802841d010007071049900420101c0100c0040400203449030358107140701d0660f113081000e08181004500340b10840440e00070b030700600d2046040807051000400c4202c110000b46030300d103a20084280703080000140d00000000c003d05030b6485501500c1c00c81008401100613007107070310849900100800000005a4592006003508050340101d40d4a803115010014207212000700144145400c140c440188560203124403980306502508002503a115500301424107452100003509501c00001c1c0040304241d00005086041203124959 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 441975224 1250 441973974 441974021
    0x151f050103150905040203070b1801110304060203070f0303061e080f1605010f12150f090b0102030403021314040528050c01032708180d0201090b0c0c0d0501 69
    0x1181203030382890b504070704499071000034400c0044640080b5003250004040300c406c0f81d10303119002c1d020750102c143d909650000c10881c20065800440c00d01c607400543c40998200761070848040d40340e02c600c44000344507a4484428000301402584880044d2030402e0310340e0102002014845862070b00c900800341c00d403090b40b04842004070002408050005031100342c5030f0300c0b450300006440020702850400103000d03070000c09610103201c0d441303138090070762000008219480c50f04558402c100c1c01c94018517841814007002d0b401c2070760000100c8040380c2d81034503160445640c5d600d292000340b0b50010009860955001440140040003c10340c01002c2020310019400c403086d0a030744030f5552000c10060541d008410150765540c0294000d50782011141c208105400098030061406002c007403044405041c0855501410300503025240c0d13842c9001e0b1940e8404811680001e003031002c0501c038070b4404c5c54000030001401d50b402d000303007000894058000c0602007520310745107010700640108007002600c0711050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 441976474 1250 441975224 441975227
    0x50307111804020f0616080c0d1709070e1302040203072309030c09130b0c1905040b031b0d09150507022109190b190206070e12151f0501 60
    0x5a802250700512281691494105018160f006080902c00092804030a9004031fa1a000200610705008003d05480409084003400c2198250312415054807100700300300e020000041c2c0c010640356040c00c0201c2e150344290150303807a949002002908140003000348407042d9001101c504c0c0e6090754402c92000c0915035030039034000d4007030b59940981c59444051501c11782c0c1029413905421010080d0140000007080e01c40800344001521400e000c241c00084003e80b84405890106501640e0325100345050f03e8881880743c02d02010b0000d0380444420b10600c840b541b054403c941c404101c4c980140308200640c141904654002085030205509101c0041e90740ea2000c10107032034000000991942e6400700811080040c3c0080c407440d60001103c680c420a061242c440a10050034810041c40da50b80b116240c20810b40c00c00c1c0c1a10096504c8001406800354020708010740b0b2100940d034050310307107409503c01031420081411f440d20790300000c4288114800d04c014142040c051860005140c141d85400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 441977724 1250 441976474 441976519
    0x31009053405130e0f1b010f0c020120060a020c011103010e0403080c071e11150a050a1206030501090b2a0306010c140f0706080903040312020a05030711 67
    0x14020540c07500d4100a02241c50300e14030350a5075001915002038018800c1802520302030150000410590040c0389000c0d0010007070380101e4240c4c9003032034103050086080002511580410310021f051101000c2c040020031420880c00081800d0081154120f060038078055000b5400031210701055400d0400d040b05003800c1900712412658015180b612030360b035030740301150b11182c00741004510000c204030503030200308181810302c1102c07620048882d4070060352500c0c110989041d850756004c3c01248014602528021085d00e1a1402e01e007002542c483c01458111211050140d07403890641c908140130040c403d0542c04021040c0c465031517000380d0b0700c6004548049102c21903e4100a0324a200c0f9008515450030155401c00010305000d902071039581d80e851a9026000032508007076000d4680a418540e080051500800b0300c1d0602c0c0b000b40c00e003600d40700c1c2c80b03100310b0001414034600420546000342c420400251001d801c542030325105c5000c1e00d01045100b241d1940c2c28402c035126040101d03140301500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 441978974 1250 441977724 441977803
    0x9090e060106030b0102070801020a08060117060d03030506040f0e0a051516030f0b06031e0109090b131e030503040308070e060901030515330306130b03100905 70
    0x10041400382c0c42c0501c00c40c00703448088415811406058000149404c00740054001c3d904c494071103101510b010300005200e50708070300c1c07031111303000d4104203000003602da503800e4004040e054600410360f6075408002c81c0191083c4151540c585203050101c40d10700a01041000c6402e00c1030058504040e0805580e01d009901901e4045002040542c0c02e098140280c0c01500290302403600032a0307402100c40051002c1d0000c68244e07000803480d8100035980c065003111140949a82d020801031203202d0b0b10348170311800004010020300c0700921025401d121a85800104d034040c1c4240e60030303445545207001083e035001501c0880200d103813a40450740d003a00070440d9200202010f048541044a0311004402400014000707015403000105216925141d1040d40e100007941e50b0800051141c00d24119075600c10030076042140c85c2003d00510004c1e42e51960340003482088070101180c2c407800c89000a040065a01c00d41d05050f00d0100c03a80100a404140442020f0221b42c0d0011110b0900151704e800c085010b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 441980224 1250 441978974 441979001
    0x10801110301030c1e0308041806080f03071b080109050f06010909030c020613080303180c0904020a17030405040c11010507170c16020402040b0403021c201801150909 73
    0xc5100b0f1100004c82052441001603141810100c00d5481d11f03202015400342e0042d0105568400c008a205061401400010145a4010b0240709040c51003181c0300e00549a00502403400c0b2442c03850005400140c2c0030250980a00800500300c6518006644010340c21b00449a070091000001d1342c42c00030700c181d51081703130591200d0042d1400342c3d0802605600107032002030440c00088001c148504200003443c80350000e01181e4418000e1020310074601002c00b1007262081d80300500b0000180ca6442d03900c406c88900b851005c025003000b154190950142d80c2206811914200300b00310920f81c8000c03100700c0c001e11340e4000c00c060b40307500200b15144070072440500c402040140100d001c03013144038002d20950400800040c0302012030390000e42130b40d029a2081a410b0000f24007172056140801400c2c07415041c1042981000c419591501101c4412501c0440d4101713400d880c0380030540f0b442240c7e1600b01d0014102516640e1240c040d44068070b012100800000c089810104114115210711403801c0d001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 441981474 1250 441980224 441980243
    0x3011d060a0308160c0b0306120601050f3a020a05041a1219050109030311040602070b0d1404050a050106050301111b120304030e0907090b09010e1203070303020301080111030103 78
    0x450b2540240c1e54051075645400c030001040010101784c0d25075116001e862259a0582c1d2410041d0800a01c0340a9681d1410035400c6a001040590b45208071444444803c0d2150b42c0b0f01e074a00d10811301c020880c03203c3d0719000c1c00c404c14010b8175284140c1926403410701c2256100101621601880212402410b962107814029450945549400e8100d400440410130803103011000c04260100c0030600c0350400c4405070f4442d84240b0130540c05002c1d4106456080c00c649090a1801c14001c1d81e98507507118036a409140000d00b241640c0701c0c0d4010586854071103101d034031070f81800d10f04181d44001003603040c2c0b0154a0301300302192600d41805030244d1051141c41d418140789540000c281c1c0384010101480e40c900c0b91001f0251149030314009140304c2e034003d0311582e08180d400300a02a80030b00003008003040220700401401000c1c140d0040d5900c840c1c0c06e1070402444090500401c4000c0350048401c4214032000c103094040541c540c008505984102e002404058000108031074180400e00008140303085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 441982724 1250 441981474 441981479
    0x60807020c010c170d0504150509190614040f15021e0f07020405070c0311030f030408030901150f14040b03061330110a03020304061202091503011d060a 67
    0x420f98505000c20702601c0000600300c04a02c40303680383e0740250300000031540c85204101c1440021349850003a1150001c00f440945019003c1944806107000403600305e40883e07582d0000d102065009008107000515200321900300340c01c21100c8100840d0048a4800c000c00310b03c0000840c40c0240c2d2051604201c8854201c64805114400b076003009011850820040c440d510169a07240106402503091762600a13000b192407d0052000c01c01004500081e0300030840c041e079900030401141e5000307130442010b5840f07450f84040c45000d0540d80c44d00c0901081ca221000c200f041581107000103c48000484000341c0419006000941d01441040ea030b02d0380008001034809a03150f032544c0701040c406d03800d040c542040c9022050403260a40700340c44000b2461142810036035044644d03403407483e903c00010030074554a079a00944d40d20482c042c941c02c00c0540d0a004031101060313010303038640031802001c145401100c40074030000c13a0024411610019080800c003214200420b100c01e0103128081c0c500d030841030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 441983974 1250 441982724 441982727
    0xb090f0714011d060a030902031006060509060c240108190503040e04020d060204090c09050306040b150d02040f020c0d091a0304080f0307090302210604110123030709060807020c01 79
    0x244540041030484605401c20002d540c4e0f00b2000746840132481d20001014a1640145854581c02d046609102c3d4a050018808a0703004800c1e00c500c000100c1d00c46d941e0b104c000e128203080c00203403405100300344002d500344540600606a4503042e555900216030044a950000b6060f40803c200e01a2260300308000178040d00a41e004020350050002d0201521006240d03540c2c0d0483e4440ea004c00000b50b0760301c0301061281e600c052202c0007800c0c118000c1201b410151122038841c14080e10550700080c4a00c401c00755500c070414911251a0020400c203c41020f005141000c0c2d4004407001c0310b280a2103000340ca4140c0203001e0f4070b00303854504069031a4060314151440281d440a401947c0c8200180803012540e4816802148a0205035441a8043e40345105001e040409240300c40d00c60000e04142002c6035400290303599200790060349040300c00d4074660058a44203060700c1c0b03488940c90700c5048100443e0409c401940502c881d03942d41c1750000c0ea07400e02100e80070001d848881c0140c1000c8d0104500b503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 441985224 1250 441983974 441983987
    0x3191104020c120a0914010f120f0b04090602031005030d05180d0c09090c06050309030a051b1903022406010518040f090b060307150f030f090b090f071401 68
    0x2810381c01262628661200c00f0784003034004203003603130000340500400d0203041d800d5004190170303400030300b4004000482400058180141c0314140078800360795154418205400d50000543e07104090400c200108542c00c001019500c2207400b010600c3c601b000c00240f41c1030018141003402034a96515080c0649154001918040d01104035804070145206501050001008100a0124140c00208520f031071600c600d0002140d48035806220041c0100542c10301d0101c11511550b0151a103030303640d00301e00d030142d8501074107012401c0554403450340b540b034040c40101e09061405020390200d5168020380c5021007101070281090a2000c054640800c07800d5020b00040d08440804c0a00110307104403c0002c00d040310703003040421313811a4464030365105000e0325000e0b250b0450410303800f40500c9828041c0b041e500902c54180c0000f0059100a1100f109100303030307c003180c0940010f509001e580030700e0802d0496454240c40c1600903002e10322003494131000002e42d140440701c2c0c2011050700041c0900040d100c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 441986474 1250 441985224 441985237
    0x1506010c051f020d0c020703020303041401050d05130b0108010c05070f02011106070201050610090807030b1305010905070e060613031e0b01081e0604050c190312030b0319110402 78
    0x1d0380b288800d400300554440c0d0012010358900c802c010384642c0c00556600580f0038440130720055400c080001e101584002c4200c50665a049007180c21098010740100c80c648210428150002d01e03020a00c01c4e01c1c801c41000411090090219038442d989a4440c90300301c608001c0c1000c0802c2c010030003200010b049005900f07546005041c8280e03107001c6100040e00b45402201c1400c0140d551344104403041c41c2600c862070403040e052400c000c10a0074042c1040d520200e034040500780d1289500091481c0c030891a15015982c2c1c040c0c003e124540b01480c00c1c60340c0310883d02807050440b503450001280c608000e800d03034880740b00300034448220a24507111990341c1140800d00d1514081502c61980126028031170582c000c044c81402003503940329903002000b0b01340480d510b44440303804c031406000201b0400114403128400854206003910240e0711820201c42042d170000301440032810460003a103801d50f2107080b10250a9003a582e146088049200c0c00780f040c010000c0102c040550740d44000d04096015220 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 441987724 1250 441986474 441986483
    0x90e070302120f040209010f050109140a180219030506030a0605041509110307060f05040b18090c03060906030f071202040204080a080304050708011104290a1206081506010c 76
    0x6410b28003074800602d003000b100e103000b00c2c03100310080c003085040c01c2e1182801450544405c1c201107080400007450001203100d0030300d0f440a0410302d14201d03a100711210000b440034040800240d1003402003100690080c9900410588880c0040399200b4024061144252002000741040410350350b2a08002c20010304140d6662513000c0c0e00a0364050a8440c0f1034070a8001d207541401c450590041520300b820b6500302a082007038000600a9694001040e6402e4918070200030781c8030442c81030600820003007000c041d42e00c80160014026600c01c1d020046002d14415907104d1541d90f00d807c20716560700050360500425a000820404c0380c07101d1000c0002040c0c0c8000c10261074140d07142c02c035a01e000200360094529407000002e000c20020100480001000c1c1034000344044500394450103491f0080d07205842040207041280469024241c91380ca1844240c040032686450040c03500400c902c08070a0005403251030810085250100040c3e04590100001600492991420011205140340c01022034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 441988974 1250 441987724 441987727
    0x111b0d060c170a0605040b06071101080c0f0a0806030115061e1101020705151005010903080306041509051803041401030e100603050a2d061a210d0906090e070302 71
    0x400c2c0064580c001c2c0a42c8003010040360090401c01013008840b46120000d209480400a540008103080c18a240c414800d080130051982c0345201c00c0014810140c0d0300c02d0340140000c928006982100306540030340740c10341c0200048000da2054108090b002c4c0111004200b40c4100d2005480c0c06089942c142c540500c1c00b0b500c0001500d62050a82c0c0203c07204641c0740e088404d120611980021082e03610180c855860060340380303440c0002e4003018080c00f01405084000000400c192503d421140d01380c1c074109560050355a0b2000c600000b001d040d0780d0524100480484486400f00c0041614191007121505103c0c3c66120b00041d001806000d40c001c0c82030241a00030040c00040e441102c0085006601030300110b0070f1440d003d04c80890b1050b2243c421017080d2000c070b44c001055a400007005610210000b07501c0001482c9010070b00c440150140e200004905641c91000000c0003545100e02140403101d4034900d851094514600b5401942e000504180080060301c005440c5950451010b080c0103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 441990224 1250 441988974 441988997
    0x140a080c0a030b0d2a0e0a0203041403030405150c0f0d0f09050d0203040f0504062105030c0a0302030403140705060a0f09030c061e03180b06040b030706111b0d060c 72
    0x618062000c180070380c0c402c0b4444641d0914031983c007080e11080405d401500444500703101c44450424009400b80f4202076000c00001c041207400d12142d08001111802c40b5100d01c1c091030955914964400c8100319100c6405c04249007601c0300e01940d503d00039140c90399060040380c0051400401c0051102d85104d41c0759500c00b4080344007030100c00c904141e2680035641d12414041001507001044e170001d40034528180f020031080d4030300e0040c0414170442c00308165185405050039443c0d40250404100203015400400c420950000020402c80e0b22031080d510450440540d82502c4000b14400e854100c60200300714021148035290f072036610142030500d610295103c2c2c0395004032a402d60007510110f40c0d032190f40c01803c0140e544488550322589428026a0840345c00c2a0341d9100c1e42800801c10035417040410b04540d03845e00318070200d450203401c0340c07000c40e0b60b00030040c0305468040254015004105a00341420a1141c4010340400043c4c02c014032080d2030358441008000c0480d2400410041070501c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 441991474 1250 441990224 441990229
    0xb030304050a0623070f1509060c0302040311030a03081305070b12090c041e0e03042d080105060d02060a0e0901090f06060203070c0302090c0c1c140a080c0a030b 71
    0x40c0207003c881c0d0b200c4440321520f550895507090360b04036100d42c0c1d0b001403140e4400034034010001485d03a41c1c403c901d0900304007501d00304000340540300030050110b8100320010310350503403590140084038011801411038000d03c030309046d01c0300d420601c003a0001c1c002d01d00041482c50045a07100c0010310860464208954400f05182c054021007243d0300700da0b40503c01d2101c2c005040010036031319031045408104500f04480400c41007101033745c40030b9066403030f24102115114140309840c0200030b03170100d1072008461140f0161070140080d0b404101752182d10800319000c01c051140f1442480040c0400300e11a020350204a0b075500003c14a00800a0700c040c9c24075030f61640303811a402000514008900013140c1407154040d20010b17049402154401d00104010483d8824408122501500c8a10b1740b03485904c41d0401c0c601c6130000812840c4640120b41c5d04402c000b1100c880d400d200c1c0c2d82ca0040601c44500b5400c0c084c800e512404000910345c2001c5851040703001d00820446d015402e00085091b5203901 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 441992724 1250 441991474 441991489
    0x50c030708040e04150c02071403010b0301051501033c0b040e0a05071508010504020a02030906070f1a160e0109080f0a05010609061505030405070e190b040507020a02040b03030405 79
    0x2d10a030f102840140820406040040e2402e580d00d902c042c00000c090000003555150305106511496014400d0403d0685080d4481349000802a00922644c9080c41d03629004502c408141b50000b480c1440d500e41e0302c82052000c800040408103580c0040c95181e244080c1c0b0300201c000c1c100f40300d6a60b0171001c140d60f91440b6044168803010040c0c4040740b111700307020f0f08052003a0f001200c046040001d0602e4a603115901a040d80d004440040c2c55500b0114128a1f60041154031074220100143c40d10a001a0b508024640c2c2d02c20010002030310740b0b403120700050000a4401c0c2d41d03164180d03491204018054070041c1d03c040018508004016551980d562400c21210b41c11945a04004800c0f8148a828050800030b0f19901805000342840c000f008460740b0031441010b404c01802001003420000d050040750000e244101005041d03017059448142c01e81c0c03a00500c2094149000803081e17060030305000c0c091050005402a002440e0260207000242032095060b44c0c2c580010031004c42c2c43c1d5107058 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 441993974 1250 441992724 441992729
    0x90201050912060402030c01030e0d0c0c09020c210a08130510060b071a011a0f190f080702070e0118200306030d020f0d0e0f0d0302240115050c03070804 67
    0x30020003044c10540103250400b1400129103041505042d2002128000062490300074034061400d17035072080c0d080c108032003c0c80440c1c10000f02c0600000300c50000d54000140107114034411510ac00c141d0303c040c0d031084600e21030200c030500428500b0340080c9010b05030b481080c01e128045c4044e01c41c1d009501c545081281e4064005500710300340880e00d03806004c0c030700a460b0002d0580c40c01d00341d669410550305081400e080c40f50130740740440000d07804440306a0403060711071501b9140741c4d502c0044c21001c03016044480944659000400840c0050103e40c030000c0c003401241c148103054032030341e400e00c03841e0030650750080450008180c0b0b40d040749106070006182800103a07032084001c1c2c2ca9007020400c0500f0495488046021548110491403500401184c0800002054245090110b0040012130042250301445950114141d4104000c1c15000705016201c00b032103403100320b42c10f590210794a0074650203014a2615030000d094404071103014000070810b04000304201ca04152141d603400c407080d0300c2078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 441995224 1250 441993974 441994009
    0xc0702040504061d0109020d060e0304030605040506010e09030a0816020f060a1b02060c0d02131701050103170403051b030102070f110102010f020c0319090807091409010c0507060902010509 83
    0x180b02c50100c1c9407020313008007000c0c29020003d2100312142d4000658142a40c44090041c45d92001d4404071030b001041150300955008006005915050a007540c0360030091003002003c0c00844001149081c0c08030803600d07103240b203071250f13940b81d210a00340f411a015244465415480f59001c00740f20603504101c194411401150040740c83e401064a09404a100d6400c01081d07500000501200311090016168a000e0940005850300c0755101c40a0a5002640c010341d40ea40354050517001280d019000281644c0c066081b0b04a0108002000300e6603208902c809070194010b0b10301024000d00fa40407640310b4180043c0090300709411a00e40e11800d0500720421150f4501c0280c0d5a605960217009410351409020001c50030b0660030080d961f100e202d06409181d0030a15903680c02f0b002ea020300441d40113007164100b182c088544480c0c0305401031005440038148028001d00080c0c1c001c205010725080102c6940d155030409503141d68080140c00c486200324140f0005100b1144e19450740c03a100003031719844 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 441996474 1250 441995224 441995231
    0x306170109110102030a0507080c1603060c03200a21051906270903140f0d06050a08071701110f04030b0a0621030e04060f0806070305010810050c070204050406 70
    0x619058030440c00b0540941e041d904203009030017982ea044007d80d020560810b1842d5550055181443c0c1000003880200d01c810403c3c000100c03e01645a105416680721500c04001506000c0a600c055100c00f400070010003034200071488003e03105000b12522032139088060f91054040001c00c00a45000703d92601160810009691840f2407500030580280942a45e0803502619030340d1200321200c291450760300701511100000d0405118a403410f4420544812682e2103188040c1c503c10301d031303006000c0118810306004011034603140c1055400125001f03080103000880c549459040800300c0c0358401c01c40340d541e50341807643c0c116040000b48503014880c1507142e03031181107140c400038052018100700e141c6031520b5018442d0079080e40403014040f5044840c80240c03042e07844d0443c2c40d0940072454a401a0910400107505c81d003030f81e5a02d0564140380306955107a545c0400480c00c4903403d100c0c101c100e07400205040d2014802e5444035070815240742070940340c00070f907801040540310706a03802c035065541d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 441997724 1250 441996474 441996491
    0x30c270518100c02030904181a01090c0305090607030e0f03030f01030b090109020f010e0307050406090218011d011404051210060b131806050d08030103050c010306121203061701 78
    0x902c40e081070711003828020004400e441600039500c4c00303215095402907940b200312082803004001070403099603100c141000a408440014240d01c0800c0c811203900c2030900c1d00001e2a503000b80030301d034400c0592800802c055652200110094508041100024000d4207a071020301b60080c00110f208000c011070311202c9514500e03200e07962030f00c0242401d841c0d9150090210050b0b540d590a0b041c902e2092038400003461a2800190601c501e582c030441e440f500e08440024010801c0c0c000e406481001417200c1c40d052251350040d100e00a400310000f081500c04071403c8950f6001705900e00c5a1a02d81c0e02d02801c05841d54042240b6841c040021812584207403010481d8924034040c06000d020b50740041400d10011104c00c1250301c0c4140660703600f80c40280400c204441440c0d014800070000200401d10145550030503a034603900a00080e0b41c2c5014031402170703440354081d004200841c2c03150080c8001c1d01c800c43d158515030b2201d4901c2d144c100b544800d4000781c82540010203510079a0070340c000051401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 441998974 1250 441997724 441997771
    0x304120b010f150c1e060f1a180411040203040809091006020d051605190c050f090a0b0103090203061815250201090506100501120501030c2705 63
    0x141d004502907800398034280043c2050769004080a9807030300700010035a00c6403504000c13000b0903030038200c1c44041d4141404203202031500415050300119100704000c800c041e4240310300c050003103880794220105c500d04080d4a611090210341c86030090000d0070b001c10710355000805a070310954050380c00f0000400d00031398a14040303e0180c0c016024040b84c8580510740f0a0281d260682040c90303401f8881c002c1003142d003113844440d00c40d10003a40300d02540e0340300272008103130050030300100003d17100f020f90a43c01081c41e00300805082200c0d139000f42208955502c84d18840040c01a0180403410140c41e06403240040c2c0b800c004141c00b50218810b80b49600310202901440e0000100c034212407801070000380149003c0c160300307840b0340071016408600c41500b200340c00d85c0504400d0400901910482003081036401d5544000801d480b0b003680c900b84159039219121081c0e51083c080a04101c00110080040c4003540540d41c142d0307141c5243c8884002c0010703860008407001140c40c0901004031130b10404108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 442000224 1250 441998974 441998993
    0x9050c0a080c101b0f031d01020709050a09140105070e0402131e030b01150e010c0c0b030a06170c0f120a03080711061533090d05030412 60
    0x114000d85a10342524544441555640b085414103400303420720600300860300d0f1007032400c02c0da090320203020714014030f4507031509419420500d20b0035000a99480c0d00c8810f090f001c4c049090642c2c80c140d005285007410801100001d040c06041020001d035203115040020f00c69940e80300416010200000ea40d280c05400504072605444250744a14410841c92411000303050014050700c4918046000a59080c0d1a10310030702da035030304041c3c141c020400002407628150030a031006c1248555419000d000c0d90030040d2014410164000d0060210f91018404658910040d507401203500c18045480c1e9a1409000070842000c80c00c4a00b982042a4000743c40c10708800540d90700c0016200c48820118810005032282c09141c4000c04110b0010003140e20f0520030100902918942d90594016042002280100504e0381c43c0f103a00840703400e05495000301c410000f5640c0100d00000301c2c158205114034040c07160344031107902d60b40840354800c0b2001040c07040000e40080d00c15150310440c0e1001030300700700003d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 442001474 1250 442000224 442000243
    0x6041a13030c080d06030503310b0d0506060f0a0306081b10030e0c0909060702070603020a2001020c0303130b010509040201090605161b090e0c030c1207050607060905 73
    0x3500908a1040000c1e0b00000710460301d600400030742d48031480144400080c00300d03a03101a009110110700000d8144141034242003403890705102e50301e040e40b215800f91544150303204078035004a00340800700c0107060b80e800a61344000300800d81803030207908029440c5e00d41c100a502c60002903441e0130070b0050341c0042108d425159500030050100352440c0c400640c04513407802d410000c054644d100300d1360003002040200c11220300202030040900d0100519640d44100b155641d0040c4610280010202e010744201c48603400c032944c698034142010f07210300c10101001c1d031410419640c20041986403a205101131070160201d2038480c211206c5a05019001403810b0b003000d441002107000303000040c2e0304029080c041317502c182045034a03a0308540c585130540d814008050000e81075948912900b16031481c1050980c4c01400c0c00b000325101c03c2e0480c0d41e44c1d240c01110160141d1003405100600d14244003411256130341001115280382d1a0b05c081446038024143c00c40b409a11415510b08024080c46080324 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 442002724 1250 442001474 442001491
    0x4030512030c09060d0906020403060b09161d0109030512040806090d09350105090f07260a0503040b040510021506011103090a030f02041404050a06110c06041a 70
    0x460801404003800c0c3d208200c007051050000144121815407982c02610f10342d90456011074449949007440c0c1c01400303000c455140306100301c83c00607182100d4055072030000754441c1d980307030086183e510130b10300900e1a680040d41400403c06c00000001c00401c040d541928026407103d48541c41d10000d00d1030108080c0000d0110f402c400b103008001540007140808032040030201c85401c0320300e42e803000000072140b0300c2c1a03c02910140c01d2074441c0310541200b03004038023300c129140010420300594540295020300c00c40303e6a00b844440b00d0044110007021503030100d4080e030714403940540c0c84514662007680910105000800e0401c6240ba254420f900c94180d6800584a40c000c250340800a07a40000c000714107001003e088190819010400c0d500f4030305000d0406140340b0380701e0414495800001100302d1049080012251120034aa5015402164800c0c0141280c0f109507441001501024118000c004010300c0404c040d4242044101d018030b0040b0010640ca0025080c0200c0c2d80000401000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 442003974 1250 442002724 442002727
    0x1d0c01090b0304060b040b040c020115050105040b030c030a022205010906091d09011b1205010b2a0a060515100206070504090b0a08060408041d040f080903150c04030512 74
    0x20180401c82100d510070b50084002030300b1000c10000034010000100c0b256049443c201c2c400800b0750b015803003100b86c00008009407141a0790342004451500c1f4501911801c80818000703e8403c010a2000c0c58010424007805802c051640c2030581d17410385103200da4000b149080400300000d50708031008401508052030074040050518104004102a0000c01e41e8041c0c0d80c42d00003040c4034829802030b0703040c403482010750b00320071803018005016a120764034503464a45000000611840003008943c410051109003041075050f4150582d4040d400450a00c0c2c2c6008424040d00010100d00c81c1501c51040b05600000c2c81c3e144400b480075210050072140107540c082c0741031021083c3c0050640b02103600d19500887c2d28000c40c0041104880181e00c10000c503c030792001e000400c5803c0c000350051324600e03505c1040140084011480c641c0007580c000d840e6110540032100451030b418007c1c1050180907040354900311203502141c0e0b044d80300b105c1800d40c03120085018020030505104048445d29a0309015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 442005224 1250 442003974 442003979
    0x40506060403031b060e070f120203150703110a120b01020607021207080c0d03020912120901050c241509040b0c0a12020301090c08010602210903070305011d0c0109 72
    0x384548100e010203802d005010045014a81301810206001c0c0e80c011414044114005e60b92039480e03080e409000c0740e846002c3c40c00b00d200c0e6203041e100d1000b40d4004000309468031a01c00200110b6102904500402d921060015009103200e0300a01c6048156512200182c4520103c0e03400c0301da000e10a05d0464004030144149583d000030390b0b80e030600300580c4d5107070354441500d04410729104030080d140a074000c41008205454160303016085180040d180001001051800f580d21074002e10752901c0c00c0801440264407551141c4060102e01c030741030048a99480e6010070300d2840ca900c80c03000c6050500c80000b00540f10700b091070380c0d22469001750740300c000c01c2c04c0070f03a240904a40c0043c084c1c9d01030700d40484c81280c2d1511500800382d90740c00c8014110f6895840c2c941c83c1c000341401c1e43c400c5011503408800050b07614400504118400c4115003060249480e1494060303040e404030030210380c0351284002c08808102c2c20310603010807480c42c2c1a990400042090b40600f400f07803132201c440c14090900d404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 442006474 1250 442005224 442005229
    0xa060b070203100e010f05041208010b0f0412030333050604061e021c050a020d0518040b06040504060902090907020d0816170c0703080117280212060a0b040506 70
    0x5000b41410f480106100d503580010b0741c0185800805120450304110903c000d100c1118050800c114641d55040f91076a202c1e07e06502c5445075440c0d449030800204010040068100c6009031514428174010442c020383e148081120501c1c015000500141c1440b80d0080140c1541200005c3c031060710f6490a03c2d143c050003500340e1034004c584100c179800c02d60400030031602c00d010300c000929550f104420a042d80540c014407507040a00603d000d82700d00d80008444038003030001c1d2804200308032050881e90800700180009016402c1c03901e90043c0d402c0c0008141039803140103040280c595503038016110000d5004011450102070001c0e82075411502200158680c84a003641c1d201005400c0c401445040c600300305c4818079031403d0300300284895014084500361802c002d0110b280a6644d441e0780c3d9894012411400c5001c1c403079940f02c1c1d800894043d80d11084800001140d801408401b041c0b015103130042618220210704501c0c26400100c20005009014840d54440782e409450030000d0340380082c003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 442007724 1250 442006474 442006483
    0x1a01050a2904030c08030403030f09050a180608010e0c0315010509041e020a23040b100f0203040503030309010e070b130b0f0c1621051209130c05030a060b070203 71
    0x100c05420700c00c0c0403a4101400c5007412100110303440020041c545a4801426884c0d030080d000441c0054101701c044040948a0a084419281d000381000070080c5010b40c0da1182061887d04e01e0011511050001145c410a01c244999003407920003806c0030303c040c00101420082d8075224254220303150401805540c440c81c100c0359106a002d86005110384000103c84044880b0080082d03101d14603003400700322101030144903401e034100700150300810103290703003003009550008103001e82107e10250568141413007400070000d100304500640e0701d010b8807840800d0071079108031036215aa0703440d551080704280c801c0004200510a5410031400c22201d21320441c020700691042030615040401c071241c3c08000e04044651101169044070f0079101c41f91200403c0390018450b00503000e10020448900380c2d41d051000090a9101020301310007281c8065134a01d40c0c03c03010390945c200e88207865030152980b43c0c0c4182c50f51400c580e2507140d01c0f49854141d03241525503d410900070b00206004480040c0c50019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 442008974 1250 442007724 442007759
    0x3091104020906040b03100e01051c02011220131509062102070b09010b030d05093a06060605071104050405030906040f0311060f07030c110603041a01050a 68
    0x103801507035900e2400000b0300030f0b000e41c1e003200d4107503400042441801031200190300c003190400140b0031b1050ba65041002047d1011500c151500000140e0b600011362081c0e0f03070210301d01a81a800124294000c118a140003404100501400d6001401c800c500d1100d070720742c0b80100314125002d001882800b40051294209200e22010310440c5e540441101c040c403ea413086581c1110421910340a0a080c0a40c0d4450162201d03a61540b80008420903424080b0f082100a00141c035114948280042400941000c50b4102c0640d803030680c03411030650b00c9080c1441c01078110421915160521404c06008490540e03101406201003040b0500010b8240c10540388032071812100000c4030b0f6210f00780030b8158481d0341e400550003900010041401008003080300150390081c4d10140c0c2c154401d5050000e64803407122030b4085110148a010f000070f128890800d000c522600c0c244091384c01d40300c0070901d035400036142124040c0605242d403100280c0341c1d407070031b00505048550560f01894840c1001241c2640d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 442010224 1250 442008974 442008979
    0x4180c020d0503091e0c041b141602040c050a0e1009180b040c020a050105010807120f08091005040e1e190204050a03030309030206010605070b01090c0c060f06080d030911 75
    0x8000110590800d021844a030f801014005c18000e1810988a403100c80e160f000030720403450590120f035400d1001041c0c02034080541c42d803403860b0381070007405406900046100790740c20421446201c0103858501030618410b16541300c594944414000143c4400c107038481c0103005200f800c83c0001e025500c00381040803210307000700c1d04031003e060005910107849605086900103003050780e100481a4001009110207005400820190340ca61811b01e886040341d00c16441c2c0703054914031100100f0382911503d0744141c4150482d51a210000e40424807000d55001078101054003c981080008844c610143c0d00c00c45c41031018041310400d8840c920710060107015a40058200000d80400100715411140648802800303000f40035542d14004000d0107000108800500415000144250048080e02c0180e50b00c101c040f807080c1e0810210800a2100703400c050200000740004401040d001c0c81407101d84207802c4000705d2001d0030401181c1c0707007000035240e00c0c04040c0b4007955103020614041d040d2030030b81c408 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 442011474 1250 442010224 442010227
    0xd02030304201503070f02030c0a110307080d0c0b09060702330a06090e160614090d0c2303101a03060a0506010306090209060a230f04180c020d05 64
    0x4070402c1c44031140d11008503001a803c40840d1804642c44025510580c850354440c0b040310079034101240c480c09142130700845030740108104000907001010070507a00d8005004ca5105075940ca015034504020130346e80101050140904074144280811003c1d4046a1840242039074202508000e644080f84200c407030f04041003034146c0300e40360031041005542c950320198161705030400c4115000102640e214000c100c03807428500c0d00e0208004134800d0081102d81c0c401410305c40c6060340c148c0700898a01000d4880e2901000240450ba0750144000401070245160003d114107003a083c81c060900e05800104a80810110760203641e40013500d108d41c00328005000c074021038111240c0c0d441c801c0910303030036915004000c200f00c0c001c211640501d12032030b000d99090045950b00c4150070124410441c40b941c0040c810000c510b1040c3c020b00202640c460515180c209031940184803400f250071441329200b40050010f410001000b8110b01c2d803503034421031401005440f0807000040d5842d103000c206403050000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 442012724 1250 442011474 442011503
    0x6060f0d0b07031505012f070b18090907080d030f02090a0303020c03060c09150c01020c0105190c050403020603010b130503070810060b03010518151305010819030504050d0c080f060609090d02030304 87
    0x1041c423014000b005980900d503100c04411740701c40f003140011489240600c08100000d58495800940c0744120382d044805130003c0d00c440c0300100c1c040c044100e030710b08145808001d1400c05d600c2e001400c50042d80281d01410816181d5010582403c1d0080e02000140d0414800d0700c0f0709036903141040d0140b501030002ca82d6180756a0070420f0180c01184c29216180d482d11082224090080d00b560082800d0702d0713402c0180c3c0000d042e05032803a005d1408043d411150a00040c0402510100188100d0000760080c0cac001c070b40d5510000e07103008038903008802c10350009500784040f829180a09030141225a1910742150306080100b0b16440c0042e80c106c03080040d040102e02101a489055030a2650242c100948241800c100401030f0000707100f030039100c0c030800b0103150000c4803400d000315120368169180c516180c68141000a50802c000c0c0a5481c2c0390240c00002e4044010003d245041c1c000601038841c40c03800c4000c0bc165030704001d103d0101500714403c40d500c40303540403048a500c194448181418100f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 442013974 1250 442012724 442012817
    0x1a0906100c050a0606080d02070b0d02031509091b010c050a060b0d08070b011818030807020309031c030c021b01050304030903140c1009060206060f0d0b0703150501 72
    0x66030410103000340c014900083e06114803600180c0c1507440b80000c8810049011074105c0e41c035005032061032540322042c8903400d0050142d40003903410060010303400320f588001d0750000e140c0110030f56030011540c0c0120204501035082c001442203140003400c00521141e01074652540f955000c0c140203103250b5494144803596518051a6900544c00c0940c150b101e01c6686001010700701c0a0043d036800b107140d0b09030a084844c40e402100e880c1c8201388a5888603840f15038098070f40810103412139041d808180024101078804002c100010503481d6060780c2d08412200000c0c1c00c442c01c8090311001c540003c90020a0401c01c03400a81c0c0300c4c542031030816560b560703d040c12104a8000c0c0c000802d80c1e0407404024804040c005445001c0110841c2c45040b1141040c1051342c0d807007024814030005da04203400103a114a41a0b528680a14010304441c0c0c0740402da945090081d441203e4070f2006c00e90b40c5134014120501114403001922080c08c11610003a041c122400405400b48000c10712a80c3c2c440c160f03107108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 442015224 1250 442013974 442013987
    0x61002031201120b010905220305090301020d0b040b0a030302060c18040e15010902160f020d080c0a031b0803010b0a0e03071202120d08010e04050115060f02011a090610 74
    0x11520401e208803550b10b5511641601283c0c3c80190b401c01461800480c085540b403003003a00452050140c1c2425807940a00f05076000f010480540a00c0400e00911002d03441c00c0c0001c240d440c10115000aa00403040d080000300c50801e11102c2c0601c56840c005d0000030340005406400084840285807940382d0052031050b01a08081050341003800e100901d1a030000000c1c00300240c5482c400c2c8044280e80300c00a035001c0b801090a11524422114600001700301c1c4402c0690603540003a103428070750303100e6403550a001da104506040107513004140751002e1540c004110b60b405603005070303800100143e035207410b840c0340818020011581000501010b00d2400b80310002c40030400a000ea400c0b86a888078640100b100001c8141d00885000c2c20010a18101181d0110001d1064842045690070900f0102c2d000e40300400860707d0350350744c0043d0160810404110030081445a80f840c039541200d010003429240071130401c44040030f100c4125401680c82e41c0c0400d920520550f100b100c1a81c070f003034088540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 442016474 1250 442015224 442015237
    0x507021309030c1e6603080c0d17060102030703110316030306080714030a03051b0610090f09020d08030901111b15040506060405040c05030d020c010f0c020906100203 73
    0x603d00d02503001469a601401c0c00c00200c100c191161180d19000c644241e028582100800d14015210114081740e54050303548424403500d503104000691242e030b5420b0b072540176140240c00c542c40746125128899022544200c60b24032003c1341c04050514a0010b9940e0241d0382c1c00400b44140c40c50188008a0204203450380804507c900380541d6085042c0034008051900a0200d0ba002d05807012400d0809658101e03681040039004042c00c0780a0740f800c441940000103030700304c07000620070302514400301004458020160300040c203201c02d1910003407000b10303080200c100d0b91541c1002c1002000d0390390088040380094010541c40d03900d079204c450311801002c19072507880c2011408a0000364102401d209180c803082c40d20300b220301020b81e55400c00c0c800502164010001d038403060018265080640216400a115100c031800e070a40340d10000e17040c86400805a03005a01c01800b41c0c00713969022481890920003410000a103490030b8010880943c8010700080c0625200c6d400300c69158400c1044901c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 442017724 1250 442016474 442016483
    0x6020f07050d09062003070605090f030a0305011d010b070b070509060c0c0a05010207081009030c08030108010504030801051c240c050d23072007060507021309030c1e 73
    0x100c2c0c010b20303070050b01c00c01d110301540700041c01444e074010349060880c00d8250b907280003900071405c00c00c6a54413040a1b11004055031800d0003644860000035000304041d101c2c0e2035443e100403ea40d81040c010b4035a146509081c641d82c0d0410900420031407480314111000140c0014181d100c1d907490080a0b1603034400d00078000e0b0000c100003007040700700354003240c0c1000c5458100e40785108143d039000120382d1940240a44803050b0486107111a60790120382c0a44803003446801c0c5807110048a03107403000c560b0000d0303003c00d04594440c401c01041542c41401c99014040450700020000d4060743c66108010144070000d0485210f5000001c14a40c403038121442c18001c0707038044c002c00440c0f18009040e600220300c4c507400c403418660711100c40d2103030010018102141480c80007065a600b5030031201007000c0c940712060124518102d40040000744131744c134090701c115111a680c40400d4810f00500c2d85100b944124010b01d0b0510f80ea00207540107280904881d000f107005507440c400c00008a0701c01034440700013070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 442018974 1250 442017724 442017733
    0x60b1809010902010207080604030503070f02150705120603120a0f0e0301020f04060f090e040f03050d0e030c07140f09190524011b06150b030c04031202120706020f0705 74
    0x80c240300541014125500c00e07400e59441d1a5200340c801c0e80c8081c20755004000c1181880002e124a00c15504e07084070b071203103104641724900e41c4111080241001d58052000035400615000817030701d40d03000d40740c1040c3d00781c00030542c010214201880703230b00900d03800c0002c2105802028440511411200c1d54001d0002c0c002c5540d07860701401001994030a10520020030380b030500d1140080d0144058008aa5134602c5d8600c0582e07881da1060039062540e44200d09101c2c00b4880e2020807071080c403039107541591900007507568150300b403079481c503150701075000d01401c00b40302100c0740494481c03403c01811260b05482d0003900740c0303031307882000344888441e0100c0040340c0ca00001c00c040800e480b103010181d10844070706d4140d00c040980044030f2410342e0a120011200e40c10384a440001d4180c0d0000a5114040d900c10074107544170f12070101d450340195589407011030b000ca41841408000704000c100d1514900051038171080c0700c902c0740100d0107000006000f565020829508968200d0116008030368400286c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 442020224 1250 442018974 442018981
    0x30c140c0415031b08030a05070206160c051906020c060a020a0b090a030e12030a180f0803070b011d16052110091a09041a070c030e010c0807060b18 65
    0x100004905840240d03003456144c0408981012114503481c00c1e00c40000180d0b1411504220036140c42d4801601203821035800c00c00e8884107000000048041481003841e0790341680b40c20704008034500c00c200e00b01038801d5110f01c100411030b00044e0308050003400307503540741e01d60078407107020f90400641c0c04001d0005510b4000308404500302040341072200d4420740b10b450881214a081c0140607000007642401a4000c004903804603005010350001e1112050a0140107502c82c0003014160145600004281e13101294140c10009100d0059014184a44e00e100b11061000c0c0280d10180018206003c1456260f13801400301d4030450444248082c80404440b80c1e411844c5200c107090800c64101085400c0a400411040701900821041200b08a0782280c4641103c00300403103000003034400c81d500a07001110501108200e095039100b03050341d03191000c1c5880d0b54100941b121201c400003604000e282c0401000040b80c047c281c800082e0001c4000421030f05000100d0102011500f030f5080011502082 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 442021474 1250 442020224 442020251
    0x11030c1207170712060f0608031603030e0105090601030f0309081204090e12341209080f0d050a11011d0c0f0a03080a02030403060c0207051c030c140c04 67
    0x111022038442d01100d0581d00380d16410b80303484503881c3c0202003e00c0c880000920204150f07412045e02006c001000040c0b0940d40c820192841e48103200300004449100500d1050640602c162484900300710000d21151408101141d12040140001040524a40d5891003030611907080768028000080c01c1b100c0c03403003982030340c0d82c0541c0041c4034440d48a4144070035030040450204400101d41c0c2d20503092414000c0f245007100004109000e200005c500e0400540e1311000d0303031500009010f0140c0282c00421328540c0c4010000503a40e0000061a4044080c00200e903100040941c010810b601c0d210b52580701c1074600300c88800e14a07842401c0c0b50b00b4074038070021b007401440ea8007105074038490407a5503000f10b860600c2600304c2400411507001c9000c010820102d80004002c00040e5410b1060301c1c900342e02c81e91110104c2e81031901280047e405400c0600043c1460414040c42064a965007a41c0240554000b0148401050700402600b040d03003444c0c00d580010410365040c280000c0c418482043d00590 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 442022724 1250 442021474 442021483
    0x30702010504210e041d03040b1317060619120b0106021c020c040b010302300a02070f02100e2115010302011d0a170a050618070311030c12 61
    0x202550809441c10440e41d441e40742032520700090019480700f0403044d40c0302e42000300421520100000070a555071040c0b0b2885014002032000c0c040910b070315501e9000c2c03220a401d401150790800e40d0942480d07986401c02c482c2c0020000d912030400c41d00c034410340c01e021607801d003400040d601020111103003e20040030000450599810307900d41d0b50803152900038492034007504e00052079645001d47c200300840c054505041e00440420081810054504000308100c0201c007410003500d2a200404032038841d9140141b44540c1c0d82007810040c3c1981440e81a03140d10200302d03070440c0d00038440c004014104000ba40540b076855800c0300000c0c040f020180c810115084261031000014819000d0988c403c150000b64807540d07810303a40c041c1d40701000c900c01c074080064100c01e401209540721024031000909546d500350703802034074512030000c2c00c40d0420514160b4600a00900444002c0d4210549200204c1c0c0c0040d140049130b820580742c104054241011a040800c040003d5800215010b491410782c9030019 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 442023974 1250 442022724 442022731
    0xc05010b0306070c080310150815061c0b0d080a0e01020c0312071202030c100c17040b2403060f010302150408060106080c0c0a0c0815060603070c0302120307020105 72
    0x402406005009420503848250441e21070021442954022020a0185028590100d00b854400c455a500e40054441c03440e040c100010020b810720701005180070990b0054078440105840c1c1030304145100d18420340050084d5401521a960f0300c5000e031031030f83c6500e08410900d030002d50f51941d40707010311001400303200c011051501502c540c207540056810005020f040300c8600c0142c0074200086541ca8104402120202c01e00b10310050019214011040c007030a802d101080c2800036401e480300b1000b0f4110320000861440314421481000040b5141010150344540740404440242064880082c3c00110462079140c00d84910b80411030781ea211805442e0680e03000311000e440c1d5210040681c0c203113114074094a402a000300004102007400740d030504e6005001d95414600340413428079200d280200c4200107560041c0000010086280180600198031018151510961500501151040c80040e203180b080188034450941454424000d081a0038000040f480c1d80e802c014000030301800058 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 442025224 1250 442023974 442023983
    0xc03021f0f0b09041e051005070c0c170d1238060f0702100c0206030f0a0608120f0d15081b0609030a0303050601051902030d0506220207170403030c 65
    0x82e1011059203458640daa00c44c030b510003802007a041a81080d101d1000c00c01c2000c445910419010520b003948a020b40d07845148540e9400050045c241000807807265540d021042c00310030481003030310780c4902161040281255040800711910f02110001c01001244e000310003000b400140820300340c80904507620b2141485d921803100441c900101700291290410580c48410100300d45001420403040c80d50358144903050080546403141c02190a0381d00c03c82e0170304200e09004d000c0254888803441200c0240250500600c021490710040d81c20034482d01c0d45082d122031020402c0140054180c0005100044441010280c00e03656441c0a517108014003500348800c4a15400784610f04080098469851005008004015050301d0a6004140c080e2143d41000010804543d0703007400008848030812443d4015030b982c0700320f00303a078001300c4401410142c8031301030348045040c194004010720100c030900000c005070303104801d1a10601a2516a003904800103000c5000018903411001e2840c61a000e07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 442026474 1250 442025224 442025231
    0x2012f10061706100e4314040e040809040903020d0906030b010504090903030e010c0c1b12200d0c03030314091b0102030705010501150908060906070c03021f0f 70
    0x10214580e4984408807002030003080143c004100d805c144042264010902c41c4541b0b2020100716500140aa82c0440b01c004410200124130104500400c1000340d01000386003101a2000070340d0052002d00c00c074072070310940d844400c000c80c2c01d02242d0f804807003070400014420048410180b8000c1c1d107541c0340c07400000110711207031800540c1900038000c516a008050356a90301d0300741000502d070700408010078150301b090360f5330043c41c0d900310f02481024074a4907943c407400c242205a10701003031107041b2060300100e4034600e05400c00214000c2c0d1b06070400182d1003520703402c0401c000c685070900614164840c40d8403001d88410700c4180210005443e0680380079a50a12903403000c103e15503561441641c0c004620344c02001b54010060380395130401d40d614814810b4034580031072078030b8450a4031020307088103045038034411822131395582040500008150b140080c041510302500c907039459940c02003007213046c0308a00c40d82208143c8280070848040c0303620030150260f0071600b100c540042400200304200b44d440d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 442027724 1250 442026474 442026509
    0xb04140403080c090109170a0c0e0105150f030a0203133f0905010305060f0607080901030c020d0f0e0a0b1801021b030309060d060b07080d0c05030402012f1006 70
    0x698200d071813a4106842d4840103614001c03001c440c03040070040b41a6140501c050010005a40c1c82806005201444205402d5410082085120b035882081c00301c0e251400c002c0e42c85080c080c0c4007540d80c064441100162070741e460950300e40521102c1440142202900214481c05003510501032440c1c00c070344100d4000140481883e1003503034449404041c0070420810007044158480d8001d5640848050700280102090700d007c00c01542054004641d2013402040f828803950b814401c4182c044000d02c0200085030711404050240031b00c01c0381c40ca04015070200703080c82c16207503060414028190310380b00300e95800002040346d17509152446014018020419080c0522010350406900b001c0c2c01006940fa10159404201c4503600c85140c400f800740d141d000006241020301d01900c000c501858481c0d6071070100c1c190399412644009004010b020040c8184400360742e2103810307408528020320b219440310314520104502281c1d0003600c00c00600c10003800754001a810b0b003080c03048407a01c0865040221 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 442028974 1250 442027724 442027741
    0xf05010501031416050d021305030f01051014031203070e04050603071a22030c1508040c050405040f08031815010312050307030b060d0207020f0a0e06060c010b0414040308 75
    0x400000c03469201c0300f41c500200328039a20070100c1c080b020080d424400d14001d0f41640b504d007643c1008000310305003031001d030080001c1d04040c040301d150942d40600811140ca00b52018000c040030900500d4401d0710403680e240b49584017000007201202c01419102e490b442c0583d030041440c1608001c05018508100203d002c5040c009032000c10f07141490b1801801c04941002c104007600306000c01000c4188406000d2041060460440f000d14004d07038100c00480e00340360b601d4080186000e0500c0030800c00350204004100c01c1c06403041070311000c43d03021035140c0303d50414152200324904043c05a603400000e0182100c070b6520310250100c1d104007034480b17940b0b0440b4100c0c5404800d11024024400c151031140c1901d101d0030043d584000310f410001840b400070b0011414903003002a000d20300f02d90001d4180c042d45081440f62880300c9040300c0640180d07092011454080a015101c07034003a9601007000d00060320290031078018041c01400070441c4080050050345030703400c1914140d0225030104041080304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 442030224 1250 442028974 442028981
    0x50f04020f010c17070c121b06052704140a050601020f06060306040b040212060411210c0112020909040c0303081305060c0a090e130606170703150b060d0f0501050103 73
    0xd076008080b0813818030700700030500c060358018030003110244110400418000140d241c501515030040701c604d4804e410380e0700c00c5120003507160090814400d062103014080c00c0c0e03140707440038000f110910540a0340b40540115000d070141c4004446c1407022001000000e00c0f540d4460b602c2102c09034225005c2151014405c3e40b2000159400c40e0180c208400084c00b01d802460b01c107421501c00307810300110b0704588403858180310301542e08403014001031134160031600c1d01e000031020310340d1980e020452119942c400582d480342c034a5031480c103000125482351000f1220340e040d00d00c0a04046c0410003031380380c42e10b010f0401000ca804100c000c5480d40c3c021907004620f10381106882c42c2d12900038011a260100d8445032600254840350412004a4011640e1000030f501a4000c10389602c00d0500380c2d100717107002d03410b0b6905900300152200000c040c0982c0c10000103000c00032203410002c0ba05006250656410242c1918006650881c800191a0b40316000a600c1807410449a41d0200704c41d0740c9400c011400e0b07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 442031474 1250 442030224 442030247
    0x608011e0c170a05090f1006050102070e250e061308190507030b1302040c020604052a0d080d02030f0f0c090a03112103091e012a06050f04020f01 64
    0x1007511840c0001e40f1400c0544c00140c10260000484000d500440c407121b00d0b240b03c1e441a10481c0d41c48038800c20003540c0420240c0054524000100960701c0e00e10345c2082900034510111752030888150b03248550310700a240414904d9800340026644007040c01407100c200141e07209803400b511034044059614146100140c0c40a42e120015258803841c54031441103000f005080200e250003904010f070016503440c8030300c07044643c00e5000380a203854107081841c28240c030002a1102c0c0c418140d040c6009001f00440075420945c00c50306006201840d00301202c0d54000d500b64410101d10001c01d00c400d8640c04025584155100e540c484025902c00c4508005402040101d030b03000700d1407440500c00075000c4030b841c0e115108058420003241c00c0d17802a00a01e07204080f40310700340380c00008008204d414412000e080415481d00d0703202c10f081d80c2000003800000c0200c0c4000c040d0148440d101c2102c03107080d0f0f02c00401d54002c9001c0c815410b01c4241c040b003000d425601284281c050741d801000d1940101250040c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 442032724 1250 442031474 442031507
    0xe06040b0712090e01091b080403020c2709060f070516020120010603030906021b030a030c0f0b01060f11061b0d0b06030c09010305061f0f030608011e0c 67
    0x51524a694104264002c40c058206021031041d010529072a030b012118001c0048900c003007404a00041c80e183c43c003070014040d500308a070030320030000842d400007616601c03c141500c4000a50310011a0000c59902c10410502203030418410300051110004416000e41c8100e0034501176911824000d0328540304400e030fa00a02d4a14103814070141d03002c2d0a01c0741103515146480f5413802007115000c1c7c21206c261300114080744500705d0501008e541013100950005141243c0700c44115018000f1796a0034840c2001003c00110103001c00070041d02c4c00042a070650300814440140d43c66582c040c160240303801c88803000841d007044101440e980040c285000b0362503003000390024801e5a1206080354002c0342c41000c0d090f1140c40c0f0821b00c0e11f0700c60040d8441d5201c50812500d030380d8a20001800d8440140c209807040fa481580c07401b5421171022403588009042c18103010700811140e064010b068582d0014895500e01501041443d8001c110801c414a007a4000c010b204021542507400404400310200d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 442033974 1250 442032724 442032727
    0x2010f1e03021b10050910090c03022b05071a030408090904111203030f090a08030f1012050c01020d03110409110405031e1005061036060e06040b 64
    0x212118081e6008100c80c00c0d140030011400b078401e020062802c1c1c44e40c0701001e6501d94520800a400d581030003100340f204400c00b02405a220300c1d45030340c034030100369000203803088240c40e800e816040c1350009015100100c03110480d01101031400c10035151142e51040210201342e000c0194501c856034811640304a5002c03a02d80d0030405554140668824010000c98002c128a111800c55039120503032585905031000085590780b6004030a610081d002400030061507100d002d003a0700245030700d81682d900001d0361003041b056564030104007805600c1035021040c4902c0b0250480140000426414034400303084e000c0743c01c90011001c0c00c404070385000701714000b500020b01040c042c4042941040c05940d4282c00040e0034540c0310400203051182c6881d164021045c1c02c072540b5084002805050400d107402001044240341c6580840e400c8601d07080042d0402c103c00c0b9131346a2001003103103001858428102000105212118001206507035402000042039801c00caa4180785050401c84003aa1550a6030a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 442035224 1250 442033974 442034027
    0x5180f0a05061c0c090f0e0c0316060c0305090a06092c060f01030204150207060207060309150203040807050a05032205030a0303050903120a0c030608010b1f1101050f0402010f 77
    0xf83c022145080b2540884003500064140345805410400500c003017001400d050a900c17054039207d8480c80b00d0b4020b42185240e40102401d00e005d4800301d1301c090030070a45000507403a044440b8801c0300000356110005c0d01000c10b425030b000101c0410382d2401a208291040c806c5d00718110b10300b40420030b00d050326000740000c0076810328620030103104c001810054105911040d0316000a00c585080000607403182d1010030a041d810412440101814181003104841a46a0f40010003086500c1018035800102080c00c200c020b004440c20590010159044a1682d19200fa102da00c190002141d2100124031350218522554045c0302701c610085c02010755052556080c1c0c0508070081904440c0e00090007084680c2000c52089446034241900000301c540315840081e0444089400910240c1c0c0340c5240d0920301d40b108800842000300d16020165440700489003160707103440c60a4610501d500303005c2880701d03504807418244e0040d4400d895452546419a008881e40440ca06a800c180d0f144040071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 442036474 1250 442035224 442035259
    0x21005071203180b0f060f090702071202060408030a0c1b0f050d061404081e0313031206080102130806060402091e0109031221181401020405180f0a0506 67
    0x3103030002c1c10549503040d00840070346075205904d02c05c40301e0150030103100c8204840c9141880c1e078141d1890045504540904141d80020b40d25007650140c014003c183c1d0702c0940035941c4040a072070046c0714000840c0e070f81d10030f41c4c20001c1c0580303604a42101c00260485802c0c1e1a1901a44448203490880c1d01200e020751405040203000400e01d0f1058403442c0d030b2161041c0403134145c1d9100b584154040d84072107913101c3d400c81a940403802184c032190604032090040c40160b005a09900c60690342600d0701c09568000ba03000c0348010310b5982e1240c41d840d0701c00915483c450214001c000304440429050369041d540e08000d10051313100380040d6640c0700b0200c5408001c083c0c01080410340000c01890501e008644941c0c0303190503a100c0c2c50740c03100441d2700701041d10b1407102800700405100d042c4c100240b04050211041406503c40031000811454201486e800448003d5050f1401003600401c0005441c0c03207000c59840ca0707401540c0c09220560018002950461580103042c058003025041c0302c103ea021990 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 442037724 1250 442036474 442036481
    0x20304050c12210f0f040b1206030c010e0909010f05091b15091c0b040311010510050907050706110f0a08010e040b0408071a0405030405010e0d0b070f11010207030804021005071203 79
    0x11300b40303021040c0112016640c561002e080984050000d2660350358508006e0300c040300d4010071452195100d80f50f110781c81d991181d1900c008140503144080030740c441d5211075001d094007043d842a01031422080200c810310000307010680e03041d1503c03088144448003007801030640c10034803507004e039100800c04440e690a0409041200400c007078110034510b0581e696084506c04240e4060300000d03212042010074100a00c6440d402204503c62140304a00d010b011806c0d0140040180c0107104010030103400b840502e070400039101d844030091030b40d01d801c0401c19001c0c40c0c11685100e00000d2944001083d01442e550714a402241c022903054802d59503543c5500030b07a440ba5804480a0100c0c602400b90350500c41c200500482c07044000d11b4580d818403000504400041d256107205002c0d0010100c0408c1d10300c0d04d03254100d10b0600c1c0c800070090030f8040c00d640c10082078103403092070340c80014000207156001c0b0003517010b00c2c402c8074031984040e400841102d0300c0c0100c141c0a08106000d2280c150320324060350 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 442038974 1250 442037724 442037737
    0x310150909050a0213120c050402090103150b0c070b031b070305070204050f0402090c0406052a0304091b050705030a030902031f0209040c03020a0c03030b060d020304050c1221 77
    0x40c019121640350005881641e1055038032906058003c07a2000c04058224421000303081c00105d40e02c0c00b01516140e60004006510801d40600d600041c60021a44079800c200380102000c0c80c50a103140d03a81e43d100e64a80e0002c10008018080d9100100d031000c200d03000c40c1d001e0b030b038200b6072085144030883c080062640031040440a200c000c010303440058460303000b654418600907a0b0701c1c529103040d006202d00c1010060100c41c0c150780c1044180f00c2c0a030442c0035960131000420442c2ca043da015024001e1040500d80300358640c1c40013150024510b501d581040b00c0d00411114000b201500040c020b55203806051801000ea030014000340005500c694085149035000504a0b01c4002c52a003011403ca03079105600e0503002c2d0002982c1c03030030342400d0041d039801c088c0500c1c003145000b0030b5500041c40031aa82c50010109901d0b10b07039042645d41e90700240c411004040c08110740e01d0810740342c091303030310003c3c10b9480b80100b0200000340e0700c540010800300621010a40324080802041c0f0117121720381c0c80326 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 442040224 1250 442038974 442038977
    0x80106121d0307060c02061e090708070e180613021e13200a0c02120723040c0c050709020904110a030606080a0b03150a0219091a031015 60
    0x71410102541c15525108980100351000345540e0300307032070800c4400d981240304941e041d94041d500780302000c219070751805140074855001c680c094039a18802070600c0c44640c002c140f07a00c40c04001085401e001134085005513045006003281d58040d80c0d0315a101e0f0300454410210b040e241e0844c01c054180300c8e0001c1c204031086401c1150740b070f081200151703564224004d8551103030b0340c40004050402191034001040352844206904080c41d4580c002e1140c070b40394500038010180c0d034481002c07445c81084118042d0118001041d0000302c00700e2182d00d0030540d06d800c140324a041a8902c0340b11800b40200b6140b9a41010181c480c2c0c0d0b081c00803c0010798040030102d0b030401e540768402458104288060b100000e0030f0303500400e031036103840c1004150002c003805d82010545404502031042c0c1d400070315010592851404d072080c6946200c4d040c1c3c024058850841c0e4a46400fa45282c075031540702400005031084007070034104400011a0a202500003201c204100c1c100d6103200b88441000740301c0c507412620a9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 442041474 1250 442040224 442040231
    0x20c19141314040302101a0a090e07030b0109050402211b010c140604061d300d0506030f0d0801210c0e0a060603020c03120703060b0c100e0d08010612 66
    0x41500000e02c40d0421a81a401a04840e40800c0c10a0080c01071481200040110201c1103100d0030002e01859042e04c1950855035450b41c0900e42450207101d14001107810100501070b540e510900c2201a20003187d080b0700c9940d02d125100c07100d0b0010b008080702c4908600081940b00c141c00d11703100b030752404000349506004049402d80d0010b1050500c0c14410075503040941010306143c509034080d54007a442c2e90aa550040c1c40542c0c08640c0021704420300303614920408120380c203070b6040503818442d0084a0f400b00358001603802c03220f0003a8101600461081e0100e0305100601074942d521803d0810041e00003c4061004224420400c00406009100384401c407804113090340d0340300e01c1c00d1880d0344030a400c100c00c481048200c0b4400c1c85404010082030409502d0484c1020407140c881c0f0440240c0306202468002080c1700d60302c60760000002d0600347d008a81c0c2c0b03a04c64410030f40d4a0541d008180d4410b420309020300c202c07820200d450f00c0c8411103a1115207899003002c0093300c0000700200034811241d035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 442042724 1250 442041474 442041491
    0x30705030a11100c0503030a050a06050a0311030d03060501051215030105040b040b07020705130e0a061109040b151902010f0c080105120616031508010606020c191413 73
    0x506000c007003801c51144009580c144038000510003680c41144440c420f10a41d0481d44012a001004480c0c0c090f0f600c00700002d403540c0e58003030030005004c1074205940004554034040108600042d02a009690440032a801000c1084044003038900303d020703080c0081c50500c4501e031100c0c03014000caa0018032843e2188580080c0001203400c6403401c40b000c0d56608245c005000501011402c540d0b0001c400d403002e003000508107008661480d640107000c010007981c82c0f4003060240d9050103a0040c1c140d001809200701d444502c0424000d4111400303040c4114034086100c3c5c3c180c41e1241201c0c0d64940c070302e100c440c180046070b2103986c40421034904d19001d6549641384000ea01c0e030644629403100c80592514001541841b090220400040c000c1000701e41c03001d030a03c84480039038590240d030300c0407a203808141c2d414640310201000d0016844039110b503007031010101d001900403818880ea6481aa0300740c210074610808a8450702503482612401c403242d02000042c0e0803d103803a8128110751000210b100030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 442043974 1250 442042724 442042729
    0x207140604060b1e01080f09010917030106120204080a03030b0102070306020f2107120b0d060204080120040e070c03090b0d090b07050903060126060901090c0b04061d030705 76
    0x8812501210b800d95954050704041c500f02003880850700798010900031000100c00007820b00c03800036140c01507001c3c0100001c0d0048509400c00301046501071412a80b0141c15451210641c100b03018100c0805c90020100d440101c0302d00c2030f10300301c0d00004000c2007440b05903142540109149a000d034114002c513030700400400c0090000305445065801081d644004424480e205081c174000403500400087c400d111055a1204400c0c1c12044140d4000818258060014094440c001030050020f800821300240415040d80811101d00446001d480080402c0c0d0300300300d0301d101c1c90055507090310110011407440c45c0708480c801c0c4010301c01c0c1400910140c8502c416030090300100c00d0440c445485040d44810049000411900402d4600b1b2480c201200300001944505050083c1d940112503205080030484c241c8540034000c498030b200f0b03241107042c00d0100303a0190803a0074042e42c494000740400510740840034100e408548842e070b0b402c29869203504181a00072900304144e541449601e20114096 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 442045224 1250 442043974 442043983
    0x816151814041107020d06050a0615030515011103120903040b390706050c010902210c0d080a05030a09140c0117040209010e0403020f060106110f0d0e04020714 70
    0x520808075041c0072040d60740100002c1d100071080b41c0b104001d0038081c0d480140c58950000d07407910b5001002042950328541c10743c00400c0c0643c040d124001342c040600c004d582d015440390380111103005030340250002480c01528401d207080110407d6600030800502c00044901c411504102d444d019286860343d520584031881d0442503c0a4060f80b03900c0064541082c40030780d00e2900030b088503c40801c080ba10350307000c0d01c2e12190311914052103c0024241d101d400d080d0b00c060400d43c0d0042411500714400c0802d0000c551140705105e0340d6104c0c2c0c64000040c0e10341a07100440c155445000c0c0f41c68241108002ca5003504080c04640c82a07466640703440002e04c400f404d85e222a814040280307000076803800010140d45d205040800c2c0f04141b207040c13202580302c1560060548034460440d92040e100d07807508030303c0c0c04481d40120480340191310000c1201070f88142c0307013108000c01004a0f0f8603d51240b12550319004419449008101085161141410503130040c0c0f1040f07000e4408450311504945141c1e080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 442046474 1250 442045224 442045229
    0x7110118120c17010507050d0218060301030507030201110109080a0f0509031506040f1506080601050f03010902090f1f1b0506010b040302011403040b0f06150d050a0608161518 77
    0x1400400380050008101c0354107145a01a82c3c00000d00c000c0c01c1c4000c0241051082440380d00645800041c004041e4108a2031000c4a103006400182c0e40c0da03503820120b85414590104a000448085016140c118140141e180c182c1e006803200741b074900b0b52070301a40c0d078043e6600d1140c28480b0501603400c2a50b0280001c00340d02c071042c40440c0c503c1c80c0000c201302c225242c8404000344640303800f42d182c2054030355040305800e644180c10f081d0b5035070b110500143c4a0340075400010b0240c020000011419003e103401414242c60180c5001600310071030820046895500c41e042513214202d000c030102e070984200c00e54100c061003600c803007003a024551541d40c01c0c0882604285480d42d80080e0400441d648810102551f0b0301e8100e22600314201981c03484007500e0003506041001340d0302d0020529079a00c0c10015508042001c5070580c0e6043d030711203010080c24080fa800c40e41d01e403404100160290002c183c0412054081042c040601d060000041341c0200b03428080c1c08000014514a4071103c1c1d40460402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 442047724 1250 442046474 442046483
    0x11010f0903020106050a0f0e0705130807050a06030207050606091b0729041502090105120a0f0e010e0d1b02091315180f1104110c060c0711011812 64
    0xc8140250401a0030355805134410750041a012004111013604182000261250400803450b1511484011151801103911030010420100c1c400100281c000890314201c40050b15202245550b5000c06d50490280f5400136040707400180008010b454000c4207150b10039182d061540554500d00c41d006a45d420214003200d40310748950070249070001c50440304082200050f401c443c00d01d0709540f61101c0c0084401c0e107607012a00410305c0c42542c4e008105a80c0c9540303aa0512041d1381c80c0c04044100540740200e884440289130401015800d10180110200001c0d224004c08038080160011500d03404824003806940c00c203d8070b40030050381d8400141d40240c0c03283c000c0001d180420308144c0e000079010b05c166000a4946001ca001c0035000ca038000c00c8194020495040e03040700f6081580005825440003a0300503e8400b504200800f034002404043c03011000322002541c031003035088600e20403a4000340c150140044124207641c8990800c04000c400302040c0c0126070360307400d014003c1c0d047d000001c07503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 442048974 1250 442047724 442047731
    0x201081b130f0515190203070611090907020d0207061b1202010b0306180a02210610080c0117041b0b03010308032509050603070e0306040c08010c050a1e11010f 70
    0x1c5648500c0b8070440142000302c58440d07544e0400d80038035405100344000141c8072001c0b95a4001104e0092003503c03110380d04500c0602c600c0702051444003180c0d02ca001e4180c0f1400d101c00220b02e00910018003250690242d400510981e4200300b402ea031800c01401408041d00c84107141000040c0700c2e1254075a5200503500041011007244080608103000103140052010701c10701004c0c0200000901000b4098041d501c000403885954032500840384d461600c0d0805106080034021481d0600c1200e0045441e60710a45442c0545040111032180200c82e00ca50a42d1074803000c13070046108402c0c004200301600641016841d5600480019500264400c3c1c40c1c41c00003008008201c3c088048126590b8020030000030881c607520f01c0a010142140515800b42070080000381e00f040c065140c0e151030400090480f841450700346030a840d074140718003c3c112103508202106070020b024506407048207840b51142844180c0b030101c94407401c8000440e0f14200182e00080545c0d1102c02e1151040240c031500010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 442050224 1250 442048974 442048979
    0x14030306010f180504020a05070f120915090e0705040509070905010e0d0203061503070909140f0f0723060d05060f030303070f050c010b090c0315040213030201081b13 73
    0xb40640c140008500b052008400c1c3c03460207441e104500300142e900c204c40040c1c4402c19000200e03640d010303544004080d0b000f042c00314000c2c04568040f520307403031100b607884002158540c550030108620506654004c5a0b0620040c00080e0301d54034443d038000700c98a441c0d400e0a6030350300000c144140c1507400c0c0380070540d00e02051101c2e503030003a21a0100030051342c0a0342c005a107940860350ba800d0041080030f800d40820118142030764140202801401100c10034420b0121500340583c000d00100d402d12901c1c4104081049940704c0860703403044c11100701025111441c5410101c4000011041c8a07007114007030700d0407644099071148054030030840d6200b40018035107050700a2051050301520924030981c010300811030f1141c0c0c0200b400300160a03a02d8855101c040c0d00c8056405000039031000c550145e00001007000c44040c41d0055840341d41601e442d140144641c205200407803090203040800d01c14000300520240d40a0f110f01a0051000716031202080004000700031079030010b0417000022030424404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 442051474 1250 442050224 442050227
    0x706050a1b1e0812090109080f1303060e03090909073c060815030a020907050705030403060507080402130c05030a09050c09090132040f0825141f0b0402071403030601 73
    0x2180d44000c205c0d0080140407911f44600d06140100760004298100011f184c03141c0c0300780c3c5884031005680c000000e000724206100c0d50307505da40041c009603000700c0030310b40003c039184000581e05007100e03501140c1a00a030f441c1e8504541c1c02c03051031003411400c2c0c0748600100303404004143c480010700e4a81e9500480e41040c2c0443d9030b601501c1e1501511070341c000c0d0f0048003d0381d200001240c0041c01410324560b602c1c003518040d411401994406042c182c501b10810241a4000003010b04c107038801c44603450310584ca554603000715890548000d0004800b0f00c009101c0a02c6984481c841701d014401311841a41200c0000d6942c0000b00c03500c0000365114070303120101030031580240d440880a200500079182c1c0c81c40240030404001040503111900004581d404d1100e072000725800d000000c005c10041d10300000d40e80c0c2c0b81c49001c400031100364202d0070382080f1510b804100d40d8401c01c5600e130307031010b031a10000004001d00407000440d640950b003000704400041c5c080c10004840c0c1d5000e4041c0da103e01d4030400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 442052724 1250 442051474 442051507
    0x4030c0813080d120c080708101d0f01080a0302070911160507030b0709050d02060711060307030e060123040f1506030e0c01080c040e04050a020d0609050706050a1b1e08 74
    0x8806000340c1020400070030b081d08406d40e03d90024051410000554584554240e41c2c4c03081e52107406490414040030418074440c1e159184202440110000180d99481c51195620340c0c9400250068001c804144240b14154004e03030180c010b00c40700107040c00c0506a05803141c0c80c0580e012a080d41c0706100800030000d071084503507030115950405c02c05051030040800d4115041c1c0c0f2000f445040b001030140100708006100c0400b400340a400c983d01e91401402c00b600038000604020541e1050900000c0e15007032080c4a008410413200d8003200b05948882030001900602844000e203548680c43c0801141d80703d00884010410380e5130100d1816558500c8c5030a01c0403246215041212050402860f200454110303000c4030703a0480564040d9940e0309049081c5030031048025484001c0c0d050020034402a074114500b802d0107042501d000c55524141980d481c424002041301213100d42002c0890b0003001c920000205015044260140000442e0203031091172104c0c04a40c40b130310100d0b41001000404a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 442053974 1250 442052724 442052747
    0x6030e010c03020315150415020303011e0f0302060318030c0102070201080603070803030f0901020c0607211413050304150512090a020a090e010f0e1c0e0904030c0813080d 75
    0x2c045185042103042c0d0322203100000c0c4081d00554403d2482c0c40724110050449008000315655901101e20080303000b5203a034800e2007076441c5c420707106003d402543c80c0c024084085543c01c81d22034140518650900007203400050804200a04011405170385c400d042c0001c2100030616000103a03226407070b10000d029000f024115501070750001c2c0c002e020b402d50001c1165007001d20320322850807503958038110902900c6036500c0503605000300300901409a40016050070850440502e0640b0740c144029110110f8002c1884c0341032444048010900071410b07441c1c4a118580128283c81c5403c3d101c15200d80441d0024403820009080002d030084410700d00c0034000d4002031a6005808262065000070f0a00d80351801105102541c4640b10510080250b020450140705000184401040c8902c05600d80c1c0442e100300704d0403014210b2000c1050310580c3ca1204181004000c11119180c0e500c0490f03035600034000403244020200801d0780c106540003600402003501800a00340660034440040443c40b010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 442055224 1250 442053974 442053977
    0x51009060f0905100906060f0f0f08011401020a0b0408070b09030c0c060d060e131203090c120c05090c0337050405070f030c0f080d0912031806030e010c 67
    0x1500920000303507110141c000302c80020001040380d480d100e205241c503403056030100d0b045603d080e07030010302d442d080720340c10301c041c1c00680311a4002c0400920540c0c1a06811042000184841c030042c002c8801d20b024403401107106104456500c441c9640308880d00106840588103404040350001c10480350707101560744040c640c005941001e0307407003c249031703143c0a010900d8419030000c55402d802c41c0725a40224000c0c51245d04a140da4104080030802c0110620001d0340c0d0b0b1644550280d00e054041d004040e807107680705020803103513441d04480010310713000524200c42061a1540000c2d5a82e20005071501908000005035583c3c209100d1100d1002c40103441141c000d404a2441e5a6001100c003c01c107003034901c160042400d80d201d10b403490418403981c12507401a070610102006012020407018255040340d40028120790b02e5083c0e080e80c841c1b910b140b44c00000c1d400f08040c403040410281c04200c461090501010b04201c0003000241906c0507000303d800696030b0100804484024003500c28000100e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 442056474 1250 442055224 442055231
    0x90f0115080106080d021e010f180201120b0d02012f16050a0303050f0922020c12030108030418110a0507050c01030e0607051608130e240904021c06051009 68
    0x70905c003a44070940701244220401403080c1541c1e1012080d0003c840c0f4201c50001005920302c02c03940d003800f0000307207541680001d00400c1075a240c000b50b482003040c00c140007840310550501c103900448081c28100d40b44c000f4112500207041c0c0074000011001103519a0388007506418a0307582500c145607145038011841030160705000c2000c01c1c2c01104803003095024a01d850380d901603400200301014088808045031901440d4903c250310741541c058801c030800306059612400f810700f24420940000e00400301d560b00100010070850590403150340c554994040d0205403508001e000103881c0c0c101400c00701c01300f42c0c0001c0500030002e00b0f10814030800402d00b400c201400c0501281551224020016814483c0016001c1d5010b908200a10402d690243c0960342e0703640c18910407400d130406442280100340d40c030400310328181d112880000c20165180d088841906141c8100414000042d100741d070024914003030b441481e2015070001c162580204404521414012058080c0410960100080031318 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 442057724 1250 442056474 442056493
    0x90b0711060601080604021b101a01030605130e120703050d06060302160201030c170408090f0315071b021002010608070527070e06030106080403030b0406080a0b090f011508010608 79
    0x8000c07541c1d03508108242c8005889405d5540420b2202698441c0e0b034488e44074551045850440356048000c10081040d41544601c42003c010b505481a500072568049041e20402200341d14075804843c6c45c104010445a08240c4524030f201c0c19441a50f003500011070004444401070003d020f82c50091007545404c40c0750030301314504c41c12a072050b010000d04058840c1550440b00b40b081206032021400140600c166042c80d2030941000d52106000c503018400e4140c0c5440107160201d0f019094180c44903903042e00d03940d007500481d038000300480c02d40c0b90344018041101c00f40c0c840005864a5500a8000052550910400d9803070422580e11403403048240404500c00d007213084000c00d0441c2004140c0d0315103612003e0060312401102c143d01500108084000246075038031000d8103008a010391030401142c290303281800b0544400f0f02521a40b5804082c0c0080000d0a002d402580a80110242d40c081410b5540c41c40c01d4030b0545e0310000c516a0a04418003500c07000b80b164400070300005000303004060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 442058974 1250 442057724 442057727
    0x7051507081605090406060216050a03080403080d021204061514060f09040b04020f0d15030b0412110102130519031a0406092f03060411060c0a0501090b0711060601 72
    0x307004080c42000c034107001890400d80c0c010002c2d180340350301c010000e016440e1615030007952902d0395110340c7c010f400c04106c0021681040d11507001940c1c3c0142000e0701d8141551906d2001d6804003811102d041d508000c405440c80322442d08501944c428440814200541d00c22008040c1003a0003810a07810821075501e032070382d6000d0032039800e81c0400001d2a00c8040c0c00b4001030090a214001d150410f000065070800421503000070040d1020081013040171003c141288100c40580303000007009802c0c540085404141110300d00c0d400c000b030f1343c40c1505101700035410560a980014501c01004a0380314010b002d01e261034141c2c8220000c0e0796000b25190382c0713140c880381c04900328945610810700074003000c5428440142c008225254200384984140c003a83c1c40c50460144103079a02c1011114442042c000c54030b40862070500440c0c00c20f241020200103442001030a07400350019081030712842d0011070004030280078444040d07005580d141d5451503c0783c0080c1c801240064524800e400620401c90107a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 442060224 1250 442058974 442058987
    0xa0804021e0f1905060f0403120903020a060309050a140c010908150105090403111b0916020607080c13082103091f09200f010203090307050f1c060207051507 69
    0x2850b0440b549a0f0304407920302c035030514004a800203908002c00150304000002440c009104480c4900340c45040341018010480341e01185020082d4044001c00c070400005220390070560741107006605640d000ca409d03944400041c0840210710f1600d41104001c0f01c07140d0380200c9400000c061080c00f03000880f40400300101a103005000e101c0c401d03244d1001007421700d4854540210000500821109070178555248010211002c0141d02e2090a0036800500d090038006e011100703441494000780560384802005950314a07006120010a850034070101e0240001004048002e203102c2015102d0001d050908044a141c40f01030320100034020402d00440f4403000844510349070101c0b040000c0381c0c10840f0300720081e20b60103601504150100010b01b03883c1c002625102d101c0c6108440300c0e50707200e5001c0010782e01c1e4000d40c8449581074010b842c08005034104504049400280140480c1e240c074550107050150000902d025034110364081000d134104081003100030245600018441014070709002d00030312a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 442061474 1250 442060224 442060249
    0x3031e08061003021b070302401e020301030606052d04020712020c0109050a080d08040203031e0d0e0610060e0d0b15031e210d020a0804021e 62
    0x1074440a0002410350f00c20381c142c41031000b0b682e601340c040503240c2d007a4550300c107203d01090307105030003900c0f8502c00d2200e4600d5242201c0c003c0702d080720f11b22007411400c603407001d10703007900802c240d88443c2c8084c5264140c460204003513081c403500589035411820079000301c412540006000f00103100c441c00c200ca01e0301d18400401d000c454103400d455044040031402902640b640189800e00f9003003c01000c0d0303004640560840e070b080e43c504150581d58810404120031510a100c4180c0242000543e2148a1541c141c2c0c40b03400601100d142040b0a10012844000b84440c0c5040d6600400c204030085224081d94100031600340040141d42003c581c103d0843e42c0c148501d505020207011950b80c00d480f00b41040204940100042d00e0600e005a10300e8070004110100c00d200b4054030b44d4003110308a900714601c1d00011014001d0039014a07034140088400980e41403010b5066081c040702400e40b62500084c82c580c02981d0f180c000c2c500b414810303c203510315042d151040070780700c4012034042030f03c511032103124 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 442062724 1250 442061474 442061479
    0xc0f030a020c060a02210c24011202010504030f0305120109090c0504092402031f081207051f150b03042004060e0903030907060c080a1808010203090703031e0806 71
    0x503905a4004e0607403138070460b00d40341030300c485d07201440b00503640040020304040d450036419180c104441740c28100c0e8082a0340382840842e90b40c2001030140b8141002e544208da8410305140d40f401d622902c85942820821500b10f00140c00000c3d01c00d064a440722109005004601c0113000f6903a6aa445610790000d900405020360364600e0356000740087c000341180c100c01407103003000d1014003c64405000c0d60044598030500314500e200c1448000c0031550100c21510301d54040c0c01c0d6980c81010346030300742d88508001e070780e1031207001c9000803411411010b000701e42d0442c80700007480780000880740c07810340007642c45000e0449041c010070012039002174100a41e007452003203124120000000060040c201500b000f01a03803b10400c1140d007030070000085010382e138410100c81d100385e5200c201301e440c071203000e5006014120a10511090074010008a05014040d086070001aa10b4544007030880e04101c0705280554050071003007040c103800211124410503981e64aa512000c90b050203801c1c11b1020b0314060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 442063974 1250 442062724 442062727
    0xd060f0b03041a0c160b04030306140a0b030717150102060f22020112060810060503031606050907030f030206060907020303010609050d020a030b0705071b0617040c15050c0f030a020c06 81
    0x80e10340c68924211501102c014803404007905c0f260511a1079950300b00d4088000c0f92401501045508500c120502e00050040c14144011700b0520048110340015250605100c020000400031504128040d84250310702c005c500e01c1881e0007130009103410409003111000310300003428021001812045452846c49000b4001101035517480101d800b0001d1440304846240b51445c0811445c1000c258000c0301c0c00c448030103004454941040640744c0c45542d11341100d0001e200348110005d9003035004690f01801c504280e448144d078a0b1201007600204d684d0031001600301e2001c22116141008103641c0003525071000718103542c14070034060051095402140e204070340c1490480c045580303c10260010b5544080a00e2140c1860303c130207012a04413034011581803000b5150407031450000e0600002311a104e0355141003654580c11509078460000c5d00944080f175480740046101c894010034002025125038401da500c504a000060030003250f200040e40c140c2040000141d69940010340382200f920456072039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 442065224 1250 442063974 442063981
    0x30316030b0922050304080c01080c0c150c0405150706140103110d080d02040f0609060206091f020909040305180102010905030d0c020f0109030210141003260d060f0b03041a 76
    0x18603d402c030602c010407a05c800600401d00306000710f0019016a000e88840c11140c0318181e08040c41e0240d42c13608004c640c44100303a02ca010301d00302d0a00383c0020003561000d2a080d2181c01141c00354281206000d0900d000280b0202000301e140700740c40303d0618403402c03441d040d415560348061080314030001a20614a00d0800018002c80204558403554800300441d900ca0780e401700c102e031003240c0388a40340c049038142500041140c004101a031107680000040d1422035009175000c5c1320008107000f207001080d8240f084140503251050703218004c074000c3d242c2c1a02ca02075402408695100c1c0c588150440e41045140350006000009907551154156004100c80702e182000300d142c01d10309450403010f9800d0443c2402410b801003420100001031100a014202007a170700000883c00075502c841d690707510b0807410400f003000a90b200c480784210f000942c40c003082d02d21100314540c0008200d5114140d4441c410000b030352450740c4110080c04001c8246041d4601503e45800d094900345141d045d40b00c0741d4000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 442066474 1250 442065224 442065271
    0x108070810030b1e1f0602150a0c050408030d0b091003030509040203090c0306010b12070311190201020408030f031602190f0c030804180f06180f020d0608030316030b09 74
    0x28409070750400d44c02c9654606054200d18102c079442010117001850310b00815150b2010030008010241e0429600554a0341620303440100f012054403010003e090001090300f080030300042c541a82d1044010617404603080800c10712410280a103511030310400300c10400a600701041c1d598010301100e0060300c0c0d6070b90100880c1008001d503412039260180c10001304042820b40050100f501030283e5081450382c1d00c90341a01240c03940200e8841c40482803144600d040c18454640103c521188000740c01c040d0f503100c6c03141c5540c1100400e424081c4020041013114a05c201602080551600c01040b2800780300c00b0074402c140f410035010f070012040304003110a004060725920700543c0c8c0b161200741d45036038800910000440c00c50042c2002420003428408400c0903004020540b040c040244c0714bd8150030200c500106500cda4140301c20350248000c0c90050f940b03105810081003804069903892504012911174400d0003881c140505240440c41c03401901d65200d40c561054000c1c50781380e094501e00c0da0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 442067724 1250 442066474 442066501
    0x150f0d11010e1009062a031205150a0b03101e0602010f0504020a0302120106230108060a14040e010f02030406091419060b120d030626030d020a0504080d0e0108070810030b 75
    0x109103150561b03841c6000c2019408412212090b02d000d4080000717440350070449403140031070340c2a280c5c001440407042c84690b01100c011030308040d210302c40b06005a81c03060a0311140020481c1c03005481030250040044503020300130904484d040d0038081205142c1503001444003200341c00041e0103408441810024100d095003c10080c0c85651070300008108c2d580002c0b001d0540203803500780041c1c0c1000114016046c0b00c40720106a600c41c181c02d01c1413804000600c0005c000310101c0c50820364881c0c2019070010340508c010f41c0a5802504007003490f894038202001c3c500c28006004460f5445465144082c2518100760b00300305611078008210011400c00055001c21b45012001480c042d01519010043d0542d000d6400c0390b42d000003041c3c2281410b0242c045414600011f000ea6810411038100e10b816958024501e083d050708250742040c0d10341356003620340701050b802900856540c0044211940e0410010755011b05940741c25425803178110840d01020589100041600220f072300811400b245404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 442068974 1250 442067724 442067777
    0x311030c1c0e03030717070e01050307230d110c0c15040503100902040f1a06090a03050708010501031b060c0f0602040b0d1b0e0603150f0d11010e100906 67
    0x401880248512000c40c0d440394005c0e92000c0116205081c4400c2a040100b4040e12a0550382caa00e40d19446030001503446600080031f441c1044500c4003100d5481846210000103070030014035450300c8503800381000c4122281c59000c018054414480c5655414001840080741c01d020341d01c0c483d00d42105100c4290902541d000365074140104015140d41c00210740c0030801d410f0080b01e0130310803059041221003c4800c4503a8030842c40c0b9081c0c440400c2c50808000500c4003c2c005041c004541c1c0d90303602c2d0b00307003400741c2a0400040b82c4d45440c0100180854905c0650785183d40d12654044680740c0f200140540c0c0c4110401444051540c1c22030007800030030fa050b28001c09517404181d036039050f4180440e00a12107940d0a00d988841c40246031800c3d403146420541c0058050141d80c919110800da503401100e015104680c0601800c8003401c290b11b441d00d00052040c49044c102090344440c2c000540b5687e4003030819401804404da4003ca031aa2221a060440701c1d681401c48504424200d00090b420111 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 442070224 1250 442068974 442069027
    0x131403032511011404050f060403060603050303040302010e0705060307111203150315010e01050603090109020607030306050f10081501021212070f05090307060809010e06091c0311030c 81
    0x404580e1205028a0080c10710751064680701828a0780c940107589403821010130f20032041052005102c1810142c0343c1c11345170381c0001e085606040d84d9580c0c2005030b030303101d03003040310141c00c0072051200701032b02405860f0640342080040d000240c1040045034040c04000c00c010308115003d41ca2251201c003e00111418001002c030107507903864038840da41c0310347d0075006040d40248103910032000c6100c08501428103a61000d81510301c44d0b464042041070940020f46041d419550300c4000000582e2000c1c000d0196510031b4401240d140e183c003040000b6a1007880485000d010703954041c02e0580e0b8004419944000c1d8258420f21a41c0c1c0340e40100c2c98600003120006103035034002031081c00c03d1440d540c43ea01c134511980c0c4550492501d01d1003100d0301d00a0b1800b590309a0b004140600104e80603060313050f80300100600028900e507800307140f0303490103074103a50078807040d00440b1014100b0742031010164400b15040c107046c4002c0031030104455540c030004180070340802002c02c1c8118480d070140614011240701 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 442071474 1250 442070224 442070257
    0x706020c0a081b01050c0d0b03160608220203060604020313171e0a051204023105090a02090103021522080105280b0406050406090b04050c13140303 65
    0x1103103000e6070b5507030064205040c500c0998007500340140c0d0502030288900c0d180400301d403c020424020401900c01c45840079414000d00c50703008040004111480001c0c511070740c41c800302d070a144400c400f11031010451004440c520f10070a1000d81c9001407840e030050070079034005070b0f80d42e21568010b4214580d00002007000f402c1184644030303560341c1d01c0940a06030002441c1204210302880c000303458800ea850640103c1c03018000744942c01c8280d100b0ba0790050000d40000000040c1d54500740c14868810030301e04d440c000749450343d680e0045030301c03480740d0040e81d0400903d4000d010340c001443c0303940705100c002d10640c1c450304000c2d0020014015039050070380d5044891044c0c1081c1440280c010741c2402440d20325860a000290501203413607485040104400c43c0c8484208041d03240d10143c141000915041510344100041c2600c0e42e00c5110010029100c00083c0d01a0060401082d21005080c0350440307c024081101c040302100c010004031820f01c010725480d00902e902190440c090300d4020030340000c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 442072724 1250 442071474 442071493
    0x813110409060506030c04140f0a1b051e030114090a060302190303140723010603140d0e0a21050a08030f0115090b09120a021203070c0b071203020706020c 68
    0xc6403c41800340100700d050700c1e003140c9443d050104844100e040c0c50200400748001c610030007403100d041500b200140a01048e1020b205820580c000818403018000070000900e840581d007522020586810680c0d0901d8074652612030384101c01080d1160442c443c408800105403041d0190b480200199806082c4640003078a0880b881c80010803440180d02064458410700624090740c81200c2905602900c480c2465945924a210081110036015202c0d0359840c000301c04140d0045c01e2129844410005200c500507500004000e80344105240c0d02034441c4d0340040c80707026039103050141402040107031101c0211007800c00500d0443c12000280c078400d40001400851099030208905031403921840c80b1600b61010021150f0256511901d00901c40601c0542068504002c0d486001d0420400700e0312880c40c00c0d000600441952440042594400201c000400c8401140407000b064a4060541840b100380c80b4001695400144603041560002c0c04804001c4035034181c0d00c2040c0c00350100e071007004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 442073974 1250 442072724 442072733
    0x6050603011a2a10021204031b050a050d0e040501030f02010e0316080307060e0a02090103120c080c0114130f060f0e030a0305150a27020705030309011b030b010813110409 75
    0x31585103424445004d60802407000b0344007030084030b1480700e510001e60103a07070755074508a590440007e171f180419a44440c803040860000c114040c3c009000b61f0140c4500c01600f180a407018041118160255003003800400218200ea0b202056290702070900400400c501800070f0301300f0f8041100081401407611000c100d04070008050051203204404c02c2003006642c000c00b03907842614000003540018003400603c0020040c400c0e888010950781054000024913a5402c004d42d000114107145980d500e410700403104100d02c10498100f40d09407030340070401d01113844140c40d0700844100902040c0d00d60901d0000340c481039002070440094001640d8680304e50311b400502a10307054848042405c41911403102a2606007413500448151080c498001e00100111100c42d03074115590361807041d42488064082030060004500c0b80500f003000203903039a852030b00e190110b45050918410985004c900446c5030740c0008044c2c4d040301248001c50020090361805445c8038032310f041019000750400b40000e0420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 442075224 1250 442073974 442074037
    0x10140d060e070801140f060c010216050705180414120c010911150702011202090a0303170903031b07020a17010207020114070f0305070609061a040e0106050603011a 72
    0x58070030258030300c0d040e02d4100701111012428010300c03103e07400e88208080f652401444030005110003901c0641002042c7c8a0642240c02001d4011200071103c40e014003000014400f100142408544081441d0a203404608000328000d0000f048203a0311154500d5580042201410201c1d200d0040d66075151140b481078083d281800c8103d0b000e4844a100d0310b514074000e11a91106840e444200b030500200c0e80045a040b2a50300e20381c1c598030b508010010340c0c2d0301d40c000b02002850094444001c80030703001d070a130110010020b00341800c9400520601042d442d107000200512610300d84400e440745041d00014404100b1907101c1b10620040c0c501c3c1d64001d640c103401034600e560003600c0700010a0b205901ca10014401c1c0c0000600200296071301d8000a4042d1001d02200d0b40902400203064945585400480e41500031070411550400003030203180c80c00f4000d00c0741001c5080001d0151516000c085851404180140c50000040000783e910501200d400e80b02e50404025160035468104a800b4818 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 442076474 1250 442075224 442075229
    0x905010b0a0e2d040804180c0f0e01031e09150b0a030b0403180915140307050409080409090309170c010206070509041e0b01030b090408041206090503120f09070501020a0210140d06 79
    0x10304195201f5810141040c40342180f040c056840c1d416000843c030340100c1d1006030101740107041c5540c0d1010390b6040016103002c2c60200070780040000d9203c103141094440c0f407020b0349818007a18148030b1441074079220074036003c0840f640848181101c0e100c03442c080d41c542d480e00d480201c0c0803010312400540100242c00420030034080f080111032180e01d50341c1802081c0413030700c0c03600d4155005540c20402c80c2130951056661a004448c8141002d0300e51540d901540c0e100241500040e200c91340c1400340c094941d2490f00080d107448000d101324014840041e40321070000b0103030018008046441d0080c2e4480c0c7d080100304220382201d01401e0302d00000c00d0002403122400250010b4507005441d4041e0411807602c80c083c03504807401d40e04182c60000c0181015040140c00c44203130f40c841040c00c000510400c0034044415000b1200c400c0e615040b2441088904001c210183d15808a8401c00c1507036000b1420008003a010b581c00c00005410030303c01c2c2c0781030410304801207082e500081c80804e80c85150f84510103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 442077724 1250 442076474 442076489
    0x1e140a06090b0c040308031803091c0209070c11010e12010f1407050307091707152c060d050a14010b04030c0609050f060c070b0a030905010b0a0e2d040804 68
    0x400b03880f101c070145074a00035800010105d00d404c2001c140907540902303001c108a429402140c2c076250600c0e01003841940c040c1d03500741d0142c14142540d0111305d40f04510503070008040c9400000d64010303444460b0b0030400f203204030303051200008404280d81c0380d039079240d10020450f030020305c61340030f42526110003883c1c110643c015040b071240100e180135200d030089900810840e92502d00c00d6081c040c80d8800502001c20800c401d114007400018100c0350449003c980c5080342c3c680c00c015000303c044601101c03000c0d008028a041000d0b4003805140e5400060703402d40b0000100000300c5545032110074008040c03010600f0034034010348000280f8118450010000d81b80701e050030780c480c3c0d991100c007510b000b001c6020b03041c2d20194101c07451507d4242600030701002d00e0301d40b01f103611342a1b680071948040c2c0e01c544001d80005c1c0d05c0704596410311400b4041c862100c601650007503034142c074102550b256802d010308078640442e042c00344000301c500b4411802d01d490080001000d41c5060034540070803260b116118181 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 442078974 1250 442077724 442077743
    0x5040222080303070f08070c050a1208060d05072c010308090111030322030315080706031d0a0204020702030a0606090c0e040e0c060309150115110a1e140a0609 70
    0x8640700e0100c00d07a4001c10071500d074032010081d45401510402001807800040108400c42000451820099280f4160083c050508244c00ea03400c001c000302d10040010740500038507804507000810001c1e081045440e508100c2c0c4e80d41c00c0d0700e0107451042940b44010108080444004024091610010140c0440980710717580140035941e40c0980720b0008849440f03514103450714002c80880000080300700c1501c2450000f0700c00e0030030010300f002a800c80d0031004040c0d200440034401550036204402c2d00038002c002c1c1c003d2503003100c01401d540c2c000c418002400343c0e4001c181c901c1151000c1094000c07142c3c0c4420148426915a1907401c002d21041045000042d14030600141905240c890600c44140300005012081d02c0c00082c815980e01c060000d49a81c4907070000c0144a180803840c941c041e14900700c003104000510b04005001d1303945d82d410349c0f0680d080300800320001000f10001e0750b00c1030041c40001c941c82005d4140142c0510081d001e110050040d24040410810180c1c08442ea0360310440108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 442080224 1250 442078974 442078979
    0x1509140709082a0d03030c09080f03190e060403050c150405062b1a190e0a0e0703062310060e060d181208160903030507020a05040222 59
    0x846441407248501c08007a0010245007240042c040c620803d003000e80b80f00d0300e92820440001c54000b290900c0141c0010781d4401840886a5211174054000e00c030100051504002c0f01e006903403a84903030b040815000d46009010110940940c500380000c0f41c00400c0a501c0d40d603603080254481610040e075900c51341078101000904101c02060f20165400030301002e041101041ea021000c2e900419842015412200e0340004040980900080095403030b40000300c8230004014000c0000d1501d11a02d808408000144140d070620482598000d0507503001084109900e043c280c1814055040900018181801201d52042d2001c903211600b002100e0403170b8503500c00010107604582c6000d0800022040f6030468002d02d00000605141c9051020011b080401000e07440c10100c0c0440003100c0c0840b43c0070b101845150040c035510303440301242c5840340405080150082210149000c01814054081001010740d240c41580764060302c0d01510466460b005040e41034034040000caa41d070048000000003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 442081474 1250 442080224 442080227
    0x3070e07091e1d040f02030d030603060e0102160807060204180b1804080901050f0903062806030308072a030e040b0414010e0601140f04050f03060717090115091407 72
    0x318102d4405540300c8a004032022980340c0c420f900900f05444c00034101a01c0301c05a0f60511000080010940700011550b1075458220306848003441010042c1e4814441c040340c0c2035240014a40c03240c0c0c002c140d1035440f0350910301a00240100d40002005003a6425601482d0000750b010140c18141200c104d20149a50b6842e440300c034508550003450245d09000c000e901b54024009012880000d510700750510b510200420b242140884020030001c02d814507000c11220401008030440103007900a100450a545000d000c1c0640079041404000307210351851034140700c038204002c1a032180500034251204c0b509000f400c640784c01074400c1c8110f2074106800440d14143c410b80c0169a00b000140350240e10700016042c2d1820300500c45410b00000328108221105008020034420048522894941c2d00f00340910640c451402c603400e000358808030600a070542c0186410a00611070001245290b403040c8041c0c0c0940f07151900000c075122403e6003c1401031880e000000c0c82c148041c03106500355140d000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 442082724 1250 442081474 442081529
    0x10908030c1e120f0304060b03190b04020604050d0302060601120b130b0103140c04180b090a0e0c030a15050702190602030a0204120b040203060a050c0a080603070e0709 74
    0x10011180d91000225900b04646620399410b056032840a6901454000206207110750000605070415240001000100580d07440b444481e80c0d000c3d030081002c9164000301000c1508406400350642001c400000c085540700e4040307074090003014100c0c644614446c50040d40d5a0800d65015000c2004000602040b400c14401d0b2504800d0042495003055003400000000b031003c2a800c03410151202840100707400707201052802042e501800f1035840b803038121409020341c4850011110a03003480c0c0c0c40713003481d41d400f07000542241e00c0c10f80005042200000b49483c101030228002d4044c0100c101c04000d00c05c03903110101c40c4542e129814889036690710400ca031140703400160820468007440d44e500105601d40c0c082c650041c41010018a8107840d0030420f0680d680d840b008481185104e4100310840c00c041c850150455907025060210342414010b004450248105200400c460030740003e106503070802000005055448080c071440c100880700500510310b070f020b6050841074940355011102075112 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 442083974 1250 442082724 442082737
    0x181e02031503162904061101060504050f010b090f03010e011515020a03050a230c0c03070501080a09080706150503150f010e2d01091103040f08030702030d050405070501090803 77
    0x66103c181d98102103540241403568010b04184110210705820580108801040035240644401000c00c400891b010b0969025030001c50140c0d00b42418880c8420030644400d0543d4200c860701901c48010780007007900e04c108101ea460303044d801c2a21f0307100c002a06502c290060503043c4e818020031707900c41a15549118000c0d851400607400b40c64a00082031198000c1d08007074405150252451841c00e98408809001c500010a1240c00160403040f1500410442e100f014056015040b484d18140000c0c000300e000501c00d191154591034840c080048030401c4503002a071002c0304100e907101d03132034080404840d01e00a680c060302c41e1581c4a100c0320305010001d0720941180607088010ba0812207602012600900500007403a00e01d4281d4801c40d002035108030041c1035882135208103616248400c4143c80c4100d141c2c1045820410074440800c0485550101a98102485551f02e03112220103d00e140301c0d844543c410f192425041c04100000440d505003201c4099940b07070100398440d00203070707164815079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 442085224 1250 442083974 442084003
    0x1b030f0608030a1115010f050109060e03060103080c030903030319060f03080304120c0f0b07030606110309060f0403020d05010501080105060402180123071103010507020c0109181e02031503 83
    0x24030804150522400e44c207010840110190346030009802d00100b00c201d030070b802c44000f0702c0e0b800c0014019541e00c1643c00000348002c0ca4581409034415000c2601c6090600000d001d06030001516000c85401b00100c84006070054101d9940c0e160150100a8101c46820000d40340d500b000800607248540303282100950303400120451841e1aa99110000c0014120101c402e1040203610103000c601c0c03001d50111811b000c0c0c6001a0b207807412160040466006d030b00b180d014844003112003403501d0400810740701d052905548003941c3d40c111540b802214091584001c0d4800600707141c0c0300804c5410740000b41201c49510090245840f01c02c00c01080e8003840c1980f405004603000c0313400456220b041303103c071403004100306041c080035003800c3c2e00d04a078001e030313400e503140108140e001e026810240714103980440703039101401d8507643c0940001e1040140b4881c02c0c80504000a00003440803269106c13140e45200d0719a07400701e4112048025019401c12900050701042200c10100c46080101e0689032007400c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 442086330 1106 442085224 442085227
    0x5040803060118080703060e0f060c07060b0105070201080a09060e100e06010815041b090207060c080f01080303180f1006151e0807030f1b030f060803 66
    0x2200c400d41075030f000d403c1040000000100310310081c2c1e80e0211020030800c8006415518040584100d00b109005900502c1180703103158004040700c902c00c5d40709100c088031240c010f4829019041c2c01a0201d04460000350b4006980c0d40f24070052885820f00141114580040354501070311201d01a41041c1e035001d414150740307420401c80b401014004002d0204840203103400c0019000a800180002503400200010748000b60b009801381134170840440d01e8801301d052500c0601001c5100d200860100030100d90400700c26984641a6140d80c0e0065240d134807030b500b101c03000d4030f40342909600d5405254a0f010146505124410b041000310a010a03268282080c5100443c84140b95909022200740001503d00781c5061402d480403840c1400c082d0ba60300ca41c0c003900a0518003190248180c075042110003074050001d521400d880d40c66508010310b05500c00e014007100e0b4140142c1c2c000760b00 = true := by decide +kernel

theorem cover : BRFrame.Cov 441906474 442086330 := by
  have h0 := BRFrame.cov_init 441906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 441906474 ≤ n) (h2 : n < 442086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
