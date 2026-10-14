-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1967
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:19:56.595865+00:00
-- url     : https://prove2.me/submissions/ce9ff81e-b5f9-4bdf-95b2-cf65af9eb0cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 353597122 ≤ n < 353776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 353598372 1250 353597122 353597149
    0x2030c030421061e06060c02030703121b050d0206060306090712031b0501200703020303041419030e010216050913030e180f0f010b070b042d05010b 65
    0x5585001c1c104500d000d1000b5031003464454a08804506000145042c4101022402074001c8901d80011103910340040d00d82d140c00c04000c01032804040e500580b0000b40305811707668004480c4040d16108070342140c007217442c0d20a00c03136001c082c94483d4050210108020070103001c82d60039510300791748100500d6514034050300c0c061400c0e802007000300038203c490220055058840e00d0128509a0040504d090404560005840d40c3c0d554062024000d148103c48590041c010040b2508000190f02c000e0b4590000800242110076404644049110140301d4040f144c21022414004080f05060007841c01000c07400240c003510440b90700300d8014200030f0f0a030044540040030084070b9a05c1c00e64510f20b81c80c0a070800ca0a100e08a4144042c3ea9100c8801640080a041903000c031882c4c48014804e041101401d11803491643d800184a0603041c0d10850b07404c2c07900319501c0c020a4403945003c28036400010702e00da5100008112030703002c40300040380740c00305940128001d1066286800c2004081d891408 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 353599622 1250 353598372 353598397
    0x40f050c0a030c0e0a0905090f010b01090501030504080c0303190e06060d030e01020f0607030902041404050a1e12051b06272b02060a06031502181e100203 68
    0x2624148510941002c1d604500c541350043c4d80811520201e0702181d1650800e4146507182c03402c00c10034640c1001080b0b0406510002880171000c00c80019000400c503001d00c0c4c0c10903840b0800902400000300490349080b0580c0b04495581c908500035500c040d503c40d80d81e801d56410046100c10b411000158140196001001c02c02c1001c09560182e40c0c5080228442d410f40c00780780091040987c041c85028840c142c20345000c1504002841000201d82c200c2c003050351485001020f120100301c0000d00c1e0030308682c0c030143c5030f980d88019082100c41058458001084180c040102449a6078007401502c00900600e81040300000e040680d6516800b0488900b0440b00403040707d10071003441800303541c4c007203240c07281950404001c0103402c041d01d0100d405201d02c0c0024441c4881d05103981081100c0d4040480e041c200901411981c410203000c2203046800b800580208107240401070491091101e40c400610640c3e050350442401886d46d5058058548580c1d4000c3c61811414004002c8440125021 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 353600872 1250 353599622 353599627
    0x30614040b0f04150f0b030c03010e0417070f1703040b07050f040e04110127030305070201030f0f09060606090501080612070302030316060513050d0e040f1a040f050c 73
    0x10428003000740180c080140c0c0c0419401c0c4103a4a40d2114841c60011456840c040000c80303007400c040020324600380e441182c15180400803c09064900030980781952440c0c0300c800c0d90398a9900b025030b005401d0301c20701c510030140015003004200380e41c140c2146a9100300c103007034659034542140000d1b901040318040c0011800c1c0c00000c18040c8504010b024002007003c2003428292590744034a1058000c03138003210708510403c444485981c00c0003000302c94030f54100ba4400003022038000c008070520b0f180320040034008007049036021a030298111850303481c4686001c100390a01c1074940005021407a05c1a141685001c13000b1070b001348141310300402e0741e1301a1924032250b107680090000140a603e0320005e1030050180200050f81e0900007411481c0c030640c403004407040c25082000480e40003400b00403203070710340640b01e100081002c5210084414941000070b00ca401242c0450003030500c2006100324240f5150070103071600043c040600041c2820340e8200f01203030190203c1c0003110800c4e01c0d0001c100300700303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 353602122 1250 353600872 353600909
    0x604150b09010f05130603050103060b04090215090d06020f072001091a210717060d08070507090e0307050c18011806030b04080a031802280b071a01060306 68
    0x10f45440d01c68142c1c586049031811001d284286181d0340c007504013a002a403654010414484603004001038540c0c100e4042141003007941c0040d5402030142d080c54601000480c010106550b14154070320360640110096549580759001c00c482a844140d048603203a40c2c005440c0e1850000c6240b02000e04d4040e120309503906e05280c0700125051403015000e072b903000100300c603407081c10002c004800d826990f0855504181407440c0d01a08802200340036220f03520301d8504100465403000e82442d445900005016075562040c10550304009040d00300d841a00c0c20840518100031000000b460820701907029200384030001000c101c03001c6e003901d0311500320380c034a0b9006100c12907140d0400e08104141c1400010150750f2a6680301344501d00310703070680700414042180481103815005502c1d00040a10820403151110342c0040c80d464203440d0070190101d07454940035030f03049004038504050800800d82a0f00c403400341c940486550601c81040301b60042a40000030301c1c0d0300034015075054654240706894142074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 353603372 1250 353602122 353602127
    0x10211407030e1606030603020a14030312061207080606180906071b050a0b04060c08090a0308091509010905070819060b1809072405031b04030c0e0604150b0901 70
    0x34120a4009018085044903000340c07501c00d0f40001d00854070003041013407850042001d000b8881d4016108008014000c50166602104490220082d003201c002c2c9a00c407030307020900c2140c10b4100d62145208900c0c022030302400002d2803500c204c60072030700c8101c101c104002c0d0384840e03441a00c510407140c0c03180d00230440316401070750341d14141529000948c0000c00c4c01c1d200c0c90714081079000180d0759446454140428041c03580282c9820324114140010749061a51a55580e101c5011000e070070802420302040304410107020708048440c91700444080c1c0d04002ca0010f0013401d491004136010b00c180c0400080d060408a8a46404900141c1d09442c4086540751000507190112105a203c042200055001c50151203214003c0e510400145180b40c00c0c501007800c40c0051407450b01941a00400a462855200040b0303948144514070000c001940340400e04118041d43e000146400701c08500030035040701b01a02140315100441d410702a2040d80c0000801c20f8405000d04000d081042140016550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 353604622 1250 353603372 353603381
    0x301140901050703022a0f030a0e0109090c050711061b1615140d0f0203070e0102070b0313020d061d0303041209030c06030e160b0705011116120c021021140703 70
    0x3190401030321f1440500043c41070444e0300120f18240440c0d880000c02c03209590003a01000640100e01e4104110314994070041c00d2401080001440030345100e0b295120760b160700c0f06941100440c060b4103003201d04010140d03070322075041030070710500d80d60140360000c1d16024075055449084090703154a9009001842000ca10b0352000154860340f58a4807807404603202c80e440110711451140d03607503c5148000000090502501d54051040404244180701c071103440d124040b50000e90490b81403e4a803400d14080c80945440f10080030b1101c580700442c0c00509000c00150f125521034a00c420400c10744c460180c030803803c94000a401c0085a820600649000c1d03848400290300041c119a8104810420603240443c00c0c2c2000c400e0300c84c04980d0408102d000d0250790b02c00c0c0620900039080c41800c1c400110700c034000c12400351a8030080703000d002e551b5006508424503143c02408000007420340c0a00603006948000c0e4aaa10020340c1010700d02801071441405a4900e01c503031445003e88070003c0440c00381 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 353605872 1250 353604622 353604697
    0x50a050310050a0e0103051608060a09052802030d08091207060902191802040503100203060105040f0305060105010905030d32040906051f0f0302030411030114090105070302 76
    0x78604200301146036a65401c1080080c81d0712044803030558150324201c0e0508856484555541d80c44031401e05c02140b02095055121502c41d0700045c18846d5402c040340740c800189901d141d034190901c0a41600c004000c3e90b04103d90080d41150171040c40d201c4100c400090850340524541c2191411706132580c2288002c180c80c81c0281d030301142104803900001c541022001c00070047c4e03c041c00003003004c642c1c981d442c112107588030441141064900300211341c0382d6000d28250310500b81d0002c00250503038010f800303550203072514241d45508551246040303981c4440038040c290115107010b10000da1031600041c15001070200340e6500301d00c01e0800b904030071510b100703600c40f0f03507002c2000740c0c02c08100c0d501c000904000d1080d110041021450101031201e0050040c1c882c1281128800c8840d036966000000c40180c05d1807841e00590304c2c0e85034100500e041e05420380c05030707155080c4214400d00e07503c8a4440e902035140c18000b000991540f20080d4200c5c451503104000b182c01c1d00b8400001e508822800c0da601 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 353607122 1250 353605872 353605891
    0x60906060d1806050a060308031603020c0a110a0f1d04030201230103020a0e0906070f090902041d010504051023041515080709090e0a080a03061410050a0503 69
    0x10040840c0741c000c1559203010318201d1034640d0108540c18001540159604009111000c1000c1411626400d140d41300007030503452913040141c070b43c03400b542c8250304845031070503076400307503035030140301d450f10405400503080318a1003540e5010000ca4003842030007079803045440107a44081c1017481c042200444031402003080e800d5568400100710f450200c0c0790545104400d100000d2034940c150310400600b0140e035080002880003a01c204100304200241182d04400c86040009a1441902040fa503440041c2c004085282c00810000345030030070061015412050510342100c01d80c1c840f8203100807030f00d084680c40c0e10303e06001c004104045050210968030031a0f00d0b0040f032101007050228040c5c915449105600c6440303010300b000300014501121006003964584201c0318100088000c010304100d002c0c440349956240f44003250014100800807500d070b8001040340d120781407072201034003c003454400c445c0340c112880210129454000e0f040012503c49403510b505110640004031000c1d00000c01c070040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 353608372 1250 353607122 353607127
    0x71223070c110301060f17010203060102190f020303040303030e01050f040305091e040e0a03020d0e09010620060f09010c03140a05040c0803030c1801020f1b0409151d03040e06090606 80
    0x101c0d43c8003809820003508070b210800c174085103070a0030052a03103040b107080e0503503034030503c107001d07075aa03011034858041c0ea51780340b65040800b110b081c03240492072407041c025410b01c40018004201a0950401d4078110484402000f00da1f8411501b40720720701080703c0040c0002c074208281105850314458600300ba461000c6400c105006880105003111001c44e01c01c201540580d508804041d410003008000202070b140a222203e10000404c2d5842c0d0306010f00703028000b900006c030220072100010400078030040030840e49182000d0360281c12000c02035400105550914441c080d482c0c0c004e0213039017070300b840402c0c1060030303135031785141c01c00041001074400c0711042c1c151180054250800c1014500409030400c031541d503080c540388415170f46c04042c400c040c1550841c011803851840041900c030740c07542c03001c1502140d0866410024000305001c032001048a00410702d1145802040c0e4040b000c051801040f1006a10380055502d41ea8052441480080c43c0c460001581505000d6081600444041c0500f030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 353609622 1250 353608372 353608403
    0x6060c050c060f0d0e0f010e0304060c060b0111010f09020328060c26010602010b0a0e04112805090a09150f061503090308060909030a050f070506071223070c 69
    0x901761010740710600d02c21342c0030400d1059215000e10030380c00c4020000c4011440d00d440d01901500c080300641010b41525690360307908105902651f40044500c05038030003007040600b5620844010304040106130300034800c0e00c0407114000d4a682d03005d0084848881b28214020b80d035602e440190a820000d00200116120381e0240311084216842c541c00880d1507540540d030501000a00316148014564419460494100a10a004054030b03402c81e420009101e40100c84501150403144058502d81c0300b0759070104441c944249050b0031300c06a600480e402aa280c0b1480c00c40c40c19241d840001030941144600302500d58502d1360300000681c00c00c21800b20301160360f80035405400310701401c80d6000c2038603aa104010960300184150348071208451070203180c24001180c0e9941c0c06500c003400184100042c8034218401258291203540d5800303421110103140144c0000c0001c0d228103401c480e16420310300240c4a20200c1c481501b014201101c5801c000d030303920281100e000c0100076054485041226145 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 353610872 1250 353609622 353609647
    0x60402040506161a0c031e0c0a030b0d1509060609051527010611010b0a0602060c0a0504030206070c03050f30070b180c0a03050a020108060a09020403060f06060c050c060f 75
    0x3170b104417104444280c4910308a04510a8040109060701030785401604000b00c40058600343d40ca04046443e00040c49040344000c00c3c0c0c4041d5085002d81764a04406040c10318599940000000c0d5105407810311500342e40c2c10703440703042c1c50040c3d40001070b0a40041c502000c60500051052030520103d0803802001d015408081281d002038000300300107201e0354a00c00142509004402c0040021388101108515145009461700000707003802d1680f140c0001c4800405100340e054901554009003215541c881500c1c104503141f480307103c2100c0c0b6000b000c03000382594102160b0386944880303220201c0425081d410007003020b80c15001c5151302c003080030f000d04c04c04030311038011040c0310304c000456440303407561102a403515148600150501c2040250030038800160042160848550f0a007014101c075250315000030000c0c43c00382c000d000603d2010600005010301c0d6001072425980c80541044855102c138811039010090080c043d1003540060a052000d081840007004440c0c420002e4038204155003000c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 353612122 1250 353610872 353610923
    0x50c0a060204050f044a030717071a0901060302041104090c1701060c021215042109050f010302070b07021609020306010203032e08030706060801020412110607060906021206040204050616 82
    0x401c2c00d1f90000c20f02e101081440d8141c103401c02d010b07040b01410542540e4905100442410342e5408070f118010206001000035004071014650081040c00205020380c610f0307420303401511a12300d5050810904041c035a010306419401081c07044100c4200c0c0e82030510940c0c0322031820300120b802c000560318142035040c0c01e10004034000c4d00d001e4070554904280c1008000c03040744100c200343ca840441000718005030407003031680c111030060303c074041003100361001600280188500905000e41c104108500c00351b0210301030307403038881c8064460180d9444144500c201c0c0001c482c80387c05640100041036000c050742941c80250682d20803030080c40c915040e03c2c0e0006e0400c41e40705000d264408550002017042500a03031016200324030007141024517140c201c00c180351411074040c000c1c0300c81d10700a0030b69440344030071070f00d88941120b42402203d1030391a051000790b1000c40d481d40200d104001250322440d090084400712030303000b40200e0a100121094102c0129110300840d940300100c04042c9000307050124 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 353613372 1250 353612122 353612261
    0x230c0f0a021f0504050c060315040e030c0703052107030e191502030c060603030313030c080c061602010f1e1a04050c090a0801140c0a050c0a060204050f04 68
    0x1030205260030185007084c50300c1006d4035460b100f01d2003401044050103a010001000c1c010454000c920080002c0c01c184c118411201104018043c480c404014070000065000d11444908600c41d43d500d03030036050a1082c050200700800040340345005e9141440c0950540462610392400300116a9507401d2510310706181800b4003000da00007044400d5031000501803282e0001c825409140b070340c07402d075030b4082c284444c2c0c0d00010b00703004003038a60344103110342001a504152108402c4810a0500c01000d41d42c0801400d040c00040d0f0901c100340031668094010f052600c0907085030700b002e1051208140002e4224076071541c4400d40c2c81c1000900a60321409401d015111205844c0d541e0f1a220041c4600100c0d06c4e0000c040c582e04000c244200340e14001100b03503210907021400794648200700c45c04c4655200e00681c06d41a0300c104410002800300030b0b4010021903008646c49804011610240300c00d880100e0707582c40c22800a0b058040d08507920320200007590941c85440e501e44040b00502c017000903003454 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 353614622 1250 353613372 353613433
    0x71101021b070f050406050d030c08120f1005030109030e011209080706020d0b1c0204020a050d0905070806090c090a0b010c05071d01060c05032703070603230c0f0a02 73
    0x42c002c00c603030a040104a005030401360382c14043d05007044085007401c0d0320707900028100304111030044180000c040c1521808191000a010749051140d154a504c803000c1c0c9660402304143d00c1c0c0000c0078903051088061040e41a240e040714005d84400540340703016040c2c0030b1001c00e601c810b492710001d6199070007400e0b864890351005885070700302c007448000c94036141940342c099102d00048002007042105180034680d81141e000da07036400c60f00e81c00ca075039000e540c081441c1e05080101140410000cc101c903025140507000310b512135034503118055a2074100c1c5c400716400003c4a40072815086858102c00803021040c10080c1c2e0b03014107a070f511480c0080545c02210302c2014030013074400c205400f1600900401702d92a01060b02d00880c6c0f260b649910865920300d07800c4000103d02030b11814210b00c680135910008040d0360241d5500c0c400940905100205007428140b8902d10482c04188000f140e8003469015510381d042480140701d01c0031079480000400d09510130086d0701803a01c00001300000c5907030b90f5038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 353615872 1250 353614622 353614633
    0xf09050c0f03121210060c05031219050106020a02040524091003050d20010209011704020307030b240909031e0f030106121b12020d1112010e100b03071101021b 70
    0x104103030001059150442c104100c000c040e154023141000050710150746200326011f000d92100200e24404180c880c03020003aa5082000001d2a02d0300400e007440194002d80d024010b560711b010042001c0b014a03007601c2c2d201854404000d020741000700031136a0021844001c4103410381c030b0b5240c99143c01700807140f600016100d071000c4c5940e0004103601001100506000758145031403070700040c12042ca400c0c070003007241d402f2078001415590208580c3c1d0003035400169000b62814500003041440503c02106d54085100754141d459034140304600a10030313006100558244454140160289202c202c1e8601817110244a0100042200c100a60090071262142c16040100200b080103540c10480913448496040764500b0000742c000c82c83d51f02e0340c0d100c980c00603038507413071188048010212024250500320300414100700400848011a0507259482c07034001040d1f543c0f00d0091050002030044899194007440401c080e40e015081d50310300004031800140c2040d450900010652101c0c0030a04400c0e07012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 353617122 1250 353615872 353615881
    0x120f05041212091a04060b0409030503010512071410020f1b151905130906121b03080f31150216050d0807080714010f09050c0f031212 59
    0x8004500c82e0701110909010b5243e0f10703100c1011320002c071000303004031500f14000101000940c0d440745000e403100500401520807103003801061a0001d002e56402400b2114001d103c100c000102001224090711000c20424031240030321000d03a441c500b070101540b0454100705030510040c042c1c2051040580d0f001c1034060000b904000d100740190404c14007030320f0108000b06928240d2006002103100340c1c2803440d600c803c1d00310b680c0c60a061550041030f2061828001060400800700e10b14903c034082c0c80300d40034401101d8081d2083c1100c522006080c3c080402c111150700350103802910106410040d8810080381007400d038a82524580c0b09444212403902080c441c00d05d207850341e1740241d0b0180c40200007a454038840c44640c06003e0007402d1141c0d01d2410800104000c03036003202d408a50007050b0a0700c860861511003858005801510204d500b00810040d07070904520030240a40e40102c0104407000081003030141d5549020306460700350061a5080203620400e100034441205040d2840903207292 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 353618372 1250 353617122 353617127
    0xc03010507050301060f200f06012904090f02070204060806090d0801120201031d010c020307050f06062d03191a010501170a0e0a06061404051006120f050412 69
    0x10041c05441808014070040c03004c1e5a011003142d40001c02030030301317510120188001c17031848041c1068460079403085407080c5045d12400b0401c1da048030701c10321000b614600f003150701710008401c91481480c190001d01042004c030340107030010340b00d59111a50043ca4007440d0703008034055468a410880d0180d1151081c850b440d40100646000d903005840e01c0940e55041030308611140d502804081d0406031290f21040000c440f84000d82c0c0f01c0d0064400810040b2001308000c1d44942140300107841d640502c0c1e00c56040e07800c2c00f140c2d4511580d0014502d06008856099001c941d64649000b0745039142e02c0b08030700307a0b1910204010412004450840f40b60640c203440c08140c0710a04999240f42d000d544401040943d03002a1840500c0081c010349007441d6840e00300550061021582c0390405100e14042d9605119696004509841682140c072841ca200c0c082840161801a02c0d0030f080401085020058a4441c140b84003002000081c003268011038011003906035070b4191030030b0741c000c144052409070168 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 353619622 1250 353618372 353618381
    0x903030c0815060301051017010305061015080601050c011e0f0f02041809020d05240703090c0b160c080d08070c0c0302090402010504170c0301060501030e03030a09230c0301 76
    0x15003640001c40214140b0700840c11a01040c032401c2d00a4241c000d00064a500a070040c000103440c1c3d28000040b50782d00d04180c0da0b10a402e41e2205070304405400d020417131980110190a80d000c2c035448083c40c0da02d410300110b034154402c410036001c40d5601d4000c004054004d44c0044549030700d0400101e0710090705509182124100b0240d2203100b441008204440348200f01c0045614112000014015050b0300101d480101640d02c020001e010b45000c0183d01c0c0c0c24112042c5043c1f00c40341c1c565101c0d40d1034100076011642241d00c090250f03035002e8070411112581400a00506542c150701002e9940c05a403030141e414955000a206500040c40c843c24a0b54030070b80659002070786103804022500c140d154a8003540c860701001c0d01a2440308005010759000e80120b0f00100141002c20641d540030303c203150348422103c07200d60701c0fa509214001030258030a0294440d14400f0002440c40d5886292900d0020b00c04d100089800e00300151102003480805000d906000d1030f5072000d498000802820182181c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 353620872 1250 353619622 353619631
    0x5060406150905130b090f040b010608010501121109030304061205280b150f071a100b09120708070303140301030b0609190501292d09040903030c08 65
    0x100c00c4100000a103903030002c120011100241d4403806044000080c2d4400340000c0e9030442d822000c03100510040c0c2001d2843c107845140518031a80d8142d0700e071102200e200500707110300c50016106c0c1903490000301d01907200e06800c410b08050b45140c14810b201282c01d64100340d00580c041102001040c001c900c0d0f50003103503801661045180e40903d002c8042ca1306070301180090022503170380c800c28048103454100d41c4034265400008000c0d2512040d615407c00ea500071702c070480300744000e8113540c60440c0c284040603015a10710040700102c5801c004980321542c110103100341d4841003c41c55280d01103005d200070005444100c001d00b41c00d60071428042c2c0850102400c0c0e1025520810040001c0303032a42c450305400c107604039211042900d50401c1d101c803040c007422140030381d986407100004518240028645024243c0480e9401d54194040d0110003401240c008001d41d215440725404005035002c1c1c1181014043d41304203050440c0103006c1000c4541d141c1d000c602084d910300307015030302c1070b00714450700d1b0b00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 353622122 1250 353620872 353620889
    0x37050907180507050a1202090414160e0303030c210405031308030a090303030c020a0204061e0b0c060f04021c0b0f0a02190302130b0f041403030c0721140105060406 72
    0x80c10070f042e005186116a031100410461183d40c088640741c2c1c607404440c0045001030050010040010b8101a030300000c2d141e101d101c0d00b100810000290043c1c13250303000d450000700510304607500c14042d00d14542c000300b082ca0985195000c0d2780d0490b0821041036002c1c40c000e1000315181c000f5001c20290388200d41d08160260744c001c0c04440c103125401008071054903810701c1d001c20081407408003a450f100981c08000e5120b0304040000c518418a003035851070007e072031a03c8807a040d80d00e00c07208000d8494030342d500d0166040000059102ca03503a039050b50300301d840507000c2c40352184080c00386d00726460314200803103091a0007028802d80d44415912581c00c440c1442c1c04500e04010000414402c4445c0000390040c1600031405039500102000c280d001401a4050251b8030008a4945280c660007405252108804050f98014604000041e50420b0704d080300181302082c1044441901040603450650f0305810020720300c000140710b80680c805c2860460300100e030a04082d020001a02c0c01c640144a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 353623372 1250 353622122 353622131
    0xc1207030f060605130b03100903200312040308070e0109060512071110020d0609020c15060f06041d0f09031b0a0b010b030406060b033705090718 64
    0x101098100880c0e90220144071440c07201e00e440030103000d5039800f40340c0c481800100c0304a0076042e5000070346400c50880664101094402004044030161000074000556058059110010090b200c9940c0f01400c41107038100b01c1d00c080b0100d42e2107000c980441c00503d0b2142804050342d04989000ca0031142400c10800660404c14010090b02504512424031a5400c021540d40c42c02008030411521818054401a2440e1080c4001a50040300d80c20000c61074484001181e01c00c034800c0c3e9014014180240000303200c40300c540e15036a9800383c030b80d5901615103c0c003840207685000051009010340410a07150602c214411502c02c24014030030740181e00050f041103490100442190140444401804850031a4000303103440d048224400804010b42c07200042240b0003440013031442203200d560240050345d141c1400d049280010b840034038800741d80684141c1c0740b00b00d00626103c02a807000281c0e81c0c10750b50491070019100240c074140f007690005901409450440c1c4c2e01d000b12807005080500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 353624622 1250 353623372 353623399
    0x11040f0e0c0d05070c0c060f0215160c06110310051c020604121103030706140106020d0815040b0910090b03211b070602030d230402011b02040608010e0c 67
    0x10b8890b298248040300d03501c034000b884483c0101d00c480c020a4111030f000d1417454403000c010740748040380c4030b01d60b001d48a400c0c0038402002200a00921500c00ea0300086100001da110070b482520743d01c802141c4080d1501201602a070b414805940702d10725401005040074034140601004005403000c244040d07004416002c00b5840e004119005c5924203844544c0c004143d040803140c0040300d0740b5803a41400001a800180249a04030300211109007441a0190b60b0f60f140c203036034402d20b03264aa0302046040c000140700302d50725090f610b04008003800116201c9206000601002c6040790340d84c4032000415010300c000240b80c400c2c0c4400d810283c000301100040044000124012402034059040d070000701d5440314184a100e0b0f15640c00c1820444103100c0d1a080060f403650800040d2880443c5020340c0300400303044028060307014016100b540001e984403500115a180c1d0810134400c0040310550b040001030f21144980e030010010400000b0b0b0a16116030420705101484061900c651010f40050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 353625872 1250 353624622 353624641
    0x2180402010e060a1115100609031203021810020f010b01140f0a0c02030604050a0b0610050313170a08101a030f0703090611030601020106061e1d0411040f0e 69
    0xc02c0e44101180c00d251150b4001d6411228003d400e02c1c05011030140341e50841c0c0320088002e0306801604009a202c400540303c0b1001c0710070030440d2001410703003020b800640c0752582c040c0d4010a010740031003481c1c01c00b40303e1080c04104d40620000102e00168450380740c0300ba24107401c1c0306010b640340c42440e01801d052039018201030b0500a103600420041c00000b180301c94a402035016070708407a4054242d44582c942410800e8403504400d405032001107612001584500d042d14a1203401281d64441909503210300e03107104842090180202c40501c1040b802100d0902007502034444503010b40d076103803081e180c04003100007550915030010008542080d215104d000d81d003420f0b640c0c03104590900301c1e015a01c0b920120041c2664601c043e02440c68000c56010500440c0e004500c41c000a0b0002d100269403039000b26940c546210100b401c00c2a980c0d60406013501c01d00d01c4400349000d100891080d0514000010101c41c18158105c40d9054009001c000709644a00307610020441070b4113001d82d07440e028030301d0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 353627122 1250 353625872 353625887
    0x15060f201506031509060a0c02010b01172e0f090207171c060e04050615031f06030c0f050a0b070506070e0301020c0d020303060a090b1f02070e070c0218040201 70
    0x1c18905041100007441034604004240590725000301c24512070800d285142d80300d40054440035252428100f08400040c01405150107004042e528090200b00e4442c4500d86a000940800078624001007481b8000350154031440300c1d294605403550b01185040020290f1030a00c0d4420020b03240140501404241c918010148580d8401d4585503103142c1d03105200c61201d09100040310a0b460300030041202c0c050b007045203214610900c21240c070754a0b5110310302746d40c0051031440d41c0d0650060210a103210442009c541d00d0b0a80c50380c0c00708810380ca1f0380d40c14407241c0e502d401108a0152021040002c2e103050051580200090b810641c5000c2e03894071419100d8500429003c00d001c1800428883d98400350304540000303415509031100500300d804000d46980c0700b501c985d48206e1f6105404a8104c4051145418801000348455600400a0460100002c0308860401580142480001c0c5005204480c61154200c3d5540914000fa584100002001c08000c2c0e04100c981403000c000040c1d811548 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 353628372 1250 353627122 353627143
    0x70302060304081c090c0303030f143111100513090207020a03050a06090209090106080309100504240f05090d140f0709060e0901181515060f20 63
    0x55250307140990440310204000c13040d248000c851800c01c151007408408000b4006481c03199509010004c580401c0b6402d6807004500200004500d5000c10407254402d070b291070030303c0a0504036918042000300c810003008001403055458003094480000185808005500c0d11012030424905000c4a0b00c241c0f800e40300b45004d2a910103070300107100000e5580d0798030007000459018044941e503003a80d243c044064800014101d00945003034012520098041c019082a03820507402103081800c0c4038204440c3c03070050201c240a200342040301085100b065070300d6050038041c9614805180308003103002007246081c20990010002e0a00c169903031681c0c3c0400e03c003802070b00005080011000d10b4009030900400c4d000c92852840b45510020391540107030054030845140e92480c0c51305071344100005084c0c40080d44660b031541080200e5000065131200b15061445c0300720000202075600b0000c00b40040c0003900290041410408581c51541c0e001c4076583da000f000c20041003110401103100f0b60307110311984 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 353629622 1250 353628372 353628383
    0x1120c03030c03020705040603060e010609270c030b04030203031f0f260f0c0a050604050913080f0d02090f01031b030e1c030e0609060c030115050d1406040e070302060304 75
    0x48250b014144200034410181c200100100016550391500c20010411040344086550070314030005003901d0113114086c809803c211000e40c410250403d02c90404000d80300440f003c5040799404000b0a2480d0501d6225078807030340066580e0700780b0856403901c00c58440c00020741c14411260a0010810700001c07102180c000d00398840058041c40180e100d000d0400d401c58003d07108100c1e0140404500043c1c2454410b01516486011600c401c00e00600d071003203000e1103400c664000040740700c04110000f0b0f18907041c01a031010b4203020200a1140a582c0f1440d1400301603030700440c03080101e1030300166400c1c0c4480709080410030b61402d05106111100214940c0082c15520100c0d40c2d45034270144102e502e03942441102c1003d40d2040000a4003c0042003501c000318402c40c400545064000103074103003c0d03400c501a2904507860214000c603135007001e81c8940f040080c2841002081181c40c001c0740c9a02158190b080308c10f191880078002210400710407022141d011480070405600d0384800c90760040d8004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 353630872 1250 353629622 353629637
    0xb0609060d230619030809100207180b01030b040504110103020309070e0915070f050913061e031b031110020705090f04061506051b1002070501021201120c0303 70
    0x755001e40080c2014650420030300c2c10242c11110400c02e00c2d180c0da128031000c548240b40c40c144543c8201401d043c600000300b240404000000c81440d00c11925130b0304050610442d20403e444450001003040700720341c1112116220120410550303018010300c03040c4042a00c0400481c50b243d02d40d0580c220380301d480300b4103141d03000001c07445a41e014000030b809011074040102c49402c0c01400e29a485661060014585401d1300c0403039490342c8500c003900303003a510f95035070343d4249a0b8031b50410406d0403103840d08688465403004001103801c01242104d07410040d00f18141011803442c2070030f0160006040d5190000c404865050000038850501245040d00c00d94400c806980095001e0303142400e5600102e070302840920401402041c42c09601d0300c00c0388906801e0003801104445802c0d038410500808010038810300052508818022100e481c40441908403510808102d00c440b003203a02510054500ea50000750301c00c1868460355400d80100341010b0790340b040359840c8d280c16203907205a000003002c1103800b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 353632122 1250 353630872 353630887
    0x3050406060504020f090312130605030601021e011b030605010203120907052d01020a1e0c0e010f050f09100512030f0307030c08130b2a04080607080a0b060906 70
    0x95004078040d00014008641c1d5002c00100e282e52074000c030550301d1091240d4409404021012410703a098502641c03200d922040c1000015100c0d40c0000340b001e4118070a540c2003440740e040c030a0425004841503c000078604130a03150160360400544100424503040c00c1d002c0000d81d900200303c2c1d042001e0002200310703640b00c6041e03690a00c80503034031051b880810704138291094000205c1d070075180300300d8494504861002500582c2c40c2d807410003002e01300d0800500d4680c62212030341004040c441c440c4282d04204c944a1089000003503007030b0401e0303100c25203034101480301d41000403000179883c40c11110780d15203260004100345503010601a584c082c0d866400030083e00c403010400d07501c80480030f00c1c4140d2a071408140080090108124402c000b66100c004030b41d000c5940d0074031407030143d0040b00e50f51107a0344902c04040c0b40a40100009042c0c04040002001c0c1c6030380401400113408a04050140d41c106108020811300f405080b601089241945c0d03051141d030380ca000c84d0b03003445050f10819141c1c0740 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 353633372 1250 353632122 353632133
    0x4022107060302180301110a080f090d1b05070803130905010e010302040207020a0f140a060c151d06040f060c0908030d0903090e150103050903180d0c0503070b04080c1f030504 77
    0x310110b0485c0c140d800c100c210204480320401500002090342d0751040f1541e500e10031040c10704019501a2042e400013038095454520a031100112510003225240d948405aaa02464140c40380d2201c0203e41011a1218511512407050703002040584018000d550505408040280b030600c070091007103a00144d202e045460b41080e900090940001080009030780302401c100c0304065004807840740d4241c1380301050a41c0160607204540d60002d10b1024031210500c0c1d02c20040c2400516a030301d070085d0000381740f03408000b0408948660f00c20521490740c8070041c90550150b401c0c80741e0500c28441428014003c48d20000b00b9500914007e2501280011480c20241c4810b50039070070810341d0160110402c0202c20b031026000140101c00c1e07804026a560b031441c2c1a4903406010a1003805c80e450607070307100040c41d000c046079103054028a5070300b0000743e88400003032034260f05030705c84a5018000301d002c02500d01c09100e505240c00b41038a41c0d0310000428511000440680c0e0581814940e90780302003414842d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 353634622 1250 353633372 353633407
    0x216141f02070927141207051b2b230c12031317030d020c0d020c0f06070308100b0409060f120b01050607030c0c060804022107060302 59
    0x1228800399044110044000a441d0300c01030080040e054245070a030000c0701d915070143c0c8203031401c80003942202c01d42c6079245002a200e80110359014400c4440107442484032000034040144100c00600c113a00c07124066070b0b1210200380c0c03840c0c420b00c0303400401d0051040c02010b10741e003c0152610f400500c0028905040d5101c90080030105000c0d404400c040107000026408003240804c03035034040c07602d6081401ea640ca105649450303800b141c143c441044100d42d05104203d034103010b103050303e0800507031411020403a0002c462260a0b9808a001100c4c019014465400b41200a85c1c0284490000c2310100f201c0784501034004041000d41400190300019501030031000d040c540e10880e54071a914035038030025080300e02403501c50a1058100096200d1110034445801d94000c502d101503030302e03200800205800c80c04003030342030280c003056440c0001c078100059009050a41c0301c9412609150051003040003003d0004260101e0511180000080008483c01128100d1030056651001d1804407503440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 353635872 1250 353634622 353634649
    0x60406110109231c12090206072901060306032001110d23031b09031203010f0e0114030601030605070203090301050a05010501030e0a0305040b18030615010f021614 72
    0x140f460b1a072420700003400841e0051000009084070f1100a110715804124084154080b0104092202d100c410140581042c0a00790000b03195a0410756182c6403001d400c034295180d04d520198200000c50311b0b140040031140980780078542004101c0c02d540d50400c54490307134005000000c400f5a55880245e00c40d01212414203013490036121070005492025000400350540c0c8050568a07107410111288054180ca10509074940084d03d01050300c4d941041d1a40950203060301401418005580c0c002c880e00214024a00c034090307456a1807503d0080003481106805c00c031590820300c1451041a54000342481c10b403900024005001c0d1100c075030a03440c62107080c0b04240c2550805c0100503c0039a181d00090480360300380c82c10300552031008085500c41043d44001404988140418021519550301038207900d6848031000250204600000349004c00444034940110305400000342296402249100000011700050203005181c4400e8850821a40288050458001d40080035079480c800e441540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 353637122 1250 353635872 353635883
    0x15040608010207110a1202090103060903030b0604141815090a2702040b0901060c120c020d06020309121c020c010f020301030318051e0d0212010e0a0606080c060406110109 75
    0x403210306203003040c441404811400d03c94171a0003400100b07407050f69505030400780d00402020305c2c3d81c2195516402001d090f0b10940426541d402180c6064075a40010005403141000c145010204002001981c07520101301c040ca444100c8140041c180790400e071507a8a0104860426a9680c0d11003448001d00c00e1804040302d2040008180c8002c02c0c285910f198181d002751000d001d40b41042c400d00c2701041081c49080300013461042000003080e14200c6099a004c0a07241c12000c14052f13400192891121a0003512003d9001042c4404d81f10708000c0074000c501025003450801204a01c0c1170300c80009011440c1800303400089a0142c1d03102940122825680726200f15103039612401c004202040110010001c030f02031520124003072a140b01c500f2190074502c0300c0031340171100c07143c140141c03001c96142c1240c01881050074540380e0034003070191545845030b8a00400a00301241032201c141c0d0b071164042566a00300001010303140d00c070725048400340d581d141030160141c0043c1c0440f500500904c10043c15 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 353638372 1250 353637122 353637127
    0x6020a021005071805030a0519060b0607080301090f050408090f030c180108060901021201051203070609030302030901150e0a1512080306011e0c02101116030c0e010608150406080102 80
    0x6858110312500c002c81e1018080c07044d030702c2e1100141a80d548480c58058030b0380d8000c81d04060000c0a4034500d40071203100303013004908004100007249031608681007c8402050100045c031400780070344651802c2c8032407082c090000f801c06d5112000310744281c1c01000c0c089c49400907144a035031410420054942e030054003100d40c0001503441401c010304203000300c2c02c0710b000e1500454403945050080d5401e41031020104145a4030b04030800c041541303088003034002030105015003008104030f8800c80e0030280c000d4074096075030310f0701480c1e15085404c4081d01c240f040c0e6001c1000c0c03100681c2e840d03045612155103440090600300c2c002c42d1034544144d0b81c1c400320448454601138020007903454051400b0b441c080e2500d0440e11840001d0390b14101981030350305d00051400c2c00600140c907143c2d005864681c01c500700381104001e405011030408680b014440c00c05100e0240400410000356541001050b2140303d540701541400f800511400e0082c9c680b1140902d98400c4114a80c2c41e41d0001c4000c0917844c00855 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 353639622 1250 353638372 353638381
    0x601030501020a110325030e060d05040b0726060a03021005040311010903050606090a18062307020d03020d0b09072f0304060309050f060112060e120706020a021005 72
    0x28003035804482d088000507030003003d4070700044c0000252100101c1d10302c0340340d0070050ba02200c2c00b005506000f007a0f0400c04414140304082c0c90f0302c0010105603d0301100032070a4502400c015042080140c010f0f4200301601906c00007440300302c511444600314014846c44107071180d00006494140d160000ba5120483c1000075107100c0c3c005000380112071056620b00801c4440d00c0040d940c509081c8009030144c0c0010300003407490702d40340103040d6103d04608400100c06e0880b8100e0216041d100c0400c0b256203540b040c00b1440304040d18010440640d0751107203011607103414040291a420050002c40a2640110f25807402c010035030050f920344900902203401c1440c00702001030801b0781e02042c406036803900303204151040c41c2c0781074514107900040000314a06442c01c00100c006200f2104140c0d05801080c0481c945600d0512035103000785445400c1d00c10703558050800c80100c0e010320f000550300d41d0018101d404154501e0003900c1e60b9503000f400041e250303001e100003682007400c0d017010f5690841c40e05c400c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 353640872 1250 353639622 353639633
    0x70206130314061603060609050d020a030611091c0c0e04030e0d0b06011d0102030415031b020c01020d050c0601030b07030f05010e0703060b07080f0f04090501240e150d0e060103 78
    0x8504c1058501c4c4003151080b003400068041301d1030780c010740d80040c012910900c080d0070050300d204c4051348040c0c50704947c1c942d82d841d2001100c44204088003107000020300d082c0e9610b4001c0d42c1d000c00040e000c5c40400b0100b80c6584078007503024148111003420901d500050240f6020f0101c01c6001e56025103403410340500d40c9003107924042d04603100d13030100d400280905455076190140b13450544040e00150705d403a041004e81b200824020401004040c2c613030032100c2c140b81d115108040d4442480d00104400d0300e810001900f089204481c50081120500c422046200d0002e441e0341102e4010700d00404503102d801046010300040c2002c882024100750001540104c507a000d13502c20300e01c0f0307902000341e25160034103843c86100348480501000400c2c0140211211410010a2819450101c07140b410f5a1002000b0684009900c0b428010495140820723282d59040d146041074860b03407911807824600580010244000202032415029000c2420054141f640d032000c0c1e07200650008407140d5607901d1604 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 353642122 1250 353640872 353640883
    0x201051e120705070f0b0a020d090609020306070503040512030406021623070605032202031c0909061206090c1d0126070605070606030602030f0a0b0303090105070206130314 76
    0x18180c15500c00301c001101036118105407114507600003c00351403803c8903158038410610141c0a503c0f40346d820041607180221900c0f030f038600f0a109820108214006004150611100604076024041d0401c20400043e401041c0d0102c80d0601d1a030098881d100c43c18008000d0045030500100d0685910310001400a9903007140c400d042008592200341e00c810030000d4030303140c00e48507990104030140301040c103002502202050402c11441104061007550b00024034100c0080d40c80c0c4803000b24081035601d520b41c400105009400c05440c1072040700e20b4007800464400c402c5001422050341c0380b9030b0780100000095424024001c500e80d07400e4454110b01c122860400030311800728064506100d006000401c140c8401c440002c02001c2e001e44c9150000684040d071200c202152030701c0c2d90741c002000180c014030203140210100340c0d2900091400f0702581086492010140348603a200703000c944050b07a800350440b548141e069540c02d813582c13020b0300018444080d6030401401003002020f0740c41c0f214400503d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 353643372 1250 353642122 353642137
    0x70503010924060b0f18030118170d020403150612030e2e0207060816020606010807022104230a0b090a081209030610060503130302150108010b03010c0201021201030f0201051e 77
    0x21162406c06602d04160882d143d0403041c0503407841c90008000860b4a50b40e80000101040303164074600005402c01d9012079005400c11a50509003c031a0091044070b849080c014001c0840c17960700320441c0b078402a04424209052034854900340701012050380340c010b00c02071009403404141c00e05410129019487d40480d02071380d800200c2000002d40c824001281c60181780602d60050095070322018011940c5000040c42481903104a04040d02c807416108076800d5495505611907071164101401240e0820090ba43c00602c400c4082c0152001e80d6580c000701d046951480c03c0c5640c0304440404150407054540c460b8540d4081d8070018038031604010b000b0400000204c042d10700a0fa606a6031243d004928060342d00040c0040c40000c80381200780c141c1601c004d0290040340d00201840c180034245a074260400450303a51558801754481c2002d01800c5c0f20555940000c0d030404da490805480c01000c1403001403c240d0161400d042035900410407180c14006c000340801c1d1140c00c0d101881c00c00e50102c4d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 353644622 1250 353643372 353643397
    0x2071406090a09200702150901050f070507030b06040c0f0f030b04090b0f06061204080702181006020d020d020c061608030f0405060a020c060a09021c0311070503010924060b0f 77
    0x41c90f03402d540c03662070407605101d03802424188000840c1c010311150750440c80000e418070502f00400902d15803104003401200384146c0040025070b007076140c41c090003100906114061801c000c82c04001300d4110000703080d80c2d001860011000c5402c0001140034021245009411505e001c3c1c0507014808488111031050342411528009078403440b06100891080c00e4a0600c091001800301300092004801080b01c140000c0031032003051110300500707c641c0b00656152000a42404040084540600141c40741001c1030010f0b1001d60420200039448035024089544140b00010f01113504281441042c2092a0494070b41900ca190045969224100a59060b45d0f02c1c410b00b40042c22070b900320300884448844100151030320b81c8030046020041d20b0085000c990001454100051810b006003850582600070303650340703000c05502101107082999a400c010b0190b41004100008144e01c403580d900583d40c080303148110700412074111001803090340c02444941000103401d030400b41c4950080d1040c40140c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 353645872 1250 353644622 353644661
    0x40b04030614180303150105040f0b0703030c0504050f090901110c1e06010f03110d050f0c010e0f06040e07020708120a170103200a0503100203240102071406090a09 72
    0xc22a214040002c0c3c1415095008000042481015500d17001d22040103050071420280c403500500b8030441075420981c0c1c407920104000040c50392501446803004464140140fa003030905020840e507002ca054130314014680c08000c2a407251003544506081010301620390388072668039603004e0702e4080c0184205000c1403581c181d004160000702d90b42c5d040300c16103211184540d203140e4404010011006425074484030140100300424024400f2075003059034500a804028103480015059200b40b10003907000b10707440b140115240e19981c04031802d9445040308110507903a0f01600700d01e04109038020100c64050012116034444c0d406024020b110400e4564011043c118540300c000d00100b440084c190f20030341d45883c105140864116002040c0261042006588036000b00340341101c00042500904d42c00030811041c2005e80c424180c81c2800c0c1c1001060750325000000130340d198298013607445005503920342a440c940c2c07031500f02c440089000e0300440c602941c0e641004000c01040d00780d202841c106 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 353647122 1250 353645872 353645881
    0x91c031806090b0a1103120108061801050402030606010810030c080a031409030a120e190816030b070332150111031209010b0d05010204030c0b1603030b0303040b04030614 75
    0x3840840b801e90300c2d402e50030341c1000742c0c100c0101c903007101842c1a101140010480d200310b803280400aa406007440b80700910f401d00300031080e0340c40c0b940500c48041c0d01da4904004e100060f84c01003015500030000b480c06100075224094003c420340c8141c0c0c0000c0c02000b4080d40042c80d82c40c041000f10540c0d010341c0b10025032200540a42003184030342d240144d41a0080440240014401d44400074000041c3c50b00011043c520f1001c01c04d0320741e20b0840d08409506480c0b08006060b400c00062404103100032061b44010b2442c0d0b0303900020400600a001410348a407040f22155240d880311018042d001001c401c0d40882088000d02d03040c0c401c4e551816003c99128429107039500610005150030b11407001103141501c0740102841c80c80010b0510703401e6540721b4405031b80d43d031f0f01c049469031400e019200042c0d6071807852410012002c0198440199200280403200d480c001584104a0311b94150134080386210025001034158030441d000312000b5000450040207000c0320703a000024552030302c0030b14270341f40d100c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 353648372 1250 353647122 353647127
    0x3130219030506151021020d110301050f100c081608031e0f0106021e0106052706010315150e041a0312030f01030312090c17100501050303040b091c031806 68
    0x202c41440c2c6001c1815006c8184e8607110a02c48031451003001207005041404030740504040d202414440c8080c64000720041c003052618030794440c40300b402100d24201e07202141101400d00c10b20140003904c400000711349600d484900c0141840700c20b52000b0301035070300d107000c003000031403520f007409a41c0c00b01141c00002218030600000340d071706075202a0010301407800003864000c408211062000140d540711400040c441d102c4040064001240460140b0701c803180641580142c5001402c0300c4c109070800c00700300910000320b0842010785000740f08807810300407101d0068a030070303c3d0105042d0304903141c11402c11294121045620082c20224180daa501107240212130b81c501003510341140700c00c0707070078010800603001e5a811840303001c040501080904c80358490010284e408d038083c0c45031844206044109810900401481090069081140c1d50600000c2a500e004501441c00e06180c00980c0d2070280d030301c10040c07141c1a0b0301040c02020020b5140390040c0403240000e4464442c1568640201f413460 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 353649622 1250 353648372 353648389
    0x5040c050a0314091c050c061302030d0302190c02010e13200f12100e0f01410118180b060a0f1b05161401050a02030313021903050615 59
    0x4084801041782000300e04607445072480c1d801000c3c041c000c0c20407038101100018884c05204007582e05064021641130300506041c203220300b0081041510401400511002c444112140c00d081454100500704862005823200c1d440710360b0395a80444160749050400e055900a00525101c003e5801c414004007035801c0080e001d84400d4818000042c0010040c0c0084200713041d90240c0440720300407200d07541e019050f2044005941c0d40102c0e15600340103018a100b00c0c1450540850306142ca510501030303000080003082c8032403240c0b0b115000742d0a015403641e80310385c4d40312150b01220500c0a601941d075a40d8000d415954818081c80607043c401000013901d800d0083e40c11200342a142d003049813080d100100c46904211204500c407140c1190440003041c810030401030702204440750410400c0c10011320001e420560117610741040000c000c500f6095a01100b40c98210740300d401c0c4954561118400940350701040300c1c1d40980c21009640000502c080098000d0041e40313860b00215000c4a500240903010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 353650872 1250 353649622 353649631
    0x31206100e030c13110307020102030a140402030c2e050702100201060302090408030615180f060301082107060c05040905071b020906040e01020a020a0215030103120c0c05040c050a0314 81
    0x503080f00b000d506003400c1c0040248001c0028110000d50140700c0c06400c241c0b0b800030740306103005070341c04070030422030500c0343c4103094021009030f212030840c0c54140d00182d651111660300758061840c0e195048500e00c2c090352103900040c4810001521245400c000600d540c000d1402640702d0040030350076001e51401031080382d003940d402403c0f161590307945446403d411b92002e0a550380080c07035507811400c5041680094224131003142c03001c0400904040410190117240038140d80f0030707078080004100001002070101c526041c541325968544246180d010094040d0460240c0a01e043c180a44015540b00c40108162401c60500304010703119408200c4805031303a0710380e800c0c3ca4007841e503940b40076240c044510b5038070003001040481d14003140b085403030076a0070990b02500542d01074401102103103880e0f07070311812152007120f005055616603111507002041002c04601030288100c200d109101c03503010340030054103000d0402d011429000704020711070f9021007402000246002003000490303100c0414103024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 353652122 1250 353650872 353650879
    0xb0a1715090a02060708090a03111306180f150902070308010602010b1008060319110f0108060a09050c120c13140d021e03070311011103160b06040e031206100e 70
    0x100c0b02e0315030910941d0340c0414425202d01100380301c680d0b6160740350144d0360f001e07500c182d1546010316141c9007401070181009204010031814488148200507031903a880e607880644840200c4d4130a03804040200400c01a04190010144d03100040b4001040383c009205c0544259500740f203587e80c60350308a00700e9005503a5541d005100c960301c003503090b10032100c09822140c01000d5480d11101c0b14280c45a00c01085011031b045802c08002e05100c0c54020f81300701c0d070a0006e007400c20b070610346100011008480d50103400c1c8070503660000f2914840031034085d85c10f070f00751580002825007011001e20314a0f411070405000c40d0041040040761403101000c003001c0e40c04d0060000600d960311a0700304802c030076265890410201e450540e40c04a0782d41000410000c501800c1040442000c1c0c500041002c0104003010303003a039108014140c0c51388400c00101c1c1a15410801000203a00c9280c001805014030002070b003c01d100111b200c4502c542c0c0100010b0085a08440c012180c2101d61002c0c0c4242200780d502561 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 353653372 1250 353652122 353652133
    0x41e080f090f0a0b030604020325020109050106090b010909200c0a02150703020303370b100801181a0d120206250c021c12090b13031202010b0a171509 66
    0x6c0c0c5040c10340240d500030203100700c489010701c503440c1011007982c069820140140e460342100c00903c0800c0c0320700300c003a020020061203845403100010300011014400c035002c40f69104c1000c00b654001d0b90303958221003000303407001d0340c0c440d104035405a8965030b41c1c03004e91042c4180c00042009a221500302c80000b58503401460441c0c0d40c031680c80421480181c85205000a58503205124075013215800204502e807040c0050400d05220500102c1c8003004181c405201c001001400601c40800340702089195103000851050901d41e071440742511204105130308803408001407000c003c0c0c0a4880320340700b8055070071249155100341d03081c40c0c9904082034068080d80780c41d0a10b0069407050504240310350001e014a600751044040f900c180c0800600240d0304007451031024001e0950041c594001440c5a0f850b107400c191036203070747e98100c00c1c0c1403100800300e5030000794032560306000303421030b06416800420008145580710b400102a40584d4440e010602503030134200b0300000301211a82c06264840010302 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 353654622 1250 353653372 353653381
    0x30c060c210c0607020c1018080d0c15060303140a03020d020d0902010e18060d05030f0703170a020c0d0f0c060603051f02031b1b010c09060905030a0506041e080f090f0a0b03 76
    0x8503290340c030011854001c03143c900d009c180c0c40e00030080045441c01d1651981070603001c5040100d03407903050700340c2d009800b03081c0002000400d9020382211044262415041c0d603913184802d090b0300910508007840314860000c140d8400844080e40a808254002e81311290f6000075101000551407100030800a000c101101003180c60401d580c200519070311034000c0701d24204066910f003052ba0041c0b0b0003240051450500103103075107081982c581d0000b50985080d4281210f409210f41c481c0011102e80d810054a240040390213446104802256038000c07108001041d203d041c082c0d00c4501c1442c0fa011000040541c40008805c18422280300300341d0541e0054008044214a550030303400205003030000003016005580c4c0200c28030688003401d4007030321071038101d51408034040c00c4540d46074011842600003440e0600418404110282d0041d44603116104062140c1040002807400020282541d2004a01c1000c01400c00c0e00920031000c04407101150f01c5c800e5410007811400c01c0c0584480610f051000c035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 353655872 1250 353654622 353654627
    0x901050601140d0921021903120c050409180b1e0604050a021b0109051905030d0506190807172a0303070f03020303040b0a0b030c060c210c0607020c10 66
    0x10f05594040c03000124040c403094036100501e08645d441d82c0f12072100044101141a0100300300400a0392040c6084e0340242907480140022101d0030940310260340312140040c0f0140300303e003180d002c1c00d00880c0070082500d40740350002e00717902003002c01c0700e08454403000b08502000241e12031054085c24070343c40050740d69a0b0f06000c06081c0160541d1002c5409000041c4540c1e10646114401241c110000400014a0070070600d003011003500000c83c2860541d0402c0441d02c040100c415940030360710082503d0f110700000c10419103540a064560f0b808450700440d00100115600d02100c01c002c0c0030300f2900702c1080e03415881c1e0800740d41d0490b4180d0500c1105166100c00204580c081500405590030884903031540b81480f100c620049005820000410040010340d40490750400003c14080240410080120342c2e070b80d41900399244140c1000c2902a0042410410205100d8100440300030300041082102502d42082040c07a02c01d00a500005440078400203000c0e407400801440c6a18212006a09 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 353657122 1250 353655872 353655877
    0x250810090203010f110c1009080313020f03010e0c01080a1503120c02030a03080403030e0d020d0e030304080d080103020312130b09040f0618060608060d080f0c010f020a08090105060114 81
    0x7260195207800f10000310110701c0c400c0e1000c09000700c600c41d503078007001c4e4170340c0e41400c0c41d0031980c50465240c8a0b01c030002c5184001038a030320108010010081d1415030002440b203042c20b5010540c152300b0b10b1070a04800c2c1011504c41032480080c0c80318401a00c44511030800e44148981d02400034814503c2000850102064004400c5103810518041d80454001c00c1c204910f0050070f0707021803080014441007603414443c200400d400034020f007000001c0000001d44418241854074100108c9000c0f03654907583c01e10131a00144104070498800400c0c45d400038145010911050b8464092850365401c50800b5100711101360b880403400c120300d5401c14560010301d4106183c50f1b0b800640d688400601540d20f8880d450103030100703042e034103104404480d14000392030040d00000100910281030284a4450195201c01180d200c45002c2e01c03411075884020340c50142038400e003000c4d801c050058030034000923401003804d01c0c00d030368840c0b00d136035101c0d82e1007400d0310b20a5940e02d000a404134060241946102c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 353658372 1250 353657122 353657141
    0x406020307050f0a030203010608070c33060e06090105010f05041a070605040308010302041b0e120c0319050d0e0102030a0c0c090204090209190806070e03070512250810 74
    0x2c009040c10280c00c180c0085401c848440408298004014049690030842e4280e03c00748929102103c2c00c102d544400642009a490100b25140d01070309402140c1001c145248224824404001047c2e60700c42c104e203491003c0c1c81080c0104122800400d03254070591a0100c8901d2903103034a4038007450305291041644501c1c40340320602c003092204034000f4040340900303070180d4025501c007940d650441c0100003c5803403e0002002c1e01e10303103452410307009402c2131090219003002c8815140c40401448440d0400c400300407015498003400304280d188110004184940301e0180045039500d007452401600c0c06038014103443d001d60300520407195001d20600901262521440e84201181d80d00c0003140140d0300240c20254499801260108070743c10440096890007e0302e8480880707151501d200c8030385414000d0708403030422883c1440c8074030a840c10014540103280141c00c1030111004035002d1a2a050b000c240031354455410083e6000ca02003d80800b0103450556003d04804207070340d075581e801402c1d00354 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 353659622 1250 353658372 353658377
    0x18031b030513030b0603010501150c060225030804052a0d050a0b180f01060b0714010b060a0f0806010c020f01030f061a130f120f030c050d0302250b0406020307 70
    0x2c10a00307111564000740c1d006600c40d08002041d41040782c00c043c00d6900c16041031f840780142160b500301803030740701c0d0074900d410350040b00c010780e10b03480344107030882a4038111000f040741081128000201940042c0c80b5100b280a20140c41c1071807002d004000d504d00d0b0741503440c0c480003801350b120a400d00d420b100c0141010701c80ca0454201004030b81d03030746011110458540c26141d40000d4020a4410144050641458020001c1100c02d0900e5131606e15400b4603030000d002d60079440441400c00c807003540891944a001000a52184060000144080600010207001601030800b08070300394020901c40e400c00d540104000c1c0000c20b520011802810708140741104c440d1207a000103041e00c2440600c221041c000203020b0b0351038a504005000311480c650000000380c2c500081081206141442802c0c61030340f24229514600303403400c040b10074045c0010702800b41d004482c00211516015401020703505040600007101034080c0342c040b10011402070028148240301000500004c481c2d500946d03210101c0d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 353660872 1250 353659622 353659627
    0x60a0b0d050f06010609060c1e0503071506051201021204080c07030c0b092704170919080d0c02010c02060d180803011e080c090c0f0708090418031b0305 67
    0x40e01e030a8607003a602801038500da0400780051051961292200d8040d10240c1464001c00c8078555903600c540907000c04011500d4441c0c8400020003409204a491651700410f40a00e041540100c1100500c03403403090910612221090051100041c000d540300c02d01096081415039881c0d450340c0b103e0303034858641d600242c000d083c00030001404280c0901c016200d5070000300d072030314800000c0c03211000c0300c000b443c0088142002483d00e0107016444141e0300503484440220002802000c00d02503018038200b1590141000d000000411551540c01307044a1014040321078081e4203500540321042d12401c040e0000b2002559500036080c1200204065400642e000508400062603042c0e189000c000480707003600000010002c0f1112210b5403183c4690055008105034079000103079644000024030303517001e80c940e10f002485005080064a030501d599042c42950b880c070a16141150b41c1c003e8060503c180d1520981607079100c029041290280d038544c54800e030341240354981203a076202c0c103c802c90401504 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 353662122 1250 353660872 353660899
    0x6180a02090712020403060509010506010504080d050c070e280c050406081b0c06070905090f0a0914030c0102090406080c15031b0f0408060f0f07030f090f0b060a0e010305060a0b 78
    0x3c0c0c40204000d50062000244509080311802c1c2902c4005d000f650401000303002c10311841c04040b80704002c4012900b01a5a140804000349013011441c2d0700c000c0c00c90b0022402c00c441242d08868000314221186030003500040c005042e901110301e50954100003130001c1c007081c0951070003800d46903000405d52000c0200d20700402c3c00d4000070340c0500c40c1514903800190602141d03e400c524a240a080100c903509910701c0e01340c0303292401385030041c2111300142d181e00843d8203100b4106541c0740b0344014581030740e69500b241d8418501035403040e03221078052031518600058020010451071203102c00108120b0b0000005499414107030000350800000340c1205000920051041c001480101003507102151210701d0300d01d8584c10301200800d0b40341c141021400308520710610941e41a40468107040c00140202051340400041c00c00c1d4000424042d5405100e1042c04610311040e0710035802110910b0745151500300c800801a8207200044c03042d0310101c04225500b0703050b0002c40019402030410b8419480 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 353663372 1250 353662122 353662157
    0x1120b0901031209080a050a030c02061207090f0b03011410140703030f0c05340209010801141305070e0a290901060e06030610021501090e06180a020907 67
    0x3002e0388100c40307000507164040015078110314100014079207030700a000c072482e458617080d46174440d004000f0108086a500300e4211350300e00c070640301c0c8403c00b2600b110843c030380050080e0441c2028010b078615118010800500b42412004507810382d286101c1401e1080785034070038403180440e80a4080140100c5440d40e00c00710180c80040c1512502070f1340c01203012002401c0541c00c0700c102094400030810108000c002251101200803c03294020482001070790b658440c4001d48480c0300c3c00291700202c2c000000914240c15000105042040c0c90014011340382d10f1040702080f507180e14001c105e604600400c002c2140c0100c01290302c90b80710003000c03440c480c002960300c48069603040a018031040300d107900011814803079142405407000d402c00a244040c414001855800020b150b0352142d00143d090702c000300d10921000d00d4504048064554550715909104050f01007841241807511a1500240f03010108192010060b2414070140c480c02c1c103d6000c1c007124440c02050441400510f00000d210441c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 353664622 1250 353663372 353663389
    0x807020105121f060c0305070318170a060510210c09020f07050d02010209060f030a060305010203090307050d05030f010b0a02070512010e060a15120303090f06140f0c040501120b 78
    0x3a040c400f041212001000411190801d4018900300f2a000085000107a0800111160550103041449003442c010442000c08010754010014440c0c8514421240311800907250301f00c144070b2581807200d569001d84441110f0802d100d80c54180754050300d80300c3c1d650020b010a03082c0c1c0e402008487c0140b511401510166031000344010030a031070029035681805010301920212196902c0250f05d03010400b0f001a00d00e018444020240100c00004207a100400f41e0020000b143d01100031f6440e444e02904403a12900240c02c280c4040c05a460000b042c0c621a50449100da004203401c014240d003000c00c42c2003281c101072186415841a0301000c80d00350381c1c80d1254683d113000d440000c104940c104000c1741c00d1243c080c01c450800c5041c03d02ca18040c80e000010002924541c2104103050202030038220040c03e1075140c060421901c410480302400b5090708846480c10540c011108242c13a0356854890340b401c2100c2081040b10280720900c015849652100d07c5000200c4020a01e0704440d80001c3c0c044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 353665872 1250 353664622 353664631
    0x503070c0b01121b060914011206170d170c0903010b0306100602010c080121020d0b0f040c05012c06070c080c03010b060f03011505070821100501020a080702010512 72
    0x400c68210803c0802c060741d9804800d803008180c2e1104c4540c50194080c0c00700c0064042e003600c014410320103e03001e0344074403900b100080505000b482000e5499041d01c6c42c00700e0180c80c0d00050b02400800f44d0880f401000680081940c000f50b903000e80d0f4940066800715000300141341c0d03265484490b601c1d0b0030759007007060900400850b4410380205141244c06030071150303803060030b0b0180b288040040102200c415025071a111080c01f00080d181914030000340d0400107013000401080e0400280401a0301d40444c4500c658480c114082c101c0343c5070f9005440044043d000310304400481403100742c440501c220750209100c0040e04144c1840140d5a036152540e40f29003100001c2d034003444148449141c03d02614903154815a6524900101d0401c141000d106c140a2481000b140107001c2c1e51003403090b011103e1141e0000f00458803120054090080c2e081303038205041d00c1d0866200480d000c026054219402c444058008003100c01c1d081c0d071102d4680e08158410380c1400018061480500f1a81c0a1540306 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 353667122 1250 353665872 353665889
    0xf0301061211180405280507031b03020405010f0905090a1116052401030b0412020a020a150e040501120209041b0305240103170c01061802040f090e0307030503070c0b01 74
    0x8040f503040c240411528020031120091080c89410045e0041406d52041d0072040c0d21000310b82c5a94031001540500308003040c842296851501c20000241c3c5540540284c1d0001d03030300c10303525100040f402c0b1903109003030140c1d6502c00503013404141b8481c0254400004e910726100c1d02d50038000001004e030f42c5250340c1001514107400c503c0e0451425003007000030036607403680d0011311404c81d41103441d41482c2810042000f065041050000030380e0038003c00c446c10b01e05034000d20f2010402d46032030355140800944d24401000c154180b4081c2807502e45401002c0c141c85070320301090716409141d0200403400030302a105490204014906048451400d9015030185000310020004411030700105106400300d600d40038011190b100042c00043e54007068100c2e04e00c90112207076220205404400c0c01402130b42c0c00301302848802260100c0b075005507009031040340d14049040d8012035072101d4100644421074484d1005c0e40003003240c070002a019a000d1904400b86240070340703c882642e42d54141c450300c20380001d0f84 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 353668372 1250 353667122 353667157
    0x15070507030c1d09010903020616030b090103080a08070f020d0f0c0c090204170a1a1518150303040b03060402031305011e050a0c230c0709050601140f0301061211 71
    0x190485600f44241d00010301030000c0050182d9a10020b4940c44007410892800395080d850381c0100d4865007000074a210000c08030f2455503924a0640c40b550b2103d020b0070301060024000a00c613900540da141c14a5650b03070064403078003c03450000c80f0445152035550701402045402100424111070716100584030444005a440717040c50a80d051005008800d10b07026400310310b405001801c00da244040f100000c1940102d607840710300c00030a01000401c0440e0b0801c41600f03913000da0441c01d00c1424002e0755607139480158074100405054407031090b0b02075024042c1b0104045055070a1a60007550320441d4a41041d6800042d56285405e48000601d0001d10307188007001045440708912506800002d10501080304015040d40908010003000c02c10600a14400e030a4600030000421a03015003140e0040e120415285d800e03200007490162440790000e0038030710310100c1c02541c40c0e003242c0c80e403420032000d581142e203040390071207210120071006a00941c81d0800c9107083d020120161034030f60000c01e913410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 353669622 1250 353668372 353668409
    0x221e110c01050603210a091502010b1011060f090c1507120c020906010e031204060918092409021003020a11161202040e060f0106170615070507030c 65
    0x5003520782c054401031290300b00314207070070146040407400c0d203c404000c2240d98942c850990291a42e10070f590040a461041075150540c01e68107520591941908607100c001e608480202111040b03003409240850b030b8003c90106901c4029143d041381c2c081460802c0f034000201c00c2001c00c0085405140e00220300c0d4001c07900d003042204034000d03205280d02d80d00e410a14514207400040c00180082e05a60521024030f00a0025840501200d0400c6005481850340d80340c0d507140c02401030219109a8000028010322101188824001c031410f0540141e04031341c0f0454800034998601c410940c200b12899540c00464005848500c03030f0712403040a989005807207543c6a80e01509408192502c40416000142d4104035911110001800d03940580c0d044e614109140c4041001003400c01a82c1a0742c0c40380204024529440640c2c3c13070305032041d56980072000d244000400300005029a00079038850750407020020190a6040603000d80d500030021a404542c5c1c13501c402c0400d00013900800058444501c0d0324 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 353670872 1250 353669622 353669647
    0x10110a0203031309050601020a0f020d11061c0605062d090901090501090c020c0319080904060b041a0406090b0a050d0606080907230603090f0d031a221e11 68
    0x111b034848401c2c00a03040400090399040c1000104050081c400c5400f070140d04184800d80300b5403040203001810042d43e4901c44611070303201041380403204807043d0820202003032504113a402c0d105040740200703030001142aa42c402e10013034600c04e541c000420f02d081c00743d0342940d0340d6401e0090007020412000541941440540b6040c0e90800c10010159813080c2c002d403919403800154540564080c40e4000b40f410680e2421200c244201e42a0561281c1840004030f5100c1c4602c004000325151551602529071404100030b205d401035101c1c5d0004580c80c010104681d202000040c03098110302d140c82d900c1d007144a480c081c11a800d5030007100004484904100900f18200a4500681440c4102d03400724550214401e031200301e12481c20f0b0141e100030000ca130781240300b0819111072001c1501941c6c3c2c10074807200020020b000341e07004801d40d101900310703807401428a044002c0e048003111400340003201e10824401c000e8108100d0040114050403581c004500143c031682c0d0700301125512140c1d43c0c09040038003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 353672122 1250 353670872 353670881
    0x307030c02060415052a130e010b070602030618090105160306030b0604090f02090901090c05040203060105071407090e0f06070527060904060306151410110a0203031309 74
    0x2040107552241c8103200c0454448128002d080c01c051201182550718035a9000c03010215200f8811001110040b520b001d20003130b00603101b030f0038045500d08501950307180c2d040071140081c4528a0005420803420000ca2a290001c1d540054003910726090f5800c40c1070100201c1200701e400351041e03556007060004203690003400001c00f1aa503d02409580d0035a00c0e00f45546002901c081d00c039944d0b80003103a04002e5460041d541c00d40c0c0040a06540b8a04001d845010301200d09080f10b05006a0720302080d94640361003641d019503411307510301c0e040503056918003100c0c00301035a00100fa84240500020840b03001d0182c80c6c01582280040e242188030410161329100003e040b1906000303043c4a000c0e42e1a01004000340c13500385c40d12651003440142c0c0c02280b120711415211a41103810518040144603003900720600d4a0901c04000f000b2a07920841440301403805203a81d0b43c4564056002000daa209001c2c00d10314840103170a480030307943d15a00003884c5a04c00049002404035200701081149114800d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 353673372 1250 353672122 353672141
    0x1205100e0115052e11100603030c030807030f050c0702030c030d0206130c0b1b0c010f0f1409130516020111040e07110703142104050d02011b0602030703 67
    0x340621911032142400400c4240521400f90740c40a5112444500d0300703004e21301c0c00308400719514512003d5200180341c2d4540903041d40443c403803207141485801c3d903482040101c030740555802d060148566812101d01c100604005c0800d511402c0c0b141da0040c03244101801030851040c560b0391040c491040c581080c9407807550b58825000460302e543c0c1940c000c6030302c0e80c1c084081100c83c0d01580707151620039070400301c0750044030080f800420040d44006481075012220603040702290310890000e0011a90146403960b40c01c0064048071100007040d01032130402d10342c1c5c100031080c03030700b080e840602240a0f50b1442c980c5241075600c2d0024009407400700201d28000c09132501c02400138206203100901d03944550320803288500d59260000d05003030301c00c01895071204403503c2a20342d41a078034245a41c0c000348104400b0840e00400f400520390f00c5e80780b0034a4000004011950b41410b140c4010003160100070802a0305021a41c001c0d119a22441c0c0c00c0e11500790b02c503a0006840b407d161308000d044604e101e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 353674622 1250 353673372 353673401
    0x2030105130b150d050103031205041101030b040902040906020403020a08030f1c0209030f060f01080c030c040c0c0203060112110a03030e190f030506091501060c0b0c04120510 77
    0x601554070384001c0211056070110000c03504242d0500424418091080364911101c030200340340c0f03690103107600501d0499001c2d6403a5030115114012510071210280c0703008142c20090b900d50310700d55000750030038a1b22160007030001414001940124064802030481100e4a6a001806100f1407170168002c03005000b255000310304012030325074003a0345841603e10fa8807594140c11055a01c80d003240d012110070060140640300185044520141c4e545000d458086084003014000300d10400c2c0087c074055144070040080281004400031702c0f00400c5403041d10420442c005903d2005a101000703d58020000034005114901c0c29080149544810003041131184071000b43c01c00109503c8070034171454440c111100d501d00840304c034155031030b11030644c4140742501e5919000005c5c843c010031814803a039110b000f40c03012016003115040000400f401171038041000f001a140209000c0702d401d9910600316441e2510b850349610102011380c85070401100c0aa0007001d007500b401c042e5000d903103240080c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 353675872 1250 353674622 353674627
    0x1e03140a020c0304030f020a0f03060905100c140d1b0519050405010e0108100306110703090503010e071802040b0f0403060b101209060f09051507051c0c0509032a010302 74
    0x4002c10340d1644600d11000d051018800c1d5030b04155652290080010014100a0015144e8918004003e8201c10708141c54a00410b900740c2c032070a082d40a005054070095903400141e007040341d418412900080804941280d484107154171003200a81039521290803911107584411010600c4034176242e80c3d03401c1c00100042030008011507600002d050171540c0c001d080050303d03540d518560a00144950f400600690705084000107801c26180c01868480c0c000d0342c0d41250a41c44078241400d0311901e800b0620305030302c1b00e00100310002c1000d82288001c205c2c40c8026180603079811149506404c002c80196041000040c2001046010302c01c070602001c003a102c0003000c03410900c0141040d80181d4840f1030007501d514003481002030b5036020803008502c040081204400c0307410702c0d5598a03902510706080300440b0000c18043c034050b80a03180f2918072407661a001244a04002010f061600b202d401407040c240160b15059400781300480c41951501c010b80310f040014808100c05500480380c4a0501d41304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 353677122 1250 353675872 353675887
    0x1b06030204031203020a02102d0b030604020d08130608070306210204020d020d020f03040c080601080616260901060b0a0219030512090303060a0b09100c031e03140a02 73
    0x4a03443d180d200c000074280183c031006c0c04242a82400e0100c0600c0882900d0301e0400b5092190201002015901440300d04050303401070306c510340442e50342d000420340c1a4402030004005103404019503040c1481501018107026180e281841041819000440801c04010030409120f9040c03046200400c90710f515501c0090034194000031500d0300441c04ac0c0a82e0b0005450300032000e00d030301103403413102c03448400310346d130b0316814202c0c0031260170076075044807441c11041001800100009181e03051700c0b034010280c09203484102d4196000001d0365038040c1881001c840c0070045550341150345e00e000d180b031001101c5a00c0d04c80007081c00c41d40103802540280d2400d001102c250755001920034114580c040c22a490420b80d800d0036180e03402200310036002800400204000d240011001e94064101600c080c04519190000c0c100a0301070402c0e40750304180c10600028006100d0450100140e01034107050000e2070358120451032145000a040700420707103406200110741c520011807030744184002da00310b0a00c1807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 353678372 1250 353677122 353677133
    0x604021c0c1814120102131403010e01020f030c21071805040509070303051c1d100504080f0918070f0e0d0b3d050f0405150d050a06091b0603020403 65
    0x402e26003442c00b5525211504504c9103095044400311180c4400d012170640d55a0490700d5101900c2490380d02a509000b420102141c05009aa40d00d07000310785041d007140d4a00400709081c0c1c00c00103555405141c00340d100304010001441d0103000e14080e980d00040740042c44c0003000a0b82c003030707400300d8012841c0904205585201054200543c2d40c50719009682d84200da02d420310001420f282d028003185007400a95a411001c082d080042040c0c40c10358131440ca80e080310404a540842e00603220f070404100c040f1074807401030014501c1440c000d11000001101074006d102c1d94508464503400f20308401a03059101d60083c003000090f84085400e581c41498540d101040f89101a003000c010b400c815408900f14003000301c030b9410000300e910030446036807032100c03225807a05003c2c0314081c021200403000f500603040900600d44500c248402440f202c1d0b480805101c04480c200c80306079a01d000741540740c0d0000360382e070180c69044d0340181742da01e85003e108a0414407500140c3e125100f8180304000c200000350 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 353679622 1250 353678372 353678399
    0x71206050a23010605070302010e1506010206010e0105010c0807031b06021308010203222102160501110a02150d0f0504060606110d0c030e0919050105030a02090a050604021c0c18 78
    0xc08600e0f20541b604c840d07240a0340582281d12008009009801120400c8403601b40c03007500c02d4409a00311042030366900e092031409030b802c1c080c00d4001802d42a004020400040040c03e01c50310a1415942c1c681510744a10760350309405000f01c9803680c001890b04103000c401000c00d000f03458588000c600d141050000c10741d84140303800d0f840704002c80b10007458080c8a0092024008080302e441410140d00050200948920a007c580c41655554020205442d4420300402020702a214020200710400da000c10030004a8441d501c0c000b10b10400141d0b05081050180d1a148100020b02003400d050600d824410383c0c0ea1900315108011030050b00c50000074002031480c08401b0307030b4100f4512124403410110303a0116030740000c5410106a400b8071181c82842c981101d402600c03113004100590321402090b46400b03400c0c5d400f03544000340c0310210b190024541c0c0000d802080080c40140380c5030100340b0316006030100045d603801003581c4981455405802981407451074840c10b038140c0303245090510800c07080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 353680872 1250 353679622 353679629
    0xd02070f05030d0e0405090120090108130f0611131205060c0f1b0307020907021005090d0f050c010615020d081b1c09150e1203010f0509040302071206050a2301 70
    0x90ba201c001103801c00e10207501c03d080c114401050004271807818040c024059020045e42070004001704002501881c0c1104003c0d5455844400340c3c0d8146601c0d1100005002020107500309440b040015203048454460a0030003070100d8021750b6581c42690502e00c0c200a0300030500c0c50404420070000201107107030811110070307940307200c0e1440124420703408481c40e50044400003074202c00007206100c10b550700050b9444a000a4020501c266500c3c80000c503114241280800049080668581c02d424000c0e0058191086040c0001656560303c000070361640790940038480c050b03085421420002584128040d03070040f03849802072200b800700d200000d280e200307944600645103158202240545050307008049015040708070390000e201e903000c0c0d8100821840c1c0c40007600344035822610142e0340070715041e203049076800341038040c6240ca020280090102d004000328110300070940c010540d4a0981c145003112405902d00007036929002c0c21060442d060f07034400200700c074455000c00e02c02c03c0210780082c2c1036 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 353682122 1250 353680872 353680879
    0x15031006080a03200303041203110307050c0c0103060b0d020903010b0a150f031806020304111207090e12040e0603030c070e010f050102011e0b0f06071406130b010510110d02070f05030d0e 82
    0x4407148ca004400605441c240403001442c000184411182c2c81405040e50418080503654038181c40780042d8111000c6200d05024843c050107036460803c0d041d4007403c0c40c0d01001d400822480c1c80b0100041d100282d58008904002c98103d500111950009004d00080e003503050421400800c00c4d215400d032103904000a20542d00000020200250007a48000d18140500310440d80081542125180c0409000f10251103140c00212080780f0400151030710400008103440346000d040c09001111030340c0061160b90540310404c48031034541c00402c4003400130304041c80502015418144941e802c0c1720950b105a04580c10303c26407840d00103145a8800404d130340da0f0740c001b030201c42440204409117005604140e20810105405040c04040715462125100d4902524015544c42c02d141d0113161301c007407014084282803401400a0705080000c0c04103001c11b8100280041c01c4100c04601d4080340802d60f01c0140c201c01d1040054904200c40700000c2d02c0c003100640482e10103501d00070070760581506410320 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 353683372 1250 353682122 353682143
    0xe010b03070e040f0b2403010314120c030702011805060d05150607081e040e07030f090b130203151501050318030f0301031a040b15031006080a0320030304 68
    0xc24015464848a0b80014100344141d110145100c0001c102c281440d500401c244180001200c3c2008030b80c02001184000081c210f03420340e01c4005102d144140c0070015480b903031407042009446040509154102c040003103a40f41741a2000620106a01d18a070b003010590303410501841d9242d4040d80c00084c04180001826550444034202100014044036000200003a0384420302c49d4000080c15440d41903113500c0141c04010305010014132891003000e503c41210008a44114480d80148494130810300c40424040c1c02a1034001422605131109042c00443c04404402c605080c030a04070340b100d10b40402c5401c0d141c101500b020030722245c144507041010000000311101e40d006403411300d042000c0100d0352180c2d114002c0303004682c02800240c480c41001c0490f001a40c030b200c10179a11460f0f100c0e10304001a02c80384165503009265004a603407500403105030419140592040900411504000b0121003030036040c080d20307c01940003143c50a2450303070242d0551100020032203800c664000c50f0904d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 353684622 1250 353683372 353683381
    0x5070203010b09010603020a09050d02013011030a140903030a0c200309010813080f070f02040f0209130905070314120c031308010b01020d0e030c092409010e010b03 72
    0x24010445180003a0b0b0060f00c5038004034035190b1540c00f4180055003902e0f1040456168020480c5984903444002d000600481c102200100411503a0030004403041c41d0020065002e84211306591800c0b400c1d01980d8008030810001c00843d0145031803e01c0c000c040d10f12281025660591240300041090301c01588403031141d840c2c503104013140030a10302102c0c0580042030920522640300d0340030400490005072a400411042e6158151811640740d1180c5020301d013030508005501d858001420544942031061124000742c3c455000b40c1c450b440e414000180da03000740070200405010b205011050385850482000d001420004091060301c0d0020964140300300c050a407607141031800000700f5800c01011a005012000002c0505000c5401c0c0c0c80e03481406444078a154201c822000d4220b0060340000c000c2c0320100c0c040c1c00e200218400c0602078030111000140442d41c01d00064482c2400d0b0f421451044610f000d01c05182101410100c0303031a1015490141030040302c92041c02040d0b041c42000001c076 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 353685872 1250 353684622 353684629
    0x917030705060a050a3801050c0102120108190203030405040905010902030706110c040e06130623150607050d05090a0e0c03061207061202180307170d0507030f050702 73
    0x690909070310004445580c03030001c07501c501601d01600d100a8440c18001ea62111018842c10701c0c100d005000e0000744840c10211481d02406840c0c4040350502c0010080c48500d240e082c0024040704110307800c02d0b880b035458100700f2032414001000c246501c0c01d400c0051801a6004001c840c1141c0303040314089039441c694202240141705c0c21000952600c50700f20005845500154030891a00700d05d429515206281700602017950030305060310302c540d0044000a441d84011220b04042c242c00388200103000c0303251154203626240c4194070240d2960340d0008101c01000302218018402e81c09489450800301c25981e82940d40c0030688500051003008900003040391039100f11400106011081c01004e82405003091501c0d41c01038403850b01640101146d201074040c006095030031510a40d883c240480407003002c100094122041002c01102c50007906191aa410804240030703103599600101c80900c1e803003080f490f00e208c0304040000d015041c0910008644c00c1015072040c0c0d115070400036621103051001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 353687122 1250 353685872 353685877
    0x40b030706050f09190305060f250c080408030d050c04030b040201200d03090b0f0405070510090803040906080f060402030c0108040f0b0106180503011103130c080f010209130507091703 81
    0x480e00407000d205003d610300b080c0005e18044a00600c152101c9842d0101000f040c0c8078121401c520b01040c1041c1500d5596447c1085103000030540b4103100615000e6490000d964015845610351354030100b04c0c1042016140310305900b010300450f40343e00c0c0074034640d1038807030944000300b003c0d041c40102400ba01c40d40200c0800130080e01408401e07078520801002c2c016008101580c0c054a41480440000e000d0010b98403e09014640140051a2080c035180401610a50403000ea0040291400d00001d03a010204040c00c040c102d005804038005081219103854013840507518260b03070707003c07800780800340e1404120654551000e00c1c0c51303801e035961410940c03200c6903070020090003449060000103001c0c1c0d00c4410202c41c14074089200c003600e03581e2000c041c00d9400810710034188000400c0812840100440b01511a0348260703000764081e55507088250405201d0070b200c1c08141d4002541072014a401642e291b4609040f5004100030b003030000d4000d0001029014880042a000c2110640c22004000713 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 353688372 1250 353687122 353687137
    0x12030412170417030406030b06090d060b010e04050f010819171303050a03080109051803160201110a1a0c19030b03011e09020301050604021e0a17010b18040b030706050f 74
    0x4100c410006000303043c0da6640c1c050700c6041c0000c1c0c6401645106481d1510440750312003001417611229503416241c1d01d005000c000900b0303062000007040c248103501d45000303807442200c0070030304050550305d046040c0b800c0c40850440b035079214012814240000d1031111611000c040d01c00e48a5890380440586988042d0b203036000600503104d88400d803410560b01c00411810f0751400c8c201485241c5270203079034409640e030203060715090781c105009190314281a004280f2070781d4014540030300031501c03103060103042081142c1e05071490282c2904c101e000c0171480e5440c40e0800a40c1c1d140c00d140a80254111000071000c00c190010540c03a4017000f011540c00350822500c01c4000c4110880c1e162020280c08001c02c84607900300d020354200f02c0060054a081d20995110700041390090007090710b402d0030015141c0c448801ca0040c081c00f00d200c0030300703036592445030741c080c05200c00700590715291000420b0304000e0f44c50340a4801c0382480c801c445540c1b404240344044031003d060907521099940c1c0c207941b0b50300076502c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 353689622 1250 353688372 353688389
    0x130504170c16080c010e010e0d060c050c0d36090218010201060e010302090402090405030c03030c0a1e050d020c2a0901121e02010c1709120304121704 66
    0x3400d14403403440032038107025801808020090380b9644000c029183c0d0082c2a425000c5a619005545254010301d9803080c0d28400600c0304031015256a00c940032a039103400ca440000d00d010880c0e16210408208802036024181021503581c0d00c0c50b80c9001c20b0302d2500d10a071109078141107544001e011140030a001500c0725020039511100b0300401c3c0c400c5200c2c1d680c0700034019824000d0001e417503000d041c05030f81a00d4029041c407500c3e41d90b580921107910409001180c01d0b11040215030020710060015500810f480307007086039182c541c442c0c001d1980301c51000440142d505100314401c0c594012044808103084003a000d0f07215900505040d0611004001c80c00c44180503484105420f000301095803800030f400c0314200400d903264040724054854548005102030380280e0003008041080a8074811a8814504070994800326600c1a0300f4132148a48503286207008500700100e89400410f100d0215074120095080601e0450710510103815100c002d0300c034440d4048500500750182d07084901400002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 353690872 1250 353689622 353689627
    0x3180507080619200f130605070b0a052e030c08060604051e1504060308070b04050f0a0503030c03100503161802090f01034703010b13050417 62
    0x7080a07584a400854129203d001c800c0300488400040b8441d07295118952140c0c05944101c4051405076075002864001061038107208044900c1d90006014000d84410344c1c034507031684070910b441d402604019107001341c118201010000c880050004254048000103000072400c6002180c070f0312035004981029103032050b0050086150840020700f00c3c05034800341e5040210b5590040200b50321500c542c4880c1e00b120280c0301141c181c082001d40b07030b108040000c0c8005070700d65480e41c52900e00e03400090216808a1a1010003090000c14000401907144090280141058668030942c503803100400b540740c1c0050200100303400b104480c28900107004c018046442c0c100c00d040e2030348003440d01d070f116545091041c0303617242c0c8603a5442c0c000c0d10810040940340c40404012030780190064480c3e110888262110350304814075562040404522400040080c100101c00c140c0f503c4a0844100710138a011b0707810f04203e40c0540c0c0714150040d861180702400042c03240c4036450000b2100c445407000c00d140300c901 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 353692122 1250 353690872 353690879
    0x90c180e0c0f0a0b0a03060e090a0311070f1205010b03060405030c0613020f010c1103070b0c06062719231029070f08070213020f07020103180507 64
    0x551119404031114030032112415031050401c1081c1e9089100781e500800101820032069100401501708002581000729242e625803c211754185022158403540750300c503490b88802e15800590041c00010003001900056040190360070b803189040c0310300784600c949180c006061200039407065840e0207000b0107554503401d090400741d5582e0040c0403103495602580010600010302e008094450076800340401c17101807400720041d214142540019690070880b41c00f07000d46547c0511841010744081f503c3c15464171008502d45140a00080004d801480ca24000071403c554040091a010b180c10b41c0c10042d0f40c0d84c2c0e0780038601046034221444165410480d2020413450030150407801b143d2020450703151595262403110034a0220322031081400d07810013140c062400c0703400160782c0342c040d40000185040d0301980c0740780c640c2055135401c0d20304883c00310300321045107041e03102c083d4280500f450550810342580740410341845a15002410f140c1e955001c80024003404103012400703038000c03041e200603e65 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 353693372 1250 353692122 353692169
    0xb030307050604150e06060d02040e0f1f060503123f2d1302060d020406030b03070f052b060903020106060201020f1204020613090b01030b180703090c 66
    0x2000c0c2c42c2251308600c100720448005450b44203003501106008002c0c170441e11107100f4066440d0281006907041510340c030701c07001c2000c020856008852101c0700144218190542c80141d05855800d0802005062030400c01c210b603800140304a0700d1441c18507850b510603011100800420400d441031181d15107031a4030003450780050408100081d540442c03010300703584001d440c88081052600b50781401100f0741182c5000100b4914555218040240c8401c1d0103849400003a941e401601a44400760b8000400384140c5030326010300c49401e6016001007048034100080d2041a10250103140e00840c0e44240249603005441a07902c4415020b040e100ca4102043c2400c07000b0b051035a400f640903609103000028200c3c81403003150507501c02d0301121400e040c8070605000200c0c00c098000e036406801170001c2683c03403844031fa088008011491000030340740312075000941500c400b001d4980c030a140c4100c2110301e499a19903010740c4402c1601c2e000480320703030074540b80d0410940c45e00201c00080a4058000d00c0300c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 353694622 1250 353693372 353693383
    0x603090a150203150f030a0b0604020c07170c0103050603030d09211112030c04031403040b1b0f0a030c03050d110c0a0605060d0c1802070506101d01030c180b03030705 73
    0x342013490340f0b80419180070301c10f10207070704910710303405603caa82d000000c5251440155044400184007519004200000600d040019003000710300031412407801480d0113080007002946c00003030806000e585003210004c2d4880c080c001c025481261141d40c1c9100304a081c4020040329002a0440840740c2c000c0e0000816449007550300328824401ca9000503008120042664452100000c150b13141c071741540d0b038050440000050041d00342c44113020101c0c1030300112000d0007080e5004200650040050704440b0300d41582c0c038014160a030400005036020039030200d007442e102038240c10955540c0c941881c01c5801040004140f10003c0f01c00f00b20617030050b0011800e0800d460103a0001d00881e1522810000d100d00007050003031682049074001c020150300c50b03086410705038034454014100440c0d9115103003025012540d800c0403481d09102072120010980b40c400d0580f42072a0a41300300d6045030350f850f200820394000c00c51f290842d580c000700d5080d03171500440c2c003901014081d661144000c0c600290390f031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 353695872 1250 353694622 353694631
    0x9150607034b1d040b010903020d0b040b010b1930050a0c050313030c0503070c080303061804022404170c030606030a0803040303090809120d030b01030b01020c0603090a150203 77
    0x1103810610b0008014858940c183c150502208a041c3d50100f00040200400300048010f041c05490350000016903500f0341c02880c4980140400035041c0380c54a0000f05c035080503000102c02d45010301003000c2e11586480e5403000a020f034105100c07a864030021400040110070440d1940060404880c45801481d0700082c1c00303407104520a201e1400c00c1c2c407007584c1a001c21100900c00121a1180c02e001c07900c41e11340400c505002d40d066a01e01051526440090340d4150086c00d0326a01c00400d00189082c500c0010100441c9000e8603860350820380d0006007004404000f041c0341e0905d8072080500c0600030f4044500a1400f02103151083c072201342000c3e102c01300030a00c28400e0247d8800600f0500700864000760482d4409030003442c41ea07840c0e034250002d217000314003602c0c0030f4014481c0100ca0b4841424a40d508510a0010816440c1071103004080e40d0840540c1e44c10142031104110312640c0000792420555021200503459581d4002d070580380070752111000e018801000040d800c0c1a905d980114041c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 353697122 1250 353695872 353695997
    0x10b0f010906050d051f170601060305060105030402040c0e030f01060f06050403030804061a0a061806050408030706090f05031902071d01060f02071a04050915060703 73
    0x582189100558540c0010710501002c14000c1003140c0b443c80450b440603502140050841024003e03184a1482c014015084443d001480118440407c1020003049004041c68a400d11075440c001c0d00081440c0000350000740030702e40741d0749101c0c2118014141e03c00304003006021188400491410315010f011a0301c2100d2024026030000320b409e91250341194242d98058954802c16119551000c5c0180032081004c10b40001260700380e02641d894528010080c0b84540e101880581004000c5031001c1083e032040083c09070030081005002008402c0d0b6000f00d030840e10015140c00a03003400442c00c816060000c2080c000000c7d072900380a140c031803900d0700950325402c0301e240c1916010f0040c4581c0007804000c8101d40d0100041000b84e100304440c5004e9441481613402059071660303448002e0075008203101005001007020700080c203000d00c443d81c2c0414142004000750003d1030108000307100b455006400c009024051041c6005801b89808141d00304a01c4900e0031490125101862038004215003903 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 353698372 1250 353697122 353697139
    0x230d05090109030f080405011503030f0f021b060c120d02040f1e03140c1806130209090402040902060c0f0d110c1e031f0507020106081908070c0305030c010b 69
    0x1000d90051050766140d030740c5519100c0d9403440301300c004d030b404207401402250950f487e655204400b201d0602c86500840c801d813201460030b8410361b8058010800311001b0b03011075100400c00e0803a05580399000c2d0000c541540c070140e03103040c400c200031304005280030010b030b1149000171403404c03031003041d8014001c440c8003603003d480c0c054841500b14540d2060384014400341b00000c40c00c3c8045021000d162050b070032503400b102c0c0840486e001080100510300100241060090104940e90801c034440d4010050641030851811036107200140d01940042c00c06030080e5074441c0c1d064115121001104d441d8080302080320f2800315480005551148008091130001c0d44240811004d564001010508408010034103418481d0030700342080c6c079400300d00009905104101c51101072583c0e2200e8050900c409080108183c074203281c0217400c0d614164401200c6502000044c0c4081d1000c0b40c0e07840b44154400c01156980019050401401d03215800250132800005440c1d03414070015440b2a0104038240d4603982c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 353699622 1250 353698372 353698381
    0xf020f07151506120203150d0b06030c0f01080c0c0109201302090f040e1608070e060a0f0905040501020f0309030304030314400302070305120f070f0201230d05 70
    0x10b00c89851031255902007a0b96404600741102e040c0c0140d980220440ba100c1c003110901c500261000000000a0355852000418040581014000c1e40314200054480441c0d01c040b68000034035107071004140c01203034400415036480701c10080d0003c050140e003110f030701102c086582081030700100414607054883c0070301c0e40c90f8030000d0303501e2b00039035044103002131081000082050a00003c1c010000c030402c0d2500403c0c208040240108807403502400b1814001c01003a0f04042c6002a9070b47c014005a1007030840c12020000b0385240320034003007940e40401c80441d2a840f58517040c0e0281c064286502c008400c08000c00c43d6010001000d14480d901035030f000c3c00210001c400e1103420031000d490b01c2e40c01440300740c450b51401541c481340c60009130088407184e03c480c0300c40d0030130034448110031421001600440d00402c140003041202c0d007045103820320780b185002c0d0403055210151007640c2c4001c1030008003850721025680039802492070010115517100340803030b001149850b96400b51850461892070080400c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 353700872 1250 353699622 353699651
    0xd050106030c0c0204021303021f03060503030c1c02030c060106080702010c1e1d03060c0702090a02280521010f0608040f060902150c01050f130b0402040f020f0715 72
    0xb105201443c1c4961080300307110b400b44000703540304e0031010070540c10700e000000c0140c0b02c10760070041855908242c001154000ca5008041c0e50203640250f11a600c01e21802d62020300c0801d0a807540110400d28450700315a80c1410307420b40c000d03a0038080e041c0c015140006001c64201020380d103c1c644560007000003001d10a000d40d8020418000c50031095410381414400d80c3c040c0d0040140ca80c2c0c50007a41500205910021f8038002c01110781e03081e840da0116a02003103081002c04030360050340d084015800d14441c0e1801c908510909441d0568088650441703400032402182140c070746105d461020580c0d00d100c6080703000181c1c800c0c81045158803000c0300000700b45104440840c06650302c10646041c0c0c042c187c0300c00700a000702c1c000590f4460000c03580d01c4100502140100841d0007410008141494122103c41144100414100183c4241001a070000d240340e05003c2c0d120383e040b540061010380d000305d40d80081c040c3d4a618880d807000001e1100038008540121010070540c5030301405200071011340c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 353702122 1250 353700872 353700881
    0x915010c1b1401020a120e240414121b040b04050a05161d060c070f03050601030c0f030b0712020c01110c2103010312020a0204020d05091b01020d05070203011b050d05010603 76
    0x2d08041400c807203030190184a040c2690001600401c00070001e031044d91095903800d00c440c507440da042e500140c10442240a070441504c603107403c44d4410bc0310000c524695846084a2000041445c411000e071a02641c581c0d00c5801d0042e8050020005803814401d00e038010072060f2500c0032000303411801c800705184180d031868185440130400900190b50f04041c00000c1d00850401d2049014104000c01c050010554000080d0300580046c02c45502d182040c0c0360440032074000d20060003148174103001107008420300e180c002d00340b4905410500d030000c2c4010002e010b030b29062900e550800049241c80c000c00b101600903095a41d080c2d840d68401c3d00100391100b0004808040e10340010701c01040444c50807030800d11a0030b801d00658407100459030012b0200d03406140e010b01c240384d4540c00c0c040c0707480c020801c44c011025104400c0b000171380740b500040e41c0c5d0446034040703c040141c00520182191000c0d0031007031143c07480140c1160302c00c210381000342c40c1d5001401e281c8010f42c50f0030f00001e070700e600c00d005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 353703372 1250 353702122 353702143
    0x30210030e2a12060c040302010e122509140c03040212030a03060513020a0219030309050303100611011a0d0c0509010e04121701050d06140108100b09060915010c1b140102 75
    0x8555141c13607d968019191103107560445688054034942070303046840706100740d000768052a1111002e04281c0c40628807104515044501c01d10728252151740310340b190481154000e2040c0103071035104c0d951403001130400c031307007030b41c1d51005e6070002140100c04542c054112a0994508950341d004014803647c054089006071101303003006a006d41443e642031f404407044240c0c110302a250126800e45191900ca16651080c4c41207080844044c41c100680c40c0d02c040c01130300746035981c0000d22855070306c14070500441e2102c0d039015204104c9019480c042100c0d0044c8040103083c0601200540e69550454041c46081100d040e100003030710a0304082514441c1d07082c2c0305440707402c400600700e0b6401c001c14401e5001681200720f41a039541c41030748024820306080301d40208903c1380103003010b43c6c41400000603540c4810381a40191104014000e00c0c1c0d4940314055480303c6500c0c0c0c2184c1250a075001241c2c500034800c0e01602d40014042d0103203035003403001c1c041e4094603240c450100e0844201c6004a80c0c0307440941 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 353704622 1250 353703372 353703391
    0xd051606030912050c150106080402010e0303071a0c09040603050106050a05090c0d0c030209030a0b101706040602072609040501060923010207180212010b04030210030e2a1206 77
    0x155014503860080025040c11009117040324015100890b088031140c1e02a000a40403941a008200440d84e00052064200c44140d018604042c025a524040c02038031702c2101742503071440000a0000c882820a403502c403e4014414410b103030341c0c0c0c10301d80c4c028603840c09414064904100c0c0030a2a0604903001d6000751000b16074140f8048281203010000e080c041c2c01c01c4201a002c1110124690702005083c3d9000d010b01c0441226080440c2c083c800c100c484d501c030041281c0308102c120741e205d00200d01c89610642082c400b5036100f440c0d00e008004405d030f80301b0040510a801d02140c1100c140301f006007441c544251000c10043c3d0302d0b407405546121580c410381182d01c4000c0c01c44015510720040d41c4400c0c039018012180c1c1c0a450f00134410b9110340d5030541083c01540454000c801280c192290781c0100810507500b45864115000310780324401d07065080007030685900034554901010001c6c00c80c01480300e10301060003985940241da40341c0c00118802d00c55905d20300302d510820f4021580602402082 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 353705872 1250 353704622 353704643
    0x190c050a0503060d06060303021b0108070f1b060e030711180406180c090b0301150e06060a1b030c0b07140d0b1f0804051b03031213020d0516060309 65
    0x11046903140d10007415641c0010b250010b1100041c046d0140f1030240d403098000c4d21104101c1504c01da00d802d07418006c941040200000e00c1300303194109400c440c2300b01c1e041c6000c0040754161900c8515840c07641070018825441c00318140c402803c04000f400d40c05e44201c41d00d0051045000030018018151441d20030050f41c108003003000550103602c8440103002456290850b100c2d80d031074500c003181541d404000c040d03807103074680a007610b02845800740d8150115404003025080c9002c0003450072008181130b0080c2c500182c0d42d40c143d401141c0c400010b98621200074080d2030703a450001c250300070100c0c049841d092500d0110b10b05074003030b00c4111407002440c40214180000510144013406540c4100e2303030414960000220161103501801480c50740300e0f00c0c0c2e2000c41c10325250181c82c080a0b01c80034150041107a22051040c0c0d8044221200074022810449064441c0d8491010b40407080200a60110048602504020010a405198110080440d20340ca5556101a8144d4222001c000c000d008034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 353707122 1250 353705872 353705887
    0xe0304060806040f0f0b0a0b031611160b120903030603061902160c1a120604090c0b0a0314130201020a02060f0918040b070f0c0b090c0303070308190c05 67
    0x710303040303503100000a0020442c1001c10b49200c048030895001c1c4d441d03094440360070318040d04010b04400700814481e1344013440c40c60045103c3c03c1c82003080c0c0b020f40800c1140c80100c2c24030380c001c200d00c4c90b108601009400009075220107815841e403180b941041020801c00008140c50703804800e582c07080c840074000c2c14496446400154903481001c0a00c10066130074002840ca280084480d40074223840342018001c114240100000c8001300c0001d00942c4110070071600300482c82c02481590030a50554021480a000745005244422160850b525000c40401d800504580c140c1110100402c1c43c01030818a8640c00b20000369156a0740010780580d0041003090018204100141004040882d5050a102c900f1002401ca503540004048141d45403030180400e00c00c01000c070030f4201c3c101d4201154030440d40c66024040c40408100585807a83c1d0200103588074000344500918203c0003802c0d207584e00168540909a4041510180403c041403510351078201d07060b108484110b899900c0e040d007049a07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 353708372 1250 353707122 353707127
    0x20f06030f04051501030f170d1e0609181b05040507020604020f0301050601020718110a110d020604020a18060911120105060403021f26150910050103020703050702030607080412030e030406 83
    0x100c008080c14403403040103a0706811480388550050170031400cad1610044c4003a000c000041e0340507a0080325080307140c1010700d4180654500510341d90b540c412410050000075400e1780301001810780c02590424100801c0100150340401c0c92886184200c402031001148902850300322070301181c2c0540543d000b44014040600c7c0c00e0302c42c2c1c0c1c010b0020400410056400402c03503079107410100203940840ca00f9400e03162540418400740302820b10341d100a01c40d600d03241e00002c041584520071240d0300ba00303512450481c820942c00010140030399030f03001c1c46140f451304543c00859000419080f004410440085414507000c002c0f103007200d8000b00340c5110710000e80489400c24912680074002e00129144120703140940000000010990809860071441c221841d049881078481629104010040410281074000440d040940d6000e280040c1c9070803042c9016a02841640000303581340c81130000f045507242d0300030f003074601c2503219419030119103185031801d07001c0e103120320f100d10040e8209203c20b00400e032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 353709622 1250 353708372 353708393
    0x1050310020903100c020d0908030307050a030207050a02041e0605060f030a0506011e0201020426071403120301290f031f1d060f0307030309030f020f06030f04051501030f 75
    0x94005069500c0c40c03011000346421218100340317280140c2c0040307001851403078000c2200e500030031100740550f1441c6044540103002d4400c08a86c0d0040c180d01103152000d10904001e50500d01d42d0180c400c00c6401303503a40111070840855540740c61418100003001c2103d04019081d201400d011400c568119201c0c800e03014050400100f41c00c0c104000350f01c1c54000c08803c1e03900c058090f01c403a000141e9032410002402521554000c045400c14034401001842d8803001503405c040f00c46a100c80507280c504000001d08004102d0071007141010040008209401e8420008100c3c0c06401101c1c070072a000080700810601a095181c01412424800070308103002100b03892001d11032401405401c03e0b291028900903002c1f01c46800ca0704082c600c1001280e0901d0322000580c1d2608500078031080389581d90080443c0c0075800014141008010f0101c11503c9802032040221070081a451b180d2810240d407441c8030b070003124281d0b240d00c24050b00800c1c0100304141c0380e041c0ca80000e040400250f041c1c540d4401d03030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 353710872 1250 353709622 353709637
    0x6010302040f02130902070b160e0114160501240506031303030f18050f1903050c031b160b12010e07140406030e0c092e090f0f0e060105031002 63
    0x583e02001308481e41100c0543c5100588041480181c40e0300711070420b03041c1107600038841500c943c444030040c0c003001d4002d0b100c10044502468480600e490804e40040701e402007192601c0000d05c0d0a1840e0100081034104054105111400c00c207040c010004c1c201c0400e40600c20b09400c1103080000c2546e003100f02640c40350050080c2404210b10038134141c0e1004031411044501a00500c0070128020000c0a01a24903810070700001402d50320038140c00f0b1191450703190705c01810b0000002d4a150701a0080c42690022036410107400841010300c2d0ba0303191665042c80203191010302e04100840e803410700c10103840c003508028001261907803c00c140715030380c1c1e00c020b03021000b07000c2140850404490024000c00180c0065600414071060024410b45880d141e92200f0307105100d40c1c0104182c480c1c00c030b80d1381c090901403180b0340600300c107511444401c00720390707500620345240c10003045490718581508209600c1040310380c208030400c034036a40340ea01c1d00001c4c0a00390340354000c11030005001c0c400f81c020b80101c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 353712122 1250 353710872 353710901
    0x30405090f1312050f0f030a0c030c0e0f12060a020c1c0f0807030f05091006050607080d110c01050c130909020906040203150306040c1d0114010503040c03050303130c05010207080601030204 83
    0x2029150082c1e042d840d041b034511413912600000402207103441c10300446860081c103080610250f42d80100140241040740500c0340903000222840c2d015a8072040440440d0043c01c0a0700c0e400d0800e21500c1000c1d50060500350100d2140100341c62260280300141e1102100d542d0f61440d5440440700d003258a15405001c020425480d0010048d41d00918413416025a0701c0320001e0000040c180710f1070055580035408140f1484c010712002000c10581d8040301c81c9100c0c01e100000301c001c280c281ca00742900980700385103119807030032003040f0038550180001c2c1524140c00584074039039640d0b50001c40070703580c400d60000e40007812800032445c07034100303078000d0340d04019101d446510201c042c6000c02c0c0307400c80c202d03419a4000c40c000410406640c1c10f9a4100d490005420b5590041d0f04000902d510b1201c01040c460421000000140c00e0003058022a0007656100083d290381e420055500c1c40c05c600501c009039016070001c40c0008981d0700000e0361508842112014040d9031703281d602000001e02c02c10081110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 353713372 1250 353712122 353712127
    0x405120714030a02010b1905010e0609010c050d0c051216060b011b03080a05010603140103080c031b01140a0e0c0402090d020a0e0103060b0a050d110d0c0602030405090f131205 77
    0x1078800d000c0c0050020b5100384d13400005c51102d40b40801c451200041a584000103502c81e060145907800485000f1500b003d4400c079a0f01c161840040f508594210300142050003600c42450f02c1a40c0410b8018441d07004d20101c5900300d0241920111502c200600858250131030100c05000988942005c001400141049066420740440b00a41c1107030b8902d003200024140c00030001c41d0251445028003514151034104425201da042006c00d0507010b02001e00341a00102d00f800f00c54400700129170010247d250b484050701200701e00140a4075500c030078949604048000149138218030b1041c03c5001c84d001d002803400e118424240002944594080b0750030035101001100580c1721480141e0003001802c80c1031540e9859801d100040399100f0310710b030384200c80d41c1204120f280c0d2040000302a02d5045490b18285c80c80f4440001d6015440b101c00515140034040c000034400d03004005041110010b4803c85c3c00ca40d0340100800c5444003c9504040418000c1e0881c40850a10000407800a416042861 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 353714622 1250 353713372 353713403
    0x5010b220e0108160f030c1208040b04150f0804020f0132030106020708010204080303150d0c03030e36061504080d12140103061503020604030f050c030604051207 71
    0x2035900243c002c2261940708490060300042d20803031200c0104881039450300540c0c11655000328840040c4251340c0c41440190201051000704c2085800511131201042c0d503a60b03840b1599a004004407203001e000c04d41240e80741c1c6030390780580f01141c030131a8000e10080c0e4140a0ba00195081542000007101800c10864040031280c00d04c82744071190152417020944030b47c0f500400902c3c1051301c0d004259140d0043c0401c100e20707000001640d03000f0b0160303080c040342d4807815004901c810610340400350803040d00140c000245900582d440001020075280b02240341c17186490a0480d403801000e82c0600250301d44040f0807510340c103401c5900103000030102c45021070305221040460b00107802c110100d030840741410114070380040c0c0c3c00722465079101060001c5110410741c4240a0014400540201d40792600e01e40480207030030b640380186070b0042032035403199103071304003148125498030046030a8418072003103080c035240c00240305100f07660140040c00003440118034481d09400201049401504600b0b00e40c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 353715872 1250 353714622 353714639
    0x7030204120b04020a080d0206070302090d0f0b01030b0c0c0c060702012114010e0708060d15020c060f010509062202090d0f05070e15011d0d0317010905010b22 70
    0x8070622801075940c45580e0a090040102036001076025000c2540030303140060a1540103c0d10a51181c001c1c24010380b103405120200d00080400c00d4010031b4020000c0a11003000307039508025060301d02a030307035a4a569560b19242000352003106548078090340548030160441c030f0803800500c10340b44107140c02001c0a030360001032280c071050b5066039410a030710750220600c0300d024404010b00410042107006064180344901170480b50000d0022406041d030050544140039032081d81c0403400410754400c55642007001c5e0029111b280543d003c86e0b04801100000805150100140380103a2000f8003540400d5403017842c0a4200c2031400b00704010b55020700040881d035440d02e901140c040d0003089a4540e50301d0301e02c2c0c031a0805006801400801201e00c042c030400c40c1d012420f000c40c29a080c01d00e0018008010134004403603c1030700e1511b0744481241d060710205076200030754a4550b0360700a40b00000780d0b04c0e26041e2040c4c80c824040c0e0f02ea94141440300d2450400b002c4004002d0903000200b0210842d11070890 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 353717122 1250 353715872 353715899
    0x60301110f07030f030506060d0c09080607020f010e0a170703210b040f060609140105130906050102100c0c030c110d06020c1e0a02011107090207030c0b01060302120103020907030204 80
    0x1804801c40d008610302081c19007000000038034829519042265182400004040340211740240c10040c1d42c405103910385c4c81c000d08418001e440701d10b007180c13000d01e02000000c0da1500d100340302320140c2d42000b803c4a2940c0000503064401a80000a607240017000a1140007640100005030100b01d000c0071080c00b100211008529000005807000c0380880310300b0103220544119040052a0b1403034404100311403a44030007020250f0355540140340b43c412001d40100c1e4140600005030a40081104c40000c8040c1568411006c545003a0250f42140030358800b420700301ca00c8510b01401191f090072102000a01c80e4aa8000c85441640c01c904003484107404503e4102e0301a8080b1007582e40003032000d210441c1004580d290340d0344620403040d00f0240b003814503120b404600c0300a050003007121208405001c00e008540240c980d0440c2191280034174100103181060880382515030350480d100105029100c1c0c0210343e1015842c0036801e03900e0f440c1d5800d00820303010040c003610400d5800d010200d10507800548 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 353718372 1250 353717122 353717137
    0xa030c170703080c030405040605010c0b071412100e070c0b0c0f0d150f050a06120c030237080906040f050708010213080601080f1009050a0b1f0b0a050409020306030111 74
    0x11740d107403030070710052204481d07003a00030700d0500141c480c15000003400a281c080d031000d15840c02a4002d042e29802103054001c005002c145000c031401040400a10203110804407503030800440181e489411050b6018004c82d007000e07204244240c00903070f65032070800084c80c2040136201031902d025605907000c0c0403148603017420402116545002c01442c0d0780703500d0310006800c00700d4049400c80c1c0703072003c05031400e400110341501c0c80e5101d0100080c254081d0341540d034419820000f00c8021007403a00880c0e009210058150807410124040c4000300e03110707800403841911907a00602c0942c542d40c5a0700114402030070225028462080c002c100207100b030025141000018844030461400c0c0000d450a180050304108110341c0100c0340c80703020310760024013507035501150100080c0142c001d04040307041c00381c4240c002e400d180c0c465050003044d501012100d1900303400215910291601c400410b141403007540e90990003d8000d100902c05200240d00070b40c6c02100c0100000340c074a150b06121f40c10745d008281d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 353719622 1250 353718372 353718397
    0x70e0c0409050a05100906050102150c0c01050705031915051c060606030e1516081008030a0f020f0c01080105270411101403160c0203100203150a030c17070308 70
    0x41400075898081704e4041c00340440101c01d000701420f01c40000d51701c07000000f54014036603060300458140d0301580100d8030b0190b0504001e00107483c200c4e9010381964002c0c1c0e100f42d00c9400342d02e446416070400b03201e8014903450781c40060314140e19040030090f444014000c40030490f0b8002d4400030004801d0f11441c0c0003801c0584012401c960395280c06800c5c00b40e841b401051b078030600c00411a02500403040218440701c203081640603500e5040034010700030f8058010707a095100004d105c144c00c1d80c101c1e040f1000c48d501603003201c11880340e0f07403052601d48840040041c0841d1482d00140840e2410f01d8101100b003d100d446103040d0421164140031909082c3c0341610b01407182d02603410b0606100c3c441c1881c001681c200003c40c5107482d0b110401074440203100100e01125903ca180c41180314045901c06030303400800315540010541ca06400a500a480a00400c071599038840300c0740c1850460002100d8000030070401c11854101c0c01c0400b416100c0fa85103c5000b038410200015003420041c2c80c1140410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 353720872 1250 353719622 353719631
    0x1b150114010f03050408030604020f16030930060b0420130e090a060c050705010c200c0d020409020a0506040303170a02030412300509010c050903070e0c0409050a 71
    0x20001d4a00c2142542d10740c10907003031608000c0420711900440c0d400800aa4005945a03074200b0301140c54004c2ea0a110032400c0c3c200e0984060592200182090719444200034207022405c815440e4491481d8051540c17840c0d2044035440440c0c250f5000115080c4e0242011030380d107042c5103503c0c42038514038240a002241c0818030340348009122790010b0140511030f54074403107401c1400c0166a01d0000384001000e442d1101c5040e51501d01c100c0558803000d07408802400895150703031002c0c0a03404a014820b464100f0440e0401d50780c0b03400644103540b690068030b00d0001a00d5078003800060b2003400382c1660041d1145c440010b440c0c90b640001c0004601076518040010038041c082040c030034014004841e0b00b801482400082607030800c03524113007262800c0000120b0240807182000c07010f0a51130300c0d500d01006241d14283d000c290000c5101e0f50540008100c011107603030055659001c4c00d95000c1e00f42d440006d0500030921030f0400d07141c111100581300d03801e081e99541c4030f20980700100c81180699844 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 353722122 1250 353720872 353720909
    0x10e0d080712050a02120a02121602040f061202041802120d03051014010507050c03010203012303070e2a0307094e05010f02130603020306061b1501 65
    0xb812034500c4000b1443c81c01e98a00307042d0b01d20095560f0326400d0080b001020016400b62028020017541050440c0000040d803104415081c000c0d4207203a03850140e0090342044611012410103220f2401507501c0703840c00808041054003840010013151100303004400c8501800005a9030b6a442e03403c070024000002c092282c0c0301c010040c15100060040420300240f0744061001e607110307924032660707040c0078603020b5140da070705007003640c540100d5000c16a0194400800880d8032400302e4440c5204007802071034941d244190b84140f658403140c0d440b0312410070b00f049011452401c10896404d5050341002201d090340009011240e0460707100340c69079000325840a030100302400078100c0340810340c00c0c00d800303aa41c034542803034081240301481c0006803400c8418040e0054030341030300740000400a4200e002004000c0034111414000d40c41103242e101d0685410310005141403007402280d101d84009403000782094082c01e1945540c00c0b04000442c0240136103000e82040045020555000300300609180001020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 353723372 1250 353722122 353722133
    0x20703051903140f120901090b0f100f0509041b180603110915091b03040b040606212006120f0114090609100302030f0105060118080604020f010e0d0807 67
    0x401c108031004002d101e804503246841080e2612103807043c5c40142c2c6070341c5140055004002003007004001103141024014820400c464140c4516250000d0001268480c0300510101c9083c2c031807a076102c4070300b00000f40090034084100b0950585201003542180e20b6440c1c060042c0340806034141a00c4d5125410010300c100d02145041000d01a2101d080604000c0703c0080f8109074003007030601401c0d50078045611522451804111069105003680d100d040c18903022407000c8007940d064503403038182003000c9a03d03012001654a0494092544401c22a542d6503407209000c040352f185081e8031825800b602c40d0303214040102400c2d03015000c0c41072103141088140b1400e00d8185c03c0110054090f140704103241c1c64041d401c0390484800c0719000d96943e03548030300c02e180044541000350140200d01c84d01484040541225010f002d098a45d00b0207180d50405080c220041403040250076032181740441c01504082500740c01040041c54001c81c1d00c5550f00c0030900022220300708844031100064032030140300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 353724622 1250 353723372 353723387
    0x3080a02030903011b1b1e03030f1d030d111306211a060702040b030a03090303030b0d210c120e010212030f01061d1e0102062a070201020703051903 65
    0xf0501e00041ca45c500031000007000c074a46c66030005001c2c1c07145480b1500b800102c1e450003081100148410380e103d6454500100a01542880c0c0c20350716081c9010103d141014400c84c00304007061800850802d500041d601e00502040c0702540c076007070410003c0c8c801d082c4d1803041c5103018201589901c844088841c07059541d100e2141a04d030021807400070882c00304c070003401141440350740484185ea251451400054000e11031a10301503170500ca203d007000101900228104106c84c0213403802c005102e100b0007848044480010010003541030000c40820140610741e88108210349d900d00b05101400707656031940c00c2e48602c4140d6000c2020b00703000c03c400c9e41c0d04100e1420125048de03011411170800b0450011040c5041c0904000c2c0041101d9040c00401c081700946c0d4442c000400300340c6500694a00c01a00051210016006005680010780744400550a400c03480d1030002500f4552202c50b600040c47c2e0300105000c1703045024810000003c141c04000f540c0b180200760310300310021003441c60081c0204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 353725872 1250 353724622 353724641
    0x309190f0f2411041a0d0207030c120206010501020c0607060b0d0803180307020607060905031201030c050103060915060f09030602280f05030a0f020408061501080601020c091603020403080a0203090301 88
    0x83c20456031040c0c01280205403021903600c0315020181207001c5c0310200103806030080700449984040b62410030301d50b10102e0032503214018000c201911842480481e1150024000d4a000d0b900c100070040711414180c0c01048100d00030640082c0e884000360008111405504040e940f8407400f2040c001d0112080346040104c10b2180d000312710303104059012400e68090000085d0145903030f04100c10502c14140116040044032041e032303040c07030340c1c40e403408204003009402a280045e140444c0481c00c560644038144800115482114000c1d290940494403142070307894610412001c04000000a00c150000d0882c6030004400803241107540301c0306052503442c1a80e5401000351088035014215080002c0303d401c00c45c04200440c00c041422002c50181c411540a61580c0c8110300c10010076580003030b020540c20800741d80d81c0c200c80c0c8504d0012030761820340090040e800740d04100030801c84d1040c0144015016142c0c1005814180d90b600e50141981140740c9100146e000010020010b140038030566008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 353727122 1250 353725872 353725943
    0x20f0d091208120c0c190b0402131b09140d02060703230403110f09060604050607050c04021303050d030c0e0121020408100509030309190f0f 62
    0x501444010040030300c811842441d84102a81601d2814440504125000c003103088003071820724200010200602c0d805546058840c2c0541c4066603203515006600ba100c80e900302800100700e440c1e68080280c8018000700580b07a0558410045000301c0c600000c11030043c0b0a600c0c2c41ca031140c94a800b083e0500444020355104590310364507000141d580b8030650341600e4051401d008580080720b22020000650f41304940c00000c00f081c0001040028008500008001d90707200c2c80740500d08040c0800114182c030703200ea004100388401d00690401c10040c02c1118000c1084a000d028000080b43c101d9028000d25108241e03001400c1c41401410080d000c009080d514040280c000841801000d0118480c1020b0400155060b000590400860301305d800400d8000110358444d80c83c00c90603584c05907405d00b0184141048006540d00f103000c8241c0b0700c14680710001c0e101481086000d06030071000c04100312018184c403070800000ca1032144181ca0000d110b100204841050b0300d00b486500c00d0466103e010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 353728372 1250 353727122 353727133
    0x1906060e040803070507260403050c04051b090613030605040201110a0309090b0f09010902030105041812080714030a050a050c0a0f12020705010f09140d05040b030a0902030a03030b01020f 82
    0x80d01c20b50807254030042a1910a444a55a1910520305842d50190300c01c1e8501c80014070558000c2c000c0103208031381c401e01c00c503403400030325209110030b84ac022952401269a50340481c3c500d60700305002001c49103001400c483c40c01021040e03aa00803500340c1c105644190b5203900300021560060400fa6200200500800702c903511558000c20100d054007543d48441e03150490311401e034907004d00c81c18100b4001814080a9030310340003400f000b900244203c1d031040707003064007800040407101003406406400200707120b00404c46038025074420501a0848003088400d484001101d0b002801840c02050301c00b40c04030f40e60520408840550b0300107048100009010002c100c6250b81044a80c8500e86031820800001d1210300100300003805000c80142c000c4d424190f81e0444100158480c0740800d00ca2840a05182100e644080c0e48030795907400f000200720304020500075000da4070040c50340540c0402011a044002e6800710b17042c4412540202e0100b512000d00350220340c0c0620800001d20141c60040c078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 353729622 1250 353728372 353728381
    0x13080d0215010e06190302060c100501140306011401050c0f011b05040531020c071d01060210020f040902120703060b0a020a0f0c03020a060f02070e060901031e02031906060e 76
    0x403003004018085a2017030b81052000c0401c00c284125001c01036400605460b03c07030268122054450708043c4010268925000001c03803eaa45040800e01842014004015030307800c2044582c44079a01848503410310005000c0500442c00400074662400f600c075002140403420007040c95041101d828100c01806410312040c0b0240d15458030303c2d0f00350b807010300d1100d00c0000c00000c3e00d40a18030085c1550300950001078010500f400001d6080129541076001c02d071402019220303840c41913002c1c050300d00181c00010022184080d290041c151030b00610310f0071403405603203d5002049a002c040b50903e021a10000c12020729003500c02c800c0145200d410451800c428131760002c1d00e0307507601e0100820180e00b0304031007414400e500750407102660740901590f45242e107411000e8002540401c80708014441c420004c203000c3c455008450040c100580214130607401d40e910b002c18403406280c40c0c00f100f0860500400540d0701000300320300300c0f02007401e079240c800e160b0708220058425a81000c154448a5400d01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 353730872 1250 353729622 353729639
    0x50307051f18260303090c010c0302160303080f0711060619030c060206180705030d0e2707020c030105090c010c02030a0b0702100b0103090c06120213080d021501 71
    0x18280c000540882070150290042580c007a14800030b8141504030700c03540400c680303141000f410192020b03a501640490708015105035648021202d1400c85c0c0c02070320603200e40d54007408403c20600e100340181c840f4448161140b92400a03250b0040d00050f08140600401d081d913210031680188082c9040300e080340f0b500380c070a42e440308041d0100b03020701910903002228032003988181c0302640d030000352549007542e00c0d64000d5441d1800d0394061200c800222f00b40c10400c0700001c6160071030b0400740183c03000341c2c801082a00c0c0007510b0801c068014044000d00d808458900303142205840070340e401c6034070710300b81210000d142c8011001518000c1e0315060501c0030071078001948903c1c040c000d20b84801001c200d40b0109003000d05118004090a1003c0c0600528903008550005460b070312072410011030f0b40305401107056681610002d0081181c0890600c0744512448003946680d442d6107015160030005514100f9020b1160300900860b041b1034254901180c0c184900100c5003a03245100c200355040984c10b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 353732122 1250 353730872 353730889
    0xa0f032406110304170c0306070c0507030312020c01050711060903130b07030905061801300f0b0a140901080102190e030c100302070b0105060a0e0d0f1407060905030705 74
    0x200c01c01d104440c90022015401003040754090018a010005540740c0c0d009110faa401c4c00458540c440d018034400600c9192140e00940050380e08000241070003071554805643c04401280d9568a490b000c0100f584400824042d083c09440d05546501c8040c0c0d411280341e080ca88007510359120b5400800035404e40740c1d450103100d02070710a540901640d079103903481c09031010050366124641041b40801c01403070f001c41c111403400c3d01c42801e032070b440c03d95003030746090111660007019032800941040303801607a80111035110343d2110494240002e80d20700c480b4005807080c5965405400560314811460081e401c4c0000c10038014010780d4000c0d4281501c0090341414031140b40c40ca441049032010080465540810042c0030306200a80319012075014050018060740c000402078070030201c0c580001a280c10284200c40440c0040c3c1c1c0d8a030424105001003100c0c001e2443c406440d9001840511804614451030064076490641c3c001d1440901c2e041c0b0240c411041030384031501c25000443c04011a8039078802 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 353733372 1250 353732122 353732129
    0xa0605060f0d061d01060b0a0908031603081513020c0c0409020d020904151b020c0909100f0605031e0f0d020606040c020102162003011104120206040b0a0f0324 70
    0x2004c900800300105014011905a003568003075800d00f0740001e4000030701d0000303007200a145d598501c00d440d100c1e100c1c941e0700d03c5600110a000d05800f074240c00403a1044481c180c02004008440180090b402c0014003d02160100021100d500103030034019608200020085840d06440a20092000350001a41c100340f404000e03000750700001c0042e040000e8282240d0b204007020a08102c8454441c0690020010394801d100141c0b013060300519042c40d020441c9481880110010315030300d030395888200c003e00764110740b000d201511000701081ca40d50521011070a5040f0010945008100c01d58281c0b900d8900400d80d20181c018400441100d980422126480034055030049103c42c2d000008070300902c1810005504885c0102c3c4403010885117803800c60000c02d100240c411038001c40020142218060241400400000c000401c403840303407003c0d840c0c0c045000802c0a8207040d035070340303408555070702400754100003074107003500c0784509609031050844842202d000318003030300051460950041036501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 353734622 1250 353733372 353733383
    0xb060c0f25030c0603020f2203020108011e0b090a0503030d090b10240c02040e06011701020a0507020f18040309090513201f03140a05220302100204080a0605060f0d 72
    0x340150401f1fa00400700d41d4840401311800c08000d203000a10141c4c010a40000c9001600032000024890100d400f0b40010203040d0500c1c441403443c04020001c039074000c00005400000103e00025030760780c00d01c0a0405410001808039004045151520714610014041e6150081503601480400b070700030690002c081c00c0c5030542890300c4100e581503810b01880f80c1c000b9481820621010380c2401c010521504035004201000c8160400c01882820f030300604903031400140c0c0c2030010501601d0f11400207562a003010f4400e10301d4403100b0b5500080c6901c1220103401185942d07500700603c003210300c5001d034841030385074408860600a60307511001010510132060414074090114621b6030b95048804c450104446200320030901a10001c1d010303018103d07400304600e400f1000280020907034043c00340f09d45040006803080d428441800d4003120501c010907070442c8206100d407014410544002d00240200b1802050245e13400e107841e03801d6490007402c02d40900030f0b000e054503981d03c41d507139102580d03035200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 353735872 1250 353734622 353734627
    0x1407030b0103060306020301090e0f0303060325260d05091003050a15080a0309090627021303030309120c081605010f021b0d050a020307060b060c0f25030c060302 71
    0x45004078083d2a440e003018003018400400001c083c1d000e03501c20300190b006441a9100001000f0681ba26030104451280e00754112246c0b29210b038807600c8ca1070910750752030942000394030340700ca500c01c490303442d02c0b0b15000c030080c80c110b64118103200400900e0307030750200d0b454142d2420002c000450f4807244003500e0141803544400116200d00080c1e0009064070900d075421202140e5540c0c82e82d40c1e640f02e12a020b0340031944208020411400c64007a01050304c50400c0440d00440c00e0f01d5075041c45031151403661a40380e90a06c44001c4101c010300b0000e00850103581d000c101d00d80c0c00c1c107222201c0ca076400f402c0c00600684049090006001d2020350707804280320702420002e142e0505149014281c0c00d84400046440080d0b5030004018a0030b00548425111040f5540d140b400781c0192001d00c00c5a62500260348240501000119282c0010500d810042c0031075090100341c143c06454101d9a50300c8004a0704003501680780c03843e1141859442c1c4900c00403000a0916548600301d01d01c1d00d0f80500020140c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 353737122 1250 353735872 353735891
    0x9060216080c0d0f061e0b09010803030105010809031308030a030c020607020705060903070914180a0312180803190b060403081204080f0c070504050a0209010509040c0e0d0b0105090901140703 84
    0x503980d82c0a003868010305e01b0f2058098086851003040101202c01d2046440c000514803942001c00b40541078403100320081d803840c1d09000c0103503000c900003042d0344190311081003140c2005e050a41041c0081c001c0310000c2d61030b0160b245001c0e0a580500007101c0844d803011013005007259000580c0c0040740c605031030031903803030008101003401c02c021038006c520400e0070542c5800c5d09a0a03e000144200e0801e0090031035040384034440c6490310821800500021114041c06108112562203810140036400042024001c2a5291807081d041103070030800300403900041d5403041e085c1d03000e0700081080841c2c8071403038141503507103203d05401858104042c00d054180014100f044040c00c403030500c1603818002d900c81c1d20072001d107603480515018030340c01036060602003070104601c2e00a0762080c1105840f041c2c18680010f040c40020f0002c644060f04002d035803040d510840d210458005002c5000b06041c03c1e040d0304000900010100252490005030304d00502004010551000560401c0340d03440c012840200c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 353738372 1250 353737122 353737133
    0x1c030e010c020c03010605010908150a0b0901090203070216123c1407180209032a03161a030c090402041d060a03081803030706060609060216080c0d 65
    0x100408256250301c0e00303082074942500040c9482c0100700860080c4034480c2c90b400110751101c0c051152072007561085070100080720320144e42030f42c003415149002402d0038680c400280f950030280e12241200d075000041c481c40c684c4c1488006010220b5000419500b480c003800c81c40003004800c0b010f0561404810710495040d001070348902654951000305d110503110341c03182c0c0e800c045124011562501c0d80e1640766041c110100301c4c14221441002a0b804804100081c0c1010f035003d60310031036150107650100f14080900480383c04000d403c0110140203445a41c042c5031500506604a104510f03070500c1c1040655442c0f410604900e00842c03480d0b44a0312040c001480c41d026103000294400e00204001c500000005140030002400242d0303044035460745418404016003030b00018089000400210303d0400840e1a180c850801c0502124a805965102c4c50121102a08500b000807100201082a6a410818100c5414459003180c0b111071501070020b03914050b9880840c042c10500403254203002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 353739622 1250 353738372 353738381
    0xc0819020d0615080a0c0e21012a0915030b03071508040b07050702030a02040b0d0209090a14030c07030303051b0c0715140301050409141f0f020c1c03 66
    0x3541c12052084a80300c00003030020020700129000002e6869001444580103800760b51020b811036100c61504040f1700040c05088006c50ba00d819407080b598800401600d002d202c0d403616202e40c440b04140b80c0e684215000c42e041c4100040310708000400c0c0050000c103800c007000344400310841c10009940f0741350a022174202401503001155840c4880180501c1c1504410010300c20b41c031841c051a41d507940c1070700c1503071240103540011750135a00100302c0900504095001031454030000304405001002c690002d0880c00040780c248410380c015a407400c003002100220300e182419108080c605164942c0c1501c6d41d5a42144800b404268644003c81d1025080241c200e0710b280c07022048594400382e02900a42c0c3d03900c544104904916240f0112800070b10402800108024010703015246910341400c00018000044040c3c4030544098408142007404000c0011440640200320700b503800c207503c0030400c590a54229040907401000680405000420220a0451203004810034941203032401c60091 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 353740872 1250 353739622 353739637
    0x10c24060f08030a09120f0f0602041a1c02041a03070909020d020a080906102306190210020301051f030e0609210a02071217031314010c081902 63
    0x1607103400081034205003c001050380107550307102c0d8084140e40340d100301107141d111007016203c5000c488500d0300050045a100b03800c68010300015041c40d44480c0f03884a0390700301c00340f1074500071800102200c100c181c0d01000782000703c03890300450400e40b03041d0a2445801c1c0c40402045400c40001c00100840d00401c462000703445851030031500c03522002451402580841390640c0881d00440019004900c00103409100319020828940c034140790441d022400828241e041c642780070506e1809c0200c2d03c541000d4400068680540c0ca410b2141050207800c01001d0301e1003032006401080180a20b445900e50500b01110550400c02c00c201051411001010124001c3c40c0c0350203494240000c0802c00070325001850342000760000c40342c0d5200c101e200d00344101c2c50283e0245e001103400b0410b020751001400591409614589003404d8101040409948100d94158031020350038404005d020150340d1402c030a014400c02040b0342000c640c800341801d5001814010015000300f400340312070003243c056407000b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 353742122 1250 353740872 353740889
    0xc010f0512010e0f090105220203070b0a05041a04030f12051201080706120513060905070807090218010513092304140c0306160806220b030c010c2406 66
    0x21541c49283c0c90b0030006041d2002041168120b000c1103c458041c882c06000d4030f14801c06001b0112001071074201d5652000007680c1c980a010000606004e1540040c984014180e903416034517030802c51003064450b8010040000c4801c00e2106000103022008111031a41d0001181403c1c56851003003101e003841030209a11021001100003d080c2c800012001c2c1a6032140d11024a5420603044103000c0321821508040760407100c4141802190700e5a200c0007199015000ba1000241c545c0300961800050707500480e50582d0006103041c10b1a2121030341c1a1805003440d115140562030300c0009036400342401040e40959480c141084400c0801c44c0800714800f0302c0c60051b90502d00b60501990306641c0c2e070885041400360500400702c1c0d28000c104d69114458844441010764041e000c1201e10000041a5940001a50060542d100c0c90512000f041903100340d0f000c1102802c45040c181003840340c000031414028400e1031300000540303103c10030104442e440000190480b460456002a02e0b09a0104c1503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 353743372 1250 353742122 353742157
    0x706051b1c0219080f0a0203071a0f010e0702031b01060503010e0a0611070f03140702040216030909110d050c04030b07050d0b03070509180a0b070c0201120e0c010f05 73
    0x2486010707254400c0464415400b503d20b01c142c11150b040312491590b2000300490030404c42c0196600c0620003400b0040319a104580c1884030598800241c0842c0480f00c005040b00d89041102005900000901404210407069840d0414890280d03513401100310300c0050100052102c104818250b01a80c001c0100800901030080f04900b51602c880c54014160360307a609200b48020880f250710215400c03540d000c0e401124604035510121400c003070002100031388010030005ca1015aa45001500e41420000542c040103152440c028080f4109070384010704e400d05007001800403990010a8a0003c042c840d80428150f460112804a40c880c94100034000101030b810303c0181584100036081001e102ca13030402400481500301582c03441144142c030340c04504080026a204600701c202d0065080fa07a044030f0302842c20395143d00f19031034100c4054002030914000601950b9112030300a0340040c8000701000328422039030b501e684412a225405060000c0d00061020980c82401192041c1003280040d80707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 353744622 1250 353743372 353743393
    0x418090501112d0c120310030b0a140f250e090103111905060403151407030506030d05180616060203012601182003060f04030f0c050706051b 62
    0x1040c40301500703d90210320000311103108500389881c102e62540f60504002c009518055103c442d50758402031295214841c000c400000040a0401d003a000b40c082c61401300b141034981544440702e04008100071504007101d0140180303000343c0d450002400080d019411030308030001c0310641d11020740c00011904082004000030602c0140340b0b000310342d440304507080c0041d01d03d55046c1540c072600d94007030640c2c004800c020800000d1054200402c00185070a00442e600e003038120154240c82e0103c82d0000400d8440041287c1c0303160034805220752103294142130341071403c001060302c02500e10040c86800f4400000d8800d4121040504084441da84030a05540d0b80d80c4400144180541c1041603010410781a100300c003208206014460701c071448111243d81d4460140c984d1b82c2080003d440c21904683c0d2615000042d8505004044c803d0920030256450350420b403030002d10703005510310700d00208403130035403810002503010075442c04840f0303203141460f00d680c4441341800283c13088581c440e90070711a12440300b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 353745872 1250 353744622 353744647
    0x813121709010501170f0304140409062a1103090f041103070f080709152a06060f050402030f01030308040201032a0201050c0301150c0c0305060709090b0105041809050111 75
    0x34141d0b60f0005a14442c16441702003117980780f4140c500340d15a604140820b100710000d4071400e40203e08014400b1800f50069180d410456100154590050200c084e081d244480000740c41d81d4004c120340b03404101219407400d803d4407401004c03022441803000c2107100b00e15607a40d4200013044605a10801c1e40da0402c008050b04071004000b04101140350500021215805641d400c8101c0b516400340b0414592040c00440f00b007070703910000e80c2240c01d17403840410070707403a0b04100090309510840002417214113010113160350b0322180e0302a40c4110300400c10042c0e142e040d80c07421411070742d050402e40c0c0b42e0317102c03071005070302611041003941902102840800001c11010f0b6061010045940007040070f6207600040003078501c800d00a5500b54240385900c5500184605c45100030540036004941450781c59603102410000300350355180c0001c10f40300c01485910824030030000303890b0342420220302e807030f18004e400f1304043c1040005c00000c1da9540104410b0080a40100c2d9801d12040303001641d0340b020340301f003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 353747122 1250 353745872 353745881
    0x10052704050c1902060f0a0905070e07090503070902090607021c1e020112200d0e0d0302030412051201030f060207140303092a0d03090b0712030c081312170901 70
    0x1d81c0c0307011002c2580c3e071460000c0f91607130254042030324000381a5210a04e60014140403402240c0c248a5800005400f0906500490040300250785010b05903190004061406499401540b5514030410002e001e5a843c03908542407103070305071070000c071191086807586000e1b1583d0401400f0780c488a011140200b004421019450340f00740c0b1003040c102160b00000d03080722180716503522403c036400380b007814001503103004e0115a5440c1c00081409800c1202540c14a00041e01c94008681c000c424003040003003c0714411002c0b641e515005043c14420341e0750021074074040c8400f500002c5807507210030a00c20b03241c0440380c00303582284804d010100640045540c03540200c4070060303030b405881c1d4652090840d4003259030020000905031200302014804000410b441307400d0440c01c2c0f03c007003040001c0c8083c4880c050148203000d031490040d065001040075060700c1e03880301040f04100b41002000204209041d1003000c85030411141009290b00380016604080100070421408110382c041003d0103205402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 353748372 1250 353747122 353747137
    0x909060f0c0c070b250c0b0306130204030f02010e03120315011b031805040b090c0d06030b0f010f1401020a170c0703081b0a05120306030c090a0509070510052704050c 73
    0x70381e00102c592a4000030300d094000000240741b00e42080082000d40383c0440a1908034000400c00d8a626490755220001c0341d00592049490500022515003590f8104442085250f829405440c000800c0420104684801000d81106c05288018499241d20031108030040303c0c540095004010001c4c01e020b01041800742018100b0b84201d08089240e040c0340c068060300307404c00f4000030241c1e10f0301e00340c10480e600100e006184850341d6510000c007280d00e40c20054081d080c20f804e1003440f54103028144581100b190403061800c4410b0354400803990b40001c454100f02d400c8000c00b141190b401030101114415861081254421280c01000340321440d0300600c0c0d520f035205a05440c0000b24910f17551549005a00601240c00644038140c1c04d01c20f54002710703805500142031f90004900c850025504c010261405241c480c2d4038000c00c01041f0007085010058101210305000200c0b80e148010114840c07030710307000300c81d42018203c80110101c01d1000703000c1c140020003d0209181500c12284650070810 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 353749622 1250 353748372 353748397
    0x3030b040e010c02070e041a01170105060d0317090723040e1603081c0906020706050609010302130903020111030106050c1507050d0e0a0f050c040b0909060f0c0c070b 73
    0x200707041841e21051180d224800c00940240400034608032070942d000c200108152078090703009407407580b00070441c00070038003906a501c2c4244044288e4100d035030864000a10b400d0107080e40303811540110741c100420409260070624245010794485049030308108441d070100d20b04404407506003403083c45420900d500c1202c25101040703011643c030b4030960750b51040b00f00304808482c140024004542c0d10002031503c1d040d1170052940880c510082001200c43e100360a5900c154003080140c20000d80d4000c00340c01c5034044440102c1541140c00040211142c41ca0460042c1d64450410781018000e41000702038088030080c26890390307924000075002d03901000e01c41844d030080c0960032120456060100d402924a42c2d2524103220094050900415440c00c4003030151040050000000f05400f541541503032040000d0218044184103010613074100b0b0340400d1181040ca07082215540000410701c0e8442540441f10f5456158111006182e1041144448490058840101e000d0300140001c15003628840b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 353750872 1250 353749622 353749631
    0xd0b01140f03031309200d0207020a0b070c06031a0901080606120601241202030a14070306030807060c0c08040f0807170a0201080402010e180a0506060702100f09050d03030b04 77
    0x707108041e100c3c42030b10300b1480042501c2909000c40700b82c6500820385500c030008819003090340c00075090b802c2d801040f0303051031654000450700110308106000c58014000806540e0504c04581d070740081c0e008003400f8042c205541c038140704501c24201983e040054001410213185561146912038071004d044850b180a462186a007880c1c20000040307080c12160300c100a0b14000c4100c1401d500000d0b6007080301c20800209421a064803200e610046000d00f58860300050840c548a468000942009101c50305062406c4400c002046101d81119005613100c0400240503401800989481c010408054003100e008100861450b130310180e901d081e602d841301160140c1e07549c0d0f0408070304503444180c1100e060b00040c50b03801c0154041c0b120140c102e1b1050400113044211030300070035800003500da006902c0c0b0045170140003100c00c080c0320f1107400c02000e42d28985001150780200e80182d2420700d1100820004400030b041d4148500d504070007418004140c025404000e0600401030145111610322079031030f2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 353752122 1250 353750872 353750899
    0x102030402120303130f0219080105160807050708092115010f05010c0b07120e0304030b1b030f07030f0f050a0b370503070e010e220b060d0b0114 64
    0x240c034441c41c4e0305062114084c401d981d421b108460f009004030303000b14000c0c3c0b5281d1180d0400340c940000c1c0920000010fa14585007142e4410300354846400c2c828030400d0340070301038074980c08002c9400182c4c00600117030f5514017002c04681014444040c0c41040101030304440303a1004049480c2c108040013080124041e45c03107a021071406809881030f240480c07510400342000803050101954005020709089a800b0485246a0151071105010080c107810004062041020076a0700c035422010b40710398080b00c2030014102e40c4103840081c0c601585107503903100003560207101e1341080c0500300810782c7c24481c0709103444800c000346c6026102c0e00010390400c4244015400d02500c1820450000c3d0104207a812101649010100b94450183c0d206864800c1c045680d403800c002c580000c1c41c11407070303a445070340c9050340070304000b540688061200d280290002e82302907065114030082c0c81d040307051043d02ea01d41100103021905000f00061452001d48000181000d00303800b00e880b02d0320203694098030000b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 353753372 1250 353752122 353752159
    0xa11030903030702010e04090b04111315120212190c1202100f0c0516090e0303010b040e070e18011a090319030507230c0402040b031501090504020c0102030402 70
    0x39000400d0380550050140d040950321495055148040c0544000b5405844c2d840303980c90014125426550310009549400c0c090400c19045002d01c10b5041d800c2018070424110f02030b400f03049100d01004030050902030b07404e566403081d070b2918294410007100c11203100d14611200c104c0803c901901d00c2d82d0002400540d44500311014207590758000c200c01c4000380054000d03245140d0051040b010410315030048000914204805401c200750804c81c489600e107801c21002c2524440c4c410010b041d04240300420501c1460300c15242078483d00c042c5480281e42d0311000322401d4248600381940140d1001c071755558801c581d4803040c16105040d4424000040c4a030712480c06103e0300b1001340d0541c1c850320390b144180c000500180030440c40391611900c1c01c1e1079915403e1081001d2104400c40e0184402900003001081001c01c0001e082910150b0915140840005441c00001c11710181c00d5019110b1f988268441c2520b10090718001304110b444504a41c1014000e4104485c124007840000091070350020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 353754622 1250 353753372 353753377
    0x3050c0d030c1101202b051c11040602030702041a060412061407030b0102010b030607140705190506160206040f03120e1f11070503041502010e0102030106030e1507021b0a0302090a020a1103 83
    0x11f40f0b515180440a54000207000e04000e001d0f000300c2d6072241d0f0880200d281000500040566600940e16138049004000c1100c03550700003080000c50001009140da1140c074165011500e5409035140c440801d400d00c00c01400382c030040000040543c1e000c100ea090341541c0315080d03c12080c1d0080061441c039006040d62003205a0305880480c944c60310003c840d48442c1c00402880c0d12407015581c11404c02520b007040d03108001e40440d0940c02840400c0851220307160b9440a2108a10042032035050980724801c0e00344a440015003080500c021600030020260030030002d00d04528110f4030907103071070300c09840d451000c1100740003a20b090050140241140800303441d40580c11101442c0307802d01d040700c0b10702142106003d0314299521101c1401e8084401e201542c001c0816031004141058440d11460600603c14120018903415006201955038001050b002d0741c149010f0380d4a0700c8803030000051501c041940001c1d0320414241c208120102c2c5500503001032179131511480c030300a0301501c2c855103a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 353755872 1250 353754622 353754703
    0x80f0a140a020f0d11040503190807020906011106040c08100b0a12021306030b0402040c05160215040308030c0a08090d0203070204050a02040302040c0903050c0d030c110120 76
    0x3424a80c01080c0401515402420980803081c0300901d030480340b0615006403400911400541080400e04000034101806050345d07001100030302204280c41036544400710f014180c0003030701a8909100060945c0d00a82d403600100e00e0050440d045841c0034904440c00c0442405181c2c994010304080c08044801c40c02807440740c480080c8034031034a42c20140f090094400c05c4000780d038082198008030781b00b562188258400b46004595505c0c56182a0050000796000f4100c8401001010048880c400401044019282c2c3d81220a840d141d10303021120180d6002e40d40002e059684d001080c000d040205500400691001d81c41c0e010039940d5550f82c143d00c0d01c01d2034010354096002000100018505503000766070081c0c00080050a1940704d1b00070904444e9580000c4003c074480803414024090100f00750405a90104d42e00c005071445039400802c01d002d500002880c5547c24500703264141c3c09202103c030b03e94155095400707402d017901100c1d96621030b01d400427402c0d2003502e02d413600294504110100c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 353757122 1250 353755872 353755901
    0xe0106050a060206041202010b1005040e0601050405060d050603031b030d0b0108010f0e090316140105220f060f05101508010b160c08030408030a140313120e040606080f0a 75
    0x205d903140e86803070a29101c0180140d0441d5138a00380c2c500c50b42d8030030143e01504066030f0b803003a841d642810300c840c051002c060902414803205010401190f601c0104494045071001c5000c1043e4a484001c680b45000d4043e0785a42d44234034070388104a2042c0040030304941c1e0b101d200c003031001045403801074490030070030b005010b142840d001d4144401080c607441c4503080312184044a180441d0b120080c07040c01d08410381110812940d40006c1940b080034040c16400541d90700c86004945480a002180e2040c3c0c000001c182c0c2450603494800c8c401036a00103020188400f1051180345003c495119604bc180d0081c1c0e5503c00c80c046603180001d2283e80c499041e134034840103141c507000c0c0300035061095a0545508170f07540c03012100c000c14180c500f031000e0002403194800550311404148030180480d170300c1c03144100e8003020030300810500080840c081c189036500100c2d1000d5099409104a03088a81400100e0700207090400000f155a488103c1e644100d0451401c2000340d04c7e80389112043c1ca00400f000c601 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 353758372 1250 353757122 353757133
    0x6040506030f040c05030313060206070e2d040608011409060403050405090c0c0d0e04060602030c1005070507080301030f02090601020d0c1502041d04060b19030312090b09010e0106050a0602 83
    0x4803103a03126003e803c01d01030108210410764590002c2d145070301c410448219480a203808205c0f132a010850180c1046180c10a41e181440501c04144808480101000004e1b00506403404450804015801c03503800036005001058171001240c0c040c050410b508129000c004000451100d40402c00c3c43c041c81d4195101c5241c180303800c01b00500f5100c0581501285c4a04201d0080c260004010201d020380450f00e41c000045082d81c2080304403112035000c881950820020301025080219059154100c0e040000415841c0c000c02281c490003007010050491100100100902c0007541e035a03e80d0a05c2203804491a82d2050012a194140c14418001040102012400080340c05011034003c0c40d40700d2005003403545c6c0d010070800840810b19010400316180d024441489002d002c0c000e5200015186030030600804049401c07007080a10000d002c00c01d0140c04800007c140d0381020820743d4004901c0040750510120484c001c0030403001441140d86408000556401d00d01191002c80c0c0e61600a441d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 353759622 1250 353758372 353758381
    0xc03080109020a030f1802040513020112020d0612110901271e090b0402100309030504060507050a0b04060209130614040b0420040e070219141204090f0501050604050603 74
    0x10040c3d00007050380001d05445208007140c52040c1d1040441c17198070480c1d00300c05001c540c0140300c1202d401611585600d01007011140250341c21a00d0346c0380c240848200103a50348880030401d00240036079001940c00010300141d1806000118070010f20f0b00d00c0032101128142d070b0307036141007500c3d0b41105401ea044424541e149040032440d40c0c4500f0200004203811048004e00c1070207003084803c010411501d2a0095050000390f003054404003040c0007040c28200b00301409a01c003c1d09500562280030108100000c0c03d804129040c052009031590150b0004550304051400401a40101c8007150240e0003250307020204d041180681822112945000c641c2101401c0922028000440c2040c1e0030031740b21500c030700c0e10450154079041d0010041d2030803901ca80c10100e200d00316080c00340881046600a030200c032075100320034000c07040041d0300c00d00200300c810809080600b000710503402d42d050b040c00880d00044c040700383c0d0400c14151041d101c04209030783c1c0721001c01ca014020b6010300358001200344000ba = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 353760872 1250 353759622 353759639
    0x50d0f15050103020d1103070b0c030706060b0708040509091908030106110a121413090b010f03200a18080f010b12060402060f0d02070312050105121507120e0d09060c030801 76
    0x890740c03040a400d23218aa6199024207040303030702c46510042c0b95803000500d50107100c5a8820170001d41406039040b40344c60203544a1400501072401003c3c03190101c000805d10040003080001e00280c0d02d01d20b402d940340c01600300041140c0091095201081410a500f80d0710080403419040c2c1d40e40c0702e0f04404150070040011500c0001c1640c0c81410140100000060b48245484000017403030340500c04144082450001400c0c000c2041c1c074030051605212800703054400120344800c0c004017081c42c0b2a1a410300700000c94035410703041c8a1075060344446a02045101010070301d01e1109400100a001503801c41c024800c8000900d240a01c850704190b020900524100006000100d5074142090801d102c20740c10b00126406a24120042416001140d10900480c02440d0040c58201d85080c8501520074400f42c850010070707840200103c8400000ea58580101e815070b050602d651402c20052030a10070782c2c0d603107144012480000c030f41c2071100008e00d188580e0340d00305910343c1640d03070912513407803d05c55 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 353762122 1250 353760872 353760893
    0xd060c02030403150902240405060706020702060315100f0e060c07030b1501030b12060f0403030615080a110c030a140409020a05031e071b020307050d0f15050103020d 73
    0x4520840c00100030010108011001c40001c1e03a901c1000011008000e104000004910984401321260303411012014450403001740c40031a8002e0340e00369921074091810300020f20840c0f400a45c4040044180300410b110410541d4030720405030391020840103480b20980d407145150b400f40000682418040105040402c007801126440000300c400c216101e540f00f180900301242c42c150724040203000c40d116580d040c010800c20403020b40308681c52a40001010380c40301c1005059012120600000c10109071099010034002c01c3d00d0040c0d04013144a24800410520080da00c0803001c0c0d0910300f403010326051700c0c4d007100d043c614a40021442c0580d0b011302074514107206180c00c100c0d04801c2c403000400300d015000414400940355591a601d20f4651408006030148243e90034440c0740350010015110b8100f41171458031075034a003094400f50100d00c002840d00d80300b84c00c21504840540d40a10400c42c003c0440c40d00c10380b050360740103805c4903100501000c4503000d100107940556440380400210f482d4004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 353763372 1250 353762122 353762141
    0x30807020c0a1a1207180f05130b010c020910060e03150402091003061e0c170105010309050f07090507110105040309060c060219090906060201090b0f07050c06090601050901050f0d06 80
    0x103a50402c4c1c030301340e1132210005040305c0140c0403895001d0140c00c3d050703c60320440d028000f00c5690b201a90f0402e40440c0458050185038120555944041c003201d0b80214800d030401580200000380624000d841001d80403040d10901c00400c140026285061802045440046000300181c40866845400708a4404030143c41440e11440d11003012000c80d505014145040b0300c3d01c965510300c03258007401030040351403603020002001008007800311090b4201c0f207401e044403000d2801003910300d03c0341041401c0c40d10b00410f200f16807003400300001c5c0c00c07811a00894451019034403041417040c6c4c4c2d1510242a80c8003141e00400042c02c10400380302d194040c9484c105510301070b0724014203004002c2400d00c001d4100e114050045241c2e020108032000c0107025030006860f65200a001615540d51004140e55010f444500200210000110403511850540d01240000c002300d84e01800e0054017240c440c0380070f014845c0241003100020950307041c142145401a200170300100810016520b5010043c6841c10703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 353764622 1250 353763372 353763419
    0xb0603130809060c0106080c10050316030b03010b03060a0c030b030f0601150e03060414010509070803030613020903070f0e0105010e1e120708070905090c03030406030b0a1a07030807020c0a 83
    0x130032884500740911410015141c4c2d60000c00c3d03902c148030208481c0745003090b440380c20401e0800400035200399000c1e1001e00100c072030a020800c01c2440c0c2c0000d002d00700d0300380c8464041c454a8100401c0c230760a03810610300311105890030031002aa420500d604c8050038886019240c1c000320040140340248000c0d0004603032245810728011340c05000090408101b0381e000d0710768041446d9803ea03d03400c20b00c10550001020f80082c5060391821501c40d46a0100600f603501c5030b24524540c805080498040f581d00002c000d0580341055151000e8002031140c42c0500101d2004600020450354014003030099400f0006000c4034044021001d02c0c8000c10a0341c10182e0011140b0514501c214810880040940140310103000c0781c0c0d00b005215000c4034030041807100c0d541e1041d0034010503510040125001d032640d5140205070320359a00045500034029a010350070304407100d90f2885280081d0740c05000c490740f00740d0b0380c8507040d161420100d80d603070349500c0d0312903100c29803d03000c0140203010050708038900e0307864 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 353765872 1250 353764622 353764627
    0x1a0927070e0d1703041a0601020a031202120702060103170a140304020f04020d0c110c18090f0604081b01050609161101020310050a06050c1c051902100b060313080906 73
    0x1a40c43c684115840c41ca0035480c89004000d1104201000341094442c0c11800c094024a1400e600000e64522403500d0203001d0014541c0e0401300600707203404a070b94016407131a183e40e05041440009564590034802501d03015004c840e81003a2442c1c82040740c145050981c1c40c924110580b081010140e800a0300807a031103ea8031581d02da403500c890000d0000207102c1c5038001241410b07030001420900d800310078039002c1c0c1c21662800c007031581c80840118407950038a070108940e954030342c0c03994545110394002d0b1020340700300c00401040158890003400f9274409a0803000500c0e0500301414241c3c0c009544082e1f1203c1408001600301006590650300b442441c40c0030040cad88181c042143c2203a000b9600000c403004424001d111070b050109036280281541d1424034075000710200311645074206034601007007484203004204000c0381310700e00b80c401d06401801203c1001e41a520041c2d9105085a40c105d00c29080203401220781c5412070681f44100c1c0562180441c21072140d80d812050750000300da042c0d200609 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 353767122 1250 353765872 353765899
    0x91002010e060109150f0315021b0a151a010207140f04050406090212060c0a0f27031202010213090b01051c06080105060405070f08101a0927070e 64
    0x1000018002c0c90703083d034001031070703000035106172928401e9801520700d00610b00c408000107080d03d02880080859075100503103036000410341542248a000300c140041c8510300402d418403c11a080c4000e043c0480c41c00c00c00d40c92001d10708a0143c1c0750885032070150f00b1800013003000313481c00d07014001c0e040402040b4407108080c0d6000602181d42c141d90981c3c0450707803010a0f604508040070400c4040e101d0100a15483c071b084d00c1c40041c0d07441b0f1840001d0030424582d10440096009901017a4040304007060a6054060140d0005c1601814401580c03041600004041030a0040c805c0f240034186002400c0341c5541082100400f52545003201c0e4104581046000c3d509000611541b202c142451004034000d40303404419070a446000e00240c0c4154500024403108982164031107140700c6c060b01b000c01003a51224404035401c011503004d04a60310000552202d240324500080141c0c010445d815000410401030040c100d00c4070590b070740c82c4120000f000c070b1140d6000b0280c04100d103a0040052280210 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 353768372 1250 353767122 353767151
    0x3080a14010e06152203050c060304050a1106091309020906040b0d030507050304170a1502090904020904111c0201090b0708030c160f08040503250902250f021302070809100201 77
    0x5d01e0903001164000c07014140308100c2d003403002d43c1e0241070480301503056060a843d810b031204203d640090070840b45401c240e0725601c80c0b01c103448a0403070092905181c442409085409804500401c0740701d0b0700740d240010800d02e41445402120500600802c01c0f2402594050301c40e6400004156654402030000090852480304404040c20a00001d0403030320403070340313003040100181d8102000d9072030040c480314083e40c4600c080e160b0f000343c04441841179602c4078140080321700781c5481004c1d0402c10750409501000e40b11200010800d10230780e80e0880e803d9035801000030364000e10100030051001040440d00031548140030384180c581c020700c00e86004815546204031400406000c03254654081010810791806200e03c0f0000140f40d51004ca5503036a200c520200f010f4240109a4182d5001c2045051610444050f510340d1480600302c40d020003490a00f04030441c18520708904c10010020b130381020803011700a03203100c0755100c44220304004105040001099032a24040110366031400081e50303064 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 353769622 1250 353768372 353768407
    0x3040509010f081209030607210903030203090c030c060d0509150406050a060501030b010207030305400b122d150112151a040f0303080a14010e0615 65
    0x400b152058140c00c0c605512903040c000180300c00d80258506226080c1180ca0101e117a0b0b900c40c0840c81c140e00514594440762240b001a00000740a29141071864410150107500840c01500310700101c400c070102d40405c00d0b40d08c05428049540004050000e40c40b5200d582d00038540010794078056584004400501e40c149040446060300c40caa158070078008900c00501c54040585000c0c6800e0250410302c60010b0350380c00161000a04015002481e11070703040000225801e02880703044420040c50300041001c090a42900407101c2c00720301e0b440e0001e000b4400c0f20031500c8800d20074144850f81c0d5a10034a40910200400b107001c0030082c095100b90751508800081031186a207030940d594030280c16000102020000300310103031502d1904440c44201804507092000b1240201c2e40c000706500020010b00040c040c2c0c0c3e0207030310500f8071803002008054205021911525040c0c000f040380c0c0e600e0750003000307a030f400c28800d035001d0170300080109500e4140070204144520140b0200ca00c0c051842003141c4200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 353770872 1250 353769622 353769629
    0xa090221091005130f02010804060e01060f09060b07030c0b09010b13201e0c0102130e010e061c030c03031d0a03120905031b0a06090804140306090d0e030304050901 72
    0x2074118028040d00300000e40f090541041488040c030120b0f01a0381d0f109007200485110190601031000c0018040161079041040c4900304c0100a00c1025a02d00c7c1404400c55240551002c0c6400e01c44040b070071007404000e640202d909a601c80316045401d0b19000445a805080500c20f5501c40c00d08500340c3d10b6100002d0b2039003000000008401e250842501e0445175100c45044c07841d03d0800c00c0d54020350350b0800324016030075000226940c448500500354028410075101d90043c5890301d00003d0044140c0d00c400e4102c802c1403001c0e203426580d203002c00020444109910240107402c40710340c00442d01c20450030b24000c2c828207000034054110401101c40c0007484884100603031101d03102108040d88100e14400c107400442007030140310481da9032a510fa00420020017019035001000824114080006401860b003281c2c0400002c2324504164a0039031242c01400441c4030040e021000c01e040008805208940c02d60180011a0608004a42d0103c5811603194540300501012400b9500d940229009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 353772122 1250 353770872 353770891
    0x203010213180912050c0c0a030503040e181b0d02040905060a1404050316020a030b0a0615020d1e090e0901050718120b04080409150501021b0a090221 66
    0x1c01d882c241c1e1046800d9040c0000400c100c0c10314005900080e15044001860748135410250307260070042c00e8503460b11046048150303006000e034100100703001001c4000e10981c1c1205001c102c0c240c2c0c501c0b41258501500c02c501280551001d03049004038801e46039003001e0b1080c000c005080400700b5800007400c2d600364850580b803c0d003000d01805150041d074450b400741d0b40da070355400700024681612801d0712402408661010072480d80e90090031541d03501c003060f000c2d50303108080c0800c03070804403090002000786001c0c00984000d80340c00218a01d000142402e80b01c40d096580c05001c600003107011000c1b402d0745002c1c0091051184010a00c900c4100740d403403250405000000301071622a00007404501c180d4641c0107949015a003d0181c4444841032034031103a045080e1414944451030800e03d148a2544030343c484074a000d003403040f0b4214004000c401c66400740e08442d041c0301400b03804182112050f5807240d1028000c002040b40c040180c0141514511304005443c503070900388034581c5a0310381152034620 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 353773372 1250 353772122 353772157
    0x16060c0803190524010c0f080306061608070203010c140d0e1905012c03070f170301030308040c06030218120313030b0117010903080c090a050a2903060a030f080702030102 75
    0x2e01c244d0380e140700e0480c3d000c24641581c1d001400e03110030780e00440110000e440c1100000010380f080e181c00d0100c6000c41c404002c0030089a106041070300350350300042c0040740302c1e5003030261050109100e14a080603103440480c235149000130105402d401003800e02c002c502280102d01c000900720401c0200310b00030038020000801c0d80714800009984542d048072319442c559448a88074000d0100000c2564022940030068a0358002c0c542403101940f0b05044401d00c103d40c00000100402d0303440390120b8019482400781c85207a41e1100d0056043e40030b407413034540100c1014600d0040c585488008006844c50240a4a2414101c004a44641e0001d600155198201c110040040c880f2003411b04c959401050001c0201c101c56a4009181601c040c0040b0002007011821840700e40c4c4070780c1c640005040040144840d1503170b400705500c20750000141c40f0410307002d802040c0b44007004101241d200ea000241450340c1c031802c542d1003401c0c1e000c1040b001d0720f560344180203580042c2c07000d100604110f10049d41050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 353774622 1250 353773372 353773411
    0x3050a150b0a030b07230c0a1502030c04120503090d0c080c03011a100c02090f0f010f0302030c130f060303080a0e06010e0c0a1e050423010e040e0f15070216060c08031905 75
    0x20414280c89c400580720034410001c1241c581604001d071019103464460340042165541031a030300e1402074a441580c460601c426640410448038002e20407110403000b43c404007548102010700b00c0b192030080150300210540320140780e10705140ca10603002451304080320031020079004118048c1040b1442191030841c0c4c2c0a028001180c01a201e0061500310550081e440c00d540c0803d894144140085000d03206210800b01c0480e001c1d001a0781e07918020504001480d0b482c00c00400c10442541d01c40111803808009902e07101002c03e00506960300b100c03860003da02e6074440100580d0180740903030108080050030303034102a11541c0d071021565160303450396241d500b0040190039120003010903801320ac0458040e01d2075a60454010310150030104c0d80019501013076000345051822034241070f8514010346910800303a040300b800b12805690150300b1505080c1c00082c0380784d4400070074003520021403842603910001914610045a100c0c0f10300d03200213013185100308083c2c1641c400f41d4551a0821000d80000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 353775872 1250 353774622 353774633
    0xc02060c030709030602090409050109030309020103060b0f030f040303230601120603050d140c01090501232208070210050a0f0306050609010c080403050a150b0a030b07230c0a 77
    0x58004030600481441d50802c0390000d050b0450a00c0014840c5401150704800e81e6070b16406011010740081c000d1103149090324004000f0701d0f2140c8100c0c086898414045070450103541601d074030001000d6013920715107807820140040340000b00b01f00c1c109030701e851722000030401105658026002040c40c003020f82c00c050002501503c52400da042905150000c00c101050001850000345411410b00c1c481e95180350104030355078826416070034060360801902800f00710341540300e440c8030a240b03d2042d02d00155503a109280d004242e4294a014201c5602c44080c01403a43c0c0b09601288540b05684ca000344030f074045035070344a10118250110340003180a240590304403988500a000c0d03440d04200c5207003420700048550040408190400450103918420855030504540c00345420004031246402d080c6010685491420310402c419800d00b481c0d0241810304422110580c4d91000f8000e00c40d0352245400c5400c4d10707030140448541801012000c2d00c00c410340c401040d4182d16039000d00b0f58030001d030405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 353776978 1106 353775872 353775883
    0xb0a051002030405011e2313060504030201020f0f06011815080c010f020f1207080904060b030a0b0a0b03040602030712060605040e09060708010b1b01050405010c02 72
    0x2111040c94001000e88100e65091ba240c1c0041448030b0401e881201d4480d1184000c100600110b00100e0800c142c40034901420075009810541d02504c5484c81045943c406c40120f00300003020701c10f659040c00249002007004000b00300180c4440280c550b82d050510071007942c0411042c1e540c0c050a03140e04801e52858004a000c007040307844040c0962150f03d22013119021070000f005254880c1d0010403000b42001c2c1c1c000140481e2414a0340301c900c258408002160481010000880c042c1d440740b140a000c0c142480d2007a03106e1038050040340403034005404a0b4840e0410100410030310303e6000840740d205500c040d0142c0c5903141d00c80300b42c94001c0102d100324029402d041010031f24590040242c012280241260181600d540a81c9500c0380c509440000010f2401801400710080f918020400f24142c040014000c00a9072807180c04c44405032412110b41e51541c06604035a60b04100 = true := by decide +kernel

theorem cover : BRFrame.Cov 353597122 353776978 := by
  have h0 := BRFrame.cov_init 353597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 353597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 353597122 ≤ n) (h2 : n < 353776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
