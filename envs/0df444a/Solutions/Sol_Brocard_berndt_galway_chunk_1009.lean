-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1009
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:48:39.18839+00:00
-- url     : https://prove2.me/submissions/cdf2596f-5d2b-433a-8dd1-28a4fd558f5c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 181294964 ≤ n < 181474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 181296214 1250 181294964 181294973
    0x6060e13060513060503060a050735010e0a050702010c0504140301021308060610030b011d0102160e060a06020a0206030c0702010c06050f010302090a150302130e010e0c030d020307031d0d 82
    0x1c0804443e40001e440e200140310070718042c0845a8841c1100354200407502e0030382c1d030042c20401c07501c1e4828540c505560a00318800741c030040c0c10030048800d002e800c51950391498281c108000803102e035202d207450300c804910194818015490901c01c50356640c2d00f401c0c10240380a80003202d000c00158199402c111844030b21a001d00c0100c0100030a00140489140c0320f0140314903400c1084002080518018111006a800a5400305440c014140d070680242c1400c006030310f081451544140004580d18000403030626000155105140980d900a44580e590f1000d99540a020100035408a002c4c0700080c40d403030204015100203401454241c0d80955641c51b0602181e106407440aa50881c3ca07006000f0f6007002c180294004060000800212006d10854104540c20f404001e2050010180090320a010342d044400200d500383c0c002c00810308483c200d560f60360141c17a0b07594040c0c090a40c40305441400401981c0c2e0050b09503c1e00e15900c103040921448400b611103115601949213140140403e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 181297464 1250 181296214 181296229
    0x1a090c19051c120503011d0a06050301051005010f051e03062e08011205031803030c0102040e1509071d150d090b0906090a0f0f050d02160906060e130605 67
    0x4074a5105140c00c2030100f4100181c28243c0b66103400d0130301c80100010080e861030000038105940f00c00110403425110f90740d0004c054071495200315495801c05041c00f94854600c09002c0446500b40c0302c0c001c0440040038140c1c0c0c28051a0041803211909c080c0300c0120040500045512100040c9040c005250044210780c17050784003005d074207000303011540002d80a40c001e00035a015101485182a0030449030f529142e41c0d21507410310100900f244e5a105030030781c5040050382e0070302d01941c0081d911643c032040740c074009003403c4a039031141b80302c1d2041e5001c440c1480320040d07008100550b01d040352055140300d440b000300e41104000340c201d407030a0500c1014214240c081e01341004480c0000c1041c55450400000058010f000c448807074100c0030501400b000000780342e82d5201e5121003030080c04440c0381031002e0b0109101d8400741840c0259405120200e42c04241181004220a080c41c1000d85805020080b0f030500e000350f201144411003e880c162410b981c00d0800c00844e4580810001d40300e50226840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 181298714 1250 181297464 181297489
    0x1611033f01081011040b0d060e010b09090a0905030922060e01081e07051c02100c0b07050307020d0509060c010e0c1503090c040e0f010606020303041a090c1905 70
    0x829101030051101c5101840f5494140c07150490920000c0598400440540306501c142644e001d40003a1140c0c140c500f641100c4001c0604104d2051075682d11142d030081540990103152040e8864800541d41540302e110303103101250418011424100004103100c11000515102e1f10001b03040114043c140a280c0241c00203460207403135180f000c1d4903001315030f4540303000c10400000340440d0b1054031140241c0042c5c0d070404c9580440e40300c0102c41080510704030a1100d100c0280d0002100320010006907003126155180d00c0c0f01e00e0807404280e480e4001240ca900041c1c030940010b81040c64091152441130019168410f0000c041e2881c10308415415421909100701044070764012551300035040c40c1c2000c82c2c211030007001ca0b82c2c0c0d1031460640c20880e00c034800c0d040c800f1721442e50741c45d06854100b41088110517402e0108002c0000b503403140806940e03034108442c00c44201c1c0e00c20000c0c0d524154400d01c15406880c1c00c4009200f030322070034407c100046031b00c0100b450000ca400341c40010540d41b004006e084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 181299964 1250 181298714 181298827
    0xd050109030207090513120e060f040e0718180515180906100b030c031f03060515060403080a211802030618030301031217040605161103 60
    0x30f429140500e0034080d614010140c0c99194030307030300810010500344122114440c1151400f03d03801c81c2c0003800a241402a055011662000400c0100399101d80845840c05a600f6403910001c42c444032924820413883c90188140f0590000c0c04141c170000365420294010b0402e001819000d003a5074003181d4462a00d41303035080e044103200c003448030b203078400c2c44025080f03071294840c030950a00b441c05d043c9940c40081c001d0781280d070b40000011000101510040c004035051581030403030715600d0400030003404003130f20542c909000440c80d6000c1407030030508640c00c5a40c0400031a0074003c410100740e515102440c03120b420324411603600c01032101c0511408003200e1320440700001c41e56090041c1813030300b8401072202040c8108032a03448403580e000401d490440342d00103600c1c03505001c101011940c2c03070001c6400e40030b01c1481c40c00340400c2151542000784181202088009a95203d0b442202c1803054104011880c1d001001000c40450360341006059082d01041001b10b0b5000c150401700f20080803915034903 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 181301214 1250 181299964 181299973
    0xf0c08031608070e0d020918030a050c0106141f0e1504080c0402040f1214060f0105040b03010912110a05072c040816050c040c0e01020c030313050f0d0501090302 71
    0x25150b90400d6002d07821120618041d030020001201042c042c8180c07181c00381c070409506000500c44070181510103180c003001c1050740d480769040d20000d03105800c8401c405180e94200079000c00e41310015201c1c10151900101112807055140c1c0701003042c4090340c85908102302034410040c900351543d2510140003042c3c1e24040342e6461030309480c0740c100800071540a226500420041002e41013241c130400c1034070b1030f003c3c8100c011103241c641104009001c8003041a50b020310000c00c5140d121000300d02e4121981600e01f0300c03800718410708050880c0c2c0092001042c00103200302c442444d42c4903054107105c0b01c00d0385084820102094940a2500c0307104e501c0001c520104841506d082e00003c12078007040d00c001520b9000c01d0030559100344039400360020104012a090070b0800078030104004d80248000060b100b04140703070305440001c01c00d2018910729809881450440c42513403c00104842d00821100c04110304203080404200c00900500c42d0321b5071000da51000400440e400b03204070001c0610035002072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 181302464 1250 181301214 181301251
    0x24070321060605180108040b060103020906070b01090b0a08030a17071b060b150304031205070302041e092d091103070b030a0b01170f07020f120315030d020304060f0c0803 75
    0x83c035028100d4030b01340e040200200a00c000507920060154001c4070900300940c8806203000450214000c070b5602500003d116000005c00032415030200e110854207a83c182040d9444941c125524880c4005010001d84040d400e50003900320010340325001000b502c2c00341000350201c8140050b44c3ea07000416030302c40340c5d61009030800e85403022914401804a00c01c0a041d80f4194030090400c00301482a9009140c0340c000241c51644694102c5010304190038003404045841d0718540a01042c9000f403040380c2e40b07814003604400422031614000b61200c1c00840d410401c4107641030b00070700140081141c4081c001c41c3c0d0107034540e0341480181c0203000c0d2641c5154580c680034030b00b0029100702e606100d0611044c100c0155020402d10101c0d0f03400240300001e602980c0702e0b203404a05d4404219000f42580c002c210429402607528401180240e503403180e41c8041c40c01b60420941ca070f07100c00c480d000142e1f01c100f104101060103020341003141c001d54286810042096201c030003940c1d0040f03034400d400d000360300d50f00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 181303714 1250 181302464 181302487
    0x1b010501050328060f09051b0f0a05150706020c0a030e060a080703020310080d0c14010c050304150b0907090501030f060b091c050a0302060624070321060605 69
    0x815004203400c034020a04003030315805000c10180c00d0720381611203c112101d0764060120681002c0303480208200704000290060520b0790702c0b000281105210080324511852041c900b803411061004401403505482c945031500b04814040c0044400c1545030003030220b0360109200b0f10181143c6810798000e00001038152400801c0030407100b0200b440384009204004d2420b901a2080d5070000003400c0040c0e50791111b5020780c080c0200d59024028600c03c0c060304410b01070f4858041900780d4481d14400b4406030200d61340034242c1d9800d5000d0800614280006804640c680c071120003080c030131860000703001c00040081245400d048030a44003003000b01c5810003155074980b00d81010785466a404100d4541002c41800040c82020381461160b40907540e425007145d080d18010b0016584030084807040310b11403401035158031742100c025101d80710380e8812034a4074912490380b942c07428140d170010746042e52540c0d0645640c01c840d00912603000031a866003030f142502c1c0c80f840300600210703160360f603d03500003465 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 181304964 1250 181303714 181303721
    0xc041d031207140301031707061b030c200606010305070c0605072c0307090b060f180a0f270b060a0309060e010c020a15091b05040c050304020f0d0302030c031b01 71
    0xc01c0107200c07040004002051a1000101160100c070107c1580c42459050810241107080b040342502a1000241800141c050b40b0410305440c03603440d66424040c1c0309501511429209101d80b440b40c200100040242d07219030700c415444085820b10604a1001d40c4584044500441d11080480d07601a07c1d00e0200400440c4500750010750940602041994400310fa180d0a4510400c3d03c91a1a50150344060740c90405450521080001342078a5014000c2d800c0d0f4406c55680c0c06500440103000f0100f0800900a080c005071181c03010140140340010304850200400098a00c0f0195501e000040c1d865603004000d00740124185c1d0042800e10071400e095003158900069400d090385403949020b0110303004500d046040e60007030342198031201c691410102416521f180180b6400345480000d078003481c1d403115041a11410f850400c480d151441c0290f42904c42070358003a5000c12810800440d0341760000071101e0442c072a1058a040c0604000d11b503166400200180c1050306c3c0200c41d12590306000d12 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 181306214 1250 181304964 181304987
    0x703020a0e0a06020c010c0507081005011e030203071a040504020a0f020d0905100c1106040b0a180b030114010e03030c0102090f181609080d0e04050601110c041d031207 74
    0x540c01c10140e4038220b0007941d01c5d0b082480c15414000681c00b20018010140480d10082509400380c0340b16002203044c8000030b2109008072040d5001d242200200c01e60310b28010000d89074080c00920302c06040c0410504072401440b901c139062001000301044c07588030744c0003901400f020b90b2520360014021200207803c03c0d0824445200300012450100b01d1035403500092a07402c0814201620501413070b01f4108a00c4840005140c0c00407000200095400040c00081c600000541e888940340b00b00201405055a018031801c2c0b41c510003440144101c0e488a08108100c688c141041179500030242c0100b07045030042c140f511311695010030303188280d0400c80130500e40c6401c1110251145000020000030081025107240708410410240c258103034060030004020b0301111040724008020300e80d000b8490002520001e00580c00e100105981d5402810401c42044103240981021030303180092200402c3c201d03040c28940c40d0500c0f4160411001440240402c00c0d07a842c41410500c5c060074040c000100c100d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 181307464 1250 181306214 181306219
    0x80702121609020901050d060f05090108070f0302060c0309130609060905010b0a0e01110a060614030f0d03181e0303140f1f091d010b120c060915030703020a0e 70
    0x1031880128514800740c404055814049006848150b0030004845501a5191101d812031a10001141c6180e03880340020448400304c0340d92810b6070700d84c00b0907601c44001c1e2080900403a980b800502c014900403000d00b299001070000c036403c0400d68070000c5c030a0b02c1c2c0c01e522611030b29655035060044000e10b0003500702501920f1400e001c6940750440c0d107112032080e002c0781403c000c0003404410003680315503041c0040b414180c0c212002e20b6498181034008041034802c400841060071800e80340c9050216400c4511780788603019003030380d20b0304903015009001d10000d01150514501c1c0c0140c0012045040c140c82d44c2c850083c40300038024549800b0342207802410540290030407280c1002004402c2018969000140c01c0c0c01100c64103000d000f00032044404d41110ba020703424190240001c0d2403038030348c040d440c0190364002e0285485410500a420111051844543d00b00652142d0181421001050390340ca0143c9031102c50b800c8042c50101d1508103441001c0029000910420941d500c11105162600304 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 181308714 1250 181307464 181307473
    0x100c05010c181706061c0206040b0a1803080d09230109050105010b07080412050304050d0b060135060d0204020c15070327050a02090108010b0925110a050a08070212 72
    0x140c040f4640e0350b0340c0082006216141c0c1500001c21182d41c9003450440580c050422600c858459141c00c105030015086140010301c9210a440040321058108040300d8002d013100f4504440c418074800609488101580d198115160b804440948003407058003680e94a0000210413100745081801e440c0b040e07200048906040c4011008681c542c07046070120346c0c41d0130507500c1804c40c3e8038005055000740d9008540c0105812550030601480d507110b00d108203030903a00c215a100d0900c1120ba02074001c00c01150300b400102d2980740d8a12440c4100e50f42200c0024100881100a45e0005050380d100d12550f40d40c9411020ba046925480c101109411416504040c44082c8185030f92143d41e280c10040d100c41c80d0b03010f420b070744244502070105205081d00681181e0355580c485003104c0c0a040c4911086000d805002c00095101c0411305a0b07560700024402420038a401c552000c9407c50011501400f45015840000c0e001881c10406003000328403a88590351144014010448640e03208190074489421 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 181309964 1250 181308714 181308749
    0x30f01020a02030405010f0212070606080d0804030f03020705070323060709051e010e0901150f05030906041202070e070314060d0218070c06050903040918050c100c05010c18 76
    0x10048156020303101c080c641f81c6028a40e600c0124603081e00d009498022440c0000e02005204591700004241c50708a81100c03503202c6089021100e4507030031180031b80050040103c0e000d0241c481e400409429002d4011140000d449444007124040544070388400c0d5404a480c00e80441401d01503175900031140c0c140b0000c010314020100303d03c3c16a110b4802040003091201c11040d030300680121000d4100940048800d43c0c64509185414040d032000d034020950f0300d060040043d100388112486864624060005034580c9c2d034404801754540c0394140151300403c09d01140c0c60b00c5101d04603100d02c4940d9808540781c909580d030b0140200c400340030702d4020444041b843d005070b110081000d00203c444600020035903034005007110001c2401c0002008a418041808003021001025109440b40f0800c01c2000030044a55030040ba07003100170003003450700062100442803401400c104440092810038640141a541d50642154918070804001c1240c500f01d0140009d040d2581d000607051803003c524010b40d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 181311214 1250 181309964 181309967
    0x11203020c04090c082e15031211030c010204060305070809061b0903030f04051519030f020f0a0f1223040c031e0b0c0f09060304050a020a060905030f01020a 69
    0x744081c0700c9000390788514549080003c0444044000d201c008150b921040d244c400c0e8488900c0760b40701c3c000c02103810724804105160075100300c0300d0312030000d181c00000701d2455940076403802c80e00340300c9001e000864000d070140c04001e00090500c0034240e4001a521800c0c00740260440c0e0016000d0030400c050441004609d0000149903500002941c01206503020207541920091069452a0340c05000c003094052400a1603005042528401c5441890050b02105005528050400340440c40c2c03040c45550f4100714001c4c0c0c41175502d01c221601c0985000b05424101c0c0003580f10340980710029a03400c5040000fa40d2082000142d016041000c1c0801d5a0484082e0140758509156214a41403400443d08001107010700c034008541c0410b000d00750f40800601c003000744903006400c1d81ca0012203c002140d00701c1040c122240d440c0d00016050420860f5024050384c1d401c000c00c1201c031445044843d00141c0e5480ac4244001d001550b1600d4126051505140c14241000c06c0500d50368014000c4100c100d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 181312464 1250 181311214 181311223
    0x20406050d180b0703020705071a040303020c040225080f04030b010504050a050c04140105040f09060f0f050619030b09360601120305120903070201090527060301140a0e0601120302 79
    0x4d8551030003589400d01c1d410f1150034030b105540069560001981c140382007802036000b0748101c2c0c1c0a6002d6505004156050001360300ca580c407810000d15240719143d100000920715800118003507021139007002d140200303022090f48982c1043c0c0384040083c004101c1031905014841e030200d0010303010f11041c1484004400940183e00031030380311102125400340141d1146c400d80e0006c3c40c2901184040380d556160000080c0341d00d0140030128640c041000c541c0500141c03034001101c02c0601305d1481c003041d025070b0000c682c3c007001d0300710100b42d198140d05202e0b98581c0c034194001c840c0b02214440d900d110702c11002c80703c03140d100710607070080755220651003440003c200981103c07072085210f40a0119854211014443c0b152901c0d504d542d088148a0390007000006461094800e0300c40e080115160b0081116240d0072030440c4c103e01d4804030100755640c43c4594443d4100d03501a0020440b8000008a04c41d240b008450200d00c0720782d154a4034030711035400c201040c018000080c40c60f0707540019441c000d480c4c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 181313714 1250 181312464 181312471
    0x6070c02280b0c0a080304080c060610090605090a08032b0b130c140a1106061e10030e07031a0c0c0a0803151f031103070c0f06020904020406050d180b 66
    0x14010104803442140301c244804134401d580801c3c102d942e858240380c04a00c9400c0744020507014461b540000304141041000102400c07600d0315510f40c0103140650072901640440092500449402400660080e0400280040030b410409505460210480784401c0c40c0d001400e83c00400d04112134181c940c0c403241410001c51640030004120300714940f00a440c45001240c541401e00e0001440eaa0703034035404002e0700d403c64102d000303680032512807104020350144024210014540403c1d1038100c01d00c0d003994070500341c0b03d460a020a0400e02d0000080c1094105c1e4810b49400322820401103001c01c200c4103171036202c0318a001490a01903100349540da180c058100003800c0000c004003003a40c00e070283c3c4402c411090010100704012001d54021014805841540302c0424100801407078030031882420740c0e1007406a561404001000c0c3d494000c0c01e5440c00c4000d980d40b590030464a240341c2c9a034001040500655207030b883e99921038024920071140c2c4d00c2e402e9404640c00380303074450001d6807405100d0780 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 181314964 1250 181313714 181313729
    0x30a14071e110c06070b01030b0105010305040b0a0905070510050406110703080a0518060301090b120d1b0303110c010902011107150818070303080a06080105091c090806070c0228 78
    0x40c599140941c451400c800035540f0b0f0750248001c41c0140030481c0300845070741030342e108130103444440e40d84400560030380e034095500514104d000c00005801101e164441000340e8011011180c0e01ca6072480802e44401340c400241001401c001003e104087d080103410f85044529001480b80c0d619640700c1d16443d01840700c094040240002e440000c0f030620810000c2c0654000f80a282c2d40c2d48d50703242c0000100011103405014001a001c0211500c8011880030181601c81c1c50f82d00b06040900d403145013003417035000f0840c1403568a207086001002190081c100030702a103c000500c1c0c0d1824000500308800382d102c10f0700c0641c450a41070000b50000302402c4900001340c10902d001e0b854907146070344000c08448103000b551044020000515505c6140b0300d0040c0b80800d0200092902c8910460036a13400725044e40d42e6a00006000d8045000548003c20705045071400c880819200c1002e541080030540710100001c400c000d074101585040b55a0854031280726a00825400199041c442d0251483c425901c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 181316214 1250 181314964 181314977
    0x3030306060d112101030606060512010e0703020c060108070e1303020c100306030f0b0105010e03010902011b050c0a3308040215160308011509030f060506040b06030a14071e 76
    0xb031600a02c410303660000b0a159418082e11001303404110b0042091100361403150515000061050144049414141040416500320303802d00c41d030801e01c840060001e8040541c200700340083c0d40700500c00f09000e07004da0310280c00d00c14581b4865400854000c1c1c1001000302c83c1d0090980000e070005058a100803017541c04995001004406400030301c010352001c3d2507020121080003c101000403007a05882091300ca05c0100460035052500b00c0b904884000d000c2501d03850400300980d803d00150202a200e581201e02200c003e001050805031140d004d0b44031081c0d074900110f0717007040c0e840c009031501c1d2442d04041c0c218810560020017070300018202a01602000c48540307070351104003040703944510041c050054151014500105a503509100d204401100103070741024440c800c0c03503a241281d80041003040c0c0e01089071a21001401c01030096540b09555103480030054564070061072044480e100002110740498540e1105440000c14207c10440b600b10140c2d03100820100c10314150b0018500764 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 181317464 1250 181316214 181316231
    0xf010e03120a27030f02010f020901020c010302070c121208160c08030604140106210509030301230a0324060503101505060403080406020d0c020d080a0e12061503030306060d 76
    0x70010011503403c20f03040e0543c0d82d003141c01c0c9034010b4000c012502190340204101204810340004030b01a00d6a0b060061704055001c0d049980300e50050010075010b41404d40186940d2409100813814881007110240742460b0500c1e6881e8020019075800008a01c10640c41d12503030000034055040ba8000030711115011001c9205a1560b500085020710f13044a409515611500c000e044003480d2500392810800390441e22a44000301d000341070003000d11800031803e603400d1101d6000030b000d140c600c44407a128450901400e03940d64240007001140100c002c05280f80b8900010400d040104240c8040981000f50811540e01c0000300401400180e06c0000380e4a206101003001850055200355800300c400304c0d011080c8840b200007403045800513002c070395129100b80e006030f40c0d52100ca07002a500c50400d07020386000c540c0200003003075072801d03920b062040040da10380018220910300e00c2e800c00b558400c1003002014450721240031f0321035008070011819460075100017101485145010800d0b40c2c1c80b105038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 181318714 1250 181317464 181317491
    0x30c050702030601030c05030c1503010e070507050610090608010903021e0a060501140a08060702120f160b0a0605060c120d0b060304032606060d050709170f010e03120a 74
    0x9403000540d008003038601c1942d407814403004014032030080e240309001e10110070510389002c01d01509619101c84000e410f50380381201408003032034002c20140900108020440000b01c003800310300c1c41007050212000c03040381080740790f50440300241c210494aa24021613000825000620700040340002034807045208a2010424208001100000c2c110703400d090002c2564804014401c1c02c44609466014429607141c203425030300c1c1e50548904c0007580011084406800594000304030004c0d404a0321440c00c0041e40098100d07104d603550580b4648005c4d01405801c030f10324041d10004203021642c0a09084c10b18a440d51203407000c4464002c20200000c0c00303000b2018a811480b800c40c03006102ca9207038034142c10003401c038282c400d041100210405681000740200806070134001d44000c0e1040d410200c1d0610880001e08001d490a020300001010000d281c0031034038503944185601e8000360480d8000c2c0d81842d400e4556822411880e508240098101c0c840480c4040d0390000000f0004a00001003008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 181319964 1250 181318714 181318717
    0xc192103060906030f0b0c040e0c030606041a030402030d14040504050907050325120b070f0e030106120b060312030c160209070f080708061e220b19030b07030c05 71
    0x4202c24a5003080b1000052002060705c0700e00d040d014940715540b544d120b40316000e4031300c202e00503298129003c401140c074104101c80550341c080310290010349050307124504000248000e58154000c6c071000800c02c0b08506041c0180034504c0d0103800c15014504080b00b000c0340e00e004074043d42c0d02443e518000543c900c00d0070000c0500414024003900c211142014207009101d034607100d0322480e0000050000f07441e862001c0301402c40c5810040803c9036071510081281d48100a00030702c401c00a840c000301041d030f41c083c802c86006042d10450148241140c0c5040284000001e04161194000b0800c0c80344402104088a9008500b1001607594820813900d0100540e031281c806500540d40804201080b50003003c05140c500c00b58942100c59075802c04c0455401c482240d07079641003844024071040c1202c40d5072008000b0600101010303034460038581503880c1e034410b40504c2942140c482074402c1031801c10350050119407410444802140e03003035440c1c401480030054401030406a9445644c009280300d0030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 181321214 1250 181319964 181319969
    0x9010509210601030b0f130602031306060f0503011a03060103021c0c03110f040c0c140a05120304030f020d0207030305032d010f0b07020906150910050c19210306 71
    0x110071819441101403980c0c0d56002d000484c0c02504220110310240404c55055106000d901c4800003090071503520310010350000740103200303c02a102d0740000050800d0041d02d0180007811140d104103031a040800d801d4501da12124545030b1b0403010480826200803a865041da0b4066401c00444545000c4900d01c1e440c003040c0c0075051050480000c82040700c141c900d12030380481226190210800c5c82c041208035041802c40c1d10114880e0805000050b1100542c0000d8801074415220410007903280d060170003100d0500d000c802c20000081108164002c0450880020306200a010300460b10b88040d50f07070096800040e061100200025603010000421811040301d081d141002c035903002a200300d1741180c03c0c0109200308040313100101702102c2003c26240c1380d54000740a1000c6894800034407407203d00c240d10002e48010f0810246040b901c2d800c1c2828903001c015501c50381e40384510700d44a4140544500b000e102039200000d41c00125a100c40d0610400ba0350b0b0304486226450000706400804096 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 181322464 1250 181321214 181321249
    0xf140d080a080402010e12030901110c0607080d060e0c0f0c0102090a06030f0e0d090302041a030a0b011e03020a0b0d06081c0e06030f180c0a030b0114041109010509 72
    0x1c0d41d8100650301406580c010740c800c0c0c03503107021101480300700141ca0000440804a0b603106100e0001698429141100b03114114804d0341d482c8500f01e00450019403140105486528000400c0b4910b0003a510401d40203003281c034040e600e82e06250784890218070440c0342c06070310701c2c10200c1d5102207101e0a50444840a100810b00160950385107000742c0a020025150124945004a030701d104440204900c04494416030320000d000c0e0442e420400181222042d0751001d480c02c024210080c4c408000700d1300031500654440b01e80350b140081c1d40a113600310710241a1071074003100e010001070300c481c95075038213482c4450f0540c3d4503407501002120041c00f00703a103d101c451081496040000c4500e0a800039901081e0392103a4003240c0d000c00303000032840280d0300e0340c1480c14803c0001e0003034072012400380c881c400450282d0348855101c100051a07103001e6001501c0c5845001e0040264224000c942219184191004d1150101490086045010b4007030380780d061010001e0750b8095030303580c0100c4d001c20301c003d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 181323714 1250 181322464 181322467
    0xf02010f0614010329011110050708060306011a030636090f07080c040513080c100506040c0c03110c03061014010207030804050103020a1403090a0605100f140d08 71
    0x114425800ca2a2000342c03110301113403400030b80c0b0003001959014039654404200c285242421039500441d03040c81c0b440c640c0c0426019030305a256411001d40203690003190103a171502c40905188040604065060744030107010b0502c0c0004041102506080d246c0c44a01260310b00104402c04c014598100605410401c845400740d55080a10042c001014050903001c0c0440b54400d6010000b140c0e20364450140d5030b2140d00040390f0058a282039003000303606c01407070702d40c210605045661712801c03500704d10301c001c840e43c002600c000010900b40c882e1541c0602d08450a009614280501030050007a184021301004080320b80081804001c005040303403071001508039030b80d03464800081c1c03e8520071801a05605038802001550561001030a1420340c1d0b0001010391030903141c00c0041d0300a62103a0a0003051000c1440020100d04040000e14840d61070107010301000c1c034413860400c0c21601d006004500501114005000840c0500300d9142950f0058124200c25074003100084c00f4089e001c41300901c0c0420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 181324964 1250 181323714 181323719
    0x1e010305060409050a0f140a081209010204080a06020405040c05030f040f05030c0a030509040b0a03020306010e060f06040602060403080a020c0309012601060c03020609120919030803100e0a0b03030a0f02010f06 92
    0x100b1b1035180304118080d403400e20004080300c0e586502d407024a0400751100d401840103a5003005010243e6810080c5c4100040c130b016a1003074054100f1400301d4042e1845940807600304880d0030540034403481000e85182082c07440c40c02d10031541030f00384050b001801401540040b1000c0103801c004940117603031010102c1d10100344514004129a01028419003d181040e0100e4120f0801050340d000340d0380c2c01400740050381e080040300d051440d0b00401c401c3e44107019003c0b2039015220030380288050007040e4094042d0745000d08000e450040050451a413480c0304004c10f091506010080d59200d00c0c00b407800d46052070391032042c0015045241e0120407200144000000c226811440071140d10b031090702640e4155440343d094580b19880612442c61840040051400c10320340700e43c10f100c1c50700c1402c0c1c41e40450354907521500016081124511511807810400b80400600389011540c46040b10b4014071a00010f040801d1f1a4098007040c9014000d20200e0890180d000b9004080e00c0d8880c5101040f0855 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 181326214 1250 181324964 181324973
    0x112060c09030c1806050303030702190606050d030903121107050f040902040e011d0f1024062a02130b01050c030d0207120201020306010c1415090c03010b1e010305060409050a 77
    0x81c106105440520303045d40083c071400c0c04015030788285019006031001102d48420140150003e1008981d0306071360b00000300c1c0d01d42d03403486002c0c0c04500942d5020340003400d6180100d0427075050902601841020180c0701c240000000741c820580c1ca0a958150a0780d60700c00c0454041c11503402d000f03501c1403e20301b07680c101440551104032032551100c958862400c0e031001190b11212511505500c80d002000c0f42d1072208901e8000340e086401c0d81c2c40c441c103c40d011040401900c091908020006080c102c5c5151400d0303c0081c0c070701c2c1c62021510090180c40c2065002a81d54514100403489203501c0d452705d45a541e0140302510b040811010a480e039803018851440000e6001e03102c08c403038114403010002d0500d4814401d6a01c81d0700d068585075a45489600d0364482d14204501c00d515922800030020403280348124164000d403550002404e69001c8002010700b55a22a900d880c05400c103c0c03d603004680494030b128180d0442030070002a1503ca40c0013040c0617000300e01000d01103210340d440e50004c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 181327464 1250 181326214 181326239
    0x30f0608070329010b09090c1b0606030d050c03070b090a050a06020703020105010605040315050c09190f08120a0f0201090b040809090108030f0a030506031006080307030f080112060c09030c 83
    0x444482010b80c900c00354100002c890f500707010345422400144910005070800e08400d076041121550414240103482021075900c02820321490f00a0700403506000060600700424034150300305040281c205907840024596074080c0780009007010307140d01d000c86e0340c07500203010b44000341d03800c4415200324140905058000e94000c001c100c005601c7e0a00005141c0d11620a84d825694802c4c0c80075000389030441d02c040030740000390900000c0c0f0301c10031000f609179a5600c00d9159007500074011500091130003002c0b0f5030b0201281d20885160700081070b00c84901d080482140c1940310301c0e0500c0710088501e890100d00502d00c48000400703502409081c030023404000d00c080d141c61001140e07002000d82c0c0b0780048035142d00a81640c918080300500c00c0b00c130134500a41169602c071402804644001c131009104600740c0d41154800e16191300300142103814036901601031940c1e5030040c18030f0032155142a20b88180200c940ca0b014043e15030f00d80440418910404e40380000319000b1a01710460340d200d802c0340048 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 181328714 1250 181327464 181327493
    0x40606120302030406170709060c1703100612020a091e050a0906180c020303011203050c0a0f1a060312090402070b0114031006051305090a05012307180501030f06080703 74
    0x204025000d1b102403181c940a036a03100c1c0d0040e603240c00b54a840c0540540d2003040c028021215490a9203c40120729510f90141d8403400c6e00901040300c907132500340e000d4400d03c0006845941d45004000702d5001d0b0f90405c41e440c040340c00841e0700da0284800d4100202c03d038100c070740043c0d6100550440014200065802c00010b940e00c02070203158002040e0003c02c1182c1d071045542d0003580040c0010091022030000050f01540a410304900e4450f038641d045040410310748045540701803000340302d018401208441c01110042e0b038442d07400c505001e0f0010382c0c1c803001d15518100c104400070300041d00c1e03203c940598510380d138899601080d0f561120a26000c00b451910001e000c3d102e02d0a041c104034034a0300541c0d00b29400070306000e104500071518a0041d040050069400e446000507000018409104014448034400c2801c441101c411040e04031025000e4012002c008100c4214644a19100b404074201c0e142403c0001d051011644600050131082d400302031107006000000007030200560b1204e00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 181329964 1250 181328714 181328717
    0x1e1c0603020f01050309070b2b0c0e0a0b04030b04060e0319020c0303070803060906010203041a1e0a120921020a051c020a12030912050702090a050105030a0605040606120302030406 79
    0x41e2400b1a0300111018001101c030064a94040d0004000b40c0c000b1700020603120b200c40e520100d580510100c00c0181c8048008010027040d518001031100075031001800d645040e003200c034080210710b0308800022a0045000103880c0401003001b280802003107901800c2880e03a08000e50741c4600080d001c40035100305104541300540070b280540000b501d4040110b4440d5540907841501b162102c100340011040028035490561100700000f1a00320381c406482155401c0c14607140382d98040c4c040341090415003a0440c0c0100080c107011000ea02604114403801c280d40b64600080c520b0200d0030a400803601c24801c2c04403c001e86110800f040b940421140102402101100d2000041020340600300071100041001038004410310000a45d80e0b24860410810700c0c50003003201c802d19241e42500310703032070360509c00840c074001262400c505040b52119840140e011040100350303d841c01194803104440c90040038195664001420410702d41d00c020090000c4d90003213803018080c0d1401035071704d074464000d420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 181331214 1250 181329964 181329979
    0xf06020711010f020a03030b06070b0907090b1804030f0c021512090703050c090403020114070323060603060607020d12030b030f0105040203030a121b020705180c1e1c060302 76
    0x1e0654080e95503040803840d43c0d40144590404c2c0d8400f10000d1511000700d41e840328081000c40041450b4100044c040c00202019182c0380b49070042604c11101c07001c028500601d080f0038800c400d601c2a025a07139125030981070000c2524509142111035000906c002980400995000500d114186000d805e02c1001034807100e0342074840902660b51121507100052150b800700010f456107082c001241500302c2c0c824000443c603940120b19603c49000f00711100c0b00040e43d910001a82140385002c1c4601500e040039a209140c20080c0220308a4400100010f000d400c001a4078000c40d110a4003100740682c0052511680050300b240c014003910449110038400c2c400e0303c0d1040840300c13042c0704050040b03a000300107518052840d50296100d1441804d9a107a440d51b505842140019144942c042040d080e4058090b16040c0700420419482846000c40e060104408122585038000200d0740c0e1101840d020410350703117400202c00101d00c074804040301d00304454000e00c0d00720210b80d002042520b10031100340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 181332464 1250 181331214 181331243
    0xc03020c010b01050c100207020118060c0227070509010e12071403060c033c010812040b0906070c26010b040b010503060d02041815060b070f0602030601020304030f060207 75
    0x11113050280715030000d400d800000b03a00300b103550076034018480c492042c10201c000406040c0364580f0784101b075207e030001c01c01881403901180703401e070f075038514224511146004d0065030010b80141c9400003003074003007070000000303001da8244c0c092900c1d0980301500801107180440794000c0c094031040c507486011104001040c0d00ca050b89808641c0703038442c0c1100d4100030304550f20300303041801e00c4012585e03071880c0090300005c550b2200c13100c034142800b4210141c407240c80707940340c03440080c90f00d882d40c44407070119442031205201c007d00380c800300e40e00c141046075865103500d601d081400003410f40341c2c402d20407190420a000d04105030804651041d0030a1402080346141d460148415903005040042c0042c004100107101c0d071030710b101d03868081800940001520070b40310384a0005620441e109480c5902c038207411410100c1d0790301484000c0c1c541d002426003031500c6a61920454144104010040e940100000d06980d20803c185c40003140c220103054000c06160404000a62002c4000d0380c80244c40b4000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 181333714 1250 181332464 181332467
    0x90c030106080f19120f03020f0c0d0809030301050a1e09140a0c020d0e090a0615020109020306100e01180f110c0c0405010b0f130b07141c12020a120c03020c010b01 72
    0x19860341240780802d0584c05c00d01d0444090554083c5802456400c0c4070300c4075007074101405031161121510060a2240400300041c0c0b50741401000003401b940304000600154454038005400c4820085c184000000c0c9043c076011560903540102c80703090701c0c0c649100ca27000a1b00705420300920504004000440c0c0d4a80126240c511128200020810184c0410828104078010951102d49000300280c41d036250030700d0703500e401d00070a44680180e460304008825031070f040c0308080d0002924500d04002502e0255014610b520500c10032444424507600041c00c58295041081d50b0800000d040002c000c040b0180c035080d4010b000c040c00144035007509642c4905140c491981070361008242c0c0b508102070710801040c140d0207207090030101b00c020200010300c045404054014a40706d03078501c81c092a01001c0d10340c030708085c080343c0c500310ba1481d007010054603030402011703140781d01e0b5880c0c00740e51410124000c2d260310b9030f52113541554900e002d1807140300d1a49a406840c80302116030080c800d10510400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 181334964 1250 181333714 181333753
    0x2120a05030a110a0501050907051c021f020a0506040503030a050a0209030c120f1605040c020d14090d1406070806030102070c05190b0409020d110c15090c030106080f 73
    0x1008006500402840d035080340141100c0d080c00f040107003100d03542c507025603030301e030a5410948070a003aa902c0404103201d1890041d41c4e28000d1840968005144000f580005041140b41c040302101c0e507917100e01080d0001c2c4240708a10703070550003d003100c509041518040d5079952040740c1c210300452402c40031540b014498000c03203203d01d000500800309090410704000416146052401c100c1c4542c42c4400c00c1d102052107007450168464403800d40051500082c8000d4801c0103036078408541004100002d0759400c0001c00c42500031201c0380300e4450084401150300303803881d02400b4140c1c001c100030035106c0764800200d00d4030520a950703561409444880c289400c2c0d00502ca03000780b65582c0340906100504020f0300d07201d05026100064217031641c0c1e61036075001c542c0c0160824640340da0000381c40c3c907101505024440e015619551803c0c81c154074194461748030080c0d10481c11102d20b115020940e980b104200001d540b0b03070010000c0040c07983d14001655161031074980c000ba50700895040014038030340c020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 181336214 1250 181334964 181334983
    0x304050c03010b0f0d020112020415030902030d0804030c030c081303060c0914030d050f0f030108030c0115030c150c02150901080906101a0705070b03040201080619090b0f1c0212 78
    0x4044007645d04e05540192600c008100030100810340c24080001c001940f908035000d00881503c00080340c081d9401810700f8000c911078150700340204201401f0000f82d000050b200081d401d03151880403441e071803401c0700c41c9100d4104220342c0c0704076195000c0240082ca40c801c490340c01482e00c0c0c80c1c0c40580d440c600980913950309240d455254124038091041c15020314020115141c10310130442c0750825415006001e90000e07080b113003071a8804204038103034000902c2401d6840c410a03132264a014950b5640d40c414055034003411021800000d40c816080d070051700c078042c605074010642c98540d8000a6509541d0300500700c0240001d007040045102a51f0100d140c0340951503078050b0350000e600380404401044021800010111802c00c040f01c0418810f0092102816642032501d50300d061a000041107400c002d000a44642c3c140140482d1120740d04e81028100d82c2c040b28082106848440041d107505002180d440d006007544080c40c1c1c59100d1483e0030700315140300312a015040d070250f41c6016510030610303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 181337464 1250 181336214 181336219
    0x8040617100902071e0503041d010803030402040911040f1e05061005090307150203030a0b03030c0c040506060d0e01020c191e02120318030c060c070311010905060304050c03010b0f 79
    0x80074480c0e42e04a03001044481d02400320020780b003c0b82c01e1640700c00c5a05d1030040d200c1e81c00216040c00314050480b02c0d040d00b06420f411841455042c802c1080e22448040c100074400d90b5030340d003140c00308949030204010042005000b004032a4250207404007428200928100f5940100c00003251881c10741b290364044e41001d0585036240f8245203094800b40d209030406035051040103000540001500c00301044140c1c194041c42d12410400022400e031003a96440314442e4006014030f4dc03204400140100804204540c0401c03133440740c1c40841c0613803182c405917005007420101c8605d8525015001404640c0f09101140c01b480c2c031441d5251039501d20400c006007203440346c14441c041c84e61051504081580000c1200c100e0107013109807945140d00c0b01541e1040e0012006841502d480d0900001040c0e05040d56858a0f2a102c4007442d5280d00e901d01000345aa42d61004414041e44500c10000142001400069807400c0a0910b9075907032582e400854480c2d802d00c0e03008143c9080c075050110310030001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 181338714 1250 181337464 181337491
    0x30f0603080306090c12070e010201060f030203060406050a0e010608030405030c040902061603090510120b010f020706050309010917030109200702120f100e0606060406020c090c0d02030408040617 86
    0x10507080249a1300f0140001840f20002e0100e8101e0000b070114687c0102410745890300f022113100300190a40d60306520212003100404420070268402240c050350003030744448000b441d07603500840e01d4001c20014039806120f6180400101300040000010000e6410880490b513a440050003080295884000300030b4000c401807001d141440320305100012614400e091101c01c90f507e8901082c00341215500e40c1e000606410301c80031010a003071150001358078081c600543e000c26002c20182d07032100030744110710070003a002000030092582984072042040d808004403080c4916100c0f82d501c035030420b0080300380c11803510f4442d400c80c000081e0348450245050005a080241c1d075003c100c01c80002e00d482400303500980d4112100408180110038059001100000e01c6000f29040315107403007401440c20380110020442409080c0e0001081145d403201100e601c0a15038034103020342d00768020303513107001a040d0000c030600c003c02408602030001c0d100c031550f035610030015a158518100c2d20a80d112502101d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 181339964 1250 181338714 181338721
    0x6070c0b0a05060a030f030302040b0a0c0b181207140a06050f100f0e0703020d1409152401020307060c0512130b36031206030d080f04020d050609010c030f06030803 72
    0x10004607506c0c1c0180a0700380141069a20452200540e21014840000509a81d4000c00700100348803150703000080050300e10f0000c442001c5803682d076800304c40d061000b60800b05000c0100102c2c5000c0018020b03e04055500c0c440d12490720358041c20707065030750006034044040090301c1d0440e540b84407000c03100c0580403042401c1c68a241300f115440090090000c2507020419000100e480d030180c007100c90000c60300201300f0710341301c400a41400d41d0780002c060200505070034891521111341c90b03021178800c80326001d260150503c0050f0310710300c954000144054101091004c51030341143c00750401400780080c0394030303d0366030241d0a1100d02d12903100030203800c68600450400700726846141c00380244103050101203200080202c0c55000b403c9403c540c20352002030385000c4840f0f403920750760300041d0503001005440b02100c80640b680c2d000520a00d841641540080e040d5070781c0d01e001100c025080410f80d030441c100b20003018045c100c140c80d02d10109082100e812011050751144804498118200d03508585 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 181341214 1250 181339964 181339973
    0x720060a02031806090a060f020403170d02070515040b0f070c110406270c05131205010f02030a0c020705090903040e10030203032b02070f0f1406070c0b0a05060a03 72
    0x40024100c0603030300d881c200381e1803c64801084242d0080405400912952000c2e2030400d00360341c26001c1c819003490050004000050103c1c200c405284211406191140050070030710300240203076440a403040c4180703121070000c4d0f03100b81440c0d4080d500031202d07616075a68125505100c00c0080c2d64480000d0ba5996516001c03400d000c00070303503848800400c081000e6a88001e82c84c010700c64041112200c0b100d001c1c0317807004100c8a1140c50300349100760500c0c0381010f07090040346080d00c01380d21603411101110008142004001e40c0580d00c2070125200c21512404c0c6454000020810000c550015104201020440d403070701e500901e00c14030305980290301d09814800c00d402d801d900504004a4021140302c0400141d9090000e0f04c020b40180118100c09800c00b101c80411545080f8800f981d14410895030010408000ca08041c50f078014020f14042e92040c031b00441652425010800a40610030030b100c1003541c4600d036030411501901000b812170f251120058101d0300e09413001c07070307018150031010000078 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 181342464 1250 181341214 181341217
    0x130b13050a0c170c0405040807020112020d05010f03061821110304031b060e06070b0c1903061e120b0402011106010f1508040308040209100801020c060720060a02 71
    0xa00c1501a100d21214654078a15110780b140c2000d140c100d280207a05050180400500c09680c104840900582c00e06440b013101c28858100003904001c0b59201404030701c0c841e90100e0f82041c00c000d03c204120340e500c0e803140c64400c48a0008031219414140980b00500721100280507564000c41000b42c0045c0d07450965541b4a900400b0b035052282e0b00400c240c0c6c450051002e40005c501480240c0803046184110b20000a8590880003c1c030402a0740881e081c0c840d00140e031905540025854026216012440240d000d88000190807040092542000d25496009401121203803d500d00c450510200140055501c90061869000100c016200070850950780c2c140c0140c0181030100c0c0101c481d211460400d07409070403441910242c80c0040008903041021252041200c2c40c04180380c0c00e02d640c0003801040d0150020707218910a02c0031078071519074550074130000d0050b48000c55880218050349515054101d030b280b800b15000140540d01d48070301a4690616118841c064465642c80c0d4010030300a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 181343714 1250 181342464 181342501
    0x11060f01180b060c0a0b01080f120d06050d030e040605040b0f090a0b0607030804030210050903271306140a12150212070804020a08120405120a020d0c0e130b 69
    0x3001d40342c0001d08a207848000040802c03900e58406880f140859052258610b04180e1000c0282d41c0a20307248018a000881c0804034141d03c1c1411581c3c54180c09403110280440d50441c44d07000020b000a14101600a170b0003190012081c0c2c2d040c0805a580c0d42000101c41c0d219001c0c030342048008011138923600e070058140d6030003024400000b03401c10804020400300d07000268200c000c01c034203009000a150f01041460a0031030b04140901141c54036494064590180310204007020b6614280d4009040d20f101c3e03001c405083c00b50010100b038a21411150241407140b0880490142d940381100c02424118500c800741c0c0c840c01180040002e45aa8050441c00c000c82101c62180d03080c0190701079912981401c1707014450903515800e4609240c0100032502e8025800103603103a004400c2c180350180c443d425502140c008580c40704940507040c01c141e00707043d18220001c0d4080d44211a40c000c004880d10b00c001a5044000001e00c0c031390310520ba48051000c0014041c00360070b1100d00040d000104614445030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 181344964 1250 181343714 181343759
    0x100323012321030705070909030512060a090c02101802011e0306030f11120d140c07350c01080408090f0406180b19050103051e1611060f01 61
    0x203038a4504200e0004190a440520b01190400190507050201c1001400041c0107170490400c031070034044d900502240304403e113444908d0107034400542d41355681c0d40104003e200c038000070701107207600c2c03d4000d4455610714500402207140070000d8280100c2c8105c0078940740da041e1076003c44910004000f0302ca030702c60020400109501c1c1c0c1c80101c00a01e170f540c2d81d0b04440317110b60101e0000f44290340c10001d0140c0c005003911041d030b11807084118903d82c480015a50260481c0a0a84d1a1249000103080c014140c001e03210344500c544900300240003c01100f42c002001100c64003034004011811a19900c4000c04140010300d844042004102c4c0000180345c500c00081041c42048801c9000c101079801507130050314222a00003e00c00c0440f8540645a04d12100701e403085118003107007003d0303698000180102d904040d6500c001801d000580f80594291040350b542a841d1407a00030b10705d90859a400580d840041c1e1550101100d41e400060303070314080c2d013070b52400208503800c11040c40d149403440707044440b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 181346214 1250 181344964 181344979
    0x1403040906060e090a41040c14060f0d0203060406030b100608060a03020607111c080a1806050313030323090c06030105010503150406051003230123 65
    0x4503500c03103215031801844603441e05600d142c442401c00848100050840c000b0900b0054080001c000d403604a15031a844020031414111b0385012403e019070241440c90800b851440038802400a8551158110340b8480580f0400c07030914014401e10340900a106004160144030780e102405540e0061750340024050300009103c0e41d2038442c41401001520b0718440342c00c3c40d010a209a03a40010a0307540564241c1c0c29509040c035542c0464501d208622010340350340c14a034000c42a903664030aa403400c510300b0540c070f0369004010b400d04144580c800b0265101060f10514441b21040001c0040000c9841d1078507080e08640d01d201c2a42079408040b10b00710209941c0d0566512103c40740d828083c007023050103c5002e03103403803c1000c040c40e00b1045005140b1030700c410301c0100100e80e0f0000490344e0084d41c2d500c0a903000c02001c4040380180105410889e4841564100c0c070076003d505511800c0108500c030000d032081007801203030010f4800d003030040030211003241c4000200302d0000c40e10881e00d00009131015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 181347464 1250 181346214 181346219
    0x14060f031501120c08060109091104050d0c03061514030613141c09090b04050f1909080d0b040b0409020a060c0804050d060209030d0207141e040e030301050109081504140304 76
    0x41c800c03134118007481c0c0b0100e2400340600c441c0d564001034100103480c4600040000c1e0320b41c008014080d0145105140c401d10392421003108204118410000645d8808801c1c821414401204502420a40500100c00b0010301404441d4607000070100e00441d1807141064140c500d9480315070303047d0030305c01100b011031040c104164489122010442140251a501c0a10f014106840403040d2404810018401c81c00c04051040e4070b110f1070100c2d60040b203940110816201e0152092026103800e800103028810003040e410355040e403035001464940350450b000c200260a400c03c00003140d52440d0040e41103a006541441464043c0181104003802a610541000e03540c000056407503a0503041100c0c016000b003580c20450608020f2102040414009400f041d400c204038110b4a950104080c1c0c880c80503000408202013031411004807018020740305111461005414a990398403c2c441c50f400240780c1c1c0b00000c0c00c024082520403111011040c440c44584039900c81c0010103d111061904502040000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 181348714 1250 181347464 181347497
    0x909060d0519050f0706020601030c060503060d0614040605010b03092503170405011808030d20070317010501020307020d0b060f090103050109150519090309051914060f031501 77
    0x480c91101c0c4a80018000c84283c0e0200c00e01303185c00c6500c514155070041d00144005110300154600380e0704c03507281941c0c880da03031040015500014000040e241a280100d0b02184484101d940361196001c1e90702842a030740c3ea02032880300391008440c982096000022a00c80c0d800c41d4140302d0b5401c14450100d03201c995241d4591940c54002171013048aa01c030002020030945d40c0044061a4099803136141c401114a0a09007586074441d40420a100380d03641c0c0310201640c0c64000e02c21401c0580ca95105844a039246006000346a00040783c0805921800000400350b2000044405d003603400b0f01407a084994607035420140d080702501e1941d1009074280307046140d072207017903c06000f14040e10002c07501c240c05040c0010354080100c94074800909007810402c2010b00c4500b2650b1210403e0f2000610007064182114002000d4001560104000791280038120419408100380c50b0100302182030220664100400707442a100304100c03c00341840060401e108418101c03845a506051a54070058203102 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 181349964 1250 181348714 181348753
    0x150a0c0f080c0f150604021e0309011d0a03031508070515040302100f080f0105090105010c0611030c0d0f06050901151707030e0606090405300c0a02150909060d05 71
    0x82202c0f0f1340c0c031458812500445585010b07411140c203031411407524180008800010f4101541e01c1c0c4841c60000c042501c2c10340940c440311854000003041091208507600f1291150603048050b00087c3c10714992140700482c01d40c040c01181e2170f4500526010b8500000c2c49102c10b04429400d2018105101c000702507120180713905c000a641ba510002480740e03522025024000180092101c02d5100300180000c2e01c95020403815a0802d00700b010100d1540d00d440301c058000203807010b00710300010082c05480d803c540003400d21400c1d501e02c207100c6002101d003001e048030f031030b4401d443d0302031400740040142003c00104c1c2d241003805071410100d20a0310210302d90481e107054500343c000030740d0b652200141c084103210843c0c01101c11107201e4000d003010741300c103565401200c048408185911800745400c0010034000d142090f00401216240d510402c0c1340b070f403034440043c0f00b68042c006640401041c05c1400d412107003900c00040007260759803911010b200c40c4072a0020103c07241e1090f9400008500a04038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 181351214 1250 181349964 181349983
    0x1e0509060a080403110703031218050109080c0d03140403030b06130b040e16080a0c030902030a0c030302060f090a0b0402010903080d090c05010e06070b090c120102030105150a0c0f080c 81
    0x121000d1003403c141c50300800c0d520700e4145030f010642090a00b440065889903002d2244041e407100803030141040411210507041100006001c2c2d8a80341800c0b0030445001c015007007000f0032005580715407490180035400c2e590701103d058800c48003c00005c0c0040e00960180aa0400240c156420845481052101014079411072072194601140c100300c08140103802560003104e105540c4507048c01105d000d044400094680d200c0c0903116200c0c02003c074400e0f80b00c08440c2d1303001003c071750030340c0c8440c1072008149190380030540050044500040250910032030441c05100707010014803105e80e13035031074500c80450040c10803030402030b0b42d91f00003011580c1980134100c046050b000c0000c40d0502441c040070910681e512103030600c01d10030b280056583c2e440d000c0e43c124075013000429000d551034841c900d007400805200070341d111540c41000b00c201341c4c1c154040c5069400a440c050001e045100010341d1a000d425060300c00100075605490020351303e0301c070703c2c0c5005103c2d81686050517840c0132030a003481c2c500f2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 181352464 1250 181351214 181351217
    0x5120312070903060b010309082704060e09150f0c0a030605090c090301050f070c02060904090503030906040303200a030c0c020616020102060a020415140706051302090601030501061e0509060a 84
    0x41d042841800b15505c2409802c2d482401e0800c1061800c0c3c0d10500709002e000c4904c40c440344461140d41e90600154000048d224004100304183c9d502e6100c0226002d0040d0b40d980003500c5807410300841070651921540c0156024400408503944982686155a20220100e401c041e00c0d100c0005607a00c52007a041d016140d00d0040079100c5a100f0181800c464000382940b0003103901d6801c1c824203541050098070840e8043d2006d079510303405000840e0140001c1c04004006100c00000c1000c2c0b1040850001e000f58840c0d034042c0701e5510a2064140c90403880c0c00503d03060002004244031341c3d030182e8000a0074040b1820801c60808040d0001800ba4010188010740000c18000c408215a4184003055008200200441c1400d007802445009015800318500c28444d40c1c0741817000d1686807a0584c0d402c641e00c0102440385217041003200744060a280404c0740100c00b100c006c580c8644c02405107a06172682a07403203400b00422584580e00301d0341482e11803030600000b08410429519003e0080070440d40030f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 181353714 1250 181352464 181352477
    0x80d0c030f0906081803070b0406051b0325030b0307030b07020c0a240c0f0507060e09090a0204051b03041208060303040f05060f0f13080d09030209010512031207 71
    0x1504024042580020340c050420074480000e0003c56080040d880d0010300e0b01941104526a80e0713815440c500c40c42d0005040020854200401c00015810040c403641400320010442c216040790514940000c0c0c0b0a50310007015150301c0f46066154006100c074280c860301d0041021003460000c241003000c6030300705907804011502086040c0b50100108854181e045e5100c0b040c0070f03d0140320311401c03468412030081c00d10300c982c24480310b9481a188114000d401003851030915000b8544030307030394810a10588021811041c0003001c07900d00309090030721036400f00f0080c0501541941c208001020000c203010702e101c504001c0003020f0188400554822031250342440000e5000381400760500c0b81c010652071103940100018058209842400e0084406c251a0b42c1e03203980380500300c1080e80c00b91401403081c00101190300681e240343d60a43c24200e0b0056810745104500c600350440b84809107000103504440840c0c01080941070804603110031402c44400d580c200300e44819500c0c612103065483d400007418 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 181354964 1250 181353714 181353737
    0x61305090c10090302010903120201140106020a03080a11160305160602040302090c0f0706020309010605100f092c0402030c0a030f0c05010f140a02070e101404020a020c1009080d 78
    0x2041441050b59000c24103022040614541c0020111042c40c04018007140013028441e02c03da000f50040c2d00c80110441543c4403035a140e0000941d25940900f00f500002c0da40c1003c5880e4901c00c2c8200200b040d18105d60b00e203010080301041c00204d898150890400000300070700495501c0d007481c0005038038810140941d4440c554010004041000b0f800002100d808211141c284c504010494002652142000d40c4907501c40708604d00500b41c5034030054006182840c00450b0076030103c10340000101e02d80301c0070b4003140c5500905140348040c0c034420380708028604040801303a02c1c44805a0380301d84010201c074041980c40011409410082c1e10840d648141c0c040e255081000302c00d210000780c10700b840c014400804400d0010700700b080154810404140005015a4440c42440b0711406010041710400b0142040104030074468650b1060151081c80042c0b00c801d1882c040c02103c0308001d699000f40609036055040040701c3c076507200c1e903a090010081c00040c0031001406945200b44c015210403d0005d0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 181356214 1250 181354964 181354969
    0x708090138282c040212120406080405010507080c1c0209060d0b03060f0411010f020c0301051501030b0415050910090501060c030e030d0918150b031501090602060a05061305090c 78
    0x740500050f03829464aa407403010003a0b800c0c4000c1e03400f94040352010683c488032a480c50134003c1000d820007000c0320001d4045241c0790844d10085c010780c460802001142d07100402200e0300c2505803004071181030200300d88000000307804000c143e2a08a1040140f030310180300c00040055102d81c01000f00729172520201e810502d0140180307648541d41000c45030852034a6922061002040281541403001c40c0e00b074903602a100304031041c10100054000c00450811841282d00115080c0e2210700090802d60321254038141801064100450303a62141e0186051004016418a0091a650424010340e1000402108902501d80205210340701d0f0785445425040040000100640940c040da209440e00035215034002144401c56a105150011040d1600f22440140c002400c581800030b000000c04110301034001c00441c017801d4601115a003600780040150b4030181b19200d031401503002503001450300c40c10380d040580d0240c0010b1031b540e130302c06a880d030070401c031401900c4440d4664013040750300d0103030f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 181357464 1250 181356214 181356239
    0x80a050d0906150e070512041a1312090e010b030a0905190b0a060b18013c0f081807030204060305031b0c0a0302041e05070809013828 59
    0x11301507016140200e14085102810910540820445c007500710302c000390502c000c000394000074a0501d04500b401e410041504c140000b007801007503c21104040c07083c3e0f5994001d01c0700e0f2044800d4003071018880e0b0f28000d0201d07580d0704020510010262140c4018000a0050025824107035803820252003480580c2088403000c240240002011454800140004034801e4103880c4200740d1682240a078031900401203c000c15580340c1036210850001d140d4001044030a04450701003912410b08080b4844176204075101c00702c0050501c040340245011540102c0d0550014036034140c50b0f0f045510140d6260301050858505602c1968181c0020900e411130b00c0c07041e070304881c482c40c014000708119002c880015075030f280c4501c0f00a120756600d405480340d4001001e9120891404050100020300d081540030300f041e00c0445c2e04500310751820101c2100303140001c1000f04520424501d5185081d4050055a01d0061020183d5072003504081401c90b10407903440d055a0f20780300051000c1083d89804001c2008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 181358714 1250 181357464 181357469
    0x909010b03030415030e0c0f0402211e1b0306240406030e010506010e0108220605090307031214010303080901020c0f1c020102093d0815031504080a050d090615 70
    0x182c2e0090412011a9504d02001c00300c2c02348100c800581d983d902d41020684c005507584d000c503420b4241c1e005c0140402c60b91144416050848010000da1350703034000c9151014200c4400b092003040c1c02c0c800f00e1075a0420340301c2015801004a800201964200c03c40b070403542217030384900c00017034680b078003844506828040e2075000a400e003009a811420708002904460b0004c1281040622108040715500002030b40c01c607800d40c100c03000300700710300b01205030b40e88079404002c00703402065507036440343c0314030b185485401c030600d552401c0280940d003541c0d030403036455001034110300c0d03035640a0082c84c40c0040284201409107254900400b111603940442c106940c1201061900f50391040c4112003080d11201c0c0543c02300401c4144d100c00100d01e1041d220500d1031070391608162034404c05081040f60390002099070003410403200403482d1750302d407034101542c0350943c40084003440e0030680030a0001303030110b025029081407418000c1c02c2180001101307085601e42401590421b4895088081c1001000045000b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 181359964 1250 181358714 181358741
    0x150f0414032e1802090a020f0717040608010f030503040308030714130e060103200a0306030b09010c080a0c0c0b040201020f0124060228080421110108150909010b0303041503 76
    0x3420f240d80000d035144000411a0225a0700000e003111001d080d8400c445040b85e01080041d06801c40300400c001c2078101c0e00805c004100c888001145c0c010803c00e40408907580800254507003429640e4081d103c8d04040e21031760071300005815080040042e0805000402d2100203111809850302401c80c0c00401c0180c504d605062038803a1840c05841c0c9040030742880004600025511003410303034101c000303100c1076001621184041d4180961100d045d044005a103426030f941e0a034584690f605002201c2e0035a499001054550034602c001482e1161015030145c0140165800d50721840011801d40310621105090814131603080c204034101000139101a100502c000e01420040c102907031150030009030840417040e0085410010040c1e000d0880717014107005001100c0d40003401c00c2e109024021110f080b0f4520050203203051095209051540c0b01d54504030004181040740130501981d444040c01c801c100355220951040746441c10401400100709880040c0403c800801c0010100d500501c0d8414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 181361214 1250 181359964 181360001
    0x9080c010b04060b090d1e08030c1309060b0403060507090b04082407170a0f110a110c0a060c0c050402041706011d0a021810020c150f0414032e 63
    0x440e203072200203502c0105980840e00f58080419126517200000f680c0100400148e40041040031070b40c944c034042c0550810307810402d24406d444e101d601c02640c00600460051240c00d1008101040480e0411034010890741020a266501e03881d80c1d48165101e5000801154801e0482000003121606030b05003222210050800c1030030302580003800e19105844c1383d4007945964000c5898031403141d020224070001a4420410700d0001c4079000701541004020801160700450001c44440e00824007030f401083c005e00d44190341e401e1480035140448141070903110617004040224203501e40c2d1005001414521083c80240d0399844109450280160012140750100038850722540451290a0b9041110a4005615521004a40c00352004e860351807551054070803d68112083e004120402e108005840300383c80c1c03098468000c02c291041007041c407400c01c4200400c02281000c03120b16286940018113407008080306060f04801107602e0500d0054060004010798507080940c49450701604e2081c0014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 181362464 1250 181361214 181361227
    0x10305030307050307021612020f100819090b0c04140d0804060c03030e1609051005011e170708010e100302030a020906040b0a0609031115071509080c010b04060b 71
    0x10361039010141100042c4031010003c2026503000f0700c400840790b41440401404180c0e1503142641008002c40240c0c000e80031000d155010b41015019000e0125041c2c4884134140c980ca00404602c2410100d04400c1e107035958038100005041c0101c00d8051700c150324450b07131214100044414000c1102e80700c544140020000c0d040096150015101160b1381401e1040b40b080040c1030550182c801885540c1040c060301c0030340150400300b48032a000382d8900d10010843c81c0d8442c00ea13948103c8040c0103042c0421b0140d10345001c42d208407904420041401e18008082208940710f081c4403417010346001c804940c0ca0401805a40a6072005660040c00310f02c9001c1243d1868011944404101201030300610200f8000740c41c2e51a0740e004000450030281400d11259521500202140c0780d03404200c50300144506030407400d240008403203003001c809017040c51526009e959143c0418111110400c807003a124181403010440b01d030098007000004000100380b44251208000403100e054002011034882404030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 181363714 1250 181362464 181362473
    0x1050916080a050a0207020a0909210e09130b0705071505010f03030c0c0509011d0f1501050d06080307030f030e01050106051603020c060c01020a14430b090c01080103 73
    0x10703540c110049500014043d251a260074001c0c2c862a24081d4008421034000101c15a00e035004604081c082c21040c031154201128210120f10160203460004448803010340e520310304400010f40113640c035000c4103507181e00c9c0d5503461001141180d80700c0c04510082070100138422000c40c922000e14000c0700070415503050240ca0a0340c0d44250002508001c015241c400810a1018081c809890021f040f58a2507a4a401c00da480c1900300620b000003e0451000c180406c034406800d0b07024001d030011204601c1130800c0119000d81041c5540d01e040b94541800041f02c0c0b009000801c1118001d40c3c070791115100604001d0241d074804403a200841c0c1c50304004000e400d9005041d11002000c00c0c042c0c0e510010103080403450008103500d05544000e0001ea0000e402d40154002c008140d0f15031141c0508900700c950340080e0740610440500200035175114500205000c1c03c410700100c120105c094a03103000c1505001c10940d407031b80125903c0d00110b05210101c4010440700400741004d10b00b096003581140c2c0e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 181364964 1250 181363714 181363727
    0x907050a090615030203040602120f1b2106011e0e090702061009020d0b040f0207020f0315040609030c050d120630020105091302040609050103020708091e0a08030301050916 76
    0x9003000c055010007c1406c00940c0d404603203400341d080d9419140c509186001c12038810058454002c1200350b02d5026550f036024109840c60302580054031182c0140d490011110404000c00e820704002d041e480440b1032a0400d1100048001e041d550391005141d0203050145550010f4440404e41d0720407800c0200d02c13042d89140d1401d48101003809030710b5841021030f03c00034007007030381d0950340c00781c1481e003107070740e14101a030143c40681c2c001c5951503a00c5402109140d2102c0344a280d118904038003600260120b03a03141c100c41813244c81f03854030450001a54442c0c6090502401c00b000c009006420381d103980418900402000e00a4900c0c0301100d12800d0368031007a01d08400c000c6002c900d00500004040d07a0180082e0798585101514520714050070b40d100704020740c002e01904000c01c44010001c02e495129100381c0310099403147c40300340b511545d8810480021015a40602ca2400076841c0c28000e840d0b0a4400002f008540b00031503c03541000c08020070351900a0030850842030040707000883c19070084 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 181366214 1250 181364964 181364999
    0x4050a0b0f190f060e18010f0608040515040803061002070506121902030108070e09030a050d020705071a04081b030d0f030902060703090602011425020c090907050a0906 74
    0x19508440a84101c01c220340c1d510303141e480003682000e100c80c0010341a03000361850380d1005084a456083c2a030081020506e03010030300880c081c0038082c2c2d1007440400e00441409030440c1c0544115400c1003c0000403907c41c0804484c1102e0f1101c010003804124203011103010651070302e6001421905043c5808600d060042d240a4404c514201c0003042d6075001c00d80303c5500e03600c0185030a41d03881da110388200b6038404d107902c0b8030741e05c61004c00f00045c034807207022040e82d07000700c000e507185464244d0081911019400c107070010b46950145001c00a00f41e440d400e0f1041d034454104d8111a140da00d00280c40342000c5036943d00142c3c06101c0350b907a2030250b130301268881c6200203030305080e1000d03007104030210700410001c030f002504080c0c0082ea54040c50341040c18202120000e80c000d02250202d41005540440d061b51161030007060f0700403c0c2c403403490010250001580c20301c11103802598000c0010b02d0410f0907100c40505406c15201800181420514103000c0c0c18000740a0000910f094034006040304d104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 181367464 1250 181366214 181366219
    0x2010e12030d020f0c0f0f0609070b030606180d0b10050109030b0a05090f0a0501151202010e1513090209041103090604020405070e120c030f0c0d0f110604080303040204050a0b0f 78
    0x22a00c0c001c200220a864182102001b02c0b04845075840b091907898031071220080e018072400b8005440d80e03600080840644080300d606606640303509060004a1700007034a80d825038103071b080c207401940c0c48410900c052140101203128441c00e042d05044e48850458101604105042c082031000c150204a002d802240031040022030307503034200486007049010b9081d41e2050040340000001c0c4101500507000000f4400070800000d07a9519030b06042e001da414000340420244c050700c210600c2c001c0600400d9203400c131a102d1400313481d103c00030303800c603002c0c0c00c00e010041e401b01d0031540c030341043c3c0300701002541203002316440c4d41000c2060070b5503500000c10007071107551503000146403140714141c054030340a0060b280c01002a40080c81d01e0312030f00d440f012075019101e03000340c503c1034007400116042060300180002e0082c40c0304e912001a401c21f03412065405004003032040c0701036110400100028000355010b1601c1e82418810082a40e0026000c802d1450130620301f801c1300d984009025a514004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 181368714 1250 181367464 181367467
    0xa030b041b03050c01020d0809100c210e0d0201050c03160207090c0c020f060a0903060b04150602030406020c010e090106032a0207080f03040b0f0703030b04090f02010e12030d02 78
    0x11032800c08800d2210401e01c084040031003400204114001035800a115001d8098034000d8003500303000c41d0064012a80030039558040f1903540e29900306a03200050013401450100c00e60040c03003445e646a020810b00c0304255954030810200020410704c540c1c010944c1390b10081c452030404014400c4240006055a00e0b904140e0200c014082c0c001c024180080441007418000d804030313203002401e25400705030700340c0c0603c02015074040e4918003803040f80c41039a404d2310749889503419a00c030a0001e0400d80f1000703400c56603e2000b42422141c0c142180020300d8154001c5942da07080a500074101402c1d070041c03d0502c454030100d6049951596510303810b46807240380001d0b2030026004281d80401c0e00d4500c1100c091036204000c410b0647c082103d50964462030115403582d9807100b03400d40d8a224900c11001c0740d8400780700840030300d50038200802c1c1c01380c002e01d400706000110741c000600300c0d403001e102100d9690060724800d046580105220300c1080c02192070f40e49908280c1074030b03a1a8403a000d403840a8030350 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 181369964 1250 181368714 181368721
    0x90b0c010902040f0e1c1d040b090f01031a15010f2d02072106091b0e01060f110705190b0d020a03140114150d020c0a02041104050a030b 60
    0x500758405100190000c10038041a02c2c0d80c41e04600030010b4800071006401403c0c01408000c400c1c4007601c0e0071002650741c04545071030000317004c0d11030b80038480403551050315480001300c6da40e80c0300d4006000d0b407050b041c01300e100d51461030300c0c202d00e86c40c507101202c00c894500c0401c140d03140c0b01144100010b07000e0030414001d8110300411214400c0c1400d11304510300f030503082c102407012025405616144243c007242d00541d19010b522103501c03203244040304403810f030728260030000340e454000f0319500f072264640d488503080490f240708041c9000d800030221060414010441e82c0e5101905240c125941e04150300050100e41c81141c4a21040c00340741c0c00751004a03005d8449590399203014005113085031165481d02581d1158101030350082e0001c800103410040b0b00405a003101c00428120751508201400044c0b140d02071119400c1c4a10109003844014000f0040b00d050034002440312850600203000c00c0103840c410441128081e50060000c1c00c404c0c04140002d85504012000340e1350404607201041d136 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 181371214 1250 181369964 181369987
    0x1090b030106050907080610052701111203130804121a10060f080c0d020409020702040501090e1011070b0109091202061509060604030c0b070c0e0708040303150f0602030424090b 78
    0x219030200700070301072b00780888007240542035002000110001d80c0d07000040c003414103e0380d50700c849142554080340320401c00310340c0000c2d052181040301880303480d8407030410303035120f450482c450305491080e146481814500400c98803c0c58540d0351140e088420003000601300840203100c1c0110101074414040414045402442031000759002032420000039541c80fa1961030104c0a50045001240110300340710001c50101d200d4021411024100c1004001c100d87c0300344403c01410b26070446409024040140300b010448d40010b00d40070f4000c80c00041401d0400f46070261941010f0b0003c40219000f02003448164a01c60300032526001d41102c0700e1035940c4a040010f03019228650008003001075452000480b0400071000d810424001c0c49c40816040d91000340b02000c2c5c0c0101c1e01c01c0c4c00901c0050004001031301035488108502050061041c000d9120301c02c01d24800c1113908030a01590000c131f400c0006107540301c04400004004203284489210a1801074103508041c0148824098049503400507032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 181372464 1250 181371214 181371217
    0x5031507030f0e031b0f0309061e04090f0608150c0a03110c0304090c020607030207080f0304150504060f0c090503070501080601170112060b030a1a09030d0501090b03010605090708061005 82
    0x99494000c0d01c0d5254000500c4800030b02001c001c50a0a018000301c03100a528040262604160064035403480d01c0036888101101000c51050700c0f14500041c2f0020030907824500c41d0811131203d41200081e0b6900b0846500d00e00f07605111203103554480c8200b0008680300e14015550014150309010903424440d0401c1c0c8098044c21402c0c42c403030f1102003800500d200a54014000256064003544c007030f40c48507a812000c0c0c2c42061400307810350808101003d05801c01c00010b582c01806114020308010040f61010141c40c8184c0d400e84229840c1c0352406106091032103044110050b60400707508141c50880441d0300c0b00341c42e100b8941403340741d40c0029626400f0ba00f06154094103003102d8000c0c1d40e140d2400340745411039202e040e202c851030190460101d04000031003813915a00030120441c410320f20f1030012140d000c014440a540e010900202c00c0100e50b60181074081c00800d01c0205444903c9001d2600711000c0d50f02652164101805102d220b40d00480c0303403501300d0000c0d1103144c18420241c0050320316 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 181373714 1250 181372464 181372481
    0x91807090905060114070b0105090c04120308191b08060f030a021003090f12020d11031204030201451e03031d0d1206050f120109081b0705031507030f 66
    0x480745c001032034020080862106816a0340c00c87c2c2c20490380c0c0301e084800645002d00e001d01700000072501042c3d408603003d054200e502540d00b90850120301d10080142054409011501400c14111400b408602d03800c0082c15500180584e014050910701d43c1c0000e40d030b40903140000c0e000f0040e841000300309900c03d4004000440d08020351204504242c60500d0282c1c9104210500500070403c4152440c5e1094680300c55808030040210f052961b03448500c4088040074100310117540d070740c1e4501942000e044008400000b4800c0c0714411030154034500700c3c0c03520401d0000d0000c40c030602540400248801d00f54680100e0201d51000000c0058030b01580140300e1500c00014030003410000700305180d000075400d0040081e40d40d80b03118200d203244004003501d415000300c03584200c0041da40882030400354105900306c00102c2c008145030030240c4440c8640e0340f00d4100821101c0c400046481540003c00020005140a400038040520b081c602c074440404040c1c01c0e041019102d804120080d9544d80103040c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 181374964 1250 181373714 181373747
    0xf070e0d1b03050d08090312010905070c140304050411040e160c05120309011508061803040306050106030204061d010507020f0d061d07050909060606030903040905010b0918070909050601 82
    0x3200d0740c0360304041307030741e51050925440001c0d401c500081d02d0030404800e070351940e03e80d404010007e9080041d000302610000304010308000c080080302c00860f00c04101c403064413161801450f82e51341010203100540e03501c506c285000c040d04000412640117110341060b4031014800041500047c8044115070440b9404000340140c4103030310b1612030306c002441c01140142101002006450314a440600011500b81304407010b40e0481d5002554401c0c16005440c411880c1c0030603030b0301d000e0304c2c1da0398401144d800f80c04c91030000b42e02007024080325402001c003d94800c1c0051107401040003c000083c175502c540740000f401070902680f03080550301c40030000d421045d401102403102080281c443c0ba0504400342071700400e80b25500002900d4186103034180d005401e22405400242c0c0e80c5401d0140591000d8940c146504c010000022009001d20540780a00001d51441d80d4902c2c0400c00c10014003c80b007440f80107034508500b0b00a00d144c200c00940e0448064600200d51640e070f03400140d43d050109040400b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 181376214 1250 181374964 181375013
    0xc041e09060b03072604110102010209130b12030c21040e0702010c03111c05040809031603052406010e040605180412030506010c06090204061212080f070e0d 69
    0xd01c0c0c40948040d5200da031040d17450a01240142c15150070842c080c40581000c50f00000104020031200d1040c1200c07404c06000252400c600900480c01416a21500308601c075034030008182149400b10035415803442800c0118102409070507400d840d20340760000f401e403030140c07140000d0a04003444240d90082142070990a07a41c900344201038082e000e41c1e040703640000e00d801c00c100700c4080c005040d22400e000106004000791144c82d420401440041e0094480c4070050050329030580d010000c40740c4803104090700000381132541c84c18618080003030040c108810110241d0310b40442c841d4001503801202480c1400e100d24403400450300900880c5c0101c4e8100071140c1043d02080b09c400d0500740114440c0c0080341300c40003484001c81c00ca540c252001400502c100c80e040f808522030f40c000060309400100000340c010b41c1c0b003c1100d02100301101c01c071490820542d0240081c4d422100c0c26070711031110103030f2035070603e0400c100403c0b122100200c2c0740320b215581c04140612002d4040321342004110501d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 181377464 1250 181376214 181376219
    0x21c0c0f0f080c0105071b020402030c1216030e0606010c03200303090d0207120201020309060f0415110c0312030c0a14070809030609071413200301050a06080c041e0906 74
    0x6005540540314030803903517080901240c1030921a5080c0545611b2400022405e5500c982c200b001039800038003031800307194040c17040d5840e2000030844540105524503c11000d1030110300098140c0d041002020b0480e0000b00c00c100a81c2d802c820b480070305a50602e06a4058914065041c084ca00c83c0011050948808010007501200000b5030296429280d0200d03120169034910b019441c46c03c26500a006070803e02204003181080d030058500c1402074524a0704041d11040417120390044028140006143c08410981510060161740d00c04201a00540183e1100c100724640511016101c6201c1c0308000444455242c4520114403150b000204c400c0d40c1c5009070305216600c6c0d040390001340d02c40e000e10f80210b107910340c001074000c084a00d03405804203a40810300030000c00317451000240c0021130711180b4402503400046642004003008460854995040100b80004144283c018000740710084050001c51000d0704199001c47d40d502c02078590354011120b051000015907482002a41d0500101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 181378714 1250 181377464 181377473
    0x20f0607020d09050a15080702120705100608011406090606210a05010608010e070513030204090b01090c05040b070803130f03021b10171f08010b0f01021c0c0f0f 71
    0x3010040c01c007543c81d2049191110100151410320340304080c201c19481c03030310006e0b07a80602c600c070307600007424015036041004405c11800c00b80e000b401304480300d4011091041603805144240805410403800801c400c807800300302d562071220007500381132040a14000240c20344d520302e03040b00d0f015815801c0181c4c0035076540030001030940080d40d03c4580c140c104000400c1d051310910303005040307600b280c2c000019922000d0003900c455018041c004598025400d01001503112405000c110740c1c4208803800c0c1d07941c5005041d030110b1f10441d0010081001c10401001040303103580540743d0290b003140416541c1c0d103032a05542d0700a020020000e14010350141400140340e004122241000a080e8651803030707540500030400d140030300821140104011380224400c2519142d010780d880708105c1c0b0300d0341c54100440c142401440c4141d101c5403846c2c2d1555051708003400c1240260720581400e00051400781148020400090742c501000d50410846000b55028400f10490140b280b682090b400160100142403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 181379964 1250 181378714 181378723
    0x19060b040f0902040b010f08130204020d020c0604050f0102030105010512130b04051b040603020604090c030b04111e030c04360b030d1e0e0a030c0f03031b0c090c020f060702 76
    0x1400e901c13491420b0b01814055015100c21050341a1039605c001c40e40d9540c8044d410040e101c2d000698004e41c0c01d1200200350b4100d44010128004104014600c0303251500e01603180c0000d82c1002e0b00c00340d00501c010445640c20100340d60030f421750144071800c0ba036208a000500781c030120314050003200b858001e001c2032100c0031402c190711190111070074480d00c50720410f000549026200003500000c04020410008001e5840080080c1032442c001ca200301c01e100001c0d0580f4110035001c101810000b501c07000715802c1c42c010101c03078882020240e00710b2600842220190085104090508500d903690100340c0c050030b03003a074034066050f00c00d802800c10341100b40402007401420142c007901c200c4140c18400e60003010601c07505184160408542c0c04103000c03c0b01e010481080c655008580c58001000241c001c00144028010040540e00910314500b0024290143c01c6540d800c8680400da81d074001c1303140700800b041588d10a03813001c030300c0182c407620480c50708103201d07402010f901405080c80304080d400b05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 181381214 1250 181379964 181379981
    0x9030c0510031b4a210f070906050a140a08010204030809040501080f0c12010902060c01020c010605090103050715090e16030c0212041a0c03042d0819060b040f 70
    0x100c51030b9a40d81824071340050344420f41a2074284116a07641440540c01c0d2a82d080383e4180503215003010300300d032510b511010407454005001a081510420b0110404100c158000c01d100981400350074603080114080403454028404026403d030001759241d1182090340005000210086685d00e0b034038103019a854008104440c4110309140000a600d18001000091080c07280082e080041000f0100140315025894881241d526200084050f81d030300006000d00142e070000160380c1d00584d11009084a0f21a0801d034820400c1400500109500040c9c0405440810408405205010340152404140c0d980204502044002040070404848034490260704081c0c0b424032908807418001c0e80c9422901810052454003031204004000141811540c141c1c0c4005080d0701d81000c0c01981415640944c01c554841c1c401c82444500104106403c10107186044140c02c000394288160152609204010301040c4152403c158041c010319500001c1113a9009100f00300d140c2c040c1403400054070f98035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 181382464 1250 181381214 181381247
    0xd05030105010e0604031a10050301020c061503150a050c130602030c01061505071113020a08090c09070c1211010606170c090d03050309150103061b09030c0510031b 72
    0x40c003008502d4100b4500b950181c9a104481d00d51312048000c10b2944e03800008c0030710440810b540000180c0e0b48007031004000c1c000c10741018000d9880d1050088a49013000c8500078086c1e405038402c0710340d0400f25040f094001014000115698981d1900160075005900404030f0500d00f0890010b07429400200410702e07000c4450003400205d81e035420f2002c0c4507503582c01d01403b003201040750b00001581400d00c0040c050b00180716058800c0c080040f03401b00c1e0040550301022522036030510150b640200b14070a00d550003160010b449150102004204800303205c002041c40c12400351030400e650003410803c0c00f150442d4001c00405540d50f000500b070ba80c200d603812207000301c07800c00b159050303d108080b26070f00030024216801455855a04446941c00201840c49501900742c60706a401d5000d54050f000358040c50b03002c140329a06403c1d480784800401300031400d10111134000c200082c00c11010344100c41d01180d2018290742d9a5000f034019200400c1c902c42101c07201400740c039400ba0400c91404c5109000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 181383714 1250 181382464 181382477
    0xa0e090408090316060f02070b0a0c020105040e010306023a09050109050d050d0608070b070222090b060a0506190806030703151d030a050313020409020d03030f1b0801050613080d0503010501 83
    0x5001d2340ca400e07040c0a8411042820010384106a0081d03200c1d8605a1040c902245495034422281d840c161081c1c104440310341d00000c4000044640703c3c03003109202002010089401d0046071b140304480d88181104004945540b411024071000f980500c0d40da5030004241d03035401015280042c020340c00b0340003000031240b5081e0042180e01c400548082a07403811400f95140080c40e03020086031202402d4040b03425409900144205803803406242c6c10140b244229141a0424108110b401d0080d504002d016003400d00a81c0544800241d5035819911141020070032a2100c00203c4d080031550b4101030003d211031480108010311b40e6218110004100c00f0030074030446404181030300e81c8140c408005c00940c061010805090441911243c410300c000e1001503019420b5020a194805000003900400d50714a11060030142e20300070881000602d41c240f003c600c1403107201400c070b4401801803030701404006c41c1681000807040c0046000d04000070440740074861200009109134000d00403140007400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 181384964 1250 181383714 181383737
    0x607080703060b1c020c0307080c0d1d040b010e0d0b0603070f030309031205071a19150b07050a080412110406030b0c070312020307020d0e060a0e09040809031606 71
    0x700384110b1041d5445152428035108024200c40702000c040200084007990820002e000050200014039904e0f204200c91910f5040004c0da640c02d1607e02c45041c0284030003030700c00243d5498030340001c20401208032400035104140b42c0040f10010404a0096080206c3c1c11a10b4140481f03440114072480c412412603501549a43ea40041f000d210b110081c0072418003001840005c1060802000005140c94440d050510075140c2d191014810007018801d00c920f04140150794090500d4010415181c02091040f42ca091000dd44803142601c5000b508510204000040100a1242c24560303500201103035100d54441841c4c09185440c0034044985204c4110380c1e50b070300d0600b401040300310b070b4124000072101d64407000445403d43c00640110100702c0c100002c8001e0715014809980038403401d034002c140010440c000540100c0c02040d1807403044c039007071041040c1680d001c0e000c100800f0041e503070001c140d00e8a00d0b0102803402001c40c0e0b03035458004e824030711a42e2a1000c03501401c0350328a0b600c0380311084 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 181386214 1250 181384964 181384967
    0x105060f06030c0304210801090507030e07060c060209060f03010819020d1106090a0e09010e0c09040303110f16120f08010501050a050408010608100b0108011d04110d0506070807 78
    0x5100364055a04203105000060300c425495002d168428040c0f480d00c041d8041c1200d5003005040134814441c0450b5060b00103001c07045451043c1c0342d11030214142041044208200c240d5280744502c034100c200008428600100042c0340c042d00e007000005046030340c41d0b1001e25030000f51504240a0803000b40300307900d04041d003034800207400c0c5130f00c42c0c02404841260700309480315030f03941d121210065003080040040007650703102ca40b004002000c415025240ca8100120202e00f0340744544107170180e90340142460340047d510103800e60342290307041c100000ca04448801d404031a0064100e0240c1d4070001250b05814865144404ac0e090340c8201803030124040315400503100c0200c0d406405000816160050004e540500020542c140a03401d04505295440511074203485594102c0c2c00c607038000200125500203240508a480c65013404d0909035903050584071404084000d80552404440f00081030901550b800b4890a0b43c4000d4071200902c03000f82000355850348113449440014524000044401c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 181387464 1250 181386214 181386229
    0x9030f030a08010e0c040e1501020d020c060d0209030f0703080711010503010305030711040b040204060c0b090a1e060b130207020a0801020c0a02120f160e07021504120c05031b010506 80
    0x50716512202c8141e42400a4100d8666004152129031202044007060924000d4a56031250780910b4408501d004110002814840002204004d40d44070a0b6501c039130741e0328481511200075684100588a1032080c1c00a0300d84100c4070700c4111070f070181c00d101206128800004094241c02801c042e91040302203030044801c0d200904c809001508144160400507907443e418070703100c502c003c0021038011030f6000000e00705d03480740d4040320206901500325800c1003200c82580ba40222058051b200501d510f80310021a080303580340032000300341a42c102208101c2e45034856180d074807000e04030740070110b903000184000390301400e01070744a031502503130014020005000b199036011540c0003800e90b03c0015800e02c003280b000c031640e96060b409000726800002e0410001443e04018a01da20011303d0f103080400703052044090442400c6401010326000d07101104502540c00640c01240c00c14441c600341c2c02181c2c0364050308002000c90000055940040960440102e80018504001c00468441c6020031661 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 181388714 1250 181387464 181387477
    0x90601030f1103100e03040f0915030b071403180f01060312030b060d09030507150902090412051306050d060b09030601050d0c030f030804151a090a2009030f03 70
    0x101644018480d0000e01a455103180a60b0050211001e1069007010034095a02848070b140c1c8071703880800c08000000c840507030403004144054041000b41004801011515039a0002810510740000828042c1c0d200d00200265521800185601d900700380580120748014404003c0c2284034483d480c8003002010700c1100c08582d40445a26650190f007101500940541240e042e40320b03406000c11900122180149a80700380b00341e4403139580300810700d84108070300c000ad4034202c00380f85810702000c016202d100d00281c0083e044545c040c0d542014890854240c800c3d8102648901ba149200240c0e070b50b0040090244130501c403005024107512034a1401c003d00401090651503403106004001c5030a04000e00300c5110f00411000b0f01080e03d03512032004440e80c0280480c0080d41041c204400e12104501412900e10b11420a10000000540300800d03100c0010300d05100ea100300e000305900d8407843c0d0101d0a020344001d04405078a0f00c4803000740c1c043e000440424064001c131a80d0b03041c0000d01100300e441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 181389964 1250 181388714 181388723
    0x50c070614070819150806040b181002030a0b040f0501030b060d0503090603060f270f0403020c0120010e03030603010e0606010906030902030a06020d0e0114090d0c051e06010305010509060103 84
    0x80c0d42d91100745285103074283c1480d11441a07917600c103d202d49000b41c13519902616001c4000e042601389444d00b00c2500310020454000b10a1024010324400008901c2036008448408056220345600002c1c000401c440a1150b61142c6040c000c1d601c040c0e480e400c614120b0b40101c110b680320341d5501080c08541d0303007080002842d030b8204210010f10b51511102640e0000005880d45001ca81401e000c620444000c2650381c0400640d0054034a1001ca248425644103ca81c2400c0b0424205075501079900c40c41540c10780d0604c00a00060944e49101d0f0340802ca1140200d030007400503420320210700b520303607206440c00c0d030195080540c11590168000741642c0035660680d0307110151441c050046005200404081b84d150080c40420804240640091f008040200e24005035200004100500f11100700608540340e8001c1c604025201c40c000c140420007d50740d00702000304a4042ca4410308203200200080d110045c0d90368100124030000504c681a00d2140b0000c01c499168a003803581e0b2500c09110061 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 181391214 1250 181389964 181389977
    0x20c010512040c031205030919020f01050717030c0702090a0c1b0314040e0a1a06040b070507030b0106020307050d14030612101b0e090408030a0b010c06050c07061407 73
    0x4001041082141e680503000320b8080010b07a4480e503481e08107446140c407a0340060008000d11195510510852040d402820241350542c040e0340e0105210317541114460f414420003060309020710803101c1000303c8040c0c0c0303602041e13680d103403904c00d2144582000304160300a0304620005440102c02e031140d00c0c2885121340b01c0942500700d000d1040c85400800c0f20480c104081903011040300e0340314401400c05041801803d01c9603142c030400340400c0380c2c1c408905900700c0d03400c0100034015407194003c403015281324501031030b520121030401030315024181c0d200602e69141303240000384042c1d012020741401842401503841900a10304200c50403a2000842038141e441040402d03401e140003041000d803540e0003010b860700a20b070254030404440380600400101003000c2d42642c03080b5032101c030404099000b1240105241801c0d10f8420090200605502040da0303100c810b24141e0b8028518001010b0303115105001900d0301003446d014603000040c04503099400e03c0c901d9203040c0300400e04103200d0f5500e07550742c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 181392464 1250 181391214 181391227
    0x61e030204020f3009030304151503020904060902150c0c0112060e070908060a0e060c09040e030a030618111c0b03100213080304080d0c020f040504060e0d020c0105 72
    0x40025804180043c41c00303181000413001c0078404015110303a101001891108191011644a0301494010103201c0c2c5a0001c2081000280e003c1514844100d4290f8002800880c8102040030003801604041c0d40040041e040000b001103640000560f148240c40344400b207c14070068120500820740d801603250082a4081c945510801449540c2c0050407008a05590f4500349002d002006030f92040000740c0e41c140c24800c107070080125540100d00c40408114203018600703c5500c0382c01c060076981051400250301f04c907a40d030319084501c0c1d8400031001d4030303550345a1680160080203a4403841c01400900101400845424400c0100b41c040d03242c000ca00e00101400f80c030318502642480d00342e42c666624030f001d1982e10100440701107980c01c1c0740d005955664001840c500c02140c1e51000d20164401c0100344010500480c01c2d5125240030309251512412910000d442c10509201594103c2c0ca80001c2000703221640d0040401c032405107041d181a000e0b2403034200d0b101c0c803852040d00c0c0444c8040254 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 181393714 1250 181392464 181392469
    0x813151d100920010309021f030c0f020a030e0a081507030c140904020306131113050319200301020334090512030c01090b0103210903060b0301091202060a061e0302 72
    0x3d040070078051400181c4400a50700103805007005403d00340e044150b81c0007210503240c041c8600207140c606820002c440300032001d4025600c42c04540010200302c1c03204c5940c261030f1110200311016140f00415903002c1e6411180c07040c00c00004440c40b0340000d05040365080401d0240998400c40f01c60080c3c800c1c80e01c0080810302000c2d500107849240c0003600282c14031003204161180b114100e074905c0e0b049030380703480c5809010030100542d00140d200b9080b60124540305260b10741280291580030181950b442021b0343c2409101e0909026036030194000070800444e14200c1600b552900480440102800301d1500d02036401424050900c01007941d003903092090b480c010035800c2c403003404a4201da150480001c100740c20b649248104486000da90401802002420b6a40d800804d070850812502c40b620606e008000c18598800038140555034080320b84151400e4000800031a08203030b40c50440c10724800029903d145c100c0b04894a146800e4020074440c0034956500540c03142c0d15507840c2c102d4215002c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 181394964 1250 181393714 181393763
    0x30c021902030a0c0303020c01090b120a0c0c240f0209030606120109020a0b04030606060212090105031003050f28020102100b0105040e0c0c06060603070813151d1009 73
    0x3007681c2c54428050918001000d08860030003840c800d07406000032507800d400140c507200c041d8102123a00c1d030b1f0500070f4a407040b55418404c0e0380f20220f03040c00b0450755600c01c41074912031740010016120140c19411101e0103a010301c2030f985070742c022910800000662005480490148080895154002c00041170240c641070b890441500a018000030350714050360b00156030180a0f50202e00d01d0036010a042003130110030310401004010b20b001030101c0030402d20418070a4420924a42d05000d0301001041c04185050b07041405503500904075a03002d29904181d5a4031070046c140096511442c440d10951303281200c0c0e10401e030650607001415486e5040c40741c900544030751b41180e4108982440f0008840542c2003c550040c0b0008199583d981d0190f003406050140c010040ba010710410000d004620b82c5c401941a402005903c202c0490000340c07829400740d0611100c0801c4040c00e11000324440b541c80204981000072020440d0083d0035400a21002d5034102140600903521401802142001090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 181396214 1250 181394964 181395013
    0xc0f0503040914060a050a2610050c1c1a0402031f0303050c07080c0603060f0409050303100f0f0b2a0106060e030606090f010b07020316060e010807030c02 68
    0x101a00d080c141c66601620032606548280e040301021001480b140b4241030b031709800606419900d1031101e45c20080644c0c5015062080e0302c01c0c100a07543d558401500502010000c000580014000741c10171243c0401c690308100144401019900905040d0b60541c3c440e0b0004051726078112050708801c00200070080d000200803a01e0758a03843c5180e210010894142e4000c1c40c42515001d80302e91003020103c2c036114254210b003070681c0c070030b4540403110390390001620341c80b0004881c40030b0244c817a8008a8040c103512070006249100100a01031004100258003080e41c05003c00c0511441c1d5602e2429460b0314584030350300845030200008000d60444000d10303a20b00d40f0ba50403028640b41d140400d01d08440243c2d108600007484080305401701e140c24407080e1307044902100c0403041400d0100c1e05000c4403806210f4200060000180541127407002d201c105500300600400344800ca0782c1e10b0007d40746080c040c4000740000c580d0340002c0c3e1054020b1003000340c0c915240d170050681c0019403600b00c8003003a020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 181397464 1250 181396214 181396223
    0x30c12030306080a030f080108160311010e090a020c0f060c03072a061509020715020a0c06050c030708070c1a040804051e030d170f040201110a06060501080c0a0c0f 72
    0x400b800701d00398004110421380d06100355a0480c0030040b54100400008040e04440c082c1c0d0020880c45a5107042c81a80509982c0c100c000108404a10b4004ac1c8807440328814031a004580350302001019407555011348801c00400d42641e081c1d11000c030034541c5a000498240103941b0f010300100701120301c64006d094000342c0e200000c81450000030000c21011400d5501214200d0b222070116058120400c5001c008110030141507081160319500c0c1c04080203a543c2940c071490f404140c04141e0352041c101c04080c940c0048081240d0b0070000340481582c0c0c8205c1301d0f900841e00d51404143d0076480340400e03044140d00140178038074422100f100c210105a0142c016101c8190510001c0b41d6543c40094000c0b2101c0040b4290304080450400d250030403190035202011b001079009603042605200e0740c85544420754100c00c030013a940e580b005860203000c20710031084c0b522500c07150200300305081d8040c01c00e031380090300c945c030090340c855143c4e8500c3d10401611100064031081d003800050681104103012601c80c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 181398714 1250 181397464 181397471
    0xe01063203010e030c06100905040201020c0d111201090c06020705060304060203060d0204140603010b0306010501050a030f090c0602070303181208210a0b15040b09060f0d0f0903120501030c120303 86
    0x300200385113980c0099102c90460380000f07042c0980c110f44038400a0082c160040284040e1a1540010b500c8206480409004c2d0710b507400552708020b00c610042c0c0704081300500714540d0450744034405000b06811281101c440e080c07504089111342c00041d00a0455130001c0c8640d01d141da031551030340f006c0d4002909064124040344400001a43c50f8052100d03d003840304404410f526180c0100b5096070710f02e1000701d02a0700110014031499074003e00700c6520358800d0030081040001d00820b40000c115044000e4405146201d0108a11350b02048036070843e40030f50380c0c82d420f074a800f4986a841000b144500500c1c4070702036200d0400500f9540190910001e142190101c0c506d000f20440c144040485020500f2540d40c802c001040c81e008002c12280c01e00e982c555800c040c180b0450351014445c1c282050b10404010510200c021085d100b120302e18800801d0600a0208500e01c113001380c0407010f4210b000c070b6001c1d0b41c6003405641a114150490341c004841d50580c524060510680c207001030300603000c040c1c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 181399964 1250 181398714 181398731
    0x130302010f14070803040b151309110a15110105130201030b180108010f0f0b030c010e2d1c0f030f03060f15080603160b2b0e0106320301 60
    0x15000550055107402d9592505103424613041d0070081c04c8c050361940b0400100040e07128150320b5005a40310745400941d990440c14100541010f140b1019801100d941c00892110124106884c0c100c505031214180084116a05801c0e2042190a204280c46071003403100558400c1d00002c800903009800c00342c3d0b011032414a080c900c2c80980284a00340c1d111040341e144003030b851080c081c86080880007000b41540a8000a0300d844c1041031480c1080f200c002d6070b844695400c200340c40e90303101c2400c500010444426040c10500381640b030142c440e810f0000e080e50388885a1851011b8282e004d01180b003e5140741c2c1d019601032940f102c8130340030196240b401085072400c5403804405003602888540d580c50801c44004e080c0000101503a00a401041548504981091050081d198420021074075458007003900003000101018030100400401d00c1002510043d40c401480c1c41c040e00003d00c060358645074204c62415001e40b46c400c0d800b0030030b0074405000c409a522403e80c40001000820300e001d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 181401214 1250 181399964 181399997
    0x303050a0c1a09010921080103020f42070f060c020f01020c0703020a090b0d0602180a0e07121a01110f060403090603050105091e190c050706060b130302010f 69
    0x280100d0745074620340e40d00c17030009081c4142120001c48003003c070031041d8007035260804018000c0c08180700081c040d44482107400d0b000e6540001c1c6a480217214900c1c22403111400d240500154007404d102010f401130742c01074100320710240d0101c4860a40201072081d00b891280d480c01c0052010550740300031402075851401036050280004d0000105080040000074203600402865417029485050b074940b6140f0804e0084c1c13200310520b00e844e60401c20050312280862110054040320250095200e81d40f2080882c20383d000391f0300c01c1d018071043d5480c80032030300426554100300c81c20060b03c09840c0c2200b0440584640c410000c60f08102015029940303442d0300c00e03210601d041d1081e6411008100000303028010710358076200d500d00401c012a0710414a00f040002c904042d10820f00700102c06020800145000304407400c821a180900072081052284400005000342c001d040120f400e00d04080b40054044003084c150f0340e014003c0341c00c40150741e1859006480c21000c251404061202c20104100e408c2c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 181402464 1250 181401214 181401263
    0x32101080d081f0b0f18042703020718020c060f06060313030c1a220804050d110a060914040e0706050c070b030906010603230708060409050102030103050109030906090303050a0c 78
    0x1a4041c0e05c0260f02c0d00f0000c034408040c8801c0c0070b000e0340140c2c64044104020941480c0e0240c08658544440c000b00f146414103e042500c40c3e003002c01220707040c002d040084110f907801444515032500030f03510640c4413050740300d20812040d500280d21a000b8808121190f114685035907125200c0d0808900c048a156a4004100348240710540f45010000400540000100e0501c2c203a81013011145954140e5607540c659501440c01864042d0b0540a0600e040040407207126114100c0140726090301507845500428041c001e00508501104100034414079061600641544410480243c00481d042c10b10071111500b011080410a205048000500142c0a0029405060329101400c41c0c3e60402c940034007910121343c04003104045200000b4011251081c00729044482803400c80360681b2480c0009020f442203680141455100000010401c041540310724080c030310945a07c01d13200e40d106c0080c0c54040a07440040c0c0450010000b400c0c00078400c0084041d213910901c01070300100d11680001541 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 181403714 1250 181402464 181402477
    0x40209060c1912021519091a19020f0f07030216060206040203191a09030c070b0714010203060105070609080714030c0106080c06040323032101080d081f0b 68
    0x80d02c1c50298a1010700c080f0906041c142209030000b00540034400d00014017155004001d60002080002c04010000307140c2c02c050380e403d411001c0e01ca804411b0085600c80c07850140d41d116004c8018a13002d4441160074001d980448c1d82030300700c05040110902c0441940c0d44a01000c90860041c3e10081d9038083c1c0e42c44548011f015180e00401c102d19051051600e000d44100c1e038012001c4552801c440012030311900700da0005110052403050b900d440344c50354a5030040d1404518103014030328010814620060141642c940141a41c107030222a010109080384002d4628a0000300c0400c4543e02180454000200a92246005501d00140c988804105030030030f00640340c003904000303000d2004070024000d4801504d404006410a5294480000c03690710942c8401403d480d410b03030308861011001c00040c40c0201990040c0d960f01e0030301039640503000000041900030068034500101d44210b00088484e1240310795124131210361180c802c04410395035402424240b458004402194014011019011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 181404964 1250 181403714 181403743
    0x40507031e080304030e030715050a030b040b09061c0203010c090e06040506030c0d08040f0618080d0801030305090609031b03070905130f170301060e040506040b010e040209060c 78
    0x20090441c5031080700c400100c0303100340e0090742019103000840c04440440e600035034035040c4114280362a0b80800d0802031103070721a95040071204010145140c00c01e004003074400d11940d0030054140520100300407280710700110340e00030116400181b56410046284080c40000710040c40f0301d4905580001d0035500343d00342800c00901002c404001142401003002d41020303044500707001e170b450320b800481d6407000000722241c4100e0810342030390248a6030f6030484010f05140c0d00c810310b15680352800600902c5860b103502c00c040101c0398002900c8000843d4404e100d000c41e03903900d812079207513881c2100c1c1c580018102586c005010044096966010014051114442d0107496800307101001014140f05990b442510050b090808100c81c82103400312500c1d85d10b42c490140f0079814800d003000e03044141d202c860340328101ca0000000c0303102c50700321800d01c40308441260f00380519030780e00d02840705450902002070b020407052003030307001ca5140a8000d81580c42c0003600240c10141c20100d0603203000f082021591 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 181406214 1250 181404964 181404973
    0x201060e0106030506030d080a180f0c0b0a05120c0d022b090201140307110a1103120406051912020d02070c0602070501140c120301060807030c0207050f01050d06030b0405 75
    0x10540300600014010320b030904007003000749080c40c0401e0321042d4070401c1d00e08001050700080d100000301e511290318481e1042c3c1e00c400041c0140760502034089440c509072480e040003d400200807035214211610a815903452600781041c15008418030080a4031007144500c0c244060112440a44054a900e002211480c105c000c0080080c1038403401500d516800c85040512040244c1d80005c07144521038074045245039a65581c01c01207440400c59001507840e405089040f00a02c043ca82c0c01030724120044003a100c0083c000c018a10f032030b200d584a42004110f050140d4086d4180ca080e41d22941d149a0a010441140107607505c07080b07034011500903070302c10742c0480d82c81d0038800600b140c0005130085000420f0081e0405001902042d03000040110581c40000e0b041881c5400748031940302042d00040050312941c4a560240c00e015080360365600191400001640d154400250b0070101c50002d880982c004004100450b0f03181d00c028a855035550715504000006109504101e01c540c0c010400740 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 181407464 1250 181406214 181406219
    0x50a080d1a12150402120105010326070c03080d09051c1b1a100504061221050a110c0a030804170c06040504020309010b12030c07080a0b0a0216080a020106 68
    0x1003200745080105280128081030004031100c4002a654000003840b51000486545a10024007080064034003c4c4003542040300000801c01506414440c0e11030f140040c580c00b82040c045085903015a24019040203a01c100c100b011500c103c0003040050040400804d0301c0b007240e1503d0745010201c0d203100140c0e212449043c1019903000d1040c0d1180800b2501049000d41103465620990f25000d0800428440396000f017225a4000040300b0000e00c0003030030900003030ba41ea00c4035801848504800361040c850300040c0145040d11429a0303001040b072900d556007845210380040324a011560f4007640c3d10f02c05e405038980b00b50b0781c030f00c2c28000552107081700f19a20b50800308a140f4a4003c0c140c00d40295100061550855840f4416101521001e603001a101d641ea481264090031350401030580028000340b442c3ca02200101c0208245d01c3c4c05001c680c8815591078a003665180c8501002c2d0130b030103150011602c513500c160003c0c4a84c4083c0100b02560000d00c1c3c442a00d554051300351178016070340d1080704 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 181408714 1250 181407464 181407491
    0xd08010f060801180b01020a1502090405010905070915020312011e06020d120b0a0506160b060d0203030f0a1e020a060b010e1c033f0b030a0b04050a080d 67
    0x80d0000e02020715040403a5454401d00c8042d9109075075002c103100ba114a00410241d10030003e40e1940350b00114440038402d040c1040034001d501c89401940610b0500b400450994042e004850040380240e445821440c6884000c1e19032000e081d0b18402180002c120541161807041c580a0203040414101c12070051000449244c082c600d50061003550001c1c00420b18a6400244545a01c101d002c07000c40c259150303800160700f45250307410142d030003040401c48983d91a49400c0c1003542c68801e401140b02601c41c41d04011048142d01c1e40203506601c1040301400005040c0c01810000d00c80d0b041c44180400c0b080c50221145034503003054401680003901b42018407001c0d001e04422a907007803c24403501d80000d0007080320100001ea00c450124041c20403102094451384a102a0203240d2241214045c0d003001c0380c4000690010541e6024400c0581840343c02c26244180950000c008005182e4501c580c0e03210740b013041d001481a22240501851074011030034001c010407040401c02c00000343c4a4981c0103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 181409964 1250 181408714 181408739
    0x27031210030b010e063c120a1104060503010501170d0f08161806090f0f0e1305070503030f0a031d030430051f020717030a09050d0801 59
    0x2110080103a400010808124080e0300c060640c3c000e000007403501e40d142404103141c0f082c21100c558010707803451843c5640010203a03948841d86044184a812109030780c04010500303209000c0300d540d030f0700200426000242507110001e640c00001c2e00102c0c617207603180c0001c0d00b151800d81c0030414001c0d082c0c00355410072200384541c42104880c0d0174258000007890300001c040b00402059180910b410006035000c1d58010028010040005804902055102e610042800c0020f10030a10300369015400462a03030b2503c101803023640d01440e2445081d580da1600036041d00480482520306005440010230551018002042c48261113075110750358084444004003125401d141c0c1d00840400d13090684c800e441c000c030440d001c0795030507405113014043d07000702d84802140300c0d1b8500702d120141c4c01084003001030100300c031074000030303485104000e8051540070242a03124024006210b04039100c1c0f415441e0300c218003c2c640080f10f4280005805d1000e548062501c0c803c0d160001c00b0a078440c0040003444400030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 181411214 1250 181409964 181409971
    0x1080607080a05071101050c0c0d14181201020a0c0b07020309030a0b06040e0f10060b030c0d050c1b011a031902041d1606020613120305270312 63
    0x20261858044001000000040c107548211521000400d050a205003848085440c481008100a0a1403104000180d00244c0042400c0c0908206140d0041c090110030082c0c0350b0082800b131400d1042c0014980804251452a40c00014107081c150140802d1001d400e08402a840340450000c443c01c204d0b0940c08000c0242c01107500130011040b090320040744242c10300e680002c00c0c108503100d40e00020042c110602c03030800c1c0f903c9100141e8a0b42c0303030300281c04424001800b108100b19601c480311030020740300840f040c002644080054151303c3c0a130b40d100300e0788520700c07030802420410081005000140e152010000c1691280a4103c404040100c2e001d0020b10880046ca06803200015481400c81e102c600a441290385100b1140a25941d07007841d0044a43c020990700c02c0070406542000c401039078020203005118000014030074480c3c250340c082000340c01000d02c400e24460a8800c0300074020003814041c0da1003001d4110b405007201d08030140a80c000b517802450b103629000b10300f060f0392100107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 181412464 1250 181411214 181411229
    0x10605060403020f15190e09090a02011b03170103050309090109050132060c0f150408030406050a1b03020706050c04030b0103020607171603110f060a1814060f01 71
    0xc0000b080141d540a1070600e2070002511070643c2c0c10604000d108140c0240003580f081e0302c903140030150404d0781c00030b5255440c0d14100e60740700c3c1c180c42e042a50743d605d80d064100280407a281d40800600281282c81320b1802c41c0c820316000d0340340f0032101d03014141d610080c1d20864042c0d00100d420f144515161318280c0c090600f0140410441d80751161102644840d9000f03007120040780745ea0640c04a1000b030700180034000c040c0c0f0329a03071100000600c61790341040c0601174040d0b0103440c2c070000b42d000240603458001c0340c1041c0114111b403640d8558400409028003804503590381e480410041e02c07c041203460210495850040c4c070f07914682001400d50ba401048400000d00030481400000d000019650640340c041da6042e07110041440c1c5020300b031010032035a1020440c085002030b6150301401c41090164440d9803100c002d600140c0105544031864070b80c1200d01c2d08040700181542e601e2780d003d115000343e002a0f01c07801540603151072101034807501e40c0640d03541101c0c04021080503c604964014480b0313 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 181413714 1250 181412464 181412467
    0x5040c0e0105220902070c031202010b0f040b010c0507090204060f02060402030a12050d02180a170a02190e0f0702010501060908070b1b062701090c033003050901060506 74
    0x480c00000c1092050410300080b5062401541c0c0c80d18840500e680f014140d090300c11995480e15003021f000580007031104803028504e8000d120790b094410300441801c07880c0500044a0300301d0150400c00600a00c01e80d0604000843e4080300c0804c1c01000044002c1075400d00c016903841c20514024507035030201140c2c006540c404010300006850000e2655000c42d003007042d225601c0400002203034a44a240c40402c4440d00120340c0905243c00d00d00c048030302c5c40040350306458403039855140c0f000240c14207030510301d42c1d000690248054240b03164208140c445002102c0201520340781d551482120a48100c400e01d4903038820486420340910826015198605184180741e1600c0906550380b24180a00c2c5020600460946203403a40d02c085810b80d80031070400e44c3c12138540004070740380714610200340208904000720881c8001c00184182c640198010102018080c210b44800d00303500c4084144c4442a20640030303075082850030324032504001166540100305400c00b40c61076400c2d11455006039104520 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 181414964 1250 181413714 181413737
    0xa1b030e060f09030f040f0f09050c070f0203030904090303061505030108030418060b0c0610050603011a0906070203010203101d07050a0804020102160620060702340308030105040c 79
    0x100010740755403150b5485440180355403900a0340782540160340d400b2400c03a0000c900400c1c610102c1e2284803c1d20f044498000c001690341c00c0325030658000307590000c50b0250402015010516064482c2d900900103001c4a10b0000c014020404032148000c0640002c0c0e42d4040601c043d4003103511015180c140c2e441c0c054115410107171000d0700d074411740c41108e0810b207581405a4000800350003d400400d40ba962081d1035640d526000d03921504101e07a03180c01f9030520a004201490404140d0b8165207801c0010095050048407000003540426811503110005102100c010380e02400294410700100000d0740c01c040c5040d051582ca1030744880c4040394000381104111115034480292108807e1902d00801e145d240d500051741005620f48540c812002102c0c008244190031110b0000710254280b8940241d50100b00016242c400a50b404401600550110300518945a250b0300507860040c0d104c54640e0f031811128124101603034001c82d00c00c81c01200400041c0350a1042c00050055070500003075800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 181416214 1250 181414964 181414991
    0xc09010602060c0a0e1021060b0a1d06130501090b0903030703030b0f03060901060501120204030807020607021801090518010b0a05013207110a0b030a020d090501050a1b03 75
    0x840080090f01e0032100828091180707403280c05c0b4880200c0380600100080203140000800031500419448940c02000c8600c7c440310304179200d000100c95414401c54140a1550130031900c20440b5000c0541641414200302226550b450051a8004905186003603a6140600141010390140d0020b40c80f084140400d144a490100480c8c0a41d80c0c149000103600c0308540c0000d108190540d8080e40500c0b4100c100140b4800550044041c1d03082621900a031103008000c807002c0e441580401005020140582c00040c1040300c00361014034402488036001d0030984210325001d071426070101e20590b0300e40080c031440b8031801c1a00d98902d10798030700074803c2a40c03990214258541e10710820b81041444011a54445140781c58826001440c08005501c40d2aaa15040035138100040c00d41c1d1030320f0180e61a442600d07207910590b0845215031070b110300f1075507a08196402500100040707880f00c1d482c1c00c40040050000c0c461036100b00030300100000c40c042c040c500071000c240d4503141c8000b41490a6510442d40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 181417464 1250 181416214 181416223
    0x912080f010b0912011401261002090406030f06021c11030f0601120c03050609180712080d05090307170a090e09030c0109050607030e0303100b160c060c050c09010602 73
    0x660b03422810700d5841c2d154601091903029503040b40103280d46012030641103001c101c1d840c0c030304071110317107000f04003000d445610094040d00050420001e44c3c0040c140a0007116035801524845600400c0083c1c101e65a86078610644039000049030702070340c0000d40c443d0005100010a200042c40c0d0707410800c40b100140c0f039659520000d030520074101c1c00c120000e07010368030a4080010b13946d1211028480b00321282d4003d406020709403651841a007040c00050884c2c01c0702c119109840e4440750003041c0486c03520a0b2650a044460350503100300d201080705807a041d00038000c0c18041c102803c01143e0700c2d119801c1c80c2828540351550180c81c1c2e54208000861154070440c41d0003910900c0e000050117858002c111443c611805021300300715401c0c0078420007801000b24580e44111500c0d24203100082487c841c1a0f01d81c8400c80e2145d03020700040500f0f004880250b4040d00c3d00c0441d07203581c0340700301d9400e85640c0c15880c8903074414400540311508410070021306111080e21913009450700351440d4103124011751607 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 181418714 1250 181417464 181417469
    0x5010c0e101b142a0918070806150301050a330f0b0a0f021908070204020d14181603021512010303020a1e020a0608100504020c010912080f01 62
    0x40081c0c01c44540481c040c40310a0518090b440f651003642d900c00700240c50303140d0b100c038900d0141c0049000300c0540c0c803481c00c440210708210001e2000b0800d541c4c2c00b0880092541a0311340780b01b2071203035600c04100810100320540c0180d003007048103141414900205425201c00506240303585090400030040c100781700c040c0c6015405020608031075500300002c00e0400381429441600d0745190030b42e0010700343d0714200c0101211111959680c98165001c041665034554501c2c5d041054492100c50101003200300c40640080351005202601c3c0c00340104150081d1110f1840c400030700c07056030052000d0300900b0f85014109100240240c60749107507602004103251014070010307000340c41007210381052110304821680481a244004200c07540c43c0d04009640d140344c2c8104441c0e01e540c0c80501c114203034225018440883c0e0003054407216909049003200c4201001d0941c032400c04654602181640d0341e030000c3c041105002000007800c15940c1003030030340d00d4030a03c071200500000b10148201031583c0d03c9070328103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 181419964 1250 181418714 181418717
    0x4060308040b0a1e05091e49060b0108040f15020d05041113060303170a060f0f0302131406130e070b0d0f05060922020414040b010504050105010c02120703051905010c0e10 75
    0x700e019416500f04201d000302c10501e2300403c035a000540c0b007482a410103c154010941009003410880040d41c96280548001e052258800c44803000560111040d0502c0a8448030140c01d0004116000003551003c0d40c04465010440803016a14101a901500400300300310050100e64038644014003c0300c2c6810000118180c403100042036101c0a410078801018072035010008250341d0b008281050301a404101d100321510850300c1c0c901038582c010368071603821880b190247e03070300d80e0010040d45080c8240803030346003600c42140c0c00c00c07001c0c18418100108800c80940b5a075003202e003424800c036051911121021450902848815107440c0f8129600c042154407101d403825143ca244404c0c0c1d0940c2d0b100075406801c0c16800071180360001480c0340103500c508406100c1d0790304c510400090390701c00d008460014002c01d102c03402610780702d86d0000d51850301d0b506035104035403244c4a16003804031400d03500056401c045c00901c1005001d02c40c4400d5581235240070b50454011400085618155210880 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 181421214 1250 181419964 181420009
    0x2903151203040b07050609010b06040e010e10081b01080a0e0607050c100606050a0f0e090a0f0204031502030f090d090902030414010f06050f04060308040b0a1e05091e 73
    0x5000101001114043c002e000070311602d504042c07500d551381d807000302c640020755400c00585a0281c200041501c099601200c5559071980c20102074181010000303040100050038010005500c12061141c2900103503062086000410074200241144078003901d00b48801e803030500b0230381c4042c001084007074105680d8900035a4501c0d0030301c41e031460b0407803065600032810700d002d100160107074200004000c40c0440b03407581480c4a642d00300984082c202181b0b06508942d440c0000f0f8000310469114140c500c2c1e840400504081d2a501d4084811000c00040900d0a07030020038080c0d2003558104250b0301076140b100800780400e4240c801042d000003403040d1213042d6000301c040b80400c500d007240a41f4a0714105c0c000c21218120b5510b80d000b40c5218490317540200901c0340700d004036040c06d0159000b41c80d0005440c0d440c1518241c024905588488140000c100340040b4504000501d0100d1142007041550f405071142000810040d0460313000700041a00c510480400c40144c66032480344003c0403107a11401d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 181422464 1250 181421214 181421239
    0x151b030807140c0c0f03011509020a0908010e01020405090907080a0318050d0302060402130c02030f0a1103040f0816051f03060b07050f06062b0501020f04290315 71
    0xa48401e940d030001510552404102440041800130b4002c03030400d802c982c04102d400c0d049083c1822906e8001c610003000c0005001402201d001c0e8005000d80c00c00c91078410103581e96040e1081c00c54200320042c03036250b50005000c00040c5003501c0030a810103c01000f60403124a00940c1d10307070340c8261002c01014403a1165504051500d88003d240041c04041d00b454554a540e160083d00c5500440b022031244102d8103c05000d64000c6c0704044030200150001e51401c0058032411000d074000141050070001d520b10600c44044080c40130700001c21108071400c2d034132410184010b04180c000780050303c80451400b0100102e0b039aa81d8800e5825502c0e4860542c10080e00200b10060000c54110403e40c000c0042c20304100500010388080045402e8107032980d075251f007010003281245944050309034500c0f5248500d855240704030421b0f20248140b000510f8250145010400c07600300d5840380c820316a5444103500010845440490050b111040e210b15501e03064500e1a00440d00e110310318001c0b144220003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 181423714 1250 181422464 181422467
    0x1030f0f0c0806160305011a070203120f070302070b0901050405040f0902091302030715090b030a1b0e120106031e020d02030a050d090608070824040e0304151b030807 73
    0x191040c280c105a2440c059501c800070140e480b44240c1e01c145030150848034000c403040c8244a41c0b070689400326016414100c10ba150410f650f00300070310990b030500402c04101d4050401c4002002c403105a9040151903144c5810064148101c03941b00510480301084900307204e82c3c1c058121020347e030713003120000b880d028802d410300010140ca00d4000d4008420384188203510951035043c03c1c00901c06c80c101c42503e61507151200c941003003141441c011444000c014081d114800c03000d180e20581c0746400042c01d01c540325041c126a105242010042100c45a50680381d080090446120030343c00d0f4001e02000f4030719554010441181520110101802e940040c2159100c00caa500e0b601c0c1c0040843c1c0b981390490a0941d111070001440d4400300305e01e81c1001890b903000da40184c0c4030301c00702d48610815684041c05090651909404203c040700350701003d60b109e6845104050340042d902009507122810303c6a0007259040b12800c80060006c01e0036203115a0721842900300c46030358140341540741c079180c0000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 181424964 1250 181423714 181423733
    0x90f06050a120906090515010f0902040b0318030c1501050406060f121a030a08090f01020703030c110a0e070c05060604150b090303040b12041505040210030b01050913020d0c0f02030301030f 83
    0x28020b26070b01402c0018211251315400c01416209c0524030741c0116580e40d24008100e00c0b4511a4040a881c00e0001405581010600c450340703500c42420b40303152810160205e81406940407460790811b4020b401070142c2e040522451000d418039003031400e82c060030741ca405051411242c2c20440e00c56101e4101b10008004c03109442c1c00c1a1002e13049917003a410300e1803c601030f0381202408501524540c12009029880000c2d00c0084a8040e100d0358500c030007540f101a9511001c46d08290400c0405800040300603480d1f2800380b10300d40c1380d607d5943d080742c40c1c60502c2c200070001e07040d940315030b0a040190b11032300e02c0a507612044414081c0469511231450004c6170550081e43e020000406001c100030741c04550305000030307110381d20441600d1030f900003410354030302143d40c03c0d54043d40001701c082511507014080d602000c062001410580d04103c021000103080e452001080603401c2c9c0c01149a400c214030324040e0721858402c40c10304600103140342070000d549000501c00607140141ca1017a00d01030014020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 181426214 1250 181424964 181424981
    0x1140d03031d0303090c030703120305060303040e0c070308010f0f0e0405122107080c0f0309010e030d1409030705031e04080106090204140f03190302030f0406090f06050a120906 78
    0x4a86a40b8459000c1c0e44035101d420845114803240641c540e811880d290200b010340030b07170b0342c050808e44114903405d000301d00916004000c0c42d014882004082032030404c141080c2d1041e0108400c243d0ba030140ca1030b00800910060303012052120065506100380382252441d079058a1408580007140e9031a414260b14240038040503d49108001486001101841000c03005c04959140f00440310b40b80c02c0070403034580c5022542464400c0d0148141000c1e00110700c0210340140c0d210001103040d8800c4080c1508592003090801003141e0744500c0030001100b60313460641c0c041c07068405903047c6100384c0c403456121310903608416050003000c640943c104485805940180010720700070030407181c641c030b104c0c8000d500c54060003200e10a0320f21552035074504a04c0c010030188014004d003980e9120160f40007504241d04030202c5c00c0d40010300082010018020180c4000c14035540c44032640d42c64081c8554507041e041d0000c0e410045c04020a040c03031a0466500d0303000324010007002400c0041814064000c00610 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 181427464 1250 181426214 181426241
    0x30c03240e19052103040b010b18010c020d06060b0c0106060c1205030709080601030302030a1e12150918020a06080405190f0b040b160302040e0a050705160c030b0601050301140d0303 80
    0x10800f41d100380103001c0610300c11803048a500307d40c0e0f40c0f90031400601d270280319a107104035680003403600101c1d4420640d61240e58170240c03942280d403407241e440c103098134100e41040d00f200741c02003140f0b1f039204000d00440009280b0790510710f034511416154400c4030100c10b2841818440000041515540b10b905c56000911620082d0f07916940c4910b0002d440e0350001002d18001001c15101041c980c0204251048101d00760306d0b80000c54803081c401c41e000d00319480800b03401c0b40c1c60703400c00290b24441e4010702c800580c00d09060003160500d17104110b6a020b9682081d010000c4400c01c01000581c00581d500c1000f404141040035802145402c28030000303480e40040942140030305000070002d51015541c003a900079640110002d21501c02182240118480c4403030f00c035841c40124481581a900894008440c0d1801514100c0e00251610002043c003d00311144410319404005000000f0580d5030002000d103007130b61640d407501c2008410600d428400314803c007240c5800c0c2c01050f0099200403441840c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 181428714 1250 181427464 181427503
    0xf03060501050f070b0c1219050117150a0f0903181d010905090109080f03151002071e0314030403030e0f090402040234020102060901021e0310030c03240e1905 70
    0x9130250315000f0340b00e140c2310a0002d04140001c079500f0500040d41e0070402546000b400032118808402d00004809890710245a40d105c2c03a0320b1805500e0301500021500a445810107040340e805900d2900f041507001f8503002c1c041c8801480b2403105917040c1411030740803d41c082240d41710b0511090045c01042001804110002102c0b030884d40000c000c0d51003001d844c0b1a42404008003018804021041e101c071000603049000c3c184196a003e54100c2c080000380d10361140000e0b02c2e42d4640c107010030044071000582d400403900304105a803000741503a404130103441030131211100c0d1002c56502c500141c4000d11450b00450840c0d501c1e00002c00d0b80414071201c22454100e0300603d0b0f2100000043380c48168018010440000c0e402c032014001c480c02c0b44107404800c011810780c8460b14070141c0001e880c04000a10514002022914207a8900d002c5c4d0b000e100410f20550388150000050502582030404032414070900c1e400c801e001081c9041c25260544107001408180c1c6401c1341002c1c042010441c06085 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 181429964 1250 181428714 181428721
    0x6140c03130e150d050c100e1306150302090307090e0c041b0e030327190603021201080f0d0f0e030709090311061303210203070f03060501050f070b0c12 67
    0xc00c540d1450040910a07054243c10900d103003480801800d890000d00168080000c51156041513262a8035162540ca8030244480f42d00000030302d030008101140d480345440f40c4050180801c0f017012904112900c0c1021407500c2158000f007511410710b840380c207050660307800d034a401c02c0d0401d0100300c5140000a200b0071042d001e6411100810481e143c803030000442d81e44500415081c004220307121640040c984480600111350030080c81c55081e00351f6034210f1201c09283c5075072600b0585100160109803000740c0c481c07075007681c0c01c3c0d800c9205030300021344c5a2041c1d19070782c0040008030320410603030007a00d0320480300303035024000381c42042e00c240d11550140b01b07501000400084c150f12000f1058826518155a020001e607480d0f074582094030030300e0342e8a120740452000240102e10035010012070842d900910440c2014420498000f10380c12008241c0c01180b081c0d94541c1885500b01500003400d05504090b15800c1c01f92060142d6100208121a540041151940c512042e51500042428410390518 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 181431214 1250 181429964 181429979
    0x70e270a030207050a030b010b0c0102040503030c0102190c020d061a1302040f06050301051e010309020907020d080603030301181107050303130c05030303011503020d06030c0f081606140c0313 84
    0x20000c15070050140c120045503510781060050704498114942d845541d082c500090135550000c54505065903081000007410345051001d00004402c0400050321060301102516413020303d54101001c01c01200d414030300581d11080300f900c04641003980010b11074605000100000e260054056210004084005400303c468000b4010307a00c41680c2100120f55685041e5000c1c0000e00905074046c2182080c92500f01e403501c282d241d802c105240104000307007144c001c600400400ea0f00000140c0100c4981803d07940c00680c2c20b90022006c0d0029881d561411009800301c2250004260030140c40f00850b442000164055a0b1025003100a50341d99003401c500f0000ca4415050040f902e0038186c2c3c80004942c40d0100c2900c0c100d40e6030184a403012821a07004800941c02078002c40c601a030307a02d20110100d8500031070080070380a0a4180c114807401d01d1202450600c0c1034015490040c00707800c00b40050b5034055100d03102812014130b816200c203035000426085009086408070f0301040d4032400507050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 181432464 1250 181431214 181431223
    0x816110709200304020d080705070b070b04060b010e0907030902030a02100f1418010c02041803030501050102010b240703050408010c0806010f080402030a0305360102010e0d02070e27 80
    0x14400c20300d072079004076101002d40460300040744c01a41c80102c120412000c0f90102c2c1c018501c9900c1081910100c68892080226503003140740d054034100380580c00c1008000040c0310b42c1c0841e020900380701920100c1100050074160009160380101900e5114a0003151010480b1600d01032f4024243d000c08085858020709c0d2468a425420004601e0b803da00c448803a46012210b0ba650a4080e0455841000006640c0274402a0080b038209039660b406c5040c03003401002d00701000b4031907a008901075240800090943d05c42881140c4100e00c174070f22840706446441030031842c0581c144806911207146040c00e03034030350080340d000140d0365007449007065280e644680350610800090326005003e82045608503910780c2c08850081d0980c1c000008940071074000c9000e81070210302c500120382d40007146560543d00c8c0e00240c0c0c0c440300000c0f94040d821881d40c0c081c05001a20110140101062462001c1c000e641c1c940500c20024019803800201e2004030701c0d25586d99458801e800c004099040000195544 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 181433714 1250 181432464 181432481
    0x150c090301180f0813210b0618011406190c0c0f0308031306020d02070309090608010506090a05040302070e1801050a020429070b01180506010f0816110709 68
    0x303500e4146041403040340b01c15039510300c1e60400550314442d9015900c075601d0b58400107030844520900000020f0309072910390b210680e0f210916115140090310314011013034182c0a0640b80c800d01030505e4030801c2d246c90060a604594488000000c1c2c0503c0801103502c42c8590030788580242803041c1d15425454220280c906003134840c418805030bd40d03032080140192000c40c04001d020240c2080071890340700081d01c031240c0190180200618040ea10396a00c0120780c40362008802140354550300704511183d03072083c0c0009102e0301d0002e20482c81c1c4600000c00c0104000c0c81d10a5243e500c401107001c1c0b520030000c030009410560b40c0495142855507003000c0322142110070300c10780d608140014200c0d410a00988003224008849228054102100c12503868200c604216101c401801500003007081c0380c10a5000b801d00100c00e54041c0010100107050310302c000c010070b040c040303003400341022a580b240020780d11003011240344c8180c49058004a80100007100a4543d43c495208081040c42e0345621a011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 181434964 1250 181433714 181433719
    0x20f04020f0c0c10050306010e0a090e071403070302010801061209021e040f060602070611031c020c1e06070507050a12020c030705040b0f0904031e0905043b150c09 72
    0x10003600c003008120402d04c104520000003401840802c0c0c4c1c0394054410020402c60003040b19403400d48400c4038004403607001200c1079041d80b1000040001b03811070060801c0078601074014000c1541981c00180c4100018440e1a040000001000e0225a43d0358484c006140d0300808605031032400c903070750140e50f224184120344554a0a0b40c1001d00202c1882480121000754015002c1c19280000036200741500c5524480385d40000c1150525111110300e4448429410325001621811003030890b0345080e5480150380030020141c1d100780c40c0c3c03040004166500003120315065540b40014076100c0d0510307141010052844020400340d154113500801c3c1c1001000c8143c003203071000d0303550318200300540d52030074003140e00100700007035100c101c0c24040c080300e5225020b800e00c070000c03000d580209401401400d000700c00049c1c080009100b00e00e42401907480000c0500c1603000049000c51340ca07000c010501844402c0e41c0100044103098140901c1500350b1502c0094000d4020701d0071400d50342c0954080c620251 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 181436214 1250 181434964 181434973
    0x30f03040f03120c0506040b0711070306060f080304030305160c080118020103180b060607030c0c1202010212041401030c030e0106030812010605250218070201091103070b0d0504020f04020f0c 84
    0x21043c80c811040c01d0600b60300300000302a16211a224035260383c03400b5100b0030400032401503009110a0400c003040081d80700d07403000900c4500c0d007248400c0040c056040380c1c03295007007080100007080e80704007980d0005004100074000300d141440c1403082d00501c0d03030011440354200010300248003458030311035078154004e88007031107184510003910103c1c0b60181c0c0002e019400481c04600d041c00c0a00141c0142c5210341040c1d0040351550702d6400c1002060340c062500d200c801d030b0601c0c003156070502655056a20f602c00b01390829050941128803582942001c0303040513a180101c00c2141e00c40d400c00c0130702044c500c00030803055849042c48006070303000b25540714090039020300018115114004031176264006031031103420f4041011040700c0c3d03100c800200741c3c0e000101003490100c0100560741ca0b4090205900005080883c40c034040c44080c25450000c1e12a0300704440030090a4842000c4030754612a5080002c0c2d03942c5c1c0c901c0061552984800d80300d40040c4042480c035010103200c00180f583c00040f0f41140d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 181437464 1250 181436214 181436243
    0x61109040c0e040c021f15050a03050a030f05120f1b0c0102070303060f05060403031101090b0a0203160c02130c021005100503071a090907030e1b01110312040b06030f03040f03 77
    0x907680c400c2c800d2030408046c400b920380b02c590007103181e10850000500382d10203170800381d071400001c030016829013095949820000c0101f04164001c154150981158180207050060401d600c18036154000c00e03442c8000403d10004444298044900800d03190783e032040f80d05c0320062030200f0b000350001c0000324080b903e400808a0115543c030300503421100c00806c0c0c0d508e0a0b045039400c45550000040c3e8080382e43d01c54805170009051031190b58810a1448030050f00e80c548450040c90500d4803200c5841401810107214000d44c03036601280011404a544c080340106407080101d240040010503600e100d8548002e129400c1c849004070404c840c4110200c0d02d00a0b10780c040000807521038549400156400c01814000c0d051107c81154008030f9410000707004034407003003c02c0c146403880803480000c0382407403981d40305503030031401040d040e110a030000c2d800c0000850a00707044043c00f0380301401f09070040000420030750f801c0001e040c41c1a005000e03a40c60b80d9458060001c01071203800201c640f01c0c02442e02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 181438714 1250 181437464 181437467
    0xf0105040b030601032a0e0f1e062a03370c020d05060a06050a1203050714070f0b0309010507030905150702010626060109020a020a061109040c0e040c 66
    0x39642610940c071841442c40c0c07241c40041d4002c0103582440c031400150405000c40550000c90084010805502c0c4c1510b0000703078104010040283d0929140300e01120a4580740540700340d0741c0f81c000c40000b5952195100705c0c4c41c003681060920403001c03810680c904108074045140201c06007541100101c3c000d6030040b590003400321054031b06650700d84400080300d10070100900c40c44160413802d00103040048040059100c042c00c00108461620801d5150f8804001c0b03401c241d000c42d001010300075210348020201d59002005486007160240a0f00a454a0f62000310014024000240700c140200c01c03069030b40e01c901b030103035400841d1004074035440c1000003000d040c001d0080300c0020750701c54041c064071458501400300001c1e0150600c821036584507400701d08500054080c00901c20a4100160300340d0700c0c09a207600e84103050f040415554010700c085006c00f50000f503c03540040c0e1002000c10b103454544001c5059004a05925070b201d400c03c2c1c000545a0380186094003a400300303880501c07000640c44c50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 181439964 1250 181438714 181438717
    0xe040207051f061a0d021207031a041b1809050106080403020609070f0312170112112709010207020d0f0b09060613021b100b0102061008071a0c0f0c0f0105 68
    0x4c2182e950b4a0010340e15000407030b54000d02181515000c01410142413100721518041700315010700c08259213900718040c0c050704c1c6110400e507020440c0c05000c0c0030030304224494064200300002003441401c801904050603420b40c094090040032404011640c1d4a5900509035481a94180c3c0540116004074145a00201b001010350b40d501c112558040d207155034243c070308140106004100039008a40006904844600b2402030480f8202c085100c0c03035a062143d02e032081089800d02c00d91407031620b070b0b08071000c41880c01c8200c2a0341d055451103503075141545000e442106002941301403001c0c111420031245010720040c860164003000513598a002d082d9503211816240991b2050080410b41e24604c0c6e00e0300203203503441200c8244001d4002e03100c050707843c210103640c0e1608841d8490080b82881e50b41080340e280c1c01400001040a210f2508030560b440703610b240228000e030031200900b0012a0312642c00c84400c43c075070008a80703008848030b40040e03c4240c0b520b0032920501c000708000c11550301c501c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 181441214 1250 181439964 181439969
    0x1b06040203060c07060921020f06090c0103270305041d0f040605100e01030804140a060912030e1f02010506060702090f060307050303030a02090a120812070e040207051f06 75
    0x7402000c03662550014800a80c11010003150880d444081741400140909401010000725981500ca010000d44000e42005440303881e005003a40013804100b203900c000907030105502404c0c20b0000e10803010004000c0d821801c1d00341c481c0e0710f84000b03a2010426034404018012a00340183c1100509410000c820f01d02000342c0c0d51480005500002c98089030441d440b02d84c00500340c401c0000840d9031140750b03d00c400000d80c0b0689031204003150801804581c8040030a00c81e80c202c51400081d400d051001d090340c2043c0c050080201420184102090300071480c50340f040343e00800705040390503009041d4440140300d4040030010350810b4046552402d000b016221001d07801013500000c0c0e0b4640300010800c2c00020181580b51140580c009040c5e20284011400fa1000810240e41c41302d040c0f00b4044100b12540c04071900c425134000440226140006403411030004900d4440180c8480d402184d20141c4103c0c2c1d1644103100090071010084001074040320515116450001d041500c06001708507002d52 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 181442464 1250 181441214 181441219
    0x20c070602030a09051f032711040c02010504020306010e04060204180902030106080d0c021c080a080405060603190b270102040504060e0c0403151506110f070b04050105070204140c1b060402 83
    0xb044810036203010340c2040c21201041000c40751035112175000311070f140723000c2d110640342d0514000c000e68060502d4084d2241204503800240035500701035010a94440051040c44003554100c00030404001440d01110010305006003c42103240301780c210407000380b1160008074800e42c0b9020b000500000041070640c400302560700c0312442d040717144d02480a80018008030170304901081011200003a21040170702001120780e034039250a4905031515602e804006024648264810300310030f50a111a043c40c0301503e07a21040a9005446098455220307106104c5000340304210f141c40002d2000c015400340c400c440d400c9409103d0555644d61001c00c0344801c0c0c2c0d8070213011400b0002400410b05070004108400700c3c0f5000040d018020000518502c140c0380c2000740080c0300c4d0501c600c0400b000300844551606200c1c0685003c510700305800712184502c0c8503180c14040302091200942d44d403684405144140d5025440e181e1400c201600c40340e60200b861200001d41d186030005051500207807582c8503aa01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 181443714 1250 181442464 181442509
    0x50309010c110613020a03051603050d3b0904150c050918060118031b0806060a0e0c04050d060507020d11060402011d040e0c010212131503020c070602030a0905 70
    0xc0000d4060489041304080c0d030050040080040054020080d500708144218481d0700070b0741c11450064103140302c0b81803d008000c0140c07107440c10101da010711409818030704103449030301440300b0071400e09111188004552200100c4100030501001c180c4031250041520b008000c04403662034183c42c21701807864099006010241c0d0120401842d9080c02d801080c141041810b118a004e64a80c401d003079600100c80c20f58100d10610b91100c4640074403030103008c03150040d28440c41c2510103e619041203204400c030f24801c4501203030080300b074181181e01800c40030380b650540550300d06080e4042e00e419a198001881400c00389020315214560b091074210051001c0c2946488507001102c1c118420000030141c004a0052006290359a02c00c040c6040220009408502c40c420b001900f8801600300c2c802017403000704014502000c50343c04040640b07903a0003040c1c1c9444944031040f0024012008448440d11501801244560b00080509521070306a80d031540c1d000d0b1a4070510a0f81491903442c5400341c1c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 181444964 1250 181443714 181443721
    0x50603070f0e132301020901030b060a0e0907090b070b150a0302150309190b091b0f060f0f1210080703030f110f070603020403030801140105040618090507050309010c1106 75
    0x240d401c4443d8060746000d500c0701d41c00030b100300745034008150000140e0340c0000d44203000c1d40c050003078036200d0600b154254140707080d07000054101c0c4401100d40e03100da034140c4000340c5820700a10907034000d4140d60300403585911240c544120344180590301074842c904404540d03a40c0c1d10b0481900d40503668060b00046040241c0480b07610b85400240518200d40140080c45010b00f650260344465140038086034200e40c01c10284090410b45001c0040341412034600f686000c41d140d1341040d11044106840c0b003507548c43c0c190011400e60044080c051410303c00028007040240200c884c82d405500d400ba81d42200540e0b581080381d07114401d00c0010086126800c15004103405403054169014551040c1d81344400c507070744060300300000b5400241c08651701140c01e02c1815408038800e4050300308a800c001c00c581036000040c2c0580518030035441001080346450142c06002c900900003400540070a210364146010040c040b6082101c400c8900c0d031070a0003044405210351291100881c801c1c018200c280c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 181446214 1250 181444964 181444981
    0x70f02010804062414010206010605090d1a0f061305040507170a02090103052107020a0302060a050d0603030309021e0d11040e0304090f1d060127020d050603070f0e 72
    0x22002002034504503528100344013501c0c603030b0107052000115000c0a030005401c2c03803241c2c0b102d280301d012600c0c11588800d005104582e0044116140c1030b5040324043e0741020b0a180c554a0b1100070702d042818801000c090140703c4a100038454081e41040380c00f0014020000c100104480040390080c0ca07561092004100d612181801c50040440c000f0540d0108100c0340c0104501e06d00030380c0200c2c0c4a9010740c0c20913034085448922000c4003002071f001c60b0b240c15a19000a990340c141030001902c5800d00190103915030740118102c84811011600c24401d81d552810094020104050168040e01e03403140d10340d124000c20740d00855180d81c0140000003050040e1a549110300803200c5046d0013030390320032048203101c10400c0608010041d50b5008035011001004000c180e401c840d424008a510f0940080c4940c80045241c0703040d0340c2981c02586191a007007081c2d403952001d030484003802a20008600768031520540015104e04016400c4984081d0343d00501e0300884c15034481e40014210000101c0d0450 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 181447464 1250 181446214 181446227
    0x1808070b0a020c0f0a050c0a0e0109270f0308010b030f070804060b120f07050105070804180f0507030b0f0922150e0709050f060108010501300204031106070f0201 71
    0x146090720040c1000c1030408220f242ca4840e007190784555203c14411010404100002e4200d040180c840c503144030f181c544a00b1079500180200407019440d41c0c400f007400b00d44a401e0103400440180a2801505035050544a08030505010360004480c0400440c00f00c0001048901440411409049669a03040100d8031050301400854401d9101c0000c030076980d944400d940401494440a8030341c0003140c0200502e405210382c0040d0600c01c042c0031190200e1001015282164400c05825002941c600300c010000e08211020762a21032511050250a0798590310641d02e0703079029181c0f0780744280e00c0010420031010840c1ca280001c1428001c4555020a00001e800342d10710800100081410300d031350900584001e80c1c8808c5495010b5031040050903100d000e9aa0014a500707181355060074600300080840d081401400e061003040189580d0422800100b007100c107421003d6801220b0704103a0b0312000e58010b00c42922003031080c60a90659152001c211041c007507014070340404c490115801034621 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 181448714 1250 181447464 181447471
    0x8070e0606070204050603010f05104b0504060b03162307081201030f0314120c0307180803090a090209030a060e210904061401020a0204020d0b1c061808070b 69
    0x19509c9012190521342c4ca406014080c2c0a50b0b50b07001d01c45410566081c680054449105a6058030456031200c04180e07102400b1440204490020345d80d209103222400380c1d079075035110036045403038910001070602c0d68074003641c052014105c00f00e01e09607007503508031820003850000f44078282e60a450b0201c8402034900815600d845100b00302d080c8141c0742810710700340c50240c0c01900c0700d02a0003001b10400da0710590041549a0840202d0304041c7e0000c11761600e0b0400a194a00c03901001002c00c529900608180690340c0280c0c94407082c507511800915280d8118003440341c043d103407050001c100c00d40c89000342d40b025400179004143c01203e588501c03028181444050340e403400782082c0c50040103129406010342007900340000d561f400240e420300085030056480710784212021803da040e1130b031340421000c0e882a01103c0c050b0301d410900019100401d01100c6036030f030161040226401703d05540e003049600d107020301803c0102c00c00c00005107401c44000b40340100002020002071000072210111140c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 181449964 1250 181448714 181448719
    0xb031f020a1407060504020306061503070c0204020705010f0603050d02070602120a05070c060c1a0609040f05031b06010801050c0c0601090c090906060c020a150507030302030405150c0408070e06060702040506 91
    0x358500b00301c0225916442010203444960302c0344204029401c081080c40c2e005081680c12140075002207811144901016012800700005114102c042d036840b41c0660729019045002000441440301e1310400410081c80110340500070070542a4100d1b0012601004460264016140d2660b401589000c82d9000092010034013205000083c08a0008102000030780560f032103441302b0b594103007400034114188111380f10b041704030318007000380b551a103d00450708030354000e004250f02d6100380351a90441c0a009000620840244104801d01c1070008405041f2050b040c001c12aa4070303910540d2529201d040c4840e0001d50141e0700402000d602da034080c0241c0041c61402940054440e5a01030540d002039000000051459540c2825442d01400000c010318801501c528020b40401d400f80150140d41c0001d4140355001c0001003d03c2014080d84800c3d800c0621b000b149480c00501e002c11981007030044c41014802c003a80401c04052502a645c007442e401040e05042c102280c1c200006060b0082402d82c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 181451214 1250 181449964 181449977
    0x4060318170a02010605060703050904050a09140a020f0303041d04050a0c0603090203010c020609070611012a0801060f1e110601062307112713060b031f020a 69
    0x411078156080c5022900e807619140c2e5600015002400c0d2200f0303801403446444200320344030001c1d0f080411210352a800341c4005c1b4459071021560390090842c40000313000418007108040d800c0364007054008445200300c54850b1450448401e06659003c3d81c050541d0002c0081040b185104a080d41e071075206200301c04482085600e681e4041c3c80300c1541e8400404652550340c44001c5103403c1c01185030516243c4010b1000d441c060040c2030752890180b16440c01d00c003401604500c0c0701c1d029042110003100280d011031608100091480c01d004c020700070f002c002341840e40041000c2d48558805040070701c4965902c2d1410b102c2918035448040e0030410f82d010f0000c100807103208024140461802404c1c503494103441004550300c03040c043c064280c1c0000409908010200004e8040c1c00c00500140080c0d8518003400c1c4000b14525143d0110040c07850081402030401034483e454007544951144280010302064164034207040c2c1e21550034100c00c3c000c9106482c060003480c2e059001c6c00c0729128514005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 181452464 1250 181451214 181451261
    0xa0f12021c060e061b03091c02030d06030b07110304060203040e0709030204050f041403090303030c13080307061a0d050c1014071b080703050a0b0712061412010b06040603 75
    0x240c0458149200c80d2072103070081410401c0b8071074441d0103610720717060035110189145440000349440b05854030a00000070901850100010b20130025601b8001c2050b074200031040e01c90030100302d404412283d21000545202d1040b01c010710100c161b0301100c0c4035400031070405044c080c24420040300180b400c42040405e030f000001581c0c40c4d01a0a000c0c6803000c0348016507003420f040240711007100a14203105940204103040d03058600100300c0c0c0d0721049002c8c5068a842c0d500c0070007408484594002003007444080307042001c3c810342d0750001c45001503202011a100341c82a080c0401c0040300003014286811801c881500c41c1440b510710001c21900c3d141c180009407441d02248402d803c202426100d00c0007014000c2e4800c001200300102810301107000b090310034a540c4c1d5040d61480080ca0082087e0095804100d90b280903120b180c044500c200030602406440301c800049030803015035054407072503034071084d1192940188030702000c04001400d840e280900309141a070182c5802c901d040d46c0c1102c801c908 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 181453714 1250 181452464 181452473
    0x2071404020d06060e0907111509030721020f120304030302090d02060a200f0d11030426010f0c0e0d0c0b031302030615010207031101051e03060a0f12021c 68
    0x83c0f902400c01c035150003802d40c00100900010000c010720002c00c4c04600368403101141d00c0024070700560807040456160a5a4a06420342540100c4000407d4855980e20b01044440a510a0325400a03035a080340c04a816015007507665229000101c1e800ca6010004500070070711036001403001d42e10182406407401c80795800700f2032651100c010f0341d0004001000702035424007030700c0403040e48080d011700502c56080d450411030b8880e442d5000440034000f4004802007001d0091041e140207294051340d5010052801c0e10043c0e4580700e49586d581254642940a003405203a4410604142c0c440d03a601c00b151881c0d0020300281c80c440705400d03954112403210000e403c1c2e103500b006604c00c0a213422190749264041c1b0506280100252002c07007010054103184800f642e00044010489810807040c1080b10b46070b10040c1c506108800414000c959000c207418116030400c3c00031401200700f620034a45c420354038140040c1070042406441c5207484080702280c050702d04030443d5000310500d006000000412a1f48 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 181454964 1250 181453714 181453721
    0x50a05160506011a09060306040e1507090e160c060b0103020906070f0c0b0301120303020a0e06031018060b16030521060301050a05131419060f050702070602071404020d 74
    0x3812555540302d2801846450803034448070340703540e080241107400c1506a0b400a03681e0300000b0300480c02180e55007c84600400e003046140b002c0d00c401b041c840c51a0910b00001060142d1600901c1a40e20900010541182120401e2a01c0003110794a54031002d0403990b4103009003050500c124101902400701c00c0607941c5180050584c1c0b4411881c1c10003010384c915005540c041690b0101c00d4505c4e0030701c010850400c0f060320b840300c815810726006a079141912401c0e18000304060800340c10610201c10410a4023400000320155541072a200c0c1500700168085003e0321000c1c000c88074200010300243d905c4100b00101350718418801e080032030a10701d443e002280240341c0c16020f1528070b100c034010701070304e400d0a1041c0b6412084440f018020341c50900d103e40c180c202c0078503008242c007210705c101c8030a3300030500c016507580c00d01c510300c2801c000c014244032005d4404404440c480620300004180c000340001088011a8501e4029003070b860314000d041c42a401600003100d400035006c00150466914510 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 181456214 1250 181454964 181455007
    0x403081911040f05010801030203030a080402030a0f050307061d120d020408030c1005220b0a0b060307020c0102160f0b0f070804030c15030e0628090f02030f01020403030f050a05 78
    0x200003503161860070241c3c0c1c245101c02d60055046c41100e05c018400742e20040101d0390a44c2d0300d0305001125480c0e13803020031300d01103140740050110b00c42100314000b0072001100403c20940510018400d06000b41078800c440406801d1540b1642d10045842e0554684840984000c1600000c010306166540c3c1000c1c0c00c585c07005130310b00115000031031564064810703403149d9a0001090320116600d28a4400510110403038200040c0041c1603800000701d0008594001d158500310103007410b0380301e04051001035921184050000e0141c0614550821518182860403040710301744031700f0842880c540010241154041303c8c540380440e00401c084400708080f04001c00055200c2d900c624209450018016064260460350304109820a80201c1d0a181c3c00114180c004080d000c0c0201d5003411003030f511a00c401e40c03055605d02c00d400e1051450500c603141000c240380038001e0f01038485c516203804030790f400c0340b080780001804901c0381d11010340c00c02e01c60b41c060611302003941032a03841c040c142c0d01c0c8880050342d0305 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 181457464 1250 181456214 181456241
    0x170f07030b04050d09050a030206090f03100518031e032a03012d030b070909140109110c100c090e0907060e0301060305030d0203130f06050a050601051204030819 71
    0x21002e1204001040008007402881e9240c4a151103051000045420840f840040e100300320100c3c0c1e0f012559100701c40000d10f001d0040c100c0d00341c1c0c07a1010b070139006040c0499080303a01e175091810b1180070b103001008940844e9000d00403840d07080f1b56100e900031a5080608404040030f62402550700301c010500c01c3d5080300d4a50800070740c403503243c0018500e000003c40d5460076203078218011000d5442c1d55405032410f80f50311000d2541c0383d03985c1c40300c12944034013190f1084900c07605111104e01907a09000450b0706a60146c41c06004580410004c05520320131000c00c2c0034203500079485405031004580c0407040700e003180d20f031142c4407540e078003d030391a000c1c025120030415030030106c0200075450304a8140c4d10b850034160001e0000340d00e1138451544900403d107941c0c18540e0000b00044480310800b04141c0e00340e600206410444841d414000006c2c04100c8030840300e6454840401d52a40c080c8041d0f80c0301d042c0e815244040f40c1e45540d01241c1d100c4000c1c01404e00c8062400d2800402c03160350140c051420002d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 181458714 1250 181457464 181457483
    0x180708030c0c0406050102030a0305090f01020d0f110901050412060207080c0d09060207050307031506051009080c040501050f0607210f080c3103020901060e0f030115170f0703 77
    0x301c1c221107081000b41154188a20302d070640402007071b40c000c01501e84188960400280360384d0384002040c20000f0f001d44244840d44005217406141d40c281d80300d1405407804800c1005481480344804400e8400c41d4001408190b091004010749208a4040903a25115800c0035041000a984020701a0444615050541c110b095a0003030260310002d00e6004200c0b602c0180796140c41d000119032103200d01c1c000944110385c500380403401020140c00120003004003804c400018140321800a2050940c0c2c080c2c40c0e01c0340100039044590349068081c6070b058450040c0711a00a081810400c81540d222250860b520402c05c842560200005851172002481a880e500704010072090002d02d41103004000706081c41c01801584407001c040004483d501102c83c900c1c4d40d4040d0b055681000c216441d0707200a5208500c0400414a25403040c42c40c04070a0083d901c11184c0c240b00010035098900308031001c02c005034941810002c06210350351105d100c41e042c2c3c1c26110250214065141058420382055503030000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 181459964 1250 181458714 181458727
    0x1204090f0c350f15101d03150709030507080615060703030f050910200306040c11010203040c0e0108010903020d180e010b0a08130b010510170f0106090801090302100518070803 77
    0xc01321007200080400c9540302d820041e01c60015180c01e03940704440006442c0607850740004e880410103d01408541c81000e08031b03217080b00000341030b01c80c2030000302e03518040ca11000801150005031603004001d0300765642d1224221a060000c43d4110040650400d81c1350801061414020300c1054054070340c50029000d240100c1d4039040c15103004600406000001c141c40070010982c0f0743c25a0f401c40400c580c0480c003503030081800c65000d03044281d2140716520000c10b000801a0718140b140848290340f800200c0d980c0d03200d0302e0138200c4100420240150b0040b5160941c407a20403401c100c03100070351413a0b40103000e40f680c42450000100341c011203d075a40c0080c08500c403d401c081400e6000c403142c40380616203205680c402064100c1803040c02d000e00c100d58119275020780101410384060803840e43c42c20152a2074100084d4601c4284580c03c0401d641000100720008180203c02480360141c009166601d000d484040c0200310050072804034804c9800c0458110106000080060520304c0c01140c8510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 181461214 1250 181459964 181459981
    0x311070606080c2b03020319030207030207140d030f09081002030f060a030c060e010c320304140d0611040608010e0a021603081003051204090f0c350f 66
    0x101201d40d071512030489188991a180640d00c041307551520340b891a401030240516082e4518002e580314000b10460003804040b25651560140c0380c014065403c4035031300b03952400900300c00c1e500e141086400c244c4610082004c00d004070041c0e280e4484600e41055202c2c0c2c3c44080c541440c107000c0400d0910b54001003482134602c0d1140105030061001c03501100c005155640303129140c0e04a00c2540300380a800c5030889a141e020304c502d4840d040c0c1001c40c9207000240c0100b84580ba0b84c06034644000306a60a5210401103000400e407000da822a40c0006d041078112030402c4840c045100040b200f41c1e442d0311501c21036120301409030004140c40d868440031035040640311800000b0080c03a0b4541107105200083c403102000b030300d0700c0c00c20360036081a035000e03190000703400e20f50f5580740c002074074610500305a41012224000204101c50380142d0070007d04161241a038141c80b5050140e9001075204000d14025038200c80e2401e0048100c20b40c0e074520746a81850103141d820f400c542036042c04508500300494917 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 181462464 1250 181461214 181461223
    0xb0f1003090c1406040501081518070201050702011e090c0807090506091b0306100507140d02010c020601030b0103030e0109030501050c13050103020c0a080903070807080109051c02060103080a031107060608 90
    0x7000d6001d03200f03034044507000102d901d9025034801c0d14108022140070400010f6580e200805009000d0400c901c00030216010110030030055178490300561030900018042c038070612601e80074050090511001100120092010f88840313401951541d45240000581034010005140105504c1f0804034052400c0c00400c481c09400801100320b52109031826000c201e41d9104413540448221040708200031aa0800c030b84501461030010954002040403040110000078105030340442e543c02405492100701c1c089880300d4081c0b000070716030f044240041c4000303030207036604544000042c07403da01525a29150f060035500c00f0781e41001610400503210041200707180400018180c2806c040d407070440791000c1070780d6404002c040540205000b0a000300303030340c1d0700740070840091944030100c40c925078462014900030715048030100c400e4861160010b60349401402d02c038100b502070f60090706042e031a545440c42d060740600c00344401c156490104802c090340d440081e006c02e42c000d041c0000c8403410f091500c1d160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 181463714 1250 181462464 181462469
    0x27140f030a0f02010e0619080a020403120206010e0106030605090109020f0c16081903020606091f060201050f100b0a03020307020106091109010f0e0a12020406081207110103060302130b0f1003090c 86
    0x39140c10000c00ea08808215218030840150b0b1030030030708c00c2c3d80300100d460081c020b503007001f408441c80c5807800008950000c0c00505880100c2d105103c03507680d50000754100c0c1e0306445400d81240c440c1c401041542c00a6000d040078050860003203103440344c4914400c1c01e200140b4010b055241c100d0406000414040000d99200840e50002d00003200454134060b60382d01005010a204100c6d42000810240b00080c43c00d001c1188402e46000311912864040e0103001c0844079601d044014900180405c6992047c4104079014034448501c2e00321a140102c002c1e52005003100f06541d00c0f100f00083e040203a200301c1c1801c0824100306078132000c1900006001d80c038124448401c04c142c6500462440c1c1c0d8810b008021149041a6070030081c50500c00b00300038103401d0380f14401601621015840c0310700e524004103001d52140361b090100d0700c0986c0055045030024000079400103841c03200344000c0d0b061944885c0c9c0d10140100980f99041e01500080e4803e0b42498119000a4585582400300400c18010101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 181464964 1250 181463714 181463719
    0x1804050706030e06060a03111815012601030f0305070b1014010804020f120f0d0908120c0d050903031e0a03060509010506030a1d0a1227140f030a0f02010e 68
    0x100c4e410000b00040301c081c0b06000140c5600031200500b442540d03034804d030020f00c64484003a4190f510303014030001411030030401518007150700c44400345070b01c141203442004600c0e0340b9920211103900f943c443c60361122840e00d045040c008100015030100d00c4842070188100b1240340c4500c1841c0c2400c0c080205000b410000c0f41c1070001c0401400b00580c1e038048140e140341800c1d2213100c00c0c00c40802c1d05915040800001c100e10740034074211010728a510074540000c0d501c4500c102c800c0e181e454034590000e0700c1111061021500007103a0548a10b220340020920458000c007260309111814038440c0344410311b101c4e815030045001554081160301406110000c0100304d4030101598035200c00b1607000e10005120b82e9010760398811040e01c3e5840410000e0540300d266003150050300c52490300c0590352a406e507500340401e11010100c0071805481140f11042c805203465424050b00d48002012210142d9840c0d0303a1040000e9040c9603a900e04028102d1824040d5445e181484d441d40000360070000000640d50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 181466214 1250 181464964 181464973
    0x40f0509060105130f060e01051207060509130908120f010801020a08041106071e0b0f0702030d0b04020f13030b0a05010b07030804020d1401020a0201060f051e1804050706030e 77
    0x3240410108801e0b0440b201130303428040c060310b2103151382c004052608241d1003503841c10074003044801c54a01e110b41079440c1515090740305844404199030f600c900d84203000015408200c80369040c01d001e6144051840d0500e80400d000311660b440340b58030340100d42640c60010007801000309505808001900600b0310000851074024907030b50061045000610181050060303101400300c035180c8404855409400c04000001d284180b01d0014025540c032000380c50980d080c0022400c11645a500c480c0a100c194008604d0100004000000303030160385501c661241c2d082c040c5614100c41171004241d40e102c01c03090f85100134114908651066030180001c43c240f4509001031102031442030440e030489405040010007955107100089142081d807100602c4444007e540c0e4543c0801500a0004a01503800a220311030b1103c0c030041041084e0700c5241d500c0b40c00791610032412810060404c4031801c026107410420380c1d243c010034040a5050302e0886803a4440b84003048555854803407800080300140150 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 181467464 1250 181466214 181466221
    0x60718080706051c0501080d1e0e0f03011b05070501150311190f0308030403080601080408030105130e060114030709050402010c11040f0e0c18010e0705031b0c010b040f05 75
    0x6940e50303014026030060040c0043e8214413241300210070072014103510340910941d81c60307928164440c8603c0f0340e043c0100d03000c20310ba5601d002c0740d500150001001540d0341900d854000081000e075040340d0300195010f543c2c3d440d0b0000184618505524115035503142d140d960030361464200e084540071a990b2000100020081c00001d0809915000489045505200800304003145080340a076a40c0010990741c600c0f4070000400c101c0e0780207148590302031703140c03281665246401528080350071500140300c7c00d010001406545003080340691032002d00b9100081c04040c010180c0c2ca07088080e000701004510954000d22145001c000c0c00e4050b00e8000000e10080c1056030010b132a001113410000c4c9015802d10a4004640b01c950110081c002c9030b03407052103a62800d400568a81e40a807540d0b034000c08070150b00007400c00101c0c10140c1224400302c880c0307005969240048a40f60009000800b040c4075284610b41c3c26201c8101030030609103980d000290150f40c85c01017100b242c2000045030111410030040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 181468714 1250 181467464 181467479
    0x90510090e030c0a1a010b090d080c0313260d0f031e090f05010e0102091309020a0803040b030f150f0f0301020d1e0b0409210c0204020c060718 63
    0x54044034115100429107541e01114541940608615116984642011841400001640d200c1e811070610385001c42a600c520011005210701c44405410420b940c60007400118410300a05a0403070441c141e07418481000c2c09000c0300320507940810f00e0841c180c41c040aa43c2d1000210002503401c00004080c1c481e00c0c2200034103030b04d000c100c00b50f00741551048466201280d0000da00c0550030b81d4802000f040390303075103030034040040c61070002d0380e1542c80c0c010140000081403080307840814000b03155940d00002040003102618100d50b0498005010740f80c0003035540000c20244c8094001e0042d0983c4038541100300744103060004007074415580714465614020740700c01100c00b12082c03090319640c1c542010f034000b0034060f01c110100940750524281002e4000c90f9104d402c0c0c3c0b440160080d050180d41c03408001c22007560045070018140b9a040b00c6100034461403484041c04ca082c090500300540f001e1f40c1c00141c12030700044000c3d0030a40140040140190380302d401c1003880d80e9403100514009081241 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 181469964 1250 181468714 181468741
    0xc061f032109030b1f0501020111041206020405031f0b04051603021803030310050909030304020114030907030f0609030e010f0f050d0207020a2c090d0c02040b03010c0e03070905 78
    0x21004090341c00454218449105014440240d03401008003103460414901c907503030240e543c000b03800907002d40c15408900c1d5841805000080d44844507040e041504001d5101074994002034103c81c520341c00c2000103400e460600c429034250046004a00c062400183c040007a182c15000442c840c5103420204206071007840e44650340c0c03540f989401a121840c0011032902030400411103070b414480481084054842071800c0303c20365600741c841d825a501c03080000c903034900094400038003148140360300c0c1220f1f000c1e00f006983e000100c80100d4018070740d00d448000c03801d400f46a082d240d4989445a000505811011210300b0342d00c2841c26800c0510f00d07035401800e000c000300f84041003000002e071507001c00e0b542c1d40580e00300c56002458403092907030f031b420303205030208001003114510004003004c00003410a90700101e10401c0c1003000761014035410300041302c81944483d01281d01c580d441c04685000e032024070400359202001d4a8840350385400208143c644081a8081c0810394280410440c10410110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 181471214 1250 181469964 181469993
    0xa08041e0302100f03020d06150224010303110a060c090e090a0f260c030432040507140c070e090c010203040e040c0b03091c030e0d0c11060c061f03 65
    0xe00340030081c91003c1c4c100e000c1d10076002400e002c582030400120340d031403e20f4400c082d074000e550200c600079030520b543c180c91400b0010610541400c00001000443c2c01180e502c2a00100841901d0800c607990380d54000329000d415210340000c0410b0b00c14040101521559508513025200501111a0f50f95445044440078140148031405541c014110311200d00703044018204c0c41240f00341c0303820030000c038a03a41390090b120344502c2520150020100514681610f03107242d0403c40f08000e0102104140000f5040182040082080410030108651074000161441e02c01c001c0c05850705a14044c040482460040d184036801d80040501c10742d6070ba0000b0403142140d0045400b8103080d83c65061481c00e801c1154400d07410320342c0c00002c200c0342c044046100c100c0c5807180c4207410070580d0303150011802c90305410480c0c61076a100e0307500486101e0050350341c01c490030311802500010b000d000003c035800750054804000d2550003941800164200c0f400108a9600d802640385030651454032018400c02105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 181472464 1250 181471214 181471217
    0xe0603041b0801091b060e03060a05150409080705070e010b070605040c0302120708011b0c11120d0c0302070e0421050c1c02190309050f0103020c0a08041e030210 71
    0x1074044200d10190108075008001e524000c0220304124103294450302d403100343c502d002084554010030024000d0f05104008030014004002c1a0303103142e0307917100918000e0b09024146103480c661452998840c050601603a10601d15952079641c94602603140a039242c11038094000b03103600620014061a081e04c03400790b01702802207026117480c1000410401a030b04041d400c0700000e1440c1084100004299040703e030500020132144a055004401040d00d044242c000989a5410000402c042000c2005011f00c01440c64940c00340c0301090390314010070004c0b0100841d01c06011507060540500c4014010a040080220740340341983d95540d1203150039658442c4580c50840c14207995120b00d09468082c60102d0890f021400404940006148080b05240c0180309540c4905188044054510344159258135405112800d0004000841800c001c0365810194280030721440c808080001d01080341c0120a02d43d07440342810000301c504541d81000243c4c0e407400f011300304016114a002d20141c10201d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 181473714 1250 181472464 181472483
    0xf010b030601050d020d0504080408120c1506010e03062401030509101512050318010c0201200a08030f060f010f0c0201050304030e030105040614070c0c031511040e010305010b010e060304 82
    0x11000090006d01424642d0500c0904d401d0400040010500090056600711000c0341e03d018484041d0b500148a117484010880c0c12808102c0b4454428151140d0030403814100344405161074404685402c00072200e50502041400040e1001c500300442008409402e207000d201901e884404c6c5a518101443c0d031270901662861804000200c40c103c840103044110b000c407100b241c0f40d0034000e560ba080031171542c21982d14000d80094a6010b4208030f10541d9043c4c46600e21036040d501e0010b2a880d41c00a003007401d025100c05d541c00660f040c8000e5100d000a0700c1071001c142800c809001071a940b0f20342c0301d270621650140340d100c455042a443ca40f50303642440d2083c4c6d6a515450200c4100348c0e240c1329079401d9030030842030204110352900162002ca04102d00b002d00b44d592840100c41062480101401c41d0000ca4020300c0445d05404a401e800c9200f42d101054040c1d40e41030090485c6e100343d00c1038100321011001881080404c1c0216801c14030240b901034070030716002001440714171020f00020103000b803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 181474820 1106 181473714 181473727
    0x3030905100515040b030337020d0822020409050a020108060402030c0f0304050307020901080a0b0a090803070f0314100608011502191b060c06050f010b03060105 71
    0x200092001152540306204c0200010044960076000c100714003400a03424900400007041c4010b08054001007100040c20103940d1010090119041400c00303201c226401007806400c400184680544800411072030481c0262180c1c00039040350603c210300c814028013280c800c1c0498001c0c0c0301c11405960f18410041284070446541030427070000d2150309000303504e40d0041c681c014880d10450f890640c0580000e201101c0981c001000350303010711503143c2001540303c46150417402d10802808844040d80d2510454000100403c041082c45070fa8096030f948281c21642c11805074031000c04c941d04001607034a4035141e0a00507540450141800000c90306000d080c0d5044d445110390241c429540d60955069250400300390a940000445680e088201402c00007140208410785600030411002d2400324280d0f54010701e0041440790312401000500308040c200c1c2d40c46070091800550314007 = true := by decide +kernel

theorem cover : BRFrame.Cov 181294964 181474820 := by
  have h0 := BRFrame.cov_init 181294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 181294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 181294964 ≤ n) (h2 : n < 181474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
