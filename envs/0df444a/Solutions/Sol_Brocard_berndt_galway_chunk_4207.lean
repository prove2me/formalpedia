-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4207
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:52:29.300966+00:00
-- url     : https://prove2.me/submissions/ddb5e70b-b624-4d7e-8308-46ab7d822023

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 756474820 ≤ n < 756654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 756476070 1250 756474820 756474833
    0x90f0509060d2a06020a0b01140a09090b0402030d090e0406050a0605040203100602010c030c0c0b040f120203090306010501050424030204180501080c040b092d04110f2b02060706090b04 81
    0x700610341170000b0310541900e80d0f150f1100b40d50500500204000c01001282c1945d188042c240081403040f40400c80c14140b801c003404642c2c81158164041d10902c0d002040c45481103407284c0440d000741c00c0407041a19582c0d10704000c0c1c4009806c4008090325203a0100700c5a403284010f60141c0380b0b100d000d080725444c0c00e00c06801c4d0307001c00301000240b40c54201000c91541d000b5100c030010700d0703012114071525640e500d00050b06d002d0030074001e0100c07403100501d000782c0783d000801070903008411400c8504980e6a08011500c0340306600a03a5101c11541104c0d280c448005150000354101707504015081a0711013092254500343c1030401c1000301c0d10340c07004001071070040c401e4000032401507030b0610a941c065004200200d8020786031500d013401240b4050400805516101207030708080d174007082242000e0400d1804814040c0308140700b0816454440f003640382c00304285510121019014000117000d00510303c003103500450076a0442c401304132000008403d4820840751a200d20800c0c200b0f03051030b0500d41c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 756477320 1250 756476070 756476153
    0x30f05190e010203060a091d07060c0606440d0203180f18070309020d08280206071b02030d1713020f1302120405010b030c01090f0509060d 61
    0x1c081692042003440159200d100e040310640d403100f040490b9035208070311071032540304541d00e2454607030081c00000b04d0481d0b801140e40346140d004080c284042c5071501d0480c000030340481c0e080c42100055194100284500300b02000c2d66801c200000f030380c011003000184e41402e0007400c0c201c005070400200b0ba044040c10411001ca40d6000380d420840c00300034003012803998003540d00503038260b00750748002801c0f4511907040000c4031540a0b0141c01c07003207440c5c544444541c002d1141c040c1d06140c140041d1300c600012551000000c40c265004266548941034281c81c0094000c061203c580c01c070354001e10240c2c4003085081103422150b034a415031851a003001c00203010000d000b0b40d5a200300716400c0e20150781c1d880c00d82a00c401040341d00f00107001041d40c271a0300034460f544101c020080300174100010301c0019030220780d412505405680d0704d100880e004580401c6980503a08100c5600001030016040c144a801d82c00308028160000c40e604c0c507124203504140c03841480318103984155000c100300c40c484158 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 756478570 1250 756477320 756477341
    0x5160303050c1005221b03080a090602150105152521090e06060d0903030507140403020619180306090c051002100f1b090302090606190807030f0519 65
    0xb0001070a101020354402e01100808403901485c0d825041c0900a505040c200205094061104c10513582d00c0c0884071908100e4a1300f02041c28000c0006080b4000300d1003010745080b0400ba43d90340c3e803c102c104210381e50b514100d0004500d052240c4c4181451288100c0c0c88000341690031005c461551600d600c0c41004a1000e0b00c191003d480321070540f58201140305c0070303a80c0011010307995035548008101c150090340340c2030b21901e0801151000340f680540c07085000381d04c255a803040e180d0681040404500c02c0d480300030741103401017200c440607106580c14400815601c1c41c0c00041c511010308007034904100c642090312929940c40001c0100121039024200800042e00c48440b020a2020065241c007805928941d001d41c48000c0c0409881c482d82c003804c1c10b010440d12103280f180107510010060040e40c0812401400c0900c04103031140fa01c20b0580700b0b1b1070f0741180410304004207443c08a40c05500605600c05042d160440300c1c60202d668060144076008a281003502c80c20411076240c241d2700725054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 756479820 1250 756478570 756478603
    0x905010e0c090a020d1b030207110901120b06130203010806091005070509090709030c0f060908010e060103082506090201032f13030602030f0601020f010e07090905160303050c 77
    0x1d030440d500d5004030294400c01c107007001a20781da0030000c844090321600c00c02403405140a0000220180c141d03000d0807a00d405140008841e0015500340690f20000b8003511a45080c142003040000b000d24003d81d5100001404211020464052880c1a604203030081151600148104505008100b20aa0151950300820700807810a064058828414a0403013400341c3c451400286007a0b01811414000719030100440508680c0c400034100300c01824025940000c40000000503030701d50500a400b5040400006030440741d2856607042055802243c0c031040b0540e9000941d401460509039520306103000340401b09030160148001030440d601c041c940b021200310f621070f46440700f00c00c010b068074044640720709560795418009040703c0107580d907100524640c0008100101081c654445078050402a0200c6d10401d03041c04080f4283e84840000e501154880340c401c001c40c20b4203401021030240140181d03103140b00c00b1f40c020818414a50000e80c04518001901621001c003080501c02ca0303484082c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 756481070 1250 756479820 756479833
    0x2030d0201050f1504020c1209040b010e062d0703030218060721020a02040e0f1614060a1b0f03260a0908040f1206200d0e0c040f0905010e 61
    0x421100e842c0203013011840c0380842c803100006446030703812078514011141c1101d540310790b208206000d50f402a07981c0c41c0142d040940603042035004a55000962000406060902001d5421b0807810125007041c81c00c0810365941d4031001d050803500421505001313950241e5218103441401001341203002056019a404001040114070500c103000c841d44040004c0d209000d03a2910101c1ca0518482006035100346400c081c5800c9500c005034401003920800151003d520580c0e011406800e26481624011030301c0301410300241c40d11400508251815081c080007640c80e000c040525030800c000308482c0070311107100d2842415006515850250f00d905610301c2e0b03084190f40905550780000d440c040c0c01701d454149501c200701d100d900b030710050b00340c09850007101c2d56200118400140c8440b01134600a1070240510700080741c0c0224440108a044d074180e182000c2c8004c00c2c0e0080c0b01d0000419000d00441815412683d250b00603a220540d9540010411401c5401c0107401c40d08810040c1e1095400314 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 756482320 1250 756481070 756481081
    0xd0b010f0b0702060901080a02130806040203012a270b130918030507060603120914040501031122020d1a03011b0804080c0604030c1209050102070b0a1b03090302030d020105 76
    0x408885d5801c02c00e28001c0c80d1900c803092000e020380a4200410903210070400d020444440c00034445205600880c020b22015410345070302e417004001d002c0d200c0c50307469814421140d1a40903421507007040b0342c80e046091044556440b4185500426000614015030000d02c804004400407810300c00780107145000c0045020500100c0074107005000f00600748080480c0c800184445503000d2001150041c0d00b01580c5082100c0040c00c010550003911511184090f01c0c03926400e041c81810305886c0c5c0141c3c0c00720300040c440200280b4543c4003494503800c010b28401d050348003031280080c0c0750b0102c1c215000705c1c2c04060a0880b00840e155000f101f8006c1c2e26000c03d0012400145044c00754904032811f0018598483d814103015501c12103940300d869108080030311040590069514030740c140030f054206c4075801c03010000c0310b040c00203104480c0168001041803004000442c0105451041410311485041800314114024026184203a0105003000801c2055050038400c07a1360720303985072000708040e1411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 756483570 1250 756482320 756482329
    0x503010c030f140702100b03161401091703030a020c01240512061005010f0504030f080720030d0513030b0f07080f1b090f03010203041b050d080306060901030b0d0b010f0b0702 77
    0x4166071b010260b031180c1038210162010700101c0108000c0800c0c0d05c850341d890f1038607d102c040075400800c0c00100f20f03101c00565802075001081c0d00000c1c4001841c038507240c2c802d81030007a401c41040c2000b69541c800d0b007407441030080c04250442c0d540142030010514501020410000100320a000040d0840403c22404603103540880044c3d443c01d09001e001181d03898400c884900035508002e1646002981147c24054844080e21480f0b104120820841c1c0210a201a41480e1002d04a81607400041d1a44045000710060040a50071031211016103035661500f42543d04251001e4074134568000900040ca64802c100c01c5d40710300201d00509050412054103400e0507407000004c401c1603c0450859800d5079803400c02080c58000600035074890502d0704003081050349035540c1c1945884030010004507420048111134406412802c41c0703055a81d82424800a41c1c031840456040699950510070196039449420000c540a003881080b590b04150082400c01e21541008140c5d00d424044070300141e58 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 756484820 1250 756483570 756483583
    0xc0911030f0c0f122a16060209040f290a03030509010909062309060a051c140604030801050a0e0a020a0915020a050127080a090503010c030f140702 65
    0x381903079280c010359070319190000a030191501c1030b5200180099800d00400039510100d01811119030702420451170402040c00441e0b0b40d44a550b078a510031310105184848040116900704e0060a01521309181d420014085404542040704460381d80d500300301c100d5100716240701007000301d82240310010542c1e00014480414901c402003c200700012942040e911500d9104010b003584d00b07062200a03242c0c04c4000e03c0301c081441c00c4580c0c4490000c10100c0f441d201121358014003010300748881c1c00e42071509119290032801c1c10440c0c1d8441c0d03e2903d200051500d07032100168005180a4809418645801056140c040e807004e0701c2114402c40500100c500c1c102e0907500000e601c1d50061b62505008405e9861510b50b502c95400c19180e141007048082e00440c0000c46544a50002c0050554120125044210702c0c1588241c1c0c0c44041650700001d031915004011742103060915080711560b540c00282541d0541102d00c0002791034603d0040950042d014004840030780d0441e6040074038103100e00075558079 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 756486070 1250 756484820 756484831
    0x150901151206090b1309080406050703090302030601080a020a0e310c08070906062109030215270c010c031b0b100f061e030c2a0c091103 60
    0x1254004805030007406032440514644011105000441d079076074090703004103040b814580c000d28040350040020a414844c10f0001940040000c0c1840e0034040f0803589504805c50450500c45c6a07a030100250754100505802491454001c051011030703441804018200d075031220708030301e00500600a240c8243ca4038411924880d04903545141e5451135041c0d403218106001070880310301544003040b003410103c2c6400c1640c4441c101840140d0b514803040300c004c09004843c0c00c20b95145e55800540103595004180c1e428000e02c11144042c00288018541d001c0c00d0354400041c51442c20310080c1200750301401c0c400b06191001501d203400d40507001814800e0804801020030030b54000326040602d1319040b03a2909508512442c2481c0740c204000600135806010313818003d0400500041c40501c180a08520302c030100d0040c141942c1e10440641c040d0a0709042d03582070201800d8a20107404c900040a103c5c001d542c44c4221401082d0b04241c5001c4101e5082400914200600040b0081c104001c884c0c02c42c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 756487320 1250 756486070 756486089
    0x181503050304050f131a0102010e03180d0203010212010e01050f01090602030315060d020a0201050f0f0405030d020d14045a05060f011a04060807051e0d0207030305150901 75
    0x100005000990300f80c05c2c0c2542c05404074501040e22410990b8006a001004001c0e0020080781d04444002d650b00d002d1045079000c806000e05c520303c024205800003404980c40134001504000101c840120300c0c11007600300c0317101d50020100402c52842c0c803a41e1250f9015087c28180105424028000c0d12480020840c032042d24403c0d40090b40d0f601c50104441c07101d071144e9802c540b03c0200c1200203002c0c040c1941c181c4a0b004020020442c0203210307103000e5000f142d119009500d130441e900001d002035084081c1000c0c1e010b54030344406000d040071200d442c2c41288030f04c1c28060b4960b14100c60b4868000303070909420081740300f40c60042001103141e03820f04803940c0c8802c2c0012407400070f02c5442d001e5020680010002d0240000340322451303040c145005d040c0c0d08240b00503404a503078141d4106050140c0d05c1003e001403001808590002d00800090000070342880b8480001000180200760940c014114801c3c001d50010f648028154148030f1180c000c190308001000184c000800a5800700041c0540c5214 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 756488570 1250 756487320 756487339
    0x122c0d1e110705030f0309130501080a0b3c070e06030c0d1b09030b13050a080304050114040309090c110703020108332707031d0718150305030405 64
    0x1c01070410440e002003400034121030502c40b0140c1c4040d142c0c2c21078950706001c2d01c0d1030704643c0211665400303202d05950012008284c90340ba15101c80b01d41040150800b0440309088a0400c854009034012407028480000364100c00d41030300120604451008003400100081038024260301c0d5285c20031280c0040c1c400380c43c04c0c2c80e40c9014842c05c005000300304c0101001906802c00070083c80c1c00812010850380502000d0101e55558421803140f0318006030014039640010111400085d1a00003468019010314000616525001080e404428040da0103401150722141d04000e40c01842c0108191035615251034800d500d4a0a8184d40c0e603113070380c08001e06004110000640b04041d0459041c4400e1440c40c140720190b00324a20b8501d1070703c52406140c0a0720701481090a5420003d45100c8602e10f04010754500717699603e4202e00828006110020120700d1005045401800b0402800034211031424203c00c496500000d070112000744101e0044680010700030030102b032010050b201100c0c0251000c050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 756489820 1250 756488570 756488597
    0x20c012618070b04080a020f03061905040812070309060f06050a0504090305120403050414150706050709080a06022a07031704092301050a0510122c0d1e 67
    0x14030b4250303005041030074404180000c5411002851040540c02500d84030003001c0c840c030078192641021145c20342800c20354440c81d908140c042e03000701e602034040c00d081801c141075611120050a0284c07041c1002923140d50001052280074812201c0c800c000503c200002c2d0301e020045107452006100e02d510941c0d8400901e011325002e20104c80c003070b480c01c40c00d848051409190140441e04240100120641c1e009952445800c02031003581550b803041c1c111a050000303a54a030b0b000740c00c005241600304003600c070001810400400907031380101d00c00d010168862207405090507004100c400f49000c81d80ea6161520122840421034038241c82d049850400c2030303112142d03894000d00c00c0e0b078890a07404d46403543c1001940c003c0400100d100c0842c0703d8042c103e991350802c1046c036640030f01503143c1c8407100401c0e12051901512944000c02103455001c20004081c00c140000b920036050003c450010070320020071081418054480c070100d02c3c0c1820002164404a0811b09203c6180c0d82002c1c820310540110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 756491070 1250 756489820 756489823
    0x70809090f160507080d0912080c04230a0503060a090b0606030c1b21070311010c02100c140c03030105091b03010303080702100609020414150901030b1201050403020c012618 76
    0xd001460508090044005a20b000c000c1c5a6410a450000920181c0824ac81400d80c1c0100c904031540c02040d008941c070703034010044440091003441503004603100c0c00011141c60070310055101741203682d400984140079051680400d40001c00091194108000f00302501500340150307441448001c440c02e02d05801081c0e280c5c5400008080c056441d8442030007558007100c410020104a13100703a64a100c000b0138101c4003806d0f84c0d460264000580c0104040c40c1310384445038000001c40946d440d000300c8020701d004c41e10090354419a008860f9400000c018086d6040140740d031600990179980172a102003a012415100f4081800300904100026001c910b13400e2007040010520300c000c440c20004240c2d9a0b111030000e5106204a031305030090405ca0000c07900d440c0c12070203c8440011405443d1012240c0110002c000e204001c0d40d01c01440e03074012511220900c036091141d0311030303002400513211190014080040a1140d08800312000c5003680c00c08030019545a0450000d9034000414010001c046 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 756492320 1250 756491070 756491077
    0x40b060409050c1209010b040e0a02030d05210903040f150801141503070801080d02150f0a06030f03080f0109021903050601021009050a0b2d09010f02070809090f16050708 75
    0x1284402c8880c0a00080c20f2040d1f01c01443c005088a08210501e103c0c07600c5500c07944101806503140d0406410425401d01500045c030780e2044c0b174210364580d82022411b03610351140c16108013416520101d4144510800019045d010f0451002d00c0c000d59450420002e001c01014059009480b80700003582c1e02075101d020a140c1c1c0d40e6000180301d5241c5c5089600181144024400c0c07422074032a9004009000f400412104140b01c5111040c0341c4580d5010100e0054030805080814160780d10780000000c9840c500d40510210b10035603ca03605814054000c551903607041e0003031001c0d00d01c1000109164410303041d40c1e00300440e00e8200441c240d0340f050b0050b42402d40302000440814244182030042210208a000d2080d00c244200c500c151196006018003642e8103501032840d4100503000a011501d002410f544080d03460700229555146002420982c0c1204500711000c0d10f01007080246172038284007503540416590a40c068034900041d0604044038040310807000d0110010b120b03428442d1440c101c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 756493570 1250 756492320 756492337
    0x60a1a0412150c050d060609051806030a02280603020906070f230c180f07140910120e0f19020402130b040e10030b15010201090c0e1005040b060409050c 67
    0x4100c8102c01c0d43c00a80346501c15008092520700c0c0c0a000305840d401001c151058076000303400c51541d071031218180c042c050409021035504d80301d28028580103945510b00000042c040842c00803020305030400c001d00309840c9400c032106150051103003031000d4849030140c4440da5042000b1307081050b000d007462442030340300030343c206080499044401c1d0100400a4012800c0409440040342c1e14100c40b8002502c00041c3e0300c000c85041e035200400d0030f03180308814034403800c41111407413450458200001864078410034900c6000c2040c8070501c2e5200c4815209445442d0b00060203070103001c07040f00070162250840d0404c10300804550b03901205540356a8156a81c4a80d4941000c0c025a114401200c80e50401d00c580d034800e5010800184440304410340460407a5030041d281c80041d202d184019031030b000a0382800c0c2c1150b58803407100e004030351110700c5140102540c000c101c1d45c3d0300b495081d562142d410ba4001e1400346051030507078041d44d2122811501100c50410780021a612980e10319519486040f50 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 756494820 1250 756493570 756493613
    0x14090c03070512010b0a0225092a090510020307050a0b1005040e060412090311130906021201031401020418050703200310051e09061c0b060a1a0412 65
    0x101d001c5e00800001c0c0702c1c07034825408884401ca00009030b1084055040e681000300f0300c908200304003089164004600ca03003040c503c3c00a6000761310004007801c41c0790b007031a0000240292030402280c10600d1000d80004854400b4501d04166078039541d99400700100000c104842d88000a000c000c28290000080c10300200144a221001290300781e03107480a0301e094410300b101820511081d8081c1c01200304132544001580b80c107070022410415490b0501041c1c00003103842d0490b2000085141c0300408040042011055244d41035081c205822440007220a981e684100003d004054080a140c2c0304850294000300c2c01e656001c50807400780200007003481c5981520243c965000f008080035521480c61031a40409903681c49007088110701000a48020b440e028080300a064240518903a52020b400f030203070300b0103a9030b103130400040c0600300006545000f000d000303214061a1500712580280540b0030644c4480b103231518103840a00c0703284559445030001d9902807041005000400341c410306c2048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 756496070 1250 756494820 756494857
    0x209060103111b120c060a0e0625050d0e010e0705030f0a0b1b13060806061303030f2a050c03031305090a0608120a0f0201060807060507060b090a0c0914090c030705 72
    0x2011703580d86402c1039600b03203112820079054021646000403110b1241c0d0521002c10040c01002c47c5050b112000d0641d0351042001c01c0009243c8074265002c1c15820740001340000030a01d401c03070b0500d410501550800d503c00d801458601043d01d4000404250203034001c80100900e8a40c248001e90314810000040c51b0f02c800803d00f1506004802c50100882e0025115400680d4902c000c0003036900ca040ca0000c01401324520a102107481034201d110030004a04010591902d6401090b443e60842240d01d039080c0e4070282c01c0c0007046014004071500f1803094008500f80481c8458541404440740284c0b03014044150004004826a4103c80010201c041c103455030540400c0c1e82e01810340c800405000850000c60040840500c140b2400c0300301e80203100905201c6045c140300300c8041d40049401d40740d40340c640384021115690241800d000e40070044002450004600028040802580c000e810322001d481d2003503180c3d1604910f29902a1040a0316592591410300c1a5030354051041d51740d1503102d010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 756497320 1250 756496070 756496087
    0xb060d0c140418081306080402090403050f1b010c03060608040503040e04032006070e031b0f06091507060e1b0607060e0f1006090b0609040e01270209060103111b12 72
    0x4004080d6000600301c0b00c5e0341107442e007000383c81c884001d550017504002c2010016012a2085004e81041458004040c1c600045d03458041810360007945a5011650740d080300003015600351150500a00c40c034102004245481d446168590045209150f514216500007500300340c42803940c96a1000b0a201d81905440504000f542d0f6502c2151700c02d001c5491420502c180d031600103840f28208100324404841d82102c00103020204000e41811074118105014240381642d40803030b030b0350608406000458036201d85040540c2900c05c0030164840d560040c503040f5108180301400d00150940c16100a603440741d40740340c25001001c12400152840c041e01d00f090004a81c0803860100494240c002849000d0716004103200700c0f84140303006540010200901c4042d810240c02410401e040700c800010251010306c03101c04003e00040090307003807180d009215000c5281140c00190403c03000e203010024500d1440e002025440340403565402e2441e501014040710000f089150071107103a0195080d12100306 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 756498570 1250 756497320 756497333
    0x110a0305010207031d030c040914011a04050a021c0c0509041b020f010c021e0f010c0c060c0801050a060302030a060b1602010801050f09010501120e01090305070b060d0c140418 77
    0x400f5048002403880300c08500c020080c43c4441908000090140a102c1190400c0000030700040000300c4481c0c4165502c0800142c0a10801e000795510600300050302c05140b04000c220390000301001c41040c81882040c003c0400025694100c03800300e040002d80c08100314054405001381307007145a0041c14020308aa80c00000d40d8042c004403001d0702210341680301500781a080c2c480c1c408041005901c5141403460582d0600d9107100c1c5030200381d0a0300c4244030041d440a00f510440101c51000c030b002c0301d0501d41084154492031703281421600d08619554140000562005071302d2103407804054010010500c92200ca5000c24020708407021850b544198601881044520855080c0e000c03982d03242c00020340f070515440b00406144000d02901c09607081100554910005a4101600703a542d20300d00141450244515142c050083d210740e03448103a189040b1075000d00040580d4000c60200701c14100140380c004201c416110303c07250406c2d2412218010a000703104411602110010081d40d09090050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 756499820 1250 756498570 756498577
    0x3060209040c031e0f091b060909090302031204050312070f0908010e0616020a0c03081209030a02060c09040b03030d050603010c05160f0f1506080c0d1e110a03050102 73
    0x3007510140080c0490034010340898a8140c0308802046880304241d40d070404590050040086001c8005101c9a154580c1790080400e540b5444018501440500110340c104921100034140c6481c00e0110b4060b80d500251130f8041c441048495034200004a01001002d009861a248001911240501e0160001001c2940f422407080c003141c81007402044030b00c018000c4e94003d90a0200504864071030214688041884402001c02c600600000500161010f400a80114025611140c80d8842001040c26051019004540941c010003540d10a0f075004038810341d00c07080d142002510f804800c400300e400b815445d020b03e47e1601000a4205820302c00b030340214050319054000300260011448184c405208041469150007540384200c00020826040380c103107a445074694802c000d0255452080d0b9075100c81400f07100b1600c80c80c081c40b21540400c8000c00340c04088070460240d44c0c3c65160f1001a081e00100ca51a00c22119908000d0004018002400d04005070503136001658030b0401d18000d41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 756501070 1250 756499820 756499837
    0x50610080d0f0305180609011e0b030703080d0605030304060504051806030618030f0c0105100b032206090c062006010b04181517010b06030121030c060c020307061b0f0518030106030602 81
    0xb8402048149c0c0251441004060b06003d4001c140c810304507240c420700d40d00322184003c142600e40e200811262018806400140190340311907490700d0a010030016600340c040440180440300c03c1c2000059500014040d80060003004075040036550449640c1c11031080d030800c450148400504007929040c154400783c401c0c954503d488144030f8a542c4480d56610041d140c088420010b0044200c11a071346000f03070140107105e1000001d4038605640d6840d1001c0844d031021000c41d0070416480103800c4000c0b4001005071043c1c1c050021507040c41c0740e0410901440c0112042c045019070340c2485030308036501110a03412044442c0c0005540d44c5c82889110918804060441d405e05400181e9403d201c0c065034160741014544074912020440300101c3c00f0b800607019400c020080189101080c3c5601c103ea442c0c843d1070b80590390700c0300d950401300d00f6980a4500441c17108100c0207070801031644200c140c24010340602d400395035010183d840c1d501d6070301c1e80c00c41c40d0380c19442c2c81030020030844182d00401c1c014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 756502320 1250 756501070 756501101
    0x12050613051f06270303020d050a03060e040809040e0a02090a0207050c040e33070309020f04060b03090c010c080307111507090303140c151f03050610080d0f030518060901 75
    0x1031388510880c0d606804c4074800180564418408002e5060082c0c02500420710b051038001440c907550116030540e031b00c0c00c0e6015035114900060001c51401c090083d02c802041e0540208041c84007640420900e2030000c2c451252180e000c210b10342001428410f2440c1414000c00900c81d2003070040850340c440180d921013841a810f1800303040184002d54210801041a021140c0065901c1c171400f42d001d0035059804991010700011401c0075695a441000c003d0310002102c00e80382e01e0034ac19090f2402c20b039000d0302410301203640c40c40340000d220641129070200c954500b2070503900409080701c0ca403d0103803401450030480f01e0200040242d0040302c0d00b0031280613699584081c4000001c500c0c3c80d220390b082c83ca005410040040011001241c20380703402c07007413005030748000000d440076070440b41c0725640088030903400caa0248003400700301c1d00c80d0368042c001c40405010802403120303010701511020030188040c9619400090307024030341e50110040380101c25058030002d1400f1a2441c0c0200240f000030001c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 756503570 1250 756502320 756502367
    0x218090903030f0f0103030206041b170c010e03010207080304020f0f060c010218040b0d021002071a1e03060904060e100504050d17062202161212050613051f06 70
    0x18412460304034101c91b0103070003274491900c0d2038880080928011000410150071988000b403003c0342c2441020003c00c00501800d115410900010412061014082d110f0b030b00501140303001c185000201c94101e03038111664a031041038440070070500c502c0d225449601c000c0c04546039601c1d20042d00103250503d0910241d4142e404101c2c1000100c170300d09007106421240b002902c40042c01d200716003c3d203004a030300440760900e598440e08070748462103c50203812241c001c82c007085455503c46140315009900e1005608520384000072403148035000f440545143d890b83d0b00d491181c441031040d920304440038003060007140780c6410141e40c0ca0304011044000030f0007a01e01003a60640304102d1600451000b0018542c284103a0107004543e003540e00008147c81e8200030480c105030740c00c110110302501c01e40b81401854004180035000034400402101c1c541e003850308205035a641c1d01150880360a1011000440351074103019480304440400401c0c8000003403140105120360001914600c2d0004080503145 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 756504820 1250 756503570 756503581
    0xe0a110a080403300f15081e060c0901120f02032805010302060901030b040e070306061505070804060f030914100b060c0c0f12010203160e0414010501030218090903030f 74
    0x4150691000812084c112403451001c1c080250400b02d112045e6134408101030074461a64820a030590b0b100f0060b82e4003410008128208040030700d5100c8016a003e0081c2d45000c2840321200d114015105042010441402503400d880b03030302034500c1c0c80c03c1c8802152a458a90300141c0381c0030103d04001c1e00c80d20401c0c00605003d0041c054207060341c2d4050103860800e00250300640c05007811314403042d03001d626900c425500000c10001080214050f20000c075616113000e0600260a0900c031040c000c01c10108030344000301d002c51702141c0468131240307050307420070f842d040c000c80c01000f901c0380c003c1c5104c0381c07072a4900100710b000405020324600703001c0400044842c07104020807071203180c01783d1200d60031140b140c514a2410400302c0d004400042c0a0000046070781c0070031400c980c01260001c0a44e014040e1800849030f1180d403003c034219007902d04002070b001060075068054014801d00381055000100c50f10003e80c01d0b0040800100080e040714054108a8102c68a1750002c40d41c000b001051a8005032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 756506070 1250 756504820 756504857
    0x4020a0b07050c01030209030a02091905060102070f050d030905030f010605102a05030705060412081620120c0709050606040e07030908270906040e070e0a110a080403 73
    0x1440745030312600400c2035151180c01903020307412400400760706003e1030300e502c0d0144e102d40100c0340c0300300034008a40e240105010a8a0708071140030b0300b164119800b1a1060104c0101008a5419101d080300c1d048035a4025180498078001187c0145806002d8035182102450054004609035a011500325000800420088a442c00c8108000d4480072525585012050200c00c81d0a55540144203aa160085d5500d4461030480192812a45100c3c2160301d5114103921007151500034210020f100481c105160004024801003201020f00100065446130180010424140035068500c10f403900d501c2440ea0554464120344205900c6c1070806001030201d151020407182642d0100c1c0503168207494400e0210000c000460040f540814100500c070030903002d5458065070a545000e11012001d038080500501641c003800c0740740140d0510301c030700400c0da40125242d02a00c080368144100c6503188050328001d042d5100c070220b41c2240004158652550191403a803180e8000c1e00c400942c0100c800501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 756507320 1250 756506070 756506077
    0x31a0a110307052517030f092a0d02190e060f01270b1303050c0409080a0e03030d020d06060815030703240c05301b0403050303090604020a0b 62
    0x110000c1c1041240ca08240686440401c6082c01c520844c02e10031007950303071105801e04000300f412484e0400300420010317880310118141d01c64a84005020681c4a400b0091000480340ea03042d01540c02030f1204044a03110010801e0b504d0382c00800c00d00e0003200741d10a5200e01e849502429440b0b20440000401b64240107100c400c1000041e0750384000c0c60341450314880000c50707910600c8441000c075000040d102c000500504600b690344190000042d1442c60014030380184d01a50700d0081c0c1c145128040410010802d8805550349400d04440c800e0820740003c0c01c40c8038110040103400d201041903e2007100a5001000740d480300d0f01c1d1010541c654110082c900d00b651001c0540c50b6102d11010300016403c03041156280148a64910084080440f0482076445440c48040000c00208550407603200f00401c00c82c82206ca090726046294240025074640100285000d4401000030001da034040311180880f001541c00500341c90700c03130510b070a0080d00d030b079815030b8103900c1204106408222500c402046 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 756508570 1250 756507320 756507331
    0x12030c020a0804061812110406090b011d04110d0e0f071206110c030c060405060c0c280803150a0b0406051c0f09080d050a0c08010b0d0204031a0a1103 66
    0x1c40c2007914200f42118804030040d07170803024508402c030010b0600586188020602e101d26040c2c0516000344003404226140c1c1c1d031043ca940750610480100d1030742c2000b4100070814039001007106285000d0045406007501e1141c1240440000030b001e00c020515030f1041d00030554050039203a02c03111024010740d86030028081c03607203181ca005121300c00092450b44140305510041900c60300f811542c213900c0b8115046040c020070203030400006c020410005010541d03010303001c0c039142403d160541c04040c2d0f4646c0c9140000500c1e00801424410700120310030103c13950b9a005500c0d60340c92429480c2a0403900707030003000602031107030b64502245a50100b004c3e181070b1105a40e809090403a110f41981014441d20035440c1882ea0b01c14842c0304900aa000303081c0720500a800c40c41c1d5131410500b50340110781c0020412141940381c160082c00440e07022007007a045a075800460340d102c0f140741c42000000e02c00c0343c1c002004a117505401401c000956030010344280c1061004100b16080c0b15864900392004886 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 756509820 1250 756508570 756508583
    0x503060108160e0a0611062401050f0403020901030c0906122015041e05120a03080c090603010e010e0a06030b010605161a090f0706022e0912030c020a 66
    0x81c24002c0091000d103245641494011400080d0300c002c1461030703241d600100001005010943c000103410002c0342e400400d00c8840d403051180c80d0740c2c495803440900301203604118000910030480c21a60b003d0341d02440d001000b654055030349140030101e03c410351152140c414284000042e0b04401c080d080440c007504801c041704000c00c0d04903c2045034109582075607010310303042c021807104c0d58548050030281c2200c41700d80c1c084400e00c4554030b45001643c1e111504c11b19003440003150710f0b14080341064640760b1500f4241d0301900c80e00901907903400350036440d40e0070400100c00003401201c112055412586400030940d001c0d1a13940d51207064900502004e4212207005004001c81403117440103144015032042c14100146003680c60b02242031120300c111245a4608081c04400d44041c0240b0003684820001005410701e0850065100c508810b4404046882c2401d00351000c0d650784000d10072050080720401101590345041c00a00e000e0010440c000791401440004060000a80415007500200c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 756511070 1250 756509820 756509837
    0xc0907050711042a1101140c0f0a1b2d0b180115030b010302010801170c060a03020903012c03070c12050106081203010e1510030c03182105030601 64
    0x42840080c1c021603c4e100e0b0a001c0014010302d51003a0f81001c1c2c1c44141e01680c4009a546a0f201c1403800d450905080b070022a448005010301011a00c08640c5180c5070204059165200d0794001e8511001420b140100071a01495101c20040b80916800d5100744854107801e14811801070030402504984000b44a001ca503400b048800c1207841909102d8410381d8000b01d04403088508a08100811b42d1040b9520a01c110040c011980c004890501501e9121403c1c4c0072402001e0300036075101c40f000481402590f0008040d14850b1103901100c113000005002072220b031600c80c9501c4042e124450110038856041e81e001c000020f800300480c2d40c0d00d90024850030902e410014201d0010903040f82c102c03070700e41da0b601d40010091810b220500c400400c035815542c8a603d8002d80800d6203800400581c05800a500c00152980e19954408000340e014500000c500480140540040411150600c0d17440444107910b030401401d01600441400c03017030403046c0750356000c410a48950100340d5a49003c1010f10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 756512320 1250 756511070 756511103
    0xf040929180d1d0423250c08040302041b0807050a0210051806040b0411030706171b0f0c12041a030a09060908030609150a15120e0c09070507 62
    0x1540f250801038030620384000d18000507800202104c0300c604e0112840c2580010391080a0821440107601c40c03110030003091070000c10524481d45c80d00c0c841d8000244450802d403803061040c4070003030b60b0142d40e014000b04070008003141c081c00288800800f810001c0e24240c00100c074603104000791189034501d900141080105003404a01805005003016882c01030061601c02260042180034015030160706800c440e0b042a0410805008001d01458004d41c400c2004200c07940e0b00c0380b241c108280124000c0034403074685484014103003040e009407081e03040022900300e80d600600c100401408007039400f110a44550381d440303141d03540124490707900c030752201c41107915038020b03110003d56002c040d01c0c00c005407646d81031b51150201e07007104c5030a65140d2404000c2112a0a100c244107420640444c100a82d41c84104006007a496160060103420041ca03004449200d001d03079464800b04a11002c1407001900c000301c126651740c492200da901c100d0000c000315a030f584c026421103e643d0f8010032310030b2604130038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 756513570 1250 756512320 756512327
    0x81210030c23030d0e1008011206090305191d030a1703090a05030a030c120504050703080906041d10321302072303040b03060f040929180d 61
    0x3460040e030301024000481030041d5010b000c03803078203c0c9080d2195542c05c00b0003001d100c0c071394912074030745010b010752900181311201c1c00310504c184540c2d1060021030781040743e207400c0341c0034017801044041101283c40c03201d0500b60480b86e000c02400385640d58110300c10a900405682c0d0b2400c04c8060502181e4a445141d81028200150742c00003251080703d03156080f603070311145141d100d81714400001c1da54010703244850f54010f03445114a84800414000c41c04c040d264582c544200d8030000f0324451001490602607100c4005940082c5107581c05001651006142071544000807100065500d03000314000c214007580d01010301c0075000c41c20407918008a0ba00b490a203035a41112003130b60184050100c41c140521900040181d10310425408810310380b5603510312400006010000c0d41030700244000d012000e050343c10381e5845107045600304107040c0d0000115004201c2e0050185c0f8041c0712001410b040040a00101c102004005400416a07603840b101071240c0344004601da0303281c00010300000603d10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 756514820 1250 756513570 756513599
    0x1080c07020901032a0b092d04200409050108011407020628020a020a20100c0609050625021216060608060106020f0c03031809040f0609081210030c 65
    0x100b030040e0f22410b000c1040c07036a800706c0e8448407821100191080050a0100d8291480c100d07c0c001d5104a104150594041044400900c1d000c0c0d50340f6a00c01c045522705041d2284031105109220341c2c1c42c1d807141c581d080a01001d000b006019030801076103205220025608600c200040da010380b40325215401126140c010303119841000412808000008824a10052000d4074054006199501d11860162105c0c1c206d96051401414a10344040e02505c400441207841c01a524002d4a5a07210785400700080400420140c0a48949800c006003000d103500e1a98207001140c411140e00390078600100c0c0c0d02c042508410800f490280000d2000300025080c4a000610a000116049403950030b5145481800d80c4004c0040c0d2005201c4500040305104540701d80d08250301071490440c040c0004043c070340240705080c0c09071880200107414410102c10550026500c498240102074460078462099088070002100f06d440300c00110b165880b00c036500e101102d07417000001030700910f0300160452005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 756516070 1250 756514820 756514853
    0xa0509011502030c0102040f0303180e0a0902060409060b030717060f01080604140403020c0103063203100203011e0503010504020d11010c230705010c0c03020607030c06091101080c0702090103 84
    0x8014007004e91108000c0c00540050800c109090400c6031560900500c43d85007000300c06010003451009009001207101035650100300030801140c01031440c030104185100d690302c810782d00ba00d4074001242c0000900300550141103c1d5442e003101d4903c0d13030242c422949040d1034255200c03201c400804401c0d402125000e511800082c00080c00503c0341104180c2d84200303ca0440050b01710307242c800e1042d0f0301885458003400c0c5078504080c280423169800841040b420710700400c0e424846002e01c1d90b9a90070803003446854080c030025502d95968115000d003003180040c120341c4400314282d0216031820148612407084d90000c2262555821035200d03609e22040741007507a410461202c10800c003103070301d440300080c20a1b8001070000fa94141480550304040b9150862810040125000c070f01003020a8800d40559404860080d03848100e86003e4440f4103044000411031410000b8080610040540c48041e0307030001e894003421540d0b01c45002d50907214048000394407035008030060020550f190351080180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 756517320 1250 756516070 756516073
    0x31502070206030f0708180c130e33061309020f0307080a111005070b15090a02070302010501080d170417070c030c06022122060314060a0509011502 65
    0x1440d40d0041909a802101c101000084801c184481aa8460919544100105aa40001d101d101c0349030391942404c01c51a4803a07581c070000358040322015440140c80500703c80c204c41c2055951a03003500c0e81d08110141d039540c211100c00f400c0f40c4a004002d024818074000388604408a030065400c6d005001030316051f0b81220040081c0060303910200305080241c91000c0c014541441c051030300e04030103444a00004d000700b000c14004801e5580250070b84008541c03127403e0170110380c1d51031221110341c21201c40a40c6c1c084445010300034007548607401880014000c0d0300074411681c07102801a601d0040041c03002c000795030704240110050f110700c00250001d03c80c2c0302c00c160f060040518031700d89802c04075041c0c0c3d00c0c070000e550800403c1a8020319100030841d0340007030501890100c01103501e03002003d071180d000380b0001034800010f00b03461418003250080d5125128200783c4030a0300500030201901207045031048407002c02c0080c0b80c428040c90481d0402840036100d07a003040c00304041e0041c80e6003600d007503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 756518570 1250 756517320 756517327
    0x303052d03010605040504110c030f180414091e0c1003020702030307080c19020f01080a0b090c19020705060f0c070902160c05010305040b0a1d031c0501060216031502 73
    0x9200c03624004600070042c650b50709480b070f814070081104580c0c04488074001144100151001e10402006880c0544101115217480b446401610102090403008540d0300c10329154000b00200060000e031030160840808a84000b00440d56446101d0310304050351115601c20080381055107414001090314518901e03025041c1442035011a103580c1295608842c4400082140c4901c0f0008010800110310b00800d5280301041640110f64201001c1c14882d0401051b000040d000c0e0101d5084605c036000082d04809042c60701c1c1010300c0c400d4200450800841c280400c806410320b100081100a0312030041c525407401407506507001d1194411b15012441c2d00074580005000d014070b1015040380003d002905103040e41914000d5850350883d000107060500c2c00e0309000125409180c030607031002209a00080c42555032107905400b8032207014001462000280e022407420450214040742922030b04140116601c1d802c090780c903066004140021454152000c0001c1041580d292080d56482c2500528 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 756519820 1250 756518570 756518647
    0x3091c0c06050c0a110d090501120b1201051015020c041512120314070c0f0203031c1a010c03271212020c0a0807060c080d14010e0c04030305 62
    0x503500304461510342004046002e0007861340285c50003e9843c4541c0203041c640d80a45030103417400c0d4060203000d04008a148a4460001c3c0d0b541c03003843d1680b40100003040300990520114007900007141d00e0811001502000143e800d03070110244034101840d000381c00c00072400c46c20f000041101407049044101003420008404c041d081e140070314039000c2c00510181010111010303080d240610503660100c114901040080741c1e021403211061680321400e0b04480d4100d000092441c0500c51014031120709000820010b1380556010301e04003400b2056504441c1100740c015600c40c00429809404544861114400000703038041200d0005121442080001d8644150704a40c0b05059012a1310154203410f00f02103a40400c10410545000c0f5525402d16080040e580d03203820280c800d200c184a800780c0c0d500104082d0b1003d0390032044d40f540042041d00c80304804100e502d4020f11844a890a600012071041c0b401c1c074040b0f9007600d4050321400d1030001c1c1912a00d00074072a020802401484c5001c0005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 756521070 1250 756519820 756519833
    0x40c0e070906030e210a0801140a060c02040f110d060f0806040305130b0a0c0308161b0302070b37020d0809160303120b010912020d0812130b0c03091c0c 67
    0x1c68076202c1c500e09498103080d42c00030381487d2068025410a200c0910356000c655910000341050b9003480c81d0032803403803102d4800718015141030b52050850a0074900c1e0700c114115400c011b060001404030301130003c02c1c0c3d03401102902d4a051b01420040d90004400240824021001442c1d40000c618440c0561560b07020002e0391038003d520781900103a40081400c0a0642c4170380d10b503030020060b105040740c03418283e8014000c501c032903030701c510701c0343d800c08080c024940284000002051080380d41d42d0350701820034041900c0300800c1c0c50880044010501c00000f00c410820380c400300d500c1c9030000c1406c0250508240ca211350010300c0c01b4000d100352004040140201401d190040d4071a88a021000030070354000019507081528240c10041c490908000c1c0300c0480e03800e40c0d01a501511f04545032a1281081c0c80d03103100382c0711140e054540c20030034400d0b07054010144410317190180c449850a038503484808647c520040d261024168000080c1040000d00b0056840d19002c50742003d44040e00c144d43c481 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 756522320 1250 756521070 756521113
    0x308040308030f0114010206011e08060c0406020106120c05060304060f09140c151206041506080403090905010b27100c0b010f080d111207050303040c0e070906030e 72
    0x11141d0000110500c40c26602210720a40940280102d8031100d0000100003559180c05208080034a00380c80c6010501e52154494980076044480598180345000003038803400340d0251045e40015031900000007108402480d001403601d5110000c602c906140c00100511030700064130644900c0d90b1680e0902e14810144515050940315011010300c1440f450304c1c15082050901740c080c010701c070150074040903e00c0c0d00d00f12021802501021003040e1130f001c0202c2c000744007a10f0068a0400b005a011401e00d0f04074165922541c4659100c03c00da0f61206001000d442080c4203041482200f40941c54005000040562294000b00503510080404200080703206445841500201c0c8010144070144100003411b50301400f600010341c4072140c5005002540c481a030035000c1e08200100340400441402404080c00d041c0c85078803d42e88414140c1801030301d9900689003214243c010490001c5d26414801c02c8611800d03198447c3c010700c61414005401902c10414185414020002641c405480ca100103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 756523570 1250 756522320 756522323
    0x3091203071425150b0609100305220305120a060f05060a030f060b0d060504090c1a070c03150e1203150f10030b01180302030c0f040f06080c0a060c020f0402090a03080403 75
    0x41ea0908a04034000c4c00440718500d440d107024250030080040380e515403d00340740001c640f515000910341d8a21035044000c110100040908604d1040f2020a01d50305c81d0140411210810969600c0d490b880c48600c112600c92281d0803802003850810080e41c0307010300103004402058200403d460490080300b0003241c4481d0004000407001081c1030032607140d00d12990000c1c102c1502e04100c5e441d070707644941c01510742c24891880500c0d0284240c0031520114070959100b15804960f4011440c3c8914000040742c101d900311000080c5800d80c0c085030782c1d1700014012924658074540602d16102e9000c406151024645d141e40c100034207818148071521a880c6c1c00e481d031403003a03a0001d00d1000d031000040503005000d1080074030311842803040c0017596010032805078020040702c6090f45126100d01050140c480744501d951034a00e00000060360010210704c000c50783c0c5086912202c2152107420540d45003901c1d1714080d400c00c201c0101c202c1a4145903000380010000141000c07001a41c0303035903020017507100340c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 756524820 1250 756523570 756523583
    0x2030c0d05100f08071208070201091d040b0708040c17011e0902091008030405130e010504050a0b090d120f0b030d0201090b39190503091203071425 65
    0xc0800040070f038a2060005041e840000d040041d10b080c5555a801a211074080e03d0b68900003484800c581c0198202070050060420b96400200a00c0040d0340c0e010044400713031009a0320700c00080503580310301801813240c2d51044c180401c5a00f44901800003000c042c01c2d4190301d46d030302e1700900a0300c4280c0c03c0410700c125140801040000a92051100c65000900b00c0c243c24001c0c400f09010704032000c810b40d03003503038415546c542080b003d004420b4090304000901d4800d55203490140000d12401140382c00e42180182285021a250080f106540d000300d0303c824800158210b1083c0910202e43d000108100c1c01c172000420114034040000341001605030070b80e03026130764800c0a0010032140c50140355002c09000e44410f030b004658640400c5c02540d00b5040d02c01c44946042c01c0280a02d50802d645141c0031041d80d211940d142c001000d00258000c2d40c03803007654414100c1e9841414114400c0f80d11409507991012040d180390098007003076030408500c60b1322005100f1030070f80f1602038440300600f08502800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 756526070 1250 756524820 756524851
    0x302031218070f150906120c020a0f1406150607060e16081f0902010509010c02041116021305040203150c0705161806060801051905151c06120602030c0d05 68
    0x304d044210318615801800710b5104208140c641110064080e61701c200f2002c12001c445c0b110481c10800b0001d00100100200d076a04010700c02c100d0b011a4442d4050000c9501c80c1e01d0b0b4858400e500360007006410b5110740d080004d480001c00c1c541107103444580303500465031485281d2079200c980d04084d41141d015076200c0003903540003a43c80180100e900c415408204070b00c44642c0c000800c40d00c18241280d06111444e4600d00c1192650b5111f0399010080b02c2249484a102d0704034a105502e94040603445071410492205400145110b40d83c01198001c0090045d110040a0b2140311040200091012801403183c640480d10510902e071b5280e001c00303a00d1040d182480c17000c1203206508074189040f545003a00c288001500030101905403141200d81c40c046a14059a90846441d40c2d004070360450b50f000d036400518100a4090403880068100305c85460f0407204103101115480c1c030844584038402001a80800c1c19640155084085842c1952601f40c06a200105450003900c0904102c0d1609 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 756527320 1250 756526070 756526079
    0xb1902070f0f030f080c0d1e0e030a141204020d1401090303091505100b0c070320040b150301060e010e100903021513140a03020d080403060c0c0302031218070f 70
    0x315401301d9902414198070302c0c144211072034801d008100303052845580d1080064040380c161032074000101210741080c8200c0081c1c1c04030503100d401600c11400402c40100010043c02c1a01c025148501d985480c40300055640e03070200074070900086c5c415910056a01042003200f0428016038038840c1c004c1d2404a980300d41d910b4160005424441c5802145280070f00707005400400100c00e208a50083d22442d8607507101d0000f080c10b10a65a20040044100f104500d10b060307811000101602000c0700c040000851030300134040e50f5001621409542d00c1c0400040c454680103c2900d4030654041c50500b0070700305194089802d8801c000c002101151810b481001103280c030712490340101d59005c00250801c81e190900c200b40c5442e9019044102d0183c801200c3c282d01d0b2501ca0000031070300181490302034903090a1122855000740400e4a1142c2880c0203c504503000343c54640d40c80d0351540c02075103000750710b203c54040080007038051100100c0c216500c076007041042040e83d02a1000c3c400300007a60f40b82 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 756528570 1250 756527320 756527327
    0x305060615072102030d1a19030c0603020a0e0a0e04050c0a0f0326030c0a1107051305090c061803011401150c0507231c0b1902070f0f03 60
    0x70320100d030603015002c000441c0040c1040d41440d042921030003d032408550041c409034114000e4980d11801249080e0100742d403403000c2c1c0d04c103036111101901c05041d508280c950900c0035145902011307003003200700101040103a20a074001c02c1d1079541c074a050343c0900450000582e040b07513140e2044480000c01401c0c00b040c420301380094a62440100c64504003140b0f0070034000c038024030610002d0207499038803401188070f03950141301540b0b11030030700d4405660f464180031100076600905401c0d000500d55074901400304d000003032080b0540f00000c05c4c8900303184842e401b08000d4000181400786070b01500e060b94807162980c00c050441030070f002c94801d120396584000e240c21141400d0464142d50b024000411070190b819550000b56170f2744e80361a000e40c0c942c908080345442641e40c05103540c240b0758007900b0401c081c0305600544841c0300b1940440c1c96002c1d0702c2c404409a94005c009080c0404103070200303009101c442414066010160409814216030761600d004041c1500001e556000101d041034080591 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 756529820 1250 756528570 756528589
    0x6050702100e0906040c02100501092f0f07050c120705040b04020f09010806122e0b03121b060c190804171305030f1b031f111303050606 60
    0x503540b400c54080c0c0880400126800c1c400380026008658500700414030600c28442c00c081c1c00b20b508024041965141030210003072840c020080c00b81c1d4080700740d030003d50111209560310040c80c1541c250514403580001540b90380824412107027440760160000c51a01d40541d90714184410b60b01408000e4034140c10302081d00c450414441c8038be44100802c10201c01040240c4003015000c0c40c181c4c5155541d400400d07842d094810000304a80f10300100380c040d05e074000540c2c50110344143c2003512800c911038942c0003640e8a00f00280c0d8990810803030410700e0b1240d0000ba0a000413040202c010410b4820451410003105582d94a000140043d02c0b250425420400d2803060210f0319203410b481ca40f039120b20b83d0b2650329903c0c500c0e40410001e081481d00c070426005801070f0000034207440201c800032000d1a59505403442c03000f000c0005041442680c900491218542028650200c4116605000c1c40000340700c00c09281c2c1b0021b80501560000103164414000a103100c0c0005014504007001044070418 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 756531070 1250 756529820 756529849
    0x12031a030309090f1b2b090519021f0504080f1c1214070f082401030f0e24100b0702100c02041b081509070516060606050702 55
    0x520030008035003243c4800001030751207052140c6561094460746048201000c958034031500c1c503070001c68420400c0000c489003c90701c017000a60100600c90104418041e0741218502030310541240c0042c030103d440c80c0603107203101840103020308403000304403001e044001502c070301801c009100801c0a100c0d0100030880c0720440c900500050840401c101400004105580007000070449000c401c080318007a00c1d000b00200c03040e40095000c1500e090300c0020720f002c001c103840100140304800818214641119070394038482c0c0040040844410f100c0040d40601503002c00355154940e2901c612480d20002e010300901d09003403a1405098680305180c00e81c05600290000c00c080700c0b01041000307000e14040c11203006540c159805802c282408809907002510303000c01a401c81d00f0160a17116001100c02c6040b80c1010546814000c1d0300c070a403070180000c0306500c00369041b2498030003184180e4040c3d000b60210000c1c7c4a051001042c1950300c1c9000d4400580c080c102040c070101d0140308500c0e208070070150a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 756532320 1250 756531070 756531073
    0x1e07080303042301150e0f10081b01020c0d0f0b10080703060c050c01060f170309060703030b120f060a0f050402030a03030c02010204030803010305030c0c10052512031a03 75
    0x14141920b80341c00b40c8000b480c91500c1168071000c0c0c00f0f150345082d0806109003000300c0d85928810741c1d501240540040803030300000444880d000080e440310602c02d8074030a5940050082480060110280c0704030b540a80015040d88910004141650b03a5810b101601d07a1180280f20458090f80c640760390841e0015108171407840003094240b101f048001b40c1c48044903049a0045490704d08240159220300ca000d151802c694240391007c0f40c18040040d00c04125030101101c4d11100c0c20902e021601c0c2c0c09a05000c03648000c0c1040004086031194101102d9458014101c7d0b030078200640c48a071402c1080e41c0481903d070003c40070006418071a2085054030907400c0303c00d1120f841d00390b0000781c940564805c0203003855034950314092044d00c00d5050b6809190b02c00c0815a81307585a0500d10b940b90000001e4032010701c1290803690550519101c0c145400a0380d498240c00d0201c00240c80f00c01100c141e120300102d203007215504d40440c00240c2c00d0198800113480004043d2101c1407400ca04c4651040d2680c083d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 756533570 1250 756532320 756532327
    0x15041502060708151f0309020a0f051305060312072d0812070306080d05070219180903030b100e10141213020d08130e0f0609060d051e070803 62
    0x2840d0050203071903201c001307190070400d580c442e0130004840f1100c4040c0e104521040b0010605016051307441365881d14000c403140784c00907598101c00700400c000f80c024580c02140304415000182500d800c0b030342e0403a41c020181d0352056a800c0c0c840c801500700c1c0c0b406940c48204042c940f01c034000740c140c54528540d000c01841002c0c2074a9100c0c074007244200f642c0c80511211050000740494806e501c80d201418803d03003941e85100f00000020556000b8250aa105540a43d10f001c0c44d48100b220640444480c00c540c8900c2590a92910005081080d41036082c50340303074800036542c2c0d03071840f908050341d000588888010f01c42000510200c003191009200c2803010000b0881040c1e03e1140595001007000e5a4441c0c4a0781ea0450800c080300c02c00c80000e40081e00441284104400a4003030010f1a0131404007820079a610b08a00801c0e0308291000d10005040a0108a140c1050030304140d110342c010f88040c103038120990b181c3d480c0008221400304020040c6e15032100c1c9440a0198000500680000f0b504 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 756534820 1250 756533570 756533581
    0x60f04170102040e070e011e0207030203070905070801051203090603130b070e1c060e1203041a04030909020c16030602030109060b0909012114010b100302190513051504150206 77
    0x41c0301400b401400501640740b0380000d0740c0c8e00c540340c80c40710300c10f0030b03641d41e102da0b090707808003a50f036174603e0100320f00c01d01030b000700825070001c5441243e00c6500f060350391280503441c000074040d26030245e8840007894002081841c0168071450011401082c01c0850301ca0700309900c0c1030013850100c0103841003003008241002130103983e9031600c00c285060603604a0b2902820a854004024840c4522083d1540900c92001c00d210240030091880340f4020b04259241c00443d884000c07a6100c00c68000300070815940080c094507042d640030b058507812110882e62400e0b18441e8110181400f17a000320b8500d50000018440c03403406019000080c000d050005003848e0b0904005081030105000c0c22030f02007074120440c14524103036184440c0240d0014000d0322240324a03660540038042d03400c14140911a81240c1c1544503209100b181c41d080c200b03084049008091400845182d40000c070300c0310398000c2901e004101a036038141901400d06140d8800c980d118504001000d401c4c103100b2070501507408c204108031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 756536070 1250 756534820 756534839
    0x2a12030306010c060203101809050705010807080109150b03100305070501030c050304020d1a25080c1b030d180b2d0a0227090105091005040b0d02060f0417010204 71
    0x205244d1101000da1640c0e42c00c002c200030b01c20709500515541d200324201c041c0e0f10340c1d03070752048100740e001d401903072019625400190799600b41502d0f410700090b49074004020705000c56001d0842084015031043c002d0365503400740ca425030001c0da2502c50700c0035200c504208020782004120020031003030030140140302c1c80341c02c06011808020400381c001e1000c003051208100e2501401c41545c0c0030804403039000d0610f1079512042d08103550100230703175003501c40c2490103043c011507800c0c0c450465a0f049602c0e2900d80480e04461001000d0b40c040e840c8400d004080c0b10041a0181551441d0341007070b4410082442e08002c00a041c015001c8001803800b201e94450b03843c45628850000004e4420310032058641441c003c00910841417100f41170202030000c0250f4001c50598410720010442d401c0289988610030000701900a03208034070100100d200802946c14240c01c4524072020050420f03030b41040680103e5620b5004004960301140300040602c08a2074900d000070314504120700850810b41046041c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 756537320 1250 756536070 756536087
    0xd0906090317070f0f1104020301051c0501060510020a03021b06070201180306020d050906060f1f0e12010b0a090e0a03050d020c10020c2a010806032a1203030601 71
    0x2a2011800d2080510000b402100701c80c0401c1e4040d1106000c0062400c042d0400101460708aa8401040086803081c2c0f130b0a000b0340307040c0c45005010480c8810000d0788400b907100d25030001c0b5215500d42c0c40004195507030000144d1414174a8024200c000d19504d002401c0c010b0501c0f000c0c145009030785c1000015190803060f150000d90a08010400441c00340c0c01d60740403074895100074036280c000210a20052000d1f0005406140410304507800c87d21800100404040c05207861900100d26031496521080100d107001e2000c1046e080521780b2081d904080707510340c18030071488c0300142e45a405050b441d00707118100000622140c20108401c0510b440309603180c20000b00d02070200940400c0b903071414101641111a1102110110b51505a4202c1e141d80a5001510180c50901071020542e071340040c0c01d075083c00010041040611500000342c0192510600600019010b02c03925180d803204a140d094412090b14010000700000300c0c4880c00c111a45440d0030384607c40760401d005000899801440f070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 756538570 1250 756537320 756537323
    0x405010b18250207080102130302041b0804060203070309051903020d170a0b04020903011e060b07021c14062a1815090a09021b0106030b010303180906060f020d09060903 74
    0x405040020b0040492420b021500070310390783e510006e020729402c03510035200000c813442564140888040c85003d04a4619003400705d1307010940312400100007030419801940e00041d02d081c00200401d054032200c0c075155200d00d10b22020281044c421091640400802224042c10719201c916410f41940900d41c03040058004049162034103c0018684c0c0d458058070320094018000f082150007540340a8980409889001c850603c0c2c41008922809072004075603507650042c00e1208243c0780c01c500c01940142c40f0009407400c1418003001c542490040c410980581c1c0702e64645450104402c1001c0c1060000024070700c06814100124041a040340200d1400c1400440710501081424010000640305014a2561119040c0c0010030100b020b5400b40c070740d015090681041040d42e48211a08a907030600018003506015801040001d101703075910301d5188060124007103007581d00d501c44020f4690540010340401c00030009420103036410007070b0b04091511461b10240b0145004400350503e1002d010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 756539820 1250 756538570 756538621
    0x70c0e010f0503031c06120f0c0603050106021b24031014010e102003040e0a1a100311041829130e071509080604020315090a05060405010b18 62
    0x1010200c2d040294041c0c401441d107240c2c0e0340851000c7e454423019104c10110115404400d1140101e1118480e1040c00e0580303449400034000000030f007520390032840c00309010399030000301d00d91400c50385c200510011400300e118203403164480c01d014a0404d034140c0c203904201c0c0c5501d80c01d1100c42d0203a034450070b841c409100541c0c0480d10952b9010040741e8181c00f08004680f80c1c070362100b401c2040744001000380111082070082000c2c9448130710300e440548600300d100c20110301d00490801c41900d0441181501c0403a14100020424281d0502902c590000d0303002d480b000245407021650050b00e4042c424000503010ba0384540a66030030306e420760503600780145a000350100000ca0080b600e040c0d0150501d84026802c865030315503141c6031041ca00194049500026a4802000460100008186004a50003009429a1915000ca51000315802046203c041c824040404040b49091264a0240340500c001048001401c802d004605c0b5240380002200e0000d102044030007500d401000c1c2096642a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 756541070 1250 756539820 756539857
    0x13050f0a02160f03080709050a08031b030c0708010f0f0e1b030102090d12200615010c0f051501050d200307030b25031e0e030f070c0e010f050303 64
    0xe101121642c0320754802000610340300f40100c04d0540101700d00344079000d0f598400c1585500c0f0f0042c0b001c58801c51184c009640d09c240802824a18002c05591036802d00c482240d0808000b0740711145040141c0d40514200d035900c002c140300702e01641c0540c61b050324013088148250000443e1040d40c400e102c000414000101c9442c45c20150340a4048900c8514010203202041d006400d0141420b601c0c03809110101d021045901c4c14191100e00040141100c0360117008980e07140d100240300c0d1070301d540804d0304011088424400150854024200441c01070008002d0f10720a1850f0480c02e00040c0c102034414ac1076607540b10b00254484503036581191184030103004e14041c00e404603142c01002c2c2c100400036980c041c108083d443c0007240001003107003071400340034404540711029001c80c1c0b0800120b2610384500d0030904c041e1070664101d08c500c0390082040760302e440d825400140080c0c20031034003100d41ca112040c081200c616480341d0640940304120042604c1854000040d949101786244140281400d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 756542320 1250 756541070 756541087
    0x80c07080d110f2a0c0a03060507020a0f0813080705133908060402090f01080907030b01150e0306070c0209041b1716081e190303060513050f0a02 64
    0xb0151901c6034400e01c0c445480300100c40460300740c2400d0b0646000070a07111020b030100d201d0001298034040d540940403d00b00350440c0c03955401703010020710b10710a43c45110700d0071000451a011801e00c0c1402000c05030b807500030000941005d814650300180d010f0b407001800f4080c0d9a610300300d0140540322098001a04805071091446245c0100d4142180c4c250a1184960264102700c0c50901501d0035544d0a0b017a41e2100200300880c01035020351604000140c1c1400520b5000d240c0780c5401c000110211200156030340d403104480c0300c4c00d800100ca0640b44842c140c80c96070700140c0313804400400700c020703105500d0a00d400a00405c1b01d500d02900c04c2c43c0b071101240c01c0c403110034080b8000380488460262901d8981b2034585624080380c0000529101e0044a4154020480614000d847c094030140010308118100c40d0444c0ba1300b15040b460500490307040c2c0e012001d0094507810340501c25100820030902d080c04102c0500080460006400c0c102810095041080b01c041984404482001030322500340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 756543570 1250 756542320 756542351
    0x915030b060a0206010e011a0f09010239090c031b070f0606050f061e0307020c27010b0c060a0c0e03030d151a0d0b0f060d020a080c07080d 61
    0x3200d0186410640024440500940c0402c0e02c0d410b0300d264111800c03da90780c9203483d00c00010140c09002012209004010128030198000c0202e52414411502010b001d503a08000c0110a4100d034988800d089400e03004c1c84442251028681a0843c2c0d400841d280980920245210090555500c03d8070041c00c5041802001c05a5202c20341054541c0b00324540c40c17610f80010141030180911603140c05802160b00e150072022100030240400b0b9003803130f010841720802c40130380020f42500c003035010781490a4590b844610300e0752400c610034902900b03030444064200f407000d101a00142850b0004105848035144001001074010600110000b00c24403400421900110301c9100189e15000001e109102000e41d504940b40d841042004d01050950f10603d082c8244220100c51149003000d105079000c1180c1580001ca8140d0f010b0040300e58940104000f0f1500e5000d810b140e52802d50204085122a034031106566005441100892030f04010740c580c804240540680d1f10400340d2600180301902c3d07207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 756544820 1250 756543570 756543581
    0x80607020a1a07180815150d0308040206040909030203030f0708010614031314030d0c051908060f090412020c01300608010c030207031b020108010506030a14040b0124091503 76
    0x40980c00b4141140d260002962101031012800c0c180100710400704403408408441f6059481c0010a040d401d00c6041e502501d01d200001d00c00d03a448401448001003030001809840302591180c4d0256075203140080e604201204050711040401c260341005101c51604020321800441007804c0b80c0d1b44a0340c1e96103c0300030248800600805540360416159a54040000600700d1140242d00c148408401d82901312800e00600380010b154083c610114000c05014a152a8001c1000b4100002d03000c0e1040c040b81583c10291421520400d16101010140f9414411164480401d02c0c01a0005040846003c42030600a42040340e500c0c000c2c0086600c803481e80e01c500300514505e4001c0c400306004050290084d0005042034003c107901d40f00007d0b5495800341c5218500d036058665240603400c0805100d080c3c0c1000700081081650b443c01458081c8109c44414401c81c42000351062940c100302d55101c03801e4400e008201101c3c01c0e54081012a80c2000c402ca05030343e040b4020201510365904100c1c007512 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 756546070 1250 756544820 756544847
    0xc01120e150103120c030206070f031b020a02150412020f0f0a140307090b06043f0606061d0f030111030f01090c110a03080a0b061201080607020a1a07 66
    0x214032242090304801e0000c81038100c07405440a0012143d200600f940c0300000158000c005810080c0051a00c500898070b5802211030b070302c1d0000d42c0c0c2c441d8070020f2002e0a2001d0220b4050790160503140c04600c1c0c5860b04043d907407804036049040030f141918981c4002c0d180b20b8024440c03c0c0900310141070791200941c544142c40e0050a8441e07041d5624645030984001c15003d81c081d014001c0042580c0e44c0e00e010390a140480600010b1405181090b0094116250491254000002d01048480c4841040b43c076400145122035040205414074204048900d590b02c081c0c00e101c50900c40e641d105482040c10040554266500b14006a41c4800240104a40c00104440e140007009000c5040c3c003007541c440c10b030740d040d21013081813036810030050b07804102c2186602c4456200c0200040005e02c105042908103015080c0803da5440460006000c1d420414506481707109400041020300420094250049001d001070160502943c6a46010808880d8140502038010002c01c01e107500c905000350001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 756547320 1250 756546070 756546073
    0x160e010e06060c03070f02040b0105040303091202240406020d2a11031f051f091a04051302131512080f030702070e061f0f14161a01080c01120e 63
    0x300c4103441c1c221183c0c915804148e001c1c9103010f4040c1d01c654041d00484058a030076480e0498100c1c50440020000c1c00380800403600120084010b446002d0300d07114554419506003c069100d03410807200078600581341803118204107034440328008500040c11200790144011400c402d8a1007181046580905010412901403044100e0031040c03060114044400e10b40d4100140305540720307036104e03c0000545130300c0b0f801503c04c200020032035114140d10040d41180c0040d0b960580422007000030341140e1007103451040e020300c00c840707010451400d2240b0b25800b178030a01c420420782d49101d403144070f01103a60281c0d0384940b00200410041c0300105065490000c0d101c2140c0d5600d14240100035242d00c180d00c103840c5410249000b1400a1402c807498501c00201c00f0900710414041d4107040f40c8003401c58401c18240414031800183d035448035401803051910018051600c1d403800d161009100c1d60301e410a000b003010810061001210210705915a11030074601845203030301e070080d40e00c000e09415092070080e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 756548570 1250 756547320 756547327
    0x20903010b090c0d0e0f060f04030c1209080609070f150903020d030c140304080c091e07020105011e0f051215040507061d0d1e060e0f160e010e06060c03 67
    0x2001003d4000d01c0c0030f40d0404010311030100010b118641ea046001683c50b0300381c00c22030029002140090502d9407160091401808006c030030380701c075050920040c1c5c3c2c0c50300007040840e082c04072150030081c260308480400700030800d00b03191201e0a9400101405a9800c400d004421a40e84a10030350038103000c2c50f001044a440c0564518002e4810031849804848080303401c0c3d2551845480481a9030441c0d043c0750140901141d42000c100e8600c0006208036a41040342111042e00e4107000400c07841402c0e260000a420350500c5509400c121000c404000c030401460300074000b2130a0303c04000c04941090340c2d001074031200103000f58209003411440d1880003070120100401c0c4072001807c0c0085030001d803660b2031450144041c0f00050310440c0403c5401101e10500240054110203a141c07510405041d41414512260f5544007a6101d03400a10002ea10401e94403805c00c40500960400300c90f5000d45039030940c03400c0407070101c03e0703014414a0150244a03002840c10784800c01250b10004075202620355 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 756549820 1250 756548570 756548581
    0x1806030612070e1f06080a0b36010906050a091d030304050c01030605060301120f030e041802100216060f030b10020105040b06011d150f0a09060f080c0d020903010b09 73
    0x10380a4048400c084c1c0f98500d8510241c4800082c4140000e440d6039607145200d075528403051001404030103178071641000380080349404c4034411001c0194414000011021243c140f2450290400410307000f01c00198035208081150b0fa6400040e0380460b00e4040f0003040141c0c00001210001c011020301e4074140c00000100401c204001c203014440c944240c808005c0c0540307880c1444250700090290310b0010900d40a01000310300c900301c07400480351007868a401d205c02c900c2d01003015100340d0880b94070304c1c819406071071045150503010300240074894401400680c110301325100c1f00510910600041c0000519681480c601c250007803903660b0005800400c00f803001000003802007900712001c0d00d0362500c2e50040b40441d80302d1320700c2c41c90000300140300000d81c0340070904001001c00841c03c2d850b0407100801c08100100078880180c2040d415646984410781d240400140070044110a15010450041c1c10030008091030300540e0459035021400680f5104000f0109004008101503158403083e803078201302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 756551070 1250 756549820 756549839
    0x8370216080c0d2109240e06130314130302180108060a0504030915200609060702010e07030f1a0c0a09090608070e0c070609150c0203180603061207 65
    0x80c180c00c2c40710499281d4444034404450640380c400f07601d2080c03c040c030207000b84503007540c020501050003110b07a04003a8440720801c40d814a01075007104180e64441e460066000000e0240c0b80d0311195006a80c0200c07100c80e0350041c540c058042140380c964001180902111410215100145501905642d00e8603600020900c802000f40300c4d9800300e2140d07500007420361001c2c1c00355501a40e416110b510340d45080024448021b004c1488950411141c40c08042c0a42c015140040210040c072010300400c3c1416a0502d0610b40028101801d581c10722607a00c0e0f401e0000503030081101d80088040640120f06d20340030000d001c5588030380814440010501c0314008000c4000e19440341241ca88010b0a503581a0f14010390b496031080342800e8005e4481006200640d100d02a80402021810f500d07001455072040111641e15400b074480d50506580c40500030058490003200e100a8002035051541c05034102e49030545801c001801510040080f80c119100d403401d01d03050484510540355166120846170 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 756552320 1250 756551070 756551077
    0x9050103031e030b101d03060112061104061211120709060801120c03060f09050f0a020f011d0f01111014070c1a0c1605030702010837021608 62
    0x21112003844000d07003100b043c002d10401602c1e80c4064411550280e8442e8240d42181050007483d070f1030300d6008036511031903406000d281c1c00303460840c0d84074040540701d041420840d481b500b02100441c4042005100d000e8008440d40301c403003422079021564401600c0c07080c034903009000c101040480c3d5503040c07010700703034001554074140d8600740c2ea00885680c0e01c86a000c80340c0184c803405410002e02d03a805102080c110741018645156649000c18284083d42d1030501d0031030b00403c04030707040e00416071810451800c4491522504424a002d0a81c0c0c40040882901c0c0164071200c1480f80d40c3c411000e0b0480d901aa00e400d040040c001e0544281502410116015010354944c01d111054480000380055016003070650755150070104441c03130b0b03142801d00311182c500040e10b520f2801c0300a00055000840303000b12200d00718841d0014589402c200d200250840c0d8019040ca00e0a4441c68442341c1288004d020303401d039142e0359a40442c1c2d0000b0302c086800c024400e4050601c030f401c409529030402d200b580d1004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 756553570 1250 756552320 756552347
    0x1020f16121e0806030708160f15050d0e0114010801060e0a0212060d03050405060304060f0c020f06070e04020d0501081e0601050907121b0e03011409190c0905010303 73
    0x81da09444641c000c00c0b070b0040740300c907100180d0400c0c0c1d95400a4040c807800c1e85a51099000d03044804050b182d43c1e04610300341082c4440d415034410510140003801e40009854010440725074410f20b044034011000c0c01500910203801c58103035032150300644002c0250070003515982032503041441c0b56101d28015018045d07901501008403824000b143c00e5000e00d00c00c03907006040d455089401911844c0410580c1e070308e0b00384140e04208040c0400324080e900c20b0001c0d40034030302c07400000803038106401c0564140d40038054045c0964200e85004a9211400314601e07520007518502401704c0c0c0340b41d000080090050401803080c5914290002c15150070015903920082e00702c42508901211142800c0d5548009000303d5400402000128100900403200d01e503a0140300c45003c41c6502501100307410381645000c0d60400240600c40c10300307503802c080c4241030101c043ca030780642603854850290340e60741d80816002020300800030405801d02411000075400342c290a4400e11055940713040c014142c083e10801c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 756554820 1250 756553570 756553583
    0x20d051005030c1504270c02330703020f1e1e0c0d05070f0b15101103030c130305150f0109020405181906060203031801050705040b070501020f16 64
    0x109011689801240c59060841303442805203401d0609201c481c1890303c01c00b034203002c01d0f0b44240075808000303907001e41061200ca81d80142101a2900035400242030107005001c421198408040da10348440044254880f413607013000740c0e1310340c0e07a54a00314a51240c5000c02d120300810250041030f4880300c400800d0784412006525919404004030100e01c0d208100c40d40b04141e1010040d14403442c003d60180c0035090283c100b903000c1c8103250726065141d6800f210305400100305942c10141070b16040c900c0403081d80441c90711645142582c29520343c0c0e440090040c44000101207200060006002d0309080610790040995048110742c82c41046035850a07035003981614228000400c000c1c00720302c01d440448000500e0000360549103480c00c10b0301035010300b034844140012889031020381c02034003c4100030035455000315035070710704414a401d000003420310116659040c03c0078020070603404002c1d541652500c41090303581d900709181c5540248542d03810710345000780c042b505016070a00c0341c00b201c410314001e49 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 756556070 1250 756554820 756554833
    0xb100f08060103060e061603050c040902030118050108060705040603050912040e15220b01030b1c03030b0f0a271d1011030123120606011d031906020d05100503 70
    0x104064032408200c2c0c7c110110009110341d541c0c014440d03009243c0044007050958a01900c41103c81d040e42e10907008000d00b60046a840d00c03a0080d2445800d004202000282903070b410082d1005027a48101d200320020180c540020400d014000d2003605060a0005c50039940d482d61141029081c400464540344e0b5410301c0078940805049c40c1d100c0f190111303100e42c00c02c812202550300a90050030440c41c1a4101980c410340c3c8003140e10b54050301604440e821110740c0900c0c08601e4002c003aa07a180424a0048402500c581c40c961102c924480580d5860220104010014a0407880c046e40c90807001002600b8150f8840d226a074a084030416121408103640c203100c0004080010b5400c06c030784410344082c0410042062140b05140c200038101a01d01517650310789480002465002d0400aa4016420250501c489503800211441100108150b5041c0c0055030b031001a0b1520104c50300c07005003010514091080150580c1145c000042002c0200007900300309081a190b20554001c003802031041c00b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 756557320 1250 756556070 756556091
    0x220b090d11060c0a1b1d0a0902030a111003020c06040b18031204030908030705060604180503030108100b0a030809090411100210060801140c0c0f100e0d0806030a0b100f0806010306 79
    0x408090300d1401c000380b000e40103040d42d0300d1505840146a07c1c15603650704139002c0165800e000d98150a402816505028080c7c1010000d200d5115050801032510401014440c080d0200d4038991003504110305080d40d0b61103000045088942d14201807441c00001116007042c01d17000d40c41409030340a5655400d119446010041d070701e10880c0c6001d8640d0f40040001103c501d0076400401746110300e00c0750604000c01a584180c91a00283c002d40103940214111001e03801d000e104009164a0031145001d00a00c3c50322a50014400d401c00030f400b4181c01c0c0d0020341400680ca901c00c2c1c08200107003500000114400c0000d403244100100314840900b40720000a012405004034450b4000e5444a4401b549500001640903032050144d6100341c010a4040ea00c030020070320400c1102d554075a4040b401074183c2e48541c0c1081c50b40c0184c90240010803092018a8170b0000740341d002d01e07620459040d141c4e00c8aa60719514a0706542c03140000726441ea40118001c480440d03c0340c1200d110f00414031420508 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 756558570 1250 756557320 756557363
    0xa03050709050f07021e031b060a0f02070308160912030314090706020c060c07090612110618010c05010603020a14120d0e10030e030f220b090d11060c0a 67
    0x4d8801ca40185d001c0d2003004480410748030421a0464410200ca10380448540304880c4000c402010b0340d40c540008041242541c03090044252400c8040d00441c03070107040b079a01410600010b070406c0350021b0769048801e00d980c000c0101d10094603012a40d8000d41d8000d2800074050203142d0583c241201c00e0402041040600060304015a010354026058620428050042c19000584c84018602c2189400200800c0fa4801c00001c0c0101c030448038614001420100e41c204031462206014400403c403140c01c600c030402d80d1240c00d080902c2c6c1040c1107142820201d01501983d00065400000c2c410002818a10207090341a124000d90b600c03402d005c5c1c21901d958640d241001080c01181c0b02162200951034207032406503841805040c002800000950303500d02c0c41c1c0280400d0f0018410010b80100d440c00c0d0148000d245103100001d410f1307120704000c8541d03800d020784864a8001c5106480c00004c021950001034041c4201424851312001c00840c5903950703600c0044143c40740b1141300340f0041c04128 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 756559820 1250 756558570 756558601
    0x2a1605030d0507050a0c0303020c01090812030a02030402030a1b050411090d03030504050f0f0604020411090f040b01051e0301051f0813030c083907120807020a0305070905 75
    0x1000300a4144035000c0d950a46041e4442402115a40142c080170b03c000340501600101550180d4000c0c8061b104030000074000c2c180e25001000343c0d520503403041400800c40c600316940300c00520320141c2c0300e840b1440031a01e0107004202c010300c3d900a940280550402c801c805070300701c410450b001d01c01e01d02d450220a4051040c004040e801000720b031301d40d0001c41c0c040d0300484d4125108008450800c103010700c4413030501d19a05030f000e07265000b8509010540c0340500a05040011b120b03001c5140150880004040f9960301100350300498803450589002d07030154055641c0c0300c04025a4104290260030006000e82c42405080e00c98054900002040c4540d020300a0a00e0300d03940b500321a940742c4201440310b10380014000c50400401c602c020000404500181c000072902100c04050807461520844800390500c06c0700307000c11014107210002890024034a001c40b000ca2484130b01e0030034941000c85840c4101c5e107002c0e41025003c0000010060000303800003c03a03040450400041c1c4507444a8000c0f0796 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 756561070 1250 756559820 756559829
    0x1504050606070206162103020405030c04051501200102340302060703090809040218010e0301050c0901050c03250507090903090e090f0105070c02031528022a16 70
    0x2c14032501000c04000c00d00010002d0060181010740040e171b030b4100342540003128040000940200302009103080801c5100703400790088038107000134a825400d1540746850003981c1130400402888811500c0f040350744102110300b4076002955101000814480c120400c40388a45034101e07911511000e840420707440bc80c0141c1d00d0b601800090b15017403000c40180c8012041a01c0d500420840f0103203690341c03072006004e8883c0308845912100711141c00907040901a42c015030280e410081042100140003040b20440e084c01d0814035140c032002e4071254610b015404200ba803807071500d0120b6900560320000c401980f0310500884150f544c540f10342600381d5054610080200c4e1902e40c0034050b0100c428030460303010444004840d2403440076507100e070a68800303071506030115141003103000130b50609100162480c0001c224400c0325081c5450700469805030b1071501c1c95010f0794003c0c40c1c8140300c0140c041301c0003409070420149080d40e21447c65034400d0b02083c08945c441c8200080b080110900e03007104005c48 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 756562320 1250 756561070 756561079
    0xa050f030f0901270e06011116090f0f180c080c1509190b180d0b0c07020a0305060406061508070c02060f0706090606050102061b0306010f1715040506060702 69
    0xc4055401944c110036081503003002c81e10b0214004010340b00040c0010010500001c0060305828110000751a00048440410355900085004450b0071f00708103c10040340c03041c410008a142d0100404802420f01c0901a801541070030300007a000050612041501402a0820b480d95595161043d41d5180e4100005800000581102d4484500704001e4112150040c1102c25551012448030ba11b0700c100744c0280c480b012001c10800011a450f05400c204001c0a41d02ca9080700010388031034002141c01000c580d42d400300002e089045480d60b028050095a0040c1219050b00305498803201500d414054880e071068400e06505507140303e40c80d044d005010340e466a180301145a001d000080c0c0c1704a9004030300000801c14500007130283d12a01ca1210b0190500241550409000900b4008090540d50300390f8040071101e04140b010780100c3e604440309081199201c1d007904001d440b1000715821442204820404000308600c0000410490510403a01003000b0381d60141003142601845c1d0029422 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 756563570 1250 756562320 756562327
    0x21120d23070807090801050702011506052505030c0d080405010506090618071107091a0306270c0d1109010503160905090a050d020a0b011d0402060913020c0a050f030f 73
    0x407180100c40842d0071403224541181d020f170b200c40300c96096540c145e078840010f0b952960401314200151131a0f4014180902e08546040d80203150740e0504a8820707210444070108a02030400c100080007111421201141501e40d0408004400b8140040854040c0d03659420107002444501c1c00c0d0858601c980d400503e00c01002111000340000500001e051b102401000b0400702c0b40080c0c00c11003207000301f440c9913010514038103810580080990701c3c0750702c0d8040d92100b8140a488401d4160220074042181e0300204640c065580c000e15004000c1401d80e000f00d0745004910034800c005080500b4076205070382ca0744891340e940c070625a449084486c082d0a604245034188008040c0d80c1100e070701302e407051045444458040d100d1500302002c441c0300c000580e101c07202d0340041001403c800f0b801002008010307908015800c00400c011000240001c0c401ca5000600f08034030341c6c2d81c0c3c1c800821908888421501c0b403040b440207079a01ca00d040d40954a80c40b80c896551030943c400000ca8405081200d401402c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 756564820 1250 756563570 756563581
    0x80a06140a122f0103061401050715021201030f140708060c0c21031f03050a02060c01140a0b01031103100909170316081609030221120d23 61
    0xc48090350100e80a141414061120005150f2103420752105842e0f240c105221400000d02154036039400344124001d0a1817018040ea008000d44a0300e40c2c100c10340e0391340c0c5202c12510000074401d0281d050a117900040010043c02400b80c3c03c01c1c1601d12441001c4184070a040030107035113403000d00c601c18850b0700c0f2100007180604180b010b0102880310300219590070503400040b004003954440c0030443e001c0302004000b00c04400540c0c1d00410a00080c1d0045000d00b15203c05403220003420010f8055440042c04e121060703001d40c40500c402c034004840582505142d4084000303018010a83d600107810b00c207844075150311100850340a0741d001140700900503d85141140500042c03001038920445100401a180b503506004603c80c0100c10b03d0500104002080134204000280000401401074a40130260540141d10b02c001c3d00c0e01202c600000e0004108003d441d07080d640d81542c01401043c0011100d500d0042c041c050851803034905115141034809440c0d040b450100d00300b86c1c14401c4801151 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 756566070 1250 756564820 756564839
    0x6060c0201141c18050f01020c0c0d05030a03050408041502010e0d021203060f04180305040302090c0a02030d0e0708070801090b060d1509020d061a091b04230a06080a06140a 76
    0x4458100c44803030030703480945c80d400d0400880d0700201e03903640d4000400880885c0f080c414010144407c5030400e00d040c00c0b40e21802e6580c00340c80100020b16603654041420700000c00c0c2910000d100112101d80c442c41a401c00034040c0101100000c11403003010b40314021240045800d0030a01c0c1940b603e54219178800d020042404c03845c10000d50480d642e12401040d6006510502412600075240c0c15511441c502c1032040202d4002e00e403602d03402c0240300640200380d0102c115218407840c1c0380c0c0821980582200c4a0604030702ea44002c1481c45103801c005031a16040d00901400c600a142d00c03400c503a65041880140014a540208049015516402401c2d0340d5407151107120300241c00c1c0303404821680d03507081c12203403950241411280c0c54184894a80380a000860b07100560903921440c208081c0c108200900480c084e40701c41207641420032035620015442c10000507001040c00382040d542c4c2401420100040d500301c081076081541c082424120340300c00c0c45040030090b01c01d1183e5454540c019 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 756567320 1250 756566070 756566081
    0x503070507032d05120a091106072301060810020408071e12060509010506030f0613080c0604140709060303020a030f0e03060a020307020d0c0c0b0a1206060c0201141c 73
    0x11140030041e80403112400d00c0e16241040f50059500c4030f42d0703948241c410124007140c1c010245060542050003800010f00360034908884040c00f600c3c4580c03620141d161403c1d815948400034812030070840c2e8103100110307054101004803500d000903a40d040f002540004264850360007600310355440750031308000c42e0b198071001419141c1c01d02c800001c1c09449034a0480c45600c414815036085466600340500343c6020300c03071a80c210208070f004001040c4288100ca403142402840760304483c522401610a102080040b40c44541c043c0c406e030341c3c50b89050302e02601b54815507800303800c0c81c4c420b8910116110282e403207288240c0783c06400501d8841d200d80d600710381c00d0450b00305400c10409096809680d07914100002406415450805a00c03843c160b10000e1401e80d0f010782071400c00150b00c000d0008154a122100309446000e020b0a584001503501500c1c3d4440030400c5d0030310701d032a254002903c1c99015444401c42072003641c2d407a0140328140108000b501502242100c000d020486010b00c504007039121 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 756568570 1250 756567320 756567347
    0x2a03061303020316060204150f200f1002210408121513050712020f0f030702010219270e0703050403140c03073c06090b25050307050703 60
    0x1101d00d0705134141241d01603502e01650071a111034010409001501052000080400d01c1e07280c58003110300242c00040408041c0020b9071800c4004072102540d054083c450800010f10390401c45000d2090b5609400007540403400740c04542d40801078001000105080c034900582d080385625007810a0700c9400464480c000e400160741c80c0c04244e400b40d05441d00c0e0300e100c407291080540068185400c10b8080d0565101c10ba0f030892592042020a440c1003180c0d00b070b42c00c1032840b081d0351501e0342c0d80d00c0c60903402841595850481c2d2410a0446048641d2000c0c80b0040c4456107000041c00303050142841580c035486029142d040c4080500164880d4403e90049500900078079146820030400c44060050340e00415100459400004200f0180800c609252131601031182814080410300030308501b001e55800030701179008003e140c1c03950902c881030700300024180d0400100074a074103101c240c068401003000740104a070f01c040b060111030903004000340c0f0720030040b0780c5038945400d5965500b110040080e029 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 756569820 1250 756568570 756568573
    0x7080601180305030c06010f2601060b04030b0106140f030106080402031c050408160305030a1b021302040306051003111002071a0c100e0c01110f0f2a0306130302 71
    0x194440990068191240214000c00145584111781d100e0241032202c145c03c01d030b40c0402c401c40104a4217500c81800000041252154000845058681800750440742d00040700c4010200300401807000c2a00c2c0a4126901604c0d041146405510445420700a01441d041e510000344010464039010341c100690285c40281a00c83e4041c0072070300c3c4078400c0b00b14000400010700106041c060803608229510f5203407070001e1205151851a541c4540d80c3c49490506000c0000c0d103a4403960301d4122000300e03c3c0066000345094500140c82e0f030314000030f40080c4001e071440c6041201043c210144440074400303030b940000401039000500070911440d0100d216600c3c04611907a98005590580c3c802c2c5001d801c01070000e03040c0d8801c00003a0191902d4140000c0f015a1480e0125400800311b00107514511041c00f0b00b01f40720302c03c2003410113500f00750300541c00c29414064036440561039400400c20307010b10700c1d4a100100c41c600c0540c09034911001c1042d901c503050340c0300001040d2131106014101c26040d10910 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 756571070 1250 756569820 756569837
    0x150c01021b070614090307060e03070b0726030405120307050d1508070803030c0d0f06080f15011401020a0206030c0c12030402100503060d0312021e0910020a02010807080601 76
    0x2806030806180c0c10001071164204003402d21a1560200c031400300c150304180c0d40c9040541c03034400607031510301920840091002250011003142c034144a154001d20308860215110100c03410f10743c9464030002408440640030400c0c46101000e1081517a0007550807100404c4021752403c0c0c9050f06602c0a01800d003480070034000d6007190207840c0130700c4140d80c1c2c1540d00700e0443c03850320407030f94903000503a00301c0d410360b40041c0304200300e5070416003d45449200e02c0c1c0b8085100f10b170741031f2a40000e1000d500007130240d0090f02300b0381000f01000a114295440c48003151912a80e86000304c01d150703040300c2a610b0041e00010010000b61a28030b02854002c4102e004213890454016503040c50903041403038141d8055400710401c002d6141200801120701f80d0380c140030b851450f00b02c000402003030b04200010181b0070300c2081c50804003074981c1034440c64001d4018441d6400f00145811280e9000500060310403440e10080c1569244040340032601d00d50f042c0c603480802d8490407000e07103d40710024582030400c810807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 756572320 1250 756571070 756571087
    0xc120901110f0403112d0607020405040b160302040627050402030412030c0804020a120311030a02030409060510080106120f0908190801030302100c1701031b090902150c0102 76
    0x7041a101e0b9100d0b110303600c0c0d2940c900140040c060500e021310801006011400e41d02a00c1015400312004c4420300751b000303010a00050050251b1b10010703400c1407505007040100120f61109500400e0103007120a55082c2c4044c0403003ea206501900f4001104800083c001142072140524a0602c030740103204800d032a803001c241240c1040710191401184100c0d0300411513010311a018030300080386021a034600d0190089007000c0114030480400c1d8104a58480625110390700310030401c0d10326001d881e502c51080310000d503240c00a00456603031f946403070340c00100380c0703007030349062910443c00e0300c65001c0b681c0382a1040d1503401c440100e81d885543c440c2d503082044540c0707209400e00248940800313030b2140031101110599509652840702402071041c01840800d400295809401080d1000840c465038025021074103e07071490450400f0301c000c04004003c02800e0707000340ba010340d1100200981c1d036035110046015a4500d001c040d420420b510f0002c448050b4000042600d0038040d800940f0740074a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 756573570 1250 756572320 756572351
    0x1803030a03050f100f06050702030c0406141315050108041b08030414090915130c140907090e01061404050618091608060907021906050f0a050c120901 66
    0x540840c40040d5031482042060f803501c04440390045403040400700030300e007029404140c4800c1806614240701c3d0100342c4008564041012508924001c0c205000c4950384411020000c1320105206103d214110101e01c08a03046100c5c0341d440012041c000d144291501d40150b40c2d050340904207a514208440c002050b09903020500c2c802468010000c40d510f0745014001c440d9a603220740002e02c00d102e203070240400b9600014102c2d9501d99580544216901c540c0c81003549400d00110050074402c0d801000115007003083d00101d50421b0946032001705940d0458116001d0707801380218000d160b00d40005001091154028040090740703a15140d14007526200043c8054000c40c881e0020051130707c0c0e1240082c00c0c001411504400780d5001e0042e102e081c3c1101030802070300202840c1c02a900c0800140c5554400c11030503601640304001031020740b006007441c00c05400c04440142c010002c0e0008941324010300e00c41c1a10400500c00041e040c041c40b45000f100525025003001c50b25920341e180c2e14183c0d0348 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 756574820 1250 756573570 756573577
    0x60506060f03010b0d18020904110105090a0f08010b04060806070f030617010f0609020906090d06020405091905012742050f090f042f040b0a030c0902180303 69
    0x954007503451719141d00b146440150341c0c0042c41c60754050302e10035000c2c00507201da4000b02d030015403210700c1c005044903400040701c0501808650303030b9018101150003d071046009541d00f00b0744090900038046403031403000f8001980c0302071050600a61101001500c448c0c0704030b2000480c40950b24002c0f411039135a130384400030210312041020159650b400c4e85032204401d4480c120040c003403c2025800c015140d0001480d501601d0034481c0104c100c00b0b075090401240368100c50152200900d60310460400b8074520280d08605a866014285440004101c0c2400f20311810030f00e60302ca1000f004180548040d000103080620900701c0000d40d034040c0350072184000051298240ac0e5603502c0c10103052007006048003201d49620a5002d8000301c0508005600c6280103550b124040e1a862661a10381d4034045581200c003458190b09441001039242d6003655030700301e000074410119420704c200c020f10030400184001d54032005155400906007040300301480d401400c0071904044516007101e00c007401190070f40c3d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 756576070 1250 756574820 756574829
    0x513050705121005160f03201308030d0203100f0305030301031202010e0a031e05040803070809010c050a08070c09020a120b041508031e0a050d02031005040905060a0605040c0c060506060f0301 84
    0x580302140e803650319501085503d000121b074030b428480070300c140500203400208091012608200098507100ca40000780c14200141144011243e44940c41c8400f00001d402c191035109140c010038100042e0b680c4030014100c1a82d810201035440c1d6440c5956106c030800005584000755501c030300d2540e20680041c07151600090298940c05c9041c006c1800d82c1c0c94440404c20b504051000902040c4408100001510078003980644401e0781d5a10f4900141d07099042c03010010f140d03115805081c0c0400c201a006864014401d8682c426182d0f150340804050f80100d810401c0044c03c42c96030525001c00f560010310300c010001d48002681030f154060010700e502c89400c8001907034000101c0c0d100c00c0c28a90214004100c00200d0341d0300f40b50a08030020814440c80c4d540c5d150264000c40401c00c04810074030320f13900802d0001e2040025950514195498003001c5410440c180c1c549040000e10b400d1502443c640e00c1030907036603144203215030f503940310003080d0140c2015040030382840005801c0350708800550180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 756577320 1250 756576070 756576091
    0x7080d150915050108131e03032013120209040221032101120209040f032d02070e070e060c070e040c090b0303040e0c0d0915020408010513050705121005 67
    0x21400c10f00050300c00314000d130400b07072200c0740e1000450100714081b6001101d0426648014019070690800303d02506140700000c50b0804011280400c0380980d4004140d07040b1003c400c00006c9680d40705c030009501181c0c4000c0d41240c00400060010f00c0d05400c0616040080c11201e559403201043c03507859900b000610440d40031010001d0181034441a1205005007410803070300a400305568013150241901802c0100701502202140301050301070000d9460001c415038101d00c045400301b00a00101350b01040700d03409801010f402040181e01038101c0c92080b0b045403640c0a040e440041031103016884440710f0ba0807401001d6000c61101118000c107809140902c60101d5140d052111304011900e102041d80d200b5442044108641403010700010760010071100301c0768660070300085a001814500720014660186600c000d03420700501d502030420350301d544000300140d5032041040c034841c0311010405099548110020001803410707120300042421702c6025500365008030300032041601c5098035a81901c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 756578570 1250 756577320 756577361
    0x1051e03190c0c06060e04051e0102040e1509090f030a1b020603070309150b01020d030c0e1203130807030507050d1a0411091f090e0a05071706090307080d1509 70
    0x184844c5001d110040c0c210760380c4003101d80c10250780707036651051143d44003030b80214918820501c0aa0a6050350003c3c200030070700ca401d6151051494004015140aa81c81140d100d4049068418000b46594081e00c581c00103518008403040c041e40c948501c101c200da051809050840016102e41c0003a5004640988000c51f907180d00c1c3c035000341c0c14405030f45001c42c82440c0446d4502ea5aa00082040307a41649040014000c114018110f4551030000d2842c1d40000c1040d40c1704008440c004000c1c0141e03a0071541110415445149580e01d6126601c0003422a621900081c8903510701951082e043c1c03849524024502e100e4002d60362091102190156503070111003040c444581094004035522035200944501c0301c840100800d410442c4a004003035006070769017031f101811041089501003003904201280c50641d642e0300000341906030000202070300d0044902044031428000113680505502c1082c007403e20398a1041140103107103040900c3c015002144001410503024800c00c04d42c1107007415a10b01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 756579820 1250 756578570 756578573
    0x30c1c150503030f0414040e03030403080910060b030c0a1b050106080c0103060e041704090207050c100e1509030705040f0506032e020706090803011e0501051e03190c0c 74
    0x211200301d910140c040d030030400880c0358030160401268292013281c022525044c800e200450028410111340301d00034403001080c00203240e00100c0b40c1d4801c1a100003182c0a401c1c640c42d00c00c09494082c844c2060752002440410304510400d00500380704c840314074010f42c58000c0428000804c410805081d0361a946d240420302c0501c0d030501c00b14050400a0a05009841c9042001800c152000748090088000c00c1c800c100d152506108036402406d40716401e40d111100f40c00e00f50380b20342c1404101031040340880c0c21310b0003e5008103101486484003c040815128400261115640c06060705d181d2501807582c0219281d940c511404080e440070080024041c5001e1080c0751908203031903842240c50820520840c10100c00d00062030050700042800340e200e0900f442c110010b8602c2200040060001000106d6005080d252501e40c2400080002030410b54550042d11244515011a0440d12400c0a003a0045188400540e0400300000c0ea02c00c045200000d040102c490200f40b200006024600d03640 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 756581070 1250 756579820 756579851
    0xa02070c0e190c0e010f0c08040605040e01090e030702090a0b0603330f060a050d0e0604030215130f140a080301080c030f031801051908180109030804020105030c1c 72
    0x800c5554414003084200040c00c0d01400d02c02d81d840c411350402401180c0c043c3c4440c82a4602c80d0111fa000ca0b046440b10340301d80340500315411a00407154401070071030000440a406001e40741d0744d04d4a1340051031400b00f0136000e010b00000c0042c032402040fa2106c030b60800d2034075008000c5124041004880200c0203000c038003406107461100500d82440402d09060f503490380c85402600301c194007152850394400d41254151100e0144880c00860b041c5850000e04e400b03000402d0280c4103900ca6825240c2d09071170110038554001c800d960460358001e003a1b54590005003030038109111203010340c600221090141401c1460101058003c41d090407000c4010841c3d69000c1106d8180e0380800c5024040c4021400b000a03030740e020700c0e0920352168146021100069000744111a00d10100c0091002e441c0c0c000c141c050180d4006440340d00034040c508552401c031040603c941d12582782c0c5a500c440b0b1944491300111900d0304042d0040302c00303440030072282d19000d40307061025a180810000c08600c1d41c0c1218800c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 756582320 1250 756581070 756581101
    0xf1e041d160f17070306090e0c151c0b0607060f090303050c070201051903060f06030c020d08130b19020c01050906072303041b0909140f150a02070c0e 66
    0x1034081c040c05100301044660083d0340c4407102c0a126030f902c22242e581d000110003501003030b402407441500d001e04010800340081180c11103a001910040342d5010001c0540d0980d1013544402d442d0801c2e9008450000c2403e81c2041c4200100140701782d003401901e85407042114408800060615504c0e0301240405406000b0749901041e109989401c005950f000600740d48919001e00c415448099607111241c0d001b40d201d000503100010443c1c501765101c003c080e00416030108500f0249c800d14800000d03541c0304050032032040c4100d0403001907600e007a585140003076070050600d0340c1031012140c184001c28080e10103420038058110010031b80c0e08002413550b04040e4050400d42c104a513400c1c00002e655000092010054a0745d107042d5500d80c0c50381800310b10f084140c0b041c001c3c012840040048c500c16035801090000f4000e2001c3c8450780a0b402240740d8440c0e0b640300b641c515401107115404104440750b0030aa000003416405881c081c0c440e81c076014102480d4102c1c1c01c200365060309006d40a030401460 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 756583570 1250 756582320 756582361
    0x815060301060f0c050106030807050a060605060f040b0d060e13030e0d11120304030210050408011b1b030c0506070503011505040503060c0901020f12031b0f1e041d 72
    0x2a645103505004008041042c880080d00034000350580d0041085002d6006000130b64010307403820307114141444e0407500c5010124003640c845051200210b5140790000c1181d00b00c1d0b032031004035481c080c40c1c00981c0b100c0c1d0700030041400c6490b90b1050005600301001c21442c0c41404195080c0380a10158135020346510705e407200490050841c1005100040c6071460000a110001c4480c016000c1c11402541d02e5403003030b504001d4101c142030360085100b80d00a409082070b5103201d80240900b585180c03841d140e09003015079000005e0602e01d0034628a201190403c030700319001e0320b0036202001540d20303400d00d082c10030b0b20036400103000000104107035584000b044031420243d241c194030300751920300001e80d600000341070f4014102c00021050007030b80c020016131000d640c2410540d101d01d03030304517441170b100d40040310213240802040d4100c445505c151411a0000403c0c02a02810030b103144071900440b08c001c900c044000d40c010000400c03c1c81a0742c1c046020704d6100b904081e01c03850030b2850308112010b4001b1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 756584820 1250 756583570 756583579
    0xb1e03011401120b04210309031106190513080415170c090603180109051509031e0a171014040b09150301150b1905030705030c090303090901060815 65
    0x51081889042044500c00d400c210013004944550a104401500050310340b0340010303c01c1d030543c42141e055001b0f080542d000703440310302d805c0740080b4841d40c98420444070000c075203100400c6644044c01c0307a032010390851418800c800c0652580d40d1480a580e0094010301610500e2001ca2040e150344818913440c840d80708000c0c081c10742003d0080c0c000c2d500540090b28820380c004400035501c3c03890102c07141021035000c0c0c02401440114103000d6200c3ca0181c101881d01186200041c40c2c141d800000c960540200c460441750400500030388a41a420850f5003004000d401e654901a0050070038196010b5141240c150054916081030301a1900c0742c040e0281c003450601810313100c5036942003036080e40708003044400303010354400000003401031420f21210000c028500d030000c98092031440c007508101840b00c8080481e5561001d003501c280c0001c481860004500300002100180441c01400000c04054200c070f00300039104000512440d000d130030000000c0e014508010071009150007159000700c3c10396 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 756586070 1250 756584820 756584861
    0x310303030e0106062c01231b030f0904050433050109110306090406060e090102090f0603090703020d1b1206180804090b180408070209150a090905010b1e0301 69
    0x21600100764042c00c480f1404805d124200300164020708140c03c41c0a100d068514404040202e81e140b95045188aa046012420040c02d084000001281d565440203003403039060034101c80800c40941340040c811600c9a151071b80c21100210702c100c0088850807118454403601d03907405d401c8011200142d000c403028a00384850064002800800c40740c000206171614040c1d0358aa08110001d012161700017070b81194060208000c0810641c090b060081c0120f44802040441504000300e5000643d184070a54001e0b00040006162510782d806030180f107102009100c034172030030a001900ba00f80e0b10618440c12140c0350b40d000c1259510642041204c4400c0519020b006034894560500990281c2d000c21030b41c40c100000e003031341e846258803510455102105a00e04d01032400c1801500401002c901980203000814011f0501d60804558140050143e6034494540082c15001c0c0459800c166101d5507202030b05a10f581751806003841980b1900c01e075000500561050508442c0400d44200f450048003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 756587320 1250 756586070 756586097
    0x20301051f0f030b1215091e120c0a08180901050102030a092106050406060608091c030c20060405060a0606091202040b03030a081e040305310303030e010606 69
    0x290b00a50450070615000903207003e41c501080e030520484c03160000503c19190b80e18a281c0122406600c02c012000035110011a40884000081d2400030b400450f034101c0c05843d00035a80650103040341d011410b0840394515541e469501d100e5001410f00064540688000c0302c80d81032402c00c4500400007032004510f0040161801040050075004880c400c00070282101404400d40c0c03c0309911a820403c200040c4c10149805030040140f0302c503100101c1c0b42c12000501d0094089494040840f260140361902c8540100480042c4616001e40d41031140c1d0092860209081e10083c0c03260380c403100001d0120b420709050440c03801100070441d00e2128142074042c40020323800700c00c02007180e4014070061180481c1d071000501a2807090f101c180c251002107040a8071070b51002440d80a255544bd200080c203504041c036000442c02124043d000c9201000101540d9800000c2c8015004c500d039240c10b800c032040d040d0b0307180744500c6601c1034000070303243c6907040a683c800384191001840c56041900020982 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 756588570 1250 756587320 756587327
    0x40b011a0a0c02010207090606020c0301050106030608030304030e0114040620210f0705060f010303110a0c060c051f090308010e0702060c0304030e1906110c060306040b041e020301051f 81
    0x10180010100041d00c0b03600c0742164020055040a800350002c180540d40c0c591900070b40c3c1d101031003900e601c81d40c02c201c000a103190180c4140820741c0c1004024520f1030345c0356141987d008d0b01c582d42c03d81c1000109511903240c500c41e0f801a00c0506903d43c1c4503004d07a000c000e4010b10081240c42c1d0003a8a400400d10582c400f901400d402c01201503440b81e03151600e03083c810f42203840c0078954024019000388001c01000002031900369059a00c2501c0304030021110308030681d62041e041400504440c010502807140c24087c0d04a1000319120360100c0d080c000018180c00c941c0402c0040d03007076074542c441c4000420150081c803800c0c09043c1e0382c3e0a4000a00d0160307002503a545000d491500c515000001050525200340c841c05c4c1c14030805002420792043d0481141d21208181c0704170300c0001d10320101c10a2413580480c2000843d14000d0a41d8195100e8104000007451200c0c5281c0d480b0355507041c0e00205115980740b2031140900c009005859614110a221140464800807205040405100204180c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 756589820 1250 756588570 756588577
    0x3200a0c020d021807090b0307090509250206150409080a18090e0309090c09130b010203160c1a0309030a05070c03150e0c03030702030718091703040b011a 68
    0x2414541414812081d0002c00c01c01210390001a4209140b00b60056503282c0701d405090048072a80d0310b6070480c46d0358200c8800e203808151400400190184003c1003c4c2c54010f540d01d81045595058100c841c40c0103120b00075914040d440313400980c02c100e0030400c840740f003046052100b10301a601403200c0041c681e200c1c04c10b0701c60552a4001d1100d0b5451640305c071103108071800d010b4600180104511450401d03640d0350b0b03801001c1c1e1144250310602c0022620f5003e04107070340d85c4640181845040303840302d20600e0f025044100c0b40c00d046101c01c0c401906044012400420100e004229551003107041c088010300b000010380c9050f4405508005100410100000b10340034040103151803070320340000c0d03d40b01429000c198001340040c4001b603068820344031242d10002c1c80110302e00440b50b070340380700c1414183c981c02a1100a545500503d9041042c8600d2283c0040000961040001d000180e691944404c0440c081031400400d00801040200070780c2818050161501000f8502c03c1303402640c1000c114403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 756591070 1250 756589820 756589837
    0xc0f0f090f1003050a0c0905070f080f09030c0706030204051201060b12091207051506040605010906050f190c110913082a0c031b01080403081b07060501060320 70
    0x8070780780c0001d60303690384082c440010715400300a90b1084d100750305000c0c1c0495524007401c83d20a25200200e1542405507030400c01d8202c06407605061135450b0400000b28180040900c45180010019084154030500c4004041e01840c0c6005032a1401c09050140c040342c40904000c99a240100510403114650155a00341c0e02d203440c03608030350380c501d103d0500302003c11003a5031403600003154140030464082074030242c2280c03458201030195508820081500c1c840e1150301d02181e00e0150a00400c0d00c1103005001d41c101901a003480c003054450303046041151803034190b00196605a160003000526042d00c20a00b90844400d60715040c840900b0030030f1044801c0040000000080a902c9014010004201c00108801c180c218400f01000141c0341e22034440e5562090080e00210880c01c05c03000c0410311a0003041c0d45240340382d542c0b80ea09032078002e000b43c18100d02c40b0410490600f481ca41341c0040892070710440011510f54545040503045c0da000150b0054100c10100d800a00200800203448400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 756592320 1250 756591070 756591091
    0x8010b040b120702010b090c270f0f01050405030a050706020f0f0d0c030c1a100819081612090f06030e0c100e04050f09060c03160c02060d020c0c0f0f09 67
    0xa45804100307a005080034840b107600010004104002c041c204d1b001340c45011274940041c848520807a81359030720300c08074000c0680d01c1000c0100500340390618124800040744181001e9160079161800a0326100810200f02c2d92544002003d209490381480390041090b146001060201c001c1d10398962211607200c6940c003040000c541440c203040c82005140d040316001624100c0003840d10303c1801c1c00300b0003110f0080030709042207000100c9680005648052450403c296501c0b840035a403070b00160b900c0040c003044040003051402000c50000542a80b109407192158000c503490401d4614030564141c0c05501414074069100040b140c001c16184007049045131460040303c14a20140c5010040701001d41e0007038a01010024100c9820b80c41c640201186802c50381c8668030100d038009180310403101460062101d92180c60214080e11072240703120f100030000c5060100c468030a0342260801d410f0144030f07500a10418030241409500820500c1090350140c142e03408400100d407140c10050000d6842 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 756593570 1250 756592320 756592357
    0x8060603060406031b060216051c021503070309020a15051603140d0915020a12020a020316050a03030c080115080907030507120308130b06011b08040603090308010b040b 74
    0x103075481c0c0d4407a2004e540e010084011540d115a100402030311a4001c4401510580042c624080b0610b0404000c0303070300041a4a041c1c5c440d410b8407004148070302c04207e07000b032002c403404565a00000c010313600c501100c0c0d80014900e0f00078010420f00080741d511111604420203c00d0300d2407030f800350894550030042c640b04c143c101083d241c00c64240707070040444110510081fa21003004e19968100001440c05105018039031000c914191049103c0c00300a88046103941e507040c00130b01207a070007410080c0d0701e40c01928144070354111180c4c40036108401c11121a00701c1006501099090301c10025440300910b8520559814084080b899101c070008010500a201000801e010b00c00c00034000610b911405a41a02c0d954110b0313010502c0d048541140814070300b40004003a500ea48030035448098010240c504a52100401543c242422003905040c1c010100207100110702e0600040006003442d1f0380010700004107013070082684030103800200900c101003104001030040b140966031340b041081c00d88a031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 756594820 1250 756593570 756593581
    0x1050d0b060d0209010b040306050f0c0a2304030b0a0e0a2316080f060703230c120c030901060b09030604060e030c070807050907020d0f03050601050403060f02091f08060603 76
    0xb040708070300c0d80007907220078100000701d103001000700070381f084a00c42ea6042c00350391141e41c40825041c2d0100c0707001012400a0002c3c00e45580716440c1440419515945246d5031190303120452580e80c0640c100341e4180a40009000701c0040d188643c504001c69032004d084444a07580d100c66010305403410407440d81405000740310b1488014410b0306044416000c1c0c4400041c1d86902e035503110702420145200b80d014600004068502074014140044465045110000f052001c0e400b4418000340203034071411014000d40080301348030080c02c2d0041202c0300d0310710b0322450000401400d45400d9040b03070048400c1881580103680340020343c0c0d40c00962081c070104940321140c80d01840c50089001000c00c0c2d102d0054001480580840c03a4401c3d11001d0b5125074041d5118101640d44002103111040001d00310001e1561440c401d510850704030704145412442c05603251500d100307658089840640059000491001501c2c00340c001c008540007500c00c41040801000c0d010300300c010010151405208008000369 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 756596070 1250 756594820 756594829
    0x209040605060409050a0c1b0209040c0e0702070806060a03020a050f040912030903090506030f04060f0605060a0306140f0d08070f060c1e0503091902060d020a0f031401050d0b06 78
    0xc01401d005070a141e192a52030031013402404050746d2502c202441c01c492642c14038810841c195124908101d00e5503800c0c45c5030300388202076030002c01c151401401804049040301e0207400660003803420f84d00600d400c0b420001c06030704054003d030405203e07440c100410130068403080c11010441e94112180080c109106c4042000740036011001000b14070b107000f400c0443c5815510441c0c600b070007503980342c000c9900da800340070b02e510007550380c6146042401c0c0000d00285840d00800a5081000c00c0419035503070701e0010410541110381000c0c0800d8036034800344107184000031120340b01c0c3c40455101d0b000d408000c020821183d0f0b408805811400d0000d0b004050004808500030f0082e4800800c1240703001c40c0d10010040d1b14a001c00343c0e00360003429070304151b1a10030307000d0300c1c0200e1103503024104000b24005054400c105a40040b40c0060040c025607102c614184094a0280b8013901c400000070110030004045600f45082d080f08890074030010700403504c33904048650240e0245a209203500c1e10030004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 756597320 1250 756596070 756596081
    0x60a1e030602032503020406170402010c050f251208070507120f020f0405060604050f1305010905090d02011a0d060b190501020c031c0804020a030c0906030c1e0504020904 75
    0x1e000140000b0501c01c030354040da82e003084204980311110502a00200d021000d03480f44c0e00c00c1800107407110410b880304103800140a9081407050404270b03400705c580da80d0141004002ca40b00703095600310314008000c548401100303110303001040d40e410422504007114590000507042001d4a54140454200308103c800c01c006000f800b0014a0402156040c0c0313004901d440759500128052044c1c500d100320701c3c0c105402002e00400c0024811428181040140080c581150340d02e9070780504018404800600d0710300c100d0303000c1c250031700380460315140020b1000c1c0340c4612202d144045a1404070b03001c21080c0c101c10502d041000444654030025410f0410001400364403504942c030007518011280541e03051103d080484030280c0a883c3c1481c000010181c41e1650701ea02d00000f4a0500b14a261803803041900517400307807000f80b048030402c1c2c4036100e4181c10940368000000b020350707503031043c0140007a10000c0001010b12040c02c2e6440c030220b8800c040a80715505c501c0380a0b54000c19140d829980d81d4115 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 756598570 1250 756597320 756597323
    0x90a080a1e0c0e0a020a030b090403080c09151b06010503060f07030c030608150105030132091603050105010302030c31022b0501050a27180b04120305060a1e03 70
    0x1c1907140c18203020000007584a000440041b2346880c00481041c24441c0b03441d44079641546803010190748401c85410140e21042c0301036030006040c20002002441c50006c0c1c12011402c0ca141a0301700301c21107940707103043d0741a0000f500c240e000b4000c00103000e00c400c8003154048210702c1d01040700d0ba1020001d03005000c564000142c540a20b46400640300d003540305482c1202c070304800074410900340c11600c80c417002000103280045032a402c00300580700700059480d50070000c03c4084560110b07039460542070350440d64104843c6039454000400c25490100200c1b621110300321803010800341c401980098009408030303100400e000700000721303c004096074141d500540e012028014400960a00303006040e03a0740b600305106a15060000c07a0701d0078803540c14025a5861a0301c9900070b252004420310b04240c01c9140b0b040c0545030100307140c0240d600461412040c2c403940506060341031071300e00303580401600c1c52808201031034001040750a40d0340d2011107049505034800001400c21449200e082d1f0100740c0c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 756599820 1250 756598570 756598589
    0xa051207110a1203030c0503060f0616060203090d091401090303030b010905091f0b210c0d110c10151406070503220b070302060403030e10060b090a080a1e0c 69
    0x3da0703001035210341940521998003040b6484004c00241c0d110f000903a0101c4c1c021a2000c480300190800c1c0c1c006141503042c091141070b40510350341da02007e9901c111000009904000c41040e0507a400ca5018006802d5009442c0000210f070f0f0300083c050b071076034032000e0101900d40b01c034042241d0242511101424003c0e0485da400e01c3e2560340e1100301c0001d6044122602e0141030001502d90080d015110314a100704c0c06451000c45121102c400910081d01e8590b220308204811545096248142100f15803580001a181c104069515003065032075100e694034036003000d90304405075010440b40400c3c1c944100c0581c17011091880451242e0051442c014a14400050920105481c04050720821b020750322900e96000d803195910070b803c0c0951900140544c1c054000306000074003075013110201c00341da0811078403561011082c14023903c88540c0a10324600c0005404440c1d4240700d65a6030243c5000030040511082076514640303c2c00301d80018010082c450b00120003045000301909004100c001d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 756601070 1250 756599820 756599839
    0x7050a1416291f141003050c0c07080606042717070501050906062d100c1e0b0a060e01031106040807030c1d07050910030f090b16020a05120711 63
    0x1180103c3c07003002140345541c01001a5000103021900d00030a4a507101c010b092610031250301d2205402074540501300d20303c10403080c440b0300c0b400f4204104402c0188159001014941001c50920003101c210702003c481c00700701ea0580313803012080303818804a0164000f4103251041000c002c81c0089004886000341a5420134040c001981e03000146035004180031280d0f0b448000005803244072001091806202000b000015800c02c0e2414a020045104403030400200c00401d59650000718a0b044203680e1b00180c0c002550300c2441202442d66500c440d480d40100b01181c245a40c007004d68005110082240c1d0b085c0420260f151110001d13640202102d01c222400241c5038505203160071240d001e6900e40303d15400720b0b601c0304c540f9058864050003042d102c01c2c0c6090118802d106071a845004020149a2100c40700e03034036800c561003020101c5008d00701c586131a041100505206081e001c5045046500040c00c81000c1400820150444280c0340007088da076411a181c10402c524003c2e000640c0201c001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 756602320 1250 756601070 756601081
    0xb040b0405030c09070906260c0a03110c1009060e030310060206100f06050307021e01020703030b03060709053a0311010c0801060c081207050a141629 66
    0x540161040e15411002d407804a580c03601407010801c012140717440095081e14080002502421894803d0b61004c00340382c0000598200011003c40c0544042e0034420380000d40e10342c1c8613814403d104a407041404518a41801180c0707143e03075010250468004140c1e24120202003040503440b040722482c41c20282c80e1a840c2c095660030841c0c80500c29040940616000110507490928079442901c07a01d400301c1c03e019040900454040c3c00003802c050951080081c100360885c1c141503940b110000400015079503a440340f400906a42e03d000d0790500a5000b20180300140b608003010b01d058a000707841c140381c0b086404181c0044251549103980e01868001c0d068460402529603000c5054001c0c4c40f10070f500c07004412090708885010700b0400004000a0050150601c50360a403d00c40e8000c9891600300070010880305001c1d0070070390f4000c010500c00034100d1100c540140750709d484206600081e0f4208410112a443c4010340e180f4018140c124040d07080e1150004641c01680b046209500c0012600d0310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 756603570 1250 756602320 756602339
    0x1906051614160902030906040b040201030902043e0a030209192309090c191d06120f1011160309030b01050a120b0603070e0403020120090d02010c0302070b04 69
    0x4100b54244100901d010403041094000c990191125030010a0f00c1d6907251a002d103440c0b00644200d041584076500314015994a01075240c0c50070034a900101c4c00103c107140400c8400c0d0740c51200343c810446031909044096401d041c0c80d03441030f25050159485030f142c40007580714401100706100d00d481d042000b02d803210701c0c0c0c41c440742841c10485600a1640d4541c081114540c1c080352600d6140e8802807982c0214100250360380e100740d402000781c940c4140c480d009490898400d519503142400b111007002040c0c40c050016410703e0440700c003d0460303000100d4009444a212943d41c13202d1903240d81d17507821411324820448109086c40e018941031103000b1300e0003c0003281c42b480142d4615601c1000400c4502d4080071a02c1212031241c0d1854010183e6a030b58403036500000e0a03250316000b004400100d044c58505144d1007103200e43e00028403c1d0200381881c19901c038103c0500d2850f6403d01904d00720f501e581172610041502420807100e02280c520742280340c0441500b007a07580b80404140003039082c42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 756604820 1250 756603570 756603583
    0x1210120c0503060717060112060b040e060306061c0b040305040f140f09010815090a050a03022a0f130e0304080109150203060d1b050414070e1906051614 67
    0x40c102c080d0f86540d00e480108451001e45c20b881d82c00c0d0b01d8590004203001c4c1d8028401156009940c00001c542c45076140240a0190441d03800102600d900c03a00700465450140501d0343d1200341215030300b50003540c010309a10038128004c0c006008803914030100f014180108151030042c031184260f008400e480740010005082c9400c01c050184a40541c0d12159141680d4070034141c40399040104030042000712201d02a1201030b10000b040e0082c0941c500110f0350910000074603900030340052606400c4071140941900301301031001e041503c85164890b00c1d0340c0ba0740c05101407581c119040c103203540c14180030500610404003400d020b44000200044d410704190001c045650180310f06094080544580388180c1c4411540b20394804c200d807040e88000303a0419000c3c0d01c603600c60441c8042054a4502041c1140d800c261030f0408000c1440421504540c010214141003c094401c510240c400280c06440c40042e07000d00000d000012400011f004c6001001203400303500f1007070007401e1000201d642d03900c81c0c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 756606070 1250 756604820 756604829
    0x180604201c140a030210020a0909061401180305030405060c0c09250504050d020d0302030f0d02090a091a04020922091e120804030c020d12080601020a05031210120c 72
    0x2014004000620b8030007240408009800d5005012201ca02000140c020341c06101c2c3d0105014040c58040340303201c460312904016011a203140025204024000740c10040380d2024180c50089514003070000404c0401541c04a4205640700364803180031029490904103074010880d0002e0b451020001031900111000c0c0500811203007034000707260890790481e203512950081071340101c221241c007001410200d41d001a07450217441a0f0b814040440d014840c503510402d14462242d4010420700b0052914038003003001050402001c0002602c40910303003454458a0170141d1249602245000a076140c0824400300c92554400784011415151304010007014900010b6608285c140342c1c080c0c40c40d24200c400c0300d11301e401c0000c0c002c460000800c202d40038100240110208910074003218010b031260b010b4010000c0c400c0a10316000d1070340c2d0200130007892000f007a250455100d404800301003200801141c400b442400c2c140c2d0301c540e0f03c02a010b000080c2c00d9000302c214508010b941d0007400b07102c0003d4016207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 756607320 1250 756606070 756606083
    0x2091c030f0e040605151b030f0703090501051206041a04090515090105061507050309130e0115050607110303210108071a04170f10020703020105180604201c 69
    0x148510b0244070031a8814000c1c16084444465040c1c000072246025000a00398501102c0d16060b40041d0390382103801c4500d0350000a0740c007003050f03401c140d000814100074103404e01e0080c0c03c080e28600041d426030b402502090142d942c494030310520b00b0907c40c55408071003001e00140304034140c520300260b0392070341c0308410041901c5800c0407406000d0180502c5005034001008c01f8031011458020806550100b0000c540c144010401c0c42215110740042d82c3c80848400c0740000d4104c074450509003591203440880400440300403043c00269180303800d840d01e40e9000170b00c01c1d484050718000b2034950300c105814101d4071600940550726030f00882d500f8038180d55540b41950320300c8e580c031070341060a001c3c0d5189640d00b07103c060206004d500404000d8211142029046a0517510f1100b10130b030074103034614120a915a00064008145502402410307040a0740480d01800030065003092500ea51002c6c2001306820480c0e100380c108241c1d0030389510f54214006188540d04046400c80c000d042c66102070481d42d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 756608570 1250 756607320 756607337
    0x2115040608070e15031f060e010e0115020f06160314101e080a0201111f290310050601051c020a1704020a060f110303090c040605031f02091c030f 64
    0x1031900003003c040e4039040240043c042589039480c20580c8181c0c40420519061fa1007a001941d0021070484600900903035034070310499410301c200c03c0c1e0300700012507240080d50b000c0d10000303011550020701c550b440728203010a090350803c1220300714050580040000d49009450090151065488002d40119402c1100500030f8060020b00c00c0100351075442040406d42020141d0405940140001913802d44080c1c2602e000320700000d81c1031010940f03007440032055a901d010410340461700e41c80010f441c1d1040c56a040e5004400000203645400c00c01d00742807010780712404590281d00500c107a4101101c036584024000200d060039500079000100c5440000e0249800f4050b0402c964044a00841d0054100003444e42017000079075581c06528480340030031100c101065029030041c0040c40c0103040c0718029281c0e0f81c41c0300003008291841508a00c0c420341040d55415a03d0700c101c0495060040d4034580940c0703e14040000802c2907090402914100403d0544141010f40c03180112210340c51507100c0001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 756609820 1250 756608570 756608581
    0x80c210c0f0c030a0e010915080a02160302060924041202010216060c020d03060302010c0b04020f060c0c150301080a240204031109100b120a020f040e040b07052115040608070e 77
    0x10701f03007039510490400c00880d0141c0c100144c4134010b515485840000d02524200c0d400545a87c149924141500140c10000922104003024840c070200141043c40c0d0645c00c00400300308c076400da0400f500c02841418008220300310301c2d00070740584503070008aa04e040d41d81822410070710054054240100d0041c015802803005c040d00912030041501d4040e580c0509240389942c403038903a41c1d8080d20580c0e00039500420307100d40e940c40c03c0084c0803c0a01d070002d040b040c001d40040c485101320344111040c00610600c0103100c0c180f000100b104480f50054075482d45440c103590300e4601c00480100c003102c0d85000103808001e00042c0c400c20500700800781d485e00f80d542d884180c04146800c10b80610b200e540b801b0170038900604035107030070305420900c1003800600e01542c0a0b00c40c14990b00540c0718120380da00745000c01043c01318114400c0e9000c18542422840c200240e4442d022122030f4600695503450b0440106600c05507084443c0289007001e802000b5541c0c480141d565070b64010701c111007201e000b002c000340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 756611070 1250 756609820 756609827
    0x21906120c0201020a0503160306080709020c0f0a02150307110613030210060501121a09150a08010c0203031b0c010c03060f0506090916111c080c210c0f0c030a0e01 72
    0x740417404594501c3c1c02c40c0c5811842000304001181c0d980c08054030f5210228103540140a03060051680560042c2c2d5849030480d49820721030884285101900020079000160300e402c1c41d00403e01058050300d079901d40c0c0e15581910350904810341408140f107075008011009403282100e007101802a0200c4052511070000b138819580c140c0292800908803103001c44025000340c0045040d0842011045101001440131407015201120440000383d10a40025018100301c24000083d00d0220001e014010a40074040e5036844080c1039416800d03907100c4411203900b113800c180c0719040c143d18004d0080071000704004020340264050b4600194070b8400c005240d1074000200da00003100130700703445034030703540d404800006050140001062248150304800795180c20f00410301c001c00340d102d120100c04425800100800c5000346141314400040005d10705900103920f040b04580541c03a8500140da40704079040c10039019450ba4600740d450045181264100c0c04005840a0035040d515060b1403214080110f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 756612320 1250 756611070 756611077
    0x2090906040f080c0304090509010f1401140f0f040c02101a03060a020903010e0a03110d0e0315060f0d03021c080c1204020d0b07031e06060e0607021906120c020102 72
    0x80007070321030002e400009015400500110400b02081c0c0e41003d0380c98800c4019110100d4081c607040c0d640c0c81141c210f100300c62040000601801c599a8072a43c140300c40d0705054609030750524841e42c0303d0743c942d0078655200d00243e00c2200003d80284040b00946501039070b5a806025249262401d06080c00345001022141c03010701d00740200242520f8450703004150081d4040440706400d552201e4030740a0f224010040110b41078417998030075103016901c14000341006c50401d4164200410007003001c00c03a590000c0d2241e000c00f250207042c98180c654a002902d14101640c2040d00700d050a901c00b4107164011440400b041c03d0360014480d1103400e0031089486d81012550a41195401d12241e400e00da050b001c900d900a2001e001028440969141d00722100d2044401c00000380d11444d403c0191440e507020740031000850b80c2d00b404150304005016051010924005001e08004103100d4255070f100d07480c4880d0000070000340b031001d98507a10024020750f900c1120480e25818140807001310392051088 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 756613570 1250 756612320 756612323
    0x2030c03010b0d030e211605060a0504030602160b0907060905040b0303030711030d06090b010e0f0609100915050406021204030507211a060307081b06070206040b070503070209090604 80
    0x5510f030110780c1d02551105503016115400a503501c00020908100d844c0713460848071503000405d0010122052880214140d82105011f4401400f40c46840740c0c12400780c90990b079200a002d07841d016480039030f900c034460604c0064020407000e028402c40810110324242940d600f60382c0d036000d041c1c940c000c1c0002d0312412440b1a40682c810800260203d00c6903110300b03451010a0244e034688050742080d0010b695458204041c00c0e036a8599005039503800148040c882c1200380c070b06046a2002d540002d00038001c14640f14042c0340700144181c2014419840c400252100109150980d01e802000a0158019024907009031095266640945003400160b40449600c10300816049040222000c07948400c8100c07050421401e5012400080d1b003403c0c21880d00700965445407003440e203c8109841c016007640310814036000404412a0440005048411604c059071220f07519246480411040c0c13140782c1c404446880041822020410080f0043c10524001c5605044580b10740f07804035240c1006440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 756614820 1250 756613570 756613579
    0x60714012c07140904030207080105190c080603150601090b07120e0a14150c240a0e060f0417030a1e33050411030a0e0c01020d0e0a090c050702030c03010b 68
    0x2003c03c014a400d100440e4400d00c40d1054030f020550300d064072425541c095845c242d031a5100909020001c0061148a01c0c00b0300714903000406d0309003100840c2d21202c51007600c0303e40c1e4181e075002403156401010110300500e8a940c105030359003203c1c1004d14100c1590303445100060a045040781e8549001081c0c2e00544421403100e411804944040141507071100c0100580404140314440200c5401e00080d4100307000302c1c2501a22210101844242140051862800701d103040c0905c00141d00024806134880c03015201440b01e42c4076400d0140988420032104002c2d88000010041a8140b50300b09100400c8001c000070484464400542c054a10b0207030018150b00f0800c500d9000c1036445400c40c600d00884031001001c25450700042420740d20044400b1030344d04e900000b4050142e0552213250402c10394840a80b8040414400007921429506015420071110380902ca081d580c412081c40000d025a210411001825110152250300900001c1c2e100703004202c03086040c1d041c10702410031074450042c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 756616070 1250 756614820 756614849
    0x30a090e010e0402060415020a0f060515060c0705010810080d1d010507020108040b041106030a0b01121407050307110616120e06010b1e0430020f060714012c07 70
    0x5110800c1c01c00d06100d1800318882c00c4807590202b840301070009080c070f01400010800c1d00d08480d0101c9100440d654181c0507400c10000801ca10502040780001d444007480c00000b992613440000012000d103400c02c8805000d584582d644103500290030580c581c90701a00300c880d1801c1000151010302500c40080d020481c0799001a0001d846031006560081c4140440d89440d41940d000c20060340040b2100d45540d07075600900c002075030300b1600401c50080c41d440107205140c90085680343e010710213403a8100f40b020100203d28001d01a56040c160f6410600c2110000c1c600001d8001d000b01d4412124004114102c80a14070303c0310034003e520050308050000c2240e40d04e0103da801481e03001c15044c030700d4106031841c0d5500c10305035a801080148801400d4030304500302c402031103000b001d40152509041001a60250068032081d602900c06d4800b00c0d191919001c80d420301c14120652940310131103c0d441e08201c9910040805109407100d0182070740381c044402000c004a940e020300d8043c600c02d891684 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 756617320 1250 756616070 756616079
    0x91e1506040e0a0309080c0607050706030506060705012301080f210c030c1605031603033507021c1d06040510110115030f0221030a090e010e04020604 66
    0x1029964210340050300014002d00c81e4070b22030b070415801000c01c40010760714070070402900d10100300001c3c00410494a4910f485143d9980599a00030f901c100c03c2456240c50004295940e00e1058a1640350010024440003100d0812011081c0c8e0144200e8a02c070001800803844d08030000e0803a42d0b2003e00c00003441520020300c64600149203001240d0340b8000c0070801c644410300207001402803c4d10010040c2000e0795031980c0b10380d560307100b500910700941c0080c202d500354910f051001c030122500340c246100c090160103000100c0e0b0f18076900741e803031115015889003510581ca501091082040343c1c2030300c0000c3c12220440100b400c0f407110000018211001140350780284d0800052560402030299140030740d900085181e0036500ca03c45004600fa017044020298400c2c02201000104114451002410b42e0b4800382e00008030312002c2c5c00343c2d41d8441080b030b50240c0d059407440c00c2e2040c1001c4a8440703a40602c02000000d1354000c03c0d810355406000001c51000300440c0b075001e9507001340300f80e0826041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 756618570 1250 756617320 756617353
    0x3070905040308041106040b070b09011109060313021306180506040b0312030a06091d0d0504181805030f2508032d010b09040c0c0c05220507020105091e 67
    0x102200c0f59106c0300402001070000d8400d0010070510340305420403046850301c1600e0b1821145400810f018040c000c0142c1c003002e80c1c45104496001c01c1c0a5103082c010034260010403901800401083c104502c0d0260114101e00c3c018103000303166a2a040501c8190340310020300c41034610074444280c242d40401207200030f215042010303551000c50300b480061380b2503072113403010203a421903015418180032a18460548800078011345441da50581401c038580b916100f4000880412240e5400712141d0f200d1851420040c0c0c0c203128050950010202e0351030381c0c90000840c00d40e9000c010114403800460200d0750304182e1810b82c00d2402c6801c2002c0506656810326800314045a03402090480c0151161818603402d0309604540600000741529446003061001c1c042240c1c00d403100302c0c050101c101c01319070000d407038804e032102a02d60030350300741c070b0461810045114002c00d4000c3c01403805d41418104420541e05520040c41540024100c485080785140c110380c05122001560b070b0300d0342001d4429080c0f00314 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 756619820 1250 756618570 756618593
    0x5040207050a021306080f03130e0601020c0a030b07180b030703090309030f0507030b180c1c1a0a05060a060203030a0506120f163503160602030103020307090504030804 74
    0x5103054442c0c99045034001114402a5040f0b51390041e84c1d01c40911081d90200a0032080c048020021480d14900720790807a40c1c26034610595040e80082400642242d209000c0001c03415406010074200540b039207065401c03480100c0310341c0005103010000c00140c1c60b0b03070a107032001c03100115540341c1b56440d00d0030110050300b88481c0035402d10102050000018103459088120103004030082d000b070b642145060303284c3e4480070744001048446031505841ea624046140d1051240480740c0c10700201c042c00900316080c040f05400307400040a040001101c4104683c1d5a100303049012081000f56107420801c40c100383c0341c0c0610001a4002d000285090103d9030009402490040040505072010600146409204e11000c00103801c2051074a000c80c2c4000f45840150440d405004408442d54103c0500015a080c2555811140700250b1020490900460308020081c3c005403038000c4460030944041d500a02c4102d010744914980003610794094485c1d17030702032680350f0f0f512a0b441c1ca940c1c60300b2030b1740344 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 756621070 1250 756619820 756619823
    0x209011202040905030319150e1f0b0c030403060f051003060504150c030209010801050f060a03091a10060807030c050405130e030a09140d03170a270b070e090105040207 74
    0x60350b03a0f00e24070215100f04091407080901e500e22001e622031082c10711081e51058000003c001411301d005002c0c1088480d00568410043d403035445000c001000b600460005030307809000c204400203103121444001200800c262409a0300505c02c800a41d40c0300d8080350402c640e081d8865520100900c00a01290850344d00180201d558521800051001c40100d841c0e006181001c01d50028902c40d9030358001c1c0c21580180400c840264400d500303500410818401c0c8407048040541c0c84207a81d080086030a8102c200001c0080b204c1424034142d2105410030400c1d0040e03d01003000750f0009440c0710b11a011300d64024500c1d43d152421300f440c00091000f101c034682c10022146481c1c12589c0c0e81039104102134510440f842d030350141c00c10b240c07049a450100000c44004c1c00781c0c88646881c00031a400a03210030f82d005205200e00d603a07a03110100c00c4000c04050b03450344500341d01c0c032021400d0401d84012044000b4011100c020743c50715108000e942d0322001c0000b081d0001e08440041106160a81c080e25096 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 756622320 1250 756621070 756621079
    0x41505040f06030506090a0507080c07031e0206090f010621060b040504081903020f2505100f0e011a0103020c0c0402030c1206060c0c0427060c18030209011202 70
    0x2035141c0119090428064008000203640c500400c5040e01c1c040307440a0308141c40d000100700034145480000e200d0b2000030529590b1322000905201003504c601340200f280405101016140d045a00300291180c0065441c968180716070001541c004c503044c40760344200c179000c003820180c40c80503918558691403403003000d07510310380c0d19405484191a5030103064401d500c240e581356030321280400c039190280301e80b030603100406105114504032022003800b1542c1c55480007280c2401c0200345041c00b40482103d25000340315000d01412629507641c25042100103100c200b8051103c000c864410600701d981d98806d8961a841861441d0100d5000340e0007003504a0103c41a940141c0055000c107090f6402139075101d50388031000030320801d8000b111041c0340e0059001c90307946141c038a0304414181d4641e503601005105940e80e0000412203c290300d010102690403042032854104681041070003042c00b100702e0004200c9517203008181001c42d039503100540754020060340c900d034200301510300f61307110000302241c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 756623570 1250 756622320 756622327
    0x1e0a032d02070501030e030a0e040e0a0203030a0509040612030e0112062303010f02031b1612120506060301060903081e040308030115031e05070c08030a0605010e03070b041505 77
    0xc95098000c5040c006990020080285004001000c4544002403185144c0082c400c0c40d00403584000c001400a01c120740105814421102700e50901c2c0852000a515100000e800d66000e6040400790007810811181007100304d946181c0f1490718070191000500041091048003c00d600800f0146181c801011000802946aa00034600e080d082e41d4039040140c104401d103ca2460240100480b030081040250705504103103401402039120f42801d84102e807030106503200001542805e040000360401101d80e0216042000074110407454940c00b09181c0c00d04000504c1e50503c00c1c201c9040381d9060f6581c40c1118915140c409282d04812900880c1d0864180707400801d08580c0f000c1c20195016600e87ca959515044ca01d1a41c080107900318824103062050034149403110314000201c81e003106501050b2680e84140441300003a10071401002c0000200c140f10070300041c0d501c103100303550081e21001d240d040c00305c0c10940d80e059940b18042600004000510001041c01290b100b6142d0604100f410f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 756624820 1250 756623570 756623627
    0x6041428030215010b070c09020f09060c010e0102040b030415091e172a0703080a1b020a080f07050603090d030b010207030c0612180203070608150d0b091e0a03 70
    0x3c06180a90000c00022004503040081c01299003581d0010400e00804502e00105d620403144240030f0451554030628001c500c01001000039040300e000c03c94004001c5547e29122000c1d100b0782c1d0016141640d031404d800001201803030003482401d08070350300404060304005881c401e40c00414401e4400321450300c80508030500d0754500c50090000750176400390b081d050324900c07a0266581400f003400e1000550080000b003007c24016000c41d00c80c03204605d410b070410f41d42d000c440b006180c0d000000035004400c5200024807400c0210b004c44440b40c90304150344242c1e558404210150200381c6030342205801000c0c0d420313170450096110070f14044041c0151498a581c80e150b0100d00202a882440030407031042023400c03411803d1042d44003c3c009070b8071240ca00c0f40d00741c002c82e42e600109d005450070b0140320401720340421481c2d2603030b401e0744200070107410b03c55425241100401e02d06450241c0540b0404402c00107440350003025a019010100040444c41c080b0740301144c610960001c58140301078603e00f18030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 756626070 1250 756624820 756624853
    0x60c0d0609050a050601080f070c03050a0e220f060311060a0903050d02030901030c0504030b04150b03010f0e070f03150b0607080d200a0f08041b0305060414280302 72
    0x42c8503090f1a00c1c00101481c0c4440003405051000703280c6c84034941c1c41c904024a403034209081c800c0b5540c01d07250403521020312920650f540400046a560b01a84000e0412540c507020240710b01a8611614103010140d6450400400e880309400300404118001e480d141c190b0410301d01400c40d420541ca0038a1000f81e0b60344440d4100703400d128041c00142c00005507203a04c0e580602400c07003483d1961a25030303c1c16186848240341d103500504020b03e1810300300b9007604c5c01d00d20358100c0c1d5140300c00200200662180c1c914142c1c02441c001003074004601400314000f41e144900c80581044a070020000e031090b4680b40e0084000f4428080565030001040c0000d0000c20302000c0502030b071410801c070019401c1040300d509108400c21080030f820704002040100c00039944030ba12124804414105400144c46611301030650a0b62120f515020f1350345075000005100e40090014041d9014417400b1407a1186400551380b50743c8290b000210b203140c0380d0010300c00c0c1440b503440800740b94060301c10344503016035009046 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 756627320 1250 756626070 756626081
    0xa0204020f03041707020105180a0b190315060e060f070c09052401120b030c030a060b13200307170a23100308070206130618120203060c0d0609 63
    0x41da16032002008000c10041c4c0c100c200f0b010b054072001c001d0304007600c1d940003c0941c454070701d4031802207108912003081a1a0032641002a005840c09151205052440d00d011915503083d000c00107410442c040c2030846090040c0010b035003d55460148150055003032004c298400f0680e8007603070b0760401020020400d005095070203042e1103075010903d030801803c044208601c1109141208650b00341e80441030303800041081c0c6624204170007080b44070890b0002414030950301002074141c002ca02f510b0081110320f5000d9007001004580100c0310999805000044400712002001030041c60101c810010352958003540d400946072070402103212012010000100c4150f84900084d92180130030302810080e4100d4403003034041d15030410f41e107141c051903801030710344248006404d800e000200c100179911102e04642d4103006990442c203035541e4905000b0540c0703284070904c00011448103808a21540c0a20501900c00d07002801420030b501c80f0905041c0350741c0041e020904441d0f40b0b050020b0b808d01c01d4002e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 756628570 1250 756627320 756627337
    0x106051b011a0a090b0d02120717010b010f050a02070605130504020c0105010e060621070507020d0c050312040311041a0a06030f050912031506040f0e0402032802060702030a020402 79
    0x1068101c0c102c0c4020302c60914210f40000201c1e50501c99a603985498404210f005150115130b100f0a510808a0803810f2803010f411a010540526200214260054010b906080700aa0720060725001c00c15040300c2074020304403a07a006800c0f030001006814410342c041c00103080e001920360801030380d400c0010102e900200380c0051503511040101311b03010800c084c06034481801c0d20020b14041c1c070002c0c6d2504651003039142484d030090b14008110402e2180c4241e401295002e452402e032007075a4200710203959400e20510f07100e407007100d0084440c44540802c4d20b0440742c2c000f0f0b8405203410030304e04000180801c0d0054500141e601c40d4482c0c010f82d1078017070000c02014240c07000528905040c484009581c0c0061500d6a2a40b06140e00c00c11148102c080b02c0c0d02c0040440740e4003d00003000c0000c1c410780b007142d006114010f030402010075030441d4030320304600603482102160f0b44c442c1c0c0111a950891110018202d0101004082d0405801c000c001030000d20b1000b4166002e8400d50f81c001412130b080f0405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 756629820 1250 756628570 756628601
    0x418060504060c020111040b161e121812143004050109030b0a0b0904060e0d0c030e0d0f17070213060b030a1a030d03050703180b0106051b01 62
    0x1404280b10461151102150051000740807486070090200080e00c5640702d03006038600c00060805601a00d00405507a040e804a240c0b0b11000f401c0d4900803101078a0030041c0c40d05a2100380c3d26403007502521154000b01c80168016122a2610b00561030f0a800301c8010ba07100b80451905915503d401e00c010529011006100c0c844034203d07103010411854440c071448403a000410040c4810303a0010000d0040b40e0b800a9040781e81e0b41c1c0c4c288244050640703800f94540100d1804280020014142c2100384030500e09001c42e8028200142c2c00c4400302c10187d809000f050140d0722034a01418512500c0c08424002c1000291030103403961014100a544910142030501c040380c0c0700114a030401da01c20f10f001c80da0005201003030070204c1654184c40050840f900c0710356184030101e4000d080e00d013003c1044ac002015a000c100c40d62001030042c0000701c50800007c0d21700910845401c02070349940d4285078010a192907603030f0900b002565950304c0410f4824040a840b44845800e040c240a02c0000c1c001548 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 756631070 1250 756629820 756629831
    0x302210a0b01050702090103060b0a03080a0504050f06130303080c13030b16020a1e031e12060503070320060c070f03020103052224090305071a0c070f02041806 70
    0x4201401c58454000c1d00c2d04000007045424090b940b0002483c0c1907a1300030380e0000700c3c2620180003861509540c0c0c00244165070103d4180c40180e0040302510813a04145c2c1e40c0e90203e43c21034100700c0c03d0701c242da109400040d0a60301c10310110744a0700c242903000c04e50b15a203130702e00308120403841c03e00d046540c002c0701c0803880301007001440ca504140c41c01003e038840c002000f10b8440303036881d19140c60004e1410401410b0600e001c9082c035200d0445980314954003071080c00c03840340900000b013a1141e0500310001850801074001080e080014181044030317041001010303032141480c031005202d0004501503038041e406100c200a100030601150f0018546200110084c500e580700150650700010135021030340f0754010745001c1a126040c04c00510a07406241d88261708241003000c03032080d00e500c182c101c082d031602091304209500a802019818010755918520340c0c007410840d98242c0c800c64204035104400d1284070300141c004462840036501c000c00c089202d000c13090003416070440d500400d03035086440c0c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 756632320 1250 756631070 756631081
    0x708030103050d4107030206060f12030708130503070f0e0c04030b0103140106090e0f16140111010902031c030b420703020102040630020307030221 65
    0x402030301044408a003130502007207a02c030800b9110070714418160f460407a0700a54031070300061604000341011030240802d0f41c4529481c10002c1d602e5808882d114010a45510f681800d480e18640c00003202100304011481c10140d03030340d00a0182c21001040c00c480284d100080341e81d0f41c05105100241c090b501c17a40f0380491902000101ca0f80c000340a1240390f8500304820300100303140100240c15240c011044100021514043c540144680c0d440401079500e080d040081140020600d200614251821946402089009505001901c0c4600f803000d00051358140300079409010028001802100001844a0240c010a0500380300d1f6010102808030410000c00c04c60700351040051400050b240c0004401c191040d0086483c08200c952a40c42141c04190380d50a41c200c50807200d440d00301640917203825443c0341c064007079082030003402c021a0903141000004213400e044044040402d000c42041200404e03004402540007801620405400700b10b1000301c1c001c02d0407aa003002d94000100c0c10a0302e4036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 756633570 1250 756632320 756632323
    0xa0c0303050a0215060603060f060d0c0914010201060f090b130204080307030914031e010b041e050c0c030708071416290909090a140d0e04090305070609020f06070803010305 76
    0x100c903070558003130112800b44901c0381c80d5003040c0c960004084c4c50030440c0110101c00a12180038980d00c0d18134a81c100f4401c058243d81c0050a4412500590781400503204540c00580c00d036291400389030a503091004080090301220f4006c0c2c0340d05580a0030124403141c0010144041c2c1e0300c20b4111a4007540000754420400d54000300100040410102c0a501941800d000949803280b403404c1e8100700b22001070030030100c1d10a40c81095200b40003881041400b4007614155488145c4015240c0184d00c0c00d07001445401d00c0004880c1014210005107140c00107681d10004c45800406040d111010308456100d2074101c00c209480c000c800c0c52003259005464094010604102080c40e852014001d500b0129050300d10b10940301d1883d411a000d131559907a11403041c0c41c0c00910000500720340d42e44510b440c0c035104040381503054400907030f503948442d102c628284400e4a40d140d030010005a01044000f02284071607105004841c0300800710b480000c1c4c11800a44580c01c0f0450503500100000010420080b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 756634820 1250 756633570 756633583
    0xc010c08010f081f0e15160503040507060c033b120d0c020628030e061003060519051915060c082b02090f030a050d0e01020a0c0303050a02 61
    0xa02c2c94690801d41000b00d0140c90306101104040c03000302c1c0004507420f81510b0b030400e0301c1102604007103815010542d05c200c040e0003c10703aa81001c0044503928802220702c24411640301d00c0e007040081450f00d02d07045048502503079501040c2d041045070044200301486082d0003a00c0340c040340d410440c862404080940e00b071144445175502c1075440c1c0c20b46d109104004541d40300b5411071800e140311644000d001203003103880307078044034151400c8013601321b00b40702203070483c00403603c0c06654100b00785c0c092030b2105d6546041c00d0300d0141041c0c444050800003d4034a40000ea480907603d02181e00d10700100741100e0954070141e40da51100c22002d0340d01205482180b240707600c4140c544a0500c05941342900291030034012403800b5098a5002511100781c034100340034007084903c05000c18075003060340400134001f0741121041c244103250341041c180c910316000400d2048260000c001d0507042400c000103403005101d9405007815405035040c040040b540c03022a000041d13000e600c1d1a640d82c85003240003410101c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 756636070 1250 756634820 756634829
    0x90c010801030c0504020d06090c08190e0c040c0507170a1107050d030c0807150209040b04050f060f040e120705060c0a0912020a090203180c030111071b0b0c010c0801 73
    0x4121001000450042819001101c034145c0d001691416280b5281018294507080041010f0034219100d04450f03000416030b114808222601d03490315030704000b90099550000c1045543c0d844078031901d007645800c0d440100351201e5400c1031071410603d984c0e2480d240702d0b004030b0b24410410104400858503040b0450302c015400c0303074020304517003401d00c0f0010390070f4880c00c2c0014040000303040d4039001300b102d1a030442d000103401000508500348585401d00103503200c116044e000e00d00705070321200181814042e00380520070b44c2c1740317110321503079800c06015120346030404c8207620580311000c0540d0307000706000e0f92000603040c080c0e15030340340a942803042c0f500c1009081569400f404109055a440d440900002921a0440d01700c0000f83c882c000150060004c0d0803501c0d1003480003003440012101482902c000f02034030310503507485061f103000309402c03181d60341c02c01440b10000304290400075540c1c00a2103086030000120b910010f03200ca040c080180c000212020460b03554908480c8a181c02010701401007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 756637320 1250 756636070 756636077
    0x904021c090203161211190b180406030222110708220303051b01023007030b0a1e09020c4b0c04020f040504140c04050904031202030f090c01 62
    0x1d5145c00789880c511600320740e0140806800340104d0110f60344042c00c807040c00310400c0b24074041545890b1080d0040d800780030201001c03200024020f40c942043c0c01560700303c98004240d010341031760a00311107400400c04001d0b2883c5907500d00c0350840404504000d860080d0154040702c3d05c4081106a403c6250750b10b00740e03015840d444100400011341c1c4841101d452004560724051800001c80c3e031540a40980215040c64082c0301480c006c450300140c3c2c1240c1082d00d10b140080703680d155071400fa4110380e442441c813a001166100300340064440300610903983d0940d20707460200c260350341c09248120f8001e6581d0f103d507500a446034903402c15a214645d00d1002000e441654000e4000382d02601440504024811400c0400c02800b4140d00611a444044101420540d0b07a80900031241042e648070740522807240b880c00b204007603081c07040070038944102c2412404a04d4030f814581086202d5000800450400c0009814010450050b001950003082030103034001050405010044c181081d850099041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 756638570 1250 756637320 756637363
    0x102030105030307230a35030a200301240f08070f030b1009080706020601051c080f07050c01030b0f010f0807020a0209190605031209060904021c090203 67
    0x1940d0040f04544015a10800082c250009100a105482c071308000412007801046441000e000b0300300c50040e01c200c10307902202d40b407003209105031070314820001002d18a102c0a05c00212003801c150f02a0400c6541c3e1014202d2419000e0169511036000742c2040b07a81c201c1c144500b4141044e10810340c10401001d041c03603e02ca02c0c040500400c961002440c0c0c504001c6070382c0c1e071030108500a921a0b03100d504041c00401c0200211407010300100321070b1003540220b10842e030700011810720100340745040e100014400a04980040c003094004075843c0320554003098108900c614041040006040240c41a00500b072040010300026046a812180b101d0141440c209440c0f4035a83c480c00203084220070f400c0c02e40d529116041e0480c070b0403a4018000390410200401c0c0310100304411440e520345030240390b00303010850b1980d00349030b141d00c001d04e842c031512601440340c0048d0b0303d0244c0151000c940003420040c01c1c801003001c040e40c000004103c0400c515920b4842c4000d43c02c09000ca04041800e4007080c03041d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 756639820 1250 756638570 756638579
    0x414100c030c1b0803030a1a010e09040803040309150c02010f081e09011d0a0c0f050d0602090d0f0b0714180d050a0203250504050f06102c0901050301020301 69
    0x240d2074441c4000c00180414070801480c1c1c00442c2503c2c0600406800c4076128a0022101002040301954602d4180d003100340b1085d480d8410044600104405404c1240c01d4403207a0720030440381c0000d00105c0038400301d0003011605000702d800c0307005611140d40c2c401c540d000c9603000141004000e500c48104000d09074081100350b8031180307030083d006150850300402e20394445942c82d00400b09040300b24155841e0070326506030842e0004280072000c0c0616505c0b202c00365900188041601244201c681240c00c070804500812410350141032071420142204001e140300b85d807041a00651041c1c2215545040800e105040c3d41c400344281002e401c0300e08491800c076030514541f04a00603552514428107020700314400300402805000300e080c0e40079084902c0b00d030860600c3d0340e0120450030784a861104507400003a071407404d4029540541d050061814091302d07000180610429070810750340c00c0c8003003034580f00210700350f01d0310300c180300d41089020b0009c95a0b8901008440541a031103c5c2c840c2c0e006200501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 756641070 1250 756639820 756639827
    0x32c24070212071e12140f07061d03030304050d0f02071a0327030d15030c080c0915092d070e0a1e2603030702060a05060d1221020414100c03 62
    0x945d10b4004024510100d00005082c1c509108180310f8070541c02908000110140c00540440506040020004080140e08103140c1c0c0c80c00304840c090b02c9a03014490245020340100003420030903d1a01c103840401e81c5641010081420f002c3c819915510004108a4110408a5050750540c007408041140f00a07458442740c0d40e009401c409807680382ea495040103594070f00c0341d5a400451b440342d0450100c41d5034810240d160071480302c40358020f00c4d4060008800c0441d081c12a000100010054040c58590202c0380c240305442c0300640c00104e12545c441c09201d080654500d21408040c0d648031000718500041c05030802d0b0740e5000351003102d03019010700b109401409844041d10210b4020702d001200c040c01d843c0782c40c58409869030b8580400001e02c03002d60b5000c94414400d203010601404180c440005002040e800208050100307070341b04c1600900f0f94800c20184c1c03101111091841203180302c2c0c4400200300d920992003102c1000c82451012140e007000c109130403145911b0300389102002000d88000c1d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 756642320 1250 756641070 756641099
    0x50601020d0f0207050306101a0f0712030f05040c03061b0203040b0307020304180e0618150411100c0507090c050a03020d18032c24070212071e 63
    0x1c00038408100040c103407052080000500800e401021070300c00b400c0c00c3d50362517400344d207600880c110b0140200d030a2803510780c032204454009a51510041c40e1007103945a03c50001d031458043e0b0101510b5104140725400c02d40500c0b0300030f501400101012501c0c504e000000c07580302c2401d01590f03e298404600304603070084203560444540e0980159640c3c3e405c0300481c10f40c8240d810002c20756942c00c00c0400554003960015203080784180032115140c85c0c011070201c015100d00081070035640000d18a0303051000c3c0446540c5c00510030504034001071214800642c01c244510345040024034107801c0c0307105102007000054000e10a40f8000c021418510703400404a04c47d9184c2d400038103070006030f040c0c180d8600381d01210721101082d405082c404803900d0001c00402812200818109008030a402c01445413000c04c81480d400810000010070045001c41c3e0b25540142c500300c0080d01800207401580341c01c0145090328650102a1171001d0074804054005290960400c0c0407a40500d001c1c8603900e20324140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 756643570 1250 756642320 756642343
    0x611030a0e041b02030310060302041a1e0c0d02010b0d0b04240603030e01021015180617071d130209040203011e0b0a0e0603070902130906080d08060405060102 70
    0x222488903141c000706001d40000240e03e1494082c0700d51040b19640d020010f1030080c1c400c500c0c904156070340da0f50202d003640910300500d00c410750100004000d61032204000c000034110511082880510629901c5498000d00d240d080c1c1d80e00181c071084c40c084c0d4203100b03c5150b80802c079404108009552a01c1d8a4080001d0005010820340500554400c0740c0d1510200c017804001c0c4140a465160303d001814100000c03802400b600c15122140000304050003100d04d40340d1416460003000b03182140310400c40c441645a8007040e96584800700746602546414441c0502900091084034070307180504ac103203134400051103120340c0080c042c040481c00b1003098661054045510350943c1d2a1400042d0040c0308640c4000d0f0070020449401503030070346907004007440010449000a80c07075661141c188961000b00c42155144d00030060130300600f0003d0340075090b40d0320040b9038510f03560f803200c1c000e408071000c40e041200c0542c03100d2502413416078481e00c41688400c0c1a40d0a12440c00d140001170b5480400346e64 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 756644820 1250 756643570 756643577
    0x608061905180307030e04270b100302031002030f0609040803060409210c050613051f090212010609051311040e2a18010e130f020402030403080f010611030a 69
    0x30a40b1039154481c440c11a4140400340c0f079076600b4500c0c000e4080903400007510b0040c0c1c10413000d00e4960f011007e005038486211070f5580700e55000c0b981d618001c010014112514000a2030011015817800c00103601b1401601c0b10059407410007a0752907030075240c0103004034401c41801c5c01300400104613006480d0848400d480c08112003249290480c1e0b20f003d8003680b00200e44441040b440a168800da031030100c00d01600540e00251956803c080c0900d114150150190380f1034220301100da00001c401c000541642400041e00030300540c0054002811000361b41e90a80d120342050001344154441d240e0000100d80981001c00e201c0c2d544c50012031a03003c100c5108950319103152003032500c1070051900460840c00450444460401c41c2000401d41003070075401081c14030702020b5441e1010f113107641602d0101481d26000ea4920052444980c10424101e4503000b4207540c400c0140ca89001840c041e42c805d80310303d402840c207030300305011659050340201e0030088014918800244e0100883e0b40381049440c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 756646070 1250 756644820 756644831
    0xe010507050a052b09030305090c010516020f030616020105060402040f0b03040c03020901090207031218080d09081215150f0d020f0d09021305010f05040507030b100504050406080619 80
    0x319a110481c507101c120113981c0d9061038a4003d003002c3d40600010341c4a0b40341003001e6101c050403142e60300102001a40420002c0180c45075620486c00702004440c8000c00e9400d40c1001e40c40031070704115040d610065011034211152003900e03020300416911400550f011800c0ca841c001a01d1064501403081c540c090800002140c144a018041100950f030043c1095403d940d40d4402000250f0210200b60001000c0b45503000706500c0c0c5009030300d00c00810000110300c108090702c1d9041254854510000403039514090140003404020103403044c0001004402c01a00d46102c2d0035000b00c090b4601c403845141405981141000d514041c0c1d20300b4084068142e4403851b0104003031000348a5240f044401c82808504000940740c43d0b0080301440c0d10940d159031035800b468000c90b055a600b03010346054000c41c01030610450610380d0250364080c0040c600462844d0702035001c1968080e040c001c41c800203c000909002c2030800b4025140281581e00040902d4904422050302030382c007100c070212a658484 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 756647320 1250 756646070 756646087
    0xd0f0c03030203070c0f0309180204051e030f0a03020606090c03040c140102070801140601090e0f1b0702041b030e2b020c09130b0609161107080a0b04060e010507050a05 74
    0x409540c40712950081c2c5040200401f03080150143d01984201504411108900c1868034800c0c000d503802c0300c0001d0403081c03010a03007012000c0064954082a40c0600c2642d040486c804c6041104000b200d0098015250030b00b000006e10142e12001448605031300c2c000c106020028000c250302000312800100c3c801d6594000000407414180c29034400041c43d030802d101065802c00704400789000e440241c8501141d070f41d07102d0a00760881401c4400d031110000c0d0030006944800c1e41d45800b000909140c01c501e150080c203500107400c9618080048019181d00320f010f401858143c0720b5280d2011000008007841c00ca0079010042c030300403203035403042c041c1c0c1c0c54400c0e01c40f064020420a192003600401210091610034406040b0040c246402e4071881c040342d0114070385092000e0340341c1c050004100720740d071040c400030004d6a0b074000c01c0019804a100d8964000f90040041c46640c9a203032080155402c5410b02d0304201c070551305410083c250a0f4500800d12554071f8108040303643c40c0240d8107049441d490344 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 756648570 1250 756647320 756647327
    0x415050a08010e0708070501020d030f1104030b040614130f050f010240170c09150103150506041206110706020a081003080912010623030d0f0c0303020307 68
    0x45900640e0010010500420601c40c1904541107440b050001c0303520035959481c160741d40d64401d00c16035001d83c00404014002c24402d0300808503c034819440403c1c22850f01041445540c024bd00554001601d90280802c0000354098041c0c24005e6842e41c00d05070810454828101c0c4202900400030b010301c10b00d000400c241071005030001d0701d080d0000c64480120140c03000304441c4040951402c1060401d281c0c58148652104100390010381040c00c038450300f4000c40c0c00b0b481e030f02c0b05008007180c0f1680e00d0810a5541d40000d0303d126000c425450092854020009004c3c1e81c480083c801250408900901464903030605640444200000a4010300300900742103000b450100c0d10b0042001c0d00240c44800e103c842d400400404640d039032800c40954402d0584015010b603404010880c1c0b10400c800300541ca8068115000c10480f0000044c12941d5001b000f10540b00b42150001100300070000400c04d80703414054182204124102000c4030f10800c4401880f0040200004080c1030b03011000c0f9941520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 756649820 1250 756648570 756648611
    0xa0507060906240801020403080405040216060c02160902030609040605070507050d0906110f060105011211030a060519060f1d19030b09030901051926090105011a0904 73
    0x100700b4801c209055076064402c0000301046154106030480c00380000d0920814800c850803260040415800c06040c2010400a9841803002c031050142151915000c984180300c3d4845003400c81c1c000304201403175150380a0400c00300394044011184107004102d02911001d41481c0c4c8503601100005107a031b60301c902500d203802001400743c00f922440080d01b10702508000e460007030301c40355151030040180c00a290755031070386082c2c1c408005400c0706004110130b502940450318000540400401c0d4114045825509500104c0321140c0158a40004119038101103182100e00004c0402000142d401d00c00080e000c1d05086e0780341d13010000100c81420200d582c0900303001001c0401410a03034400c2c940002640144024003003510007140b03031004244c0c4103034000f00719a4500b806840d10780c20842031200e07230150303145062140b006200c40160b114607503003903100500c0c6065400348134244050030310802035421214141c210180203081a51301c42c4500c02000b0540c3c14a84003190041020102c610b80ca41c0c1608 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 756651070 1250 756649820 756649823
    0x30606070812090c0a05030a02191a0d060e04050703030c1506060503070f030b0a12051006080f06060603190c170c0d1107020a23030a030816030605060a05070609 71
    0x8001040036825071941c00b100a00800200703048a00d42c0e0100740070030560340507610405515500540c3c9220050410400700003005012a811202c46d0340e4030b001c40e107142c8410420404001d03c2c0050040110034540c0300c0d2101a1641224110080c68980c0c1c1c0e040d0380300294040a814450980300c00740401c580c02d040f0303401480110b08103000d030341d5550364081d1a43e00190350f03a10108030040c002d001d078607200b44a01445000c0041000008510b05069002010340740d61b000d95460103045048140c12009024000080990400404d0822004c010f024102480541201e1003001d0800c10310908220700d00e4800c08400302d55070b0025800c03420b8601503c0a840000030003030242e0b0f1110030007504002d140c02400c0041c504040c203001001075243d0140300707885107142c002d502058406d824400000c058186e049140410038803000028203400009280402803030307003100001c40410400121510701036401c1c01d07500c00d41c1030611070301c0d0070100024a2030083d42130840401c540407a00702d040c002c56070231040c07009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 756652320 1250 756651070 756651083
    0x1508014e080a08060301110a0513050d0f0b0c04260f010515030c18160207030f060603060612050a0204020901170a0209100512011418070201061404150b03060607 71
    0x403005190644194116800c0d89001c948a80001801e600701801840c5c0303a0140341c0c0e00c517444d082402c0c400780c031507030801442d1242071035440b0000b02c1c803900d0302941544d100780201c0c45203080d042203282248001f4402401c41c10140350a000400c50034842c4030b10b070f69602000a9003800c1003507400d41641c6c139011210b075484c0a998245030034411130100002d100003803101c06500b543d030003004240605c0f890b99580d2101c07000e81000c02002420704c400107a20b0500700015881a5140070b0b035213854050062032000b00070303a030030303a5200b8081080000e244161320041000e14030090b020003442d26941c4c0c4440c1c41c004064022500014409402c1e880f41c07120650301c0131004d200e031581d0b01f0500d8902c07000b500f202d00c00d14040c011440b00701840c1070261090b1007c0480351002d9100030780c28481484003880382414415040101112803040020400b18080d200364220b500010f8054039100c0034520600c1c1b0220090300a5140140481d00d000e008800c0c1e6050b00d01c2c188010b03580391074600109003203104152025010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 756653570 1250 756652320 756652469
    0x10c03170f0411010509061818090105100909051e01060f0602030c06090102071e26030703060614070b090c0a030c03030201060929030115150801 64
    0x507115201c0705070069000e01d0010038091901d030015601e034801c1c111141c4e07001800381f009202032010080a00490140606a804021340c085022450f00d44261042302c66a5100d0042100b280c01c002c210b00010035040c1420304c00b04500b921110b0b121000b00c1040c20102a103022808030742d00f0250440401003440c440004041540c03040004c4d1240c00c40c180c107c406000b10400f007085068140280c0c1c0e051a001011078018561131500e070101c035500410100d9801010310401c0d0201218529605406072518111950328074001d00700604641307443c0c0180c400d200c002d111703840c031281d0600184ca038032550003001100141c47c0c620955160041031f60b0002d40c02000c920010041110394903e080459203c0e80080c4a5a6100c2c580b41050b10150f000f0740903181c02440307401d040380c144491642640d1b40054000a0302c00c6001c500040600c441d90081046503050b0302a15010550014010740148ac0400140440c2411240e51640c041c20202e0052011450114464245010800c00d4228810548480ca05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 756654676 1106 756653570 756653581
    0x60203120a020c1c1413050918060a09020a05060703030e1b0f0103020703031401081608030705030301120201110322060f120c1101110903010b120705010c0317 70
    0x2080800704203c1719281c010340041c000003089002540405d403d04007800041d0901403c0a450395400140507141710301c1c08211107070000021100400c070704129000040d140c60442e001140e10103000942c440c20550540e0240c061124608181c0340054003404560003400785106066800214000c600c1115600c030b030f401802c40c03520074200043d10300c80400d10041424000d8009a2a55008000c07950341e000d40000000010905400214a0490240d0710140c483c00b040c442d58410880001c0c80d40c04680c0241d65030100d44080c1001c803034940c0303040030002a02115041940d818408021408903000b442032034544d80080d087d0b11008403860001042070020089807c101040000030500c00f1510074081c01b60700000005460056115100c5004060031240c0f441e00591207602c00145804942401280b6801220401d00f4504842c05150a098880d00c09110300e14590301c035040c0400c00c = true := by decide +kernel

theorem cover : BRFrame.Cov 756474820 756654676 := by
  have h0 := BRFrame.cov_init 756474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 756474820 ≤ n) (h2 : n < 756654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
