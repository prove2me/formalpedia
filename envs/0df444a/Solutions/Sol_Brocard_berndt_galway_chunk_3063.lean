-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3063
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:33:11.372864+00:00
-- url     : https://prove2.me/submissions/30b7032a-00f4-4170-8b1c-71162ef0b940

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 550719424 ≤ n < 550899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 550720674 1250 550719424 550719439
    0x602030f040e090c0a090605010305010e04080304140102090d1101081308091003020c070f0f0e070906050307030f0c0207090f0506060301030609082101091803020a110d0b09060405160602030a050702 87
    0xb4400425241740041e0065000c450b20b40400b00481c0d6450b20a050040c07000307100c5025170b420701d03654552a0f48809080500043d8802030408400d100a50403140c409500420182a0b49400e241001e0081e4012410601140c1544c0000d15005a450224445143e001200c0c91910001404024401d6850403a807003c05500f80310400c1890301c10420600901707003110100302c0041c40c2c101040f00403001a089843c18220030030501c40d445402401d5a030a407103450400715101d42e01c1c0a8120000c0c03200d0040012014204108510600d80125070381065400e880c4082c803070f40d11004941416980b09445090304013108000400105030240c0c04000c1c82403180c00f1840ca01080625400d440800e8006442c1503103298000402c2106002c0c485c459070808104850240310284d134401944502c0740385e030080d0082106210181030f96072030314203210480c4c2c3c0c031882183c09424401556070f918038080301d080350300d8402c4cbc0303a82d4080d14014040001c00c80c1c90a038001c6181403002c90044410380c100c0041240c10400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 550721924 1250 550720674 550720693
    0x91407020c0a091503020604140f060403030f05030a0e19120201060e04080306150309160e040b150301020904020a03320103030c0618030507060c2f0703080c160602030f040e09 77
    0x1140801440104103000701800c0c2d5140301c9c010406540c0046040074441e160400c01000025041064035000f0451402e00d541c984e6540c091031800740c8481040542c46c2d0103080da180488084280a00c40c01501a0484649c444231044050f400c80768140144c20301004c050300014009440303200116804000034050644100742d8584031882d68100352050714441d00034030b21100c450b5100aa034040200f4840f407920f849802c00340ca0705900716202a1520b0300f0b103981d000c0303900920703182501203c00304180500219a504401500100100f2000200f480e0083c164190603807002204030101400d02032154a5810036465650180c5440310050000c0301c07095200c2a60f042c000040240c0c14420501a40f07405541c0d203030900e050421254984011821302c000c9928014048441c455440c51b008900040445054080321426140c56600d50006055141c0000c1c120440040801c4149150040561502283d034807010240c0c2c036409080c00d82c444243c2d0503c020480002c0c100030194004580c001515a40c95 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 550723174 1250 550721924 550721929
    0xf0f09031b15040309060e060f0906070204150801060f08070303090b160b041103100e03030a02070203030c010606050705070e0702060a230403050c070e04170901090f091407020c0a09150302 83
    0x2900f15010f5002c1031300c40c5800c0001c00d03008000500710f054103c401307a10340ba8415004100501800700319600507040810340d1030441d00c843c4e2042c002c801e09000101d1025640e081110f0192683d070140012007259202d00044c5490f00081c0802602e80c591501c0784c500e4148007010ba2213800484100055070058075070380d0040b905101189010b240580200b030504900403007411326001800c0d4001e03c8152034281d01440f002c00210640350840c0c9402c2c40588d9070383c46400040d1460241c10940c000f554600040015803941100050524502c10010fa0728030b80c1d40d540c00e401c90320500b02c51000242c1c110700001804805954030000803e000441c0d01c0104584003a03071204400012181140415000941c080008404015840c002d024000c015a410315040d52135500304081c2c07030000300e10f10038041035060f41a0301601c0494040e04841d0694504039550f91000d4014020484080e218a62650049004a48041030401d01300d0000b0705881d0310580f400b48850010f05440e92007200d1400d03880c0c00400141d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 550724424 1250 550723174 550723213
    0xc040f020306190317030721020d0c05490605040e210915030a05070e0d03020705040c02030f0f450301020f0c030729010e15040e01050f0f09031b 64
    0x800c80d400052b195a8443c0c01c1d642221599100b000900a044c04140912444090690b681022002014018841c800000c1d40ba0030b0300c200103090706034203060f800e1452403c03982c040c6040302c1c8111401d01c0b45601600845484080c4080c003c40c0e420000f0501c01c0654078a800107007072054002d080001c5403211225156459007064a0700802d1756201c070180030005034051110301d0001c104841e50303a4404c426680283da2600340e885402e001d15107a401072182940240141c40c56560300140c959586c0300b4059a00c1016442035480010307545000107542d100160806841d18004841c41c03444070f10300304222600d92174110940c4403607031664080040c1d100c1c1c001c0b8000501041183e40d001143c1350101d0703140c00940b804118100020000710480031506643e889246681100d0000c20301c0c1c4055211101c40b112030210b240c2001382c21500b428011100303d28150b0103c0e00c500e0545482400136100c00c2c081c01c803d42c109807a401030351351040c00385800028910000e24200c2c3c80400c212581e03580355503800d0405 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 550725674 1250 550724424 550724477
    0x4140307090f1a0301020306010507020d060e0610081005060f01180902040f05090c0f09090403022e0c0f02030915131511010e0303040b06030c040f0203061903170307 73
    0x286031a04074040f1142080e400c424a00e00044009609610f40130300001c00301d010f440d50181c4130340000885c42c010b006842e444442403001c18000e071940d0b46841c80b9000a040e005100d01005072207540b00705131085207213108581c0240d00c0107014070490f200c00790045854440e840e01002140d04c101800042e84101b900c0104024051040c0b92002685420700308640014028460b40640c402042540512114481155080f520032111048507407560304041f0701d0040000c81d4030140c246e140030074410003c11401c40c014607000b80301041c04003172203201c3c0886004506030400ca000d0b82c02400010301500d02410021a00c11007209201d040c000c2030382620606980c3e50f800181140091a00c180c0b40c19400300d102c0c04070683d55402404800500a52281c0da84002000a0654034000c0c1c0441c00c982e80c144403901044c0d80060003800a00ca1600742c06000b98003e0301e0480c03042000f100102e9004500c40691012a500415091942d01741c21038064913580c401441d0390b04000f04110790b1007040300f080c90090003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 550726924 1250 550725674 550725701
    0x2060c010c0306090c090e131b09020729010303030e0c0406030602070c0b070c03080901050c0a0b0601020c0d0c030b0a02040807030b0f15130b1507141009080414030709 74
    0x70b040386040b00307032411100176010075020420b034150305000c080c44040d0386a0708070200e0b00c4e039021400401d0a10f113480c0204680c41c00f100c100c1c103000000f0f01d403145402400e40d440c042c18000440c02204085400001e90303003001c0740080c42a680041021134081c4d88007040d404c0f075038010f03a0350308124200050100c69840d00100c4a841d8049270580078441e007028501c01800d000d1100314588207041c0c1b96411056190322005004030301c00541d0585c107910030825601610401400c8aa40031024504200499811218180184a2803403000703100c0c6489a000140e890300100082c8011303003180c80302030400500608031400795808000004000d002000518020350240c0500031003401d0206421000d09009031400d01804000440030039103a603110b508006000050800054150081c8082010b000900f0340713101942e20041601e909000241c00f01e020140c40e00415124480740070030710728003190001c04024003504001d105c188035032070034500d00000560004080350b070000d981c0c20349070302954100c891075034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 550728174 1250 550726924 550726931
    0x11030c1206010e0f01050a03150603020405180610180207050a0b1f0b030705040e040321021308030f070222020f0c01290609011202040b0309120a090308030402060c010c03 75
    0x5a40405109078000401c44e5031a40700703500d0440010013590316400082d1400c0f50081a03070754210700e281d00038030086501810a200a16182c0049045501c1000c9a1281c0f4080c81c00001c1006000d50b14240c07c2d07502040d01d90010a252139000e00080d0800b00084a07180b01da400b0b1280400d046a090a12941c401120840d51402040521046040951005112002c24403e0000d542d03042030944054400500b01c507402503644d03013022150441490203c0101d018000e601e40c1680d40c45030010903070200300b0311070346c0c000a5480558554070701c00d014242a002c1300c10712a4500519150100d200c040c0c1d03501003031f0050aa134251050089a1200d0288045250300060798010400280542c0f07011040b41041c00d026603a00d80403409000f0520540e0714400d98001580400c6680503000386002130904036004c40d2610f03100c0e0340c603010b9a44242c032420300501c10900c40c00c0a100246007142e00c000d046a450091407440c40c1d0381e11503140c0014100300e138058000e100c585010036091255026030662581c010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 550729424 1250 550728174 550728179
    0x109060c05070f081c0806060306062511040b1503010302150d020f0307030c02030307020d08070504080f0f0129040513050312011809080306100903080c030a030b1c11030c120601 78
    0x174120100200d0780400c1c000c4050410005589034015254031810a40300f09a4a2100020510381c40202200c4000e0a440314041c030000d010002e507020012031002d4804100501d200d10801c42d220400c400b071025502e031b0401c014030050502c08540e90007100501091802d1041101c030b0742040c0c3e0000348291070446404820400039a40c140903000f5584245d00241d4070714240044029154240c0101003010320a5000c04104680c0c451404c49004001000c01e0701d04025044001030340701c000e00196040c0319801c000a0358141c042e0903140c001c034008110b441d2210f104400042c00080d280c014540e40c400c009820780600450401e0008001b0854414000ae00c0b943c1488100b8029240100484920314605070701140050401800c4a8200b60129004100c14811484c101d032a582a45c2008200c4080841d40290107000000a0440040c0980701031119107919414058003045400d101c11041d01c1410111000c00c0701040c1c030a5000002030300f03441c00c024030b007408919041c040c1100c0e40790503803120004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 550730674 1250 550729424 550729453
    0x1504020a05040908030f090c060d0906050a0203070210090201050409110a020f0c030c240c030a030e0a080d02030703060801021b0f0708070e0a06080706030902040b010c020109060c05070f08 83
    0x1603000c0c160803a010098080c2c1c03901c03580c07010301008080303281030302404000c140505410850110440b100034503207548c451203021210040c04801e04e040783d46e44d043c0404268200107500907a03101d8407280e401004003190598000c030140c50986026030600500b00302c04070310240d0b01e002d0150502321007281243e0b44d464050b0000d142810762070000d401504000d512403001e42d004180c80c1d08820040700c180d0041c800c076960302550042541601e006104000444c210100800310140c01c184080c5c0e2410444013203d40c0c2034607103c6601400c01000d130001040308900700d2540c0c2e40074540003079880c940001c403203881c4d00503107003242d001d00c1d254003a13900140c10500c500a003c100d00800c185404001d00086480c11917070f5540c610b8180180140340303000300c0003e0101141644103400070b000020071a4403060b610b50019000b03052554003030740594107040800106500420541c08a00d42c1a59542496481c00d0070840391010060b00840740c0d030080d5100000e0311071058080b00d0150000e10040c1244580c036250 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 550731924 1250 550730674 550730689
    0x30b13060e09070e180f03030708010f080a020d060c030b0316090c09050604030f020114070f03171006030f0905012306030607020a06050402040b030109050c040c02030408120c030903150402 83
    0xd020ba55500c80e0324244084094200d142d5000b5224110351403a040c40141800d0070b0215009905180d0300c4080204000e4a0b8410b140504032044207003d821111307100d5584603103c502d07456029401c191910078a0300041c1c00799010b40100304c8545000501c0085040001381010030200102820807030101050021a40c240300d81d05200700b4a06141c2c5010780f51001081060007148405420454400550b4003907901403404a87c0545042c000d00703907602c8007450450395802c0c551109500041c8010440d40d484c07081d41510500480f481b0074948612890b000048024201420f501c0d44146e0302d13084c559000541c00d0140390910111039001207403c034009000050b00b810000c0c6824403d6001c0018042800c0d00803c015031001d410020203e0190360343d002060240c03a131000d1071034041d0328096404084c424040749040c0c040d08100d5003400701000d07400c0200d07036901650280d0a01ca4000c1220840d90824220050607400c03128800c0c0c900301500780c0c00085c20851060010500d0425210802c8114030380b603003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 550733174 1250 550731924 550731931
    0x130201230307030906110c101107080309101d03090d030e030d020309090615031501211d07140919050106050d0f02040b0901320d0b090124030b13060e 66
    0x171821f081c20702c0c0700902e5585035105c018032580380c0e80d03c03074148612141104c100c4d1f640d03a401c0350407190b0741d0404018944c1e0300ca00c0946440f500398901303000388114405040000a0034018000290f0802800400b00012180900403c5060100c7c101c1c03000c0c2c00340c40901c9501c000310417640165469030b1640c8240240341c20000d1a40344a0004c10b10799007095a014030550350080e80c0f4922920340d03491400c005844266044c90000d6148192508a200220190300038946481c41c0c2d031407a0304000c0140040540d50b442600950404c0c11101c020701500d82030101101d13030703c01c0d40d5a04000005080c1c4da4480c084034001e80200000500c000341482c0e025116020700022011101000c5181502c0d00b4440d07940341c0241514541004052001107031a8642e0044002c2d41c190340d441c18000300d0005011941c002d5200c485c0d00151725080c1070b0b02c07490030710345804503504803031603054584200c080d00e0f0414201c6a00030300d01e082c103060b03407028041441e0300d4010312008504051800010060700f0100103140340300009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 550734424 1250 550733174 550733201
    0x8010e0c0a14011e05160804050f09060604090b011b0f140a03050409021c0f02030601141e030603190305090103062103030e0f0102070b100e130201230307030906 71
    0x21100002c260768050580c4544104106100443c0000e42008480a218180c1400058041c030f50340070044c8162540180200c0c1c404480d400b1504d100c4405104803182c04841160380200c05020030018411a03410005089005250641c03140d103c200e40003515016001068071008120702803e006c000d00c5035424000f2617a0200209100601590003c1141c4500e00401d04c100b50041994210603104410b801c0c2c64180c183e0091007044810390458009400807103203640064010b1282ca51000c0741c034412202528010010b04030358920f05145070506d680040d0815426215a174042024181c852552840040c4603075549a5503072244000102661466004120010400c61400c201800207008520660794103003070204202c0714840c00f0b00d00380316100c1d298003019400010342c501003203a101406445400308501802d041c075101c605c3c1c507036030044c1120f0003140c0032070500c0c503000598025420b404408400f03c146105004400380441036a03002a0fa00b0700c086511760702c503481000024090040786840d00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 550735674 1250 550734424 550734449
    0x4150b03030304050a03030b13020c1c0504050303161406090f0105070806091803040b1605010c0305060a0b070c15121b0e04020705070b16120504061d0a08010e0c0a 72
    0x90303220f135600c40c3d04542004042c195111580401d64442c15200d040e0807051440031903d0f582c01d0240e881d101d00c403001d00c902003401c2003006903074041c2c040c0d41a68190b440250045003010104521340314956149601034464880070300c03040180308400c000b860b104441980107080041d03002c510f09401d441001c1d01240510800004001040e20b4100e4403981c40a818a02c10820107001d1481030305510540d001440d03036400000d400065403400c41c0794000320510500080001c002020812803c495042d01c00c143d003e51604c4040024031180c0010380842c40c01090460103044c2e4401c80584100d40d04c4081c0d0b00480c04c02d420880003071200c1c2c803070042886e9062180f5034014407646001803003040d0407060244a160f0100d012800d02900700140c0c0094400340300b801e56609402e2162144800c01c28904580a05511100d8040d840c450020340f0700710b650039211580780080c10000701c656054110201c5801c00304090340051119024040d81d1540c0c8105800741400c0c030320740300c140015250b60790032600301c4840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 550736924 1250 550735674 550735681
    0x140a1203090f020d0609082d12010e09150a050f0a06030b0610090f030f05060702030c0c060901230c0d02060103022b120941040b060304150b030303 65
    0xb1110303019444650403145282240d102c3c0c50701c500144201d1401030030b00d0801203010040303a1a01d5580840c0070041200f51410011005004019449200042c038141d00319400104404148210103e402a401100ba80e4500740d980702c0d241418401100c0d08282d05440300140440d6690ad0071001e90020081c030f000340012429502c60941140b0044d00b50750060340280c0007406010b01c603064081c040c00c90506030815055032070038461461314810500f0355030b034040c0c240820045030002085400c04840100940842030f000c0c1c007040626000841001e0502c258500103980f6146401a144005080b450300d807512100d400220503d403045004054042d94440700c0140050b0b5a0400c0e00b0a0051490955030040c40300e40103c1d24181d036484100a007401052007505582a40101e4454103680129080d00c0090b40000510040d00100500006c14011080c0424940d80b41610440000840c003130b0011800c0f101d04000f00781a035100702c40650b161400b1b18040c49140106019601c10504200d006504605 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 550738174 1250 550736924 550736933
    0x2a07240c0f1b030c08220e010e090f0601050120190c090c0806060904061203020d033225051e041a0705010605060d0c0905011e030f0207140a120309 65
    0x7040e512002e4203608010613481449250040402e0394828007801111b0710a580d22403042c9186800e01460f007030103980c3c03000555103400c000f400341d001440711801440c803a481c000040d0356075103414000401078071000b501c805900b481003080d40d280884280d48060341c20068201045856030a4010f4500103080c0a405040f441d4040c02c51394000d80d04030395490742c5026800008004100c01ea202c00310090f00256001e051540116640001c080c0b5920306000014808881002c20b607404803020a180068400c0c0b28a080501c00030542d0242c09040a841c0c1480c03000e04604480412042d080005080001c505014000812640c40da400d00100d005080034140031840b01c00d01401c20426501c1c0b0307808200401170040075002480248406051b1540d140c3c0c002072410b0181074240c201c8404143e040b50300007299441245038034004500c141d503c1941c084508800c902811100c602d209282da002c1c442000402c03910700c0c00e515807512000081c080c01840c2d20700805480310344a140424035240c1003510010a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 550739424 1250 550738174 550738187
    0x10f02010515010503060d050f03030a2301031b0317070615060207120821090c030f06061309020a06050a1e0c062c01052a07240c0f1b03 60
    0x240b00900344107469030703504404600c46412a00740900148252525240950004402140a00641007090041c0c00d140582c801d40168100225542244a03400401c08200c00108251884082ea44503821690b0740c1c1d00c400304c03030042c0c2e070003000f0340b0034400030360041000180d12400d81e001e43c4040340446190719182c0d0284d292000707480303000d40802c41c940e001010008603404451244400d2103407040009100d056250070204110350080700e83c443c10450000c14600010680044100c01008080c250346160a010350301e070b1101940d24850380c41c4d615090041e50b401c03086101804440c1c4d00d032503c51410300c0c00100403440019202500740801d40c1d5a400040e800f21385180c405401c283d0104074010001d0350908000480380b440c80d00c40c1d503400085465a0f00640106009080d01100d0250200c061881c07101d01d8888146484100d00d0b080020800083d001d8409500c5042884500080d1184203501d0a0a84101050480000d101c01442e090307516013002150900d41000410f8500c44011554040d040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 550740674 1250 550739424 550739461
    0x1060312180305060109050105010e09060d140304090e0a0c060c0f1b080f150c0a0914120f01050601020d080105180c0906040b0706110304170a030b0d050c010f020105 73
    0x4014108591003124099240e0308070082d0b5020f011103040d5031352040ca801c0148800e000b03141c0050520100c0000c14900518140d01802008100014070800769585801d401c000c02002c2d441801700380000141c403005d900c07680035050b03000300103030684158502c1c0181e0042000c2c0c00820500005007003a80105600b42c4016505a611440f0103000c0d040e50588851000810340c06010340d0310601c558540c01e1400450080c3d0041107800d18852961581c511801c1e59001e2000140002016500c04100c3c204120300b103040c2040000e813500351001c242081c0c00d428000c0301c2102a070326039110380038407010f560304000803d40c400c040c0c5008e4120394100070002e100292094451803180c080000410501182d141c101c818030343c0000d24469503103541d00000340e41500aa41c0503034000c0d140804581903150901c045a2140d64042c14450001c0d20342c404201c1e143d00b00150001c00c050703941180c1c5a498a4502c0e006101f076000d04000e200d881c2100e40010401b44884081c101164180f0044c81542850400110b10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 550741924 1250 550740674 550740677
    0x70f0920041502010213140406080c012f0114040b011212080405010e1009260f1c182907110a0b070e1e0f0d081902030307020c0301060312 61
    0x15422520b120407030280c0280c0d40000c0b92048142c42c0080c00385218084840300d00c03000c4c1c43c10310103941e66031500d54503181e5403c1c9050211300d101d00c170302144241c9000c40c04420720340701c480011900505860903084600c2f9108541c0701d0301030390090009025041da0300350700501035002d503005510440e131340d00740048074440c488605222100000c6000c0140031740011840d02c0ca07140c1251488412102c3c00f1010b8880798005844a101d009800440320280009a0b42d0740e2806001c180d11704141c0502c1000360b680f19a10300240b400121003090442102409540303056502c00405207401e400e1030800d50140c0031110317001a11890402c2c00350388803400328542c05510a0003410070b5405000c01c82d0405080c41410007004042c03407110400c005020707030800c5004490140c2900c001018140b12100e11500d00e1a8502c02640424504160030192800c00d0034082e20b18400e5820314100741e8100d10780d112480b1200c0d0800050b0300080704002c6616410046010142000c40003805124555100c940780100e13a1400c100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 550743174 1250 550741924 550741949
    0x3071e0c0504090602071a0703060f0308090d1401110d0606050304020a051903060516020c091e070c120e0f04020f0301030204020d390f170414070f092004 68
    0x910403140c1c1546d10307041e0064034401c8a900103c0c0901e0345c81c0750440d030341d10100b4542000403521140710f021710380980342c0c0117140528001c1c444080000304a1003d8007211031081030603841200c10000c1c014904c07912403c54405403500c0e00400d40000380c400c15000300b010410305104100c0540e403003101341c0702213a40c1034507076112040d080d4840150320610360300041d02d000d007400140104400d90745040d0090503507660907561050010303004c0060101040c1c3d03e41800035405e10929100142c0b44000c00e8100c00e00742807a00000b00b06079a440641e520390401d80700410b11885d04282c560904051030700d60280c041302d085291200b1921074480038001808040e001d41e50200300241303031603059401070b02115000c441c03c101c0741c00e03030150020101000a51120110020030702028001c3d005550220300c0049079100c42107920884c4840c1901c0d0b800081090f01c21009054541106030b0003070010b8005003101c0c284201455050600c1c4006076034003030032541403035000da0003910700004491041d101501e900c0c10561 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 550744424 1250 550743174 550743191
    0x31e020316061b0c0605060d03021b01030612061a041e0245010c120804050a0803090d020f0a020102030403021009050a12060b0906030712030c060e03071e0c0504 71
    0x8074001c020f002596543c2c80d04210300009600d070031598101e9182d10030305044c011036845005220b80c4d1180000001c001d680104440c03d2000078040950800280624000030030b2540d8951640326400d941074151903c0b80d07203802d08100c80020b044490303402c190030b68040c4800080b00745105415214015901071040e40442c0c0d0300c0701495950014807509480c4c0d42501c1d00c00045500890303403001c0740c580403900d04000e01048469035000e52a07101810342c00c001091050301004006407000ca4004000316540d000b00070504000500000256024865075001085400f02040001e442d00e082d9005080490b441b4245840060b0703030002c1110186c1380e055400b0100284001030595154289030822a4800c850b80d102040550021141c0110103019070000d105040e110028001030000c162003564040d08800c609201d010015861054014844d203016000b009054548070201e030031034001c01c0d0168000003680b00c280110816010a41d08040120405100c0c3c6a6103050b01c1e910b2030310659015a4035510701 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 550745674 1250 550744424 550744433
    0x120b01080a0f150305010b0907020a020d060b0f09040c0609140d03031d03040b1e1606050601051c150503030a0e010807050c030d150f030503041707080712031e020316 73
    0x50f41c18603c1d4114070784064592410354041d2004001c4907000305292000a60420b2001a40181454000d0000d00b5418000e8030352030b001e0070760075a015030010f4640000010f2511a0701c1403503c118018100d420047e400c100000703004050a9020659007000711544074410786d621100d21028a525040c000780801724a100f1907a90350070001e410282d40001300340000c5500503a03000f032074401ea241a206100c8000810000c106001710b44801580300c2c006070325000064482e5220507000601414014200300044000c480541e1031442c0101300c46445001d03030201c10b8245050b203409070008501440c24140f1941c0b0080030302c000209641d0400400d28003150744513000b0000c94030744041c02c0301920364a0111100f044050300d1240b0304180070407440700300044d984001c802150203030307680328000e14030301850040300302100c4011108035007090180701c01c0014010b81c100480401061241d01072082d0310568103016042c6180c50000071070444543d80b100c1c517010b0b80841200c20035201400100a680d119040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 550746924 1250 550745674 550745681
    0x219060b060f0d0b0603190e160f05100c08030a05100b070515010506091e040209061b0d0503060d0b0406061a27151b12070201120b01080a0f 62
    0x3815508160001481481480d4100060100002d407680510100c0c00032000d000451004850281c001e6541ca4a00c03a102070303c81e00115800712810f0201c490411141582e08014681c1c0d6002a00142141070b0401c1385042ca101d0310100f504060070880c00c15582a10303298104c0c03000170289a540d5541d10000340007221041408009440c4003905d42e5210003040c501b40d640d4082121901141c001d542000103841e00d080f10450710803c00c05007512007201040703680c890702d18200044032984140c003840380c141c1036210b00014240c00305200a1084e4036040002560f4100410030b801141040410030401c5010b89812180300002c0f0f903ca00b04001c03607a41d6090090052065801141206d200800c04210004160016014030801c80c4602480031b11103003010611210036004868001030240703214418004501c010b41142c00e82d84021030310320654064031605060200400d01007045000c40c0c1641956840700c1d03a040300001c0c0c2c003000c2000805c90f50000e0b0603010000c0c69903015a0f11613803000707400b100d00d82 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 550748174 1250 550746924 550746941
    0x101b0f150b030118022202090d0302070612020403080f030c07120306080c03150c0309030c010c05030103150b09061306050d0b011a040609031104111602100f021906 72
    0x4041901110400d00340c08003070500511401e10960901c0c821102180d91103140b040650384c02803da55601c1d440a0040c103e01c803d032960042d10035828020000c06840b00ca982e008031600c02d5025140d074504103107000d4020287c0900c0303480402e106100500c0000e441070110f403217181211403569120303500d106200c1414070942d0340c01030500441d0058890300d80d80541102090742e642c0c10a0744c0e81800301b001071594580a4100f445003001e014004280c90045500055401015400950703240101c5142c4150030750b0032071000d5000241002004100303104000403003440c4004410130601c072000124000a4889a02a0440f0301c5551414141c43e54880d02e6400032008000281511000d03214a01f0703c0005070101b4415132210541000d10b079100080c102084806851680d160340d0340705401c5887d5240000d00c82102180c03c06c0d079440c4400381200e00302007d40300b001c083d0384425118081d80e2040c4042c0d84d0300e580d00316060020480c10110065004200400388441c0c031108513400c041c030781c18617801410740036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 550749424 1250 550748174 550748183
    0x5010302031b130303020c18040605150a0611010515130b22090618031b03091d060a0b1314030330091c050309070504020f09030606101b0f 61
    0x3c180c545102c0d204043c500b1a4042d8081c1c6030140361450511218403080380501000c00c1c3d459001a0009400c0d40c015508440101d030102c410b0540c403000301302c042100750810383c080744082e078484082c08024018030364450646041164003001c4036003c2102da0325003035140c802c03442d120b008000850f1201c01c00303240032540348003001da44414001ca0350030060070011410f480c0103040c45003007100003101030103070380c5520742c1680c0c3c00d0a9020300481c030030a903c202001c101c00700701c050750002840d00c485c04040302d800080451924480e00f0041c04200100b41c1680c0305041050b402c1c04400c4291a0926200044903003105010400e5003400700000d05511401012541c45944250500c040011400808004c404548141805038580d4040075907200c40f0103900600e01340e00a02401d61a074403c1e0061500070360404200d41c4d00f80d0b00c8600003010f0f60480c10402032a4207020450320b0640c941040740b150004000e56642000d5410300800401081900380d82e04049910506004204500d1440880070385400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 550750674 1250 550749424 550749427
    0x5090a27060b21010305121b010f0515030607020319090504050c030f01090207080a0e010302160b24030712050a0507180507050c0c0907031d0a260405010302031b 71
    0x840d90a5140ca400894002c3c0111000ca1000d561192590f98290b058940040c01000c80380041d20804d009070388107042500f48000d500a00b144500700034018000611055140481c01c2e140c000090400c2d2601c0343c1800f4440e521201c10b00040980200481c1c9440710084c407010142645e4860070344401c04d9590120f500b040c901820008402e000801560207505480e10349109a41e9800100040c0d009074030340908250020890b1080d001c0c0a045040180d80c0181005420f000180c2c51a4072110690340c4251403400005080126500300040743c82036011001c4034118008440314013281d51b4000034017654140302e031114035450500c84200142140300781c0c820100c40806840d440c1d200006444001070325442401c0401042c1c0860143e02942d90008804005042809010703007005003040e00500081c0502da941c012031b41221600812401e15600b182c00100060071191034041030044640b1080f4100e5802c80a07001d80c010801011035044450901e40581ca075180d91034020000040e51503225140c900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 550751924 1250 550750674 550750679
    0x911101404030b0a0509030406021018020d06060806070f1b060908040801020a140405031015150302070209100e0a090614011409070305060105070209090307080a020f06010605090a2706 81
    0x4505101134481c00040e1014015511100305103542d074021070183e0000340c1c105107581c1121500580c02044155004006006010625000701e00442c0347c0714800c0d00c4403602c03907100380b2a110013000a241c01401d0340c54055507000001400400c010060700c0741e240000071400e4458217100392904586c0040d0380142105580d40e50792000d0b036000b0f5000302180030104d400d21400482800e4400140d41c00c0717540c050042c000722513041108c21b0050428a030340d4042642400404074130301c040b481c00c810740d2004540740143e540e01280104240545d00900c80035003202d1055080c0f242c40c00400e0f0640d08504c8140000c50303041850714181c0013800507841000c1580510000000c0d4a0079580140c2c0c0d401c0f6010390340208203803108401107094400480e50280801c208001503070060403d891140e0b801b401007010b50b41440d05540e50031820341c3c405100b027801640280028607462006000c018010001e0381010b6103000c3c03841c030210f806035900b489650083c1600c01d00200820007081c020141c100d807009020402d094 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 550753174 1250 550751924 550751933
    0x904020c1f0203010b03070c0501090b010810110c070608070201020c0d0c061a0f0d0201020c090c190305090a060506030c09010305010203011502190206090d06090b0415091110140403 80
    0x24480040c503a00c19035a5032007032a40941a00c00c8074165400145c1040c65a500c2c0c141c1920645040b00046580e0345d80e409a00002c10041e0302190b001c2d050703400180111040703000c1100b0a82c2c0c00310a644000000402141480d03040016900048038840e080071400e035940d00e20203034020f0240c0b51014106014a41c0e041021b241d0000d4010820f522824040216060041501c40c240c450317422002d07000944040003408501d03142d041083d00e94414030480d01003020860210f01800c038180c955141c48600425401074201e800d43d2442c220704d4541ca0b08020a24051380c0c1155070700e02c2c41401500107603032400850f074a6142844026064040a032104141e0b580d43d2034aa4001c3d03209101e060b6030002540e1141c6001d51001c02c810010724800c070409e905540854080005540c0106980c0d541325a505801900190302801204001400b50f001c0300e500e440c20741050110300c200c202203420130501d0300f0a000001030190801603207140041d039805409800440742075a0704000951040c5001d44080350000800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 550754424 1250 550753174 550753183
    0x602010506130203070c03270801020a0e27040f020607051e0c09010902030c1209030a08072a030207050319020f09190b01020703060c080403020c2b06020904020c 71
    0x82900341d030101c4056810b00c0e4004201d00099640ca400540302c051440e01091048444240141800101d1001c0120b00c2a80000f40b00040d4440304260350080303042e541698021400c0780100034195038000000c02080032036240d842d460180340b140110004e0200b0140003450245021881c3d01420003992a00da509000d80e8455140740045c20300f010346200207480c0c000201700440c0f00e007400b50150005034203281c4048081c1d04000c20103032485400b84040c03094000e1240049000d2000714019650340e14040724000c2c14020010803100512140f00450006080750000d1403400c0304107140c0c1000e008400d46022410b10710f4035806a80d145c0b25259410076504404420300d80941d20888800c11749910017000e0040b4a202200d502c00c036002c0502c40030019400301e81020080150502c1903400c1561070b556084202d420320f00148000400e440c08110030943c0400a0000d00003003102c1c50301d40c032960800700304805000300401c009043c0d1101201410810560103071429160000c0c0190b489240702c2c051103a88 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 550755674 1250 550754424 550754431
    0xc080d050f0f010f1202060c1606050a1215060e0f130f1a03060705031b040e010305010b030106081209150f0901080f0f0103020d14060c13090b030d0c080d02030106020105 75
    0x2c521280001411070040302055045071848001c00c4111807440d005c11400d500711203078007a4a40541c4020803801490030b0400c80140441d41c440a441c2da080e44801800c001540f24030b034140c00e142c8192120030040807043c40c42100e0480c0f074050140d40d01e05000c039008a0720141d0254001c1c501c0250000001215003140c00407180ca40410130460030020080002207450b641d905030140c02c8607002c2402140315500035030f4086c0384614050070501d4140c854520603402075100042128400300144100038083c0207507491501d04170024440c043c1000482c944821000d01d8249060500081d00009600d0307240350b00c081c11000d20741d455194000401d81102552000003d03d000581d881c0008003241e5501d0b000ca40240c1039049101c100b40c1c02c41e424030100841181c07040d52001c800249801c400780d810040a4454840c0702c0300241c40302c07000841000c050301a904131403401030912500c900142c40000750911700380e80a292190120320f260510610074490703182c0b881c1c541400000003169013074054124901 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 550756924 1250 550755674 550755691
    0x30c06070f030c0306050d020103181e0b0601030905060c03100e01090b0909070e0f0a060e100f0503030c12090619030603020a0506030103051507050c0a0f0b061f0c080d050f 76
    0x40760724415004c40c200d680602503154040d451845620255100354015a003e650419202880003c04e803680c80340074902d0381c0c9000442c40e03101084410094030600103074002c1f0f020300701444080110750b42c1b503440e400700508241e43c0c400b0100001e80a06820010750713005002d034205100c01961518614800741c1003110083d0300503440311000c1100c00d28000394482c12070312001451500344d210019007509662001d03014040050b00c03a900070410032402001e10f80a40942589400500d2800e031303800c4864481030307004610036001030041003074448001c10002e40c0300003028600f41d81e8030050030002c2e54600800d82c1e42004101c4c0541c2c070030980c0360150f002100f074074001c5070400b035415035920800c0f403148424000188130b41c03c0744030240e0503120b04142a5401c21070034140359083c4150700c8201460250701b0101500d05414102c4910140070307079100c00744d4011b501641c6508042d00f12400c0036402296003105c903070412201043e40800d2014820590300071903400401805141807007021440500e0013601c5010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 550758174 1250 550756924 550756931
    0xd0614030618030a030f021309020d0609050912090a0b31050a0b0901030605090c0717070206160f080310170d080a0207020f03030f0a081602070314030c06070f03 71
    0xc01c9080202c45454032000c0320001545080e540190031030281c890180c400424030740a10074100a441c650203110040d010200e001600e0303001c402000c0050710400e81c41240030031715010034000207800c0400d1400400d401b602d081540c640035940032408040c2c4607804240320941c0481d881c95500c1480e03810780002021196888504c4600d001c1e52903d142c1584185a40a041d070402005040c03514400f50a1080c01410002a400c1c0d0340d20204240708403c4a1110703e100300024240200150b0304c214000090400a117241484200ea01140f04c41c4500440082c0c4402c0000640040022800d9540290348d4448110f0b40c03030b41800c0c06481c4003000b050007851000a540814003030320794400540c90302c15100039580c408087e26120070440c02517101c808140c0c0c0020390820b010f25191810001000c01c410030307080c038980e101c840340c0b0000c04901c4e002d41140414145214024a55036000980e82c1c152a084040c204192480d020210300e50f2180780320b802546d006000401c801590032a68400209031a0384051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 550759424 1250 550758174 550758181
    0x31602031207050a0203161511010b150408010f050c1b0307080705071721030702071a0306090606040e040b0c0d050a0b090117030d0b2404030c050a06080a0f020d06140306 75
    0x18040d840a000350030061528081c01c20080d4442c0000270480c114120000449000c0324020070700c00701b4138201108884100107010080d50f0824840d02512101d496020842c0341422041e5008031704c1520088020707038508a42c406003000043c8200c4441d0b90b1300c500c0156540405240243e1907400c5445001940b14098284803808400410b4008628484c8a021500c01118100c000710a401c06000c0d94118442c4400c081064405006e02902000d0300c000559100d242400400c5800c0300010b12640c00303200140700401a000c3c00c0c4c00c800d60041c0d40201c04c01c1d01e0303648001402800b8051080d801040b2801c0c001400350500043d03001007120f101c2528284a241c2c0c82d032002441d03461b4810380d904401e034820000c048590b02d5a9010002110004102c64034143c1c080b0340c0c82000040b00c4042d400900700000e010020032502c100400c000b4074040c1c8000c0c4007075240180107003200800500101529458240c0760016141c59030441e074031010080da0400c021030310382c40307540025049860514000d1181c500031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 550760674 1250 550759424 550759453
    0x20a090501050d0609060e03160b090703020123090603040b041406101202120718061509350c0103050901090203060c0c0708030f07050d0c05031602031207050a0203 72
    0x1041d050302c0c00607040d60444902551060003e00b601d90040d10b8666171001002100801030000b41902d041d15800150364180a0030503c0341c8900142800b61240d000240801c010f0740c01502c0c140300c0300c20038101c2d00c3c04520944042e882c40c0c030480c14000d45c4081d0000800040044108519010710f00035030380540c1c10480d250420359210420b4501c40014540c8071000c103e46869044541c240302d1024101c522000c101c411031519120f440d410001010b100c8011002c1c010060707105580040c0790482240050104e51035010b06040000e001d601c000e07260507180c018890f60928424000c080d0300da00e042c0307400c80341249010f4940381030780c000c01d00084c145404154120414010f4034005900103024000540b6070360f458142c60b40c000c0f0f02c800c0c054000c00b0380c0080d11180c18006411515001503401ea40c544041c501142402100700750030081c010b02a8580300801c1d0b000085d9400800800d03102c00050b41c403400003d10701400003c01d00d1010500007503000810601103440361205100350f00f1149500101c07441c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 550761924 1250 550760674 550760681
    0x51c0924060b1b030f0304050604050d1707050a0c0c08030c011107020a060503090f070e04031101020715110c070f0303092c19090b01030c140f060f0f1303020a09 71
    0x503a8100d64020f00032079811500701003450a00e03c3e18041103070700d003c080c0b817010350f02900125003c1d6440c0e0481c1c0100010301005103e1507a460781d0a1805820ba54805c0000c0385030840060510b000308003010602111070790280803170084c801e0b08030b640242e00340d0390750004c03641d00d5120641001d043e508054041a0710b4001d24156000250b00800c00e100b0b1030b0800b039086505400c010a0061207100310008410445c1c002d00002010b0007a01a003a0414501410003400b48800451440b8450780f0410508010581071011245c440901c11008108803e030491034005a000700034680c0d0317050041000001b90b2400c0c103401c3e04220b030b02c80d44900140c16a15095104841020248226842c801e25001d26034508a010020f0f07000b00314422400b000b07a049040001203e00070542200c51051313030401401031000300003078407004080c1c410b0030728104200000812010001c0d181c0301c40c003450b40810004004a01c0b202610f81c0e4503503003130080340c40c1c1905042d0307502040200d10080e8000e40c1c1e905004070f0914150701 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 550763174 1250 550761924 550761929
    0x1c0b09161e090b0f0f03011701270605041b23030102070308010608040c09090311102906120c0a2a15140a02070c1401080601051c092406 60
    0x111000c003003501c2c11150f400742e54404003413010500d82c20041d4600020900c03020398040e0106404108019016005050848011700b01d900d01340070701c00d4a9110344035584480d4a0102c0d5100001150302c0e243c9251540c15164800355503900c01601c900080b4500c624035070b450070100c0c41003110308164500f0205040c200d00c1403d0029001411000040c0907240c000c46125400030322551801c80b1f13a540e505072140444800311022400144001144003071040c00300141c080d440d400c4901004403c001c260901900c1624204000e001041c80710051255559a0700350780c203001001c003100c5400d10f010702500409a1000298001003440c81c03105000001d07143d400c4049086045081960160039602c6d500115182850b420310415201c0f40883e00400c41070345000d01541a001c07003d41c5496003494400c0e8050b109400c050010b00000810742603a070b90144000d60481000c0c20729075a1444161041c11040c1e00c281c0b101810b036030800c600c1d41d04001e2048010001c0f50300560315034400c9009a85c0c4c5105940e95403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 550764424 1250 550763174 550763177
    0x18060f04080a051806120f070801080c0d060b0301020309010501031515061d030d080a0f140703090f0606120b0c1215030c0904150615051c0b09161e 65
    0x24402d0240301c40c024002040c0d503c5046203c52000604080080d003150320a07440303082c00301491000c1c0a505d06c80c410b401b9811441d2400c020082d9810304903225515044006943c1c4030b61041c0070010103001b400e6000806e5600c01038001c4d5a40d1406026580c0a84428402112071000305804404040030034400d128140a100e40100004c514010046454156010300485102800d07141d65034942c0c7c041142c201070b01115140d14049240030070404003260050805a86191308082881e4000011f429484e07074010b007242070028641c10903040403481c180b4400001025a440c00601140d000702510300030031038510541802c0e4065540500820704c5005000c00400012010300114030100e50420f01c101418101030121501c0043c0c1c20300240c000030040e20282c0740c550440c2e44202c500704150056402803d5556a101395010851100600c688140308002c2400c1202c3d50340e1545403103041e00141c28040c1c0013803418469080c0082071801802080386030501046203410303005c6441490303a8150b1604002c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 550765674 1250 550764424 550764427
    0x204030606030210020a20120f1b03010b0d0f0804120803041101030218090901020c1e210a08130804060e040b0102010b0d0f0816030f090806040c050409060f0518060f0408 75
    0x7c8042d403403400680c094015500100c0d0206030300000ba0100a204000d0684500a110484e48014045c144a0413110f006001346d0401000740410744400703001041c00e86d0311003034609141501d403c0445640c06540c01c542240c140d5060800c05004004010b58000d601402203c042012540300540c124400c2003240b02c8000300e40c0c215a0041d15001240c0780c2d00c0b00d141c000142c64507c2d904003050400f15001d032101101c40c440c002c5d4003a808800c02c4100761002c581c02c8803c0c0f098803a80741e81c008d42d015841054007000030660014540c00c40c0d058019850302c1c0d0017500da41d15140c4500f0080d02001e1a100c005000d2440c002c441c01c520343c81406100035000b800b804089104032580c481000d0868140c1c0d00360b45004081162000000d04089130f42101c900940c1c1d05440c20000740c0c0020a0040c0540c040c10403640700400307000108022800202c2221002c60f000035030168907251000c06846046441c0c0e103018680000c02144a0a0303404207203010041c9001d0301c074581c0e0343c8005010550300a9401038002c003030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 550766924 1250 550765674 550765703
    0x30f090e040f0b07021002040f170325030e1c0b060a03030f0c050c1002070f0e010509130326010f08010e100203130c0b0a0807030c210605040204030606030210020a 72
    0x1059000307410943d44d1050751b11002c051404031090360701550240304034140e0010100a45103040c40c8082107140c0c10070203036140441c10031880a06450200b040d14031680034250300d40030507010316014011040040e0010702040440462013128102901c1c0a40703598480e02300042d41132130141c0c840d0701541d0b459141d4818049204408403100c4142070411070781441201c111024540e03a60414489401a40e8000e20045d800d24002e41d0140f9007541c00b01280354203100040c00a80c0c2c0b5a5020707680700c440c29080151041242c1000c840306800c407072032018a4410800c041d040e44104c0d0304018182d440c54051040d526a940c1d0f1110300f00d510100a03108a9000320501e018145c3c4507070000c68025403500c40202624503540c40f400840c201c281d00a0010110000b030b008801d540105400f940252641000c010000031444064200c61020506800c918211010500c070034030654050000b070f0a010300308648a50b00c0703242440c018407050000703030711840ca585008070210b88001004000141e00510328250b889 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 550768174 1250 550766924 550766933
    0x6040b0a030b0901020325080c0a0c080301080609010b060307021203070504030818011107052115090a050c09060d03080709080318041109060d05060f060d0b0a0b0f07080f07050a030f090e040f 84
    0x3c102b0701081d000c00280b15003201c0403c020a01560180c803140c0050041c6060182c24142140d0318103841c7ca005220034410410682c4c0c000c240305c03003000c21114400daa260b98071041200c0d03a200d0384d00000c050603800b081c08401500110354a2104000c01c3c0c0320845000044982c0729959049032148a0780320040c040303020040000d101404900d09002d80440380002171a10011081500844100116500007200b240074070070b0070054150711410980c0c04210904141020926032054403402405100380c44010542183c4030300e54020050407001c09603a1210b5001d41115001e0890080840c460343c20400301540541c03d03c0d0844920b0407008003803a140140142c0107002801c00101115800b01e81400005040d8403260300a01d9504004803000585080301020000404569006540744d01401d212155490b001d002c11502c003a41c004401d151035411040e140b04651054600c02001d60103280500010141c1006500d0740c0308000c0c0c0c0b100f100c2c494594580408110084801504c215131102c1d1540115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 550769424 1250 550768174 550768177
    0x201305010c0c0302040c02031e0f0a0e031e0a03112e02070f0c0e1509190b10110f06130803071211090a051806040b0a030b0901020325080c 61
    0x5070300c030b0403400200c550b40b90005002c4070b405904080c0581c1002902214516a14290127891982c000405042000f591300c000c03041e0145880b04030510400e8a1203005603030302040001600200442125034034001121030780e40310984441c049000c02d0031420305a10001b00420544034117600d606560f80315210050341021740382008042590515404c00407000031500c90a04074442c04c1c01001141000d91601c07580a8505000030f0241552340040440f9041554a54101d580c0150058901d00b48400522490000a25103046040c3d07001480c0e06041040e150004030225804203498280c1c7d5000002d1140d040e1500001c9842d01138114110100f2000039050b40040c50f004480d030300c2d05d0a41d03005490100d4040303e600111006250700701082d0501d01d85000780e00c0001422042e40c012441d03881c00d40b255051000c01400451143d42c41d55111804c94940d20240303402182c006030155000d0800440340c50003941706440d0420781ca140c100800d8188480c551004044142940d0745014541d50822544080d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 550770674 1250 550769424 550769447
    0xa140405030a0f08040e01090603170a0c060e070506180913080910300b06120a05070e0315060102060f06090a0e07090f0615110304090902030c09010303020120130501 73
    0x44107801e05c80410300250020f152400380000303a40c00100c42e411400c00c0748101d1800b0310000c482400c100324110200d94000e98420380690b00c2000130401003212000e050030030a090308001d0304440d011540d641c0808490303e0443d6803002c16100e010443d140c4072162460071302c6444000d0058182046500004c2c02c180c080c018544204c1c3c94014a4829400d0350840d50b04104000306c1c411210350300400aa10360144503044c00240111a02840e00b4111701806004a00080480e89115a1880003980f118015a44160100c0005040d1030300b100900141d5441c044007039585a00600c00d201c0010010007888030204e0081c0e40003000e081c000c2e07503030b501220301400c02419852814000c01c200021901a5405082070a00100f500412420309000d03c001e09200845a803204000303e401040c8040364001c000c45050300c1001901140303203100342c00803c1c606070030b01c1422600082d0840c000014554190f00036840480c002078800007020741d00403c920540644603c294004030f0342c0e0b00030003403503020f00340b100b26 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 550771924 1250 550770674 550770683
    0x608061014061201080a0510021905071a040803041b0303140310030b090a110609010f120b0612430c0516050a0603021611040e01090501020a140405030a0f 68
    0x20f00b05800c401c1120b10107082c2e10051403580080d10030002c1010901c101004001e240f603045040502c41007040c030340048018042400e0110020390a4180301c035424880c0008031856480707500c9810245440001a030040350f0a80b0008030840c1490f18850440e02e02000326034041e602e036002e42140f00c0d01c20103645d001600c0c0c4a004950300d0b00c000005a40b29101601c03a0812030041c1c403070171142c0d04144640f41c0c507400c401171140c1c02c200030045041c1c2e00301481d80001b1486140190400745003012000041c49204800c41d442100803c40705048440000c00ea80701e0b805040558400c003640c4911590720301448240140010302170611000d0300ca802b04404a468200da1400e0a100c0807280c5901d41441c9001400c1040394107003aa00307000c00d05202c60341d200207140c00e103400c5142105500380340020440a090003004060a1102800941c0d1036402100041e0462002044440d00c0380c40c01500075070021b00311001041464004144c0000e242003903404868016014021117161550381100380c0507610002c84 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 550773174 1250 550771924 550771927
    0x60203090a02041109010215010308070f15020309010609060b120103060507031103040b0708090a0c0b0d090212100606030b030319020115030b100f061b02040608030a0e04060806101406 81
    0xd0f9031140101600b610b40c1d401030a07583d40710100020700701005816108107129030320004100160446044418080d004a001c03200e0505a26103840d140070452107520115002105004240c2410b52100040701d00c0f100d03003040b100359250071384a4140121801d0700c008a95410040021a009401c410b46c410308620300080c18205500345606603400c10307103082c0d98604150f000c100146402802c00c5800240c0700340100300c250616651090107080e14052180c0f8040033056501b40c1900c0358103c3c0c40003507130040c90401c64581a105150352aa8504000550300b030828000003443ea0282c41054241c40c0081c01a40c41d0010410694001518140d807030401c541d45d07501c240d001c080c82c4501005c043e5105034203050310307410814526603040070b03d13422561501a50320000c0107401d401c44140000c0c46110058151901850f00000d001412036601000d041c0c0800105207418903886641820701100488003048a02e0300c030003100f0f644c0c00044a80c005201d0401000340820500641901240040246040d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 550774424 1250 550773174 550773193
    0x1d0c03150112090c08070b090d031d0603010603090308060103110703270b071412071b17010c020106080d0807120906060b090f18011e090e0f100203040f06020309 71
    0x20454a0000f81a12006814181886291001e0080200510030300200f00d084c07a042038000740c0c4141503038a0082c1400815104407495a03140f00b00b541c0c9a0000404a80d160340e5a403101402520206134100d00051002c000628558002c3c403030740303071001031888019040000603542901c545518103c89c25a00031144025001040c0f030309401000340c0004d9451540341c0280e4a00340c0810203641100b4001070700404201030040240340b090310b001c660496408100700c0340002c20311211800da07400090041c271702c0c045044200c010541150201d40202d40c020805030f07a5480c0c0340341e1a80440c41070034001445074008520300c076214841000b000c0c0e030340000009d04141942d8641301140d405a1013503043c5500410001094603049403c890304403019900307c1445120400d0740b002d004c0d01400340d8442402c040c2264045100c008100c0ca01814510308100301d0901c45811044d503d41440b480c804051161a4041a40304401c0c000c2d00d0003198005010300e03c251241c5d9601010750401020421944100b8541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 550775674 1250 550774424 550774457
    0x60607030e04110c060108030708030a09030e03060a0e07080c0a15141303110609130c12090506010e0108070608010b090f04020a0f0e03010603020123070b0f011d0c031501 75
    0x40c0c07400e028103400000d41e103c03090804c903420190160b1286030180c105000c08404111074070102c1c0d90110300100d0010300c4206901d0191101581078110307d4241c4240820401140d10651010344003203035540c1110300b91551000d4442c1d0300e0040c6802184c104200341d20800088034105c003041c0c1c11a116040c0b004101000d5094140e46401616288080100400e01007090010002c4000c41c0348d6001c3d611070b8501044140031414401107030443d640001d540b403030440045446a554144218029103040c0007600c4a401c04e540c3e106000c0c004d0042c480301c2c4000004900400251940883d440d581360220b59078a803080c0f060894104d001030640007481440c800707405544620090103428203a44803400c0c032401d511401001d501c03450a60034000da00d4100e0500c0580c4c1c000018611546100c10042e011030503070741800c0313241e008148004044581d41001e01c868241c83e941624180c1d0500703044244030300508820384001000075520302e02154000c2020400540100e00c0c014200035040c1003481690301c80747c1c1c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 550776924 1250 550775674 550775681
    0xb0d0507180203011d280212070e090f0c0418050a0518151e0108030703110a0c0b070c080714040615020c0112060906090b10020a0506060607030e04 65
    0x1190590000c580c01d000a2511080418032500041021400e540c1444103814000d10310030701040c500e0120b40c0006260030a0302c89115148075010302c10340d40007024410f049001e03410100c02d0002013001080092032151041c02505248180241201c4d0f042d03e40c2c280007441404040e0031240d00300c0040202040c9882c2c400582d030234031042d4900c0061071f840e002c2c80810442700080c00148454090040c1c210240b0800140d24107100e004030f180c00140d403a40d24240f1644540c00d0500480501d500c000016000b00200103030130024001d031504407400d0341200400e515542415070040c640303407100c4801c3c000d544010018210380c1c5d00c51000c2840c0c40f42c44003c6180713001d480d81e0001c0c0c4504c10036411100e085c03c06004400013040300420800016503a028041d4561240c042c5072810031080c1d601403042c103c5943c00c2003005010504003001030350744500019002c0c06c81490501d019180c1c6108695000d4800100b2181c1680c000c805003016803a85010040c2943c0407603010703020020312060000007640c4074403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 550778174 1250 550776924 550776949
    0x1020408150f1b0a1d120a031202090306040311010b03161401020102180d020102100c120612120f03060905090d0f02030408070b1c09060b0f03030a0c060902040b 71
    0x6003525910301c2d10407489004a40010b00b4140c618a0fa1404200f00040d150f0646a4146180c203014900500f080140e80c032070310311004103961200582c01e1921140101150100d0760a000e40e80720b140300b4083c40c0303980f01a8403a00348203c0d003582c494000100030038442c1d201824000705010000c101300e44d540f00080d141c0102e032912281500c0c0d41c404100090010a1944492020280002d41c1003e010280e4281c8890b1000e4650b80280c4150012a045a10a02070244a030020641c10450000100c5000b000d550014403500202441e1503000700b90100c04803010300a0075440b90707a007030000011200c211400c0c0d604980d54018142c589030080b070074016134010240304408410080506141428004189004846002c019034104220a20048201080725001d80390030f6100380d0380e1111400e24007803100d49418481c43c051454002030208000b4190822222140111081c032800a4002d0400da224800c81c030050010400781454440001c8050700030000e80c0c0d0005200141e40a00400420000301c1c031307078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 550779424 1250 550778174 550778203
    0x60d020d0e100c03230907080d03050a0501060306080a020d080c0714130608071a0403060e06071206060c1401020f071b06020636030a030212090102070807020d0501020408 75
    0x821242c800e400c5544900d91403030115250502224030b044103050900c40c0d0b000900c0645a0117400001c102c40810440c15005190a804950200c00b1100006000b40030580c0c80a104500700000028820300c0b034001e142c03c0d11050700c05030000d01034030f60070016005400d01049441c044c09001d80680e001044c003002c00103140083c0394405030707041070b03041101003800311060b01c5055151030400c2c8041c403030004401084c1c507070441646555000d00070710740740340e4000d507840140442c3c24008104000500814002d004e071000b600c03180c0355088170100c840c1c10396000d406410006035050505074040f9001d0300d030310200981c100c800185044115070000f100c2c0e62040d1030586240c4440204810909546840e02e0001c0c1070500c05061a801d003040d0300c050400074000c50900120b8500f4490900001032032100181c1001d00c1e084170303038461700100042c019402016944a00940708070000340e00c0c407818000c4494040d4030040300d600d4644941d080010080f1400c0342500c0540d428400403449080800039003207000442c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 550780674 1250 550779424 550779433
    0xd0507060e060406090e25053001061209120903031b050303131109070314091506060f0d15090e01020910030e0a060c0309020f040c0f05090d0804030807210e060d020d0e 74
    0x22720070001c6013441d51216600000c40c0b812200102c403c0c0c22030521b040d12503a01d400403840c4100980f41000c0c1880f107902400c0042c04281c1135001c181c008200e84210fa100b6102d85031003205520005c5140f07020001c1c003800c42d420400006041d00e0b04000c5214102e8400c000000740e04900001041041d10210391560100c2e80d581d0307500d0421040c25030101d62102501005100c1c40103d48556204006c000c1e040702c0c092075001ca040915149200250342e90380d51600ca04100301000c0d0121081101c2c0c580c41004c940a1030016644144a0180212000c50801904078000300c00704500c128004c00d00300f1103440690040c100c01c0d800042c968002c400c00e00340c0596002c141049940104100618008400d0f48140d281ca02c40b0f40131150020814140800b0341c0c18510f4940c5005000b06800c203011410051610800003004420005035001070220725006a90f511524401e0704820104c1907000f10709540821203a0780d0302c00300e40ca4020001c0c0807214083c1710150400d03c1c00f080113820358120510703543d1680c20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 550781924 1250 550780674 550780687
    0xe0a0b031f080f030a0e0d05060f1f24301a012309100309140a020603131b150e03010b01120f0b0d0507060e060406090e2505 55
    0x5080000002502c20b60003d44a0440310024155592050b1a041c10074001604000304581e030315034814001c91a00310040c0c681c80d180090b8110302c0c80c40300300e8500007070301c410041c50404018000201d009407001400e030915060b045081d42d6440d103061064000803c0044402c990011001c003c1100c4003080441050071840c1d10300740098140c903403200c803207034410001510f101d4140c0c1c0d04c101d2007080081c1c031070f07280040c1e4400040034040611030401300c150040c2d14030b541e1034501d5625074010b00600d0b0240460701e901c4554040040c0e101d00424002a510100910224525051603101416818072400f011008801d030040005104070256114880c014000000038040541012400c10030b0b034801ca008011603134080c40040c21040c050218500c05070f50b41c014004ccc9082982d40080b00f680f000401c0c10703007840880d2820669600150046c0c00005100180c044c000d810404c2c181c0701540c1e0181c8600b101c0b5420051540d581090042603514401d800d450100903804110714074410b00b82c919a5510b0b550035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 550783174 1250 550781924 550781971
    0x5060601030515010f0201090b010815010e0103030801170a0c03080903060f0105090a0207110a09090512070218071803080a09050d0f06110d020c03040f120308070e0a0b03 75
    0x440040406041c1401c103002c00084141c40507203c020030300700f400d0069061540c62002c9004140e03000006240a990000206070003e00107042c0c0a81c0140c0e19115180d03a0b01d403811013009200a00c80203000c0b40302d2400501c4415180400750010700038541c2100c00240351615080401d0003940d04c280c8500d0f40c006140a524117092045a131b108510725140c2c0b00b55450440495000c481c0104100c82c42980412204108401840c2d4040b030103400400040005480700c519000504117a40c2c100d45034822500c09000c11000395007076481050300140b03407100805032440c0d94440048010300324410441003c00443c410111710441324003550084039407546422030054041c258078820b400c458442d1924404000c0020f40c0441038100007907100c500401e1340e5900320403203a15400740c603d002403064000304034204c05c603034004081c002726019075504180c1da941d102100c1c01001400400503000424400000c1d111a01400007507075111409001c40441540e9658010029042070381d42c242544070b06034034200740300e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 550784424 1250 550783174 550783183
    0x5040302040e0c010e09060303120117070e0c09060d02070203010e0c040c110304091a0d0302010b0103050c030103150e070b0a090f060504050a090b060f04060c052b110a06021605 78
    0x10002e10010b00c1082c0071040083d100b40500084184554000710005505440503c10354441c51103c40c114510b550f11510003096443e2294010103440c0f09000707000459041501c4842d01812a161900d490582076005014256100c4055402c0c0590200228801a10300740700f10f852001c140c6000d4014020103208000580b9442d40389901000000004400005804412501215107200000401103c52524181005003042c0b80390780c06200c01922030305040e010341003954940e200b6a0100403564511003c100780d80000c0c04050044102440b200800c94400c1e40304d8900402c5600031125007564840a0400a03448585400005520640200542c012540c600c502800d41810580e0810381004045211107005100c2c0008a64840000c0509034035010101c3c0c500000c0d2000c21740c1e45649840024001d050b10000440c0c43c3e20490302a804084000329500780b0207001912841d8035640c0c642c0d000c50319010f00d0300400d40c0c54043c1d03016520010b100c620091911240b14291b16040c1d51072401c05901300b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 550785674 1250 550784424 550784441
    0x3090d09050a060905060c070317190f0c030e0112051503060907030203030304022e0302040e070305091b0612010f0611010b0a030f08222d0605031806070504030204 72
    0x544070b0500d082c40050740020080301900c4090310311680b1406641ca00d6440c1c00f03911341c0b01034094200c0fa03584456030100707103004213040c094424288008100261007104c1140c0f034000044001241480000d000034403402c034a00d04030344140352401400c03541c14001812100181d0f04074106e001c101001c800c0a05062000e9a40803c20707030081c010303c0c0d103503401207034403440000c10003480380e24092840303041c1c84003c0062003b400c4080b02d070b80049200644024000754000d00078400a6407414001078900c070312a01401d0711802501001c0c10b1005079055401d4204e16044842940c000360070710003084036407108071046008001000030310603e50b14040014221000004010302c107131b410445048800d07201c611402044a0384130010138400c0e0328900300480c01e806000342125200f07005032006084030307604450072401e4075007206549030034801d8240c0500040c1e117809840362607403d0524003080140e00800281d42e1280004015915038455241901d051180486081c0c010800c0428180150304045c4500602d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 550786924 1250 550785674 550785679
    0x607050d110f0f03071106040902040303180905090c01080a0b0402030c30130c051206040b100303090b0904060b0a030221040b130303181406100b0d0e010b0603090d0905 74
    0x4280d001ca40201d8130781c0f1488002820311200049030b01c415844000880740101846503046454903108c0ca40144400b60240c200c00d201c03540400082070301180c5214450291403588001c180d50028840159190600101480b407540e598402c03a0f41c40d51110b0008510550000b0009551409103503202d40e1b460744c0030f08031402c64864007103481c400c50200346c4d89681c000e181d0b095450850b01841c0340080483d5a19080b540d0840b00d0f0140a81c0c21800000d28a40900c2c4180c0500101d81c1e60802c000924800714440900080c2484404200c440403660043c003200d000604085039040d299010421140d014a19074030000764002442a8400c409181d15401c0e06040d502c10b00950410f512032220601d00a0800042c504105103a101014001c0e400710b030f1001190010a020b000171401c03d1104907031100185c00312030083c400000c0d80130041e42150801c0d150b90ba88014107001000d01c50300000e01c090740d00515550f68812128036640d0300c05000d141301c0d2000c00010300f50041141001000d5030300c0ca601660 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 550788174 1250 550786924 550786933
    0x60c0204240b0d06210c170a030e030a050a0b1806010f030204020a03091e05061806311119060905010513120803060913200607050d110f 60
    0x3a9140603440800d000c0710311550740d01c0e0f00c3d0880904020010810b40c0d100e40c80c9110360035188014090450901484a4001d40c1c150881980d100107003581e20300310602d040015000b0380c8660300024002c1c80484640c05003e03040320320b50801a0349162900e410540c090340c0400400782042018803100144a98a41812000d800903514089400c00001078900009215580100d00001c055120f03034024085140c000c0820000c5060b814070703450712880e403501c0c20790300d03400747c100003a607903010310101c1300d0600284100514541d9a1404036122009501d00c01444000c0041103040841d80c081c5004901e840c01090b840c1e400c00d40c0c9a0800c41c056910300400341c00c00240f20002c12995400c020124202c42c400c1c20f000369202e02c00a100c05c510549a0403840c00d100c4205169820f1251880c040d5100b1202600c04d074000c0e803640d021105000d0803901c00184051403540c5001c02c8140c1c0c01c04d000c3c100105c06407036203040002030b5031914140164800c00341e000440c3c01007042c0030b02d1020085203584415280140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 550789424 1250 550788174 550788221
    0x4111201150c23072409030206030c070f12051207110604062c0a030912080a0c03051204060b09070513090c02031308010c08060f1305040c050a060c0204 67
    0x507202a20000c005000b0030100402c1c1c201e00d00f50684050441c0038004165401c0701e032601d0196040d5060030b0825020303440c03803002000120b80900260070503282c00030320f500e0843e03840c00b480403110352098100329462089000403000244880b039940b59a0180358442c151100344014200740100300081c80001000007010341040600f00c04034460750400e1b0002d03408a8020304a0313101d80101044034002040c101c880400e440818000400c904000d00e110f699030145d490743d605c00007440f01c00e03180c802820503a03007005520a91401090840b451b18401d0030403a0415001d0703002c0030380c030340303c1160700345c503d40d4945a98a00625001e0145507110350030b42006800c012050b0502c034107c150a000300d010650b07880711070341082d074000c0003030718004041d1410f542681c54031440c41034040e1900000140110f080400030400c00c0c45c25507010035000b00040c140c5909916240c0100019040c044e00645025003042000b00b140d40307500c039041c405040c043c0c444400b1030030144140411600c42444005e041d0000c01a070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 550790674 1250 550789424 550789427
    0x251509060e1212040e100603152c0f040c0b0a02071a090301051009050a0c0f0c02010314090a0302100203040b06101214040203010f060503120c0307020411120115 71
    0x802400001030390a99002d588000c80345140c1104103040751a00c140c003180002c1c1c1700300319110340c0d0300c0759118041604000d0380d588410307015210341c24203010041c400034000344600698440c1c1c1460b869260f12055407d1030340f0094400b40b84c4402d5aa500001804400308018803100700a031070000c1541c3c0324000c3c504806500000c0d100c0d00c660060040501d40170850b1a1040d05240c1642c584100c018001c100c54241101410840d50240c800c2080541c1030000141a81120748141d680e4403046813103500c2c1010510500321807010307645404034140340e942e0b1180044610b000700701a1051610703000411030b02c9c0d80e605001c1c0c0307400d08500038a07444500400401c030000714180c0c405c13500454182c8100340600003400d001e84451121414902202c0c0c901014250b241c40640d429500170390082c1c000300710f60700e0b020074894140c52050141e560507901c0042c446600c1e40100303000304001008901564144a50b69000505540000030f0f0b90a81030408100300c550b061340c3c40032150041941c6104011001c0e0300030740 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 550791924 1250 550790674 550790687
    0x90103141c142b0b011806020d030b0301020d09080406140720060c0d0305060114031b09040e1204030c0b040602120a0c050a050a031806050403110325150906 69
    0x203218540610209018459080f009000060034155540340b145580c0c510491100a050b451540d60000c0da12580500c203d521190300319090350000e50182c20742c04019a029009002204070041d050342d070030480c2c0d40c2d80c1d00c031504c580103006200702440c1da9198902040108022041000011804400c000c0c2c0c8000402c01040321510440c107941820751103410100142d114055103120010380c0c028600c101c5419507050348803c0c0304850988400900e0315000708920201e00088a004103030705c140e0f0491100f2020320102500039110010008035505001400e51418000d15100d0f610010300b012900740b040100184074900542103090300b250800b0b2400340b00075a9102d141840141454000409041c201e215690380c019040c0c100c421906076082da46041a034030010706100b82d00040480c085000340d1a41d46142104584a66544504282c21900d440184400318281240d00d131241001c521070440020b00c000324840b00c2c002c00c40980c540380514800c8250403114200c0f04004000d1402e01189404c0036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 550793174 1250 550791924 550791947
    0x100606170417030c0c01060e0c031810090602190203070b071d06030c030a11183706030f06150804021801080a1407080a03080a0b090103141c 62
    0x20015094445040c00110b0b440900d0501c0140a0b001080020807224080144030300e060840080125580c1d90702240391081c0140c07150356107180100080348200d10a02001c0c54101410f01c140c4041a00e41150b040450349802021203426402003411400d407000082c02c0e00030600280050751502600b9604c41c1d0304110000c000506005290403104015000c41c5155900620013403c141e640c1d0419144800d0780c1e420496039844224240400c1d165500081e1040c1c81d5546030000e41c0400003501102005401c0944c80c0c001d1242c4800311500c0004400c1d4810401500703207040318415601030030400001d094820300c405251a56082c6076041080d40e001920200201266141c08070840d1607500c0025041c0620b090040072100c8500300102d00010081a0705030780500c61022031007403100d500b034506c0d100c0190703101c2c81c0d0a503003200c00820302090140d00d80c2c544c0010794140015691a054002170340c251030a030000d8a40c0d50303407524040207600040000c440b41c100c0442420311111902c0c0c40c010038107680074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 550794424 1250 550793174 550793207
    0x721240515040e03043804090b0f040b0a0b0901120f0608070e0c0301090b0402070c030303020d150f050d1415011502210903191104140106080402042d050702100606 72
    0x1100031855603003a100405440c400744900047c1d50b030355039a0324400a058030703143d0540710b01001481c070700c41c1c2e29041c0f08541400030064607004107030740360000d0183c49802440c819810700500180c008607018031442150f04c01c004034000016528142484245030800c1c540001d012114240c050081030341607001544d0443d6034031007000c5649000310000ca4044d00401a000b1b2010b02ea5010110800d60507401030102401c1e80e0904100804080d0241c60740c400151044c0d1400b90203400e414007090410942e1520300314003e1030703001d00c45203507111490304e00040303904d510070b50300c690000600c1101d02d00c0d0141411170703409100801110258501603d00d84801700e40d01e0b007800c1d1001402c941143c5051101e004190303d60300500031444c0307131406d02200007407409400ca4400e5141c0905492440103d0310241d051710341e01e070b0303501da099501c0b2744c20b000c01030000038514140c60240c180410010042041aa1005603483e1070204075130a003074502030304c0d040d81c00300c0814038a401c01c9420b101e02e43d402240f00c000310060 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 550795674 1250 550794424 550794479
    0x6030602071523040f02011b030801080c0105090901140f09100602120a0f0c05073209040308220804080312010504050c120a0b030a0c080721240515040e0304 69
    0xd61006807030700004c0c0c14904908c80d01450303066080c1a04032001074100c079a680240c4007103603d250011101841108019a44078403c20010710000e0764038955401e0040019201c208141c5401c0300080c0e42c004c084034800c0801d1600b400c240b01884d0305000700f45c3c4a01c8a0f640407420000c07408009030008100d41d07800030070041d90100c0074003070210402c004401024a070700030101d21415600900000c1c00c000c4481a900da880d100c61850034101449010320035034150355500210b0700e1311a040184012100041d40309840044030400109200030f000b0030040c00320800960341c5007103080c1001c2c006801603001e0752281d4640b500704400c00f4506421140f071030b0040b01c6824180d90750f10344228002c00c6164881070b01803007101c05410400c000701000005840f107039400c41e0304641d07880c00207902d074044483c0300c860728a8902c10b11000080d0410006070700e0302100d05120b110f10a0300c0c420001142e00c200d504904150002c1400320260800d40f183e800b0784000200994070b000e050030f80e00d041e0130f805d1080100c1074008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 550796924 1250 550795674 550795703
    0x908211306050a0f02040602072603040b0d020f030705030a0e01140601050f070c1d010e01050310020a0302091801090c08040b06011107080303070503160c020d02060d0603060207152304 81
    0x2070740c850041070711901400c64031547ca07400001d544003014080ca2400f000d10745440003c0d201140110800109220010351410703042800e0082560881c803134004405030203010342c0300b401c0b0800c80a1817040714150744494681c40c1074050030041c1e90034818040e099901d8010111554003c0a10413076011000b070802766900c0c9038050307254409218200c00a03285069254011072502c802c086451807202d100d1b252a00030366200d403441c0301c4e0800d080c03040c151b00d5406250b060f124080c05401a0610440074140181895030313440100d10310940001001540c502c5000c014007030040300d40b150090026881c03a141a40d40381070f0382c0f0203d00e5100030b807109042c0412046c1e204071500e010041613002c2e003003044c141c07030300c90900e104090700c0c603001501c1e4811803880b024003908010b48219150210325400910303640c4107040e503400703020455004880341000c0c56201e00e4044003042d440d0004090091203203018503a100103a6100b40103c0b01d480040c5010643d10f406801040310440b00891740081e040f2403059440c1c81d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 550798174 1250 550796924 550796941
    0x13052e050903010603060608060603032502060706050f0901110906030a0509010204170c0307170309040c0e1011060c0307051902070312081806010803040621090821130605 75
    0x1414910742d5041d820700c1c0010040040c01e401500442d040310007105c0d00fa850340c600705a100c0c061001d01d00220100d024030740901f1143c0e00142d0741c0503030002c1c001c18989489501d981c42920411203401e4410b0880c01c0600c480c0180074811000841d41210305a8101014900016507a210140c4000c420540310030100b24840029411200103282c1c24a01410a1a40c0322919807100e4040e200ea43c032038081d000c80090900114400b41d40e5001b00071010314a01091001000010712642d00807500708441d51460150f9038a07030f011912200c40c400d480d02e0003407a8140815600e4814010180b009615080c01440003807a001010b440740740c07100c1d169a01a030040041c0403441c5c10001e0384044c1c031114a1440300184290404000d80c098000ca55818841103010301c40a95030300820303c140d02480e84100800c00815110b88040407047c03100c445032010441c2c00c50807980903240b400c3c00660702000000740c901c00c0b440c3c0c88102540350a440a03000000791034903059018610602503005085a41c41d80700142152 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 550799424 1250 550798174 550798177
    0x18051f080903130303090303170c0d020711120708120a200132070207060e06090f06280804050703020f030109020a03110f0f0603040f05100c030213052e05 68
    0xc241640001607584da036030400500e03503600741c441038001c250940c809201010038030756413074410405101024902280410120004d40c07103500305480e200030740950041c1a50781d0f08642d045074a05003000340322581c2000581800c1c1550700150f40c01480003082300f0710050350000000075001254807101c922548010319018050301548403800440d203003d8090300c0f60190700f00c182c6206005010060b1060340c1c1d440e030040e6583c0545001e08004541c0d03c0340c00410501e044030040500e91409002c4025045400001c55541c3c0c100d2140e2449c694215078410300810341c1069a0071241e401441d00740c5080c2071640390079480b02c9c11800084e0041d203d01030080d00c11389094010b4100191f02402094030555241071400f00742c41c6c0d050405220340c440d002c50b1200340c0f0741242c1800100c540200001d140d034448d0743c0c0d600200c01c2c41100c202c801d405810300310080c1120074801e5800c0341c1e03002d8601599a0100c9003009480e442d0580001e44210307958952411001203100c0d80030360400c40f029504007000704001c802d4505 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 550800674 1250 550799424 550799437
    0x7051002120d090309050d022202040504140403031407050d05360606030d0512070c150203040c050a081c2a0b0a020c0d03270318051f080903 62
    0x881c00002d120350804038980d20124a8074005e80d610fa181c1da4454041041c690810b141c06940032904040a50715182e02d141d040c1c8102e03030007160041c90a07541e400807805403400c508858414aa80b00c0801c01815007500805403d27503e0021841060b113043c5034060f10a0045094030000c0c02e544000003807540f082c00e401e1100c803281000100358101440d118402d841c03401c2d6080d100641c0285008122141000a5000210441ca4480f40c6c02d2840440c1d10480040e401040c03c0308004001400c1d070041040080c480700035050802d400340c3d0303d1800e0308100070300c00081c0d84014002c50310280c0c10090b00f2004103010103881d10103842c00803801c0392000222032520001c140c0d05c007000f20b015001c0500184035010684580e1240d480c004030343d541e08150714120f000c1c0c0c1e04405101d8000c00d03807224415110307500c04038101d6080301d00c0800d54001c45000031103450f8a010b00310003065901c0c0e156240ba42660205e8070040c8400c8a96882000003030803086150b8003400100f5080c00141000b04456040074001c1d11030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 550801924 1250 550800674 550800703
    0x6120a090206041d100609080304090902060403020a0315050c040605090f0409020909032215050f120103060603020102060609060310110d0e1c05040605070f030309051b01030e070807051002 83
    0x42840c13924042c440c801029180c0c01070052400c900000d001b801603a04004541c0174401560400d4640001c0c10050106030408a900141c2080007200590301e0541e100c0145024441070380e1008000010030041320400703030600742d03a20404d000401c0100c0e8000300301c2d240c0c81d00588100003030795800000700f0094a0002402540013034180200400c2c1c0314004042c2c40004440020411110410080010748071050f00035641c0701c41c0300c5005101258010002040c0344902078400f146031004048041c40004003c8e00300710b40440d00c1e148104155a0304000180e00510300301c65900039030800c0800a40c0d82c180b12940d9480243d11204484041e492a400b41c4200a40c1c211042c400810310000c2251124507040d4420800e010030001112518401d00039501910120380b105882e00d2142d4035441100a00d00070108c01b0103841d4101440080c200b4420900c1c004001c0a1908942d0011030014050311041003451040d94061141041038240001d034050882d14107440e01c80d01070300a02d03400c900704070a0101d03224 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 550803174 1250 550801924 550801949
    0x8010e0c0d02121c030f0e120c07080601030c0603050604180b06040207080c0c210a030e060c0307030809010c0c15020c2b090e15040c20061506120a09020604 69
    0x800300ca14100c2442071003145d940410410060780b9003c01103514504580485a012000020303003140410010543e0359004130488110642d1141c00b0340c6400c009030001c44501e49010020813541307826028068100d80211810712100f800c801c0e1070b02e02c2c500184c00103000d4000c090049401521194101c480642e003104100c0c0c2d407443e02c5000c660786c98003922483c41c011103100503070036421a09042d17051207901c005006002c9183e49501e0441e24524459080750344640d040100d0001c07243d007040100782003486521110315030320f8100821404c440c0705880c4c1a05204013054418002030750a107450b11010302c0c4050040c2c50f004503007050303417600404a415840505400c9150148801c00042034007000301603a0302d02511640380c1414100454041c0c880c2100b652074681130b0308444c035094101680d41003440c6000ca2091642a9024800000c2c401c09408250840801d01010314201800f00f03000070001e0301c6d298902050010030a001880007424450210b0390740a0900442d56014220750040200d05c41d001d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 550804424 1250 550803174 550803193
    0x15020409020a11070807030506040312060f03030206040605010819020d06060506030c03090106060509012c060301060e011e0c020d0305090a15030e060603071401050403080307020105010f08010e0c0d0212 89
    0x60030001010043c0c0c803040c800e2030400202500002144816240d108000d04440d848542d0159800301000309580c00c0701c0e480d08004140301030003907a4480107500990041c15581454184102120f4040c0c1202209811182c2c0740c0e9103080c3d81c0c4101c2c11007203505403085014149035051004c014452500003560083c000420b00200070741c0310019601440344d50008010700ba50f2400165054402d8503c0240882c80c280d1403031200c2c0342c070310a0802c3d501d00c0c003585140c159040720000035032580c000d801aa01040140c03900c0240c9503480b00030b031404e0303824229840826040144010b460100f00e214000c0c03249001c0d003042c40406100e40151a86441c014041d40740203515006018008071901c014500060b04e88043c03120340070320000c3c0160185202a000e0301c483d60414098802c61030400030030b01d0511030104000400281d01c0e00080d4400c4225900000d4554180210780c040c1080d148d11900050717051a40c40c091091001c903502084060131280b0740220310031031020845031465000e0480b642c0c042c0402d41c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 550805674 1250 550804424 550804427
    0x9060f14070c0e01141507030e1201021b06010b04030b280203071b0c0b0f070f0c2405040608060d0803280e0303042d0f0510051315020409020a 63
    0x41c8400ea502d805104a643d81e00c8040340600702c080301d1741981d17200d00e40d4041c0103c90781c94030303000f810b40038000e01d00070b10a0410440828036000c1c0100f03d0b402140c0d070000d41245400c00014603910749250040103060706514040041e505400303940405000d8540c1d0b84042058a00c0c2c0d4001d601901c030020100940e0300542c0d1074800000d400864131040441c43d1040008003032003d11080f4a03030141d0140301d0050361424513011690f40d810890305140b001c0d030200700e041c012a04101520800c1480340c1c51a180503170508001410486103000e541e00c00341c05004016409582240940302a207081d440d1890b1071b40c0c4c40c080020101546a0750280080000000788800041481e02080d0b091040c60080d401d500c2c080303031400c000c60714950040034003031300b0500126000486116116a031888008101712070501800220800d10709a0301d000c403000011404800e00f005801d1007114003110044108019604d000e84140040441d034000081060110103201c0d008a01c280d81074030060001d031203045440e400180c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 550806924 1250 550805674 550805693
    0x100e0603041e1403040914010605160c090e0f280f08070609030f030b031f0506150c0723090c09030f0102030106090503010f05100e0c09060d090212060709060f1407 72
    0xc20490f28140218111f004510002c064103d4803550345031032600041030744562200508101c100c45007091030000180070710403400b03900d020aa4040107802d04100d00b080040c030381002d103107a680440360340c1000381110710148400354555513006a010300b100e029515040d8164401d41c40f00810b01840c0400c41c409140d07201c52000140c0c030b0140c13003c00514800d07004040d900c81004041c15241266550348803503814054101c260803080280c10a00107404205c1003030f503150400c140450321075100c21410009541462307a10303c80942440700005811500c0350101e5100c020040880c1d901c09000226034480d6242002989510000d200c0215101d503100d07580286451601e100e41403003982883c00d0b00050609038441c07540102c031183c030707400f400314a820903403030190307000800f00c1500c1c10040c02682d405840300002000005942e4900190140081c03040111406101001800030360000c010040d1706904010343d401640c01030300304500b400408280880b0a0409140d030f0300e00e00741000c1101000c10000c0f01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 550808174 1250 550806924 550806929
    0x6090507050316180b0f09030d181707050913020301050106030c0e0303130905060a09050106090f0b1c11040801061205070b0a1b0c0503011406100e0603041e140304 72
    0x724900e0218031003d41c00c60316040d5441d04071202c5075070340310100180e42c0b000700146540383d0303090003250074800c0220029061203500c444c4000400d1083c0030303003080b40f0f08203290344000e03200181e00101003104610043c2c1e960341e554000c0e41d000b803901e01e01041082c1a44510034054550003002804190f0315040004d01810007966084080b840c10082e41510b4a0044103541035a0000200301c0f0245d441c110b441c401030310002c0e104a030000c1c2c40000204000480d8000c80b4080c000985a00b9031952605ea445101c03807003254890301000b01c05000507021300b419906202c0c0b80c90803220010510800781c0c007445072144210782c0b1843c910340c6000c0c030024190300000344803800e007809001030b582406d5070ac0c424081e851042401180020741c9902c0d500902d02842038503100100d000b142c1d01c812182d1a94040b0f82115607000c1c81041d0303510400100030881c50300c002002607101d2031740b070006100400c180c00b040c4e8a020107070004040d0b0005031002c5203400c51040200100d145c110420102014280040640303c0c0c1c041e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 550809424 1250 550808174 550808191
    0x3040b0d06170f07212d0822050f010c06060504021b010c0306030308070c03020a0b01090203041416122108090105070201060510210203010609182a0201060905070503 73
    0xc0130005175420060340c401c1002c06032211039030a1000541c0c0c0c0380c8000000b81d503c0d204500e40340784141402c07a1a1465039204a00c2031468941d10310101c502ca110382d00b800a580102812803440500854981240c000c81504003801e100320240350707515000b405130000d03401084e00580f000c100640e002c0b591501c4001c000c8171102c000c010703091446c0c0c800c500340c0b445404042c011551601c04290290300c65110401818040c0c41038030100046a954030040090a07070000000035008404e11041c040c0e40400c41401c0741d8504014604010300c1c109418009441d4402c000ba003003090020b410500000c914000e07a01032404c4c034228202041c5400191003128241c034290030729840c020000f1545401442904150303900180092100c1306000c9007222015248911008905031885c4105410156030002c1c6010703001315191010341d00d0511004c0104581040042000e0302c0c24100042001d030b00c10401c08110017404030341e40b2280c0521002c00c2e409031545900c032480c0389160004106a2507805006503003d000030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 550810674 1250 550809424 550809433
    0xf1605190f0b07030507121106130b0a1a09040318091a040b03010f050106020c030d1404090c050408060709050a08030c1b180c040e071103040b0d06170f 67
    0x250815900c400d05000e41c034503101510005200c0800b001014004191191901d1407030100d2135640c100c518851204c00c400410b04c1040380400c058024410560f00840864a440711107240752284981c0a01c00b9010025840c0d480c911442e0840320050300340c1c0c03040000741041c2807a0030a898014140c2c0d6140f10905040c2c031820070301080f4035007140201402c82c00942d101d50300301c116403020800100480c0c1c012646c0341d9a6103841583c0b80b00513001e0700b402449950003034a02c0a8200082c1400d02c42156062003c03c513070800c04003203103038000090710292000e2503c00601d8200c1120706803801e1103540c00c504414840d4800b0001e00c00c0d4000102000e9400640748a034581b95900c140b5643c81c014002f460074a90400d80044841c881013810403800214014488440046003540702e000c4102e0582c0c011088500005085c05445c06118000740c01c0105883c0c0301010016104c04142c89004a0150b0340070f00400050800401c0e02030b4000d0f1014007600000b242d0f001d046080d16581d6a00040341e03000c2d05004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 550811924 1250 550810674 550810699
    0xc0301051014070201030c200c03010c05041a07020607170c191101180f06050702040621061e0f022701051608071e110604061d030f1605 60
    0x4190b803039074950014034248a0a0100c0d90340150050503001c0382d16402c0201c14815038681000d0441036810042108010700b0b90f4030486e10606094441c009040e2051240c204020801400e140906c84001414410035684804c01407000a070780d0701c500600036003c454900000196640e52500806080c0d002808485d400302800001815001c05020081c05140d001100c2001650207059814000c0c00b503c18075019441c0c5030480220340b4041500042d00207040466127404600b0a8452380000c0c026804000c0c003030311088000c0e06035400da0301c40010105510740c840c0b0341031a1400c0380c40340d0000070401410f02a0025055605000350040c50b0a08207c0d0501d188441000381200000007014034181e40304e61820702c20100c0b02007515081c031002c40349160304111500201c2e0090145c02c4552002d0500a541c514440c10100002080c1500051065400b0007080103d41d4000c07000f51402154190401548642d40740020308000c0342118807800307030144006d51020300c01f902c0381c0801641c10840300b0592502d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 550813174 1250 550811924 550811927
    0x2072a060906030506030f0102041401030e06090a121b030c2906240d02030f09010501080d0e0f09010906150801140904170c03130603090c0620060c03010510 69
    0x29a44600000310748500c109000d218480d41255a204001604495035a9180d240e10360032030344194032000796481c805000310401c0d039143c018010180d400760300404140c203102d0389607501c8201c0350500030508401d01144000c210f01607032515a08002010414485140905011f0b141c0301c041d41040311000740400c00008040c104a102c20051040c0c11000c0e009070f544c032001c4c0007400440d0306e458001003864448200b50744042c8002400480b002240150322410b1900c100d8005034009000420264100001030040c01c0c800209011800c40e0b41c41e003034907a2400040410050a60300c01c50300d40107060440003044417001908103804a8101034400e14030f82c4800300341190003c40a000c0c2507a02c0a404c0e0b910406460310f10700326030300176001d950384501c440c02200c071000441d0702189000074180c0010807031071242d41500108200414181c00c05102c080d0b840c1c2d41e021541423060040c03400b4415681d00f40c101180c103290b26034001031980000c640705418110780e050003940091061a00c0b8010340c0318541d0016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 550814424 1250 550813174 550813253
    0x30b070305240604030611130e07020d03110421050601120f0f0804050d030c0c0b0f0d110903010213030b0c0915090301180b150f0d1103100207 63
    0xd200800c580240018a401810a91014074075040c3e4400001e00010011030114418204401c110400096a410001c40408650a0160f00007030021000f01d0801240d02e0300440d112940d25910b01c0c0010b600706114a00c130890703011741d0304140a80e00c400e1401400601d004c149440c0170b6401032080b56216a038a58034880003490740040103001015951820700001c0003041c0c4200014410182d040c01e142d128004542000c05800d420390004466940c88414440c005980c88007410071140000d10384000c0460b420281c0c07050a144006030790b51680400d25a580441c2a280600c00040c000d5681d024643c3c54013300029900043c3d031485003034008100030810010883d948680040c3c5051001100c0100c0e445c00345d00301c8e00c4115010354951880d040880703003031781c1030f80700d1a0b20a0b1640092410803c10300022465140342d203a0040340c61060703940392666001d507491030642d030141c03440506003000d8020ce0b00305010800003400e07840c0040b4005e030070080d0030b401550801c8044079040c40454004a19030851 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 550815674 1250 550814424 550814431
    0x30b10020703060f09050d02030a0f02070b030c1c0f09050111041412010b060304080c010c09061d041d03070b16050d0b0607020a06081906030b0109020313051204030b070305 76
    0x35074000442040054000d8101d02c1e4100340c0001c000901d600d803a10352034140f4521841120041e007001448044a542040704505aa0100c0c40100402400c010006413288030107010103a8000d0702182003030035401031000440440e200c2000500800302101d292101a200780b134401c43e01e40d405c04951490114040e001e44040700c5074940c95040d1000204140940100c24024032100d5540761003550016455078002103004a2107600d0b00741d0b81d82070b82281142125400e468400802500c62410800d071984004103649002d068580113800b43c1e261000200140448841d0800c040c0b2484100c00f201c2d078020000e08041400740400350040d680f02155040760721107004400020038030500103481e40c1c658542c443e41c544100503042030718008050b000282d100041e91700c0840012105000c10200354a51081c440500c0800c0c20144002800c503503600021040500509039142c0d40440040c896012110310014110303048802d4920a40d1100b041e00c0080d44503000c1561055008070100e074403181700b44079041c030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 550816924 1250 550815674 550815677
    0x2100e0606090615162301050603070302120312010f0602061e04080a1101050906011e061d01090b0c151012020d11100e2110020c070f0e07030b10 64
    0x1455440208004041c0c3d280342000310312102c180401401e042d419808040030a0140015031b146960942d60542c411501c01400b424a034140401d008441d00c000800b4026a0390403540d8811078401e080f0b040e0301d14012110321080000c24480000790543d9280d03c00030540d02c0d240c0c00d480081c0e9401c01c40d924218076441c02904400f4405c400240440d0720b6501408400e0200e1609224034080c41c02e0460940d903040e2503018054201a00420050f8002c112007801042400d624507400b80c64000054000c02045220010081c0603010f41d2000780c0c1f00c0c03032179400904200e4041d0341e103401400e01e60307541e14101020b5031460941c0e02c8010a85d5507505400e40c0044801d1404800c0c511130585c1d007405140820800d08035060040303d0341181c850307a5644080c0030b01c00001d0f80d400c074002500c03070100a90515600c10b00300c0042c0c10030076000394810b0080ba20f07203061140d511000d030b40d6000321504685844007076801310440d200910004242000e21070700315400744500d40c0d000e10415030110100081c0c100601c81450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 550818174 1250 550816924 550816939
    0x30705040b0711091e06010e0f28030f0312060f0302010c030909050a020705010501051009230d06020901180e07030c03061502012004051c0609050d02100e0606 70
    0x100c819400d40c01098070500c140d24000e03408450b00040b81a468017610340b10b03011620300d007a840c0300c2d010100388140e014000b441c2560903005100007044a00341081041d60141400305184403511000003070403c0c80c4104405001e14040c0d81c0d06100484101000b4110002420301420b0551039140c3d024050540d161000380045c282d2030b5a005407080384541d803040382031006400c2c000400b40ca980c800c40c1c2c071030040803602503640c1d1003a10b0401c1c21220140c00140c8510701b03085412203990361001e51b03c42558490a0051310f030750b030922080c1c440700143c4091070340d10810341000d00d803c01603540c01601a8800c2030322846c492040c003da175064207050b2401285644021500001c081e1403081e0820348400c15603040020311d860711200d00c010130004c2d1464030720140c0c0d119030781007031141854040c100f80c0024011103181005d0525001030f5283d80c4400c00c0c01c104056147c81c18050110391b0b4050188a5406411280031680600d0301944450306416802405032903c08603c2c502180411840d200d00c0000b07106a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 550819424 1250 550818174 550818179
    0x31807080d03050405190804080c010527010c0605090313120f121211041a0f03010b090f03160e01150e100207030503030a020304020a05100203270a14130203070504 72
    0x700c008141c010300c01d417001e2180d80204900d5085000508002c0d50164440d08c0d651810030040c6403420144c1800390b41001000c02580c0c07005100f070001010800c1e41e010403540c0700c40305a070048433003d0680701e010f41320910302000c0c00844036001005000ca1840c5014040b0003d42d44c8052407a100038214001d807005100c541044000b400c1c420402c040f81010303050241e94010101112000c03100c150003036000d12a070009060040d10020b0140c08842a5100f600520784160750b010030080b40010300c107070f01034018081103844c03160340c1e00340074030b8801c010140032905e0003541d0a0801d40300321460b104041c4002002d03c00420501280484c51182080e292522902084000140140040440c801604500401c440400080c0090000314020304180714003503242e05080c010085141c0b0350381d000900c201c1c070300500404080e030080709072440c02c1c802501d503018100800c4002100e00e65106030441e44401008400300e600302541c2e007091004c3d030090b501c000b00008000840d1040b440141d801401050003403004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 550820674 1250 550819424 550819427
    0xc05060910030e0f0a030908010605040b1f052106010306060e010e09040812010806010807120317041401020d020705060c031515040306140114010f080c07050c0d0602031807080d 78
    0x344903203d90348102d80d000c081c1d10242c03600f003c00703090085001501c118800c1001c480c090282e4406444c0441341040100c0074500080d100c90703020b441c1250f60401d15003e01510381c0c0280180ca0b003410943c1c2070082e03512451100980b02c40070440d0b8280c042803808002007078451080e6100580c01106844500810540b40208200b8100c0204100c5507600200840f200d420914080103000f014460010545035040c00b902504100c00c070381014105404010001010942c0056901c031840140070038844161228200340c03200c3c800340180002701c0d41c0005540c50000d60356034000c0c1899070264042d20700360b41701c0401e040884d100580d00c1c0c11810080301c0000b40603203400c95603101d46402d190002403178940c6c0c03540c5a009481502d01e480d90f82d02c000c4001000300203012100c0c1c4d0424542443d21804413542d0180c05010840017404030307100c8410104551007041000c11018130841c1c1c00400b02030454a6074a0000040c1d8011550070440ca410034400680030540042d5900540d4905000f815985000840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 550821924 1250 550820674 550820681
    0x50411010210051b0f041a03071b030909050702031e030702070609052407140a030e0409150b01121103180a050607080c091c060c0203040506040302130e030409090c0506091003 77
    0x10090905c2c0020840060341082588131084201000d80d0941d49170701e0150000b070300c0d014010b0701c080349612800c00100d00003548004880c00b03030703400940b00080507144d42004a265008103c0007616103c0d0200c07252080440c2040170f940f00b12055422181040d44801d0210f94480340d5201daa504420000c0070982500c260300c801500418400060600341241520360000140c0100e0310101c041c3c000c4070295090552116401c0c074691800c1d00d013804003101954502c520101d089401030704896888601d008a41c0c03180c0c103a6005420507078005e02400c1070790b9094002940c01079801024201036444401030726500480d401c00c40a0b0000b01600056407055010780d5082401000310220701420031080c3c08540d5400090000b01c401e072550050058050b00e081021100ba00da10402550320a110070002699241c084500356581915070351202e000004100c03006e00344110f2042400d00010402244c0300219511503907c00340186072040d0055030740c400b800160721800d180ca6800c20010781c10404078a00070b40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 550823174 1250 550821924 550821937
    0x5030d05040e13020d141c0e09061504030b1f060203031506300702062206060e0106081005040902010c060510170d0216080c0d0501060504050411010210051b 69
    0x8580350783c100940c0007400c03582ca1000d084403654107040c41a02251000c100c3c2c0010b400403085140411072141c100640319549034010f09100e01100b00021b54a82c6450880359004201c001480e501d454070f91900d2142000d003101c4030350841c40c0b0780c5250f103100c454280700541100d03500d4010317524540303070100e001014118810020341c000b40700300020b040b19051a86240340c84440c000501c0d141500200410f048680058141021584103130140400c0003c0040786125502d9241c00c40c0218000301d141100291080e030f84900c0e91603000c0341c000038046c0d030422011442140c40c2160540c40c40d441e04208022602800d002a001078440c1c600800082c00d00c1d071026401c1a680c425030030b41c10380d0708c0e00500001c200c40740300405240c01c0302c48282c000c2d6404018016003030030304c1c07503103501054208544283e48610040c0c085208a008800500c1802429444440504000b0b4001e106074030300b80c24000c0f509040041c1c000e00500c00c41c811001e031074400307110312402100071160f01c2071400d0f4041e0403003030700d500400d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 550824424 1250 550823174 550823191
    0xc01060824010b0315031e010507031e02070f08030106090609092c0102070c06051c050412050f190c020907050901022a191d040b0406050a06120b0108010605030d05040e 74
    0x440785201207590030001409492014080c404071f240c51440842c2c291100601000c2c11325080c1400000c00c24114001060050035110006841d1039640c104401d4101c1300031005000c3d9200040046032a660141d0722605a038201d80394240c2c0a6541c2c2440402c0b03d0821555001380e0800011500e100f070070700b1003007183c03c00312040058200071264481c0c1c1c8200c4030b0742d0700c590081400012410841c1301504003a0b040720251072000c00080ca01921202d21544009154900308000064038503070030b00d412001d84502d645012001c4405c241c40741c0b0094074861408000764031a1480b040000d00261081c82120038012060703000c1d2021142410048442010b01d824040c540c5001040401e4141c44665030003400c400c003036201d014160310b0700110000a141d410403000700c881c40c4404100100e652440307003d81240e8050340020707640c0d6804000c40010801e6030028504000451f02903010300184200c9641a00c2c0c4c24002040300c607995404140d52006480c41007008500207101c10000804940d42040c1d0103a1034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 550825674 1250 550824424 550824451
    0xc0103050117190c171006050d08030a0c031e09031e1e09090e0325030203030403050c01060b0f0a030c020d1209050f01020c03040e0a0510030204090f080c01060824010b03 75
    0x4071030b648120065000701201c6a0390000424848508947c0582c0000300410341c2c503002119843d0721003180501c4001c009200f0740ba243c41452003907510030362101140003903440207030740e54003664001d0310301600c0c22000c02e50004100c81415010f581c2d40403003803142c1100c0354032100f880c0700812201d82c2c04005c0d9500c016041c04208080000c541c9000d018003144d00820002469070f50050750440e0800c3c5d00c02d106108001503c5603208400039030000202d0b504103405003865a1508080201e0b280508061b81200000071000715102400398030303041c00b030983c10708551024460b00e01e080c441241e90b455074451510000701d01140c1040c002400c0d502600e40e442c003807800e44407100c1c48030600c1e0b82a68480c0a150019500006d8100030802500242d2600040c0d4130700144058241440c0b142d00d20384c8503010103442540e0301e5a8080c10020006103e41030540d000000c00e45813940c000c0c20030700800c602c0c403a000e000d000b80414086405c844c00e508140c50f44624660300d0700350b42408000d0302c0c0b64200401f10075581c03e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 550826924 1250 550825674 550825679
    0xc14060a12110a020c01021e062403010c12051f06050c030d060f080f160614071b050f1503150111070f1d0402030a030e0a09020c0c0103050117190c 65
    0x42c120040007561003e400400c1810112400285845406280070a5158200382c88003059800402d180360460078074140c2c0e10006612081580164034110040b943c15032a20700d01c042c7c0b254000e01050b1290030168400c000541e00c0204174000c1c81420b41c0302986403003c0d441e0a2200324010310280c4400341e9448200ca06008203039480008461340f680166007117501c101010411a44100300c500700b240400c5025210210400c204044200c5130703802100c0602064803003620280c2010301c241d820254101c0b96200700380340081c01200d0711107404c1c0143c40c01034080e1344561096090200d040038a40d0440954039146a41e10600e408480c110921900e0400444100c2c14003042c0c41080050058038000720203056141c603044204514400090311a001c0840800c00c200243c1d402103446d090f41e9406003051044070351002d0001d150140e694205128a5101241d82200e007640080c0c0000300e040281c904000d071381d8880550343c003c015250181c00d584d178032849900340300503510140d030314501d80320b4049500d2454 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 550828174 1250 550826924 550826951
    0x6030c3b042a09120b060907090e06010f110d12061e030b09010e0624010e180a24080c190b0903010b0405071e08010609060305091c09030c14060a12 65
    0x4d005007043c0ca04d103110400303100040c680820b1941c1c00603141e04114420910707240b500a1498001491103040c07054080203d0710250060700d80b032400c2d40001045d90112440c080c4080e100e00c0c201c000107452185044c6010900040480c003002c21094603200d02940d0a18507a901013007500700401c040025500c9040841c8102e000300041c0c0e0040c2d0308148074503414031840f0072000050f0125009903040002c20100b115071510f460030b61308902840c02c09510b41d80c3c0e0351895400083d014a080350f110200118143c64a01141002e140041c0ca207020142c4030b12a042c0d2040141c040400d020140d402050080100200c2e450100102043c080c09400441e0841e02403000034110341c400c175145c0300481c5d0340721050b800114414480381d014040c80c0c1415280d95040a40040504170039000e0700044c1aa96800302d01d00f117804002c4510280d80025401c00041c603c0c2400900c030902c1840101d4043c20441d001107449510710a1206c0b20f12405000303107040003841d506c122501a48201000300039661400070b4203880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 550829424 1250 550828174 550828199
    0x1403060a1212030f09030e060307030e062d06011b060609020d0f0e0d021c0e0604120b090601030203031207030b13020301060e0102060f0106030c3b042a09 68
    0x75801881c08070b1421407140009002da44080d00315080d03c03407911781802c3c0065001144940c0701e10b401d0b0b4980ea125916068254001c0500c001001401e108010401007000521400901c0c0c010050100503500001800c80b80c14546c1c0030b5400501281d01c11244440003609107550142050003400e011800660b20756400c01283e0011402c7d203842c51302d0300c1e01c0c8121202d03240500c1d207440003017100a0007036904a0100035122a5a642034030303090f811314101520070f18802c0050982a400003408156510342d40c0b10401040e204052040f180c1c18000d0000902c40000441c04034101ea40107000ba42c81d2183ca0b013035502c0d0f01e94005202200381542d428204545807181b4600102c4200300c1d907401680c0354103000b00648800e2541040d0740c1190310100400c0b84601c01c0303281c070340c1c1184c5803810040398052484e50156840920541408120100040380c00c3d800b0420300c0c0700254444061031109408408031080c0310030307940c003004112100d41000041d225128841e824044172031a040c904104250380341c10140059 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 550830674 1250 550829424 550829459
    0x50d170408071d040308010905060a09020d0218030f10020a0522080c03011e0209040b0d0305040303081815071107030302070f0905010815190e060906060a061403060a 73
    0x855100780c4051018020700203810943c0f51000003c0c1c2294a0140c1d0028940c1d80140181000c4a840c1e901050494560106003405880d085009549910140d01c10350b0007500503c10032252384c1d000d80d00083e16400c0c0866075020750245213015140c0c0d40f00030100000a5072240214804021081050b0326584003100007a2040401c904c240d03405040c901944186811500900b0a2207a40341000416542120407180ca01e1045010790240c1c445419000080042024469040e0441000c42c5a00d04043c1d00038002e0003520301c00d48401c2865291000c012003c032007a21940145540301c1060088401d210f480f041c2e81c09890351a1020422001403442e50030140c2c0e5034400c902607400031030140a03054503180404040e11200c141003103958540801543e0b503841110f0b5000b101003e48001c50303200a104400030075a429660703414092510308070051030750303180103c0b0312001e03900030740d8003080030340c98407803825010ac1c0c1c0302e83d49000907111403241d0703e01154005800f2941c840030402c40060382800d41a0f15261 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 550831924 1250 550830674 550830689
    0x1020a12020f0f01110702010e03010b042a0801030803070c050a02150a0806030c061207020712150f050c0301090e0c0301091b0f0305030a0f11070807080c01021501050d1704 76
    0x40c03103080d005202e8601a00a100811180d050424180d844031405007603c2d0720301d409180c0f01542c0c40600e004680100320030071040b500170703080c0344a41040c000c01c420340500c141c2c00b5050000e200a40c08204030f03131401003800002c00c800020008200c0b403e10030300c0400c07400ca02540c2a110050030a9000501c0c200340340c0322440c0343d0307180420300d01c0b5490b401c404503030b500c082c0c1034000e0403484002c200041e17064410040f072400c07070240311004544d2580c42004007802500c403108100c841e011103400d0800c400b83d103408401d01d80324106020505605402e0042c240151030301c03651241541d003407008c3e010150403c3c00030341010744a0150402d401d075500b40200d1440900a01c0b101903900105114003420011130381202511042c60102040000e10010444510040c1464125a42d9421180480d000c0f01082c12440185c40b03107207001b0400c0f08000c02c1d160111907050003103a10a03500c8100582c0c5030600c4122000d080c030200f90040019081c04055901814403901002403c48460203d02d0615007280c0c00900d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 550833174 1250 550831924 550831933
    0x906050906030c0903250905010807090e030d09110a06021621081c0b01020d05030a020f0c100608010c0e13110c071707060822031b06090c0f080307030e01020a1202 72
    0x202e1b0710b02c00a0b2034054030031001c05101a60411840d60359565052040c000f00c903903240502d280140c420f1040c3c030900701e0701306010f011442241c2054080c002d0300380d0303409105231440302c0000b82c40d50000960010000107041d41c0c1c84460b2512080050342c00200302480c1c034101041c078441c0d002078241c200074507806105084400094584040f11021901d070500303030300e0540d0310180610424640200603a80d0081d4405400b50341c8003054900100c5a0159001c15442ca10810b24000b81e6000950002e10984107154020021801c62000444980780e0144c0c1e00c503004005030782052410703410b503040031040104486d5564640704005594901c2d0024580c05807101d40410080c07e11000802c0c085103008105529003d500360030450000707111032400e000c6a008882d0002890010180030b5000c88018050391012240d01c45a10304104002d070550450888903911030140104514202c4000f5005840480000314102151aa81540c21043c141c4241d810341c0b2558820400044807410a4101c01031150b0140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 550834424 1250 550833174 550833223
    0x106030602030906010506091516080705010228050a031a0d0b090c010c110f13060b090306160c020114040306060b0d0e0120090402040e090a020109060906050906030c0903 75
    0x603402c00406801c558400c1100f00b01d03616407665560500c4030122745040106580c0c450906001c1c1200524a00c02001d0301d04c00300f9080d0a000040d8090503200c07070b00e84151074044c1c14440b1021040000c2d005600041171052001020040c4254403607111800502d0a01c0880074171140003a08818011504950a94030001005901e8006000102d05220282000d048001c40c513920501c03100c01122000e80a042c04070b0107003d007940d0340c0d030b02440d40001d580c0c03040003e242c8400070300200b5804035218030f000c1d110324004140500d440710101238022000c4c0d941e0000400302c9074011981c07032900086a10660b08103102c0403011504c40e00c01c000c010805810300d290341c1d288a5050000b9644204240c81c10b0313906d0a149180801c0000140070081401480358560740c54400300050003d000b82e401032007002444108100441200051410620303000b601c0d1141c10340d13503440080341c00d07610071300801000500a00c06030100c0c5c200b0001450300000340120302410085a500404c1c9069904c074501030003180341c0301c1d05 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 550835674 1250 550834424 550834441
    0xb1306031502030f0a020f071505070311070803010e0709170106090f0b0d080a140c0c0321040e1003200405010b07020d020915031e070609081009020111010603060203 73
    0x95049071001c4150300390b14020040901041c030003080d86004a0b00002c000c451082c96808880790aa44000404144c1d185032141e4002060111403003004a0f02d000416101e01c1c0a00080e510f02640c04205603240d40c0c285011410800070180007102842070b980d901149400b5a01d5107a80e03140141e5000141e03151800f282c1c901964640b5040b625000e2030b000305066161501074070300c6822500204500e580b50302c1e403a070480311117143d089510400040030074034072500d00022400d092085021000c403034000343c10f400f041c501855012034100342c10000b0001000000c40c02d540c642d92080055112082c020760b2502c4d003c0c4145c421030f44d00c4511101c0c0d1020038031289860720803280902440690b050600d011580480c07110300c105500a44601054800145015803100c90b0109015000c0c1c10750304250759441e4442c41d9a01d01c00e24454445c0150b80b400300341288185034050465000000814540c030800100034001d203070240059040040c20000720881c44e8003400b6500c011031064100503a00d10700b0120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 550836924 1250 550835674 550835693
    0x150207120e030a0f170403061a100816051603020f070906080d121506050c062406072a0305010b0306090c01050d140103030c021801080319030b130603 66
    0xc04a003070104503001164580c800048050906a00070b000507040308660070200d51a16141202c0c1c0c01c1c07210b000801104100154019180c0042c003181c2c03d10320030005074104503034417044418002c0040c0741100014510300004941200e5200241001c0340b405c141540e812005010301c5905402690003e0302d00c8244e05405c00044000744014441000300328103101c01e9540b14074504000e42e0402c14600d4008180010301d5102c140081c1e200d10103001d4017a650301c0050032903088003403880200d0181c1c00c002a010390b8500c0f242000c02840700c0d205030255840000b0131102e40c1000c0c00c20784800e5020541c081103500301d20502002d00310507050f030480b042d1a5180450030342d002143c040707000f90044418002551030005403007922080c2400d00948501100000800602d600d5110310394280c54070000100341078025400d04419802501e40e030074a40c02d2003c1c1c4060102c804e10030082a42e0042010302090429607482140340307040c074070f07011911020b040e0000300481420b00649048603a00c00003001003000454 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 550838174 1250 550836924 550836953
    0xf06160c05130c0e0d030519020709020c0604120c0203060a050c0d0507081009090b060d02060f070b190c090e060607050604080901030e070f090915051509070336150207 74
    0x85400d10b0941d4146c3e0000d0a5001715003110341051070754003c9034482030090002e0070282101401c02c40d181c031800c11070582c0d01c020980d400d4400b07907800200c09140300e206081c0002c03c42e801030000c007000c1d26050007803c01000c00901c41c0016000034016004601c00354050280104015034464010b814144641004502d50b90300000c410391620f00c1420016115680c03541c3d1241c411105140561000c2c000308010f40308a0303c200d28041000245001000505203c4900600b0300d03020714862f00c114228040100c0d2022104400401c40f40c100411004c3da55612041d0320807006407156007055411b40d240d924218080d20100c80c803c0005c034840f441c2c2d59061190303001c0101800000c010141ca000b003480b814550030b01604051b41d44490350304091000c608050504012038010400061424510300144100841c507c284a5002e0750b000c18010351003401500425055a07400d00342415420300c0040c0c544120080c200b000c88c0041c00c03114003180265401001500c011800980c2c0c038581d5140c950707108410f01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 550839424 1250 550838174 550838179
    0x2703060e0d0f020a0b1302060f030103050d180501050702131b210504120804050304031a060a060e1e0d0503070311070e0f0f070915110c0f06160c05130c0e 68
    0x1440c00c13201184035030409035008000d98500c1c10722503010b8004900d144c45070400c3c01c0c040c503070004000010010700240c541809034107030380c686126000b800c0b08803005184c00d101c2c42c1d00281050040c14054904540c540c00f0500a280d030000b100c2682036400301042021039010f402190780301d40ca13040c0c1d40d42c0541c0e4640c55080102c0301000746107020707612201d07004c1c0c10009020403c04e100d00010301300001041110061504511010106210a80c2107841c0d10300807200c0d140942052800015414005e00303c26551241c01401c900c050075800c4110084c0c402d800c50815800b040a814110200d80300784020440769002e640e503140c0e00b040112506161020680c80b2002c044803420801030b00501008882e6000800e06000030010740310b030b14007141d8492141e0840c407101c901c804030461941c1d4100144412020141041e110501d42681c20040c02d00c1e106540759402a008104088990001030129004144510032046509803201c01043d0000b0900c9020498103645907400c00544e0b811110b20100c00307208 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 550840674 1250 550839424 550839433
    0x100e090a020408030a050c150a0504110301060b030c0705070504020a08250f031e1a0102010c05030c1918140406080c0d0803061210200a2703060e0d0f02 67
    0x50807040c030350703d1007405e054900308400410007045051062007500403603115030350b100100e8103203c2e0030f100c0240700943d001c982e2544041e580385024207042c02072404a41401c481c050941c0c0d104205550720f540005011140c80c020f60201149594951015003400e00aa90382e4a54524000101d0100c1004440c11414480035543c0c02c410081d40c840d80c03642c0f00ca0650f26010503006016640038088003400071002003014100045400e0280580080ca141c80000b41e0003849045842441070390341b032009031030085600c80100050420820820a184810740c00d509c0c002400c4480903846c1200e14002d81c0041300810003100354100140781070b0103450042c014107800b52026488407000222417003c040001440e4083c04800100180e0341e4581e4108604201815a410942d6090314800180079038900c0500c1c440303803070048e04401c4401034150382c4400d980c0d032100202e00c030f004000d1003003090170b02d401d041100262400c0400042d643d0300030007002d0005440205502402340310042d0443c207401c000001190310 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 550841924 1250 550840674 550840679
    0xc050f0d1709150a03090308100f1203050f0310151707030f0e011e06080c01080711011503030c0302070504200f071b0e060105070f060515100e090a0204 67
    0x4580c0d42030500080c1a900300c0740d5900012000c5a2080d100d401281c202580c041891304966406811107840c041c07107907490010643d01c070644100002c9141c000c0180e105440c91060110740c0b01c154041034150701030f05080b424038100c6400112145d00840c2e18140001c030400c8100030001c901c00c006085031072541411250400c0503403402c000048020b001c002090384030004603085207465404510000302040c028029000605240201903542c04881e40348203180c4000003881290103e00c2103c00c80059481d440b00381c0b20850101c540300c1e90301d800d02e000d40d5600c14182181d65031540ea8000110b10036140e900c8034030320a0502030305041050f0302c90ba00a074109060902c2c0100315030300a0f0241d00c280301c2d2198680105681e00b0f807a0380281c010060009000c044140c020301d402d4003410040701c84001ca01061030307442100440d00713070003103c0340100804280c0064400054007604820b0f407100040c241c551502050310001410f85940c50004008900264040402820044002944a4a0004154034052 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 550843174 1250 550841924 550841933
    0x50103020a050a050a030b030d18051e01080726061f120c03231801090b0a050601020f16080721060506010c060203010306021b010507021c05160c050f0d 67
    0x1083c15644070030001e00084241c4d89500940c0100d100d0400030b0220380c2c0f0031148920181c0200e000010b0080c100444250003d007601e0100000c100b800f0303000d00d590012684010044d1203400b4040e00349001d01510042203000c0c49140f4050000582043e90304001504201c800c2c800c0c0e10040c2c20b00c151101c118040d11040090b0082c0d41000741b0810b4240009200302e0800f01140200700c2d6800c030240103800c010301c044154444042582c00b40c240109003400080240c640f5508030b83c89064010309035661390b0000f5110350390b1030713104075406001030060704c00400c81e400c402428003220910f250340c42c4514520522400000704240c4000e020fa201280c05a0f880da2504a090450780d0080103104540707420024078540d10400420050a034010015910707940c40f450a08040d400200711241d581c41c0d000440c044c0c0c0c00d41405498002c3c10160050602e0b600c060b044090000170155001052010802004940c0b230f02c03024038004140d010740005401541082c040000b050070a13080e9610811001d40c1d99030114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 550844424 1250 550843174 550843177
    0x2c15151207080912120403020c1f030b04020d0203090d0207050d0807080703020309030a1a060402071a0601030209031b030d0f090b0306010309020d0f0501050c0c0312180303040f0c050103020a05 85
    0x85600c0c149482507039915940c981c40c00350310f44c05003101903601107803080720040c4c89001c8a0145100e50287c40d009400d44050249002c1804038807920001d600d802002c4150190384403403401071001c3e00151404608100502c26640305892081542d880a59000c0406a040c131900014010454849440d000103031035800180c050340340b015101c0c180000d980800c0600800403510004009000d84284142d2818502284008815103143c800060400102c0034034040c401c44845c00e50042c00794100c011192140c2c64605402403542e418550b08000030201d0359400c101c00b014135000400040180c1400c4024141031440c05c03500c05043c0540315a60151203600701420406503200204c1564581d690400128085c01111401070f40024280740001c062090421440210314000c3c3c2c002e001e41c0d22080d0b07001d175180c030070202c4188040e0401c0c0402d01c82e00305000240780d004100480120340800f0094041401e641c41034800b225148040b080340310403c40300f0850b4030001c00e400d007011800c000c130251019155 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 550845674 1250 550844424 550844431
    0xd0207032f1b030106170601090609110307030b0a0f0b09040614010507022b0b070e090115030905120d0212090307020f01031d0f10060902040f2c151512 67
    0x250b03000b41c600641e80b400d5000d04000c000e003a0b00ea5008002e55024503490705002e000d10700c3d80343e05140c0c0204020b4100d024554184044503012450340ea81c600003200144001e60482d41c7c080c00340d01001601011000d5030002810200301e94036940e1102204102c00ca4200b0380c070106541815511484542ea00182a5441c5c8c030b4065541580c8448410f0803030500c4001000d500c80d00903d02030030081072101100700240f1600c02c0b80c0715840c1d041a0b080c104412000240700304000d8032204455240041d00c039130401240d50344210110f52403a9076915003006070390440001a80450707800304850b00c0094000c0c1c0d000d40c0101c008030165162100c1034001c103400c011240070302030505031a00c0d40e040040c120035209615922201d0140e403038180d80c40501c0c07a19070350781200c1044460b00b01400414901c405208131001c9030103101d440304500340340404c4680ba110000c515041c1a01c0354a40903008151582800d81c820008108040703075640d01c0f60101705a004805024a40200051029401600c42d00c1e2030b9941 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 550846924 1250 550845674 550845703
    0x307180308041e091b0306080606030c1201020405030a210516080f120a1d0d091401020c060f2101080a0f080c0f010915020316030b01050d0207032f 65
    0x501c00704040c81ca0510034040c0d13001c8207500c1d107000c00350304900e01e00e08401e02c1c0b94486968107002a079510b48140d0ba50303410076284198146c0040c3c101a0261034207044019940b817020740098101680d907000a420b0441405051310340c1040c101a208516040f400e0f800400703001420701038140665915040e0021482c003000902e0300400061341400b0b000400705503108640c094817149110703e00b0311010b82c080c0c442a140c1d80e034049a03c504031000802e000c03541c074075110104e540f000071952a00c141c800c1510202114641075004580c1da01e4059280d02005042b402d1120307400341d603a505d000340c09070088507184809a941412040050100c114080341c003080042c0c0212085805007074600344034a0500c2444c840c000f00c0d1007001400500d6100640116110300d0050040c00c60820214130f1035000c1e407004403041c04051002c01c107810403260007680014803010043c54150b080a4009550700304982c000740095000c101d10104144c00600f8086806041c0058007600e01c0c1d003941d2400780740c1d96030241038031000e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 550848174 1250 550846924 550846949
    0x303090201020a02090406020c06060306010b22031a0f0a020a053001080f0f010b03060f04030c05060c0c010b010c08030601030c030b03030301030b010510030228021011030718030804 80
    0x1503a10801041000c50740007170075400541400d01d04880207500821180344640900000204603180124040d8100c030108140030346010f1560f02581c1911009900b8080342d024800c2004c0301141d02c4559501c2c019034800b00f0b00115040c800210f1080220040c9590026801004a08149580103007a51908100d4810801c8a01fa600c000010400304101d803030305001da10400006a00c0303400040c0d15000071058003e4401e00000030259a007660f00712400d0a03055489038001c580f880a02c003102a501038004d251a012050700c07a07a07a03900302075003500c50900300180420b29201055081c4205101c0600900b00303050060b44580d10985103001c004c0205040c9541c91080009290294001c0c400c03881c8000c06599880d80c5a24003400020303401c2c0a4903000300d1440146001060007403007140d00003046080e000c0341c0303010294516800e60300840d0f102d508500550000e50406056402009009001a480c4586900e400a03004092400845001503600340c400420404240148201c0341510020107206 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 550849424 1250 550848174 550848191
    0x3061503150408090904050327150702120a060614011b03030e0106030c0b070b07080c0909071101020d0b09100e1b090306010e060a051509040509010b0a08030403020909060f040303 79
    0x101000d0140c0c0b250030307802885c4002040200500840185032200c0e4031000742111615101c0311020306400c07002403541007102c4040048102240038040c0c00203d100800d507202580d080c048840c2005110303a400c44005445010030b20180348403070110f500c2c1c01c6083c41c100002c1000c0e654090070000d06c0030009424556a6804984e540c10203411900145d5040221b0042c0940e030340a006480d940521004c0d46c0005d4140301003040c461058800e00e024100032154941080d42510400c000340e000604500148038540b510400290000c0c00a8144825103071000900c015104081c0701c60305400a02c461001c050b60541884264814601941c1008442001440015034480c0700102846000711807607040c4200c0c0000103240741683e1106101d06410b4580c8582f03195282c0502c8480201710361006101c0704240011011400c0990200364030290800000c10056035080200d00c40c9002030704610019000050140300754181407444581000c58080200301516200d1141030151101510007400c058882d10320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 550850674 1250 550849424 550849433
    0x60c03020a022b1b0f030302120a1701090905010f02030601090911040308030405030a030608011802011206050a080109060e0d090627060c1203110319060909080306030615031504 78
    0x116401a51680c666028441c24400c0140030048804200113505803c040303800711000d00d070101145e505400400146545c1404008a500842012010803900100300955401c142154500a10851800040032081400e2007402e544005002c078401c240100300303004150b41e20010100480307082800009a000c034280001100e8426544044c0043c4004410300050000203c01070600c041d058504100fa55940c11030746090ba51203065400481c019001400301650051a01c000743c180b2118001032400c3c2c490000400c2e092950308803010a0307548203200410880c00d03120300001d21000d40000c1c10141201d400c028142540c5006903820040c000203000300d80340018142c49400030040070140743c2181c503904020b005401102054032202d42002280444034082d00c1100c000d014502e03182450759a40c0c034000100020f80508821407283d0300c20001540143c0e0b40704032039001f4840c2000b01c2d52422300400f018034004025100c40c180100c160f064410740d0b5800281d4981c030011520900c011076845041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 550851924 1250 550850674 550850719
    0x509100c0203100203090610080307081602360c040302040221131101050c0d2007080303011e152a030207080706030b0303070813080a0305030907060c03020a02 70
    0x5000b501032140d0a1038600b4a12a80c01461040c103c41c001c0740d00720b6031490302c641d001e14010300c540000303900104403603000b040d84500244940b80e448440c4141c202415808141000d040300c3c8003401c100c0c500054010440c500c06404800c0840078002622541058110494030303200342d1200030302c5194000b94415450306020200c800e84001d000c8a22014507101103a5103681d04014802c995070107907048039a00ea580144243c031020341941005041502c0004416101318a41c501200207100c040903503451040700401280e009000c030103002c1c1da180d51401103840201b070b240b101c26180c5000300ea1000d2103020800a141000c030261890220725103060f0700810356041aa40e0500526060740700380b5802403503000580c0400b12003c0c82c045030046503072032a0407000c88180d1800350394150820000c0c40042010b0401034036040400070302420020340d0b9445128035083d00741600b1004280d0101c10004030b2002031055500900c4542421040308207595402034940c4113160b0700070b209031040000b0382c0400302801c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 550853174 1250 550851924 550851947
    0x151505090d02041d15010e090607110319050904050601030b0319030c021c110f010c0b0405011517010b090114121002031f0f03030c0b0405100203180f0706050910 71
    0x641024135a54a80b400940761039444070002d00c030160071380000844a61a6a196100e0b07407a21016002a40300c104080b10850015070000c1140d2000780328050306152051501c10300c186080c1c840341d588400c480140700c10345600034607090606103845003a0040e5200800d821280b4203039031048076000080c0b442c00f502d4804044030080e400282890980c000403003c02544032106003ea0580700303102d042c0000304039020555908150000e10200c15030300c0084c0c0c51100142c2c21030321400011a819500c20400c0d6240707100390b40b2111a0510030300304211410802c0c441d0500d80403064403451a00d60501625100c410300c43e50516018422405c0c504a072440300f030166034200c052a031001e565a0030220080c10b0700e24031440460a00c50b41003d40040c840b400b540750082102c1e07040e112003502c200662583c0000311001841541c0702e001e00020050001c1051008503c40c64400d4403190010703c08282c1141740c04c1c1103098282c29580088014400540c020f0150b45624008440001240c10003000481c2c0d4860180f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 550854424 1250 550853174 550853201
    0x91710020403080904150506041401020f0a050c011806021209130603030f0e04020c060a0c05070b0c03071715040b04090510050a0b0315060d0c030203060703151505090d0204 76
    0x7250100c10058984001e008420040341e091214160410b4006080300b542e100301980440204020030a140282c03005040d540d0050042e146101240514541040304c00c0800711805c3d00000c99a000f1584c100c06050f180f6942030b4042c00099051050180d40d034041c80304a8094013401250017000c555035251045500b10320305206001c9540e4070324000c1c0142015801d501c0c04208814110085404c003403003690b0840c2da00308024203503a201e01103010010041c000c0040104502081120049018410028042c0d20008407065492400d50401402180009000645054000107003c2c1c81c0c0200c05105040c030368121000030b1501c00303401c0020b0081a88420081440c041e00400c051040c102c0d41c80213214007142c900c14024048558101525140e001c2c801c402010310007401f040300c0e82800100098410b100303c80e40e0900136120b800103850090100c504500003926501042104044801080010304800681d48254254030034041d2450042c03c00e42c601540f0450281002c0d035031503130003452648590 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 550855674 1250 550854424 550854427
    0x1e0303071202100207030503061003020c0706020d03180f02090603100c05180102061603020d06090203040f1b0f0306020309011104030804080606030a0816140f010b0f0904020109171002 81
    0x154506404005400c907014000b40c003490741d19140c0700700f20340226440c2c1981a50791a2840d40d5210801408217030382c00c80038003056824400c250005d0010815813010386916002001c2000b18150028150b503d82044010028901a582400030391082a1200581d0b411030782c0c2809941c07000c010074a0300f4030b41d940c42d00981d824001e4044059400c0380080081206009001e22101c00e00001a6525181a071315401030b00c601031441c03030035075100358003426100762215004540160b54859150036030b0001e440035140d02c0b40c91451041081010380c1e40143c40b54010b8290304a0610b4580d03c00d20300d40b45440041d0600c2d4000002134040c0c1c10a5002c81c14038007011480e103854580380e060492407a0440c2c003850040f0300c03440011074032501e000030350085040c1e4850f082c40d24200020581c98003000350180300321083c8843d10801c07000c4040510000d404044400e000140044100081240d681c5c00780340d826004200500074480540d078844004000d480706404283e80b9000008252884c0c09200510300b42003910 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 550856924 1250 550855674 550855687
    0x90d0b010909112704050a0605041208061206010510020a2a0e06150c2d07060c0203060411240406080a020307020723120c10020a0f021e0303 62
    0x540b580700008460041c0c280220300030002081c0b20209510035104900c1c401c00030030031344024200500c81c0358440d00c518107840b09210b159035a0010307070744241c50464800e181501c0c06011107a0124010703501100c1224040d6280011003486a240c02040c001d9a0081c40c05200f80705a96000b044504240e581c001050610038142420701c940c803242c000b80702500c6c0340400314002420242d23403030168000c810042880030700c090405a6085180e01a180d10328003070203224540d40c442c6100180c002d0f040e05800100c07012805040503110f080a406030070520512840c00055005a02d0020300554040e82c01190180c20041d441c00040200200003015003c0200c00013498980d44007010240c0200c42c910b031101c08154a80d030a685081e8082140d1080050703100e1401000810249250581d0884c0c009030a20110300f10503020410001c0e41721401203099103e0340361015141058201d01c0c4c5038041c2071028001d112400d83e69038840291049003c1c0c85260481000c83c11949101c404101e180b9004049039500d50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 550858174 1250 550856924 550856939
    0x40e01030b06040b240a030615360308070c0506070f060c080601080a0c032403021507031704080904050403080901060e0c1b0c0303040f150320090d0b01 67
    0x1401160842e003d2828880b1041141c201071800c1a02440c50050551950480c00ca44024640141007200c0405450b82800a418003e0101c2131030140b04580d203500c0d01c95404d1500501f41400310180b040a05a03180d2084081528011440d0580c0d07800f00d12141d540b42e0500b07100d5081140c40d08226409000000c9650070403400d050211051031091405011481c0038080a40b0f20000485500e400b107000130001400407000d543c07011000d6030060800081101a0f5607955075074004581c50140b1035001b10354103009620b00010802e80744640081594030b00049954020f24400300d03400e400032813528050103d000c00010401f6141e524070040c1040000b8a01418010030101042d1054111035181c250042070480101519500c16884c21151624240703030161415810f00400c2a081e0450180c280204d0300e035602800207100038545039044104403410444e074000c0c1d490713460000c90141850301242152841c62038058641b100c40b9015042d844005200c0030420328034000c00000c01c5124030b03c0001c240c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 550859424 1250 550858174 550858193
    0x209030d020a03110d1b21020a0201110316120309170306040f050c090d0311060f0906070f0e0409022404090b18061203130e011424030c040e0103 64
    0x14025501e183c00704c07124031001c94890a04541c2000050101190203c0c00f80e84d90032851941d81c411040d5080804511894807401c0c1c021245160058014013214420342d07902130307005501c2e0910302c0040d501d045070700b58110b2014924050300503c440040303c1c09412141c0a0f6200310003060b0000020f802030b0102d0f00040030164421100144110710b442714000410807a40709852050401119903864050b9403007c001900c201e80e80100c0401601100c0c9040c203d00501c0030701e004801c100707403108081c184034500e02e007001d034000d050100f08140e00300048510b9501c00c00040c08000d01b614000780d01d25190010400a11001c010004160030000c0005c2450400b28000c2c0704551007180c0c2088a04c0e4080204901c0d5400440c86420402c2134101007a80da29002c80182c0c4081d0600b021a0700d807400c1c000303005140c200e0a500603110290355100401031a000101c101c031a055040715940d000031100310102118100700803a140350780d0705c044009040710550908a40c041c120840300c01c40d1540e560726115044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 550860674 1250 550859424 550859443
    0x150909150906070f0206190222090c02062d04030e270108012003060a031e0302010b0a120b0903040f030b061e031c0e041d0d021b0402030a0209030d02 66
    0x1c1c040004e2410320520108105014144480303110324802d0700d0320100c5e4042c1d0451890b504407115440c20025482c418620948020585076a01148002042101904200d0300420301d00e6004c45525041028070040e1109210b4074aa50240280c4e6450300d007421103c40e00540c80390fa800c121004940f260441402a000010401c44c01c1c103e080e90b1380b03c260175400d8480c410021004403a815510f60041c00c500da0203107501c400040d06016090785ea82c0c88040c024405a500f2600145d001400e00c803d0650a01a4510002054034800d50300b5290840d0444e00341c6080d5005482884104e0111b560000240121801810310b0b80300c114401d9104d041904180f1800e59600b44500035030030610000782180780c0c00c40e000010041c007801400146000f40b00303100454412101c10008802120441ca0341c90b8402c000100300c000111001070b0440e000f4580c500030909044900350351111402d098140f00140b0b0550703030030105131400f60b225250b98a00d407019025059002c1d92500801c0c208216007a40022440e05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 550861924 1250 550860674 550860677
    0x60f02120403021507030b0f06071424100506070204020a090506040f0608090d020d08070216091a0f0f0d0311030706150b07030906030504110a080c03010b0915090915090607 76
    0x1038179110444107030103c506030801c1c4c5800142c1c0d2110800e0320b140882c051b01c02c0a00070608482001142d80006003810081001c106403681d035281500580ca041c00d0b6810340c002100300c1c400200d01d0406000900741d004103031000307200d60b40024990904900c10001100205409091316449130f80328813580101003003500418001a0492001500c070000000700000c2441c4690054111070a40c1241281c20020003007010040d03225140601403a4110340ba1f481d001006170740f100081240d01e4900110b0210f17010a0618825500d403c0c180c0d281d641d504194601d030400460310403448060500e010342e121100400a0241804007140c0303042030120640100300b440010010f66441280c591441d04c50501a42e40081e00060310142c051205500070342c08150818010690015a103250b04001103401e400c0340c200b6541034018070700d0541542024021480c2203002200d8103101071408c0d4003a082c061000c3c0040c54466460303071020480309081480b984200c0c8a018a41a45611781001d1a81d03440609481c6e0710b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 550863174 1250 550861924 550861963
    0x70809090c0a0e040510091d120a0e01080720010e01020c0601050a0b0307120c03092f0103140402041d101a0607080d0902060d06060e1207030b0103060f0212040302 72
    0x160a40342c40d228246c807070002d65a26005507400c1c141c1103402042c44010681d040d20501382d0785051040100000d40c0c504440301d01441d40c41c090344000034200004d503516141481338000c14860b1541d00082c418808100d20f5090407006140160b105002d0902c6400170702d400c1d4800182d410a100b00440c0302ca050f294213440c031440380c907035800c200101d61000712501400140b9045480000c2c0c07689403c0302100148078980403443c14107940310b6410064203000c1e68682c503041e012007400e0800c0803122041078000242410000907200d103c000c5000040203100038441d41c4c0c0d42d200c11007075009071010b00c913aa603402400c59841d0110450640010300c180150328200250342d0500c1083c91070800c040383c032800d91154040e400d168100180c48094a948002241d016000f44031404400025124400040c0b50540e540402d1405600034065224106000030100b07801580341400800c0700641d01d141100e50040780040d4248903420541c009000ba0300c4440b03c40d1030301c0c1b02800141341e400036201542c02003061449 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 550864424 1250 550863174 550863197
    0x30b010e010e04060b0316081501060207060c020d020a0e0c03180102070807030f0e10020714031b06160813030218101806030506010f06020d020f030f070809090c0a 72
    0x1414220350920808034448a80d41c0054002503840d00300d1011804013404481002c103146904081a044940110545901c0007103103a030b82111007040300380142140d00140900a04119000342861868007002c4e01031030075540004115241d94502800806508400c5002030520024101c810341c02980c40840c4020b6115100d03580000610031a500160301115483c500000b035942a1185601c402d885018030102c403000712040d881700c6007104402c0507642c1c0a014482d0070b00d0792010120b1542d040d82d030701991140313007240208074074181986564401101c8450302c940d4194a480340c0030203940802007005501146030200482265608005c1c2c9108440b04d210b00d0134100740010030410111903d11100b40b1540c4108031859180008640504034014041075039a129100c441c0360403020303406210800d2620000f0420b455060065092007156840940990501d04601664034000c0303142c0803101b0040029400c1c200100642220118600584400c238075192009400c0c103190001541080850070540d40d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 550865674 1250 550864424 550864439
    0x40e072102091e01020a23070f1a0c03070c061805010c0b0105011b020a082103090303060f040b030f010b0a0b04060c0609030c02091303031119140906040b0301030b01 73
    0xd0310b104202c05000b0900030f4440701d90341802d40f00407071035081c19801091340b0301e400b0032800c1c0c101d620500b0076190b8886a0b50312942ea01c40c98114142e00108030310400401c03e0001d03900d8401c0c60306c5a10b0681a01c1504d1303000480320301d400c41c03040070310040c54040b090314001419600011342112041c8903805d0900364507503640043d5002e40e440000103140300d15100c01441650702035090f142003904c41a0000110060503408184040a01e42001d4000d074480c002000000182c0d810071b810788603086000c141503043c07182e4080d589010250041b4402e120340303581c41306207459580c0a0100d100c0300904540b01e0f8050059114000e00345c0d801c8881c0509074240c004a03a1000f014100c4003181c6081c1e881c030f0a188500d8a4200007041f00150442c2000550300031480965a44090301f40038000e9003001743c06184440c9005000c407a01341c4412440e50b03000740300410352020050780302c0c0040c0703009003446a00c90000313080c11031aa00c9602540343d8004c10114011400040340c40c05541601d00c2041c40342001e07600c4540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 550866924 1250 550865674 550865677
    0xb010501030c1205040c0b13050f030a0c0909170d0e01110414060702040e07062d0c0308040f060c0e0312030121050c090a020d140601050a14040e072102 67
    0x11240b000c564550b021031001406a4041175125005090881184d07889282010555000c441180842c0c0c0c100c000610007807074070201325052004101d0040c903103103050390307200d52128000d8480c00403010f079240c0610007030050750504910705000740b105080e0b07989a10310280700108840c0386100c0b210340c40e181005031070541107000c0f58103454060700e2a200408062042200c1c96024070b10072a00701351030348008036222600b0003000002d070510361a25004030b01c000c500750a001c0304120010b2411411044106165900407040c03014241c0c05240000c03140c0d885043c070f40301107143e0860043c0020310b000400c0502c503074840c0203881c03d005d007242030f03400789107112000310f600b80002c1c0198601d07551139441c08482070414180910a240c03140007558019061880014140101112500f400640000302c8080c213040e50f106214950340d280928070f515042403800240b45000b22a2020240007403012071100c0d810410741560020941c0a0030f501807807401440c0107045d0100843c07080c0107c0c032a000c0100b40081d6500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 550868174 1250 550866924 550866941
    0x6030709031b030320011b0206060306071d060d02090a030506010510140406030b03070e010801060611030c0a030311040306150623030a09140d0e0a0501020d0219021f08040b01050103 80
    0x103545041170703a00300c04000c0e00265803410010080d9a5a8070300d854403250610060700200d02034014145500d041000c1c0b5040007001800d000030400d18511aa054603680c0145501007030059514070b884c0c41d0a000c102d8003d20a05040680c040350016000003086030025100303040c0c0d14103031034580c60440c14600c01c1c0c1c0e44c07100c140001e84200e2800e200c00c2c055184a58000d4481c01c8009084602c016554101d0403804642070300942c0a82c0d44851040c44020342001243d046c0b94032080080d460a10503030981c2d52150003101c4001d0406441c0d043c4020510f14050540d005550415400c01c904a000041806600340e0f522580c0042640003070721010b91500488407124203500100c640c2c1c555070310170260100a183e115011900d851414032240740082d8108420320200c04161109002d1000352000c0240951003540000c3c11540000318461001c3d038040f4000b590410904800c2420317440d075200252001c038130402145081e100c9000c003030002c03c0d172003115207000f28051482e04402e641c07940c00440c1542c4086 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 550869424 1250 550868174 550868177
    0x50a1e1109040804030b01080114011a070213020d02040f150e0d1b0e070c060f06050d0204090809040504080d050a0c050f0c010b0a06050703110a0f021e06030709031b0303 75
    0x86140841904203581ca15600078803406803103107003d890f590b52180025080c1c1042d00755030f564403904440c04200c00241d82c09040794000d0b44031680b0840615205038410117000a01400b60040e512480c80c1035601a20800413402e00b065441e1030f00c0d841841450000c03841344040c011102d034800011540070380c00c40f02c0800c41c00340c5408444010703a101d0122550010003080a01142000e0005103c0b0b241885203000301c00e90b0ba01c80c000800103007030250660320780349001400b45290100801640d96051505940c895065401050044041c00c00d00e41c03500580d895140c1003410901004100402e0200a003002100424108115194032030341104030b54080f0340c60000303c2c40400010392403c80300005019001400e0002003250112040802c10030b02d51a40b000b004200042024020903410071910b445c000368400c02442c903503005444040c10020190340c00ba014404e024144801c5210081e40d8407040e020140800307941e0308051000400c8124144001d8a4421000d6111120214002031341c0c000ca81c0c26 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 550870674 1250 550869424 550869443
    0x19092906120703080f0c0d09080c1e0f1903060203011e060207091a0a182f0c120f1b0123150d050a0b09060903120c16050a1e 55
    0xc3d9528509291322000ba40300c0300c060144151140154101300a14001105076503100805140440c080e00d41451210302c5840b4030140641c0c501e40e400c0781d40d000f040c0c0c102c08842d46540c407000301d00070901da0480480102e0034002d12280100501c0810340007581259040100101884420064400d4440b41c600592005030044107080007050296080340040c0300301d1220000c40070070080c00007281d1903070030350000d40b003a6000201031050b00705621641c1079080c0c0440007800440d00744d1a12042400c2181d540e403545000108958a0008042280441000802680e80e5942c00c0b0701c00694902d0b0170009400810190315641d801500206000c1d11481c02101c0d1116801c14106a0b810032944030020502c0846084905080440d580d031034080010b03d900400190a1400050404070700c0800001c04040b500d9011f0018018124000001c1303500304460036220403488d8545c851030540341c0c0b141e4041071103c29541150f5a0600c80082100d175401482110305456180703009110018041e01000c000c0c2c082c070103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 550871924 1250 550870674 550870679
    0xb090f0c1c1b120609050c0f03070e0901020c150105040c0c02240d020f030f01081623090a0c020f06010f0e04170a171509190929061207 60
    0x160304880c0c02c1c1d0340740600181034840e45a22803142e890400799400d590707180e11102c8003018480c09020407418014156000c030001200729020a91b991518400c00c11509120400520711305801c1d07068622251010041c0d4941c4007107412403003454031081c091503118500d40050005801e02031074584031200e5015100e40c20400c0c0255001c10b8000080640441c508010070030344040442500c000c22041c0c180382d40e0151642000d03c009250070701c058000604560009a02d0009031624500c02001c070355103a40003074411814400d140d6420b041c02c2e40c0c03041d0010860401d100100e8020781011500045980c00c40e4010454440c10942e2240c003840399030000c0f507a0841c18420122298032140c1c5c401c0c041c05040d10840c82486640d8907035440344881c40005611342d000b0080c40c150b400c0f003141c3c003d1101d541c2400c00510b41c000007008421702402c920358a01c02c0465009014500c0d820030032803560000d403c00c080108500c0b6450740300303004800712740c41200082c0002d0b20034034101040701d21820201c00144619030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 550873174 1250 550871924 550871933
    0x6011d010501030902010c122a0c1206090c140111070e190e0604060204030c060305060310050a0e060702300d090c0b030901020a080f0702280b090f0c1c 67
    0x131660300c20b904000b144200140030842c070746800d494102c2103030740e011840c05120200b1400901030101d0380700c0c401e8800300300714041004420f00000b541c800c5006104004110325000d00200001c04c4014500c061860300040e1090f0a00c4403803400e40c0c02a202c031104140001d40c032948410007805010340c0404c1c1c48000c14082813021001710940100004001006c00034021010324001c1c00f12000c44c1c1541d0006000e00800161030084030013064141814400d40c2400d0001130b80700c2c54400442c001c0a40c0d900009040805160400300f195000c3c0c2054840034144442c0094030340010000c04000c0500405203045201c1018100261200081c440542800920740480380900709002d41038401501c071340c00110305414500011800303207840d0301c00103030365507070f4810043d103081002020007508031b00d020200a040394010902c202c00308030003096060000e01c0150785032101c2d00003140c0a411400080d04216152900041080e584c05111086414900d4418100201d82032901d2140201140c980316000024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 550874424 1250 550873174 550873181
    0x306030a0b0703020706020d0614060a0903060921020d020606030a0f06090516120c121a060103110d02041a0313030e0103020717090114090a14030c0d0f030206011d01050103 76
    0xb105180c0546407803425101d000c240d82000d540001155562101041286205940d4440e0410144c801c81e090100c86a0003410104061001800040d1907a070035104019000004002c01c41d51488002d0f0a40b00d0490001c1d079400d40181c1da0310140c820703071000c985286400030b01007200c0781c0d00400030301c4042c0c07250381d50300060550080304031844e03c540e64241c00c0700003543c0c0e4400081c0801c0c41051240b001c1509080c0c1509400e9032124000c01108070f01c1c03101060103c4440c05003e8200207481c1c1858541760f00481c024804540c00c80b00a2502055130b40a522554000b0022114031000041310f903480490700c221103210550301401d50781252240800005d024003078010703081c0014180141040e400d0f49500c4d0440d1801c01005006020000b0009415078020000142c501e0000a08038140595000450b07040060341c001e00b0b840044031031003048141d0f0b0821070101d6030000945031140c0030820b440c126103010910102140035000e10303400400c0801ca492030040000161041c120f000307920f84001034005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 550875674 1250 550874424 550874431
    0xa06081b0406051002061b0a09140a03060501120c05060f19020c031203011e081f0b040908120f07080105040b01120606080a0b0a14040b120a03090509060103020306030a0b 75
    0x19840b64030005466480a60003a140300c0e0a40107442540f40c80c100c103041500550b100b1a281c64001d10540c00e03919440788002041c2c880e05556000c240080c400000c811303044590005000300d05050010540c2c0e81c005000e49500d91043c001991002d880750100580d034003070072400c400701c013605101085e003a42c0c100000c60360140090040d00c45520040780440d0800758000840c08091b2000001003201508401c4011001482c6002d00c030f00c89824401078540b526103403044d804044141285032818000554403102004200820410680c1504e20780f09071541c000742000c1c4101c0b88200000b44661081e504070718880d003a26030b104191a82000d04010003001041d00c10760401410401211041c0700900c9418017400c03403625480780303034a00650180d05680c4410b4040b8010303608003004101e21a10400d48030b052071800c490204040814102040000e800707206509103510034000d00d04103060b008001030054070300c255407003841031755004c00540c281c1c0310940356280c059005800000126814404080d00b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 550876924 1250 550875674 550875679
    0x131e150807030f0204052a09010905010c0b06040e1501120201031404080f0322030206150a0e19020705100b100305090a02010804050c0414010e010905040309141c050102120a06081b 79
    0x447e40c00600401d01210041650b0021039000041d43e907410750b81109510008103802d00c0c1a01c03030500103a5403184007070409080540219220340c0749910004080c000001204990050360321250303907610b003162100702c1842080e0302292401c0701402100c4000020030f4400c58000d5081443c040c800411040c0a40c030081c12500c100b41c80d0740b044802030f083c20070411000750007917001381140c1c11711801085280c1e0019941c10310424607100c1c100081401c0c01e407003a5000101d44250504442c40c80c00e1000640f00e0708100410700e000d5001000c242458960101a03141410b481e08001510800310580c2100d500399003a480e0fa5004d24044801588154900c640c040d2241040e56080148440860700f5103a10900b101d8203540648014400216000c020a00400400209100ca4140741e1409019107800b406030105403044401040a10740703a684034092891040601a8840c00c0136042c0349000790440301c4820810861000480e0b03c10340c1d00d0154900345c5400e603001d05080010760091032090500c0c580e4458 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 550878174 1250 550876924 550876951
    0x140102070e04081b1b0103200c0f0c060f0d05060a0e0907230105070b040302071e15020c03030d02130906060305070206091b131e150807030f020405 65
    0x180c0c041c1c000c441e0302e015610840d0281c1d2140c95201c0004001c25118100c48444c0c0c0c01031141741c055040c007400349282030b10f0a09000820740c2c800e08807120280c082d007e9207a10800f001130380d00c40300c1034001000552108a01c05031010605a5410000301d03204061511500d1760381404110b034010b450380c0c04180c11000040000c4081940c6842003090300302d04032000d02064020302010004d0251200e0003e644680d030940700100403013080c00192250042c40d80140503102e242000508043c0200107d0000d400c2c1c0c200c8010201010300000410031810340504914600c080e0310800c4d44030b00004a21b00380010081c0510308181c0440c100ca00290040074484034414503c103030000700aa4940300d040080e12550383c0104d000c4ca81000b0107480c1a00141810110768440602002007200c0101d080001000850319000150850341c00ea001900030760310801c08080201c5103010490751294000841c04d0b401541495101340d441c0c41c0346031a04220701c80540414103280001d801450706034849a400059050f011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 550879424 1250 550878174 550878179
    0xb0c0c210a021902090f04022106102111010c02040f050603150115080703020f0c1509070303050f0904060315050109050a1a0121181a07020714010207 66
    0x4400080103500116000d00d400960921070315070601c103040b070314914803074103c000340d05550103e00148402003000f0852008a0089421581c03911a240c9282680b0050585060803112a0b40c1e22049d042d103040e1546003010000140112414048070084010394542900702d03d51a00c038507c96440502c1c03070504024241c6619001a545d920a9900004d03403c8000540d1313280001c280342c40c001007400300b03415010908004002020710070040034503c44c601c2c60301103c503031580c40003070b0042c2c040c1d20282551031101165440903480e000403281000310441186103141c0d1a0b0580303c54441c02c00d4007000c1d000841c204072100512243c60000c1140300e001400c00104103075a030b21422420b8440b0001e446000b900d85004100200942c0149500840c401c4001c02240350000c0c08104014110594103050000452104880c411101c04241c4c881604050174445125401108141e0340c203e500304840040300103d03241d80301c10218540f6480780e030041d00204100c60500031001d0002101c1c0c1c250504510540002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 550880674 1250 550879424 550879453
    0x7020f030c0102040f0801091e05030412050307111507020d050a050f060106110d0c03030b0a090509030903061f05090c1c0504051b0307090e010f0903110d08040b0c0c 73
    0x41c040d01070040001600d49050101c90448903680764403a040581c180184480810140824052000c845442e640380301400b92078102d003580150740c840c001104940d041032003403060120041c912036106944a82950b40c0d00380400521485c1000c040c0781e484810720484c001820308082c601c1c122070040040310f85010f001e0381c034149010310358240402d2135044a0010400582c20000300e0340d590a01c50090410102c5071000100b020b024504081e0416817070380302c0d41680340c44000e0140302a0842001c2030009203804020344d07a880d800303103420342e00901c04d41002600030603401d52141200d03080740056040017403901c410030511401c054031151010004202d034420440013201907a100d000d401c40045030501e0035060980c10107900040c080f43e00404010a000590340210f0310000751024407074001210303426486000d00601c1c05544882d9800c1c5054400030a0507040301c00101020703114411039200da034a0590890f505081135400401e03841304180410401c2d443c070400340c48501118030480d050600250075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 550881924 1250 550880674 550880677
    0x909020a080d02031b0316031b1502190c05030306060c150103110109290a0201020403150b0a0503150403080a090204090308011505040609090e07080d032909070807020f03 75
    0x1d95002680c00014079a0417076241950720054000090003450400c7c03004101da2a0b481a0490010b00300b0142d00620f0036a5459101c40d083c1442d080b540c4150010030040e01c000007507000681c2c000b40302c2c1c1c4420b00c2103115446060200b8045074440051411500c1d5042072220341d4100d0385a045a40c011082d81c1e00c1c081240c0d0078454001c60103503030300d040d003192554000342001119401c10300307075440c2c4d800140070360b21004010340c102d000c1c0300d507400c5a9411708003c00b28020700075a00000c0c05142c1c010710171844070303110f900308003140704003240c110200715039580030550344034505a0103801c4602c4190020700840c0c003c0f02026444001c24074041640c400584c0050100ca08041003200880c5000006025140000c160300c40040700d9400c00610305802c000c000b074030003078a03441009440d64613804210038000083c800d11004100b070004580101d810700700d015025042c140720040049980c001c001c5040e00b0072001035400608042d11803240364990710000c99441d10001c00000662003900c4440080010800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 550883174 1250 550881924 550881943
    0x30706090e0c09060d0203060a05040b06070b070e10030b040c0c030207031b030b0103030f080c091c0821070f0e0f0913050304061205100510050a090918031107030b010909020a08 78
    0xb85d0040c1d413032800100304400c44030160070060045141c0415018940c8900040b0f84156400c01d507034034180d0307450b510105e4200d42140901034008042c00c00e200c0489030160468000c3e008126011f10000191190855545c010060081c2c01070748410130402c04a01e80c005002041980315001d01400ca480343c96440145c4000e90003180020030302c403485001030f603100d50025009150809024504003406000681d54805d200d500c0e00111003040c3c0d403408000c1590308548011185010481c0090098000400d01010446014010800803d0300d50300e803d1003503181e038400b030310024100c002412540052000b4180024144290420a40d60b0040810401c0001e04024080c0341d0754140d80c004840005426100013402c003021590400906001982d1071300001c4d20080854948552540002501120358001c5544490401460414200175095007141c1083c036580c081d40b54000030011020400380d83c0e440501c00a46404910360060011070025000441681d00060091a080d522040014200340002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 550884424 1250 550883174 550883197
    0x30a08180d2a050901090b01020321010e090106230409060f2708030402060304031701080601151b030e0d02130f0b0d0f15060b070308070e030706090e0c0906 69
    0x110482826802c0d442e032000c00066201c2c101c50a850700d008034007110018002d90403896207400c0b24031900d034030030070035a11040054400c4015942840307041918a901c00e024011410149a00140340001c050040100f150411500302c01c44d911b4240c00c0c0c031940c130004101203511584801110700821180e000711403c450f41140300143e8800f020414640300100100b02d54889002028010085604c1405603130380550180d92040c0d80f981d4034034003140c1c0040000b4120460441180021801d00b500003a074034103848020455108a01506034251440200c800104e90f00e007840c2000000001d00c1003101541360b52000c3c1c108001014503500141ca02c4102292000c1560b55460260300e138407a1030b0052100490303080ea05070210f54000e031103190480b042200c01502030741601051030075806682d8403000c0180885103115440300450710b4003d1042005981060018034040c90201c1c40c0d14000c540709003101d205486064126203000c1040702c401d2402803902c081070000b0311202102d51180001040c01e051070307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 550885674 1250 550884424 550884443
    0x2010c0206070c030e3105010807050a05100e060301080a1b030506070c03031d0f160e150303090a06020c010e041509050c1201080a06140408030a050a0e100204030c14030a08180d 78
    0x1904001f00d600503449924254081100ac0055071900201c25055035002d8846a25640c007904050b2992800f45075990f403c4031000000261605012a900c20401c0c840c21008072104001d00e00f80000011500014003203401540c0402d1019008001065a903842800d0104003031401202001500340840580804c40d0000e0005d090b54103400c1c00180c080c8002a05001007007820719101c4150000d006018590160150554503110358040060316100c000007007804112540fa101c00a4444003c66142070116054081c02241c5140c5402007581601c1a20300003450945400e4103040540b03000380c8400c105000410015000034044003005010b01031220040c8202070f65444d204088800d9203646170300c0300440506100004215400f102d41203941c000c40030460f43c4a10705600000d00340201c000842e48580c81400c01034000513005001264090120404a01ea50b140703104480358081031540e43c103401c600c1c01e10300051b1604024107038109142040d03025165031000401c0c2880307a1181e090720410300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 550886924 1250 550885674 550885759
    0xc0819090e0103050606061b030301030c03021e03120703111b010f02010b010f0f02010b0901090b120c091614030f04330c140708090102010c0206070c030e 68
    0xc1140d0103500a145404088005602d1a212542c44c1c06020308030390701c201400614901080248000400e5529031101640d60705c0d40c0d40e14000c804005a403104a014094500081555014482e142403003680060003038414102c2221405a032903009002c00c03002c0c03259652020301c616008012044125003e44800038001e40c0e0032001500f5040c50a40040c00c5a04210b02c072401640d00c060304210b9041c3c00e0410b21121b01440c40280c0c00341441c14406500104904000503440480c1c0c0c2184100e100c0903120108030380c46c22000c290320b40340140c0c0c1c1c644e00554240041088a02410715102080320545000c0c14408014102c0c40c40550082d1504921a08010203010a100c1918079500078109004100791064105540803064031000680c80d4103002d40e40c0708103801813406458030001c3e40b0240c400302039507160384d4a05010550008520a0300561030074003100c01041c00001c030030707001d8501522010380500203550105e0744040102c000a4001c400d0080244400d8440c0b404d00c003800d074410300000108030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 550888174 1250 550886924 550886927
    0xf01050f0301121a070c02060d140a090606060203070b010e0a0209100503190c0e1207080a0302010e0d080f13051c111501060c030305090109120908070609050604050603070c0819 78
    0x1040c106001306043c20000502500c43d40010240104681c1541e1080c6c03141040000344004007050b52800b030100b5951010000d0b03e07101d6074060b1100f584078150400c503d5480b080c040760ba0f0300880c40c000f48130702034480040c1300c6005c0c050070700c55000701104405468840c4c0007001c122020249403444000c00e8000c01030007110000003103135100070b50100c481007203100d03400c0000401e02258007990b90f00480e42c11b2141043c95009004810180549004542e10b4500038900240240284400e03590b039030140c00001e100c101d114511041c01035079021010107a1761202e04100089902800040b56944148148006015170300c0042c40c00079000c0b503c5540140d00008035050805000048e4800f042a80100511480790098030303445085416280000303c40d81d803401114014114424060501e20500911181469028203980207440e81d0100751212641c0e221420349070040c45006c1d040d8049410303c400c0c4454104030010756801510f0341780034000e400c12511100a5036020710504404803620b0b000d0600c105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 550889424 1250 550888174 550888193
    0x10090b01060e15030c030403020114151311041a0c0118050c030a0209070c1e0c080f0309061206040228090501020f061b040320010305130507050f01050f030112 70
    0x210401c0e50510540b090a0803c000d43d88802850450866070110100d0203240c800d6212401c1d9030300c002e5040241d810280004044060322014042c80358480e010481201403440c050400060100800d003420141450404030200c8807110001d860000d0500420800e031310709000303082101d040c4060150290906080590800311044501e40c029801440e032070700161145e2102a86c00705003440c00b408440200d00e07250380401050540340300200c0044804400f40035100c908481122400b20031201c041600c0307000030f9100c1c0180e10200d80e110f5824801072400166002d141035114100510061901d1003441c51401e02800300101144040703c51100c03a441e00d900441c644014100900007011a40840d250b081ea0380d03040100411a1181c075034200c00c000e40e0712a4180c4001c2d680c4604501c44034542d003200309640d000c40340f40050002e8103040c00b05020200615a518001d40c1000107484042c2c1040140a2407880302483e150400804004580d0700b690001c0213036000c0c0460007500b0540345001e041c0a60030703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 550890674 1250 550889424 550889447
    0x30a110702031506193b010909140109060e071208181f0e031b09040318170604060b011b0b040f0b0108010504170c03091210090b0106 59
    0x200000c00244016940c001100d000f00c0800382080b07295680c440d00814201e018800040c10103051500340170031842540d4000300958010343c8122141042080c100741c810182e1070008442610890005120000072500419940e80c004c032070182d130440e06c00d202c131400c45d01075510582d4a1756840c00e80d0a05101c00b445008024201d4548030310f0400311640743c0222078414044a0403050003550102d10315502c400400030b0041498910768100e90900040141c048007010394200c0c41b0703004448003039014028841c5030002140b8060100c11050f901daa40c2586d010b00e012460301041351108200003a40030340004090300c500c0340030024000f5801c06140c0030041c1c803d03141c0300780e041c445c4120600003926640400d810546401158810071501c441c2011000c0150130f00024101e00e00a0002140c01da0301500a140194455202d6000d02d184c90503e03111540520500719007950030030480c3d1540c5107400c0c05418031401104050318513051a0300300c5482200c0c42800100c0e8401c000d03400410103030342c001c00400366 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 550891924 1250 550890674 550890701
    0x20907030e0309190503190c0b0a1707020c130c0e0307050d020d17040f2d06030c0203041508070f051905031302030607020106050f010504050d020d02180c030a 70
    0x1451554200c0c59100e000d0f00040e00d001d540400e100c100140f038484100f0005000140035221540038924402500d0500301030280d4078035001e5203001038007984081c00c655031000306503500c01401d600c80c0702800b00c2d1600035042000b107200d000a0840d107656440710342c10020304160320004500901100280554090100141c8030303400c000070401c00c0b030320b503180159941a4122041241f0201d98604401c5c02c0c2d18200801381c421001250200320000d8454080c03007a643c1c03500321144c40d40c00c0310b0701d01010800501050a03110304503801c10440c050103908900742d130702c54a0040d40c0c101074682401d000914040062a80000c00603803c0c0305202d900b101c7c2d020004002843e000e4900381c51640d0140c0038000203000c441c100034000001070b002d4403090700c013022031950041c01d842a500344160000d021784054000c2c980b003564400c4d9101c04546c040d0040f80c08a07600034101031000940364003004030400600308240d030041c445600760307440496006441449200c00d0b1901316103a040c480c2c100011914024220340703 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 550893174 1250 550891924 550891931
    0x9070603050411120f1c0e040c121104030501020711010305010608090d12020910020709050105040605030c090405010b100f0f09141003020c0712151b080c130e0402090703 75
    0x4003090348040c0310f1601c0c3d98143c8501c111810002c050500c2c2c2050308003004030034041e06010f10440c251541c400c4a56200643c0c5400280480208100407a50b40502c0000031804650041d400182907400100300715210800b0641030a40e04c0d2507080c2a680601c000311210701021110031019078152081501408051400d45124034210079455501d4892500a10611508065800503ca001e030125070001401600039980100d800e500a55101c10781d02915400a081400100340350500d44291821a1802002480d04c4044a021b1021000d8042c00541d03007552500d1126031140c50306080c40d5402d07403040e07692a0030054859401404075a0300140c4c0c0080040900c01084455544900354400c0c2c401290407800e0380b2076141d07081d0000d106440b00c691141c010500005818441c01c220b040f1170300c1c0500e440b00813038155021800103d45100d020148030310b900841040c1100d00c55011554451f01050526103002c0943c1281070002225038081c1c540c850800c7c081004605040e40d215401007100d0a051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 550894424 1250 550893174 550893181
    0x40801050a06031e0f0c0b030f01090b060a23071b1203050d15090e0309090c0702060406080a020423030f01090302070b130b1b120414040b04090c0b030907060305 71
    0x2004403188003184098401d2243d01d400d05020010b208199516809291700b580fa1f0341c0e170140b0b06019082113600c4007103201d00d0b0700002030380081800391001c8a00c0042166190184121064a032042c0d0b5080b00e503003150a40713a8003840301ea2128000c001d12070182088280030000103642e4002d5007080d4002070088043e240700d04002a0b0030809a41c24620f46540101e528160b108806d801002ca42d4440c501031810710080c0c00704c505c0c000c030040030380240c107031490410b90f51140da11204900c1a04802904000704000400003d4440e60301507401c4000540e025141c25135034105001a00c501390500e114100c502c540f0350300d19150400180f004004034074000c3c081100b80c1e48020b52102c00d680305c0d2541d81310740003613030360100076280040c8005021101d0b07005031903840403055031080c1c80c00c0302c0322020144248250080c10080c40d0090302d0440d5208049800c034400c4403414080600a40041d10360465250030214000500460028024190342c404180e140e1400e511200d1402100b40d00200a162500060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 550895674 1250 550894424 550894433
    0x209130213170f060f0601030b060c07060509010504080a080d180c03150b030f0705030c0604150e0f13050708010909150c020f0d0f08010b040b03041101091802040801050a0603 77
    0x807041141d0707810340c800355500c03001d096581c102200ca9241c81400c2c0502c0003000019100e00850350f0080380b003a87c04100400100d01440140e00c201600014254000b80040248a00c00c40080c03510041c10701d80203040035544c5400a10b00f040300c0c00c048811060209204d480500d0764880d40600411170b14400c1441c9071075031500c007108516030201800482d004450700b100454950802212500054101c92140848481003600c030840d81c01200e02c02c1c0209211040c40d0724001c2e055a0aa03035150442d2050540c1c108019a104400071841c9500020a1840c209003960354856110f4107401002001c242c1d8038003624014483d1340160040c114151070042c981d001304511800d000c03c110900079001416840102041e40b03800290809040f041c400c40c44000004c90f4032903070303480c0c4208054036590341a98a988000703a0074019409007015843d402d10001c5d0115030501c1005e0000a4181004000c841e221f0420128820000300903510031a00003808001e00b60091050640c4004c11540400c1820b085564 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 550896924 1250 550895674 550895707
    0xf030b010c020405061c11030d050c19030e040e1b15070303150512031207020615190e0702010207111e130b090a05060f010c171e0703020102091302 65
    0x40607020304c1e03484000500715220210305100c1690240100c900030420f6241c400c40040800000c6402030190b210311511107400384003950001035088025100108441c2095a6280f100c41011b50401030441d0b56484a62164032942c46074180e284007510f00b0030500b403861521b40e6143c0b1181c42c0031309201100c3c1c418107a990001c1e20803060f4185008580c1008103c00404400d416400c0203912080403d200d061043c0000010482c2048003500c90700ca41e611504245d1b00e86000710351b90301c142c0b0941e82c03481e101c5140c60028111b070b034080484001a025101c4000d030001d048125040c1d00541c2d8001206824448115111800464203c0328103580103480f040404080c081c05200c0c50142003030030141007050041c3e40141801280c040e280c034815242132000b81c005804185c0c0e0307560150a88100002d0709510640320a400e4542010b426140e1030041d19110100d540a01c0350020300392078030907c0780303000c842000061110740d01940c005626030000208004039164198031012190344104548040c02840b1079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 550898174 1250 550896924 550896947
    0x3250219030302032208100507170606090105072405100816090b0a030b070f111b060f0c0708070e1e0105060f2a0f210309010b06040306020a0f030b01 66
    0xe05c868940e1180c003015204840b1500644010f002d40c904005219400d0b40c031440c4940b070035688a28014840e404000203854080c1c5040d81c01c00000c11145820303501400c0140803052048126000798103414105074089a854039039801519240c2051040000164401c1d50140c494040500070303034400e0040c0d00c10205074a1049013142d5454150340308442c0e5a10283d0002150411071400c102e16040b01e00601000c035001c04103001c5424007400b240c0940c00080c04148600d4900e84100740901c480041000c140c2200c14034504500003001000c28004040c04564010803200c002084907a06004000e0072080700142401501030185507003041c2000c0d4202414112941907401c0f5589505c468520700f9548140082e40c08095030141e062103d0340c07007515203038800013a070300c080c0d4084a00010081c0c1d103d05000c15040e04403245004500c0c1c46000d0100115005943c910000660382c5040010489541041c0e0080d521075601068200003c0d800060081d054959032600300161441140080d041c5503200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 550899280 1106 550898174 550898197
    0x5100f02060705120f15120105090f0c0a06110106030803070804033e011b05030901060806040218042402090109150c0b07020325021903030203 63
    0xd00c03d0324040744e0349000412580c1c41e103410920040c40003a2081130540b4072428242c020b99079041164144403c5040085140d240149510342000c3c0c203d0340c1c50103e0f0300800c01c038007003d58a81c030101007514842d0070071000004010050074010602a04002d001e010004288580746402918251044c1d2107a5211422031040c0c84000e09444042039003004007146c144400d54141c400308205440c50f259500000680e9000301003480f00d00740c510803115011820000a215101030280941405860240c00a05541c117065010402404103480031240e0803000c44045020041e03900c99101101084030410001c0c082e501c58050001d60044001a022030003041c80003400203007c41507801c5552541d1101000380300e00c1d890720800342030001d00c51760860104122096510513181820400050f0114001540036101d02c107010200c001001840481d2a40080810009600108845e0030f0000e2 = true := by decide +kernel

theorem cover : BRFrame.Cov 550719424 550899280 := by
  have h0 := BRFrame.cov_init 550719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 550719424 ≤ n) (h2 : n < 550899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
