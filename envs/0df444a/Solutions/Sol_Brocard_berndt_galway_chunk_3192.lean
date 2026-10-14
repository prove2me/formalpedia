-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3192
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:56:28.56499+00:00
-- url     : https://prove2.me/submissions/69ae27d3-1a34-4593-af68-46303dd75620

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 573920863 ≤ n < 574100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 573922113 1250 573920863 573920873
    0xc090c020d1b0b040b04120c230f031b06100506040b030601030209040e1c021c030b19030c0f15080a2007150b09070c0b10091b1107081009 61
    0x60782c145501581181d03440c201890008010355040e101102c0550b10041038007101c0303124aa041c28180d0300406400101201d5020f101c1d180c0101c07029050090085d400301000401c000c0008186030300d202c4012440c2d03042c500d0308282c00c00303074060300384610614a1502080190f5a250503503081c3c610601c0159500e440d03500060700284500c030110b640050500c3c05501c8109400f2034480102240c8408501200c01e0031001245c891041c82e1180c0000021246090301452080d072141070b18001c0170b0802400c015140040d401301d6144d40e40105c400e00301002c81400b44180b004403070300040c54400310903c0b2a164210b00a402d40340000c2204610b580c3e00c0f8021040b0820340c00002049203a50f80003242d9942d03013410441c180003903844600e04254245581c0c6142d500380f1480040c401d540325542e800403098195250300d070785000a0060300b000c121908020500741014030a007a01002d00700400c1d4605440d09001402840345100c0d80c03a101d402601c010024108003154541c080d103100e24001400440503c0c3c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 573923363 1250 573922113 573922157
    0xf04060f140a0e0c030106050901090e19050f010b06040e160e060c2d0622080a0305090709051012050102071a1f0311041e0510030c090c020d 62
    0x301400350071007800303000220490303074007403980c000c030440650344000036034800c3c14240c030018400c0c941c000100e90010084440e82e5840103c810780300d9419110024040703034910410301083c4c8420b4866400c813074140c1c140304a0074031030b0000081068442c5400c1514000d00d0b01301081000742082d4505503400c440840c810721030606002500c900030320080e140c1000c0660030340d5070361526806580016109800404443c0c560090907a9814000020b01040c3d82e0340760130030b014840708050f5101c403001941181c4001340200e0054228114166000107407890420541464508280d05c214901c500e0901800340c5550f00d40703440e0f0142e414418010301c1c0541c440c40c01c6802441090340140c194490210072522000003880540d020b103048400c4120501d1728882d09480c9018240710080560804200c034850f5814140c206005c4907a458030705521400401240b1416144111003040704007032004024420072107001094800303003c0c00182080b204a00c0342c4040d690750300c984507070740038803258000c08106080b980c0c0d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 573924613 1250 573923363 573923381
    0x41203021615021b0303220c1206141501050307180807080f100b060301090c0e040e011b180b130b0d1e0e1b0d020a0b0901170f04060f 59
    0x10000c940401c002d044020b40054800103680500d415011103c650b00106680c041c4040d00900f801e4501248400181c0034541b1a00b103035140340300d00f0006100320300540b40c07034490390003814041000b105d1510300d038850f00d100911101c40c0c0501c10f629102941d0b072000aa990200d0070b8200001603914164100461009551001401d40708143d008a22607001007203041d841031001d8200d9203007019250034241503074030082ea11070304110b0078001080518100d400000b00a0030311b0402d450b000034030a0120b81070b510683e00446c2603a45a00e50607401c1c6502d0040185d00c00018074000082420403c44072042030300e14403601c1d9142d240071440349042c2020000950052442648550740c8041c4110400701520b01d120743c0c0d00582401c007103125090301140c06038168000304140030303045000c080e5004940801c0801c000a8004012802d0f81c0c0058840c0c070b1260014207950058240c0300c880c882c000500c16003040008000c40c000071014880214804142c10b60000d070300c000c021904542ea40c9500740240503242c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 573925863 1250 573924613 573924623
    0x204090203040f2312090a1706070206070c0c03140309030a030f0e04020f12070e06070b0114060c10020309100c08070201061a04031524080708060412030216 69
    0x1031104000101c0c2c0820405440390000130016005080c1141009034401c0200720a50042d44154a4a41c100401041e003490000c150b44a15602e4000320403440d1184224141240d00000501201c0b5804102d82a404081c501c0c06060800a50769800c4500456100040c400440440c079448203000030702c20303540140805400c4a19940150030700628401800080742c0c080341200100c008142814022105450206049280740806180b0084010b403001000b0f1f100700072240009036205d40d9913400821700749000d018075000b0f80d4146030010309400c0004a2a0b03101e100208000b20005101040040000784044001030b201c1d80d071754a00a04220140e0400d840052a00c5900720380c0035000181f03280a02810341c002c1107010f403241440420540b04032185000c440c1d0901c020000690441c00011000e104010046221203a40c449100300182ea400e09025040d00070100703126803d405c00515004040301c000602070307030038903866415941c10f460908408068000444000c512050032400c00d1142d800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 573927113 1250 573925863 573925867
    0xb0a0b031e1303090501030203060a0311190f091503020f090c070b0106050301030b0604050402092a0c0c13090b060d21030c02150103081b1906060f05010c2402040902 73
    0x4124610070092002d1800c5001c81c500798000f1401754404e1090360322603036010740440d000754119140c94100007008104681c4c40b6034010481044581440070300f00040088505001404d400c1c2000001964007928801030700181c1503a0400250741c40e80c851401c50720081d01c103e0b00c00d403180c003110340f1280303c0d45c40054000c40c1001d000084260340701e0011070480c1c0c059401225182c48003000c03c02614402d90b40039512060407000704512102008541a594200740e003040f0b403600412601610a0f0004080e03d01113800483c1c1425107424400040ca100010107001041090550345d200c0d00036080103820035008075508a540c00400550032501c00c0c1c00e40781045840c030044190080200500880d80c00140140540c00c40b20b02c0d980e500c0145075050f650f0128000341040c5004410030703002e02000e10704103d40d104015032580e0b6049801c0901c07100c02c8c01100040341c0a81080d442c00f41e80011940024100441404e695000ca00d40c000d080001140403040008581c1003c10f210019000d203403c807031890303480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 573928363 1250 573927113 573927121
    0x80406090506070210082706150414010302010e032a030606030a050d05030a02040e040c06030e0a15020c1603050c030601060e01020d030f2711060301120b04030216060f080a0b0a0b031e 81
    0x1c0c823103201c0e8800b8210445e402d41000b0500041e1541400c42040710600d040c014401907008034490321154502030200c801442080305140100c0400304090605100150609035140c281402500d51244040e001040d40e01006e50342d0356a10601800703a407081010100200d004003415804031001007403000c034001628102070810300d0401300548141d2006c03d2400400054043d004141d82090a070003154900305064249503890283d40000d0404216010300c2c24904040c28204100c03a029602480c01094000c01a100b494a40a810b800510503c2221000c0e03602d107a03030020300300310001e40074135010928564104528016003500d203060035149010300c03040c01415072002841c130130280c01414500e01c2c01b07603040103004480c4000e0007000403905800a0f13882c0854200206c054000340320744121281c0e141000d249004003116500702c0710006103051198450b140d402901e5580101e4000c804010010350400051408a0107120b42104010040001510b50f0940a24425201d00000c0c1034022460 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 573929613 1250 573928363 573928441
    0x3170906090c22021c0c02070614091c02030106030b0a09020103061203020303130c030503030c07030305060a0501050412080f0f04171f0b0d050a08040609050607021008 74
    0x9012159407080c0c0c891103044000c9440d000b03468142d4250b020300768200045a400c001c4029501c0101031100c4c5c1e005012076900361064034852014a03000560240031680d083c00402002942109440010310030140944242176030b940c4000010101100c0e8031250300f10b21031000c030f400340c00c056102500050f203c00410110311120f4004003e814803d81e03003008010b03110241080b05009061000e80142e00600000c0d541c1c402480c0e0741c500d800d0049131000101c0e40c0d6079490924550003224807807101d4001040d102c2c209a018021142c100604580441000b802c100000700729000d41d124462488400c14900020f010060040315000b11030081150317925141036080300d8035548240b080001c2205103041d05048440c0201c5c88050005840f070188001c40b5200054001030890700c034006901c001c2000c901000031b0300c104024149548101049506c4a2600c0005020303400d06500060103190300308040401a580c00c068000100040d051003da9a100d40a195407a00d000041d001c3d0040345203c0c2c00c80d0080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 573930863 1250 573929613 573929623
    0xf0f030305070909020301031101050c0f0f0c0a0b1215240702030706090b4305010c02070b0912010b060d05150a05060a030b03030d14040b06100f030504031709 70
    0x1a4a4015a0390396940c4c56104900c4244006080100600c81c00030703e035846100188100f62507241180d1011600310b103100e0900003181d07a88415a4003011640c01203052480145000b00560040d13681407504601680e20304540042400b40c0c01e0312003a14010466540d080b1a0480940c0c0200b00c0c030445100c044240f80d40d5000d40d005134864400c8010000da561310070007404c3d0644030701e02403480c180f00d886030030003500c11a080f810340500300310301c0d865081900c0e0b00d50964040a59900101c9500c8000341406403c407240c0d40030f00c0f0110740007070200307001d581d030351904032405a407080daa07040f12a0392004c095030040100c505042c0d4030041c0082c60000b46002c6412240c0101043c420b0f5103029040d40c020000040c0803441107640048041c400410441c0c007980c0004210701014003031f02e1a1000810f1014200c5d0101c030074062a0310171320b5041c03100744402c4851542c0d2100d802d440c607140d03203030014401401c1b41400544100416460340c8c00038003018481c4012100007814010f28101604201d606a0340f40e03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 573932113 1250 573930863 573930871
    0xe012007030c172107061d010203070f0201020a17060616080a02061311010507230f070807030f1b03050d030605031c140903011503060b03100b0306130f0f030305 71
    0x810183c41d030365030b040e00003040c1c0903061321150b003040310307614041c00c50412582c011010548106969400c0e4044d007480d42c24280500c600210300041c0c1d17034600389070302800c1081071030070540441e8410310280720f10703c1c2c10044d0401c1c03c90100c441140295501000130b061072050000303400b4200c642404100c20014080042d040101042d002e0314a169103034203050140403c092000f0b030003594030000c00496035016500a05845000c2c0031500c04e9030482c400001d11001150040c1420f560140045000d8644203101e00006400e6020107005641d10f59100e000d03410800b8000a0000b4602c991070007803070040403501600655201c400c1c0d6200403080e0070060010f01e054032078180039014100052081c25100d80294064884940300e00c2c0d103503040c42c1f002e240643c00c21440950991341e00e210f0b8402e0480407210350001503100380e00c0400d07402c0e0074009247c1031000702a10354101909100c96035600396008260540d001e446030b00302044241180c28445c0507041c088001400c0100c0d044085000e00d541030b0006441 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 573933363 1250 573932113 573932129
    0x9190e070914130b131e1d0607030209061603090302150913020c070506190f08040309050f1503040606170a03092615060102010b0604060e012007030c 66
    0x4600d5662001d810b490260480042d84880c000055040c44003440d400090140c00c0900a0418000e170f070003240b000c458000c04428044240c00ba00142014150f01507841c502ca240c441100303202d250b804e0029a5084090b104100b490740105d020074132a00d5007000e8800e2102c585003500421403c0d410017030200702103400705a028580d07501c0d4a96040c90b022003100c44808024017242612801c1e80c00410094020038030b581c070103000c0c01c13200062696401c0094040c1020710368400a0410100030301412145407000f094003480f034083c08100100750003044890403240281c89094130961100300191003141d44803d100300406d0003005010a01c0700c02e40c0a041901d0200300400b1110b2180c00e100366540b070712840d0043c00140002d03001c2c0000846402000c000600341c900100c2140000d8041c24101107086000d8254084440304020719581d090140c504108070a58105117040d0600a00034007190031000c0c503030705106080e000d88485a08651a0000c820b012505480c543c507103900c1d112400071001c0c03003003000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 573934613 1250 573933363 573933377
    0xd03060807050108040209180c0307090b03100606050f0703030f061202030c1c150603021005030405010606090f091805010216030201450206070b040b0916090209190e07 74
    0x2c00d54020110240160380041c590b00e030917039682d100e44802d066030400440143c010840d604142d030300d04110314409004107080100ba220006801c0c5890000c4104c024051603041c414104074440d04001181c413500d00031074100c0c3c4d68410702d08054010f040c3c243c1070304030326519040c0c000813040700e00a0300f6595280300f00c080d251291075000401c2051004421154075010143d1485800510081c08000f030301d102c40d0b200030070482d40d80d40004191185404070203020a000100b04030130441c0a201d040301078611400d04030320444c1003124542c10181940140c2d10b032141e80b040501c4110783c264115000c400e078050b0095580e00352265001014103480c3e0340880c055070914401c0c000410161448031403840d500c0d80101340f4004070390b11081545041001a5410f440d28020303040150311107900401590780560620300f540e0400e4075002807041802800e00599030032034150086481c2050b80d41000700c805240c1e000d81c881802c00001082d034003035401c10246040445e44000307590942c032030880b88a503901d51a840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 573935863 1250 573934613 573934619
    0x27030b1806010f0501030903020111030c07050708010c08060d0f050a05010c0e03030304150506130e01051e04030206040303050c0f13090b0d082d0705011e09050606061b0d03060807 79
    0xa50707150800c0c000c0f4a0f40070382003401400701d075100780e2003201e1503030207840003290804000034080c08540c415102d400c0040310020307421061000c00c01040000380b29010003000000f00810b40140540405024680b00700a400f00b00c0c401c2c006513000086602d03800200b507504050741841c10a0081c90001a4980440c3c16144030460628010060713074851500f0000000c4684014621302c0002c1400038110340d4000700783c0c0b80c21000c007400f605c41c01907078007100c6d00001a141480c2c1060032100402c00000482110081d0030040000e0b03011404c1c0d6005036046c00c0101e216118a242041c00c0c6c016104c80000480d030214080c1c4180712840b24600848209260030003001070b00e40c0a020f040680514054643ca200b00700041c41c540c18480580340071428281c1c0c0490310500445001143d906c40c003401d0b9a1a0344441d0082403120b00d60320060a03820386441d081001c0005a680c064840000801c1c4d24480c210200d54607080c0703c05200300c11503001e94207081c1d506031008110b0282c010400b82c010341c6107512400c8804 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 573937113 1250 573935863 573935911
    0x2090f0a0609060501021e031e0c06060a051c030905030f010212100302100e0f06430807050a0c1d0105040c1409240d0b030303150127030b 61
    0xa000f603904c1a4081d0213a840342c0314982d840e1216140740030256104c00c1006150f20030410088182085040e40b825950302c1c040c4005516090703000d05410300c81d02c840c20b410007031540c031003503040d03040d16005001d08c5c01c601060030142c490b01d285038001a058055102c02c10100b11042d4000c000b503c41e03d0b04040c03a81e0710381422040a082803030000a4006000c5507103224901d0040c2041c9070ba1220050125190710b20540104141d50403403203209048a00078141d1060903c00c0202d0b0321080b01d005400a0850104801c480c01c800c44840c8000e050588001003200030b0040511101503c103400074620000355581742d45440f10081c0741e101c0740d000d00403400c00102d01d07481c090103000d07007003601759440605452176003c1240f82540314a40ca103500c909001049ca2508155480a004c1000da904406803111080c005040035501c07140305051094000700100300100302000d007003142e84142868050440c5620540507040c010980302404003000143c900042048003403510301d8458042440800c0303e1003480c0c021 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 573938363 1250 573937113 573937121
    0x1050a02042102031207051c030f0f090809060a0507020607050f0f030310030201200604200f06120c07060f020301060e01050304020907180e010b0306030f0321040f02090f0a0609 78
    0x2945a08804034560f05d1916980181280a01800960b086d601781002c030407400e440324a200201180d1504c0c0c1000309502c091040c8001c2c0594248180580881642d41c0c0c01c01d4860070725040d21510340401c00e82105031142043d568902d40c082d114a540300c1e0785003861035a8004949009072280b24081003403030742d10000300980b0f000b50400031140203000d0541e030041d21400000d483c070442080c2100d18841c2d15043c02c004160107140114060322868081d040d140038042c0940000c01d0065031040c420143c0c5455090440750380003030328684c2d040e0f1034943d4041e44909116580d0080c01c0c40d42000c41d40180103e00d41e00039412242c10351510b1171505041c0e001036685001c101da010b940102243e00140e00c00e4020b08101a8001e03030711140200f920780318140c1c84041c5000381c00150f6821800b008201380d0b414100700501c0d942c000b61000f07505058418039108110008003840740304a0080502040c10404000360100401d0750051070b1407007520b890000b414684000700c42c80c54005c0d08001d40002e1131000e07441 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 573939613 1250 573938363 573938429
    0x604022b0f02120718021c05070f03180c1403011803030501053604020301020d06080705090a0516141c0f0506040501150305040c0302271e060f1201050a0204 69
    0x52140304c0762640c450050007504025550283e0100c0c42c404d40401d030440b031042302e00c201c290781c548446240100c10005c0443d5401c00d001c030000c01944003d070003c941300440c1081140c59031681d00010003c5640070038050185465001c10640440c00090105500761b00034034140c850654454100078070f940c0818001c4002440d094074001c004022030041c107690221a254080e0000e40054a07001d0401103003421500c0030750218403550406c00d0180003c1c0361014005811081c0103c1c1809035041541c0c0d03848504a056205409005200c82c0b41d580110a8100780d510025044800c480c141d00c00501c4030f0050110710707450000e10792420b0005a07a5140034482c1a06940031103800444e11103074142c065000744000b4100740c0728140300342c00003c01a0303100f51301c2c0d8411245041000ca0341c40300d4000b01e4160980003500d2100003a0a94003062200d50318001400c1e03118204031101d0708a5014000451400303451904d00350b03000d500f400c040090511071a0011f004660000e80c600510204508082010f181802 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 573940863 1250 573939613 573939629
    0x3050702031c0f0603170d060902090102071e0302030102120703150f150e0d051f0209030a081b0f030c0c010509060406032c0d120902030604022b0f021207 68
    0x180c040c4005032143d0384294800d15051000060344d81d241d4444880215458072201030074100080c4e003880e128047c1c01a28014001039900354244600200040d481d1074650080390b0400c0e10405440307103c648402d48000055402900855440718103001c00344101c2745c02c03680700d4003182c1070182e501c1050481e41d00000480b10b040c081d00401605044001208407503a40c0e200041010b40c204040d0542c0e01c1c0706442100d24890002000900012001c0b4104032100c00309415000c0c1c0b041c002428039880124041030000c1d8803007821030703880d0b600700080d46a00c02054403840040c4102451144040c0700000144003102103002110600000340004450a1046001c115007002080c44104116400ae80146610441d500c40034528183d2100d00402c0c08a820170f08a0415408108817004445d0884941505032550950a20944450b60040303070fa08e5101070b100070f00680345007800c44d54018a03940e03440b04070351910000d030042c2d02e01410820083d03800f00070241e114043d601011030680341e00142d200c0c1103030821 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 573942113 1250 573940863 573940897
    0x108030a1d0310020d0608061008120904020d1406091305030405040b04200d0510150806030f0d0203281d0103090b04060f060b03190207050115030803070305070203 72
    0x100e0296074090340c10a8000d50940f052540742000c00c03d40c2d00152189006040c0e000501d189008403035482c015016100030b50298494a0600180202051101c0c0540032440b9040d030350147d25020400070f04c00c540080031709602c7c107000105640500070032507000c2d081c111081c00c110b444801da050f8003c40c03810300080143d84104820001420150400c01e00c082000b880024050898800081511540c0301800041c1d00c0004000c003044080744205500616002c019100d0380d400c100160784c0c441c41500c050414481c64a000a005036400c20151030440c04a105480030020a441c004c1d58903041f00d41c40203440c0310841d0f1800081c20080c040301c01d585d001d980d91145039440c1c0400c803443d1417520710b490504054481c0c242d200810307002440303140214400c0c40700007202a040c600043c2101e10641024100001c01c0003440414259a42d0020205c1206400140c0c0d464452070643c1c010500030910358140014810000b0500c80848040c0d40321341c641f5102441150341e0b1200c201d0300c910680c2c80d201034403100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 573943363 1250 573942113 573942137
    0x10b03070e120c03060f1801110d050a1d030702031c0e090406020f040b091e090105061305030a0302030c0601080f06011512060f08160e04020409020d06150603050108030a 75
    0x8100450b016100390402510004541007000c03034101030040310302c4a50b44511009000c11140100f40148615111100803c03201d42c03500c110300c941e8800d030700303510402c41e89a00c00720303203e6901d65111034035100c0484540d450340410030000329100e80000d0170a9120740501202d1040080d0000c0301d8010340c95455a801d5640f80b5544104014158040d00c00d60705c5550130b0041078090740341c40000380302608036800d1091303e4460040800c1444040340b010020b01041c0c1800c2c5210715251240300f1419654202c401a803140b910441d2680e0500055010541c14803824198009240c0c0201c000c03d01c48044070141ca400382c0c0c80f82880c1d41d441e03401404601d41c0c0da000c10010040d08046402c0707290712391814a00900803011108841c41510000d8010b1400000c02010412096a081005400c0d0844d0601d034452558038014103054903110041020707000d1521401543e04554404040e0201c8640c056402c01005c040c00c2c903150403510b802d000b014082881c12001207486400081640d440a895540c0c1c0608421 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 573944613 1250 573943363 573943369
    0x80d180b01050406090e15041a130b0112050d030c051201091a060a0801050103020706060519090f0b0306010312030e120304050d0305010b07060e120d090b0612120f250209010b03070e 80
    0x7c001401030f580c00381e844003080c0480c40070040d00c0e409020540301004441d001414403a50883c01170b030180800e0540ba00492000520106400c915100d803802d0006401020728000e40d1a84640b480c03a81a04039101c0000c2a4401603502081694000340b0014103003058040502c14a4400d00000d100494041401000190701c0381d0000c00d80e19200b5100499841d50321008562112500381940100c00c00141040c0a24440383c45080b144030003600d424000c2550341c002107600d4a81c103000191941c240e5610a400d000d002c0e4101e010510a000c048035201c6031060414a80c6401c150743c221000d00480c0302c801c599620034042d0718161112480c4183ca0511281c0d00d00340200030940703000105004000d409400c1a07030b0600505413202c10602c002c50b201c0c000d4680548400340007464a0700c10380140d10100d00b5408000b5514000d826200503055a500c0c25061010603400384417034400340845241104031208609034040d011071842581d000c1110f0362a0303465200e442c0803c80d00c00300010743c5216200810700e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 573945863 1250 573944613 573944653
    0xa0c05131a090604080a05010c02030915030615032e0302010836030705070f0e011502120721080601210e0303040b0708010807030302030403080d180b01050406090e 72
    0x901c8284491404807500301243c20b580040e031043da0603402a0080d4011301200b03002d40c1c556240b252000d0b52034000e440001590700c4030711030381c0300c038440030b010000031240d44030314018030803072080c0b40d8104d0b0f102e03c0e04100c00003d000c00e40e840d12114140030340742c0c10240703062150704200303495058580e01c03c1c980e04caa007000030340101d8a015404040b16280501c440c802403050740325081e400d4502031541c40c03150b402c020749051410781c00548116041801000140d01c0b000791706043d6400c42c6409044000b5a5a0892820304048004460740380c0001c0e4120401040c48610301703085280c1c03106c205040e20300990541d0390a8044900070701049254003c4005003036443c2c004071922600c900c0001c1c3e052060b00340c0d28619001180c00311101ca8000b001d1205150300601030300c0c0140180b400034a01c07542103650080d01c80c041c0384001400410042404080421782da0807080c6e80040c200340510202e4501e00f401d01e4108001c1c46898021854498007181d401e4a90040c0c02011082e0380082840d0407203808095245 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 573947113 1250 573945863 573945899
    0x906050a061e060f050d0219090f0e04020a0e2509060923042304150b120a020f041b0c03090f2108070804030804030209070807080609070509030a0b0a0c0513 69
    0x3503420448c0c0a140510ba01040d204041143c1e00c042d1030074105420a0010105078102141c0300b1403001c1004010f903a0440b1000c295040b081c1c8030b0303405d80c8401e40040050f080101c101d1050310b01c2c0788103004079140e00c0552201100c2055561a070b0040e0344840c0302e0708017445250003011542090f81d9915440c2010f0f0040b83c41d000030100e004580d00c0c0703075100f41c0c402003005490840345804906080c018900960007025a004d404480075030802d9840307020300f5500c10482d030000740242c0c0b040c05403180c10354031a800703143c1e20000d2050710310b00180d102000a05035022a1800c6010484c0d5143c0800c1c05d24101558006440c6c01070b0080100c0a24581500c5110310502401c440d481010440036000980c80c001a00c0118818400c0d952168210b10411482c10b40c020000d01c00c01a24100700402194403a001d9500300c0c0041d140c640c89504c50002c119464840c03480f0980d05403140c844600b003000a507443d883d02c1948040e2041007182c000c498101c49902c1080c0040750f011103e85400d01145000103607180030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 573948363 1250 573947113 573947137
    0x1052503090810021305031f0905030909040506060a090c0c0201120f0612031101050f0402060a0c080f040906080a050601060f020a2001080a1b0c02040906050a061e060f05 75
    0xc00341d42c0e500c95443c0c5122241a120f0094001c103078010104155a56030010f860201d0141100390840312600c5000216500742281c05919241c483d403d125090045501000340a08250b03103074501814200d540340c4081c0c1e0040d00a0074803200000e1504d500d8810a04c00107203030780d01e0041c1001c668004407030404002620781c0303102d80e5416055803082e04c18804d000080000d004030780350000c141d0070301400c110060003a0a50700d074107100030004c0341c01501040030b9006904480c0180c4658450388200d403c0c490090b0010044000011802409540000500100d402c610014040c00d5111001c0c2610b032110500c00820766170080340140b06580c003a4007258501007862040710301003110303501e542c1c8071a02062035407800046182c8001d682035078840d010550107070500d90140b1010701140c0c03040889042501c10301d0b0070030800c01c19007070445d42e9a4002713002e2650416400c1c03145080c81c0ba0300c40001c025078400c40c03a250901c604114a080e61460020085401c241c0380c1c8520f642c00c844003a52284d0022a007003403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 573949613 1250 573948363 573948377
    0x308091b15090409030c1205400308030a06050f030309010806030a170a0e24031e0903040510080f060f01110a0c060807020724110d0509010e01052503 66
    0x1c0b140d1200e1094030740c0180a642c400d064081642040c2d001c094400d244002000004c125113100d00a00f440343c0108600d070360212005001d850044032032003034580c400805907011002000401e000300e850244d4011044114100044e907528003c00441401c80c003001c68054005001c41e4505600810106602c890043c00707407681ea6281c0c1e5200f040803031300c800300c000b98400f020801e1010b09a01c40a10804a0010b85c0c1640010956541d542e160b04000302c0105100b0500100240f1040380200c1d0000300107103510284142420318480081e03e07a08103001d0140620b03079005141c084a403180410b540148001008411180c541902340142c00e025254424140081c00030442c40d1102d0402001c0d80550140e50f1011400f8101503009003901c4d00a401001190300100080c0300c0c0030003010344011039081180281e0f40c84202c1100c103582100d590100c140e03450080f9006c02030910740180040803a544240e030746000c5003020710300648850081d00c0350758100c4c42c804440246503216404044110300d01a0800742 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 573950863 1250 573949613 573949627
    0x90e2a030c0a030614280f12060b06070209010902030702030403023c0618030c0a120b06310e060106090815010312081003050102160308091b15 63
    0x1904580c41074a0410400e440010391280681d4140b050700c016042000d07000b031058a5010000b44802801c0c1d008050a03082119600815600300841c01c2c0100341140501c240307650340b80700e000d6120008600c16a0228281281e8403554a030045c04c64480550080c410f560348d9007405070400094100410500543c84100800b00150303031a01c0e80c01c0e03984641c40c808a880c4154045420703100384408240c0e05015042558020a940d403602e082d41e40003654188034074002205000041d190840381b020040c0c000c01c01e0800402c030241d95034074100c07006006080b00c4bc4951100b030144808540c2d68802502a1070301d452029009906940741d03407008072880103010540b1002c100702c0030b092481c00c0c0c0c804070109941c894200500d41084c0204903108081941d07a400c0c561440c0c581d04030342d092030740d103290402c040c5100043e41d807031700b5991b40c0c0051900003000719146c8061084046d400c240340c2a06071302003104000021904000003420700d0174840d450394000405482d0701c2c00c0c800c0f107450020700135489003014040c0d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 573952113 1250 573950863 573950941
    0x1b0d030c1403122202090604091a1006170405120a181e08011e05060307030609080d061509050f060c0102030c030115020304060f0e040633090e 63
    0x10b41204040010010f4090070421402404e108440c2c042c2018051440e60100240c5e44014407190300540c2038902054082c410f2400007014154810913000d100c00d5141401034840542c42000140c030030741c2d00e82c0c8007142e640c88a034004e5240b017203a00400a034010b15a44100c1801140942642034003400c1004885c40b003030b0103c09070413540e42c102010a4001883e18440700001e4059403008003d5140200404241c1181d210454603040c1c9112000766110030210380c094508015940c01580c10407820441180c4a10341121580e012265a0800c9800c00f80045810405980030354150000364031036681042c42d00d424403080005292071945d0140042c403103450114001c0c00110310840c4103a04050f0350303605140000d40303015104c0000508560043c4020302c003082e0408103158a20900e410010007000a203000900a1324040d004000004000d002540c2c0000d11390300078400c80c050b8851110115503a403c4119801d107001c0c81085179180c1c881d0007003180314401c81480c4149560403040500502e003d2054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 573953363 1250 573952113 573952117
    0x14010b03071227060f1e0e0f06150312031e0903040915030c0f05092e150806030d020c010503090304050402071b14090103141606020f1b0d030c1403 65
    0x10b500441010005190404c4400d10541d07000200d215001c002004030300c58182c15920b4415400d41e88a551140c2d121715900d020400c3c20700c1d26502000326401441c0a08070328111030040c5a0315406442549508080e038030b00d12041d40c0c403604170b211282c130344c01c4110313000d00261600107031200c02d9030b010420001c18594614000d122048240d1211001d9840c61441c01c00c40c00c2d03041e41c0c402c9044c7d401b40d500602039a520100b1031500070003e281210700c40000010300091040001e0703000c0c20180681a00040e1404610b482010300c00c1617901c54421580d2800241929030911001003001a0004000104550b010360081c5400000d21030403a070501d40c072400850101e030b020f10016140401d082d40101480c445515524000e40740041300036845200750300200d014004103000040c03600c0742143c8500c0c4504810491503040c100000b1200c20b05541d070b80b101a40b21455000038040758020070036440b4008461058011026101800460500341c0300e8808880110450360111412a905c00b2110100841000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 573954613 1250 573953363 573953411
    0x90c03080d060f050a030c05060a02101803020f0d0f0c03050f031f06050c03041206020702040c0518030604050d050f0c0304080c10081504021809160314010b030712 72
    0x60700103070550919140b2a0b10680c2680302d20b2048000300d038140002802c0004010071104140c9015445c0c51034204241d080c4101c0d1520421440d00d88801070950107842c001a80c1e9a03402502921400a078822107551940d03d51114280442d8000802c0b105440c41001c0020841340a4548a0b003480201200300304d07554000d60741c103030104020701da0610308040c1ca41c66100c010251400d055141002c1401c034682c070303802984600300222005d24000800d005442d0100c0380c4559009008200076040202d000d0300e50b03001941100c1544d03507520781d02c6080d07050000f0130602075600040107218070240404200c2d05e40d4031020f03030402c44940920040c0910320041014002500d001000b41c26000c007241c06001502c0166005d010420031804280700841a685160980e44001510096510820764051802941906000c0741e04000302c03030f08000d00083d4101e40d0900c1008103940a0010780382c100000c80d1191030a004244040d03800f00041610a801088554134840b0701c49030228540c500209510904174800d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 573955863 1250 573954613 573954637
    0x3020301051f0602030c070b16060f0905011a090c090f0901060806030d0503190c1b030806120309090a0906060509190c030608031803010f240b12040303090c0308 71
    0x307845810040614080c0c03030b0183c40d0b148010340c108281c0003900da555400d644101580c1d0300e00045c10030003241c0008100702916400200c18081c4080b003c5842d0018641d030341c6d06540d15464042e00f140445c1403841e005c0102500200102216154803090480da40d005a030752540c0110441c000b5551502e500340c40c680284010346840c201864800140341c1803c04c400241410404100100070040304450f926094070346c416000003402401c260400d4503000030390111041c1000d200c0c0207030303801c056221f032049114800c00e0781c40c0c41800050310b41040daa8060800180d42c4202c00d800000c03448030301e039409200c1e0b003809100c0201c2e0342c0382d0b91404a122454180d5111440c02d48001101610041e980940c609041035460708001c0c8034503100e079081c0c81340240480c0201e8140503140310b600c00d607001d4100403151503003d0010406a408100300215101c04220203003503503500b84000003086190401030b103912140c0425900110740d40ca940850060441c140200c8a200344542e01001140c9440081c00892984d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 573957113 1250 573955863 573955891
    0x2270f0114040c05040303030e0f030f1b0a0512070804050a1805060904030f0e13110301030302070602120403030e030a050607020105090f06091207030207080f031c02030f0c090103060302030105 85
    0x11041c81c04240040c0010b000d281001c0500034040e03800b10842d001c0307941510b00018030300300c2038544034109070840c6140b842c548000303e070318082220410010305003440100051409841020000313502c0e400c2190010300a9040741c00c0141d421100070005010983c1315a00b80ea00d440c0d1903c0005103008030940140c94110f4440806400f800b89500c20a90010343c00c464035561840c055500815110f50340005400304803d4081182071a11011000118180355400c10b000840344402e07401e0064000b440290018420182c0c000f90090010410011201010812a291030f06548050b034409220341c0086416114070002030020a500303006a070700503c0140c0c004a52030a01c024a51300e011550010303480260024000d2140303180c0c000a8072a80044440056510f0320b010341405d034140950350380048481d000f0b0905600d904840480200712001c107450201e00640f0581c0150012808212040d140340603042010881c42d44000c805010b85403014900812116142d6000c030307003541c03030a40300441e220b84a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 573958363 1250 573957113 573957119
    0xf0403051f0c1d01031107080315031905060708060f0301020307030f060503030f040320030a0f0b0a050c180307090903081e160c05070509010e0a11130302270f01 71
    0x403405102c0307078203400746010030315802c0c64110740504106020425041c580d585103140021030000701640c000a802104031034483c9801d414008a203008803400c0b41c03207030044070182e03c40501c03000c0e80340c6105034215000300569911200c0a80d034108000c0d0034154850442100e01c6600c0e81e00b400250302c566881e6a002c10503441c0c050a0f0750558010741c201c207200350801d11074908001e26280035281201d410404c510080a64980d403141030000c003440081e0540107024070402803110000c213480c91035200d8018210350343c1e1040f0a031001c0b1042581d01c0c0301d4454040102e00d070400b44d0003945c111108001410f890031199208498400c81e5034402e011000b04004d50b0401030340c00036156211409075900703518442d80c3e18010405d01440002c05018400b40403d400001040c84010801e04000d840042e0480740c0303d58544641c20703041102100c90440039810f0040903107061102d0020b44058020030341c40852814115420080d10442440b500404206040115805e654114942a00130081c490811140d541 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 573959613 1250 573958363 573958423
    0x30b0c07172208030904050606090a0b0c060a0525120507030b0f030a02010e131118101110110c01061508070309172b06150c02030703080f040305 64
    0x42038050b019240780c8081c000700109440402103511402c0d003142e000419599a400048850051a01454001500300d20104400d41351000900705080007004940f091781c0c80f4210b901c10f0307032000c9650700b09140c1c0041d130f84041402002d41304405488141420000350310450f052908484041312100000394452000c00036a00f825000760b40006010b80c0900386204031500040c03d42090818041c1c02049105119101101d00341e10400e0303e0802c4214003540c44c1603001c0d602d41c11081842e1000d03c9403001c00c1c401e003415401a00d24258894890b0090105200c4544440c0000c10041c0d000141c600c3c800c01c0b00001c40b04080c407800f0040c0030038070207122141d440182e005119500041a410515240058940119800601d002043e20301689015030362040c800c1000c05403803410540000070305841c1d24442c80d8900300d80080c030564001a608016115900e10201d901c084c681c0006901600400d2040c40401c490a00507c05402401480752525550b42e50f0b080c508201d10301004e28008107015040c07078400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 573960863 1250 573959613 573959647
    0x2070e01272a17091b01120606031409010506010e09070c0c0308030a060807082e090606031103010627110a0503041101050a0203090433050306010905040c030b0c0717 73
    0x54410340901c2d8682c54613814083d03560305a501c0f070003644000520080742c903a00c54180e5030040b5075551410f01c2125940c0320040d025083c0500708401440c1143d0018030f000707030144255031003403c05940c2c500d2100c00b0a0244840640041d02d86410016001580008a442c085040d00154072880c00203640346481c0003640c044910b070340c104c18450b0300441e0b010454400000fa0143d22190000031114603520640202c5901c905a04020400d59080022400a00c142c55001e43c2c11240240e403180e015041010400d8201e40d107034042ca415900041034100e11902c0c2000c4581c0c2c04540c0717000001a40c2140000000700340d0000c1841c200059000003c00c03003082046449070121410a0a28908180c00c0b640c001e5101d0084c1c43c10140250754650240c40d041895103600c0c4100920202c10402e460408644812040c0c80d41c00789038042d20401000180c851031900c1082e200c4c0340c120940743d606605503900d8103208080504050803d031030078041400840c40840150004824015109a0304c820503400d00b4400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 573962113 1250 573960863 573960887
    0x1206050c030106080c09040f0c031b02030c070608060d02121e06040b2410020109110609010915020c06181f0540030302070e01272a 58
    0x28041c40100503290300251540d8004a5001d005500c8600c0031011800420100500c080494140040c41c00c0054042e401092611002c100803603a104a18400303130780d64406c20310b405255034402c3e00c2c200519407040703800c245c01000081c00a5401c1c3c0040e0001284170071035604000c402d030001d0384607680081450080a810f01c0c40d50300030f17244501d1325842c0c0c3c00035110010500030040f005549040c4072211500079210003a0b9004005541044034800d0081c001e0040d54411508101d5901a210f00c0740340c12003c6c1d030241c490507510030305118242101500c070b600709a65500b095110340104469a5941c14000c0d004054a4140012201001008005d03400141c184950b0a11800805144095a1120480b040c0300710032092140c006840811101188206130031184140525140c1d0381c1c0000d100710590b0040324000c2d406c0ba800a41c80d100194014003081c841e1500b14812045080e149805022601c0b8201121480016a6555101c1da400c0780c3c980320b4661106000c03441c01c2c0300303402a42140307041201d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 573963363 1250 573962113 573962131
    0x12010608010515011d0d08090117010b03062107120203031314090a05070e0135161115100b0c0705121b04110714030327150c0d0204120605 61
    0x60302891000b01e0807842d20a06c000d40100340006501180e80d01480e0078212003400c012488501d50fa5407180d81e25640c2041e2400c0303228400d440404446d40d0b05580c1c07501454400440075101043c6001180300d041001108101c1e0540018001522042c2d11444840021700400c01005003641c001d07402c0001021004006a40441c5000d00340940654400c00c194005d0381d081c01c284041b0006280107003450b40c0c00f0800000703040d002c0d15418854507400c00820340a4a0310030484294404a0b91045e10700881a11501c24103502500c950038140301c4601030703290021184002c0a6a1a40350808801582d001c03c0c40c80c400340d44601d400300032030304105d884400032540070000742241c4221440159102d07031a016809200d203403540322031414003001c102121040c5504c0040d0010b54400f0305551501d80d0422103020b004404001c0c074014214241d054040903001400f030103008a080f2007804200c410794054050308a1759024002540421040e2000704050800d04242d0808200d003894504141d81008000c862 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 573964613 1250 573963363 573963407
    0x406030b01020d091503050c04180207020415060206070f05120c070318141311070c0e010e041a07090503011104031e02090606070f150606081608061201060801051501 73
    0x105e80640d10403401c0c0e9102c0749800314817074030740e84040300181c0101d4102e0004282d015000f070311035080a500600300544291800c2c00400c25110580d0f41d403c0040c85060301680104000450340b0b882240301c0c1c8011091030401500303081c0f510116940c11042125907103031010380001d0705010306421800030000b01e8025500900302c07508104040c0074540401c05c159000321300c40c0b44581c9030306c20b194014200580c141d00c12252921001d080c00d50032111648600c03c024a0180300114185981082c0107101c0c0e600088849510200040504141000244a04c3c2048000c41011456580038040c40e0b080d08042c0c0865900c403400c1d41032813038001f542038101c030107240081821480140c85142074a035210348103c0e107075500c0b41041e06012454002140000b88052801145040140d0240c0e00c01401d940d080e0707a440c480b5030341d408007805181a07003c1d100d50115511030700040261909406460394030100304000300d00d1a0b95500c4060945106580765014010300c50120751140d40d22141e0380d1085203050440c44 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 573965863 1250 573964613 573964619
    0x5251b080c040b040f0906140a2901110d08090712020a1403030d0e0106060f111b030705060c0309030c01051c050a022214011d090a110406030b01020d09 67
    0x240d841d41c011007094010380d12080f80c5003095545511580c0242010041801600882c0c0f43c5800100741c00e100e0600c15030124070100d19400c02901c208803c0021035007100001c4064900ca081200c03040d28071140c100810a00320700c465840500550a1a8106848941c00b9007001800789080c2901c2d60809100d01b090f1040d14005a51a640c6c0c010440301000c2d0010400d4a001c40803174158813543d01c200544174141101c0ca41c24040c1503004204407595643c0e0900303500c0c420403040310303800d10707640a03007455600c2640038005040201151000189005048a09032070342c5802107035898000c401e41c148241c1020800410905041c1300e4040385000900c1d00c17520388003000c4900350175080c0841c49020407550382c200040c0d00e804c0c00e83c100c1e05e006144400c0c043c520303410002e000c00d500700030b402034640c100d55884030b444095000b07003214008001420b608186481c02003007403041403807004245101d40754580d58104d10002080300200f01401066901043c3c01c80c2100029141c403030b10151010801c03a15007010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 573967113 1250 573965863 573965879
    0x201020a080c01060e041b0e0105180a1b0203031609030305190e0d05060a06060905030a14010f0e160e0121020f0402040f0504141b0a05251b 62
    0x5801031980890640e4031441104007075401010903130009110b0011040500042c01403500095450f954101c0d0ba2072822a01c0d1800950800401e101e0b4640200800f252003c40700c0d013000405a00089200001556034950110b664102d011005090090307003000051120315034400c2d01620110115003045805103195940007080d44c0309821508030805400d0442d5103600c3d00c501845035201e000203200f056440d00d2420800c1d22004161a5100300900d400b100080c1c813030103406210204c850090141c04600c9080d1103583c2ea01000300c08070400d43d503035203401c3d03800e4507400c1c4100b0040c0102d202c020004801c1c2083e03600c0c01100a0740040710b00d501a07400401200c00c074245200c214544600419142802e280702050902d558070004075406400814007007100c400e460041d9080364800c031001c2c0300c030204140d0b8003c1e0010081d61000d812110720b03181c60359002400c0004002e00d10b02440c0052800540f220300c024181c0e81030100e103010500c81b000c000c1c14446109600c00d50124030441c0700380000d19284d25 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 573968363 1250 573967113 573967123
    0x5040f0305031f0312030f0e0706050a2601030302060f0610030c0e030706030203102309060a0807080109060b12060f18070806090f070e0c07080f0c010b0913020102 72
    0xc0c1001800000103565500700364420032400102410f80c0d50240d20b80ca03140f030304503007110103e01c0081d00d446445a03800d41c00c0c1c040c040c40c1c1e03001e220203402d8184c10264111a00c0d481a0924002d00c02034100100d5840440700000e40c0300c2600f0303881070b12554110310f802404d21001400700f0042d1001841404003d58603600008004203803414000303040ad1140c001669070f0080c80940a505002e0380e1000100e140d011307001107100e03482e020340610025441e0801e28110310300c5150642c400455071914100582003514072030b50130941c020211201580d407000303100e2510707501d60880c1c0340356510f60b007034881084020301844039038400c00c45800424030991814140e8500c0003d19441510620501280b1300c214042c074211000e200510942d403407075031a0008140c0e1034000340c6442c241445051804580d080004c52084251351100504224580307408100f40d515800444064031031200402200ca04110500d00030304400c041080041500d007071040400c90180b40041641c402d01c4020320070703a00183e0b070200d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 573969613 1250 573968363 573968393
    0x210b1203120a2703080106030b0d0f080306010c0c03200f09191b020601030c15080f0901060b0703020a0204240b131a1b010c0c11010c0b15130504 64
    0xc80040c030400d94103c10803030f18240002c03080707034032001e08464401d0640c03041503141a6a5107460500c0a080503209200303c06010540c0901804102c9010b040045e59201c011034205c0c005241001c629070b1541c488940030a220741c4111140030b070090a02d00400c0b03020180c4e65114100700c82e01120f1582800106690700d03801420f10020781d4903030707402142d81c4030307507134001d00303c901140c81080290980c0351400380d540d400c21300064503440312000001960b42080d110b01a114007459131221801d480e1503d0320040c90b9030180002c0f02039500e582c004111405428040d0130554000c0c0c2c01001d4954003030050004440c65940b000400d242d0702010a424401802007020803200b44030002ea0340c451b1000b28400703445881740c005030b420002d580681003516400710007030540c1c0e88059524600a40d02c03144031038221030307031000300e000416000a140c60110780503d070f00500191041c14072201141311627498949100e021590360a201d00040000703902402c1c030000a40064a15000401090910fa100e182601114030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 573970863 1250 573969613 573969631
    0xb07020f0f030f0a080a09060501120b150f090702120f03070f181802090301060e061c0b06010c0515090d03060902070b040f02030f0303010311090906060f040c210b120312 75
    0x5c00460504144d540c448074101e5000314081001d542c4401d444188141560340641d8146400700105039400c03210610040c80408c0100b90030703400e00c10002404501d1800900396400c1d0701900400070000022000104840528298038682e249003041d00540034054401050040044c030f200414950b4028005110558251440301d050603440201c40340060702c500c5c005203400d9401c003007000540d00d0b143c1c0ca01c0d84c002c100031110b010300d10440d0700e409601d400010b04041c0400c6815004108594000c100340140d0780d015509441e8496000541680c8515040e50105242c0e030100752040c0c0c016625108000182509a00030751910011740c43e0440042000b420103441800003a0032181159002c01202e8400a841c4003901d03101c2d07949041050f070b066290188140101504000103000000206000b40b00f440c00600101400034003001340001424542c0022050100030344070000a91540400c0309020f0058000100c1d6007014082482040784a07a0900e0566a10502010700d0034000d13494900c0c0d100d8110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 573972113 1250 573970863 573970877
    0x601030312020c03070507060314190c1e111e120306040212150a05060a1b1506140301060b090607080c0705280501210504020d0b07020f0f030f0a 64
    0x788504900910680500c1e41c0548000100e5508014002c00d9140498030192070400111b071342c100d052024040d0440d9950325465a4047e48109800240d020303070f20b19052850110400c9a00b1050951041001124003011501c6c000c0368140b19039080092004140402d0303403c0c1c200403114000b640d99800650384c10011020040006a010744a40d8152103982c0100c1d03240c07140c0381c248a4903483c2c50303c2c3c201024178001d800b40da9010890b81081021510254a981e40d2002c0989050204400030b0040220844244141c0960b801083c0d00d140186000741c18142102c0c42041c02c03030f10800d801c48103264400340500d841842102c0d640c1d0f6030b00341503985203134100d14501d540c0d6548404450070581c9d40d400c00c51740220301c5035201e0700c0f1080c04070790f00240640304d5100000d100e8945d40155192100c03c07035001100d4807402036600c101141900015006407002c0c041c9048106555039140214504072207410041c1d101c004050480c0b142049484409000c0344059032820420414680c410b1140365100020300008c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 573973363 1250 573972113 573972137
    0x506060f1e060708040f08010c020102090f0607060e0d0509091005010c1202010207050111040302010e19140d05030c060f2404051531050f010e13080a0203040501080c03060306010303 80
    0x240b541103640c0d442e4401001c2d0740e00c58449441032140c1080e8040d00c88650300c0c024450589500503c00c5416a41c00144200307507682d1098104852079110303010442d011500c0b502088582142004029855801629995260704030f80050042500001f0031070311100f1600501080280d1b0069007094408e5004401c00f00e0703040c04030b00182e0180c82a131200612641ca008200b6003034080c004080c001782c0780300344d948514108080041101100340c030044104118007400040190304180d80703c0102c1800c0c0500210607031012510b44506680000c24000c103984c00050401018454041e03400d0752045410002e08040e1401019032002c07103007001d20450107199036001082e000c4003455007802040350000d251140001c00d8404030700440c414200d03900b00010300300007023107070a911601070140704007072042c3c5100345680b800c03145070407060016180001130720b10046e0007408076162000500d91242e0b00c2d002142d44a107400001032000e0001040201d0006e010300900501e03a4000c142c19044a4262414a0113007503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 573974613 1250 573973363 573973369
    0xf011b1202240708131505090c09090a020405011a09090604020403061d07150806060a0306050d0602030415090206090415050a03051509010e03040315060e0c03040506060f1e 76
    0x454950002480155224071000c4440802c0107126803503550b20360600780c5442001c4a03045641007802444100b00c2d842d03034004004035600c0755070f011803180c04540b046540d80c808115005402d603001459a00418041c1c1e00b507007441d001c1c0e5401003140300388503a5081e0030145c105a95000c0c0d02110b6124810100c00310780140d949405643c0559013040081146d11280c03d4805540840400000c0704e50042000028064114030120307d14a403494a0748461517480710b04220869012051240030300d9a10440071846481e00c58088900300c1c404c110060380d9090506003419401e030b9a2481f800254146141040181c4030034050b2000c003a0f0a031408644079440380d10640c2a8215034009940015502707800100f444030000303400c400e5045000307208503030b500c3e0303600a9402e0302d8224232a10300c0d980c07042000f040001c0b1800f0a00b00c4000103440d0000758607480c1c1112244002c0282c5207c0c91400c0048103000a01009005503508400304a458082c04d003141c0c03010403103c080240703401c0030680040c4200820b0703031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 573975863 1250 573974613 573974623
    0x1120f0f08130b07020909072102280303030e120a0c0c0302130207140d0c0b0705040b04060917061506090418120801080601031a06040f09050105060f011b1202 70
    0xba01c10403038000e44904112003190001c21003070f84103500d01404142c1080d00405d14106954420140e41461150540c1d220100090089c04030303080403e01060390403550624104500008880c00c008241c20b00e1410001c0a4522503681011301d500102c00e680c048604500490f916035089080101606201c0e051040c0040c05641c40a5080f05101c1030b9050b5482c0e003a8010082d052084c40405c0c5852a482c20050b614080e80398000c003c030703a00002c147c011810303040016a006034545050340c9002d44580950790281c2259000c50007040c40c2c040300348240c00c1c42010a4030310003054001008245090003d5481c41445503150328062900050030b6150303500c0d2504140781404001600c811009510700e001600d2507088840320700081c1848002140490020801c141202d80190014003214840000180340c2a070241481d5070040c1c3d1484000300c03d001300e0190040850140c80001024501b080c103000060b5400d19841d030410081035001c85070a03052a95008a02c0d070802203030700f0a800c00034000ea10780 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 573977113 1250 573975863 573975877
    0xb03160e040c02060703181109060d061a100513210507031b05100f0315050324092109010207050a0801020705010f090f060e03160c05030601120f0f08 66
    0x1c0750070003041aa15503000150203000300c2130396604002c1228010001e040201c03c80030020062003110417070b4480c81c90682d07903c0e604000b0050588981352a1542ca1340111400c000729007522209111201c04103250000d3b40200100507800c00a1800802c07000c039000274000d5020315003038441c5081c07040396a5a066071404110f183e03c03100f281c2c1c046403039040103102040f03c100e224040001403040890300d8105000e18000c16416612010a0642e0f40e40c4c0940190180c2c0e2882440081e85002c0050303a558100694009004032140f030300c0e10f849003050018246480101030001030b902c038000320310824440124180d068030510584c26140c50b9042c00403800c100c400d501c0b9583c0700419042c00f14100c42c066000744051072040c0c0080025041c5031948034240c984d0161701929400501d03201c080030424607040071402c500c04800f940c0c03800302d80070901e403452201c180341980c5c1d0200c084400d101130308080085601400e605200340100d212260f540b41e04410f100e400041043c81100300324010011142c0544040b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 573978363 1250 573977113 573977119
    0xf03080703110c0703110d12030203150a181b020d080a1503050708070501030c0c0b13150b09061f0f09081e010c1e051810030506120105010b03160e 65
    0x2407a80c00c811a513036514250700040c0c8460403240d00340300c1189080041604956130046194078905885841500290002495105842d03020020b101c400e80d11000c5840c050091034000056011a00d840c1d002154204003a03544030341c401c660540312040c2c00180241c200c01c001c0c606003403240d0301c1020b50406401d840c2401205641c010718048204100400d520007550b420030100d030001942c3d840111b0941f00811038501c04180618401d101080100c141030780e000054a004000115041d5500990031444010840c1d41c1d5558039014075691600d656071507007003141202c5034103d90005a0004802c500d000f120703031061020031910140030310701031058103004180007416529640000d00c0d02981c003a41080e412803081d4a05110403400c82e006422100740241c090318076074801e803801c01050781c0320b510200c56000700c0030724032070030b2031055a800000001404841e940404d035820706000341b1602850010128542d6410000107200380c070310400139250302614000021064041414050b5980c011180312660 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 573979613 1250 573978363 573978367
    0xf0a03050f060115020c0604051003090f0602130801020306060a050901021203040507031203020703090b031306090f02030105280515040903031d0f060c2101030525030f0308070311 79
    0x70301c030030000c50060f0481c0e401c0c0343d91803151088003504985a50480c1c044581c45801401705000600703090000c01172508203801c0c0099010701e140c40f914102d00c50000200c0f1441d0700090301006000e0325024810081c1803000003503042d401d103440026070074080c1c005541c007044400b04035584560306c2041040d0312106a022101c3c0d8905050600035258140d030301003591016003003a48205454407a108581c54240c042c1c0e201004903080c1484107583e0751000e0300140040c0c02000d28003021441c01d1040d90b500d0b0f44103001d401240680b501c10706095400003004400070031500b401003410341080850313075004407c003901e000955640e0f0307c0480e41580c107041312154200385010000001c042d05a4084a42e8055000b0040501011803503204c0d03840c5203100c50424a60401008500c04442000190100d81e0524414108072980181840c0b400002684182d581d0781c866429441803019515402c2d0402d0184400d407a04681140c486c044078281da5000141008400800520003620907408511140c00b0810495 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 573980863 1250 573979613 573979633
    0x102120c090307060f0507141f0b0a050105090a0e070c120e0102010614030d2d090929060d0e0102031e011d060d14060a2306010e0f0a0305 61
    0xa000d40003074007070500a10a40102060b22401001ca113030405190340d50305464030040b580c13422040705001a80c1c20300b5100300074060406400000e118a4104418840002c0083d0504100841050198082418004100185040c0b030301c0b2080c089040e00c1c1280c0c1c281246490b9407008035118556403c0103040e205400070740001e41ca51100305201c216a00f640280602034540034011400119040200d900d54010f400b106c0d8003138000c143e100d004d911780700706040c00b42c1c41c1c0c2a0030003522208002c03840c00244241c0030070302400c1514401c501c005100c1c00301e14074020b8440700740c1d0680c018002014a00c60040450a1200780e0070b190405461003240400940d03c904041003120b11004040c0c00030124001c1c00c0300081100044108502e41d40b20085d04001c103ea15004140f210200d158401956640c0d82410b612046800070007423180a6401d5150008110710540808811031140b000741ca803890f0403c4040c00100d13a400041c0d540c03910b400304c13000310107500d13840700250319110703940d0004059000d20382081d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 573982113 1250 573980863 573980881
    0x11106010b0c1513081c0507260c1803010603050d0903141606050c2e0e0102070203070911070f0507260a021318060c1e0c0f02120313090b0a0612050405010212 70
    0x70b012440300140803027680e20003400b1210400f24202c500d40c0680e001031080800e031011070a0b03e01d07a094800f81c00024025100d441c0c160507e0340210032400400c01290080003048140405180c2614403440a044c1c81501c00904444402041c0725040810401044542c0c60820900c080e10320188804000c81c401001c0340341e50790585143e94510340b459807038404103440c0c104c4180201d50b211940100503140071418800d825008045258108450030010300c10400043e03102d01d00032100502450052824519046126410b8240030a4001c0c1c180d40c0d80f581c00701041c0b0000345403901d2a60488414021620041c0e0f80710080040700c10500049092081c1034080c032071254043c5204c0384055440074a08000b801e48409031100400294001030b002c03107015030201da40c0c101403c854a100600c0381c502c2c505000315403031458000c4a100d1030590142c180030469501a4031801040c5101034510f4541d50341b510a0150605041941d0502c4031a100d4000504111081d41254446000300c036400d51541840100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 573983363 1250 573982113 573982127
    0x1f020c100c1805010504030605040309031e0b3603090d11030c04020301080712080702090a1a0301051017031e0706060b09100e011106010b0c1513081c0507 68
    0x25000410b02c001c511180c900c0b02c490745202962410307141c0c0c610f03043c030315070715100100341c006c005404004800b100400014000ca003e80007000201031140c00b52045800c003400c602e070000d80709512181c035854040e50004210f5014452043c00c19000c4260140820718982c00d6200d11303a40a94446030881c045010009400e16519010b1816021151201e505005000482c84207018031300040d8018001000074049016000c503081e4890f400c0380d800d00310316501240000304281d61340d0050940301d000300402024042001162907008800070710050400440700050040d032801200080c1c0f070410701c440b99442040044a904c51141104482040020170350303004d40c4d401c0190111001424110005030090040d010380d845004001c3c201440500344181c155102e852400415044c42103408221010010900186008191080701280e4501140c10a141840c1840d800c4c41e0203904488d044c040e03180c85010300ca02a403984408807030754680e4291003000d0400150019903803402e0828040000582d0b04c414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 573984613 1250 573983363 573983381
    0x108040308063106240e1002070b0f04081b010837150909020a14011205010f0801231b0c03030c0403020406150f05090a03060906050f0105030703051f020c10 69
    0x344840a1490352040e03141c0030100b00c424900142440f11b820b001d0b850105c0544401c444240100e80155aa440186540d5040a480c1e210041408502000450300610800b00c0349141c210000c5805d0604c8000600034400142418407480ea1401c0304080c14003106584114003600e1406c0f044030f927150082041d01900441d42c03030001424070400002a91450340c020000d0fa80d50082c00e080d90319052446e103409050300c607030b0f01c58100015005003000ca520713544150741c0039012042040721000c1c2064200c500703580c103919030101000b10002c0c810340c81070b401081281e04968100791644c0e04102c030840300307055801403901e081101c1c0400828010404e4401c0c4c002c0c0122032007944e05212540d82c0e49186c80302503046040c2c10011900c4110300d8103c0c140708800800005500a00c00e40129031261281d9049540d07000b0220f98044d40d98040c02038010854510b02c1c0101001c8004013112419640c80c1a00c031201c42c00440320500c044042c10030025450f0301681d5000c48120115200d2041d1403130307041c029050b000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 573985863 1250 573984613 573984629
    0x1104180807060e07060903060c0507021804021903080f0a03150e01030b01060f02030d0507020f010f0504060e010b030d0804051911150406050a18030503120103050c0108040308063106 80
    0x90a200d00300b0310f01240c0c200c103c4a40c2e440740d001d45403940d2501805022010710400801030100040f03c0140d40d0090005410031210007501181d15085c0305110301c200c0b0f660625129460101b000b000016031140c02c0758100801c800c03030181c0f14030b11554290080d001400e035083d00c0d03160312003020a91004e1040713024100ca015600048060341d845070280c800c03111441003080160420001401440b50b03d402050f000142441103e451039400c0440c3c60858104921842a8a4944081c041800314501964030108405002001000f805000003aa0740c1c2c00c00c5512010304c150034000a09001041c0081d90a520074621440002c411618003030424440103e041441100c840c20b02500742018141603c0948401740c443d14500220401c1c01d031240c00e2803803030700300154202c0c040200009009001501030442c549080f0f124130750442ca000c03814000e560382c1040c10840030b2410232000c80d034841c043d650049000c1d0307181aa07400001c241d100c50001046201410007414084220302e140b0700f940642e040f02d02c42 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 573987113 1250 573985863 573985871
    0x13091a160c081b070b031e01150503070c141902100305060f0d0c03050d0905150c03071415090615011b03050a090918030f03090f110418080706 63
    0x80141680c0c203110501e40070349403410030320000c1580141581c4800f4100c221038100c40c4004d5a6446004050f0310403107004a400c0c00100f88078910b032260785c118901602c800c02100d0b00c4e8664206004109000061001c0d042000301e103890018800c000e03c1032400500c602c4155498107900d42c4804512079000c19080740181c40012000c14030341d1080c403d06000340ca0003021106661003013010001789612804054820300d103801c000100044040110441c000801d4031445d078402d140104111100d1180ba502c030700300b8502000090500000402203840d4603a02080030261075942d500c0031031070082e9800b840c3d103109059006102040c200002c0547c4104d080007082d2041032542801125200640c80d1031240c151136410072440024010740180003230161529113071440700d6507075164000392500300c02000e01d60401021150141039000781e04407490381c070030304003803003815603913550300c1c0d80c560320f054020300f60079024200b140581d42d40303801040b0201c210174441e030103160710303428040c40c1540140000c560315494 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 573988363 1250 573987113 573987151
    0x181d06130e1005060f0a0f1a040b090d061409070f2102280e07081005010e0f0a180b040e0a030203032e0b03041101021b13091a 56
    0x24600078459442151409080c2c2c1400e00a034a0002d410050102940700d00811320144c150f48031914040000c00c80f0b0034402c00300d030b8034180b805140100c807589400048038040005001d111650403c88031031420030303103903010707083d00e107042c80f03401440a240074644100303440c0c090010a103000114181034501214a07450300e1680d42040080c00c00011b40c3c5158943c441039a01800361400c40a480d1864503000c1c0342842d50385950f20580c081c0d421a800403950075549000384440b0640c400510f90744004081d40c540010713410640003800d81c8020000c4944528060802c2e5085500c03001e452000411440a41c81400020104030304017030585150f0b03141c0124501309079407910b40782c00210500c0c220b405802035491501d81404d414100c024400c0350310710480c1400ca03050364450f00e40048170000c0002d9224243c5038201458000241e810501c0d01a045600c018185c04002041450001880f04101d50200e0b040c8003d81e20103000e4113010802a00d22413204142c864440c2030900810310480e0840101601040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 573989613 1250 573988363 573988399
    0xa151404051503040212120d11070201080121120f1d060406050304332d1e05010b0a170c0d0209041e020c0f030c0d181d06 54
    0x45200e4560b210b1000700950801026a400941e0800d0000e400c0419004810003058508015880103004401d800519440c1110051040b0304444011800d580d2610390f20350002811440103004040020480c0000359440c0349000140302c1820350b00002040700300e403a20074058440295080c0b001d02141c0607001881c0609400d80c01600b410b10010b10007801c003418031004646036000100211001d516214820900120802001201c52031324a1184030200e003810042c41910000d0151004001450042c1c082c41440c10380305403500707440440c00244240b011080c1c4841201e00350b09005403145403100100740021590010714100361b02d0303101c90042500301000011441011642980c0001040c00b1107000b140c0c072038000702501c100040001c14150382c4490308840318511840c00074051640005c0b0600d0004040c802c424502c0c01c1d0b640607500308615201c400703458016000d0244100030040c4a50100040086075100141403007906410041a000000414519095420b00c0c4101410000d18171155 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 573990863 1250 573989613 573989617
    0x70f05011b08030a0504020d0c0b090f040203090a150207020a0e04030f05040e040f1106030a1b0201090b1801060e040f030201051008031207210501090b06130303110a020a1514 77
    0x540d000c4a814516502c1d03504e86001020080c0040b60701c0a810300c00740002c54052110074016015440c1c5c1159180c042c071003001070781501000b0503801035005201300504034001103042100309401c0001a1601c03401c1a545070000d00c81e05800a6200800801c04510101002c054601c02ea00c03940341c50340058031030070080e1034501447c40b0300e0409883c80c20025000039052800e50340028401c4084c0800014000c00088040c0c02c1103502c00000da0703a4144080d0550510060100307000d41d80c0c00204441030650f110049200c00003012581004c0843c0c0c500c01c0820001d600140040c22141214243c500301361520440d0452803840071740c019800c01c4081410000b183c5140001c8030402002185401c00c41c10320002c076410000c00c0c1ca4148000350440e02d0030002c0c1140742200d902c0040c00300140c00d40c10001d1400071241c0c00c40c1c0c1180685010700002c4003103202e04030200285d980508007030503500b11040324280f07007411600c0025004a0214130000d460190500c0c42c1100b001c1540314480d20f03141c8012200964 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 573992113 1250 573990863 573990917
    0x303090323060c0a0203040b03010603020901270e040c0308070b160e01050417010b040509071a090f06070c050d0803040203060610091a0f0a02060702070608060307090e0a05070f0501 80
    0x75420034000320399081d8151000b0f110155641c019a400d141d501c51201070a40c209900c0400440d40006800007150b034040d050f00129628000d00c81180d84400f0603000c084c09050068100001e0b4180200d028840d4010b400030055901490041e0b4038001841c200c000b41c042507940d1500038141441044003070b80074818500300004180d44030742c103041c0b0b4184903104915410071500300345e56850824001c59292406018807482444c8010b004d42894101121400340c1c02c12100500c006040c080b50245540d10320760329074458030444000342c8845203420010b030f5032001a8030440c4c4c0714041010550401480c640a544038900880580d50155241c000740118103c0d080c00a0001030503a440a000e180c0c1d4401350074400b01c1c00030390441c2c00c2c00d000080260040d80000359007000f5034859020031000c0d560410040c2c0140100d85001d00850400101103582c81059004400800b42c132001c544413401c104104458142da004801c4500180c0c1d10298a4020a80d5000b010300180c03015202110041400e4403020507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 573993363 1250 573992113 573992183
    0x90b0a020309060d0b0a060f0927090c1d24010c06270b0f010f030f02040203040314070c080c04090f060c090f0b0307021612062403030903 61
    0x40c02c14154100812548000c9404480030340c0ca440c000155140e01c4054806003d03e92541d11a00f511860080c0c0070001c0c9901a44960001c0c07180c0785443c0903c0000004500c4007140d0100b03541e1540c3c40c1c1000e0083ca81e802ca000c0e4112580d0100594143e510180350003101032010941d01380094070417003a1401080f000050118141c0441100061840c0d4446441c4c90b500c07940421500040c0b000c0040510054003054425030281c6042c0a10b058010309802c0c01080c030104403041c040d02c1d554444005410a0305c0280c891a4080f000900303040c01043c141d108074080310206a9590b54074a84156000201c0c00b80360710a100c0d6278182a600e040c944580213034582c0054005489000030b43d00d0201404200251034100003111000044802c0440000c0e405041440c000584074941050000d03c0c0000803041c0c0528110720105c00c0242903545078200241c2500014003040041c01039254145509040e02c00500b017803842180041859030202c440310039284074540f01120f0003906000794860039104441c07051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 573994613 1250 573993363 573993367
    0x30c1014030a24080c0d06200306090907030209070302031e160e1e040f0603060e0a050c090c071203060513020d0b0909030423030a110f0a0608011203090302030a03030903090b0a0203 80
    0x491b103882c12090035580c0c420300010404c14015509500c0c00d50304a9419030039100d004c130034045140f60449072960700002c500010190390b440d64001652295014102c3c1c0700b815030000c089600400103051020000c2005207242c1110f0a0203c004044580200c000d140016481c6410182d50310f45182000d100c00082a1620b60740617036603007000700400c444400d010300302d0b80d20b9100100251030740c006c2403e0f00e0460005403801448a080960400c40182c244034411401c001c10002d86c0102d84066404154203c0008075108080300c209400030006500b052f6806080503051008540c003e4009101d069100d20090241d032217200c3c284221440192000055a0814042400f10b0350f1814505000030080e0780307141c1648542d05000c42d0520302d00c00300c1030700d0115680c003032103130030303041001d80690b61000541d00d00c1c0280c2d04d0046c0081100d94180100843d49419114000506102c4c02c0035501458000301a9224080d1615010b40141220760702200850341f03c01000881d000864103540300c0b0003051700694 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 573995863 1250 573994613 573994633
    0x105010311040f0c1d0d020405011707090c0c061817180102010b10050306180a0902041826091f02162d0e0711010e010b030c1014030a2408 61
    0x3078402e031610f0717030403034541b4804101680d103d025290007028003503d150141e0b0710711402c81d401c149840c0c200c4c2c0c00c03050810020030301c10b9a2102110004c150010400566541000c002881081032490060050b41e05100700c0c62000301c4c8000180381445106003400100c1541d03400590a03224030580e0035900c90303e400108540203002d44002c5a22400003031800925000c111107481c400c1400b615400034090366100c141045050510030301804000c503803405e2026211694809005000b003002c8813410700c022907000c4258920181c03c0e100110001440e800780c5205110740b40810300c1ea403003d0b4600602c0b58502458007524100b020030240c6d162490b01050205200e02c401c03046512710b945a034000c0308559800943c034922200c05501800071980c90200c5001451110350a5554a003c1c4441caa490901c0c0450039a800091800c2054815940310b0410390340204192003400c010b400f84c0400090000410031503030900d500c491011a00b4540c00e802c10f00c80c84800c80ca602805002e15105036100711111 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 573997113 1250 573995863 573995897
    0x40e1c0e190b07030e030303040507090c0e0603041104020f0a1206050108040c0902030903041503020c0706050408190812071106010f06080c0304050c0307080703260910110105010311040f0c 83
    0x400f4900d00a042c050300c01011880441e1031a0b10868054a15400c181814040410a0300844500103014501400008038074000940d42d84009440241840c032031000c600c0a907110350701980c1910b480310011503140d05040e000540b88151419100a0941c41c00c10046503960140003190b001d560044a40c240c1c40e810400d1000003503101a102c03400c1c0f44018030001601d0300c40700c1e81d8170603000490340d805603c03042100c4000385850610703003009090043c00d0100340000c800000320010f9074035030b001c01100e6854080c103041101c0e04c211032045910300f03c210300308201e05070840c5508a1801120085130700e030380e80c0d88282c0c002d01303e000d0040d60f0004401802040100d5280d8000e55001170140c2c054a103503008960000e0716000503139002e0701c041c1e00800d000f00280106248440411140c514440c8241c141c010305c0f01c03680f131041300096440b88105024030202e0902c5844002c0351203031844000c0003d96120705204041090280703003507124909141e0884a0018075000304c50494201d612080000d4500c0800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 573998363 1250 573997113 573997117
    0xe0c091c0503030c071a0124030f090b01080706030c02030a0c02030f010920190911070501050a06090509010c021e03120c0a02070602060f0103020f040e1c0e190b 71
    0x901100c003640d08215a001c108284001d501541c00c3c0c21005a82e90414900380390351100741003000d172080003004010498030f41090100315900d028990002c07620981e80c0001e80c0103218108010301c1e250b2400c100b10040180c0400c281d41a2034860003196401a07a401c1c00f182a56426000324006803c103100d60301950b805a01519071107480101640d00e000e0041000508403642203105440c1030062640e8a440340c04105d60641401205660091720800b040190300903600480c4103203290360307a1303a03d041c03a044030300f07003090b1603105510000134011401c14810141c0948868020780c042c0c40e1070640816140c1c07005210703034120201250054140c40c5511072283c42002421802d444050004001d41140c0e2188400414031521204158075154880300000034076040c8690030441c20b45d4003e2080c0030980035644031807411680e0440300d4034800815213011801400410304110b0251082c80c10300480c9124000180c9000e04003980c42c0303010340d003c0b0ba0030089038440049203154910f0403403105002e0341c0001d00c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 573999613 1250 573998363 573998389
    0x3070309300201051b0106090b010c02060f03090a0f080705010506040204290d0e0f060a0c02060a110d06030807020f0f0d030e032104090507032d0603080a180e0c09 72
    0x44c01404c103012180c00c0d506205001c15894943e954030003061042100500c00d807400c071402072806044510495000c04d0480c401c2d80885042c074200400050412201004490185a44402900c00d400f489241084080e0070a98040301d007075003400005141810648252405c0701c010900724074048010b00c0313844c0b40e0f081190710450800c0e01c00700042c0000c2e905034051017512aa04000071314040043d012024100240038102050342c1d801c10708a0034003564001292030300000c0381c034000660581980d460781170a01c0384407280f180f800d081102c00801c0c0103108000c1c055440c000e0315804201e1000200300004c5200701505168080d000715400305c00310b4403445680400c0000941121082c0031000c1e14845d56a00542000d1111680081c1c00d000035900c90180580200782401c3c2406034280190a0507800b0700351580a010106501e0702ca03030300021150300312900071a0000f0602e585c6120031000203005c40369018130039800b1500390900066070322524110611a9600b4a84181044494000c0103400f020a00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 574000863 1250 573999613 573999617
    0x40207020d080301151103090105030103170c0d0905090a09030206070309081201030f03021c0c0b091c030605031e060103030c0206210703050609060109060f050c0f03070309300201 79
    0x80c11941c001080d110040d40a03013034190f94107503070720540c40f030080244419a901030384540040c4020032159800005407030551b40d004601c0801884d00e0803a2281074000c1c040382c2c01c2030344541448a003803290402240410358405440365070456880c2e00e10303001030b140c1ca81c174001c0041c0e1051002401c0c03d4483d500820400d07100311182440c008241d281c5c10b0a0a000380c2094502d1010807040b5402c060f010800ca5000d20140040c410b103a002c07100001e00403680310103010303041600000000300c0c9810300b1302099214408641d00c0d4910003486d0b4400030028046405414042c2c8034040d80a20f008002140000200c0c0507503004051503070071a5001c9a80c000c0c1c1c240c00720303001001802083c1903030280518950080000d284007840c2450084030040a0700d60140c0714901034030707100c1705110780c1342d0748995801d0580342c45003003070301c1800314200b4201c03106d10801c12440d86502625517498800b00010006040130342c040d56540641c0c075107410808d0b40e14000754086029100c000284000c0c01c444c46026450414014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 574002113 1250 574000863 574000879
    0xa12051515040e0f160b070b0c160c080c03122d160215070209040f050309040e07030611040e070f020307170309010e01020315040f092f0f06070204020702 68
    0x40081400d0b00c1110890f5a41e68000240c05038800c2c20400100c04030380742c0010b01e152140e26000c0c0c07040c1030344a007e002410a550520004e8a852845d004888103141049281e6075032101c5820b0020800d002d5001c1c07030b00140101c080080441c03500041c2d01c2181550360300101e01d00340c03181440100d0090070035a8100030b6150101c0b03214142c034072803010f001401080d4100d0b48003c6818810000b4010800b660101d1040c3c05200352805a2141100c095000d81c0c0b06600c07103040d0489051080c514020860741681c0581820200c03200c0c1e1201203100f10851b8400d02040c13011180c140c040c004030b800b540c0140300d1803414803c000f030342c01c0e4800c20705480c1080050060328601002d40e11003100ca42c0d006e150b20038081704000203000004009108200d81500004004c60031418440303090480103821201041c8290744800b6403011041d1203600c80315440d9800300c40d652113154108242e921192080d01e01c1e40d0701c050049089502d90074105124248032200a09c0300c0d00d002000d508010094000754400c3e0381240407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 574003363 1250 574002113 574002151
    0x7051e010305090c030d1e0f0e04020307091a120f06090601080c070813080f0d0906030b030f3f0702041d1225080405100c0b070503060a120515 63
    0x814030000d00701404954542c03c90740300c019040600e6000202002c8100045448d0f516141e50344081d0700280c03904200c030050b070780b80ca0f207240848107218141c0129000b02401c0c920b070250986414000c10300000c18034929940b550b90a4480411800111200c50700000c0310800a43d60b0b40c820980c0701d0b40404920030395401c00003030ba00e0342d0300641c0100c1d2000181c000090403d2000002c104250b203451800c03c3c00a004081580c24024508640c620030b0406040d240e070780020460b6000e11091080c0f1380082e04440280c1c8214980d10001e6240c0e040410303042005140e8a10500908007406014030342c106500da00c0d00f2041d509210041c000c4428090764513018892504500c0c40c24070150380e0050710300c1401c0e6200c502c2012104500000d040d548035058410f2002a0000740000303050f0b070220745007190811502c12a40109482c400e00724000140b94031007403010071062580100140d80240d100707441400c42c26848100c03003505020f892101400c42d9218000d8003044950110382c143c2c7c0401c003c441407500b555 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 574004613 1250 574003363 574003369
    0x601050c101d0f07051002030702031606030509070608070c020d0515070224010312030608160305060c0a050904090606050d0501050906090304060c030507060216050102030907051e010305090c 84
    0x700718109101e44540700c40608001c0d4000c0000c0204106a800141c0803607507116440595490140c40b629018129000e01050440e0092095a07165a006011360300104005182118040011b004141c0824504408100b00d00c0c8005000020b99007139071601201038960120507202040001030490780311810705c1c49080081d00501104616440004508040342860703040641000503128190305038004404d0341005060704100040d04407030300000324280c0340786a00c41c2140581081d40003190346214510b400344c580c0e25600078001c1100d0003002560307200d488040ca0306481e4454445200e00041c018840c00c10b03249041d83c0f24050036071080b203000581c00da41d60042881409012000e441c141d545800b000b440920a0004c65880001000550725207400c0c2800585007800184000c0c2c1003080109504003000907035411240c0341e03100c2c0b034090400900113241c841d02030350040321408968000c0410005075800d100c181c5100ca00a544818481c0c208644011401040010540c144a1203000c460004e151 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 574005863 1250 574004613 574004623
    0x6170c1903050f220b06041b0c060c0503040c090b0a0305010c030914060105010519020c21010c0f12200d2003040b04060e16080d1701030809090601050c 67
    0x10403644001c566031070b1081c40c540000c02c1c0208440345104002c40ca41204a4201c446104041da105008940c55200c0070301040003050b042e115140e82640020f0340b108521f4101c0c101c0140c4500c11076040c030a023501c1c224116014001a01d00a080c0c8850305000c0c0842c00b040e4200c0d8000c0303d0040d154000e40307981c9807200c2c4e082d10300320b504d1100400e070395400340300a010080c2d0440341c200109000401265260800083c0141308500000da410606046a4104a442807016003441c810051400100d506400010380c44142c2d9680d10002d0b5620f00503400b5170050166036040d031850360b10341740c80805903041406600078140d00c40703122041403031841e0701840c1c211058001c1c10450000d5031000407c05400d40d610103d0380b8002c4240d00d0022418010040020f00c00081650303c1075103c1008100d403c0095041c900c0e200780c20024040304002803101140c018000030300300504e203010f543c5c0c804151124010700140c0103c00c0c000a03140000c10001c43c03c4c142000c0205030b4100070180342140ca0291020f50b414140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 574007113 1250 574005863 574005907
    0x3091416050d110d1b050405100302040e19050d080108011e0b0f090103060204090c110c012316050c04091104020309150c090307060318300e031606170c 67
    0x20141000280b0b0b144210b50421001071b01042c1d804211509007009070149000c1c0e0303407100a01c81da072224503107000010f09000700c4c00b1080e580c0000f0500060907280007910360007145124000501180e00015400070140141180312702e902506003010350740b0688010241c01208520351700b200101682100c0c0d43c44249005d4000d6020304001a01d46040c4405081512241a020002c020140810015180010071640800c01c0d003400c20000810201d003002c1c4480265601080100c84007043c48500750000601030302000381b2440c2540d1410714164100021142d2521025040d03c0d45c19801c032074181002da000f95001716a400844400355988a0b41c1502c1d03200440d4060004000407822102604040202c03401034a024141442898035a460280c1e0f620b03291103026100c1e511900c1051607120300440000c984034080201d48000451446015140940c80d8520034002e100d018030440e540245004611300b0350f406903854a80081124000e64000c8101601d8900211000c00c11403107120b0b018440343d194 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 574008363 1250 574007113 574007123
    0x91302030f1501091b050d1503020405040b1f18020705070801020703120509063306032d060105030106050d0f14041104090c270c03091416050d110d 65
    0x150b40c100310070401070340d0070515105445c1006a0040c55895040800c1e122500301c0032000180c000c19114599100401c2688080c0d0404e14027028030041c4601c407035034644103030020001c661144505000c070700007200d40e91180e8001c01c1c1035408006800040e07030f001030040b10301134411501100c5e00e80020908a92041c0c030110b000c14000003000c01c0c0300c8040c1c01500c1c1d002d1420405841d091074034a1214061582e0004110046200008030307020010350f1502c8240400300142056440c1c0c5001c071703a10300711300c1d009428803084141c96400802201043e800010b04c42d640c1030756a541542d1030718006594a4106c1c6195030701e486c0d02c8150008600c2d07801d1181280f90611030343c528030141081d0401402c0e14a005001c10b00035410702d5103842c003007810703203800308216030320f480716005040e20300705c4040911011209408c1d041c0382071400703000030b00340d242e004146070030702641e03c01c0450540b21480383e03a6070700c04060342500d0b001140d070200064540800c80520a50240301840441c07210640001c98500b521101120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 574009613 1250 574008363 574008403
    0x4051003150b09010b090130110414060c1f0c09290319290d030e010810080d090603060b0c19020f03030c030a0e0906091302030f 57
    0x24000c0512100141e058020020840a0140c50100707180400500410a001c440022081c0c1503074403501e8070020540205110003034541da01d909450300c0c06801c008010b01c080c203085400807044600c80481702141e840010041201d20304509010380b681104c5174440183c041e2803a02006a0100d9201084120a480002800441000c00a092800150003140c01c1c4204255400521071941c01d918520122101c009600c03590740080852103001506040003e250600d011440440401c0c20a1707002d1100c140882661220140284468511000c0014000410380c0b00420030781e5024817030070b9810140a10b042580e194407210041d1138004111001400218103010030080d056151255202400c3c00155052400511004207035464020400601c0c01c502803203211411541d40050741c1004400180682e0780f1030581d03204031902c0e608805001c00101d904a5114411860300800007407081d40000d0084000344c542040300860210840c02c102d8051003080318401510400b0021900f819481d00c5d01c170f50b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 574010863 1250 574009613 574009619
    0xf0201030c0804030e01030e12040303090f0503060601120203090307170703030b0303190e0303072103230a0e0c0402040909020109050402040e0c0307021002040914090f030d0b0609040510 82
    0x5085072058034007501005030407418000020380c04041d8200203602441c011801d9250540c0a0342005803002140664440018002041540101400048482080800032501c1c0c2e0740b401d05444170021901745002980b4041c40c1c40c44200d107680656005070809040783e0138442c4c80d0307980c02d02c0c51698122101c440b0501144003003c242d89401422454001a0055070802c103a00c04443c4040c4480c0741c3d05018084640900300d803a0b1420000d41d81c1c4079030402c41890000298050142500000b02d0040000a060110103039100c00c1c901d80341c1e6485281e042144003190b484080403001003800a803c50918011076148415a40c1c96001900c0507001c0c1210001c0c01c00b00920014082095581c07045003d140144070401618844280450348050803040003079032541d0300c00c022414a01909101c0802c580301150214501c0b0301c1c1c0d40081c003086100009045240c549082d0369660326a11031030595550b20412040d0b03644440c5c1c4d00460100000901858246080c1c1d80c006410750360211550010500c0c906420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 574012113 1250 574010863 574010867
    0xb10030209130503091011030f040314010c090e22050d030f05090d20060103051f020c0601090b0607020d0506060108060d0b011202060c1531060f06120f0201 69
    0x30340d00001082c904030204280c96498644134050034500620800c0594000305100703021702000484103580e28140c03580c0b08104010381c00e480d0050b0005480107020a55913400d0401c052040600380e070b101e9103c1e8030241e0f10345918810600c50080c0866416104000008802d00c4214444100c40c0c0c8928081c05903035404140050898404040000b9880d00f40000e10403c0f400c040341c01e008945091400100f501c14507803540091810008079402107100b004000030600030b001c51142c502001550b1918800413114104c03d013640689050340b00039411031001040100019840007901e147c000c0c00c21410103085030002101e5040c102c1080d40c054228504018130766038014074040d8070031f000315030a0031000a280c542545103c0c05000c1c4241c1c80d041016030100f0f641e1200300366443d940403001142c02c5400705404444006006880600e44203a4800180c0908180408000a4202181c1c00014004042d80703802c4c1c00b805a04001101c016a105808540c10344cc513110b441031070f40100740131800b5003000e02c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 574013363 1250 574012113 574012129
    0xf03090703030e0a0b0f07060b090f0a0c05092d130e0105180a0308041703011d07020d1b0804080327030c1c1a18010e030c03030c070c030b100302 64
    0x20041c0305558118007032240d201e1003c146c3d15604070750031210b611169246802001001c01d4403081d0b80c071a0502e0308204505040402d818030a01c0040c6050143c080038100070b0b95107004000b041076202074114075244620328558003c0e400c400c50109000350070701c40e050215002d95000d0807050107154846a0b81c0210b00c0c001d020b40c40d00a6031140007095200c000800740d07070701c030711685800404114201c40400c052086070302044010300e103840f0303045a480d6500c10300305280e0030030309401100c40c070000c1002589160000c20450b00300722868561400701b07100031010007810f908035a0308885a003000c0c8401719608204201521484004000070ba40f2110344a4584a500300e01d5007400d8844d5111880340c243d25203a040300c91844151004100707101d0100c45c68020142c03210f00d801e00380c0141c4980c04200c400f14800300030a44580d007400c0204800500303002159180d2268401c50410760b40200045039000c5209001040028001e90591340c0b015180d50305c010070123009803640d660741c070220a01030055180100e5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 574014613 1250 574013363 574013387
    0x20c090a0906060b0f1204080418291c0206070b0901020408060907061704021f050a0f1701030320060f060f0904020f060c01020409022a0f0604080f0f0309070303 71
    0x1134164100030316000c0c03040c0203104510700290040c6209003c2800c00c0524420348019205802d03200b0b4601c2e003c640300d0001000c245030144c452001e100c071407412029220104c8070f0150006044844810141d15002d85130b1035201200301e810250400014002c111047c2d24140034203006400036913151302e0b0540b2103141c09800340061480744c010b0304c020040350380c00c41d003546580c9100064460ba44c0d901c500006090305400d40c401c0380b020810b050320f180b82036480401480200b501e07407200d01060441c0402104d80b119a030010302c1d84044d4240050000c280070700707402000b9030700942c0740044441144008904010099814400c10352601741402550b2400e030448041800090394101e82611307281d0001416817500c145114056400020000103000d000e40444001c4c20528106541d10f40c82c00380c12440030143d0381074080948944010520013a4000b007010f50b8070210716401031030503442e6510345d00010340c00b01c403172000c541204018916285020324040c51060b026a00030308151841c5080c05001440340300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 574015863 1250 574014613 574014629
    0xc0f0610170d0c0b06010504081005010608010614040302060f07080c160510050d0b01020106051507060b060f070305030903041502031209120d0209030307052b0201050c0d0903020c090a090606 84
    0x1984948480c0d12404005183c0d030425812004c640310320b401624a803180341c00c8030425002d80e04151f41104500d0b040617048036019901c00401f0380c0d2358a4200c07812803064071030034200350007000200094940b07000903004941042082510f00300307242c1d07201e0446904ca40c03054500341d048101d080c50202102c644020003014243d403c0f4188a40f4900c000380b2911504040300c1d0041c3d0f654100b45600d905c00d510ad90058100984003101071000d003215403605400180302190101e0404214001c2c50400340c040e284c81c440784c008141d0424a4968082e151608000c201102130f100900c000034010107610000c10078104541c01441d9141010a444810507a000f03042d461958051015070117031403643c0c022070b4241c410346400180c85100b0080007034214458180040c0c0644a944480303941d4480304201e0145586441c11441200180e4110503402ea490480d00310104100511012100b052190440800c44c0e101e071064030b8000100d040014551007051744c092103820340d21900482084518810a00079115035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 574017113 1250 574015863 574015873
    0x41a13080d030e01140610090b0c1f0b0603060105070615180b0927030706060906050307170604110d020409140115081009080409092607170c0f061017 66
    0x400079400507001701414481c050240309100e0801d1a110b01102409004008210f40c1d0758403044244640d0341030b05104601481c4104441145003400b0391040740c001d0754000d0809801c3d90745200040d109900130340004d65507952201d010340603411080b003565000d8030714481d0317038614101c94000d50401c84200c4001140500b0480041c0b00c5040c101d001c00803900500c41544011074545007080b00d0031801100c4008109500301880482c8803032881d08000207440e420340803181d58603642c03200203840145a18800140f07400400204001c201c032915080c1d0049000341c4000070350213565010030100c4441140c1511b95000b480036107840c2041c00e0180041d403108a100c403d25050800c080251180c0d00308500888881d07684a408080101543c162402030015403401c011001a90900498607604a034251038400303503e008a032100d41c5000b0076110207982082841e01e0051001f2100213641d801104800c09a10400104464a82d03003003140c94030581d0703101c214221161030192070010f21102004000055081 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 574018363 1250 574017113 574017131
    0x20903100f02120a050106080f010b0d150b070c0303030e0a03020c09070c0203060c0306090c270a0b040303030f050609010b161b0303020609060615041a13080d030e01 73
    0x40021282005404500002540d1548000c8070009105107412400d90740850320801003070034480ea1145d4101c0b4981c2d2108900340e0384004134a004518240207440c0b1218080c89403010302105039000c442e183e6000341464016a031500e0b56580e4680040c2d2080701c00d050036490034802c040d0b06016400c24500404010012400b41eaa00a0b444050b110600c038090480703800011202445407000c1400035401034240e5842d03062103c00110b1703c0e0700c01c80712240190310203800304401e48040c5007100d64144860b091003420142c907040d8550b83c420f030040c1c010750100942c231012540640820041009606c82d4070002000d82d14000200281d50b03008182500c0355441d034004001005409080303903280402d4488905c0174843d246400c00700925403c400100c0b00c00403490100805030002002d07400781104d1300486071165511010803040705039901741d40200342c809102c100181c0034030003281550208a003c102e0705060a101c44c03000481c030b03a98000e0700e013540b14100481382c075501881500301002e0070030020300107035035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 574019613 1250 574018363 574018369
    0x11010f0e15070606090e060406150509070f21020901030e0c06070f0501020408030a0503091009111201140901150608331e0411030f0a0507110a0b010312030209 70
    0x1490300308480214000b440340c042000700d501000291440900411140d001004130f281c2d140340403642283d00f0b6181c0f18144994a0390706001d03100701d172030082c1074101030f5842401c00c44911000608607401c0c07190140200c0f81904419000c0c0c42080c108000040e140d41c0c10000040595180040c1a030700d5411a8011803c551075460484603069040107074155107064900c1c1c0f02d40244240e034000c1400d80408103401e2502a0f0140003075003d5080c0368221020141109a56011900001c1005090442c026114181da04144c1c6a1405200c840e10000603a41c00040c3c0c402e200c0030048845c810742e42d658100d201804040d441e54a030241030a442c0c100c219246c06000d04a8100320358050754040030100c4805c0011001a404134116808042c1090044040790b000d1140c0041c8490140d520541c1420b805500708128070064900c10300c440d804040454807000d00c40d50003481c01030544010800c2581e44228031540800818002d0ba00c0740c1e81805107503140d424400c60034075801200d6004c05004000c4161035075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 574020863 1250 574019613 574019629
    0x70215090c0603040812090a0b06031b041503200102060708090a030c0f0602220b0f070609020111060705040609171b03070518060a080a201503010311010f0e 69
    0xc4060ba6415560380340d5043c002a0350044d007804801210802040201541021030480c0b1308501c03540c054038054640340c0400d0340314800064259900c55103029094524071301500300b403148604000301400701507103a0701c4012645520300141221349604011401855904010466000c7c1e0329280c80b604500784000c0c000d031100160880502040212900d40c0144401500380c82d00c07665000d6000c550300c85071411034071802405c80e10b02086102031400000b80c0c54840404890000e200144100d282c0992940c56500500c2d0741d0605074108900c0a600c40c1020004102ca58014402a11010f443d503144c81802068010150000344c0c0740000c5989911401d00e0005150401e0040100c0c14411a0300210200e4903016255100b10f42c40300c81040240b0f4580341c00040b580c054802a42c890710600d86400c8225075505410000134003e210b030140000403081071150300280b080008081d224040340064203000030b50800c0e00242d415800304065015a9a0000c100556030314090a090714a0200769002a800d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 574022113 1250 574020863 574020883
    0x605070218011d090102040b160302010c1d010804060608010c08041101030b100f0338060306090103080c192306061509030703050f01021309020f0703050714011407021509 75
    0x50050601080d04d02c0020740588000d01a81080300c1e4a44200003989140d01c4a802402e5016510700380c0c030307009242c2c8180b16054842800c5904a800ca6450780d004584022004006a138020754400d40402d51100c00c2c0100300c401d10042d81e803480c29091508100c0c401d650000c85840c149407030520745140984600500c0b40c0d00d0301c21418040e07010341d400642540074100d00000036254002d070f40880940e420f42ca18501070201d483c107607450148000c420030300610744000d0382c406078800e40b50001040010101070040101d40180c4c01616080c6a50385a104450601030701c0844001000d14142e4540d00c90314102a140241d20304000d001d00d06103500800c2c9500e8a1070113421080c4400520201c01d0740301040b140006540c0401110410b618165a02d8000d400c428210340170750020b140000b03041102402515a000850700c1420710700070a55500740c0d201e60004800b151082c3c5143c100d1000041d0030b08c20000420f04004042007513150000c0000c0c185005030001402000d02d4800380710444500003103602c15 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 574023363 1250 574022113 574022159
    0xf031b0506060d110904140115180c0c06051003020915011205090a0203030706060e01050a030c140f0910141c020907020f06070e0102060606070203250f060507021801 73
    0x103c640d460601246034811900190b821030041c5080c04100410081c80550703244290000300b1150601c4e20032503050305000c0c13045280381b550310030035032040e40100d5018051403019800c001c022100c855482006555046072174181c50045c1a00400030b505008204c0c641c41400940089c1040c0e07451400600101244c15040714a40c2c1c0c1c4800080e5411010041601481e40042c210307510b0341154585200903010700e0061b148030038080400011641401602c2d1800c2e20340c01841840303c0350814400b88a480d40c01c2403007581c01401e03d5800c8185456812003a80501e4011000305607241c1080d0b968000150303813420300b90080e14107600d18110050b1040d8506a00c40e81111030100c191074200c4103d00e840e0142e0035124281c0160010b221902c0d401c494101c850100a03000d84580c0d54801d02080001d000c1e9400c0a501130b00002c515030344034450034003040210040c1c00c000e482011b444200545d0b42d0000d40e000800030403000500c400c1136141c00901e50307950000303118404429604005c480803008454500b5200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 574024613 1250 574023363 574023379
    0x402160b09100e011e060f0315020f07030f0f02070506040e09071706090c0a0303080411010306181a1f0813060507080105010f0903170705010f06030f031b050606 71
    0x120038002440050b140341280d010034440c9201120400d4001c000c0707100c900301c16091902200da1440128000c0000301c84041e81d2103459149152a43c9a001c00444152031585500700106500f00207603d01505005010b0381c0e480881c0c64444102400345030300410b05c5415540305030300801050f41ca0a00322001c3d140c2c4003144816644038441d1880c505202500714181c281c1e495a51080d003000c3c0010704622841c00c050031246507c80a034180024040940809000201c201e00050003280910000d041c00c14018500095200e039120820760540e4541400020142d44441440c0801d020f01d80390124400c008030390b0700121a41a202c0007299041032a80501805002400034500200765040c52a0f46900304009000e14544644010020b400900426001c50600c8601030080c91280390f01c1e03000d4907404044800c4461094900c0356440d00044011a425922222103500c2100c3c240109401944a541d02c00b0030529189406065032040e0031948c042c15000a9903100410000507034250808001d0314111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 574025863 1250 574024613 574024621
    0x7140102030705012f0307020d110a0b1015031803030917030c1b0a0c050f061b0f0c060a08070f03090807030e0108060a050f060307050705150103020109050402160b 72
    0x1034218080c056003c3c12a5280c114440b20041103030020700b40a040030b003c94504528110103641c2540016191640182e100d8464100d040c1c1c0105004201c00d04c408044402c54034040c1e41c3e441021104841001c1c031294013031803c10010701e030030120480720310486c141801031038001c40f0100c0c84030b01002d1014003010344075482e40c42071004003410328500030f007a240f910b566480c0407222024242d1244044105d410054a0142c1d1113040200c2c8000305d040d44840c030710308410b1420040059002403110760a034840003c0100b407003240c039040784520859284601909650303aa009959090608686003140520030401c12603605a40c8041c46c568031544c641080c50040703058042c02c0340107000000000300340344000294601403607008030340721002550076660309841e0396078007050042d1030409110f910340004082c180388445107010780295600c0881881c01c14240300c5191602440c2c01045201c0c010800b407618014800e5581c0100c2110181ca81554107510313101c0c1456800004440d5818058804c03e4a00085 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 574027113 1250 574025863 574025867
    0x1605061503071505090d111203070308131e060b042a02030c07090c02010b120303060a0b1602090a020906070b1911030a0b0d0203060108100b0405040b040213091a0105130509071401 79
    0x768a140070b0220f45180300141d50300c41e501e81c012b400c254045441d00c40022031000c030a10441ea00b883c0d00c00e90150b040108501201e202403018141160510f480d203484c41081d4840384900c00d00403141d1108500c03118140a0801c601c911500c0c400c07021904200b00425480c81c00040d0001102c0030301a001912841c5000200d0040400f0200940d000c201c0d2180034008100000145008042c200c54080c4d04c2540c4107800710423840303101120780404000d440070002603d0890f4109910105200e0054500100d540000d40340c2d6210401c11191910060f00b403007045003141e41da0401f032070f0458900300609100d2415080c02c5000092512401646031002000720340c941125007810a07074040d013240e516584415542e41c5a242264602440600d40020b0f410036151038061103002c1c9400c070070f61a2654507543c00744070341c5009200949500c65145c0800000042580507440048280030407000d11950401c010030005a0245802c446420304000a000d8600d0000c80d0b203404a07400040300c1c841c105095001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 574028363 1250 574027113 574027133
    0x813030207030804060512250f02070509010306060608090c13091b0303020304060e0102160618120609021c03140313241d06010b1605061503071505090d 67
    0x7000f40031510126000a5464010010340003485d880300000156584043c42841e190300400365040300700505031110500540038400c0c15421030102d00c182c4e1200c0d600d810204200c144203a008035103242e61250208069a03000340c07440d410102c80c1006c2d02c080100030780000c0e00704400c40b001a40340c82e5a01950400c009001842250308004081007142040d40d82c14040e403a50064840c88002c22201c00d000401903102084001101c0055245804001c2c10503c5c100c59160b02340c041c1d0403c0901000c80414800c0034a4400401940b150b0400710b003220651050246807030a20007403140c40030b807440c1e8145c00241c00c0111a40386080d1810055180d031317078040004072011401080a016403891004140c03d25208032640884202140d4040c040c1951920000d81341844140702001581c10120044c8240403841c4002e003075030309007040c3c001c910344001c0c0c840c81d040801c05c0e0b549500340505030014049508003441480d0040c41604401c0145500710000038140d441074500701482005414152000c001c26911 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 574029613 1250 574028363 574028369
    0x10f1a1326010e070e0601051c0c09050a0902070302010b06190e0103020f0c160b0316050702031011031e13030806181e01080601060c081629010b0a0813030207 70
    0x100034400c480043e2140b940300d1140e0300502c880ba940c0b01c0002002d950282003120412040d803002c81001980035409032004040c8044290104100110009410303601c040040d400360406541c016951002407401900319450030100300c0c090710040c869083d01e00c0b120100300b108842a42811b1407000d0080c00101c00a1051519480152902040d41c1902c4000024003008000586907955502d9403150b035220440c0c002203030800c502000000201002c00c1c484d50203001c00300c0c80a0100c0c0c88040294200206580050700c100710740581c040100300080c000007411603040c8041c0c0f1101540c604008440301d0805202e480301805100020001c03030b0740b90725504106000c8104900c3e0005480c02e109000d00400c6861503403990a024911001103002000071400740d048a40b26103c1202c911003079550074860380c01150400d11509410f110440105150350b81d4000716010f282c01400714a00004a2481c1c007a4040e005030606000910559105c3d6400101080d0080600e481c050310001282c0307001c91402c40310f60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 574030863 1250 574029613 574029689
    0x309070b030c0901140702031c0c0609060f0b0a0b0910210b130203100608130c0b03090d170408130f08030306011b030801170f06010f1a13 61
    0x100880a0504400f0f00440c11003680c55181d0020b08180203141c078010785401a52540102ea203001d03c0940d00948500c1600c49401d120a00745c0c0e840c0c403010122152070b10b094503815114494000d400c0c0d460b105490342c110084039601030007410803044060600403010070743d004000f1113217910350450190806a804110541e09661507400340380e9410040d200707806003c1d01030028041c480c0410310180c0256849001000c8041c3c9585182c00002ca8003c103002d008000304090311050b040114594102e4034010341480f611059507401c1c20b0007036500e040d01100c1c1d8a020800000c800c8051070005980742600150005001502c4144101d00400c0032082944441e0b40c00b080503070000b81d68003000c8040c6115010076244c032010600341c09a08401043e08442c01400945840c0040c4003161108500b1080030520108070b0f450090b900c8161342c5011800c0e00240c1c101c1c0000c8004008204544542c0d501d060040c0751554149141035400300791811490040e1004c0110007041c0d14140d241c60400e601904444e8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 574032113 1250 574030863 574030867
    0xc0a1e110316111e04090303180605010e01050301110405090601171e150303070b041118060307080f1b1801030303240510110c030f1f1107080309070b 66
    0x1100c1802c401510010032202030400f2040c40c006450041201c80000d2140c4100ba0079a200341c1c02044000c000d0140c00f14181a501c10a4040300b002a220035075203980300313031030020301c95052641920703c00005074031061003681000c2c10002c0800ca44010381c1d044a130203580148258883d48010781d51080030007841030b58589510b08004c5c260f48880d02200982e201c800031540c517500d99100c1680d0a48110f403404c1d400d580300f00310400001d9002401c0a034402e028405140000c0b444000084218144441800d601a500800e1142e285810f00040004003040d4004061180d0306845a580b140030340ca040402c070014940072160903844032409061071000c00680e43d20b15684131f103001303402000300c100e00e140c05182c2800c10f16800109003030f061041e503500820341c2180722662141160514451211075420b4056852105810346081082c21070003680c10018101d211100b0707620086403030400c2c000300035890500c0c1c50518400d80c00030480e6129904000c0785540d903070f5801c102c0c40c60100c441d44121444140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 574033363 1250 574032113 574032127
    0x4061107080102031f080d050304030e0d0203031305012d050c120a05220b0d0f02130e0403170709050904080c0a0623040c09090c0b0f120c0a1e1103 65
    0x1e42e5030300c038005c0c441140364900b00b240c84031411075590b035285211b4004108100042004070b03008100031020751200400f6244500d40d00c0d40071900350b400ca14215004502d6011040c4442d41c0c00c40228050708003039030442c8901c00d0140200402c038418994000d024408001011000b495090203881006010310219a988809171344008201c1e85c4146076110346140b112041c120031200740c40c0c0d090704543c10000400c1c00c0100c0c214615008202644151900660030444500011040a06007000b841c082880d0241e5103400d06002d450000d03d03641c0c80c480207a09038104000103400030705250680354280d0f00c0c9401c555031841c0148031f070f110f512100e0300541305455014040000981000c0100310307588903140a04610b1160065000c0000c0d2801040c02a00d4035090001e0a840c1d0b010082480c0941c40e5000015070701c00718103c040c0e204140103000ba41d40010100c4402c0000220290000f0b1811603252504001d030800800c5080014540c00c40103001c0000074480f1842100d4440d40c104420055a5072181 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 574034613 1250 574033363 574033381
    0x7120306061b0206160f29070c0c0501110c03060f0f09060f0106050703092103110d081f05060d050603070b0c030a080405120c0f01140106020d050a02011805300406110708010203 78
    0x20100c03149480030707c1d1800580e4540c401c89504080741d03480b4992005140c00c00c80190360700c034404040c016031807291100209040d60200401c0740580c0c40451044200e08080004c031807140c50061516540742d12800900400a00321456241100c8031860440c1e1140d03528030301201c1c041c40f694010b03007001e0340c00380d03540d0101c94914102c41c400b507120303440e81480710610416040e2500082004013000c51090400145024000742d80d1460304142c40c202c0c400c10644a1000804035081413210262503661001008800e082c20031070b89026203503000805080c2040385c5015a980d100d11034071a420401c800020403304841003101011406603252031a8580032080b03881f03545d0b14031240f144800d0f5800e02d05e1a1468030490940179050b540e180d07001c0c2130603c00501003950154400005401190f40e44c1c14907160b01c2061031340340d003000c078031071005401c0208032614080102500c005920002032600c1c2602a8101001011541103400d6410301c06041030f43e910105090014035401720038113500001c02c010000c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 574035863 1250 574034613 574034663
    0xc060204121101031a0a0e1306050709060212030606030103060f090204063b0105120f072418051512040b1b040303020303010e060607120306061b0206160f 68
    0x108080e0b0301000682c1031034021900b403648482c00ea94106c240d4200c2441500d1054950304e42c01000d40d010802d0b2044240d80e80f008a4000b142d00d10002038902c10b0502c007899043c0403803e24003c05081a5046080460000f0036a100c184002842507a80740d0044200c041650000c924a603001001040ba0700d60b201e2121484e2549000c1182185100502e45031506810030702c0a0011025011805456824001408400302c0c0e08005050036104940d0b42c6071540f00c08100c144054640ca0064101d81218840490001040c00124605000d9400c80c510f81c40018980c0000840d413080744c0d120307003030b0180302840351a620449911a90380c3c09081d081000b842030110105010b5100703500d0003829225198101c03452405030f804000c0041e001000104000401e54043c07542050b00240002d20304191a515013a0034106400c40901090f00d0b003038100b152980008814041040403613222022030a41da001882c00d100347c20030500841c072000ba141c01070203100c22014a00c107911140141c9481940b040d20f404c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 574037113 1250 574035863 574035893
    0x405060f09120906090d06050118060b1207050a020a1e151811040e030f0909060108010e06040c110a060c0818100207050c0a14030727050606090a03030305011818030c06020412 77
    0x80d410204002433038400e44045030500c140141512a85485030f030ba003101d182d1b00c150b1240381148a001a44d102050342100d00e143c200c07003820002201310000d031520341c051040420004800d00e00d443c100f850702465041d076241145900640601840bc00200000d000300601e10460141e81701c0402c0340352038628448020040700710f0454041409940324070045032650030900480050541400100300a0b0030550802032940d00ea078103011350512019141d04d480e0507502d0742d041e00c200791507a207010801600324020720b410018040c00c00d001008000c0712650303504164030100780b40950001c1c1450030f0100900400426000042000e01202d9607035070300c01d220000c0c3d40f280c107100e030040381c1c0c0c00107202c0d41c8200301c154080d005884c1080c0841407602c00b08024000101090b1704560108280c00080da04c1234850750245109850024541d410021814149084600d0b040c2da03161504014003660740800700c10340103095062500080f0700c0d0702d07441c0500281c0070710303800005428140c00c0c1038810050140c42039120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 574038363 1250 574037113 574037159
    0x30309070806040f08030a0902100c200105220909051f29030a1515080307053a0e01020d030b06090d0501020c060405060f09120906090d060501 63
    0x5100d407280c907a1500c0790300607500140540f0070154460300103460000915030159903020001007240c6103402045440c201039500c2c40000d00410701e40c0d0200300c0c00452180000300400c2c03554824504100001c0c000c3d04c182260f101d5808102c521203020160b03282d80e400c029001c08142802681c0842c6402d40e80c528001d0a03041f0440391410f0203140a4182d84100707060b038183d2100c0c00300c604481c2528280d490f080307902070075054060300b030252011584610240503441e1302c3e40c400259213207000e002c48903510041e030082246a0010000303034001c650300090f0301c43e0081250041d030003488103c0240744c6200a0880c608550100140b8905c441c41d9006101716008183c02e800b51410860001821801c9540b154851039120b903040c80390740c08070700341107144040c0d440c801c5000603d172299501a4500d4484101c0d070444065105400300181c0c1414880003d401414240061951160210b07003141140503c2461032300520010454000300c0d5150410400c00d144c20000401c40395131199000c010a41038411030171a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 574039613 1250 574038363 574038373
    0x191203050316020303070c110f1801051c171b370c0b0f0d0f0209011e050703210504060c0e010c05060105040b060910020102040e0a02070308040b1b0408030309 70
    0x74602d80007000712485410355a65803070304c0c1c04450399100010704842180320f400c1089035100c400243c4912110780300603080401c01041c00c0d0b14000c00c00200301040440e180807901d940320400c00003042c407881580c084070501d0781180c81d208011000702032001041c1e2040c01911a403100c00600c0100c0d11152901c1c0210301c1408108a0b08105646204646084d8000c0c1030b564200d101f000702030798901c013801680e041010141d00d01000e03110180305480510700d800074002d41c0001c0e004070702c1d078204171081d6500590340e101149070406854045c02c20f000f01d9002505214101d03808800c004210b84000b0081e4002001c100442d042c0340c2000001032003200400c001241c1804e80500d8298010440c2c00c0c02c0580c0000100b000b6828041440050f140702010203402050a0041d1080c50340c41e90455000e406241d400141c0321880e10011003da800302502030a145481040f401002c01d6006803090743c010303008a0040200d80b286202000791020301c1020000110011074003080756640070001b940100042c5003124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 574040863 1250 574039613 574039651
    0xf0307030513020f010f11011a1903020105030a1a1305090606030304050a06110a0215070c1e0603020a0210051311030106060f0f090b070b0106031a030601051912030503 74
    0x91010b40b03100080e42c082c110014040185d071284001407841070346e6140c8104c2c1ba4400240c01420759640b52905400181e800e40321101c51304040700c4160701c034403680c4101480c6902c2d41e00060f0103480041d100486071a12000a0404420390040c0b04000c4c1c20003901a0b41803000c156816001800d00382e4100740c15001d00307070101d419458000255001d0320402001404002d1600b0003d440c07210f4140e01c542000d0040c6514100543d40b0f1a14400007180800c04441da01c0f101c600d0280a1a03c254014035080c0c002f0a00003420364040050200c00d071081410016642c03058100168a070080f02410201164201070400c400004140c28040d0f502e44650101f9043d400050101402e03103255006040016044400c3e03c00100e1140440d66000c05190400d80c1c0800d031a403582004c40e500000068814008140c0100440356041c8140c0602480720002086841e01050000f52502d07010301c1018416845003102c0805120210303440c1005040c0512000c1150420780b81c043c160707410840340c0c4040420244400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 574042113 1250 574040863 574040881
    0xd0809060307031406010c170c1501120b010f1a0304080702150d0617030a0e010909020c1f3305030609060718030302070b07060923010608010c050426030f03070305 72
    0x81d4066110031980310400581640c2a819001404040c1152160ad0680820f000c051a0014060f0001c100d80383c200b1811420322a00b444c2c01a4000413840340d4008040105c0400d1445c3c0341c40e5070807100038a0f507591300d13981408500d6000b104000b0f940800c100180380f50501303021000b0700e985078124000f4059030740c0c1c603180d24140305404105070900c0d0f003040025203c070900c50848070704542414103200482d19203c5440c0e00c103c2c1c000038502038141c0c3c0501441d0460400c000480b40002c40c00003803d2241e220b5140311822045c0340c04180340d50415401d50305007070610119007050041c140190884205140c12941c080c1d0300c88040c1d44810200d0040b001d504002c440102c040c0c0d050700c4d015001004c000307141c40303126043da03404094140c541c140d54400c640700203001c00c441c3c2025980c110f1814014203459031401400c45101d03902c00c1ca09689400c480a0030640c11105031000c1302c4584640c00c50070b241c2c0000701433001c0174580307440400303000005600303050b009610301840c0a82c03185e0707070300f0401c9644011034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 574043363 1250 574042113 574042127
    0x81b0f0c190b061e060906040e1501030513080a111908070c0e220609080705010b090606191b050f0703062f07050c031b1305150d080906030703140601 66
    0xc4c4491890a18072184942d0a00d81c000303046c6000060f0080c0e1411b0390302c0b51010900701041e1000344414040d208140d01c0c0e0340e0325010f0a900403e018a142810089503a100300f2244103044210080c8414601510f01c1d51005201841400c0d02404556842c0e00c0c040c5030900460744500c900f1100103154500c0450401c0c1e4259140388180c8119108901121100389a51140813052100b00d4581e6103ca0500f80015154030203014843d1140700041020042e40042100c0600020062406040c040c045101000a030000c020312503039031400e001044629100c040406000003110113001840b0b82d0521a00d842e00005102c01203c0c000d1504200c807050300251700c204032003203044030301354041450105080c0c1c890381c40042c410644140b0403070342c4030400c0c03d000c2030a0283c14400d031b1484942c40b666030f5009050125008440000d00141001107282c240050642c2c0c2039007108040c02044100a240200043c5c0022242410300090220b070312850003920060160400494140303c0a9600c030201c1d441c0e5000304d403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 574044613 1250 574043363 574043389
    0x91b080f011a061b102306010206150d0201050903013303021f050c01050702010501230306011203171005040b06030603060a020f0708030103060f0606081b0f0c190b06 73
    0x43da5180c0701c00003041e054032203400340c944001e602440d420140085150b1251003080e481c40807032441140c00618041010800051a440c190b4014404100c4038881215189440d444100c030071804128042c00100d41c03600940011642540c64146d00d0041c5542c91041c1407010b030140c1c060b01c070700d001d0381144140c507516103840300035002010285994800340c2c1c4400b00b110440040d140090510305090815400d682c01a01c0b84000740c0d5650005001c07082103041020011202d11a500c4547d00c44000130a550380790522404102c8d6000f80712030030170948140010075a403840698888000e040420002040d050280307e818480c030b01e01007410080381040c03c107403841000010081e10381ea54503a100c2c84040d41c81405d0750f4103c08001c01c0ba2400240f10b0364051400707540114070000b44260380784c00110880703229820075410700009408105807507040001036808902e40410040d210180c080210a20303001d030384040c0c0514098564a0030301080c8104062441c0c5c0d028802200d100d40300d40d0144a01d00e510b81e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 574045863 1250 574044613 574044619
    0x516080304060e13020a0e09060d0c14010c0c030302010516110309090405010b0a0803120c07020303030a0b010507200114030c180a09090b191806091b080f011a 70
    0x440200001c1d800f441d890540500094003411007081c40000c0b40c0d04981c00380441c0408650340d2200155141400160703e5803118090f21301751010344450319100d0144042d07101da6030100c02c802c020752555902ca0022060329030342c00b075258030030a600c82c54081e000e0001221084110085410240c070741d1481151500c041e40f0558018518040303c01e014000d25800041007a074080d900ca14040c0075507180d140c2210020304100c0050342d01c4507081c4203903800c00e81014081e540c80c0c1d01c05110b83c0700941c4c1c000c81180c3c2c005040e900006100399111006030b031030b4001c80101500362040c00207643d0301100065503ca4002d0802d0781d0b80c2d903061403032140c080d0f4203000a4a88a00886041c0898a001c520402c50044000001000c2d010702e66520400302055030641d50080b01d078040040244403080b1135100c0f44684600c0a02014401001803240c0030b40c05c2864001c019050340d84900207a014014071ba54400039024141d04415403880c0c0742c810b050f54a24046e40160b000398a050400901048656481c0324044001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 574047113 1250 574045863 574045867
    0x1a07470412020703080307020c011d01020c06180406140102160320130e0309010f0801030f061d0601031101180f0312090b0d060509090a0f02060c1e03040305160803 72
    0x40d12400d4031015012048030643c40340c00800301c0031030380c2000550300c40c1070117034010800c1c400c024000501080f140d1964881131605044036082c03ea8010540341541c1074107441c9140ca4412200c01e44580d500c1000120303401c40c2c5042c9022820310241c40b000514180b00380c0031141014401044403004460314403008d00810309880c820f40d040e9504a0402d483c0140040c03e45500405916848084445d46800d0780316aa0000803000c11a5070880500d208000d16418060036541c5161500310404442d8a002090b090fa6004030510f141c0b4600114084429444101d0b032103076031685405071280c654012920701188180e1181c1300440381c1c1c040070106480000180e20314140c911340e80c45501501c100c0030501800001000401c8038142ca41c050903c1c2814254041103851501c414801d9201e40600491400d0f000b0700c54180c0480e8050922030510f50341500e4056603048050030043c18040c2e015000d005920004030420f511500000150040e02d00442c143c1e594000100c030b02d801d9000303035403040510940003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 574048363 1250 574047113 574047121
    0x2060c2d07060c081e010e1e2403060921040b07050604170a05160302010212100501140c19060b130501031401020a0c030804020a240e0a050a1a0747 65
    0x3103980c00c00d0700503003101d20400800e410700ca210b418208c011500c03901c6c1143c000c034014001e0b030041c0307645101000c419400303030087d0700380b926581d80c54025544600407a01080080d40180c120384204540040c100064501e0701c400c0341c0d28000340c07514404d94056171110340842105001c014400201c40f46911251501860013000b011711841c04820004141e003036541c248030301d54880f4424001d00d0b10170254003414602040c02e00001500741002581e540254450600924000351000034840d9914441c02404052032880c518140c8040c0028640181d0002009050020841065000203069a03caa00041c0d2101180c101c80c0d4203d000d14842c02c2e00184001103007402083c0030351215508036001070200107140740c844c0415200321030803c0d500e1001000c0000301e40840341e80044010080c580031a5504100c929000010301d110210740504043d001c2c0c01d142c440f0b404110402250700c0c1a500208071a0046aa000529200c22200d507980412401c0030342518a141e0422448102d1080c02c0342c101040760315 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 574049613 1250 574048363 574048379
    0x606130915030b010e0906150a0501080402031c03091e0308010b0f0d09110f0a051f0306090c0203040509100605030f0601120510080d02060c2d07060c081e01 69
    0x40001401c022a20000c04030100d0314400d00726000e440c0c142510b2a05041c9540742d40d203030074001042c02e000403c82081005165440c049014103d40302480e000b146615540002070810350f00c43c89442c4048422144803032195010380150858a000e040c50058144151050810b0303181003910003800a10040014000582000c000d0300c000300ca1391810a04001388010f040b0211344540c1e00a0b87d1010740885609141d262a00d91140d07079071000e0340e200505919040218202060780100c031182044a0481c01d0b10051081d440344e0002c00d40b5610601403c15542000707034403035019010310742c0a4112000010000d209d03030034505044138541e580e42440c658075200b00601041018002e2410400c0e020905141c1d9245801444d00491291103a0b8400c00d1400f011545418502c103448001e41d017091040001e912020740030307108501c07880c003031302d07003104d11115000310f503072100a40c06008903080414110240402036000d00c8010035140c0b244849600d501d04c81c000e100f4050750204c500e04600e1001402054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 574050863 1250 574049613 574049621
    0x5031204150903050403142a0105120115031b0e10030e16050a0801090213090204150807060207060c0f11040b0a0801021806070f0b0405100c0509030606061309 70
    0x14011240798466445100c180c00c26100b6124055002980124051007809a13115405103202009001852403401e5841580d0407000c1300961802d00351120200f445240e40101c0440d040321414103085140d56849030078003080c17007081c1300501c030019103000d221014510503000e0300e4a89046a0710f5124000340498104100844044040310806840b1070007030150705402c00c118a0303045d0084801c004c41c1403c001c113102c085000c0d90720102d01d982c1030150300c0c400b41e00c44600c0e103a011001203101040d07525043c00800d000d016000b942401c00e10840d4000500c1e2000400c4000540d12540d096031413007541d0700d170201d03250012a1009001c1c0404407003030340d00013000c40c0a094102c000250010070031203100400a00c50742101d501503059039400081503202c0a00c0d4908045103d4400c80c0c0550400d040c50b100c80c0c1c000c1c031110000038070b480c020001040a00c41c0401c20446030000c0020207100e080c89403a00140726400407540345000c0c5c41040d000c00e406140a2066442d01e00301d8020104c9110302c0c040880c4064 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 574052113 1250 574050863 574050871
    0x10602120a20010504031106070c08091801060c0c05011701090507092706090c08041e17071b051f0309060c050705100204050f0906180a1a0d050312 65
    0x405014542ca00c089009800001e00540150000040354500b905000e4010401c2d41d40d882e03250340003c1c042150080c0c00c45079040b821b50708235881548448042c1d001c100e0040801c07500b001d000038007400001d410303540f0002c51109241308500100341141e0300d60065030440c1101e8800c0040c0001080140b0564a0a80c00340364001960300e401c030034144c4d43d42203082a54911080811481c00c008010008441da640116001000956820800508214801002004068001000000c0b01008484441c0071900c00c1e0a06580019213200541c101c0701c82e159040c0e0205400f11200300010208010501c03c13880040700f2620701601c0c1d020360001038540c420030243e4170750750300d41455592a481e00105d5400d1198500d000382e140c5503190b9074806420001c0c41e0402110384441d450780100000e102d9601d400305c1002c01c0180589a01d407583e00c07114000380340c003001c4821450100050004100020000d80c000080710280d46c004c1e180340001c100d0038131010450a50300070b41540e05c104403a035401c0c0c5c6805056944 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 574053363 1250 574052113 574052117
    0x218060a090c021c020609070e0907060f020a060c0302090f060306150d060b0c0f0c150a030f09080309060402010e10170c0c03040905010906061110050424021c05010602120a 76
    0x5120301408401c0c10049000d044c0100503400300080109012040110202034100096103030924078111107003d55800c0070b40614002c000d904608029003500030002e40542c0b030740c04181840b0130342c6180b0f0001d0080d00f04030752103480356a600d0740f038a0071030902c202200e004600c050103001090f60945070082e410342c040390012114981c0c0c1c4c0030010301c103501d4a0141600c2075510f4042d0800340d0001614500d0954203841880c41085001d980c034004c07642d224211a0900c4140c10701080e0030721114061801062030280c040c0512100004202c00e401010034507a00c1140300b6201ca0340c418907a1014000070400f5116a40b010807000c0c141c01028070390316524564090b07000100c0b03a00d00300350518001c0c1560001d0713200240e540d896600501200c1031600540010b80b0561a29078040f41003c1901c2d940c41c8a02034644000c1a03a6001003403d0143c8803006481e01c1c0140c0900141601d0340384800340c005c2d03005061468010703410f26914522103149010749412a94254000c121071420340000c1c00c810380c031003000401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 574054613 1250 574053363 574053373
    0x60c060b060c030c0606091e0a05040503040b0406020d03050702060c12100510080703050115120b01230405091b04051005090406090506031509120f0c06090a0218060a090c02 76
    0x10200c00c0400003414003030344844c068072180c1003e406000a0716005000056090307451054246109003495000e40e00c800d488a02240d15101c0b400c4c2a8214840d507000f05421120000c6c010811540004146e09410b00c5641e0800c441d944182040340c507410140c07402ca46980c81002041c0802e07181c071012580001810004054103070343e800000746505d0304800684082a070a0003007240d2a601071017514010700e08088000b40710301c2c1c5040300401061070b0a00c86411141d403000e070504180d11580c1c0404c8000c803101c64007400009203a40081003904540310303c42c8241e024000050100340010440b011f0503100060311802d0a0500f0104003e411941104c6010454203225010082d070b294040ca500528141c01c001034141403440a00d81000740c10001035107081c80501c2805642640003070b03800c00c0700074603e402d242c9960007850100c2031442030301c002104512a0100380201850b000c210461a40d20841e803d056040c0310312030351030103a40304441c43d5601040301c0b88200040d442030341004000d45041c0c8140ea03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 574055863 1250 574054613 574054627
    0x3070c1103030a03060f1d0f0a2c010e07030812040201050706050a05040309090b090f07050903060103123f02071e1b050306041e0c060c1b060c060b06 66
    0x1e4610b81240301c0d00f07800a03132603000812580c081400e000c0041c1c00da0401d09000038080070807902c00c414018082d501005445d0340010181400b40d80600c850350108000040032034140e80b140b590480559809604075442c0c40c5015203800c000150072411203510080c09424040c034803180c049802c20082c416410b0001c200004000a0540c0c82420b1141c0340e81600000c2c24146414014541d8809800111100e880d051500a0540d602d920007940851825115210b540e91190115a103000350703604d0300d401d84140030004c000c00414001a000480c101d90b42d07000c080b203181810310b005032003c000e00d1081005400a16001e0307079402415040e081d00c189030252402c0c040e0303510002d51a00c0000c0c42122100300c1c2c5040c0781040303166440c0d01d111407035020041000b1070914000980350440540700524854503503490302e414038a043c028081054000c03011700040c6544000c00340041042e0300c021a120020242404505645100e00105843d40b603910001c0b600195502e81d0010f00070480707100d41c0244240002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 574057113 1250 574055863 574055869
    0x302060322050d03060f0b03060d0c08030c0c180f0a0e1e060a050f010803090d0204110703200d090510030f020301061d04050103081e130e0105090a060b03070c11 71
    0xd0401520402c000d00d01d4250040e40242100c2d0244c00c2000c4090400340d003040050140000e69410580032120f9020700c442d1403400207a00480b43d40184100d001c00724420700000300116200105000503900c03d8421800d03480c0c0a40074010032120141c03807a490b000420030a80359036020094080080044812105480310f503034403c5001d076402c801c3d141e445071041252040070fa00902d81c000107043d110300758030350500c1d4056499000740901c160081203004c01e050259038842e0410450034900194981d40d44180e4103000f06540c0b03920f4501d1202c0301d5090080b905c94040040e03071185020f95560f95208041c208001c0040074160a81a0801c1503210046040d440a140c80218001c10745502c1311003900c00080050a1184100e5081901c1245003400400126609504503401400f404442402c4482d81c0d00c50f0181c18000e004000c541c0008944021403c11241085641078030811a604041552007042080a491180c082c401100805001051120780150041100a44201030700c07a4800711003004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 574058363 1250 574057113 574057171
    0x1b0c03060109020a02010c0309050d390308180a0311100c050405040b19030f02060c03040311040e0123090114100303030b062104020f0306040302150105030c0a03020603 74
    0x440b5203580001c00000c00c42d02440380c2601c2840900b424040706a9a880b15600c0e40b4580d4440000d014007059a01c40c0907108c3c030040502500e14607174400382d0307800c460f07200f0f00704403400301c0704030045203480022580c488151800c00d041d1800c1140140f04192103036500302d0380c0d5482522510a54418004d94000500007805082d8001d401640ca541e00c1d145803100701301c2540c2c40f0201190003030001c01e120071801680056035030150b03500250005031401d40c920219405120f80902034101d8000402d0200c10040b414000c008001303000c036418005200000a11400c031440c485140c8654218040c400942447c100c003e50340c44100c80c0c000003809012075401100e0003804982c540c10002c41120144205034144c8103601c40440c0544d0110f017010340b081d40bd0035110b400070525240d035002d80c0000800715a11141982e0101c08060103444c01c0d0b05040c0f60103035495003141c20785000509a8400454182000520020034800c028805400c551541d000d01081d0340c070182c00c403c3c2c13025142d0b0408211a0704415 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 574059613 1250 574058363 574058369
    0x803091c0f0809041409210403210c08070602030108060a11031501110d021e0102030415050c0d0f09030923120705090702072301050a1b0510090b010803030405031b0c030601 76
    0x1018181207084c4c030744203900304c4c7c1084004a034080003e20007800400c081502070b1443da032003440040526034200c9020b98009510749401031100f100060121304101d01c030b0300614100c910000840d200344d1201e0890105440d84480080c07200c01c0e091001403048641000b182d08640d0041c10280c0c41180c1c0101c095042400c900045005644120801403c000040342000d41d0348075018000c6007036003429034030110140c1003008000720051711003000c20b080c1030103102200e10181c545402005000b0040b05200090480301d41d0550100b00031100c009941e00c8100c0c413000f0000c3d00c0650380e01141060004005282021320003401007881015030100c0c0c0c0761584000180614025002404050b141520501c0c1c2003400710041481c1c2d0601040c40840390760004165030754403c0c6800c1c80150103045480e00e4144460084010307000d0700c90040d41c03c111400592003592101c4c060b07400e0781c4090303807034109060b901d00c819100201036500400140c2651000c00d00c200c89c144400300700361070100703080600091607c2c40c04c1e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 574060863 1250 574059613 574059631
    0x13020c07081c0c140f0d0824010909090f080403060b1306060906050319050c0309010c02010509060f041506030302010c1d0f0112060f0803091c0f08090414 68
    0xc5040c80011401c0146103540c81c2081c0030110070001c82140200328103074001e0001e190240f11000740080400900c609021510100129618140000c0004201010940e400b000003903482c8080380c0b11220805480b01c0c2d6000603110700c11410b140034103a45c0103211140b42501c0b040c100758040e4000038000001400154090140482e6a0309060300700606007a1170280400f60501c0c180c000c11555070045098400c4400d242403054817641c514041c01c1401c00200100203070780780340a08006046902e080554001c44254000704045803418030260300701e507019134400c002d0b07034400e90006806004c181c11090748070b031181c805500c0c0213803080301c040d00b610039a80003140980d46622005440550050200140385c290192620900061001185026400c6204a4104590b4806469621002c1c0d00200300600b034400b0300c401c40c141ea400b6655220b8002e40c5025118040800b81040d0400c035401040c620380307030013205800c600c0b1034503036404c80103601502d01c0c07680154445001000c0f0b030306d00321001440b40c0009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 574062113 1250 574060863 574060873
    0x5030a02072027040201050d02090907110f03070c1202010c0f060542060c0d090e0c0a200c0907030509070b0307022d06070c05070501020102040b090d0213020c 70
    0x1c8020084180145040e0400f886844025605000c110000b840e800075020b0030f21740da1b203690000300d0b40081d100d1080403d421440c05010300c05c00a070722401e0300b015164501c0686080004201c10303e9240d00c0b5020000e444054000424410107074076822100c1881d2050403c1000380003503036a20b9200d103c038000b00740c9009646e4010000103e44460440c9000b860000348150450403101111220b5039645484241c6801c1d050342c50110354076a8022155502d50326001c9540b01c8901e400001d08603041c5004001340120217401003480111307000d05880e00b500c2c482e1600105410001c10700080201e4901c03103002e151041540e02d5815403170782d01040780510782c1c0f598003041da407600c200300f07914080c01a031040e00c0e02e0311704004104aa07980402c10546d11005564034422003041c48040107010f080000c99110180250400d001e10242c00c90030000c1101d104d4000c0e101010303907402c0160300301d01403846040c4078540c040103000740c21720b02a215800a00d100401824150381120300c004104d8014040703e035085d50003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 574063363 1250 574062113 574062173
    0x1021804110c060103120801090c0906032c0a06140f0105010f05070c0b09120c03060121020301020f090108010602010e0c0405072304050109090915050403111605040614030a0305030a0207 82
    0x4069803c6014041480c810300ac0b4080301007008004405a00c9041c0405585102000e030008804028912051070401150045240c04521076201d08030b0090884141e4500380d0340c00704043c1c40380302c01b40c03189001a20b0030000b0780c42e000055a201c14003803688402c20804000b0000081c10042000b80a0b003410501503131101c441c03070706001100e9003900c414060fa9101e00d0780240c2603500001e009064402044c0e05581454000000e180c03c1405210001e41c1940045401b40107050380030043e0004400c241c1c3c4902e0940d91300e540503401c8503032a5045440c1508059a21401070600d40c0080d03410a00350b01e0488a0109007556408503100743d0000515100800a802c1240d076074044805030244c40c503007104000f5080e1540e1024614070100411003a22501e03503000805041c020800120244030380d400f5940c448201d410306011564050280b40e1090f0303e040300201c0c2003410300300c00c01040c420145c010b0624a1051f141070b106a0070040c00000c565800b01b11240004103807818100030190380c2c1c5020190449 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 574064613 1250 574063363 574063367
    0x50a06230109090c051207090207060b1c03020706080411030a0b0106021015030f02120a080c15090a020f1f020601033813211101021804110c06010312 66
    0x80c10b074040740c20709040c01c0030f19001c60b502d0700441c0d0888400320303032103d031080001041c1c0703041284680c0180c01a5101007200003d000303854201c4a803800040f03881880d8030700842040d0b100c002c102c01c8040c0059021400130300c00c082c0292071154000340035803c000401c05203513001915100206800b241c08109046c010441e082d0100109d145111342070f841405002e41014281507003107901d00c07000d0400501d85101c1d84c255101e15080101c00001078084c0d0700301f03803003c0c140104a0340c010000300b032980c410f5291080f501034010b0102805188094040c20001e80e0b15000c1003941201145c0c581c0e8040c2c1e4150b007076800003444c010b10081e000610780240c07100e50f08d981072541c200c1c104000c02e110162220440b5000c551041c91408a81c448004401c1801d5291509211100c0204003401840c050340380300c405000c020064914002e01c01030784c1c3e400d00d000a41d80c0140d802d030301134442c8403202d50a580f0b62004251400d07802810708180d9221046081c00b0750803a66529007007081e441030b103030f1a0346018015441d075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 574065863 1250 574064613 574064681
    0x305151212390607030606020d05093d0903380108010c020606040e0703031101020d0504031205060d1106070201031b0f020d0801061d01020f330c03040f050a06 70
    0x190342814100401864224084d460b55400500365040000c0014020800d5a4031046264244582ca9a0b8105540c04502c203150b10090a00600d07001c0d02533131262203900b8414080326050341c1d40003500000c1010b010364a11001c141b000c0000408904558010085c031070000c1c045c074000d0a51a001240f070f542c800c1d501038117000010f40080e005030308149501d15400000113a84044945c1071421040343c0e005800354a0082c0038034013500c000030342400240030a01d58421810600c4c000013543c10802d54480004018203190b00c00c10081c5030310106042902c0514007030300645540c50041c1030105552883c809601507a849a030341800109803000c4511038425030400004900c001103050001040d4100a400350403030311500352100340902054491032260b4424800c0150824180701280d00ca04080402c0b84100307400b050340d80782550398080c1d200030f0300c80b080b08695001d1920180300c1851900d42c1c2e124442010b0421406a8040c410301522070005106403040f50107a035005a098500081160f440351500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 574067113 1250 574065863 574065871
    0x2100b0d20012304170f0a030c02011215050609151303060c0f050d0504020d0b0a0c08070509150c010b0d080304030305060d021c0201140a03051512123906 68
    0xc8a02400c240e01840d8148085500343c0303041d1620800e00481034074040c0e1600005400c01b40c120f0044480c03900406412005060002e0300c01d032280c041d81c02c038031002101141e21042151807040c044c52010041e0b4100704004006601000e404440c1210400301042071342d0340090f128203025038902c1c01c20810300000d80b040120044852030410804206d0650081841c0107104001200641c0e90011504650303441c885482d0042d8001c00c0310810f49000c440c40c81c020030616001c3c00c049010030f000035050301e00c610225000c8003c000d00b80900c44030103407000c0328181c0140842500640d41d035a4110442e50b62000e98103980c9110300321039681c07031409141c020180c03500640741d64045e011042300140141ea44400c4400140c11b0244207401030290341c0012079659030070b504031007060b01c00080d1584a10b541074020368480c1c030301c0c02460f201c4d500401d0148030040306011201d000c1c9401c254010144030b0013580060582c03040300c020040340058030051072160014040540142000d0441004900e01070a01c041640 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 574068363 1250 574067113 574067147
    0x90503101506081005040f02030a050702160b03090c03010204030804090e070302010c02040b01031e0c030b03120a080a09120c030210050f070507050a0510060e0c0a02100b0d2001 78
    0x20855514216003151441c0a0801440b88460014013a108400c054000800340180240545100700034600020b500650307410609909040000307140900010780380414110030b036140c099980c640500c1c50010340015000003054001d50408042c2d544d024000b500241d80503100c1e180d6524540b00da002c00320b507552500ca42d202d4000c3c450400160380c000e11101c050039012f48001c6080f01d101c500480042003012910900100713103d804040800342640f29801440032901d04000c00707110201090342d582c1d00103001c690400004c02410101a00c9203042c15004641343d600031032110b03070320358500390054904006180043c50102c800f0301403683c100100c10704a8254481000030382000340d405004800018140000e1000c00104042041020480512002e400c42c0981e590000c07a0311001000e450280b089400d06c80b03da030081150071a81c4012101459800d800030203200440010000c041e01141880130703481b613407004010f000300d01040b803404050590810f214000c41601d0340003406068402c480c00340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 574069613 1250 574068363 574068371
    0x3071e0801051005100c060c0e04141b0702120f0d0e0105090a2102040615091d0406090c03020904060e071d0a0906060305030f0d0f0c1b0602040f0609050310 69
    0x1040558102034082a61401d07108440f02c18400c4a051b101000680d00040400e0724005500407071660001194500003402c071780038424181000f000304910b45080d070700c0d00e130182014502c11503101c01d510700602e01a03101805242072085046112404c3c00741820203007403103030005000602180e500c07130708191006a00342481410080d08801080840d0f0341800703204448241c040440c228046090b50300304038541d0040c804d000c4c01307840c0c0c950307c08020100c1c11010b010447d034040104014840300340b0080c1c48203044190351502c2c2d40b580c9541001c1c003100c00d000c1d1034035403059101002603128915814419802010007107a00d10280080d580b600340168401c81e8261001804101521004481550000c03908030700404c0890701c900748000205482d41c0010b045100000e0014ac0500005014014101040004021110030b5440400c00d85168406080004401c030040b0349242000e0300304017000f10301441c401802c040d111b4101d1006007403c0d42003100440e142071010020b500d0200940701ca501020700c0c0600c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 574070863 1250 574069613 574069621
    0x2b0306060f0c1104240b04030812250503060a060f0507171b101a09241e09090a0317130206030406021b0d02030405060f0903071e080105 60
    0x1e028400c0c219059081000581200050040001c0180440c900003031040002545070440ba1040d8a01c2d81c0d424002d4105441e4001003411840003900c04403078025030124a411a9030b07800e00034001004040c041c9004800b0604070307802d00d5243c0e462150581e40d4a034240d407801c0c41d10420465850750342c040c00c00c0043c0d00b80d1500c031003540501a5018141d00144601003140d00721407140700381c0034060468203000c0200040e1040030a000920404a4030415030821580344901c00c1c0300f015141c1035001d42d4001c1c000101140b80b44408403180014000d003c00345c0c02c3c141c540d25000500800c0740c0c0020080521040350451030f03034030300140065004554030000f0403481c0c0307065a011b480ca18840601103c144600c40000e428420300c5c1c414030a210394000d0609540c1c1c81c1c9440c05100039080f400007992010822154a5110b407000507000740580f4858004500340742c40d103020011294007810107080150010b10070b45060381c03005c002c041c004e4044510000c2072075600d51200000880340390702228141e030402c1c0c140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 574072113 1250 574070863 574070867
    0xf0d0f0e100b0f0907020d110109030c0f0510060308090102100504050a0b040812070305070305091b13090c080309040509030711010503040f051509070602010204030c05040504050f2b030606 83
    0x3140116007540701146481d4000b00242c1440302e07080d00a50000b8144c010005200d6001c04c0c200e5521402c0c0d01e030f02011000ca00d25050032a4220080100401d05401c2444042602c41040840e018429401c035104160011164000e030b0760380b50700840d611000031030120300c02c0d0380500140e001140380c0c50b403c0101d85010f40700c1e107603192282e80001e004080f035000481d00344840c034001c64201004c09190032480703041004c001001802d00b101c160002915082c041080d990010402c18025039090b50303005180b10b041010010700781c60302445103410071707a00c0160000040d001da080c0340c0204034000246844a01c03ca0a0202703488005040c0c0000343c20401c00080050752500c03141c00c004c50207203001d0384c0301e0b44c644c078100060342000900600b06114070b041d00b03151060b804a00600c1154000e042d070315915502e1005900b81c0c010303070000401c0050907007018452804c00390320a03580140240202c5110000540181e0308110f840880012a450422400b0301e03a00000d51048038400098075042211034901800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 574073363 1250 574072113 574072123
    0xa0c0302010e0a0b0a020706091a09010b0a081c02100c08090c1c06020304061112041a070909181202071a0a20070302031606090b2a0102040b0f0d0f0e 66
    0x200180e07168041f88000a0100c543e01440030540d00004070791003058205031026039144221100c03251903003440c2e0980c0a03030030902c2c201d0302252220402000e0041000c1c1c8070000624503100203500f103210301d0780c512201c00c14502484448164a455070501c609211201c6d07404c3c020840e2045006000707074504005500d4001d90416103003074014000503201e844514042019280c208400c160401c008030b0304566007480d00b260a03002e184101014202080d007105010910007040f2004800701700b00c144104606061070300320000c000303102d01403241d5010321030391400c14407140301410b000140d000a00910003125042c01c40c03c03100041030000303420f245d100c0100802c80c1d0004006020b00c01e400b410069600300007004140c0266030300a0a60b01900c0c0304a9400c01d2030a1a80715090028078859000111a0360f014100c407071040c0c40140300f4466403e42541c0c01c00300943d03103d07022019035003003000043c00b40d04000604500215001444c0e5254141d12103041511000c40146010b1072505840302c1c1707a800c001035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 574074613 1250 574073363 574073371
    0x403030e03030c071716180e06040507171c020706020601081c050a110d0203030610030b10210e01052d0106080903070203060108060919080702091005060a0c0302010e0a0b 75
    0x1580b03010481c0d4200c2c54504000301540a0085d0344848400807504109800002d12004038410082144c2d038500023410b5510702c410b8602034801c7d04111010301080f61030090142002158000b1503901c40e0440c00800c401d06020244000180c10041003070000c0b950500140303004051807801400c442c048000c1060100c0121021103040c06000103482d036403d400350911548000c00101a210401810840603449501c12145c0c584601c5040540d101130b103000e441000b26030000070b450381100d11031050054514428800c2c2c100840788030351115102c40002c40c01411800038043e0004510384c14103100650a0b456660501454031502e201c280c4221034442d2046411140c09140800982d02c1d002002c505512a00c00003940601a01e400800c90140000b1002e0154101004031070320612005141c00c0c802e40301d400000c28134641007000f0310242c64440e82064004206014070140ca40e40c802c0091420b030710902080000c1181000304405043e020b02c1200c0065038000c0180c04240c50b155510000740400038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 574075863 1250 574074613 574074629
    0x6070503030604050f101509090c090f0b1c0903051b390f061c06050f04150e0705090409140106081c0528110708030a080c07050f10020403030e03030c07 67
    0x300b04001f0748076450203801040d000b4001c1001c11a59003008110748001c1c000c515819141c2c1000280c1c800305602160f1101405480b14084004504840c0f00076000310382c015010402c060205203648003e030301020816188000091060314141c03d240c3c800c01003992000345407040c02604003100e1150031380f01c805401d42c0403980504180b408100184060081402a0304007860503440128507544aa11940544004613507540d40580e840702000103407061600406000913620074108203000e40b214150b07400c2408c50404138100840c42c8042403c43d01806426140d40c0c43c0c2c0c00014072000d90030310070480901120409402e40030b0b00e0718445076400000d501d002c000c100300002c50444440b00324a10031803104082c01e060185005c411001414141c418843e0080d50003070800c005880840041202c050003981d4030f1f03040f44c0b952030320180007a43e0000081a10035000300700000c10f6010b818020141c1174a1701c1040140c6407421428020401c0c110000080c2c002e5004000e080d80000d40000c0c3d85086500007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 574077113 1250 574075863 574075889
    0x20402090d0b0f241c14011a0102101112070e06030c1c0606090b0a0306080105010f06090b1c05091e010c0306120203060402121516030b0108042a0506070503030604050f10 75
    0x3906c0c00b2220410204c4020341d040d442c01c06061f1041440c200d072500491000d03800c13240b513400c5805182d01243d101c00020b90610a0070030942240c40f1245034115070040c0c20b814001d80d800810300c00b24103d54422260403141c00b03400540d1019501c4020b00c120306811305414104459410705401410f044090702500d14441c02c0880e400c1800c07071198002c0000f8020100090102d565a040040036600b0036024420102d00c0c894408980002902c06031100c60600340003444c4503681c01000c400042c03e014041e800c139030045c40e5140c50200640205120001403010000840303445000000b0112200e43c0c10407000e40301450f410202583e40080c5207a0003580444900310180b584650b802d251000901302d02603403244900c100320b40c1c4807a91046d8902082c0b81c1d1402e00c04003414000445034658110303030040403851200c0d080100d40810205030790014441c100c2039a8000c1e119800124181c215a00440b0030740d200004028013805c050080710303044007072360080d80c006043c540c1d5269110724050158040c2141e0b2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 574078363 1250 574077113 574077169
    0x9090213051c0f0f02100503152736100209180705040306110a021b12010908040305150402180a150909051b0d020402090d0b0f24 57
    0x42c040c88101c9500c00c05030120220240b40441c102e10740c0e40b0050307202e0303401e00c1000980e240c0100212032040c2c0c8141c01506850007241c5c204040351703810700d55103800f046014503030b800352003401c29009019848103600010402c0f284594043d80890914806070f0740d84c00396405034030184001501414000071001d0140c2c03928040004214002c8401051800701c00e8484184241c1c00e030040010025203001c2c07001802070b6030101c60701064602c42c408800c00142e01c000000000404001304c109007901c40200f80d000a618150965802c0d07400309c146c29942c400e00054200100441040702000140d549403180308649000e8000502456054200e01c501c07440b10400240324080c0b070350016240c0b0109501e91040c150702d60b44503c008101019080341c641c0302c0c01c1000441e40401c0110085030150003003038240354044503403d100c06500010000c60b00a00c01c40d00385800501440c00d0684a04500c805800c1e6524200051403d00c0340010b01c400d001c282c9031481c018581e101d44c0344180f0b6a4041407a011080d1013 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 574079613 1250 574078363 574078399
    0x120327010215131703010e0726041a0a0e0115060522050d0b04031b02060405120f01050a02070302060703112a2b0203031009110f0a030c0909021305 65
    0x12800c24020200d150110913a0040b580c8540594140c03030000f00001c51550b100c03402541c65810703141c00b80d100c00e646440c0c100c0390040c400102581c4144191101141000000400d9a4108003542ca000311651034030529200a5001d201d4861500720103071261440914002000d000341c07140c180d00d2040a84110b174050a207146071040840100b4024107074218001d800d04040f990360b942a20201c00107074490904034111241440501c2207180c0091035545010716083c00c01149403c00c80d445001801292200f500742407003842000e00c035140341c020169503030100d854000e00b4064010040002c0c14540351441d040c10748000c066400e52050b041140e101070780340e10301c0b590010810040030300b1355100d0141182808005121200000300002080c00284558810280d0702c03404110380307041204000312803c01202c403c1d42c01c102c17211520311305030b58900350b0000f1184484d0f501101c2018003180e102c0c8441c054481d4040c2602d0300130064202d045090601a48605180c80b02a200d800c1c4240e01698039582d10700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 574080863 1250 574079613 574079641
    0x60303122a030118051e280203040308070807030e0f0d0201241a04091e0c11120a090308041211060a12110904180c050d080412050c120327010215 64
    0x100e0031a00343c0b0100d1034100c7d0307680c5c0c014600051584c5c5412084050b080c50609500940b4021a40364a41f25010390300e902d4200c40090008000b2400c05840d4122064115402d00c16841d4144104000e088401c0343c1d00e801a003540e001d01745040398920b2070000140718000031810041034440018030808030b01d40390302403551503000c0c581140081230701c0c1140c004e00e484440c0366201e0084900b02c3d024083d90007003501c00c1e40c06506030140c0c0c0761581c0014070182c1501900f07034014030314186039041ca40030958032611460800d13013007508003460308840d164031007040c0044002c0d840702c401c100302c1d00c0d149040302c3c0201c002d112140800c90744c114161190107012000c3d07ca1816236001882c080d00800ca030181600c0700d0464005600b4040d1208501c0280100c2d207810441da0b50308400d5040b0401514081c6040640002040c08020a54650083e447c010720580e40b200b2004500d00d907020001d40e110b80e00e010600b400c0035002c5640607264095203044c0202c590300499a07030100c6001903407117011a941c4280e805016 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 574082113 1250 574080863 574080901
    0x303060a0315140127050114010e060f0408151f06050c1509150a0204030309170703020d03080a150e010b0d060312030510170303040803060303122a03011805 69
    0x1941d14001007504050700058100d80c5c01e240b0640c400708858070907200c040f180280500301d01214040424500d41d400381e8809940c031f01c009800b4900c1c150340c50400c010ba6030403a403c200c0880d00000683e86908036000082600b00c2d401c84d840c10160749211020750300d480341500c04c29040c000042038584150070140811060017141102800840c41c00d1858a92900007000101c1107002c004000300f00181140d209460549074181c5030010281d04000d5604565107584007450610b1084074400300058980b0340c0e140344024482d803521034007410008500c800b030b0344404402d01d1140c4c01840c810450001c9519989045a40075004103176030b000002d50a102518060f00007812401000d602075201942c1907200c10321660003a9407403080d00351503c42450700ca80482e00c02d0030440d48140f01203030100c0c542c80001c43c3c1050000b0b088a00d00041c01c00c034403505d404100e441d580d116007002d96212254940c51342482261403846440340ca550305180e1481d0055100c100c44060140c0c2e80c1d0005040420b2401d114041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 574083363 1250 574082113 574082141
    0x1020d030b0112110c0d2c0303040315150e0f0c090a050306090d1403090706080a022703060915040f08280f0306080c010309060b06070b01090c020303060a0315 70
    0x290045141c542d207050344401444090340c1b01c3c001035204a1403145000281960940c80f04400342d180103c100c180312035000c07140550502003000f002000a8681c2440b80880f12a442e001c190b00c6100d01c08482d40c98032030362051006042c034004010748080056100c0e640300c118002d1540c1c175509400040344441003d50406c0d0b815100b0041801034008002620a404402caa80c4c0c4507131030781808094140320700094030541e100364807540d8203001d12401885003940c0140b107500010300340074024010a0200c0d2001680d0008002d150182e80602c5c00d040c403103540e1040c6440001c1c040704132038038841c01c40c07905e005201a242c01c400d114140b0030025010700300d41811004506005c2e03c510785810740030001c2d43c1c0c00114008120703070f20b01c4140164000e0107818211030498000d0f00c2d130540084c00640c050494154201c131055544d144a061541d50030028101d100c6c05218910b65544c1084e1a140071203405010785c02c150f51003401002015510080c3c4001aa50301030030100d0382412881c10f80001c0e0001c4091100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 574084613 1250 574083363 574083371
    0x9090a110a0513050f0105120c0d0207060212150d020f03071d070e0307030c0b1b0d020f1203060a120303020903070e0717040b0601030b010c0206030a150b030601020d030b0112 77
    0x205a025003e400040782c0740b618001125510b200700315054080c1c800c2280802d409021180d0910a1400c000da440051380c0d81d801c2c6051042d0901504a90003404211810340c2c0c0402c01d4269500000003c0e42d00c110014160034540c4a004001580c0802c484d030000d2003110729148140140c0c60500260000b03204074111a83d800c500102d0303495a0101c2210500001590f94081080528000600d081100c0c1c014180304403960800314091a07550001a25100030303040c800852440c3c1c4400c100c5491054110303030280082c081b020711000d00300816000e060070001810f109010255940c40b05c480103c4010365000c1443d000946402e41c003a01886402ca54180115000040e500f00d240890786e100d4140c0c2c0d07030781a040c032030760f403071072894422091314064060881302000920650003035106028042050400c0c5441326a55400500781d0307442240c0211600c0c2c0c40c0d564941d5502c1996404e000503100307140f40303181146081700c0000e559098410b1950100b68954245104a90141d580c01d140380d980d01034280 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 574085863 1250 574084613 574084627
    0x60e0d0213060f080f06010e0606091f18091104090e10140a0c08070806100203090301050a0608010e030f071b05040213182921010b130c0509090a11 65
    0x1400704040c0c41130391602d00070491300c1c02c669007000c17414a058845c81001185191544014000380c0e0300440220740d0041a83d10759031184111004480d01d50000a58070b0710303034025403160b500b54000703016440400301e85c0c181070341040806044010b85085d1920508001808a01c054280b80f5200351003148a14442c906001046034012649141c6c3c800d00c02084240030780c481c09102201c610001300c480e540000d101c00302080e031904d800e104c2c420207104244100da08003003104c400207084a0f07050320300210060792650101f007a00000e004c2c55009281c02c101540c1402c07036030795041050f0f205c1d403440108807005102000d80b408660240c0740b00500b5000d8804c45d16200d60b881142c415034214000e030104000d9410317450070308030840c3c0a00490344d030449850380106403100801c4900415682000c0340e0003408018200c0c10746101c250055010784421002254000d03154003400344992940503e4182c0c503050101000040d500641100c4407108252004e075015504c0852420041c208020154503003c0006080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 574087113 1250 574085863 574085879
    0x80a090602270411090f0409050f12040f0e0601050706050a1b020115050405010b1615050915060415060503040c050307090f060e090a030503040f02220e0106060e0d021306 75
    0x814144060f2010050b1160800c56110a4007604030300e254401d903440800d413039a0031b098100701c413180d1064040703541400804000500306990150006003000000c2020014800c60801680045c174100c8244003460030110002480c40c8214000500340340c0d2214040340d50039049602402e0001042c8c0c5ca00300a0003104100240a8051008a588040c90300310380402d25103001d2107400c0c1260119480503150060010702e584810800c0d02041d070750101480c644180012260164500c114a514084c0807030890300300350800141401340807603020f82e18001345450718054440710700b8195185800c020340c0381d6880c0e2406074002c4c105504819018083d0310070005205005410040c9000300500301032068a481c1c2107240c0c0a04003c40d01086143c0c08820408040b0303020308015500306c0d004031050301980815801040303a148209001c80040e43c540016400d440e00b09100c0c00d80100e007032030000e000c11403038064028981c41d01c03034611034403a40c1d1410075074046613908217400041859140061001a603540c41e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 574088363 1250 574087113 574087177
    0xb07060204080f1f0b0a0308070606050a0603020a09062010060609090e06070c031713060c0c0c0e0604060315020405010f02060408030c0f040e04121b0201080a090602 73
    0x1032209107100f69503603070b811a080411020540b0004d0300740212101c41c030100d010081d01c000744c00960400091000800410810802020002e00440010031490301e00004c2c01000f142c95440344007054814421401c03421350083c4e000c0110784191400401c907040c85174560007e81040704d0098030034441c401e512144400b56800003401c80c0c4164550308030043e41d0780003020580b41111030941180c1c0081c40014600c03409000f80141041c061315203001824081c0946203210326064959024081c0c01d00e01e00310800046001d20101c0c00d1051900c44092645a910203c0030742e40f90046d0001401c801d80050881c1c0c4495100000464011440b112907100c0700c0301a030003d5000c2d02420b170008640c1c1155000b070500004006029030390205842d461030f990100c600c1c1d00d076044401d502070024001c0200060b00180e90040030300480c000d05015020418405c07002e05141c07030800002c0000c10405d090000981c3c1c03c401c0940d400b498001000c6170b002c4807460f02ea0001d10034150407100c403700707220800c2c2c84c03100710700a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 574089613 1250 574088363 574088369
    0x405130615030305070b0a0213060c021518040b03010e0d0305040b011a0d0509071a0a030e0d0c02060310080d051e1306050c21120109180b100b07060204 67
    0x2008101d00460350580091020a030700020303001c200100081800501114849a80510603980060800020041e14550140164001e80010700c50803154020740c90212882c2c00c8141c00e84035902c0c0f500b5221440e210251405039031851085648a41047c440e403829000742d81c5203181c04003030b02c0c4603c0740101e0240042409a50944d91401101d002290620f0700703546800c00c001718001c1e001c0c10071206070100b0010b400300510b86442400348800000b50850103801400702082c4614080303856402003840103086503414500305030309503c85420501056080121041c0b01038050716515079903076607800c0180c148501da81c001c0c4460302c6041080041e040e8000041c0c4180b0300302404600e071002c040e1040070b00c18021424042c180386c9107e082000454042e000034507d9075082020707107201100c90b08082075a201c03140b012a0041c00002a01d00b6010b224441d5140500300c10481002000b10503a0304850711140c000000b00506040408644007640a120703050040c01c1601d4419030368041c504e054000f03504144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 574090863 1250 574089613 574089623
    0x512070e06040b0f19053703082a060a1b020a120c0f051218060301030b040308041704060203071a1b0328061502060420010509040513 59
    0x4804181d00d03182a0080c000100d0004151141d02401c1d0400c00c074051021111003980c2c07007542039000407961240301c0781000c800301140d5030104860340f03d8807001d40800100c0c942c610b12441b006e810700009404405807803103000070819135100c4c0c11603201c401c1000d0070204051010340c0318000820407000b00d0b0350444009008152800302c00031501102c00d90fa1440700d508020118403000d064046421303c01c00b001150369008889018aa9140313464490814007030301c281d01c01c1c1c0d480029100305810300281c1800e000310342c02e940135407656143d0345890050f84c40260004080040c20b00c0441c0c1481030b4651601045040b80d401c07581d0310760307035690081e43c0ca900c080f004848250010405000201c8101c0c085889800c04401c3e00d07c2508850300348841f079510082c4460703131044a00644007244000c20b242d4140e410381040e00050340d581800105501162007101c40000c55018070100000a18a040000080005480380d8540007006800598140c0618804190468a00820041c4900b03400010548040c020b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 574092113 1250 574090863 574090889
    0x609020702010e0111030703030c140307020601030309120818010207150509130b0607020409020109091406040608120f071104110d052a090a030f050303040501181106070c051207 78
    0x1500e281d82c0030200b0740d17002d800078005c0901080c0660400000740400745403420640c1464000340762582c0055544600690081d1b005008054201c0500e4014046024008100c03003025070360a5502d208072400d00e000512484c2c030082890b4001c100c0c881c0074204600b204040d21090f4940200359400401c6407a114038070300c004000014003140700d034100c07403040a0300c1146041c401d5000d0001419100b50100d040290901000803420b405110320710041456950110302400c10b0020003040e2644c6400c42e0010381c10401d50001844100001c89245607084034400741c0741c0099042411145c1021a80c10307400c00d040035000a00e220410000f0050002c402c0f00030060390300c50f08006d104620303240c0040320204503001c0d5000c0d0000e171494050720981800405410030300b07440359980c031440d05003020b040307810354030100030300c400c1000a0103070300d1668125003030409005490342c40781040340441d0a2918001c10000825009000145c80120050304001c1d00c070b18a1814035503a1580c0d40e0b0400d206003c403610003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 574093363 1250 574092113 574092137
    0x2c060a03110621240d0f020d06060611061014190810050a0e0601150302090f04020703030b130507080c071506030302100605030712060c11010c030b01030509060702100e030d060902070201 82
    0xc4d45203a042c60300d40180c030f001d0b49a00d6944d24041c03031109404041ea8409a5060741d00006042d07400b8840140c002940d0700040301003840b41c040e19040000c0d00401c00c0400d0742c1740a21003000300c5910b0b0710200c48110380b10b500c00048403d50141038400342c0c101d000c150003004c01c9082c45a00c180c100354007a144c44501040040040e03038445480e02c1082c003426003d03085655410400f24881d030050011141d0040c220015407103202d000404070380c4400030032400f103501d5032a4407405151808007401d005e4842082072210b417500190051034524000d00b034030b50000c4045402001d100c2c0c41414640c9800c40e5101c200016500c0741800ba558458801c244280705060041c0802d00d800c0200f0180200d0306000e217096400b496941d2414007410402a10b101000b0300d50704200341d031110900446c4109503240d1400100c1c60703005000181583c170010108009584000300303100000740d000661540b9076006200018041d07020410b020700b103208180c2d0780021036041c15004035050304551300a240030b602c01d07200c072445a10f03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 574094613 1250 574093363 574093411
    0xd021c03020a031103280e0a08060403031425090e0415050108030c070302040c020a02090f040c0e07020307030804111504090e191b0f2c060a03110621 66
    0x2294503241b105010680c040d200c00c20b102202c06058509075420b0045a00711b84c0350110719001050740c40361070350354060820300c0145501485801c2019100e0034001c8010300d04905405040c0c6010018250390050318030307540c40198442e202450207041c01c00340c080d4060a0500380214190914402c0d0301045203810300010303070101c0020465925581141c080d059003491a000c00004004545188056016408903000140e9800c2c103641c4c071884080e1020002410681400c607002003981d001703069101c0a010912840b80d0b0004107491507668545440c050582c1c6510700044040d610441c1c541e0010307850b85000c030f000356080000d001035500302c0d0010031000305d44404890f59441c00c2000320801d4140d441017100800c4441c00350b0300c01c00c04501010101155610419240100d450307003c0416102d1203140c40c034100e521503021000300c2c140e078a140503007800c0200010b1801316107880300921138a030188001c2c0300342d19490203450154208000f100391410070740c00069085a0100c0ea0000c4c941c9400201c425018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 574095863 1250 574094613 574094617
    0x80a0e060405011d04020f03010f091109060d0f06090609090302061506090d0c0e0c09032a120a02040504060516180605090f120c030d030504050a020d021c03020a031103 74
    0x2410594a140400c256880046013031140d00703010700d401980801005201c454101d0040d8002c0482e2720714818102e1415803c442201c80c01d000c01100740800700003d122580e20301c001c0e16107410201d04009004210300035148010005603201005450502d0000100644107034481c134103040c025001d0f00e400303a880701825076202080b2106258466001d0240d0410703405e08010300d0076094491a01510100e8940070700051aa45c100c82c0d904130900002101102401d0a0103461440340c425401406043d240301440c2c50490a49800e80e80101010801d24040c2e8108000000417141c014004011505287c02c002010b007401b145c8991310040b003061200e80261240c1c0780510285c40c1402d0002c1c0850900c581103407243e014051495000070042e00206003503540c42c80300c00c1110306020082c010542d11605060a0000301d8100030b0a241c078050070440464008511070641941c101c4d030340141d1044030300c002840905001e0000103402e00c400200420180c0009540000d14002e8079281c810070050b1140315524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 574097113 1250 574095863 574095869
    0x603130210320a111501031b080309100e0d020411030603011103070f0e040e03030f1816181508010c0314060d0201030507090503030a0806042421060504080a0e0604 72
    0x600040285040d801c4c8290074031600c0200b600d096070f402c1c86510b072141e03107040b03404e0b001960031a419104007060000001091802000312001a505120100340011181204036105800340b100a5804880540d9110341c1a6800c941c0104104070b00e0a40709140115030700b080340da45001e5842c10030f00c03003a0118040e003502d00c5402c00783e0f00c2c2c80703210103001021500b02a90002254100c0d4848c0e05400c4c00300c1d001d00140d4426008000c015045251003003585420741140c50a0b40955040725000c8040d4030010301000c4141c4548201303500d06a0b0f10b25507594020084204240c032800c514040200d0030b0741044d084142c0c0c0300d000b0740d0144000c0b00540ca4032440b050040e140c090380704a9407400c240055010313401c455440440c82c1491840d031a034620100c0d065a01900d1400001403586007044544c0c07400f03109110003401c861403d0b0201d5028034010904000c00b40c05204000560050001c0102024094680100343e00c82d00074031150402d4503044400341c00848802c00841d0b01240060841d081c10801d403821 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 574098363 1250 574097113 574097207
    0x3090f18131a070f0f0e10030e0309031e0c0102120706051005090a020d1103010303080103150e0d05040e06041505041802030a030e091f050603130210 66
    0x40e160111078103400c1c49140d4040b10120203042080c00c000d6160041580b0401c16502c520001e4098082d005000c2c07510600d040c0b06101944629071400c0d102d8611300c80550449003000951043c08601017403450003100c6507550b2620410828101e01c100c03551015a01440d040b04407080101d03d8001a030726541403035180840042c0900c11440421629044036800c104020b00b44004942c80c1c201180045c14103c4007202c5040e00081c0b41c00440c0100e200c0c030824202c1e0168000d0855042d0703513008007080410f01c405007076103d40d00945560310040750320400002c86c0f60300891b00624868200907090307821611031500c0c83d07201c00c000100c450510f4080d04901110040c1c207844103d003040104002030043c000044640c481070f110000041e2020406008036074002d44811042c185c1c10b808008003000000c2108147e05008400d1074034840c2045c0344030003503c4044509903100d540e41d06400b864402d04a402079404a1820000b4840300c2e005030300c6481220188000d4480700fa400e40c0002d04003075a41c541054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 574099613 1250 574098363 574098409
    0x30605120309030f010c1b1103340812091908010c0e1f030507051b010b280509040f0807030801050901120305120408070b010b0408060708010503060423070803090f 72
    0x105000da00d0801c06641449640d50045c06081c0c3c401207454801c1d4031031700303032500c882072103800c11700354545506d011b10910b0750384203401d00c2424442f01e40d48802682c01d0b80c0640380804140d8401640e00d1a4101000501101840008079514007032603010b4051621440046a20b11070800c0c0709041003130305003442010258040340f95214520084008100007404081041814040403290000c40140c3c918407580100002c81c10194040810010965656100c960307600c04100f50a0303551380f0b0440c00b01c00c4800881e5822195511403c0100030f144010340002c24100c00040c86030201178001e2074440c142e030710680b4a0a45d9a0f203a601c5680241815000980414070a00c1910701c250f48030140194050310903500f140c20200c0e55991803000c11401c0c5c0146c0480940441c041c016a2001c22034254821400d1400440b65450280401c2d01e80c070015101820003040a54010007a84035a0210207544880c6070403111a035035541907141d00ca410800c0c5241c800c1c2c1d1008101d007290704e04000000841102ca242e004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 574100719 1106 574099613 574099637
    0x201020d060e0126070b030f070801150507110303090301060314010522030309020103110a110606030a0b0106081f0f090f050709120201030605120309030f010c 70
    0x1040c41000000402511403085101100302a140400784e4520303a2030180f40e8204465500082c0c1004800014803001d2126a0304444c803a0354103640d005110303600d81e0000c0f41d88026419900e400103070107001a001103210000c0d04000b540b0010216442c10300712402080c29501642d0082c2d4149120070400e1400d00028050558402a071200c0f90340c044c09030b030258502800072182c01400705940d600907002164081e13030000054005c4001856202d0650311070050420508100110607801807030b01080322800c0000b10080450340c000ca03c3c2205a080c100c0448048500400007003026507003004403042c401e41901c01c8006040c01822aa00f2682001052002d88084401c4040c0c032916010400c0f189a174060304150903950006600e101b804501e0004030301070101074201076404625881d01c902203040c004020404548260103403151881e15180303031403c0b0341e0709184400100c1c60f107030090 = true := by decide +kernel

theorem cover : BRFrame.Cov 573920863 574100719 := by
  have h0 := BRFrame.cov_init 573920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 573920863 ≤ n) (h2 : n < 574100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
