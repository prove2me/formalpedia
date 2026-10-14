-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0065
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:39:21.979484+00:00
-- url     : https://prove2.me/submissions/1f34bf85-fbfc-46ad-b9ea-791599ff9972

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 11510798 ≤ n < 11690654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 11512048 1250 11510798 11510803
    0x3070b0703090c05010804030c0b041e05010e070602060103050a0803061c080d0b090c0d0506060c0303040b01060809010b1503040609080301091a030a050705090703060e070306031101021f09060e 85
    0x1039846101080d2160791510801414550b554050b240c2860b008002e8640390300d00420b242252038001d81740c680c09002050500c0700004000303102d071000105070800740e106481c05600034084003000171a107001e80107021445902c04a047c078101c0b17130000c4c000c146449940d240c054003903001403c0540c0c003940003101400c2082403110100b8034070340926892a01c402c52290420159080b20302d5651188030500100300303001010400b9a500d0020407040050a43c1e200008605148030b0141c40800910020040004100c280c0a80074181c034581e43d1030300c0d090344810f00780b0703030907507003008120b036481024080a0442c0c1c3c00040080c641c0140140c0c0041102203698079a9001035000b80c001c01038079a210302e1840c54043c41245180b0030520180c0040a6000183e00c4803502c80c0001d0140c20f01c52001c00c004607548034440d8014001502c2c4809d507494480c1040705001d0010203103480704031902c01070100a082e540d8004900380c01107402e90943c081c00d28414120480007482c100d8000c60700e9550b2a025803003610400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 11513298 1250 11512048 11512051
    0x50405010902040302030c0a050901090b0301200a02070b04030206030412021014090d0e0a12082214040e06070305191b0e060c0a03030f1d06040204060b0f190203070b 73
    0x55000041c3d495086005041c201445d250245010b4100303940c041200303469100515046480501d80020703072241702700c000f0b400f420640300705000c14000101074103201c1030104000d207084040364003190030083e600e2034090514025072001070342c03000060000034040303503601c00c0e044c0b868500c0c5d00c10b4a1a0350090810007080359580d0203480b000300d2180c001c000001100300800041f56540c0d04100035140c0030200011740340040c034001c184481280c030340b5078400c02001c401681c81c3c94502c0410003800032000c10703440e84501c03001c5c0316200200468014016080c1424030034411417603e440d005d0880c070f41d92540c0a4014101c050125145007001c46c0e24007420042c0b610a8a803101003000c040a2100110704005000c0e01e829480c2501c182c2c420010401c82050000e40c004079070f0b91508000c124109924403a60061454400d644844074180100111207000451694880c038821102005030544a400c52505400755001d0058070b500c003000201904c041080d82c40c010203a051040381d03d044a41d42e50800207180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 11514548 1250 11513298 11513309
    0x80d09020a1d0702011a0a0b07030309080f090301050c180103050907050d081801110601030b19060801020307020609010501120822150e01050901141e0a020a020102060a060302010c03081005040501 86
    0x1294424042c2c1644d0a000e041d281c100c044800a0350325180d100043d920381c03030900c00c1c102c000e0000901030701054000c1c0c000101d882d0300b108610351100c07000c0c2410350090b403040803864820b500e000300040000684030280c5a9458211103840c0c003200c1c0c4400103400178000070305400e80360f124018000480c1d503550f960b115501e51003070000a8561090005440c0380319039192a203414844040c81c041e242e5400041c6050440b50440420b50054803160107000071000094021141e00d420048081182a815002507000c0c581e42d600b12a965a20800d0450803034000707000324280f4540c4699640003240903c005050780701100e010700c40300c44800e100c3c60b02801907540e00c4460112803409000c554660059400e00750048203080042c940706441d40000d0200707a40380103619000e400803548400c054100004030107032241e400c50380c580e50700385108040c2d0b9645148000301d0051040400082082042e8000c2804803a410b03111441514150340c1e01360b60000d40100340310303526010f542c0009640d80d100d0003100e000b4203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 11515798 1250 11514548 11514599
    0x20913050a0b091006140a05040801060b030118110405040b03010b060c0109020111060907050d0515070201150503160303050a110601060e1002030306010815030c040f0203010e010f03080d09020a 85
    0x10a20b000740281603038010301c181c0401040384802c21100e500103801580300d02d41d4011071070b543c030b00076182950340e40520f800c200001d40ca0702501242d8040e52078002c40c141c480d0460142103c00c00041d14005980c07840d20580001039007448104007904141c1c02c100c0149200a0010505450540108031145c2050303900101e00da454190220555070000000c450900c81344014205900e000c1a500b60f503481030740315084c0500c8a0320700360001e01170240580e50b40490503040140320740c01e180750024040c02000f43d003950a905045800101c6240014941e0081150210319601d694a180c405440d15044800c4d584240501d07200c9c2d072001c4000c18000240601030648412900c81c10030b40c1405102e00690104030191750082007848150303a001410b5035403005005070300242c444503c40100341004050305a454000e0b0400001d030041942c0c42d00658161500c80c849000c060b80d8505c056200c0c0c0b503030b80c0b001501c4031008008070701072001190000c10704680080d0500c04043c2c0e9802010070030580010707003100d505 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 11517048 1250 11515798 11515811
    0x7030f060203070e012a0c080102030405061603060f050d0204020f04032901050d020904140f010b150301180f060308040603020a20030d0510050301020309030406120618020913050a 79
    0x207400c20311800100344c082c81c02c0d8802d4008100c05500303181c0849911b00308044100300950070415201000b034080d15045000b0b5441c3e040a240407075650100b80e4240b400d040c2c940c2200c016251081c4130345812500710408031340d651484c0c02c0c2032054007140f801050303070001d0b020405001c800b030030007004000452081a4400300810301200c100b0a01131302d200e0010079115002c0042210703644600e044065650126981103842d1079514150307500c01c1300a004a04580142440008100c03010750191034420703805d071003a410f0101302c81e181a2281c4800d009803d6a40b0489040004024407584400b140359110200050740c40d8407502c0fa04003941241d880750000a03000640c0c0b03035480347d0107401052400c2040300403460400c24107400a07224000d002040561a96030700c0001c0000604040210003400c01030001c5607a41081c1d010701c2c0d1240e200740101e02c0031070b150001110021407244984011146503007e00c0e004100c680582c54040e512086203d0b85c06207401d140d071030700e2112920425025144503040090f08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 11518298 1250 11517048 11517061
    0x70b0309010606030513020108070210180203070f081207050a02030709060303030b0f13020c0709110408071505030a0218090c030603120702090a05041707120801090902010e010302090307030f060203 87
    0x82d5491034021600f090f0402c030502c804001c1d0b250030807415540c2401d006880b40d54041c0100c0c9462010040315084608002e1400c103070100d501c0c10003100e0303070003541a00c10300c07511503510907019515482240700c80e60000068421483d403000180244d540b00700e041d2202e00c4bc823038002900e0040b003a00040900d9581f00010410180c251040206800069940800c941b0103a000549420340b81c00d00001b02540000c0d0151072107805011440242603440710030008000c905d540098a600a80910b103c1413007030210110301040c040641c08010442d55498600d15074031051048041d410a010741d4429500c0100c000d40c4682e0360b9028a0311420b0f96035211900c03860410304043c9400e02411000c64640b60800024000d0784442510592010340343e540460f054860f4038061709103894059040d09000e101081c801e08000002500c403d400100e81e032040c4159032900e01d098110356a4010080c0403500140103203103030b540a90040e00702331800a094443c060364a458410050403c0041116480d07400810041c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 11519548 1250 11518298 11518301
    0xc0b03010f050f030c01081503030d0c110601030c060e040906050a09030f0c0b0402040e070503030f070c06080c071203110a0306080d0503060d0b060307030f03080403080601051c05060d05070b030901 87
    0x51104079a400f070981880c001003900c131095280010b040054000014485901c1003618a440c0c907406012030740e4a4030300f07441410013001c66111120001d00050120354402c80c2c00509103046c0e07500140441c00440c5003000076640c400c1080502c80c0c019490307001090200c1e120784140e512807000000e02080340800c0f85001402400b00f10003034014015800e034900c001c9200c29189a40c8aa0b05076000621100301d0b600b41842e0135060350000b43e141c40001070a20249031107501404841c1d108030401860305440c2c02c8280c8001c00708642c80981c28800340a034401007803c00c000e04907142d41d5400c0001d10400130880b0244036030302821154003c00d440d240c0030400c0706000c101d17070408403031945002400c43c1041000a046d0716200325005c1d21034650540842e9282d0f40074001c0c0d07002564441d50200801c1402c0c41d02034821b8200311400d401061241d0000341c46540540101d40f0b418a803440c0c41c040000600ca003c5008180240107207410032010710601001560802c00d080140802d00303061a142e2400f00e100a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 11520798 1250 11519548 11519579
    0xa030e03010e0c0f040207060203010f060801090504022b060e0705090a050906040807030915123605070b03090f0613050309040c05070f06020309120708091c0c0b0301 73
    0x6000e03a160030318110b014440490501c8031074108680360724814540800083c064010400060041c510010000070000615580d4108480c06600c55909607aa20078402044030002c07500030307412501c402082d04107184c1c07400a41c08003614031100f4a02d121601d072176020464135829000c186c298440e00c0244118034100d41541e9004001140c240300a183c40a4110f45036100a44010140e080200d8804109401aa0f580740684602d20321614401422100100030100301021002d221b442c00d20200100903074240760741117600074001030b10f04042c1c4142c207084503844460300c241c5041c061010003080d26071012000b503010b089220300401880340380440150030170171301a001e0300d01448516000f0001a1001c401d81c0d05042088070009103d688040081d50030f031091060060040091110000030401039034055800b0b0502c2c0f8040b640d100c000d6918103091485007040c0684000000e0028008926000c1e5088001164078114041811016a901c1212001c1c0e5000010100004401800300c00507070101c1d030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 11522048 1250 11520798 11520827
    0x30309061103070507060f050409050c090406120302070315020f03010306020d050106020d020601030308070e030604050d021015090509030c0a0503040519064406040507080402060d0905010b040603050a03 89
    0x11882d03d10141d840701d40d40d40040c4110010b201580c417aa1204034000d009a134001c00b03407417000340851b140100a900890344031030703605485103160010201d02c0700c1454800d40652680358005140e0340d411a2544110402c0726200c1941c0c141c2c003040054100b031180006140258450400541c8803004014484e0541c0c0050b00813404641c00001c18113101035000400c28116501801c11890640741d07140100c0b000e600b4610715540520908081c40100308001606d01031140d4698295010603900d0b5105206442c40712815000d20070381404c1c107115109041d40b100360400c0d000c030100d23403030203496800f44d6040001496040d134441e0804102001141000c07544001000d900c031078280002403c16901504d017451510402030403d58840714000788061103201c031281100d24259410510100d4041d10b1032000c022194180554240300c08074880034000e010321402958028030309030805d03418440305802000c00e9902a10190b4840f01002c0c84c80d11140b003a1b00c01341d800740300a800301001e54200984600b543e0b4070300b0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 11523298 1250 11522048 11522053
    0x11a03040503030c0304050c09090307030915020307020111030403050105010e010f05010503010e0c1305090907091404050304060804030903080304080304060506010c020603060418080d1d03040f0b070206070c0303090611 96
    0x10000007a1010080301d0380030880c40707012500c03601d850905a290140d0544040c0c0c2207800034080c09a0103a00001502d0070500c265268012540c591004081000048103000c02690080c4a51001903004003100307000124103030100c0e401c2558035150070703082d21400c0c0d004180c5003a10100501240001040c2880600001c2c00c00391b107194908104504144002401b20f14000b00104103140c1000805c40c06400810000340018040c1c02c1141000d601c1d03004034490030038503615001070b80c9000c1c07150502a40c801c81d0000040c45c185440c2500030f43e20143d005008030200100c066001c0000b40314000036500a90080d42c54688a01e031900d072103011030340c0240c4890b052110000c880c0f00180c2c0c8100407a41e2101341510080381c004054581d01101d4803001d20010500c0c6400b14800d50490358a900070305000c603450140034200b040e01c4d20031a880e07210394040c0301c80b40200200d081c08018101e00081420300e00c064011494117589803034a91409600c0e4004a00164001c101004590703842200290340c2c0c00c66002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 11524548 1250 11523298 11523301
    0x10f0204061704020f01030f02090a03051b0a0f030201050c12030903120901050f060f03011409030903070e07020d050a09031a0702060109180f0618060b031c120b04020c07030b011a03 80
    0x171504900102c001d81056104c85865941448540560700b01c10707805402d01c445192a403038031135100c060320036140e600036104d0440c5080514002c409001150414075503041298115001161b1750740c4080084281362144c02d010003082c0296034011485058001c0c003450703c0e20728240315901e02d0301001d090074a941c1e061a0604c01e62002068000d078215800b110300812082101002c00c0c0944901e01d444046000010300300203000d48084001d2105210803026241c00c1502c03404606602d000640340e400c0141d0094806400e203500807401007149444d0350401d003101582c0c1e5070311702c05c00c8080304001302e41e0090780030140050950100301070790143c20b2400052052032145902036410300d6241601900101e0080c80e2981400100d81c000402d6200c803082e00103428100742003900c040e00340c4014103406441010300701b444810103440e400d10801c4582c2d0312408946010504503025091408041d84d020764204950040501c0800000c0c004520a00c140052907160040d80e5416203203010b90302901070b40420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 11525798 1250 11524548 11524553
    0x305100e0a090201020708070e04020405010801020705060a091106030106050a0924050904021209031905070c150210050702010b030c030c010e0105031803040608010e0702010e070b0c0f010f0204061704 88
    0x30300107640300100480001d005005400101c0c41c1043c00d40c0640964056440013281010300710303011511031130007a81e041c00180d9030b0300ba2243c02c0f4450b210740900300e03800c40c4020410a60498012503d404d00800b030740b406072980d4400041c0c440e4000e0f400b0300080381307000400454054110b80300300300038088400103008140c0304408945030310035411b4011040080024003150b03580c1c0c0b5a0b06a03020030524000150040c0342030081541c0d070394002c111001603140c4844070400b809200b0340c12903090b03691050b407a034001d520f4061041079161408a0440541c090000b4180302c00308180b080340d00c41d04481d0300200320b0402a030281800c18648030321b028000e4100c11255081307640c1012030080340c00428a403850752035545403005010b03609c1d044203c00c1a8040003600040c540d60041126060761003905030b603001502c4500d0264200c909404191001d0b4100900811200d08a00060608000054143c44010b515109014215488102c04183c5141c3c0418103100c65a07004100340c1401001070000d01b0320341001c0c5c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 11527048 1250 11525798 11525819
    0x130201050301090f02040801060909170a200f060702100605090906180307050102070807031202130512030c0106080d09050907020705040b010302040306050f0109050604090804030809010207050306040f0201030510 93
    0x14000e625030300f5144c032040c094001d11a070485005040d000000c00c0f20a894020b00c00242c55401010394034420400d9011300c0045185044800c0c1d0840e40c1c42da41048001024410501d100b0326130030002c02d0040c014a001050400c2c000719210344d019902070030f03030705941c1c3c0c004904680c00c0390842030003030300108100f0030782140001c0c1454100301004600b0b14201c000905640c590b2081c0c060043c40b03035002050342020080608040d190f0030b0311a417140d00b42e43e45403402040490092101414581c00498010012410724400d42d5910001a80540b841d151000745810f080d500c0035403040040342c0c00401100354450340410340d8000b0305012980c15148e030800368002559440305004203803203035640d40c141e03040c640e000341d048800031507100c0713424045d524000e8180302e03911a00b4402c44120328104800503026182a10031106490380c428941e905003810364540ca100d6812035500e05056219101002c80d2039030301005100d00c501e204d0340c8400c01455a520004064850280141040c0001d1110501150350003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 11528298 1250 11527048 11527051
    0x30209100314010909050312040519050307050c0d081806090402040b0714010c051213060501231207030308060a030c0305060a0f050411100c060c0207080114070903020d0507030506010605121302010503 88
    0x2148c2c114840340c4c035141003190414400c046994680d82a041040040000100140c00210700610665100c40c45120a120b05191411070041a40400700400c1d941c0b007441445880e48924060016428200742c0d801141c01ca900a03005087d28600101e0240104507000c020440140c8248000b480f0300e01082002500a0141003001444c0d48800400150405001c1301e04604050300308009001550707440c071010484a1000c840f450940307006c2990030000c2c0c240f490220300d40a081f9001080310fa1300d0f5880c21202c2c80d002801442c1d00001c2c1001c0040410038840320b1402650091000c2c050034200040040211441505100016402c0c0b000700004660440d080b09a44d00042e180902c0358082c05604803189048510010200c074944103001e51426400103c50054503007c80080040c01000307000c0c8013194030221180c1001a038014418801400c1c2910080d4030148101d040342c1e544c80d22651410f0170b10038240c0041000800c0403d10300286c4100c10b0a81d0b400414040d94400c1e07604050b000244980700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 11529548 1250 11528298 11528317
    0x180105010909020d12030b0d030e0102010509070602060a0209010504080f0c01020d0e220209130b0a0605040b0a0f0504090204080a0b0609040b0f1801150e090d050414010302091003140109090503 85
    0x2c4c0102039585c66030280d0040b02000d2801000f410701402c0c14640540b14407203107201d080c01907207808006a990b00c000118001503503100c1c1c004240595070805c07080d029620035401390341042014080052401e004100740c09107400303103c01a00542d580303140021b1600510030071101c10004c01c0c050000e40d0b40c0381d452060750780c100420711940b001f44040300800080d1054105140d00035000c601d18800744541c6a0000d021090121100e88150740c1d9280215403500690040ca01c00220070480e150405018000340103000b00d850800a06040e62401c00c2001c85e0000d5200103d2a00b10b4444002005104032409902c400c0448000d90305046c00c0e1980d52012070010301c1e2204c0315600402080c0301c000032801641c82c00f410300001303225038109040150070480d224440c640041c101c82c5c01203442c418021818000b2051190703181030600f85401c0700900582c4a0000c9a410705a0801c14814039899503018041c00e000a5103011410794140421070104440507841200d04910f0080040c00103000807044614412 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 11530798 1250 11529548 11529563
    0x216060c020414090a1118010e0403090e010803030907050607080d0504030e06040b0405040b0a0302090c0a0c06020d0b0a0902040b0403080c070e1305010f05070507030c060b0405180105010909020d 86
    0x10094400b150041201640051001450343c0801014060001d00403440d148034401011142850105000041c43c55070066101131452a006012140c4241c012591203070091521400c4140d444d108005100020f1b00450820703040001040540e4504002ca84000c1c80c0940e941d0b482c1407544e4403100031501511403102070558494002c2414148203202801c0c42e11801080d09554542c3c400c45200c082e8014403809001e141884030780e50743c0785005402c0c2d5044a80183ca000740913039450300035910560025103000c3c240030303245c100500800e000d0310240c1030042c1c072400c001583c090701a04121954616501024140e030040000340901c4e0781c0c00043d20121703540030080c540c0360b40c202c05000741491016045940040c1510f0304003c168505041041782c0540120001c000c0f0004d06054842a1503080300c40f0f00c040b40d030810900001a204016900d00a4050b40340000d61315011000101a16819210000300f20401d05c21411009800c2c420f0751300500da41c500411040040768007098407107649850180400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 11532048 1250 11530798 11530817
    0xa050a020f010c050c01060906030506130312051008060907080718021902010603020901080c010504050906030312040c23090105040c02030c030a0305040606140906040203060103110d020307020d021606 88
    0x5500801c48a410010028020720505a03903040c000c015402c00c0c200c400d607a60a2910000b49070f213862040c01c00396500300015140c1603450308500304c22120b000c04102d0030080b05488858100c0040d2040c7c9015122030714050f00114504000145000805801b48480d600050020003840703100103109d800f210044071845814071800d4005a000f40150800900d00001000903400c0069040d030145c81170703901c00c40304ca509598079070003115666103ca6a40f40d000c1103007003200380100c0ca0180d18040e4403c000038112441c00d8102d1104a1145c0800d0304c04480ea00324070441803001c01188200e0b1013400c030490001203244003c560014103400e10612640c2e0140b03943e230008001091081c400c40e4089544c00701103075a00d140710340c8001c000304011039056071038600e810808200940c9009203400040e5006280203140e844540030000203502c0a401e00e410b15036541079110b01c3c0680c45000c0c0022204003a80183c607450175180203401d1600011a405c01c54014a5404080c502210400700503940c4914040405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 11533298 1250 11532048 11532067
    0x9140f060f0c0c0a060c030e0a0b0c07060612060c02060705090a1406040e0108060103020a0506030702030a030b0a0f09020705010501050a1d0405030d110702011403060d08070602160b01030302010608070302060a05 93
    0x544980200f24203680684c080000c01e1040603048810060010358080040c0c5407030011494441c9a480d0006108090400c041000313003008801501515005d10800149a50354220f0f0b40000861a83d08030f5940742ca85004034400ca80506c03415512141504149103000b01210024800d1040d40c062300c82c0b00340712a6004002501c40806072005008050703008038140d41c40c0c2d162507903500302c2488103d2086010807404905801c0c480f069a02424490f0001d500b410040001075000e001d01c0351a427600b152900d10001101c00301504000c00a000b8100c0c0180d940c10541807490035544148c004500070310200b90200101d8101034017039440c0803200c0c1801f81c52034481e85081415842000c1c0410301141c10103801d83d051040e980b00611200313100340c1f01c4590300380310b6030307001000d60004840d42c56104940f9074178074010606900003000424440c0030f0052922285800b44510380554075000d40c0d41102c0711380181304141d024861a030242c2102e000504138070f49144c1c0011000e10644103404200900032458400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 11534548 1250 11533298 11533321
    0x10b030c07030318051e06130c0e09010b0a0902250f02100c0f111008010803030a020703090f030803010305060a050f0705090102010e06040503250c05010309032109140f060f 76
    0x284030350100646c1c00f13000700040d06600d501440001443d00f1701910011402000400000c01152944042083d10035860710540402c1e400b0000c2c1032400c20f5403941c5214240e41e882d0714203240a071681c1400141c4445c1f01c44050b2140c818520040c101154070014900d0100740d414400c5820190304494405850060203000c55024007a4000104a0074403a6140e80c01c100010040d406c3c80c2200740c9011400425074030085441350740c02e02c107804250300100082100720f0707056001031201601905002080a65271021492501c1c10ba500130f0320160401700040c8100030091100c0c541042a6400900035800c000d000b05203011000f501c0002803100c001000140307a4001e41146d0a1660b4100a07101189003500f8070303644a07481461113440176403150a0818142d1048003140c4422a040321840304640e0800300190014080d980041e010310a000034142e40c0364410006c50180200600340115613495280303002017000b070a1041500703058004203110110380500041c1c9692100f4407842000301501e80e103500c0c20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 11535798 1250 11534548 11534591
    0x1518050402150301030302010c03110a080708060102030715020306030c060c0706050306120109060b0f0103060b0403020603100e13030306060507020105120c04090e07030515060307030605091009030e0306010b030c070303 96
    0x802c03031021000100703054043d40310b42c162140e2070700d06100c00380c40d0080c064041d206100c182004518020046042030380f0923050030b80d2281040c0100c0f0710304481912038441500c1e944441d102d829070004208041c0c2e040a0249240d25801694054100150000c2e143d803503e060f40141c10170000c000c000642c032030f42c8519403e10501100e400030061540c8030309286000d090f508041324081eaa03810b092042c6940700e44130700011182070084040c1014103640c2080100d60000e021300d4144000094085030070702d15014402e0041c1c030301116640307100e01c4514001d01500c1380c1d54018024000c0500c40d810240c0d8100f01200c00c0c4651039a040007803907582c914810307000d0050341c22400f401e900d400441a04170200182c1001a01d0050741142c0701035240c40c6d086070340c04000701c88a1b43c25030400202080098000c3e0005a081207006c0199079449410100c280100c0c0d400c4c07402940080c800060340c0501d400e0034084203014180010313000e0314502e41903624403c10311039030800a04140d6030b41c081c0a000f0320201c0801c2c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 11537048 1250 11535798 11535829
    0x20d14040302120d090503030306010c0b040203010b040e070303022a010309060603060f0204140402030c0a081b0d0603060c141b03070b0a021c150302010c0201120c02101518050402 79
    0x950101051003421990b40c150000c0184c0400e50b0704402040d640b07000016680b0500b0141e66590022229a4484064000192040340c1564036480f000b4003075500c502a0003210300c0d0000050005500c2c50600a20342180701c040c01c04c9202c000180f0114903141500d107460900c0c0f0a003408280c4419030301c1e0000041909510203170049284c03003529a90b0000d00d80040049500000169800c00010420002280300940d2902c024440c00c015a0340050300400c0460741c00300400e0700000c0c1c0b400d818140c08059500060030036680c55030300e82e002e008000d11846240302e03403140c0f49400d03001507a45041c1140c1502ca85180e0814503c0d0000701e12a503400200102d42040c0e600c411a0305da03509100ca008806500080d03007105408403c0740c030114405e0320307610a100c07074107061b00c0700d04004910b11380041d141312041e03c00c241d0400034488202d042091440c020f41d0100002da9006201000d02002d2510840e00341c4075012242e8030030003808000e04650007114000784002c0039000611074031584001080d4060300000c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 11538298 1250 11537048 11537059
    0x2010807080105030a020913060e0f0705040b0918030c0109080d0507020a02010c140c030102070609030207050d030806040b040b0301020307020610060203070b0a020a110a0516060908060a0b0103110705060411030d020d14040302 99
    0x400102d030201c0e12f540360030403200071030b807443c0e4507071301004144e42218181070780010101000030070611000340100311104400060307901d4000c82e004480d0071745141401c1580c01840c00948864580502d126240c1d1140680c8040e161812080d40004c185101d80c10300504412520701c041400150248640c0604820050085540300c085103064005066104001d50260046403070006840c00d002a100e4101a8140d035109181d58134a030810000f007901c0800786070803a54030004012582c80900c000c0d40038025a03002400d191501e04c850088141d00c3e81c03c030500b107420a0000b280010404400942c100740140809601d598403000d0454594071506142001c174490100032101380140401c01605070200316403401c003038036200e0301c003518400b9036072285180036800400003c40c00940c940c000b5106040515001c10804064030000340c071a00446419601c541104040c03008101c4401008006c1c08815000307888160400130380a521103c821100f1428804482c404003c504115403c0320081c6500522 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 11539548 1250 11538298 11538311
    0x203070e0d21090503070f050102070303030f020f0d0915020901050f0d15061d030303010b040b0903070315060501111203040201110c0409080306010e01090e160c050d02060402010807080105030a02091306 89
    0x20080500c0103138440c0c58002d0142001c0850035491060520091301d07810380007060f040d40745560441c01018000c465100310380d820302c13001c0fa4041240340100b00d031801850000c01c88180b1828401c01a00d0000c042440c006e104109004403640c02c4002c0d1211402a440d1041e1241d610300c1c01a0042c001403442041051110400401d0781d0360081c920415204005540742501c90038403060590302e00c42802900310029003484100110707500b903002801d015002600b074a610503500e0781c0f6a800d0078850004143c050361500780a200710350b03226081ca27040041c00001032000c8690a081a440e0303100151010341081000084c804040e40d080083c6500242c02420030480900c0300d050100003174000340e80031800035113002140ca806601c507501240c10742e41103003a145c1aa4492208200505070521510018001d04611410200f1b405001c10304085506401070411440c06d4800100841e100070301e01028442d43c940148050744001408920303103503050314504282e44411100030141e004e91000200120704112 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 11540798 1250 11539548 11539613
    0x102120403080106080702060406020c1501060f030c02010204030b01050405070c050d08070f020307020307060305090f1e0105010b03010f121a090109030e0102150a020a050702060a0507020f040203070e0d 89
    0x150228400c60096407903145030b980b251030403a201101602c00200513884000403801085d2194010100b0041507412500406000400309005a100360300002c0480c401d41e0032032244c2d0342c05d030040301d10001c0d5070300c001c516140c2507a0381c0741100300060044900031592000000d82450061010810450300700d000c50354008001c100084c080801107890340c00180c107108450200900001c1a00c2d555540240500181800d100c4101d000348802460382c001c42c4210851080f1501c400d211201403044005885aa00e0500ca240300d825070320b060740a804004c00400040200452101c81c0314140c4001840005600d5103a0800383d00100840362a01d011500702014410035000540c040107542d807003600d820001c14070420041e83c6914541040040c0113900000140c5c440f4100e600611107032006007000c81c107041454005c43e20680050706100c020840008080c01903152070018000c405400b11810341c91490702140c01044c0760300342c0b00e2490144010900c0f0408000319951030107448200c00620080c0e041032074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 11542048 1250 11540798 11540827
    0x806010306050103120305010b0a03090201090b0a020609070509090d050d0209040203010e070305090f0a020108060d1205030703061a070204090201030f0e0106050103150303020d0503090a1a0603010c022d010204080102 95
    0x20700c000c4980120250701103583d14007e0140c10f040311804582181000660042030300a01014a0220304014a02030040f0781c1900520141500a0075517000704190319111051900c2d21246400143c403c0144904014000d0400980b01c10032203110310780507131680c1f0321900f208064000d8056559100c0e00220000c07810b0400900c6180c41180195424410703903c55a48075501c0d030841c1004041590803054071480554003c05c28541c21000180000354110710701d8580980954540b8016400260004240650030380e05000c3c9501502c2d015100d440b15000c5000c0d601c544bc821910024021500c40b0b0040d0196070203640000d10281518030b09100d0054444040c500821583c0610360210340303001c0c1d4402030070701c001c02503000380da6041d001022403a418003c15249070700020140102845031003c1c1400044007045125500c02c40c8400c14191814101c0415003551403801004045600c1800c1302c02402080c900108034005c2d003002031100019000384070030301a210725042035002d5800010080d2042500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 11543298 1250 11542048 11542051
    0x150e0106170c0a0b1e04080a050609070605030106020601061d040c050301050a0f0e0103020103090203121201030209060904120509030a05011505040e030a0903080904020912070801050703020c060a0b0a080601030605 94
    0x1800c00b40d5034141c0d042c6081000500702801030342d15038203040c814151641e003c0d034801200a064025030504040d0b0310f0410b203250841d5110102c4142d0880001d000013040308100031402f51216040c50350442d0b050010003582c0b0b400512905003040300c494916a14468407051a040701000500103000c8015410380182c2942d10078490f035800340144440000d01581d1142c4610700b5a180700c0c900b060140d1940c2c00440240081c071070241d074107004020075042c0303203404400102803040043c420001c0d00c1d0315500400c5a0030748010311080c0618000c2d41040002100d0b0710701c08003000c50a05000e070722820075501081c07818182030340c01407981d031034448a0400101545401021580c0454051150400782d513000b684a0007200101e6000c00c1a81105100241030800070700340403100508014204030100c2c000070100c5980300040c0580742c0000c401031004110170700070242d00005601382075141c10403444521341d4482008240069250799100c2c121203664031144404000d11740d000450360705585900300070005000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 11544548 1250 11543298 11543339
    0x110304050d080a060501120c0e0909070608150306070f021e010203090c06090907120207060507050304020405090712020904020a0b040609080f010c0503010308071a01170618030403150e0106 83
    0x20ba0030001c0c02050240c0505801e80c0d006a596407142650810070a01401e0840501d20a20403402c0342c50507207859040304d0703511400454000b485068a031000c0507114020183c507502181401b0100c0c1c0102d070320300003040313a00030300c192601c1c01d40030b510307080100d0034080d408600740c10b070740c0404d500c0c41c062040540166003c1d641003c02e031010040c40b4030400801d486000c42050704030402400044c145802628514081c410b201d20242c50001d0680d111000c40320104e48200200b074020003800150706251050340c0e4020f50340300c0100005810804003124004c0f40d01d00085c030a108002c002411900c81030040f0000341080b0003225203850f200c0e40050280d021318000c26003140b00f094200c829010050003810020304017038441e18070310b90075600c0d42045076001c55001d95400b000000e008106400101109000f0700741d00c00c05081c400003039020582018000782c20600c03200981c01268503036140120890702103c0e070060703100d40480075514400026024880703200c219540f829000181a58240c0689540300d0b5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 11545798 1250 11544548 11544557
    0x120813090e0304060e0303071220030403080c0d08040809040b0d020a0306090210080408040603050903090a0312030e0a0b01050609031006080d0906080f15010e1504080f032506110304050d 82
    0x82c45c21041c9075580c012008054030000c6264424000280501e174101204581400d98820f0a13a45002040c5150302c96807048400d0040024804800e00061201d044c10070707110b1918440c5828680c41e411003600500b0311003889203550310010403060360b88900c403111035030740a030a14249541da410078030000c192000090303000383c0300c10311950f902c3c034468202c0c60702c66948500405d041a0070603600f2070003044002d0101a45d0f1000b002007019594a251840300114841d072020307448240d40352401015140b401d07000d541c56520202400780000c1685141c0c1d0f056480c19100a82c907400c4a4000030310f441012201070394598604900030603442d20219551b1450b190f1074589848443d6a640100c9080310b04962111000d40c07c940403454201e48400190b03040001490300c04242080c3c440050f07488008458050f194540000301001100c805201049087e07800f10007542c2083c142d00751802d00d40036465261644840072a0001c82004002d502c40c02c01c1c405c402c1600c680b80e01d000e02e46590b8450b0540726034030205 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 11547048 1250 11545798 11545817
    0x50d02070b03040b07080709050607061a060c0c0f040612060507080c0703080402130e0f03090f04050402060301030b101517090f0a080c030408010504030c030305060a120813090e030406 81
    0xe841071400c50380101c0c0d0003508a02d4a80ea201401c0781ca00501608a00403c02c80110004480c0c0e151301c05020054080c403000070b80e28041a4881140e030003003e021074011502840100701c40e01002ca5120703181ca605544160071a81c0f8030000030300030701c4690004d20a62144141c40d4052100d150300c140d1091040740c032051200e40320400c280c000f60080c0b20000303001850807000a001814080c01c0d100d41042080004034103800f001003c681061006002c0c0c40130f680c0041010b01c00b5251590020000d0070341a035081100d41019000b046141c4014000030701443d600e1808262064000008c51008101420078015003034442c201c014081c400d04030b20348502030340070b0300825846000462201c41402c40d0354028100850551786400d4982c0000003405420b000510000031800b40078095944076a02c40d55400c0d208007a24a00a821200e014005c0e501482c0550400d001c1c545482c125001c46a4100003403a071a041004649000d1f5075007904080c07151030402020428440000000d00241c60381500ea10a40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 11548298 1250 11547048 11547059
    0xf050603010506091c120c0b010509090312100803030a06061205010621230117010606080103031b0501091103010608010504020d0b06010c050703051506040513030806040603020d050d0207 82
    0x96020a005441c0e010a080140d4821842e01d80320034041c05c8603580e04480c030342440d512022001240c000503000420595080340040091a40741103016240031240f410b07541c1415080d49540780030382002c0e500030780c0b6488049100249061030100061400340c007143d80c0d91401034940006040103118160105140203030340300c0c2421143c02128140d5032261398504100442503c01c061030380c6240c05481000303030741341c0a8903c3c140d5040f141090301ca041d10280f5519500d4030401403030303040b10300140e0812a40341080c00e109280e03100034014116a010715100740409030864402c003c40d10850f60040541d03107048a03241c00c1020784175003103006d4a0103d00800181e40e44a856a00381d44040310000d61298140f818080000c21b120b00c000e402c0b620625207071486040719039806140c84425003050741c40d80e1180c0d541010400b00d4104141c1e210100341e5007030100b030400ea014803a55a0800c40b0050510000d51300092082e2a5684480c00540d001400b02c0d0824000d81419500c4442803103071000180150b45004c6171 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 11549548 1250 11548298 11548309
    0x5040507030b090a020306040204050d062004031121030c070510090b041205010e0601060509090106090e04020409051c05040e0109020a0503010b0c070308030a1a0102070f26010606090f05 82
    0x41655028040f004559a035018110003580000d00391640030340c3c240008150358407035000304003409201e01030010b000c2c4100c0d880c00820a00070159203100c00d03030410082c00000c000030071151144030152a104005201c07a0701c5254146413400070001a44030100b02c0000941002904400303c605c180e038808140b2020030000c031131038140b5004042800030100320030050007060780c0084881c0c0340200000140210f00b03100103410080280d00080018001055000151074541001d500408103814001c1c251403608400141554000b880688500da0300e48811040c80070a0002c1d400d0200d00c079030005c0c0c03a220310400217445504180034580e20080d180b800898042050320031510b1400c8245c981a0843c1e00e0f10b002240d060384000d581c000d040c050b5110006c00100201c01640c0180d0251341c1c045176980c01e0100c10782410841e100d1190441d803164408002080040c0c80780e20650f04120b10348420f280ca12107013210103210074502e07010384e58a400000109240e020404805507a081c00111840c1682c4c2c0e4100301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 11550798 1250 11549548 11549561
    0xf03060108070e04020a03120903060f0504031205070c0b070f020601140303090613080109080301080f0606100c050a0b0703061701020304080412050a140601080c03120403030e06041206060504050703 87
    0x740d4080542407100c029100d9603a64001e03c000c140c200c00640780d0761100320310000c02c02058003282c80701c1028001c001003800380a005144002d4200b22510740b80d1002080c1804481841e6182507454011a81d680d2040402c0040560011a0101a818480c0c00244020304030007008006001c3e0100200b8920500e154442c2d0500b002001903060202250030070081d54051084d090111949080008000e41c1c28000c0403000d074014600309480f50302d8500e03030030304045d1007800e00d4120f40c0208003000869a00c0c4044004801d41e54034004120380c500713151440c58019020006000f000b1000c04111076203616800c5a01030351640030ba01c18288952a405500782d0106507002441d50000744010700000e014040ca03041c54a0042c4203c591604081d11654080300e0f4261110350260440c000501107100f0800c8241d4000ea42a001405c0300c001c01c0125507081d0240340030080070010b0b203200124880d50342009981c040d100748282d21300040010304e0000300500c06441340c03600a41c20400018000782c0a4070404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 11552048 1250 11550798 11550809
    0x3090c0405090a0803060a090507030501050f09060102100e01060e15010207121106030408040e09100606020d050414060705030a0809060601090803030a050705040801020705062208070f020303070b150f030601 91
    0x91441c000c80c1d03a0b07490b9031303504001e001c4c54100c0283e18000a0f400b2180c0617090113540316860020f45941000103208180001e030300c04034003800e0610b040c084c1c9070747d0010312861194004900081c01c00741d0754401d14050019688054491401d040078001c050a001c81c409240050907003c50f10000e948600100c041a41000040c0c02441c4954917600315040c480700550f805441120041c0c139040d2160000f4801e00c5040d52601d15503801100c2a014514003031142c4005400d4500090034008000d80c001005d52141d40100e9014480050805480380c42d1101a15a51540041039070b80307446000c0001084810100d840034402e200c0c0b0345c0450200e5020b4189181618081c10244d4a50358608a10700d010306806031480080260800c000030707400c0428400b030000d4520400250a450810045001d5422242c044041003810708600440002d040d0004590030315134442c00080105881d4000030b4154050404041c1010b00c080c41080b415511454010002900480740724480740340f001b00b8103a4410303003409039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 11553298 1250 11552048 11552053
    0x1e0e06041101051b0c01110304050a0501050d02041a03040506070c021f02070e0a1a03070f0302150d050a060503100902010e120a020301110a08090c010212071a0103050303090c040509 80
    0x8140800d0110000390300c0d601c0103041c81840c01000c010505a100c0c50504e1414841e0408909a112584c0c0200b80c1400004010011810682000f0020308001081d00c10541401800998a00c4001309a01600d000b403100c4c04a25940f000526036410700c6602c2290111803e0044c070780041c9065000c0c030040038078241c001c1c04054900034188004110141e418691005511680c100020002d21000034180f062512113004619225503000c1c42d800c03084194111442a000742c0c000380452007141c0003201c202d0b501101c035880c4411001d400950309101f0003444020b0603041008002580d00b494014004031003064040f10700b060000c2901e04111100c10324000e0000c0c07200c1d000c004080c07400000300c4050703a44000030744904004650010707085858079030308008003003404541a1000c83e004603105034464064006082c4511102000035103030000001d00e8203c8040120341407040c040170042c5840c41d10400600e0351a25610b0f802e10594a8104a071441a24490003005180700d04080c0500e6000b905d04900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 11554548 1250 11553298 11553301
    0x10612050c03040605040204020705010e0309030c04051e0705160515010602030307080402040b1201050f0105010201061703190e06070506010f0b0c07050f060909040b01050a09090b070806010504080f011e0e06 91
    0xd5100141c45c01038002e0b64000e400b403211001081c828403038540014100e20056980c2c800c11002d060500706c1c080c400f0f5101c4c61410080289010188031440102c052031784415005540764041560b850003229149203100d82240850410011300040b452803d68010302c10b6501a0303030f1440121390300e10040300c62800080031714001c04c00505240d0002c4144200040004204030240c00c5500d08558045441040220b80c100041240c0d58080c85100007078a01d0202c4452a0501800026560710801100c110320f490280022142548240b03121000d4040c0100225692500d90400c42e43e101400e00600307104a000503000102801b0100480d030b62a11140e014215107880c0408202220b0120b00046411200811044445a45000003180704502ca031510710000e506100900c16099455004a4001d916107418203021602c803100603540b104072482c02941954480004813494020380e03000b0b650601c00d003030300c2285940041d00441c0011060741d1042102a94101074402620384045140c40315410400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 11555798 1250 11554548 11554553
    0x1003020609040507050408060f013f0611070b04020a0906030b0c13180207050c030319050310050d0f051903050706050603070302150406030b0307050f0607030c0b070c11030106080613060609020c06010612050c0304 93
    0x11a400304cbc40e019000006442000076400425603129420488069481408100c11850301900038401340c60264000c10441d811130340d5440078401c0240001e190705c900410b1241014071132000c02c03c05400d0404940020104814424010790014001281d6038061a482013206090000554080f04c0c60f4101100d110a02c00a069403ea40302600040c042d511004000c1056181c00f8101c031101482140740d1307407243c0c030350f03080090900002c060044a0045400d4900000c40d40c0482034a074166000040014241c5075500003034604030740e0740e10082d000051507983c2c0c113a010149000d007040b6040d684050049061070003c06403204c005006059110150524485035403c040c80a014038a100c5c0c00d005111440c5a101d0007013100381100c1c498001222000703c0010450703103250f50008110150028041541428a01da85818004008442c44202495240300b03009a5412203070040c4507400e800c55403084d4410640c2c0d1910801d0003040085407201000300c505003a14400c05200701e9034010a00d0454031640d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 11557048 1250 11555798 11555909
    0x30b0f0906060a1b0503070201080a021809060102030706050403050a0e06070f06050c0708070507031e0b0a0b19030b07110d120c0e0603130b1003020609040507050408060f01 76
    0x401e4201081a02d00c4d0001080c1d40088100e0840d034003403402140c5841d142d01c001000c080000b01601c0300b071401840008012390b900b000c02400d5510480b440a403560380c4400403407550181e004080c0846042c50244014035070800c00400c2d0402071035813040c0b4128040001d2140901c12108014a65040c1c00c00c0c250208011383d001980112680d21582c0c6844c0c40b50701d07250078540090f042034500c1d0b00700d074400300104110000c106c000076910f03010080402880b600e80c0501050001c0c0402c80558503200c00704565518281120350300000b062041280c41c0d280d08021103440750442e4190003084800c2e600e5080032100140c5043d110700f03280c0d03c400c0d154943d50400d10162986131200800e205414011910f07669400e0302441c491b46c1400703a86000c0305a80d05140103a10f034050524804490404014800b6850b00070403074003041820794020841da00c400100f21041e04c1154040e01140c001c0c1402c0c00782c0c0d90203001ea240e0403200c8006400b0b060010a56a01500c02044074403901100030600c1800801101c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 11558298 1250 11557048 11557057
    0x3070204050a091401020a020d0e18040302030d06090f05090105090703030c05120414010801091107030c14030a0807030b03010221060a080d0c02031608070506030c0f120403030b0f090606 82
    0xa40c0790100f00d8440541d1600c69100c9440038018590b500071a1344450694100810b03092443d0034034242c6415031a0001254148000c0d00c250001004e0380000141410b0080080307481040c04c2c540c04010080c1d644420000501003103044054060908011400b14a01400f07428020f070629806004414a550b41c15100080c508004440c540944a42c1c40100803540014100804102e01810400d4121200043c01542e05070051460a468941080c241c40892000c0e030b401700d641420400e2841e40303141801d25001044031281c000c980300005444603043d5208c1c003041d000e003440fa10f051103004101c01c205401d0740111055421480751100001d1240d4000c504056080003014164201da144c80d41c0031981400b0f10500c5540200710589802c404505040090b55607000d04088000381e041e0421a210341c4460170340c07103610b22070300340840403c4000c04400e00311098584091a4240da8154400c2da85000500071942a40031030314203844140d050a244010042c801c40080c25016595215000c02045810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 11559548 1250 11558298 11558311
    0x510020703021305010503010510060f050a09050604030f0308101202060a051c0515010903050607050a020717100b030c150309010905120d0617070302010509010c050115080607020f0307020405 84
    0x240301000409a240e0b08140001c000c9203102c007090307941c10101414296240a0b145448000c0e8443d4100405d95002e54101043c6d422850100e9030340c05195002c80f200215500f0059000741e000a0010070411316014421480344203846070681a0b40b50000c1c0942a5514840c03840914510140040142340c41c03002405c80390b41d503003031060400601c3c1c814103417171801d100b20f421a590f40c2c59050101c41498988904c854040910b00403c4803400d5a580300d4075a5809400c1d1024400d01042440c44030b40203100d4503010b0420000d40d1000c03040500b50312681c5008505030544110b1800240346101d08010510b41c07a008400b81103002000c4108601403107070703030004050400556a48a821000410500c40c0d000d2540300c0341d0480d510b5424000c3c210007190b286600501590308620010754200c0d20204a0301c0440e60242442030b201e041080058465071010b07000103110b5440c15141d2046200c000c3c2d80c4406039144201200c1c2140d8654009907514826900426a00d90092021200611702600081e505c182d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 11560798 1250 11559548 11559553
    0x80601050708030906010303020f19020f0609030a03030c0f030c020303150f04060306020702040b01020a0b2d01180b03160b0c010207060c08070807020601120f03030617071a03010609051002 83
    0x707005499200307030b41d08295006403464100c2401041415410091a034462802d200942a0601d250750302540210b540c0038004c4c080d680a03941d4481c00c0e038039401600e0f06100702a09171043c00b5620300e4018010038072007103401c001c10000445c11258070701c6071041150030b004a800551031a03c0718403540c10718078081034410358003030f09201504040d038032a405190000c40c481e01003d61030301c1441c4104416282c0c4a22802c2c1150302940444011505886110f0780180c680d18000e6107030700380d5407403140490034002861502e0381116000040d42c150103d8090700d03464050b0000f00280c2884504044d184e200380c201c00742159441800900ca031401c21001082442c546200040c0781c0001d6584007804c6c0d544001581d004104400100280203400002055204013140b014143c15814501800c02d840722126018200d030300c42e5003c2000f05402640040c01070500c01044180d1328550358016a030b00d4200340074075100c0d15804852500081c040200b41c9042e02e200742c903038100c050700300340912000400d280c50000461 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 11562048 1250 11560798 11560807
    0x10303120b03030a0302040e1b0403140a020303180112050c0901030e0705131e0b010906030506010c1a0613020f0a050a0903081201150e011e03140108010203090105070813020108060105 81
    0x70b55040004028070311950302e015880b945441ca000501308802045907006113103041803103203014450320444056030350020682c1c42144680c0c00891034000d0f07014000b034241c88001403203541042c1c0042003c18008007643ca031088030000442d000d007a1a400d0b1056001c1010920044100b5806900001e01046c0761008641030542d580300003c5040b80c66040c8403104c4e9654140c15800e02652412103195091504014481c8018500000300040540d1080c2e10406607640081540b5070300c640c2a1000042c0c100304046650200c6c1075a5202010041e9801c0d4030406000501400c0c90390b0324000d03a0314012000120714180b8080c020240c9050b03200e0000c190070030004090100008034007001604040c40c640c0c034990100d40c10700f079003800d2540c0d095400e241031105003104a2503da82c003210310100b01c48040460a54020085801c1d405002001d100c1c06629411b4400807404910540c051071040d1129002030103903894040307054900d900700b034468000e000300e01296400954011107502d50004010714120303192 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 11563298 1250 11562048 11562071
    0xd0905040b030f01090b0603010513050a03120204120308180a0506010e040201090e070f09060503060f0f040b030307060203041214040e0903040f03050a0203010c020706050702040905010207050a05030307080c1201030312 96
    0xf184e080305000c83c6d220b080101030100b5410244a41035011282101c03042c0c030040c407a20f480d5030ba002203900080820901e40001d007114403881c0c065400034000f0031b40c0c0100b424094076000d003400d034080b21610b107422203460500c940c10700d00180c2209607030341102c00b401240e420031040000b110340082c4142d06000324000005440c43e800400350b8462045640c80d20b81c4844450310003801824594000020000c0c1803042c042c099031402501d115440d001c45410685001c2900420043c10401d01295450300001c5118402d2002640003540b05900c0b803d0f45400c2000c070f8403415501c402800301d04154110050005000213515044065040000d04c0100d03400d003503031442ca40c5078449054100322019042034801c0c07000c50409018003030701f1003524005031680b181000c100521038020468081c0c4129100c45408007400420750440d920725410000b030701c01c409100c2c1410750b500d074015134860b80080c2042000848100104007614014004019496080d910f90346040b5031113048460005140d65695401408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 11564548 1250 11563298 11563301
    0x9040207021c0f03020c0a0621090b01060509010e03010507050406080406020c070b0a020607031b05090f0301050a02030105190e0604050a0b10020d090902070f08031308180907020d0905040b030f01 86
    0x5100d03c43d075540c04014a00b85002814001e400000c1801202c5030101400880d4000c44a1004281c40c4200c040d2410802070011010b0140f8070f0300035200c002c1c00e50002c00d08a504c0801000910340c2038868205030755002052500303c960071510000001c0d0240010300c003151007000c98580140c052080903040c254444081400c010b41e96102e036400b0100020b80c40d04060b0140308081c1c0c030031942d060400482c4410403901900c02c0e51840180100240081d00505a40c0c403140c0040d9440c4015008100380e25003003060300300a601c2030040912170700c40b1560741007454401c00100c0d020303203904204a41c1661a0241403002500000d4030802c034458480240103515141c0c0c961034400d40c0344942c01091025100c000241081e826a009211068010000200840c0501505c221b1540e40310505c0caa40c1d503102c481007060080385000080c02c4a0380054120b250200720310185135204004c4170704001c2c07a1201c80c0d00340d030758580d0b40c0142c4c4080390801a00704114a40380d40711440c10200030b4240c0700b40c24800100f690 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 11565798 1250 11564548 11564599
    0x307170705060c090f0306070207150504080f0d02012016020a0308070302010c030509160506070c05030601090905010f020405090a0507110a060f0612020901030b0a0207060f0902090f06060904020702 87
    0x114804045000c1325507103003036490814403038010340203012241046a002174540038980224290f601448040d028418401d6007120000d040b10820780b003040b92049034907038940007109007400040d801d090004424907034404141c06003120902e24280350000b00c4031502c3c184400a0310590b8000003043c000404105180005d00c0c0380da100340e00006500c416914068100e94018107001e00c0f45e803002d41810300002c03103900b146050320000c480e102d448194a1402d940480305580201e134060041c40700008668080d80c00000b112449500240026040f6030f0400c000c9016074030480b03034807d80a00c08144200c0456000310b400c5005071608a509010320709540c0c1c98181038a004036041c036500c00130401d40c1103031480b681c03000e006007040c009001c01d041d030005291800c06000c05440344600201003441c51007294100c82031564001c60034008086070403190310003002100c43c01d9004002680000c0c0d55800d4015801c1e00c61440200f40500300102c3c4000c2c00000e421902d030898000356031180c2d070140c4010700340005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 11567048 1250 11565798 11565811
    0x5070201060b0a081816050409080408070602030d0f0507080403050c01090506100503011a010206040201110a051906050601030c0912020604050a090203012301021908120103110a0506040305030717070506 89
    0x340c2da05117124449a0f21070f10304424401600b0405000402c160041603c0e4200c030300490f40403c404045081005991140380e116015034428441d00284582c0c021015150000180c0010032070350741440ba454054403c120350800002d40840001000207002d40d01074100c01c1241c200002d0345000e150b49103171030a40d041e1862449c03485201030410070307464240501c011641804180d88440c05a2000103580c4040140000f4144280c00c01142c680c200e040103245201c54015045030040544440280c50b180001c04050320385506042c0040c032236500900864841c01444d543d8005c406150402400c03240004000899100004200000d05a41d843c0010300c0a09044180140d50f54075101040e450b540003030303602003020020b022209034103a80102e004800a134200400c81121059851f0001c03c80c880c07076218a00c0303200403100200074402c0c1400400c8542c00c041c1c4410114980700c100f00841c500551000804641c13080205900007070702c0b40c81543c2603040301c0c5500c81c240620f80d40e40074203107072088900 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 11568298 1250 11567048 11567057
    0x108070203071b050f0f1804260901260106050a120608030409050f0103150906020417070509010503160311010c0203070b0c100501030503090108190606020114090d0f0305070201060b0a 81
    0x340303c0c6150401c00392601480480d80891b030b925854010924003065100650850a21107000600b4010074842d503026005005960791901d04038440150041e030450400b060024142140000340888280282c2181c0714286040d8200baa02e001c03022149544001101c004000c00d040022106e403800340200400303401d80d040590b44407400e044850044400c014004074921403801f004002090b003858041800c20940c00d4003040011315402c009001c1d00c15584030440c40301c0d20a410300d5680d40007140440135984201e41103415645d1301e02c00c040d0ba03001968400310042c03605000820003d0010b1616000001040c1480c0800c0b541c25000281000d071282c0c070103200050005152000741c0d4003800607080b8131107240740400c070650641c1c450b907682c1d00404c0e44140c1440318804c007048802c02c4840e0814a41300300f54405100c0030b52220b0009010b805420502c0d42540c081001240c5440740c00301d115a85031300c4680d15101020350010b003c8019003030107015101595600c140108080c1c007501e000b072180b85c2c0706444 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 11569548 1250 11568298 11568353
    0x90b01030b070e101d09040602030a0e010c050d0905120309030a08060a03030e010c0c05090c0703120203150d0f0606030303020c100c0807051305060301140306090a050a02010807020307 81
    0x100341c010020014520020407558981c581c1c51039a89000c42e80c1c900c001032400030100d0312018444036030101d0030700d003440c0e122514070100020031609400075885503015041c2880031102c406046800d8030248001900410300a00040c007446030f41d64480c1c1e0141c0c0c010012034010340381c00c4481705074507031080c0c42c0035119800005d40c948809400400e541d0f0042000d0b00d4180e1503510b903840040154113500607942c100f28400107030205114050f02c40304098180203181c07640714100340541e04666800542d00f00c0110340e00c042c0e00d2234805036601c01e8074071890000141d9440c120a4000b00010403403444012035402441308003450104642e4800d06001e5482034800590302e11009102030b14101c0407407100d402e9607007800d10084040c1da0000d0030325000101402c0c80c2d40c0724451081c81004c0f04240f07070811a0030903004000011400c0002501d811b20700c0e4198140e8000d502d41a00710345c0c603019500d4000e811030780f08003d64401540310b00c072074030f500001c42d105807410614a9a100080d07001d0007440c2400741d588605 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 11570798 1250 11569548 11569553
    0x506030f06120c01080126060703020a021506060301090c0203070501020708070b010509070c06020c07030812010614041d130f03030504020f0a0e0c13030203030c0102130e04050c0d1104090b0103 85
    0x5841e1800c001c1070310000c00c4040003400008140081c14058071f02460040c2d000d20000c0851003100403800301810080c0d551528012170010000e410861b00b001c010300c0b42a202c9020910480c072041d00407940034250520350f0b03091004050240046955400440c8000c01808020400a00c00f401c1401c0c4107608655035040f250424044802040c0c002d5841100180c041c014116000000d1200c40c0b42d108402684940419401900b004c03c03940c0007809108c800110f01b10303121400740205040e29881d0301c8800c8860b00265000c41540158050030b01c0d92107503a050310160001076142c0503401122001714203402007103991030710324030400034600700c021a4444080c0421864141200d030700041c01070341d01c400c1861401c120030b000d204001e03240a44144000171400046507200b080c40e4069900502200c0d07664140502440c000d50160740d10090b400200034010641820000d0905d01440e0070800911a030078041081000c0148403080403a9401909034104003291520700641040c90f000302000c0f00a5071460 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 11572048 1250 11570798 11570809
    0xf02190905071b110406081f060e04170705010204050a0806040605010501021b0123030403050c0712020f0103020a0c020310060503010b060304051c020708100504030e0307030203070612060506030f06 87
    0x3412507014091202110003540c43c2e43e21010002d15084088503101e40100303404a4001c204507081800240981010740b1224581a036281d2035464815104111080d5101082403c803002620b00501405401040c0214501800064203030389006030001480c1659960009110401c194458034454000108100c01c2c86128420140100020300141503070f80710094181000d00e420450444c10311550026614003181110034682c68001c81c1d4000310369904150601a106030098002d80d126441004004a102804003010020155028240c00800c60070f0300019030294120f00500c804001c0c20104030703005a581041394802c081c50b82c05000a1301810101407500750345058143c0c07070086608106010003d1000070351030300801c07028485201c400082101c120f0602125511610840c8200520010085010341c40b882c080e5221342c8814904030440e50602d61074800074800603501da08410340070010b00b03000ea0000305444854140000768640c496001412541081d40e5420404070700d00c0400c4210700b000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 11573298 1250 11572048 11572051
    0x30c0302100c0206030a0e0309030604050a0b0106050f0d05060103020903010609020a1403040209060409080d020301091506020d0e090901020c0109080a091a0a0e0d020306090a06050a0e0a06090f02190905 89
    0x7514110003803a5803600880c800d444003800701e800040d540c4c40084051a8103000303654000c0300c01025101d8900341030078100c0d601e00070300720240c134582c0030300000082c014091002ca942c150280506542010241c1c80400000c200040c0068180360302000001c086660a104410103000942401030300d4070100311008099103030300996840b04040420a0002503902d800105601541c02c4601044026a502d01700041e40101340345508494000b00010459145070b800c2003403445548905642030b2642c40c642284d0f108054030001020070b031421044221030815100c01c5a210807140009031402e00036001e89403c50f0420780f400c0d160614003041216460358030003600001007030f206540c91408142010300207910f00c01d1a514509101c1d2074803062185898844001602d01e400600f52503161078190005d0391121500202265601c0ca000000b603403d508a10580c54504a080e0080404800d43ea5589000f0681d550303082d9000070403071440c000141d80d0300803d1404580465400d060f514503100b490301c1604e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 11574548 1250 11573298 11573329
    0x9040f0605060103022104060212041401110f070209071404030804080708010606080a05070e0405040807020301050a0615050702030f06010f061701060509131b0e0a08012706060b0301030c0302 84
    0x10000142d45030b51b90b0303600e4102034486100220f0341c0c0e1110f00e820710091142c0c031110440e04d401e420800c8140300c0b500303840b05003c0701104001d101c14503013441618040d00c98500701d43d804980034003a01016061030741417030350700c04903504042d6252013803041d40c1c225603082a0300484200302c00243c184502c007801d00c1110011b02c2028002d2001034181030015104003001024030141c241d5450004201d01d104042108d010880036208100b5030420b0f00308038200d6030028806034001e60030a00403d0f4074410a01c2a0411074050660b03074005c00b80742000c2207800340d10845060707030b051040041090f240075052007850700800014420b40f00329482c2100260003401040b00300780c00750305000f0040000d10b8009044581d01801192044800181001200010008034a41c001d2100c11181c2080d0050b411408800c0aa0811100c08450903580c0d41c0007401d84541340e1300a003603a000c0c0d4241c00d0041d61510001ca171131920410340441d400d5120f040e08100340d04242e00550b4801c804980800a500303000b10108030840 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 11575798 1250 11574548 11574551
    0x70201030e061b0c030702061206090615190201020c01060603050103050d14041a0c0714012a0f080c01052d060d020f0402090402040b040f08030c060402091509040f0605060103 77
    0x10340b000600f40940e0241c01c2ca8408841c00140700030707004505008503545e05600421090b10380060040040c9407400403134a041c0034a01c01d0b000b04807603140c103603210024103c070303a298140b8003092482e0303800c4031100100001095640a01c10381801c400c01f8083d04026007450350b4002200e41c035604050345450550424070003030101c0b0983c1001c81441200854081d568a803001d101052840720410010703104401850499000d00c082c007040d11581d480c4000c01e03082003603858602c8407001d000810b044c0c504500511812406550300e420028000700000300700e40740100542420f2410042501d82501c508503801c00d0281c0526800d1802e00c805201098000c41d030441000e000c600c0e000d004104a20090040603108580162242a0a95803601201c0003154050425500c96a4072201034595411070b00890704401c1c4040000309665800000b0703104405000c4000f40056151502800b60f0103c0250010a500c0103403003003032100741c9542080d0b0340141d04c184100c100150b05414401d0445002511305410036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 11577048 1250 11575798 11575801
    0x1020d051c05060f1018090b06031b04030b0c0702010f05040302010206130204020d0213031214030103060b060d0c02100b030105010f032010020d0f0c020d0609050f030c03070201030e06 81
    0x1003542020740400c400c01d000c00100da496010000d5150f4001d140019485404144000605ca600444240c030303415094417810304040d100c0d11f1840664041901c565041603041c40012002c200a089800608a42810032440d05449480c0c0001034503003124040a07020000504c8070455a012240040250140c544241442d0442c3d0000391600310160160000c9130072601800c082d581c541e4120b039003114640b20115583d00e00141160100052440140e0710861031015480c443d0b4068800040303201440403a6a195a0842d40c1d44c400a00040c2440350f045807081c4078107140310006d4400c8a220b455141c000341700b401d1554540f801541c03100c15503940280d040030010804603c800343c00b40140c0c1d41c84520702e0100041020440401540030311501d034800d9407100400380583d008a06403d500581e56034180554110380010789100c407100b41d000303401c5100c1032032000110300b00c2c1c0e1154009a1042080c3c3c0c110b03a00014500d469900301765420021504005802005c542c0c1500c20b002e46041e90340042d1005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 11578298 1250 11577048 11577067
    0x10c0203120f040b010b030403020f07090c020c030303040b0106110a0605070503012102030d030b0105070c03030f090f080601061101020909190b011d01030c0c080a09060f020c0307140109050a120201020d05 90
    0x1900e0b011b12175145070001c003101041c10180244907054800e020310f806c031002c056641c1c0c0b202d0082e1540b40b9000015008a03148403280b814003004880c800d070380010411a80d0703403904504541007819050751000501a034404980011020300586008400329541c0036101c0d41481406010f00c1c00504000000002210a4a0050f100070510812001403414000780c103030300103001031355644a4000001e0116034100008020141c0000c2401105030380daa503801030903600d45250341019886070241c505c0c0d0f03a11160040090b288580440401d0400d140000350419000c003020038521182a41d1003610080c501020b2103c00c60a44602c28458009290074646580f490740c2071040d4045104405042588500304440800d008441c03806880da40300c1c03100c0b03030781d204040002030800d0158002e1000180310003c800042c14400a054841c02e107004002d01003052400d6030b0f500c280e10b41d58101d14140400540c000699984682201d0000c155100c1c00d02c1d01251148002030614841b0080e010034408144041d400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 11579548 1250 11578298 11578313
    0x60801090b0c031012060603061409070b0a03020705030309010b1201090807060207080c1005040b10140409110d050705040b060a09030f05010b0d03030209040b0609010507030e040608010c0203120f04 87
    0x100020314400203650b946421300d4841c000c40711a0003161349900c41450b0201044150760140702241e009180400c80ca806100209080000070b81d000340565000c500140f100703c40c11700041a06001d00e0030014600b040e955966411078004a4a078602c0340d544661900c41030500e00540305a40646000811000045548002e040d0040c0c1c00041c01c040d0f400300e0328a0400902030102c0d00c2d030203030407002c0b10210300c88214140003511040344c085400b80840c1010416051100100c0b9058170070390030000b19002c2040b401c1c00300030310300c1c0c070800c0d90b41d103800e02d0800a40c1d40b01c10301e00034000303401440a007205600340007d100c01c1d038480d0130016008003001c0080c45015540100004150b0340e11058903000c001c8581400c0d0301602d00d0504c0c007548100441d00680030035070154003c1000103070540341030000c508203200f00a014010341c100e450200c2c004104681c000ba10072400c01485c1100240005161034440e00f2060860340c02104550160303000040000440811494a65015100f0401d11000c0c2c6025502d404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 11580798 1250 11579548 11579551
    0x106050406051c090506041e0201080604090609020a0602160b04290708040e160c15020c0a05060109090b09010905030403020d02041409060a0e01050405030a08040302030409090b010504060801090b 86
    0x20704010000c074000c200070108042c0800712290300d2000340003010303c90400549175103043d40c044507145ca00d10311685158406288030709606405031154041030742c07180180f102074041d8000c11265591b130b0320500c02c01a2381d032400c8400a480682c1c010084124040140c5501c0390594018202d9a803041c04104400d104580f00c940320801482d90b0f001c1d61307034808032070000980910328004006d0030022070080350f50b900303409d4a03c3c4034072980e2465802490303072413805a40e46c2e044204047d0058070a029054103c104030b80042101d11007000484c0c40d401110340b00c0a08042c800c2c0c0108442a48a14601080c0003407a1201604480e0f210020806189240d4030301d99648100d03c0020700505086d40c0150941d0313034544c0001c0314074100c400000081e2820310001c0c0d8480804583d0781c20f900d0720301561070b03c40403814400c03180b060354441c006503e060230344901652501c4008000b1002c5110402011801500d0f0b406080364140c460308a6981c6541082e08000503500b8940096020768500111400416241d21005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 11582048 1250 11580798 11580809
    0xb09011202010c02011103040b0a0f03181704030203010603050309030639040b13060206070507030503060402130305030a032304022409030f070504050105010903080a050306041506210501060504 85
    0x90b9100300c83c4c0f006983c1a040301e18818514040400d00241c5014420020440c82056036a99609a44240015002c94440b550011050880100c1807000903118020420848030810300c1d69060503502e500203401d468640d003045565070804210050241010020320b600611031160141560b0008100729102039004041035074241e040c0c00244004035400f004031406003c5000c00c650340e5640521131710b1120400d0384503460040c030482c00001d1580d0300c658281d40c0f0b079a40c140d950919580b202020071000c2c0d0048280311a5181c261600040081c804000600050895850215010101900700e4840f05c0a900381c20f0b44c8001c00c0c008000059460241740d01c08000071803428034018001e2910050316004105496405119410120546d04d000041890846100311801e1241c1d82c2c0369001100c0d1802c06100c0100340b14810f002c0d440f4098041d00c040c5500110251002810121700c200300031808100390300400c0803800c030090b80c1000c45c4d859400100c0e8641502014060b952410100600742d1141d4403c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 11583298 1250 11582048 11582057
    0x40905090106080307061802040c0e1002030405060711060c030304030903060501060509010507061508030406120b0609030307080309010f110c060a0e0706200307051c090501021b010509030a150b0901120201 90
    0x42000503501894280745250f00030300304200d4070f00c03100c4003d03018a03912f0001c2d900ca00c800c040088006c0d0300c0002246e05903040501118180449940c1d0f00358861050500c85500200500c0b0708682c00720104080c522a6000e075881c18807035803950402008a81040c0c001c0300400804200112869030080c3c2122110341c0d012500003611410003400e4072018025030042c2e0000d000c00200021403644c0952940c03400281100b080046007910b00410500c0d01c124401d90340c05410034466800403070700384409540c3c06038402e00082240c0c0b5501c0b9408080758640c3d03921030755444c0003180c0c02e00300d00c00420180e81d000354052010090b210f0040789091345c0304900c0c440c2004220942c4600e03107400710b000c0320303403074038141800304494036281c0c240743c6103840d00351000c100001206d90001110006225840b440121041030300585040c03c0c0981114200f001d07003500807814080c0401a001e041d803001c0010b0a0802e000e508050004c04104009405a03010300c3e4070603121f005541d0050101d414951240000180e0900300b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 11584548 1250 11583298 11583311
    0x6030c01050702040207020406060509010201150f03120210050403021006060201050f011a040e0c0c0c030625031b08040203011503021e030a0209040c0302090a05010e070c050f010e010204090509010608030706 91
    0x40c01a201b8079400941041c00c00400145164101001d0101c1500c00d030000e00011914505030001c90300d040c49140c0320310400c3c1008102141040e101c2070845001c91047e03401c0c40c00620003010a8440075102200141d001d001c0e02220048240319140207800184020303c500c0c2404200d9901c564410701940c03401600ea2404040c140d4041401c550007441803402030030540c40c0409400d4a55000400c510302d40f80106090001c062501044003032050a0101144141d45004a40d00703428100500c50681416a54544403850060031a03080c0da551449035104130041c81e092041c50f00303540709050040e807003c016800920042e91001d80e08048184490101c14401111100091604e81300000203500711030400240400d222490b1030003070a40f4000c0d2442a4a0b88544031104115682442071040048035100840c00d01d512035000c05507450301880407242054400c0300c0c181c4c211030a2410600c40e90394001000c2020002c540a41030b4402507040080000c5464208241d45a1255400040070147e6961 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 11585798 1250 11584548 11584553
    0x402011716030c18090509060f0408070807060b06040b0a020708030f12040c0e0c120c120403030b0a030c1805090106050a0b030a090506070302070201080901060302011b0303020403060507030615030506030c010507 93
    0x10140c84843c034480301c0f0f4400b9695145d010720300400f0b09840c3d5900c103018403c0083d544040414885010b540c0c44143c4a00c0e00c6c0d0f842d1038103543e540001d05c2c11280e0715268007041c851035440e000031b04060300030900625603401c4140310182c64244180e1280301e05400500151000e40c2c10030b401d80d41c3c8004a480c0e4800c5a41e10340c5402d072560116500724001050b0380f502070122003a000005010f000c419134000d105942c403a4000300c1d105000b4800040d03002620b002c0014002032080d08044290000508544181a1241d482503030001058005d50b001d00306a08408085254034011140c01908400013080000d0900011a248000f107026801544100001240c000c80960384061300306600310003034030350700d04102600501a40c891a030a9002450301400301d4400c00062050500b201c2e070584403940c0d4140115164106104c03410401d8042c542c1c28000000451600d0040d42e105507803d5400003002400c085159507407841c0150103a04140c5044100700d0b05880c00580c5007140007007420440d0f1501c0c40e03403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 11587048 1250 11585798 11585807
    0xc080a09050f0d02030703140301051e0303120403050c070506040b030a0b120109050a0b010b0c1e010207051b10080f010509040c0902070b06040608030a0207090906060f0605030402011716030c 84
    0x610002d11441410140c1440503804000f8140b014071903a031f660301c20303990315a600391117000a0240c65030101302d119803c00151244500e074401c01c3d001800b900e05055600d030740181030f038800700c50079030200f034000842d410405010710000c00035040c221200350525003800c074032410b60300004000d8905141d5446403548140e0300c21001441198000d8002c1c41081070910f0101d13295000036800700c80102a5030004103807010004c05507100d40c450304e0000d0104854500d4211041c004103e41c0e24407c0d5030800c140e001044007031100b0902c0d0050545c21810b12140c0720140007a1002d0040380f201000404028046e0b00b4030740e1240a81110b004448801ca20384403424000e04220640e03100300c90003440010443d0070408851402481411304540401c41d140e90340384505c1e00d0f40b06ea0100d000058000354400d0183c600543d100e00450b60041c1c81c0000c8407030b19042001220111608014040360740442000700f15030f4090580b011665803880d0b141e62a051142e01e87d41650205c042070010306465103d4404501e115 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 11588298 1250 11587048 11587063
    0x90a0902030a060314011e05040611040902070c0906030503071704050d060501050a1d010303111e010b10030b0102100906020706020301030807060c05070b0105130e011d010b040612021504050402041410030c080a0905 94
    0x2c0410700355445a481379040000d5205410407601180c1000d0300080b05403041c440c40b01229086400746240115954072440c4030300711060501c0c00703850140408035242e1036078031065040d98810800040e03103505143c2081200c4a469200c00400c1d011100c241400c0c0007000300c8141102d5043c10305131144580120800d0504156004d02103c80c0804281000381000542290b030045406480c00d115082d1104800c40594000b07007401800342e03200700300300c2411b01042d80c0304452903030007208010b0510884d40c1e6170506aa00aa1090300c0140e0081004002e000b807d100b80a20b10705642459443e0010660b260721511805200d20b0b84a0b00c9140d447c12840c0c50103401040d42c08461800821002041d0900442c049407281060401c070340c641684461181018032a030000e5802c0f06c4025400d4900390790820040701608803000d2000c1005000002c1c003070f121030010784050418822801b41c9400c03a04144210a41c0c14212a0301301400c0c0f0b90412600c5400503545078202460440205482d5518140585408003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 11589548 1250 11588298 11588321
    0xf18040507030207030f0f140f0d021603080c04050f09041e0b070e011103030a0203060307030b04030309020405150d080904090b10060f11060a02090a0902030a060314011e050406 78
    0xc0c0410009038a80c5a40100f402c0c030702c29140c00c0c8034442082012500d48031801c4c0d010012542d4101106ca5054185028101417000b03820028548510428108260b8104050030220a46c080b0034407020140c020010607840342c04011520b0509242400003103101c1d01082d406805540d004000c5410b001010341141c02540c2502c40800d80d54040b840c0c28400c940c400c41348100060750309003123071500350310135210300640d10240b40c025030858480300d0280c0000d500290001e030741441907410000c001860515058861b501030385000421840d540144026184001c0200c86000000c2c00000b4850340d602030003240c00e035000b2102c0768848905002040080c20724113000340c81103164004102d0741c00c803441a608156a10341d9a040910000000c040da41c45400c99011001074100800003482c1010b45d41c090500b121000f0003200c1e00725582d100f15003ca900540d0b043c108183c440000340140721562014038013840c2e001000b0001680e501d1209140c0c1c0c4960b044d4006820f03151404101402019008242c0b4070b80c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 11590798 1250 11589548 11589551
    0xc080405190302010306081b1011060901020a030b06040302060706110409021206190e010e04020105190f02010605060306010c06090804150c0507060c02091602070e010906140301060b0f1804 83
    0x16100300d20790420101d5120803400a4181200450450004540c4081141d1102c0707408940d80d481c5420810007942d80b0000100b04200342d030b0b00c481c1e480002c110a50042109000040e03480e01c0495004051750020340c8040d015500411007040103855180403501d500c0d13084080092641d00386521907016108a07030010f2003650000c41ea1045500421007168041d8504440800c0300151009629091070418440d2003181510080100300c031030301842c421540700344140b50071486c8c001000c0f00f0003200054100794000081e0340800840b070980d024840c610251604940181c00c3d031078200c000903c02d0a01000041c00140c580e4406020021198103a038040d080420101c407440384000c40c010440c404c8090b050382c2d58132849400045443c040e10900f070740c1903009014041942d9443da291702100e072102c071043c2d04501c101c1c0000a08041d200d011180038042010012515074540140c0b002181c0c10080443e03c00d91602104021003081a03080380c42c40805400c82035202c40b1079808107e004003000c00c0b1181c22a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 11592048 1250 11590798 11590819
    0x3010e09120c2d03120903070206040603050402030c01080f0601030c030b04050408030f0c040b0702010503090a0f0b0907060305150f0105070602030106080103120206090c060c0c06040f030309050105030403020d0c080405 96
    0x14008030300784400401c082c6041110003c11a1109048070001a0384407450304100040c4000344902e80445610981610481b4542140c03540460806d44c07081c0c1c081400270713607200306100441c03038280012980704409103000c80b903d04000005494910024058038140f40e99a140d0a6066000340c01100b43c0c1640140100038034540340c01c02032011307070085810840311503004000561014001c804d417004e0b102c18030295030400c1206d5005443c1030380050310300c0030b6a11071810395400047e69100b404c8a000e10610100465041400c1c22030f280c0003190f0848824941030404002040c0b0000d0706010360001e044a41c10304198003500182c941d48900304010b80300700d000000200c0c99642040c0514100c0f4421001d00009a412880c100c2e10341006581844d4150403244182020b451300c0c07000f0704990704840c03060310702c0001d00200240b01c03580541d1107040704014804041051640041500004290a00340607146141590b0029111807003140400c00341b20b21448490203012066040d80c0c041d050161100c00d16 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 11593298 1250 11592048 11592067
    0x1090c06030501120c030206090406090906091407080c060306011701060807090504050606121815090d0801030309031416141207120f06020702041119021203010e0912 73
    0x9040060041001081c2808000222440d0452000559076006036008035441d0175582000340f180c0c002d03110b455009460390004244040e0504c1910b01c101c2c880d21002940102c1c0b0701c0c0c030985580c9808a040714580090500300f2a800380843d1600d01e40070115034141e529030702c00f030042c1c0340d40b4400399125034000080d10001c503a0941180490340241d4898440440c0780b40d0303440420040d03131003c03100c0b85c3e001107041c03104814120072280c10035040210140c2e5130107030581e26204c0d01d00c1c2103220124040301c190600300780700f0401c50500c4040520700071440c0100d6158116100503008060501c0024042892030301030040d402c10601240070481c05803030440801c47d5032010f0900d054580c900d8114070851201c03c442d0119a130002c0c1010880380e100d6440d602c8a0310315142c03d0500b40d00d10505a455a400700240d0780180d841d0710680c109414100c80c2240c581c160b207401d40342d80704041840d84c4103662010016840700789440007540e0444210380a1035030582c0e60440032038100184026102e1600d2404100e510a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 11594548 1250 11593298 11593313
    0xb07090602060a050411060d06030611040501030b04050c0301031202030403020a0612150807180905060408031009020702090c0315090106021e0309060a300609050601020a0302070501031d0109 84
    0x803100207608546994907144042c0f0101c61080d900100790310110200400c0a08201c0043c207448010108002341c021b0380da40304e25087d0b070700d0141d00d0014030600280a00041d038251040c0d642e0881d0aa90402884c40d001d525400d1920045c0809001c4881c0115101c0d207592080080350301442d13010340081125940d50801400400700142d007401d10f941002144000303003281c01030040440740903200a21896107402841841051010880103003640c480e0b0203c0081002004002d01461048400c0381d56031070600440d696880c42038214190340b50040007244c015030785003802c458000c0c400880c410b507aa220658403607211040e040c8a02e410400c1382000042d4079030040b40c61081e105070581008015000450384540381c2c0f00301d84200340d03c06014040c1d201001d02c6059106080354038290f4032107604003c0c05444030a1518411090542c5031600e01c1404207507120302800703400480a00040c03900180c43d9401948455a038003415040507942c1e0b11000ca140f070301800c2d04411140b5800200002000c0382272544 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 11595798 1250 11594548 11594567
    0xc02010614040b0d030f05070b0c0403020109060f02030f130509040b06031c090312090b0d0c030c03020301030201080f0403140d050a0c05030702070330020a0507061107050603130b07 80
    0x50701e40c1060441903a9007002c0c00344244809000385448940307546944c060b1140d01102c1848420000140f120b640060071a081d850702900c3c44c1401242c0f41d5240d880014280f5845400c45130030084c00c50455030b070b0560000709540d614407241449e140c40d070039404070b240003084481c0d010550140c00c6030188414008000b07122070007407000303a0a4910030300c002d07160001c5030001035031850001080101e041000c03400b00100d521800c0868582442a240ea0b41380701419500300c000b0030440b0a0b03540448202054140c850003190508608040d81150314580020305138940c000d1000900c548114001010984a203110701e00310420720020a4560031b01384a00c00080804844400c41d042ca448201c0c041d980c05041524030582e0240d0040c6551030940d80c80d074414007032080000310745500440482c01c14881d051549041c0d01c0c0d01f40d00070f204951450600529200d420b5108000f4410040704005181c2c0c0c0106412044e030708203440316543c03030f1100d104010816a1144000e405041c030801801a44e80e80140d000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 11597048 1250 11595798 11595809
    0xb0d110304150509030c030405060c070f150305070f0903030509040b06030a0e0606090417070f0b010612140103031e02030d1103010510080c0306120307021201050601021002120f060604090c020106 86
    0x3000703e640e403000c54540e02d1150004010241e0f00520041000c0e141031401040d0003404582912060399442c0301550740412aa006034548081c108114195030354948901c0340e0003a2186440101e42e24440c0b40540a40701901001d8100a000210009140c50325000315882c1100a03040c0c82c1e880c134115a115004214a000005442c099000401c45c1071909010380c50107280c02000800c40e00c2c0701819003944507444404200d45840c0410300810100b091542194000d000d00e0300e0b00c00da61060324000c00215040078400001d01010000140f01182d400294131400070900c50b80c240f954095000181d06c2c50140030b07030034908a41440c04110440f8800e80c0554107c400039140c1c3c1485800e0803a06503202070089070b032490f038418103000058141c03404a508182000c640c80940785098426000324583c00401154050380b030703464101748034aa50381005002e0b0f4050700800e0071030030020303402c03c10641900081c240350228003581c2d02281b110341c1d9440894004180d0fa890030490343c02c004801030301801e801d200d80e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 11598298 1250 11597048 11597051
    0x507080c040c0305010305070504150b0a0512070309030f140405041a0103060602070b0d0903090b0a08010f08030f04140604081e010b0108040f020108070315080f120a05040b0d11030415 81
    0x1007185043c040d00401d030680e9032180141420f80d0404042c0b100a06172019000d890741010440041d2150300c48c0c000b80700c000c50075a5101c1c1c0e140d94514046031200b10161840c010507141c81d5901000c207034400c2c0503a500100ca031800c00048144620304109078002c2e9082660300500c1c00082080310140d42c1c40c03070b1146c46020b032000e1221320342d41c19050782c448056100d08404210100604070710400603600c81a01c1500c2814025405500c6101c1e01c0c119401c14154034011036403440c014401d9040d100311341c03001011204021803600313210044088503030056104400c0407400c640c8034040d00781d40716010388024144070f00c101c030003030300c0c00c01c0408490070540b101c2c43c4015441c104a0030001d51162001c50303c940e0b0452540441101181d0044440c0384008049030209581c842a042d04041c5000c944c00003810210000c0c070303580c040f070542c107414024480515510504100610182c958004060b9801c80b045071075010346800102e60703080050300f0300417100c03403145000004102c2040040f0b90300c040145201c42c030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 11599548 1250 11598298 11598311
    0x20c0a060905120105093414040b04020906070209060a08060f070806010e010512060d021903051b011b05070306020409020406020f0f1c030b1302030702060703050609040f02010c0507080c04 83
    0x4516003280c0050743c000000350003070b941c42c4003c03103180b841c0030b08240403000040b030f500c044200450302c410280b60405043c440f103010359988d00745814090000c001e0002c50b021842c10440c1e500203111841403200082c0030394040c400094482e500e80c11380e0401440a0f90940302d143c03a0000104a480c10f048501c040400d02500c00300303400d035104038103120b101d41c410303100c5910306505500b0041d00000014192a44101c041c100c0d9401600c03801000e002c00d4040751362403101c81e810b40ca04242440d007101c5441c1c6401c20b04283c811090ba81c00b0244208808040560b90348404803410700b03030300b846260307003024240034000200000c11480c20340c000d01c04c40d0300c0755003580e00b10003c4102490329000a0142c05040d035001111185c03000f6160b0355a0581c0d00128100004c2d5070350305030046240003440891004115901000f0000143d0301845442e51002192034100840d20b0001c00187c10344001a001408000101c180f1108590044010b11110743d002800c0341c1c8600e030703a10740e001c0d07460000d04000340c000c0b810541d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 11600798 1250 11599548 11599579
    0xa06020606010c06050901022701021015050d0c1a040509060f030714040e0a0c0303090e010e0a050a020f03040605060a05061e030903090604090507081b07060c020c0a060905 76
    0x60041d015000c165a25155401e05490303181c041c00f030180c400e1403195401c10010b00c10b503001d0090920304440d4005458500b030102c2d000a0705102561490110030750400380c615000a0911800324260340d0102c3d0b80c000034440703900b0100c610351007580100341600c41d156003200d03408500801070004c0b070300c0c1260402c22980d26101070140d4044051952901030f4000c42c024801c2c41e028242c8500c00f400084c0000071045039882c1c11300c2c60058041c000f2b07140b00c41800414001e06500c100304002901c0d444447c61003039450300c0452442c0810081030b0b40030315551040403ca82031526011141a00300e0f5034199030b0cd0f401c050800354000c0800b900d000f0300c1042d046500107868101402079481440c020041c954010812600300700107540020321902c800c4c0820440c0100c00d1740d8920103007014203c0d00b40c00142a103800040540b401e0b078050200301801d00c0c51032124a04c94015411114600c0c2c2c0003402040b51544603070180c0c9410034200c403250340400300b1a80031035001d500040410469400315a030030380c09000705 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 11602048 1250 11600798 11600803
    0x2180609070309030c120e0d06051806190c0210051501020708010506060706090206040801020309030a0905040213060c0213020307020102070308130b1303050403061104030203160b030a0e030c0706020c0a0602 91
    0x20780140814855001d00c4045401008401c4006c0345a050803145140783c080012120300102c48103c51055564040c48207100c07440b4040c0e40c2d0950780400515003030030682c0180002c07560440214009548600c1202d400d81d00c28005511407041108090240e4100101d800c001c81803d58080d600600c5032000c005500c0e001400380600500d00601014600650340d150303d805001c04050603038110f0380420002411036003d1008502c640c00c150080c641340c034080100200000c02c164070851050780144803440081c04c9a521070320895409081402401c400e07440030480c1450003000f40d0844600c08801c1100d45901900141002c510a545465017035440103211a2a0a160103024150240c3d480000e0880c02d40c01103d43da0881c040d007000c9091590300da403580d00ba654006e1000701d030710030046410030843c20104452400300f8001001118081e00700070459402e03000081044007110344031041d241c00c3c5d16082c81295005174040064a41054075203802a541d09455400c1a0203020398003000140b06101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 11603298 1250 11602048 11602061
    0x5060301060f0b0c03190201090201020f0d080106030b030a0c0801020408010c09030512030c0c0106080705181608100506070602090f120601030201030504020406080105090717010606080c16021806090703 89
    0x203000301407520381800c0601d061900070804c5000300d4807041100850001201c0f200407180d001603800810f4074442031000900f800b11b10105000141e0051807841803480e00106c52a06607001742c5000140030030400006898041c0204c3d010b071010360580c4021900176410f400030825252000002e0080d6a4000e8084071600490310018245400100000c445120010011500700d401441f09608001018a11608440756a40900115070200c20100000d040c100500d01a403280030f00700c032a40b0714083d50000100c140c125808402c115691001404260101c07554402800c8003074441c075250846850460000d40c8544850351044010100c40403091409924080200c10b00c4000b49c20b841e4690f5005602501000e042264800d4649202264000007440380500c190300c414000c0802d03a1030a0151034000d02849009401c1e41d0510f5800e2022a4002c0308058000415102c60380e500c8a0384980d805450003099030082d4000c01080500d1038040300348800030301030313402210200b000781c485020650451f01c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 11604548 1250 11603298 11603309
    0xc0303070213090503070b01090902012d0809030f040602060f0a150306020a0504180b12030405030c06030612060f090118030c081c05070c0501050609011d040503040503010c0309060506030106 84
    0x1903803001d07201e4520036003100c0703c828803030021a814182c0ca0340d41d0300b104032401d8000700c5031955100c068506540c0e001c1004081410140303405c01c21020700d017903818081c0d45060b8119051064410105d506440c0c1002201c00383c0d49500701a644031078403910001d44030502502d0548006030050046076603520540705942c0b00c1013412404110311855a6608806900002000800c1c403030144000145919450100c00c4100905400001e4036801d01d0204401c0300c0e03d1102515140d402484244174a440000ba200c01103030046503910b84a81c2c480000038101c2c0c4201d040b400e80c0c1c4c0078800601103000b4900300504c1c050340341c1031b0084c005030f40b6444081e50480d410750340280c0003407560003007000031070b407a6801004d0f030801c1c81c0c5c04e00c1101c00c1201d2601080d00c1080e240c850000300038118410600800303100d0303145c21007030849029181d03515081d55004007a0b0080300081950310340c90701003006c101040045500800002c1c0c000d0010362010240500101a14003003a103080e414800024000c1c5818401c100035500c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 11605798 1250 11604548 11604559
    0x40c0f03061508040318050301091505100e060d020f030703050606030d0804030e010309150606020303011a04080d03020a0903050601080303161707030209030a02090f0a0608030301060c0615030b040303050403020c03030702 97
    0x6649882c1100c40400c10005410b080746c800310003003101e0b01c3c00e000300302e4901d000c0d11241080c03100c2c044071481121801401400c04000b240e10038080c88800c281d0b190f42195044540c010701d140d15000042c80e0044100800343e0512550800000308007000c40c015100d51000c07010748000e600b0f2402c0c00da840c144211030003400203035448a110f25542c001d034004a07144d4022411406001d442c00fa0038802c450350b54010350056070001c001003000c582c2031107907148031980e0a40b0a500307103880c0c6850b10ba602c520b1044014145030b000300350304520601c2003152400854210044602c40c1d40d5900c0c400f51a5402500c0401c598081c0c13110705c81c0144c1c02155500031100041200140903a02e0800480080d0001900c2e10307414000c081c025000b6903140e4513118010b0341d2a8001ca500c9003450404501100c05da035129500c00c0c1c200b400104800368100b002d046590307410100100e003c03094800d00c041a000160401001c0c1e40845041c40245541640b00c148554400d03001c4a481d00c00070700801d6540d0155020080d80030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 11607048 1250 11605798 11605801
    0x30f060d03050c0a0b0a061a030103020906010509030a140d030216030e040f0c0801090b0a050d110301110406020d0e0103050108250902040b0d060e040201090b0315040c0f03061508 79
    0x242840c0e03140820a074060300d0503d0829480c070300300d9400d0910508041d210904041c091050800c25849844000c18049584603101804115401c041d800140720103840380c41c0c0f00c0c0c0090300f1a40148203c3e038881d00010252000c2003070301d02d0310301d041d0780842021081c05c4c80f0b0781980130101c130f0003842140c400080440644110584a540803642408000142600680c03500a8031002d048680115a00a1000d07180e0740203660611500400310303180041c0b02445900c030000c04006a0b280c62034182100c070b030414084e00d0700f1101034001c02d0140c42074401100c2d25680010300002c138540d000c03562012015140d030350360b130461034180011404d035102800f03404a103800040c1d15406080d8540395003020b41c030307180c5001508140d0b00c5104004980060740b1407c107101c400030301c022800386940703d544081c1003500d0550006050a4000a040d0f1303070503014081c60060000081180e441c0c558031400100341c0000c10500c450400a9401003d0300401c9090001003824007002040245a6501144190515030b03a119841d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 11608298 1250 11607048 11607061
    0x7050603010b030103060903020a0210090501080618070807020102090a090914010509030d0207050a0c12051e06060d0f060c0e03070602120f0304021203040308070b010501020c010e010f050906030109090302060903030f 95
    0xc0081fa9412030a6104070680f580040c1c89003180110a80503c3d21901241840d140000d030100000500481c49890b401e00100c5400f01011101a049052890003600300e50720034030103a0081c8217a01410303a1189480c60005031403025074101e510518451070041140c4145814a5400d94105a5140000b90010b001d00a0036240a0b03000d0301c1ca2074020804c449840e020740d15219001c244c60303013000391104507818040c0c05100042100d50884070f81801c0c90359206084804650b26100e01410f175522980940340e03007005011194001103e502c0e00300000300522245914044c0904e0840004103000e4090302d100020101d0010542c1841d02e020300d070586280252030300d444c3c0087e500081080f42c0c0031001001d03041c00350b030703041018002031407160000079601e0071941424102c0714416444141154003260016001da680800d100301d4181082c2424485684801c4040e00c060060300d0b07405401040220000940e40f41c541c00040e41a4041c0d000d40d4507079211b102a8984034801219461b880070540d0011402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 11609548 1250 11608298 11608301
    0x40b041b0f12020c0c10020d020c010f0c3201061a0304020613080a02040b040606050d05040312090302030d0e0303010e0c070609060203090d0905060a02070303030b040b0616030207050603010b03010306 88
    0x5411602d250801d040401c400c4254100d0f04143c9954180340c0c014141c0c10001e041080c1c0440d00100035000034122503060038002903403078000d0301c1c0c2c580c1040341010a19903002c0c0110140c01d01a9400402285101280074000303083e00c0d4000040c080d0f43c01158284440080c044c4a110305444440031021507881079003d401d4060341c0013600803038000c40c0401030076142c051202d04040180001c4000342c84c0c40d00e214010001521483c0b40f040788100d107410001c00885030080304440d038054202001003540c7d613560a003954520b03000da03100d81c0194207000e8242d0030964044024140c0c2800340c50208411446115001c1d520300090158000c0002d100c000700e050300d02210007502c2d035248134841c08600c8e62001e5890030b040ea0070943c0d690315981c1c0800f0030b01e08a550002c000750050702094496500f0302c402100000d503540003a12018052503911160024262600c0e04000d108250190800d96130324510140c01280e9090600203034018040c8407408100c5280240469040715111071001c1d040da400c64443d01c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 11610798 1250 11609548 11609567
    0xf0609070207050103051306020307020a03090906050a050108040606081204050301060f0605070f0c08070f03060b040c020303060607020301180302030c071401020705060c01090606090506030c010c050304060c03050403060f02030105040b041b 105
    0x901c5c591151141f40001e616000a40c4188078a6010b080522403502d0b000c1d0101c0c800ea084105258100002849151140e04d031660440d0000d00e40b00180d0b80b03941c10440001e20340ca0300000014081c0b00c4019003010789c06c2004104440e01500204100b565402c41188244114003800000610070445580801c2804814070b680c940210200f0310034568801c00d4a150200c0b03070f800351110300410142081409000e00ca200608003058405000481c0014402503c904c4000c208034403e2001003202c40c2951000d51004a0440c0c81c001070400c801054100a541c0343c03c443e85050082c071407207501088903200400c0d402d1f04c005041c4c000709111400d000400c805074201c02d95129080d07584c0c014102c00b0030790742d000f51401403c4449001480b1300702103003030608010401d03070301c075060200340104107000070380000031201107403460703c2c2480b0907076120700e02254203115542c4054003183c00c01c15888401c03003460b4000c1d412140100c41c20070619040c0b41c180405e44003000d6000f010700107600c0301c1d4042d1a0060308410b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 11612048 1250 11610798 11610811
    0x1b0e030607050a05211504021c0e07080618010605011706100509061305030705060f030f0402011e0206010e060d02030a110109050402070609060c030605030307030c0614010602060f060907020705010305 88
    0x90401c0000310f217140b00c0441000f20448250031100a005040140c1c40030b80d42c04520640e0f040d40b030040e80b03000c00e4483d80030b01000303502c0d84d031782d10b8407200140c2405001c01009004c0311803c1c6e825030704280d04001442e80003240c421020b5441c0140c0060f5960203410490719454042d00c4101c0d007651078800700003501c0441d00480c02070000411183c42d19544200040c604000368004400c0740c2402c010504d4913002e05500401d010b01070402640b24180103a005136a446212443c01d40810b9569100480d0540c088581402008502c2c02d103c0205580101e400c034180c0340c2240c0501c1007503454408015140c2445103019406401c1700044a02040c085400c0a202d0b03841818043c508a550b10049000c0380d03c0842c0075030b4490743d1020b00c0401c001140c0114540c503055481c041c4002c84c18000000d03241d215044e8024103012400e42144104200d03074000100c083c003803080041030356039107410107910f54078201d13003210f044107000e00050b140d03140074100c0b580030f490303103a00400103542010015030007044041d01c803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 11613298 1250 11612048 11612057
    0xb0304020a03020901030807060c030605010504030f06020705011e1109060a0e0409020306071101051005011403070309060912020d020604080409091106070813090c05030403030b041404061b0e030607050a 89
    0x110150300e134024440d00940c411211156507411a040403800c43e8044c4440c40f00f09410580c1c20000b036a804004c2d10142c0c0e800601248904100c0c0c0383c4840240f190a030018015409c5c5505507450303c1200ca2000b0b0761801e809000d110300c1409416203d002e220744201d05900a0041c8041c0039280d02c118070340392004201500c0041d26000f5074002a1500104a45400024002c0380200c400302c0d00c00c2c0980d039001f041c9500d415117000d040c0030000c1c0101894002c075895611001c0001401705100c3c0d08071204039900a0070402c56010781d400c11141d0010390080c1d41015104001710907105a00c00100300b4482c40d00402c2c590f08060500c000d0744040d0000b6003007650100900020940c0984c2c9000041807001c0c442c5c205a541c80c0c20f08680d0039145000360f40203200e6580341103008410b041d00003045950250b494500015180c0c1c06100090061111000c003805694003c02000100540b991000c41800d41703500031354000c51984078048030104041d2140903090340091004c00c01c4503004034090400030025050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 11614548 1250 11613298 11613319
    0x906040b180301110a02010606081005010305091501060909060e06090114030102040306150509060d050604031407063602030a0803060315070e090112050303160504120503030f06040b01090b030402 86
    0xf0300f501d151408481c91482c0c00555401e02540910454000301114109402caa20b800010480e42074820310030241410f0311500096401b6805000d084144a52000e140c5525612988000d00409041c001c1d1908145130850100303004580c4507100344205d03030090a0030001da0801121000301c00d02280c00941664080c071022000407040e00445451580c0d21035035041d054034107401c10848080291140d8012000b1b004840007050b00030550552182d010709000c5442548000d440da8144034040f00a00007034584460058030794040c40040503000195075050714001c000c9152100f46d400d0f913000080d4503a11540306480081c45000c06568803c0340202a41d0318502107814903003903071200312890380000310b0382c4e28103900901d0b010700707181d0141035050b201c2d4850380340301d688550b980e100103062556280314503148901d0b440c2c0305100301d0b000b070038140d6a503035000104e0b4a00b0f2960703500141c0300700980e00b52400004500d81480d22034410ba5580595900f031101d840d00d03101425540c000f0348103a070010030703110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 11615798 1250 11614548 11614597
    0x20105090604090f060e010b0706020c0a0c0803030a0605060309031804020d0e030c190f0201081f060306080c03010b09071209051911030609070b0a02030c1002040807060201020906040b 81
    0x81c040e1004008604010407408900b12081d01282e00c26000309840e100244011f1082c1c4c3c400b00705461405902a00059803606240c0240e40380942505000b090101900304c04512a1030120185002d80c980400c1803080035100c9007040041d0004513200301c0194003e0041c401ca1240410010500640240c40146071052881e03140e400d841984198280340c3c0d000045003003e007a000c0240b402903402000340c0f100010203598405000f06134000c4040e0420426a0108091000c174140034070322484d144044443c43c56032810b018019004070312481c01c5601a120f04000765050600030351003400001007c0d111990b5482201362046260b2509018496a94244000c00510f08024103c01d00c2d110001052030320400d8a0400201161403e00d42e0103a0001d400f84086044006010700079911104840398542091680880c0346000d103560440b03680c0f080c0d042c1c2c0d10300c065540c0d0007031080d94004401c0d00c41058071900d05900740d104540c515904103030204402c108125045018011000c10083e041c0c10a40c1040d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 11617048 1250 11615798 11615809
    0x50f0f03010906030b010f0b03160e0405151005040e0a02030702070b0c010203061309020901030b06040b06031303020601050102030304030516060207050a0308070e040606090b0c0a0b0103030207030c06080603030a0c02010509 98
    0x903040000c40c0e0383d03145000d20900003000d0301503004042d200d403000506414100c0c00700360750001420700100c2c02c559002a071821405242d1100500d24080e00c1040b41d0314248807130b0213100005406c018044e0070000c0c1b82442191080c01180c081c1e40703000c1002c600325101e001c403480003544000e22800841c0990040851840c160340020200100104000758036402e0420030020515072801801c0d10a51138032402d9001a11003031826811250400001c100599450000c50050a81066001d80c132650020402c00034509024245e1a998000d50849040b6030300c4000680e03883c4400e48001d000f00e80e040c04801c0c01354000380d10140440d44260405420320307100d0341d550b84c90302503124011404a20380004000c06a0303444101c1c450b0f000c1c001c5400b404141c0c5450006030901030140100c1486660000d00d135105040100008840343d0740c0b01104103242d41e500d003002501c851035800203d4001d43d5681c800500107125140042c09000001c01840c5024401003080e0303000e409074002241800380500c00540503641d070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 11618298 1250 11617048 11617051
    0xe07030b010603060501030c021905011104030501060f120f060b01020a080315130204181107080c06150604060806061b06070201020c0f030a020303060105030a06090906020a08090f060601050f0f03 86
    0x8904003400c6505081c0c01800f501c129800a03410949800450b107107580e80003c542117100c1180100001044444c207115002d00505541c0c0101311100003400820000150702400840717031022030800995440f40d54503005d0f418000000340c007200c0540c1c0030001140e0180c0c01150340520500480300b02d45415914801d40740c00484002d160b401c2c04854100039070405c5403144000c81c0821804514180c02d0800d0856805411702c201c4034415030320b80e60b07030004041e40e4003154500344d00280c8a42c0c403045201d04880e80c0e03990440790807a80c502e03aa503100740c0c0c07401c0c8141590151076842c0c0380c00c007ca07a5818144040c0c1d0b04201e521031004a280e43d00c0c14441001803150500800c000d0740007690716070004200500d0b120040090300016441040000304403a401320075a40c010b03409207049980d944504030700401504041c0c01c9100b41915041502c0100042d6500801c05070703880791201c8074241d461940380703501c0d208048c000c84410b8003c40c0005030356611034001012030070074079150b01c0d08014501d0a8035805400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 11619548 1250 11618298 11618303
    0xf1009030b0c0301050103050702070b0a1b02040207210905060915070605101a0c03090f030f03030702060103030305130210030506040f091203140108030a030c09031b03020f04020a020606060304060e0703 89
    0x80180146e50781409001da12210500040101e42d02d402c0c90070142c3e202c2d071070808040000100c80109000101d01030a401c00b60020401e54861f0528140000440100166020f14580340d83c2070010050041181e00700f1280c00503c0300b03040601038018800e401a44492141001e0020800a80003510750f202e21030003010703d01703010100c0c0741c180a0100920140044156040707401840300a10140001080350400d540995148061000ca800032078a40309a00101d41e00501000c001c1240103540010664101da000340e0b014486501d807540384800c69410084040c2d000342012020700c00050180e0811034102d20060300c0001d04018503070008046424142003212a030700708090804149504d805044170140003102c84e44815498030000e199030340b003020000020715446108403d2103e0003108148021604050507802d00e140711741e00d800303a080444c04203c2c4507081c4280c0903038403414148241c41c912007240e0018141c40d01c1c1c540030001d4070740000300111b80c2141c03241003802941c2002e03c407a00c021031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 11620798 1250 11619548 11619571
    0x605040b06011b020603160903050a0605070207050a06020a02040b0609030d02010605090619030f0510050109050601120203100b03090a050d0203071103060609010e1504020a11010e0c0f1009030b 85
    0x1480c000040c40d00b5120000f038400384115040120140c3d4441003240e4102c1c201e604003148840b9000c0003a601d86403580d001406a00440c1425018088250000c078415185c5034284d502054881c41000f200f444140161401640506806001400c007031340f0010500800810040c00c1001c048002840d11241e56103410040c3d460304001c0000d07042c21961140c01210071241c00d444909020806004590607200203003000c0710000e9140144902407001c2d4030703803094080003400a90b0b140c16140c0003030300d001d4074582c4c0003840c5080d8404903001c6c00d00c00e5070f02030207004100d404580c1c900300700791300645c0015029078118004c1c0030b00ba0001400c100708801e5051141c2d0040c586600681c24005100c0f8000c980c014001c1d0815000c006456a0341d100c40c0d41504c400c040f00c2901c0ea00c8043e8a10510103d400c03c90340c01130720010f81c2c030303101a8108110310b03a0004840000c1c80f044000201d00c94451500c0079942e6007210540801d031100b840c2ca45903e04044045280452101ea982e440da2014140c00382c0b404040b91 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 11622048 1250 11620798 11620801
    0xd02090102010e0f0d0311030610080a180f020f040504051903090b030709030c0b03130f0302011401060203090a080c0604030204090f0f030c060507050a020604022808030301090b030d020709180605040b 88
    0x2907014081c4070b41c08000221004c1c29889c258000c04c0d808074118001204104c440b00015010001d9681300c5100c030401509401c1e101c900038500310004038180202a03100b20014064589030b403801e406201d00c80c035441005000704004132010f42d00800d11065085080c0111002e01142542c100400b451148942c3d5691005291039814000707071591864201011141c8104104080e241c039110301d5851165002e40022191422401e080780102154100c0d901005070000c00061080d0307000018007000d2030200c401e0700b10b45550300d035030555400103003845036000001440108050b14050380700c041b1440c01404c1d01e4810380f40513a60480100d000c64400c40108242c3ea050f8400d003c07240c460240d114050742031151400760781c070001960f1503a00030402413156082c520345d0007880058442c2062420307031301900b103180140c4501140c1d480b07820234080c4400075442d01c1900140d07450b0008142d403100b1015009040c00c01c1c02c1420340c0000c2c15400d005410442c11300c240700c0e00001d4803480b40300c3c40b5900503814021079 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 11623298 1250 11622048 11622073
    0x4080f01050604060803040602250503060708040201030f0c0c1401110d02040303090f03030518040e01020c010e0d080606030a05040c0b0a0c03090f140d020d0f030507060c02030f0d02090102010e0f 86
    0x1c98000350003000c482d070710501040c0230290300000d8500a80250310b0240302404002d4140b01c0080841d40c0003241c15000307160038850001c0d000812030340914400d032814880c806030f03c0c2d101700445800500a00000c0e581c0411007002c01c545068040110b2001000401c03000b04c051442400745d8041600340d170300039600040c204103241c0d1106070400542103401428020604d5900d00074194020750108a03506400844044010b6403141d204a2000039440d0095440b2680783d6a00760017041c089086102c6030180c01440c85809101e514054868403005140ba03085481c4c10001200401000f0b2007100c010380101c5004c40c0d00c5503000c1c00f070301c561005541c418041c0340b41494003c0910300c290740040040b4100c1c40781842010620700d802121800260340b0101ca00d86a800081c24a420104020300700c40c484890550a0550050007001c41c1c900070f80043c40780d0802c001003281c0d203204d41034070150103075014000c042500c0041c0c3c00802007850140b00110b0b10905850b80f49091079900c00640e03150b03600c2111070108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 11624548 1250 11623298 11623301
    0xa0209011217040b04090506040615030209040506030a050d08070507201002010e03030601030c0302090604030f020306010e09060c0901020a050601060207090f050103020607030503060d0b0c120c0304030215070504080f01050604 99
    0x401000d0b4031107140c02e05150014035040b5010750f001c1d480d4000d4603100011103940311640030b44010402d0a010a02c0848042c9014009601c94140750b40554203003000124507090000e040c034055a4040b0003440348400846007101d40c0400a03180e0403c10004020103404100440d9255450801c0e8100700c0070b05c1d2106808010705000c00401c01015079051108489070350402200b600c2d489a02070a0108807465902c004034001d11800b07a1041d0312500c00300d800300510001150034004144207404a445590300ca220002179103108948540c640c1d8445400034000f215040098140600180100d031703444440b42c1d507841e04215090304200300581c401e00c0100710a880d0741c0035107150300d0301002c0100304039411071300450040d00c50f211000c0c3c00e00800201052080c0c480e1480b2104158003c0b0717074209241014400d1120f00ea00062020107031401203008a8844103402085a0045606400070b01c40034041d19404400000b00030308400500c8024000010161014807001c3c00340b0080500000317081c03602404000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 11625798 1250 11624548 11624573
    0xb010e03010e06010611240612030313020607080409050a0f1b0504090207031103030403030e120301060c020d02010e04090b0a051006050f0f040312021507180603020c0a02090112 78
    0x14401c0e030400e0310001c00c1c1000490300605485652800c402c440c0b400c0c0c004189440806a00002200d40b1070b000f203048505a0076105d0300446048030392541529801c0061507036800b003500da0256040640c00c4510040c9803060080403003a03c101c80302e0b41059990044082201c0049030b07820340203900d40348441540741e1540700d4509030303c0d94500707800707000640040018400d014030b00401c0742c03a41d0b00240b10390905009880d4410308881032401c4950307270305d0280b400501421105148203d2031080307000030101940e0007404e6a062320204d0f544d0f102c80c10300c0b54081100c00d0441001c01d9040c0304c41100703d0380e460385039405286c2100d4001d001e10662414148040c0c0e086402c02844005003107054241400402d80c41005c4030b00c5240100d0b9000d0301c8080c080e107450354606c110381c00101000007800f404611140c001c20390888843c149601c0c181079545030300d025210710401c1d14608080210140741071114078001d03405040c4082460080703d01d4902940c0c081611440280c0108190401d0701c0b140d207040055146071038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 11627048 1250 11625798 11625827
    0xb0708150402040f031104020d0912020d0e06030604020d0b0418210203030c03040501060b030f15010306030804050105160b01080a050d020c031509030c01091b0803071a07110703060b01 81
    0x2180383ca8900f9045486440180c04003c2c0f186508620b400d405680c1c03030f01030714011500e0358010860540e8603d0300005440440b02c0c4a4050700074649858005400303007850703000021000d400940395549203c10040254000b8000700700b00b0f03903104040c0c031042d262486180682e003c0d800c0500218205810018108055a040219130300006036078844a47d9002c400c0d01d400005142569840303441c2c5107080c078054800c6400880e500380c0c0100c100001070004142103402288045010031100315485c2c01101070f995940009004041c0800003008554442c400601c0360400000056800c222030795144889910f085c0d105903800e0b03200c80130480c00e2080034130035440005000d000800c00508800040b980342c102001c03031005000c4403140042c0d0703012014001c9544642c1802c000b008200e120349014800541e60110a14010090400100c0d40e40400011102401d03003218009014a07600f030041404080d00800200402080e01c040c0c0714907000411a00c005180b05100101d2202980c5000400800c64440c40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 11628298 1250 11627048 11627051
    0x10e0102090109090515090415050901050f13020307030308090c0d080904050105030a0f060f061e060e010c050319020111040602070e100e0609090c03070801060e07030203010f0b03060406030b07081504 88
    0x5100d1b032001206d005400c103034401c3e5449407803079a480c00c0982c45204044210028541410100100c614041d404203119204000d0000f5140c0c035641c0140c40403440b40100207405074001c817010700101e400303042c00c42d5004c06e68801701d03200080d1520114500000020b802c691007040071403000c0003494103000d55405444143d00410307031f0036202d4070b400d160500c180c200036284964501c101c405886135a000440585004a0064900008104000c0c4482070f82c2c0300c0d17500026208003103402c4662003424560380d0356400100560400030003d1552a500c2c0e0541c076400300f559030303c0ca00b44130f941841001601c020301081d0043d040003481e0002402a444005110502e40c0200c00001d201c08609014601d8000b4426038450b034603a9134101c0071380d203800004214154940b141040000f1480d805410090941c0d00d031110825131500d038404150146e020a0180c040d8104100c0400d0011041c0b01014690085009201060095407501d8842105d0000c1d204a000100103004000c920980301c1c1c92128483e2080e80c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 11629548 1250 11628298 11628301
    0x303020604060b0307092d14010311010203040b160209060105090102031c060302031c02010f05040c03060c0c171c0902061e0d0614040e07050906060d020f0f040611030405010e011b05010e01020901090905 89
    0x5061802e02301400020980b84800805a110780d10800c160f078003a068643d000d580d260b240041e482103200c441c000c100d104100b440300003915540725106a8828a0701a0001c50801002659655506404e10150741e0702541c3c5d1003001015036010400444071500b00c0300500503043c102d04000307013560308880d401c40100d401c01061000040f4088090000c59402420010789142485c0c0d0440304100344104c040c0030a103480c01070035950518000101003404942c00b400301c03098000c8010105641172203070041d622440a10081d2020b01000c0c481c80c011841801c00300d45090f61000b800e4049030140d4110a502c20b840c254880103500740341c465030a00300201402401e00c1171404d00000c2e03400318014403280c0908000715804e000c060158064400340b02d500300fa46612180301d402001061741107886002d0028840c60741d42d03045d080000c02200c09545040c0d40d0850000800801581c9561190111110031302d0803c58110108000307210b0020b05682e070000240e0707100f6101000400149607a000344405514200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 11630798 1250 11629548 11629571
    0x9060206090705012604081305033c01020307030f11030402030601060f020a0f0f0302072102060a210b0906010f020c04090303060302090c030703050a02040303020604060b0307092d 79
    0x142c09000c070f90003480e040c00d8203000590b1503010848003003100441414880b06001c20085408042e0042c82c1e000c03e904680341c0d564008056803030785c8040e0b040035001180c201d040e101041e440450b0364072080c0b80740364505580c0c0c010201400ca80c001c480c4c2c5030000340d0715144e200121310b241c0115190100c2e01d049031411402d040d00020380740e03507040c424081403041034010903510714001e00c01c1f5140c1680140703201c0c031645104d0400203a11010030608900501070080046210384070f42c51500650800c00040254144c41c03907082c030809031f015400700010704c071403011a074214114801c1c08204045c40d490000c1245194202401800c10002d001181440784a40d008404ad584c0014048a201e400300d82c0840c1c00d40560900380c004044e1a04043c1d000038035002044078111100000f1402040140e6041003a030340c441c00c42c8000ca001c0c0d4000100143c1080d404100402d00c66001500b1246005040e20241951506110100c0d510b0828000d4914086070010140101034040c204685000c104240003c0c100c50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 11632048 1250 11630798 11630803
    0x405010e01031509050715080a060b0c0a030503060a03060e01092102030702040b0f06070309060e01090308090919020a02010b090a060515030a021c0b0415080c150c0d03020a0906020609 81
    0xc0c5410003d0707034602d9414140003017041480c0040c8000d200482110080850007056024200c4425030400e04000001600c1703000391040342c5005126070043c199240d0745550446841e0b0000c0c182540c440341142022000c510540714004140403181c00000b0201160700d010000041d41c0781034208150000b1841d0041141c0200132103613400c2e411030340020640c04650001e0800d20781d09999940040340400c99004040e002032100040c0ca0382d644501841c03c03910780044642c10200d01000345410300c2408030032003508002002580103c289941c2c04600c0203400c08613000c82c2c0103044100c005030f44503803c10205003802d40202c2d40010955400b40701050a0201144568801000d100300074400040094081c0a00c3da06840c4046242140003c00514100101d0050401200b220348202d00c1d2a810b106c0e4200c2095110301211051800b604840341c90404000e081540a0501c45030b03c4010488070b20010002d01c0b800f0052800c0e03403801a160840450000d1004800e9040002550700042c188841031900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 11633298 1250 11632048 11632073
    0x110c040b060415030e010203040f0506011a0403030503070c0f051c05091806120d020c01090504090b0115020102040b0706150b03070207030206030c09121c050414121c0801050405010e0103 82
    0x1003c00a04602e11212000c40c018411541c8071050781d4070101c01e1104010104440d55105030240b401c482c05030b42c03940601000144800c2105030050001c00c000c00c0000c4c0200e0155600050f40d0600000c0d18280f82c4812480f070081c02400c942e55041050a804004504400300700414118504175050801480c00b00e901c1d50101c0e9202d44408000f5800600243d94002400480392601000e888542180a00195460701c024520501042c0c0003040803615051503c60031400c070307030130020b40181d691820320b0104681c0100c50940c411035408003c0420320f9821a4000d01480f4400c10002a00f241c4558a00007408816044172441000070418040010780c0003681500741c0350110380320390b0360b6100c0190200640c42a8031220f6080311021162071040800070601c101c000c0345450798110f1010907000126190310843c01007403464900415071100504010f04940c0415882e43d08681503c00b464400b0784000740d01007100307000110901e00501c0a400e1030f0060307500404140720110311035410f50340c032205074021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 11634548 1250 11633298 11633309
    0x7140102030906071e0602040806070512040f050712080c060c04030305040e06011209060f141e0901060e0c0406140306181308040b07030306050a060507031206050907110c040b0604 79
    0x80100b003200912004003028480141c281c504d40208054031b14100d80650464481c6800034010880014000e80c01076089460444000c0850241503942d5a1984224004942c00780c980d40b050010100300000e000403028202c3d806110182c6e1134440401d4820301d440c0b00100203064500c0248001c0001a410600b074405035084c2444480c1c031a504c000c01210420036021900b51031a0820303801000340030859000d00e007450102a014444181c22110100162005076000014a68007840441d100c402101c801d54001c1c082000120341785664507181c68a605080d070b45040303800c0d80010200700080e0000e01d200381d0030a000402a04500d02a000210741140f000c0b070a0307009200040c000b50b424103c0001004400d9480a005038617940c0f5801c40910a030446503013240070030701c1c0c50b0f00440c3d1858200820740803114690b4030f40d40760611903070702207420760102c08001a01d039480e21400705041d5070355140c6c54441d08490396489824034554000b0f80c908071b2041800341c00399117003c90b02c0100351140310840d4107481 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 11635798 1250 11634548 11634559
    0x9091a180a0f020a0503010303030b040b060906090d121806020106031e02030f070303052205060703180906060807121e021b010203100305070f06020307030c0204110705070305071401020309 83
    0x5540100003006040b1040350004441e10008a9410841d0030030040c506032806a0780801c2100d0303980050204035280c01074410340c002c01c01d2140b9100c0745031085c000c00798410040c01c0b10405503150395079005005041d2802ca004601c4880241c145890a240040300030060340c8028030402d884c40d1903010344804400b07080003c54401d145080155101001700d40082140310045036030041d40c9003001003042c1c01c6502c0000c84a1607c01151100303610f00808102a1200204403e2030034506950588101580c400000a09030002c8030004519071544520401040c0580780d4404a00d010310000b800b081c1c031029105245440d080280000140303007900d0040080b03107440c0051f51000b203098040c00107907070307070000359450b6000104002505400c408010112440b50b01107458582c1c0f252050b07003121125004100041c1e00c1440948042842550b110900c14005000000c1031701003164154201e03800007100391404d510040c3c0030001c0040030428a00140407000500c00460102d0000039281d210701100b41c2e1042 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 11637048 1250 11635798 11635801
    0x516051e090306160306050103090203060105090a09050a060f150311010809070b0a0e030d020c0102060a0504230d020d0e0607060f020c07150905090103111002071509091a18 76
    0x100d0400100d8081510080441d1424601004010444030a4a44000001c1d080c0302c40000d55501134007601c8000c0c0d03401070151505130300304800e114040000800ca0721030240c03160003040105a092000c1c0103490300811021824910b00209081500c090000d680042203000204002061048105c0700e020282442c1000c030b80c0e00c61490040c41c102d0076400601006500051010b03040b900807024507000c2c1025000e541502030054003c0c4e07112850300d01a01d01513001040011114405907203d01da02a00c00e401c0070140281c0704910030020f441c14480c0001c0703644052a004e5640d5010409040c4940c075500d011109003400402013000d5000d87e02e00146126162002c8080d00001034058510004840c01218001941c0d1514480c58401c005800808220190800b0580303080c042c01c694180c0350401500074020b140302d0180708005040d55007038421401a03010214540320032880004502e0720380c1d03885509080c1400309200450b521201918504006105000305039100c212144544083c0c0510941c071030b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 11638298 1250 11637048 11637097
    0x11e0509090f01020301080f07091515050d0609020d0510050a05010c03030905010c050a080106080124111002041409190c02190507060306050306060d020f0103060306051504051605 79
    0x70503200d2000c0c0c0c00c883d400400042001440002ea410849031000111b6603802e0351405a01c0440d2520340841c10101c50303421050184031003010000401d060185041850059421141421290b464212808107034001a0602c03020030a0b00034540c009450036005100c40c0d1811000422100d0b06210b03041c1401400415241458005d41c4100c0c03ca64000c8000c0c0508004285c00030b0540d4049007208010400c500c1c00401c141c0e1058401906a44007050f0009800590381721004d03030f62291301122400c010601a8465050b00c0c1030002400500003507901585642c00d02c01c18246000e500350040703000d820100104100038001c03103c1400d040326901d40c0003805a8040100f2800d0110650300098612800004070081120005618040703800c0f90380c0411106843d0001c2588604041d84c1032076100d4040000c0b03001601c0c1c2024080c1d603410050400050255480d40c0d00411340d60100c9080b4620308501c480003001d0308150058951080020840741211601940060528094600100703e031200080c05060b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 11639548 1250 11638298 11638303
    0x20d0b1c020906040212011202150406020c090402120f100612020a030b0a021303030806040b04050106020a0605180d021b06040506040e0603010b060705060402040e0304050102070b03131b0608011e050909 89
    0x70321180e10350035a031b00d5070b1074850f03c2d1070824100f1801c130f01980a400c401e0120003846000e6900b5901d03154060104508640c3c03c20402c400050701c00d81c0e001d604a20340d50b0204901308040d20b420007006c0090055066180c104404032207056000c1d201c0c00303c68001040042c0d44d05842001a00c0e8040078a8046450f40c102c2c4000901400780540008400e406010081c190459440f03481903000f2a020301c51881c4010603c0241c0f802031054801680c028040103000070f00b00c0c4c001c5540400030340d08072450b20b9601c12806213400f00d604426005a00010102c6682e4407951031283d420030307010313181d29103818a864040b40461049100710b11040307403110f011030020341d001c4d000914a44001482c9507141e501071305100351500c0b001c0c1d4040340b055150288080701d481000c82506e080f140160040c2003085d00e0700040880079030004005032019060395141c0e80004440d00210b44110540d0302d60416820b00b45107001d0001401030b00b0403048039000484d030070800358075074a04100b40c84081c1c540008a840d5921440c0c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 11640798 1250 11639548 11639557
    0x80d050f0c0f1005010f060e0d0203010e1204060801090509031b1c090815090615180a02040e07081b0a0c21020c09060a030212030d060603020d0b1c0209060402 70
    0xa1090040c02d200c54251940001c4102c00545861001c002990780c5c0d42c0c1440c4c80c038410348102c0002c07801003500c10825190801211000d50b0000c0c00108200481c44074041c20841c2c5156081a0412f0108003800343c02d40c0100028054110010f0400941c2403909482e41e0320300440c2c9501e001103400200342c00300601c0c1407100000c806842108850360511101028244501c01e000301c40b85d610401d410501410041050325010b0800000608881e40b9118110f010000222690f1500300c5030710070542c04540902c0301d40a20a110021005171500d061161a0001c0003003e0074841c00c01164600340100344103881c48101343c00101901056079211415019500074288400c0944410303030780340300100f22030803803c6443c1c2001040d07400e07140340c480301504106c000b00c41070307a080b900300704d5100301440107050415206100600010440c0d0400f00c91200c0081900c06980000300080d0b0045041101440c4a005000f04404129508000704070050000392142506d00c40107441000d02c000412040d803035560464 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 11642048 1250 11640798 11640817
    0x906040803040b041805040309090209030102040b0d020c0d0c03080705031509040c050a090c0813020a05090a02120c0720010905040903050c07090603020619020c04060e0402030610080d050f 83
    0x80740c0b00d40c2c0e603240b424142e400c00c0c8155081030f51000c201d13003140c540504c203e900c1070f503060700e034507a850b0308251000000b50801d0f450709815660030080403405108420243c01c8084040101590314085150007605101e0000308001c00d0040c0c030342c0e070000040d03000b0340300b194080710303030315249403255203007280341c401d640c0c10055a0350001e01003810301051064030780c2060b0680c0d406480342c8d11415a40d11581c1c04407500c500e8010000b40301c4101046030000104088080a800102490035050b182d41c00508404026543d2807015640041c4000a402e418021507074413084204801e07003000b11580344c1207002403030b48124116a2034030410401322a80a0961314014040c003400406c00c11031140b40282c150b90110032198400c4c42420f00005850f02d10b8002c04080d6540a02068100744a0340d410300316000c03081039000207501a000c2452115122849420001d003103070f4039480c1d030310f090500601d030900c88050040700035503081c400240503100c0c0c0041e5940220149152155031001d04cad10080f2464081c00019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 11643298 1250 11642048 11642053
    0x20102090405010315050c04180e0c030303011829010507020301150807060311040f05090c0708120402040b041104060c03110d0207051005090d060902060d06030c08010c05041a09060408 81
    0x40305008500d1032440d00300031742e040e0400441e00c41001c000d05500880c411148070840c41044d00042070401e40100d61203060840849900c5d43c1000002400c2d43c20907000380318500c055141d5140c14003003074041d01c1c4108401000d03061010840040680c004004020b5007414072000184110071514258020700c044e07a030361994035004980301c0c000303503403a801607104031030000f400c02d104a500744900038122412105070a00c000a194a450f00780424281d0007401c1d88040d240174003220300440d0128009045c00c01c60800c60043e1850240704201c12a1140c034a010302542c501600040903001c188215410b03501107080001b100340b000d14007200d40c0e1b2034610b6900710701c2c0600803c0e01115500000d002c015140c0465071402c2a165502080354140030706540d00394014103883c11400454601c1e480b0b00c003094005400d051404510091904c00c0e11041c3e80100d44c180340600c0204aa500280704a103130410452601614013443c0403648820b8101030300708400d080c540054101c4159072020202c40042c0408401d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 11644548 1250 11643298 11643301
    0xc070609030806011107080a1b12060b0405010b0313062f0703030b010c030206010603050a09020d0b04030906030608060a0b030a0b0a0c08010f0605030a0504020105040f0e1009050c040b0703020102090405 89
    0x1c0040020304140c401c6408203140c426000c0a4480204460081e10305a500401d82c07860261650315140415840c00031200a11b52004103101021a210903c4140205008103a0320100740a1104503a8142e200d443c070707424180b051089424904030f15072050f030b800c0b006c00305151031950f80b180c2c00014141c3e0350078503200703000b54208aa02e010202814095010391400c02211800c03c0c011754056000d041c2c01001a0061701c0103115860180d8810340e04040e05082c00660400c60380c0c0070800401a0400c19500c48160b032042104155201f00080090400c5160502c00549400d01080e615a40a050442c1c001c1d01c0740744400e09514100301c10009035800c800300c00007604103102c1307900040181d2040000002c06140000c9041440c01c1d940f0811214070782e41d01e034503568410480b1402008040d0049041250401c0000342c600d1240380b01d01c5c05042025200710740c07030801103036085c50910658000300065080030200080012481d0039242151801a0500d03690f905614080780240700d240c0d405c0d94841d15000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 11645798 1250 11644548 11644553
    0xb060d1802040506040209010f081e09030c06060f03031608090612010306050105060a05220b0307020d11010902010804200301050c0306010e010201151202040204030507120507091b080c070609 84
    0x81180366114029601001aa2544400d0100382e228601c9000c2c0829210340220840c00d104161083c0c1c0502e800c50600c80c5036440942c0710050304025505d00072240e06c04200090010000d0211030b4001c4001c6440000b0300c0207002c0885d40328005c8100714210740c0a030346200001d002c0e03102c0483d60282402803090b69100c0d006080041c84050030300094440e145090004100303800e02c002183d0814109407100b030705050540c1403001c1110f900b080c12124032030001000007964010013014501a000c250080c00a07040d071b548004144041c2d5000f000500c0e8104a90100542d0708000b40c0c50700150060001c41a440d40c242c00c0d00086001c012203540c0642ca404200688459104055070050100340d0311900b00c403150310012803da42c8403501c102c001115051081014420910a2860301d0780b0150000d82040d036030f51242c60030305400c0da000403481460700c100a0104070051100c40d000c0d0281003000c019001000b54620114400c144280040c00801d20110301500d940c0b50680328203992004041c00050886c1c0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 11647048 1250 11645798 11645831
    0x20c060705010e060703020f03040609020609090403050307030b0d120503090f0a0b04030905010e0a09020a0c140d020601120b0c03060a09020a020a060b0d030203030402150c1509060f090c01030b060d 87
    0x12990741c0c01138040c1001084a0510038000c6459003401500d4aa095448940f5084002c01112204a910203020000c2d0b00c55511400181c6210f20b01a0b1503154403490201d00144c00e0318410180316206603468007102c3c00041c5411444c481c220490324146071250749002500e403401605a031100d6841c4188d0307095030104426504501c0c4518441ea0391001c1c895030f520019030351940800d048a41c40b42864405004d20b01d680c0d0f028203c940b81c18030301041d000c4d00b82d44a010189030109801c00594128600e51030001d80c040001600520440d42c040e4244a0380341c031f9800322040085e10f00710003002c002000c241165640302c0b50070090042124119556419080043d6136040040002c84d045810000c0d100303982d00e48000c1c9000c2040c1c15801451a5079110f50802290160700b043c419158502400282d01c1010204103c0c40340080c2e200040b895401c24031a081c0c40c0407030050411942e40d14450400c01408008950008200802e00303010412801d0103002441038000e98054070b0906103807880010440111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 11648298 1250 11647048 11647061
    0x10204060e0405010302010e040504030e0d050a0b010e06030a06090309051302030a05150d02011202040b1306110c010f11070b030903070201030b03030408060415020403050109030c050d08190c020c06070501 90
    0x1541c0360a031040041405000c1035403c00d10000c1c1c0815401400c0c907130700b0b0405401c09940244240340002d6894084000252006d640340810742d1940c0c85400a5020044150003841c09000481c0c02030489290a00009a8500d07050b200180115119a05401050302484011010303080007412140c4040801400b035000b50411204000d0039401e050226800b451010080d408443d800350078484110460707001074880703039110b4000c9104c1503804c100010384000220003905070b00003000718858103140f904800074001c81c413183c50207506410000300f2100b170740e81144030984c051f040e5040034086482030300c00e01401c2032070583c441c15038041c0000810140d030001000502026200b46c074100882040c0030240360381c9004500580b005a03000001140114940c200d045449081070500035141540369038915082d1000b40c0c1c42100400c6001c03001c0300401c0801d1004030342e0720f44503207030042d11403924800e1204480004c3c00c80100003691800c84415a030320a114214054102400301039a8034124a440780c0204075 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 11649548 1250 11648298 11648309
    0x50105070c060b09090601090b13060605030610050f0703030c03150e100603090506060d05031c05040b010b07022808120a022416120f0504020906010c02060706180203030c010204 78
    0x10344141083c00d8138001c0803040c0180101c1c40117141982c2024103c3e402003100e8280d40760f2001540070100c4070541300b40582d0000d49a196a040d8803410800b052040c1007840c00302c40424070005000900b030714001030702500c4907a50586030104000101a10070b50040c40c60045112031540300c008045225101201d805000e103000441c1841d2095031070408508440107203030020610b40000010604500c0c0040000c01c4035800b850980e0f107465007204258903205020405c1001560311803041105100000c2c101d98014546015110b02e0404a0b50002d9400801c0140c44c5040e0b440d00100307441141d10305e1541e070016000711022510402e0f03906202c51115003007203a80200600c41c4900c602120103c6000700310b0000401410f502c06c50300d03100000104107402071002d01c10000c00380c2d542403064501c1d018501403048136010009050615006001705d81400034591418070140c0c00b01500140c07203001c01c4904072500240005022200405628805c90001001951503c030100d00c3c03030244034040d4005c000b2140c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 11650798 1250 11649548 11649551
    0x2060309070e1e010e0408040f03050d0e0103020c03030a1d0316020301050610140703030f0203070809070605042105010b0d050d03060906030b0601030e0c030102040902040810090807081303050105070c06 89
    0x1650b000c3c025000345000f000d0707402c101d401400100560041645c49a40040c4900c1250341015202e048404210150750700640d119402414445446a00310000c61080070f001c0c6000d40c0350050195490765a440090706800f4a03581d00e140740026080410715201c51007402c2c10680b40c2d50511107841c00702c0f074926194113900c83c0d40b0f0040030074071038940b0843c03060b240f0000d84c035032842210721000b6040c1c1a1704950303c25801d048d140c3c1c4550700c1c0c0480d0340c4001c501c2484070791101c1d0081e05000b100036150802907005641402400c0100b801103100c00400000d980700640c005c107000c000c8618010f4058002105445d41121032203554200b0000042600c110b010301554080100740e64400c2910140c035602d100240c4003c0407100400c2d01540b00790818207000c880c1400315005003d0401c0800d00b280c0c417590014881d0b50b8080307000e01200e0400d100c5003c02000c0c0400511034105a504d51911512030404c0c010901500000e1482c460340144801000940d0080020062854440e10140103800349440c21501123 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 11652048 1250 11650798 11650801
    0x4090b0901050a05030a080703030e07060c03020f070b0d020a02010b040501060509011205060f040209010e0d0c0515040e01060c020109080303010609090509010c020d030507030e0a050703051504050a0b040c0302060309070e 97
    0x18108143c600c401ca607030080040064058a17142c0e18455480034505808040e140d01d5800340144007000742000071309507643d0f104004241814000e00381184c80502110b1904402c408200141c0070400342c2e000840da10701c0041c0d81e2261000c0a034010085a0106034000c0c0c10b0900010714560008083d000d114020b8039004500819001c01d030045440032100c00f81d200180da90042c1d181e00f030540c0901818901030501304502c450301c000007410340700006022142c1c0448001705000300d0030300300880402d041400d1080d50900741003807004592140c0500650040184c0f000760407003507a00c941403482c000d0013880c003078940d203507141c1a0040a1760883e003e100981810200426601c52051161039801c40481e0301030f00c0705109060044000d410050110030805840307410000144500340401c1041e5032003a001015924514503220b0b08080c080d0344040060b01d6900108000315601041d111040ca502403407592071076950389441c4003100000d80011350004000310400c900000c0002d10308058070302d10440314000c0e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 11653298 1250 11652048 11652059
    0x10b0102120a170601090503010509101109011709070b040807090b01050f090111010e070902070203070905040f0f051e0c090c0319050606040503010e1c0207030b04030806010201090203010204090b0901 88
    0x1248190404000020040200c01c0000e800c0f0344003582c0c20900500d0502a043d540314002400c1d64070649001e0f0154002d820500000200340c851021030000d00344d0302030f04100e85070700083d0511000032140300301d0391f03114000140e009409005540240c0403904003240c8072501c0300c18903035031000c0728080e62211500e0aa11902a513024005070340441c040c036480c0c5841c2ca441c080044030108212400b81e0346079034a400c0301d0180000140001c1d00901400040146c5032183c600406103042c00320740c044000d00d071a107000c3c4404550000202140c158001d600b15803480520701c2d0091402e448040844800011400054070082000c20031040302c070411070b16104907499500002e00140700650324142e5203c000d03040740b001040e064000503804400141682d060a544501090954030404001401604403000e01512002240002c0b40c000340644014000350f400c43c1d80e80802d858020740060240601388000641c00d038400d4010b002c0c210781c050002c0d03482e681d460030800c0c09008640c030a24450b6580b1030004c1803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 11654548 1250 11653298 11653333
    0x10e0703030f0302030c09010c02030f010e0a03030605040606080c030c130303080412080c0301050409020d0503070b0f01060305060d150b10080108010e0c0d0b0405030d0207080306090108030703120b0609040905010b0102 96
    0x82c11070070851890b11147c680150b0350014195022601030203000c2c0c10302c413980000c0c420b180e01e4400d104080c2c0910b07207132460001d088400c66040148980e00e04a001d10480f9407103e0780e2507000001e03104485e0390383ca0744c10b4041e040e80a443c80c010b60b42c3c0c204000104c05c16502003009805184079001080025004610603200510119841c008000043c4010050351404d40c1094680b20300281081e500302e44a611084d0841c1c0c021481503415120900602085030305d8500d0050052000d89820012800c00f040010046454004041d0184815840424082400b80e1188118600003451158821544000509902c0f424890b0000d035529005041c54460404140c08442100041940d041c0e61445d42c4c0703040d01400094020380d610310082c03240380b040326400e200030120a030149002c152640340c80d000700444408160455440e43e08140000e00c00a0b801140f00d012003490000d01041c004c00302008508140569028140c0c010300f050b61400a000042d40400c11440c02a4262008064010150b40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 11655798 1250 11654548 11654551
    0x31e03020702090c030a0603060608030901020c031906020f0f0a031a12120a03110301060908010506011412090c06070f0210020607020607030b040603081207020c1509041d010e0703030f030203 84
    0x350003c95020001c2e02d9040040011503003d10015000600980c891f11400f04850982d00098002e82c4001010704040d038041000c03504404007107000303011841d41884202c0b10440905402804c46801040311091a2030527800c0c2d410103048200c03115200e800118004014004c0610415200703036404052031000d0410410040162412000078845c0c9070040132100034581c843e1000c0403c02d951030740103444051400c4010f40c020b0080c1e550380409541002c450b5030071210b0161195051042c801842010105500c3c25214140c01d002c0401181d60385900d4400c1c18100941810f6900c03440c001450707020009040b4448282a00a40354041107507400c40f010b903624407040d102440035911420005410a1080e0031030744038101d016001050055076540d81200300d03009000c42c1005400c251040202642d810000701e0400746d000c03a03010526080e002d1489640f4071032220081d00031901d450100159500e802101000e03400c1407002040100341d116910f0b0348035051400304900043c600405400303100c2c4a070082c0d9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 11657048 1250 11655798 11655803
    0x70c081209010813140d080106050a09060e030a021314090705061605070308030c030115031a04020d02040e0103080a08280b180103080301050406061404050405070504080a031e030207 80
    0x1540341140000054543d03401c01000041401c1c401d21005001640081d19144101420001807404940c0307850040c150100581018081013004d01814031015400350080080b40c030711b820003220242d000001b10b070401e000024040d40294030b48040080b00d1029038851200c4d1503100184400342d8a0b2450340c10f803180200d10a070b07980041e0601905102092006901c21050b01c5a01203c00455030780d51040480d0700301321150820541701000411083c020038240b40c0001056140030400e145a0302d5032649061403a228090180f0b50110300e0048030411a8112070140c0041c0d0803041c125030b5240340826070f5038002c0c90f04030006024031307002c15100a0001034020002440d5464020004520782117040103082d0600e41950000c406940707000441155080603000e5802500380d2996581040c1c00d200c2510a154040c20030407440382114009083d4110945007651822280441c0c15151201e003101e150255400101c1603014408510013055002607201051b8906040243c0403903494175000da00320300501201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 11658298 1250 11657048 11657083
    0x1a030106030e030409110901110105040c0e0903090406030c0501090b0a090b03060f0d0f0201020d0203070507030b06060403050304061110020721020f030a0206090606030303040c06050d02090d050102070c08 90
    0x6000c018001e81022a418607000101d904060743c41021034203444912030a8901c46500140344412541d0003080a0643c03ca003800038440340c00c103176640c13288900da01c1c4200086688080040b40150300709104640090800030710a001050b240d09203a42030700308a2282501040f4004c00015038a0000c00c290f03030448402da00c41d813048500c0c25003030f03100941c801070400f0703840451200710700300c1583d554030f518810303a00079641e40701c200601d440068540440e421304c540640d4001d1201c6800103a000403100c081c0e0b61f0000c03495205444000111784140517a8000800e240400300700070410581c803203041c1425000e11402c5802500c04540c000040307200340c03100a80007a44c0c1d000c0041441c5008010010031891501c115881813411844580c1583c102c00d1030580143c00440600491200c100461074211000314050b600d03504107580c50001c50300440c400c2c1c40c18048086801c1418803290750648640c4400a002c0a201088524109001b5444104200c403403400c0410045001980000c01507000d41000c0312 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 11659548 1250 11658298 11658301
    0x80a1d0619020409110903060106050313080d06030209040b1006080106050706020a121505030c0f0a05150706020f0c010c0e100c0615030b010303110c1005160506090708071a03 77
    0x220200c9441d10302490314407403a020400000d9907003141c840e43d14101c1c8401c0c1e90640f1888003000f003508207501039100d0001c004d000e100b80034240c8203031800914400c2d44244025900d000f070101000282041d640080d40c4803c40c50f04100c1030100c5124601e10600c80615041080303134941105803039280d0280140c00000d0402e00c149000198a60b0090a80010b6404c0825811500100c02021b8410a07164541c0f81520848100203d003020403c0c040017010464041da0304042484c04500c0500d514400c0510454128130589a801a6802207540c1641c0043d01503585203481e500c0c61005500150002c0c0066103014900c408851107842850b681032802821071034689039a020440c3c2c90944036209607901e513a61442400c0f05031402d600359000f188201440000c640c91803c01615124070492410b460790400c200d40c105594480301c442050010a041090721840514448145c0b041000001805442030740d003489285000002d09074100c4403a42c040315044c0d1f0302e80355080d039110094404840e61f01c00620 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 11660798 1250 11659548 11659561
    0x201091203020d08090102090901030302160504020304020d020d0309170303010f080f0a0615051e030111030103080307030504060b091e01050409080306090c0c060a0501050f040603020904021003020c0d080a1d06 92
    0x44e0064001c501c540015041c400d0803070010341402400c2c5d0003140984d2065164611074070b005020035000f841c0841c2c1c1103040d4035068020030340407021418005c0c400c3d0822003400e0304160085c0c0c3c2150103070584010f00749081c035008001d02c0c1c2d41c0d807081c018203c110070032000c0044c2d0140c001034038540040e0840090442c2d1005543c8460180040c40f0141401e20502940458542c0b00c9000740c191107031004900b951a2411402410708452180b030402c21142c9040005002250000c0212078001c0700f6407900081a5803242000300050000111603a8002440f8080c48100c52004141c0c1d280003540952100d0306903030b24000c00c41100c4408400402d40142400010f00c10f241501c1c845038403030a000307202c2d813400040019150414a0448038050480d0303481005005508100e42800328818054504010f05415a0002514508014002403090088074024500d8034400d0f01601d0101815004881d805d000b40300002d820751008607245240c0600d426180f0407140304403d041d000c60150074016011941340c10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 11662048 1250 11660798 11660807
    0x150501021902030f10061802070f0b0402011b060b0f0103051003110303120103080c100c09150e09070c02010e0405060108061011060f01090e06010b0904090203010b090a0203040201091203020d 84
    0x581c01d07641806280314640f840c0c00c0600030b059412045940010301e4900b0000e110004042c40c80c007950302d0501c103011080001b0f28810346d884560b41c0200c10910035549030300c01284c03250210950440d03140c0c90410320904012068102c1c8580200031a640d050102d800001101180c00843d00c08562581c140c1e400c102088442c0c0c038000000001506a03803410200b0000c500680d1401c1e0702c00c0b00c4082c0d0004204011001c05c3c8050003400ca040380c3c0c103000e40c2400550040c1941c0c0e0a005071100e511001c0700d00811140204019170706054050845406407411160140c4075044400c0140e0100e01850441c204915107407003503a04c00c2005071144040c945628040c000850601c0c580202801041d140745013640d5020050380e80714240b00c0c07042c5100c80d0704020000054a090040c01c90f1142d0241005000f00564081034680c030000540b800551281603000090241a0340410316800000f14814050400707100c0d0000c500c168003e03211003240542e103c0025444100305a005001a0080e524003031009115 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 11663298 1250 11662048 11662093
    0x8060d080903030f04030203070b0c0d080703090501060e0106022103010b0a020a0803041b1d0c0d02090405040f030e030f07090903200d0810050102030d0207020406030b010b030a15050102 82
    0x42803401d08000303040c0d012a00d076900c210f05801c3c8065000c02c0400845c81e0401544000c0d0240072031550411501c1004581e54042e9902c8039014072030648001003038284241d2000010a4000000b8800260b0f2140a005655420b0040c040140074841d8a040c005001c081d1800c03802c0d01d0400824550784c40c000d001c110784e0f084103040c24114061a41141c01003001c400c0a540240c0c043c900030700440700401c99002d000d400b544d0081c4403070000c0c4048100da600c0041602036010559504c03076035a409aa4090b00000c0c480c420005512074600f03414802409002995204060307c40d4441c0c40b2982114002c05076500310203810b000c15a030000405100f03002c600d8000003452031180c1040f50881c1500215800310514019400d215075110944040c0d600342d2021000f40c2009240107540b40c1d0034140300000b5100d109580300c0c00300c42600043c5050031921268404c90044d900402603610a5856100c00021988241e80e140b40450a00b405440f44029070003c003421640141c009004010504040041910b075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 11664548 1250 11663298 11663303
    0x10201020906030408041508070c0f05120c010e1204030b2e0603090303050601110d0c0507080f030a35041b0803070b010807080a080c0102041a0a02060f0708060d 71
    0x1000e200745800c545582e4041c600aa00c44d000d1540c40d40e0a15007a1181d100303010340002c080098100c1440100d94100085010b400d03000001017411014508040d858009c04922100e000710b0001684048100b040d400103800303400410a6510041c2d2822901c515406580000b9014002c1800800c01c3d40c00168070400022103211072856284019114541100c5001d40c00f150100e611075102008042c1d040c030a040c0c0c00b20007400c0c017481c07080c1c042d200301c0d036198600d010820900600c0030102c01404000c1041e107004081c80000c59181d1f101c111119600e80d01700700c0d00e100100c0c4090800a0785580e070740fa040c82a03944c51300c0c00b000300c100500a015103000070140003a0b6042c0315182c000080d00744d2015041002d000960011540e0f086645001c03000003105a0208020303420004040c4410207000c642050040e070008003050721200c44c07042e60b900911869102c90000d82c4c0d40c2c40320078910b8003000041d0400858a80940b036440c4e40b9410411580c2c48100c071130700c5c0041c1c140d0000640b14601014010100d60 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 11665798 1250 11664548 11664551
    0x9070807020c0307030b0114010306080601060c05030c0610030b090102070b060d060e0f0c1201020705030304060b0112091208090309010c030311160c090c0c030806090a0e0d0305090106080309150702010201 90
    0xc1c402c0b012070b041c00e0182c3c0007600c150401c0da006110000d11003994128512003840c1c1013045a00e850403070b03900c804042c01040300300107400da01d4100740b2808105451030341c400f0720151035113030418010441000b042d6100c1112800601c4000501c146811320031740d9070140d004812a00c09680700800c00c0042c860020088901d41da0384c3d80248040c250400409401c001d205c1e00811800d500d07002082034084a114a03c0100da004202d41d078005440481901d40041e0301c4500401c001c420000142c035902c075141a0101c92500d489240300902c4064240c1d09500d10158903800f41c0e54551040841c1c90f0320682a000340420381e03402da82400280309600c0343c0e52810280e0394190a00c020100d15055414400320306903644003072803074103000c201914418804815403034101900c07a60460707a005481d10f140144034911a6a8000000c0c0700040c25800140290308100c0603070300c05492001c0c01900600058030381042c250718011002c0b071880000000c8501031b0300001c0c400400d1140e610105045035004160403811035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 11667048 1250 11665798 11665813
    0x5030706200a02010605010206090705010219030309050d03021801051204020d05030d02130f08060f070810050607050609010605010e0d020603040812040507090c02011a04020307031d0d030e0c0907080702 89
    0x294008090104042e10754000300362103142c04002494441d0107404030806405c42c0f102041283c1c0c00003005e52140d410700b1600c2940d98054202940180686000a00303c1d00030008681c5c81c2542c103030700600f6011440c01905052404480c01103a00c1d0088003680400203002034041030141c540380c101c1680141c4a041181d107050516240c85041c2d0300704660746011403d5840302841000c0302d202c400e2002d012040010581c6250001d080180b030f00c0007034204000d0080e0040455092410010b00801810001e4031866440a0904d003c50792910211081715465180440110b010f41c8108214000007100512400d0600125000c002c442d034000351045902040400c090340300e00401c034403042d204500440152040910300301d00c0030b0030741d98919080310031a4508200c14562004440000d080b250041d1b03401a2244d407962010b84c020403208150100380d485e1040122444200000c41750b40d410500d6400380040f80c442c1100d00c0d03542c01e001c1c4445500501d0070000603031052144049590140042c4100e6051 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 11668298 1250 11667048 11667101
    0x16050c03030a03060f120c05010f0e0d0c030b060907090b0a03020c07030f02121f02070305070203070b030108010c14090108041e030c03080906040314030604060512010501031101020a05030706 84
    0x840d0700c60001074012988402042040445c103400c084001c01094081d91703151007103a40c1b10812040345000309414000c00f00f0390504c46511540c0403000c00400501001d44460b81401d010034803280078171086400b83c4140000804d0b504280c0b21050040305c0b0f81c1c880c05020741c03c01c0e24803402030300102190420540e003030240c5024a5400c001d800001c502417801480410943d0040c05118120312020310303402d1307019030019043c0c00f180c41001d040c400310396000142c540100340f400b12100d104203403000c0d626125692003c68501409070055049480d0310000308184201010203a400341840786250740c0c1d14200740b00065540d40100403081e4013501c640030641c140a4282d448406c2481003034030030340004140d050704404054010141070381020300c1500410051609a80040607180d03841000c1e08150000b0001c22455200c603009100a404014005856002000840382c000e0009200548900d10130143c6a0519400820b10142064001c0c0c055480c2c444182c81d203801408c09032101081e82c10401005185 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 11669548 1250 11668298 11668303
    0x1803091a0f13050306090d0f0f11012a0309080306040908040b030a050a05010e06060a0f200307060606030902061207020c0d0602070303150b0403150e07061713020616050c03 76
    0x4900801444089010f4100310505282450040603d152a80810400392049401000005d103c00107442e01c03000141d4192401c817501041c025050400d58204000e07446280c40040ca11542700c0c1481e031020400c41d844581c120107940400c000940046420400b0860758140340e000070780e00b2401400020310309a9038844e00401c80d401101d000d41d000e40e50300c1c00e1003807550043c02154010b108201d40e50390346041c00c01c00901d2905c245100041031085600880c00200e006889200e40d602c65a89066200702c0340c441d03240d483c0d6108040403991709180c0040428a6070107032050400f200e401411003030038040410310400711054003800c62010761280c40c0c0c0114280d5901c080010b00e507071141a0150f00e9003540d00c2d002d4140c0c0c4c400c05800080262408062040190141c159011260400f90900c80c80040e000000c000b4006401e140c882801500342c0800c246421000110003288034100b00c8403207540b202c0740340f1041640c01c075000354460740811203000041e51015242041e1806401034806101c080c1001030b2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 11670798 1250 11669548 11669557
    0x70204060506040f1703040501050405040f060f0f030203150106050a05070c090f0204080c0d0203030a0f030e06010f0608010605031b030a150306050601030f02090906091b0301030305030105041803091a0f 89
    0x3800c04d0503400e0910018a5000c2d50841e40d00541c402542002c0c105000070b070450245025890007165507403140e081400031034004200a200b44840f42d50226141c914007103040c0309130b0100b07901910400d070740034500f160204080d9040761107542c0d500341081c009280031921584594025a88404500400f00d0008141d2140c41a0702000b42d10049e80c40b86004002030400c041480308a1140f4071602c20507000d0b0301e0100403a5420941413404440c5026031410076002048030380c1600b810741c8101c034004104800f02072881070540c0c21a444441c001e81e0b841c0c90441c3c4510044580300841c400b561400741082403444095a08201100710101e100701c5541010310704031016500507140283c48409011031540c041c4100b400a5210326000c0d403030b10380701c88045081400040c15990140a01d50009093340000181d0b0076141d50202c401c00d1b6070780d60b4078140241950021700a26200d140380c0f12810b0380c1c031194001d801c950690f25499403c08540b5094561110521429140150150412444e80b16108090041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 11672048 1250 11670798 11670809
    0x11010c080301091509020304030c020105130e0103080a0912050304030b180d0e0a0501020d0c0807240203010501090e01031211030409020a05030f0c0c030d0507020c040905010507081015030207020406050604 90
    0x340300340d800d0300380c10b20680c05540708a1175544100103100110b54002200302e43c858082c24010341d99000484614000080d0307520448101d01c00b60000300402206d24001c1030032103090f0351a200d07455107074101c200022483d1100284941c1c0200020030006a040e0f000b694802d00c1400300451510300074100b14104203051424900148509900d0202c514202540001518003031000348031449890341c01602092035144090109400411480c0800040c0e04500b500181c03c1403d2814003c1c01c040c1c40700180d002801800d02180c4c1800b408625454104090f40c12650404d000455000c41c0726000e5030022502c04280c901ca00040201064110413800240142000350f69041e54030b240041e00450520405003801c0b82002081041c140300034800802d1b00c0711030703c0741e400005141d181d0f100242e10b09400c1c1e188058210b4107245902c1d080c45010760000c7c0c803c00040c9c88a11072036440e40040e110200c0320f805240d9900d013207020340c0e00d0000d100fa805800c500d03201078000174140da12040003420030f8002d544031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 11673298 1250 11672048 11672051
    0x60209120c1e0f040207060b04110403060c02012003060a030206030915010504150b180411070b06030105040b01210b0c090a060509090403050304060207020d2909070311010c08030109 80
    0x40039000d06040180240d840c071540d0a40b89070106800000710300ca10310041441c4140d80120b5200280031481c1e21000d00100c0c0100100a030300e401c013010304015040341c031060b68103e02c0e00c13100d94500360040c021180c1d01d0416082c032028011000d810740d92180c001400c425080b142e030540200c0107031105002580500448401402ca20303480020000c02184140c001c40d001d1401c21125a8480280c022580300b950020383d01941c680d0107800c03400b490ba01d8100b90399a4001d040281c65007864080b60014607180e4010100c80101da0b403000b041c14280e4005540c000c00182003140100551001d801041d200700c501c1c03000401c150903150700d4440900400b5103554449080c0001c003a40c440c41c4ca802c10a000b8492810304c0d13410914018001a82d440e0000c00150034001c0000008040060550442c0c0e1815801030070b40301030640c54100100ea0142e0345940d602000c1b00111082d40464500c1c03403091003000e04030010100e6509596410600d01c60461800341404048010781000801c0329010f980038140c0600c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 11674548 1250 11673298 11673313
    0x70602070f050a03030519110d020c12070303020403020f04180206030c0f030f010f05010206010e0a151502060907090605090115050f0703030c12020304120806010e030f0309040506040510090906020912 88
    0x35028001f00c15142034214035841c001802d00845c0d446001c3c0c5101c0d01e0241c2005840310843c00c0c900742801c9040317021982c0b2041c0003c2107030415405601800030f490081d41e242101010940500c021036805c41c404403080442031850740300602c0c0c8000195401000b80c00b0181c10464045c01140d00d507003050398400c6ca1148910300600130a085004440c0040001b4401411a54035000c101ca01c0388001420000005407685002c4034080c50b1240b0b80d000500c3c1c0040c52051045d44540000c1d107600b02541c5a03001806800c000150080c000e005203400c3d50001040c030341041e460280300d10201800b950b81b081c1801000e1107001007594590000e0300e00035010392408510503170b0402c4002c082c050f000100f51b136030354810720520003c0f440261540b141d028041c200200307640c03200e42c01a03400581084880d585071080a0783c0381ca01240c048050310140c0f200756000d008540b2402e081205955044460400f55000f200040248a0254006030000ca010f400014500340707140000c560030310b808603240c045941c050003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 11675798 1250 11674548 11674561
    0x90306050609011a0904090b1906060e01020d0c020a05190801060e1005090711030a0e0a080a030c0305030a0f06060806010e0a050901120c0f080105070f05030408070602070f050a030305 81
    0x200c80c1c0c800421a410b001940c1051441c040d01050208843c409040100c2c003e005902d4986c000d800081c1c201704841d040745000d80a0a940f0307000c0900004829080c00c500040a500450b5005020303981600034000c014111038007118000541c2d01c0903a88810083c8001a150f202c524102031200f1003080c4011103103040540082c213640740d80c0d005000201410040101a52001181c103096a5044688214544800f14200e0b0f10050307080740c00180d80000070302c0804042e00101c141d0344c00340059440108017540c524800d078940345a500d002d030201c1c000d86203103000a4400d50041d5800300b00b91100040a140000b0b0303d07411689a40c00910100e111001032081a6030000e4084101c05001c550680c0620b061601264040c1e6040c461801c140b400f100807141006200d998000140a02b080c2400c041550748611501a10f802d54803a00800d1034034080b0301171035100d0402c50b8031581d08034070410314000e02a900e0710003d5101070800da032a42d8060040d000001c005100b65502c003406982c010403a420003d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 11677048 1250 11675798 11675801
    0x8011e05120a050f03040e01030602181201020307230a20010e0c040b0d0f061109060c0105040b1e0c071410060303080c07020a030f020609030d0503010915050f10051306090306 77
    0x101036400c4c81c4e80180401c1080d0200340c950315040d00da001c1c1015031100312006500e2503410994040d541d20074400d02c401c007420740c4158051403094640d55035448030302400c00f0b0840100e04260010041142e070030030040840b94002c902049404c48109200d25151b5044800c4c542115440c4400c82c0450300065100c104a1070540a01c1041040845007a42000468be980700458400143c005003e5a01d480064020750291030540b824500051f0140f40e40d0090360340524000d0074101c9080710f42c080c465000c50041e544211001d08400d40714048845141ca0b9603102d0b00741e40d00503801c11036800910001c244210f2909012041401d140240003140060651401400e2040300808100042506020703c03400359881d04840f00c1100c1c2c210070b603000240e405001080b007602c03e24610542510410704840c82c0240e00c6001107040301c0c10807904100c0194003031b070706030312040c12480f405600500038161002e8074504410140012440741c01c0a6181101c0131711041040150765209001242c150380e0200240301c20b0303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 11678298 1250 11677048 11677063
    0x80c060f07091d0601050d060f08010e0a02011209020f0409030806090604290a030501020310061106040b010329090304030611040303090315021303150f0b0108011e05120a05 76
    0x710306255440600f0060070485415894240e0b0f11051104030104007241d01580171070302070034415402440420b1726041810100d03103161081c05101d40c80c00c202070000e11400f007108101e099059441c000c081c021a0000c0307000c2c144243c404c0e07a028000c41190f80c602c1d41c80d48142c0050500c41d8a50358282e250035000c200e0107000040c0100d0040c3d040405056140d00c1ca034011301083c885840750855140d03450b402040c0c5013442030f040140158800400c1c081446100c1500b6001c807501992030200c0c074202c21155a403039010a880083c06100060700510008118800900b9201072944545541c800d500700c0100c8140c0c425103035042940c00000301403050010710b0090f584000074141d060340ca420700e1a40d0081c00c8440921010303024401c3c5010482410702c054048a800000022152465548070309103d0304540ca407079200c114161502c0e0200941c028140a20412071105850394640d42e031900e540c0341030107864012402d402c041c03120030214443d526042035801000c0038400a0600c08890300c1e050303140820 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 11679548 1250 11678298 11678311
    0xa05040201110f0d030f0603080403030905190803040b0304020301020c100b03100e030405040b060409020703030b0103050f04020f01050c01021605030304051204080d030f0e1e010f06050d0b13080c060f 88
    0x69407200308500010384000d186000317240014403280c0141d950001840160401840d180c0001000001c0c1036003c42c142c8182c2d08111620044940890001d8250985130720a252654000f0f10081000004800145601600180c0090b14004003004082d080c81c681014100c001d0fa46e84000c07a000303041c00c01903008500d204040421909480c01e88282d902d0141c0d1103943d20551f01c42141c0101915000c017624018a5245400d54a8a2462a019001c0c010080c0c42c140000d03e010000768448840050403400350381c0141442101c50310541c0119840c1d800319034110348640d002c000d24081c45502542044925008002868070790401d0324040741400300303101c540045220700380011b100640e030101d507021103c1c1150a000605074480c00c02c00700500548001c60146018601c0740c680c40b8010b5134000900317014000020801d4900c944220801c48034280542500903c0740c1074007400007681929410b801524502da01080c40d0411787d948015070780040d010031b4003a04200188032610174010100380c1c01c40c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 11680798 1250 11679548 11679553
    0x60f0c0302070b060d03110709050609060103020a1d0f1027030c060c170307050c0c0102010e1b18090312010906060509010c06060b1912020f160c0b030a0504020111 72
    0xc40383c81e500301ca5100540034620802c45600e0a50406000f140165019400d030000d43d24216540c010707210080c0000c850701802980801c0000706150300c64800c54100f40002e4890910321642d41880001c14441a401d040e0001d4100014200c59541c1310075054102c4220744d10118400341d0f0003035800d100d00c00288401843c1e80408420f0001801058515054554901c0c1141c2c400c2c103241407000e6400c0c0d07500d40000300410000b09000356241c0c020700074890b000e161011140880c4004004a003294007161402546402c2540350048400410311011000680203009144103941052085011441a50032510a80c80002d26604084962a09600400c02e040f800c004992502101405501c1100d02c000d04004042e40180200144c82d4058006842440c00a0303499440603c89400c090200b0074402020581c0710281260440030382c000c4a125143c0d1395081340c101508501844801816200c2c2115140c011036400310300c880709100594800c010290000c1010b0403c0e000140c83e080d2418004141c5d0b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 11682048 1250 11680798 11680807
    0x12020102150f0103150b0d0b010806061002100b0102100501060e120607020601140303071a010f080304080717030c060406091208040b0408131206020705072301031505040207060f0c0302 81
    0x3140b4500901d0440f5001003103400c041c140c80700740030000c0030004089036000d145441d1f0441481850009941030b10203c1088400a803541800c0100d0140ca1881110050b8010400f4510060741070b0402e20401106004840015aa80400d0340c2a03030b50036000300000a0314000411454503080c00c111400500c82d001425050a0440e03009417603000c14091030192120b201c0e44001207840400881e84001d800840c02460354100709007002c0007490a1045510b10368600001040b0786030040120b408540c2c2500c02807902d945048101e840030004611008412f0100344944403031000140047d0f0300c00d138400c1000241d00c80051900d05141031002070200e08000140040100040c01520b9642e00507070800c80b9540c0b69681002d508010a005030010411240b02c8001d00c8104400398000e00b1141c0c0c443d60580c0c14080c0c0361100355490070207141c2c41012242e6803424010455019a226405144049401c004400e84580107d1700340e0317100e07910032600ea540da1164a13013500300b184520040510540b400351b291 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 11683298 1250 11682048 11682061
    0x309011112040b041713050906010e03070e060307031e050d050306010206130602041d0f070c050604030302070302011103070e040e030301050105090915040507050703030605010512040303020306040906061202010215 94
    0x5004002c10050602d214000410b00340400c030380076160078180d078904082d07452144240c20401442c0510842e4010040705000c110b0540c0a0050525404c01c041e000b000302520305001100300800280599406005101d4044040303214041e25034560307100d00010300e01401c5246441407520003540e405204002c02402030008503a030204030b058114030a8841c070240107040c1d08003207000f40310750381c00a06149038040300a01c07440841d0001621a0fa00950010341c0342e6180141600d0420307403400000c001d50000f41c001800030703009901400605000e4400090b820301e0314025407070558410340302c040104003985911000c80c60b080c05030350001e40c1610040c6041d940740a00183c16030023182c107014403400c4e04a0000b8034081e80746c1c10f010907143e0014424088c3e801d144102600c60383c01400141c0009081c4600403403294020021503007401003283c12002150f03903a0700c00714000d4001800c034070b61040d244c0b03d40e20042a5180190009006a1124100c4011103031001a10f002c2e414203010201001d074034104000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 11684548 1250 11683298 11683327
    0x9040f0c0605040303170402030114010801060e090703020102070308030a06050a03030c02030d0e131d0102040b1b030301080c010804030c12180801050103080a050307050f0c03030a050f040b041101051e03090111 92
    0x500c5035942400143e1907520010b405800e25510303c1c112503847c032f0000a4a00015000442214810707044615241c64030251251642d6203400040c1c0503900c0079204100042c5100c00031580010100d0340000c8143e12032000600040c411703841900040e6400c0800d00c190314040c8007420315000c460800741c4003240c900c000701f4204d070b00b42540c8000c1242d8a0840307170f22030b505e22201c1d143d404021a008643d10750300c4501040c0c254100c4a15003485007500c03c50440c800c0000012039060b10441c900030a6551080b00c01100c40703d2006008404200502075120300041d40c0b6002600090060f407507840003501c21021191008000c0d0780428500d80c109401000401c0382c1c030003118526030701c52816076030700d95070f04a0030744282c031512500d40180c200c0051001c6a192010001d180100c001d072106000300d0700c60503020100101e09440281510244201081c0050100d282440e051038040c1400381c14100d10030b4200300f0782c5a03000820714803117500000b0403035006003e204400ca88100000d409050501c068140b61 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 11685798 1250 11684548 11684567
    0x402030a030509040207060203270d050d1d0307030c060b0409030c1709090903090102060708060108060919020c060402030607020d020d0e060f04120b0123010309020f09040f0c0605040303 82
    0x8080c042c00054244403071304d5a0701107455803508120709542d04c0c00c000c05494045e0030803d142d00c000e0400f96103954840707000443d00400640c0ca90380d6070780c20000700340707207031001001d2060726100d03018401c2e42881c0c44124140041e0548a02039202c0c00b980ca8101d0a0400c01c4e40e10b0515214890703441c1286000000342c02010030ba51454101c000d0005219a600480340340c1d1090901c0d40d58446040410404868000002411001402c1c2e0a4807000c0d11100c50603038000c903055a0060200301182c2c0010200e05014a42e20343c0300b010b00342d0401c82202003070156000c036480010120116000b190400c01903040c10003041da0000031510003891022007118000303468a5003000300800f00000c84580b07403100d82d110010348400c0c000140300c05a0f82e6a907090080748482000f102184c98a2052000080046442c04400450300d91a5210f40c0000c201d035004400409645800f01d80c04010b0000d582d00c40c1e00c40ca540300b8803491059849010383c284605200882448aa200c582001010441840000d9205008c034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 11687048 1250 11685798 11685803
    0x105041107031d03070e010305101104050f0d06020a050705060603030c0d080901060506040603020705150105010207060309020102240405070b03040302070905040503160b0106030e0102040b04030209041502040306060e0601080402030a 102
    0x4800c4004000308803d039070364a40e0301c45905108203440440d0f2511178072032050481c1d22032030454611008410f0039009440e030341c00503801c1c82d83c024442007125040085082c9600d0500504400701e42c84603540394012a00201c1208001030004039204040050800143e40c200c44100e0044d401d001c155002c440d0f9404440810600700310b180808160aa44250060006014010401c3d91203035200c0000074020b400402041e01e05100d4402401116210110b0384c6060394010780c00703042c030b00382810000d07400f50012010480c114805c03403196171545030b8050f400c0340080442200021260410b03080952800100d504002e2099904109120000c0e4001441e402101c103840d030046542da0703481c24018110700413841078500d60001d00d690781d4100000c140009068a0903924200301100a07420030714200d00407402030a541540410040c0098a042007030103902078414540d400080740d000803144287d0b00507a0046813265112030081c0709050122080c240e04c840280303441c58151629400080d51819031001c00f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 11688298 1250 11687048 11687057
    0x6040b0406090804090f090b0609060904170c1b12070b040315090203030c010f05011e03081305130203010602150f0a09061104030506061009030503031801141e010504110703 76
    0x11810844443c0580d030041041103c1001072041102400003c0c110302e4038101c505203807a0001480a00e400300d0054002d04000d02421196901c41c0d840b52443d641d02011000401b20078032014010103010005202c0d104082d00482e10003650340402d004503011500d040c12019041481c2c00d1100040c01d40680d01100d801c00803007084011030700300a000403d0035120180d054000058401811034054000131802c03606803070101b03e16a030344c0f00445a411143c1208a1040d01e802008001040d00503000c0c0085007810a440318402e41e44600064968080303c200340b80a58022004025841c0c0500643d10f030f040050144031407a00c0c200604202008000b071840c1c14030340d40c8807024828055594424040b50903050502d0b550b0781d4407820290b540b100200c031900c1c81141e403001700803071807441403201c1000c40b03501a0080d4115114420002075000500e00d10805940d80c404140e404400505d52090080191040c601001d58401c4880120040140c004502950603c1c884031018018507040300c60083d00342c40d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 11689548 1250 11688298 11688311
    0x70609020105120a0e070f1a0702120d020f060a090309050105070309030206040807051c0b01120302030c07030c080d02150c07020f0414160c0c050f0d0b01080c010e010206040b0406 79
    0x140e0b02402500f8403400c1c5841210200110b0006660110807501a90b1045540e500d030b5840c07079144074510b24011154803c281d00c082c001c07141c00c00e80251180d00e100a0200c0000300207400c0f01443d105240c15800010703808160319004400c001d0140742e40142c04050305010141d01c40c0c601170040d003801c0c070549040040018600e401c0c140b0038030403000030b5940244550760b200d680383c880c0d0341d030ba200600400c0c4c404c03074800c810031613804107401002c5181540314254180c16840d1560881c0780104400044e070960008103c200b01585080c80741802452143c010502611f0800b00c0300b62505545851003015540048000030502a5940e41c0715132082c0300c03510840c3d480100384041888642240100f94115090588c003802c0b001340041030070720404000c8180e56049003d0074003210b101400305000340c140590305c4001d100900b07100b199403401c0354014085a81c2c01103a9550f04241e620300768013001c016080a00f507043c0b03030b6074414005401c0c26004d100800c0e80e410079403107442c4003820150006003026952030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 11690654 1106 11689548 11689553
    0x108030a142a0304030501050901020304031d0901030b061c0620030103111c0503070c050f01020d05030a09110a030501060f0506120a050702010204080a080706050109050606070609 79
    0x4000a440300c2c0b01c4210019440888000c492140020032012001c40c0c024014103000d40d0039a40016a24030f440d0a00400f882c6020b0901851200030030301603619035444000b03c07815079800140d409a6a1951400039602005030b04044551400000900c0103002c0d003544401400d1107014400d102103a5480c03120311461009010081034003001c40c80da0701050800d04150764030075011580040b01890191201c5245411085003110040c1c842d46082c880c5060071500c10b00020001c0c001886424455800a0303c2800000c4c0100031642d510601101071184504044000000240003941c086803a800c045020b04554020324a41946002d000540341c2008030403510403480c055110f000a0b211051240c015100c0544030104640d024400403400d00d03030901484083c00d20488100b50365070401d1904000361103050f4490b10a00b4580400c02000d81c540d4011954210761010700003625140a2 = true := by decide +kernel

theorem cover : BRFrame.Cov 11510798 11690654 := by
  have h0 := BRFrame.cov_init 11510798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 11510798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 11510798 ≤ n) (h2 : n < 11690654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
