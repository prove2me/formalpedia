-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1591
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:45:02.028305+00:00
-- url     : https://prove2.me/submissions/19460af5-ca5f-4d0b-9676-c4638fe5a862

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 285971223 ≤ n < 286151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 285972473 1250 285971223 285971227
    0xd03020a0f06150e01060306051c03030b1311070605010e0f040b040c05090405150603011506051c060602030c010b040b0d14150106020133120503120705121b 69
    0x3a1182800d10841c144126012950741d00e01c941800c01c2c480c109800b4088940d01c00d01a54034080005041d102281c00c4a481a0075000d4076002d8a840380d00800c003410303414140031603401e016000141c1110811040c1c1440c541c1000a036010381420700009201d1548550070401080e620740c01c424540302011640ca01000f141d04012601041801103d0780c0e0013885100c071940443d89070030104041c2d0500340c50440c0e1f107900240740f9804405261980e25480a01500200b007c01c4089001b04480240342c80b032003060050016441310000d01d00c2c1c448040d04002c44505125840d134a5400950b281c3c41601c000c0c05a5190103011410352506001c1c0f6000c3c00c40062007070451020700d44400203407070030b4030090410520481001201c0081042402d13402428290000a040318411106034008500d910040c0c3c2d0300000401c902c0900c1e48840e00c00c1d4191644040c0004402d81c480c0707400c40c6135105240440300e018400500b008000340d8400024114010710715000c0c51a070301d81000400d04140c20408404c000401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 285973723 1250 285972473 285972493
    0xc080607051e0d1104080609060c04091509110702010f0311090405060301020c100b0f24130803070f170a020a030305060402040f030c03060e06100501030f0b0423060d0302 75
    0x24a5003109101521004940b501d01656494800c41d06a10130384c02c141038011804108981040c44010780c03020030352020f0311241c80c00c90401c510b40d10841c02a01035040d80d860310304001c10070107d140d00c007500280008003d40d000c0c03040071070401d801008080b800514000710502c0740354031900501000443e000f0415041106200030400900300051907190035650a00c61320b49400010003200c62003542c01800007030358282c50000d0000c59242c00700c0942c001c20784101511030385034100b10f1105c442e0102601150b1140d2000c10003c070000e01d25806401d95100110700c0701c0911110021801006114043c40e0b4034540016252241a01034480c1000158028804030b40120707009420050713110100410041c0f4082d291807079030390080c030030303400c01d891a5480e840c06204100d1580314000050005500400c1c140c600701400c154501c0c00d600403181055103489417007580c130001e504002420b9000820a010b152030400031100320042044050035288102c030b000c1400c07400c04044410324a90160301403c10001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 285974973 1250 285973723 285973747
    0xd020d03091109040f020901050f060405090601051308060a0c03060506071b0510200a24060e0703020a030c03020408120310090207050a1407061b050c1504030c08060705 74
    0x10001c40103680c400700010b6215910341d9900207051150340310f0300a00040c58243d006000c0340e0303901600280e00500401030b4501095a031784040e40c00301d0b1411175540c42980da0f510012542c5001c2c510220320300c150704000c04a0b5520700403c0151284554079010010808049400c80554032780d8070a55810100401441000c2040007902c2c85200071080c00c205441540d50f004507a0010814506000144138114a2050008000d003000804107049004059007000b603100c1d10010242d141c000d010301c4c4c2210811840c1141c2a80202000b06504004400c19241500c8040c010350301c41d0200000103032411601c104243d0282c0b00755425980480c0050074007902c0000708002031f0b80003a01404080c02e00d030b0f200250098140c001014500d21520141c91226190b2400040d10303820034032100802c2d00322090521909a008000302d041070029001c100c018962401c0c140c0c1402d966120803600941708161004007194031751300520071280304071102c640840e03459480c640c44280a441d5400011420401030719040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 285976223 1250 285974973 285974981
    0xb0d0c030e030a0c06050114030c061612170603010c05090d05010b04060b0919060507061107021207080f07151103040f0f0f350109080f0c0c01020d020d03 68
    0x2055060000340d4810100c90715246402c8490f0003400100a5070320203080003118011a801080802c0100102c181038800180d11a1405d03c01c0c036000ba100842d030401d40404018a00b80007540286000e02204803070b020041c45c8400b04c40a80a540140c50040350315401c0503c10b252030003505503201c1e030406811800708802c043e144141aa000d40d00c0b10341c410010707030700d41c41180000c080201800356200d0000c0140004a83c0d0b0200f0b1502140c0c080c541045070581200448051b154011000500c0075050400300380c642c015900c010f500141c540a0078085990002407240c1520546c80488441a84e514060b40e56000a400f504901c0c040515010759103a00034a840d02e100e0f2074820a5030304040c0c50340444454041c0d55401a0100c01d0030000410010440350325010161000d00e511400307035825020fa90b180550b803001e5a03524a500742241d01404802980058800743e84005810358892171200408440d03000200e451840740245d10350464a980006440f00c0c0c401d00c190090200081e440509600074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 285977473 1250 285976223 285976241
    0x20a1103030409050a050609011505030c0703090e0f040b15011d010201060e07020303060f120a02090a0e10020d15050d030f020c09090d141c0213120b0a0e070b0d 71
    0x544010710000c103200c80140130b5180b0034043c00f0400a00791800c00b0801040c40d106078010010740c0a066403e4002c66400022240d2020030100000d0f90340721707980b408603208640769100c1401300040c80184101c282c0d0106045000da40a103840c00356684680e50b20b405038006c110015400f203552000d2412444083c51072902e0a00c0c07050000182e8280c1c0c0741c81036641108100e80304c01c0140c100104000040c900800890f09180090f01c2640306940b001455075940c1c1040e40c4041d01c500c0c6103100150180105070403402c3c6000c005000d891120b001d150255000e0b4011510a04003582040700c030040409042d600c3c2d104640000b801d84045112a031000d94003d54210203410841c01860718001d2191901400b480c01105114000c110001c1070900c01030403016200c1244110303d00801c280340e1059128402d43e118041101030050355010880024181c440340c0740c2c424000e100c40c9103118400d100c0780182d87c40c442c0164035400e1088040000b01c20b521490580165101d00710b06211031000810241d0041002d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 285978723 1250 285977473 285977479
    0x30209062b0c020a050601060c0c050d050f0111120f0403090501110a02040603030e01020d090f06110a0b010306050906010b0304032c090a0e150412050a050d06080d0305070f020a11 79
    0x1150141c1c40354038054070040c024407805a4002101c11381040b07010000b242c0100344074a0500292211655181084000e9129003403217104011250000d10209200c181d4544100c00002c01590310061682ca04540100000c0ba00d03854050300000c10510038141118422645913445202c03aa0515006548074002d0620071451441a03135070090040c0c0711842808013035402074031014020803591000901d058000781e814000c000d50200b00300070059099003018142c60300c0d400d01204050303641181510384000302d8005405009101c00010901490b030b44400d025002c04010303500581e803181203080c0148400c0d02c0003070009520465050f406000010b1076000400078851180062100100180500c9802c0c0c0b02110541e0766810603034a10b180802c0910a0345c02c80004c401e44618103900d500c54014855a110340c14007000180c4036070014410801c50350380d02d60f905401c000e02034450301a260350f01c1002c545000468501000b04c1c1c03605d4051110101c2c600a0b0307a00504009540740e8455002080707202d05a60 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 285979973 1250 285978723 285978787
    0x61d0403080c1207120c0f02070e0c0f0f030105150a0f050306060c150a0b03011a0904050313080d03141302040b03030910032408030f030603070306090602030402010f03020906 77
    0x440908103c9014001d500c5560b40d0341c0b4911803840a03000b1140d85500e08018031802e06505c000070f50300415801d0840e010240040701c81d41d6000c071240c0c920310800c03c00381c9021034000b4000d200760034410701440c183c07003058641c181c1c800c08034144d0031264030451003000302040d0581505480a40304000965010401600d8941044a050412894a42c0e50101a55411206000c000800106216440200c1c60450080c892011024100011156483c9607140205000d20000c0c0c2845800c1084414200c140e540010b8042c3e500c007042a256115400801e00084c18000801820400b10a9403402482c1048100000c01714950030000103110400005805000600085103160303189a9607500b03032009030f02e0100e03481030b40c07040000d840c44c5501c03540e003050080c0700e10900085100100b40d0703200014200c400c075560b444280000e464444658030040440c4d00b0000c1d008100f103100d030040c5000701d100b03032940022400941c10075000da009002da202e8010300140540d00e0800214419601c0f800d458109481c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 285981223 1250 285979973 285979987
    0xc03030c071a09100b0301021c1107020910060f0206010b0a181a1213120818031c0c0804120c0303111605060106020c0a03060e03120f0a061d0403080c 66
    0x41d0030010460f880e10041c1c20400300303008005a036000304010b00c00214001c602d40b40ea5029004980c01c41896108110381c0d40310b00c45d20b00e100c0c8510844280580090070780605190000c1c0b07124015887d401080001281030940721082800096803506886c60024040c1c240503101c0c40071114141c089403041158141801c0005000100c5001840310ba00313021007540d501c805070280f06800810161142e00c000310719002103800305001980b0900035109620740713411a40c68050310001b03080c0740e080400d5003e00000580e0440300340c40b003003c192100c222550511264003c00c1041d20a100c0841d40941061703541a0103c0728144551480481e0754400e00700042c000c11541d400c0d801d01d0f080351402441c44e8448810341070a00408012280c0140386507c020001c13000c0c8807000c00d910384814440107100c180c131f40d006640e15490900649042c0f0418444922451401d001407160900701a030304001a06d24000c004151010301800c040741041c148103201c01e030790b110780da821940d202d4020080c4200d010244078075 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 285982473 1250 285981223 285981263
    0x4110402070c0f080c01050c07030305130801060b3f31060b0603071b0830090a0201090b09041e020c010612020d11040f020c1b060c03030c07 62
    0x80c1014251811007094521304260031340b071070501490320190500030306121490416800250f25000c0e00d81c94602181c80701112881c040d03203103245400c4031429508210020134060709100180c014600c0c0010b841e01c19100740c100143d00c880800c0c142d0556140070075201d1048100036800a900903003558110b502052220161441c00305824480b400030310f8485001e001405071074020003003031840484000d0328504011801604c1c414540f550031030001c4091040d1814001c0c1402030b90b03050045041c09004142d90000030302c01c1145103072160001d02c0c010f0400302c3d40321700c4000b814117101507042c1c403402485801c1c00000341d4240c021038942036005803204208506c0c2d01290700024186070742000056110a4003401d00d50a42c0c3c100c1c0c00250703071842203142850151703884210701000260001200c8920060101c0420301030042000c000d000180001030a0884003400100404242d0701c0107032090004007510100005442034240340d208a900600114002012020041120511820900581e103d0032146 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 285983723 1250 285982473 285982493
    0x60a05180a051908010c0806030304090c0203040f0e040b0c030106120f0b120a060509030304020d02040c030f0e1e010239010903120b040905060c09011704050703050f0708060411040207 81
    0x3c2c40d4400e240349242040015024028100301100500f44a0114940200804c2d502d0046129104d040794464900c110500e000f4000c0710058404030484801040d140c0718000c02aa4050320210746201904c400240f00c0031143c400c2d00c2c107031034042d0389a09450080e6440b06001e8004a803025101c3c65481e001003010340e41c2c0142c204c284207000303030107045440c06506090301101e01c000e013078000c0c0d50400c004100c016075814115088440d81118005a2000c0b1100110001c1244c040e214001516180084030503580008520007000080750101b20000c8001e03440c1d0f030a0380240e652816000c14847c18110100d10307007041070400c01c207100501c01d4414404040d12800e50b9840c039015804101400c00708100d000d00c2d402a00c0000304150780500080050f46c2c1c03500e6807081c008112601e00c0001043e0700c2c6c4140c0c41210070111601000c0010282410103003422a150716107840112002d125080d02d01d412044041207220450326000040c0599a0b40d98a54000000c4041100c640c800e900304501da00054a00d91 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 285984973 1250 285983723 285983749
    0x90405010506030d0221031e040804080705060f090f01050705190b070206040201020d03021b16210c0312030b040e060403020705010306180c0201180503090906060a05180a05 76
    0x100100c1c0e2400d220302814200311035690310004640240b448030a4042000e031117055425001290a503482e584c50769502080701003690800040d0b000b00041c402800000c0011308241c5103441c0644400907601e904100d501d10035040d80c0921100f00b171010580714a80b5208110140c8010f04284ac40e2495541c0c4040c2003502620628138046d50100a00e000d0010118013194040c0990000b851941480d40003c0e59a6141c500c3e08400c0540024a0034585d03c0440b4400511150000031100c00806100c4801c861500500641e0025410300c1704d001426220040c4400380c3c00c0c0c000a4402006065482d4600d081c0802e0b0808000c0c9602d0781c00a00da1a00e503032140221040c81c40d00645250b061070b00e8000d09045841c1c1c811410181411414804d03180038a1000186000b86100000d07400201340083c0d000d8524014040d82148201c40c008041c080c0200051960a40c03c4486030603da03290b03020483c181c0111012500000d409001525148000c0314400c54114001003850b46929660340c000b07111100301c20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 285986223 1250 285984973 285984983
    0x1e0726120408010b09010302030604110f0d0303020717090a150302040b04030605040b150a140a0504092a18090f1704090e0a0327030b07260103110402090402090904 72
    0x507003000184000c1c4244030740c205044a01d041c01c0d51660b00001da030342e0b0b005400034007030340820107411f000303a81e03002048052160003030800c0995041d00d0030b01a0003504044010344100c0c0d1410f40203800b40410200302c86903140f000b8034091406040402c07061041540c80b224a050590800020440700b070124040c1c0300443c841c01010400b854540350401d00c20303401a0511140c60007a4a05454554411203240240d40f080f1641804c48030b15003001900c04480c9078000d5812526202e4100e040c4072804240030112004040703200c10705000e40e5582c0900740c4080c892002180c940d1840702c0c40c1c10b403c03500101d00107070055044802c0804a910f60f00c00d01c000c5440c1e4200d1424002030100020700180c01000c0d008005007000c0d000c03070841a10040d01c40385107c000b16840409040706019480d110076000c4001c5c2d50041d850304001d142c1200094001c3c400e2440600200d032090351803040c012201404241a80c1d1b114004c0c0c4903980144040c031000e50002d40303031158425001e124201d0280c4a14070114403683c007072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 285987473 1250 285986223 285986227
    0xc0604091a01090506031f030b0f1b0307050406120221060312030c0f2107020109031710090203130803130c05103c0e01021e072612 58
    0x88804040780090a07441d68140304151108115556a14044e69802001d54540e0748a804c202e40c070726000d1105640005080c00460000d10101c0607003003080611031052001c100e000c40c3c50300f000c0c411a90000f00e81c240b00017402000188080c0b0702c210f0744a82100c40d248809400c04148070208403180c000c0d0400601c25841c66002c0000c00d107010044521400000d201132859418040305e0040340c1c4c07041805560000c400003ca0550441d0700700c4003000c400300c50500340e42e020306050000901030003080e40c00742c1c001400800d100480e00790030507400c1d000b0304404001c044414a0078226401a4100401d062080c0913105031220200d2407201c0214410a40001d400a0a107114640704210795850b810580c0262091035040c1802900b000540440d0649c0240034200b1201c0c1c00f0b07042c01e2001e1112705034040750300060200b60059401144042119400f6000e540040c60340084008a0341800071045d541036100c41401c100d241c03041c1c031129041107500074000040c42c1499041529000d448a100c079111080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 285988723 1250 285987473 285987491
    0x100207142419020d2111090a080102040f0e0f070807020f07060206061003180b0604020d0204080a03110f0c010c080d0507050403060b0303040b0919050301050705071e0812090c060409 80
    0x410311422894265509008040c1d0003203800c4400010a07200303502424555408040c00c03022a41e8050f13031f04007500101a00310b040d072a05c00c0b190203500203100780c000f00c000e2450080b41c541811007a03240300d4032140c0d00d001c01c0e13a0b0320440101ca20845c060710801c150300441c445070070344007010300c103d1010f003a01d078008010900b0403506018500880a100008161078207400c03115402d200741501000c40e80241c2e9400443d110a070003e4000d00c10890342c1d1044610024000809640116464145034000e441c0d1a40c1d02c2d0300c02c540d090300c1d40c407003612200090b000f455500b02c556014120004500d400345492a0800100d007160400300c070420346240d40030440c04901042000403a000b022021903054003e9400c181c5170007520034060240100b000e21504403051a0021009100304100c000c100040c024001401c0985c0003409503845404250b41c40480e060409a240c40c120011741c80b00b550041e45917151101e00035120810f064080c010034814011a8100c0110343d840740090400ba040d810070000340140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 285989973 1250 285988723 285988727
    0x201060311030601060f050a110106030b0108251a09060a0c05070b0a050d0e0a050a06020901111c050306011b03080f0703140c090102070506040311100207142419 71
    0x280c01e40d42d01c070760320410042c010f90340e000c803864080001d541001d0b500e451204400381c1c1d40100c0d5035a2414907628020b0000203005010380307039038100c850b00c1e4161404104400c840d100c5490040c0103002480850407000c0000b07011902040c4150861400403c0c1010f00040028002d80d0201d03008030005824604090305110003405014000c00aa035100c2c0d01e484402c00d809007035030140540c20203200b0350300c2218101100b014404070603a42e920100b03641006440380b130000025081003042d60300150103a407039059a0000000c00c0002c40303444035070458a55110000442c0c0300d920043c181410840409000e8410065042d150301c0c101c3d02c261034409041c03400803072036411003100500080800d0b0800c079101034070840b05e80d0700940062419407070700d0b6a4110180141d141c0b41081c3e11554200d1400280003003070081c0e5488041d042901143e6030749803918420002ca960358424042e400c0b560301101200001d900e0312501046004250703080607180220003540680c0f075500803d006507402e01c81e44450486183d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 285991223 1250 285989973 285989993
    0xb04061505060c07031106070615060e030f06010b0310051002070303080f070806010e0103020f0a05090a090501050117060a0f061101050622050a0b040207030504080601080601051819020a02010603 86
    0xc04140d45039410020304008140c1c3c4d032846440081c110b040c201c03180403500e844001c11a040550170240c1444140203004103131004032100d00c103040016401c08001e505502d00468801c407220742103001803084e0790800103000d84542c0040c0c20180d00045802c1d00041c0ca40302d0618802085001d0b40180c10501d00e9070602038441030000f00740e00c04082c407050070460025004a44a80c01101c20f1070490041c40c034901c0140d009203c0c50798480c00c004004203107131903816841402801c0101081d40d44c07040e0980c0d6404e50300d05031785007170003810701142080c54144500300200400c5584007000074500122255240342c08005059250070010018142c2c03001240680c400b40941c54002e0760070355150005100e0509401c0c071071644900743c00031190f06c3e0300104107900c48030b4106411070100104119601c0802e460090220380c042c2c450b4074a03601824000003881040031030050f04813000540b07041c5010405440c1002c003107400408a0600c4d098450b9148084c50480c8080e00030190180c000182071429400d100004c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 285992473 1250 285991223 285991229
    0x7030b160302040509010b071a31050c06031302060a03020405120a020f10030609140402090a0204060509011229040b0f0d02100908100f0b040507020a140106030b040615 74
    0x40750041004101e10340b24031880c2d904541204200316107400d0349140c80180001031a11080c0720040c1d14007441071039540c0241c00c0d81c01c159a506e8000e00d01034041003481d4000c9811402900c0d039007002c049440c490401c80e0085900c000010403001c0100015030004465400500c407080009038003080601c03903030406d1056904c3d0160908014080383e0500d0f40042c0600c100c002c0d205010301c10004401001d50301a8104034090603600302c0030300404200364507808401c20111403d074860004e0a0108007034401901c212400c4e50b5840e40e820f4940000e000064404428000354084295a90b03612810301c40c041d0950030340310010b150307200c00100c0a141b08100a0f41e0004208510551030350021410582e500c1d00c210f68800c0d419070f108180d80c00500f8003a1a8402b240d44180614041c1b4018121f0741d1409502004480c0000001000300007154000e00080380e46c04c80e011409a4003210011012038908440049132102c0030001054054407a80c90300d10001041d1022903c41d9191014045441640685803000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 285993723 1250 285992473 285992477
    0x50901050a112b0603020303070803070206070809060c030c2107140903060a090c030c030f0201080703090201080f0c0d0e070807090510091509020307050c0d110d0e03010e07030b16 79
    0x3007011807043c01645050320b825501801001c0c09040c03049180a400501c011a0003d003600e407150003074201000d07075a01c00c030341c1e060050007a000003035481d50080200c3e60180782000c000382001e44d202486030000d540040c061030f41c6030800340703c860800c3c2ca034021504011310b55006511303d0b5051a9001030f00314010031000c6809120103000c0c00d0301d151000030384c10787c0c01000c03007402091050311828000c032501105c0d04098144000140040284542c00f501014224800e0360780f02c8455880e10422401c445100c88002c0c0010710800c045004090500d8007560891401d55400c1c0c90000201d50034030807147c014415070751903004a80e08100e08041030007a04002c00c84640c040c4010b02d81030901950303d520500404104075074820701410412601e02c021005480650004c5507a4206058003405581001601d99035910801040c0304a0354810325030700c440849024028014a01110410f5440c200040b503c3c940640d641c0c66081903031001005082b0085001c0c004070045801c00c0020048110a079100b03081c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 285994973 1250 285993723 285993727
    0x9031101050114010c14060f0103110f09010b030604060f080717030408060c0d15060905090703090201120911060d06032006040303050307180b030a0b03061005010309021201050901050a11 82
    0x4258802109501d60035024a00f81080c4d6003071703141c03101121030300903403180c2c036807041c00100041780c0c08e444e19840c1a24003411207404001201003c01103001014411290406d402800412a118560000c0c40c2c12a000070004034100e0b4442440311030010a40d404151103034003403081040344908456100d42d0400d00040510318003030a0000d200d41e80c140140014110003000103000c054081740360f03c4100d001c0b40d03081c01c3e03601070382c2c3d207100050082c0c90a0056601c60079020001c030390b4a50207803040002103070381a116401c801c1070680d540303c011300d80c84000b654030025046011040c1c3e41c40000501099584080004420b4198203196960903564440415101c4800020881c00c1e903801080d2002c8990520304036903a41d440550841b156403c00450f8100e0444c100b50114002d07500c00081c40c07140720b55180400900c0032450030580e036610192155070001c075000380203000d00d500c04d4000301030060000d000e440c0e500780c0203210103084910460b000300b4a65500d4003481980e542070b019640c3c40d141c2000da400c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 285996223 1250 285994973 285994979
    0x40501050a0e0705070c080102030612010506030606120a06060902070c0f0605120c0909040c050f0a0513180206070f02040518061602010e010e1507080103080403080c010f020d090311010501 83
    0x40002080340502e18a910400002651240c850412036803500e910218408450b5520070b40903000c7d40041e211f203481004d14030803080c41039605105e0700d84282320040060915403500f0b01403229050801e45040c41d14012420000049401340c041d4500804c0408001a500e40203820441c10580303007900039506901d40000c0030040c4aa014007600e0b0080807806011195403110290240ca80c0300d90311245810444100800040c00340e24600c8608448080d503000102c041e40c0740800c220320b0403500a9507848030325034200411b0022103070b014235003c03844800001100c100c607070000380c410340100700100c9001030001060000c5082c107003d07203508045a0340c41080101c0c204204280c56180040c41044105a86140a100507100750041090749074540c001f0410742059a0502c0e844501e0940141c4112900c1000300d00460b1288003168101c940041c9082c5c206400c5903502c80003503000b90140c510b15925240344a01c182040e00c0200003030310101d0f600060850003407802500d41700624481c2c1d5483e0345010010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 285997473 1250 285996223 285996229
    0x8180c0306010b030c0702122a060a03090501090f080c0106090c050318160602010603111905060f0f0424020c0a06030b1f09051e01090509041103060403021b04050105 73
    0x440c15540c00f4120039032640c3d200130080019001c0c40340f02a43c02400503082400800d00440e80d06003000510030300c02061030503000130f5100c0030700f500384440e00f00404101002d613051290f40607810091040001090021050304c0d01c3c4840c0541280c1a21503200001d03915513145424443c0000030000d890081c0201422008003034014000245a0700000324248402d50340c0da0810700c0009619140d0040c114003075615804000c0c001c0c495400110381140010782555005d2038040740044902c0d2070401c0040d20f560800050220710b80080542010a040502041540842d01b8010340041c2411002c00742c070319401c6e1040b042c201070401000c2020341d046038502900503120b0402e218140c030b6941c180403c003401542e0110345c06217640760b10002a40d50000d01002c84950040d255000c892003200d40b146954506240110000c1c10000941c2c08144071010811090519000559026000d0b100640a040c110b170013081c10b005044070220b0050700b02507105000c00e414078001800c1c40b101a102041250f0501003c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 285998723 1250 285997473 285997483
    0x2901080106030908070c0e220506010915270b061303020402091305101a03090604110109170106180e030403020d021c060501060e090403020c010e04020f04030308180c03 74
    0xc203020943c85244040a01100d5011246416400480d00c103441e81d40e400c02a04106054134402c0c49822500c041d400403a00340c09813111074039009070181071035900c0c0400401c0141a20031100040341018280015880e54410740b820790b4240303401071444450071041d0700400301c07102651101d1258074180304960842c0110141c400550fa130580d80180d80307403030410009131001c0503c120f2003909400c01d010009100003c003824012600509805c0c001c1c81319040c0440b03403501040310031401503400300c03000501041c401d60440602c690107041a84240340c95580c1e0608000e040e140011040e91107017030801043ca00400c000151501c11001044050403044c0d400d0345a1017188406445010000c06400035540d58031001d24600c01c00e0414018441c1503890540d02605003446050003141c0d030780d80c101e13115082500003948250351640c0580b0803070703c2220043d107a42d1f0202c040c45070090390900802d038504c03000500400240d4003a49500007a890907403940340c1c1070801104540c415412520035001140c43c0016 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 285999973 1250 285998723 285998729
    0x31409030712081915051302040801060b070503160c120b1009060f03080c120313050f01182a0602010e01060506090102060f04030e0a0e070f0e360a29010801 69
    0x1300c08119241032205032200d502c4e5540201d680040605000f94441c442ca41c02401103a2003207000313104550b910f0307601440b140154800a0419042048081a080203091042d01024030884d8668449900d030004504402009230003140c030500c03240107101c240b403e070100d104020189100c081c0603490030039548840e0010140f200410751785010644420305103090088068004c14880d8094030b9140a070003a003452041751100380c44500407400108a010010700900351f405001e8480030078403070798903905c4000da41c0d80d007001024200440490608040035441d612401406541d0000c10500c13000c00c8800d0031684c56501c018030480b420841141d060740c0100f185d0b40c0c0104000000c0c1c0c0250382e24201680c50015102c2c0c0c850b84861071013008038002d450111001d0084c2e80c5641e85005c40b00d540c031800ea0300e480e0b1040001d035100000312501554044002103034440042000407054101080000115180c103042e00e00860090715034118800c1000319180070310303210640c55001c0c0a0078070908001303000d42c2c030180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 286001223 1250 285999973 286000021
    0x5100510120f0c03023606161203060515040e0a1503050d03090c051e1e1e09060108040b131113150b1e030703140903071208 55
    0x1115441c9844566881140d1020200900740001c0c1c0340240001d000b50312044048140820070441440300e00354018483d4482903070ba04003014001503480400820307810807001c45140441503158040010443c0b0890100c040081c0c502103025402d10080055400d000c848500d07110206200c10003c50964240480d040000c661000981c10800191a64249070301e030006040f51107052800d0703101c15419882038528a0003441a034a10540b1402041200d0b40c540440084001d80d801808000c0c5c03500020602c00750488403145013000f00c40f8804584242900c08003403200103d00e40003407806007060312182c0c1d8848400d10300b08285250560700c0c186080c0300074107030b0381c0340c1003007100d80c00c04000407055030a084920083c00084009038100980c00074048210316809940080c5600241c96140c0005407014085017017602090303a140032034210a6508010f104908041c0c940e203041c5007200c00388070090f00454802000e1955801d550810b00744006440140700200881c503010844940324030003801380d20311a21 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 286002473 1250 286001223 286001237
    0xf03070306030c0803031b090d03350411030c0310050402010507081801230403020409080f04030c080f281a090d260606071b0b0307020105100510 64
    0x1561088004208a400043c990110310b00081802d0728004040c52007051602c820600c94502c0301e07908030f228055140b045400c0181d01d07001a00007409441c80c0c1e5203101650020070344081da007064401c90003000c11a030303403a4211f4046c103200c1440400d070020b0002c03200540c02441242d04482c0801c1c2c2d101001b00c288600107a995010400716840b800803200340b5504035075041e407280d0703003d404110144820522180400e0b4500140040d01005044c042003034540703e6002030030b1928540034030018088940d02160801020011000d0701000b00015001542c00b50030f51249060030414401d10707001c2421380707a813000d81c04800000f8a42800c5c85058070090304071006050408075525101400d0a17a0561070f004020001e0204036541d0800200000824060380e901948131810210f68100070002e010008458030700c4000140c02410144000d2070304520415015410321001c803410700070124242c0242000c0d0900200f440380d02035090103042e0f0000a100144010b4910313050019104007500150f04040c0859 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 286003723 1250 286002473 286002481
    0xc09031401020408060c1909081c0c08040f18050f0c0d020c011b020d0504030506010501180801060e0a0b030c0109050418050609070617010e0109270311100b060f03 72
    0xb0740594008081e500c0445640703041c506541a02504224081200302d501242034a401500c07a08000d0b00320b504810107015a807256048822a996010084d041400494038040300000c6c20326000380005c2030300c0f03c203c0d4502c80c1041800440c00c0140c0c4d110b0300c0503c1c101014030509000b102d401030340004013160b005541c1c101224204010f030003510680f4205500e400003a0114186103000204620380603825204405401c05040c0c419002e0f50001074035a900204c010300c00e40d4051641500e6910074415020590380d074401c25542904c00c41e800494000c004102404031900950040140e009000ca029120311502100024040380c2c8902c42e10f4840c507200c190900340034540307900f0712080a8111040e0f0b4520f180200100d5540e2141d4031481c0c00040810110455a0ba901c2440a060352203c205179240da0740f90013401c0c4050240340d90170a10242c49801c549500c00249042521003600c651600000c0e190202195403c00510710740c03040c000c034200302c1ca01c03003d660b40c501110380203500580d010342c40e0b8803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 286004973 1250 286003723 286003763
    0x9060108061006050a030f1805070816051905090405030d06050109030f020d150e0717071203081b1206040b01050f0702060c0f010c111020180a09060503010b03010c0903 74
    0x3c2c207087c2030840c3c0e900d099031b690560008040316650b600d000c3c4040300c048135541d11441ea565600c101e082c42da4011100c1c0240850b141c140d0314442c514605202c01d40d403154a800000d400c4000a4408852030b900000d0074244030a61070048100a000c04d08021041b681703180c07580604455880f400030320904031070202c2020481a030f01c03800414031440d8020401c1f003040e400b40c107540701e5550044102c4c0119444040c01003410000742c0406585020600301c0061505035025680c181001d4050040805040c04014941040101a1000c000030061441003800e1410901080ba00403644a904101c41000300700c3d0040300d035004440c007169060360300030b41e2045c5042c5014144440045200d0781942031800252403240e0040500340e280c0500c0c402c1d07440c0c4251145802c01203e02c101c4805c41148040110710341c500c100c03100905220170405117580344a041410004001c8a602d03008455119036410090241d03081c2446030703056062007540204882c004016026111050b548401400200300245d4144612 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 286006223 1250 286004973 286004981
    0xe01090213030c0f090b060f25061406090603121b16060f090902121303030b040c0207171207060b0109091811030c01201f0509060108061006050a03 65
    0x980c001c0020626181c4031384180c900d0004034481c07651054200b00c50381402d490610111003c0200c2d1401e4a860460403d13010741c440303204409519910304c0c03030302c1030400800c440d40529100c0c6000c01603e560b01b4a0031004001c25950044c24240c0030303a00c200c40010f5504401c00447c0d80f0005414496807550f000f1640c0d05141c24503050350b0b5444034070048800108640c0000c3c803050000469262503807099100c0c07445500320b02031700420b03e40301340003940840c65891101c185101c8050007840c0c0803665039489004501555411182100180e010180c20040300c80008103900400c000303200a4030003001c11011106142c084c822000e440c0e01d95505210905070f024106140003007100080030302070450269941d1801001c0303007500f5030310020350a12145045c41c1c0440c04000c1c111058640c0803148020001003261421000c007050070b1885083e0b01c00309649020400d608002a1035500410503240191502d0700300700061f0b00040040d840b01d0144190000352000c20b00c150f941a00d882d5860b0140f119080b4090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 286007473 1250 286006223 286006229
    0xc090c0702011211091f0818120a030e19050c010c0b010312020a170306240a03090203010e0a05011b110d05210112200a0302091812180306010e01090213 67
    0x100c002d10b821071800d506501c03200200c091b5448150f41d9a03144e07405111840d01c00b5007109040c0d00b1464400042030410000f50140402515001403600159000746203480441c141d816640701c4d8900400c000c00904204040941c0400e207043c03204a81030390b40343c07000c000060100038180d40c201c00c41820514400c0114980082c0c11100c000380004080340070b43c206500544000b4064401c10122490140003a001038911140d108800c41c0f8240380d1520490081854a1040382c0c1552101c00061b2848401c1040655440c0100000500c001849007020ba0845c0110b1400b020700230480c60070081c4502c0844c07980e55012907400c0107584c4080c1c80018060000c000000601140e02ca0400401c0c40b0100d17104110015100306c0d0502c40d080c12070000c0b00d0800001c4d41c0030551200c580f0b0800c1c001801c0c00300c12660410880180e08900340ca2a603596400c1501ca014100014100820410140c2500c400d03846e81d045801e030042d00031740d414401900d0f90340e40c0501540c25010340018078014040c444582103401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 286008723 1250 286007473 286007479
    0xc051f031d0a030908120f040909020d080f1209060702030f180d08041d16110c060f091c0f021e0a030302030301180227010215090c090c070201121109 66
    0x68011403038041c4c51a0818042d41c0745911600f0960500c0303403594400c50749501d8020f2052824a45001140710140c09410000c0b41c20541500d014070014800740003500070042c0c00d6042e217803141c21810b555588424010a0100d95034410310500810503008011110b010381c00d45052591005000c04a0b251401c005c2e00c1c40b40c0010030241710409100030f40010b4800c1d035500c03030442a4550381c0304003074446220341564800b4032504c2070880042d81b02d0064503440c2224210703100307a4071454040000220650811854140c042c500040c41e81850302e40150070b540b102c1c2141042c60711040d0385846001003124801e00082c00781122401c00760441059014203603040303d000301840c6006449283c0291a07030030a00c507058180d010305081c0303040f40d412070094980e035510a152031030002c4020300102042c405201c00282c194010b404411002d10b422082880c07003440c0e400018062800d948081c13012072a03004140c442c2c10310081c002030006070b9000030a103030080040300340419010b0002c0303074041c264496100c41c00d41c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 286009973 1250 286008723 286008733
    0x50403090b0a03020304060b0f0a050105210903180d0803130f05030c0d0306080c010c20030f030c060a06230604051002060402030708123109090c051f031d 68
    0x14200f0307415001544124402e000c1442a92102010b0007120382824007d0f6611100c524814801948160083d018009001c0d01420b8031450400b0301006554040d607a44116400000d43c00c40840b2210112211400c015903024000705ced51900c0e0040d00703000c0540104134a04004001030300344411203000c12541600141500d64560091f0801e07661445500e00d0440424203100e00020040004a6940c0300d0300410b07100c44442c01e0700e5a0b1495261011030b03d02015006800343c0100c2d15840400081e051852030070021540c139081010136030701c1d00800a1140b10503904150082c020341c4c3d0815080c192200e6035180c0e24038050016030002e440381c022500030035045036113203407801c003007603070002e51540076900035800d403002c0f41d4850070403a8a81e070785c1c052440781c031880c20402600c00159400340800e44040c0702114503048034007000700c000d910728560f002e8900d9940311800d01007400810b4881d400140300485860320b2000440382c540580403500140c8038245584e81c2602905800b00e009050390400c038020642e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 286011223 1250 286009973 286009987
    0x30a0b070f17011409100f0e040c0b13061110020d09110a03021023040f15030504110f130609020a1d0307051c06050403030e0d140d050403090b 63
    0x1c1c81c048000c041c03200010a21001003614040403080241a104019103c0d4100b44403001800f002032009007001c11034601c41c1000061905001d010100600502941d051490809081103070089800d600300c802d20203000c002081d8400700b12903c12040352402d082c00404190041c0c141810070b825400546000c030300004104807885803a5005142043c4140e850b0b64924800c00207008804041e400020340015154602400701c80c015200003400c1070481d580f880514802907008140c0303402907408000461070000060000c81d0107c200c107080c604a6240c200124906900c03032107081c0d0100741126014007002d56401035240c8034001103400b000c080c007509000b4103644980010003907100811180c0003503e10308014410f0303034149495050108008008120f01400c0c9001c101850132001d0020101c0c400d010300040010700c07640103862140c0d0003900c002402060040b8013908107030003107610508100064444d02030284c00e0405a90240c0701540001856544178a0182d807600c41d20303044070b60f40e201f001c5058 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 286012473 1250 286011223 286011227
    0x3070507080309010f080c07061805070e0709050d021008070311180306222907030507110a21020307171305060301050f090a110d1b0c0302030a050702030a0b07 70
    0x410f00001c1c2a0380b12103809251003021105040190345940320004200100b01c08560950000d8a402c41e0900003030099480c07d03a51039140140503445000200700d5441000400d54106007400d0007410140c440d0070003c00342d540000d02240c00c2e518100d0a0010100100c2d050510942c030001541c1801403d40d6503c0c225162000640c9510f801c03114802c3c4a0100010544c69500001c2240200b05202e0300640c00626614010300107102d8400121108419140c0d101c69206111014050f288933100000c00e4240361074000d040440700c507404041680060100c80000d03401e4108220200b104200c0c860343d000b200f0200301c0c1107120303246002d40440381041600c0d41c80e1000f640100707030920410007c0440340d03a5030000d000c0180024428190301944081c0080100e080210005501646518000602c0c3d5903a100c1c0035160307000540ca21110300d656002c0184590041c0d04044104001d5003007541c2c511840d540c00135680c2c03217019142001c10001050781821504d00b0404082000c0d840030401c2d05900e069040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 286013723 1250 286012473 286012477
    0x510060e09060a020c060406020706020d0501030609052e0e0106030203121902010b0f010c11130c0e06090f1012060b0309060a0c050d11070605130201121a0f0102030705070803 77
    0xa800705078018400400c3c20640d10b031089440307025207100600142c0e9100e443d810f000390000c01c81070314815001c10058005580d03502c19a40654821000022040000d06240b8940700b4a40d860b0f0714114401f044000a002c85c11401a4024030507900100301060390400035030242c402a40001c1d01442803c0318150f03081040d00107084440d5221821220000054000300c0c02c0e1400100f160707800a540d0401407038103521544031181c01074080c00e04c0103420f02041001c12955441c0c0e03007040200315030f41c1c0c203019021030340465140800ca00440d105800c041211001450610700c404103607111b84403911500c94680d004012001400c0c220080412415650764400c500b2984112541d00040c098040099035400840c400c600c0142c4955a907541059400c020541c024440301748403801e02c0d1800c2c003d09001803030a000d014800c08491080503026034042c1b00140003400c2070403980140504050181c0c000890300c2e918440820001c0f030300480040140701c0142d0452140303080183c42402909004a0100780003c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 286014973 1250 286013723 286013731
    0x27010e150412020d0806060c0f0f0c1005040e06061c020f040303090b07030206010306050601090b0403050f060f040f0602090d0501090c081011030f090f0a0501140f01030209070c0510060e 82
    0x280b0300140750351804080340c075035906090480104041c0380c00f14109003001409070007284d12450846100d2a4042030703944c90507140f1210b0404540c4485810041803c1400080c40d04d441d06052950916003413001d0300501c404020718081c011240803038a50005d6025284500b92624410011580e40300c2010f05010305512500050300440e0700f01200080001844c412260401c4c0c16502a001d01d909503a00e40010300009040030341081010500071649142840041c80110302c103200034420210b00e0340b01c0e01d09016005204903514027030360041001285011640b150345981c03128006a59550440010b000c0d025030b00800b6005602c0c100c10700e0200304a454500c01590002030803034450100c460340d80416281080140611804188045114002452501034014a0085c1950011468128098602821804141c845079115024407101e1490182d07001d40000c0c141e40c4210880d8199008582003c802600d40402c10503c1110b50050100901046851008a202c1030007803658800103110070000651f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 286016223 1250 286014973 286014983
    0x90a090c032406050109080303040311010b03030409020408010c020601050d0803040602120411010809490519030204030c030b0a0b030615040513050601050d0302010e1c02011427010e1504 82
    0xf02c0403072590300a00103103003115044c0e40210301c1d69544ea94100d4000c00b0507610700d0699034903002c20200964040c8068005070606000c0162a85e1a00314103600b580c034045028400d542283c00140324548603c034a6004683d00250760a549484519207000203104864044007118030000601080048801301c0c480b940500346e80e890b51584419811544510b26a00f503100000c000e10817402c403911040765144194440b50b060409031443c0002c90249a42000d248140007403000120001440000715200e41c2c81d22083c074046083c0b9055070307540e0206c40c6460001400389030000300081d00141e03480d00108a1701c500501561800d00713040880070300c02d80c40032000b1441071f41440300051148040e80400040070340c021008003450791034003044c000303a8100342c034003a42155210f0548550807403080120b404d40400003040460400c4070800001d0031500501d4814043d504c0c20014010308005c2030b04907403104d109850350201c078608281081030040408600c0d0031402e0040c0d82c107640d00b91000391020351145010ba = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 286017473 1250 286016223 286016231
    0xe04050414010f050f150307090216030212070803190207060f0c031802060a0507080708031302010905030109050d120f060b040501081003031d06070516030c06020705090a090c0324 79
    0x15000c0340f0585204030740395403400407a00002000144003126000c007016014050751141c0352035510540c20392f4404006c007031102d0305488400c010140d04128000d40c10310401c1800d42050015503908101e440064118610320000034401014880594100d980c070030750080341003210541c403241c03a01c09800302420710300c007083ca00143c0002d0301c09806401400203a0081219160004500080e603454206403010340b40c00320300340b19041c000340841008500a01c159800312001ca1802d1000500c404100c3d0400390190741230005120000e4400101880302c1c41c10b40c10040c802c0e10000552000400020711040342c00e0341000340028891100e0780c0100151003007a0381d0f1001e550b13103c40c11240c110440384802400160810109e240c089c020a250b0b0700454802010317245880982e0300c0c0c1c1413421050201000b00c160742d0b8101001046048900d040041003940041c041c0c0e54075084c001030303400784001d00e6180b150f5160303440003040000b0041d034040510381c4a00300c68201104810310024015040b03403032204140c0380c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 286018723 1250 286017473 286017491
    0xf130e070b07030e060f2a010b010f021b01050c010908090f0402130b0d0f1a09180a03050309070801020a0801170604020607060f0f020a030b0a050d0201020303040209070e0405041401 80
    0x451002c451407581c041d240d107a0443c4c208401e002e520b9000901c1014031404c01d11032546020340344082804e900f1f8803480d1020f004070340d02e1056421106884102d6042c00f000c0f9030280d506980102d5821111003a603038051210700300d41d2005940605c00c0c5861503695500e005102c00070818418081d0070070f00c00039070f00011000000d200380422440f071000a18900414950b04000304c1519034010001c541103580080b0350548032240c42c2c000e55035590903c0c40450f2400080c0005820300603096640980c0200c02d400c40d6481a00c1456202c9410140103410800c0010000d1043c0344204580c4004200c800c1c021596503841010040000b0400c0c06694090185186803010381c200c0001c025000790b80040101d0f10303018075555007600401b0039103100d80f43e5076102c9240284030b00440c8041c1c9030f00c502d00c4d00c010034a09008030402a00100356041a845000d95051460140c0d030f001050300d902685c19030301c80380765465010094505001001807640d0050820007040100070411102c118203003000d0f0024007418034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 286019973 1250 286018723 286018739
    0x70801050a150e040f120c0f0c090513111002030c030a0c1401020408030a05030a0e1617030712200105070f030e0c0f06180301090804031208070e01050304020f130e07 73
    0xf070280c4001d801082e40b850748002040c0d60002e0350031040d406041180d40551140daa01c544980c3d05a41a1410185540708005034042409625841a60482e80b01510300865a27045a40d1803074080650056060440c2480d4140c0208211600c00c0c10380e100b2243c9070548644000d110712107106040321040140401e650700004c1c14002e036004d561040b000395040102d16403040b0789a0300004d00703004580c0d464004842d04c401c3d0900034002d101c01010b0581c1d06ea01c1c1080c00001c0f98000e00142c0c44c80b241e0003085000c002c81c41d40701246000014924201200c0e10342455084e0704a4014095604154071302003e100f2040d400c030881d02544059038505000b022641030042e80ca400c42d400181c1c1d00000000d490031041e1420000500d000301a40100ea1000340e60000400e007102e0700305c68200d8002c400000d041c02805442c080303080b411344041c600500c80e49400000200345074000e5074024180300b40400400c0031552450b81a017000c0c000946984000e4801c60030f1000940074506094080780030714040403407041c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 286021223 1250 286019973 286019999
    0x70503030621071a0405120c040c0507030e0f0a050a080303060102120301050d021936020f2b0507020a0b060a050312030c040e010b070c0503070e01090b03070801050a15 74
    0xc045030090038100c0d26040c0f4809044c030034003401842400080201052964400c0048001141340070024905004801c09000440700400440400c2c0320f82400360b600041d40c031110803143d034a4107480c2011200c0d5440f003c5490a01141c0066034001e07c005000328a6000000c06107209841c03d0303084a80c0202d6482c1900c50782d11081c05a80d410909220840c0e0150034809012a909071b401030616040039914030f401c6034014600da00030307000001400310218100c420800080315250001408610f410700600c050084c51165412900140301400040f0480194040501c0e00c0384542c1601484980360002c4000d440780001a800c03106070307900c100880c01ca824034140300b10507502e01500810880302182c10f060b000d40c100500049403d5401c00011500c4201030010302d0081c40e10404e032a4940c401841e081c00f0914076600282e000381e0008204000562411034690704403206a4400500003158101003414000300c1c1e04910229800c05090181c101e803668403080300c003005803100402e20f03911089054924 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 286022473 1250 286021223 286021279
    0x30c370f08150a090b13020a020705010806060406170a06030c0308070b0901050417070507080109030c0209090d0c02120c0d0b0109060909112b030c03300b06040b0705030306 76
    0x308000203818050f004c16540300300c1032032600401e0188120051508002682c2c851050030005801070b2000f0441c558005507060f420002c00c4400604260030108014807a0003141e24240d0440b00c00400704002c125268480310186401200c5a1b410a0322424000b146503c030100848040c2c2c400800110500c006201305806141e01182420880c1d030b02c0e803c0c50300c95401010b001c2d076643c013645100242802092203040711161103510b41c076100e0b0840d801001f600c12001080e01025400100d8004500365101c08440304c940e80c103c4240346654218444907142081810780f050704404007011800604c0a00c10440c1e04035054010203103c01c585a618040c180c0d082c00c2402820415075210440d900d06d01140d54902ca640b5001e2a00c2c0c180d4090b041b582214190100700390701082034030030400240343c2d2100d005c00d103c8801e403c20308a0748005034103418100d0a90034400d4461944c40400c2d87c40760b558902201d00a054040031280c45a440d800d105440c0c0e031095400c41e20620800d445480403a07440c01c244912 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 286023723 1250 286022473 286022479
    0x102180d2f03060108060405010e030301030c1809120c050c010c171e07060c030507080126010e03071103210304080d0906020f0a14030c370f0815 64
    0x1e565480321181c000c480007107a14880702001d20380d480940d032410002c584c02001c400b03005100500f0282002402c5541030150310503103070010001407002c1a40907207914100c440e5240d0003043d810001000710000c040d83c2e1401482c00e40d400704480c0000e075120b1650541e0602903404e032190036504074019184881c0c3c204d0005d00140300080c00c2e0001d03548000152448004048101e0046280e8584142d49039110401c2200c01075691071407000200c0d898415680d0001c0c01e81842011075040131040581e24221080c2d004458100100113040c01c00290041d545c0840f50004803500c84540d85030a9050300108007031139000c0c5c8680f41e02c3c2d4ec1c4a84441e0324001031940442d5103180f66841e291a03e020580c06030305a0411940c80303d0040c400a0f6551001b0144000c0d004095a290f09003020300410001c2d03142c2c3c0c0e0090042050080c856004402c104440507181240c800e402442c00030081180554910098015049848030742034100c2c54000804100c542e03d0b075a0f0f80c03c4c1a60741d00302c440300c42640e2842c02c150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 286024973 1250 286023723 286023743
    0xb060103062601020919031106030f01232106160504230d030305160801081f110708030117031905030a0b1f1209050c1909020c0102180d 60
    0x201084a601098002e12500300252624010310003085082001d030182c40e000080c000010418042d0840d05074140c03208c11110146103082c08030b55000a0301c1c06001e00c06c9568040c076034645c840d4140358900d10700460090016410305030548880d9100307040034041c819160003103500050244d0007080d1500300811803500c0345800c10b030a0100c074514154201202124074900c001e400d02440c1d0321102114881407007541e0105482c6401400141384804012000b000e01c515800140802c83c801301d050710004035203000d001040480200040050403034401c0f403a07180e100010b125002e100c2060700a50503039000d4210900890300e43c0c4140c0d03a40384105545100980e5802521492140c4030380002d5411000b0a500840c2d070407281400a2020807052803a440480d10f01d45824042035000723103c0b01660f50001070208500c406540b00c26445400e229442441410381e100d109520300548400d12000c1c000103c41152100c4509038464001c0d48041010280d603034840603103071032a20b00145100b549540c00003002c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 286026223 1250 286024973 286025009
    0xc01030b03190c0b220509060108070e0310050a0e150c070633030b0c0f03010302060a21020a20030d15090f090c0501090b0f09010513080105040b06010306 68
    0x1c1c01c0ba0a120402c440340d0481040000b80740d01c00a01400501800c0c1d142041c8100f05140b8851440c00c2c20781c05036010f4a094801c01034541e030003013200c541c44041c41c1000d03100c6d1354030140001d0070400e286104c030f8015407400040c0001006e040c1e1026018040200031a201840c42c402c440300005000c44692118070410401c81001504036007181820003041010301820200308208813400c408840c1001c162112141006c00070300c40c0c01108150090003604006240c09050703000401e4a10050001034000e40000918201b6948500b003018910301c40b942c4203401405205085202a5001c0c400342d000003918407840c8170000c02e0504002c14500d041e000254a014500c0c01b09101030070800c401844038000d80a400120705803240a00c80c1d01c4055403d000510036038074a4007001c00502508070604000b0303912410302001c001e0308112070101180d2002c032910b1b40891001200c0324403603210250a240e0250b44c000902c0c1c44150009030066119003800303a002d580c2ca000440440c1c0c4903210380d14640301061854 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 286027473 1250 286026223 286026253
    0x30303040203030d0f1d06190209030a1b0302090106080f010602030a0c1131060906050a050112200d05060909062a0417120705030d0b1309140c01030b03 67
    0x100300143d5005d0030114401800d4080841106008000b820064003e001008492005000c0c0103a03183c207080e40460601705001c0110b551814040c0c40107200540a450301c107100d000d160050f2005640c001c000307140c1e96850742c2004100c5002622078983c08514000041502400441070f182007194540c0e030343c0c070354805540300c000c2c62212541c1c02c5500800c3d108600d069908036005e0070148013006600642040203034410010403031f00c859000f011054504101440301f43c2c0d46030340ea00100c480910b0100150b41c0421102c400400c0ea810445560354240034180781004400c00c0504504001c2540c20041940c4800600c1154030301207a941c0500d420410004400e010701c03031601c10441c0704005026900070bd940c15016180d0380590094500020034020780111000100031882140648007011803e22200e030791056903134000c505204a0294035101801100c0e1510001c0c1c0b0069600c2c101d0034810511682007203020002801c40c0e061050145689045403540203000341c4000c080007800814411540d0184 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 286028723 1250 286027473 286027481
    0x20a0210180b070e0a080c030601050d051507020c040c05030601120f06030b0a050a05090a05030a0516050d0807030c030605060304060209150c16090c0e3a020906030303040203030d 79
    0x10411030810480114081411005003d1042416807203540e1110718460401c80c03000125484083e096100504c8111b2644005c228036045600584031204401c4040c0340c0a803c00c07007003c3d043c40340c001c222010440090f074000354032961520180d8003005801e420400031038292008032103e601041c4904150341582c0101d0340030140000914000064290722640c42d14590f070700c2551401e6901c2e8a66040c015206068402c6542000d0000c009140d42101039a601da00c1e0b000702c21342101444004650601907c041b200501d000d940e0080c1a107000c0d544000300540480026190140000d21304980d58034060f01a01c22030041c6c83c0e0040400f400c55640ea9101d101a50000c0110758004095a42d10960190100050200c1c41c00d42c002078042c050151141c007450008580c400201350307044c00b140360b40982d046218030b20400b2050307440c3da0070303000a6028035112501429003040c00400c01c0e5174205181c1e041600074007010b4800c8403090095190007082661300e0200740d50195164004004815100410b0341c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 286029973 1250 286028723 286028741
    0x303031303051c0905010b1c0303090203120406110708030a0905060706020f04030506011712032202030f0c030601090606050a080415050c070201110703170903030d06120213020a0210 80
    0x240041c9420007000180300252100411807010070389413002e460800800f07000d106804602500e1150803540d40180c0d5051882c01514081c00341682c400106081d9203091040020b02003500442d50f903250f503100c500905902c40002401e49034083e039000890954000300488052000c99036910314000d0a00f001c100f00c42e4041c48089a01075400c01c0001000c0c0948030150000b180544003600c4558035000c8650055004000c0460031500621035250684d085501901e4000190314490f540301c10701c4240c6002c0103540c0b268080e506110b00100f02e0001c00002a000c81c00c2c400540070781e00503980e502c24100030b9400d6806150049a8180200c0140380d00c903400c115801401425032002002c8080f83c0c2d60202d940a80c0c17201c0e85000001403131025940c11400001d55003900310002c113251461a219500150b001000c02c8100500c0080c03038a4142c0d4040041c3c480611580c0720402909a46042007040540c075142e00b203000707180711381418400440d94800e84040744000c0e0060124100e0807003860004212802c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 286031223 1250 286029973 286029977
    0xb180a020a06260c071a0f15010e130605040b01020f0307080a1416060606180e0a020c150702060603150a02031306020703170a060f0308090102150f070f05090303031303 74
    0x1040f0010a6040380e096801800092000c40c3e0342c031024241441a5207015000c00c2083c68000e09128450031101c010b00c0d40000780c268401c1a030f00071000101d40c0000c1507080e0603801b42c001e0f550308130031403100d0340403404523503007181c0420002414a00681e240d0b9030880b050700c401d400501c0100046030200005202c814864503200b15140c1821070030f02c070560040041c0c84912300c0c0c40e111000401002d07201e900060045810541020b4240301c0620640b0f800f640a82c1e084031490401083c2c6140d003e4041c4c034000d464550035110528600948680059002c8444400602c1003d011549504011031050402c0507488e10ba00656540d14006401940c03026203e1070405040a4050340803501520103020039910a0761840324001c5083c065540401002d0084890586004002c010f01004446140c089960040e201030300ca02c80100141d00b0101c543c44031005d05404102003018018107803041c40c2c85400329483c1c2d580c0c080c40f4080110783d0b40c09812052a09540f0820100d104001d04103c1c07543e40612034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 286032473 1250 286031223 286031267
    0xb030705010e0d020d0c0e0708010b07081902120408030306090609040c06110c060c010f0501060905060d05062106010810020315010c02030703080d0f0e0f070302090a0b030105040b180a020a06 84
    0x9a40c1d01c1b41c404019074412605059581c1c2842412030344100801d0040a0491686051800940b03070382c3d60301e114405091403c3c82c0c1d0720240e050154020302c24401c01c080c2904c0d40944855840e500a6142d45c82110f013075100b442c440c40050101d14090141c140166000710358948a85e0500303d081c0c48030080500128682d2191015001d8591349440050105103401000828400300c0c0444940c2981c0701038100105000c80f40c401400075031250f0381030718030b81c400c0f10341c02042c0b036280c600102c3c115480881d540c1044070018142d01e0961900012414100c9080d1811100701080c1c05481c00101d0109950030602c0c00540000c2d1041588140d02c0c2c81101030000b003daa40c166581d545981080e0300c41407050102d03513181e009242080e1b52030700c245d542584491014040340d1141014264548101d800002d11840062002c21002c00c1c00382d0214a01a03005002040281410b050000065030103c0e1944200c003036202110300051808070b0590300e05036025015801d001d04040e03003a1742e840200181c4101422007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 286033723 1250 286032473 286032499
    0xf070c150e0a0c0e060d0302030d2d05070801060513091e060f14011d04090515070e040522060b030a050106030f120207180b062a010b030705010e0d02 66
    0x40c0400c0c002c00d881920b00015461903c0020002c0c20401400548551045001c8001194001c0201c0344a03150040c400a410010014840c80781400f072148003400b40c0740d40051807480541c40e0b1059000d960b2540355100729a903142412680342c070500485c90700c90740840c030301001910041d802c079007200300904400e00c0c0e000c148040c5400c01c80d116030340604a103140030b01d130800c04481c500c4090099480280307001950100109008140030b9211b41c0c0440c00303503a9460084007403000c18819140020114244c1c0000c40c10704c008010141a9a2854184600d2400e4086500c0d114031600502c030f180356a004030703008151030343c8a0200900783d5040c029014010303010003100246080c420600a5840b13000e100490901e5030400034503c1084001640955200d0700d024401d0302c00c140100c0440c0c0491040c04205075045602042450040c0701c07100c00b80f007035680842c00301c1c41c0c15950780c584191441802000318400140c109540d030300181c0b00d40350204002e00f04007641800d00701c0740a9183c034005880032011142c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 286034973 1250 286033723 286033751
    0x30909150902030f16050a1b030c02061306020706030e06040f030909090b0a140105011b03030204180c02010e010501120303200f1305040501030b0126030a0302040303080f070c15 78
    0x8002c40304140410f904c0001c001000c802540c0c40c440c8035109103000b605001407244040e0918041a4000c002a10051402e908240c03184d44000221503001e095242c0b40c00c1c030801100c10400b410300902000d030207202c00c00300311103209104003880c540d9024024003d03a1140e850b100c0c1d00700004903056041100c10742d400304408659000c0d007140140700d0240684d441c508000800708445600010901d0a12901c004004981c0d02065013450720f0403880d529400ba80907890150028440c0303038404030400b402d20304048048181d0b60300110082180d90001e0040f10190350201e4200d9074240200c040e515040c000702c0b400700344a544480d1012070101c0d007428140d12407100300d1105421a0780c0c504120000002c200d80d4070369000140c40e0007020260340512240d41150f44880001c50140201d5100c40e05001d0702450320591180c01010115010341078980e210b0f80b07000020081d500c41e0200760007040102002c030300c0820b14030b402684606590b43d103a48403540301d0303a0303002510b00c41000040b5241c1d41f10720840384021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 286036223 1250 286034973 286034977
    0x51801260d0f080a090b04080c031c0911040e100c05040902030108060105011b0b0106260405030301050301060b281101050a0b04110313080313050f0325030909150902 73
    0x419542c880324071601d40389500500c0084003c0c24181000e00384a4544006418603070040d03086580102034a85404c20522180e18601840150810300c0c5105002800302c4516580010b69050003041030380b00d828940c0082c001074842ca004004415800065589007140050303000b50200c000300c0c90a1860b1981d07031100c0c40c00740d0300281c01001c8113410a0004019960304000030f4041000c484d00b08013000211512502101c0301d05200300704c1845146004070242c035588401514641203101031580c80390034241052036403038009018282c025880d044020a00b010640145c0303000a50125816000241c0c204241d0540244180380ba01400500b59000c018108280a906d1199011120008065411358100003d83d034008a580c048080e00b0005c0c015060303030303024581c050960440341c1036540780c9402400d50040400440c0240030780c060000c44151000b0080001c00c180ca500e0190354101180c42245200b480d5024040100864009102003101c100c40f90010307000955100700c1c007444281e07a00c81510903a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 286037473 1250 286036223 286036243
    0x71b05030706062c0411060702030a050106032f0d060212010608100e070c0605150d0302031305120d2d0203130b09060706200f07030905180126 63
    0x35444407414040d45001c4d200e584030007018241e40341d6008440780341c03800300d0500240c8050614034075040a0902c0361606000c9030340e819409001c5503944000d5082141c000d290301c4c0007c8904a0f40e95604008000041040464110400103034039500300403081001240100c02c082126055024001c103000380310352503640c5000b4441c40d201e4408511349001c00c1011b5903003a400124a90700500c05102229a02241c0300c140954403410000707035516624030901c04c84202c860020340c8010030381d080e0b00c101175001c800740031180f94031080c4240d641e80b20010010520000701007003090340d0010010103110b038401c007a500008042121012030407048140e006298001c000187c0001d03074400600242d0400c50070302d58500802c10056154180256400081c20b00e02c105e00015049036211804102461007244500e802c010713207103422903030700c010002c5402541c0d00051400d03000f003505a100045c00381010604640e05908201b0100d00c50303070070003401e4003031800d8440669407003c451440100400318100292991 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 286038723 1250 286037473 286037483
    0x30a0b1806070923011101051303030f23070509040603030905030f07050f100e09040b100b030105030a03051b0d05041a04030203030403030f14071a0903070209071b050307 75
    0x404008400c149140030800340c501000c210340003030f081045401c00400c0300c90860514402840300c00d2100012220f10b80307042000c0380f20354030740801d104c0c0400d04a203079045914820340f1b06200b40c2d58008005000c03114141c00078601442e00c0001940c3c070302c104900240d4020418200030741401d80401c04101140d4054000310089817014000380154a0300b0003600103007501120040000d01d00381004215820001101c40d0300500a034000b907008a0301410b140b070b00644000d00403018a00d0142092520002c05980c091100586d2400100d13240c105c0c1021079051740d0001c0c00800070685160303411985a80420402d0301180f00030b51009a07480c1e018844810407413610b0782e9898503641405143d1010b6070549a90b40d5110030104800c00051f280801640d00712901400e044a102c0800c1c82d0544140c40544914280c0c900002072801c01c002e0310100386a10300c40492a0f040c05941d80e1011941c3c1c1c0e105422019620500c1d03100015841c522550500c0881200841401048502c0755901440d60300301c54006c880d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 286039973 1250 286038723 286038751
    0xe060c1005061305070e010503060303070b13121e080a020706020703170105032b11101b0305010e04020f0303090402071505060901030201050a030209010507020a06050a17010f0b09030a0b 82
    0x162918143c14080c0c00c03000394607001c11550070302c81000742c40c0511010382581070140100003d045a0380900550740416000009044c036403505852843e0408244042100e81008007840c0b9458a886046c0540e42901c42450624a12544113010b4802c90401042000203a8082004000081c080c1c005095058800d0b1108004544c3c190408200300c41d0580150f40250712000d9009800454a1a8150090260201d2015030703032210000b222650103a858026440c45901074048103a141c65111840710300c00040c14650311000740d0001c80c00d903a0207100303417902c45c0c084502250240c90124240841c5d200300070112454000c20034081400d0380c000401c1994107d14030040c0c8005140c1c3c0b07015140e8040012101604950b04550000c0d045004001c907620407d580400c0101850b4040c804661180360020b00b0000c440340c0e01d64008000781e00011103940000c00044040c51020900781c225810380300116210901c07542007000001d4180c04c8250440e916104021000c40410720b8200c506019402500080c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 286041223 1250 286039973 286039981
    0x608270607080a110c0a1106130603111306210203060904080a02070305060a1a061e070f05120403060c020105010602030904090501021204260702030c1e15090307120803070e060c1005 80
    0x3a2601c4947c02c481d40500420010fa480142405040c0f5060f100d0070304000501292030103403ca5a4090740442c0c032480c054034200450281d41060400101c0c1d00703549800250a42100e1104040c2d000686145401c0051040486c1c00202c07400043c0516140d58030441d801141c0d00e403100c0e80740c00026100e0039001c0c0e940c0e501c2c0454643c4801303440d012800003a14120701d0010380c0300072000900c208a040c0c2e5595107000c101d840811046000c0711a0041e044011503e95050241d0791b090356600602c0308444076450300001c88500b50060103000c1c102d5160750050350400345044203110142c06168000c440a56003080040000c1d00d0b03562056001d1800f501c00c0031400c031034101880c1240134407021400303011041403102c0b4006a03000141c100303140f6805d4425090308203022030303020100540d024000740d01c80302d180c0c00d0107900c6000320090011560100d00711031a0700d544102d60000c4002d642c402815503801000068800e6000da10110405400034188901c5c1c610701c1c54813542821072080c4012402501d034010301c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 286042473 1250 286041223 286041233
    0x30f050c0c0f010203061c1707030f08010806040f0b1012060209040e030721050f0c1005060a030203030315030327010306090b0904121101060608270607080a110c0a 72
    0x4958000b046000f189541402d00c0020b07110040c40750f0100b00003400110341c0e8100700c1c2d90300b161500d640341c4e000200d4039070525240c09000380c11003400c05000142001c00005001e640010041e000e42d420416401c0c00e01015244c4c4410b600c0c00804642e07141020000024032890180b41c00d0507820b008072001038139412101d080105484d00192039100390fa01c244511fa021404104003007109000ca4680e60340419051300050b070790741c0102000c0c00d40b028004103810001d07990200d1080e0340d01c001c2c482c04001d0380e80d50000f000100c866a00001e5090307802400080c43c804076110303c2014000004044030b0400d000325000c1424a0789800303a12403c041c004c50b915240c0c3d41c05003d103801402140e41d0a018847ea80740204a14800041020304502d51040007840110b0040c145800f141903020000c0c05259141c410260041d41c0c10f4500c0b86840121081015200043ca8034440e0352076a80c001501c05522903810488682c400503202030300c80c0c1d42e03c6034008005c03a2180000c1c14005103001c0604803882d072034100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 286043723 1250 286042473 286042483
    0x915222009030601080d0f120b0d11090105010207060203070b1003020a061d041b080a0b0901080d14090102030405091e0a0605030c030c0a12060e0f0715050c0a0b0403030f050c0c 78
    0x1060740541c1c008412009080c7e0007013a451001805403600f01d0103a0303000c0a08901a1060f079004603001040354a8960a000f110100003800d0032058480a500d6680c1d40012691220144603110058009001c5007001401d4401c841c0c0c0c1265030346454080035600e940000d082a80217a11401c0451580240c20010201c20040c41070100b00407101003001a500c100c5200c003494114090b0001c10106c0340c00280310040c1a0301c0121003a602070304000103907864900c100c0d51a00304402507004a2402481c003801c9081c22800c0790803419069000d9418030f49800240a807020b8044c2c0424280d40f034080120501d07480b50740b401e901c1403812700c2001c9000c0c0e02e060103160030f0205108a10340079400000e81078040352a510003040440c1c0c1090300c02807020300302c0e00300301d40107001074400890359000304800c0c0602460002080c20070359111000030b060000d09a078040d42e40307201c1c40040000a4200c00003e1001c295521340c0f03154060700030704012070019185440381e0f08481c021200010201b0003c5802080c480003000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 286044973 1250 286043723 286043729
    0xa110109121103121f090501050607020d0512030c071a0708040b0a09140a0308220609080f030421110c040507090e07020c0915222009030601 62
    0x300204401521610025006005240c003481401c0240107021041041214260324600e0095082402c10b0340c1c0a5580c2540c0205d1001d604803a01004540d0324202c0c41124101c07400103040901c1d02860b907080c8903903049620b10a0714940920b01800910208840080d481402d14102c05076480010380b5010071115036408051905a02110400c0711030764100105a80203900400c01303038400d42c0ea0100c030b1409865418401015004011041c5d03c8000d00010410140d61007904c84821030740c0e81208803a8065149030b009107110244a8607240400d526901503003046000f800b0301c0c0e10b8800c200d814020305502c00da0b402c0b14002051010034030f42c1e402200310a40e03400f8a600e48a41681e030751000559880300502081e40c841c607a607a0102e007842e4010210780b4010318060400003d54905420040c0d150500042d1503400f03082c100b00040c0302100400800d80700660028290fa07680360308090031032203501280c01c880c42c4003503075600c81c018600410751008000320320503035100d9524600b04081c5410302c601a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 286046223 1250 286044973 286045007
    0x41401181d0f04020f040504170a050301290f090d021e040605040b2808060403020319051306031527110a080c0c010609060b09190308041707090c0201020a 68
    0x3420b010040ea2400c10040841750120b60100d901d44460030030400a808040c407624a000300040c2c0201389a410901860407a4901e02c018140246070800240342e14200c0300c9180c000b50020405c2d0094030100d038000d001c032403001034400070302c03080c0da40c1c081083d5080180410380000c1030313045a10002c0c80c00d030041c00041c21041c1d80a001a0404002081516030005a081c640c2c0f141c400182c10005080d202c150014100f14085884034100b80c10041c1d103d1303001c8603e1a4807100c940c0400541d181c01801101d070b00754140c1c0c42d059841c5107014001c900401c404590403401c40e0707011200080c4461010300b42d0702c24454500790769a06000c26020281161015802c900354035406000b05400a80c024031150f902110380d0340c1c101c1da1a8006280d0364010300c820b420040c10145017a20114a84140d03c002c0c2117001020340b6070a140e00c4003114944422a100e00c8010300c0840100410300801619010708484401400100c500139911b821800c1d00380c03030b42900340c01c0c0140c2d80452901e4107a80c1c00510307004e20106072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 286047473 1250 286046223 286046251
    0x50607020a020a09110702040207060c02160e070f021617010b120c0103020a020316061a0102061035010b0103060506160204020901050d09050a0302061b041401181d 72
    0x1903400f00310030400e00c0c869040320030342d6109584200d03480b103000c840d8a184c1c014004c5540309854036080008000e16002c5000600c03581991140040c00d41d004002940c0f100e002a03406550f4103641110180c031078488060860103024928164400212410800350241c102d0690382035045490700790848030722916052280d1440080318200950201d040041c1420030f1a0140c0c4d2440e2545040e8914440c0c0c00880d01c20000b981c030024240b107207a0340a03c0014000040c0c0d40c0300800500700490340d071001621300c10420100000100502485200b5815102c188100607040c0f0714641c29070170301003056003110010140d46a82000100390b030b052090201618003201c1032800c0c2099540c0030600ba20101c50000e001d66400121050568060410303a2100e5418107421f003d115079500d440707605c40c201d1100860152040502040002c501280000081076a50380700c01c0c10301e40340c0b420700221845688101c5050044e010ba0369510904400100c00240200560079060144049101c14912000800d0460301c0400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 286048723 1250 286047473 286047493
    0x120711160612020906160804030c09020403050106090902060a0f11030a0302040e0603010608060a150302100c050f06011a07020409120c0c050d030c0b06031f141008070b0c0709020d0905060702 84
    0x2440c02582c0c1212926108000c010002e883d02e0451f030f2046800160441c28009070016000416800038400e6074441c400034443c03103070780d40c481c0003e40f102c646000b9401034007400208041031040001c9518411a882c00d8107405000c2c20510b400c0d07501c10503410002940000d8107004a04440c105103400110a6008004d201d240003900c41d01d400c2c029000c4000341d511030303841c40180401196080301454000304a00d1a59110300c034040c02c07885c03400b241240c080c09010b2808003007035008500241201c08101240b107918a4a4140c1211035004312002c03a8010303030f90f078294004109031030150000503c540d210001e00c01d10302d007001c0d440000d45901c524419041c50a035040001d9100f41c90301c400c1c40e80004541e41c0354070b0750400039050805070003441c10603500c1c000110000c4010340e0061610b03103207181480000c9031a2100c20342c102142d00d000d606034a5100c21006c00c0442d80140c02841100d03034080c1a101c10546031091582664008614a81a1520b90141005001050080d241c01c129540024942c140c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 286049973 1250 286048723 286048729
    0x901051005030c030c040b0f0903010b120c0d061404030314010b03040c060503040303090b042603040b1302120f032701020c060f0c06010b130506040b1207111606120209 74
    0x1200800343c3e40c402c940803002c9282464101d05460140002d01c070640d07102c0c0e00c8600d0140a540207000e803240b0070341c00d240812030319082181c07000d070004500d00060f025038085581804058004108100c03500780c0c0d640403213051f0801c07048030140141d12a5401140c0d5140e440c00f45000c60b281038000300e617030a07400c00900c00003503180e4070484120313162401c0450712991142800d174010b01c030880c0b0140c100c1040c44100000c0164440004105000c0f140809103101d00c00d5002c2180d90008640082114041c0c030f0100d14980c0c007076000380f480780e4070040080445880c1524091708040c4d49101c011800e030b001003150191301414840703019000ca00344180c2c0d4014215440001e50394040394054038024000001c3d1010b0210003402161001d010900c00c0380c425503941d01e000302d00c0317500c0004980ca2032240ba0304041107504d0400f0071601110702c0081d0301814034400c0c08404507902c01c080d10620900c40074018400c0ca41e0010b0141400c081141140c01803150b1410602920a01d011015600280d10401103d04159 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 286051223 1250 286049973 286049977
    0x1031101140a080709080102030a05070305090c220b030304030506040215160b04051014060a09050705181f0e10090605160606170313080c0904060509070b0a050403020901051005 78
    0x10600d043d40e040c2e1607400090f28203000540207040694000810840409a2904000e001d00256942003100d9590384850948a0304034820389a4001d140010001d1170f03e6001c1003007109581c42d20f200060681400c80000c2c074641c0640c0c03044a01d81c225004000a501c2d207049800c1542c103c40b500641303091486400d02c001b890310043c009003e500c80801140612074104a16103803604004002c02c880c42c09203000d0124020201e030454814031941001003208004c0e070040038056484c1742c884509207100f5100b00044206801035498000170f070490300d864030200c0d981c82c107a01d1003c2503d54001d0001c43c1d0b000e10a503100c8080070030f4144821a0400c001803a800001c0314448412401b4441d102c0c1c8061400354082c000079400040c40100ca00c04020410300044000c154841030702e5801990340e075442010548841c01704c0300250340035030018001000b194040d04801d60060108056500454881d07160320030070b4001c40ca0520000380081414030450404e80306050141004881c000c542d196410f10041c014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 286052473 1250 286051223 286051237
    0x8071b02010c0312150e06030a110607050309090c0322120e03010f140105010908071802090612040303023013050a080c150a0e0a030509030a06140103110114 69
    0x8040c1c01c1407003031503c40c00d4000c4c2203100000c0180000d0001c07159107802e403511030080d551800740000218031360f03181c0001d004034801c0e441021603110360445010054282c10800066a0340d000404c05104590340e80f07517640744030300e00c0869603680360f00b0300340340d140b001c3d0034000d07201e00083d00501141d0300030070308004031070f410b500044c500a1070159144000c40d025040341c001c1c143c4814146100c90403404e40c140c0c0c83c58180d510a0b80d454060540c1e9020440d038078607003803003a0482d40d401d250f441400308100e81c00900da07070b070400f51400340340048050900181417400c50b01507001903400700d000801ca11407040c0c4c01c5102c0b0304141c584859001140e5901c0308901e4050030310391000085c507220704e04004003800042c0d49103030441403241c1c0f82c0081160182d1100d01044021440800020014196591600c10241c40139003803001030080c900c5c50b56080d1026440302540c1d81e4140715100e103c60014066002c7d044101000c0f4114403c594518a00140205100e100e00c9050100004040031445501010754000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 286053723 1250 286052473 286052477
    0x20d1113051320030114180114150313021306030b0c071a010905060310090b0f070216060e0901080c01140a03091208090d02030906041707050a060f08071b0201 70
    0x7255500d42d44024103550040c1c2000811201d000c0403038511442c091412100e183c0d164440303071720401040210300c0546002202c9800004001401814440c0468610401005c2e0540c1103408004844c810241c004840d00d02440f400c0c51a040c0460502060228071201806420301c01c1d203042d6035601d242d6043c01420341ca0325070f201040281c02e0000041440c00710b00d02c1e42c0e00661180d40c564200b400500b1044510902a01c124905602c41091038800c1b01042c0c0c0e0010b00303070b04041e22801c107554004038000e00720310b0440c030468015003208009480070704014200d940b02d2869080300d034001d2000000b016484000150040300c500a020b9801007092400b01401003606540d0706110541503000340b00301c4030050440710444d80031504c0c42d071300090128050380b4501c0c01c841c24030f240200120f03942d10a1030a0075070000c400340010071082303681c4a5100884c080510564455548503408201000703d1a400503000401f464117040803141c00a0072550051071526000170442c141146403160184003980080c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 286054973 1250 286053723 286053739
    0x320d050a051c05010605070c0b18010305060f150a141e0c01020c06151320070f02060c1c0302030106090302100521011404020c0a140a08030406020d111305 68
    0x4070b00e162030040c02c944005003607410009540c4508008010390010f41003150786959440011a8242c404801e6503503048007901c7c03424503078650740d004502a00010781082e80010441c0f03040e103000d07603c00ca145100c2081154183e41c8544420b00c005003054941d501a07003030030104008040d044814080341404070b07445180d1260740c4400c20000c0c180203110b40e00c172144540c010407007446207218501d011110350007011242c1c04109244a41410222100d01b1142c600018841c0840c58021000d0310150000900586e100161603820b9004111070350f0010030511201c0c0c10000c41d09601501c1c0c0b89182443c040f1501e4114219810001d003c0d125518900001e0700c2509840c13a428034a52143c421100200000150346c001c45a204425540641d0203000c1d405142c00480d03031480080c142442601c07510b03143c040c0180042c100c151191040c49105180c10130b40b90080800724800b1802c0000254040c901c0b414005a0380d00240340750703008541d10321901201c03400080100242070300031960350a080d00c0007161410b03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 286056223 1250 286054973 286054987
    0x1e030705060a050f04120c0602010506030c1e0604080c1c08031f0b0d0c0306210b090109051905011404080a0e0105090418050610051309050109320d050a05 68
    0x503c2d580074162090140c200300042c00320340c9100080482c09590b11030324400c0140383d1102000d07400c0c0c840031075200f60141c0c40354894280340c0ca404c000d08030b516542000001052598800459101d601580054046902c5410400d0860400d1a44c1d46c45400c9017660848400300903650300c110611000e0050641e035a10940542c025150790300000c0c0003040c5031040c03a540c0f400100b1a0304090040d0725080800300e440e110f00002c45540490174500c40248160403a41141c2003541c60324a01c1030f0141c01d98110b9941c0b082c4000000e281008001c9170810b280790814034140052500c1820b44901c0540d070301d80c045016040c071001502c0c140c15640700120f542000d50720700c0f000c480125900d0140e001003036070141c101580c010380103448181e609030f41405034080d40c540c1e40e51504a80b103402d44510440360083d8800d80820004407075a0702c030840c1ca602c00e03000800e40c1c81d02616040c0b5031483c41c001c10300032225040c465420700091000c84050a000f42000380c1504071940e46c0280840c01121840000e01000141c40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 286057473 1250 286056223 286056227
    0x17030f0406090813080c0301110a1211120c03101211011d030d2601030809010c0f0602120937021801030812010603140109091509060b1e030705060a 65
    0x40c8484c490f1300c44500c502e03a81c3d02d0410740e907500080300d1014000c0d464024010031501070302048035121304040d11480d0004c0602c3d0000c0b4000c1094000307600b40d8807800d00c540b50b54407000710840c0f4003a80c071114003262030f0309029440c100e8080b503644c0805c0644c2d0307410365040c00060700303881e581800c0a001d080c581e1510b00c0109080304106402007415906004800c80105a01c1e04010070801525500003c110040da415207a800c440000780409000300a00b4414030f607240d84503020055886204000d0800c808949949036426130300b0a031180c0400c81e2200040185800d400c000e05c1c1c00a51020301d007003c40c04440800a40365400046031441c1d1315080001d9141503446501034075159600c0200200003560b07681c00c2c1007159801048101c502880700d00c0000400e107109001c2e41182d40704001021a280e40391051510041a84007000c03201081401c18a440c03050080c03003104400c1c0e0051801003002d100e201c081080c00a02c4601a40c5603100039038440c02c613610001003002c1540c8041d52015034076840c1d41e2007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 286058723 1250 286057473 286057477
    0x10b030709050f01032907020609100e0c09092104170109020a0b0c0c0d0501050f0702031222060f060305070f1a0705031b07062c0f060c010c03020717030f04060908 72
    0x44991b84011000c20b0040150740000c089110311401001c0d140e000501e01d40c008141c5503902160280c69120101d03540d801e00d0b01c6108030760080744800480d1020030210700c00d181b03402c101e0468072041c48408a810803030603074440168403200b1070300002001050354540c001813001c2e0302800358040b003510104a480210304108080301d0100c00041080144002601c0c3c0a800b82600311255000200145c010413622703030000041d200100c41070080c0015540d90341c1d0b0082848c0c048442c261000300c65000320794010441c240304d10160740c2c1005002180b8141142040ea140603010b6002245c0e414004108005055110104007200340482d9440396540c007040c20400d18501810041c1c04400751602d265003031402c40090103500303e41c86500c482e443e1170300c103032050b0301910090441ca03030140d04210341100207440c00a05030500007000420180c10003007084c01003400c40380c4038849071011070790004001003400010840d480c018040b40d41054a946803c07254483d0455016000400b02515031031503c0400c107035241 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 286059973 1250 286058723 286058783
    0x160f020a0f0902090f03060609070c0302011404080703020c010906020a02090a0b0a0b030f07020109080910020a1b060315050a03031404090203070323011a130305060108010b030709050f0103 83
    0x11a402682d255540540294080721990b84545001d0001900c0d504001c40e55503c6110300070070038082a1f40b142804d4810414002c130480c11035513544c40306c1074040ca40d05c2000d4056400760138019101e030460303d80039240c0b8882010340b90503c5159070042106690004040301010780c1607600720260b031038600700403014201c1038140541c400c115000103d81c075a4024003852203082040b0b80b01d007039905d0b0001305074202ca81070318000d0300d0341404110107401c0342171468101540c0b00c0700d0f20444e1091142a1034450846284c01c0070500d80380c140403010001d455150240c03100c00d820302d50318800c0c01890003000500381e2000b48801070901052414940403802d0120903540186400c00c400e6680b0318100030024010301e0906103400081c4440200c40a52240302c80703c9038140d41030502c82800c1c89040741e04400781a0482e007805290f25049a002100284050101500070006e450001c1040d42c43e100426003041d04c0c680080b10541e2070082000801c5841300025411070340c000241d00401400340c0a406500600c0300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 286061223 1250 286059973 286059989
    0x10e07050c0f0f03120c1201050d210f14040f0303080c0403081206210703080d090c0807050f10170601030209060712030f0c050403120201061721160f020a 68
    0xc0d210b01c3c103c002c00102603001c6484150f44403a5600200e015260140c000d0003980c051030750006101d5414030170213952600c0e00a503002244010102d0340c1d0800305100d0b040010010740038002e2104215004001d0200041e82000f916080034106043c0f0700885c111440082c0400040c100803801035500001200c0107035030003980c4d04d55503280032044d003100c070b20083d100d19003d000307058000302c10f4450b480700e0520b22107a00405020301610310744405000ba00100901465159202031240001c0c50180100300100100005031030300038985803c000240743c40380021030081316600e20706000203621402101c0ca10045510f9a4101d8032000d004a009000b0003140702c1c2c1000000906a007403092030380c000b011024195400f07215442545a8100580740d40d1080e00010070000c0c0004e1000800c807003020240c2c172031a4400000c146a40d403084407181c0300c000d54519042d070401640d08800c040215903100c1c040c151aa0420b01e88103074011124011101000d01800b056040822034045580e64050701006211a03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 286062473 1250 286061223 286061233
    0xf0d0b040c0b031303020d08060319050102040b070b09010c03050403080703051009021b0d02010b0310020915040e0403030b06040608060111100609060f05100509130e1203060301050906010e07050c0f 87
    0x40d01c40d03021350032200590151060f2840c80141a21480e2910f04c1004050040e2141403c5410380386c2c0c8661a40b1404c8032555005e220206164080c0d070064102640140105c190b1414100420307402c540b140c0340ba80c0109400d01c2c0070030011a4101101581001480c50002029035441d0106034000704250400c144490002072000d07a040f001d5800608040c03c243c05450660580000c203900700c800c0e000c01190590040544008000015409040c40d2a00507081d480407588440703401034070f680a6002098022400410b100c107042c2d042c85200c5042e0016a51245480d0501401804045008040c4d9040102c0340003403011800080c40458103a5200d400240101602c0d0550324010f0f00440c018944a542c1181d0005000d03d01010118a0713442c09850b058a880c20240c1480301d6200620411460300c0d85030912000312910130404482800c0c0d4131220f07103840b400d04a041500351200900213000703d900220041c400c1031000c0b6100741c0c00c554a82045507581c1c1d01d10705c0b11414018074010180143c007807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 286063723 1250 286062473 286062481
    0x210c25080a0c02010239040603021005040f060e030309060a021c020d0f03140a0b060408030d090606270f060504050903041d01150c0c050402071109060f0d0b040c0b03 73
    0x540c48003030b00340c803d80a4462180300c1c0c0800b0080c021000a0110380c0e072500c0d05190500c01301a84184405007006440820056101c2c0c0100d07451050071901d80300002d000140c2000192041e070403602c05054285880f00c1141d09620021b0754a01511030061300c6000000742c2d0700c5a580c0200f000c1405502c00030a10700e2014691440a900d40c0203d8007003401090783c41c81d010040c3c610030700c2102c403a041d040030700041c00e4842e89644401407800b810fa854100a0401010559801c200060040c06141280100d80750b01c1c0c2d440c229003650040d5020401220603032480840c9102c900d901c030a40c44000e001c00252001e00701c52064041e01c4254885904140352105006912001100510641c2c4003099500c060b03541e4000c1041c400ca00901c56813170048542401000e01d94480c1140e1030791540280069824251030790005012a4805042158034034034501040d441e40c189504910761015048455051040540300400d1402c1c401c0d4a00a003000c4407140060200f0881200c641e002d40784d104000d40c0c40e40341c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 286064973 1250 286063723 286063727
    0x90706051c0f180210020313120f0c03050106150903030f0c170a0306050316060801060f140d020307200a02010503040501060b16060605040b0604120303060503060c210c25080a 77
    0x3070350f000d0f030060362981c044e40b00c810b000000f1510750042402c2d40b507100629011040e210002110340840e10b01e03901c002d2130804a8501480e10003e0350180000003032491400611072030414004002d4018002401c0301040480e400950300c0148070890f04003107000c41c1c3c1600e44000080b050900703d1010903004240000740c0f41d071550007241030381e406070100c9490056640200c1c807011940d21903080020843c00040c00003900c1051030f055910110b0921a030009516150300e085a081283c005020550100400c0300207a44400c1c0e00e000c004d15207482001c001c4030819007d07111040d48001a06004000000c60100700c070950080000b06203c0413029201d65000e40109511740f69110b0580300141852000b24080ca418425001c2d1444000c100358a024586001003441744902c000550a041d80d07100300003401d4a0a00417103101302c01b04c840e901c0d5103021000d088160f044195055581c0d050a03081042007490034281150300c01d40320180b0041c881d0700424401d023403664414134010180c14003c075005620765 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 286066223 1250 286064973 286065011
    0xf0912030c03050c0403050703080a020a0b13032010150509010603050103031101140604090816080306041a101413030305031b1206010305070c0b01031a090706051c0f 73
    0x1c0010399061003991950041c8000c00c0c0910701000e0055002185c0810020712000c000740255202c90040c0d41c1101560303242c3c4004200101c4800010b40841c042000400da0b0102d183c500101c01c0c80e410010039640409015070303410801c844100550394039405801c00e043c1d040e840000400e00203111074100e68440131300401501082c0320803404600003541c42020110180910b840c681e017840c2036180c05a480108020103043e40803416a1714000401c07050480d0072a41151055003402007041c1e659900b400801d000c12600d040b082040014548480300800c3d544001514100c4155072401c543c9080b010301da6804a4811681485031284c1e49100000416402c14042c2d071142c680d0145500041d00600141d601500c13403140d030001018489400a01650300a900203500189076103480d980030b040382e0703851003503140082e042034070040800c4042003003040940e040305500905000203810741a140c08030140903801900c1000b884100d020041008440103540490261143c01d5001d20003221002010036007a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 286067473 1250 286066223 286066241
    0x20f04051908030f0a110105090c03120a02060f0a1b020d180503060601120b0406030506060a080c030a121211090f0103110d0b04020f1902011512060f091203 69
    0x14a40061801d01c40e00307000000c0c07800311448040614a0b02c2464001080303264464040e90042c4a04003030701d55450780f070910949200c0d00d00c100040c0882001141007500c2c08020101828680d2410071000007441d5011031407135040300d0020340c41300446d2250030412001c1e081d02d0f1120b40c50141c10101240341d007030f4002034404480c441034555030f4944407002c0400081c5012030052981580c0140d0200f24a035208450500600c00e1000c1c00082c070090b1040000c068965560090714654041824411a40340008140c001006400300503c040e03800c04000c0381c2c880900800c064001204403184800180c007504602100c0b5028031410811200b0182da05640390f0070900501e40a080c50200d000099400f92041401309011000d81034100202002e050303020b80400d462064100b50240440c404081050000d08801000c0c980c0341c0014106c0140020308551403a01c016a071110011020040301541e1016221415000507011071804492564a03000d0003550308010440031400f0702a020840d4158411104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 286068723 1250 286067473 286067479
    0x506071403040b010e06040609230a05040b01060f1205040305040303110d1209170706061503020f09041d0f0303011401080103110105090a09020409021c1a0f0d06020f0405 75
    0x284032055196440039000032900100610312401c0144803024900300059840880240701041c0740b52074141041c1522a0b46070392001d80c500c3c0103620302e0b10300c400c01d21044e8040c000700c10400c500d107000d80702d01c1c40300b0380f040c4116010310810032034170a42c95114100c8500000c007001001d0015080515008101d903029120076030000302d180881c680d01e0600481c1c140c0e072800242d0f940d4000320790305000301d4000300300d00c500898144a0203044140f0910390900984a540d000d400001500c900c1c0c00d401c046c02d10040459078081510400c4580d031560010002e4804500054500044005c50704050740c442d4984084941c0c002d100d00604600110740003c015030594030f08042c0310142410340401075503800c0c401c0c000140500d03032541e003071070740ca510034005421145402400c00c000e441e5522091400c982c07080d00701704069030300010142d0b4444201c5052403205191002c0401c501c24504060710f2151003281c0e0360780c0c42881d0582554030300b17940f01e0500341d40d100e030844800c40d6600a402c0b11042664060b00c54180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 286069973 1250 286068723 286068737
    0xa0312081503010b0a060e030307050f0717190303110903010203041b091503060911060403030908010507050702090402100e062113082b0903020c03070b160b1b07050607 74
    0x607032070a040c0110080068041d0a60351440e081c81000c1d204442070382c210030780510091118a01040b03003000b0100b802520301c0e01921303d950510401c6548011003400162140d4002e800441d0f040c10302c0c41c0d800c1405500b5180020f999002c1803410b001c5485044000ca034158004809d02c000c0c0074025244071102000d0a200800c01503442613180b050302d800001d049120700384080d040001c1126600302400281c03180140702c954200880000c0e1441d00603810a400042c180141402103034024440c49403c000d1905143d400e16405034000b0781ca5000c01000240244c01480b0340345002c0340240c06060784202e009013a59101e8018030340304c13003150703541c0710040d2034250b43d040105003403e4502002402064100d030b8031518001d42810707620500e41c4422200b4048070039803454068880c20610504020034881d90141004d4040e03007040610b401100d0300408a2440c0411050a48a20300a00d507189950310100d2000305682e03281420698602d0309120780c0221000140700410000007007041c501c030704030a0310703a50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 286071223 1250 286069973 286070011
    0x815040b0f0d05030c0109030206070323040816080423040204060203070206031005130516090602100f02130b07140105091005090c0a0807140f03070605090a031208 72
    0x205450914a54503000022050341c039a040c1840307802e1501c5940110100c0e4501021005070341d0031144003401c140c0050b08028280729131b4640c58051210b64a0000d00e00c0160340000240c054201c5601620041030400d0000c1c0d44000923010001d05007a0070703003014a90b515140c4e11101000e0180c0b00c010412105885800c5000c0a454180300350340a890140d030080d800c0c266942c0c01d2018903030020342440180310004c0070004940e41c4d241c40b821344006440c0c0d008511424800d49403d02c1c80241030480040c841c00071000d01c810303680010b01e00300ca22076004002c5803021080700054000d2081103e00020b031080e4000c042640c2030322074024002a03125488449140440d0441341d0b08a50094443d044070b80c21241640800280c00d030016500140f5443c1902c0d03404c80c8801c0010641e0700241c1c86104503401c11001003200d0601d540300c107901514203850440c1918014000603882c1c1c0d03c903000385000e020010450700078545071042c401018540c00701d48000c00d505401400780c0741c6542140e1000103d16400054 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 286072473 1250 286071223 286071229
    0xf0d0e04060602030316110a05010204030312050105030a111516140c0315010b0f04090516030b0a0e1807050607140705040603050a1101030e0d18050405011a09010c0f030815 76
    0x6a224003510346640a4404901c40200c0d1f03415105400c00400d4855050344001041081c4001c000561081e01c0e00c4803851a03020109060b1030050340031612980000003a41c01040298000d215000c0040f0340c0190424026001b01c0c01078020419250072410092405204024201c07080c2c41000320b0380c108a030304800700e4204040d52641d184c112541407106580040120b0a5030030090f00101c50010881400e06895504000803074a04848004200030400802d8a40a8142c801d00d516840140c4031601003504007894030501c00009082e813005814421100400040207000300d4001e440c004103c03503944c0c0118203180c111710410043e100d603075000d030103000100c0d4507152055034212a44000a8205200e070781c2c46010322810342c0c8507a2410f064484040c0c0889120520106560048035110f0a15089d0705201100d0341070310035009240607500d0080180103134245124001d00790a071400305540c0d00e48448004880c2842c1c50800200300030030000300c5900300354101d48044e114020311002807100030300349820 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 286073723 1250 286072473 286072477
    0x9060902040605180301020d020a050304060e010b030c0f0f060307050a0305070c15021305091602100e1c050732010c080703090206070807110909030c0c01110f0d0e0406060203 77
    0x10315400f141041020180301441c080413200052030040006043c04044100401a070340284804000603d001013084200549481a84811101c1c0002040b0601d04080425900e00008100c60300c68000403a101503140da5220603107841c00c0011f8030964890400c2d81000d030650300b0001c0508046810100020300b464420001e80d14856005403064401103a9070b04503800940c0030070502000882c6595020416485425409014900c1007040da101c801c1c000c00c0090401c03080d4840c0f03c40071418249403160300e0000081c000b02c80b40348510301100c0829110003d5601d03102e90000100210049440c610350702035400e2080042007001075809501154607140b26080702e400380c400102156080000c1079849202c0e5028034021803016020b60300c7c082243d1100310068000300403c4a400c0314007111705d001030904035003551f000703581c5000540c00c0c21300c04000b803500c80400e195114100a0740e42c8201903c603200300900d08015101c1d0050300d070203080d60079005220118200003035005d10f040c0ba400043d42840002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 286074973 1250 286073723 286073729
    0x302030c0f0c0a050904060209100504140a0f2105061e01060e030d08060102120f070611030f0a020d0b0d0507081c0207050904050106080303100e0f0c070b040227010906090204 77
    0x1040d24050500c4d007008000c14010384203450166003840080f1140e01c6051080c130b4204101e40307541d51a64075102040114944c4103803010300079800003c0402c4145441d20700d0100351000c040c3c040c400360304101502e5a0980d11071401a009205107c1440702d20180740d2380d8410400c034030031340350ba41c244c2c0c0b16201540d01001010f2003507010b0f03100c1c22103000080c0c440d54034243c2152051054034069090006905920340104090a80c15580040c411081064920407100c1b502e910300d000500b1440c2500c03003021070480041146428031380020345e503007294045900802030102d0080103c1040350150625a0784c860850190005074030500701e0003540285030290800c0c00304680d074020721025041c2800d11003180805130040f5002e40d03da81c0302040301201440554402e9006622146100e8a800c0340840003203000750100314a14404018460084008021101429000801d031300e0a84c44501c08101e070302c500300c40c0d441c4070b011124602040c004a00080181207521240041c044940c480001c00102d204030702c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 286076223 1250 286074973 286074979
    0x301050136080601080105070813060f0207021806030c2b05031306020f010b0607030f050702010903050d0507062a1112040e06040f0b090c0c0709090302030c0f0c 71
    0x4a000c11484a0090260040c01c19495521100702101c0d400301e40c440071503400241d1590032240050150030024855941c0c002c1661511002c142855984040b0000b440003000d49025243d2103c0f035000000350701264400d945c09450842d0105603901003100e0007034180d88041c480d0144080340b00305445c0451891183c4071319122108410740c2040e50790303aa1b842a0744001c485901080c841c140210602e080c00070014076590300035282d80d06c0008141401c4410040c8618440d4005014007070110398084a0150000c41d01c0c10200d9503118640010399200641d5800103196104045e43d1440340d40d03114000d400e040380b0810040c042080c0444400089140d6030000094281440030b2a04445d489075030011410007918058900b51041c0019010351a03001d42c1260038001140400c0c0700072070500c0d114040c0310716400c00f0b040050515009c00140c4640b0041d0102d001360002017a880f48a00c4207101100040c15107000c1008600c0e250714001e5141e03004000b080c40340c0d009020070490780200204e05203484607001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 286077473 1250 286076223 286076237
    0x91a0c1020070c0306090f1703090319050c01110c0706050c030a080415050901140a021306030b0612040606061106090a0b040c050915040c050a02030306120a051b090c03010501 77
    0x1081c1ca1030361603003100105483c00145400000045502480348590441c00303243c0c42c846d541c0c1c00341000d103c103000c0034461f80c01c000020410015402808800c0da00c03880d18501c402c1d0901442c83d80101c850340154a111846c40d464480440c0a00394080300904078051000159410700ea03968000ba5064050044102040d400401003a1710051090300c00d1980980300741003002c54820850204d504032801140d42c4220781c0c0d5201e03c418406150b4142e04c039406100c40b18154540141510b004456000b603105240a240e1120b6444109035903540035503d0004007148040300343e140505041000d071030503201e00c2c0c01288010040c484003440220300c091044c0f003110001c2103c003049942d1030401040007401500d0315480010081126650403c3d418012501d008411021800c4401040100d031180c0401c00c1c00d01c4820408000c5458000c130650350f10542c01c0303864004800940440a041150040006100780108404158403202600c180c2540c0041a5070842e13083e5034440c03c0040c644800c0c05054082101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 286078723 1250 286077473 286077521
    0xd0b0708100b0903100c021203041b15230c010c08060405010501050705073003020c01080a1503080715021b01060824040f021002010e10060e011203091a0c10 69
    0x3007901304086c0d9030703010701c1103a640c41c070144108140e6130003d5400722150040001004298140c42000304040c1210f00191440c0d1035440d08050555480320301c0500451412840400e2208901d0703040e1003484580328000d104210240c0002051640d0440d41075105030700d0500085201d512610545005683c0000180441402e015001c2100d03100e2042d004043c100540001d142d83d042c03d40301001141c800c1d001000090428030000d88201c000800c4403981c1c40c600941080b4402049280d0011682c102040b51303a541d4150030580d00442d12003241c000081d0002842c10044008507000d1500c103076071840200f00d01c646400b402600c40140050201e030100c3c0442039001108581c00c5140e400c0343c4100c445030380c0c6032002d6000c205000d0240b0a19409070350744128100c1c0528043c840300082000c0c06004006148c10400044282c4006010328000b0394107c0c0541010540502c02d00c201810307520448050600d48040050070551105900400c0341c00f5500c0340500054850180d005030782c21404090080d618 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 286079973 1250 286078723 286078753
    0x40605030a0603050d030608010b04111e390609070611031603030213050a12030f05160b010302040c170c09010e090a05040605060306071403060d0b0708100b0903 71
    0x40e1501c0074456070740000000041e800c0044803c0807105440c0411014603000b4507074215589808007501079402c0c1081e00315800051030840f00301c1000d404241362640e041c40204422401149002e90f03214882210398905000000e1404d5540000150b16003d00014400d15a40724030003034402009a61240d0014071007076010b00740c14441020300b802182d0809000c800921140f101e4082c09901090380003d00010139403141045002401044e143c280009240640400c43c041001c04040d040014881c00c40b803500b4403807011141c246a03400161900182c0600b07051091840038071049100b0f5240c000440622401803110160140f81441ca0240700e654020700560a540814005410004021a14003041d901c110078240130f03262052000034245020301d0484100c03034014200920940c05041004003444d070004903504040c0c1040c1044d0740760f86868000c161288440900106008112020006c41940c0500b04a1184c010000d004d0103c1d0f9031000c1141903803040400e44c5805410080c06456005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 286081223 1250 286079973 286079977
    0x5070b0601031a04050f010e0105010207050f040b12060108030a260601360f080604050a0f0c0b0a050a08010f08030703032705070303030501151b0f12020106061103090303040605 78
    0x1c450210780c6682d10b443c410005049983c1100c018801203510001442200c148851141c003410f000c0c00240400307420a40018112440c0c1c0240b41d100d03c1e19200f0030840c0c1e45130a080c8900c0510b4170802c03a40c641d41c4500e6403984030b03080f120100d40080c0c0b803110905550301800d08a00d00da24018144280a80c403020011500f04504852040d00000112083c45050382c404120030140c0182c1c0c01c3e041c04140c20401d40300101c14940c1d0160034158410024400071400114a00f40416401a003c0d011309001d464480300003c1c10358030003d079140003c10010f698580040061503800d85036582c002c02a0b0700d80c0e841c3c04d4000710380e010740d800c581c1c03003406100c000070b0103644400404000d80e0700c003d0700030035042c80c0003900c803100b198216120340201504104064240c0245409005008018000c59009400c001c1400311441d400e042510f03004c40052040c070148450481d070041d00545c0038403080c24103c00190117000c20707208000001e01a6007007152540d5000c07094461000d0b000340654034082c0350881c00c580741c0e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 286082473 1250 286081223 286081241
    0x8160603051b07140a080c0d080c0c1507020703211214010b0906221a1606180606062604050d20070608040c120302070e070c14060a060605070b060103 66
    0x148540c55003000446d004102510b00704014600400382c004203490010b0945c00c2c040c14080e104a418030100081c0ca074041a846000c15110514442c7d40d5034498049150801562002d8103000000720301040b4042d00d50080c804822503500d07072044e0441d240c4801e5003100d0400030040b60200e900310050107085154001001c041000030066404c020300c0200f11100c00b0540c0d06100308041420004004003040032403d070f441002980c09031410f0904d982001301802c410f1020003030078296903150720b0820028500000d5840ca400c0202001344507107511000c0d1001c031481ca5180f60320380031002c180c841c211280c000301c0e11403a03000b0040d288003c5210001d43c3c460302e0181034040c03902e0382c407011010503e0080003080b00501e15a620f0003620700f0903080600700368040f0b40100c50002078207049100420b400045e100308468820928140d42d545901044960480008005102c804440305056031441c0015010380500c0c40b20f002000425919801650248a18100100912444400105598025031000d003a03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 286083723 1250 286082473 286082513
    0xb071e2606010306180605030c100f05090a0e07030501090e030a0212090406440c130b030102070501021e0304031209021f020a03110d05040e1008160603051b07 70
    0x24551141085c0b840701794008120f00300b080e5103a00800051904102c0c0480258044c0c3d003ca1024607000390003001341c82005000000c1c49800600002c080d21075002c2d680042078290455041d03820503002c02005010700784148840141025000400820007004030f90308881150000c1c500c8140e8040e421810750010001035034802d944180000703101059002207168029002584920642405110b01521107000098007a1030b90b044807020301d601001840140b140c2d800c41d03805981d034490400c090003070729040814680550001c14800e0803c00c0c150080e00c16404403400d02c6886c0000e02e000200180800c48020f00050f014020380000107201d503002000890014011000018014010100001034414005d005a01a00c0d100003030650003402c172400d071300d012005800d0640481000402c5801140180d40c4003600c1200800c084001444009004018080981c3d2462546d1202c5680d04041445540003090400c0e001a8103a80d415540130488018200705505005554a60a82d04004800c040d20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 286084973 1250 286083723 286083731
    0xb04091a030a05030d0e07050f04020304050f0d050a170c07030c080403020301150e3403150b1e03040c30060204060e030c0604120f0b071e26060103 65
    0x410784007402090302c00e80c02000115a00d05c51461030307208031400e00e40e0100184d0000d42c0180308a0341e407900c2940e0480c1e8110b42c09072f00c9868074180306040c4803440e1040d204500c01e00d071000c4820f80c2c00c8030250a4042c101c0c0ca03160301d200d00311040b483d00c20008568004500383d0404c8403400107070140c400303240c49070300407400b0900709922580424211507005004400c02403040108001440d40418169489170810610580000b044082003000c0d25203041d1300499001c103680c800b94460300c250b1003001440c0f82c0d0f404205103c0e03a40d410010140e400000702a801843d05020b00302c220080b901183e02032540a00d00300c00c0b85107406044005042c9039641380c21010300d040c0444a24071014105819807900944006a45a1421902070280200d08030000d010740c03c02107207912940d403032406940846e401421040c40300c104614026002c0e2810a400500c0343c103501d4180502141d000d100a00d11074000006001e2200c200307001514048400c0004000f000c2d40d0261030000c0da6440c0741025002001810085 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 286086223 1250 286084973 286085021
    0x2040305061314161a120109020903010b090f0a051602060c1c020c15091219030e030309010f0506011e0e0f1005120a0603121d0414040201180b0409 65
    0x90f0514000400e598004d040540c800d12244800521071500140405036403071800c405107503074504a000510030740b407015a01180303030703800ca45080d000280f00f644001e0040411b0b00c2c01c1c2d00141840c0c101520500781c41c501d07110010709070b00d15400c1c0060586000d50010051592501120341f140d0b88440001c1070441a00025848032940c140058044200e2010207400c4081c2c00c00c0100031400001018480c0c02e601502c2190410710b0213000722079060642000c07200c0880042d91040d4040e000840298007180300020400c03283c42d10640c000e84140d09c00780c1c01401207454220044030001c030810201040c6521082c1c0c03400c8801d00805099000a00182c510110920005c00090034031000c0c032941004190006079440580c0d02100856a0114024104001c4141076071110280350b01c80b0007420062048803100103001c546000c3d548604944010420b020a0035115107001c03c2c14001d0f1000ca01055016400140f40c0310400840402d80d1080540780381041c0c544100e04005d0302801844d60240c0810803401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 286087473 1250 286086223 286086263
    0x4020304053c0a050d031107140c06160b09060c0d0c0e100906140307050a080405031c060303110d08070c1e03020c150702100c0212070e0108010b04020403050613 71
    0xb0b064550b800000c0c1c41d5800303182c20860700f0003605050440401d45014180702c0070b5241c0c6010f5407074043d000000820f070280e4003c0c03240e10304403101c0c00d06640310902061400800003001050fa0f0411720030019066191038414003966601c001b501c074500e102d9800c2c0300b1410025400c1d03001d03050701a40d0745000000c2a040744c0200310908000c058080c0080c05900c002d002d41500502115000c0d841d011045185140199004240d030040c120350310200125000404c003440300810a40741c0008410482140d2130080040400080074107100441c08998140658441a0408140040082040c0d1140d2001d80d560341d02c11284000c400908032034407051001c45101302e43c03420096910091182c0c00411000d1458001c1044050556840482d203c0c01040390a005865085a110540c902c5050400001105200080c3c40c03012400d11120203101e05c483c00141c400201100c2c904851031500200520660101808240e03c65800701420f658424404524046107482c003403815a8011412001d801d0621061 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 286088723 1250 286087473 286087573
    0x4140405010c0f02060108120f0f030a0605040f1e1107060905030403020901050306090a080d020c0f0a0204050601090f03110607020a0e0114120c01110316200402030405 74
    0x825039841e907490041c04099a007141c041001c0a9007800184103e43c500142c0790340c0c42d01005501e2000c0140412a0b40c00fa00e111800d68060300410740c43d20b0f4407403620901000040c2410f11071a80700d80d050401d011460100c9102c6c0214108616620260205041108d20041c006040d489050381c0300c04c0180fa40410100e01c80d06d10351034841e401441e41ca514500400c40314080c1a000b541c4250043c2e400d00104c1c820002d040707245294032008040c2c503003568000b904e000b40542090480a0702a48200548401011a16021052003114100440e4682c080116803046103070050340f0441c5031004042c00800d0440c408001108070080c48180340814075404500040c8050b03009090310f0381031500600c00c01d0404191904400d601741d511a1031b04407100c1902e0354071848c2040da9414820107480c2c00d140c104040c81207484e901d00e500101c090000c07452502c1c2c40542c024a1910000c0380d0038605507000d61030640212801590044020b00c1281041a000e40e068514007488050b03040000c10800f54103400068 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 286089973 1250 286088723 286088731
    0x1050f10020f07090209130c1d010c170a110606060409200708040609090239061816050303070318050306010e153106090e03090a0f030b040305090414 66
    0x90250702e40010205007d40c6042c464160006141416400007455078441c0b1000d10381c02c281c460413610994640c0060b108110100b401914660050402d41c12041c081d900034040000961382d10245440c02d44001038850b90f058885070b500403410041041541d0903034200103c07c4410040303010b40c544280d00000c0250380038140840d03504501240411070f40360003007001e400a00308414150314040e05c032014000401e00c0c122407a81d040484050b151028030079107201100540c0d400080355010704141141450310328000007a00d40c0ca204401e03140e02c2c40102000600c0407101c0c007134019401c2c95031a40d4166510145203882000d210002c2100060351f6a0422006008000010f0300e202d0b18100038041e5160407030030a44140c0a10180f8509504140b0b1880010b5840c1074600e83c01c044401d0040f422001401041d03003c0c80290382001804181c455021005081b040000c94080305034564424424010109a11000d41003985044c00100801d001d44000c106201004100150f00d19074800a100c1c040001e503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 286091223 1250 286089973 286089989
    0x2206090e0109140c090a0c030e120414220228030c030b010516020f01021005180d090602070b1e070b07030b1c02130b03070e06011701050f10020f07 65
    0xc08101031114500340d41107402e1001004d08120b1100101054040401400f01c036051503650785003220441c800d901010458000320103481c09042e074001c0f41c1c14107800c02d00070024010000e0032000301c0d41c07608204000701d202b10140d00100041460601c0c40003500030503150210126000500d8003c05c0450309040703150702d003035280054200e00a000080460329006490b606210003002070080d0b07114020904200c40c0d604954001e4101e1061004070b080195404810280600708402d10820007030b2603201040302c80700c40b012204000141c5100300c8d00c58001d48102c00c090b030064081444800c0d140002003140e002203003a900c01d030042c2d0b504e00682c00c1d80890401d89a0390078540034405080d605004c3c0400c1407030304664003040e24280d005011400c41261200a101e0808182521f0705c0c000141c010318841c0c000203003601c00d038541c3d921a0b080c1a0808540950010382800724804a800c00f4041171410b990010744990410401d82041c010007090b00c00c0da56007036104a900703d0881c400d0410121010300011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 286092473 1250 286091223 286091231
    0x1060b040303120c081e040302100207050303040b06030a08030420060d0203060f01180603020d060f080709050907031106070501091506030c0b030103030c02060d021309050f06010306052206090e01 86
    0x84803c1d03c0445200c100031508000d4417a0601401840c0c600b1141c0d414000110200c030141c42d94501030303180a01142c0501d81160012070510140000407001c4c610440c0640a0058a6505c401c01c06072a2080c48100400c603d0050000c900441d17020450040303807082c5554020741180c000350000348240c04c12404007003072135000810004241017800d25603c22800c00c0c03c3c00c0507150017a041d000440368141c02007204140e408104925079a10720b40090b0000c01c50380c18040d00250f00e9001203a181c40c890b0107180030f064200710124041c5000005e1170801c0701c1d0482e10308a00d4603141400c210250740700b0b0780e05070303451340d250614603010a0304d21700c460303040c20703c07141000812501d980384c41c03650407000d03038007002440c1c030207100400c042a0482c0070b400e03006504480b556a500c10075000407009000314030002001075025540800d2640960344454080c00000b04400c80d0f59403030000440695016009858001084500c034110540c000d551845500da00c0700004204c082d20ba441c4001120034042855049a4403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 286093723 1250 286092473 286092497
    0xa030f170c060f180c1302090301020409020a0201060e0f040b04030815030d030b130207080306010c020a03140a033c05040306051e0708010e0714040914040209240402030901060b040303 81
    0xd1342c1c4411102d20008019040880145c80010240c0e214000c10391031032a000902c51601d50780c01e60494016141d880b408644903805103c0090080c502c9009002c00100400c0103d510a446440114440d07a808941004103959668007161101c038007801000501440c0c005601c1240d03000c0c045480d0540742660000b031a00c00e40400c01c0580d55190355001000703441000500042200241203c2c0d1000003820403408130911480810740b80d103015400507050384e124141c00f8800c0701022492441081c0242e131240f00c0c00c050001840000401d0b038031005490502d0013420005c8810100340756405c00d0541c10628105030f13880d03c900c81500d008545075106403101d0105050070100300305130541c03c41d00c0d46c078103501d4035030601541c1c001100f8040c1174441070110f45d00300501c0044540f01218082c00030182c0038485400c820110020510040d28224400d2034500001001440740301c0004094040903031940a103144200d00f440029800a808466103540b00c0001144001e44540100025482582c40d0f00800e20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 286094973 1250 286093723 286093741
    0xd0e0a030e15030103020d081204050106140105040b030f06040f0906020408010c0302031b030a090c141315090f0608030403080a080601090f060503150405010605090109050a030f170c060f 82
    0xc205608a202c0c40c41488860b01c90407001c0c050b681034980c155902000e03540300b82840c204500403003c1007031800c0c41d2401004104901034001104a03550005400801c1c4070b04c500554170381c002c5025040c0000402c0c400150100881d071006a00144c004c0c1002900825013080d42c42620700545090b95000d400050030441e07504240324086150b00e070341c9411415420b00c00040301814507003021794600c0307a001001003071140d05241e2203d50703010707441459400c46555079a01302820740360b0105000c0c400c2e00e030007901c240740040c1130080302c60103c0d025176085803032410702004030000c0c05400c00c9a070000759500d0000c900d0306001c0005001443c0030f04480f50b169501c0c02d4009010610080c00981005502c55042005428244e4100155000d40c100980c8076030321030717065004044652000f00d03480390401e0000690150020010f180191003030f41c490b00002d4450003403042084081c8001080c401d07908038004040345881030412044031110001500c1d003c036402c1d08514005050303480c108096407a9090020f081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 286096223 1250 286094973 286094987
    0xa09060c0c020f0904050c060a0201110d0c020d0309050309120c040c0206250c020d02060d0c0806040606180b070519030e090601030b0315060d080301030f06140c0409020703050d0e0a03 81
    0x3c0d0104c80184480c034090f540d141d241c009801e500d074041c010200e004c0120350300039000105c641610342e0384180c07208000c8071000051320140c44108054010900e8201070584a40500c2440c4d5070000c0003185040f00342400d010300c140c1b0f1a602d0000d0350042c2c80d981100c940e0b46011300c2c0103441195004094a0a00e030b424807a42030407101510707020b4000400c140c0c165581000e0401c4034180c0407a1a41ea110006002142d102d110301c0c004140644e19100700f203850283c2045616000380c41c01e4078100b1150b40c54100541d58010060360302241a81641d00400001c0300007001008010704c98415141522206004e0740b000c80c01e802e904038046250301341d0503000780c00c01d03145041c3d10020134030301407020a0b119404640ca038034003000228400b044010025090741c6801c0f440c403400a6101001c19500e41e9641000c0d0112184110100d0340f82d420036011014050031540c00c2030040e180c9030f040c03510302482d05036401d00951209100300c01344841032040800c2002e4911800340001d40d0a005440300040c1480d005200d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 286097473 1250 286096223 286096249
    0x12101104090b0111070e040807120917010605150a2d0210060315090c0510050309210f0715020c0c010e010306140f04021e0a08090705060706050a09060c0c02 69
    0xc810004403411444c0014002c0444500b060080ca06441da42014681032007069009041404210920b01403144d200484400300ca44504200c01c103014200040c0d8241c51440c40350a50164404103070302c1481d9508402840c0d42c1070141800f04080c141d5501d442d03c2424507084490f0a21403030055000f289806101041e6000d44641c420080c0341d045950788a01c50007500841d4400d29a00c11948003040102480072025001c01801c882c0c61001d002c00040ca2640200c45441c400e008807030030300c0381c402e0010500c18004020010030f1810b041e46102000e8050f00203100940e1a8400c03440078040c503681d2480207241e20b09802d00500a205d0b955030001d442c0d00c44d002c08441c10940f40480c02c00090001c3c0b440c0d0f440d607030740c1114071102029030100058007900800081d01c0c00000f4880c4030049a0125100805100b2001e071145201513803582c2c440c03034440040d0300c18150000000c01c04080028000c0e030000c3d90142c0d203030b0310016003141c00d84c0b00d40c3d003222403100f15032000c034003003071030080035482c0c144294080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 286098723 1250 286097473 286097477
    0x3090503070e1504092a05040504020108060d030210150806090c030303010902070c0906170708060f07080601020115090c030e01110f03040f0602030a140606090a030212101104090b01 80
    0x80c601d851181c44400310001e28a4a9010606082c00401da1381d94011100741d940003c0602c4048002c0c10020f040c0800945000e90001c404e11400a1281407502805214640507102d0a00e5540d500e02405000b04601004070b0031400341010582e84030010b0700c902c460382e500301201c22428a0801d10003500d13224020f440c1e2291644800403040c0203680c000304a9066800300100235840320684d1411040241c5c03d83c11210a842c1041030102c0c2440412411403100301200d02120000c1d42d95119042d100c0743c0650b240301819040f000090003050080f21040c1d0840c506100000350036000c01c1d0701c0345185100c2e0b00000000d50301d90011814280e0701d4081c4000c032214800007003042c0c1d50400c280d13040c0c034810017912aa00e0321020001800b84240440c00c1c0c52640c4e002103007555249041c1d0054001072840340c1e42c10130b032000400e0120764a030803c08103039202c100001e801214150700750740810007800c04010510842d445034904050340507415004881100ca444c1c041281c885040c543c8800a0b46ca1850a541c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 286099973 1250 286098723 286098733
    0x60402090a0510061404090204170c100804020415090903020c040f1103130c12030302130f0b0904050c0405120a200109170307020a08060403200a20040e060403090503 73
    0x21803800c3c4a924504072883e5041070340080501c800c08100500603940002c80162001c54001100341681160300c06085600094032202070214040010021480031b15100090192002a006040507881121800001e0b00003042071591a040303403007039803c034100440c0181c000d105000d580d07082c02d00502c1c0707030618510014003402d81008809c0c2114000102105411060b0004041c1840b24099100000c0c0810071600260403030282405006503203e60300071011192950030000720141412800300c151000d5102c0300340741803200020030001e07090203413030090048001c000004495940001103044140f085029003185031840c01c2900b14048082c40c2010910301072160040503070307070182410b41514000030071107140314091076505145000d007910003900422070407408607007003100042c1c0602c1944296201030403032281600d8040007054a40c1d061041e40c0c024800540044e4801c40c400140000c220001070100341c8000004040d82c002043c00320090300804140828180d100d681d2001503c01680102 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 286101223 1250 286099973 286099981
    0x90105060d060b0a0e0c1b0d140901030e190605060f010e0d050a08120103140a08250b1302130c091413060906090608070e06150408030301030302060402090a05 70
    0x28081d418a580040825640d01e1440e543d42d80c86812040107083c0c1904440a145441c110340c10305a48802030088011043c0541c110074108001140c130140705c599903600324048a507100f0f1a80340d812264040d030506841d0001e03000320351010088081518039401d070b403850401840c103003201220000b404841c002c002401c41c03c0003c3c0d80041e606005410162045074801c1c0c56410003c0c01c0c144c503524000c0044100141560031a5480005107040e01d006141102c404a41c1c0369400c1c1c1d0350f410400c8e00a104c181c00b404605806c00f41d800022240300165661aa1841465581c80f40c064504454007200107603900c500d1020342c1800c20840040000402013001113800c0081c0c0501303643e00a01c9407100142c07102c10481088e85800d090300d503006501d40c0090000b90b40b1180b00d1405004280a00024645007903000605080c001401100322801c980c00b44069031240700601c442103420a0f24040c00c200100000200302004000442c0254000e5015050070304041c8100150280090728003400310b81030000340 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 286102473 1250 286101223 286101229
    0x60309030306010c140111090a060e0a0302130b04390c0605040804080109060515010512010e0603070b07080d061d0a0903110304080c100f02060a0507030f0f0b010809010506 76
    0x80e6001802401c1c8142c44d10340d58a8000b4104501c144104d04075404d2502c1420782c8081a0054140c019044810501141e1a0fa508844008040e800349901460031030007040581000c462448081d00040c10100d052080b00300490f046e91400301549165071f0b010602e0f0101c40c0c4e20b5100c1030240c600e2400440244015002c001044580b1800010700b05950700c00109007007007989011680206107850080c0007100e0182400700c0200411900c0000c104207150030346011358441e604484030204810411200f99086c030248074503804c0010721142c0c05100711000402c56104074400f034044240705042441d40c846440d00102c064640a0340501a000c0c0303006101c1c290505003002169000302d12001c0020049030b0340c01c08a0719004400c001d6102e80c000081e0115a8a0002c202c02a5040056510200507501c02c4000c44465120110402c01038000d440401e0b100d1260b81c0260ba000f00c02d9281c04104100010841d60848080c07008440503159640320a0000d03503006142d6a604c9080301008001c2481c004c408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 286103723 1250 286102473 286102477
    0x108010b0607080a05120703140121030c0c12050708070f05010c080306010c0209010f0501030e0c0102030406081306051824010b09010c0c030501091401051501050307261506030903 79
    0x40203140c0580410131a145520810541e42104800f01413030b0020b04200324054020144651b80d1001d4920f800300124040034541b20201c1212400804c0d00c0ca81601034a081359904002817085484201508001a10602e091111403601e40203001a0000c1031601030018500986540203002661043d0400c10841c1e0300030380301c41c46a6421904595580e62240b00480e40c410250708001d500c95001c500100311540070030106400d681c000e0f02c0030030015a4203599035648205907610140140c0c82080144909031151586035001583c1a01c004100003e0352382c1e03c030a4903021529000b1480c040b1555422955003013052900c03c585030111081d40b60b0178105403410b201c205000c5c175038941100007071003481640305844036001d00344c03c2048041401e460b441d105010f00140c61068400820410b01c0c481503050601c22035002d400c3e40c1c000d1150743c0c810400151510340009007405c080c4100002901c02403010b47c0c030762180000c6082541c0e949031804415a00c602c85103100c90318024032040c000c0112001c40041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 286104973 1250 286103723 286103737
    0x6110303010b0304050c030109060c020d0804081902070b0a0f080c12180a061509140112060513020d031808030705060f0c0c071d0a020906030712021308070e0108010b06 74
    0x407620b540b1340d0b8a0030003e141810400c0d00da130300340d0b1a261104050100540c0f00200031034440c0d00345c404041a041d81110a90300c162800b5119010400011180d00d508101090850040d80107072801d407a540c1000c0c1105800030140240454101c640340d42c4d075141e01c507821650280505011900f0100f160601001844004000349000350180314016882042009410030f101c0d400700042c8203416144004001c080528402c07081074a06021401c002490341c42c6d038640c141c13543ea51721041d2503109600c41e040a440c0160411150603966020900503880320003422507580d00984135000a410f000058520341030003944030000907002404011700091001c11566000381540c1900c48107a00da111140c12a441200d1041070300744200d00c4002445000c21014240c1070790764103c0e9841311740d50680b1541c243d2003000d8003651704c400100700140341c0e580501d08400032108415001402d24588209008544d0100e0b0012700d91907001400802414038404441805401c3d940c0090020b400d8441c081011805481 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 286106223 1250 286104973 286104989
    0x20a09090b0a0c0e030a0c08150106140a0309020603011e060806101d03010e0d0207050f01050316091715090c0907080a020c01050c1902010c1b050307020307090e06010611030301 78
    0x3034a180c2807188130301c0e104040303010010140d501c0d0041c03031719061145071018840c040481c0203061050f540f40300d06442140c1213580c070341c98418039102c000308895010fa1146c0403a00502d0380d600007a4000d038450401841c0a81950880510142441c01a01c0480d81455010004000c2c4410403ca040d0b280d1078254400241c0390b0402c800e07010b00170401030f2028214401029015842c6c0546030341c901c000015054040e550ba5000d07905910b4071a0103006185030032102c243c2c08a0420400310342005114024130142880342d14118640396200c44254101c84501d4059410a51090b10001515003141d0b280d20303007081c0494018030310342d50341c907010401d08640140018280b041d40e400140849909070125800118520000c2040703280c58207d5210a8000740d002c0d2820383c0840d1001081c442c014440c03c82800066100c007240885980c2008024088014088895000030f01a0f41300588041101e07030041c0459900210300d8601002000e0b1900005a0215041224001c1d100d401d0315004021281918401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 286107473 1250 286106223 286106231
    0x50a060b180a09093c030e2e020d0305090d0c030507080a0206040c230f030106050306010e06010311030106090b070f0b160807050f030a0906090816020a09090b0a 71
    0x1410020740b01621a601c070301502c3c1e081400c0c100401c480c0d40010402d8803125244401d541402e007159407002016006032140001444200c1c1c40032a026060705480c0400c0208451802c01b4444210304448a107280740b094804001070f00d030090340e50144508408030102c1d1804211a00d0304140895407000c019038001d040c846448480703400e0500c20710446900e41c2d00a6400d03917540034000c030001e580700030445059401d01000000816000440521883d007040d9140002021030841c000b0842048000c00813507900d5940e0b518001840d407028403a0328002c01c141804180503250040024095503072400019112040410060003000d402c0b1500005075046402c00c0c5895004915012014104600000d0700e035013400300c1005039480050104980d0b01416543e0300040d601c43e42e101361524040c034031080d04104424400542085070541c0240c0001307005142c085401103458980441c40d91140c0d800480c1c541002c0c00c440c0035400c1c0440078800510760403c080180003140c4d20380318020741014040300091919 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 286108723 1250 286107473 286107517
    0x21608030603010204051207030203060703140714041802040915064a15090a290f0a03180209181609020a0e031506150d110904050a060b 60
    0x4d40c10345029281c050000361908030221105940c1d6a288e10040b40720b4030400700064a020301c2409501e6041c102001c01c0851030329045400d43d1a000701001480000341c041c807001070035001359201d28040094170340006950310304014004003602da07250741c91006450703e0340042080c1e0340d010b040e211240d00c0d8071290808201070701c0030f1040da00030034007401001c81c100442400b204203003203104c415500300c040302e0741605540e01c0400081c6501030703075072581d80c00800d490040008100502101074800c140d101035691100ba581040b4500d070308139541844e507190010031561400d682610803528244011082e200303111242e680000c9188000070f24032070b02d145110001c081501c0701006880043e101404a0307111040e242c00c0ea400080d00280c1c064000200d102422070114180401c100003081d600c0014050240c0d1190240040303004581e92a1071004d10030401040c000d800e501c1031060307510724040c400b039032002500704000c15a14050300c0c82d400a0b28110080041100c00c604542d982485a14607910b8990 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 286109973 1250 286108723 286108729
    0x2318060115030902041d0c0f060a110c030a05151e190e010e010c0320070305091906050a0801170705040b01031e02130b07050303070c020406080f010f06090216080306 73
    0x7100420003900720341802200740c400c1c2482111b951142203910120740d410240e03101004141c503c070116158000324100070144c0c0d51486055146041420101110440030940001c64604114058159615000900c0211031406010001a0441032030712050294500e0921543c2540402420740c0c15a113031030203506041c0403030641114551001280c004c0140c1c500e00a0340d580600304201e052000686401c1c441c110a1124486021031031000c3c41380c1d9800e101c603687d425111540801c0f8100c0d070000304100b0110104d10800c103402d0180c0300b995075082e220705200c2d8000d810140d060704100c1444506161450322101d0004a810440b40220380105460701c020005030010910b05100c246801e10001d811081c801c45034004051780000c03881101c5016a03201c43d18107440c054104000e003990810004546500d10032140c5589403400100b0004080e5030b00e6002c2450001c0d07059255079141d454084001040540d403043ca001801e1002040d841c1c81741e0300310012401e800c80b41c0010018200031000c03a401b51 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 286111223 1250 286109973 286109981
    0x5010206150906120a0606051002030a0206040206031f03030f08131109060613080c0f12070b0d140f10060f0c061d0109150f02130b031306231806011503 67
    0x56141300035603010140504004000d02514001c00e4010400c001c0d41e403850070f1000044440100d45e0ba070180c020303501c1e1542080601e80c4080c000103400f400c0301c441c1101030348070821420011031194407000c80b4000181d101400c0050002d000b40040040055008045000f902d990040d8483c21100500207170344d06000200c2d980141c00003442e40003203003103002c118020005001113034040122030399568440003c04015040c0c3f8914024011034008002c200081a8100060054001c18000205020070b004065a1168000301c81c4a030303482c0b08140034840c00d009214203c40c00360010b45400e50202e555040c014025030080c1000515003035640503200300540e1115804002829064000c0c440318485007040c911100c030844040041504c1e100941d898560035108403280d081c010100046260720f090b84840032508004d044011800d4a441e4905c000741d580d22808001c50201a00380620010560328035090150041503503500b855080c89505c0304100000309541100d1004d000c0590707044011000b10064 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 286112473 1250 286111223 286111249
    0x60612060d1b1d1029121501080f070509102607110c1f0e0301050c0301080706090e04020d02150708040e0c030717070e0a030602031005010206150906 66
    0x1001c00e140100350240f001403031101d200ca551001e0510b42e16011880385458989100344441c05510700c0d0500000550850103541e0680015555400e0481c001d0724411070b10405c07202114500c0504020303178420f603005400329800204810501e0340d903250052000e01588528814180310380358440b47c418050384118a45c40142c15000c0c100300ca8868a080d0240d502401a90741c0c0c80450190200c0090304100007654040d0490004c0c0117114031032104121110b0100f030b0714004030400c000b400368402941c03024003d0f80c0c080c6600c810003503aa985420381070f50605600e900000200610340340108000a01c03000c510b030300716404846c00240c600340380c40014004a01000032440001c004039a00c000d00404501800446181c40e4f82c1c0c6030710350380c0c0000c101110b10044420b1b5000c100c1200e02c21b42e10084880c0410340c05a0070381080c0802c43c2d04e250005a08003090303801160030980000800032655007214441c001000d0a000410460070300381c550960000080d114103000d4a05c6000203059580c0e00c405024203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 286113723 1250 286112473 286112513
    0x12090e1e1f0807170114070c320f010b01020307020f1905031222030206030a0c03150909060f06050a0b07111003050f010602030405060d050c090411070308060612060d 73
    0x10f01d65550014001e00d1003a859440707015440d1445880c0450b12409003e446408140da03a40008038150355007203c20f81180e080d115a14552210801d00040508031403100c903189d000042c00301d400c0b0880b0075400d49484001140c1190014080d0310016110703000d6010040200326100d5900c0c01c454603d60010380100c0c2e000315410700c030700161044004c0341c0c40020040c18088540541d0800003e948050750740d6142d10000750040b4003000000c00e0180b0076404000000380c80c0c50003284030410455000c0088005401c4a10380996842440080050511561701c94108a40c01405510324200000d000004a032241e610b60300d100103050381c10800100040031900354001c2c40c45a0703104043d003004009180c125206c80c0c00051070f500200c0c0d1130f400002503500320381c001001a03150048030080360b00604000b0781300b03e6441806002c080f0065541e8010301031640c03040300d0456201c008604004062407400f030101c500030319040020b01c000b885075000c00e030350129042c0c80050801a0303502d00040d25942150b10703100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 286114973 1250 286113723 286113733
    0x90e0a02061603180b040e1e1501030e010b030309120118140637110304030f09090b01020a02040b130608060610030e0606040902060712090e1e1f08 65
    0x51821901c42c2d620b107425002c4c0d03032682084010289221000b0007180941840c003a8144400c00c13107051a80e80481d44040b105482e050400e1841004400300c80050300e140800176000c0c1d0030413056582c0751203190356106240c40240184403080c0c0c0070035140d1007020f810398010602d01110b40d820030001d4001080421003000c00d005d03402104d0030003d1024180e844800700600075180802d1030128000e11001003059a5080c2614044030340707014181c20b0161072181810251600c03000c1e03801c1100013001c0c0d40314034000e07266100040701c440c100030b00b0b94156400502c99149054155049a6030020390328800d030354152800141c4002e0000080c5100c001100065102406c1030400b05030584045122805018140e034001070b50f0a618100740d003550034902109105900101c0012918945600f003000c00c6070015048038035000e000d44480040c0941190b1240c041010040200507040c2c507184030340c0d44246840840d000700d01c003025509840c07040c0540030020b0204406414909070380c500e85000010880982114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 286116223 1250 286114973 286114987
    0x1802010e01050705032d0910112803020628090c2301020c01030b011e03060b0d0501031a090d0f020705040f06080c061306120f020c21040609090e0a0206 67
    0x141d1200e410300c181701c0e05141c004041c514124954040c1d487d04e500c0201801003081c126802110000c503400f100d408644615410790a0a02500e0b0044a1130008810201c0e500940d0f8100603241010242c42416034a0704000c044911a10b03d48100141003248003004c5501d0701c0505005c0000c052170b0300a020b84205034a69041c0070300600117241a241c0c82078003607908003103145006600b11000140b08074042400c3c130307012076160724180c004c080016495040010b1569210141a0120307040003105c5500d0aa80303000500c2444404144070620a1440300300b01c0c96441d060724031544a5102082070030a00c49602100801c150080c002d140c00f0700070140c01080b0030162070b03241d04c0103480740f40b141d001783e4040d1441c800100c0c240001201c110b08a4481282c005c1881c2443c110340d8900d00610820446a481d03103814802e2544d070008000c0222031030300800c00a9041c8030924002d6517040480b80d00403004100c20480c681d00b1004881c11148150702c00600e80080719445410010f010788020f500000000e0a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 286117473 1250 286116223 286116247
    0x80304110f0a140109151b06060803072307180903030b12011a0a05010212030702070504110304021e0108130c0b030109021911060417070203060c0c0f011802010e0105070503 76
    0x1003107104000345d0310064142e5540c901030342d0b485900c1c042c04002844000d010715600e0382c0083d80090b02486100006003084c1d0380c40311107040d50403c60b4101e59076804103007070440c1121104521090150030901501c22103103082e6132084504070340721503401c1c410b407140070310700515000303501c10500320802030310280b00c5401900459001b000f5070401a0302c804c120708880001800c141c440750044d00e0040e00200b141a503041c280d40c6064000038104030452003003103c0400c5130346960050f4000310010504403034076400c091041180c000c000c100c0c04002150051142d21640c0c0e440811a80c0024401030542c2944074242040004610b113900804900340000000040000880c0d00030100c40814140689440308005021212142c001d49075900c1384d444072003c1070100301030084010300003000e030920a280440300d901090406604a03103140340c5010103e5403c2011400780044000090350900810454010414810502c542908081e040068105450310564004c00440f20121342090440e40c070380d40329800c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 286118723 1250 286117473 286117499
    0x91806040602091e0a032d0302010606080a15030809010917060417041a13120501050108070504020702090c0d0207050a061e050f130201020c1c1a04080304110f0a 71
    0x201130081048642a181d010320b90058410601c030010401c4116a01e10385a20209150344204503654100e200101104170114401e41c01c5002c0c1b09400108000b071030040068000b14004116080c0075040c600900c50300c1005c004d03404150b035406040c1a844a200e000104c8450384550048866141c0100000015400003c1d40a102d603100c0d00d044040c21450410000840c0294440c4040400407103910680708070b0315802070095404ca46036080d000c40d1f501c00c801103407000c4408050300d02da59940300520000d50280040c070041c0006480540c641240fa9010402c0d0680050104c0c0c041c0d00c011640e9200e24074503030112007400703070481e003194020b04c0c150405c64002c20744c0084e514420580701d2041700184d02180141485202244400384c196035030780640b1084407140441c00c9046004024503687d07203a46210201c03079480e0101d201200c0866042c984410100710ba6007020440e0520001004001039020080b26400740d4001d03622606018010082a0441d9041c208540d10000c05600451b1800120103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 286119973 1250 286118723 286118737
    0x602100e21071205040506030a0507140d0207060606110c060c0304090509030414010311041502070b0d14010503010b0a3015050a0b03070b070203070801060e07020706020303070e091806040602 84
    0x1100c0c00f003403d461000d460522892103100c0c1c02c040c040c00010b41c109042e030b2041d0b03840002414141e0349a0100707008607105500c400504e803411a40850000144041c9201d440302801c3e460500c07007510482e0b2854180e6a500b4501071034824103000800800c902e20510a0710014118120b0074003c608100070b20359140e4216004400500c41104020b4547e58424000c101d2258084280344c1c0c1f6007400c0c051000000d4480070446415482840c030005124000d45009110000c2c188000198124041d01c3c50400b03540184c0c080b0340310740c0c10140b416031030766119412071084518541034001a0421030302003002941c803006041c50b4a180c134403800010b200d24008101340e032411981c0700b080265544030904045503c0c480004e40c25900c00c403820b100401102000b044201e000508560032039654171b040d1425038001e60016002d25103110244048260108040d4025118a0020390306500d80014000c0c24103540c071043c10321513500c2001088450440310f00c91001c00d0000402d41c1c1081c64503080c028081c1d40140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 286121223 1250 286119973 286119983
    0x30f0203090106030510020f040b030702031204060e0708120301170a1a07032405060307030f0501120c05060c0d03050a0603051b0108090307050309090403030b0315060a0b040602100e2107 82
    0x143c114611032106e8403c4a05024600c03040d141440d090209107540e9400080c401015440204100c040004542102e5807045109590200e40d80003e4089a400c0c44119030050900d5480246200c0c00c0e0250101940d055540300e0284042201a10441e1480c0c000348000203440c4080143c01040c2c0400442c00c0300784601c2a9441c144484607170464043d0309001d40201c0c0520000c1424018081071404000035500000c0610b808654501924441c0341155003e0b07100841c0f001500c4168070070000080e0304400201011100307141001140a070003a190001e8045603804c140e070355000510f184038694800809140c000044509046e524600300c070042818200103800b18001000243c06594008100c4000c01c0d88900a1814201d00c0801e02001800142c03084040c5074030f50010ac00341f604c04211071480e84811a00880302e87c03d140040c4540595181c1001c441a40c00700004d0002a400051401c0c6a0842000004a80d440715020303905103100090084090000e258140c00f241c1092405010313014018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 286122473 1250 286121223 286121233
    0xb0c01060e01170a020409051018050f030f0d1e0e030a0801150f1803021c1205070b04082a0a0c0b0a020a1b0e04080307020d0c0305030610030f02030901060305 70
    0x300b40300f450f82e100001140307825901841a04006041c81c1d000710b003482d84100c00f2117054041111414080d54a04900021103900701104081480010480d40c088055000041c52401504404409952051030041004151100c00280504180c441c10b588514002d00c0e08106460592003219180d6001c0f07184800050400400825000746440c06a00360240381d4881c0c2003400c40b849400e45017052400c81009400e61503603000005a110f0080b4440005116840a0b641c83d00310324144007804010110602045014400c0c43c0001c2c03640e012680d04907800022030742e180c01403428861001c20485800c4034040c0c8908440404078400040d50100b51032207202820541a12202428420f00030030850381d00582c0041c1c2842e002c03a0b115509001c40703040c0750034445003c503164840340d000d90300156030807107001d00000300304010281e06000c1a0081038062400f50079080007514010f01070300010304824841d00b9001000c3c403120303020b540003202500e01d83c042035403a440c182e88400e000b8103061105640360300075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 286123723 1250 286122473 286122479
    0x5031507030b03120a1805190e010e0c04030b0c07020d0c05121614010203040b1804050609071d0118030b07090e0f07030f0b04051302030c010e010c0204020901090b0c01060e01 77
    0x8086001c8910030b95401c1c942d070401211500032245108100340014111b000d000000ca15034980c2e440d0000000111103040d640d8500d48601090b071044140c0c00000302e0300c0328000380142e5562100440e8101d907080044001a51203003131032200140b04902001b5404024142c0c100e0411885074101000c41d00210f0740f229a5040005d5000d80b1402d01c541c1008130148158011300c14007840c070201d450300e4001841202d0409444000130700c0c041d0b001e99500f08450b0039207910100240f416000d070719031104080e41c1490441c10540c0b005080c43e6001c0d030143d00c61507085400582c26902c2030a01d0441c401e9100c2c0209200340c2e80b401c284010042c20f03074160002407035812000c20348405a070340440c0245107800034030809035142402240148840b01c511820340751116185602c9544500503503008401d88813650b4403001701441010300d8400030264407030502101c2d00300900c850b030304540460b00041e010758015076200c0d010300048904581640090f219004082840400010154007650030340d003031603d0052299072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 286124973 1250 286123723 286123729
    0x4240801120309120317041a0a090312110c2d0106031205070203070b0301061214060f1c080a180503070302100f09051c05061b030f0403050405031507030b 68
    0x3061400035000c615901c03000c2003204498910354901c04c5c001d01d40400d030703d150304e20403a00d001029501515030000302210103c8441004c40e055400c814108410420264540da010781a00c42c00650401950341c1c0c2d0804030b001e22a42c0044400c2c404405066482c1d0b08050f5045620b140b000d0000400d01009140440c0c0c5486014440c44090f00e8108209001d481d103455011101d9601401d1300f281c042c0111000000e0ba00103100181d800307004030f40c503520450b5516843c00b4045840d0a40c20316181c10328007061001c1c0f03440354840090943c10a8030044c10b007002c0342e5049000600d1805006001140003c1c00c034240c55405050ba0a13804840b4550a480c20350f91070800d5a500d40c603010295028032910a03e100050003140000101354160500c2c5414980c0c2d00001050208040300900d9802081e06075801004010312009501005841c942e0002101c81e80d10b4484a0000038040880020204d010a0502d4003620555004040040c216501901d071a043c0449028003582c03c00c0100f41048e001010340c1c9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 286126223 1250 286124973 286124999
    0x16060e010608240a0b0d0f03020f010609051602060f0a0c1704060519060609090b010e0d0b011802031501270603020d0f0c022a09090604140a121404240801 68
    0x4d0360081074946e94441945800c01c070861f03140740484c1548103a0200110b007503002c0c01464014041e0400028440c030b42500c42e900034000521801c4110340018040201c0b50781c020a034260400744482000034160b0010500743c4070401caa07840039001c19054400c01040001c00e0300036901c15201d070b500329155903200060b6401031745e0fa540100408580c1903d024000510b49a00200251105241030103000e0f1030741d4003140c40c0c2001248161150380c440310052100d68000242442d660444c0d000452031071600c440300000d000c00e000705007410000641251055101b00b08610b54403601007140c09041941e450030040c00a60013484410106030030901d000440801d5407290900c01e451a07009004030900c901407005940754000040609050b51045001007500c030b03894100c3c80f900d51200103005908060a0480c481494403851005545c08035403144001402122103040c40503907402c000c4401c031150140750983d406940c014103031048c09a203640031342c54203048960350714440396100c00050f6603e0794a016440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 286127473 1250 286126223 286126241
    0x60b1b030c031603120905010506040b060703090b0d020408060106020a12030c1b02041d06240616170a0509150f041202041107030f02060c16060e010608240a 69
    0x290300305000704034200903000d0921210f24401d01c0c00390b20030300c4050203010845054107800e855681d9035a04001c8141800d1040c0e0440030f504a585905107111340c0e40050600410340036007540341c8404165154000b5881d01901e0142c0120001c4d900c1540e12000020b503555840d400c15608150085aa945454020300c0b62602c1ca40581d5100c2078040043c203014100c061100508a821640d242841c1d284030b41d541d414448a0365040001c1d0040d801c00843c2c400c1d068240d1103803c5411448203860401c0d82e95500201d841e407030380c10301004074003c0e0a800c2010411001000326000c04000180310001035074040300600d8280000c541280d02528241c141218a01400b2100111420104000c0c80031a481000c40203600d0710080000c20007003034030311305000f4981000030114046803000380800c45007501446499031295410a01d1030030701011b00b0018018065002018203465680d402c2c480003010203400c0b10004d003040004450030980c1fa110709035010400112100ba500b441c14012980e0003001307024400039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 286128723 1250 286127473 286127497
    0x13030503071b171803012d0f0518010f0608061302040e01150512010504030f080a090b0916090203040206040308030606040f080a140c240904060b1b03 66
    0x3541d039a000c06964811420846006180d00d4091560003d5450300824160812143c0742e00d86034501445140488564044540d12a0341480803401c51000b0000c00c6451003403007096036420030340600c121030004010301d0400d550020304042c00c00c01c4c1c000820021000d41c8000400800c02090b44401c1e150071212140501d01894100c0804104002410200000d1007400208006800d0369821565421a003420140c100c401300080e808200384e20b81220040303401d8220340002c2c006450710b585c001b001c440b295000e26007403042180100c1d0703020000b5400010110381c440610101420015004c507900c030b06808403030098201550740410444d01d503000342d0b800b80381d001d0000c81c1042c3c21640d078205c86400c000c040c5030300007005100000745a009029070340c00810aa001500d08000141405003801c0018010420307168050219001c042d1212151850862980c0201e04914001c2d4000c0754054898a90740c3d69000f801c0050109140050740018204142320b44d440507804204504116181d0080c041c001728 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 286129973 1250 286128723 286128727
    0x3180111030705060c0c0114100302010306050a1d0415050a15120201120f0e03030a0b13020306010c0f030504090e03130807060503040b0601180308070303050c0c0c01110a14060708130305 82
    0x328415417405001d2198440001103400c000c0b40d00d403120720250498840307041c610043c07000c00075540c042c40380d803000e00000d44011030030ba8141481c101e1010b6205c0182d0294090b07020000d030620000c0301445c1d03c4c100c680c810602c000d0500032448405400090082003600d1a0400c0c000342040040c00441880e55044e100c2e1491660085420401003460010f200c041e0780d02c444086000c071000740025445440c00c40c0d40028826500703404c0c0902c0c07840001e00e40100610420912000e40c0c0c00c00d810701c501503030003102181115003915084415000e5507110340704403401d2000711511301d030340031028181d4186021540d80d5041d41c0c8043c581d45d5903e481c031079040864000c0001c1004903039030542442c0d0200060508081c071214041d07100184001a9000307a50580e00400d00000701039150240c00c0c3c00126004032107003003448181000da103d6045000460601c11010024440210280b03c4010b0719a0003260049105104080703540d120700003110309000041c25400020b40152982c04400a8150184d376071034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 286131223 1250 286129973 286129981
    0x130c23040204291209071a0f030a020702030c041104030b060904020d3323061309030210051006121a010305073c110a0b10080318011103070506 63
    0x10720801d550320900320700407013041030f05400640c81d81c00d03a014004c07800081030381a107001c2d014890001030110814046408010038490095502c042c0c07034220000020041c0d513185a031002a18042840c0c40ca150400c2c1000496540d81d9551400750084034020001581c40b59035a101300a40510101e8009500c500428200300110320350910b50b1601c5812400d140168042102110102e03011407424483c02c0d985411241c1d01c00100c180c41c01c0c05028605079400818244080002e0314655942201d620850380c8804c5042818420000781007604201401000f07242040800c0ba400d4121902800d80070983c0c005c80682e0305101340c07040681c150350303500540f0100902040110050003000e01040b0407c0008001481c11020700700f0b540f440b40d1200bc210804603907040048031900021107d9440070f001e40c24040d00071060001c134400340b0469000b060807400e45e0b1911014404070215810448040c4008100da0000142c1030035041a08a82600c0b100400c3c070360305032207541c0d03032007401801001070700060085 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 286132473 1250 286131223 286131269
    0x60106080c36100c0204052802071a01030c030213020f030910050105121e01060f15023c011b0314010f0602060c03130c23040204 57
    0x181d08080c0c107070030442c50010006503a08030202c041030030910303018100e902c10000d0751a9109450720104140c0c0e0720111503021410280400c044010043c1c01360303444c2c0000581140f00d01c40440310518a004003a03000761034041c4158029001044c0840c1ca07690b9000f000b500c054000c68009040b26800074810244508540c24007080d003001c00c0000c005541c00344014050983c3c0755028610132041f0a0092511084d030082c0342e0103881c410317804940100d80c5000c005040c41c2011482062525000d04810a10100d03141024010001c541c4034000d00010b0030404103025140b1028003081c1c01c0a075088410390040034402a081d40b1004061035454000001348640c801c404601c0c81c0707101981c08000180303034050f010b03414038500c0c3ea400003200007039518144000c1022240d00554050094800800c2d100c0d0305105001c4c2d03445001a048085584010002a806907200c01240600d5944200700c19440c950390401181c3c2d40452076003c20308001a01c5e03200015041c10f1080d94210782d007566000b200c0030307104013031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 286133723 1250 286132473 286132487
    0x4080105010b270312220b0903101d0303070507150b0d021e041b17040c0611120d050106030b040b0f040f0603050111030717100b030720010c1103040503060106 70
    0x11480d054005c00d0703003100d2117403a50710242101d10800c1e00128400150403d131081d1940030303a0040c2d1004d4100b409424910348002400741803c60018600285200010820009a0f0034003100c403113031480300108000c5070035400000340c200760740720350544c84401c0c65204851007601c0041c00d034541c2007a07410403c00d01500d000500c080d0441d0b41d550305090b001e000c940203d001d40c0c04000c2440403450010940f50701c1c80e54170524003000702c2a004541c0303003142450796400c0303da18103604c00e0008010304c860706419240d80600c4284001c0f1841840e0300d640d03aa50f8200b00e40075150911516011919002c00d021282c1454010340c3c03402d4000408004600ca03128040000424010074000040d0f03035107090100004009100e20310070800710120940d00c03032516000003040d41c00d0124041e0884c40041050018404500d8008425200c8454600b03883c1e07580c83c50112031006008441c0c60000000007484592400103511200b411500d0750784640b4074008600d099507072441103210340ca403d984004010090240b207400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 286134973 1250 286133723 286133797
    0x30203090402071e0327051c0c15080a0b09131e0204020d050f070c0804120f0816030809010c05041403030702100e04140402030a0f02010e0a03030504080105010b 71
    0x101402030f034a80e0111558126100040417400300d111280c00c001d008a4543c5074600000b4612007098680d070038000450000d0394071944034140c0880c208010020031078032002503005024081400e000d56045075100a081c00000e803104002e007854100d03031148600b00f00c120f4510500c400c20152450003455500c080043d602456094201445100c503040180c3c2c440c0000c180d0100301c500c0220312801d20038034150304074402902e070006100108170b0a0300000c0008090b03508031040c1c0340c0c420400508030b0505551081c0c040d200140010000076284000f013000050145075a0700a40e1410007940d103450312582225220201030b001305c1c405000030810000103031105008080044c0640742485110b82c085404011100140004181e0030315038401581811b00c2039207400381c540103200340d0342c1c00c0ca9000b207034607200918400f5101c00071102e03042080da40154071406c022080580030924480c3da0f4100141a034000c1d000d8407819509000002618001038000d646103400380a08802e03520100b400e01201c0605816 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 286136223 1250 286134973 286134983
    0x30408090f013c1b030c1a0f070f02010b180903070b01060504080d021209010c0309030b010f08061602070509040c090f1b020609030405010e1906021c0c03020309040207 74
    0x94070700240d00c10750a003800f035082c00e000c00000b14810840c2c40c40981031032400c034003080200072000d09040c5010102c549100d01d41601303204003008100d003031121815042c41c8040d0000800f000134004020440301c00144249419600c0d020f00680989049083c2e030341c0302d0340407075008882d030401010981800d64003a4000306520b040b2440c000f03050fa6840b00c0040240d1007000401c03404503041241400600c16003030070300703a079102030590340481d00441052801a446014100210307002d1326000c041c060b0348040c02564200b000c458040da51240c8014180f21140100469401040c0c045882004601384025034441d940e006001d1250402c400d02c4882c04004100b941d0309440703c0c1c0c00283c3c11160b03204038000b69084010206a454000d80415480c00140901e001194450030422900202c00300c2644c040c0c40003440c3c0403038401710200000704007242d9880341e46002d021022000a10640008684200010140040c40c001c3c802030740a9840000d90980038005d0381040140c521a4079040e0700a001381c1c0d03c94 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 286137473 1250 286136223 286136237
    0x90a020c010605030610150e09041e0f211d010503071b06060302120a050d031505040501080d090e010315020f0c011802130605010518060c030a03020d0c05030408090f01 74
    0x90f00000e1324010080d03481d80542c0181d08010302c000765507090070600c480d040c0d040c44507450180d00046801d14000400290404541c941100c0c4004060f400740482c00d508411b14000010090901c45d111208010400790880356501c20044000cbc00380c26581d540c01e0010b2205101d400e103a0006440c1e503840104044100200c4154a00c1007071400a406100d450003070f0000a482c600358814001000101410004668000c100100c0000d10006020361410340e01e01c0c000c10606800303d803e0078860303a42c1d00b002d58001d0500d40045100c00c40000d22200400305503590001e580e40e00c01900c65040001e01013308500302e502c00d0035842250ba6002000c00326480215580340c90150610075084994031000801c43c0020049108154944030028031421310070000200420340c034040c0064264894540011280c0000c00c1c01e900a03659104140c841404034041030340c0c0d803070f00e0044004000354009009600c0389031502c2d900711111840b40065034804c66111418904d01f40040c1c0c00c00201f255039641d901d04015507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 286138723 1250 286137473 286137479
    0xb0f09040b0d05010506041118040c0917160b0c1203041a130605060a2702040b120a14010609120204060f090e010e01090f030c0507050d1203140105090a020c0106 71
    0x80c1529400d42500403c00001c0c01d0400da005c0005032405641441c0040320288440c689001c600f040c1f10420080c02c544c0014181604c40301980c1c42042507101c40c82580c0380161183c8d0400000c5800140c0603046455034045035118090119103000b40088010070780d021004000007407042d2802103070040d01918001e20381001c0d0001118408000301c414442060701c41440c4030410000e80181e42c1c01c4507046540a4000b4144116110103540c220003240d0480d4401903101c1c0c14411070f504a40c090b044c2c402e00103070744a4541d030491554075030594024041d60b20740500300801e51901c500c81416520303641d03503014445140004201e0503a0780d1040a0f40d100395600d0001030901c000000c510018040828046400b0000818a44c00c4070740510700011035906110342200007401800e001601258503003001c25100f000f40c24800d01d450460b07080700d600007031224818800d00c03a000000c024110f119640500c6a90a005400d009401082c803866030007404503000308100c0b4105801070320103121034800000d00706503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 286139973 1250 286138723 286138729
    0x5191e030807080c010b220b0607120305061003050103051b0f0d061505150a140c01090b061f1e030f1a1c150513080a091e0b0f09040b 59
    0x2c40010b00b203603d01400038001180d44001c2c0a01d02080e00704640100c6044d0105280c010002114880c00142070368a00b82c49505940d14002d80d00400e400c4070071003155440f004009401410143c50417071003050500c0310300f43c40034424020581a26804400b43c10070001c005045218100c135041ea0399031003400c0b0790724186151620301e00c2c3e2494500801011407100c48100c540c044001c10764020a0144900c14558070a0041107012a0301042051500b494110140c0352403000601504880900c55401e0284110030300c003100c803c5c0d90240c00d0490300007441e51261b03000101c7d90074a404125000c00c003241704040300701000202e04410441d49040110740700992080768011a82d400360042c0b0344015032400c082441c200489120000032001184902c220440d85481c0110200d8010885405031070b4000500002420251068440c1e8000002500c41c106143d010b481740186000302d075800f124900544d00d07410300c05414001111802d51280d840c00d240b00d865160554046840c0580041e141e100081d00d6031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 286141223 1250 286139973 286139977
    0x1d15040c05060d050708090703111c020a0305030a0810080d0e0604081f06050301090846020d020610090e0c03070f08010501080c180402010210050705090a05191e0308 73
    0x200000800141441c0c121705c01381101c40040e0224a4a900400d0f00b0720020384482104606801c049031140c81e840c0203101080070041806800a40054520b080041001000030103000c115961303448644443c3d80c1c1982114040a80c1d118008195220401c0300c003081d4060500c0350102800030740381504c8c040d00d60050710714241c401c1e520140b8042e000242180f2000e4548600c03006000210000e01c11080c150711000500c0c09020000d500f80402c65606952100d030007400e0301c000082d1400749000040b88850035400360340c2d8880d4100051b01030101c080344118030100d49540b0070364012402c90308141c100450700005020500903050741d807003807054040c401d94080001400078280b0003000400e0310b04014501c2d09580041e480300c1595840b03460101c1d1107072340c0c0b0b040d0181407840342201041550385a00040745071040c0d003035060f0f4403035140206000215074044001d101040341500c0301c5d80030940e507806000790013403c0026410700b00c281c0c0800b0f01520b041ea507200d4103080780e6a09581d10080c2c41346c0380c0b40555 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 286142473 1250 286141223 286141237
    0x30103052a09040201120e07080709050f180f0105011503051509150f03150108070b0a0f14070210050c2404030305060109030c0b040e0a0b01120209060d110304061d15040c0506 77
    0x196011407420402100c0800ad0600584843d200501072410888941d80000310094000768540c41600c410590f00e400400c0b202084080742c034020b1000f07581d00c00303403100c01150714501040040e041200040c00b048000d42090300002001e0030542490390b6202c1c40c035820a000141441e403120f01016103003800d580400400a11907000c4040701c00551601c140b040c03034111650f00036215034405000130402140c000025107016503560610250341c0c51350140d12000c6d0320030000e00039440010300034486034250b030100151a614024a0440b075025420881100124502041c51290880c000340080e001030300c603400558002d5018100040300a4607070b89c0d0401009035582010f145d00002040420450310000388041e040040120200115a4120b000030a56485100038000d0b86800040215503034461008075158003138808410050003c0b01c01480030540d10558083d02e000b0708140a0104030402c044000352660402030040c200146240011404200018402e492600710040000f0b200c2c0c580c1001881c807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 286143723 1250 286142473 286142501
    0x1e0503040b040e090a0b070e060712020109021311270901030308060906040605101409100c02102c01020a080d051602060624071205030103052a0904020112 68
    0x702d03400c05a0030f07440083c1c004d110107099409841c5102c08035488519040e009541072400800c444002004130b02603101c0d452009007441148107940700b80700d0381076014540262086030000c4c00071401803a4082582d0758040603800b180020840e10444212804040c080c42c000d1006540c013100040c0d0008012500c241d0094001c64031aa00300941e07484e08032102e90744003408031400c002c0b2608180c00711324946850303808e5005000c1501012500c0030702c100103a418666006144c0c0c9070441204500030303c40d00d10548100c0c060b0001c00000d0002c1d0b40141c954018182c401c3c41040850f41c20131800390031270070200805074154000e443c1040c001c83d00c101c0023072000b403420400100d0542401d16071002200780b410b0806045400c80070500c04240e030345080403621b4030720880d100e05d10503001c246200d02c90f1017210401000c040b00d082d01d04041c9900300010314100c034018000c0d94400003000c43c6640d03804071142580c0d01d21100c0e2428106840ca04004525081130040c942200705a410b80305031012500e8441c1403081c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 286144973 1250 286143723 286143727
    0xe06010b0a080c1c0504030c02030118020102161a0a09030506040f1a09120717070f050607031503140a0f083610050f0409050123030a1e0503040b 64
    0x500301c1d0b0045031440e00322045050b0300d0300e8918800c1c16080c0e8800501c100525058a420200d070602d40310b210345088450300100204a02c1e1030442001c40b003550303590b100700d0150003a07030310104110104140d02c1c400c8400c6440040c02611191801d031184d9444502c0d10800e1008500340403010070000c00c1f100784224462107030340003000141e0624074041e003103000003041c9400c0200c080000701d26002c00d00403803585440d0105501e0301420303e030000d81e0501c43c00321600500d8001c940c0505000e1440ca031000301174006c030142d50003a240d0240440544801c000b00780010140d2316000c00000d8400002c682400403400180d4180c11940d5492101003003990714151001440480c061602a150b0b4844084e101091004050910811541d840400624410711441000051003080e00240100e0413502a0001410100d07902c41e11102d80313400404003801207803917100032240d0121101858518041d05d03450024010008142959540f01104011500e280c20350116000e8040018104101820150038445c00640d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 286146223 1250 286144973 286144987
    0x213110702040f02130302040209040906020c0105070810061e0905040c1e03060e0a021e0c0105040c1710150807060804021c08030403141606201305130e06010b 70
    0x40d03664401e043d00f1554410410b0250b01d6030301e0560b20045076815200962a640008005002054007950140c40107000180103124020190f00c038900c41c0440d40c4a0744000c0c0c4603036240b040c07802c030207000c5c2c0070101e00010030f40360480e480d0001c0c0440d1190903140606005440f007012030b064a80c210140c6010440ca14460b106900169000c034442000515042105524144801c00710035030145c98003071030356070020b4011526045e64042d0560384041b014080d507102d5610360064002c0504407025600040440e01c0801c4080040411070408a0305170010086e0040512402c4000c003840d124405100112080029160000f8000d101c000d14040d1202541c07031400f4014007032201c1400020410b040c0c1c4c00191030b07001906900940f600107170145400c2c09002c84030048119103201c1d178082a9a8250844e0071034042000d07035041b1090a0400640d41483c8151039104035416024a1040e03180030001c0000520150804c2400230840c0301c10b08038080341e2a0304480c0600d007440310a0b000310040e501c001641e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 286147473 1250 286146223 286146229
    0x20c1e06090d0503100506071412120c0405150325200303041a15041104090b0d0506070c02060f0c0c10020706020604242a0e18040213110702 62
    0x10720107548550600f90700e58640215240c1500c1c1e594012070740300706000b01e640310030701291581c8a04404540b00c00c8400c0354039170001e020b803039421090b0703142c062214000010301c050405c2419107084480123480c001581101510503a000c0e04010650030540d8462810a0b05100c400c09010543d4401611901916819800c490001100c0c07184203010b6544208103100006440356800801c01d24042503a138456292070100c4844c44a1800001e0b50050400007810b100d00c0c0c038800180211100c442c4104940030000c3e0900200c40c0c0e04100140043e0489400141c80e240591803001c0345510040c6818500f080c2e190b26100980c0200e1450129a40441e40598544c06c11400c1d0303044049045c002880e06900d4140d00a42e07600004000415a10640c040b0381004800314446198101c4540800c0c091101c02d078000b4819186446480c042a842c8550546401c5020351030a2985050160511001c0320204100385411034001c0c2080360028111740c00007106000a20450005140742e980140d503800e054010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 286148723 1250 286147473 286147483
    0x604080d0b090c090409031106090102120123040b18040f030206060604080a11011b06090201090b090a0909051e010e0d050f030a110f0409140a09050a06020c1e0609 72
    0x1100d02680b1408103115140190300d098440d80c030021100405d1150b4103140850740c540203180c000c2d18a1207110141b20200e0019009802d0100300301c07a16612683c5c1c0c030480c10038a100c00000d400c10b00c1ea0354003107680c17282c101038020485c1c0220141101040110030710700c4004402007101d09540d9280901c05d444205a41400026003003441164403504241c203041036036072070f150f03440c2c1c0003000c0030a04c0d0765030301c074076400703070b006803c1088142a0072594200b46090140151000c82c0e022400500d00d5000403800e5180031042d201000000740c10141290709288400c4000e1000b40800c0d02d4500c1690b040c0f000fa400364a0b81102d01005000000c1102500e01c038000c0c1c9400d40010300102400300078013a052080711800d05803640071102d0100411100441c45064640380300c0d8400c49184058002400301d042c5159400501c1c0250a1010712640c075035908035458200c555199000f000e40e0010740b00c4201244494014111202c0c04034140c480c4444007548500d5507080171040c1340c8058124104109502c04203000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 286149973 1250 286148723 286148741
    0x2f0a0303023708040203070b04060809060703050705120402030a0c0b0d060e06060304030c1a07020d0908010c0e060a0509090a23070206130501060b13081605011d0607050604080d 78
    0x7840007001030542c048140c50304040320b031a00800403840009400d55038100030001c0104107441c81070750b5490b2240c100910301c0f5030881d10b8141510070980032075003951080c422070340300d06c03080e90b681810943e48212442c03600c038002d0000d0384c1c036124664540000c501001b490340d004100200000f581c0c1c3c81282e0b14031050701c1e00c540c004c1000141c4e05007000907503102c0b031007103075800f940c1481d144840039540e1070080b2081101c542c01c0b13140c10249400b00f295040d00001c01c00090355043d03d490380001c0c1d5440d0143e09076518003e9220000359002c0702e042460070801c0143c11003180328180b031820300c1c0040010aa195074200d60700312503180c54403203059000d0303260540c109144504680808840c0790220300a03640e088040d04101643e440b4001d190140301d02940f00c1005045030182c281c1d640c0040000043c070641d504d0141049a014004000011411000001d011200182c4450001129000e8101c0303060856407821500004100b01c450f00182051010a100301d00c51000241c5400e42070f41503200300c50364030b4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 286151079 1106 286149973 286150027
    0xe0a0507051905100f051e13051f0807020109020303070506100506031504150801090f110a120f021804030903050105162f0a030302 58
    0x11422800700c0d40100d0724503000c25509071007480000c0c094800c559100c843c1c0101c55290500402009285880703a003012410801396048081540150f10b10060200c0c000081c10810480102d150710301508054415001e504900a207400340d00b201c02000703c0038040c020001455003407003504035400007603000e01030ba5190012032410940c1d403a1f050b104946003041c01364001c901414031009a80c49106846e40c1c0541c04240c010901000b803411100c132030300b1940d9055020a060509000310181c8074803905074500501b0403420304509101c07030021964416a080741c41084540b280d016160b5916800c400c078803507240803500c002000100c0b580c240b40c0c0c140c00d581081000b4035800080f41011680201d0083c040b175510a840741c0c0d8060403111410000c5414001292403402109900c10340d681103c001e909607400e410396910b0324041e080314040300000e40003d841041c0400810845095200b54 = true := by decide +kernel

theorem cover : BRFrame.Cov 285971223 286151079 := by
  have h0 := BRFrame.cov_init 285971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 285971223 ≤ n) (h2 : n < 286151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
