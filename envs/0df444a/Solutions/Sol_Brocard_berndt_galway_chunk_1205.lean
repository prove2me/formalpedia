-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1205
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:45:14.356021+00:00
-- url     : https://prove2.me/submissions/2378ee3f-af7a-4e38-b50f-da9d8797ca8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 216546762 ≤ n < 216726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 216548012 1250 216546762 216546769
    0xb0c030901090807030c14010e0603190b010c210507150e150f060909010209041a030d030b0112020f1312060b0306060a03060203040f1208040b06031c11011506020309 73
    0x18980c083d0304241c0c13110000744080f944100e411411a603131103001c1400d190b209801a50310b1311071072a00c181e105d80048104220f00540c506104008a0328900400c00c2d290b0000054601c0010120701900b90700082000702c034103010340514900700d9013460528608000880e80d0340c42c10300d0351100810344019283c40188240f05403c001019101d0040381c4440e80b1072800a0009510607402000188540100c2c0e010400084082d0f049038040600030344244021518810070b0030f0a100d550143c240a44140304601c80d08034800d2107083c071078540583d0360000c41041c80d0b203818065002081c099070300141c1001404480714180340024010603400d0040351040c01c090801000b220700b5840042d00a0304881e040003000ea6a840f14042a25440320300180c50b6100d600700b81400c101d031181c00609408019040d00070442e0403400b90744c0b0482c45821003008583d2090245603c50410405036808400086101d107804e901810905000602c01c4000080342804503402000c5c038140e03548140003603040000d40804070709 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 216549262 1250 216548012 216548027
    0x15091207050d02070f0605120415240b030106050406053a1a010206190f061205062206020703210509190c060f021204030b1501030b031b0a0b0c030901 66
    0x41d04070031485c5e0142c038100300505039104118421503240000f00026042041501c1c1404084c064100c04200034188508004142d50400c0c3c104c80503004007000001c0c44031041e40889041e958203a0340c0500f4145030600540c1d483e0801c0070001074884a10140306412185602c0c1d41041003000c12000b868006814200f9003207a02c2d140c1d041d10540560301c100d43e01030341c00041d0300341c1120005110400c4504031000900003400008031030540c0c82c1c1400000192107031808180c02210b4062021395010b501c0700600c001100305801d0344c50105403580c610040c003103180380d4050000d843c001c0c102511420f459a204a4030005c4405c5542c50310342e50742040c0a00d080d02000f0310024080140301b0865014900c0e1035070640c80d100380c0f203403c0404c4410200b0a501920910410502d101d181051075107498480c54500c151820450b40c0602201c0f01d084420b40940c40b0340909205c3e00030180c05003d4038004642180c1c1d00c01c040d070103040c0d00001c62000002d02ca90200300180072001405001e5922000003100041c01803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 216550512 1250 216549262 216549269
    0x30209071b15110735040b030103060608070f05040f0f0212070207080106030809100e100e030c0108010b0313050705120a02180603030a0509040906020d0f150815091207050d0207 78
    0x1000f040c00720800103048010320880b07172001003000d20300d800d0329513003902004181030051061496011400041c00b074030070809141030340e2041600380012521410095900c08180c030550307041410984040009060a0380036a80e001e1035070790049080340d07800002c00c05a9101c17401802e4034a8001c000c110105505001c2c00018088020013880341d50f00e90785070b9021502030450f03039a2044030b1001030540c86601400c10403800d44c0002e08500603102038600080c210b10741514440340280620f984803441c82d8880e9207000d050319441e114603415503d44000c0c040480d11800030440c1d0340c1c45450004141d50359002500303c01e2280150003400d5180302841800300074022418401c41d80221441440107035600441500d4843c42c103494056161501c4030006405000c101d0030203001c00e4030004214182c560715410000144442c800140300401201c940b0100c808064464000e064005440089510700394003071868000c400501201e00c0c0000c00b000340701d110f6202e02c5044071558041e0b01c100c50550340511020006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 216551762 1250 216550512 216550541
    0x1060c06110a02030706110d0e060109050702030301060801090b030a0506011e0b042601140c030405251e09060f15030c050304030c080c0f07051201090804030209071b15 74
    0x1000c07440d5401079075174000c9140044c180c54440243c2d04030345011400f0380e6208129807109200c400029a50951244ca007270080008960070040001c0d0414000011207040b5a0395645100043c1c0c03a01c0364100042161040e4660b0500801e040c10002c540100f0100e030180503003281c071020a40301c8000220b0040e245500009402c1003d000c00c2101201c04007108410862202000e051003106e211514010211080600e1410a182082c0500000d82c0c202031803140c0c2c0700f0303001c40b00d400744880502e002000c030880103884240a0240180034159200c15404100d405800c07206c5c22094680404400750750340c41d0400a60200802c1c42080386455501081c0c0d1146402d003001c01001c4103d213401025840001c2c806001d016241c500042040f82881c101c60705118808181c50400c2c03a01c0204945480c2c0911409200f44008007072240820010b100d00e945081e4820040751415240d40e082c0040c0107401001d003001c0c0041d4600310303440c00050b241d8080401d48540000080a200e8400c50707012204101d070b06816 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 216553012 1250 216551762 216551767
    0x1203050a0b031203071121070c061e050a02010e0609150601050a08061c02060a02010507020601170a0b060307050a120303050703060305061b0f0a0c11060c0303010911090901060c0611 80
    0x40b00310200489170002210f1400a030b110024503000e43c43d0150790703071a0180b100c40407021024295201d101a00c220780c42503c9a842242d038800742151000408810010b03041400c03540a20658020300081c1100d00440c00003160628814103100d080040840700c4ca4016049010320143c9507200c2c0c000c00d607121000b42400c5003444c0c215500100042d2005181307501a662148a0300031001000540103e207503801004030359910000ea00081c0170300025640c2a02510441c00080760540b4440384840100511340b009200e41c01403600c5081510001900098140c010040c0224031500e0740c07074200b40600840188464502820310340102140c1d0f00070868020140350800c00d10000e840840c0d455042610f6415806080c841c1c0020300c41d99100d01664451b200c0000600203404a8111004203403150203611034030300210351402400308901c00c1401090342900704200501043d08160310503020840c50f503a1150800d13a500b404645400c1d002e07004039020549946a180c07c002a42c000c852070011900410750 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 216554262 1250 216553012 216553033
    0x20c03070602030c100207030e060417070e0106020d05180901030b1e040c0b030601021002031009110f0a1b02061201091803051e0c070e090607081e090102071203050a0b03 75
    0x30b0701e6005e03905000ba030891300020f000c402e242c4524511040305200410b040da4640c1d41d0401c1b401424000c1c14000114051000002032065402212038100c810540140101d6002d08100300c40d10751222001d140d404080720740f140e105031220840c00b07010750302c0341c2814801400c0c200d030819803004034801c0c10000403109104000c00100107000400031220584030040d2a42c07070340f00041c1c0c10000c1d8001482c140d50f10220801c611101e19844074030441d10410010413107104c03a02c40c0c0480911803004010b035281802c1110308140f600c100d04c00c0000b40002402811031514560014040d0750080ba03111000e802100010b1000204a100c0c0440c03820b0710222466081c0310f90b40c1e018144c1d01441c80010340e098040c80b84046040f000354225095900414250b59480d82c80790308900b000982907401201c1445540001101d590040001ca4060241403c0c1182c6045015800e142c00c4031008140030a113540911406c000903a252a12020015060b20040745918160788040112500c00c842d40d44258403901220 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 216555512 1250 216554262 216554287
    0xa02071203050a2115060306050406051f02030403050a110a06050a090312090b0c0a12050c06060904061d0109170f030a050a0e0d0903110405010506030a15050d03020c0307060203 78
    0x1d0344440301a040c10a640c4c1c003428104000e44000e8800854074a04014819080701d0044010784151707906510100200c82d11181400300b156003d004154009a4040d00f500120003e0f40c0c10b021483d213240f04480c0b40541302d41d6620b040c00000c1404640740da0700303080c4400007450408802005040a86440742c20300f501c1260050200b500d6100103401031a04840c80071031540328102050142041044e001e9a80c00550f10140e0745903440a003e43c6c01d070021103400404c1c1440781080b01c02e0112000300030455900c6860810a04200147c0204c07103113a5520b9031300c00800d00d0300440d240c4092242d00000360101640c03c10500380541c0250300075410b2810401d005080d9400420b9039002074110b10300146540c0c0341c20142c802000c400c0000c4c400f6110300c0e411590003a0780406001f0984e4414100e01001d039180100340815100b0a0246a83c481d030f05100247c03100303a482c0d002e951305104c0e04410780b41c81527032100458aa04c4903c0b10540c0142c0000010041a003010404c601c018030192004500e040d17441c143c00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 216556762 1250 216555512 216555517
    0x1219030b030c2b08030f1303090312180b180103180b1803040b0d0b0409030909020702010e040f0b031905121b011803030f0c1d04020c030309030a0207120305 69
    0xe14482c040210000b4081080761075400b06983d50300c26a00c50b299100d040c01d0141e50130459058010b01210302c001411205185003a00040d0750584404015500355507d203c541101c0c0c0b90004200f004900c0c0000207460347e100c01c2801406081c502a56804140350300d10703100300d034101d030090500d42040d0005032010400d01c00301c69810f400c0310701c4007441d07124401d40b8602c100d40485120f00600c030104011600c2406600108845050354a08110a95800c0240815103a40b080c0c0500424103841d0200810421500106552881450300000a40818000030304641382c450405402e43c0c1c1e9541120240d0801b00218181421016242c0001e10034660b01c4559415078a04152400c01020a18150100030303a1560140c00d8000802400300c600e11408032815649e492b8815000281012842682036140e4441d01188200d00e541e00d0b140109181d42e050301c60401c03400300c260401d07030800107041307008401e0028600a040e40c4010710354902582070001c1c80c200198201081400801c4101400281c02004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 216558012 1250 216556762 216556783
    0xa0507050f0c011b030e15040f030509040f0f0e10020f0d0e030c06161412060906010e0307030b0414061608060a1d04150c080402041d1219030b03 64
    0x21660703545100b822002d0252011354142e210707581404220188040d09600401307481c607040011210328a0f081c000c910804e0000303440141455a03810804808a03101d00005c020b8164042c00100300085500001c00c221030740c20665600da190707681180d1403d40300074000d400380348403902c13002d40c2009255441e0030340174490200c0500c3c1c3c16035101c400454001c403c2c800d030b485d01307103da03410742c1c10620388100e0036502c84000700031010001d0402c900410301070040d1020303204410140305424540f40d8130300c010b000c601e0f280a005281400400840a240c6a604000d0074010354400c04000c4850308251412924184448a108440d40c00480c100480c058002d91206180c941d5481e10001c02e4503010007051340104c2ca5007050b001e006800310b04180000021107154041d51281030038083c04801541d000080310309005000740025010b101180241c90309400400301052441306d00c160300c400c0400c6e080d1801e500754071051021840820098504c5501c422030000940190401740082c542400000b52070341140003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 216559262 1250 216558012 216558037
    0x605010f0b09040b190801020a121e090804050a080705030705030312070c0c050901080c2d010c02060f03091b0405040b06010c060912050c300309100f0609050a050705 73
    0x64030f000a07610003040c0450505e00b5004014156203a070308550203584550012400714451800401c002001d070701c10141640326009415900d82410300c80c0388040c01818200f500c82c0d800a10000c6442cbd5180300c0080e0042007000d0003800c90303500c1c10342410300b80429544914030a80041c0603c1501c05002d001841d881a4586454984009140f6144841c20b10301c1d08038582008503100082488000050b6400581384111000e5980b00c1051300e84075011185001052014005034460350700c02e50080c409044000e2009010074203000d962008056290011078100f44c595103e0004440c3d45070414100e08080c10080d1000d000c24a003540b62280b00340009410541003000040b41041030120680c070443c4081d5000304001c3d110b048180300140f05400c1002100c480d0b008400e030880d03d0744024a9106c24480c030380203014903050303140e00ca060010303000204489124003600340c495000b924544101c40c118640e00c040000c59509003400c240c11540010200c1d1411403500b82803203d41c64222003500c20f07464441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 216560512 1250 216559262 216559271
    0x209130f0b07110a060b040f0b0a0506070827090703060806070807050720120619020a0912030c06050c1e090103020c0303040b060414010b0909100806130605010f0b0904 74
    0x1942d085840340c91540844100e401078080400401803d500310500c0359008950074420a8000c902c154200d030041444941d0112410104012605141002e41140390141003510b0030f1101c40b668641f0084451840d1305c01080402e00200c0e410b140a09020783c12410524003041170509202d845640c41101a104000b44801b500000e04014880d4003150a003940c0100d001c80003180d2840010104a802000d130f62042d09a0aa002c180e9400055921f100b80503810a4520f011000c2c0e107005c0081d4408601c5800b00005c0c2d00d008a00d00484898064041c2d100c1d903610a0707038210345d0230014100e40000c0c10300300180b00100600e0040001da80c003120031520800399090b59941000340180c00174820302c080300e02c980c000442084140711212981900c520780546090000200c0b0394090500d00a09018420141006105041c01c40c20a4183c50303901c6000f01d00000041d60b00c4012a0f460503008403807a040190344401400c040103028051180185050700200c1000c9050144103403c1e03025046030341e07000740d554 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 216561762 1250 216560512 216560521
    0x130503090f0d02040c03060e09010b06041505070506040302070905060603040b060f010201020c12071106070c061d06070b06010e0102070501021e10021902061b070b0405010f0c0207030209130f0b 85
    0x900b860201c0450b40204200b0516522810140191801e48104200480704100040c0c4a0806000d16018008010400b80c945401c1c24582100c0c00d1100101c02d0400800b4030207400040c404014a40c000c500270340040c043c07075180003000001c0d220018078690154000b40b00f440f0014004041071500540115020720081c0d02c0c0d040100d009001e00c4103201c1c0356214504d6200030507801100100a600c0c05040108102901d01e07051040ca417241c203a00908001d8568010814640b09a00486c0300b020142411402803240900080f07060300103040c143c03480351803541031101c4e0350707002507009110750030030b001030941240f40c040044d4440002480003210740e0440710001035811424812400c02c4121000d0171500d425842c80e4000050380b02947c0c0d64090721806002c10305001e600c2d0392038605250b0207503103986800c1d015951154020800392040750b031036480e4000b1124059640c000c01144080590042140d5403643c0100005150090309031441d605403c0100008900716a06186800b600400304083c075031107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 216563012 1250 216561762 216561769
    0x14070c060902060414030c040606090b030a0605030a060209011d010509040c0314130c06030203010b0702040c02031201090218010504080d030e0a05100204060e010e10110109060f02070605130503090f 87
    0x856800290b03c8500080c022445201e02c191101d42c040090f030480d201c0b000080140811103000d4000c41c80440d620f2081001002c0300ca0004540c0500458000b00c0c2c96542d8902103031609445c0c060440ba0303a40c0214803007009503840358207d10084507605040130b6820304403002a020b84100e02c400f074011510b41495100d03641c041d81048140c00f00540c0e2101480c030703007070891500116141c0c1c400c459144140000003000c41c840c0c001d6138141c030f20350141503250205990030440100391305107000b000c0d030000340070780b817a40400ca07803c180c02048500c5001d40e844150013203034816000c95032016818000309110511030002c0c0040c4100d1420070310b007400244107401c1d80c0070074034007082d40c1c0f80104548200303051100c0d0411260090000c9440c1e076100e080c0c0d20241500151801c015100115810200c0000d1107521180705007409812a00c4000c0002810070050b00c0e03100548441c135007207200b104d030002010020040c0760307c14190702c4991800c44910b2602c540d9950385e117034400e903d9401d104404041c0c4d800034568 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 216564262 1250 216563012 216563021
    0x601030b0d0203070b0d0b030303010602060115090e0708012c1b090a032d03020a12050c12040314010c080c0a021203090115060e010203041a040512031c14070c06 71
    0x142c004003112140d650b00c402072656540722020540f00d141c10a07a2040c0c50f0b0a00009a9040c0c2d00f081d00645031307aa003002030b80302c1d594000c080c3c440100000d040000031100b0740c4140b154029000c580c1c8490042d0f0400c8070820050303038840740d1018841c60034600400049402e0440d1a0000c031a140400c100100c0105e50402500540c40600e6000001c0d600000030000741000c1c003c46260258101c800c0342c4103003181504082d91010300074000d80c2041d000100020703059406100c05281c60b00780070f400c1c80750382240e10b03280c49403000b490b4050403000103090081c0030341311088050b0303500d03a94001d01205103441307402001408064900c007882d01c00801c900c0f21a031b0092104070b040f2480d1980598807880c283c0201ca001c1d01c0d682030401c070540b2043c940440d400e40f00700401c1d0321841d0181c000394030f02403074000342c3d140200003840702507401a0148000303e46503845003050504421050011500e4210002c03280e9100310514000889452800c14040845400c00130019480320182c109103440f0386003802c0c80c2020300b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 216565512 1250 216564262 216564289
    0x37080f0f370c0801060e0f0609040c021606020709060e010f1811120a0c020c0306060607050a0f060507090b03041e0312061503060b09030a02040509160605091e090601030b 75
    0x1820072500c4082c00780c0c080e0304541261855034600b03011007007501c2031041c903031011414260481d000300850450b03428140c0003440700100e03504c116a044900741125041c1e0030380a8101c0001600706420070050451280200009010030960f00302c459417403c810300480074914812005102c030040d5041200c40c2584d0b01420743c640c02030f04901d03580c0c0c0300582d800100d0002217421004a900e082e4150300b00610009030b8100040c009401080039480e46010007000340c10a400454091041841c0100098045441401114880e00f004107060410f04001f03041c1c11181d4001e00352004d4288104030100340d80e90038001c460340206003010aa4842070504441085201d46030032040e60800100140f0b20360034821401e1441160754080021035102c601811440c420600c0c0268180d014880d100d02528241c2d06c803e400954510450f854a1401d1002e410006141d0348040301154012494002c241000043d04006029154005594000c1c8100181d03061001410003810560741d00f009010301d884800d8294801c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 216566762 1250 216565512 216565621
    0x203091b03070509190c05090a08030702010f0809010b061903060501020a05030403080d020c1b030c01020102120606031302091009140108060f0907120c030c050603010b37080f0f 78
    0x101c000e00800901f8582c801e000550062a03103030800a4045030102c140da91040e8140e41d200d411040c1044100d07190700340a00100065503031100c01c070741c2e641d40c0c10004202001e2240520b00304140300703030006070403260a0f83c006030543d0050f0300704400080d0302104031402e40780e10000450700c3c0c0d400f51000d00024003812211590901c0303004110300e4144091902e480301c00d1012400c45407440301042c0124203030700508071210708070381d500c002040c080d03c1c01d6005142c0c02051107034402900362060f0000f031610701054038460117100b101c0303009200d036410740e000e640d2001a00e40780d5a000c551401c102c01e50f4400000f46802c002158034004035a01140c04d000340c0d00180b28051403661034141c0747c141708403d96030620007200d00d000649000202c508001d001d0340e048aa12264007410126903102000300f0741984440c0040c0e07240c525044480e50076603141c106074141400c0d91a0380407403a0401808591a00243c00e040307000700804200b107030283d0310502d0032a103041c08801c1110704041d4000d01840c1528280030f003009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 216568012 1250 216566762 216566771
    0x20406060503060307090c0905061e070c03050c180a091a010b0a020f0c10110111030c0711030f031b030d090506060306070906090320130203091b0307050919 69
    0x1006030744000a50301600c01241a151075a0343c421711442250709a03546880400c899100800c0a441c1c0f24026165158a030f0580860f1000e4000742c2c0882c91f44903603022200b405032904180b09100c410000c0e00003010f015200405802c200454111103641d0080560702c005071a104040104000d080400c0c49003e03c0b02c00c02030381c95860f071143c648076800c031840304001440380703d921014001e4001603803204650090304203c010310010104842003c0381d80443e50704d640d00c80601205081c4450021031003100700300030320307070726842d2510f800132001102c0103680d07220350f100e2495003040345000303c11102412000342100806540c61005981140262503171050120319000071401808000314105105007000c40035601c45e9541c464054030009a14024075001441442081c0009040400100818a142000d4000501c5400d000840155111031200407080e004000c0c03040041c010000d0510b54000304459003c401c3c0d807480402d035070303031220b00c0341e240700380d02502c0802c66111810042c100302c298032140c14030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 216569262 1250 216568012 216568019
    0x10b040f0f0b010219062c011508062e08030313020a0e0c03010e0a06150903050607140f0901031b030506031203071d0f0409030903060501080a031218020406 69
    0xd004205107210500180d0900d0742202e00341d840803507041900c00700c11400500050300c3ea03d6450082601062035141001c00c50103007000c680c40d2210b5200611007040c00410b070619030410314070300342d400e651009203641e02180a0140b09030180f61015000507001340b901c540c41e103803100501ca48042c103600080e12030000100740720b0061029117070109564000d550f03601a03150741e030034075924004040790040b002030300910040c0a007100130327007226403c5003009101280450b10b4070b83c210041c194100140005c83c1c0302035020810010140149980016a42000c0401c0b5800c40b0411261303110700390713010220110000708106268001d521080040701031002c01036008040c0b0710050024901512114400d204041809100080c128203c1e441812a552865005da603101000c081505014002e503034400c14000030313540030380c94900c1210b0007280642e0300c400700c4614504160040ba4010f030401a804d4014803a841c1c007003900300403041c907000c802882c00508070210301c2503643d140d01c0c0c82000a6001f4280007000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 216570512 1250 216569262 216569291
    0x60507110121020c070f090f0507090b0f030a091406041401090f0209060d0b0702010b01110d02030a080a0605090403110609070312180b0316140f0714010b04 69
    0xa1100a00c1901400c000380c0000005460050481807100150850344a4507414072603160040d10306811240100c3d800f6a854543c00c2c0c403114a150400d0000b00c1da01c3c4000030500103d401803a4000b4881c0c1032201069040400c0042d95100f1800e48100c1c2e04000004a02d070058640d0101240715000800c0300d0ba007411b480b07151519020107603030aa40c038410302280480e9400c01841600f002075400504415030700f203960300740007490701c00400d03180d4880b01050a02c0081420344100c244101d5250b400016180d2850001501e00280d013a1500e1865024000107040b803074000040f00c034030040c5820046030300e47d41c7c003240030042c0405401a680100b03500c3d0a02003019084219003840103001c0c0d0a44101d03903600c10b0712960702c0d941884041c4c000300010300d061a00c0c5010714120705034461004001c803449074032441551840d034001e035501b5082e01d03050104500907075030008494904c07410f240e485510301011502c506505002d03404d400741081e01000c0c442e0201c1602503214100780c00380608280070400707400501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 216571762 1250 216570512 216570517
    0xe04031808101a0d2f011b031b0303020408070f03150b0319060207022806050306030a05061510080c030106080c0415021e010902010815040e161e0509070e0114040605 73
    0xa26250007221001c0d0450000036014a0108205c1030303590480003100911040f044200c14070080e000e000030140e0300c0c00090b4444000c200d0f114040d0310090383d150b1924810b00e1030607807281d00081001c01d0510007480010031060645040400040740880c036107440f100080d04003c0c8600a00a1503000e800a803c10050300d9009000c42c01d00885121200d510038090744070b80c81d000035810049009982ca42446420b000380007a5400005c007a04807a840d007155605d00e840c21300700b81c0d001d4900e80c0c0c2e125421410f40c580303400c804c1210411803500c4d0300d45081c82c52800000340018020002442103402c0082c1102e440041510018030034900c1c088088018000081d46995000c0910f8120900480e58107012000500545440540c181d48170715440d9203100700d1485004404610960041d2030704201002100f0400c02901e0380807403559010300c06850405284501e18117401100890344c1c8001381007019903180c0148503440500c5081440c4850403a200480726400f0151400f1004000400c001c01c455038000007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 216573012 1250 216571762 216571793
    0xc0604080123060f1e040e0105011401030219030c1e08060102100e0a0b04110a080f060703060617090f031309060e062103070c0e04031808101a0d 64
    0xb00501c425081c103004140120003101c4507500105040760044650902d202c402c0c007180c0c0c3d91451a225900404009400d45049005815850703464000500142e0448c50031420307985070900701145400c1d002240300c0c0594040c03100d56001c0c565900e101c10b68603805a81c074182301c800f04411a01001942800c041e14003501500c1d018014883c41466000c1e20000e0310402d99060013840003494880f4141d0741746107c001009004036015003d424426000791074889249018082c1c1c140035084600c8030406040c94401c008048400f01414190304001060700f065045044c0094501c180358655101d1420615204104580700d12512001410a010045041032030060b5007001c0c209001480da1003035141e1340c1910503680140c0c4239044081071508200d881411410042212081d2801c001c0c3c42d0721800b000310b8080e480b41c00c032a009007040204141d4014880611100e2848242c40c0f664100305030503a449030305100f40d0300c0d8550b888590100002d00e9400c100c01d08600105605c220801c07501d40f82c2091000f140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 216574262 1250 216573012 216573041
    0x1106030a0e10240b030a11040f0b0309060a1e0c03090c030302010c021509071401110106060509120f0709270f050f070b160816030903110f150304050c06040801 70
    0x2d0360f06400c0c1c010510f410040311420341c562410340d202e4010140050105a1000003180340800c40012280c6141e0780d60001045c0c0c403e4229103c1c40e0880c031043c2010401445010507a182c0b68034502c41400c0b0b83c043d25610040380c0c000103900c6072044401da00030502c00b00094800d0300103840001c20940d0541151840700351603400d41d1004980f07035510000c128000d850b103003900d0300007020502c20003c40704015807545074140b5154880d080d1000700f00b400c45c0c0d5240c200200241000a4201560501011549504014000803c80410755070002e80c0c403410f8500524511988a09001410020514100e61121501514809182d484c4c0c070344a40401009a03046030f240c018500f18000900010031100100c40d450110149030520080b401000784800c5081268254018848807d0488030213200b0b812051107912803030281400c41c00c0907001c0b41000c03020144241600e543d83c5101d611118800c0d105080780000c0b16171661180d29140b41064900c40059030402c4001c280094481015007207000b901e50400d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 216575512 1250 216574262 216574301
    0x60906050108010c180e07091707060f050a0806010804110319061b0c11041b030e07050306090309010302070c1215050a090b040b150604060903060b030a1106030a0e10 73
    0x4901c2030b56443c08250040d0814085d41d50304100c8078484000c130b0fa61040843c07600078412070f19190b09005c00818000e000190740d2007590188001e07500007503034005095182c2000d03804c01a261000601e0140d00611a03410015030b07001050401c2742815014040c0c1c88001c054440b500780c003c0f041c00e045944c6e0002030341c0e9541407074502c82c02d1300355103106484003034403e603030b954041020707a22803011114110340c500b81c100e03581e815070300b002080505068000c8030303040e80c0105514100350016460488160481e511a030441b00901607150400001c83d0716143d020300740543c8510341400c0900003050760754031182126044000710020800740300401600241c20344001c114030785038009244c0c1204c0781d0000041c0030502d0b540c080b4020403280501c00d0ba11410701c0d1040d000448c0c0743e0300842c4c0306811036031105012800505085c010011540079000c4000c0094004292800c8191a400c010b250307a5400c0901030000080816a20440c0d90003d130b6803402c0358401c4a50a0391003804213401080710081810801351b00c1c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 216576762 1250 216575512 216575531
    0x6190e100c0515010312050a020f330f0610051308010213081b09090c030a080a14120c0c030706020a05071103031611030106050904060c090602060c0403030e01030906090605010801 79
    0x480503050b6900000d0211a5181b809800e881960055000c5c07400e500c902601200c0741c1004100c2401c440700100440b951404903e03504111100c00301c039036000c844000c00201b11103495500701d560742c01b0030b003241d01c0c0c1c0c42c01311240011fa4180c031a80c1c1c400d918000100402144034041500144544044500600c10581d0f0f01c402150701c03004120029803141407611500302a9291900c8035580141480081c0d680d02c116603c00245400c6c0c015404944090020481001a0f03401200140c002c8034103030041480c02d131151141a000b81002801125100c00100d10311045400030000d4586080d4070480440d6155100d601c00b03841034101d140111a15461100804d001e4140481030721040f20044044d0050b00d0041d959000060030b1068800350550b50b501e5001805d1382c0c03058152070040b4018000014441800140240640640d802030015948004244415444028210b8045a4140c41c03c85014121400100e0181100c52800f42c90281130022000030322120f0f9001e281207498402c02080704042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 216578012 1250 216576762 216576793
    0x10e0106111b150d05010608061c0b040302030408060a05043e1207031a070833040c051207020619020904020c0f0d020706020c06190e100c05 62
    0xa41490700019400c8111961003000c140026001d1200c00101801c043d080c2c1c00349003181c250032043c0c44c00e49264070b60004222041d005502a81c000d442031b900203a00300c552881e0301e040e00c41100b03002071001003c1d90024003494800c3c410750b4054a1424141d0b9200c1c18448500c002914007507600b0b48482c0340300c071500b402801b49001e8180d2040394000c00c0098030341424841d01e840d24641044030342c01060203101880d052030306001d40c00103580701c0c0c10700c2c034034030ce231050200c0440d20801486a807c0c0081d44050204440e1040d00940302c0582d44201d218241c0a54000340c040c1a03424a14107820904110b000c040303c0f41c0180103400c108810040d0302c103e542e5600c8080703980e40c0c001d035900c40401301c1000300041c01f54000d8005012a003405071015240a1000c21041c0c9014011003140300181c202400c07840c41d155041c00480c004004520003090310045410000d03030b40d80710340b09420400c40c07070a90303000032030500681084c1480b9500a200000c2c0c126104c101500c80c85d0800c00484443c0200400c9030712542 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 216579262 1250 216578012 216578027
    0x80c030307031b0201020a0b07030c1103030c160c0905100305160623070c0902090306091506040b0d0f080414030a17070f0b010b070b0903120f1b040905010e0106 71
    0x7a0140d40d4142d00701460040c0700e02c411040d90084c0c0c118092511903101040c12014a940075102c2658000f031170a810000003840b059850310100c4050700100184000c014010095038140d48c0b03443d104002d103c1440c0b400c00010300c00c07135220250840c2011304204010245160807801c4900a00030b0b602020145005c0d903200007814012440454001c1b59520000c1c9140d5003800100c4020b40e0350b261900c60142c071032441589054dc4180380440e00000d09108a08042c13102d1a0030110708001000955983d0b03014000b407100003481940100c2d540c6400408590b201c0383c0c0b4422243c0c00000c60a41c3d200306007803405003a44140903516602c000c8030301184103420002100c42080744c000707564081c03201049075611fa9607441290244e4002180c0c8819102095141c00441d0003000120074040c0e8402c40c52428602c030110080c622255500180040e074442c05500c522140e210117006581c07009551087d81c1007100351024840303602d40100124010852011603480281a103000c40c1004415a90b01c04046490f42c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 216580512 1250 216579262 216579277
    0x1e0c1406042301020f1902010c02060118020702220c0305130309091d060c0703020115062f030c06060406050d0203030421060e0a060c08160507110303070c080c0303 72
    0x40721509203260888008402c4600b50200d500005854036601120100c51600290341207014010360760301d90399449809110301c01ea21840303400904060b42c50141c15030320047d4442070101d8500d400259a008660310980348100041201600344039401c61981c02034014180c9650740c40200c0d01e404041003c1040304c0800500031541580d551b41c038142801e109038046d082c0300ca80703040307682c400c1034012021802c1440311078480d6101528050300d640301403c6c0282591040c8800041d100003643e414003200d98000c41c416170148110301c0c0d6400814004800104034629841d9200f600d01001c45d210308c100d00042074803409801c0898086c40680d4485003089410b911744a0b0095140c2c1c001c000c2040000c00050300d2010102c40002c520403c031311584c850703405075400c40350484010b8000d12a5041004400d01c00c03941030040601e003010140c513118040030004400c2d440c035002070000103d11042044041e41035459080030280a80761945024900040441d40030300950780240949481150300e8100001651081e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 216581762 1250 216580512 216580523
    0x402090619030212010902040509100c09050a03020f120d0908160e06011b0c030609060c0e0303041809020a090516020c0a0608061f020c0a05011407060c1e0c140604 72
    0x401e16607404c029840142c1682c100301035413148200b40c00b40ea03541c4600c903c21802c20010740103154101e00c4900c111021080d40c001400310901c2c00f4401926a03590082c1901da0544112411f41e00320400a9802212411040c18900c948802c0040c070507031045000c1c0c2221b0150701103441848120440c00d04621550040210700c03040744001034519807040c0201040c1107040700529020003410b8846a4407440c042d002650203a8a85000904100e02340c400c0014840492501451180340f1034003ba03200d1041e486400039815601800110201e040d80c004c3d40700c03d40c0203004a10050740c2d0b0500d000a05404c03146541d0443c034040c1c9814550b0300104065204010007440d035007030141007140030744522901400554004110380c800140c11a42c0658040b00b103109034005146500a1004200e0fa201840d00850f0421007903512203150090510140e0f00402c0e80810040707090381d41180111400086070000001a10207000d512504940221f511818240140d240c0780100400400c03a660f140410b0703900030007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 216583012 1250 216581762 216581809
    0xc01020d0606030e0106060806060a140c0303070305040311010b0a030b0a06050d121403130609030314040501150609060903080a0e060d02090a050609130c11010e0609060a1b0305040507050d080304020906 89
    0x2900d0b10cc0c030030303040c020042540f8042c10b0014000e0758a01d160012582031012a5940c410700007859000140f074204200920024070156074000e002c00e209100c0d51100501300d20721803010950114868100c20003070900074108040000742800c200c8032180410f02c213500418107034042d415100514004607403007269807807400310000350555a19001003112840a40c10981c1e1410303e03181d112682611140154080c100100c0c58861030080c132808404194804000d0105581b0700f00285600120000c007226009030100d501c0358003401c810f40303640c0c04280006912441c0011480d81c602a00c2d80600310441d419034840c00340544603014441244209240b490380310038155180d141c83c10785500200c40002d4103142402080f50898041805e446540043e00e6407504540c04120701000304100803035102c0c03000b00050240d404149400c41d2440508040d883c10541c84000140078030100300407920040c10043c00080da03402d81c0d800c201c04550000d1380d00f248599040701c0400d183c6e00e4009139031070030f50000500348413 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 216584262 1250 216583012 216583027
    0xe1206011a070204090605040807050d020102090102121b030c030c010b0406052107052d04090309030f0c1d07030e0d05040603180b0406140907080c060c01020d0606030e010606080606 80
    0x151608030b803404aa0254856a01c90001030203801164000c03803040b1803164440781c0745e25085d41040750250342c0c04210781c13050148007556070340080c20b0000c0c0480104041d41d00c0003400c030500c07101c952203e004030030f80c80300103121130f480800040142140c10b5404020081803070142c0c00c00069980e9403084647c4500044a200884040e604141300032282d90400c49195554420105800c43e207a4139401e119036407506080c1034900d840c01c00705012203608403410044060b240d0341c007504007400b0780005002003180f5942e0740c0c10002c80c0705501014200e550961100c41ca000544240300740b40c01c41d000c000090500c000c8144003440010036000c03013801ca4440a007404e0030400c04400612428034003503135035241810310308042599034005501450140b0710201e124400031b9480300c2e0400000e8411030903644040002c101c45500403034243c0340910226056603407001155645ea0180c0102c030101100989402c0340040c050f07401d64458490648010300a22005035113203c1503500f0745046030301c5500500100101c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 216585512 1250 216584262 216584309
    0x21606020706140f13080c010f08010506070f0c0e0c03010311060c06180313120507170706030c0c02031e07051905040906180332090f1c030e120601 65
    0x20072080c100008070343e04004d500802009840403e0748502c0f003582040c87c0e150302030b5138091003207904202c10b410a03122551404011440c03900c01d1300710103400c2400140c4210304102480d030341840241001c00d0040164105005541b98a5000b84070844414100c030441e0138032810301034183c0c3c03c459800000303410306640d6a5405441d0240c0c000c0000720a010070810f5020b00701d00d20101e00e01800aa0000c000c070782c000ca140c180e04c2e0a00740e0300241c0c0090030007a84140e5962000428070f0540300c452502040c0c0342c4107013500b5260000701d072500a5143c01b81104401040c1c038903c4c00074042610b5602200c901564a074207210048041030001480400303c1101480030342040e400c80340a0701c0c840c0900007860200c141c1c503400d10b1808003d08800003444d00d81c400165140c0e018802010200354203000105400a8100c1c00440c451450081d01541e00300406018640d200301c660507020f003a0441c400d000040525004090410390944c80740b00304007005950040c03c40000e05141a00c2440c1c003a182070400b40e1500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 216586762 1250 216585512 216585517
    0xa0204082107262d031317090916121a0d142a0301020922140a090b10030506070c0524150907050417030f0a02160602070614 55
    0x1c4025000c102031100c0000200b840140b02120040d45000140c06030602c000d0300c0d919400c4004c101c6010244140142d10440d403911180c0c0740d5100b8040c0c030f0f41c130304100303003002240c000d0b40300180c0d201c00d2110030048090070024401030a11503943d83c640503401c600c5240c0c0e0031600e0360280002d4038194030484081e182400c0300301c902860f002c0e03415242a43c2d40000d24500d01616001c0c00c2d220484801c1034820a620401980035114004070025404c104410300400d040c440b26540034115201d00e095a840020900da00001140340c640c1701810452620317641c0d6030003500c2c50313a400b02c649155080004092120701c19503102660340c843c000d448291200c490484007641402c0303060b1181d000750600c810600c049454540c3d1115220b42c03000490b0300e010003100440c000712414140c00348440c0c0013000303c01e9501c00101c50644000e01c00d5040d0f90040380802e203103107010b482d81102e101e00c00060b288040c1c41d000541480800809622511800e40313400f4120f84841c0301e880750350081049910b080d40e102e01c0d43c41c013 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 216588012 1250 216586762 216586793
    0x11160b03130510020d0c0219080d021b160f12020303040504051801020307091a071115041208030f0903040605030106032a08090607050f04031401060e0a0204082107 72
    0x211200d1002c0b43da48007080381e0001c11604d848655848803000c9041d0140a00e801d101074400c0f4010305820f04c0c1d2101c1207244600d4410308450741d4000384045014000207060070924060300b0854030070114070301203259480402c0c0108131840d0183c0030300040c00750303032000e440f040ca0f80d01801640c20325150109000142c0809405010f10203459448141c038440300748051403042d02e0690780c041e003540c42c0581846904d07140d101981241d8000300032910220f00d0350544101c4402040d0b503080c8064070800010001400b981c0c006400303885001070718a06005038074000e5401400d0501c0503099503290518180c0d034902c558499003000c5034041c401040f515009038000b03001c03c0c2c9a003080d03181c070009044c10304001d25040010407010490350810300020200030060f25602c08013900740145400b030680d0000c21135004a120080a41c01c3d4129500146030013074108d00000e28061070041c1250070215021030103074005014800242c49501030280c01404140302d440071703400c0041007583c47d00140c3e1300d81c0b40d001042c081 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 216589262 1250 216588012 216588023
    0x40203010204051807090509090307031817030414010207051e0409020402030f0a0506060a02120d0906050f041b06081503070b0c010218041a090a110a11160b0313 71
    0x40000340640340c05070f501c44204c1d18a40540450710303006001802e1a40682c0245024102c0c00d000c110702c0703480000489900940504147c3d080400ca21480000300942d80c011600700e007025145c0c00f943c11400000745c010366003041003240141545c10012070ba036102c81e01c81c0b15071003030801c40c002c542c100c01f81c03c000f406644003820104500c080f980204d401d81e44195902a034041b04001000450003485c0701311600f002003150420b1030a803403031800940c0c812a400604107501800920b0302c40d1220f165115031021079000710140010300d0040c0c4a0085100704650684a101642c0c0e45e03441a00c1c0c1985d00300c0151181510740d03000c2504c4031b0369400142881100c450b50503100b948004220910408003402007000a0720025a4a01214500c1107640f512040e22600440c00d203003075210340300c003401c2d01642441025104010f507980c032000c1c48405860b40b00b90148402c040061800700329640010500c401103000421140c082d6080100c0d0224a0158413545000fa40d0a0000ca50012264103000320300c540901c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 216590512 1250 216589262 216589267
    0x50306060120100c1e0804150c11060126010e060a02030c07050715110c0d0f030903060515090124050c010605181b031303081e16020f011a06030402030102 68
    0xc110740c400c03038141d262070b0004038001410000c08562942c0551803449111b02d0214103509250b03507030711840d01500307803070b41c0810780ca41c14403aa07014811202c0715085c00213030045a0480d43d5401c44940155110351105000341403a01981048002c14000c800800a051009241e1507507408036000094002806031220501c0402520f00440c3c02009132070098001c0348103150484000e198040d181802a1512a640b5000b190181410740c4d95903450120240d0403121864a040080ca4200d5a103401e42d040203010074904801c0c01031017807000000a0819005454018890340c0760800b1203004035400c141070021a034510940c0b40c2c1c0511031405400781c4158240041101529180000c10900b01060b0426010029034200507103140b00442035119807582802403403031030424601d58061450004c030090b05200e4140b01150468002c804070b5210300b40c0c0940e00301c1d4541004061001504c2c40700405d04010311074509070243c10501031055403006d60b54a44209411400c0c0010700c103040d00002d0017079034555809e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 216591762 1250 216590512 216590533
    0xf070f0512040b01080712110f01090b040303020c01020d03022b0204092901050c030406031a10050304060b041a040e0708070b250c0b09030703150c09050306060120 72
    0x3200729540142d114205242c0310398107100700a072816140303500100004100d070100101060b0301410f40302824505841c01c03803050704c160006035404075607a0302c403c4c1c6100000400205241d030204039010f00c0d100981c00d888c81d000706d0042c120180c0c00b54800c0a020b450007510544400c825460001c020300891090141c1800d548007643c50441d018001100c0e0901d0445050408101ca2000402c03002842400c02c0f40c1854001c01245503039020754010071081c5035440b4045400d4510908041e100a90010640c52030354012440c000c20a400a0b10126612402d2110307281e0075213850701400307039031042d81e10810846420510400c80589040303030040b1024020000301041c812014005a0301400c0300020f1255101e11420703000c01c40c0c0c1452001c510000c50079400d511f0000d46100204002c8034003052029448042c020000390800c2d0050740010501c01400140b40c400243c1c07500007600b0209603440702c3c8a400d90324410715407550300880305e4a001404070512001c8543d1900e032201c08603454402200d80e00d0b0304 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 216593012 1250 216591762 216591787
    0xa0f080f07031d030d060305150c030c07030e040c090e0f040302032a0106030c0501170105130b131509180f02061605070e010f17070603110f0d060504050f0f070f05 72
    0x401545e1781c141c107403962814000d1150802141c17400d09942c16a030000c61502043d20011030001078031803c200321300040c80ca814503100f00469010f80b04001c2081001401ca2075018010381143d21035918000700400000711140481001c8900c01c5170150040d40c9041302c648941c00f5000b024542ea08001c0d103005c2c11440224070b00748241406541b040480140850030800007400c03034181d105603806600194001071003030713440e498094407050180d08008500b03000383c4070020b215008aa219007c0caa0720305140d080d6206180c400600c105e40d40e201d4100121001e04e400040c240005083c050314100240031040010b0804a000344800e09800b00c580803401c0407641c81c5070401c1d0300740e407028004800c441c00601c9000305480b0804003e02c1205860700c1140400003550340c0b200da851160005160303035401401c034403c146c803044071650444540d01554500c3c0c8011141c00030503003070040b103001d6881c040006a84000040d0708500036444008a1106550748540480300b5401c0d4840781030030403905110200c3c01e0034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 216594262 1250 216593012 216593017
    0xf0503191b030c0803041d10060f03090501020a0206040201180e0402060f070b1815091c0302191701050603060604090b01020703060c030e0f03030705070b0621030a0f080f07031d03 79
    0x84540d000d0b50340c85282085405218907201211041800c0450074410022384500382c2c01d086600a0400f00450748041c41e05900070310140360003078815400051204081540803500c50702c034510076201c00c180c0d00444ca40304d410210160242e90000046440403a0152402a02401a41210080c014601f829654034095000c07001d9070040215144044204030f8090240204002000426400c0100d0310304120740329a51001c100791101c032200401006030015201307404603100703480c0343c0b4451482070100c0a80104100349a9850301c140c0c510071000810180f4000702183c7c00307050000c20050070b003420035040100821502654130305600c5800b1000000621a002d0508507480946000030403503140050b50741040c0c2d148255844a030401c00070461640c0d00041685c4113290820560b1041d6661040412541c114081d252100849600715039480800000000e06803001c1c55580c00460034000c6c0020f0b40c0a880503a01c0c02d00602541c40080c0d9010310907403140c0181011480c060001c1101907410f90b065a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 216595512 1250 216594262 216594269
    0xb0d0603120206101212030c030b0406180509010e0d050a0c0f0311060601020105042f06030906101502030a050304110a080d1b0209070e010c0b0109060f0503191b030c 73
    0x141c03c100100203003c40003204041c020080412aa4041303001c580c1c0c0c5240640d0f42c00b4109003419902c041c4032403042e00c2030340b050000d858040e00c10401c880e29102140c60300c01648801804040c02c10700000c0c01e40c201801100400d00030b600c02006021480301095480390031052002e42002a5444890701041141e044040c0d003600035141e074032020b02e80e1242341d4107000005043d40e0641e07043c0b00500c00001c0c010300010301c406407404084942c1c0c050342903504010700f801d03142040d4801c00100500c003803402c0103d451402a500390b10780101c190340d10001241072240481402015130801d21030701940c00d014000865001d841140400483c5001d000090341496241c1c1080c002135100641803101150811051750300340141f8a18660b42c28681c0d4001803450000400910400210003040c01042c1d0245030b40340980c540c0020108895a182d088035001031080e4032440d0f501c1c40d4a490001858100031a150b1000d4138075900d45060790069407502810100d400c11500b414500c3c4410010100324a05030b40c00c041c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 216596762 1250 216595512 216595517
    0x1110f060a052401020601030605061507140f07060c02091b1b010e0115030204020906210402040b060a1709070f030b040c05040b09180111030f04020109150203040b0d060312 76
    0xa00f44010200c84590862203865031031115004440320f20703a00094202c4c1101d5100c0c40204040d9620004502400f0a4280c031112140c0007044a000708000740b02d16212480c0400b0441e880300b081e81404607901c02d40c0e4070681c00480c03551440d200140c20a000d50701c1d840003010b00740600a408419016126078400700412204908011460041400a000da0072103400d241000788031803020030440a413946090b200c0240b246d640016001199214001030321022400c8050801d00e520310001504040601110128030640c41d020825500340307091015154600483da884248001c10080b40300134208000c1c1500d0311511850400082c1d054008080070059842402000380904081ca041400303448141c00c65403059007031407415045034444034262540207601818025200355211003142c0100344000766642070140010820140e05030798950320b809103100f0303a95165115503462030fa05811294003905030058104100801183c0009400740c1088031307403800c000400590303903a07418480f1311088202001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 216598012 1250 216596762 216596771
    0x906120f0f0106030c0e12010902040203071e090608070c0f081309060503010b03030708030a09020d29090304120c050a0305011d03070201050d020a0509030106060e030c030c0a030201110f060a 84
    0x2500c02041680d41c0100501c0c241442112040140904900040c1c0706d0607011300c0030440742d000f02801c2500500b1140d9005001103540e0705000000920b03064201c07141602490b080188080400d124060300011030301d03241d0380c48190761184541203d10410400041c1c48855020490501180c0d012004284400c0341c1c07945003e000d850b040c00b5a090314050b62106200c0d0b454170103641c041e41c46c084110382c00d040d4413402490341c0e95a080b051314014400203001035086241c2c00144020411103441d041ea10380e00c0010094900601c5404c41040800100d41000340ea8005000800c1010034a4000c2d0410a101f00c880040250302c400104002900a90045d60340740e450b10b09840c01611203146800502442a01452400c1850340010b840e62044003134000403a5030005090310414440c20a071515150f00a0090145075500ca034000c1900591711400752003402544c5a50100f881d000842d054440350140c401c0788840e00e035070015514810101c2c0460b46600a20301c0c80100400244041803141c4400c07440040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 216599262 1250 216598012 216598021
    0x221010e160e06092205041b05091e0901090203010f0209090903041d06040f090302010b010e12060103020d0303270309050a08030d09030504080a05070e060303090d080906120f 77
    0x401841c055034215007407244080707000071103840300b004454244c3d00a564a0310380ca6070300345640c808440c2210b20007981920305003e01c0100110812400e90180b4100a6a180d00d80c0310710411500040030f840c52541400301c54030311815500d1904c80c0300d03807144003e0000215480070382c010030700b5640c141e848030800660000d000c0b256071415283d06e0380c00031000e400440c100b038104400e00e802d52900318924040900410002505507032550011820042c100c001488417034640d1401034040d009250b401408550703203482c103c02034185540099510040f0000501899196800b0711041d0280c1c403400341c08041d201d10116120303041c2045540c8201240319400c0c20b4407262800d00402181c1a0341085110b1060755004010b000000402d0302c102405250000403088080d19003614203200c0e940c00300185000b00143d00040c00400304510080b1000000c20103480d40d284010180c89120b1a80c1190780400340000510201e075440d800340c812070801a00b1030b071034555051854003080d03200300c81c8855590050130800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 216600512 1250 216599262 216599281
    0x30e120a0903020909010b1e0411040315050702030910030f02130f0e0f07080f1801060b0d0509070f1511120903010c17060f130c050a14070804090221010e 68
    0x1640c00300e1003500810000300800c0c0003401114030745051041d007111001c5d031550243d84174ad002442a6041e808044d9441d581da141c948422038440401002052038040090310290003c01180c601400051010025182c80001540102a02041c1c1d5581a5090140c01d90480007044990b004d00403007031802031407603d0103110880955004101c048041800740503c0b50507a041300100750041c000a1048038556141316840030b0840b4480341d4400c0c039608210b000540c0307441840c010000000706003c20b000c103695075841c1d955150441d00c2104800548101d0800902c4c00c003d0b0b003c0e8155520745440141840d11091680c54883c1c031360002c9082001c0001d50464500d0240b055000b403415034146003407202c3c0d91050710f41840c48010300f5640210f03000800d1207082d90b039152030b0002e02a50410200103224041c0d00080075a0004028040801c2680410385403202c4250150f0710440d5201d050549000d06010000c40a90050280d8003400020798001114400039545600d0181003061100c170814079100600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 216601762 1250 216600512 216600529
    0x309131b18090603110f0402160803060f0102030f04140105190801140d11040b030a0609050114010e0108060112062a0306090606090e040203070302120d020105070509010c03030e120a090302 83
    0x4210094500b4008000040320b071150250402000c0b5240c1b82c3c59841c0c403010901030f04c02c0049603176881d404170080c5020131401c54055405100192882d400c0c4060f400010782c0c1c5c910800c20018a959070504c410041c0ca2841890030aa10310180340c6079003812003201c1316900ea03900c0301040c00c0100300c00d10014050310740080c03000c000341c4904440030212a400e90711a40d9010900100941c000d5449240c00021078400300301078816a0380c056801c2003020b01905010b4000e02c1301ea20340c010f60202c2c1c0400000c00c1d1030320003d030324180c80d04000074000d0359203440c215080040c8a4013040310090703128803800040b0151030726050445829000c0500640500d100000d00b03c0380190000c0f15041c0c030b0943c00740b000580c00b0542e60113580e0120840d040f9078545000003440c058081e0b000035880a2480948040d018020420440007042900280003e40701c0210070745a03800f41204280c001906c0941c10400309100383c200c900240e00f140207a80301012180080e220b035a00440c200c0012400e556020021810003400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 216603012 1250 216601762 216601769
    0x12020604030e010f120c1b060b030601090c05030a0504170304031107050a21020402130303200303060904081b060c092b02150f0307030504110d02030309131b18 70
    0x82244944d00390690250100400c0c8858190305a079641c4244801e5005903286282c2ca2a455071803018000140780c008060400000e056029004443c00040c800d6014000c00c81c0c1002c441d1200b50941c0e81d0700c0141c40007080c005005540144241003030585044605004600880c0243c1d159084041c040011514010080d8003445c05412800000c000d000e0050300c3d03007800c11103018a1640c4003041ca00004010b07014088000e4048810324400208041d0011201949041420109114010401c00c082c2c0c0720300048403150740140c0b5810009002550705030042c9914480071802030001603554407401d03d40a8121440001c004000540d0589460300d154452540700810060204014107010b1016484002c0c4038004d0188170450400d6004020f01c00603204c1042501802584038603001344020b000c0c100c2a0f806943c42c0d283c03551003032900c0c1841c00b401401e040d0058000e514050070f6034144541e00c0e4613021170a114a98440c3d00d11030a41214805010066071651880c40210703418421408030000b550 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 216604262 1250 216603012 216603017
    0x40510030b031b030607050d0609060f06170103050a0b040203151f080303090d141216030e0109030c08030604021b0d1107140607030e03060a090b0a11030c03090a12020604030e01 78
    0x4040c01003c0e500005d21540c014603d00e0001d03110030380312034a0805000c007a00040c580c24145000464680c02d81e40b0302c0c20403500140e640c5032050313406202c081040340c401e000152840c0c0103110b000000c50202e0340d4041d0020700c05003c5810040903440d090861480907161200003074005480c440e0000051901940a041a88041c42c03550501c010820b65426820b0810310074000383d9240300c85084480c2087e928104070800c2820124074002d91200005090300340a880401e03e803004170001382905119020000b58151503c081542c0b042d100c0304082c0c0c1000300307500e81c440d800300042c101d0340c1c040740c029003941d0103101c0c001e062070350a02c41c0240c0154007406090b14590700c6000100302c0d802038240c400c5803043c425188075940304014101180c405410710090713905482100c060016640055100c120000c0c014074141034070351610303105182038600642d01402024000c0c00403a0044100e10011500051410215a003074041e039030f03d607410318000c0d0a404001d6000502000141904000514000402407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 216605512 1250 216604262 216604303
    0x509100b120a0e011505040c090f06020601091109010507110f0414010e091501031202010906111c0203070f08151012060524030405160b07260f030408040510030b03 72
    0x200300c060b00e104401d10486114a84502301486580c1c013803002480940030005039101603030b8591002a40e641d81c284544100545002c00c0b0f60514108003058400d140c0059648518040b09500c41519103514913014544c0045500c0c8281140e0f5100d208401030000701c061410071540c5800700c0c0c05030381040240007013099040b00c410300408414028096041d84c1c0e104102040e21951305008a004020341c00005042524180e0022481c054400c0502445040e0030381c07558414860f48501c0d800d90206032038030004213600d0051111914000c001c070a80c03240032204d07640e4040c410304000681040803003c6081c0865651707980c2c003403100054021903000e00801c0e9154041141180e440f80c0b144c00801c020034400300c0d00440800c04001c2c0034025004549030185d046200c036500e4000010403540405011544240608100c8a100c512030307800740444d444000d041814025100c0a05034180d000034011520b1900030880030600c0d42c3d0f0f02da07405405610b29030b00000d40580810134546401007c1140300402d6108 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 216606762 1250 216605512 216605531
    0x6020a05120f0702011209080310180903081503030d020403121205010501020a06050a0207020306040b01150810030303020f0720040c02010b0f0f01020705060706140f100509100b120a0e01 82
    0x202c1d021140d04503420710f000903d02507150307a507100600c4120b50003411410004144014249103006c040c041e1010f07808200c4501c0708203140c0104881d00400e0003008204000c000807844d14210034090f40100016040c1d038075240c44d019241080380e0042d0022140d01c1b007840710745030300c440d40410400449031790100c0c10455541032500103540d80700c0c2c03544002c21107070f160b00002e541803030581c056500180e4040e04603800780c1003d10b0070440d003040900413044501440314100b00e02d81c0c854070826000380301060150000600355141140650321480703404500c10300400030398000500107180c02260492040c1c00c5074024011104110a80f503551400d481107a06189803c0801c1c5d58620300c0300300540c02111a0400c071076807100180c0c10708541d54000340d07000e00042601d805000407504408166540c844220742250307070701c01444410840c280e41e400c107592050101884103090031500c0680104400000200715952400482011b0344101c00300004d0f182c0803014402d40c460240100c426042904000b4004000c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 216608012 1250 216606762 216606787
    0x807050a2102061207080711031204080705150109020309070509042f13020d0e0a031e030b040f020c010623040f0902030a08120c071203021c0606020a0512 68
    0x3000601407100741d0101c80040c1190780340e00407036002d031000012401d02e0740340c540c0c0e0141c0148011030740c1c2c10104038868030b88407503410301108940e0403083c8100ca4104584803600c0388917954101035170448652041c06c0d058848641f40c8032240d80241180318001d03a580c50010101c0742021001e900140c001c0c0d100500703200014511340c2030b061710710b4140000d481140e07503841e00f80e0f00b614400002d0030703402c0805c4202280c0d0310300003a00185012450402c041c03100b281d4040702c0707640e81e010812003d40003074220b0b92440b170181c04e000111481c2c0c105d2450041070081141c8005400c540b680c0013034418040d80000e0000d42441c080c000d070001004100c1400900d5528509035003503c03d082d003a014405c0d0b603552501d0058100e81d9001640841e0058211200d05880385402140e030f51081d020040d440d9400c400289508070382c0000c445640364405c1044d81daa801603802070380039411240e07d16440d04400d80f041e40d9141658480d150007801d480e80244021022801c00508200b0903070803081c4942c000b040a01c00116 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 216609262 1250 216608012 216608039
    0x19052403151909150225021c080c060106090501031a012015100513050603191a1609050a0f03020913150212060906030705100207030803100807050a 65
    0x500a00300401c1c0030400112100091020b002c00801c48030307082d5003501d40c4d080980d001d4000c0c0c2c0100161140c80306a10384070110701c4441403400035401380184800100081e4904e00300301c1074a1003031403242d0a040f01031020300e09290090300030b0703c000f546071340e801c01c025a0725002c1c040003441189254800a4480700c0000c28181401103140b1241e040e10030700d150b08402c100041860b000d01103015104c3ca041c0380030300c01801c003118401c003482100007035420a241441d904c102c6002d000010028075284500402402640782c00410954101ca03603003400d96440207507503100c2c0307108013243e0340185074040c030f40000500000b0300741c0c10181c01405040c3d01070002ca803241c692007040d40e4040740d4020050303031880140f9901320102c010041102e181041d141c0d201000325000760203489807402001515588102c24000c1c0f040c0126500b031340c541c0c0702490800003400d10141000d14248184180e61850b600c9440b0b0040e603034025904179925040c4020100298101070095902401044071469411468038151703100b2503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 216610512 1250 216609262 216609271
    0x910060e0105070b13110307080307060504060204150206070f020f060103321623040b040f1802210304140310140a05010605040f0e1905240315 63
    0xd2000d00180607030096080d034400ca903100c0004002c40c9401314100410584244003140d0005040d8210714044c074020070610184c544500042d410000145c450300050039000d04103a402941c01c04c0007007142ca03100a807245941c002600108814107000740e000b800f10001d0440324003150000000503110160225402c0d04403034009207001206008804141004200350700800c08c0c00c007658600040f1820085512108244000030000010b030f07507030058442c1c281084803030004803040c08404a030a45072942c00741c5481a000b80001074880700f03004024048504030050480c2c41a0b41e201e0000841c580540c920008030850806044030b1020f6002441d41e030300560090f120034030010311081c00d940d1020800c4140e01c0740501001d2005403d01d81410181180070785884480600f00710001c142d031801101240c01312135203038190481d1245405c260741018207016190068038481c03120b029481050701d0155601900300f40810348400c4aa5814041c513131402c480c51350f400303600b14400c145000c0d1300486441d5800f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 216611762 1250 216610512 216610517
    0x30a030c02120109261c0911191a09060702060313020303130839010e1f09150f140c06041416033207080307060506091006 54
    0x10003880e440001c09140251201c0e181ea03619002d100c1041c00000e20380310b0382202c00c0004a80017803908490100b1036110710683d004401c0c14503000407030189915444034010500404a031800b0910880c0001c5c8940564040b0341064860340740705000341e10381c4c1c00b005003260400c459100e10f031940003004507039940034540c8060701c81c410100c0000d00c905100c2410b41e1885074000c081d256103a85020b05107407a0400c41c0190680c0b403054000f40c9160083c42d102c0030f0b04444030f5403420301111b0030143d00d000e01d5285001076241000140c0d012b140141d1038603641030010008401014021315a40c050042c4161220703803001c5d150300071800d0013211660b0000f040000c03800051901c5001e1071a0300c0152000c1e84240c81340e40849120b214100028850000c00038200d00034120140c1d0385d018261148015160040d0201820700303100b41116241180c0d40f610b2420781c240d00902d4800c020700702c440c2d40a0070641c0710380c007102881d00000b401c002041040c0c030071a43d00c8441121142001c2c2000300798040414440d0048405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 216613012 1250 216611762 216611777
    0x20901051212040603090c05030d02070b0a030f1107020f06030c120709030f0b0703180201120e07030804080115050103180f0212010612120908150c040504090501090209060609030a03 80
    0x7054502480003081031242d18118030354499031918005c00820404000340c2d2001410080030403603203008621881c0744051540140b40803400c048e444591607010000781c0091595410240881501da40500400507440c200640d44803d02d500601c01d2080700240c18503c80c00d010810804542d105000f500c03440354944c07505403060361310540d0907260000b0347d0700050503800c14103118000f001821481180709500c0e66a0500001618410385401048030000080c0406c2554040c44a0815940d000c55182400740301101c00c2c40c1ea0b40d071503018981c0e02c42d0704602e205035195440c040e454626501d81800910302841c00b007040c007604403404142c0d12480c960003007240c1640e284000c15541c0301860740d901c0e008014000c1013a00d540301129500c401002c84100c0e08000142411400d40d4020f80561040301d41c00005000200034030490481210b80c000c00e0130412040600000c03485840b0352043c0d6005a114200003d07822030382e80108402241c000342068800c2e54100300e83c0b40140c5000c0750021000703a250600300c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 216614262 1250 216613012 216613039
    0xb09010f14040b091603030c320721020904050a0c060507030807141605100f06030201030605180610170406020408060a09030906050d020c060a0615180b091f09090c05040302090105 79
    0x2265210350392720310300460781c0380790301c0001800304804a50b141d00c40c0c0d000c0f14402c035911a01c62018001d1600c02c040001d041030700305800b509001045c154003511850940c1d0a00d0015586c204080c1f407071340c108400042020410301d04041e04001e21541103040c9050402d00b5007841c5142c9003d5104001e414035102c0000390201c0100082004401c1c1110a0f040b014000342e1003284080005107202d100681c002030500c100000e080c10005d11a443c0e1804000e021039940da120028008030003440c03003c91003004011011646107400313081c2c03110f00442c80340401503039a07881d00515034036002e4060000c007202c901d400c04600c0001d40021180f0201e0b503040c140f150f19281400070010003400740c2000041030b0f00600303007005a40209980101c0944a00701c0c2c3d1140e84079924042294030450000b89800040c10030001032110524900281a0f82040245200c12401c90904028680d803181e07003403200820020a412700640b040e074011552000d4282c03801c0e0b800d042c074540009014240c1842100d0290b4003030344411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 216615512 1250 216614262 216614273
    0x2012006040809151206102102072001090e130c0905040b010e1003030507210f091205100b03070b0304080a0305060604060c0b09010f14040b091603030c 67
    0x1846005280090311118030301401c0071400355120408061113032114124038040c14506070300ba41c2000004600540c3d191b9680b60602c080408524031100a0001a801c01e80004068495181d5160350150b409a11010189881a2020900c0540c2c10030007039009101c0c909039034021a004119840420406903070f031140e4440000c2c5c0f06240c3c038007510cc120f020001049407411904458003541c0302e0303200314045a03a941540e0300005802e8a01c038440122400003007001c60301c101c0107030270321354001c404105540e00c0c07080f8030820428594003148085510001800a03450300500c9420041440032500c460514075992002d840c0c0a414500b550466076803c00c1e6601360320b00b0007a41c0060501000c21a075241004e00b00600960052100d4800081c06e0000203212030074000d00391421039081e0340740c040003030700a0ba8401c5d00000008040c40b800759622005242191464040c0b2a803803801c50401c0149070400c1d0900c140c0320a0b00030805545540900201c0281c1c05428640d40c04403078161400b4270b440d8240c0d261030f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 216616762 1250 216615512 216615557
    0x3020307050105093f0f0706090302030a12090906080d02010608011e1d0f0304140d020112050a09050607050714010c170c07060213290a0e040f0c0804050f0a0803040201 74
    0x400008082841c80c0b840400000032498681100701c42181d4400c0d07601c60b009c03108143c207404029016000320400390005104018120140d0b5030724244845407035207400d243c100b1520164040c2c0102e50188006000c007903028404c000c0904030103402440003000c2190524211b03104c0ca1012070003590b580e40c81c2c156040031060001d142c00740c290141e406403910010000cae070300c0d0410b02420720b4000c024180840c140c1b078420001c102e2994107031220a40d511200b20b0400040c50b00038401c800c03403a220030300c030000544c0030b1003050b200710190b40310141c541c3c000382420311101060400c0302d241c0740e140040c024600c3e0b4210108038152400384040c0c00304c0f9500c40755801840d008081c0002c0001d4008500c2800714022160010151007041c1140e6020782c4a0f01c0c151299040c103c0c2007104032010810072190141c2c031901c2c40c0460024090808103080e10030160401c101c418020018000644000c1071004000c814001c54903200050802050048200e49500d44c080c4000752009040c045081d03403101e03640c0f1136543d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 216618012 1250 216616762 216616849
    0x9152105010b03010e01020901090806010e07110309100807090906031a07020f0105071e1d0613120b01090506030f0303010e190c350a090303150b040302030705010509 73
    0xe008003441e0490170307070107500f0501c0594040740d035003800840c80c240c1c0002c695049604502c0c5010f642e8030b50b1031080c1c40407408120080b0581c0010080c0700003c1c2c44040b076035903294025549412492629113401086401c00f600003800c064240b03001040400c5011400304000f90740c0044603006611510303400c1c0e02c1c20740d8089821449508020030400c1c4160013007022940c0100840304000008140031085500d00d0061044802d201844078040d60b103420b00002519502c2042d502407405552941200201d100102d032044511099260051060100e180507041c0c02140c154003d1103e80040110240c0b203010500504a400c40140c0018011031000c0001e51041c200e000d0041001d800c00f000c006100075900400b2014154003103441c0111b4007250202042d1541c009544111585c072001080409483c2000041d0109a2607001c80003001407a41031840040c0403a0000694075440e40c07060600b08420780e8080c9041c403005004554a0f80c40d01c40001103032603800384403820310200b00b8406100c403098010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 216619262 1250 216618012 216618019
    0x7031502040515181c050106140112110922060b0f27060703020d0806030c010c030e03071e030c0b070305030609180726060105060f0f0f0f0409152105010b 68
    0x24003601c0004017821050b40d40200d0003441a2a11203c840c4140c1e2080c070301c483c1c00079082a01c005a08000c1d41e00804c881c18074110320740d14103400240060480384440c1506001c080080c54651140e642510070880180640c945090800064050106950203109506c980100c543c4180c1c401c4824102840f040010004102039211811402d00030764905403410580b010410083c08a00b0f64500003a0403603428405959560544600d55404c4034031110b01a02d50b5003502c035401d4042000c40054480744006c10408400c07d0706286076013031260340324405a21801569074208610303800309a101040720b5003c001078030201e04588902140302901a042d00c000b0204c2d0007810008107414030500281445020a01d0602440d068407140b02034a412003071150756400306041262000b101c072204041c0c03140860206440d402e1140040301c200c02503004e80c90001c0d1081c0006000d001c0b000042c41041100340013000c101000500306500c2509105c403040c6900d8200d00400552010064250000840d004016 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 216620512 1250 216619262 216619279
    0xc1314060319020d0212091006030c05060d021306020c0307090c0f080601020c100e150405030304030609080706050103050c0a15082701091506081203070e04090209090703150204051518 81
    0x2000355101030090ba05003070213000d44238541d00c0c044903178050b5a050720741144046800c14a402c040100079448489440c4d00c1c0c94080c449140340c086260352020050030070350054890400c02c1d408240c1803d1042e040300341c0c081c0c6003071660a401c42e0f004142249483c6141015900c903103410006170f18001004e181c00b0f50020400390398032a040d5100c01c11041032201a0b450108142c6540c11499a50080340100e981550040c0410004185203420010310b1a000342c0903030b0f29254641d1241c4c4140e5609030810b44841c0c1c845510100b29061215503203000b04280d4107011780200081800502d4400c003d072450000398240c80040d0b440041000b40c1d05080c0b82c030000200450880c0b482c003000c0da01c1c8401d50b0598401d1400300001480d9002142c0c103202d1510070b510184c41d650b1040c105449010305007074000c1d000750381e400305400180c4980b00078902909400740240421031940c940544900c0781c08803900160740c01400300b08070b142c0f2005012036240007040182c07900c43d0306002100b001804c6081c0a198041040d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 216621762 1250 216620512 216620527
    0x11502031204030e0d0309050a080304210f0807031d0d0f021011031c0b0103020c030a050c0c130f24050919060f080127110310050c1314060319020d02 66
    0xb1007d40001c45006840c800e941e01e075544480750302c0e4041c9110304034100001107441d05401c001c110010400a104803421105000192203000322034102400480204036160321b0701500308540703016403001c0e0b60216651400c5041c2030340c8000c00c100302c2204c024024440f6400ca00b180c82e0048400c0c00d1800e480300d04483d12001c8084443c4011200704c8180c1401c14170344154403186521074021504880d00180003186071400300c0f1401c8a680d8030011000e04240507500d2080d00713940ea2003054910303040d100500032030703000c006240c0c000c1242c03020a03c400340f48901203070b40200f0000300003150301120400c507a6000300d0b0390740c0c0c41440d0700e041204040e903031101e141004c0490b1000200c020f22003030700d42c050001c101c841441c50080c0b0841c03101c003280c000c0080c0c4000b0400c00250110900e92060000030b401e444022907180c5e140700c2615816100d10b0421000410381403540340028003010010920800c071417940b142d032240803440e00d210242c98054464000c100346241c1402ca41c045800284c1c40300c004540d100e01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 216623012 1250 216621762 216621767
    0x40e010e0c010801080d050a0c03020102070b0f0106080a060302030613081e072a2c04030e0f0114030703180f0c060306050405152202030f0a05011502031204030e0d03 73
    0xc14581c06010511010000c901c0960020300d040820f0501d03140c0720302d4005004c00a44203020613901c120304541d020801c0c0c0380061000041c150050004240c40030a5505290300548403030002003001112611302441007015a9000502c180c0246070124101d05000c02401c080910b84100c901c110000d00c8401003c084086032035000304a158022109aa01003080c1030f08012060b11101800e4602d06d12120305108044401b07030f000540e07905407001212800391051080162040440381034022500003901110b40b400c1103078806400340e500746821595a6a80000c584590101900394410541d50b0b42d940045510400100e400d0b06030441c0d40c81103060028030b065030245815001d200c001a09003c40050107007003501880380a540e800030a80c401c0c100410074850910210340411101d4804503034840d841001d20b200a50140d034031074000c2c140c01d01d491001001550010fa014400040615401081c00e90f030100c140c0d41e410140000f02c8100d078503035080840ba51805003115030b91144080e5442e008054 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 216624262 1250 216623012 216623023
    0xb0a03050a050f1501030f0b0c0d15050406050105040f030f081c050702102c01110c1e0c060d02090d06021209070621180c1e0906150c02040e010e 64
    0x101d0f5012100c5150900180849140081c48000d00701c0c80350850001c0041d02540345141d00984010440b0308112000c2e000d0310940d60109005a1001d440c1c4200b030005080501400300a040d0a0074040d18007441c1024801c0c0c040f800d80b202a1503c82d0301000c1e02d080004042c11103030301d8543d41c0581038141d25601d0001004000a94905003d80300358440d8010180e858007901d40c10000070401c02d88c00806580a1885004041c04006c4d829561415400c0c04200c2c1000a05101c41d000002001042592440c134009065011808007084e400b0792800989555030604071001c50781407400140c2c652051801040f000003a000300101924000304096030218910140140f10301016000c4508207a078079407042d5440d41c606402ca41c00180d00c0d6602176142d8110fa044902c0d803901141c0302007a528480e03140d6014403000b42d005502032014080e1840400c51100c40e019003d003940d481308105c80d80c40d000c01d14a644103d00142400c0c0079154104105640d1264424002108048024400081e40803901a10384 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 216625512 1250 216624262 216624283
    0xe030708070e18011e0509070504060807031a01050a03030c030c0803070809060f070f03020a0c0c08030a1e021009030c0605090102030a0c050304021c1506080c10020307030806040b0a03050a05 84
    0x41074865908500c44014007540503806044070160b591005d0b68403031000906401080f10000d4401d021000583d80c40c1ca2240c08000c20300c0b80041e120090452500c5c8625072006180c40950120200040c061642c945d40380c5001c496050801d07282071521868180c610607a4100051700da1341d0040104851950000c20b035038890704640c0269101750750760815010001e0815500d200c001807d60b10100c40e0140658000c00c40395000b4100701d01c040c40207981c1d14240320f8035a048a0308070780000ca014480d19030031454498090f030480c1c4010b01101c4041e80e00940d540d00440070302d0000b60700d4150310403d1500502400010701d8008100784041d15145070300038040d50040d90304011081c0b400020b0b420562207081500e01443d4001c0c65520017041d10b0f2400940185a41400d0360142c0302603800d03900312051842031100800514010701400e980c040c081081215420208009540081140c400002d40c010b4040c1d038482d030121000602101d100011031036241483e000102503200e420110001d0140004141608 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 216626762 1250 216625512 216625531
    0xf0b032a070c23010305090106050d08250809041d0f0a0b01080705091b040b0a08010603060506070f060e01110c0a151e050702012a0206090d09060e030708070e 70
    0x8143d40d500e41108030a00d42d054060b1020b4007102034a03aa0740c800e41040741c10003d440c001103496a114070008114030014541141d041c03100103094003503111a41103c40703088040402e140c055000ba034403120624403a21052522a0355a1032604403400280110800381861400460340c0c2d000b4080035071940ea1601d203d06459510001000140001c400101c807403d03150f018124002c50b4030366010071042c1c0c0004500e260500901440302007010540940600754070b0100b41d80380d440d154500500a0304807043c58001a0145c1d07810402880801c1000c924040c41c0c0d90f00810001c0e01c2501b22594500600702e42100702c84c480340010307c142c000c2d20000b40080072140944012010701441c0754015003151341100080c00c00a142184250750207442d0b0388016441059400085111034082c4503454a40d2083c0c0700179510502d02c42500c0328043c0e410072425600c02041002810040101e044c040c003220382c1407240d00108943d286890002d03850910a01c0002e00c1d00d0012542e01c191180b00b1032040c814103d0794580c9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 216628012 1250 216626762 216626783
    0xc060237080a1104031103070e28050112021215191415090406062c1b160c0308041d240904020f090f0a0b09010f0b032a07 54
    0x81d84100d8443c1241503040e91809030300d401d180d592a210700c40030250b00c0030307894002c603c00001d00010030403089106541c3ea91202e01c81243d1403041d4210260f41c0b040407000b5a1801005202c815001c100003041a60100e94083c032548001010034508002c0000c5012210001c1c02440380c0120340c602d07000f2020780381610910011050314072940d41d8034021240c4084000d01002803480d54100340107040d402500480c0041002c036207178821050f0900c160300808a4140c6075070105c0314120b8460040f260048400d00c85025210000c5a4400850041c1910080c61810640c1440b00300300b100449131004562001c030302a200e40d500c1c1a0b41c2c019410888050196007820300c0081c14441c40d05507014103101503506641031019024050101442000700200d0300508219201e4949580300c4a4540c401e0708500c48050880c80d02d01c90030005c1c0c8503c00c03c41c90055407120b0040c0100c4900b94642c00507500f500031840d440e940e507400d50114560394105500441900b4800ca00d824503150b400401225001300c40806 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 216629262 1250 216628012 216628021
    0x723030d020c10020a0c03120203121306060501020c01200c03010f0203070e0a0f0b03270708010b0a0509130201030914070f0501090605031302060910021e0601060c06023708 76
    0xd0325000c1d4a0402801601c80c800d0620015641442c2031491030462710489040903445e58034680480740548003420f803910140072007806c022f40b0b0300400303016010a101401c2040032180002e00409080100c0051b407146d94240ca01032000c04210349a44040300a0082c080c41e892492008000c4d4002c0d00c2c9000015806881816241490061070040368400290100468a4002000010740026015010510340320380c0c5189a4880c4032003508030003200d000600591031400200d68210b8840304d000c54050040c8038400c019654840c0070540d80540c400d95603090104191004800501141c0c0005001e8410043e2658003900001001c00681d2000102c0005140d102c80064545001c40d224120004004000040c518007610004141d514409415542400311000010307100d0b099802881005078440e00c0175001c0075400d10580411000540054855541403010003081000c0c01c0e04003908594001440100e40114040d42d89040141001402c52601020b41c0d09202000035041210000e1000c03000f04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 216630512 1250 216629262 216629267
    0x3030a110c040b33040b12010f060210020c01020417030307080603060c030103020103090c0504061706060a0e13031b06050105040b0118050f010203040e0106030b03070807080723030d020c10 83
    0x810101401000204111518405000c0300013807408000d09110792007480e104407084401c00340c4058000c05015030f885c1d40c41e4200541031094140d118811001e4901401c00c409600410030940c4a81e660f4809a03076800c1d81002640680726030760240510481190448803000b00c0440a140203d40301d80ea0318030f1a450344010140d45440075a01e202c0c0011041004000640c000d40c401d60300c09104a00c10340c2c000d561007000030111049548400d01c591541c8244d8820402d00341f0039103a000208407241d2808030300b07211001000b464006d000742029070f2200c60400901d4080d031000002c00700f4a8803a90300442d803a10307204000e0b103400c4c4074a500460a02c0c502c0a095030103446400c88007044004007480084c5860104541070748421201d605602040001050392143c1d801001d000e005542c038081545000d00c001d25150030411fa100403440c0d0000c1d0380a00c441ca50200302482151442c41c0310034104000c1400704900c0e03900000c0080d070b0602c255130f030b8401c034241c022400000400048424040a00010205 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 216631762 1250 216630512 216630521
    0xe0106021e0606010518040b0d03030501170f060130120f0e031c03020c071d010b0703090608150904060b04060b0403210c12020303090d0e090411060903030a110c04 72
    0x9a80030410911030842c06c6889103600b150540c10080c03010401e0b40b415008240c90180105064001a44541c0140440300054042640e2403112400824031a4040c0c0780d001e888040c103000714621206004400e40008113811101c48007034100d80c01c01c88100013186030034040c000000008501140ca03600800c00611300415080e560410301030054092502d561440342d418080440101091641c203104801005204020010140c4403072210007070040d01240503203c01e0034050f840820105070812000300000d0740001e10004a441d503041c45401500c410301030000041503158044c0e0042140b1040006005240d00014000ca1099400b001010313101c10303512105203d03501014207011582d040c402c86052000122102c01c0c900e070b03c2d100c2046021551003191544000250500503440031050042d1041e0511414811034401c1c200032095140c140086440b1800040010f0080003541203080c103039450760012980074060042c1a207603203000010b4040c08240300300446800a10910000c0308a0342060b101c3d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 216633012 1250 216631762 216631771
    0x12030801060f051902010216050a0203010e0102090a0e0712050f0a0c0504080705090a060911030103050c0a05150702211609060303080402150d09030c0201030f0908030a0905070e0106021e06 83
    0x1d0f01031900000c0d20708000b01c83d585203201c10441d076080007605400424022000c00240c403030006045c089049004241c00e403040030403801d82c183d104010f41c60203a6210075140084a04003071400040d592012415142d50000c400d8042841d400c1a0402071080c0d10f01504510070304010401300042102004100e0b85402540200f180c540c1c000381050010b441d005804c2c070340c0803001d04004584207856041400a45008081801211201100602c10414103015109181100303540f10725400e8a40700014801030590030400c0f010384d20008054080d0340724500014001d0390031000c044408002180352a648007440e1015100001000074086080c001602a10040726010380d0b4151807a07c8a03001c2004c40c1c449141c0c8040412400c22200540d5111030242c000c43c0c90003501c0c0c103440c4072a2400050305032141000300500c814500401440010b9520056a411103c0b6402c0000c070402140740c42890185c9941012295803016800000c1d0303c0d030700041800709103124843c1014401c1c09904640e0f5900800d84 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 216634262 1250 216633012 216633017
    0x41a0906011a04050d050a05100203060a0b0c1006150210060e0a0e100609060603050f09120c030c12030406110406120b04090f1a1302030a12090f12030801060f 70
    0x100b2a00090340c008000702e9094406a03031070f01365541d0001e1503203180c0d00300c201c0e0503421001c151001d202c0c0c14099003c10241ca00019882c6107820400110390f0009402252482900800d011814030310400003080714040050b400c121b100e44540101c6000380d0071030a400010303c20960b100309404428000d0200301c41185603108159101c00924402420510100d00f5191040050b081c500880307a0242000418510000281082c1020703070007003e482d4000e120040e018485828080901d10008a44000c2c00b0394100d0f03d5202c4a800a04601354400c0480c0040940b190518ac800c142c50500001e5008a00c0364104102a0f40c082c5600700c0d15005901c41e640100300030003a00001c400040d004440c60080040001901d02102da807115a42d0200c400d040d81d401040c00d03031500c0d0001d4400301d031640080100091030407140242d030000e99100b1100350000c110410b408098601180507492803805014038002050180e034485203090041d00141005500280a0000024506000c1d503111a240400d65 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 216635512 1250 216634262 216634273
    0x5012103050904090f020310050105091b090103050613060906090b01110607050a090e07030c110105130201120b10050310140a121a011502150709170a0b07030203041a09 74
    0x14400c20008000c0b20384d05940c8102c0581c1c07540011b0350306102c1d00007007405540300081d81e0350501090100d40d4600034050f058136200c21140c940020f8022040e01d000c0402407a01103120340da64004111850f51030601c1c0032006040010128241e034660f0806001e58404200402c2000c0c0c1c0f00340115689042802d1040664000c400456269441070300100289466418880183c96840804800d541c0301200c0c10800039950300e11820015501170001412080c004000384842d041146440c526005900030007818055958214010034055801027000c115009100c1c4a0800d04444040d00303c0c1c3c4215403074601c503c41001c010980034440440703000c00c1200681542240c0d828404517407401410107200f5562000003c0a030f48540c0c40c2006035501820300301d14002c4a9681c026000f07847c0c00c00079031172488110280d400708a400c03544541c205045804401541461000c808085410216083c1000c1e219101c240c04200f040da405400960041d4403400c400025202c00c0701d18007040040584400705590400f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 216636762 1250 216635512 216635527
    0x31002120f130f06060303081e0a0e070b1815180603070203130308090a06080112111f0816020607020607030515190303030506032107240501210305 65
    0x9000d00c164001c2d140e40e0344503104040c0f910ba080b440c801890b42100d9407502d810b024000c0544c0089481d4204051a40c0140818100c034400c06030b001c0c00401070000160344500020308504100011402029059252a500c0641d03c2c801038243d44c080d26154041c440b030044420821041100721201a0756507076180180d84425002c1001d1544081e01240842c40188156207510002d2401440214841c47c8429621074056040c8944616154040001e0124400042200c0700c030200e003505240e58800c909003408039031040000c54640c4050701c3e40481c0600c1e03001d68003225400400c3c581c0900310301c41d409550084c0c840d01c102d03922001140c0746401a08a0781c0071442044c000d4010304c0c1c20040308001c551240320f205011400c448c0c820000344222a00d903410400501d0b4051140940001054000d0010881600310381403c511680c04600f19074000080d108048c081c001c404414020303100321140c80080642c0740400c0240001b8010082121070419103d590380342803a0740d40d0f1510303a01d81c80300d905010b40e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 216638012 1250 216636762 216636781
    0x40812030a0615030c020c120a02060901090b0d020904150303171009230105010f0215090c0a0909031e0c081c110a08070f050d0f0b1207030203100212 66
    0x10705200c1c85203844140c0400d402450703411504801e03000d55000500c03030343d00c010002c0c43c0500501c00240a4540307403041d00e150b03000205810810b20340585407960b8590700e8600490322103c5a6008908854010034005040c040980041c20034070812681441003000024110b52396885520008010400c0e00c849a40c45602030010968049582162820103503a1803441a040d100c00102603d120b0725179400c08040d2212100819024210a28210305580001140a543d0b0500c2d2403542514400010000b90305100400c08800391803000f07000621025554101a00076129001003100400c0506000b0303140400d81c0710500c1035014456803611080c07a402c2c3c03141c880a501141128807221048541c00d214046240120074001c0d41c030703610080e41c44d03104490003031a142c00039082408008a4004584c5101c0e84101900c41d606441030300090a5611220500020328640180701e40180315902c0201c01c2a402240c81c60460340240c0981c0c08402e00500d0400491103030040c2e60160f894080045001030b072 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 216639262 1250 216638012 216638017
    0xf0a050402010908010216150e1509100c050c011b050405040f02121314030c030a080a09050f2508030711010c14030702100302070f0b090309060705010e12040812 71
    0x5006040115100d43c0700d010303c030700f03907402000d5035840202c2c1241c080d0208200c0c8486d008c80c1e071265100c20080740849080c4240c4801207103802000136100d400105081320700910003e9504a192001040443d0040d1000303000d50704001c442c5805540380c01c4080c2e52001c030281401418400742e55a4500d0326040c01e08000060a4517020b28200c680c5c00d0010702d04804901c3e901500400c400741d40004000c10b54a4800c0c0e48050040c081c0c03466400921820400c3d00c000010703109000183c1c01c200b209036840060200003030800020103001c51060301210240e0400109102000d240000803454503e407c003007080603e044030703108181d00380e40304000400100d9408006040901e8051406846000c002d445024101c04040c0e00b00409070000903d01e070842c60010102580b01c5c0f413908080d07082200359110380750541401386014140301e88400000f18180824412a00d00080040c60b49031120102d0800e82d00038003100c61109143d225412111102110500a49040700d0310040149051030b040a10501282c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 216640512 1250 216639262 216639271
    0x2060115110102030903031501110c060706020c1e160509010b03100f18061208070b07091203030e010509060610050a050409020403060506010906110a020409021302030403080f0108060f0a05 83
    0x194000307141480020030700003113000e4007a0200864403402e0001160030400560103030241408580201c200f00840045040354000400f160415104c000f2410680c000e44a10713802d8000f2401000c034001c20107d2041ca0400b591039094048070b00c0d5600e43c2c451741038140310071700840b5403260018004001d1324010000031a8010f0000401c0341d5000d50b40d0920170004131864008101d0792880d4115201d07060340d01e100b080c0082c43c01c400d07085403c880d10f860303c6020303118030280074182c1d0110000103001e083c0280c10b01001000102c06950580c9400d080040003042c0c00301c2c00d003541e9403c040100d101d40e100040c0c814000c22008090941d102d00d10707101502d10b948000340940074403030144000515421248050310046029540210301864610001400716071a41c01c00000e00480c03112036100d581e4001901100035034142c0d400a41035903180005074901ea0525140500280004100010503078000c00d854010400d4000f03006c040e981350702c40d05884810031201000030340a090001031441c0c0e216000280c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 216641762 1250 216640512 216640517
    0x1a0d020603100f06020303250c020607030e090a0207150204141011100603060e0609031b010204030b0c04060f0219022206230a050306010b092e030b040c02060115 71
    0x1c86680720f00c000b01e940801d030b10120150304040100240034103e0510014400c440101d040c1881d00034140207050500f59810103801510080703001420503008105074064004001c0c4608000e1600b0500003000c4d500401c001c9400d0954150314503003103055402650b09072141000385422244011081c01403603e0034040c14020022469210711074244140800124805080004103a050860a05400742e5150049001140d4042e02c2040820480482070f26492050540340000e020350000c00b5070301900540c0c0010308032a1503181400008800030008004a40c265100d140f50f4180c40c9006076101e42002c080c11060f03125044110303005161241c50417400d4041e80002c1c5c120000041000000c855141c0c2200003140351540194580240c5d10016050700c2c10300300c400c09241d5040c07101080d107902040c8a00c881242d80443d4040480d0390301200c1054448500401d0340d40c1d109032a01d003c0c20803c025003860042071920744500d07224105806444601015900104400c5c4d103080030300c20190502080b40c104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 216643012 1250 216641762 216641791
    0x913050c120106030c030e19170d0608010b010e010203040308031b070b04060b010201112106031f02030a0f110a080702190506040506070c0c0608070c06060b0d1a0d020603 75
    0x50003441590850b01800301d0b0b913800201c64901c014003504980034100000082e034410a00c0c20002014417604407800303a40070010882c442c2489903810750700d004009000d1400c03030400030046503420055021100c010401d0b61640368900c500001a030b2284600e01001d80302080070030018003410b0b880401c2400c84c840850100c0d01d000385503280c0c5250040252400c42c0da064607401c4003100e9603424090002807950340c4010500c1c0001c01c001c01c0304c0b5050b80c805103410b5118500c001a07495031301030001c80718a0f92206c45801a045a10340f80000079401210810391684ca41202d150400c00c451260030030f07005085440c1841c080305001d0548814900801140c11031154844590000c41f40f0280424818490401011941090b1900da420514014040000c00a400c05034170041448000301c0030444482d8145807401c1c0e21307a0801214003181c2200d001e00f01e142000800280c40701e50f400209101510b44000300141c10b00c882d0f505905c2c1d050341c124194003003110520500549052402950002040e029046 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 216644262 1250 216643012 216643027
    0xc17010b070c0515031602010501060e011101060503120304050601080105040804091a060c0a1502031003030c03050f12070201051f090f020c070605040314070302010917030c0106150e01050913050c 86
    0x1a460089182075a80b005004800d06c1486400042c44110748030590009001d290f041400052aa0f81b42000c02c1d810080d545034508046a0298040006084050184c402d01e5000d0300381401c05a02c141c7e030499081c454130300002403100042c40f8280c003a0758082d00b0185054503241e2020060b003020000c0080c80101030f01c920742c00c3d42c0e5410003400c060708480c0244c000d041c09810850100c200105803c110702e80100200f2141c0c8420300b402c0c40a49615042c15000a03072541802c580c240506417030700c41e1340c1d80300017a0300743d8072680310020910440140e03009009a944410032032880a40f8000b84e041d8165802c035003803080c0280d5400602c4d8401c2404030041c01c086140307512920700b00b9581d2108002c1b401c0060700384180009504920010303403102d0010140a40f565000030a98a40303441200b1a00f50034266001d038403d020f204503084200c0c001d0003442150b440720000846c03890f402d580c000105040300d11342e50700c1c0d501900c02d580304a079000f08804210310203040762002624000342010f104140820550 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 216645512 1250 216644262 216644269
    0x60e160512010f1a030633130918020315091906020a030c090e0a0b0607081305100908070b0d2702010e0a08030304140f1b040c17010b070c05 62
    0x1a03009200022030f18240e6880c0c01802e540750403844414040b4000100100007281d10f5203141400348a640d0340030f403200032191200d40009954085240301201100241c01090100701410305402c2d00c4400c10108038004100c80c40f0205280800d50007901070300104498a41003110802c5581d220a144060301c039019584003805408180c0c64000b241c0301c943c0428a070000503458801c0c070f101d134030142c18002d1855060850710601d201c0000d00c028401c0e500c540c42041e064075200b090f150f2295101072200c0e01da544000c00408641d600380906800b413140e000c03101c42c1d024801c5002c841204d500070081c28103513007405540c1c000d561042d05042038560304c4982d1101652901c5c00081c00b00344103c000034006541d0380c0b0005103554401d0228901c13030404860103100c00c0300301000316a0040d40c03007004000ca0070804420241010006400c10300c0c40d010705141c400f150a0000e880c4042100211020090344802c94000d44200b443c41d29a81001c0c05150010b1080c03001100041131624040c0302050161907486001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 216646762 1250 216645512 216645547
    0x106050a030501051608010807140301020f030c0d0f051911090604150e01020102070305030c160b09010605090c03040f0b0a1401061d010c030807050906040314060415060e1605 77
    0x44680fa0f549004010708042c442a00d100d82901c2c61524601c19450f200e103483d901d50b1640205444416068001042540d0950440e5203204800768901c0c2c680c030b0090390300e0720140c00800c004d00381e00d800e0030358101081e92640315030780c4500303c2da1020070f81070034110441400031320908101c0c0b41c441c141040b03803a54030b80c2c402001e8001400042c850318035403c0c075030600600c0c10540301e680905681c0148800701c00260046d0950341d0117004081002d844e9040181c1d000c15108100d200580b421001030140500503806400a07002d0361401d03a00384000382c948c004040982d110444016084a0500320450000b03091100c00a0700480900c0010488000c07184000d540e054080e840440401d0703100e03031b90000000d4527200c1a20402c40900b001d02d5814034940b005011558010040c03800c0060000d1002d54a584a0080d03030003854004071841c000c410313100d0311150748410546040d1010000d0708018030604259000d540240c0e411114182c40b41e807501703000040035280070321042e003e0040501c11181c0341d92000a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 216648012 1250 216646762 216646769
    0x1b02011b0f0212030c10180c09050109200927130b090f060601031d16031703090a0602070602040518010302010f110316030e0d030302120a02041d090106050a 69
    0x2400441000a204000c000c2d50400c082c1c3c002500103120451078613201240801b000c0c0c94903c0003048000c04002d29401050711140d0080105010f00804103013400c840d4061030583d4030700c0303000f081081d00b40808903da640d140e8a055500180170401000700b1f04102a82034400c0c9000034828509412112500465500031607400199003801c0d041d0a040c040c0c10f82c440f50b0401107283c041c0042040a9484545411006080a041c15125014024003d50640d0038071051252541070f28020280c0e01d800302c003003151505c02a1883c4d82400a1113010201207011a07010f2900480109081001c0b036488802030340000f0000c0e42d6940d030a01000419440306102a01c00d2458102c120b1107943c110320001d8002c0c40100d1081e4100b04070103480d00e0701281c0002c101d88260051004d02c000c00702d014903085441b032040701c0358141c00c501c0001440c020150190081c1c41c0a00004c0d81e01c410765601c00d43e84400320302851184500c0103140304103623095841100d81e11034000b44035000125106403500c0210b2240d200942c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 216649262 1250 216648012 216648023
    0xc1704140c0d02060d09080409020f0d050121060c0915050901020f0102040522060b0c060405010f0c1b0c08011b0201060504060e0f07050408011b030b010f1b02011b 72
    0x9040465200501c041107030441e0407034070030070200c074503401080307141c043c504114001c5642d4a04090511980e10152401801354001c20740d95501e03000503200140d00040c041044182c181000452400181e2801d10042c42c9401e500302490b0004d61100c00181c4207500d280e406209440300040740035050034139144c5d40c0b2002d0f40c4520f070756282040002403030003200e4100c00c0e89591050005000703039610000e52142e42150390310f171420009070381410000100003030fa00180040100007441652103201050f40d52013140100020080e0550412146040c1c40d81c8000d0040020b102c2c2444001020100400141d890b000721107811084d40c41f42c0c82c1c3ca0071540601c040d2215000f003800d40c004156824050b0b0300160100707480c20b002c082c0c5821089810b510300640001300074074a20000640d082d1045081e40c0052290710000e012040100c00300000b1102200b002c680000d080a540f4100c95010b07960b00b0843c0d410f160b5175a0280e0001c1b0071001300c80001000100c0c1001590070720f040070751100a01d038010345030040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 216650512 1250 216649262 216649283
    0x30409020a0f09031203110f0711190602060105060d0e06010602010605040f020702090601030903050705070f0501080a1b0e01090909080c010b120d23070c0306050105030c130c1704 79
    0x1107015180502e00600758080040340c0c2c206200140500d403e56140c4c54050802103a100007480542c000e80c000d680a40e105a18080b444000b480024019a0301c800d1042d240c950b00c00c06961402d200c1c1c481d207030103507101680c000c00c01002982050801410f03800902e9000080c04e40e4a10046420032400307900500060b9100c0d58140018a464030807184440036900c8114541255a800f04000c01e400620b114140b543c0c8804220506000e8000ca4110302d601c003040e03500942d110620300d40c0051040c061140003c030400300140d0031119902c94102100e80c0b0031001d80001110150032155102d480000c14108603070f80b840047c09003840d0040300780c07203403052031380a481710401c080f2242107031740907002a84565044080e800176440b0204100251902519150318051510100b841039141e120b50351001d0700400150603018000402e1042c410b0781d2040e64203100c1c9903039403c00c040d42d034014600342c654401c54048015084038410b5214100c0104581040000e660448801c0c81c80c5aa040301c050354100c050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 216651762 1250 216650512 216650527
    0x6020a260d020a23040608041104020f070501020706050a051515041a0417010203040213090503041d04030306081b040e0f0706021e060106051c09080d060806010e060105270303040902 80
    0x6204101303184803080320146060902e0040c000b0040c4c02c014202401040030070740c00030901d031520b4040301d1001d10030b001800ea96030220315142c0d000f54451001950441d1501001c1500c080e000d0007414015840c2c05011000d8100c000b08115207400400b84105540e04200400100e140c1040520550304804445003a01daa2402d41206202074090b0032040961b4030402c1003100503540d0080444c0d0910b142ca400054150f01c6180c5a072440c4669004101c14003111200b407020340302c10320a501d204511a681c240140c0781c0d070790740c880d0390361704421250726140c11a007100c0c0f25582030560000c0041c0d2102421507082d0000000c2c0d090a00c07030103420242c0180c005d0b40c210040f00d001e2100841018070140010201c81d03240080080140c01602c1c0c6207034140c041a1784c4e100414000c0d410001c4c10980000c20385603542c540351001d038000c01c182d11604889000354400003d201407280700b03080c4504010f8540c0c0d450102c40700100814205201400c1c040d88102d540d020400340c0302003010304098a03000d030b40166039004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 216653012 1250 216651762 216651797
    0x5100303120f15060e180106050c070308030114130507050409090f02120a0c060503010e06040f020d0614180108190c030807051e0102071a13150b0a06020a260d020a 72
    0x40c100e1700faa00854a00e00b60b4080c010003500903504680c820b05e80070f91600301002c00c1c3d80c10030205510140ca03c84c1c1c088008035009991000703900306424200c98184d001003d000c1d007241515811190b640200d00244020000c00c036083c4c00012107584901c1d0500c820400c40e40c00100c1c4040b040032102040c1d07100c42910303c10801044032010203400305061590840d0701d407a40f0f0b401030400050045001d05d80b144038000502d180f68042d10a04070706900b091002540351111012140000340b0310a1048031149140703407003800c0050f50b2506883d0840c014048246442c40c3c8144140302d948411149192010800408544140081c01d030981c4200060081c0c507602034041800b4948210b29850f069204100600c001040c0104002100120409841c441c0e999980961803171926054098039180c2c1558a8842c8175415a1204144c0d440460728204116200c0c00b0032640c0f103911840037800c8951800c4e04011207079100401a0b0540c001d014400d03d0301200301c03190b00c103903000b0003c01804119400024900c2d0391 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 216654262 1250 216653012 216653027
    0x1030b0612061c150902030c060405030307141518010b0a060206070c150e0102070203060901090f0b06030309060c030c070602120a0e0d02042a0305100303120f1506 72
    0x104129811401c100302003244480c011409000b25110324140104080b01e058024810542d042e0405070f0444d0790854040f0450203090079860407482805201e6140c815803400344146c07801d450002d0025401d28010f941d0b41c4902c9810000e0202441c46211880c040d203503800d0290034414204500d0450100001c25440c07400d450001c021103104d40d003d454148001a400221554010a107140c80f81d000342c1c86040c1820101028113403101c00504108090403011015002002c205109900300c904540e00c5480450807500ca0880040c00941c000c070000012400844900341c11600007000e40e4a08400c56000426a5000c410718043c2500301041c2c031383c407824040c0302d242d00a0500d4006480e005c1c02d1020103500e28030564081c0c0d400c0c40749042c600d6410b6100d09104801880d40600b0070400d0003806a4601011401c26002200c08440c40444c606614402d01405e8061152a403003440c20704d08581d1306036a90915500a422a540e0754800d1034030520541c0074091010f82c107101c0940d03180381010310003017048 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 216655512 1250 216654262 216654281
    0x204030818030c2d0418050708010c080c1c020304151812030e0f06011d090a030e0d02032a0102150903161a0106050406030606111b01050705100b0103 66
    0xc0c3c00803111440d00e6201c1d410030900c410050180f502c1e00241401c907080300508014681c40c2c00030b1910700c42400564042c842c0401d0f481c0240b044401d16603541210b00e007618500c0e0074560020b00d050020811075017005002d02080d0360440d00015074040041016422608111000d40e0704030b050340e980c000825560311840d200205950b085041c0c0e500749485403203501c0c0e0a10a07070801c140e540c1d03503807800c500000d000310081941104140da105507542d0041401c9000300388000400008034502080c00d108000516070a42503240e224820907001850400000ca40b0b080703020398041c09090108003c030360044024250300c0d030b90854040d0071215840b0009150480251600804c07414040521584440000507980e07400c15984c90100c0da0407851410300c046413803010012010441081c008a03120750000301a2041d10400d5070100160b0b80d403900103d901581d000700c0491103402260a6021000000c6050b1380300b1201810f0a500d05403040e5100e41c41c0803807040403244c1e442d07561044150310351b902d806040c146 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 216656762 1250 216655512 216655519
    0xb16030c0e030607230c0109110a080604021504080105100806090109030e1201020405060a0512070507020d03030c140d020c01060b07022110060e040b0109020307120213090204030818 80
    0x11100d074010039641c0101409010600400c00980e840c00c8040c03035180c6102800d1300142c1d1384c035203904a401a019151309842160404a48116402981002d20301c1034120b480071801040342e600c40d0f4090214001d007114030044284000c000105505409005150247d60804c000c10012442d1240050501c20064080010f40e41040c580502003580030706013804e0b0860072243c0e550a081c080110724024071903a030040360400760100d08480f441d9000405000d01161400c0c00a82d0356944141c1140c0c18416804000d6210102c01c10490100c0c0c07095000c511483d0b141d00b01443c5800030341102120369042040b04004403500001c41840d59a02801540020180e902c40f09003003042c10341c00108139440780d000349200c0c02e601000c203800c4031500f0080325440c10b10f002d038200086030b21502c0ca0702200304210303401e03152000303ea40000740341d99180c03003221b00c107900f03550f54550081310b40d034050400396100341c1b001940d448412a02150400451005000441c840c4c4110340d80d480005005010a01d40c21031618031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 216658012 1250 216656762 216656777
    0x512090a03030e070f0311030a02030627011b0c0f02060d0c0207050d050d050a0909060f170f280b07020d020f01110f07030c0f06051b2502010207030b16030c 69
    0x18641c0c400e6040c02d0f80e1f40190a00540c1000401292400502e041c000c1d505228a8082c040c0f0100c0000d07107080c0c1e0803148240d1011460301d000002c0d09a45c1c03091000306003509202040040644078944400f001840703213410408100756130300083d91070380002101c40d50141c0e540300c103145515010000c0d28010304003238501c030380c9801e2180c40702900c03160050762900a11000140c5445600d10804825019001c4484101702c4540c4a1042d056500090b0041460810880d03400d0b0122981c002400301c4003070179110041194000448038000d90384003410002d03180001c5490040000b58585074490f1143c1d10b0b80d402842e08505007500240b038a60400280341c003903494405091100f5402004881c18a405843d450744e4904d807900c1c04980c9542e6211000d00302d00d1178580b8007010010280c210314001c960440081404040781c01c59101140718514501e15110000c2c0010704507051521007140e030080c0140155040c44d81d4a440c3c0800c45402118502c0c0c61905403030030494034540501c42c42030b0100389071401c000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 216659262 1250 216658012 216658019
    0x60b090301200702100909020d0902011b02091f2607051008040809060409020705070311040e0309040e031c09050607031a0d081c140a02090d0308070512090a03030e07 73
    0x40140f003814006401100d402d48034030035060251195100800c000c1d0808c540d500b450943e100010000e60f84128005400b181d03561390403158840300307003c0f0b01350018400040c9848050340c01542c00304000d424004001c48003400500c032280a11001d410040e0042c80003241040c0188441c100030750364016034802e4040031110340f10281e20580e56580300340d00149103552582c000001441500a03503001324461030001a54404208002ca407608c2124070034000203002030306810812041e5043c0d0000f11884d41d000b0322112549103490f0300b020143c00100002d41c0e1031700c2040e03000000d00203081d541c4100c0781c40d11041810108281040341c181e200d1030074a000c0006195160242c144005c4c0301d81c1ca188501d20502c1c800c81440031403811595441c1d0b94104c0e031110f10984001402c00741013020f1200301d07003149c400c0000394202161700844840c00c0000740070314045c8900d43d906841c2030300c2c094400d404100e030501640882e0811130182d01c1c0162038500040c0703e01c14451900030140c5a4040b450110364005607404c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 216660512 1250 216659262 216659321
    0x609070c03051204020102190f050115121b05060705062d0f090708030406031e090308041b05030709020c0c0f01020d050912060106210207020f01081306060b090301 72
    0x11103c80e011290894010788481c00100d1801044008040d540c20404881d9401c019064100f0401680319100a020003400c046c0c1d02083c0310300c80c1c840c07442c801140b030001c54001505000000110b40b44407285041a40d205d4000c40d8440d0032800c070407a499807102c424000040902c19080d142c18041400e6031300d0400f202c070340e040d40a0b41c003d054071003580c401c0030102d01c1c054410701149000e00000000c4070303202e650f0384034028060315842d004420905168540d410702d06a0b01d001d83c880b4250141c4558003d81c03034503074501c200b0ba54503009a40f0404e40311000800d8039902401100001d010044000d61100b10302107405040040060720940b04102d01050003600b40d80201f186110000c03642400750b19400503c0c00b0035100c045d07a0390461a035009840000c111190081d140c3e0704100c2c101001c848151240e11700c8181241309203c03000c0d502515040f00020258400d0700203591100107034100f214680d00941e44c0000340c80700c0350021443c162020903801e5403030909202d03c2c03400b030580d0708507000703034031000707141d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 216661762 1250 216660512 216660517
    0x90503060109061d1302100336030807090815101202030d030f090203150106142d1b0a1712040602070501020909010305031c06060503070e0102010b060d050609070c0305 74
    0xc083c3c4e07000c0f00000c03021031100501039426500a0700703401e421980024000e008000840c440030090707440304120405004c00d6480d4243d04020081d1a040104140d2000e5910b00c000a03c500100040b001c40403c003844244100307803c0c00b00030304003a041e600304090342440700c4940d500500108503040c032801000d40c1d0009140f014440c01404c0c0020001182681440a0010000b010f5091300c92a1180a101507802080c94101c5103582d4980203c80b03150b12458901e44900c1001c86035142c407000f00403040d128012510f60380d011a88a00900e0283c1c100c085400c01d403031500d00d0a074140c100725440000d00c052034507c40c03440041c05030340d149000c840352951040f4110250010384035507404501407003002307001d504480700084011b082d0309a541c2e5a02c1c21a6407648a400c4552480310442800038028070b55014400503208540c50309030850b0ba43d10412210020340c90749040c115922444840400e4540c400203040d0314400c400082214900942880310036140a4481006c20000303d1508020a40c888207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 216663012 1250 216661762 216661799
    0x3030a0e01030612081306020606060d0b0d0c0905180c0a060302030a02040807030c1a0301150c06090b0a0609140405071206090c06050318070e06040f1b09050306010906 74
    0x103040c1952244003004070000c2c9100d4001110314100c451840060001e498040d0442112550611400989415040782c03504015508590042c1c070502000036034024039040765825000141c2407442c45c0340c140d2103640c043c200a0b800102d169941da018090918a5802d0221a40c4401001080c40d40398001c041461400184070f070f042050341c040f01040d020081da80488000700451411a15055207904000003c812940b0580030f000d994040e400b0050107646082c0c904031000b1511034101c0c2112420203407880001c20004845042e03a402c11080001c1c8500160740c001c80d140c0f030300051800e0410b9104001c4400d40c0e00e00384040e034030210800000400000d01c0d0b40503a402c11210030801503440c507065010f051076030402003211019180102e52030750721001940c420040900c0e4042e22046c2c884003103031030342e109008035a074148501c400a00740d4145030700855400e03c0354020010344018411080001d40c60f070000b0500014081c0002003105190410859000d456480e10800c1042d02d04031020003071626840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 216664262 1250 216663012 216663017
    0xe16090c0309060c1107060908070e0702031603110c040908181504030303020306130b030601090e070e040804170609031606090b0406060302030d0e010c110f120105160e03030a 77
    0xa4a58018920a41104084540c04a0709000982620601905d02c44800e10f45a415100c0c00030700160b0701e44220b0040c1c0840b51204080c2442c68180400300c00300759402842c0009500c01040640d16003245c06008149860007552072800f00d640c0300740624200003000d07078124131a0b0300705041e50300070031094021541ca403001d4909034509000010081030080300800c410301001d0034041000820701d50160025440362a003101d80b24030604114844000300d45c81c81324010b415502c080c00521025502d6445a2a0305e001d0400729642c0c95960080c44401090845085801c80c00216003080b40090ba88410381c42900410b000e4229460f202d661a40d6038041e00c070354108a42540b074181e5050007651707802a04044d8100a003000c1d035103807034140b0b00050700d41444124000c0c4030b89400302c005a07214020701341e9403440c140d56a030a0030b110703600d900e03106160120010764400d1000030084015a40c03080c00c8081f0340104030010949181074120074080e91403418031241401050341c4403401964011044940c00075190 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 216665512 1250 216664262 216664271
    0x10e030a020615180403111006080a0210031b0e04050a050618040f14011a0f010903020f03010b0301021c0e0106060917010605100909052d090102070b0c0a030e1609 72
    0x9400042804001c004e00c0f00303002128000740030906a100155502400014048881040405000d5800c0b03c030144240b8203a50080044e901c01444c04104140e800041e61502140b0f07541c3c103421141445d030001c1a400c0c0401c891080c080f901342864001c041c3c3c02682604100420304e032400c0400d0303003145548a1088450407d8001038200402000590306241d0040080c50040c00888060790080003000d402241c49024080514000d141031440030380c1c050010303901d0b41201483c41d402e0200a400075140c180d03055403030b103107202e000e91000d2002e4003a03116030f84070080740000690200001c0310104020004140d0500c1381c18010a83c1050b114022208117000a0f2a20a07184080f0344c0140b180744c0280d68403081811007607003d603a100800c00140c6070114030401058035802500480340c3d1114550480d1544003507103030701a40031504e6180c1e6109480100140c600040ccc1d958801d074481084038040c2681101140f28111180e05100d040904602000141000d180c0c0d4960503000c813241e8410f034803120740c0740c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 216666762 1250 216665512 216665551
    0xf1401110118020316030809012102120f0901050c04050d02031903020a020910060c3509011701050f1011030a090e0a1e0203060409020603100312320708031602010e030a0206 76
    0x2e0701c442c803144c0d40c00130a0840d24cc0b403150030200c403096025540f100e180c15035480490f00051061140743c1c0121000c0c80d0b01840c06107000c0c03d21502c000385c4007060703074035006100385481c010310050f8040150512a50151103800221300c1000b07801d51001d0700121203000045400d00110f40c0002013219500d40049140d41c180703401c00c103020b00801d2529290000000d482c00c1290344c40b084103020f403001d0542600ca42c4a294100813040310144024072900341d05c00c1c108c1071505628101403140110b20656450504104400c40100b05e203540d000d03201a0001450007181003211900000340d031900b11501d0001446480851089041d000e0320740310700e0715400c9038000007150150759140e0018103429400340c82ca5071685050901c00d6000d605511080c2d40092804504090441c401c0b2501d1443d840c0e40603001d406400020020040b260060100324180b0608100110102d14a1000745104100d4140d03a11380800355020001e0a555021404265591050001140c681d401003080340d8000b00d5251040c0600c1c8a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 216668012 1250 216666762 216666797
    0x504020702120a11090604150308070804031e0303060b030708151908030c010b010206070f030f020d02030103060b0a09060b0904050c070b16020c03070f140111011802031603080901 79
    0x10b0002d822415440344818400801c02900c0d010070000d082103542d4012983c0e40801e00c81500c07401c0840c8811504505820b00c0040e0601c406050f1040c09043c00703908081e229540c00e28080003600d600c49290400c2d1014504055260140714003804403201c6450860800301400f40503108050102c0a11200e020303901092900d030068480403894010000c083c030300745c0d1010519240c1e80005030310b450550910f00340e85180c3d4000a007560013143c0382e0350f900c182c084c8021300450041c442c1c5d04140c60566003c00c80c1e1240115103001460183d40a0a400039090808104004200c0e10a6108814590406204120001505081e00d04061055802064981d2111400300c1d4510030450002e0100c0344180900141d51542c6d1020103200030a80c080b5490715540004260381d914003032054000c03a0032b0610003881242c146142e000700e16074040c10304154464003201c4507803d40e801c0f64400d08a00304075500c0c4034250b24041000c1840c0c8800c032024250003600795154451144140b1402034107004281e0384e8024803c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 216669262 1250 216668012 216668029
    0x506010e0a1b0f1e0309031202041d090a0f030504151701051e7603110c0402030408040e1b120109060501052a1f0e0607020d090504020702 61
    0x4d43d000c024403500d421400540181401441900003914074020324402100900c01c4609885000042c5010f2040c1d4824017108008001d02030001c41c0181038514000510307020819450620a4a440d0f03142c40c01c01c106010300c560440c920104014102c0c0080c009226500b810505580c82501d40e5100041e2070340d030003116030481013216034101c03444000307848100d003900000625810700009030700701c001d90a803054514500e0340c002034070203038019410f4500e2500030342010318030582500c0817030801d4050130780240125002400e01030b004100303044000c09016a040c8a0318468000494046045050540701c0040a0045000700060b103440107010802c4100c1c1d1403c0c600c007204603032462560356070040b820700011175000e01c02d045410742040b601007250343c0107405840034248409001c1c40d003010005607407040d1564010281106010342140261121102e0b51000c107502c4030258003051030b20041e078446103008401072000045402008110451a5000c550f1004944040341c0150301c0d120316000090407103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 216670512 1250 216669262 216669287
    0x201110a15021e07050c0d0f0501020c0d12090b06060703140304050a030212090906040c0915020c030d09081002030c04050a0e07020601170a020607080c07030506010e0a1b0f 76
    0x10307031030300e1020034030000150010a000d00c05900c0007000301003090710390700031401558401401341d0420700307400c1481c0c10404101071404e4050030001500403080c1d01c075542207030300900c9045019007040c00b4071110705da004070850041c84260502001a94402d45a8032458800601031070f12a220029800c02894480c860034031400a07240c5180750f603424940340c61130ba2540176480444c098050071007261001d10b014010390344010405000d014036a0340e03080411009044203401d15081c41107440c4085400c1000c000b441500286a400600d14500500e042524020325034082e402005241d000c240103c540104440980f84142040980c99446440d2400303214007941c3c0005801c802d2241000840f804003440442c0030751202d40948203543d80341d84402e0f034040750742103200016505c500f020703400500380440100030150007201e0403410880e12550040c104051035000343c034a80c0c802001844000d0b0b0064120b5044032540304204451440c080d59542c458a50340021000e0000c800d401c5510700740580e4001098 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 216671762 1250 216670512 216670523
    0x9020304021f09030b280906150603020c060115052703102a1d010c150219021b041a090705030709050a0e0406020a0504080604110f011b0201110a 64
    0x2161140000280f0000b02d9220540d05100c102c0040795000c034951980e40ca00e07440d00b14a0707540d4038002c200070901908a1490840d1244d5852408e4140145040c00340b00107800c003a07802594801924594034501141038118607c0c401145014500c141d0308501107584298444d4024000b0560300d8260f00c00c844004100d090709400b4280001e807078422203a00070062003102c00f0600c1d0440041e01c444440c032406c01d15090000c1a0004044016038560b070303020b5884500145070011054402e50342d81031480c1c19103580d2981c40b507008980c3c1e51194507000c107692000c51080c4000c000c0d618000050b00380d4504041811400703031303a03540390070f618051500b10400300b00d410280444100d8204140024403d80c0304407514000101462004112032804190f20303400c841d6404ca080d8001c2d01d458940300d009500c6007600c0418004200000918032400f8000326101750f0090707505507440c009503010302402d900c00c04040c504121403070342120303002880c0d01314007400d1507020f103000c500c40d88040224500d04140340102902 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 216673012 1250 216671762 216671809
    0x403140c0a050307060c0219020411130f0f1a030f060d1209060e06090a03060203091c0f03060501050903030706050402120307140d050c1b01030908030f150a0506040902030402 77
    0x1c0c048004004c3c00210b20030700d030401c414000090b04a80b145041090f0518110050394888050b20700b58100071900a4050ba03128648400100c140189034420340c441061408004801c1062a20403610360004040c002d07034182c3c0340c0c0d512080185240c400103251003401344d0100c0100e80705031601900c9540c61070740300008654450707001c00090b0281100d81314140010b48002803d0038a41888015030340b901e807000d0a400e00700350456030f6940103900f000300808203621440b910b0002c0303012107c000d202008080e4440e64030002c5000d070020706903050342e044a410710900700007011541d1000811140c00035041000000d441c0c407503100040030a4840721401c0c05510000c1040c80c24400030041c240280301c6142d040700c03c810b409410a840600401040300b50707941000046003003c001c02d4500004012051400042c1c40c00315948080c2960130039503049040319005000c000c2c2014440000c9408904110341c0e219002c3d29280014405c0d01c1540582c000a13034010021504540b1404c098501400c4415070500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 216674262 1250 216673012 216673033
    0x140d1b0303230a09153605030307090f05040605060f1602060409060e130201050702090702120307051903090b06060912030a02010b150403050d0f020a14061e0c030403140c 75
    0x200a421482c4c010313106410280c4040f81c00301c0041c881c01e039128401c3e0665100c2103100380601007444045260b200384043d001043d20000960a0000b54880e0603680c80340d0f11034506081129283d00229002240202d103002c4043c006581d400c0305035020015111061556421034400000b80d95400d648000d422007000304000c14a00c00340d810002c2030301c0604240c40480d5031010f409a840e00c90642019001c034104000200260502c070050756404580390040701c2c400c1304103c89055465100303c5030003000820208a02e481ca0b41001e4410ba20342034107141c103004d1280d803500c803503d001a024019038840c03200054070340000d803180e1501300c816404e1041034a0b141d41d03555001a0181442e403002c18401c480e400400300f0a4501101a41c00317898014004110040d010107081d92070036170600c83c8400390b1140b50f10b241d0014031100403071100c6d50741101c007402c003a00f040454003030041c0c02040720360494090003042100b070fa040d45090704c0d44190580b0304044518041585405180304510013410113009042446 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 216675512 1250 216674262 216674281
    0x3080d140f0c0306122e0c0206060a03082109072d09020c10090501020306030705180106120b130b0f03071d04020f0307030303020909060607031d1903140d1b030323 72
    0x11140c1b030300302100384109160001c0c01c0b619640210341c07655200c80c103042c050000c918440c01414280704540c0c24425801d102e50f03030b42001d070a4211030401d220f610444051284440103108100b03802c0144030350480e88000e030b16402c0c1d0600130354095100607985c007040741030034004100440300c0158446802005241103504105010307501c210303680f90291182d8400040d05080201101100f04c0817149105400c0c4d00b009000c0b1451694013107034a04150329107070444261b5842d1a2049115000407800048600a410070301c096049200b409500c603800913081080b01490180000400c4407100c600c0f900c8030f41c2c0302c1c030014081e00d210556003509407040f518040101a0150b004002140742280c07140107544e00c2c50204400352044200040024103800702000000e01700400c911080c1034000c10090340e0b9800c0001c082031010080d882502c140c1007529100c04011002c0c046140c528000c0e26000780311500f611441200c800d40d101000382016a6140360300519522480d455040102d0810344a00030305240717011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 216676762 1250 216675512 216675583
    0x30b1321020f070b030c070b07020709110702010801050103021317030417030c0708030403030e0f0d02130c110715051c0203070e01030c08061003020c0703080d140f0c030612 76
    0x494110f1081820224400014500307417403003070f0500c040007881c007065a542d9514142020b006001913200c3c40304041502d071100e004a400820031000b890ba202c100714000144540b1040e030005052520422442e15600071a1500c0030503203000225110f175422182050324658401d0b584000c20980004040e550702e00804001440e00c48242800c4840203929008225107038852031000074003245a40b0301d01000350078010480ba43c00c120081c0340c01041074207500442d03040f80d60443c20034002c030b54481c403003110944c1241140c01d42000d420000e181d40c501b400401c0206e2400c000d50782e400d001c00400c401c001c45540c04a65842d50b40c0905013552241003483c3d000d0038002d42c00458130301090500310a520041c0c030402200344078400040c05002c2201d807452050b8001d45c4203481c940c000380a441c601001081d403680003001c00d03624000c00000c290308000324103103459030086c04038640c0110f082c09200b03100c0325a405482d040001203403802801c0f0030040d9220714050000041c01c400c02249026000322504140a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 216678012 1250 216676762 216676783
    0x91003060303110304080d0806030a05010f1509050411010e030a0f0c0302270f0601090b0304080405040516050a0509010c0506071e0e01080a020a09081504060c09030b132102 76
    0x210000a540c4004500c2d07105e00503402100440d5001042c4a0b01907031155920070782000d40030b001e0342d91003000341e25981e0950b001100e0002d585038903040080461121107288000030312180ca020080790a1a640e40d807071009500705250304000c0b80da0312202507940c0070310400720125400050308c00c2915462800c400650317258841a032184001990100ca145c4640c03580d680304c3c504100418a03140c2d070b00e0342c94030200b01d000f4101c0b5042084416001c00c404040d00000c2d4021405400059212858201000f040da1001000c46442ca00032070f40c1e000d0026040b1040d10900851420314940761540e400040301c1c481d04a00e80545988281e03814891001e0f0001c4e5500e00c0f150032b411405a120f030001c803042c0d5801c003501414500294160000994082a5034050604050107103403010307819a44403000b500d001342d4502c1110460100340b090000308040d038803c14a62490501f00074520518545032155170100042103002900a10051201004041107100d501c00c90480c480350364084503114001d6860000e0750 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 216679262 1250 216678012 216678017
    0x50a0308130809010c0311010f02030f100f0b2b0212070e0a0b160501061509090c0801090b03070f08010207050c030f030304021e0406031a0f0723091003060303 70
    0x3021600740c0c9400d110038181d0300d402c40320003458908090b00446465449250650410034800c454007100c1c1402c0c05010940c0c6c91600c000340e04c07802e00c0c152050303021801030b2005041300d0108508119a07514221940100c6114412094841d450818010454184030040c07645105c02c0600b002070400c031607400380c40c0c040044680b0328460794440c1400c0c0c5540840e040d503241c0c0280d28075410811541200300600d1692840000c00540c506103680c1c0314203440035a0801e000c0040d00d840001101c2e58000b50040041c90441c400740140c500d600070180c036070a0103010350702107151901300300c991540301000360030002c013848100b81c4600b640c1d44621034000d4016620444880c0682180c0050f1890001110400708041001551440c0c9440d400c010207540c42d44a844481c58403002485521f0751644a008000c500840c2031030802e0a580c001280e500c980144030201c091206000d00000541c0555080c2ca180035502d040c40b0001c04103101c00165005000d101c80d40b0403240016400840e44c1078024104982c0f02c0e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 216680512 1250 216679262 216679277
    0x15040216051015090c03020705070e07021221060f0d080301061209120c020a1505130605190f02030d1e0e1c0c031106040309030506060316090f02090d050a03 69
    0x2d00c0009075a414902000306280030b4a040c402880b49601c44c4a401d0210300b00103103000655940d080c1081888c5c1d1018404034103100c100080c058052005264008100550a21317207100001d40c40f10142601d000c405c0907203981030018485848015602c060140010900c0704a06524900300710160300900512000841c1c000060780c541185001d04003443d940217865181c01c4d03600c014110703420210b06c030042c0e82c00b08402e6800079109103404c4100000360900d0303642d00da8a10340801c510380381c105154090030030803104014982ea0350b03626010740083d12005107428950b003069240101d2440c000c0390100d6070014500785c81c0195541c0306d03800091341500c0701d1100f0702421140920294891031400300410040307048030640900700c0d01c10a00000e09502c40e090036070390b030814a4241c03031401d041200c1c1240862900d000604c01e202c020001a60321004c120010000d04140707004c0c40c07400460310b10a00d4445501c409100301407102a40550306442000380495060310f403641086503552000b03d0042c0d0220b14076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 216681762 1250 216680512 216680533
    0x1110615100c05100203100e070e01030b06040e0402090c130608090d0306030c181b030905061605070201080907051005040609060903081209070302060d0213050f0102151504021605 79
    0x160b84401c801940107406043e4604840e0b0540c80a54802000e08a500e2004030001c11140c400340c1c02c42d802000305580b2032201d08a62000502200c0001200380d2040c803051001700096010007483e00c0d071295054580c2e8800d511845410020707409840411049480210030200e0f68039404180d00303104001803c210350b12000c0c4124164110b40b1217000c050401410703003070305000300740040051120183e542440010b41c3c03011403e900645001d40124400000c4d10ba0184406000007081540d030003104030b1201070100b011940010340a807148480081c14000100b000441c0700e10705010310b500800000c1e1400d842c0c05200b01c0010003e40c082d0140700c010420508000c40c01c28490082c1c1c030117480c0e101c5032051801c245062407c91602008004a1031841640004001031310391101821020740345040260711841c081c02003541403440394110b1030090f00e0348001c010030742c0e900103555600d0030f8020019104588503501c8942d950203101c0c2165070030500001d00c801907042e60510aa1800740a5015556441078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 216683012 1250 216681762 216681767
    0x20a080c012c070608131e03110c0a050d03020102070605010f18060b1606020c0a030e0a050f030c0409030c1202060708130c05040e2802030c0102060c070f020111061510 74
    0x1203030303110400b00d80c040b44003446201d0081e00516004a01c011000c400301c3e843c1d9440c1c4071107220b040e0214200100070092801003540005e002e03070900b04028064420260340d51302082c0031480c5442818410303030401c549841450300030f504956010b074105809120303e40c1c440318881c407099440e20443c0f84451142001d0140c00700c0a103d90001d82c2e2281411a15002078407a280c4c10140400b075003910700a44c00c0040101c0b07600100007108059200e0749442c07400c3d485d0281000f00107161a03000034010200c1c4041d041b42e6a8011905a5211004031030000329926203003422105001200c200402a4000c665402101a00001c540380300d04000e685042070342d910100304420944c02040014000d44600f1410301c072510306a0403c104090b541003ca078140f030300002e0650400030004024405094601e082d907000c0d402c09000507406860280000e200b503091041c3d0300c40c0c851240350b0000e031410030380d1f42003a421a0300c5161011906581d0700308441d050306000005105041c40c0842c228412040780324008078050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 216684262 1250 216683012 216683081
    0x5250503090c1003060801020a020105060a0603060608060d05120f0904060504090203060a1a0316050405060d03080c07030e150a0201050f070f031a1005120f040c0b0703020a080c01 79
    0x71a08010b8801000e0001c18400340000b81400d04041c19290078010560f00000d1000d0070302089071b42c0c00441c42d0b0a00809105509070b02d90040340815041c2402440740c0364104e050a50440350030780f90003010381140c0c1000c50074040000020b071281d06000607502461080440a005030310340031902040010340d41d00801c01100e1045000035007580000340000d10b03103131169100301c0142100032030030210480c190000a003454070710306164401036140d9005016034100343c8180c40c0d12440a0ba0003002c6c020f00c58502520000703009108a0803240c0004010341010300c1040311240c01d00317024051a00c080c03414101003440b5005504c00340d00561034100040c0300c00c102c00800900800300b5441c1d40038502000c2c8803c501402c2c420a0b01e0584a84845da1441076480f40300080d5418181c41d6541601c41c0803d02c0002c1c01d0384805001100ea00701c13003100b0720001c42c1a400c10401105c038207100255a816091406a042c009544000351100c1030118010f00503002c19041340940d2945541c0b00c101e0004403a242c0301454 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 216685512 1250 216684262 216684271
    0x50406080603030313120c06051314010c2a0204060e041e0b06061308030a081015020c04090609020409110a06030e06070c0507080105070e011427120105250503 70
    0x2200e80da1080d45c04a4101c91101c5101240707442c00c1058003100343c8400017962002c0d41c201044094032041030003070104030414a0310249404000f0b03c01504c003400c00504d6410b101707100341c0002d541c40c543c0d00f01c28403a0744100e41c40360794007810602107203503100d084021000d012074054405840c40ca001409590b0002e8512100c59405021012580c480906101d040d400030120b504042040e000042031040341000501a802c80d90703500c400d000e240c0400c0c1c0540030005580b1035280090b000c144000041d4010a05c05103810701620002000006402c001c07000d0640e049019400500d005800402d2185007440f030b03840110180ca031400c000b565420100c0443d92841c050000a80029011445c10f41c4918403845001c1c3c040d4040310600c544030114903007103560580390340c00444d1507030031105002d5821101c0003082d4890795a0700c600b05406140c4201c070b107005603043c00811f03420030581c00c80f450740c2d15400c0040e0304116000800a40c5030030700c0403402c0d150342c6c4006240c02a0240c042200400c5c0306904480c8078 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 216686762 1250 216685512 216685531
    0x20d060e190506041514010f02060907181b09030507080307110f1807050315090603030d0c02030f0f040905010b19080606250c0e010b1c020f0a0504060806030303 71
    0x11114820008018100500910752140e00c6100890181c844240858046c01810740802c2102d12140d001402079100c0f80d4003841990050410452000c0010900100300d8000c03210362a400c1c005184461300030010b0089825547c1a0807038032a428039401103201042d28810011100e455803144026907030303805010001081840502c401d0109828020b490185107a0064007640c08480292036180c440c18040341c01c0e400044010003080600c4e020081440d0110001350380016084c14180c01103a03c038443c0311440c607607081c8c864144080d007034401c100f15550505000728098540a007003c0c2e52080c1c0e4401d01c51401d0085c04c000003c9580c040007002c403106406284c00c8445000100d000a85000200610803130f8016024405000500e030001c0d0300c4040102100398500f40c119040ca45012590900d0300b00300780000200d00148604544a0200e40b940d1644210705811a40807041c4000030f841407c030752081c507600104800042076003100141003918440d88030146517650301014140d490000300c44101c0c0c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 216688012 1250 216686762 216686791
    0x1a0102010608390603012907031407020d14010204031103030f0a1d150309010f0504020102030901030b0a03081318090b060f01030b0307180e010b100e030307060e01020d060e 76
    0x300601c48400200b0041d0400d085003408040f01c00003841c540099000c0180302c0b9220000031320405000300d007411012108280207003000031030f0710010300ca1113690313103480380300ca80028520f0709541e244404600318560001c50149104c130071b030360880e01030341243c8003c41d09021120190200c0c2c0c9004001c0d01c40554030010918184401500101da0b1500c21059000201000781d00c40c01030b44e102d00054540750a40b15540c1a0b580c05e010035981e0031034402c8400940c0261030a006d100050b03030b02104807486c24409180c089050003884001400309549a80010035401c0c00245030012800740d0440d050840f9007917140b1104034182c03080018107803004c040b4000d01001d80040028aa890810f8840140e5401807500180408800c00405d2808220f900018004505035480c3c6a18a520b40560100344142e48000c5c001d15041b40b012a0a03c013165945000b800045461512103032410420358000c0e5410520a1105491900340c2038002d5000140c506800c0c0c1c02c0140100b0358121203450785005a030421400324 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 216689262 1250 216688012 216688063
    0xa05030d0b0409020f0103050c0408030703030605010f1b0b09070e040b0405011409252706140f042304120e0d03020303060f130c02101a0117191a0102010608 69
    0x140102230080c800f0803292024080443d505c80104054101039101e0340303000865034281000507110414500b01a1301b04000344108000d40518041c8115003d40d001e8441c05050719401e107058104074203034100341410f0b0f8244040105004e050443c080c001c50094000304030072182c074807502c0700308101140e1030031080e4064011503020404685e1a8601e40300140114542180c48101091214807019030890145129580c6da813060f03d414899a070081c5503004000300c00c05002004120702a02d00c1050520480e0b4606080881c80f1504612110981c40c00049401030324240c0350074084001c045066000154052040b00b01d14140304a8520050b90140c00071070942d6921401c0100204240d901c15403c92030a11240344040d0f124050103084515580140085404880c10743c000c441c42c56481000310f81d10000d929401da41c019400d0392641d0745004540c0e03601d43c1d480300003032514501603288480c49460040702441c62182c0c01c80d01030014100b6802402070a82d60032580341d8a2a06440c045042d03070b031403100700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 216690512 1250 216689262 216689267
    0x180c0b12041b05060c01020706050709080d030e1e0706030f02030f01151e021005060402070f023105011509060f121103010e01050111070e04110609030a05030d0b0409020f01 76
    0x580080b611410751449032030f00c440200d40e10350071030401221071317a40115501040140d1805401d034070a61601d0701d0005a480c1102d4140d0340c80f1004c103442c0c02d25036250342d080c540a0b018085258800410a485203904a00400043c0d6030103561090400107880c052138203000c000740b402141c0c054200740f10304000c0b81e4204821600f01d0442a1001c009029940c900b10f400d40394201a00d09242d42550003074180c0304c41001c1d1000c1944c400800c1d00d44075910400031000090b800c0644c0e5240c0c00e4058903680311450035405880d0610490040b072100c3d41840340c400291016041d04094140c814181d07404520401140040d92009928000c10010032000c540017118540b26004000d400c211b5100c0c040743c2020540140100c5a00a03000700c0782c1c0000500c014481543c0001541750389100c0000200740161400700014008000500010544081c41c0907442e00703550755070140c9011120080503035043e001c10745080d55681c0d03c5142c40f0500c950400c40c40c01c00500d0980720340c000d000c0d00a40740380000d040c0203004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 216691762 1250 216690512 216690533
    0x6010909080f090102030702030f01050a0e0601050604261203190203040c0b090f0a0e0103120c0c0e040624030201030f09110d060e070e07090f0501051801030609180c0b1204 76
    0x1c44e04503c014010840940d40811030007078002d0001c0c00003e80b6080c980c00000542d44450000d0344181e00c910010007850310768a044808440080c041c8440c0740101c0308041a03413004001681030f55100381c80b0b8071039004901c20003d41c09142e01c90030ba0020294008543c1b02079010807540606510340142e0b08110507092040140811031005120400c18080741d0001410081c8030341108840b03a10060051007040032218a404964555003007070303d105c080765600c00e02c480c0032a00032809074000840100b810003000d50824001c401c0b460030542155440900782e038004807114030040c1c0c006802c0403484034800d0f09520450250030b8020803520b405405400500c44c0032003242604880141e583c01422201d841306002c894068008983c0440d0242810400241404200e42088000400003a41017106a8018003203600045000c10080b030464852001a0010010750f4007003104242843d049007400c03504641d0150096101d140c059610f55183d032070822050060703203949803170849060041000300e00010031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 216693012 1250 216691762 216691777
    0x305040501110f13080312071b080706020c120c030702010309020a0905101401090e0708040512180102010615080c0d09060908270a0603020a0201020f07030c020306010909080f 77
    0x4181d1a0482c020032485500c000c07480c80c420302021400305054981d5801001c001c100c180011800c2403c214030019140201811850601210091840d003112424001005894014080640341e150905019020790700001103a8000d0180b040034840401507101a1075000c42904011402e1541950054009009002c02640c2c000d244642c0060f1948103030003414412480b1044516441c2d04c0d10f00d0040c909600524404e050002190091020241c0c00041603800300d03261504800903151824068148001c42060703440c02d0720002140c0c140180d07950000d07031500f00207a00030400c0c541c0c1c81d840c419100b92844407a9001541d6100807aa69645060103005840c407011b400140100280d500c280c12034824403003c0b545c400004c103501c540e0901101c402c1c03d12000c0060184041c203000000104451410300a0005040d400f183c4045158404d505562050114581940d9201124200a404001100401c80c4207104210005c42c00c0c0340c45000320343c80b4660150344141002c01140302d01e11240c03c200b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 216694262 1250 216693012 216693023
    0x141c030e0f030319021e04030b0f010b0702011437020609060a0914030412110f01020a03031109091503060711120a0509040c0c14070b07060b03011401030606140108090d030504 77
    0x8006d05440034850b518202640d070441056a986203107280400a01000500e41d09820802e10010042e025288085030007199091900791401000358a429400340561910700864110320800c08038035141310f60a00480440c0c40042c0b10700720a61500c200c0e52520f0849032401250442c10200d0203401c900e800480521b441031043d6030250310015841851500301c0d03882a608013440108207414802d589000c00c683d120f098403a01220088400040e680d2030001d54000e081564614200381d244c0400c0050b070340454001440c50507d81841410420f41c450805d14080c420b0107040f0100f48100c0c00b070324a411346032501d074000e0040d0345200a000c400d5600410070314000d0107010030041f0120f64480c410040042c00700d0700c1d901d0306040d540c1881e24080000b600c0b0000749034085902400f08220002c151107066038440d5010541446a002103405000c4896041410010240001c01001b0a40d0400f10030383d40e0380350384140b0011a0100450303015105907282c0106420401d5003030311091203500010b61040c00b51 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 216695512 1250 216694262 216694267
    0x6070f170304060f0f0903020d2f03030a0f20160c150e0a06140f0d05010305060a24050d140607020c0a05030105071b141c030e0f03031902 61
    0x18000280c659000315401c84126075120200c40008a90f44100050304404030410000c2c94050f560107513803044104030001c14001011769020410f20070010540401c408080031180f10b242901115541c0c5c0c01c00c2d104e04049a0401614880c803500030f2145003500f004090004a07a420280b882d14101e911002110640f940040c080c0800320305002e46000040841440c0c50503c5021140c0051400341000d8085201350140202089000c0d413221441c420301050480041da1520225140c011a1044d0750b0035005041c1410000000e100010403c68400c1c038001100707000c0c8820411080345010300107484503000301581c400c10702980c102010103100d10f600c0b80c00d001c044070345034402007072412004444040050b40004036025640c2408010781e00104000c3d4001d02c2542003a0001401c10150040106490004010500140003000c55034500f00c0b481501a503069840e000400d0301050140141040402d00705840044010b400049142c0450142c802840c21512080301116400e041014040c02280d000e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 216696762 1250 216695512 216695543
    0xf0a0e09100302030d110c01050a110a03020a02090f04030504060503090a061d240606220f091b0807051602090a0203180a1703060607080c0105042006070f 68
    0x9040036103000301121005650224a1441091301d4071418040401c10818401a46e1500e60000214072401d03240900f01251256540341084901210b07009200e00144905c4880ca007d258021901240c16402940ca0030050707a901034001101a10540d0020002201000301b008418841c0016640006072281a1403421a15490715410341d034005c0d9624120b60f44482000c01100001c100e07100143c52600840e40031104a002290614003000380720078010607002880031030400c1c4400c00c403d4000706060310f02d00f80981790001044140c0590150180f0903180640c00d00100b13001040802250307502e65608000d036540c00404442907004181c1d07010202e01802a003900507526460824800c1e0180000181c0303034500144041000583c46041006940100100202241d590325072104813400c50050340e545c90f00c81c4404504203216020000e0b04d80000800e0240106806400c818003031800340000441a4050210348a181007002c080c141e4891000c00c584070000d007014110f004114090344802c01070246 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 216698012 1250 216696762 216696769
    0xa03030503041b1206060e10051c021f020a03120b0d060902130905060f01050a150503150603010b07050f010c05180f0907020616020a0b0a020313060606051e0f0f0a0e 73
    0x1042e03c046941a803030b0700c007d015080300601c0701548982e1501188800d0b43c500070104030030002d600800900814110002d00a5481c1d0014207400b811000c8040c45100c00d544500944480c81c2150440008242192608804541d80a20808420014501c2c09807004c1952000020400018102c1c1c10400502401104d03400600c50b149070709001314040c0046103080050b00b21344510513000640320f00790500c014400b109544110000040c600d0034941d64944400303105d14012090745050b56449000000003042c040d00141c0500b4085100d1004c4981103002c07800064213981548481600080d4140300600d03000040600030304c0000c00c09014900c1242c0000081449203030121401009a880281400ba0803444e0080317600a80f07070503202502840b402c0780c1d0b40700310540000d0030514031580c010010403140d40c4120380c004d00c1c2036070210040005541e130750400b07851a000405402e18801c1340044505410030b1120444045042c403c0d84d0920f001590410544240c00000c000010001d114604103050344 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 216699262 1250 216698012 216698039
    0x30106020a1e0b0c0904110a031e0509031b010204050312090306071106130c0e0103060b0a060302030c031303021603031107060801051804080409090c231008070509090c180a03030503041b 82
    0x40781d031360042861101c0d1926584424400b1010482b198a003004100b0031460103c20765981c4071418480700c550426440381540039004540240ea894003c2610002e10302282c4401070a80401c198147e03001981d90f840c059400304c00b00c00344c82130b440d0481800030740c103003424404540906d88102c402c500055266100c403044418241c00485105607140044402844c1c95030b0707540000e1405184c10b52440c41e002003111014040900620041e0841c1d107200340405000f4000d400d02804428050400143e40c1e0600400601900502d45000d0182da1804500c2902c1003480906944010b0502e403244403905a00c0d02030800014406c2d00c00c0350b4240000714041c2d2807070081a80060189070030314040c604080c6100c10b0601c207600d03805a010944030160b405a212048030544405503401c010915698580d800d540070f1180000b1281d00c088110108401601803802808901503c50f00d096201c1800701c0c14403900d9103040c000603020940500c00100014031201101c144400c40e10984000325039034032040c010b0701 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 216700512 1250 216699262 216699277
    0xe01030c270b030a0213120f26070b06041a0108040209180304170705040c120504151404050f0304080703080c16030f051006051005090f06030106020a1e0b0c090411 72
    0x3c580015111121040035034205024149090847d5121030300e640e59100985075088000b0318a2000c0881032140e004000740f4084000003000032559102a149490105000c00301ca81e584124503114821a0002d0101541b010800040e1940a05074589400308494010000c05508118a22400307408520700c090000c0d0000700500c4031030181060440d040c141c18170401d41c0200d4040c51070325103034802c0180e00811918100441d0350000401c0d449a003002c00034160798102401c0b10303a0800e0b4483c420328102c0804140b0660103101600d1084145540c0c1c2910b92144e842040040d910144003031001c14031800c014861050f0003411100020f600141071032460086504c1035544180101011040c001c1c24000c0340540d56504000308121410180020344000242d500c0004000011906589544900c106004004001401c082d00c030369541c40000d540387d200d14030844900d0769205056018454619224604039808480184c440c0d4a10203205100d40041c0d184075403068407204013540341c150705030040040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 216701762 1250 216700512 216700531
    0x150e062b12050403291801240e0610020619060323010e0c03100c02070302040f1d01050907030f0201021c020d11070b0a031107051c0e01030c270b03 65
    0xf0780e443c504041152641d050300b040000c80d0314410995020309038081c45a070000c00d00051400380b5001c01c1506005210303910200200c688a100c4000c02c0403003108000d41101c0a400856280d03690741414046840d001000000140c0d0008000c903150450140c40c201d0f40140072400090f030187ea986a460161401c220800d01d000885079501c0d034081002e000c0c07007080c1c0390700384018413204411002095547c160050440d10442c2c2d0f903c401c0c04854400c3c00394000854004000303002c82c0300f10007890390081c40810018501c0d003d501e10051070b2000107000300d500ca40400c0c00039200c0145151146003c07400e0038401207045000300311000c0e1806a103010820303903a42c00c80c0e000b481c034406041d40140c0082244c3d42d46139240da004100030421400040c0480f07100880c00d01e404640b00030000d1403032220380101c2800074814011030402c02186e694100001081071400d41d508007900403414010340403215031289840002c0e0340e408410950064003010608040b003000c42030710749280d64480c42201074106039051140d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 216703012 1250 216701762 216701767
    0x31b080f0703030b040e060a020a020709060815010e1005040510030203060a050907060903080d020d1d1c0302073908160801150e0a020403020a0603150e062b1205 71
    0x34140d2500c00c013004814265000c02078044028411a9103200050114000310b80009240d98114400d024000091007401802e02105450f04002e580300c0e64819550660301c2ca030400001742451022280314010018000403425081c10042804003070f000c010640424440803a000000503107003001098807402460350002041e0502144187c100380d40c03540b180d0704203d0b0741c0c0300c24004070b01c3c00000c60303440c07640d144001039407866441c01050103440302080c0d00241103403a5500380302c00300000c5100041c04c0901c00b1031711141142880c00343e08034060084041d22032500307005000302040340095103030b001c0400d20821981125101808085108041c0c114030041e4103c0642e5051608144041c0c901400200b002403101078810806860a842188640b40307403080d006001c20900e01031941190007031500605580ba48940b00d00b4003a000e0940e41c0003240d1005010380000500c03080301034040d80951402040c0c404008000300783c2c0f21138081ccd0b61a07416420b07001c008584001a10002182c640b03a0041d84690740c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 216704262 1250 216703012 216703027
    0x109060e0a150c0b091b09220b0a0c0302070f03050a02120301090b1203190807050c0102070b010810060501091e0b18130c080417120702060612010e0a031b080f 70
    0x24090180031749103a00c254846c0102944251b103c05035444514010b88003001d190f81c0c0d0030001040340c4d40000a4002498140c52101d041c4100140114840c1140020a01c51801040400c8007244112000680303030f50b0b000b48802000034807910092410b11100d01c100c0302074164110340c280b0103900c01e9025003201980c4910b048d0340d5007070988407140d0001100c0c0c0554140004500600b0440304101c2901d020888104001003400c3d0252003540c0c0b0400408000b15102c5c0c000e8500b28154542c00c6c0100d0311203104c2c204108400001c94040c09040d10030607994070708428600983d4551441d0302e1101407100c0800403402246e00c0c00c41c1c0014007003050b10b07080400c0300413040006020105140407a9001c40030306140280003c0b81d080f00003a90441d03403008800e009040124040541800350000d1b50100c01c148200748019a40e000542600a820480300000c9025080e00c4035801c0719070075114411a5000f01070824042409550541601100040d02035a00000f0b40d940245d42d07409521052600440400d001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 216705512 1250 216704262 216704273
    0xd0e0f010e060c041a040e09070e0f06010212090303040902070f03171b0904090b0709030b0c072105040b0304031d060336190b07030204050109060e0a150c 68
    0x601d062600001d06810304054450389024426401461030725001841c1e40280301440c0130480d0010303d080d081600c07650420b0344149881da01103100c1d414201203c0b0307000c01c0c0c0c0e442c00301c0c498a0181205800401c4041045a01842d040d0840d00f1074039410b00084c030001036840114001821800c0c49401400564075143c94040d11040043c41070704514500c400401c59202c001048a03c1d04c04050401c0c00d0711450307400c001402406210f0fa0083c0300341072000c284401e190300304011800f07491042c180540103030744011100415020741e00c4058444e9600c80c40c01d40c000500a030250002448078505989030a031583d520504a5000b134600f140010040343c8444190754401803035610a050844a0301e14504000c0c043c1c11000740e030a03650590340f0090301444101307c1060080807100741d40c0d200c15150440c07c210012030440b560350f082555003020060001d5a054480d10866080c0c4605840d604800f0381041c0342210510040b02c0302981180751618045607100f81850411004245540c50181040c101c1c40c24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 216706762 1250 216705512 216705521
    0x20c010e0703030c0b0a020913020306090c16030e150309031b0a020a15120c050405091303090b0703170a0209040c03050606271e0915240d0e0f01 64
    0xe540198100e21414400030741d0024100c0741c003541084015500da16481100070007803151680c49030340034544410307004502c24503402541c031584040350301900941d10080d010000303100d00e85410708052040340c1c1200000e8001c030003100e64010302403c910301200403180d2820007544240d8404c40903600104e810312542c2c00300418401262080d0b806003001d0100f83d800f2032032450306070048081ca82042004d1f102d00c1131240003424000c40389108244030514aa1101400542c0280581d9016003910000956a165014640c42e030300c1d41d00d6600e0114881c94000c00118139082140d00701c4c1000f01c1056400d10100720340780d40b2809002c9804005a03208a110200021648200c0510090604107001c1100030380d6494103aa5000707560310b08803109411450641103031700075001c02c0b0b0b07503018000c1c01c0940c0403149104401c0b42481e4007512130112680328104909520045803007259030000e4110302205d241210300e5450801154210030f00ca0420b050b80c6460420340360b040c180004c569015110b0501e052909004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 216708012 1250 216706762 216706781
    0x3170405120705010804150b0a0e06210d0503040203030f04030303050640020903060903040501030b061603030902010302120f0405010609151203050720040b041a0d0507050a0801020c01 81
    0x618102e490700001038100840100081c1120b204a4001504600c0c50340181c1890b02e0002c00c40d80c3c401c3d40300c0e40e009141c81030235542c043c02100b04c20401902600c04000140000411800408100000b000225415800104202d805001c1408070b21360b421030110180c00554400e48001c241440c1280078826042248a24048844041d042100300d05040c42d0401500d091025061070b0b01c5a1020003800c060b1181c80a000e0f0184a03413001c000c008071022024000b914001d980034416031008504100260058903d056154540c000555000038042c1e40b206002d94410b04001d800c22043c0500c020b00c052084840c805020002e404000c100002071003144080c00c8060410420040714604c0e410b240d034183c0c0a42c6102c0c4400f400d403182890f0003501a5001c466004142c84080200241c1d480c05503800185801d0145040501c041000c0c0b80a0107208076952004100c400c8071000603081110401c001801075400b03004040c004102c41d1a0448501c001d01751100000d60384510904405085401088 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 216709262 1250 216708012 216708049
    0xc0309060c161b05030f0708010b0d05070603051b0c1c050301080a0201120908030907030606060201060b090f0d0803130506060a0e13051c0f021915021303170405 71
    0x480010b11102c0d150380e50018052100e00d0100c0045034024907081d0032442e0715215039a108084603800103540c0c000c1c1c8000c107009000301d440e030341c044c401c0b00d55415200410035040100c09101c850711a43c4041d40c021000a22803004803010702251070f1aa020b00c081035942e030000307400800f0fa100280510408c1040c14074000345598076141071552100780c5004001d040192170f0700703205940c161030f403c584030322074010003401e41d2401c02c0c00c4456900d44d841e02c81100d1060400d900055150b00600c00c100880702c0d03100b001440c0445807010003242603051903d6507400104082c1100200e00110040d610030b4281c0c403241c051440c0c3c20304050f49003980c01054280300304010741d0140708000c1280685a0032440c00c5000b001c2d11820f524221381032000800020350581000085440034582c440c3c0e1990141e00b05400f0340c0c10350b4142003014510043c822201030200c40458070f0021006405a0003440c000b40541d0440300d52503103e80e203071003407400c4400c1182c1c1307442404a802e000c246000020210b00151a4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 216710512 1250 216709262 216709267
    0xf030f08060118050d020d0b011d09011b080901090b040305030a06080726032710030e06070e0303070203012405010804030e0f040b0d06050106020f0706050f030615030c0309060c 78
    0xb1094012003e9007405598003810203440588110b44401c045080f807254021007080c0710b980c542e84a10903408400d41207a42d00a814400300b141c0302c8046c86810f10004034041c40c0d1240740100d010030381c0e1074030b00906030000b55980c4401e0400802c1d40120000c0c040d510940d9415a00c0c140a2111402e85081d42c100c07500c19005103e0030030844038808010110b18103502d221038900c45002103140e095008402c130b2081c4c1c20b4840c14030030b4011016500406030490307085074501d010301101d410807021100b04901e114043d5000601048099004085004c40b444004080fa49455280d5003c28250b40c2e4114140203048424440145001c44008424014000a203070264692400f91801886040c03014071060051008401031601034445411841c01000c01420100300c0705590f10f4440d00a180034030580c8018000c014084020381c0012a146003210b10644d110b60030000900700207211a44080d0540381c0c0643c140d00e103c7c042c602d110000d14407505903d203009449181100c0c2060a14070028204580074004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 216711762 1250 216710512 216710537
    0x20c0103111204080c070902040e0f0112110316060914030d02030d150909080c010c02010b060a140d1509060506130909060b04110901020f0c18070201090f030f080601 73
    0x14409460b003442400c0c481280301e8445040100716441950541c3c012401154004101018150003c10444a0001d0b42c5101070b0344480250f04000401e00900c07032080d1010b40598049419030245030a621002010b59220000030301085010340d15961014000c600364101c1040b11200503521039161550540140c42d1811000c20020744901c0b5003e00008a82e9458004c0c00c1483c0e001c0c0d101002030940ca03c810440e4001e24142a101d07904407421356425503082000e0b1514152041c0200211140050005403c0050100098a001c1d070300000041e0000c0041c00440440a1203000f213400c0e070500351f00601051400c0c05107842c00c1d02d115800013070040501700070b90402c58030070b124001c1c00c8503078652000032049514600352001d40007400042c0d91250500c0720400700b00f08460000c1c60400c03403d8084800100d1014852170301d6076040205107030701c0f0100d0740400302d40c1c0c080140740c40da1041c040d00c00042d0300c0d00d55554000e071304002000c007500091b01092408603c0b5420840c83e0b078208200b4241300508510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 216713012 1250 216711762 216711791
    0x100c020c360907030519141501120219150906030b0108070309060905060c03062704080a020a0b0c1c09020a15050d0617010b1e040b06090d0303050601020c0103 70
    0x46448101c040c0520401c00202155028091080a154024151407a240c401c2410540354884c0010903950002d03803061180500c10000b542036101100c070041820300b40c0c40c0101001c0b1405440c00d040c0e0b04a1498190402a8520050000043c0040340d02c1c800c00c0254030b9400904900d46900618140f52410030815aaa0780015007598030000a00d00850300f55072030310349407000d418140b40c01000c0b8071034101444640b860900185210300320944055620303042284200002110680c2c0780c40c100384800d4040750104440c0401004140110700444625100039650508107910807500182c400724003242d8031a84000005118100c0302141405008403009170700000d096041900c10300301100d00c8015101248c80c000e6040e140d4002400700100312043c0c0d6205d0742d01400c803400c0d910700f03055464152101510701c0c050b400c450000d0414011542c0070300643c014040100420400142d102c03030144211050b65540c10902d5555034403d0f6004541810700c600003901d0400c0a038251030500d41030080f00c5030380d50fa = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 216714262 1250 216713012 216713089
    0x106060311071a180d0f0f03020403080304020402031f080307020f0916120b120309100311250609060b0315010b0a08060a050409030804050709051302010f02100c020c 73
    0x1c000c11120609038039103440c04c000d040b00349600c140060040081c2c403601a9081603400d51030101039158182d0302d202d0712130304078220312682c00010304a110502c081409401d181c1e006c0d560102c0080c143d92002041e4202ca4040044240e0200e00c07140e0000484204604210346641002c0380c0c2561111002d05000e40d402d24001c6058070305404100d0050941815140d003500105c40031400505040f0b4465a48130b4019241c1d4091040035000301c803d200c10150141c8284580e420503001d0341a62400c0c07101d403005200c032115500380b08415000e09031130f840000c40e18034450b1100403846410005901054042410f050110040e040301c40001407000411076107000034201c40700300d00070780303030818260751803000080000f481038110a8005141590b00340400d50800071040c000d41c090402c881c2081d60311a1210184c0340d0807101c200906070003100303110040d4020030411a00c02c8a600680e914a802103246800326114100f43c640181d010051481c02c2e030070700c18001c240c50f8951710002003801400024507000350 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 216715512 1250 216714262 216714293
    0x1403070c020f0406150908011d06060d06060807090f0f060e070e0d0f0f0b090f030a0503040213092607110d031404140906011d0112090c08010606031107 67
    0x282d4414441d80d500e40e40d5a03201c0b00191802803c1c082c80350396085401055410a405074887c2076282824184208010300614003103030464800070000340c0d50340d0303040c4200564080d104880c4182c43e1440814690000c2c031500d4064289403200041c480102c0300c202c0d081e5030800305078241440c03411406000405002d030000e68840342e141040315010003c2030200d145141d0701035000c0c00306624506404200a5645901d2103c54001c0205086503154a01d244c0d840d40a403180c42c450503032040041040e910b016002640d40640000c110701c11080488001805507111001c2c01c9911013480845884050355940610100489c0100e1460400509070f9841c0b031040c0105e04035522440004e6201c1c81010700c1414034500c841846540c0395190303a61009103200b08081c0000780c0380b088880d40000340c42d5522508203001d6140000c0001c0d5060350030400152001c01c03030720781601c1c1e207107444e4a1030030040b864010200d002080c01e00b000042e81450710800401300c544004d01001038100401c041c0001c5000c440c400b0001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 216716762 1250 216715512 216715519
    0x2150a053001060e0a050901080d020106060f0504030b0a0b03031c15290708070309140d240f0911100302090306070305071704060506010f05040b0f13050a0806071403070c02 76
    0x100300d640f500161205c8a20361040c0c0d07200041c04000b03d8131000200303450090038550b400a1005e9600d40106450f0341140c81c1003000024070612081000c40c0201e000140c0002072000000745400e840000b190441c0d00ca066940c21a10f01000034030b52011445c81502c95070500c0f09020541d4508014108807814940030141a0301c0c8450300080d500300c13007100204c8003055800400681d84500600d000341c0754010500c03a24001a44403400308009042460000403416403001d03c80c1c485845010026a05100030810155030343d5540800940d00003030b5204501c900c5000d00850051000e144080046600c0d08110712410180140308403011620009001d03034002e046030501183c15a28408111946207044d00c1d80c0c2061000d0360203200078028a0340c0701c58050042a80d4500201904a0082d115803080c3c0c40340c011510010000a0900000390028002c2600c20100c00f40c1d80e03030b03611400901000c0d45500210401d80020050010190708680003809a00700500c2042c00c1d8584150b02400700410302d01c02031301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 216718012 1250 216716762 216716777
    0xe010824010c1e2301020906090118080f0703051903050f2209050a050609090705010e0a0306020a050405100e01020c09070c0f0303051e04020d0f02150a05300106 71
    0x700320843c10003001c0c0e00d99180800c046440c0506100014943c801c500750112130900e81e28003070701c29060003182c0c5808009440c41e031401c080c8100448149071304098004912540071008503180c031092000c0c1c86527070360f80f400410701141181400d0f4100900b40144c2c610090915005900280c6c015080d111400b950001035605d40300aa160941c1c88120b04459441c0440a00d00c0443c95100f00e0340003900928040ea8100f00599070041071283c040415546c0b06000ea010300010421580304100c0c0c1a00424054409404940d03a9503504c010ba800c0606130201060000c101400326040516a011150649141c0440c5105036240042c0d1101c0030f451a583c0030b1018000044c06c070300d001d07000c256105940400d50000344800c0741002402844241e843d200140000d0007205642c0b03060184441c0995002848a41d60f80c071300d42d036a503026103503104080340c0121418001011401c5154040d000140860b1940360b510f003007090061081c5180c00c5034907518442c5503510300c9904038031000100d054404a00b003404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 216719262 1250 216718012 216718037
    0x12090b0c0a14030106020114090303040c030204150512030703180e01060e01030605030f0d030b06090603010e09120a020106030314070809090910060b090a0e0717070512070e01082401 80
    0xd40580c002d4000d0300b95200000000904207905510121400c149600c050380c45031035800031070351644410740d4062720a0b14040d20600c05450640d028803540031154103000300b05543c40000c603c0c0c00198440800035608082203070380030305400c8041b60101d4000068110340c81410240008080038041c0200000c00914044090041e4041d5204070302504009007240d116158280009503245810600080000d00340b90b0f0752606030503c0c80a8446400c0700a02075410340e0b003864401048551b00400820541c03003050103951780c4405000040c0120822640007289090460078082e1251031744200c803100c404070420014000c29166000e4542e880812a51040301c1e88800014a2420311705490512106142c003500245c800d82801c01015110b5007075a611300c030503699080e08408014121100c0011130003c80c50b0b180751880c5204070541c03103065410070605001070810030700a40d100403505c0d1004907807044203507400ea43c1c010141d198000b084a0940c130700d4079212240c001c0d03405030031103c2c141808100c230b8107903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 216720512 1250 216719262 216719267
    0xc0201030b06030a0207150506011704050102040e0103080a09080a110d03090b0f0a03050907050306011a0d11030114040902031e030403080f030415060812091801090b0112090b0c0a 79
    0x91201400240b95907241d00701365007a04000c3d402440200e4602d01340e044c07507c0281c07009000e614030803170f8140c4505d54060800c04011508400040046401d95400c000103d00200412001030103503004c0d05140e0703110303035514101500d9141c1e590050421640006012000241074000c0401c0c000400e41d480002000c840c9410b41c0c50500307941117040101d00c04501c518030000e50070701500800340da40d5406e111640f2980710b89600e5800783e0203200d403d600008014050200020440161030040481183c07414113041c1c003c40444000200995440100000402062000304d51400d50076108583c100300016107680000e58440d80c08041d03070b28110365201e4103082d5050a0080d10011508025280d950388482080172007030741e00495046605000c0d0090700f005050541c4220320503512201c0c010309100c0382c045405021904085900c980c41050000385144d05d2681c5805a07008250342d40000c12281c054500242051707041c5415a800c052a1081100c0890604060942c0003c144000103030b680130041801c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 216721762 1250 216720512 216720521
    0xf0216050d02012001150f03020310111306090306141e090109290c072f03100b120c010203030a09020406051c0b10060816050c010c0c150b0108070c020103 68
    0x1382092461100e1301c040c0c030039106401540c0b220400c00d1101c1c040b5900c0c0d0050b1201c04c00b9078000a50545d000003840620005281d0118628070b01080b0080e043c200c5400030004500400e41001d0005010720320b0030410400c285c0500c2c2c206050a05880c9400d00d4000c07000d820300301500040e5880c1e01c60407408541d522031b0a5000300b40c02c5403c403020041340d05010340c21680d00820340e0340e428a04c00000c0006198094901c00382c9003a01d80c071034070704080503941214981194040010420504d10128811f4507955801c004120000e58880408140708071000c08001e416000c840046c0d006410444820190741c4e0b010049a82c440020340002070b12100b00c1c004200201a00e42210b42c2080d802465140303007010b4481d540c00000d1013000012590346d0b9284007800e003c8042d00c41e41c0c001c92440c00201d461050301ca042c00307000000321b151560401c02d0f00d92100d8251410b210f0110041506552140180447c8031000908410301e85401c0c0010107007000000d00541004109804001c80041101c1c11a0b100303412 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 216723012 1250 216721762 216721787
    0x4020f15090a0e10080c03070614131e06050412030804080d110301080606030316020f150318010b030118031b0c0e0a0e0c010801060c03020c0303030103120f0216050d0201 75
    0x2e24a456124102284150b80c15a40303508901c4c1801d800017100c101c0002d0100841c0e0003d0040e24080b0300e041c40c19100103100d00e00d514842c2c04140500d005c0f610f41c0f810084010040d078649205ca45d2524200d074280b11070603403c248200b2200708424003141500740185540316915203400300a9507120305020385c40307010b6148000d003040e0621401e891b0942c0c0d6100554182c4910001755052500c0c0d075401c1650700c2c49980c191001d80c0303400309503141c05441c2c0f842c4415113032140501540d140a00099101e107807030f07008403020a041e00c200b40516403400d03c240300e1144190300540003001313100c020358000c5044454101c001020411441b12200341001c40140141046502c02200e0007200d41350007601c00c0e104000c40300071700e41c94608000024136060024461000a02c1a10381c5e20306130342402c004484454045006400f544100d40080526850400040d4001c1d80515450340c664210340b40e0080c182d035003044082d000c42d80401ca2005d0002480c140c080d04030762040715007021100342440103807464a003010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 216724262 1250 216723012 216723019
    0x31a280306020c07030308010611060a020904020c010f061d040c050607020d05010501032904021f0215090303040201110f070b09130c09031707050c041802090702030705060f04020f1509 81
    0x3d0024a0302000060ba00f003035911070f449485150780c880c0310441d05004401503918103548900c010850921441d401040c0950011b08098600b40000a4a5007500c8040040ca015030f50740310010028582e01070030310034a00402c4001000f141c1819194000c588049000307443c8100c50000742e400855442d009050030b0300d54440c00a01c00c569490804500e07010811070f02c5000507060340d800030071824400310903178032407580284941d940320f038010f0081190741c04100c014000d5110700e10141e01d12500904c5d12500c035100c09801960f0702d1500b0320005051080b103c150b840c0710350200c4c20032400c6500105815040d40d11100c40e19071038a1140002a8059548000ca800c9652400009a80ac01c0c3d20205810981e402030b0b44080c2000c45075800e0401c0e51090840c081c0c400d030414010010286010f81042d80080c1017107810903415030840d0002104090161040707405640000340080070001c1c2881003550121041c08417001300c0c506a000304903444202d03608103220b4820704142c0e8050040f004c040c5e49141c3c5015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 216725512 1250 216724262 216724267
    0x31b0a0b04060507030612080a1202040512010608010e0c0a06140f04080609010b0303031e060a05041d2b051b06150f030313031b0302060a030606031a28030602 70
    0x2d080c20401004184d070104002420841e02203042d030010359101d05030f0341e40040b50506d445041c80c01280c10102122a0104480e0200000101070303035101059081d401d04e2400010342c15181c01181400c50300d091340940b64503041254130784a00e5654029001c1100c08500740240c1141070500050002e1090310040101a800070070089400c4200040461041914000030030030a40e80d1001c140c1c3d61302003190342040c480c081d224011b00d21a04c1065180d0405800f820144a0075254000035090b0b481178440b032080c1e024000c0241c50750120400030032f521508141c9824a0315003100c24586003070304d11440c2c0142400760000f5203814010301daa01d84a58103203002c082d14074030304000381540d0751155003001c1c95105000080c1d03120010b14000c801c5811580c1070003140350703010b455580c402260f0006460300c0090040a054000096250040207020910003540e00248850401c20702408640c0d0700b1551000e40220303101640d044d0348901001c00c0001c02c0c000401c1d420104005035002070501b10b40c100921880c0007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 216726618 1106 216725512 216725521
    0x118020702030f07031208010f050607060b0303070203010507051b0102030f15130207080304020a0e0915180a12020705061c0209060f031312020c03031b0a0b 69
    0xc0c0c03d480255018545181c01c00d00164019100d04c2c072920b8141c99016880001d01d8050300700b00070f01c400c130903040c080410101d0045a07002002155181007a189560701007003600d03c0c60350300400921035441d1486000340b40c0d8003c030302c4000018076801505601e589040c002d50740b180610303046103d2241d40b03880d0760002d040c50703000e140d0390003c031114502c49018401d400105499800b42c1812a6241814410700c00308120560001980c0810324091055a940124600c0c44500000c940080c00e07171190303100501da007180100890000c1c0b24003c83d10003003049000c1c150300003035145c2c1c0036034200c0c0d0343c0c40050040f58860240b25018140085d080351000d04006d501500804102034841c60519a17000c0303418540703500584400c400c1c158040c0c200c100b0400001401c0c2485407081c4098440070350407002080d03481c02550f10a171521303c01c4070085240428100084401c0b10781100f0a448603090 = true := by decide +kernel

theorem cover : BRFrame.Cov 216546762 216726618 := by
  have h0 := BRFrame.cov_init 216546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 216546762 ≤ n) (h2 : n < 216726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
