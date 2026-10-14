-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3682
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:22:50.11089+00:00
-- url     : https://prove2.me/submissions/f6a94578-4517-4da0-aed9-d74a0d365db1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 662050359 ≤ n < 662230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 662051609 1250 662050359 662050369
    0x503070303050603340803090d1118040c091a01080109020d060b0406170c0702010806010809121207020c0103060803220e04110111070f05091e0403020102180f 70
    0xa44402000c1c55103400008410391020001804460400040c86000215010781080c503918140242510f080da102800308000c03200004540ca0b090000d4030030f0742039100544481c41408040491f03103a0124217041c0d4400020165402c590289006509010403540b40c06142d0040340c2a0001d02010810786560b00031040c1c0e0407200303003411259411400b682d90b0410b000c21074000c00107134100107080c030004100859000d90000c6c08030740d5480c5558031000e6942b6042c1100c3c0c42800b90b83c0000380020302c01400207400303500c0341c6c1e0804d40100d6410210380c2416410004100036801c880094100314900904001400e42c2c1045041c014140070708042200c9828901c10684904c02c05021903e0309902d551100343d0082c040700c1c140020600c501e42d510150900d4070300f200c4071140070744140f800955040b108c01c551410208103642141e0003401c016880e14074100c103101400500405196020282a01c80003140b1201c161b128803031340c480c1c1c1c00180d80c7c003e46c41410368110b103085411401000d08049841080d225 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 662052859 1250 662051609 662051617
    0x5011e0503100e011803030f060f05030a0f050f0d08040c05060c0c060a09170606010905061206130e011a032802060c03220504060e090a02010f3501050109030503 71
    0x4070328000c90120f82e00d903003079800340a102503107064180307581480c6804e16500d030340310700c104075090a414070119607603040e43c189061180c01050791641010031a007002403080510505c01c540704000b034460503181d0406450a04580322130340340104e10070b4030400c4100000e450490b009800200c40550a0608030486036070303201f9101c00301a01840c40054400350107030103010000b00138103501a901c802140540c9403070b5100c500c25128a0b000c03a0480c03201280e6840c00c502505c3e0384281c8a10010303c41d51700c480412218020204200819540e16454210b400100380200b010391101d91002c05003042000e0145407903c01e00780c0c82c4407591104070201c0450400e100301d41d843c4098049400343d880340c0310700c83d0082c00e620903141483c1203401008a1161145480c1701300781c0807100d0480f400c20920b079413100b150010b1041146d0f00441e035003101c1141d400540c000c0c90310460049503454102c4100120944a4400c060b02400841810000038030f207141c042c55a00c480e6000d44020311b01045d0852035039442c1d0350307a801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 662054109 1250 662052859 662052883
    0x14010501120b1602030c07140405011212051303020a06031a060c07050f120f070315060311130b090702030d3b0312070c050f0d050f0a05091305011e0503 67
    0x70030540f28030502031081064802030b1022a050f6283c1903501e0039031a06000e203055980d80650306000000940d00003016008d020540c1010316800340400c01070013141c681e4010031000c4100c00c04a900071025859004041d0b02400c2140c900003010026004030011154030390310490f111b1001008409003244001c102d110440c3c0c016604001c0320107070980020140810301c01448854811003001a4041000207044000ca0740510094201550504840b01c1644c482d80806880e286c01c2c02c000307504c642000c484204c3c0e0100d81d0540041c1703030225140011076520065402400503400030459608130760583c802c10076000103280200c0c00d00c0c0a855042c03100351710f040f80c3c10401c054550340300403090101441240c50906400c4118030061400c1000540340840195040d9520301c07480e00c0101c0101000585243c014007280c442a080104c032010200c200d81c0511812410880c040c000700480d41c542540c80352b00c00d00320b0b80c0f0200d02917050500640c00c0c0c0c1030a03000d800d010500314804104035203010a500c00001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 662055359 1250 662054109 662054131
    0x13032310020703050d0e070e0c030c0415030b15042d0303031d19032714040612060b09070c11060304020409050316050c01030917131214010501120b 65
    0xb22906003640c4600403064607031030160411080020b24080440d0441c203850520100c0120381d22540c0b02c4100d40d000c03c0740d49501107041000140b15a0901d9035542042090300d150100301504000302060914007008201c10192202280034000c1d80740c800102d01c040d200003100d0304080102e9540d04d1240480d00c1c031015041c586d60b031003681e1001e0400610f00580c3d54110048881e04411080302035035070b4001c14020b900242440980b100801090045c5c009294150460350285905000c01142100c841c204115445551703800000f5140c403401d3b030104001e602a8000240684200061000290004280400300041509124005900000b501030b00001c00c0c6c6582c0c1e100e0350340e403011600510714614041d00b58031010580f19041c041c030240c42515148110f06450a00e50601c00640c142c6000c02802040b079800c10680c00c203002400f03000303010741309041c040701c0c3c0c002581ca200d0b941105154101c240c0c0d00b803c5209042005c80002d008041c014100031401c80e00c004016100e40c014500c0162600f5141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 662056609 1250 662055359 662055367
    0x305150d02061824031b091809101419020403020604060c050a1709010f020d0e0d150213061701030b061012020318060c0c060414030409021303231002 66
    0x10340f110b801840721601d00032500506040c10421380141138004681c078000030240399000c0314448140740140c0320040009016101d00483c9030401101d4070100900201c420312821000110743d9000340146a00903052003226416820081c1003011000c0c91060440071840c01080204016200c0b103080f5005c9901901c0c002d020b140091404504200085d0720290068007885421004004050700510304071000741c0b40d0b12101079000c1c0e42680c5946104101e80c0c042031f5000e07403d68180c04c0c81d200305030368240320314541003c0c1250448508200d0f000194448a04e401d0302c0780074480b00780c000b000d1054480d000c1d140e1518a40c50340da1084180341c002400d26003d40301c64074000010034041c1000d021038040381d0b60155104e290411050340fa108081d212440e1034412040407890403a40c07842103d6001c0c035550084c090580e0303a80c41e030a05070941c410b5502c2281c4801c010004a241513407010304460850700c3c0782c0c0300c0c0ea02d00d10700709101882c04100a250f020768014407440040040040d2943d001c0108440268175 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 662057859 1250 662056609 662056657
    0xf0d080702030c10020904150e011203020307050609030403050f070b090f060d06062a0b070e120607050d051f051504030605090105180a120813080a0305150d0206 71
    0x254003c800a00e04148505254218a910590094464040107403410070100c8092000040380704807504c58007888814440c01481000183c602403500c640c000d0044034503124450340d80034500042141c2e0754444d07400100301402000024441e8140c8011000d000f802c0003420950b0010030f03481010b20031407027000c40d0309030244242c8a0609495007a40d07900c104000b0b95649041c00f500c4000078000308280740c0d10780742034100105904020140300d55002681e403603030350b550b940040c0c0340024bc060400380d200c1c14241e2442c4407c1800c101c02c0744034007040c1d655192039007403118807034082e2180546111100555503880c0d0f00101c85414210080b01c400b1075030800030b0922803402c03805a20075500050000360034402089070307031401500315902400015003504501500742000584400d00c1d218000c0c202ca40701032000b020f0621454070140c20446a400c0e40740891120358944542c1e40c800c3c5081008a91120100300c440500d04036001083c08003500c84980c03002c1d003070740040c000f0f12a10080810f0300c07542c0181602 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 662059109 1250 662057859 662057863
    0x40b0c09040f1503030f211505130e0606040b010203090405192306040216060504020f130b0f0303040602030406030f020705030c15011a0d24091a030f0d080702 70
    0xb00d00031441020080b0960464840d00440864002035010544064540c80c140748156284680c075845075441107265040155000040c101b400c1d040c0c5000c02500c040411280d031140030140440301d1000300015000c000a5200d030609500410b1188110320307000140c105a40c001c0111000d1140403940055903a0314402540316030600034644d44002442d050002c170054210913118144607254680d00703100c41c0d90700810002a40300f90b400b11a039003041e03020031900096441d00881d80261000b405850120003480204940c2741d2200f09142946482d100c852400d41840007450780254400d40c0954501401c141c00650340303100754403a6800b011b607500315410361a00076070b050f90306856215040c0c90380c03100060004e036558a0791030901c000c00145940001030b00907030310881d441c0c40c0074030045903400c025140c00b80000900c80c0c5111184a00c002101010207070040300920380207800807410024803c84c00004104020304140d005034060b9008600c030110707100380050843c100441d28608140310795107015040b4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 662060359 1250 662059109 662059121
    0xc060b15190314072c280b07030e040513030e0d031b14060c0901090302090703090b0c030901060803270d0807050325120f0516120206070503040b0c0904 67
    0x20000086090038030000c19404000454282e9004003a451544500030030046180044650903500990080b105003030642410642c28072950180006d90380c0a42d510400005540b00c40740c11800a1003e000c080894030f0640319003508400081503103140084143d0f030281011034048455489004820b81070b0341094071038807921400c404103001d55100c2d8001e925240188000b9150014080c0c0030340c9000645000d8540261101e1041c142d5540150302e1650b001e010f800c49024211030201902c0d811944080348031861128054052401890354034640291001d0031603449400c20203164204102c0c400070528821200360603081d00d0703007009010a40050016482e85407d00c0000d14003000411240103102c00400580404810382418050803014801e149910342c42c038100003010300380c0004482034518411400e00203069503d0908914045209408803020b190a060496030071000929051a40b0b5040c809150800301c14204039095041c83d90307900c81065401820149040404240503d4039680ca420003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 662061609 1250 662060359 662060381
    0x41d06180405120d3b0f0c01050a0306050904030c03030522080a0318030c1b12260c0a02040f02070515040503120109050718060f03020705010b0406060c060b151903 72
    0x100c04011001c078200c48840c515000f100b690002c44544810003110100381004000006c0e00030304a48007180c001960503030814002c500400d99500700101c1c032920341d103ea041c0610300a0300e9041200035507140040503542d000300f2710741c04a480c1c90510f1f41509809089041241c5c1c1c8442104c3e2950484207040f00200b04e8a0040c0000d840740b030f0342d150705161300580c0d070201e100d020b003070000c0780300629442c481b4220540b440f030f44010440962020002c60017552945c4065400710b801541000c0000c0b1001003c2d4001401d04500c82d0010420142145464420200e4096041400350704102071512015141c0c100c160b4031030203030003000e4005400c000050007107504da4581060501c01c00d50f12640b559004100880b4480081881b800c0c441c12034203d601c6540d0111038907603507900e01c845144442100650007000702141c0540d00c0c0c0e031a00c0d4090b503a900415014000d143d5411040c46000d007020307415251204034003070142014280e06c0420171020300c1160032052000e56840312003102103904030024610f60303982c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 662062859 1250 662061609 662061641
    0xb100c0515040f0b01050d0803130f0b0c0d06050d020f0111070e0f07110c03032b110c071d0f13060501080d120203090d080408041d06180405120d 64
    0x1000104400040000c002e40d0185004e91031580e00d400a0118000e401c9201a112090900005e00345210750784a030b0700d50503c10940d500e02c00100f5910748414001c151501c180000000c100303110550718921610008280c22143c07808a5142c1380c01003640714280050386030402c036001d4000140100108400070040040480441c0d20b4a009206041558000c2d24500c0008109014a030143d0200003407100003004001c01440c6080d0315040001048a030b00f800c102d43e440c031420000c00c2808214410380740e601200098203030b51111555413075800c3ca80b180e04419071240300184005503080e0100b190f0381c0c0c4501582d41050311b80d112940030070691407007083c0c003d0a081c01c100003c1808a004a0001a84182c5407034014280c0045900c407804d81c04121000004c0b907000c1a81c3ea4007652280e0303c603680040c09581500d1425403107080130300303908820340702c141c1d10002d000e0b040c054181400d41a81a02014402500c80d4038103090303440c079460342c640351101010705c800403e10600380d01159001c0b0042c42d502261f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 662064109 1250 662062859 662062861
    0xa0e04170f0f091005090109090506040e0f16060c0507140604210507140315060d0c080d12020403081801030608030c010506040f0b060403060c030204090e030304050d030b100c0515 79
    0x71104000c2d9124401e40c9010f405048404c02c40340d4010410307121010016112002400d0600076441c00170040140281c0d84241c60714115180d2030300502960405814001c003400000b1098400702c122043c4e2a8440c00030000170107464004644081981815102c3e07050701000c40c0d10a81002500901503504001044c06174040c40d440355400c5191804146446503043d6240036540c7d00400a481403101c181540503000400c10385400d04c0f604101c0c66204200030f00c40500c440b119190007601c51016004000194002c0f81040c4200d608114400e4586008036030035460f160465503007103d14040e90510541c010414003400074687e0080d00014007078820742e412030f5100c107003140074240600f1083e40c050380207510b0041c1e030540340103c038001c3d0030b03490502800c0320f8580b074510342c0e8000061650403580c104055003404040b03404002d0740140701c1c0740c200c101c00554072404d20b0b0401c1d40c10b212074104441c05144c40e00381544c0041d200c9602c10b68041107581007070841590300341841c3d0308100d0080c0d95400d2000c1254 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 662065359 1250 662064109 662064127
    0xd050703060509091c02030a171f0e18010510090e0c040c030b1903031b08070c0b071a0601080628060801060f1b020904050f060403120b0a0e04170f 65
    0x1905d850188903d080050410242e9100784d03142c0c41202c4009002422004000070744281c0000040e0b0401d1480030f040c280f05428907601e2212b171500350400301c4503210b03640c240480581d2a0b20034282800d0704100802c4142042903c802041c0b40a01c00c3e0026143c4503200110485c9080c0030a800c0b460010308240300400c44d40d00300600412210b40460300c2008000303200c8a00c407981844070300c1905d0703050b103c03100302051250b1400000d5512140031900c0300410401500014104040d2000400c0d903502c2c0251925035a2420561070b01110b0081c80e600c2184e00b0401045a92214182d40c01401c2030311f80c80701161000245801d415a5501801c45248690718000344084e40505000c1c101e03017007981c1e4207400b00c6040d88212182c07070103085445210340814120001500d407400c2c840e90428841d40c200d032100d8140c1c07101079090010840e016008185003c243e500280a540554640d06404540c84407245081143e03103210b156020f44040e010300d204000640e407540714942294814810501c2040c7c8441040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 662066609 1250 662065359 662065363
    0x50d0203090a080a08030a1107050307030e0a060302030f040605060303070b010f05090606040f140d02091009050603010c050d0507022107290a0b06040b040b0d061502030d05070306050909 82
    0x1206495010705000140003030200e40115980c102c260344400e170700d8910380701c04801201400401341c1103040c00c20f00704003c130b00060b410002000410300c00e440702c8080f410310fa01009025080d40e403000c001d050042040045904004450590080d40000300190640740d410100b45140903819008149030300b108000305a131507200e66140c00b1250219041d285030f644000500004d80034138440c0760640c60b0116014030a054843c42814041e00000e00104007800c020380004450800a0f20ac0481c2c1d5900d486042c80521030078000c0300d0b40000250000c0c482c480580c1001080340c81240080c44001d0b0781c0301d001c00c050038401d220a0004070143c1100b8245001c5000f4200541d03032100c0d804071800d16000c070340b00d00094100f1a880f4500d285a14500000780d548500c444081c0103061551940007408100100d02500710078080c0019154401c1c1c0e01d511540c07003802400c200c602682001040065400c074880c181c03980007084402c03403210030902041d140c54070b1405401a1100703030040ca600c000b1482c1008041c0c500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 662067859 1250 662066609 662066617
    0x911121f05190b0102100b060d020304150b06130303031508010504080301060806100c020d03090902030702240c0307050f0408060103062705030301060c150501080a0203060901060b1213050d0203 85
    0x401c070002c5540358805074030b240071100e071020050b0250b000745290b03100425055104121001d03019000602d0560512001000c990040750116088940604040401d00c064801c0340e1015500307440f03075071414210348200781da604903500c0014200b40d11001c150580d111405010f00040198030024448c5040c07520701420107130802d0164500085207a000285540741480d0001c04049043d128800b01140c02c0c0c00b030003200c40f04050190103010010300006541401403008520501190340034021104503403115180020110724040d00501501090000f407602c000d080700c0d002401410056134890720914a01c40e6409240e000c803c00c1d000d03600c0004148a4650004549519844811101d0711000704440158241c0a040a03240764018030051146500945001c6921402200501c0214240b05556000c0c4c80090308441d56982081e0722072011801d04010302900031031041c00a00c0381c0b074140082e15903203010300700d420001d6120f10340204621441c46c0c200050070700c0e007186c15103400000c107810280d52544 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 662069109 1250 662067859 662067871
    0x50708161518060203070e0a0f080c0402070b13021c030507110306130b07050c0a0f0501150e0c0d140a090b100308030406150b040e010e06040911121f05 67
    0x1102800c0d00700300440074801c2d210710609286045810320310a840d24030007034000800d05400c0c45408080c5400f10755608003a03a0040032085048079195080520f450b050480d24510540280c2c014404100084c100201d06648049400c0071003a82801900000b410001c40c4441030703060340f4403001020140355102d00180036650140700c008814840000506a03511022524030b0500b126020b0b018001401e01c4a003030b03421803803c0c50035500b003644400d07100c0c0c14481c0d6030701f084a8030306600303d44808020080c0505030840108145500d20103180c0b054480313800c80000e000f50402400055100c084040980c00245100452a0000490b241810700d95004000c0d88009440050340706c3c2c00182d51190840d8120b003a80c4d0b100c10982e095032501c1d0764a401518807494603415801c240c1c1c10100d40302e004200944014004000c5045055140c00c036030404045015010501882c14010000b010400c11040b640c0350b000c0a64108000c091422480b80c01d0070030101004015110408200c0e092400c00d80010340104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 662070359 1250 662069109 662069123
    0x2120102191d0d021528050702011e030912020d2a0311070e0c030a050f1b07150609062c220204020f0316020601030b0c090105070816 59
    0x144011400e82d100560900c0d008803411049420b80860f0810111a1070103074400b500c000c0380a50480c064980b0f6400009199007000044201020070008140d1741070103408260501c540780c000c070ba400081001c14008100c040080c0714207501949184207034850300e04140c202603000543d24401100946480311040c0c5200020300c7c10400c10424403a922011500c2100c620340b01020b4401c90f502034400c2040003801c1d007024001c80d40006920300318505028410100c44c403101d9942c0c035161007008112200074050600306040b440403c1001c00a00c407940c2c00d50f4660740c3d202501c4040a15100202007203081080100505180002588000b2a0070a0301a182d0142c001c210040100800d10220640004210303100c82c0c1540200c0d06207211278a42d0050741c11561000d5207400010303000704003603074481c000800c1400000410884110140000203030f80500500c05045a07500d103889041c0981400340507555007000028100036a60300400845980c0ca5020140548400f083c5102c1c1e060800041400c0d1415 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 662071609 1250 662070359 662070397
    0x20906090c0c1c1e08070309080c060f220c0302011d0a0e070207140904080a09080303011e0602011803050318120705060705071208060a181b020a1e030c02120102 71
    0x160552588404c181c481d540c0d0f01c10a60342da0042140034003070703921040d01c4000c0c08201c0350100ca90b00307111051042e04000b4241e145801c01034400c001202c44d1620107071400c08141c08580024585800241c110303502440d29069002c041034081401ca500c02909a90242c40380c074000600941c2410340da48982416000e88014039a1545c1c050845a1001d6500b07a103c03e40350f00040028804101a20f0740000e14070b8142011a229903003607155074000e801c4038810300c404495020204005a072060080c22030b0b44000e006c9a03d641e10385400c030400002d001414090040001140b13024115580d040d848403002c2210660003880c10317850419800701700103942c00e019820010360b4281c05141281d2a07650301c001d03003041d0700c8881c05080b1030a982c080c01d61544030001c8140010b0011105500d10100c0320840d0000441d0314980c00e00407200e007900a251815904009949000f043c8a400c0030282c4030404005c8000245913480c049a140c15080002980580c25010030709089030158007800b80040f1304880c02440e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 662072859 1250 662071609 662071637
    0x4050303070302152d07090806090708011d0316212016030b09010b041a030616120207081e0a0305070813060c0309061a04050a020403020906090c0c1c 66
    0x200c084e15140501748040c4040044142e00079036201039500c41c020703140400002da1070380c4000f41029001d0340c4034a49540043c40c207000d144001c2c860852101032440e04010b04251541ca5151a4060100ca02c041201520040801c0c0500080c40040005424001d003074249912030000c3c184120600e400f2225000c0400c051003408000203030361a210406820b010f80709031440c2d0744c40c600c0a0004243d240c2e02d54030340c3d03500301154a550082d4408020107110320b00c4214030b034005052610f10b00420007844c008007181c0d4107100c00d0f0003418000300035610310400359403881d0b5070030550541d106005201c48035011800d075105901034030030091300350b40c01299018811a101d440c401c80c2c81c0700c07050301c2c0140c1940005030888001003030780c1e00c00c48c00b000c2a42008a6001000d0b1a1441201c4000d280b0b446800d5121845000600e850f100c1c07142d11a01e08041142401d00710303004070b1a00e03100141960302406011000c46c16001f8004141e6031043c3c4181c0440340303007030400e0440c403103120f00030b159204c003181c001901703102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 662074109 1250 662072859 662072881
    0x309070e0903070804031e0507030b07121109150f0a030204031712060111010e1204140108041e0f0f05010b0a060f020c10140409061e0312080a020405030307030215 72
    0xd184d044034103503041504540b40c1280300040081c02e25135100c1264500307400550300303010a500444c0245001b0065141918028040a60450300080058031340400d59a041c1e001c2416121028015600c030242031007001c0b9503144500c1070000c409001c84002c2107003051107a00d60020b1003500d20423906660130141805414401c0d00860054441d0440400c00140c225445940b085800d44007140c0007140030000801d020b130401c0249100110780c00000907042c008181007a2034164100c03000e1134562054038090b1206071006030b1581d40620031081800e0041c2c00e03c40110042004640c105070781840b11803c905d0300b64024000d140016004024401c0001021400307403521070303040c495580203000c13404240d4003007010441c880b00e440e07004e1040c0c0c03402103000030042501910103086001400216a41801c00b46d1000c1022003200200281380300b41c0903c001789005010740803086207410031031141e0300c0741903012010b0b00968001603054807011603904149036000844034400100d42d05a0076031921000c0201d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 662075359 1250 662074109 662074117
    0x3030403050d09060b0d060c26060907300f06050105160203120708090a0f0302030304090203070309120c11010828090503070b0906010906030312020306030f01020309070e0903 77
    0x58081002444000c50b0349055410000c00d5138420200020410804030006560403074040c0155485951402c2c103e40054008244c1d88504c000e41400070201043e20200c01841c100c0100010300071455a800318912074000c4904040712541220440d61044030032650b00c02c81018100e0010344142090081a06030489115400c00e80c3c2d4107944103403404084480c0204400301013007007286c1610071a820a00c08122440240207aa4483c141040d902d0900f282000382205481d0800d40d003034402c0740410001641d00000f1202260807101000d62071303a03100e490030b038028002c0304806800d01044840d1241c0700780d03016804000c41ea1050680d2042c00c0c00c640d0045404020440300004101400600c080c2c4000c0c440c810710001e500410004660303410555507203400d58101d031508840703945400c0140201c551040c0070042c05410494410000c1910390346005110349060140509107607400808503d803510140900d0301360f440001e0081d50b4a040689c0100d6036414a882550f841c5441c803404104c60000c08000c80e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 662076609 1250 662075359 662075363
    0x80901060b040e06040b030c030613020f060c060f040c05060a03022101060207090f330e06030601030b0c090a030308010501020d0207050a090b120a0614090d020715182303030304 78
    0x203441595100c80c01c5c08010104070501580c94460900e04c6d001c5a81c00300701c000d114a80e040c07080b00040140d07106100d0b91080d12250140300d2001070040400c8010002182c0e030b0312110b00791000a2585450400000300c0304960000c40d04840d00140c1d014506416400030103020f421810418510761040c480044403000a000711801030304104d0040080c40c81d542c0084102d2000d424000034a03410009071840130b00034214403035444406002004005c02c03101c0ca605401400030100184551402e01c0000f600e45c4014003000f40300c041628007207007c0b400d508064440c45034010b04424000394481c100640103e40c01d201c1c850041c0b0500510f000000c0c4081030180803a40041c248000365403c00c40c0c010701400148a032140c10800326911003a50380340400c121015580035000029015640907a64584200f0081402d8050f034004011078800c0c2da80000e880c8201c0d1039a410031a10b100b65500b003188c0c9150115903910611000f88000702d0090b070304401c101192401034109940d1410000b06058480c0011180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 662077859 1250 662076609 662076629
    0x111207060e0a0e090c010f02010b0619030e0303101206110d14070e01080c0f0f04090b041104030803070c03030f020a0810060809030f0d021303260f07020d05010b10080901060b04 78
    0x117201015402a414aa1503924500012580e03d0550000c40c1850300a183c400404115804000c20010b03014403418032040c4420700954910325004001e010040894031510380c2900e103507400501401190740c82602546100c8086d40d0b5074080440320302c13025001020501c919981c036040491040d0340161078034141054180c40c0c000450391011015105030b040340c0c0c1505681c1c042040807040210542c002000a0921004002181985801808200e551324100a500d11004010a002182e204400e40e54000c40310303d05004451721a150803005440380d1000c450301140040348a40d541500288140c0c8500d00002039080722683d10001105c1c521825240d5601540003040803410a00744000100740c540081e04c800b62801414880307900d0404c407035500640710540805100c02e400c48071092102c1609140d04900341c2010340b040d0400f840c42c07180b110000d20640ca00b1a110080100079001400c500c4002821030a400c85410005000d2110848400c0302c15440c00c0307804a10311b4503002c1034900765000025 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 662079109 1250 662077859 662077873
    0x1807020a080d0b06070b0702070f1410030603020402040f0806130c17031606050a050a0c2a0606081c0f1d041b0f110609030304111207060e0a0e09 64
    0x449500750303446100019410740d11100c4141041d00e61344018501c081c4038544204e10f42c988420f000781418010b8100540c0c0400404040003900c240c0e035081071141c00c0460b603152030610045c0098005255541c0001d40140c00400c0000c0c200d0410483d07882151026015221103640b282d42c0d040c0762004180006100302c248400031700402510120a030001140329049078505513421061815019042c8030484049403500d0411007400c1c210700445402403202d000900503520000f601401ca00c0134881c502c031120086000e00c111140c448400250901c0d0003c42c1000a0380d1105801c0c1d03181c00ea14a00103d2920007503100c034031030b82c0c810054a06051020380d91400d2550b4050300c0d00b1044204448160303402500c2d1281107401800220081c074100700c007a150f02c0400030340030b04c1c080c02600c03440118000c10340004040215000340030007200e512503804004102d1002604002604000c2c1c010700c000302a01c280380e00400c10680216a03070305030070000c80705642d1155a440025960034170481e544491f58010308 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 662080359 1250 662079109 662079113
    0x1c0315030807020a080102030a090c0605270d170403050d141602060c0d020d0e0103140a0f14040b040b06151206240904050f0903180f06030c07021807020a 68
    0x540b00b0584000c0c9031812107545c4040d21400d9800581e1850b45481d51425007004102c44903014900a102a051040c01e041240407050b00c00c81e040282103440e58000d01d40801c0c3c13a0348451010780010352055400141c540309220580d60f0380c00a001c1282c4030300c030b44045007420b2030150218080d40503056150b103181c2115200c40440c00b682560080b0780142c400e1026005619087c0078125040140d03600520428450b4040149543d00708a04035060524000014203281480c0c0c06841d03000c00c0071040071640d04403c03054070004108110706042400f00500500c42009010412180a1800395121011588880c401c101e00c4e0b0b060100202ca40043c10440d11040c100e012140300c0e849800103003101e205c6204000007121405031841c041d4503640d000a50040140350910491350001c0715105104a40d103454100b1566911074503110344c140f0101e00074244501c2c0c0c0e03241c0112a0090018001e01c0d1a4100203421480640101c0030407407144501c2413180c0307001c442821030a84111006d07801001e038501b1517 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 662081609 1250 662080359 662080373
    0x1f0f03030e010c02040f05060916020a0303050c090d03050406120204140f0d0210021f050105010929120a0e010e0c12100603050f06070801060f08180f1c031503 70
    0x70403070103051060b16039111025903228402c44000e01c9180c1c2c40401d40380b030f08004006010780020f2201145404014011490540c00110000301300d0385410005855241c00207a050386004a810702a84100e81000c10b03c03c042d8410081c1c02180c10039242c80b0080070350810800c3c1030b030280380101c2c00540d00c40c004462040c0b904102000003d0300107410b20359551902e070045403e10300c0c426428000760b0300581900d0342c1a5294110500c401d0a0b20404000a50601000a015002c0c0d80b041000c0e5030031050081e004184850412001e55130030042c0c4640d40c56404041c0400343e9811103038049074a21b0001800c4c8d0343d040600400c03080170500c402829038007a004c0304008400d48251150300c514843c10300e004d82d640480d0300c03d010107107024600070300300307801040340780c615020005003c0404c10405500400c11540c111140b20010101c1c0c0c00d110440ea40d85a149a44440141c10300d01b01c140700740e9401c01c00314040440c51180400c007401c207000002100c0e400950940e282490480e8820b00c0740d5400300041080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 662082859 1250 662081609 662081627
    0x30605090f01031208060f0406090209011427220506090f1b0f0d02270d0305040303030914010c0905090a0e07050f1801060315140d061d030706051f0f0303 68
    0xc0281300b080f807c400306010500700c0310305801101103282e000506c4612580c01c404d000c02180100385009181640ca0ba00c0c844041500d505c10100101221071a05510741d02d1111340d1250442000c0541a84c0b500300401c1c40103410240c45c081c1c000c030001c40c0800c2802c2850302d0313600d20500b420708425102c070104c07004540c1e05501c40c2401ca10f4030382040c401c1c070a242403035000a001c103104010956599951b24002c0d809400342d50140300344501d03558000d1100085c0c1040a81d011280c050800040c1c400e000c0c242040d80c030084400a01c43c0754607013040070302000e0700b05044005458007038500c8807203603846100c41400c50b010004603240e507901044c02001186016801d041e07050401810a2624032425104080484002c2e040140881d403201c54034190f4101e40700800d00100350585070115070ba4409400f0510702d0b181c000e40a80526216191003102024040407640c10b8500c8504070396840000d0300b4030b1401008180d684000c034040d00c901d14001d0081c013141c0ba80c00d540341b28200041c0649155001c0e504000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 662084109 1250 662082859 662082871
    0x705030306093705060102070302031002070c0923150f092a041a04030803010605070c030510090302010f050903041707080a0c050102060708040b010504020a031b030605090f01031208 80
    0x2a0100d02064400f0448054545001c0080c4924101e002d09000c24165100145000d04551100c20108003580d070014105c0c2b0207000d078100040c0d584207141081d03000000503402c889107207410021908001024108900c0404248202d41400d0303468840007280056442d82103541d00041c1088009410300e4140451601300020301d548514100b002e403280341250350841d0148094040c042030801840e5048808081d10200d15a2064949419a0b0f2462440d00060240c03108100003c200703081001103685003030300070b141c20208a402c40b18001101d4005440c1c442c20440c015403c0202da04020036150142074050000d030030140d4106802c103442030800f040d031501441c2031031041010004240105100c4824481e00810201d0700080c244030019207000300c041d010b00d0820440c0c104000101d100c541341c0b24103540c0112400361399410a514200c01030084021202420021095981010794045d4040400c031141504c01c8441076450050251544000348009801c8004804403036804910540d0110383c405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 662085359 1250 662084109 662084131
    0x1a010f020102120717010e0106080f1e010320040203040809012a0506070f0516080a020705030106090f05280213122604051309050a0f05070303090506070503030609 72
    0x3c0d46448500c01c0380c40054501d140850039a150083e00e8008001e0300300d0150011040309101549000b10050400130024101c00780a0440c801041d20b020000c031411285400501c0f410400396142d00b0154000c110000800d141900c94000001c4642400d0090f6845286c01258003410110bd84006403480d0506000c1141008203582a02c1001c41901075440c2d031160181004122914084a010b040d0903003225000061001c140b22031800107006800303d40c1c809910801035502c541084005901d89226030300321650550070504042884d140d141d114880c54810311038140310036142c28802140010308500704d400740034803081c0252a255401e03001810014001c5801c049425a5031a49001d09030400b80c0c2124181c51441c0490a10501610301000c201542080c0919040ca8000000c5601c0700407510305078441d8469140342c081c000c05104103003a0542061141c507100d0001c3c81e149484070b01502081f40400c513aa071010039103051520950748016400401940f4544640c020070200310801820f0030150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 662086609 1250 662085359 662085367
    0x902030c12070c06050a0b0d14122706030912160b19051501090e0a020c0a0c030b010b040b090d050c03100f1103040804060809010b0a06090302010f031a010f020102 72
    0x9152000c5000b0321a000d02c1e0307a040320701c15862900205881c00603003691010750503e400070805540c0c0004044071181d00980611103802c0c0c40300903034100f805c040c500c00c00000001c90724411140000180c0e03588400c2d03080068224071070303440402c4121700040e00ea500440c0d00000700b240c0d0006004c001080c10050141c404455041c66a540810b0828203c9030110000c00d800c60700b00c1c030350003140502c5400c0403180d81d00302160a28100020103a032020300c0344107001001c41c000f08030740b180305a04556411b0b80d000700741c1c0c42041a0f070400001003802444110380300b140340ca000086500c555401e0b60182c6800342c096510b00040c0d101009110940c0072400d940c0c0307000d510850b5031981d4007000704010321001628041a44000580400c04880c1c8140000005000800030400081c1d40e000855058802c141800000c80e01c7d44501c00e40184801e60f00d05411000d010000325480b038010341c5c117004680c400da80c0d901c109014800c0840658015507440c00803103034500e4401245601410b003400081c0781e140700041c10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 662087859 1250 662086609 662086627
    0x30b0c0d1107030e090a0506130902010c06141014010c080927150303030405030702040e070e070801090b0607050a110f041806050c0c060412050c1515030a0b010902030c 74
    0x186502903081140803600c403140441e000d0030003900791540032608206c1000a40ba0800c081005450312555001c2159901c0c0c80c66811a0b0003041c600403440c1d0440c0003008071100d480c09886002000380c903e0011000511000182020141d2084038000f106a40e1310500b48017655a900b0703250030041801d540004080b60700c0b12894003401020842c045406d10058882c18041120340080445241c0640030f034008004000c007141d4000112642141c0c140d50000307110400d9041d4a0070308039503030804188a58000f003400742c000c1e030244405041e10b20042d001c101c800301d4541000154807036840c008000b60051840351020031003240f01024400b4003d4114080d01c0d0401c4001000c07503d41c40004001c0d02c8200e9211418080b9501c85c440d44100b0b2100864540301c00310314810382d00c01c40240010000f44000e840349a403548240b00f0b4400b070007100022141c01280304030170065040d10440d001541c094901440e1489850002000c0940a4226003c0f4540d40d0814030b01780040d60000b4103000881408001c0240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 662089109 1250 662087859 662087891
    0x12110d060c0c060f09050a11040e06131208061c080906220f23030319020303071d0d20150a0f05130509250c110406030b0c0d 55
    0x1e0001141e0320a00030740b003503141110840b4003c0c00600115481c0c000c61000091001401a40883d004843c441480c00204005009001f088a4102c81400340409100d94654038278460004584101c0f4034203940031181c034044a44010442e0301c0790303028885100c2c04c000441080c0d98100b66070b00904059160845420220313041e6840b10035032000c0300e420302c1105030580303003e01c10b1200074280c410110b1060901d004401c0341c0c1300314000c1080040d214207504e881a42d40d0108221181c1056110b880184010107401c040d482e40c00880344030340070503410341d14a449500307101d00103012114002c058070711905181d29903400e5480000604100c101c50342c0030030b000325030359002c060b1114103050302500e5840e18074800040c81070b0300c41c484503418060280070800b403010003c401071064070790540d83d40f001035a0340855000c0c00750954008402106220800b86603841c0c0c0109900f19140c05072a10101b80c41c0c082c010f01c422240c0510018181406d100e01061040170003000400c080030420002040c03217103666a05132 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 662090359 1250 662089109 662089121
    0x81315020a05060c0a0806150702040c0302040e1003031b1b08010c091e0608040503070b01030b100e0618060307031406060a06030c0c0605070909050103060203090c090112110d06 78
    0x640580d10005481d0100701c810058603034451002c100d00e0342059241e0002a050b042d02911b01e512502e000c054007000080c80d9005d5034a000d800074414442041032400190096125000380600c0142500004c0c0180840c443c1950441358565901c01c070b0a0049103143c0b03000529084101c0390210804003070250190040d00c000c0103000c10034000034801045c814042c2c411981544000c07860b0b442620360603e00d00352840c50300d04503144c82c20404070580d10751410508500c20040020003801196002006002600c1c89862141540ca00011801505c802d55160070500864500b0780c040359034030070040c0f0f0700039244a80c6e4220301d000e011242d40301d4481d52600000141c980050702107a0082040200d1464841e200d81d0081665040070443c0300c6444c04002e04014685802402c1591603002040d8010321a242c00001065091300030040d650f101c0c900034029601c00d0314030300c6080c4180841448145030143c0a107040350f8058040402032100e0742d0b21200d440320480c2c0c0c51640034549030391400105880e800383c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 662091609 1250 662090359 662090399
    0x902030103081b06010308120c09030d020a02131a041a031203151f0311091306450207020607060903082401050d0902030a080a0801090c0c0813 63
    0x202d03883c0d05948404085004007030a0514950f80040d0040003c600d0820844400400d82e907580903c6540c0c0801c00901c52244031b0641d5010b1042c0201007850a5001c510b02d04214401c94443c1d11040103012050103640300c0c07450f4101d400c008811b4082d00b070714003503008030802d00040c58000c0d00316140c400000e080000c100103c1c0b03241d43c400401c100301071202d2b042c490016030044400450a0340d890400246c03d48032290080e09040d41c40100103690400b107400c0d55200031004100601c0e181d141c0600c0341c0070304158801d0000d45c030030100541d51110070f91070814880e01c40020174003280001340402e1030110720005a19242c034560800a04c00540c80d003400030000305008a0000c520304655250040000500030100b40b072080000d032700310103180c546500e80d0542000928103036403900c0700c401d000f000406500000942c1803041715202400c10030b0100281445c09160b8a903c1d02c0b036a0f81d8210b000c00e81c1d403407000d140006102c400c40c020000d0140e4018100c80c0400c1c0c50f0106215403502035221141c4519088 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 662092859 1250 662091609 662091623
    0x13080a0c03050d03110a05090d0b070203252103090f0803040201020c0f0906310e0d05040305030708070629040f2a0c1709131815060902030103 63
    0xc1841440000c00210540b060503150402c450030f142100503050340140da0580f410020001078072103c941e03c00215401960300000101c4c11801c0c0b40001969a5101c00030141d030309000c28200411140e8021442222180c000c0343c0b04d0b80b64036004030003d05001900640c0e20a055450b0110b80c0802d010408030501c2030702c290000c50340e82c2000c0c000a07203441c422105a42c461007050800508a4546c9401c2c15006001640c202c00c034210340f0089101104580c26000d903403481c112110b07800e0326516400c00c410110b522815500c803060940400c440034803171307408042d100b68400c00170040050204c000410500c1d011341400101000c883c41c0421111134500b0304102c0c46003114102c9029440d01c2d100700502110342c1d802c01c11403d00c42035007103903074000f403000d0b40d101d80c4041055010105018400c030945955001f4284400603a00c5c2c0c4084030b81e50420003185000d000340801c0344200942c1442034a0310705800c00407101c05104203550340c052800c5009040f04030980c4604001425510500103907011314803444c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 662094109 1250 662092859 662092883
    0x1050303310602010b01093206090909070302010801050d0c0605030c09031b01030c090305070302120c03031909060f021c02011d100506062503021c020f070602030c1213080a 76
    0x100040c11000503400c480c100c20b1101c06234080d005524110410161305081c80100c01d849802c000441745d000d1615010380129a440810015a40c041003d0041d20302c00d8894508036626a0244600e100d410140201805042e16040c0000e501590246034006158070b21103203040032000c0428105500c10b41072480e10440003143d003101d5a014059100d181200d0b02d007e544062440c0c4941c2d40c1c902840c0f10181c0070f074481136481c4040fa40240310900d00c103130014080320350b220a0301518409010400c0c00000001d865042c002c5642d0348500c4100e4030010040c0d0081c0139224120000382855040c0140d0441550f40e41d0401c100b0403840c5d0982442803071040e03409400d2086002509500741d0b000203046510541c0b04001d84801c40c02c030340007030940d605035500e010300c5202d2461030141d02c0d003042045c0d8481c60414031240c005d0b0407a8002100b032030001e42c050075210099500e02041c1d80e0780c06506150121600074040c400c100e03a40140142c0032600c0001261407110341c0d05d1107080e01b8500c810384d081c1c0ea031030031030341c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 662095359 1250 662094109 662094131
    0x1e0f022206201c03020d0b0f0a0b07080d020403080c0d0e06030f13020307060203041707031a0703091a0a15081903090e0c211509061305150a0e0105030331060201 71
    0x1205852047c401503035102690201ca40004103424514002c211b00d15130045624401e101d051800d540198000050031992561241005143c0d6001520a00b140748642c198004601b0b11860032160030f040c01800040c11074546400f03030030300303424018038102c04101da0440010144e502000118001d0405c0d4000d03580c7d407805c050760001075801c40540b0a0190740502c108100044044002010107280c1c0c00744290a07442d605c80440103004200e02c0035080c01441980f11400c1d89184011034005d240101d0b04120010420400070010b01c0d45100383d5031150031250300c100101c032000200016103403007445d06c0c140c00f584511650740ca892080d0f40d000c104010125080080d01000303071407101110301603100c8907200d15243e130461042030072140005d40264110000b081da140c490300006c030103d000f280d200380b00601e04a03040f00f290818120900748100042e5000003501d1a0180c3c0b058141e40025014620f040b80340011a100b085044031540340e03040b1880c0c0c01000e07001840d00c036000504620341c00411008200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 662096609 1250 662095359 662095361
    0x22e090f0b03190b030a06060603020a1d0d080c0a0f0b04020f0a0b0d0f18051614031902030304080a0b06090a0b01121e0f022206201c03020d 62
    0x40d00001404001002401415038402c0030701d00350003c207040e010461882040200c2d051402d05180148003504100300859041e4041d00503007807460f45603885108000a000800308104000e1a00b5504440011800f0f00818021002462058076000032038600d110b01c2d50f00d06543c540d0495040d9003080c5540140021441d1944001007016400c5031100b5060341400e01c00b036100d200722001c07800750301d590f4030201c0d0000c461904500c100c4c031201e00702442200c50034107003030382c848032100e45054000d51a0306001c05c1c028039076214019004000b078018118a01189a840b5090415502c10703681031105101c000f41c4480100b100243c2e840c426812202c0c181000c3e024860389800140c6684441414141c0800060364400c281c1e840070b1300c0d108804129200b44030001504080b4248286102a0401d0b40c0c820907903c2e40d40051071a42140391800048441d45d007070035001071000d40035100004d08400515a0f445800500e2840620064401c0e10302c1d1865000500306401c22a0794000b020940125512000c0340017 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 662097859 1250 662096609 662096639
    0x1801031505041e03091203030209030628090218011d06041a0139030905040501140d0507120f0b0f16030c0201181a09010b0d022e09 58
    0x480c800070312903401c1607030b43d07515902102a12855150009410101407610545030307031005120615030b8441049280c10f00401030f51010725014024424000071480c03100c030600703c0743e2210450745461a54580c060200001400c07040300141d030710081e01d880303a609d203403401da600d00d0080010080c16203808060320311021084074000c01c103d100c0d528151520b03100403601c55142415a80c01d29040800780a410012449803049028450041814650000c8000c80c005c0b00a8181d502945425900316591400c000540b003090040c91074105100d0200e4002d401c2a2040d00c013100d101d0f01c15504800e884542da41041c2c41c8094066501e600e159844805000c0900c0d05107030400c04c4140c40c1c403403510705420584021080c0c841d541c010566203980b0210464401c4d070119a0042c0750060b0709001c0301080c2418040c1c40b10886490030001ca040003c101c0d05001403240200154010305040d9400540c1d03000c2105009011040ca49031030030424031842c0c14540c0810074908040551605c10f003650038001c03d0544984 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 662099109 1250 662097859 662097893
    0x60109020c151e0f06010908010603080904110708030f150436210201140106080403030218091015030e03030a0e07080303130308060105030717060f180103 68
    0x120410504107568030101c1d92000da061010070403900c98440344800d00300208212411808440c9210501403107048000c222070158400340c2c1c0d0000c0c09516601628201c0c2d00c544401801614100501c15050410750886400810074541e0755040403e140c44800255004540c981e001e0540d40082200c00c000741d138410004c0b14801ea80030007400c01c80716003e81090b025031050264601051110548210020394008101a84108803072000c2c40311070160040182110400c102550901c01c0c0c40228094544041d0704071009951145984d0b00c840e201940203510005030036240400148016409854500c403050240d0507070218041c01c54070344500d0a410030002101042054102000318109500000c1030f42e4000c0314041000613040304070304466207441d88079880308255010200c200314080d5441412416054040e4035002c6541c0c1d107590044071984412542403000c02c1e090b00c440d03005603018011050340020003500360140e003e00140000e4003803c14549004006a5a8006204200c40c464420702914 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 662100359 1250 662099109 662099111
    0x80d060902180f0f03010e03030f06090f04030c08041505030402010e10021e070f03050d0305160807050d0609021306020f0a030917030d090605010311090403090b0c0715050903060109 80
    0x9100300d000030040c00301480c0010710070000e0500480d10f694518000024800d0b004000b000000341f5410090b4490b0403c85504900d0a84000003480606010052a00c1201020040304c91aa07859a00f41c0b6460408181580e01400030b01c800704510350040f800d01d0402804d601d8003a100d103058400107084042480c44e0034000c440c483e001207a020380002c0d15109204911008030480030b66078880310300d0440c455000d0595000d0507600081030280115042520980703c0c1d17410f2000b43d1350380c00300c01d1074106443c00140019501d0310000e066644144050011410001c0b00130801d41d5031400030100f6a0060283c00c895003280500801402c1e170108000d111200303c0c0d40150035800c1c5c031038402910003a01d5100343d0b05003490700003110130400801e200304c40880d94034010402c95404982000340c0106024081224568690518000f0b00e1070b02501c071510460749565081059410300f8143ca006800c01c2c8521f20302071051000109980800c060000602e00c001c0d07407400d4a0702e109000b054946141a40300c11815 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 662101609 1250 662100359 662100367
    0x5103c02010e0303070c080f0f031e040f0f1b060e040c021908092d1e0d060b010905130e0610080703060b01140c07060207230409140604080d060902 65
    0x1001010081d13035405005400c21a01513040c506051070710b8400c40303d400001c1000003c05448010840001e10701404d4401a03000c001480031500d04c2c00d007a42610058060300044903e034001400f550300e0101803510803040007000b11548004c8c01400790158028802050b4008000041c504251141141d400a244000c0c003000300a892131445d010356620700a4080600042c4054031512104000640c3d0303000000001d05241417411600c0c503602e03200e0300d014032072001d6001c002940189440d460b03c80e0000102000c0040300d980e56a0700083c203000c800319050112104001038183d61f4081c1021408840b1034010030100c1c103c11103507040c4400181140051440020306200b41c000000310041560b074000000140c0b406c1e0600169045680f01d03010b202c078040d0004854503410404100c07441128031030b03002c449015880e4015505d0300b282402154445600740d0005c015985400c0e04802c503564042c14500d04c0c40680800c07018140002110252800300300001c1c2c0c5580e004091042d00000c1426001c00c41c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 662102859 1250 662101609 662101631
    0x3010e07031b2603041a0a09061d090a060f08031b06010e19020d0e010e0c01051c090c05041503140a03080f0603010e10061404060b0405103c0201 64
    0x1c10300c1881c20107100b503103404007000783c58108201d8020380007002c154941002e040c40003003065409800100001100d040c0001051802501529640386000c694004d201d00900c080c000d402c0401004084115260324001a038000310032a000d000d0400b4602960341c4d40c2c021108030103160000300407060300da03102c0b000412569824540285e0090b2828100944061210f0304440c064080c400b05000c48910304071414107807010550183c20034000340419540484400b00065400b805000e106000344039120300c60b84626050395000501c0c1c04d124400080c45c6030f480f400032500319209a0400c50002c10440c4081c03013840381725480e0074052801d000007018020002d42d00101270380c030068203000401000e5001b05907035903001e42103245540700e03441c01ca41c514981d8010300400360015100d4036640c0ca074071010706091805d041c00b80b42d0961741000911440c01d86041d05211480c002d40340d080c0200540c035010640401c3c1500ba40c800b80055542e5158a0070902ea80325110b007101125483c070540e0701d0510310a00e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 662104109 1250 662102859 662102879
    0x101403100f060515041d0c121009051605091002031c0204050a080a030c020409031e0815040203012303160e270c2101090605010f1502060109020708040503010e07031b 73
    0x1b00070841c80410030b0180c648106180c0c076405001c2c841002885544108410300f03506101d558201c4014000130320243d02d07100782c400300344840200310700d001032402c0215010a00701104101540501e03481100e142240507201c41030629400a4410612034000404010514018109c90050100c2501424151450759409031004070741c054020301854894a240301414040c018400b0504c2c84040c004d00198043d500052148408941507003c0e51076010b018204c3e4241442a00c0c1030303d01c994440c03a02254403000402c403c451620743c19516100318426070a94282540c0303440014050940c9400c000c1c03c2100c10b5141c40061580b031b6414070040c1e05549802c901000410601603007081c0c4200600254440101c41010411465aa8298280444802003000a510640c1210400e060450029403141943d168044040143e280107034400c2005001584407030303005140651090440918241e66103010034251140000c91550681080a041040c0003035100150804601880389645003070820b4840a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 662105359 1250 662104109 662104139
    0xf1206040f0213020c06041211030417011d16050105090607060c11010c0c14070e3105100b0909030a0302090f0613081203101403100f06051504 63
    0x1d020324528018903400d5481d840e0001907402292841556103103903101800e650303444242d8040303a103500c0c0314500c0c43c8407510401c4507424503140354000e14a051720700851100c00030780000006056550310f42c1202d002c0401c1401c1c10708868205d40c0038042c90356407c1c0840400b28410341c0194180941000710740c00079501c460403a05002d50100000038000540701c1c0895442105034a03000e01c80d03103000c1c417030f41215400c041c2894445200d002e80c1080b0510041c007a0351202414801e106500300d0740d601080c1070b480c00800031030f0036075540507484114000c88603440c55950400c80041e2901d0f00100c20307030314078121030340112071514809541e04440c0d400c100020315581d01c1744c407103102304141d40031440070016980c0c40c02165038000000c01e01c03901c0340c44421703080380d940240340324001641c850880032510060b440390075079108861048401c140180340194458014441c645030322341c18000c014006a80d055039100e644002080350100140d03c0f8204400d000c0d50150840d05020480f200f80807c1060040d110501 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 662106609 1250 662105359 662105363
    0x1516020f27041b15051b0712050106050a0b1b0a020a03030504080d0905030c010c061404061e0b031009030c06090305040f0f030b070f0c1205090f0607052805011a0f120604 75
    0xa580c8403103100c01000d0f2400390b070402c1c0806024081f40011554960b0100d5400c60380103000801080d651b80c81004019440c0381701d1100c20401c00e00104a5029110500d04140340c001001d44411503026400500c542a05800c200d0125001207802c0c0100e42c4100140b000800460030443c145c1401d150000796107403c02c01807035042044003440d603410002c0c5030b04030031004c10050310100b00310300301850100081c00e001712156003a10305551080728403c0450084c4d84030741d840600a0721f80c1c9410038481c0009482a654168140403001d6145030004415114072042540a07a88040d02c603400c0c0440d9600e0b2080590141c1460510407000b800820700c2c2000840d000304407410b11583c803000d80c00d8282c0d40000c1520010305900c600c0e016104c0f1403a0000020072944004544600b4403c080703800700503d82c0203020b00a0420360181d19a030055a04101044a0381c0d00880c4c5c03030b0381c2c500c4850303616682510642480c50b0b8880364000c0e002c9456080112440c1c035810b60441e44001e040690034a2650b072a0401000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 662107859 1250 662106609 662106617
    0xe040203090115090219170f0417070b0402030c030d0512090703080c070302010e060c0d030b030f1603050d0503070203180604030803070203091516020f27041b15 71
    0x1290030074800f580030980031414400070a2038540d072a01a40f000750046900710f09090390824401090034481d49150402040c0801100c6254441c003c03900d034100b10061046443c0c000800301c105140340144040c3c203201e8810f00c40d00e915803801784149400c08411400b203902075031000d00900354407500141503175000d07207903080000660b40c1c0d00099685410610791003c0d00340e040c00244d043c11071034042480d005481c000e8070b4801e042e407482d07418010548039652906a182e00031911868945210703420140712208028111034007070300b5251074030303007010030032424685007020880d81081044030910020710542084e0610600f145407088019441303114081e0314410b16410001d541c20b603581c0f0002605c010b0340d084003220740c0f00e241140d0007035600d43c070884c44c03140b02d0b10281d80c043e071070400d1681c21980a0208000562140803443e030074440034000300454181d1080400c01d090003c0f00c2100c1c0c011a802101c2540c400c01401d2a040140d0304040c0d030601850320296400044c0312212f482c0740c28000d040114a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 662109109 1250 662107859 662107861
    0xc060a0c03050d060317070b01060f0c060e01060308041706180703021002070305010c0f020118120e010e100e100206010e07050901110f010b0109050d0b07080c040f060c030e04050402010e040203 85
    0x4140f00401080d00000c1050f10342d03c200f455407400308406016424403802800b803860342c980c3c1056407400040002c03080043c0710b80b52440c001a103581c201c104201400000898000d07100d55907041e042d00030b504545005142100442d48d0840b00704901c941169551301c01d001c000d4412514592203440030301001c0c1c050090b40d180780c601c05100b0800d03030005681102c000c0251140b0150000c00144139111604015820400510000f490f03c041455038113134824000041c8030a00700043e1041a00da1001c0ca040c401d03041c0618042c0c1e214000a9110709180c0d03039410241c40403284c01c21504010901c01c000442d40840014014882e400e250560012070390308200762503800d04801240e0242c5142500c0d046030055424850307004a054201042400c0241c03105540242c4600038020714490158028210700c4458000c107100a010f89140707600200043c05007482c1c641c03a0441c07480b104003207602410006840050540074558441006000004100c80c180242d09103500000c240140481900784103a038004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 662110359 1250 662109109 662109127
    0x1d0111070f02040c05040b070c0e1e010e0a11041d070503130b06040b190f1514030a14090307020910180b04020c1f060f050306132f030c060a0c0305 65
    0x3d0f46c0003090b010315200d035262054949441d4102c00c07071044000140880e00801d005081900c032111140301e6210382202e940e840e0254a810030382001e4815014143c2d680c10f80b4191050004c0108003401d404003100b440c01c642040b00f648104e0009024404203c802d00c14446103025480003110b840781c0118070381040351038410024004012410a450b80400000701101351a68044002c2e0215480104600c0d1a50b554079805a10b201c40075103000e00048552604005030036407400907541019110340b00142145440c40034040c035410640b2a0709161303001040c00700840c60040003c44e800418403042c00e10031441e2a4544510603480a4030015803619811480c580d5111541074464910002d802c40d503c40740c02c01910701e58904400b000c0f844007814a100410f407031070002c07010030031288090b0040145036991b0610300300e20b0040d4441120f60001c49015a800c5241c0301c0d1002c0301c038141500200c2038540006041502d40740d042200c20b402654248022640c2c960070024a40600f905410100d6030f4280e00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 662111609 1250 662110359 662110367
    0x1020a080f0f03040f060506030c0102033c0c06150a27020406090603180201230415030b030f010c091e08011a130905060a1e1d0111070f02040c 63
    0x902d22041c0d0300a0110401040c88030b5505411001405800100881d403161405c2c9034490301d11902e1a8096030041210301c0380c14215070b518400b84c8240340c3c1030328500710030401525000c98483c040c003c910351011801d520b0307544c8240001600080c01ea15200d040002c0600820202517061296804062118801103596298180c9100e500c1301154021940e407622000040c00002c22070281c440000d1814041c010546003044c0d038110081c0c2c050310380c13081800003000041000f00729600030302c0e0881428000010408044104450500c10759200071541e846510241480c040c00d0410212840c1c0c103008405198a40001c6c441c0d0a0721a07070611106100c3e0380c40c8110712614055482a8010762030310b40049290300711445c511114010803503252591360103120b2144140d07125030501a001c1e80151011540d45880796000c07640054800005155882c44010a83d0171904000404850480401902c040200080c49502118203511505e10f08000701915054007196500600074000d86e901c6000c20142401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 662112859 1250 662111609 662111617
    0x70201020903011409153903011d0708070e0402130302090a062c0601030b01120c08011a0c060a3305030115050619031d072301020a080f 60
    0xb900a02c030301c40e0425403d14080504861880182c0603a2000b5408104c45c1003031240168040703d90391000035a20b0302c03001800034003181c2517542c040001c9071481034451200041d50003080c1c0d69140881e508020b084129000c0001840e01c030400c2030310010400985e400c000c00b418104810340f00141c90b40c242219010b00c00e035164201035884400e40d02080705642098103c48107803050341c0c1800d90020303c48030500d0700c0c1c001c0e80300b114010741083e0380c0051010752095102c202c030102e052415a1710001d000c42100100c80701c000031580004c00a10043c400c461085114880034500e0710700b480e180c0070302d118245807206006003207040b000d43c40b0155540d08840106540356906290881d401d0004400e0950801030b5003244210b0740a5401c0c81c2082010081c101158000c903440601242c4c54240c440c0009505144800200414144d8603802185411400341c1615454595172004042d05d601385100381a4803011003101004050518481030748a0740d0110380070000c1640207160b651103103891b51181d1301d1409 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 662114109 1250 662112859 662112877
    0x30603102c160506041d1308030f06090906010602151b04060903120503040210030906060902182b0209070e0402210f071d06040305010203090105040516030c0e07020102 74
    0x12040303034000c0e1070500c0428590a800c0c400c40ca00b600b610f82d100103200040c000ea10512500148460200740000a10348002c1c2d4001c4414041c0004101c640c2c0c0d0300d500030342050720b0a00c6074202d1030007040054100407a10326005180303080201184e42c9040c4c0000e40c0c80000b000f00ca02202c0c1c0d908040341c40c81c0e282d0021100c0349544030b50440e80303654880c280101160501c2c4402d8a9410682140440c0f85002d50200d0b0b02070f94014041d0046804440015409042c10001c00c1340c00319600e905c0000c484220703101500c1c030807141e803034100ca5504c01c00040180907443c1e005102007000900341d940c21400406900380311040d50541d4040815a10b880c426500d120003000c28581140c00007410140c006c15107994824451440302011105859003021a22591310440b0f4100100f041050014108203242281351224640101014a4a61640e03507043c2a40c2040e181e40100342e4449041c0010010244003403410b07441c4086555001c68655140c89400d40802e101d0014011003040c04a14000e1007901140c2c0150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 662115359 1250 662114109 662114171
    0x6181e1e020721030c080c0c120703170703021b01021303170c0115150810051e1305040b13121815021605030d0c060b0102150108010603021503060310 66
    0x3c2910800a00541a07000003c00040c1001c0c0005400c0c960000544901140510042c9a203900c40001c00105910822090b4240008c2c43c40c400c2c1c64040d44601c00d403050001d60307005a150500104090211510b515245040d64010b00903039000340d51314940c800c122034000703444e01070006801c1040c034224402c200c48490307a94200f8507020000c1d400851141c0c2241c8840c02418100040400100c610601c182e40f110382984900108100b0361a000c602c01d0010a19a401c0d04205002c50780010002d203032281d000d624060704d8030308100c1400141c9142c1c55201c100100c0c885112650341ea642c0d02c0c80c507507020440c4107101464501001d40001d4040010161411810711003210840e424080d640380b0700400907481000d50341c000881d0718100414446090410790322401108515960744002400003401100c0c110710404201051508080e00101e0090082c8400041e00500310b00512441650300d69140144c00b00400074800740d0740300040e10548010300f440c000140c1c07103180c00c0340c07020380010b1740000c7c01c0304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 662116609 1250 662115359 662115413
    0x30303010b0c0c010801050906102703170405030307080309010f1415011d0103020f37030513021e130204050103050f01080d08090106181e1e0207 64
    0x400782080003401003069000454280010310070045070610701c24051650400c804c0004503100d4145883c1c850003070303105800c0c000d43d00d22401c0c481e0803252860700d684084030880004100103020041c01c01000785035448654503d070a0420010035500c1c0710392500201030f0a00000001e161150030350001070000e05041045c82018000341002d050440c05503a010b920360480c441c13000355503002d186d021009041c055464100d00b9101c100640003900914400c04400c4400c000d907286403043d0400d07140301105a5140356500ca403401c80300c0140780c2d54070120301050528010602c402d50031000b502051b001e0b41100d202006204421140e07070382c07d4803020f0254026122500301a03241c8440e030080d00549800b03a90400a941e509000c00e2400c1101707210320035480d040340a1400d030f45442085a5a4080424000070913101d540ba6085010101c48031a8080d4081e503030b2001480d1040c15560a0a81c203910030300c01d21007201c000d09001482400f05074001860307640020341900700b000e0112100080c04e03400d01c96043c0303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 662117859 1250 662116609 662116619
    0xc0c060f0c0c0a030c060f0902030c19030f0308010f0b1303080a03021218150c09010f09031202060103060f1506050a090b040803030603012004060f0c061b02010b040207150b0f03030301 81
    0x1c1170140d80c0049515904240714060161102e00c5400c06070380c0c0040040103030020400501207070b40390701d941c0d5810300c40d0a00408808640c260700507150702803096549104035031410019003204803654002c800e0303600007001002c60784204240c0e42001d607500000b0080d51400200c009038024440c0702d1410000c0702c89a010840480800e20700d1485450680041d26880b065001d40a00d210404507001c2c803d0160600203e00d065220300381c6584950924201032a600703440f82c07541031091005a0304c0e603005074071581c018010414240610103c44001610500103501c03020300c2c2414040700c500a4808010000c02c01410540c801c0713a070704d030050503180c00b0141c0c0d484d12080d109440e50f000300c6038640a5802c000048149103040810401c20310303640c00742e4904160814004995000001d10908100204905018041740243c840c083c803c1c0a030811000701c0c0000008040c4c20b40340c1d0102e00038800ca205205003004101700c0c080d9160011048080080c04040b008005146039410540d5107406210120012039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 662119109 1250 662117859 662117867
    0x303051c050a15090c090918050304080d02150903070303051f030807020906030304030201050427051e0f0712050604091202060108100603020a17010902100e01080c0c060f0c0c0a03 79
    0x43c400104407500d104903919064680192140d130520403000484402c41000f00020562003181c90640101d80c401200c4060b4442e1440c54016822009080d0089007060071043d40400c038040e204260f00820038468a080c10229071a4060004050b042c10380b41c00000c1ea1211214801002d00d00410038402c1c059926401c1404a0303800144080f80a0f40b11000441c03ea454000182c0e41102e45c142d48407440e20382460400e006001d0500640e501906945e0820a481074040c007070280b04110180004800d074841c1071480f03068500107030024440c0d041c0d550900c407607140e00080d5070440310000d41b4042010380301c18001c50001e090604014001d04415400e00c9019540801c419040321440001c0b242c1103580744a545046441c1480000e51001903172a0421070088a41859843c803240c0b0000001c8058607034010488400751300541c00300003440a40f0444182d030308000c6e1250400064079103242044041401d0070307a105809441205034421880000b0364008080045070b60002d0414192500c51a41c0d00d0060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 662120359 1250 662119109 662119121
    0x4060605040e0a26030402100c0203060a02190e0603070c050f15180d020a0f0201030228030c05070506010915030503220504090f031d030604050604030e030f070303051c050a 76
    0x161031030f08001002c0c42d20b282c0c0c0b040f482143c00c0c103501d02034079580700e47d420040200710f243d11200910898001010240ea000d2001900c20315103040e0150b81d030924003074008448592200d511083c0b040380c02903105503031100d2007070301c0d0b1100440c2060f0760400041d05095207450620101e00c40c2510452194401031010502080d0142c01d8540140704903c03041c40303180340c03100f0315510311500503480030441d8000700314514441e03c410b9006050051400c00c00c0030145041d81d4500390040c02a01c4402680c1c0d1049a0500c2070f003141c12840c0c40c0841c1401204c0e81c40d56180c00041c800c902d00a40c07500d41c0510203440040502004651100840f0ba440c5100408d0080c4440c042c500c034074407000c0c0003e0028443c00d1170f0160301c10865000c244c109402019035000e40c2c062005001401413020500034281c9651010090f0b54000c50082000744024035251030000c0c041d40d03426038014080c0c1c22260003050002c0c030019003401a00e0303141c10100d40760540a461311500400481001c12039138103007018003680d640a54055 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 662121609 1250 662120359 662120363
    0x315060c030a020f12220510030605010f0f050702062107020a030f1704151b090503071a0703080a0902041d0d0306060504050603060a0824090705061204060605040e0a 73
    0x2d5002c41c011141e203591140c003280011080541c3c20004030703038072980740100100808500c9120b0702c1b1031919140807900c10310108903400d02103a0b8802041c807840d0b81241040032210b08030300d04032800104505000300b09004050000f4090040407640800c0380c4100c8050003450700c401c407042c1500345007031840259210b050100035008a04c4894a4040091041c966500e440a4003c4207168984540c0e45122955102e0414042000e96400ca480740c4800ca0242c0894500103030750350660320764101010982030001603808051010700180d00c1e51400010320303050700e450030b41506110300d4507583c0000010141c00f4030800294002c0c60300303903204c940403100e40a11001820301004c4560f0900d00b03440903030455046000e07840100d0003c1c40200441e140c00b01c011a07000c00301400c4107403441c2e51054410314004500c4000710070b41321003110b1040420002861181d102100d0760091005600d00340c0400c601d44128022185a8071724000000e0502200341c04c244000c0401a1040048100d0110f25680b40e641d003040c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 662122859 1250 662121609 662121613
    0x10180f0803010306050a02091e150d02070501050901060f150903290f2703090d06050f100f060c08120a0e0f060603330a05061c0c0b0315060c030a02 65
    0x214400206920980c0e404110203850102c940000c0f89e200d41c0400803000c50315922003521105800b0f4030240358007400e03200d8101d40d401b50720762016140c42801e44800502c0d03040c0580c5824010030001c94801000d20450340c00791100701509a80d0282190140b4031078001403d4861408082448080904108154500b0b15900407215894120324040d10480c04c1e54408501b840211510003180b103109214031407814a041264640548540450701326503c9807002c0ea64907569408001d045040024026032107075100880154641c01e1a52243c0340a0890085030f080000c00050202040010300c00c461035042a01140d0711149451540b020203014040d80d000b43d80d0040010000c50301c00002816801100010007825200300040101c60f0401030600c0340d03140807101d4003104200019521546805081c0c240d4000c0ba041c41c00e40c0030300c28050404c0b5410110031310011082800f10b42c884402805503801c807181c6d95580c0d2a10302c440c180c20306c4020341059012400054100c500c1000200800d00b140c040e0702 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 662124109 1250 662122859 662122861
    0xe070b0f042409300b1006050307050301090c0e0310060602010b060403020f060c01020f030103030f09060503011d04140709020915120a320403030608010c0210180f080301030605 78
    0x150156032002140c42c4200461080c2c1018000d03812032503401300503010442c014403024101149490715400c0c00f02410380f0036246120900060885c41034814000c0c10442c10030f20310354104440000d0981c8030501c24028425621450034804921038115546c000c1c10040403561481011100c2c54009d010f28842e442c050341c60044050424205102135508403600140640ca00d0240035061141650011001c40441e56080103455200103c44001d113020710b00079030710b20702114501003019007943d8803900403805101c0144010003030b40c1504040081c1e200442508501d1035100d5107450441c240c00f0f90000070150080c1c00012030101080d501030101000c040b03a0210042121010094032446411361280d41d5840d91000510115841d4106940c402121410108900b00d28120003083d41e0710424402c0000303120741c1c1444240340d41400740ca405444d06100030440d4040c00d0b0780203075882d030b11140c521820302d4a8004080c41d928543c2211848290046402540075034146400e50055009000c112036840c5804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 662125359 1250 662124109 662124149
    0x2060a1d0913080706060314100b03280311070803120a0c090e15060406090503010b01090f06120213060c1e0203060604050a02070210050c240a0e070b0f04 68
    0x29001074003802c9151000c2020710101e480303000c1980d0100606403003031070301d030840003000030000c0700d4040c0c400c4804005082085524412501a25100c168607071080d1b001420119951030442c040c800d00307090200401341c5030603241c9000d940c20160a000e202a6004513100060307a40390100c02086004c0e0718006480640d40d0720035480c1c0880310a50941e8001983c107000602241052000701034111030003001846803491641d00180c0c05521541101e400141107100c00c01060400f40200b410035002400e0090440341030034100001c1c8102c5110b071500b00012400c6060000c0481d60485261010207481d0b1041d01e43c840001900c64000c400c2d0407590003040702c540c2c0d54088149161400302981c028058841600d07418104000b811010b000c0400c015401c1080070700503580c981c800c4540b014141c43c1c00d612003503212840c81c104408580740d141c40c2c43c1ca00180c202d900c0c0768a40c8070b5a1014480c203000454184890340c903850500140c00906100c074000a14452030303100200900211601c4030240100c040c984 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 662126609 1250 662125359 662125369
    0x2b0e010c0f1e030c0516030507020901090513061a0904050a0302060106050f030a0504080906031501091401051c0b09010308040302040606140702210714120609151302060a1d 76
    0xb820a544411611510080700e01e0312a810030001c1000c0c6181080c10003044002038005a018090101c010a000084a104504195990600500348644200807601d4014501c1074442d2071002c1c0100003965031803480c604003203410303003a440001010f00007000c44e2405142c52a620a4031840980c0584519000080d03034078819821141b1001c6903c80c11421502d96842c44406000f010740101c0e1052028092000e2940340c41014502c6040b090301035440003004c4c400003411040c501d801615021007481d0302c1100c540d0700300044801c4104002c3c1e1402c408a0043d11a1004110f0704101d15408904040008207002a807405041903034002c82d002c00000d941c03800255009044001607900900c0103000319009850013a041640a010481c5040c0509050400140c10302090b50000c000f201c00c495110140c2c1d003420841940e04030710b00401040f0301e040c1198450307603881c200702c403401c010491000040c0c601138000129545040e4007a2095442d4001039001501c113080c20f01010581c0c40c0094141d003039602e00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 662127859 1250 662126609 662126627
    0x90b07051006211e06090b18010e120915040303081617041b08060901020c01060806010f230603010b090f10050f0a170127050c2b0e010c0f 61
    0x181c003c80f01c40c489180d844040e0070b440701091a54661201103001e0204810780110000c1c540301e207410300310307610300502203d095071901d200d451038903858002611601c00c00060b01d0481d0407090f543c2103454100d100e0001c3c0344d4070081c0c5140d50014401280001c101504502400e0041c8028002d800541056000440d85101d003c0c5020b002203001402142c04941300c89428500d09d1008030040000d103884654840c5400790a50790740215a41c001480310310380c502072244070003500c80d0b40041d01a075450b01007806030880303c3c0e0040d000c41a0301c000e41c40035640d2100c01152815031010700b64030785130340c0c3da580e000425400c0403506a016401031014084039242c0b03401c0c0805c0400d116160715080841d690091040f41c2c004030025814042c0b086040c180f41d100c201040c500805c180d1071a100c0d441044500b14800b01c2d03441d00303030b03441d41401c00060108985204040d1118000349154031031070f80c01e81c021071216000010030316402c06898461100428407064200c09200e05140d265804000c41c50401200e403c1c00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 662129109 1250 662127859 662127899
    0x2010507140c0606130f0e0f120f0904020a0203040312080403081e01170703050111030403020d1d0418060914120412140a050f0d090f120f03090b07051006 68
    0x8103c0004510345015001c4880c5001c2c40385001038121444001e00003219000503030710b04968040500c02e000c0d002c0400010b540d01448402581c18080c10f852801c0080c09020b03211446250007041c86404a0710810a81d401107400130412101003d080001624030303802558298009114070001401c0c0e010380c0d080345005046d540250b030755584e10741010000071240fa105a0981c0e0702801c6c0e80000801d109001c0c10301c4103c0310103281030340d81c00c0078500a0301c1d0000f101d0a400c00d100f900d0340d4042c12148a00300d020580001500c0c04600403074132920066103240c01c458001c05083c5403000d10824004125042414441c0580031220101810b2010286030702461080d0340313102e468511b80310f0004000c0000241000000001c0754880e100954a03a800c2c111110b14a070082e0b402801303260440c540c0032121170003c1c210b1b083c140c401e03d030810081241010303049902922500300039034903508251044001800030000e4800c00d589a0070580b80c10740c0c43e0f1014101204a5600340303440400c40081d044800000f44c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 662130359 1250 662129109 662129113
    0xe0418030c0305040b040608180105060a0314010f1d010609021303060f0f230619150e1c171312060912052503021f06051002010507140c 60
    0x104a558003114181c1c200c1c24102c081100620000402c2210103015001a120b80d441700c2c0028500814070030050f041d90181c40c0c21680c1400107001c80390300c070b54001000392600702da103c0311003101080d00180540101600f60454615110480b0345040011005441e43d84850300240121785d0742d541b50f00241e0048081140504107140390420000744550f214501c07a280900e00030a11740c00401280301250b02c01200c0c07204594880890701002140300c4e85403030f032150382100c0c1020011100c80340303165901d5141c00b8861015000000804010340210301149220038000d188040c114015010a03213032903020b04084488081c1080c104800740c2c2014207440180c052251400b98180c03074800300d95540800ec0d9400d50702d1a03a00d03486600030030001d0041c140c80c0c240f681c4420380d540d40452200b02540c1c0e0911041114050440c0e01c240002c1da01044480e102d14804440b854602c01d010310202c01031031190300203070f40b02c0d02d041b00c009005074040d00068400c0c211600d60764446018200488100d00c94018800566 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 662131609 1250 662130359 662130401
    0xc1706090601150903080a0c020918030a0c03020c09181005090c0d1a010905180f1b1210060f08030309150403031404050a151413140a120e04 62
    0x403c0c04503218040038510761804a80541d40ca465076130709a8415544803000444c0302d003512056080c58849075422442c000c1ea0340300e0701c10055007429240d00840d00c0310f90070040c4084135201818070803c500301038050b000b070800b580303400c14003003250900e1480b41d03c415281c001c0355100d01003c2703268442c291144284101030080c1044440801000341680ca404541581c440810300f4a042480c0507070b0790180030780c02000901803c00d400c0380000c003003080020b403545500101a40b10610400304030300d141c04108400c3c40d0300c04050b0500091100241c03164440c00741c40780c0302c81740513203400b1a0411000c5481c0710310252200c1d5200c0006a407a8070084403412015401040c10076080f00c0c0da65026903009000c0d140009850220001c11041d4007021740d001c0d16268000108102032001510101204159001041000407000481c1e55100100141448488002c80100c00706200b400d0800400c803202e500d094610850700b600e41105a11084504103000070000c04041165060074402c8807020f2155250125031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 662132859 1250 662131609 662131619
    0x120306031b090522121e030609110a120b04110a17010f03020901030b090c100c030e040c090e130203160602010c05090a140a09060b0a02010b0a030218090a0c030c1706090601 76
    0x22601040b9400b00820291b03c1007043d008108165282c1e000c0655907001c81c43e5494540200151100845016207a450400130703291404c0c2c03c0801c4018240604130007081c1c049420340040e00610b41c000b00c01425840018154840719032014020300703100e90b0791a904080340d8903140c03441d05110250000030341107100d600050001c1800a5501640403030b4803011144a81e0301342c00071803040e10400d1001c201007885042e1480405402080b01d58028030241c1b400c10881040310b5004003134004e240b255120900d2200041000b4102da1542c1c180740c5a009030072102a032003101c082d107079000502e204010040d481c1031260300c1a1031180d000c070b841c3d040b001820500c0326404c00700e007083c40364070f40c202580e0701000d48400002e024100b07001e080e00924100200c1d5440381c6401030b01900b904d1030070707284a01c243c190120a00c01070740c0e0009507031032030080510006e07003d945494815141009040010f050100401000001c02c00420034400556505a858003c5405620b60741c0703656820030787d0314000f950400001445 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 662134109 1250 662132859 662132873
    0x6120406020c12072f0f12012d11030708090c030f06191e090c09020d0c09060e011d01090506040e010e060607050703120306031b090522 60
    0x1800a008a400510301100200c420340b42003851003104521803030109804080c0300c00c0a2120342129201e8910700c81600703034120300342c00030404880c200d071051504032441c18081c1c850b2809001c80c80c8171302000300500d807000030141044a00c1882c81064842e40c0009995441c0c0f00c9009240c0f00c20011119941980c65080050310140c030002c00030b40c15480381c03040000381e82d40e0800c2007001142000c0c1c040c00c21802e04070004203c040c0d03200b00c18039a0354186000149640020000104603000f0713035100166141e610300c1c0c40100c41030241d004601c018004108080c17281c40541c8015212100c81d12041d500964641080d114100541481030200720203074502c80035019021302251380b1100500d0100b410795150000509560030603005010035804080052001d5600401144d412200072505607080400594640c0c0c2e403203165000081a0703440400706908003074060341190025503804440707615a00d0003c20500c00080f080d01c0307084609070030f10f070100345000c3c0c3c0b00c5414100100d4469101c007071308039a41c445030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 662135359 1250 662134109 662134111
    0x50102030f2d0304060b010207080a0503040506130f0902090f0906060306211212010e13140a06060803180a0f0b0927042a2601060b040512010b0612 65
    0x107511a5006044002c0c0d540854010f6205901c601d0300007a4160141000902c1c2010300e070455640381d4080194400490360000599046400840c2e03001d44d114009803040d205840a584000d03189001010003051100c42d03030300a031100c0b00d410380700945041d03003100412803400170546503243c218404101088007401c06480541c0a60100100707407e4807426160010700c2e08640004110308000045400a1040b1045084900400613142c0303401c0141000c2400300880401c4000090800c0345944040c20800014807190032820f0300300b10100290b99440d01c1c4039841e5400f442d5410000c0c089101400400d01c0c0482031101a180b9005242d4505424654011003580c07044070020751011514002100106011107130000c49a80710503101441e00b4189440c24a51120071281021818044031011014620030018801c907012031101d60603140e01110f184400c0c0e034036992462080c0d4200500403a02d045104000c0048541c1510140c000d01e1034540c1031801c82e9402c121150b401a0200b120240d040d01c00c03d0b4071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 662136609 1250 662135359 662135407
    0x51003080703110709021308070617070e0315150108070f0e0f120a031419030c050d0606080709090e150402011b1203112b02120f010906050102030f 65
    0x10144943c0d9282da81c5004650b52001c43e203035030006080c014108208880c10000e021000052a5050070250043d0044000c0c2c02e40808004001380003c40092041c44c0300002070001400b9688d200c4d4025001010355001265607000c04000100000100d52045424901c100c02c40d640315001c600310550200d80c140800e90045d40d00c841300e00c1d10340400d42d5070a60410071855104000301400c10b51842e001e400148030005c0940101e800348651106c403559031112041388100341c60001004030604009591500132003102451051521201054194000040a000301c1e0261100e00030340383d8412036041604d02c6c60401c091250054072038860b061130003205954019105042903940741c03c0f80e03180d544201e4107140045e02d008018000800b01943c01d8491050a810420910f600e001d451600703080c04410b001111040000866095002c0300b0380c207a041c1c07250701400c0c40242000b4140308400050103030081c041c41038603900e031001c002450740c000801c840c00050200002410076144404208484c07840b0110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 662137859 1250 662136609 662136617
    0xa0510020c03031c05070507151d0f0a02090606041a0d02251b0b0720060a02070e0603240402030307020603010602012a0903060b030a0f030807030c03051003080703 72
    0xaa03907032581c080c005812680015020072100707010404800043d281d018202c00148502080b415000c14482e02002c4080e0a4816010035030f01c0d0213943c030182500d80d05e4036212035400350307c44a0780075480200d0818181340c0202c9080e0f1003034495204010482c49a4807a015003100803600190183c4840009001004280d42c030043c1407451180140b0b07c001504024184491480c2c03190b070742040099420074103141d640c8551030321050705040030009180b02d004409401385044603081c0004240d4030701140e4480501070309445c1c0710444542e01a45e04c40c06800313510704408000d00010b015040000e00e002d520b10261284000c000b2406026001090024205a070140010454040943c0340d600041d4001c0030a42e00002c2c13845000c2660f0701038084003440a00d46810340000490105600191250a41c2e422000c0081d040305400700181c5044110607000b0401c80780f80292000f0b06420440691191301c0c651014070001350703422b908900322a4111080302440001803401c0c408180b12402905c009071080c14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 662139109 1250 662137859 662137873
    0x528020322120b010806011505180a0f12021f05030f04080f0414030c010c0804060e040204030b010611061005010801060509030123090708070803032a0403052a0a051002 74
    0x400101502d40c207040980300c0400080c010040588100419401004031610030640030714030100003001481002045200c5011900001c0c00c03e03540e055801c401480508a00c1e0b000a075a204030040f8200e0004043c1d100c2c0900c51b20f241482c00c510007d0461046da07d598861655883c3c000d010b04440c805401038911070020b1110b036000d01d0b4140e005001030314000c510300c420300300f40404242c508941c0284250410024101c1f803070001e0082c00c151402e41e141d5013008090401d0a80101c1d009014a03403010f04408242000043d0701c079088062841c541d140841650f806944240d40c424000740144580e600050b5104010040c0910980103044189801400070510100341e4911003c015000c2c29030b606138100110074880d2a001c00c0201034000c003030160103004081e03d08010580c1320f0000074103003030b21541000c10440f0580e0700e21025414031083c40884540765603da0402580c1c072042e110640114184604007014100040a18403e0011004060b174041509207814404030031211a805410762207114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 662140359 1250 662139109 662139119
    0x105181629040e0411041b020a0809151903050609090705061e0705070503060108160b0307020a290a14040212010f0908030421021207020102070e070528020322 70
    0x203800c0341c1c0242e0081c0119413000554004010447d5003210b5038002170113602c612006a623401050035184150801d81442d115688940131403070103500d20110035012000059821410034030f01c02d08600100c40d5541c10021a9600418449401d005440c1c00d90290312111080006182c810002d0200031749540302e645120301001e034104407a0708080b108640d55008010140414181007128600600801c1d0003403000310b15140d000c07403400f0003a0237070380704402d000030005440b01d000f00200c0110300d40c40700458020365107003a0340505042244107510308124100000c610101e2250040715081ea03109200700d0402e8840740e0030040301810090210105540b508001081005c0b94400d10000da801f80d50019600c1ca000d1800980751058228100040400d400d20455440e50024100c0141485240d070540d4550940c00182c1c40e04181e980b0281b5400002010401160342c0070001c1c02c0c02c90072051419242c68010001c101c04944100511030040e0b20070707c612108108070086014000c0d60305c810060107242c0324 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 662141609 1250 662140359 662140379
    0x2001050301030804150903021e130b0a051519020f060601020c09060f0d02060c0c04050a09050d0f0203040e010b07050d02010c05091908010207030e01020d030b030606010305090c03010518162904 85
    0x490540011440b2000103040c150411044ac04a4000100f03001c00c0408401400914844e04c10f020f51406601044441010485c0d42812150040b103403500003034002d00e900c030000b542d4845423034010025004010101ea055400040c2448603850014002440d596400c81804034071114410042d51001e441040c144c056250040140310f8004400080c141c0780090009002c203498005d0100a01c6518200029010a90104001030300441c1ca00d01819007508511007240346004a8104200582c007210001800d840b0080042894030300c607005036092140c14080507401c98808007032540c041402005010228500342400e080500c11070704440418a0f103803040c00b403ca0700030400490100d4171203a8005915a0104001c0c641c492a904d030520503a0400c00100c0e44440303001d000070b410304d91544041203680e1001e104400203d44040d000300450720302007500000f21120310065180030701801144042c40003500d07210300160f4040705865048410f03001c001c8581026003a4100d20090b00c1070001159a040d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 662142859 1250 662141609 662141629
    0xc040b03190906052a0301210816020a0b070302070e090a0501140f010f03120309030c020904031806110309130e030307170a0225110607200105030103080415090302 72
    0x901c0f0001103929014110a001008103c00c11050144200c0c806400900c0141100d041d00c1040340744060035500b001c820a452003d4400061141e14046103103c001c1c040c805c40d50728058005c882c0000e03e40d80e15000041d061003500344c0540103801600c0d0500c41e00d4561b00c3c1180e00600004101c0790081120b071100750844906c04185d403000e00041c0b04ac03021840001000c103014145010441c074003e8a180d40e61400d00170b460b1303642c4013416200c0c00c2c0c540c1850b0050480c01102d0343c000e00b0301b01d0342e458980b80c0242018003804189503140800d03813021035040d01c110b507460b41c440c0f00e0800440c41c000c0c0c500f00f00051030140034885010552903e1124902d4081400a07501807083e0345c80d102040c034460120115481c20003010070601902c14010507080b08210600b0340340c0600182c01c240c4405a46007455907007800080401034104800003513140030003018180c6d0811a04812441001c050110001103d0301d100038031003c3c0c40740009210a204003175010146450340c41003070801c41c42440d40c1e0350218030f80d080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 662144109 1250 662142859 662142863
    0x30d0c1e0504140f0109060f051303030c03080a0e120306370509041e111c0b0105030d02060720070b0d0e0a170a0e0402072105030c040b031909 63
    0x80c002c201080007502d2120007801c040c80444441034443c1d200c00000748000328900c50b05003000b0001844810701402034044403510080d0340c0040203d07980740c0c14080e04004502c18202c0000f0b482100250380c28200c2e05c25440103020040c058084020000050801c03500040e0420b980070707610000d4482510040010020344601450444032040890f00c43c0b00e09800240d0b2020307000701c00c1001000f001442031080491859900750303509000528038103103171291340c1c104805550811850f8625150264a00c20f800507894424810700c641070ba03c42e001c1c19210401e10701d00038050b030321803004100c0a50003482529450440c2001510b4405001d084242c900640c075401400700d8030000a6907281e08000b0701919407002c8031080100300840003a81d4a00311014040c00340c02d64028082451403180d40715041d070803101000200159140ea90500301401800e40d148109944c48209404100e101030080003580d12804001ca03a07181414603200444000380d01c0104800d01040415100d00e160348441d03c10713048428 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 662145359 1250 662144109 662144117
    0xc060e0105280603031e030f0905010204090605040e030a0503090f060c030a0608010203160e13052401080405060403030c0915020609060903070804050f061b010c03060b0c030d0c1e 79
    0xa6601d00c2d4255444001242e0045950400c1030600110381c003c400d2a1800c400000c8424506c2052102100100b000740411041941018030341c00c14083d0540203030059910441d410052a603030b03941004103c0d5031103143c1508030307041400a400d22074000d00c05194002c00c41805d580e204e0020300b80017803e04808550020700700c0404003d1100c983c0561185030003030515034000714030b5400c0ca01c403a06000e003400724152080040e40d0f030100000340c651150276802808074407414001d81c141344003d10312211407110b40c94003100382410b41f09510b601c03815040d80242c2c1c0050290041c2e4449440840241152001c020140168607000140d00b4401e47c14820030b0b010180d010706113504190442c6414800003415650300c41d40180300f000301184400080b10308854084030070003e20340d22640070481c540180e00b0200808081004900b01009041d00a5200700546640c10811581c0301c1040060314001c500d46034080758024800030035a502c035a40165005082e03810138450815900204e1301c0d8480320041000002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 662146609 1250 662145359 662145391
    0x7050c031209060c0406170402061b0303041101020a0c09020903010603020a030b060a0f063c0f0f0c0c150e060309070f12030f1416030e01120515010c060e0105 70
    0xc0c04081c8045500041d0303030444d4500c2d16150070001000607160b00e0760340c6c101201281c0410210f50310007007280d115001c4030030621308005501045e10b0312030b04211001d1b07884011816018040b50b1002c101468101e91040000c0707120341c10000640002c1d040344082c4c5416641e54a000300160b5a010302c00c1c03006610038401d4840b60700d01402030052000c4154404000b20710301c01403e00c41d058115945921000a960400d442315001501004004010b251130100d55000a000292282d50200d8640350030b80441c1c84800e040e5003508000c8030164040c4101400c0012000d5090000102400041e203c030702e51881c002c40900314400c0041da07164401d82c1c1c041142e07403181d481080261141070080c1f0007000000d151038001d51840d240030f08a64410001007041017083d0082880c882c449030141c8124041900c2928000390a5240180c40e07410201a024041002d226200804540301c0c010b45d4031884a1030008400021840015079004c0d801d01012144d003500e400c0221898602449140d01c038404000003004e032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 662147859 1250 662146609 662146621
    0x312040b04060e0604021f091703091e10030b0607051005090c0f0904080705070e01060807111617100207080403060b120c090c0c150f15010c080307050c0312 69
    0x80311643c0114001c00c0d00f0203000c01015035034038110030701c900c41140038468403103540b100d04a9505c502600181001c594480952013200e10000c0645001c1c901516460801d440e030072140507241295680d074590041c0c07903c070003c40a600c00c4c2c018629010000d8151400d252041d9207040c01c00c0c0c4048000094190b9420400851100820814020450545503540007002c1d00c0d010441c0170344000e1014000e9103000403030100b045800c10100300200918640d15003039585a150091000d041550880c000031450910080d8009010440180d182c07451400b4800c194900402a40c007000411142c10140c010a031903801d02100c240002e1007040d01c00c849083d600c0c2c4c110301d01038044070040329006008120040794031419090000c1d54642d680070480d845c0b80180d4810040c0c41d00c910420710040110700504940501007000b109140703014804858090076540d03600156100d0b00c400c0c0450b054001482814141c002c0f030b8801b0019904070b0386030304e80180707401e040703825445c650740c001c031208110a0b21000c10802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 662149109 1250 662147859 662147861
    0x1080d0e37060309030e06032502010504020f01141c0609060305070302030f030708160c09020a120605061603181a0711011d010318022d090c0a110312040b0406 70
    0x2d00b1182c2020409500c268800038038841e100340c103071400fa170400000700d80310302c0007005201614400440000b00503603008100a020b040c1c20f072022802280442040c04840d800ba00c0d000001401417a10039050007002141c1920011000300d0209507150b48240114050302c0c6400b540014500420003001d00c20f14500c18580b4149581d100001e2940060003858001180103003100c51407020021641e01100050801007901c140303680c4550000b92001270b2450300c058100d0004008490348420030007509a54100748100c9105000e14400c0c0e01c05032544a00010f030080503403800781880c0c00c440450844d15500380b001d002d00792140010003110082030490803c5142c680811141c8000c0ca884419503000000c3d141704001c07050142814951108c4120040d41d003585054505660000e00f290f0304614490025a0020510a1080311040300c6c40145461424603c5c1e4550040204100c1d49180c80c41e0400100d4100c6190411403946000030007140042d1821541598080c078004e203000d402a040510f46a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 662150359 1250 662149109 662149219
    0xe040b0d021c0311070b0316020c03070608041103060705032e031a0c0f04030f05210405041a1003180b010b120105120703021003020d060b090301050f01080d0e 70
    0x103081e80401c5e000c0c48005440820340b600826415180c4840c400b12030310503414000c29401050f00340c4250640011529401405280160701030020482141d01d421300341a03c1ea08225891000305a00b000800c0d1001c0644000407820000542c070070748003020340c40c00f000c03181000d9407080c0ca4442040c00c5c044001c5c1480440b003900800280700b014130301910240d82c5401400b4a120140070101d840340c014040c06030510811181105007491119003a04200040c003154225005050050f8a09003203001800d60030040b41c19607150081000c80f101d00f00908c201c0280034418410b6510180c0c403017560f80000e50402e0010f003c3d1400295154407002d504c0e40500844c50705030300c5113200320107205103884440c1010a8003000e43c0c2c1c064030151300c000394100058000e03106618000080d10310f004800982142d440000d4013005804900a00c2141c603040c10007075044c00c00380200c1d42587c20072220a0000c070f000c0d41c01c410100c1409068a40c00a800d10b009250b900c05020120f2640328120b4018207001c0c140e0035141c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 662151609 1250 662150359 662150387
    0x70806100329040c090b0a03021503040f0f03050403060b0a051311090604060206090d080408030a1a061204050d050a0f11010b0a120b01080a02010e040b0d021c03 71
    0x5040914021003000586005440060420009000061000540d02c0c60018003800c2d908101a41400c0510302603010500c030780301e42410f641c50441d208401d440c16802e0002145d40042c2210070340c60303500c020b011059201400c1151074041084074903001400400b1000f04050080e160917840d149107003000c0d400c0e101881c01451080740c6216051042d5900c0340380340419400c1140d030004c0d03900b941c80c2482045104030301c1c01980c090300c00316000611550015000d4443c00140007030b16044000b80d10203030780c194810344000300360301c8051000856240d020b60000d403010004002e520030103011003011941c10340c0407001286818800804000a1010070012543c948003503140c094504860040e004015000002c050800c0104132a0010310721002508401001800280580441552a00d42404c440c0d22548212211210000000340c00d103030216001c0200c0390180c5480d0131458042e000c02c001090708907020356101306605040409a22154040540d08a0518a80080712402c0c00d0250588010442c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 662152859 1250 662151609 662151613
    0xc0b0705030106270806010f170105010602070b0a1403040821040b0109150e090105160302040609050409300e0d11090415022a0309030604170403050715020708 70
    0x422460341d0000444807013072513820038804243c90040319030701401c4041e403204009108010011030499401e0303241c9030465052151900054043c5484d65090700d409200e4200542c02c0490200044185070004061480d01072401824403407902000070407581040d41c042d01d8071030012590740da044812807182c0081c800441440c0156142035610f408080c0c105015502c17010391180c2c980710700041030340d0000c0080d01c3e03036170501c0703206290070100940207010486601d070703c1c0c001244050468a0092007180e05440706981d4401d4860704107070a100241000c900129411002c1c1c100340f42242218402c0300001c10180e8400911498069800611080e150030001e41300d040c1003004107001030b10021550640342001e8806081c03075540d07400d100c52407100b81088004c40500016000114401c403c0c54401c0e03100c07914000050000519a2103580d034043c000110760198800804103020845068070300c01c1d0061100c036034525150716591190300708040c2d1350005048400c1000d000b468990140480c60150880c0b80c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 662154109 1250 662152859 662152861
    0x1080c01090503060f18101a030111071a07050903010903020c100306080a06091415040302100e0c010309020402190503060f03010b011d01090f120201271e150c0b070503 74
    0x101e62039100c05c01038401e0610760b19190007807491040034004200e560551840410403011303800303500445c1400d80d010981c07080d442c04080c656414174100a80b40050381143c80e83c030100304c0510840002c0c82c809040302081c440f092140d03003510707502400743c0000948680c0c05049600c400c003080c0010b000c010680203050500700b210500c40e1280c001109401d89030000c1c80031508100e2824401e525421100d081c0800e030041c15a01d48800d01042010b0b8000c510982c00c86000a0442400804641040c007142c040b03074004240c240b02562098211005050000b000149001005002001d070a40c00e40c2c09100030810200c20001d4078505400310114604040d00244419030500000a16080b000303d12120000140400c1c260075902c20001308014080c3c0074010103580b42c40b00b481407110f682c01c0318201d0016900f0b112201d018030405852241a2a01c0c844c00c0307054906121a050442d0300e070b601107000884110100142c49060240d2503001010161201808404142041388020742d009000070240300b0100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 662155359 1250 662154109 662154121
    0x1a01020c0618180916090912030e071806060221030f0a020d0f090203010e1606050903010e100c0f050c03030703020d0e01050a02191b03050304081201080c0109050306 73
    0x40485000900c0340800c0c03040400242e0000c1c140900039514105080c2a103010402e11200009000f50b00d068001d4030706003a0743c1d45540510555070b104100070001c0b100e96000c41c0c001e80c002d1300000419a4060300392b0707880d19241c40306640b044508030b101d11880743c0c403140c0411070550180328212500d00b0a984544200406411002042c40017070308601c101040003000900307504c107613411389460401c419001c0c0b125042c100c0760600030f0251803000341d100303502c2d00c480040c52540c0010605030709410414030782565440e2010a803003e41000b221560155200da5900e1001d00c2c01b40249070460600380340005080500302c034020609140c8200c40010700100f00b100c84030401c400010f5a0303219406240142c0d983e505c0100500c040c2c65145170000d81c1d58200070a000d502d005503000b0341900b00c800c40150a5201104000b02c90740c4000c950029074107070184402c0004284104000c0d980b05014182d42c40c0740120140c1c0c0c44e240c41c942684040120340024004056641e4440f43c441c000b09012402429641450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 662156609 1250 662155359 662155369
    0x90c03041113090b0f01170a020907051324140f0a09051f120207020901092304050c0118050303160501150e0108060108010507120203070306181a01020c 67
    0x604041d20107480440c03141026510041c03076503a01c003070b005024810b0014628104044200c00d4541800b290701c0000049410307014135075049102e80440c030042c9074001c015001c9c407110300809070030001040001c0105925411800e10910020000c000c000070352460703940010366010349009410010000e410300500e219245280c2560250040f8185196843c0a80ca1080d18079800c90750080d03402106c545029a22110170700100700c040c880689420f101242c6107030740b80c801c9201d0480000d51100e8500c0040c801c0c1500381c0d0002c51300060680b132003540c03210403d1080c1c0c01002c0c200c90440341540608034001c01540c0c04240e144180c0780700e258116100782400c2c00640caa000d103040d0f2a204042444c1c1110a004094101d2118020310502001c001510380d102d40352210000d0007a544075125140c00050010014401c0c0b40c8254002d40d0f40140c2006151003606c00b80d440074105101305900c5030340110760302580b040c003881c4041c0010000240041c03030007061100c4800080d4060706540182c00811031544039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 662157859 1250 662156609 662156611
    0xc080607050325021005091e0c01090308030a020906040b0a2d0f03060b041214060c0901110c040f020304140a2310110705100603020d23060403030515090c03 69
    0x500b240003000c64840201285490b582c02c22410045d424401801000701001c6081c210025a00324580020108000341640e92030070000384900041d200901000880c0215020b190000c03e03000005d0710b840e030200f00060176500203400030a010b000000c1c1e0a00401d40003c5001082c0000610404154070340c07000308054000310803030140620200c0c10084009034800d42c48003015040d42c1111a0301c5a44990140c00c6501074580304540c0d16261100c0e2218540000640a2180f10825002e604d80000c4500469420301c61070317207081c1280701c1e5010340d807007541d0b4a00400c00340d03545c2e40b9001a1a803415040c11107c0380d068480301541900b0000000300407a02548103002c1e03215a0f100c170f201041c1c401c004d002d0301d00445010080d943d00e2424040300540b444540040101c14065011540d4143c02640341e20221270152200075400b800580d503440000300482102d0100100300c0240507600062442020304040046404900103980d800c10031904440603c1810701542041c2c50305449450310300960a25844 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 662159109 1250 662157859 662157901
    0x140607060902030f0a050c0f090c09040b01051902030307030f180b06030c030109050d0305011d160306152d140c07080703142a12030904090c0806070503 67
    0x144807040401903403003c0019414100b0841c048828000c4c8130f06001c0c1e1200c40b605100b9200b81064840000b00d841c0880c1c0540c05003054110051900729074104000040104180c1107041c4017080c00b150120801054041044910540180d952440e0181d00202252040114842da892801c4400000000c0a045042e59075070721012100381c5480d00e000280c58a1100c034100c95042d030a02c5418410000080380c9114800550340301030080c1d981740d140100042c103404105120003100640050011f410041005161020605000888039211000510801d042000c484080ba04008181e0300c0100c036003d010138405140d054407080d082010748001d101c1c0003120300d081701814021031030700c001420030f10080000709640002c85402079921f241c09215044440381c00b03161405060329150308000d182e0020b1074a14003105442ea50060890200b2520301d8101840001c03500c018806254182c440344203100d1203038051002007d04501d8580d01c680780640c001c01b141d01f00b18051042c0040190383d8204208a0a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 662160359 1250 662159109 662159111
    0x806010e0616060b0f01030506010c080d06090e012c19080c031c050a0b09010e04060605131401050402071a04111804031e050301060f0c0c03140714060706 68
    0x6a00e42001076460300980a60b200d210105868100812496510a4038203503019074181124002d04401501100c4c0211101c9011440405107900081e000c10000c001131001e40b80c00081141c0c03107a107520220307004001d440d18a0781d561040e0a95401000c81040441a04040861821419920980c0c1c4800ba00c000503a200c040840500d0108105030080e074046074014000c0380d07160340742c10481d120746025003c8182c924603d0305000c90262080e078020706c009582c0103002c2d011107919000c0700c1203158200030320584056580b00c6c0041000e65a2000400416455100104070312440d00b03409202c041042e40014420b81c410040000004e0000a03c2c0701e404004180d181269504e070b0400240c8010300c924842c0e802902c24480b12040c1700c0c62060240a18025a189040001d0b81c5040c0320a070a0250b1110000c0b800600041000380c0c815034236851322516602d0103032158103440c2c1d980c406c80720098004a85401003014400890310080203404000e2115500900003204240d02140c914420718101415035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 662161609 1250 662160359 662160377
    0x50f0f190207170307091805061503060102010b09010605091e030d050a2109152a03150306020c0c19060f0903201f0512040c03150e010c0f080601 64
    0x2002084841519090040010303a9492034040345c0101403100ea030068502c0c6400e030300c0c1100901d0400384074241c41001e01401e1849514500d401c0ea40c00d07500b00800c81e80c1150340301e2407100720071344401d065507000f0621521a130707858800100030030004110002007a11103400d03104030f040042c0d0b0000303a110101c1590b4206280d1301c1501e55030855401031600d0504400d044040d414228510003540940c0840340038200300000d604a0010f1101540c1c0740d000ea084e504015580840d0001c005400d100740507081c20300b00000c0c50b0703285901100500c00c0c00d51056441503404130711018842000e000c080a011000c0710b03103408070165543c0081610880d402000108106000c1e03154002c0e006400c2c4c10301454020b041d10f11400b10f240d440915001d82600c3c018064040020340c0000b129030012900384214068403a68203001941000c403018a0740204166009860348600201258100c02c0c8001d02807244000818002c0c3c966003403a081d00c1c00740d030050040201465808011645c0070b10000d40016003481c001c542 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 662162859 1250 662161609 662161613
    0xf0207050d060219020303010303140a0806090603010609092102012703030b150a0f03020315041109060c0a050c06120118060315063f050f0a06050f0f190207 69
    0x24001c3c036828544d040841240c08924a40000c06503040b00c4c0701e40e5a400c04020418495029402020301040110309144003144442c0340503100c0603071240b00540001402070b035a00e003c2081ea40101c000743c808900081694221107019080207000d0701040c0000c4c000100b5001040074010b078464010b010711621a010f0004040c4a078001901c0c0c80381c014001455400800700784070b0300b41d102030200c03030100f5540460310501d41c5c001d0003903900c0b815908142c1e40d41c48603103000340000341008e80c5507403504040400407803032180d480001400403803140d0740040042040928040b4a03180300640280d1040740f06004000f101d00200707031010b06581000c0d0b44000740c00d018442d2103002d040960030041c201146100142d5802c0600c3d0300503011202d0020800b90f00d0b00c5c580b2220008400201d0441c0c42003204008050b03082480c1d42c00c040d581c3e6220707034200e81604080b00c1195041001501046920a403510300303000c00046651040c941000d442e1101020a08040c9982091001d48081000e8455000314404003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 662164109 1250 662162859 662162861
    0x6010e130609110405010f0f36030305120108190602300a0c0504150807051201030b0f0703050f160210090515010b0711150d020c01090302010c0f0207050d06 69
    0x1004000b0360509200700602204500710640050261600142d03004440042d881e10032a20340d1080502030311410200711000c03590600c410012101c0e9061090702c129001c0680810015900081d40203995941c1ca40720081c05460340c80c1c0781070348100c40030b41c000d402e017440341f44030320113940207540d805400144d44801c0b00c20402e100d03881040303691099501c3c2c505400c005551003040c0500c100c1c101d503000c024000000b9002d8400707020350b0080e0072580e83c0180d0140c1d00c003401135500030780107403942c104503050980c40d66001031540000d80044941c501103405010764103096141e40d07500320740c4500341400145030110308406100d4000304541c544162050390030707001900034040c520051182900501c04024241019a82c402600c09140001c55048000142e504280000d80711781681c80b8141640d0030300c8005c208010300d0b9901e4103e41c14030004010110400c121480246070344148400003280c1a0442c5c2000b034210f8801d841100c062148c100000601c0b6980459500246e40c012030750203600101c541070007c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 662165359 1250 662164109 662164121
    0x1110d2003030a0903030b2b060219030213050a0617040309090c0201050108121c0506032d010b190902070602070519140a0804050105071a070c11060306010e13 70
    0xa80c078040081400614099074028001c1e0034041d071018017420351513005120310584803056041d944554100088403200038500c01c094980d000342000341c104015228405d84041e4281d100002280e80011a0401041e292115000524040750b184034130034680b4201030107600aa0500e080d10b00b407140300080030035004042c12005070003698030800505035200d401900071718080c050a0240d202d22016058003200b10303021a4081c1c0c4807990386040f4401d450140502611002d0003113603140c050015030801808511400381c1310098044640c0054041c4020040c3c21241c214841500601881d120790404144894007130048803110f442c0140e4507a810b0805c1c20090007404d5000b8403a008948411200311480d81010a0043c024000000707150240d08000d40d842c40d481360001c0c0031181c00d110030092036004201404030389000300704801c401640074404640c3c50310100c4100e400302d00d00b100310303605001e260381d0348581520080d144140386090120001c0e02002100301c005100391a480c4682280102d0b81e0004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 662166609 1250 662165359 662165417
    0x9060f1d0a0e0a0618020426150f0a0c0305270c0d0c0e0112020a212f0a080303060d14010e030304030e0105070b0402012609030901030b01110d 63
    0x45206818100b03800e1024085611480c0300417545941d284161070441c0c42280c0495801d150310080b810640e000d8090110354444d0442428011030f01400f03c1c01b04025441031041c240d10180144e03d00d8040700030001ca035014400300080610303210030840c1e55040100c40000000a10104d46c0c080200366145501c1c184183c04800d4010701d090001c10104030a003d0004141c8080601c40c048582c0c9500f94101c810480c6a4041d600c031f0840801003080405002e00c0d60300c1a59010702c00b203207003160341d165149402a80510301c007400c1c54000c8802d0402c0010300900e00140340c00c80d0300891062400034455500c2c000a8400c0380b2070f039a80d00403a001c1040c1003a002c5c01c00f442d030303030024842040c0e050f485a1b12a041103909070085215080e050f855580b14400b181c030040d6024400c109280c503035400440c0c11200820350b404003585890450390b0320340160040b00d48904c00000c001c550341c02d6440300040c02d07a92440400b0307060011300354185407800c8c4045070b504900403017460228558118400d200e03c030602c0207042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 662167859 1250 662166609 662166629
    0xf09060804153303120c0308060405063006060a03030215091c03020a02150910050408090414043c062003060127060c020a030611030709060f1d0a 64
    0x32800f0450743d070312950012a4012542d204500c00c070703000252140702d80e060004002031044000a40103240550220342c101101071b10300700301c5000c0020f07a074441c0381014481041035101d030300c00c000458108001881c2e008106070b80350302600f491950042e5440540030046400301c922003001a4044804000041030480c07400f1494440b0500211302600942c4427215040040c000c103500c0c050301402e604481809100c1c064020300e200100902104c00401002d00b088500210401c951000c079543c50160303600442030710040c0c50301c0d03040900d018103103058126107140500b0b50105813a105000240b030120307036094404400c456440ea0034078000c00149400c1ca030540300344081d00c0d459500c072400301c4050341c03190b070081e00c07070b000d0511480130000c1700d0016000d54505204d00921081c4040c3d4031590b10100301038800780120441603141d075944070a03203c50b440c401549400100800242c1e55110784006c0060030542807040003040a41401070086e4000101c80c0000c03042e5040c9034400e03031581c003201c200030031000311 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 662169109 1250 662167859 662167931
    0x1f02160807081201060503070504030b09010b060c0106050307080d0c260301030b0a050a0e121b01061203080c091e1207090203010504060b09090a0504021c030f0906080415 75
    0x42c02c0c01c0741e83c029203c80007000c5140303400030500074003070000c5034080e040b180c60707050801c1e01d03564601100d0000101180129501ca80b000040c030740324200035123000d0400704004070f80207052005042c6401a1580a01482c0e0f014a102c2c1c1d003000e8110188070401034101070340150502603008520310b01c010741ca0903002503160020001013400001c0b44002e0050740b010b14180b203140c80d0b1400c20000d40717641801b2811150464090b0108503940c640050235910034150f2144c00110105014a003180d040c2e03449078150101c201c4d6441c04066220b0040c60b4080002049176040c5104180400c8010a00912959034400c0c5000720200700d46c1c981680718a051003007400c0724003664480b841c803c0070350000c0c4517080c015400c2010220749698400705684290390060590030055580e00390080c05898007400580e00804580000c5010781e071980c0b084240780b4001d072030300031240300344007001001f1545583c000d5080000000500c40020000034000d03913000c6000e1008104d03445030340021341c19540d02c4a00c0d052304082c560 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 662170359 1250 662169109 662169113
    0xa02090f06031e0c09010e04020a0e1b0c010204030c120b0a0f0207020316321e030a0c0302011202071101031113060c0b09150117011b050702030d021f02160807 70
    0x1c4070750005809660100e5566a82e2004a03d00d036015500254041cac011502840702a10311040301390320a034241c260300c6548880140c0c3c0043c0340c0c40503920150b240d40009060051040c49172005c1c1c001e004807040c0d5200410380d0b480d500940880030748480751450f140c089082140c46070b501585c0603d0b40050a4a00720703140e0100d40c0010701898070a44001041d061700e655580c0c0720484200d4031440309a560b51421458030b0003004440780c802c070100c12000210800c500150f46042100740980c0c2c0c40390441e101d80c0d50560001521442d41c2c0401c2100085c010010388001070b0f0000a0101415020708000c2141011040560b4660084198081e02d40300c1104000600a42c4004040d864900400386800e0a0311030b1400c9603120741c0782030071242414640303400401080c030760200c40110080c0568000035442890083c0085141d5004c1130080c0010030100b4003400b035280030b10100403012035070700003040031842e000080214031a01059151003d640070500803101c801d000f110b101103c1e4041c40322556000b0318 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 662171609 1250 662170359 662170363
    0xc10060e06090a27080d06030305120907210f060f060303121803050a050c01050106031a030a15022505030c0d030e0304030602070809030708031b0a02090f06031e 71
    0x8841d410b10600c00301021542c2d10701c29200342e000048061098420201c180f0300c0801c0c440700452012100e42404004407000803e2600c9900040c502c40c0d50346a59481040c40601d1090401401980b5180c1042c8010030240c10081214100240c400601e05100601c6090200900707510300d03030180800b030501809401b0140a0780c42030040d2440303a2a1a01c1140e415150321040750803e0001c15040040c0405020100e4061405061070b41a246001d51420315040c1d07500e400c1d514203034841c00121751100c10075004010303c000050329180d000d41c0144494541901c070380705600c5640c4122142c295001801a264860b8503500d000c075001c130402c418210580501c2d00130303580d42c4140400078240c0039071160540414800c0c00390400c041c620100850601d0f0642d111040251303c109400c070f031840020081260380c1e840034810f4100414000f8017031601c402461107242c40c03031991404842e4054010001c810016a80d00341d01e0307504900c4190058815130749140c04a03141c41d0581c296214000102c00c114240c0d4000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 662172859 1250 662171609 662171611
    0x418030210062102120a050313030314030f0c09040b0603040f0c080a03050405010e01090302210106060509131a03031b0c01080609040b091608060a050615040b0c10060e 74
    0x458107080003050f80c1d900d00302d00b080d440c115001006114980b5140f0140c6030001d13200c03030201d1710001515681c2c00c4a1395490710b164022340c84042841100740e810424142c20070b1103075518044150b0440c5c47d52820648042081c070b0300030040c29042501240e2043c15440f01c2e403041040308805801a540da040c10705000e06070b4000348400302c030402210240403400d00008640b001440340d050701d9072801c0074104801522a03202c40d038180e9041015610001016030740301088030754642441c0300159600035581c3c030281c1c2550050b030800d20511400b0080e01c2420749030111650f000d0001c40b480000c0d0308240c1a41031b01050081c800310355042c4400b2071100404880038050f480c0d812200000c0303030702088414006594840040311a41c2d80017a0705000a400324040c400038651041c2c1070815509507505500602511103099004042c2c2c0ba0300060400002c042144107441e0019030454040008040741d21038000c0c644203900810f0291400403030034402c2205c0801c00b040c641d007100e400910850303807a01445c0e140b07a14 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 662174109 1250 662172859 662172883
    0x6060e0307060504050108070507020f0603010605071a0907381903110d2307020c01030f051506072f010e040605010e0d020d02180103030207080d0206041104180302 72
    0x740384400030786107018070212400c0b41c0d03042c0c40303820721035940600c140d405401040d4203070781002500c40002c10564810000b10301030003442d20b5543c1c40f40c000e820803107980c580c02074a8441e07840c201c03401e01c10391280015441040725040a070000081551084080d0000704502c0300c0c101c81c042015411040b03044030303801317856042400389070303060f403405207030b604030151820129010300481c81000300d03020710300540d000b880c1000c28035030600c0e003004226544001d6a0704201c80a10058004500c010040e603810b00a1840c00c54211106200c0c5042c20b800300d0740382c2d07102c0400031032044800003459410004440d8880481035080e01e55000f0950717401c2d08449080c18007000c9140040c420030b04134444c5207000d03c61113095940c1a541c00d0070340d030030700c005000010391105016684545107050510060b5600c0000b048940200854104154558a00a460304e01550030211050f0807911501c00050f600003000c1d58403d42100c00540100c82540c003081c0204a13050780d19000a0042168106060b000900b40300805 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 662175359 1250 662174109 662174113
    0xa03060903020f06190b0105070f0305040915180903090807030302060f0703140705090a05090103080904050c0c0d030b040e0a0c030c0f24020c0d060e0118020f09040309050406060e03 80
    0x20303070f40300150b03403a01030031141000c3c060018281900c244580c0d80c418110703414181495441c01491351a480c405060f0260102c000a60018007402564a0b500a0040e41b40104920799061420180f0380070788000d5501560000c0d03652200e540050510800800c001000790f0740c00e6a8a29440c1c1c00d00a444000480d600c0501c44200c0c40400c400c035101e84a8800b20300784041d6528170540b150b44080700c81d580b01c8025a40d10188002c4007180c544e071000c0c00d06000714401c00080d644c4a00310380a10040d500d004000c5040c89a0600800d07882e054081410059500c803450005600d1900b50f0005d4020484464400128815801d405041011484490301600c0c0600c00c0700c0180382e44d5941220b030013552401681e200c1c02201c0070582281c45c400e05c91011942c12030050701c1c10320504401207005462410030a8410035240c4444480c990030030b00c5901c45481501141d90707000340d03564000c0782c0c0000c040304a10b4095100040001c0038140716135001c01c00b0b408018414003034561349400080c242000740041078071074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 662176609 1250 662175359 662175373
    0x1103090d080f370f0501030606060503010e0a021e0307052a07030f050c090403090e0c0307090b0a03092f060901021c03020f0406030f0b0f031e0c0a0306090302 70
    0xe4550180786074469401460218039280c121001100d03522029003200300c2420488680d0001c0007034134090582c0c076280a1000140961442c01c0000a45860768040c030305000d001c000601c0804000342019030b1101c0300e110702580c1c800d1501040400e10800f9280984d03080b80100034000040d078040010451f130304800384425480d1226850403101498140e41040c1182e04c5001c003000040c807030364054000175002d0401d603440841c070b14000c14005e04040305c0440006030100c405004c5404a00341305608504d114070800d0461030801c6014000410754010001b00040101d1030102e47c0b8400d8011300201640718086a040060200f21043d03a5140405d0029001402c60161100d9041c003500342c842a1905038010b000f080041000c611010031000248170402d6003c000007000c030f00c0814010001040281d50000b20703d07060341480f000321841c42c0c0d00f8600c5612a820711001540d40041c501d40040403c895007000740d07424806d201e01d0260340106583e00102c40c0203001040c0142ca40c40403051a000781c09840311 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 662177859 1250 662176609 662176621
    0x703120506042a020c0901060f0908010216140a0c261f05180f030d060509061305220507030302060906070203120402060c030315040c020703030207090f1103090d08 72
    0xd031002c0240d44083c2d240c507561011160043c0841c1000c2d00c44590054900076080f0740081210020240c00041c00320300030651025459030304c070b000c2078002c041901c000c40c2030001c101000e49401c2107080d40502007040b4481304c40740681050142c00a41c503407207090b42d40c003d80c5e60185541c02b00c5141c486442d004203030f0b00901c11540b00114414280d0820f15103004181c40e21220381d2001028040d040c02c203031104c1c103207001c1c0d9046c5003000071100c8540d09030001d40c1c42d002c4009007001a11700c42e0700458064501070b800d001e402d8039950300c03007132032240b000340e012544d5607445450f400507140f008014034a200e1140c2c500c00500002150f00400e8074001d03400d5810641e01c1a94031039903500c058442c44010391040000300c46070501d5010080c0c0062000b031049161000803104540f66800a4071003040701d05103160782d036001e0714080c0314401681005002500260340303540c1b400303500d414291180c03d01d21911015903408002841d8820512000d8124829840741062108503503100c0300d80f014040480c1c00e41c2c0100701c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 662179109 1250 662177859 662177861
    0x1605070b0705070909060b15030603191101081503010926250f06050f070807020f0d080c04210302060a060b0d020c0a080309160f030302030909040512070312050604 72
    0x1c11600200102201c5280410000c02020055030640d80a9620101d0b80c2441e921085030316038290030407101c83c1e220b05051042609194001d040f102c418440203a51b080011020007941c400d410b002d0822040554802101080e02012064555819481c01c0314110400020034226681d9400380c0c21040054464545403c140303109080b044c042c00850094108400c948070384a00341034520941e09000d03c600c0701c0d43c0f00307000c0d6042a164043d03c00c2c03178402040711460344500046d50002d02d51009149011044d0030040e06c91400a004104001800d40002c1ca41c4c00184103ca000342a01054800e50300035640700d0780b0030114512030450050103074902051180c030305402410b007941c165020017840d1038040c0a50b5802948281d0312021a40901303820000801c0485000d1031003032250001a009034504440318101491050b0017250407803154440c2840813131b50020030b80d94016030556080e070441c1c032142481841c000c540c14000303003000340c005462820907602140c50319000054640501107501d43c801000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 662180359 1250 662179109 662179117
    0x30501062c010b070206070c0b13241d010c0f0b16050f310f0503010b18040f03140d0c030c03021608160204060b07021f09030f14031605070b 62
    0xc900c1c0d090195102506d0400024045980b0404c424900c20341d5036030a06940f40c12541d0a1600e1a9074000108070303c0340c0b518180030b028640f980c0841501c803001d201c042d0104140c0c0c65900c1c031a0f0001e54040701c141e405000ca035183c0c150000000341c0e0707442e814070b410781204400316541ca5200c001e20307850803003d90048040e05d546c02581e180880c01c00c56501c00b125a081211041026034503001000d40c6205d4130940d40c210b010f455190205109140bd1000741070130744007200002809490012411900b800002e600180c016038456040250700d0300c1c50034219040084134079000c6081c60005601c1c108110564816202e04005031810f02c4405a501c000f80c04a0180701410a90310540e841e000c4001100c40c401010426050802c0c1c03c064160f9401190480310f0035007001c030640e100000c0305025894030100c0c4000c1e045900b00403016a20b403026004040d90464800103100a80c0800100104411010788580c00c100100450392030700c01e011a030841c01e1110703020990b120b001e9940c0201c0c290401e08111 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 662181609 1250 662180359 662180369
    0xf1902150703020a090b0703030e0606010e09060d05030f0d060503011803051206150a05030405061b070f08071a040c0609080d080903040e07121103150103090606030501062c01 77
    0x445654a0600b42e01035442690401c082026500340800d44411000c042c0c0509070083d500044d14034003440c4118600480980303040d040c04440484044079030f90350800c00c0e6011000b5113445907a00765a180c51441c50040d00034079800c900001c14013200501311544a8421070b41e00310000c1c0006054080d02074561100c0300c402030000f03401007001d10941f00603502c0c001d40103207010b4405901030040c038002208980003404800d000800010910040c00020440c07d5000210303070791000c0c0031158280040413207103d01a0300800540d10100c00009000460065410442d0007290310312948410b038070390040400086600b1140341c0300e0b82c0d10229519100d114020300341c8014500074414403a501c4410b64881c0c100601c1c1c00e403a440f08120225403034152441c00c03800b270150b584a5001c1081201c072038400340e4014100d070b08000300080c810080519007000c0490f20607002070a000070380988906150000e48035030381016100e036007443e0002400b10500c0343d905d09441e602c410b403841001180c80402c0f040f40c5080c452 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 662182859 1250 662181609 662181643
    0x40e040c060804020d0b10050a120308010b03011d0408090603040f021e0108011202030705031b100201090308060411120906010501020d02010626100509030405040f020901020d20030f1902 82
    0x41500081b00107005a42014208503603000c0241d841001460296281d0081641249160306e41d10070160040300e804c1c0504205c01604e8195030401c8132100038075822820400c98100820081000c0c00602d030103d032800940504026641d15041c10000c10990710070800720300405448851032000c1a4801c0b0213118088140c1d0b5a4156920340507100b655000b10540599150103a0103002450340d600b0003007409171022040b8800c00206508042100740e02d42c4034840420b6905000b20680065404412980d10074400c660000c1c000b240045c01c0038081c01160080c80c40b0090b520140701d880d450018480d4102c0b0426070031581d800721001d104a09903009803241008418024500c0e5207030105e01c1808001c410407141c125401840281070302c4050300c01c1034030b003160240c00014040c01036003804d001d820103038184c2e118207501c0d101e40c00c00000c1d138078a1007901701001c1050038030344200e0480c0c3c3d42030001c01c4803402c1000c481d2541c141f100e8403903040c0d008070718204241700340d0010340c15014008910ba0420041d6004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 662184109 1250 662182859 662182879
    0x41d0129010e0906041a04020d091704080d0f0306270507030213092a0f021504200102010609060f0e150a09020a0e12060f0a020c03090f03030c03040e040c06080402 72
    0x51001034150150500820b80f40821b071001c00c1e8540e44080e120481840c0404605003100b07003400e0f0803000010b80034450300501000300307104561000451018140c03651606c410600301c0c00004600800650f001500040704440a00c071700702a55205044500307010319070400c03a988071683c00768124403c921045010f1401c11504000701c001179444400bc8501001c584216101d600c80f0700b200c1078000c0201c00f00800d040f50307040f1619035410003000d0300c044035448031050780703080c10748501220440c00b08644041200c44c0c00710a0040c0d1003034200708010014140c0c140300683d201c0c804003c400c0250f010709104070610500064683c4104040310070000c4014007540e041074180b0100c0e4000e50b02a6101000b0f02c6202e183c2500181c07550215416000b110f60064282ea0030030b032007a501c1e80c020241001d0392041c014000c5501d09070011049074a52130044038401e110f2002400481e0650081c09800001408081000035006241d003140c40c2c03046110300350341480070b52a03c0d41651007280c151006900050050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 662185359 1250 662184109 662184121
    0x1602010305100f08031b06130615030204020a0203040812070b01050d1103030f0c0d020601062a0c080109020312040b04050d390509010e06041d0129010e09 68
    0xe07009903000300301c03000c080c800b030343d140c51901510901c0c6502042030340d400024056100e4810311507403401d40210b4006402c00f8203080d0003000b150840d00d07001910044d80c641019101405d2a1400300095034094019901c8402007403000c0e450390010b01c205012802056280c281c01000e0100b114051648040c12a080ea4200780a01a01003034a1408888032042c100da010030301c1d42c042018101c55940003440c141d50303c00c41940300d824502c2950104083d5480403005115043d0803030543c40012804038050282800c224001c03050351104113101901204444a01017904038064210344c004c035000b0345c01c9945109a00014040780d00c02d0b4860b0320011385040c402032146203003107990b01086900480c2000120980c2031404520b0074080304540d02541c0008070301c034030720100c3c50521900030f04c01242c1c81619585441c01d604000c3c40006d0110b44116962880d000c0000c1001c807440000c84242c800802100283e070305120042c804060b2500d11992a02002422a40c4100100a0520300260005a8940b210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 662186609 1250 662185359 662185361
    0x6101d13120c08070c14041e020a0210051611070e070c02060d1503020f1512090f0d0e03070b0a020d0e1f0507020f0402030402060304030c0c030b07020d02060c16020103 74
    0x2881d88030007045078220340880402c03480c0020300400c0e03005100c1c540700d031441c109400132041d254412140c051400c205c0b2035080c0784404001002d40348011940980d0701c0442c920308034240480442d0702c1584a18027402c6c415680e004941e180d206813103680b81c00d503880700025081a92001984580c8194a050b00005020984a10b06500750b451020b0402c2c2d082400c204040016502c140404084c1403c100504209519144a4a81c0703011401e072012601416404210040c3c0d2051010005058030000c02203140040100720106203000f041c03066401c0c01d03480d1744004203d580c403002031038405d112b04c403c007003a17849200d8122400d8000359001400f10181f1410709a64048240c04540e90000364a9582e03a02d051100f403442c2d0b000d460965406641d518240b0400000380f802411280c0118410304c20000143c070751000320f03030f00240c15007400c03a80c0310318074a04028100c065400040009102c0014031500940010702e01412480f03640a584465031501c020b501280110903820070121898000341002d9400b0b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 662187859 1250 662186609 662186633
    0x30902090726010305150c0901051206060d020715050c03010e04120c0507060908010e060106020a20030a14060f0610030e07050301061217130b030c0c06101d13 70
    0x140b40070090102e4856503104201c240d0080c2c44582241d502d80d0f0032088100903090f8410040706410f410403200c0c4000910501555040c08484681100402e0681d51a54107607103022102c140d056640c0c0c2d82900d44000c031400b01400280035942804045185194540240c905a6010900d4003001da9110384070342d86006e14040f00602441000407141303001c901e05000d04400b03050300d5214130003441e1605200600311003582068034800c0e0881c0c001405041e5001c501000b80c0354201825022070461803000550b4070082e00c6010b0b138184200d20b0818208000010b41725201c00e540000da8081b541c501840000c50b00301140d04c150b0102c503540c07111442d240607500856003c04117801721079a01d51103a02081c2129003a030030007052055101504410040200d58843c40c40c0c503090314850801800400d0070004649038096251021404070000300d490f0f50792010f890014200000b1031701e03c4e040441c5150580000d0f401510034129003040900452000581c81c14001c145100540c5404a0316490748038079403070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 662189109 1250 662187859 662187887
    0x15110f0304020d0c0905011e26030c0a2d0203070501110c04050103150c090e13060b03061806010b0a0507020f0301060e160e010305070e1909091b060309020907 70
    0x82010b031644040313548515964041e001e4038100080e44d50402c15480d9804008604c0a0904111404140600304508001c42e080c0d80200c00b6841548003544612411806040600c441611854000c00144400106204a050405d140015414898040e260440002e0410207905980f11400400c42548035030140740b014020901a61010340c00c007000941629001e038426030b0071942c0b802c00c00203400c8031b41c41140000f8101e0b040103982140f505041145000005254440d1107950303131860814410150000c409411008060f610706160400703225403401c501d4009080280725060003c0362082c1d084045500c20700442e200c1c41d05058681e17080010800440c48107d8055484290000d862a075042505005601c0300d05080c1c00a1603404004162a240b04111350416040c401800403e03070300b00000d40820b03107040c1d880c902100350310b80d100b00380110355074000d40c0c10524140b200d409000c0306010400016040d5002e00440790ba5680e0220305441746c3c2c440c003030352160190000c0342903203003d1849942108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 662190359 1250 662189109 662189119
    0x120d0f0302040f0303020109140303130b040c030804150905041a0f06040801020f071103060112020d1a15090108030306091f08100c02160e0c090102100c020a15110f030402 75
    0xa0703d840100c0c500360303500e510480150b919554860100060344680c008a01d030900011411454540c496141e00d10660740301408150303281010a09010140f81e1580140d80c101d88aaa51265505000c2c3ca28032109044500051445040810300d80341038000e030041c0f000365824601107103440404108441c4171101032030364422003c100003c2d2801c800c0c0060301c851408452030f2900d03140d85083c03c0403100b01d848492842030700110010b01080c2c40e032441c1180103d405485d0203a09060b14508214503140b180140c1e804886140b042101d0b0300d071aa803003e0040b02c02501c0c5140f8a0b66503002d0160341340429076400741d10403a0b103000142d00910314421000610501490040d07003030754a4564504101c01c0030845407456881da041c800106804010704414225801c0211884501e01103000310a800040c1000d03800150002e00070030300d83c0c420401c410707014451b030303404119402144a004c0e50302d00300303410f0455a240041c42c1c3d01031001224421112714180107a0001d240078895020030b00c940c2e0009108031303400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 662191609 1250 662190359 662190367
    0x70806190902150a1701050907050304110d120215090307110303120408091f210b03250e1302040902040f0207120318080403020904110909010b0f120d0f0302 69
    0x940d41d5081d040f0b050f001c1d0040d00b2a41c40e140032000401e2200b490801050b0700950f03400400c110707101c81000c280e100840d031424940320b81703403441c2c140e201c12030b80701c010391b84160810680400d1100f208200c8a000d021502200c2c008204030760070020340c81c4100c54004e1260014001400401c1c40000281400d8100030152884c0c6414041d90320b0300d00c0015182980c0000003c03420342042d08115943c8407641c103d4060105080004090041100c0002e56104109020b100540c501d81d42c1e41d90003001d56106c0081c00e5403020b404282d456806055103103640303014007950700360010304a0304190381240200004003e0b001001210340130f02c00602500c5400700d0b006540d03402c0000c0344200358800392081c18421072101100c900c81c014010180c81004128403040008401c101000501301c008a4049990540c2c0f40304250703889080c1144002c00c0d0903aa10b4000100704102300c80c4c0d060640c429091400102c0d40c0b010407940d0b4606000003d00c0090030403a840d4001040c05091901a400b20491202145009850 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 662192859 1250 662191609 662191613
    0x3090b0f0c1201060509100305090d111603030305090c0f030a08031b030a020a08060109050a17010207020301090b09011b0903060b0f12010c170405030301050d0f050105040f020f01020708061909 85
    0x1802d0b900f6032081002032030101d0000c90354540070b840d0760340d80606e5140030b01450510081c09030b02c4c0c0c4070b00300342d41c010b101b00005006018601405030b04082d0702c0021509800543d40c3c200980500412034400c0198010301003241c40501d49010b100c09582c202400400e000e4039951b690216991001d001080300382c04400c244004440ac6600071031144991080140e221810000040e114210140940e0b05004036443c007800703e9214060403008960210070000e003072400141c080e500a10401d00b0280d059424005c41e48207005034a88500d020341c12001c0200450800c40481c079145a5580f201000041c0456030200007051a80e00840d80410f0020040032174050b0403400109070206200001c1840e03511071400750314550300031310b40140100d012521207903542f5003981c526481c0d1005000b018490741c1e0b806112000d10001d00c0300301030807941c854000c001508141c1002501120b00761801c038403c50000034184035551001c1610030842e10380400920464645100c68102140019480c0d4070b4282c1c1c80081c600 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 662194109 1250 662192859 662192887
    0x70c08070633180b1507030915020c010f0807110d081603050610050307140408060a0c050910080702151f0812030a05270105090d03090b0f0c 62
    0x42188408440e5802842a0080310714003040d844450030042e0344040303010007400082103242c0b0803442c03180400003843e0354450b000810881c15a0540b00c181c043c0410700b401090340050014040c7c409a040107091918001e2080741c5d11000208018001810f0402c2a0703e110300407a03005820003c2820151800c10104181e00c0c40d11003a80340d0080091042000d101c00031401090702d0300c5840340340c03509000364a0000042a43d0702c0400a000382009000000901d100748900c0e9129510391503028001e40d1039580c0d220f4030b80d45050684109003818a084503a18895004404889a000300036201541910f1400029100c1c00c000800d940158012001100707280d0b0741c1030902c60703c510604010309858018180c040c4c01c8061480c3c011140075400787c2a1400400b00417000d07030380d0182800ea004501c50340d0f40082c0f042c140d05c007403006606240d210200d22002c00c2064106a101d154150211011704ca00d6080807025580922000380c0280c2d03441d070200d07001c0b10f041e2175225400043d0031900c924182030026014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 662195359 1250 662194109 662194121
    0x90204020a03050f06030c031c14070309241b03020717061605030c0f0306040b0a093c021b0303010f08070b0f030106030b0f040f0f060504050f070c080706 68
    0x1e40040d030350b1420010325003108541544c00100c00e4000340f102d1503000011030395840340a81030482a203004007614042da489040e20f00c8610464242d52615500c40d454042d1080e20a80912a00035111031244c910081d188a0a20210034543d41d5000945001c00708640c80b00c0b5401d90141e045018041010905407101d10701d081400f041071001f40030604e0608001b1482505c2240084100641042440003803135812040c0c6448414a034401c40e642c0d12440300240040154000680d08071103544000a52004540c1c0f0140c0c554404036508424004003000030400f0320000c4019501030720040d20396030200e03016a4041c00200002001c4d80280d00482401c903403540d0405d030310038408509803000521103442d043c080140105100200300d401c0c1040d1862000541c00140145020035a907014042e50341c1da00c000905000d000060402c000f0708054100d41c001511052854204d2142403600c0058107040500c600c5120b071124010241c01519221402c0700c0d1820034502c184c0d0396480c244507070320200708148284 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 662196609 1250 662195359 662195377
    0x60604050f04090230010603120f0207120f0b06010e100c051005011e080c01020d08060d1202060108160308070803040201050c06010b070b060108090705060310080304080c010908071d060409020402 86
    0x1e6170000021200f1a0440c5095800c100c03460341001c40030000658598801e0701681401c4c10002c403110800310080785440700320761004c4c0b0100c00500080c01030000000b02c0c42403c0780501c00040c080c0d911040191903807003070080d026802010381c0440744c602c03d120754410f035142c9100780c06a92800340c2075602c140640780203070000c8210101d4500f5001001d15100000c400902e1240302410380303e90362000103900c0b02c3c0e8410b460418040b02d440019059030314921100c0050394401000d0b0f51000010740025540e080034002d5020b02e2040504004a0300e000c0c0342d0300c0b4204e85d0320001d0b86140c40241c0d42c0b00c1780d40740c0005e0300c100d050200910003406012014042a800790040203405511354400303003026201c4000141100c4c6c1800320741001d2020008000c21340b001500c105541440e540d440d040701c40e600c03040c40c4e035000c4110f038040131502007491203002c21101d103802c0090780e07011055070b00d0f41d44075500d808a6224403081c4002c20410000c840c01c0c0c101c02154056002040000d0b031640c80e401060513640301b482e80c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 662197859 1250 662196609 662196649
    0xb090c0918040b0a091406090d0311120c0f041710051b03070c0302161e0602011e0506030c0907080a060e150f03160602160806060604050f040902 64
    0x2454400d0800c8903050007000d28800ca200c040d0b0030662600c0c680c100c0c0140a0409440d100d004c105c040c49002c04081c840b0b01d01d04c0c0304960040c50031100e8507448420380c03c3c0c544002400d00d500400000440303416141e071074520341400d120f00c5d202c11506a5003a40b050b4200700c0914410f03c0b001851620300c02c0b0300218046400c002d000c0104061882c41e0031135070000d00d40704090b0300540c003007800174000000f600e5105d000b900341000058040d00307050380381a6000b5043d0603603a407100d0b40802e407400c4144000d061001888000002107450310740513400d0751803c0c528407400b0410701c22050612441500120341005018050711000c0d481c00000c5448414111050300c0484d2000040c05100740701032054000030000b0b1011038106060441404c00b00082d003002d000e12481803559041c0c2c1d0f9075018450364a0151a80b584034081980c2e40c5800f94449540307058000e4842a030303410003e0314010100300e40341b00701c070b00a0026240509200c2041004000c030760829400a5407001c0341001615a1100380c1410b10790826 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 662199109 1250 662197859 662197867
    0x313050a121b03141c0204080d030e03030c121f0b0a021b061c0b190503120711010f020a061e0b04061401110f12030411100c060f0b090c 60
    0x10002e81100e41c4103800c02498000340c14010007280d4002c0304400c03000c103418886a0380d044032803201d24201c5030401450801910025001400d68400500c80e507000c509500d007804168504d1480d41d449000864000e460b01c00f00304503084a0305012400ba87d480300d0407000d500c0000c0e0003104804450a49904446940c003c0004d0341841d56404000360b1440200360b40070411118889408580e043c0101d825001e41040080c5940d400c6008541080b07079204005442818002403802c842d40c0c00360f01d03900c5042c0c0680100c0d0040c0301e858402d0411100d50a4000c91b41c024500c8010b40112501075003644600118000c0000c07050000f040b5028243c5110002c62184088800d040700d2941110403028909101d5482d00100b08614000c0b5030341042e10800c00d0a10401e9620002e42d401d0a121350480c9409031400303801c03c1d243e68110240e01460195028060600001c5003030740a002d0700c031804007181c0010521041a5100080305600600c070a5100c140b00032a40a5491010030a2150145d6801c1c07841d002c085 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 662200359 1250 662199109 662199143
    0x13270b04060608030316050c010209120703030315080c0105160b1305060703060609050f060708190e04090201020604060c1b24060f09180209150f01230313050a 70
    0x400340c2e00c003600181c00030703528504000d00c46200000980b642041404408950300440c41000c2d4192614010050414a4105042c2d410709450b403010703010860110746041610701c2c541a0003000541640c410074010000c1c00e0341c210040d6003075002180e8060581c51081c48002c0020740710300006028a02d0050751003020142032402d40d062200c001d0080c0b082502c1c04004000c003540c8001d07030300e045400546094002403d0500800c2c418800d03280003038a40b201c0001c0241201502d8000000040041d9032140071880000c0e0400041e108a030710064010390116010070013094807a07000d189058141c0c1000290076040c036010190460074400c0a4881c5412080701c0b5005000900c03002e582107081210400005040c0170500e01418001c0c020325040c960f80d28402610480b0a10000341950b4000301030038854035000c000100b520b60220044d60103201d5003c0c410703169500070301d00c0011000383d1501c40d54098031030b00001545500001c00c074611011135081c000300490424030803a64414015001c0e030038542a04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 662201609 1250 662200359 662200361
    0x423070f0503060a0915031b0602010c021219110609010207050c0418030503040302070308030a091101030908040b13030c0b0c0d0f140c0c040c120c02030913270b0406 73
    0x2000c0d08a0a100d002c00400a840d55407103000700c01e0303031790303448000072049404600710303040400981005012008030005542900c2c1c40e03006000440340740e98003d102e000507021040b40c99001079160217151101c1408000c0700c26112815a82585c4154030305041c0c0b031500c0c103c58500e019001c0d40c020500e030b50f0004c0d00b04203000c001e000152000100356405e008040b8a40c0004901c5c0c1c038254000f40c10070101001080400d07109000040044d0781100034a9160308100e81480c0c004d0240000403500c071440d10926641d15406801039129041d0041c400a09052410060074080c0d03120141c48038032110b96090200c001200c40c1640d4000e402c0c1481c29079110b90015a0240c9005500180b0106104034405070703805243e4805504031071084030010a50b10350010070701d014607181b9120141a0b00c6400d0400c0d020000c4e42c032414400707903010010428800300d06030b58420b03600d92141311910b40d00544007260030300c05280107400009011741600c96035201e0022003492001048442c0d10100c805903256420301c4144400703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 662202859 1250 662201609 662201627
    0x30801050f06032a070c060e010807110606130e1c030608030408070b0d020403061802040609020f1e04031b08100b030a0327120b0a0501081902042307 66
    0x70681d40249541010b06030000d008402c1c80c5100b1010f800450910450010101621000f980c41119a030390903417141f90145c46500c2942410740003445060000300194858048890030b43c00310350180900342c0342c15003400002e08000f070510300002c0e01c440c80c0c007100c84d03010000d9003080c800e00c000b014040340d03419000030203070780442d4030085556200b808180824080402c41e40111036503d44c03006c4d5606418046203010b80100c1c0d1019000d545000914419203509909520030342c0d208039800c00019480350541e034201d0190b2803070322454103801d10401e40e8a540440b0348d0490764205240107801c05a481d80e901a0032103820a40924138038098004004050081015455243c00c2070320501130031004001107556088181c5000d4100500490f4804106100308600c0387e041403582145000035445500c048000115007804a6088501c00d0001d0b80121180c42140e0588413250040d00703040c40044e030040c00300c001c20b81007603034025a05c080d081c0d0600096401d245125643c0e140840140c43d28810107001120 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 662204109 1250 662202859 662202889
    0x120c0c060405010f05030a09080307170a1a09040c0f1806062313051512060405040201021213091a310c090905070806031c1e02010f0903080105 63
    0x44207100c148a2030380c02c80c0391200707801350902d00551a580c0e001e2541000d002074200c041c060100003c10b000c60380750710618043c0c03200300702c24013030765640c8400300414211b4550301c0da0303030401230a807045003101c9152080d1000c1d0001d004002c0300501640790a42d07203655001661100080d484030040800140040b4003c04004000a0901c500d03046d042c0c0c0400304103541c050007500d0035100002040f400700d210302c1c0e0480014210290a00700c99001e18034011066900c449190b0300c84000b0f80c000600d041c6402e0182e00e21895047e4054807100112103880e0f1070a4005d0000880714180c07400e000b043d03010103481105c44448076081c560341040303104c04c02c0c06000304282110081550240300d00340f0030740c0036a10030100030142d036110020703140000300317000c0f91485034503000741c04a5800d000921185590100c80c0501804044003501c041c0c03000012034821081c5940c0b80c1c0000b180650741c041d405814213408003520440107000100e40403150014003004c85000b450200c01244960740148000d041c000c002818142c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 662205359 1250 662204109 662204119
    0x50d030c050903061515040e0c070501020705060a0507090e0108030a080712111911060103080c0c220e0f120a0903020d061d03070206161b031a060607030c020103051503120c0c 77
    0xb40c00d180c108c1c4a0038100500034040c0030000a8070900f005003d604443c2c20717640160540740d180c10300c0800600030b0042540c210001480602020603003030103507100300f4101c2e900074009620345501c058054032500001010042030005140c00100600b08a0103001039031010010819a00c6048008607003800409803980740030462070780c480700303011080014024103403034105400c9915140060307181c5244c407044003d0680c0020190080300c1081c0451801d00d104108418802d2000c0141d2814940e40c4242071180a070140c1d00c0903c0034840742c07c40e000103100d010500d03d0a142d000c0e0b280c0c4c01150403610603074000c8401d81d640741594000200540780403420b130f00441020314500f40458000400d603000b14052602d1800c0300e41480b01c1000f850781c02a480d81c0722442c034981c004031f81e28100140312002e0700c0e180c500c614820030001006850b2020440d08520751540342d07a403a0005680045008181c001c3c045070008003440c2c1001e00540e0200611814020740b20f80070b40e52203d14039000d60030410140907090240d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 662206609 1250 662205359 662205367
    0x30f0c1b0102042c0712020f04120c05060a02060c0c01060509070203090109061803291f0803030609040803100e1f0512150c090406060e0f0d050d030c050903061515 72
    0x90700c2583d90240c00081d0703861b00c1a41442e0365000e050080c451242c070041038441c006800103101400d90045405d05014126258445030b85000b80120361096401a45c01070f00000e00144c00d20a60001400d9024000c17030001030b00c2c40d140c1010030321002007030790305c0000f59001044070001507a000c0e400038082d00344d41c508440c1195440403101200700041c00010034081d01c05414074041400d060744410307045640d44c0880c002c1d0500d6660143c40c43c0c0d00a04600d500d899204000c1900b00300001120b0064101a2804130b041d039403511605410b401c0642240ca0750300004c0d00008400310000704141c01225408031612058180c0000e0307009224844d80b00c603020740506120322305c03070300c0b0301052901d8407580d900312202440d03907140718011040c4109907815034018a0040c3c00300d2600da000d400d03640d100000361407280d18941d180c0c0803c507142e22500c00c000c041c1d40c80a01c409200c94803075080044da6210900f02981804103103800241041c2e8100c0d006520514041024181850002421103420710559a15890 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 662207859 1250 662206609 662206679
    0xb0d0f0b0415051002010212040803010501080903090306040204020703050919090f1a0103150308040e04112d0109031a07080609090d030b0609190f051005030f0c1b010204 75
    0x8007075164418241304008212401089a001390101c5606820944450819103000d240907401c0e50404c0c001e0301e001501c174400040d030160000013214042d450040080445582d20b500704406580107020880400c1020f201e01007454072814030401d054415120240211410008854100c1d410603402c51800c600300300b10341400c603013105500e92084c8000e290118407403148d2103603006070300c1184d0b00007401e00700300080002d0300e03000030f84005010b00e20981401c060000c40d00104500e0320203031440000c61040e1030b209402614414490b444440106050000c009030fa2a200d01d00c608000e40030384000b403000e2604200c40e039a40001600c0d40844122a134010504004109030398884031890658145aa52000341c4440d80c1d031030b000c2c1c0300c1c420310040610030030429080e11541912580d101f891210701c2d00718008038007032402d03200680300b18015544440c2940d03211862100d1440e8060511101c110301004120301c2200c20342080103251000b403002503a00e40c0380915807071300100e4005da6204c03000005005a52 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 662209109 1250 662207859 662207891
    0x30c021b06090d0c031a0f0103051c18080102070b0709420c110306010b0a200111180f15030a1407020c030c09070203030106050a090b0d0f0b04 63
    0x320315002030362034035107800000c00441c540e03405400d405441d401c0e050b0800020003a0700d202c0a10f5a61a405400e021381d12a420704402400003030000501c181c0040f004542d000b18191001c48035451a0300e4904143c3c6d81c440b0f84030044403119008200d00e65000224030003444468003c00f504407131180b414802d2a450901c1024030300d08200c1500c0c1c00e0b000c0703945641d024010301d10110041040301d140c104c03402c0035041c10058852104140106c0d80e4103444420f1740c0f02446d020502c64102e03900c40d102c60b854000031078070441d84581c4002c003160070424000001200e0b114240b19003c0a544103410b89550f8000e05040e0705c0841c4594021207200d00750380c0f0900581fa40f04d43c1c0c1428049940c80c0c1100e6125154108004041c120341f070215401404200d00300243c0342d5002034203c080e04000d41c10380e1242030100051000c00082140d080026a2040004120042c070030002407403070748000d00d00b00340310945071440c2ca0304680c400c01030704044580b11114240c441e2624032418082040441c1d02b00941010008520 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 662210359 1250 662209109 662209153
    0x60608030a022d0601090b03060610050f16080a030905070b07230a0f06200c03070b070c060504080d1a01021f06030203070305102405060703030f02031006030c02 71
    0x100c107000d5124403c540d80656082e040030450445029940b1540e1641c45000040056201d418800d10500000c250b03c1c5c101504028220345081d510949410500d9517180680d074402140903141c0d034841c1e01e001d40440c020380003900020f01240d1b800301d64500541012031800c180303508130400300320341002454006400b2052801122030020848a083c034a21621b1a040c80b2040344054203050207036040b0030070840d095102028440501e6a00d011101c5a075010b064103018104008815520801c24803000c41c0035030325810f48c0306000c1c0c90105040d00c0580c3c2d402c0d060301e2080d201184d0403440403407028501c18040c098441303541e40d21603a41171046c010100003961400400310030b01c0140100c03021100c20a442b0f812000c05542c011b0300f00d4007450354a03c3c0540c5c0e151480faa400c054249080c0b02e10b40203550081500c1010419114103914160030101044010b500c1200114241582c1d5100300c440410b09c1e0019502c036004908280400724603210000c0d0a450a00140c4421500003000c2003031400701ca01710b10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 662211609 1250 662210359 662210383
    0x7050301090504111e030d020a0f0f02030705030a0f0b0f06100e0114070f050114010b0a050d0209040903030b090601080c040b16050114011a0a08011206060e01080307060608030a02 79
    0xc038141d203583c2020345404112030300c11074000381c204c5101000c03100f108145540d442401c6c0e0071210040c0a0000c04ca850b81510880201690510001140441c40814039481d0003130004098454442d690030001c0e2500b40040030031502000c03001292020300038000d080b40d601510340500d601040c070340f440c001b0b08943c4409004c0b038240301a1200301c078440c0c0d1088040c50000402c1d10301196480905041031407203c5280b1508450740d60030500400f115800c00c221050403543c1c1d40802c1410092070000644241d0064041907011030382c288082c81c466501c0d4028004032500030b8038009200078001c001c0c0954100d0082c0403078180520b40c5d081c844130110050446040b00d08078140140c82d0042801405550b24803540050815030900e010b5a90384460646c1c02412108103041c40501c003000120035030028018030300c400010850000040018410300c0e40d0301d101440c455200010a02c0d1140031000920300281c004906aa201050720001c0000605c2400040c144180007076007070801c11a0000d50300d00389003440b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 662212859 1250 662211609 662211611
    0x1080702010e060702150a0902032a09040b0103153605010e060106091a0426010e06011806050d1101020f03190905100804030e0a030c180b03060705030109 68
    0x161109100390b11507504410310310180da5032400d000c08020342d0758544100914480b00580040b51143c0102c0c40f41000f2541d0142c00303011400c0201c2d0061003070283c00190788a541800198071401561809a00b61141d441130706c003e0300303035411410300304040b407030006620b1905d83c9070221480b04c40340320071100035203130052048025102a804002400c404c031070500051141d800d20005000d01c910200700581030311a240e13a40c8500981d107010f071204a03034074040c0c007003250441003000b8000240101c180b907052021154a01d9910300d1842d5442e82120b05112a030600e540040005208441c51a8007818160000c048280102401c00000641c8549a0301c8000c0072900e10400129041c1d00038804012451006800d40740c03174070301c290015546c103500000304600107418610041203926103078840041d84140c582e168000360b81d03280d40665041105503199540480c490701c00200103846080e0100240c00e4031601401007581041d160019100b9411403588650062030030000807941c05000e9904551007044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 662214109 1250 662212859 662212861
    0x603040f1709130606141608092206030c051806040509011104030507031101111e0c0303070602041e210f020a06051c0e03090d0602041d0405010c020105040308060108 73
    0x14550460b44506680950400156800d0940c1a03045600000444149484900340c054180c40c0c0c1e410f140c451741d0081c1e008884180a00004500a00b01900c03500300c002d820407054950b61640c1c01038000308800c00200789512042d040c400c0200c0e201b18540104805c1e52154031f021041c0d100300ba62150010100d50040d591030001611030f0500750000311040b100c0320315640d6159100d00306252520f84a0005841c0c8091030080340c800c9501c0b480914030b908102d5070152615048050047c2c4031084d40b464010654403e000411788607a80030b01c0141042817040310700507903507803902c0d180145d031340391070740300802c02d40a0024200000c8001120520034074288c10400400d40c5440e2901444442030420b020350011030f007940100f820350708030005101180400035100e22096403041031400341d58441d00384072040e800a000c41c000509100320301c242b51620a00025041544500080c01c01d404081d03441050081407009100500100788030301d20441d030300b42c8028066803a003a20084c042e03404c05420313541000001703c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 662215359 1250 662214109 662214143
    0xe0112020c2415010203130608040c0302030102030712111305010f0909060b0d0e0604120c03140a020d09090504111203270111070e010902070804180c0305060603040f 73
    0x1c008400c0e01d1481901e69258002c001d01d260350345090848114004400c040e604071219800001035500304441c600e422020721f420300c20102c0303800c18050b004440014902d000800143e500380003640c8140000da80300c1c1154440084000159035607102e070200d65100410000801c03074500d0f420f05054400c00c1c245a001a004010202c80d40f18055205443e410314040010400303060b000c000f00414400020305101804542c0342c00342e1a480155401003501c402c0810340d0500c14081d04910720b0460023800e00d104048980030508030b00740d120840010058100b044000f0080d42c220b01004090955104d00700070501e000c3d41e82c80c1451482e02542445403201c50a1403181c40410000c4998000c40e200e01100da200300502005541280400d000703000c1243c0039803000f407889000034840708950129401c0740030342c0d1800e45032600a502c20768040d510a0320800c008106110541c0c2144a01c002010001585040f0f903540181140c02c050500d900c1a04c040060002045030340c41742400030740e00840c146030001c00701 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 662216609 1250 662215359 662215363
    0x10e130209120a03211b03200408070f080303010803090d020f061330060f0e0d02030c070f06023703170105040b0310020a2003190e0112020c 62
    0xd12040c2c00d50788548403411080503403000000b02500200501084c0700c1d40e2514006055505d40098540c010545d41c94480d02640b10350416001800c0c003911110310019648001c81c1180e025421070400c551205004000c0d02103650814401004c3c01406141075505214009443e4425034890314418003000c0b644006544c0e0ba81b02070880d00000030245c1e0340d0340d44081840700320020244900f48445080400400030049015401307180e079096944561a180c24940e203050091440a60071014190740300c0001098072820008528107403070940056440d44040c044540ca40000754004428501480d40100f1443d40c000400c1299040d45690003500440c05101c44882600030300010004810348040c01014150021300000c00100c148480720910380e00e8400b80016592465403051b055802109009207189a82e400740050040c80d141410401000548140801c081e2070502d01c07141d00300080f140c45040400541160315a174030700b4081c1849054400192886c401405113698468000403005c4512400f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 662217859 1250 662216609 662216629
    0xf13051b0a09050421180504091e0503041401090311130e070b040807120506181c0302030f0a06060212070507050402040602031b070e06060705010b031b0f010e130209 73
    0x220740410140c585414450701a00c00c2e01e041200550100b603821030986e01c00d0500e11000908100548043d130318240a210041c82011420350f03a03441c1440b008035255407950110264503000e50700a680f100d0030000f6040319046005441e40c18803a0b04002003000520388041e82c0c20311107003194a1400401a0f4003c04040c0c0701014032000140506440410301010500141054940540490300280c0d01c4201e400002840642d000c0d00503404171002a82c1410b00441280340300c0c0300d2009540d03800c08824003d0f41907141c4010000042500070042100d0707450302410081d84003441c50310500096107040b00c06516440400900000c45100007008810700000300001001420051b0085680da40c0e203000017900c3c1d80200080200080040001c03401c00e500009511043d40c8035030300f001c845620340c9001c210180d0301c08541140c2139503d500780040595024490851021804281503140311045010003c41604d60700200e810300000340141c582c02e490350380050504d04e60728440107039541860000907443c040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 662219109 1250 662217859 662217869
    0xb0c0c0a0b0c09030f0d0905091b130b04090c030b030d080a020f0903070f090c020619150902030f090d110606040209031504081c02070201051801031d060f13051b0a 72
    0x1041603415481c0d1540025031000c140d81d961fa48402158561003000800c61050398201008110201d0b071210404d0340c1c10003403000c141942c1100c0c4a01c0e584540b00c14058010398005100c8640d580040e981c0079800d4050505038150440140820410200c0094490140a462a0708143d03003c6840c0e9084007040080780d10350f4070014201c42d40e26666000d0000003202c603010702c030905414080111a15800014214050a64148180c0e880c4642212b001c00030b00300d41d8505480d05440000001c1d00060501c011401a5081c40c20211a85800c0f1038a03458034401001400410991903040e403490300c5e002c00c54a800c00011030703000d40d0350089000001d01d408915850404141d03c464144030400c43d11a00400403420603d400202d400501c010880403406400000b90124030208002e4059501b0011250750701e160504000500042d01c80401d07803c010040866036896012109000071000d51000341580320040d200e050148032256a2401e490b4044442c00e000c2d0b41c103180101c41025607131480c2030000741c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 662220359 1250 662219109 662219113
    0x1f0e0102042405090a0e0408040f0e1503070515070501110a1215060509061b0f071d13150204051003021209060105010f0e0a0302030d05070b0c0c0a0b0c0903 69
    0x59150308100c2010480d8000c00341c004041e940710303103126a0095040e03465513000140200c1d0000c0c0390600c4840f0581004000702c614020410000c604600074820300e41c042e080380e800d03046075486e0805a481d501071000458a129a00040c0b0800050351880014990341c0d40c81c01805440e05020300d850350140c22480001410500c1c04034030300c031416074007601802c8036041c107901c1030000d209030b400b4003204038804d8026003001450800445da55402c250b4000d00702d404200300b092000701e0f010007080382004082440641d4503000305200300000f501803000c0b4054181154a406036608140465214107946a4402001015400400841c00d126079050360000c02d406030a11444542102c0d00600951201400c180385e80c1e6001e010035105840041c85a0684006171598190100310b49403d403944604994007540c00680200702100603101407141c405020f407d51626502c5da00030386801a9007000091a0b9240c215050040c10710514000949040c10341c2c000c280181c95403681c0120510900c24005107a400d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 662221609 1250 662220359 662220367
    0xb060d09050c01140a050904021b0d11010e0309030c010309050304030b07120507020a172203050703030f0804050c0d030302070f150516120b0d05060106031e090201021f0e0102 77
    0x202078082a01d400a0400341d0310305007030759204145401a80261081003002a0060012022070300381640107142100544140140200a00b40854500061074481d040019003040304911044002d000e40c841c00c524400c0030307604000001c4040b95640c610606401d0400d42ca0b6101c038030511400307108075005190485184402894042d00c060700d0008030b10181c000003481c040000b5506403000c10095407295014080c080e0940c80510700c503101e40c00c1494600b1500c00c050040120325050900ca05004501c520080c01d0211b1843c01e029000060040b01304d4244a119000c1000094020588044002007110001800c0d003042c20114001d0141c98002000c0c44e4028503404240540b8224540107121780c1a014801655294014045524000c070b594000c00c00344000e02d00000180d030040d10b901500905a000300d10440e0700d591340343c200c017a4040000310380e455844035481c4084900c0321046080b02c01c405d000386003480c0e000075521501000c1c2c0c50100c0207802209001841035400408100c400c41000b5512 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 662222859 1250 662221609 662221613
    0x151e17030a020c13240f0b090d200301020a0e030d020106120b2815082406030102070204180b0702030403030906031d0d05041d04050601030f0807020303030106090501080603120d0b060d09 82
    0x4280c0382d405000840307a50080d002594100da40c1c112006920050100b10f21850327640d8540c41d41365013620f14802d180700d560711039910680342403015110f980701507a500354180d41040181410200120920030469041980a2111110300c11030328000961001c1c04034081c3e0307116100448079002d4040c1c4044058208031240203100b80c2904000c6082822500034030b030807a9205412566020b07083e0f959103920a01000c1d42c07190300b010004150384001d0290001d407500e440703980080d04070307980000c1d00a00c90000988140c2403080c640b060541c0a99140001d43c0b42908640300600203041c60b100c0d1400b056200c40b03898011201200d580040012201c1c00c03102042c01042e0007030141d8005000c0d1103106445200090002401e220000740103540150192a890b400c5849035085281075038425184240304200d40f82c01030b14208000c5000f400203a98500c152418900010f000400c0a0800d92280d4000f04c0d1100030000190111100d0000002001079903600740004113450b8040c1c007244441080c030380701441d01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 662224109 1250 662222859 662222921
    0x31e120f030e0f06061e1003020304121d0405061809030315010306140909120f03010e0106080601080a150803070813050d080409151e17030a020c13 65
    0x60840141c0701480700010140440c2e582d552140c0c658080f036400741010806a04240010142c0321000c0014140b00500000104194000200024002075400410032040c0007540705410304100481c40c0020030030300204602d0080c0d115444906228030341e5000400c0c029664020b1800441d03002c2c2c0d550444514225108a840c1d41084508030030743c1500800e2481c156200b4071903075080d030700a030304610703003804440040c004403070790007080802e0f14811010150140d016480140c60590101035000d680c83d030516100000c10101030344001c052154140601490380e800143d80e60340000d41c1c18001960a100506070f4108004c0340e80a400203000003e4080b0074000404020305a403a035680003448a241e4581c00c1c00f5070b5202404000e000e00000340000e021204160300301c0e0036540401031152070010348420001a2a4140c000d41c0c481280a08904015500303054682800c0c0c4140075001d07505000416034040e440d841402c204902c100381384038401c01e4016065000c44180300c3c82c44140c07803980c9207c1030309071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 662225359 1250 662224109 662224127
    0x60a0815220f1104060f05090a05090705060d02130e012904090e01050402120f03041a040308040b030a0b0406050a0e1b03160e10050f0315030105071206150504031e12 73
    0xb0380a039080c40341c04141e51001051b02c1e4100c5201404900a959130480440020b10b006007400000e405200310010301555408058403061298200040e903840294007a030f200c0d1081c0e54482c882026041004200340121540b00e030b00c1000003c4200d20100f41d103061030000c0e6202d02d802c503103600707031404031803011190055000e40d02c500d10a503010a544030705882080d03601c842108018245034000c2006100500a01c0d00c420490655a908030b4249612546e69001d1a04141c120fa00d0341c030790200400c105180e141c010646141801d0780c08010703442c04c2001103482c1d0070307484c041d02008031070000c04251856444980d0000381c0081c5040c068403070070150504900301d405000310400250b00f11280c40344500e850400400b43e80d0711920b45524000c4003500d40600784e00000d2035012943d04021401e885a1000e02550f403084460f9541c00b4200245402e41070111403c2d90401041d5502c1d9504021107150001c044809907504500b070002d0001c00e02140b5074131381c80303102e00040003140001110141190410b82c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 662226609 1250 662225359 662225393
    0x1e06032a12180b0613090b13050c0f06090411070f0f12030b3f0f07060302270a080d0c030e03060601021f020c0105010e060a0815220f 59
    0x3800b1500000404030303002c5980c80400740c03010515402081103440c1011211461107400c1c1c0000c201c3d9852601c580d891603000b20b607072840c0c50f03800ca00a0320400038144480070b4440000c688203004202d4100202d1100c0c005d80340344a015030341d100c0f01c5480c4d01c0c0b00c0ca420369002c50340c0505d03011048071003840c001c4140541e5560856241c0001e081400143d4020302440e031151501900c114852594180240c049090407038180f076801c0041c60b101c44121911820490022040344001d081c10f80b10310042c0351800c1c3d8140d01c40020180305000d071400480040e800e8000002c401d041c0000d0403c1c02d600001c00c0110954041c142511621420b1914242c02469031400b131070194803044030b402e01c400f05054a0341011204180181c12140000c441d03810791105801304d148064000504052952095600710b81d802e8200b06017040750300b070030416149400710802c006040c001000c0c0c00941c81818084d506100b019002030315188205103000c011014044803c4030550300803441d1082d490040c10701c0920010741c039090b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 662227859 1250 662226609 662226611
    0x61803010510030b040b070c0b0f011a040b19030b030a050f0d050405090f0a0b030a030e0a080304061707050d11120a0b0d0f0503160803101e06032a12 66
    0x1c040160801c03042c0c044981124140c540380e03480342c4d59507a00d484000e0211040c0300036002e8010102d842c64910900c5440c2102c240b2007203505003502203d000300808a11103a11408200a00a981d0702009682424248441301d08a0b100f400e4419400760200300607003905441034441d8a000c2c004001a48140280301206807400c2d80300d003030001c031060f100c0c60040d141c200d0802008122400140c412941d40034083c03102c0001c1107070107500020304000024109034002a0f1000c41c0c0105442c1c440302c0400200900c20056190502e4100090500d0140000c14140e1003074034400a0709090090089071010381913000c00b00905c64480c3c00304d0560780c005508a04004204000054580000384105080322000600c0c443e0006150f0703071031205802008604494034081881600f00f03e42544a00030300092142c07899a803a0f140004d0000313287c1c1e00e203a004900900c0402d9650208100c40b0010b0005c0c1d0710b5510700465625002071704daa00d11050340520000c03604440c41d00c042010351000c514201ea0000b028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 662229109 1250 662227859 662227861
    0x15010603051518061912140303071e1806090819050c041e061203021002070c0e04060213090609060614090f0d0501090b061f0e06180618030105 63
    0x8185403414440c15000350000703044a8a90b5000c903521030f41e690701c100b000301440d99100700204204c0003101240e11869400c9072520801c4100424001d007100d290401e040150b00710f04c0c0121000b00054480c401c5943c40152041d1000540c4c0c0c4111071a62002464910f40607100d95180b5000300b0000c124072440c1024018890f802c0c4580301c0300700200315001e4000008100c02074001d02084010015904400300780101e40d9100a5540301c54000c5600511720200d10215502250a02a0a09001e6401c03114054810016240040c041c111040300b52401d03507400061603515032415500034400ca681080603d0907280c00050110f10701c2e044441650400c0d24180600ca503074540955078600b40405504960030280003800c0741d8208100d8690102070018010004100c1c81d454050844400034410303542d0b01c28010030048075042035482c103c240010080178400404000900404108582c030045201e02e50002e2201645903001130058034521000740500e40d43c400380b80030290207001d25032509019508044c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 662230215 1106 662229109 662229121
    0xc09030a050118031803120f0e04090c06020d09080606090405071e0524072a0f030212010e0a03030e1c11010b150703031d1501060305 59
    0x4119201c00401c3c0d05005183ca412900040400c5c10100020000212072118030b01c810142d40c074100c4182e505a180c11544161082007142d80030707003481d8440c000e001e0131150102c03c17a2070f0750b0200c583d20083c000080c1e500403010311449090381c1100780010214200072800680c014070a8080c0d40c1c03001d031907440c2c8904400d28400c04004105450b0018002030400010100b192a00750f540e0851b12048002024018420041e00408441250180455140e000c2001c002c00030701c01e000500c8155100c0e005650805041e10090f4400d000141302105828418880c00c807000f0084c0024014820254900b034000c2e00c260b99400074030380320303542c48855000130b95031452440f081503070303652640325072101c450900391001052118030541c50411508211201c210880d9240c0390315080101e141d00c880d24050b2001c103034904414480d406002010310711105015516070585105442c1001291504 = true := by decide +kernel

theorem cover : BRFrame.Cov 662050359 662230215 := by
  have h0 := BRFrame.cov_init 662050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 662050359 ≤ n) (h2 : n < 662230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
