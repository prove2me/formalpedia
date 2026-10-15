-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5304
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:25:41.159012+00:00
-- url     : https://prove2.me/submissions/f22657c8-01df-4e6c-a6cd-d7498ddd12da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 953776978 ≤ n < 953956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 953778228 1250 953776978 953776997
    0x207050315071d121006050a05010e0607030311040807080d0e190e06030a21090605120c071a090d030f151e0e04032c030606040c031803 60
    0x24980750410034010301194800300700800160755400f1041d0489001c501500c000a0f4030244089200501c200381a0b5541c0c0c0070784a29042c01a01030390040c41103401c11a03a183d1420340c0d4400540346002d0001d907460b0008801c12440011074040d030001040469024a8146015030321962a81011626048044941c10502034104003030f5210b440e001600301c0440d85012005072090304111041564401c049039050000002000f5035024000107440c190050f00440741610f11700c516480ea045102540302c00304a1510380482c940b03105000707580e139003103031120200307403a4035208252401034016a200b1074244500a800e521400480c82019000d4030f01c0303000800300340740d07160030160070345486201c003005c07007450641b8210903100308041040448030f140303907200311910064181e8080240250003040b40d19007241c003804100341c1d000351010540a00041d452504200c01c00712400001000c84180342d1550000000c140d051038075522a129802e03290400080e0780c18400d4407640e520301194425004103220b0300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 953779478 1250 953778228 953778239
    0x1826100e2a120a0b0601090b0a080702030d0908071511041403030702060406021605063408190f02160314011407020c0a3f061803030e0d140f0d06060207 67
    0x88900e41c0005090920b07080087c24809040043d01039108068200032b03074600070400d40390003401280c50002045800703000c0c900440c100010079903c903070002c035441d1035801310001c03007820035101d0011584100d0500900c3c06140c10b600c0c2c9000e05059002e40d0745400108001c00c016643d0030001c000502c11078028080d40d03542c2e0302d04804240c4007644114026101040041860300303d20340680800d03e00c10b50f0000202000d00c4001d140e00e082408000c06080c1c0000d0360f46e446840306411241400d206540300851003510b440106e07212444100c201c40018200b801c14030004409038000c42c1629580400040d200c040342c0200e5150000640f01c1d000542c020300070103030740e40c1000c44420f400f030820884c040100702440d0003131580300540c80c030140e42c0c0c1f9481c081100400d40050040050415001203042c840d030160390704000410300141108030042440e1288580c601c80340840e0301d40c0d80c48441d4039a00303002c500c00c51600d51030783e01134002072800800402c0008440d107024428000540f034a40d000341007080c00c1a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 953780728 1250 953779478 953779493
    0xf0703292823030a0f0b0a02070c03230703230714060705030f0f13090b0a06030b060c071403160f05011826100e2a120a 53
    0x15005541048180e00740c0803841040105040c04035000305107241030300d04040b031145a4490b00340c000d140d0305004003a252828482e01115486040e802840711407030545481440104911840348020454480680c00700301040c03030103854601c0310b4203082c0d170300700c2103a91982c4039030514406800840d2108500003003010090070f000326080d03a580c0d00c84028120581440c003101040080c1c005407900c5a81c0024080d0101701041c815a501d1000e0740c40d00d00d841e020052a00c500f01d07046580700c10402b916908001134000d160340509140b02c04c0240807650b17482d003032580440c040d10004a030242c201104001c09a54031504003d901c0017030042c1d200d1590141400700416040002c41087c032030051a248809101044070f4142a904490782403c080b034003080846580a08000e095000d0304400c1900c246811103050800000740045a414064070b84218035949808110f84841440401c81c0e4080ea40418030b0740e07102c0d00848440a007110504038081c50b1200000c4072002000940c56658121182540c1003105a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 953781978 1250 953780728 953780749
    0x40b180103210e0907020a0219060e06160308062106040b0c0901091701150e091c0e01080a060305030f0706060f0e0a201305030606030c01080f070329 66
    0x9080c81c6104210b540041c000846107520610440da00d40100d08000d000f00000c00c0220341c0030340890b00000c0d103e101c070102a0010b01c01d000100300304075040b024514004003200c0381d020079001411000041500d0480e03920780010a5070741c12001040300800b5650026030341034604008170380200b03820f1038107281400c113464014001e03c9080c001407014010720307a000300b10201a25511004403952100c9481e4030b60142066120403600da00f400d40c004600783d41c01da841c0303a1207040a003003140d800ea4898048800844940d088060024046002061042d0311a0000e80d41180e0b10190229034a520b03922480c0c19540302586c80d60b51600c2c00258041008083d01415008090f04403191455510b0b00003011810341000703200c45601603071035048190942004049009079001382000c03d03103624601d040c0112500860141ca13100707100c0c190000701d940c640000c0c8408980d00680d100401e41c0c55044900705210340c0034055105050b11001c000480c10701e04c0d041604188103284030070703420108041c01c3c80250520f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 953783228 1250 953781978 953782013
    0x50c06070209011206150303090618080c040f15081f06080c0d032c19051f020304080313050a08010c0806092a0307020105072c040b180103 61
    0x181031101401507038a00e60380700e04580d08420101c8040d0410702e0510000e2003007250703c08203c81201c00c04000e240e84404e20301e05640c16a200e01e40020441002044251420b2290744040e0313010743e41000325401c01e50092642468940d001250207101012892800071f01034028401ca9401500607014071150607544902040181c5003c2140b9811318402e030b03031158800c1c010103009418650202040507c209040c0c1c45a800300d256041190905030f11001104025031f001c240b0510b80c60001d48417040d42c002d40e40301124002130500c00784103050582003242800340c01c0c1d00030550000740000520518180010211022020750030068a82880c082010408194201d01e42c1c03689031000e140640d58201001d40d4000c80216101c4440c4e0365180c03070840790b240000c0d50a15050111a07070316640b005082340074601400860b0000d114a030b441d841e04a91788501e400000403a860104500088071000300c1c0256a06140600046062241382000c00c01d1840810703d449803e0000308010400c1c00804110f2400881 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 953784478 1250 953783228 953783239
    0x90b010f05041203180e0f071d0901030f0c0e010b03160507031b080d06090212011508070804030302090a030f0212010209130b0301090f050d090f03150203100302030712050c 76
    0x14200f40c800005500402070080c24000040c01400840c0b801141d440c0003001034102803070306403405000d824009001501d200e0046800d984501080455140030a8000b100140002c2020b0b881c54888504020310208140c0314289803601c003003501c0c408140c01e54060700004084a03074034201b443e502c9030400350f40503005003000070500042c400a540200001007820414400c00085075040c101181039204100040041502d01080000d80100c00e40190003411700303076003030b4541607a038070001500c0800c03203008424005254a000114058001c0320602d4010b402454010304224011020810704482c83c2c10a40d2220010840c410840c80c06808003049980c1e01c80080d41409a0b820119501c01074210390342840c44d071512042880c0b91070950141c442150080040d03154841241400b80c0c44250440c218800180208004101114007692840450307030300c003461403200c00015102100035040900101c5803140c540e04000056070f41000088050070f03840000201480e000e24009140071010a04c07d8000d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 953785728 1250 953784478 953784487
    0x7030c030e01020735010f0f0605100f050a09030b070c051c02060a0c1115062407030f0c05061602010b03120711011b0602120702010218041a0406090b010f05 69
    0x2c40980c80b1103900c40c80b034245081c1105940e071783c0804403545008400c09541c030703041074a502111560440302c81c510900c07408000301500e580c2803061504c60a13400b6804610300c50380d90400c00d44903400030702e40c2004524021328040e440c4d65808442c503a081d80c04000040c8200c007950700340701c0300340314031200c0381d40814440d08210783e4900c029440e81d80040107410420b907101c5a000c034081c081d5904951080417841070340c884800311200201d01c10070540b41c180c00754610a14000001100320040c0c1d001c0b240c803000346030400a42d80e5003203030302e0585000a1010040701d07280003000124200302050203101884400500d10101c281c009084a21030740c60716100c1d601840350007494601610440c1c0082e038000c809007409064010060310544170042084524082c0c0454050a10a49601130702600c980682412481d4031201e004a09034010f50081b4086610f11000200e22807a03d46e1118400e81d002ea00d00c444d030340795081d00060889001d07a012615640d154402400a90ba00410100c8400c80c50f01f0441e050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 953786978 1250 953785728 953785739
    0x2503020a0f050c073503041703160f08041203020a0b090a420605091b03150301061a030108010c0503240d02040c2102043807030c030e010207 62
    0x222a03842c0705100c16200c81d00034403609965844012a072107285003001c1240340b8150701400755a41c1c09441000c00c80c0103070140b108c102900200442c1d150004a1090b9010051a0f441c0c04070107454680e41203030545010000000d0b44181450b5441e409802032700540f80c01c00c440d040074071400070b0081042c907180d0808090b500001c6d402446038003042111600c3d241200c88078882c40c01c54966810040720105c205440c00d1034902d40d0503040380e07064500940e26038405440d042c010450507034100f070046480c01014000650b811032240081008030748000c00215005580d007145241c0b441115a08c151000380000c018090f51209004031604c091451516910b135140013100041c000700c0f0800c0d100c40401a19100e4000341d175400a4401c1d00b00c1c1c00034400c010760b01500002410001440a1604000c070301407082100c1c01e071180c400d940445040d034100d8480d030a040070f01c1d0ba8580521440c01d01000300c90780e1000710401c8881015100103882030b00c61090310f01d030f00d00380a03040d03181c0c21413618110350103103206111 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 953788228 1250 953786978 953786983
    0x314060601080f090a060f2706231504060302060406090819020d02060a02010e060f010303020105060d03050912031b030c0f1603030c0206120f010f050604030803010605032503020a0f050c 82
    0x25101c1d0845400039800d010340e20380700f007c1c0c134070a55050842351071000348200070581140380d4451980314000402c0030707107a40000c01c401401c0b25083c0c419407280140010700c031761020341185401c0e1140100001a074640700d50008005410039001040026485841031102200411140040c10104031070004590320076400201c560120480090080c00c010403d03000841c000d406c000341c110300c2d040503980c1902d03210343c00018522092001b42c1c01582054041280b0382021190441023503015621586014611010710000c41c200121549403807004020440c4507480c400f50f4801d015030907001031907480d240c02240303034034101d0324521843c00790300403440e01d11011440c003243e03204036540f5041071300c4c1444007400040e1080c069040300d60a0395800b4800c21501080e03d0003014140c4011500c41c90820b40c564090140f28000c900000b0111801040140132840c011000f85600420380c82800003041080d00c1e80005a0107201160ba0101c1c0d00030415500c042d4201c4240012180d00707280241c00c1c4051203000c0d03903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 953789478 1250 953788228 953788243
    0x30405060c0702120f1b0f01121e0e010e0d0f050d150e0717010b0405011205060604050a030c0906060c0506042301180c050919150314060601080f09 65
    0x1d815500000707182c001c54803210080030981c1c503244140c0e1408100e5080ba2a2618112035000714142045441d000c1d4514003c02515150b000c10fa4075440401c1c13a010100c0010404410071141084200a0058503890a8022500504032510005c6880b00317200c03111600d40b51004800f44207128400d003e88000703035404025a040102e8509020075a500c1501e4495003142d26500910200c0a0800400c1800c1ea049840e40456015210f09035846a90342d002c4e080e0580241c0c010b0381e0026401c0d01446007100002e4008540100e8014091860903668000141028185d5402292a00d034000303002c003c2040588204030040c0224200b10305040c44556407142c5646c8002c0c0001d002c00300000807050030318611101107207501c070200001c03c0f180385201c072000744001d080482101e54a210071004509810084181405090681c41c031036041001411040043c01c0900c0e41989110f08001000020550300f5103030650030101c00c0301030909804c0c40000142118001028801c200a5480910001d140c0004020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 953790728 1250 953789478 953789491
    0x1902090f06011e091211030c120c01030515091303120b150d0b1903140f072606010b0408060a1a0103020a030e06151008060a150210060902031b03040506 67
    0x2158489060343c00391a10b041c10f802c5440603901c03400840781006614601018015407c40407141388800407010807003046d40813000600290040d2510302d10550007500469003120f4003c140c01c421034002c40c007113001468116195058081c51441d20002d040d00100068a4142045010b1010400300000b1924652200400ca080141c00082d8152680240d42c800700000c0c400401e1000d1000b00c611244018040e1408180c03200b04031122112a07032000000c401060105900c0540011032a11420721071041c02014200b13112000402065140d480a002c000e010300346040c01d0a40322810081c17074500c3c101e8010a482c031035918280301d54031890840d0150b1810f400003403801503a0340c0300b0400c044000d45080070006015205e004103000641d030307110301038540141050b6115210072009c510100c9041c901a15041d41024552600f401110350090840507814514011250550301550800c0300300c5031301e513020f0321041d503000c4107010510b24100380c513500d80440c000d42c0301d00314100f644a82d030711002c01a082d07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 953791978 1250 953790728 953790767
    0xe07020c01211b020106080105010e0a1d0f0106030c0611100209040b0a080f0d14030604020d0207210816092306030a020a0923211902090f0601 63
    0x1d007480c06074882000c0ba020380712054280110140d8460480e0009030a40800d40954284200400c00b0ba0052103000d04a41c810b41500c40304e504c83d540e403a00203260528654200111070b822101c501041080416141004e400000a00707510318142048444415040f50040041d00000c17803c42e810300080081900b110090010f988201d454001030040c20720380e0615030001e4a5000000d00c0c910042414094410b446041d14040b540398801210003420380394480707002200c103101092a506055000d410b6456400400510300380b85c41d10b51403484185045500340304924690f4445490f035001c603015170008400205a6200e8060081c0509140b90901410a0a03120502007144140719080222501038001d042203589080802e0924007075408000c0410104240203800540120052151103030541072982e070041f00381d2040300b04081c1c0c0c0c4d0001c0c080805c001d4219070b040e483c80300038001841e0750041d040c1c241c0144c0c50a80706018840c0001050200e01150510130000f150360004401d40086001010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 953793228 1250 953791978 953791997
    0x2706080c041a1005120a0902030d0f0909060b03180309010207050910030f03050d111207050703171e15033d0603020f0406050609150d0507030c090e07020c01 69
    0x4600b0201c401c02040d180c1c420b1000d8420a03da941141c0100850020802d940c00e4a03914014554299945070308000d41641c04444202034480c03282140b0001200c40e46443c0344484d517280e01480039105260840261880000140140e503090b01c0340311010514100003844c1440c201e440080c1d2150842d03c00d540c0a0640d0800081c01c0420050820340510b5100303030609845612402c00402d5034001e10850f20101c1e20f401d88800f04005108107898000030680e60303441c081d41e5400c1044540303420034481241440707144e5107801000f440040c0c0340380c800c221042581035040320441d055500c400000d4920103d1111a0b001715603141c40128403181f900320641042c000840301030303410034121030780f030500c407441c02007503240c5004500c501d5009502140d000702d404200f0780d8400310070842110384501c40c0a03403202c0c0c1040141981d0801503181d5030201080c203031040c1070140701041031003600c60440d5500b00180e40c569400d24080e41281e682e6014210000300f8905a25007400080e40da41a000c8800e41400020039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 953794478 1250 953793228 953793251
    0x5060d1a190b07031205090d0813080f0a020c0a170705090c090d0206271f0f081e130308180c0114160b2a040b0904090c2706080c04 58
    0xa003c005441c3c000204407c6c40c04030042d0307446884501203203000481a5000c5800c904201c001074002c2034004407803a01d000b200321400862036109861302000e6015014518001b9510b07a031807070006008102e1445201ca9600c80b600741000078641095115055290600c503011018006640c1041c0d0280d811808000103030001038000d00030450281030310b041418194511050200c0034052042d41075610890b504100302a542449400d2840e4200140010602040e036900c00c0030038540040d41540c811120100f602742585005c0401c541145110200302c0d04041010713031000c0895480380f429140c10f03036500c907222403003500c402c0300a1080e41040088041194aa0100022224500c010074802e0961541624100c2900c610417184179022104900b40d02c4410081c0d420307203614921034030700d2680ca06410203008800d9a0002c5010a802c5542c3c0d00f00140050303a1300a8030005000c42d0002203e4010364012403030703800302109c030030801140d0a00e00c04101100c1c00084200303110300122808160040d481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 953795728 1250 953794478 953794487
    0xa080a050403080418061215053c070504210c0e070234030813030813030611090108070806030f0316020f100c0f0c05060d1a190b0703 59
    0x2d40015148807030004001440e21103d00e04042e12100c2100203110540d034803500d04e101d0300c044034009803290001011300024914503900003948581c6183c01005000c42c0002002c000000160f1030140d00821003140e014440c03551b107a4150702c09010329026140600f480900c1c11408550200910200c04c4074a440702003084800c0004040c3ca05a220f07070f221803800c54002035507944070200401100001d4880c40403094500c1a10f051160000c3c020b030490a46156075008035640f000c0040998240142c40103c00240200b009103855a03006044008803419414164104c038240c4000550340700c0e041101c21103590708000310b580d00001c5810a1006a901c1d500402d043c60321502c85104140000036000404030100c0070310b0002507000361254015803407414180450b124030707c1d40d2440820102d6400798002003140c2c8505a0441c412026454660380d11000b181158000405030113409440301c480d020005000d1007084442c1c40200c5250049410500303404920360054010103001500001d404400e05026 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 953796978 1250 953795728 953795737
    0x70e0112082d0702101103180609031006060f081b0a030f06060810090e060f040c03120909140f0a02181801210519021507060f050106050a020a080a05 66
    0x100d0150200742014a801c22640f008034200e10800325009982d806510174402d10500c501c0d000002e41c60580c1d11001c00d540b009103244215403258041100307102ca502c06011540210600c0040414a01d0074044090011500d100204007000400070800c44049807142c110150804085840c40d40e5112440089000e0050600c0d4207001900301030700010640e0380403542a206009101002c0384c41601c429840095801c0b4540301d43c0c45502280100e800c124040d109039404c0742c0304020f040ea2165580e40c60042d0020309a0390040841c000780d004010180300c0303024071418001c41c41c0e1040d1151500b6402d001184002400003085182c0c04110103114014191803002c030490018181151603841d0f4440f61110202406184101d401481200909212420340140a96400720143c1a00840d002e40440c0d0a1100101a070707114842d491001c04020001c40203007403590040e8404603004000e081c0c11000c2d144182e00000c03c1007400c21108644075800b061481c4c805901c403002d03075540c91840300122164001e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 953798228 1250 953796978 953797027
    0x30d090201170906070305070f08060609040b0a030606140d021807140c0604060f090503030c07020f090103150b0f0307030209090102040506040b04060f05090109030b0603070e070c05070e011208 85
    0x80c40b0305000d5184400a503e900c140b0042d541030003a5a550f071000c0f1604401d00e42e090000c2103090000c1030240c6058005451880700103000052281c16540c0015080840e65100380c071183c3d81e989050250508258070010040c200b42c8103041305000036030204180c198a603001c4490100900d010070100ba1107000c04000d5a110321940503190318600742e80544a03102510104c0b00740f460000c0c1c074120508070303010308030000e50000007442c215500c11070f80c00341e00c3d4005c15003240c2c00110380000005d08ea0354903614501031400350b0300c01e480309035150389040115060f5400d024400d20451005070707402d82c0e0000d002015298107841d1030019803141c140040c003a0040703400c115408000071901003030000c031500191040f22034582d12600d00c1d101096050f1068882c403110b250004120410031303c041030050107000d4215070041d04445100e03582d00b01d002c034411400e03181140000c021000c12070a02c1420003215024101c40c044441080d40b40c0421106c105000801c000e01e00b01000c150780c0c00c20003026002c49250318 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 953799478 1250 953798228 953798267
    0xb03010501090c08060414060d030210050127060522180f030909180303090f1515090e03190c08040620160605030c07200307060809030d090201 63
    0x140c50b07984602c041e140440020700020701481c0080c050b03141174003400b400d0000e605079909058444a060198003181c100303059065114044c14141c805c80544a00c900a00c24140c0c50840c1603010486004c1003e41000d000034128144001402196951004c003a008500c08989010b440a5050481c000e0224014281c40c02c1c8040c0c04140240403d00040c0d1001e80d00c60340e55404401d4039121044103c41421718602804071560b0040c01c00613019070700c0711154900a9150303101303500c3c03150b0345c040662250000000040780c5541144045940b40142207010700015002807203c40101d03041e1a0340c0b80500103150000c2c0000048130415a070140305040c01080d04a40e80fa0b580342c0d22807a02510349110905060b00c040c612a0b440d00310001e01003961280d0129208016083c5450050200c5090308040c240158014041003030500003960780300310100d80404280c10003100c040d10310070507007410201d6000c101400091010070050030004804c84c2c144003110b500000d05c3d48624001243c1d24085a040751a0381d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 953800728 1250 953799478 953799481
    0x6010612020a32040b0c0c0a030c050f0103020f0d0f0c1715061903230103030e0d0507050310091205030c040b03100302090405010209030d05090604170c0409140705040908030a050a0b030105 83
    0x185813800003006c940c92010229408800640d0a22894200070301c009080701c1007035001800340785030003c4d90b175451803014903015061090404040300c0d0387c0d0081c060780b820244d5842200c42501c0e0075006525441102e41000d0031034181d128182864803100500403d160f42c000c003154601544c64009407040f07043c403c12840d66500c600b0704003900820007001403081c20600d03e07010005010250500070b040c2c030b50503560080401000d200384114601c1c030400c2124076000703650700440d042d12b007000b0300803c0010303002012401e84800d042c10000889803840b904200030b81001000003905083c41100e0440e4029014950359030b032449540f400c1243d40b6040254048003003000d01040c00340c1500a000035403011025511135148583c0165075511402e00b007160040801d0000300120300082c840d852040919409450300b000c51140001c0071a480000c3c100c1d4031002e075000ca11307146542001603034003500040d02e0400c161480d58039805101c0c0001802d55450a84a0001400d031400c0c03504254090302e00a002407016 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 953801978 1250 953800728 953800739
    0x6081902040b03011403010504030e101116061e02060103020618040213031e0b06040905070b070f12090f03080c10050a05070e1503061903080304030206010612020a3204 74
    0x40e60703c2846107100008059001c80329500c1d040c0f00ea6409642d040d2290341520340480d051104145010074444103100e15042090f5083ca01071044c103032613003c1b141d0a01646070a00d20054281c40074003040c40204801c103150625610780000d03015064a80440d070319600c85401845600508081f9040a9085800031a0780011443c4c1c42c00b04c202900d00c02d00c0044199500c40f03401d5004480540f0010f40304c1d00d04440490003504060703002c0d5900c2da00420aa8039119262001201f29910030720044500d00c40c145108400c1c01035007035140b0321904880c6000200d641c50408a03488110a038040503103200d90000c0c402d141c5e07200800c840d0002140c0040e090283d887c110701c1c02801400c0884000010520707440e550b49503071030b111030700d18070340208032141c2429a00e41c0700c14403050f540f00801628180e0200e20010005c5500e100c0918460380c4694001d101039814404010301a00c01c0c260548402070040c06000c45040e00814060041c0030212401c000e001d605010260766640300b4041d01d00c4e40e10300003602050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 953803228 1250 953801978 953801999
    0x1e2313080a0914060a021b0328060b011409040f0209042307050f07060c03021c060305010b0d020603040b070201290a062a050a080a030c020706080903040608190204 72
    0x1140c3c0240f043e0492a0079010900c8501d110b07143c824001030300103820240c0011929054400b0b091406400c035450701d00f403d0301030040c501141e070320001e94401301030740402040010302481c0707203801081c45c040d0400180c40301c0248041c041e240405128a49a074a054844150759042d80e00801005100384410203440d010000040041c01860030200040000501d010780620100c4d1000e80014240368900002511244018515030114074109602004000054140904005403503d442c80e00066818551f140c11130858070401c40050045c448040c0340800741e6507200a803648140c106040e2507040d5100030040380100503030310426044402200c8031b80400480220303142082c000aa45242c00d2548070002514417800210701208100c1c05413580e0b22840f85182400110984a1811101408201d94800f80c0c503821104c88440080d945400c51901c0c5641081240002c0071982000003103410304050141d1240302d01e0150005100c0c112010807903e20000c240908050203014045480e541c45454a90 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 953804478 1250 953803228 953803247
    0x822150b1807121a06040303030e030409090b1e01030b040f03030605060c01021c02070c05060706060306020304080306130509032505030301090203070807020106050a2c0a1e2313080a 80
    0x503d803e251545014062401d90292040710100502240c02c4c0361540d030703084001d00b403280d803440e00c280070504c400982949503001d1420a24407030040b80da10f615081000241e10600f40c400000c00d840081d0040000c9901403501070340240d002081900c2080a82c10240d0107800180d001c0754000c0c50000d0004040700d019030140c600070310108003040010703030070501c01c4003a0b000f41c039005000c940d0710308010007803441c1220060240324480c0c24003250455030b94441801702d03003044409407080b00c40081003000e2490440d0780302c034100d00510810041030400303c003025035034001c042075802d0064027141c16603803502e175107040700705060341c0f000459580e50707182c40d4000d020350011345690000c2074009000c14510f13801806481d05440c0c1c090503e10b4031903e040c1140c8020503894081075240035210010302d1780f1a9104503030310b10419940101182031510307411907078207001c00c03036a103005120b203010300102214650080d000b100700c8182c00340140c1529403000c0d0790303005a00b400f801005a0b5001801c025000e80003105032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 953805728 1250 953804478 953804507
    0x2e050f07051506040e0a2a08190308070f090510030b09040606080c031c03020a030e011b081e040809121b0310020a080f0903090307060822150b1807 65
    0x901c0300d403d0325034000740d0741d44400c84014580c2050000c11090744000e410100e07c0301001c82100301400f50b13100c030500e041c2148641c400280203442c003000310500d41c100440680010140c58511024200544020081c1003e8040c1c148502c050000f00c0e080d161007a001241e00300380041200800d4141807a080d00200841d1203120703454002d400e0581381604d404528440c005548411103106220110800c034029800745c010764003030554411010151100c01d10801c004100c0024003180c202030000c10161141e00f005000e183e03205820050038010480f00a000c54000e03030b02480d510344840c01c4d4000260300e02da52000b0519944586101043c4000091400c002c00c1c040c16000d555240844140d010140e210365450a80815003c8d40030558031001c1203952a8011059002c0d01d0400b2500000a0b0070900c0591001d00010465801e001401010000e058200c03001180c4a03020386c403040d0b4070184010401c0502d20a43c603a00d0a4820007038583c49000c20b02c03801100c0c4c0340714a6107015071014080b034011a641 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 953806978 1250 953805728 953805731
    0x70f05040b160611130302100f20120a020a03090510051c11130f0608060901062313060e10020604030c1719030b01030e1902041103090a022e050f0705150604 69
    0x16012540c06500c02e201449c00523903441b042006242d581c689050b07404c10141140307101706086140f503a0395000c06411008216406001c2004407410010b144c10701c0307a08800e01c502607901da4000e000350444115010b100b04c81d1821681ca28002071000300404416060f64600c000010b1101503007058900e68109440e0b544001580130b0b901d13480d08592042c001c1341c2c05a041088007006002c100d0242e40500c40354a60f0301c070a00c1041c0c03000250310030b20350401000300c910070050314401e01109030002d685103080b0000340e170041020021840029501c1c02c0c007a0000d810f00510305040300601c152a00e010740343d00d800500b07113680c03a600401405c04420301c6211100001c0d161400c41003507584030340200d90b4403c103100000d110000040e01d80c0f07100e010ba0741e00c040b0f80c040d55039442e260000c00100302452040c1d015502a0200407658011300c400602c050b1200000c0314910049040711441803034007036400ca005458895114807410f4185c600314402c40801500502c19880d9160000b5a91090035110b01c0080e80c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 953808228 1250 953806978 953806999
    0xd110111010603031407111306050f060f03071b05120306090708100e0a0b21070f060f080601090302041410120b04020f0301090b0f070f05040b160611130302 69
    0x500078200c0320340e4040240064004840b0f180360341c0741c0c1c03009080d6640c0180001581720700c0410000f40c0384c021a01007440c0013601c450341002249842c0f4a03058403140156103841ca010810030748400d041c813008003402d041c850300c114204036407141c6c0509030251942c0441100e000c1032480a000f0b0b1150022990b06102d140450002841c5034032540450340290340e0021025138140c1040c003001003000005015401c01d0b03546c1e1b81d440c8825501c030324540c04243d601c1101240c148450341e40c202e080451a4005180c40380c41c0810400c0400e80c0403000125802e114600226180c0f9030500486a41c111644080e50241c18500c40b1091100540070f042c1c011041540180d10b1542ea0350008500f10701c1c5858050a10b030342460008015041844841403502c00003800010a41400d0307444055201d030590f016440940828100306003140c100308030000d22621030a0250515240414010745845040ca07182510102e07040524108030b020741009a06907001d0002ca40c803001c4ca03d000c0d2040800a10042c1d01c104000718 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 953809478 1250 953808228 953808257
    0x70c260d11030a0c05190c0503010606050307080f1e0f090106060306050a0302131803020303040302010e030315060913020d0e15102303030a0507110301050c0a0c110d1101 75
    0x2001c1a6011001c001c1c50410800c1c040585040240c4030f016505400380c0d42d20b0b4007040c00da00403a074061501c03822945013445d060100741400c4400f181c024400b0701c04c040050195280d080205185d1000c0c0c0c48a1154a542e0346542100103501081c0e07003610310808034410700000c640c80402c0e245c4110004c0c00208412030f9124802c80030784001f8440c003500300c03440302414009401c1011112070024040100414501e42d5880c0114130444425401c0d80142c0004c000d00080607428050200154030020041d800c500b88a00c0f1500a00c0b099058284035440000d126441925115522002c0400000c03007151624002c0e0000c0b00074200c3d2404c682194000e582995401400300c1d12120b01625080004804240c01c0402403110005810b8119201000700540c114581d9020401003d004041d5654252030310f140b494110112580e2840f9039100b80d06081c10070491109083c1070f1418070031140f43c48070540095003046540115080300751354024070b040441e603041c000c81d0b540c2103488900aa0702c06c4030807a0341e513 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 953810728 1250 953809478 953809487
    0x21c0f0e010c021f03202703060105100c061a010e03011406300102070b011d1f05090c0301080601170714060d02070308041421070c260d 60
    0x1540c000390701245400d84e016901000c4400e084060a250600042a5511108988203201840c00c41180803000040c80e40b01c81c426050795110306000b24824003200c0c10060006622900140259405440500c1d6a03141452080e51000001900306108110103040411004a010400480140402d00341c80400c001420f05100e00e004523681c3c0702c252a40b98071134a040110803605c02202c0350380c030175400483c000f8444e440080490b000c02d000340010790740c21191038a404880c00c1644040450b02a644141000042620440780d0098031030300c404043d005012010b4280c160b81d03800c00c40d04521075404024561a0034402141a592201c0440340b89071380c0e0b0001c1c1e1300e03110b602020300400b541009078100074200b005414216109002440d9605240010280104903001243c040c5d000581640a01081c02001c00c1c11200001035007000e0482c07841041c0c19100c44132102c000d10324150300000b400c04180400140658040e0400d9041210317114203149400e5805110418450b0103402011103418000f80074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 953811978 1250 953810728 953810747
    0x80a0c180f152402071a09030d08010e0a02040b070303050a020d021201030501051005011d01121109181b03041109040503071a0403080402130e0106080f070906050a15021c0f0e01 78
    0x613a401000c0d428240b1148106041d110300140340c690b0b005100300d500c00e135030a201c080200140c5c1d94543ca510f614215491089a02c0500707032402c61481003005000074041c0ea82200c00960305800d0214041d01c50004c402d00038858441499916071000c180c0d40044c4011102c410704a0780103a000b0721031070701c1c1d0b41c82c20103042003180719950216185d0400000070440e41c0041c90741c034210506143d18400d4034408000c081d0f45220320824040140020520041d2600d244040e80711700fa0207c3c0b8401500c0c000306900314088281020032560310b0b004c00080d0400003400c1d580c0210f0600a4001c40c4d45003014503049540e80c21403202181c1d00441c10581d107103000d0104081d04d100e10b40564580c1c00944494007400141031104141c585041d03280d02c00c1c00f6020809001e103000922143d001414410b1054052604260103074120000030782c1005030410855460040c41e0090b1103203074581005484401c80242e03c0d1401600c13036960741c00f2048034103107286600b02c440c03040d0042c00351302d520200a0f150001118010724 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 953813228 1250 953811978 953812049
    0x311030906070809120703171008030a120207050d0206040213091509020102101505010906020c1003021b0a060203100e0405120307020f030409090507080a0c180f15 72
    0x807100042e1014803030354129801501d00d90035a2144030980c00c50744001d62002c2001e401140c600a03140408281c4c0440550740a0404600d0324040341c10000c84640b60321841125100b0410220545060034050383d044416150b8000100c1d00500080710019480b00c0e41118240d04c940c0940303030381c0281030707241d401584002903000750391340404420006e03040002d2215910503811841107030058290740d03596114039409c29600e60098038a480c0703850001403105165400c40d104640000100583c0342d20780300d8070180080103034240940c4561102ca04100c0b02c805030b00d982090380c45001417540a011850740250f0059440400c010380b45a00c07502e207000320601c03d45005000398420011210700007803490185800c80000d105907100c19400402652444d00240c02009266550390140d0040080802c4050000d00c460303c06801524050344501164000510400a6404012a5600b1004010f9115500700001c0d10000c1000e10114450285a804280500102c85e50703898580007521100368290b003041c84 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 953814478 1250 953813228 953813233
    0x606120708030306011d0301020a020c0f03012304020d0804060804030e06030f190209040c0206090c0301050603120a12091101082208071103030c1b06070308041b080d02010c03110309 80
    0x226242c1c011206103032104800190201846c22020003039400380020222882d240e4018400c01504030104003107004255091440b80c5c0c902020907090b03030141014940146070702006100555240d0002c079190044200d0000c14117040000c000c10103e8008540a000c0d40c001d45d140e07208424203034280074041c8401e49414200074447c000003441015031190b6040210022400507003451005030219042e203099204030009608614204100345200b007101c2d02c0c0d01d40c0220001c1c44a0b04110002c20740383c000c101a14012207500180c040030303e501546808111035000c0c003013080304100a04014216010043c1e0079400203080101040401003080020390010f1400c0454042e009107a5075001401c1c0d10446044404840e142084c922075541400907080d0501c00fa405414504103218200c6800c1078110007580c8102e40600c0440040b96110844940c0701e0341c022901c8400c0e02451220640214040e0300c00f0b44544500045905031650641113f0404606501c080c03084252401250f038160004460740740d0540d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 953815728 1250 953814478 953814481
    0x1020316090b0a051b0106032135040302070f031101020105070201050c0414030111220f470c0d03060b18060706020c0106030b130f1209051206061207080303 69
    0x3010b966805ca6007102c0c102c000003070895a40e68400f0b608207120500f0507103110315050544400340d0401c4644660303680c900c5c1031401da00d045503040c4824400605414204500c1c0000107020980200b01c900b01925004140003041552441d02081c0035030104420f50055080c000400d54450050103841e020300e0010185904040c14841000a5010324281a41d0305640381c4c2020201880044000c0018040001c0d4000c455516150692060b41040e8410a10703080031203c10881e40b0110044442103418a5404a0408c80b401c02d1200098400031205c46800b003242e030141411042010080401d09084801c0d540c02800000c0180d00300e4003a481140c03140d035401c00004402d086403403a41030507048010034041c1840e41a407074910882e0422980384e41b40d0782d0358140c14414803031045411584451024600000d003003581ea01c1448071850608010010744d69070705446100c5010301d942c18081d1802401800f444800780e041555241d2040e01c00c1800b4038502c4840900e100300114100013654122001035245 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 953816978 1250 953815728 953815747
    0x20304030f0f020a20040b0d0503120c04030819200604060f0204081905060105100c1209050d03120608070305120d0204210c1707031106090301020316090b0a05 70
    0x2500ca40c00b00b034408500654550f40c00150205105184401031201c94104203003c880a010440346c070480c94a203d80076038403242002a00000c201c4107189114003a520440c1c6480e00c0c050172502560f0402001000041000c50320f100b0303031541c14071000200703036107481826003001c0902c0c01ca032540c400d0180306600a1000240418010740260b01d10540c88800180380959410602d414244044c00c03407c0484d41c441844418000104843c80c05080212040020a1394591010740000038a407801444034140280b00c10300f181c003a8603244000d04015000c3c0c600704a0314a4014840c60b01c2035040c5141d180b03800300100301d2440000e1a074098a82c4600200b00d000074000044482e07402111444050070380030480451300300b64602c0468080140350b9100304960307455181c40c0c5102c640903044407280e225050000c07403541c0000207103802100c3c0c1128110703018210560104440340700d03c4108035003640c000000e0050004400da2422088141669030000b61511070501c0c4d240c41c42a0440c010010f002031109621 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 953818228 1250 953816978 953816987
    0x1a1801050d0303182108010806070509120a02060a03020903150103080f0315102a03050901032c0f1e0c0418150f0f020906041412010528020304030f 65
    0x100941c4c0940c891155485940c41e070110304d5480c00c803070080403185011060300700c0c0c0101d2028058203100000e40114030b0300e100018840c2c003c403c0d0051043d54209424200c500c4140705c1440c1040c0c010300300550311200b1301c6c405000b84d03210b1412203000f88100c0380451500e1410000e0241070380d512901861402c402901004640c0c4c0020b010000025051410070445540b8060141200801519581d210206003204210319154500b0000400750b2103003400d0700026031050407980040030900300000e0407030b465808102e04042c2c030018040080568801d204001c80c1c0065030002180c440004c031940007442016040078034101141500301503100220058051610350098482050000f900100d0340105485103450001e500f2044840b141d03613070200071080101801900d01c541030400c0150301d0000d084001c61250b101d41d22912003100652903072201c2c25070b520090000c480cac10050092119082083c0e5000d800080f000c03040d0740340414029603448850241c020703607104680544441014200034030040d00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 953819478 1250 953818228 953818241
    0x20a0e0a050a0e061f080609010806060f060307030209060d020c0d0203070807021c020306040c0e060109030308010306050c1c0b100e0d030324080a020906090405100f09061a1801050d0303 82
    0x17584162420700d190291010301c0741280c4503015543d1500c0d094280041401040001a0001032560f007200c0300f0480340f900d0303c116111207414207032001948c07580c4506003140207002d480c00569001e103001801000c180c0ca01d40181c0500c4107048162030554003a2002640c0d64410740790010040c2500307000c40c0c405858411000c850050101e00452894207140c1c1c00603080190407a41150822a0030704103001c03d4415260440d44448203013000042c1c542541c0303002d03000c0841440001e003481d8a40d4006402500440d0580700188804800c1069003c0c00c0c00185020700720b901c8086004604404581d20658403900c9404801d00b00500700c07041940e943d8a0480c007501011622503c0481602c01001440d15024030301d20050062001400288601e8410402d9154000d081d080c0709484041c140800b0820120b1064041070080d440010164600032a41c2c02030f003140803018001d1031400004c0c0302180c0d41b080050f000304a0464402409807a10310740141c65500038002c00c0c1c3c101884002c55400a40a0b91200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 953820728 1250 953819478 953819491
    0x14010207051008100e011805060d0803131208060a0605161506030308150303270d12030b1002100906060b070c031506080d0806120709020a0e0a050a0e 66
    0x111145074035400412455498242c0745000140381104100366400720101100141144800d000f1a9524080c100000c0ba64142c2d42170414559442c0464100da648529001d1300039408002c441d1645041205022043c2c40408207071030390b1400143c81c1400502c81c3c10740e0b41c0306400040142c20001d0a001088905420822446161100a139000700c0480c000e100060601d00051501203003407810352170010032600e005400c031828a0a00e5805025650f80841580ca83c0658140c410803403440b0901911040c2c13030b404204a0708840782035450030500581c1c02034960010820307281070114429040034002c180c4140c030050b40058010880044111b507054100c021190300444020800300c1d2a501010880d601a010813506003422144c104104181480c860308404220b010030031003185001c600300c0d00c80708222031000c104000800001c00d5940c403d4580c8040c1c0002da4106c407041e645400001c0000d521001c244d0000c182000500002807a00141403003c3e070700b02411040c9042e14143d0340040d5994060082d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 953821978 1250 953820728 953820733
    0x20d05030718080f0d0323070203071a07030c0c030f0819060914010f180903050706050a0b0a050a21030c0f052406030c1201021303080909180601140102 67
    0x11020000e50b841405805440c400740038101540980d14a1071500c00009400c50906041c0150802d410303480d4030303080c0006c1c004036084081654956134100d047d489006c0c001042103800f04030002080d0340400f6180d105080076241000006024001070384c142c500e1048c0100052004522181d0041c4074440c140d0b08400c070881d43d0301924408411030803e40d103113a04503a81d4103940d034009101c103210310100706004208e000d1541d1407103414481000c441c074101c00351070030b0340079100e004110801d4842c0045840041c2c2106c2c04000a041a0000700b0140801c124070521035192410045410b103070244412080f101032040001700c400e0345008048840788544003c2d01072005191545011031004d007506110b03140b042018140a9490b0402d1062130a2000540036801c100311007000f0607518002501000c50000300d5030300300c000000403402c0303000e4490810f201c555012940301c00410010b42101500062900715070882e602da032540502c2c00e010075240820031099120100400031000d103030180c880110018410b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 953823228 1250 953821978 953821997
    0x11d010309060b0307060203071e021302031e0103061d0c01050702120a02121e0307030936060323210d02120a1508121c0c03141006020d050307 63
    0x904005176544403a0258100007003030010401c40d28188074109a401c4400282c1c0d2119402107484d4541c60920400b0142d070003c08140c0340c0005208144370300e0302c47d200c1500c040d0385a19010000d4481040d402003110345144d00d050130b81c500800d800208104c180d490070305140c020740070001c90721402d55401d0031a0003080070600150312a01102002150540001c02d43c007001000e24807018117501403208030b1070300188582400298800641c00032550050214452884140314001e148601c2d40540709400002031550a4081d000c4d4210300c0441c0c1c002d01042c0031408290440002c000d10740b0030204404e8000304080030300c1049000300c44106481da00c80d402d0400500303618000403a031100010000f00411402000112643c90003040003030104012100c0e101464442840d58a003620900c0080c0e4070070104c2c5040608000c0d030b24500c241150740005000c010000f030001740091048041c80030303448505400141070000350011180480b08250300800c00b4006408080354031f80c1002d010f07402000f4541c1c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 953824478 1250 953823228 953823251
    0x1b140d1112071404080a060b0f031f0b0904211202031512010207050709020a1809020703031104060207140409140c040507020d021009060b13020c0c011d01030906 71
    0xd04240901492003229030b040400c0301a000b60590088030f604210100002d00c2061030124003030000300d60081c408645507100c1000141e800d100340d2050780c1c052040c003029007041c06a50030641c1000c07140d0b51003001919020002c0c490136060484020f0034000c906e10800b1100d441500d1514520765140c41c02a070420560042003099034070941c0c0b101040f200200341081d451420a840c440c0310f140c8131008520303142090b9030700c0c2d440d007a540c072400103150740c0441e07034800050058128004210715069002081d50b1264001e00c000c1d089544113500091401c2802c0102c031040c402100d0035036100b81c0042000030320b408500c0300c0d140c40c40d590080d003064803042000c0020f501c1010440c2481d04039406040d02009010138001242c800518600c21903021480d542e1103190080b5543c5140b200b00720005c22000d129060500181550b6410140c000c511100300b01000c0300c156001d86580345140c015104c010500b500110703405503001c2107542810b00d002d20030045560007640030003103842c440c0310082403043c2c505 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 953825728 1250 953824478 953824511
    0x111e040b030420040e0d080910090501022d0f0a141b2a0108060406031205070507150504050f0d060203090f1501140d110402040f0501031b140d 63
    0x15202140c00061580c583c01552401076958241030b54103031401c01c11340b01d40e400880d6071a80622074500900c0721b620701141500c032080c4055580c8000e40718043c880302c000c40c078005000354450184546109c40754941841c10000c40704100b0310303d0454941b501d00b420407192101400e58003000c000f02c240111100300303000c1c0000910181c01400b85c54500004a9100413002034104903801a162051640c58482c900d50700c0c0b6664080110340320f086c43c002c43c080e560400854010403041e003018110140702e602080801e0361040c01404613600c508162089180c0d0b6945c0307110030025807204600454030a0005000300e00380142e200180c45c030000d003084414801c3d0f4403424200d130700540301c08203e41c0007403813201e901d41410440c013100115865000c640c552b241010b5807100d4507000a003c0c0c410810f8000200c00d0045503018004604001041155279540c0d810780700101d10172601c16540804d007860f11942242c0f20110740c0c20468103070b5480c1c607a0041d41c0000b0a0381145e1103c2c41604d88a587c030b00000911005a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 953826978 1250 953825728 953825731
    0x3030513121101021504020a3b010f0b0319090503070f0602181f050a02070f06020a0606090e0604030311120103080702041103150f0414040c03060c03111e040b03 71
    0x5102da10241118220009040c4429000240c03804800c00007407000603211482c80d00b04584211905914030300d8600e400c41d00d54221030120403035042407880c1c542c0706107001001e00c50403580303840c1c203030a031b201e07900d01c0c907502c0d180022680c16807406909500c00c7d8107107800c0d42006503c00e1127102564a44400fa6070350502002c0d00110540d1866030210300140311552400640d4103403081190444491914403100d03e817290031a20a80c8104100400d880341090b0007004800054200409140c0a8540f01d0200950382d44c814501a25a03500300350000410b035899100d80d14852084001034030455590752404c0d4090200d800301d5840401080049420b000401d4000034040e612802046540d011140100001c0d25402c4290725500d090800034014100030003441d80c0701c0c4120030758420510404e00000100140502d09081c8503c07280c0348204800c101e40c02d20008240c030701c1088200480306045508404590902a0740039115204124450140380a41602c047d000042c0c00194907180d10380100020b90b420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 953828228 1250 953826978 953826983
    0x1121a090c030111040b0d09140f030702040b0f240c0709050412020d20031c0209030d020c030c1915020d02010501050f0105040e060a030b0709030b0609100303051312 73
    0x1180c1c800780e0703a2070300307008260104820a03d124181414241626214425019040c51559440c00c00b14204040a021406800d040805032102005ca5002c001d44962004030100d00c0b0741d1800701d4031101803a110034206c003071b044040c012070220680203c048144200c00c03101c00341c10f80001c0c880b0035003445040000e003024280d202c1e40451942400e180420503c00e01c0c01d02030003950007487d022034605034088005007560804103400450103954050032811881a120a0141150544943d200303582c00da8008110490066044950414a498049844400041c5181c0d4150003008241f00382c0d2528840c19070010301110582c0e1411a551300c1c100e1b414980c160021405030b0016540404515020701c103480c010501600d000101c0204000020000d1185014100014074044041001d6803a401c2501015650181d03001081e400d1500780505a44a283b10895503032074403400091450410b601500c1c01a040c8070301c0e44048a04550b820f8a2582059401075400c04841c10300081542c4281c1846030144d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 953829478 1250 953828228 953828233
    0xe0c0405090a030e0d0b06011b0506040c031109091e0f060426090306060d031b140118050616020a1208150f030a08030601050403060504060209240301121a09 69
    0x292038040d1038103290600442c4217102d90709800000c20416014581e200b2024601441510002c0625030380003030035450003420f54491a0100020006d26481e1041541e0040000c2c0405a08080400c4000740084a07001140d800c05101d007021884040100c240050a04050b80e006002c0380c0c6c812441d280c4111825240b410740342409911280350408500c4515000e85034461620172410042962200054401406465120000014988600f00c1914203001203440000019030720b06010920007107582441005500e0864a1804200d0021140ca0050351001c003920440c2d0703c0c881c07803000b07000010641d281940241400d200c00505284440b4002c5000d5131a8810300d4100601d40a00054603a0b0b100c5000710380007005050a41da00040000c001540551400d42c3c0345e943c4e5004031024040c9a00082a2a00f024148420069150050305000700180d0b2900c1e00c00b02c8803444160031a20b17004441031005410001070020310080c18041a000d4042c031300f5804d81001c8096100080f200464050b000358 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 953830728 1250 953829478 953829493
    0x2a0126010501030c11251d0106020c0f21071d0405010c0806090402040504050c04020c101404031b0807081c1d34030c03032c040e0c040509 61
    0x2d68243c40f0340c3d00b40110382d1625443c007210303071080e507540ca100d8451115191001d00c40100d0910b1148601400079011140c1d03840d007165100219540c005000317024031000b5008080b07100001e801d105840200c000c40003000b0720034a8805e005044010b500100710900d9034050104045004010302c22400124200840001c26524050078410708507461a5184e00402c26403070184079003541c0d01310141d0b8000f40c046900149940319403500901c1c10720b1418400d80c1090011846080c480c0c0c002c11a154803401180c01400030600c0281d48040e180811075000b00800d110b540c0d1920300e00c1d0455002c55810344103035a003925200e4507465004c203079044606050800d050200d00ea00700070303038031b40910f980341d24069066002840c03503403103855101c8002090600d0142d800040c05800c94659201c00e840c8a81c03440b12840403240c0300d00f400708103004540001d4000c42c891041c0d030461f186c003000c0701c1110244007009486d1100601d0080001508440064007180d1040002c030b04c0c400e03030301e521855015800ba8001040403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 953831978 1250 953830728 953830739
    0x21c0b06041d0118050714032e0314070b070314041d06040e0d120b0a051008090d020604080403060c030b1906020705090f0703050c071b0906082a012601 67
    0x76121341c0c04400344881c100740c18410929080003c102080b030101881c5616513a0300d05000c42d030700c64000c4c0000b40140d1805000640d03030000c5028407007507074080e500ca4540c4100b0504250741d20200742c480e20704c0b031b00004c01c801c41c04240701d0710300d840c2c203082442c415500c0c1561381c90795101d00c64000003491088010f84010f000540c40c0610039094006840c0025000c021580a0b001d004880c44506801344582ca03072562005564480048002500c8024011899004841c8004018501c1143c281c0d00511071902c42840e200c0c00018a03d00c9a9032008245141c5400d43d80c501e0050000340301c0840600d42c5542000300341c0d5495840c030844c8882c0310b0101c1c0e0500352414000074900801648840c0c02043c0d80001c0c403800e02061508103621004a0030041845d1721404111051489660310140903602d1401c0300302044030744011180e08407a40140c003404040d0f11400c1d066122a0200c081c45200700c07035003080c2505400b204004c038401d2001410009038190031180e0f42009101525030901c58800ca11005121 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 953833228 1250 953831978 953831999
    0x303113c0f2e0b0a05060d1404050d0801060c0b01090c17151c03090b030606040308070501060807150206150f040c090e0a0e03040b09031006060c020108010504021c0b06041d01 77
    0x900303401e11420303c1081e01c003202003008070300039000760b030302541000444a98105141c3c01c074080c000d014003c0c95105190030705000d91600d00d0301c44044001000c10000144aa00c254844409107401691b1400c071070b464007a119006001d252490b00c14410740d412a4a458600011078600c103802002034064040c0c080c10800103040c00f2403002c080d241002c0c0c89206c0100f584418a002520400381c1e40f9996502c1381c1000804900640d800245000d400080d0f501c100031041d00000103d50010341150105521100c00030a00e00494166030016886500018409500f03550484544000603156072544c250303030303404103082d542c2c00c03e9820081241c0d203804001c142c1010020907808207001d1408c01946001d60721941e141d101d02c1c03003149400600800c4050b00c0b079500344501e00d40c03c0c108020410005a0380c503005000c004030300100b40e000c18160340002699061a000b25141030b4000e03042020f0552901d6000401000c0e080e1225030044000d02c80464041025106880842403407219500503602d0a4103070784 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 953834478 1250 953833228 953833303
    0x30f03040317190c1404060507170412052b08040f020a06031d0102071e0303060513060905060306310609111e0904080a05070c0303113c0f 61
    0x78104181d010b00040029178020944d01070b5485480c100d96548014186480032800c40200c640725140e000500083d0a4100182344035418411011fa4107881d899040502c003810280010a90008411000b07403c0302c2d03c00c3c0500303035001d88940074008030501030381c0100e030903604190080c1c00842d64030800000e8540b140301109001d86e803284004d618010581c0e071202c0056119419225610f002e10740954101802a0404801790038040c020740130030408028540098503691180464091800d000308100b03080c007044c500c2c410f550410f0170601d0b07071080317844149000785404142c0140d2045090170b280042c94502489144500031110396465541401c1003020300f440050107003c1070940201c0c040340035240d100c141a8480d41254990f42c0710120b06c241500d040c89601c2006100e003003030b040701200309500806002e0712565101b084881c488400d85802d54980070942d0500c80c1052188045080c2c0c1030405103d907118400901501c21001a40c0703402481c220749c4007a11a544031841031856400300d404510308 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 953835728 1250 953834478 953834501
    0x9031b06060f06030c120901021b0c09010e0a0209031203040618031215051f0e0109140607050c0603090a052e09060e10050402130509030f0304031719 66
    0x240601d08145001490442181c2006406014007000203a00c50816505503620180701b14101d0703010385403130011503000358080720044400804018040b08241800101402c40000140c03c1d24026401c0002100a041c8018002400d0036020069148292401e002400302c2e00040e40320503480e8101480d00505803805410440301e024000c40c040b03030200307500c0510701042202c41e01c030005402e18400c18080c5c403540300da004560000c0c5a5000f1803030600781d1142030124166103075104c04894515600443e445942d51080b000c00701c901180920302450300200806071707030b0310440072030325031030640000300d4525003080f11030420580100c10f04106000007404000101008a00740c80600b0491210301c00700348000340005c1c082c060340ca2030700404225044d40700702e40301c504050880388031080f0380c0c549002030401146c1c101d01809400040f0300c0b50700c031705000d25801040307d44040c5042441310a901c40c880c2d003008105030104a4a1580602032421801e1134901a088010601c6000c0511140144c240e03071720328900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 953836978 1250 953835728 953835733
    0x1050a0e04050a03050310120b0711010501121506030f050f06070e09072001060f05010e150f030c12070c0b060a030c05011103040b0a05041703070b01050607150509031b 74
    0x200000030b4800301e0702d221041d6260a003991281c46010178050a501c098004058260201c9012400c0c018040c42c014425440c5650f2500c10384100b490550981d64207104001030070702c4107a0114002002c64818130340704c80170103d000550741e55a0700c51054405034044151115001600d41c01c40600c0240710b110360002c210704281d81d03070812100100d188018011304c040704000118540030080041e80884d4400145401d00038440715496405112244040b885114040340304802c1401140c104440c000720001e008501c0242003055a0b190801e403980014421032001c54200a200501d00c51030080601400d22646c41c0310500441e8034001a100801a11451103441090b4040001134070a5a100b42641c1c0c0030710301046203003050b482c0c00e40746010300d801c8041c2c00305003c50110045644400030300b048070410040d1b00441d19000004035100c0c4a0000042e29002050006000301c0c1055401040740d50b114800024214407030241190440b1010342c0c126803941c100141c0c4030034101400041d10721183c40da502 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 953838228 1250 953836978 953836981
    0x1c090f08072103120e2d0d0e120307060609050c13051003020d020d0b010f0c03050d0203100510080f0942010305071a0405010509040e010e03070b01050a0e 68
    0x7001400309000c2c0c1c8841d0700d103081c00c6503004141c82050101040382d018101448400d003501c12a58a441c80414964030050350580004009039410f03007112008880346014090b0241c803041c0454441030030040c840d03008074100a2901d81180d0800c0206902d5002d08400a0030724201199007094580185c11000c0c1c60500f40810002482c1108804c0201d4a007110108180503d040095000c1e020710300700e010140e840891490800103942d08417004080c0240d907480c00c800c0c201c0c141030382c416010203406000a0414080000040001d40c000c41d0424214141506904c0d6540006200403008a1043e030005032103106001e1044101515250462544006440c07c501e61181c2c0e1090540d00e0f001072501ca04144081c01034080d0303014038160710400d021000845668482c180709584502510603c0309035001d03c1008803218402c0001e8500f03484050f91140c0c03a20118004210140400d071344131a82075541d07140351020400080005101c0c262081e0f801100540c905400c201c0c62000581c07020049442100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 953839478 1250 953838228 953838239
    0xc0602010609020a0518030c0a090504021507150506060d050405010e07053a08040b0a08060607020d0f1a01090b0a050402030f180a02060a03050f090c0a171c090f0807 73
    0x400b46c60303010305880030300c004da240b510000a10307041c481c4450715000b0600c4540031070204140d0b00b010744154000e0707070044501d04c1000c100c450300d88240c1a01038074581d0840d058040d5419030707411081e04a1802490b0340e082403100e094140803036009940848060707645016802d2158014070044005201c203c1d10710012550322044010441e644543c11050101c140003564000b000f9210f501001176000603201c0e4070303242c84103082d50640c0e101200c03000102d8894000100c062904104861003282d01800002c000c4d030041c0d460044c4c1e07118141045841c05c200c0c00c0c45080210400070b859008001b4240081034640385602440340e03820407500418080c60042013008005451502016000b181c079110f00d001c800e01c4044035a09241106800950140700000c2181306694035401032070040a50b50980c0b0036603100c8075071960303507035911207103080d08a648110204081072891204009030000c55064a40b01c030300646104d03003018100b82046000c0b0720300c4501030000395480300c0448080e16819000304074032400e06 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 953840728 1250 953839478 953839487
    0x605060a032004020d0603030e2d1521070f03060b0406080c040e090c0a0909030c02060f0d060b3402040b1503040c03051c1d030f0303040c0602010609020a 68
    0x704802015100b00c0c0440c40280e200c582c1113804104290508101c5036440340350042c01444038180c19441000e0b84110849000c0568000b040200300078024034050348100020310481480820542941074000e0110780302c040608114407045881c09040c51896103000c2d4405080401c03161042c904040c54144144901000c2008035400d6800c0390401011a5a84144403000b505c03868000a003030350400c4007880008000001d890365003602c2203a01c0a5910b845a01400807a00c0105000d400910645a81c0d070241c240310009005284112a503146061458003084090368003035030208101d011300091146540340c0943c201c024004c031400c00000044046c2c401124410000031010380702d25500c81c80790324a03941300f48031a0450149505429160315041c2080b52110140744815503403070191680401c9806001004481e11805a4680322034160344101005d000e20005c80c10a50140700e0f210350215100701c03c00240d840380c0d07c40d401c0c15030100c0c01c08200a0a40d40d1070380c8900c0105e170043c0550358890390003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 953841978 1250 953840728 953840753
    0x20307050a140f10140c09030a110a23090709151407151505032d03090604170c041803030c1e0f0212030609061225030605060a03 57
    0xe511402c4040380d49001818480c03080ba0283c600e120351112044070100c80d401504680680c111403198503a00d240000140e03210f000d01e1182d060700f0511411000525440c0145002d510140039803034416114040c003c11864210250250801505603032541131800d1400c2e01c0d80070304c00340760510140345480058000b002035011403809001c850725a070b401c0d0604c00360039510019001a2080054003000321400014803555584882d060344003070f0003213100c2c20f001540340c00c0801d51007051076150905c0e041100300d0490884c0503411502003000307400300c07031741d12100900043c04200500013412030260000130316050101214a004600b44440039181da8180e0890056550301400c1c04030f26131818035412141d03201502684481070080c0502c00d004590304c400b10640c4500d1a800b210740d070340380003000202d45002c2110703240d9202c0242000107006041803800603207070f0180f2004039501720009001a038452500c6150105180755002d004000384801405003d412034001c0d1555900d260440c1c580c004107071003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 953843228 1250 953841978 953841983
    0x120c021324091a0609150c03091806010f030603120c1406010902220b0d050604091704050a08010209030c330d0c0c0209040209150307080105010e180c0f0a0b0c0a0b0106020307050a 79
    0x802048007047c00500744112402c450000707080b802800e22002941e0301010b001e6881d40c0c00151420507180c00346c0e000748150030580c0d80040c500913482034008412281c4a0b50403004484a170020541404003010170051a406410008009038071125a0100786404891141c1c2410303900c20300d0403080219000010480b1013a23500d0b00400b0a01e42d59900200700503002d01c2c40000e140028408840e0240e1000034040c01c10b490089030881081565403c50700e0a0b802060701c0903070305802814040c1164a409a030910090108043c42074200c4402c95203d104c4a0410315141100c0074001803503901c11880c2c4c070801c2c03081c0d03425042001d14000d00343c0208100c0e0000900090103019144080340605546070a801300e20400117085440c1203440b08a0603001c1c1c1001e1040030024803034100440c1c1e40020010015181c2c0c45803c1c003c0c503e00711000d0811017034580b11402141c02201e50140851001044001050360107101e0004080740685c0d031a00b038080010581c40441150021701c00c040005d03c02083c1d0802c080d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 953844478 1250 953843228 953843269
    0x30c0d0f0813030c0b15040e03130b0703111e0705150a03110d060611010c14120c0d0207080703090f14130e01051003120c021324091a0609 61
    0x2d1181c40c00740d810031320010018101800e00020022030458098100492900560703040c080300303251000c3c0388c0c0ea074000c2c130100c40811004400309110079200c20000d002001d000c0d00c1c11100c610a03007202603081007202c902d145645066415455002002002508010142900c0d60441140c0323509c068400c500460710680c0c01c054451241c80390103504941a103005c0c5040c030508102c81580c51101400ca08441e034110b0080e5400c2005403070f243d5005054000403c0342c1d0fa510307685270281c03c2c0d04c8100414001440c46040350000d1098141c41710240c40038240c0244101030417580d8261504010f801000c0036880701c106107441308014042c422204501c4240f81005560340c00b1503203605031000018166080d03000403158030700010403c00303141c2e00340d242e81160301900680c0b9a01c2c4600ca4102c441c1a200a4042c2d00003040e0350594804440380e070700020001d5840209101c00d29150f00300c1c084000c415138004206140c0b94552803c1200d462030002080b03000844040d49450004d602158104081609003650030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 953845728 1250 953844478 953844511
    0x70f4715040f090503270f09010302010810080a030f0206180c01030b18151305160c02011e08010f05010c0213020304021c081e0307020c1011030c030c0d0f08 69
    0x3868030360803488020ba03014055171b45075a0a2070151001201414016010400c0140000d00c9402c1006510b01684800360001d5a181c1c00c50300155503400300588041004070400c0c600080c060814001003000611a5640c82000f01c0220402494907070003600224440071000460000700c0302c0020392140b06542030038041100700310040007030240c0780d286028651411004041044094004090401c14001114440e982c050400304000c11110304561294014003e01c05911646008641151403644149480f40d00c0c0b40c40e8035414000da181026071880030500000040c0421a54270190002400c42845c2c8a603005140c0d8000403003240100484004d11a40000402c00f9511803200410724a0220071150480400d60701c0c08481c2580204040c50007041c01c0c00c40a124641160206d1340079000c0740e40188143c0701008100410350494154600c1400b03030b0b420304003000000c248003401c00444200045d68448400480345130500e8103a030b006104214074040320301d24140c0c101048030b41040f40c041c500400c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 953846978 1250 953845728 953845751
    0xc010807180801020d150b0c0303060d060f0e34050d0c0e010303110606090c07330f15030b1609050607050a030906090b070f471504 58
    0x620060300800b07429400007440c64500003841d00480c0c52a5109540c0039140c40c1ea5213424030303d0740540418842c10350810404110146403070030124500900807180020014185e545200031640c1b80303904502e0642080d14550f01402c1d81e400b5400c1d10048121000001000c0189403e051a20740e008142c429182104140188054030350341078041d0a2004551040e540c69060161164030b40181e0400244151000a042400c100a80364000c0d02940201400c0c008156070b51459001040038107442c4002d0603204080c0080b2002c1100c5001e49602000101d80800c0300302e00041c0d4011018060030901200030403c00204200350b5168421070107944000c0f0120348a000b03c0f60308480c0e500047d401000820301c1014002d01048950150307100e611030a07001c0e44e46560940b41c2001c10320500a03030301d00501ca03000c082000c0400303902841d445101040c200302ca0860141e100940207030b02c070303401c42c00c1c01c0744509004001c0f007114080388201d0704d10081da0304c0c9026041c0841501c403012042e401951500e44000c81c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 953848228 1250 953846978 953847017
    0x70516050321011a2502150412020a050d0f020628031b23070309030209090706271403150109050601030b1e04180b071e020c010807 58
    0x2007000044002d151880007600410352044400c1c0075004a2401c0e01411064940403981221158400c00c9441d1802101c450010700e14255104010381e0001d0141c450b1011201011740240040d12420b42c0031790390307510340740184454548590030103805505060039800c046040e4032810710a1590440d040e940e11010528030b0b400f0340780ca041007c0340700c4441244c1e1344c2c48140c15400c000b410707207042c01900c0d40c6031880100c100d81884980d6a032844c0303030004449042d641c0c50000300078a40b16010741401100c455913540800c4001d8800c40d0f010410790080c3d002803280301d03800300c805001c08241c20a803c40d220004032080300600454400c0d44001004942008a0783d20207120040c0c402d2140041c2000715a924a45031000c5c000827150280064a8440c4035407007444c15140118400c0c0c1c42c1b801c2540354a2076041840002c003180502c014140442241d20b100003200c03c1d05213403054650741d4609401280100c621820300003084036040a54011a80b04155030340d0183c6416800344507858034805880b41450f2488 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 953849478 1250 953848228 953848237
    0x11040e070906090c0e090f0106180e0a0903030e2404020f03060a0e01180f1203090c0b070308010f0b0313031808011b020a050607080606090913020a0e0705160503 71
    0x1010740c1403440000320009107500404c080701c059200c0f0100c0c16203000401021034800c407920f010a0050b14018420710b07110320300c9804135100010001ca036264070b9081d004500325044502d00e10a94032007190340105540360143e4040c614014001b44551405074070904414001c501200380090517000009055558070441c4104d140340140a0350740d1402e0a004802c0541142000358030213600300000300030403010307001d45900c41c20341041c03201c3c022551699401d03402103003901780701742099160b602e454040707000c00611074003c25036840c0c0d284d91111607190250070060305034400d0491001e4110100641c180317000c12254451000d140040540010307150039034a01c020b0300034000381d480015030081000703101507004c2402c6a802c41c20490820102c05400c90b40da00507071200800903004003002c50321250040014a0f0002001829681840c7c03480d804600c104004031400c44800c580803c2440540c00c00244034009000c524252549a2412002c05031080c460100105903020010300000280b10081c03081c1c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 953850728 1250 953849478 953849489
    0xa170706140d060b0702120c030c190806071215031110090906080c183c070815040903021b0d12050403020319050d051b07060819050411040e07 63
    0x70000251540c0c0c1c504c400d508502000c81c003030070079058814a180000528400300c208020000c01d507180d0313000144800c1c0a070040343c815003c441072901148100c814090b082c444d4903e6610300c0c80c11249001c0c0390013905c01c0300114075000c01c4403000a0010504801d000d40e2082d90580c1c80744284105124115400034003680403010b580d1410a020135604000b15041c5614501121001c1481c41c4125041226032010341c1c61070364814801e1881c001040f03103c106031016000c601d01e072411880e10709a0700000d182c4100c51481c0080c1541003001180d0100c5e03030b50742400e80001da07020440f801880e41c0196075038a03040c6002020007440c202d007265a070340d848a00c4021650140720103041c61100030000e4895040360204074881d01070403509c00d6044201d5000c01412940190041400204021080e52903034092651405c4031b82101d11104514a07040207180c008011580d036045032071500c11200341685c0d2440e100e9000c41820801440045a204081036407034601c122000a000d6040d550038500c0c000581d40302 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 953851978 1250 953850728 953850731
    0xc06050a05191206091e111b03070309140102100203130503070506040209280506041b08040209060d110402030705130605030402011706060307030f06090e03090a170706140d 76
    0x580070b140d800300302e894201c00411010701c0900d841e03540100540d070341e4400c203000b07880386544042c01801d61600000b1641c548044400d280480c6074542c12414105090000440d5200044600070544e100312854020007503000b8018000781e003240002d490704900e11341650710035000720100300c0c15040c1c6500000d1696024080b00c0c0c3e030b0303c005d1600e9920f601c8202d4040c0d2242d0440c60014842c4000c5100c1d240882e2580070000f14420301034215000244005801c1c00c3d0400e944041c801c18802d01e0040c0a00307800b02c503885c0c1d03c1c4503203030920410508085c001c04840c00303140800074200c0043d076165441400c0c80d40840e80941c503070b03844d048115490701610061031795801074208000b83d2140c01c0b00003580103c2c000e80c0e034010301e4100ca0054990610007914065007100040000035842c2d80700758001c4200030840840401c115641d4407510040e01e40c03c801d0380e540c64000060901403443e03c995442c000f00081c0d044200386400c040b0100340c4440c01403240d201400790b00350032010703031742402c0b022240055243e540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 953853228 1250 953851978 953852017
    0x51f180510081501140301110a0503070c0204020d0911040c090303110a170a030606020a0c03021c060c02010f1d0c0105130b270a08031e040b030106030504030207120c06050a05 77
    0x18031001e0f050a100740a80c40c15401c40b010014141801001c2403d0103410b411480d100180104440e254001801242042004a50100141d8a83c00206550042d141c004122945603060200600700071501c014852031a0200804141d50007040e80300880c4d426003001080c94100185450810603040d0000340320925036102c1284401e0340b1000b4000103e0b1a550401520f41c80f5082680da03400d481c02c0281c01c542e86a007040006203850441d41c82c2c2d0000901c0d1346800000c00d84c2c1c030352090791401665000580d44940c058031091102c1c0c840c5060b481540b0b40410b24110401d61190b45401020008504102001900044a402c000310040003042501703c480c0e0707142403090943c4130b00703038000032440e00010341c011116545240c1120201c0a07244403801452400001045140c0d401c4441c01e889400b13000c052100081c0218054080e40c02031009072008202840c040c90000e007440c900b40c2106001c3d0640420303610100710780c060244283c83c0c05041003680c400e800c0e070701990b0500540951551518940e03a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 953854478 1250 953853228 953853253
    0x40b030903030f1f03240e0303010513090b0711120d140f07090e0702100e03120f09030403020105031e15120102040602100f1b03051f18051008 63
    0x10085206110101c20b1419540b5031890300810303161300001320352030020150070a10100e4042c5c0b19403070302680c2039000d02c19003181c6c04203d54207851001040209030303000440100f041e400c20884110b1800102c0303404102ea011031f0b55810030fa446010307201600308902200c60704030001c010003001400d95070101035145ca0358911161040581444800c2c01403c81d20b05011410b0b20b40442141405012680c6607503648508004050b20030f020001c201a0842c0706203500c014155640e88240c82d40c2324000c0c000b441c1d50304950409510140c01c00f030108a900f1448800f00401310601009a07001d40b40d0910f0616501e8598140d0406030b40301010051015200000600400c041a0a442802607405a9420300308601d21030001d800c03809640b10b0f60300941c024030b00840310491590b11136911140c061900040c40d80e040c420600c040144905103901203540d603014081d011640440d5071407040c448181202c0b4050419149690200e603401d030b9460b01c1625900070501800c44052a00003505403d011244040c003401c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 953855728 1250 953854478 953854483
    0x30403050708040e041e0b130215040e010806060102030f04091a040e010c0809240a14010b031504060b09090a0603050d0c030314360118060c0f0905040908040b0309 72
    0x3a034085846d1321802200803035441c10039204046031a04158011401d035205920030349907903031484007280d0241144010010004541d40900041c1010078000000c641c102000301c0d162800c0645001d05641c4248031020040c07410300101c03019180e003d8804580d041c180400181c11005281c841076003c0d0409000c616400c50560100c02251465601d12600c0d8403617440041c2c44e01d1110100b40c0740001d200d07500302c0c40036001456494000088400003d0302d48804421008500020307003013100411000014468101a011050b44940c1c1c4100c41c10860507140400194251140e54001c2d40220040710000b4507a480c0c80e13004070010358105082e12403400312590000c1c010600f80401b140441d1074800c43c03038041d1821680b031b5440f48005481c99208004d54401c41b1140c161710641e50b0840da609204c010303403005406e010700c11400c241d60300f0300b0082c1d142074940402982d0380340c42c0180c1040840d09441c036020394402d84440444030140d81c0001e440420b8144041d0a03c1a5000540724043c00002c2c006900d100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 953856978 1250 953855728 953855731
    0xa0e120a1b03020d2f0307091e2a02011a0d020d0203012c07180b1915080f16030c020a08030c030114090c0a0f0e030f0f0c010e030a0602030403050708040e 68
    0x92581c4910401c0540c0c151107810b000c45440f440d05030740051f00078484840c482e40010240c1d003581d0000f0301c09101c410244019541341c3c0031005a0031040719010b8900d0070344420b500c5400c40c3c10303000902c903d007002852071008043c0020102e10801019a4090075500d41d05090b00e1100d070003800901a4181e03050010110700e041c44a44080c88004503a0132481d440c000ca800000d562134024200420f0002d0850007001d40040ea806560003c119552038070b900094a01ca00c00514038550090341c142805040a48901c0008007a48000d000076402c02002c4000c1d245a655204c00030300b400284006040c0089243c500300130350090034100000184410454039070003560403101d03071400ca0140204914140191241c00350b036103c03042642030290f04811130042c1c1050041c043c2a150100340e00b5040380c0042d1030030301c0b2804185496045510000080700007848021800b200a00b40100034118000209a440c0394040025080c0c0c1c0e40800410b04240c4940100c0c1ca001d40c125400c2525a600c4d2090314102c20030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 953858228 1250 953856978 953857013
    0x402040b0a170c1230040f03031110140f0a1b08160e030a0602030c0f0304030e040c081e15040e0304080114010f03020f240a0e120a1b03020d 62
    0x46031552102d448005445c00040c1d082c201104100c4910645500c0e20b9410340304001c60b00d502c140000310703020030b451050000450082d034541e050485018417585c2001c002041c559043c908200b40808002811981c01d030700039080c014078030000e56958201d9001043e40840c44180c3d4801018818070003540840b034603015505440690030000c5503210140d400c4040350300c292f034041c0c100d002d0110108407154040c5078007102d035070b25452501c61860451625a4402c6608801180c0343d40b1010321141480d101e8004a02458100044541031032542e4140d1003c0300c282001a030b80c00040092100c007042e607a601c80200015000f170104416038000c03151260810702660b04c2030f41c039060780030303480840280e180d6048030110b884410070681150284070001461040090700506080f02d8001006446600c48264010a44540b61141503c110040c4040e15054104d445594803031546013460340f000c030310f040c3c100b0fa000039840b0117101c0d2281d41c60340e00040d81c0c0c07000c1e40c040e80030542141801810b107052142440c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 953859478 1250 953858228 953858239
    0x10c02270108030c120c15160e030a0c0b0a02011803090e07090b090d06182006030f070c140307030203031504051005101404090903030e030f030402040b0a170c 70
    0x3a26064810303640c0c044c1c0e920420325a80021a030b48100100728000388560000306083c1c0351000250401202d41490958105203604040286d49004c65800b031030006000f21b04502401c3c800403940c0316042c0c600304501402400000004035070b01240d000b540070354401034a0401d40d400c0c0903503506015003600354a2041e420b040541000141d4a944500440c800b80c1d40e40082044c204410031061052559054070100c1d1401c0d60f89010b0040303582030248103c0142d00c205556420440c13152940021403141c0c1c0d40f40340c0078010600500030714100c1000d910340e0200940ca0b084820380325500b0404540303945188071240f00d0100044180c14550b011004501c6841744030141500c104100c0300b480100d5008403001049851000014081490005203501d0828034901d050200c0d00001112005540d1150b480b8542280d9500103030410076406000e404d0f8440b81250182d803d20840c944203120074070000744024402d41e5194507804841ea1510391340f170082c0c1000e500c034282000404907915074038049000400d1041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 953860728 1250 953859478 953859481
    0x10e0a05011d060c0f0c030d050603010e0114130c03022205060a1508040302030c01020d021b032b1e050702070e060d110d060c02030403060f0501150509010c0227 71
    0x5000560b6070010b000ba00e90001c02c03082c0c0d0f0390802c04107190003400e4000c070b10100401408840700010000342040211130078001900341048010542101d00002c480080e59060000880c43c2040d9480c003142c3c81400c0601a0380e110307100d490055500b0041c2d4000a41c400b9400d24a0320781a01070070380c20458503040380000c2260f0b407200d1003003011504252150541c0e000080c00340e21407140c810051250842e01c03034012641408410b0700340c2400d907041151552001680030840b422000c40000c102401c10800c2405180790070303440c004980c668070018140c2103071100070760301e041c58407141c075402912640c0d05036481d40303078401000c00944003520b0141d491500501c2044c40c08a8440041400c0c20b00a030300081240d0007218450b87c4484040d001c11025682c88945490001c01007951030042950305225540510754540c2185000d904032001407500340f9015141c200184422550100d03454003a00031403d0080d102c60000c0c0048800ba6003450b4002e4000c0203041c3c600440900e86c01900c0c52402c8d0408010102d03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 953861978 1250 953860728 953860751
    0x6030b0a0506042919060e040f020a0207051504051309051b060d0b0418080703021504080a031a04090b061e03250b07121b02010804030818010e0a0501 66
    0x382e86058242028248800c080300301078211842c0c0f221400380313010b003a1700e00d59242070b01401086429a40321201203071100942c0c4909217000e215907603400a200c0760860420044c444006e54441d001d02406021784104414a084040800180d038020640100004404100d6611910241088080413075940c030628002d420321034051400c0112020000c0c04290605a01c4440d0002500d1844280c91f0400d40e00c01c1c01a440040d8005440503150042d20295a05c3e8020701e4020701c3c1070001c0d01b91110044654060100081d00c18048a1181070745240201c1d000501d00c01001c0b4610740754050f250300c40d1405030042c0400c211200c215109040407240c11101e40304140d000381403108034814640c0d05030008442103150081e1009203108403002050720002c0a0b0b25680c801301d40b03a1101e10f060742c1042032032941040ca60781c420030322070107940d400c0b001c8640c2003507650010704044c41c003403c01414400b1410006aa00d0003610300b21180d4000d4800074050102460b0341e190711a10300303e0007600c081d401c0888a404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 953863228 1250 953861978 953861981
    0x17130608040b0a0b060702120c0306011e0e1803070f020108150901030f03030e06040602040f14012012070f1106070b07110a0b0a05330103051906030b0a050604 70
    0x106076044040541d40d0750f6502890701c010059404005c1d8400d100340815000341c0c4a030030842e00c1103001d01c00200380700c01e0745030704262400720140d100702c0700408820f903640140e92062541c2c0b0212040a6006207141d22072802c90800510900900001d910001c1601801c0c08011445126018001c2e254124183c0b11a070401d11080903651003035810403410b400410000d4604203840c1c00007802460001044103900c0c12290601c8000c0c3c5094900f150042002c0c040e50324403003270650080c09210804414010094000b0340302e51f030701c02c0303103204401d28503240304880420900c1454800c0390501d0300182c0e911001e150003980d100a66509580c211140712812046080800441d900a41c000e00d598000e50385404040b202c2c4650f0300c1c1202c2150080340ca000000405000000340034012400c4081518502901c0390000c1407012141c0c00a080c00d48203500c00d200c07203043e141c001e0581c02031030701090f02d40d9803d401500148041451402d20761402400100380300304145414022000340f4410722645c0c640008020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 953864478 1250 953863228 953863231
    0x5041a090c040f050f030a08071407060306030f120c0203070f180608072705040b0a0c0816141c14070309170a030f06081015030519050a17130608 64
    0x30381c9070f0303c0342d6001d00c00c0741382900034030b001114002d00700c41c0d07211500d07910b5486c80c0d000711400300e60300ca02d55a00b40700c10345020701021010380302ca442e013001940d1540d10b42c03e030386000485010f089248100203a0a07001c0c883c10141d08004d402401312007050ba03440401000c28603076031103450f0001c0703d002c0c10b074403140c16140110303400c43c2c00c124001c2243c58188440b1080c00b02e001d8050100d040500ba10395000d104081c00361510890050b41d115245c3c0c6089410a016140801000010010350204100d20302e580d41c401c01381440b1f400c2ca021003440c0c80b5010100301c0c84c0304014040e1150310040c01840042c0c9120b421000f074030085c18107101a151507a010030b80c20303249081d03c010000260001608080f07008034000d060510074601e00411080d01035840d5404803107030340e00820740540004545110f015090300401c11160941e40740c00c07030640e18607280c8903220754250360900130328050a9241ea040c024100049041190860400d80c20310040000d40719407540f021140700401201035000280f000c2c000c1103c1c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 953865728 1250 953864478 953864489
    0x10e0705060a030e0f1f050a020a0914031914010b010203070510021602220b0105040b12090a08210f2a1e0405090a0203040818010905041a090c04 64
    0x803410b050318400c0580260014110000440c812a4640540c000c82006005103200c80a036901c241c00400c44202415100002c3c10401c1c00d50040020769803550b400740d003403c00c8840c3c250300c040c2c1e04400720000a06291400c03d04070903144506600c103046c0071444034034841030b40031071000f08200601070005988074010268090700b02d03044035030f040847e032240390000c106266400c6800d0041e41915400180104681f50018020710000f68255162100521417410b070b00d075090804a003410310305240124039204d24201d00d500701d0140004580b84c49030402c002c1d10855444004180c40c0e0b00090030030000030965040180209000002042080682051070f038012003414418050715504403921000e00e130032000410801e15010002000490421070550010820781d54245942e14540801c01000391005403007151550f204105000c0050300c148112032000ca22504801d03030100090006980c0088517a0000e81c0050600005a401c0401e0070210715200300b089401c1d070020349a507140d0620368080e60141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 953866978 1250 953865728 953865739
    0x90606090c0a031a0603041218150c0807082803050c07140f10060503060a18020d030507050706050912010e0d0e0a0f0b0405030d020a0c050616020a08030c010e0705 72
    0x450b0a4070310a4124000c1001d03141030000480d8030503c00701e0201c2e0700840d41075507542c8940840180d465840300d0b020040c410540310304501c160422580b401c501c10226011024008001884800c00028400703852400d034211000d185c4900b50130850300e40302c403221100f091251601e0071079049000c0c003910829000301301040c400340c00c0581d15950702405d2045000200201e108503281d021401f40b04201c000c22800c0c041c200856130f54501000c0c10725041002e080343c1c500d90708081c0b07804c0ca450300001c250010701e03404880c101010703505418142c1d464412501c02420f02c7c0207a0b8004540c0303d42103401042da200342900d40c11520100c2440c0035007290007180d10001244c000f400b04c0d040b0148116480c074050034000f00015a00d40e030b01d80604401c910b090340030240841000c9010811460240b004400c04035040c00034080d2066540d46000c038401580c0155807180a02181d40b0490650455044c1c4029a002e00519182621003a50503629081024903070291340c2886426021070724003050300741c00c4a202414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 953868228 1250 953866978 953866987
    0x61305120717032502010c230f0901090b04030f03090b2803020c0106090902031516030218040513060609090302030d0c020102120f0601140307050304060b03030f0f03090606090c 78
    0x418020b15031020b0010f11068603001c0e1041c241c04403000340c0e00b00c242c10070380000910381c000c110080c0510541180c24040c01c0300118056816036020800c0710104a0b440d1901556140c0312001070391070384125046030415640100d40030003002540114414154000d0300e4140340e0690b108600c2d000b5104481c10146010003140601c407140d07030a603c00b4840d221690030051308104402c80070508441c0750f0303448118003540320b2450406609041c0b1074520308503149a6022030514020010b28a0150329201c0c003406c15a0008601d03588402c28600104031000041092101c3d040482401b20280e0f0385c1e031000c2c0c4070079161505c005002c00c254482c00910a03490b030061820b01c44400d100c000248000c041450640d5000c106504111100c1e448c814429000540f191105003008130004040c000e11a8a140d24400208180110540c02c002983c0e480741e80718501140400c01100801d0440c01460b00304c0051290103d50000111554800f641c8500250b42c1156855900c020820040850a0350101c0180d0300800c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 953869478 1250 953868228 953868263
    0x60e090403020c0f0f06070c0317030426040506121611121815030118150308130b0a050702010e03070f180e0703031706010f0207061805030613051207 66
    0x144613062030390004250021102e800d00208155501c4031000f19000d45c4489030a00400c100201d900200ca40340b000514110300c0d03e0b079248410940c5181c5955502c8500b608190708104a81e0211805000f001d8a095221441d04600d201e910705e0a07107000000c1041c004581c120b01c0e11450810100c100060010710810755880c1c0841a0b030380c0a842042c1c02884000080300b0180c442c0300100307905404100441d5075070343c5410b80ba806018221004000c01c0c07403d120400103980030034041d0320207072600f0108040e80c4005000303202608613550303030018032030103000b0822000755900302024003a900d0003a20390340300d51160441059240d006a002d0310140088032401403098200c0941c0c1c00103a020802c000185103c1000442803801c20160b200b1000558500b81480540d01000d0b01940c100700d0a08210024040c0e07814043e40780e1215000b80d80c100f0002400340c29000c09002c500400410014043d03075002e043c98440c0a43d6080300e081c013505c0c5449a0a011140030016508950f00a034001c1141005e200685 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 953870728 1250 953869478 953869489
    0x30f150513120f0e0307060513060903081903021c05010f050d05030406030e0f100603060b100210020f1201030515011d0402150906210a06050102150a0615020601060e090403020c 78
    0x49820304001314104a0344080c1c400f000100c010706100d4030744c0c5880340c440860f501884142070300701c1400c02c82ca40c1c0d0b04100107020401a9400c02c081c50781e2913030003c1c0007400700b14002d0103884080c0020140103c12445e45200c1a80424140d40e018031680c824161900f0030700c201020b001c13070010010341c02000200140e0703100703521820442e0b1039901a02c0d5500c1c00d80c070b5054500000d4001481184d69115820000c200320387c4298800520240d81c1c0342e0902c60740000180d11004040d800103903540d000294030b18000c0b019402c503130b001e8504800702d10040d612410310383e41c1d0b007401407030601b080b621013000070130020000e520700700c51001500c41007105a66960f0030720195115801d441442414140a000c03900c0d82d07820090411580081c4034030803a0300c640400711041c00d001404541074545030039010301883e64085911000c445d6110b510407010340f9040460b00040402d40e01c000d0162044030f60182c0020350200303115040301d0145d42e440041402c10350411000d4002950002c000da40300c00c0c860741e100e0800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 953871978 1250 953870728 953870747
    0x17160b0a060e01141315170114251206050301061d0705031b09010201061a090a140307120f05060405160503010b0105120417040f05181e040c030f15051312 68
    0xc01c61042c08007030f40c83d600501f03920040000d94004d039455010040c81581341c0c0703e9240d80140c4524012000c400e80b4414040001d20b8891040200b0003500340e80d000040040e00004024000600200501e559826419096410701c12007140c2c0181e501c00880c00c0c1da807054003076901807920070f4101a0380c00c0c020801103e45520103142981076540307d0310b0015074201c400c007130841c0508003000203560310b600071010003a2003101c41d00503088804a000fa40c1d04a034400048250030744601c0748055040c4c04250a0052501c170b6580340c020080d02c60316042108004002c41c00201000c0c420360840b40141e00d8004050030303164500708190004000f44503038040c0700d030701000040d0060b000345c408120342000204658015030142c1c2101040f1040510100814100202120400780248010403060304010440c403620104100b83c11920070a44030214080c0184028802c00071036124010000d2000b85161182c407140c810306c102e03213500d480d040000d041c8090700400f005003136501032050070140400307500681d100d0301c9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 953873228 1250 953871978 953872001
    0x140103110d060e030a08071e0f030902040e01050403050406091a0307050a050c0a0c0515030c04030f0c1521020c0607110c0d060e070602070317160b0a060e011413 71
    0x440340142030f10440e050000f0510441d0503070300e4400600d05000044d000802c00851071b1000b100d09603058140c03a50000140c1070840e55071801150700301e402d00010b000340c646030003c0c14040d4a003101f8041050b4100c0f000304112201600c89554240d51140b070f040d00c040c1c0480c00200050320400c005420103104500401c03050307079141420350034103035203102107840d003500050100c84154001000740058a0110340d8050352804c0c50354607914516001e240d01c252801684801028448407041074002c2180480e891710161104220350321144c5402400140300c601e51042c640d0410301d80c20f20f90000044507000329491400342800920f6691105002218041654000e0320998083c082c40d60003959a110900a440c40c003844009c2008401051058107010f0258003000c2503600c8030701d040000428408814020319980e0700800c0e150500b0000504691281c00e030024038800115041000e001c0c41a400074040c0c60180000ba44260f80350400000f5110112004661162030324049081006c80d0350880c060100c3d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 953874478 1250 953873228 953873231
    0xc0602040b190e0616170c0d020105190608060f0411060f0d0509010501210c21151e0510030b1801050f06090703020c0c13020c01140103110d06 63
    0x355240c5624005801c101822440d0820b031a0a450810b0340c020500000040200c901c0b03441c0c010703090340c4850741e00d1900d0002400c080d17881c1c0034805000030000039035210202c00401d68084070001d0300c00900a29089502400725000a140b132190f80001e0700c50304d0180d86c00d0400424080d03e44d034000c0440c07110700030030484a07103545039551552611030310003400341c840d0f01941c0385440d22507542d060001d480c0300900b80c03400b5030b2401d00100030512400ca179500c03003031349103100a810792141c0b03080200c5403286c0354001541e03110002d40040e41e00220134202941840c007a172406640c40d41ca0340340d200f0960b0111035032507030343c5002082a054803088036481241c000310081c120072801980d82e41ca45080d140104e41d64404c0040441c00e04840303410038011603074082030418180003e45080c0000a4401034041c1805c01052f5000c41c407031a0680d01009070548004004140d56021109021088040d51003144030700e000d03509200f0509082c500c440c801034140d80e40034000510f007049080034400e568050401c01c1e903a0a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 953875728 1250 953874478 953874487
    0x60d0606021e0d1242080609070e040f020312030f0a06080d050c07032901060c030807110a020d060c1d0a03020402130b030907030303060b0910031e0501081501050618010c0602 77
    0x29001d411400f050f43d8044490004515445c4046a000c01c8903680500040d402000800c08040c8011800784165810441e0381800703501c8a00707051603202c49400d0002e401d88a0103002d158440b00113000b41d0721803010545118900d9480135070400035100740c1e106000181d8020702070401218010000342c092580400c04942e0415560748818440b04081054600044183c4408c001d002030500d002c18013401e058200120301d001159001000c10000420a0b1304224000d9402400d03003209200c41510303190014000c28500c00c0c0d0342001070090000b500319501048040f09080c50700c80000c0c0c100484800028440041c06240d031f000d00010758855120034244c40c450b6840440d0b00d2460702c1c00345015580c0d0700c0040403050304500d006811507915802c4a96082c1d0309004645642d51120120340c2c0b610850325000c0b4007400e8540caa000800a10100750040754100b000100314918000380c4074400c29084078803800c0c00d0f60b070b403002e0044501c41c1042c1865034980342c8009407590350051000c800f01500c03480d001840d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 953876978 1250 953875728 953875781
    0x1030218090a0f050f060f0604030302030a0806041b11010e0a03020709020d180302010c02060a05041104090203032b0b09010b03040605060d0c0611060f090d030b060d0606021e0d12 79
    0x1104d00484406840480610a011182c103160105014200058036140e24090942e18040e549006d001060010400400300182841e15030b90081000500c0d100c801a40e0800810300180c6110500519090380d580f034102080b413200400521030b800142c142d006800400c0c00d21038403101940c010500d1814098942c5040890004241040c800d03e034000d0740001f80340140e42d20020700303014028209030130040c141070501c80414a00310039161a004200c3d800184035100d0701c00300317055016007401c400361404e088019052046840e800c0c041500e442040c100000031a840801115007801e00880c0d812210500001d00007a07042e80c0001d8020100500b942034441140e590912003544030340181e00040d606031134031a55544200400d90f040a020030035442c01c0d01d0b000f500341d83e50703082212480041680302c645001183c0c45000072284606110b000a100142d01c60b400a91b80f862001034040b849540703e29100900702011405c0e040d94000d0b641c03003050215090040340c020f05041d8901c0003030600c58004101e05c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 953878228 1250 953876978 953876981
    0x50c0a021002070e011d07180b031e0c0c030f0c1f060801200a1805210f0a020a030f020118080f070501050c060412090b0301060206011401030218090a0f 67
    0x14054035a500030000b6a0800d0403890800c0010b80c010031100703801c103080c0c2e00c01d083c1b40e40605900401d41d02e020300e0080c10074a41003c5102d010340c0b08404121002007802021100e10401407001050142c1200c8552500c51000e8154402d401808055400922850b4404c4680e14014a00c842c03240081302d9951140380e040f00d00500101903550911740d941c060401c03603038070207008141641c4d0080d5408403842d48001c01c03a80d690303c180760058007007020b100703005803560b003610070344101070310002d0444124150f134508203a85241e0001114400b178840c101707042c000c51800090002425038060010182c103451030b1f8071440d811214080403410300c803100707542c650100b00c0c92600c400205940b0004cc908562101301803411301c00c00781c0003141000010081c038800d0b410300061142d001039024805818252000c4421900980c04d9000110700c4003000000190066000030b60605960040e0161100c400406005408a2061211003030743c000790b03139548214500d403a01110741e100f020300c54041118035a0400f03880 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 953879478 1250 953878228 953878249
    0x408040b1204032c0108070201021b0102090307050d0c0302310603020a0b040303170603120403050106050301050a060e040f050c06160b0c03041e03050f070302010b040f051006050c0a02 81
    0x3544212100b00420f06902c0200d1820500b02001400000302003124249800c0701c5a82100e41800055804509054402d5046400d20345900b43c2050700840c07014402c501035800300403014030901c10820b002c100d501e0044141560f080d88446040329161965084c41a00311000c4110781a00c42069041c010b0681040c959844201456200184036802c500c10090464550341002d0340c0c080c011f00050000070741191840004001c105d1031306a00da5a000c00092800303094800920b4030721804a000020880150010402d80384114002c1c403203540c3e0182c0d240210380c0303a8491004c1d58406d0b07501190100d45418404c0360398500950503101c3d01c240314030201c0c841d64860741c00100660803441801090145941600d6048819013218030718604103a200e120103403000307209400042e80700f10348180401d0302500480f0214050b42580d180c0354810390030068001c014820781c0c54011170400701a440b00c00360520a00f84102501d40c031031350009040600c12696a048101400014855900c019003d41d80d0a09480d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 953880728 1250 953879478 953879497
    0x60106051918030b13170c0a02040509010908071506150c0210120218010305132607061a120106030b01090c0e0301090524040b01030b1e010b0901170c030f0408040b 72
    0x705c010700f0a030320340721a21088800d00d40103543c80c1806000440007010543d01c40454040b074001c01d49031190600c4038010020150020505400011040200411042c4105011001c1201001181c0d5203501010324804010300050001e2805040720006203005103400944000c1850642c124594200b81c0b001243c3c050038503110301024900c03410801e9a0300d401070590111908070600f40e20381240d6280280d00b40f0740000b080c0030004040e2450840e4030701c1c1c802e0b1405070350094000d011521010203048401c000d0403d05030b0003242200d0302c0c0281a501401071000b01c03035005a2841c40e0b68a4002010000c0203808405170810a064043c02c0ca1540e0034090340d50114080d038081c0c07400a0410f910300c1e1010614410b40b0000c2d02d4040d04210105040f070008034110303500042c0360703e5241c3d1a0040d00207102c014010950140c00440c00100306221944007504e40d0391000e88654402c0341e000c100001e440b000440e5100740c075510800001c3c83d8040d54000150b0041e03c240400781c1007940360007030b60704660480d101e030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 953881978 1250 953880728 953880751
    0x615080708010c0302040b04120f0503160b01171c03020f12070305060a030c05040b0f04020a020a0b01060513330305190203160e03100c05040503060106051918030b 72
    0x340700d0840e0030320400603000c3d500d007001c624151810700448618019803007080041001501c0071001d00c40c0c0003101d03e121541c0207054942e40c19102c40100d81c80e942c070000650705980c88a00200304101300c4042510300442c210010034a00720300350300026a4000c01c40840b001c06401384020f0420580340300c0541900042040744e14850b02e0000402411510010070592003411412010400329003810111404d40760292400701e05500042c000c99211030b01038459a411a00c0050301c5c1180b6075011a840c103603e4450413141e40d0316603035210101c540b405480303607076051326040110400840d403d20300284440e08001c141817202010802207906101381c0300c0d44220100ea1900100311f91101450f00603d4002844c1e0011030039400c28004030403078010400c0424080c025603040501e0142c2e010451a91080d000741401e010481e60b440d0b0040080e0040c0c8a01c90017403042000120b800741c040d0060b688030070307030007480c0401c0b91398903400407900c81140b0071518000b804891400f0001c1003070031283d5885608488030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 953883228 1250 953881978 953881993
    0x3030302191b060f020f0706020712031a0f0a08030f0a0e0a060503130213020307020c0f040b090c030711070b0a1101052430060106020601060c0f061508 67
    0x109100180503072000385040010300320341112614424642d010700c00b078011000040d4451801505030081c410b42d000c01c03029450100c2d000c0200300094004202c0a4403402190003440b01c0c1c1d00044c0c0070380c2d1820b089119511490407512040307040c00f000960009600501d00a100d0344c6d00e100c002e043d9484107812905144000420000031900401c044c202c1000684031a5a840d00d0850010f18a001c05030184440850110701c100540d50388025003024401814001c55403400c180401035941d0042c0070000d4081c241c45020190940381500c5407503d803900241560002d60f64070747c12401d05030700040840781448429441c401d00d0040403c80b5401406016118030395841200601501440340498010f000b6030400c1c0030840104000c0320805070349142c441950440c041c0034400180c081e03065079039900070f07100d032100c2c40c2c180d440304415402900c448120a9444590725110202d031102c00c24010b00300482c0c4402c00c824009100305c26013061550203030fa0300160500c2070500d100150034880c1d028803401c0e0711074034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 953884478 1250 953883228 953883247
    0x1032019020a082a0712060e0a051f0609140708041b030c03150509071707090207060614060315130209030d020c04060b040501120b0609180108070605281803030302 72
    0x382e002e071381100440040c01028500300078440c1c040d51450005140d2500e810b02046001002c114058541c2d50210a035a902800c624914000c0816940c0c500c1c5a40e003450b00008030a001441007040038406404034030080d6545803020742c1c002d200035104881c48207030640101074540302f20824402443c071406946140c5841d6040401c444003019000052031480c007401d20a011000142010840d402c0899507440c0000040260b800c20b01c80303512841c07001c0d00008080c81041610303031243c015212000f50fa03031100c821080902159010464603010b04d400310401c136080780d01d031184824080c03c3d00640050f140805500c0803905003101ca1890f0300160f4450000b48555180c1406604041c00c60010742504080c0382c000000c004982902080350841d689039078800e1a43c54050440e0310000003c2e003440b0016000c450001c810103002d12401489016135180401d0ba28810700440d201402001c0c07046038001c228024240c4000103400b004014041400d0301c814488017a1001140214066140140c440c038194 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 953885728 1250 953884478 953884537
    0x9060b040b09270a1a0f371502010b0102100906180503071a070f121103090d030e1903030e10050a02070b0115020d0c26040501032019020a08 62
    0x80d04061500942581400c9607501caa243c43c00c0c82106c1143c06181c10041000d9440349054040306501c03000d6620045151600c250110302c0b01141c0c13459034900407019004c0012401c07140240d0311540160401450203040b800c403a007214145074016000000d1084d04c68202804141c0040012211900b02103445001d011001400790340c0c0018030700181c1807500c0c1160004203241d107650300345401e00003070508a07452513669034840c01d40c000e01d4000440d0ba1707041c843e04459841c83c0d40d80239540024240701000d1841480807030a4811404444c240702c1d4611120754003600600551150b00c40e04e44560401c01d000b251150084e2809a91640c4005903160b0310350804120000058101050720001c40056208242d400251000358003c14035101c80020440c1c17810242c5121440411908034501c1d8801040c000304c03400081c01150700c01d80b010049070020920301480f02039810a100e4400070180402096a451650000c00c030310178500c1560301c4201c06a481001302d401c070061400306015013000c450b47e02d1a18 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 953886978 1250 953885728 953885741
    0x6030c01030509101109040e0703050d05070b13060906060906140411032e06050306010f02150703021c14010305070f1401120605090412080109060b040b09270a 70
    0x1e181c24840c0740f400c0c044032030380e5149100003482d00780e9179804001d9016403060140c40c90303a10000d01c00c0c00f0020590403601d43e20406404113a60070301407100e22140b00c90240c001c891321f0541c0484c9400e00c60341e40001c400381340ea05005040c1e5890f902c462034040090028440c0a010301040c21000441c41d04025280030342075501110035000c3c1c0d10300800080080f1a200c00c5d01e40c82054060961583c099a0613802d10b44449541080754090807440c021031040d40000155124030801c0e43c4006281c4901e4000300d941d5000042c20714040c18021000c185820700c82e400030001c0d50701702d000600b040c00a496104003103e0b0322820142544414000510800505101d13580080a0144100e102d481c00c1024034540d00ca0ba0b94030190502189030140b40d1001800d0308244001c1074000d001c3c24842c50075007403c3e104800341c11180c40c00a5010f00000c5035400d403d118040a0303690b10f03190141801d0814000d5807007a4000c0200680c480d464011040441b185091000c0c1e600e01d003034160141504103854141c1c251ba59 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 953888228 1250 953886978 953887003
    0xc030312040b06011b0c0302010e0f1011011e06080d1e05030a0902090109050711070b09010507060b030304031b081f09030309050105160212120118060f0603050603 72
    0x100300000c0320314100c0c400c0c2604035400041441d003a4030398030300685000b02442010000c40540d01004414083c1d20721400e81103074000c0e01c4080091110600300643e0130200008142e210820300742200c01c0d030740300c1d140021700075418500000ba0a070465115441c00d42e50003400040254494100f8003806409101502020713090742000b46400000c2024504803480003c4120204900030002a00302c0d0110740010040c9600608071346e82c0703561030300120300c06450125251004100c111242c0114070704002900780031107c0d240d00d410f0910080d00c0044920b50710640381560190b0300c13442d2200c0b00f541c09100800c000c510035545a14040c6400380580d18642c86688a503d043e081241400002ca0441915803400a10181c0024a040461038203030000c10001c074001d4141d610f003100f04010a1040c6040c000003c0440e0203d41041060307544600c032a10400031800d5002c03c9210040110b22040c000740c41200040701c10100b000d5442c1c50080c2c1c01e5551650103007000a46807418130030310b03040501c00e04840301d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 953889478 1250 953888228 953888233
    0x2120717060108030f0d09020d0f0605060f0609130e0f06040302070e01080c060d0906090311010b040e0c010c022403010f1502070510020709111206060c0601050907050705030304030f020c03 83
    0x41c0f50018850302c0c3e0240c0c0c41c020b024a1400036090001400a510102c0382d41e600628400c00e40c0c00354200001c900c000203e04079442e516100100303001c0d262030700d100c1111810040900c0e10f010685418080811001d0000140098958040c2c0540007011700c4004121a4010010056481c150030000e28182070f039805400d40c041e40000611078041d007c11240c08501040d1f40c600d50b10198a40c080000344022031014001a20b0111080101070b4000101040702c0d81e1440288200083c00040104640a400c4050107640c8400e0400700c02e540940d80e2220080d00080641c1d9041c035100706074881765900c1401d080110700002006012009003d0904009002300c0f030f0214509030029540a5034650213030040c2441082c11800e4001c801e80f082000c20098050b0b903005001c2d411050b80000603d4100c50150400725146400080e02801d000301503d1001c4250f000600c016483d00f4240110050082c0001e4104541004000c1c086203003003004501562190ba80c07034954244444000342444010341080e840794 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 953890728 1250 953889478 953889481
    0x501051608220b0711010e011a0402040f1a041502010e0114150904060f110408100c0507060b0a0314030c061b180409020d140c0a0b04140d0212071706 66
    0x24101004410900d076000d00c40080da44c40764201619004521110145690f0804220718400603041d048801600c00003070000c000300c0c01c3e0b60100000d9000b180101c071500c42c0c80d0301c03003006003252081c81c070040b45e800c1ea500b0354074091f10f40034816582181094000f0140c0c1d1148001702c0c45140901c00c11100350b003000000714050502c6c030101080c4118806236544218001000302d01803003c558081800e1182c3d211041100b5085032010158907089031188500e540607140b100c00caa9401d60090058030030360356640c0c03032600c84903541e0400202240d00a17035400040500d0080b0000b80d0f82042c552103024030000560716240d0075521a4900a00208003802102074860a60006042c5e007040c2c4012900000c9a0300000450744041001024084006907200c503003001c02409011107007002240b01901042035400c0340c1c8444081c00581011840380750740d4140300b000204401240c6006400e04094014264500b40f52160001000800e9208940425400088040141c00407a2151200e5041290f020341001d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 953891978 1250 953890728 953890771
    0x8032502060c03031e04020607030e0424030c09050c03012303061305011505091303020c0604090603030f02011a040e15040809030106211b09020d05180f0a17070501051608 75
    0x15000d42a0002d084c40302d9103440c42f800c0d07038aa4108a09099104640d00080d070071111082d2400251480182d400c40c5002d000441c0168590189030b03c1500c41c202024510b07440c00850b00c8a40700050034085488403000301d403050355a01449103d010300040003100e0b420410341d0502d00d00f11220101c10001c5001601c0e420001902d074003079800c0d070101d08944074800c403142a0a0680c2041c0804c038072030360b003e000000c000c2141c075615404802580c0c001c6c1c0d100e58840c0c080da03400340c0c2205c9001c19018040e840000e164a511f19043d0000984960040240c13219800704003810001000251012103000c070740030445005500b001d00c80c101c001c0c5030580740c01e5802151207403444040300d58020701a0604080d014800c0390508203121280c01844940070071540c80c142107602100a0200303854202202e06803a60990182c2d800040c001407199410004d003020b544d45a4a17402860302040e0800d0340e0507000d01030348020942c03c2c07203540c0c070a0500c2d042e10848e000c04004010404080240301c0c48120407850309900c074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 953893228 1250 953891978 953891989
    0xe010201092112020c0a0611031603110909010312020d1803021e090411100e010c120903080c0303070207060503041a07021c020705040507050301080a080c01020d0f1e050108032502060c03031e0402 86
    0x2900c82b024240010300e440c442a00c1e0406104442190760130400d000000820010017088068282185509482650340030314000c54003030f01c1c00b0f0041c0b01606001c01040c405480c0079207030031900c000e03420b00343e03104030203440c5c00304924900880302610305418134043c403ca241800c80c001d10043e412490005001565400080e010440031071018101110280484e40792030f02442e20900076540014465440f090f482c200d403603880e4822500040103005807040020340e070740100c05880c002c41c2d010302c003058040710203203c40b014060020b01e04021403141c009801217420050740000102c01c8141e000d008283d080c0303401c2c0029240003600d00310400c401080104102003002c16142c6c1002d43c8402425503960b041c090440c06801244401c540d07891038000c50080400c80750384103d0414038480c2108000d03100441101c0225842403060ba84035401c20048001c610704603910342400b0428019031003144200d50340121b07071030340c000c4403135655107a000001707009115040d5003035481e07102c15110360740b0010301e41a4049013 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 953894478 1250 953893228 953893261
    0xd030e06190e010f020c150d02071e06200d05040606030c0602030706050f090a03051c051303080906070801140a1802090a090b0a030b130b07030c0e010201092112020c0a061103 77
    0x201102c4000c00c88d454045290b8044814581c2c00052500c0040020304000110014041c3d084441d40d00e00080d21942c00e48911004500e5580c0800c038904266804029602070000100304455641d03442c08003000240900c6001c801500b0140e0003181c45410a281840440b00301510740e8140030700143c00c000440b040003230700207403455040c584191141101c41c04103000f030119100303110009090404014041804c0182054581c0c000d644600182e20340d164103944460007a1450f80000c1c46400042c40740b0052070f01d00755540b04e0094140c0c0391042c0c1d40d080c824072000d441031040301d506800107031008492510980181c013901e41240200702904100d40019200700c02c501c00200009186400114100b00e00400b0860064011040078424500500008d0052001d49990f034007042c11a8016009544144100100541e003e1300c1d851305c5821071412440b0910610300f805040094800c40301d80c2a54007800a480b9141c1014014a07009155144c1b00c4161755010300705a9459001784100400c409840f44601e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 953895728 1250 953894478 953894509
    0x20a0b0703020f0409020313170304200109090e0307030206090f03030703050c191707180b07050f2a120303070c0c0f030c030204050a0b0d030e06190e010f020c 70
    0x59486825103100f03105030040b544030340625031020082002c408615001c40600c244030700c550b8030f0f01d81c242c0f4104445034001500d000d032440c0a4040903050900260100c0030b0030640c1410514560ba60300e00091041d2610045200303280c0c2c002003120300130150104516500196040091b020089800d620199613020007171010f810181c8404c0030440360100241103800c0c040d50303a006100c40050030000a0f02040d44140b070080300d20b00b8540001c1c00a4443e40c0030740484003240c004005064542000700281d600034810a071241d0107100001941e0000401610845007800401001c0c0e590881100e023802c6145414031900648100c15003010a440100c110f9901c04954100100c0300304450134074103040641600104040044400003105011868080c102200e200715402d109954802c00060256041c0c00300e91900a40e00345001d0340081e001e440201420030303000d0704060400403194171000c004410f500c1008045424411a4041540e01121118030890540010700070808500041401081c90b00c2e02c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 953896978 1250 953895728 953895731
    0x11030f1507050703030917030f0604060b040303030902150417010c17060d1401061701050c070f122307021c020916020f031b16061409030102090916030c020a0b0703 72
    0xf140406009500403a0080d8101070003c3c1c1d9126003000800c99030344240c480300100c94074100084c3e100d00d02030140005035401112903d05141c607566082e4042d00b034005080b83c1c03000c103801004d00501d11800261005000a0310408a4011541003a60848cac161811020400040440d0f8121001c00300c6a1240c000d141a907010051a45034240050801c1d0242c0529334076500b842000110107444018042c0c07110b400c50002c101a817140488a00a4810138000610800c0c28850801c00319080f85600c0c010301e21305050a0309007a942c020306401ca51421112110786000218209083d410000328422582c2c1c0d034003880c4400c3c0c42c00c940004800403402051220200010310081001d14030a204002206039080c0890703031500ca0340400e00c1c0000c070300c401c01282c4a11514a13400312105800c01d440342110429141c1c001e40e29000900c44002c1d0380400d0f00e1541540d02003040c604662550b881d094801c0c14206a403249021140400070281d4400031034000c00c6601070b41041c80070400e01c00c03c00350498850f060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 953898228 1250 953896978 953896987
    0x203060a0323010f0b01090806041a0c160f030305012114010e0a05010504020f1f0e0a18140603070315051e090f070b0a0806010e0102030408070311030f150705 70
    0x580744042207082ca0b003030700d5003800c559640380788160b00103000e4081300340c0f24842501d07102d00340b81d59590400c0701c001e4240c9510a040008084140500640001180c1e080c0b42c902142c00032400005001d0000403218080100d49071010b0592510035140076040c50308803010040c1c1035000440000340880c0d000341c445034081c0d14101103400300b54443c0385d07981d40c0c000940304038902e1810554020b0200b142d0603400f4207807890700c01455250804a82203101d44092200c1500740c462481118601098448a90450f0625001041d01000d00140c00150a42c251001c5001d0000c1d4071541c2c40c0710006002180650710904081c40081c4003003015645034a07003480001136a03500c40da52101d107007100001016000100d9000d0040f00e1002040019540c12890100d400b540d50381e0000b03650318415485610000b88110004c40c2c00c5610469001c28801c80500c1128181512000158140b58a55200700c8280b8100109503003181001d0099001c03441809001e0900b8402459044800910003403102040010015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 953899478 1250 953898228 953898263
    0x10603020906182107090506030c1c0317092b0f0305040c0e04031d010e0d08031b040603020a170f01031e0c0312200d03020a0201140c040f08010203060a03 68
    0x8503c0c40343d61385074103102c28604846045079240c641c103000b5040030504080000e80107044c00940c2c0305080c00048e000c029151040030401c44452000e0404804121119800c1c080c900411181540620440340c050300f40340c0e8010a0705681d5103480c0310928424603100140c42e9040d6084106079182d0300342800d01280c5980d0768684a084003da80d04500c100c0d1401009100a165000308544150300c0b000d1012041b95103114010341e07003910a6480b16502a05c00000d1400085110000d90341140c0404015654450300d402781e0f8005803c60380144000176401b25091411030b511407a800706040001643e034115060a80d8205420300050001607c40b000350906800700340454240c07032034025040a80e807146d02e9100e1910100700b40210020400107a00301c1c1d406001107403111206079080818400070b00358040f83c110158040d41201c2085406d5541e14400443c50b4a5000700540c8202240100d507544c0d9414040c41707002c00402a00b240c069603106108025080e107a100c2800180d94100c2c07095080e020580 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 953900728 1250 953899478 953899489
    0x22a060a0b1212031603050606030402060904090507230915010305060102030d0632010f1808150406051e0c0f09060a030603150b03030f030a06120507080601060302090618 75
    0x6011011440c4500310b2040f02d0881e0f140d01860144545c0301008084511407a800c5060b12010f1b16410341c444130400c08500149040c500600c00030368060004545014071742c0355076040103c1c2d40e000d21941d44001d100d589040a203040507015509007114902d526003889200100e03020307090424541416500d0002c01d0302ca070700801c02d80d1b450745003042e401e200b203c0d2122000e05520a00c0d501000f14000000c07030b040504580382c3e20f03050001004ae502c40349149070440088506c080c0864210100c51030b07031840811071110500003c41c0589440c0e1b0b00840d90304040c6040003c0f01c0c2e0080481e4507401c01c02800e000c18100c0c01c0c000780d401c60030100c003813601c030f01c0c88801d00c04d401c0c45005082c40d0b000f2000188070341f015030544c200c001103034013400d00110f80b40c46a104c08400c0c0c2c1c26101c11700358184c000f0440801c2200d46100a1501305800c41c1c0b0004030192164000e08092112800907605544183c400700480300040002502414640c60150300301030715503010800d13900a00d05a0304188006d45001071254658 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 953901978 1250 953900728 953900749
    0x41109091515190c030c0f030504090c0e030609300f0c060a112a0106030807080c010e070e011203020f0106090207053304051002070303022a060a0b 65
    0x60100c41c5802e01420041010350040c0c51440c0240310500250301014041c03030700b03450030f03a401d138494034130011306c40d90380c001403002411089003800818000803036200d00c18460b510382c0109a440e4005103001880805141901c001d200610607401070321060022200300c95805180380c41903c41240401ca00b000f61125405000c04a03c40d02102182d034400072070000a020380070b070b04810000c0008812002543d2024412001d18800d004032202012a060079070701e5110746025400800040d42e25100e40e950401540b085609035505c610100d10745025075000c3c420f44000ca400c400080c40d07450301e4500d81c03c406500c1413090515814110fa5a8030915000380030001103050010000c001d250b4460400070029003019100381c03018464811440c08841700c0340395800140d8111406103405811514072100d035840b006108072801d0055000d003695401d5140041e00c000380c0b1035100582c44429600c0c0200a100c1146185440500c2e00c06444205140200e029504031210b480b011420320050408900002c00c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 953903228 1250 953901978 953902021
    0x12050304060f110a2a0b180105040504050c1201090e0d0507110a0b0a3c0507060507030b040f0207020904150905060c040609050a180203060409021f02010b04110909 72
    0x2400600400c120842c40c45400c4204a80e41780101640700d0041e1341e02c2c1482600802403202030030001404a5107034800302c070f01040c10514081b860161030b04046000c1c2c9109449802c640003000c01c05c000041054001c0a014040b414000c11480e6580c0b203d180d500d81c0a60001c0d000d106000071382909028080c911024a06c4000e0286c00005640c0c41c0e03200948d40c00003102c3c600103045103205c0f100c0d0450740c0c02a00401400b00101e0080c010101c100341e0740918400c1d0b074500030b226082040400041d0709006851150b03105407000681c1199410134801070b0b03280070007060012841044100b0059680710b5115400c0340e003001c1882c02ca8855010010010020584040e04a10a400810510f07001d50300c0204260342c4690f40340c07100d0b0b43d540c034180030b07540000d805882546c01070419a9030780288150f01550b1b0000b00100045a500c41032707004201c0d03101390390f1004c1d1551140b50700021266a0240584e0540640a64041020f142505520b81040c015555501c0c4560901c2000c204401c0c7c007179544040220 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 953904478 1250 953903228 953903233
    0x100f020d0c02060a0b100c0b09030c0d0f1d100c050712050a0c09050c0430030f0305010b130506090a05040219090b030705030a0f0603080409020c0712050304060f11 72
    0x515070030040c1d5100d5080384c2050000c0c0c10b00c003030700c0464100100300304000d44031915103d010190300c0c1d981641c1960001c00c00c1116200c18000e20300342c40d004208004d02c0d008142c482605801c806c2000401c1040c100d9981202c103250303e180010b0070707214100440e80d45c0e0740c0c2d403820899112036481d140342803411503800701031104026400b0005210000c01c2030303c025445021a40d0445642d031080c071065030300440b540d00b04410705000c100065280107510045145c0381500e40c140f40106120280001c015074242940090b5020402c103010b40c0d0541b10b52405400c0b00e07003510342041240055004910110b00070a40661004100d0385d1050b1070391004c880160000a1066407140b00d03540c0c0c01126040c4911109002401e00b1600140b070300c80500490f80240b080c0c2d079a441c0b442e900c800c00c81c0060911401030b081000e0b81e40c04004003080c0c10602034405821120070140e070703c0c01c80b0f8039103074503181c91500f0000101c1020301d110000140c000003250211303040d5080500c4c00d082496419210703140182c13050034060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 953905728 1250 953904478 953904491
    0x41a0702100b090603120307030212070c060c0809030409110f040e091204060f1b0b10060e0405010f060807200703030807051602040b0607050a051e030c100f020d 71
    0x240c000c544540d01401c0c10314200010408a000c00000706000d0360525003581005d4044803c144400c402558041c07881e00340949003040c6442e146460702c5c0304a820600180c0f0801000c8204241070080541401442c41c101200d400c9c8603040075281d03c16440f030341611a90b121b25043c5041c01507000c1c0c403160704141405a8a80d55640c11410380441d00b02d8114485000f00d280c03500b018508001501c0994403241c0d00d40b4800407262100766110a22a0050040000c3c404801c1c400142e03085d07d490b1241c50904d48103900181741c410b015001640d0a28418816403c06006001c0326113a0001c203012514580744c1382c061512008000d0f0349900d54590300002125684480c040003000000341c480c2260311994a000f000c0d0b90f500400c803651302410402d9030364069003100100251500d0717000303007440341001001c440c41c04000b540c0c0c01d07180032085081100c1540010640d40742c481c2440c2903480c9803a80d0400503625088900d951562580480072081d44001c0d9290014000c80556506807650199249400c0040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 953906978 1250 953905728 953905741
    0x53c0d020a0f05030c2505011803030b10020309090a0213240503060913050c10030501030615030c090507260907050406140d0f0803010f170d0f08041a 66
    0xc0e51040c80c840300802c400002d558429886802103d00c038403403c9a6003414851031428001490f00a8101102000d0007030054202040303080c8114640c035034034000d244020300d050785400381c251811500010300c1403010f00400e51049801104440011204417049101980c82180e80c000901500440d42d945c5c0c10401400706241c2800d42e104400080e080d994403400c0c403082c1e0411280d41c40301301e071002d400ca00401c010413041d168031000c1002161003001a0b501017080000485c06565601b4540d40002c2e4503440100103001a504c01c008422100c0320020104504503141c0703900c036141a100d0280540e550700001307401180b1650b06000e80c80380e01c0614100b8140182d803103810503002520b842500340103d000000c2c040c9080e10914007211f40e80300c912011030340c540302000391140c46208140e4082c0141c0b0000c000040851000b140a494041d403c100030354245501740c4501d014041c201aa83d5001e1171141034144c2c1c0043c0700905460795440e0206031507640b0319003032b08414040f0804007c0010982c00f030007103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 953908228 1250 953906978 953906981
    0x4021305102405042705390304120306080d030911040b1c030504170109052806090f020405041401150e0c0919090203070807053c0d 58
    0x302c0e04541c0005215100d001a000044001c0b10b80d8030303002c10360810040115200c0b80f00c421254401c000c100f21040c03400c2e44015015100f003100c00c0040407045804066070395080080d02d244464951841c07002e0100e82601e0b601d018440600040c12980d40c1840900e6a203120f5086840038100302e1041d0307142da441d80e60016020b441090004c80d5800800c4d012403065040c984240c0d954804e0040081c0320b03c00c441c1c00d40c0c06824152613015410000100400b00303009004030340f400f00c00c254030700c00000c0100c0035042081c02d1903120712201d0b0080d100381c0d54504040c408a200981032641200000039160f4140c5004890030038481ca00942045c1040100810312070328000c103280e0210303072b04024021005640810301000950380256410b030341c1c2520204090307158800c05007040920140c60070f810000415020114440980d01ca1511144c001040052241c1d101548680000150400e82d05001080054000d8000608107480324000b1700c00804402e080300010320446902076075100e91342c0d00c803500382a80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 953909478 1250 953908228 953908261
    0x21911100903021b0f010c12200a060507020d05030105040f0e06160f020d20010b060d02210f06040c050d15050a1d013302010b010806030d140304021305 67
    0x40c290059220000b170400e502e00c000c0c4a00161744031911074075a80e45d8009500301e4011402d0411110b182c1007101e140d2044900f03202d00140000810801d0b020f480d01d031055a400030021011504400807084c8a1608141582d064400444000c2040303800095028020410f607102e1a695104079010701110320511140c41c44081500d644101c00007242041c180da485210048203800910701e602c42c42c3c00e804c00000103c819100010001c07403860440400174030660000040d401c1d802768006540c09840a2041287d04c0d605921000352016180180441014500041026010307684036480c1e07008441c40b4078100d8605801181007007000b820481404085c6110300c0c000c55005000d2624040f131100d40240442d0b20b800c06030207030b0305440e070b081c1011f2580001181c01504d41112500310001021504e44895a61400c035542c000150303442d1090004051641c00f41000d4065040041c07a4070900c1d500440003400e0800340502103a5036261803000c680340b8003941004290052801d407e000117810712603801d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 953910728 1250 953909478 953909503
    0xa0606060509030c0a060e241c0b03060103030e19030c1508012315070204110901080a0b0105090f1302030106020715030501060e151b0303100902191110090302 70
    0x848035a004c40e824020840340074054040405c140103540c090500d050884000d004c1c80c01d071216103c2e01602030b410780c4603402c404a542c4000c40a20401c0c405036860340701d0610801c03011001424554503646015042041307198200740550300d4034000340e242e559202c05003001950b01042d511001540c40700c03400b00c400c1000700c044000807440c00002445a5401c0211603040c20000c14040141c2c03900f0741000341d03e48100c201b040d05620280300f03120250340d8900c248003640c002c1c122200c0e650503080d8001042d8000050010380628a0048180240d90703002c402c1d1909d003e016260744d201f5038200000100c540700036455400741c1c0c600000020842c1a404540303103081701c880244204062501080076010b0340c1c824007502c40040c0c1c0001c50348006280080d990340703280000080072403900034030039000000082c847c56000d0b0305920000a00810b4020710519900070080c02004500b8916100c0080042120a640d050b08001180101c1c44141d00c05100100b5001003414080114021301d1074040d44070789404004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 953911978 1250 953910728 953910733
    0x81e1803070e0a091406090607110f071a0904060f1a1206040b040e0303040b04020a05100206130206190c02040501050d0f060c0203161a0703060b03180a060606050903 73
    0x10805040c005520310a4500780078070320b1907603982d03d21590001c000c13854080d035440c0140040c1e03880071071091000d20f004000c68006803035240760241c4050f111541d214000d9019620840030071400d110f001c10050140d40028580300035103581644881100e008403c5019800344c030340703203001174901341c2c0c00c03010300445551841c1c29034a8458290138002e40e000b80a00149a88040400a0351900c0c01c0c3d0310601114030010000280b43c4c1006112714510f4100300c9048410718000e409100070b5280409181d402084121424051000404c00003503c41d1400f40ca60520712a59178020780440d036546060343c000c1d07905c4c198102d60050006000a02e456030700d50082c0d01541c640000841e030303420305142185059030080d8030007955030341030764800b402840c0141e400000c40c0010b000c0001e61000103100740d090240115454081c1801b02003c0700c8040c10084d03d00800c0c1480d218042000d81c140c2825694071900a48100c4031003008440744509084501e44000d107000d14007039001c501c02c0d4202010308502d0100703908 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 953913228 1250 953911978 953912017
    0x120b120307050d0509150702060f03090d020708030f07031805270703020a0914011e0f0e030303060d080307091508071b1707060209090106211b0507081e 67
    0x4144c500388034040d201c580041d445000014800442001004d10b184040c00007894461210804282600301741e84e0442136800c0945000001135040091f240035101300310240d850101c40d0215904540304445000f02409131280454040100e04407900d0010903000d01040c0940140d0700700e0441010203000f02d00585c02d1004046001a0700c207100343d581c1c40703420382c40f840c40d05410080e80380c103819280c03100103042200c007034465503024482040281d903251454544004811103800050203078042610280e0090b0320034000c110321179840290326206240c01c0042035603a500c5d1000c04035000c034a90f0f00b046c0b1a100c21184d1410311954419001441000c055460071040450030074840c0007035540a0024166104082c500c01c81498500c0003002c59520807030006242858500c0414ae240a00741c1c019030200d02600b801c00d080c10010b807804110360920072010056607181e84092200c02003030b0000ca408002011421008024142e802c88041c0d20b035040c0a100030b00c0c4d2821134a407003036100060301c9017210204071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 953914478 1250 953913228 953913253
    0x10f080606012c0d050607090902090901030209060d06020a0801050a050102010e0d050a0203040302091005090f092e15090f060b040b0c0c060d06091a01050901120b12030705 76
    0x59181d004180503510f6010394484460750191801000c4079076110b203201442e07040c9540c0d13181109120b00c82c2c450009000e4900e400f00e00905080030961000d600c03140100008256540d070f00aa40e810741c1d50444490f26951074407800b090000d00c1032003000746103071304c0003440035401034101c1e0803581200c4085460913103494032680124280d40e05070404081c00d5008411405102c0c3c019409083c008840e8411079003450343d00e8002070100c000c01d90303880710455030300c21b42400300e424100442c0c0d51042000c020502c09051207400780b540c42d00590015500300700c0080602045400d40d110b8800c0d94440d14130103012030a000b0100c280c1030f4a039031084201ca1464445480300d00d00b414010030048440244415040c68500050f10300103a01c000325580c40c9000ba242a20350a03907a1740003034103084c031f4002d40c002030140c00c00040b4411950b21162110801c210441750b0344031a03920004842020f0000e10b04882440089004200901809240b040e844403170942c038904e11000c00005421494003481c2101e00303035000344 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 953915728 1250 953914478 953914483
    0x1e1b0506150607020603160e031002030109060b070305040e04080403020406080618010c09050114040e070c0c06051206221b080a15050d0c0806010f0914062b06020c0105010f08 77
    0x83e0f402900030f0700510000780c0342c0328440c00d00700b920350042c2042c03001940e440002a0a081c200318400d0302c00f940c084014071580038244101805401d248038030702d281c8819910b01901c0c50060744940317081c85a803480094104522001514011680500184a03a944824030192624021110b403004545426441a4011014020300d152550310782ca0f181e022900300001111020000032017844034080070007001414480b4102118807a1030140d951030841c000b00d2601e4103040f2039691010080200070f00000d41c04000c0c407400180c01510031a91141c407440410944403100b60346803115075070a840c00c0c82c40d6102d001200c0001d0340d140d0031903076018000d948106440c0100c84682100c1101c0409150f0f0070f129a082c044000707400755000711b02c4980450b40c2c4a542e140b600d50b0903004014a0481c0030310800000d0403038000e851782c80201100c610304500e4031038007150408002d0003140c05c00c044422040c80041c2c1c0c1c0ca40c1001490382d0404019540c40c40032009180c040c007000e20902180f01c6040400040c0c07100003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 953916978 1250 953915728 953915737
    0x2060a09060e042a031b03090302070902030c0912160816080303100905070207033503070c030e010e2701150f0e01090506030a05040c151e1b05061506 66
    0x252070189500a400c05811a1213520b0801c1c14245a41d80580003401d01303030008084103000080c0e80118000b0b199180003410032045500c4641c50900502c18090854200d10582daa86903050b181840c09292803100d40d4a050359a000803c00080100740c04901200041000d80303030f0b010101c0c413000d800340d504c180e44d030343d24801224200200040700c00248007007009a009680c01400500c11209040d4a9490f619000c2d01c22840c9105990144140712120310030200b41000107468855196044d85840c04000e014030000500040402010010880c26a8084c0040d03500d0014007620042c2003416911005407541481081d40b00040c5d010800021044001d00300100002c0c02a80c0d415400c0040c91020f40d03108000707410b8581070104041000c00c2c1c540b2030385d002e54401d0341c00e0302002c6554203040c1854200d0799055000955103880c0c002100391940e81000c00e4051004001c02c3d012081840c0c4102150b85005203030b0406030124030702074184103106e03000030760360702550a660494107012603007810001c86115 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 953918228 1250 953916978 953917001
    0x510050303071106070b07020303011806141306150507021c050316020f060a020a261b0f030318060a092a0902031006081501020319030902060a09060e04 67
    0x20070002c0c20001041d0002c0c0c0708940101030069418007069039207000e1541c108551641c0143d0011004100030716000110340300d0049010401c2040301c0c00d15001019400c181c2090070b0081c80c41003400f020078890350b03101800a00040111180030840b03190000c0082d408000c082c2e2003202d00c64124441001e8800c21100001c0c1e22a005515141c01c1e5816110032021104060381e100091881c5c01100c0d4813428010f1a444080d9400b070800c4a82ca4504040383c400d12182550101c900100e80059000c801002c42c0c03105050003202145a1014070380603460301c0c1e264100d103d4640004402c0c003001010588040c040d5116801c1611915560300c044101107a030075803009040c940c002c000340c2c1601b003048444079103458200d00840d070140f9290070041d0f041c1c1c1d10980341c1c090001880d074020001c0e26070059079a40c010302d080403040c1e01c0e90082070000756207005074a4400385240b6240c0400840700c0c001d5010074851a40540895290041d86c0c001a105966078480c0502055096420702c2e014680b502c82c00d10400c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 953919478 1250 953918228 953918233
    0xc050103051308180907020d17221b090f150e01140d050a2103110a030e030c010c0e0f04060e0a0b1c03021606020102091e03101107021008160305040c030f0b01080105100503 76
    0xa003152002b0180070049400f9a5401d1203200e20788024010300d03004c4005003070f10400100707514003100c0c0d0703001c21202e03056114580c000e0851002d02c0180e804580c054112045030080384900c14a0ba8001a0742d1100000d00078498414400d0742806c02c10003000501c01e40404150185c0380034590310054060702d11050030b5001840c42000002400b502990101c07030944110012a814003141c01e54582c01c50b2080041a404107015003510526441c1c00100b000a84405460034006c0c03d24185400c400240050103900d80141c03601481411a210f10442c01a28103400d040c2266503120340c1030180d10b0302190402c00301080ea001c04003081090050007110401c0002034a14006540e0341d08201860750f55684060b5818050b02070181b071240c0701e0303000799403003200b001c2040c55443d4403900c10055241d25080c8940d042c04810010851180200354640c48940f2460602003196592881c20001c207030056000201109100c018a078103010034800408d0503140710350000c000355180e960070100c00681c20700c42d50354940d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 953920728 1250 953919478 953919511
    0x60c05030103050a1b2d08070609030f060b030d0509130504120c08040503030d021305010305010b03040615030206120a1a1e0a210c050103051308180907020d17 70
    0x1a0a040898004030403500d5250b0b1010349a01805d0003001c042c0452074101074000410100020006d8075004c000d004000090010034584900509a10050700c0090080c0d01d5071164801400300079000020207000003015243c800e00c604001030070b40c0e040020389600580803140c644002c0025031040c11701954200c0503244854402140c00c840000c0301041c00c8862034001d10001883d92000c00142032540b0a1100158a95140d400001c107140c180d03030b10850425003005d004221a00440007282d8016820484c0071a41d0700c206030b0080c521009039400290090800200c036541e4988001e00c2a0213504200c4c0c0c240510401c0c4030023070806040c0b101d25141d01c20255440d10701748249201c1c00c128001c10240508803400d684081c030110014440400c001c084003e101c0c071a08216420305100040c0c442400c04112034201030728056000c0c04031a03002017a525002444800d1070340c480fa164080c49100411074641440e000c1c1d002501c03485046100d0000c500c0c444064201804a0107601e44074020740701004a04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 953921978 1250 953920728 953920733
    0x91f090507050a18151202100c150e011d1c0c02060705010914160b0901050d060f06030c05090310050c07080c070512011b030203151c060c05030103050a 67
    0x1084101800c54a9118035400040e00e92520505003000340400610003a50360007058105064a900b01000c0d034a4803514501448a500c00310f103e00300c0f40e90160764050742d45800c1901690044170415000e80844ca8407519034006100d15001078075002180300c001e001c81030124071003110203131411040030500d8000c800440d1100c002d446004400c0c120620b0710a4103129107401142c2d15506c03990f810b44035a5101c1d01c00601340701002c0e4240d940c460f590300040c080034001d10142000d00500e4000c0014029001540c407003140e02c40c3c02a1403a800d02890100302040d40c03580400d040106c90f1281401007401e010758510094080c13000d0740e180500140c0036000211034180321000401e00200041c184a6051080c0030100d1070200c0034100003015980105140b80c00c1a0400c0751004030007400c100560b06022111124481c5600c0c0351703004006c2403c0c00360303c13030302d40509040c0300c2483d60707000b82d03040000540d145034901c5c40c0c68000741031680505800c110700001410200c98074403013404040d00c1548111b004100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 953923228 1250 953921978 953921981
    0x3061b0318030f14120f0a05010e01030f03050a050c030c0a0c050609090a090807080c030c06220b071110020711060f0a1209140105061002010e1b031006120b091f 71
    0x20408a07213018a08409640e200da40c0b0001541c06c0082c0385a1034013080440c80c824401c403405011810102c00283d03155a81e20075540c00300d11000ad00308603002c031310209840d0003081990b09100000041e69121490383c9001a600d0780c0000080e1410b9002a1000800341003000407110303100c501034103e00c11a603c002000b006008800011034122004000040210701c3d204050f03d0200500c8000c1e65031070031480f164614119014010106036815025012040d040419400c6079065021450084603510481e00740d035000170034000a01c1901407400c580c0030b4820316600400d1010300c111004100b100d440e0003803080d01d014101c120f021007401040744804090042c103580d20020401503010500a0450340e840d500b074034075002000c2b051f81d11503051000e035107400d618510003002c03c1d01c020407004644080069890701d07500314160068860300405001a1000d014412018a64507014412160f07201020805511003800c26115040e41c031000c58a84500810310314105100c1401104981c082e1010460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 953924478 1250 953923228 953923247
    0x717030702101806020715050702011a0d0f05190606121a151509010305090105041101030b13050106022a060a0e1f020106061b0203070e090703061b0318030f 69
    0x441e80070b840000300c40051380500040c000c1030311a980d05084c085070115108151240038001074156410940c1940149080348a6031050603400c9400860401050408520107994004003400c14050040c142d044c0c583d695880c0c4204a00c039840c1080135503510a01455120000900200252140b00d540443d4103072040f85039402601aa180461010144002401c6403603000c000c0400440085101000c640e098450154003004a0300240920f181c42d9072407460303145144c5200b42c18556500203036415030300c480002c82c400d003203258000c0005586a400c041d648031103030180e900c0c811190f1683c151140404802c00707c1d00007005001c072410580c66007016100440c428804940108001040741e04100c401080035201042c070342c000241443c10403000510821f001e20100c480f001000c0c14250050302d00068480c2121070800d2009056140c80d40ca00342026010b0703201410660904141d00000d45010066045030720032901e0400080200003190251500b0181000e000b05451202c60003500780901000c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 953925728 1250 953924478 953924501
    0x6050a1101020408010603020f03010b0a05041109090414061e01060509130207150c0c11210d031b080717071115101d071101021b03071703070210 64
    0x34280218804655401ca0f0810b80c44a02c29039140c210420035410103100c1c8001203402a4000e0003241c09060102d0804085481428040d030f940703103040515060024199014904018102036440c241818240f05d540394102c803110990141e0008640c41034101c3c0c009003910350000401e0309290780b8086040d0343c2c542002c1d01c00c0b40c00074101070074070b4908221840203040d210b100307465203900400304542d008205c0f02101600d40500c041800044046100c0c00081054a08212180b14500b000000e0007802c00055403080500340c03060500744400590150042c1d0120301140d4450140411451400c4a103078006907a01800310300c000a480e400711041d8040154004181c0c240900a4041c28551030b141c040e07070301c143d410380104620600800c01c00c0170f140003000341500c203454043d1020611400c0f2180310041c4c0402c1c1845443e900503450241e0039016a011002000c0d19071f03201092503040140c0b0ba6200c048115400e08121040d610f015060405590081c3cbe03560b802041480302c1a09408020540380e11403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 953926978 1250 953925728 953925737
    0x6030b042d181220010b1e0406050901030c140d0f291017030406090501081503100e0f0615010e030709051303020d0804080a0806180108062a0406050a 66
    0x240b1011440031408a900840c3c1566030141c1d40744c82102046a1080710401510710740d040c140550850b0365503421841c0141c1302c00440720080522200041c0c02400c055005541203282c0b800004140150701008104480701000000032903204038042040c0c5809226000340032000b140c480e0404900848903011314111030f04488605650942600450ba00080ba40d0903c0c5001002c4144802c5442036008003040f069180150304042c01c20401234540c9000b0700031241007084035400130b2074408845807841103d00024054541c80e000011044002e80240c41d132079000340c4074440c0c00c0c0075050000940d00788502c114840650130021104011209183c800ba142603161040940c00714040110344942805207010078400c0c0c086465904e00a07050440c0d006000c000c0c0070b490380c1004082101d074030854544584919080486554840004100070780d420000c0100d000020000300312f5074000101d1341d0152070031240b03900d43c2c1c800640100030340c100840b051803001c0509010070071229005002030190701c90b06050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 953928228 1250 953926978 953927021
    0x2120a0e0f011e06060507051005060a1814060d0c1710023702030a081801021819030503070b07030209091501090b190f031506030b042d 60
    0x1c200d82907031403020110400030a28000c5040000702441100d009084030b0070b150b0708044040d00d5007a00d807400007201401d01c03612403000808950712860326401901c0f6050060a10441608030306004141c0300034a0994031204201140092070091200101c00754803070301000fa01400d0514048640100c08024511481ba1258507075220000e80003600055a140c18007031290030a08601800008075960356200c00c00c02c14107640c0d04503034003100300e50302404141400c020a445098044410b0b905401c40d5640729480822002c048144256a00c155858203d075642e80d445084104000ca484080c400102240e10800050780061181c000059029036181401810004c5c0079012982c1a50100c6076075841c50f1ba01e01160800f503811050303202c09016440440b03403c081002c80b00c081540d04151180c001e00c24902a4103200e144070b6041032207000b80710042c9001c0d540d0b6a003405000b5000c0904010321903400c00c007044041700155400700515200014100d68410000140c0d44024000e002d0a005c02d04402c05 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 953929478 1250 953928228 953928253
    0x233040e04050c04151a1608030f061507020405060d081209100c0f08040f05030a02030405031009050706081008032b06030305271f09060302120a0e 65
    0x9040101502858540c207440c01e0700d8510b080680b28918580301e9031812103c002c084204003586804d540400c01040703841c2554101303042c3c82d401040c41944034080704121072010000c42c1c0002d0741c018031007203c040e080e50b02ca0900b0400078042c0490b8500041030b00b44503250142c5015080242c0214028003415000180d5071290402a40140060b01c041050141800042d0a0800014042000007103080000f00700c00c0724010491040c00620808014001000c1414080f45890004906134410203c0c0d590b104e80302d00107901c0b50044d22034907200c0e00070300d03882400d020154006c5041240d031000252543e10b0a0100c20b80d41c0d160003038031190400030543d4000c900a10100020207452440107001c0843c4c91884902c075103c40c14000100b644c2c541080d0003040040d0700b002c16240030b61440d003d1000c0d0303030000c1440000c0007444444c00e40d80c08807204003205540640c8055480e060340c2c1654a11a8050f281c02040d4281c1c801c801c54145514444000600419030b181d21180f44094400140c5800c0d01418 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 953930728 1250 953929478 953929579
    0xe01021b03030a052a0d0815060912010f0f0501140a0b04090e160306140612061801090215040503011401061d0604180618090803240306101401030902 66
    0x890a01017640e021001641c04650005082580301c542c01d50460900d507000700c0410041c0c0101070040380100034070b0107a0918400290030202034840d8030003081050848012040b00904802cac41940355070041c84440a40c0c82c00e24a06203016164182111481c0601d0400d189005185414104419019000340c094070070089900c08070085010340400f1031107801400203074843c8100902040e100d41c40c1e60710904054040440c0b015403001e070a482c88865000000d40382c07400343c140c90000a5000c00e0a41e0704031017000340740001d0800c2d14000c0d030082101802b94a01035840c1c100c28040e000100d540482da0300d190109400481910401c00b41c071030b41c01c0990740d07003140a20b410403d01003494242c890406121807140c643e504c4c6541081e5140600410b10640c550320010310024107001034603c6810203003405851609a10002460054201d032054603200001d094943e0a90003a501c605281d004407101e158804c1c020000c505070010001c0c60724010206c5da44c29000c01d0307606030100f074144400070b400740081c64 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 953931978 1250 953930728 953930797
    0x9120309030c0b0901030609062d08010c080901110a021506180c190315060309050a1e05010e070308041e18090c0b0f04051012020a0e01021b03030a05 66
    0x190f1105440da03e01e0700000d41900c0e6283c106403621443d241003004000708240101c0d00022030400c0d0740c0c0c5000c0c9090700301803159499801030302141d030074080740640c0d841d07000520900c5006584001c1162044c1640030700380707038403c0c40004401a405012500704d400c1c010714020703030804402010b0a101c000c40072030b034205a030812941aa800c100110702c0001c80211042e40007042a41480d04121800c404034281c0350044c103d0007107104141c1c0c0c52800d001004070821515250301e4200303081c1440041d4500f81802c5046803881c3c1100d465090900942c007894000030100b00792a80540c080e400c19090080060610030344040e0380003480384451002440390840c26452006101010001c601b06e900c504103400368510f990300601c1041c50030000c10104105103000d030b505480d400c541005100100941c00c5604000d2a9860565580300141d20001c0380d4020500350501c1c0c0007038007545c140c1306801c40b110320305034540002c89406802c1040b0382400c2c03d100e40010702c1c0c8030078002c0303585c807260b051801d88a001810303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 953933228 1250 953931978 953931989
    0x605180405010f14010c051207020f040504060914030405030601060509040f050702070518060306150d0803071206090c0e0f0301202505070308090f0d1505090a0309120309030c 77
    0x4907051051121101324803145000030b08108070381d10102c0d074400303a403002c60b09200c500c11040807a89104555030058004481c290090050005007094180000140f411880843c1c14500400d1072003414000481039a04603000240a4040c80e072030304200792019404200c219a0040e0b550310ba90004800501c6000c0c02003080d0f41c028100b403410710050010a031585000003541610036010800c1980e00007800c80d130b005040000880300701070113001040084018650040c02c699002c4204001a5802011941280d01689007402103036520b0340351004039000a01e0890000c0c0507a114581241083c1400745440b100250001502012641c9056030010b1a02d403d0504004001240c29100700301801d82c5038141c41007644000c543c1000e81e20503640d81600e1000400d07540d0080381d01c89040d41c1d03034620041d01e824040d28182a440135890310320391032045100024010361418020403c6810009158a103859041c3c41d000802400e054130f640c20f010000d601201000020507000c0300140040032020010320 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 953934478 1250 953933228 953933249
    0xc1009030305071701031203060e01091514060714030906040b1801030506030312090c0a060210060b16150207020d0b0405071e0b03070c0c18050c0c07060518040501 72
    0x10518005042e2000a022141008407154444619407601e465007411650f0040ea420b5001c40b01c000300303502602c0c076940301444d00c0541c0800003800c40f02c83d030807180200328180e08041005885211030b044101c607080320207030440f109001e0040055018040700d00907101e00d400320b9003044040c03000699643d000d908000210440071450301051382d280110740b10001b0090809001c10718ac000c02196036401101001200e609110b408241c0c00c100910074045610006414444825182c444c041e6560b80310340350303107440c413440c0200001d00d21442500340c4442c13400c4144645071241060701d401e030080341c008040d0180644e003003080c140141d49020369100707807500c649a0312586140c0360510a09044455000700141d45d10a4904241051409040c1054840c0c800080b516078031810310032034285680c4d060017090070101c0500810b180725079020600203100c1c0114280300035a603070500b051707aa000d6100607005130b0b0702104040c4034190065025040f0003180c02c0c2c031030303190340191000141600c2c401e900103075151 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 953935728 1250 953934478 953934491
    0xb0301110d0b040207020315040c051504030219050f2202070f050f1b120a0507092f07080f0706060b030f2d100806040c050325051003020c10 62
    0x7803198011100c90840456003181070101c1d40e000b081d05d41076400719074000e00f02c0b48000602000b042510b007201034003010b856040480c0f4005141512517000d4003080c2e1051200d0540e01004041c0c014650041c1d80b00500529003030b150210902400d4000500d503001c3c06110418900400c40031807000c0d0a081340142d9802560000500f00682000781c84000051150041084100402810784103410305880644a2804448421080c2c034200b101101c1e00824900400314001050003007a0881182d0a5201e407105501e2110300e20f1860100e0b18005a101c4081011b01c80000030400b210041c09800182200d40340c603060300381e9550030481e03a094211411501020050264034100e49480c0d550161006c0682944c082152001d050030010040e024070042d004440091400c95030f030744280d0010309030304080b2503290410b403402510001080c082c8038040e00c50324455a800006101c07000c0701108000c0100c4464a0800c1c052103104040d4032800b0007030540030810007114003010806c050b90203503030a6000522 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 953936978 1250 953935728 953935747
    0x3030106030b0907090b250f12030b0d14011b05070605070906080f0c0f0a0203180916110313090b0406050a0510110a05010c32030c09040b030111 64
    0x212403800000a014503c3c100421020580080398102582e49401d042d41c0c0f40c061040070302d082003d00f024541000300000d08201f00300300516044240c01403050b2000e04010b0442d210440071215641c51141e48501003501c0003010900d002107044071118131400204900040b0500f00c40003012040321a40040c0d0f00140f4042800450300c51660031024500c5c150030620701e07004000301400340160404200c0c40781e0b500420b0f10741080008882864030240d440f25107841104070702a4030380c1c118181018072011554403031003c902c0d282403020310584401904100383e2201b01c1080302c0910310407600c0c0c4028801000b04649503110030403a04004d003910b06001c240440700104bc00306503001507111a0281e080b000040c850703503407000c005019200841c5020001c030b2080c803080c60300d00080035002610390351a0180e40b80341075522910000310150f441a0404800f0110b09140400d24050798a2084244050002c900040500b01c000d22481000400105d203102c220400039003154000a00071120301000280a0310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 953938228 1250 953936978 953936981
    0x60e1606090803090906280b1c06050d0f0302011410030303180c05100c080f1b03090d1212060609050f030705090403050a110111030411060702010c080901051b0303010603 75
    0x18141c000d02035814100b044c000300c0c11024020341403034840d080c0000320342d603041e0900a0070704034504c1c824801e100442d40c510f200e907032542c8007001c070030715401000b14005407100360390140008031000500b100044021544070b41142800e514000c40465403500444000c4440d42e80c0b11901801c02c56450071036140c90f40c640603040307036078000d0003500c943c00600d6100301042c0444c01a00c100d0703100792102103410301d80d01c408840c507495154004240460128685a4264419000d86450400d0740010f6039421404000301d40d8074022090080d6100c8060350000c0d001030194010140031b19802e0402904c1103521100d45c070306031003c6400c5003000400ba200204040d00d0454041c2040c448168042e00c04c0c2c60804000c9400c00c1d40c020009014050002050000244106041403140907400d0003001000d480c462840025401602d042c0c8504030003c02c1c1d00c0c000d1034140304860380258140c41d0f0b5060000341d40d175107141d03680184400e681400400e1094800c0b2103040c3c2c141080d2042401702456980d818050041c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 953939478 1250 953938228 953938247
    0x417040e071d01020607110c03010f09030206010602150c07020a030209040605160c02090a050705040305031602092d041104020408011409060c1602031212070306090506010203090d060e1606 83
    0xc40d107050b29040c848a99801142c101e4200a051800e21046618000784c2481c1001800040341c1542c68044181090090781d80404030700e43c401c1c2c0c01d941d05039a8480f01240d80e01c0c51111080d41d1044c101000c1081c5464410007003080c00d01c080c06c0d0b520280d6681d0000307025400d04a1f01640c0c0c130780d01e03801000010800c90b041e0190002107428040102411500480c240c00001044038441c16600c0d0301041c40d442c010404d550040d58048201c039600c601001c00b5511040101c0002c070300401c005404500d14a0310b60b1070f44d2000000d50b096480342c0d1846c5201c0030705031060141040c3d62014100708156010f8840e80000c10142144d04008030301d0600f03010380b10114100081c8491030603000340c000d202c5c07224a190215511a600001071701d0541003140002824000d8182152085140c00a00c0b04080c03050f00d43e00f80d11410341307502c04002e04c594400c281c1050b00d401b06c50b03090041c0c200704541880b42c80c116030b54201c50742c00b802000645209543c685031a003003140d600c0001201d8500001c20a081e400040c51 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 953940728 1250 953939478 953939507
    0x80d032f13090614010302070516170106120f08450301050403080414070909060506030c0103112b0204031a130506060d060f0c120f02130e0417040e07 66
    0xc2081500e000130704002c0344c2c410b052260401d40c0000d126410304c10108010801e042005011009440d0b6641d951848004601401c50441d400c000380007410480b03410b006022030750841450b003403a18040e551701c000e9600c0091000c041c20107400c10103009803801c401544420080f6404942d0220840d5841030743c90b008516114031980c108810030002176844048aa0415400300b4440f04110310340d0390342d85c1080810741040d0b60513483d1a0341e0800303001280e00658003420040d0191a8640110350044098a07049021005426401c0001c1c4000e01c1400c0840d40310520760380c003081190b800340300703000050380e00540c030955220700b07180404160003244c45079883d0405504d8030905000d038001e40d5007984030759000304894424110220340e40f0074450903410002c1e00c1b04d08481c04000c06000440054122011f41100c410550303d8454201905003c2e4400c0310482d0761448000b4444a24000000d810400003c008031803907400c409030443d025005038041c101904005161070300601c2c000400421150041c41d48 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 953941978 1250 953940728 953940731
    0xc010626191e0b0c040e060108040c140102010207050115030203011409070308030a090203030d1e020c060609070507080406121104060f0311210402100801080d032f1309 74
    0x105030188040e00001d110640c4000418505080c414401250004568000d0b05002640042200c00d841d800c00400036242c4e034070380c05141c0e0f455503001101c4c02c440c2160005e1008100020074080941001985410004144000362401d8002e548440c00c5d205400220045922040c0003071045207400e004103d00c4020501c0314107503502d00b50715540c0d50381000c2d1102030700c5194008003098040c203241c1c0020b090790744c01808480d80c0d402e04481117401000c4600a044400b000314540500c164014021958040ca003803000b00440d8640d50108401c00b00c2c0075016106008081000c0f20015202c000900002d02c0d0320f031100d01a011b405d04041082d03c84082010311250303030401041c0320094000c04003021004052a00003154400c500b203205051041c010020301c20503600440c4000044102d25203440f45109603141c50100c1c00c02c085c1036481101c00e016299041c0c020301c80c2030400d280f20fa8810200d2100e004503002140340b601f60f41c504204988070387e400740304400052460f11242a030341c5200061041110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 953943228 1250 953941978 953941993
    0x70b120a051609120503120c0a020607020c0a1e0510022a010504030b0a060503060a09052b0c03020319120e1f1a030714010f030501050a060309080c010626 68
    0x1801d402c01401448003011070740d40b404013802420810f0311f085003054000080d0300c2c10425000c03550350300076464000052107800b001422503440416907804a800182202c184c2c9414810341109511080f0340c480032107604200c0016148d03955000c43c20741c80c8400d4014000c030a240100b50340b00e490085032065203800600c41c204a0b5030b64440308460840e5040002c489207034803840d0307800025165580c002c031350610609061008140103540300c0f200c068401c0c5d04450000354541090142d40100c0e140414490a031451020380b1315002ba8261250710307200b4810b03079281071345401900d1704030008001501c00295101e428000b000382c061050b0305d101a00100108000200c05409451414031000d92178105612082d44026440102d1910301c100340740113007919030242d202c11034905442c040c00c10103800941a5600903841a000b0b1140c1410f9903805441e2568680c00c150064025103e14036080760300704020011001c0701c1d1028481c541c0980780d460a1000110000e004190000d800110103a203260440c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 953944478 1250 953943228 953943271
    0x60503071202030a0b0d030908070504090b010e0402030a15091a0907091d0708012f3007121a030a110406080318180c03060d05070b120a05 61
    0x700012000070821015941e55901e804d00e4024003400b02540703401030b03010108001010f41000290301502c031901e044132001c0780e50b00108070940f55600750140c1140d00080042c00800c2045929590090001d41141c1501046954244805d044118055109983c4078405001c00000102c0b41c0340c0b40c0458082d105503810a0101c0c10f480d81d102d886075208655607030001070141c4c242c044402d814007003c0c0c400e030303070046649807503180c0a808481040ca490030300511821000d1145000905141961181c4140c14240c4100c1c081c40c81c011411500f120750403150816820112460a8141c41400c079a60741904d06c034621102c1c0d4040d02d4404030800307602124040714a449031400110001e400e038001c0301c074171070351802c2c41d012600802c220f0304011080e0100050541e2004030021a60000050540342c80c14200540800c4c0359181c0070544240626140070800314209150142d00500c59900890035661942d40e035005045196000b07101000c900c125640c20021102d41d64410380d0b520a02a100407100c0e0403500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 953945728 1250 953944478 953944487
    0x105040504030203090d15110309070f08030d050a0b040513050f061b0f0d11040314061b090f09070e03010f110703050a0e06070c1e05310203040305030106020706050307 74
    0x680d225020b850b006c0080020312860720350482c5280c154640c2003200c500c441654400c0e9a00855a04c00d070385c801c82900152040c1b2810602088030006405181400110980c02003d400b014010b20fa000d92079180364400d554a500c11180502103109a0f030280c90b805c1d00d401c9040400002540d0a40d030486001c100f12440030b90b100301702003114017905c6540c98070850103440d45030250302c151034031440c6440f01403c08240004020801d0780d005401000c0b50030380c908211590340804032640d08082c0c038140c580003142d00c00b4201030545440d004000060b6200e410010422010b0201c44440c0000d18142c0d0110303807400c007032003040020800540f0034000034002d0300c01d64000d03100d41c85008041103000940c00400710f120700c040d40304903e401001b16035203074aa400c281c50380b000c407409125510204c1400207140c1051394090f52084540207040b856264030800401c88410120b0700f5075040c1d840200103d406180c1e001d100442c4528840c0c0c80c1c0f90b8495050400003883c040854001c50240a020801e004145420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 953946978 1250 953945728 953945737
    0x306050a050111011107060b1305010609091d0a05010b040e0a0506060d230309181005040c0c08040e0114030303012409030203150403110a02130506010314040c0306050105040504030203 81
    0x1c1c240841502045500280182810342805e5540d01010885030b003003000e03c1e0003803807204000300e415111200040903070200701c1740300381b1500c00030600ca10800c00907400c1c586c00400340d60102c413003c0050060050681810801507140c1203500ba55030301942c0340320345418420313940c0b2080140018500030704145d8405640d004003170619442200305410040800c066401210000540e040c0181d074541d1460a0855494119114291140da040c502c0303401c0341d040c1145464466610b030b42e40728040f41d24102c140802804c1003070345c8004001c5255649804540b07103800038001084811a002130035072601c83e1100d161040b5280d0144250010001081302e0f00d01906000341d1254007500b840c1c1100d0a40300165000c1d25960b00003900350003611980a02c048403030700102d20842c029142d2083e8024010750041d119400802c0c020740c002c01d070b0031000040030f0840e482103a1001040c140001d00c451859014000b02d501114200c1c2e1800102030144104030490040720700404043d6010300450a050390040c4d20780c0038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 953948228 1250 953946978 953946989
    0x20a0e06030c090310060914040308041101140a18050a12030e0a050a08060402040c0807090605180d0f1406040b04080319150504060b280302071a04030f0306050a 71
    0xc008100b446900000301c45000c0b0004007100c07000021361407490090851403165440107032820300c21000000e50703445198070542c0c0c5903032000102e44c1c0d182d0f101400c460000b44035074100000b10071400b20f807540302d05c01811150004d80340c0b030144150f04a010500c4d913009412082c012070110b4803c11000c0c14000112803081d5040c10008440c180400c04240e880019600407944421401d80010700c644012032154016402940c050144035a030800668224400b91603000004404005c00c0050301c0c840c0b00074003005c10b58000c80039140042c000008501a07017060341034903444000d0f242c400c10820502d8000300b1501d44400a4181072030151141000040d0003007020300620400000104401070171070522281481000c41004051044110000c0003031460181501a80c9080c0010401121510580b40001d85400c645024604004000c010301001e50700c044052540a1000b000000c07641c2c031040d031810068040a000741c0c9000c0c20014103841c5881d01c41001d0600e040c405029a8656042940076601c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 953949478 1250 953948228 953948239
    0xa0203090603090c091302040b040504020913080c06010f06020d1107050d080d0c09050316080c1912051006050103051e100e27030337020d0c03060801020a0e 69
    0x35503040c400344c10a041004200ea110f054101001700b00d1180e001010a0140292410405260300005210841e071042e10003942c400111800229404208000d42440c584901001401c11100700000d40c58600d0a070044028002d80a4040c00030a5040040c22440c0d00d0500e800c44c0800b040d0101c0d03580b1b4902c6d50281e14083e2000088101c02d20441d1002c42e1000d01254408010744041c031040104540c5542c0541c520a00620039111002040c0c04400e10654194074040d000b2102d4490411865505131400350f0540040c50800107a03801c9201001299540640080e0040c28205001c01080343c100380c00a50502d0701d068207000c400502c0c7c41c500c0800482e41407260040c2d07100d2441a059003149580310b40004c0000804100204c00704500044c3d098980c3c3c28980100034011159580300e0001325440b0403d24501c08110b03080981e440c044c00000d0044a01c0300300b00d0540f84481d0016a400704031b809074200c0c0c40343d000002030390345482088010001907000310304003228a04028480f1030111142032056 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 953950728 1250 953949478 953949481
    0xf0613200a0314010c0e04060e0105091e010315050708010602030304030f02010219030605100507020d150615050702010f081311040204050414040615031101050a020c030304060914060a0203090603 86
    0x20703200c01d0400c1c00555000000e100c80002081802030107841041401c40001c0c11186409030750303060a00070702e0259294484070078440c1e0300785824080d50031001003040c0100000301c400700c1341e0340c0d18000f24a4007860103080c07510301020000d5002c40035900041c111404011500300100002d0740e0100c250303504298103241c402080d00e205041280680a0b0364a20010404503025442559406503c104112101030311090b44192240c481030780d4600989401940242a00421b2030010b031218410a42d00c8980080010f8100d0302d80c454000c09007075501a60010500002d0032205561300005000d02800c2503251401c0756203031180790800c020007a60303401013015a080500d061a80d450750151409084090020000c166000c10218011101500c0070754401d441c01040e6401085004451000e81c2d8102d02000850700c00a0011259503101414030811401541c0b80d05816a0307003030000740024403099032242507480c204a425a43d00c030301d0600051040c0000c0200703034816500403050344c1700e0340c4d03045a003540c89 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 953951978 1250 953950728 953950793
    0x20d03082a0c06090f19031106241f0f0c02030d020312010f1a0904020d06030605102301030c12090834110406030606080f0613 56
    0x10402850580e0461000d07405003048510850010741078210030b0100300c903016120854016220881c1c5d600802058200c1d140141402045101190520703101e403030f01a009000342e140d4039083c16425213100d00500c000840d2403004c491381104540d901c510440704001a450010b000c86460f00c200e4110314180a121045160103074003d054078031940b034015059944404916200948030380c4080c8258240c000d018002007030710f04580b00074106483c40f46006240c0c0300c11604082a2a400c04000d0943c0300381c0810410f03640a6550107403800541c86900c000c9018142464814200c044642113550f0b4002c80310480c0c0700c5c40100d883c0428282401382800030f425102c4100440708103401b14469580c00d400c10511108004082c402030a101034a041c2c542288a03a4600c00c2c00d004010f078400801100760380400d0320120315200c5954520310402000040c0966403550392105850b042e60080c462a000b180c035500c00c104003400800e034042d54804d44041491075540d60f8940380d501c1c20728001811200890300f03040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 953953228 1250 953951978 953952001
    0x1115070e0634051203221a10171f0b130e120f070c170a032012030f0f01030b040809010c150c02120a1704050a0206041e080307020d0308 60
    0x2c480d504801562a0140015082c03015540240c0c3e0384414481e00c0700d2089801d01889201488840d0b0001c45042e030011070000189100c5009400d002030120701200c009034009800c001c044041410b1405010b032110b401c400800308c0f1190710b10b86068242001d52001840e0ba4018040c5001e02d240b280c006072181e141c0030ba103885d1085c8910001500c040015002031404106009840c18a00c43c071158800b0303640b194418100c48900c0154010305030302440d503000004e030041000504a4554002c00c002401420b504685042d0342c030360707000400c003d000043c0410403620000c055400340001c20705215551440c2e0720303243d09a1004001a140e14404103011141d41c0c030920003443d95076000840745003c0e40280e001c41c4010b00d0a0286103015210ba2030905a290031020b040c0c40e00282107440d100100c100d100d020102661009004030b82038000c03095001300603690b200190011b00003415201c3c081c064140340b554050011174211068561003808000010380e9040141e012456041c0ba0505940e00c55000b05007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 953954478 1250 953953228 953953327
    0x16080a03032034030c060e07031505090a050607091d060307230a09140f1909050c100e100c0807021c020909061b04081c1115070e06 58
    0x10503030100700d1100f0382490b03402035200200034000d0030200407103c03004010300e80c3c49002c2c0c80000c081c003510794100141a403203540001ea004001300e058034042501c640c0e503a4240442202e814011070082e08041c0500f92494504400c2c0e0040d10040001500307001c0006541c2d564684901e4000f00015000031950024883c41600450381c050312040205443d068010301400804034210a25624040015129290200054054840a80010070f982402000c0e4009060b18440a94403072013030303000c0d18001d03886903980d904043d0982ea850f031580200030310400000490318840c4404002d0701d80c40718008210000d08642015a0446410f02c0300b100d101070b68080c99400c4480694081405010094207503004240e0038400c070011014907907100f0f2081858180c5008501840803c0d5201d220f01d1302203d1b2204142c05003030051402c2400c3c0740e102c050300e01c918080045e0784003141d8000c00424042c034103801a040c11100307002200c0440c2402e07502c1005407592001100024181c1c080000701c0030002c50700300101c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 953955728 1250 953954478 953954557
    0x70816150219060b010f020109030c02060a17270a03140a090b0c0c0a051e040b190305010c1407031209020609060c0c0f04140406020c16080a030320 65
    0x1c000075483d007050703001840b900c02071901182e0031019402c0518418810030000c19417648800c011000703c2d4003440541d03044018000300b808242000541648214291144a45130b031030700079400341482641e0300702e50040041080c030326035002010100019030803c2011002205007034070151680b00207641218031480541c0898000c160000380150b030180c0206520028080a5a0b44821180d41c0c03011b01100c0f10000c40c2c10880703103c00c141c0c80007407840c00360003200c40035100034080c4255844484840d1442c0145600403552070795a403d55418994204442030b641c0300d1400d26032414840395460140c41d51440884070002030360303a00050811592004240e0f01100070250000343c0300e24104a0b034964509480034800d1107030140e080f98021601d424056403a40c2c3c481001a24410344442e92850701a42200c08210030f41c1c051140035900f00441c0886401c01085090010710861840307007400307811501644400583c107043e260707040030000401c4046a05440994180f102c0500081600030b50300d50450014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 953956834 1106 953955728 953955763
    0xc0c0603190e0a140303070201060b07150b12010516090803040b09060f0d020d02121503060117011e05070f0915030e0c09070201020c0708161502 64
    0x40c60358203246070112a0481c62554416070b6000454942140b135078030101c10040200c1d824020400180496003c5610304686030b120004010244c0240003000303034460800d07400d03517191241401c5d00005490003c1001d81007070404d280500b050792400d140000d038003042c0030803452004401c0340c0c12a03502c084c0c010700c2c0c038134440180800b54108800c1203022500a024144540131140010308140c00586001a03841944001400b50658040d020840380c90f0a0280e0f50010340f0002240b03810b440b030501a5048130810281072038050302110203d16441801c00c0a40303500300c040e5402403809200e582e01c4601e002001c05504862604d4a132040580c070500300c41c0308140290203507021162151100050300c0e014040d00010420f0240c0c00d446a40c0141e500054040c0d041d0020b0204a01030641d00c0c01070711208210f00e0303415001403c60301482400122004402030350078020031050419000c900c00b07 = true := by decide +kernel

theorem cover : BRFrame.Cov 953776978 953956834 := by
  have h0 := BRFrame.cov_init 953776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 953776978 ≤ n) (h2 : n < 953956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
