-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1736
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:29:13.658671+00:00
-- url     : https://prove2.me/submissions/7f8fa89b-4531-443d-97e4-dfd6c7739229

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 312050359 ≤ n < 312230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 312051609 1250 312050359 312050377
    0x60a061b080f1801090b0f090f03030408010f050c0a0801270f020403060e01110405040e1c0e0108090708060a050903090a0f051003290d0605040c03140a120f02071208 73
    0x803c0088800300c011508001c1a000b02c0c0c1c5601c0301040400d41041000000b010300341030103170884004020060000b4110303007165103d0300035651514500506501188240c1e540b0030b600d0007001c0d00f4820510001040d05805014441c4084000e00080b0140200300c82400c80c00d262219013840740c1071342640c41070b0207504148001c03120307a03082c0001181d2000045c01340e5041060001d90300c5040900d800e0400000d0000a6488034582c0104441007c000705c1000f0408903110480d29801e10080700c00c000140102c0780140504000c0d049001c00313000c0072801180182e0840e00780c1402040c2626807001030360944c41048001c03503008a080c0e80015068403e1042030084800c1100c000c4210a00c060059041e0381c80082130441c40c880090000c1c3d00091007206d401c0314004058440340c41072076140d42e0041115419a8103030f951101c0404208100103620400110109040c00a40707001c40c0b0a45c1e941c6803050b45804014240240e04802c0c5a420340308002c1600105903c58100c90404810706104582d90b00000c09 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 312052859 1250 312051609 312051637
    0x3091a1e0a020c060a0c0c050307060c080c04180c0509031603030306060e0105071209051905040f1119021f060e0c0906040b0a0203040e0108010e060105030105060a061b080f 76
    0x74000303140e40d2080d105000740803806460950b4400c0b29101c01032040031520400c1c40103000b68400450000c1015225a602ca1500042e0030300300c012004d407000070010600304050504100a0006a050890710342d41d245000b1340100b00401c0400d015201c6018100e0340035014403d007000000d101148801400449002703840c01c20071143c6801c402ca0b1802100e8602c2e07800300d10200900070001c2c4a001011400000b60310700038010703944503000100340c202d02d003030794590f682c40c915000c3c01540b409200d640410a40003c0400c00081c500060301c0340d5005c1c13154400000c050206e1610481c0703000740000c00d0102020502c03090144501d000f00c1c4014030090050b5200848400c00007100580990103c8160007401044107003040d103440c000c19090340c00b04104c03904602003480002000f089005805000e412180c0001c40d5440e82c85004030f2800405900142c0720382c3c1040c09110503902c0f1001c8400c00c3e2046840c0c00109034a00398400c03451a00e80b070380000c2c548603002903243d0188440743c0c0070700444c40d0f440310 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 312054109 1250 312052859 312052861
    0xf0603240a02091807270611070914070f0c11040209030c090118200f1308010515010f090b030c070203011407020c090f010f0b0a0e0a08010506010f0512060103091a1e 73
    0x4100414001c41444d00706d01c40c2c0c0340038414080c240c010140e1100c21301811048500d11038846425074103954004102ca41d80010301030030b11a800ba00302e9450100c900143c40d001060384c200f500e40c8054a50301842070b6000d150b00190b9040c16440906c0308080300d890190000003d565030300c1c00c80000b00081d05080010605d004582a03643c078081d4403691104071300c2c51056090542d58101c040c4070350302052804115003203130103000501c11f03401e008207031003401c64603500d6204c2c2201000140c4580c07100c1160000304074800c0002c0c03003100000029030750050b41c401125510b4003183d00c0401e0040c110010904d10080c2d1000c100b2071026030000710000c0400050f51110001d460310030518611b12070a0142c0d510384008080b080c00071181171405083d0003611071501d41c014416400110b12540900c0d0042c0050765102d0b020841c071541c003ca42000e03640f41d149020751509100828110307c0a001401c4d29040603200c801410034131690000c50010707804480c5442c0070b203040c100f07088401490305a0700780c090090150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 312055359 1250 312054109 312054137
    0x305070906230405060607050712170a0210020a030b030a06050a141501032d0c0e0307051c0501110d0903090603021602100216030303050f0603240a02091807 69
    0x40682d0b1070100d41000c07054110400042040b015020045c81607070020340500021002c05c130200608001002d103000001c121005a007040b6a194915042117001007401b004908901c90f8001032a948203c0039501c01a11408400310072009407206021030b507418400d1400301018801c01da40b142c2e00403d116a810081110003d01b0420f055208a615945d051210400c030409940039410088000c0c6076111040030300517800c0064080700090042c0c22280594480070144066000004e42c6030070102200106140344c50040060481c10301440143c00401540e10184d04020302508150340c000c200990f00ea44445500b5183c1000744045042900011009000026924041c0c03089444020700d400c0e820b101d00d4030640070b00ca442c00361501842d00b1849105c0c2c1c80f40380c0d40800f05801020758800e54001c603040c140711126500941c80502600d00c0703508084c10f401454240c90701c003d85030400c680e628150700da1b80c03881c41000a000d01c041700b580201d039803884402d40302404d45070f680c400c2a2545800c192400c0c11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 312056609 1250 312055359 312055379
    0x20a0207091a030613231606031e09081204050a03080c13090b0f1f02010501050f0a0620120705010c1d011b1e05060106030507050301090203090a020a0305070906 71
    0x580b48a41642240012410060350101d10000d01e038022000c1100c0201141d240301d10b00c00e030205500455810a541d40e03021703400740540c044006d1000d4a010f101c00402c4281040c0e1190652643c1d40301e66030380e44010410404000f05681010300070791060f841c5482c107401d1032911044036100c12070010709248005180c2c11448026600849168041d66070f070b1f5230828240070014103140189540c48002146020480c0c1c4d100d43e00500e031034601c1560070105641c1c0b8070000e4203444060704010310805180c1046999502d5030020b0404407400c07442c2034040112500501c98084800e00341984880c000d003158500404d000b07600401146205000030000030300031400445200c900701e1080f0940b21581034900c81d00350b200f0642c84103c0c0c02407032040d213803c00751961421507081e0040d0440c0700b003001d01c12440d0248902880224010309460505000c03d1a00c1c030340c0142107204c140a45044194003202003441110700f001220702c071980c00303013036005030131303142d09100f07649074003611130001114141240401c081c112 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 312057859 1250 312056609 312056651
    0x100c0f0215010608060d2103020d1a0603040602250b010609061b26030114090f040c030209071b050c03060919120c080a05090411161101050c01020a020709 68
    0x590f81d880096118030302040304202c50f00005407908654107101814511f5211040a040742c16a140141c0d1010b8100f50242600c054003c3c059000300903071000c5805d03860700c00c1141d40c800c0d17010000503568103064269850751a4004014902c1c4014131030820100602c00c2d800c2c80c1607034419151020610355581080728100d11142501c400112080d4010340003400c0d6841b0b81a41d01c003040c40b407d640c1d001d00702c1d148802e504241d0041e011342800e08042c8401e400d00605840e000703800c40300344155038905502c40f86400c0d0060f2000078083c5019100003012240314a2449201c05100014120b1150b014107000c0c0d40c076000721b540c6510a00803080400d009900000310305440740314074010303c09440036540b00d400d10041101e080e10240b0001111180c00103501e1002407495455544a1035100c2d0342c3d41086c072048036606401c85481c84003c2051031a1010b09040c6060103940c02103036040e601d410705004907a1800780c4411079003030303600104103003400c00c1e000304c0c106050f244440020026814000d420304d0316420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 312059109 1250 312057859 312057869
    0x60b0f01050d090314070c0509011d0112020a0302040203070f171311030102160c140105030f01050d14010e01060314072d030f2009010b0d020a02100c0f021501 70
    0x481001494442c4440b500107180850180c00d100d000c0c22074520003070066a000000854029074510f0080c0070380e1a21542e0140580049011148004040022100f145006018a840c1441c0d000504401c56440300f403c1b902855002c0c10654072401c1c07010018180511701c9100402185052040e07007104032803104064400c180e041c1941c0907403070181d11000c19401c0d1305e060041e01950200401500d0310304249004c44450721620340e0040640c034003000302e0f040f403400c015800d04004080081c0080b0b6824034071034905440382110f20514004e0f0310b10308000300340075043c1d10441c10750030010146402007040d0300040c12070b8060801c00c203440c0407464049131a07042034010603510301d010020307114940c1501070300c100002101c101d050355126241c0d150040e03441d8010004840c8070031038221a80303000701d01024003000321100740c0e00500f443d418a0071410072405180c040841c00f030781c0424040091031003040240490369000c08104014400c041e001440f100140c030031500944506019034035501880000035048030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 312060359 1250 312059109 312059117
    0x902161110021b04090804320f010809190b0901060503030928090908090f0d110f01030207081209060f010602070302010c0f061b0201150e15190b07060b0f01 69
    0x50560140384880c0011079045410550724120200007608203801840a018190305404404a100d42181c4288045500d41440000a4a8000596220396002c070040303c9c4e090074481c3c3d103961440846803819843c070517901c4000301480310b5a001d0214410105005142d660001e002540e12602030594a00c030b80c0c14075680202d1204a1480400410448034480060700c5460401990f6a00c2d03000080e9112510203507143e40b800030300014a031a051300c0c082e0802c0b000307844e2130080480c0342c2c58000541c03010b04051801070045840030b000076880707a41122234890b071101645445004070824004c0d82d40d001c42d4048403910810001c00c805610850341c1c0c0c1d040f00c1d400e500904029045900460382071010703d20807540c448030b007101074001818602441040d1f01740e0500f02d101c00d03800d50382d0090a4421b01c1c84124106407500c24180041c1104011040c1e2118603c016104420500c601099400003034454450601c07480100200710b0b440000001e01d10742d40613101c24440c000c22081009105998644494041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 312061609 1250 312060359 312060373
    0x24060a0e030c1509040e1f0606020105100501020d140d0c0908121c0c1b060b0a062a1106030c04030b0115080103110a081b010207080f0604030513090216111002 70
    0x2c2e1400b60024000081e0010680c1c0c03009510b22001c07030744610107e1a081d11581c4401d002e0000941c2403141c190302004940c1103043c0c00f480d110010b52940d448450590800a89143c56001c030f00900d800c56060303125402c0c04015a1085890050076030310b0744c2c0200d020354000d20544d00001214a000d5480900c01c0c100840103000b10416002c0c0100440300d100018098200c002c0000d2210000440400074091480881e10210890030020307202015006a0240304204085030282c0002c51454240f0700c00300c8049120175401810441102041d82c04010362050b0000208034040609030003078403c591041c44d4030384640c0d898100444290070302804280004e2001070041011400c00c404000b0440f0004c0d0a8842050f00c0b00303006814007009403080091241a104520410f50741080803c0c000e02c0500003501000d642d10780c040d51a6000500007508020021689580000ea5003801000400100100b150743d0209008590144541150181d0b0641c014440481e01d03401d10b0070000300003154660140c911 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 312062859 1250 312061609 312061627
    0x7210c050d03121503122d171030020d0807020a09020319150506030910020c010501170309012109080f0322030824060a0e030c15 57
    0x1000c49008400c0c2c08001c207603002a42640c0651003520080552046601107013421420410b4a02c001c00c0d1500c6c04000c084018001d0202170002c080c0c030328080c81c103c3d0042801000400701d8115801c100710045400c154814090803c1070044c0480445d2140ca101150915990b40d12810410f032911540000d00380c0454414010b1134081d511995007480b030810982001001e802003105000541c008141c0c2c01e60010078060384118003641400c109143c810140009040c072308007580346554078428540507010100102e62905810b0141e454000c130f20b200b0840d212208843e0841c081c0c0428071802d2200c0b40b000d8001e02c0040e00100031100c8410b01038680d207102034018401c0c0d841100c100141100c040f942e41c041503000940840051081440d0750440756120309082440c40d5295101d141100e102e01c0b0312a400000080e0410040790f805031394008100c008440c801030124100303450208003070f4031500001d40060001e401112403200103105400f260f8a0b401346c0340a0205440703c48030410082c940a0001400e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 312064109 1250 312062859 312062869
    0x60301060b0415050a2c0103111305090402040e2a0a0e060d03110a0f17031614070606150324051c05060705030a0b0a0605090108041a070207210c05 65
    0xa250a80c2c2c901072003038400221b100b03007400e40f03d040c000c01008a031441083c810b40c0d00d40a400202000da0404518150760410b00745e407034240600ca0507000d0004c040008003955940d6205070000404142035480303061002c1130b01c00d01c00000311688001514a1500001c1d2403c21024607801c5d00c0d030100302e11100761907400403c040c004140c0c40c200d042150000d030310100881c05000b0001241d120f008540104c1313a19143c0614200245800304680000030b00802480407070188103441008a02c1c1010800155281d01003002886049009402e440c01c1810004082d1291280301a1740140c96408100c4601c06414924911485e01c40068000113074200900c450b14003604803003107000d081c281c040d0400300f0b00d5031041e00380942155034002243c0d01108010400c2894040c401c2500c030115041c0c04c25074103041000d0814011400001d04001d00140010200b0a0503203600d00103844c0241200e12a180c05040203589007540e01840b400c0c842195191183c14031502c84ca07030785096129100e80149424403080c44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 312065359 1250 312064109 312064117
    0x90b0907030b0a0306110405010207122a091406010809010c1d1f050301050102070b040602070608090a061103070e150d09050709090f0605070806010e0f0105040504050f060301060b041505 82
    0x2948550482d00020024007140b02e441512a1021030035030b07c4a1400001a081003a6644012000e41d0843c1c1020000b030034502d0580100d052002c0d80c03c11141b80d8008100c41003803107400c201c80d070030b160250000260180642c1d0600c1044241c0c0c500c5055a150840d45090300c2c0034010100118100c80d0010080c540708201403142da40b0080c000200741400c05290008580c001e1940d1004140300000620080d40e041c030120020784186014145807a04d0054020740d1001d09114070740400801c0303001700314500000e1188000c0d041d0882810b1010305007003100030580342c1c826100d01000c20140100c01c110f50620744415910301031038075070860520541182500191008107421a00c50151030008501070801d032152002d07040c0a0f00b41c2c4012160359180c11f50031240040d004c103040c007041c00108061681d210041400307260b415103403008601c3ca40001070361140580e400007903116003000100440c92070300780e03212032007020210000c0c051b46685152540040c0b190b8005c482c114280d80615089040c0188014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 312066609 1250 312065359 312065381
    0x31e0c050d02030a0504140304141003090213060504060503070b040312021504030f0f0806030604030e03160e04050c09010605121e070809010e07060905091b070f0b01090b090703 78
    0x152404510200703580890384203c0e2494200c660761010f010600024032144803d11a0031402145000d00741004d51344081250300c01e49100e000c1c0720701c0e8000e04030310039004041401d40c0948010f101c2c03002201b02801a2119004660085160040006061400191100c02c0742d0000888510301400c51316810041111000204254070902281a10350005004254071807802a9100700340500148802080b0201c08080e1b00c0c10040360100f8402c440e0740220791150001e03032508040143e01c0b2840701103410800c4141c15403018900415000818000e04880c5902c10340c491400c0e00c0000d07040b60100500c8101c00e00900380080c009000c840d980a003030a206a401000c0019051041640980300300f10000c0c0c11a0003000103140f003003e1008001090040072005081c0030003804100381000f0f0018520700243c85818402d03141180846c1c2803a4504400c50f5000200400c816621032907410151411612100c00301e441c42400c400000e9921200d03c07500c00340d00001040d0100e43d44030450110080c1500300c0310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 312067859 1250 312066609 312066617
    0x60f0804081204142a0d060f0e0d090801050708011e0308030c07030f030b03060a2004060f08130201050d05070e0d0501150b043804080109060c031e0c 66
    0x2011240e8094040680300f41e00c9003100c0c10254030f04800d81070400d41c1c07424060005284100d103428801d40004044801071005503049900c4a150703080110203030032000b000c100c20a140582c4445210030100b070503d03141c012912112017856480069500321001260160f000907804401800608211900162000641100c0b20011501c0b6161861103030b000340c074013001d40000011100c0030160000d4414000c0c0c180f5040401007900c1311400700ba00e9000080c2408409591800180401d401e407031640501d00028880c4680c1701d540701c8001a2010310319001960200e143c0c40c0000c2c4040c0380c0c1c110284040380e8180d542900b8030912803080070140c40301810b04007d0000b1a5102c03c1c035921004080c0d66400c0c021400402c0400314400016050a003031b0300302c450014000c10060080340c0307149081e0810700c102101d4141300700c0141c89400101503680d10020b24000c5000a00103254030741500020310310740c01080c0400c401b10142400b5002c4940c4c0940c401c49004024150051941407580100c2029901c1c0c14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 312069109 1250 312067859 312067867
    0x70e0a051b040b030711010513020103020c01090515010302030601080d231606091e020303090f0a0f030303020d0c0507152021150a120206271009060f080408 69
    0x40070389280d0401e401c0010800d4001c070802a004c0c0c0d1150079100781d880080002c002e50b04001c0074802500e4051a0043d06068000442503481002503006000c02a0000b00f51140c220380d030b1088181c402d4007071100780e01c81c1c03246600100e042000490003c101150701e840704203030820050400e2881e6800442680507845040c424001d020030702040c0d4290003845142c3c00250301800b0b2a003250103400b0388240d03000520000c20981d0040e1400422070319840c0c8112203114100510600042800352942c11610f41c0d02c0c43c5030000400c158054000d0140c5044145040c0408881100110340c207015500c00035020402a060019400b2600e40c032000c540b00c800550481030980b0f2050b2054a5840040119180109010310071141584425000d41140b14101442c480c0c18a11000503600307003180c002d0001d4221080d0140c801c642c1c441088412009880651901011081544051036000e07030b544107010380d00d508c041c801341c0b07480703010a8415071701d4984905000040488084400e00b400170005c03101050200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 312070359 1250 312069109 312069151
    0xc0f06020706052a09062502030d0f0e01081306020a1205010602030706060b12010b0a020106080a0605070e031501060e030708120c070e01030807082101080601050a08070e0a05 77
    0x10103000e00c1881240c0e0003110f819044101c4ca03491040d81c0b0120100c2d08010301c540e0f48243d075600300326240941c1c600c042003440a0381c0d9000400302c0302d9081009506114600e480f03240c594100760740e844640883d40700e01120b81c41100054500003404c4032400c0c03404214896400019080e031340500070601c524a041084c81c060640c00d1412540280c001c0c00c05a0b0022a0500400605001300c40c06000d40c142e2003418242c4140d0340380580c03c010300459021a00200c1c202509030f100350300080041228a080b10f4402d5040d09019004160640d1402d001904281040c4058200020320f409082a00581183c3d6a031a001c0d04456801400c00d9041c0e02d8040c960300010780f040c0820a5400c0100f0181e5032a81c0c0b0702201010ba41b038941c0719441580d04000100040010907032a505840b50940c101c28081d5031070440321500c0d409081c410080315004140400080f82d480000100c0f5416504184c0c0c00914003502e4001c03055859580e0b00c103c0c11001d649100045903440302c1e8000b00c2c3c200114144081d50381080f4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 312071609 1250 312070359 312070361
    0x606030a0b09010324020903030405060918070306090e030a0c030e04140103050d090e19050a0605130b15090307051509032b090305250b0d0f0507020d0c0f06020706 72
    0x1ea20685895070800c00c40031020780c42000010001e45e07800c0741149420044000f003a140c1c0200d218070361181e100451200d40984807c00d2080303840d82d54040e050901c1c6030480c0b02a009002c0d50040360304030751402c0361005205e2000000c071381d0629071540342c1c4a01c2105641d012141ca1484000554000b03454412003444030800c1003e4901940c441e5000d0800b4052155004007030050590084a0041c07803071080c0104c00800034000c0b0300000d03002401048075a103000b4070760090100b50f40034581101490045ca40810713202d030b01c18060071300125000c40c900c1d9084900712525005003800150b06400411003000a40b034003030140f29a0443c0400d2150500902d1000039081001241101c000020300b1000d54654107000c0d000076005000700e09040151754195102e650795110381c1c024a0914071915040555040301c889483c200400c0302620040e545c0304071401160241004035500801380d03040501003100c60340080b91103050181a13a6940c2800116a26044c121254000c803d0351400da080000f24041915 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 312072859 1250 312071609 312071611
    0xf0d1514040203012403140319020307030306081b0607020a05041401030308010b0703081501111204030618081204080f0301120b07020a1104110d0e2b05030606030a0b09 74
    0x10256800400d07240500616003510341c890030030040011494400030300c0c40400030b4683c1c10349803c020060080c5442460091a6211b2004d9001c4220360446c2c900358800e60000c01499400d22a5409001c0569a0320340903544400360025100c1120a01403110781c0c50400201400501d40024900c0c00020307030350b038049022a0722018820032001c03a990014014103401511545c010443c041c503962400d4006d8500170620b13500501400074100225001c4049a03220b1800390307040c1589802075810005080b00c204078240e000d40f100b120400e003800000100c0b04d09003a108950b80703411540c8149880b64605003d0100361005004444140041c888108001000e0015501030318920b031202c070f01811903042c206410700c03004040d0300444d8807086c3e04000040c5200000340c8490710507207000c141e0302540f1450804c113028030f400003d0010701d0440e8010303510900080303148540c81a070070200000640c1c08018840c02410141e40c42c0403130b504001003089801c16030011a0f00804860b000141c90305458000703108610 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 312074109 1250 312072859 312072881
    0xf1a0118030b010906051002030901020d0309050a02030d020d0f0e0d0605070c0602030405010203070e030102130510090803030411041b02031e040b16110f0f0f01020708070b03240f0d15 81
    0x2644420a011b681440ea10380300200c4401e000071404e06202c100003d60310307a0000d04100805854040100800108010149040380d00800b0f55911101400e0020b60741c0d65201440c1d800100604c0030b000c1c0090141c6465645240040d0104841030a05c2d160034010b01000703881002000300400304030005c00d402c0c0c8055401a0310400000d03940b03042821b802000340f02002d0b440d520070391042001d030300d8110508464000f00c40040c0c1301c0109207203a17000c00396500540341c1c0c0070940e140000802c00003040000d110364030411104031403c01c512042d1064100b441001c0795654005648204600e0341201e02461448050b62a401d400340e2a00740c55440705900307504010205441604040e100c40e0801110302d01840c42c0c19026600c04000800100001d000c07007000801d524040c4076151382c82015a40b080c03101e803026010030790403141c1103a41da91180305240d0088980d03c1c040c86400c000007415411048000003c0c22000b0b00711486115810b0400050600e4030108580e440b421202000e541c58480c014000703400c07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 312075359 1250 312074109 312074111
    0x11030d021e0301080c180c09040b0103020c01020a020102120705070c030605100f082a03030406050705011112071205010b0d0f090c090603020f04020309070e04050304030209010314010f1a0118030b0109 88
    0x50b0610003400b0410500c000c6c0c1140d102210410480b21a80701016202d4032402200c001c1100c0c000180140c000784100f4081d240f1550002a013441074580540040800c0a14100300c120282c0d80c1c0f090845190180c040f0091000801d0310041020500d9504016080315201d0240c1c80303450380c0d480e14442c4809081e40300b02c420350855420030103400c00c1c0c2c18800d941da50101e030625504407a400c0000b5160302c0307140200d80621401042d802e052003025400401e10140303004003541c0ea800c602602d40000c980c12684e06000515211040060700418044ca40c121080102c1c041d0809545055000c00360050385800c2d548aa0741d40e1400021902d8018000000c0004203000102c0d80d0960043c403100b403070058600c502440c01002403010048000803844212100080070714600c1d1070300e00d4028114404c3c0d50003c5d520040c03103000030061080401c4042c108031000030003000480c50b5500c510064400740882e45540145000c0040e450f075015090041c4041c0319000e0398450381e900c079501c0305104c810a8010311011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 312076609 1250 312075359 312075373
    0x7020c06190305090115051306050604080a050d020a020d02100c02100e12030405090a1d0f010f0f0c0206010b0901050c011409010e070b03130f020d030810050111030d021e030108 78
    0x1d80c0512030190803d10400007401010040040c49060360389512803a0b00980b0309a0044400c881c0f40c2d4402170240a00410055540d40e4440100d60355604850098400b401010703008000d41e800000c5890180e07a002d4000f4440040680070400b030040c08a5210051040241c003400045c0d4800c00070170b110b0041c6840c6c00411082e19070602900e00c040c62038100d2660b00c03c02c0107224a55510644a074801c01800d400701e6a406410070b02503811801220700481131049504031a15240103400c205041400c0d00d60421916090f00d603140140c40c80080c500d00980c000d1001030090752000b500600c1e00740b0060400720300e09a00c0d50020340c00c480302c045158081c0d1840790188031403013400b8011202c0e0401c00074010f00026003010190001884003900110180c08000e40302001c000e60000e40c0e0f542c1c5500100701c00001e503860b09000e03041c10700850705200302c1d1400304404115907029100140300300080000443c10b0090b201c5000000358003650070061560031002c0b00d80e5118950000442c0601000000341003a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 312077859 1250 312076609 312076657
    0xc06070f03110c030d0b061608180f0906010c021f08040b060a230a1505030403091a0706050903040906060f080709060c060207020a0308030a06050a17120307020c06 72
    0x440d0300d03220303490085000c1082541c0c0b1809001082c0d40024805e001c000498161200c005142440f0b400304243c405c103100c01d0740344244030156015241403050603103021f242d40200030801100c101903400c0203504c1140b500116525500c074025480034180f003e001c107035050040300403c05071031003d0210317880010f4005c004c004c104400002180e80113042a66000c44490410803103da02e03054851400d8108010785854003003940d40c8000e60390040c910303040b850524000904005003a94070844042d808200e002200003000e007101d00c242810034499180b00f5042c48640e9859002510307018040756054401408007003513107041441404010507581d11a00700729a001800038103a94030051865050041e0401c2c2008040d410a03290341c2100c3d442400141d40e60102d100041c00c050b010f07000680304071008000c00002203000c1e4842001e917181154120074050307030350310107180420841c80c640d40d1079000000c0030203050030010050354200100d80156007180003038001054154214014142c1108070f4556040700c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 312079109 1250 312077859 312077861
    0x51501080327060910050708040e0f1b0a0e1201060803040e1608060105031f08010b1c05030a0c260702040b03060615031906141503010f0b030c0c06070f03 68
    0x71101c0141507403010002c12110009610f80180070760a80540e1104010302861403144007110700860b0300000058407107403140c2c4110a60384048551048688030070012410f500c40320015203840030829440c16140146801007140d903000b25a0100e50000400c98000400040a0242401804002004542b591301d003c808004481028081007100a401c501c120540780e401003c20741d12803020300b0300704d6071b03034483e00c1d00c01c00b000ba00381c00c000203150b02007000461844419080002c0c0f01c101120000081e030085109510108040704004141c0c2d401040030b081000d001d4040c86070500d01900541418150614101c0b4010f11194203180404000088240441ca030034420a0016182030380200340c0e5242c41c90109102042c0c0c0302c0d17443d0400401000080c00444456000744c0c0380c9110300340510040d999610140f01c05444181040e200f40e0320001006401840038080d00e04882c41c2c076041d9035083e8501080e00c000d0b6440640300a0031541c0801c103a580c680303010004c01d40a004682d8400710f100792341c154020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 312080359 1250 312079109 312079147
    0xa09110c10051b070c090b010e0904060c080709060215100503060906010306060b0405012c030d08040c08062802040504060308090910060c060515091305060c030105060a03090515010803 81
    0x103c840c0092140a0100b241030007504152802250002240f030f02440050f00c080c2110300f45503900c07034034560412080082c0345d000030804046030307220755016444108060b500454503001e4400140e02030040e41c014828030060f0030b0341001035942482140f17510340000c681004000c40e11103080d98060300040080002c0351151900510f00340c00c1840c20079040070300007010340c0b030a2524454040e07a00601c1e508018245840804804030040031141c0318030400782c010b01401070880341910f124001850010711401c010600324824400002c107462492020381481c54006100340d250150254203010106c4c0c0c6441d640306050280d03006004d21500c625003401004041003004000004666a2140410000d0342214640390103c2e88200c000c03c00f035542d5051100b210751042507103035000c4100001d014802e58444881c0d4000341c01032064407075641c1c9a0003581107901c820b104250304090100807095515109a00c1103490b603100d10700b0384e025109100c2450000000030703000b888140d040001c0c3c8550172165444c40c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 312081609 1250 312080359 312080401
    0xb1801020909131a150f060301080a02060a03271209030510020705100f0c0810050102070303031d060a02180405010f0306050910110703031103060a09110c1005 70
    0x35071809414401007000036401602140019505100c1142001402e01450075a5000454010140d141c120002800d4000202c510760040c1c115840a010a003000e80449050303c002000500706520300750700344004c41c2d101500540c01c00d13507100301c4408401d8810710104110036461030814520703041420002d030448040080001070041c150020170024a01191056402c1800e0750f0060300c81c00c0c903040c220308050b40049464246894000b6903c81c44010f64400e02d4000655940d40f0203d541c3c00710300f41c081c0c440c64050180580d02101d010000a80701c5c0e00174101050900d86448c050803c030b901d0140c0340c02402e441c120b440c1c540210390750f1110f0a01c140145440c0c0012501030005500d49107816003102100e0102038061903d0b04005000f00e0801c0040140001200c0000c1044000f0030703c910340e0b903800508080340080d040ca45824041d01c00902078034000d0600400740031a02c0d00d040b14402c0188001540702005038000d011100c0446014408400000602c02001c2803501d0000080f2580f480c1d00300071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 312082859 1250 312081609 312081611
    0x307050c10091101031b05090a09180b090a030804122a0b0901060e0103080d09020910050307050906030c09150604090e01050a0c090e0403030f05041b0e07121808070b1801 75
    0x20b0016101b10413202030030f602c640c20401e98426090000c07036a400c0c2d80e03810010f105818200710440030400290b80c515000d005030045816924bc4180c140e0b2225800d03071000d00041c4d03400c00400d000c42d0141c40006064049420000403215010030010810600001d90703034000c4030411054010b008041900303d60003030040008025040c105100e0010702d400600000e0310986021401d0041841b01d40d201036802c940041110b0502d24102088501c0404c1034040c0b01d0107401400c8000811382007640f445401844000d014000b40c0090380b09000c50b1800007030082c081304030341d010030300c400d911650b00070000f4001c051030118024001e40d104a080d81e20240c058019985040f0f0310a440603802440380d8265605040750a0b40d5403220b0404401801803da0300c0504185844140820007010681c20001200d6004031a0700c5665900d143d107078405001c0f02c10101051a280d803880a0b003c0c00e501010400d800b00c1403c4c8215a0f01d503ca0624503088400304070b880581c4001409601009043c02c0c0d1071030045a40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 312084109 1250 312082859 312082871
    0xb12090102190804050a080408060403120c0503070302070f12030f060f14120102091f021606140708070f03020304031b0b1b0a02030a030305071b05060c0307050c1009110103 76
    0x1d0a003102c90358000051041141031004602080018004141c102c0d8004401c50388403a01d03448207503200c01b010b0301d00300c02260410010030b50000301c038003c11781c1640c01ca0f1605070a554984505030080e61200c4000c17a0f841015010ac980040e411054003c560010781d900090310150700c3d810141100e1098002808803500c203902001010b071019405440a107069502c0030240441515040c0640541c45000e94010700200440080380005a500c244a406640c2114042581000c280884011f14001c69001441d00d034804013800d007505008042c2c60340302c0c00b155481c224098880c1c03400e181c2070343c02c2100180c10002e000c105003c0e0f011120507200544105d90a00d80b8501280b0300003c1c03050050010603440c460941c9190100103008a03a02184c000d42074814030034892400800604049030310300d020405c12141c103620034600d500b030228000c1c2d0250080110740c6a000382c1c0034552300014080380400c101000350140300c88040c841e00c40c41094103880881d500c800d524207403102c84000d0055a04041c9410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 312085359 1250 312084109 312084127
    0x90504020901090c09031403090a3f06021201051807020c0103050403260a0f062102030727061a07060b0109090234120f180b12090102 59
    0x314000b41102e800c0c4a002925042210042e600204142d00103841c040c50786040420a0501000070a58210100d03400560130303803184141c0031142e541030001c8610880165541120014560340401d1200e40030081c0700072401169544800c0e43e00c403026000400c00c00700010845428040d503070030b554408070f04411801c3c0c80e2404000713540e00b5045c40d080d4101034941c1e01250030315011306217001e21103185414007401c00c644112000701001c01654211410781c64404500500302d00d078401c610581c3c08480240c41540c060700d43d000300b080442d80c4140c2c1d25000301180040c0d01d1030101c402c400c03450100100202c9000c0e100054004450743c3d58010440810151500100d40411100304d500f0581d0107540020601e5803000101d40003130142d0041c1e05c0e0355100180303104140c0300c001083d0785049040c50b407500e4805c24100240659101c2910001e01c9103040d22110400140625886083c004481c5004800d090481052320308642d40360b0700005002000244280d05210442c005503880040c1c04001d501d400005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 312086609 1250 312085359 312085369
    0xc0201060b0313020a0e0108030a0f18290a18060507020f040203090109060c2f070e0a0e100e0114040b010b0d020705010608011b020609120703231309050402 69
    0x14900740c00300ca4442105011550f1720004c42d00509006e08041101d5a1900c488a5490b84078140042c085466000740c00c400034071402510315401110030314048120300e01103a00041030141980040000441040d4400d002801c5025040e00100c0340d03560045090004400c55610140d90041010413800300040c902503107580b115140c03140000d8400680d80d03610803009a00500e6204001032080f800c020101105a50000c0105039001c00c00307014500d10312454503508a105c0ea5040d408a09402a01e42001501d203009082980420100e00102d020200c00d40c010b410070700d00f440204071490b40c03809585c0c1498400d21900700c49080d405940703850703814140c0300d810303103460144562141c001c0001007017090311807a9019174428a0303014009116103516806400c2c0a1701e58030210310004803035100f030010361510028406010701e4000380900700000000900c41c4141d44481019820310130660304451800b0780e5413400c400382d0b40b20812043c1d01c03280c4002c2c10b103111803e25803001c15006d0400d010310001d6952 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 312087859 1250 312086609 312086611
    0x90b03010b0c0f010c030b0f01033e1611010e0d020f0402040f2603070305041a090904060c09050a03050601090504061d150f1e040203100c02030405040c0201060b03 72
    0x1e21144585400c0c000d80d401e031030303d0450000341c101c075400d09086056094240c1c101d540604002c03102c1024031a446001141101c0e01a01c11181e0f9a16808814070790820205c4001c80342103220b07080d42d400200d00c802501c2c59134450000440c0804072000c4004c1072021401400380090401d02c1c203040000030303c5001641079250184040d12504a030000c80340d4035501d960455005068a0078580d01030380d44d80c0403030031021071015040e5600d80c1001103042e54040d0084111516207902d070300c0301800c0600f0000305481c4a8140f8030401d03240c260800118280c0d07a0f070b071010340d03100702c0c880e4130702003507102840c40001e101c0130381603020078000c0302d84040500c002880441d1060548074038a80009540d40e82e0b04098010700801414405d42c85207031050040c40000209001c11103c000800742c1140c0c3e295080001c2c0c407140b048a0b54403000b003002d1a4052503248090801d0b07040785c00201160054440500d05d1011111071101c10800b5a2001804012500309401401201801400200b00c110300d006030407038680c88 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 312089109 1250 312087859 312087869
    0x908030910031b030b04060902030f010902160206120a0b0f0604170a020a0612110910031a0913140607050910051c020304150905101517030301030b07090b0301 70
    0xc44100411001480b03580528911565040040c1c00c0345050350010300180b81c04041c581c000c0d81480130205881d206402203a01a028000009007680c1c81c003c0004000e422900c8640c000407030702c40d40138005d6984c440182844a0b002e02070681141000340c4044201e0b030106a200307001f1010780e41b07000c0325a074074401524115400c8102031106c4080c1d110303596080c0360450340c0081d84100700d9000891069841416441d007003c0000c0d08003c0e007600d22003148150300500070310560100340620500703d20352003904600b681685c0591840c800c2c01c140300000d590f254080b039121603020003001007081032004101100c000b046440000c3c10b09030820000c002e203180320b0046c04070300034403004101c0c0c404103105a0480714680798104440000c580c8640156000e51b00c141da0942e262007035410754106a003424816a06010342c448010220f8a628400300005082542455000b440c69000001208440000c100031225100000fa50352581107192424140102500c00c1c0204204030390103120a40e1408100ca0541e5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 312090359 1250 312089109 312089119
    0x14090a08031501020715020102030907080f030d020931200702040e0a060903170601050901090e07050c010509030c0f2e1d07031e0305032a03010e07020d09080309 71
    0x1c0050b90040c0e1034003c032a4011707501d1125107025041000da065000c0c42c01040041c06945016541e00c034601e13a98080c0140080254004000300303032031004030f580205104400074025407880c0300d0521050896500204285580402000c3e00c1103e1007240d200d0351a889811801c030300300e030003081a02c00610b8000c0c024000c0c000c0d580c0d008443c415a1042001c1c0c40f202d5401001808003500b280780050940d03140b02411100c0c600050045070446d0300801c261741c0c140b04183c0d00c150000740741c035a0390041c6110150484090000c00c1140721203000003800380754801c44d0303e4001036a6500c1d0b0780c1985460020000b960100f5500400c6240301c20b6407070804000e440d6060300710340c0354040c442d61701440000c0c0a18a070003c0d9000f410349030311401180108140e821a4090305100341001e45031a9540c0c0410b05a4800800080d004c00000301074145801014040fa890344c019055480e002c0c49a20449600a8010a41e0384201000700304c511a81003040101440d554070f0080911894010002d50340d000e6604214494 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 312091609 1250 312090359 312090391
    0x2a0302070f0605121b0a02070815013804091506030203060d06050403031d010b01080906100e09070e041b0801020403020d03050715110c0f0c0d03050a0e0a060314090a0803 75
    0x8403030412000300b4043c0f0305c8051155038500e85d0001a40c1c4040600c03a008160003a80849030b902080028164100c0301c00368400b40f000802003a5a165017102d1200e40d490040d258407510400d01b2184000c0c00150510150000c0c808031400240e20016102d0341c0810300305030040040240b9901c8504c0801400b550240d404141911180790075805002b8824180c3e001ca01209184158028150030864010101303882da6202a00c070149200c0c1c44a81c12101702600801c00b0341e040010381c2111000c00e1340110780c0415070340700740d03103448100300d0038030066400707894503e19004c10f01600609195600010410700d402140380a01d1a8003045800000071300286c1407020110703541042c02199406c0c503040c0c0c550b07200c081110000780780454103150441f848070f10790391291002400940100103028151580028130303070b440c102d4036950220f80320f91007030b0341000802c007206410010a8490f50540750242c41c1d1500d0225034400002010503640100030402c403402c0c0d00c40e60405e4041000c81c001c80c0d410020746880c00c409 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 312092859 1250 312091609 312091621
    0x6081509071a04090f09080a0e0a050303040303052503020a02040b041d011e0203040c1a040b0301060e04180b04080d02120f04032601060f2a0302070f060512 69
    0x14041103a00025194208840c2c0003030880720b52000300165440724208021075a480f4030340340d003250981403008003191003c01040da055401407a407207102c648001c00c00f850035601e880c046030440c1c11590045002c110007048030140040305280344090b0b501c001500d955500019240203544010074074010740130781c2d80c07001500041d881e140c0202d64200b000c60f12000c0e165010069245c001c103a072082c50038803002a070b606207140b80a94000c682c001c40d0004110a030160070600d0760403c0610440066459050401c80001c41c106860042c5000b0030b41c0c0c0d15800955030902c4180003d0383c14601603084079408900c041800954162415900701e500411010b4542c0300c00143c0c44020320820710b0000380420200e04010031a001c946615100d1880703a510200c4424144a81e004010062101d00c41300640c1d92005011161040c540050025080e14100300314056076090310040392110340381c0802107200080000240f44c0c04001d940001c1c180400b18040041c500352005102e80200006030818840740804941 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 312094109 1250 312092859 312092863
    0x20a0618021009050301050c1606020c160905071e050d050403050c0f0307020f06040518060a030f05150709080d050c030c0102030c12090a03080a0902010201090503040810050a06081509 81
    0x4050790250402003121040702d00941482014030400340700391308000015503505503039400c0d14014400b101c4600300c1c00b9860ba2314400a508415800f403078a1181101d02d500808140701c080005101d48040003c41d030401e604020f00c00e00c00d1540d140c0c2801c946104011180350301400b01d40b550b4452450005441c2c46070b24003203429200f044100695845130038048070f08108003100030807106200300d43d202040381c3c0d00e1003440740f140514802ca42e40201d030451220302040b81c00d0301c0b1952100f0000c088003541070701c03659400e2101a03011400d80c2d680d0b02c2061408602895150143e401c04100d003000c3c1c801c1880c0050450307844100040000402c900404c41201c01c0908100340d8421141900c0259141d01c0d0100e04143d1903009120b140c07032800480e0300401c00a280202e2002c02154042d960034407103649807036182001e4006400228110740d6200307000320105d001400038001900c10380c00030740b0507145400100000e460000d0039001c40300386024420416030800013a451001c02a1562018644e9102d43c4418 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 312095359 1250 312094109 312094151
    0x304030c021807110105100303020a020d0305090402070804150201090c1a070507240e2d180604061a030604150b0d060905010b0310030b060301020c1e0c0102030a020a06 74
    0x15808807050000d0180f02504203410180c000c0f4402d000b0032255a407400940080941ca00c0080c1c0583c11400011000d400d02d0b0050154141c003c0c11b02d20f103060805400300d4100c0e800500d0507241d42001060510995070345500001904100748028400e000e05615440b540b1a02c0c2e114094461900040c03000b0b091240d10251680e1236000360a0b561010358a8000b01c0c10701e0b803141043d00c0c070701c05d02c1401480200c2c01444440c0e00090301030000070800341c155a407651080d01501168612240100c520035455441031200710000da080c100a600340d04001c41888240d96868001c8040300724808080785032801c003141666408003080310040703a081040000f5580d1003805400400113100c0019031001506610340150703007154140e00017080142c0e687c1900040c107000542e030640314a102e0003010004100c811440b241c110078020001850600c904440c5441e01042c42e00c1201d00d4072541245d04400304080c802c20f04521030a0000d18a0000650b10081d140c11031103c0042a8694a61200700c40144507012a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 312096609 1250 312095359 312095389
    0x1020c0301060801090209060901030803011a0d020a12050c1213030c02090c070302210d1e060f050a0b0f0a03020307090f17060a1e0902060d051f0504050c0304030c02 73
    0x800a0b60b8503410658080c0490040590241c00c2d12000f18000d8104000580e040729000080a421030b420001312500e00601d05840c42c0c4415014000031044440510040c00702c0552034035008517900e001d100350b90507204010000100d2110501c1004008140706060662001d000c4102c0b8a03010901e14094030711840602c4040c3d00000746000300030403600940c00070800c1500a800b12880c60090350305030000381803114081034403c0014002807003400c580e500804100606400300707124050781012020f0480e00c480d0b00070649020072480030451420040c2c0803002524818441620702404a07924042e64490030700700d0f0080640c00030026920521804c00f4038007418241504188948d0b4541c1078811000a440503048603024000101c1e81e00c1c4030301d200d401646110000003070313607062000e444100188019002a40c100508005440f4414458030449114110380c05c0c0c0e10840c60159500050b1000040d00600c0c000c62900003030002c00b0311180260307030f445585403030002c01c03403070051000c02c1d0300078400100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 312097859 1250 312096609 312096611
    0x5150d05040c090b09060d0b07030f0e0a020a080105010f0612200c060f010f05040903020322060f05070201080c03190c05030105010f0203040f0b090d0f0f021008040b0c0901020c0301 80
    0x148070811507403004200481d111100c00b40f2480c070488003003048034101510310645c03107140102620000b03485c008541d03500135418100020030300641541802a1000e0104449164100301c441c101189071015410025152850003005030b076040c170b2103440703140703c20740900300c240002c4125102c42c4072000d81086201c0c01c62755000001200481c5141142604407135550921805880005180c8980c0d04c0381480c1240c400c80c00345c090a07031404080c8401401107080030390860004000305030a10800c680c0e02020065190700c007580591800100405203049010f641c030400404100c0c0e02c02503a0310640b00da40056402c00c81e541c0d01e8942001c0e1098000743e0f80d0f05400702078241081e825105401030080d41c121002038a4000c4080300000003280c5034860741c000e810f00d0082d111828814088250003030503032508040c00d05403804040b03440d40e4102000d0032104592441c3c41303031040300031400c0001018805004605140d219402d0a9503100c000c0c1c400100b95417020f8001080041c5640e10070002400c1d54180500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 312099109 1250 312097859 312097861
    0x122d150504030815030a03050c01241509080606221d010e010b060f070203010908040f080c01031803080c1b0708060c0708040303081306020a0305240a05150d05 70
    0x1502101400044a05a02044103400010002400708011010108005000e002c0580c055034050ba1160040030b80caa1540d0740c0c8592552011300000113000e440c540810a9142441c901000e006c45204a0700c401c0040000f984020004003500007030310703a0408800c940c07025642883d44421008801c200c26211a010304186040141d000091090038074101030303c00034400c044181c541e003400d031030170b5100d4550060750400c100801c00b102c04014042480c070040001c9011f101d035480b91400c540103074211108070b0307006901c1080081c0b400c00c000f010b08078082c00c0c140046000d070240b80036a108203440180620548500140307003000d216048440390140381c0718500f25076448840d00d5640310280e01a01e981d038401c400124060350f0440d0150350169a100d41300764901801c5a40c210b50f0b0480140080131890444101a13000078001d0002e0007620341b440d0f40001303a9281c803c3c28041101061220007850412502014429445000001c01581c5040c2e030000326282c258262117150f403140200d1f0b6844a0f00d040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 312100359 1250 312099109 312099143
    0xa030f020406110d110a020d0f0605090f07060c030c06091a0a0b331b0105070c0203010b0109050a260d0302360d061404050d0207122d 59
    0xa0070403d0341d5210004c641c2c100d14849400d41d000110443c2a511a5028041000041c0740c80b0f0010925a4032402da48002c6ca5902e6603030030f0680d407056420b14503a803c800003042007144200200c400820151900e1158440141c8001e04410000040035103101e89400c0c3d41c10500c60340240798103456000b49090041403609080140051640d44003683c441c51190b00403140f008440480b080701100b00c04400c0000080385101c0824aa20401003007281c1c80c400b0500b112444000c0c4910f40c032448040c0c0314008091a83e20406003100d1440488074148503504100380800d0301d510180b201030710910300e000483e20a41102e148880e0b180c041e8403030f815100e071009010000c3d42c980c020300004040200c41e030491440801c000c1c0c5050030214010002c0d00d8800075064080c2c0f03420800444014050200060702071444481e900c44124101c1b016900c5d940419800b016540d0b04000031002400d04081d28100103406030b4a10703a8210348a9003070071941407108424000e02a21003460501030b540062860070f01c040cd0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 312101609 1250 312100359 312100367
    0x604080901090915090905100504150506060304110918061003060621080d0b0d060c0806040e0601151e0e0102100225080d0e010203040b0a061a0a030f020406 69
    0x2000e00c40d80000c1c990384000500360040d000380d071030b4070404c0d400c0c40c4101405c10942070000c155400741640c00380315607541c080c820354031407103068051406610041920324031040110196140604400d0184000300104804902c807208881501030742152504000d4540c1d40c11800300060040304e0a5150143c181440901c0680a40e000206c0344104003d108099807100c912007080a03401000f034102020103e0600007805080c020a404c3c44212000030740300000380042243d10741003007812140075980e2503042d40a59007050cc016031007402210184106003120606d01e859640600ca0901000103c002c0c41540a010b0314218050304200d000fa019090340000008242040364403210340075003d0f213545c07140c0f1048907000316110220031402101881004421100c100659820140c545030740500c00300c5a0b01400740901e40c42040b4801c005600c3c0c0c01c1900f40940e404c0800f81c809980945000d00412000c04a28012841c1b07000d031908103500d421075480103030081d00c1341c0c2480c49042c51000401044803500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 312102859 1250 312101609 312101617
    0x20c0d0c0507050906090705030703060f14120606010c060207080904150e0705072102010e10090b0c0304050a3c150509060a0f1d0a1707030e0904080903060408 70
    0x1641c121042c0c0d40c2d0350800d2180c084002d4070b4868100a01d0300005206a014200440d0801007500e8005100f6940750f8050120405d00c1d002403690b6212180e11220602c0d01643c0102040941005000c40b810010f0000e00750440010b002484550085500002c0c080c07800151449880d000d4030034855802c58961501c030071043c81c00340c9030100307900390085a40d16103d0000d840301e050b400448a40d90740c0c14190301c0340a40c1c4024074100c0440d902e0707401449080c10b050001a20140d43c0b841d01090b0601280b8009024483c014851441c081040c410000415000a80c2ca98140c0d08144006803000310203e0207188209a401c440a010b50130b4031301040000300811611105900a000344210101035410301d43c15030704181d8241a03194086070100d81c030076002d513100514910820000240c20010519502442101a041089960811309002090201c04601003004040d480e007005d11705090303941c001e41000030325000c0c180070b407601e000090300f0441450b040392504007004040320303c91714040c40c0803451a44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 312104109 1250 312102859 312102863
    0xa0f02300108010b010e01030e16030b07020c1f050703020a1a041505060a140126010f0b0a080118090f051c03020406020601181e0c140408150901020c0d0c 68
    0x344540006070182040c49031200a0794143c2d55003400c6c0002400444c090b04c01c0490703500760303401840c03c81310340c100f10907050100071442003003096024641050003904003035004542c0ca010b007250400c18500105189100310750300f8200d0034240d444206d5410101d2504211480c000e0078803049840039448000d540503420b100754880c4042e0b000030310504100c4e07c00d8406c203580582d0401c510a0b010b218004070020f005003025010b140c00a40070a2500e4041078080c2003103c003a0303441d2007500041c880740082c880c5800c00703440041041464200c481c48002c064280510030b40e0044420108074090800392908030f01039243d0080e544060b03500d0542042d640301c81c55041d103a540e1412041c0d50300102c5000380265000c5554503000340045070303e4038885c0c81181c0e220303aa8021010383d89204552030369015185c0c8074220b842c040400181200f501034041c00d441003104501c04501d070b00344001c02c001140020340e211500501d038031544554a4131758041c1c0c06030182e000007540718000c030610700c40011b0380180e045503070704c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 312105359 1250 312104109 312104197
    0xa06060e060f06030a090512161a0103020109030b1005060a0503060901060e130504110405010f03050f060f13030e03010c020a0b01090504050a230601060906021c05030a0f02 76
    0x61a12020030881851242c01d1940000c014000980b2554465200100c3e260241c4143ca81d000707601c41e082a00c03640003101040410140c40030481c02d10114420001c010040ba00c018800d55043d41c0000e40301e04018070006156491200015000302c0140b0a50303c02002c2c0600256140c010070100070f030442d04102c41c19030090841d000001084c81c03080b40c0e1000540e00c080c1c1745031074007040c8100b003502a0800030720a070381401c103d69140344a9113ba110303184c020541c1c1014408d43c1400c628143e03042c003100364500c8072036a214000303002e1842040c0d0503040d0000d8000090503641d00c0240342c2518441c0c200d0140175415441c0c5210301c4807154021440100310b0740705010812990381c841c2c030804201c800507140036026034080c4200c240001c880d64000c07401104400940004000e20091061502001f60406800211002005c01031990104800c0d006881c1168021001c0188a54000d20900000b09000380094035a07001c0030851807294125421541e000304a400d486801501d1384940030200018541d400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 312106609 1250 312105359 312105361
    0x1b0b0c0f010501061e09050a0e0f01060512070f12060e0115050c210d022a01050402180606221a03011d060a05060d0902030d0918021b0a06060e 63
    0xd18810710403241600c88a032250740a80d0441c00e2500c2c0c00040c0b500303601742804a400404216a6504402d55004010703000c0d500d20300340350138588041c051006910003000e00405000c060b141408510701c240e480b13150b41c40c4c5003d05035580001150900d0801a003400d416140c100040390300760000c0b110a05840c1d03840e148050f1890561381c21203141c401c2c2d4501c140aa084951040c50307103c2800450001442040356440c1010242c0303407841c0403030384a407031b00300d40d60210580c2d940c007400c00070310040700415500703002000b20b4502500400e411840b00803e58143c140b42c840040e2080e9141c6040e18950003100184030300400031003521104030407080c000c0e0041800710801c1c2c0d803111002d21003100d05940c841918002c0d150b004040d107000300304002e09841d900a2810314086550307120710011707103053700d034807140822a001d03d0300515040c40e007007140c80740401c440e00303009010484058424002c200d0007500f0060343d40016030112100d510007000468001d001c1c2c18441c07801e0106a4124900303849001c8410307241 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 312107859 1250 312106609 312106633
    0x1c1e05040b1b07051213030c080105100b0702091602120c0c0f090103031709010908070f06060f05030a14240f15010f050c07030c09140105030109050312041b0b0c 71
    0x490198100052945e4803a00740c030141a01c04030098101c00c000c1038010b013416520381d40d511092032404e4000f903883d42e64440412000034590b4044500500d083c06415107000c40c1070300440c4c0400700041031400643e200080740c0f005a0f100b045404041540c01404940f9424900303a25a1103480d140a2a0310401400c80c130304a461074070001050480b507040e100c3e4070f013558029041c1040500300803d0070502d95038500c40c40d4003141d100c2000780350382481496840702112180c507021013100c0483e0055100001d200c0b17400d02254400094901c6030a401141826030b03014504440c07854400900e85142c4084d280e0103a07201c101c4450544035009240b41c0521010035524008550070300f0070000f040d640003403880e1007074001c1c450050008000c903008580c10344d00d541d5203a031180c0d10328124550000d07180390b0359501d40c2c07030700c2410040c4024050300c0204e0003030000c5d14254407419920b01502d40040000350031480400e0410902100d03420401e016410440303c1710b95140c0c962815031700900001e00680c0969090162 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 312109109 1250 312107859 312107911
    0x16121505060a1e05030a12020d022e0f090b060306090609120306121203150904050a020f061b0d081e01090507030f020705010c020d051c1e05040b 64
    0xc07090380d01030864060185001c04568032058400006420708403848000720712a1000d115034541940221508100204a100000d03d4450000500c0045400503d01c0700752034085942400402d01620303040e06040000114a0030041000c52031a103541c40c6410a1a4104240100658403514044040d140a66a150b00e8962549001ca402c0c0b01c15030000081c82107030380e200e02c024680000001d8006910800a8140180361101841480100000100400050101452240001240c256038541c01401c0944d40c0c00e54030300b09814003c1c403d44840908841396101c1200383e0341d29003c40088043d81d0082b442000780c855200b0b8039454005040318000869205030700c4200d200c4210303c440e00641036840c15000900800000c0c18260070180c640105881e12030403400604000c1d40500000640030035940000787c42c10200801c140c06020b0140030510303602814401c1c00c0c1445040c40404250100c04071000400d00400d000344001c0580341500b0310003440415003589200c0d50142c40c00d070a160003c00f43c282 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 312110359 1250 312109109 312109111
    0x40605060f030f04080d09050703050c0a031505090a08031303080615031f17161a0301060e01170c07120503190b04060803070807060f020304020a03021216121505 71
    0x7560400c1c080002c07900002ca60310040ea0700501070300c400ba041c441d000030218250b8048000565840e40038000038414004180030401c01e5210490fa4040c1761480c5503150140380ca0482c0d19400034543d10307000120707885024080040020351004100d590307071510700360f0b9071885c1000200550000740c0c002c00045050074503004103101428541015030850351286007040103180d07600c074102c18a5818141c00141c907106480300016069021002e004030644001011081c6186ea07030141d680343c4c4002c40c46d00825600401141d065a1540c548140b85800c0c01d0010389100403030843c43c040072049041000700241c0c08074041c0000b240300e40140f24140c40007007022103580c041038444603904142d0111400690803076034803000c0707030747d40c0030b00040350840d5100324032803e540124205455410300000c2c000c08100013813003000060700c3c00200c11411802e180e0027142d07168825000090003600104001d2402e0f443c20010244644401c10483c3c1c805521844c00000082e10302004a40201c2290111049260580109 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 312111609 1250 312110359 312110377
    0x50607030b03160b1b0d02010204030b10051516080f0406180f060e120a030804030912080426060703064214030702070e01170d0503060a050a080a0204060506 69
    0x44030010300348200c0000313941c01424000741c400c0d840c51140d00b130407409000340c0c44c0811032900016103841c51030622a1218400502090052010074410b120940e20300410094240c03c9015058031100c6c40c5140700c48041030300e40050f002c0200410b03044501e480342030040094032880c2e52504041c86040f492504284058007440c1c0f5410740b40c005c10f1000f10301c81d4400181480d8018403003a01034080c80f5501e42003c0c20401d06078001007068042109058000010100400442828082443e03041e11060254052409080250340305501e02c0402c40c1803817142404000b00c4a8261440da007024880a0018801d07407042c0c10b4028810500150300e9514111041c4161b103400c4c107024940381c80e4078403910001224113003840500054031220200d000031030024600c030300701a40040090b64200303000d0011101050340300b110b99201daa00740c3e140503000414203510400c0d040c1001d60300c0f51240c1001030800385d11904060b40003481c1d82000140420300240341d010260090310100040b030b80394024044148550b0802c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 312112859 1250 312111609 312111643
    0x30315150711270a05070c02040203010b0d060503070e040303020703090510080702010f0c0e040e03130303051c05060d02010804030905190e0112051c02010f090b07080115090905100909050607030b03 87
    0x20500e0481e5002507901c9451482c0c906001e46c401c0e40001c0803132f0400c1c0c0000d800340b203010a01900140c1c5900c0740401600d411030061211900c0c0031207441c40e0f02d0005100404064000c141441014000d85800000d8080241a03807503418024a008100d1141203810500660030541c03000c03581350141c071468054200c01da40f100045044030301840007500c40b441500300170f48002c0041c2118650150301c0344000e1486561015a180e072b9510304100d81025060750f07506841c0c545014031107039540b41700840034455421b0070b100e04156198201aa064025030b4407403038104180600d100d82d03c559041000701134554031500315040e40d884500c041f2104d03c4204004000768004002c3e031080d02c600c40f071040d010480520002c40c0c031140b20311620069079911042103c0b91160340040c404503d4001d10128007402451440032108000400c008261408034410705500030307521004200302496000180c400b51444410034000040903150142e641e404c2150b81e540024a004007001c920724021510400c20300d41068 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 312114109 1250 312112859 312112861
    0x414220209150a0e19170604030f0f0c060b040609020a0c03180b0a050c0304090606090501021b01080c0711060c03130605070302030a27180f050903031515071127 71
    0x8140184c54401720140c4625203100030b40020040c128140d018011070f00716014050714203040ca401f0307004001d84680003042c1300501303c4900040754007104500030755420842c0801d81501e01000321b0300404980e049801901c0c00040c00000c05900540700c1c4005a10903a180000d122403d00400d22000150081e070368401030410400c1541d61064014090390742d90741b42076a15040d80d40383d03c4030440d00d56a0040000c541d611804200719030f014030142c0084031a00c1001c003004560340b4002800c0c202d001700420b400c01808580d4030306000c0d02c16115490541c000e030581d60381e10068201ea075a00d401c60302c140e0740503440e102c002040b02032080050301e40b010342c150010760074030074200c106aa0043d0540658000b800d100c6d00d040c911500824143c400800018141d03120341303441c54145001b1741d10100d034050511030400307080c0305948100104803580702034506460201e01d0391060020310b1100d08500c00001511007c600c460511455400200b11040c048546401e0744040900c2e050107140615100d10f00135651034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 312115359 1250 312114109 312114137
    0x90209120109020d2307080a02040e0f0a02011103071509061104080a083001150c05100b0a0b0c07050901050d03020c010f0e270601140414220209150a 66
    0x1a8400805e10b035240d0b400c1140d0b0380d90055080ca84101980441c8640d4000d00310f140640c142031142e103441018610142540e2805484600c0e0f03103807041d40d8000d041003524104041c0080c02070050301c030310540c0000348035480c02c1c0450851000d4540d104060f10030a01d0400049158030440080749c080300ca414018040145150b00c681e080340e04403801001404030307000001201d0754150542d1310360b240142d9401c0c0b6581e5050080c4146203224605481d4248454495244081034000491640d1110031140110f1460b61042c04145e104825602c8a800c040b004600c014402d1000b16103070041c1e400503074008166a82e21402c014a000140c0c1003d0056001010080d8195202d12040644035485040104080344100082642c0f480040e500101d80d0b40010149080000c0014005402c5402441c03c050b080360042e0190340700340b0961282811405200c2c17582d084684507040310461030a0408810040e00c0b0601038018065408014480d20408500c4c000f102c0410074141507a1513020181d942c2090883c00c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 312116609 1250 312115359 312115373
    0x41e0f03230a02040e030a0305060915040e010e06040302070305010c0221031b0a0f170f071211070b0403020115140d0204020d0903030b03060c192106090209120109020d 74
    0x19070440c5040e4052a2800405619a4001c409104a085009603560880500c2c018100d401c081c218034450000801030003481d8411581007500b00008071000160104403421480c010801030240b01c04600800c0200401d044c0c0201c1c03240c08581c00f0710020300001c415240c00700d86a0100b69041c0e12095103200c1441500002180610340c0500700c10a418604107810306c000340d298101300c01e41070005014201906030345600964004a01803005150085d90034054281310b9505001881e81c0204407100710300302e0000d9000d8000144100c15024499904c4005050400c03082000322003c0c2c1c090360800c5100c21401c0301c01900b0303c0844220000c0300d0440c400420070040d031000c0e00e80b005d80e40150207100d031003c031a1480c0f14000f005403094800181d0380880030241402c001004000074901c42c0140030100080c9858681a08143c88034540501c00407045003c0c100200c074441042c900f003629203240440c8000030f56000f080f4890048411004100341d0f0b86000d8240d07040c0346002900407801d01003000002c1c000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 312117859 1250 312116609 312116663
    0x705190302090d0c17010c021209010e1c0f0606050f01140307171303031808090904140a030923010203090d020105070807060609050a05060d030f090902041e0f03 71
    0x4001c02d68000055252101c4c240c04060342c0040b100104410080d03641003109100d030350650001400a810381d00c0309490541114003456070003905000d4400e40584243d90340401680740c61a4502510b004007105080045096607441c80032607126107054400701d080c0c50b1240341aa44040160750700f00b503001035080703218840d41001e00560240080d602e56081804104e08805109030301009000c0d0718440f4500b402402d54441c5040d0003042481d0780c070182d010400f030404031280e0102c2074401c86400d858501d0014200881c1d2040030310640114a411000c01d90301968507000c488920400c1d10080c1007002180751000890000130380580e00c00c10850300c0c541800721540c06c078503005042450410b5502c5e02c5001180e80071074011a075095031480148100900b07072041c150403c203105410400da00c0c200c80814540c0344080d0303000c3c0030300607502c804003090380c802c0414038082c05c0c5d000015502e5540e902040820348240c01001e00a0b00c003000710100c1ca2101c0006058203c036008002d4041242c2d00484441065007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 312119109 1250 312117859 312117877
    0x30b0f2110180c0504060302090f041110020105090c061c0b120d0c03030507210506030a0606060f02070b0c030f0a050d0c0e1801060e060a0c140609060705190302 71
    0x40c5440c404103041640c42004500701c0b0b0341006041c200b80341d01d44000e40c030380c03160032440c451303442c01e079050000d6107400710120703801207203690400415203403400c0101d41c682d0381d50007550f800000c09054003842903040d00f0a501401d144000c0342c3c0b0500b28442000303514084c00b020802410381805000c941103101c4d4000032800e07000608490300c406a0540020304000f8003230700b08401300300e5480800041543c14410030380d02c0b03043ca02e420384959202e54418030f0034810782c405000150380c9500c003044655805101028081e60b000408204082c1c3d54500906a00d0308613a400000d130140600026555180c607003210149641341002e1842e101e00028013505030380104128104004d020702c503ca4401203e407050304444809a120303202d1100082081019620503100c50385030100303041d401040840d0f0440c0c0c2040c00d8606c22900346c4e4940c0103c800031642c0c0751030700b01c000c0c00003075466905120041002c034510740181c010030b0940c1d01c80d07030341d5181c152110310881901c10040b085032180c5d011414800e034050502c01c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 312120359 1250 312119109 312119113
    0x70e0c0918010602030f090f06040801090c08010b06070f020f041a1507050a02010f0c15060f0801140106030c0309020d060b0102010506031b0904020d05101a010903030903020d140303130201030b0f21 87
    0x1802d0174009c01c110fa001a0010300160b0f541e119040c05020007108141c004103c01d00091282a00c0580406c0c03081c02890310081a40c240d02c02560304542c1c2e5010801886031000e8400c000701086014051110340410b16482d0107031130b401d0b003011003040d0b000040b6110142c108000b0840400c1d160f00445919070003200c2c813410491508180d80000d0301000c02c0c810825044240490310608100318045c1204141e80401ca05a00d40024a0500c407011402d05046a1003420300080d0500303460001d401500003000002d61009400250100700b001d5584900c0c440320702079008110964070303901410303504c96151071650540d030203a0450014901c0c04021301580300e44040e2030020322a03242d0303807040d103001040e19940412a40b80c520303207092061003000e280d08410091a0030000d040c0385403400fa150500d2404068003c900d8000c40d5002d2103440e4003561540444501140e50703130b1038581280b060440c41264100c0c0000d003030200260291a14100c0c170402c034400200484005201c59a0b490310b42041024414014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 312121609 1250 312120359 312120379
    0x20a0308030901020417010603051615030b1c03021005010905091c2c01021015121407181a0901170106091a040e01020c0a0f05070e0c0918010602030f09 67
    0x540c0c0301b000c1c15240c4550074000450402e046180040c1030820130320807103585c212440310400080400300452a100140d604000426095141c0450216402580c007045044681000501056030014402149510039001000380c2d90f2103000f010180c2d8010303205440c00340d11200c0c00c0c040703d04003020300307000200341810a201d000710b20048284800300c540350200c990003c9050030a403596014000ea400c0d07041c6054080108544125010140064601034101007081d141011800c21100d1590070141c040c545c41255240e9603200301d206990611642c000030424204504c0308440701c0c403544001c0340f20400030050f107641c0e03080242800b5181203c01140c0e00564031148001040000d070b1003201a4842c500d8084080e00c0c41020612098a02d946090152a072041010042c958004610142c0241d03100385407040440c51030a0140c54001141c1204016515501c140b0070410881030003841401410782e10b119804203050b22408a40c0001d200c0d55016030410440c000e94103104800a0001e500014035600071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 312122859 1250 312121609 312121619
    0x201060509040605010302040b0d020307090b010e06030c0c1c0507030c0f1a1608040b0c2107020106050f030c010c031215150219050307060f060806070921020a03080309010204 77
    0x3649a00b62401e4a01075500c2005000703608240c09441724850b800d8502c21402c1c0b0165021a0303660030107110350350846036942c40042d416031194141518408000346602d450b410f04210300b41d0141e0100107859480c0c4102c01c0034000320702d80e01420003170040c1c403a200c50b4200000786d14240d0f002d00d100c02044801075190320848002a9921200c10301d2401000000c040718070344404801c40d42144103d664051047c10010000040c00384551190300c0b04c90500d20b2500c812540145683c41450310322441602c54420082001c01541503003e441120340440e494900c2466503418140c9601c56052080e000a04980040c00842d01960030452540981c600010b0000c00f84110fa075500403a50304201040070111321000c0700c0503030401c419030071302010043c4a504201c413036460301d41d20311072520010013140d15400b55100d50301032540072030014102981650bc0743c0c6040a402060b50445000e00c294280320420712100308540c070703170191181c01c0d8040d101005850940d03d03102038a80004004031030640d001c01020030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 312124109 1250 312122859 312122869
    0x7030c2c0a0b0d05061311190c0b010806160f12050705160b340c06020403020a030515011703040b0d1b090e010b1206010e040e0303130309080307111002010605 70
    0x4a0011045001981d0b040a204000b000b800c05910425400c7c02c0140500314115076400304e82121005004a14480d10b01d83c0e0142e41c0d9100e002005000000c0903400007a0034200402e589115440c808421075a40c0d800075000d40e804000c03204104001043c44a241160524542c0419040211420b209050107c0f042e00e80c44101101704003290410b50030b00074843c4548000c0003400d03c00d2070051402c3c13442d41071100200145510b0a0224040100c41d4070481c0c01e001c4541c2c11034001c1d40d009051041d010380c403420100d42c8c0b40000501c0f04607007075003800002001185c0701407807044882a04040c0d07141c640b81c0520350b04c0a412041040d01c0b0fa0741d4490700ca0b200140a19045050007046445034090030f4513007414110f02050580c02a4130943d410000241030500c50b41c6507580c0b04109007072800300002c84402060003440010034456040c030000041c4103d507040c1a241810161195440f45140c0c0e8980302c0f46516070241101c0140400381030a2188007a28101522641000940c400003846a40d5000020703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 312125359 1250 312124109 312124117
    0xa030e0d080a18151e110a0c06060e070806032505130e010f05010f08030a090501050c0a0b25021501090903140a03020414040207020a1a0c120307030c2c0a0b 69
    0x130115581c58850a518104032030a490805000c0d01c020810054203104160b600e2082c00301540070008042000c0707041040c60703842040178214030703076106550f0f10305420040c00582d002c0c6d815501c01c0c4034450401132450801b00740000300c074080c440015502e46c9003a05020032000c10400c0c20303e0345512400f60359071000c8240318011805660305030206040d45007086007288004c6941100c01c07a0b03042081444042500809501f04072502841e0855864401500340ca090040c1007000606141d074890511041071074060309400355400d0106030605620030000c081e0b980300040310039050300314902c1004005c0b41e500d90380038862142c001d0400b108440741402c484100365000c031030004046503003c00d0600205d2002c9102000c10748040d5000c518104164002030090000d40c410000300540395551100c0303401d03281050360309001c0c0da0070448510040d003584003492504201e800310700091901110300742061061100c03840305d001c01e40c444c081c810100d00f0382c010228816115513401516405001a000804500070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 312126609 1250 312125359 312125393
    0xc020307061416090819110405071215140d05010b030f070e0121120509060d0906050903160f0c0f08011a0102070501020d0c0203100207080a030e0d080a18 68
    0x120b0464a040741031440362240ca02c1c8114100056194284041203000a00300b01030266207411220818080c43c00c1410004050b00715500a410801401005a0000181000c0c0f448034401809542c0380260001d0702031026200c0c0e80c102401a22003d866402e14061a8001e2405140041b0308200f00da030110b443c001c0d004017140d009074000c0c4000c000f0480740100150240840c400b02c668550b1514030780300071040f41c02102038010303844500c000b09100e00450071a0064200270b09030a407107210b1421514001c01204100b0317121503003070800040029101004482d114441140340700002482030712410f5040d5041e00007100d1112080380c0204500ca600050f000003001402c0001c1210b01040d4204150351142a106034195817014205020607a00401c1c440c3c441c800350b14007685050b0032400028500701c81000050341907440003c1c1002880810300061100c11010344040c09940344080800f0fa0b64a09944008000ba068601040842035650460400e0800400301e0003001e902e95290108150030340120 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 312127859 1250 312126609 312126641
    0x15120f0804080d08070215070e010903050106080a0201030e010605150f090406090c0e010801060207061119050a0c060804021305070c050d0e01031103060a0e090f0f011413050a060c02030706 83
    0x240f0f003121580f0446191340300d1410301c05003003036400d9982804403000b8064071510511100e89190150750b40b28940354001150000c0080c06199515001984c54450703045041c0d00080c200703114001e6014050103072030121040600303629500500341c2d10548442d00202501e00192030204140e2800360b54070701400b80644441c4c0e1002643d18820807002c0e0502030030b07040007410702690354010400d140d004982c00c4111207085c2014042000d40344055401c0c85c004244020f040e0080744031050500800089042d500e62044900c601c182d915484292080481110001d5008041305c039450110400d98008980004080c00d0403607120840c0c2d607401741450140e8082100203a2002d55100c1d07250381c14080c551011102d02011403442c14001c0104075040c4503070203060f000d13502110102e80c2c9610100841d01c80c221501003a1007020050740d0520b4003074404c090309040c41d4000ca402181c0c4c03c290703001180c52101e50080013844030440702e40d100405000a10b14110550009011003004110300d40a20307560903144072a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 312129109 1250 312127859 312127873
    0x310020403080301240e0f0a332307080d05041506050a0803030f0603070f030311061b1b0106090921050f030f1009021c0f15120f080408 60
    0x20482445100d07545a0007030141d02844514a2941251140001250a032456184001d0071f40c04140c000500f0b0340114100003840d24441690110784502401c4041005074207103400c0b030442c504940e40c07001c0303151410400e000103a80740384e01c2c803031038000300a42449404030074101030030b6410101c100c3d14200d40540340082110072500410400740704440180104a92b4800d0700c1d82011412662030000600480015001d0004255156020010600186004031085d20042c0d20b0b0300e0018135095580700001528410400810100c82882103e0307460040400305507400c0c41030802c841172840301e44800d0140030755a521000300b480c1500780101c80c0028001c41300008441ca60505507541880f01d09041c608100051008001404a841c1240d40141585c0400030054980c1c50038110560007a9100f0b1440c1480010b0f602d110170505900c2c80015142558204005803420350110180c40e2043c85850701044e240805001c02601002d0444c8810b018824201c0c6290180d81c941291f036016400c030a44070ba1205c0c1c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 312130359 1250 312129109 312129119
    0xb0f100e032b030b0303161e060207080d050a060b07200319020108060a21110402130e0f0f0c130503161a191110090303060617150f0310020403080301 66
    0xc004e006001d0400c3e00110318215003441e01c00300e15a0b134110010300d00040c0007092940d0030040c100220160360417000440d950344903450004000e038044440d01c06400d08200001d0000c01c4244122822150814611403802c3c0195030b41015605401c0a8082c1c041c540d165044100c0c2c41c00c001858840c440e0a00c0720024040e01e00015100c03040040c00c49105a20540080c4811620641e010805461408080309407030720501c0d006184500f005038460300729102059401c0380140744e1070b01c0700c21104244004040c035160303041c00740301540c0e0460300001003810020218146038104001818155a10702c10803003601d231202c0029082024102940401105103030080c0103503c0014481206401c2d000112407600d0740d42e42c8000390000540c4001c1c028821500604100005c050003000e01e0051840c5040108420501d000b0703004020500807000041d800564501c0024041440d007401090136441c204070540b452010000d950001110860301400798076180014040e0300d0002c3c00c090346c416500981c0320760410f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 312131609 1250 312130359 312130361
    0x12040b0603120301051003090503120f1006030c080408160b090d090602030c0c1014030a1505010c0f0f050708030c0606030d0306030218040201050405060a02030403060b0f100e032b03 80
    0x419040c0002d0030204010000c69550503c11079101d00309042c04606421141810b170300314040c11505240014103402000184882c1403030303051140c1062a0202c003910f881d0001101108d41408030301002c00d103040c02141c0400c80c200f01a000724449011444049070003a40e54050b400c10075a00d8182c0c0354003485418140e03540141404010301001d100850a01502842103a520101c6013101d5000f80082d200404009114200800c2c0041700000c5141e074130308064130f50030001c003502c0c2551410501000c6c5d01069941c45010a4084281c001c2d00c40b084602d0141c990050102680b0000c442c140304448001034903002c00c0c406400001c010700301a082c0d81c1750070403e150800c003820380141c08051501c3e605200580d02c550400b0615034070302c800f001c0309554904c01a09c079803183d030b0807480e4421000314028040300e038004024415240f023110700b8051910b4a1042c0800c501c064013403650302c0150300081c00e94084c4607481d086102d0000408035244440712540b028610150410301c44000754000b00d08807030701505 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 312132859 1250 312131609 312131623
    0x23105090c12120c0102040905011205010501050102010c120209210307051501050a0303050903011508010207111c0b0415090308091504080a0c020a050402030901140a060305030909040812040b0603 86
    0x10680d0b0050148a1500d50103840c0c1e00c4100d10001c0700d010219880c07111060035415600a0014107104011f19610385155112840d0181821551503003081e001042c954418040c045000d01682c43d01e4100350078004080b4065042032400b250080c481e01000c111800c078503c00728090700741c2a0065030317881480c1d040c518142680201c4181b10171485600400c102c5d110f0412130800c49401d07140c41515030304010002070242c481d0326070f04440c0c0350340c113200850000010340c014400c0500c13844409028210807010710007600000345441001c4105060f615002c60303005001c4940c007910038148110010024000b4404503159480198000b98051082200304001040b240e50b941c0c1e84100d400504d0314156462003128401d00b2902c004109515580e43d0031502c4022171f44019140041040d9164507103012624028414950204c6000c0b40300030101d102000144640016203801c6005035161400d410180800c01a0160080351540c0b03080000142400c101d0b10428040c03803044848111b030303050600070103203030044c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 312134109 1250 312132859 312132883
    0x708011e0b011b030807020f0109020a09021303150c08010b07050a0210050903010204140f060a08040204020304170c060417090109030b100f0f150809060402310509 72
    0x89444044055015003880d840080c12503010041440d00180d001290200c4202081071282030000d61290105a08044018490b400d140e086801d04111841c41c0c6087e503280420194124800d0101444400741c250001e00280c0034001c0350740d030440e9072a920040441a0580b0b0340014640c0e8452100c43d540d48441d0050040029254050410007103860305600c1d1034034003c00134422400341544000e861b000b03100350798800800800842d01c884d92005080701c101d40403170000b44150445442000ea0b0702d804004c0d51400045039540a80e26512582400020345c0050029241c1c011b40840005100c51020024a400c8c180c02024080300d0419203071071055035100c400f155455803030074041079200b82d0f03221807001b044030b82080b010a816110703021000040c0c0c034a034000000d40300b41140041001c140d10307100602201c00c40d4800f20b640506016084600000645900c036080e04020003007400b504e4140e00300e8030002e0f42c0e003815400002051405000d1900100d0b451042070740c490007000076440040c0802c2200803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 312135359 1250 312134109 312134111
    0x181b060906080f06120d030b120a0b0130030507020f1c08031b0304050a030e042703090e0702010f050f040201020d0f0903060c120c02120913020702060d06030203070801 74
    0x103401c200700941604002042d85100c1000603001403c0f6546130700c03500941c4002501641c400c400121802000b609002401d00d000c4e2841e051031410442e070002c3c8000c500754004200d00a540d00340710080c91407800c4008042030003124144080e0300d20ba00d81c0c0d103100d4828480e03102e4980c1c0b072a0b5407050120041d1111040c901c02c58502a10006d6040c00c003404010301e40e03000420540d40d65402c164281580244080b081c0c01400c0032041108101c80013038400301e801c0c0240c6035901c45a44200800c000d0b141d2a40b002d800c404c490704000c40c00148500ca5401d0321b18481d003488a00340761500d03801c00190b00c00b2240a80144c0d1910b0760309210a007203119240e041007030920050350501d400d0b000030b0b40d140b508400000401200b42c00ca2040356214801440c043c540c00700041c071a58400307000040040000d50401308030545010b559072840ca00014001d0604203103040b00c2030030190301e00200509040322400c0030300c085408008070030041e030340c0e60f00606404a210300700056041c11401414031300541a0803010f0b8507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 312136609 1250 312135359 312135377
    0x30c0e01020d05041401050d05151206060f0d0203030d0f021306021605090709090204030803040b070201090f0305090303040e0a02190c08030609040816060f0c090e01050d06181b06 79
    0x398481c0803113054640c1d0b83d16000c0461100d500482d568070500650141607854501400003407008000000300e015000ca40e42e0400400404440c5d8a80300f069691642c0b1251603e109071142c10802d2400c041c00b40020156410702401080c403a0688402520400b1281e90020f202040b10000d2242c3c04054866031000b017009280540901c960f00b205809002d210700403c074001042580f1451403000603014181701551141d07581d00d401060b503001075508544245c03020300025500f40c41403140991450300f201d2003c0c40700070540c40903a139580c080044160580400c21010584485000328240504040b050040c0c2d208030700301003a0042006001c4460400c02c00340314050200314200244c2e908484201c5681c00581c50300d15010b8046e1003180401e040700171845030503d003440219400f150b0102d001c1c1e0300c280422205424121002200d034081d031603481004d207005100c1424280c0c982c80407548180400620060036051200d00459010003c8a0049000d1036048201400c045034200070440390a0000d070b1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 312137859 1250 312136609 312136633
    0x9060604051f1701110a050a031a0306070c0302010e030c06090c060c0d1d13050f0a05060a030605100e0907031407050a05040c030f0c0302090a080318101e030c0e0102 73
    0x58000a1007090001c0c1440a42c41d90315110170340c84208000304ca8004950b540d1811480030344182c00c40d801703800110386400c6000e040e40d00d8000903003050000040c040e1901d03035180d0505450390305040ca016030440d07580c0d268002c00b004003040205500c44070f503002484585400f40404d450030001210003402040203002140d0300c04170019000300b908110b1304180c40030a00d601c0c903c900380b0348109001503120503d40305241d00c1d21078030741c03149000d592010100b034150b6803643c0101d8161042a600c1c0c81c1c101a1600b400c00114140f6802070b41c11066092110084994072800c542c0d040b2070a96200c82c140d04010420410050340841d070241c00c00d04800903004107803902d40060136540a902c0303060300690f00c4514202c0440d110f0703881403c0040e14035000f00309030040140b00400941004401c54059041010040381d40400042500d242140c00c40150b6024012641481010030725000d910741800b20035031640c0c0c010310b1400700103d00700c00745540003d031a240c9180700030014181c803e285c905640019602c3e00c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 312139109 1250 312137859 312137911
    0x1203020312090c180f10030c0b0a0c0203060c041503090b010e0a020d060b0a110f030906070816150b0d0525050910080705100c1104140906060405 64
    0x80c15081400c00c0c01c0c1640e1401c2565062400795055264050094101049042d44404205008002200c010701745030b541c3d05401100807a2a00001c0c0466020344000c0000c0e101103c000c01c0b220111380703032246c0c5000c802d5000c645810026200c04031050070200d404d008000c407603000e1034508401e520b400d118403c1507403185102420180150004d42d5500740004108600700e8048900004070144100302142c1c1d211a001c1d2503400c240c0ba980c3c0010f030f040ca10703014006070020717801c01d6290826028619040030300b003c10419611101c02103a120109000301c00303000c10541200705085006d02c1030280840d030485000c4089603540c038030640c49030180341120360100340f000601c0240c1050041900160091003107081401d80c8030343d407080d94050031030820801d07400615021002180d1258049920007503c480c02c0001080804480e20002090881d003200801e0380810300036024280940005120314400d00c00c03007021781c001c5611190700d034042c82c00e002850800744251507100c1c0703000d41c01b84000e80c45032110324 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 312140359 1250 312139109 312139117
    0xf0c070602090105091201090323040909031b08030106120912030b0301150f081002040503030a05090406150507020f2b1403070302060f0705030411060315060309150112030203 77
    0x180c5480e601050a180c580d0082040b00d19450006040c419101c1000d0440b030702900321294128001403041064003050891020b808080303100d1402e00d01e00745428040e4080003001c42401c00d0b400c20845902041040159105102c0880d005043c019a84d60601d600a003400704d038800003600103480c213240c07000071940c24510b070000000245404100100e0450000b40900003403040d0345421a42100c000400d03440400a403030444030060141c0354846080e1030564128081c91041c90b8050700100714804d14548a0001440e565200900015213180c807090041481d00f8040b103400d020440005000080d07141100c0260034600b021614200303204508504011301c2d0007103140d1814950f180d04c5c0c92808101c100031101880503d240e0849443d029035040c000c1d5900d106994078002d0211460103e1400380c401e808580c422904041080d035240301180906c4200d50000308220078030f030700070b043c690701e9983e44200442c018041b40006100060020600d2600c25806900c0740c440110300c580070400083d000b105807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 312141609 1250 312140359 312140363
    0x130816031e06020307030e010b0423070309170c0c10020318040e0a0506060907020d080f18070f080115030c170f0a0605010608060603190513061a010201050f0c07 71
    0x4070701c4101c50845500c0d076800042800070a030394000b00800c40030f15415444910201c17502d03002400b001005d20b0600c0f080701d00003a5550b50704081420208480c0d2908503040b50440403510b40042c074052305031580b03220741407101406003004c0c00002b03040480110411030501503107130444041e0071000035400c001c0d541e071040c8511401d40c0c00d483e0f5000480c565031940f124120003001c40589010741c80ca864001d40350402200c419102d20f45d800b02090555100103146094011581c94580f0651905046210460b6004002c05242c60300d0383c40150140000348107020050203402680ca2009091200c00b07425500d04440540c1188a2040200042038003212039104641d42c41e08440610200d08481d98140740081445e07a0482c49018080300401910340d002034103e50749a1340744540b603107454040280a100984180144070034896011250841c10f42c41a50012040e01d0700805402c07003a6111810350b290a818071810b80d500c030340908250358080c055154020702040c411840c40c03800d1841182e003400f9100b00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 312142859 1250 312141609 312141623
    0xb150a09050415050d0503041d040b27011a090108210f19050d0b10211b0801080f19260313060f15060c02190b13081603 53
    0x20712403074620f0110888050080501110000705a90402996070b61091007000c20140707640c1d80c2c0402c0201c110303000780c0c0603581c010350404141c0c45104222050910400e1b410a5400e102851256210402d20606c61420305041c4407241c0d00b4417903810032944540c164400c0340f003074010400381d4411200e840b0082d0000e19051030301c140c45500c0d444016209015011950214501d080d030048040d90300314000e850741080d0008103220445039282400b0500404035841e00109039506250200003007640641024414110000074039202c00480b000c008200d250b4a0304049285100180900320003480f0740142d11407000003d003a40303854084c0000340c00c0580800035090005182038400c4288020205029901d0f40c80303038042d100e040c406244182c0e18075007141155071500d40b40851440c02c1041c001c42c5000002c0a2000340382c5840d100051b42c0d03030448135000b26031004900c41c00c8d107248017402219102501c1c00790b184c2501d8100304001d50a9603e80f60f0032000d4140d101400d0003d15980c2000c98000356580011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 312144109 1250 312142859 312142871
    0x1030518070e040602190809010608070608070e12010216061503380a0b01020c010801050a140f0d03020a1e08030403200a0602190e0303030a110d0501090b150a090504 73
    0x92540c004e014480c1e080c0302d0034000301e0003894002c0e0710168886c02380c69400f00801019a41e00c01687d504c2070240700c0e2a0205d6281030008680600030003000806a5002c3d0146000008210616003260b102c00603800700c04030b402c11071200303006039442104c150500d041c00d04100c1038103540360560660703034921487c1460400e10f80345000c00c52007a102d420a500e1004942d080d9402c0c1103c07000d014004800c1c0745401031140d1402544190700c00c0d40590f049502c0a0310301072117981013000641c54100e40890403500701c009401d40070b02c41e8640c42e0101524600030350240030030b110b951904850003180c010b60404541c444e2841d2070080340f0340c4d4044035007050303050814051100301146111902203010284080900038840c500003801015001414000c0b281c48004681849c20030301030325142c60001d402601a401440044e41940c100e501c4240d1007d900b6141c5070400681c03005000641d02c1c00d07000116225103a0207050f0785800c0014017940205e49594411382481e1440c0e50090008900b44a42c1d4440c5171204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 312145359 1250 312144109 312144113
    0xe06060a09080f03030106032403030e010302070f08070203161a070f2102060a0618020c0a1506050306010b03040201050d050705040f0e150d05030a0507020a1206050601030518070e04 80
    0x2201c0c1c1d0020409401902e903c1c21070100002e480c0c0d002482242c012a0402088100d4208034148601c0c0c01400a40541280f41c216207088481030b00a4441d03074180741c0d08000c2c0c440814002115010300d2485526000c0e81c819451040c9420300c8110b0610340c43e4008416021700ca0032110103500d209445c1c50041054662240d400c000080050481c0b0103821034000f00d05005484c00e130f0110a039401050358080f182a501c1e4181c2c41d20445101d4422014002c089126910040d401e07038000f844d408903003400300c0d12800c1d00f0b501c980414440141c10702d80050750300d5600300200d040500c130b440d0042c0b4580c0c2000c3e06610b4140c00181c80d510450706500780c0746907108001140240034030280c07000781c44440c95128515840d912030312031290342030352a821802c0c00716046840134a40b582c4141881030f8058080c0d41400310311380c1c09880075045290100d0b401100c090000c2600c26000c484c80710614021200803641c0d0501c00005400c0345d801800c0c881c0341d5288010814078038a80040c41d50200c84880440420982d168 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 312146609 1250 312145359 312145367
    0xd0b0307030b0a090c0e06180415020309070e07020303040309051c17090312070305040e13020d0b01060f030e07120302120301030f05060709060e0d052e060f0e06060a 73
    0x6420080c5085415000e2203072100f981e5100e406181d1081001c4100b03030b621014030404c82c00b4111340c40c5610100c081c1003003040240d94160349400902c50211641240c5085120a00b41d801c11a0781b0b01442d0b002503400c00c51089042010f81e005400750015520b142000d48000749082c00030f00074140240442c3ca5150010442c800c1d100d005150480e4584404140c0240a810b403a80602441446440b4041042c2d180032100070850304a20361644030141740074a0010005800c4100030412986801991001d070301503190341c0500f81c0c04031f200d404060400c2d81003800c054418220350491000705442d0541040a18400045407425116030744030840051a0b01d240c2280f0380203d101c1024054a0301100000800c2101512403e13200d210700d0590380c40381e80310b00c01100d070108184540c100055511450703421600b0500340000486002d903094800070b00e101c10041801c40306403803600e030300300340b0200700020514170714465000a01510240b15422900d04510551181c00181001b44256400104904100d002d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 312147859 1250 312146609 312146623
    0x1003020a110a080d0c090e06090414060c121501090506030a02070c030c031106070803040320060412030b0103020901090e0a1409070315020408151033080c0d0b03 71
    0x1500c1180d08030782c1c40d490001000c0c2c01c4080800c881904042582c44405d005110020035601000f03411142585c0301c004000b101e081c06001900c464800d850020b10180c01402147c0c816558283c81c01d6888418810b12801d01000402030310b07800d03120710303444805603a100a180089a10488505032039403120114000244140180207001c03607000c1000004119024a1140c01c0364058401c0e00107141801c403d0014501c9803010040000d181000010002405481c0f950078104880d4800040a010076001500e0074100f580d007036441d0111506c54120341507143c041d400c4416820b00c2d0a40c01c14a0b03980010f0b100d000c280c002d16207114510030010f0700b01701895001922214000c00b84502504040840b141c9a4104e4041500c0c01800e9000b240d1540c2080d00071201203038028401414000c1c9400200b182ca00c0c6c0280203003265100900001802a0180315580181480d005422090716000194144007010740f0052b102440003501c100002207c0b0581641da20300800c5401242d42102d4000003030030081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 312149109 1250 312147859 312147887
    0x5010f02031914041404050105030a0c0909031e110c0f010906030b030c030115081513080306150c2b20120a090e06030111040605090402040f321003020a 67
    0x10002c54005000005c800080900c00720688080240c3d0f62141d05044d19800107850243c04031010807010041c00380b81d0b130f100030300c134a01900e00207141c0e0580c14442a15614405143c00c002140800940c200d18410b2003819982c40c411110b0194009014001801c545901d10441051590f182c0b500340381924140308880c4100c000071300800c034150345001c00400303022040c024030815108400500008000c0c1c010003138094049152241042402c41d40c0f11071a542c4001c1429401c4400641880345103503c200182445c20310000140c500700b02e00f09220700c0505c00703e00303c0c0c07004100300100041c26650040c40c0c400c5a02035036600f80760907603102c00d40782e840c1102c0c2d026081c000e60800a6007024140d4454680020348070b80c1c1d540e001d0304d502c1e10300800d0300740e660315620401c1c074540410042061501440003030a6091024001609065031000e00031100095035002002c00d82d040c031607800421881d0141d02c021450301e50495080c81da100d070013003408000c060280c1014035078001038031030712a8011407622140300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 312150359 1250 312149109 312149147
    0xa1403040309060915090e06030c040603060f0b04111206011707030c1d01081519081c02190f020409060518070f080309061303080a020a020a05010f020319 68
    0xc00c0600d0000c004211a220f1140001ca440e000407503500c07091061201e0b041d40580e00c138411a400c5c86044010340801800d056894461080360307543c1610b81c5d0192900650046070000b5000c1c013036110880c10783d042c2039211032040c4c2c602180c03050f098125100741c0310b08004040301100340d82c1c0d40e880180d96072000081d0108a040d1502c00f0407500c42d034590003080f141c0a4503600c9181d00c00d0038440d41320050214481d03050201d6000740004040210542c50140a1032004003840540b28003503084001581e840d40140019800107040240e41021440303034400015071500c02020515070000c00054140755800004081d1003545c600c01055507120303007010091581200e802c108508054035038000c0e05007011240381c100e018540000030403003040740000b01100c0700c24024600c1d0100383c00401000341d000080012003615110400b00119a210014200081041d0020b0456a1050041000640c010342c405810020009500391603241d010043c0c2e017540c2c0c40b0752255410807415000c1501d5503a0168440c0c1405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 312151609 1250 312150359 312150361
    0x9020a0b090103090f20090c1b07122108061e0f100e2e0c15110301140901030804030b090f06070203070317370c031b090e0703020a1403 60
    0x102c901b03007102040c0b012440b00304d05407910303080c010700094650454030b25551100134001800007071412045d00b814020501e0565260307503210800e0880303014100c41c082d240000101d000512a042800a03150f19008a003002202e6103000e10008039030600100340c000300811007151040241c0c44171840c048180300d00400700792031003c2501300106031608040103944108044120803000a10402c810541d0044400404090500201095980c10307401d074001c032001d054030020340580c00302a210b0112741000354803040e43d0f00d515000440d14403038a9248942d100303a2902c4010400600404102c50849074002188607840d40e484000b00e00304145117507035210310b011f070300c0412000603404001070003101d00c652100c00d09051540b84500c42c100d012a080c1e401517407022100c0d0940040310700b0f00070002cbc10440503446402c2403178040000380d40c8810303080c1010984408401015081408810400300c4041c50403451045c60242c5103200744401404000c103042d400144141043e02c14200004a090491991503076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 312152859 1250 312151609 312151613
    0x803091e0d0b0f0601030e0c190911030601080901020412030e0d15050106020f0601030507062111091005091e0604050303030112050d020607021c2001090201020105060409020a0b090103090f 83
    0x2d01d00480d0103542ea1106040020b03085e600a05c500345140681c480200b0503040308500340408082450003602c1d841c90410300020f600085401152360141d400c580b46912801c00c60000740031200098110704040c0d005120900095002d0031110341e8081d010f00d0160316400940c40410707a8100d041c0809050708404c6109900f0541c0b0642100d812205181c2c00c40b05850348802c3d0303403521040c0c2070100400d983c01c40329040098522134580c808416091011000400107540f880e0300c00c4422408030181845004156840e4501d0403900b00c1401d2802800c04501d04404940000e0070300b40303010f103464203805213901009900d0f02c402d020344018110140440350341e541c41c1c10040784c121200031411540c500c02c192100707901620124150340a110705070000c0080c01311410303441d02c460f42900f80c40000c2004001c040605c02001e03601c0c146244000e1000000c1d01e0489000090a40b0380003058203020310b041007007040050303d90880110498055005481c2c440003407070012005041c02c00e00140000d01c011141d201 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 312154109 1250 312152859 312152873
    0x1605060103050601050109120809060f0403110f0916030504110d0305031b090102070b21010b1b0d0e1201090b040b0a1815021605030a0909060f0803091e0d 68
    0x4140c0c0d025100311103ca03a698070045030440114003c001e80c0e00e0000a50400045180f400741a41c1c4d04000e226a05110440c10101300980080d80262441000b2803a40c840034180002d42240d4020151204000c61802c52500a4404400c415078410103583d0f50000d000d00205000d80300020000602c0c0c1c501d12545814000d149030029100318030101078525000955072380b8030302200d0041c0c6040e0017415000f4501103d20381c0c1a00f2010f5422121005208141a6480f0504200d400380c003141c0d0025844031204042c030b621400b40504001d5041d40507401c50f020280c2c0040039010280c0d800c48007070b84500d0455407001e0141c031441000a00400410703050108000c81441b600d481071003492020086c42c82e11017001e1100da000c40d00d0140c040544882c0f25440c50390160000c200c040c0103050310705035006050341e800745103a00403501400050204c1d5401c1c4818081c9004110083c031400022402a50030140c900b0f84034400c01503490302c1a60000018441c911084080f110031081c014428101c0032102e0802c1c003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 312155359 1250 312154109 312154111
    0x2070501020f010905120304170d0c02060603010c021902150307031b09030209010e1f060e01030f0b090112050f01020412020a0501020d080402040b010504120503040305010c080403140d02160506 85
    0x1800740c01212071a6840c910140700b0190220f4101e001000c6450385558824100c0d4800381c0300351040316a609020b09030807444402820009030505c2c002401e44082607000b0f08149001e040284a40d05094603042c001e6070000d00c1480c4101c0450704c01d4040d00035440010035980c050700b02000c40321000b108102c00543c050b4444480e203141c1050803140c44e08644421601260580402540002c9800050049000d15441d0b150704c108034141840980041c0100354001080070781c450f03800941c00340d9211020b941e0500070000218514041400320400c04230014150003414051842c030304611411040910a00300480f4000c1d2000c04001c564441d02c0d00700c2c0c00c00150440100340e003d8070441800140d554400500c040800c0c80940c2e5040007a02c03130340d00700400340480d04022810001c080c0000309440c3c218032801c00c2500d208030020b50741c407407551500c9030a54544081000c01d00250404110100b5040280040b0250545007010f54900044c07401034001e0189203840400170315500c0a14080000001d209 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 312156609 1250 312155359 312155369
    0xc160e13081b06040b04032d03020f0d050f0601140403030c0609020a0509010803040905011401022e020d0e1002070305030403030b04110304050a03080a0204050a170703061b030506010525050a050d0207 88
    0x68840940111103a54180709441d5230380755120401e44001c44440e211f98061b0808000802d4140d240c00c400301d00044c241e410684003485244220800e0009968100c41204410788200c0510b505140c07568034050241c1d010000080c107000d032549041004c40d07441b02192006040c008022203215611407003901c0d540d4010b4000c401c01e280c41d0900220b100148841500d01002e0168001c20700003021001621100305a282c04504d00c1c2000342c42c8044c4848980041c255288440307200081c0780c168005800e03d04034025101000c0300d0b204002c07550110f580141160f40c840c3e01410040b61980300e41011500a01e054444520120400b005000400101188081c480b900940d00d1082ca0745074202814201e00c81c0c4d204e0141d20044201e000c00044221a01c0701000054681c10b0394210380e500d440e948281d41008210341c5506039660400d444041c0c251182d03d400910a2800032708207880440b81082040980500520443c920346045081160800c040040d4079444020349400c1c00342001c0c083d544030700700d01038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 312157859 1250 312156609 312156617
    0x3102105060c04031205070507261b280f14030f0c06041203030608010908090a060305070e040b120f030d060b03091b13020c160e13081b06040b0403 65
    0x46600382e0b021400382c801341d9402c1941030354a40d508020a03107051380905011240780c041d80000055011720601007042200408628007c5405d0b188011400c000c0034010201c200c80080c46082c4040e200c0d0000040742d0319500c4440640d0910b600c40ca08045905a44450715070002c042c0c1c042101400700d214003500420a400b22070392100580001a16818908185900030f60240000c005a500000a15070300a029050006005480d5010b0500792801154180c540840000d40c00f02607003080200b510080800b0b280400c040c1c1040b00f4002c1c904668141c0301031003903407030322480d400c0c1d5a5020405134003076010000f00c41c00b0310044240c003a2240c0001030b902d9031162404100040044d0a01c0840c1c0c480e540740d2000c1e2043c204403c1e0285403d0005580d019003001c240800d1805403203040c8010064100480010300f141c0e620145086c40c50f051300c1e0403c2c11078802003014001001c0001b140081111303801825130740c5612024042281c0760310300e10b40000b054410001800107014400180c81d004900075a1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 312159109 1250 312157859 312157861
    0x30711041107050a051b0906130b0d1b0f0602060c040302100516061b020f0319030b0a0b040f320f04020f032a0301030b04020f041e05071e03020310210506 68
    0x41100c122808c840580e00807106c00405807903a5529804480c2082000385854511840350700d07101e040458600c900983c0c41120081400300c2e1440d11980002861288010851803804000d0051039011383e100c024001d41d0020b47c0750038014040ea0039108560030251000000c0640c030b091000c0a40240c00c5015283e000e0311018404c50b0744042460014003210400852802089040225101e51051000c004060b034650000100e41e903420380b081c0003041c08000080d00c0d0f6090074800080c480f03966104121490700c524689421910132800c00c03400400c1c5106060604007a28040380303030304c50441c0d03031a540140b0020f0305004112a100c040d50080d4114942e41c150003922140c0c070220400c103080002c00d5514180300410000300d550003081c3d03020344080c1001c816101c240010030203540720117215401400700c020500517484054800c49600c4071b0342c0d290680d5155010b184034513141f10044081c0b0704143d00000002e10407610390502000900300150900f8046201a480b0041c105000c10700b04c60900400b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 312160359 1250 312159109 312159163
    0xe06061503090c0d060b12060a0e06100501120b300a0f150204080114241e01090f081f090b01151709060117030711041107050a05 57
    0x80240c078802d018a000800096000c43e0400180d1052510125075131920b58500442c3c61f00c4103541452500030120052003542005180e0380161007001c0d41d440070f6030f80303d0800c000c0ca01d503001c40d070241164030a0030311061030f0300079240080c0508011010f090b0050503900c072000d141604101c1403594000c88a04001e11540f00f40d01d0740c1d807145013922000d841000c0f191100c1c800b10b0081403504901103080320005251a50303400403d4251041d103d42d07104940400001c00646034101c28852401c29400721580c105040c3c000b0010311001d034200c102c5c005000b941840155141d000d500400b0141c41003498000401342c0e80d2680565851150416400d140105411208040d80c680141c0c144a548040140ca0750382c2004240180ca820301c82c00c42080015401889440c050141d42c1c0030302502d104000b07044658103004000c18030020149614009502c10000c01c1d01140c40c0e034100c92007146049501240a0107503020410550040c10405070440c020f0070000c008000c8000741000585000e081901500d000030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 312161609 1250 312160359 312160399
    0x1051308030a1709030901050c0304030b07031a01080f0c090f090406050912070c06080a14090c0f0f0616030207030804140f06041206050a020f040b031f05030a081c0e0606 75
    0x40c4e030418501e600c1440340d00c40c0e81d80240c000d0000707104200216410950750b0380300d0035035142042d20002d0100f55541e0b000c05a6803a0315854a084000030300709205941440340c401000325030010116604004023060300a219650800c24003e5054002c0a06031181401e05046008200641b0030340304612401c11040200702e8800150768034280c00541c10003c9a10740f00096540808c02040b80201a0741d031180d020b014410f1030035850040f8150740080203e108d0010502c50804154940c1d14402c0680000c2e10105a5454086a83e2000081110380d061092450280c0c500542500000e00048012030049400030004080d40c140300c070112100780212585200b07100351072240d03000d4000110384002134130000c2141500700d25000700300b56200519001a545504079281c016801000c446000001480303295460041814420604c00c000e41100300d16100c0000e6a4a021000040402c0c3c40807503402c00e051914440080303086d4002c842400700a0300003900350f48401c5c2c22291079108880c4244c00407144518 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 312162859 1250 312161609 312161611
    0x2130602060606030403050c01060f0902070201020601050105030c07060209060c0f06040b1302100e030a0602040f05030625080403110d081602061005040b15071a090a03140901051308030a17 83
    0x2003c1c1c443c503d1903d444d24205c5641c0d000301480840b0b9920386600140c1640c0e0700c45420002c0400c0d22005031505800d1000905180d0103a04c214100b10341881403000c0c0940031001c641c2951341c80500180d48150980c04a40c0501403003044d6034440c010444018007a82012440c43c0c4698450161501a9995107001c094804411038004e5044a0000565024180a2400524049070040031602c1010180e5034010990b0701980200c0c40349084110b04008a0400f00a019009196504a42c06a0302c0c61820b0201040b0a10a40b80030810b00b4404607041c50300031010102c4440e905800c0c3c80c00b50398144000782c034901068404010800161100c0c00d03140d88042892400b442d02680c00d0902d0501d0501000090f10000c54560f41c0100014480581c9282c004010306101c1d01c6804a0f00c640c04d902c0309900481c02d4002c1c50038000b034001d00c031681e0000749e1024010400c00103010340c03107031942d00d42c0340121a00d00480304124448401000c0218074150008050002c5084075038a050000341cad13402118080d810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 312164109 1250 312162859 312162871
    0x1a0315090d0206130807061e0c02070f0506070f0c09020f070201140a0e011d1f0201200a080a0f090606150306030b0112050a0b0703020a0905040506030d03090212030d0213060206 78
    0x151302803408000812410003170010b0b0340580c00100700302d0366100550450001000d03800024554401088002c04e030140064401060103102d0313403041504c1c25000c14401d10880070021303d005014504e440030444c030f1010350b00103080321610441d01d4580244a281c40f95015070801d0380410400c490703c1e000710800c90100c40c58101c0c46d90710a450701c0301d02c0d070064400020404080328103861440350845035480d503042c000441d40c62101855005050b821011382101c4226032112222585d0398059042142000e040f252109601d00c0c040e80141e580b22070319001812080548041c05060000341c006100558004030f0907211044442800c031840e005041d011034516100041041c880c640c0100441810102100354441c0520151000c80e8496650401c0b040c000716910340c08a6404181460010b80c000d480c44054202580c080100c2d08000000980e96085c85102c0b034100340d02e41c1411011519250b1030140c840d0306550860381c69580318001e0b00040d401c8800d800724a40f00c0c80e0000510f0910000e900c90140e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 312165359 1250 312164109 312164131
    0x15030602180603280b06130311010809030304031b0c03080309010c030501081b06090d1a010f0e06060a0201060305010c090518010501090e0921030f1e010501031a0315090d0206 77
    0x808080d603c0b11039401042e0155160303654903085c0c5212030f03c50700700400c2e0b12204610745440181c01c51070318111209001c00740504015041c0700b0803501c5080001201d420a070103050140609078138460855181e1460f400041c900d01001000100b00040c001c0a5405000400000d101503071800c4021000c48009116240c01c5506c0040303441030540340310f10082400040640300302e15102c41200443d01d4032130400c404030b80c00d100b07286112905150402083d4050280307071041045540ca0019641d50426014041d03074805d280000e0f190120a0003503000030011580324009000040300058044c00101c0103106481c040c0c0d80c1e00b0000e55a0310540c000d00da041c1e0b20141c603503418140c03d00d64030058500c0014040c603003501c5000c0502d0020364003606260604000f03001e0b86a075a10702411040b040c6d26001c0c001900c6900701d200d039100c2c0b000142068034103441f000c2c0f17400142684007100750700e00c04507104c8486405005841c400c0c2040308020503041d1140280c41c00321114040c5403176007240d81e0f81c02190551095 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 312166609 1250 312165359 312165391
    0x3030c0216060c0503121503100e030d1e050901020406090611060412051605011a01081003030503330f01020610090203180f060403020d0e090412020115030602180603 73
    0x41c010f41c205450715004004403410250001209851a141940c241c241600e0703401070140d00e8942000345039230b4215441000d0001003585020607a030b0303000d54001c0ca40910380743d50f100b90000345014030102004000c1c80c000e2001c0d091205203207000354028080c003000644c004001095030b5000c0c00c02c010340c540914008120560b03039a01c03442d1200106a407000c0801a041212010796038070404100241800390340001840051090010086414603070814148000301d01008081411038003078404032901400e1542ea84d0340c90f4240d4402a83c07400042d80c1581c0035440307244400c4403051210340c143c280182c0d0141c44206442005a83e100005c840f0144094032014092001c0001d603000785030040140449104015403100d50203040002c407803800849544080100018540e0422448080305c040c0d08040920f080740001042e2044e00040000d4002a20007440c03c103601c1c402d61022121300c21041d0320b082c0d015101d16240000c0c0d4000c1c80340110064500900c0300062401000f1603004842c0411400c440c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 312167859 1250 312166609 312166619
    0x150f0f060f1a030601020703080d0c03231303031b170a021309090f08040603050601091401020705040221010f03060c02030f0304021c06110403170403030507021201110f0703030c0216 80
    0x10b0b9440141254114080e2000010006010380c0c0a8803802d00742913404212083d107144012b04450952600000c0301002e4a03d14440640305005907400204004a01c0454941400c0035030103006409080c90741041c41c0c030010541287e1120b01c4504c088020040218a0340780d00c04a08141d02500a1a4003114004c00d820405541280d0204000502c83e2084142c801c809440c0c49095401a6203c580400c0d00d400410000d03691020140340946075984281e01c902c0355510000355125403c0c09094000c0e9800940c3e40740d9141c40e000801e507401d801ca0001c03160781d0303114420a0340700310451004035116414012130040450010080d0707210040340307044146c1107943e56001c001d8808092410098031010803103024020901c00d020300b41c983c00f201e040305541d40303281d45082c002d590010100c103a004181403100b4400243d000e400c17280c410780c04403061200840b80c2d05086005002c0010b402c0c829170b400054083c03001078104040c1c80c0c0140683c408001d0182110000c2c1d071959210242710002d50000d07442408 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 312169109 1250 312167859 312167909
    0x109150207060c15020315091605040519050d060209010f0504030b071b060507050c1b09040f150f0c1b030e12120304060204051f0e0904150f0f060f 65
    0x1c6070358000c2004d551058007400054040b03074025600740411801440702254641821200950091a0500c2d0b0301e607000a1404010441d018a0044500ca5162240d020000003ca0000030380a004028060041001c803868250001d600400140340800d140010b500c60542c0210240c2e02101e070008030001d896640d01e1400c4845a0203210119840d145100101c0c0c0451604d1250034420f02451719030555480c2009141c518203041c1140c1001688000140c0d00c5580d115241e4081e0080c3e0300c1098010716411038a0041c0003590050900d050306861b02950514440742e80d00610f50909040d01c032101710511801e1004c65a000081010b40070400c0c188403507001e42440506060060802429503040c03803480d0350301c5100350f403090305c05842482c0c0100e428001450407030002070303c0720702140080c5c00161810202034408200c000c141485001660001010701c2f00f00010401c482810324804c01441c00e088035000700402e05043e200388101e191600c0801c034800d0b1303160100252883c040048640500d00c81d03400d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 312170359 1250 312169109 312169127
    0xf090c0e150d0f06050a090b09030a021b04020c0303070e0f091618120f020909010203010e011e0f060c0506060f1e0409080a052d0702060705010605060d0605010915020706 75
    0x724002814140f990100d04075220b2280180380030b24011903c0c00070342c00c04000142014104045d00d8004000312070140b500040c002442c01c4210094107650300c4018000740080c0500d180003407560100000f00315803070707500201d4078805500489031080da4442203410321090000440b10b0704015002c84070f445d09090b0044014032040c01c070801025a01c2a103407440c902401e04c0b102021216405040081e80451a017148480d0b80416144001c604540c503289094100f8201842070704024954000c0c01100c080d901c500c1b060241500410162000da56000020002480d59109444501070307400131070030f545080c0c0441040034a0040520f9612040381810220940841060961082d07403000c3e82d80015031884080e03e5a151146c5030503494010041c100d240c600000300100d030a0441f03040046007106500820340d49050707016229a51552850728220b40109082e80249900c50b0003c01e504002181c00c0d00150140c1d8800c1c0d03035050005a0b142c0f80072500300e04801d14071300940c00c001d0b400c0c0b1019206003060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 312171609 1250 312170359 312170363
    0x10618050402070c181e050601091205070b030106050405132903010605030105041a0907030507090507030f06030507090b01170c0a0c120c030807080603150901060302040f090c0e150d 80
    0x1004e06980c3d4010303440e24810800c1d24803001949683d02040000802446142002c40d901c0c0244058540038000078002101405844e000644941c181800d12404021800107407001c0040c0a650b561100006071240c0c10038420039102d0178500038444030b00030481c05000414184280c0182c400140e40c0c01004034400c052510b03e4056507a4a070010f0240d909000b02801140a0305aa51070364181e03012020f9042c00c01807221249601108003000004e600080d02000c95010203800110740e21801c5007280034050790192401c110341491008414040041800421a0a461420006021964019a00b5502400b02105400718000000d004030700440c000303020040302440c0002000c135070741d034403035102d101185907610000d0341c1060b6400400d5040700031960031503181d0030a44000c0c500706001907a9601c11a545443c03080d01c00009c01d00340b040941005001d59401402400702d5100c100500c8000c2144a409688804200000085041048a925010b8580c2ea00013050440c1c456003407002c0500d034030000f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 312172859 1250 312171609 312171623
    0x105030a150b060d060e0f1006020c0d0201030b031507120b0a1511070e0f1e0403030902011e0201050a0b060703050f070f0f060b0406060e130e0703051e0601061805040207 75
    0x644060405184141c5c406080e80f014009024180840403190300d05000700440d0100041400902070241c000400740f03000141100d01d80b00c6038090b0310048000c2d01d80c2241c8035415201d440c803070400e00803038040301d10305c42d01c429958040300840104090050b2000744901e550420b040c1e08092015140d80a01c0c2c8016150300d0070702e080409051b00d03840d4508041c83c0d002890050300701088c0103014004182c1c041d000640300f01a00c0c01c00c6d41e500a410386034280584020241036940c00703c1001c59001d801103501405140e11394929003000140040c0c042c01e02150025240f13881c02c1210a5946000b106983d141901075603250b040003221001035000b9030003a5019202c6032545055000085c01b08054a81000d104001c080b071480b8154052100303940301608402e0902c040103284403055103400c0a202e0190583d0140400c3d0f0f82d0b0040401e41c100091030700068200e02908520003010503541c0b100c1a02d800101044078801d81e600d0700211003e0403000c0b000c242c02407400c0c00810061510341c01400308180070f108 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 312174109 1250 312172859 312172867
    0x50d0204080f0703120212042c19050f010b0403240906060e060a03081602060c0a050309120c010503040b0603011b0306080c0d0c05040504051218090105030a150b06 72
    0x85407511442c0700d50701209034086070081c800c2050841060b14100e07028002011041602007007410039020703a00464118140983c0c03000350240c6140c181c10880c404912041c0564148269904045e01c1c1000305400c0d10303828200407401c556170702c3c02160b04030760100103101e00785030840d51140780644112428034168000d6181e101031484217440303180e00041c856400041e41c140341c203255420f00c0034001c110031f1042c0d841715410400709a50074101c5a0714040c5803591030700c041442c40000d44600680814610a200303440004082000020041141e140f0484040c0c158091040b40c0caa41ea03003600c42402d00144007440450001820f05070b07134940010b0700800108a480003010821b503a4940d04068000194640c02c08000c4868180404404004140d8160440407020703101c00c500c1c2e00551240b64041c96131000018240130003400396000840602d9501543c40300744503c059a0001c0488c074a61003003665800004a900c0c00040b010001a80000d510540000414003e0001c1400003100c5410080c104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 312175359 1250 312174109 312174119
    0xf03070210060e180c0f0103021b030d020408070e01080318010e090f0f0703061a070c0b03011e1205060a1a22060909030519050d020316020f061303050d0204 69
    0x8010a00075240803d900100352911101103403901c2ca40120600c510381001607403008030b455041030384a0b40300b801c2c207004d031760b640c00042040c0e5400c03103c0000c80e45e00d000200b11f01d0600c07041600108101c0b2613410844405c0ea0300c80096480404081c490f207103460740104000c042c0d5192040030900c28541c1414860010044600032511582d070864040c05d81100700d07401c1203d50782e09805203d810400c5407408000b10f0341489034004c040c1048821005040901003598030402000d4010320000c1c1c0014020700f034a0f941e403048400c0040030082c15221035001c00d000086021491802c41c10360894005004141c00d884044100c401085010030706105022009071000c12504d4105660040008a04041a8a8017615480ca040300c07030940040e44407034144550340011903070180a480522600d10064124044060020f86903445119110304506002104000c0c40807a0f6500e8203856010326029030304802030040f2503c1d15030404070b500143c07800d071581c1030701d010a21039005010110030150300145070035210 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 312176609 1250 312175359 312175361
    0x3150302040f02070201080901051905041e080a0207080d0806040b0102150709060207050f0d030f05090418050120030a02072d02010212120601030b0414040501020d0608120f03070210 80
    0x110100c00b8a858001640500315640b114907141c2c01041d003c020022414070400ca0154001402c0044907400c2e00c4102003000d200c254032485602250034034002c603100b1001d00c0d151302c0c6c5400c540c03501c1001d80260070340012054004241c141001c3c40550340c03060250f491504200091011502050451184075034615401c40300040c280e0050446441d2561503030300e000300c006c5c6403071800e4000502800310b0b001f0011380c0c3d0311010103100041e0b915040201c85000181c804840501840410300d922a062040550542d0070405820002c01e004a0003840701c250b10340540b107003610b10b11407403200d04402080083c140008035409403840c54892070304d4051703000b0034401c804100c1d050301006001100d00111100111368040225a00f80440e47e0b4545040010081e035540480800034002418141c4904010400760343d0343d4452050a80e950007004100c3c106030034a14000e4000d0205005510b00d050404a010381d4005229880e0312104903129180c4540c1001820240e040a40004194031610007048008045 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 312177859 1250 312176609 312176621
    0x6031e0501141c110f01020a0b0f01030b0106080907060f03020d020301080d031d07090924050106030b0f0d020f0a24080703060819020a0b0c012009010206070315030204 74
    0x20210203260003803090010490309010f516030480380c204220040200080c1e000850310546034007110400c203070090a000503800d242c554000100004078280c104040004004c066070b0503a0300800c040440c40c1c4c0c0750601995500002c2d50701d068107520070f034800c004461007031102000f800100c0c5409401c082c4c0014541059810a800115440e04100780b0005200e606d8032400b001d01c42115034020340c84485010158407a8020700405240b2130300c5203002e20500a4111200c404550444140305032241d901c0b00f004020b10082c003074980000e04100907016546408070403c600c080f0000c0010304019800c0d03080015807404140156089400c18070000b81c403101800d2070b01c1c445021214850303251072244000408511004262000345440c19006000d1034a00282e40000402250800f200d041d00600008040c0b1801d54080c01340000d00041213015a0819003042c082c042000f00941400010305602c00c003180940007403140164407000020740b003035129401038410000b0a281c64038100ea1250046819a62 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 312179109 1250 312177859 312177869
    0x4060504030b06030106121101021516090602060106170a150303091805010f0e04030c0b0a0b13050717040303090f0b04021306060e0f061204050601050a1e06031e0501 73
    0x20041010000c0c002d011a01030f0b80500c0460007000206e0412102403c00340c840600034100554004d8850007a9000300030f10740c400c2c3d009a11300101d81c54103200c24200c0030b00840c00e03400000c4080c44000741c19400058141e050310150b4440402c0080100c01103015007400500030344409484031000001a8820f4070040003541c02582c44040d09410300300b1401982600c07040c50b02001e4507000040003001c1c0300300c000ca010707680421079030206503c840c00c040314a0391400101a0017485001d05000309821a544001500c000a480f184071010100000600b2039408039800300110700904549038035450307510b000581c0300384203050004240c80c0d140c50320180c032101d60b8001c40f04160540103020552908010403075130800820b10600001c1d04081000f0306c1180d0884005000c1d14010704031038039603910802600c40000c4042c500415070306e810b040a0303690701c40c00e201d2140501304a02011036200c240e10882c01103802100301c002030240c6001c1c01280180802e03001d054583c900d896030b0010011440c02200d000b00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 312180359 1250 312179109 312179117
    0x15031f1706040c0803180d081317010e06040218060a170c01030e030711010f030e0a060203040308060607030e310b0a080312010b0903150103030c12140306040e120406 73
    0x320b428503000c0070404460b0054030f980d0744203200c0d2441280c40042c140c452564243ca0580c0000c24514001c0524090024000d500446101021801120307200d4840d5440a1103c001e0100000b0a03c52035110101a54007075044003914645848400300541c10075045000988910041075035007581540030514184600000d42080c81c52803100d40c1e05026542c241c0612002946c074003192542e412012240341c0781c0c070505001c001418801d07000d0080d800150401d010b00f041e00e5210501b880d00303800079401144d04501007050003001c85d0075810100c040c1c450150303150321100445139580040100b1011203402c1e0b40d41980e116040c0324000602140b40d9030780c110342d0710004950b941c660800c0003840500c5401010040e4403e01c50b140c8200039200c00d06044a441817122603640c016000483d08080600706c03040c81c5d5582c440000001c15911000307000e50b180c050944420289500d030b00c2103808201c48000c00d100c00c0024008500d00b49040d5110500e102100e0040b81e924101038640d0000c10703001907001c0b40100e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 312181609 1250 312180359 312180361
    0xa080a0f060605150a0f110d02060603120f182b03080601030507121503050111210c030103120306051002030a08090705030715050c010207081815031f1706 68
    0x14280101c4001d00022640c1c088440091510100180560303041701c01045409500c2d100c040e4050b11015000c0c216020644004a03404c80c0065074410040d500c042c0280f107528480340d510314860003500d00b0001e150380000c2c036244c1024030000d052402d6004190340960810390f110310343e0300b00711b0480798000014490107001400e6801c02030b010078001409241071500340f10800101c2d0b540442c20b15aa4040ca8600181f41640c21102c03500055454100038419860403200d00303c007003205000761010a454812142c5540418089082109400d80e040c150300502440184000303401c00e82284070000380385c03a0001d007040d6a40c000413100c2060004030700140e04000740c038030a07003035000f184180c1c0140c4010041031114544000320740d54242d10f00c608525070b48004042500e02e4803c001320b82c0e000c11130400964403030110341040340c201d43c00180707007a82440b0b030a000488541020310800c5da031f80160039001800c65690101c0400c0b940044402d440412880e00000b06504208000d680c00d0901c1c454014285 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 312182859 1250 312181609 312181613
    0x3031e0c090406300206030601030905030f030103030e2403040809040e070f060215010509060f060d0509010f14070c02011107080a0b18211305060c0f06150a0b090a080a0f 75
    0xf000004802060a2548451003130003513211202103e40021007841c0020750760390942071107800c60150f0061210201000000042415030041c81311a03409130445400e01d00e03032400748603c600a42810340d0320540074000d100040101d24800d000d00b98140c0c0140010030004401c40c0000c1c01c10311507070050550a10302403014814213904000e4a50f03442c0180d10101c1d82c0303505100c006a034454000f00140c0c400c892400701024a912004242e81071660380e0034060205060207440640a4003549c0642c500492600c511006502180e1001034000c510317035160644203680c0f41e00115550030000c03c5440c554401c244000a04500810440346070380d0090b810104103090040004d840403241284036419503212021072554005a000403154804128103019561074181c140c8220b02082076000310b501c801c2c00700b5400800d00707020a5110481e103484045d56a259141c0038031600c500365016030b1036001444a0760030b0042ca54004003c1c41080d2f0014085080103039104086464074080c2c00044a01d0034841c900703102 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 312184109 1250 312182859 312182909
    0xa090806010506131203030209030f060f1e0a0c0315030c090b0f010912060b0d0b0403080f280e06071106010b0304020108040204051b04060207060e0303031e0c090406 73
    0x40540000c80c3c8140c6840011640101c0300b6140e4068414002c038020424000c160180e4100c61040802070140d42c00108075005080c4c4a95003107540c01c0d01400e82d6400290100d0005011013030704050704d00d00c0c603a5600d4088810004066030080c0c501810399170250509405501030000c00158070554448a01e9401c0640c01e005a4900800042c021402c0c80f4a0025580c6c0107105039082c2d5030118030403060b459041c18200c0151001c410b849810410200c108070a104c59443d80d5481940070342c03189078654485c503050101100c1d003100c1281300c0913000e2011084240501d120300640c07265a14010500350f104c2403040f424100c00362a144080390b40f00c24545801e0343c043c4000d50040203c924194103516160300064034007000280001d2280d40d0700c00000702c00c003001384031a0307003e042c420030015140c1d074540320043d5840069000302c401141403e41547c0701d624001040f240b1540c020042c0c1003240d080440c2c40c01c0c200001414100d61140240031603091030b12284990001000a007485019000285442603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 312185359 1250 312184109 312184111
    0x70c080d0c09050f090c03190c05030a0c0804020f060717040e0105030f010605090408030901020d1a01030e01051333020d1404020108043302130b0c0604110f04020a090806 75
    0x140180044d02041070b880e41e401c010300d540300c2008100719036030b6650410385100c98070b031508488d20b40d04d141100700400c540e4054080c1d4450340d1003030010480b04129000c2611405002c0310300075444a0300c13051a00072410020090020148500b40b00180010801c01154154001e50491440c403050000104040d140403c4440c1c0e01c0303901c4500800ca40d500f441e01049000000030030180c60014004041550b5136801d504480c16612450002c1100c00008580d22130b00070f8000b44078030b0010782406902d042001c410704c603050182c0d0413a030004a0000013a5181d03113103000f20800f404400785903c1600320849500c2c1c0e5820b11041880800183d882199024010846000100c80c44034030440004200c0181d8000411a130455045080084580c11000c146044018034040d11000c3c180205140d028100c0b2340e13000780031030340e10001c1e5074680d043d01c0d05030b1400c082c0101c112a047c02d500441c007040102d070f0740c40a6035100301c3d0094514104511800041020790f4840e008031000a900d10004001500041c4455 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 312186609 1250 312185359 312185369
    0x8070530090409110907080403030b030106050612060303090d030806090a0c020a1103190305070c050d080d1a090f27031c020714060703050c0f040e070c080d0c09 71
    0x50034103508601602003980c000c011000d40203565400b4160705210789801d044004e40c100400701074940c03400c500d00410f0345000703641c2100402c1c10280c4803500c0d460117010720815102c2c05041c05042c06515204407034145009001d503900350004004141c000d0300c0c2d00701d109800138040c0c0c440240700d042c00c500b407041508004001d200001c0c68460714104243d40807c99450b02c41d0005e500801040c0e2810000307060080c0b00c0500b1003480c80740f684802c2019080b42c0a480890b008010700c0c0303a1a650b51041c008407103000b0400810001c400c2049010701042603110052a4455007941007800c1c000c900070039881075066a0400504101d2030801510b480ca0013a03031514407105142c00d030340d0701505407011075a0740565101070000b08101c0b91122554842681500c144a802c031300030b00c0780c40303044480d034a0310f4003000d0702c90100080c00c02d00010170b8400103504617004002e000500d14600b03407a20107030500d56240500090104040c613001c000104440c038000c0d02084003100d01c0043c04005150b0064503038003082e402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 312187859 1250 312186609 312186673
    0x304120507021e01090906290a080711150f09010b0103110a0f030b0603130c21081b0607030c020c012d051b070608010e06090103061107080705 63
    0x1110700142c81c0d00c9594a902581c650401004074040801668402000e801c4803668928048000503001185078224500b60119142e10800050b01c0703c0200e41d0340f05030785032034000c912a24041f64070980309200c0444000c604070241d0b01e070b0100380d107800c0d01c0c8000c090b94000142081c0300103210001c4000c0c422220001c20900b410408a04910104407003405a024804c050110322268100c1c10343c0030b40c105202d011001003040b5039911307204d00f90390300b108242c0c181600c1d020780d1180c3c04541220410503100c0602468040c403000013005941e46c520170382c05002d01e00a40580c020b54104a00002c001550003070660762070200300c42d400654000d103000c1d0480c00040c10003400c582e621102c4098a4084050074500030481c1030f442d41d070f1040603141c52090315490801051014213075140200d000ca0b2404c2541c8190707440b01d8850340d841c0c0008581c0d21050342c100364440080c42c01040041c04590011084076400c000042c2401416194290990030003c4262010b401620034401c00242169009a8404030210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 312189109 1250 312187859 312187867
    0x708040609090c0f18030c151107060206040f02040b06131e060e04051506030f0103031803150b130908030f0c0c060406151a0a020c01020111070219090203040803041205 74
    0x540107000352452004c60301031040820000040910702d004d058040c540000ea550b980640d100079040e030706070172981c180c4006001c1e428502c414800225410f01240d0312940200803d848645818400c1303240710b07104a900c1559040b00325901d459030409065601441c081c0c0e0b4007180d01c0c118520f079141c001000c0408507022154014480c1c0c5812401c4030201500a0b0b400084c0b941e03881e50a840c401c22a40411544500084100170105092003011416a80b10769124403000c10384042c8a5500d000c0360000038594480029150b0104d1904c2c3e0098820803001401200001c15040c1005d048400c220002e41d5200300000030000c0c00ca088900c51500002f10b04012442c0030b100d07040c00c903150300c07016000a0007951111204d9590b058114854405841701e40000c3e241e500c05100c040241d54840c0034604050302074120030058a60043c400c280c1203510b8200300754034141003982000030020490440380048c402e42400070400c000988042d6129a11500e82d0a50700c1c10142044440e860301c1441100401400704 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 312190359 1250 312189109 312189131
    0x1061208030903041d040c0e010308120907050a08151f0b0c0102120a0b041b08071103130b0a08010e09070603021803010f061a27010c0503070804060909 67
    0x11800220303420244040d100c0d26001e003400c0c1184aa036102c119401c1d5241204580804c1304500f00d03010342c2c03041c10802103066a5190505082c2802d2001501065080c00301c2c2000709035480e402c5d0340c04208a03041d181d0342505c9400050345020760b50801c00360341d40b0101d5081d4080c00c5003203405401140d000407201c1005074503c080300700c980301c41c015004009008a40c6c4400c3c82c809405503603c0440e80b107494141403405440020040c2403106602d40310b20300b1f04844d82003104080c50754180d8155070360350301d0f4404d581d000001d840c045844c0300d4400c0d0754401007121201c0c021201c842500640203003826550384c3c1d5151900103100c4441a04031218811084003800f000d0340300000c88a0480e01e01c3e04001d0b85464142c58918903007800450388035055420042840c08200c0303264070241c1510f0112181c6070075034030144100c0c0382600505c00188080e4044c20b4000c140882d04021480340d0880501d8009100b04241d5500d0341181c00c6404125178003040400e050103510b80110300360001e00302240040158503046 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 312191609 1250 312190359 312190379
    0x803041403071208031e060d030807090302030313060e0603130b061c0c080d031413020d050a0303060501031109060d0c20030415090521031306050a110106 68
    0x940304441054039400c0030340d64a80c50610200d40245603c014040c078a8600e070502400c0c40c0c4c011214560755180b450301e0010701d075008813003250207080e01030110020030340203680039a184c900c040d04040500c07030b02c106c0010042e541000241011f201545213200c0300b0740fa014000d4007100c00104058401e070018070070441d07429144130004290a8200d040030100d51907800110b108202802c0509a2042500022800f48040385111404441034541142c244408100d1308030101c46050b035450010b42030031404100c40f00c41c401c0c0080c15181c0000c00500410400d66075003898485440300450100e529078000304003560301481100c20800720b030398215151903120000905030388504000b00f00d41c13550300c1040d10303522071140280204011400d01c1d5094020450400250390740c109102e035210860b00d13542c400c42c1052042c2410300490704090041c003800c80391180d440d40c40c0c8460f00014102e0340310074000682e1655280701c2402c0100b885458955840070501c40040c007140c1e6800b040016681444010400c2c00b41e2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 312192859 1250 312191609 312191617
    0x804030e0a0f06271d040305040506040914010602010612020d0203010b060a120b0303030105090a1e0204080c150702030309061e04030c140409150c030605120d12050c0414030f010e1c090803 83
    0x840c001c10011b03511441c1c10f99082c095a005207800c420046030101701c13540c02c0d500260012100020b4088075a03aa15000c83c280e4803280906480c03800c0403070064005040040c88900000e10080001c50342080e51000305503550010710240000919002d181803e081c0ca52092a03500c24042c1c0c0036604e11744c1041c0214044103406070002c00d05565070314204004000d0b0000c40c500c100030602c0190352b125581c50003d1760710124091034510481c0c206240010402c094000c40b200d055010b006141821952001c010b9a034014400f621421403018081d00c0d02c07100c83c000100050b500c50f00c460f0880030304045500c144049100d45a500561a0000c1c14000c24149490386070018200d281c04204501d1021085016210581c859034020000340041c054050021404011069403941c0e5140034400c40d00345030f416104207880141e41000100001d000504810900c0460803401400b2100c805c1400d0682e542120f0b02b807641ea0505403c800300196101da03d1030745120b0703013244515000300c0d9141010000d0b40c40b841 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 312194109 1250 312192859 312192899
    0x19050403050c010e040b0901030501050a0b09011d06010c0602072004020705062205071823010b07081903062d17010e0f060103021f0804030e0a0f0627 66
    0x408a00c4040b056621600301c20140d906c090241c0f01503580da403a080d40601307810794040092070f040a031000f1443c1021405d29040f550017400ba00d400700c0c100c0c540c038804044041c0013241000780d0220000085400f0340000e0991034854910781d107040000c1c6030300d12030a010303002c00c940c4107900402a002c0070403000180c1d00d4200500c40c0b4801000c0b00b80d610040300b81c1c020f2000050481c090f4140000b109040340d1054041000801420700c110340c000c0c54420710300010100e81710410804000140040603454010f495004e108504d01c600d4402c85200034030503240e504411a0000351030b090700b4410401001c000e200042592081440e1101c981c804004032a80ca5000d20340d002046091800c40e0381c0d409410050100c1141000c0e0b41d030704524041d005403621000d0006901075406c10a004c2d507100c914141c00e1044040640c0d4450113a156550110742120890707045550180309201d020072101142106200205203685603e80007030103807000c07488421500300c0c1c1c0000500003113604202650508500300c808003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 312195359 1250 312194109 312194117
    0x2040509190608150f010605030105060a081302040e010c0216140d020607020a03030906090b21070207030b190e0a020d0f0510330501050f07080910030219050403050c01 74
    0x1a420075a0000030080380e4481c1c400c500c03c50158100b850030102c0c103907028113403440c00500d00e03a885200c2038900788020f10550f90060000c1101001240c4503114031604601401c030340d0601142c940d0002416242c02c048144503595540211803110368042166086e40d00c06004c0301c0c80680c0c90020044245443c80c08641d0003070141e480750108565400d41201c20307190b4014680e01840f0f4507805c000701611014062840030841d500d8000c50704084410a5410355400c5411078a40a041c00200c1c40c6811800f4042005601c40d084c408000a0b051000712845514114010980c1218504141c0140e4207040c0140e07134150402403090f005038541d020464040c5800402c5040540118a0701a250482141640202030b00d072810643c0124500207422000310700b421304501007482c1508030145074026074420580400e10400082241e0005c0780017030901d00d40a114a41e04002440001c03550340759040c0a040000b0350300241d51244840c00034038883c003507100307890030318101400c603030700c09031354095400c0b03594140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 312196609 1250 312195359 312195391
    0x705031009111c0b070503060a210212010507140408030f09120d020a060e030c060412030f050a0c0212030106090603020f09040e060f0604090302120706151203030f02040509 76
    0x4400d000b08603030b0b58040050311103401015600d00f20400606101c10855040241001040d03815202d141501d004107002880c0c0f00c42d06103000490840c0000800352000c401c0002e0b201a00580d42e0240c4007803412420314004111440d1400c00148095200854010742d4170060000380300f8075500005032911806086010b554400c2403200280034020406403007100d43c440d003a41d1800c51940400d410341058411f100900c020300d1240c0106480380904040344146030b009800080c0415148505d40105500500340003804441c020b10320740c180c2e00c0c00c842c6880d0307440d02e480319903811650420046404100e0035414a041d0750615800414031200c600c42d0342c00701038002c00d00d94240042c131030840d107001c0c000070000c00c0103441c1c03154040c0d10340000b2074004a0050441000130207a0400d401140909076041c2d002c1c10001c408000e403010290003280080c1c0710580d42c1e06100d020002e00c4900440540186074412203210340620b0010305841150350000420360041c00200200e440c2d02d084182c000407019105041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 312197859 1250 312196609 312196613
    0x918150518030c0a1205190c08090a060215010e010e150126100b0414060c0712051507031a0103020d110f2d071b03050304030b090c030705031009 64
    0x8441c100303140e030320601e000010b04210310740310004444400b140301e080002202d05c00c0307243c00d46041c0291056400b40c42c0d0300d1202c480600d48500e48e0303400800d1150550310304002410020070b5040702540c01410240c0d108184000210300100c9a0b40d0040000603281d05041d030400319a00e54024001c3c0a400c1c965a01d05c0b0790b040c00717030b001d00030320a10741d20b85d41c0300744815110f0a42c1100e19036106076000b19050782e40d00f101292040000080350142c440c031018603c5460b950340180724841e0b10100304240c580c01000e038080b40498409550481050080c0010614100c9020101458003406850b400030300d0f14003641142d0100c0e010641128004007400d0050300c900100c95440c3c00780c68942d102085001000806464420340300024002e500508101100d8084401488444a880c5075038643c200c04010703c0f0b840f0000e4810458900c14107269215800d900ba40da40c4c03507503d0342d002034200b210320040c100b0401140c054104242018010700310001c0141900d440042615451140f044100b03481d03c4400c0001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 312199109 1250 312197859 312197881
    0x1b14040b060a1b2906040c020304060e040209150301061e0c120203070b0f18030c0601120f0506090a1101030b01140d060512070603050601170c0703030603060f050109181505 76
    0x10031608941040340300420a00005840c2400c15049400d80d51414042505401e081c80380130301c7c020b5182c0080d882c04d03040020688005044e0000f003035015808002d20300c41d030b0711b82801ca051002403455241d03031294100b0101402c041c0c505840031a0007040c08010422141d48500d120400b181c100703261070741d4200842412070441c071801801800054041e400d00003003010071a41184192a8030880812096203404106e031688101e80411a999000d00010700120311200e1403403802c00d100d000840d6100046036110b60038220120b03002d070015001041c118081c0302c040c030f01c202d00b941400d00c0c0401050802000203051140c105a40041c5c2d0752010481c400140d0355540080003a00c401444183c1131810082010350303400762809a00d00084c1014085036031540159081c0c0d00300704007a041000540d5581c3c0451082da0820407086d403c09da02c03848000085062071141e000310400c0b24030f02050ba5030400c40e082c010389210004040f04c09540003140300100340384258048d22808142000b0035241c8494091113 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 312200359 1250 312199109 312199157
    0x6010311060c030c0c030c040908040510091e0f0b030903070b0408040807030c050312030906011232070609060e0d060b0306090f0c03070605190c1b14040b060a 70
    0x29000c2d202c00952031342014000a40150302000c00c404440b10603100d082448207884861340000d1000c00c003440107111a2a10351081100b00001e840c100d600f640d0340b404bc40f003044a410900301d29058412205104401c100d00c56100a030501168013817660900b0550a552441036020152124000101007802c002c4413408440061041408a441064a1b0f040c9508000c1071441010301c02d1080111170982d4084840550340300d0403054002c1c016036840c2000c0c0c00c95154881c54211081c0d01c007c07110603010042004bd0802d502e44104100c90750106114241d450664241c002030b0500104003010000c256000b1280320754000b06840f07000c8501c0396850034002400030480c1455050040c0010880f274114005100800042e1903422a010b8090300c80605488440314016a80010020031001c0e644e644400740741c2500c0c1c802480d101d20790b280583c440081100c188c409034030701d0a9941208000c0c00080030407000e441e1404071010024100b402002a40030710645d842d000a0004041460440703501d017496038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 312201609 1250 312200359 312200377
    0x10e0d0203011d010b0d0507060825080103140715050c0109170903061303080105010c050f0109080408161404090203190c09050c130b0f04050d0b040c0501110601031106 74
    0x911414005910031090380f5014920b400080d031034035222108a2612484040c031030740e004005080000c0c10000d049907003910003040c10350710210170010020040200b0740c11041114640d035030b40c113081d41913207000001c542c1128201e40d0140d000e00d1081c800d00f89100c0d182e4075050160f0030115035980386140c1d200d0140030503031006403126251300404c61034031481c90010700b8800c2c011020340f40e290341c801c038030304004442040c000342c00a1400e00052145500031007820404a00403400c44071442d545407026400d4581c0038101b02d03103040c008030b01005000b0003089110503442c0b004002040542c02c0001007400140c0070039905100d291035415100640d242400058072040118117a1a032811542c00c04506e03408280c40b51a070707182c0c50040050442c442103025907091402111110341058070f0810804003135004081a03480c2c2c008100b100140742d82d15040c20107842031041c201c50b412032030907040c05403030141d4541c0110b05110180c2e4001c0c0d444100460b02c0d605490b03020003080380343ea070000d01082c0680584090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 312202859 1250 312201609 312201611
    0xf0e0102070b1e0103051513050610050a08120d0f0b090705040e0604060506090405040203191b120807031107030b01090207060b0f132a091401051206010e0d020301 72
    0xc031906014a1a8042e440303030118540b000780029058462441d014801d12002d80107400c40380745030901c550b54041c10b6402c107803152000b031b1907000d0a40b140350502c01c0075038105010a50301941001603043c40b81c04100140480307009490b80fa00001c107080c00600c2480c00c8101815510034464101030002c0e030240b030310458090b26455042c80d083c14041c01c564898020319040b00740d0380c0001690752400303001e91000c0d900c0240c0b1250401c41450140400b400000d4030032030381801901425241c0001044611260f24040c010400074841201840c19007005e807034010030480000c400c107050104c0c5036032040350502640b524103440b400c90544e40e098140051074200901804003600009070145250b00030348120f600070b0b182003104500f428100200a846445603a0304040100e102c440414110b510240800c402e00c0c020413865181c54540c2c182300d0700c4890091006ca000007106110350900121207207000102070070140e1800c80c1465408810a030000e01050401070b406445030542d131129a00a0421a80500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 312204109 1250 312202859 312202867
    0x20411041202151e0d0605030d0e040b0d0b0718140a03030f030e0102030a0212060d23030d0c031407020c0d0809030109060c1e14040b0906280f080403020706030f0e0102 74
    0x6028040342e449812006880b03406c000d0049524507000c12000b109902ca902c3d503284d010915014080a80042441e51b40d000e580c0083c0030000c00c500a48441c4200302c04d44da242274101c841c040f0405500c201d40c0085451180129500c040c42c2c82d00b40070b10b4240c80d01414007188803458250120041d2020200101172540040148802c45400340c000c2c0000c03c01c80100c0300f076141e5661051040c4111140701c0134084001210014110740103054070106480321403000c0d246058030724021402036900585c1752400017981c44410403856405100800d811543c64405884800686030000740364012401c009050180005000180d90340d0942c00100c12a43c070240501079410030410152410080080f803824281c242e400c08444544a00c1c110048900c80d00e443c20b041601348003141c28260810114a50029010000401c545115585020320350101c00d440240d54000c080340204031601c28840017052101c648140400a500801c80c0401c0e1141c601d00012001d00b00d500c540041c010500c0d0414003540b0010b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 312205359 1250 312204109 312204157
    0xf18030304170a030906020105070e060904060806040b0406050c040b0f030717090706020607020304050114070201020a080708040929040c09050a0e010f300807021203030402041104120215 82
    0x4a2031900f801e000c0d450340b00010756142810b07400d8030400c481c0600001d00c0c40100e0303221071524401808039100e003c4c0000840e01c0d211400039113000c01c265000d86090030074004210030004207024450f803007001c84410600b09880c0056040380d50251480700040180f0103c0055a514490390302c0e88244070042e0040081410f140c40011b0300c510a6006c1c100c014011480043c040d180000103c804403201a0b5401140d035440e209034014580045104904500426210501203242c88001d000c040d4020745201c0c0e0f541d483e14202d2811510b00d00300e52500d06025001700c5524003006070604481c03010680c1c0210304080320720402c0b00c08841035040580d0202ca451008176080110f00306e0309050724502801c41079000d8075140240320f0300303e00702c60021800c10700c2240d42c0c9a9410008500242c0c6120344c1e4403d0501c02e01d9030000e6401001c04000c2e9801d9072000c02080306518207402004c04800070f200c0031500d05406c10a030b4080c1c0500300c03403029024015040e441242005c3c2d4208840400c04424850354200e0301b44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 312206609 1250 312205359 312205363
    0x50f0d0b0a090c02010605040b0f04021c021c0f060509040209091e0c0415031212020702062b0e2805010203090105010302030f01050c041208160501020417030f1803030417 75
    0x98040d0f0700540c40e00f40041a0b40c04c0c1440307000c06e500030051185525011701c0d000c001c0654042481301000039140c4659a0700f2001d140090148107401d110308100d918103114144044a0b40c10080511003400c100040046445050f6069042501501e000700e1301e6031500705131490540b1040526200c003060306440640c04002140e2061031105c2100d05100d40c403c243c0301111b140380240000381a074182d1a0401000302e00540144c4000501000c3c05410501990000f505ca83c00c00c07004640c21009103019200107807400003410011100e41c5408100d10450120165a21490568280341c0003940585007207005003881424141e041d4010300965585ca0320000c030394041c1c0400e201c201c0c068402d008910b03e020b0018054a48111040700c0050b04051401101001c03030581c001080c0e801490030031480c920002c0130041c207030100e8001c40000d641d50740f61401c00c0302450041d1a8888072030f08140010135140c0304800c112040303800c00501c0151202c6400707000a0440c403c0341c2c0410301500700042c40316002040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 312207859 1250 312206609 312206621
    0xa0e0904080405032406060c1203010f03030807031b03150e041202070602120a080c0d0c1806050a0503011a0f1810030902220f060801021b010903050f0d0b0a09 70
    0x94041d19104401100c25910040c80c3c50f0561601c178070740800103910360802a01070b090b00303900c41003182e18425121f40103407031542c400c1c1c10900b241500c0d21402d100f8507801002c61074114145240401a403030107803540e0050940c50702c000781c04044d2134900300001d10884540a4002e494101d030340600504282c0b9052400100c114005000342c01241c400040381400402c02d004d0488036000114a070052054040b220400c2c014040300c607002040c000001e150b14a032281d1905144507854008610031204010700020125a024208110307003008041e11040c0e01c501540e04581c3d2500c80101c0810394004040003078050003d030519444404140c4180909010300f8ad0314800e10265160002134003141c00803801e8030b68440001e5001521031410740b000c06c00303070166a0386070184403c2c002111030f0200e150348103480d1990310040c100d030740110384420700f618441e032410109141c1400800281046a0f00500035009454182c0004000071403a80c41c21a1140c010394540c3d00014038031030074151141118002020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 312209109 1250 312207859 312207869
    0xb041d03030610091e05280e0604060b03071d19030b0c0f1c06050108040f03050d0b04021603090e01060f050307020c0303030408040e09010b010504050d0606090903020f060901050f0c0a0e09040804 86
    0x8800315030740c003101000401e03540341f0f8a1550300c08141442101c01c241c070301c05050710750815a54040040c40302e900c0f40240d80100002d07130310882a44070080c164483c0240d03001c0894444d01c2400b11400f07692584910311022240d0000c45c0b25010350f280781d036001090054041407002d001c4009039500010600741e02e0070040c400d601400700300040d102e0004444401381160003c0c442d01c0d408030380c50040ba01960142400007940304c004a42002c450000c20182d800c042c880c400410907a8030f142c003c140e00100700c0c001400e10010100d03c15890808000d0811a40001c40014054000041000c0d180700b4844000142c01c0036044a6890a00746401d0f90f40d81c2c0580320780c00c4055211004a01d104074103004032019080b050b59240d080c41d00340010058441940740040301e126076914000141c840e03082c002c001c4a0350080c0c020340440040d441040b81840c8006200d07071032503490007040041c403003036001d03070381d0b80141c0e842c0c150070f4030713139030942c0d0103480d4140e01116003903001070b8500c10401001060790003401070720 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 312210359 1250 312209109 312209119
    0x806071706120a0819021e03090424090e0d0c0b1303090305010903170601030207050c09070e0d0c0311010801060f14070515150303040f0519180b041d03030610091e05 73
    0x9070ba0641c5a0301082d103c0d0103a00d00306c0e0403c101185403890260000200b00d5900e042f00450114854201c03100f4030420303403105d08515110601441140740602411b00300c6403103414030601e01c5c9102c0c0d8030341d508000d00174058580d00310b1101402c03050510039003505000e190b03ca030081003800000d0801824500a8107200902e035211480065010b51080c005d0740d02c05c50303000c00182030341007140c0100250344100030308a008002508010300300135a5120303480385041c1d00825402c4685411030801d000308048041943d414002c40000400441d41d0141c202c10741c85d603031441c0900300702d0707108622101c45100e82940a4110300c9007642205a022814802c10b000b01c9840b404c4000741c031000028035072a4099841503006000d5401d104218070306103500d0206107152501303101c03500c41d501c0305515605480500050210260707a0719240d401424a0302c03034040c8000d50301c101000c40d405000200c030b0340c2e07210080c1124010b903005403204d0045801550080301401421115000c3d4100c103000313100100c0f640d0310480d0710034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 312211609 1250 312210359 312210373
    0x1c0c0e0d11040c09082a0a09051902190302090607020607032007060203041e090501060504061101050f16020114090309130e0606120c060409060806071706120a081902 73
    0x580c012242c0004171000c0301c0c090003020700c0c64690303682c4080c20760b404101c040058008881c11a901c0c0c004c010003030000140002050308041030814554420040080d0b075007441008441e9429180e10204c0b00040700614002d0f076610914008141c1754020108025084200800c5010415410600c400c014070f0007a401140101c08800c40c0f65501c014511440b000350f0400c00c01070118854450411480710001305c111814960380f2018002120b00907400300d030020760042404d01c0103e90195000f02c20b84400703802802a418020101000711102400c07074000904406134004a00e8001e4001d003141c51170ac0345190103145020240c458882d40594600c42c0700340052005900200d402d48100401d1441c5400140000d07070342e5105103d40e032840280262024440c040c400102951400020300180c4008070b00443c01380d1500d003100d80b40c080c01038041024000b45179050700690350310400d00355100030101c520b604240c021103038141c1401c20806014114810004100d140d145040b8020b840000055007100d40b8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 312212859 1250 312211609 312211631
    0x6090a05042012030c0708060a020a0f030b0f0307060807030c03021603080603070801060f031406131502090409082503120c120c120f021c0c0e0d1104 66
    0x212001150020b00b0042020703030807081001d40d1549404410310103482101c1840b03035054007600d15000954150344680c0402c20a000913a018080c064101d103141d40c0035418084240310140014a181c2c402e001096507900c10000107641d0210300d035500c0d10700601614010703615801e0041c42c820301160b140c808603082042c05540644203200311000ca044141c065902007441d5981142d41010181c20154184070315440810320040a00c034560003080c40c140344080039880d43c98004400080100c007100c0701e4000c0300402207105100b0424048065000700011500001d02c0400c0000307000307005015401510380040305040000c010020700e483c811030104180c100d2103103202c0703d10b21460341d40e0090004424a43c0030f10122020b8002c00034051150400d0007e0b25054554501107501d8210001c00003410210b400340c40301050710620b444c00c802070340f041d403a0403008080e443e0012034032010512030300c0d03544018000180c0b0418001d0003e4100130f0190034851020f05001d8010f0003210101c9119a02d00251528 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 312214109 1250 312212859 312212861
    0x80f0a0c0212390f030114090604050706030e0c040b2803060f09080d050a0906051306060b0a051b07050901030c030c0f060e010c0f05330709030b0714070b06090a 71
    0x30100c3c0c1d2402c41c0c0c00304590950501841000c0040100e405640710038600a082024404a0f0b10404800b402800c0740c0c0383c207050203494001c1a40c050f2060610300109e2002e0341c10042000071105900f03440c04101d03520044045050001204200405c940c81d50f40708410200980030319034100d901842003403180704801840d100407030f0003100c801481d42000708a42021805c0c55000a9808119a980002d8001c0280ca80e2015680101e40302d942d2003030710191840070000301d0300c100c50180034504c4400d420800350340720240441c4580348400030070003900010311083e072600b002154044e03e005484003606503580c1c82d040702000b826001c11600040304050100b0781403207002c00d80e0211342c0a80d607001c4a10b01c4c4c410054400c40c290602c00c2d1141981c503914000031550401070108065114504840b1030303422a440c00540613002a40f08800c8640e103418071002e160f01109080c2601c0c2c001c00c0949103034480380000e40306904446881e148440c000b04290082c0084000014810001524021071540e240b5030b0030300c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 312215359 1250 312214109 312214183
    0x5091323091501080c01090608070e060a03020c0f0106080721050706020f0f06090606010c0602120702101a03100e1e0307031209020901090506030c04020309010522080f0a0c0212 78
    0x5800200350321f07810040c0754803550300d03180c100380c0b00d08003d01125525408200c50780d00c4074a082c00460f40004503440740b4803003000041090b404040080150313a00784050280c8a203114419110106108282c602e000c0824100784806107a01c502150f01d060744d20400030b9158644540c500c0070360f004641da10035607900082240d6210305035980c064000c41e550a40152030b6101180402c1e5070240e401d0020390642280b001c0d990303000b4042c907001005a481480b02103025551076805082d54006115802c1100c3d440000351101180c010450129050403411105850190071443c0345441440b1400e0820780408080002c1038a41d009036101241406502d09101c00c0c0e4800d404029000b2113440010001d01400b40c2c0255000100181643d41c0c0d500b0f0000042c0036a04165641100e90355104103200d90300700b04205c840c40b40780007400400d201e07840d243c0340e4200701d02502642c0352040700009400504288506010744000e94000d21043c4a8001c0308615980c4042170449111085401150300e801e2032640103600c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 312216609 1250 312215359 312215383
    0x50306070813060b040903030f180b0c0c030c060118152114070e091009031b0204060308030708160201020301080703080903030d2301060509132309150108 68
    0x1c408a4440400c03140c2d000603100402d40d14155142e012190550f0b40c4c2c050310803882e000c0d9a02151281c0072504c400215404010a901410003164001c00000c0d40d41403480d52011500c484e2980300c0160580c218210320581c0016500d50140b08008034401c8070046c0b203500e40e514101c40401003201d02c0b84003566004128094512040480d01d0041042031003006c48407052442455102d609440c1c25559624210617500300c4800c1170300c0082081541c0d0020007611038504c48200040c401c00b41e5584014180e10410301816640043c0c91858a00b952070759000301c1c006550159105a91340340024006240c40000e44800c3d070401c000040b40c4e0082481402501d059598010150a032245140c1e6004c00c035512901c00b00d9010300050008482e00009441080916a01c0140c103584144410060100340390058000c001889014450b402042c0c40c0d241c1211210b5082c1c0340001010380c074215011520031200104041a582c1c0c8400304940c51001003a003000818103001031107410f0b621210081e07244d955007820 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 312217859 1250 312216609 312216617
    0x6060f151d0906040f020d0c0216030b01030305070507080a080c15070503130c080a060207050708060c0322052a060403150c0c1b050f01050c0a15150f0f05030607 71
    0x1c41400b8980084596040b460080001500e12840041a020b03608440c00318058159920508800c858040c0840d08e05043e504001800722420342e59007184510042c0005804c008010400c07404000c0200b154002408140088445d507259900d48242c0c030340d004414440c0140260b05007501c80c18130781c40560b4054400b680b607140c1540d0701c200603400300900403030f0155102c1202400c0029158014400c81078036500030180543d84807034504085113805001e40c415040b40d03004a04004005040700103a03508800300000090b144080f00c0004810108203200c05021801046009203076007036071100581c10b04a00c1200100801c0c050780412510b4065488058400d5007504a19081c0071026800540c0c20045420b00042c0b0400d56290640c0b5401c1d40e901120407028a0041401245400502c00c4c01a00302481c00601d4003011100f4107840d04115640140345800d513200b403482e0900203401012042003540e071002c2c0181c1c1d0350103004400140f40d10506055110105c0041200d040115600344501802c1d11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 312219109 1250 312217859 312217907
    0x703080a02090d1b0503120307050403060c052203020a090c023a0809010510080d0e03070b1612020f06040b091f140603012f0706060f15 60
    0x30190000c1c1d0b11041405500c4a051000540041c00b4a20030a5554072142c9081601d6410719080c1840c100300501d00302081d0f0000e0080100d490b501c042182c00f81c90744a100410b00c052101d409854a003e1490960340c00000440503040c56010100408204c900071901200b5103a81c1d0880340c000c5a040044120041c0c12400143c0d01101c181404c181200c440c13411401208400e41801800c03c11210308440001080c4c0f07001d00c400b501e001d0180340c0e00300500007085a0002e1070450030b5590740740507104082c14840c841c211030045640500481c0000d080c6030b00b45503a40c855074640321070007003106401144c00301040c070343d6a51413520000d01840c11041407030042130180c0f00c0391200008000003d00d05900c1307204041100c106840b182d0315104400a2000c00450b16108040d0f0030f400c2d580307000f0000350107a1b00d082c0070180042441c80a68044a14031142e01c542c0c031081661081c858403600c9400307403469080500000c0e8584001091100301da00d4241c051340305d904980800c4542400500180c50381000c411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 312220359 1250 312219109 312219121
    0x13030809030c0301110a030506041a131d030904060905040816080d0216030225060f02010902061801090b0c030a03050910050f07020d0c12032003040602030615070308 73
    0x4401403545020003802ca80c0b88020560000e42900c00400b040203015502060000125825000d4a504103404590900c6051103800359405e82e401c2600b25980710307400030b6070003100c40350841d400f41045128084a0328000d0807002040381c3c0d41c0d030081299502841c94040c00003810306040c80740358042d030b40c050141ca18168020919503210340302102c007a01e07951b104002d2050700c00a984002c2c0102d25444100c2014503c5a0401a04240c012808034040f52484520100812a100c1c525401e4070314a0904200b04a00f40307070120700611250b000250007035000100c040d45800190031604c0c09485c01d0780c17800705858407100e14030800e006100700316401e80d0050048142c0c82c0d0183c0c04c100d034001c80e10b0044503203170080280c0c90419541c0070b43d0302042c944001014040d01c29814400080080840e040160744403c15607101151456007001c00410907940340341a01480d007107501c44d844200b002c00e170708948906150804a000354400d4808612a200101c000c2100042c148160f40c12543c2680711420240d641c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 312221609 1250 312220359 312220373
    0x3308060c0a02031201030308040623071d03100204090e12090f0114070b060301061d04110105041a04051003140f15030a030921210903170306010e04021303 68
    0x1072404019030109102d180b040c048803004007802035000c6e0356001c03805e0420f400d050080342d140f40840d6841ca00340391a4810b13007041141c5c500c2e402c100949029424601c410881d514074a00300b4403503580c10301400550220010958000e0400d65801100070032140ca02d01018a030356141e542e0384e07001c030544140000b60f010b181000f07440c2c0d03080b40306042c660b02c191001e024410041c0d004600c200c3d400003402c000c1c441d00c0c0c14248542c801801500e225070101c00c0103403000c0043c0110040008110480d50340c02070040f80d2184058400511886010a248060743c0c2860f02198006000705401030002c942d048040340d119010301c1d1542c02030303149550882d4a881d4508216410700800030f88412445641e140100d490820030020360900988e6400d800c203040020705440807800c0f281000c148450f201048000c5502c0300c04584165402940b105441002036000313940c66403a45e4400362900c0c81031782c0c0600c024810b420040d4400c0400341d944000c0340c42c8210400049010306240100103c4d8500030610009042e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 312222859 1250 312221609 312221617
    0xd1e060326130603230601211b0f020c060f0a0f02070f09020702030105010e22030c330e03030705090a050a03030216090b06070b07123308060c 63
    0x9116900c0345003000c400742c9880d8461807a400500002d030317038400000d6802940400700400401540d180141400e0660000704001c4448400c141e45c2c400c1501d4100e5000d0342030b4800414201c0791208030005d0384070400054411505d04d048400980034050f10386030f107071601ca000c40340094600681503051180760102150300b442d40c3c2c1c0c54102503100d84680469007020007245d00340289074044015070388900303d00c141801d5460603031002480154620601804c01003507081907884091014500b140c0c00c40700e0404641b03c1c441c45101629450700514400c11110000038004001c1010320800422682d1070039058080702c003d03d0001c05990028800314028620420007070020b584010850004c0540b40c00004441c41d8050740120007590001c18030003078280c1c6840e4005c00a0420310010001400303c44027140d03182c0f2820744020800341c1c001000600490055032900c40c2992058410454400b801003500c6402c955811038601111300441c2c00c0d404100c4881c089070a8031643c50107002e040c0c441826040702900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 312224109 1250 312222859 312222923
    0x80a030b03100f060e04020a05010302070f14070f0605090901142205010801060501020307120c2f0910062307080d05010f09050915040204060b0d1e0603 67
    0x9100c00d4114030680e81084018181c160020001031106007001507041154040e52002c070142450000300809a903c1c60741910880341c081c01e01580e551120f140041e2040c140040007032088844140c00e400c1c0341ca00142c01400d9580030130300e0040d0252200825103480c0641c5185031341c01406c09006210030b19801c3c0c00801c04034405403c1c00500c000380d081605440d010f02d40d00b403800701d030f0b0b890040111074024003510004140a00244d4038141c0c6a032074500036480d40c20000e205000c03a03c10f01c0400c2018800d054007912070780320780c0283c00b0000d10300c04001c40340861200a104a01d8a0302181c001c0b1a002d80f40740c100c40c6903403500f800c0000c8500c030004001890010058640000307003c41c0c40421002e03001003908400b130080019442d030402230702560003071a5401c01542c15140808001c1044400a028a59003140085a075559501d600c0042c2c0a821160404101c0711400b040b40d1018034000e40003070504096000802d9034150150014404481a40c13002038007070300b00e1a00d11440f900d801c0e240704401c45 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 312225359 1250 312224109 312224111
    0x806101211060f0a02011b1e0509030c040908030603100b030a0b0a0e030304290c040e091e15011205070e191505240a03020c070302100806150304030c080a03 69
    0x381480480d20a030350440c0c44110b005d030f5111b4840d4604490210401c80140703a480c01c00c0d036041403040702a924803002d5410950b050007800070300104669000c01201e8140480104207000340100f91a282c80603800c02d40b038590003841410781142074424240540c8410640141c000d2000f40006c0d2224064144080c0c4a5070703405a0350030100e0364416050008511480c0108110082d00120a0703d850003c8046000b15136032000701401d000440131400202d4040714000b0b801c41c900c0b5115404050b003003222209900c0d150b80034104049070701d00008103034a400da0100e050307252010303a682c1c04030000b60030004d200102160048101881442071003031b81170390071418006080c142303a00200c0704101240c1c45034411401001440400300914035100458443c3c0d1b1074007400800340d0308201014843d450051040d10001c1c15004070380c0590445080200301c008540003490681005440701d0041c11064095455500400308101c102c110024500308480c0945d0f4955038000150095448440709904100c41c08e0b0205 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 312226609 1250 312225359 312225367
    0x40321020f03010e0603060a1109010c0213050a06091802090403030222080a170a08010b0901030f140405010605030f0a03030b06040e0901140a061805041e050304080610121106 77
    0x2252400081c43c040d010101100ca5541015801c251900200404081455003040600902044160b0039210288020b003030900c10340c0390034800200058005000103200030310f40820414440d0880d0004000c807442ca40c0c00300820381c610b000f0060580301049001e5000043c1c0c00104002a10a6005040801c0c1d280d10180039000006155110b0503e990f01044c0e20781d029590510601c070210341d2000401c0340303070b64500e450224003c5c8042d21910052086015041d400314903441540d0294010701a02c0302025410441070b4a4440c00d200702d00010f490a460540c42c0c800003080d42e0800054203c4440048002010890f400340c0c0c0803006001c10503a00f540010f020310000524071020181b00740110700c4180041030100720408403020b541c100a2074010f02504180d410400d0320107412030203000342506000030420740c1e12800c20060300d90a40d0301002980c03401c0440001440710100142003a20a400c003990804e403034030204038101e0125405020b58020700c15460702c0c002100000710070700c408800b80a913414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 312227859 1250 312226609 312226627
    0x30e0c032505030d0c0302011103010522020c01060306060e010504151404090b0703020703140f1605012c0610141e091906050303160b1803040f1d04032102 68
    0xa1213550a0108045103070340c201a07040580a028040d0132900801a0071704540c075020001c0d003100766495081e141c0c8440242c00104907101c0f81c0403280d01025a2009100d820764034948100281054405c034403501186100100700e0707103000d01441045540b03280040545130304060307000a040b0855481542e00c180e03100c2c1510005958018030324410900c5031030040e11600a41409000c8480c400f1041ea0f10b08070400083c4900380184003a0b940c0c81500180607101c1c0d601d14540300e801000515603500c01d600988650030f0203040d5103862042c8405040381562141d44a6000b914020340090013400ca14551040c01c00c091400d2103d480314681c1069410000d41107074150116804020a80e840b451040c0c1c1c00801000e030a00c240201c20062200364021031400001ca4481100c104480314002c04c0c1c0c100705404505041c0208030703136a600c01444000c0d0b03075582d99a008048207802180c8a00031a45210038008000d1001ca00d14041c42650951510145200208400076409800d94184000c140c7d0030300120038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 312229109 1250 312227859 312227863
    0xa18030b0a06050103150308030a02090a0b03041101110d0c0f030c06110d060e191d060106120501120b01060810080609101503080403240c03090201030e0c03250503 72
    0x2016000e1140d000030b590341010001415514540c2d8242403a0303404840410003c0e44410031a94480005c641c010380310386c2a4000900708180590203440e072148040306000512205001c1040001c0090301d5030030040b6920203030151201c0c0c140900102140400c0380000c0401e01200701c0c864014880d20700601c0452107582c8160480c0c0542d0640e0192440100303411940c04203d200e108003600042240b4907881c134000c8045014403100c0100080f00c140c03506c03846141885448600203c0d010380c2ca003511090368507440010311440100218001d01410301c0300004110f01d00c0321560b80020b401440444050f030030000240c0b004a1302500041003858030740000202400140555030040020002920030255401695010f03103038020207a2007004404102007002840c9041200c00b00e0f0b6200c0d0780495044810151807000c010780e200340e6290f403030612001d2901c669145c1e0000f011503100f41c07130400003c01c0c20b500450b0b403107035624072103501984200c0c0f0655014076040440d80b075001c94610040c00703a40e26140403174 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 312230215 1106 312229109 312229111
    0x6010c05031e1309020306040b060703020a030c140d0509040509030a021c020c0a03030e120309300a0c06080105091608070c1b06110607050a18030b 65
    0x202e4490030400c2e90030100c042458030b020941c1d500450300103588116042d0384074030315045000011f8a48882034a41964066004080385000d680d4207440e0402102801d0b10240c4142c060200344c44402c1000200202d516524183c4481e030800a004c2614006054035140e5007041c131440c21003580c000f9140342c030740b40154800c40712103141c4034090342014002c2004a400c042500d00120a150300704201c80c02e202c0003230b20b5071185903d0311030507544c8074010000c0065010f0321081c900c000700104a02d0004410200f401c80c7d500c00c00039846654900a141030084a410401c0c5000304005900110408d005040694242020746031104600390f00c17074811080c843c01e00010a02107141c1030310508401c107c181d40941c621000000c2c11011600072000e900c20f0200042682e100909185000b10361240103400f580c40c0c0d08d0034869444004e40d0012001000c000c01c109140000202040b102c4070300b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 312050359 312230215 := by
  have h0 := BRFrame.cov_init 312050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 312050359 ≤ n) (h2 : n < 312230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
