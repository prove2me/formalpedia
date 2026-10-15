-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5203
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:05:05.009243+00:00
-- url     : https://prove2.me/submissions/786c7bd4-34fe-4cbe-971f-2c5528fec443

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 935611510 ≤ n < 935791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 935612760 1250 935611510 935611591
    0x9010909061415090603040c140109061e110d051c020306060f0a022a010e190b030606040e0f0f152107030611070308011e140a0e 57
    0x2803412109215402c01c5204003409110624030342d410001c120000c0740d00c4450300802e02074a900300707070800340c0d072039a10b50060301d0150002c90544000ca41c0038421280c104c50b5596102070848145252144112103505400828481800b60b000e500c120207204140690382070f943c5060b11045800151200b0002d99903000c00300303e10400074041951900012110094980b01406130b0310740c0c5281040346000258040041d025a041d8002e4228480a0741e000c01409426079a58421081802c02c00c45140485282c1da00280300682c0708100f405a114041d550000c0003c1445081a56403520b100b2602d00403949010b00e03086000401c0070b14891950350640001c0c0b5140b00c50704000b410000314500380d016a2203805011a207006001c1c1400f0200300c03180141d503001c00306200018950711914140c0d04507604c104c0104510600220b80c0140901804034031510700304444890a00c1c1c110007164508880d04080c0e0040c030641404240d4102a1480706d0050701e1040543d01034030f4160704048101c60510b101ca1441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 935614010 1250 935612760 935612771
    0x9020a0b0a090b0f0f03060d08030f0a050117060a09020a080d02100c0e0612060f030f01140a1517011103090c0330030903160311010c0305070504091d1209010909 71
    0xc2d003031030805880685c440d900e034a50341d070f1b00da003000a11236500b900c01c0282500000410800c80c01c3e08411100c1c05209000000e0081e84d898000700d0780040384003180c0040c50f40c44003001400310300c0c040d08001c030b4150020705441c100e0b40c0c80d00c0c01681030150883c0000d000d640031008140c0214854400c81c0e540003203e140c4410122001d9000810510502081c2c40c0c4000340320021070195612000000351a10009044034038040c07494000034007a00c0c000c10700c0c26000200078001986583c1c5401030006000c0c2103e245100300b030074020014040812141c04c2409507507140081c7d03801c0f400d200011030141c030660000f8049660f4180c20140b138605407100c409070040444510300304807001c40d0242c4800c02605081b99813280e848280183c80c500a1150100480c8014040c41e0141a00180001c800000800080c004414443d10035402d0720410744000d00005e6080004205040c50395001c1c00010407944e5002c0e074410390752030300c06203442080e1150444c04400041c8815a543c5c0140e080001454420420b009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 935615260 1250 935614010 935614027
    0x31e130614180d140307110304080706080121020d05010e010501090603150c02070b1e0a17010e0106020c0f0d0506070e03070602070803190c051515030a050d1209020a0b0a090b 77
    0xc40001484c2d4004802c00100103e903c0728011400300c11680700b03030f004407502c85680d40a0640e480f185440b400c4041054100042020344000104075111100303200c0c07503842004a58284019003880d40400e036100d5690300a0084807007820b000b464000c2415100c007081150450074900345440c02c1007a05014035240c410403d14998010a000045030001c0f07100d130340c4552201c410549001045484001d01f42d0000035103006207900590300720b240c60400309017648141c0c3c881c9004c044641082c003a03074000da4008225410945010a091001f00402500d148034104403580d03078600e08032056640701c000c114020b401b8021402e04100358001441c43d48000c1100e186044000c90301c078403602c0c0202c0008031a04101c02d28060141640701d020340e034008121401c03110400c2c5040501001995a40c0a65450b036401802034940010313907003645508800a045030b81c41c01d150130f58504c411014070310101512a1138540c05a0f661003c001d00a028924038603684080c243c0c80100703608126080100710540a020006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 935616510 1250 935615260 935615267
    0x10c02070302010305190207060203070305011211040c050f0d05010603112a030c06010b0901120c0e19050d0503030a060909050d050a020313080c0f06031e130614180d 73
    0xc0c212602803c0004d1261150080a02802100109411481c0c00000e5100406c020341d401103100e40c900d0b542c01c11040e600d62070916240e910a20b8098040c1d0b8407480402c103c0d00d41a400a00309219900342545400d807440024180c94010100c3c0c80d5605549100410500b501409048801001a00d8240c503180c00d0145c02400b10320001d01c6072402041c5081ca14001000810031120030703e00e21004c898045d80d50303410402c2d850b88400703035090000c1c1003d01c081083c04028060f140c02c82089032156154810141d00740041c3e9103004032000400d2201e501d0014068550491840c0c5c010301440285980c0c1c40c21285c0306041e0b5915a0189107500d00e4880b01001040380070130b03160390000c0f4074a00241d41d00e44d10b4001b2465809103d800201190000c078001886031000140d40912900603242e810304000220100300303940c00101c1e44810072042c540111f034a11007d50300e02680c00645203000d900c6220868640d00c0841366500030400420b440c540510148101500c3c1c0401c88035003100c000c20035803200c4034004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 935617760 1250 935616510 935616523
    0x90603031805090907120821011d0f0c160212151003020108190e01061214010b03030406030e0a171c0912080402033a08060d1e080c070905010503010c02 67
    0x8428444800d01c04003000001c0d401c450703021001503450301d0061110000f03454410780a01c2400600400281c1803103600b039000710700c0c45c42458180c42080881e60f404014038a030754001425407000301d030070b41d80c40d50053f1b6442e800000c040303080c0c2d07004280503035446441403c8c180f0080c005a004c040040000c200503070348405041e5109417403032b103141d000c0d000d001e10441c003503c119003280c800c03075003041c2022a103904c49814001095000d640074546120980c1400c0d17003210260525150141c000304001d101c200e00a8001d1840d0b8400641150303241c1010b134071541e0300306541c0040c10404480000e901002e291420f14995001c842000082040821596948400d0031a0221800502140300001815540c0038080402c08d04102c201c9001e84a50011044502995407108a051110090356a4020a115903001c81c0b0464010700012a042c0c6507031a030381f400184c2c8142d03000303501540c0c0900380c0000d04420003408101d0396250040c081242801180710680700140c0000d4040e80c580442c4035840707a400600d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 935619010 1250 935617760 935617769
    0x90607110718110409020301030501020d23040b0711030d050726040b13080a0e032808070c08030c0c0a0b181009090c05030a0c080601021015090603031805090907 71
    0x90510141e24400f03600340503584c07182403030740d1012000200348007042d00102880021440c0401031540140c80b020070860a848210301c50311180400103000820400741d460b0071000a0a00c0140300c90a090320030300c1c4d6071011501140d00f40e210424000c45c15000401001c1401d510100e07600c003040700e42d2030040d84140040006e0010101072012030030407500f0300c1c40c1010940d001000740303642d0300044601801403910103189038080d00c1401503038040135211403280c4120460f640724449030381455841e224200c2c0c000754000d0380e0000d5101000684864200700a040c0800944d02404161884404000128036a80d008200c20081080701031100c186d02c4e060450f03c448122150740035550350f004c0032201c80a258202c50391103880d003101502e285801c040518800c040c504810b1080e130018500031a5440401c0e10450701607030020507481c0e640701060308150030f080f044628003400070350340d19503c1003503a03a1980280c001c20070351120b82044129800c90724000d004161441c0b4028101925069545d5403140714 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 935620260 1250 935619010 935619059
    0x80d0f030903090e0a0b09151503040606080114090115050f01050703090e0709030c0f1a071704030c181a060f070206040801060806090a08120705120906071107 70
    0x74150405028111400141807500b103101d62a04d4032180710030060501d041301c2441600304000280325100c00544d00405c004e005080c14001144002c1c10340c0d46604080c0040304c0c100d4981002044c4408244134000740280250032181c0c0d00d0501c11492400c440d005103211003c0c00d40804103019a8a17103010380040d041c030a281107540c60381e6034102180c0800c1c0c036400c2051a91400b10600c0a52079110300002d007507900440301c1d40c03030703107a900d03540b03036554600510500d000088400014102900da80010b014007900a400d9200705123000030704507501d03602c150001c9503509405c210903c1062803a24410001a4000d00e04018210002042c012403a007100e880b507101c1c860009a02c4141c91812041e18941940030f4513480d1100e85640540d40a081c884c040c2d0b2085115280c0010700000c400544000343c990001e418500d002c221400101107410004e01c0801030140c01c10002c40e402c0e4191410764890b100740310107030425040280c2c00600521203900402c291b41d00804080c0401d0f081c02074288070328081480d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 935621510 1250 935620260 935620271
    0x11a0904140106090c0f021c0309050f070b03070305060f03060f150904050c101403010302042012010602070501020c0306150f060c010212010603060305100b01180603090c080d0f03 79
    0x98004140c0c81c1014101d501c41d403c0210004a6003a03580160030144840c0e00c50074041800c1100407aa00c102c0d11404212a4400d001400b640398060341c0100e09090003078055521a443c190503040c07034000a40d00c245964000001041f01d0554980701d2207801c207504840c011581c2c0c50380c50000340c0d41d080250004d40c50941c94030111380d0103003400300f80c00074082014040340d400b4036190500f02c2c0c07142980c41566029011811102c1190f501c11052002e02e00c01400040c0d046074256000d0000602031501c8a02d0040e08040c035481c400500040070301041c900c0c0c03a49800c000d41c14224001d00b0550f00d6408541954003219841030207540101d40706a005074500c0c40100c508842e1000191403003ea0341da486c0d084070000030507098000f810340003011411343c031040d90710031a41e03652000c0381210010322000d40150031600981c150803401c1e030080402c0000c140340071035104c4c0c02c55050540c1c40d8080e034040800310381d640b8560380400c030540c50003034024010740c400b408403400c2406014001c0c060640e103400030142d0f0b41e03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 935622760 1250 935621510 935621513
    0x90f12061a0d0309030501050c0309030a03020d02070b0c07060c050c150a110f040608060306040c05040b01030b06160c050907231e0901230a0f140c03030612011a0904 73
    0x8000100450070007818a002d204160070050468042e40c0019503882d428100021224045403040728003904510009503d4505840011002900209400324680340c0070171410700800d104482490252071800c1ca0745540e600145401002c4034580c4201d002031001c14000402c00c2d8101084800c450070a80c44900d07003594850349020014842c00490700c00421001ca640900c2006903070260090710380700e4440c0045500c814017019994203007210010001c4c5c150010070f12150900c0c1c1c01c02135112406040104081d08213000140072600041207080111880f0402c40c0140000a021800204005c0d14800c180e818903600041428000808660403540703180182001c0109481c120341290f0703400c0101c00c10000c00c4545401450f48181c032000c0c006407408101200031122085d901450203100500c00b8641104d501c010b42d0482c2445000b1014000d4520a01c100d136503440d0001d120700c256038000b5541d2884c12800308652180105107003050f40c0e1606150080450388154840b10300b0000322243c0c01d15542c0c9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 935624010 1250 935622760 935622791
    0xf09010e040902031e031e130f0b030c0f12041506091103180a1b03120e010906080601030f151a1e1803030703090806010518060f1207030b0601090f1206 67
    0x2140b60724440d1f0018045110103004200340909a4849000f900c111140d6131841c0c41892070703005008007000ea14040001c1410000d0040c002d00301405c003107842030b08024000001007031100c400c40e0140e47d00c00ba1070301c155a0058151207401c000d0103280030100300d9159240f403140b1031800010a14401c1c6656034048502c403410401203807102030340c00a1110380754041d00a0580c000f140b580300c00c0702d8100c0d5000c00c242c07181e40282d420222011041e51821003403442c0403800c40301c000c0050b0a040c14503544500300c050302c622500601020100c072100b9083c0d50362030b2580068040d640c28207900201001030107410b0450500d21040380b107200032403109079200c00e480e06581d40070304503041510340e161000081c40c40815412101001c122803598003a554543e070390f0310900c03524035030166045c411291341c180014070311300e0161412034081001a0103100081400020f441c900b00c440c0d00b00b52213142d825020001d042d03038004506d502505910319410041480c02d040d0035140d2820120042c003403601d54048039001e511 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 935625260 1250 935624010 935624017
    0x31306060f03110f12060609042d050c0604031a040512190e01020303151504080303190f0c050d0b2404030311011503020904080403080f09010e040902031e03 69
    0x94031003614242e900d15202e0460088610030310300031550b9011607282441c0c030586580f000c2601d00c01401440c2d48040c20044134001c0104104c4801c80308a5608000902015407a041413070542c80d076082c1c031403c0382030907403402440100da10300c1081c0401043c00007807a100c8502c0c50860501c4c2c1e01101c151204c2c0380c100c2c00c040c00040410910240814600550b144190000710781c80d485898030302036901d00703100482c0c0300e02c0110744910000c800030072800120308025141141c0715a5020045050540700d040b04d50550380185c40303110042943c581e444101c1c40d60f03445008d5001001700d80c104036030880d510015103903029801c40c4100440d60f81c100390581d9100d608510b5690520400303003584001034514006120342050100b5130019402641c202070034041446000c403401c42c01449401903528590810450303101c010421180400f06210020004920001501e29130300082029034545011000052081400e06100e9215501b001c09960140e20b001c0340c00101e441d150b1106842e11000140b54615512 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 935626510 1250 935625260 935625269
    0x40206040513180809010806030105070e0d0201091a090910060801060e0f0a0e090d05070b0117100203090a020f030d0e040b0102010b0a14041d0d050a09230108090f0303130606 77
    0x104100c480f0421000700001c211a071003d07280c62540362149014182200c80031100f0781f001c01d000c10384800b0640340220f00c1340180c610501d454030085071900041c6850307843d0303110b22040d2644085002003040c548210034541c030540496114845900c0d040e0001c00041040c0300f0101440f5509400000544451450500290380a0004070940350344052a240e6454110f901e0000c0d40545d401a100541c8240110b0348250b41210b00002141d090182d800c62010507840d4094142c0301f4920100800380c00c2c0d0020703610a0b403441c80a041c0f04202401800140441180c11612170341003031001c5100c0071380150b400d41c0350b220146d800090310390000e0700503801800f500140a50060354040005012000d400d901015041c0031355045c03110322104120384aa83c0c020350009103c80d000341803402e0241c3c0c403840161040001601d0056242642c80c48122408212403048245080140342a0700313503540c00c240d03107039007214009008003280022149081e071203010142001e400d0726140f4040c0001d12aaa070080400380 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 935627760 1250 935626510 935626541
    0x1911060328021608030916080703020f2e2007081c0210091a0403080901050603030301080c0f0a0e0112060e030307080a0905100e010b01021005040206040513 69
    0x81c104142103403070340c0d00c41e04403a6070446000050048800d019000340c41d0b004000c102d00c9003000b08980c0d510019030300028a01011442521350400c1381c0c14013400440300070f0081c0710140c00d000782140140400d09031100015070141351859200141b021078140121405c4052800552a400c0c100d03030200d8081113011f0055101e0285103000c05020031010445004640100080f5529440513803060a000c404000182c4d016070400f000040c0e03441c203950005251503100d80e01c281d51140014507220a429001c0e50b0a500042030361081120038030342445003070740101d4114029825980b4010120b9590f9a200d070101d4000c00c0d4028103849a9100c50050002403d519125486e580d13848065014003141d80140c1514840c0c1080d40e09100c010012080740d0003460186e4510301c1d01d80d80e0900300307000340070f000204841520070403800b400c6120301032040101500c0c0d60300001c5030b00000603000914140354500402c40843c03a05043c8030050b03407400c04490869800b6100303a00c40e503458221030b038001c054420020920 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 935629010 1250 935627760 935627767
    0x51302090109150312020f1c200a020402120411010903020306220503030a270b1b0915040515030114041508070b0a080108031615020c150f09060405191106 68
    0x21941c000c28801d189940000489900c07c1c4c000a50010000e0746012340703000301e6420a003010414100c0b0340415215800c100846190382100d034007140484c0d012500b01d402911006080c00204140b045001001031002d03c0c1c071015481c110b80000e51100009480550160b502201025000d88642d44c82c0c11a0707030b002410b13251a0302c0e1510001c40904509801003a918540356982d0b90000072a5292454070381d08403086121980d50f00f0b560b01680e00740d06090101c0310105005681d440d540d2146400d0700340802869040d1250b2818046c442d00c2c400d0b181340c1c17880691080c401070102c0324107007a00c0c81c00712504803400f1a10343c0c403440c442a007119240e002071004d800f5144000c6010026a002411003081c141d03200440b6a98800e042a200e009124202e80b02d03503410b44500c0301055078a4100064004203140c01440c0030b2283c061940b034200c51500f0012010380060030000b101a045007800d6000c1c042070094202072803d552820788912803121503007aa603126500e00000d202d03071040d01c1e440d45000681410f40c0e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 935630260 1250 935629010 935629043
    0x2030603160b0a0201240e0c1c0e0d0c1502070f05060c07110402040819080d0c0e030c010203090306280c030207021f02030904020c0f0703080408010513020901091503 73
    0x25581d028600c03c40141d801c3c50550240c0c8060f0f070380300310480701e4000038806045052a500003000720b0041c0128444420500140d40c0d901d0903881ca8050311600940001022a60165014101005010568140306050f1111004581c205ca081c2d23602c0c8864031001a50340c41070749425440400b2002d800750a81c410001000060702110b0014071030f2502441c0c1194180c1803100811080e40b03d180200705454110f2506102e0170607001c2d4024000074490309070130f800c2c039980f0700e4500201c4107008003820001c0d661214241c141e080a004d000f46280703081c40510303c1c20000b50082030741c403500900f03c01030018000900c94070002c51402e4404200c0503903e01486051480304004020303421400c026881085401c458140c040700c036680e5000d03120310a4001e9400d100400b41003000035044808c0100d160300450f126591428400d1280701e01035072040713800c0390315070703060031102030840b64000c0c064603265120f00601c1c405650740c1d00741d0a044031554000031600f00400880d0743c3c1c4118056000030001039400a42d00c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 935631510 1250 935630260 935630279
    0x4060306020f0c10050c070201032016020f0a03050606130e0d121d06070f090e10030309091a0607050a05100506040b0f06070f05120a08070306081f0203060316 70
    0x50b12001d000104d5144034024403a03981210005e0b030342a0002c9030100020401940a0303044491a0782402e0502982e0700030b1901c0c2100e540d800a1803a1011082d4041c00303104618040b0000100b00c2c4066441c200e0742d909682d109170b69004e020380f14900c41e0031407280c0e1044240180e003001645200140070303255018101440179000c0c8a810640c104c10900302014424100420080180e100c04103000400f01500c68a805407840c900c40418042013043c4004085180b404030402c0f03600442c00008200d4074a450750034014404101d94019400c183e082c10106a43d40b001c5035241d6150020071900150741724030714a081c070301d050b00d8508010914059098203803d401d0346684014803410045d202448202018020800d10310070301114694805420302020f000708000b08842885188107100300c42c08481441c1175079006401100c035010006110340104520541c0c0350050100400e140302c01002e486640542038961600480c00f000c83c966404000200c855504001c404c0c044110b07070451141e110786404144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 935632760 1250 935631510 935631517
    0xf080d060b18040b090703050a0f0509030a18061e1e08040c090c020a150b030604062405090a0e01110a020304140a0612090507091407030608030313080904060306020f 73
    0x941242d19044004100340c14280121501d000b0020202c541c182e40303202055001f420050103c0003004d035600d0b0b0b09801100c15115290080c10300034000c54981245e00300041c0400a83c143c2c0d080c401c18601c408001c4981c0018030000f072183d1489002c02e00b80c9100404490483d40102c241e05001c80c240c2004240617048422103000d5030040999a01c800d4139090200c05482004105400503032114540d03070003181030340c0c40840b01c040100c04041f0300e1a0006000a140a1003660141d505541da1442900d03d040020200c0d4083c4614480d0041000c0c40d10300059801d0000800e80b4680c00d41745d10003000c44000079403120b03444140f0107440c070391100000d8074001d6803074019018503840540c0c200c0c0108407d151a61100007254010340e070758404145444106406000b40140c1101d0521a840c404600080540102c10755641444501c0000f4501500000c05598440d404550642c20030804d0110041d81102800d090541200d00d4640c2c86c03081d00080f5000304002e5201408403440400d402c149614001c004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 935634010 1250 935632760 935632777
    0xc02010203090402030a051006020d091211030a2d080306132406031103130305130513231506070507051519030c02150703140c090117060901030f080d060b 68
    0x2504008c0b41c881070180c3c5e07920504003140700031848516081040604000300c40244a200300c117001c41910f00f040c0824500528180115268481d0318909040032070308513400182809c10484094130403046840740c00c0d075413101a00d26070094285001003a4400e1090300400b4017020f03103544108004450842000d80e00c18103000308400a81031090100b00c03c0300307940a4070700520300d0138000e44030021503990942d100e038491040c0d40c0c264154801c00240ca80da420408002da2110030740701003102039403540d6030f440d01e41c0307100500310080e069a0140100f1100d0000c201c10b00d440140c42c2d00d4ad507405103041c100e20380046075000b180d00800100120303540118140203810000d10f90717209050503c41922040d42074405a485100040c0d1042003900070040d50701491a82001c802d040010b0340d000c82d408883c4864404480c403015403c000079500d10956400070790002c0c40308840400e500541031180010302000b00c10710001c2c04c06400255036409022002003200d40303107a13840504100301e6944088250f61074005608 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 935635260 1250 935634010 935634031
    0x3060b010e010c0b06060705100228050a02070303181a07050115140907110d02070e01062111040b121021060c02030903030f03060310090c060c02010203090402030a05 73
    0x7101e0450394054494680380302c1c2c0c040c0758004a96900d00c20310590341c108180580303072071040e1040000c00c065079200a1003a02802b403640c0501e0510101d046114112a182003420800c0400141d4200369010540c3d400b9a58945003624107204404028510a406d50f0003283c426030244084d9008004150020807120784660300a008407501207251500b520f9441c070030410540302ca0f16441d1854600760940a5101c81c0600f00744041460014505107814800404c07100540d114035814050380c05443c0310f80d8014841c0c0e10b41a64a442841c40003400340311004c0d20a1302960b26000b1418500b03491000381d0780070700343c107040994940020740103011508105035411460034580900101d21340004181c20a5111040c1019109000d6582e481100a0044460310401c5000138441240150f4003480100312884c0c0d1482c12030f8881c24030b8400c241c18040e0303014901071403d240900b80c00008498000704401c540c0303542006034602c0355600060b81907108600c03210703034054400010405183c07469071010780164070300c01c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 935636510 1250 935635260 935635277
    0x7090f0b0a0806060603011205100603290c070807060b06070c1d06060306010f03060308030901140f0417030a02070b0103080a021e1c021002070506090609010b010c1709090103060b01 80
    0x1400c0d1103c506540c00da801c004100018010180e240308044c40140c811021a40e03122620b640060032694690011500740107040501d90803000b5111402101965501a551440c01c1000295040c2d22500d680140380302c401013412002d0000c581c3c44100d1520000c1d2920303680c1c0032645081e02c04000140100382c0c11041c00c2c09001c1c1442d0034628800d208260140000b803464a690f0019108028580443c90405868002c0400005c203040003541c0680741480c004121603c8400903007c0c50b0030300814010b902d8001e2400c02020610704202c841c1c014200b1907441d075403500d8018449011384613a20024040100c260000002c1100d110b0040680754840c0e030a858021440c18000038402c000508442015400b980c0e8142d0319034008900c1241d52031842c0126072611000b4076a0b1808e82c2c000520603580c4e40c03c04400c00000d000140300c1983d00001060080003880030400003e4040f0181440140207401421424029880002e08685079010b0040c050f90359523960349006d5014240f1006014001503030174 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 935637760 1250 935636510 935636519
    0x506130b06070215090d08250203120307120203010b07031b031d040f09060209040c0c03021b0a08010e010b03160f05040e15070c0302241807090f0b0a 66
    0xd1140461000008041e075140c60280e800b0000c80c84001c920b40840c440c41041501d83c1a074808040d42d45035032088110740c1c0ca6898512450031403101c28108501951881c407a02001640d01181440400310014000394903903d03420800c40c1c515003c440e2040d1a03d1000001080e41c4101c00c0203000c50601c0780da02d8001d0502464184542c0f01d00f00341008011518010039001200003401d070a4054150280c800522021035100400c01d640e030f001401d07111264001050364a50506009400500400d41020b09110171301e55002903031140101c403200c807503000420180c41c441d662000d03844003c02481c0006d21040c90590145402480c0e18007003540b00e8411251405040c0041c0b1152404036501040c3d10021070740340c242480301038a00504500c100740541c1c020b47e00301b529106040c0b0300070301e4180c0d50b06a4042191501a250180140c0745084180e51810016010303225016401c1d84030421918003480780f9000060709240500d40c0d002000f01c81d02304081003030401800d5016039444a000c840701e05011707658 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 935639010 1250 935637760 935637799
    0x10e060c071b0e0402040c0e190f080718020a0e1503100f0b07030e13020c07180209061b070305030c03090f04020a0804030c0f080a08090c030c1f18090506 68
    0x192041448183c801c40020380940b40540c4041f031151028100b100c0c22004207030004480c0b0f00c84240300c800c418a8242c0c2440b1003e90144a01c1c0502402c030000c169090400748800080e0881c0070f104c611880e00081c0c0c0928076440340c801c11110301d1001d1300403a8031100100c0c2101480c0c000310780c841d031207508054000034050303002a12030049448410307940b1b11702070381603e08030b400b062101c4010b03401125490644140303070001d1004021001d200006404081c1c10a1407003c032100c41744000d161030710f0050024034216541d9400301c0b04002d4060391250801c040c00290281815000c0e030014244d030002058040300201d000c0018000940708441c50060001303a0720800c0100e0103003007195000204d0358400540041d00901500001a000b009003100781d40c542c1c0c2d9007002d26400200308000040b10241409a40d62081006100171001100500203288100300803440340e0320003441c61050314110900c14440302e405128100c580302d81c40c0c1d100d900920384030226800070348026650700c0c6c080c41c030f0405206a80c0c1607 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 935640260 1250 935639010 935639063
    0x60b010e03010c050a140c060115020706080f0c0c0c1003050a0b01080f071b060608030d111204020f190305010e0d05030712050c0f0d05220c17010e060c07 68
    0xf0303841c3c0c2e60502c40070030012140006161583c5201a030108480c1c2d1a81104010107402031926141c184c41b00459500000c1c284980396020f0742c1131000c036034140055a40c0c0400101c1d4040d181d400ba03c0d0300c0d98400e40c40185401a812041c42d00402c12034488081e0301d0381600218031946083d6000d02c8007040c43c1d401101e41c00d60403141d8411021220002c1040c8921030b10340c01c560000b0310805044001d044c0c2d200c650407070311564010704040d03100061846102c040342c010030034065903104016043c02071307508054800c5903005000901c00e9888958101c11607a50311040b0b0f58500700c034400619400d03180e180aa00030030300684048214462202c0b80304030307240701d401180e02c0780c2c240b5520404400d08100300d40d0068440680620402502072000c3c1c0c4010034083c1c040e00a5980f00c880206690419030700d620340a174540e41c13030700300c02c0740b50b0f0301e0711601280d6411916801c81c2d206032501e0345600d00d0403404500403c25036406d20320f10b007e03090510448141c0031001d080103d02503010b01c42100074121241f0595075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 935641510 1250 935640260 935640281
    0xa0c02030705030d0c0903080a090303080a02070f1b09020c0c150702010219030e0405040615050a050f0f0604030210020601030b130b04080c0703120903060b0303040e06240403060b010e0301 83
    0x510401c00313855044001d0f00308100150150038a44507468603640e40c200c00b508409001d000080c1500d00c100249070744034040c60740040c1e914004525100c16a2561603084c0c03032480c0003600040c0d2911101c11090000d100b00c070024416410308545a0222a46e0030703490700f4a000a06103d10006100c81c81c040708038408555456505070004e182050b90800e900c040c16241c0d01c4c4c1502805102c000900740b58440340601446075103d4903001900752581d46200103240c60316000280500184001806291074215040312108411607419283e002d102d00060098403036500029003051012690b030220b1500040c0c4030381070300d1059000080c50758030601c400d244241140d00203003050400c070021038046a0440010034122010000381d41c0302039120307140c01c1c1d1641c151910450000391100000c0081c08214170030f041040f041103000d0f600e414a0911580b0000300058100e6200c2c00d07000030008200346110380c100868001b620201c980f681c0e41d038101040201041311015012400010700c2c06801d24040c407035000798a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 935642760 1250 935641510 935641513
    0x90c11060a02180f0a18060329070801180f021e04062a0204090201031524020609060f06010507150b040e011e050621071a040806010603090611070b0a0c02030705 71
    0x318908280c00c441000f049129680d543c0c0d9034200400400c4c030410b4807044408440003444049d170f000e42001180c231580200000104a0600c00500c8407454040041d0200c25002c003000c983d940c00d4054040091180d0315415601c42d00001030000080349400c050000c881072500c0c2d501c0d10b5010810410802200b0a9801c001303080c842503030f03c00518043d40082c20041c018940001c60740550641d00c043c1c0c050340e40042040c0d1074030380f00c41d001c00b00012090a114100ca0301c003400320f60401c0c807a04d95907484082c284426414808002510701c0e4404d60035100c0c03580e00401104452850706142c3c200800d440002103020f5406d00110b0102c030801401094003180715890303400241d0f044040000020500078180d107030302080c8003a40d604607102c1d0007901c2200c1d040b6240902082072034404403e0b803140f95000c1c0d0340b0401c00c080c4001c10048a000c141c1e241100d590741004102c000c1e0309c0c64201c00900c40f100b080c81c160400400d1240510a17070040d494820a140d80e420002c203c11724505990707178021a0f1000300a07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 935644010 1250 935642760 935642779
    0xb09010e03070f08180402031e061e090603030f030c12070306080c10030204051e3607120203090d030f0b0a0302010507021201060602030307020c0a0f090c11060a02180f 74
    0x21030381402800003017450300c28016611880400101aa0700581c0e4920404249640b00c5503941d07081103100307800207000c031540040050555045055400c600709030301c3c461f180420000d0707280d8505104565610b00c20003c030035500d18050158030969048840c1c5004001041b00020f01801d0080c800c92060302e0440c00181070341c0c0101c90070071203c2e03d0142010006c05d9002c6c0400100c9444510310340e040555000c030200b00038542c0c9818003c5104010b19006880c1c18a10341c808a60346800303004405c0194001c0220080b9515207106841e500060790700d15840c680700000700500000081030044258403e075400740140f01070000c030103040c1c4810b482101c3c0d0100d9580e80c10401913020740c001300f42d0244040e10300c03004002030750900d07403c440b51507101602503000001041252035062002d04410602184c501502d07078100034080400d0440c5014100715555074070b610000241c0100544196403558030704640041c604421040007070b4004001c0d180b25451413407803914613803520104e420440e1501501c0b8041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 935645260 1250 935644010 935644013
    0x2809030c1d0c091203041202012303071209151a100e04230c040302090907030c090216060504030207050307240309020d050304031b0e15101b0b09010e03070f 69
    0x603941d008a0407684d014944101c3d0285184041c40548003c040b5440c0b541c400c04854000508208401080c09030500c543c0d040c0411981c44003800e1700d0b0040300501e071600c1800140ca01341401004150300103060b6080f180e00f81d0016981c20b800c440d0707007220340d5482414034001020601007040308512064020900720407450300c2030705142d03100c1103080c505144902100341c2412040e0515180944403040c8142c4009418070a50800080700c940000e2401d0080000b1890f5480d4440c10300c03068019001265000070b02c480302a10108503000500350064820805030920b45006903542541388a828024081d10000003241e419407a140c0d065090482410369850700110f004400a2141002c200d0b440f00003c544140820010000307003001d940301d00394030f510113040060031000d050015841003020300c0300042040311b5440da00303401c42d9500c0c1061340d4560000303000384410750381c140c40300b4517403007100c00421803890034410504c501c140102180f1000708a006000c0344160b461f80704031350b80a010020175040703500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 935646510 1250 935645260 935645281
    0xf0504051506180408030114100e040c050d1b02010c09030512071b0b03150a0302100e0a0518151903150609051303080603160302062809030c1d 63
    0x9038400c500402d0f000b00305000c1c0c082214040720960b81920001000300061084004004403001103440807141e8240c18484000c000f024003c400418501507912000f0501c400ca000da01540c1c1d8003a0785000500c83c00092202c26129201d410010354010760a280490221900498400c0c00b6030b500080502400000d000252001d0303807003c40b044858240402c4035400c4512041528006044400803041e643d08200c104d418800c182c1001e003622415299030200016591090220401880c1e03080049610302c482c400503400ca41194404e507005070bc2003400c6c2c085400b510746c18511925610b41d011001034003000c01e0100031400d000100b00c0f400d401241c140042464404a028042180c0c00081000b03500c0e81e08200030b44070251945043c0300f200f030040300308154011300b900b039101304240c0003000d42d0310000180d902e41d540107110103405100001100d6407011800050741703080b1402e481d8880e2240c0003a00000302b03007403c948001c0d1192100540041a41000807540c180141107503012200341d5142d048809 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 935647760 1250 935646510 935646553
    0xa060518030a1d0406080609060a020f0901180506130906080705150d092102100c120209030a050706080f0c040e06040b040e0601091506030605030d050c0717010c030f050405 76
    0x101043d034800903010381c50740e40e81d000f00c102410420003c2d0182d8103261804c41d180c8000a05080391351401070166041122000c8240c0d40c80020074a44406210402803002065001c039401007500403000040010000502038034490032510140010440340340c0d074901c0030b5150300040c003038070307070700c060500c2850131080e080c0b001400c030000c0704010000e00b01e10590740780990a255480c0c0700c030044900c0002095003a8041c4044143c403202c01c00140940b00d80c0304001006d54280d80d603042d00d5191f02182941e1181c0341007003042d00ca82d501c482154201501c405020348500c0d81214883d000040103800954507514110649044603113141012110362240800c22005e4111402a141c12944ea0005280043d800b0003110b40200f84082001490466071070440796103004d15003202046c50300702541045943c90008150000340c50616169403150480107a0780e05085159020b4014501b10341000c6072030312419440091802001e44081040e10010001c0000740d0b141200c003e003860704101032151006517221100b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 935649010 1250 935647760 935647787
    0x130e040201090806190b100c0b0c21090d4103130212240414100b010e0f1f020c1c0212120a030b030304170a060518030a 53
    0x8000c0180c0340c04800b8642a003c4904003889030070a010555140340303d00c60b2042080d42a51141f84022003070300082e024401100c001030500000c0c40000300043c1c1c01000303036843da0800040d85101c03401260040001078030107403a200c1c02800b44541c81c1c441c10303001e4207a00c0321580c1074020030803181c0809038080044034500781c4103031300f001c242851508000c59250f000f103105d00001c82c00c4034480c4520340180301d1205249840c0c1c0d035459000c0079404808000840c014041590010301c005016540d6181401c4444030403644900640300c1c82140e64501c0c002600002800325007aa0f400d40d2038038002c010030030700c001103e4409403c66819074a0042554841a03140369901c03850040302c0b484803000c1d01151050b040c4090314040100400603a000314940480803c1c6400c1400c0c000b0001309500242c003071614400e11800324103140d91b034200d99040c0d07201031081e240101070f00c04290a52a003a800d003941c40d62400d00086603141d26040c0001e43d07410055000c0c0107145d81800c002d504001c60498165040e004880c1e6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 935650260 1250 935649010 935649017
    0x30103051e0a080f13050a050f0904060b030d0801030302152e0b03100305150603190c0b0d02030a0c0305070e0d0c170f060108030a02062d2802130e040201 68
    0x9114010a02c40d200600700b1000b092426541c0720f42c81c3c4210f8084174020382059100f031803851820441130f500d007800a592074a08403544103241d200e0f4a0204010050302074416018004c5c0032140503455042800203048900035000d44901d00300c0150390400100045820703000b072100007092450540503200c40c0560040c0282080305140c0c3d1241000314040e00112040414003488032018800c200040c01010500513130300d1001407050401314002522191203000c0b403040192021180001e01201c030081c4002072801d130141c19510b180003003105000c0e52044603049039035070a040746203c400380310784951440f480280c0c1c1d50303410002a90041114014241c0d80640e04130385509004214035903c03411940f02e15010800809000280711122420b03c04c0580c400c0541e0341061040c0100c103a000720720340d540200f03100201e105280341110941500030303526480c11080500130701000a0507884030242c80c0035408044003640d03000b0105a048090707103d03d0040b082c481c0c186100820038002c0e04900035801c18414103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 935651510 1250 935650260 935650273
    0xf0a17070203031b061b04080a020103050c0417060f060d0209010504050c090909010c080c040303141c09050105062814010c05030c15010f030209070825091505030103051e 75
    0x4c101885184c49109000f0160083e9080c8010120304180d401e00081142e20150308003490402001d4031403041d6940a8141a25040082d406544501c211006400181038090407114040e240c560398200031180d01d40c51011044c00300300f4514144c20070580c2298010304031210b40e800c0c101448060072002d0580780001d1010300699820b603232805040b9101d086403400002e0000d0300c1310402012804068000d006091040006001003940201c02c60403240114605594036840460b8642c0501c08189130100210301c1c1c0403c0404206c010741015020780d01c129012108000882035a0088400902100d00d4608000c1800c1203c840c0c500d41819040605051511321103002d501c43c10305540c41000044155044681c140800d1212941801d024100c40c442182c1000d0640c0d012613645e104c05000d0400b8488448000354001c1900c2433080d001c4682441e540403880c2050401811000c114040c41612101c00401c6c0c8120a1080702901c0c12283c000d0014889119848031032100440100c1c007024140c01f910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 935652760 1250 935651510 935651527
    0x130c020106120503210f04030309080712050c120306060d050901090b01080a0312111215130902030105010816030b04050f15090d0c0b0c0d1d07080f0a1707020303 71
    0x82c59050340c01c078000d10245540d5801720354120f500305d00020305414500380002c01e010300401c810700381590190b07041c140040e03401c04a04000c030050140213001014445815086c0c00004d9020000c0c00324600c000d1b045403104420300c2510600341c0000c6991581102c014000720060100070740010703400502030b0000042c032000e40e488039102c40809802c181d8040d844180010109a0320005141c1c04103200b600c00c002d40d05825065114a1040c544101035090900c00803031050380300c55403200c840c903800030803e013418440303910b89101504840c0b80a034465441d24000051070440440c82c80918400d601120402d5406d60340c030120701020103003040d54144502060b503070003c3c90411540c410003110081d00703505890074030180d502e080c1035200e00d4820015211018000121111b09550b0081045075041e82c0b250074001c0726000130300d04000301e01202c0c00c0c041c040100c400c8000c1103100035a031812054600d181c00c45905240c0d110744508005003030410340c17a0071068801001001d0444244000c042d00c0c80d11450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 935654010 1250 935652760 935652779
    0x20303030a020309060a0b0a150219060b12010b150a110a060204140102030910030c0e1507120804080f0304030e0301050907062601090c0507051507081302130c020106 73
    0x11194000751950000034403081c00d404002c0a0b0b44601301c0c49040c81b4091041c0080b41307000d00c9500c12166020903481c1c501c074480f4002e00082030703c032003010b840019598060906034080c200c0040d80d02d02880f107421402c0c104c7d07441802104030310940600340e403000100b10420008254000300d5040100901440e404100d102c0a108052420f07015020250f00c50b42452072030801a280000c2160540d403041001c10b00c144c842506944019515040020701c0301300c45c00c2d00b6140320944007034456004040d00c1d1406114429200031b44441ca01907441c0300360b41c0a500030240c5112200350341c00380500c8800c0c882c2d200035450348002158454403a1904110940006000c6401d60320103442082c2e55401c0a00300380070050f032014514460b600700d8a00788094000005884c0880c01060142d100d60645608000c240103014400300c1e907100b036000302111007146200384c1420720320000751203403030000350101e0128100b80c0c4944950041c1c40c0d00140171400c5c009403180300303074002c007030310710720344095548452000541142 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 935655260 1250 935654010 935654017
    0xc010e0f1c06091505060d020f19060c050f030703142b05160f050a030e15091b27060118081e150610090f06210b09071407020303 57
    0x108003400314003e0228901081191341e202545201c0c10701e4041009019522607858901a0360142e030b01c1d042ca0000c0101240300300176403550007601d03410750482c00282264080d54001c01280034000392221005841c80d11303a00c4c1c0c4181040a000106064110240c2e969024014600003811076010750303000130f43d8a541d0506103410b80d140c0c501a03aa03181003100307502c1d4150842c8403502c55840c0011035803040d50760151850060003004010107665a80e0b0080e4a00d00300070803000d00d00010303444483c030728140c400540d0700d0308400e24215581c50340c2e11900155003000c0c03804461289240c420703007800200c101060303600d95400400c910b04010401c4081468015a0149503014028203c0a04061003110300305010152000c0300104859010398004c010f001da4900132a50440c900300c44590382c20501000444002e1029004908030882d5140000380e259000281c00d905a1381103007500da00707101c1c1c9005000440d50700020058020041c00001885a072049030720080b4815602c0c03030b580c02d00a450300420324607003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 935656510 1250 935655260 935655263
    0xb0a0b220f080c03010501260a020909071703090d0602181e01140f03070503060303071b0f061d040f02040e040b010317040803040509060a090c021507020c010e0f1c 72
    0x503240c074800e01c0101d40c03d0004002c000c205400901141d45001f110324200400400c1440018000d82c103058410072040c40404001034000b85189118200190388544803509403050829400d000354010107151404015110b071880010080a82c0c2c41c040d0312120061340c4241091140e42e0603c2e0524082590b03000c0c0302c0c4508800000001390074103050710024041d507e6019903602c28500034011f04940c00c028508a03907220025160460301e0392100350209241d4069090014420380100f65070700d4108c0408200181110440c0c00d000754041d80c2c8210984507036402114407103c803100b03034422603001d04103034115002c890000c50b401441c040d84c07240c1c2c200250500b900d04490308600ca5004000b842000b00c20f82c8410a1245001440d040c40c00d0f60440ea0b901c00c511403140104040000181c040c0c2e035010035100100b940e039109101e00044104002d480d82c0c20004005140c1d03074a00c0c08144800e00c0018640c10b03250040c2c50743d40b68241c03810200b100918020000b1a0310040075035110480319003241d040072200d0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 935657760 1250 935656510 935656529
    0x10f020c0c010813060203071e020a110a180903090f03060b09010e070806090613020c0c03070602010e0615010309150f0c09060f0804050f15040512190c0204060b030c0a0806040b0a0b22 81
    0xc241c0c0f80303041300c2d14580841549224180100040c40a640c0118100554130365002c400204000d4a107030580791c410140d48684044100ba02000040c84100c1e000450243c1046407092182c0e070300e4190f51203ca00081d607010000501800001d601401c000e034810350803080007480c05403041e0300c80304104241c2c0d10108020f40c07580c0014150601904081003514040c1c1610b000038001503010701d402640e50b880c02800588036440342e031401c146c01e034003d174081e4803ca074021811210042060024001411032901d80381540c5240094840c0482d00c900281000d0754002da948200c0c2c18044003040302c00c60720291042e51540241c0d2058403954004002110b01c0b4000c440112030240340c00c0c10900d040c885485071040c20440704018001c000b825000c2031000c0c440080c104401180c12034000300340208030030341186540c00000018010314120107009049000a00da88103401a50b070f0005000c2a0b0342440302441e04004a0041880354080d140058000c0740804c2c980801c03c030858151005400400c0e80c45401e11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 935659010 1250 935657760 935657773
    0x10e120703020106152f03040905151915030b060a090609060c08032d040c180b060f071b03150c0f0206180708010f020c0c010813060203071e02 63
    0x40540a00802c0c00605111101502c0c9501110340640800001c1c14180d01c00036000d0000307006a01460106902e031b800300003c50782c5441d01c0f0000700004180945510b070344007104a1a100c100d00d05400b0004112400300ac140c40041d103410100c5200901090251080c141c8541500c0b9007a16420090000c0c03403800c0d40c1c0d00c5800c2e0305e4180f0190034040f103500400200000a50b9034004950144200c03900031a08020703445422003183c00c004010b01d907856050751028040320600007403094122403a401c1d6110322545805030300802c400c0008a6602100742c60f040342d018000d03e14001c030010080e0016602880001650691142402034160165042110801c009068900310b80707001d440ba200c03589602d800e1450414100910195843e0380c0242110742c003600721849007142400c00d00a5000511400c4000d1100c444504113840203174111194911262084034280482c56106812045c003c00300800b2100f04d40b14182c5500019600051408040c44600c40000c3c08060032544000c1c1e65070034075400b8002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 935660260 1250 935659010 935659013
    0x60f030f16020a0507050d230715020a02131d1002030412080402280b040f080d1b1704031e020f010e0f0105030901060503060112051005010f03080903010e1207 70
    0xc50314801d44a001158400b007074032000101c2c0060720006aa0049a02c03a05e1041c2c646007280390300d1500c074001100c0ca1207042c080d411010000a43e502500d400054601c2c0b0310035011001c03039480c4110000039600c203441c3e15841d01360016648c40081c01c602c0d4039002c401114402520103203000f0102e620344003001c1d400810002440024618411401d48519004010b41090b40000e07040618000740c29104089071603040500b800145004002041840e449039150341c1d950300b07480c29000b520b20803a4441e0240c4101a40394a202c0c0701040581042c40407900142025910340100034910061180b0100340204800b00c040781e85002120345c040f001c18013244a040e014414800a02403c26205051010b2203542c00c1c07442da2038600d08038400b0020301c0c161b51030f81d648820b15405400340d6400243c16000e4000042509588540440c0c1800e00030011621081d81c200804401c550003442078000c011540b403024400a8805401030803a100d00400106800b01c05086203820420488900135454400180910 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 935661510 1250 935660260 935660281
    0x40e0109051e030f090a1d07081b04140f1c020a0b04062003090303030115110a02010206010519150c030f080708160e090c03090d1d0405091905150609090a11060f030f 73
    0x1e40c013104820700615001280702000010340907500503000d0001800355993341c151200e00021840c50001030200000c580c1c8005501002c1a84d10b20aa00824000b04c0110700441c2c14000c9904030f40d416a10407502800d01d1404407607035031603226454054001004040c48c82e90741000614041e20740707000702c04030707140103503502030010b4455041142d801d40024030035170050703070700800c03002d0440788245c070752000d000f5200f58003010f2992030303030000e140590043e03182c074407801c0e0711544002c500d074801d480e41040e00c110307801c0c10b030b522a6080b561400012903400c001040002c11807004000045103087c900c14064490000036114402102d0701c1c031032503101000302311702104100000b40c070714102814040003c00c107030240819504882446980100c1e00c034404200358038020000404440030080c03e1030302c07412140c600181c450b10b84d03004c4010011500d4011507924900300360380600500165000308105c0225176502c1d116065414141030344940c1c148880b900c00000759000b1032107030107112000c084902c0d1295510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 935662760 1250 935661510 935661527
    0x10c02190f05010e220b1305040809010f0504080616030906180c09060303141e040305061006091d090705040c0c150b1302070f02040e0109051e030f090a1d07 69
    0x214030540343c550350800305032171001041d00c0fa88080d600128800c1e080c000400c005074082c165200c440c624040c200020700c202c100c0a805011001da0701d040d1407000300801107425000b03502442c0303110707000070b404210f035024403411401301000d85080100d192030440e11030504460440b4444c800c1403a4900410040040524004001e0032078981d040003a282581c500810541c201c52800c000c0040020b00c0040c420006a000380381c07004410342040d41d07140c813443e100d611220191000031507013103c0d65000c18800d010329140015039901c261210308140d00b50742c1c0d02c10f0252021b04000c80d1030140540200c0d20751100e005108103100c1c107403a00c404400340d600d054270b0181c0001545c01c400600e4603444070360a9a608031110500310902d40e0252b1103402c04d0a000b0041c9043d400f00a501520300203080b0311580064001c91201c90003581541e03440c40d04900303070300c0308080007540c0b1100c3c40d0010892042e40c082440701410480801600030740300c02e40c845501d0b000038040d0350a0f59250214507800c01044580c4490308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 935664010 1250 935662760 935662787
    0x303020604050c0102031e0306031204081501080a0b0a15090507020a0b09030315210d030614010801080d1d0d03171005030304060f030b0904210c0f02010c02190f0501 73
    0x552620740306c401421107c0109011207101d00d200000850300a44e0100100c044070b5582d0000c03d81e98030781c0e4140d20f9540d582e40f0001c0914080301c00c0000582400c1c04510044816080760349c0020541e01d020011001342071a903409490382c12180d40103d820801031040c107205803943d40085c0041d104500f0b100b210684000c20b118890b920400422005003400b403d03540f14a507042c6e4000d09212034035a41101200c1071404982d80703601c01e03150707594a10341d0705800c10800c4904035200070b0201c054410045841c1402401020900e611801c840600e043c80b1340314a164402c5403220302801c49609400080750411001c2040d00000c0c0c00070401e80e6120038812903181c000710403040c00600ca51818020039128040e502c20340d424490900e1105205a0082d0055402410000d1014409207824a81300b07600350103410200104601c07007801030456501865034280c030144c000030090884030300ad500440c1d4120050300102d0b003010010b0000000202407050010140000c03984c94892030381040001042d103d01c00d0344 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 935665260 1250 935664010 935664013
    0x40f170c100b10111e0706121a06090d020d061a09070e01080408160c060f050403030509060306030a050a120f0f12051b0d021c11030f0406150303020604050c0102 71
    0x51055550200001c10b0214a410316010011502c1072180c00c22540c0080c945d2220180014210340c880040ba00d041070303035000e4540315120b140c044c8800049821080c044c9002104408079001c491a1200240c8034880e402003200903001e40301d501041da4441544ad0896000303440f1740c0400c0f620340bd2441402c0304064142d40800b031900d4504001440e5444411450f414004448041400d200740c08080f110202410307017580e004c5003100d207480106200288281c400081c65043d510407100d215400315802c59400d5035449042c0b0080d0020040c0907440500155494815041c52000041c01400040100f60241c80c60580000c0b801034060304034142c081c0c15000304135150304442c0c1075640102581074100340210380001d10741c0c2c0e050001c0310403a844040081e00c881c404920403242c52040d0300100071002990080d42d08409103904000143d6420000b0b44140e070800f44009128076203d0912103911900502c40851168502441c803090305105400540058000c0030800040c8035041161810f650750078070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 935666510 1250 935665260 935665271
    0xe060d0302070b0306030a0b0c0a08071d060903030405041508010c020304031703040204110f0a030b0603160c030207090f05010303110f100b01050904050106022d07060305040f170c10 80
    0x80c0c00075140c0405005140c801d00700800441c400e924100300d19004558401e0303200c3d04905000d4a5099940c01c00d410b41301c0003c40074030029011078828150103e000340c0701c400f040400c401003010800745400080116406100c144000525940d0714000c442500b070041001d00421810b2101403400c0d100104080e50655000301700c100009902603110f082c580c030205494035200e48661002a003e080001e90600c046a0049090090215810010b082c5403005440812603010107006028460004031200045010000180c24400e402691885e60032440f9105403483ea0740c8528424007200c2000c0c90003021640d0790030043c020150020a44409040d42c080140600110008029610b05c2c08101e400c5080341c0b21000c5c1350840c0d00030320565802c80e02c010002e00440d03031558002503454059440744d14a80401e0141c0d01c540181f000302e2099400e00c1e00c400f4000d00c41c1046825409044003a0088402518949100c0040b40180e480ca032a20541500002d076104801d00119240c40d020300481403940d4a0207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 935667760 1250 935666510 935666513
    0x9120503030609250f030b0a030b07051b070f0e06190b0a09051f0f0912061805030c07140a0b0706050408070f05010902310f06120506010e060d 63
    0x4280c982c0040e00300da00141c00d40d036503040404203c601c0720a034075000c8002540c8003880c0c0e810840070f600512882d9010414125150b0800001140705d2101814480403500450449440f1304c00914041d0001c1403a0403010300041002890042c19034080c0200c501e1031001405010118000c441e0045400c45904c02d91900082006003100d50b644501d04005000180c60100203015031088001490024084c0004141c0700032504d100600080c50fa00002d014040d44d044610b02500c0014240c881021040d160629160307199030040169805540826101c0411500041c07800c00003803001285141c081d080e41440c1c040414520405400c41a1144401d1001440500c00c0030040c3c400c0380c5d07013003900800c060312682452080e91044150183c2058941c0f1002020301c801504482c070020b02c25118044960119900003007164040c00b8200342c0d131480600700364650741c115004011904524040010700d166503000302c0f81d01040c100000c444540001004004240d0b900d0061644007400361201c601e4403155 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 935669010 1250 935667760 935667763
    0x1504030512090f040f0f0f020c010506030a15050a090c170706020c030d140d050c0c0c010c02060703081e0109140c07030509011206150309150b0f2707080403091205 72
    0x200050b0380125616810103c110b81c2c950800010b0301d0a86c282040000d100c850440080d40c0702c0495200a176003004003040352420006070400c2c5998006941e40c0100310038808520140c0b1019000380c050903258080200403e122050160040c00e40c00780700b24000d01d012002178100032440d48158203540200c2100c030310f107881c041450701546005d03242492001d00022101c00007030241c004490741c030504e000e08100a421803e00140012607201c42183d140c0340e0000c004582c80d85150800940108043c400f010010f0300882c2c401c1e80240001015a19201c0c10059000045901364030010a0700c0e145c4108000006080c0180c640244000303448916142150301d0240c040d10421144c6c1d410800c80105059141304160f00030030281560000c140c2000804030401400b40050040685250484142c01c03080c142e15846440e05001015001580e0b5405402c10805808012100505001c40941440d40c24000c2180c80621920090f00c0390700342403c00c0d04000301218010341015188020034503130100450030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 935670260 1250 935669010 935669029
    0xc0308070f080c0c01020c0a11010801140a171f0b010306050619440c0310030201230d060e060907090509220c05121219020309150403051209 62
    0x20207840160b458a441000b030740203118161f4495028061361481c00100481a440c1d0021718500348d07102c034120703601e481280c1d00303243d0070401f081d0380011034600030001d00d5040b4007418090303a1440b080e030b00c00c2381072450804e400100200c0c0b01103180e07948160320481580c0601c2124084d100640c0c5803828000a8500e80099020381c00401c400e0040720385003059015946403404450701200c3c4c0305503c80006c203d992691203c0c18000c2c29142c42c142c0d00003d102d9074945c02c10340f445131240d018454252482c50300156413560f0400485100c40421070b01c4700c1d0403001c20000901c0392a000440010700c052510310042001840500020300c9840e5050511024a5000100c001941c00c22074060402d515040600307000c80d100604d0a0351300032079001c541001e01040749407200445078140c0340d00c906000480d59841d101c1441240a0100f00d00511542408541a0414240d102e115004036441c0022040008988400b40e0001c00041a400141842004001c3c4050f05c980d0b646000e20a05069050000506412 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 935671510 1250 935670260 935670271
    0xa150e0d020f030304060201150e0903090118090e0705030f0c0907030c09180c080105060a02031e040317031509011202010e15030a200708030414011b0c0308070f08 72
    0x4624806440a5565018110700310b070700010200ca6983c1e0b92021301a000c2c0c117510113800f10000d2034100c0001c03007034810f4002501ca8100032001c1d40c9082a000d00540708640400405180324030342060104003060030b4030554044000d04c600a15809142000701403070000d00e41d1705070030b050b00706080145450301c610b4071181c1c01100d5810041000880d0040446451032103a00a60841e4000740300184103400302c0d4881d2003519100e507038148150380c840c418001e80303204d00c2c409103006078020842c0084111002e520054496035404040746001d540340c0315911241c0720940c02c4803401c1400818022101007500000b0711001d81907982400544c54505892082510150041d0500a210901024664410300d41e401d0200d419001c0c43d131a0b00b062640c0000502c6403050a828018052040500c008101410b4070011030303004140a1441c0e4481d41c1c0c0703096162032415006015921951091420b102c8200701610381d10a5a03500b0302034604500f001400c03d0400b4100a0074450455a5a9641580107070345941c0710 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 935672760 1250 935671510 935671519
    0x209120102131a07050105040c0e06030f030307140715022d03010e1e010303080601180e01051011030403050a0b0c0c0c0105090303070b0f06041401061b030e04090b04020a150e 77
    0x10b0f0544030581102d114141c1c00400a519003c10401000b25102e0341c0019503042200285a83c0d0710081455503440c460321160a140e41305100040300c0510840208124400d4000000e08003800e9941e000901191180d80113041c680101d10901e5812048007070a568500301c180c840001003461514140c00d00c01030250322008000c03500080c4640c4047e01d200921100ba44440824075a52402c0007000004103444a60000316003005020740c4c02500e071030fa2020b072845450152002c0e46807804120003881c03180419014045082c000c0e160712003050002d00002d41c01600075149021480c07030116200980104015100c031828841001c403001c0004444118183c01c1c01d040390b0307032000707500080d246000d2110b0040c1101181c1b800c011200c100d1959890154201340c4051041c2c44141e2404128203400f4043d800000e10004186860081c100c0715001e5030754007a0520780031800c0100007240c1900d84600c01a641c01c0c80d41d4051008500781800080700400701030300300c001c0d01c85070407200810010305c1030f0419208 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 935674010 1250 935672760 935672789
    0x1e011d370803100b19110c032a060d0c030f09030c031808120d0c080403020d051e0a03091202030c070302060304390504060501080c0d0e10020912010213 67
    0x9034051030103000c05004e91114603915900040f000410280640038120002020762114402c2002d00090f8000f6030517000b00503168002440101500d0780c045052003054213000420f40c100c0c0c0ea01c1d180018144601090b1b0089600d6040d180c0290070350340341e62100b4580910b000d04500120ba448000c8110141d41440c101601c0030300034198000c046a2500030050030700400510b0034003c481c0c50001e000401080000780704134004e191042c0c82911040340c010300540c1203c003040c0d0340c19201d00f0041502510f906c0207140401400c1e0305c54843c1c4d4212680200c040b035514502e410600230140f42041c09001c2c944025032420351904031054940101c0d00c0000d000785008000b107000c0194a11895890354072156640c0e1403100200e0411040000303000d24607401c4940c80c000030a060605000d00015900107840703c4103642c80302d0300030444a40c882d4489044495443e482a100e0403811301c4005043d003c14030380542c40d001c4002c10801d20302c460100d01f10440e0310400c8143e00728000c00c14100c2c01c0300c3d64203501d120f5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 935675260 1250 935674010 935674021
    0x203031b03072a0302060c070b0f180109141509030a03020a110a0503040f0923090c04090c0f0927030504091e0b0105030403021e011d370803 62
    0x220369583d40b100782203400360000d5003d0503044a0400b02038a6000f9401c8450302d844400b002d041c548074200c0c018248041c05c80002d2040541c1c201c01940065410341120b03540ca9100343c11908445444004545c00c14024a4a108105040090300d0106030307903c1d40d605c054140b600c0c05e903580344203e081d1141407540218030344084030300884219040c00c940c1d00c2540ca100c0580c0c500070351254032500800380c42d0f0403102c40c0490500c0180c4154000300c883c400f02500380103445045590205c4000305169402d118020f0311407143c2c3c40d0350080001143c0308d41840d849280c10300143c204a514160000900707103240c19075844e40144449580c00c1c411140c1c82c2110789460841c28212340301d125a40003a03d003642844803401280e080940a81c81c80c036000c040802c0440105001103075181300503640500143e0142e64000701d40d04141011400002d1203000004820308020420b40c2c4810a092900f50f0035000b02081d80130020305e00c1625651300d01145015820b208401e0420000c090154a016010303c030048002907 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 935676510 1250 935675260 935675267
    0x209090f0703050c090919020906060c150402011d03150a06031a01080d05070b422b0f030306050901120203010f0507212012070203031b0307 62
    0x201600c0c60a054400c019180e0501c01c2d030755280c0c910483d006103240c80c00200800c401244400400018183d071209210403a002c22100d000c01410082d0301c80010441c81280000821030018065610040c0780000d1a1600000d00201440301034002011100044034895580c080f8041908803c005090302d190340720040c00b0030092450350401402000c64440315a109441000c8240c121403c41c3c0c110744940b00011011111401090b100a11400e103641c04100800b145800114032080c5101c150840520801c40030b2a0301007810102542c0145a08000302090502d11184a0044500e41e074401e0038034840010712107840d603003000140c0035414007000d440c101403198010500400005166001e6941c44000e582d40b440d04901d000c0344a50701e000c001e4284001c040c0103261069000351148000c10154034107803081c6c00c0041c10000003040c0e0310750309001d030400c4210f2420740300c1c0480740c507583e16011542607042e054400a03041d0410366005000f0401c2402c3c204240300c0c155607d00041545940b50810f054 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 935677760 1250 935676510 935676523
    0xb10260307081b0c0414060d1401020a05040e06042a031410080609010b010e040b01020a0206030a0902190302100c110a15020c0604030f03030b061b0102030123090103020909 76
    0x18540352000544a004800b80c0d002c09a4140c0d482c8155a138800503001040308a40b41c000d4101c000315640000a0014a031552074021102d000700144207070200e02c800d005003207902605008000c500d001c1410300a209059250650100040d20108a00004480c1d0b1034210307008030000c011000c402409412445100340c200340318041c1401108091410f00060317010f0800810701901802c0d22442c0c0014401000501030440002e20603101c7e41d80180004050001078041c00550506520400000d100140c58040081d84a0b0703460180003d942089441001403410703c125014100c0c1c1c00f144018005030fa1114201102030340182404a1166003074681000c0c1203c82d4000b0550000c41c2060000c0c8100c44000c41d42c0c0c0c0d03e10f030b65090f00c000b2001402080349031700403400040e206a00e00c00c18000080c0c003d40c040d4000c0d900c000c0c1204c3c103101d00c0102c400705c0c1c00c0580ba0540c0355650080010003010b2a043c000080c06070200d6064815561420701151010905110292113a5101c5010940e4a5400e00c0a0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 935679010 1250 935677760 935677763
    0x81b0c100c050f030403080a240e100315020307020d020d09050603040f050d0e040b0411031902130b0a03150303120f020d0905030915070b0705181c0b10260307 70
    0x301610b85ca0035080192240c00c00303c48903000e190810003003e015480031560b02013154050040700311024100319665004603c014000c1040140010740400854240d0b5000c02555004050160345c0e850910300017401c040e551502d45d41594031250a038035205411007120b0701501d00c1520155103d03501d904003100c0441c01c030f03000034180340900440d6404c06a40710f00c10300340d000b10940e4284184401002808100c6554218200604c241840402c0f60300d84007443c081c8031a514080c1c00340c18126808180e0399034000c180e1100845081c00a0303104001c03501070180780042a8040701038040f0b140380d030b00c025018080e55590545617643e140c030101082c501c40c3d07056542c403030101d1000b00100075042c03a015580341c0c0300740c0089100b20300c0e003100d54552009050440d00c20325400500e580310b58450500540d11368000c0801040c28140b0042440c0c05a200c00e050007420200c52a610380419010341031041c54202c1c05030150700e11203022a01848801c3c0c0051040016007480381504200c2c074255402d007400e5001d100c40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 935680260 1250 935679010 935679037
    0xa08070809040b06031e1f08030d0c0212030705070c030b360c0603280603060b031b060a0c0c03060b0a153903081b0c100c05 55
    0x4284003409044405040800e40544040200004210810103180000c45045000b40490a81b404c1ca4014403030103e60400074881001200c00040100e24445940e0b90b00704100d07584c00494500507110b10341c00f400c40c41c1c010500151650138003c41c1c2c07503c281d00c8020095002d01c8000200d440401c0441c066010045030416280381003402c003003491280e2402080040220106009884914200c10003c141e00800c1468002c100c41a011800e00071181c1008081b20305040c1241500a0425101e00c01d0901c006840c00c00000c0c03e030b0442c50440112803103444514003e600c901c5054951054a49082204050441e0030341d89800400000300d07a4141c100c0401010310010120001c20000313a6000b00c99081d40c202d40703070801b03503840780710603810381c0780041404000035028030a074040c07030707030000c0441c4081c41614a1000040103103100000f01d40940c100202c0020725204108501d06c0c0350b160b0050701082c6402c3d907030361401d84c1140100d90b840180c100b0440c0b11a43d140480c402c4d6601620071561046121030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 935681510 1250 935680260 935680267
    0xd030c1a16120239100203040c0617011a0f040815011a120c07020d030806011409010527032505090103120e03010e010f0e0d08010303020d08090a08 65
    0x841a008100c00003108008107942002042e000c003803900a407002040359065072605103a9032680a4507809042d040302c600b40b07480003441c0624210500070003070800000c0c01c016039281441d140c19030005880c0d6000408000c40e501d2011010b400070303035100341183d045801401e40c0e602001d0011545214031101201049000a0b00150115011034480b0f03613149008604155680e88105c580031403100d000c05076045100c2008055480ba1080d00802d8115443e54803031070501c41180c1c0810294034080c0016800b2440400401c0220342c2d01221076102040340d050182e06191350540040c05034000c400034407801080c0b01d010203400b41d42406100001c2d10004048407440e200760719410102c04075400380311800c088510804190f50429148090490b54800c09840c03541112040c12207081c5011200702d5030554171101d5420001000b4054585040141400003d0200600152903d01520b002d040c030280003201c0300400102e44c0218000b1603030901418804903641c0c2e0484000d0820b15811401010604081b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 935682760 1250 935681510 935681521
    0x30c2403051519030203010c051911150c030a1505060f03040f0507061101050601052502040902120313080a030813030512010b09040f0908160c050330090d030c1a 71
    0x9007030b20740440317000390000c001000d01c0001c100c079284200c0f030b107003111035a0400140070034078400d07202d03000503003205415607440c08683c1c002098058020360b44800c0c807180c080280002121640b117014010040300c618a0b0304a0311301400301d5604d02460340666202540840002c00340585061216002c60b409400d64100340d840d8040074101060a00080c40158a414000384043d4011000c50303500304480382c0c4021004001009150725200c0c444402c0303070040c1c0c8540c104801078503081041e8004c425080701954848604940d0464441459030001c20f585e8481c046d010003080d009020780f6008100302d60f0346005a00141002d84062241d1170707054010700107490000a0844200b0090521040304031001d200c05c2c86060701e100f068960741000034000e030b0b10421450000030100300d03144000501c1356600768007031035480700001d04011820070700e4006400f110704500300100c4103414200f102c40160002a0410f0b00350400b0401c018034806006040c080c0904002d0b062084880911601075250b143c03402891800c2c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 935684010 1250 935682760 935682799
    0x140702010e0610051c1b0b0d1a060702091b0c0703120215010b091306030503030a0b0111030a1d0904030c0314041409061c03030501030c24030515 64
    0x10303010401d565005000c08038424980804800b0111000245601081c002000b442820444400340413101c0016002840000b814200c0e910b400808030420301d1074072080540b0480095803902400a40d042e2602c0d440711041da5070780c505803816103406851602095440c1c4580050003190071000c40b1003500e001c901ca0740c0c03c040c0010600113487c4181d110760041409600141d0b80c900d0070400140007840e260300140b00c8528400003802c0300707400040000810312038412901c000c42e010344d00140c905800020802408030b080380a03601c045c010030320300b8600e00d03000304a20faa12406126210070170400e10800c11041e099550801401110005142c00c1c104e040624001d003420304a070204902140d04001c402021002c0081a10126810901c1c4564184981c40c208654420700030709040e0b003d80c00d280400306040007450b1844040f1303c207840009055042d4100300300d1400150b031090003100f1994140c820b4419005001015029071414003003410f444035030038440a00c0b803580810703801c135640c66070b0651107154 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 935685260 1250 935684010 935684021
    0xb0c030412080f1302151209010e0d090e0a0b041407020c15070311030408250b0412060b120d020109031e0912080c0607050d0e0d1b0614070201 63
    0x41a0414410301d1010701060700d52410032180540f00403048000a0940c0264411400301c0701d200034600481c640707681d914120305802c0541c240440c00030131070400c507810200348140c260a29031714000702484551004000d0030a0040d00036400030f0b444210100c2e45a414a412503003e20300001c20900003440388007a08014002c04480c40001403040c1008000c49040c044103440b114021854038900d0504681c82c09d4807420748442c828010f0f80710401002882903401d100c0207814050b6510048641c240750511400403100300d4225004660040004204a02007000200e4140380e10200111300141d81070300040710480e880d41d00815600070308822000310740d410b52192144038440e03242d00c11481060300c0038890a091454542012545e081340c280101c44001d4007440089205488041c1f41004105650741081710681e031082c0490804201c1b10403004075400340d282420140c2c8002c0581070201040103200c3d8030960a00c00181d843c140d018420b0001d65081f91962501d40345098595003000300c13000b0f00815 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 935686510 1250 935685260 935685263
    0xc01111b061006082220092805090c040c050a030f020403021e190914010801090b0c1602030a080a0315080304060f0e091f06050a050d0b06070b0c0304 66
    0x3070000041220361500e5908042d52810b43d20481281c1d240e240004c0000450402c0074807910b441c40080e00001c1d0112620402c10361a003402803c0c0e801c0c1130303091000310200a40030020740d1050b1441d0481032008840b5415210404030300129242d1602400c0c0c5051000140d035064126050640d20141380d40c100c070061204c022240d8041011a143c004083c04a0269001c001c2d4000c1840d00a0000b200c601003055840020040c080300c8662000c0c000c0d000e071344002d94810340103180c440c100c0c0c4c1413106001c002035005082c01c800901c4410800d030340f440354a03000101070703030104800030412095032008428040c041e20742c054100c0c2c80030915414003c2d01604205248000681403810a0340100c4414000344202c8032140c0c02103051070f05005c4251020b003072000700c500420000b01450382c010f66410071401e009030b5000182d1021000c07076048010040f01e03642c02060521170308200c0c88001c141e11500301c030313880c1c1c965010004c0c1542c2d0340000100c0e0780c807030b83c1780150911000c80306002c0280c03860f9000398000c3d0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 935687760 1250 935686510 935686513
    0x203060f070906021902060d110712020d0c0f17160b1f1d060d080a0806040510150e2e02010b0108070503040b092b030605030708070b0c01111b 63
    0x1d5643e0001280e48180509410610317440d918034003c0142001e0010700720311425640081102c2d108e03440480f030700d0b400c42681a600015a503c0724403800341c060140c80d01e040404c1c03400c100310b42d0f070b907845040c50b03401c1d9010024092854090381e060b401c2e09810a40b22076042d0350410042100050401c4020910280e50b412a4900c00c8042c0b80b1802d0810f111201c1181d0003240c404210b004001c1c01100a000000c01d0b00d90003041401d1820002240f0340c00804030400151594000c900b000b4042c8400ca560040c1f084da41c03882e0480c0c0600120b625a040410001281d2511015250480740450907690040d01c0f540c6500740300c901611002c0031005512100b116455008200c5c080c919001120724087c04e41d20341c00450810000b00f0f01207030051a59a80c04203d10045404110218600042c2c08292100b0b00110045c0840382d0460294940982401440b00318010240507042848180c2c513102c05101d030139404103000580d4101e030300c0f083d00a06085403a203000d050721101c0d104440a801546400350b84103d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 935689010 1250 935687760 935687777
    0x50c0a0206060d02150a030f0f090b0a1401051011030316080a06150c02060c0d0905041a06160218040f0c152007030219050301360f0203060f07 63
    0x80e420302c83c0c100d0b07103803030340042100e00403480c22034111940b40d004846200400d41c680c6103a240403841c6d806080107080580b44002200d82c06410150720211003d048501514100302c0c1504441c4115403005055850455414003031104822003a10a40c4000300c0c00080c60002104200c5c96804001d00b900d0804882d4581a0560b900c0c003601308201c0d52a4001d6010740d042503145ca200c2c29100f10050030b19a407001d070100740303481030983e0740d00d1418500b00c40000004042c0e0805200d142028014003103104000d41420064910f84400501d140c040e92181c0503500414104403000d641e24500d0704544682c0355120a451402c150621003a40d00d107007081611480e104420005140880001045a002040d0b54042c52450b41c1080001b03494400144c141c014402d02d0800303c00359480c04403e000448400342c661f0a141c3ca0034040c542542e40764480300e030500d0784607010f80c1100c0c0140501003241000e0401501a400712a14041490b02c0b02c185c00a501813081e4405c00c2101a001280c250003040141c8071aa003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 935690260 1250 935689010 935689021
    0x40b071b030909200d0b010f09050f0d0303200304051501051f050d0e07090f060503120903070f0602060702100c020a061d030a05040612060b040e09010609050c0a0206 73
    0x111a140c1002030000762941c008000d0120143e000410001044020590080031042c03ca08140c00401c010031045d5620300750f02100390381020394508149090305000000502d4000041c004105041c2c18601422a180d449010544240d2006000b4903201a961070715540180101c40140c2003120211090310404450305003e400359030300c050489a000348040191a0b078400c0c40003001d062a82d400e0300340907051201c2e00420582e40070b0343c20b074a070340403005200c15842c0c00c00f40020742e20030f4190842028039189051000361000f140e070b030404880e9401c0d059078803650140424078040780c9600c1005a12040c410109000f035020500501440441d403c9945500c0340c0c0120700c1c211100c405143d805a40a035285000040054005200707a080110040444c2c01c144000e460642c0d00081ca2000014030010301400b102e504112002d40c003040d191400c0044034240704241d0b00a01c40c0d07000780111034080c000001d8107581d094128101034140801c0510641c100007000900c0c5800000d0b00c440540a40c000080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 935691510 1250 935690260 935690297
    0x81b010b06180f0d05011a030601240810050d032606010906030b0310180b0f060904021302071b0f050913020f0d0f122d03110d05040b07 60
    0x89210740780b500080202001d0008000200715503036541500306030700c0c0e2a2540400c4081c420300c10002d01c2100000c00002c0c2c00001c2500f840c0050b040032503483c0f10701194450f00714420f103001300c009495013825442500c4085a010242403283c0c4120380c49864401c43d04201540005c0000c040c410707141001010709500ca501e4400b00b00121041400100621001c0142520941001e1a10080981542d500e90003800c0c00d4030075241d0713000381d03681350408206641d800c0210b40300360a07901c00301f0076003040090f081283c0061104a00680301070300c640b8292021113000000e03541101c412a502c220070394504e4610000702c0082000030700c50200e0f440d01c0c1050028441c1080c004051143c0280e14510b60505101c1e400c02c40c0000201c1e01c1150030032010924600040d550044400e0158013409900c071059000d940e0082c000307194194038000141c031f00d20f03011120782c16540c00d02d42000700a0402050500800000c0d12040c090407840000250410080c081030181c0c06203040d0040030f299440c240c0c00e100114000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 935692760 1250 935691510 935691517
    0x501021324080a0e030304051b030a03022509051504150524070519060b0a0e04060504110d1a0108070b030c0703030207060e0322060203071b03081b010b06 68
    0x16410000110001d640d21480303034841940c080004803001403200011040e0601c0c4d40c004a40c2102e45500514010841600302000414403081c203d00901200c099690003d482e06180c450407085207c14a20107890007030100c2d03503040a48094001044949011400745e00000c00d031014445c00b5034039101588104c884000c0307000c0280c0300c0240c510311100525804500400c050403030b20701000d0009001e41c1002460174050032000882e1107c29981c440b4403801d041c0103c441000300188504508181040101440100950300980000c070006075541c3e2414104002e82c10320f254260320080c441d1201080060231008060f107214036184184907030381c94102c99591640c01d4080c25400b00d0b020300c00603c614410400030301005200e8540541018041d58813601554030f6840310904a17040400c2a800c2900104100d0410b402503580c4d81104a103803400c007039204d105904015006011007054130030000c20407100c01e801035511029040d901c90340702c1d01825002c258001c403102c684d42000c5040300e8a2030f00c80142c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 935694010 1250 935692760 935692799
    0x3030106020c12070b040e04061b08010e1305070609080f0c09041205040f03030c051902060901030f0e0a0b0f0108060709230a0e0709080a21051605010213 68
    0x10b08012031140208035180c1095075980724103204001c4042110909400500002c0030702a003c1d0a0b42c1c10149484c006030303201c854843c43c061418031700c00c002940e44040d6940c1100c0302c1c5031960360252030b0030f1240341958890880180c6980300d46680098920752011351901101c158405076907081c040c3c0c41003547c4941109034650340c890707920f10118001c1003960700d0b110010300107410b24a00d4955240d003c002400030f03d80c0140c000c0f07a0b504905c40c0c2400303001e110300700c601e6140642107070140e600c0340d0014100f030141074121030406580740d14202c282c0e002688030161005804c41201e01030b4a00e480c0940d210301c01101d50045c08174203503000048103080014150300800c199246d50300a41d003450112010203a05040d6225040c6250741c041c06c041e00c0d0746040a0190151442c240140d2416043c0508191642d1b032008500f540514180c13004a00c2020044002e1a100c1ca8204100d24a402040721280074030580014660b054036481810040154020000c800c280d0390a908401d999a4404480c50f241459 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 935695260 1250 935694010 935694013
    0xd021611030d1b1202070e0a0c0e190b0306060f0f13120f0b0709051903050c0303090f04050603010b030d11070e010518090f0a1a0f1003080a020a021e120303010602 72
    0x2000f80080c0c0260701ca50414801407048401043e910300704081404e40a8034408180b81d581c2c0c0c1d050000c01c0d80720844800042058034289800c48002421031a540018440c1c0080b0010210108040d1360314142110340c070aa20701b41c015290a01122040100d5001c061580a12b100e0582e00003808040007495820164110340c000304034080b540c64031041c807038004004900f0000e00304000310300b0396a0420342d012448104c91085500301e05603d000d40c940304107005418030990042c8081c03c0e0035925030560b1000d005060314042165140d41c1e0100b070240503480a07c03035050250f0050182107543c07010601294201d410111408180da03482c0e1200920800e014041d0041d8203d0040e80e1442e000d413a40ba90018107032801c5800e110b00f2560503e0900702803913011119041c00c0148030141d149941071441c0c011280c41c0600740790341450080f45c1911039491000401428012842c900610700a01021010075005044800c40303008004c0340c10b07040400c0420043c480c13509142080c24920000003500e058031035a40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 935696510 1250 935695260 935695307
    0x622080706121505300c1c112806080105010f050c0c0a18060f080a0212030f030f09190228090c030501060f0519050d021611030d 57
    0x40726001e4019203050240c4045502c00010301130b01c2e1014180c071002c6002c8a400c0200c1c5e1840070306a0950411680034840d60b00c01011900d40350340d80e00c0710461444404440040c0d5000c103107850281480280202584140303070441c170340f0001d0b13a03500c10700a017505450a44031740c07641c541e002941c031000c080c000c0c0c50000310f414440c140c42d680100300509981c2c0080c012a90b100646e0b80000d2140d0510741c0108070a02081c1b00c24042c07515542c0140400341940c00444040300307080042140c0d40f1884400040d105450000d071141c2401c40910456544111940c03141d50b407440c1001c0c842d003050704240c411000a100d00d0441d14120050301040b132610541c028207003031282402400141c4071003038410900c0f2038060790a000280b00000c0344100000b401c02902c012840b03603d40380004d8054201504410b05100c030030464441782030004207100040c0b103d14100a601c0e298001d207950b00a009092180d0300a8801c10801c006000038002114400c200071021600e0000a82508640b107011440340b46040c41e05c02d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 935697760 1250 935696510 935696537
    0x10f0b04030c0b09030f01050a0e01140402062b0504030f0807210b06390a051f060302060c01060f090e03031605090a060e0108010f0e180c0622080706 66
    0x80d0020000104010100c8941d52990340181e0b003148e0f0150b4485001603602c015090142d0400c1c014400240c5e0180c0c6080f00e03501e0305401107101ea100760b000150301c2400c942080c1c82d02c40002c1e0101110380f40341403410481407805203401b921040e10211003002103644403001030002803045a440740e28141c6408840403a99069a900024142c0c100400364800810b1009107101d004040500130041d19800740b84201d0380b0030448a011600ca07082ca200c800d42c200e80341480c081f40380010305203004180c07031342050700c00303510b5100c010000e00080d040294440400120003000000541004068a80c012840300d0310a54506202d01207600402d4650215003052000030644541d01200768804222070802d41c0c502020000001c5400800790072072008a0303e807090958013542d1101200f405000d500c04c04002c0300d410402401d03982d080061629030007040d00b00204040c11018071a515a004018101a841d003000c03040801c080420540e54111100001c02c0008450f000041c8040840e00c01c1e8464900e2600e22 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 935699010 1250 935697760 935697779
    0x30d03090201050415031a0901051c0618210206150f13050f0f072604051005070203040e060607021807030b13020a030b0a0f050d0c08030a08010f0b04030c 68
    0x96010a80c10f102d42480001005088001c0d01381503208140d44c00201517140b40711403840c010004100c680501400030050029031103804450751808081c030407140201d0001c2c90725101034415092860014202c61800c2d00c20050440c94003180c0c0801c007100d5a040c0c8400140490303841104a45d000c05100c0c1c41e42c490721140c00c0c0045991406c000c041e040c503806815040e407650649605035800900078010508201c44990140700319500989203103800211280c0d00c014514202c4840110f100340210294081002c0100801c2030840d03080030301e8401d210b580382000c1c0203516070b00070340f1035048404074680020321189410001c40d01001d0b402894108450f4416034000c8110700c0c014200c40034196070300c2610702c035070380c44114201e04090074003009a030308d0324110001000d8510210326680503185610040c40903005004c0201c0c1514000d481072800c03007a450428091040e400da1100000d400300040d91360145901c525090305031441c041c0c610300d141d540c8040305595813285100180969201c0b14042c001102c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 935700260 1250 935699010 935699021
    0x60a0f03052520010e0c0901081209040c2106051c02030303010e09121309060914071407020d050a0b070f090b090a051002100506040b030a11010306030b090d031a030d03 74
    0x4a106201e10f81100b0301007207030031161801c801a60760b500002540311985171600070f03039001d03040e150701070180c1c030001210400362030280c184a13030b1145881e00d452400140c89102c0403500c040c00881041441e100e11008540104660300541d8000c1368160100065896000d801c13242103079004c0c009610710703031900201c0c2101070401307004040240035411041c55a00740d08405844001e292003030a560320391521000800319031095008020290034600e20807041443c0d00c6040364003c07424180385203002c40f5035400750098461040c2c000d50010407083c104007030010008107242c11a10810750030120341c5661f1420303240035400030401c1001400781c101c04c1c040005c400014005428014008248282c0c40b0380c0000c0690f80e608402d0801640a00a00c8040d0240b80c090540c0200c400c0c0c3d03040207500d40e01703c0031a0300c4a00d07060001c1c20944008899050380d0740309a00010041da0091003020f120704049600d96140c01c0d201e02d418002074104440420700d60007a00d82d030340e18038070028010a180c40340c188056020300b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 935701510 1250 935700260 935700287
    0xc041404060207170d0213060309050c0904030e040603050606030d030b0922020a08010c080a06080304060818010e03070b07080f06091317091822050705060a0f030525 73
    0x7200802a4115440c4c11000b600407003240940c00f684410614140348401c00d0554490000c040c100403480010070b40100c0c043d88580c10540351781c40660b54601302500c06065000034140c00c140ba2540c000140940030038568041c120442c140d800019030640b0840c240c1d00c40c1c9071010340c0403004002143c8281817248051000b031481403690b5070809410f40009179000840e50140d00325035101c0c44102c2219502202d1190300c5a86c00c8010462182081c492540c2c80c040c5000e41c50a00c06040041403000039070009825407260140300900850700d0700d0907a95200e42010600721502c200103008540351600405110303200711140c1c04414256940c081c1081301102c006060001280c1c0790001520101d45080d02c48005c440c01c1070141359840315403000b030244410748210b0740700c02c81c618082803080c030002890014842e151010184000d4a03010709107a030500701d0031ba2110340c0c010310000d4004a480e0700103140c40340c02e40c0f058800f00542c0e90354040901941041000a074101d509069100040600600e024108d45 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 935702760 1250 935701510 935701523
    0xb060d0c03021309260d02090a0b0a031e0509100f14071e081b0c1c0f03140910020f12040f06050c0a02060a0b18070305090c041404060207 61
    0x40795290041160b00d9030010341102100d85800c2c4110038070810344800c00da075a80b0710450f003a8a44030300151015038001c40c0c070186007a03900002ca250003a43d030058204040d040703d420081d40c0e00031882002e0010000d41ca542c44510940079004090441390f8480d5510800b81d803405444a03500c000500001001c02c000b00c981c0180d81c5401800400c000c4410b280d2080c1d1644d254040d4500402100c0e2441079814a410301c20442c10000300044100381c07034400c0100b40f240c02d0441c1d072a42650004a800d000140c130109a45031000010104425445010102c03419000d48080000e02400d5131444040b0100311010f1400e1b80c80110b24080460a5500402c0c1808002070400d00707100310000720003810380302520140c802c10030842da03502c14032040344501e40c2c108144200d064540808008065103450000b0300d040b07262595880400029192281c044070303a120407400b1200c861400303103c090300408064465120912441c4500803040c1801d108014a4007a07042049c0506e6441e6075500f0080d510100080780e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 935704010 1250 935702760 935702783
    0x30810030b0f071b2d05120324060306090712020703021c080906070503070c1a1801020901021b0f0d050a1e0201050703030c0201110c0a060b06070b060d 67
    0x1c1800c07441c0d0940034040c0d81c62000c030103082508004200301d030503440011030101c1c42164040002d14043c85048203078164040e00582c000140740520713075800011009061405419007426414a030300c00154800c02c0b010008080900c6502d92005001c010481c3c0160801c5c0e0801c08250700f0724018142d00d03445552403500f22410345c21400300105a81200b00124050f901000c50b2410200340c0141d0304a1200d9140b6000b60302e0300e00070050682e2001c1c05407204050000000c0461340c0140704402040030940c20960480b80127003070a0b20501c841c2d80c21254086807245800c8550b05150041c003c6402c0100160300800c03102a9840c0c4404058058034002d039480446810a1070707482d101c1a4010380c6140c0100c01416850001782003c02036580001d40f6448140f42c00702a000c0141e070410280c4044503003520b00020410386401080c2d00401040340009103c801c0400c02040c201c01c0084c0c6560140e2281c5000d0141034280e100784003180c00b411800806030401c440000e82181042c9a500f4040360048035251311 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 935705260 1250 935704010 935704013
    0x1b08150f04110a02060a090c15050706090b0103030f0915030e07050907020c01110105010f06121805060612031309020f040b0301060302090901050d051518030309010f05010b070c0303081003 83
    0x803240c00400c2d0812000d004900715040c2c64050040540c06220030006001607079260f982d0941c2200e075030140003640340302200952315103442101510919540b115042280c2802406c02c8642c0240074031007140018062024070380054800c0040004507150072a81c8141c80e01c0d6184207601401000da04295940f00c1c0381c4000409603980215607010310b0090700070704014017111000421b00c04070198240ea10380c0c142001000b6000300d0256020031100145070502c030101482103142c001d005880c00707420308031b801000c91405115000c9a104e00981c0c046072030241240000c45607a883e400703900c5080303040980c2c0074810044100341c0e130000e240f40081c00b80c0c0c071854242c03512658840c5130400e03044600000c4c4c2c00b0880c10354904200800c1c501519045881c0d09104c242941d8142d51954940e41d81003c0740c15030004141324505c812100b0440d4041f81003500e440b4a0001d07091402403440c540441c801d582040000201840c1400c200e4481caa00700c00c0c0c0d840303038a065071410750b0750300005484104074880f540f00000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 935706510 1250 935705260 935705269
    0x209030a021e19150504030b070e0114180405060d0b010302060d1d0309010306060503091e030c0307031106070305091c0504050418020102060105030c06040513021209060403031b08150f 81
    0x440e0300c40c0c0c4080003d40d00745051214580c010307203c00000c0c40000c101c14400303e49107508a036803000c03039032810000b0703540d03444012180d403556040302030f48042010491154010480d611051102d0054904000340d0b5914820808611100000500314290100060001d030a010300144000c1c0d40303002d0701040e02041402e9604080d03d190500c0451500080751321205503a25010380c000519507854954154240b9000c16500c600442d1481146070342407005c04c03400c1307200a03c1a1225086250152910b0b41c0c514180074105181c0d4058002c1d090146100040380c0c10b00a100381e501460612006190510030003604c250345c0070f5200844014060b05010003c2c2039500c50064607030040b4080880c072641d0702d461001a192031810f800c050720079040031540902c907031113440950b02126021200307001d4403043c581c0034900a103c4c180c3c80c2d050303030130b4a5003c018184100288003405244642d03410044120f003001401964694045031320001030351a0041902028070741c02c200e00484008200d05a450184400174 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 935707760 1250 935706510 935706529
    0xb10141509030d1701060309110d0303090206040602340329130b07030c1e030204030602040f180509150403030e25050a032105070f060f0b0102010209030a021e 70
    0x14000130b60160703103800b000442c1501560051034642000d0000c1145551251040505400811b0046c4480641c00c01810b2280d000314007502e4002d0411507685444560003526680c020a29644d1095044800441050391014003c0b03100b001e0300c41e80059a00719a07480346c084401c1c010715284e1145070120b04480c0c01d08100c1503401248500c0014420345203515040c544403800500040c00c0c50f1a00305111025600441206500040c2d00d01d141106500040309030f00a004036000034000d01e101240100e8075581124088083d2a8070040034a401c1002c16001c20642d00100c0b040041d030340003907240201031002ea5202540003803003400c001c500e1200011501d1f2500541c03040c0c074100d00c903150f002032018015450a5001400f4103807100842c0e507080d515218000500502c158458030885000428058450b0082e52402e9a01023903410181e0300c241004009000c2d00a03026101500d4035114200035070051084441080c0098081c0034040308580030407003504541c81c0c090b00000c1c1a06181c0d0900c0d80c0d1044034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 935709010 1250 935707760 935707783
    0x325060503100e0c04050405090a0c0501080a0f060e33190302030102070308071b0803012303120406030f0902130b040209040c050d061d0c0d0204030f06090b1014150903 74
    0x42c25142e03407406c010030040d644050204405034001040032404038610340103090980380b0070708050210352034124500b070080c2400112041d80c00d141180201b05a4480c4180502905d1151201404050501ea44060ba5114070b403520140d1982050100c0042c28542c009042c0c6d0228a400010110380d42d4000c2420383c4cac03100d40d0490000c0c282c0c0d400c201c58140c205056101f88040000035003d0030301070b0b80e030f003624503c810f0141c0703881c208050030214550015101d801010701400f83c16105000c5c00d10f4880c40c00340e0003501840000c603082c0000d08403080e10342d1285820301130b00100f68403900b0100500c011300070401c100d003040e00306070204404412038440f8080c803140e40d03040d82e640643d10340e80b443c85d0f41c0480d085504008140d045040e1401c412103441642907400c81030100b0304959901401450300d0082c8910b600007007000d51001c40038400e12a56a110b00d0a05010341d6400c003e41e034900c0599000e101240c0111441c40c2c5041c80b091a141c01c100040384a0800c09450a500d44901170000074980040f010300c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 935710260 1250 935709010 935709031
    0x311040b031501110706140d0e010e0f071409060f010905030102030c12010b0721170109021c05012d0519051002060403120c05070f0803060325060503100e 68
    0x302000310f5a1140000325420380001c040c0102d5420880010809600c3d414210203040c80412010b5680842d94002c106c8120804002c2064813801040d0586440f01c1180c580c8650250140000b0380e04c6600407d0041d40000030704840c01aa140c2c000c108640c100440301d18100800d011002c929514244011806003000c54642d0380c880c650544407503103a000581003c400307010180314102c0050b5a401c0d0036a411098034604482142c1c1040003200e11002d8440072140640e804800002c0c800801e174020b2498109401d2448101d081d050021016941c0a210303244004c0c0910403207200c1d01210740c424030a521811450451002da0301ca0008a81c130b0b41c054042c00c03a2025000080109103030445804040070800d001900c06480e05840180c151001044e110f0036481d1204002d401c060300c14400c44000030340c80201d00c0107924550906c0342554100301c80580c06403141034405506820103200103070342e9079542408080000e00b040804c41d443d420240001206c0301480c00c1c08202020795154080c4104003c01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 935711510 1250 935710260 935710291
    0x150f0d0501090b2e0c080c060a0f0501290d06170d020d02070e060d020a08010f0c02070501020a08030114010306051e1302040e06010c031215050a05040c02030a0311040b03 75
    0x6013000300c0200c42100b20704100c6000000b0824000c01c084610341c1d20243e50916001e02d14460600c4101da01c40c8640000700380c0508020071400d429540d000f00300381c0701040320801071685c0780ca80b845890391018491640081e5403415204206045000812074000c13000400308805a031100c003507000c0c3c1410356030120b803a045030b40380007141941040102c8180c7c0e00ea00c01802c4007403801c40c00c07608201c400b521160251200c0e10f6524155110b400259009003411b4008219038400e8a800328010440d480c41c890040c0164080001c0d10f610010715a065140c00414191469180581d00f010b080c1c0d03080f001c1418180c03036180003e111394a4040c030340c0416a11300c0190003241da0400802051011102c1c0041c44144140f00611661000002c615031000c42170810b0004101281810384400281c00311003c403080c00d00415440e100603501d400b0045501c2554480b00140d2201c082000759520408030b4001a0700c1031042a0ba00ea109800c4030741280406034003649006d486504011190344102c50010080c01c101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 935712760 1250 935711510 935711531
    0xb0a1508151609150323010311090c03071d04090813170601060e090702010b0a08011a040c0807080411131d010b100302090a2105100605150f0d050109 66
    0xc1c03a02c10300701e50281c40e000200394100788202003200400c540e14030406941d00260082140c2034003400801c0c0ca64002d02d0b06d410b683da40380444000003640302c4140907071181404034007040d200c0c07410344e1701a2031280c840701d80707400e41d0006d446500f4524040351540a9140c40016010a82c403100400aca800d10098482d00281003105e070000c0c1e03000c01049003a80da4461001002103a03030284550b001d00d2411034000c051902c5442c0c1c2240941826105a0340c007540f0485c000413007120550091115400300c800d90140d503020b407810042141c0741e04240c10f0204019500143e182c82c414500345521502c40c28078641c0022131880402c1141c041c0204103040780e03564082c001441c00d40c80326240f0406010300001d110100d10607003c610556400d05403181455000b040620155440c00c4200d009416407101c0c0d4654108032035064006020302a0707050740e40703005030740341081d20584038050740c4180d8070041c1649451000c0d00d400d00e4a258459030780500c1d404003c0c418408040c1d514000c45008110088c404142c040e401d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 935714010 1250 935712760 935712781
    0x50d08070c064b0302121017032d0c060906011d060307031403041e030c051f050702130e0f0618120915040905040605060402070b0a150815 61
    0x600f40c00b0180e411410120b0314114551500c404414002d5400d048860020380b50590182c0100303445942c41d03080c140100500703a90800301c00804c54800402402098000c012400c3d100d01c6181301c0100d110802020301d5501e0200700c2c2c5481701c00340d115500301f07141001c484c078924203205058070b6807141c0b44c000c0c2004028110108042d52400d04111610388428180300c2c0c0025592100f0b48001400c0440107203000d8500402417003628001c0400284500501f2034408407a43e100b6400d001c1158400800e000110300e606008011010800440084104107600075509580344c1d0040031b000c0341c1c0a440c41041c0291b0341180e0044420b081032103c024040082041c00080c1481c0000304054586240100643c1d42c80e0170002e5601c08441a01d0b500c29a0740d010701c0701040760480da582030150500c03800503001854105c6540091311681c0038070740411042c4c640d10200420791090740070103090581c1000114900742d0407136200c01036403459204c0307500902c1d654080036410004800509400b120302101001700b03280703a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 935715260 1250 935714010 935714057
    0x112050c010e010c030f181d0a0b06040b030a111b061b0a0e03100c1e02010c0e1c2009060603040201020601030f0c08070b07020f1504050d08070c06 65
    0x42401c002c01c0e06042a00000c0100f41514405001c101c8241c045402250050105000009200c000b0700000c0d40c072500030340c10000c45000030b407110210340320000741d000400b4400d08400e1203005010794649850007240c0c1d01183c00181ca280011a035540c1880c2030040d9060040c02c2044620780e40e9500e50400341402d50030b1000003805078210003004a0a999058500e1040700c50100b4103062130b0100207003180102e80760610b00807404096500d0724003202142230b00400640030020001d50fa10001d10a01c0c0340480c01d03914046007060110b40300d600c0c1102c05280c0441a1080d05041590600d8034050948441300b45021062400200307890404010070315080062444c0d42c030602c29039040d807a504040d40001d6445a051001610288003c40b00c1001c02417800b030300d2001044000216054992141d0400030142e1102100f20301c52140e0710420f140a00b006034a00501c10500d004190506245c041070000c4238000080844d00020100715560000e01651100b40c05450107a0381d18025907019104200e1024 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 935716510 1250 935715260 935715283
    0x150306161d011209050a02090a090b01120c03061a04290616020d14030304061a0306191503051005010512070e060d0201170f04020907050a0504030f1a011205 69
    0x481c9004044035503604907500c140d0034001580300080e809400c1c100300781000c58500d0001d50000804042c80250714194010101b80350042a464071076907a206010710f001b5035001c00040c60403c51200c10004034089a12001c080c840c440031881c000e00a102c009404c6680e00c2044000c0e000b165950766400150100d44120034100a5507031380e25086a054240c000c58450b103100038860aa5094030340c00304020100d00e607250059980c200ca031a8103062405a000d0021030069410121104580c19150718000503900d00500030345404008501c00d6410441c09013400e00209041c00e4108103002002407000c10450800d00d23030034100003078194100820485040079000d01c1601c1039120300c400b44400606400e2142e00040300700c84401c240c402510041e220b4045001e842c1840c903020f0410080c0c1c4408002c800c500c00c2d8421030f480050b61307595500c180c4003400342c034206c030740025000e020a00006015a151100f0039000c0c8400012201a8003100b66a0b136100340c0180195074a00010941006800c000807071004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 935717760 1250 935716510 935716547
    0x150103091a0406061a0f0a05070212030715020304080a0e0102070b0c0c09091f022d0a1713020d15051f0807030210180911071103120f0315030616 64
    0x170909990a16107409607410303420420b00d0009005a5150180c030440d4020750380505503030621015000010740700d4001160940b208980d21000c8852a031441c42140c0c8141e50040080b030424480e140116a144c0721115a00d040d07100c2d60802007411070702e01024003d41c512100040442c03040034070038404031700c001910000302e6074412442031422280c113059922000c80c0f421001600c1349202181d002034107102d100303d69098541c007221000810440001011200503d0325040070076500c0400520f065070f42110701d9051089100e1000c401460640d074940301040c0586d10754600e41810320084800c0702c0090f520a06401814040789004407144200c100081c42044060300d00139185402141021030051100010000789002900c2901401d0051601909244d0801c001013001140341441c07540c01300101381c6454000304d205521510b40002c0000c14084040c042c1828415034004a090981010307011515281c03006188074481e4a04014680c89404036030f07140a4126042c50000c0d00c8080a1805c10044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 935719010 1250 935717760 935717789
    0x603410c1f05030106052d0a320c0111040806092116021309260c0c09101d242d06040b1206030d0206150103091a040606 53
    0x8198002d01074074115111414840d50f6a0160070980d4543d564119801c00c0074070b20745000717600d200307241d0b00900004403403510b40c00c40c4120004100141040000c0240e4900f1b111030a00703a500b81c6003680070b000b008810f1000070505038001202d00702c0c2c07a00309410510320b503072140040140a01c0e040002e1070100040c0da080004505295182d8100d5200b881d1403960711580c00c0200070119211501c401002410030b000401c0f54010702e16000e05042104102c20003c040c040c0011035a00034524222100042c01c40001c1c6a584903042c180301549100428407a004510b000000400809040e030045001c0c201c015821024075140c10003914070003505d1002181482441e2202a15807501050302003a840076501c0464102069012140a074008029060300720f00e02060018840707103107002426902d4182d40042050790b03103d4042c5039450700303400c040b2070041e840000400e02c039a6441c80240c9a60106140205903032850f40c8406e20820b10440102c810503040d0300401060160512400d40600340c221080b860 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 935720260 1250 935719010 935719069
    0x30f0218091c0509060c10060b1c050c040b0304030503340c1b0e0103020a060e01020a0b0a0b0409050c0117070c15060f03051f0603410c 60
    0x1541e0100328010202041e241c150808158011800d60301388007401092195915034201507035445588089801d00322a05016011030002100302c01d4403212000e0795041100c0302044c00d0002c0c003801003d4000c1407050340400010030040c00560085128a010b0380303545230b40b41891040e000031508240040d01c20a56500c81c20b0205ca02d400d5a646440540c1d4580750700c101c2d040c1d06090010010400200c1050905100c1c0040c00000800d80386040381e00032503504004c50b5440105a03441c6d00c140d01002d00680101aa01001401896603a42c022402d6100004c004100c43c001c54112000c5010507a034036807165189503015a88151895501071407001d00300c0550034020740c0545401440da900a120300160b41e03031580701c8105070340a00d0091035040140d0001030783d24100b840e182c02088031800841c164400081c0c0804110380a10030440c0e030300c18809020742107180b2419161022440b8102d5170b8410250640c0a88401c10443c0c0311810b0380203020f0468681c25108025510444003000711401c18110450030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 935721510 1250 935720260 935720263
    0x20307170405130218040204060c0c15090e10030b010b03180706080a0b13180b07021516030f110d06060c08390303040309060c02220902040501030f021809 68
    0x202000031070f009a1a10b0b5146103040c0c400015464140c0c1151000c9400561140d00c0210418006d02880007840c0d0300b92217201c1040400780f480c4c41440881c0f05104104851409440d00503840341ea2000002c003000c0d00c03a0f4802c01041800e0780071180c0796001000340000010103001103662040d0080082c0085407620002400705940105002001d617515109012252210003c0603520600b09200b0041d091500007081e40703015491a0a56a49003010001802c2c01e0002500200d0901c0c01c10741c1641a65503514020b0200800e80164006c064907283d014414a0700d034050400000c0e0b55a10540e2603d6444003040b0441c2c09681c428001c01c0046048103010626003000c0300c182800080d040103101066000d16074460202882d21071103090b074901e000c14100c401202031801288203590703441d855540c1d0013040f10444100b44001e03600c0303c403503055084010101075910f030392601d04039408107981c0e501e500081e0032600240c4c4149c80d119580500742c0114501440c4004007042000000c038202d060003002c0e00e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 935722760 1250 935721510 935721529
    0x31b1306031104091107050c010813111807020109050c0a0522020403050d020c130b060904051510030608010501050108040f08031312030e061501020a08030613060303020307170405 79
    0x8401e0641d154514030101d00b200c1c2c00c503006081e100e8014000e54182458980555101030030640e414007802550207403d6200d01b103c0c2c0d000c1c10381c02040007000755042e00c41c9100400d0034034900d0384c0f10540304002c21400c0340000c08544501c0040c1c000240ba440542013440c203001c0c007481028412003908000780308a0392a42c440503507080006401507410518030030408000d00ca103410240041c8074014807131000c0382c0d0006280410200079216500702c0500100e07180d00350342c0038022940d4441024403108000e030406a1105902200702c1010120b1910244e02140300166480d1022000039110402030090382c009014942c0140000e107030040e030740d03e040d46800394000340032000245002070010104031410406601d220301c041d004400c0000e280010f980150062502041c40e500c02d0140d40c000484021213110f0b690384c84041a0050b204890580d0780f08406075100034481d030351080e040c415644040783c4901c00c1c54040c5101e82c004541e506940e040055841c024000c0300b07007009000b040705100c0f43e00c2e004a003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 935724010 1250 935722760 935722769
    0x4050d11030f0f0708120910111c0c1e0c030207080d0507080f070605010902120609150d0201020106180e1216060506030a0b0f01050f0429012003031b13 67
    0x41070749079640e0b40f4050a2600c03d0980c0c88211804006c24050441c90109034a000104495010050045418003000c0303130707005140400500744003c14001d40f50407030a400c464194030340f030300d0481d64051044050074a85030407540364100041026101c00304141c1c0400c5024040c20704e00000340709092803008014424070800d1002001d80d40f003ca458680200341c074040d01c420b01d6102009201a607100d0400500a40090905a0107054040040783d031f9802d0100c9810300803003e04001e416011010f80038480c3c560b1116004a0441d0750f1420300140c3c0d03a0a104180101d5140c1c88400300c0c0c41c3c1c0c40612400d150041d0421300a074400303001c00c8404520918480201841640140085041d0340c2d401d0005c1c1c240004100003801c800b01c420200000d14130f403051418141c0c4d2007150901c03d629031420600044440e48212a4040480302d02e0803500c512000ca4003041c409814541105414104003003031401c00391900c00f07480e07590300100500c01c611010342010310400100211950520140030045208280075224 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 935725260 1250 935724010 935724037
    0x3061c0b01121a090a0c060c200d0c0305030901030617062d07110f0a081c02040506160209070804051e0c0a0b0d06170604030f0c0b04050d11030f 64
    0x2040c00300814403c40c2c11404100c0c51000003d840c010043c80e448440326103045810b42841e503008940c46004010030510b040e0060390358211130f002c803006810629500c14805a01a01049500002440c040c44a502461003070b07029545440d100c20000d070030f80d0055042082c0d55103d083e1424010980010000e900090040512018140c000d0301d0780b4010f5001c1c00c1a900740e103410b000f04031410380c00c414a0310304101020102d90303400707034448519900d840280a0007807003044c1c2002020320030907404074029561520404014035281d0340701c001580980c020341c103e0031b000420000d05015841c2c09070300e060340300c08542030450320b81c03515a0310f043d12030994100d1010315114002107480300000c1044010801480584a8508691a040c000c4580e40222803494410f504007400401d0450300346800500c2010300c040206001d44482c2c0e001d8650b00e0999005404118055980f070003c1444408464003e900071409000b80084424000309048801811a2060380c010400c1650904840c411180582131002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 935726510 1250 935725260 935725289
    0x1021e1c020a1e020c091620070905011205010e0102040b0f030901060b040f090e030702030d05030a0906090c05030d0c03051615020c06010e01140603010b0f13030803061c0b01 77
    0x7035003510400b044001890f01d24040200401c003c07500000c0205880101311031150342a510724101d8031408546400780e600207042002080820070f00e848040300124070650680f507401c2d441d04510700c00c80c0d50913803016602040521080080c0a4284120f004202c0100000d41ca003d0502032102d18501c00c05106400c01e6400000080300300c41d0031f44c00f00c0050308080104907600c0e80c0d01d030840040307101c00e4010004e05928004601c51003071000012074003055400307400b902c1e004100c5042503500c2d03040288504d411544901c038000001c0e180748540d1442c94896482032031242e050409052901141418640c184003542c1c8028021a82003000e07a400c00700e5280782d43e810103070f00749007039242c2407400c0340c1d61040d8500100e00380c0c0404d0004615181a40c076030558220030f0b0707a680c08407505c000c0c010040e181cae008041000148840440c44000b000c0c4141d0300740002389044429154484102260b500680344040c003c42444a940ba08502250064480010f000384441290f02e816004a006200f500c41512612 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 935727760 1250 935726510 935726527
    0xf081b0f04140a02180102061504050417030907030c0518041e3002060c07061104050d0f023a030e0d03020d1b0302060610120c0201021e1c02 62
    0x340c10242e03640c25448040c0c2254148004820042c0d08405107054a0811350b6003900402c5d440054090b10640356032805402c520441c0b01800700501e00074100340d8542000ca4890103142c0d84000041d402940041c000300741541c51824a8035110740da94000d18440e02002d000710214140800155402c0f42c1c10900d1100030105c591710b8411110706456000b04110741c148420315007010107517a400da50450681e03080701e01c814800800c90729040215185451a0014400030f8041210755001c8000221060709942c60143c80e00005450007006800c202e401d080ca4141800c21400c0c4039050036030401c101b040e1408e601c0b40c040c000c6003218440d030812140044801c03000d00306162249515460050014142861421590500a484580d81050900424807030300f145d0300d030610085600704016406a0151030191035a508024070004041143e6082065520b0116030780b21070f611034440c581c49603130001a90b8030350041b5034a03070810900b002c58041c88005e0080c0d07100c3c284641c0e00d0b04176182007481e0050355501d92 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 935729010 1250 935727760 935727769
    0x6090605092b061506020309091801060509130507060e0a03081c020301030819210e07030204050c04090f0b1852090b0a031d03040f081b0f 61
    0x4048a102254080c1020403e000030740d0310031a04041162000e034925030311880240e0b40d074420a8040307500310f170060b00010700f0030001010710410034504500100d07019a40d070000a071021015a4001a0b80d903c422a050410004003e540c0c004c0009041c60001c0d81034030000030304400000c2c8000b608580c0005900008015200844042d045410004540340c0d41c403070134101010b40003003001c62000c0f03480c6d00c02f41200341d013381c4940c03860034078030003110700240414014030014000c5282c0048180c880c0ca100400140d4580c05005d01c02c911500a440e116460040440107072000008400807492600c02c6244054890340300759040710f0300751211180c294903441c000390702c14030700000102e840d00040303900410400c91562070b01038548242c02442c401c0380240380802c01020014810032020900c090810404490344401800c0144424100025007020350790950b8482110b01c400c5139403e0300b000a085c08022661140003025003d04001411083c07201c4916401202c6100d00442c8140c1d004400c130700c440c0d80c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 935730260 1250 935729010 935729059
    0x90207050316050a050f06040c210611030a0b09240a030611040302040b06031e15060714210307030b1201090c050f0f0303030a0b0d020a080a0c0609060509 68
    0x2615002c220300010a0401d180c4075182c0c98400c8400c0e000304080070a03100030000d106801540c100040c0380095261030f50303405403d45030310040f64691011403480408640c3c144a1101a4011186255628a0018600341c11030304c0d413210642c414000c045c203100541140040301d480707950180c41c942000c100c40100156220040d50701c020201d0f824200d0368200120b04401420859100756014045c150b0504100049401f0450b1303d0806950034210000355004d00817000c0da00980c04e4682e01d0b80c8203060001103100c6a001405c103440396060241c0b154040c0400b0041822620075150459200d065800123142c403500c4040d0540c8201a1a080d10040b1940d85604041c9075001d00002004a50018500212805094841ea030721440262005041e541040103c403040080003d01561071a9641d008440080c84000c106a80102031501c8c0c510051300d07002e03021750180c07510400a09000045190000c1d060340305801c21010885520000c0201540003001d81d08986012034004012208401c1041262039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 935731510 1250 935730260 935730277
    0x20d0e1201090b010b0703080106030509150423070806010501030902030312090309061c05070e10050723060a11280309060f02070510200706111206091503070902070503 74
    0x343c00400000c4584807500141101407080d1101c440e036a0740c0d00b01c2901250700031038940c0060b03041189041881c081a204c019401407003000e1904050320103032460103940c9418143da4070154003c900511119404020040c01031500b4039040c407800c5202c3c0e003c03c1d2a8082d88150340c00c40c0008101054840c44107006075000594098142a01c40b81e0142c4400310030004142c040d10001d26220106083c0d80c800d50718250004409021981c49a0400c1c00480e055400110255844203d0b824078002240d0031541c030703c01500102000300500c1c1407244019084034030550840c00c3c221020000e401080088044491110030310303500203418182e5103074003038016000411004282c145440039100300e03080e00740d002d00031a901800450b04c41480c02e20080084a041445581040c035420500c50341005001e0003d01c5200c0c411240841c540c0244281d000076900080000d60003010b0f580c08010071400c02254850f400766007501c030024200010404251910703900e000d070f09005500001da510a001d010803c98503120b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 935732760 1250 935731510 935731523
    0x11091207030614160801030209010b0906091005031609140904150501230315010504110c19061427150103080c010c020601150e01030e030d0b0f01020d0e120109 70
    0x1e4100100d10fa81443c03045482c00580384580414207003140c4034400315416698044c0001c04281d0800d40c280f8941c0c1c20503019550b105004100c03e0840f41c803601d405680142d540d4594640300d091242c42c1208042545250310b04110500390308101e081001504411461400e6900c0100e40d02c0307d0501c00c001403480041081420700300400007505080e80c1d40720b09a400c6408502000d0004400304241d01d554035100302104540080005002915281d402400c1c60002030350b40c1072420000801903414400410290700c01441d8034280318080c4826070080e1501d00d4080510150585001c210841d40b17945030f04804a894610683c140701134980070054108007280c5142d0612066a586c5040c1d102648680940c2007207509102c2c034901004d0002034a50b060344c0321a06d90780c2c06501d4540341100d50130b5100d10002e0403d91a005044880041400244a42c004c0d0b210003241c3c1d030b04040240528650000710150440d80000d8411440c2da51107108880c10b000110b40f0b281e5040404080280500700074180078000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 935734010 1250 935732760 935732771
    0x601050d092f0f04110c07030305030604050a2a110304030807060e0106031e0201180602010506010314060a03060f140903121006050405040e1002040b1c110912070306 73
    0x500840702e0520003001c18940360b81c540c0b02e4019400d24900303284010416080003240ea44030405103400d420901800c0c0c12410340300d01b060280c009143c580304450b401980450000014807900c1d00345409850781c0092011b400b840300003007801c0300c0d082044a00030014a2030040904140800f8450100b400d601a4030701c085944407034580c101192070317901a000869095140041d000b0350310710107008007402c4030303081040440e40e040906a00442403d9100c012810041d103001c5605000b00c3e5034502c1d0011f0310482c0d0000409182403000503084034003030b44d41e00200c030840b0820400c0c5507807103420003170070340354410004104800c080c03500501a0401d011440c00e4074400c1000c02c080d00c0000006001c0c0309034240000303d800d80b0341e4080522480400d0107800000740b0204014441424190040162040144d00b2180350b400c920020380101d800c0303500112014400002c1074503003440c01d03004100540480240c1040881d4005404055610900b031105000c0d06120303050b17480000301800000700540d0014024800c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 935735260 1250 935734010 935734013
    0x31211070825290c0309040219020606120316080c0f0a23030702061809070f1805130c1b110a09050610030e07081501030c0605031506030601050d09 65
    0x103206014841d10005084040b20000300c404416205041c0c06070040c90090b055520070f00c58802583c0001d940c030020744010040c003040c40c0ca6501c01840c4001811203035000390240c1d110000d00b4110041c02d85413250a410310950101e8402000300d41c22801c005030034100c03141d44e072304c0c0c010760301e0048801041250059080789805000d020866800340c138458040800542030f011040c4021407400e1700c10b17100d0340d4000e024240042c1082c01c001d0417220400704e409005584020005011100100c030700700000362900c03040d001d060760802d203900b0b860000161560f20260030200407504d07a0998035409840d0503140d204099540c0d028401020700b01c8190580001822058180030203c0c001400806001e0380c400100024485181c1c4201c1e0301035200180000c03600044001d00720060f10942d8030750310340c03402100800aa2854108000300c4030f400c1b8035511400c0c5602d103040c205140810f0358090010302c20f003041002031000b4900051050130600711083c40d12034032040c1c0100c0e800c6c011520b18007207061501f545d510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 935736510 1250 935735260 935735293
    0xc0603051008031801020c010c03080105090a0207150b04150e040213200307140a08041b18140108160312030605060a050c330a0b1c030f08010312110708 67
    0x500c4131600381c086607814070485004480000b030014000c1c4c00601c5070001440180342040105d5001111008058180380f446e0302c425545500c05503c841100e035803010a1242c50506004a281e81180d02c2a2120039501d0603024042000000740020f100b00300c1c003410000c41020b250700242101c0c14284002c0c0400884101e81d08580e401500e10b080072038600e008070501c408021040741c3c1d0a04c080d9958900940715513445544062045402c10f01c0d030010104049040f0070310021079007222441320008105404d284c2942d41d011175040c0c00c820380c0d9070007002c1790446000241104100301c0707034003007004c1480c414860000c0300108079603000036501c07940001310a0702107a0b005001c2c00700d46030f403227050312888100403025001d40c18080c280c040110804000c824448000118600d9010f414281c0c00714844880d0000a0100340c615185107001c901c1030f00c080024140d10a9a00c01c0030a902e00b40041d4030b50454559001224a00c03801d0780801c810312075805446041030114800a18000b02124010560743da80c03c17 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 935737760 1250 935736510 935736547
    0xa061407050610140409080a0c0309050915090108030c120d02160b0108060f1b070c030c091b0206040503030604090515090624060a0522080c09060d0c060305100803 72
    0xd401c03035080820713026110320b00351040140306548000c1062800702e5908066400c2c503039600d0160f05000c144900081c81c2d445004070581b04001c44018607da030100081045060041a0030562183c3d04c2030091211014002038140c080b8402122100c1e00c41e415115108040d11942713214043e101c220716a100c0400c064807080506848240301510156500c140702e40043c608103d81800c0001d1400342120340d0a0b103240300a0031040e0080352151102038403030301c0e0b04044117602d0b400001a03e965030f12030841242c510b00c5400d61281e55101401c001e00b843e07240d00c2d44c1c81c0005001244103136a80e09c40803041080c200100340210b19203864080706460722480c001c2e21380404543c0020510003000d8a0540a29005c0c94000040d100402440c18184030603800ca03000c0c1c210051598a1b503c23500380340c40d80b50358900f00800080440704000d1040074166014881c0324400a070149000340e00302400d11001440c41020a020780f1001e02c0d00150781d9036000440000c540c3c803948180c04c540800a21400001c01e210107a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 935739010 1250 935737760 935737769
    0x801050103050f070f0f050c03040e01170a0507031e0218040507050103151509180c0f05032e1203091e0b180103021314040b0105090a061407050610 65
    0x200240d9850515800c4204411210240012000312a69100c14003c078225031035021b00386840ca090a42000d01e03246550301c01e410000160315500010046440000c0d0004410b43c2110301501c265145a510150b0792070880c0002006001c44030502c15503540e0081c0e15500303d580080c401480114081c1158030007007000d0320280c0d040d000d074100c00300b86035020b8060b410a81060040c0400c90510700310b241e400f0040910480c204012500400288482c0d10141440d089010121700042003c45000080d24400d418140d00741400350910402c2044a0314256803462005e000d8400c2030508038070100d44e260700225400c50190841700c0e4050405050f8001140000e40e070848080c115031280c41c10503811015420720500d11120300c04c1120224000c0030000e002c00c111818100581022110324440140d1030050700184141d0148056a00d124940f078003074858503920a00b0083d281111410101c1c0440c2c50f94040e2200740201450000c4410031420100c815071034010307050f1001d5003050039942c2ca610308507110303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 935740260 1250 935739010 935739017
    0x1511070b0a060f05040b0301180305040e090105191d100204080c090103050d110a1a070210200c0c090a1407050c03091507050109030e130605031011070c0608010501 72
    0x10307207480340500c82d00099456443c681d030815460801040054200317009a2038165403583e4650404489c00c0764031807010380c801c0c1c503416241c6017061452681000010180d0a180e03042c6014003031115144154103201d060072000208c4c001200c40e1f00d030030507a001071002c410a0b100d445074542c000c81142c0d000c0c00542c1c010000780d071001c2107110200f088245084c003024295801c820b24014011f4050056540d0310a0b1807000e841000706680c0718800303901c1c0c00040005a8401c03520800020b035905000c94030301420329141c10800c3d02c10042218110040e4256070240c0b20307900140d00440888200465040040000d003c4485454001c810501600c0c0b03c86000308010707140d401041c0c21034054015a0440d01d0224011800e01d41041700700020750101e030740b807145008801c01001000c02c20070301038540014020303100d82061142420600c00b2003112061052002d82c40c120090025a9001c9085184516000408542443d5100380118980b2074080001c3c0003540340900000c00b141c0121a242c1240ea0988 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 935741510 1250 935740260 935740283
    0x7080402031c0305102319080616030507030e1f020d0905150f1e0c07020d050f060c0f031506040807060c06050604020708070b071209031d0414010e04151107 69
    0x1031010481803040d110350311022018800e01c0e0024200010081c00910303040c400d0030301855581c88c0d45420488103840c1070404658510240750a1038044c040e80342c00c4841c86c90108044102c9540490329180c5c2c02e00a800700d007500d240c40001400c10703601581d10f03580464000300403050032468000e550f024150a20100c6148680024001d094120302d13aa10130307400300e000c880d01d290189804286000c0010543c1e0038440d424007a11015898800e4035010082c8242c0007041c032400e802ca031046c50204020001d02c040c80b402c024601d00f01140100f601d81001e20b0505414250140e80700066450040b50040340562044a10029900b0391041b03031b030702c2c03482d0144104010603140d4200703000513480391100150200b18204030ba2400078690200e26603100841e40380c1520100e170514100c40c25582101010f038002207a001c0ca84019038091010340d200803508607400c010204200c020000d0301c0c1c20512a0a100031042070005080c42540b10002442020b003071343c2080341214101003d10507802c4040159510000007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 935742760 1250 935741510 935741519
    0x10080a06080303190c0306030c0e150303030106050703050c010e0f07030c050406030f0206221707170c0d0c0b07030305072613030509060d060510050301060807080402031c030510 78
    0x8001c59020390140c1401110544d29008450003070300e01000da040c10999140380002c04108070209201c060070072240e001c2c2c42030810702c860a02200081904c1c3d8825001000100901a0840c08880c4440ea1508200342c0311100e500720540107020a6091081d1405084600350b029100800c211090b0b91042908402d8a030b1a4000d1104480c080e002c02001030080f030b0300080140c5000c502901513180c40c075031a450f84175642c420300c921060180e031211403000107140684040010501c21320018201440207240040d036040885a5150010982030380104401c03a5200c0c1030054540300c83e4090941402080d0791a0000e1400600a00f41202d41d00001190801c150b0f0502c3c02c003407422020f0310039014070503aa54542d20510000e06c00002d80481c18000b040003111003c1d00e401c4050410b140903240d001403410f00c1e01051002c10384c11011003104000040005001c4c1c590005407980d048500e03482d01007880e076070300c1c404a880c00750000d0121840d01908211a20b2407549900082d11a05c0510440d080b581e998 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 935744010 1250 935742760 935742763
    0x2040501120201080f06061e13030305090f0f060d0b210303040201090e040b0a05070e0a08060603010606091a030c0904020c160602011104050609010c0b0f04030e0904200f10080a0608 80
    0x5a039102e80c07000c010011559001405c230148001d4100754081246041d9540551020503041a4400c80101e64042510240c0d4541580e400c0a805419983c0b5100171341e801001818074483c0802001015580328090388240d01c9540044011544000d0704d80d00e0003001c83d00c1c2c6079890704103c030100c0c00900342c143c002c00e580400d180f0303c0703000c0d82d030240c6040100d4807041c444901400307000f032222003001410706010b1000d0f41c0310062a4010700e40b41001d0307c141d003003510a00d82500e5568103d042801610602007021810603184130f02c8402102e00b1480d10313030719842c000030040c1c4110019181d015002081d81c4a9144006c10000c0790000100560b902c0a43d66000c11b070700b82e81a1340411140d40b13005010410031800c06500030003c41c101450001d4913840ca5a54003000d94506480e01d40080480008010426820649020f00320340c089440c40c000f1b25140d512072404500b03111032004101341c50002c1a0598a03030000c0300304c0d402001003052409006000e00149090000c440d103400e098200180060170140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 935745260 1250 935744010 935744041
    0xe01050114120a150306060f0e06010c060c0e0a23031c080907050a03120207061704060b191d060f01270306020a0906020f151308070204050112020108 66
    0xc046441d42408031035040020407000040422200301c0d00c82042044400b0000212006140309110005d416410010b17150745841132908a412520045030a12406e1303a00241c2c0d80d03c099078002c6000c5508564038904588500304502040c2d00441e01c040f01080e603d190940c4c41c1043c08103119030150208660b8200341d41e030950000310b0307200c20041980406090348502c03111a8040010011a05c07042d81e110049a0038011650041d031350708802d65512604c40d581406260001d150516000c4080c01c8042001150800003178001044541e6440c0e101945455400c882c110361b401150001850030741e10000e0004480c032481807000039400900001c1c40901d412a14070b0b00d111810303950070040100c15240c52500442c604030307490f400c024011000001424a00052281400c0f0b0368402000c2403500101138601541007000b10030a13001b010741c16840c0704500c1c1110341d00501d01740f1955071a5005040c0b201841c400c03450081e4220f820300c800070a142c805214180191071013aa80e500c81d076612820b00032807001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 935746510 1250 935745260 935745287
    0x114010b0d0207290105031b03031207030e011d01230a0207080f04091d031804230a0501031b0605040608061c050703060f11030105150c0a06060e010501 67
    0x900c10300c031a03080d08032658050600b09109a035410400c040b14071104aa0400c031108104a040e010001070145003810f0001c0050442c10b149a041400d41500c00280c40b07001d030f191030000b801c18440c00a0b581600c00e410072100f42e038044000700f00c0340c149520103c0e80d10204201a91081d801c00f600c03044190f400340e801a81800d400d5000e000c01e178460884000195003c0a829640104103000c2000444502c5000f032000f01418280041c4c094500c024083c0b030118400e0b00c108594105101600c181a10300120100703907441200d0021760740c1c4107a2402d00c000c030749014048142010700b80030024002101ea008505a9010b000208040e0b2031100200c41d000f000c034060180056402e100410101b8010358a00b500302e0350082c05159110b0a002c50569600f40140302560f6692001500f0002c1c080e1510404005c090010014042c500c444061004144018400c090084004000f00b01c13140040350b055400e00309070705040d140040205c0c02c01d44003621590240b07074200520310000040c9580582403401641 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 935747760 1250 935746510 935746529
    0x317010515041707030b0f09010c0309151113060315051c1502120f04120e030c0603191812031b0e04110a050a09080c010504050d05010b09010b0a02011401 68
    0x3030900140403080c5200d01d4600740e040c1308000340400052004038240d4440d08000140310b500703203845480c4ca4207484803200c140e0107040c074007038003240841c06140c004550884400d41c04030b880f01e0361b0106412180704450b0452000c541404021410340da154100c0400c2d0000d181c0f0306001e007602c68081000d8146420780b43d2008180c05c0c0301c034000183c000c60301412000d52441005040040710b0034519500030045910050f520107103401c000800c54400c0d142c1000c40e10b1407620b0403103240d100c0b02090356030003d00017081c89413402100080c0c101852401e00a464540c01c5414051080c41d200385c08401801d040084490480c16062120040d01c030b8420700c903c405d9411480c0c092011038080503200c65039a5404180c006071180d8100a100301d0b944010b108805ca40c0d038446c2d540e440000001484589203400c03805003600b1040d4403002681e404401e55054440888144151800c1d6280c05801019589500c80e0400d10796000050840a414060000090150000d200002821100e0303400c6074424080c08051 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 935749010 1250 935747760 935747767
    0x102010e0c030718060302031e0105360a1a100e04170333010e030714010e18071211030f190b1305100803040e040f0c120317010515 58
    0x10261040d18000c44100e100000601c946d02ea4010904001c1652000c180c495604d540c2607201072401d2050342c0d0b200b601420514004c02041d4440c003412400c646047c1c19203886142801c00585061000381407880e888034a0b50400800a0305552a41d0030480f64250101010b8200150004a02c0c80c5144541c0d440206e03031a500068000c0700c01c1d039410141c140468251241410f070080c000080c0005031000c011055106052400c0c00010030090102400c4c40c003d0b04404010001e6180072003050440b07410908041c0c11400400010401940011441045081850b03090100160b00008002c4100c41030f10814040c1c0c01e90b480d62506c1520040c6d48028502e816440024210808050901c5d484c0c0c04040340400c040c0382441c00620300c02143c07031900031020307a201c05003c03c0d41018164203000300f03600806581094038001807595144002440a00700c41000072224003004040b20f40c50019011090660b0002a1203040041034030118843c61742c0e0660003103001094030301c6e00d01850b40c200fa0168509618 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 935750260 1250 935749010 935749019
    0x40f2304050c010c1a150a0801060e04020f040e120a021204030b19290a080105130b15041803110c03070501031d070605130e040209040f14060702010b0102010e0c0307 73
    0x101401d0525007900d054500c071605c6816a20860750040c0103207000c40c01c60f840143c0d02030400440c2c048540c400caa040c4c0c50b0190070420262030118003039015804543c44202c0450b0140031901501d11402600c607036004000301420800c02d448041c00925409500302e6900c1e441c00b0342d0540d040d118901024200f200410000b896080c01194610841c00707071a034012038582003008081c3e41ea41c0c924003450600d0318082541003018103220040701e00810804000344118108014854405c80100c00054000d03050a00054000c0d45400c100680b04040a0420031103040d08a0042a5415026208800042d00244240c080d02d400090360b13a0040e000078090072070715142100541c0189207683c98500c007070280b0101028100814003105004005545640350b031071902c00d03204d0760003421903001420400201e5040c070001d44c44a00c9480d42c020b0780001420542750342420701c2045258081103907446445280202304040d5419007104c08103800c20380003404171110180b2007603140e00100f018650142e0290f00d0810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 935751510 1250 935750260 935750267
    0xa06121e02030a080c0f1005010e070507050f10020d050a0c0909020d0b0d030206190e0c0103020a0201241d0c0307030b12062d06010903020402090f040f2304050c01 72
    0x40d0441c8001c0840361204030b02e54841189802040c148241500300c04196a0007903002d1180c0f003070000c0d100d14208a070b50b04115804201500250112082020200350301d4104201040782c640004031060480302c0103c12012110040d41c00007005000050030500031505201c0140658a20b07441035884209007681424006d1000703421405030300108a80350f5032200480d0310f510454580040c0203038090440340c0f400c0700100501140c2401010f014a1500c0141e0002c80e40114417100501001d20340565a1800c0c0c01c0304901400d102c001c2468515004d00c581c2a06180e20740d60007007210442c4d200201e07405c040c110f5025008004985005040d6400c10000d4107451083d1301c6600401c000402d840f810041c503140d503d2418008980b01c04110416040d100c11600f0b1030700196070f12016481c1114094a840d0300028904003491100070b004640100e8540c0b03050392500812591404050700c00c2260030707841401c10014008003000c2c003810b0070a440c01002c1c7d811084035058461a0094010301c02100c8400044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 935752760 1250 935751510 935751563
    0xb1306031b0f120504080a110a1110050c2e02130323030c0a060515030d0f050f0a170603070b04031202010204120602030a0b01081003060203090a0203150a0612 70
    0x60b42041000090f00312102440d22490307020318084c01030b4541710900048040c007040d8562042c401c99a00c1840c084001495030b400307440030000259604000820448001c0c0d506000741c1208092601680031b90214040d01000c80d0300c0003003045407285126041c0d540b9103d04920402072005000c540074202800491a0f244644c403040c40c143c00b060920001c0580200d003960007050500d031250300b01054070018440b40e4004d05400030000c92510b1240515100006c3d510062042e00310140030001c1c4002d5000c034010010f81d82004491031505a850500000040110185504904108803e800452014240011a44c0070780f80d0a4550501c0d003030031a00c684207180c028410450456400304000f0500e10000c0d8588803c403807191a01584171300b00305094001b56905064468104403505040000040007030f6409011250070540060f9a40c54010985041c10350301040a50188950080e00103141c0145003400e01c144c40302102004019107400c03403410901c6c00c00e41d020300f1441e51000c02d8a040640ca82c1c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 935754010 1250 935752760 935752787
    0x29070206040302271e0402010c020f04052802040e0c1b0a0c0314060c030633070309090209360f011d13030e0105070c0b1306031b 57
    0x5039030a295880e40002c45940340d803078071428042e082c0359140da0051840001e0030740149544810000710340389040140d414410091000e41080009500c10080d0344170075200210703021002d00184050314003039102d01e140701c0d403800e615104440f4003204945003a0b41e601c01d6400b5aa04170f040001940c032002c040160359040f2000024a03c0070309602c14500a404000c800c0415200c3d0a6200210345035042c45907911200f000e005c21650410810410044003010440e64018005c48081d8031044000d561002c202c030b024000c811503113036201d591042d10800344020f030100034801c2e07817004000390720707036401d081640649050039403c503030318510715050040c1250301745407002c2e8a00300420701d03030102203507807030407024191140c200b003001e4100140305094102c1119000c07603000440100e06e5040550035582d40500014000d0204800c140b03218405a11820483d20401d401041c4104a207071a407840150310f600807403000f4541c0300b6207440011014000d002e0065141c40021144100c50f11651041d161130701007040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 935755260 1250 935754010 935754019
    0x3070210060905043302160507120501051b07020114191d0a030201090314010222061806050703032d0e060a05040b19020d0203010816290702 62
    0x803054910034007440740304010001400c001c502c0e8286801c1080403040101c80c000d21204054041e800b0304014024011307000848240010394518500b0840c20700d8009128000b80306005541d000a070a0a03c08485540c160141c0000c1289846101d03813160791404540e14190980c0e01409104d01540c0200800300324030829180b41881d0150100c641020005111941e2020418100040250321950048000c07240d106454143c286030641c0c001a00003045d510004019005484052555001c2074060b12142c168010070b9549400e00206114592600c5001c0c11001070102e500e14010b011444401a00f25120b64880300d2a008060324214050031001d100710814550070b0a0440880c036690300e26950b42a00341100092a14035801c4442c1819409000340c0c0c402400c00e001d002c00302d48070a41d115001019a40c80c2c3e000c818031305045030301a000f9082203101280c0301000000b140f190205800b007201d00c02513810425551110308214181e110804003e601c0d00c0c2c04114200c09a40007002010410700003071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 935756510 1250 935755260 935755273
    0xc05011805010f0b041803260705071a0921040305161409010b09040914070b070c050a0b04120c030c0e04030224160504090213080706020723040f0c0504060212040e0705030702 77
    0x442321100580140c030355030001740d80040e0200901448582d42000034902c3c0711100b2190409004096860040c02c402c0340071501d0484c00300011100c0401142c000350307400310696100307035865100c89480103840c0c825101a0f42140d4401d0b0413030314008100c14103039402c481c58141400080018040101201c44040380c1c070403c107070320300740503c54200106002402601e500700d664995918040c407030101680d20031030088a103040e080c03101100c808240c4055034600101000c400241d0b007800802014140d201510858441c2c07008107251580c55034981c4258042d408031000010300c043c0d03641d1100d00103040d0030284c07403c400125030b00c0e000d884141406000d49103851803d041e01c60009004a80c4541d480043d090f050300d90400c0342e00018031101d8002c26650014140e06441c0c05000320104040c02c0740784008288e0720981c0522a6156132003aa0703e04405041000030460080000c2c02c580e1160040d4005441889504404149c0000894003541c04080444c429511340c400141c6940d040030300310390194000d45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 935757760 1250 935756510 935756567
    0x8040609110a1413090b1f0905040804051e01140a0e090a05041103120316031b0e01030635010b1c020112090b06010c05011805010f0b041803 62
    0x14224280541880449402106110341c100302131040300c01c11040499050400420100750003c400a0348a800f10700d0801034020810549450001c594000c0c02c02103284c481030000b0310000d1030181060b10402d40c2c0003010000b1021030304d46844a421002070004072000301500c8083c4e80100580020070a0f400c04070440f240090008411010407214010010f1341c0e00100070034040c1080350002401d20039406005103002c0086403c0d518407000b0419842c4c0040e0403689511644258001030000f01403884640c0008c803000e0000740103282213181c0d14002802c3c44000b182d022024082001c990500480c0c415030440000c1403800b407000c00241150703c5541e203818252894803400c030320380c00b03164601400c411305041d01c0c400508098800560588000d107007000602c009050900540c1d00001309003081048200c040c58031901420300b511200c007440072240819420002c05400842201481c00030520503000702c2001d1100b00c83c40588a845040009600a0042030050350b140010140c40c0551044070042d9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 935759010 1250 935757760 935757769
    0x90b1b0f070311190e04030c030216031406010e0601091202030c0a0b0703030f020f0d05040203071703270102060c0708040914011707050102120d061a03011d04030804060911 76
    0x642c0c01520004032001103025186000302000080b0a400800000000d05201000d02c0303c2d4402480282444619400700c03041c50300800903032600032131407181c0c00c86481d01c1e841c3c2030b41440c1ca4003102c0b03043c0f48078407000858104104490f0610440c410395540e0100c4c0e01d041d2004102c9401d1050a98160165400702e0200d40c95200158001c4c0100b00882c0c4c0c0e885400c1d140080407100008208202144140011000d070b04501003181c001d1041c014010400781c4407400040d0409400c1d9021068640c034111810800a0020020708007541004481c1034a00c000290ba000d402c01d02d505825006030004000140c00303140140c040c100703807401a40045e0500d51500c02c2c2608031003c148040a1102991004000c220303000040320b06140014005001c5071450f01d40082e5403816100c2c0b000d0138003500461943c100741c40a40c040c0004059010140303c13410101d003819a40c59000b0701a02d1002645640718032008039110b42070300d0047d6803580d04c0324510350b0f8946500c801080d031628121a5140600300c000580d60341e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 935760260 1250 935759010 935759023
    0x606080313030b090a02010507061d010e01050115080921040803270111070513021c0b0a0630110304030e0109170307080f090a0303120507090b1b0f 65
    0x3988000340990314214100103c2a60300104120032542c849990400140d138400252441d19a009201095290714a01d42444101003020342080940c079002a41015104c15009541200e0398181c00095169880d041180d0070391040b40c001100303030f00a80c040e034a0304829000c041822400d40d20385a09103500e80c45000d0031a489000718960b20028028950b0802880d071102007904502400e20340b6100e80200103442d22031120b88a041e1258085500351416111f00c0d4044450006c4195588008000c0c0401c5090040222010040c011814802c0c049082c40c080c034441290005e11501081d190700f108442e400b0380703006504850307400302d446075048090410954081c5014901c039072030b800c29050a6500060003c030031940400a14641e50026851090002c8115105940c2241c60640e41c1c00e90641640a1445241c0d80c8542000b0003520010905a21002480c1d50b400d1a2030b0501054690050442d50458117020383c40443c0803c200001e00c1d4038074414003c05045500050b110007c100c012424100345 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 935761510 1250 935760260 935760277
    0x30a1b0f060815040522051f140112050601030b0c0904061412120403150b032a0604030b0c0304060e010518151e04080c0601060f0e0d170706060803 65
    0xb0096014460040030b0342c0750700c0405030b1081c0d804103c1803030009200d1a0820200450b40509030004041c002442001d002c00c2000b90344051000b20318890ba10980c40040074400101d0070710240003000410801080004004640c0e00840140460390943d21a0640c2890103041d5507420f403402c1001001e1526903019402c020640b1155106d4902401d0040c052910550540501c0075048501d0340d404002d0307103074252001c2d139400001042c0641c82c044410b200519a4040007545446410380d10780c1c1207402c1c244034007100551262082c001400b4042401a00e01550000815040c180d0001a0b441140341001e19401801100042100041e1801d501d084402c1500e060303c8229017244001e03082002013000700301c4804146511750403460200d90318112a100105400c5c0764941c0c01d404682400031203c250fa0a0010700b40960b5201d581d11580504507a001900280100b0a41c0c0d0217281d9600d00413140c90000e030f400c0300e8072078900e0100d0103aa0005901400d000c0307640741d542d80000302d03c45408002618480 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 935762760 1250 935761510 935761517
    0x60c0302040e060d031d0105040506130602160806070302090310050702010509160b1813060e010e01082b2006060316120303090c0e041b090902030a1b0f06 68
    0x541c20b10380148403075000108030034010811145941c00103544020307800803d117608107620800d1016200129041e103d2940f000d5480080880d040ea070318064440300c07070116a81038080707038011040c600c1e41d03180c02e1403035215845054100d50005a00d160198009185045e0300a043e03c04005603c881da82c100c1e40c00341d84c9500182c3d592000c04c0f401d1340c0c0c204604c949102080c0c0e040d105030740c60b020304030099100300007001c11b88010551000d00c094451f5150b20300c280c2d070075540c00d018079a12424844a00c5609120300e20034000201c0002038050004a84c0c842c1ca00d07440790810382840c9a045003104140011a00c820806c605038418489200300c91600c41c0036011154068441d90401c0d6040618024803500e410110b0b4229001c104068900c25500419042e07042c100801c2d42401820420000d241a902c0b10190b510248100010000c100743c001d401040f40003050319209488035600401c440c04018003d4260303000c60601c2d80450300009131810200760980c4503032580c80d2210b01104c89640c01d2b03070010020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 935764010 1250 935762760 935762767
    0x706232107111c0507050703060c0f0c050309040902122407020c091504060314100c1107050f0406031211011a010f2613051002030714030c07060c0302 66
    0x30540e0102541e40161052400c40b00c0b645014070050380300e46030003104009030b07802100c040740b0140c082c50995041c140c000c0d040e28081035076400c064020748107609070782c00050010300000709098040c8038004122a00907004506200c407440c00e0000600c2d0300001a40e00c40104840d4820142c40ac1103010310903030728043c00fa500013030640b2182803030740c1001d0300c1d1205541040100041c1515055200c41e132050b03000541a0000400c500800e005000c5600302904050b8481c490543d103090018000d0448403000c24104500650780c175044802c0e80d00e40c01402044d4018500c200001d2030000041c48440d1002000090034680c0d82e59100120114040c1b890042650940c1c0c4401d018000e01c01c1c010112500102807500300b82500008160420401d200024803820241581740070180f00d000e0306100c00c240440380e0316410558100642e500186804640d944070b4000c490350b02c0412402580d014a00a40b9116090540b10000b0f00342030f00001c00c1d84ca0084d0701440b8000201c0d60034022540c1c9214070740c50042c0d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 935765260 1250 935764010 935764057
    0x9100e0a12180918150209150f0708071202060a060308031b090301151a0405010509010503071101110d061d0c0a140403031d01030b1323270a0302070623 67
    0x2060b011017030006014814000c09883c0e4580303d41e01028504030140d060342d209540240d0803194003e804024082086c0401c80000f0803640c8001446030070056000c403500d40c3d03120f110b00c005980381c50000800401042c40425491004611a000ba01c3c02090369181042005070119003152a1610004980d102c9603001300840d80350308041c3c54903128050103551819041c400043c00c50304ca41d44000c2d040120010000340c1c0c09109090350301044285000034449004010a052210382203050301c42c3c10380d0b203444400141e125004050410f6600e403c8171040036075654030703001d40d100c0c0c100200740307800c0c090101c000398100e000880c01032000d14441c1e2a045140c01e5404106640c14140500c0740b41410b1034071500410550361484031029041c100721000c200d40d6901c524003107070b8000d100d510b0b00d402d03110602400400c051000c0110503807848000c030074064480715550b40382d644002890280158200b04400e21400c2d200e80c0e003904048107a4a88155500042c6103034144982c80034551403100014941c0056 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 935766510 1250 935765260 935765273
    0xa060e0a080a050c04061a1801030b100f030b0a0f1a121008070506070f060b060d020f0c010e07120303112a100203071d0a090509100e0a12180918 64
    0x30041d010f414000b5807c0d40601d1100707401403089500a0000030b0310000e003140103a120780c00c50f9050000c05400c8401c0d400b841c01d80030f40300042440800000c24240418030946050421f400740813100035090030032480740340031203201d10078180204290141904021021020ba00c85801d1406510f4240f01c0510842c50020300310301b0050140c00c118030483c0200204808075012070805200c2c143c101c1c1c80005c0380e0000300c000031070521540341824152400441d0403181017900001900301c0e41004002030041c845440850364540c04140160104c01503190800d8022a1199100101c81c0c5890b46406250032461308115018140000140700c0e6407502c090050f420050034403201c00450348a000a50860620303040242036064030b50000780840c10944c0300406940c1c2c401c482c0030020a001c0c5000c110a080130213001d615003082c541000324903801d01c1c80000149000158403030219401100c29a0721010240e4202c2d0711850996072146405481480402c0001c5144a0086404000780f005000513a081c80c051 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 935767760 1250 935766510 935766521
    0x3180501020307150c02014208151f0b0301240e010c020a0302090708040b07022e09020910060f020f0309060306150c0106031403090a060e0a080a050c04 67
    0x250454205201800008070810080341641c131840d0800700d50030345425012401008000c5100f42d00c2100814158580c440c0c010079041003218000910030449a041c01500302d00400c0c0c0f04034000d46e03000c0c0b4140c55240208903100b0342c1002122151559400c24800c4100f9106d509810100c0a001c001004101d11a0458116081c0300104191800400c1002c5409420440450f02d2941400b40c03540200c2c045580d0740ba424005140d00524241150800c03030001402c104040301d04650104140002c940e4150000510b0310f4421400e40701da02c0342031040d0b003d89008213880544120810348031010b040041c4e54064640b44a40920240c4004041c64020300403c0c65a450601c02d05541116505039100d4201004031280e4100590300d1550b2a00c40c413010982c043c1c0d10410b031025101010031480045641908400200e80c02040c001c80400300001c80b05449208840c4615417203900002c0070050b03203029042e0f09080b25402442e40710080d50743d15581b0300b01004c5400403255a082005006040e150a1103103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 935769010 1250 935767760 935767769
    0x3050309090f070e0603090109060e0a260315130903020d4505030703030306031104020f0306120c060c0304050901060c0f0b060d02060705060f0a02251a040318 70
    0x145040c40c2883c40000e01103189101e09180240760000010f14a60300940045201e580c0c0008100103041c2030701c4e0001d844108880b422114005c0c42881c45d4014082414640c2c160b141d2480160300c0d5484442c54641e40082c01d0312482c1d0810452410040e1020b814810220700600a4000d40120300c4140c8008204003150501501000583d00c081507048503000c801c1c01543c0001d500e6842d40c0c1207c203840054246080d40641e50600c14144080100756154100e4402c80748540c060724180300003201004242c1c0101c03640f0180d40001400014054601106081c2c0d881d081d000039100411141340100d80158480d55459141e940005000c001900301801a90700420807460308003011003c82d540c0400d0306202d0100508441c0010300400c520340c2d41d44294460031175000f41640e50380d4816103485e544510b02220080b52032405800000d0418031503000321203490042d09119214814108040d00c0c0c00b1942c110250340074415804c100100ca01c10750030700360096010b515040040c0f0065564070440c1d5003107421 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 935770260 1250 935769010 935769031
    0x20102070614130b0606280206010e150f1210021b010504240b030a140607110d030c0c0c0b12010b070f0f0201051e04080706021b010302070c0e010305030909 69
    0x10803079409120088603030f1031640702004444030303114100040c0d802c0c000d0101680480b4070003400c1c400711400c0340680c22200300350303502550b04603070303070f850f081c1c0b40d0b16004548895021500f01d84040051600c11303491240881c1c0102134042c1440d2000c045480c10000d0f4000d00c9283c2c0c1d0018101306440315601000f2140c00c81040244403501d003079031350046510f501c00c09107242c0e549001180c03071b407900298000301c40390342000d01200c000c910381d030405540814861150503111f00942c404106124410300140541560020080c100424081ea08500900040308683c0420040900e030b0000600000c110300c0080802844030b580340c0d08141d00e0b1484030710060f440f100c80064204030301310005000c2e004120070710390001c02c0080200b07054001a200b03403185020b03041944a41c03034030004031121b2020142040c2d030300020484400b039454820036a0341e44a2080d41d500500c0d030050070601c0640c03194000701505403060a02006882c0c1d10402940484000c1c0c000312015040482c180405003024040c880d444880c5a8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 935771510 1250 935770260 935770301
    0x105010503030d0237030c020a0b0f190501031a01051e0f0105091903030e01020307200105090a090c0f09121103120a0e0f01030509030d050402030a080a0201020706 72
    0x8000942c0c81c41280209806541c002c214a0004d07105400e01200441c0c070400c58a41c5610300f00304080c140303c801a84103002c0b070320b07102906406520020700c101c9425400032814009444900c0c0510f202d010090042c51002c45181c480c6151311414081d180c0210311410440d80821854200140403100503009140603028209414281c003000100a07034491a080e01c408100020580040b10320384602020940c21810301d40f807410003401c0240071213003104d00940c0e500e01300ca078003c001240c6900c43e5441c0034058510710496406140c00811008840c950141042454062400302090305102a075004200c0c403036481e894142c41c15004403039884000541d15002036840e0620090356038001e020003010303108901d80003a2400c203850411040703000c541003121a6445241100000740701c00a0749500c14068264588500503550090203441d01600c0c101014500300f001042c181001848004d0088e80e241c4100c91207040410040802400c40385080d600141c0e0303a0006080460507200d0b400c21141074003110f038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 935772760 1250 935771510 935771519
    0x2512050c0706140d0c1d030105070e012a030918020901050d0216060203091608010c05030f090a060903030204090c090803041a070b010602060601080f09060f2802030601020f010501 79
    0x22440c00300b41c1d070241c102050102e1044640c142c45008560000309001c0c600b0041610540d0403800e82c1c82d510a980e64240c4c0c0701c1c00c02d08285400c1e00c1c0c081c0d90000101e085110281560342c00b0302040b0301d094212610170928050ba42403800c5042c40c00394000d4011808000c1c0c10700a803030507020b106109200042c011341c6405421000200113103c6d2500380440380343d01050040c1111421034501c1c1900390850701c155124109241c40c103846042c20017071608100036005c0001002607040c020758682024a8403564155600e58850f401c0c0301d5401005003500d4040c41c900c10740000c010340724070f02902d0300943c0d0060320740b41400303c14811100f0519000007841155802081100700c00400c540580b5002c1c40307581281880048102c40781d0003000d000800b590140c2c0e00119280e9800181c4e02d20402d800da03030303159454a485500204031344050358107981c0d0340c0000c00046c2c3e03203484d881e8003550040c0020000490804014420b0240f58082403400990240c0010a02a107036a04100c0a1202102e05008100d01d5240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 935774010 1250 935772760 935772763
    0x240a0e0303010504020c0c100207152a05071215060501020a020a0b0a1101020418050609040c03230d02010515060c060a0902010c140105062d010806062512050c 70
    0x140f00359885a0703000580c034152000300744001d0307064640140014100000c0e402e03029403101154084e01000d000c0300c0210424251050303103c8240744406208000800705021800349041108100c02c0e9441c0c4070340f03040052040d1401203c0019180a00010003c0c00409080101511401d602c001e04641c041c5003110090394400c030409085586075080315a40e034111b0041907130340d088a03071030b81c804070352002c580002c500807980c40d800d00031050390030200f00ca6616242080a100820360340904041501c0e42c05000064941b0400421000c3c100a9030450081d80d02c040e51511141d2103c240050351500c090020000c5005106030369040c0440e845420041c1211409075034020003413455451341d884002200540e4095207001c039a0ba50000e040d023606103156000d0902801c0c0540e0714601402011000240c400ca502a000e6101c8150b01d003546001481c160044030319a4001d0190380d4403800c10089090b000a1011029008044071034480e00900d2241c00d00c269484081101181800380c00c02c680e00503540c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 935775260 1250 935774010 935774017
    0x7061d0d060e0a03020303040c2705070c08070f0302101a2404171c0e271519080d0f0908030313211d060c240a0e03 51
    0x10a49031040040118140039001d0000c4045294031801601c00740b01c207165000c00110702c51030007015200b0704c56503251940424190f001d40e8000e200300198451050b400318540003141c000c2b1261030100e07150f5105403600d200d80da029103070407a40c43d580b4070344a00c201034042c0300489440d03c040000304040a034500b00c0820781f2030444821441449014100c0714114500a04d0104900c92400c8942d165511480b00b5180c0e94441000014613203c0c80c10303031440120124808800081666640d10020728444003803144421151002000e448500c00014403101020103410703116094012400f00300303425003c1444210501410b81c1e41c03455059030001d01642c00c0c000f400e504844807500e0b29485000c400d03071084824400e00c3d084040a0300000051045240c1404811346202e4040c980c0b0f00e4020b9413001d54000135460280704003011403a490301c103082d140c034041c032503070805900a40114984a0762013005420300c0184009001903030024000070b59491001c000c01c03a8000c00c0208108021014000e00a54901 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 935776510 1250 935775260 935775317
    0x30201150e1302030109051506090c19030509030d09110f18040f08220e0108030c100e010603081314030615271503061e0c070503040b0a09080706 64
    0x11140300742c40c811501c0940c041070116410000f0ba4060301e8000009401050b0142c0c0c80600c00c400e039502060f00600c1c1c05044941c3e610003c010fa42030000c86e03003025001b811000748406051f001c14400e513903c600d214090704202900c2051840500d0401d8070030801e0035100104164019000c0c0c4644e40c0b84080e1920455070400c1c0c001c103aa107180105450706501500c02e00c03500c1510060040702c1001c850b00c49042c0390007038803503900780c4e140785a880d04109a603d010780381100b14141d00500d51a0030100d1590f01c41c040204c1c0c6940081622920794072850700d035904c807051004ad040c1902004004814403104010420300042340681441d080000440000613410b00b100c43c40380c0511403500d0000820042540d40b060280314501079907140c0381303410410450000d901c42d8040d00519000070060f6000c1ca2074000c00760310502d8090441e41b03420502d07004d1a0881c103001c48140c40304102c00308040c0c8040340075108035542544c071410034504141003e4201041a40040203010000c5030311032103030f103401543c4c02885 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 935777760 1250 935776510 935776531
    0xf08130507180b130b0405010e25020705060f0408070503010c0816030b0901030609030f050a020712020607051207050d211e061e1205060c07050102190309030201150e 73
    0x300e418001c0740105446803e0a41c44076102d04120075603805070b0040680702d01c0880e410031030f507a41c030800d400c030802c0700321101e07581d9801080b480d10075180c420340d0415100c840d520464440d584c44034086101d0350300a0310010303038010002c601000003050030007064015000c141d00910003a51190380c040d140200c00f0b052001148a0f00c0f8028040900c2548072002e210b1005041c2c0440d540d4908000008081d516003e50008413643c410860f918040c03422200d42114540c01060f415151900c00382c0c580040d900120fa21581c10800e0001082003082031415041510341c9a5070348034041e2900601e02440c4880000601c0801c4450081d5918031030044410340c404c1c02000f069030424102d03a500080400300c4c41389440340c6825404a61000c600c14100c10511855191070b441720b440d403008071b0b001d01c9140c1009025038071400004481c90394010141659921802c0054100350070948248000700c09400c078a400203a4031a400b17010306a0900411602040d444a4003c0c03003030800da813112200780000d1481112 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 935779010 1250 935777760 935777789
    0x120702010e0d030605091503030a05160609030305070f0f0e0609060c070801021309140a020c0a050a03180e070210020f07052b080c0304060b010e060a0f08130507 71
    0x418000e42051030820540e00c1914140c105007407000d4024007880c001d10b8081c1c500c000c0094004100b00f8030764071002d68028019801c0095055044a80c1e42c00051144200d502607241000010700038040c141019229481c04943c5280503007004050401d1002c448040004900c0c40566464209458075602c8405940e01d9594078090400709000703119040000d4250300c038050000802d0070041d40030340030740f00321b02001d445200e59980910050300d940c650000c24500d491408035100c09420780c000e01800d001c0800380c4402c1066031f16000d040c210400c0c1e040d0040303034949100403a0030700c1002190010381001c810070020723801c1a10000f5501c00c5031001160505500283c1c20841507120703415511100d0344a4119005d0400004111a0841c50345116465040250303143e180b01500450348c1c18420340c0794a442d070341503685613156080940141c50019061002031802e004282e10759074000c1c16104442d071242d095545e010800200985002050411441000030100000400c081144012545d103d40c80c07504 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 935780260 1250 935779010 935779021
    0x3051507090320120f070f050105030a0903031812030c1713050f0708070315060806070804020a1701150503120a12060e090f10090308181015050a0b0703020312 70
    0x2440c043c000680d40d4071108041e5020704600c000290114002d4500301580d030040e075511501d5007600403d0285501281c403d00c00070b04000d42c190b000c04a51350113807a0100306200030307504110011007003620a6074054000f050303219040b40c140c01030f400490503038070b41188120040e006940c0c4040b07000e089801d043c081c0380051400d0010401c020048075180c101603480c0fa40d03485502a50320070281c4001c8030002440d80c0c5580402c0c03500d100310f03004c5a07840d601a10340e554808004903100503004200326405124180042403080b202090351803402074100c000501c0c15800705140804000c1680f01d64401d50008840007012140b02003503030308607101070a00800048481d030300c900c00781a0341e4000c044070030100010426a01d00002d001c545421582d03056070380035911395822000f501c0f00f514002d80400c003040080f580158805520000e004020400c0c2d8010195840340c2d401a640c0080c8112074515880302c051040b4501200c4400080c030054101b10b2528000c1d0303801039200c1c054511f08441c9501e2020000c0d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 935781510 1250 935780260 935780303
    0x4060f0c080313051e1e07150f08060405040213020702010c02090903120106080603070308090f090f010f0b070506060f03211207080411040b0609130204030515070903 73
    0x5140d6030291007203071646410850a040c90441850640b441e216981c0021019a8000c0c1e19802101e1618040e00e6640000d640d4001c00e11107003105a0203512400300c000881d44c031009840f0350f448000381d4941e12007184626008046c50070140025218074684001c1c04010b9543c2c2c099200b10508000002d81c48040b0b074001a030b03440b0010304019400400d010100503a400c0c020006100c03400f011202c244070390f42c035007004403000c8404661141c1c055012660603c08980400c014010a41008255078081d442000c007080c0751000590707800031844c11140c014000081991484400381101c4ca80d450300300245034407110b0b03858101800141c02200d8005c42ca001c640c90612030340c1310800325942c546680c00c0280c6a140040d80c8049202103039065242c000c070395805c4c0300b80c0c8940e0080ba04000786044084068080100418564141582c040001c11441209488242c1c0150045100e034a005848600c2c5040090401c1e190507804521244240c0802c8040d0350800609020b03290010b03a02000300040500300c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 935782760 1250 935781510 935781527
    0xb09150a18090b0c030421020601060503040c0b0c07090e01020a053f040b070e010e041508120d0c03060302060d02031005210106050a050315090c0d0f0b07050f04060f 73
    0x25000743c04940801c034000203101c004502131383c42001c1d08003074080c0d0007201a0f41b200c900e84429006030840e0004110b014441c4000d590010701030314490b1107480c3d0700d1050b54010741c4400f908000303d4003c80d10030414034009109000e11081014029031828840c100700038010300caa000541e0106c20582806002e04611b0091a044411501c4490319009104041400100070444080b2250280c00002581c440e20031010300c0f040040684800100501500c00c000240803070102d6800b40142204002400341c8007080801001f01c0340d0700709295211404a20700d820740c5c04411640b0140743c1400000c0005894a204646541080590040c0c498550800c24a10424130340e020540c00b6004070a601d19a540c1c030309034000403400c1e4900803c00c03599035405100c1c82149c2480b482d0780c0b642050704016201d208840d803043d80a05c035030007541c211517812000a83c540741d00203c1900c004103600116420044071361000e039042095402c2083c1081d1404800103903c2c4554001c100c1000720182421004074090300b0070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 935784010 1250 935782760 935782763
    0x2003180d0f1718150f0121020909010b090c0a020721031b0203010c1706010f080a0e0a0f030f0206100b0901050f1c0f060b090d0215040e01090b09150a1809 68
    0x240c86150340101604d002c00306013555140c10090755a80001100c002d040f180070841407560b948480145416020400f001d140240254019521004070034010394803c5089407150601c0340d581c9482e0200420000e150503007076003100b200089404580740c00500b07002d8640381860b80c549000d0b040d02005034503c2e200403600d008000e400d50300301140120110780080c021400b008440e400341d2980d903100c100440b25030303407401c0520011a05132404282103c580e41c1009c1e10f585240c004a854014880d030340c1130707104040c4400c10b41c00142384210461480340c0c1404200e8101c0840a420354145c2d08004031a0307194814013180c43d0620000190145c01101000300b41d9902e4025500780305181e00e40c050003000605004082141c0d214a4480045007140100d0141c035002c100141074041c03400b941e5400e000b02107042e82c2101900060038040060980c9006613410301900050401044484100c0700f801f00004001c1c2c1020116060380b01e8105158075000308400841c1c0307650030024103110740c5111620060148180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 935785260 1250 935784010 935784013
    0x70e010e061008040201141806210f15010f12090507050f04150e040606030510020a0806091e0a02130801060503121c2003180d0f1718 59
    0x54002003040010720590302610461694070640c0c008543d05403080b28000c1c0800c04000b10700410040000192101285108190382140090400940c058200340b06862051004a640349000016107441c0f0381c000b1035a5001e006281006a0303404903020180c0950303410801e952034030760302e401e2040714640343c806ca407604100710610307250829644524040c0241c60081400c00b400240341c0c1424802c00300030300180c07981c00d00b07054103110000c03040c0c22011348191440d030707281c0102101040007445076417071031449004010394401c44c02c440074240d450300902981c0315010702d00030842c0da500c0581c4034400361040101c1540d1150340701c4008000a0103511022038030066001ea020a008505600c8942540c00890480b82e032000c0c40f1003000103d219602403003500359a65034141841e0040740d0804000c4060350012030081019010b060040c0381c10444080440214010781508201400d00c81d00507409014501038041c214103440117011400c2107254052103a42282c002121103000341c3c1040c1d416000c0a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 935786510 1250 935785260 935785289
    0x11a040f060e0a0602120d0209030a0614012c130201020f03040803040f0e0702070b070f06020f09010807181202220b120705100309080c060c03090c0a030506061207 72
    0xd0000380b0300c0051002d01801903440030b80c042440d60000504891a210b10303003200c5d281a01c5280840c0203508134100107a094440c0c00d044000040490103091111503881c0200c41e1150f1510348030742515078a21120a8900005461201c0c0000c1050304160f07001003c09000c0c01d0300384170303807004038a480ca1425074040c0a0102080c086440310340400103004682400d00d00c840d5094942d01000305028041d1400340160744210340c100a2000000c0280c14042d02810f08a42050010f45418080c0e910014030b044040000140080540d81c004140703d401c56900c0c030780f5900d0842c1d08808400e0b808403074000c80707103001d003e50601000c40d66110101c54401800c04000c5035800c0e460100b02024154614223140305011024003840d5082000440b07004550001380850090700c0c84140550081a404205440c0d000080000d80c0c083e04e02007100e1801800e0314040d483e62441c18401881c10b00b40300c200503034070032514483c0030808540c00140c82c41d041001207030109031810f00c0d4101e0620307100555000200d07006446 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 935787760 1250 935786510 935786519
    0x5100905041b150f031b0c03090801020c030403020a0e130602090d081204020a0b031e07051603180603020f1213020d120f03061d0a0204090906050103060b030c010503011a040f 77
    0x28070703081140300140c84080310b440d04c0b40c2c0243c00303948400041c2d40c900811442a08040c501c20001180224004d003001c1769850340354181d61303081ea072008410b41d0956100007010001c50622002500c010200c1d40f00020460819004a04244007014005410107030081428490703540d4010a00082e40c1c3c0c040780312039880064100d00300f4002d2044070709038070465000d40c001484103110b4003102e01c0303415400d02610304445c182c510844400d90103003c03001084070501c80000d500074030380e040c003400d83d001e0340310081040c80c5070440310341f500c1d959005141014014040c0800744044001036980c00d84d22010001101d45c0e91460888800c841070350042c0d40726407245000f00500c001e40c408940c46603140d41c0c6080383c06411410640543d011032017406845100040040d40020340c1508d0706030003126088025107015074610490040c2d544420741501c0b4107540314010000c02c81e03280b050f01d02c1c030a03041c2c024001c0d1792040c1d0006060790005201d085910750070001d0107075000100301c00700c6000c2c5c0201d48038011000d456 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 935789010 1250 935787760 935787779
    0x360606190801060e18030306090a02070302070b0d050f071404050103020702180c07050c030a0804120f02041b0221090d0804051504030201180f061202070b16090905100905041b 77
    0x80ea940310044a245c02a80d241c0d2401208480c0714003400b4100721425200e03111448000d600130074007507003140603001e40030506d191060014007a0003607841c1c01045c0c034205141d10042d0044054054414040074000c05906000c4e0081501c088807424207005031070328014004640245829a1a5060440c10004002d05040f07004090000d1500441c1115108403840c41450781d40d164140000e03040c90300c18007040045c20a00500b05007014821030030840040c00e95401b0900f61414030030410000303d1100c1422040325070400210341d5228804e1003000300c0c9940c1c81d0441039280b041110701c900903c01c0c158984140058407048400500010306a0358448145d40100c813072a0b08a40003c900040b5029401141c07090083d1b0040c05464000c0103480750305141102c140c514081017000324458540903c2a080420200c588a038800e0004110300800780e650444014140c4a90350002141945080f040c403411300e201c41da05005172488544001030580316030a10006488070980200e203869013000c004246000c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 935790260 1250 935789010 935789039
    0x100e0c03211c02070f26030a11160c060e01020c0a15090f0303030203010f050402031626100602070b190507031e0c03081305030d0c0e0936060619080106 67
    0x307210310100701d1036680e4503910020400c0b44056844401480071a2240b0b01d242e018012714100b0480d101d2800d8044004402c1c114a80d650540b08002500d0302040030030380225480340d50a100344080c00350b448100d400107030300c3c1c001401a412040b4404240c40070050203584032070080e1248803180e00450380e907850000c010b980b09000302c08580400c4400050141014002d40f8002c00603041242c1c03c800840c007044440c403203001315015001503814446540c0c040407001c5180a5014080390310f9960b8100748020f403908042d507200800d99001044400202440082641c5a588241c030b000c5564503042c0c10700700d480e1b8094080ca5070070b0000224000507002e03040f0518554462003502d50003620350740e600180c064081c20381006440c40e041084450040403086c0d2242c2c03c8884107041280c441d425500c0420b540500407191a0001c1c04100d48100d803603000e16950b42e40b02025070b524030080060b0300c1401600e580018120034050070524040075000745668000038090891200204046682c52000e10341521 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 935791366 1106 935790260 935790263
    0x210f12090506040f080c0d031b02031006260d140d14040c08010f06060c03080a09060e010609060b070302031218100e0c03211c02070f 59
    0x10b584001420142a10001c908610b41c03c2a00e01854281040700300741c440d616007010440065130154401c40011000e4011041e881c055101003407404030351200c0e0121240c1044808222012014070021041400b1645000c030314448020307041d114401a0004c00020f0010406042110300c46402017400300301000c000222a00b450f065451180d07000c1d1400c5458800c407074000c2002d52000d0085211420110f4020080c1701e11f007800c082d01c01c1d450a82c005043c06074040000d0007080703150f4020b21501da04a60240030180b4400c500354024070700380c080c1382e107010700c0d141d000320b040c0c940141030b01d060680c141c00445c5004070300c003010514034000400c16081c80d40a003880c1c100040d17040c0a43c581c01d4014400c0803881511400800b4105003510a0070303402684000a1608007945408803148014401e0848681d41c1000c020710810000482c07100341e05039400010000b0400820702c041c154182e = true := by decide +kernel

theorem cover : BRFrame.Cov 935611510 935791366 := by
  have h0 := BRFrame.cov_init 935611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 935611510 ≤ n) (h2 : n < 935791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
