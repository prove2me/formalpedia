-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2136
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:45:25.063758+00:00
-- url     : https://prove2.me/submissions/67e7541b-8ace-4c2d-8cd3-0319f44db2c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 383992805 ≤ n < 384172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 383994055 1250 383992805 383992813
    0xb0c01020405031b03150901020c030703030b18070801060518060a0521070203030402040203040201120501180f140402060c070306230a090b04030809070e04080a17130609150e 77
    0x541020001d03802c4000c030603140d40c55801000008171303a958a141082854001248001c00d06510081d41294014084841907a03940e06444c14098041c028803001030340500300303400900640d800c04a1141d4098581c980e00d0282e44c0e4600a0700315020f4020341c41e5840c03890b600818080e103a540749001840e448400d51101c03500c408505402c680c2842d020614840e10207440020050070642c040112a84564115401030300c0303480340e00048030b4070001a10034500d0b061a00c0008100c1c8480c58881d05c0d038001500c2001d000105400050b4003d5030000c60b60f40d5030400c2100c010070010b01d0140c02902000400c20101c407a003595a40380e40090350142c210180e00e0035040001002d000381c40c5800b095101d4442d40013481130101554400c0140c280042c07024003000348040125031070396410b10202e0000d111456240619041030308017151142c2c4031448010124603840045001d582e0000380d43c5200300e0801d00001020782c2503441d0300c00030348004207041f503110320740c08801800404030f803040c8425001258010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 383995305 1250 383994055 383994059
    0x13030506220f0206130302091305010507090305071412030f04030606170a20130f0f0501050a090504051606120629160b040318122001090b0c010204 65
    0x841e005a000c03074061410080c0c042820300c04107074042d604042e903903030569403241d80e145201d030072411090064200035031050580c0c007031040329002c142c241000c0c0b501034002080f031501d0b11001940c18031300e0780c40002d0a075040400d08120036407032581c00450014000c0c0028480420780c1501c1030440d805100f40345010400031805006020007407203800003510f401d034220410b20452902042d66002612002803554400c0c04501c403046265001c005440d04000d024102d6030650502c10002401d22116501c007900d1030418200c80058543c09940d04882000e41404041400d210000c0050200180b0641d4280303d0080c51006061400d02e01000034140c650312218408802c8203c81c0941d41c40c0d034001c40014402c0360040e0403000d110f00351010611600360b941e80c0d440e010582c6080c3c010700c8400d0003074114803141c1e04100078160080c00d4012540c0403000c160b15000d8649210b401980400700e8081d0021102003945107240c00060f0758103100507814180074000f280e0f41c040014181e400160300c0c3e20165004502 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 383996555 1250 383995305 383995321
    0xa1a0405060105040c08180a0b010810150311100302040815241c060603050604080c07090c080c07020f0316090f1e0c05040e040b04120f1d0613030506 66
    0x541d0241808441c14401d8045c40c00d4014014180580305450050b030501c6041a00c40c0104540e901080c0e2203054001c0030b40c4d5680c2d40741d4880400d000c5000b030180c20110381c020504642c02c403010640342d00a10f061841d01c044814080100a040003d070b0500d9803c0001140035002040a00703071058505c0214001481c010310f981d040144821450b00d07180a071140307041021340d2042080200c1e04615044801d000c002820107030040c03c0c1590002d030190065400744014040050001c0c21410104002c59083d2950741d1501e104980081080b0000500f5510128111031b036400700405180c3e0008068411300c03105800000e080070103011031003140200b90102004001d02500404000318550740c0c040040c102c0e02c280c24034507280300503281c507525503403501c400403035900030419640503005c2e410100d00c0382c2ca0546071014000303200355000c0d038640c84c6445105a1243c030403680c0c20202e03081947c030380c9000fa941c10004034000380c030110042c3d401074050001e05402c07032038504400015806580100a2401c01d016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 383997805 1250 383996555 383996563
    0x60112050406061502010c0f05031f0b1306050307021506040b030102031302010306080d05040b1e0a0201060609050603040f0f1509030512090a170913020c0609010c0e0f01030203090a1a0405 83
    0x84002c00356410300070b0005001b500041d034104100520b06200e0307682e0f59040c000140300383c032042f000260703a010b0480108810802d0400303010000460f646145035103440c0c410988076408111489401a0b002c44030050a8404841e0b586410500142001c5624035010001a0984e082141c66800a02040003002d055681c10f0003a44002c09042c2c004c1c050480e4910300041c2503105501680d030799082e000401c0c02c0c00d0324140c0b28000890011004c21502c50380701d031000034080c0020703203e02000101c001d2030104443c60324004803809540c0c020b2548020382200d680f81c41c00c1014000050310075504840800751025000e0060b41d514500c00e07a569aa01d07040300164101700200940790b015580c0c401024140007850803000040d041c815034056039200d601110006440c080c1586107804001e00200301c20089160025550f402100054024042d100a4400446080b440c2d84030385980141000d0107650039500950007903400c4800401510140c240d00e4682d01000444140c40540c500130310400c000a00070140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 383999055 1250 383997805 383997839
    0xf020a0504020c031206120f030d050a020901080106030c09081e16030b0739050f060606091302070c0816060813170c06010807380306011205040606 65
    0x41c0d003107050589940b1059601d0150510442100342d2034400b050f0300d6541c4003640100803401504503040345100036055520703a04040d88d07417440746003060b0101e103035079510740240c8400040695802d00260f1806000328090720200200310300340030340c00e807010030364400c10301c0034140c142e41c10a5648a0034529041e01380c40c11500b001041204040d078403040c8002030400c00c801d034010380a80f80101040020900050b2400e0344855440c44840c1516071080c1c0045800000280c1c1d94000c0d03003130300d05603d140d00415440710000c07200d459001d04100540e992620302254003500400c1d4540c0e00608001c000c0d99504c3d034420f0b1607007140303c40703602ca022062030383e802482000c406449145403104181c1800c041c4200341110021008044d00302d2588940300c0762070a01e0039904d24401c14800c4507051350b51068902c0d2910254080d14092000d01d06481d94120300c1c42061a0b06201c410301d0911a0403000a585110b0760005054541001210305d0301400e15500c03406418003c80c010310000901e1840c1c00500340f0300702c01070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 384000305 1250 383999055 383999059
    0x1b080706181401140f0304031d0405060d080318060a060e071403010306110c01020d0506010f090303080114011b030806040f05010b070228090603050c0a0803030711030f070f020a05 79
    0x504000c1c01106814207000400180a08062442c61341007040c241250103504907008280b81c0100400c4141039102c2e0100e03c4180c04c040c81014000003840a00080d210201c074800d4114400251040006042e07900866100c00c4075511011410202c013503071801e01c00284e54005100351141014098031180070040d80d04010f160a018441c411003d450031054001484054001b0343e48007002d1a4503483c070000c640c0102e01c07650007155030f20f0517041d903100140b2050720703c140044c1c14a40d4034444507000e5060101a207802d030f12001ea80b680307098188101940c0111416040200d03000340c1c401e412042c04001c00f10b0340d10a41f1114214030344201030004503410141c0c603501050620700100850030305c6078100d50001e41c0603a5041c481015010030301c0841400d0744d491040910341140000b52800042c0e000c1020369100b42c2c10348640000280070070210003c2f9000b200c501c5d40081003c501000d0144c2c46800301640e194080e242081c0300c07180d1001d450340140000b91291800030181e04118509519000e014100c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 384001555 1250 384000305 384000347
    0x518090609061303050f1e070c0b0307141e0c070e0606030709030b090a08030117010e012c070305010c030b040b1f030207020f0301060b071407050d0f1b080706 70
    0x9080040145103d00006820300c2400a0750f8045451040200d8004884000c480703403401101601c0c0d0000355000c0c80d0b00340d94218100d94041101c400a1040340c0c00f4000c507540d9000400781d4020000350f240d000c40c50f5609002e0090302d00761008480c040190841484d244040e18056240144a00c4206001030125200b04010002c00059a40045540b03061380d8011a07446007035560820402d00d04024890060600d4070040000200f84224a000040c10302da4040284a507003030200e0200c6c01d0300c1c1e0322100e00740b40b45048581420308540c48013442502c1d081080449440035a20340322103003142e40c0480c5000019480303c81d00d06d0030307041c80e0140c040e8000c2c05560043d80300480c0c02002d00700601c881180c03010540c000800d8015542d84d1001c003101040300600030001140d035410b100156134007001040320503d508002c428902c001c02b05040c1e003126006858107540c40c40340d0352081c0c23108881c5102254420042e0017401c048502c4641c24a02a04100000704600341c104407015042045010b288004001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 384002805 1250 384001555 384001561
    0x61e0a0f080702060c0d2c0d02070b0304060c12020c0709050105030d02060c0a02010b060d0c0207060507120f0c060903030501031103070f05040f0204030f2f030a0b0907051809060906 80
    0x10380094001d81c8092420042500d641d01d03a0400c00180440e403694204030070005140d4281d160617801f0000d24142032508507445082940700c01d985552403441140c0752a0701c2400050b002c00e21070340190054640920308840b00042844450742240c02a10b040409540407000900040c2014810140900740441c000c015240c0724150082d0703140f4008005441c6000d020621ba0700b680d001b5000342c181c0c2d034001051075440340c043e00d03070b080300800044540c036005104a0b0310000710640585c4c22a64080e40007611421401e415400659041605044c500c080202510820b800701c0c0b002d1040c25011440307036501103099403460625030041a00809120312079001040100301d200b030400da500f82150400d40b00481c4042581f2041c50090266500c0a407003203a181d210079040081942d40d100c940c400095200c1079500400300c0c2001c0740030403040c0c9103416034000c6c0c0a01005c100003100c01503010215004503640b4a4035000410540c207000183c0c0744c44c01c81100c007030013541c02080c41031541c8400040e0040070306103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 384004055 1250 384002805 384002807
    0xe031513060b0f120a1211100b03070b0304060c080105040c0e0409020a03020406030305030a050a02070209060f040b040f0b130504050a08071b180e0f0705040b061e0a0f0807 76
    0x1a00c03440c00804980c0d42d28402005500d40b100b100301021401800c015041803454849034481c54003280c100d9501d4030300756002c1183ca01034020441d84807910401042c1d90340d00040e110707008186224a0590620407000001105400d0300d0080d031140d4400c0c2c102045021040d00081c3c2071001c1a04042c2c031480c100f07503100121550007405c481001c075003298082030b02c1c0414008203400003d2a04080d400900306140442070541000066001d03804c00e0b8000c110954030b000e000c0e1300701d01644074001c0d4440040000b15260b842c00130b43c0c0c503404800040001801c005110005012501110008a000da49034000311000b868401c541c50b0714908000c4080c0054601135031040d4580c003601000400d58400030481d030017400701d0f400d00466440c4c4e030050400030075a2640c000481c01e00c42040080507880c100021441940c0e40455140b94141c3c01d0030040c00c2072818041004064806580001e810040900021000480c0303e0b602c110b600f585108056600c540150b0020a05054808080213019201042c400b0139 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 384005305 1250 384004055 384004081
    0xb01020c1c030c051c080c0c03030f0612010c1107090603050304030204091704031a01081b040c11060a0605040506030607050f03041e0c1e060503060f0f0307060e0315 73
    0x596018040c4107140602450143d81c2800342e040b004c1c0040c450b0340007909070385403030646000c1400841d80360f110740d560b40c0690600c0310b4440c0010510443c0c0051010442c0408001120b98026000038107107544490080d407103c0c2140d0040320003c000941030100d2090800c000e01c201e03000341440300000c0c480c03503041d920f44555a114501c0b000f4000e07542c1d824200c0034462074988180102803400700c03450303403245d0f203042000c00b0140388a02051a15050400010351040001e560859461240100c041030900c94007008014203180c5803100c280708079070880404c03201c01844002c2c891000c041b00022054101070611085030b40042c40310340250300810502030f0711a0803c0072717a02419515a0703d1540da03034136803034150050030180381c26042103100c0c10440c2d0104402c00b1042426201544046c16401d805004111400c2a041c440c4d10003282081010a0342d6090003807814088072009402c0801c1c800c02500130900d04440ba60082c000109a403000c0603082c50705005084203000040b14001d00c81c24040703180881 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 384006555 1250 384005305 384005329
    0x90106080c0907200706020c04050f0601031a060703120b030106031e02010504052d03010501061d030703080c06150603010f170a120f03061d0112050c0a09020405040b01020c 76
    0x8241200c0c2d0001c2e0701e1500c12400e000450500096006185109041169031551103004407400742c01054103078002c5e400e00e485080d1160f03142c00c21101c0d8503102c42006400914001001460b4000040c04400280d00ca100081210701d200c0d42d1201d0465801030145001c4841084a86100364100102040070440480110141c01c1302446201d003c0c40c000d10062320144207541c4225044041c08403451542049550a00380907680307030180f801c100b0446002c1500b210001d000312804140200304421141c450b115010802e8100501220441034507a210018141c0005801e240d81d036000b0010460000141580121351003026a8000c2c1554141903100c0d0a1041c240030780ca06540400c41c86040340c000c2040326456164004002e0040210b80240082003800001488000700c0c0c00c00c01c0018070b200300303850340c801104502048500d090b420009107400e600000c15042d1b5980c0f0403c150340c44641d5810721a170008000824005988030303d0482408241c81485039018159040740c94091815121100c10300c1c0c2d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 384007805 1250 384006555 384006559
    0x1a0703050322060f0b0d1e0206090406080c0307060c030503070f02010f0606020d09170a03030203041a0709050a090509070303030f0906050a0203100e01031101261e090106080c 77
    0x512aa03802141203040380b0401c0b01c0c00c0030048095062400c0c000b141d4040d19150005080c2401802900c04c05e1085c902400c900082a18042c903050342c0111b1083c3c0c0c500600248020a114580340c103a0f00080d007501c0290700010407541004152100398a400c016200007804a03041c808980011524082d1441c0001046074081c42192007401c001c1034802e6004100c0c110b00d104d001c0012686801c1c0003907807014546040d502069a5080200740b924000820400300070142d402084110000d170f4085003c0d40000d0000c544150320340b40c080c00c80003107030b070901c030f1103460165034100740c50703141c4020400ea51016600c407000070340c50321092049007000400c4074410b40b5054100455500b00300b80481d40100300084024051510304428040507500315002107001c0c1e52200340303980c816611044c085020100a12000300510100c5100b07140715402075003400c0c3c49071150410b0701c1502044c0d610f01c00000303004495070b05032000c00ba82e800d442d03d04002089500b00c840640204441c45c00c100d4069991100255001c1c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 384009055 1250 384007805 384007807
    0xc050a12051218010606030e030f07030309050a03020609060a020721111015061110050c2a0106080601080a0f060b0409050d080108010c080f040c050415050306011a070305 75
    0x30451900440c00c4030010025404403440b03a181c103895840502d0101202507516500b0701d030002a156110340105825501088065460f140942c101c410300766104a00450078940c9907060b2001040d020703c000000d480c025009416645804100e0a0070400c0090030f00d1202881030212101003007414038824034101e00b440d0040026440440e0541d80c030544107440701114400d08020104429a981164100007130f08072501c1000c60b200c41003642c41096154600f425030f031205480d030b4003060b4550080358104a0302c1e140b042c0b50200780c0d64510b400070102200c20b85545011080404010000d209440003054240094582035052141d2175440384484003024003040c0502482c041805800d0f84080e0180c04014400c2122900d035141c0947c0340c1008224070004111074400015200d24180101c580f4042507a40e00303202944c5195450840502c041c005aa200d4244031020071380d85c40c1c1d4800c01c071500381004150310040707190800309450628140c001800a18504aa042017110400f05446503035615041003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 384010305 1250 384009055 384009083
    0x12120a110a0f020a021002010b0306180c1003180b011e050f15160b24030d050d0216061b02030702031209030a1203050117010e0a1101020a080d050907060c050a 70
    0xf01d2608035202e4000e54010103103039250225540561004081c04000c1e419151196924179414500b408200c1c0d050070140c0100161100614000c0041d00050265040c00107000c809148007404800584000329114440b520041c000c498001c87c00c601141980390170160b10500340008154042c03030310340c0700d140501c04810f000c800c900c1c4031100341c42c40440d8440e190882d8a03000d040592081c80c050b940c0d0194ac00a126011018603c8019030011424000c2d008062801000d00c0032a91940305c0c80214815a0b401d0007180005c4c04610354549205015080109a0224500010700007071070f4040c0080641d4001c0100000586003c20b503520029070022803e5100c41541c0007003414030f01096001084485c001c6011030143d0f030540c0c003550680d210000715181c40c7c41e4404286080700c0340121101c4161b40704854403000108200c0c03824848100c10f20603103482080ba990303080b0660b00100002d0901b55180c4040290131003042103000000d000c9842e1818054410b900c6680c0c48400d044c6d4007030034003002a43c40c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 384011555 1250 384010305 384010307
    0xb09241302041a03041403070b01051005120f01030312091e020f060706020d0b2e030e0d09050f0d080d020f09060d1b210e0f12120a110a0f 61
    0x140ca0003403e1560640304200c8051a1242e0690310071201140c29400c01241c169603c1000400d4498003076001601a510340d0034032040110803c0f0b00c0100c03170100b010070410300205001143c0001c0c003411103901e00d140b441d415841e002d000c5d59099000080e01c9444c2a000030003240c1003020801c011000c14408000103d03107070010500d4680391341900341e0400310014800081184035030040000284031103042080b21381e42810003201c12109100d10a502c010b4031100862030242480517441e40c1980d0400264503203100103124100741d421440840821000e00c8100074a0404d030341122010368046a54000c0c0b0340031540c49061a0241e20981d410312540855030301008500e50084a0b21150003c000f552544441005030014040204001110083c0840c0c0ea500300c0c2d0040d00040c0b403100703400c215401d0141c24607000030010184424100d07007500c1081028417542d40d05000090300d00e02c0d62003440d5602e943c0d245d404032810b2400b829003a540d40c50040f40e0000030b08000203450a06041d4580400c2c0ca5501441c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 384012805 1250 384011555 384011557
    0xb030a020301020a050414031903030f0e010606120e010e06011a0403020306010e0103020f0906010203190e060304060507090b07080a050703030f050a060f0b0702030a020d030c06050103060b09241302 87
    0x1400075010740c0700040d2024a6500070010700100c030052107040040e1102c2c1014551520584042d078040302c0c08201300d50f000a40a500240f082c1c00b41c0b1080091803050586004d420364415134002c201250300d8400c0e105240103180030714000042060002c4c0862010102c00b0340d80d030b481c140309041c4688959224400d0b204c015504480055800a080b10000e50f111038024452500c02e1208a204c0c0c40362170b25200b82403c02c006982d118140580145041100b1484507202c1c903d8080c218104008202c081c00b44c0b6599a407001d103000364015a00000c0750303d00b84078054081d0802e900082c21800c820f005800c0011900e0085581c0e44030a4a00603865107403515003540a0138129110103210307400c0034100f21003c202640541c080350a5224008610342e5142ca01f10094420f855001c0d400d0341042075404054100542c02c0c48600c1e2103440c00c181c1c5004192105000c6030300070303081190440c0c4c98101144180c90f0020005801a4150301d079022400c201c3c2907042204202d201c0d0242c052044c0828203640d100c0c41364 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 384014055 1250 384012805 384012823
    0x90709292218051e060a030507090506120c1e041e240b0702150f072a05011713050f030a170603030703030509071806030b0f100306021606060621050907090b03 70
    0x70109d5a0703407505c481b020341c0076140403900a030052a0440b0481407600e40080c804100d83c5001d4409041d851620f03003000048106800d00c26001038987d07845201111041c4511403150303502680001720144c1450310003c1081e01c4503202d610b07000c46070310148428084402107854995044820148425441e0580b00b2140594040e17202903400c04126030040c0004201203007000451403440c3c6481d0311681e039074400c03c841c43d400303840e000428640c003604a850b4041c10303041d0041c0c01405998081d0850b40d403560324040d06e038a2104007540001c44c086c0a6580c20603500e1020080c0d5030f55107000f6243c00c1700403d5403405080c101070304158981e00030401100081c0445009403a0184031580750301d01e1a52500003800c0c00c1d00c4215060000d40b400034941e040c100c40b00500502400c0f5801e403003d40303903440703680194215070140502644605426400a0749a04c00d14005101031345a00c06026503600f41c07a0020307140d429803c6409070a0500300042c1c08001726203e0f041ea40300e0000050080c02c41404039203481540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 384015305 1250 384014055 384014063
    0x601120e1504140f0316110310020a050705010c050301060509040b010c020a09021803010504030f05030a11040e220b1807031403030105090709292218051e060a03 71
    0x841c10b100601c1510b000f0354070516072240403641c00112440c0102e90702d01c07035403400180c84ca8a0603240f400040c42c000001c588900700608984a00409035043c00c201d030300c030b0031100011910004000301002000c0c01a034144022501f0310070f042d5898031001070800c1c42610350240c481c542d01c5027043c0380e41c0e0250311101744003074003d403030a910140c698081e44025448103880301c0d050b0541440088040c507050142c6441682c1c1681c0305110031103140c400342c071030f0740000d8010300e08180c895603180c441d4240744004d04014443c18807040400c0c00d00a584000000c4203100156854060020303a6000c940e0321103160ba0424001c9070440c155007441681c490030440d060300001c03d501403810b049a40424000043c1d816035030110343c00211600e03400c4e8192008507240c81386190106080c542052168a2140410725071a031700c3c0034091400540c403c240c801840040c40f8003611b0000080240070301c41d00860f140b142c40907207500800050424040030216080090000d20b06e4420000c006030442e220752903150000c541c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 384016555 1250 384015305 384015343
    0xf0607050a060f0c02010b0f0307091d010f020d0b040504020d0213140a0e0106080d1409010509060a03091e1509020f0303030f48090d030201050a140601120e 69
    0x300b1407090f000c1c04002c04140c0040d0f0800d0b65030728451038103252801002034018001c0c6211460614180081d08440d031850f42c08509031503460802100031701070340d100240301a0005989020503420030701207401400d801c9018915080401c001a280c21803403129094040350030042d42c400405001c4090019502c4044408842509000d980707410750304895a44440c0c8c00013409459110310000e41c1d54403000d20200c0c00100c0d900e8003200c038211a14014140440107140603480d0030036842c00724100f98840032a010000741d8a0260f8401c0c00071210382680c000341d80c0d0344445c1c0655210b0303c81c005903001354007100f050706a850601388215643c0d11407041c14100054107036901c0303160000303c203100d8190407500740081000382c040388408080604c80d042c0307101c050104152003600c02102040402030074031152965104040165034075550f00c01004c0c0890b14420786c00880c0d680b514030b144c0b5041c0d4900c40560000301505900f84501030382c000f4043c040c4000740e0100052010740c01c0070301c01d01e0002004011000c40c58 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 384017805 1250 384016555 384016571
    0xf090b03030d1d0102180f06090105071b153209130f060b07060c0219060b0f060f0a031b09050d1505040804030209070e030606120304031506180b0f0607050a06 70
    0x528a030031b54041d10f804a0310b40d12070320204018000f191182d1140d184c0091800c12030080010414642c001407400941c02c036051b030b6500d400d00038041d1061f204000002c1941c80c880f120b001c000106183c44440c903240340d6101d03441d02d10380300c0c00e480b8050007074000c2c0b0905c0c4541081d0032804441c0e02c9040c40040140081c46150b90760129070304c49034080d1606640d42c0e814174100c021041c2c0001a0304200b040b568050640040d400d4035668014520140ca082d0b0100d100d28803036805a60780f002400030110081c220f2962058068400380c2100d1072000005440c0d80e0300b580c000b02481e0441c281000b124003d95200704c0b030029a16000300740041c0c1c506043d18280c038280c03d004c1440800c50140c41a00c0c0b0950313950380342d500c032180152280020440b80039803650201d0300086007400c00c2918209004400c03000c4a04140d1680e448525850300600b1084400750b44040400a49841d14031800303100d55441c504200c4d000502c0003052021003003002d014000c0c140011100100003040055000702508900d003049056 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 384019055 1250 384017805 384017827
    0xb0912091320090a080601030309030605090c0337021005030705130905010f050d0507030602210a0c02060609221e0506150406060203070b1806040305040f090b03030d1d0102 76
    0xf402c0940b41500556840c1008151500000f85890590380c03d80c940c2d0843d280f0b50b54400010300001000302215009644406090703480c10006041d0041040e900320760f07940304a04009107a5213041440074900003400d2030a034090380340c8480c1c45c801c01c00a490001d9030390b0f0303c00074107441d01d00c220b81c00d0b115100480300c00000c1c8102c4e10f5010505a81072104030f80d02c005d40d900f00300102d09400e020701400c5500403e20820001704507a00401c198801c10341000d5420940a81030008450304a07188103081d07886280c0400c090354140100c42e40090226100003c07418802030700c414403100d05044e904c40c01103240100e4184000c50b40d045544826403da114010022407400300d8aa21003a03c507150000650700080d5660700c0c260160384155030890740294103250050300c3e0908150405000307607030b0341a000c800d6402084010700a1611030340c02512403d80e920310381034150020341c07402d40c0242511440d00031300041680d404003c035104111516804030310f4085868522900c049010340242e001d61001031940002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 384020305 1250 384019055 384019057
    0x5030c0303150402030106121e060803040305150c03131e030e09010807120b190e0d260f07020f0607020109060605060702091308040801020f070b0912091320 69
    0xc0c0040c01482901c030b400e4003050000340d00081c00303403070702080c0e040000c485c079a82d89901c1483c00c0c1511059035540c90710710000325021605203410100c0203400028041c01030100420880d0004000b0165030300380c80c60421001c48031408042c128410141400c4582c0c000d107d000c49003010802030105a003915010381d440e000d02990640c001d0301e80211843c1000041c0102c0c0030410408a40f1403048813005190030380e0310011903080040070b854610841d4000d01090020343d104509003ca1680010708501801d15409000e20b000c1840360b2441a03808140707440e9a1032038400180e004201500d01d1516605c8140080c0c1c00c01c4150320103a0510b100f514108520b20ba41500007082d018050b01007006450346030303400d03c4480d00c540c40700a0340100048010401c2c014020700d5403240c00b406030352858145900ca10b90346007640d00070180302900210102c1c41000707014148580c05d4200c4031120083c0a40b1040c0861401c450090b281040d10800410342000301141c840e800010038191403e040c442d100c1d942043c50009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 384021555 1250 384020305 384020311
    0x90e070302041d0f0720010c21020301050a03030c02040f0c08061003020c19050a05070b070309080a02090c090607051f0c2a2109030b0a060e13030c05030c0303 70
    0x20b480002c80054590101071900e4000c44e40301c610b000c620744e2040f07000e0320702030640210794410f2201907515420032002032184005036000381d03a07265192500900a4509500850301c50f6040c02d104200401c100e584802080044a030b050414205003c1c9a0001800400c44007203080d402608100c0f51410b89948907241d58401c042c03c8401070620050941c08030708138001c0b00c281040c40d520514480c6050559031280303042c2148100225017403c41503941701401c000041d400b88611000104110042503045103103100074142c8023000f0000d01d90300c0c0c1c0014425440c050800001d4803400110040180c4800040b2807100b40c01c034046610040c0445d1f6150110103080e10b030120010300d85805102c91511070a1100072690b0705d1510b04080d025815510903440b850300344101e403040680c03880e070320300928940c0c010411500c03da100c1c200c006240d42030158030201c0082808441e5880d01c102407000c0b1200c40d00710341d00045600c11504040d1b60703074502074072500304104001e0494800491281c203e001d000000b148 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 384022805 1250 384021555 384021569
    0x4020f190510020109030207030209180a06060602010506060c06270d0203030406051005010c0b1306060608062107030807020607050708060420060a030519050702010e061003021f090e07030204 84
    0x101d504a4601d00301c0c205d41c01130500900581082c0300c1000517161550380240c21465424000300100c40202200346045607400b070440350a0f466074010004d40343c080c8203666004c101558074528003c2d1070344c4000d80b1513100800c20038036400600051000503040d03a41040c0c030541e0640c103e0750440345440c0041d660f500125021918142000c001403401c0c002c20b0980e50407604181c655000c03e08803950307141d00c1d0000c01403407200743c0904030f9440d0000c00c810380641d800a0500d03885103440e504002c420302401400000c606440b000c02c1d0114070140381000100303a011240c02120903900d801140c070000b81c003807003064009422840351000219000001040450046201c1e11030301980c84400700002d04039070440604598071007024840b82001c1030180d000356034032500c600399840d030511440c0801401c5500c282e170389800503075452840c00c0f05003904000c02900225019500c10400e0300c0c41e4009142c081440000340c1c0b000b000060036844c61401401e080011f08484031901c85140340040b4010002d42080c45440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 384024055 1250 384022805 384022819
    0xb011e08031606180807032a0b01050117040305030c0f0f03160801091505040504051507080a150e070f05070506012301030c0206070806030c03030c01060e0c0f0403060504020f1905 79
    0x1100c0301c2032010b40413030302c04e0340045520f041110036241034a0584004808034548110a101c440018082181080321144107000c601c00950400000410601d8030070300030780745640450144000719400c4030540f0b500c011004030303081d03441405001d18070300c901604a0f401c0540074013000303200e00014100c90183c1040304540e14425682c0e0b9440d409070a464603058400c907002803001c0d0500503070415070000f5a010340a402200c140275104000b004400d41d088418400180d468802d020b492403050003013032607004041e50036031502d80c01c0c03c03401c118008015000310148184020b202d0034080c01841504c280681000585040350382d61140d108025000070b84142ca80e0a2003003429007258083c0c401c040c1804140c4d4001c00c485e9031600300c1a6128500a801568148100c4021505c0b9550410040419100d01c10010401c1d600d0700d44948902e40010f00042c440320810f11000c11a4010501601d00300d0b60815404070305c0741c03182d001003071500c11301809041d0441d0800d5031500c004803161384904c0480320144c402ea = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 384025305 1250 384024055 384024071
    0x5011a0a0f0308090406030b090105070e0f1e150a090807050607080d05091906140108060115050d0f0203010306140a0b0a03080f0c1e0106080303040b011e08031606 72
    0x6900c030318000c44010340315851003400820603d0024203c03080303002d840010f48039166112040078040844811415a4450080110f19a8400d009040c42c0006032140f45a181140e0b000801e402030001510301b031058040c1d000c84595840740c400141d45421090225681d100c14bd00050400c2c285021362500d6128034040080d5a081c4901211800d503008102542000292029000540303405401c2e060107109001c10002039490b056458455241315410004902c0c0100c10540f04d001c0c0144d0004800780c0000004008100c80350044010040c003502d0302c2d03941d03821100b01c02c80c0181242446100c101340b01000100400030035034440500d448917036690144603610801e480041d50743d103128082d00b0048441d410000291680060111040811056410400c80003291031030589a240d03810f003142c4858039000040074083c070540000c1c0c8440300240d46103140584a42c41d0090040c03003120a103807403ca00307403908a843d2076400c20103002c580342520394400c1d00c49a8041401030300380c2d058880900d8032201c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 384026555 1250 384025305 384025309
    0x9170301052233061d0d020102010b030d03020406120b010c0311240403201e0f121309110a1209150608010b0108042102100623010807020703060e07030b0405011a 71
    0x5502651590380c41094860303171101d0500c40890034071344040b4195074850000a866aa00384440110300c0c81590307006032104d18000b001455400c0c00030010400c02c1c541456040b02d039a20500480da41070b018200b10800c2c9003c47c041501d07020002001040c00000304c1c2c0354046041c41d0311040c50089001e0b5a8840c000070a03001148204110003c011055070f10000c0701400c8503c8081c524100d4580d03903029128081e0307800004500b85042c002d40d04c1001a0001400300340e1240c6003c04001901080404010028a121612420b485113079500818881284002d1424490b180c00c1402480c3e8491003c0c01520b0807803800d03001030503103802041006d50034000824000e5104d840c090f07103e25003045036003480101e043c125240006c090f14040b0114014404400003400305402040001c0c40c03443d140302c0f02c000e61107607206084419403500604003c03a00f8107103c9843c1e40002c442e81543c0d0400740005041910250840c43d01d1050760000f000003882c2c40402090100642c014291007040701c02160024018100f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 384027805 1250 384026555 384026567
    0xc1506010f0201050618070309060e0303040c060c050d05090402040305010e010b0901062307050309270a0b01170c0408010e01020c1501080a03032c010917030105223306 74
    0x2e034091b04034408414242c45a441d684242c0c3d002482030400080c0202152940030079526650100501c0da0301c00401e01040064109010740241218070300a40c80d80c00030743d038080d1585506c1403401c1c100000850748200320358030340d41200d00440c1e1200080001c2040050264003074080b01118910483c00c84000240e0785024083d02d2507154a100000d104c00d0080c5840700300c060f00905403d480c0340c8070a00c01e071a41350f2552030480d0b103207a00100c030310b181e00c204030559200e21990060281e03400b142800810005a40c0200b0341980d0742c569a41d0301310b0140d4a0703a04085480c09183e12890903582051503081103540190b000b803881500c854143d460a5200d0984450900e40c00e1180c1c12295205c40000030100748254003440c2110345943c9851900444032206001d40c0c01000c90559203a5564680c1008116885202602001c10004a107085615000c0000e1010960361f048131168409003200c01c801c1070b03050380441c15480c3e007004a5030040300d41098000710424003c07059407441c194045c0120701d05010b14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 384029055 1250 384027805 384027811
    0xf02090f010b0a03150f031b060509130b0d05030d0e071401080402010c1103060a020309060612030a0315030605010f0f0911091219030f09170304050409080c1506010f020105 76
    0x5101c2c80c540241420210014604410b076071180010804010400c00b00b0310f0310385002103000700f007404a00c181d0b02284140c001c541e035000109001c400c200d601c2d5030342c86568501d00c3c5034030304013400140c029202000c80c400c041d4543c0c0091841c04000b90b05080741c0c03920b6111039081c1108008451701d00780c60304101c040c4503019242c944d01188d88038000800640c81102d07a440c41601c074280605000540c2e9000c6494000103452021500e5004410483c580303200300702c850391142c2e0440c2c40207908804c50030b80c19107920a1140e8602003640703410440c0070511050309a0700045a00c0101048503695441055003c4109800741c0000b0001c0b00c00002030078080c60061920b00240344264901d401c407440200030b03e015050040740d90b5401240c45001700c9442016813100c0d401c0c0640c41d80707065038010700401000b6864981101e40300e0082d060910380d0404002040d1020344100b901c00003440c0b581e509040740c176409808402c9200748182a23018020340002c5a034580100800c1e2141508484055070076820b0310011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 384030305 1250 384029055 384029069
    0x7140a0e0c030603070e04051e0a0c051e03160306050105030601360207050f0c01170a020a0e13090314160201030b0f0d060515190b250f02090f01 64
    0x140c40400c036016040001960028001421103040c16034903403200b428248129003d99098000c400e292030040352440d101c8226441820140500e005240e580507000c0442d405018001e201c0c000d1000122441302c2c0d2284c03040306000f07084807007150745030f01c0b120b41040f81030104842c02d904080000507207003400203541d4140c4108000c88008540403e121300c40d0000d81450091013140d800321040d05041c4241b00a00c00c2078040c801500c419100200c0305850303c81025601c3d030421184107816005a040f200400350448890f40e0050396030700103203038211200911320000701e60040a2501d0728540803010f90101e0020f07442520b80d03800038601500e000c00c3c035000310040200c1014405400000540c800d5100b03007030000703004205001007040702e030106000d00103d44049580c1c80d030b06c0c0203002101101d2001400035010850780c400308159110b4044020340300714070410380c0308540400c4242006803d03000c3c0c9100030f0f00300d800f04054008141001910038802d030209034001c600f40004621600001399005040e43c1c04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 384031555 1250 384030305 384030329
    0x6050d0b040606060905060f070804050a061211031b030a0e1c02160513020d0f060f0905010801021602012006073615030e030706091a010503070b1b01060807140a 71
    0x190700700c2123407544803400c1280d21007800c000216443d51240340d0709000d450f4a940d00d401456160704d661040b202c0c0c000c040400e80e5003e008010511076040c1d00900419240c040351350322a220424080060441c075101c4422078096030110300051840305c0002440400789600b02e6030000c1601d0a28036094185005043d00001c00504540560700541c006240440c00600300041d000c252070070f03400c21100b0640203000e84000c905000c00810b0703081d004450160414100841c0740c01c10412655030b590991100081c18042c107403810749004034008144194500b012010f60f0a00c3c5089200104419a51000380d0070381c4030915001e4032003003007030b507540c1d240c00071302e04164400d040c1003d0000c158807500340448400c068480b03072a15403204041c806000c1c0544960f0000c103454419260036039600c0500260442d2990595004000550340051108112807100e0262a84c0e06007040300540c2104c5041d400355007642c24248001106000042c101c0c00711034105600c9003c808030034041100e1003100307119203246584 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 384032805 1250 384031555 384031567
    0x60b03062806050a020c041406040905071d0403080702030a0906030b0a0314010c02071a0d022802070806011d0c030604020403020d0803010e1e130201020106050d0b04060606090506 79
    0x1426020900d2070314081c900007200c0d4000c40709180440100340c004000082d0040360301c044664041141c0040001c04072424404020011026070103440000c1500d44a1030321120200f050150922020020300080f030003400c1054074000d105584540d06880487c00544080006100b0300d1000c4107a9042c0411952180d240d0303440d1000071030241044160700c41d40705052031000000500018408022014a400040744400341e44070041d09001031540180d02c000480219000c0f200040003c50b41c1030100c50300d005880342c6101c400300c001122851490945030b0342808c0f207100c0541d00013503580c00711481c0130700329200307aa01e40f00c40900c010481030034100f81010500110b40c0d4a40d10a02546e8068006000142070030341e80e030005500004041400e8504980000060000c08800c030719065002135449203e4440c0b5818604c2590102c10003091b03002c40d566080148811a03200307401c50802410014840004c810319400c00380040c1c00d0584003115003502e00b180006185000300307040b100b10340004010300d00303200b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 384034055 1250 384032805 384032809
    0x30803040b09071809051203010f0b0a020106030212010504020306090d1b081612030e0c010e010e120106141f0c0b07030906141e0c0a031116050a020112060b0306 71
    0x6401415008190092aa01142e10b00401d1030040c007004c40124003003500811414a1402d003404660f403a180b201c010030040c04036805040c03001040faa2904c0301e0640d22200014100d00524098100075800749464010745450101500880d000e14000c0b001e4900c1a164464520740e20003402c40301801040b40c1c9003a0184c85000cad000340540b03040c040c0d102640b800300c0341c00c010203116003200800c440c601511009031040303541c180700d8900e40554180080c07a2600090001a21550007501c100d4100700c048000b0260707a0b21102460a554480e86000340051512565200d406848907190940240403292185c1d030094480b40f48195800d03400d0310340c0480502140c4a968070030000901c4034044c99111491100000c00911980c19007454034203213a640c6080c2148021041c1c80f41030300c10341031130341c20b1424070400b010070740202c0c3c08000050400045d1140740004440060080312494100c81800070f801105001000c130340031140300d100346c0c5c80700d8030041c01d20b54400882e281c40c01105905402440040c03002c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 384035305 1250 384034055 384034073
    0x609070e01050609041112250c2003120c100204030b1b07080424051c150f030807020f0a03050705010f030605030f0a0b07110a0609061103070c020f04020403080304 72
    0x1307000094008150150070300404c0007160701c20140031103503449100402c00100080550201c0303410300505d5145008072260030040600494417000b5101000b155280c0350142d0300e05035034401618003d0160780f4a0840c0744407030b80c5640c000c80b83c440018080c204e190300c0c281d2114030072201580c4d80300ca9900410340b50180d2a003002082076140842d03000e01001110042002c2e000600014000500d4400c000020349002800c588a00001442408414820182d00c641c01c0f003114041c04000c1d24002a0310302114281200d11002507008000034881d031140801481a40002001034074001d03500e0f03a04102c1c5c0081442a241e50a20024200341c100c100140407541c0324006010b0110800c3c81c000c1a00c2d42c891000a08008d00b0400e818050b80c002d40e80ca10801c100780c1807c65019509007131046094101e18040c40d103440000c02c009000300c2d0740e01c200f02c08000255022003a641c5074445429103034134000f00003400c20301442006074130595802c8c41050447c9402d000b1901640d9020310303800d045895036176900240c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 384036555 1250 384035305 384035317
    0x10915090b030c0604030c05010e09040506040b0402010e1e03190803071d120d02060705090a06120204030602040b0301081603110103020705010905030309010b09011502071802040e010b0901020609070e010506 91
    0xc540101c103c60a1280d4504014101547c01029159005450007001503c0c8565529045006d00c954070204030200c0c901040b603540c8190010114001690b96100490350317808038200c813035030102d41901d105008041117646d110000c442501110122200c40c8495007880b1070000004282490400c00207c50714400c0c1c10f400d00001d07840500b05203600c0a6000540c01d1480c690302c3d02c10a0340321880b091107040e81003019680104542c140743d07141000d2270020804a020034003c01c0c041c8103104000c20280720fa01e5040303d004642250007151540c0d200d0300d0302e40c4103034403c0c03068041a1203518015012001c4140ca0002243d0b03112500b090114199401500603401420095420755038881e45c0101240c400e00045109601d00e40001902038109000c105880030b043e08070784a4842d81c9002c1c1c5d0a1079800080c80d0017619040e0302c44202d695409902e002c007074480d17070700f00b00346803241c1c0300c0005400f880c1c00b00070301b80500c4c1c26001d440442d41d0389500c00e55540307003910031144e500d0707200c000401403410040c000740b03a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 384037805 1250 384036555 384036559
    0x609060d1401230411090402060a111203011e060206160e060903070e061503190b0d051603150209100f03180b06030d05070506270a0515010915090b 65
    0x141c00b2800300601403000f405251000200c2500f100308020044100d907040c1c0711940854001c0e60600b000d8000c141c40d03019110041041c0101080c00550300c0c80b041000803003050307080c0ca200344d8079a1641c04107000124401500c1c00491140d034004262a0300206001d807140d90b5910b00c461000c20003400072294402460720480e080b540400c00480581c40c14828100030b88400d0702e02e20210700f842400c1c0000c03058000d152481c103520510900155075400e0b030880515000c610b601003041400380b00011142d0300004002007661144c050402e86880100ca800821640155041e40e1075000101d00c50050740304d4a40c2140c0d00c0303214085c4800c40d203401361103224110300080c940020080c00401113071800d01e00040058804080d801c3c1004214035041024948042c40e6240050a2031000d5a60b80d94483e00900411204543c03003d40601c50130041042e1400c51500c40308549815105050564869084240c0c1c4d004d81042c20001007201001030090b0340b8150440002c1d14444c6140003084d5004000c203801c003075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 384039055 1250 384037805 384037811
    0x6111018020402030405011b020703200103140a0903030c0804032f07061d03030f040b0705030f031e0f010518040503121e010906030c12030207030501150e0609060d1401 74
    0x300541c580e880030303620a6206900009501100c55401c8030405004074000341158801e03071043c40001c2020901406001c0c01c030440c20310700354007103006a000d04030f03417400b420500603070724108070305c103880d1703400c03501f03c0b0ba0281e01c040080201501c01100c03091421603001c0c01080340b600c0c0d0304000b81d41c202c600c0040c20710003e1990f1740b0300c5803040d2824100b84841c5d2004000035441c5681411903441c1042c4038058040c01c0300110f02d019610440c000050080b440b91054447e00481c880d014460b0920840f00321600400032681e503442c18030851070b04a0b10310110580100110300001d40c1d08080741034820305a4000504044140710131400124106100a10403601404280300015000e450086018045c3c9120290000b041040707410707020110805a001e843d240341450001c2010449146401d006c0d03a0f0744940c08402d46986003002c0c2d14000b1154070080840d80b0300035810141400c46043e842c01c1e24a6200700080684449003041100d03070050301c02e160b01041c07030303c070420004406500204010380000004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 384040305 1250 384039055 384039101
    0x5040c261608040f020303040f06110a030e010c0822030b090f03040b09010c050601080304030210020d0f050c0a1a010f08071401182d41090405030c0601061110 70
    0x860304540003944940c009c0c0034243d03014041d041d0031100b03400c25400040020000507040f82c800824002c0007103603640c184070b4040c0b2a40184044901140c3c014800c1001c00040c080c11400443c40c03415051000740d510f0010600810103c480104905a0040307064009500301030808080100c0795124900b00c0d810700a802c034045002076820303c901d03402029560059a01d461070340c014041d010101841031001c6400042040245030b0b0040b400c0459000d180c0780c502e4035014407402d124501007413010050901408021601144400000d01038103840620f200201e00702c0c1d83d1621507940e0131030f900407203561403003000c1c01c0d8106503c22409036103150780c54100110182da071099421845652510641c1c0c43c408112002588001e410006200801103c80c0103030f051401c0070719207480c010002c01c16840d2040780c1c200400c000c44143c400c084081e88000e00a070001e003070901c3c015603a6480340d07146180c940900800003c03d580034030030030f05034560b440d0040c18005040d00c0c2504003c0c0302109030100d08100c0e043c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 384041555 1250 384040305 384040309
    0x130b0d0b03070909050c010906080f0a090605192f090d0b0c0d050709050102030d050703060f240201021c09020a090f0b0424060305090705040c261608040f02 69
    0x241e0b0040254410024a40c40541040c5040062811100703042c411040c100308400d9501201d840e51107641c80d40195605e81310b03031002d00041c0c41d12190240c1880d04243c28071a042a141d40002c090404a600c104881106140301d0000c450111100040c5c10f22060402007aa0001c0c0d00208100c040003428501c0c0c12030660f460b00b4603040e040d078541d402c00c5004191550449050320896401110a00f080c410f154a4403000035138a1140840400090340c880c4041003040d4082d40121000c1c04034202c40c01d4100b030f190754441c22a42101441e4044102c0300e4141c01c03c0343c50041c42215a00c1c0c141c401c000700f00c03818100000010346040c0e041242c21805420300040c0da14000e00c101007940e03006102c0444d500b03030484d0401c030595844405030921001090709070000d11007a030400381d0440d802e9050108166544080807800c0c1a00e0b5030141c0d030845e05045034a01b5207076108a641401602408600c02c0010200400c00d18880c804c0320300080c3c00700c030040b203890000e0056429943c05031061094400303507642540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 384042805 1250 384041555 384041563
    0x8070f0c15061d130804060302132301080a020f03060d030c050618010e0c0108060d030315091b0309030504050d0602070c03051e030304050a0b09120c0c120102130b0d0b03 75
    0x400890705103082d00070f001850707005020407138000a803c4c1d90010b00f5401c6445103240e92041d84642011306a00141003007600705010071340001410000c48140c0808801508680380f030001680e0301d80020740300e00018410030068401c1e80ca040303000079003c41c00c66030342400340000900c61190540601400320781c10400640c3c01c0005920581685d101c0c0311146149001440c01d451a9505029158000c40581040b40c0d0380060056841001160416a5440541820741c0108858950a00001d403c2c0314049a0074101c0d4005e0111034030116007042c070002c001d4400701c0c100c4405080c01000180d0402040045d8680840c0d80820103000340001403070182b503076480f0351200b11940d00450721074001610307202400016402c0c4003d06a90341015500c0d601d025650151508101e90006000c0c50500003c20003081040180c46845940c0c11207a6540c1c2440d000c146a0396080452000d01c6070041c01484c948200c0c044c02030b14880111303803007226030150810020345055080714013690022a680c1c107400b1207941d0200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 384044055 1250 384042805 384042809
    0x708030a0c020f0d0210050d0f0603080c0f060c030f07030b03032107030908040b0a02150c0c19030f0e061c060305060a02040308040311130e01150608070f0c1506 71
    0x248500d030722601c4510601c00740440044007213100d034207140750310400751300c0d6030f0507500d030848031032609680d00c80344000c1020003494025010b0b0651840c000c004000c11000500900c2d0700241c0798107c03034210a601d05c20981c0c0b00001ca41004040c002400450075540d000200542c000c1001d06001c0f884c0007400003c41e246400144a1a9040a60300035880000d80f03003840c610b8006c0d002e0b14081c051400b0584460160384218440e12000040008a1524044c82441521003403003c58102448500300102020a5038201c40d0700800315001d821810034600301c904400004603a4103481c1c00e800c41030303406030554811464060301c540250b420019000b2440f11515002000000107070000751240c04d504003079152100041c14059094410001030000ca054030003510704483e4005c0c0c1c52050b681c1c0380c1c80465000c11080440340318035420020040081481034000c10105854505041600c0742d40b080100c0b052401512103101241d004002c410001e445000320201c124050403a00e00400440540312048035560b07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 384045305 1250 384044055 384044057
    0x6050d05060406060b030106020d051b0d080a0c0801030f02011803051f0f06080a0209091207080909070201050601120c0507020a03140601090e031204110901090e0f0316020d050708030a 81
    0x1090400042100314071400d030281824400242c10742d03050402c082e580d00c600900d0ac03002e2000c04100ca2064111507c21104080702210a880701c040c1c51100145c51124140c884080300c606040b08880e04030720440003d030490360490440d211082c107a80040d41c5440b03000c41c00c0c4241d080041340210228000b080403004d0150300410b4203920500002c48901203c034010400b1107018240701d402c1008070070025603413812070740444c1c0010f0b180d111880550f240c0802240041030724640421001b0510144402411400805440d02180b0f983c603070004030300300c4e04200c03401404504c0405081070710007907903071201e000b50006003410307854240f5a8002070350b000758980c0100c681508128050030504014040721f80100400e000c140400080200310701d03100d0140183c2d02961540600000f0280600740b0304c001d44502014126404650b1540c0c1d840c03014000d030041812180c03240d1503c2d071640e00d50000848203514129490314a44549a608004005000342c03030035a017600c6001c50104041a0070300040130a1682 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 384046555 1250 384045305 384045313
    0x210403020d0e0307030206070b0c040e07030f14042312190215011a090f0402120f011202030a1118011202030d03060305061305010e0d0503100b032806050d05 69
    0x1250000c050b0742c076a0030081e0094110540400060702c5d8501a07810482d803094070b29403160b0364007891505a01442c2d11100040e034108090010f070359015440005100a000f0003400100d02d126105801050151402040c4014a8240d205c070b10061640340c00420180105981c0e5211070000d0000c0b00da0040100264108800e0003d48441c540420280540000d07040891403650325110403400340718400c0c010404481000120b201c415628035400c400c07507141c01401151601a8400e40141e039100898200581151010011900b13403130050350341082c2580100204000060381c3c0c1d412828001619115402035035170501d40e2442018424041c2c06000d10f000030032446134140c0101407514003501c140c8420305103494010300103e040030039042c2d413204500e0000c04030218185441401003d8140701404030f40122125205ca140e4031000450040d25040400710703000380c440a181c1d281e448180e41070312050002008041c03160452171401e1f40c5070329070359100048080d620310104001c0d61210b4021201a00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 384047805 1250 384046555 384046573
    0x9100c0606080a03030f0c020105010b1c0b0604090c0e0f0f06210906041109040b060f030709020a050c070b040f0302280603060617010e18010f060905010302120c0105090621040302 79
    0xf030b046c0f11f003200000e210310080c0441e525014800d03107288a0001442c0306882c3d800600000e0009030382013504a85070103003c00380d8590340c82031080001d10201d100c1c61300280105980a00610b0440920a680c00300202114611b40c141400c1000700d90090340515041014003560001c080b00300121503100b2070500e0080d09040c42c0500d00b05070a0308020701030b03600c55a80748041c8001b0944d180d1700d042c0d028030f0a9524954007041d600000e40303014295808000514000500b9003022a881005482840510421540c600392100c1c5113070b00c0c40c081c40c000c0b101c1b10114034100f0130151800c8000050280f40002d02920102907021300f40c10040302075004640071035103ca80412007a5402400b003031100200c1c61044140354100302c2c0e0075091440242c01c00408400013840d001079a4801e6108881c5045161420024542d50fa030740c0c04041e2100344016886010104020250080049000e951b003179030503510745241c458881d0420800da0440c0785020240203803160010302c084100603c140c0214082d80090031441 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 384049055 1250 384047805 384047831
    0x301090807031206030f020603070c060e28050a2a08030a081e01052412011e080d05030c0c012306060a0c14010b0a0e01030203010c030209100c0606080a0303 69
    0x51045500190794070b000010401b0034800440080c0555040720090750747e171902c8400715454001414090245441d010b6181c105441c0010004400b0f0303007034100a850b41030fa0243d03400c243c9203841d030041c02c0342d04070000210008040b081d0002d950100103001000c0c1e5001524500c2d210701071500240c0d1035501c0000c0100c2c145800c4403a55510035030145200c0c003441d0100c1d402c403540d2101842001e0059013030f00c10541d40d1000074201c00e5080310910701b20340d8075181c118a07607080c83c2000f8880c00240b5131a011007901e4a00420701c4032010f072603048006110545c04e0b41c00464560380300902c10901c4040510015031380b0070086c0605010f640c914100002011000800207004c894050013852107802c0400120a425030089200441c190308500c6200052114041040c0940800c0310b205074080c180c7e18002c9070206200500e41e0581e03000760001c00c81020100300c250200d11426a40c160f01050105e10cd44d1124841c200c0303143c1e4a4402c4602050381581c60201c4c070700d840c4001c50b0450100c0d8465041000792 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 384050305 1250 384049055 384049067
    0x70203070b010f150e04021c0b090a0e15060f060309210406170a0204030c0f0e0702071d070903060c030c0e0307030b010308071a0103060b0f030c060a050a0e030109080703 75
    0x143c01d803080c1188400c0d240a05261184400702148003d1040d11040a61260350fa0ba05641c0c03140102058503403040d809058400082c40c001c4c0f6403620400800011607900141c500c2010645a0414002c0072600c0180f401c900e80440300070701c1d084d4442c0904288420715250500030f98010899030004040352500310042c03461050f440700c408501c001e024801000100c0d80b2040002030ba140c8885003243c1d54031002a29400380c4150380002d4003084100b036000403005246040002100d400d610300b80d5140c2c03907038102261103620034840c0b926a05c0c1c80880308100030080b00e200641041c51414210002a0380c0d941d203000f1f5031a4a07075408003080d42d03900700740c2c045a00004150b500170411005408581e08581d982007508006000c040d03d42c030000700307081d81084001d030700604400010015a80440d0380d645005030140c00d580229034080c40c01c0e012950514280011035010350070300248034606019045004980c0d980050751403a00300f00021a0a0005850030b1080001d41802a1000f0759501c01c203040151078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 384051555 1250 384050305 384050309
    0xc1b0303133c020f15030a02160609030c030f0305040809060a020309040504060e0c030616031e020d0c140306090402090c270a0b040e01090c05041d0103023102130e070203070b01 78
    0x2024043d41c41a010170340101125031080c0c0001d401601c400a034000f007907a0740380441d0300415a40c03400c1020380503d40c11801540c0010300c01d0380c40341c84d104050784085080d03420543d0020800c500c2440303103622501d4a0000340c5201e03506072044900b0320002d0703400102070711019602919010b9441c05690134082d014030009014a50560007030065041c009024101c4510000701001010ba41d0030041c1c011a00030035030540003584642c0c040d5101c3c5e031058022030043c0300c482c0450010480a04800400385400015280f1560b80181030203d103076200e40900541d613100809a41d040d000c10000c0301511000c0e0401e848200201e00c82c01e100c3c0101d4402400100c003840c1d00014100b200c00e2008001c62040140000d0540b50368076404528201149416916801641c1000d5101070010304100700d11104d0310101c9049034000c81c0c500d07103001e615080c04109529001d8283ca0600c5150308090241c3d81d441d0000c151400e082169010841d68441840701000010b07150140181c000040041c1030100d040e042d140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 384052805 1250 384051555 384051559
    0x20a2c0f010e03100507020f0d1106060f030c010e01050c030d0b04051026030d050906070905090105030c040b03100c02030d0b010e0d020d03030b06030c1b0303133c020f 74
    0x200440001c00003a1391102c2988041020603100d80000b02c0c060720038400c410703030b034000b034011107502211a5102828840c1c0054081c4428450100081c00e24030701303c5100801110050050303c00d0b00c038054011509589840b280700e0502108001040c01c1c40030400003040000c014000004a11030503000300070640d44064821010b070507211a05000c048400e000c40219442090b40841c0103400001d0050305500070002001e04961800003000203a179030108803544035141c15640c8584160322082040781d0320b01d0030f001f0103404da4812000c9003a5800c1952051102a20080841782900c182c2003030030003a10000c028420042c1c20100c0e40000c0c400c0c140c014000710b00c0090a00343c0d03180c4002c201290382107481f10006442401c801c5518000d06000f41e0110751426006002141e072840c3c82c03049103110b40e000c0c401c0140300c130640d000a00c42614011042c1c900034450102c0c00c0c050311815840722240d1407000e01d00e5a600d151a21288811030b08201495401d60402d40c00d1f00e44403c03258010000c0001c0d003400124 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 384054055 1250 384052805 384052817
    0x20105060d080a0516020a0303030509190312020a0504120303090212010c1b020f04050f0916050901030f0212100605132a1709030d06051210020a2c0f01 67
    0x2000003075144054640d680010300e0299110840301074007541e041c1c080c40f0047e42103403d4aa0100c14190f06402151003072000508507202c0000704800c00b40401d102820140014007441c0f01491070041c2c40e0010103287d1341074070700341d81000d882d2502c6208034140320004a002c01e81e150300d05070850911904203040508110000c000e9010010750213829150502800041038148074800f10441d512040c2c00c0e020408040d200300281c4c68034140020354020b0a40307a54032903119110300780400700180d603158030558101070440d50142e40303541c0e900d001003040080203c2c0d111550395081c2000c82c81c10406141d80244075500414160300c0c0105000081c00c1505415443d14100380340c900b0340840807040c1c00ca9900000e040056000854081241c0300101c006240d56502c008405009010320000064002d0661000c0c0800c010340c1e40300300b04060307441424547c00e06a00102c00d5208250150742c064950a41d85040404c0b52546112007007820300581407030362001640e503540c5200d43d03042c000f2002c1d6504800303080036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 384055305 1250 384054055 384054079
    0x609060503010603020723070303080a0c020a0b040c1e0f05092404020d1406100915110111030405010c02011410091104031b0905060114220f090c02010506 68
    0x20003070720050203488181900014084c0810403074104c868219103e107400542425000c0c0340d01c035201d4071540300c244c000039401008254ad0a00600c02e2040c480c4454006110584256031450a80c010040042e00d400001c0c45000880c4180c5165003c41610300e00c1c204020b10303040003035844056a66802c5207004688040801c2042c00415001d05403c0f0405084e0b1681081d809002070041e10036190300c104035178104010003031a0752108100c45c0c0140c1c02154900310b04411004200c500c46450b129044d4286910400c2d41011409246440a4440400000305104810040020150b401074030100c07070583d942d1071480d65440c0d0a205203038151035203d0602c01c060604607011103010425004089206139103200181ca03000d80b4108450045901011070003600080100c0b0400050043c401c1c446058100000070f04c656129159000031010300e4803a0b2400c1c0742c0c00d00c40c00424220324000d4915928044107011a40d00c408502c0e40004040c90700000c242d50200b40c200030b0a440c4050070340307030194041400c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 384056555 1250 384055305 384055307
    0x60f0e06211f05011404021e0a05091309030207170a0c0308030103031101050c09060901111203010509090f030d0b120f06160305010f03030c03141606050612061503032b06060906 78
    0x2003020076942190092385904c18040c0c3c6400e411450ba81051314580300040492003160014003a0084803c1100c04082d5402007048490981d02c1041000700143c211103410f01400c08a048000003020040381140c90146007582d642c03610b13028070742081c0c3d01007a02000400c101030303100011550f251720a0b00240f060b410000c01c0e0300c1103401080d0005200f01804030300080c582c3d1282c54071810b5003c1c8901240c0302128085d0f0002001d0b4020301030b10f800341c8541c80c001010300c480080c036280c03101c55000081d842c00600d005008014420006544d6204010310284a549030081011082803000c40000e000a41060203844004140101a00d400c1c5400e00004008845000b400300742100d400d400d140400703082e9803038100c1d21422140d0b446194110302160302c81310700c4035421042510521a241c02c011580b580d40c10032011203242c6014031000c0d400180002d07014148428a805070038030141c1103a04206d40d41c00000b03000104000c00c1c240c10300e0300501c0140c5901250043d007009000d0340c10074190460130054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 384057805 1250 384056555 384056579
    0x201050a0b011e050a170123060a020d031802101218020607080d021207050403050d03050f040f06060801020d0f060b0306090708070903062a03060f0e06211f0501 71
    0x50f041c091001c00308210314641d00403210000d20040d68024812250707120784285040058a07150b511600200321000761150030418104c48a10402e03800030000841c0f03d503801c0f006000040b21422446207007111034801a00e902c6150801c1c40c2041c0c407404260b00c0d020310b020382182d8080c0c0107156080c060f2040480580c0b150003c0340c41c241d0300010b485030346100d10384280c1e01074403444411560305001e100402850552110160065038030030420341d021100d2404d000c600b510810b542c2c5049902e51741002c94002803070301001d011018070809000c00c4c0c0541d544034041c22a0441010281402d45500323001c55451158440c18000e00b04e06200e0905600b04280495200c7c01700800312828030455202044185004603d050000e642c44002072001540e0707503004040071592094607440682c203800203619564003902500f400e40d0a1200c40500d00fa19180d1080e100100281500e904400100e5000006101d2894860b03400e103401402081a4100301030502244200100002c880d540b0f841c005100c81a0880 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 384059055 1250 384057805 384057857
    0x30303020903070e070c0308090102090a12030311130f050306090a080a0903080a0f0e151606141312020a02100e0609090720150c0f0d0204060201050a0b01 68
    0x1140058803615403002003450715105411101549480b0700c00c00c28900d82c41001c0c0c4140361b00c0b83c1d45400323076912188070301d5080c3e005608803690b00c107600380c05c02c0c45602031240c070320b460107402840c0114802c142c0d4125090950301440e90030f2101c6c00c1c12142481011543e1038004000c0500b50020000780c503205511b203440c0d24440fa8010174800d00000c02c98000c91113081300101860b00071f10240d59559a1131f10141480c0103401c203020102d41e03160440f00c60752518108005150305a140c1c4107141c1510030040c05407000300e0300400c880255840c03161110700c07610701c45041e206400340b00740d2408800060030081c401116220b00c80b011544490710f000010307103c407032882c9041a103505015029010140001e040750042c48081c603041455039081041c915401040c1d4400c004500c03800d8180004141c1130107460306070001c0801c541d8000704022400080d150001407903504c10705a0718500340402a0705c407806a920aa01c4400141c1d16002400b546464910403407d034050242003d0032081425008140380c00ca01c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 384060305 1250 384059055 384059057
    0xa0b09150c0a0803010b030609090a0b010302060d02040e0a060501030b091902030a02040e0708071b0807120e0a0e010608010501170a0b0102030c2505010201140f040f06050f0417040f0303 82
    0x4208268020020412000c07280e03070000f0b01c242c072583c44140030f5945410880300e803489407500b075020600c2440e004c40d810380070541011003080503a08640a100956110401c1e12a00c00d81c03c12000801401c03404445025041428001c5019481c02000400b80d81c0140c0c074244c8035001d03404c148040300104103030b60b00194600301070158480d903621031442c0080c041c40d4007120b500ca81c10401c020005501414035481000b15444032074440c002841b061045000790711005140c400d0420140f000300b01081c00960003822145458510918600046100214030780d102d1620500c6440050020580014185015100c20b00c0c0c24041c5040c445600d449051019016100c00e940d102c0010b6000d0b4801e2044a0450040404607028550125480541c0790801c4040d424800e02182d40440c9175031060084011280359192400f80940710154586060301010344100d41c810310641403107002038054000d20344955605001c0e03c19500d0542001c1d40b8100d2041020201c20604100900a40c4814240581540c0d09 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 384061555 1250 384060305 384060307
    0xb0a030312111314030609120a110307020d1a010608070f030504050a0f0b01090e0309130b0a05040219080109020703020304062604032a08040b0a030608031b1212040f02040207200a0b0915 82
    0x94500cac243c11880341e810041d401c030020104110034000d014040402a140603c0040f07030b16a0b07601d808880c0194181d03000070000e114100440d280500c00e81100d500280103100341c03140a07161390340f0608005a8200110b4494040310700400c100741c0d030380c41921410007425010307520349040c90001071641c1d2101c80340d10342156610502c098654843d0303c14140a080301030001c45d81c50002d40008012407440004100c00a00c0c060008502c4d84e40c0c0e8026101e000e40c1c990001c50038207007810800d80b130120f0ba5400700140c0d41c81000c9209000d0b800e00e601c0c0d601450098940f54000a8002c0c403098074190002600031428400f0641d480005841404540850f080c42500030303281e02d020342d8100c000e06410f0380000f407240701c0401c44c2820048800300c102a8040d900c0304a4820040e0030602c41d0460090703035460922480041c00003404039200f52011748c8a6413000b0310040c907200c1950303500001c2c1103140c10008418061b8600111250408032140c0340508071040f00b0904001003400041c0c4030110b0070341c210401c460 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 384062805 1250 384061555 384061577
    0x604050c1209031c02040b0415140d06030b0c091503060d050304090506091311090a0906020703090e09120f0915030f06040b0a030312111314030609120a 67
    0x1030500306640740308004410405103402d1a6094582d04d4000c500a0010844100d120316035840442c4216800ca03621030350394506082c41d11030a4032a02d24403107414802d204d204125440d4283c022001450a01a00c0200246a505604103480307980710081802c0d0a40e1010401e80c1d4440d42c500c118581e1b007181591055580e80e40c0c82003c50011211088018591311000ca00810075070281c3c3c03c00b40c0305c0e80b019214031086aa8014084161a00400016190500b04d2224030141d040c0340328540e034051500e00c030100b0b90b4480380d03076214101c3c0e001c2c10044d0b00180c00148140309807210040d042d41c000c0c0c81c2100030081c03840c00c99060b045074490540e0011044000041344803454075400070844003408009521511391501000011040e90101c3e5190b20541c03030114500e5240c6410740c803e0040d80d4140d9200d00c411040802c02d030b402000f50b4006000d0040303080c0070030040003100040e8030028285000d200d9400340ca802c010b06280031005811607860380c01c6840d01800c0041150290f07200ac413010f260400d1044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 384064055 1250 384062805 384062821
    0x5030d090309120c080127030f14040308070b0f09070e1801020309100605011e0810150e010810050919020403061401050f03060105030304120203010b040606020124030b060405 77
    0x40e0711a401411860503250180c030038031a04203034100840b51000020f200541f45c8060f2603000b41e421052503281e4201410082000c24403c08441514192900307020800b2842908403d6882d00070340e0044984200001c0d22208002c3e0002c4a10303000300203440316a41c94205402025140c0404c2d008555004207504009000d4201c20031500309441040c000841d901d00b00304004a8840642a0503030480c2402c09a00240039482090780e013031683d50213540e0003540764130f03038030116203411000e8810341c00d4000800e404100052020100480c1d0b03510b588484079007030740301f1001500c84a0010700c0c1032a0555001c000304070765200c842a090340140030a912400c0d60503264a490028021504064602440d010a071541460780e8041607058880c125646000d01201e4400c25595103024000d0a07059081400304000301103118520826603840100049400c0d0701d100f02003000c860040e0312000041c0e4481144101d01c0c0c40084114010f5004480d8002282e400c58541c0d009158010f086903000701e0340d400014041c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 384065305 1250 384064055 384064067
    0x2190e22020c01090b1602120901140901031d0303011809080a360501080a051e0c0412051b0324190507170a0b0312070c03020d06050405100905030d0903 67
    0x82c1c0c5c80f02150b607003414100c170401090740300e00e0841e50242c40760346640c1c041000440d040e2240c42d841690342d080e900d56800d46440d05c503040183c100d414140c9030b0310b410010b9a0b48007078800a104023900116160340c0761011070103c00b031400c001c4d000894a45002c0c0340205028100701d406480d81401c200201c5480c450300040313001c83c00c00d82c1c04003001c07950303005004242d02e401260007200c0702680c4400154035032144000403150145d8887c0e00e03683d0b5000710300c0703e05102c1e00c02c00f42e07201040304407207803d059541c01c00700101040d284c1c0407030381d41c0c11106071001031071300c0e00c1100000c840082d40240141c1c82c26081c0c0003410300c0d1239400440700d600d00c100050b810b440c00d0480c5004040c0a07038818001418126409061722080c90280102a0141d00c0081d020b00814804c0d90002c2e4401401400c1441c001c144600c0075078072104003640c1c3c4407a0030002001613141c7c00d0b01d20007002e02c11000010580342900300a070404030304607801181682404205000300380000143e0f5020b151000000404c19030700d260980d10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 384066555 1250 384065305 384065321
    0x3020310090c0e18010c0e0907080702031e0405030d140706050415020403030309030e040c14090301060803031305010e1b040b030106180b19050a060c030905030102190e22020c01 78
    0x3070280043c2045444c1c0901c008104030440e13010003d0002e440181000d445030103000c104260017880810018070064441d10030b00b038100000e80142c03883d003000451500761000b5070541c4455120380000c0e04004505003040b40103448005072900a130103501d205003401682c425404040d146c6030301c030400310f4103004071040c52180e98408583d0071580c0e03d544c2c3c070700a000341c40c2c01141940414030012041080341014021964551480d03690740b442041d40305c544030070360b422010780c1d150150b41c0d031800803e00d01c070100029809400262905003101040707103403d41c2560340d051011086508408020340080c1c03100c1c07100003081441150045a81c60b81680800d00403c2a607100140084880319060000c1c901ea41c004602103d00352028859040200c009209590040c0b0840d500a0070104040010500c00e82c139002503c4c0c403901d0500310542e6a000064207a8114030040807840b100713046000700c0b0382c1e0030150312040a0020b40b41a0350840e655484c032014024003d80034542e440d00014403481c1001c0039484440c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 384067805 1250 384066555 384066569
    0x1e05210f011511100e0d030b03070501050a0210090501060806101d090f010c0810080123060105040807062c09180109060510090501080307050a020f041107051c050403020310090c 78
    0x280b6030131803d07500250100d00840070722070061800c6080118443c0c0980410b0800c080d00420201e0720f0240116400e91185110714214001c401003261942014040c1e000118054000422280c1c01c244081c0d0910002401048003820003200411a02c0d1030f8030481c00c0c1c5101c0b600000f02142c0c1d10b064449050000c0c079002c005840d4a0705020507200c9802942c0700b40502d003071002c02031909881d201070a080311599948014210465030601403034110152000342d109106140c01da01382559901c4180c0350250582042c404901c1540854582d06a003030007141040000610543c107041682c00032952440c4003401e10540600c21100002003040709400c2a000f081e4410300c10402441e04810001e100f40d036074040c5520107070600340001048800007055861954004000c1c00c101c00c0142d0801c030341600300c0400740340c0168980c0c0c0800c88a0140c24064501c1c5401071002d822101080c070f240402d10000c0c1c14000302800002e000c1400562800102c1940801c0340c0c610014a0b000ba80c20260640903541c2d10000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 384069055 1250 384067805 384067813
    0x40c0e07031a0609090406050c070b0f06041503030e1201061e05030c0d0b07030203040213060303030c030f0c050d090c0905040f051209060904020a1e05210f011511 72
    0x4051581c0c558000311203268042c240014050000d01003180030f20803070000fa54000d041c01c0205021440719400340b60000006820701c0d18046c00c5648406d8900c104580312024240d02404004042c1018011080070703101d56403d03a40047e046950142c0b1108110300198000d4135801e80e0000303420380c25807020024007903107000c81c040070001038003c07200c00d403045c05294007a00030410400018141541c1030300d01d007030b4003003e06901c903500c8001c2103009420080050384d00a0916060701d0b00717002030748039400286000759008200c0b40c07801c003400307001e0341c441888900040b03107001c00007200c040e4000305803401c840f00044007048000315401d06106805503600000c19061400d03041c003007005284c0c8007900000748520b0507244540d410906000450143c449880d4101c0f030108141d950303501d070503801068402000d08004280c0c21540d85001d042c08011040c80c1c001c02e00000b403001c140c0800081807456101040c10f05103441c80c11f0920311a51041c181729443e031001b814644904840c0c00340c04060041a8088200c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 384070305 1250 384069055 384069061
    0x30605041e05060f120705182a1e07060b0904050c0f04090501050705030f0f09030405010f02031306110f0c0d140a0503070b010603110307020a0213090b13022b0605040c0e 75
    0x13446e00c03841d9a10413548640700500203104a00f80b10326004d446040006118204034503480c0141ca0007608400e16010000002c01101e5100c40540c01070100c00340d404468540c8905103840c10b80112070340c200c3e032541302c0d084d20f6040200140c400104003601c03030f0050b00c24074000104030700450041e02c2e400c10700400d00d50170003080224480c0e000f0040c52060380002c800f850151204102c80c1d00422059816484540040005001c035500921a6181851292048070b2500311565040c0c100d4900b550803040009110b2000300515103030070014440752070b034002c0213081a240b110001910340203001000402524024001c00124007033030045038807243d0410b099994642c203500d8007248c110400d000c0c8001081c03070141e6102c02075100c103007624803800382c030b80041c8991111602040607020082c8403c10041d621101c6400018074058581c034090005104e44d44068030b01f920400c928403040d2042110820700d85424030780340840d101c0781e1001a64001c84002407584a6040c42e0a5801e0300f5044490020400424 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 384071555 1250 384070305 384070339
    0x3050a0605060f121207080c1510050a0609050909030f0304030e01020d08070e0108091002040915090507080f06011403070c030306060801050120011503030906030605041e05060f 78
    0x101ca031140c142118514841e50603201080394040490065041540c00480200c480e4086030b0300401e84103000e18031090400c401c040d144c5240c120813401c55100c6951800c00d000b5031000c110204800f5010855502e442c4a080c481d00400460071032040e01c0c883c0e4410804140529001d004131003001444041032a079030300d05400d014042c43c0540b1540c030700600c220340c018000310f40f190b400e08e4050440b076640c0080071030f000c1004540301103001d00714104034058140c0e2640300603000d100905c000d0500001c00700c0d00144021220002c0c400c00e03406502d085080508006240d507020740c9455001c11117075481038a0341c0310040100d96064461884032080e206c008148458070f90014031824000344241d8017440b4141d2039040450b11900b0a200f11804201104043c41c010700035a200a003680188000015603c1e03560f5403076000c4114564029004110208414040c8039450300445c000307000c0644050010007455403e4003030000c2d00c4019850b5056484010900c1daa440101248803a88010f058044059011003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 384072805 1250 384071555 384071561
    0x3040b07110607120b210c0405090c03120a14070c140d022b0203030f03090709050702030a030b011823120c04090221010c0f030b0a0506090a03050a06 66
    0x9414004220204072441c01c00e04002a5036100d241c0c00d0342d51011048032002c10501405030030448580c084140070059001006003c503080002d09220011702d1011207910070321046a40140002c8c0480c0c0100c000c0354982e80300000c01404541c149008903590f0b45003007404070307030b1074100348408090031500054a10a001c683c9101c0025205e04001101c00c50210004000808428850082d003002c64580c0442c0000c00144c2c11440c10390219070124041707a0fa80c0e00003404c580c0840c407550a01c400110601020480411490020f8100700750104010f050684000c1d649014040300c1008054981b84a140c90b030748034aa2500c3d000f00480307000b1040741d4403107462402c03d100c0c4800860640d650500454120b00d07040024107040810b540240c804142c42e14280005408400001d07a0011221100c082c05001d131407201271110380d084400040c11403080f00d00100700c0038071400c0c0d450815042010801155541089040440714225805682d83d17480c3c00106010491a500240481c00b90300d655034144900b60b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 384074055 1250 384072805 384072811
    0x5031c02030d061404110c060c09040e010609090606120c03201c05010507052506140f040308060604150e01090f080c0f06040815040302010902060d0c0807140a030203040609060203040b 81
    0x41d01445811b0710b10000341c900780160101c507101c40c0c3c03102c0082209010048010321509501410100741c11000314002400e48200d40e000100c001c0e45d440c03070001404198803441000d440000c4420855010701d031604001012140070290080c04070b46030031031400e500d507000200ca04c403000e032031030700000c007039071030318100d41010040c1a1595400d20340028203649c4103404803484140200a501c0c4584800880e0b1820341c20042c0089032911b94509601c02c040030440c025a01c108030440002845240503c0d008180010240055008c1c0c0c105100901421440c3c1f406104054420b14206c03940c402e9400c012214071100381d12444413038840420118040e4000b04902503200c8090b143e242c5521450300c1030040a1055102e01d01c4150045000a03000d00b09486190741c0050092001080110a0360000340c034a0f1f100134035061407e542d8094150740c0e10b4003e54030950180450400c40190079880700035000307034480d50900d0410142e0010004081054580c0450040c5070001c00071034803440c01d86002c070720b103480503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 384075305 1250 384074055 384074059
    0x2210105011505040303180803040308031501080411010509030c2205010e100302100201140c040e070804080405010f020f0f031b03090a0e1306050703060501030e0705031c02030d0614 80
    0x8000302d6018005400b032842003065641c2d0a203403901d5601d045400d5110243c40a140e504148000501c40318100091701c040e50003440c6290346c07400e040e80500d0b0071700004104141407124032401c20011680c080d4a0403101ca4003828480d585003019800030b42050502440d160380b00151580421f1260004800c8100c0c10069107802c100a0341c031b559131920352070400c44582010000c0c0e20000e000500b4094041c1c1d14102c846c2c000400d0607010007580e10b54403a4102c07460105114080703401c104030340c80d03032203071a4104802d030401080c0e0381056110b0412030f2103540950743c1442145480140702a100b040240c0030b01890303509039483c1d0394850030070b52f45031303800100f203071400d00211051004480f00100c21200c180d400104062a001c0c43e0120098100000401ba1021006c5940c0590302092241c050584640c0c00e03950001480f60605001404540d03041c0c40401455100c075a080c8225280021002e0740500400f000880980040000303d1440c07065900c0300c0111800c0c4000000c1140e80c9076201e80c3d1020007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 384076555 1250 384075305 384075311
    0x1401020c1e010b030f07060315081c0815011e09050d080702030f19060c031b020a0611070206071e050d030608120a050d0c05091207180603050d1803022101 68
    0x30f54010103607100311104100700b00e40c010090400015019034052506524445ea40002e12591803244a00b0207020420081007010201c9a01c5035003540a21f4050348960602a4450805042c1e00002e00030703c0700303c0c83c4442c2c118180125000303643c055140c290043c823004000c0f500d5000fa500c1c01d480b60303404c5204104e00a01c22000c01c0b0700d80100c04210a004c0031141ca003102c0008010780c8a58001e000c2d06602c140505580c1c407021901d24200030407a07006010750350020f080220151a00c481254010307450009000c00c02d005400050f61031008440c030054102440c40702c0d8600e2580510303111081d1160040152082a030380e00c2d003954050700400d08071880314056070704c81071000700204101c1c41115007081c00100100400c0f46a500d1907401258141d031a4641542401080004598104903e00c80040c00380e100c80300410041c2d85c100461404201d00700c03014441249156510303991030310300101d18401d1180105401440d202d04d905201c0045400802200650700c145511160108250840d040c055003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 384077805 1250 384076555 384076571
    0x130303021e1911120a09050d140c0303030910050402030304090e06040b070e01050301050d1a09010e010b0324150d03032324060f03090c120f0601031401020c1e01 71
    0xf0042c031407100141c503402d010300420325120604d821036500844484050151542d00411280c94503060040e8444c420074001140d03000c000140c9180440e02a5400d103c0c2e801003081080042001c1040200d0054606010030240c85903c00603046010326044260b6881c5010249902c41c0d40000d02c80c5c2c000d41c0a103a0f060341d5a15508030494844e803006020342e0105004100401450402c8000701900a0083d84880140303094944504850707841a80c1240039a9114025107440c0702d028495140c1c10f00c4101c0042042c0e201c800c80442c0c540c40300c1c240e44403d4401c80c20001d8120503940c075000358041002401c0350030683c01c902d000340c0140b030140d20740300525140c0c1d2003058000c0180c10049004406142080b28440d0a401c403002e951048029080c1c0c00040900ca0307085050303003840295003e401c074480980a20144c100521240c1481992801001d80c82400d000124540100300a41902d40118501a0314501040300601a109100c00114180310746042c903442e085082031484501d440d01d1000b404502 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 384079055 1250 384077805 384077807
    0x4050106150c08091c1209060e0303120f180a03021506010e150c01180506011e24050f0d060609082109030115030803092103130303021e19 61
    0x2c26810002444500100300c189014600a039007280c503000d44205203611145695501d4422046103203102c00803444941080c8140c90300148980741710007082c4e00075400c000c44d28980c0084000003070400303a0a200b0040100309002600444c0c1e104411010080720244541854002c0d0b031105104010058501e44c1c1c00070072004d41c4903646e0110b414000420500807203000c42103d1106900003800701c100340d035950030868415003000e8131140d580740c019006030030f40758900020849a41c901b440040c400390103d42c0b0511000c07090840200d18526015843e100f00007558000b03460034032030b11104111860020440700b4008209400003404c2d184250781c0ca0f03203015518951155640482e120201c40501c140140c0d5002141d0103000d081c0b0610000c0020442c260011481c1501e04a1a003041e0340440f0000b0410142000c1004890030380e49035560180d0b684000b00445101500001e0b15a014000031400601e040c03500c030b90181c2d806140030008107640b07034040c0c0c580c540302c5500406480020080b800c600903c41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 384080305 1250 384079055 384079067
    0x305010b09011203110705180114090c030103030c0302100f020318030c070302060304080904050106050a170103030c020603060d0c080304060e0a1512020712030c030b0301050712090305040e0405010615 88
    0x203c83c0d86034043c421014655042d02d55000c0c451076407502c1d01c1225030000c0c442c0d4603500800e95003400102e0700c400b2075045c260001c110810600c00a030140c55220188803449a100e401c4078112a01841c0440182c443c0e46412030510018100141c5540d08010740f00410450581c001d60040d4030b044511821071299010058a80c000d90801c44500c0c5c2020b1410005804c081d0700450740f140c800c40000e450907044100060444500380c04c544000340c400300d02d041245030000c0749501e00403000e005403501c41d032450391300600724460312000034000c00c40400429201e4442100e01401694060310441c0e100762a40815a601c2e00140315020010701d805000c0c4500741060011b4109036002e000c0c40540f4528a50015503240021582c001e034560350070480c110100d002960314000818856901103680700100600405071121892883d110b42d24040600030307900d42028025a0b010040003010400f08510305041e10a07006a6000034001d170407130001c00c0100601903001e401a100d0324060310349048000e80e000c0341c130 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 384081555 1250 384080305 384080309
    0xa05060307230a0512030c120f04090c26060a05011706060a02250303030609020a08040201030b180c030106080106140304020f0402091810060201020903100b010c0803100305010b0901 80
    0x2030102c00341282e820070a10b5503000c1c051101c0c09401580c03065a038401040c28000307a40018640e503000401e0f0308820380000d020890f42042c00c401502d0601c13030410403480062240e0310940c4000b595034416641c006008601030341880d0201602002403030076107010002d11040c1100c0c018401d459828002c1010740c01000419800021540043c64947da24018040302c2d500c10309440c4d055104941144a0b4001a84407806018010902c400103039403440c074024007500c809400109610b80103002c0b85907880d5010b0901e0703911640900e004601d500201c0c011500c0d00780780100000b001c160400030003220110400c01941282c0c500e035110b808a81c3d81ea80115000d00c02c541d404410940100046005440d014085100390b00c1d004100628101c440d900040b081081d030309407002604141401c1110840303002c00c00308002c0c01540000d5140c06200c4002035294034559101d50005a92030394101803991040c0041d070705d0582d020295a03541d041a95030340102600d184000c032480c1d820030081d4801810400d0070681 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 384082805 1250 384081555 384081569
    0x203062e030f0c2f0a03120b040608030a080411100203040806070c0f080a03020f0415021e10090809060f0d0c0c0b0f1f06030f051b0405130b0d0b0a05060307 69
    0x41c005031300421059182c0c3d0b01083c071900000264508401030507042c454800203600c40e407100c400000b00d0300e032500291000707482928420391812004001c60400801261841d04551421800700c0d0345502d00800e5640c40040311581055a4500c4d036120320303130004010002d0b82c4040003111034a94604a00300c03800192042d0061402115426940c0014011405030a07850040c5c140581000c1c445e1150741e40d00d4020383e001c8603191001e4900400c4440c2c040c0402d655540302101c1e45c0d144080c1e6801030079901d1580654058005030386809200900070b584085d144903107401050640d640700c0c1a000d610b6940c02030340d607500d4203030710300b41560607614098a90720b592198000b40c0e500d07241c0e0341c035800015020002021032a00071540b03203500f02040c06080c0c048015104a44001034603643c50041c1d40708403040203100d465503540c80d419000c80c02102c14291000c41c0c0d82128010382c0ca26100d9110805403944903902c1d07401a0b0000c840c03104000a49514521a403400001080039035100740405580d15007074481c2d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 384084055 1250 384082805 384082817
    0x305061f050702010e0d1106180d20010314070c08130906050a0b120a0902040906150f09110904020c0721021206040f03050c0f0304030506150904150203062e030f0c 72
    0x4404e05240c8040c0080d004508102006074601c41d002c01c4d1004500c03807040741d04941030650100b800f1448004441494401e00c0c1c1005a9800314455400700ed4000d0541f80a11403040564020044980c00312044604420301e100c51a642c1c1d0b6800034041c1c00b15001da01d1081c2040680401c40c44590402c0d14544494407100c00c0c41c40e00e030840740000800f0100c80983e000758554155001050290255850102c0c03030a0078810320620b0311514244c411959041514840d05000c4c0f0b0200b41503802083d2003040b40100c50040c2d45c2c000c0ea0248505d461003d9101c503e40311460211070400d086856084900e4900a5a009042c214004441a00e50a00300e6006041210510720700000c6407050b4050000f04058108680e8004800d11885185400c00e0380202c42135480381041010120842c0846646030a043d94011902c4c2002c1d40e500d01c039030f0a0085016501d50340480015070380e61320210045c40d901d42c01250008091101403036280b01c200c240c00b010340072908000c0450f8207102140b045921008881d580c003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 384085305 1250 384084055 384084083
    0x7091205030f03060a0b1219060501140a030e060901050106020c0d0203100510090612021e010507080a14070503090405010503070f031b08031201060806030a030f0305061f050702010e0d 81
    0x312043e08080c0c040e9030040309010000c40c840140b100203044148443e0201001490301c0920200100d40c40c3d00b0100725681054410016643c200d844810410030101c1003545a00580804600603c072414840020340314030401d00412042c1903100300d0580d4034650a495a4a000406118042c005054001e4143d8800c41e000d101c10320440c0d000b1a0081138409108100c550307200fa07400155007058110700b101884a0030660304500c1d08450f07121746288080709020788240c020b40060118050804050066500011651600e51050310701d0001020b620084c103485070300e1410f1041d0344c1e800184000d40510701c0e02001050516000400c5000c5540028001581a096a54410102c041480322002015007040c0c0450300060a002a1450240c0c0d048030005540c50000020500b02000d01441d000c4d422481101c00401e80c00f0210010032407903410082850b03121080898005161211046508010420074244a0341d00000608006000340d0340d0b0030500701980100300240c0c246610060018481d5a80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 384086555 1250 384085305 384085327
    0x11407090b0307080609040f0c09020a090f0b090d03020709110d0f0e060604020c07030831080a121b06020c0f0105010b1909030b1504050f0601020c01030b0a08010905060709120503 79
    0x191b281e02c213103e0091501070540301d0703039401003c1c0340320740103d0f10b40e507004200049003591250700000180140405c0716000361a2402e480380c40e1140918035400351034000c49150905000304080802420300c103804110500d8000c0b21140385802008a00c01300508200c4494a5807a807401405050103803940688200d40358601000000d5010054825550003846800001701c1d07001c80240ca42a00403800b521010102c0c60031081003026036101012178000c00e1201032040950004640c1401340c4d1003a801480005501c0b010b80b912104806d885901c480418003020400030070750050a82c0c10f441c10110769505118040540c241d4109000d00364031844180300620401080201400603840142002141c0780e45a41f1040c0801c00101d03429a1400300010541c6c6840c01c0600c2461740c084a600302c0c0460905040e40000e4844001d00b041c1d504058441288102581e0303844202d0b0002d1558130002c00c0100302c04d01e00b041d1109030480e83e240100b41d1568001503648a2000d8990025600c240a10725049003044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 384087805 1250 384086555 384086569
    0xc0e07050a120510060f12020f0c120f070807020a080604050a02130e1f02040e010320040b06090904140318090f070504060305090709021b070506090307060e040e011407090b03070806 80
    0x1086c5001c01ca6000d0800d030108031544028500440362012440e9680f2503010110303d0712160746810441c1c03034020801c12a08030690b4003990000e907400500c50395204543c3c000140e0144040d00680700a01440742480100800001e4094035103109943c9100a40b44501c181c0302214240e140c465184d410a40794201074101e00c0c000160420b001d85001401d0584400300058002803d03003084908044902e00341800c40f00d50300d407840d140700e4100d9040c40f860421401140003030045030921800307007a200c000f24003000008804410608600c00880741c980e201052000d101400004000d40200c900401294691000300c00151007100307030340c032043d10341890080114003c000043c040381560080106c003081d0400e0342c1c00146200c0340307a280d800c840b40c3e9081c40141e00b008065402640700380000c10046010b13807800b06120044a2042c00e14803403440384140803c01030001c520507103005500c0c080725030040c00f20006203640910f810f584c032031081b07984401100c0720b103100986131000400c115070001405490b01e41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 384089055 1250 384087805 384087827
    0x1e0c050405010f1701140906010e010b041505130e0705130b040308030c03150a0b030a0c1e05070c050603040c060801060206060d060e0a0614070e040603020904030c0c0e07050a12051006 81
    0x2800010300304c030301b4a001803642001562409480e40218004000420a004025000d458110081da1903c0c1c41e02c070b1003000c00f1000790001c0c000c4c0200401c4800d0002000c2d51b1003001001300005040861400e950003c0840c4d01001d00694040640c0d0404246c0e00140004d5a050701c1c0e001e051a0f2541d2100003540e00360390001009551451170a284408903900c510310910020300d03010307c0e0580c413400c0000d40401074400c080c99050801503140021480c04402201844c41640c15003460355807614113081c03081d80d20700300d034005170b40014001050000f0492000c01c0241214801d96500307881c1c0c1d0300c41c0340403070f2101c40076101e20380d01c095550225004140140e0003404040d1000c4103c0e002030b070f1550350325003d49240350070740340840b5000030030404103907017200c00350f880f8190850b010004a41513034002030340c0ba40094805410400c1705100c000802840344005000381242c0d80c140c445c94600321200070040e50100707010b18001501c0581003100d2000e540103141c040c0300f648030380c800c0942c104030f002c0b16441d0b140c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 384090305 1250 384089055 384089099
    0x8060103170c0f16050f10030203070302090616020102071a0f0319090308011e030201020a080c07180920030c10051b06090613050316050102071e0c050405010f 70
    0x800c400b2161150802a00c1150000f0b00f001d04082c80d510f42050490041a0b4041c0d40a101d2090680c60a5911984c52610711141c600380142c40b81c40c0d030042100240500c0070782a80000000504c10608032a031810181d4040c400d070700b01e55110303442c1d40344048111008484103801541c18460180078030303000740107190302250310041204040c81c8000c2c0d0304180d4030040815004140210018805a4148151510418205503100d1001d40c41c5600003950340000c2030340903040348000b04584034049418000c05001344140e0005000b41d10b12558104006c0c01c20307000407581d82d030182240600780d51402041011b541c0006001d09035038100d19052114644189403d1000c12804005450012003048852011801824002c10075442e01c5500f0f1442e1150107000c40d80c40070204440000010400421180c24542c03042e50300e502403001345001400781c051b2110040c003618030768000d8007400c0308000603041c400303000b60361004150b651402404120781c4203000d9010303c490720181c140000c81201d95040c4881c0c80f9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 384091555 1250 384090305 384090307
    0x21203090607080d091502071103030a05221d07020609011b080405010b090a0603021302030f0403180503100c02011b0503060d032102030118024b0a020d090806010317 73
    0x20568400c406c4c1c1503210036041429a01080c07040c2440390001c60308810101c160b00651500c282250040d2140c040c0044040002c00c2012101d61024050b00c44580140a4140409052200e004500b0781c0000200d440d4801407040000048082005015034040c000e10604140803120380700700d00315041c803001001170314159299201d014081e20f030001d4161058011a0300054128114410060f2180c11080014169401030082c00801e42c110031085401640c9428204104200440c0c1350720300d004258041503042c05100c551100032003654110075111180769000300030940060240d4504204074200c010300140050000442c1c500303000c3c44007035480303029081c0005440043d10304c0ea042c50191006407050f40b43c02200400610740c039030103008041d254108040d810509104480840610b01e80041c104900c088005420881e0001011849c19409180f1848409070840c11080d140e03841644080c005108078061582e00ea0700c2010114151020321020f001c60740d00e580c5031032820802c2c1d01115002090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 384092805 1250 384091555 384091571
    0x803060405091c050d06050904210909020a03021201080303040506040321181a0c070605191803110d02060a0e0c0a0626090c0d03120612021203090607080d 68
    0x4120b0f2400c100495a44642e0307001d028500b0010740e40c2580c000d0b03021341603880912002408190034810603d10038090070451010303902044400c20016031201034424070018014007455490f40041075080307030001904c4041e0342d032590f01030b65910089502034040c1c0c11010101d0002486010300600070840405241c0c11450309510a4007100c802481302989407502101c44420800d0a2510034604030b46104580301d0340c542090305402610600000030104c964a1000806240c043c0003202c030041086001000b1001451440c0c000940c0c15080907801b00340c0100ca00f05400500182810402100d9409007143c2d40750000440003030300c082e20300560340b40108555200140c944e40d4403c3c0042041e40d07504400b16156805604051031508030300640c210880e010041168000901580c017001c060326a4108400c03281000c9420410b5405d40004440c1404000181c0c40480f030410503e1030700880b51802040c010300a980d649201d1402a943c0101c02480403002003000040549901d100d0a138020403841 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 384094055 1250 384092805 384092833
    0xf01120b15060c0109120203030112290c0304020a15120b0d0203010905100e030a08060f010c051009030e030604022b060f020a02010c09080705210f010507080a0504080306040509 78
    0x1401400002510f82e44d070705000c4040c0001d4620002d0040c1b80c0f40051441c550500c09036810007114008080c000c04500d41d0b0010b4202ca0354080f00852880741c0090035014101590f03440e00560081d06d09922031129084003041c03000c070010341c1003418281030300c2d01441500001c00f020003070003c0190855201a200c01208090b0b2028001d001c2420b104001500c04101003d0529040703480800007150a030f03109010303118159401042480d0082000c844a105171002000100d07503088441e00d000f0301c01e010f0b1aa032494060400e820221001d44203413a940c0f24240c004003490740d203a408581c0650b000601e13540c1c002645100a03400003104d451841414140c260640341c22042d103c2c03591390f9410850340010314880c040d6083c4103610014010346041c41c192860085030640c2e510640c06194822204290082520201c00144140c2c072018003041d03039003000c9140301207402440308031801e8002c20b041d2800202110001d06ca041e00c5954440f06143c05e41c0c0b00d250138000140390040103c2414450024004902 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 384095305 1250 384094055 384094057
    0x102010905060a240e0109020c25060e010e1309020d05010e070e0903070c05010806030a02030a0c05011e020304030f030912050705040c17010306020c030f040f0504050f01120b1506 79
    0xa011850f82c0440c0807180741a42c40e90083d0800c1c0c0015a00300c180d0810b1004d16035102809044500c03204015841c0d0109281d082c1c14500454100a2130b6948440a800c40d412029072201c101d681a171284030500c108040192034061400d54460781c0034092051200390141150f21000d00c0364009812500700e45c0a0b80d40300d80c00c485442d010701007280d0115608018442d40c80c0324040d0300c50510400b550401c48a0f070340e070700d8102d882401424103008a502c005446920104016000c1c10740003022034400349841d040c00c078a00200740c0034550000d84000c0c03416101c0848103025500030b08065000b50f1a16255403aa075031b8000450f8001c4080000030071001401403110340303880300000c0c002c0000d00b07800e030710700010413044a03003250104c420b0200c2c00083d00c0038054200340c800d04494020748003503500c030740001d41a410741c814580301141d40a0301080104419040034191402d807203040d2001c10103070300d4400c2039000410003482450014541400d0b00000a545504125040621184c0c10428240010002851 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 384096555 1250 384095305 384095311
    0xe0a110705011b030902030616050f0406080a0507032f040e0a0509010515010e0105130801050c030910020f030406090f060e030702012019030e0904080406030c0207051e010201090506 80
    0x1060f034441c58210b2002200aa0a100c0c110140c1000c00c102c6400c2e50100b40c81d0000104485203580a9102c090206c41c0128211225050213182c450340c0d82d92500000741200c0805c2c0c500a80d29440c1000180d030107400b80c817640100841c0008061120034007510700d01043c0c05d012985400b490700901000918544071800107010f90030001022955142172050700e403c5400080c03108005480d5207401c500303266000700403401c00107400e28040741c3e5025034030340710110300003580c1c002d6200d9840d0400304003402c880340740698041d4401206960758002608040c005a004080840d40b440704100041800101c1c0f507441003886a10903030303150080e00d4094648104680ca07008074103080c1d401c00a030280866a102d82c0700b00d0f200146440c2a00380001d0f6001241c1c4e20b2140300d440d0b040d0a402c0500000034140520003000d044900140401001c0c902072500700342c160003034800c00011a00f44108451034a001241304811303643d01410030902000c103050700d105241d00b050100390541d541c50a641d40410781c20f200d4988 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 384097805 1250 384096555 384096563
    0xe09010207120e030c010c110402210106080106021501080607050903100507091a03010312080402060412050304150f02060402011b05010f05090c060307050a2f06010e010f050a0e0a1107 81
    0x1600c00e01ea4084c5414021002140c4d81004640d048803400201360240c5880548020b80d070060f165810300314400303a14803541c0d00450329903051600025100e40d211124506071103a550030348003404c4007441c0020b6100028000d60340c0315040b180000b01a9071083e4050300801c02c0040c1250781e03005000c0d8458044590540e54140080c2102c2424050038400b03510680c0c0680020000c10f1856240d07880740094610303403111003010410520041415503079180140c5e40508040101402262418a001c079504d07401403050040003461001c200201e503014404042c031108254014000d1a0742c1d070340c01100e5222118500040d40c0b0b9580c0803460100c4d609206000101c4040400000c09080180c0401d25042100086502c2000100108030000390b0010595000000074105280c000c400d0340c510302022159200d03912a02049442080002d00d03000520700e04880c100c0450213034990302c8152200384605a405007507044015a40c08201c24003044100b242d0012503540009901c0aa40c51012815480700360291 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 384099055 1250 384097805 384097817
    0x10091b020c030d08040f061e02040303120605010e0f12030d0203041142030403080406060501031112042d0b07030618090204091407030302011409070e0901020712 71
    0x142480d01001200c1105404038001c0100c0301403000010008034001300000d00c0c3e81600100d2608105007030700184016103d01400b082c11861940720000203411600c01a0700113000440714040300070381d45c40380c0001d50341c06035603504060842c0d03000e00c4503d01d03c2c00c501300d801c00d182e211158802c9509001400807858080d0000d039482c1090300b845d102c2d0b42c001101c00340c80b41011801e1202160140000714910310b0410010707c9140b0301c107005540407070011060500d00310100200f000308055000480782d00c180d106500400205490310011070444d4000c003004440101e0802440100b421701810803036100b032048011005140d00d40d4070000c0e607403240740c98940d000c1030690b40c10403c000429082c694007600b580307020884203180121082d80c6100b501812401a517a9015204c155212604060043c40e04000913200c002c00324540595200603512040d80154070f80f04841d45001c0d004104c01d8020008803000304011410001807012a81014045200546d801c00a0000003100748403140700091007030301c6074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 384100305 1250 384099055 384099101
    0x203060d0b070f1e0215090a0501060f2303060105120c040c05030412110d03020714010908091507051b0a080703061d160b0f040905011404060605030c0d051009 70
    0x15040043d500d40909044d00840411404035500203880c50095440940546194440c401458180750210901411a5092003004240d0031100e0355000102e41004030440480f061050007201c84688546000f40c0c59002540100704500d002c000d000c080c00280c500341c0b03c00e180203100241c11a0425020140491400300801c070900100d8030720100b0100c02c5060140c00510b561320020380751a0b05101d080d050640c0442e0f0a411712600750070643c00004148002c22203000389042805190704000d990511030750103044040c144146203425268032503806401440d00302e00030b160380707090b81d406046219004550f484000a000404020300d40c0203500419001680b445203085c0740300c1d0100310080c0300810b5484080000f1003425a81420000ca0b070711340620311780b280d0080e601005035204d9980b0040c161814a000441c24140706220101041801c0700c003000f010740d0b074480aa0301c0c3c0c00111086900c18406100c680c04511072900720590190544c2241642d003a181d0586000329400f6030441601c0038070007184 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 384101555 1250 384100305 384100307
    0x20d020918150102032529010819050a0b1b0a03020703030b0f012f031b0106290304030504090e0303060103061e14030a020307060224060d060203060d0b070f 69
    0x288000c1c1e02e0030b20140d450001e0403d00820041184840c010fa41070300201082c081c0542540060107a141c10704080d500711050302d1041c0d42c10b100a016240030340c0200d03001d90300030a4461550666884e40100034150600d983d4a44c7c401000c0000c00352550040c2c403840d403c4041d0600740c001c0c401e2804640300162112454180142110851841c0c0c5001c1d04100b81092210b0b03070000d0b400c41c2c0710680340c2100b0002c5154016000c100403012074820751584408201c0811001003c81200704040c2400c00800c019680c81d110760031a620a40901c005030714000c0304402c80e140d002070086a11500a00300303186426901c0d102d400c2294500843c4200c81e800100c24840150782c14018000284443d8000d9100340305a842000380d200654850803d03080c0c000c881400c1701e0386052040041803074005080e40c110302d86da818007039101d5500080d0340b04420140d035030a0002c0d403c0806d48500030400a030080460104035624078000f03600c05809107900c0140102e0040008400c040c0b0f040c450307556560344014640b80100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 384102805 1250 384101555 384101581
    0x415060c14010908030105130f0c090e09120702011d0303031302040f1a1903020901090501030b070206010602030915070204050a020a0909020c0303040b100f0902040510051c020d020918 81
    0x400c01c1d0725034100000702d00402c10300000c2d01e0558004540d151032030340030138156800902005080001c8582048951011941c01c16406412100074074246801c070b90760403440b80d494110100c0c1d00e45041c4004d0040c900507504c60070740121401c03242900c480e1900d9001c0c00091458008032403502107003528000000450415002d040e503052103120b01405081c1507072118070b0708090b00004090044000c6034051000c00f40b2145100021074018201ca200d6503110444a00600702c24042907520008034800b050600b440017400d24100d0b100d9901650500301d0b0002001081100f000c030b8036a01c4001070201c03401582d41c900c603850040041c103600694407008160081c06143e65a804110364900c10301c800c540c20400401102c1e0b22036806410301216913607001e040c0b400d10001d0740102c0d402c81c60358100800c4001c02c3d43d000784140c400460391007402c010300e04011034070751007201a8012090030f5280c80c450401d043c1d401400543d0074059000d824280c4050201d0421445480300d4107940124030184210124518 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 384104055 1250 384102805 384102833
    0x270f07111b010e03010203040c03080906250606050114041503060e10170a0816140a060e070f030210080a18030509041503020d15090206030703090b01060513050603060415060c 77
    0x4c0d00035400d42c42d15450b030320080e06061102030031107080050b0301c8039550740394022141046001d407001040e424083c0310301d0103040c2825004503a511f16290011480358018580c2c09081e0801c49541880c080c1084041032035062000f030740309c007415210305012500c291748588640c410701c1d040303c04034000341c40e20340700701001b903101018441280c115403545c3c40481c58607011038004050231403188012007003600c1d02d2820900d40c50a10622402031507040000c01041c2e811194080c2d98100441d4103060b21081440c2040640b0f200095100200c581c102e81080d025502d4544e008088900001d44208030081c50307030074201c100c0d00480c0000c80005e012074003858140b143d10801c003c902d098540d6541103902242e041c00060902800201d0b40790002d0445044541045003070b01e9000c4e00326602c81c1406030015001c1c104a00b4111411450b0314008140c092044040d07441e030780703a03611075204681c4c81c2500313020091740081c00481d00507880b18488800c1e024501e0840008007101d40d07550681071034500300044014125 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 384105305 1250 384104055 384104059
    0x7050c0c0405011d070e01142826061e01020c1003020c0115060e0d05190c03050105061219030e0307060503010806010902070b01050405250806270f07111b010e 70
    0x7420035610315980c0107240b095410b40040e84695035901445a50036440200d04402004d074004007070700c04a09c1e81c041260310300c60709040c0c4c1c0e803008409007002020551000711030564000d013640f181b0340b1810741c0200b0002500b002c10700540d030170010120049582560510300e41d40c0800d800141c071f21101c09092042d886850250708403039001d6400c1c03001c0200401408a5881d1140c41e44003d15018008107002004445240c0c0800143c0c90302149000000d0040502c8156540e520b05400039150b420036140420041e200c0c04060022003c20703d5900742d01c1d04d0700c01c0c0180c041013102c410042040d1400c000c000301800f41900d0b00c0b80c4961400c064039150200581090149a0041c0011400141034100e00d40c1907920461b4085115602ca4400d481d1041e90181c5080c481c505900c0049407181d0403c602601071202079032254207840000c0c00b1104180209515110800000d80008040840318004250071104074030303205094000c2485900d140030412080b036294501c2000090420b9a000103031943c0c99202 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 384106555 1250 384105305 384105317
    0x5010b1c06211a1617060a0b0307020a0204110301030501050112080f1c090f171216020307150515010914010f0302040b0a0c151407050c0c0405011d07 66
    0x10082d01c2c00e50301c000421208852016100c0100c1008410182d01c003103485040d81c031018a290650f0290f00c4048103119200104180c0e40030003030070036002c4490340c1c800c0f035001d0801e4082070720b40361540b451648001c007500c003180a40040c400060344d41303006000701c40701c2440d4155220350440c24801c0c21150103a00224010000c41c000000050100d0700746c5414441d803d15058031801c0c6000307401d2442000c81c07481250289084500300422425244200000d80201900300c1c06a2005002d150705110740e038105c001c145411030010b40102c0c5100c0707000c503001e03076a0303c185c0e81090100c0d035075060105085415a560a91a541003190314a003d0340d0544d501034091034449452031030300410030000d4a4010450f41000602c015941c1903e000c2c0d0100d40041171030a000a658221040c0700030882c83c070404045035500b1080c0160702810360ba50280c94107a0342a840762900b00d48441100340c41036408100228180c1c0644601d0682550303c80c0300795070081c01101141183d4940b000111568403800400079000d02075 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 384107805 1250 384106555 384106559
    0x606120b06041b081f0512100c1803060b0303090a0b0a02010507030c090923090d120924180c080d09030c140303130801060f060f0c200405010b1c06 65
    0x640304d0710181c1c01188800840c03c0101307000c04103950000b069044280c01c10080860444034002c0041d00050741060440104044851484100c400207503c0c4030071254580100320600c00b080ca1640070340c15103240141240e14044032540842c84503082a8880f4209250124540382c42c41c0d0280103407903006140385010802c4007401c80002d8a203065900400d00b005644070103c0100340001c0b005501008208811801a0725020031155510300980c07500d5000190742c0d00010b05210308a011b4000030380c1d03005d4848004075a508483c058212040c03995248020345074143c0081c0b00314680e404100306070140e082001900d0400683c246070241d03280707074141040080d0004001241c880c50450302503c040340095410f184056000a1a40c0291448051390308403428000499042c158840d4084070003203100704038001d6039100140c3e0002c810040c4071010a00c0000550000390618040b0a450724850b110030301c0409404002c42d0071920243c01c280030141002598058a1208000a03d0f061100203010b000c6c043c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 384109055 1250 384107805 384107807
    0x403180602010510030b070309020904050309012006160c0c06080609130c0e0c0f180906190902031810050a05150102070308030c19050a23160606120b06041b 69
    0x614a05c0302500c40c40090000c140d646100ba04030040e100c3c0c00500390741083c100382c10700743d44aa0041d0038042c0850501310541140160001941282c0d0030804098070981e034624080386035050501070745070304202441c1c4102000840d44440d036005001a90344004407864840d090018a60300031f8802c2848044240c410f40015202c41c91400a40d01130b4402c0b4400d0351030701d491b00c154500410340e8464500c80007007100900070300a1088400050b6040b04d5030f41d80da03100c00060140700354030940426580c603120f46007441240c0c0c13241c0046030030085079002048600090031245007003114000b007540360a0b40740c000303100140b00136000d015000192026044078800e600400030791740d802c5500c802031441310003100180e041c41f15a002d49150454424a0340c20038680a40c00516941c405240302001c01c22040d2a041480701c5504c490700100500b03104d20b031914a102d080f28203000200d0f101126901e854641c085940b0344110310310303e1030074403916841c81142000300c02c001c00c1d14404840c0c001404030101008880da = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 384110305 1250 384109055 384109081
    0xf12010e091b011202040b180108040b042009090609071707051e04051008011802010f230d1e020306030a031805030303070c12020f100f0204090504031806020105 71
    0x14035400c1c0716903090942e4016145102c88881640c2c1c264800300d0005039401c01c1c6001400d2400882d00d210b011380b4405001921980001d0f5000703418862558000fa0001d088140d0303c1000786400c1041050b005180b00008042c101c045402158640080302880305941c002c2018001809200403806e10302c8442c6a400c540e100c440380310f158820085490403041100840c0d1014501c070300045d10610407071622482002d00c2e02107600c1110040c0d0310b80056020032902004c803040125605035205a0500720b0782500702c0da8000070001548074030f1400302090240b03081040003010036805151021600e840c8a906c4007141100700485500302c43e00410800c2aa0394002c56044502035250800404800d042074070b4060300a860381240760181300003c03c3c0310b6010740108800c041c040c841c0c03c0d118070701020890100d8a4181400c0a00b1450380500345484004d1660f800c080b081c5448241c0c010304040d5510300c00c0c01a2503040d90280c0101d4017440c00c1c810902040180040900700c180020b00c07850516a200c8260303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 384111555 1250 384110305 384110323
    0x180403050d0c051c02070203070605120a1d06040506061504140111190602041a0c0d08060414011517010e011221031b09030302100903090302060f12010e09 68
    0x4216601c0c02003010340c0380142c0a4684c2000c0c0281940000580c41c05010001c0d800004182d11a104030100001c2c40f62180f0211240307400342c220110030303903101c81c03041d000600082d198070018803803130760761080e049a000c010b5248254000c1c0002c1c900d0382031920038400210040420b50100903c200000c2c03002c40b80c3c08105803007854080c6000c4a440d5605120b90381410410386156911000102d400320610172940c0282c4195881509402d0b94074015003001e00d4688110083e554040d00200c185201c103d004103100d0307074050406040410103d48071075404066181c02d03000343d030300303c0342c8030f514041c40552003400300c0032031110143e948265504105400c2c0402c50144070340000b41d030040b184002002007000d42c0351003020020203500c2c0b5240e52114090041c140e4860711038035081e41c600b8086162441581f849045136011f401a0814914200401018201d452016024414000000801615040000d00744400b40340001c5440300203060400c100682d0680c4080140d18011090180c0e409001c510202 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 384112805 1250 384111555 384111577
    0x27061204022e080f0705090f041a0d050708010b040c02150615041215020a14031e0708090106090506100f110303010807050405010e070c1e0204020d060518040305 71
    0x124035040802c680000500e081503440300c0c514801c0340742d02c1054005800600800055413004400d9988607011035160103841e03a000d510000000c21112a41410f920103043c0034001d451039403030246103001080240b03000c4c1320203d403251720078142040301c0c0c40c0c2849842c0958500300c6050103203200f0140003e50b45c0440107401c8040c00c403e074010500c2c541d0340a03c098511702e0a0084903448682d0740c501040800411101514100b03481111a220200540b0803120072800030340b00e00505840b00c4e10b190800b504000e085201d0b4402d468000c294001006948074031550041e44c8500861030605242c41c00d4030385550000c0f51240c2440309120300e982d10404035002280ea03d25004071004000742085517034000d4200c10552034000000082607001010400b40b00381e400c10f403000d001c0750340d036261080c0900308121110300009004017404400144030003140070f000d10500c812891216131a40000c3c0483e8400034220340607540d80c2c10100181d044c08103140100841e4451158280d1030070351406070044c450500300305 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 384114055 1250 384112805 384112819
    0x1a0903061005061c1404061407030e12160633030512160c06261504020a11190b01050d020907080907170115081c0f03060b2706120402 59
    0x4484403095505c41d40b0b800c51083c440340c401d420507080c854014540c400e020494000312500007007100e4040d004014a507041c1078001c09203510010040851604070002002e1103da5508100022401c14080c0e010950102c43c03011107803146600828010300d2030900081001a170055041002c10404074190f0040f601d00c2d00f0842e507550b60001080301c0820969801010702c082801d02003441035110b01c0781860300c000741500035054400d144030030840001c00c6980c010000b5010011010a007010740152174508130a0400c10310b02801030034128200f5140c03559003624250042e80754014018900142801840e0030740f140d260391082074012178072010004101d0401e120754040466281e04040000e1401000b150307400d19402108406014044d2049480c081c3c105054514007160520380800c28446c030011040c03070400107000000c0c040c1c80c1c2ca004c5021400605589140018170180c48500814104941c00303c65440d00c41010f18204420b0070140901e03018030410b1008600c0310103200311840d04950119804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 384115305 1250 384114055 384114097
    0x31a04080c0a11011202070c03080d110a020109030210021218030c010e010902030105100b041205010219020307060c1404090f0204031a040c1202100e01091a090306100506 75
    0xa14607205032940341c1001e124464000d002d00941c0c2d400700361031000903a1008441c1c03a941ca148001da024070b11007c0c1100d4030325803040000400d07600081c01010501e0304c0100320790b800c0798150031442c0c2203507106102503515140c8810405030b05000402200800e130300304509200700742e050a01202d0004002410900030700d108600403c1c400c00c00d03201109400b40003800340c1e40c00c12102c940a0004030740e00301d000c4e41c240390101e03041211103044041a140c1110205042c41e20304050307c9a450020700302903405550030056100d02d0543c440500704080f103a50002c59584c4003920385081218950018401004941c60b1030b2528030070301000702d504903904000301007102686001c0440091086910080004099441d000e0507000012a1140b00710b010320209210f041da1140150f482c81521440250b12007110400800042c1c000d000072039007900107152440f603ea03250200341c0c2040c1c201c00d91100d0360381c1c8041501745803864100049980404200c561520a074034210208069010700a0000b00100022482c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 384116555 1250 384115305 384115313
    0x140601032f060c0115140d0b13050604030c1b21030228020a0b030c0a031a0a0305071802071e030507150203010e01090c020c15040905090d0315031a04 66
    0x1d841480000144003940e51080039a4260003030010341c10070507041e0f10b060300c001001400b072210b41d04103940c0600821840e01140c1e5580c6200000140a405920071042c8210b0124000b00041c5108074402e44905100c0c0c846400d146082c0ba2448400000085042e8001e0000310b440c015540d090f08001080450358800ca03103416410505421482500e0200b00036208400c940f00c1d21540203180c2c025159504420703141c92944600e80300859052800b9401000f1003110940329500c1008031409085c0041c21801449002076002003080d030007a1001d5000d46405c3c007103440220301554000c00418421032401c101d50741d40e00d01c0701c19403125128440800d09855410305005100b16659142e008219103019807281d00c00381c0081d0800c1c01040c01c0002040700100c1d2400f0103204a414107440f640061103050000e100b0040d500b003038001d020030458003c1c0800a012032a034001c541c010304664000e00701d0041400401021200c1c0c2084000303100c4d140580410110741300c060958200900c481c1080d09542d11810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 384117805 1250 384116555 384116633
    0xa0f1506030602030a1a0901060c1509020303030a050a18050c0d0302070b03090318010e220b060a080105030c03030406050d0e1c0c2f1323010314060103 67
    0x20010340103c2c00002000540381042c1c0c0450000300034500c021010800c07090034032825031824040c010104169491020100b42240045105050480320200b040030196000c2425070b002a41c21044098603041070114041e580c0c001e4807050074045e40c038084c40e40e00340d4441550b01c0700403100b8240202e4100d00704100340340c400e2041c0b86c06040d0305004255a1b0420310304165803607101c85404003100d0b8044802484543c818242826204401004024410300142001d00b1005200c80c400950320f90b507411004050700c4a00242240c0f0000303031115030480d0315240506003030000003c3c0092007038104201c00d01c00b40da000000e45015003c030318000698205614056490b01560b04401e02528600101040c0d00076404001c110580380f140d10510403511102415900c55000700e0400500c47c51601d448c82c032641032a10880c450400460f002149441c08058901d4000b9040300250640400746001030041c00888006041d9040009008009039031440c2c40c4c3d518107002d102d41e0b50580000d0000d4450358800c0400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 384119055 1250 384117805 384117809
    0x112050c12070915020c0d1e0203010507031e02160311010e16031209030c0627090c0215060f1e0406091a040b06070605060d06050103051b030a0f1506 66
    0xa0003031580342c18542c102800c0d1000c00d10a5010307000c1c0e000c00f03000035144003203002d500c80701e0080c2401203c001e5982ea0203d150f02c0000001100c1c030301181c00c40025980c2400754074054403454400264003903912803107100801212420801681c010070109840b0440e80c500460807c0e0145020f03256840340f0111070b40034000e03481040e90a40310701071040d80c2d0704212038148400c84c0d1041131112140b01c0240004c2d10141250320020f00910b180c51801c2005901034003501862481c4200e80458503400040700c0d00c03d04005800041100f60707070744403070518141c0402c4040e01182032101c0c445801c0ca0b0a0380003a2103160840b03010350144a00511640881f80c031140da080c00168010028001c60351901d440c0001081c01010003e08103d030403070825580c1c14944582040c11101514141c50071410b9110304d40501006001036400c1101c20a1040100d01030703210f5203010794418400351104101c0d80c0000141904454140740c8260081014a000102305d0880340454980c00401409601d2600786507000405240d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 384120305 1250 384119055 384119077
    0x30a080c030409050115080702010c02250f091d06131203021224010c050a06020901050c07030f020109090b060d1a0d0c0e0108030705030307050f070f0605040201090506090112050c 79
    0x1190011880301080e110804100034a035469071001d48d0740c48000c07400c0c0c0306500711281c05a0014107400007841c03060036110302c1d007000c01c82c044040c0079a1030b420a1310007480d0350711034140b440d5610003034410701100c40350780030507031084030000c1040e800d040c018010301450b00031700100310060758000c3c01c8555001c0e4050350081d90000c0781603a01490050034843c61400c0720b41889144a01c013408269256006504202485400c90300a0010202941d0354000943c85250414188101031103034060b9101c04000c10000341d4894006030429020900c000747c0010b9064000c41c0c030243c206400c00750395031a00d200760f401c00120ba074070100f6018480101640415866150590000001400c400038000c0c0c02ea113400882d01c02605c461001e81c4c0e03c0503444c1c0c076401240341c014060f40080002c540c40b244030740c010f07090b06a03441e03040500d403011a581d900651100c544080303c000c0d481c2c6c03040200355038000c01e6200040606a8a651402c40010300003456401884091034030541d03035001140c0181d1500c010745070043c04c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 384121555 1250 384120305 384120311
    0xc010906020313050c010305011404050a06080604141207030c0b06010e04050127020c0c0907090803030a0b040506040b01081f090207050325030e06030a200a1d030a080c030409 77
    0x103c2c0c07402c00c440b924a500305660303e01c59a04130041e203510912906048422400b0302d200c40da400f031003c01003e060080c2c15a103049817507100c0412f082c80140300036030083e88280000040701858004282c00d151192140b440c4640d000c0c0a403801180e00001120740d51035101e004025113565020040e1071208a0100940d00300e071824001080c4400441e142003100841000300b9240c121400305c01c401a44540045c000060300f00b102c50070564100800140d8001c101400c14008551300c9001c50f40ca550402c0320760000c001e8030b9009500c00c5080600c14071b5040344081d44d051218071300d00c0c4000382803c0405400c00d100b5482e90002c00421001c40344e150005030031101e01c10356560342e03c0d043c0a9901e8100c424100d040012480d4000d888100d0329031071010740f987c5601d9100c009040003040164681004050004031620703006900380e20044410901021580d000140391502880c2c030004002280c81c4039000b0000b408504000741e9a81d00180c40399031554008401c0752344040c520441401c60045506c52180319007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 384122805 1250 384121555 384121561
    0x40c0e041407060e03250e0601121515110d0525050d091e0501080403110d020610050d030e0d020105070c0308071a01030803040b04060b150423060a03020c0109060203 73
    0x7a10080c01103844d40103c044038480c0c01e40303210b800f084454259039444401e02402c420401460300e03040d1982d100324141030094610580c0c000e4002520402024024000a14142440f0300c025400e5000410141460134038500c01d94031000b50b56032840c0410140070700c9030128144052035500305203040c03400c2c00001c50401500c46880d01030303910f003404400c40c4046640c8020210703a4003081c5141c8080400201e580762034403071420b0b0056500c2075014005170104142d42006c0e01e841c400401c40c01040e03410030703402002c262501d10712000c01c0201d02d0b0041c3d886504600429000710391322640c0c0d4018040119603800e9462450b2005807010f10540d14002d005641d041c2d000018483c4031000341401c24050902c01c2c20a042240e155600703060240030042c000c078028000b08012a03003c402d100d42c070600c15800001c002d0001c81c001030207654805231030307021004c001506210304d150b0700c8402c60400d440c58290005d070340e08280008100c0e000e009038030010558045949030900c0025000b0f40c99041e04404115600e007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 384124055 1250 384122805 384122807
    0x20303010e090a0f06091a15150f04091d0f0607030606020c010c12090803031501020f0102130513060f06110c010923030109080307080702070608040c0e04140706 71
    0x900240704201c0c5030048400041e0310b0b410003048098490764803181507242100c0366a140401405410026201340c01040e02201e0300600803900b0502880c505002180f8070103a0408201007503900c03100811804a00380500c6a000907081d090703800740d0300c51220200d10001d902c8142034941500e103900c400e49100700424800c41450107e000c0340a05100d9805000e501d40318070051341e464004000003400a400d880580000c510380010f400000c462900d84221076603500c1e80b419107190010740380f4082911551000107942d680402c003582803120300310000d41c02c00002100d0302171003160b00d11585000e2038910081040800f6a64004000f80050b042600407540d1901c0c0020421980c2609520031032280903103600c5250b0142a403c0b040310480d46081d09030b1040ac401c100000d41e2003403506a095034954030b418001039820700185114015507503400e0031300d00d000d540007031400d240e035401842406030060500001c260809a003a01740d9004203411080740c1c5036441d0005ca43d41902c09000700314001c00b03001007072007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 384125305 1250 384124055 384124057
    0x91005070506090d0f03050c1c050114011403071110020a02010b0f06130519090912080f0c030103020607320115270b03030304030c060c0f0f032a0203 66
    0x3240c0200200d035055980d91406aa0f60010050400041503144110050242c420b401099000c1c110304001802c10111501840e80d80b0b03941da401003100c41d00c031030041c03004032000c0d54600f261039001d10300103034040c0c01418502d80300e104c007a01d05401c00112400205400c1d60421088205204c8054210f41d11805400024020051403c02d580300700e0803825000310910f02002a1400b81e59a82a001310162601c81001544a407078501d00c2110030040c20001500c48492060714840c50140c841090311500d10003004107038544c010800d40d0ba081c112014428140d44040942e8150395051707a005680b116103041440c0a0409a40100c14000700300e8541d00700c00d22000402c06081214000078440745290200c0c24003080003900810400300d046243c1c14014180d41d4112080c00810358800248040e03010000c241180e20490707098003c60706100384281045041e21070b400521034079181014202c1584a4000c00c07980010603040109611500f4189c03600410100c18180e10030310111001900701350702c10103500c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 384126555 1250 384125305 384125317
    0xb0405070e0105060a0f181208180406120f0204110d29011d040f020a020a110411180a0503030a18150509010503090f0d17150105041202030102091005 66
    0x4281108000280e9041c40004d03245c00c10b11940b10000100d0b00340c103044804a002184401c4c2041c2982c00000d003140d441e642c0548194080e540030b17a541c0b9504286200f4001899400700d02480c600310b0100800441d00060400d00c6502028483c5d151415000060241107034146401e05041d0003c2c0013981e003865035120b0607e00541c0b4502c80844505031030035204840024400d070303001c90116004602240b0140220310aa454000c1c0001282c0400041c0d64089030020003021001d0380c04907011001b07020310321180c0c0042040071102803102c0021700900d10701c80c1c015054904010312032151018202c0d6605284070010307000c0501180d03229065a4801004042c50030011b0011004081c00815085012b00c03425900301620345403e40703003220a000443d09540000c007194550700902ca403846500c44103000b842d1520f800c0740e032000c0103851060705200001c800a468442c1151000d40d42c1c10060740c108082c1c404450f00480143e900c201fa5001090181c4949100d01da840203001c02c1c030340d0b6500d030801d0203800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 384127805 1250 384126555 384126569
    0x90203090d03050f0a0c031d06011d071b020409020d05010f06050a080316031e120e0610170102070b18190b040b040606030506090a05060a0209130b0d0b040507 70
    0x1d100141034026011110151101030000c2e0490000400c42c9072250040c16550b03c40b8580060604600c104150006c1c0001c4640006908200b0041214030408010380c0c02c1d440300810101034500b441c0d200074103002d50364503500d1103030410302d100d9606541c0c071a88024042c43d0046e088550020f002d1030814020180b6035006000c040c90080d020905083c24500e000175204100002c514166512032890841c6020180440820040c00700c07130b010207001d28000403041009030700c5101100500e5219003040c2c803402420b14565510030b00400c24914440c0c40c1100443d40d202102c0c16085549095a501a10411201030003071040f00003070109000131103010f82c0c0410701721001c0e07d0300303013510000000c101a00da4070080d14116403540031030003180b8442ea806801c00d05c10301c1d00084030380d03803561881c0c14544100c1d10003490360000c50390b40080c80313400e120256102090900441ca0619040005001f2a07400c4180d42c4215507130396206034281c2c0303941d2410f00d012500841000c0b058905860080d640390315a0107066 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 384129055 1250 384127805 384127813
    0x105150322062c1b040207260d0c0f021c020102040f120c0527130609050f010506040e0706081807180f0c0512041109090a030e03070b0403200301020409020309 70
    0x2040b00349010407805402e07408007214150711440c510030817000e5004008252000c1d00ca19a900020b2040242e6100c5811920308c81705454540300300002c1c04443d0344c0c04a800a00004244040c0615070110307940c2540c548142e1030654101020604038024001c0f5007004858280d1100085000484000c0a00042d480790b4010040f140c0c45001340701e2202404e680303c028072009a41c01074584110712140c1a8070184070744c1c01e401a510180ca60006484400c0400d98035138024035040031602d8000e00505038032144c1520103002e120300d082003040c0c0d103010070f100f140c0802214001141c2c0102a4402402103a44d0340e10032680015121440e0180a00c020401e2588003443c218201c4080c85d40782c09a0a11a02c2030348644d802d021141c0415000315034020412035000081e554240800c0d41d6445c1250b001c2d15000b4001e042000031403801134142e0540b111141e02c6540700a604000c1c40b0014000c403410303a54810303e541300000c220444a06c500c00c1070642583d26500100300032600820b140d0143d4400c010360001c031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 384130305 1250 384129055 384129131
    0x100f030902090703062c070807020f0316030e0d02030322090914062a0d23090708190201030e0f03031e0a02070327050409050102040905010515032206 66
    0x242c01b446150070b040c4d0316103190b4000200854040d07010301e0303070200b51401138440d15001c2c1c03511035003190f004084404c00304d4902c880f102c007495445006d512842c1e20a8500040f03280490f0000b0350749014200ea07421544a40c41c8540c80d0038840e00b0700140040024010030721100b2880e02d49049640200b01200c078171803142c58001600104011403410404116442558012001c850480c11540c0418001140c86403507840c6040e40d0300d10300354070204c0584610700706e000c1c40c101541d01b103040010a03400b201b03d95210350b03010300740e5285507400018400d9090a0004c0c0c64940f042020b406c001089034101c03441d000100410640d92005000501d001d071000a001c04140e0710760462008a0040400150000e1601013500c000046000c01f540300d100305a1440f0040141c0d01d40c00902030324131141007154541d40200e02004103070f925000300303409030800b11107425034a11681c41c140d903d8003008004180e42c1c489500c0d280d00a900018010300740c6a040b10b4180320360141041c2c8410302c0c04010100001e612030040303003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 384131555 1250 384130305 384130349
    0x10b07030314071d0a03081201080f01021c0e070807081501060807050d0c020c121636020403080a050c0c011407030e0f06160c09020405100f03090209070306 69
    0x100c1d40c402d034420380301c0c101d031a951910138010f030080e0310b04015005100618040003154a0001038018071022568090345503050003920742c103004041e02100c015a0060005c41031007100311044140d9090303002400a403400002c68198075140c1c980d0300176240b078020300c5404500a0340101d4142d410301103200c002c031403a90703070b0380402c0758403450844100c00001c8082c461000c0a00d03072904001c2c0000c4140c412140c400006a00040d1460308040074624281d01124500c2c06640750f4000c2c0e01c009107101e070032200f10310606a41c2c2c0b80050b900c0702c032110343d1690086030086018040d43d054402868210030040d40f99240d928000e402e070b620903014480244696804c0b2080c641c42498080c020041820469007004180c2d40c054512042080c50140c0c4002184004000c070384034440a400086a00c4070690a5159542018650060650444000240104010700090302c64120724010b00625140c0380c500705c44010380c114020105d1440080d840316010041c0b142940c2c0c1a00480252100001102460f9400d40f030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 384132805 1250 384131555 384131591
    0x207150e0a0b1b07030305040c030b0903070312020306060301050d0c1e091a130c090305061303110c0a0b030c120c0903281704170325020a03080a030902030303010b070303 75
    0x580f64401c0300104038210010303110381c1085400c01c1c482c904900781681c8950390000004002c0f50204104d038000b06000c424117a000e18040c0e80c02c46502d904514504004020500c01d11050291600a54542d125a800c001c0c90030070304801844409007141030b030081d000b00e040ca146400e04c14100d180342001400b89022405901100d92054020700c10050000c82c44050701c058840c80b40030205004600038000003003041403060714030a90400c02506642c0d072041c41c0203441c2c080090f0804081d64807058440300e840e1200300050302524110906c0700e4607551146040151f0b4480e080e88200c980808605000c119070a542c00740290b28003c8055401c01440c0c0002d2940c082210468403046030540d920160118141c024040d0402100d210380078605511032020285c008070880c211003040d400003a1648000b031005401420440700100102025899500000e204000a000c0504900800141d032400720303020342c0c043b0184603409030a0b25141d6035103d003006880d41080c407058012034141107400083c82c25440d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 384134055 1250 384132805 384132841
    0x3030711010b090406050a090b09010b0102060f10030b040c0506070302010b04110a0c020603090a0813060e0906010203070b0703060518040605061818011104090b03070906060e040207150e0a0b 84
    0x1800c01c207400e954031307202c61000c0c0c00013502646e580341d9200541404618200032703442c03180c99004004a1801c10038400289814801060180d8400c504000d004c0c3c520843d0442508880d000041140d4075211410f04070039040c81c56005035402003000800004050b010f4200a04900b0100c0b01000741148401460080740316000b21040011070820b0500d0051801c200603507009402082200c103d07034a9591a0b803001da109880304040d100c0401030400c0010392143e0908080c540903038a00b4854140310b40007035034070301800c64002c0404500c40d0003c1c407014803070b900020013002c000b0b06010320704010703c1780071917508801e0300e0a030381d42805c050000d60181800d40e0b041d141000307042c00760116696821016001a0078400d5942c405548a010340202000ca40d400b1300f0183c200c0305d400083c5203102004040c900a000e50103800860700306001003040c96008001540c81d42c030141c03030150b83e0fa041442c0a0346552001c1309640c0119243c400c0441c001100003440f44085445071030b950080e40c6601d040d12004013568 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 384135305 1250 384134055 384134059
    0xe1b04060207211a0405010b010207030f0206090d020603071808030a051608040306050c040608070c050d0f020c15120c040803032e060f02010f050411090c04030605070203030711010b 80
    0x100d40401c140403c00004a0106065500c5100384112584d5400650315141a40c82e03900701800c1c0034882841000e100d41e00c281c032400d000401d140e900c1e6540340381000743c19440191182c440410b00c04016100c56208001441d40144165500e24200703401a103803201c0c010910451a40c2c000010504140c00001c0303400300351698603243d013002a02480c8012400c00940300300e481e50b038203000000000700c4034000c01d07000307103042180951030ba414004000c0000b007000b4254420011600500008191301190928001c0b83d5460007400c1e01440301c0082c0e190550f42040705422100031600c88044441c0500940300c1140c1031402c1c0f40300780e21041c4502c94140660302130728880790070400124460a20441c1c04644064101807150408281441700340722205c4603038008408940d21a040416aa60a215110044040c0300382003201e403d080c1c0394000c0d500d846130031250007504018045100b101842c82079070000c6a0249050001f0314000030002e407a0f8100391074010200d42010f904518400e0180900749400f100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 384136555 1250 384135305 384135313
    0x31005030a0b0a11160809090703090b040b2805040203010b01050301030b280e160b0f070206090402160c060207060f17182e0203221104060e1b040602 66
    0x1400800000900b0000c9a0842c0c0d21010010064020300b84a194645903001b0743d01c1d40e40342d0b0f14400038801c0c6020014142d03010140b91804241c005103880b40c69a40090300950403030845c2c0d450005c0c0301551016501d400114407141c030389242161400b40c001c1031040b4820b400034800c01c00e5030340064039180020700000700003000640020781c0d1007588840b0581d26140301992400014843c0c03d110046801207401810365400500c11a940345190440b0140101107008040d40f5200c0c00005401d460b006402d030003842500c002402000d181d40710340684075950300c078080c6040345a2880c0340c144080416032040c54094001c00c840080c00314003ca288200d00701c41511100142001c46d54a003860b020000c1c503100d00f03000b001c6203c5804050811440400031001c41d00e00c120003500b5043c8c0506044004440f17106d050041041229400c3c1c80a00f5000d000c42700c09a030054134a503031901d0312000815590440e04180b40540018a04142c010b4090080441050b0107201002c01481000c46109a02642000d0f83c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 384137805 1250 384136555 384136561
    0x90203100e0f24120102190e03071815080703060e030316030b030a080432010e060f090607031d190605130b0c0706090605070f030e030f06010b031005030a0b 69
    0x2641900c80c15078040d8001c0000703852035400008600c040003020904d4103030341c045134405104016401410130081c25080180c100c1c822040041d03070303c1c2c5441c001c0d00710302c990f20400c2200c078603025000800c0c1d00320000da00846140d1a0910190f9842407840152400f904041c0c0d454040040481120300400d00c42c40d0344c1005580c40f0074107801420080700400d40501ca2070f104c080124698401401c050100c51686c0c900c030103a048100030103207010340c1d20320982007016200d140c1c03da03070440805451000241e60b81512005034580c02802d50141c18126038125900050308020158091009280c80401044208094210b0801d0000781c1c800c40460315100c40d02d401c82400311a0240001d060103c007200c40316400a51241110441030300040554203459004483c240041d6030842d0106003e4040740c648603007000002d03140c1d1103442c000100040c041c094a91407c105944003170003a6611142c660381182c009594541020300309031700880782d0400f843c4488001050f07515001c2031380c1c05c02c1900f0950000850f2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 384139055 1250 384137805 384137821
    0x7030512040f0b0903030709060527190909061a180612012a02030a051207110f06040201090803090f06220806010302090a1b0c0c0b04090203100e0f 65
    0x65000303881a580030301d1502a070b4000514885540e845011088041c5440741050940030f010718645801000c240202030044107a801e24008058400800150012400c1c0c000c100118000c4055018144a440c80500001c108101241c000e10042803003103a04001c0c8004580d0549052200f404240c1e92010203400c0740c49207a0780e580710043e04807070700411074401d4540389c0030420300b116100d1800084004800d43c04681d100c14080c00b043ca80286400510303d07111090100810920514940c19a603030f0b621000725030340724031612007401c45840c410101c58510516106560359010b04982c01c0707002803030b4204d02003000302c00441030b501d0125000d4946051000d00d00c041000540203d00c6003294108401111001480c0745d6041500030031140b409040b240d4190b0060141c030f034900802c0340c01c410f810020148490206c403002c88001991754580042c0001aa24100854101c0c55005850303c1e8008240814031641ca540294080d030076148400c02129500d081c4110310000490703c0004070740a02c03001078015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 384140305 1250 384139055 384139087
    0x1c06050403031e0e0f01050c0403030c0302100f020c010f0c020c041e050c04031106030708010303230c0708010f0606140c190b09060702011506030f020d050103050a17070305 76
    0x30301c01d080100d5000409407070444022800d4510691040c1c5440050104100902402d2610b07900c040003840035140c140c1c402c1f00e071403050303100003020804121080e00503d44244400f2001744031f03110042c010804001c41450281d048402300600c29481c00c03858050304a0b09204011402105402800f52050007904100041c8040c2c0050014203810907442c005143c40d61084d00c0c4108014500c02d9204d03825402c00c0256001c4600c5c03032500a00003042800509a0054a0b107170442c2d60601d404440400071441c0c14001c24402c03441080580b0f000714007203170510400b2424000340c404460007008541c07030001222080c1d814900c51480494141a41c44950140c60b00040c210021081d088400091405184440c494042c0c40c064a0f00c82c0707070b0000d002140304c040c001c460701300c80544020b00c61946c0042844420443d01e2013003400b03041d903a10540743d0302c1c10035806550a2001c140782c204510369407810000d480d0f00d00c1d40340031100310700030300340110b40c0103100c0781907400e090741543c1ca8a08180800076420b1072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 384141555 1250 384140305 384140311
    0x15081c050c030c0706080c030103020906120f0f07080c03060115030506030a1509290109050a0b0319051212040f0201032d06052b02010908101a1c0605 66
    0x10024100030034200c400040008100303103c074981c0241151450220000d054402c094500c854402c070404c010400f40c3e95502a550300300d4401c546410007050403903180d40c508501154901c080d40103190b18400c07548030215915049501140c00d54801d94148001c05896503424060100c000710101d004011841c426807015030b00030000f8045442c1102642c6405441c04440b512400c100341c1c071041c12204200d441090b041c1041d041c0b4110700c80140348884080e0090f201405154889a9a400000c80d148015080000c400f000502a91507488000c100540c0b500540e03e0151110b100c1e5032075038000d40d0110800c9440c0d060b013000340d1607140d4540366582400b5480e00c980036410151150b101044000000b042c90400d03480f5214845140300e0f40e020f01c90255035165002d9446003610a040c0d400c1c590041000c2c011180c00c031112018911181d10040e0780c1080d9540202c030061061a840008031949a0302c558484e20080500d9030411620704104010030138070250510b2540c03200e4440b10001001c0750032240d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 384142805 1250 384141555 384141557
    0x10e04080405120304091515140f070506011d0106020604030804030306150e0414190f11030c18031b010f23300402060307030f020d060915081c 63
    0x11078990303181c00003030055150114014640d0070000b000c000302515440b80404050180e140102c0075403800300d2114945d0716080d2910240114105038a400d41440c1040b1000d00102403185515840d29003402541d0b50424064100c00c0d0f268011141902051044028105c0d01e4641c002c24083c0c1d180d95040390740543c044c00032401c0c9611650045031000c2d0100154448a4650761400c5c11200b0b20804c000940d600c1d50074403140040c2d0f11060003054a00406e541420621101020a980400003800001407002d441e62441d44500402480a0301e0914001003219044200024607012a54020540c4079002306001c06228441410300744103a50088a01ea40e100200c0d06044100d1001650b80142703060002c0100c1c03940c207000249408400c113407869155280400640200940f0003011a07403522920050406440b8440100000319034903c260004901810700c40e90554480340510000000340600380560060182012516000308600415440c00c581c3c200f0020540d030842005c410310007550f80d4032580 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 384144055 1250 384142805 384142807
    0xa02010510030827040f0c1b0b1302030f0607050406110d05070303090f0f0b0603010f05010b0a030b030709060f1401030905060606090315010b07050607051306030f1d0708060a090209010e0408 84
    0x13030f03c0d80e4030300c10010f040c80d00020202d1880d200e044001c20381450301318000e500c03001c0b5661020100340b0390442540e010200030f2003000c1c2c408150001901e0012170213040b603d2881003004101c80c065008001d0011501c03d900c44c6510200c02c1441e40f81c50340390320b91030100061828001c420200c5d220382c1103843c00d60300030440028000303120740b1404181ca580c1502a10681184818046070382001d124066410300205410001c030f50520300034410341d20440111400300368440c084600995401e201d4000200b0000404000d0303580d5680104456252500c5517a0b00c540c0f203a040940d00394064041c07207075100d900001030b20540d600d000412117113070482d1810b41d400d0320540d14039541e081f0107a42028060b00900d41d4003a02c0380311514007545480030081680c0100030050110b0070080d10700020b0041680c2c2d182c240404c450020386051801400c070307507181c00104086040388080c0c0007400714807001075540d02c2003a180e55581e050030b00d1080d150031480c0207402001c003000401c52298003140b0309810510440400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 384145305 1250 384144055 384144127
    0x2060304031106101a07021c02220c0212090303030403110106051002010b2809022d07060f0c05070f050109120f020607080f0106030209030a05120a020105100308 71
    0x702e07161a5084454500342c000ca0300c02400001c000102c01038500300c0150503149010625404a8003081c06003461911841c030700d001c401c0c00c41d6034903031065081c03003141968008030403c2d0851000150000e405c4440141c0580200811642c20305001c68071501c1c0d014000314510f4640799402c4400400c10580c42070655a905c40104103a03807441107818820a00754000302d5071000e44002c024402c03285131607809031503903081e18090f52040800c03682d00450304400401030b160510710313600440c2c00c1c5140e4052948d10b070b41075085e14101100303000580480390040030300f004581000d41050045916140f4050041041403000c0400503510301c1d10300ea00301c2e00c680b001140c95202d580c1c074103020125400034a008503903e611030b55102e89c1d04104240c1d00030318a2415000c40e080480c0c407454010018003441c0f04041d00020025603a44003040b09440540d801000c6461700038006810000981042155074015420304005c10551491400c00d10f0640303411048075460105034016030440100601d110141d100d20b15004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 384146555 1250 384145305 384145337
    0x30b0f060d0c060203040f090504020a05010c32011a03120a0c0503040b12070207030b060607021804060f0c0c081204150204080601030c170d0f17090f010e15040206030403 75
    0x42e80000301115001141c4950410306498070300c260355009008401c0c0f6020800000d80e6404050101b00e0b9002c2c00c122241b054541400c54010140100c011700c8000c1510707401180041400f558500442c0340340013003041992410b440310510502c8070510368036500140015081606c6500100140700342400c01018908071507603958150b0704941d002901019012900310307812004061000e6000f0b000c1d20142c001c46041d0781d100d1400c0000641060f0040707101184500131516007000e1107000c0c082001041042e49400d140050182200702004883d441c100303012104613500031095640c1c940da01050b01c90403c10403900d44101140010700a41d0181a20b044c4030442820b14401007015150b400d0103450700d9030550601c00e941c80d400c0d07441598149041c80030a006524081005c0342002001e16100c5d0b00b4007000b00c0700b181d0008911710340c03003c3c2c03240501c144560302100154400c2c525018000034060411100c1c0c4490303e410501420282015100c00010014075292000790707031242c031a040041c10704050480c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 384147805 1250 384146555 384146573
    0x6150114120a090c081609110c0a06090c14092a0705010e060c0708093c19060f0f1206060206060f121011071b060806030304030b0f060d 60
    0x18070740d0b07801d41d550500302e003800310000c1c1c61009040102d004001c101581d69442031250720900c120400c640c2d44440c0c9001446000d0100c0b0391901900c0f084658407034a601f01807000b81080d110499000303481680020341d14547c00c10520300144018100d048581d11401143d0b4102e04082580f201c4420445149a6440240c2d000e807080030301a000000c3c80c0c4801900032482c1103400350411500184c1808444005030301c140444510540c29518101491010600008004542c1e034100000100512803c03c0200351040901c0d0b1156045540b000100d1509202440f500924050703a00041c1591401a0990b401000a1500b02e59180f0305400d06203007241c400821101d07542c0000c00181c20038010b0144c24900041142c090b201d044488500e03d006100c051561003000d0700c1280e2080b40c980c1814900700807460700b40c42d07425410000702c128440340051005100080d81c00303402c000c00d188202180e054200001a54142c962000b60b044141d107840d804d19905483c010012580700f0400d80c503860020ba5a04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 384149055 1250 384147805 384147811
    0x3062809050f060109110f16020a0801050a230f06011107030813080c010201050601021b01120e1f0e0d0305060319060b030d031104030602090d1b090e0615011412 71
    0x14040c03c510350400540b01c05603190125610b00b00d82060188115a0084000f02d6240d0385480b008088034007681d10200e1140701d1198081c1c4040c0d4a003a04201e5440c489802c20130400b800d0810302410141c049041d002d03880070503245511052401800902c035540111700c806051030b117820071940899901da85a0406500459070141c14075201841006003400070007442c0b110002c01d00080c8440e15100c40001d55503029030382400d04045a00c030040010f03034047e20b019004951503203418002d00d801160391a0359211049030b411100101080780524080103031040143c00c03402c0402410004544102c1200901000381440d503060051400b4041c0304a2040132a0308001e1080390085015841d020801d8103209100b40c041c401e042c2001c1d00716131010344100071201982ea2103900140c0ba403004002144070041f1211000f0310300880a40c0a0b004000818825012100074500078040d00710800e0742c1036212002903440500540d270b5050416031541c060208109058040e40c1c041e4200b509a04440022000907 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 384150305 1250 384149055 384149083
    0x302161e03110118170d02040b090307050306011208070c05120105150a060503011806030c0303021f06080d1110090b0f0a0c0801180204050406030b07030b0306280905 73
    0x42010800c2503081036000003000b00010082000d03184152202e815081210b400901d01e811443c5001c4008000d03006940071565a036a086490701c0d102c4840c51915409042c0302c038440d200b4000c001455240000d00c0300c0c16203d01d502c40252919850390380c4003590300034103012a16010000c0011a0035240c041c030010f03444000d000045180d080501c800400d003192030042c035004141c0e41c64244101500501100e045031301c0c1da41039200840524808200070266a003001301017810881000050683c005491a2003450324050030342640350b0780446100b15203651040781e400b5005000d00e805401d010704144108804031500744c07241d10302a0002e1004031741c2e82d81e80c21a4014a404180910b4865520459501000100040000b2900040c024105070f0f814400c0e80005120400290002c00c510340643d0b0080038050410f120a0f81c0b04e1401c1e50a80c1e1040b170701c0301c001070724003d14801d261900050450007440e110304441668a005445001c010094181d040519a2503151940029400b04116000d80001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 384151555 1250 384150305 384150353
    0x52514070f06050414010b0f01181a1201050a030309090507091a0a08090d0c0f050f120406020f070e070c0c21140610150c1202010f0f021801030216 65
    0x1c14503240c0d00058051905c02c0043e0b01d0111007005584030043c62022148007402c3c10540ea546070756900d010042c1c150040301c0180c0720150302e000c40c042400c0140c0804800d8011092b030f03e03030702e510900810b10301b54171002e000100342c42030420181019134030840c4c00c0040c17440c140300e070661030b4401e041d0782500e66a81d010100b0000501250302c20340c011003068001c44c0c01405400880215040204881c40b0f20741c020380030586482da01420001e0030062550120b0980050b14400142ca076170b21a40b40c1c00c1446070344094040c04d030043c6641500821400280e4810920701031041c4c840b00e00440c0d50000c1194101c8800a800e240420003444540c1242260199090100050490352801120030411484400311580c400011b1080052a1034240f000b42d460303001c10030142d08082c1d08120780e18038451101921054400300e80444482e81904002c851926a990038000780d82800b180c0d4040740b054490058240704060011155584a0307001814a21811a4003012000741d90b140c0801c01568410403d80303a40b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 384152805 1250 384151555 384151561
    0x30b19080705010e06040905070c0b09070e0708040f200a030b0a0b061e0904111b07120302060a0902010c1704140603060d020d0c08011d01052514070f0605 68
    0x8104034007405050300380307424180164560042007141c000c81c0149000c0c1070b141e0740041e4030503214100c5140c1458111584100b942800940191034201d45e0140924118400b000100b6080c00303149130a0240b540100c0d42c072060b07004c030b44032403070011080e60b0782d80d102d1900012400195960340c8608005103000d108009040c2c14805802c008581104e45658001d040a000c469190420048a00303141517010b21501c0e03692446100050017070142c1c41110084010204800c1c07a205038544095665000d15011a82c0382502c481c480c80c55001c40c0d843c020300681c849000202e02262320b82145d401280f06060003075610b0015a070340e0b1841461011070035490070003c2030404c0b0703811503405a5212000c1c1074419602d50b00300381002c101010643c0c0c0c4047c2c001d50018200e1001c1200003211003000b4407503040200205005903142d0300845000c141502ca866080030003250070b204c2c251550303051822a4003090300b00140400d0081d01c02c0c038800c0c003003400c640c1410700000780480e11281e9a078415521492002a480c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 384154055 1250 384152805 384152819
    0x2012708030c19080f030c090a0308070209330607080a180f1a0a09030b071710080601121b260f03030606070c050a0b09010f14030c0a030b19 62
    0x90f1600e00503060340018030a08010504400444030800141c0c10301e55038075070300c0c544844041c2c490800095000b00d103c1c0d030000140314200000e48403881c8200d03000b802546410085000000c0000000155016030801012490401001740388460102510140c00c140b0303a5250721109800411040c00803e9038402c902c07003071440700d90040c0f0182404a2a80189505019a50000d030030710600704807070110002014103d9038081c070790341c200955008640b50a90710701044020010302c3d11803910390440124501081c0c800d000f034403005050782c600000603d0345130301e40382c03203800e41c2060080280c540080901040c850b04111000e00c0001d02440212060740c003420f8410000f10a10f52070800d0b01704d8000709031210801002100b16a00310800303d502c2da8840301c450a00c02092030741e6034011940044401d4001810003d020301034002580241c0b00c0d15424502900140c0d01188042140b6194810800001e8071035040d074800761208554615001034451010000f0400141e1030402524110383d80381c1c1c0401c144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 384155305 1250 384154055 384154063
    0xb0310020a090f24020c0a081609090f030e0112050f010608010b0307020d0311041e09060f08060a050406020904090f0209011401050306100201021c05040b070c0f02012708030c 77
    0x83c181d0f00085640c06180210b80c907140d820300301128182d00f180101c44842540f08014040003020010300304503903e40c0d5a96003d82c1e070181c220204008800da40e0001441da89a44103104074583c0201e404e4288901d03076a400c96500c01403c0c00b0505200c1800020f00401c207162280c940705075000707040103101d541840400792420f201603101e15246802002013040300755000c501d05c000d1400e07a0501203440718085a5107041400b5070b810074801d03010f42841080c5c1246042d402c0000301c407640c1200b00541500c078150396551038290300881c04158400004070710b04000c50340c4550340c085d00500c001402c22080c40005001c0d54440d1105607102c0a5241030ac505518207003c9980c0140710310300340e010034414013100182260200410b128071600707100000c0f103041c5000303404482e800c079080b03d8084248054070380390000070042a1403d80700440340f0800100c0a60051902040c6030b40c1100008001d224031390b00445000c0b00540244840844a13084644035803049212100505044e070051074035005000859403030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 384156555 1250 384155305 384155309
    0x20111121b0307020a020f0a150504170102040609120f020a120b1008210c030c0303010317030609010314010f0c0507030201200a082a092403010b0c010b0310020a09 72
    0x2003070808005000d07046070001071412000f0340c140d420401040da0300b0b0015031015099407010360f40c00c01a601d0040030681c0040240180d81619002e9846864071902c1c00d4204d00885c014100498902c4d4020300042044850b4140c096103e2941c1481046195001ca5140c02041e0b1007a4440250304c030180003000b0741519520360100b400200d00b2941480d000303000e41e036810f040c44840c4a8800601c032406e01c0b542c41508558a444262048940e0782990f403041560b0f950003484199081c040c882d08070303a8aa074040e811030340034050081c040c12040c1d003180c82d8140d20441d00e14450801d9940d40744800484140740c000c101030519144c4641d500c030314160502a082d6003001e1402c05036030f840700d0300c80d5510016041c10b86111444a1400066a903078044144c1c15034146628081a01944600c1000714141420300074039901134207468486090500c680340000d0300101890102c000e0001740018420010500d01030030540e50200c002081a01214001c60304240c0c008580c2100181c0025061461541124000300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 384157805 1250 384156555 384156601
    0x303030b0103051b041403150702061803030115050c0a060f05071202040e0c09130504211806030b06040b0414041104080a0803070905100809070f050604030b0702011112 74
    0xc0d640503084d0080c00b9600c00e50003005088540ca0305040003d8600700000e403010100340c0d05040440c188800060f59441c011601d207460070011905074049041c2c080305880c1203400864207244e401d61320325410740303031500800096001e40c40740d1144200414800d00611084286803240001c00f801c041c00000c001c0845e070b5040c80c015a004100403ca00c8404465280c0d111103031050030382e01c907212440080c028a0200d11900629810a814001800750a401c1e00c4041c4018043c550b102c4032483c0b0041d54030406000710020210000300741000098002c1e04034000c19600204010702d030035220140350300c650700180c00c088070b0416400e81da46010b0420303100c1e480107461440c00d80d40c00d261501d01c1449d6144041030740180003503808030201e0402c2e8003c500030001307000c008103000c0344030103502001413504100300c54804c0c60b88156080010224403918140c019114082c040c14035080c00c54903a90903042014002004541d62110724034901c0e500000689a09030304040040c02a06180707503120507641080e05004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 384159055 1250 384157805 384157831
    0x50c15211918060902010c021302180a05280807080714010806030d03090f020603010303050a08010f0803040b0309031e13050a0f15020a0618020109080601050904081608040303030b010305 82
    0x1c02014074901c0103070402da40039101007040c1c401d43c4012074414007921002500036020b980c1c2c3c5200380c0c0ca1b54000d0540c040f5103c5150a00d22045005c110341d4444da44034160b00580f24848111001d85100010180b401c0891040f41b200b5658070142490101c4691006000e0f41180034148455010b003000d070703120440246410900780c10640300003501d480740208518240741e502d01d4900200156402c00302c0001d80c00400042e1a903079030303050182181d03001e400b00d40c0000f100031001007402c0d0713101001c000a550481e0010b5040c181000c071511038a80c07010b8810241707880184100403140304c44041403201030402d2600682c1369800041d42c0304006a00d5040f4601c034a01c0e03d4000d00c0b042e81404502c01c2280c80b036048485000010394030a80c10002c125601500c141d0420b0b0322010084105e510018146200703036079030000c01360f4400003180c60712401c1c01060780c000c92410204000c124000c001d0710302400401d050380744d01560b959550444e07034070960084000c00d45800303400c1c00340d6070941314031a8807442000c640 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 384160305 1250 384159055 384159071
    0x1f110303010e011502010b061204150c050f07020f0409240203060f040914150915040819090803030406060f0e04350c0a0b06030a050c152119 62
    0x60803011414050113005114100440541600c01d402501c4d4201d4081c1580d50b81da4003504406174581401c649c04c3d9000721000f0000c0c214001d942c881e040aa4005035201420010060030310710b000c0d4002881aa4007820501086199641b03510903800c034184155040050188003900030078031006040601d6010b83c0c41803080215688450200f44100101160005a90000c0746040d42d41006100c0840d2481d1061b4208401c800d07042000881c01413044404503044140040040131011404807801404145c084c4000080c0e14010004401c1d04581420050700fa29126415203240d508122000c2e03809548641c010444507004090000150151007140c0c0e026140a4541e03403a03904003022082c903070194420000d0034031f903240e03034071a81d01400c0032100a56458840804554601c0b90102c00c2c1e0303842c030312040400c58520340024110b01c3c4e1a8010040d04890340160f041000100701d01101031a1050100329504c40e17011510108960344620118186280c10088070b16003004c81040c00c007480302490b040013 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 384161555 1250 384160305 384160319
    0x5090313260d09081009030905091e0c18090403270512100f02041d1e0a09031e02100209030f030a1d010305041a070e1f11030301 57
    0x441800e44041500840214094491407855041440c1228945001e001d03990704005a0190504046035080c03011111101c0680301404c049a42441000740855400c6000704041d00380308400d654816400310110b044494140101c800080003120b000184980004000c3c8070038031018000b40e5282c005a400c80c29a11707050364081c1c180400743d10408940da004880d403142950000c0d8118000c1c150203000c50703100c54000d58400d5682c10b6900103440340d00e4100071800c03d505605100782d03411200d805902d20400460340c003500d02001000340c07a09400c0f400c1401070000e40744c0c50f14030345030103010040d10008011402c0c1c10014903900d0300c9141c0724540290022464001a8006000c0d001b00020340c1006a403003c500000a02e448803070840184140030200f80c128001d80c0141c0804400340e00b0000044c0074250b844011002c542d4120350050010b070003002482c2800b8203e0b001503038000100d080140f011102040044d0045c0d080c0c602c038000704144500c41820855101d00b10700d5880050400660540d418290 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 384162805 1250 384161555 384161587
    0x90806070c140f0f03091302091011010b0423180d200730120c050102070b0109060603203c0d060b1207050d021b10050903 54
    0x1001610003206001d08500c031000500120712158941d90441c2e411544c16083c01c1c0d1260421000d56100b08010803a07103040c02c1c0c10740200d45001400405000348442d00d0300040c0d0b0006405810f428280d0b40c1e4a00b00c8059440354402e0f1010326828103500c0c1e541d000d00c018000c40c1c0c00c10003005249454980e000d0844002070001700907103089910305002c040c400040240d4080512880079464851081c11000a150480158490064203505240c3c40d00300c4c0091201683c0231148800c0100295000f101c83c0910038410f104d070342001880b8900161034262031752254031410900fa00b20541d07059560404200703080d010320440524140b90525a40c2900d07500500383e02900400040741c18142c42c82c190060182680f59000340201a06103c10710a49800080c500e40342e08004000482640750081c003150034006401656005170340c613515825559076042044034103400103003a83d8001c680a00c9081a1110900295610340d0130724001002008106204c3c0015500b014185e104039800c1006400d03003082d5051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 384164055 1250 384162805 384162827
    0x306090605221a0a140418030f0c1121010b030c0f1005070206030a02030a140105061b07050301021602091b0d0c0c0606080d0801051905150d0203010e010609080607 72
    0x8000903803a0490200c0d40b0f0485224804243d11040305280420a144019400168103000399010000f600c203460032030201010607803010340030680f0fa0049801891066000581442c4942c100e200002c207140049444004030000141440da41034424a0040000340b1071184030349405c800424544030114085041c0c0c40401d6800b034010410800b84603809401030003181d8407141c0c0501859600c0c5000b1070f20380001e401c05c0d40e401c6205807c18108051044080423064140d41c0e0082031075150a01c42c0c44d12510640c95112010210702a1120004655400b0300c05131010700849490b0320009401d920400a070b0b981d0040c800c80b0200d10a03ca440948003284007550f01004284000140362183d0075402d03a4103440d4180c1c01484581013005c0411003041c08100e150710b50885840b806c8040c0d8a49041003d100c0d801c4080114182104104002c00d15010428000c0849200e03010341c83c2c4111100400b06a074002d0700099096000714004001807648040c0d480002d06d4440060501e45c180418020120b00180e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 384165305 1250 384164055 384164119
    0x20f01240b21010b040e010b07030e04020a0e210f0102040b07030c0f06110901031a0609040902060409140f0a140c030604020c0109030f120513030c050a060c0306090605 74
    0x2ca0320b449541d40c030380c0221103122030210000650b50395612901c3c03420b5200d07026080000740c11100014440c280c0500780c400c01d541c985c4800501065503000c3c0002900040c000c0f1040080406034000d01391901940202010040c96001c0e4480402c080064500f000c14a9485c1c100e070b1040008000ac04070b0402550500741c0e052401c01602501c0d801e0034400721480c0440500454582000e0341e01d070112443c018071400400781c905000e40c11404c0d054a091280c90100135812517001c00070a440b5244c1688180041e5200030001820151282e006104a500c001c03000c220301c40d5101c00303120782101d066001c960712000e000c5017440322807a0f4045034020304101424607035244601102181c402d90341c2c2d4068814925059008000c404201d080c0100700c1603101401c4400309501c6002002c504d0901d000d1306100b40c210b540160295900350750100c800d0040041c0c02d0310240075103015000045d40c40c0c020601d10200710754001c58801d0800004504891559000301d01c42d010074541120031002080d142c070502d440b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 384166555 1250 384165305 384165307
    0x90b0f010c0519081c061703030403080415061d0f2a0a030e030c15060f0904080a030914010501140603040302250f0603090b010b1303060b0a15020f01240b 68
    0x100d25100c6254003503042c03403080041007003210041c15035807035000101f19401a0b0107100800c401d850510703200d00c02620054005130005001901103154502000c403000f02c600720009045648610981c010250a0402c1401902c00070600203d0700505d500350790000441480c02c0c00e0456030300e02041d02e003100007400441d03013200410942552400b903031140308510551801d40c2d40d1808541030700c54135003602440052010302150301117800c034100410f4084100c00d0151544005454a07260303120b450300800d071a00d08064556801c1d030009a00400d503040171031250800441c284d414004603005c442214070349207000307190074010400440d50001c1c00c0013140381006a05030501d501c01d880301c84c8203105a0001c216030441850002161070f816070112071018000e00d0360b07411503600c3d441010114482da62201032030400c1c0c2001400459400e40c1301b84200003006000346150760340c0e000d031803220307414500c001005030f040074901c0c80031001d080c001c82031f07042a0070b0040454107010172100e10b00c03800240203007040c50314 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 384167805 1250 384166555 384166603
    0xa06020318010219150507080c0906130317120a0b090f090708010e0c03060109020c0c060315041118030a03090612090b010b0702100305011406031f090b0f010c05 71
    0x402403004c100c0744100252075070340751000c5003450a040e440d00140c2c80d007100e1030240064101407003000100d02451121940c0c41c07034441905c0400c507054108140d2068060318281e0008002000350031141da076500c2c03c540198640c48007001c2082c0001c0020070240e01e150511806039080e507103894540b40e10060140240559864520115103401c446801821207036180400815194000182040710340c68102c044940d160380700c07588031041e409a45902049a800784c9a400c8151420310f0203190b101c0d201c800810b92000d181000a4140c40380b0140c8401c0644c0700180308410f4108140b035034402c070074003a001001200030b5a81c00501c02100b0748125810400b40b2400e02d040c40e591500240807594202c510949296120400902aa489850121711640c80e00401c0080c1c01d009001d024100e80c05211485d446008100520405500c0141840c0d0204d1400b02d02881d00c5204030f003001c001c0c05600000207900c128a030140240f40350700701d0180b414444049a01c0c0d00207980010303035244001c03607c000e14a900e5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 384169055 1250 384167805 384167807
    0x80604020f0628080610020c0307261f0f0203100311031006080724140702010e1009090e0c13180b04080a120b100e0a09090f110a0602031801 62
    0xc1240d0f0042c00038102c9a03403880d65040c0c1c8943c1090141404075202043d14011180590352205050b509540581280e9020005c6480741ca859415214111100415140c80c1c0f40c00f1506200381044451f854181e07c0005103421206403281400c030900b410b07000c5103141000d22071604840c4172840300500d00c1c80b05402216594409105041c85100165801d100c81c1d601c40c2c0e030507501d07406240101c3c00c40751038103500481d01101079600940301e0388168407a80d5007880d41400142c119880a80141d0610032040400400c070384400c0304e501e090900d20b070380f81c0030000c0c1842e0800c419100c864140103540d610180710308849980c1c004890030541c1080c0c0d0001007552011580700340c0c00c0706130715000e420140d404d410403040c007018000504802801e552800c10440c0701182000071140740305442a00500d0036060010030034001c03070b2000d0a46000801e000c20352541c910916099407502007088a8110704108500c080003180c140300344050100300c030341e11070b603d042180003941d030b0050001c0304040f0031100d624080d445e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 384170305 1250 384169055 384169087
    0xa0f020702010507171b0703110d020a03110303070803091b0103231308030906070206060a0f0b13030c06020a0c090509031c02040e130b06010c12180e010f030b01080604020f06 77
    0x581b0300061603100a12403c0c030759206c48003071100740d84149040d6011011450300b402080b44440d4010310011000d402d40d01d4102807083c8240f00250548010861100810b1551000d10b12400302c1d40e0003081a0b002080044001e002c0003a10981490b003060f02d404880380050762554003041012803104051355078840007510341401e10401a1071074030000117100c030610011031414400c2c2e501c1c2c0c089416540b41c00041c418618528031030703884d03285002141802007440b10b800801072054980c004258060712912899050a001d40c03119025070700031a01030b010040750040d80307402001604000c001a20b040c080040d207034131949071802030600200421140e01ca150b941031701c02815406a01450768900b10240c8002c140081c0000d440403815140060f00640c4186090701c00a5417000494095514454040e19108925481440e06540303d000110f0104468060b082c02459180041d07450640386003812040380c00e041c0c02c040c50b5600031004000150322405803000c4205819108150340700c2d840c042c0c000e00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 384171555 1250 384170305 384170317
    0x80a1509020703020f15041e240516050c0601050405060315090d090e07090e071211070308010e01060207030f140102031003060e030901120504060e0d080a0f02070201050717 76
    0x51544045455414144c0c00204200c410342003c017281c00020302c007400601e040c41c0407038000b042c2c4114002480921710705103400c0342c41c031381c032455040902d090143c11000e105205031303003540034640d07507481000000c100c120b4404c040100c4d20304200d8903142d280c0140c10b072100b20501070170740078540320004149281c40c00c110a81120710504282059400c1c10384269855030303550442800020400a00814500c40c00c603079280c0504115180c860180e454042c000c0c0a414000301a0014480c0460a00590300c280707004140030140308410315070f45c4540b1854041c0680f14182c00c910b09607004003005002d07064000030345e1005e50760071030614000160507244c50742010340713641c86485c400e500120078464902c07440e03030300750301924400c0d60180403d001444105a980c0140028140040d8424152000403551980000d42050003600007041400c1100c5c085882d20034a02030304000100c2c1e81c000c00113105a14481c180ca0200d003080700394500300058000034104c0c015807502500240701085203401c032030384039812242 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 384172661 1106 384171555 384171569
    0x4050601051908040311030a080105030f030403020108040b0408070c0b031e100612020f160c080d0c080310050a06020c090c04061b17070b041e03080a15 67
    0x2a41010180040d018441b110480f4089428140300030644405640c80e107101c40e514040625240c40c0c010011911542c00a000500050307078401006604147c10440c8084661920b09103d000d0340308500c0c00a0504070101e02c00100400c0650155108544040c1c0b819022200c280e800c00c24584112548025080c2d0f40c1801e216660184000c2003180c3d101b09401070a14542440b1101164042d8007182c18081d103105500080020f55421003020b4080314010703003100c0c000000081c00011090034010304226000c400200c5220562642d44001c143c0149601c42464ce5070001a440e14055000305001c0e01c04000083c5101c407404044808650340b036a02c1c03030b9a49401003c0700e2801a94030f44c0403601c11541180742c1c000c009248025002440c05070260f062542050310301900c80e050714150f948071002d140700301c40c0c0110350402c6100b035101c003c45d1408610802c0f0340118410900040c0c118503 = true := by decide +kernel

theorem cover : BRFrame.Cov 383992805 384172661 := by
  have h0 := BRFrame.cov_init 383992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 383992805 ≤ n) (h2 : n < 384172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
