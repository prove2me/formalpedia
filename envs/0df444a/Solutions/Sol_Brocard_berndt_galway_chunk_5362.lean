-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5362
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:37:16.750424+00:00
-- url     : https://prove2.me/submissions/2574ece5-094b-47d7-a07f-45d23b23e375

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 964208633 ≤ n < 964388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 964209883 1250 964208633 964208671
    0x60a0b01050c031e0c032a1f11040503060415060f0609050f0f043917060109030203120c0c040b06070303050c0904020705010614060406170901021b01050411040203 72
    0x404402c000c81034541c441d15442c001005c841182584c00c0f059200082000410940407410401c7d118888880c6010000d003625a1140c0388030b4050384080601070b4200d0340c0d00ca0240c0d509200a0045030081c02d0000d0071120709141c02d1515000700c2081409840c0010700384040042c0c40820180040e060766210f85503202c02d05d08100501228080341555154008100c10040d00f6646407031243c00c40e003602014600e03006c000b500209410840000c124400b1103009007114800c425401101c8440020a01791003824640f21140100d03440c0703105400180d03040c0070350300072a8518413003103000b08400c2d20788038145da0700000b904e010842240c150f10703910380d0007240421a0600103032003070307110562000046450500700103002c000f0800700d802445049840b42c0d0b4a400c01d100c1030b6a0482203c102040844a8078605810120004c005805088207840d406050b0804158290021340680e20200c00380d040d054518810a40003a010302001e071000c1e5203000d454000301825092500850b03108848a042010032481 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 964211133 1250 964209883 964209907
    0xf07060906110c041409010c050406020c090603010603080c062a160c03082d031302010c031202030f06240a27080606011214060d23060a0b01050c03 65
    0x20407240300600b1800b4102d0044596a510710030082d40c03030180300e80c0303801600e40383d05d03a14211002c41c0309403424060184010040c885c0d000178034600f0a241075620b000641c03203c0001c03901400082e040100490300108a01d07150748400150140305984100160042401111400c1c00003005191031038001c1c1030810106c100360b4204031001901c5c0e8810502c0c101000c1e680e80310442c264002a55a00d00e51a8036805082900e407198100e401865481c51010301d54100000c44c2c40ca848820b50009040c02140c800c494281030040f082c0c5081c5054029040d0341d01e02c1c0448050016010442d09035200700746018442d040c07200c542c841c40346182c080c4040749103013241c104c0080d9001e00214850000d20799000002c0c00c0d45114540c100801808504010181810440005821a00c03d10070009040e4030701945c003025200c4000280d904139070103403860050403000d400c18104035600d9001d2505080350801d643c00c1c0920000035170768815202014200810401d400045481d0701c00e41d0350b0550300341d10500030504088 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 964212383 1250 964211133 964211147
    0x8030a0305071e110c090606160201050d0f060608010e090718020f1b061f050418051c08060415150c150228050304120e0409140f07060906 61
    0x40903030600c1410790108010114084003d03140980005111070b1195101210401c09440c103074a08484400e0745140c00c1000ca200c501410001c0c000401483d408070b025039002d40111142c0e82540c0d102403103803401e071450040184c802c621a4500043c1c1a500000e03c0c0300c000c189041c01485050003500c0611700d80002d100c0c071003013050f15008010b60f00b0840c2c1440549004000c040c20501c400c411880040c501010301d0070500c0041562031281d40d09809400b5020a014924041d900c5c00c503400242d0b402c1000040000641c6000010094454544080c008a40d1282c01c1c000d40c1c021035442d41d4441d9101014402629082610348012044890080c06002250081d00350202043d02d040021101651038028158001103102486607900103001044110b1780360744290142c084110003501e0b00910b58009205110040001e400090a80c01c60361031030b4410440c802c1103400051091021440d541011101e0402410040035148598082020381c02c2c8040340031340031107107503440f02032007540360510584041c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 964213633 1250 964212383 964212391
    0x20c040504060e0709050109200f0a02070302041103040501050a290d020306041a0705070209060613030c0611191208131703060118050319140604030f020601090608030a0305 76
    0xe5150303000341100d0841048004001c01080c0c4020690b549420b0b9510112780030420040c038a1846018020341c507000400803504901c00800c80c1c0e07952034039440b10403804d0002c903800080d8400e06020010000c20320740740103540107a000303000030822031321140b090000302c5601c0d40000c90910713075130b4030034411100006d00307040d41801000d4181b1030011000d500090501104403001c9500e071020b40000031990301427114107a0322103018142186416030b030b030700028403003880182034a01c0350a0000e41d40710803070081a043c400541d8003030800034007540c4403000034019101042c481000c51062031000f40000307030344030740300d5006541011291020b01906501125020001002484402071685465001680c884401c01080005c00f962545900300980014990440c8002d10300038820881414080c60b43c000c01c101110140c80141e0040c0307404689812120380380361600c40c1e826400307004100024544c10082040e00681d441c0d0030360301140e0303c600c514001c0b15501d003e00c4c10365501c24002c02c41c40382e010381e00080d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 964214883 1250 964213633 964213643
    0x62d1d0922080c0d02060106020d02031606050a0902041a010219020f0603090a0816020918060c0901020c090901060905011d0c0a031b020706030c050c0c1c0f03030b030d090303020c040504 82
    0x90041e10f501030f24508010006640c006a101e4001001500d40c140400101c10000f0300c069490500c04200c6042d0b18108010302400c03042c0e852001c1142100d00b648040d5410394041c105008210101000341000300f40300d40d029002d4015914004d141404030001481c0d51b55009020526408540003401030305d820007003c01c4c07494400c4940c01c801049010014002d1007a6008030602010754900c14081c0c60140502800303848408140c10040701980400d00316409039a40c41615190081000100c0c54400e140703200035005282e6006014000b08190041c005840d503a060610660341d81d00c02d203001c140e1810002d011440686408100448848070041049c1039242c1350114a030203520b956440c40e016081d0440016900280f0308210554160080c0d00300302c00b1505200781400c0b0034159007616000c0f403051143c400c0f10b12041040750f4a146258021026411440021924071146005001040c00c5100c1d148a44203519003003070200d00c200381d00020789a15902030000c4550000900019201c041d008031a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 964216133 1250 964214883 964214887
    0xa090503121b03130c0504141302150a0206060a080c0627100c03020105090303100308070c240306120f0f05013b16062d1d092208 57
    0x8501d0381542e0103103001e4004165915500c00e030038035100b001c0000590181d80218200b02030002c402c90b580ba040c50b48842c3c000c004100014032403001480144400b00100c81a080c0801d24559103a4000303005c070f120740010b50310005105c0d140c0c1d485c660344004003551a503003c0f40420102d05041d90b070403041c814a500c100720300204031038100c0c0062141c510320003a2000054559403a00709140d0309005554000809a015500c0c40c00e103c7e042101e2a2141d00015241c41c10000301c0b4000c000e0f0400b803000c010010405424540b8481e0f6406109580d40c00280d040041c2c200079000c40c44541005900201d25440410601215003641c2c4030300b5401c100d00c00c15510342d5600e9030200802400d0340b1040005102c1d00c3d4403003100030b00c4096040c9003056500e2010000794004c036401c504407212030802c0020740b0007a0401c44071780040c820300da4801500025070300d030b0300c1302080c0c8000b004290000c03020007506071808600a01490120107102003070904440384480c0c54800c511001e00540d40c007141000d07403409540254 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 964217383 1250 964216133 964216171
    0x1b01060503070312030f05010506041518030c0503150c0d111308031e030108060601030902190b0417160603361a040f1101031b0f080a09050312 63
    0xa0801502e540155155080c00c081d080d080c560500c566040d0b1750120341d082000b541483c0116201c1c2c0128003d88400c040c404448818507405810f084039484502800c112459880f032034415010745c0c0c03c4c81914001d00c00c1c500f000b615501d500c42e07214032840c0e4181005042a825001110190154080c0b40c821144200120302404a18841103805803004000660741c581c400015004001c80b2036188241411040c00103210241007c90340d250000f500340f90120700c03190751780005440c480c518401c0718030f04544648001480c00340e450203030049440b0861408007886031440b0791622841c00340361a0380808011201446458000e0340186481c0c0c1007007803000b8100e10380541c1c84810394891060010301a0054170080b04008683c03042c10544120040145203908265403541c3d04005100401440700e01e101c406045541d2003540105402030b0860a017154100d908040906002c941125000000d02034900107440c49000d030082e940800d038458002e602c0c0108448035400c4001c405031640044101200c500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 964218633 1250 964217383 964217389
    0x61303080f13151401380405031519020306010f0c1704090510080c010f12020f0304080a2a03230310090510030b06040902040b0325080705061b010605 66
    0x4241441640c1000203213820075a42c58107070901050744801004600c0c00900560549814040c21030303440880000403070300911598001d10790081d0380080303405200d8880a001c0d81e001d4140c945005003011100d12388011040c1c103000043c0e2100319580c0703020800e144884050103200c0c100030390b01c15011340041a006495080122030590095004540e101d442d01e01f40504030f04400742400080c02ca820050032645031400c000b074060801100700b00c0c1440005e0f02a0981e000c01d5070121880307640c0e1400c0d1241d0ba8170707052824944607005038181030005110b000480715141c5246a034440d5140c0d80203402d1f440e840c0680d9040714894011010101c0e40c150080080204400380c5001d0342c0941301000c0826481c504100015046400080100840c03144003c8100042442c40081f20b42011003541e0110340d44010340080381c0a45a0000c401c0d801d44200360f0b4407028814a12104070000880c00c00c0102111b58650040390340310f02a002e603a80c001410400030480089428001080080f0f0b000080b60081e50380d000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 964219883 1250 964218633 964218653
    0x90108090109050105091e03072d020a230406270603050706021c1d040b030a23010605010815060a092c010e13020105030a0906021605061303080f13 65
    0x410340203503005d80640420004180c0f0f074110071140c1a80114141317911070301ca803005c04034a0701940c901102b00c0100c140000004454441d20982c014086100e440d507180d9032502c048480300c40604514000311540c03003044c600780c018003041740c000100008409607201e0058030200392010000058039070b91000040054014000c0c4402010325030050440b003c02d0000d0000682a5044040b0400c80c2104803846020b581c039182021103d4241c4002134103c04980202e403601b0720b0410090504c043c40c2d80c060100c01801c1c1801c000c840060802400200e650303c0c0155026081a640203070000c015041d491490b040040240ca8000e000703103401885540d03502701b080e03044074428603055584c02040206080d0050b03510038090040c904d80308a02c04030316000200135405049542c0080c100100080030031401610754100050180d00264219a175201f99551100c90341881d980072110342c003c4100240c422485030000d11030b03007078040d1248201a5210901049840801400302c44180c0d11030701c0c0c540c04141c62520f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 964221133 1250 964219883 964219891
    0x10504080a080709060c030813080c010c090906120b0402150304050309011707080a0f0e030c0705090106030605090c0c101109010e09010b0a1d190e0604020f090108090109050105 78
    0x100d0958800815400504006004105109002c9008030410106500460301d100c9247c140c50039000036100c80c03680e41440c02801b000079118860214171000d02d40411350041380103405581b1170b00940e90351080b83c0360507207119104d28041c010341048200041842203400799480382c8018501c000070085d140d1844410b4005031030a0b6155480440c440721196002101a8580401309038052101c1c030300b00c8801090904003c0c002c00455855242e00000c051484d040600280f03112000c4c1d80d12001000c0d0a65959209445081c1c0b0410340300d000055403e003c1d10440d801c1d11805032030000c00d42d90f16205a84107602c01141200d0920807001030b403210104511601c1d28030051150082e64500210000400c15055110400d1050408800401880d060082210702400680c2802115544145181c01c00c8070485c1d82019042a103201d10020310440341e1031140b003910031400c0023488a840c2c1d0303c28001240602040b6444424082180000f00c0d802162416484003402c0c0003c40c507a001c40c0c0c2c1d42801d542041d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 964222383 1250 964221133 964221143
    0x70203160e04060b0d0b04080711040c0f090905090c0d08040510090504050603010e031c110a051e04050a18090c081b180703090201050d0915060909210c05010504 71
    0x20a210400c0301900038100040f104a07205c49000d4000c1c0c81d1211600710281004004842c0010600d003008072400840e51950340090041140312804c10000d0030a09025038108005401440045001c4010780b00d5140a119040001c0603c0104801403020008244c041991941c4c01400009003955070b1030084022a0b0782c0380e640d452054580f0040c001540c5015101c10320a90410b1140d148050000003681d91412104100c0301c90b410101c0e121b04020700c1070030b0300e00300d500e0b80000c0c040c240140c0100c0200758030a04140d08a905030003001d56520240a14001c10741e1045140004200c4101c07a48903105561a249000198804465940350280100e56210228035081407841406040e4000034410082c078082c3c488004c000c0c0c50003565071140740020090014199200031003019a442182a9003030148401000c1002000e203040482110380c080c840c004519080000105d14055207000316501c00b0742c40700321942c8035003113603601e001e02d6510500700d00c00b08201c421410000c41d0003402064040c0c2d001c3c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 964223633 1250 964222383 964222409
    0x2c0f06070f110c0d1104140c0729040605150301050a0c1101060e0115031d0a060501150215180a0f0b0705040807090203150a033009050607020316 64
    0x101d001d400d0100352108540c1d80d4020007250003c54486000e682940750303008a41e15103e80c000340016000b4038081040903c141d014008000341c400180004000c50b9000341c190580000301d0f07940d09103a00b000b000840804070341c1c2401280000c0c0703641e00900c1d0000c1c110b00d041c08602d03000c5c1000c00d084400440700e0160103911224001e41281d0030504500d191180d00c8000e001c241c0c20076000a01000c0c0c188680d51a110040d002c0711000351081c0d1015000c0c070301d1a100a8640c0004008040e03440c0d50709203080e58424035000000410740000c440e440c5e9500c3c0c0c940c014148240c41d40d2000449500c0041810203001c211101002404c03006000c1414268030035210306c0d0807404582000041a00c0082040d018000100800d219075200040d030407007104d00c00640503035a1342d42c0da8015055203540c00d00c0c00d034001d003901c1c0c0084100251704e0411b00080040d513401d0520b4004804081c21440e004040d507002003000000c00b0700c518100400140070150010f4120350041c04c2c580d0303100318030703040542c0160411885 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 964224883 1250 964223633 964223657
    0x50a030602130e070e09162c04051018050105100f0c141f020405180c28030c0804021018030f08030601021212130609020909010518012c0f0607 63
    0x200c0c2505039007202840042c854a041c020102408d0741480030745070380d0001d81119120140a018603034040c4945801350050089040401010403003400381d02618045404a44664188003000d104441c12504024a100d210401350401550740c003c40120003010000d4044004020498501000801070f01c41c1c4010075480c00302420102401c04030000d40341e1518010842000070396581c5040140002040d40030111a07181d103024850148104450301414a0058000600310788a08100b4101480325840c180005001c03008212100d04084038001e6200d1a900e10000c205072007031030000c040d0750f0103d290510941e200d84502480210142041301c6a400c0041000110359041c0700402501011158003070820714074640804041c1e400a01940d2207040006084051007500d8201400083e000b07052800e45080403070303100b806400103c40c2c42841c044581c030220041841407040c0220f424485004000c4030240d20000c1d1403400e002c10350b64035144180e54400c4c4082c081885000c1c0100129262840c003009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 964226133 1250 964224883 964224889
    0xc091806010905090f0402101b060f050c12040b0c07060207081908041703072109031412060609030a0c12330f0e010603050a0b0a06050a030602130e070e 67
    0x142e59000790780280e446206202000e201070a03a90b030000da0440704d14a00710014101110103003144030912580d0071080580105114140d441000345840404041c003059940300281606c40c030680e04401b07558100c440000d03001c10300e0f000701c03141c020b5003c2c0e40f20f61a16460b91101310598002c000143c0d41e050001070600422840c140c201e4602480908020784c40f4038294664000180d00b4841c0c0ca40302140c0000080c82c918410b0a050403604c1030303c2d9490f80080b1015070100000d01144404a01090000c4c911500300c140400a4940503010400040410382d1000b0620032036401180010740c16204401020b000682060414409822a410556402411414016220111298004110380a4134420301141450055424450040c42408100030401e015a035004000000c1003000d40e510b001c101204009021400040280c090344d00304402e9143c400342d000442d079403407080c03a61005075101c017000041d00d81e4000d0000b152900840001d004d58901e403e80c0710603405c44075a00000c1044200b5080381c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 964227383 1250 964226133 964226147
    0x100204031b080a051c02011d06070306170a0201030f0f0203041227060c020109030c170c03070605120a15030b010e07020a0302071e090f060f12050a0b0c09180601 71
    0x40150030080810020035100c04c3d03125041c4001e289190101e01a0819005000350816030724241c00100003080b000e43c26403903e807590410342d80d160000f801c0140000302c041e40c0642c0403205043c2d0001600005032141e0055004110084580400c5030300c44a0502140b5010b1010b184201d0044007005800600e1141c000c0410070341c00c22038075058115048442540e02c001006006603441ca0030921402c1005c1d00041c3e03141c9001d50b000501c900c00541002c6045060b2007122140342c0c007280100c0e10352052400402d600c0e080e41e4000d1100041040c8030054135240340d0400a03800100030400050115044956480e96560942083d6402100c500c0100804503880c19031035403011643c40941080000b950700252a01552b1103050081d03040100c2c0c0d100c2c115503500c55100100790344602002200321490f0207001a080d14480e424403c10005000245505014002a0380f02c3c0d020b1b0103010008848c1d40e4440180b5030141c5403a040c1e0b01d090240c3c405641f2480b4220386c510341c0c0d10406c01404d1805c00d00040c03100c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 964228633 1250 964227383 964227389
    0xf030906020d0801030602070602091521010b0a05090d14010209090a0b150d1d0615010807091e0e040302010515061809070203160308070f0509030c1002100204031b 72
    0x150311004405032803d0303020b20f00c203041d40c0d4003600241e40e0310309609000e000307405050803007a8023944008411032848200303001060800280e020100354000c0206170b480c520780c001d215100c811102000191030746d5106500414100380001c05601c0e407114191620b1680a09041201c90179039800640c902e01c03880c019401c554003640c80070b0144800240100824401c600d601c41510510501048280c03414480e50011078030b4a03000d48080c0030660212a005540300c0040e039801801c0405101c400300594825001ca40c8038160549840401915021180c00c041c007850a08a0321945420000305491300008050383c060740c02a800810b031424800c009105298026654501c44e0104005108400000d00c51204481c18105c40c0e4449642c1c3d09117041c3d04611900741712109100e0b0300040c07082010740001718107001e07141c0b0380d481003c08404041d09807083d11a00c42c0d01342c3e1592107000040140e103007804412110f201d0510540350150000c098240a0303030800d400482d40000c12415462140d48a40100402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 964229883 1250 964228633 964228637
    0xe1501030c1a03041a100506070f021c0b01060c020d020d0515100f0504020331140a0c050d140105070e01020c06090f0904050304180e19051c02010e06040f030906 71
    0x245007095901e48529030310080174540ca4510010000c0c3c010400000b55900400d03000d8600d0361f64056070320340f1002102184608920a0200d0301e0150221080311107801c058592100204c5526400c0040a80700340102000403a4406811003c03070b00140c4419505200349442080100300005418072003a14800c070060070038000300807241003080180c65a201045c121501542d0050781c944501e85241400e0024280182084130002c1c849184113a0744440000d030b9500030000c03080b140040070342d41500e400303450740c000c1c00359900f84d003040c482c40c0f404480c8000e05078800c1e407100400108151009007512022144200811032040c03a003507895806220004e0b41550480340c483c50900c205001440e0742100f00501070142c0c0c0f01100240800a0800494010344034000041110104201501c000351000944d80507841c041c414161071201410064032240c140d0180203400d07100d0130055072000d01c000d594088011992251140048a2030502c0701c00d0007680201102980140030b401c003d170010710360f6400001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 964231133 1250 964229883 964229887
    0x40c0306110729280911011404050d030f020f1518281e0b06011d130c0c0606140405010b030f0103110f0603190b030a020904060e1501030c1a 62
    0x184080303244002c141c4c020359500080f0802851048503110410125002480701442c2940070402c1c0260061044000a8241d0300e9805011580c080c1c01c126004034403d0b540c0203035040040d140000d00800802c13540308554411510800107480d001442c21300384fc62018001d00d440002c2c403101d124649102410030f40003174007d0464601c4416046001506004500500703450311424500300901e0103200440c1100d405040144001541481e0000100035140380703000c9180c0c070b000c402e8406115100d0b401601c4004115040200700301070240007602a03172507180200310080d06030100098551040c100504148100b4150401e00001480102c64068104170159001030041021500a4801d114152603210028030343e001000004030300200958500c159000e0004000c007c4d507074603150300c51480500c1c200001d104800d001014540c035104c2c816000394000341d2000001d0041207040c3c0003162040c0503001241c220b20704015109151000a070001c61310f4010240e0200100c42940c1450b8080c1d0300034070030581c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 964232383 1250 964231133 964231193
    0x1d18070f02030f030f130c0605091f08070f1e09030b100f030305070f0c06081609060c140a05010c02060f09010510091a040e0109050115050a0b03040c03061107 70
    0x68500d004c0203105201c403d64084c005002c4c1d680c0c894400d00441d600419170402552641c0000c1e1003500300740c412078055000065070100200f01824240400109a00c0c1c1c91002e0b121100211000000e10700e4007014042d5070348410080100ea0485031500010039035580b20694158500f402810310b02034040d001c000301c4460148040110400094100c96040c00c22a54802d135900d899803000b074000320050880030828030002421500f00c840390b4881c000c0c41c07003110321420904030140c1e00041c060080400041c088071601e800a22700000c140700501200d8100c0340b0b03c1441c2d64403a400d40c1e0748c0203142c20050304040c0c10700029020303105556030004450300007030180317140c480c506401c040018803840e031000d41c03241d0020b00040c03007009000003142d5000d07006202d00018001600c0c06446200b5003116150f1a108140c4a02034415801c8011795400034800010103262102c0030001b03800152003995400c1c6446000000a1403621601184282080c1002c0e00c4a030349003400300103d46510282d1803006c07d01c41140c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 964233633 1250 964232383 964232407
    0x2a0406020c04052d070e0301060909120c0818030106050312091c1104090f020a0602030307020f010b1c0507081006031502070b06040518060109020d0e070f0302011d18070f0203 77
    0x1283d2249049465604c050b40d8011040752108401160303260154030f8035801240740c0707103190402c00086007c3d18882540004103541201d8042102c0e20261055105003c181049015240489042607004001140507601c410000703041c440000e94030f440c0070200207160110350904150506907000d400810b604042c1c00c0d0b8503003040c04000415034901c00c40d960b426682c10040d260003903c40103034002d0440e40303000d6283c2501a580fa88151440400b600c00c20b0882c0c0c800e16814050100e05c180b0240c241c0140d6090100c2d82803003850414401c892a009400d004144440d0402500c00d10750b00b20710010070000d00d141858118048031200750766601d0300400a0102141100700d034550020003d803800141036550707aa81c4d0005801c1491510040d008074000058841d51907009440308107943d500c00c01c50041c2c485c00f016911580c5203d1a4420f5503494001c001560203090034030300c4826514140a0b80c1104000001e0b840300040e0418814031034454240020ba651180d048106060140010362801c000071b038803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 964234883 1250 964233633 964233691
    0x907051c05070b07170c0c031c0e0906041d0c010e04050f150f04020a0c060b01022b02100207050d03050a0b06090609040b060c0a0b0705122a0406020c0405 68
    0xd24005900e0024900040040c054031002c4403124040d41700d0345480c1c00c0203d0f02e0710340e80c1c00e0b03410502c41e10030507829501c41c0c100320304201008042c580b2484645c41580090100c580001006950300c15030b92b0103500c0c0c03031400460f80e100c1c0d40c2c16103501801e10031914100240032a41485591030086103060100092440341c1c500c107907000130520b440403000010490005410924180309241c000e030011070024001e036040010344050501c03e04040c42082429001240e841840d0752020254040c0e003407044a8516902c20005200c04240c8180d031800030000c481d40702640c2c030200701112140e105408100e50307a07034144146904081020b030140200d40d80540020854011049064803440f00011859a01e94850340005140d03c00981030b1520707191046032803a1203e01181040c2d425200f56000510424403600c219840401e01ca902c098203611044514007000404043c003c0320400d11840000642c121000608028000c90340145015540f01052206440001d07010081d003400301e02110b00030842801c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 964236133 1250 964234883 964234889
    0x10602100504230a0210020307060b040216080d020c01051302030d030614060d06080d03091505010302010f08070c0203060f01080114042307030804080c0117060d0605070905090907051c0507 83
    0x41443e03a001da2019110305002200d50025440300550702804007064000c4040c095490155404002d4520b190f0180801da211b0080310540c5644040f80d03607000948607a01410404440610050410381400c06140c01c42d44192038021100e800340b4842011490f04100010101c0010f25040c441c55180c07191000303480441000061042d2400f143d40c03138440344164080c1d40140a103c0032501c10b218820070103001044d40c43c0c02a9035040d00740c0310480d818013490044034100c1382d040c1d4981045540c4003c044400400150955081003c11092400980c0e410460366014203c803038088000c40d45000c600e1821211050142d40082441d102003001280400a03055040e0400451041c022414012041e050014a800c01007904d4800302c0c010030078100010310b04200050a0302d42103a81e0081000c40c4010001c100c030001d0340204440c2e900000034106130000c540004003030608400061311071001400010007100d4400c981e501002c000c1185140810001b411070031080000d582141c1c09031956510307001c20740 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 964237383 1250 964236133 964236173
    0x7200901060e06070c0e04050f06040b0402151c050702071a1e09060406030e060709260c12010b040b0d021f020309130b0f0a211a010e010602100504 65
    0xc50010468030f0fa58200c660055201c1c810b50307962900c507100c0c040f8415064805440b10311070413822040070340b400600f45010310780041c070300c103280d90751507003005606088103090400001042c4030b18054140c6c1480840c28117140480701151919281400a2604c0416844405104100d814850004119004503002450140d80089404555025605c144c2c0300d600300c000c1d00710f02c1c00100015060352603848424901d408506494454968050444002445000d9a02c40021440065148801d00c400350600c11100d007007070303a10076402e000016000d66800c4600c03120703694440c0352803105842c00f88a80540c13075104542c10a520311081e0081420441d12f40e207142180c03d20f4814150010b4001c20036030b44039100c014048600c200040c031446001c0c210104005000e044103100d80e10381c030301d0001030700420380d08052507101079040b050017803007941e94080e241603510031745490b003503090a030079100154080d082781e641e400c2071945410340003440c0c0280c01030320a065030700d01014000001c2040c0c0c0392400c20b1003070b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 964238633 1250 964237383 964237397
    0x10308070311061b0937060302190309060e1207020a0e01030308041e0203120a0305090d02030a0e01030605040608012a0903061d0115050411211b0705030720090106 72
    0x44801b0800c160310711210752280c0d240d050010b50100403000d030102c0051148400e074820b2030b9a1014140c0c1680507482100c0360002030402e5018049200c0e5000c504c1541c058440802c6075507820a18a04110441030002e00c0d070400090750b5019410814071010091031111a9800c0562440e20014441100904020041c0f17280040501d000407a5015551103d500281503410507a4414804500c592000340c6080100e4103283c0011003c4101240d1124058035075005540740800d01c20044900a55101e061410305994038400f003000d88031449444050419a40005501000000c1280b44103225401d03010040d182064003115907039001e00e110007280e41c0003d0119000e01603511610300403240400c0041c0a610b0020101d0300c00052000c8035040f110182d0b0100402e03030300b59210f07408520815410510501002900c401e44002500300f840c0c0c4001c10743e0910049651211a0208a901100c01501c00741d0010544c0c6061000e0f0150215044e1a20b4a50086002c0a0342c041141d425052007a8002c2c8006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 964239883 1250 964238633 964238647
    0x20a060c3c0806032a040b040902010c0212030f03160206220615030506040605180a03051c060b0a021609020301050907080405010f0c170c0406080c160803010308070311061b 76
    0x10050030042c001200782402c10600f52191404131740700c040090314801c60902442488500380751041052194060756030740c0c3c2942a540030300503121408403400700c161000700005a814100320024601079a1142c0c3c201601c020751b200001c4c6812805000d001a0301202c2c10041d101290201e09881e180350b10030f2000c55251303d05420051001200d5001821f2030050b403003048204032844d0312491240b04064102503000c01402c001659620100100a01051081000c0752038101a0241580c44c1d0030b94010110740b03141c07101601d01c401c0e0001c07a08040964420707080f401404091103850405030403800011406d66250800140340820040d000c4020700403031764080ba00f84082034100c1078100c50301d10404e0008041542c001401e028003044041000b00d440c001048000103103808031001c580195507841190b80700c00c00ca03441c0c554001ca29258081d02010080400691244061402507000325040c50b20b549044c00d000c2e000c00c882c501d00200903008101040808501743d440c1e400c000640e007030a280c803020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 964241133 1250 964239883 964239889
    0xe03010f02030f072d0e15040501120b0a0b041205010c0305071b050a0215040e010e0c0703111c0512090c0915040e010f05041a04110d03020a060c3c0806 67
    0x100050658001244405c07007180301c0c0c200102424054068a03403008421100104c2d09450050303002d5540003c0e6200308000f80703035001f500000d030718240040500302080d030350b040b07404025402540001803c54030030019800b07118081c071442205d0010707170800b80001d191041005158182030300903004003100101c1c4100c00d0102c200400300d810350303000c5d21144154641003404c2520707811074070455101804810003c282c220131865801d0150b82c3d072440050910201c1d030b80c02d81c0c124406080358501403185ca5420f82e461380310f5407040c001d410802d491305603940002c000d002c0078107400106800c0e86603110b048060155200c003e6032960010400042c44c01043c0c0400001b0b0290560b421004000c1d82084004c080e150115071049000310301c42c406081c14801841265107040c0400c4074081d00c070840c600690301c9a818984a2024010310074415199440019075401d011202103046040001d0303002440700c00208880250080348611000d106c0e42038040790b8842c0303c5d1012501900808001000b00030a1241d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 964242383 1250 964241133 964241177
    0x30c0c02060a020c13021b120301030f080d140a0b0d1220010e0c090612060705070312020c01091401090c090e07080322090e100905030c0a030e03010f02030f07 70
    0xb107030007045a98a00c0400078450040d4000147c1c065030076400c80c0d001c450004e0001041d2420031072040d0614110381c6161554621010542d03c03d54040c83c0410031000440020300c21000000030040d0a9441d5040400810045903896000240200da2850783d400c00300f02812420382d482d00f070318500002d40c030f0b8582151a03455100b1000c0600b10758280000540318140200d1225008002554600b4099807a5400c0161210a071003440742c2d603800a40109200502c203200408065000f41090f000c0103400300300e0349080360702c0b404141410342d540d844000c040041c90024034401f01c0c0090024040c1000715101d0700062a518447c0c205883e680d200110700b5082d003440000d0081102c242640d031121150450301080c002e003024045200348901d00081560045482840f000d01002c000610315411045031500090031003180550300d51109010b401c0c91a030301044540d040038030030b03130381c0019103402c007000d142c25030b190340c1c544a929070f006004020b0b8100c00b0300a0b1661251892400301c040b8240071207924100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 964243633 1250 964242383 964242403
    0x6010909031d0f060a110d0302250201170a0504060e030a4d24192a02060f0402151c021206031501030c05130b060a0e010906030c0c02060a02 62
    0x210000c00c80341911a0020140506c0201003400c0da518841514400c401324400c24070f80351040c003020700c1c0c50003454024800c160070240c4107044c1015030320f8402c2c0c500c841900781110a1446907485500704002c008050145070b05074207450006605003001100042c060030b9503032061540c0111160003034006020101c080c504810b143e12100c40b400090710f021490008941c0f01416090b01c1811008408402140b026001510b801141c0c00e101d40c0b580901d1100da076041031508550561200826406000c40d801026484000318291114130b1503442e00181c2000c800501a0180c508118200070160710f40d01c000e8070700e09404041459440d1919000343e80305100d10124403482c14400314540103064030502c051405000101c1c1120161502d00d0382e101041c0e1003d000043c005a070f098001c00c01400e15550f03969001100d50000f041d041c005c64049203841d00030004400001e981032640605075600842020060403251800344002d401c420340180c403080c00500024000c880014104981c24800d004500b01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 964244883 1250 964243633 964243639
    0x405041a0616020909030408030301140102010b12010c0f05030606040e1308040e101220030705041407201207080409050405070f150801050f010509060d0203040506010909031d0f 78
    0x2c600d41c040080b05040c0d2080401c034040c000090220340064070010603074003150916401035140d03030b0070f08070000341d0031441c030044505564030f440c640182650b50146c103440e8405e0010000400c2031a450380100b4407091070b41e801050240030014000c494a900048806903602511510706a4441107180011994168000350140c2000704000c01c202043c58900341c000c01d0b072480c0c1c41c02a5601c2d510700280a52940000a20341a00f450003e0100b882c4100b0034200f40d6402826217003015503420104050320104c002c40c0c030880035048100401039030000d400c201040d80c00c4800c54109022000c58079a40c03001200c528008110224110042258140840300602001c503000d00c814141407804039602c83c1e00c1e00903044144c4c003140000c40c201c031056002c4101d8031071550300c403a941d03480c03c8280403005003806035103410000100815000e03522407600920703e072802c000e80181d480c641380c20414100700042e08000300761f5003416400300100e503020724000c100020b03004d0018084080b940001c3d580354615044160 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 964246133 1250 964244883 964244887
    0x10c1716170a08010e06100c1b170717060c03040f14100e210c011103012702070201050f130e010b09040b0307050603131b09020c160b0405041a06 64
    0x40840d4100020b022038031065154950180d07203904110342d44413811035085400c06003180c40d49030340d00d1142c102244003c1c051083c500718010115440d450030f8282d03810080d200700c2121707003050081c1401c21884005000c1550f501c9c1c520545002c019450300c8001d40a21a01c510100101d0305001d00c401e181c80910ba40900c2082e03855014290f100d480c5c40b020500e0907802c0340b07841c19080f600b07032001c02c1a03003105c1d903003000500158801038600c0956410404903e0300755035850b4000700801c408040154045d0491009004800600c41004008481c00c260718600f1980103100040060b40c10405880402851f42416a01c03014152003648101410f0780c17044d4000341c1080c3c00003d00d071440c98018044810b09440074060030410005140d5034250700d100d40c0ea08108c0410000701da4501301043c6ca062107106800c24107906048800c2041d00700d010780c0244411990008400b4040d500030041031003003252700c42d81b80c0308451501e11003a026000714403603140503030388030120700c042e16800320441568448001c0c8115 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 964247383 1250 964246133 964246163
    0x1d0d2406091406150d18300906052a010f0204061206050a090203060a0e0c0901080a2d02070807060b0f090103050d03020a112a010c1716 60
    0x500300b20b15038000a00542c2c0c011900314180700d0b5544800300300200a441ca040c0200008000034002c00841c910196440c000d050001003e000010034100c41100b80d8100c0c03008080c00034458000b9966024003800941682040f50030b401c2410740f00c25000701c410f183c8036500b12000f41c900c03410103580c144006500c0c00201d0340d2581c10715400340c419550150f40309004450b00251b0141244c0d01801003a5001c00048000c0048030340c15001590300000c094809001c0c01c0e69800107120401e070680742d1700c21100d400301f166109942d02841495001200c8d03001400b040780800048034170004840300009900440510f5108041055011a10101d9022402e00d541d00c0050802d1801007680190084c41030b650850006280e16140e24250f05803600f1800bc0c0681307400405040d4000e51026100e4002d2200004840c104610b041c4000c0c8031000201520030000c51200e12500303203481000200c2030510900d0036050b4003185081c60300c4650504168807281d500c2c8a101c0c00c5c1618100d03500402402601c2440080d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 964248633 1250 964247383 964247399
    0x3090218070801060e0f090115030612080703080a02030411010c05120a0c3e0f12060a060614220801020301060c11091b1e18011d0d2406 60
    0x16040744e83c903541d41c2248070b25031410030005103890340c0810344c0040c02c10010b01110007134021030802e40015003000034003a580c032440480c5180e04100c003900c0e81000840c2078018150069001640200041030840c5586000e5035008004100340401a0400601716080760403c4010030001c0c000044429100d502c8644100009000640000701102c41616030011040030b0550030080c11444003406c146607400b00d41e4102c01040d5050b050541c0d9501c00f1540c000010700d901e600c040d980449408074060045881c0c41d840075001d94000340d00c071a040000d030030102400e0100e0803007680c0001400107016642103010a0354103282482e250000047e5503c00400000c4d1542c0140414144510684407010702c10700240804c00c4420341150007032250450010150552aa00c2c4020400400b041c4c0a080aa21a44c9a503544c0c3e03802111003002c2d01c40e1002c030201c00d250f8000c03150624107480e44204030800d003a01c101044018943c040000c050f00010a6801c00300d000307001102c4440a04c0c89410072029542d9192 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 964249883 1250 964248633 964248647
    0x140406020d1e0b15031b030a0f060902090117010b0a0c060902180412030e0c1c0506010303030f0b09010b2203050a03020319050c120c032203021503090d0309021807 72
    0x1203d44980610342100303d081c0021001d4902c030307001160a8070a810400d841c0c030340456000401038150320703544450b415020040f0744601d202400e401d94006898a09800c0050800d19000304081c141101c080c00401c100c02a000c22111606810700d400c000204240c500800602681c0a0082d8402c0034114001d40421160100910850150914040c01d60480a090f0103c1d0441c5000050755000b1103411122400c0000310138803e00300c24918280c00307229075155507041c01401e0f041280040c0d1139100030202500d540c040c41c4000c0350110303064000c5515004841425104000c0320306940303c0600f8107280301c040c200740c0035401903400c04180c403003025551038001e4607544054041c607003141030850721000140c41079040d51440314008000f810030b104480390200307043c6c201c607056504030b00c81001000410380038200449a440c9108280100050031841000b03003c2c280001075201180040c0200084910000f511101804140c28009001c86050001c50301a080b00d0a03c00c02e042601707003e10160a5001d91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 964251133 1250 964249883 964249901
    0xc11010e01090f1526011415031609090b0109030f05070803190305010603110706094b0b151311030603060105030f100b030a05010c021609140406020d1e 67
    0x1c1d445035140c03a03601c0700e42c140e20520144071051782c11000c0148038100e11214900e00046000f401d1031310301c0c0c20140d420001b6a204070f0720340c02044149401c10b0300c0945c2190421000d81000c01041c0300596013000000d04118083c0b1000c0d003100a130310a46018820244800c40c0031306081c2050302e42d074100c4403080215072180d0035100c000182c0750200005807148644a9601d81080c101700d46490901070352200e401404001400f642c0000c10034004094280300214040325840400c90001072041c40d41901403155a002100e0081b170300101c41c86180083c520300340707035940007041070f001349801004280840c2107281c0c0b8908002000c2e2a041d46c6034201042000030f54401c030011011244039a880304141612814a5100152aa405020244802c4810b5003090000c030a020341190303060b03103454540d83d080d1a1101c8200000d030b000785001c00301031101d810110005d000040300601c100c500702c02e0315480c000401080036000c00c1d03001c925080c991145411018880051810750b100040051800600803d1104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 964252383 1250 964251133 964251137
    0x6060b041d06061e0702010e030717011a010c02010c11040504080c1006141309020d06021e040f0605210103140c010201180212030f0a0914010c11010e01090f15 70
    0x20300010b00d00d10707040d001c0b5a4018134040089078452400d880c2203002e5000380e80b00300c2c184101001101040e8600308810001230a0749210001c0340d0019224507401c650408645040d140402000002c03140d0300200703a03061003603080c40d00d4650296241041c00c83d2038000e0080541c020300300000e010a104200c0d002d001101200710a13146003002c2c6504200448540c0d02c07503107504002032440c80010b45402e41140040706035811001c10080308660018200c10000c40048a4040d030110707018420581d0f1541226582900c00080c0e454a41005d03039000007240b00380b20f81c9040000001c0c00d0241c0781c071308403000b1402c1c491440c0e0080700d55860b4035103030713444403039051010b0303418070074154004032561050040c0480d441c0100d0504c14150703440e80074068032426000215606210030041007640316000c6c80144428280d070b40d130f00224142441400f540c1d850b4590611810813400d2850301c03012600607105000700d01c4e03090034071294a00c29400140c80c1c014080d4444988141e5002000600564659115030881026 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 964253633 1250 964252383 964252439
    0x140d060605032205060c0c030403050a05100510080712060204050907030b1203070201090b070606051e090711060f0a0e030724050f011a0f03240103020f09090406060b04 74
    0xe40d04600c8840829903011380980c0c070403404108161000f034010807000203244103582ca040d413a915014900300d1610011103a51307000e81000103c1c0790307281c4a40c2c0d4000b069103218003811461301c0c035055a40c041c113010f44020082c400e00c150081000d150b04031402880080c120419038942003101500804080301600d009500041c881a1241c1c000b008840503a6416110000c686050404169241d00010b41c02c445480e030310100030a25959101400c80950740c4d041790110f8801840043c0103c041c009000c50b030900c454a10361451440012404030b900000240d150001d0741c1d5154000b07006008421640c40d024000083d0140074004841050740e080c1140410703215907001880d43c0c1c1d42c2255811241c16104070180c9006020580205400201c803414031500d00f400c00400d0610038005600c10781d0b40c0d05c01e560a545003100c0d03c034218582146405001d083c11801c0030360000d2a022188590402c20744291024030000d0100152680014007030081404082e4480742c9560800c10098280000d001d03144002e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 964254883 1250 964253633 964253671
    0x31208041505060303220e2a0a080c030901111908061c0f06090611070203061305100c05040e0903121f0302130f0e01050114040b0d03140d06060503 65
    0x342d000740c902038800500107610b01840320f02040384001c2da0340d00c13040c40a03c2040c0005001008104210300800074401501911459011904400c85c0708126a2020100c02d014140140ea000810194841c2d107941600d541c0c0d0780c60500d65801000311211407499070310045000390b00100400341460507159983c4400300d10351141010000c2100301c0070800140c030300d601e4100c1c80000f0340a0780f440444a1081d00046140e6101d40e488505a401c40740381c9055542001c50380d00294501080081d405c189402009050f107000d41c0c4601c1d0302e43c035801e03000700700c402d03100c505070940380784541c0c01c80d401821034907a4000c8a00302000701580720ba00a1000c041c1002e025000f090002c5580d56855514004030350307030040c441d0b203983c2c280400d510500042ca1420f9136210590302100c1190b01400700c0340318070344000203207543c100403840741c400c6002032800f0f00030751509090300e0540e120105130654164150800d41c00e5403c00186881484c850399083c480305038144a00000c50a41102c003860113410744103041616040707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 964256133 1250 964254883 964254923
    0x70e0a08070b0a05070c0e0a0c1b0b06061605060907030c0501050307050703031d0109030807030f090206030a0f020c0339031e36090903040303050901030603120804 72
    0x85010b100e5103201e00304111880c41e40110000c202c03007840b80a081745155603510500c005032004459490007075803103001c060f40c0c1c503600000b40d03500c8410001030b81610300c130151a003c0b60640c0003844240500c60000d04412718144661b21000610b42c420304130303282c0d85480b550807602c031425031100310742805c42e564001c00d82d98003d00546c0e02c503103c91f0f07170341505008042c0ca0480c00f6140390b9000c0d20a8103414202100880c03001e00810020a00940702c08105080000000303048603ca0b00100001034070f80b00303101d80141d031030804490b009944840089080359406860000900c104050750f48030388400211007035401898400000c1c000038110f0b0342d1078034141c5001c60400400000386408200d400400841e1003041000e00b00070070000840c4105420041200600720206540b5191a213807000c040d80040c06c95001828040816402622209194146080311070394038021804000c2c2441408102850381d40d2103076110b5001147c20980415044c2107210002e85070000683c0c00f6560340320000303d00342c2c0ca0a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 964257383 1250 964256133 964256143
    0x1606150302010807031503170c07050f010912020f0607140d14160c05031e0106080c030604030c0f0609030c020f090103020108061c0b09030405101d09130b070e0a08 72
    0x103a0103071200c40f915901d00d44104c000301a05244001d4100380c03910084040399500400040840100c03820668900100380407030f280001319402103105a607a1202c0c0c10503640c0c843c494804480d980555159801e18078400170b0554000f81c1e14090b0001d0011035458107004000030907403a003203035203020b0301c070840d40401c8122040241a03a0140d1302c080f00301310f00040f46840800301c284140c0151015410f003522000064241030b90403007001c1c0c3c00c0d10041074141d82c0250a2207004000d0540c2d20040006210341d4005c03d4680900900207014042c56061074000d2009071400b01c40c0b07196010f14104845607181c42c01802204035030074203900409444003820458104140110f05894051711030010940d40d010421000824005c0240749030b58000310845d0008000d140070320b00441c40c0401858449040c04240201c1d0480609a0350401c0032005400564110022304010004070a0b01c0300815540d4852100c407030955110001860803551204201001d60700c00c145140c40003085410081c0c260342c80500503070351 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 964258633 1250 964257383 964257389
    0x1503060108060d06020c0a061506020a0c1a041a030f070e09010b09120304030506010e0606070c1206020f070b01030c0510120b010903170706050a05012d0b160615 71
    0x1003110310021601e18030705582c0203000d00e40305800c0949001144881c003807e200603900110b0b910764980c0046e4101c0d02641030514041e20585c8010000744480c0d8403200d48c9408144100d03103034035408110540c12102c0150481d40a40000d02d03070b000003120300e0702400f482030b0b100b180e01c851410b038204041a040c0e8030515803c3c440e0070340140410016424a02140d401d0fa0110075901d034400c4c0d4550581c1c60000050000d04021409080505030a40c501040303030309081c0006000c02d00c120010044040011444202c0c03034240e484400003a6001e42d202c0c60b01400034804c0030b8900072051400b0420608001c00c10b403c65059a1040c0c64015140b5500c009002d0300d130b0b10410308000442c2902c1c0d90985102c03496803001c07846020500d001600c0694945076880d6a12481c100500c2d80d0f48009041e4051006a001c0c60740c0222003004100103541c58802007060100c034429451402040d00741c80300204034421104013001d08800c0c2d5001d0b980c0c06000c8000000c42c8451042203502c1800c01d4220313198414001120822 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 964259883 1250 964258633 964258637
    0x1030c090504110919090f0c0501020a15180804090b010e04110d0f09060c020703030e010f2001060812090a050906030706120608030d02270303040b070503040b0a02070515030601 78
    0x200d04241d00030000138450040103407801d0000b8842d2249880c950740985021a4011880c0d4000070343e050411b0700d10a812a00528155170000402000254807036941c00d01c00a00000c00181e4805003004c0005c0d00038003202c0c0a400b2036408500440d13800000d40c00760080b48026214144942411410b20064440d06000ca44020300306000c08081c010380d0740c0010044104044001800da80c1c1a80d5100480f40842c0190005038440c14041c8105604026403084080090824050a91114000030105510b0482000d07085408081c103142151094118402400c2c03d80e043d10b000c540881d94441d9140c02c0380302018802d2081c040c000489003407000d2070a02510014000d04101400e007034080c0c031520120040c41070310743d42d104400950360a060001e080240b18003e0056642e0401d8141070b983c640c140c0b080c40c0408000d01003410340c603545c000200c03801c54840403402070b201d4000342030040c00c601486d030180b05034603400254002c0c0990301203a00c900351503080700c0100641c840c1c0c8091080900003200d8442c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 964261133 1250 964259883 964259903
    0xa0201080c0c01061203030203100b16030e06070b070315050901030b07080618090a200f010f17010b03060111072312010f0e07060c0b0f060409080f0301030c090504 72
    0x70740784101c40c001c0603600c80308000030800650b00c40058807400808030003074001039804428048080d0440c0303002d000400f00e0304406400c1c04000004041441c00c6120300906115000402c5030060710b0711400c0c0c43c421500400a0b01052800c03680240c09003040f41180203d040e8462004070b05d91500c3c5040038162504a01e0206042d91403290588091001402039039000b4050000f95443c0a058408075100300b5840000d000e00440030310707006c90540380307000424071250450f007080c480343c0d1180103031340d1038401c42460070500500d1100c00503100c1a52000102c2d10b80500c00f0b0000c038146038994000c500508080c0e0320788800b800c0324483c1d42d4a80c0214012142018811312030701880420300c50041c1c03046200200b24501c8042070f001c4560031181050680f82c0d000f610740c8101490241e09005000081220741085c1010080d2551a0780a00d2401030182e0b040f410b44001003103c075203480d80403203905540502096910800071628880380c1d0402d11080340e409c2840c09000c00c99400c18003d9602607076121103080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 964262383 1250 964261133 964261141
    0x51f0c0b04140703030e0f0111101a03030a0c0b06030c1f022811120703030302030c070506010305060f01120b06061b190311070b0f0714060c0a020f0a020108 69
    0xa1195034024209590700d61418040400701481800040000c0d8031076180e8504402458003800f2079403d2511507541442042c98182c02c4140740450900030008030540002582070607840c1c8032101100120010b81c0500c008a4084a665000b0f10002203207401743c5030350708842c4d403148101507a48040c1104a44c106610b4401060b0784030401080c00f54090f40340c010b450014219884034180307849855071504900b4013485410050024541d03e0840c03040d8141d400014194610655555582035488000d04040d80040081c41d00040c25054a051543c40302c16159256560b0a001e0b554007419200200751a001400000701803008040c08501554450483d9006585003c20452103821401e001e4072021400c0d41645141981845081616901048510088280c500340140644000c4010249945c000741050105c80300b00429140b0b00707080092060b0355980c8910380114031a101681c17256807440307007409100340841114083d200d030320b07400d60803590014898900c1d15594254030002074082060b0030049 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 964263633 1250 964262383 964262393
    0x30708031b1204030e0d030e100909020f040f0e0105090c0c01020c0105010b04090c110a110127030623041203060305030c07030501110721140c0106051f0c 68
    0x1840d0710a120101c25114080000703480a4140d018a04003414680c1840402c4105600510300d518a20020b07139440d404003403142d402400700110540981c1c0f1500401111120152044030382c1006004182e10554a13074452003080c202603005400b4030542546d0100f004941005800ea05a040310303c020301e0340429440d08030203641d80d44e100805c41c40055408202c0000124030900646000f400c0c0d007080c42c0e03580e03480d0209100031545146c07403003070400032800d03004201d89800081e0482d42d181c0101010f034034210742a0060b41c11104e001c0340c46d40d1001c0c2c0b2140260444030030080f00001c40303015050501c9516a1115252609982d1074a20428442007001040201d90815040c005150035800c000820685a0300c1d80f51070740d002102440016400310300240100582030203080460101c41c40c209042c070369603503a00b0052080001c00788540c2c01031f45480b41070b9503114403401d0080a02c031b10f0b80306584615450170b15010308030038014140102c1528010300701081c0a11044e44501880d982c03202c841040903a14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 964264883 1250 964263633 964263637
    0x18010e06120f0a03030e010204141314010909060609110714070f030818030705090f07020309100509040b0108011a07020f1215010e0403052b020c031309060305030708 73
    0x9281c0c102000402056904400b0040302c4000341601c8000c141d9411035103002403d440440c0180440c07a4018031081050f40d0702031800100141003141c000440d01c1d0106101001030030001341e000388014178440002a4440554480140d1130f0003114140525a180d64048013501c00d510030107407014a00f0003101c00030403104031089640056000035500d6071556002c0392899200c0c241c2060362a0000000c021414459100a45410750b1040c0e018220f2549410001004e140005095002021100340000e480c507100f44116005100002c091010034101418000c00d50382110500321300513450003244a140750b0040004604881c0f01041050403035512102440303840e00b0905040b45c1020b98011442c000d90342c1d00304403c0840b0504002030803021410008004c0e81031040e840301705581c40500910002c603901c1030844640441c450a6030002c85021403c2031004030050812542c0b003031000c503944040f840c000c4020905e02011080c1c0340806a1107241203021a5058480107000d0341c0308001c0c0308000751403400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 964266133 1250 964264883 964264891
    0x403081207091e18050609040f050705031c08070809060a0b0a030f0b060a06030e0a0201050304110a150f2f1e06100905060d060b06130b0901090518010e 67
    0x2a1200c030450303444900344504030088804014000c2010f0050001e40081a07040034035468a0905001c3c03802d202005c101500c80c080c4c80500717a803821200308004c0c0201041104002c000103401c881096a200011010210701d81200c0d400140315207022540d00b0744107080c200d014071020000340c043da072650012100180341c00b030301a9030890110034001001c150110011003415000702100c04440c45d0460070004050103640210703040c182b8010750094507010018a0082440e42820001c2d600d8585c0e05000e8840030042c0809544440070580110b4013a5101401001101c42030f100c2282c490380d40c076410f0344c44d400c42c02d604007101d030100b091244850b07141c0000180d003400520705449801c2c01c0308085e007004070590012001c0320350050082c001c800c05541768040003040d07081b20400290070b2090001d0184404040040c0c5500d40340c0f41107080c40d584020480e0300042d001d01164601599424404409810a903002c43c080f5008100c0011642040c4800c00143c40300c40f150180680e082c45902261050064 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 964267383 1250 964266133 964266137
    0x91801060e01091d0604050601031b030209090a060608070e24030a030c020108011406072d110f0d0803014a071805220203160e060403081207 62
    0x400e001411080901e5214040c1c0b1400350042040d40212a0074402130703904c010250016408a010400070850215503a4107403a40040c110103507001a610005100380c1d0b9410195000d040c22050020380400060307440318051041d07809014550341c403d03180d42c40b00524854205c408090000003002084008000c0a104080049856540c042a0b02092130306503e000c0c2100440d02c4541141c0556821010840c01481c80440c480c6003100a00d000c500035004c0c00728020030b51038145960407140300d020490980070b50b10b035561440b078200d6541401c0c2c0c2520446050140548420091008142440380c0741280e4030307400c194403500c0c69103000d0003803000c101001591001020300c150055444504c41e41075484020031103001d80004107030017404003c60fa4000d01214180b14034203090f01d5404000159441c2260400c80d1568030007040d140608024521001d00058803510000030400021040c010500c1c110119598070052401c0c270109001c160b12035400b0181078058240110031074400b08221640c0d2051481c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 964268633 1250 964267383 964267391
    0x2090f040b040906090305120c1603030e0f06190f020c030a0c0c03020a091b0e241b03040e0a091a040f020d0302100b040902060d0c050708040906170c091801 69
    0x50380f43c0104540c0100300c218001880000d82100230420940e145130070103030110000345010701144405040b1503050350020241a100c2e041e0606000c0e003800a002e00d00030400c1034903001c2c9400d10f981c21a0f1602c2d800c056100c24500071444a06501d144280e03124249441c00451410795400019551b020313a0f00f02c00c07515034a0808020006803280d040b0740300102a0002c02082000f000b40082c0781140045000030108815104190b209680e03080144440140303030501c00d5a070014400b00c05a070b03842220403002c1e2079101003081d24080c00c1c0c004010000c0307a021103001040c0380c503070500b0102640c104c40c0d0302401742105100c200d202424807915013a0881d02c02c6280910030500d642c0400e0203214038035000e501581040d401581c815145000708020380408035000c100f6507060740d0014140b40030302000f000110350340d101c4000300036005030700302c1300c03801d402000c590f483c1c0c0d546078424000b80c0000d000710074000c013400b500691300003000117030103007000c60060048455560b1544104503101088103401c40543d21 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 964269883 1250 964268633 964268651
    0x30c0d2d050a0605040509060403080a02162105040b251b0303020d17010e06010e1e0307140d030c0302010209130b030708030301080607110a0c06120b0402090f040b04 73
    0x52840348441510200901080c10318151258104942c8141e00107030107136081c541085106040440c409901c1030745400c0c1303465a40c071020396901c028000c500003c00709220203403100c030038005280854030540e03188400045103071502d0401100c1c05d0040f4811b00c8040c0c042442074196078040e45214000501c0d026030100031900103515151642d40e80c80300181442845a2800e1051640c1800f45040c0e120300c5060000300d2420041050b6008001403250911884c58600410451382c4507050f07039111010020805121804545030300c00704080d01c520110f100b8441d0700000030700c0a00c3c01940410b0503c0080c041c107000205900d0954001c0c1e04c0c20012800c40d50b0030800c1440c0d5940e8892030721b03101e4004800c005000d804034001d0529054164024980c150700610040010300e4001410030390000c85850b000c400d1780c5070002001d1030103a250800400c142c2000740c0201c1c0d029445201111400e112400c1880b5010103103003400308a01c103581c0303c03641001ca141c1c0304040c107040030f030071401d0140806400041c40c003c0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 964271133 1250 964269883 964269941
    0x6160f0c08071a0a11031b07021c03050a08060d02180403030f1a030c040522080708280306032f0604290a09170f1e0111030c0d 56
    0x18241e48040311401c419804d00000c414a8480d40c2e0811a104031810701d9401c1c00c1c0c003880c002c0010b40349944940350000807207800f1900c80003030300710346945001c80d200314130310700c918018003560402c0c0c1c1c460001483c60702c000b4141e0b20f000a004100140c0103010110021068100f6521004009200798203060f02c2e1004810650b6043c400e00f54901400041c940c519400003080605040c45242d21b68800c074140803c1c042403204401d040030110803499405154403201d071030510700ca0b0084003005404c007240420001d0300c0030815410403c1340e010900601d00c0d101901501501242c0007404060300000310501e2862490880c0b80c0764403030348a0308c01885200c2d01c0ca114001083c540c85a000b06134500c150107015000c1040c2c4400c1c802d003600005600c2c07420701c0c9580380010444503080c400e4240645880091001090b4113100001c40203282109803514403a8180d002d507092480c44141c58084e620f001c24140b40f010303404090301d00940000780242d1070300f0300c13075072aa0f0080c001c1c209045155440d0340c005141c61007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 964272383 1250 964271133 964271153
    0x6030403022a030f070b031303110d050909090d02060705030709091b0201181a060402070b040c050a0f14040203090f030a020a02091014011107090c080906160f0c0807 73
    0x42100c40c8a2840c0c401950b040c141480c1001d685020940c0c0a081c050020a02090540b40e018601c2c003043c80544803141000c0310024078554106a5034040c521252007442e511000810720204256074400c50b54981d858095612400d062003400140c00c01001b10b04454860030003946c000f0a20320380040348a44560148044510360701c8404154a40b0941c2c180c4c0c62038080c01203010f140061000942422210b4442604338011490300f91449810080081c00aa41d0381d81940c3c602d035086610140541fa01c0d18140c2020b134401c0c00341c00c2c480c0c050010b00180e44100915000195501402d01091102074001800b010750000f500c5454280115041b01c46400020400b8007207181560b40100794042e60350040c00700001d4060300060803003107042010701001044410704012070800780307864140d0b400c044540f070341800c01d590004e00c0140e082c00d000f06070130359106414030b00483c0300c036003500c2203500d85502c2010007001c581c0100000c500c003501202911800340e281a070790305002d940c95520780303405a61210885 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 964273633 1250 964272383 964272433
    0x60f0d11060a0504080105010b030402130903092402060108031801110a02220e070509070e040e240a0c02070506030a020403080f0a0f0e360103061d06150603040302 72
    0x68020404203e0f0750800d015488c01403076807565091650601d0b8011510b14200804498055502e0b42d20000415200c1d41901c2c0062601841050340c5a0103541111450b55201c141a0014483c8074000302e04800080304440510a0038428a0071120317005006560002d254103180d1068002c10545102589404160000d12548451056250359101080d1001c0712401e10240d80d10350310040303092200342c0700c2d01c010300e4108240341013041131080f01d200010060088444400303114003441d15a903126000c00740e0344800f04002030b10303120303c00d0f542c100071201221034100000005902039041080681091001540c004071082e10140c80e1945a84500c4503c2c1e04c05071445460190014070590703015030042040b403c10704075140c0308007440000000109014103490300018800d106158120341180c0034040c01961246e0f05121240b550303540d09100c00248005816581c1e0b104507190030407040340010801c18440ca183c2108006548010380c02d01409410040003101948a440494002034603150410409 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 964274883 1250 964273633 964273637
    0x7050d060905060106210203061f05041a07112107081c0503330301050c070c0e070930050a17120a020d02130b040518060f0d11060a 58
    0x140720603a1a0503440d206050f40321108000709600b41c00466081c0a00b0804510002080940c607a00c0310f200240c0c0c402c080c0c189d02680b2400c0142010002d0b41c101000c2c000320b960600d03d6000a0f8501442c04100340310b040401081801c01140700c258514012607401c0c0c440c0c481c40c030f0303011020140e100d00030b03e000940e8114070095804000c10b042e040303c00c03403100b9010040c645411801d40c201441d00810202000c000c4083e056148a09003c100c0003000009090040040083c86541803800c0c500e07100e540b0044098480d402120f46c041441c207500101c0318001e02d150350341e05180743d00d404940e0f0600b030b80140b040c102c00720080031980000602c5100c0c5551440c040c0f0060440c0c2c0e042442c2109100000320b882e180038840c1070001c3c06807101000781c119807222442c880581d03142810490440240300b0000303e250100d0070520085114107206001c0c10030741c5c40940b180114034401d00e1084180b544105e91450348808000000c9500d424050000002d0511482400070503420005c00541075802540c0c00c880 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 964276133 1250 964274883 964274891
    0x16080303090d0e090a0e100207080c01061a0307140717093606130501080f100b0904060207060b09010909050118020307030201210f0605130606081807050d06 69
    0x1a400e0a101001c248039150810140d0103d1000110ba0184801880f9098040c1d03141b420b03030071800c3c003070255241008020b401155110382e1443e020040d42c2041489222a40c60a1404955201802c001c0c5204070902c030103803401d5644040049a503860a62443c200c011b4045c4081c2000070f5080c000001200186000b207521040d102040c8140600c400b00680d00890700350450001c8111800c1425420000c5400d04000640c0c40070045880c0342e2185d120001d2451904000259104000c5510320708214000c00381c07050034003102d103810180c400301c5101c1c40d4048108408900054455070007407000c0744c8a507001040154045001442e079050036881899080c4e1524503440401500b8403d10010b02c804200500c080b0500750003090b6a0742c100c1c00001e061020b035050982c5210303102001e002d90000d80c0b0101780641082c00303403960050415441614011030206030102406446c500030f440a865840d61142c0c0d05540e0070030b40041400001801ea449802a2200030805440d40d00e02403220314002c3c00089 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 964277383 1250 964276133 964276141
    0x60506040315290d050a0c1d0708040b01260f0606010e0306010b03010608091005160801060f020d030b12030d0b0f010819024009090809040e16080303 66
    0x905440800d0b920f0194012580d80d032009003150348610001c000400c0e20408007101551420524000303500310080c06414194400040c898485d54507862030403459070580700f55403504003007039a250b14155802480088040010f01004e040341803000f80800e481c02031300c404101111500b90412091146250f040e4021070100011940c1044580f820010300341c0041a4541c03400e04480207e00040c0a16001c00039480d003c103000350b00c100b00801819103c14010042030420981d05003842c04008844000f1442c0000000383e0103020b42402c00328614a41c000d410007000d8a01d0840003400025480c540c4540d2800e00d000d01420b0030005848075500101c4001400500c01c0204040034051a13103060400080408000b043c80d200401424510072080c400340e260145820b101071034155088440d641c100c1540050120800342d4004012004c0e405081d000b1455140c9956805070350341c080014105e5003040000f041142040e5000d81007400303880050b00d0455000498000c414407140e8842c00380350740301000340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 964278633 1250 964277383 964277423
    0xb010510050d05180706110307080f0405061c0b010f0c0b0403050c070609210c0e090a060c0c0308150604290a05180907080a05041a0c0d0e030708120a0605060403 71
    0x210380a0211b9040c08201c200e00d010002c0c1c0d0ba0301c6421401080301f00046004186290b0300001d450180400819098403a51807164003261049030002807a01c660400098108950103010220942e20456880f1540318186450f4000c203080080c0c0110200700040000600c02c0c0720070b00c11000504240d85d00c8a0070b8034945010101c0b40074030125144030710291002400c001035160681e0008a07124480d072080f0540d42c1d0940c1c40d06240150344041d0481d03007031018840456070b02082c0150b035a4441c3d21519003980350030205030031410b00e8400352904548100700921055218400c404d10074000c120800d813000103455411800380d00104124408101d0101c0c4003050610840351440484030165400205850980c82c020301418025005019040e40c0704c010400f0300c201d40804a585030140c002c039051908146408885661041184400e02480d280e01d00059032000310403100d0312508488900d007450006001c0c8680b599015240e140c07403c0c3d580e04002400e480b00f4014100440c02007403281d4004524083d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 964279883 1250 964278633 964278643
    0x90608011a19030f020301030b061e21010b0409051e0607050409020703050c0a0c1401091a131205100f0b03120313140a0203010b0d0b010510050d0518 66
    0x280700d100d030300c489140034008818400e4030700c041c4060706640e00310030060200303400925211101a10450002002205100d044000140585401c0e18080208074008803862142d2100c03124203a0311868000c0300d440c1c00c540c12074055821409440c0002610281000010200d440030f600c111101d421840c00394250f254201d4a440350030941c03c020b09031515180000038524483c601880c503026501003040c2003030500c100c0503220340b40010400c132485245113042420100c8810b00c65008034034845c0320300c21100d5109500401c21070745501c610000508054404c0c59894008110f031580c15950508006210161070428070501405500a4600c5082d18500c0100340d0b00b40d2658189443d08000c1c0104440d10000340c2d00a82c500d5030281d485c0c581c0c07640c0e1108003d0021414001d0003842c456903540401c11004200842c00c941700320020031040601c84180141c248003408003a1844424030b00400c124203142d083c4481c011910328102e8900400d0816510440303105540302c0340d24060200c201e90002d042005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 964281133 1250 964279883 964279889
    0x106030506150a0311010c0f060f05060f030106031104020903011104060c0519030e150c030a02010b04050703050c041203170a0b0a08071a0f0705030424140d0b010210050709060801 79
    0x10f56a00301d90308544402000b504085002070401c10450500360074840300484006403076601202c00e1000d011003494400140106883d041d00c141007080802000346014420201100d502100418034000c1c0041044003e4202c4036400307825548070502421819801c80040003d02841e0300d403098000c0060400368a071140032030690b89030324610161940441e4000241100c1801c00b1242035141e000203900701400303805600406102440040b584c29059030b0190410f51700204203850420460b500d090045003981c0303007030f02c00d02d00010040205002c04944c01c049007a0b4107000381170407645038100c6400944001021618065207a039030301000c1031240340112021004098240003002c1c064145180c2c3d0010304550030100d804c0710300c0091000c211140c4079003aaa105c0350007800f035030f17241e03951090b140c61300d80c4615001e02d00303c203031110001034114050396100c003400da500c1740c0702400c01d1040d01880005000e4540454150301c106401300e03901d0314a0b80142480303074040c0d98403900c4403031130941c02800307415040e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 964282383 1250 964281133 964281139
    0x60f030515010801170106030506010b0a020f12071b03020603040c29091e0d120207150905100c06050405030a11010506130527030307111b01120e010603050615 70
    0x1e0418005680d000c0d44007070640382c0c0b8103005804080a403403601e0050520b588020130317074081d00000144094244000c0c160118094099500030212854041e071502d0920141040911090010340b002c684100480000c4080e00c04c00e0060482d2681c0000c2c42517002110300315041072520405200b4500a41032005018195151041c40440780c50f481e80070500520740ca0b24050415a004014038103400065007400400c0504009424049410003011200c141115000984542840020400260704181f00c214010713940d84543c0c03905103403c0003554800c000320707034041041d07000050001c00d1880c840c10b409144500011540c482011001506d9140402d800100f6a4500000c110b0151105c0310000484d4400450011302c6030b442d000c0e00c81560714010032015403419884801c883d40c0a001000b54012811a218a46200e040c80e01c019541c05125200806005050540c0e0b96594043c60b103041c02c0d200da020021400f000e40e15a410f00b1110300781d1040c2e641c0d42c4224240304403280c0607e800e60440e0820307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 964283633 1250 964282383 964282411
    0x41806050f0910060e13050f04031e05090907030e0d0903030f0e0d1e08030901050405010b0609060a200d0206010e0f040818061204050606030f0f1002071506060f0305 73
    0x2804030381440c0e50f00e80715200034803110714504d02e8241c1e100000c1d520102c0100c00104910704007225184040541100c00308c01046600344181d444106000b00c1424042c034507500d1a14222a00c410f004a12a01400341c00915884080f400d400c01c00034001e2401d4400703243e443c03289082c82c50800a000191008408043c89480c4502c103016464800c0c0d02450a41c002210840c00c0307402c113001c01281018981c000c2e040d072801004bc40348030001074001340d00841c0240024040415103804003c0359200760191943d2084003007203210f00b0f840c0200b120000411141f040f1b13224102003d495142440c032440240c4006820920040c01174222080d40c3e80c0e006086c1e9031702540d80f4505961400b02910540144810074040c0903c01115907860401b11661a502c0b4850601c280c181072400c16a11201650124400e02404802004440c00000c0c0b9501c100c020800400c804050103200e4002980a1607054482c114041a12100c421045c06680020701e840d0ba20a244210341c0c1e1401800c81e01c0c0035041007501d21701 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 964284883 1250 964283633 964283641
    0x5010e060a06080108341205070609050d0f020d080d140108030414010c0516090c0201180506011a09041104080601060c20040f0903030c030c08010e130206041806050f09 74
    0x400180c0240e010365000320741c0146d01d800b4002240d18800c1424580030300900500120b600d040a8201485991181048030301d02c681710308046c0d070310003036500640c3d0b080f4040035465004078520240102490740040d004500c086400c1c1c5402c060f5900c00b0410410540d1112480b034421401165200d00510b4a4400b55042906000035a20422660030b056410800d242c5044c1003848070502030080110549400d89a025079501160405030505508201c055460f001b1682d01000c410f04640c00d18a034810050006c0c0d07070a08000f8000051200165410110f043c0020701c11070315640715500044c0c0d8008810798440b46001d02e00e92811505801400802254a509200203506805100c0800c08025004000c0700c01810201d00113208a8506505035030800710000d041c160954400e00b55018940d8042c07150551500c4180c83e0104203100f8dc104080c20103001a403005800f100d1040d88a10060081d85890b6407004e035201c144804072040c07166980c0d9447d007000549130401d060104180265010407003450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 964286133 1250 964284883 964284899
    0x1030809030f0c0a0b0c161404060801090209041b0b0c070f050d05030a05031519050319050a0206030402210c1f1d21011e050c0f0a0c0605010e060a060801 68
    0x313030500c290b044000c004204520404000c3c0485094580e25880010640c0d5131415041c3c00ca0b0008006240210325110700410701e443c060140180c5142c0203410164a511075580340c902c90050070809404694040801081d5522400001c3c070402558500805019081c1006050856441c0e4002d912900000031007000060b400300c292042c12071a41810742d1240e0b21043d11030516509403d84540c000018940064002c42405400061b5203041c8c0450b4540d111054800300740d800300d054064401d40c454803541005241500c01140e0080c070161000d854621000120506603400c200c030505035130003040081d0b0711424010410410080030041d607556030940a00c014140d100d2030f0381c2d44000303405200b17070860b21901c60301041c5118085c50010a07140c417418110150083c00e84080200101c0d01000300b520305800b403806030500070390001041c82d1410403107a29842e4207070300004881d0144007400710a070010814500c02d050007810b84448444c1c0790b01d0400304100c48100c0f59080300c004c0c0404040180004c030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 964287383 1250 964286133 964286149
    0x3060f0c1e1e0f02070e06011202030c073002060601121d030307020106050906100206070c150504200301050420060c0f01021c051506071a01030809030f0c 68
    0x340c40607204981000304060880b80c6a000201c0da01c0c5208805a4070206075500c101d00010003c40d030350a80303030104e4460a2041d810b88058491500280d01c007004185440001c0e401580c11500f03034514189801002d0352031000480c64550b00c4400300c00764503251486450034003c0801e10610b2840609040c1c0340c6500068461000e00c0b078114150750381d580242c0700c6203d20322101c120007a6428200c3c0d880c0e20381950024081c00050051500528850010a415051540b04602d10300b245401411031680c0c0d807001103d12201040c1c0a45e0b00c2d0030f0600703031600b04010f1882114021401286154600c521441e50000f80d49030a10784240240c0c0f500c0c0800c40490160072400d14112190001c0424101c0311100144290013400034541060103144000c920008c0151b0003851080e014006c01000342503450415001c0345c5044950808402d404c4241c0920791800c0030040500d01e109002d90b1056940f160385406500e14240c00c202c9d08070340000b9140c959494104418611403486100802e400c400c0d0368040f07403c030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 964288633 1250 964287383 964287407
    0xd1101050f011a0d14370c1b0807110913081c020d050f060907050306060a051b01140a290409020d08071a151306081603060f0c 56
    0x106160f600c1a40d0348030215011244000c00004041c003180c29001269914903406031104640311200001c1104540b10341c04054415822004003205001c070458040405003411081c0d001c1088030000300105905948112020030a00032481a9180c4045242032190b0001d4405081e1103407000700b08004130349140c400304c8611143d000002548034031603084600c0c111942040340f1140907001150144003107030380758041c9124880240908030390b41c81d45401c3c4002c6d180e040d200343d000150708000144d040c1c104071004020714840c80c80d04038a007940b1110b00704000c501007180c0c034441d41d45451408141d07544c40c4200795000b02c5240e00401c400001c0ca6407183d00b0700039002d001140b005120380c00c20b00035940c1c0da120b80a41ca801514034810300080d860004001c0e4014030007102e0611a61803580b010300c01600d642481000d0bd040300c034880440c40c100b003050042c104210300a42c0703525607002244154092040001c5400802c0031b4811342c80c19441e10001ba114141c4002c6202c514000d0318030302d0303280e020504c0012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 964289883 1250 964288633 964288649
    0x207051e0f0109090e030c01110c0703110a050402040810050114010c1b0b13060807090312080a0914030d060506070b130501020c15091b010509011218050d1101050f01 73
    0x1034035281c00d005869001e59035002410491819245080314040400144069042c6a000300450b824003100003d03079001d1014107007955844510144002040203405010307504004108805035995074001a00343da0043e0019035082d004501365170b0800d40d183c058580901140d800c0d03040981c0c01e0b83c000034280202480080c0140120743c548030030491070340340709101074043c107015150b580040d020611403000581c03280400042007040040d0007940b02c0d96107007040da6440400342810f4907007610104c0c1c00d084050500d03444507030348844090006845000c02401d071841c403c0510340303408101442c3d1044682c5948a64010042081000c0000d0390000640e60b01800d4040903002d14001c030f0406600a005207011050741e40310701d44801506200746000e251146504e40c0440c0e2103042c5640c861012040c24200c080c0c085081400069150b40c0240040340d12407040402c0060100b0000701420300d504411b46c01030b2140c1d000140d203011141e07030110012200014002c024001410007518041e9040414450004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 964291133 1250 964289883 964289899
    0x405120f04050d03180b0909010b2a0f12070b0604110705030406051b210901030e07030c08060c1804020a0e03010f060e0a06050d38070207051e 63
    0x2240c01440c0d00741c038042e0030003070f100d501904460715000d07000c0c00780044d48440c56944204005244078440c2c08580000401a1801050380d1030200800341d6a044070b00d40c2140c402c09505104908130441c0d030b005285465460041c100311030104851801d04003804440a4a10800c024041c0455407244040e0b421100c15200080c2240c0740d940d0a003618001c810000304035010000d0001030455010380900700b8101889000c4010085410704030341e413031004010510003869034004002400382c0290180000701e070103040110320103000c107200500b4504650801c0703c3c41c8820140074403c10f1001c01003c0c2d0300c0a1450303146450140e0f21200c05002e206050045440f603500040c2868003580b20744411116910040d00a0046c1740c022180383c0c028101da80100020f809012001956440c03441c0074000407142c0142034200c0024007a00d03001400311a006254070381603110744c2e19411504001d440b0258464401c59000e0f55030401c5c407002170a000041d44064803a000308070590181c0840c031000c0d185926070031512a5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 964292383 1250 964291133 964291147
    0x5280c08070e0f1e10050a083409080706110d08040b0f040807060606051e040b0a050c0c031f050604060609150e031f0b090106050415020a020d060e010b0306040512 72
    0x204003446242d0b460f030b0170410306048105141d82050280000c0d500c980c698407100c0e03461710085001140440c4101140c11003841c0a0b02420040c1d000d50f0340040050714001ea1040e4603104210726211060740914001165044a040c40880038808001c00d4800f80c0b8103003501341050f03200c41044100c00703003040c2c4007060440b01140c2006450350803100c00ca07910420501007945c4d00c200103841600034101c0200d009000840d000c1c41e405003081124151085104460b0a00d807103c841221280c0208055900d6840745484c5050b15035410040e03011101203554210000607003802051050f10400b41c495400b49060100c00c0c000243c100d1003110a07114616204945c001020f80211601c007504c0384a240c140c043d00402410386100f0b480140008500c4050600c4140d84201c240060320100340310b0070b8000351050201388540c05002d13001e00c111100600c100c51084000d40c0010b02c0300c654031711040b00d0281da10748043c50510820b0061031b01480b4124041c009030302c0d041e01c0ba152100101c00e00c2c0005007800280c030b6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 964293633 1250 964292383 964292419
    0x40b07030e010612051005010e01060c0516141903030e0108041509050607090f050a061b05070603140711151b0d020408010b09010605070605280c08070e0f 68
    0x701e088520448000e0242c0c07580d80c24004050900031314141d81c03900800c0402c550302e60a0380640d60403110400c180b82c00607813911100303c03501036044a0440d0980207031110700441c511000001005002000d012109c4007050a0800c1a244d0700380504c999275003039020040000c40c0c9c01c48090444c0c0503003824503030300903603c500e0400d0380140c0079801042c00302d142c10300300c801348840003942c18400c5043e80c4450342e400b912088c0101c40180c0910410740d1014060900b4003419204460580b044000300030b402400c1b0005985507410030003541c10807400666034080003035580182000450300001c0f01d04101e4880101c2c83e05582d10b07111104c07100701420b80315601040310403941d07400340c038189842074076050380302c1008956503400796002c4d10550b4525070034a212030500f4640010894102ca049842e03081c0b6100c00e030f5840e0009004001c00b40b02e180c0c01043c102940440200d42d100481d441c4030b000000b403400d0050b2025010304409840c0c0010030214000f8020382c0c3d140c0303a140070f0318030f0021507500aa4018000c03030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 964294883 1250 964293633 964293641
    0xf0a021912060605040b01031503020f011e0c0606050a06080f06060c0a05011b2f150c090301140c0f0309120a05030106090b091e010210060803090f041103040b0703 72
    0x4010415010a001c07a014480d183d80048250341084805000d043c060000450a0300c5482c0d00b00d8110517000181040186000d0a2034015030f541810700341d00d1f000f01d01408400c2c00174010707400004904180c42c4481000854807690020382070490741d0040700390500000a050740001002200310389100c001155041c0c0c0c442098801c01804081201c1c40a043c600d8246d018286506002c4020104400740700d6096000f070303c55284000e500700800401207903c0115105c04031200054040c5c0d4080d44003a4410104038600395407040110990155941250070300789400c4030010b00036500100408018002c22408030780480d512510344001c10380c1c4035200c04150904054010381e000e5501c5000003000324400e60844080c604a695545494003c91717a41c5c58220224031a080b4990b80c8400c543d840820210800d801c1713000e10039410f204a404803044140c150080345c0c0ca07500700c0c074041e070b0010031a41d0280c640751600030114002900e013071110920b18042c42310b65000c00b4000600700041c99000500040c072a900c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 964296133 1250 964294883 964294889
    0x50a0e01090903091e05041a010c08210f04150501061b06020405030105010f1502070305100c021504030207150e030a080319090c0609080a0507051509060d15080f0a0219 74
    0x5030031040446403048008101142c1e02c00c06020b1424121300c41980011034003231058602041c4c680c10002c2c2180d0351414115800017540e150300300d101c110380c0b0220034604120b1a00c109140300a18149043c41c2c2400300450514010549029080c90010303c95240e02a24100807240310000c01a81400d0501c0c1c00f8020b0300503600003035010741c81c2c0400091695111080a03007190803105880c0011100500d0407a00d8000034000a4416072041800012945d4140c0c40440c14070448d1041c3d506400b100c049020807072509480a50042c0c0c480502400b0305885414100340c101c086060003805800300e440442d4561703000c250058111003001c40003d0706040006102c1c0c0050030403080400c000120b074502801c401c2168041c100014080301404031303089500103010611b09030004018004c01d4908410400c00076894101c102c4501070521942c0800d80b140300c09404101101c100100e01456400b2581d81c803d91280c0c030124190740644a40020721001050320f00d00540c054485103800c0514155a10100712164 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 964297383 1250 964296133 964296149
    0x605223314040201030605150405150d0f0504120201150308210406062405030a05040c050d080c120412060c020a0c03050109021008090c09040f12090f050a0e0109090309 74
    0x40208101d80c826500a100714400d0700c0c100101c1d80c4900c140154030b66180c5040060000800c428060761a011121038022080d410400b85006241100581174030900c5504503203031030b107400a100c10041182001800100710344000c01829000c40d0402651100c1e41c4005018410005030f040b0480f2210180700078030800b080003c4685040c18a0a040140705030301c9111319403010301420494000040005c50401801e580c1d402c0e0540d00c440881d00c00505000e407040720707183e4104000103984c1c1c4462030004402400340d048581c031111001030360f5080c1034400c801e80042200400040c89010920190a40308603001078002a4840c181042603207000401c5c000548011203541d400400c00105400c682c0f070791442510b140c00c4681c0400d5003941d070107100b9540c514540d0040c5044452504001d15150b52040c0a039500d103c07014829102ca0301c00d04041481500010800c80040c4203d1116801d071400a001c00d0702e0515095207002c10083c0c4000c8180501030f4180e0f1510000c0c0185441140042d018081c0b41c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 964298633 1250 964297383 964297391
    0x509010516061e060602010605060d0f0b03120d0f0603050a080a0314190e060105101d09011508011403030d0902180106030204050f0126040c1206052233 67
    0x102c8107420a081400d4032000351242401320105000b0300c1030003000c080355406002c0608095400100002070301841c1c00740000c0b9551190410250f0b40c040141d0400e1080b4407803056510020f140244050b54190014902d11906145d000c10010310b00007140c502c1039400c0000c9a0b258641c0d0072044002d000c4000c3c401211540407024400b8246204204054603107070348004100315000540d5883c3c41360f40910815501600481000b40c94502448501c4414041e502c200d5403c5100c5000082741e1100030307017080300010041e01d815100d80760444803c03400b400c04403049402003071020002942d2446407201e41144151260710721011034a03146840100c080e4014410640da603154407008009400c14410071f03100b1500e0f1040300748030354020040c4060014120f0316452042504901914000c1c901400440c0e0b15504100300203400e100c011081210188115804640c3d4100303152070000301244c2050000340c2d11034810520000480a40200300c0c0c406024102500c90005040001040c41c424806000403d041c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 964299883 1250 964298633 964298651
    0x30b07030515010f0905010f170408040f0b13150306320d0f080f07020307030f05010b0a0b091026100b0406141e070503091807050901051606 62
    0x680041c0c2c03150202e0200c200d054060300340119110718800304038034082001100184903e500c100c2500030002e140d800c0982d24035000310441a0a020112019500e00501007428014550402100302c010880c480307089007020120001500c580303900348601e100d0000c40b250f0340284240a508424001c24056100207130a0344c0c0c0400408182c00281980031500c06080f0101c41d80c2d1074048080442c40c0e41020130400303003c0b8942e031040f11561014000351900c070340507c042c00041e9400c21541e400ba40c8210740c0ca614400c02c40c82c1150139038080c2c1d600c9600c144014442880074151070001e440c0701c0b034006c5030451190910f104007625065003400104841d07001120440d800c88a1014045020301079004034041c041d903540d981d088180c090b90041c03100140d541070701403854040803c0030341010a100c00034401a82e0088402110540c444101250582c20116441c403483c03031300029240ba1842500f09074041880c014400030101d100e0034a00c50706003c00800c05070040246000c0b071042050b0b00c003408200520f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 964301133 1250 964299883 964299887
    0x150504051302510307020d08060a060e01180b0f070b0c030717040302031207081f080303010515130b0c1e0a03050c0a06060b0c070e1e060a030b07 64
    0x4010380c082c1d02900150149160b0043c03984001034840c00d16044642941101488414007102260808454051076504003c02003804000942c0540c5085d00200248550002d02800f070b0100146500e01c41c410740d84080199903041104003ea03c00c00b4a8004030441e40d6043d940c4441c8080d07000441d5001002c078803440d624060701e00030541240a40d030800c0b555503c1034401c04081c8401c45038500000d00c040c400480301c0000080c0300f0340140c881d0064a090070030030302004081c024104c0b11000003c188005004580c4da20144628800f0b01e5911004200ca00f4428041c0d41d03440103210b40c50140d0b8619201c0c800c00c058040607182d45400d81160254500c0c0c1d0b540800e120307908680e102c030b96140101044242d44503a045007580c0081c05a502911b04100c50340c80588003034101881d040100e0007407121800c00036015100b507034058141d400486442e80c03444518140341800300e0700708031554401201405003260701101d0004481038214450b800d0360303030303440082043d5040075440104091070f03c00038042116 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 964302383 1250 964301133 964301161
    0xf0803180a0c090605030c0f0d15050726072a0512121f1814040f050616050409090204060518041e030f08040606051816020c06040915050405 62
    0xd9107940e050000586845c00c26444400031054103074003030100c000c640110b003004400e03048441c0c01540707410541c8000c1c401800030b80b0340c1140e018000800082508268a070300d54803600c000315044000c10b4003490000b201405078a1004000c40c1c081200b1309080ca02c403a510b4002104a80e481002d4501102105022806503002545030601c1c0d5600303c1e00041d0400094000e082d030a00008042ca40401d280c50844140048034400080038a0b890f86900c10b142d04882c51001e004500c203400c00912412241407290401b03d014100c0f01e1003034078151454040c00e17441410b4400352a04d08800207000f103400d01c002001400340d944465003045c094401150202511841c091042e40100044100b29121854402c598490003400a003ca00f001000c600490712860303070141e00c103100b0700300020800d403280c000480c00211381855000c4441da000800c6800904c20303070680110360440c0000c0800c02410340c00580c04c2e008074025500d40d0355440114141042e0a400c0c0301c0018103005e00100302c0381c18910790500c011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 964303633 1250 964302383 964302389
    0x70506010f0801110f131d06041d031b0307020a0b0a140405180403030b1302090102010b0603090c1909020307050703031d0d110f011b11010501030f0803180a0c 70
    0x101c01c107850004004030180610b40001040c00c284071302e40b43da481140c01054010400e440141000d580300402c494040d40ca507440e4041c1c440c180d02816140c003008210030b803500c4410020340e2643c2d018507008007140000540e0f0710f4402003000e0386006000c0340f07443d6146020782074000c0d501c400d49080010b008564207000348101070b8990346544179004501500181440340344a55034005200c1e8201200303000701007550540040c031074540891002080000907150000500c4180b1285500084500c80d640e024440d03651220000c1d103130542140b134181c10140d2203800c1d80d01c00c03a0280d071060f0b070301400e01c803240c0c5030410141488980031512403c0003c4001c00a4010000882c007180c0340c0040043c00140c3c940c90240ba118203080101841d0344800340480d050740c010a5205491b2050081801500070280264001c0c0140c4901d09602049030100081070130144250030510750345484018004506c00150600c07010383c00c9600c080c0d490300c03602c049070820305d100b50651425009919440c2c1c2000152401c07107080f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 964304883 1250 964303633 964303649
    0x80c060c0a0903060f0e011a040c0801030f0b0912071b08011b030c03090f05100b0901030b0703020901051908010e16020604060e0102070807060509072313060b07050601 74
    0x4195a034010880003481104000310104610308810400588280c000043c869000b40b40854248100340c000707401e480707141c200d81450f810455811041810b2901c262480c1400303601e0300540652540d02c0c6c2c0300402001c610003030940598680001c6202e40d003007003031040241040e41c029607281e0700c07401e0a00201c1520109013200e03c07a58100092030032814021824045800164031602509000d010390081a1110000003456210100c0c2c201050705004c020440e81e0080c400b4000c9017200b03000310401c55445a0407548600c52031401400420542d00683e03a110402c1c0c00d0050380c1c0ea2455005031014000e01c1044e42c540d40030648140c900513031144155041700d0111165041b1511442140c81e2004070305600480140d1142000a0201b4a1500111070384810107000603d402c0b1540c8803c0303001c1d840303c0da0954110f0380301c0c410300840386020041034004280001c1000d2441030380b1059450b20b160088941c034070540001126002c0c400540d44050000c0050f5800c0701c1c0d9491716403034240c2e11441c007481501c0d9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 964306133 1250 964304883 964304893
    0x509010608220510060e0105090603071206112b0f02160201120e030c0f0f010510090b151603030509070608160908071409090a1e031b080c 61
    0x18145016000d0786000303241026541d64240c1998002400b51000500c0542d002e1041c000c244c1c1660865111709006001c03070300304d845090740c1054144020304e035015044500039445a0f004100758080d207105800415404800072039040c4061030070203000d008820181c00700c141d0704101120b480a881c8120100e030010b4000c2400f02d000c0359118101240940d00352072001c082d128040310019032280c0004100c03907544000016948400a09052640c1c00c01001c0c0501a4002c6a800c0c0c0207000030051744820042040c000d002d20703d04032410030034036141c0d0b202d140c0c1d05640703506c001030882d03443c0a000003040e003000f2020781c0c84401c0800030810100c2c640605070f0102c1c5c905801f06500782c2010500c002035802e1600c400c0403586070f4200100c01103948200207400c010340101c01040b00803052008400600803035030a4240d80d070188040020344d03040a8031008459004c044e51380300140b5103028588178014035912a950200075800c0075510410381030340703a07815890080502c0d0200494540540a00500d14040f0741e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 964307383 1250 964306133 964306139
    0xd0c09031b0f060e0d050607020f061303020309060901050c060702061b031e061216050405010e0f07110a0b18010b0603071d15121501030603150216020a0b0301050901 73
    0x3020408090050b01c0e06181c90301c10030b00c0200c1c0101404420000e0140009440c9400c0e5151242030040c259241001038118440b140164042006001e8000b5100350031408014025a1701950b24800e076901c0300d009080125220499038050300075034076210345101c281e41e501d16081000a4441d1000c485105500d103400d10040051a1507506692240004200a8041c400d00700c8022504190040c80240d200c400b252210401003020300c42a12007102c901810ba890314141070411066840582081c4035031000801000420384100048079004186400c1176003c0108540c1d00c036042c201c280c2c4014107560320714418007054145d080c00e90a8152400130081208540c10010021079100030b07030300790b4001740216104a4440710341e00002030295000805d40c0040c038031b55410180c0c103a0403074020500c00100c05402c100c070544034801e24000c103c40c00d03e01040003908568a0340ca5503413500c00d52880c0b01e58049441d480e00c155040105146540080900c030200781e95141300503c0398024040c3d1030195400c90000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 964308633 1250 964307383 964307423
    0xc0507020d0b04020d02151e0901020c15130f080c03070e01060e03010207120c03120b281a0d0606020a080714070302090a27030906080c0d0c0903 64
    0x14522280d802484126221000d031907180c0e00b940003400513640300040a034141c0050351020013981d481a1001c050341d40f2661116405e007100350440f8034014080d0720400c00750420713aa000c5001100c2c41c40480f113003d14031449860340b2070b9034040d907800300c5070840c00400c0200d032036444d00e40704070111400c1d0800c40d081482c60109050b2a00c07580d104411440c444800188607160058082461016001c0d00060800c0ca80743c84140041c0103100920380855102090a01803550050b92890408000d1401740990003840012a0602000d81408544040203040061311f6481800020b401440b01a58003100b07800b9040c00031804ea4020402854001c0c03400307000041903070000c1082040c080d00008540d080240d1511a480401002c5142c0101401022004230040e51840755090250f0a8010000750180c90355030000045103240d4185050650440a400c001940c441d41d1a030036903807249000c04490300c4110701d10301c807401098403000700541041400070050b40d1044c01901280d020f5003114221541150b00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 964309883 1250 964308633 964308637
    0xa03150f0e13110301050f01050f03010e030d0b010302040329010f05031207020d02090a0614010e03060a090c0312030507080606031005091003060626120d051008030c0d030c05 77
    0x7403101c80711021000030701007042662406455030300031030f404001d294854002a00715101103401c941c0440c609001400035080c03030f103245265104190001c102005100810716500d00a0f01240c0d00c903907403600b1701c00300543d106e60190b400070750744800c1c9411501540f040c158950345d05404001002c86132000002044a4000a41c030112030f03024016010701c141c01c0baa000300c0c030351050b04184d0300694000510300058803a03c640c1c6203c0d220030701c0700085090400c40100010151100d5250410003e610000400e03600481c0154205100f8900010304808034a02803c41c51110703807000d84890044000400c0c01501a0052446000c40d0b131f40c1c8007016600c03402000413500003904d4004066408100500c49400c10001c4140c11185d03a100d62160070b81c1c1da0760391006a40c00c0fa00201d00b8020720b03d001c4224116102e80c0030007d0a400d601401806841e00c56040990041d50248600c2585848c00f01d020005004140310140003400305580e911442441d03c6940e50000c1040c400000b803a000c4851082886441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 964311133 1250 964309883 964309889
    0x402100e041d190b0601081308120103060c1103030606030a090803160e0a060206060405071209050715140d090204020717030603070807080d0e1504151407020d06020a140a03150f 78
    0x1d04c0751001e0f12000011100700d10020081000d543d0485c3d288008130750303a04060304151490b281408050740c1185001801e44024107031410512a610600c0f01d05074201005031703030340041c06a504540765500d440e002c40140404203005040c41c1d40c0003052200006080380302c0da2090105480f44d010700507010082c06854000c620980380141c2149001c41c51078031b0305401c01c6412810341d03c0c01700800282651100122138081c0c000b166594040401008032101c411a05100d40800d400d021a114618640e601468450b801c00113150035605c404000440d52a41c1c1a5403255401c4102c880103129980520443c6034819501180700344074070980011120800540710060703940305406010180c0880906480424590300b0700c5a00c4008000c07070001d1900c002024100030f104681200e02c9500c00a00081c2c840902d030300207841d5013036042000b000581c854080c0503800303e43c081d40040e541c0e441070904a561506603c6c1442c8031000006480c5103144d07041d04007025022607080c0000805986044100344080300748 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 964312383 1250 964311133 964311143
    0xd12031116200306010f060206090c03060415090b010f170109030509120111162f220515040605030102032509030c06090e1e0402100e041d19 62
    0x2541c000542e00c001c0c4496a818210308000310300080c0030000c0e040c00001d805c000c1d52801e104808000e000d80c100032954000c05010054205502075202207a06d41c3c2000b040949000c1007883c07040903803207040c0d0003010841e4001c119240d16503108c0511400d0001603100340d41e4510200d1080c54000c0c1c00c184200c0041541c180c0f104c1d4900031100003840304071000b00d1032100d4255680e611040300010404010941c0f40e91b000038815010740e4502d03150701401c1d10f076640d516024075111704429100e170b0081c000012900003100d0141220204030034115038403010b410082505801c00c0240001c601c0c0203c00c1c0090510122024000039480d0000e240c00c0340021540c1c0b0a612481900002140d09500107520b13070074915142c000000da0300ca0b01c803601148159070200300041c0c0300c02c204204060b0b5242c002c1e42c00c000d481e00040302090b031301816414072030030180000e8450f40c0b10740314207a1841d00400001410320000340c8284020b204802c03031004402541c1c031056149010304121a070102e504090030b40380c2d00e6448 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 964313633 1250 964312383 964312417
    0x80316031d031b061b06060307060f020d050711030a1202010b040b01080a0c0e030a0b1608040b0412030f11040e0105010908060a09080d0e0d02070b040f21020d120311 73
    0xf00401068600c1e0300f09003a4210b032040104191170451140c2040c0754480c490000c04180c109442492710b8202d0f50b0b0700c4a800c0102c00098499099404156804804800d1030304685030905801c0c01c00085522580341541403103500c0300d84003003041000107140941d0454008202000e0804144401d4450080c025800a280303080012111030055000030f00c0c558a92400f42d200505810120b450074a04201c2a60304a107040c0400c8501109002490080d90305490007204a0425aa41303214078900508010003d03503820161800380352099120078203113001c0000a100501d02814818443c1c1e0041c0a40c800381c1046900104095018544001c1220b6407140284000d035280b2071031000805d50010700f19800281041442158409401154640c04449000d041d5006e101000a880c0c9a00ca620100c00c1c000280003c0001140020b00c1c4001c0b11941c1c4800400d4030305031740e01010040c1051100075400000d588060062095054214003000b100d038900304484040c4d403034825151701403100000288000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 964314883 1250 964313633 964313653
    0xc1a040b2d0309010f020711010c0515010b0c0c0f0d02100909140114040c0f030c020715210b0a2304050c30060d0c080316031d03 57
    0x41100141400c0e03504100d00d9503001907980044500350103034428445008008028401e560b0020310039004004080c1c20304625040c0036940360041d06624584450511080d102c40200b07000050003125809402c01e4048209c2d50303100c541c3d8a40d103400800c4819280d200d004107034022401c012040000e00d41005280d601c0c000c21590030015550702c1104068208101214005044041401010000500030080031a150b041a2022040003000300005204505061221462507001003241c284442d042c44d01140138030070000140d281040c02da12140010080500b10b03064558003450340703d49400c5680c4904c000303101c070091100541d480079504c558820380f4141c0c01c00c140000081041d042113a80b680071700d890000b0710001401c0f108101c032600340d50328000a1404440520403105105080c2c6a01c070040100d0403000c0d5030400400041c040d41c040c1844001c64003e011032191148024451101201c0d0b0700c440ba01080210082c03410411070102e030326030708958103580743d40c51400402c0d40050003c02610107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 964316133 1250 964314883 964314899
    0x70225031a070207080105151813110406170c030f0607090b0313231204140906010512070e0306180d0c030e04020406030204030c0803040302060304060203070323040c1a04 75
    0x2d090042548940c00000072048428011584200f4207100308440c41c07100401405500ca00e80b0f80d00c5542d6050702c104002c24001da0015094090790401c180c1c468210011010400404480e080604903a8188440c6840b9070390000340d41d005564140c090328070456040c0c0e01140e40720800c1e501480420b1003c0d0082c4029034000000e10340c4445043c107501e2a80c03006480f45009100852100c1000c110698003070724a20304100802d02c0c040146d15139046c035240c9000300c10420211410f1070603120342e4001e008a0360701da1144003610304038010001103294904003d2000340880c022050401d002e80a4040007491111521000b204030604c28030141c00c544c2c4c04c203001143d081080301412801d1001060f5115541d131100d00c0584080d00c401d17100140e8450550400302810b810b9a8006210740d84104070074001601c1b030100341c80d0403540c001750250316521000c00903000303008044d4107004a4210f01401c151580c140e81c01e0240140c0c0141d04074000680c1b40da16149505080d440c0401c40d51404102c2001030340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 964317383 1250 964316133 964316183
    0xd0f0f0c02032103040b0631150e090705041526010203010f180608210c030310150206090d0c02011e0302070c0609030c1208090907022503 61
    0x18801000d40b02050701400314401800c00007140d5003034001d000300c104000c0103210390051f81c111500711040c004100d0100c0500c41e81e030ba403455000b542e03d82c1e0391094010011312500f00c0c20030044504090281d09413912850120407000720b855040b0742c0708002c0c0010b4a410300e84260840404403d440409042c01d21070800c4801d5070f80d11821003011000c0b41501404038080c405140a840700d000e22998051030710001e565140031140c41c1d50b44491500c1c0c00bc01100c1d900003003410240c0017240040001403080d07020381007103020f10b040740c503460300002042200f090710546c40d410a40b9400100080d440c81c941d6000caa50300c00032544829658806141c03983d069008450b44140584145080d502c0c0d02081e04111320b050040c4c0c0d0311400030980100302c80040080800550002e45064a0300343c0d201c51454443c00040c03207030740c480c20f001c15803003002e1482406014400ca4038201406410405c1c1800c000c44025550018181100d0507000b03d120501c000d100340340c403a030084a802c0b4244038451885600404400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 964318633 1250 964317383 964317407
    0x80304060c1b0302031b1f0b010915020303060405070503040b041104020d020409062903070509060c0123090705030703120e030d02030903010c03050601050712052a0d0f0f 75
    0x4004102240c00a0b48060307000d20050318402c2e0301840d190040e103099004511002d40b032034812600035068051000040360801c550386881d41d100481c100c2c03401c10044e00c0b641815007005884501601854840580010045000d141c05130f808100f640d0f94200210303102d0200759001005140301a010901007102982c3c00c288188004100500e05200c19441030100d03072243d40000506038171044100440650b018400200b8a514038084a00003020170f52407035039200040c0701c44103004000c0f44941c00b58942e081581c59400025000704648114441c0b501c45110306c0000c90480150503400050340030710045405c1044800140c0181801c0341156030f540d41c8205541034100c200000503505140c0d80c0d90801615031868283e402855440122900341425609081581400e1505101c2407090513640403007260041a004264032510307145101e8111901c1c41051040340e0340425245905c2c04038140142250190201d060896802c2c4036040c00a444119070248001c020409441c6800030060084000f881d013 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 964319883 1250 964318633 964318637
    0x30c0201060b0c1e0303040503030103300513080f03040b1b19050c01050901092105030a1115060109030b090f0102030c22050a050103020a0314090a03140304080304060c 74
    0x1006894180980b4103400544111009611002540421260400d00fa8807200035820180d171540c07805803151340d52444103100052244402c0060004241d0707a22007501d83d001580c4c00a01d00741d01d00e0441c002c0c1690050381d560300b0007250b645800103442c5000103002c0c070366028000207507003020319000414103d81c100e40001310840c9074248402c00f28a41c103012040841c0700100d10804c0403401d42c02c0c100e01e00842264550706102c0100806002daa81042c0904201c3c0c3ca4800284903180f90100e0301e0070510030701c0d00020018400801e1040c4490b0300300400740c990b0101507007260001007001034400c00318502941c1c401e010503080d84007400403610040045602500c1c02e001c032035150003418001822a40200c400c010340c000c001c540201030140b120f040340072114094030302c0312501c2d003040c000900c00142880740a06050f40001e150743c406e030298005101c440d03810b010b2943d281c80d041c00d40c980c8400181c1c00031030000e4400101a024540c0f00401e81e4026904044a141180d40e1544c07041d0050002c2694002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 964321133 1250 964319883 964319891
    0x723070603240602010203070206071b0b04030c0f0308150102011103063705040f050403080105100201180c090501060221071e11040b0a0302151e0c030301140a030f0201030c0201 78
    0x50724540c40b0b84050700420b030650005039070b072170000c0009082c41741c00b9040f0400c2008115100e0351052109515032403840d0000d900261903211450280c8550840000061200c040c0640342c0d03041c181c102c21070501c1b90140705c600890010042c8012422180c1c20032103035140c0181480810b62a0510050240d9150b1043c2c0a00b14080c00d000030051916504121000c140c14012b00c060060f4103190003892106d507a408420b100c10b04183e680500619414010f1324064000302c018805403034403d402141440c0344039011111102c1c00d030304005520b95503c1c050b150340e40381054000640c2e1880012907103003124046801d00d8880c6d00300007070f1003140c0e804080152031490f02d46120708204074000844e0f0412500c50400c0000000310141032006450b031011000740302d5000100104056190451109580d80301408669545e91700d03041e51075110f490b070b0b10400c076540201081d111552500000118140d490040c0c03180c9180300a08208200c480c0140401816a081c2c0c0b0b0f0b0040055010341c01040c410640380c00081 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 964322383 1250 964321133 964321181
    0xd05060a18050f010203061302070f2006040f05031603030c0308040c0e070206070e0406060507020103020f04170a051009170d060e1017070e0103021509150723070603 73
    0x40d1030700602048124080c0d600005125031498580c12124094900c100d00b5422b0004688403030b0300082415401601d0b00f0091400e80c046805010302c01c20061a0080155071183d44900030000040c065010341c6010b4414030f5159500b50101590b90400c880e41942d07904000c2c40550350480780702e500588112140c1c07042904c0416100702c0030134102e11900081e0b0041c112490400c00080070001549a10390040340740c0302c0c062000590020450f0f03141038080c00c002da03171441c0c003060142c454425071340546402c01c03400b046003901550214180e08038a00400c100c8400c0c0c80d075040c841d0222251810028020107440c901041c401101c44e002d4a0038007010700d80011389940d5200d0310350a0b188121106401d00606000500022805204280e140000312004002d5103090800c61400428180000703403048a901080350a591200340071948800e4001d0290180c0361040b8207000856007007011300b160700004100c00b503806c0e00d03c00981c0116003100c480041c1841858084260020a0000155003d50780c00394440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 964323633 1250 964322383 964322393
    0x601140d0c03050f0a0c020d180503060403270810090f0501060f1a03091e03040b04180c0519054006050310030201260f040308060d05060a18 62
    0x1501c0d10400c648021a052070190400d2030700c154010140faa000c0e2030110b4403110720f6400903807028412800d08040045080c04179a480c0c12100c29030140303031b1610548080008040d0700180b41c49081c560800e030884207074440a4802d510458501955146034484680f2614018854120030302041c0106910744034003c4a8407103d013524955001021160340b00307001000a04400c40082c0000d4805801c110f04500713100c07100139210001141007a43ca00841e6001c14030218040c412603004000300900f250b40ca03940c0d034540301c90001001001080d201c1c034040c010700d0402e0080044400700c80705081c005075155040c6100b40c4460f040785a0700b00c12a20740c921107545641d03e00a00302441c0d40111407164079510060461181c402103504403004226060040c8095031202824103002d0b40d509007014036030b1044040803070110344105503030020a4a00627051040796641d5032405070103a4008e51f90b603015662a070307051080404113940000c0091740204001030100003150322450001011072a4941c80070380d0360b00c43c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 964324883 1250 964323633 964323641
    0x204090b040b150a060e13020f190f050a080f2a0d0507030b03030d11161101110106051302030a060308130e092a0102070b04081f050108060601140d 65
    0x7100e0982c031030350a00040481540003c1d0f060201103c1c1400200d0404000a01e1808a201440e006100070192058081c06940581d40380e056817582d5246c40712414130022014161036055000446c0c560007a01482c3c6200b2030466003044040e40b11242141c6469075483c080010080035030b003d5194180b18000b00c0820f07820b007516001c2ca89841d503500d6000501d80d9604941007d40312009244c0707800d0100070fa44e00c01200b9070f0880b41b9034070400220100c416070300e003019200f00d40942c2035400003240450200030f5003803910003c000c0282d80c0c0203070014084030100e007240c0ca1400344560107071003c4020350228406800659000e10803080116845689545035032058100645040d41c0042c814024003406800500c007a030300180720001080c944481e20081c001059840c08500c10294064450905590081100c41d00a04414607407076603c55440d01219100c099854048500c0c10423a440100aa0440d01a56058810b60b9000e091162200c00054030020301d05e0041c050303d8807081c030181c500307030300b603445 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 964326133 1250 964324883 964324891
    0x20315070f0801140a03030804030c05070e010923010506091f0e09090a030e09060f03070803030109110316052208060609010501111510090603050313150c0f0204090b 73
    0x1101c01180d00e201d08003418154050b04943c0400c480c41680206541d5264101c900b02c03901410b024203151070760b003000c9505179a4082c02410600c140d10300000c01c001c4c0c1644490481b152000c0c00c20202d1440c0d0700c02548003400c0c0040c001542807100040c40280b803c0e8004040d031180081690303401300e46480d05420250b03195224078001c6a40005560b4042c140060610751040b60f04010300b05a000554000d020b0007101c2e91183e00540c1043c0c000781d065200c0c40b41143c40c49000030b017114030b295030318442c641c0d40c0e50090049107069801c00c40040f45406146058a010710f807071608224941000c0f42c011112500020782c03000c0f8908080c01500d2803220031200340c102401c4014007810440c54110148407080106034042410081122440d42c14140082602d00c80580c501c0d152016517101c0c10040c081050098002603080c5151030400801c03c071001004080c0b51040b8282000c08940d6800141c2d403041d03400c008040820a40034800000074030486403080300394402400090002ea098480100f0000111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 964327383 1250 964326133 964326137
    0x20907021e061b030f19060518042901090f0212041520070b0405070801020a0903050c010809030319060b0c06062416081603091410140702031507 64
    0x8414000c540300c82c410540400c2100410f00c43c41c40c101841030a032680b074002c220141e04d280c018000d1420600c0f40c0c001100801000300002200c2c101c00d2004580c084041d40e0450340d140b2590596644c00c03101112b02d00c4c40784440a071945440e881d110302a07003c2d01c00400b004d040c40c0d03401c0280315000740303620000d03070b0080303020300241d41c2c8501e02c402600d42140c603c0c0d0b09402c0c9441c1c6000c001014030544108442000e9848109003c6d241c84a281c150f152889a40006880d5400407a201040c607511482d000203c2e80910121032800170b44c080159820003041e00c1e007402d1030b003040000031410326026031640c3e80320b00c8402c80014915a512488016900200070440103500b00b10b05000b41c83c6084c803141985082403602116100d400c60700b4500c11882521a4800031000d00b0301c41c4018000c5240c152035203c0842c0c1c3c2d01c0542500f00b4540200885038038003070850861400b0a0140441c18810b000040380ca0781c03502c07400c41c4107040c0081d0400d030f600485812645481944000e000d0803660317145580c0540300c1d036 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 964328633 1250 964327383 964327393
    0x4060801090804030c09050c04060c11031002220503030f0c0f0607050318010e03182103031614180d020a0303020c0a0b2508121e090a050a020907021e 66
    0x52400c2006812664018006d06007080280701000540308211000c840c05410716a9055a0b18642200c100300307003c982d1a810b00034030040c0c03028070350740b80c00822010080030403071030300703006142d40b0100300f22414010a60168010702c402c0d00d101401800404115180c94219000b0301007006106107000801c40b07580c070003d04040140145006440d032081d45c1e0a099038002e000403100001401e580e8090362540e0050f4800800c2c1e0752040e46c540080d0302c40c008e203d0740c2410810203040100c40f039490f4804c0c0e41d04d101600d000c0d0125071009100340025501e40000b521070a10300a4040c00701a81e88800b00015a884840c03000300c240140e5611500c18011842074002c1d1400403c40d07070400c024144a940807181c407040401c902100110045075446200c0c4900c030007942d601403c2d05011100707006281e2115844000c075402d200a04141103041081009035004c201143d42c0c0e001c400d180c40300e18001001700903502c0500520014541000c066511032258070440710009100d42180025898940040d1980d40007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 964329883 1250 964328633 964328639
    0xf08120414060c2425050a20030a14070b060d060b10030b01080c070b0a0c0c0c030c0807060c051e0f010c0e09070512010605160b07051201080f0a1104060801090804 72
    0x80444c8140d801880c940c0f01080180c0d4110000c5404000380c40041e01300035000544403501800740000813030b503407004040415034102c0d1581070f50361303544010764400c042110917011a10800d125800c40f000741d40d020208603a2034440d00e050000e8460040390032100543c40381149403250b12800c40701512b034049a900451908460400581441d5003c0c1500c648410304110340400709d180c02d06001d030000040803000446000c0210200c4685c00c440d140145168200744000040c803128811460030380f11000183c0e5422540d40400307548129144070000d007907400c2855150f6a0303050805203004007200c00010740340340c404070444080c21580c0a513804008103142607030a1255081802036242d1102450408515021150625000e8428140b0a0f54200480002e204002c1c40109550389032080e44504d10944074204480098065000382c481150003800c4e000002684c6040016140b0140302100054041600303141c07549130200f480040c21980007500d983c000200007800b44140c080250290319210388540c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 964331133 1250 964329883 964329943
    0x61c0807080a121a01020a02090a062414090a051e1f0201050c03040515040305040801022106010c0b0109110910022424031609060f08120414060c 64
    0x15901420984c0781c0390070701e101c1c82640c0000e08480c400350100c490701c445654401c10320340a0300207504060840c101c140c07510a4140300c0200b0401d03500060b80c42c1c0420b503040310382c10b18201e400307003202c200d62000c0950010082810306815a80f540b99100850a5100d0180070100e418149016041010300f07100305401021030354207200c1c440c0c000b501240318034039604290301c0e5541e0343e0750391038072104529940308045000c15000d001260000c00d0400002d54a50112109188182034040c080041134078041c07000071615032040c202e1020090784101600c42076428101c0e41c50041901c91440c10b0800e000304860095a0340e1035030803640c256a5a40200481800c01e061044902c03207001e170305014034800105000b14208000002902d800d070b1084082013030511000000d01c1c10140c11440340c04000c80315800300341c0750301ea9001642501c005924800071705907510781407581c6187c3d030400c0480e80c01061000707000c0c080c514590301703905c0d100081146041c0b00c0343c1110300b41846040c41d102ca10b501310112130f0201842c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 964332383 1250 964331133 964331141
    0xc150d0e100e010603150518060c0a09170703063810140f0d112110030503040506030702011b080604050a0b03030723161d061c0807080a12 61
    0x3902030b000b4041d00f840e503900c041c0340ea100000c0d84401140c9480008805001c080ba401c076403100110126030260030030000c42c5100e90702034004840000d401c0100030030010780c08011201c00169183c024a07400740355845000003404a070150114201d81014043c92406910707007c4039030008400440002c001d030183c00c00c485c0f50b05000201042c0101c980c4041404240386c07017900d50300007000752015030310441090107034000c0c041020740007030304030020400c0f590380542c00406110a441440c0c1d509610b890b00321120201c00c0302880014099881041709202c6030074448041c54000d0014000490740118041c040c801c490030072151440000d058600300045860a030040541160140030100070526881d00480e03107034480e040001c1c1040c1c0c4240c4a60800c2200c9200c0405110301040c140d07242c1340f9200031a520f07020364601c24864035203030303030003000358104460880383d805031000030101103c100060030012207284800d54203880d030810a10800c0041203540d001041c3c44c203201e580701107000c040e14641104039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 964333633 1250 964332383 964332401
    0x70f0602010e07290708030906010e090a140c0607080d1505011d010e041b08090607090608090a060c0905030d0804030210021615021b0f0c150d0e10 65
    0x168148a0842c0c903007000480c1c09000d03070394101c620015280d03118007202d51952205000100030240002c5840c240080000554003d44025090702d010341d0762120312000c4d0314800d075000c0900b6041880400700050f850304400701c80c1480b510550f60301744400c2001a40c6608901c0c0242c4880f0800908580803c2c0e1034480c0040c4d001c1d000009169481c10000020320000c032422070b140c2e40d0340c0c45802c08406a80601c1c031507280713204002e00500202c000754040080c043c001c0e500600200c1c510102150406070080707555841180c203981c800c0310044c50008210348010018060190170b010300350031180800d80701c0c0900c14140080d034a07141600d61600c4141450b00070158005c600b00180c0b0b0052000186c2d020401021500ba20403000d030f1034082d102c0301e01020380c55012004088980e5007101d00558541074001d00b240d6074543c011311810307620003100e072a00c802c203800c031000e03282c0c0003180d02d4402032034040203503114040007150742810a41c6c00100001115101d0070f83c80029440040031250300d210740e004075001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 964334883 1250 964333633 964333637
    0x301090f0201200d030c020a021f030b041b051c02040f060e220b010e03101508030301271b0c0c0801020f03220813050423040f110d05070f06 62
    0x880543d003079020740c48440c803102034410562a5054514014420410310507041e0300144003036903451704580442245052500c88502007030926800c41d64074a09440303551f03014409002080300c1d0594406040f94154440c41c03843e051070074800c02d460307000801480a000680b9005403e00d102c030341802c101910b0040610300e041c1c03051035103090000d000b4191040b0001c00c4901c2c402c002c20f03c05446401654a182c3c011121909441484a001585285a0000c000c180314401400400e5516140602c1d01ea1009014902445803410101015824900c0788810440000d010008440e1404041540103081c41120395001455418140082c07005e604583e900a05040000310f10300701c0e0b04001181d250000601000c05425844107201d2118440c42111035150f500030748450761032208810200b120710303103801a180214035100500360b107500c46000a807009514440b403000d0b255569a100001d01d41c412004490b02c25a10b505100c03552076541d00010310301d11032809094850f080c4000b0008440f510391007841 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 964336133 1250 964334883 964334927
    0x6050a02030c0a300b2b080d060306090302012412080304151d19020a050418141e07121211030a26010609140f0301090f0201 55
    0xd0400c03008040f00c9441025041c4403081d00041d03401404002201076503400c2152030300e003211040605940c80341c07403628400c517855020581c9920712407480e14448280000000c2c004084400401c500d000504051144c00c82d0110b4550b8036a5190b4080c2c481400c0214090703034445603010410000b18500e045a03000794010040e82624001c0401e010021a49020b00384804c000041000e005451403051a91903004206011500881c21045032031039590900b284980540c84446030a0900b1017401c0c3c0043e60010701000000d4203040400004150013080035032400b1800ba005d10004850140324400500e050f405000c0c1d00c038034a5284c88226907031105034411600111010302c0404807030144c1d4901d40f82c00c80f41b03a12100070600410f88518007401c035011001e06c4081140301206d54070608414500d03c07100c14045034030221443c1d420b03424200303009603000b0070b0840c503080c0070a55440c200007420304001405000c05420b8135000c0703404c480300710f01d09440340004219104150350b0084820321810342c40c149000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 964337383 1250 964336133 964336141
    0xd0902150403051b1311070b0906010f0605180603090102070c0b130b130e06061e03040c1401020a030302090316090f060b12161124010f0609051c0b01030b0406050a0203 74
    0x41c002e540c8682481c2c48051b0342c0c0014005407215901910840b170340c054110009810000c200c0e9031b80c0da01c00d2041540c19140b0403c0803d80521940c2503a14405c00303200b007141450704400c100503068000a2000d0a03540d420321500011801c00132541d40104900380c4025030b903554545440c20410300581290010b46d5082003001e40710701020203001d0494001c003101d244036845800015200b480b400491120300b61007801c103850451240001540164450b01c80750000750390b288000b5103030140c50141c0d0b0b030150308205c0c501c0b80441e0094004090f1400b00074161810800300f115010002500e50700056401a070351560845180510312403540544481200d490401e03085600380720400f803004002c1403078240e89a860907070690240c420a44a041200305507490394602e22071580ea03880c5040340001c03040510704000218a01c01810030000c0c0c58940e5038000d01282008180300b005038003407000c40383c0c00c0360500e40400072510900039207010318480c04030700b0124101420402d045d00c801a082d00e042d030b84100b080c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 964338633 1250 964337383 964337389
    0x40b010504090906021b1b2b0320030c15091213030b0f06010305010905072007090e100506060a08150109050909070f0b03060907050d0902150403051b 66
    0x1039012180ca00303001155207140303444d040c400390084019910010700010348031081d107031003c5071007107070203074446d181c8941c030000307030b4100048401a58071682c3ca40da0400c3c0300104201f00041c024100a0213800e080581d4221003c410f6095003450000036103a42000c10f45150502c002d2010310160b4441d24840c030254100b01c0c0b07450780c50b207580c2909400e000c2d000180000800001e031103a940255040105000720b40f034200602008a201114501e00203440d250004c144600a4402e0602581080e82c6032560b4400c5407042069908c04c1400141c050310540340300090550150013011241c0403410058018003644e941d90790203566029100c980b2954013808048466584031f41042d80c400c500001d1000c2513209500140d03515401c40d080b1f07030b170803503690001c2209116000440c64210792600a0480c041655819903583c41d0000351f0b8803a91014509001c40c02e501d10030b10181520149840e0001802002980000d2038042320382804646000701007070400a000040c80342d0039680043c010030002c030300f101d4000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 964339883 1250 964338633 964338637
    0x708030901050379030b07090f0605040b072406061e0c0803161b03120b011e080910110c010623100c06050f090c040b0105 54
    0x5141002804000101040580703c55062000c400f52000c501107960502907060901e0340d03d1003184a107501c40c44c248441010000442d40c0c0300302007480190150794464003407a4000b81ca10140034503202c01c6a011000c5200c0c400401c0c050400d5444000c2c449141551856880440350720940602006020800000312007804440040d540720a04400c0140712582c0c0700176500003120304031241c0d8904100810090b4105030b003980080c0440c1c0600f003c2e0701880310121007901152100420f00d410900100d0a400030004c43e55064100505020002c0120600307148070303564005105400141401c3d42d045400d90803881600f011440078640041d01006002e401182c0b40300b0b61a02d0010032001d440090400b11081c0401804000885024417004400710700d8900726804c2441c41c50302a5103000030004954140c1e001042035614942c41002c1c404d4a00020401c2220090702c51a080c4000349418400040c2940308440c850240344070107040074140030f4003031131402a00141441c015480d007200c00d03c00741c1c3c20000b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 964341133 1250 964339883 964339897
    0x21308010e15340e130b0a0306090501290a1a2d04090b03100203070c1101030b040504061a01050c0a350a020c1801030323130e0603070803 61
    0x209441112180b04050710800b8906070a040f49540b00207140070300142d002c52859040321007101e00d5800074070740011501c1141e100081c09988040051400c00c00681960040c519480c061800000d00e060700030083c502512209110a2204002c20000d00040c07800d0310800015103012400360010303000000707100c0380350310030081106290f00145c800718060210b80c1c032100078002c1c00400c6c081e44680d61541100081d201110149100b406160f2074481c0004030b0b032080d00e01c40d50041e514000c0c41089034498914080d484066241056110144856070b078840d80149802035119000c000381c0b050180c0e07503a0003e10f00aa181d141045001c026014074400e000480002194000101440e04910008619640307610102140d40902b040e480302c1d041560b40001511004c9929001e84150031241402c22a203043d00722041022021700d40b00600c0424841c260b400b01c3c4405400d07180c0b002d9000401c6c0550503070822802c04904664904050025028516200c2d401c01000d90040400034244440b103510ba0048070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 964342383 1250 964341133 964341151
    0x90b09150d090507151409091b0d0501060e040b0f101d030f1e060613020702010e090423060402060415141c0c0f02151003020301021308010e15 63
    0x4624501604880c0c2d101c450020b6108003101c0c00c450b580c0301148180d00c004c0305500d0104103002c8848007155003a0301216036545004107a03029a50310021130011000e2030b605081d510703100610249142c0581b500c5000c0c06005580c613114490400b840400040c1d404071603000f0701682c0b00031150a000c0d00e0761102a141d6051509000403209050309030f00c0c100c070b6548501e29a152250300038650124802240040e8800d01c092229130f4500c161521180da01c407004d46800d40c00221902814095a90039409044400e1051400507920205a07000903282c10b0b0a0394280e500414200c1c410409804035490f4150500100001e0300c0c447c0f51036000212140198403400441a08a801c0820084d1007070748902c40161980b0905d907100c01c0d14105a904481555204040c46490302d66108807071070041e0300902c5001c0b00360740141070401401d03910001d0000040d004540072200d00c07401200580d0300380082d098400704d181d0007084982c5010f40b46400c1d01c0f0589411a80c0f0f80290040e0b1043c00c80b146501c591000e041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 964343633 1250 964342383 964342387
    0x31c1517010e0703080909070f170709050d031d0a03030e040f02070206071202010b060f030411012f0c04050f07050313020904050a050d0914010315120c06090b0915 72
    0x208030501400d225100900c00e409650380101c200315690003e01001502075072410000d80c3c41180a484080e888510007005c5080541a10400b603210500244c0c05a028580741d481a903a4030089540301d512154110085891000e1105c0300c06910309841c069401b084900310081440e41d14060132003a4642d0711140510345448200040c0b03a8a50101c0e0700540d03020303020b00d58074191410b00a40d410342100462005500303008515030b8918004003501c503c0e00d41e64000c14610b0f1100e6641c2c60000b0302111a15041c0092148200702146590800940b0102d02041310b40405103100c4126007000171000c1c1c02e510440c642014440b0303142641010b039502002a041103584c130740fa200c1e0032039201410a100254080c83c000c0c100010081c000c02c5944000c1e1144044030901d0007185000c1c2e0700390000d4002c2038405a190f840d0910558400d4000d200700a00b41e1460300151a1540c02c000d42105070788106031740725020381004100312036114100c1c60040c16080045814409010000742a80d02d28003042c000c00000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 964344883 1250 964343633 964343669
    0xa0516061107080318060f1906080601090c030e0105100314010207081603030c0c02091f05060a030621080a030f0b030f010e16050f2e02031c15 63
    0x598050101004600301507500c40c002d600c3c0c040855401118100b000590350340a00c3c400c40c80c0012040d0149800b04804d280b03599410012132012409041e6400800b5291180010900c20610015010307000c640408100306071044405416600c017003a81c0c5206038501030800900821000c0d503030082d04e9025010411082841d03200314007a000343c0134040c02524000401c520107520381c103040c24085220391010700680e0080b0301c080e511310791401e1010390008020400600c00715038250003a0702614254140c0000642c8030b5011880580221130b807003010968613074040c420a01c084c0c14502d030a10000310b07010340d0f0b001710b5030340d25125002e100c9001082c5511144540034611981d048a0304c82e820203404c03107000a0803800014083c22003081203140d14001c050221a09004035034034601501c0c0080c204607440c0d08a00280074070b15105104401301603c0401c81034180d540307030076144841c000c000da00450b10b40c0030a800d0342100b880c242c00c2c505801440c002d501c000d4a804600e5603012236025121640c41d14103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 964346133 1250 964344883 964344893
    0x60c0302030c010c12060602010c1d03120f0a0e150d11090303121603090c1a160317010621050a110f03040c050604051311132601020a0516 61
    0x20b1800210322650078403042d040312a62051043c08a07a201200601103590f556a082e422141155980000100c440c14025850242508d0302082460094112000b05200329070106083e04902c0c0080c1c920b800026140e446035900c03544040241c48110b40d01c4030300c481c1015000e02c05202d5040c440010319120004901600c4078001550000e44002e001c0e2941c540aa9500241d2000102c031031045000000c40020200e80c460312944240c03640c0803100000560a14520481c09180072901d0b0740d424100700721964000751350b0703400c00745103d102e515004d070000c1c0b850190000b02c1505800c005d00304940840c800315407000a480403680c01c080100c0c0010030f6143c0303202140141081c0e10001503e0040006d10001c10448000110711450082d054484030a4035071003013103403c1c0725911546602801d410800b0804a007a41e10041012601c0501c8038034040c0c002c10304000403609a03000080c00e00120f100f40c3c940d1440985d000c4814464a002185040c400e050040c2c01e5006568081c102e078849143c050041007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 964347383 1250 964346133 964346137
    0x303090a1104110301080109051b0a0b030a020d09080c1c0f08090f3405060f0d09060f0203041b050135010e010503070e0f04111c050102090301180b01060c030203 71
    0x19518403800c40c4e43e582c40340c0e03416018158844040300e141c483c154039101500509920301340400001060000031a2500642e0740d12504040d10910045608000140340100c0301d05c5118000c81c81048119150720422492605003240c5103020350007034280d10340c8103004651101d900c0e4280e01803400c01c0b07051381c0c4442d0200c030306d06911001410340512500d5142405601030150403000c3c0c21080107002c0200c1c20303035007003150188013a01c201c030f8000b00d0511003041d0506525010301010707820000c1c0001e0640d032541f00c40050399075032142c0e018503d034008248801e00181c003028480c03943c0c1c01040c4401c80d5207020300090801014052108092204040d202035403240e0070244203034800d1000f0403800c1541c42d0401401c4107a000e211301d900ca8841e0800004211110320003541c132a60b070031009a003199443d511405507001d81ca501043d8801e070f0340e4404099410309800781d003040c14000c00006072140f107000240b40c2107a500344102c0c078040d01a4180c50000a00b082c00c100d041d100d41d40361105199020b0b2509038618 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 964348633 1250 964347383 964347401
    0x3110d060219021c020703020604030b09120d020a090b030f041401020c06100503070501080c0307081506180901080a0209041203090c06081f14100e030106030f140303090a1104 77
    0x40382c8000021403107681d000520f20a42280a0440d8030344405800040c0d0b41c1e4003035071000a40050080c081080442c803906145540401c404080d244840d01008080342c00b680168000c0310451340c0440c0700f40b22181d000e1035500c080c2c88502034561650812203003400307800400400080018250000d0443e9185003034050b511110142011150607050190301c94864100070700805011384a4180001015849500c100d4007070321403c800d581c45e40d242c4401c12100c012000342840141c410000d580d079001e4403808010142c01103038840044d50b0300c82000c10086c1980c41a401485507600c085036920160369a01d41141d0000c1e4440e192400801001e0000e41c007404043d10702400c0c0314001100007401c2da0304507103a54441c03541d0714000d04400341000030318080541d25015410413415a5550013030070b0705000c485119100140d00340700381c8200240d0000303801d413550742c1c10440e9215101c580000030031a114524000c680441000f079429450200844c5595020285014010030102000c0d5503082d1990341c426444 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 964349883 1250 964348633 964348657
    0xc06013003051309050a0b0f0d0f11060a20030a020c0f040608030a0f03050a0510050f010c05060a0914010e03120c09150c060603060f2e091e0603110d0602 68
    0x1c4035607803070b20207000300401c4661440043c00c1400910940c80d05100e2320811020003071468a02e44c07610b4441000248401a0890341c4c442e44012a006642d1448007802d06000c06640d00c0060780d20b1200f1503140c1b030034591080300d440c0d80705000703100c00e05030007150840003603a055420003090f107203400005000d070925600a8209000024560030011fa0042c0003108440c002c1d00c0900064407002681401c95104545902081c15440341c00e20080c60041c80040c1600c01c149003d030a4142d040d03d8a50800100761885492a90b40700d441008001c005504000c1c0c544942008200c5c00340303400740e503580324411000c00601000a0600094100341c000050340c8002d403000c2c1145003491070007982203040c4e0380000903c00f1503208440009806140010306284600745e103040c0391111351281e00e52142d180c2d0380030342c14940031041011005111042c402d840c0c1c0c0140010310b0045a0300e040140780504103540c601986000fa42800c0c014030104041c1c0003a9100c0c44000e071450070020f859420184000e01445200c220 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 964351133 1250 964349883 964349917
    0xe0d031202180604030803010305070f140409050114090105072c0d030207080f0a020429011107030609080301050907020d0c150b060a0e09090706120203091906020c0601300305 77
    0xd10511b5806941624410b00407203516036150301e4075042d065014803403000a0200c10380706502e50709040e00708074006403080c40007003004000e14440304500c07403040b180390100ea035444c0204002b10754090301840e005c0012501807160f000d1401059081d25040710752a9025051009483d001c05108001e5200240038040995001c0c013443c0605c40d03140c6090ba8000c4e0700c5941015400741c0840c0000b417840c804601e03604204682c404610005507101104009244481d020b07140c2d0020205100707000b81d9141d00e01c15640d00707070b4942c140001c010000c10080d000404550200341c1c1c1d943d02a070050b041c00b403140c0c1c11440c946040c0340d0a950a40c045c208a500c03442c0c10400100d21600c1c010340103000f00094070340484600c0c0483d074031120340583c4c1707107400e21176480000c10040242d0b042d005c16070b000b10f4001481805544854020304070440302c450203100111030299001034008689102440024003403e044180781f000008907044130040b200e05560560700c100c2c004034001041500030b4048489955031000100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 964352383 1250 964351133 964351139
    0x1080c0c06062112190e0d060c03060b1216050702090f060a1a0310090b0d020d0c030b160801051c150e0607020a060f09030c120c02030a0b01060e0d031202180604 71
    0x42e000035001e01d0302e0307454101d40c20140d80d000d0902240107220241564800d41e0b0541c80e0880034000440d072700d07001d1642d0340c080450926002c1e001003284c0040310340c0320121410001049110400300d4031914042080600c8044c1c010381d500c188242d048003d50b540640103441c0e5000007110010b0680c02011059000c0d00c000740c1865029001d18800c3c01c2280048031026a0340e00c540d07080d11915518168442002c2103150014540f06000d5109240038010300c802c4207859039600816800c083d01c003183c002da0144808280d8503440401240580300640c2d07490080b03011030400b0405041681c200034442000000901910785440d0302091040b408901101c9a0f41031001c4040d40351a10b0070310a0f1515030908200d070504200c02e02070388a14035031540e9413a08014142d00c44c8000c103128040c0007020820380e00e00400141c0e80130405507503800e0056035544415490b144000e00203144a80100b40605880745040000c25044580155100301c501005690b078050800614461203103810682c1d4848000309000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 964353633 1250 964352383 964352413
    0x6030b10080c1002190f050c010206041106180612270c060706020c0a120f05090303041512050a0209040e0a0f020405060f03030301030b0106021905031c0b0d1101080c0c060621 77
    0x11b840481c0500160341146442c0340049171520340448010f4084982c0058901e21403d0150003440c0c01000d010b03219a8400c0440001205648160031030b00280c0c0140d807e00031000100c03821a10405840012f00200c1c403034a01400343c41b19440e1480b00c0c81000089206000e005150b0104c405441c808415034407001414540b07285c10705014803402001885001004200f0b5002c0e0742250107070440180210304103440c1500c01c1844941e00c500d94800c22002229582c40d030402802202d02034030a0000250701e820340c40c8280012501c10b01070303c16043d44250400008580c441e6500240542c041d203011900c0e0f500c0d6004611050501010590103100000c000014403e2040c0503a0584460303a00396001000c5102c0d1700004000d1000003d03005400400c90314410750502030541031035260900002c20ba03c24144005100c0c04101003007507807030b1044c0944d01c1140d581c0c4180c5540d8851020450541403242d20303820203540c0c0d10001c0c8418022102d20351510340c041298030580c580343c030800b0120354105071079441d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 964354883 1250 964353633 964353653
    0x602030a06090e2409011e021809011202010c022b0b010e07050318010f0f0c0306050102061e0c0403051603050d170f250306030b10080c100219 63
    0x1402c1c114514000c0d214002d4100400c0d015201d0760841c03026122144140c0c42011500d43c084e0002006650b10507400041c01d88406135000d000c80c2440c0700680b1001d04503d80051032841e048940c1c42400054010f01000c1000200041d0558080c0390110078203104d0b102142581c41003626a640403079032011a440c1c0f8010000c41940814443d210040c0c840c0d0380c0f100c0c64040004241c0e0003601207003081c0001751900484c0000f40c01039152030310001c641e401d41100c01004840ca00300807900c1454480d41c1e5490015014018076006040030702c001c000034581070740e50580540118500c442e0045030300d40030462070060002524060b50b0080c0c04d58803034005d0301e44001050b00f010b00c4129154080e1240e0a03c0140c041d40685c2c5141d80800c040c84007942d80c0ac0e481c5900c801d0300809120712030401e90000958010354a440d200c242415440000d0054118100811001c4005003070500c0740300b00e50014016a030010990200d0030b4000d80e600b00b40c40b200c014041e4200310501170381020841801c5001c2052010b03d120b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 964356133 1250 964354883 964354889
    0x924040c090b0304060e0f0c0406050301020405030d0c0f0b0c070b240d0303060e07050c0706020a0506070e030f0607181a0403020f1329040b010f0e0a03051f0c17041209030602030a06 80
    0x12707040044954070414117090380600c2c03080c158550440403041c1c01040c0191141c501d264855010814840c0541e030760394000400599107801c083e280411420f040288603100306802602d46c89003040f0201190103010700c140f03107084205001c0c0c4141c5030048105806030304404094250307040d99401c1450440d00080c0310790850718000d9000c2c82a0f0500181860001c103420101e00d8000014100320750351910103542004404170410740500ca61451000c0c000341c1030003c00c3c0070b444039a8410210081c04980440201c01c50742200300358804203401c400f01078425404039400c6a40c150703040d8149480b10800500d001103804002c1d40880c1c1001c9a003c0c4529000b081c5402004e40c00038600140c1141d1814042211180219203012482c0c00d10704001242c0500074070340d40700000400c1740d00c100e5226030b5a603081040e42d5200c542c802c500e0038000ca811042030300406032135030a1441d2010b009001d402000301403501c0540041c0c0100e4620001c251a1446040e454010b10307040101590b80c1d0030140183d200070700a900c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 964357383 1250 964356133 964356139
    0x9030c15040f180c0f020721060216140d0207050d08040f030f0203152e09140f090d2a140c010207050a1415090924040c090b0304060e0f0c 61
    0x43c03c88040b24010a8045103402d6298020045a8104098212609484120481080401180c0b03000103083c9e400180258116080742e401c0900c250300c0c0a4460130340c1d0500f50019170b00403c08000b40340e43c0c0011000b00b110001c0b100d9192500e4a42000030b614401c80d00040241002094088140480c0424045080380300f41d0855003109040400c018824405031400d0000541051552515041c10719041e060514a40b00340d80d0140e541d2010b1204403a9442c0c80c290719052030070100860745129150745903200e101000500828000844001c00c11040e00907a0f540601045100300301e00f0362260050013110341c0c482202000c40301012012075451200c80e41a03401886074810102c0e0a08050010004440d5203142420708065070008020415034007d0340e06203074a00500200c141c5030307542000c180c0203003003c0031a1405d01c080c0c022000c02d80300e20503004c0c0d400781381005507029140358441e000004460300c80314040d440ea03e0b907107400005007a4000c255507061158110611840c0300c007161028251100f1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 964358633 1250 964357383 964357391
    0x308060d0210112109010e0a21020a05030105010302010e240403201f0c0f061518112a0106030803010f0503070b042d060503041709030c15040f18 64
    0xc113801c480c0401030701c41340d010380320028000c000242d4003e07200a10440d10050130300300080c8e11014504000345440c43c0444104d218500c07500103505007c4240e0002c0c01050703000348003560554001818040c0345006460148100070700ca01c0f1815030090028a040f14074611541ea41d56881c108042c40410a0400e20b01056034180c207140c661408605008040c668a1031084010003050010741d4001d060010585190059200100001703850b44584d001da02c401807205008242080180d40f802c0502e0010000360b14685414101d90310b0102e4195046142c802c2034245200c819a41001000c558082d48410113609020010040280074009141a80c1c04a6045c0b040c040d036500c101540c40880d81329850400000308001e009802c010301554460140105201c8480702031100c1503e510401c980c01000014000b2040c4020445c426015017441185e2160702810007643c503000035211031844403540c1c4510045040108241140700a90f801003034685561045141d40d502640a89014600b01c0c8859500d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 964359883 1250 964358633 964358653
    0x40b1008060c07120e090601120b0616110312071b0e09010501051014270a0f03030f050405030c010c03021e01140903070c06080402040b040c0509210a0308060d021011 73
    0x101e0017441914090042544005403605070064440d4280966498540e9442d80141d00c025194440100080882030650300608100c82c200520400f1400900d503100390030004440350b1021240080e00c001d00d400207030178030264182c0c0144c04201c0110380d00c41e00034018440b041224105041d880f903030481d80c040c0c0b44420f45442005048802c821a400d07001c10015090010044014410480c8902402030143d002c1c40340c01d183d40010b540751401d40c04029082078152080c02010b80c05141c2c0c8040560504100742041d040a00080e160007108800340c0c10014079901c600c0c01d1520070440420914411a43c1c0c0d55510f01c400c0b10b8034064000d8121080d0014160804a01c1400c8004210741244c0c2e0820102d80e08135007041011207031070001500c2640d01176290f0100400503a10f034400c1d0074001d03d42d40c8819950300160001e0111091051307a104092805c0f20350120b01545000c22807010711581440c0100ca40d0ba110400105400e5038040b0194129018003444105640c000300d4240781040c000d0100c900c0c20724 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 964361133 1250 964359883 964359887
    0xc09021b0c0105160f0c03141b0d0b070216090605030705100e010c0804080709060821031308130602071a040303090b28021605030a0506040b1008060c0712 68
    0x1ca4912550000360b0400c00681203512801e01399050f184901806810752155484141c14403500d50016035041010141d102e4440f001044a03807120700b401c001c01406240c03120000b420b4044501005041a1031100002e42424420702244401d108281c5086540342d0319165840c004120790701419001c1d1003050000b04d01c42c0ba0064505145d0081c591342c2c0410083e03804011260780c03a84d440c0482c0d06420900001ca840801446030101502401c03000184003803600740141d00d0070651942075081c0801d02c040e03068042e00d450044139030000c0070380f0071201120340da071400d60928403580d0507030610310010f80e0700400e690f40d0214414003124841040c1010440101381c05001c0c0d40710b10300c0004c01180034120100304c81c8845070050118500c0650340610030319625501540710800303070100c2e04c0c0103230401081300900031103410042e0040c0c00150010180c03610300e41d840d40e54404010703202030007240c039480c00140c000f11141408406410b1400507110141018140a54180c0240001320754080314400b50025940c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 964362383 1250 964361133 964361143
    0x22505071a030c030a0e0a150f0c05120c09060c0a08040302030706080c180f0904050c030609030c0c0d140a201008040b0a06080708033001060f0504030c09021b 70
    0x100c01d41c000e45162176035405a03000f0041901840c090380619092030004c94403583d1034002d206400c520204840000683c0f4034101c5416960200a10005102161040c2642c51119901020005025a50380ca071400010610f0140031480b422901c01c2520000401848e0805002281d00c241d0890b0049a201c00040da109402141c0d540d5400105116505001c0200c9801950030480606402446030302d04012625031007080700c0954640d44140315000c603505081000341e6125079048044c60404085115550b26480c40b000114818030504a450091103081003510281c64000402c0322901d20f110f01c0c0200388005041140c00f1244d0101c0c60b005c045052a80d00079800b645141c0d200485541c4940d41c404410300c000d42030104c0d966550703401103405101001a90003600e4080c004540750041c0716102c00c00c0d0312181c16009051440c0f00d411400080d000208141902e056080030640800c024804981500480e4001f900ca0500c000740010000b04640c0101900e04810300c071460040c2d81c5941d82c640d50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 964363633 1250 964362383 964362391
    0x30309060c090305031c0b0406090b03150907050108090c0306180607031a06070311121e040609030f030519030608010f051501032f03090d0e03030409022505071a03 72
    0x3a0070400504140c6c80a8880181900c25800703c0001c074401d820000c00e04403142c0350860511b4540d01c020b07503100f900e001c01095800c03010314a03e4241c90305e40800000d0712030925204a6060103125070200e03005680c24080b003030441c04064116075a81c9407420ba0072843c00340a02450b0180c0c02400f01046565202e400754844040c50281d0381034100c40741406111455000d98000e0b010021024200b4150300024030117501040e11031707001c1a8850038010198800c2e01d00c000408401c0f03540c200000c105241e08880214100c030b80055030b1250f0454541810344031441031082242c80403000480400560b90141d0142003078076900303002008408040c0c0c20301000c40b00e06640c0c0c0d0341000602d1240701150340c4682c200050340414040c034001c40e140084900952880182c1109817100408010003a8603107041121030440141840e005d20031400318004651244143c0c05803006a43c0c00040ca541c0070042003056051011101100d40c0010354942003054545203640901902d41c05030344203600c0e5074070010050701e000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 964364883 1250 964363633 964363643
    0x10c022b0c0b190606050405130605030703060e0a08190908030a0e0405090a15091e03090e0a090b040b06151e0703090b0a03052203020607080601030b0d030309060c0903 74
    0x501c2200d49a054400000a000064901d07026490000c114002d0085400420fa2500d0703c80c1c4507402c290800160410644a03d002286041c44c00c101c5aa070000d0840126a0048800100e0644034159241401c42c0c4000141030040c00081480911403100d00044080c0140c0d034400c4c00443c2c0f6000c025440c1d110345101200084c0200d140500c007490705500054008a01c04100c504410155441d0030064041405084c11703207503a1364030175003484007028140301005440c0c218580d401c5055078020382008052f0003022142004500000c3d99050241e1150003500d4102c40b07045014030342484c058042c00021110075004101c0101140d0400060b50107450b14103c4c2400640c04001000c0441300e40368000703c0b4186c0401a504500003801d1030110000c2121001a941c007040c90b1811580002c01e5032900d89140440b005e03907200d2400420b42c0465540d4000380c940c6442000b030f4580500413805004001542035210400d010f110307041680543c001c4040501c110070a0240a100050540340070403d4407010304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 964366133 1250 964364883 964364897
    0x105060603150f03100c11010c020706050414180109051e090a020d170f07030e01020c0a0e1806070c0209011205211303060606020f071a0d0e010c022b 66
    0x543c0ca4407030740f8480d103404054200e038580c2d40c4001c10081039620203e183c902240140b80704144c514000c2c00f60b002581c8480c0000e04801d0b1510b1001403580c442d5202c0c0007084500806507204580e5001002902d012115240040c80d503100e80b4120000d00050710403004013041c244000d848200c00112592282242c070001d01100b000c40d8080c844000c3c10504100c480f542c030b111414205601c1c2c40301400074803204000d0306445075031510b006070081d610306200703505550014040c58000d170707100c8071180d05560540102d00f1007602e80c00d4150000313401c140003840050160ba010440003030345c42107414403920f0080703800702910390b81ea80e06400030210545002c0c240e900320340b40001c0d04a07505201480400c880b00341d0145809034928950825104c9038008494060f05e407a030401c241c0b40d0400a1b140030070461405008880d03d0901422100701000c1c03205000541c0c0468110840b4100703601413800f41c03900400a20040980341c01c02519844403203542c14814003181c001000c039044010448284040d191580301c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 964367383 1250 964366133 964366171
    0x30603120e0f060c0f0d022b05090d050105150f030d030e1c2d0819091502071209140433030b07020111040302040c020c1207080105060603 61
    0x581c1012201100354000c03004048a8409840381001404006541c10141070034404020015042c00b580f802280115803152003502d00b540c03100d0700d20850602d071440803d1101c2d038000100350340ca40644200030b603104601c440c0480c00c0c001c0c19040380c1d1007007007040c03098a05500c801c010810542d03100590b5541560100130303941c840900031351114880181e08800c4030401d4901c0c2070f80d500c0d9190b1540c404c40010b101c02800c88804c42c2d0301c0c2c0c550500d1180440031807980c0428400003d01c00780e070080547d1324030056503400c410011032952115044940060a0540350700b1000102070182d40b00720801c4455030820030280380014410801c031000c1e1000c9a0015015001410411028100d0240c0400e042412032102250745001c00d450068a40c44043c4001d0900b0702d10306283e4250790300141984103590428880780c5000c0300702011901a203034115000251000c541e8002c038030b0b02c0420600e07e500072224414400b003c41c07000844500b150640702c0244442e564003800e02c030083c0415940c80b101034034039038954 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 964368633 1250 964367383 964367387
    0x7180e0a091115090f0604061d060d0e010504110108040b0f0a14040b0a0e2e060905010f08060106030902130513200a0b0415050c03042c0703060312 65
    0xd103800e60141c00d642e42103152400c00280703c480070040c044000c00d400581305500d401d1800424111183c102d40b8070341400c0c9002000751038010002003003042d011031502c1820140e66a01c080c1c41c40016100b1040050f9200441d203a8004e0000351420365845800460300019907204012180c41558400003030403441c2c65a04441e090410302510083e10203441c2c0400c1d0341c10034818041c081c8214010a0614164240400c0140441c4d40524264044d60405026580741c2d128842d1480d180100006041805203e04070300b030f20042002d0f4004249032400c14000081c5224451151000c0e41c0420064404c0c6990701d4009500300c40100000a40083c000d06890402c1051640282c3d4021582404a0b20f03a03440395031642d0070700d101c0743c5410140c0760540e11b1101031420714a00d4000604410740c0880d02d0542000c03c00103070f000d10501d070041042800035034080f000105109039401040d0409000044034401c1c000b00c9407880302ea895800c030101c0000d0015030000e10a0281000f200c0c5c1211610350070f40588442 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 964369883 1250 964368633 964368641
    0x70e0403020309030a060b12011103070507030504090608030a090e0609220b04150f18060509070f09140c0913020c01021e0705010b09071d01121407180e0a 68
    0x209a007580000c0c8202c90350390b1028003010101034460080050701038590000c01010f00703040300300b400c3c142e80b400e0f00c8042c20307543c0c11044a411030960308200d9100c44041c60304450620031a00a01c51040c00c040e0001404c01c8000040c2a108455444603d1046d44440c82981400c8046411320740c030064075000700e48011200b0b400021000c041f000041007030481502c0b203804074902580d0441d586036042d03a02c804030311041c0c42800d076000d04d041c40034005030f5071528400400e62982000034209e6552407001c25a8140700308034250007452000000f0104075a52842d8500404d14450012420b00c0c644002070a9080490110780078071000170030220790f102e4440000002900a120542c0c150341d400c10109101c0c03400e840f40000710140d0283d0180e9940c040785019401d580e41c04180500507843d24041c0482c241c0c00105d0100b03c180350310700403926441c0d6000101c4000036071482002486261a00103451080711450180c4610344980700c100495158013a0701c5014600b80c8030300000c0035290300c0400c3d800340c41600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 964371133 1250 964369883 964369891
    0x606011b110d0602220b1e25060e0c0a2d0b07110310020a050f03040303291014070b0a06030c18060e060a03030c03030e0106060c030e06030405070e 65
    0x1001000700c50b1540c507582281d00040e03600300546030070096400c100f00100c0f0860040d01003140c0c118204400da00b07104096050506061244600101313501c15a1201420700c0810041d0040380071420340c0f02c90034998010103001581c02998064000041d0301814288006411511302a420a08070f03200f60b9034010500d504502021030702088840c0001e242800c1a010f0b01c0003d0040b1381465004070003800300343c5000042e1520b85080d038014030466552035000826070b515503d041c0e0801d5569070301c0346002ca000304a804280340581604500b81130840000d84004004150199041c040d820406c1d0002d490982c80804486401c0404120742000902c2460817103801c68030400010a0060322695a900e0307598064003c4907000110503007115807484c650240700010903206641c4100da08100c4042403048015000280c20b20003805886002c0510030b078854204009140000c00c03509403101302c01080406041011b9001615800003640c441ca03010781104c0c0165030100003403100b00e1824861104000c0014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 964372383 1250 964371133 964371139
    0xb0403030b0d291501090501051e0708090907140d0c180621050c0d050903070b1006090603020c3a17072c0a09060807080606011b11 58
    0x245400d00011004003424a82d40b500f03400002a601c40d54071402400c2200904e4016481c08400c0c801d41643d8120404800382c81c1d00380f80070b030382c0d4003209034030940e0340b180343c00300d620350706000240d26070a018183c0c001d416520760480e00c5144580390404215040040e00000c2ea001c3c5c0030401040b007100526a1242000741c400d406e0406504076641c071901d01850990303000501060102000c51884003c4041e040b032030b105003000c20860f034145222410528000d61801c1c000c0503a07641e010035a9403404005031104180e000c4000b1065262403135103034141d40068414140442c51040c3c2c041a814000d00940308001c12407402008454040820203810a0b040075000d480f80c04901001c50280c0c100242c41d000403000d40c3c54031321800c04411003590b0070200003030980c1c040002d00c03d0768040724100c5599420045c1da280c3c2d0710301c031415603400005105585650100c00c48600d08100024080400f19114040790117030300c00c1c7c403403564500006407104003c4958941001640c1108080000c0c40d507400090548006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 964373633 1250 964372383 964372399
    0x1410120b0f0a17070510080103150219020f0f15061504050d060921050a03050603011d0619020304080403060903050706090609050d02010606022a03010903050a08090a0b0403030b 78
    0x120307001c598407000c07076004484801c0540c403007948042020440b690040105555185189444650051103400107000041003d6409180319481003d940c060356501080d0703e076035000d064100d40c40a0b664400703a03808010f05010b26040b413521700c20082001031f0b03001c6050200751301682d40c1740100881460289808a1310703080c14080860740703403200e4040c52403d5100320000581c03c00e0078103003298000c0a008108241403500c02a06912692003015212100400c0c01c01050b00e840e524006405480410213044101522158a040b0400300040e128000c402c40c042031030b104043c5116440c141c1c801200e0152041034100400c0002070101c0d4040d50906000e481c040d810041c8a0b138810081e41c81c00401034617056240e052000c2031200910060104840e00d00080002c42d19061001c0e4561001400003294142892404110b1a907620126a40200020000c0080180c1c600e405041c0360007444001e4009030702400040c04003000040c0101c81150410b4204000e03554030b0b40e040b400780c0f4a80d00e05542000f16 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 964374883 1250 964373633 964373659
    0xf0905010507050319080a140c0703030203040501060e09150a020c0a08030a06030b0f04050607032f0403020a03050105180c2422051201090b18160f1410120b 69
    0xc4c03004445c2c200101541c030b580d0340e8180f1040d800e041e036460748807403840299050b05001da030050142c11120101c0d45400c01580702d070b0721070070401d0040105500c20680c044110081220007003011407402c21919510110005030f4841038010300883c0212504000c0961000b0b003100d0100c0c00000c0510b2b0300400886020949a4807982c9030740f44502c003a55030507100e00540c414041080401c1c49044c1d840002032a003000a94103440180303040c2c01ca44001103800d640b50382c202c4011a801d003800c4401035070700942070340c056540d24a002402498203c500c1d04071001000300e560000000070698809400c80106040400d1012600041e10400c01c402080700c5018200103c81c0c02c041100d149015035030035460319000e82840c007401d100482d183d48440c2c0242c2d03458405160700082c2c0c0300f240c80350041e4403100021142484a03041c42e01d80810003003000b44106400200240714003504504800741c8403404a004d901084800500203003c04203004500800c0c200c5c000814851129402880c1041c0700401210303006407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 964376133 1250 964374883 964374907
    0x1b070b070803101e0e092d0a083727050d0302060105040b0604030519020607052b05030405030d0506061b150903190e030a1a040b070f09050105070503 66
    0x1113030007a550080300d0b020b20030040c1405000149074094a0b80d07000c0c0c45900c02002d20003c40400a43c400580c01e4210216803103100020800f00c81841d6002c0ea03400d40d52030080300741440f030b41160013000e007800040790140ea5502c0e90f007803030002504249032500d2603541148050084540040c024200582203500c03c0000c407980c030303500880c1c0c405000c2d401421301541000d0903c81641d20b001d07807481c080e1004000c100001180011034203800c4600750740917142814a44001001071040c26400741c4144224400d01d007a08031890000c2c1c10b2141c2ea45111000c0b54a0100150303018001214094030541040c8200c0b013801d0003a421041e40000010403052501340c1c2e10a085803450021a950001580700751040068600d0049441e50482080e00055080100038a2580650a113695003c0d08110b0340005c880000d4070300704041d01e14981d108190301610a01005c0c06610b0141c1150281c8032681d503d0701241450b401000407818a00907607556280e240c6c1014015685684000f104486030312041121500702c2c0307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 964377383 1250 964376133 964376159
    0xb1003022b0914010b0a050411070204050c04360926090405060402130b0a0c05030711100822170414100f08180a171b070b07080310 58
    0x40d0616200085200b92424009980054050400e009038501014603130541c1d140801c400071210115401306909819082a203024007540304025040740c2402d040c0003444d0740070800f4100f03845c1d801800d450004078842c2a110762000e8201103210f4481080310307107025080107401003003e003805040346481003030764000865271b9558881c041c0200441e02260440c0c5030300d02400fa058005c0c0c0c08807019401e11000c0e05800b00401031a110740c0e80c0c2c000c00020790300091402203503403807161504881070b00e85503d00c40c00c14802d00303424411218813030301c2c1440881491a014640310390140610800c012524015109840030f44c9030800b20640300850111000c0c03008940400c014809840ea40000c01c3c4229a064240400c030201f0407681002d1055001803951251341c4000c00319884030030004550b00958481030100d0500b00241805042218220605240c0440e9100200081e00112400004e52650074022035152000d5024011180808002d02e1022400b800c02841c0c00009154800c001180e5075543e841c1d01c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 964378633 1250 964377383 964377457
    0x40b03180a08030618060604140118031a0c0c06280626150c0307030f050f1801020a0516140706020d0215070509010309151d010f0b100302 61
    0x1100b070010400245042148000b8a00c002c54105410142007480006180e4000c0340981d120507500407400107400d80c8a031612a2408c046851519110f41d142d00f0611078182032409000c000808100200b45510116822070700da5120520281c00e80340c44800504451440343c41d00c082081c4c4002c1c80c00800e0f032404c1c1c450b0f8401003880161042d1004c07a8901002441125619030188d16003000f0f482c000c6000d01c00c3d400a920110011000d5540e580c0c3d000c7c20340060000403000d1b481e040ca000100b0038280071101c030041c000d90008115065400c0c11140072401e0344941000d86000a0003404400c600500ca01c1580c2c190600c20f160202c22604819815440e0250b42d502410044c1d2240b0052804140c041c0040404e0f101421208030513440d0980000e8020709c240f043c80c0741095034a10406c070900200c0c41410801480c1c000c410301218401859288821001c004c1107045940f801c21400701b115854802c16220a10243c00c00b800f08000f0301c2c098009400406501801501d200921005403003403028401c11 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 964379883 1250 964378633 964378643
    0x10e060d1a0405010e060105070f031704060e120406021f0f020a02150906060d030e12010c020a020102121204200901060c0506072f070b161511040b03180a 68
    0x444007005080000399001039120903d114030801c01e028003a40e1040840b40525007100701110498424541203e00a50340c034100c00000404000344010408150420645000810100c6000404018000000d4400c0748a0040580e00c14080c0c1c01c0900700301c000700402c0b00c90007140042e0140c409107401c0e0076648042101001a007003000e000001e0411412107a80082d03050340100320524051001c500c120940c9040542842088000e080581c1ea40300940101c400a5400910031054042070203552900c980300b00328003600a40c02103441c100301041c151080c000705200e4003640c80c0ca039601d40101d44050000c0e18407041450160103200350f2101c0300020b00900c0e840d901d50b82201311600b042810010050700800c00c2000078501d00301600380140054000140341d0040c001d0303e4501c2d211081c82e10b04903a2040000703403004264100c410b40700310b0880703a20034003d10f01c42100c460040a10320880c0c0c40b842d0880070f084000e0005005c4801c410014503400101d256a4000d6a22003041d55450b0802c07214040740c2d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 964381133 1250 964379883 964379921
    0x506040e04020312190318050f010506010e03150c0a02030f2722110d05090a030809070f180e2a010f021c02010b0901060306230f010e060d 61
    0x2003103041c00c200343c118a02c000400103007801111380700c4801017010450004105515800c03800c0c032041c1031062040a460340003007111002d001012195018080c100c1d03110780856081401407007030382000701302c03e4001031006000d071035075a0360f20f2006c503aa50480e84086046100a0040c0d88418007040c0003007071000c01c0f650441c050302d40d541c0c000b01030802c3c40d40348040c080c0c0c0546184803030558003080121040020001c01281c0740c1c00080f41c0c07182e90b004400d0080c278803070706002c1406010300e8085034800000b170196882d58903950300c00d08441e9460030148112010f142080310b082003107034070001c025080321008034804651444c00c008040d1408480e00304425001c14042d1400f03682c11300100440340340030420300784004a200300190294940a4000d0110300a40c414032643c25914401e40c0f100c00b401d80010320044003540c4520000303000703280d1f5000c0c8120b244105038228040c2c0a4a0448009943e4020003419011070b084004458900c0040e00640e0440340501102c04030481501849114564484900b8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 964382383 1250 964381133 964381141
    0xe040507080c01110a060507050d02040e06030d090e04120918050a0f0c0f0e0a090207081b0a1e150609020901080115080f040812070801030302010e0609030a03150506040e 75
    0xd4145849440b26606121014070b40c915001c10214100c49500e4010200181c1641c908a064a2600c12010840350b05440004c0c0818488219600306008040a6044070801092094141c2d040c180a004030802c28800000240c0080d894010401c0b0598461512240b5145d13140c0c214074414542c00c604100b12900c1d0400c01840320604d11444000c0c0f044000b051103038460825015200903c2140d4000420680008160b896242e100c010402040140e034119580c0050341050440c45d0801101600145400544901c0e0b4610005800c19482e8100401c022150900d80400d4654144640100e503682464180700702001405d200c0d02004001e4001c000d81d449001e007000400501c4160850070103c1d07003805142c500c6a0b0303c040c6190303021202e080355650741c1d115810b20300080d0091203070703000154844200b0004c29541c00010320303040b680300790001d01c01e1961000c2c502e9100c503801c0300d06404603070050041810092203074001040b807414000b81c0d0201a40c4580218000d035100b60496120700103941d00340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 964383633 1250 964382383 964382399
    0xe04080a05161a09010911060a030b0a0b09150f0d0506046621020d05150f010e0d051507180819030e090a0b091b1b070e040507 56
    0x80f0382e000400030002c0040c4219035850185102000030a140118400300c0c15201450281e4400c4030200d100510140156640705690303c840c0e4046100c150048100840002140c0c0854095440301a10806070601b00180d1240143c02414010122a40300351500500702450040c51800308400882c982c0c5070a18074510340e400c03241c8610800c810b5803071000340b0340c3c8800c14600150a24640c0b0142658282000c8d88201e07045525560480c43c01c400700d001100d2007020218164020050140e540c40d06114564415604580105021090a4000d4a46541c2d001198803401c200c09280c20300802c4041c0c0510562900740c50003112440c4441c40342e45031018002d2158014412681d442d1000c013016050500703100040740c8031402640500741c00c000d4400fa2104050294101c683c030103034040c00401e81840c01d26402d04c0a031510010f400d005115800c040b58402d240c5504840300c03030700c840310050f26049034000c2c0240c004116040b500090b000c1c484000c40c0c86400612081d00613030007003000703000c15404e040c0c507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 964384883 1250 964383633 964383683
    0x603060d211b031b05120a0503010518010e13080c030f1c0e030a120b09070c0303050609010506040e040f020d0308041101231e040f0602070e010e04080a0516 69
    0xc03010703000d940b1035510400a81d0240f100070034800d04640300401c400d1319181c503525003910980800d848020210308680e046904c4409141254400c07200d10390b60180d4000b0650b0702c03040030b024501421811800081c3ca00c84200b00403915288651055440e00c0a030070f074180c2c115000000c41c240300313080001d50398004451450320303005000a070800812601440f201030654a115a850843c2400035810603610744155940c00303500705260251128600d03182c030b040014840000c98030110042464080400c02c24184008580c1c10b840d80541800c4c906414200360000340030004204a030540f800003074900060700d0f842c281d01c41da5807081c8c840f620b881c00d003803034101050099452a203040148015459101c074002d2070305074443c2120020f280d40d50340c541040845001c00444401669a10001000650007a02d030081c0001c6403941e90aa500d4151103c084000c0c0c01020300c07030314200c1c1d0541d00202c0c000c2613034940100303406c0149003001d42c40d18505010009007940c4c0b03030506846001d80c1800c1c80d01c902c00302e030314 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 964386133 1250 964384883 964384907
    0x6060518100c020d0618031e030605102d030e1009021e18010602060907060507050a03030b1c080d1805062206110c0c030307110603060d21 61
    0x703081c551060807190000c0c6008180b80001e40f044070720003038031014040a0350000511015205101c40903100f64200640b0f82d0903d1003480c207401c804a110b07861014420310075070003500c800416001e00c042d10b2020440d031448000345524950811342040d00c10300d2a016a00e4607050ba1a0346000c220280703082c3c00c03d801e0469003001500001e00740480c40700181e0b40d044001c51a603c3c000c2a1224804d2981c0100b03601601070b08891300b5042c000030010449540029000d0b22034484003084407296600c40808842d1030040311001820b13a4042c80300c280000b0300070b4008145010019180341010f0185c01c0900c1c1c0400768a2100740d40e907102c00140c19094070a180100e801080c203444140284241a40da981d07074880300200754500f4483c000c1c04d92030701e0046074981034000c40d810070002d1104013488440d80d600c40d40310014203c0c071446490004900e606010040d00c4100380c000e9080800d15068009000c02984001c00840d1310030381c041c95080c0000e0358281403401440481011280c1c140400c44041e1035a0030b540 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 964387383 1250 964386133 964386139
    0x2030705031606030f0207020909011a04110423091609051c0f02030f034308090f040c050d0b040506061e070c0608041a07091502070906060518 63
    0x21818103921a0000e00b40c421514a450002018070540304030038000d008021009500484240a00071a00015088103101d06100d00404228040c0c01c130400045480d00307007100041d03aa050100f00504508a0a000b4401c00d043c490040f5900d102d01c0000d2240c0001c4a400702160084810881003e0b40305103090043c003010398003030342c56024440540c0803250482c00c0080240a4207400390342103403804c4c08003035440d2a1071405c8985980c181540740c8107030140408001e0440d01d50114074803441d0b038200c4d80602c41c000d84000b01107541ca0113480e43c50341d40c3d02101030b00740c1065621080000310f468920645810012556410b6240c0c4480d00c190f00545813240c2400c1d00c5103003401c050050541e6104100c3d400300000524000004200e511608210b01480c14040c042011040340090307200d8005600c10b00c41c911604407189401e0032001504074000341500c08000050b20103030240804885140c0000400003240102c40c500d6603125446400e503207035a040342e800102c020684130280c070002d142804405d0422 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 964388489 1106 964387383 964387393
    0xd020a032015032712070b0403030c0201050606090105070f080f07030807020f030702150702041b0e180a050403090b0703050304120201050f0610020102250203070503 73
    0x1070751000b03009803402d03014030b29200d800d2011248643c25500300b18070488040d24540b0045004950610098810035850b08201d80c8514003602495201e030400c500c052600d49401001c4d6007400354100d080d6030406080c00050b6032502c0699100003000c0c0782c01038071022076041004011507508005032810f03000003407014482d90384100800003d4003d81f1102e41c251580354040780c2d1000c903204114400d410034000e002c010310300044150f94451184240314101003681d0001004c030b5000201e078070444101c15046140094000c08481c003001d0702210051402c0b001100a200c40240082480717040c90350720702c0012f0415015545400c0a016026440e6890320305610b00034100d980107940540710103565046150305244140501d0388180b401c02080041ca032103500520192450506120003955024040c600100c581c1e01036480c610408200d01008215086c018181021040d0304a00d02903044 = true := by decide +kernel

theorem cover : BRFrame.Cov 964208633 964388489 := by
  have h0 := BRFrame.cov_init 964208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 964208633 ≤ n) (h2 : n < 964388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
