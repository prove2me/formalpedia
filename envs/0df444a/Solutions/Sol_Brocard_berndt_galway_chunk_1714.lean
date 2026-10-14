-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1714
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:24:24.419982+00:00
-- url     : https://prove2.me/submissions/f822764b-17c6-4964-aeb7-fb63e539e95d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 308093525 ≤ n < 308273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 308094775 1250 308093525 308093543
    0x14070507030807090501120b060702150408121e18030601080f150717150405070509181b160b1302121b010309151e0b0a12020910030f050a 61
    0x10f10868480d00c220400c591068458142c155800c00414010f419080c92090b040700707082c06480e02583d40c04002d0604146044001ca60701da0a000100341025441c01c00c003e20305000300034605031100c0b07d4401422aa46c4265500e46a81113403e845c03c4c040240c25184d541440358000215103102c011400d50201e00d201c0080f0f407041c44107205000440b80b800c0b0342520110320100509910041038800e2154440043c0c038044107102c8031840000c00303c40040c0c40c3c42c4002040420104110705101d030b040c000424854040306e206162895100862845142d61940443c002017560840d000d0320f84521a081179208a401c0818038180030101000101008103034414484411400e40616020900000c2c10b01c60071244604020742c10015070140401500464400f120204100d0a46115101d6041403152000d0340d800d8020000039104295080d04030020b20804185400b0044c0c0d4a103074a50305562507068854041d5980c60b254901c011010907800600b441240703601034030410802160108000d44510261 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 308096025 1250 308094775 308094781
    0x70605040b2403101e02030406020d05060f03120901050d0905030304030323040209250c0309061b0609050304031202060603011401060c060504051c03020d0e0d120203060103140705070308 82
    0x7070005054000c540743d01038110901e601904207164200c0a008460b880da0b6204880030140c4c28400ca90046174107032049a40801d810041040a01446400c1101100c110351201240340c002601c407505045140380c1070000158407030b82640124107848803105495820001c012180c1000d644a46c0110303401c60000c2d11f13100c14034190311200041c5555000c2c0210040d01c0950300c42d824403901e01c3d1702910007820020081c058003000b00040015610b00c0301140e45030709441000d45005400658280c00032418001040001e003030a000490195034001e4102a01050010f00e80c10300506501c40e603000901500004250719003100d400245035805044c068008000c1689030642c504085c181c00e01414000444124460000c81d0305904034580083c003810903600c2000c0014407080f4075aa010030000c0c0444c1e004038614031080c11314403802012081c0c81c0d020f420840c1d0701400c01010503002d43e803d40746899022003c555541d100fa8041d5405500d03001e842051401d014802074015006140214005503441c000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 308097275 1250 308096025 308096071
    0xf0c0b04150e0f0405041a010b0c03091c0512180609090103060b1f020705040e0705060318030d020708090f03010606081816030c030b0a05101a070605040b 68
    0x322811156411521440803007120002c40304919034441c0701ea4012400b4844081c0c0e036440f4418140118451541c801384815100792001c1c0142c016400f04000b07402c14001901003250100884070064001c451006801d160114200148044550060170b0f40c030915641e48481e0715a007008100d01402c91840040300320000042103000c1c420400c0305600300c1c10840041000500c242c0102c0740c800c800038261500911910403440040c0004212440180d00a2108000900b4584500000b003407450000d0284d540c2860040782940c070000e020001c0c1c3d01c0403011503019070041407080e105440041001590745003954141540e041c2c10030360240c1d1103500c4641c103802092030144a042c084803141c1d00d6055280d82d43e60f40f4900320f10880710b204211406900003580007d0b045040782000f4500c940e921601c0e503070441c1440c4c0700b004030007042c144045103807009002080318440e10010441d40346c464046103000191460040342e00406000514190034503080c00100608a02144c1c422f0074a034803070300b207403100b9902 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 308098525 1250 308097275 308097277
    0x10050109060501140a350406020918090703020607021f2105100306110702090108150106020a050c0603190c110f0c0108010b0d02070203150106090b0705100e010e03070f0c0b 76
    0x42c1c24804110207070b00c0e010007040d00700c09521740d40c21103800e0b101034645865103c1b0740f19541241c04a903d250700161108041c902950b51140042100741603802e03a162803042c0a60b83c242c0b0b4000603101d5000441d5050440d81c8802c00240802004100c40790344c100003001c054003440180040d2102c1c2c4200c0208417a800c0303614454588201c900f2264607440c507185454141c024134018102801c84982081a00b02507111b81501c1e900900c109002010102000c907100b40e100401030300510f04642102481502281c40041c0000511208503442da9880d1107032004400100500803500c283c00e401d020b0044c440e180c125110346910a001c10580b08030310f00751f18810ba2600400c0ca080f90100e40c104005105242c5a507000d803c80c002003c1c1d00601c0c003071164000900c3e00342c100d1610385007002a513006200460340500c4850040c0958020f00c4d040050507654035850320f204c24024282035a68003d0342119003c02d401c02030300c07030080c0e0058941d00ea04a05121103480341c000000d450745810610009007009100c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 308099775 1250 308098525 308098537
    0x30d2a09080c060f16050c040903270803040902030a0617060403030507050c0d1b06061e050f0612270f0115030507120804050a0906030201031a0616051005010906050114 74
    0xf584500e0040d11742e141401000c004101510103116080052036107458030300c02c8550490083c0c0710840004007400c1070011800c00c03034445e5401a000c080042000303401c00000c1e05c06640190f00c0250f180d1381c1e540381c1c0c0002001d140d40321000400b4129126070005001003001c03406240a80c0e020301481d501d142c2c0580c1e0921a4600542050b4882c55001e406e0310300c6180c422031801c10851142820380300c0354440900f0f0301ca27a41c0103a881c909100000190341801078032044010700c400d48490148009010008501c0e0003800d401e03050407061080060714060700c8a00f040c0072019811500811001d030450b00c070f656801540d56a1901d0340c0b071b20700b40c00b05201c4842c1c82c420441c0c2d40309008102c4141498091a8000704e4103504840d0700e03c040c40b010440ea82c4080a07640502004540025124a940001020b0754105081c4000c0c14060410903007032511780a04131000090501d1007075503464914500a4a0000b80450311100d480c5400000b04103001203030440e40464800340ea50345038425605911043c03503c181 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 308101025 1250 308099775 308099797
    0xc07030e090126161403150411040b060c060a0b040b0306011203030222060302070c05040c080103120c05030f030a060b0316080a0f0f0b010210020c030d2a09080c06 72
    0x11550300b0700d10643e8550020700a030508041d12002c0340c13040c1c034040300d48070760382c00907003041200030500304060504101c80d001c40c52428041a81a0030651039280d8900301450900f8061500d6035155023a6071288411a41c001c170200c008c4421382e14100440788024a01061a1849203041940e55192840d0014155040e9001100102c1c42d400050b9015002907101070602d0419215100408109030351030412480100b000752800b594400141c5812140301b00540c206e2403089213403543d10041260f00c40c0d90700781582d138005400100940c14102c01d440310307140307240002d05a200008202880401c4040514060741c40c00005100321521040200360034007080324804d01e044095201030641c1485948004e0304500000300000702508000040d1054030380700d800d5465071343d407117462900c1c0650307042003020441c100c800c80840c100891a00115100d00c40c02c51117440c650740790000e580180141140d900d1a030404101202d0306a008240050180501c034401d200b80ca000e80e42c1d04014500341703c4210343c806886 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 308102275 1250 308101025 308101049
    0x32a0905010e041a1309020d0b0103230a170c1e1c120f06030f0f0c05060f0a1116080d1b0c061803061d07151b1104050c07030e0901 58
    0x10070b420f000e03888045e401d040140c81d8503040c440026807074a84200e03660310f0189031008400d605504004c000c028182020301d480d03440350500300c5078101c408640c1c101c174143c6c0a0740c4c0304820385075940a43c04c40c0c010040910b4103801840007104c00c0f030769903202c045e00840c3c400c800d8500040300c1070360092401514085034408104a00c0003102c5843c0154020003031f80c54002c80004080ea00ea84030f00208a020450440f604c000c806048001e000d01d030060306000304012541382c1c1c07505002c649040880e00401c0110401d200c0211019448010288600e03840e40b07a00e10030004000d40c4da0080315940d03c40341c400800100e600001120701c03001109698491003900111284a803500c0c101d000c50314000300c52000343c3c40350300032040440020391034045c00e008081818880304000b00207011003820107070707070350f0107000301c00c5d00400c48020003504014000c1c8509001d0740310741014001410720f5144024800c805a07800307840d140c02c00c10748120402c09095141d002c0d0352680042c0d00c404041c844524028016050f030100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 308103525 1250 308102275 308102321
    0xa150c2703080706110706090605060405040312020d020f0f04051005040f0b07060b12010e0f0613140307081201060327140a02060c010501060806030304060e01032a0905010e04 77
    0x1a00400616410380318210000d81c2c5c20300800c040016401801c1c0449070030343c45015030740601c4078602036260440002c850030007031410a6540035103900000c2060503207407078010031182c44841440d41920007a1582440d050784c1c2d55800c1f142200d00c1e274800e000391841902c0b041844100b003032141d0143c0d070a0343c4011640868640c284000340104c3e40000394212440c5880d03008605041d26041c15080f04603408000108041440003a0b03103040000e06204409517502220402406a000129031321301d00d60884284200751810000b5035056110381d40000e42070036000142e54040c66000c8140314102d5220395410000d09250b0707070701c46464801c40302661030a1400b032030030b5101181c0310180c20b046404440c0f04503800341207250f0100703101c1d4000d903011101c00e9658500400030075401402c410f034030100c100d0107140f905042200140c000c0c1680c294850405a46140c40d141301c50007000d0a031841c88c064034046038040100007004117038440c28055a400201d6040f21034000382018003649031502e801500c110100c0e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 308104775 1250 308103525 308103533
    0x52d090718142d060d020c01150f08011103060d050c090702060a050703111b03090a0807090e0c0a03060c0504030c090c030f0209011b0c0b0c1e0c091501020a150c2703 73
    0x601704952262071554204042d0801e000c0902c0340203070030a4448684110707549030480d2400c6000195001c842c1d41d07410100740b8000507403120100c0750b008200b02c405c044a44020f04000b40f4100400c00b0280c2c1104002d400d1011407a00016110310805442c0f40034056a40c80f04821000c5e101c0d4040000107165061003600710060544210003880e07400e00c0c00b00c9081c0100080040d0070725503294400d20003500716002c1403041d04050f002d0f0541103a01000109100354545010491118282c4005046160344401c00c2c0050380c0b00304116402140c0000c11040b0094030f5111480082c070103554903401180c41e003140c441d1498194004d4032103001058645403034040800894501c0701c5408113046440a0544001141310090000a40001c0486600030203004050400c0d841c040c800507400d2420f0756000700721541e5580e4030164665401101c221180d2041d6084030700503441c103080e0b0701000b042e00840c0b54000c0348144451748000c4031140a80d0310310201001c40d01280700c0c0310a86206510700d002007404240041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 308106025 1250 308104775 308104777
    0x62d05071713030201050603010212061c12110c180c0f07050312010e0106030e0607030b040b030601231f110f010603050601052d090718142d06 63
    0x65541c20460520301031804001d4400c0411104442001d25400c0d0540500d40d0910546a015034154000c41c81c1c2500024002800308000780202e00c250352001c070180140812000042c0c7c415407010961111440030540685140d10b07040c4000200e00c031301c0028080900e000b40040006402100d0100082c0e15040c501480c1b40d448009491905a01004010002003007000107007020b100e625900e0301c040d4180384c03030b003503240006038041c10407d4200912641580d00100382250010310030f0400080480309000420007410a0030055a454011180006280e9040c41c0540d0142c807088110080c040507040d041000205404010030344501c09104110394480c0180342044d590403810040305c2c0340b41050400a8251000e6400443e0103400c0080104a01d04280c2c1941003800907100104042e82d00c550780c00c001c11040607030900e110b05800c00c0400c0c5824080c03500803001e46100d0303444410042c1c40d00d0707003801d454400f003032440c5c02900c012407040a603447c207118085140c00000d95800004c00c0604c100030309 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 308107275 1250 308106025 308106031
    0x1b020103020c07170d030b2227050d08011d011707030b070e0a09020403020d17090d030201050103051204030f03111516020708011109040207082104062d05 68
    0x10b2071103250404600c042a81d1007020324100c0510060401c5080700b04c009007600c2540c0c042c20300070303180f0101c0b620b03120444036021b120201c00c031400041d914062100d0f0103000c1c4050b5600070020101ea2500800f440000308042c1508001c039101e150003640e89580310995051048038256081e03d03100b0043c00300c4800300c1606c0c01c01c002a01e003180d10346a200d4807a41980c1c001a038542021403c0b2001c0303055a42006014080244000c4a003107050514503004100d00f070309134040003844405803010601d19094510241c0d4007210002c0c126640950241ca8040d0081070f013800180c91030b100f6464461220741c1c03042d04860a80360f00200b54104440c403a03605030341418ad001c0812900303015500c44108001c551801c9103101e081c0a8401c020000c0000700041d040546c3c84d000075840c0d0b4148050b100c82c1103295002c803413580509440040e940d401d1414540c44034092030445001d1841c251100d501d030b2410240d4400d02460140c0020422185c01c100400c82a4207002129080070311a84141004002c00d41c1c051380e8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 308108525 1250 308107275 308107297
    0x7051b190b19051e0c03040c030b0a0e01110c011505060406080901180b15010804080a0507020310061217070c03080c012d06060801050a050d1a0a1a011b02010302 71
    0x12610408052090a83d072080711030400102c00104007100d41000f008081da0030280090205155003410b07190201281401e000c05800070b900c680209681c0500c40d4001c00c040d6981d80b0082010020544652219501c40900018150300b0301c03843c550f0030240704203038400700c82c0020300c5545818078241c4203440d0303050000d058510301d568a1152614015a0300175043ca8240316110288261a1184c64044000d10a20303285e8108103043d410000080c2101c6d0441d819140f150600380d0300e42c00380d8400285490604a030454155040c140d00048503881c024800031214411281e0009032070407041d0a02c041c5c054050083c021b904110420408240410f0050400806100010a814000241c04041e258030005980e00c20f4103051750600038010070344501c00203080c0c1072418000791752411000a503248098040c0c140300d1102d04e01114100004884a007144120810595040b40b40142d40c1d50024051031b0b40104052030603005408556101d440e8041110b103030241c4065460b940e5400450083d00710f803844203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 308109775 1250 308108525 308108551
    0x20a090f1515210f05060103060b030f1f090e07050907020d02070330020a020f0402090102060105270f010f090603050a1b120b040203010605180a02130b0307051b190b 73
    0x40e00c01d042d034001e007130102e8912400810582001c00005085440e10362100724201d90278030a11003401915821503400824100c810031040404034082040311500c1d5000719a12071600590001c1203001292000880301e0444500ba1903954070300303080e40c85680d90010752005822188007840051500c0110900310194040b107241c80020540c40c81002003030030000100942d1080c001c0c1e10843c6010318614240d2041aa8158103004903000080d40d19001070142c0307441240c500888070039909080c4c034000500b191801c008402420400b00c502c0c840c41080c040c4940c0c0c03542d00702c40480c02c2112402448102ea9000c00100004400d0743c0342c82040f03881d80890340042c184e03c61000210b07000c086401002e124040c00c0c03d800f503802c0c07501c100741c00c544941c2c1c03046004115021607036003a0300c01046040e90129803101c0259072840f44d103900907214040c540000312900c101000b03101603103900c20007400c0412a440390319008a07200a1f03a141e6594481c0b11004d880c010074220900020b551081a5900034000308444 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 308111025 1250 308109775 308109827
    0x507060c02101d070603061202042403030f08010603050c0f0903070e072001050402061b150115080f060307050d0201140301030b0402150702010c0f02030a020a090f1515 74
    0x341096501c1c40f8020112a00990800008071005109082c010300d0030b410100295481c14820a4120b0601ea1004e4825580e442c0c03030308120902d8201d03061181d403007100c002001c41e80301c2c680900200e1581d0301102c0007a1600b0001320382c4074001c0c4103d03401480c800d0901410140142e0180030680c2c0300c4600b0b16094041c10b400007030f00c58201400f160041c800c90300e90491401040c03142d0b00c1086190080300110303070b042409010141e2604011100070111202c008030a1000743d040141c5041000c00440c40c02c141441c0000615980d15041121401d0a40d603554210b502c0300d4148414016040e5404c81e4980c2284134100041c2c601404021102d41c410705200740c1c04040c1c80d21080d03480c2c001340d0041c0c078107401c41010071003186010001c0c181c1100980d24580d0810030b2030317000284183c0744858002c041d1800e0103111010b654040000c509000e60041030003014a071120249000340602d4014058041c1c14520b606141031701100410040d00c82c80b4080341501c081030f80f41101e244441c0500034101c4881d004071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 308112275 1250 308111025 308111053
    0x4030516020d0f0602191b0b18030a0807030b1206010b03190203090706110a0b0c03040c050409050a0204061401050708030403140f130b070305030a0f0e0f21040302010507060c02 78
    0xc000d562400343c0b074010f84540c101c4030091001a1b10201e02800c0042d040c000c0100307440e06043c0c0c500c540d80c0140c4a005640e6507488086206101240c03116030742d100210340c5412681c5c0c03090742d0340d12941700c50303600340110340e82e100600100381d000850240003900094011b10841e90400042d660012108041a86400040340c0400c200d900541d80010a600f05036014003501e500311350504004a2820001d003040b490940f100c87c1924000b52130700109910020108060101424181c2c0103401f00410810600c4644e08d000c60b40c519401004074021800c0040000346002d8220683c2c091141c180c4816240410a030f440b510283d100400c21010b10150803840011041100c0203402000040c4200603901d6200b400007050710003040d8042100d8003010810346000941c01400d603600b2000c50200420031481840316040076100009402c0410303c10700b03213820340301c00c000500c2c00f000e605009102c04446042c546110001d02c01ca000c0a8040b036010000e81000810a07072100c55a00740c0e83c81522507008000314 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 308113525 1250 308112275 308112293
    0x403030b0d0615080d050d050c040315020d050117071a0706060b12100f17011b03150803090303030705161505011701051909030912050f0706050304030516020d 70
    0x50305070303038043e40c9980c0c03108030030700d100d481501401c018002480701d8440b4030001000c030722a0001c0b1034065074840b00032425041000c410750f00a56480301050f07003906070000410000750021003030500500d0500c0c0c00001c0d5100e090300c02c814919804000740c40e07000e05089486c007010018200300c0301c03503c1040003000041000c3c3d1044c8006428803404061352001d07520300c222200c1d2000b030410700314450340e52000c0041d070424000110407140d02e00d02004c8045101c0301082e00500e101c040c1d926241010075001580c083d07055001c0141e4185200300300310400e484428240d82d90164200f469015072040003c141005e020700040c084043d0004020050401030b5510540ca910600e81c00909039900c400061100340180307042002e460300c94200801051034030500c124450070307151615842555442c004201811320034403020002c0c01807245031203c0154180b421079960502c0054400c01400b4906000c0f400e641b150b82164000c941551300c403824440800007101e00700780c0c800000c991042800381e204d400949211 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 308114775 1250 308113525 308113549
    0x50901090504140106080f0702150702030c0616090e1005010c05030409020f0a030f0c0807140f0c0706080702030f030406020a09031b06020c0d0507150e12210301030b0f0403030b 78
    0x1c1c03000d42107949030085c00f420300720780507207811002c003440001c00510720750014580d003842d4500041e85640d61184c00b801d9046110f081e00b4003c15000d00700c10040c081c440058502c0000c180f030342c0c82c1050a81d0b600303a980450201a2150f02544031300080801c150b610a100710a034150150041d2850f150741c43d550f44081fa408400c030300003101000700e8843d5070b068041c401c030081e01c441000c1c14400d8080b0604020500c00000740182d0a0000c400c00100300d195210b0160340f8032030000302c0c0095a6130384411383d95075901080d10034000050280300000e0003092012041d28580c0901064007801c60703e507035031000040e402c40d04c40b440400281d07640020118074520102d00d6408009070289942500300300c0028200320701d0200e424010340002c02906c00083d0000b030000c1c120750100c940b403260f142c2c00401c2100d00302d1168405980c8040154041603a864011542d00c1d00315050001c208010203211400c508640000d10029101502a500007145405008c0049030b0041c403c1c40c0000b580c0300c0110000307011001407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 308116025 1250 308114775 308114801
    0xf09130501090b040606050901030e010e0f100e0c010207060e030c0a03030309060c031e0b0a03050f0708011a0604120f240b04050402032505041b030b0f030c01050901090504 76
    0x140d0010401060144202c200c030403400e940a02400d401c00078054000c2c4541003c0350b041580d5210190300700c100a5020b42c00320f81710358013654404814131742d00c581c4d030b82503440c400b44400d850712049a42c2d8400000741d02ca0050010b801820706d0302d180c860103a0b40d040caa5504181c050140d0414030482e640d40d00c5002001d14800e0b1000208000941042011030b44184164400e140c80c10341c0c0320041c56119403820f0900c142c151000321744030b00c2c0c48000c0b60b40803100f07a100522510a2704944c0003042e4001c1081019901494002c000b0f02c0a04041d03d491a1f003c04100d5410000400c000d00030011080040c08840d405815505241480b075030300ea030705814201d086440107004010054904100602401241a00c111014401c2e8142500002e448001d61021500c07000b00e1880803180760101d0004100040c540203008100e58443c45c9105002c0a020585580010385060320640f514906024006010030000d00217118900c649001074845a10080780380d07051040e00a40010741d0b0341c07540503c1c2250904 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 308117275 1250 308116025 308116031
    0xf12080c0607030606020d02070806061c1205031e070e040c020f0703150f06180903120e010515090403020a030813080c07090b0d11090a0e030c1c0311040b0f0913 71
    0x17500074007d041850a64211086400c0b42e581005104000142d840d00001c0448081001c0e82c00c1d0070060051028810004200030640c8285160940d040070246108541401c00f0040e400d4903921030020b00c60040342c0c48400705103014070751103090800b580308071504800740c0120303461200808442450100d03143e204403800401c507181c031902c0314514020700001c0b0309112001c0c0300c42800c0c1020300c084552529814001147e50b00240c400749440303241034500c1748610dc4010040440d201d051940600811035241c0e00311490051156828100342c803070548600c0c1c250740a00040d907050f517401c49464202403c2c40c3c0860701c0d0354805001080c01c5a0003040d038500141c004100c034901d841034040c2074452264140f4401c0c1c0c040410300d40811004810f901d554507040b40e4110f00384d65020040380040140c0400c20010784804545208100400288000b620000d0300a00044803500b9800b1416100c0b8040c241d40030842c01c1c003041140b40c08a20150400448034a100b80c106001c80c8041420700c40314801911a19403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 308118525 1250 308117275 308117279
    0x114010f090b090408090f100302040f050111030a030b010905120a140c0d080a090e0108031b01110a030908090d0308150f012a0606060e031002040f12080c06070306 72
    0x4088030340c000925040c0401d200d01c1c0b14450018141074030040024003070182c0050034280c6030361001c6c04c006041c000284250155249010001d000750054040c40b4a880c544001c003046941c000c0e0f0000d900c100003500114580412414114003502c0600481c5051002004022455940300f1140c201840740b02d400810a01c0d070303241000b0786e50200e048001501a049202c0c590b40c1034452803a0300d051260090340300b80c0e40301d10308e0030100c40c1c412040e484000051a6240041036a04000c00141002c142d80120b050003688078010072400c03101036400c84007280e2401c02c24480d519000350002c2850340e0044c1d18035800c1501400c0401e034a00801d020440c0014078050401c01384000d10404100412025540b03104904a03440002e03000e00c00010115510b1328800200718286080a00161403240d400300e41804050382e02c00001e041880b112203417503c40d0182c14100701e41da000510a5a080340e04840e15240e4507071810a180d2080c52024606440901040003400a11501001001d0013484d41d5607001401034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 308119775 1250 308118525 308118539
    0x4110a05210a06020a3207140313060509030d080f011202010e09070906080705040501020318040e0f0f070902030c030105040914011401050a0b03040b071d041103100f032d05011401 79
    0x60403100b92001504106c4807810b6081c03900415680301c1680301740040c0c10103060400d850b25500403184020b4011410385008141d5903404009003020b200190304442050310071060503540c4400c120f80104e03d994181004100341f8850504c85456a80181410301085100728081500c4100c1140d240001c984d40c02c40402c0010340c0a1307a13180d40440a49041800c10703080c980001d45921480c9040051900352465020343e682d40c0741d0218000600400c112051007801c001801d481c2c001d2085035456238000c20900045401355402124801d00c48a8411881c40c1e0809003000020428041309440100840501d0f40e8418024811185645003400b882c4000b0740c50582005842c59141d00b00d0201c10005005010001d0544003005030040c619081894118284a42c0e4502410303500806036409420301501d0803c2e0000040254001e100b81c205514144e82ca95078130810b440711030b110040c40c0c2980005110080840100308464200358003440c401424080d031215801e4803029043e08031103499800042000d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 308121025 1250 308119775 308119817
    0xf0d021306020604120c03090803031611070302031c02120c030c0601090903080708060312040905061009060503011e15030515030d020a14010f1404110a05210a06020a 73
    0x81c0800e01c000d01081c502070307407803207001d224841403a4113008680848004042c0154a01d9018100b2001226140d140440300015a8800424103101044689400088920002c03a07980c0603a80c0181c0141004000c0c0c040d400344a59011f524101140103140b0401d0480c44e081000b4901304110320300642d100d0840d051070380c2c148541a40440191841c0101810000c0d40000206a00c100c0c0da08003000103503540d401103401d2002e8587d00388141742c000100441c54840c0d5a110360701401d01680c080344c000708804c9007034612107898012180031420a01c0104041003a5851950381c10200c1d140b2104142ea0381d01d4000303e40b20b400c46059000c00c0c1c5542c2000718000700100c04d4403903000d0480c002c0c001d242c8004c0c4041d4444001e000d01400c0c071065500e82c043c1601c2d09400c0300c100ea41c0003000410110b14030380000d0205910a54044079080040d0683c00d03200d290094480d030035114002d2101c0500c004080300713400c1008000c4100d0010f8012450440c01080c60307032020f040c13401c01c0364507100d851150301c254485003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 308122275 1250 308121025 308121029
    0x19090509010609061404051c2d060b180c04170f1e0f0102130608071805040b010c290a060f05091e01030c061818020702060c07151101020307080402010e01050f0d0213 73
    0xe2040c1c0302701c1d032034800c0391440f030307916800c00b2001400c403a982001ca6040b03500c1c0141d541c0d5801c0c0322030030f04c40c2141700940103004a4222000600f14900c40e401e00c0380d120140c900c4442c05591040c0c0b007001142c20311044510b61450a2001ca035000c000030260242a81c22486846641c200b01910402c8019007240c10207a104182d403500c007a1071184002844688401400344501890740c641d6200030a0340210f459215164103c000103131841441c01030801c2c400d400c51240120444c1e07140104000701002d000e01d5040d60b0500e000c4c4103486081105114129800400c20400360b020700013802508424010f07454080c5008840c0e054009080100141c40ca250400800c84900d00c4100304101d260b1003c00d0006e0313031074441c240250b52030956000180d1079010300401c260040c01180c100040d8850007040074000000d403515078684c1c032802c000d24a4200c0c00b04407007c0000c0384640000400661094002c00c00b1710300c0506140d0300348490752503415200d80040440c03844456000440c2000c6e98201968140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 308123525 1250 308122275 308122313
    0x80c1504051e03160803061302030c04061e0503040314121806010f08060103020907090b0d060e0a020a0f0e0102010608010204141206010515130302040219090509010609061404051c 79
    0x12504080b0840f524195001d02e1300a00413850120201d55141d0311b807900314030011004041591241000d080042940e409403040c0340110301d000c0848107442c641c01900032068034003910f815003540e9860300c094564901821101c070003100108440360088411584181c0070310008080065008001f0074264079010043e001810281d000c2034007041140c400141050650f58141c0300c80190b51900e00007540c10920b2604124038641000c00c807042044110317404501121f10a20f40c3c0421ba443d2002105c00301c0c420000c402c40060141100800c4090040140300320085040c80005007003507449818508a0300507070002c1418482c1c00c8001002441e0060030354051600c22009030540754580b40026a03205551b00301180d01171000303e0101403503000030385140001c42d0050802d650f0740c402d1022204401100800c0c89001c180503036130118440c144241002c1c141e0300151140c00078a401e2240a0b65900405501d44490070b0701000041255129001c1c2124942005244c41c2540046c0d45404210072000c0f4400308 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 308124775 1250 308123525 308123527
    0x40509070f030e0606030706030b03010204050a06050a03050106031109040902302413080d0c08010e0a060f05132307230708070819080117060402030a080c1504051e03 73
    0x102d43c0c0c0072810700108c0d9050700b0005500e6003041c002c45e019016940c003181d4000d511040029000390020020030400d03e4a0740d08001ea607884402c183d04a0300404030714040d1450500800c10141004d40c0b2103816540000d118a2001c138480e0101c6040300584058448441c00031000280c0d400c4082186903e8a440c2c0f440c445040b402c0d03114800c440d4600148650010f1202109102c144172500d030440748110800c000a1000400e002030140c002c00d0281314022180ca84800040c0c28200148103902c2650401c81000c00004d142c441000000610710484440c7c0340e070b851004c48200404009a0b4070303200b5040440000c80e1030030a20207024040e031803092400ba404811400d4040421400844103007039841400e03035031a00307038508002c4070700c0c001c02185014000c25000b44851303450300088501d04a90480c1c0401c422100c4c40e4031400d40700c510541c0d00031b4042c1d0084c210400042d80d000042c000003505e540444210301102002041030090554003514180c005582d03c0400021640326000c0b00442c50b4011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 308126025 1250 308124775 308124781
    0x207090e150709030f0503090901050f010f050a05040806040b15010c0b16030f0e060415090c0504090f02060d0b010e1203070b15100306140306070801090f02040509070f030e06 77
    0x10381c48401c16030400710500301200000b882e4070f004620800145030031a0000009945900d00243d503a0302000c080c9108a8440c000000c8620300f0032003010b10303088181d50304015404041002c1d116600115000402d000e0203100c0490314003020001244124000c94914405082042402d44d180c0031841880b07041000310303244440403c40e4050f40980005d1030594042070f008d1130b524110014902015410381d26818044003811042c40000c0003805503004240011030395002c0e100460844d180000002c0103240c1f07403081007041c1c5c03070191701007402140a03800c50004c0c20815070024a099005005030b4275030642d140140c1c030881d6803201d40f801d9000d001343e55004101c20421030580d5a40a5440d004068410250020350510070080ba0140f032b110b0301818045000e100508050043c0000340140507803c2c0e280c10b00b100f00391500060303943c041c603425110070881da420320703480c0780160400d0322024007901e40030440010340f915514821403140149507120328648054201c0241521600082d001d190341c818400c2c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 308127275 1250 308126025 308126051
    0x302041203050d02070b01030f0201090f0617180d0f08010503060403170403030b0306070e13060b190207030c0306290108060d03030e060403110f2125080a020709 71
    0x200c00580d01401c1142e201d01079103c030031002c0e100b0300f580140400b280700c000000700701c043c0312031203050f41c800d032210702c000d540b503102e80c1e41204881d106000000d580800000e101d410305014041c0c020042042003854020b4408820385403080300d4010100003104440c05030307240d0360310000700c03030141074120081c200509250b1402080c4054200c1410304a8008901180801d80268814540004042c05071130040c0303803e600c0a4440c280050019003c1c500544810100204510610007510000c2c0d100c1030400c0c507000d15500070070f0741e181e8085080d403040046c0400414600f080c103200840c071412002c07030b42d0301c020116800158010049070706910240b001c115116030301300c4080341d8131150039034000c0c020031141d0600310b014249c8850302c10154050081408181036110180b204186071010031144802c04003220740340e40f01050141c400c030340c1c03500144400e242c003840001007400d055420050251610b0f01001e840102210400031554080001841039800307070140101c5000308501d100c100a0001c40c611 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 308128525 1250 308127275 308127299
    0x3070f0509160c020a080705040c020f070605070c09140a0c05091003020306030c1c020907020a0b0c07081c09060e070509010e06040e0307050f150106170709090c0503040b07030204 79
    0x30040444030314030480d40ea07041c0305105103c1d0b080c0d00104040e9070550b85200e025100d0000340a1580070343d0400c891140624000180745a90a100a00612a517850008100c444c0e80110804488070001c0c0c00c0f000407240d15501504070303410008103c0d00c1841c00e14002071000c50300c0e4080000c00b44601031244000c1c3c2e5031803421290801d0060309000d81e60f0340c1c2d0a00001e05104040d0084d03944543e40040ba4480703088007002503999580b098550241d1a210701100307036078414a2904c01825030040b03400194625501780050003500b446002e100c0d040c10030311640b402c00304011031100c1b00042e942d0042e14060040030301900c0258140341d0040c040031341c01d20000c0394442c18140103000144001c0707000300da51030f05ca0754840c00d020400c0d8001d403611030341c0b02d29005480726248112055948100c000895062a500c07028078125202030300d913280050742981d00d10b070800d030340200f8031001d20604900003c1c00305582d004a0941901c2c40d03803490b68038645890a03040100c0302402c44000c040c4144028031070062960 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 308129775 1250 308128525 308128531
    0x324040e101104080d030504150204151103040f06080f0f0106020a06110c03030c18010201060b0d230129040f03030809010b060f0c19020f010c02210c03070f0509 71
    0x264045a03200c409080040248203031340c8180d456110715030b40d40703035420352503407080f40160711464060b0362104d40c040a007004c0e801030340035066880b120090308a880d40c1c000c0c004030719900b07805415079082582d19a4030b00c2c10010564002000715925608100c400301e04140b4031035000d410380007800c045505240c002035031035032002001001c080e580e84541b0120840c907410303580e01c00080c004481d034030703d00b0b04a1408140c01c0048051030b18a88250032040303560060051405442c080d0468505046002d060b84025101211101001580ca610344100c2054030156007030103400c40070f80403a40803500440711864125100076808403148140400c0c045c025180030030404503034042c80c001d117460b00c50080040c014001040c0f483d901c95400141030b820036a2460281207290400029a00003164815445c80c081800d0200258080398940c1031004642c041c01501c0c030458000fa003031400a08020f59852a6823010309002c550650046400c4201071404100e0540503215031540118803074500004116120b03005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 308131025 1250 308129775 308129803
    0x280807030e0607081501050d060b041805090a0303050c09040912090501030b03070e090f0604030c150b0f060c0c0d060b03010b0d050a0818100e01120b030715020c03030324040e 77
    0x1401071045580c440d105940d52140719110030889c6551318074603000194428030800c1c100000b001d0106001c0001e0748641840703150b450000e03028880650360214001c0000918400c1103d00912005400340c41c0d912030038100038812154105030316000100034010305000c1d03102c10704050512014001c6502c0c08a03005080319482d0040c04a95201c0d030b030246040c1264030310400f10500c02d071410002490b03804410012a02c2c05000c00c0381c0d0024400100c041561a084215a00000c480901c3d510381e0a01000a210442040044da0340b04669180021080b8015290584000d901d410881c00c140c6001e2045012044040b02c41d10040c038499a81c903521140116400342c8940408988015180c81031808008207101c01408409624030309000a4103000e980602140064090400880c0011480c031910f82d80e200010002c09126103000c4400109031814107104003140601407000507036032010005140900d50100001c40402075904403600741590460f00207204174101500e2005400c1c0116180150000b4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 308132275 1250 308131025 308131051
    0x1506080606070f0f140d180e0705180109051806030114040f06152c0609070e0f06092e08070c030c0201020a1502040503011107021005280807030e060708 67
    0x66420300805e0843c01e0120107185000d02514038900c40e0f44100d10100b903a1201e046540c03140e403941d0719440c18146c1202e034034001c61010494a8103039101c1d018104400d0070145002d505c80fa031a00003040742003490306401117181410703d0910203180f800b80100301e2401c6191401c10b403141780944503030302a480c1c05140a000c3c03503038569030117070b003408440001c0c1c025002051840840c61a0a002055584195005120411203240100d512490a006c80740c0c000c04c2c20366151072000c10410204840121810001e40d84a0407c0001c8151a2100c4000c8081090f402c00714420702c00c48a540051032a031016010410050a1410048060707004020070108542614015803108598030040c0e01d03000d121880a0613440000d4041c5248207059001007054070310a07002441461503c03401d244d182c1c010324000941c0115030b900c2030015603100b10050040304d015012000c00101903540a10011441800c22200084c001400c01c11499018010031070100d0240000308118588a8002007404001410030045092 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 308133525 1250 308132275 308132303
    0x4020d020607110604030b0708090703030504180b030d020304150305040218070507060504080406110c03151b0f09180f0415020706060f0609120b0609060109091506080606070f 77
    0x1810400265060700646019501c0380c40341070407d0a008111002000a220180001e4010102003030000440e40c0c5522641d0802d410f02c054031920400e050880b080465a030301c1ca070202e641e802c2006481041107034001e550b0b5141000803400c0e6800c18051900d00381350810040c0030060310b62102e0340b5004c9070032400549160700c03912070450360352150384c5025000f10b08003803d03c003e1107555030080003255400c0d10b032503030f02941c400221516064441c00c2158940c1000144040360340c3c442d004540d000c00c602c4441c90702c0c0c0180b15510300c170940180543e118054030104a550440c24100c4640100072119460707041c503403030500400c4501c40b0001700014030400740b000150001c0c031101c1d01660082588002c05000c07064072401c40b0843d800f1103100d00400511111000200300040107650b9680707a404c20600d0342d55948090500ca424140030700020704106510304006a4400c2c01d105481e00134540d0030343d0801107880c0c10801041079001902d420321400c0200324207800906240d0041e8035480c0e0000148030318034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 308134775 1250 308133525 308133533
    0x1b0e06070201090b0a0908010c090e040602030718090204030b060603091906020d06030807061107030914150c01050f07030e0c011b0c121506050108010b130801240b0304020d020607 79
    0x3010030b60255a00010116120f16550f4111006c44240c035030700b9000b040000d060302c604030b072012810300c500041c00c1c0102e004070b0003240158000316480461030510b078072840007085070205020000e9004d400c41c684e0100e41801082107070121950440400c9400505505052503496100d66402d85201240440340c48110100490340e010b03a01b07000d904400400c00305581c0d00700107030254401501164103500d002c04c059440d92090307043d80c0030070360076984103000c003800c1c0001002a0800d411916900c420003110070018003010000401740b8005038000851241400e2000300b500400c0901800241400e24180c04065840010f0300c8680303a40074601128003050001101d44a042d01c50303000307405039000c050041452207103000000c840300d1088c0c1a0105200c0ba900d1350800711800d078010240041c04031001000318030640b0340902500c19001c6e580da0341440d6140c4100c3e0842e0a641d0540325001d82da400e0000c48894120b04590050000184052544c0341030707800140c1c0724040900081c8078100c0410700000340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 308136025 1250 308134775 308134787
    0x150f030e030a02010b1323040302010b040f1418030d020d0914010902010f080c070303020702032a031204030c0504020309030c03071b05030c0a0b0f2206031b0e06070201 74
    0x10118010741e6591210244001d02a28038400b5590041d0b0b4040b0700880c81240611550101034281840da0000e4130035204644e0a000005c3d006604640d02c8600c030022550303540c42074040d6410325007000105002081c601c00e03c3d0400c0202a2291000340604200c44a00c000c07049511a16802400603540c01702018040300810781c1c0803029007054103420f10800c81c0c06055000840050007600e50a5420b02c0c1c07001f040b134101908503103505a000043c0b010348006402900034096440c8010162154550541c01d10b070220b10402c141018032f158101400c0c0703500e080500903207040c034403103088252800c0d0540e100c82505410038803525000c1c0358000b0000c4c00b001c00c107009680380e03180d10505036a5102c4c1c060600c03601c00214207455034044040e9802c005854900051641c1c1d01010290079a0000c134640404811190000c0000742c545540401031964280b00328aa030074035850403860170004141c100030008040750030700c002803000200801403605100fa00a4040c070f040400c110384495955520f880104c0d08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 308137275 1250 308136025 308136041
    0x30506040612050f0715021504060b040f0b0406090b0a03260f03010503101a220c020f0f0708060c09040204170123070516050106030b25030501150f03 66
    0x5030181c41c9450b20200320003c1140c1ca9401c10031300031100b1031600d5051615080c420520034402591060450032082d4140f0030007503501c240100400140030100b42d01040c251a0080074440c140c980d199180f880614091003a00c2c0a030540450800001d224100414018502800064882c07159000c8581040072010032201400000d02041600d8440c4840380d081c454000307025240c030901410564000503110342c405c0c1c2c0342c1100c152982c1000c0c08640d40c10712101c2d50b81e0b4000580400c0000c0d03a001000515401080380c91019507008040240c0364504840c200480d004659541d900f141c00d04002100000820607008079034041c0320b91b41c4440c800000b80003441107500544030710000c2020310b00d000d2419807006190040312540c0c044100042040e030300041c0760844038400482c10900075145100444580203900f05d21030000090300640781c6c0c80740c00c8804811030b010307010000312070030001c44038907a840131040a0300c1c0d60800703204070750502e4a07410301ba6041080384010480c4243c440d9140a10a80003120 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 308138525 1250 308137275 308137289
    0x60e190b06160812090d090b0c01290301060e1015170411030d08040305041802070c030516120510050601030f1406031b0a05010e06070501060605040e010603050f04030305060406 78
    0xa080c1124070b0f01c01d6007504040c0c604a04900b0301c07000a002c84002260038680546166241ea640c42d00340011014075401c03101f2007001039940c40d403a1492600900c05140c0200da4a080c140401042000c2010300b940c450360030800c00f01588030b003070240c0440708420000607902450009554542178034021a580c040c00900d01c1c800741b03070000a1106000300b88178840710140e420380941c1c0c01141042d10644440d0400e540003000104200400c2003160203049042844200c400800f5280ca035458840032405105031700b05940c60b401c503039078412400450840b00300040403446000061203441d6120a41c840001495004150307454500280c010ba100e9800140d85642c071400400801c03100c0054807485000440305a03000c0d20464412401c0241c1c0d00d155807110b07036801002c0048032814600110b6840401c4202e0036000141808101c00017402070081c04058040c0d503544a4030341c3d2406200000460701a8042020b0501c3c1c00d0900003400d05000d0070715030098250030089102d40302c0e030011600615095000300303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 308139775 1250 308138525 308138557
    0x100f0b041802041e061211010816080702031c0617120703050a031d07180605030a1205190e0f090402060904150f1e06020105070c0609050118060c03060e190b06 70
    0x2268908000c1b80c5415402d0140061041480b035200c019210400161036240400002d84d8a1902c0c1c0d61040303420740d5200c1800c2c13040da8180304139207186c044240a02c09030307500c030141c035000103010171402d50700c00b0240d40b0110740003800e0001c41011401e00c00e1140c89805802c11800180390341ca014041d8103c480078100081495840383c558605140e1074103414050200d038500300e20011041d041031801070710150303072004010f440804800c1d0b8644908204101300d1409000d400d0088140001c1c0e400991030700e12039182c440c14010718400c006c201c40301541a046620a03445113040c8809030311080c0c16200b01e09400e48001680d5111050321003401d9800c0e906c029a030000c0c014001c9810728200001c140400b880c07110711008552980c0040c2d0984408542d0080094580140b40d0041030168200070071903409000000341c4444219031100214103240e00654840341c68006800007940d15100709070040c82150300038845070602d403006211401c05540c101040b15107071491102140c1d41c0301c00300c5d210003040101c04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 308141025 1250 308139775 308139779
    0x20f1209191e0c030f020906190504023709090504120e0301152706030b06090c04050a0e16080f16090b03070804020a0801020715180203100f0b041802041e06 69
    0x345595001c682c089001c3d5050f00b0104040d810b1410b4842c21027007100880450791802c0c50244002504a189000c0e81c941000c0c410311400b8845001002000002c80403580c080e8400c1078010f0040302403035101c0001c60b49030000f000046040401c044440c8040d5203010514541d54000103405004004040780c815602c40d4400110321010f0040c618581100200461000c4d180c49040d90843c0c145101c042c0242e8040c1000030b11a28041d00015886142c00108508040e244d41c00700d105126a900505100c1c2803000502c0400e024100c0c40a4941e0048d2406100341c1c9480c0d4415400c900028000e0740d5000020f00402105074024208800234114034280d0301d40302d28000c600285000c3e4151030903130042e004004045000e040600803190840d4010f440081e113841003404000c02081c283c1c04049180c110b845200c4010b9505001c24103140d800000b010848105082c3c1140c122509d820741c2611542c030303088400c1d2280c2c03988000701015940440740040d40710313640789401c03200c40307104000007124278900000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 308142275 1250 308141025 308141033
    0x507050d0e0307050c0918030301030b0a1103060d110321031b070b0106080c09040509010c1107030f020405090c0d0606080c0a0e060f06040801020f1209191e0c03 71
    0x2410316002401401d114035694850025101d2240c3c400181c041d0f005201a801c09003803170001150007856402039220f10400000b4580e007503400c03c1e04110380354006001808002e00303950268050040302000441d2a50409000092822840c807030010250307020100700c09001d94040c814400b1328480550302c000d80e00e40340c181c6100c1d56030088483e104040da1400c0c200f1081c10303803541501c100503440003040708940d003006000d4410704402007039180c038190208216030303042d140ca0040500440300c0364008100c00345003801c00380050004458504041d40029030800100d06940c40f4801b07484d4040e1400141500c40070845414450f90f281c040d90807031001c07042c4004110059000300100c8012605407918011000c04001c0c07401980d1061600512401001c04c22030f20f0031050310010110000c1c9054501540c03401c0c0542681c1200141c4201c203a008607a45803c40480d4164aa00580210203040321f43d0700084100c686d07221600f40030740341d014407030948082040c1c903400c2600c01c25000040e1201640c1d903498 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 308143525 1250 308142275 308142277
    0x120b0d061b03060b0a0c0f21030506040203070207060e0402040323070e0105210705041e0509010b01020a29190f0b03071a0d060f0e090604030905150d050705 69
    0x10018102003407000285552082c81040f0940740d500d0340c840d11300f40700b100d412184200c191005075404100e1030742060004900d60307021b4a01c4400c8001011281e41d0440003d4201ca000034000340c00b45004004000407698041156030a031002820181c04641143e000b14009020b83e4100810070454010811950303c111110480d22904020499500c03985800c1c0c1144114000c3c1328094007c02038240c02c5031001031810145555160134011034680070f175500d0001c1d0170340e140c0c400c181109610401c80a0b049130610f0154070740c8140d03050f0080c0856030130300740000d664002c05e80005e028040c00707032940c96820f0403120f410260b0340008000000f42d400c0801084000091140303401020341c1c42c14641901c200554000d602c0941d00040103002c0692030000c6001080f11050540100310004000c2010244070b83d20506024107900406200c0301424103001483d601c030301030b080d030031241c0c440030070040020b901c5421007041e2141501e0703a850301c3c040107007141050b0081950000d10513003064100001150700c01c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 308144775 1250 308143525 308143541
    0xb03010b0c060709030203060610180b0c0c04060503030d0209030304030f03050910110a080a0306050301050c0c0106061d30060402030d05070b010905070e0a0b0a022a01120b0d06 78
    0x41550801d80310340f0000d4a854080303100007501030b0044400100185419060700000c0d22080c02d01060200141007145a04555078200c002c3e03420300032580c0c02c0d59072000c101c440d8600f58269400c116980c140b40001c2e80d20f020700c3c003100c0b95081d00050f4514040d1002d0090702c00860380070800c507810f6440f5140160031130300511810b80c01000640d0325010040d05c21800380c1c034240d0840f8042e01341e5428079140c00307140780e0080140c50207040d1103050006080d1400d01c900f0340700e180451411070310342048124203400e40714542d01034401c008119500804a0444071410a000c06040305d01d07003034004030600d40042841d01081043c45055610300c460314007039804121a0f100d10b108605945150324016000c1c3c405018000c0b000c0c0264018400511a0300c04d1f603441a500300c031080c20a0400000090000349555040e41c03c0520a58400300708201d4103a010070402c600031400c1001c2d0600d108001111642d6900124181410814004c03581081d00314681d1285156005c0500320402c2c030300c40c03401c6c40f01c082c7c113600d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 308146025 1250 308144775 308144797
    0xc0305030414130203070e0f031e0a0203060c0a0f050c0114011e0b0f0a030209190b040303080105031b010c2a080f150708041a15010e0a0f06030f02040b03010b 70
    0x40800c1841c003104601c00c17070780b041c04d65854148500c02c1603410b00075141c002c000495003501c1004401c446c031220350801c607078403035158a0040440d1010341c4141400c100c0080d02c040e4268005108400c00c2e142c00007000d5100c0704562420645805a10198a0140a8110402d12803035100e030000705580710310700c0f4001c19944403107500b48043c82d07441216810324841c98210100c0908284500107003107200b0b0700180600a8020842003008a4100e04201801c203143c2c1300b5021520300203000c20030507802909681c0100809c801601c0211581500e0344926464148020f0420a8a015040400025043c480180903540484904050f00380f070310310300004810300480ca00c6102c0d4020701031902c1000501c61116107054990b000f400d850b00310090b40e41d50800791085076400301d040041035221043c01c3c60184200c441202c07107111400440e0001d81000814188540200190b03141441110701c0c3e1040b030b00856141e4a00018a001c211507001d000380101d4000c4c0d90800e5001000044503210030014018840203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 308147275 1250 308146025 308146039
    0x708010302010e0a081011071e1b0602030d0903030e0706110c0a0f0927080405010906020610030b1504060b0a03380103020f1b0c01050705060a090c0305030414 70
    0x400f0041000e603140f54030612030164001c00155075104004e41003403400c0313110701e0096820200f10f40e40303200041c02c16072241c070102c41034401c0d400d051060960103043c03861103a12400c410715007032a4000b51a84900c500740ca00080d01c031080b940070903210f54407151204103180c0507100704548620300109884014503901c00f252090140b03038441c80c0b41000c03280701250725065042e540b0350700e404004030141c21140ea0b24a045d5090141400f0041d0440e0103048030548121492540e85007080f00242040b0042d400076011940120304004240004000480c1603c0d0000c81109581d910b1382000b0300c010300404c0c0700315005802c00c0030024a110102d405000c290910382c45c1484010840004a0200b0801040e141101d649800034003140c1e030844104600d0009040c51302500d4440c01c8024071490340e2001d410404441007141c03107070702100814003c08000f8034003441e0040c50f205090311107503550341014040b401d14941c0c40480350200450840540c1c000c642c4202501d45403070b6034040e0745400c0d100c440c551a0151032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 308148525 1250 308147275 308147297
    0x302270901060e0411010315030c0312030e0c12010b030706030203090d0c050a03080703060b18010807050c032704090308070e19090504110a091d0d0215130b070801030201 75
    0x2042c02524103554505a5420b20365940e0340390020340310400e8545d54185541c8080d040107600031041c0c1130014600400c46055603600d1807804980a14158000c1e404051420741d0140c2808408200d118015000b190030450341407403040e0403401080002c5600341c1c184031780100098480d8268004c0c0d032142c88004159058481c0f41003007076802103e0840014810b4001001040003e4095a134075504013140d45000030b1480d480e080711000c42da101c244a1500e07004841111122580d00841d40f65102140d80341240c02e00756003148c4075030f590140e206c0c1415504000321151303c0c0d50f10190482c40e83c1d054028400c0c0640c40c41404e0203040c946098403090b000450001000c0c002c1c3c10700102c500664400300d94000d034034a1a15644200a090282081f84c40c0060456804059502c10702c03c075000c1c1c0b001e190001045004580402a1000d020540d200c1340e800000500406036000b1070b0f841c1852401e482d14904650b01e1044441c0700030f41c410002404c00322541d040c00f04950f13200541034140c83c401e80300c640d41e1017 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 308149775 1250 308148525 308148541
    0xe0f010902040b1503061e03010c200703030509040c0e100305010f0806010501020601030b0c0c16080106140904060b01050f0406081b03041101050a0c020d200d0503040b070c030227 79
    0x99607580210744d0300c0802c102240380b50070000e05c482c07407041c0c90005200b180c1d20700c600001d00b910240090680021055807409070010340100b0750300030340e00f00701005005440c65a603020b0200e000f25100140305554901c43d10b14000e0041c50501d40b502c1d00107042c0304c111000410050000d00c070078094420308260b10f400c04a8940300000c8d03540c3c16104160004e200581c40d580e20324590281c01400003812010500140000800400900881e0b10b090641e11a006052501007821181c0c02d03840340d211001001000c0010f9201d1907081038002c0d801c480045880c80c3e00c9801a2154401d10158000c42540050005401da60025841c0d0260301e407207202c19080c030040e0150662601058500ac0e1100c168411344411540c0508000c102e100c0c100d040c910b002e03c009400050030340c0f031040c009171420488040750011080744c1c00e80300304525100701d49884140300580c450035030b20302460003260303442c00d80050400e00303200543c1b1280f0b00841d401841c41391030554100c11856000314a840940c0041e441c2004502c2d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 308151025 1250 308149775 308149789
    0x31112010312050a1202130b1306120c0c02100905360412030b01141209060109062d0e040305070203010c020309030c09250224190902040e0f010902040b 67
    0x101100d668000d420b028001c40705e8000d40c4200e4100c00c00d4503200b80e0004601e824040542a407003444041c5589540c82d1000c042c00c1d80c01c0580545a01030702d0285c000385000e1b00600f80d8180c86406450f805c0c4d0034004561f00344d903126280d40010383c2c050f000c04100300b48002c0c4980400d0042c544078240460200100d09001001c9400f60b03030043c21805500c1c1140d141d240309511000d2407500516140d084540006902c00c9160b00070041508144810b00822250040401205004040000080004030701c1d202411111343c1140402841c510300302c107040c00821215141c4100a0482416981018200340c0340c081c2595001101c00c81c000d509010f40044094008420741c0c0700c07000054050440380501208000c2c4102004050040400d11400305200c0034180d402c10020900c81c0e0707001800441144851005480c00200850181c02e030880e0070130a44008001441d00c0c451061030000c10b07245a28800200680b01c104800c040a110300d00b2801140c44054010310350319402a201000b411000d50f09102d02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 308152275 1250 308151025 308151037
    0x16120c0804022e09032a06110f01021303050d09030506220b040308010e010b04030c05012a050105011d09060402060310090e03070c09020306011e03111201031205 71
    0x46031440c8001000360030096440783c0009100003041030307000c1c001c80b2a40c1c41c65510058020004120385805e0082040d446610720381051180309200b46900e2541c102280040701d8010101040724005000b80422020482003520140c8200295102e2011a00c80040c00c1341c244000d40d110700c9484200019140141d00f500300341c98208018001c1c41c2d80d024884510718201044160915100c003440c0c00100b5000c4140b0b60241d8441c0e07440d001603515106c445004030303070180c1080d400c8820400c41000050b480c2d640b0347c000c1742c0080c2411071540360b0103003106500400c034004da200d844030b440b04000104003065008905a460303840c000c0c014651200c1c03010301d10800441761b01200e54001004a005403901002550380210b5120710054403648508101064512000c04c07020b8640c400300e01c00c02000924442c00700a04031000d021400d51a010300000e241e5500d00807242d1983c0420810b0291451098015070094004094550b603100c03c922031004942d14244426036074091802d0b5880c141501c10340031070720 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 308153525 1250 308152275 308152277
    0x1c0c030914180c040f1d010e070507031d0301020a030c020f0a03051204260702040b010c24020c120d06080a0213110d0f0b0901060f3516120c 62
    0x102100b031540010101440540783c81030100041c0000100800c5906070080a0140d03083d00c69201c0000e111203440700c0c14180c21540a43c4d00e0743d420807001e01e0f0b000050300c1c1556010300d84414003004c030032001501101c0300307840c00e034041d400001c0c261840c6070940c00c076804a1120ba801c88611038000d103201921094482001000a81c0400113125028998440386410501036104068203510428192001140440d001d02109801107680001d40c81d140c81001c0c181070080c249100240065501d1400303a80080e0380440011003122208845001c096042d1103501c40000b0450723600030075003030103061290081e811124405091860104000c1c02c0403900700802580500700740401c040c01080c00024007001e82504c440d50f80284145910800140151810320b40008400181c0c0711002c4188241140c0503048002803013070031281071010b10781c0582000040c000b0316009240071524002107400d1852800181c41c000724070039044c0050400c0c103580b0300b54048034580320102c1c0d03070075004451401e42d088010490 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 308154775 1250 308153525 308153539
    0x152007080709050a0605030a0318050a0b03131a150909150c0d0b0307030807060e0105090601050d060912200c091b16060e010b0307050303030601030e1c0c030914 71
    0x3031190b0341c1010b03030805007005000c100b0607120000f00303180c150200310070750006004504c5241d501d0442d12800c40540b100f81c890512690410350255003c3c88013408038042c00e410b01004406000f65a151180d03105801c1943e20b4403401c1c44001c071307000d40d0140d600c01407143d499a0003040b1040d0001486415109044c000c0ea80c03d940c0f100f16800c0755070440b241840401b82c44d01015041c1e0307179043c08a000558450308006840b501d0034200f44003181c1c515400103660340e1505051003d4421700049603811900115201494655a4900302015000c0c13102c1c0180b01c7c581016400d01c1c11500801e00d0300050006ca410564542d40c0e00003c02d0f0f481e059054500d0f005400ba20100b47c5007400c0040113850418185101850101905440240c00011000c151440ca60b0354580f00131980c4280100407499900328000e0514500f4800041d44038070014001a041c996140780030506c4041c140544c4c10b000d20b104200c4000322020240103400f00290a4040b00015500d14010400106410054160031070207801c02d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 308156025 1250 308154775 308154779
    0x90703020f0307090c091703120408030606070b01080d02060c0a09050616140c010e01090513021809071115010e04150f020408160f05091303091520070807 68
    0x40140540d600c11101d03098050fa510106641c11240145100d000d2195640b88039103180071081030a1054044081c6060f4000b0040e03a142403500c941d40a03040f68218110540e2615160009901403158090082082c11014000110101e0110740c10042d0100c075001d80d82c0b00e81d20020071031a10b00c100c008850101e101702c0418041c07403c0c03443c09400700381700941610003080d03525101c0f038024415898404002e42d2082c801030030346590081003202618000e080403d0342c182818002402480304584401101d40d000c00e5400c400004440c184040d440302820034841e40c00d003400c0c0140300e130550001103044e9208100082800c0501803c101d4103d58241905040300c1c0c4884d42c1d903805904000350b240e03d44507215520716081c0c44a910007800102042002024055101303202c2c43d415609030b5110010f44110224204030640b02c0304034140e4800140c074403e00040d559850243e800304541d8000104624200180d00403c0d5000a190344140703d100030503640041c10388503c607a48400a000c2d03500c00b50013072041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 308157275 1250 308156025 308156029
    0x21c020d060b06090d061a010801152f1e06060906010503250e01020111040f120311011e05150112020901020c0603100f0e070c0308060f040608030316030509070302 72
    0x221a44103802449580f801044c00300190568900340c43c16070b4481c0e0740e60000001d15504c1d01d09800c5014003802c01c80b0180d8940002041c84003991020841030101d146125040411025160000024062440703655402c058803116561340d0030390b000882000160340350711100e502c0010351900c5402c005240108940d141401100c05401c054508250318420f9824800c0300e44151802c3c1882224981d1288078400c02030000909550301c2d180d9810006904020600208100c4104582916000d444100e0000310714a0b0403103840c110309034520a139502c0c0c0740e55581c0c070b18482d81401d030049a46503018041d64551081c20141c0c0244405101d000c0b40c0c035176180c83c01c00341e52034000d000601c074140140c42c207050300385000c190103500440d010020401c04480034419038003152440c00140140606101c600c1c134006202810301e0b000c202d030240074000001d000640395900d4160700755914601510510082d940c0720006035aa0b001a01e00d1500c0030380101070525000e00c40c0c49621310074040b00008040252860302 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 308158525 1250 308157275 308157281
    0xf0f0303071b0b0411130e0601030807020105040b0d06060905180718051203071b0602030703120b030a0c06080a2a0309050f030c010c050307120c020705040e010207021c020d06 77
    0x442030703900800b00d240303000c042000000900c0c4284c0c05101c004442d003011208101915128a54642d401c41c60203074109503501c0001580b5040d00d50240c00540c0c0c070506800140c0f0a4040e80d03005440038200000e16090003030454011070201c0c1c0340c039254022055142c00070031400d00382004440b0801081e24000452075031003100800480384540006103031617921780001c06e41a4900407031007900d0b40d02c0080c032001007150f080003442440c4014103504070001d04085000b52a8800c580020301040105004c19059426a500212240800404a030101c0381700e45080419401d0a1080e0701c0400e06100005801d10000c0c050100c08202d0900c171081013003003000e001c4c962204440da00d02c0c10181c1c8e03203001c200019420041599a8040e840065880d01c0003041c0c15802d59400d094944200f000620030f004207250007840703030443c9008080010071200a0b803c1c040b413400c1040d9101070740c400e05040743c810203a001075008050060080d2090300d2040041458550f0807054444002d4010312030079810000704440768 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 308159775 1250 308158525 308158547
    0x603070f0c020a050a03082101030b1b190206040210110309060706090803040803011a1806091810061d18070203040302060d1a0f010206060103091106040605030601020f0f030307 78
    0x280950b45030f41d1103402084c0c16110542049441c00c2c400106a141d101c1d42c2d45031000c40e8200071002d184150306540d10f00c2a1440c01410300d0200300780c20043d1030315041280c000d07a081010740c030450010325640403c000b503440c0c3d07060328260301030104500f40031f110500c0781da941c10b03521a00c5802580b41c6a18281800921303480201c090765480d41e039000d003c00203a0301200660056010703940780c0c1c1c0c8039414203103070201421200003a0107007114100140c64000381c0d10303c0a91843c00c41101c14540391640000441c90410310035400880c1030032520204030b1310601e022426001d07a40745a0764911403c0b02402841e8140c20314041d5903511000746000741d14120400c011b4298415a50701c1628213242d0b07a1750100740b00c2d42115041003010b6446200541c0c0d089044080902c100c00222084c0b16101d8200300080e464400191200d410191118006818001c9050300070342c030000b010300410750f90381e600c4000614a40040d6890f5005000d500c580200ca580000b520350508107554014510750340b1450310507039001c4021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 308161025 1250 308159775 308159779
    0x914040e010203092d0d080a021201081608012f0f0301231c0204020307030612080408010b0904051203060114070501140c0c0705040f09021f08060603070f0c02 70
    0xd1030100c0c141402800610301030180b50009002e4010b8043c55080d440149101944001a03043c455070b0300f13400c0005480942c3e80182c206840c0302e4940d20600070192003400b212401a0f03141500020b00450002074106250380c074810085100e58460448500f60780b00e817540082e0040c40071140041c050042d140201c0b4411488c40101e03d82418081d0500440d042617101105922104000b4215500703400c2c40341580d50703411511100359203102048030100303072081c80d00a401168080700040900380240d01c040050502c0c480c0000b44c09040c0c4ca0030300d150368800e00501d607980d420454440190b040c200106c5d03000c1c2d540070014140e45025641e23800d0140e00010a0703641001034000000c244000b50714028010f041c0903d0020039004c106c40314003081c0501c0613000d0b180400d002c0200394141c03100820a442550012180415044070301d00103070000e000c40300c102940c0f003000300d00400c10091140e00d0401700401d01c2d8550340901d503150001c01c4006c4c0000c03a0315002040380c8128040a82e445110b0080c800b03840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 308162275 1250 308161025 308161031
    0x15120c040f020c0a0c150302030702030a1808010609020702150705100b0f0a23060a09060503040f060501080607020c15160309031407060e0a03052a0310060e1501091404 74
    0xc000201484c0411000c81690b18000050042c00501e0340410007610a14207401c0c25441c40c10181c00c02035691042c03020440401003034448108240050240d08001031807550300910140e074641c48564002e5201c1141248101d9900ca503034100418200142d480413034202000c2c1c080b001c40140094050001401301c4c0703501c520000e05691041e5206080700c00903240651049040e0034042c4a20041400702c0120036114000c103101485019911140b68000d4a0030351400b5516a1228503240182d204560401401c1340c0c145400880d5a510014a482c4202119821134200c0d0865031305028000780501c0b43c4140411040090311f86e541c400090501c8030328424034144150951700d03251054464075680c400041a0040c0e0f00400c41c2c41e45c800c85003804104101c5044c04985d195030b482942d80c0c203c00310501c0c1642d044010014103808110404c00750600f020342a40c0200c01c2c80c2c400c01000b0409401001d075210b82031000b2882d40c06000c0b0f2007038020181a101c803080603007080d0b1400008085a80503590140e2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 308163525 1250 308162275 308162287
    0xc0206070602070c0605030402040e120306010c0309050631030b040b04030507201e061e0f07050705010306090b03070902160c0312200303010b090f041415120c040f02 73
    0x61264100700822150751b8490302d909152040000f43d6140d0381d0014410352084440c4403103226600d0031681c01c034a090804480b10baa039440c042c9d40c1c03004154440380c0d02c490b02040c54414440c00c003096030000402200740007031500180d1314a0714001e459000147c10b4800401c000340018100c00b444d242c03c14000c0c1400303420043c0a640b03003d44c8201615403611a90b00c00c0312841024100f03410441002600060965a00000361010440d1401030f11a50982c00007007412210304a01c20708102c0701c4400841105903940d4802e81001e580e9050300b4072695000a103041c000180880441c4907422044030700030040c0c41d00e0761800b0948406034004c203015204004c03002d41c0c0303c400102c40150f030400462003840056501c1d42000d8000c2c2901d8084640300c2031504d001c81426074841404011a410760700c0c04000c6585070100719011540c10340c2601800e0b5002032a0402d0880c0002c403007443c55120308400030380e00000022003000c4c4803280140343c0c0129441c1e0f002c054020300500d8560050288200c4010006090070b03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 308164775 1250 308163525 308163533
    0xc040f060b0a0909050108070803120711060a020c070e15040b19030c08010506040510032607050606030105010603020906040b310305010509010b0a03030807030f050a1505100c020607060207 83
    0x36100410708004030b800f14800b0080c41215006050040c0809006804100c0c6010300441d100d118244d6540f1801c90b01c2c2000500c25405120b102d014090346008403942460045802c0001b0350215046448521440400140558110070224494018034080402c2e480030001848064002d0b1070020b83d00414a441445840c4014040c4c0e20085019142044005181002c1c1c42d0850710064100303401030b400c0c20100840042d41c92180c90480303611940f80044038241010304140110240c0511150a400103078003000c1c040c00140c40da0180100314020885641e80c4c4005030224403804c04200c8d08640148403c2188203ca203001d4403114400144400144420005030880c888400da107404500c010700d01e0034000d00c0310074459035501c00004070080217643c03018000203524a016100007410080c00b440020303c150300ca40c00c1085034808480e4240518185020b1560203000308007800c514103220a800026035140c2903800e80d8000c4d5090304c030403100c00200d40a10180d5405003034150342c126020401c200c009 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 308166025 1250 308164775 308164777
    0x516140a330e13050105010e1011030d0f0c091a0903070306140f0a0b0607080d090506040b07020c09011a0322030509130c1e0c0b09030a090609080c040f060b 69
    0x20303140326a03076652902d81240070491a003804100c40c0880903c4d000060207a0f0b41c10050025400701d0442e0b4141000c0e488a00458103809240b102880a0201242d070007920b240a822000c40c1406640302400060b18498084070180340501c2201d90345100806411006491000100359280c4003a054829282d2a030710b400e01507410316a00c00c1201883d074000c10084510072a5199082859000e09110070000e040005005019140000e0400500000c0e038841c2c100c01580040c43c8154400c05550709460107040202d1420f03c126450f00c098001c1c0c000340c41301031505080550507181d02ca100c2c148804901c640728542e03504010219205101c00303c1c0003203040043c4001d10751400b44203944003030752290400140701c01c1440768000c4014030b50400c071050003541d0b04042d009078800340550142980c0c1140400480e250500d101e40a06008180801c0c0551007070b001c4020b01070744003640c40c0c0c0c0650035034a0004031a4400203105440064000d424850258901504011804030584801107842c03900e508058610f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 308167275 1250 308166025 308166119
    0x18020307021c20030a18120b0604180c06020c0d0c030f1b140a090e0a0308060f040f02030405010e2103040503071502070302010b120703080c031201030516140a 70
    0x1942c0c0c0b010440c034445d258481043c1901602c0000c4071101c01385400c0151041003071100c0c1c0240880e034031400040150300c642d0b02c910040a000007006882c0262400c0613507182d52103001c0c8600501901540e001c4909050078a540026030028140c0e070254950703160b6204200050104445221f480d2020303001c000c07822001c00c0081c088040c0b01c4000e01d00c1c458100451040540c1c05000c20b0740c10448410001e60002c24003c3c00281c050825a40503502e003000a000351460100595000b858005031000c07104581d40611b00c40e900c03d01c0208103c601400c074090392002c4100703a5895148681402ca0080b40420024641140c41380080321b080c1461580d6056101c03001c031040e140c3d03075a8003180c000181a4240a6520200700a4441801d6028010503203500c50b07101d800090040740002802e081d144104104842d071840d1074000ac000e095859140460300c0c0c4503100747d04c5000030489100410220325686184800c004018a4510014070b040c403240c600110520007001e00c2400b10b0561100250101c0411603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 308168525 1250 308167275 308167337
    0x180904060605030111122a1804020408150a020c06040f060b090a0915150501050906070c14120601230609100f09140904060209060c0304090618020307021c 68
    0xd02c6582e20104035a01c0840101040c1f0344040080e0003920039990218028266103041c82c41d240c0d22440e4106107000d0303508920905821903c0054002030141000c51307440d04021955007034000ea40c60359062034050380203211a440e92504104080340006090400c100810342c4100000309450386c4000020300009c070100d420002d03107070711425007804001c1d50600c00d98480b0b072141810882000c1b003c50f0300744041414041c09040c080c00142d00310081d501c032000c3e02c0300c0c640c1c001207042015464400c1c1d030b030b00d508441100c10701407401131a84042c03082c0d01045150584002c10300014a89a85a0100e6480419441c20a0700000b0401810345191039440303440308d4600c1c02c2d8440e0755080e102100003c2c91400326030301806030100c2980c0a107105a8510106503001504041d02507122014000060b5492165140e400c2c081d200016000895102c16003041003120324401c01c0710100c13400e1071000d1041e44011160400113800c118410700c103181c2c0320318003000602442e16010000101c030a044039010b68800d89444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 308169775 1250 308168525 308168527
    0x91306080703140109230703060509031206010f0f0e04090503030405010b1306060e0909011d0a02010906110628060b0d0f1104060f0e0d12080903180904060605030111 73
    0x4000d00c107032407014088000d4008020031403c40140c0321b8546034420340018a0407900200802d460000003088007a014507000401003205042500c40720742e883e0f1100c1e1075041400e4003580003a50710360140c01c1448502c10540c50b0f5041d1130004500031136100165200d82644282e46500f208081174080004e18442d501c140c000241e00781c030041c00c0000790500070902c80c40c558189481170011075845031030f401040f8016107140150340c807085410380c0500007111a440c08000c64507a410200c0c00c0c0018402d03182c5d8000c0e291101600d840701030407182c00398151441301e603660006010030f12000185071041500503801e404440080c41040c0300e28140d401d00e90040d04451000716202c00005824403a0724a07200100300108030181c0240020710313907400307030f4480c0200303110801c940054550702510003c0d1100700e000b0b060110200d11841c02407036000d2154620f80c0050391543c0000c174110310020031148018540c04d14150341102c206d08100e000749000707000322061b9482d01c90015036620240502036120316104121 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 308171025 1250 308169775 308169779
    0x105130e0609011a0d020c0c03010c0815010801031707030314100f050d0b010317040f06050426120c0712030c0203191a0a090b040b0a0606110c060913060807 69
    0x1500b66041c0c0104c1800491015030010b0540010101c034421103041d400907032203076215140c04d82044005528240c055023040b144201656208601510890f82c0380d801c03c0b400e1204400440746d0080c240001000403110780d640568826846015200040c483c0c9008680100d009c0c45955410006440c1c0c0e07408541e40d4801400319401a50003500a014141c03290001402942c684030a100d4042c0300281c81003a851340c00701184000c0d44203d81c041c1400e45490382c1120b96aa4004006500610a503002111440140070b007132445140141d0110390101c009014030000c000185a25030b1094041514a02ca0325500243d6608030700ca640003c540292aa003040a0b0700d07005050074030706000b0405042600d582da1003c0090880804140041c011007101020b5075900c49402c002000280805020459403100704001c00ca0300e5a0414400d0444140c203000d0283d680300c0540b401003a01c0100d03580c98001c0245141c035824801d0241400715030090210b0a40234800300400e048848980001c0c00c5a04540c00c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 308172275 1250 308171025 308171029
    0x2041b091a03040807030c0b10030611130501110a0b13230304090b15070b072003160507051002030c010b01050307051611060a09140d0b0f060105130e06 67
    0x30010040c00c040000c20304905448018041a01c0001c0000340040c00105620003170602c2041c01c038140990029200c1c03801e0a060022903480319140c8812111503081c40840b190480710784003a101d4074034507000705454450500e001507030041c03400d0794403a016101d941109400b040c03108500138042da030280144e890841107421f14950841130200c40c200900c46400a83d8158000002118201e9503140c40c0040ca070400c1c0e41c0020050703071414602c50001d06010420409002400c06094000c5419485134041d1903414280b00c00284400142105190428003681e80001655801c0e140c14034440c3c803e454400b40c0b2480090b51071003c1c0a04030005a10105070015240000d1041c0e070035124090030400e056180004005080d840b0340320440b4002d0039000b10705010024108103020318060b00610003515104090070040403c1d0b410310580300044005800d105050400394032586040b5001100b0600a80d210955038120f000c01800361410070408108074006900c4810020001e003c445101c4c2c3c181d4184541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 308173525 1250 308172275 308172287
    0xc02061918050a0b04060f020118050105070e0f010c02060c0106080a1401060f0f050f132d091a040309030f03080f0615040504110409050a050415051504110702041b 72
    0x1140703020b007035030f070b002031081d03030707801029a000c550141c5401000c0191540049002d00003a01181844800240301c0b80300300b00d01900031502c01d000c00d070307110702800482302d0400c81364611030308426001ca22070701604030150070500002c01c1001040000801c290f40d403a900b00e890110454416626a1640f1502845022082c0901c8005002c000940501d030750420481c4000038101d44940b51142c0c2c1c540c1050141034032200c928a0511031082010021100d0410320407254820319841d030b2403202a10301541c54041490300c220803801c0c5d04800500540e803000c502115010401800c281d041c0583c10740d0000000b00c0c1c00080d01c94180c400e43e81c0589a0800001000c01c3c0310000c0d149520620301c0681550151403d1415101120f07002c0b035001c03c2208205542030020310582c0c101040c070609020802045c40151307004180607510403203c030342c07a11803c14001c00c21500d06580f80079582c42c12802c5d00c0349a21305034200b0070b03003550350030790391454103144c0c1c0d0000d82200d0000c040c502000d00e81000fa85a0540c00c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 308174775 1250 308173525 308173529
    0x607020a0b010b160606090b0f0303032a0f030705070b09060412030c031d0f0c06160f0206160f03090f0303050409050907120f0b0c040806070c02061918 67
    0x10008081454996a400300807031814024a101d416011540e40f010552240c0e00340c03c11600808204032242d12071a210b00030708104103102e40034011b2560400c007a801e002040300c0c81110180e0003680400501c00103102c0300c151120602d0500c24041c0911007100c10300c40000c50150b00d0350303112240da484980c03414000d030b1800101181641e8025000b0803010418181c07048120701c1092400158180121100350020840f52040c0508050560000003034040f00103409070224050030200d509410085040015521030708804007815000ca030000c500041d0700c41003d80130684018506030034180c103070b1800d121501d13015030141c80c0001e80100d00d40034142c1140c1007002800100180c18005800c64401600c3c0b88541d1042c41101962003000420340c1c1000e2140c8005480326048600741003000c0d09000c44e00c500180410b884400046010a018040700030455045602050203003049a8960101342c82664140700140c2c1c129100f00441300c003807540d900e002c0c0070504003603c03400000404a030072800c05c90f2083d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 308176025 1250 308174775 308174777
    0x90702010f180201170c160b0402090906091c02030f070b0406050f06211e0618010501060f0c020a1e08011d03041e0f030c080d09050112090201140a08090607 69
    0xe1411030b40540d902c0b070101c0c0050014200c40703042caa1941490300780b0b40c1c0b180084150500804200100c200100d00101500840c000c444c001c100361181d031052030700d621059498404561064100008160003131440e18903c080c01e006a0b401c0c5207409001d104c0702c1e400004116100420b41040004005242c8521a00281010703900001c6103032200200e410054840034110300c80701160900070120004000c12140904603d251040c80101100300c41d5031503100752001107121a11080090b0503050500c11141210555510710300f01c1202c2c1002695040d400000c03e980001c00c0810101d0f80014885003e1141c04000f0380c800c0321180350004941c00c50b40203025000101d6004140c000668100105440035a00000e550355600240703246241034000c401d034400c801042e0f00c0c20000060101040c415801c540d1424240c6e6000001c0100c02c0394608050301815001c60101101d0500c075904540c0a0f8a41070301c181840301c1d07018045800c540e240d4000c2d03491880010034410802104130b40034480300e6040405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 308177275 1250 308176025 308176061
    0x703021b01021905010b1201020720130e0f0a050c0a0509040b0c030903040e0903131202090403030c050f1c181709042705070605040b030f04020609090702010f 70
    0x40100002c1d100d40d51a106401c0c0d09011401c60000d1190030751210304000d10041000a1f6020f03503440844c046c0d00302100581d03500c000001c5141c0b408030201d01d21403005600034641081d0200c2481c040e001040b22410803c0b0610881030040180041009550b0041e40101c00034500c50410304108030074011b45401c601d003e10a40001c0c0000600640401c0e034001c1000d0501035240d40d140078a003499130049500c54004c042d8000306000c0705c1c0e070020008010303124005403001c00b02500c0e030340c41d41d00d000780e4050002d4200c810f4000107000310f4400d5110b00e2130704034107191051901c0042280c20007250003181481c460454034208041c0809072501c00e070007034100380804c005c105040c0394032250000511100d201c21300b144009035003610340e65503170300440c44007810200c400001e031002c0500c02071000317196a0484251080140120b800c0d409001a5811100518082c03491035035400c68800f819a4040c00403a0400e80500028035660780d0107611a20402c0c039a0b000007815040c17500905c058594501c0c0a013503d0341 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 308178525 1250 308177275 308177323
    0x1005030a0809060c06040b09190201020303070e010306050d0c150c08040605070c05040504080304050105092a1215070909021c05060f03070b0903010b040204121b031205070302 77
    0x140440c000e145250070164071601c402401010903158840e01e00000164010706003000300700201200764a01841c1a0000c54003034109031403441c2c0850039000300280c09a441400040c0070075114800400e090b41e0189070119900da0f55802003256000c014000b11000143d2820170301c1414001404541a16a9844d081c242c3c0c150303684992003148243c0c0034142c20480001100c0060110300c03105000248006802080986001e052130501a0402e407422900d039400d2902080c01c03010700088180060740308891000070500781d6003921000c1c031180c50180e81c00101c41c00e07102010641c103000c001c1c4442d0a010540000d407038003203401414840c86404c40f0761103901c10701c00c2c5004e04155560506200710241d00c00103854580c03e000034608000b00401c0c0d039144c481c2c07080c0400d0121450002d003080300ea023036002348446400700c0108130690107036028020003d803401c09004081100788480c401d174031010600451805449031200c1e403464059903004008144001505401c00d03604002c1c90b0214002005150755802c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 308179775 1250 308178525 308178529
    0x30b030129091021060e2118060c060711030f0307030c030905010f060501090b0f0702010f1205010e0103150e061b04090207062715020721090305061005 67
    0x50018010300542602c4001045103500010301400307800d844900d200b01003507456045441d42c0c031a08003104c1c050700f044640d001d0b404000961000460b68020720080e0100d10003101c542c03e41102c0413400e416006841940c109886540003003041d40341c4480540051b00d01440081e002841c0840303610180d90003044500000c2c0417200070340e0341008403494041120f00a41c2000c030040c0c2801003026029501e8520115086200340d4081c034111402a25a1076984c0c0d40c440d4455158001c2000c2d5580e40d0740104000401588110380f4411008040d040c65541e50311480c4074001140c10036008140f044110720018005d001c244010051110f00007201401603919841a031030710303804041c0140314650005000421203035419000e40300a48911030086460b940113041020141034407420407044c1004c100c11088202602c80c017a000c0143c1c01c00c020800c4019419881402584012802c1d01c0300a0000c69040180c1130f400543d1a891081c0d03a1403005090860a0080c24a203020300520303202130404108002503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 308181025 1250 308179775 308179841
    0x402161e0f030c030c0203100c0e030a0201090302040504051501090b04110702060702040e071a040e07020d051210030206030108061b031e041b06050d061211120c040c030b0301 77
    0x8941c1c50300c3c000f04055000e290030741d85c8001840c0e0007580344c0a1401d072107061070826800410a000103a440403180d483c01d400f4107807102d200c01c1010380010451001800507003020b420103500107100350201c0703295101d51b1004141c0340c04280c001c000c3c0c194039201c80c09510310b000d01500030740000080400d4904182540001c402c1d1184c004028000c603140c0035a04058501030014030001c11100b2842c159941040d038005140b513000d07004403c1031051541c0415000e5200160b118410401a101c981c40c01c1207000c0c0514101c007004107902c0b590742d1036040201c01031702d40002a60081c0105401419581045205000c000c1a1501c030a081d074042407040006412864100c682c108140210b1070489465a00f04000100381101d0001004480400b000a4540c0d2041c001c00b240b0400d0907041002c41d49404a100340c9000b6000041c0608403010518595441d0404e40440010700d5142190180290741d80030805440003021140046030740c80d400c07171080d400e0a000b0a1418402602c8040c0c04c40380c0d4081c65950 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 308182275 1250 308181025 308181053
    0xc03190e0612060f0a05040509030703110d050403080d1e1413020f010e010e09010e041b0f0e06040e0a03020c011812060203040f050a05031b0616050c0c0402161e 71
    0xf040c01c000110300045e866102d0315201516000d00107003c00c0c54403503201541c83d80034240480004001400356002010085902035001407150386980c074051540c0c40c2c090702c0d5080b050aa82c00b0326503440114140c4100a00360142c1210903000204000d10044155814141e009002c91022008800c52400596038403024021000003420050302660b207201c0100d501c950171035850380c0c07c0402c400021480c6c0c200004070512684c410943c0369440a070a0100c40e54035034881c03048090003950400c2c00d1140307003c415081c81e405040038200090203201c1030150f07454005201e03810b0300035821580001c021940d000c088030b07001122807280b0038803035440c003116801d88102149010700507940c0403010030100f06034410035905458200c000c0343c180d83c90904000f80c49900060714000b00a0300040315454006c1b0100d806807240c001c170a40006004601c107002c0d18a0350180507045481c0c0076014041080d0382e100d01c0a0510443d0008038005107150520301900c201d6250081400c1da400c4014120700004c1d225072884d02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 308183525 1250 308182275 308182279
    0x309070308031f0b07050f0d020723130b0f0406050f0d0602040314060105040f05010311150d0212010f0902090306011202040b100302120105040c0c030804080c03190e061206 76
    0x9034940d681d0301811a00621101c500c6054806100700040404c0128040c240c000e02800903100d1100d0050846a0703207a101f0804e0303a0140e00061000c0081200c501c40212000b081c0c807079185001c1e401c42000600c40180c0304402900150f40b00c540c10704030b04240075160725132034064408114641c107050000e54001403c1c007010f803207121410707038440800040d80c0596006651080300e15203501c0c007804050340c940c0c01c24080c1a000b10b19003003d107200b680da1800389504072504030560808440002c010701c07103d45a06080030401480c2045038005104140c801000f00c0364030981d8203a03041d41842c4141c803d00407030b68400b0444900500ca122265078010030143d044500c60032905004051520104001d4030086010300d920070041c41034074045540580060030b500c91201840b100581c2c8440801c0101d44044203560005034500340b51100103801a0b401c0364006008424580c20207000d4000d42e46140c3c000d5800c0411842d2602c1c100c040706411820240c1c1d246001c48880381020000041c0303080b201c40040c8807078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 308184775 1250 308183525 308183527
    0x6080303062b140304140108010b0406300902031c020606060d1b03021b0d02120c2109121f020906160b091002030105090402060a090b1216050309070308 67
    0x4482d40c1c800c100880071841d404407440d001c02c80b00007506900d9801c1841107a11040d081c900a42003503104120590607520b10a01441c20281041c004540c0000101c0744154030768075030002e8500e941c180e2410365031025500c00c400b0465540030303c103050402501641c2814241c004007188000b054010400d0743d0f0000e02031301c00300d86800a02e0444800ba1041c40d00c078400003401e1070b6070b40d00c0c1d1640c03680040100e0303040d89003098006580304207802c3d40c9405504460b8010303040380e80104c9010000741c004014901c03802e42103500000600d1189030010744c0076002c10b030311a10000750f0202d050030b2842441040500d14030282041442022051008058400d03151840c40d60010740b02c90950780e030f9401d40d24046e942d40c84e160448be0340c52a11140b41042607801c02903501c139400c04152481c14600031a03050790000b41c40074109440b20703070a1100c550844c02e000803c4c00306240300425551246406041040e449030030104e1b160800c51034a9041d844a0081481000000c00800c4030400c000501c1e0421298082059 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 308186025 1250 308184775 308184829
    0x20a0603050403090e0a050a18020904060f090507091406100815060415030c110c1507080c03031f061d15090607030c0501111216030b100f030608030306 67
    0x8a0b61080ca03608911001e030000d406001c6c4110243d404184516901c0c0001c002419404400c422040108040250710401c010001000912941c0000002d0052000041000a0302d60340749800c0011541007010541c1d511503001f41c000e032032950707680c1c0c200c0401d4541c07190341841d0003401860448002c007400d520b0589403c0c24440e40d1117040440700200203950300b100d2084040d540081c00340032108800c3c0d00081d211b91201160f1701c400b06040015500041003c000344440c2d0188107a00e4010a04c03e41c0c9000d801d00640300440e4042c001076210b42c000303070001c120000542c500300314401420703000181088080074a00c0401e1906103105070099200321045d40f0350b00002c130a0ba5801d440b030902c40350740024012625600b0190056171601c40144110020300507519100c46600c164000c2a000100300d070340c440e020420140c550000703540e074940140b80206880880001055103420708181040004400d0310b0b001503940d80c148038400162181102651a5043c19000aa114050b0003009a206441c6030b0785 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 308187275 1250 308186025 308186027
    0x1208030714030a0b0a0603020c15180106080307030801080105060a050f041b020f0f0610150e06030c0309060f010312110c0312031009050408040603020702031e01021308010207020a0603050403 84
    0x702110301508812195030f440c01d001c618000d04694610300380190385502d0041905806802078401142403d4000c1105000308408098402009440f1151040c00325000c3c03500001c2c2800b81d04042c1240d00e00460340c40d035540c46c0007050084140e1040c9140c0c0d01d003400f4044c0a2782c1d071460358000c98404403041c2d410a540c00c00090000e00f01152090750b290803150700f007500a5000304699484030344500c195415801040304a60721400c003201c2110080c840c82c2018458442c03180c0c0a00c1510082d0f1403d450100b00c002c1c0400d0b215401502e011025004c08005c000319200e0401c01d866210030000b100c0151949195102003107400300152610501c04868101c10b050b02d030030444e1610b039604c02800c480c200c180d0000094002d0f4800d9410100d811048600425440000c2c01298000e55025945e01d01d05440c05104078025003000900b00e0780350240303004049420701d541100e0461601048001641c40303011940a036008005075012045503401840b802001d83d45d0b81140348121622414081031607912407034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 308188525 1250 308187275 308187287
    0x4050601120e0c01032306010507030210020a02280b150f130e010e1902040203100b0705071e060504091d060f0106090e060d06110f0d0e010f020412080307 68
    0x820848110310b89109064800d5001640011005084c0c9080040c400480c800390650280c0c5108480b2103514440881c2c02c65100d000203102d01d900910507074816590b00c075240010b0f83c3c0501604c1d030040c2c2c052025040c0700c0fa204c907000001211500c00076422060181d50b003062410380109501c41d407007200086640242ca4500c4440d000d410020400a0000d081c04413800041503002c803900b18135843c1070705201c0034020004028500c811509902840c00b08079038200f00107540024031900007511480800920350030382e00050000c00344100c0140008505084014070300542400c04079506129a1004001454100701200c065440910300818156003c0d441300d0304818426290401d90320410040205c3c3c140886511030580320aaa20050300503501c0c8001c003481c1c0820786100d03501102d51005140003d0f100d070300104001482e039542505040d40b1000300407058100d0205a00d42a4580003d800301e41800e110b0035204400804085003030500704140c4440d40002508000e01d11607001012a01141c0612 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 308189775 1250 308188525 308188547
    0x30903090810140a020a120504020301090b070c1406010b07020d020d051911100f0c02040b0a120c080d0504050d0609020607061a0102060601020309040c05040f0b0307020d020a020901030204050601 86
    0x100c12100594004070144005090300f541000c01c1244040c0401c42003035641c000c58002c400720742d4581e000511540e001c41c004000240c000c90f41036590300c04a10000303030741600c21885a042600c485c01c8c41162424031035140746090220344101d401000040c0002c03880300302076410344c0703030143c0342e68049011034404950240e49204022f00356200e8006180412204040300301602d43c0300301b24004125800d1010b000c80d102d84c0c070100c2804111116000c2046600c507500c1245030600080c0040f40340004c01010940c5807115401a15030b598600e0902428403400380c266900606149008200d40e441c00c2400070540e004902030940309178104041c0d0000d105540c0c000e26240d5030000c00321aa54402450200c00070f0a0044491f400817500146010146d0b001080e0317907200d2041a005107240c40c40c0d03801044024004e41c9909801d000c018400400c8985403c0a0007019100e1058803e0b664140184041d04c0d014420b0f046400b1544010f1030b40c2c00503200d2541090441c0c1d416100800c1d581c4411005803050400b034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 308191025 1250 308189775 308189789
    0xc200613051e0703020a09050906041e0f05010b0102070e1b0705070902040603020d0f020a120b0d14030a17010609061805040c170105040212040f02061605070302100503150103090309 80
    0x58034060070741d00d0215062048904c2110300901260380d80e0301f80002d4840403180950039400081c001408942000b00410050b4a0040300d45c41b4104103540342001d020041134241e40301e0f903540c02d14072406d5030100125030243c0300580c640c41407444c18070540c810104140c1d1002400ca0808a011810000100700703640240903041001d41d1520f80710400100290070140206812904011040001090a20840701e036541d090f5609443c001c0000d01c030b14050458641c806401c00000c5100b100440d41d13001e02c880710395118102466503000c03003030002041c034401c00140580c5040c1803001001079903002000c0c082200c0e040d003407004200c2000d42c1e070507082c005d040d80b007180c0090a1840e203079182580517103c14102a8614940320305640c803076050008a014a0325034404006141c00458042100c1c54000560300c0d200801107442c0c04148001400600400d81d411111039100400510842c81c02c512041c12121542ca00030381140b8040480450300e10b00710020030b05141e5210003032003d040c41031203400060224 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 308192275 1250 308191025 308191063
    0x1104200f0909010b12250c142514011205060a0f0909051e030a050f0702150a0e011701050f03070b0a0e04060f05090415090b0a0c20061305 61
    0x36415081950f94030001c1c205228441703840014510001d801d0340040460140074144100e2954508180c4101418010030380300c0b80389404448a002004215010200c440e1103000c1a802c00e0a01c00700c01e110031540c00210360100c14440844069901c0b241c80040d02101c840702066540317a140c040783c003040e4680c100000ca48041400400c03494195040b02a2842c0324000b1250001c45200000c12440421500c9200740e40003000062000d51061019141490a11100a21b00003040d0b00069812043e1843d03500f103440301150003140703a80c1240f400102c0c40420301340050400c1c0b100d0340400c1100014001d951003603690030b1041d00240c90400ca80b201504219040c181c0c0c0d03981c3c1440180200000650151246041c8940861501c030f00e400400100d5130003402405c416100c6569280c0c8031941100841c1c1480d5842c04400041110f82ea0281c0c059400900001181c041c10200207014031108000060041d07521030319045030702e800240d07540e40041c984521524058191400601700203c1d03040208240307013 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 308193525 1250 308192275 308192279
    0x6130b03071409100501142101090e06070e0604030209040807150e0f0c0303040303030509100606030207120806030a080309030708030108010b270610110303131104200f090901 77
    0x3542c2e00c1411030446098419a40b0f918403c01100414001d139400140c0000001900c58588030203040b00d80c0082c2c81010601030520f44007188808240d12003102c4580314250701003000c3c0140800340c0c00010034500400c0b00740d0910080b407090300c12440028000e501c680005001c0c084204256042c0a50080503081d00c0d600020f0b0800261080d4085080030b40a410703c00c0045900000f1001030b0504040c010354107107441c68030700b039004000c014201c00f164020300ba0481d003140e04a214a0015006070307100140c54151a083c00700301c842201c00c400040c4003044090100b55a00054580c2420364042c00b075554070303601c12109a0035401400b0004000150200c008070303241c00706403c0308903090300039105035000055444401d89000840c9141d1100002c000d40426114100324010140c1034145081510030303540d003a61440d280d54030403110645030310440700030801000f104801e40c843c0030004480600c07803108035071003405001c00b1021a02040c1e800000c0c03004403001020741550f0b90702d54024001a1306603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 308194775 1250 308193525 308193539
    0x21c0c150b100c020f120c0a0b1806070305160c0f080619050403050316090b0705030310081b06070c080703140f01140117070e01080c010207090902010806130b0307 72
    0x12000488807032140304082814401c82c0d1046407407a070b1441d0004c101400c41ca01017414002030400030001c040c0c4038050002a102d0a440321401c1c0c0c40104652070301969510034400c498030300301c01e011501074851002000800040f0b070340142a01c003580c1c840c4010000d941442d04d000068070b155540055450804800300040402c40815054880c59001320011071884004111b80b04840085500074080782050000c110760f0b0101c00300d064064142824085c01158030307480ca0f10303415041440100e0300791f4000820070100703082da6650300008103644001400da02044810403900d00c4444807466000f48404100e4206000c00c2c03120a80c01031410318140c030360041d128284214000c14101e8920304903c101915064003540511400400e200842196000380c0d080a41c0400007456034110403810788124140030581c0302e00ca0241c0350091002ca0000c000d5160440d002900340b5940b58854904c9038945070405c0090307600705122a500c0001103c8100d00f12600d0f40b6950010700509000541522a4041c00700d009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 308196025 1250 308194775 308194781
    0x60801111815040b0a03180f02311a04090813140f01030e0f10060f170d1110050a0b0108181506040204030f1101030516021c0c15 57
    0x20000804000c41d10480d00c5003445207410010700403981c4007030708110070409081040042c10404400d8640443d4072507030340b20f0884410350440425140d008800104500f149480c41040340e40e10b00020540400820510b0301903e02100761030b581c0381c41e030780300c601840310180050103032104c1c0395000f1300420040416092010b96900050080013070030400020104501030020895030000d4401031107580d038403022000440140c103e034010040315104042d1020940601030190312084c59110350001005480c0140600340e030905a445070182e005581c0410602030f4010a1403101c904581c02c1a15204220070700345032030f010341d0740016000d482c9008180310841003c1e4021403c1c0010136a0760a00c95158284000001e8000c03402c2c0b4500340d8409a03003680904d6260a14941c04900240700500f00740d034a1320340e00c024151004d0115244504040c00c20325560709442981d4000e0903844512801c03400046002e99520b940b4000d1903584440340709900300d801d01c19000011502d901c10a582a90081c110903035003d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 308197275 1250 308196025 308196037
    0x32120108070e01150c0c210b071b1707050f0d120209060703080c0f0a0509040e0304120803040609061107020a0602010509150c0f03011e08010c081906080111 69
    0x16401200c00c000780585160300180c1c103039040c0025034140082c06100644080c1c030010b10403281121b50302030021328981140809026501003060428940249161555070111b0041510061050f00e180e019002c1022201c840c030469400054806071074400e0f400000301c1d019014004040d44a172000d80c100100c004100ca201c40c02064a80c8001400000081001d9009072120640c00650900a05011030b11441303031240c000350900e5086140c03030100345841401da884482c1d5200411000145e038280360034648a84252403030480065420127040103000405e035034418102420920010001c203090280607800716151300c0d40b12000308036298450300c900e203407a0004401644900504180010500d0041c0580c911030103d0340040c00030103039081d84001007008060444003051106022019100a2140045002c4e0000da45c0050211101c0000311104075016040b0201d540d05210304803450b140c1000702c664111458204800300d64400b900e600c401089030360311107802982494107214600d0700d41001495 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 308198525 1250 308197275 308197289
    0xa23041e0906060c020603070807140a3b0d15050420042a090504050106020303010e10030b01030b0a150b0910020106050a1203230306040e060601321201 67
    0x72a1030795551064134030288010000e5004801003001452142c40b500e041c90b4402e0b1641414191041c1d001c801c030132581c00201c00b00d00461704900c4600382c2540c40e071070500b01c03d41410382d089a452038210030011101d210444554003400c1180000d40c01c02c80055904080c610036240100204c0c079003810900c01c10034684440b02e80d0f5000b0344812030b94134142405010324900851149a0317407100300503d83c60a80306405592020410324850110b40c9075280c2c00781c01d00a00555008603141d50400c405400c4000c005030044040900030082000080e18280e00c40d81100e801c204500c0c11940c6404004002e807a0400710b82c81c248030b81d48008240412910064100f10b842606d5008004e0b8090748181d00303c0d111801400e61150642e0410400f1789503040302403030210f110780b030134059100c00c117078148541414000108030042c00100400956040c035210f41c07040c4030305c0c00f0010401824004000781c0300910b00e095106010450501341040110b201c5034103a03c01303000c06042c2c0d548500c2c0350b0b00d0840c800c0c400c0c040d040d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 308199775 1250 308198525 308198531
    0x160b06010302070f0308060d06060323030a02100902010e030d03050405160602060f090f0d08190c0f0c0c0f081501050a03081204111003020903010506060a23041e09 72
    0xa105510a200741d03909240d000e41c44810001442c1c0f01511025001400250300c2401000c05a0014810f03005050003075118001031145407103528466502402070100742c9069a00502541c1d400076400210b4600004289800241c0640c1c1800102d0300031070075490072909842010504488240d040d030010748633600482c00e030b5500000c00c18005800e40501d00c1282c00581c0300101044060002508464001030400e00b21400e05000110484c01c0c10f009a0286010a001c02c04000503000e01400385425005800c40c06c001c010210704014022004035800d0a00b00700c80c1c40a072204000000031254007030140c480d15543c99a665010342561a5a1551008480600280005000d051929082080c2c0781d0006070135040c190b60030311101031143c4c0180b0544980301d820502040c603444103161030000403510790b070150b9140301002c2498291030001c0c01c00c1c0d002d00020094541400d40c803600c500000c03056050b0f00c14081508880200c0d060280e40c100340e02c0000d502c00d08954000c3c000742008201c1c2c017581800c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 308201025 1250 308199775 308199781
    0x3101a0d0305211005040f020d0c021b040203011503050403090503120706110909010b0708070209070944030403080313021504080a030e010c0f03021b042a090b160b 72
    0x343e14495400c1d40c00b24868941c032502400546400c1d0014090554840401030400400c90300001c103950300c94000c0005a04548000740c10b0350001e1892a0713000d4020344056244cd41340c075200c41e0000485504110400d640e40b400b14080500c10151403000b42002001c03282c0c40170300c580c0070480a40c08103804031800c6141012509580002e041a661341a0009021048036840c00b180086039500804045079005001c0094400607075951000c0d901506003030365a44422420040141c0301c0d9032407071032041c8139800a4001458030000d440c440030941d541c1c40511003090403801d20318600e5070107150001440800b0100811410714201c0c1c5010401b24021212102c6200650050051520075400b4011042c0c0200401c200821301540400c100b084040c501604600100c0d116420300031460541100103800c14440c15403001c20142c080282000304541c20454800f8884400c0c888807a80307420f00b008401c4000c409010980151480f030003c1802030b500c5640c494900d40f94450355a0084812600c0350005004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 308202275 1250 308201025 308201077
    0x503100908092209030215061918110408240c0703081306091a15060412030201140a0c030501060804030e12010e0307050606030606010503040203101a0d0305 69
    0x205003085400c60000c42c64200c0726418403078a01c0000c2401145007600031401c0c24140101c0c400c4120160080d8040e04401e01c629080307040580021740303510700c90082c184200d502c0d040c0c0e1400a004680ca582200001002e007801e8100c040c010030450b001d950100420300081210012411400740c400312030081c0c108608034800003031043d10035a00102690010700c8aa00040d01591a039504a5000304400d441c1000d0b640d80c2c0b9042e9404a141290680000b003526090b00104010203908501907141161803849a90b02144a6004d40e00c240580e040e42601700105141c005c0d17100740e00310f681e4180303224a0703450b2040084024100007044180040c3c0f9110001070000c0c4100ca0280c02154169507a06002911004010714420b00b0031021440d5541e4200c550b1500c20108001c1441d0cc1c456000362540d4a004020035003000d0000745002d051080030020800107039000320304408408004200081c211045a1561401c0c40b650603440790010790712001700050540001c0904028040407600b10444010000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 308203525 1250 308202275 308202281
    0xf090f01150323030d090206090a060e011202090f06091305040f030f0e13020705070e010f030506092b0e03100518011b0e0d061401050306010e0f160507050a0309050310 74
    0x101c02c02d43c2c1d00306115154400c0344607002030035041d00041200d8100700504001924501e0369603c100301007048400040d01e156048000ca54542e02098011030a00e940079000c0380d44000e40c0031801d4800d00000620b0103d942e11070030650012401d40400b007100d4645450014410305585506070040b9174850a079150183c403641c8003038060710000e49503007030ba00d4000c41d8000207074014400031a502d01070b119003c143d544409400c3e900070400b03015040d18051071030030410304007070b005031410100b41c2041c0d4180360405440d80c0107503180348a1511038041d08074080030448681c42c448080a50500401a24030700414280d04280d00409034001140724481c000b105603400c071180910076003075605000c5001c41d0318a005981451340214007078080c040300400703540c4250480366810f1410001c408000010310150404001d00d502505000c922850360307042440e0328801e658002065401540c403101c1c15103070401d01c5582990903042c1d0090480304058540d290282c4407000034040c25000b40304240791511040a180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 308204775 1250 308203525 308203583
    0x21020f0f04180b043f050c060a05060103060902040f260609030d050f0403080c0f0d05090a030e09100b18100306031b032102030403050f0c0f0405010302090f090f011503 74
    0x40669290f840046100000001303c401001c018006c0500c14600075035018400c051007018680307030000c0c203860a0000503048603907a400c28010780b8410b00003406a400c1f440c0b1540242d0b80000c41310b10f80305015180c000c2c59440c12000c04412801904103129640d0707000800b030581502000310500055a400031052a016400c580c0500040c9210010a00505102e002004c141c80351101192400b20095041002d0300d8042c2c5030400740d50303c50680441819071002c1c007600d030b070f150031107440700e140c100140d4010540080b070168244455002502d41c940c1d00d440c0210a507586800341c403187d607040d44501d0260082205100682e0800f21a064545810807240420000d8a911400c0411a1201c1850b0382d26198007800c000b4066200030407000c00070070740402050b908140c0440c002c0070f41d4801c0e0410b1081e1517154034841390207903040070014001a964901a06e03807280000300030700801d81d114140b180c906030b00d0403a07601155203004404017591440c00500c0003524020b40314400181650091040001090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 308206025 1250 308204775 308204843
    0x4030203092206030302030909070912060209060d09080717090102100f1d0a050d020703020109030605060a1701090512090d0209091002031021020f0f04180b04 70
    0x401c0008007900e009000d041480300421982600c1c0004640c1c4a01254959041500564408100c00e5010b140050003103601040524080007411b01c1c240f03404e8010085d416001b0096a00854100c156031100c03429943c1c1d0100c880f40601c480403440c00d244078194400c240968400f0241850881c4002c1d81c1c0048560185c4181d00604540c5e6600c0c0c0b9540003041d452411041080d26110098504800800782002c41c1c030003c03024124002041c0b9160780360540154401c01903400100040001d40e0304915401c040703d070860303004074641d503941d00000c618004541104010403a8003480c0241100150b0007100800c1c8160200c84500d0180d0405402c0e901a254419511243c00c414490060070180380c0030f60004c032104202c4480c4441030300c150080e42c104403204081c20000190400a140b003485a00d0f008680c3c0b2203d0010400c440d40106810018a0101c1d50044101520080d000d4a440c7d005076907850003a503040b1007112041c50103a091060030380701070312442e6000c80900d0042c80029a080c10500d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 308207275 1250 308206025 308206027
    0x20f0105011412011404050f100c08010b0a1815020708030304020a09090f05120d0b0d03020a03031a130203070e010504180b06070501020c0703261c06080a0303200304030203 76
    0x340b003044900840c0c02a104010f5403540500c0490240790900280214807071b034050500c25080d48e4200c0c0c9054280030b016541d0509000c61101856049140c1ca415500340780001565030000c0c103015241c40c0c12451285100a000050000d540101d0040100101000c0d90943e14102d0743c40c04131550782d02007920041e50151010380700300720f078506690004201511410f032001d011004d076100e0700d09002031174180b20b460841c00114844140018481c0c0c5945003070071034291a440d05507482c0255180102c0200a0500d0b44c0c40341000081001c05114546003500100f81e809a0b400803504400690420b40e1140041060208c62a0480d8003034400d54080e51501c40303210b00112214400500944605140260022820840d40c400725000780000d1000841000081210a14503c6d00000c1d11000040316080405d070401000342d00c0040f80304454180e04568032018647c51111028001844c0395032040b08a44102c4500404041d01070b08440011550f094070303800100048803201010344021074000340141c00c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 308208525 1250 308207275 308207309
    0x5010306060e1c031103040e04060c0908030306040507090b07050102040306060603110f07060f020309030910030c0c0b06060d050405100c090506040618030c08031206060c1504240c020f010501 84
    0x85090000b612050207417601e15010805040640e04551164020381e804840200c108002d000c524000e60f511409a440e242820a260050480c1c03240805860541310310b403201e000c03070340403486086030401400004042550311310483c50308a00030b45c80b41c402190342c241070001c0095500c1c0a4860b150040c0d0030707014410729145001c6200b6400f81d1110800f1500b40b035440b58488405007061014522074070208004581d0b414001080001c101d040301c810404143c11706002d4401c290b0310150210505501130112034694640c000080d0f1180500403096800701c4c9404104818094001640007180954520400280454040c2251500441e0060320b0b040002041b0802c42e1038881e103002202402949048140c0e19282d42d122740c00025140d210031b40c107500108040c244290000707100b54110400b100e00f2880c05014445081c0c0340c5603c1030007048000519400102440051081d1402078004d0015040c80501c03a00603c0e002803140607140740051141c01501c0ca0420750500c80d16059401400742454841 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 308209775 1250 308208525 308208559
    0x230609130c0b070c1806060e04020a0504030506070c021e0a0e060f1503060f0402040302030c1c0803041b0608040302060114010c0503030426130608070903020d0c05010306060e 77
    0x22610300d0101c507265104580000c42507902d501620f14a0b02c20452010258a01a5000820402c40741c612010500d8810100580f82d089041008095030503200962a04501e07401500c182c021035102924038082c803c20010090b5010f190180341910840d000ca41d800c01c80c15200e003030281b10a190b91340014800c5c1040c400c80c0403481c601b030361000c3e004007035404004602001c100e030b8503000642c982110201009001c907504d02007008650304403040e107085081034990b4000a55a94500c40d4480c0610903d2010310400c10300d4160700528aa00b01c0039040d40e03800e05150601c00072440002000c0e00000640703001c5526072140e403200f8002c903010341c001c1c440c1d41d003070035a2124510000c110141c140b0298280c000c000601c00d01c06103104a0144807010500c07620038a41d5480b240041040384220503081261074420020409003109903502807815500c1a83e80301015503d2540c1d540029602c6030389d01c0b10503420004070301410415a502aa401e001c800d0382c0d00b00c02d03504c1c414002c00d902d5020b110003512400031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 308211025 1250 308209775 308209801
    0x150339061b0f05031204171c090602071b0608070806130c11070321020d0906030b130527030a0f12020d05010e0702190308010b0328230609 61
    0x280a4520340441c0c580c00d81c0e0f82e51031503210703001c80d41580c1401e0b0100700501c20201111045081034880c1240f8018880c1062000700003240c240e01c110903500c113010000e001c210350648516540c410304402010240b0205088a41c1941c030400d0b001406490010320349a108003440390260344007610300c18008005c1079048015041b07160600381084180b081604064004100b800300440c003c07008010401300801801940000c09408581598040e5103440523481d84186054115003240c60f00203449800c14000401c46190213103c91611420102481070070045075130540c0b104228101910740e402d4610803c203441e4000c100c110340c003190651140050250158800708030a45400c9801407905402407024803c0342c400783c000403400d00c1070408203c000383d0100a8160000c0c18401810450001e5907001001007405008030614140c0100116034481c01500c1081400c6030010b4a800444d841055500010100e104e4070141c01e500c060021038084510440d29802803101800800c25079484410030610 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 308212275 1250 308211025 308211077
    0xe0609040f0f02031515040e040308090a0c06031a0f150a03020d1817031005010309140106060f031d060f090304080f030702040c08091015033906 64
    0x5196154200a40307107102c2480214841d14042c104815424002000e000c064844220015030f080340c00c0205000481d031214861703034810b038103280c81d01c40d82d0f0b01c5903545418031041c00320080444014450200d546a095040503082103102000c41500150032000c0025074128161032641001508c0481034001c8091170062040c2e1149003809850300134020010300c101da041d410600c044c445404940d204020329121011110340c1c0340320410307046040c5180c0f078070a80720040c451181819030b2240000c08010785030040001c0c0d0309102008109076540c80502031701d0180f090082000280c030300960b00c6c0014554442c1c03400460904001800c16580d02c0c3c1c0074624400020740142150301c424800016106000c100544100044001030341d2200c055106000984014000540c1880000c50811150850006081c010000a42d0020914249051a8004540903600041c2180c220b02c00c44900607081c0b846e1040c0e01d125101110701d02c0b003603007031560648040d46005010000d070b0344042841b0310101d42411600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 308213525 1250 308212275 308212301
    0x1030209030c0904060c081f09051003020607030914030d0207031e050715030b0a03110f2106010f12021302130b0d14060a051008090c0306010602070e01060e060904 72
    0x1240858010014421003c2200d0443c0e00300d450b03200340e9000c144d003c40441d80102c2d240109004030903040200303c0e4400254001da0880551b0742c0001103141106054010066401414241e0307205144c0c140140803120380e00401c0302c5c01c00c80d21034181c0c40f81000500000c05035801e5014089060455a07811b06c0d111140d0402e013002e900c0300320040b0228405104c804018170005081a03a0184846005030907500000c0e00c00344a1102e030302c002c20104140c1410f100d000a02184c070100c46418660004d49100501100c0344a6145010041d5807000c5c400100b0a0607100c0695800c800c4aa0321030540e0041001c503c0002d4109a01406014401c0c100ba005400c521031444406c400c0103894402484880e0030400311244425200c503064101c03906440b5040b44c116006a80c07500c19181403801185405807802c1500003002800c2c0d0014640032005d00c00c4450000000b02036032030650703403088003e42d10f9400d8083d902c50310b5035601c0002211805038038070542500000c2d192038140300900003000018180001d0a83c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 308214775 1250 308213525 308213533
    0x6090b0c070b120f0c070f0b070c05030a09140402071e03120c0c060e010b01080705070206090a030c1502031602130213030309090e1b060a020f120406110313050103020903 75
    0x124110a40342c0180c2920b4506000c41011842c00c1d600c0c0f0803507074001401d007000c442030401032440403540d81e03c4404401900301743c4c0c00c140c0d81c807844003c803049403540d4000b820500011940c840020782c031145030301c102c1d21901003007580b8410b8801044100c0c41660b4004201c05c1e803015001c40104000300003c009503010303007404c1004d101c03143c1105043c0c4008200240004500e0300c40c190412545104640e0320a074818020041000140d002800c510303005080a41480301c0441d01c1000c56480c031048908803003000e404024210390700c1c40e1460051410340110001203506100c4045014070000580c0d00906d03070314005242c0740e00c0d9502484501c0701100c680d0040c45808111418210038100600c1000714400c0c6d89242000307142609a9088a0801c14460b60342d8000b41c1b031a0b9498140f204002040030001c460711541d9044803031060345810041410a812401407200e145d414450500c00f4108131070403500c0305466140c561340810344a200d4000ca100810310100418401c17940b0070b90180542a001500322 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 308216025 1250 308214775 308214779
    0x1260706080702031303050102040e070507030906140f0d1b08070906080601090e0f0405010c0e030606091e24040608101d010e03070507090618020d1d0303041101050406090b0c07 78
    0x1c0045d200301c81e081940c05a40000d02082841902c000c1e00390300002d40e2414505200442e0b030014200300040c40f40c1c3d0108411304607600045400d0714100d50852900b0301245030748031003003c0600050302c2d0f00b25142c060050003458501c8114010030340d0381c2c0306042c0e40d5207400e0b240e81800000ea9009401929445c10440203000c08102440350700405800303060b5200c40001c0e28a05454614290342a5002079020486d03448103080702510300180d80754110400b26036440c9160340c0c40542251020611581415920381d1106000607004940318484900c02400310000410141e0b10030300003601c0051291911a9020148142d0b40b00015408040c2e080d0350080440a40c225000501d400c0d030b0503441d100022038200081c10301c108041009a140104100c0106004083c5050364102d444180b003501070b4240c0350000b8045070128a00c0d0b0000903004a102c0c0c8406000c6c68520303d40740e480c0c00071281200e144101841010481d801541601d08640e842e42e078000354603040052041d01ea410440c46070341288601200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 308217275 1250 308216025 308216047
    0x10080a0f050408300123060414061b071d060d120318021216170705060a0e151b0f060c0c0114011502061302062b0908030126070608070203 61
    0xc5503001b0000700101860305807000c08000b02c204645820345c0c1c0718800800c401c0010708054048003890f030b8000c50301c8640382c410341112094409104001c1e80300a02400001080080c030710300001e00c180d041000d42007403039519542400b44032940b0030409050030b01c0084001e100544aa049a03003246003583d0031008130b4080b90b0110b980e0001d0721031078025640104110a900882250031640180031a028000c0341c03030300e1045216259007290003240d00805000485808041c06810401501d20019000000e40082d20041c140c0c1500325000c44040e504044081c00090240096a0b0511040c00c0703000c0c14540c1c07600600c40129078050f0724a03200954136448140014407e09c88418001c000505d0201d8180c0185017000703003440002052040c0072428850740ca000342c1c80311402e5801c3c040940143c0594035203845444511192092403510520b0f041c042c040c400c001d84800918100e80314070300001c1e400d0410b0351506804444c120400b0140358024078081001a116100e0301c0d030801d5550054a2900c4107c4603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 308218525 1250 308217275 308217367
    0x90c0d12030902090a0c0f050301050d0809030a0b0c04060e060a08060111150a0203101d0c0304110402070f0201090b0406080c030406140f04050c0f030303180c10080a0f050408 77
    0x148481c8020b951b0744144030041c0d0850061280c44280346007071440d642c14100025904d144052024000d410049403030040b940b420003e1a40a64005648041625014890080d1940140074640000d026900020f100307040a409a61700c50115859070000c983d20a4011260100241c6840c1400d125020140c0350302d480c4081e8480c00350799006009a500e25108014a40241e0681e10124003a09482e480102d1442c001030b5103030f00006402c212580d40e07121414900c46802d81908030652151000030b01a041010b03020054000700c1c400c0c3c94002c4159034805500009004e207215200105117810b000644400b4400011980303e8450305000840000010106c0880002200c03600940316402003403009111040080140180007200d2401c050440403000c01e440780006402c0d5200130103c0079550100301011b0104950451014012041701ca03485200100103a00645a13240700c24581512254042098000d40d031145800c216402e2a2a00c24950070741404407005086c1c03246078a0100209a08500c42 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 308219775 1250 308218525 308218531
    0x41116030306140d020105040317041a070b070819020f0d0c050301090e0105060619030b060307050703080c030105010903020d08130f1805060901090915090812090c0d1203090209 78
    0x80c0e000101c007030804031883e041c21901210240303d540c0d000281070050f80d0090845007a030b0740c81110817900c207041207070108080c01650010302d550308203140541c11414000000d0801c10b4040c02e55526070380c54103c41a40da0f568142c401c0801c4910207001540c09503100d40041c42c45180c1c0c03441080c41c00c20600550360072980702500050000d9030000040080250305d028240020b03030035900810042c144400080e4040c0700d94003020748c41c1c40c9418802c0c103040e4040c3d4001d0801e011b01401040c1d40f031030070081c024010b42c0001c4013207000c2601d905c0031801802916055030f042e01c0701a1100c100250654080103071640b1010004c507041c501c2080152003049004410320024450803040050b05c07070400c405600f48090750103c1801c401d01e010b08202a503900d031b9039004d0445000d08400112a0250300702003e03010080740f08151000e041c003c41c803082090550042041801401340319103242c0780c0741c019944031488121200c3e407200c1c9114220011441c40c0700131042c0c40155050000d01c606c82c50f408100c0d015022 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 308221025 1250 308219775 308219777
    0x10b07080409050c071205040f0e060f042c0a0f02060f1606020d0b0607020d0b09031b0c040b01020616050a0c061a040c03020f0f0304020409020a03110a050a1404111603 74
    0x214050007001900200211b4410042c11f20b1401c02d030801070380d012040c0c0316202e8169000a010089840d6071180c2c5030440002501500c240120609040215070740c00d0090090180048544180004044045aa018a103a010540c01190354032502002040d0b000710403465062001006181901b42e0040c003012040da01c540c80244e180d04412180308112420724201c00e000e141c00700401d5005a494040500802e54400c2c0c0380c88250303d82c480164514001c40c04400d000c1ca0302c82070048015000019a0301e40002d007145e05200c00a043c43c012601c500040d11500c4e42c4d281000100700425000324003034520421249003030440d41d4032584440e000d668401c01801a6074824110100c054205801240c0c000003c50900750300e082000b007421452840f981042c0907940b10701101003000c6650f46c1d000701d81080d0f0010320404902e6120b092031454214100c91561107041d64010000f11814445606001c5408021044000d40005011b02025010a08040081081c100440c140c4401101d4812110740d000f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 308222275 1250 308221025 308221027
    0x40c09122310050a050c070f0501020f121503010c020607030902010c0b0c0c070f05010203070204180204020309100507020109120807020c04060915080118030f0504050604140907080708010b07080409050c 89
    0x1001d030140c022640c015100c004d1050821007004401c0a07080c08844443e5809100701c400c000d050704006009004400008058a030005800140401440c071a24019001d02140c01c0d003000c88803082501300e99026080c20301680140000903281c0b8001c2d8010034980d4018105410203103800e98600400d1581111030410000010031140301040d000c00605024041011141c1d025030b08040001c2e60f60302035104001e1060f500c9031100c0360100400038090200560140055490342846118661951a11510095a6858038000412a51050180c0c0c3e0415030082010800c00900240458501500030300110940c8607080814030b0907122072103028000e0103034078000107031500042e0541c001a1b803243c1c401c07a8160b040c451241c100d0324040c003588003510303410b041c8100a884486020b45407802164003040d48030034007080c001104280c0f041301424a120860b03080001744c0c2d901100b51800c12003660100c00158203000140f2103007581c04000c0c60154041c1101c1c5041c540e075070b810b440540310100d9000e264100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 308223525 1250 308222275 308222293
    0x40204030f1209030201140a020f010207060623061204031e092117090d08040803030604061205060c03150d060e060702030403031e0e0d0c0302010e040c091223 70
    0x18080300791540740440c610f041d640c82c1c0d140d900001d00240c2211042c00d0649070000c0c41c042098000c20641c025000707600001d5490700001c0c2864002004a8440e0100341c6403c5825100220300d903000d03215020314000c160604240100c40e0030030341031500520890901601c00f07000d030203400b8400d82c050b00e01044c0366201c3e801755041108102c9000c526640e204030251341341a50100140c029190750005114075805c0b66102e245120014511214512015202103000200810409804402580706d584103071414402c007135440d4000600301c812400040c01e281c10500104861240001c01950021002d00b510409040400d001580c450a52a412185c581c3d5070403003000724410030311007640d104017107001442c03d280ca107880c0a08800481101035000c03804030090070000d1400b41408554049000d00b09844908840c5003a00880781d81e800141c1c045840014418468582400351a004140c0766446040c920710340051030890300c05600e400c50365070106490500c40c400e8515110b05512080c3d50060403000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 308224775 1250 308223525 308223533
    0xc0d0c030902030a06050118110912070f0905160e06070f0303060b1303050c030a21020307150b01270605090d050102070503030a050f010f060e0102070e10240806010503040c05040204030f 82
    0x280700058440d49040070402d485c845a6270040d03070800b0308243e0b0460800100c040714a4203081054000b40e0b00e02c0300e2045c000c102811658050b038452048200f0410300740caa2020f080d50500d461000d02d42d4003080801620b40011070440a003103050b442424085903580d2203d58541d8542c00c01007620b10041c6816000300240030007007101c12078080003500607080d8401c207921608074444540041c22001b00e0626203101c0c000e4801c1044901480e00b00b00144c0ca41e403004070540c030181210b021014002242d50f1010483d4030044141003800c2380840240c855440d141100a031030300c1e0009120300d03502646081c2c051010410030300042c2030307032440351f4091a52490020f035200105c0d40c002e092900c68180da100103002e04d08612540c84140c03000d50801c0c20209159000403880d00100350800801c80700d50f2002e005001103d649003030b051342c049429203c0102c0e41062079031001040c1c203424030700041485000c00c041c0e5005000454005000d040007141312034843c1c0110301a80e000303600494540c0c0d40340005401384 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 308226025 1250 308224775 308224799
    0x903070c0e0402060909070903050d050a030c0207260102040f030b070807050f04050f120d030c1b0b071103040306090803060a08010902030d03050603210a0206010e0c0d0c030902030a060501 83
    0x740480640180403410b01c0d402148650040700c800e00e00403d0010041080b55004002c028002c0d0703405030440c0d0341c1000c1c03500000d1894101c0142480481d0625464440050000c164042951003000e4040d00c03103948450603d41c60ba41c2d503010010f003558208004280304d04a194018040d6005100c00862410110b00c020080e6174003c01e4002006010b0129034421101daa040720102d8200f12400b5501146280c00103400803607071817603e030503846040641460035030190041c0308851066120039544900e900080070b00310b82c0b00c00008003060340030707000592090302880c2c410740b07030170b01107001c80f82080c1d201d940303000468400900540d910000070040003028034010000d100600403a400a01c1b00f4400d50b4046039807004c21145010502d0f8495002414030b0300c0800000c120010540f035076021000340c009802c8080ea11003400b00005001c3c0d80004100b440b45540300a0284915a5a00303140c640441d03402c100401c0e500082e01c040589130200540540d0f0f04002e4a00158001c1d0400140b65141c10841a0f030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 308227275 1250 308226025 308226029
    0x6090311120906070c0b0c0c040f090b0103020907140304080c06061005070b0c0f07080408010c08010501080f041b0608060103060906050d0b15040203190e07030c15030b090903070c 79
    0x210354881d044505400000000351180c003601034a55980b41ca10b2031800c0412011650042e190030700020a800080d010009450700710f0362810b0300d082140c0d110103103803d01075420080d00a01030f820320000400c0107080001d00b8a9110290b8a04049441c2400542e100c03103500c103440580b444840401c05240784ca4091081e035421000c00c4840700820807403244007600e5030043d001c01408603c802d5000444124a24080381c0100d01c5e00842c03290b1310011894181d4441e0040d000300e9201d0361900491000860082c00120705a50050312000c8080e41d8400c60b400c05510001c00881d843d10110555190804030011108060a41038070307003912070f00c1c0400006048450035840312140a0921380304101d0790b1201a02c4803070482d0050020b2002d9074510482c4454108095099074019200108104c816000c040844080c501c020a040c0541080c07208202e076a0811404041c0c5001e008000400100324000c10760705500007907090101d02e1340c844500290f00b96508680900d206d03000010074604000f030109a40d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 308228525 1250 308227275 308227307
    0x903050115050a0918020307060207080c04141b130314060f010605041a0f0c01060f0e011805090f010e0c130204140d0c0312090f060503090c2704060903 67
    0x7140a15002c0011202d9400e03100e0390103010390302c03030443c80f002500c0900600f1664014089400d50740c0e03240402903030b80300e1b035101c1c21080b0300400540e50214501b60140900203240e2a5040c00f158444082200c520711201c021410402810880d02c40c3e0109200300b0b082c011402010826100820840c6407400c0020040102d210840c62100501107650440191020ba13070150f420f121500350300c1c0038001c403148a10840000030362000b00d921003014805401103c01d0f5042d41503420b400360759517000c80c261f00000707010b6045840e100d10341c44402c4651a80c0303d1640300704c480048400114003400c05600710368495004203040e802071216403c242c18044c0c40511084038140302140303450318112005c2a881c1101001610464855110030103008202c84088091038101c0240700d400d540c42640982a9000f80c81424180700340107c000884601980c01d50744140d0151000d0000080d501080106404951124502e41221a01e84111000d600310449214601c117400002e401c07812400d000e0081110a44241 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 308229775 1250 308228525 308228561
    0x12060b1305040521040f090203090c030703030801090f061d07080705041406070507030506010b040f05120606010315090204081605190303030e010f020f090117010b1204080c0a0309030501 82
    0xd200080300701c1c03032048040d5920302c104080b124112451080703501424402070003046c04202c0175201da0080d40248184001c4030f00080f00c0005058980800f0711011740400d461600402c4440c40035000801c0c000b4410300d000171655120309003450742c2c0030441d40d520f03602e441440c2041200b41e0031240c40c5400941c0c1e420a80d08040c42d04581035180b0f807404001c0e9000750380c00705015007000030811002014551000560b0820341e10750416a13915041841004801c41d074112000645080040c03550716040c4d030340001b2b407603184d80300d40040d005041612945600c0d1486a407002032a4200b8ac1b000c2c001034550740001d444283d0b041c8100110741d0104e904241d108a01070701c032076450141c0c084041c40032030b41d143c24081480b558140c0b000380188403440d5051011340c0002941501d04261400621000c030003626041c150501c41c0340d80030003070402402800001e8004002ca150354140c00c0c3c07000f0b52301a10035841d481c80c0000c43d8000904003000003400310003268001605104102d401e01a160001c1d40f03160f421 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 308231025 1250 308229775 308229781
    0xa020705041a040902130504120f170a02090a031713080f0a030f030204031b050306091614060d021b06160e010302091903240203060a06051312060b1305 67
    0x76a0b00982d410310094800d0356190300050031900c0d9014139410741e00003d8020000c0c2d18050410080190a100340d110004841c0e004052609010b9590a90800800001426982d8070808c0c5e03040203500c0054100c0d40320301400c200000240b6031004092402144240c0c49407940b424420180700150207405c5002240c02295841642580001d04000c106405182441c0100c0300c80005034020310481d000548a4500c0751048280c4138060001311084030000d400301c86044d6035814040b130320307100301114510200c5400d031410019120076480c010303420302d0000c180c01e00e40240d140500040764091000e0b0040261a40c03003410003441c0500260340e2006184541645070880d40f0401000d5440d681102c030f040c16030205041d030064a03a0301415180b1364201904034070300c40e128101118100d0b0910000190140c05401c945407110190082c1c0c7d005100284c900900039080040c141c8a64000e44450003c0000966000400701011141d19104134050b5100151400c11001840103001d1619580c0c5401070410b418 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 308232275 1250 308231025 308231051
    0x9070915020c1008041a040c0302090f0702070e0601211a010206040804030308180d030509010b030c010e28090f06050d1e0201030b04020705070815060904110310110a02070504 77
    0x300a40740342c3e40740c8010195103625010717581c0e08540800c80d504044000402040040d040801e10650b8003c8601e11202d07944c48080782c0340e4207021030752000142c10400c0f0400080c503030440d006030000814100080d0000c6011680841c0d84000801e01000a4991043c1006c01141e5040c00c41c0504081c8042d00303e900c0c140d121b04092b44a50700c0b00804102820002995200d848122092180000300503603c3c0c281b0003000040c040d02c41520445d90725444c00794a03007554038001403e00c5c0c1c5e0820603140c11001c440d1395020071184000e0150801c405d14881c06003104c1c1010b20740c000b44041c0022020028103c0d004440d5202181d200d50081030290403020204d10116101e000540c00340c3d00460f105045000071807004902400b80c0c5401290000d0005c900c28040cc500401c10343c060703802c6c4004584400280b940107501d111425a003803a008a03150000c14042513040d84101100d00d00603081302d00c01107240c07410070202e90015110707514008011410910255050003828000c0c541198180064200600b07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 308233525 1250 308232275 308232289
    0x10512011116030309020a2903060f090408040305150403180f0504020c150705070203010b03012304050a0b0f0708070c050705280e0f010801020f0301050d050a0209070915020c 77
    0x402400c0b1141c8414103000b01403003904034101e055806400c1343c0e1156515204001ea0b04603a031080800220b210540c0000520352400762482480c3c020801040c02c3c0c0c4000520032803040280084e030f9829420840070011401c01c00c80c205000c03088400ac056203107410b04004240071051069189203504444007042101401c80000b03007990300403100184c1d20303400654507928010001249122000001d070802640d03e0b0420060161b443c0260001d02550036a482003500b203980080d07075103400101218000d903810000c02c51507a400340c410300407501c45c2105a103032200120400c940340800c1d040b00b03104014425a20005040c4c21007203a0901c1c5020740165078800c1c1d00d800441c000c443c0911020b00005101d031b680310384a680301000c00098100c0503a111203104828420807101c0600c0803032000000500704c1301c144200c501e00520f4008032825a424101048001f00450781c0540311071003800124000b503500c010440340240d403643c40360003043d403610404440104078155000c003990030040c401d030b000e511168 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 308234775 1250 308233525 308233537
    0x1060501080414030c100b01030e030304050a060203060d150f0b04090201090e190e1e0703170f0415030507091a031501090b0706090209131101110c180105120111 71
    0x3030324043e682d1103503404403450b50081a02c181d00074461410201a00ba54a40c482d40040704281d9041c00110302d0200c0e600d030f9070300c0141c0f001003842e0700800427100841c4055015503040720300144410b502e005641c4401e0410b074620044011800e83d105041c2c2d00c100040d10811088070410381d405d000ca510980c0010340440d445126881201d40300d01d00003410247e49002003001010010740410040424010065641412040c038007403400d0f60f00810003030000001044003c49512030300e18048241c5026001c01175410440443c14003250a10001c81c203900300400482040f0501da400085500d051140100240101d40c0b11780030084403c3c0c9148501d81c00074080343d510212a0542130b610300b2000700100e4446e54030b64805100b4003070102e80d03c81040f0143c0c00445003640212603482213500c6200c45c103107420103494401400c00220718028442540148010200a0421015a0400c1d80210045402410030021842e88001504014415460821903030803540307550000801000541444100440c4595 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 308236025 1250 308234775 308234783
    0xf030910060e070c030c140109050601050a060302090a0b0a1206030f05010b06041505031b04060c03030608030307050913060509100504060b0322240225030e1c080a0e0111010605010804 81
    0x21b2450014413001e00071800da0410810001c01c40c05c40c185c10040e441c0c890a0040911844500d00005413451184c001d84503107a00041c0700c440c400e898055040b4441d40050400010b05c810344030540f480345190321803000110301982c9d80d07407640c549034500300d821905107511142c8118003e00c070034440d183c44c0c0e9660200c00702c1d2038109540d40f521101010460540a0071242a442400050114007140c1c032119800d5410b1198a090084945807403210ba160b0204403640344c0000c0c001c2c000f09a0038a0482e03140d4240041c055000074880382c03150081f030f0f058501101d80c2d14071030100c003c0800c0b903401d040c441c141c010a1034812007400c3d41040c4c440b03490912044241d2427543c0c503c0a00e01000d001e11900205140c0307110300152041c40032000c2c00d04000c0c2d00312004203840d00c101034250500150500d401d461619a06640e00c0e0341025050080141e21a20943c40c3c65890624035407081c005001c850042000c0e0042d07841e650154030700c0c0380004100381d42004001d51540d041440402c031a90708100b8507900a0346c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 308237275 1250 308236025 308236037
    0x15090501020706020c03090102060109050c09210703120e0d020a0e1b030a060f080d02061f0308040e06102c13180b06040c0813020103020f030910060e070c03 69
    0x904105029000d80e94014140074800030b800d40e4200340000c01454800c0e800e800b41c40c41ca030b981d2a51041103400490308102060300c20018010702c1d103400c0210241e052204850500c130407103a00015480c0810030380007110900040301041b404150050041104000c0031910302000c0a05513000c10181d0703065201d440894103290010540d50044d841d161140f4200caa0b24617074881c50b140083c1400f400309449603025904d405100801c804102054a250080b03550300244802c7e2134110ba603c114dd0050780d030507085600e0400b40800041c01810080004007485100707003030b0038205103003000a0005241d41c0113050108056a07108a0100c100e07a100b0a5103200910108a03104034000c00d121048a00060001a06c1c00c42500000e1042c40240600c03d4050309004015564000034482101c9241a10720080741000c0009400306030781101070b0805a1040c5809401c12207024005040c0e0b4106540290482e080070408500d0300004e48210402400c1d100c031384a0721820700807000f901e0703400241c0d00036040146c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 308238525 1250 308237275 308237291
    0x10315050a0b0f09090406020405090c07031b23060f01091b0f1808030d050703020a0203070b100b0406050d0c0e010905040203070c150207030e040c0f051b01051810060315 75
    0x41060f0540e000740401800d440c58500d82880e252000754001c0c003646100b40c154134003141080c000c5106981d2140d9064035041099540c0390100c15203c481313614100c1e01020307210504c1114140040c54810300804200040c00b03141482c3d07000360034803141600200c200c1d5140404007010f240003c0d8040c80e1015031400e003071078140180b000445d007080f0070407041400b41118800014500f8800030003044904c903200820001a100d0318402c0f0241d200318001000141d0041c442000071458056000744c0040c41207082c490381a035241c0d40080345400a41c400000300d1070214946408a80034000c0c110070104918002e900c0c00c1428001902c00459401454055603001c0b001600d078a0091a05034007607604542c0c86082d501c03000842001075400f0050480005123840b1441010342414013900300082c5141d200c40500140262046078030343c001414501154002e0800d03007a159030203100700c42c00348600410b00d1303d03c000c1c0110b1007890214480d00c1310504500d04101040451b13110340d11907000e07400901000c0343d514 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 308239775 1250 308238525 308238547
    0x2d05060a15090f0f03050c330403051903020f07030f03030b030a02040603050c150913050403020a0b040c060807170601051b0102030c03040c0524090a23010315050a0b 73
    0x541c2c00c2c1c2041c0c001035001c80000c00e8624554100f441201c0c410400c9490001281d000c1c0220030340515480303200b0003010044180c0780c0075010020145000300441081c1481d940740c580301d00d4040c001201039031000d0a213200105140c0d051150340c011500410007003c40500d55580c1d092505c10400c4050109543c50003039108a980601c825000260020002e20a490b242d041040e00c5840e400d10951095010340d1101016940460980c0c68440e00100050108824285103101420300180308400318080c0014203800501d202c00014001c902414600d054a424490050034588000c0c009a0030b01c45c0302101000b205c5018040703594010800c3c43e000b41c036515404605d60401c9600250421554004402c02c80c8409050015503c03407801115a0b098580c5e40e1004d03c07801600000010880c000c1d001c841810b1098400020030802e0702c00f510700700c501540c60402c0412000b145007e00311494030b081d000070399580e050143c242c0c00c900140a800c0100d00d4a400900504614400d880c285903010034150400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 308241025 1250 308239775 308239787
    0x1207020f030a1b081b060106111c020c090f0109180819200105060901140303041e03020901080606130b030c090405012712050412020603090106092d05060a15 69
    0x416400b8403010341710b01c10f5122a40924208910a0403140b007a07400001d2041e10410301400d503030f080c2c04003400740036602540b40c15801d4000200030041d44120003107280c82d03880b0269520b04c5031204200c1c01d502035050200c04401c0c0c81e011050761942e0000351440300007041070602151141104046c040000c1c1e03166140c1540c410103107141030f030606100030b607840c040248107400180c0300d0341048426403e560b88072880886906010f80303005802d6030040c041400045030002181da102d038829501341903065a0b0b0b034005500000c00b43c2260b03505c0e8000e90148607490070654541110580e01103030510000d849040402e549040001240d84146c1980b000304040c45000c0d44152a1000c400d030140e4408001256a40d080d28038554048409800c152455a000c5201d0410750b8180c2e1030b6403a050b901c241054003040025000500454125540c0b0341001030944040e1040c1444080700c16051031011008103421042c1d082032880300212141014100480c0740e4803c242d40781911012107000046da2941d8004840c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 308242275 1250 308241025 308241077
    0x606090e091e0c09090303162001020d090519110f040b03010e160605040b04060305042307090e160603150e0f0609010801141b120c1207020f030a 64
    0x20107410348003414a681c4085043c100c82c1d8000c3e14220344c2a21031815890340e03031008885144d000a001000000010310480e5450101440c8031410342c1c08100d0040c0f01401ca078406103030104020758076480b20b0f0070042c06202041814240c80c40c003032102103042e2100c07c12100740c40a001d104000d244020300070350365294005005690301034000c000b801c26180d200d0380e035169114507010014814800005000d0320840441e030503608041d00080c1803130316181c003e801410f030103402103403404000b0054004904c14001c049541829000003007903001c1c5040c000c001181c61890507200703203800a40ca18103550b411071052800300d52082c980061103074010350320780240c00e9103508034120200164041c004e420310550350240c001c0314200c7d8401e1450b60307550b6a1900300d941000301030303400c03516000020f9455200310003410b1030005045900ca1034174041c00c900c2c08041d8021504174071680e4011030810408035900d0185513101c007550004202d40d0b90a4010140c0d24010b4060050802000615034150700345070444e031030a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 308243525 1250 308242275 308242303
    0x14090d030e0328030627110702100f0f141204060b030d02030a03290f1201240e01050102060411031903080a0f1505010809030c0303040c1401030606090e09 68
    0x3010000c000f202854040e8120003c0001a050400100f959003c10307010a02d803820010602c4102107420040c074018280990b0900c0300840c1c18001000035882d48000c9c0041000c107540c0c3c0b681c01800b00040a401411304140c000100140c044003440c050026504682d000a4002d40c0e90600c3c2d510b5203030020160222a1840340c142c081c181c141144640c000005e01110f514540b000d00824003110015100d00d401c03800300600c0402e10042c0c06585040079181d18000c2c0d000035041e00102da560841040c20b65403075140f10a84800484408010340c06504001c00280c800305541c94403d500d0480000d583c0c2001030006484c0a41a049021199400f00a01c844144582010710754904480c00c0181c400034089039441800c038189184004800010b00c540c802d0440358440352490301d424400111400c8100515180c0d00b8481001204007401c010005944118403e0910540142c01c00b4202c0c0044044441c2a03818503041078000e202d10781d00301c980c54095070050b2008445694070403c80510300081c00510103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 308244775 1250 308243525 308243557
    0x21c170a151509050126091507020a050c121e031207030c0810030b0705090f0a0e070909061a0708090907180b0408030a1b0c080a030314090d030e03 65
    0x595a900790320100001d40740c2d501c440314a9a80c0b1401940c6400007641c0320256540e0604201d0048405100400d4100000600301c071140626901d0780c0003030f02d1003902c003030780586c7c000002182001803c01182d00b0007081551500034143c0c0403406981d0f99008080d0201040410f40600004c42404006503000ca0102e4501c4089030b0030302070006001400c2c8140320100054080f0005545e0041440c3d814084940c0040c01c0074155440303207811100741e00190b01280d445850140d001c20290399101080d03001d002d5a500c1c04145081040024200d08003560240b0300b0281480070400c0107051030034111003500c452081d0305a8920641c50050028403c060711a0707800014503040c81155a400407d0b40300c1c4924041d4071380c100030f0310391980c100140241d115091443c3d00030401c60761214070446804200b81a0100c0880b441c03030740d580c0d03110b1060710030703070132044240c3d0001102009060f81401b4408031160551504003a0342445503243da12000000c03400c6003403584401c07949040903410800c4817010b201c451100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 308246025 1250 308244775 308244779
    0xa0b0103022115010f060c020f01180f0906050301050709030b1306091a01051905091801020702030d03020703020118260c0a080403050d05040f0306050907031502070201021c170a15 79
    0xf00c42501002c1c0582e2000003144c1501041d40c80c022041030581a800418401d000c1e4416001180c245009040440c20b400200b02c0000d400030300c4214480c040c0103094404580103041405050841e200201000c1c04c0200e031440070008200d1649000d50840e00c0301013200b4001000b41424401b6141c034010040c10350072a45c070300346900070103035240364141ca00480e600200072410b8289405022900d000e000c0d403004040c03000c038a8048080340c0744102e0710000000581480e0b52600045d0800c4088e4002601017500080c02008060342841440f40301d50b45c0c011602c810304056100c0070010500c0001c201c4580c0b0300b000d90841c0b1100035000380c0315114a14030813120a00c00c0c6103010f40d90740c0c00c503200c00c803958820440051210f81c0135205a4054901784d00888560b00e103180c64030400303010301034911751036806948004008261341d0200410f00680400c07003d46c1d60a000d00c00203103888100c4200001742d01118449582c0f42c1d6100d40c0c1c50100f0301410450544548482100344018070080445909408200c080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 308247275 1250 308246025 308246053
    0x3150a06020d090602011a0909010b12030d0f0212060d020d0506070c0c0b04080a020d1401021305030c240d11030403170c130303080411120601050a05030a0b01030221 73
    0xc25540e01025600d80081a84c0c4090503400d8030180404950708819040d08100242002e0380c3c06548468100e002241030700c2c1900102d80c1158007c0e06420042d0800a00f18001c901140201c0591142001086140c0b50300400142c805a07009046c0b54420200c1508020a6640d002c503034000c56500035056644500708004058101e0301c80c0e550840e4004582c000000390300c42e83d402503400b1202c2450150450007400da0030443c06240600007220244030181d0000101a000d10182040c903403904009030f030700d038108800c040c506940041c08138030900f4502c614036024030915888066000051580507101c660400203440a811040440010500003200700018941d201c1440c103101c280070444200e490301c4072610340701a403203017443c0b420740c00281d01010070000f440790345515406802680360015290b0039800056174611324035100d9074968003034401484030b441e00e641008001d002c00c6005060b0001ca40e030340c440000c0d60520010b48501d0030002d40718400b2105403200d0b00081c0c240001d5888034801c400c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 308248525 1250 308247275 308247283
    0x9061b02011d1617030408030c1f0507120f061a070c0e090309010c03030f0e0c0a0609120b13050a0b0f0609041a06010302090a170d0c150203150a0602 66
    0x818158128284800b1100d8000120320030b03070f0500070420740d007400505041050301c20842c1c004901a4a200070400000c68807002d1000d4030110350804e003e00b085000740d84d54400c8085642e2040000c0a14101c1809180c2e90482001101c03018074243c04074003207151002240040030150300c01c0407000e440a80c46102008940014810f07030f445032001c1e10708151603e80080d400107040383c03583c041d17900c10410202c0a602407500c810002e4403e00d008107208004c00c40e903400350740d10110b00215603408001050000e04e80903080e603024055628015a88600c0d000100007864a01100548200142004140d80046d10300016800b00d0700101100c002400b10b1600c0c42e11000202c0b442c1410a0380700004c181c0500d480d4048900864110502d0044c007000034044400c100d0b00500342c40d051503820401640513031a0542144002c041c84032441e0803503400740400f82e0402044030310031010000e0303901c00c2000064601d000c41b00042d12400c001603c80c1e4500c5000e007038559130a0101940004146000a80258002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 308249775 1250 308248525 308248541
    0x4050c12221a010b0a0f0e040609110909180706030b0301181505010506030601080a0c1808030421030c080c0102040302040216031b030806010c030c0204050108010212070507020901030609061b0201 86
    0x150802005a0781c4d40c804a01c0341c06092001c0c400122080d640c0f001c260701c52106259000c01c0240000340d242d07030300d4070100207c9803202d02d0405a1000402c1e420842d00d04003003a0b039402002c451155078580308118030b040d116071050060701d0070702da0b56040c0e001c0765850945c03040000090390b0301c0400034501c09003040b507148011081442c402508080010a2600301841981e00900040e100e0461381c2c1ca4210040d0050321500d0b402c08208103601c1300c005031941d8540341a01c000c10000016580c0c0d1401d1840d07190440c110400301580000d40c000029001980c031039484041a50043c00f400d84400c900300619000e0b10995201039031150001c903001c8450302a00034140b900703900c25140c460001c2d1600c501c00c00443c6c40550050045140703a4002103495001d010a40c0b002c9106c0e1a1400707a149059001408842c000e80100d0142da40c081840500c2040090000307400c500a8101a402c01c1011340c0007a03c80c484c14000107100c5c58880700b41d81c042103c16004400001620343c030884090100b072070003e000701604 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 308251025 1250 308249775 308249813
    0x60306220b0a0603150b0114030405011415040c02060c0702040507050f040803120f04170901020703170403060c0813110105040b0a0201051f05060714190c050f04050c1222 75
    0x9841004041051b204510b03803d041a100c1d18444940d031140b88074150801407043e141035484060540c115072440c050f6174030890990910b1b0740e03210b501006001c21070b048444070b601994848030622851049980641e0442981281c02080e0b0740c0e204d040c21105401078020035070301c7c120003040204a045011002e17203041c03a4071450b0040903a4a4000520100340c00341d038080c0410740101065003c00c2518002002d00213030600403075407800d42e00d40c1c819003501d07100c818007224200b022406000300a00340c081d10205602c44d1402600e28145140e85180c1a41b4418009040807500d546050250b40100c0550b00100084500f0580303030b104450b0043c0c080e000446084024009000c0408a07124070f220341142a204050f00050070310301c036a9101d0560340f9007640d0075000c2c2e1213421400f80d2000b020b480c4003001d80d0301ca1480c00c94014031780000e200803c20707a10800c0e8401e505020820810324010816507002c1e015200b0140307260344425a40b034041f428102c0a03000e20a040a8400f010b00c0000001c0050401103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 308252275 1250 308251025 308251043
    0x307030203151906060c0303090c05061b10020a020d11010603150e070806161409040213081506010c020904020f04051e09070e010b03100506070308071205060306220b0a0603 76
    0x14040105041300d8141c0600400309000c0074003600468480d0b4841034915100f511100100ca85480014100e80c01545010a4940c0c13001c1c441e50210006010450310151500001c1d4103003450b071031012b5181c070008174401c01009a010b084885201c82504a00d000b0341d0040d100d0b0100001400e02c12000d4542d44040d566548101c0f44c00180070500081c20304d00c58074003005020300019006904480c0100d8459456015107024002c541003503072144001d001c2c1c11040301413110480d1809540c1404c00c0c03141c8140000038032804c4100407080e6040001c5450a90741215060300c960340d10300c001802e1584951070250000c0c80d04040205480144100308544840c05010801c10f950f00302000341da80d140360088200314401280100200c06000c4095034115a041e1842004191988003244031a0401c100a40014491000b07020340e80350009a0701204040c0342805004a15241010999646020340442000e01007a18a0f0300c0b91320f00c2d4420007482c00d601212941c1d5070304040ea900005440e06000c2501d22881d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 308253525 1250 308252275 308252311
    0x150904060f15080d030c0201020c0708010e100506060304020907110d03060515030405030403082b0c1421070c0506040605180a0b070f090b07030215010b0705060c09030703020315 78
    0x2c1c1e05003010842d100100281800600e041c0300310b000d070182c20b08820070356400b07000c04601c000f42840000040c00551000081c1501002110782c03420301c0001c1c01c1d4006a00c1c15052040302d4075604109c96211f078040ea42c1d40c0c0c031603d5040c1d040b1424445002d03420f0450060100500e40e060341904000103c038000c8850100306841061040c40f07510040e240104035600400003040042d1041c00504103c1d82d03160903065405092810300c1c0301540014000d8502c0b113581c0c039842d501040d001002d0240e000400c038509030a0040c410224000c040c4810804c00b4003000c13040005104d81e00c111031282125520100380c98103802c291a00b41c01030f21098030030680603c005540c0140400000544210160f040380741080c294880d0041a1484016080f03610300708080c41001151908066000b0020580309500400d0590300003001d01c04100010f0b08810248001080b401c008998001110f64100700e00c00f00700c640d18561200000d2a00c032960b1b00080d014050242d00070013584181c11042e00c0b40d5094410168051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 308254775 1250 308253525 308253551
    0x203040f0506010501022a0111032d03010510080408040906170706050309060a09230309090a061a0d0e0d0507210918090501050c090301060b040f0e150904060f 70
    0x43c5095020780690140701e601d1a8280001f01c0b443c0300036072060520f0008140581041411a0f228003140d006040703001a006002000c4002c4000d140c540c0c00104505550420b0005100000c0c0c83d85d98904100e240b0f40443c00f030021030812980200300c03042080107040e84e40c04841d84d40c071301020280421405440c1c40007400d00d01a40480b0b11903a031030b401030041c0d5524249c91100800c013602042c1c4d4083c0784540d248980072600c2003c0f402d01d420560044d911008001d08100001000400b195016418180e00700001da00c072045206201d00c54150064984d18080c8a0345c00400c81c1600959407442480e000f00655908003004001060140b4000141c01e501811080d0b004842c03244108002100c11004001c2c0884124040d0b1a9003014034001c00c070602c60740c81b15420740d8030540d8030840702400007881000c10300e0240314100040101500301428946048442c1c0101c1507184158100200702c180005c42c900544070381d0b1805a00001e050500701e0500e42803000080030328241040c005490b01140e072460f1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 308256025 1250 308254775 308254783
    0x7080304030b060d11030114010302100c02151810030603050618060402210105040c0f0e0906070806120106030f111212090a080609030a020601060f0203030c070f060203040f050601050102 82
    0x1403600221020b21984860040c007054005140084d5407450313178022848010b40d028042d030303a0b15079280c207400710140d4114010409246000d000e400180101030345001c0c01a203548210200030400b1020164817601020400c980350340400e8a0958070210316880907402a80651000c81078038001c0d000c40d1b02d9559074842808175001500449506a8030200c0007030010b1070701004d03d441207480347c00f04802680344218a40d0035104140c5041711500752040040c010340b202c0c1c1407408003c041c8106188000d00301100b02c1c58484c00c3c0030b40386004100080c40001e500342c803140d041083c0f0780524002000101c1d900e042880c09409070f08030840354820078000018452610007544401044030402502c0e511030410166461a44880300c0c051300004c001c070b00095004014031410344038075a0356007c0d41e85e6000030f100003400e083d0141c2041c1300b03100d40c444070442040d41c004143c81e44044012199580e803481800c02e44a40c0b0001c1100401882c0000100300400080e030fa06032909610031003c451040e41ca5100581c0c035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 308257275 1250 308256025 308256029
    0x20109152013030b0c0906032403150a05040203070b0c0c01090510050306010806010311070803060f03060907030b2802130806090a0b1f081e0a020f010c150e010603030207080304 78
    0xb00520b400040c00807400561001e40c0100800701080d182805160204540c0c0c0c104550100c001000601501100019982c8200c007085045002d40140841038110341c0300d1110140050b01416560340003d4119101000a2006049840350440d220010900c4069454009680160001e1042d00b0001944e08006030840500e0b525601d446048d99100703801142d03080030003803030181015120702646c202a009040107080d901c0c0540410f580d0303885c0030740510681501d0980301c0c9010341d0100040184681c0c001c100030003600e9100340055030a807691080e00d1000030520380c00b0009203101c04009400f034a02030340204410001d44140c1d603d801c5e03603010f02c0c42c1c50700310480303040d000754100002000000c0c1e001c001080c1c3c003010400d0082c0e1500c020340d4140c02d03000b80325000146503901050306580e802408004101c0c0c1012440d00502c0c0c0761b170192f03001c520540200c2804605100c0101440401c01c0ba03a122204000b0011080800c02810350020242c0600040e100a90140c060032a003c102036002004841c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 308258525 1250 308257275 308257297
    0x20f030108070b072003011b030c03060f08030f0a050702030105010608040201020c10021c0323040209250302030408070501140a060605030f130302033c0702031c0201091520 76
    0x8540002038016010403005c9865195140d581c0b00c14005018894050940c08081c1541d80010480c10119010b011205e058210030301c9280405410040304000100302c078819501c1d60540c5032140109002035455000b001b0009505500304400420251340c40050a8031440c001d900702e40c500d6031a0000d12040b030182049203001a0442281100101c0210804140002091070000741ea20b2902e4000003c084098605c458240340b030100b0f2005500c1c10034402500004d81c4880b51111110f5898410301812458030341105040d0080001070522900c2404e4403a5250484002d02050900c3c904020b24400100c40794540d10745042c0700818410310441c00d0728400c4041609010003038859905030307519031822172002c6003144030800803805e150011070183d015011800c0707107824041c40b41148906241c1044a1041e440e140c091050401680d0000742d41034085114108001800354202c804074050814414080c0503900000c1440c5403401c5141c0c4140c081c9a15465280b801c1c21090804240c1d901c11550703507030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 308259775 1250 308258525 308258543
    0x2070f0b0609190c0e03010f0509011b020c090c070b070801091107020114030a150f090f020a0c02013209090115021c03060f03030237080f070204020f030108070b07 72
    0x1848100755130b100301403480741e41c14040724a2003100002400c0d10b5608959040c15901e0f0300c00c0c400045002d00603140350454580c6403545232152000001e64a05c40b0000c5988038031714040100e017005040d9411124042d0300601962642d1a000720702070050003081c0300c0c01f0441032611420f401040c11080907101c425030f050303481c0d1020609003443c820cc640c00183c031030f002c4960381d100001d0ba61080c8030b46070001801c004c806402c40500d4803c1e20012102d01e214840410b41c01007240881207640710f1800d40e01260b09007415003450304900b0340c05001b10f0f0f803062800f009070140880e4410005181001e06030500c0129071074902d684e01e404242100b500103050b000c001d03070300c07039441403604a6036501c40c0c1003114694a40005c03010341c1c0d400906004d204a07403055000d6002442484020139003010310305581201030300021114985d4804822181c6070721000a8460103010500500d444592002c41d15903c0d0010401d54584071101c05a0b0710070343c000c1c03040c08000d126403940086c2001d0b4060580f03401c0d5070001a0b203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 308261025 1250 308259775 308259811
    0x90f080313240c06020f07051612230a020306010f0302090606040609030f080c0a0c03060e0c0f0103020c010e0615031605010c0b090c0d080a0f0203030103120e031002070f0b0609 78
    0x90b68000c0c0740501c104c8810781c0074842410301e2031603c800750001c1030048000f000d04540c010403440a181c00d0350000d15140b0303c0560b04902103401d44141030342c0a0003ca030703520800c02d000a20b460402d0f02c03440c8001c0d0306008400000a248a0b0a9105002d590080300c4500b2a51608001c021041c41103100b03142c003240010400300301080741c8801c40348410340505013880c40c05500d1026241400c0c4200811920300580c0441803060013120300c40c542e800140107000341060310300403000400903201c0003001d90405400042c410a01402074028485440b0144103c07919420203100a441006400390500d01a01c0f4032400d183c600800301c1c4482040300d8040c0c603030701a1060183c480610640c030080c444901446100003081c050744409000c201c0c064001e226072511000304200c01070500d10060003080c00c40d44148014001325400f0481159a0f200d503040c9030613020b0310180803074100619900c064103403901c082025014045d000758aa41c0140c8607604444050381c41d00208030031500c084d01e1141e503100d0420030f2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 308262275 1250 308261025 308261027
    0x50403020d0b04080c0106030c180e0726010203090a0201032702130209031506030d1106060631090605010302251e0f060506150a030c090f08031324 65
    0x40b19030400d002e000031038501003d400d0014291590341d070003140d8982420340c0c00c01c81d210f16280c02280705002000c0903c0004034021542d40d90b220f031405011484500901e540c09495200f1458185040b100d83c000c0d520707807501201c40c6031030303081e00d0505a01003410103c3c0c80764500c01c01564410b05070024088031107505400d40900c560150701c10310621806a00300f2180a01d0390741000403100450b5141819101d44c03500009142c100050042d4403014407070700c800400c2c4501808565140c4c40082951615115079010906a1910b09028440080d075030a98081e411070001000011017a01e29100d4248542660707803004500320b1240c003041112045030382000c5031000349030b1000c07411014000c60401c00c421a00e002e0361050300f880c8400440344202e2207603456040003620302419a00c000110344602e15010b00c00054803075803180004050030507660b00860019240203920110250081212030344e200da450f00040c7d55640c0c003441c02a0b002c0d205065000803114554564441407a20360b0080da1003481d22060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 308263525 1250 308262275 308262293
    0x1c0806031608070e0603121c0e030a0c0212190803010609081f0b031c11120405060318120301030b07020c03011a0f04110d02040501090e100527040c090606050403020d 73
    0x420180d25010b1130342c1d0541d80140303687c007a02d01210b200460b084404905401ca2089810040344064103800900a0000c05500301c0c0030642410b0301581e2590804084940c1c2900b401880c40c0364034110541c0c181002e0a02070624060741c1612803d49440e4103150312001e0007580e415001c03441048045140c400004c2c040310541010701c1c1d41901604903262200b680071f2391050201c01038080300c00140c0b00c0c180c907104190100100e00c4e4402d02e0140c00c038501170515010509510000301041d55000007016071410b13a180821800c40083c6e001c00d01140c40c3c0d41c4a00d040c070920b140c2510800c0051180004d1085146818428058a40d109a29a8022010049c14400817044070b0028542c1b141d0f480f00c00e190385012440003015000015140140e84508080000d09840416040146003e09a100b001419807001d128101900e0044400780b0706440210111b50259050f41441140d041230324051000b040325814001080e581c10003000c3c0111915040c4c115028002d42c030020b0b5000b1404c04050010508090f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 308264775 1250 308263525 308263531
    0x3090a12050c0706081f05063403120b0102150a0c0e09011409090d05070f02060403080a090323030403120309051e010f0908090f031c0806031608070e 66
    0x41402400c00d508110b560381041c4440e8041004035443c00200100f046034802250b041e08424034883c540d80d418880400c03a180544c64216421b150030402151102c0310100d4202c80e06520b0712009503d032105440c0040c211845481403450160800d04440025800030490301d944c00b0740f04035000c0c0517070348030a2108086e024800c105001c2c403d41c803400402d15100d900c101341c007074111080c2100f0301640c0041031041801c001010342182d5003041a810aa1070303440740c11103c1301900980d81c10b194240c04e0000405034072035a4001803403001c000861901c0113402c400403404076806460388070340864130400d101801341007842640c107031034008100901c0041d45449145082030309503c0c000424009641c4d900d4a86185403241c90340703440407405441c107006001d0140c40b03c039000074101442602816034554a9502030b803000340340300b442500000884d984081001917444402c5040300d134010182180041d0040c1403d8a51500a01908c804108a0790407455840116601c1ca0020040720307152038002e0719481005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 308266025 1250 308264775 308264777
    0x8091801050f0d0c050d030801050a060f050415050904061404110307020d0c05120c06041203061a181f020c0402090a05090c0c1515030a0816020406090f021b0303090a12 74
    0x4042c0105464880c0c40444c0035041c408d4507501c0c01541007004100142c1440e034000c6041054201c0c1600380310341d21009450485900280c1203a02c0c08001f002500d05014036136420b5086840c1074400201c92560740c02074002ca0310191410402c0140c1c1e84030002c00d43c4402c503100360242c0d00040c1294007080c8944503800100f806102581e8400340c880e4030701c0031140d00c8442240c002c0d91001043c0018081c40501d240080750450038104030341f501c0c145120040e04030300300c10400c001070b0119130741d59400c81d00c2c041c0c1c4400d03040041013500007084102114003454004030400c0c006114800c2c001e4200e081510071107070100d000400b00f903840d83c5440100b100c0003c00804420341050240030783c1031221810454540101501020039490740780400403020380d0800c0d00c115620990188803030b040070444a034115810315015850b418101d001500101d030140866030b02107e030742458000c02c41c0c88808554040d181d0b00d010b4000b001540c81c00007100555134001920048050b070040743d80f6a00189960420847c0d046003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 308267275 1250 308266025 308266043
    0x4020604060e03010213090b01021b0d140c03060a06060210150509060604090e030304120f1211040302031f15080d030209181021032003041208091801050f0d 69
    0x2203018081419000387d0020003590f40300c400390741c401c0d070301030101d6084a02426a0710005262240000b04601d08100c400b9140202c100d981d42c1d00d0350001c0c0712417002200003030708448c007070705056441d18000c01180c41001c005029500c0950350060342e0303000d00f03c0404c4140380c219000f103003080100440c07614003510695011200f0030000544100d1405600344c0782140c03001440d160328090030446004040c0390810410064443c884400854003c1102c44840c0d10041c40007a1824244e40707440f8462240c4d030400703507041c800c900c140d103800a025403c00c07100031444001401900c1c0019001000088540952080380e002000040d82c018880d9000c4c140403203004140c040c1624000000ca0002c400503500000d0181450000380011940c1c100b400782400305c100d60108041c4412748009083c0074290503160620306c02c03a41e00400c40c0b202041610003a00101700920a0f1051902c1d080360190311066155000c0c0c442513807c182c03404481d601c000e0407204041c0c0b00b4000b000c504410000b000c1034040084a500b42 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 308268525 1250 308267275 308267287
    0x207020a0905010f0603020309030a1101110f03040c12021809070e04051501050603091b03030f03010f08060a3e04060207030506060f1005032a040303030e0604020604060e030102 78
    0x3540d00844002412026400100d55040105000d032440d480d4200b41c1c1414010002c1c0900180004103e45a4048a2401c20a260381c0d2481160151280e417040c3c507144030001c51140e1561aa810045018a20403101a080e150b658044469041031000010b0740c400d2145e151450f06142002c6610b074000c00d003805075030140c0d445090112401006a0702580c20780d00400003c990701c0b5021509a000d070100302c80c4c2c2811440c00820941d512041c0aa64032226010441070301c1d856141001560b000d40218103a0640740d40e12a2403c2182e60524801d02c22035214070740101e00c5030f842920485003040d0001e50070000500c0380d032903540c010010b0615041c1c80115a03110114500001e40d01904c043c2c00c2c20ba003d810041c4c6941065803404002804c520712880e00c640d58650259508020001c2c030100c9414465125079a8043da090407009040c48281450040d07801001d0701c801400041094038801e031000c11440c1c800e0341384681c0c5d60340c003118000c0d00714000b0030003030110701c0c00390080c4601000c0c020000340c0b81c48 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 308269775 1250 308268525 308268529
    0x402030a2c0c01050d111b0607032c0102090909010b09010b040608010e070c060c0503100b030609180f150403111f0b0406271b0f0804080d14010f1a030c0d020702 71
    0x94458028000c44400c0341a404520040a200007500242c0314900be105a4480035800c246c040e603d941c2542d5145682c40c0700040805c1d080d01034400d541d0008115107801d00d40140518080d2038000e80741c80c0310301510000410008509420784090b01c404d50307101d503507907030031b08116144810016080350103210386403d000340002c48078010010003000640d1025141e08000848041400d8a60882605048148204101c0d516031030f215580c4503500100c81100f01034180001404c2c10210740554002e8002c5000c410a10300340c14901c0c1d401503101e5074032a08980e048a034102c0d06c81c0008800c643d00b140c050540b060300030000340c200164181c0000c000181c2c190744c504e03881721304443d1785596140b44500300c0c4a80c02184a01c2c899500101c2080410342c0360b07001c44a50040c20758030070410310014400004082030512003030009030745051000042c1040403480c0c3c107410b010b03808804d119140440100e00d00116111030000c10603007861588140407411500c0e48250380074a80c001030b0031181115030901864000d0307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 308271025 1250 308269775 308269777
    0x303060103091a04150501090903120f2c060601081e0c0c010c0206011a211003240e0d200a0b07090303030b030715110c0402030a2c0c01050d11 63
    0x40e0702c1084562907a0170f80301111003c2c2c2c0e6050b03004002c1c82d843c0940c01e001180d0040341c5403403a000c00d1500015a11304440322030000701300079820490200d10fa50030710b02101c11030b1101541524840360848002da6112070045889400071140f0910b40b0b00e521502906101242140c50b4000c0d21034044036090940c082e01c3c650850304030600c180d006078001c0004002010b1219003008403103141685003850400040231100580000c1d106548442c0b80303020000701c0d42e06580005078041c1d60300102200c003400f12030700c404044507111284945a40d103490118944050002007241c900340380c80e1903022000703101d0301c058070101c100d6000c00b0720140600030007000000d070381d0900f00340700366601e807030381c4501034203600b40102112120305110703029a1005805200551004003c001c240243c0d10301001d0170500414982d091580c0b601705107030014000b01c1403000d008030719080203060041026010001145a00c030400f6513492100c1010b04075004900d400403d540302d10001c011880d0b1910012030b030588018412903079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 308272275 1250 308271025 308271031
    0x4030c08130e1303050715090f060c0f1706061b06090106080637020d0c120b0301060b04060c02120d0c0308071806030234021206090303060103091a 65
    0x2001503100703040c00314072030042005400c2405889090840107495401400e240b0a0180213015408400900040707009103801079140b581e4001c0076418042500e00e0408080c1950380d40d1a400b03d010854a1070080e8403c002d040c030112030700d9410700091303110802804425845214510150b6461100c0904441c400300f007010301591000f800080c80320319203c1e2603414001c01408405594040d07142074207500c00035501203815540720b000540c882c1c100c8954443c1c003c0c405c80501d1000039007420312200d00513810480300d0074003400405060041c0200720041500725074081c0255064040f0500007400b4184c86098450070862001d060322409065004030b851421a14000180000f80502c0300030080650000007960401c51505100d0800420407041c20820100343c001c420816030301040344503041d40013034100b005030003c1c6030107500e001d5007500310074148040f803c0e4160700604504e036a0301800003000030074520611010300554150f803641030046010b00308004043d10208806d0000d040226103140d120f0b40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 308273381 1106 308272275 308272297
    0x2010606050708220905070f180515030601051204200913030e041508011d0a080304030c05101a040507030507051e0c1e01060801050103081204030c08 66
    0x20000e032950380b011950130f080c40240300c50303c8c0c2c010400403420085a91003100b82039124031401284a40c621038140c04c19071460200d119000f0000c0595049003051400e01d10305418a19110b03135008060f10107580d000c0d2400c03890303080c5106001204000140c01ea40e158800d103017007855100340c40d600a0000d0f00f800010307482c642d5240e079964819015924000440224243c650600034000c00807051013498040004161107101d000003d4003002d5070343c3c8550720918569513680c040701c610a151808503a0381c03040305075030106148503000308011007081187c0019081000000c11081e110040d0012007030514100a100906034081d08542e2001d11111500c003021102c5d0082c5912845849100b4401e4003402404038910308004644281000360580240503407915903610500f03e070307000c1c800142114030400c0b4242d1176080d030706102a8058003a0a010440005e55103440f00c2c2507202c0e0140417 = true := by decide +kernel

theorem cover : BRFrame.Cov 308093525 308273381 := by
  have h0 := BRFrame.cov_init 308093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 308093525 ≤ n) (h2 : n < 308273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
