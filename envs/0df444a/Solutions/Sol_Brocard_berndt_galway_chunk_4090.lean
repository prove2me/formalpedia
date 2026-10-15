-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4090
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:32:40.75944+00:00
-- url     : https://prove2.me/submissions/dc1721c4-b7c9-4fd5-8ce3-91f685730604

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 735431654 ≤ n < 735611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 735432904 1250 735431654 735431681
    0xa050c01020703150f0f230906060a0506071a16200607050a0207050d0b090d0503090601050f0319120207060c23070b07061a0d030e04020a110604080706110a12 70
    0x41e0f51106428100c7e1040300c2c0d160322454010000101c02562143c004100540545d40300d802000503c407a41d507500c1000303000c5420030740c0c401b03444007194107240f24140c810300319100c49031600f6800c00040000144c110b01040b503042e264003411044400141d112400d00f1169010ba55110901140486018002414200035a44116040c958440b804a91044881704044406002800c140a00103009100303201c5803100f6442c045045141010285541d8003040c400c1c0d42c0201107200d04501c031900e061114002202e0300d2800c03d8000d0050340f0b811030160000000e800018001d8000101c0c00c1d600c00c80f038000740030781c11a051481c00441c042c000309243c1e050032000506440748400000d404495400a031a64500448001803036400d100396803000404d082c44064030450b80440041c0010780c02c0703150000303408403d0f140103031a921814001c3d03a1054050240c55064030403502003000300200d4034001c2598a10844040c054070b09404030000081c06030312046000304d0981007200045101c0341d4489450b16198 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 735434154 1250 735432904 735432911
    0xc0313260f030f0106021207020d290f090f07090c050c1f151d070324150c0317070c0b090a02040b030c0a0b0d02070804080a050c01020703150f 63
    0x88109901035580107140001e840c00011082000c15003501207103500526007400640503da8481c90810694490481d000344100b412020284c14032000440501c0a1038110204104621110301c400546240c12104030452120010025a001348086412100c41c070a00c00203010072428045e5910140c1004070080040110611200c440c20504103c0c0c41c44402015070242c001f0360f41e003004442511010341400d00140c1c03052004001d032092041c074080940d031160b40000e4117600ca180085002e00344200000103441204140841c0007421500901d08a83d00c0d00b030140034441c002c10060720603800113400900814924685088040072405485a21141c14902040481525941c54540744c2c01520f030011a94449a050021800c0c039100d04881150118002c0a07030010b03580020f6030b40c2000c0c4c01410458400402c00c10070404090301503c44181d4001c040c5a1195110701da0300303549010003001580c1c0c0744112142c031541940041a030006a030b80007440043c08031040002c06010b81540e0600c0f00b0f42a0780c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 735435404 1250 735434154 735434213
    0x50316052101181e0f0602030a0f020d0b0103050f011508070c15060501080603070311040f091203020a090b0909010b16060c0e12011103180307050303070c06050c0313 73
    0x34288540901c03d801104501404000c03401c01c1c0c549150301c640f8680003481c00090507404121050000c80032a58401c501607a2170b0fa88001c203001070205080c290102030700104801604441c5034106189240007aa4104255614000074841c0200300307120301803106e14207484600030640301c0c0004a903c04506d0500c40003205640d80c41603402003003101c0d1150300a40c0c4903424021036a2094460760007150441c02820034a045854820f140a0f07004403241c8507907901c0038107424081440e0030924001e80c00c001c07207002d0103481c004050007a6008a08040018646600100c0c03400500300641d28405000743c07500b0381682c00e003040d610082d800441d2402d403107100c0c9001d04000800d2405148040320b0156210706c40c1424900c24440d60001151054030755904008003449404035903826aa40688100c10060400c100e0350071b40382c1903203d000406495800300004000c032407278100509400c13040c4941ca040005a03030302c0c18100a9400240da03500d00c5a15200079080105110000d08011094458a00042ca01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 735436654 1250 735435404 735435469
    0x1205071b08030d0b060c0c101103030906060f0a08121b0105040f030e10170a0204150f021c0e040f0b031510050a05010c030311090d0809040605031605 66
    0x10980d40700da5001d5000040e0b40c04001018081c4458418055a00f0b07410f0001601c8150345400c4000c008a028101c0a600710610511841d404e501402482050700c0d40c1c1c0c100030300c0554641004594060091806805100c40da0604801410407030b402d00c8040d007054019003c841645a0200d000c90803044940c10900300c49030b90a01c82da80c001da1003250800001115450301901c000d224480744da02c50b1007080046003000e90400e4081c11001f1400c442e990107580c642080c18024052a0401d0001002081400d90856000f080081140555400b01c0d0752900145c1c440096100e14290010002406100303401082c0c2011742082d0a08000400080360000380d82d00440c0c40c01540c442e04c0511038011400744141101c0c50040030300076010a451aa0380d8031f08000c0060510f5204104c000d04059485003100340002c0010141c41805800510b0703404039070914145032140d0303000314100f01d1296207805000115071500003148419000300100e002d42035403030901003043c0e5580344c00e000072002134040c80210460 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 735437904 1250 735436654 735436703
    0xb15060a0c0614090c0d080c060711071a160f0b0903072108040f080408150405010c0207080715050d0606090312090315050603150109020a1803120507 66
    0x40d1595504000c0700180d09100d000e94005541405100b1401c10900545003408a408049400c080c5c402c140850f01902d4201d00f41d10603421000d150380034010600c00300c0c3d1b41c003240141d0b58004c54422503400544413011040e03600a01b100340242414100004c001071495455140d001038090000500e01c2c61454449020040c400c450201040d040016400308200400c1d24140c690038603985412000c400b44040034080710809000074210380402d07c803450402a160003190b000e0b01503802a282120020003415041e0801924111015420b180d0380c042c41360710001e01c69080707a0043d00149241403400074804032403003071481d11204002003048083d403d44860300805c1c006107029954115168550300340b4200800c6000e0507001041091601040425081d94002400341d590590001e101d442d08400246000751a030602c0149101c05800080c01a015501500118610707880d03a580080354000c1207035401c0b6490000070040c0f26000c1c080b44226100700042c0064a22807400c8070013000c0c4003030f80403011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 735439154 1250 735437904 735437917
    0x40e180c090402190308041e030506060103022208011d011406010513080714011e0903032001050f090d03060e0a05091204091b050a05120a02160c0f0509130b1506 71
    0x68042c005000c02882023200541c00d81e4007a0004040807c45c19940c42c6526140e020b000103040540109401100311041c1c90150a412180e02c009407106550b10f010901a16460326101500780d0752a403d2600d03901c2c180594000d510709060750003042d0383c68000640303085e0084503541c28500e600400c0440c602408000380030260941ea8103038032815500340d00051001c08040342083c00200c2c501005480e0310303003003040c48050729407500701380845069400c0714039507090700d61000340965800c0100f80920004070155440c01042c01030203035100110740000603001c3d01c84510407007440e000c80b000003840d07201c42603001031340080f020010360b202d850341c09803903880c2a0401e030008030f401e690b40c461000810320170a48510f1883c0341d50502c1401c0081e0500e003d00240510060010100c000c080092210b111300c0c0e0440342851300a01031044060741d241480044000d0303034043d6400d00410500c02007614901648034034400c82e2025001e1008030115690010340d000b01601c042c605031401005001e540e503400c0c0c0036121 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 735440404 1250 735439154 735439163
    0x61a1c1106181c033203010e04030306050f010504051219080417060f0a090c030602030114150306100c1410050a05150a230d08040e180c0904021903 65
    0x44611104109141000d0000d031440a000c0c08030180003c0d1704040312400c04141c450180c44440d842c0c464900b03c244031490483c41403100000040781e001d143c007041d5030007039001c2d0b502000820b44403c1131002013006429410302081c0e00380001c01c600d1401014250410f00e41400f501d800ba480308140881c940e82e40502102d188002240c1440b49550510701d4060580988000340003e04028083c418441c401815034030074142ca81072500180812080414020340d07001d0401c640e250381d1205000c6500144800161054038001100c1c6a0701c404130f000e8a0198100600b41200317021441010359903445100307422500164081c1440107141d00500174400262000070021989140035180d1104541004004804c0001c2c6540d004800381c986001080542d6483c00d4030301003100490400c1d41e011054440810382c028a5040c202c41045a0341c3701a0080f10041400030742580c0340c00c0c1c0320117240140c2c1a81900d096201304070f2000386142a1100540103400600002e003000484c80c0301c004000c500e50030a54 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 735441654 1250 735440404 735440437
    0xe030d022101080114070804120e04140903040f092310080303090c0913050c12070509010311011803150f0e0102030711160617100b0c0a061a1c1106 65
    0xa10380485c0510566100e4040e00d0100154038259580075004002c205000c1c08102e80c5100c42170960b1566442004181d42ca15241011864140c0e402941c0c4d900038001d075074440f0740703900c0000b4240030240038040d041ea184011010075400e680c001c0328030a00f401415441c00300f071600000a01c10038140002d600405403000940480c0c0c002c2418007440820250403410b80a0118030184049000070912000c0701802300d0b40c0012032820307031244628282864106561001a074400001007154074414030402d4002a2240800801c90560000c4100d045120140c14550043c004018050039503010030300a0801c4000090b4841490403c2400c9070000c540c40800300b245410312106000042050198420826084910703803070420038000d00c00c4400302d1035001e1000c806008150421811128500a800301d203507019103c45800c0003007551010454010303a4002c1c076198461100c0d0620354403001191001400010300d210850ba0301c00310044035034200341d0304681c20036500c03121f9596400051491050326081c18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 735442904 1250 735441654 735441671
    0x16110c0d1a0c040e060a143a060e150109020c160608091209010c0602031b070c09050106030203070c120e040e030403030e033004050603100e0a0e030d0221010801 71
    0x400210380007801c5240300e50210b0004010300d5681f424840310041080c1c43c0e01c00c030f002003481040365440000c00e40c00401d064510411611641507030111006034000c1c04148189001084000c0e01c940c0d0051005803103d980314018402c002760f40e00107001c0e0460b1f107000c40700e1070001c14205007070180d83e541042c8005079040d014000a2441040368282007a8065081c91070a014440041c0681c40001c2000b800c154022002a840d25140f41c51240040481c05a4a0740c07980340d458006180f4040d0b0081146962a041c0081043e0b0302c41d10a407440340415449540002030b4680f80d0002a10410018000f000460007800c00b040e01e407400358000107220b400c011504c0b91f041d407401405030b042c0320340118000c1d4820016404440003c0100c0009040c8201160a0307845ca42894801c4600ca9900a1a00034000005000c2c5910504500008a034940c0c000d14141d43c5803004800240e034024950070100e039000380464441001250300400d0003505650302c01042c0408001c5120090320240e0011100741d5440c5040d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 735444154 1250 735442904 735442919
    0x1e0908010507080a0e010e030d0e010905011b17070c0311010b10110c03010207020a09050606070b0c0301030209090a0b07030b0118080a030905150406080c09030f0616110c0d1a0c04 79
    0x200c01084030300c5c1e0000c0c4991142c1c020a141da034003d540704c1d204444d0f220030142418034000e5004803c615000402030051043c821503a841d84112802030100048444a03102d46040400300301a01851301070340c64214118090703c007110348010f001c0400403039560703178140c0c0c8030b40c1c1d42e804082e0064516642c0390b065806c0402315806041000071481d660080e40100301d24070050341c5005244040c0c51400c5000100c98548038081101801410002000c45150300280034a040112000d18100c0b13100302c400308400e0341c4103c00b60340c49115100c401400c1d00f00c15004030388040d000b5084075150740d0040c90302c00041380c121020300402c44d0480d0710503449508000c1c14401416401000f50016010a4070b132090f0742d4a50341100d091912961084804120800c030204070121b00c802e0440d514240000c0c100c0321581c0b2249191034640c1002c1c0c070908181d20800c00c0307801c0f615009280000c02e0314041030140000103445014001071100740c0400700d4419117064184030084409408440c000c030f041c150b10720b4545081084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 735445404 1250 735444154 735444161
    0x91903020120060402061b03070c0e01060e030c09060f060d0f0c140a0e0303041a0d0e06150d150608060702070603020412120e1c170306011e0908010507080a 69
    0x281c8214101d82e1105010b107200080090304668169061551449070101501604120001035916400001800011721000c0d40518059480441881d086a40d0341c0307409482c09070300103540e10740503005801c054055203018100d06a110001071300d0000203440c6040000c4083d1300c068800b05001356140c0815030450078500c10500d1103d0f2904007940c0071051000a003030b09000e0120500100400d400c0340f2285a2810301c1960300500d0b01c0411440000402c40b100c0c01035403c410180440d051a00070080b02c0c407080007441c0d50280401c0440d180900c5881c00500107110710a01c010343d117550307400000c0204201c40c2d00c9044000c2011001804803070405102c000e080c00641ea204a082500600c01805403c04920500d088203600034201c140b50007200b40261089071015204a0f07201243c0030309407a1014a401e03812412a108143c13840c00300311008040030450209565042c000307120349080150f165003510403000d411020741010000c607946d0f20302003802d44200301c0b600c90014580d101072100003100c501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 735446654 1250 735445404 735445427
    0x161e03030f090308010e09121902060a150b13120606030b1e0118380612040204180c0306060e0c18011404032f0306011d0c0919030201 59
    0x200140440b030b5241e2002042030a060240d00c03811003182001c82d06805007004881e00f48a0031101e0309890380c1c2d5a40301c140329001000c003564050f0107070100040844a2074841c1d40400391a1104a01c0700c0c0b070520002c40c0346170708140e0684009155a0001003042c490300d00340c0d600d002d4420080803d880c0e0451821030b9541724084d0a4841441c8040c0f40f1154a8038443e81e803c1c15160841c04a50040aa0403203000107483c000c48850002e22100d41d698040040300c0111402e04900c01d6100b0400000c01414004103114401c2910700c1c0030030000100c2c0c01882c06410084a03030001500380a0110f00a445160f484000c5034004c40c1c805a82c2c000420501800034040356014510704109421f00c04043d411040603441103400d181000031140e0500344a500c07001c141c6014541205180d0100c61a040c250048030781d41c00910700c06081000b40790b550030701d00018802d0680391145c07c10390550241d0f001c003145049016154020802040c010400a610303040d50503451900c001c601d100e81e07685540009080c40c245070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 735447904 1250 735446654 735446681
    0xa090204050f18130c050d1407081f0c0e090c0a0306150c02120304090e07170102071e020a05060703080601080703150e190e070f0506041a161e0303 65
    0x440c601101c4006114074254014004078400c0d20740115460174820070503c980209910144c08012507040c040c0700c80c40c5110424120045510240c1c0b910b001542c0d0341c1c028110f21060650340301084802110315000704407901c9150030b1078000070603a40000785024400b2a901030204d00b02103412444130354180203100080c1414030400310941c4100700000c28518070004064041e481810000d040d1000030003c41c0e0040200c2041080000c0412071069100c000d82d106001c0e500c0101d5421420702d0703c040c42150700495004020a802c0a0b0550401601e00c10600040c1c2c1e0041500200043c0d644488004141c964441d42d1103030441d1800b1800501181400381001c030825150001c2003196a5a141d101001e480c0d440310010416921100d40002c45600703400030003103546c140088055409c000194400076115001c4141030450784581c00e00005004a2190b610a40444501e2400d0030f05040001c0208050003550103c201c1980c0c0c94101482424250b14042c45400940800038541e140c41040c1080c0c048 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 735449154 1250 735447904 735447919
    0x10e030705060f04080f0903070302060c07080c100c031b1232030106030902060702030d02061b0a051c140408130e040515060a090c05070b010905070c150b0a090204050f 74
    0x2a440b4480c3e17a026807010310381c807030b10b00060f082e0555904100310300c0150340c010a10303070303940c0250f8400648400d80c1b4401c0b22120703c9004084002c916009031120740400c02c075078400042c00040d44048407440c3c060381002082d51403030400303500030420380b12070070940500b142c96400d0440320039036100400c214240781c802644da9a01c1e01c194200030188003182e04491407890f010801048500009109214590700207615200380404007600e19000314003a4070404d5001704101c1070300c0c00b030b120900d8a407243c00021800214100103000c20f40415190049412030704560016035100038400b000e440c103d041d202a1045c4001164111804a1803003658024200d00d099241c1381d404c06554103542c0b00b04101c1e0807600d041c504000107d580e141c3c3c201076001000d50007401d002000172100081e0266000e0081920f88800c200c001041082242c0900e9014003e5982c49180d000210740b9a1003001484c0343d80451b0030794031a516681150380381c3d0506005809000340041e525840e00c000c01c8610302c01c0030342581c0100380 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 735450404 1250 735449154 735449161
    0x1801030503070c090216110613080d0e0d03020a260a1206051c020409080f0d061508130f0303021c050901060e160806040b0a080a060e0615150c010e030705060f 70
    0xf42441c0321b5610390300c41c0074000c0c0d0701c4050001074980c5c020b00903545030080030004001200c1000081c1c0f81040d1a03180c440030a11000310341030020301c0300031380c0000d005640941880e00001d06084821005081003411210303034040d41d5905800c966001200d81400070700d0a82001c15031001521403000140b40444208034070126070300051004180800001c0c0c031840e076801105050000400c00c40c0c4c4101b0742d07184001da95201c03044907000104900e01810020445c46520005d15501500d0300c6400307840c2e00c1d80280300311241680e411316403075003040c400c030b0030190240143d22041c400545030828060f64480003107558905a0400e0382181e800b50300843c0358220203030601018401040d8010a5030b409840d108042d80e0b102c0b408a0043c05400300b405070406590380d00001c100c7c070082010507186108540c1440b4600c6001e410f19500d2400f99502440074007403000401583c900110822000ca6101c0c6403107041c015800c00b96401c482c445400e88106410014241007002020320915600c00b8005001042908 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 735451654 1250 735450404 735450427
    0x1050307050d1106130f0f0b04360507020a0201020616050f030a020f03011508180c04020a110724050a0206150303190e03010b04110304060504021801030503070c0902 73
    0x241e840050548421200071003c1900c07030004513800c10f01603120409440b40e8800000c0505100383c8038003e652284031001084010034201141c045580102c11035080d04003100f40c1111440111005100201005410503a01c0342c0c1da000300c030320071b40d095005040783c403416000182c14118010f00301c0710003090248101050301d401009450180747e40e072019039102d0396000d507860020707c240311b00094500340202c00082c40e00303514100341540c07842d60350710042c854a036286071941e050207040c524074803900705584140c01ca00b4150b014203000ca990f840c11b01d00700350b000c0039014204542c07500300201170020030011244460700070140090343c0e0031501c2c001d4900416250300a4581e40c01426002c0400b0702c1000291460f03508000b51480d0301d41ca40304507a2014a481006007000c000c00f1a00c40c003e500f48500b900f15481d286c03140c3c0e4186c4418180880c910780d60350b0740341802814000d004070381c040600b91055410b00c068441d00f40c003861081005507a138222a003000b040081c80c9600c5514014010041c080f5002d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 735452904 1250 735451654 735451669
    0x18040e0309040609060528090902010207080106090f0c020a0b06010503100e040506271c0c1209062606060d02120408030a060905060609130b060f04180603031d0312070b0406050105030705 82
    0x48e101c400c800201600d031440100d003002c034541c2c082c058a41c20103c012410203055446101010f10380c403c01c0003105510341040c0d8581d10607100c09800081a100041c0d29540130b40e0003541d104818030b004071421a00c0b0501002011001d85003a100c69005400300103500a401300103c0c90002c4d0a1020b0110302202c0d0000d603510a10092031043c801106021220610b0103400d4a90900c0e03800b1480d241d6801214100414420031845400b0000e180e88402c2e5401c0c000b00010403440e400c007a00e130501980d88090034480180d1010303c0ca001d64940c20041c40c0f244d0001010364a0203a40300e0100c09550341803035480201613403816005103c100f8900010f210f010b0b90780300f0880d0482d9409480140c00760003182484001040740841481d000540042c580d0a1002c0743c10003001074410794803000700480754440c40c00b004c0b10b03118040280460b4812812217071014442c0c801c4180d40000604440032410043c0300540c243e000410125070004454051104001c10340c01503502500043d001480018501400100003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 735454154 1250 735452904 735452909
    0xa0e06031903050f0a021501090e1203040f05060103030914180403120603051c1e0c020112020d020a0903020f0306072c0904050610090218040e0309040609060528 71
    0x340328000e0507010540600c1c140c071241860070340c540b5190714080c4c0707020351140c000e4002c914038445d42c50004503d418041c49441102c2254000030000415a020410030326440a8001c3e00d00b248284507040000d6010040203000e98030030381d05d080c1024600510842c00101c1e2850041c42101c894011030a484108c2e89aa0703401509172a05003001e50b58004210014249070708050722501455a0440084e00c01d00302c100c6901c80a541c030180c0c0000c960303c84840040c8210a0a00040c64054a82002d988600e200c80eaa00841410042ca03002c04c2e00300e890704980c00380c0700200104040a00c2041907140420035410303014402c0e4082c00c568030b400180200b418141703801c4212401d54544a500783c6141c0309102c070070b03c9400600303a15460301382410f01e140c0e01d0344111088a0000d00120000c20f96445a00a1700c0c0d614400500408180e8200e41c1040003926200303070307052141c0c40140480c08281e0344500a11000300f01015001030f60500301820300c11004001108007071600541e0094068940d2100c012004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 735455404 1250 735454154 735454183
    0x100f090905060c0706150306020c0d08060d2603090706030606021606050319050f061c1101051b2509020a0806150702061308190b04061d010c0203090a0e0603 69
    0x10b84d03c4c46858080020100303408240c680d903441c00404010442c40c7da008040e1140702c04d041b00e42e41c44a10008403043d030001c4a040d038200c0c00101c83d050010300d1000030200c018088540d20003000c0c2042202d0203058000315512015944022004c0110039014400c000180c0301603c068540003000d9820034014043d180304080420100100181441c1074902050810360403049040c031040c101502e0440025906450043c4642c200c9494048500740c50880d040704203500013000d082082400340150740a0308400760b141c1c07642c2100000d10034070110274000c0c900c01044014940362090f4140756500c0c20404150840340b101881041072102164000f1505544000120348200c80c03e081d42d22035540c54001c8400007908484040b9402c0c00581011110100b5164034100316040764030b801e2080154480c2e160000740040d526400800c010640e15000b5008200c8440702c10480d10480004260840b1919103412005800c0411045100e10b44201808010702c6070620344103007824101c0000707490f900140358524 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 735456654 1250 735455404 735455407
    0x12061015170a020c03040303080109060510080f0919050a0614070c02040207020a0306060e1603021215010207080304060f020f0105100509090a08030f04152a05040e100f090905060c 79
    0x200000c41c103404913886031304280c0aaa4507540d50b440c01404041e002e005801025060840226071810a048030356403035020303991800e27100e0700c1c0c500021100550291200d0701382d015184c50512600c8440034040d10007880b071801020158010304200c401c540c10750100b084000c07101e0051041030399006200e6020705404890050361880c07203100007050b16945500090102d42030800c0041c2010030112041d100d400d201c440303409407000700b50301203040380b140b20385406e520804540810400181a050081d00e41d2060048514007600d54803858915002a03202d400041d288850284080b03134140500100005c40f00000d00c051b0a082c01c407070b082e07015540a000e000c0c030784c2e10000a050050403c1210500740d080819079540c1c1c240225075110396003084505440307902050402c909219500d1003454000240c0800c1444101c80090500440300300c2045010108a824040454400d00348025140200701918a0001c518680141103400d8001588807950051406003014003107034010400c268050540c04c00207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 735457904 1250 735456654 735456661
    0xa08061002071a071506180908030a09050312251e05030903160c06030b09040b011413050a021b0307150b12010e010e010b240304020d021206101517 65
    0x403c55400b40010180507001000110403440155a128000b919800d48078100f4940c3c50381c0071403042d52200d080080502d0b0040000561015440d80680102803241e0142e900d0310b12111141c20040c1820340c1c0c1840e407000641c1c44881000101e00081003000804d050001c0881e1062444242402c07a01156000b1b0040000016a02d071324203004a0303410074520700180400079810f08203484914618000c4801007071428030201c040b450010207440c41251f001680d009280c0c02c02c41410414007144420030b41091900040d42c00c070402c02d002d41d9100b000300640c016168403039044482844100c0850845da1500200311038004945150042c0344003100c60340c8046403000f00f1801080c04040304d461a81495440e1544200c450601034100c02c00f0781c00c1c0b220007401015052020000080340881206000c10605506280140c4204000e154030600007460100703c400e494010680490214103800b9964000798104410f41800903c0342016020b9880e01010094071940b000c2c12401006804805500100707001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 735459154 1250 735457904 735457949
    0x5040207030e190603061d06010c0201030f09140606150315010e090c0c0f0102030c090405191503050d020307081803161805180a02100e0301020a050a0806100207 71
    0x10b901403444003074940a04943c4002401c15080d00500035640000e0919900141c0d4484400381001c061000d0500c100d243c0e1a06801034901d1241c0308030481c18962600c05050008000c0d2003038040407406008030100c207020280c210b03410300500400c03082c4140c0305142c03c2d0442c0340c11340702502e83c060003069210b074000c410f540040e5881c4000c0039a00342e0004128082014543c0f40c07030050206201e2807021195403502e1252005d00b41d004c1252900308400c1c0c1400303208080d00d020381045070429100480e202d00c0951813007c2a042d01d140301c68408190b14184020020000300300003401035142144041d40c10500655078480c0680b280341c0910b40d54078103192000c1035a40d01841008149490603141140325540d030750441c1d4200c845d260f40303081d1461405001666542000d03e8100c00312a001c5d002d00b00c41c000350780c00c0040d03604c1e000040320308114584d0410f030301e5034800344002c1074641d815840707003134984000c0d0382d0092078940d00a010301e000c2c04071020003041c0c243c0c0000710700065071020155a580300c0e44012030f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 735460404 1250 735459154 735459167
    0x20c0f0f060c0318010903050c0c0906060a0507170705160e0c0301030609030e2e02031606050c0d020d290a061b050601090c08090d0219020a15020106090b0d0506010504020703 77
    0x205504ca51812091a00300b58100008100c42184801917a04200c240810171603205070444449421460800c8200c0e4018403510051441c603224060703a012246244070b40030040d8100081c00c9030183d1101104034441c5a8800644000b40311104402c1c00d245400055070103140810300c0010041d68940701240b0801d030041512940c8248060803a4021075203d24500e40801a0700381080140040c0305502c0301c00503c040b04071100030709003e9600745104e00c5582e031100203250091410b0401b030750500070740c0c000d40702e540001e184181d0303034030404540c1c5445848240040c03d4040b01100300007691056980b52612151003800031070300e013400d001c0e10104603a108825000350604004145010384400411224882d90140105c0ca83d00ea403003021641c1ca00145507a2241c4900c4180c001d85c0c814040d9038048560682001c00c2c440c8050011101c5583c0e030055903111000903840c0c030300981d4640364240701145640c441c0e02000c9130112010000c005541d2111034488070103000c4c40740a190000313100810326000701d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 735461654 1250 735460404 735460441
    0x60309060b101d040c020624060f071a0115081f030c090b090915101214010f0c050702092e0e090606150a021f020c0f0f060c03 56
    0x18454501400103a00083c12260307204403607840014101080000d0b42882e02c52034114480d1500200740d107440e05e0800070601d00d800c504406100b49401c41001044c4c4540f00504040313803456626688421041c50b00314082100d05a010464000b8040108040c2035100c1d0000907080071810b0100f2144c485c14241030705c900c0310000d009040c0c09040d000004018015550000725420180c00700700d40f00c4035400700300c007442d000e945000c0079610034441a80c28548100300305401c00f280d01c0c44614502d6449400e0854903907800b0003550142002c040c15032061100780602100e2642852080100300303100c40e4050300a0041d090041d004046100002e403450705050310180f10301085400025003c441d401c02030b20038a0f202d000d07030042400306801094080500050350b03800340310700a10101030b41104e40390700030389030f00904a4001188140c450428820601c0450200244607126015030358424203603800745020403550340469076a2191990404c0400040b401c0e942045000b28920340c0c9845d010100c2140b0380b20f24 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 735462904 1250 735461654 735461659
    0x72102130e01080c281e03060507050d0e0c102007080607170118020702060d09230a0b0615250201110607080c0c010e0703080d11040b04060309060b 65
    0x1900100f03221030001030588032031200701d4080314001510041c1d51202d02140a24048035910b000090100d9009003000b404031500ca00c01254800c0c0c0d594441c041502e4040d5100400f0450020340e1441d010214028000402d807040c004143d410904000309001b06d4401d4001010007140380e0740d5401500c941085040700703500c210700f00d071915515184001c0c0c40b124140c4480000c54035800e6941141090321035502c2c1210300350484003148a01541504003e0760000320202da03c03100421000a09605034416203001c6030249074480000b02e5213980f44540044103405030081ca601c1000c41e040001d681080c03555000405413245a00a0036120000d14940205234990a00100d80d24282144c00c1050104002c044e0003640c0f59150303440c20f1000309484000c10340c2e05800080d2840c0c00141e01c0e14006004001900e20705000141d5411400d8045080034016001203581d40c01c001003074100c444080c046e2101c0c40580908842c030b05451329100348068401d500c80c581c28540c85186500030b00c03026501950007800c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 735464154 1250 735462904 735462929
    0x1f06080a05030a030509070807090513060f0b03011811040b0a1a03070306060c03050a0c020f151804020a1b15020309030318190303020d020d0207050a030807210213 72
    0x100c0ca001500c0e50403180c0f00c400000d00c1e000005036001c00004100e0304840144014150031400c104640014020081c5403505050200b01c0c0080000c00ba0710905c981c1001040c0009812214103040500391400000f0428800011101001c0400d0291010888011040764002107948100020400c4907900d070b4032154884107411f07085824010700c900107502c290702c143d4080200d162074190590724100880409400900c06000030135559015082c0c9006407400280031b151150725407170000f40f0400c3e0504607114040300c042140303400310700b05007030307032100d10404aa040d0b092900e0758000a0011010f0003aa06150040042500c00c1c4001c81d81c42d243c586168030800e6650385468040320740d59900946a01710805040c2ca59400801c802142c00b411403400c01c809000402c41a0b1011800394010800380c5488541c2004072048030301c494401040118403600141002d41e42508000d0310101c0e000300f4401c18803c806801c140c5070500d4240001040040e0403005031600d0281c2003040041c0603540003040c2c514803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 735465404 1250 735464154 735464173
    0x5151c180c0306111e160c0603140f09210702030a11120109050319030b03240906010e04031b05060106090503210702210607030501050f040e1f0608 65
    0x12a00c0d44401075a015450130310000f820700c9040809885800042c503409000b00074a003400a018000400a00c40703032035014a4808450f860301a40e141d200e60024002ca943c0b04080b410110402c200c007548802c22000386007103894214541c540f9050b101e05c000300b85246810407401d1071003071002650040e907000307411900002094540442c802002c64291807041d081e0041c00807a4038014095814030941c460301071400d00c155426030350300d02916103a207841856120300c65280c581d00d04100f5100300d00e215406040b00c0300c884803280e801600010300007103030540014006200a840502d6415006541807171310b11219a10a0b07600d00c0029466803006105015000001451a0307202c5081000d0b5001142582da41d0881511075003845404078000701d05500060001c80054509102200c0d0582054802d652999014051a5051043c02c64941f408640e42d80c00502c602d00304031440f0400340f14240c40400c4601c85500c1016514030040003031a01080d9084241d02c4140d00c2d50f00580010280d61342203800901 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 735466654 1250 735465404 735465413
    0xf010f181d090604030915050c2406190501050f0f0c0705090a0212040b1e012702070201121505030d05092818060509160905151c18 58
    0x644200104028155a021440040c0b002c60703c030b80074a0389512003c050300e24240b041c2108035098104601071042c107000000c140481841510041011030030b0204504806021032480784070080c2055000325000c000080b2561903503170502003520300034206140c4900d00715a0b2a4000d102d10f840d5074819407004601042c1030040000c3d00c00544004452160281d554492110228003510550b82c03014407000e000f040100c0c01f200b1005411041d9040001c1d4050346560810301031020a0b4009542406038201c00881200d043e0000c02d074000c003c080c190726112242c0c0000f40401e42d0140758040341541d810006512800c0c9100d550f00500024050751b001c5200d400d8080d085401c01c1003400d002d008160b140c6106098244141c200b0201100031007107042d814040000714050368206100132803560b42101140d555a4144041d20880281245480c92407031440b0081151005602072406031910b0418203086004000030380d501c554448084100705152002700101a11400101032104281801d0303260911 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 735467904 1250 735466654 735466679
    0x51b120f0c07063b06130602070e01150f0c0203070b04050f041416090504090c0503010c08240105090406060905030d050a02030a050c16080303011404020403020f010f18 74
    0x540c041640d1955503111000d070b803414035201040d1024072001c0e0b4822035001401c0c14400c0e1300000003241040300d000d40360105800d540403007078041007482062001c00c1107545c10051400644210203181845502d06034420080c4c603849540c07074040c8651000e102c1d0204d8451031640d56165002400c030740c000e035550690314840ba4028098039000b02c0b5000300201c10f0b82071030300401035003a407403907100c251556a2401103403803648807002000c100414408005031070340da43c1c0940452140180310110903207240c0710401d42140c41c13280400c828824411304000c22204c0c081c4070f50035450001c0c1e001c100303130001101c0101c1d0b0328481c0d40343d1503134010f02d05007010407441d503c260444180c3c0d400390100c07400450460740030342d86405084042c40040e8020010350810078403c030054955198081d08550142c2d1912140014030400c2d0f810000056102000401a9080810940d45211000e03201149003c0c1150081120030760f50480d00e0b03040c81028004401c0c024855071481102c0380010b0004100b40b0340364403011840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 735469154 1250 735467904 735467917
    0x7150e180612010e12031902120618090c130906020309061509041518021e0109060e0603040b04230a060c0305010e04062c0a05070803030403051b120f 66
    0x485660b55500d0210405205040c803040544005181c5c0030b6861400210741e41c001400c0f0340c1072a240c400c01c0d104400141c000303000010036403c0e000003d131030141c003408440301d5904c4007110038984250511401c14400300302106410404d0b81d441e940d1a1405200384040d100750f070f2000b803a29100004000b22200c010420500540c146095800303860007010820603507443c1554050664660540401c04c403611643c000400c9400c0d91022f0000d0b142c96400141900076002d031404140749510314a10703520361740400d40002030006420000d03d8080c68401040c840e0000610081121946101003030034044100100c500411200300702e01d006980c60360010f0b454010441044402d2418004a03d035218040d0203258141d07003044041c020360f035403076403101b101a2845d69042d41c40c00c07503400407140b200d941d4072000d0101e5030122001070000c0034403840c101c0c2c5041d030142c0c4501000e41040c810f001c0080d0f4020111910022071034030284c21404044c81080c1407011081e60011140c000040c00c3c0180078150015050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 735470404 1250 735469154 735469159
    0x2360603070b1c0e011e090308091603020d050c04060303021f06060507030f0c053031050621070c030519050d020301120507150207150e1806 62
    0x4541d560740700d0a0755240140034a5601d001c00ca0501e81c00049a260300107840110000004035101d15001c10404036481d083d030b882c0703091944580a000a040e0404141900805004000c000380d80c00440d2007103440c0c00b00d0000921882d10b904888091240170080088500c1c1c0081c810045580d80b03140c040c3d55034445030201141707500f062200c204c0501042c0b2840781240c10549849280101e1036400701c9020031440c0515007440000c1b02c02d48049181004035001140007404107080c2e070310b442e214265902d222049054503400c2c0c10482d407490b14540c03880035614603c2e201000020440749001003034252104e0340206800101c0400c61400000e41c10100d8040500300350080302031030703c1d08007040b110340074003540c0a00030690421498400c0b072209444420701111038940541002406c601c00740682e40285c6c0130070130001b5030070307190000d020b82031205400030009041d00f800c00000e0520065215203103032049904105e844404002c443d0b0041007070011048005244012007007260205012603442a54201d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 735471654 1250 735470404 735470413
    0xe010e0105030f030316141210060e030105060a090e120d090c0824340306080706090302040902060c010207060606094113020a030c091202360603 64
    0x61903c808400c990082e941040a01e00b031b5115560705981031000c0c0e1300c04140c400380030082140d160105006042c00340c2c900c61300d909155807801d03000810821081222501c264546010701405540341828101110381494000ca0240c0d0002c0c20303d414181030385600c80c5040340005c3c801c40e0200c3c040d40080740003445009160300240e140d0b0102e0741e44142d882e001038101051185051890303505100c041c2e501c070800288841c81e100c3c600a691603000025046800c002101c0c0341030010039905805440041cac44660000d2900c5031416900a012070703141d1101a0050b60b0380d80d090400e54071075400322800403400308001e5540e07401914202000b400c0314420440050011007002c10114810007103200d00c0c0c00302c40c62810190308005540c052a60328801c0ba58805280400740020503100c00c141c02110303140c054401600c0d90240b8001800b560450554041000000c0f1010b102c0908001050550560180c0341c000d108220358012500618024a162440e010036440602c11009811042e43c0f08410660944 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 735472904 1250 735471654 735471673
    0x10e151807090f20090d150908070c08030309031b03040e0c0714010605030a0236040c050609100315031b0f093602150a110f120a090e010e010503 64
    0x8004e558086400c0180c50701081104280d280160203c5145030052601120080504400008954041c0703400c54400401240c0502401a0300c0102c0c4c000306003d5000e1465807a110014503207901c1446003220030590311030903c0c4011401001560301401440440c0342c0c0703508110000b0f0710766400c07944c0211603c2200029466401c41d045c041e1200f11503000d002003881a58aa00700140c0c00b0303042c180310000040d01c038000c201c0c2c0801c0241ca110170000340200f84d4000e05090902100d0ac40060300824006c07403042000901c161520171145110260602c0c00080384903042c0c6c0103400540c0345178005401041904005890444900c0f6a00211195061004511540c1e405820142d5802420740800c82c00c0d4260200d4004d40c404412882c18800d4500703450743c0545c26400622600100010542c2601c40444c02d120500e070000c0c100400d51140760020700f0b5900c100380300145d50303841c03488002001c2100442e070924114082c8541f00041c01d841c0301000740d20740c1c40340d54081181c0002d102d140e01c24441c45d60b11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 735474154 1250 735472904 735472931
    0x105070c020f010c0305091201150b07020109060e0102070501050d0e10020405310506031c0c06060e040b161b1109010e0c0a0c02120102160b09010e151807090f 70
    0x130400c0c164540c03907080c2004543d6080000c02c441000b40443c00d5501c428110042100f08185840038100d000c0e40c0a03140c80c55400010f002c44400d030440018400d0a4503d21501d82c0c0024410045540c24078020380d4400c880401c24024002e0601d066440e072050403071008c40c44c003440d00079000340e0300145e80403030307101c2500c071443e030500d100c80000c102050100031f4591034008103e4200d25400360300901240c1d101e5075250f05002c4a00c0c840000b2a000400200e00c070b40c00c00c0254000c000007414210888103107400d20b612240614800034101f1030149000480100103035000320815245c1300c100080200c0c00443d54100b0644c1901c4505000d0f20400e0400c1c008598920040050b034001c0c2403c418031410002944402d03281d982812100360b910000303404640402d09024002407030140f604080c607103840c0903e0b14001c8002800906032240c2a41810128019802c0000e000507090b402d201c06010300380c03a079030441654501c210368507400c00d000e820000b2907102504e40082c071013044a8401003040d03d642c4446c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 735475404 1250 735474154 735474167
    0x1302030f120f0901021606090f170d0807030b150c0d030501030309030b07022b0908030a12110c1c021006050607200604080a03020c09161b050105070c020f01 69
    0x54051038541c050048078403400b044806050b0305001801100e5224100284407058035000368007600000b0940c200502424245500da04010b08103510641886204a01410f84480c1d01c0810302d000c211040c000110038602c25002950505000b400c1040043e0040070600010750000d56010454810003510410f180d211740700d000c1c1204d030182c1e41c0318a401d0440e42c4000410700c01030034550441c4544000d402110088194140c00300c640b40c3e201111905c1400000340090000e94492030180e0818020a0760142d08041300d080e401114140c00078000e2020380c401602801145401116807051420003c201c03d08070f1305501c4100c030f841d001c07288001105000c070003e80319a8040e00742c0100f0103102c82c3c0000342d420800050030b16100e01404440c6503800780414815000390f441541c461348804644410706406100702c4d4582c54040d114030003903250448455001c00c007240184000c22820714003410001000001d80b808517944903000348443d00700040014180c4c145200d0a034460901052440544c4d0300600 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 735476654 1250 735475404 735475423
    0x51f0806010317130f06050703020f0706051c061a0306091006050d0506061b0304060e0a05091605190224190b0a03020402070b0403090b120c0a050903061302030f 71
    0x83c203080f61205042041001d400201c0c070200401e20603200403403100203e020040151926135109a140c400600b030080c0341c5a54590300c040c6035005494140b00140d1320074215804800a5060740380b0600c1e414900c0001803a0039407018528000035030740c5000554104000314040c0d001241c60306065100c24990280d00c0300d1502c41c0d01c01150f4200101d210540d803d8000c141d1221001f01114100006148080c1500c21074149040c1e41d50130000d000d00446401952403a014001a1403071a00c160511002ca054201c0c083c100310300c5252144084440644100121800b9409040c000c807010148841c01941e907401150512616a00000028180b8007596031080d11401c000094800c41d01e80400e0400010454160741030303080f28400001001503210f600041c0b05aa1082017030081901d8241002070070900c03241c014120300b52041207503d1040c110b11542e6904503401c0c0f69107a6540c0c02282c42a1807074403910b21ba071905406035900b00000381c040b50b591a84558001e8082d5458042c146940e152035013600c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 735477904 1250 735476654 735476663
    0x1a1309120f0e0405041110110d0302070507030f0203030f0417010f0e0d0f02070906030503120603070605040e10092901030e0a080d020f12090d0206060105090f0a030204051f08060103 80
    0x4074102c4030103260a030443c0760050f02860341c40740d0900384000460030450308420740e03601155803180001c0121108010f600644401440d00310308252155450588620003403101500e503074900b081107401c0d9681481103690f000941c68200d0394482c0d554041c01c0c103060740300200c02680d5203841055140000785004030364481e2451340103807a00104088059501c00120801c1c001103129002c0d0104070121103125103006140a20000c5031100400b10000880c884010000ca000c0d403c002010403015030040d054a007a1005803180030081e0b9901c505170b24004006070b11080c001420004070301110300444078054401c01c56040c00362141d5180c0b034015010340302c150860f01d100d5442000c00b913011403203c402400c0e410060790000341c80e110700d00c520414180c012003000f0690121110a02403505420016001c2188945c00500910b00d841400640782c1d0050180090140c01c081040c8903440d601d86020388003950340200100090b00f082002c00a0b6450710b0350381c101c1d14407910a4046100f400006090b812071707511 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 735479154 1250 735477904 735477917
    0x9070906120f080a03091205120c0906070b07111006090f0b0f100c0507171005010b122211010e0901080a06181712010905070f031a1309120f 62
    0x2990f01d41005030300c500c00f002c08140c2e480580000050200c941c4007100d03042036850580302d07090382101001160004d00590581d040810200d40240c507900c05031294a074101c21000341d02c0d683ca02e400e88403012070340201102c9009101041c0c0359902580d12050540b42c03030360070400000e200500110200d03200302000a62240c42c3c074400040d5460518018002000c4519000c1a400156900c0c1c5240031b0090300001c4203030b01c9445051422403010030040e501002001010301140d4500301c8280c02501c5110b90b04561800910001032285210104942c0c3c50850700300340e081c510302142080e50340740d03082c40319071800901c0c00b03542440380b171400c071344058141c4514030082e0240c1011996030b40000e12019402d032405991006603070010070031001000c006100d20505642d500d002e081500841c0d188140c01071144240b6010901054a81c000c0c006861111942800104660280c808070810b003012541c1907440f1510395400038860a642d042096100e1041c0307041c2314800700390082a540000c2c04000325002484 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 735480404 1250 735479154 735479183
    0x327120e0117040828092c040503070b0717041b240216030512130f030311060c040303020c0904061113050a050103180f0f0b07020610050307051c050f01050907090612 73
    0x400100d0840150850b0014040147d030000e01c049002d0000c940642d039541001c0f8085c818404030317650303280e4008601d242241048032000034000354803901800141c1800e00c2d018420001210200120000d004450024481c5900345401a045102a43c3c4150010702036400c118080245010800c0103507544240541804c03050780049100303e4100030091038400c100240300142030540512461b0186000f55500c02c552186079001c0c1345000340140c03803018020b00400040001c25030110303008621003422640351045450340d040100280c580f1845076501104006102c440f02500302c1140c134201e60341a0b03006900c41da50344006504454941c082d0301118a9645100800286030044100019103c1c07043c02c03c0d41c6e81c20f42c0b5000c10300b410880c0c0d55405030b4441c409101c0840002903240b07005080440c010203210341070a010428954040c04246202015081200e04101d000d2004900305000540200704516055032840c3c0d0b203003180d00c94000b26520f402004a416101c041921a90f07a42204803a0320290 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 735481654 1250 735480404 735480419
    0x14030f030a0509120316030b0a05041103090d1b02011110060815090a0302120c0312041a1f0519080115170f030403110d050a030327120e011704082809 66
    0x526040c2c040d404880081c9c0455103644500c00e4039500750701190280e48038a070004400d441c2c0448121094184040c800007a0880e4030b182c1075a02c5040d5081c44d200c030803503200103070140c6000d0391404041c1c0254106103010901303040c00202d140d901000d810f152007c0713856141000e0b0300c408510402030011b030032035015000704e441c1c034100a202c58103450742228035100b4100c6050f01110070546080741d009190390100c2c174008569040898108144c0441e09840d65018500c02403500c0044c401d5a000310040c4003c20000c0903d00006402010401c000380300380c4400d8038003400022031074010f103011040d85080c000c0030f0b06000260303480307480c0e1454000e41c942800c5403140b01e14030100407442640102450032110000e1403d000c0508154801d0b14045504009190380758490001c942040b1858561031248502040801380c22100052142c1086410318600000403140d0469400710f15101402c08001d000c00c0001c0c50000b88101c141991100d81d03100d40b65030b440300d08000c055480d10b0001e071150380240b1161 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 735482904 1250 735481654 735481661
    0x4020a060c02031011130503011e050c27090c04150c2102060106121a04020d0e0a0821010302010c0b07021c09140108011214030f030a050912031603 65
    0x54001011620b01031400315074102511040c0c0d01c1030000ba400401c58800296410303a1100247c18124001c0c0611040c030840080401c10302441d2415141d00d03600410040c0390030004803580240d0081c19030b0b011038421448207107801c1c7c16140c4070303009045230380010318550001001c4d80d003500c43d890503030004464075840480d02c030304042c80d05032604140d000d11000382d5804030710944021f01003600507113041d40c0340c508007034160842c0080c2500d2040c02c1c2000041222422144401c03400c1c800c450044c0c40c1c204026502d4028070400c11401480d20a040c00366040c0211040a0017041d00707202c03018584059a52218940c0007020700c0001e0106003018100400a03413500d425540c00f811500c12200c8490010617840010710700e07500814041480c286051207410030b102d81a40401000b802c10094951500c3c0314040d05805c08403001c1c04a258407501c006040e203080c421200d0384034802040d80d03200d0800541c036a0003481d0640e2001980d2084101600e0809590710580380b0074041c800c0240448070400c441980903 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 735484154 1250 735482904 735482927
    0x301030506040b060414091c020106081e010e2d0a210314071101110f0318030c0307081b070e0601050901180902070309170307060b04140a020a090e04020a06 69
    0x105c3d403580b030100c1005182c03580d0310344110005002810602e42c0c1080c0c003a50a5010080842164107056081c000380c24006000540b2500030850181d50b0410360700098014044100501298060040c03021008042c0c0000c10059601007005801400f683c040259541d12442c0c2c40107251450342c2903170700b2100c54440050700300c1c0c000328100845d050001214203103988030100c0e0a40c011459180182c00361003024490322446021180109180907401790420300c95000c01000b941c2440c21340c600c07a00005c20107205a03440d0b102020b0880341c643d140740c98085450380100c0420312400400c0c641d13005c9050000140034040f01c2c04010700e000030f03440741001100d055219140c1c99050041c807040f1200710720790010b081c50040644840040e120f1101e03180c0100a0403080d8080d050f4400b10070844181c1c0c61006c0120340300140c4c040c0000500b05400d01c0410040d000b0032200001a030021820004107074504cae0001c192850042d0b64090501d52200711440851100f643c02942180750114180451070007807088941 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 735485404 1250 735484154 735484159
    0x1404020d0209040924090f080c0f0106080106032a03080327100e0d02060c070c090504060e060112080f1608030a150f0e0411120f01050114060301030506040b06 70
    0x42d0900070408142990f03141d61044503e14500d141d15168980f44085480c104113101006010302c41d8030707440d94032520801c001c0141441800040c060090907040054910301c03241c20000380305287c3e40700c0b6140d0007000141700645d9008055008200325514051184404c1e080f82048121031608548501a00ba00001c02c0001d9480a1204107045000c4082500055444107401010796242c00003440c0251044408100b08941c010420413041d05d8000c02c0e9961300c040d6481110351a000746042003900c220441d0f101000daa4030f410180420f11542c4c4d040f48014281c10000c8442990b070f01c1000c11104c91964001928021080c0040c580742c100e010000c00c150602482401015259900c03244002e9005481b0300c0c10702c0f81d948130010548100100310b10004d04c0d6660600310a24585141c480861100410003845000b0038030306190a40e4800f041e45c0c98002c54001282c00c860752101c503540c0245000e00a01c0c4100c44024041040ca10784039080b00d0580c2d174000041d00443c0c4490350f40140c0d42a0103000c0382d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 735486654 1250 735485404 735485407
    0x23601050c211b010f0b03010902011b0305044e150e070b07050f0c1e01110726120f0705031606091a09030414010207150305090d091404020d02 63
    0x8000608010f2a15050700804000980344804207400b400301da51301a4514046d0b410600c4480141c8c0e08410800e66543c800031f4904000003d5103000c885903c01c40d042045641c0d0940444107100403480388581c880441d03c41d08104038003030b500f2405031203210741030000c820b00e100354903030000640e29000302c2d94644665900400c1d80d038030710000b5508007074081e001064a06000302d1000b00740007040000302061304141c0c000d00b2090029402040b404c0b0201300c400c06607160381403407910240c2d00c60114810064051070541360681c0d00c4240c0d05e81410354201e5400485130301c580c00118508004140c9560711a5050031492030078651462100d0a9000440252141d01003400380d00700400364008220a00c901c10040051403030b00505e05460825260282c6690845041040013540d200020403038080c1d41c0388100c959003042c81300004034a400100d0308510240e00759541846841501500994050001030055580b54440d070102215810898840c0400088078001c00b101142455401408038203030880000d07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 735487904 1250 735486654 735486667
    0x10905070b1b250e01050901091109130b03101506180b0a050a0909020724020405030f06040303061d0118060801020c070915030807080a03023601050c21 67
    0x1903041c000440c0c816911160b4036000803411000d0b08083e4000f4188240c045181c6505102c049580c001d014002c8000d166528a13540c030221340b403441607500742103004003203603550f09a801c10900034007204801070340244200c3c1a0300c07000c400180104405410f0754001500d140340362490484000000711030750348400c54a0100451850500401880345014546031540c0c1d030002c00400070180007a5070310505d000d903c14080640091824600e1924800c03244080310383e600080f02001000b84140c0d40101c3d4180b00c0d081003c04c2441d0007203640d070b208600a440402580382d03107040603075240d060a144803e40080f510014400b4808000140d4100b440304080050402e0301d81007440c1c220b0344207810310000c503400241c0400c00c141050188100800390a03001c00e00d264515a2444a540681c0c00010325141010903021403180c4a6415075080300c810513200c0b01021030408400c0003061800d0036100020140c1d00b00d001c202e500600807240380e100c4030b0008000c1000e150034a1040c0d0741c0b00c1104040e5440080010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 735489154 1250 735487904 735487957
    0x42102190305031905161101050c07182313032003180a0b0702040e3901020105060d03110a080c0c1e060319061d1503010905070b 57
    0x1018091841540155550420150340c1401c0c2e00d1060000410040101b142030130341443d6585d40007885902c441031012080b180c80040c0d0300d60007184000311031882a51030008040340440580031030410b60381420040d64403843e07044010b002301895410310704d4108002064140d80d164400311869030203454002c80b01c14002d11214101030003005920132560000c10031f41c01080100100d6a140e10080f07840404031880c00120041034040c0d1a0082d00c01c03030340e4004400b8001e0051082a006144003103d0802280e01c0100310040b06100e059800e21701c8000491651036540144501401403030f00405651400203595400c51344000c11040c007010038002c2035040b400040031080038000301e040320070241034800044014011546102c0c2d82c44410bc0c410f032042152a40c45900450340c002c562201689100040a00355802400c1a648500705614010000300030f5403030301d1044640038462050b94501050301170f208140c01e85005410203050f41d002103004000040e4814010308640128912410340c000300d4044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 735490404 1250 735489154 735489199
    0x203011409060301050103020f01031d060c070318050913021c0605060f010e0a0e0933010501030209090106030203070c080318070509070806010e010e1f080c042102 72
    0x46549180e948011160240c6401c901d020303803121050b0001c00c41d81d80745400080c038025a0124003414140d4510310359155100000e000b010017407a103c03c6a003e810415607100007a8000d440a60010301d01c845084000c1d14000010000c49a000380754001503180c0008400d010381d0200001c9902c10100c00d00000010703000301c820b008240c081c100001d41e615100041c070852210392407100c0d04114064000300110381da42c3d22554250f440140803040380340d1703801035158907020442611400c0812007203820030346054602f0106107500328090140328540d030ba420040d010f0380160a1582e07840600e0f000140074151099001d141d1154030f07440c0c540f40740c86440d150301b41b0300c5d4000d84124116032400f001b8440030300303000c210400041400340c44041592800c014018400d04010300701c0341c10020792914641141e031282c0050040000020318541c010020000d9108650440103645000305046c0300005140000c003406440c02c4880004030034551192900c00c840e00c000c11140f0890f030160f9106140da01c0c00d0082d01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 735491654 1250 735490404 735490409
    0x15030b1c03080f07020f0604120c0507030b01141f110c0a0f1a03041a13060608010b090a062702070b0c030414010615050d0f0c0507140703030c0f050c04020301 70
    0x485810702410101c46801000034010980d00655000c1e006c24401407900090290340660040d042c840309a50b0f06000311041c8803003850251491091500102c144110703260807074121500500895141c02404052000a0f990010340ea1030100112410b007000307602466002d09180f9141058070301c041c0182000844002448e0001c012410012000b8482c180107031142c0d50f00c040a074001c150640c6800e9440c02092241c0c2c41503400841c6108002c40c07410390024080152203030b40040c05108198035042428024021044003e20a45404c000306445802c01d00c42c00d03040d1407003800c0a500250358231124819030b4442006a540c01942001454041182c0000030390050388000c0b0180e50b2400c0a00380300013508a001004121070345004000c12415134854100380401b1035504040c2d4607195a0406030004010304c61080440303e0418800000c501c1c0c0c0140100764440c4140540c0400e4005003101c5039898203a8000100424584180b400110b440080040007084c822011544404441310109090782c200380e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 735492904 1250 735491654 735491657
    0x30e030409060905060904020619121e05070e0a090e030f0c0c011205010f06080703090212010606090f080c0603060a09060e010611010903020a140102090a0e06010906020715030b1c03 80
    0x2a08148007142c03a038000d05801ca0700488003007880d407c19400045052207510000340349411034000014043e801175a001440d980035150030001898925044400010407250075600c00746000c0000312018082c9040f0088000f001e130945a0090400d40300f0401006445130300d140d0b40c0320078807030500c103510030f5001411f42d00000c1c405072084880c0100050321011210800038019420180144407248003d1340c50001c03501240303031141031500c903840700350002c040c800b101070b41181c0307209542c5007404d00541225040380e50b503588503142c06540d60f14221801e0b06038007807494a5001007200505900d0198051500080d0090082c0d480380c2d900c0b5541e5084480540c0008441052540104012034004083c2c4640501c01c20091100003280d6030000d45031000340d040180415010025151180c40c254141c444800028041c02c200381e41743d08403564401d0702202e0403800920f65000108640d88049a141d080320180800c003071100160a50a4020b0400301d0085600200040007074195004010071044203075000303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 735494154 1250 735492904 735492911
    0x33010302161b03030e030703031b060209060d0c0801080d0806040e0c030601080106080c0616120e04110405030606010318080706020706021603021507090308030a110a0809070e1003030807030e030409 87
    0x3d42c0f4001c1c1129200c4d0401500c2034010420803c00300c0c1d040042e81d070880c01300603041c219a00030391500c3c0009020703002404e41c02c854003085103518103403594090300b4000110b032030340c042030781c1e80311510341e0744103003049440c8005040328012441e41d060603040100307500c02440a44a90041010202e882e021003640110442e0391211010171a05d0024080c540c0c0411058540520303050206c241658510140354004040d03906aa96031170f1a2803061040c1c01001000910500c62000c01c0d8100b8401a007060046a20900403980803a04945c0203106011280040030f89031241e1628a13240c6103580d0f00f201f001038810b55000c02160000071428401010a104141ca424458200d5414004e140c440c3c2402c804800d80003582c1845211a00400340d0401c07241e00100107981c9070ba5461a4102034007001c04ea00f40002e001107084e02e844c41d000420a41b00e4400c04040f03072120355540c0e800204c0860103591040d207601c4840014808a4441c64500364824440d040100b401c02191100c0d502c0e41c0e0150380f000454994 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 735495404 1250 735494154 735494159
    0xf021626160c0510050327120a1209121b06020d050f16080a0e0102040e0901140a1b050304020103090b151203182202030f33010302161b 60
    0x142c0103260800b82c401519808244060b00c4006801c500c000b91150703112a184410001d043c4068001d48109400700e0400e590340301074940c40c06285904a4401180800e07040080c4000b040103510586550580142580740d10350304000c02902c1c0c1e0100c0104818002c3c1c02c0311a0319001ca0610300041c4801105118001860b1a01c20000c01c0c00b0480602004d100f11103144020b004540e1220540c0d400000d80724000904403a0306207960b009120350740c42445c81c505141c0403c45220703c10741c48520000000060b01038541c0d940003941742107500340c2e0303142805c5062401a003610715101d80041c540c40740c41810002480c00781c079204c5440882c4101c440941c52021803040700191b04107a9518103420808000443c1016180414401c00e041c1c2c0000e158040c07840740001c11020b0440c0d03103440b1190a803a85d011075583c03d02424044501504503a002005280f07504c048100e100c900380423401c030080d00d0303c664100e01000f0004401030360080d090340c0c08032090108407030046140c26118858042002a19070320b81c1e031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 735496654 1250 735495404 735495413
    0xd41031603180f21020328150f0c09150806040b122b0903120c0803070c060b09040209060904081e0c0c030109050a170d0c030c030f02162616 62
    0x4076003400648800b901121321005850000c0c0425050a4410381e000200200503172400030382c4000341c00940441c0311041d04182401d8a94411010498603944c14080e00c003201009031101a814441c10001c0b689004235002d486100c1d055080e00a4001400850740b139943d440001ca001c0c00000214000d03400207d10b48003070746002c0f02c2e41454644441d881390384440c0000c6010305018414800030700b0f86c48031440c020b120103100301c0440072642e50090700c440c3c6070b090500b40140124425801265460700c0c115000510745020b02c1540e218650042881810b5604c11061010340103010704200c0d4440070502c07072200b411510070000080e10740038484494a030b08a0404180c5810807014200d40281d26007101803001c42c01c0807807000079242d008055803075041c83c0d44020000c8bd21456801000846c90800a68155030b810381041b02c1c4a08103644c00c0c4102c80d00380f0b40700c001320b105014441802110b40c440c0d14002038800b5250303420a030f02925000024840a80e100781d0681d00c030618500700c00786003079200300800c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 735497904 1250 735496654 735496679
    0xc070807081809150d110306042117070513030b09150f0108030304030c03230403060c17070c0201050c06070903050609010216030e0d41031603180f 65
    0x40b0b0044401181508158094000303035005030b400743d4010001165440103100500d54003100c0618040c089484600c0c2500304410b541d1500c1f130810712070524400801083c0c84c460f001c9201c18003d6504d2008a5031500e20042e140d81d400f00d81c00401d619899500000130404145035644125040d0700600044522101c101d400d500b0005c1400480340f010f0f40041c01307040b00000580e0f42c81581409c1810346100c02d4282035514050881e4900006441c0d50000d0140fa89054040c00451703102e941e042c0030000d2400019900400c154200316100100500018400341c8205401c0a1190040c1003403840c000c606010981080400c5406802107000800c040041090402400307500c402c0c20802141422045030303041000d40c0310762402400b00404401e045c0a5980c4281a40162660107680011300030034003440441d0200350040c400c075114946001090316091000034404240c850031015614103050492001008520124140d08005c0340454500900842c1140c0c2406000309508003400c42e8605400342c0d44a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 735499154 1250 735497904 735497947
    0x2f060702010c0519080c0706090c05040e010c1d010c0b010b0c1606090612020c0d080603060106090501080408030a0213081c03090b180f011e0c05090310050c07080708 73
    0x410200300102c80b1034421407003440701504c100340351080c2c40351140900101e40f809100000f50030586889003640070014039484050071550f06070380030301003004a21041400c036405003002c2008281d402a07400b4411004d500b8910742e489050610248000280e1502c075000c800036000382040c154005138002c010740e030030049154407e513100b4001c4484da060640c010949800e51103a4402e1003090030b64440d5031225501690350301070400046800b003c2806d2401800d190040d1009406801040000303d1882e10501190094580c182c4401d00306444540e600c400642c0004c000302003c40d07080c0300c1401e0009510003000006c244180c001d180d11460074442245291241a0460516282540c20340010340808044c691204220401c10701d00300031003019074140b80c100e0b000016954030341100e0444003854418100740c1104540010000940c0b122010398451041140103035066000c5028140000742c15041194000c4840b42c10034105000baa54041c1d03290002001103c8000e00818142e1591a84043d01d010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 735500404 1250 735499154 735499157
    0x9061701050c040b03060307050621061c080c0703050d27060e040f060b0f0c010b0603060906120a08400920040b07051005040308072f060702010c 64
    0x282c0c1407400001d80b4030701c510f00c2992140321001c0300140c450380d01401402c0080c000a0300241e992500070142045200c200c500c010804140382c80440c4135030800a641c01000342d04100007101004090312140c480f5002080108500c2c42100301c080300044050240c0005000e840e00d5076500310004050040203007030060b51044950f40f410b0402c0105950001904c0c2c5c40e0f02c82980d00141c0200b41400c95805415182c00c03901c28000002000307654252000010800580254020400e543c80ca80400c0454031041c1c0c0c03081e5000d2540790204005240c501c0d6082405a0185c2c202c5041d0039035940c8511040d00540d60194845075034003582c640131280d00440e500718042910140e80c0b07020400d038005200b00200e000f00b444803591141c100f94103400c613140ca80752400d15032602c26141e990b1003000d050707160700c141d100311030b14021080d02001c0301c04980900c602580d40340c3c0310002c903913590b081c0c1201c010040070206014603950440401081a008500b03c84121036070024142914014202a080d520205030341e10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 735501654 1250 735500404 735500411
    0x90f010e06060d060e010608030a0f0e0f010810090509060609060907081b040b03041110022b0c1a04200a031707120206010e06150a0f02030c030409061701 68
    0x3589180c041000c541c0118115003043d1840300c03d04040c80207004070112a40c05602e0100007090901d0004041e140c6811959110044240c1548044034803400601002d50000c0d8410340c2107125600031000c00e1341c414008030f10701c50426070701d400480948006071900e50030754000206000d528109903041c0c903031050040c1c501c083c03d070034101c600600201009000c102c0403606020100d00303059500d421200200a0240451b40300c2c01c0034102000910f2115055900c20014103015000007400414003001c0c040e2851040c44410f103a414038000101074450f8041b0410011b011000000366620148100d481c020f10b05922503480c0030700c5d08500700103555011400303842d110703c54a9865a14003401e10252540301c804039001102881d08442c0900030110000d2100c2d100101f001070f42035000400a0403503a0308441c136045902d4020610100c500000310f030846006041000c3c0c0d0029018041e1208000718900c12039141c45032501d015400c42d0016004182c140d0384034101000b000001c0205941042041340080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 735502904 1250 735501654 735501671
    0x10306060e010e040209100504060b032502190203010609060311040507030615030f06080d020a031706100804020a0b0318010614010c02120a0f061b0c05121308070806090f01 76
    0x1c000f96400100000d00c28000c100000c1d81708201550940001c101c0504280122074465949240e00c4d00211140a0500310b082410004e41c00611044041111681c016000070385144002a400c161075030b4040e82c0541d21b030000040d02c0d940764031409004500826000c43c0f482e403103504201c180c80c1c001d8901000c050074a00c0501c9146407918804d60880301c2e07400d0029038005440c0362329000d810b1f03075072101f080c0e8019010500496900400c0d025142c0e0b100f0f42e40d0001081e070000000c603000d8816121a500b010065030792120a80c000c80019404c0350000300245a000d03990541c08110b44c1c03007181c400041c280d592101040181d003d000b4079000d040208200c01d100310b02d0b400028003480542001078400c610301c0180944a0205101588901e60822000300d0b0300012402e100700a000c2c54030868184212071041c1c81c290303521801d502408590b001010302415085d5130180312a0390005492080c01442c07002000134124170030082880206441070280c03030300b03103005032819050115400c103640c16a410f004da43c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 735504154 1250 735502904 735502919
    0x12050402130e010f02190207170303010e0403030b1e0a08031c02030403050d02030a15151403150301060e04111207120314031003050609030717161208010306060e01 72
    0x11200c00c00036180c000b030b08070b14040e51140942401241d0210f4940300080c00150101709280e01e070b40c641110303000c40345030940d42c101401030f8908404045045030010720060050440207040c00d034106029290102e06005c4610010305c0300360307158513103084007070001ca03030710b00c4034200b4502c041c0042001c000a14103000510380d480c0e14082c400c844403800c09500200050405000c5c20540c1d003900d12040c01151240307801202c540080041c02800381100907900c10008858407040400c0e0f118850341d90783c41d42c800d20000d00d40740c213640002d4661680300200c070300074102d2602c0c01d210364401400c1c5844508818109030800d42c402a507070f40310441c0562040d074540c0387d007850009051400c40315070344020b02c00b05c44a41070498440d8084000541c2028001007803080b004186650038058900a0054502d16141c00c0706c0c6650b02d1240f89002002000986070740c0d20b10340005c2021b81105880415642c403005440e44d5518030382000038007031001242c0c03550014000e2001a114000c080d0565082d0707031183c0e5040c0310a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 735505404 1250 735504154 735504169
    0x6010f060c020d050a0b010612050f01030f11121009060f0c051902070314100e033405030c070e01050d0206091e062a19020907030e0d050a12050402 65
    0x50207070084108800183c2009810081c00c04c0c22900600700041c42e586420009100c00b0302c1c2c3c598825602c4c280030204103041502c4009a04880d1321940c8404420fa9568500e40c1c00d01040310000e500801080c01c005480c1000e00000c07006070b500c0d620018140d2894a016804c50b2060401002c9103803504c0881d842e50f58121045600d8083c6c401580000313221805801c03883e01c102500002c02b0a49400e150300c0e058800010b80750301000203038906000c1e01505003816a5240a40c10b222000f0030740200f0806d4902100c101400714082c4028518101400292580d81c650350184464588a40c0052000c0102e48110b010030b6001d0002150b09240340303036554000401034000e100711248109090f10240d1418031a400914050b80ca01808107916000148054482c9801c0b00b20110001c21107d446041100008110091410100c01c400448400b0076001d0000e6988000c00c1d4206069590815940d15201002100c04070042d0f070307071250703550880390000810400340403007502c1d0701c0c9090906010042e9696023 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 735506654 1250 735505404 735505427
    0xb0f0603090a0b0a060b09060d1e0f0c0c08040b07020a0302030a0807030f0c03080a020d090c0602010e101e0b15030f0412080f0604020a0309080c10150806041b150e0306010f06 77
    0x84500b41c44014440e100300080850200392034524000c242104ac049140b500542c0050440802c1000f0070141d11105494501a5100091200070204014410711403004080c110960018150345601c94517940400e29144100a0540e402080810001c04050348a02c144500012510b040120075001d558050250034028125801054003c0385003d22038000781d201d98240c40d085030386403654075030b90b502c040c3c0241718400360704c0b21a005400c11159400813074021484080d181d41046e40c3c040241d0003205d40108440300000e40d115000d5690048a80324a40c060340c02a07194103441102401c240c07400c501c4011440d4800c9052064071010010398201c0540015403058040c0c5002d41d584268400880007040f650900420301d241c041100039104400065503100341c200f2110800c0302402824002409050510401206520200c0040d00081c81354100800352140300c1a2030424544410b4200424040181000300280100351406010710741000414014500803800301c0102d030418400510008021 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 735507904 1250 735506654 735506659
    0xf18030f090904061803081008010b1503060f060d020a23160c0b071a090c0307060309240212150f0f061306200714040b0f0603090a0b0a060b09 63
    0x18140500c5402c081c1982807004100916500700c1d18011f01000b809440f20f000d1818a40808a1417250501c1b80030707502c00c3d0041c035043d1581c111542103c0c0a0384000e0410340c10201b0350403000c0702c9481d994050414040c0303001000d41c07100f03107541c0000c254081c040780101d441305074100d02c0081000b04404659040360201d84640131480ca60620310300c0040d080c2e01000e0b25407070002d150350600c600c01000c40f0581010f80000700f10390301c4507584960303900b0b1708401269068102038000c100c1d90b8003d81c0040c0c03000e0702c0b030494025001c59203495500d91540f8014000c0c0f295800003092100b1000d4960000c1d44105010304c1c0c10040e25136074000c00c90307040300511128021145941c00b000e00c0d90315042540d04008480d04600c840c1030316407600501c42c0d680c01c112441c01c141c075800b041d1214000407031654107951600390951000d00d60b580400001e84846c001c11900800d182480c0344603038980800542c03080c44201d000340380b480768502d82407078590701c0205801d400500d484001d12017a00d10000300d40038081c04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 735509154 1250 735507904 735507919
    0x81203100e10080607271a1c020d0e061b030c090d02130c090806042d060908040f1409040b04050f061906062d05040b030f18030f09 58
    0x24120700306403440d90b94001400c0e5104c0c51040015180d80710091441d0100c0b05441001d08040240e441102c914907030207000220546500221070940c0c2500242c4034080142403503400448050150302d080768402c2d10711610302521075405541001e02000b50b25040140d10b41c5907032807240e604024081c0e601010300304020a990000c0e03501e0059580760304200780d21380c00904e0440001540380000d4001c159522440010a00701040010109004075400b4801e98210b01e4000350801300d094104d400001180203e0707a0880072411390300c081409449000d240e5071041240e1035445090110070308410b0704951051405041030030b20580381c1d80b15515840d4001c0d900c4050311035a0385481c81e0448c00c0c62802c14610406200c1d5408218060790002281c48070220854001c10401c2d80714403089508101e003c510b40f03441d08040070031600340b9841d074545880307420142c500a41407544070000d810841d4400e603000c4d60300741560000e01c100c5040400841940c5480c250045181480d0145500300b54028100f209100d1041c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 735510404 1250 735509154 735509161
    0x90d0308071701120209060303070f0611070f0302010b0301060504061206180f0303050a0b0603070e0111071a040f0b0403150f0204090f090c05030d050d09050c0405010807081203100e 80
    0x1d8401c10680c56001c0e8265030702c0c0c1da11004882204520001d069215030b5a2102060349410044115040980c1004072407500b41165100d4001501401c080d0302c15104003004818040f032039a02a071042240710b60300104400b81a0001c0500351000da130405881203252401c20800980340d410f04014480d4003401c0415560540c4a10303a0b03400404690141881c2d20815a440415038542e1002d403148159400c100f0080c072012083c070019010898041c0302144038104c01000c8d5600485d1380e108140080c1080303800310303621400150800101190019400140481c00780040d0141c03a6404014140318529141081d141d900e0390380d41068194800c034a0700340d40d00d08501e020038aa40480e00a4107a503c0240300a001e0141c0240080652850940309401d2600d001b06192a0110b01c4104083c1c05680e0a414029101e01620050403140000c031541d04c5403140d140c005456901034a03000780f1550001c1c02603a0301d01711016081100c0c0e5103418450500c10010000880e09010f54141914101c40558140781e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 735511654 1250 735510404 735510407
    0x130905010507080f07020a03030e0c03070b12150a090e0a0219030b010504090804052101020406170609070f0e041d06070f02010b010f1b0209040804050a05030106031203092306100b090d030807 84
    0x12f49280d00d06070503004a01d008641080b44000414000210301e103000010364440050741c0d0800b545c0301c4001c1d4013101b109001c10152130729400448130f40d01c44c08203640e200d0746039a0005044c0107102c0700c1070f0518141d00070100240600c2c05401401040240d4061118841a0790351002d9481280105441861289801c440c042d01240841e0320740c01e02038008650780c0d5110f02d03028080c00e8965030031940c1c06900c040082c4081c00c1c1006003030302600650b11181c0c0a100c0d1460141c820408020000382c0003503480c003142243c9030390549c401b007204c0a1203020304260b0401090041482c0c51130003440055a040410000b0540d921000000c5c01000703620703206410b200802180d02d040079140f0710280d032150100003480705200c0017800030003c0300c40032a100114a6a07400502d801d0311101d20018152103040c1400d64822030190308840b480380d115041d0514501c10800710003004081c40803000d078172940481c0400c8202114501000058241e035140e2500b804092400a17440e0520b410b40101000301c14000300c1c120301d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 735512904 1250 735511654 735511663
    0xe0c0a08100e0a060515090102071404090506040c0602151e070c1a2e0902130b0a08060f01140a0c030201060f0621050420130905010507080f07020a03030e 68
    0x100100e08040302c260800400010181855015203485546690803a1204a20303540444851201c1a00a0300c55a4907008400303c440c900010f06503003060300d0340034010003c0e506021940c403c61040c59960441307420710100074a003180e26031130921a060344105228612040305280d20307003021003110304106075071344400032901400d1040c0006d1803072241c501451004500d031401144105100b450441c400c207842e4414415041d81c8002c541c048074115241408040b081d600201703035002d030f03180102c40425a1003502d4000c640c080341ea120000b9442406000052501207141d0308505400d01e404540c0603090809812140b040300d0780d00003444604c2c0e1501c1c003098001e40050006042504107450f1082e941c280203840d1664022105520309001c420300850401540300d001c1c011074101004d80410781c80555090001106091155841003403ca1505000384590141407400c81c0304200125260520900c05001c1482c040c0c141034400421204101c0300940c0000c2440c00c1e40d0f09403070045000c444103460942403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 735514154 1250 735512904 735512909
    0x906030a08090616030201144b040305070b060f06031303030615020a02011116030311100614090703091502130b1b10111804020d0501030b100e0c0a0810 67
    0x540313420700602c909254040d40151300d0010915085a51507460010840c820040c050b0106032412100e40a0041c0340c0c01c41d0780f44070b925900d00c40c90040000000c80c81c080750400c110307811400940c002418008000812290507048501610714001d108550000114240401403031800691040a201d106040c8250800402003202440c040182e0045a600030340b00c1c100c040080c1d0100c0c1c0520003c080a210024546040f05045042410b1544c1160707000c460324648007c921509100302a000c0d0110482440b41400511b8104a0b400c0048039440c244407c081c001840f00040c50316010002000c11240c0005905000084000594516001c0b030044448001a003041201c0000800d411240020103c8ac0702c48040c00c1000320742c24071040780c440364243c0300300c6154000c5401052180741501d40e0021051290307613000400150518064807914400c6501c00d038420340e011440a03080c401c4040d8884262005060015000100ea00d84014140701505c03884903075004010f92140000c0d030700003546211101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 735515404 1250 735514154 735514177
    0x2030601120e01020a0e061312081e0a1b0b060f12100b03061f060305072c1002010c1e02070302130b100e100e060c0124050906030a080906 61
    0x40d03040d900c02454001d400545504020820140907048585031002c156030120026800f000d500c41d041c99100c443ca03400c40c0001722030101c1c0c2030020070b0710301c0001410701d078a1343c0110325219104c2c00b545800400000c00390b1040340c1602100d40313722010a003803995150f401724040d19040148948800400e0300b4601c0001c502e6003501400340c47e55500c02803504030040307083c0202d08442e0b031610340040b054024050001c4600b007500303901404000d8540241c200c0f6034041c40034107120106502003010310b01c200c03013181c2d41143d000081031040d0402e442d002e00c2c4503078802420f01c02003201100141015114038003e4801300b00340c1072500c400300c0c0c038070348200880c030082c41d40500b20500380c0d2001c680e4000035180308070403d845002d401140f803940a20528005003da0310051003c2c0c1c41c0001c0303400569158208000043d00b0100c01c000081d20340d0000d00810800c4c0e00304136030200008070100190041070610b500900e12850140090101c1941d00041c0580b280b030300440010303a11015800015583d2003100e04444 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 735516654 1250 735515404 735515411
    0xf0302040303080f0c040b0d02220e040f03030b0409030e150406050d0b040b04090b340c02030106030507150e0604240c021509101107151103191b0201050d0203060112 73
    0x7655441c04d4012b000c0107052080b000151036805801c0018410150280d0404440a103002402085460403550070660190400246d500120404507045d5a0a0841907020a104030b07250095400e200000c540c01d0700700f00317214030b04042c204040100248510380310400000e88605000d11180d0707543d8003215807000c0040c0100700c4c2e00b84903e025141c118003202e005482d08090920519a484800302c03802d014061003803800d00c00d240c296800c1d01c10581d003003016a09996907000110010b0341c10450720018000b003000c400a0795840300303802000c0003143d030701040c002d000a00c410800c600781c115580140d407404031024040360036100320407907614a1a80c4082e500c403201d44550a888039410b0010801c02606130390100f0385c085002d50655819829a0401d0041e82c0056000c00c02800c121441a295203854900440c02c2c5048103255407440d00038510b500c88103403110000760511034106000740310000c00380e840e846429100e50006051406080f2a01440c15000400904c00760f10400344603a107440080c8040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 735517904 1250 735516654 735516667
    0x1f1403010212070f09080d0c0b0901180b1f050306010b071b0b1215090a0c030603080c06010e0108060f0f070c1406060f0d02030c040b03120406020105070f0302040303080f0c040b 78
    0x6004c00134100241d404240c04403c08601d0740000f241a00d161001601d9200d00c0100c0e0340d85101d071400000f403003184255661a07100584510042c0c3c001e02c1207003c3e82007035407241007412820132a014440c54022403900c411a040100e5100807802c0e80c11a04503626840e200c0e02c1500300425443e041d4201c100042c50b41041c041914084400605003010032001c484119596500c3c00c0d4410205400240340c0c04049840000c281d4032a5400825030b4203464a4040741703403070741c950f80c0040070382003011245110340000c0c00501490108166150040c0b84501c02441d503810701200254002c48054541001c43d1628000605450b029214048016501244561002d40307601d030b600340c5645041d00c000c1d110303460003000c0ca0000c1c80c140d115590540e80040141951051300000c10008007020054076070540110404031024035001e0f0701400013801d081c1c0000c00d99203085540145410142a640014148180001d0010a6118001c2c130b40c402801c000c500351030781700d4902c01d05107030007942e10094403000e002a68 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 735519154 1250 735517904 735517907
    0x303020706021c0c1203150905010e0f01120f1a010b0c101109040f14040f060605030a0f03030b1201021b100b0108071409060d090b1f140301021207 65
    0xd0304210381403542502c422110680804032840800c0c40407100061a0300b00d1080070503502400040f280541b4140040d405181e407026203030140301a8088680d09641d040100180103148021680c00f01054113003110319070401c41250140011884003422454007100108200081000425014000d64070182c010790784d2140d20041d1507100034405a15806140a0304801c800310b07000d03107040d40070007644041c20000c220042c0310060150a0742c0307588103501d6201d800c0c02c0c0c240c544802401540281512074001216007800c106607603007030b8407103030180d4001c0c0c03003010205201e8024020031079403500d00400e1500e004000135a945585603900c6082c0e503c00100e036408003942c0040c0c4005071a1030020381c4e841c04040200711084442c2035a00c2030100311803030000f44802e846417810740b41c020f1400d120b40e4140350020001c503040f030304000d240340d4149035503031680c0040c020459040c55000341c1d180c030040da000d0070030706441020304102c0c8980501240e41c43d40002c0c1d540d50a4050310a203001c2506010350740c0c503001c5030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 735520404 1250 735519154 735519163
    0x30b1e04060905012003010524070809032404060203250503010503010606080408040314070b07030f121b05030601020c030a06090c0e0903040e04081c06030c080a0320011401030302 79
    0x2c11100c81d032a00c8048a05280c070f4418001c2660030104035141036a2078031052000a2003298454500640240020124150f0316400340c00041e004140c25521038880000741890511791480013000c0202c010100750700078103007001da55400750b40503001603141e0b100c000d080c56031000a0580e4810740c0081005008050303611102842c101d480031030083c00309513998201039464001c2070720080c06e02d440030801800800c0d084402070010380c1207002260b000c165581c94030289600b042c0c000310700103206c0d002242400d9034021900484281c0c803410422610030070380480100400701c50202e005025022000032030310f038001d2000703c0380c02c00c003e401c0d2000c05040d071500310003c000414084030449041980800e1803c540e0701407a105841440045281a0800c0314040301c4030001130085403e500c3c1008055000312441ca01592000c0840d03501280c040e0462a11410000725600010350340d0303001d9114080480e41c0003080c04a080d6201050082080314917801501600d02019042d074004000e070000801c050f030004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 735521654 1250 735520404 735520421
    0xc1c0c050910170a02070206030f07020a1205120106030507020d0e030c150d1112240a14030606030d090306050a0207141b04090b0114130c09031e020a030b1e0406 71
    0x400f2101c042d0780b032101000c202d000315100650480740901c00241d6856540c85442d402c150f507401120343d460b1503562951094942054008001000030070030400302c040d0001c0f15405000075042c148128a0070f0f600003503031880c4241d82c000400194a039080c40302e031401c0c08100400342002d004800d9100500f803c681c455070103640100314091820000c00c8a00030400c01340ca0350200103120040540c1c44a841c08000407035030300c440c407429020003110605180d0300c020f51180200000e100d520b0443d150780d4209401d100008004c03601941021200c4540300e94032a10003010340c2d610810000700f54450492800c02402802c0e00181503c180c07211060074040c000444003005694040e00c40c103251000c2c003d100586945146c0180320500c80e5005202c1c12500442404611701c0c09040385411200d2061203c0503180504d1450010414030407050007402245040c6907294801c3d0360008550403c0c43d80402d040700e25510020742240500c00104036041401c0d118049100d5188074109034505003802d000d0002c040c0741 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 735522904 1250 735521654 735521687
    0x603020406110303060603061201060b0310170f03190e04061e0b0f0702041a18160306030809012109060f0501080a0c03150917040e0c1c0c050910 64
    0x22044100c06003002080324890301016101d942951188c2c000d1200301405104c401002d55254103004c07a44000e03680245100c8c10810480c1c0390254079040003c000c00740b40c550703407950b142c20000c050350812000008a520b001041c00d62140302c03820085085841c00710b440c1d030591b03100341003150015141d60000c14100c1c100042d141e103100390580d103804200491207201c41000b400078040c0f0034103015140507441207400c140420924130074170504c01c4c005070035030075050703914021041c11780305100c94400c1c20b24403d9000c52041c181008403d04503100d2244c54051100102d0400071002c3e0680c010741d0103010400000c6050050510000c0058a800d8001d40b41058030304483d00d283c40000909818001120346019400c802c100013020308607250301c00c0c0b40d01000c060f4103642e85c4440f600400140710050482102c10116001511a0704200107050f01c1c041c080d00c0205c130560180100c404c210b240c0c420303844c4142d104207030014504210b80426525402601c6510380c0c800e6001804c6408a41c021081c4400403618 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 735524154 1250 735522904 735522917
    0x80f0d080c07050d05090a031b0303080603010c0207030204150803070c05011d010e040515031014060a03021e010c150f1104080d0c021212131d0f040311070603020406 73
    0x304015000c0300d015500000d4660b030300c000c0720101350501590042c060300c3e6001d040140f40d42e80f01d884e100c7c004022416010b10100c4814010000e0541c0440c00c990812811002030010340c0078510025510b82203800042d00c01d41d5910301482e098030b5041c070310f100103180c1d10040d41e0315008a810041560b40c240d108041c0421054800405801030030854800c80850585404616041d14414000200350041907580c0f000981e6280c510f01395810000000c40400000001c02c0c0c40321514400001c00e01e018181d503000710241d070810b00040e41d4128100c0729a90402659184641ca018012140c4600c160000f900d444800300b4259203078140b03a004034040f1078403080148400d62250300034100501c958030450039940c000d0b450f4515910300ca6444040007500007444142400c20f496001c0d4100001c44241c800194000100c03150104840c2410340000d00800030382d591001348100400a6807000103242e06140d070300c0400041c04150040c60ba1180c403444c524101e4034107a480b00c5001c2c0007035000740924008501c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 735525404 1250 735524154 735524161
    0x170c010510060519092105070e220312020a0815030601030c0501052a06071107030b070f0c0515100807301e02150a0206060f0a080f0d08 60
    0x560484101c4102d99220362501812800c056a06200c0c00041c5040002c4007034001814600013401d003c511504800b800d649088a19100345000400d030b01c030300500a0b030b4004001115002e440c07607610449021a409259011a28084070408840034003030a01900c0440c444120275803282d4145e2182c0c4800071840015102d4100b0140da0b41c109220007825190f001200f4015544a000a01840f0345d50395151030000d0402c00c815011051400c178409031960202c0100080c407907118590301e40205112000d03114080c195158003802600041409061080c00020120341c42e2040e84011030881c0c1050545d86d084200e203045d0030f010402543c021078000225040414416404100c80c8216002c40b007103040c0403480494500b0a26030840e0100207005964030000000c602d5199000e006d20b00c8410340840921054070410080303c64410806051050a22480010031b400050950f000341c0c044911110042d00c0c000052803921242d00302e96502c1c003c0480c3c400d240c40d03001034250810b0307206440e102110303036 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 735526654 1250 735525404 735525421
    0xa030b0d0b0105210f340e190c0e011404141302040b03010b07020406090b100309051c0c060e01230c0405062a071805090a170c0105 58
    0x228000015100c084034100403c5640707040340c5000890744500e20310710000c464035001c050030810601003580241d00005a1b0030400039001c01c40a180802c40004200050250302c030201c8542e440e070080728030610312480440c64203540104480c028410000080c080c0000031031004000b0080f805110380410400c502140300d4003000c400703907016550105d440310030707100e41c1c0030801000d0840000e01c1c0303500c543d0030400401d0100d848002540a400f40000c6155204030301c0c414801203070382c5580204081441c1150f20030322030b070310014130020326405c1c0e14011a610794a410000c0c28190350740c18504074484000903038481d09400c1041401801d001d00c004210090a5512407402d0f510001180103905001040641c186001d025210b82c1221501a0090401d626038010501540c800903204400300141c83e42d6442903480c11020803100310102c8041c20341c051802080c5845140c0314403034024115241c00c0040c1114204100c1c43d00000d400c0860f8007a40c00e0041c0f1440d0880d442001603120a500b0b0000085221 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 735527904 1250 735526654 735526669
    0x21032212020904081315020c01030203071205190c030603020111010b09010b1b0a0c1814130312090f0203120304021305060415030302030406031401030f140a060207080a030b 76
    0x9806400410104a100307900b003200324140240b08446040e400d10120803c0c07018a940240900806990401407508100000c0d240c10041e020481c1010f004204200026600024962041c0141c00c400b00e140c0e00c40110702c25248080c81d4212401070b1070b0084c203d00c01c3d5855040082100c1c002e0300c2d28444080301c010306500f60744e421503000d600f01c0698030040140d03115030b10040c810503072400c010610303c0c80396240032402c00078900019100c8807000041805047c0307a0b584800340d1340200c0d242c20420001443c502c1000c11000030840c2c9c1c00c40b42400550818107003c0d00ac2c9480034600c400d4100b11040883c6800c00b41980380c44000e0380240724905030019414203c10450b402240c000b0000840310700500e07200005450018480c64000c1e45030711070101c501e6031002403040513600c07a4001c1e607115400d11200800f00c0d4603180340500c80d81002d8004101150520545c030304000d4021444010001e003e00c9920318141003114002d203114400203030362060100b0007003c3e0000702c000d81c1d0141b0462035108200b225a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 735529154 1250 735527904 735527909
    0x120603102904090b010303080606070f0846051c05091c09121707060f05060102070302130c0201150603060303030c050a2c10030504020a050a03031409210322 69
    0x13101070001800030a01032180c895000030000c0400d80b400c6080d80e50f00101252140cae00f22141c1034003003580002c20014151001c200d02c0e60301c280280f0121a008244444500c109024013107008011448900c1486001240c20400c03960700d003408050b61034003c1d5001064200c0e480341503405015072101c1c0e04240c400040900a100c1c4d560704100034244509400c8160007071340b085605000000c0d000c02d140b0b41141c0641311f0345008403400a80300d80103c5144041d0f4000501850454004050500040c0d0b200070114011282e03a120000d031a250000050b40105a10081b44c001070090140000d62035600d82c1003e000c2e00c0c426601407120324100d0707500751040c1c050302070010701040c015054003e03a44809800c6040c0c0042509000c150903c1101c080761310307511003940ca8400607454078100025410240650700007400c0070384500003000d00e59180217001e49a05498511540c9000441982d541d4500448940040800d01110400c6100c120f0b443c1d034a5010380c0f01f500c41e88100307000300f425180301007031a1001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 735530404 1250 735529154 735529163
    0x9040e0f060a2a020a060501060e1201150915030c080a0309060509130917160204060e0402031e0a02030303011d06030715050d110c0601030519050312060310290409 72
    0x1441040c0c03500f600e24007403210186001c51040f0030a00c3c0c0444e103140246402070036162a001000c11408050040a03490101e8030000c9a0500000004105901c0c540004070368000c000018400c40f100c803030b9003940515078009007020b2615140402d01c500089402051103220f501c0d071000d0540e80c0d280c203079a0750180c0728180741d00980340d074100b1030f904030250804454076108401303441c507425400314001d00b80e400400301b00007801803000e014803c60504d4456440501641c414030101443c043d80003da84100ca2442000c110140c404404c204078000c0102080856000382540d03242d6845001d07040e141d01030200f940031102d48210204001e030a0100e517100031742c0c40300030024400c0d50208000b914160f12240840070003690715400f07050040b8038400981600c0911802800c107952460a003d80f51518100009d225200c0141c03809001607000000c58012031309841c030400d07480d91038800007410104c0700400c1c0500d0724200350000c3c4005144e11802240490308500c0009402000e40511080783c1c1c03640d40062 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 735531654 1250 735530404 735530441
    0x303091b0a14010507060f050106030b06030c041a0c060408031e192d0902090c1615090b09060403090f0501051c06030c1d0c180d02030309040e0f060a 66
    0x200b880c1d070b1400c04924a06040c480e28050141e0303900811601820203d102241d590720040c03004541c503002c1c1c02001c0130116441c1c0d0031802c1034403100c6000d104510071440900441c0a124580d034528406842c4240034210644600d450f1a007004190f0f9841218900030100031048040ca0402c0424040c3e8098003e02180401510301034400b14002c091080b0305d000c46107020007240900c1d02e09015004141e031904040450000303150b1040c445503e00240800000303d406010000760840354994100f0015002060700c400040391a007000004e25030039102501084149003003000424000645500541c403075139903055920340c1c400c0a2807064682e03014850000d2030401c08142072032a0350350b01901d420030000b40005c4055507503407041c0c00c4145691010010540c5005480d401c40c080188030f0b54031800044402d40703441428840341c42c07222901c503c580d100300341103140b00c0300b07640f070400549100800213007080000950880b98596210240c05403001c1d030b0b101d11000949940f000703000e22141c01c1d0405507180c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 735532904 1250 735531654 735531659
    0x40e0f071818150216050c0315060603040305090a05040504031805010503060312090f060304120e040b06040603090c05060d020d05060f0a060c080d06180506120705040207110604080303091b0a 84
    0x200c2c4110010302d481e60959800744055030b8541760700001408242e120b0380050080030034503402e25017042c11001302854121050010001c00f901c40c0400c49070701560526110b980d0304981000501d40704d141350003d5402a10700750030041015080b81c902240e040250b20100201603865004655a12089400e5030305030300404002074035004c014003d4925444000d2140e080100c0c4140801d0b400c1d0002c03181528201504801c2035900b50b041441c15020b07240a84080c00040b640c600401d0b03040c8514030460080590f07400007401480090302c82c001c0600402050565510004050440a034000c0284070002034603180c04035200380740c082c1d41106441c0015050301001c45c0707000003e540c0c3e00c9041006403082e850410290f881c1031403510500014011001d140050591083d4181c022148000e00c1075018030b42c0201c0094205400040400485004503405a92800140780041c502e10341303d00d4003070b013103d004100419510404400365101c1d51480c821a1211314a81d42c00d005204d441102c1d5a070404103544c002e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 735534154 1250 735532904 735532913
    0x10022205061602030a0203012d06141002011b0302640f0e06091302030709050a0e04020906010912020f06070209041a0603010c02030f0702040e0f071818 67
    0x90042c640d0000b01034499120450700400e0075650801e501a00c013484403445200300b200032881500a649031940304106103801e202910030b4160a100c0464400c140b0811150381c03041c403d401007141c00306c11001c000c80f07200965070090040d4000c14111515540050f204c1c0c031482ca2021004030034070f0075801080440045802c029092100c45044040f52082c22a00109040190802610f584020340d5110503d0400c2000c0c01840c03060319042080c45400204241003c1b65111509000a043c444d0001666074950b144151045001544800c2d001005281c00084490203c0015481103000b6104d0440da903803041d0044840075458010f040b01c03403134044150005824400c0b00b141240d400a00220b00d0003005400207105128100c9080f202c12445814240004003480d140c260072034410fa00a110301c8005d40000f0b03443e0300a07002403241201d03010881400350341da0340c2c006140c1c0c2180a01511301051603100e041e0384039500ca02440c0051022044000c1426000388214450f0755034451002a20110766502c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 735535404 1250 735534154 735534187
    0x80d210903020a02090103110310050c030720070b03041103030f0412020109030c0b0c010c05031009150f081006050f0109050603190c02011e050f01060804060603051002220506 77
    0x10309604501c50b4425030001a191801d0840c0a54081c1d001410203a8a86040501d02480c040003503500c01e0800d824486034004e44029030341c20a6480c100312140500e0407107202064207160b00f00503214420070400040385a29080110701540c040e49480c1140d600076405c1c99928401d400c1000d01c01802000104240c40507890900140740c0305240c48130402e40c1c1c0f5160307204450003e400404a4110000c2c440742d05500074821401c0300c00b041d00b0120309600d0011f00b608a00403240c8074450b0070940740d8540070f424003941c1c1c00c1d90f40545110243d5104072038a0700c1c2140d83d01c098003402003400a00d010004160b91030300c800b2882100300144e50301c00c82d442c00d000912060740c002805950035000b00300c9502e0103050307450184915a5006500006031041c24113142280010340c5218050503c1c80d04042c050b0681201aa16043d142c450410080c0c0c1c1c1c845180c02c50041c2466400a0200d00590142452495441d00189400160421000c240c6013051003880e45410722441102d40c01081041002c4104003c5007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 735536654 1250 735535404 735535421
    0x50303130812010914130201091203020c060a03020433110a051c02100209090c090607050a050d0801090203091e030d230c03011518050316080d21 64
    0x25142030a00c80014010b40320000c0e000048400c2d00c591418010350400c203a0158000b84038140005040310b150006841c0040d0350107500c4001c030b804076042082c0350007013001c4480f01070041c0c452a41e03200d9000004000390040d0040c01c00c2001d009c001003601f9001418843ca07420302e10307840c06003002c481d0070054900045d2044008624040e0361500008100117001c40e07558911000045070010005450081c203011304002c01821051050100c0c0e025921174181403640702800c440d04c241d403204203400040b814012800018031600c80c0c120140c080040101d2848071208e020344444481da40c030307640b240060b80412a250051980031640c0c0c0c4d00021681482d000c0b1080550003603a261035111075034442a02c00e15010b4018101c0d0050801c1d00c040c4000e0003042d030207007091200c5420355041060306142081000b00c64002c00111102110483ea10350314548001d02006045031072100c0c9050b8080c4201d6801c5c480d042d41c50140150180c18980192904190221050f40000018008408800041c060791 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 735537904 1250 735536654 735536663
    0x901060c03052713060e01050105070804031707080d0b03070608150907120c0216050111060f040201030b04060801090201021e0c0d0609120207180b060702010e0f0a26070305030313 79
    0x1158220345a4407540b04c20141c89400410125809041044882d0a03290682c0f00a0400500b00401c030003013121001a81c09582c0c0c855010015900703550401c60140c0161880038042100004813028005003e60219a07001003d07415100710316951203040e41c4072001141d5000c0710b2b0110010b100d04038588076034050751000c0341c0d06101c2d00c0b814010045000f198203e898540159010281d035408680301111000018038091804411101c5a00c0e09240c507101d002c0c0000c440011080c0100f411603009030414428607001400422695950b0550a4040c042500b41680907015464549a008062031106100d80c800040103242d80300c01881030000c500020f5500f5a03c403503613044141c001408030504200729040650003001c0e11814000810300c07001c0030204044a00c1d00c0c1c602c80724101c0c0c9442c41992060b41c0c09090103031071070807003101144941411002842e4000401c1d00e0120364000b521800042d04009001c0e412140410090041c3e030f10071090101400d42e500078000a003491618540b80702e8844e118 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 735539154 1250 735537904 735537967
    0x2182d09012301021c05040e0c0703090315200d0f200c01024008060c031315050a0e0102030f040f08130303020a120314011403010e1b0901060c0305 65
    0x2030181d0400c00845d400a80000a400020104513051519901c660003240d003001107854200c0d02d5901401d0580306d440000c2c62010041c1d100c01c000030680c4d00a0400024111000d9481200c1005003206070344010140c0382c0b890724044103e003040c101c9100d0468043d003c450354070711102c440d400002880d00503100600c003564007081001c00c0c1042c0c40c03800041c03522109000d2400c900c070300c0010040d9242e049002d280c00c82d0b0f42030030400030010001407054101071b00781c4030b5694988851108501e1a410f00b940500748640089103250308110341c0d40854841d8101c182c0070029103401d69181403d0384425900380041c800d130000440c1c00f154217151203007030301032181d40361314038207580124030102da002079038015009600007820020a10050360340a02d404156440c00700302c401c484686003000c9610601410405040b442c90343c841e1503c00354000500d014255088995410340c1a2400a01d01e0b90f5920460095a1010000620754043c88a900a10b58152645400d15081000d12042c46154442d0030340c58a40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 735540404 1250 735539154 735539173
    0x7020a02061806070606052803060b0a150206100510020a0b10030b1303030b0a0e1503030d0e03090f03010605090c030405150a0b040b101202182d0901230102 69
    0x1100c800401403248500404034080c3c1c83e100c2040181c0718070941c9030700350781c0d20320382301c201104c681024003020349500200009002c2d40d00400704070100000d4105904041000002549098000a07003521488042d0250300c80d10780c4031000e011356001d500078601c001da48072104040000b0035005003a0b0740503600d02d400406483d566200c0103c2620240d0307800004202100c1003d09156041c081d040c82c01a0076078004010901c0c180c20070110001c010300c40810711040c4c44520000d598140300312040314a038207806205d2403e0000740c036a03d0743d0148000e98030450722440d1180c0c45003010300a490842c2c1c0001d0041c074082e548c50b021858540d00c000c0013218540500f42d0426011b01c0001c40040c059100c10000003407440b549001d00080310345d030455442c07280300c02d00021400503038421882082000c21050168070b0300035002511200001c081c094552000740440801c0160b50003140c1950186142080c4040740c0002c0c800780b04d08160300f03000701c500092002020380c1c2486420f20310b002c0455010703c1200d5007000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 735541654 1250 735540404 735540409
    0x40f03030503092d1005011406031e0108010608070509090d08070507080f1b0a0c0605210405060405070e0c1e0d1a1005040834030c1a0307020a020618 66
    0x130108051030082c0d042a808040c403034001048501c0070001c130344904003c5c0354105100140710740c1d01e40032160b22818000001034030800047d5071180000b041c2c43d000b8510380d612003a441c1d01a08643c010801a803103617010008541c5001450380340148043c40c05480c07031805000c0c040716441d42c010580d00610030108002c40c0040d5294004141c3c07580000d80e000c0d110541808000d00d00707a403409941c4040d41c0030751451400b24107900380d00030440e8054281a603807011104030128148402c4040402110340440401003400f00209019101d91710481c2078646007034451200020301401900e0f4a003d4840601c0f0508840328443c007603228018412003602d080c1445c03a035101d416a8001c003411170080d01150306150041c14080380c2d203155090f09003441810541081c2d091303555443c0c15104146000c00c0e818503100a600640d11a4810581c50750803103c0b11522401e207480580c180d8826558450107030440c0c3d0940c0040030b41543d001d02d01541c00380580ba040c81c5c0800a0310340009460020780f080c019403440c01d59 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 735542904 1250 735541654 735541693
    0x4030c090203100603020703020c060d0e1207030e030723010c0b150102010f0917071103030705030304031b0b06040504050f011505030c0612010905040f0f03030f11040f0303050309 79
    0x4040010001d81e0341d14045443c041d000d8919030201d400d2500621030b04000a8000c1892031503001d0648141d51544c40454540e400f501c00880341c401e0178042c80e10030240400c1100d00a01c0001d003e9118042c61483c03020034503541c1c2144e44981c43c0304034640d0485411503040ea80118035998014500340c90410b0031900c071448a020150b80c0840d105010041c41c1010b540c081c01080ba4524001c481000b0481c0c240d01c41e0450000320001400980000050071b0040002104c00744000190141c1100e448403141e18000741e8a500964080d400b140c00e0009103040180f0030b031100030301719a01c0031f500c00891f00c0d100184400383c030f00500210780302d0041c6203481411f10400d200e4004103080d90940e04414611b000241030400e4406600340740291030805c000101507021809182c111521542c6c0000c507940ca606000038181d1605400070210501c840c000c0d01450340c141c001c0040e071101a441003192141d00380c400702d201d1196118185400105810420100e40a10044c50b40629804140c40c1c03120070181610081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 735544154 1250 735542904 735542909
    0x6040b0c100228090b0f0c0313081621080a090302041e06090e1e030c0d11010506120d05090f030604060c021203060604170c0910060e150a080c04030c 66
    0x60f81010748500901d01c20344004103c207456003426020742e42403410044640c810f801c1e10030389500000409040b6000100200c0b01d20071801c0303468900d00303034441c08220b0301d5810340741d0704645140e84000c01082c5403903044103034650702d1503602c005c05c441240d90317441e06901c0e00b0000784001402108440040541c0b6140990381c0c480d903400070070b0214042810401000c8840c00c3e0045031100380b805410002d2000001a440650320040207003000c00c090071040103156200d03950080c044e90203440e05002205803c214031464052000c00280925550241406000c500b0140044502c0d8061404880300030b008034000d2803400400b401400c40312452070042490200265400c480455035400c00d01400e5605128461410031001007140ca1410b14000007086801a40601c0581c0c00a200003600e60002c10800b81c1116138010380b042c110b42c03806060010810141e4800c0001088004007800014605002c110340010071181c2c070f25003004a03910048030070303c1c0000d01e0300068080410010000c103100c041e41200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 735545404 1250 735544154 735544177
    0x12060f0a0611190210110307140c010f030507020a1103030d09050604051608100c09050907090e0c0a050715180b04051b031c05090a08030d11040506040b0c1002 70
    0x240281c0d5090b500e0b20b05000000305489407042010f2800c0103a0342d402a542e0120b60a1504920b021488019642075100ba0000144404100810709080c2c40c0c01150505040c102601c3d81e82c160b524000c4103800b82c0e8821115840143c100607040000035121000c0701502000280880f41040c1c0400710840450700c0c150002c1c1c49990000782007008002c81041589044034003540801071041c600750308c8640c2c94014040c604441e1b5119000700814910610f1140001c000040c0709850300e04107040e0103000d650007401207560318204000010402c0c5610403c030b54400800da0b407030030309e010318035141c0e01c0b80c801110803e050029120303600078503e078445100d0301e01320034001c0411032101e0400e40340980c90050099901c0300b0010707d000e00550184e8012170b06c1c51400781c0c0e46524038609501e08000700c41c984103401c40d41d9030080392104d02040580d40000034240f00001d11804201c0140c180710910410700039403003142c0e03109100b0081440500003400141c082e8110880454040c8412001c0c1340b41a42c00c403000000c4d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 735546654 1250 735545404 735545417
    0x4060b1305060a0504020f0f16060915060609050109090e0102040b0a0801080706080f0406020309010e0319090e0c1e0708042301031a0d03180602060105032112060f0a06 74
    0x951900c420103d00400f0116003c43c0b42c181d00c100080c0081c090154854510750003c60404284500e00c914a083c80d548444100031600281c5003d80381400c005e966a010380b4500840402ca40f800740790ba4000b90f4805840340038280e4a044460000f420882000c0b880d655003d00002031100300b002d010344140f0745561a0329003150305081c050751070585d4030307032007141003002d24414002e10610101e00d5035049034101c04050380d0707903850600d4280580303d400303504000b41c403000800011412101c000d51103949855511503000303542d0b8210781404002d050f24400d41440b0200030308050240b800540d01700400e80300c00014103004e0b6a4032a0200b681042c1e0000310a00d040c034100040d8100380c501002c645038001d0804205183c140d00d03440c0d800303882000c006030003042481c16103800e06003d40b00780441c81140801e540e441c940c42e140d009444203006c2c451140680301d190b280e10302400c0d2801820714064500e8002034144408415880e070320304005440e06070803088200b070b07980964a6820004000c0d10702600e454 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 735547904 1250 735546654 735546661
    0x10c020601083c0a240e0601031101030213090219030605100c1202031c06031103030301150f0504051f0f030213030b04081303050d0810061704060b1305 67
    0x50074660303c152040401400c005092460411000840403181142540d42600d110100038040c508680a580681241c500ea80c00d2a08901e05424421040318901014080c0300002810303541e880c0c40a0100603d0103010000070300e480e504c41e034050441c00641042c120400c50740d030130044040340d11001c0c0351121204517200e0000001e405003c0c090041c402a034078040d1925800c1d2000f8000e04451070b000302181400720921100714800c0090ba007802070f220f00140440c205c0c100304800100620702c0215480d2144444410b8103141c0441139034102c3c0c840c1111641100d03180030086178100411107030384e410300400303110114850b240c00c13004140710801401282c07000100100c0151444a5640910b001c242c010000214000360f000340381c108a81e405000303d0701c60b032120b180c810040e0013000c0c0341111000742854004180900011407484100346500d60b01c00e0303070b1280c14080461401500034040824254030021000b013004407000c43d031050080400040101780d140000d81c2c02c4a200040000494403007060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 735549154 1250 735547904 735547919
    0x121903180308030f1008030304030e03031e09040f021c05060d141b09060f15040306150e010501140a180302090108031c0b0901060f0306030501050c0d0c0305010303140901030905010c020601 83
    0x155017100e07040702900c484504c1e00c2451aa28840200700808002d0001030340ba85030344040041d81d00c0024404840800072200c010442d800b600411961071040d82001003408420300d5500c02c4441d1440d00d0700007920046251900388000d00303c0613048a42080305141910701040c480410317000c4c262200405402c41e010344825860081c0140c141c064880e003480818055541da82240700c0002100039145041c10310300f03498000d00580101d40c0301404580c10600c0707e401d0000e00e445c00c00f09642d0b0540e01c0c0c0b14a80d03203d400440c1c03200c4c042004c4541c0d00900700004070305580995a50705038450507030356807204c0b1030700d03079001c54042e406c2a40550b1041e44003280b500030f11001e001824003100c1d0780c00f01c10090204601d0001e45890410721405050020208c4400d016074440e4204502458011000307101e2070820107070050321603211452202c030680c5006512510744c0d2183c003800e4100c80c3c060f82d410803607801724044601c40e5806005660f0515984101c020300250f030a00641c842c4c998030340c02418266150421 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 735550404 1250 735549154 735549181
    0x170901080a050c040614130909020a0b0703052703120406030b12030d0c2d08130507030b1e010320091e060f061206040b12190318030803 60
    0x72499105050008010608000b5411340b41200c2043c680550000f80c0890081494440c880c20aa00700c0403d06020030009040d030000ca045a20a0719501d0f078565460101c080103000c0c034140100050306c01c003c0f4440c00640103480d0140c1c02c030191448890080c600c07000926042c01d00118000d406c401040400ca00c5070944510440300c0350076152800c04c010102032440d143d1264854400c01c00e0365030408141071034450140782c8407076004c1404050802d0070b0200803c03071813882c00c1e09a100180b005070000d400d00328080c00d0010803651040081c18024215620104160780003045865100500703005001e28440d1410b1042c000e6024036081810045800001610328045107910b40c0215201824084000f40781c02c040081980d462100d01603544407240002d61801c110f22455601190200b18407640610780100c0a009038401c482c20041000350106120302c0d0305200c143c03070540e9000fa0061048120340c500f0b0030186940b180ca400500c2840c0b005c540e400c5005980c00540704448080100104240b201c0c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 735551654 1250 735550404 735550411
    0xf0b030c12120310080a080706060f181a04110d1404020306040314123d030303020d0213081f1802240c100f0911120a17090108 56
    0x4a04094541401ca0740c1030b60b0340150400b1140d090400000250134810f04080080a8401c0c042036401014031802d000e1081c0c0c0010b0010364105103001c50019030a40c40d0300322101258009000640c3c282d4421201e20000d00e4071a85007a060700303050081c40f60305d83d55882000350040d840c030250f0780c84500e04081e01003160403000341e90342c50a52040070702c4050780d4001525584581e261070b00180f450800c4c052001d4901440e0200c0804054060502041c4008651000130a25000302581c4070604440e56242071096604006080340303075019414400709109800400e400000840054500a040300102e40000d0081d402004039420101903110700382d180f00c21482c14030080d088140407840b47d0680200c081c40004800900c01c0d00e245030072070f1b500311034800842c0304004601106500d850071862500c0c0ca800a03180c11362501864081240605032a0f0f1091658494025142c4c0300860a0001401501075440040003442d2280c40106000500c60f203a54510b41e900d00001d03103445682c118005018410040e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 735552904 1250 735551654 735551659
    0x6051011070e010f0b16061803080906010b0d0b03011509020a090f03050601050105030a0e010914071707050105030402120607030213050904030f0e12060108070509070f08010b1308010f0b030c 84
    0x20010041c4441303d519200c140c0781c005403061781d60716480f42080301050403520b00418090038118000202140c0b02c9200b09228001c3c1c41e000030a5030740085443e1610002d000d03a101d0044240050700c8080142d83c003100842401800004680440c85005c4251840d143d01a52450740c001841070b9944d948010034900410040d264400e40905542c5c906072a407005021b410304001d000300004004d100715811040c01441d00e10002c2102845d80d0a0821802d00010950015407040f0030b000280031001840455a9030347e004d02500340c040c00c25004681136400900309a0340500e040300c0c0c1200c0084103104240c0141c070141ca00581e0752032651081c01040c00c3e140d01032071141c0200c10030440401c5c2c000c5455074802c0f11624084283c41104400070b5100030240c0c0c1034031040e100b008008034250000245400170b42d00c04a03009000c959810b00221601c6a00c0840c200000b0b0451004200140c1c3c0d900160018268480445414948480c402821550304400341d1425a07114500e082c80e5042c24084511001d005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 735554154 1250 735552904 735552929
    0xf0405120708040302040504080f0d0606030c11030415020c09160f0c02010206270a140f0c1c0203071d060f0319110607020402030412110a110607060605101107 70
    0x342c079a00001d0045120180c0640d1b180e00008023080f40913411143d0415181d11015101c51409400c14000d203180c1c007848011034901140d40040500464003540e90b108940000c2d8070780b034200014400710701100031036202584242a803094299030380600f624070501c001a203400f02da0b8403007030000380340000d01c8040b041486aa004d0f0311001d40d0303004c40c1440d1300611510500c039481d814207000c18840416104100c000d802440030490402c26a40c2c4585035a00d002030440b00c02d90a03588900e034907030700060280c9500c0300205403c0c42c4a010072601c4803562900050690741c0082e9990001c400e00300441010b00005140035040040718508441440b00c10382c8260020150385456000004c1d0410340000054842e0074140c0c04040b80d0354584040360080c59018200b50b40f40d080600d0507082c90741045881a02003003110f0382c6071710031703240000c0d1282c1c000341c0281200f02e5440720a03060180c0c80d48116801d0756070a840c1d07400403581d80c682d00588040c3c410342c0d0b0354003044052041411424207400e0381002000828 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 735555404 1250 735554154 735554167
    0x61b080a051605040e070c0c080129030604021302120103030c0212060403020601090f0603020a06090501171b0307020307170a1419050903100507030f0501091803030c090e0f040512 79
    0x503c401514141c600800b00da4109480b6600c0566440099200051001401420104a001042d00402017010000c1c00003d20700c0d41d0300c140280400c1c42164145d4042d8810000603016181004441d010f5403505000149001511400c0b20231400003600140c0c04610700c3c00002045080c040580410102d21001074516420b055400a4a826040c0309006503151a41180302218265034048c00040d580100481000d42da0340398080c14085682c810240400c410050402241c2007550b0b00d184218441f400c01081e001c8420204c2c3c070310fa00094030507002c510040c45034400081c0c8442d0500110081d144005403582040c0c04010207422000c50059080c03501841101200c10440d0440c4903e205541002038840d2481c00101e89003070b00601650b0304450512060080c42038151344604003441d20000305004c0d580c0c07903a16080c141d410442100082071054006503000c644241d1190040c0051444e05040240e5980c00c1842168000d40d400c24050240b80c2c00d020801204122054080301e281045e6414900b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 735556654 1250 735555404 735555407
    0x8030a0504151506081005060c060f06011d04020723060910020c0705092806050102071a0a030518121308010b0a0306020a090902210106030b0f0d061b080a0516 70
    0x50581c85007030180205c2102107400c035003105511001404018000e182c0310030685c160b450796420103440c202d1103040c81b80081611075115082ca03090309916560407068114990045c80000e43c022103098580d05084a12002e0203010b584a00e07502c10720240c0141041d0520699075814806640709915031184104021b21000401150040840d001100c24410b039640c0e000040c40038044c403600d41c84024242e10401001224154031802c00e5031001c0e42203400598541843d05401ea21418001607614003d2001402d82071080c1c010325444281312204c007010380100103810b445c0c01001508032081a102007448843c9108007044640244000740c028801d0407030b0f0760080340903615140005046540c00142c080186401a0304031802082101d50855864204c840215000424030303850101426004000151a5210740914840c00b0001803440c500ae100310400c0151200070010215600394440003082e5480e86602c014109441c80c81e00c40090b18a801c000040840c0c40040c413280c1c0c10204030183c0600107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 735557904 1250 735556654 735556691
    0x906081504110405040309060f0507081c06050a0602010204050f0a0f061d031b01030c020d021b01120c03060f081b0d0317070216061e0509060708030a050415 69
    0x540c80c0c021500c41074603a400e050150780000403109400c1401d1101740800c06511503150011110070b6965070702030036034016082b140742c400e5210140400009004880c400d14000e5071040410321012030015070f1540d11000304030140798a6001502503540072038200018141304c0c040032000603045545260050500540d0304503c94140100410801150184001c58100440242c90880028112051002c03891200c1000f0580c0c190384900082c00d102007090f03c03900010b2180c2c4401003035005410040b0704c000030380302d00c0c601e10807003181000341c69068101c1814840c4180c00505540d9600420032608010350f00410382a072740c1c0441c41a5000401c1d90300300c601c09955188030f00501301c0746420000364608044139041c01d4503c40740142413050003401620364000440100c01c105200da203002c2641d0701e01090700d02206101c0e403000781000340d403500100640315400a100301900102640d007040d803107441d04070050700100d80004a41d40d8403810300050050320412402041c900ca03a09110ba080080c004103900f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 735559154 1250 735557904 735557923
    0xa180b04030c02060c0304090b1203160b130611091503040f0b0a09050f01090516030b0c250305120a1107060c050f130e1302060417010213120b01090608 67
    0x1c002e64a0381d05421036807000212040200140210707078580ba181d00d504001400c07101e9581d0300c6015210944000c403d00481a101c100f000344850100012031030f150751900c004020070300900c040d2503080030b40c00114640314111030101022003542c2c41d0f0071013606100715489081440d4410540074420440000c2c601d80e0340c00900c690004a00300f89841d60b1081c00c01402c03403844000d006000386000c0d1650b0b0001540410000744c010340072600000d846000c410120a0345000182800e80304074002280d203510344008042c1206100c1034107041e19900c0140d80b043c404800e200714002480090b1080b54618080e102503005030000f002000101400390100050f481907c000505c00c83c1c0365445140c017103000710150f4a45480703072a541a13842141728000500c0e0602401181c080101c0c03100805c80440e00a00e1034425035501410203440c086c1400710711440340c0d2104a4810f020340d000c1245d080d41c0550383e01d0600080103a0a400461000365140c01c00812205801c100035003450030100704000a00064003460 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 735560404 1250 735559154 735559157
    0xf030506130507171c020a26090f0a170a0302070b040f052106070c151404260406110d03090203100c120203010f15020c09011413050903030a180b0403 66
    0x2040d213600d40494149110124030102100340039001d0400c1070f03004a001d100080c031840c12002a64198068030215651401c0300192081003400000340ca800c0129034a03020903002410340d2031079a900c05101c404001009c8210313103160004002c000401d40c041110b04c0117441171002a80c245030403c01d400d0102109480741912803268860b0b682402d07001840b60503440c0218400359800c0380b402c03d00150800302c01000488103c0e14101d07090780140007034401c0d41d03842c5810848498658980f6111039807170107018540c0e80c014442010302c440c260700000e00108000d0881d42c660750850340e00c0d20125424203000f01c4802d814141031080d0100140d501007264403084680a200281042c581401100c2405034000c0c82c0d4040345c400000410030000f1006413a0458061840c0e2075052001102c08076110f9141400b6590030144040c014000c07204010908072510310040c00d50415017903900608000c0c0d80c01038413a5909a003001060080310b030180d00075940004104000c0e5080840c05642d8076001903030041c800340 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 735561654 1250 735560404 735560429
    0x23030313080a03021225020712021519030f06080609060604020f0405090c0d0c050a080c030a0b1c0b0106050721020a12030b040b010804080a0e01020c04060f030506130507 75
    0x1084030380294103884000070203010b41c81e940e03e8406c0d0b05002100c00e890103840800900c10090810034800260031040d608a8582c038030721751580e0b50901801c2140c80750405429401442040b1310741152000d011503c030145d0ba00843c4040c41f00701810100c4401d0340151556400101c10081c00c890f000072480d410210941c0d0040e0f994250089005003030013160400d9501418010078442d88880440c068502520802030400c0f030100310100a480e01e2040d021034101051035240003902503c03000000d140e01c0307440fa050102e012140c840008a40700d1096000c0070f80d0400b0030b94000e0500966228881c0903005e0380c280f07503203400d0242e25018641e22000c0e8141c001594065988a00a40b0900400700300c0c641c82007a070350842c8d10b1058094003a1a51900d858040ea25107480b401b0150f01c00c40d4501d0149400010203860813007607010446101807119031107410b41c820500d4404180c0c6442c41108001c1c10704102e0302400c903040d894018200500030b0300240410441c118502d011890120340481120080c41405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 735562904 1250 735561654 735561667
    0x90402030a030807091e090609021e2b1506030c21060e0903070302120a0e04022101091d0c0303251b1e03080d09030c0f2303031308 58
    0x1c03101280c1700c0c0c101400d45801e5060040340e118003144800241e600740070007070140640305c02e0040b04034007911400c41d070b1400c14003000303480d003076010300051000c81a08984203180020343e82c1c03041005041c4074101a81980e54100400c041351210300451f01030115840c09002c1c4440b900d10040c041c0d41307403208056032020420b044550141550340060300410900020448510300b0301403080e101d40000c2015000750240103a40c08040e1200750444030024035035191400405000c406200094116003100c1004226900b20112805803400d00e540c000d15152030046210900341c1070466a148400c010442a80d1006080d03418564000c0180e40031140a2040f41070442c004181d18824074502d030002411903d400c401c04800d4008010240381580c50595414142c1021005005450001031001810051043c070071080c0b440c2c4990400c42c0d03c00d0092800b031007514180c0e29140712200c801541110000c840d2100062040543c2600c44000c001800c080d5041d490001010074103082c0c800f100030070031940001d91 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 735564154 1250 735562904 735562907
    0x1e080108011a010906030f2901180602070909151104050109090b0a05101e080a1407020a11010203040503100209150301030b04062a0905010e0a06090504020f04150903030806090402030a030807 84
    0x1014640042c80d0303840864020045008c2c14000c1402e150b9800590b20100d07040301c000300c07000c0450444070281d00502106141c07141c0710b0000d1411004c21074044001411a600820072401106107080c01c140c4a03130b07501c0c0d140c44005000d00721258080486203040c503841c0700280d40d40303800e500101c4d1000c3e91182c52a03605a10210790303080000c1c0e14001407046090131b83c1780c02d80d8442403152191402d181c00700490725070281802580304044071a07500603446040d15000164035290050451041801140e0500c0c0d103510002e401c2401c942c0c203100419502194607611864035101034000c041200180c4c61455045468101c080a4024400b400941d00c0d030030410f0014200a42140d0001042e101c0c4003881222280010501aa688140b60000c0d8410400e440d940c84d04141e0701040350500c0d11401c0b24149801c0034040a900400021107481c030003400005a20303a030303808103080e03600800e0781d50701903503070031460007401d5030340e001d0f00540c05006010100801a00c00092003005150035080c007401e1a61346000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 735565404 1250 735564154 735564161
    0x4090507030206130f060c0b06010e0a05060f0d06090c050406080c0702060705030d110c1518010e0f1c05030a0902150412060b030604211e080108011a010906030f 71
    0xa42000000134861081080b40d800c020070b80f118200b92179a455603540b41203d90000c156006400001072001041d29076014521061500c003000e400e00e06615545c00000c1c0742d0b40c00c036544a10b02c00000007406500d0340c03440d00c543d1000d0205d00031304005030121b600c0024000c0c0110301815080c400c0c214007080c10701160340c041e181078a50041c18243c0d180554604162250840e4410b41c2055081c40d201d8181c6801e124103440802c034410004020414052002e8200440c014100d940c048091200116145601703004903480d41e013905008041d100105003150b843c00e001c10030481c402c90008030f500700145500c04200c9401003821400420054800c1c0001400c6c00c800c810700101840e400a40000c2d190003040746506a00d0242d40c04029460304030092640b01c0d4812a4002d00d4204989040c44520202540c0403080903a64588070b450340340503040041000d14181001c1c40480e8001d00100000381e008d024850fa4042d030019010300080314000040d00c0700b20030b40207040500d40c0310a90415a0042a403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 735566654 1250 735565404 735565409
    0x9210d2a11011d1f0c02120c0a0e010510110c1003061505040509072304081612032a020603040803010303180f060c0c15020705090106170604090507 65
    0x5000c00304115091501003010341d510503150b8042142c1e41d43c10542591403100c1c40e0b000e03150142490301c0e0f61320080c803030036040c101d07500c600380511030034046007405a100d00e0040710351000c0c0d55004240700301c80c1c0300c200500002c0e540d218802c260480c00041c840ca880308a01c0307010395480b0f4103003460700c841010b062604005d0640350843d040340345040524070065154100c4c208445010b0f260030380b491070010003210284128000e0681201851020980251007501b010764007260b485240c004d159038110491101d54041d504c154004d80c8030400e60002803600b407422070014089929070448101c043d55010707198070034820b0711008103003007115032582e80c603014060751440d142e00810b40c594030728007482d10b1440307604280400da0014103505c4004800007200d0780d164046d0703240c9480383d80380c461a2030b01c03c80b4141c081940840f1002c44c80500010141c0509a001545034220303005400200d080405010720314005901c26801c104518004401800a40c08055040f080a032030110350040a0304110b4179003440d41c1d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 735567904 1250 735566654 735566717
    0x71409120610031203020a0504031515080c01032a230d0f0b040902010503220c0b09040f061a0c07150f0215041104050406060504020f09210d 62
    0x2034200202d5440180042094074030a1901d0411240e0340b040c210100d010b031a98000102d10100414008a0740c01c9400d4100e2040d0a0000701c0e04441504c2c040020750f4240c1d2024180341e00c00d025080c25580c044c040d0506008140101e11100d41111210207084546856a0418482500001c2200c00910340e4000610368200050590790303d0714020020003450f0184070000f103079280c800040101d140c94080e051460707030165a1142551903e42000344648480c1401005051104540e00005403000700321000425400180c684c65501c0107040c8401d855001080f00c49031440d0160070300004070207401d1050b1004119900646905031002100c2ca4011170741c119800051000c0e12001e08a40c0c000b80020154805509546500100740400e84036040700b560001d1040c0a00350300a55981440e90201c0d0b0b002d401900c010407043d54460120b422070703004d40c0401031054400550944281020348100c48c2840621055864050a4880c4151207a9001500350100700202c43d29884451590107201c0000c81013 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 735569154 1250 735567904 735567913
    0x2030709051c02041b170907030c18140103240213090c021006060f0c06090204050406052406040b1b06011e06080907031214030a0506040b0907140912 66
    0x600004180551020104074442c43c14200070381c01d00d032110885400005695240d0049100e40701c0246c800c0700341c0c010480e09461140100c0000440c1b210036600703000f01607803240d508101c04801d2102c0c2c00e031a0100720600c01c14540c1f40041000950000d00b001001741c4000c55181c1609400403010003038860b00e1004000541011404140117446502803544075141e9000c40c7c41000055013000103580441c03141d400402e4028a801d100c0740c0c0141d16514000e4441c41002850f10340c1540020102e90307041d0f4041d02c010760794004000406003400302400100c03558015804a0304d48030300018600744103a00039900e240710081049085250350224041b01d50500ba401e0314899a11313404500c12403c694440031042c6004c02d1800603900d401840681e0180f40702e80060200c41d415074545000102140744030400300402c55001c84800c002d920003071070162081c000042001d0030114100000e942ca481c0d003aa20030780c20301c01880003150300301454a0310075a10034103842e25110a080081c4a501684c160001c00e40074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 735570404 1250 735569154 735569179
    0x30c151406041a3f0616050d18060e1e0a0506060616050609031801050c0d0e12030426030406051c11070b062d0409080d0e0d030b0904030806040203070905 68
    0x3d040f00038000824a400480d40d65544006c0c1541c8101660f8200d00c020600400a41e076003400c840d001903043c41c001d014048040c0c202503580c08101e0313240b00d10024031908891b002c14210203000f1411450034a600c0c00400c9400c102d0384442c0e4551030f003c0d00039442a0000200c1105156283d4140c28a454208041c1da00c3d038a440f416094072070b0301411880040407602c1c44840c2c0b066009030191600c1c1d030f6070b110040c010800541c3d030540c0d00c901c1d000d0342e41d6402201c450b190b41c107120f400c100600141c2907640c070311090089074407041518110001c14988007508140000e21081da48103041c1d5030404259142c51034140c55040c105070080030f601034000465280090148140700381c807215503004a4050307942d800301c01e5003610920031400700360301103c3c1c06143c0d0032400a510f1030517800001d1103078001c09045240c01c0300403941c14119054a00b122640d904030b80114429260103106d002d51000b401c2d07800c1002c078505580c005201080041c5400d11aa42c08000300e18582c0c0304080d000050200501400a4090f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 735571654 1250 735570404 735570499
    0x10b06070b07020c090412030207031103040f0e0c0c030a05030c0d020703052218020a0210090b012306031303030b03010c090512190609030c151406041a 67
    0x3411074410000d407042143c3c50700541000307502244a190087c0c008a90900d050038224041e50250806804012814016800a95082c00240000e08072004440304061404d81c840f40e044c000205200c80c036040c00d00034400e00b103070040101c3e07841e0140340c54110790300d58400c0c0d0140c59074014114600c3c0d40d540701041140815800c80001c1003640521030a9081065020f030f000c0310b0604030303070041c2940c00d230f55441da422416695401816140c6079a0064505000b0425070110444505840568003900e40c030004000ba0b1800c0d03020769204801152505050404100102d4490301c0003078034a4001040582c20320050500c02d40c000302d00b06000030b0003406502c04040004202d00c05a0280610440c088101201c191100040070550b03850510707043c54010680f501c1c2e1034000d0070750b54000c1c1d0900c101820300a00180e51032451902424164000280303441542c0003100d0303055401440359020b0b40c6401e1f000c00c0c4007032301f4041072034043d40c1c100c0d1a01e1414180040c4003100003c0c91400f81c4000182c00195440b20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 735572904 1250 735571654 735571673
    0xf03150a0e07050301050f030d120c0302070b1e06090106170604060806100906060f080a0e010207150e010c0e030c040e07090e07080d080c0f0c070b031305010c0807021509010b0607 79
    0x71b4204071465880c0c008a181015100c60380200c0d85000310f41035241052440b005134025002c041c0d60b50400504003c4242c45514824000700c8024003003407481c0e00740c00c0c9202c518207030301904110203071405400c42d814440c01030a810107044002220700240f40010303c4540e92900a0000307080c50030140c40141c1840c0031894030003141030054804490400384040b44081c4901c2142117014156600e82200340c8854184c00c0003403d9443e04192295002c10200000c82c04120304505246404480000e0604540540900316500749810301d040000716801074081d640d000170007101c0c0134011540060107802200c00399180c207405a11000d101c1d8246561001c4141010500300b044a000e141610b805c5030766030100320f404540c100c8004060340f0b014008030600c03c68030000303800706040c0b200481d0041c50315004110110b810441700c820a5200c0303643c00000b0443d080c0199003082d180c0f81002c0300705050544010352200d6030381c10108980204030340002c04200c025088800700349000740040d0350303580c4c2c1810704103080b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 735574154 1250 735572904 735572909
    0x202d07021f080912091302040b030907090f0b010f08180d0e131b0f0905090a0614091506130e071806080c0702010e041d0c0a0801020f03150a0e07050301 67
    0x20030450800030301040700c049803044c0c2080e20701110501d0b0030444402c00c201a540c00008207440d541c01e0101080201300c2a000794042c485800080c00d00b00d1405515206485055001c42030f4203007001c1c440b078190307600551103003010811414800b03032941e100d8116880c9096072040d0406a8800d5840b02d0344441c0d080400492010b000740c41c01c0c80c101c0e1004000d0020340d0000405010140c0429260384069445845050340035007507803600158240d41d8000040c1e100b14295084e41e9445d50340d4408101d0600104480e400e007003410344281400e440e000301d00601c1e0500302400140208400104021429816000072003c1c1058041d440240d081c0f8800080c0440da84500000c2d44c00e50178100403622600440f201ca204842d84501c1501e0542c05500468041c1645c80c03a880e00551143d02410a01f80301c14100c1d591040d65000420801c07010700100140031b05e040d801102d05900c1040400d48441d01d0b102200d500904c2e0f925150840300d00c40001ca2075000c1c0b50750000a4110b00041401722890340302004504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 735575404 1250 735574154 735574157
    0x10c050a080d0c08010e0705030702070b0408011d0d02070501121401030807030306170309040c030b0904060f1518020a1403040b04020910051807021f202d07021f 71
    0x150100e030030030b50b0061801e0041c2c00d00d000e1b01350700213001184101b0003103070320030007510546040c0ca90f41c4010404580040c1c0292806944818020320341c3c94141c1c00c06040d0081c45401440488070b400c03006900d4400c180116410045c3e04a0800d60400d017980110203002801c0d5038504030b542e034900740080c03c0d4201a6017100000c0c2810000a400088684c100c40107100d400040d43c81c00008404100c0101130700860341b8103045d07e45410f4005603130b030340d00360500c181e001d241e012400c40c00390001c05040314489950050303666880c1500f03000030000c000640ea50120344503401a624070312540151b86400c19402c0d02c0f440d5510000401040003d10040e1900451003a10541c40c0d0762110301c1c01108070242e83c02541d410008041c09000e4001d540c603801c1e60019120300640310702c20720703111903030325280e0b00b070480c09501588602c4c07048107050b2040f08000d2a6a107034140d45042484241d20007080381c000604112600c40001107150407610707900f0880d4201c550007404190391303481100034100c00ea071040d4803440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 735576654 1250 735575404 735575411
    0x5030f0604021206010303090e041b08030a0f0f020705010c050102090306011e06020105010e0f0709051207060e0f0102192901061205060303030a09050f0a14070f030b0402010e010c050a080d 83
    0x3c0455800181041c1030381d91648070068120704004001c1c07500d810041081c0e4040300402211442500a811954080c02c110000b969858201081c041c05202410900f9000c201119008079a810f83c086251029281d003484c1c50381440e0400d0034400d02a000d5010030540c907002d0032300002417030082e542e82c100481c0341c06405040c080755103200c01d81c2201d0092003001036421542c1c0c002180c1644480c02a030340550300d0b04011490b25100c0021481c0d00090248cc03c0d0a0f07440600c041c8403040d00105082d06000003184c90314209201d80700002d484040c0219000441c824141440c010080f403126040c480b8466440c0315100301001d20500d03c0110828401c420114018041000c210305990040c940300e1103028004600e182c440d003452034000d1400001c10f4aa5028007100e030380810f003003072241590540c0154551040002c06511145c1041c0161f4000e07070011440c89400c0002540b890696076000d90242031000000d0104001660b124a293740010110300504075000104100e850160919611804042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 735577904 1250 735576654 735576679
    0x4060c021201020f04090b0d12020105151e01230304050c120c09060f060d020f031006090621020403020409050a15230a0b0d141504082205030f060402 66
    0x42c00c07882000e015503100d440800007403204407990341051000c51400f41114403900351903200c48008292010440340103075150418004004c0f0000d00c07541600e20121810160742c072508041100600c01da002c0181401a1202006201c6215100c0c00d1000445610415620f18040c601162a101a0040548500e90040e140d82e6040c400043d60071112802408030409602e841c0100841d84002d188031a60181c010008222000c0443c0003400012490400030303500d900b0200c0743d0003042c0c40f0f00c0e0448000c0010038a420403600740d102810320445c0c0944000020103c1d0240c1b41e4134003900c52034201a4200e42030111070400c00100188080c52240a1f001c68802490810f0401c3c0a40745003139054407041171004020454072040b40b2180c1c3d0400000c44c4c2c0042d08002010200700c4001800e5004e603040c1c915015a0050140207101d00d20321038400e1801d109113458541e0b1000564084c4114042d07000303101010158420240000d20000740900500315060301007450315480d80c402d011913049000c0c082c04d500a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 735579154 1250 735577904 735577939
    0x1b0515030912040509070c020406050301060902070b0603030a0503070e0103060e0405060a0e030c0717100603141c1d0f0a17010b06160b070c060501060908151b0f040b04060c02 77
    0x83d24140d9100130000c0342c098442420490700c600599000366405669020300144603902440365000400c9000400350701c0d140a41884c5c030124000070b10450080c0c01c1003046942207544101141c2d402401c60820915000951004800820a5400c541aa440d409060000b030000c001000c1e4445e60310070106201c40114003501d40d03200d008a81c0d030459140c0c41154248545034140340e021a1050340c900c1164140c05c121300c080070546002e03070b0096034094200300e00c07494500024401c442d0444060b0010151165a1050041404403141c120340c3c1042440c0c0a8a02c059481c030000e201d03c0c03038009149a061648661110315107103800322015202d586403000740c84450411505031066469596132001194110340c071003180c0d06900922043c10490f1811004002900e14402c3c0c41c06842a955044040ba05103644079140c20300110f01c481003100ea41c020450380c1d28014011303121440c5040d22260329610b0420350940c0d00e002d00d4100c1d8001c0070001c40c000c504540e000f001404003600849101074070403440e500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 735580404 1250 735579154 735579157
    0x6180c020c10111c03090201020f0102030601050906090d12080106030605091b030702100207050a0201031a030a060b010c150b010e0a082104033504060503041b0515030912 75
    0x441e000203080d062180198090784122141007000015a18800f601e40340130401d010340d9403001e502003660303107000c6019540d0400c07540100a4181000b186141820310000e084d5000f600d5886101d01c1c0000380003581910341d81c48410a595010b0541244a08080d0010781b810100340241070010340740840028541c503001d11418003a007848042a00000c5180d407202c0f1407913100520340c01c00d5201e0034688605641c030920013840c50385d0040004d0000a44c5620005080c1d60405c0810440b011908031070700c1c500d581c0800c01c2030341c0c0d5601900004464415000607100d01018030409010000b1070f0114138003010b0160010303425010260f1b200b41d414150f250820183c2d45642c081c0103c02d9200c00d0a41104080080c0c110106040304030b0030750304150352562000d10f61311400c540060318240007039201420742e00400b07800036640041141c0701d0805003403010080460200a10103011a600300c20300d001c1500c034000501d000390801030301c03508140c05d2340c1070000c03225030041e0b4641d8414030078a01b040c84000072840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 735581654 1250 735580404 735580423
    0x3100905060a1409090106030510060801060603050103410f0c090c0a08060d020604090b030d14120a020d05040c141c0311013e18060c01060906180c02 66
    0x4100c14112401c09010f04d036207005003810541e41d602c2d000800440c0040100e05800980904081a91030030301d00003c2c2590000d078456030505040c0001400080e0101c44034000e80103223074550364016070a401070703da048890422180a03601000007c51802c1201243c1c501c0c44480c14001c0301d1210920805010103894111401c04410b102401909800c0e84590055a0000c0c1c1c01041d0840650240e000588503500c03036031101c00d4050381c0350450000c1d41000d02c000800200d5905211008140d05500d1141522499420b074880d01070820014104150550541300410f0160204001502d841d02d080c00200c141d601401459503194900040740f0302c0c0280984042840440c41d50485c2803455406441c0245450707010100c0e952584400c0071410204081d0101d5140b0000c5c0c406c1c032880c6081c180700545006074003141e001d801c0c02c000710410b07503c0b80c03100b900840c071082d0361103503661403114103190062005412100e001c5051180020344100030b03114903140c14113111010014000044000e036550404074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 735582904 1250 735581654 735581669
    0x1103070804020d14030a171e01211506030b181b0f0306241504060507080d060e0103021c11041a030a05030a032715090803100905060a 59
    0x40041c00509080d409400420b2140001d0f4220368100000c190954000b80e4009000803400302d414000c04048401d09a00412050711203a590030451801d5050840d050194080104450007490594050140003480c040d42141c0380c1c4600f00928400388000c1c00766032000392840031030f410100c0c020300e5001410491040901004020707003a00d2020b8044141612079410b07038844040c0c10714411945040c01098403401803226000300403881c054400b00c401c426010342c1030144a1f004903034807500560b4012503081d2412030038450344030699460b00c075a80340728403407a8200740c504141002440e1090f004c01503058902c01c490b01c440e000014144642c90b010f21070b201810100002c0030601071800c1690080070094141110002d00c1404440840c2c07a042c054041112a6800001c1d42401640d05100c5c08905d00b0070130417906404407100700894881103092101815401814035480140c0000e940076080080c0c0c0035280549920f0f201c4a0070100360014440c09803054280310000781d180c1750581444041c0c0e401e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 735584154 1250 735582904 735582917
    0x50a08030a0c02130e07082103040b040c0f0b03150105180405180304080321060102120c012903010c05160305031302030f030703090807030f020d03140406050d110307 73
    0x1d0700c0d04603071258078110143d80001e00c1c40c0480028014a00a0030f41000c1c1010050800d103180c1030000380303411505518290b02468840c012011b0094050440b0340245c3c11100e030103a42d491302e00386003800549942c001c42030a0800040021103c0d814406507205100301c0c0e0a9210580d801801035a080c4120324400144e03000203920514180f401e98000c0e50411071031910b40b104504600205451a481504458070545c000300740e48140c0028100300601c80003c01a4200803800c281e00040e41d282443c40400c0f40c40c4401142c0f24003031000c2544000d0110034041001b018660415402c4a8014500c080b01c0f80070717508150880615502440495400c441e5070090305003c40020b450484080d0000ba210840140c0501c02c100c0140c0c1e0100f0502e56265801d401a60b9a46410b103000f07010049241d01184282c1c002150410204680220200085070192055821401585804c4400442d04c40070040340d1031010801003401503000024028035149500c0420044071440644110b600048642c41d00041d032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 735585404 1250 735584154 735584167
    0x20d081312230c0109020a0f030809060a120c2d0203030619051302120a06060f12090b0414100e060c0901050708040b070b06010c030c06020a111015050a0803 69
    0xc9002d0052100c5425241518459010790b400040c640c03003e01e504203e0381d140c0f0040c0c5d05500e031a410f020024000d022120b02d0720f0385566190b00790b5002c2c00403040c3c81404085842c0e083c881c01042d56400040400034100b00c920300c650b5000d400c0e02078085800c0c680c11038889407406c0c0c00c51244046c00028105400030b6045682d844100b15444050350640580f000c0c0c80307c800945502c40b10041d0150400c000405621342070781c0c10088040c480010004011241040c604200058000c2800d8082e800e50389048030f404090000c101c1d0140031000002005070848004000070f1040c82441480440b843c0c2c2e007a511115003002c2d0030025a448860b00511035080034002c107054022440007000207a4040c100750b41000380c2d9448003e06904aa40b01d110010300010b082001c2000180350182d000c030302428030103014002c1ea18001c1c145080c85500410341c640c0024000362290140380004030701c8001c2c3d0212100c861290403100094000e03079580c200704850002001c00d0600e0165030342ca040d650702800960074100e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 735586654 1250 735585404 735585407
    0x6241b02040c02070e0c03092104060305070e031009110303070209131412070c060f0807200304030302010e0c040b03191b151701140904060e03030403020d081312 71
    0x165a40c141043d4031078544002800c01070744484921401c3c580c8409510b03490402c11103814405079130720f040c01e0441a19a500e8507070f81d0990684040d54040e00e0001b40c541d80e02d200580d03c054000c111180e05104110287d40b10716401e40050300c200d4481c4060390511503400703050590b68001c480000b903100300c9200000f06070700010240980602d014040b5904241c0e2403032001c0742001c9046074a1003100070001260342c1808442c0070b0f660010708880c42c0c00c2041040c141d030000d00d04040585070b501009004070508920f08131101c4941c100d21075441c00d480d86e8580d2707860082d009041a519040ea28016580d8948061800c0e101e6141440b41c040c01500c40b01c61102d851030891072948101320f80e0b605809206410450307050110101510f0351034111189030081d440301404031000b44034042c81d08510080103000101c1945090b41600500382c1d48048903840d5850400090448880e6001c6203210100c200001c1c10b5002503201429042c548464201cae444071034a02c0001d00300743c103002d400035203142c44003007845 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 735587904 1250 735586654 735586661
    0x909050c190b040905060415030b09240f04141006050a08030307020a020105160618050f010b01020319050702091314030f0313030e0307060207060f031e020901090906241b0204 77
    0x6c00001d1000962003070710300c812000c40740c580d0000c2d205a03400c2c104115455000b088076581d07041002c8503c010400e40c882c0d064041d100c00805c412500c100785004281004118100d032414600c4079401c2d21204000e1641c0c407070041106220703140c0301d6110354000041d146008001c0700d0240b10b456024107030458594005545950100843d100b124000704004008030388140301d0700b0702801007001d096a07101c0c0103041051801100fa144c030f207490f900d02807440703209030b0b000011a004011016888050045030040c1500c803401540806508950b402042111448404031081e50492040c1c030083e41e014001e802444c1e1b00d00401d4034074042501c041011481304211a43c1c140c900070300c41c1c503103508883c1c0c040000c6410702c00e865010320b026901519081c45a190011000381066655240070080c54040e1006000700013000408401195030015015446911030b1401e02d010304240700341806210399a91200000c140381120034030241205203c10406c651282e00546107500c249900240401c9030740d02044000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 735589154 1250 735587904 735587911
    0x60e1507030912030302030402093301020a0b0118200a030f060b21061c060e1501030503070512040e06090603010f15030615061403100909050c190b040905 68
    0x18015003000c000f651003032521080300101d10955015071281003e205020700c00901410385504c0c2040e031000c07009030002003c41003001c80c004412142da0003c0800044c1d06090f40d60002500105402e400403907010222120750003c10b079642810000c1320461031340144903c40000900786443d104000d280880d910a40181da4014402c890014006654403d0500640d0007040904405d17403050391210450100d50101030b42c8240203030b81038117102d24501c240c410030150b50b079401407095942c1e220b5441140b1040140515142a0407071071401035859050844ea2138201c130303800f22403520030059010000c51015003524200c542d1003900c1502a00d42c041080050000185586d03015980e0700d03c560465003403400348800304401d220b00e4802160550625000b1b4a100c180c6443c000110740d0410007035158802da1f0340020707641c2e8101441d142d8603503002d070000324801c40c1d2240d4509070a0400202c00d000c40810320241400003180c14544243c41c80c101d98042c06042d00c280c0603444011b1204001485083d00400ea0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 735590404 1250 735589154 735589157
    0x4120c0503070e0f0c0d140402010311250804080601060903210e010e12030d0605121203060112110409061e08100c020102040e04051507030203060906150705071806060e150703 77
    0x800721b81009410443e9034a10300200b60118944c148410765801d17208107100020081d81c071500c1c1c10012a41001c9800403020710b4041404910180c00502104906980250910b8015119196502e80c4020164501c2e03020684508505101e400d03e0301d00f2101002940041a860344002c4401c0c1c0f00055510003880403003941c0242e0b0b8041030b43c505000500007401d1641c1d08010004402c2d08007001e10a40d25107030100d02c8603540c800f0b40403154403021201520303441a006d1900d00000c2d04213000c2c1001078a0034040020704560085004201141e203900f080095400c10401c2000d103801000001070805414443e24041781c10581d0382e02c40f600056000712103a03104600000d40752a031344404c82c01409504a50a0350b03076401807141556a030b240005280e402ca603440c0303825811424410001400d6074009002c19205602a40c414000f0740401c600396120943c000044c1c030f110359568020000c580b52040c4410260794640203001c01c2050040504160a010141000c080400755565905055200210540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 735591654 1250 735590404 735590407
    0x902070b06033a0521010f0501020109050a060519020f18010c170f09060304050d02060108060403080112020112022205100c1101050705160306110c100c03020d0204120c0503070e0f0c 80
    0x109030a08041c05c0e0701403001840718000c80f03580340c41800c2c00c540e200d17034005c5811a4107006040012601c0015191602038105000040d07948912a1030200e00c45075441400041d070020036516030b00c48800740505041c0d200001c207041c2d11520340d8011544851548001083c0d41c3c6400f01322225440a50040d02c4440000e5030990702c1c20425100045250f041103030111515071081e9208803690380d040c00641e00502c2a0802050f06051941d0701910300d00050085900501e40c051000095a200d18008804070b002c2040440d911000403a50400600e1001800b88103051031790400109803c1c100c14600b00c200399a0b6078212068070655440c414075282000c45410000300340100c10101d20103000074003042448a2080188a1562400005a95400e00980001e407010300c250307042000042999840075848500000d011090b80100360020700912204040007032000c240403c1e1294003881c0050b01d58002d010004009941d00c0c1019070f100b8590180713522606800c0c02050581e225000200d401030907611045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 735592904 1250 735591654 735591667
    0x4090302060f191d071710150504020d05090c010f0f0302090316181a0a15140c0313050303031003030c030c0501050c2205100e0a0902070b06033a05 65
    0x9200352407a08125158203006852004c004a100708410802025a0040c8000c958240381c0d0084c0c0368a0b01c0607408251070785885182d100c02c141d48415102401c0c000304110b454098000e456070060070121520100e901c00c08409031850b6001d0b1003001c00c09541c66440c10f0b51110001c10403000794001c24252a014402c506c0111589805601c04901030110b19607403030f92880101050700d080da526054901c0000116540c0b5901d56142e0640440644010545428440c00b07051021120303c800705d03820901003100410b04014184000c0020325010f40114280300c4003684602c20182c0f20b200c16500450011204001040024004d00c0560758039402410034042d845041e03141c1c50309455045448443c8071000040b0110400d48149501c090124012600c0203a02e040801203008080c102c2502014024171025040041d5507203100e842c042d00907a0b0f0250b403640090f281003500f150040d18054400c1c01501108107110700080b03188208100c070b030030b03c02001d0640383c0710018260342030000b448108103040113030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 735594154 1250 735592904 735592951
    0x4050f2e1506050306240f030405150a150506090d021c050d081602060603070608100314060106020105010b030c0f0304080d020309070e010501090e0a1505090709090b04090302060f 79
    0x1540041c240380d203e20381c1d40c0c84d00004025035907180392a52800c818000000048034000e01e410b88001040b00058203661b51034130f0030603038a03104a1410355072091120030b0400c41c0f50a65900300006a5680a0034060b945444000300030444c0201e902094115080c0503040015144c00d507407003071001c82c80f45400950125142c44d410b041943e41c0340580c002c035200d607042c0107031240007460422212446201a02c4a130402c400003a45071111481800c08011485000c602200383c0d007100c130402103a10050f00e0728600d22040c00982c80302800d00c1660003651030500001000d0300d40030210307445408145155440d010141802400d1238001400a507280e11003406040c040d00d0851005501641d0003d0040200381c3c81d102d002407410105030840c6040042c03105040080d00000c0e01940c2c0c100d1030380d03840841c1501d0203072076800c0d1220290380003540c000c80c43c9043c0440c50b60421490b0f030a44251420a100c0000c0f00740c144000d8400840006005a00450019941030b80740c0c511540c00103414a903c1a51040303c069 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 735595404 1250 735594154 735594191
    0x60706091a0105030c0d0b070f1803050601170c1309051e032a072309070809010c020a030504050f01030f06140f03070503120d020d0c0804050f2e 64
    0xa1180340c03801c0480140030526003040380d1004000101ca10340316990195441041d6000c0c040c10880620610181c2c00c0c0e8283d02840e5200b0a803240d81d83c0c1c641c810755690400701d540310001c1c4141d110a502e4000d6000d245040825a4891404013910503070020400d80c14180003482c450005844034080c2c00240415001e0004c0c00707005030340e100d60045440d540e030307811000c02510203071485610841c0803480b4035012050125080048409c9008441c076580440c9110f00703a035402208840f94002084030400c02e4890700a810703207015071221b800030042c03102c21030401d0b039558800c0b5002902152040c80204a1072800d608110500d080601d40410906d0680480b60300341c2d8221b800c094010b0101461038440c0e800d0211001e42c408204500a20040b072070030b00803940390400c2c5450021004070004004100071110b404032010100102c208200200da4210003d14000c401daa04036000d005484403800304810026404a21600da0040314000d004400100000701d540030f02c00144060300c5855100c0011100c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 735596654 1250 735595404 735595433
    0xa05030343050c0f010914150a030219090602120d02090a030b0105011814091e0a0b0a1211040203060103060801020403050a1e0515040c081605010810080a0206070609 73
    0x30080c0302086064500681045110441e03e8007620100100c2000760707034801d114908440601d0b03001104034000102080302c403009840400b801200004002039400d5241c1d000f0700d10201104014024115076007402c460350b901500c680d10041e44011800680b41e085400144048801e24900500d0003070308401183c2e8030380c480e0340184c81d65240b041c010042da50300720f00c05007003804103228508600e5051244000701c810420b0107080c06148200001210f841c100c1c06c1081e00c01035554038220f2240750000212010740344441002d40990034a150008004c000f541e208000a640900002d07800740c10482408020741004282604154603440d00040019007803005001643c000c2010b800000c3c61030400d5107200000c1c03e141200c4041c90402c01c004544003251710090400da980d0165032584407402c1452802d1590b4001144501502641e40c1d0f40c2d9222940381c000b1644280c0314400c60781d803102281102d4000b20311a45000d600510100030061903d8802407104034072a00f400500b050305515080640281034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 735597904 1250 735596654 735596767
    0x80d02090d02030a05010c0f0908030412030309021507060605040507080f040c121a01050312030c22080607020f1b0f060d0216050708010207240902121005060a050303 73
    0x2004c0c00440123503c030004145849a50806401c401e14140951f9564803070340c4500307480c45400c1c1e440401010700c01e07002084116002000c41d41c103040103858201503039102c494102c0b00d46183c950300042c142400d015507031140d5000c1d107850710503544040c0d05039100c142c001c02c102c1d608000c100c400300e480c0c00000c00108240380a100204804034410500c001206c1060700150f02c0795010000e20754402c25003904480d071242100481e19128021035403250001c040401a800d500c0e452a41e0100f005c020000b4035501c5408940e00702c6490710006501c1c552a00c003640880c12280c03500c0c04c001c00c2e09040014010b0400d06000d40824a4544060784030000c90700040b208220000d0610080b0f4140f000c00c1052601800100c8021440c12001e984c2d140100b8045991860700002840301c0d1846129460f840b0410081d0007402c90203000820307010481e1503402000c0700034800c0e450303c030110301941003085c401015510054021460300c8500d803961500710030320100319500c0d540941089400342c07031951500c0405003800c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 735599154 1250 735597904 735597911
    0x130b190f0903080c0f0304080f04090c0507030201050604090b2d040f0203060906010b0d09050a0c09061e050906060c03041a031834120b04020f030307080d02090d02030a0501 76
    0x1c9240c0101001c10141c85105200000c1c4480850b50a200702229003060b03001e24806c0d034401d4285550760245c001c5a2010111510b80903a021100b034003d40107100041c400c3d0300030427640d940d00081208890020030054031203901d140c00a4031900c0448031314161003c02c9071191501040050b905540010129800c5900981404058045007010001c441d00103d0480c040c00f855030500b031003840707a400340c9540710000300e0300e810070300d010b0000510008481380d07041281d020043ea01c07019900090800c0344100f1013481d20380104009590700078152901641d000502d00074103501d50b0700802699400042448001d40401c000020300040c2c071100580f98220383c44207030b0351203103413003440341c07204520b45076030500140c12400b001c2d0816007802d0300d1f07298441404a1f041110100c3c1c200000303111a800d800c00c4204031100c0908609000d01c104001d40301c1d510032901035110300d40010070700d9220301500c0401000d211007480704001025450300540041c880107010302c041400144c00092528030317108000d85a0381d54 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 735600404 1250 735599154 735599171
    0x1140c0406091508040b06180f090f01020c060a0c09080d080106080601050712080c0f0c0304030606210609021504090c022b050f131503060e130b190f 66
    0x1088445100280a403a210f103031050f041d510701510f0b03031500400042900e581500083d581382c2d1400e00c40ba041e041c210121020a01e01071a03641d0107010155164078051059551104681405002301c410708010000074040541302d6407034080143c071000b28213038288010140003003040c00041100a100115035602c4c4002d5504d03202c0050706230329000e082c250402c0f20402001c80854040e049001443d00307145070001c1d0079622804010182e000d1503003a11080702d0b0003c1c4020f400d40c4004090402c2d40d00850042040c1662000c400c0c0000c82d40903031020340030082030440320105172a80c2c8104007007800540450341c02d00c0d8040c55034800c2d03401a0444100f5a076604405003095504202d40c01c1307484c1c0d44800ca404401c006109040c441b200c4080c4503010002c00264400446d40c4031025591022040d42c00c9580e0103444419240018150501354000640340520019840c0304501425010346118458100b5049841e1910030003c24000c1c0481d0090068641d1143c40c04441d214451040812190005c0e4014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 735601654 1250 735600404 735600407
    0x23150a03140408071e080d0c0e0a0e160201090506010b07030810240c0b04050c130c08070e010c02030717010b010329150310030605071b0206090301140c0406 69
    0x10902664100004244402c1000044549045404603a04000d00c9901e20500f0400a010296200c0c0010540b02e00411150103003625600b101c00000110b45500c07002c40240c03010300250200300d128180481488001240310001603028113034442c45648000301d6400459250b061601c5030a900c02c07450702c48002504018540c3c403240154001510401d1900502d1800114010302001428111118000800d1401040e0b00036624603103000c0c0e11864419440c44d01b0b0a103039440d03126038801035004031006541042036401e584684c407241800d6803070b0b00e003031511a44030858105610842079130610103045d8564003d0381c0d00300042401018820f6118030600e2955004500755101398005506040c00c0c0711002c07005110b10310107090840c203070680818100d60b02034005800c0028211090307190b540000144100040178165000689000d08001e00443c0c0f245e41040780d03e8200141c10824000f00c802c0c541d001454403d008000d480340003000072410031910707010325042c428242c0c0d039070100700c3c0006410000613 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 735602904 1250 735601654 735601661
    0x3050105102304030f050a03020f0a030c08130902030f0613062702070b01061d010c0b0a0e01061509080d05030f04172a010e0708030423150a03 63
    0x510003940c420720107140c40301c030140110740c410700380000424a0752400c0c2c482d2220310040d078000355007000019030003030410304005444a54003075055005000c1c6200d1001400000241c0f00440e9500d541d80300184c0203e81c03640d403042e8200c965128940c80082d180010302e0501e03400914000c00e6411a840c6145c200030301046000300840daaa072001d1801c02804024171030111f803010003142e2040b41c4040c00210000d0109009120318400182249040e80000c50040ea00c040c4101454248102d16401c8014400054030351054442c401003000c0003240000300445440d820919492410342c0c0081005919031490082c2c0d0b03000c214000001461006003002803000400c440c11100103281801c0e031071810721941650a500300148080c0c03039003600e2038000b41c1c00080c00040b0341c11900c03150741c0d007812540f9604284204004118061115602780409030381802c03008203046044944040c0114034081c503041c861100240c9131040c843c03070a03003002069242c50311034101b03030070451580e20210fa0380e4a10550300603044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 735604154 1250 735602904 735602909
    0x15010e0d05010c0e2d0d0203160e0f160e01020a050f0a060f0212010302060f04090204030308010905070f0f031508031207090605190c080706090c060e04091e021507080307030501 78
    0x14290480180201760551000e120318103088210800d84003143c0c4010030345640e00040d0094140c4146080014640000c0010200b55801448409440d44506008175405c0c10251095140c0140d00181c1c2003045000d121b241d1480441030041c2d800c00341c155110142416032402104800350131001c0178004002c560301c40c0441503883e00300214100840a040328960000502000707004850004400b05a506014152002031281000a6584984074a402056204d0a02c144a85d080c00c20010800250117142c0700840040c8a036501d004502c0700340310072009080202d8400c00d108030340310b0300851035400a0001304008080003000002600701803100801c0d041c55644030350100101030082d246c50240040c16109110041c0c9805e50300c003a0365041c00c0005114152004154510346004c90003000899a042d004946040c3c81b0352003840288424002941d0318030074000c004488054864049209c00c090302c004160014001754401c07503102c804c4642a0740050800e898031140413003003000b01945801001e01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 735605404 1250 735604154 735604159
    0x80406021e0c120a0b1f061110022101030803040c1205030405060f040909050f010e0106050123120a05010302100903030518130c0302040305010b0108060915010e0d05010c0e 76
    0x9002094804542d2580181d0b2400d6108040c0392458856030030b820030884000a0300010400c90508200e901181d0620b900c04c1e10801146007006c00003107660058a289041d82c0c01400508045455411608e000b903100c0b5000d4003070840001c080c4914403d03030780300b442d000c1c500c01c00140d07660382401c0c10041c3c08001154080140c2e1001506c034100003900210070340c1d0481d21b0903a03c0e9134440c0c40302002070049008580249801c2c038075000402042c807200143d00c2c0030b001c8203040200204024044114265102030103101e001c03a103004001022016002c1d24080c080040a00d95810001418032554070400261064036685440303030018401e5107007101c502d8115020905018058510f0b642d00138045010b18410480c0b055004240c0134042e07140d4949400060101d41c0003086001116200075000703420600054646619184609083c2c0d4080c60303106000750300c005c149607060760781e1503840c1c049031041d0400e40b41040050000201305481c2c0d1004107112a200764000f02d00721640440080c030015040c01504d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 735606654 1250 735605404 735605443
    0x30a21050c04030809010c021203030601081b3106080a0e010203070807051e04060302040f120305092b0c0302011b020f0d03141210060e030303160c0b0408040602 71
    0x74034075155a08890840c0c2e401801c0320707281c00d800001a240039000a40c00394000354880044900280080300644c446d80d02600c0b83c8803e51070394420034549095066003440c01803030411120031800c007000d041c1030281c941006c0e044142800d0541e441c41581255212801051010703080c44a00500c0d030181d500701c40c000c04021400c5151050000b07103100d00c050140001d11500140803801a008072011401d61008048115030707407656840010300961080c4030340014001d80000c041646402410b01e0b041481c0c0690740c090600d0010400c01074901004008070092a410300c1d21029900ca22061080b0706a004000388504c0600d523000140c112039450000802070b01e205400e0800680d913080d10600b031158103a841030204a1149002d803510300740b00a43ca0154038020400310300c401c0f007010000c0d20800e48003071080d81c02c0d5030310300c002d4400c0344400c500c49905030018000110303a040c2d00d80841d4216669071414024400d05622032444074001503c1c207442c5441c0003c0d0603c41103030100503a000d04103001d038942 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 735607904 1250 735606654 735606661
    0xc0f07140a03020439180506030a020a1b03020d03060506090a170106050306040b090114090a03050a052104020a050a14040b120706030e06160e01030b12030a2105 71
    0x24441c50103a000c024840c0c0da588034034a200804c3c0c404415003c45103100c0349030084011038405426030501c2c0d6a52000200a840101d8211403920400000c1b02c00203840b060541d1140d001142c042d40086509004012203000301c1c028040c085030303004450f640a6005041c50482003000202130f14815000b00740034074070411098a0949485842800310380640040f48041301450300598054a010f41c0720a41c5882030206000034001d09040b000e000d000300c0e50007008145552403014070300c0c40d0112101121504000310f44c03004640a40018a24024103241c100c5c0b07410307008983c005a9040210001110107014000c00045041420202020782801c0344c2c1c040c0720034608450082c240300c1c0726080328001c544400f04c100540d101c5880940001075407130150b801040e22134800800400c80f000c00c821051180001040c1c3c041c011a017000c0c0200e80ca0340d81c040199000d0001507025184000030035402076050b007040170380f2041c1807028241030955540c2c3c91511390550b0070001d212852201900070030720325100a1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 735609154 1250 735607904 735607909
    0x16050906040c1e050d050106080c070305071b060c06060e06030a0809040b060412170a0509040e0a140f21090121090c1806061d03070305030c0f0714 65
    0x4403603110504903408620242c1c55071048500304039202001182c551050703209601c2903040300240400402d240c8040009a0343c0d91011a0b02c11f01c156400c0b44424030800210700403074440c070010308160b4091303203406014624000000510300c401e41d00c240005440b01c0940c608201140c0680030040642c0c550703a4125082ca107000a0301d5034001d010017040c5100001d075001d15900ca40d0425041c600e8000d1049403110303036903480c9464407241680101e0300d400b140403410541e40800c03030030307a00b005820341c0c1c2d00e504081f40a01400000d05060921041a102d040128070020f00da040f80c00c2600392001001d003c00380c04030b10303609141440c03003004030041010b49006142c0c01c84191003a625800001d10b091526002c022080c00c6010814220503030485040182d1030041c0054043c00000300e4250b0414070152019940800c0221a0b180c010400041c00380c10300119406002040a48580e1009082ea8034480e62941e80ae07180d50701000882c04607401000d0b040c06020b0b07044c0b080000405004000d0450f0a10701c500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 735610404 1250 735609154 735609169
    0x90d020c040c180303020c0306091605040c0507060905030415080f0406050c04030c03032a051b03030d020c0c011107080c210d0309141902040c0c020a0f081605 70
    0x8440c0101e41d0b46403800002071207000540650b401c00b0388418600e544a013802501c451500035041d000c0e00c6940045098070350000303130900000c0c42ca030210555450404040001038510501001304100003401418042030007442041c0c002c602c91001580d40d1440d1902488945910003e40c8040c05004410080001c4000700d900f0350003580b014001601e035442d9100100700c0e002d1904040c1851805400100405400080c400fa0302c0d4a000003001482c452404000c860140a820041545d00000708040d4581c0d81c841400c0041c00d8020240e0b81403003070390b45001c0c04980000f80920316540c000c800406042d6003041000e400b100141002e81046400c0c8032030315031340300031070141d00c0d0180640d5182120052000104003110300c01e0402643d00302c0e50450340050203440d80200c00e039182d4491050514000b48001007801543d846d002c00919154030316000c01009142c04e596000901c20007810f810f0040c0d035622803202c003400003040d804000c981050300b00c45c9810018421603900c40841002400b40f81c1d02c008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 735611510 1106 735610404 735610423
    0x16090204090b0a0312030e0705180f010803030402090115090b0d020a02010b031906091403070b01090c0302031027050c041818170f160b090d02 63
    0x303042040c0d00d2814403004010005c0c00c444003508034041d82080b240b041040096030115235540c0d02152880000c00032010105203071100300072000c1d40f080d66190240c03440c0f8008504501d815400306901c80c3c0180641c0003680300d640c80f040e4059115500110240011901050b00c0f00820304c0c416020390028900fa202550804622000600740003489020340340e1000c01d0303070350540410f80340c0798010168081c0644a240c006913103540060410401410041d200ea82e46004942c03410201d001101c44180518042500420074000003031440300402003640c03d080c46021001ca8000d002c002000c0d916030f0094525810941080201a1807002810844540c101841c606491035201c0208941d140502c0c400f417820744078105000300c0c2207034900000221400303070002e1424820496080b50303604130003030020346c158422406a0800501e0080076400c8240c00000f442c270001485000307500c404100 = true := by decide +kernel

theorem cover : BRFrame.Cov 735431654 735611510 := by
  have h0 := BRFrame.cov_init 735431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 735431654 ≤ n) (h2 : n < 735611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
