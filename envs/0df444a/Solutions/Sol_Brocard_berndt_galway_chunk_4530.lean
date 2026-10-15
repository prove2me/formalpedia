-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4530
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:54:47.519984+00:00
-- url     : https://prove2.me/submissions/efd288f0-ee47-4f3b-a691-286482035d5c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 814568345 ≤ n < 814748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 814569595 1250 814568345 814568387
    0x7051c030b011119030e0d06091b030302070603020f0f0f030403090b0405060d0b13050c1c020906030c180301020d02070c0b1e0a020114011205010506040e07060f0918020a 75
    0x102c015225203030546501c811005480d0303204144109401070440d4800c001c8014007e65a030b401c541072500161007a114121211810300440941b909140c03001c3d0b0301600d801d94000c0c030007182868401e80c020350000c1c0c4180207055042c4400d0700c80c00c90140040c40e00f10300b105d4155881e0709040c60040c280c04500d41151023150010300081c040d64481d02c3c180e80e6054044600403d015804d040071528400070041d61186050810042045c5420800b005002e01d01500001c01d6401415201c08000c1740180441c55900c44003c01c08074500c83e407850050010403c0307464102c18101007910000c2d0072030b80100405040300b500401c100007400700140c035000044c4000400549826410480c44841c104031103014040080c01040d4100b1084c400d50160344034254448004c452f6503142c0f02c20b4115807030450303001c6510f503003080700040050419005103000c40c020f400040051506200069580000308070b121020015541303000604801510710910500c900ca41006030707101c984c000f008003015801080a505060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 814570845 1250 814569595 814569617
    0xc1e230907030c2f01020304060e0607030b15030c1b0f0705060f0703030905150c1b0c092a070807022b02090717090c0f0102070302010206011a07051c030b01 69
    0x24204c6040360612421814160782c00b001480000308040f1402844841e035071002c410003041000075881950b0455440c01103a0807030340c0c0d41d00c00300e040d125000e0b006508080004030040e001d5800002035900900400900f604001160351002400d48003000008465480351661061f840003c1c0400d00241c241078861500d80300304183c13808442d220b6000b00030105a61000c1c21000d00030140000b6150402d11201c03000c0905002c091988641c00090041494494803038500c5a41c070000202d0b4500c4003005000d40d03541d643e0340e94200b840142005100d500007581034614494107900302e001050540d105035002c41d2240b03214014011440f02020059003d0b41c03c411648400466600400c0070a81d4102c4007074403190354110b0200c42c1051031a10b003042c00e0229030240024440e01142c40403140800f903e0741442c1c0581000126a0b443d082d1001a0258200f071005100d105050400c10a0304242c00710707681e28100190791385624000c640008824023002c2c1c141e00c207c02c03ea25008000e1032040920701201000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 814572095 1250 814570845 814570847
    0x201090b0c25030b070e010905060a0c03030504030e030f21030906010306020a020a0206030f150f0d0b040609080a0801030501060503061501111f06050f06070c1e230907030c 76
    0x144410088450790700c8011004841c2d80b0788032808802a40d4080f00c440313400c3c28440030203401c9140c58a05180030810400000c10130b03080460544401000c699108668102e0755102a0000c2c9000f4105504000fa0300e907400c142502c0400c00d00a0038601c10000f0b04c0c91070400300d8401c1e540c00c0c0850f072100c9800010402c0c80060711000480e5410359070403200050381e400c1c600320f041c0d02d0664840c00080d0090300100030094464241d0400074421a00b0070142a81c03080c030402009205281c07600c003030394000651442c00d000300703170045c100c5a0300c80d1044d240003481d02c100f03481d591115007101c801040098a211f0052040003000c2c060039000303050a43c010002410315003100c0c1e004a180405889c1040302d280351004107950200400c0e4840090514469003600b044021036000d0001405160f0142281030309401141c102041150203140c1c106000030181410180b82c0c44005101d06540304460840200c00700f0b002c0044503882c2007070284041030724000c82080007400040c0f440103081d18141403410159070441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 814573345 1250 814572095 814572103
    0x6190b07170924071707020102010b0a0834080d120507080c0f09101214190e070305010f05010e28050c040807090c080f100303050915070f0201090b0c 66
    0x488400c484840fa8903809050b4030496000b100c01c040d0a0968159400d034400540e03000404001d8000e900a01c507041c0060700b8040d4030603d5109010050740100d084100a0181c0f58a40ca850b080b10700444684100c000301400032812030b0f801041c01d903003006040d00907103504102c040c01001a0800300b4401880e042001402c01c01c03000f896640240400124558000d074075104403200484003e1800401d02407500c4000c1040b071284100c114510710709600c8082254110b80b007184915030894007601c01240c100d4031f107009002258058200744c421000c0120018000f8025440741148140d0000303801d40c904012283da07400c01a00c40b080422044010260b5010f0440700c0c00c400f1410020042480d40351f685076801c1c01d12851b440007485010300302c40801c000c1825040f2070302e8840c5035604c000154a6401c14a000740f107041c0d03640600c0807a580703000c00000c1d018602410340050010030a0041c594240350f160b0a0f50301400c000c54200790003000d448119a0003880711406404524550b81c24001408801ea5803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 814574595 1250 814573345 814573369
    0x50a03050c0f030601060c20090f07030c021b10020f06011202310b01140c060f0a020c1504020607170909090f0712051615021207150506190b071709 65
    0xc1151480e14258205140e40c1031610f80400180403421036280c4100d070504440020b03100400040d04dc04a00034081d4400102e0007503c100c0300b035098180041040030091074010320b0f8040401d6000d100103c6807050010b1010314020300f0900429104002c003481004400c50510f611241851003040d45020341c0940c0744c480c80c0840c6c0240000080c2401c51000589800d15041c840c20144c8400051045c00b0300703404501d0314014070041d5600c3c55071340c4460000f03000303038041c3d0103c0b118581c0c0311044903945500429005d641281c00a001c041c41c0942e282c0f6241c1d080049810242510500018004140c0c100b00d049194062800e401a10240c205010416256601c500c1452040c080650444003449010310008860003943c140c0c40600a80e100ba403a8007041b020103400340540265140c8060108038001200c86e680d60010303140d800d124140d5104401000c0140c440790b001024403030001444c0e031122030b400000e0a01c41262503140d10301468010703407808103414028203541302481003103041d460324400d2001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 814575845 1250 814574595 814574603
    0xd080c04090f0902060301060c020103050109140708100f09020c0613020604090b011101020c01060618030f031b1202010b151e090d060903082715070207050a03050c0f030601060c 78
    0x2d600c094001c1c0d120080c10800b03601035400180003000003501342c0c101e003003803480c280300fa02d06008076a80d4100c138104071484039811014003064000001c58961140340090343c400d801d9007011400c1a120100600d030340700c09800008025500154003400342000b00031459001400080c5031049000d103901003202c50080f44030f244101a00d80c0000e030140da014007100d41003601090001c6403070f1544241100c1c00b0b081144221008942d030b1400c0c960108603000c000b1010307645c120b501d242c40107025030327022200d0340704070741c01900b000b00418600c80010b0780b0b04404041c000e5591b0f001094451040e07082100541200351007084482c41003141c0040c2c2071142c461060b07803e40e400c3c031158444201001007010041400c030000e01142c5808129802c05401010142c0981d100b82d400c90049100200c3e416610400b92400c01800e502242502c0f03840402151295445a01d07807040d03c511503035400100d0004406a0811950358002080700881400c0159002c004030380100e00804a5500d0210090004240040098 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 814577095 1250 814575845 814575851
    0x9130b0a030224030406050103140a03080c0a140c0f0607020102160213020f04030f11040902031c0210060b121003121419020303060316210507030b0108030c0d080c0409 74
    0x12440303031a125400c0c241c1079a00d140f803a942d1803d440c0400092000b4003045400b005008020b4802c03403000642d4000d25540360301e540c00207440f200b0124650750014640c1d44208800d1848000303942c0d040c0e801400505018000610b860011002614207103c401030006003160310500041c0b021100c0c100c00b0f030046a8050724450b01220744407070304801911410b003441c0c50003100054000100915228502130043c01040740000140c4103200300000c2da0444440650300d58080c50f190044244443d0480481d12440e00465020f12110303003a240540300f4640c0041c52228000c250600f10785100f01145a004800c07491101d1650300b076540700e2010b04440440903080101c0341e40964405031201040340c166240d9149480880c010000300299a80d0046411078000d01400f01210381c0c00306132000b80800e4607500c0c02910007014040800c1811202c1007002614603200c0c06034004007080040d10024043c003580800f5669812032040c401e40303008504c541d03500400070f014040050420007a8190340c1a81c129081c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 814578345 1250 814577095 814577119
    0x14010501110c2e0c060e01060f0e0921122d19150305190b1501140a02011b210c0e03010f020307140301120f0c080a050309130b0a0302 59
    0xa0b1604040d03030f50b445205041e910f030308208074540040e81a02040d1140c0000d100d002d84082020b807d9403000d2040c01c0b050403d845003031060b2485a070100350300c4038001d4111264490380c0515185550308c1c080b21250a000c1c0080c45100078203045200341e900202e00700015010030007880b101c0f0440401c070712071034600000c6e20380425200d0360b0340301081c10940d0034048241b0000c0700e0381c41203403221000d601c0220340500c1006400c264043d40020074034520354001c0019a4555514001c0c072400b100c40800513410440c4280b0f42d062280ca01c81d002c1c14003800786500000d05104204a03d0300000041d0258505000a400c60b0007219000c03201c114180c14800000481d00f180412030640e14510041051603065091a046001e4498240e000d18407c441558907180d030034030380d0051080da5110a0040420390a581d134000d40c080360040051049007445a0811030310240d4440c0c1070390820309030341001c40c1c441d00300041c0700c559071030a80b0217000c030510503500c100003146580d03000400615003440000c0c0944158014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 814579595 1250 814578345 814578379
    0x11030c0f0c0a0b0a150801051006080a090b0a06080105060319060b130207140d0306060504050d0813030812061f0e151b012d2a020114010501110c 64
    0x8601c01660b40f010b040141c07400e02c01c071000c024003000d4a4145840d0000900012409070500459026035810440400c22509003082141c110100a05291555440d40302d6080000c0002c82c829225422089000407081e007404402800d48401400f00351007684204034070481e00c403400e0010304440303901880000b01802e000e80880d100c00342c485178545120f0310118600c401e110000c210200b2500d0321005a0b0241d07541620240c0c200e80d0036020b22000150700f40b1080c0a03e00340301c4030082010703000d185458180b01c240b000410f1165100d800407916000c000c60f13580143c1c0e02005145412035011100e94a080511a214503000c1074000c20940820036003030748580304ca4882992181b2142c002c421216521041c40c0460341c181d5400440410f519031030f00c19460b4030102c038a401004c0100800401e00d00e91041c2a042e03801500c0d02a6480f002d55907202116003020f0354103140c3c0c0c441c000b9550000310300c0c070610085954a00405034003007030500c0121210700049503004075103441406011a041380c1404c85003c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 814580845 1250 814579595 814579603
    0x100212010e0a09080a02010902150301060212182e2105070c0c06020d02070902030408030c0a02030c06011d090106032301060801110c1b09160e130f11030c0f0c 70
    0x1006410058009050105d090741900400b8000b070094a2031008903034004034817002440248600e800580100086030308120b041c074010081d0020700e003075142011401d03a0001d031000d00042d0720070b01d40e0350105110700161700124000c003901010780d040c254243c50130040c43e101c0d01454034050203003160391100040c40040c0524284240c464004103c1c8100303e444c0e1902a5660460810f40c1c405880703218000110901c040c001c891169a01901650441d01c0c0e050244d42c050b08038041080540c0070500c08403249102c01c014580c02070040112200c039000d0828000c0f6420b03c0090400680359042840501c0420019020705104c0210030b8101e802410208203c0e034010246031b0058000c0d0350900720541161007140003e000000c8150003a50304500f00e005074040380940c155240ca80083d204400540c4140510040e541c00c4001810300b0030100e107030030300060396440d0b0221501c000c441ea80c0c644001403c001e84a8003004039110080c441c51410b100c0000c540d10b004980b4206100c40d40044d003600c003001c2c140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 814582095 1250 814580845 814580861
    0x9180216030809250504110f0403060b010c062904020c070e060609120c030f07150f03060306020a0801031b030206030f0c090a08060a1505010f142208100212010e0a 72
    0x45000a46803d001448034002801c5c1c401d4510035070901d901c0440ca00c85600c00c8501c0080780c285c00514003840c5503240c2c00a0031054000e07a05021166110002242d01ea00456000c10071440e10713550130044000102610f6515018210300592040c4080c41c0603240018282d41a19000c061920095544500240342e52241c2d0401642090450080c0c1120801c00281007012080880c01e0b9109000f81c610401d50f00c6940b84500140b01207050313600400980a81c1402c005002c0a150100b40c032601d944480060340d001c0c40c64500024003904c0100244041807420300908090005c503481340d185141c0004140d8040644014964207090021070380204030481100da51030030291030009603a9030f8003032944d221081102c0a11748541440b03488a80b642010f07881e00141c03a416191484100680b40c411100100401c17080c0340701e1941003101c0c0b124005201450040c000fa03080b003a005541c1051007007410603406498000781940140802403007030000001c07090546040406032882d41d500c00d160302001e44085 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 814583345 1250 814582095 814582123
    0x5090c040f020403050706080408030a020a0219050a12050a0512180f0717120d02180339030d1805060d0204170f120d150609180216030809 61
    0x503001d00340041050300540b0442e40640d0541d5071440d961501aa00110110340081811004000180400d0312030340c003401c00301142e4411208002100b8003d000f841242e40720586003944280300000402c03c1d00c0c0c6154035054210b10380f16051030701c03944000d8040c0c0035100c0115007402d5080300050030f6042c43e0000b21a0280c0c03c00071620045000c0700f041d83c17612004d0041c0f6105500d003002c03a00c18100c000821071158030103244004c0c50422240c803a20000d42001031a1000c122209142e907050b55001c000010b05002041c84a0000128100d03a200c481c0500d8a5800191000307030300c0e05011940e0215407400300345820b042007a50740b001c89102440425503070f040a43e105d4004142d0940c0c001041c3e0140c410703110410440107072091038003215603640700d21920b1a103983c0d10024894110b040c181015042c0c01c0e134000d00101e0320620710b1409201842e160341050002030502203041041280c160203191000e0441c440441c80d000c0c0c0309417540c140010300c14010f000e001e00c10300400c4c2c90035000c01c060311540f1b4178 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 814584595 1250 814583345 814583351
    0xb030a06060e1b1207051b060a020a0e0102010605090412231804050613020f0c0f030a090509011424180103060518061512090f010507140d05090c04 65
    0x1104030340c0210384002e0303034044080c0c41005682203100701e0410850720f03152041c41c50403520b1794610104403a01d40c846180599603111210f1106011202041032074000c501800d805038680d05040d100404040d0415030040c116810160208640d480309581d26070069003042d8213403c40041050260340c00c00740000302d940801048905261b0300d034004e5001d840d880035609000400051014204010b940080c0d401a40c4007030100a0f550903035607164010070303180502998143c10301031024611810041c800d20840c1d0300d9000060140101d660281c4d240300580011252509254189014400c52462003e103041c0038150360051800c1000c00810514003c02060134410b60321100d0314500005907004820441c04242400d1003c2001d1610b002000e10038101040d42c901c0a90b908420442c2d0000001403512400b0000c01840507100300c030b051003512035400d440082019000d03c212150841d50010100e10400030010744044a28044030222235620201d04408201c03901d03100c42c6a8280407000140e560301c145 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 814585845 1250 814584595 814584599
    0x1b0f09030b01091d030a0905030c09041a09100c02010605040f0c0c030807050403020a0303200106060c0305070816200414040602221d0105040e0703150906020d0504021c0201050d0b030a0606 83
    0xc7d00c108405c065031001c0c0c00b5200700c8107a0100f44100c1003c00e8800502503c07a2135840222950442c0700282c1c041075030021902600d040c07005034011690305822110050b5101c0409000f20b003818010742c0b030b2164901008004400003c00020700e0381c4041d50005042100c140d01244e00c40740702e42c041d500078680061200d000c090b681d18001d01510310b100380701a0340c00400307500d400c2d58038010300c6000c0484907242c898602c0241036940403a01d56201c0c03207044500c45024001c4080d900b07402c1c0726070310751544200c407081d02e9038201540c1b074098940300c01e0076076100710b061603152580c0f90180407145401c664002c0c0096100c4401240c01442d01260384202410b803540c1500c00a6420700001c03569072958807e41214000341d03290720078402552030085012500d50301188080001500307045081e00c441c0c04040700064442c5141ea07545c420b1703034030183d40401c2c7c80362944103000c1903180030342980340094484202d408104101d83d002074402c3c01200102030191b56586a14100c5440c1440030003420b43d40090304000840e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 814587095 1250 814585845 814585847
    0xa095415020c0c0307150c0515151903120503090a12031a030705030a0b04050312010617070c03080105100c0203011103090c060f0d1508011b0f09030b01091d030a 71
    0x1400200d121001403280f10501c081c1410041080b40c280e40310442818000f4440c44803c0d240541202c030101d0f050300c102c000e8204400042c5101d28010300541100120003800042000140780d440d80c01b060403420315000400018005444260004010341402da07103a85d130f030b409240d050540301c61000e005849149141c0c0d0400354158402c85080704940c02d00f441d05021a0241542c600385800b500360540c6c0082031660124004003a040c2c0d1051107002203901d02460741c21541c01a41c400e0b8840c0340490520740810304e28005445074140d1103821442c00082089281d18000c2c42130700117100306d9000d084071015104249118001c0b054010f03801030300038008804040c1d01e5a650b940211241000f90007442100c0c012460711500711052031845010460502072512000b20041c025070005210650064a00140307030602030142c100c0102d0740420410b00721000247c05032a101381d40c0c00c0c05042008525090000402c181c117440e056a55408000640015003034000d4500494040c000c1c40034880030515000031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 814588345 1250 814587095 814587097
    0xa0204030506090a02090a020a14030402060403120906091a4503160302030a110f090c0a030e0601180203040c03020a0e1e040f06050402010e0a09541502 67
    0xc28402c0c2c1d920411ba698483c00c00003240075010f002c074001180030000502c840c0d0780740301440d00315000400c2c0d5440c00e5501c0e5074920001c2c581a40010206181090820a040d00300f041030000b020041c00c1c0310070b80383d0082300c000b20600c0b4281c500015080008401883c5a542869104441100142006030081c401c940301c90f800d0b00c00381400f4401d1203140900310390014165000c41c11281e01600500341954581c0d10341510720491480030780c22201c0d094400e201691020051802080c2c26012a561403850700310080c103444401040a070b441d40311000410403250702d0314580d420608038200c016205c2d216071074076202c0302c400c40d80003a5000410110204038034592482c03250050348918040c060415841c0d03483c0143c41d100729000380071140f43c0c2c05054007150180d00810303845441458980300d00411600090311640391900000d0400759a00307076000c1400000305031b1198050403548001c040000c004e22200198180c006075414203d9036004120440410b01640010315500040c40664400c4603099035000b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 814589595 1250 814588345 814588363
    0x90215072613080c010905130e03030f040b0a09020105031605040b1809012709050c03010c03050a0b150f220b03040c120f0201030203061302070b04031e0806090a020403050609 77
    0x4440c0300100040094000130b014103420b4043c0c5464490300e2501c005c0107481c3d00d0001401c400c813a12840008003500e814001940b00e02808550b8242908150400740d0841400a0240b6255440e1030414005070fa040010b680d8041400000054050f43c8070308100d8150041c1e50103800f0150340881c1446a054441d04442c880c100e00390740d034030310503a40d030380e030502207110450415000412200c141e9150344081d5000035114900940444142c40200004242143c54985140c000240c0d100240003041850f401495003402d4110307100c800c02296440801080d200f1401c1701d10078103400041c0c21140c840d04002403483c40c4041100c1911069031145219000c1e803080b6400c40b5002c2c000c038408103000d4410201d444100e41c102c941d540f540d803242d0340150025440a8600ba0b80007404100d1048607041e140000d082c446d20940d42c01c0506e007080d02c1c015000c032090b0452201d0021001d40203002d41075006d0603d55201204030303545407064403644000c00003441581c00142003800303404100409024000b481e040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 814590845 1250 814589595 814589617
    0x60307080612010e1f11040b301003050f010209130902011b03110d0813030311040b0408030c072c060a03020607030807090915090b12010c1d03010902150726 69
    0x8420740586c805440f0344124002c4e14000d040500002d00121040c000708200d04d4003a41007182d040c14a110703201401da0f0121900750050140e90170504c200f201c14030800004241d50f800a50804100d540000c40002011005001e1181d0b5040d4400640e131180501c101102400800d0140f075940d139080c0200b041d501c1020150003840b840903071409451050244510450703000e41c0c20111004941d070708034040d003041c4040f000c0300c4006000101c2c00c2c1000c503005000401258005664a504055080c3e0400c200c41e0300041c3d0401d8038240d1442c91070243e030380d0f10306408450300c001000d507910f9000003561683c0c00d030006500b000021407510304041d04402c419000c0e0116803103400e110307913a4091840c29140f050a600c042e103c1c0700c900810000d1348a41140310691030003400e444a025480315481d003180c81c0c0310b2266000420a260103000e001c4190f031110660b00c01a0000e212401c803a4012038201054218054130108000a00009002404c8943d1401031100c0d00324030208251030880700d2458001c503e0f103032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 814592095 1250 814590845 814590851
    0x30206070f08012718110a050d1202010e1006090e121b070b0c010b09150609090411030f010c121406090907120f0b0105060307080612010e1f 62
    0x103800d8038012110035095490503070710142180c0c20100f00d158000d10038030b13490700414640843e203400c0f00b585010f5100914844110485082c059082494401e03120300e1180740039031072010050200743c6403002d0f0446025017109881d4240e18502e0000c038014108040340d01c4941c040c4e880300ca419200940c01040846518400501c000007000c83c0745a150000c2e9101e60184000400c500c00654003090f8034410f5410383c580503a16040d5071382c0903100d0141c0c410f11083c2101c2c0d64903500d5002c9490500c00d096040b0480f869808042c8002ca00407800341c0c0304400265129203551000503007000281c8106018201c0c1c060103071040302c030240682902030440721a031800400c04888c1822000f44682c4a1b544410304107030383d036041907140c20040c020b540741c1c00b400000c494000c484000c1b1f4006030b40e64403a07a00728030070f42c42c3c09840c405c0360500d95114001a0001b51043c4400c10a0116295202c0c4086070070610480f4440703401045054564010300c20115801c071940690034404150180c990b400c808059800a814 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 814593345 1250 814592095 814592101
    0xb0a0b0a090e0c2712030c010203041403040807090207062a090828020613030c0501030606050408060708101a0d0f02040317030402040f14100b1329030f04030206 71
    0xc00750343e000b502c600646a0206602c44581d42a0310a507140041c0d002408120500c1704000109040d41d0005125100683d000004e00040200d0440200104c4203454069402c041c100140f141c1c40390380e5441154071464020a82009004031580056041c1c102c8060540342c00c40c6004001d40c1c0114904c04440200e1440480000d103e8030220b45550050b1540d162004d1000090581000c541031510302660000d1042c450b89000c2c080403003050001d10302800c030204111745880001404d03a04540c20841c10400c05001c02c01136600f002078041d402400e14100f0440c0d80d519068044041d9005501c4404016102c1030042d000c03008000040c0000c00d80c0710403e03c04d20803c2c0051318180c0c42107110041121180020380084130040c6809190010710040002c03c8140046d4003807800d880400c140c9006d026058401d000700c0c48601d20100d0020300c1794440e044c1c01d08403424082d9415845c2032140c15030b4809104082e404400c0b01c101002c00440003402e0494032824404400ca52005048800714007503c54030b404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 814594595 1250 814593345 814593361
    0x14030606030601180906020708070c030b06030a03200a23013209010e1c1206030b0a0905010e0a0309030309090213120602070c15120b0d060b0a0b0a090e 67
    0x1102d4181c82c100d0104588002c40d107500c8100401200c2ca003078505a07821322107400000d00000080c0306d010f000b4280313548183d080d41044000408051b1030288243d1103490302c040029044100240905800c400c040c64010741e2090050034681c0c4100004c101145038170311241c0340896041840648601e0400030425100c855612201519407940c561500002221058239105c0c14003698903400310340500040b41e030344989c45205207800032141c94a03180468208420402d140d10103649104950403a01c280011859500c4400904001401d180c0002c2d4581250400340030003500603001d605010411180c030011745003402402010035000490004402c020000b800d00c0303003170007941c1500005c00101340c0c40ca403401403c040990b0f100c000484603990280400c01c0862869000040180800341d4060920040c148000b00242d1400072810501441d012468100d40c803421503041e40b140e44071400192224947d4001140c281050384038520030100010540c0e40a5480030701d0408554102070841c02075120701d51 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 814595845 1250 814594595 814594603
    0x1506020a0f02040b01170411011b03200304080601030602030603072c07030e030d0b03102309160602010c0f03090b04020d060f0603030305150919020a0e040203011403060603 76
    0xc001c0c2062680050500161400c4d5101103007107541410400c40c00e140301c1e141c14100e108121000e0f00e0207404217040b140c01c0d58101900c8108904044615043c00d2506e5038068180c40d11000074a4080710145600b80b2480404c00840d0b010b400c000084681070740c0d4a01e0000c2c00fa5204581560107400350240024851403540340c00e0701a00455034040c2c141c18900000b20144005c002c04d9101056107503042c0c40580e94052008000b170390f0400c84082181e055400a161034080e101c248000880c1c500700c1c0341c0801351400c41190000100000031415a921840580c82c0b81c030301e0a10290031480d0850000088071601540020480c1038542c0b141160003003018001d5080f10743e1200046c054000080c0040c0061600010301c0301c0720f5101d80780010302101d4000d5210300b141c41036041100403da4880a2040840154880034490901214003040710301c0e00b00d001e0101300b80080d0020003402d8010a8407002c1b1402100e2000c00800c02410840d00e0b5a0f56000d240189403026052502030b021700800f0480ca410042 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 814597095 1250 814595845 814595863
    0x7110a0815060406080f25051005030402010906182601060e2d06061605010216060e071419080a1110080c0f0a05190908100902010e040b180406150602 66
    0xc805032004444202d1f50400d0344981030400303a941e9031380c80d0f00410256124105a803a082076a901d4a0704c1b85080d20025042c0c4003241c005000744a407500a440c1d0020b1400d030313102d09842c92078062490300101c11284100c0802e01c1c3c2c0c070070403a5500301440410244100c02d0483d2060350a0070326856072840d0f049508540340385007086500c1a4601c000042d0b041c1c18980010086c10226298041c0c40241c00c0c0c40e8a401ca0b0815025074035200003503a00401401410700a161726521001c0107801183d15200528152010844115026251010146100150124405000f0403102082d1141035001d4900203001440304041c80d4821100d00f00d551407114401e000d00351194403007484651410203c4501c0100c96046280c02074200305041200d500380101d000700d20440020180c840d4035415007007001c2a420301c20b21185076228103146c0301e01c00700581c1c0c1c020410210050150b800207000e00f045000300c0c0e842102981c1c000202028101480104070f040d90203101d101420414000150340c407040304903141c01521f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 814598345 1250 814597095 814597123
    0x6050a29010905100e150c01150e0609060a09110403030f03150513020d110703140c0c040b0a09020711030c04090c03021e030703030302040e01050901050607110a081506040608 77
    0x700c0001d10541c00c00350a5003003070151601745090103070920000649841c0d0207911405440310082030700941020f0900a102000344440600c01038035040c10394000e5284401062140326100902c007240490301c8079020803000d40001e020921000d100400114940d070f00a110450018072880e000501081c400d1080614406408004040741454907080280079010301d000d491845a08016048503152503101d68030f04a6211080107445081c5424003070011b050b0802007102010041080b0499680d02055241c150740003241c0014240c403038440468804010360700b29008862000130007209114603048601c50f032407812021100d6200511003844160340c000b000043ca03010501c00180018505159002c100040c1850252043c0c42003030000707450005903500517008030f0b900213014080181d90020b094050301c405d81d00e411035545003001240c018031030b40e8006425840300409042841c0da9040b150802800c0f204c2c02c80300803000110748408824001d9485038407461904200268042e80458451410006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 814599595 1250 814598345 814598357
    0xd0e0d12080405030f181c050d11010204090c03020715110a0c081228060609062d031410081507020a080307030f0506030109110d020a0306050a2901 65
    0xc124152400e490240c400c0ba07142c041440000204242d0001400304100d0249811558548203824000c2c04410045007960f651059410300001c11030002e0060164180d03031400800c0101d1040c0124020f00654209070100e03418010360000095040d000351680300c0c020414202d06d80074550a4030100c6007146880e00140c08140460342c0018050b22612402c035009005072440d15280b020130882d101c204694189005040c2c00c64000341300b00300003203041481810713102008031a08000d009440e2058500c5008200700507002d190b03010002005000d280f8030701c0c1000c4a40c1030b1111304402341c05040111480b099450104001480b007108540f011400c44e50404080e0409814001400c00050002040c6000350300c1040002000101020011403181440d9a0300045440d1300e0307d010001d4820140c021803181e0b04040c00140418449500d50058420413035643d4124045880401d00e40082c40c0d10141c4150310344000c001000206401400300e410450000289000d403c505c1407420503a0381e408a070008070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 814600845 1250 814599595 814599623
    0x6030c030d0e0d080c060108060c180d030203070b190e01091a09071d151801060503150901030614062403061224060109180b1906020d0e0d 61
    0x10142c4141c601c0200040c0200c3d806030015241d4a460b644900340403611684a980104801c1070144201ea81000d00404d84a00d8080501710146204400110841c03007082d030070910700b08050003041220406584072102100902e058240001d40c007100100002c0198141031a404a919041c481c9a2000c1d50000e034180750b154600c00d12644071400200800001d200d032010200c3c1600303d00f103d03001c00040a41e50201c4526101614603420404010b43c00e0107000300511b690502030001c0d05c0380381900c8640c545582c0fa036461420800503002c50b52802ca40040010307001000f07000f06504010340300206141c6400d0651038040c1403111a01c2c0320540a4a445508020091650340080042d604001c00038050702d202044110030a0801e00c005503080174140c130404404440440c203105075903214009091104600c0d15090146100b804041504445c50707a48a16002d8540d50790001d12050302001c0342c20010781620f40030061342c0c0c0c264442e80b400c04504000c01400a62414103a540080d540c4509207008000f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 814602095 1250 814600845 814600847
    0x2016090204240903080f070c090501270f060b04050406080c0928060b090a06050a2a05160603050c040f36140603011404331406030c030d 60
    0x110955140c40400400103c000046194400a4050800c0303c10480744d8550316454913a540f0419a4020440141018010044070f01d0306444070740014584071000e8000340701c1002d4800145411188000201d1605801259007141c6130050410303a00141c2e001c1004d00e0b12902c0450303075003401d0002264480c0666001921010881c0010307001c00200407000040e03581492805c0064410b2500950940040401c242d41245800302030280107262500340a4582048907800900790708076054040d01c440c0103228003042800e010341c0000c8000d50040155003150b50f1031107d900140c015885613100080c10318011410540c07a0f042290308446c030b101d4a10000c01c0c138100d640071048010900040c0381c14001140d1040c05a0b818000d4880418030303402c006030b45076080c0c00d000c14201010308140c1c0281c0c0750110320081c504102c0c02c10342d08140c100e91868a011440c0c482004000b5400c2443c01c3d01415207902d10326a45016004441c075421940d1048529031303100014556a41081242c0070f0f416403002030498803503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 814603345 1250 814602095 814602149
    0x10518070302011808070b03060415140d050a020d060c08070f08061002030d06060e1003051003171603020601031e170d0e030f0415090e06060a2016090204 68
    0x68106a4013040034265584405410b1041c41c0e4031004040000004001944c50a8030401420800c1c1003459100c007414000143d40081c440381d00c02d8001c0c05800d02080900c0403c002400c03003150700a12203c044105454008042d0111000b2311001c40e1007040400c070a40d010b455612480c0c10b46680d1030045907101e404000d9444420344400301540400c012254880d4150300414004e400580c90f00b500c00030200041c062620380c0480e01000301860301c003d01c624900707a801782c40120b0f5040a04000501c80071071403444140300e00c03407400802d002e040081c10105500800d102d41264018000790586000c11102d80c0014556110001d05846201c01d5891072030b0301c0030740980580800403200107810381c040d02a441c9180d000d5090380c030401030089400c20410043d02e0400451084078540203230360f507140c50303500340b004480500a1441901c0101d40c411172948680342e14241800080c0300740ae0f01c1c0340b440000c00c0e203d141024881c60307010101d140200d080c03030441c02103030111a810206000ea071020b4600c03084032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 814604595 1250 814603345 814603367
    0xa0b03040b07030c0507021f0207080d1b0212071d010504021903050403090f1d0109061a092b051c0c1112120414040c1e03062601051807030201 63
    0x2030020070700054007d46c68540342d40b40c1c440300241868440d40c807002030113032424025501040d6250f001d0310402d08080d601c501c4d40c0c0444580034024603c180c01500c005616648800901d01e218800c440c00080c1c0700c00781a0100c0b002c0715000e400c0c240c00740d07281c60a11044c2d110768070003d1410001880b508201503c254407440e44503010740f404030902d903100c243c88140581039612118082806a003003040001800d1400360040140d20b4007005003500c0d00490502c4214818000071400b2000704a049503900e4480780c6481400c906041c10a041181c400700c9494044411801e076030710310030b07171868040d51a00c0503030440040556440d00c04046585030389241c0441c07840d14101c1e13000011040f0082c0d21103400c10032090300100007130101d91150f007004500b4404146006c0464800da05020b0a940c3d40c0d03421500c0030380610760f02480070b10b070101404010b0b4041c116651140c549600c2d01c0c40d80c000040010741e018031003180c58400034030807a2580302c50a0714000104043c0b00030f50300030800800c01503004142e4041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 814605845 1250 814604595 814604597
    0x12060b190c06060e0115030e0106032604330801030c120503070605100314061902030c07020d0c06030609050103021c171216110d08100302031b0a0b03040b07030c 71
    0x80c103d500da1400c100c000b0802c0c3c0c07050840781c1409501c18840c81d01409115030804400c00200302c02442c50300c400321516550000c4498444403540300001c0306120710116009040d0580f00d0903118040301c09941580c0c9c2400941c2003c48280303851800b2031620540c0c205040b250001e00014040c0e00b0524040316040312420100d5043c4002c02560000481c1402100e100e00556040d07400c0c22072842c02c000126044811003100d250b0400c83c200310a00c83c049459051100000700016100c0e92218105a03141c8194240a5808411203c28600701312800d20410162042564280a0241c0d60154034041d502c0a0200a500c881c04100c50150b415260300100c1040d0f010702c0308143c4080140d01000b180f07a2041c1240e03030700d014000080000e80c0116801d038442c40c0c42c00e85048101130078040d40d8035440352001e800e000308001544002c11000c1c140740314008050750700103080c1c0380558194039412a00c80e27404080d5034012900c0400010307074032403640c041c1c0340702d039401141c03071000c550301c07040110010401410030304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 814607095 1250 814605845 814605851
    0xa0e01020d09080909070f0503160905121e0304060c0b1302090108070e130308041403132607060f0c030c1401021c051003020f0a090c12060b190c06 65
    0x40c200701224000c409030a0b0150009542d00c21800301800003e960082c100c0e02071000a12007003540a5000c0103c4c0d0b40800421155488081c44100c22580911940e03c1258032031a040c4050002c0d21000c10700c1d0008000107a00180403400440c1900e03241d000e50322501c4045003013130008030080b8020490403507009003900e8520070003140030350026084241c282c21079074181d4000c26080c41080140c0c00c035150840c04a4411550848003a58010514075008000610180d0300058000300d0341c400308203950440321540d2038003901c2c903212140e4807500c03812101109450b005100751100d1901001c91348006a51f0b036070b5a04900c42c540741109071401d089144044040112055241c4003042005240c0c034081d10940d400540e95000003840104d8040b040510032180620305000c2c050080a034a6015084903416507481c003060310303843c0c00240c603d070561740610040c42c1030400103240b10340d20542d00d0800e03903112441001086d07128106541d0701c2c000c0c8201d09a5041c441404120360314050300300d0440301e0380710350008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 814608345 1250 814607095 814607107
    0xf06060509011119120e0a03080d0c030603050d0f091a071b08031c0507080f0a0c0203090402030a23070909091e060f0e03090307030305090619080f0901140a0e0102 72
    0x110004c456000016207940c0041c19144007100d92011110720745080449480903068115100c02186100f146c040f011019a2100f41e070407514042c0e00610010768004d4141c461071421180e000c0d02014182d42608001000088081040081071104905007980380001c6d40c10301d4850358034603119054901010400003545070740050252000c10003490f041e5102110407070104007810384401a42c2c1d010b400c00c0700b400210300c204010300700361505040d03211078564030100e100c00107484141c0c2035108000810360414000420007a8001440c6c004114640c00c22809095600400380b501d40d90040a0710b05a0006201446c208040c82c0650022040710740036000d05100d456844154184180c0484011200f83e9291a000c544225941c0701d09005608040081c2d4034200e44a00040d403680c0d018040201404000b01300088a40c90343d01c241d40c95401840014076203890b02c200050140c500031680c0142030f444c1d0b0b400080100f5018041c011015007400c2076580701d5180c281b0580c000d8002c0c540303240115035080c021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 814609595 1250 814608345 814608373
    0x12d050937080a110a030c08160c1d0603060705040e0c0c160f080c1302070c0e0403020c030c04020c0d2016051306051011120c0609010f060605090111 66
    0x400107041c2d01c0741c00321507510503c1a00261076910040caa003078940c0c0202d00c10601003034001c40e104050985c0200c0c1036076036400900300b0030740146a508025204400100c00424650030407460703140d04403001c01c0142060780d60399040650b1458100c0d4000700080c000c0c4010000303407007154040b0381c0140c1400040e80c107080d600b264052400c071401018031001910304004200c9140880084c81c042d00000000d8a10801076401040c02d04500a0700308080a500140d910103202c0e141140300080c00303070303200b10300860704040c14025503401809020034803c1c050f00b8450344c0c103460325208680040e00214080c00c0610343c60f071001c3c3e805440e8461904002c1c45c074101c00441a00c0180701900c044039103003009400c00d5041209120050319189030318007009103442410700c0799503501b800b0b9100c041c17850f01e080307241e5800740e001c00c82c04e085016501081c1c04802203000e004806011034018880ca0303104000f000341c004065008419920540f0500011600810821a8a504c1000f2510700305640608645a0201c0104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 814610845 1250 814609595 814609693
    0xb310c0f0f030b190f020310080d0f08091216110103060e0a1e060f030327210f061a040618020924040303021c051812012d0509 56
    0x41750324400b58004100484e44240c440e84d04040d0600f40010a16100c50000c06000c06801d1340e5031205200d1450002203905008001021416101002e03070b507100c20b810b5a8164483c4451001241d44540104108000d94443e1160070111591101c4003081a2540107002000301141b040002c288030100d1421990360095016260007400c050480070304044c5542070050034108540100d048500807000301540e0f44030103240031010341d51081000d030240040c0c0000f000049100400003800c021386000003400703202c8160320844018041602060381715004078100700440d01c42c4e000344240940107800f81402d034140c940c0500710715900900440032180071849044800001500382d0407415034005410701c1090750600400700c5200c018098152030819081c80030b811406008001c00703030610705c0717042081c80e0790750740f40701c82c4104010200800c000c0c21030100c02c811a002c10300340400c04007503000c9402a241c0c0c041c0b1a4a1042d190100074041c240c45000040307200c40c843c6025110030b5201c1d20004408054094 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 814612095 1250 814610845 814610861
    0x108120a0f03023a020702090114130c030c200622050a0602090f060307090303050304080715050103022706060c01090c06030c09060807020a0b310c0f0f030b19 70
    0x10001e003125401d2504c90b409210780c01303891003081c0c0c010300c56030005850b9410b06505440305080c4105400c41c085000c41c20940d001d072140320071181022801148960141d0040c0350034030580e41c07030011040c40b2420300c000400036030008a150b50710040005001a041c03100c078071781001d00750f250307542801030300e8440600d45241c00e242a07441aa00003004c503a0b41c60042d400700907040b42a06c40a0852801260103440d06103207200140900400000090400402000710b40c40a81d108500c2c421260342c1060790b10083c08240000c80c010407200c00384480c1d5450380400c10140344043c003085c0207242d49000a01c00319400503c2482c20300d64075244842c00040f0405e984030b0103440c11381d4001507042410b1310002d09011144e0301c104240038500742800070141c0c6c085076103003920341c020344c01070050784075140c40d141e04030802900340d43c0a0100e001011442e4407034110400c042e074003605461300002e03150403041c040740601d0300c62250520000481080090b05188109601800301d149040d903403561080780e030094502e18 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 814613345 1250 814612095 814612147
    0x3060f042004060f0b0306030601050d2102120a020c01140f093006071b032c0405010b040f09020c210d05130b100302030c01030e0a050f0102120108120a0f0302 70
    0x81b0400c00c6904040088078010070040743c203001a0000c036101c0e004092003c4903100100c030a44010741019134000c10080550303400c031818413035903036094080013500c030142020081d001484540491003601003800645040074a03031040185400d11034002c0000400b90420900d174140400d46107214031300705910f642c244803003909001e48502d117018280104819150312400c0c00e0174608034030000100e0382c0716260090304440c8140c0c040700d038600011000c00c12501010322651240c1800008a81c00011401a20844002c0ca07082c591150300c5110100990040d00c079110000e40c04960401004010034030005240800211003610303004102d0081d0055581c200c504000e90341301d120900c030801607014203950b40700305d18074005844981564002034990a20380c81141c101512191900c0703000005020902c82140d014017200c0c2c6050150248038041c0d04804ca804403440980d800018040501003201818000604d109518000c01081e00761664000d9080c0c42003019401d0081203d4250302c280c48603141058 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 814614595 1250 814613345 814613347
    0x120301030c0e2404020f0d0c1d030304052407060c0f0e010201180204020306030705030f0a120c030207030b0a020f0c070510091a0a030e0a06060503060f042004060f0b 73
    0x800240540800000e808140108002089001d034a0300c58220b400010f0740844015035110021046021140a8041070314031007442c04104c501c0b2541c001041c80b000481c0c0450f810102000d80080507100d00503481060b8000030348240309030f00c44c0551003605280e20310080d1a24186103c0e0780311365045404016150001c0b0b804a039030154110303000400511001e1091000340710540084a045080290541e0020f00441e004408030329a030f602030124030003403c0c0281c01c69006030b0441cac90143e52000341c50703015980c070301308240344400c503502c608140fa05164050300100410741c40c540d50070020702c50041188030314581c244181085040c60900925030521680300030620170f41003600b0004401040c21814003070050607481004038090b070b007400f000710300030303a51400c0e840302d0303000c0000e42c0a014a4071041d40d0b07901605001108000e0a6480310043e610160115604ca6540520007602c2d820306540c042d051078420b82c9120b001d4281089401ca041c0d90103040415803942e20001164143c0c4540c00c034400c0f0b814 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 814615845 1250 814614595 814614599
    0x38070507092003150d0203011b020303010e0f070c0f0507211407080d0c0f060203010b070b0703050618060f130c141e0706110d02090405061e12120301030c 68
    0x2c5800500c0c00c0b002a050000303481e44c141008240c0000c803400f051507000311001000d0b030303003036540a61000204a502d04040c0c01810b22005000351a64824020501c4c0c00781c2c604045429a0040c2c0c15062240310a9200c3e005c0e43c1c440c5841d0312041d925207034400c54040c0326040001c1141804203951608401e204103c41c0b55007900d5152001d141c089900681080750721040041100d09000a060030400c0303607904051121031703900d052090703c0309100d41001c4e00c580d00010000805541410003030901070300a43c00090390b41c40f42d02040302a01c40550f0000e5000b00040301400780150890b64040d000a40146100996030342100402c00515510781b02940180d50340c000265015009442c60484031114003800386003050040740c80c1c109911010b03e8130486200440d01c0c4003008510f600c4005400d03207007240d0a440e40c2c070401049020754000c0070028040c904180c08600c6908110f5028001d2043d41d4480d00071201562043c41440d13100081079043c1807203188800340d20341c07840000641c0614056000d280401e8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 814617095 1250 814615845 814615871
    0xa030b0306090a0b19060b030106020a0203100506030606010e040b030a060e010c020a020a1520010207110d1a0c1614010c0801030b01181112010e013807050709 70
    0x140d000b81850380a0b0031010345200040c1c40c003254507502c00000c01056002e40b203030700c41d0700c0d00401154120800210001000ac1506034002592080d903030301c00c5088901c80e290030048002980c0080d030381d03541c040c1c0c0040041015507002d0300c894a020003000d840040c400c00c04c03800007450007003002c0c01600c20640d1403030f0014444c030081c000c14808042500044c050a805640030a50125051003011100d4845070450401e592003884503c4128822031014803058410009142c001d500c00350040f01c4030a902d881800c400d003030201d1074892182e0400e00013081319400d4054405617400c000c000c481c50322400c003e446c034804e040d40f000100450080441e0000da0803480321150031112906144028441e040004000141440000d281922099050b40441032450b41d03400c40501081284060311100208894041d1a0000140350495000102909480e6600d1040c9801c15245140017105500c0d01c20401014546174200c15070b40a0444000c40c2c600210380d180c2d54100034194000740c61103034844050344030340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 814618345 1250 814617095 814617103
    0x60c0d0c0b150a231203031e1302100e06070305090f04061a130b0703110d050f1b0c0d14120a080103060b03161e09090201020d080c07080a030b03 64
    0x105481945503a0441e00100c001044440f09105459041420010920101d10054164807031814040c10720022207280003800c1c1d0700ca0b08103c41c001c120744807880c40c0740d2417401750600c1c041c0aa149010b405074901403540a101540c0c112041c03203014040c80f1520202d05849000003401040d0090303480b10b803241c0302c01c002c11081d0034442c1591403195003071020502c45001c8550091502401c1e04402a94138920b0f03ca100300000600d40c800805e9042c0401c6c0c07a000d06401140481ea000c52200036240825200101030703445003c3e6040344d0729006410b100b85403003c2c00310f10f1030b14400302c2c11501b190740b081d42103800201c54004024044400030728203040e05c41790901c10000c2d8040f842080ca0a91f003014000c80c0020240c030014407001d0101a10780c107420210751003c1c0041c8801c140c4284080d49003507107403507540403000030400e240050750100710400074021a007031040404031903050b400350000c2282108125945d000107050294600020031402c2c00180e0b000c0c00034002c2e005030751000f10b554500c450401d402c2c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 814619595 1250 814618345 814618351
    0x6130303060b041a03100e0a0b040e0604080307030207060e0f03071a1905060f09101d100311060408070f0f05011e110a050601090e0c1005090f060c0d0c0b 68
    0x1078428841400750130301c6401c0748280c42860400d025202d503104401588269940d5000041d403503101c0091091000d410f821948400c0000e0360103011290002d040310b90789500c1110003070405e00f41407000c600e00030f129400400c00c0900a003004240042100c01c02d0742007007030098041c003807070f4400108e2404003c95890340e4554860340c400301800515024070910000b01802c8680e03ca010b585a0005d000e50342c52105901c40080042c1c494901450969544035a12100380550f07204900c40d0b0754206015014002814880c112590f29446101d10b10354032111040d0018043c20b42c0240700740004074142d0010000c0000628003102a840308514002400700c44031450307045a0b041119170125000d6031010480011480350051414484180325101181d00305061210010401e0088100024580038150021750308054080b0560700d140e003d080411001d901110b41d402d0100702c0078810308420740751604002c0800000501128a88402d05208a0070402840c0e54517002c18504010813060241840e0a258 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 814620845 1250 814619595 814619609
    0xa02010807170c0d0207060507080402090112030203070204090f050316061506170901151d01080d0f0c0c050a0e0f010801020f0d0b060f07050d0e010806091303030e0613030306 77
    0x51622400b030800000032400928680b540c2c0800295400c84421540c11906040d4104000b044a03081c90078000300306000544059100300024000420100c003800c42c84e80c1c00c103038150011486e100d9640e0034400036244841d41500c280c1080c1c0382c0c00010940c00e000070b040e809031922410520480c0c62a0a20482d035044041c1c044170b0350010820b0000c6900011190400810300000b0300a0f641c5043d443c5015102d007605054520b07184000004012841300c60f1007014854681c00000e0700d0780c0b036040d05503a03210301010301d00c00992a4440f60600034003c0c1e42e003444a0780580c6481c81a961107a001c100017502e1644643c4a44101604001e2058480180c1c14007415442c0000d62030803541d904070051500400c40b40360190395607a00b08511550b1044102c610b45129607090a8841c0024104030b500c403141c2c80c1040000c1034000380710b1445507104590451080c00014050009034440314210804055012011020300d0760b00c8140d412040c200300304551041c0e8101c01c601040f0744003032500805858055101031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 814622095 1250 814620845 814620857
    0xd20070302100c1b060e0f030f09090f040206090907140316030b0108010501020714030307120f09091506050f1323090f0c0a120504080403020103050f0f0606091306080a02010807 78
    0x1302d4110142a100840f40b42c20080205403440c1c00c0c0120b50a04030200300220051000240840740740134541c016200e100000c0391440074540d50202d180c141c89108841c025406503040028000502c2c000b000c2ca81c0218291500070485181071011180790b030b0043e6260304e4194188040349041c15030601680500e80030a103490412540350100103595903846000d030703c0c51403800c802c0d688203a483c10010313524610b0f0002c0c581d40c0014942d034400303040012400e006074000b555070301e00450710070100c0c0102e080c1f80107100c00702031030b251400e10211501d80100c0b0444144a50030042091850b502050990203020903078881c0c8500e8a0003111115100402d41c40c0e18002c2c2c0c4040e04210130307207500560456004040e0421181d070791000350000c462007220000b0306e05070140303004140001c1c080421b001d002541d1003a01d04000944403135501c03030144002220303099540c00c01440020348034181000030300040c100c0a0100c00c48190300520601c00d13910345802c00b0440c3d5018014a2055680c00104607802c18940e09010b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 814623345 1250 814622095 814622117
    0x8220801020c0616020c06030c03010f0f030809040f06050603090105180a0b010317040312270b07150e012f03040c0e04030c0618031d01050d20070302100c 68
    0x40ca803200001801c1c06901e8402c82c0030340d61194020b0060071b80c010b2000700403507030303a00d03049005c209190000e0040a0480c5410030021a105070360029000c00c2d21342120f030f01414030341c00004003c042d0018050a41e400c0c0d0b00c4c0c8500058075287c80010f14040c3c008440007081510b030001240c404520300751101c21481d4441185000840c071414200e40c15250840808124003401c00e46601e242d00c5164402010740d11000c818a1b001c0d540720300800c440c1c504254020400f0030656103d0080300c00c1c0c40c0240fa440c403100304103400009134410030b07001d4411641540071800d50041030031070342110040945200d560369100c03206c281803101c158480c80098121440c503802d6003030544861344c101d90540500300c5143c082d403000c2014117028007400e0140341d074016001e0044c0703c1d5622001e6889032030000210041000388a2580c204503000c41040252681a55194240000388031100007030b1a2510000000e0414070707840d4800710448500601049000e5002004516802e540580031a030980d825841000b8502c03500d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 814624595 1250 814623345 814623367
    0x1115090315100b09030c0913050606030d120c090f090c090e010b0a0503070e100c0b0f091002070602040509100e0a0501060509301e010b030c06160822080102 69
    0x20300402d0740c2650310302c2901e8207204c0b00424a0046003540340c0b0381c8180d10b00300704511001021b840c0d041c514071482c1560340e6502c0d00814542d40716041185000411107441d04141e0000c800e0b40454030300012454a0341c11207507215000c003040c28107a0000c060003522000003809042e0001d0701c50005002004c40200320f9850580509443d01030100321100304100000410387c80ba1107400d441920440040c101c06030a640044054080f06015001311508042c5c000003c020361400c909551007440d18030060b018009c010031004009500c2414101d440a6003400007207031945550004038460004040d81503982400c1244500c0031090040a4104e0b02d814400140a410352100c00d40e901c104c0f0031b84400c82c0c0c081010078503039400001c551154100c440f9106400482c0e003400240311209500e90301c07200740310b070f140942514241c500c100c803010341580c0000c074031895170b060017401000c82c0c1e07034103441c40711488980d60340e0401e09600054070700303540b100c01640c8421800d0f20703105d652008040da01c00031461305284441c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 814625845 1250 814624595 814624621
    0x140705010e10080c04031e140102070b0a050c040b070c0602011503050c0d02060919150c0302150402030f030f0a0207151209020f041e05070309030210091115090315 72
    0x202c181003043c8080881c40041d612000d82d40550f0b4080100003810110405038007815510220030303100440b880a13090b080340c41c10320860360f56540052800d0080d54400040d1b90152501405107500000100710020740c0980b8000503004082c852001030003d84d1400e070000b0709480e582d0000300241040301d8400c2000070400502c0302c01c1050305890b40d1000c031a05000103510740c058480915040b140000604501c0440c0c050030006413007503c046105030501c0d50303008440c100c50070320b4014090390101240a055512508541d94003d10080482d81006040c070082070954000003410001d40e0000308010700d40e107030180300440140c02900015138046242e198010101e988445160210941e11003040e81551958065015080c00280080c403182c0b030740500000c4400b0000514020803444c00300460400f603c40c5c002c8450454040d0300078000c0d1544050880001c02a00c0812100407002610b003000c1c1d03864000181c8664600d0b410031300d84a01510b4141400c00a48038a0b01c040700021400f00006101b5210b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 814627095 1250 814625845 814625869
    0x60f0f01052d040612141b0309010906140108060c0703050d0c020a020916030516020a0210030b0a0b030403110606100e01050c01020d09021212092b140705010e 70
    0x488582c0054215841000e048958150344041000014011540941020164412040c0d05808228203a0a0ba051684850003a1200e000003620944841c0040e90704401468001d644c0c41e0001840d10442d55a40040381d440c50041c9d50b56480c1900100109a400d124041e0700c4005400114500142075030020514400e8068842c003040d0b407030310b015078102d200b0882d074041d003a80030300314081509081014103841c0c05c040c4e8010300040e04180020344007800150480c1e540d520540c00606178140380741c0c200259401c0c00ea441e9070406545011034a140c0c0c1d50f00802038024003c6511155481c249402c0080010385038820300c450b40d0340400700303202c010b0720703400350420a008152500144040004004840a03c55003d10103050b40c0040b401902806d65a0702502000d482118901c4440102c1804542c590300d50010310303a5400f000f400299101e04001c48100c2d841c50b10007800d0307820781c104c83c4e0100c1900c0358495000d0354544010400010303014001c121702009000709080c05d4010b5814400011002e000c1c00e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 814628345 1250 814627095 814627117
    0xc060f02101e0e030c0c04060f03110612011d090c0315180319021c09060e18041104060603060308030c070c050901081011030c18130e06060f0f0105 65
    0x6409003010340c191150720038070028440b15042c41407100c0b1008080e0780341c1150700307070802038001c0e48032062480c139203032191a048610030761041c04154595100c4c1c1461002c000b0000e6005a8200060010344c152400c14a002e440c00c014801440b03200c5010080c04400000d08404495001400d458690750f400940c407500410181c0c021382e044c3c0c2e11691b800c00d0944405407004881d110203d107078000b024480e5000414003199078201d03840804002c2d008a00446210034003004030305600c005020641c4600c00404601001034a03507140c5510243c580500030008450582d08007464030220700582c9030500070398004211500c1c061000e40d043d07407521f100d180310140000d05001d0b4000b541108220f0402000c0c40200001403500c181503a503034110640b1105210f100038501840c2038085111040c040055900542030317009810300f04024000c4140000040c44401540003403602408208042c06010f10307072030180d501c80030380f24a007080c000748101e0b01101c40c0203030b1240c0c140360340320200381e64000c0c140c544c03101c80c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 814629595 1250 814628345 814628351
    0xf04050601020f0102180f0105040e130f0b011e0902030603250e1303090f060c1b0509070309140d08070503070c020a1203080906071d060d180c060f0210 67
    0x80c4000603441c140109103a812254004a2140701401003811468440e00b07060350310302c0200540000441e07140c8158029440d044c00d54002045003450300c0c566010005200d001014041c0c4180c0e1100d5103510000d9000c21118071020700312444010740070f005c04c0014900c00c0303419070644c09c0c1080069114500940e4840b52841d0003c099454000000d00d00340c01001c400f2110101c03810012901036141c0d080d40300940114002c86000904c604842408904032261580c0d0000d280089544003800910384003450442140300f1b40c804103207030781e45601c0759000b0455500d000031403808514010340d52001c4014082400d03040f00000d8110703942c0083c02d545d44401e0510b040c41c1d49a90b00a402c1e0340e12002c1c0a03000e500070056030408126001c18400c4c40341407501a45500344181d42d14500070350340e51422562440043c2c0e940c00d81085d55010030184150b0440010f291a0403c1c2089460740d08599081020b4040d18080204120a003d5442d0150000d040c052500034951101144c0181d5500042600801c000303036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 814630845 1250 814629595 814629601
    0xb030606090414070305091204080c0f01050c1c020c03030f0909090a050f060708010e0610080705040b220e010f030f060905010203071701050607030c14190b1b03060f0405 75
    0x500d50b0f000b4034540d0750f8602141d5960901910060003404101e03039800c0d45200d640c44141140c4480d209403412102c440d4000c060182d0907405112400b2072640300d55040c00014802469005410321204555421420004c2060581c921009240100b814041070007130b0000c100310408580d2403012a00159001c1d00c800e00341e5140c04000920f42288101d003d0050700641031848140707180400e403030703000d12100d64170004140d072141007070038442c2c070b098544942c00390b2100d080c440260700a181c0c540c0c1c0b007003a0742419411700d6500c501d029178513071000c0d0320104d0400440e881894103845114108000d0490030441c160707190704285401c00c0b0a006400081d040031a440c120700c0030000b10fa04030450182d031140080d91030b41000d0301c014211404000652000c508244c0022820341821000d4507852901603807082c180031200e4480e5000014804c0d58410540503040c5100710503105030203500c90082c0f10b04448040b500d014121000c1032004c1c031300d042240c00300800611000b03588441c0d1000d021081164001410f031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 814632095 1250 814630845 814630849
    0x40903090302060f091f080a091e0c180e06190b0a03061506020309030c120a050f030a020f2103060117010801020424050712050403020d060203011e0b03060609 70
    0x5803090788000e51000c1c00041c0c11807010300c44c074040c00c3ca108003640c5140a40c0001404001844d01d484000400100340600141d258021a0028490140140e104010400e900265085041e0340b44c00144d4040000e04801c1000c2d0f03940f42c02d4440390400f903520401500080343c8042d52101c0c4098089607070000144900407420040b0b6210551407100140200d141954900d40107000c0c0040c440d42420081d142030380068110700101c00c0300d040e460001c02501406051b04d0810032100302c041050303140b901c50f031404440040c2d1704008001000d44040e0041d6150740d91310034024034211000050105c1500130000b040003501204646040c80381c040e110f130603126952440129071000d861006642c4582c80040002214001940140705884170170060484821450344421460030200c03035618001201080813801040d50003000300c01c45685450300501d40390380ca0f000614141070b40d03031068405550000c01004504c014110401c81140e4000220443e9031802c11280d8003800010482805030700700040511040e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 814633345 1250 814632095 814632107
    0x9041a090106081501090f0b0a260a062405030a1205090a06110c010302070b0c09060d0207060f18170c01020c0a0602040e072a03050c010516020606061206040903 71
    0x81c1001c43c0448404030240d203803a4221501c20320680c251203160140003904008640611000c41c0f001034160904580b805810748458180c1000b01a4202503042c440100f80c00306024040c4694050780020520390710448508a00290064400c3d01c02c3c1071500c0c0421140d1804101c4189094001d10724807510f42ca5880155003130706c145040e02e03500420042003c10703601e410145140101000004640c0000f40000055080b48224140074082c84000340022b8403018003080101880340019100504103120800c00030180e800401c0c0c100d840702c1d10303500c0b00003803004030340301b00d801c0065041d160f00304413459500c8458481008205074100808000b40e002e900c26425011200d5524400049444400c45800d0001c000c0d003003405038945012070307400820101440340c014800c900b014149e1346a01ca5591a501217440098014202d081c40030620106003042030a01c0fa2500c034400d154203030348881f104258000d04001d8020301aa100303040601007800c0c081e8009100e10f60140084c1e400081c400f003e802c09a401c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 814634595 1250 814633345 814633349
    0x50d0f060b01110109030f030c0f0203090d021c030809060c0a05091306050a0b030405100525020a02061612030e0c04090503040b03160e03011404020d06060302060406020f0c09041a090106 82
    0x7139801c0044210815910100c0d0141da0070303585d0350402c0714401240d0126200d200b218070000c0183e00902c01c0c5c101c640790507071482295510040c440c480d001c0113018010b4040440c000c068001c12188010801400c0d001e0207510b60058245204031324103062208042c00ca400740214940c000d01c0401200c4440582c036a0244c40600401084c00414681c3e0342080c20081e0b0040368100e9503402250941c402e5600302d07020b507c2c01a000c20404030101c82000c04100904840b858000085204006110001d070f113540e8000c2004000b00a01171810b0400360034500c140e4190224400c040600d000d400c0c000a0710080346103e80300c0300449000c0303110003450a14500e0350240fa04101c5c1801400024816845103040030a03508446e2511560300d201c0400c03040508883c2814490441140c03060006030040c5018801020352174071540000400d1a103a0700498819089900300e100580e01280018061102c20822041055001c035955076052405070f88006c4080b401c6100c4803100c001c0e001c04103821070029003113400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 814635845 1250 814634595 814634627
    0xb04020d150b01120501060f081902190807090303081602031b070323031e0706060b03060109050a0305030a0807050d0e0114010501020114070e01140403051501050d0f060b01 76
    0x21100101c0c0100303000414180c0340d6140800c40454130750300c01118030700440c1c0c1280d42c2d40d190740c00c61140318401501c419030020070549141d21210198115010580f01400d23102e2500c01584440d0310881102034038807400070f0056028006100740800000b07130b11001090744a011a00d85501c45d020080c2d090303255005605a1a07002481441d20503030a03440010042d046a0043c81000010044035048030343d4007040c400d0450580c3c104000010a44601c42d00a8165039003078000da52510750617444101c03c40d003940d04061080c44000040c0090381d0b030f018160401520085820142561071540c0e9039a40307100d091041002d02501400041e1668024420b0b1000d40801010511100414800316402886107030280044046079a002003059481407140300d030600312120b4051a29102c91806845004072030303507a01c0c100b240701001ca06440300c241003c3d100452098000301100e800e10348250510f420140c01140c020070b0030441c20030202d64545d0600700400d0304410001601c94480004035510b00380400021 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 814637095 1250 814635845 814635863
    0xa020708100f062102011d1009080c220506010302090913030909020a17090f0f15150a06030c0507061103060102010f0c170c0409052509120b04020d 65
    0x5007a81d0a6400c1100c0a4500300010400785880c4d5144c11455004a40520180b9145210010040d4050f0403120781d40355918081410000701c000001d512650394802600018501080400a102d010400e5034840042100c032600d03040040110200840825808400303481d4a030000704103264001c2e030440714801c4000c0d082088503c1e00444003000407003480411070004140050010300c0c125103109894100e4800d658405d004c1303e0758015075040c900041e00d0b503011342c000d4141080701c2280c100015002052a4409443c5443c2c019a03d42003a08000300501e60600a84a03100915600c0c06464400d40e919803d0000d054824400c3c11101d502549030010055842c000c050b0203c515800007846c46482d090380240889513000d03845406403400c40107280081230070900104060800d03c1c3c007a592201560000c20300f040d5440d4040c00c196803050f500031707110303d101d16a40c0480303d0400890280e40302c041d0501140c0396240892185511540ea070000e840040c2003004541190f84c1c46101107041d0b50050506c0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 814638345 1250 814637095 814637113
    0x509010815030106120c050f06030610090801020a180b09010f1107031a06030d0306241704121707120513050a0c050415030215070302101109040c02060f04080a020708 73
    0x100f0341550001c1c0058810780c039102c02c002494030323000024510b140006806103045072110801e105e620100010b050b0140180b400740407a0004092000d09400c121030f5581390040400c2e0f1240d024540b072141c00040d96031504010386161643c00184425500714070707103007442d440b030542900d044c02c05801e40c00042603491030007025035088140720310560080000302d06440001f018900c06408482c480e1140c0250040c0d11001f02000c080ea88050004110641c10f0403510040c0c4042d2808000c1d404a404850059110403400b503001c2d8006803c09812991000071121420040800b520780604081100815a01c4074000340241c14803180408074982d0000c2180c08800c050300d02a0301044940c026207004614007103040c0002c505042203182181c3d00503000b02c2c5600e08a200019030b56001344401d40540c851050000c0703040c1664401d079040300f01107580d4507445854070001c100c1541c01a0b010401194040814484601c1030320301e020380c0046d41701a049940300c900c108240e003006010752280e0f405014680c05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 814639595 1250 814638345 814638359
    0x40c02010218300706031a0f040c02151617101e050402130509060429010e1905010f0c03210f020a0216050105070c14060d1a0306060109060509010815030106 69
    0x1d0900756171041d20140100048122080f801000038039a451380910034402c507001900709135024041c4c0810030300c1950148080e8060b483c034020400c0d50000005045043c03a0060503520a0300b000d000300d0056501d03c0c01d03041c80302001035561000e004001100c03000c9500d2101128400b4000c50050402510540d101d06003010214000d25803403081e0743c00f4041c7d000000c2e4013884c0c140714402880f40216121030102d04150482d00c684034000c0d54140c144402c001003240140e80f000840f560706040c9804419000d42088001032100700158200c000380000202c240c00025002404501d03100445c2204203401c1c40b40f242c949010340350300b007126a0110302c0094400e0201d0350110741c2040320303060300324140c0c4c1c00c0b5640c5004641911030468003808030303000319800b800348981d020800720360a14001c0c811414070350840c0b100411140804000ca001245402c1d007241e141c20300780800ba6002e402404c3c0926000d150280c09040b07807003104806410010701400044108400c4500d1902c4120b025008010050319116 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 814640845 1250 814639595 814639603
    0x40c0c080d0212151e01020a061d03040e0106090605120105040e0a080c0a03080603030c150907210308090105010501140703020f0d02060415110a03020f0c060c0405040c0201021830 79
    0x411140500d030b803060a0980e80f115003090f03000004040c0d0040018600580703030389d8002d1804e801e50a02070031890910140b400000c00240015005250f4644407951400f0320250000203603a00200511406000c0c1c00032180c5e040601604480c0d040d40c000c550325054046060514188000c01411640040740c00c1c2e011400010300c3d9025944642c40e00c0940392240b90825580c1e00907880b580c0031a42c010707401c03c05551001e102281e0841c1c00542101c0c245602c2c0d021a084032070404030f519480a0710309141c0c2d424542d0000d040c50f0007805440c001c2109504020000700f05000500755141101c0000039100c1c2010b10800000e4078038200c05007600c0c2c0c024000c040003500d403d001e82d030070fa448603010920203a1504613442444c0b00820340421036460400720700300580181d0407004800900300801d00501d0a001010b10245100e41101c0048680d1542024108012910310f84089411a0b00c140200b80481d90301c1202d206c0741940c102c0d08000094409001c0316801e00c210000c448510101604030100020001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 814642095 1250 814640845 814640881
    0x50c24010620030412025e02030601140417151e060d15050a06120c09150b0703181205030d0507020c030106080309030c040c0c080d0212 60
    0x36603401c101258040720040e040090102c028160f8008020821405409040b603480181c03001d800d00703007026528003900703814001c0811100d514029440802c207030341c0c14407422903004220b0100f0700e03508004c0c12144407403d40032803c0c41c0c20f00345a000000c50b481c0da00070450b440f8013030100260740d5505c980b00d50340c01849520800d0390301d0142c42845c00d13103002d0500969145215228034000d503144200040701d200f40001c0b000c0c01c0103403c600e98100007004503064800c0000e02e1146070340d0205150402c0008203003140c0c910b0780160100c0314107140607000520002c003250100d45004001151240710002420480d25147c3d00c40c501c0781c030300050030303408154000e0181c015035880000002c250b1680c41803000d034090314000000b00280c100704681c0250718129848180c000b4035500c1114840c2c00350300086821120b054100044542c00890030003000e20302007004040e10709059600313000102100300d0140c00380300c403100010301c0c100c4081400d16070000150f06450b0b00100d001482d0300a8100204c0104046440e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 814643345 1250 814642095 814642097
    0x91b0837060911030c0706051b121807080c040b041512060e1b01052a030c0f010c02030405151207090305010507080103110d0c0e01030605070825050c240106 69
    0x3c02d00b0a510680c1c0e820a4901ca4a94141c01c41d01e0020179644446c02031034020134480790030898070680c000c1c0407111070280100390382000c0c0107185810703c1544040351940f014220700490340100c00078082c81070301080901e2010001c8d1000302d001c6031010000b5029042c40c0d49440002d82080600258451040b1100c142c01c0380554801c00880d00340004036a114081d911a210f00040e4140814886501c520018181c42444002c94655a8403038802d0b401c000003102c0740628560320100e4030000aa10501c04039200050810080200241e2407402035101d00891003450301c141070495001c00940d0002084a01740a40894000c0240c42c01c01d0700503141d40a00d000546082d0701e09000124454001c103481c905980e00708190000410b403401c100080703003d8948048441628450f000141a1281d99015010758880c00d8081014980608003e1801800424812464405190038202080700480c0040001c000e4038150760346c3c40090003050320b07182c003240207600c2081d02038221b003110081410394141640e400d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 814644595 1250 814643345 814643351
    0xc120905060709090b030a08090f03060c0919150e030a15022502010905041a03010504140d1806030f0605120a0201020c010201020f120711030a030501091b08370609 72
    0x88114510032034801000072609640301c2c42944010408d402d014048100c0c0081004001c0c0d4040b401081c20408144c0340c0d496894000b04071a20b43d40740520304041f0b408030a40504042e00d2405101750710548401e41503605001c0d45d2440d0f03030003640301031000084041c0c1014a446240350400e0104009501c508004034a407494548000e0030201c044490700c103941d030141c3d20760303003554103113401c001c02000e0707004c01c102c5031041016600516441c2800b410f4403603805808e0b050801d140c1541c0240c2048101c40e042410000d000780390804905410070640305540c3e0f04c0c0340004034080341025030300042c2a40d4102c0303540081302d40440c81f202d200000780160b07001c0c805c0e42031311041084607005a0030307401079042c0103040c001d0a01218000b6000c245440c0e51140c040d28040d454040140301381811540144400000251204014040d001d1a8040c0e89800d200075030481004495808004002d0034014001d0041901c4100c80b10001101c0700789a441180b00b4aa04407035204620060b080040205104894421341 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 814645845 1250 814644595 814644599
    0x31b0618041113030b0c0a170613150e0109060e0a05090c04110d0609020a0918020405062d030610050307090509012309102d03060606120506010e040c120905060709 72
    0xc03040903a02108581c1e1a035462008c00111410340703614000340200d80001d10707041c081c071840b40d2030f014001c0d0510342e402c1c10500f0315040c03842c0303000317580c00580141c0403a5042c11010030540038010030b40c03544650312500c001100d80350243c030700c3d08207000c40815a038410f051590b00d44000c0380003001403403440030503a020801140c0d1485d2202c20f90140200030300204080f510100314611440e203804520070401c06006107050f4644002602c19046000c004100031010225499540280d855146102c50321200d4103081d40303440c0002807040744440c91803204001d008004910903600609040e070103000e0041a080483da101d20300b41d5024270031a4844a8121200c40724a101d50410303c08241c018120402070613039290a288417103415a2007011710022541100c0c1e408090030f01d4440e41c802c05075104a101150083c6092802044d0f101143c055105051800c020b2103040da800641c000c031000000d07131300031a104550b0304e41a5000d106034041d5134041b504059081c010040c0208506200f19240e444020000e0707 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 814647095 1250 814645845 814645861
    0x11706070215060d0501020f041202180c09060715060e091b3007030303060e0618040b0601020106090e012a0c0b0c090409050c031b0618041113030b 65
    0x9281000c0700b54120a40300080b9109082103449401d8050141c000503241240c142c890310b4142c0c0c815400700700c07041c45641c44402145003d04109501d04075201d00f808040c1410010f80d0301910030162441e214020005000c420002e00304c1d4280e152041401041001d665500b074642c001c0401191500a603000754003084040700350300b04849807010b20250001503542c0350090160b044036281e0500d0140607105500d01d00c0303a10b42c10408100a180f1035a0003041e100d1070300d540070000d000060540c42c45618030946000001c255800c4032035029800c844100c40c1a100c400051340102032541084c00601e0603c2401108400150800c90b40c0ca00c2c11041222007034085c0c00e0140501002c2002c04000840507900302c3c0115009031015504201c000d0140d61034540610009402ca039415007084855402c90040440549028400035200c040e290204031041160280000c030603208403840801400301803400d03007038252240d90000e00ca0414403024546d49044026051506080d2480308507101c0394803e00180d009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 814648345 1250 814647095 814647103
    0x304060b0a08030a1704050a21030c0305071b020105040803180a0b160623010810060902090a051201020f07150f09150504240608060109060b0a12090b0117060702 71
    0x500c3c0c0d182d0300c03100001660301c11710303510700c40140c000d90341ea20842e4a00404609010704426406444000420b542d0761603150150903140c0d000340c0441454034240030030840c0c64001892b41803d100225413102e002180344016a02402250010035851001055002e401c0c5011500000000b50445850510680d02c10b01d0308030320312070000c43c001c112407442c00442c0002c0154110a9000040342d600710b03481e81d010148100205826030242a151384107000800c0102c0c0e05109803801f5220b0708000390b107040318136404640208114810dc0b40111850481052100030a50682d0901080050780650721402410020791038007900300e03001c0400b8540903195500c1d425911070540e01ca030b4080010410310881060500017094001e000760742c20358545007200100808214144d0392490031034030025405003083e05591900c030341600600545854410180441c40b03021060300c148200c01e24165881c40175005150014100510001300224507110000c40c03094000b05040303803403420035021240982c0c2e80d0882245d403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 814649595 1250 814648345 814648357
    0x506130f290a0921170d1a0306010b0d0f1112070c0c03060903020c040e010509010b0d0c0b0f0c01060305010b090f1626040b2e0510030905030304060b0a0803 69
    0x71460100c030400048800070503107031343d820b100000b070302c00031000d038441d0301100c0c02002e0407503424140011540101240381c416030444210060484a52181c2e5038007183e92498107014400c00d858000c651104e180119804c251180e0942c45e0301800180108850000c154205040c0858442c80d2000054002032203990350040094101d070001c903a003480c0d0384030400105640c0c032003034085004034003400c10103032120700890509003112000000c40c1d00c1c02811310b40c2162070107047e0314440c100c0d048044010844c1101c00d00181d0b00e44081c070654030340212814041300e12510b01901c010f9403c2c00800000d0150640c0041380304074040d121a6002d03a01d8101396801424100d560f05d404484858548920ba0b20038400c000020950944a9451449445e102d15040070122000c0710b60042d00c400b0046041e850328041c03500c189154075240c41044000c5071070001808240905401480e4020303074101000e01c2604000ba003950048150703603903828a818684090084103c48600030160346400103002c120010480b01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 814650845 1250 814649595 814649597
    0xa1d01150503040305090f0319050d020c060909100e010e01030b07110d080406060b0c160509040f140c0d05010b0111030a090e060f03030f040311190506130f290a 71
    0x200d90f0b80c0b030359402d80c1d0503001406080d0300902003000c03036001520b0030030440301d00480b8240007440144031854020f1411400c5076840c2300310341111146201c0754850001340d550809003290707840d041d59164407211011050035440107045154020000402e401206c10280c10390b030050503407a8513a903030382800783c84c080940c51181c1c250303600c072001000d000c6200f04881500300c1e202d0980400c4107a82c03510680d4064100c1d400c03e210640010b507541f1f440d44041c0030024000d0070196101903441c601070b21000031000c83c10b5000360181101042401c1d080b0010303c548035003910010700c0385c002e40c1d200d410002e000f4110300c04003502140f2040c140ca04055000800d4502c8000f5642e107800406044c03045215140401505040d080103100444502370b550902c0030740310110300c0d00c03512611a880c605001030b04892901c046030260f0845200c03e108080140c10650940e0301c1500c00c1d580d10b004074000c4407486c482580c020002180101710100d00b4180d51044c94440c0c1b80c8101d940b00000c0105031540d210b40c0700e80400b90b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 814652095 1250 814650845 814650847
    0xb0105041a062b0c090e04030e0d0512030c22081b06090402070602090108011403031e1902010e0c04060819052107020901091404060e010b0a1d011505 66
    0x90142c0c58107400406030b400b06440c19451003806440c034809018118240303594038039141c2c001100040e511240900003040c80000c00c4044e810a41c501511030720040d00380c14001e03440c44c05071000348601003081645c405800c942d41039607403801081c5002c4a4015210001107030504a802140d503c03040d200343c10a9905281c003610036120400d40d090400b400c0d154080ba0828800d2144050565442c40500b880c1409050056036800b04803000400c0140143c10a8080e000e0036000d030102030f100082514004105200d4041d001040d004043c1b40d1070103075600e00000480c18001207241c05a064124011074034841c0704542254001c0d40030003041d200940664021940603d00003502d05a14014207606a070265040e19000c550600242158443c080081482a400003944108500700b001a0714018400314008001042003c181007a80b024007070006042c040d16864503d0041b0800e510200317001c0c000411b408849a47c4603141c0d1700300c518038201440484040c000001c0d020381c0c000704540591a1564500b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 814653345 1250 814652095 814652141
    0x20c010503070e0a030f11150a050f09041a040f0b010518120307060b27040f060e0a0506010306110a08040b270616090807060815030a0308040b010504 66
    0x445240d00002c00c5041004100050156203843d042c840a02460180310703058664900d50600b141c0181c14591041e00940040040201c100b507500d058406851b007600d0090790348d0410040700740d11400382110f8140d000307140285000440c00341c1909144420f8050b01c09111042180d1900401c80320401c9a1601240041140407010108002c04224110004020521880121600d00c0c5190032180080340c91076a142d60070340c0c81785040320290100710701c070f800508003030400314100300d5003014040c20040c0000c640c0b034801c104110070341d00050b1081d00a5000c881030010f082c10503a58400c428841929102c2c50710645501261403001120601061901c51946544403a81c0316030580313800401c844585180a00f46a44082003220320b070450320f20350380c02054903080c80e02d26203052980800c015414042d968108000d075000200380007049aa05040c83c000300e40c0d80011046e0080040300409a05001d0440300200b01904480d04500550141c2c407440c1040e070720350050204484004a0007111514107050b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 814654595 1250 814653345 814653347
    0x90901020f0702040b0a15121a0a090203070c0228051801030b0702030906031005030c01020723040b04021303170702011719142d010b0f0c0706090504050105030d020c01 74
    0x104000d07101c1c3c0070300804644c0da0b580318624807c003402d0104000041542c0c500d0112144503000b4000d02850f42000c0c080b181ca40d003000544074590350303c40c94814039000300c005500e0324045c5e52001d00741900a4510120030f00f0042c0c884018000c00c445070b03800c0340b08204021034203042c01251418101c0f80a0715614069085031140401000b0003400c50045100c2005a0400da80390f03040518055490042500303c2107040c032003010b04142d000b01c800c0d4115407103103030100030003901d004009400d0210804c44044800704400401d0107494492201508a400020503104103c0200c0e020406c49018060854800c0c00d2160b914840344201d034000b83c000b80c041411803980b410030340b80f241d0300425000c0901001d440c21044050580c0c0051480c0312040c0050010407034014440e1105154040722410000407545580d0070301032840b4030601401c900c0a60105a150301095070711b003103c003072a0604044030740751070355100010f00500c1d20340a00c500803420440002614180001d42e11048217058001d000d00c00d4003940 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 814655845 1250 814654595 814654601
    0x60305010311010e03190609060608061005041a0301062907030806061b0f06060306060103020c060c030903221e03050a02010e030309060d02131509120503040512030702090901020f070204 82
    0x1035482d81c54080d0480b2441201b800001411000703105001c0841c0e00166402c4c4841103444036400051030b0340240c010007400ea080840e0102c180c130802c8400040c0b4051480c1d881400302940c00c2919011b40c03034044085160107003d06142c105a801c046d80070f031121000c400c015603901960744004c02241079030000ca00140f4013203000d854262541420542d201c1103581c00b40f450200f0640e0702102e40c3d0054402d11400b070509011003036000c5420308007549011008800e03039603a035100418100040501102140c081030040c401c0f1104280310007481c0c1105a000c0070080c4885810384106094811111a98a20390001d0b0701503030202ea4010001c0c081d4105250015181213040045e008e0745070100300100106c41d61040e000e030401454003440142c0b94940440303650343c58005a0400c00703000f031124901d0b003c1030b644400704005a030311040107aa030100580c0351851941c02207800c41540603080900043c17000000201a00400b03000711407450064480c8480e00d401c030b1182103909104104108012405030400750 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 814657095 1250 814655845 814655867
    0xa03080a080702120703030f06050a152a050609210901050d09021e120705100f030e010603111e0f010c02010909060902030f0a1109090a1503080c0706030501031101 72
    0x1c010340c4c0c40d0389040f050804403540a5081100803e82d43c0e403401c06555850b210310030203002c054a44a64075801c02504509418003407040764108803c5914008a006041e542458840303510403800d000c403213541c9007058803060111180d61a600c41c408030300842c1c0c0d040062044000307400c04509072602800c2c10044034a41e20031070f00045030381e032282c80180058851410b840f41625100018100d00c030007600c00c020710340d1800c2c81041d0103940824414059956001000480b620035800c00003a080f00c100425005040d0425401c91294640040081401904101908036041c115042e503c440206801c100d1116824160366411911940145000d5401040d01d40300c19401414803039071480e5511701c040150303456a000f031502e00350003105020f403100140c400c4940205181c030f02440106864070000720319000d5450120302c604600f1002c00c885e222194407a000d40048a20212443d41d02d0381440f10003580180c008100c00e1241020002d5010300c030b4800c139416070350701070851220490050011980c00f0804 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 814658345 1250 814657095 814657097
    0x403050a03110903060a02180a031106090d12120e0f06010308090d24060b31081e0f0f0a020d0302010e100f06050f180a11070305090f0a03080a0807 65
    0x200980100d80c1da0410500380b00d01400390015a0740c4c212641040101c210041d008c501520108100f400004c22035000c0703c40458040c0d81003904e400001300007450322040340794041e09164010b4121008940c3c003201008200c0303040790091099408030100281d03182890036807030090b40c11144c0107000041001e0010025404010304000011406440d15004104498583e0191036051441d03030020340c4c07040c0074190040c504002c24505040c0c4268141404512120715004000c48041140e484580c1645036200034014680071900c00100c0e100c000884151090150385d264415202c071703001583c20028018000c1348040c0c0c041c14204a190b0700f032100c19846a43c04a0640d526114001c070040000c0090f851621219000800d07003c011072035000c1100c0f02504190f000d0040380c08a200c10703488500741000f040c0c810210148c2e841d5142803082d0020310420440c00220b100c001080c1041c581d1204c0500790b240300c1124192422915002008508034803840020038082c2d091250340d61141c00341010f00d621500ba = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 814659595 1250 814658345 814658347
    0xf02130b04020a08010e0f0417031012121101060506220e0c04030c060f1b03090b1c0b0303030f0c070302070305150a0e011523040609050f070203030403050a0311 71
    0xc0000035007a03030000003501001854031001080100d69030040550050b04030f140d46081414151280450000071490110b2072060010205210030700e1420030500420403940c12000c0c0b46103034a482000700c04c60f1403160340010f03c0c0c08800314078000184282c0c01154401031a141c0303010301c00e251405a0200410b64882c00004c180b900082c0e140e030013902076205142300c812042d592811762078480b080800b03d82240040080da14111842150810107000c1100120316220a88120f03030705c3c2c12030b15901c840d0810000c80c240842d0792203140741c607031000007c14410720809200030202e00d07090550341c0c0402c0f175110860010400110780e00546000c020700300c0c24064410b80b800162070b80c032080c2c60301e806182c0a04041812604102d83c07a07180d44504005074001c440217000300003202905081c03900a50045522009002400e10221030315401803841509000c0c00521825aa503984080101400c999401486a40740001910303d031000c81100d00c190381c0350700c4260502c0407082003100203041c01c907030194080324 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 814660845 1250 814659595 814659611
    0xd0801091112010b091309030f1b060c0818030717091305160807180911090409120216030c0306020f040305010e0601060f020c01050421020d0f0203190f0213 69
    0x950152082c3c007a000f041034040d568070300e25040c0036010640038011107415140c0750f2410000f82d44062040e2403030003030345444500410041030100181755016001084907182c10000c02c1141d402000c80d40c400c3c089030b00300400c1560a46821342e2244954040200480c21400b0500e00c1c0c507501e0300180030344800c0540b500f2012a280d480304001c0310401e5a40203088450b0b04012504641d201d0016580000e00389040454800500e0404101584a0003007d00380c0343c64032181498001da21003900c40121000b00140118000b600740300701807090f0054a00e0050140c41510030416400030110000c503076108118401c0700340786496036002500482000520030b4400c10000022410901400d5100308810001c2c040651414102504040750095040300355001100c501032581e0f001000d480407945860101c0c488800c400f000b0820011a04500039030051201003034405000840300c0d0036415520a03000c851508060f5071245980c010081e1004201510003810301c1d005040c90680607500c0e54103545c010903014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 814662095 1250 814660845 814660867
    0x70504081011090a06091404060e070e040f0c0804021503090d05070203191a01051c0b100512070e090105040c05011809060909020406050f030319051911010506030d08010911 76
    0x64020307032108000503051b91040c00704d82212004500003c1d403c44080252511740011a510584000c0c00c140c1441303c28411015181c440b0340100d4019040e10f242004120824403000d00640c0c0c040d00c0580c0502a15000e80b40803900d001700720390040a160000309040382601c002118140d0001804a8242c0500e000804006000c1c03e1080046449541e500305203c0b40384000030228081680118820305909500789100440b0a0301c0780c442c0c0f9003080b9a00c0d4103541d043c0c150900718480d54071898020445003090240000e0100e9035070b0548414501030269031f225192524280d4a0503100900207902a0100300280d60084680c4540c012901a207191900e9840d01103404035226580011803450b10351100304114613103403084502030542140c04560301c40d20700020036680d024038101c035844a00005044a2482e01074010f2351924007040a0001100e0424500241400c6015070180791643c01c0c000426402d2401040065508a0782e0b9207890f0f09070301e0618400d01501410000424002c01085200da00e1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 814663345 1250 814662095 814662109
    0x8130303150e01050f0904022101090b01080105070f0201050603120a1b03020c041112041b0909080714033402040e0d0e010c24240e07050408101109 65
    0x3001040490380b00c03507151400f4019240e8000b00c040c1c0c8035455040400c001030f9280340350b6031032410110588054000203024101e0040049420203007010040c18000211220150001c81c031a40c81c44d82c5403003102555500c140c0c00e070385050382e40c260316801648040941c1d89890004e404680346918041200d441c807030000c40121840b4010a4005030480150400b1a081038040d0b1045d0f00030110b0820324004e003c20f0302e21400e010142008101c00344500245918000540039100079180c500020014500d042c9040d0b2200ea108060442e02c0c45201c6d80c8a64410344080b05459900405620340c022210085600441100402e0481d0100448011803100541c81d02e2107062210301000c40146034145001c1b40c0581740364000c2c640385040046220a03040000d0180e0480a400c5800b200725803102800302e818240a058080b100c0c000701c1c80204051102400c43c2e503625800c0b181101039009054135140411142845280070b402d5055004a2032828118107607070110614101800d04282003050243c001181d0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 814664595 1250 814663345 814663349
    0x210030204120b0a0e031c0207050a02030709020904050a09080a080a0e1f050105090c120405070302040e0102030403140a09060e0310020a091505070b01093620010813030315 76
    0x10494141c010025510118805e805011394440011402c181801d920f0840c508000d0806002564002c02c04c6020001c0c10040c21000a80c0201500c4410740c5507210800250003005005200d1401c0c07030046006400584036142065400c00b00407480d01a4401050f01e60b42c0c006400e650180d82d0300d03a081d0341c0d80d0100b40031826010b050000c3e031040f0608960501e100350303101a001103204040711410720481110070000c94480e8085484940c1003559141001424003889a00280d0400d040c108d01c0340101c141036000714880ca1103515012810741d40d6a0f4841994003400c144240800e441c0082403000e64000c4000e00341c4a4002000c462001420009280907031300980e084c5000301d4002241030100c91003c010348103241c815841c199080c1703003454803071004854040c03082d85003c41e501c4000c1050000f040a800000542c500d00a107a11b128007000e504040c8070010050390310480342d140805031030b2030f02c61003110400340c140e40748036007a1a4020688901911017404a09050361144c4007820705619141c5240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 814665845 1250 814664595 814664603
    0xc010209040506040506030705010c0c09050c070605090a0201080126030a0824030a03030c020307170d1d07090b0111071401090b0705120901050409110a090e0c07021003020412 77
    0x18590001209100685002030f10892181e400c0c1010001d2581340012004c0c219007092800704420a02030501003c1070034103030064040381d8242410448d0a0041c0801401200e1040e0005c00613961041149600c81d85945e4009000440000040010030240e444400d61030040c0f0280c0e0098000c0a40c60504d19400219400c000c50b14a0040020804000aa904000744840191660014850006503d95034400c200a082c1907030b524065034040c0c0308005680c40d81c1c0c0e02c045084480850710050031a0364220080100c9140c1c00c1a801e640c9409100302d002d0148251303100100800c6081400d40c40281030461006810440c507246600d60b50802005950010805040c0b28102d1034001c0e00010510701c510382192030502001c01241c00003400001e015400c0007851846252a0b5001c0350040b01d0710300c9035a21007100141050138414407280c2000050034804d40d180c480c85500c550350b81803480489030449100c1300c1d4000602100000d4104400b03001c50035015880e005141c15141e1056201030044100e080c0c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 814667095 1250 814665845 814665847
    0xb2b0b0106021c0507060b120604060c030c0509150702060f091e031c2c0906010201180f0f080c011a030622050a1a0901140c0304021c06020c0102 64
    0x4050000480415014281d2440548030001e1100016a450400c2c1e42c1c218080150000700c000900840d503201103084400144540382d80d0641c01c042aa89000540c3c0503502d441c034101034503007110b0182c80703814802180c640798103003004010740404c82206180e070306d60703203420348100800f80060351440e00074000d2050352100c107901c07821160184540c000121544402d240394410416030240d50000d280824034040c030912506c3c005003180120b03060001c2c2c00d008210804903000501c0010001100d030400108240c83d039081668890b00124240c58840300542406e400e403a21101c0421205418400c1e11400380307125941078551640d60107100d44c88128610808d0f555014840500c1c01d204003103401191040f4010301d032505214080201803595051a20781d58800c0c1b2400c881042810300964141c942c21107645400b8124005c2140c04440d41102c520701c46504c1d01007194206a400c40c1010301800d030b025103603811555150309010070902c0d0001d24000e4007103041132910002d02c8900052801000b204005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 814668345 1250 814667095 814667179
    0x1030f03082208030406200d0f0606051602010e040c020a02011803170f0f0d140f150420071b06050408070909020105070f030201060911040326120f16021902040b 71
    0x22341200c841a0400000c10b060150801c8090f6000042d1040e04a1400300c94800c0416071005030b400e000c070b10580700d40190801544071216a000f140c20340520303000ba2940c03400b40c203003030010700300b11402800014502d81211100c001200750140280a0700d242c0e03041500e19000d84606c880c40389400c1400803c81268a545034145500600e0f811507420846c00c2e0407284403406c0c4140f011040c100d182c0c91040c080d07962144640d2421130001c000004100070100040d0b83c0f581b00b403c0270302c4402e0b141c1d04080d210041408000401070710400c122021a01e046000e080c4c20b5080a05440141808440a0781000801d200d4680400d004d075041da84c0d00c0d8440d400000e00c680c03a0080d039406450040d600081c510b8001c1c80308001040c40104020241e80b01072018030101c040034561920540203030f044540582011200300103260083c005614040c1a0400701000c8002110034100c2e515041c6105c50900e10714040d415000500741070b00100403603000200149070030102000c15007042c88150a01c40700650420101d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 814669595 1250 814668345 814668367
    0x703020c190c060f030c12020a120603080a031803081515031e07030902061206010903082b0e1c03110a0306030c0e1003030c170301030f0308220803040620 68
    0xc01200159904060049891140c4068202410a8000c0c7c0c44280c00050345003c20303105444c14122000b07035172001c000c92912400c102d959504803580c000302207850b006c04c002d8015406c4a522010580c155514001c80c1d444042840345103091700d405a030060348640c0005100c940d85006103106082c08005a80350300c4007102070041d01c1e10064280ba041c10303d894100c50141c0c0b03403101100c0c0320300c90303841c8004110b40b60180100c6807444160f001400f485030202d840808907545464051203800390000003800c2c0d80d21069010111400004851411350081d144240a0403501c42e82003c1c405050400043da0106400750700000d80c8048003400001c1d42ea031106200b00300e05150500040c200c1444450104c0c0f80044001d01640710500001c0d00344540c4880b105c04101246034116900900409010703141e503964501030070309005c0403900b10b000c61044400644000e2080402102c0508002642c1c401c00c90b0300d41318401e203030b8400b40044d1520b5403245485034113208010101c0001c6e1698070b06148c0c0d034510b6518 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 814670845 1250 814669595 814669607
    0x71a0703021c020307080903030c0114090d090b190e0303130e16050f0705190c09050f04080307050c0a060504080a1d060d0f24050f04090206030703020c190c06 70
    0x80c030b5100b031802ea0385450500b40e03000042e6800c0b20307403081086d541c1e5210721002a03e18003808218007003070b60900b40740782d031030307082c0310f0304141c02021624119022107600b0881a01d00140d03500440f60490003c2c4040c0c440782c04040070300c445030320711404c05001140090300800d0075944040751050110f15078a43c108806c1c0c0d141c85240e03900c001000700c1c0c10340069003079500410038851403007291041200428a4024844284400c54214414144260f9100d04c6460700ba100f11306c0510620103030340d2400b0006201040e142c1103492141d940008c1092643d66085c0055545400c400084003203440368800342000110301e03200301d50003280aa8000c50311001c1444008020030b14441541c201c407001c040030950140c0ba04025602d21103034040d80866100903e000290050010130500300390392460222840340303030441c144040c00b070312400e980d00509290b01c0401e02041d980100300007500a1000c20001d01c4080c4284e002d040d00c6c08002c03040d81c0d034412040060360351f1040c5a8406554210b02550300308501d5400c20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 814672095 1250 814670845 814670863
    0x4140d0503060a0e04050319091a090d02090a020d18060c02070f030b1806070804020112060323030c07030b090705120a0303051801180605100b0318071a070302 70
    0x454001e145142440218480d04014400c928900e4505404078040007020b0059426111a001e112002e00190300380003040000c7e113100c0c00508002401c510b01e10030680700c003150094400506034204200566080c0843c6010042c0500e0300300f5828800c0d925000d0b0107000c1d8041074030360744829510859070340c1044021161020044800e65205001c00c0010449441e0090b003120f030030840a440980c2c4a840c251920b0800c402e00d0f88160180504010030180c00c0881140158000e0741d444040f2042801e15000b1110107000c060888102203c0e00c82d00c2d0b0701704128411040c038521007520304015941c20310600d421050b0b00116850f403501d20800500c18401c001d89801081e044900140c0c0d20300c0c60f48a1501c0d81c1c0c90800c09010140c8030000144401d260b49482c682101ca0003000304480b00d00c08050810a4058400407034190342801d000c1000c102c1281115402c1c0c400c0b458015141d41c840e5001c0508c503a40031307110000d1718045d2000005214904500000480d51245500e946c0c0d181c1c90301c1c0080c182070180b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 814673345 1250 814672095 814672097
    0x5030a060905010f06033b15091002070503090405010b0703030506040506010f120e07060908060c121303090810020301090c0215061903080f0c07090605010210051e04140d 75
    0x1120040013009224040642203031001d040000d10445260710010308002e030602000c0551080e00351014103e510044c3c0101c17904503040c140d868030803015040d80518141a0343d208210f5100c00240c0d44444450f5000f05030040c410001c032494882d905011400345c1d1001da010002100c0c02003040000d0540502489d0351100b012101000700340b5080001a00e030a41d94140c800c1000b0941c7d8001108170429400310550540020858800b5641e500f002844110b050203103500030b01464000c508480000400c1d244268425124040c180d560002e8140c4504280941038042082d01e000000c0c006800340072034103000660002c056940d6050400c4070b4140c1d05801184400c40d40122664208000d0382e10040e5001142100d54218420881d480f030040c80e00703180c102409a00c0009809040411604010048983d401c0240c07138105a64139903030000ca403031500c00c917800340c1c21040d00140c2000d2598007896000c0500d000120011880e0f903801a407440085504952080c060762071018122400c0145200907682 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 814674595 1250 814673345 814673351
    0x60e2107052407030e04090c0f0501020f15060f01021501083a0806040204080312090d0908070308031009150e010b0f0403020f010311030903030604051b1905091005030a0609 76
    0x2100702c05a55128082001d020010001070745c0c0003a81d41c41d000a245560400010240b0513110000513460300c0c11403003250702521801e80140a04080481d075012450f100c4c0010410700d640382030a010031403c0d046074507811030040c01e00703204a4100341d04a490203040500c000f00161041101000d008181c0c0090110f80e1004000542509819841c00507111040a2078050840e445000114002e0b00803070304040c01e280000f25070b102814019141c500d04c00c070a030300120307074822030804801e07031341503119011300289608001c8040c0701103480b4200458125010365030422076240d480e00201d00310350b030030100101f42c440070170b0007004031032110180903015103054030502d0301c0d04d148003124070294070640c800240a207556490244081c7e0003580101052002c9055643c0d9925082e2101500c0764800c9411078030982c41d200c046124081001e09503044004d030194490304c1c080c00305051082200f84810744104000007007040d447c143e251101201180107194880740e2310380c03c0030382c0d101c0113461058000c1c0300f0940c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 814675845 1250 814674595 814674649
    0xc02070b1c0b0613121509050d030c1e1707050f0d0911090c070605280b03010e0f4c060f030b0109050f10060e210705 52
    0x10900419811040000c0d40c005850b002d60400304040e4014941d0400d031410040d80002034071115441085460380c4194540d807410310300301c20403a080381c0d0f5180b0060010780c880764411103201d001c0d51007030391400c0c03a90610a109059003500542400a41d121040010b8010144000700c2c0c04504407280d0001c0c1a4107007079042c42d114100006407801444004551a501c0c0c1000c4000c0c000c1900c24124035500c090221411464610648192a8010f0320100c8a480ca0000003c840c640401007480c42000d05624880c4c8503400705040d100a420000c105581c5550b0320010244245010009440e5402a500250154800d000040411040500e006400c40b0505021513182c00c810300d2019040700071841a02c0a060124840308801003800d5000b00710340300c90100000c420321100c0205c0c00d04a502d440018000d82c1d440010800044c2030542e080d48404441001c140409070040d8098824118007901c11031007020355080001c0302e1032014060300c50f5074200001c18410b03828041070b5810100325074000300700418 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 814677095 1250 814675845 814675867
    0x61c050706031a0409051b0105070c0605030403230f07080912060a0c030506100f120e1e010c08060f15030a060f0b2115130f0b0a05060306040207030e0a090c02070b 72
    0x40c48101860740000c87c001c42001e4582c0118207903600b00303403c107030806100b50715007201400070b03401030701c0607000714200302c15140c0488000c40341c00c1026518450b41508140070950100c074550404142161807000c00d110100240d21021000310194110b24020800ca0502c880305c03034110f0b00002813010425080104109403619000034500048005103456284003940d4902292110a00d08080591038145043c0d02c0302803100040c410b002650101060b031202041c6109c0b24201c2d00201000004241c640d800100c161030500000f9544010181c24420386e10000304220010b94421a884591941c2e5600140454007001d0100005024807285052801542c16003020505580f403541c1aa800c0307240c00000c903003211041180c0040c0e4005440340c00041d540c2c92000000d0f200d001041c1c604e032458400c80c000545026001d80c4102d072000742683d0315649038142440040d601444083e07090010b40410300e00341e42c03240c201c1400204840a0b0009a031500306000a00f00f031850360010700300a00a000e090340c2e00d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 814678345 1250 814677095 814677103
    0x606080103080f0c06040f1b061b05100c030f0e24130f030201050702061b040e0901060f0b03040b0105010c11091f08010605190806061c050706031a040905 68
    0x1607038215045544808042c050f00f0090300c01c40714100c003d8020b84c02070000304803403100710120300d5103e0040e911140708038480e1400200f00502c0783c01c000842d64880c000340d00c8481039002c005540500190340707010107484080c0307050b58500305681d80045e40d5544540310301051481400070100c4100080c041c40c22030254014403039001c6000001d1039035000400304180c4894200140e03251a030042c0c90180102d0742e03050207402410300300c61000c098062640040c0d4459000049503071000c5280000170700386400c26080c0d0000d01c10081007016107650365500480c003010415003440c0100b104610143d81d03031810b40b0300768560701c406234051810701207540c0f520400182081204400f0500680f0045a50b13031b9012002c0c41403010103500d02202011070540441c03201010b4000c0d80c00d50b50300341c4640180300a074401d500307400380c61482482030319000707c0c000c107046d454034a000500c00460303100440c0544005440741d03070030001ca95002c0c60100396140340e0003008940c03c1c40040310f01c0508507000c001c40201c6881d90750302c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 814679595 1250 814678345 814678349
    0x22404030b0901020d0f0b010e01020f0601090e1e0c101b1101050d0f0221040203120a050d110405040501121211030705060114150f0a051803030d0501140406060801 72
    0x181000398000103000700401d50603100d010417400300902c40300315004016002403d003d48180d0000d1070300c1c1c01815140d4000138042c0b2105507040001d000aa207002946c100a0000d400f110100340225a07400340300480914100741031500d8900600f13a644045005c209100302c40c800e168061015500d0600245500303844082d0040d0742104161140b82c00703181c012601e43c0300d00c0710002d0504c1d14110300030643c3c080303c1d0301414010501510040c0d00c00d058044da01c1003030808840c02503269016100756110028500c014201024580c10418200001c00e49200300791004c0214601d0300040c04181002689070500425006122072421a030b402400d41d00c80c0714004103000b21505c18005d2060606040c6170040044a8100e07401000355509542c468030680342e011000740389c0714428444440b0182900c603005c421100580c1e80880840d29000403c2070030355131500200f0702c1320860110940700c10880e803000e100805d07031070440c010000350560400003100344c02c41204081c280264584101032040c65006403840f41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 814680845 1250 814679595 814679603
    0xf0e01150206070c0201090e151002150a020a031419060e0405210d06080a140c03100507260f010f0b0412110616141501140a030b090a02240403 63
    0x840c08146000584200c21f00e58010f05101c00d4900c10009800b040400341c04141600700e62200318084100e108aa071942c14101d40581d1440200201e6102c07031040c0d0080c0b40d001201c0c10041100c2d03a04054444070702204aa801c080505201c295550740e848911845010300380e0112203494600301525419a510500c007010049000308440313440f1080b01c480152070305900103240903c507540e162010503854400002c2c0440c2c80e1f000d0108000070440000c1407440841c2c0f0040c0c0146000d0705c003085d0a90282c24081c01c04018404200c5810f003030100b603900311903d4041021105e08d1a1305000c042104025016408019101c061203406d00c04400524200d030106c619000c42c02d0304040d03603410608501c0703000b0404154020000100f1078600003194681080c000e0217502106c001d00320303010030552101001e40449074000c2d0240018004505005054120709401070301d4561215140da56103c12120103850301e090990152003500d045207003071500b03550103c0301d8070741d84400039001000c024000c5c02a400b00034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 814682095 1250 814680845 814680857
    0xd0b0105060703020708030415030e280c1206050f16082802120402030706050408280f0c1e081b030a0c060c02092505090a0801060f0e0115020607 64
    0xc003c1c503108000c09000f4040420a41c0c0c0d40d00d41e50b42042c4081ea0000040c1008641481c2e480b80a582e000300350382998200030001c080c1d01e8041c1d000b602d40c070b1024001044078803100c11340d00461001c03004c0e29140358051080c9000183c40c200603d605c1c180310b40040c03101c0c60201c41e4500b0906d0050744000c2c0340d038124007200a6281c006168241c400c240800c0714480a003403510100e5001c0304020f604421314002d6000b60f05450700302c0d486440481c0c9921681c0669500359000407080c00101140b1400100700e15401e408041c00745000d5650b003c0051031410040e1000c481d005002c1c0450305107a1982012100d0400d980700c00c04c1e150020071600c0d03880b06024882c010b480ea41490041d501d0a00265446951004000c0d100c40d440780c101400302003050000784d009107040c000260384c2001c680c00c1001c9258004c2c81150041c00e89080c01c4030180c0c411403442e5080035a00c0d60000e0480003d000b50001340c002d00040101e49805e0000200705804140d00c02c0e000580c10303400605841d60081000c0c1c3e080705075481c003d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 814683345 1250 814682095 814682107
    0x1170c130c0e0d12180f05190e090109020102010b0f090a05070e090f161418040209100302030901050709050109150201060e070f140405030d0309060b0a08060f01050d0b010506 77
    0xb5205510903000d000c1d041410a101581004102810745008618a44600806010030000c1c00e20617522070052440480c41c0c0325080c4890320340200000d131100d08040005c0b1b541038440c0191104882c013038610800c035a44030076490781190307020b000d94142003005503500041450130b400011808400030b801038024598400128070725074826004120080800f5028405909000c0300c603120361241226403100007007088080c5c0d0781040c86a800d001ca1000d020045604002c1001050411450742107002940300b40d0800004034152070310345420352424003584005840f17282102005081d104010003842c20080d2541c01805541e8000c1301c0c2000741c0e803085020b80300d41071410700180c1c010481c61304a8001003029500300300707007a548140d190808500550b100200c3e5030404810301c82600807809034991581089a2200f4803034402d50020703403414000d910204da22004000443c0d00c0f07000d00e800c20324007600b1600410800d40303035007160180100402e4480d0071300f000342510785012900041c010144a441c000500d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 814684595 1250 814683345 814683347
    0x5011a040306020325020f071d073906230c0304061401090b0f01080415020c010213030b25020a0b0c090916111b040902030a05100501170c130c 63
    0x5207021804824028030002e807081c2601a646208000c07410545100c0c0540101d2182e82c02666070619003100c440d10036107a12b94084c00e8400d105079401405000c12042d03000e46074441e0480c1c0000c00720741d08210400f1340d140c8504041c0c00f941d013581214510051140b040c2160300244c1e089050b031000c0c1044800b80c0340e45552401d9070180080c1403184224007124400400c13079400c80d0b40b000c00151404c4801c0c01c2d0750031b80e91005498000080b10054003406000d00381141042e981c0e0020424144060700044c81e20440600c0c1480c0300d011034100703580c80003500c401c200f0b000d56240405040c4d0f0f60b161040b4a840070849400a5407030340900d000905810f1401c2c0800c8030302d2480d00c203891100400506c1d4040d540703044441400c011428011034000940409102e00401c03a000c034151561691401103488183c0480007484041d00208e40220f8140c45440d0014020403001d1240c1d001d425a0b214001c525945007181402008400080145042e004a2107006143d51001240c02108003034401c0400e00c4400c0d260 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 814685845 1250 814684595 814684621
    0xe030a0b2806050f0405040f060b0d0c0e0106020d09030b0103061d010c2703020109120507031502030402040b04021603140c0f0f07081c0c050c0409050f0105011a0403060203 76
    0x120140000c40748415a100040c1d29007005094410507120201c0303c1d00312808000c142c403c29a000350446050b00b9284010a415800207000f05402800850422140c1d076030700c204000d02030340300e8011240000014803080340d051003101000d00701442c000e80881d0071078440000c161818440180003580d29104110a9915401c00042c00d1001c04001c01c0300b400d895101a09040d46400c212140c16100c08804065401c01d011100c02d40e034041e516035800904023100049500d0030510140d444c1e11a00b40004009001c500908a41d010303a90005603c9007003034811b000607200807000183c4074074014803580c5946d4810081d100401307605031602c0401901508502d000c01e00c0b83d15100031032030003580310070740d4803080024a40306c0b15910b841c11122140c0d0f54403525a02c80386600c010184280e0503814500c2d03464030038005010071078010010386803030f911003000007400c90300b44400807a0240c114800550400000380300b814014000c102c002408081030900800c820720607800010240d55001c408101010360300f0f4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 814687095 1250 814685845 814685881
    0x3031801110409021c060b070b0604090623060414130c0513090c0e0606040b0c0f06010f050117100603021602060706060f12020312090301150b190e030a0b 68
    0x3948040d5155140d0000034041c2d4480c9451600401540c4d1300305d06410002e21641c01164031542c2e543d030a102c80c59a401e40030f800098003a1303074003940314007652003c03d41c40e205000d04142000707131410400d845000710b202c2841c002411030f48140c0c5130064018882d400410f045034040c802c081144c0e00f050071880c003105102d4160b040355802000c040d640041e421a29030140301c07410b00800c0719014071030356030609031b92a0a08480080d080b4506020402100010001034000205080c5c15250040c2545141c81c1c03402800768400c2c2a50a0b0881040003a03580008001e01d4080d0141c10304821880c0c000340c010340c4200d103403003454105a07000454211030b01c0340140e00d100c1964010310b055507a0280f804d01001601c00b9008103101b1151182c0000303001c3c1d605807803048901760302801410b42000f01407541c03510303500300040c03198041d5210750644041d80b01d0709028002030030000b08955181c0032062000900c030310240020005220101855503503641e000268074400c0d551102045059958075030030000500d010b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 814688345 1250 814687095 814687121
    0x212031204110a05060f0f0715051e130f08090406030602030901022104030912020a080105040f05010c0306060203030f040503130602070303030b09040809120f1009020a0506040803031801 82
    0x34800c0c841045150b40c200b4000507402c40d0100041600e500c02c014403440342d24411034803507038100b104a41c581d003c00007903c2d4a60045801182c003255864079070040e544c0445a45043c1080c013010368401c000302070715458010000800303070040703402180e8910300807403010000504108004100740c140c0fa503882d0485d401455202c68295107a09050f190305003c1d401458800c055400344d4207104c1d4101c10001403041c0708582503640e465010f032070150f41c82d04c45013042d44181c3c0c00541c45000400d00340380c24040c45000358811980c041c3c801c0a1401c0040c2100c94003040002018148842049040e038000142c0c0c0e0003540390202001c01e40c4840c680076180d8854468080c91500f1140c000040035a00480c0f46803c0f00c0c000d440a00c00201c2100c20060500700480700140701c1c00d028000b840080c20402c00c1d85802d0100b034001c0364600e45040e404103282040141040317800c141c581414208504154010700c00410b019a802d0303080508009015440c1e000081c8280348806607a025084040002d401c00520035050b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 814689595 1250 814688345 814688377
    0x418230601120615140d1a0a1203090902031906030308150f0f091008010c05040e0702010219050c0c090a0e010f020a210b09010608010303020c030f0d2304091d0a0f021203 75
    0x10301f20504030400c3c403200c06100b520780e401d0028030034880c120721010455040d0380d140c020b03500384207071600290405001b55101c040f10240200e506c0456210348000b960103034440480514090f040a5001d1101c040c0f10307400303030610222603210307525503140c5401c613a8021500c8010540d01c55a40f41c1d0400b20a0380700c04040d60a02c00c2013010203070403000400550300414000c1c0304a035181d8030142c0c00d0340300740d48208850440c2d14444100e450b10034005003c032040450180d800401030080080c0d054a420348031460010358410030011412001d1140510001c3c1d81d18040d8104a03204001400d00340d820226055203100b040e49000c0c0d003464540c8244840180101180003d5843e02c3c002000c002c42400200c0161268090b100b2031403030001848200c0e04503840040c03d14080340e401c02c41e42011001001c03204542d800c3d0740b0b100354518400c041e202610100100042c41d41c1c89008400c240c5000a001e2030346508400c2101c1c020488020003480d8058042d1750070094848810708540ca1440b42602e007403686a0303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 814690845 1250 814689595 814689611
    0xd0204020409021e071106090301020705120d06120218090304270b010309170c010f0609020703020c1530100807060e060418230601120615140d 63
    0x5074003808041032004020300013142e0180006281c0d200e034000150010000541c1e0f5449490b042005150519000e00090b0900c0c9095407184d140c40c45154091002c054041000d218038091841503c00a0078144c1c0d071461441c0c2d2a402298042020034186c085498000c800150a1182041164020804042d200e00320030684194220551a4140c0c550103550606580c80c050350310a00607001500c3d0054000d40101c112070401c800c40741e0050b600c43d9059500e44c040c1c2640801c291040034020303c02d151001d230f5284a07901e0000c0c1030003502a4240c0c45400183e040792215940b2405661004483c02c5504800074003040c03510104a510003c1045443e802030100f000074044d070401042100d000364100c0b407240f612020151900b402886116401032000e1004103e82c140b0500300c83c46080050000003142d4010f2500d03c00d8510340c010346041e245031100c1c240049035a2140501d10000c01c00d080410075107042444155508050415850400141000c03100d0780341340c4e20044a800310090f40040055103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 814692095 1250 814690845 814690859
    0x60e01171c0c020f0d02060a03050402030c0a080705100504060f120b06040b1b0303070203120a0e0303040f0308090703020d0b340224010608070e060f0424050a05090d02040204 77
    0x5400c40422805440450131000144c1400280c0100f001e84c0104850304007402c0000860081034010026039045c811100d00d51480d4448017590000303000000f024040c0740342001c0a01105040e007002100400c14104410842603601018083c8008010b1034020300d404000180380015110744c00b8183e902070000100000c0304084074000b0503101c1c0c00789000041c44610101159124041210f101002d80c20404c030060f040705103401003560103c100800000d94000c4006c90034503507001102c0c08c4501e0003009584000b49500041e0b07259100000d00c00400816040d07501041490040c00703001858a078016001c07801149010320035005d20907003044402a144064007813030218035044030305003002d80201d07041d00340300c03040e1440c00400002c000c1d94001c000d03918294007140c540300010801c204001461007801c149541d80f000030f00300720032151841c60f107860030468201d4516941c50300d41d404d444c01c0040610411900a000e480c04d884150030b003d0b840b0603180c0085482c1107107013030009512601c00240428a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 814693345 1250 814692095 814692107
    0x180905030a09150c110f1212091801030f030309081b25030803061027030b0f09060f1906080d200a02040522200301060e01171c 56
    0x85100b0103d030808281000700544107031040c1d81001c1e00300025421020300908000040411800c0b0240c45140c61000180f00325090411b0b5008010001c480000c086d480c51a000c807000000d003140400b1a910303540746030ba0760700c45d99500302002018551607000704014802c8101c159015000380d4007100c50b081c0700b440901616035030130401c0a01c2041d521419074414180325812001503c3c0d2020350b01389507072918401c12009a10820b0554200f002c5022900301040c00c00401000030380b640e0000c5032920341146030250492000034010445520b0035410031407a2440013500b1038210082800900003501c0b61110029241d511510089025080100014500000046070818034803a55070b654007081182d5021030190840545044043d8040d24001002d8034040c1d0095400400442201e08002c44103d56006060034202d800d0341d0003100d504070941b0514101040d202e0701c02044001b00912070410400c80558501070143c5040d40c60450316060007102e0400c00120b02000c43c211245400b08030b10002420 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 814694595 1250 814693345 814693349
    0x100905030d02071509181d0a0b0613111903230a05091f0b060913020a0e0301270c03050f0d020c0609090a0c181706090f07180905030a09 60
    0x30b103483d00040d02491034403170300200b801e841031101a00b42c43c0040400c4500035240d007410100f02ca01d01e0b400c8400310361a0030803c50400a20440503c00c0901c0c11008200100700511080c0d4669800c18041d988801115000c88501000e48907600e220420350100c00ca00401b844900c0d500c038044440c0e0318181c080981030005108120f00340b410300c030655a070f822094844030101c81048080750724000381c03003010f03a007a0802484804060480c1341800d040100180f4030381c05885900e000c640e80040e8040b400c0f03030b201841010040064000b8002c081d80b40356003529a0b10103141c105081ca4607402c0740020454a48035000096821504580c500c0002c43c0115440f400781c0d0070440c1c094403d403441c2249505040c802d0b601c0480000b80007160b55610004d0000c0a02141b090803c100886015071511450b2001448800341c43c0250b01e40c0410303070305074100c07524000001c0d01070310300d540c07001e202c1f010703c0070000030310400742d504214100d00c11599410b030402c040d110301600200940004121529400e0b404404041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 814695845 1250 814694595 814694609
    0x102070507120201080f1810140601020115090c02100507090e1803120a090c0b040503161406071a0a2c0c061602040f0b0a05090c0306100905030d0207 66
    0x4015968094145485140b408020b000c95091000100402c9119181e50fa12506030389140c110084000b44031802c003881c403065004a40d40c3c036a10019400c0840904580c003613400e00081001c0614013081440b6104c080c404d009007039803075801c0702c82d03020f109010a1907100c256800c1406203040445000c1d242d940d0b1809440203c0e014500040d43e915030144d00065210100c80c042d5190400540c80c0b540b0f02c4100404419440c0d1711440b4400000d01d10f05000c100804020418139115401c000415003485018051070351880d29031203003884000b458401c02541054100d845aa40c0c1110f1303e8581900080704440411104940080040000301504521200c3d0002d140c9030807072070340b085c1503200342025041c038155180e40600c5800c00c007414420002c10a19485292001b10002d4a034005000e445035001e090000984402d840e44083c20001c500d0000351800716032103100c1c2c1c6070041507448213000082030b071072155900c6181d9007030080c02446d1003c05400c000d0700341d0b4400e00070440017035a511210b00c1104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 814697095 1250 814695845 814695853
    0x5010305120307050708070309260c0d0512090102012903070e0405060f06221d0a120c02060702210f011b11030c1e0d0e0901090f090c0801020705 64
    0x40d4403203207000704881c0700e000241c958a0030001c0d00d4480207850b802407a41241440800c0c107001c00d0f0a2022600d480101144140b001d0081c405030382d040d4103000098900398064003250b08600c001032000316041540500780e042c0c0d15181c500d14070040f40900324411a05a040b01c0380080c0040039101030710100c0348450140c00f1600c520359070b07680d01c0d40209000c13100901030360003000104034400d62187c0005d40004004140358054512010b080d00d12406160b40402d4050b0354400c00c52850504100e164281c502003005481f03240d840382ca801c100703c0007100c0c15408001c40d141c03000c0110350310742040d211141d8014203101014010b44c01024001d003100e07940310020344151003910f030400a05000c0d6002615043d503004008004c41681907400d2404201071160782d01041c00103020142040000c0c281e0200303044521181c1980880c203260604595200420800144d0103030341400340c0711744c91100c0c1114085c003030000702180c0fa240520000c00d1505402481059102c00001da00036054000d40750340c074041c105403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 814698345 1250 814697095 814697113
    0x2130f0e1b10050405040f0f0e03041d0c070b10030c2c160c0f020301050901060303080c07050714010c1b060905180a05071803121706151e030a05010305 67
    0x110001180036000b0001075810070080c0400e042c039811660b00032041e002e0204107034211042d24401e81e0b010842041c1903030700203e002c2004040d01456002030411000d000201e908105000c480703d40f181850240400c0403800100b400350070001002e00055400c07403d0306080c8c685601032070028102040d00008400a407108681500d110716050501840c880e0511070691840e8101c2603415000829058a96801c000303900d4bc00758800780a03d03403207640d80d0400001c511b810351601401d030f61070140c018185130b4400c0c4006000640002141000e4a003d000c80c59044050503004071000301016200410002ca40482c10941c0d0302c000c943d000a640040c0c0f20142d98a40f560140411020b11003248039070001d500f03004c10921030060f4099604180146031240c11356580c2030b80c040350101315a000300c1c0d04908007034811160a5014070300819004000b601c411007401c140740083c07502d5454030581800d007400060200c12058105410a03204035018040644900d410920b29008020034802524076000305488 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 814699595 1250 814698345 814698349
    0x3050709061406180f0d02040509100e030a0503061912240b03070905070c0b070c12090302010804030806010207090626060405070b03061914040f0501060c02130f0e1b 73
    0x3621310440e500c1080180b03000a55080000389091844080d8100746281e5170f80340982c886000e40c92241c100c40d030007420f80c40768034132201045540f4150040300d240c20500900d44030351f5000e07044030f80202c412a2070801807141856a11000745d141d0f441088420b4005a41608200004070105c080070344078180300d900d07200317230168179016900c0710100d00380d040d000341d8820710154039036502181c0c0007220340c030340ac00307a02c0c49580c3e8001404809491440100303400480c22410011031859a0300c07048131b01d1a08014491850b4000b03014840c000e0001001e00c0110000698103900c01c102c032000805c0b0218082c8032156940010803c550316620200c103401b1501d5501585010000400314041c40e07120b0000d2008a2910317415610a03080a4100d42e801400111f0034400135040450000c003510103a400181282d00c010100003c51740d12980c0800b5641c00c0500412034542c00000e4058101e4040e500142021480701c0502c009101c1c900d1f254001c1d40ca04400070380c00c80000640030440c41041142240012032100c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 814700845 1250 814699595 814699597
    0x18221716030e1c03052503020601090c030b06030103080313020a1203021213051003060e010b0405091303020c040b0103020705070602150c04051c21080603101802120703050709061406 80
    0x1807100f1401d00070032075007400a44207a0050140c0c440f180c0e070880341811480144600c0c8824044103030016404500180180070350b507c5034030580007903401d00f08030324800800416403d000510002d0910710012001038581e03142c8420b150343d02ca42c001c0c410000d185c3c8403040c88001600c840c005034018030070440c1800c2c259900400300c0d40b9294001d040010f0305450081000310308649106298209a12440d0008031711100704034240c003801030030b83d0884d00d41e400d02c070a100c850341c0300034140a0070301c032091940c3c404a50081185401a5000d440102d040100d00005801070b00c10010000e207648600c100c00114640d001c0f8000301d205410301c5411501c2d46840701c00a02c0781c0650b0140035880f07101d0381003444820301016282c414092149400e0708842c0c0c404030802119001c044000400f26070041c041109514042c40700d10189031102c00100400501039008040446500c00020300490310101030444e44001045000000d5a00c0011103420544030308040b0007a007542d01c94680210841c01414000d850170030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 814702095 1250 814700845 814700869
    0xa0209091906151d060d0c0e0103080d0b040b09010e100e0405032a0c010c0311191407030507170109050d110606040612030804151a18221716030e 64
    0x100032501c4c1516003000704a00caa4007100308031450360404100080010703007041c030540214001c06400d600e4084520101091302c424041a6101c0c62405041e00c00c1690383d20311460641d40340c681c000da990b55400c48880d404022940040d43c541e0484c07010801081000002000400300b4581e10424148500045840d070701c91a28551101ea040b50041951030352145120b02c2c1c000d406407070015689032006da501c1d800c0c509601d03668070300140d54018030010310402c1185241d880c1d4600e001841d41da4034584500703407520618007885c909490041000e5504583c00d40258600e60341110554421405124020341403040700e80704031600d401408000344c2946424440c86044400140c44140d00141c0c0303039411204100f0050003100c644501c07049218000c0d205200d90030091901ea4a582c0441d108801040b09101c800100c01103222100c901308610003070340c141c000302d8412540d900340440e0102c51078804200d400d040801d580c101c80118a000e00f00d8000f280d0059041c2c040d4541c00b01d001c0440c3c0030b100e5081489 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 814703345 1250 814702095 814702139
    0x3150a0b0402040b161b06031a06031e0c09090708220308040b06010c0b0c07260f13090c0e041812111603051c030209030a020909190615 60
    0xc2c04420990186001c40c01045842094646c51000c0c2694400200c841581c12200021b695001002d2034200540341030400f882040766828151715002c1020201d840240050404450854000c2107020588000399143c580703000740010141d1610460003040140304a44840c0680c1501500c1d040f0010342002e0040d00c145c16a41e920040ea407684c8800b2110140982460b04001c0200343c09004a60100c00b041d005603203191070349030340c1d404608003654201c20110450784401010342414403029850001c441c10066251a21a1942a0907200c505044065404291402c0c14001400080c6a1200d003000c0540001c490401c1101c41c5845c02c072040210791030000340840320b80030300c43c1c012900440c881c411380d20f03183d409c58680411006002c802c65a090344101d89540c000072201c452155803082d90281100c0a280031410001c0160000fa900c1c0c2c2903517030180c080c6056801080c0d142c841409032004035804803049610881c4a8a802401030250320310b46050804407140200350310b0b103000300030346081c080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 814704595 1250 814703345 814703347
    0x909080309060a15091a0d0302010c02010f020301080d0807090b040806040c080a02100305060307051809061311010f03060816082a060c030702150a140f0304060b01030b03150a0b0402040b 82
    0x30451498010b14120300e0010240ba07801d06210116947c00e624110303030a00c04d03400400c400d0042e0300040d0035254942c1d03888186500500041c01100c5000a082107581ca003840c20300c004c0d480d01c000c103413050720542d0041c0404a10006c1c0c08100c8040001c2c000c0d0082e482103c445d01070030703590900140c030740080900081d4400c80951141c01e015219400890f0401401019140902c8c0c1d02e200080d801503540d0300e030b113482da05401c2c20030010311000d0203516409804585402c0c268005551a040075400900300703076050190301d4094040c8984258004c0c1d01401c40030003150b000c51142c50b96a51207981500c18129584910300381c2c000d0342e000f40c040754003082d61451612800151544c0410085421240686034944010301590004d82e407410100030702d00882ca180145d513101e0040380280001501d00b00c000d186001040f501d044940103a007101c2e4403e402400005014a103131004030302821f000e400c1c80364940b080010740c440202001c80d141d802403401003070400c00b52401400b407109a0081d4032901c072032008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 814705845 1250 814704595 814704599
    0x20d020717060708070905030d03051b0307020a0b13170d0c020d0e060f0d0c080114010801061d040b131a0405131e0204020409050a0e0f06070c030203040909080309060a15 75
    0x10003109000d412100c0c50600d0906e4a031200e0110703250a420000c0800065154801d110001c00784121002095000d001e00324918039004902a50714100f6000042090924cc00099031824648178401e88181c0d001c134014046c0c000a03002c0790401d400503426010719601d02001c00f4150750001070300580c1d03c086510f03601407024ac10b404101da40c1d003100504001c50082041026460090792080b1010103d40d40c480514a5040c501358030400e4685d00f2040b4140030100c8018450725400056543c03200761f40c81c00c5a000c0c3d01041c004180503001c030301e51030350b0001010800301c03d0100d550f8002c800b034800c1c0d1481e26280001e600d01004251002170f0780510300d865002c00c2200c082013040903c4502c0b0445500a082808403a074041800c1303900c0360384440d154642c1c4a09200215101e4014031520000003402480449503400d032158868002a041d0014090190040002c040c001d1068400030805044204006003a50400444a6004451640c00b80c0110030001d07a07050710f035101d8010103014240d200c8406034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 814707095 1250 814705845 814705847
    0xe0604020f10121d070909080d110712020c0f0103060e0414120d02070204050106210c1b0b040317040b040627030c06060f0315050c0906030106020d0207170607 70
    0x700300b41e0b0000c10000001100b00000180030305a1030803000c442018108004100940c149507198104407001401d004074600400c810505032019540e1030f803800616141156581d204520540d034000302072510180e184d00c00c503a000b04403ea500a01a40c842d94507a0704040110201c2d41c4074021406044200d4000c240442c0b40c404c0c04c0008050980c045603204401c0c9101d43c0c5958100751010055103400045403c11800c041c02141c0c01003101d41005424000708044440c00d0104000744c00710f4896580f6111304080d0b1040e0180f2502d40007551010902e011941860202440100c40543c00300e41c032121180d1010841281452140b500403a280880d62500e5407050041c05031720150402d071810043c08a0848000a400d01b2a41840303502c40d080004a1482c01ca826256a81d1000250034a600d5040020890303200b1640c080c600080c200280d0f43d034a61034424104d00911101c00e411410100000c95080e0700081c0d90b40880540b9000c480c40c483d5240310800015001e641e024004ad00711401140d948c1d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 814708345 1250 814707095 814707109
    0x605091522060c050714060132010e010201060f031a100513020702030715020d0908060606040e09150408070302061308040314120a05040906050a0e06010507061401060e03010e0604020f 81
    0x11400320b10704503161026649400c1040a169880c6c2c0c4100d4018a004000e00d03051000d5005407903500a0145105201c155414052003141e049014144a038100516600307a1007135001c80c0282c0420300030342c1c2c18030340c40e400c2c00540c6440001042d51200d2201700800c0360b541c42100e00300110368001305a03070640f481d07000e072001c0a13404c01d07841260141300c0d40e140850a0301211924911203841640201481555480f0042034500b1a501c180107a42000c1e0520078141c0380c0d001142c05490403401c51080e55100c1c800780c18a0700c0320341111418032622190601040005040084c1102030007a400c5401c0c0d6101c07510009050090721400a080701e07008c000030030006002110115581e001c0380700745d464194a00c0403645d4550f0220601100140b0000380901010405203c2c8602a10065a801d00200d05002c1e034130760106805001d00c0c0c180b08000c9100c2c020003140e030308440301035481c98403221200c2d42e40d00d40140c20300b24011842c03032007942081c400850303603100050b400d440f8a4000740307080d440314050010f200301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 814709595 1250 814708345 814708361
    0xa080a0c051002130b1315081e010308041226090a0b03101203110105100602070e0405060c1e07030806041d060403110c180f07050c07060509040207060509152206 71
    0x1218549036000188440011040a2085440d0300d601e08d1500d84501800e58a80101c030074006e40c5020f9000501c003180001c0150b03800d84140408005103c40d5a040540c408908400000000a44103100c00700002c40c10002d0030b02c1050940300c034030815490b400305400c64003080740d4400b902844590200812000135020780a0540603007058030368800308510301c03070171740d2001c64030f55503810f0340200c3c2046429410442000149180085095a81400d655440c1c441c40045c0008009000100d0580740d1594140344050505142c607440c2a81c4032580d14024084210444e1141e218501c0c01d0010b42045403005416000c0c0382070f40d00034007000c0c0d07603540d0182c0d900010404104824405c1b43c000c0034145d01d42d407580449484180d401d03032800e45880c03c4442030840d002480030b41000300500250f0848880001d0110a46220b0f042c45500d600c0d1160102d0000e00410324080c2010307062000340141e01c880458042c0c010710070b1641c88000f5071f40700c1d9041030425000d11054028a82c020840c140030880c50740c0401a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 814710845 1250 814709595 814709617
    0x10e0402131b0306030b100b070219080304030507140406082e0608010e0d110703030305060f060318160807030303110c150915070f0c050a080a0c051002130b 69
    0x48840c0c84112004203050009126004030744e07500c40600070711582c5680f882d440144003001c0c20301141042141c1915008045001f8040d0101d40d003407518004560f803058020345900012203072915601d0030420303601c0b01c0701d00c00d502030407006411030f81761801d02d03001c0c620070341c3da51000900f0280815081d0307601c00c0503040d030300c942c01c0001c0c1c806080d01880180104402007030b0396000030a07030100c540b40c1281018001d26480007848010701c04c01807861008115101100d400d414001403076520600824992540f0560b083d038041c00000030031421851a00419880030a1803003101c600c1203183c1d4503488501c0c0c00713008101040d8820b8408000107480703034005110240b001c0ca40b580c10004030301800786c586034902c14900c00d080004410444881001c010864490780480704907601030a000c0000782ca21401c0c66203a80c108421402d280d003e010007040306040c55681720b03241a035140c081c0f4134000c1c120b0250860445443c001e030703041174010704210700980d0340e51000070000e0604a8a0001025100d0f80064102c00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 814712095 1250 814710845 814710851
    0xe031e090d0819230a120524060a0917030d02120f07140409020d02040b07060e0d140307260a0c090603050405060f07020a15231e09010b1905010215010e040213 70
    0x10301980864007e0303501450305209040c005491440c02030804240700c115090203080184601105160700c607000c6412500680601104072010032040c606521420940700c0103e80009030101e6607030185a0418030600e1030754034504250310765040860b801164039142203c2124284000d1290503c5580184401031080c940103142940d42c510440c44c0350407600040e940551354005c1442036001c140b0220580c9c14140c84c1000c10f90480c0f1101401d03a0201038521020406004a00291001d1010380c010103e130000c0045905d51030000306c20405441c048618500080e0390840004496000e4010345000e2903024020300000c2e9100909100ca040004000c88218412108040c0100b07480b174001000c912280000407801c10800c45516180240b96180710309081508000c2102040a43c03000440d01c0c3c1c0c51501c0441c40d03803206000700d4050081c01d049180d100d03d07011822501e61140c400c104045880c281c00365403c0903200c5840740030f40c41d403d2250301c280f00d240c0d0000400518003c080c04a105043c05000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 814713345 1250 814712095 814712117
    0x60d060e0a050f0102040e07090621020f07111002010b03190c030b07020c09060604030f170405100206011526130c0803030403030e010e031e090d0819230a 68
    0x6600e030540e5083c03000050f0b5070024040c030440c5c2d190000340b41d100d2900c1c1040c0d040d1501e0903200606510b0045600298002030000000c5d4403200390b0101c5420350000d554040c2c44d50380c0e90610390504907640640c81e00c180403410742c00010034018042c090400c90001c0c06090207540644284ca02294100b0007100c60341040c80d03000c000100d40c101e0550081c2a10390080804c3d0740e5607000c0c0120b0172400340007203120303103024002003000441c41b2000b055240e502c50052405134071406000e90307040c00340384c1250781c7c412100c950440301e1903070010300da90483c0c1040003080050090143c080d00e5a41c00b0603028045070858140301d07030350811030f005429084200b50701910710062240d1608009016550042c00041e00000f00340420315038940141000c0c002c060000b04088241092402c2d0740c0d10465000305c180b18041031150340080310060070382d000950082c003030310342040c0b0030b15182036507a01407294446005d0b2042c8000b110329100b07511071140c150043d4140720780d85070322140102c200d80114002104100920795a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 814714595 1250 814713345 814713353
    0x706030513150f2313121d12010c030f0216031103090315041b0b04230a030b04021e06163002071a0f0a050c06010605130e060d060e0a 59
    0x100f40304e40c11310204040145107007a16002c12218098504e22420101e000e03c040403038100709980892404500b030460038a41070915880115824161890b8020102519164503200641046035858159a01001040f403200e51a004a0040c00b5005c2d080d62480030f09103001a02807410183d90003100000c807414152688002880c040030440988903500c1c00030103020411048500d003c1c05510a4440c00d0001400c1a040c0b4005000714403504a1008449580840d0034103810a0b015007a040980300b540c5494076803c01481c5900161012805000414141d2030700d0b092104540d1b1141c08000d152526040396480c82106035001600700b82c95101c240300740e8030740d040e1110100d032104405181c03079881d6100003c0c0f40a030400ca0254007410ba01d00da0300080155500c190305c1158030403402c4040507030711640e8011048130b0f40d0240b10113402d0588203000004c03c09a800402505c4060341e035004080c0507507282c1c0d601494801084d0307555078200703003400010000610302c3d81008200480d030204844d6500c55a8507 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 814715845 1250 814714595 814714601
    0x504020102150901140901090308070e0a05040e070e01050109060e0f18090a1707050a14031201180b01051207031a060a081005030d080406020c0c100e01020706030513150f 75
    0x43c1c1071907141e42d600c0c0300c0b0100040072084c1d943c0c02240c0c400200402c0d2200c0d18094050403008080c041000000e50480c0c005a55500140c40980805081008080741c1740c3c3d0055070b9081c3d41d00514a90760b40c10b100014070f640c45100c00000380e480d10703902c622240041d2828422030390480200d4660104000124980e090303801035107948075074912001880055810704040842c140828010600903500300503031000324100103078481400b5031001410181c0e045002e1646d0860142e0390103c626a80a40c000041d0072800c0340c2c80802c2210102420000481c40800540b198031440c4c034010030307a68811000079a0180240d102d1003080000b044009440a910800030310564405140500810191000e200c010b50382140000c014000945c001e00303143e0700c03000002e40102030092004020f560006031844004c3d10a00c140070f00c0740d102500c807a03000d42e05d0308000340034600030003c130034014400c21100003500340c440d014242c0611400c4134401103818260303d0b05100104000d140c20000e5440e90541c0407a140944 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 814717095 1250 814715845 814715851
    0x19030f0618090b010e06030304271d07270b030f01111e0708071203090b01120210090e01050409020a0f0b03060316080d0f180b0d060b0319050402010215 67
    0x1031000a402e480c41c5403407180e0040c107170810410308408200300080ca80300081214203803422101e0100340818040003000760701c240e544180034050304000c5542042801c0841c80044003c0c090103448149803a4042270441e034845101e005080c0c034170360001200790280c507445284013150140540b0400c1401612060079103400280358141d00d00002480f401c1100320165230351782c064021a1062921255889200c020f01070b000003e040d88185903d81003450b80203902130154242e016a01c0e011540c1c2d218060380919140c0344040c1d004101a04121408510420b030040c203464202e0740307102e6580d007044140801811400c100320f070058002d5101180c2111b11501c00702c002d02c01c8000352a40e0340b40500134113081903128a1414514480341c10144003150000c51186210700f11490022500a07100408466117010765031600d02c050000c00700800e9003030300c0030010030490402410511510b035403600003852900c001c99220841c0808400c1c0410038500c01e030840c07074100740140b0481c0d9800c05c1c05200c40008820136 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 814718345 1250 814717095 814717139
    0x2010c0215161101110a1205031906060503010905060607120f03020715020307030e0304120605150409060903091d06090403090e0903120a02090f040f021e0405120319030f06 76
    0xf20a089503d6a1100f0640c003200e0168010b81140c500fa40d80e0040c0c4c03c490384051b201400310110001d005201180d503030b10340ca02e00c003c5003800160f49c1c0b41d40c0030304950f0003030144140c030170f00301000500c580c2002d50455480c2c2e0303404000b00781c45c820100b0089030701841000300d060405400b000160003050b00102040c204c10740340c00300180e60381042000502201c0c0121311140c0d864000b403208204290011507003004454011201084036074807009002e500705c03040650b855100d4640030215003072105560000301c00501c00d44400410b5510746190b8503655045940d1049103408100c006941e0703041c1003a446801c1846810104803960300c0d070341c43e005501001c581040b000d620104201500da285600800d80204540350214900740304c1d2404540c4035480f087c2c8950207252078040001d1000300c0c9a040b28880e108450800070980034410004149a0007031007800d2141180400290006102004840c9200b4015207840c0d01d0030103c00099003d0030010b1003034191301d82d030303280c00190340c2c0e0364041011402807213 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 814719595 1250 814718345 814718363
    0x705010c023001021810080708070c02041103011202120714011206080f060403030c0305061c0203120f04030b060306060918070e0103140d0801081b0d0c080a1e02010c021516 76
    0x385c001800640d00f4042d2500080104640500110035000030550380c12451524008142042500224010300044482c040040740000000a03c0172025465041e03241d10031940b00315482281c040b840c3c1c1d80c03281c6004103405150300034503c0e4601d41c01890000c442418801c00856425990301c0304034141140c1d03014079005030b04000d0400c0109589441050030701d15040c05c0410840c01c21a010540c01c240411000c1c403680c001e8a1100c0c255034040000585107000c080c8240d0782c9410001000d0f980350090f00c0116200080c80c0081201450081340303032807164202411300d0406986507280e0000001103080d4103102c0f402058004285e4812801e41d09020718015418584d400560100071407400f103c0f40c034180e081001281c0140300803940072401c002d00310610140c02c40510300401c00100021004100203218055110001903154404582ca00003a07004400340704e1620884490000040c0503044000d001550794103a000052820001c0350a059954850b2581044020541d03c000310f420300307400340d030640c5c0307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 814720845 1250 814719595 814719637
    0x603070206181603081c060602300d15090c0314010608040f02011202040902071101020124120f05190c150507060b01140d06080705010c02300102 64
    0xc042d007001d03902d89201c0d0002c0181151003000281d40312501d0000621591001900300c440d2204144c0003050102c011801304602d554456029540b500c400081001000c15000004d850881c070f140c840640c81d41c1803040d1860140c9450f50032000b01b481d1a44034213403400081000c280020f00303100f48642c054054a00003004103003c00c0300150b00c2030583c000410003a1100400c000207003200c654000c405e03428208562040fa10700780b264041d008940003003a5003807010882c1c00c14030640c5c5024a02600c801c0c0c0007007142084000341c41e5a070303800494050800f01c03108c8908122282e416140100020b00440301003000e141d85996085c28801090f044d890440741095864051041090b2210020280f90030144008800020058014026a075014000d10340d00c1c0000011030340141480c0c1c590940010701c081e41d40301e46031b001303200501403806282d0b585d2050000c041005c0d40904c118941070740d00142004041a0001d03189006062050920703209002408044e0b0300f178803002d0000d0030617001002c400301010300f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 814722095 1250 814720845 814720861
    0x132f0c030a03091a040302030d0c021c09050a0f05010f05091c06091b051302030402120f0307060f0b010c0602031902130501080a05070f08090c03060709091a010801060315050603070206 81
    0x301c0b0030705001d0105a44c00d0100094001040740c1d00b100c0c4440010402458004069060541040c0412401118101074049060340024210282e8404944407845652900b11821941c1481d0040901080540862247c69405a17025101c0320360b004017400381091180354840125441c1e00400c480e1542c44400490402540d494030600d000040c03e1400651450600020381110304240320030f00b0554000007140070754403400c1c0b101c620850603030219468420a019120703074907807103c042942d00380d1505440410351400e6000c0c1460101c0c05030354480e00990a07841e118003c1d480a0500c148230b20034400040d11910550010304111112503008030495032401d0000340c100013008000c1801540f40030704120300b05420080741d03406041c541c94406100c0d42c84441d00c915180a42c03034003035490710072136041101b00c0e5485481c0c030090b03c00049060040403005500da600c031601320111140494841401484881d200ba4441c0882c0d80091000803085c82e40d84000c01c5407a0700035a820070060f00030b101045159 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 814723345 1250 814722095 814722113
    0xf0705220612110108061c05030705030412030906090b07080c010f05090304050f0a0b03160207090f090c0602161404060b0c031201121709060702090702070302132f0c030a0309 77
    0x1d02c020b0a00c0300251425000054800c915180100e0f44070305e150007d802803200400640301c0484d44002200e950740d49a2603200b203100d1055100301c00190010502050341c41c4070380c40410481d0000f65140c1d08020556a03009981e0f0801014481c0940d40d0b00040704c1080894003826006008030009590340341e0403c424011004200311085016403810b0000308094070061007220b0313000b034542c044504030480d03400c0c1c12800e10307005034031401d016814902c0182c0d4003461540080e005500c58146481c0d03c40cbe030b911080c0e071160840d0100110190000c0810046000480d003081100c040051001903d5503d4118000c402c2e00300c05107427170442c2c3c408280d50082602134607030079024100c60780d1030048100b03d40c3d032007503480311440780100840711001c00c851415880c2c2c107007601d031441d0340185142403610f40000d009540c0e56040c8010f03032040c520300c040c0103d66415486009560004032144080c2c0b0159007202401c136400d80120403c0c04001084107404a40d8140060010110306a40c0860f21410750b0a1103554 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 814724595 1250 814723345 814723373
    0x50303010b250f0311030f0414150a1107091a0120190506010f0b0a050724200a0c0b0c0405030304030308010806010807120209041401020316110f0705220612 69
    0x40740c6e10811040303007030f400d00c60b00fa9801c07608044170b1083c01e1003000001c0380f065049104110072900c03000c04c543c14007035041002c008240010a040720380c2d003036880144c10182c48205c2c460410341c03240035019a080707510907800040d24520001040481246d0718050b13924220100910118420300c0c2e01082d810080140201801801c03d110566640350510f01461003038070071401c08000380000040d450040080000814001c51101f010611100c114082d6000103846001c80c14052003402020081d0004814415580582e00e07d80c7ea00702d0b2030301207a4030354454000103421030700b00c42801d100c0013500b60b0301000104003440c429a40c8483c0c6506d00500940340c068181c000c000c0d10f42000c4400d1040503041e00c4125000b17601103030a464075848034180107a44c03920b01c0c1458036440d4000800c002044c010444d008854803281d40e07501c0388800c90311132016111415245018219000380d20204402c0c81c08009600d0400c20f202d0260365214008000e1604965280d0302c4104d619105040311402c2c0544500342040b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 814725845 1250 814724595 814724627
    0x10b090111010c02072903100e07031509090501020c010518060f060303070b06010521060a12020a03060203060303310b030712021b0f01060e13050303010b250f03 71
    0x81000c07143c042c1d194031031303802029080340f1054a040305c40e007000c140342c0ca5589032941c41c4503540d040100000540001d1800b0300002c0c100d030306010442c650f100c0e00c10442c01040c103ca1704101c090800c81041c0c0a81801c4009030303015034080c01b08607074071710f000c1c07141500514080003079072003455001c403100c1c4c00c2030b4000b0b211501203803102e8104074880e00c0c040201c852490740800420310707a960700c50060310640502c100c844983c617800e40320001c000050f605501d014070402c40d010b4207110764031100603a003d4030b04a802500651301a204100041c001d401450700100c00a003581c0c10703c003225240c0102c840e00075801240c2620362050010b52000446075890207410940720061071860700e0240544030100540c54031401a40c0091100000031130181041000c03000030003550000c0601c03400d064040c003c5d50240010040201021030300c5641c1d130005418400c1d5008001e1400e5a2a01d000c00d411500640700050500b0740c00d08049440c85074910f05450081c1c1704410460145510f4240242914882d000c019 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 814727095 1250 814725845 814725851
    0x82118010605090f0a0b0406030b0702010c1b1a1b03090a0201030b090919140f0c040e031306050d020d0c020105090105060f0f0904060204090c090812040e010302010e0d0803010b09011101 82
    0x2218448070902155404030545e0340114501c05e1000100380240340f00d60010340071072088414441156419042682e10b40c1403a5603512002041e101240c00300c150911000300b861960324034000c861085100300c103034000e80c500d858048071003da0301c25082a600846001070340741c0020956400f19030b01445800000c5205507600c45141c5000584690f0750080010252840e96001012004010915a9001d24960f084050f1180703031503481d0311965a8240300c821540305c3c40c00c1500c40c00140c10004240d80344152070780c0140c46014605282904c0550006e040d4800c8140c0802043d0b40c804024000d009420f60182e000241901e0110b21160031120040d042900c44c0341d090031402c040e5503903042d90100003c4110307090402600c503407508038001e00c581d0340300c401042c1c1014001032503241c11260b408222030350001510408508000030750b8283c41503000e440709684010b4018030142d40300c2c03150a2680240a071803844004000e40312a0041d0300240d000030028200010003041c9564810a104000c14031b05000b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 814728345 1250 814727095 814727101
    0x303070e0f030705040e07080f15012d031104050a1506030e1507080403080f010b030109091a01140a0506030f0a0903021c080f0c090a0308211801060509 67
    0x400c0c0588040c0214494004010350980654042c0145001408003c2c400c12100b642211400d44410880c8911f01450180c8046100298004242081e010180031483c490390b0f8280103072100391040d110080c4004013581540110300d00710b080c505102440c0035002000f0301d1280703101000140c1d06c008023401442c5041c00b0384502120103400540f8160781040c1408581001e041c02c0e414030707000f080b40e14460a10000340500615541000800f0b01460090351104242d607140d0210b00c1ca200000c0c03040f0440940200010060010a41d101c1540f442c0729070f200d07041d080c0040305140340052080e0880021260194002c1800340340920304280105815036440381540742c61074541c0d244807801401076150585031044901010710900210300260350031a5980f2507100d21a074000c0500c007046840c44884642da07000315803514051415075071402801400f418495003103984252a6400c40480d21640d6050b00c00300d8403480960105a61040220125648442d1910000300e400d6400390343c0800c0c0500c0f811014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 814729595 1250 814728345 814728347
    0x131b0e0606070218130b0408090906060a0504142706010201052a1e16150204051e1f020102180906100302072f120606010504090f0b04090311010c02030307 68
    0x8079400c41c0724000504c1040d03482c0300005640444e07074000208070150a204104c01c1200c600082c10300090280c0b4a0303401e95a41c07900b4845103210b07450074038002c5182448200002d000405e501c2d00b02e0800038184070380481a118a84041010038151482c0c400000c10410001d940e09200f02684203141c4075000000c440801031251f20040c4090040604640000d0b50421600080707203204181d1940d085115039500682115010580d0143c2c41150748581007040048940c02d00e000351004c3c1e400c0100101c888818004107454074000c4c01092540002060240d074004950100001c00108850340002d640d40b00041c85410b20800c43d111000d1040b28071030f0501101d52074800c0203650880f2603003401039640d03a160801800105400100703090701c0700c800b50a0100400c5845924403034906c142c41200300308140c40d60698407590112034460000d0710520040022040f250060700d00c50b681e107440001d011101e1000b140a482000500354041000c03a804000c4003002407003540380442d8588044c4d4118100004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 814730845 1250 814729595 814729609
    0xb091c140a080a0917031006080c03060f011106090109020a0503010501060915030b100c0b13030e13090611070b07020c0a18020d050f0108010e1c08131b0e06060702 72
    0x408407081100c110001403150a85501581425800041041c1c0c2c56840084070301207a0f10840381e114000b040f41100081d85400381d100d071401110008851401c0d56962814464640500c000c5a810004420003505441400303101c21401100e8440022410700168014000c1300e1401d0381c40316000760b02d46001000b07215488019513040d11020482014080c0c0001c2044001ccc040300c504c81c581c4000c220800d41c0c562030f00061405015440341c03407049043d5940b0301941094010b8881c018010a8040e142e540051504940e01203d042075220002030039405034031014101e90940c0d60209100d4000503400041c40340c8460282c2c2d1010701c51004140f40d913080004100e0508840c460744002c840765076060f90340c40a80750140c503171440300e0200c104420300c0c2c10503024200724000c0c46030355015443c01044000981011498445a9004058406c4440003603c0c00702c40c079460003005500d2000380c0c0c0c440800050850403a0b50b110281205142140600b09200e250707510001078000e40c41040204290b00058841003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 814732095 1250 814730845 814730857
    0xb0f060406030905160e15010c030c06050717040c0302030f0f0a02060f0417210a0203041406130306090b0f07080403030504050c031006031104180b0a02070b091c14 72
    0x481d0100303959105140ca5842c240b130b9172020038002d40e052203010aa211408102e0307445401c0c00340f018880b0321014401529203002c800300c0580016211201040032130203540249800c007540e40381c80012180340da030380440405419a01203034000140c100c2007040d40b50401458200c4e140340300107800244041c5023000d40d50244900001e000d0903001c03662a0b2090a0740c01518014917000d410703d654802030158280c0c442441c08488010006402080d6405100780b4042e540040c1c01c6400a51274076081a08119251030a00c2d600c2e544034804018428243c901100c1140c02180b240c01c003c109280a0700d003007180400010310540e000bd03e880704002c141c69100c2113131074010350903040001d12502c40303007051030400d03c108081c260036216240c00c3d80816030895208104a034010901d41f0504c2c05600200b10582d20f03200358540b020103080c80c0e4000030811b80404140c00c00042c280041c03402101c2d98480703007401400c442c00d4a171034104070b40084003466030a28a58040300c140ca00722144200700094a4070740d000769 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 814733345 1250 814732095 814732097
    0x40f061101050a02281214060a0603060807050d05010b0621090c060301060c0f021e04060b0903030901050d14010306020408060601030b03250f080303070216050307090c0c0204050c0301090b0f060406 87
    0xe03a00b0040c950103007600032041b01c2000d40a01c110703180c00c0903080072801c0584003a402240401000105584a0310504060f61a1079000d0083c061904040007421002c401090f02c40c0d550b16000f0030000d40d150402084241c1108010002ca401c40e40c81c0c8682441005021070b0f1103800054190342e09580b944100d90640c0c1070303400c083c4401c2989003420b040c22040d0b6000250000ca000302d46503040740000b118030b503500e6401c0303c080c00710945410816031035006840d08190594028850060f640d0300400c040c0404240b0b40900244d40e40c001c02c1c0d0075403001020fa01c151100d580c0044d052080c1101030020503402002801c0c1448100d050402090f603d8514034010707040c4824100341082010740d000302d00002004003050351601c0030b413120107051300c0b40d0003520494098490259048da0b1206016129000c5903001805031501c245424140781c060000441a0342c1003000280004005070389620038240218184c000d440c0e1250304114600f0221a01400d0f02d52044a00d5412003405950b000226002da50326 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 814734595 1250 814733345 814733407
    0x601150e0105160204050a1d0f073609120e0915040e060406022d0d02070303181407091404020d140f030d15060206041106040f061101050a02 62
    0x1083d0700000203000920350080d4003034100010700503101742c1c603007050398840c10314a4481203000244c1952655040815000005600107160400044002180c40b040708410200403860301c45002101c3d981c04203203092140c0c8100d54550a01c0c050010241d95100150401c0c02c0800500c1c0c54480058040c2074000c005440002d1112582c0d882c1d80c4941d08403c1d4001c03c0c40084403907a040616004020350000c0a080100b5100c4600b110b59854130590020044900f00084500d04105114188065409000e058082c0f649601501c0ca072a0320b00c1581500103409410f4540155204a641e41d0030f1400075813010b60068241400c2c0440d841c0841e400d25001681120030105213801d03441d003039030340364109142810307503026402c801410f0f50400700082c1486102000c04101e51504484000c0f00b45902d070043c03200590005001500155070b8421020543e900140340e5420030303944030107641e100340707164000c480000c1c0d0f00700044040080c240682034200426013019810400c003200b5241104601d0030600b800661 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 814735845 1250 814734595 814734607
    0xb0105181306020c010e1b060a05030714071709010f030203010f06110c030a0c1706070e0622150306090b060a08340f1409011d040501080105090601150e0105 69
    0x11065040f03070361110000009005000600c1b062945035068500d281e81e040b02da03d02c840540b0301c0d0200480781d101019444450550319030305804c0703594540b90007031142400300c20890b140c04500041d2401c1000550f90002030ba031001c070f40c40010f0840c2c01c0b50162030245801800103220443c04004948140c071842c3c6030a4045c01c2c11448440d00c1c0c400032001c180d405000320b82200c000c1c820031007080401d81c0c80c0b020716458894892402c0540d0760008452030000200c07516184c202034034000c8000e2a001400c0c502480035814016040d03012030003140e000b0074444101e0032b140702100c0d405d4000d40340189a0104100108103421020070514032510004072304004004d40000e900b05200e50030743d80d400003842492004103c0880004200c203440b900000045032503031030f0b0301038007d201c1c00d0700d291039070100050320f07080881a500560b40018503015102003105007449082a0340c8442c4a428001d083d50340c008111401c4c040080390821906030812049180c100305201542c41d0000a4101601d0003071800303c3c2e80300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 814737095 1250 814735845 814735853
    0xf04240b10020a05070501050c03070c150f0504150305040f0b090d0e0f06030105151201151101150e060105070f1a0c07080304110111030d1517070504050c250b01051813 74
    0x30bc140c190003020920b00382404100740c40c004100710305402864032160304803040c202c2c05464031b01440c89250314482c044210780e01c40c14400e410160304540305001100071202d0300c1c1c2d00c40e80c982d1002c56980500d80c2c801d1260000f035644c000340366910805c05848100c4404014004a038861105000d002c1c01741f02660517100d0000c210208480d408001d03001c0801da5035844841454015641405910000f0040c4c80002107614061180e4210012200c070444a000d180c0256526004001086141400814000c1c20040341518032843c4000f8482d440f038116160407514403545600300038000007031061082c40b0345000241c00c2811203800c50341001c05c50344103410079001211140c00b210312142c668000802c0040200c01148c02600300082d404c01069025a210041141d140006003823090160348000c02c1082541170992041d50407900021156180043c43c0c451100117a0050020352100c01292500700b0601c4817800c02c160142104403400f5008018a00c80b01800b000d0240c0404121054480a00108 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 814738345 1250 814737095 814737097
    0x50a020909070f0f0305010f05090604020f030f0307031e0203091503040203120c06100501030e070504021c090507061209030f030509070e010807050a0801140f04240b10020a05070501050c03 83
    0x3090f0841407070031102d4070399100703d401c1e880510084a441d824407a030228011004e001c0c07184500a170000910312552540c013008090712400d4449501802400914a4222070500c02045801d000ea250034006210f4040b4070301041006a42c2c89085410a0110300304999a4114030700c000141c003e0150345944540c0002828000c0d90250200c44042c0060400c3d07085d00c02090307541c414801c08418103800d0f503441c001901900c03c4020741100542002100344998034156014102004111a1480c040c41d840312800007200c113500301c00d82e010381c022142009002e501c11240c19088000ca00107000e00102560044e003900c1c0c0313464801047c036455100091030302c0e0040001100405c111404500b507541d45041654880c51540111402201900300105000e0814014040e9001da460040c0701660354202801d080903070003410071101801c88c0b00038a2050050702c1002141c00e4051000010301201850400c0401d0700c90008003000d43d0040c64a02010680120324042100d0382030070519a134103002440e035815 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 814739595 1250 814738345 814738349
    0x20703080d060b0307120b0d05060109091401110403140102070b060616121112030408180a0314100c030b090f0a090b04050c010807050c1209120a03021b0a03050a02090907 75
    0x15040c3c0401000060b80e8407a003002d2504025900400040340010b05008945010640182483e8003d034010003000e0200e0b44040d6041303010710300b05003405039080401c41c250741500c21002c042080c0807034180203009001042c600815240e000841c504145513a4820385c0c108001c014600c1500080750360101c5040094110f00c9442e4060100942c140c4c40e981c020349400600341c00d440e02442010100202c000c01501140e001e075410252a03800c03d2800c1c981800804030041c1000c0d0000c40210001002440351070791903041003461400f403d000e2405c40c0141d02129808003108040500740015400d50703480b0706482a0308a014450300f51100c0d511500e804025200c0742d10300800d00c00100c0c08200030b00a001c20b500e642200240c0e03e01650362503603d000c9406000c0e1104001c41904141580782d0702204c00c1c402400704003005440e05020a2034081500e041c06100c5200381d003d42c00c42c0105d2030441c283c0300e0040001d142c0c00c80b9083e80950035600e03020350790300f6110310090045000c5008104510010840480 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 814740845 1250 814739595 814739609
    0x2d050c0a1e0c021324030b04060c090e0903030406110313061a130b120307023604060b03070602030a02030a030f0b0a080f01050a180f0c030507060309170307020703080d06 75
    0x4a0052501310000805140c0071145405c01420702c281c4d40c030802452104d040369000254600143c40320b072245030040000204d503005018484d603001401c062001c0e40c003881510f0180c041d680360701e005d041c502e05484e010f04000e240c8070010410090034000100405000075007001e0001f403881030807200143c3c600704010300140e01c0b44c155000780022101c560031450b035040050300c01c3e40d040c0209181066032801141d07002541302000310f0300501d000b08038501e80b0924000c41c010340013014520a105c0100d01400b03950035650716440d0304002c01c42c0d080410450004100c1c61004601c0d10501e980001c0d100d00070f50728080100f40c2caa19248101804540000708103100c014140100203a458200e59541d840700340300e4405550a1400240100c1d90510801c001c01c0950714600600070540d556a002d41e00102d44d00311124280e01c0c00100c0450000c02608002e42903580300040d1201b05410304500002e201f00a070131500b0002c1040001e084d41c0410107a08032544810503544070984040900c002d4591174010751 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 814742095 1250 814740845 814740859
    0x3140907061701050612070207030b0a0603020f100816020f01020a031b090308160212150907300201120e0102090a051002071502012d050c0a1e0c02 65
    0x46051000400c040d401c59440e5181c84041150025800321292003d200311680180207100004c8500c0000c903030141e010744184140d50040b6141d03902c900700c942066414420182e40d54000344110b040078401c1e00c9034900100c0381c81c0003400a0400080151000030604403140a23a640c1405225000300140301d07500726214000d5482c1d004046004008055010010041ea1601011289030303900592164043c0c070303000907103240f81a40f01e418004291511003003c98121281c60b04800a410080c4480b583c000641c01440340941881c3e8051480c00b0081d03001014814194101c03a020101e551a151007207106030701b500c0d01000003d00058640360010100c2c0c41c01d182c1451080c03403a00c00b041d4018401c061040304c44030794650b203620034032440c51002616400540d20880003403002808051802120201600c0041403903246941d200c003100c5800c848488580c5505664202c5150080c022694040340d4078810500700707076690000401d2107010041e00362086400c0b84100300301c00d2007120500400c40c4c02401c50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 814743345 1250 814742095 814742101
    0x17060411180112110a03050a201801090606110601050906010e03060f01080613110114161103062505210108030304050c1507021309140f010b0301150e070314 69
    0x101440800f2048a0091a0342c2184d501c2e4901185001c1c2503d070494020b201e01d100383e0743e503080d003103c40282440e240d840c402206296583c0b000307210390a00c10b04610420a95241a07107040a86609030003000c01e01c80b50010380205c204000600e1030450324201c0303444400d82c0350303000161949a10803030300c2c607011b016160400c0103080c850712101f4101d51225086480640d40c0900314420500d94410050060b52030941c00e0351558803850b0300d0701c070082100700403501e0301c084166490194900841e0480f00444462084006850284252076004000f040044800308460a001c107006c440304c01d82d4424458045091841c008188103c4004007412884070f02040d40c54412041d501c0d00101c80483d6944100e880e4000c142c10484160f62420b452040c40c2401d00489608014850007407401c0c01550940d144070201c081a1100300d4015008811405015849801070b410707425100c240c100d05010341c1c100203c00182460200600046403544111001c207529400005c07400380641411022940d0150b00074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 814744595 1250 814743345 814743359
    0x30f1f1e111b0c09040b0709050402161709060304030f05090301140414070e0a1e0504030302030601270501030e0f06090f0d1b0f0206040308040915170604111801 71
    0x2041d0b0040c490700d12040070599504150b50300d0301543c1c1d049410a141201060000391041c00c606e4010303410b0b08012807000c2c2c444003c0b4040782c1000b402c5500f85080000100e007440004c00c0000c1c204009885c046240c0f0344000d011a685100262004003004644443c0c90b1081d41b00d4825101064002070003400100b808109428003160143e130280e40c0c2220000c610036090f480001d40c0f5080f40d4002c5e03d1220306949042d900c0005001040903180403050410701441001f410f403084a01c51403081d1001a103130704103003000400c4901610100b01202860f050004000c5080008210865000340380205010755880c01c0d031800c00805d154012114418a024004800c00108120705058044030450ba0f0704014a0740031104051203041c00c8040010307006030200401c3c541c0c1100c64a0a00241c186850503070303280d96100e201e5101c2c0c0e00c9070b046a680d5003002503d940c0308800c03080050201c18410000038104188694442c00040c0c001022a031845ca42080f00b500d640200e01c2c00300c92801c044845e95039403858 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 814745845 1250 814744595 814744597
    0x100f08010501090f1404030e0d0501020c01021306090e01180f0e0c0316050a14030304031202061e070e011d0406030605040c06090b0403060c050f04060e030f1f1e11 72
    0x90803940d1800c0201100300c4420030305ca1480a40c1c480c140941d061785854070141c1e030024042105540040041c11a41c000c103031f0900082400c46292000141d0b5980d555085c070b80380042c503030080401c021030003804200007001640103d040d0350310010f40460b0707500131030030b01d0005008074200021007504140241e50090004140f542c0d14240c29419620700c0100310b5180364002c031050191684c004d508050500c401c980418031480c4070200a800c0300c3c0341980300e40b600300d51a8040a40000140d008034100f0060070700c05418141c50842c1100401c4e4181442103028000800f003522060410400700f0811414070350382021941c810a000d403040000399141d0400e0406071400329010364020840004c0010355030320032214001100c08030743d141410941140ea486028041c4521300b0001c200741070040401664125008000408a90311030019080c0000c044c581484030100d807100075504802200d00040031080d020a207441040040090000c0d102550b00340c030042c908883c05006860a0302c004402c1403604 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 814747095 1250 814745845 814745849
    0x615020d02070902031012142a0a061704051507090e181203042f03010510050a0b0f0f042709080a03090f1205041a03040206090603100f08010501 64
    0x1e82901d0500e070711820b07420700f64441610240d031220044a010441801031903241e800c2644100d240f0038080340544142e40c038084143d1503000c1c4005508200508491468800564030881640c5409241c0d2604a01505480954050036107080103040040c00b0803000380410040d806007095070110038103200e6401002c0e02d40500810030b040c018040400d1122170b440c02020707924120503000b0428041100911421741d04081c20899002408008508141e60796a10b0014141c40205031803201000b400101825904040e02c51650442e0310b210601190700c514541070203551a46503550341d6880954902c03c0785100749062801100d0340407a01080d070344c1c020106488400d50707094016a001503403c044004550788130f440100081010004200320130b0098104c402d0f494010444c03081c01601d1501c1d0b15100c0c15031146001c0011700c0014040c8840141062408000c01c00540d120b801e44ca45507000ca091403107802d02d82c6104410200c001011075004488100160610481b0f2800031a03481e01d480d80680801c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 814748201 1106 814747095 814747097
    0x16031203021c060b12060f100f05120f1b030708131406090d2c13060b1908010b07020904171b0c0f01110303190615020d 53
    0x61081c1c034014001c0089503030360384090300c81149215400403e00d612500502c01000c1280d112303282d52150001140c01d1407480345c0541e0b8419101401520740031109203070058200701c1e5207101d0b05c44280c09031903056070320104200d8a11580382d441c0021036100b4000f90b5004001001e82015140b054581405400c1c0c0c1d80313b0546103440b2600700350045441c00701c02c0d403003401c20146880d40505100d1240620040c0747d03010414012225007003041c192145403040d000031001c7c0005804540c01a03008024000050384d8410301d1400e0369130184201c5030711002042d003800001807801284070480d1240d035402070403048136035116030b1081400d41ba0490980784175201030202000940d0a1071900c082020310500400c05030704421308200003440d504032174038100b26100411045084000050307941084045034803076022041d0882c07002c02032109511a00c02a0182d401c0c640c100368022850390440315507 = true := by decide +kernel

theorem cover : BRFrame.Cov 814568345 814748201 := by
  have h0 := BRFrame.cov_init 814568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 814568345 ≤ n) (h2 : n < 814748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
