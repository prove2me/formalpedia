-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0532
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:17:41.747283+00:00
-- url     : https://prove2.me/submissions/da584a8a-88d7-478a-a21a-f30d03d4a65e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 95503597 ≤ n < 95683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 95504847 1250 95503597 95503607
    0x101713110108090606040207020402040305060403020f1605010206070c081204121d06040b030717070201090204060e04052503060207050f01060518060904030e190f0501170f0a0204030203030301090507 88
    0x24104501c52040000b62100420051740105e4102c401580e100e80320700005001c1d00440d0800384c518024403003440101074000810341c4d20308200c81e0551300c1900d05461501850030641c8505030158200c41c00040780d0074401c82e0b4081c0360a01c00c00a9a00304105ea1501e10002c040c02c5801300e03441d0303048041d0740c980385070003074501011300f29040180d03c3d0401c00b91000c03031400e004610401d03030f4a1401101198207580141000001c1c400034110001031490200d0f00207010340100c060580c0964070301a40401d211031a082401d00c1a50014003c0000d01010401142c400e0b0050380f540c01c401300008004000182a40020043c51380038100800a103c3c1c600e41c01421120305600076840340b0002c00510400c85412003a1641c40203007280c4d00b05240da140d04081c2c42d02c4e160400d5560340410a40507619080f11462007603015180c083e0212980d940d240c80040da000600d1602074001c041701d03400000c449402400f403a80e4002e0307000c2c0000d0300305640d80d03002c00d241d50000e810103021141c0b500c081090281e805 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 95506097 1250 95504847 95504873
    0x7120509030405010207030215220905060a080c130e0304060201091406011a0703020132010501141605030702040c02070602010b0102070e13060b0603010f0801051302030c101713 78
    0x200000e14a050320700800030b90307250f06e01d220080c00f80c04480020584105414143c1c2c400801001103084080d4000401075812481402015107a85c80c000118415061a9407400c00f83c80404004014140480040107c0a540505400c00e680d440320102c0304400014400780c00240712980010030004001c5c41c10f20181c41001411490070361140004108181003000083c205000710020f21750380e0b070785a08080303014040c661440504c1d22047d078200351500740006007094040c03d0000581c40c5590300d901c01141c99100440442d0384030801402086501503000c02d10280c024490003c5038070300381d401d502007010f494510140f400035800010040260b00d8081c0160415081d0910251001c281800f4070119103180103041c0b480c0040a8104110801401360312a00c00d50070024000798407903a54800c5411180c00e03e00403440d155080c074003c20310751454140400280d0f54000c01428600c80920b0070700802c041c20860040401840c00000c84190200200304d502a42c490349150300250501e04204043e4001e03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 95507347 1250 95506097 95506111
    0xa0e01020c040548070b070f09051c120503040b01060905030307060e010216050304050a060306050f0d02060d05150901080607121107051501061b050c04050604060e071205 75
    0x41c0004c000d03001030030072049016070084001820703032000f140404100680b00e885880c00f04c003405028403020411040007400c00c8500c60582841140da034030301c040700c1c01040c242e020800300e01412400c1c4042d1a00c0100b500a58420b80e91012030b8882e25107510510300c0610b1851400b00700004103100500c910100020b0141041382020000301c1d180c18042582c81c40761040c0588490b07a03509066003414800c1d01260585201c00828000400306410116103d0f40f040c07190314442c003d43e04000600e68002d005000c11070f1002060148035403002000c0c4101d030702244000701c0e44098200060299100680304040c06042003003088580500340340b00340a40c036001a0450303112030717000d24104540c4540c410720320030034003c11110108411303400321401041b80c010a80c0c02070080c003c4080340500001c07400d402034121915075940c14182084c1c030740c900201184480f4082d00e00d070004821000c45041507006150404400341c80001d80540e50b0502c1403004409591100000f00c0d070190240f9a00c419005103500100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 95508597 1250 95507347 95507351
    0xb1e040303020319090308070c0611120706020702030a0b040507091a240c0109030e03070b070b0c0304170f03061f0c021314070801080f070302091f030501020a0e01020c04 75
    0x81107403400b030764901441c150880b540e40c0300382d83da0801034407801c0508015a030040020341c561645217001c0e05150707074a000d03e03400200300744001d00100c0400200c003045a0340d905200351910405440d484065881340300b0a907010f00c9494903120018509400080c42180910081d1160900780301381e0200351210400e490700074544038480300140d551000f50a01103080700b400d402d00c01100c0f44180094900850b04c141c2459460700c5035010926030801c0c407603a40480300301c05031022940c591003140790b01c2c0202e00000d031000e400d081c00584a90b80da00000d541183c05201c2e16006881c2c8000300c030f034841d0b0100c1e48548071040c0100c20300c0002c1c2403900070300a49503100e6001e1501d4001011004007540a51301c030191141c44203488001d481e11107a032002112141e002c624040903e0040005442c0311020701c144602482030100d000002c01010480c041543ea00500c01d110913101e4540404224000002420355003014000000c0019424401441222065101c5401401100c000641048408403299005038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 95509847 1250 95508597 95508599
    0xf17091c12050606031b2b060302030705090408190201062303190203060604090314040303020109051005010e06060a120c03051b0c030403060c1205010806010312020312040303020c03130b1e04 84
    0x5081b02d1080b402c000d16105443d81c9511b001500444400345101c00ca6940d0300343c18211a0150755203411010580c1c2c000e078122618550f40d14280700000034201c401404c103070010300c4414086440d201d880400360303440748004030740c42d80c503041c49034150103200f000c01c401520440c0c001c5860f804d040c045851140300100d40001c4028031a00425150034000346841e1050799585040070806010399034075100300e6120a00e10791074a8992501900030705040030141c90310b2088484403040c0d048640100d42c140e501010ba01c0b4481d850340c00900c03440d80c026480150520916042810080c40e180c490068407001540d0082641e08206030329440c44400d0700958965188100302504803448000120340482c1d42c4103100184050081400b200e01a00301800b03001b03105c1c10600005102c03400040c10300c0c1640e0148004041c5403040b0030b0700766900e2003000c03e003101d045100c07000074012030300940c041c008545181050381c0c98005c4242e10007800380101e800c031701810303000441c20301c03841c0c20280096074a141558507006d19003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 95511097 1250 95509847 95509861
    0x3060613020f21061c150507110f0c040605030708071e080f150a270215270108090a08130504050412020d0f17091c1205060603 56
    0x20a0695600054000840500c42d4a040003101c20520304101d030100c440d800c2000100b500503080e52214070031002c4c0c48402caa1140b001c2202002c00758001e552803401244420305001a00000b4078030000d01201c8880d94960400510601580090040260002c820b0101c00c100c1220328036000a40660700445040c0500b078000110082942c081d140b2071611303070601d0010340f20909040d402c40320720360240030f80c420b04101000803400001110b03c1207920089d0388100d0160100c81c404405480c05005403000d100d0b883c031042c00700ca0440380c0058541c0001300c0c843c08481c1250340c030003000d18900d090040c40071008035a80c400009510a0300f460f10300050f01b040030302e056440c0e411400c050000c100000b4081e01e403802101c1c8500041001620030301c5030b890541020200d03c2941e110100140c024034500500091003210f07203c11607092901d5550320211310a1400c3e48420f4010044c00c01c61241d10048076900110b41400e0b24040c4040e0381c0e003003402d0304a0b81040281d03040980b0082c060300041c4148901 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 95512347 1250 95511097 95511109
    0x60105061b01110c10060506070b0106200115050f04090804150e0411030a0b09010503060c09010c0b040803010810020c2e0c1101180b040602210c07030e030606 70
    0x40c0603001c80340d4000088184200300c0c0100580c1e0140d569001000410590440011855600040044c00204506556a01401080d100b0803100605002e0000010b10055000e80c3c803045940c1407426012016820002c040c2c1d003100d103040351201100071900c3d0100000e1030702010b0040e4180042d9418072601030b8550383d0a14078002c0c2c3c003c003039100030541110044140b1175031448160950080003408540c0e0580b6800d1620741c0241d5101c82c1c92420701559094900300b0044060407144080c0042c10f07190307075000c58003066403c00352039141040030103407424010510400080d40102d0251010507941d504d42603450780740100700d46200e1405401800005038500000c207041c861042000115648021134080782800400e4101c80307205140e292044503a03c02d40d111041400c080c0d41c443c02000400301c144030130305500e5199080109500100380011340019001d4020b00480791301c0d80c50415450320040c03098612180b08641282e18103c0109030304c070034144c1c0051040d0b080350054019254504016003c07500c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 95513597 1250 95512347 95512357
    0xf03090307090b01020a0b3103080f060105070f120f02060103050d050d0e030309010b2112090d08120603010b0d0809040c0504080307060e0705010203030c0301030f050c090406020d0e06010506 84
    0x10405a0f81c143d0f01d406079000b8040c0c4461540e02c515441220324280b201c4502c5480ca000c0ca0711028074107000e500040e1004146103507940790309601c0c1e80140d9030fa5410402104200107040d44c3c1001004d10032030700041d881d81d0b007941c816071143c4c800b003221400c441c200a00b4489109050811503000350010004070f407010840f80103040c041d1400c0740ea501d90040d811005004020122119440008204042418103501800080e0411a203682c1d07000c0540c2200c925400310080c4c0042d03107030030500c2c070080980c01800c028038403104043c040b240c0c800c1481d103c10312a60031248330340c41c00c1e842e24410882c9510f0203103c0c00d03400d2902100c60f5801c1911940382c3d000e8900070f5034442d5005990304c2c001080c47c83d0184007a81d0040c8413000c100c036540c1c9024079001010306026100401544186a0302240320b40c00841070301c3c81010100304490460707103583c80d0f0611000910700103450502503020003600c503403519140a803141d80140005603440aa03401d441c412945100c1c06401190003440051040e5501e54044031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 95514847 1250 95513597 95513609
    0x30c040e0705070c03120e03030c07060c05010608010c02160f03030509010305180f031b010506010c08070809030102030c07110d02030606011d03033016030e03071407080f03090307 79
    0x50380c5540d00c0406440364800e040015100c040060070000410110f1030031040d1a00a40d91249032816400d0103165a80c010401e450005421043c1c040c0300d4640b04180f00707400349000d0800464026510035015085550a5078041c0045e00301c11040d000464504004400a0041d0b402410b4040c2c5180c038028014050048400d04041e254070105071580344000c61200c0b070040802c1521010450350010559903889402c03d14070412080d8100142da82040c030030103102e40c20603116411164042e61301c955540d4024007048610607014400e080b00c0d91401d1022314440c20142c42129581c48032410704003c420304030045c0c00d00c118140594000180c40c04184650000e5003800d2050000545d90701081044800900e5190144004520034442921001041401400d01e01c0c03945a82545030180d0103500b07000b121795010243d00d100071402d03154030951000b441e8852440c1600e0401985640e500500c01d00002100d003a54040c0d0710030302c10090240540c0c000c40c01024000e510b8200d2001c0400d4542e41c4c6480340d5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 95516097 1250 95514847 95514869
    0x40303050a0c020d1b05030d0806030604080715020f0d0e0307030207060513030b15010801060207030f080a0e09040f060501050406060e040b030316121d010c111201090b0603060c030c04 81
    0xb45046485008840044a90003010030074500318000c03941101d800544902442407182c440c0680110780905811406001c0103000341010340da5946a64400b544482e05c00c07250040030b6181d100c100743c81c5101915507036400e6107005030398400544400c2c007a40c074144154803049d04100b0400c40041e4001074441e044070b20606107180c4502c54020b407540318002c1c9a00140601e1410b604009407511000e030039000402c401d883d00401640c88020490b62075082d8000104021514010000850010b00c06440300860358580013008516640205010303120079901241d5101440074618200309450144601405099a081080d00d20f0f09600070076802c0c0c40c0c03071b200e4020355803000c0185d02500d00340101c54101700d044070301a01c604c04a1a201c1049103031700740030b50002405c0541220550603080e446141050059440d1b040e10410b94652400f00300f8443c070859802603800d41a401028000e0003000601405006824402d01d44441450f0508000034185002c502c42002040890417003d400c0c1e03000e452411050f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 95517347 1250 95516097 95516117
    0x10b0a03090201021f0603021f020304030b090115180501090b06040302041104050307030c0e0a0b1018050907090602150601020a150b09040b06120d0f031808070302010b15040303050a 80
    0x5030305004111000e02a0040e044135460035a8042c6d0300f003503007101c0c801d99002c2a14211421103884044420302800c00603002000100041850040c1c2250490b07070800001903540200c0030080f81000c502e510407086610b40060940064449118180c0144100d40c41030100014420004095125a0000910990356680340010300030075030341a00c024240240071650b0f255224180300301002003601c1641790301921240007030182071180c01060096200076080407020020f4031000c0c0d600d152070f02d000740740d80016064006503a0f03a482c401d041c0221f41e251604400c80d4240700c3e00034100030b4a0307000300c810f0184200a01009903030001d5411200c60f000030000038510401c27842e100c0685031701d400550f88a803081080c881407007548079440380510320880304550196a0000e00944030104650f40b030010401c1c04140003222402a00442549814889401e041e05020755a40c10140c01005060300180e54698400c134003070402c10294509040d01d441c4044c102031840d42d000f840d51203981500801c0101d4131b04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 95518597 1250 95517347 95517349
    0x121b020f010c1407080313060302040501080103060209240c0d180504020714070323010504150e10050406090b0601020303040c061d180a0c03060f03060513020612060a0e010b0a030902 80
    0x802c0c40c84201805603480183c0e00c11000c6d69030f41011040e600360003080da030000340090281c4215000c490301a12207044603072864480c000250441e011507504500011811034140c241001d0626680c50fa071103070940c85904405c5010718240e4101404010b0000c8001640c0c00e0021540802c011a1011180541e441c8020303d017210001900760200409d80c400c4043c0401080304500d0b95540780d14104040c2240c00030601c40160a8030010f840150101c91080100303600144141c1086020144d0001200c4c82101c01c0d610600c00c407030f42260700b540d12641c1e91944030200442c0d2810a0381101091009505604081c0c4585039042a0b070b00c100300500c081f41030350500f0b041c1490b40c0340c40e0b40c10780100415400d0341e0040c0542c00c804003c0360801c0d0824038105111000074000d00c03902c0203455108488660780e6065645440c001d14024140c0e0744041031203038074140142d441c000284001224808010380d1030500c1005e010a071101c41e000307503940d01a00c90061181252100c1581c56400c003130302d00804c102020b40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 95519847 1250 95518597 95518613
    0x4050717031309112206030f06150c020105090307030b06040c05030601050a1b0c030803180106141302040e010305031201060323070e27010b07050607120e0307121b020f010c 76
    0x1160038042c001d51718040c4d036103002d8806507404817040390b00c0601c007600c0c43c1941503080b1140b90040c0401030340250622017045104140c000304152060400c0c034038140442c070000346406620360086414803000c804003c038600b05409110007201b02400e140d819400c20400103085806103c50722410814044460042040708040038044c0725045480d80640c0da48908082c20281d00494032804117034103012500040900510a1004072048500d41d0120550b90a003001121032403111510052178080c00045800c560380c42e04540250703c2680259030f120f41c14800c80702000c905034080b800b810b15011142c1c0c00000c04140c82c03400c9020881421620355503014065403900d0100f1071050304200740d403900b940002001120b00644808036440403d02e03aa0701c2c14035241c40c0c032070042c00a020303801c2440410443c5014000c44a14442845408600100d009084600d10b4109080541c0c51000070b41002548a0b080048540300400e610720b40b213810b607580d4020600c1c4201d007190035070401000034000002c1c00a11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 95521097 1250 95519847 95519857
    0x9040503121302040b03061005010f0504090501080a0210140d020f071b06091a0403060b0a12060b0a0e090d0e0f09090609060105010f020d03020f070b0405071703130911 74
    0x207511200070500b02101440e00004082900328012881c0130b01d00c50341c038500041d08920a06043c5e4000902c05c1c00d22004441d075a06031003800c000c2c4402070002050300821130180501920415000340240192401040b00d00591002408140482c10300318200800c40841112030000b4801d001607034400c4052910142e42c40b541d20081c2030004200b020f450283c01400c401011104d0301e90f00c0e0a211502d54501c000e80c2d81440c0e800c002251000c100400c0020034507044903000c2d110081103698075a54030702804114001c3c12404440c1035a440c900709545203420007400c4050300884024000b649080d07040c3c169200a044000d8041c00701e003035040540c40d41d810307864808007400900018036030f05250078581c1d65141c0c00c1c0d40c01d140e980200b40000c19554031038080896032500717a500602003200600003d400a6102c000e00495100c42002940040b4996840f807038000c510581c010030796189040f4000340e00070300f038800030000c980081191f070307551000606440b0182c0c0c441c408009800f43d1181c04d000b0b41071140b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 95522347 1250 95521097 95521117
    0x3072105040312112d0f030702120106050907020109060510050f04091b0803040302041112010603180206030108060a051503030901140702092503091709030709050109060f0503030703080609040503 86
    0x250041c40d11303c1760b65081580007940c02603503240040030301c40f5401079124142d601c001c00711584280140005490b010024a25a5600c1d03000014004d4581000c2180843e0848050700941e4640921404100329403080760b40c0040714400c500e0250381068009030320f04c840b884425108d5901e807051081401110684c1c0e10311a001c0c1d4100d100183d90380c4a800f07072640c01620060b80b00c0c41c5401000c07d840c0361030b8400c0740c0720210b1840000150741c0c00e011050b03004203814082240f81c4040c4010400060310742c58003d6002c2c110440c010b040910388075860000340c0c0d000078425003e5a0600d41c0c13002c000d0f10b0001c10740340301e0391302400c0001550120008603050341c064000d01a504ca202482800340da2190090b180703401803208031400d40e0306680d05a050b429201d95250090080f00e681d25580700498244010709111440101910b0066640f1a0b41030185c540070b800003000390f69a443c08112008040385501d0040005802450401c1116200030301a00300042800c0c0c080c0f00e043d0001010844144211002400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 95523597 1250 95522347 95522353
    0x90f0b060a090602010e03040b0412080d0f0204090e0f03030703110c0106120210031109010302030408070f0501240e07050306010c050709050f0109090c090b0d140307210504031211 79
    0x10081000300750b031145110b1400954078200358460f03020742c044220360940d60051030131850540341011f4500c8001c00c0503002d84001c1d50501001900d07448070f004880781d90040000c0980c9680c2032a802904035444c0f101501c81d994421342710710841c0d200c0801aa0b0f800701c501c0c00c00084094207420001c1d61881101480b811715440c4c400081491942c041c1441d2459009650b200c00c2c130400540140e0403100300111815035603005004002c0c0c01c0d84a81c009551003031044c103200c3d080800300e81d103410b0320f84522001124281d444081d443c1103800c4c10250301d550f110140042c05c3c0c2031840d11580c0098810013500c1c0c4d00400c203000000440a0740942c100c40c2a40340d011044030820390385c07500100b00808050b908100f615802400000f1000e50500400c01c400350805d0500c04601d10b0901c1c1000100034190816402000201c82d100100310b400503441101e01104024640c0e40040b0f00d0b20001104c0392001b0040015009a44903440c59805815101541d034410140000985044030660720058000f000d45010301c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 95524847 1250 95523597 95523607
    0x10e040b010c021c11060f0910031404060603060e160317041203030605010f09060f0807090815060f040203091e01090c140f030c01020307020904020604090e0f15040309090f0b06 78
    0x1003441d901440d13070300340954010301144075a0700800507a8843d541000d403030403100340242c2003940f910500340d82c0700c4203181c00c0020300005010461828404201c409480b1241d0300d000401c240319080c05010740440c00700000d003408540d068541c41c401c000701d00024045844610341103401940d107070f00722005000004c00b4951588220700c3c00502030025806041e0004500200e0541141c2c011846241a50301545466501c8000000116040100100588204000c1003000a00c0c0c0005100302982410b840c03210280c1c61604a09110902c54501c20480c040d46c41002000305100c0007041d0804903030b803040f40881e444a4200a0340d805021081006007805458640c001240c038588c41c1c003040000c400f0389420400a040300101521051b881c220b031405600308200c010018034007012810707031042c401400141066114441c1e40121800c10408000b00d500c61541c80e03004400400403800d04094000242c20507143c150b400034800700e01c80c0303d000c4a558966045140800168100708403c1601408141e210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 95526097 1250 95524847 95524879
    0x4080d09200907081501021002040f0501080f060a0308070609050616020d360e0c031807080c040c020a1202060118050906130302100f02030f0c09010e040b010c02 71
    0x1810101141e40e042840c031107121145424161540c5101d00c3d590f03142c2c00107654658100d0151030150355030060450041c01186012446944080c1000e42500d05100b4505030074240003414589010f1304211144280304104452651a800703c10281d83c0c0c4601c24684454840c41c0c040054a01c034200101140503480400c405060150301040b0595125822200742840300b00301a40d040a04004408000800d00120340c0c071144006e03004400004c40203e15500c00da500c010030320340e120b000e41e0402c00421001007030041d0142c0040f01d0345216590180941260303440d100c10a81d6807210750003a076004545032051140c210f4000d002400c007807504881e000b0300c8440c501070025150f217002d004045403117041d00c0500302020458422980f044140c00014074041e154440101400c20f00620210118800c903806071f4011a6280107e80706981c00000250700e90816040c1c098914100901c100c181020038000080305e031303905c2501e42042c40d00548000500540910040350440003012020703400454540c0b48c407241c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 95527347 1250 95526097 95526113
    0xc0f0902070c050d0209011512020c1e120403020d020406080d020c010f0203070f0803040212160303021b1e04061208071202010c080c030901060e01031a06010f120504080d09 76
    0x11144203016224400f0384501c104100c80d1601d000c0030f0341141c440c0005000c0c2c00b89501100d0701d0084582880c002555007268001d0136030707010089800c040d810440301e000801080c074482c0118684010043d04500c2154401440c1c075010b940b00107407103407007800d1b00e600c00e54480b6404000a02a01401d40702003481c0c4200295461a20003e402d000861144081c45d0042c404030640c1e000300e50025040c4e03491034064641540030b4101900507648105410900d42d0741c9a81004640140f81072005403070811851820041c1c18a90040040c12010f4a80540c804030780d1b5a0b004041201c00046458195000790743d008500282140d4001d0720340342c103000080400303200c640c1c0050000140300c0c0c0b84000c0a150342240403426521504c400e4004a50f0040115451841c80005503a00c03004e440000204155541c0301007140c00c2d07013a0b10940d8005258441641d00340e1454002c2c6500440a01b88402c400c1038158004215441815003429125036510100d800c110441c412600d503085040024400e500d03041c140261 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 95528597 1250 95527347 95527357
    0x3020d0603020d1b05010801121401020903030415020c03030f0a0804060f0e01060504050c0f07021c0b0c0a110706140705030903030a0e0306011401080f0a0e0607080109140402030703030c0c0f0902 86
    0x80c13101e503d9000240310340c840d001180c141c0e035044120745113042070f07541c0340b01c400ba0444120700c940355004c6c0518111610100042d10041c080003118948141c42054081c3c00d00360760920309402504200843d5181d2282d034012900803161510b45110940d0302c1c0d06181004140145080d8500c50401c0c54084000c001500000700380c0c1d04c11201040541c80320320038a0300600c83d0239910303101c18405000354409481d000000d000c00c00880800d030902d2030819692160b00d034600b194140201d40c408942d0281d05070f07220a00040190300c0700010444c090078018060040e840c0c51000383c22010000540404001c000c0c03040c2c402d401c40143c00c07251038540d41380001d4180c02c01d0070b1242c0d00034071401d0300028459500c00401c503034103401138581102c15190008850b111110042105030340716180eaa01c611200c0003004880d219400780e40d107418003541040280c2e4296084000030340301c0204c941041c000560340104000084030746c142440340b10180c0300d1804c10b0075001c0701d0388030070300d040d0446500054600340381c2c000b04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 95529847 1250 95528597 95528633
    0xa050607020610061805062805030411090402030622060e240f06010804060b1e09010503070303090b0a090e10031703010b121005040c0e030c0901060f03020d0603020d 73
    0x19610030340703640c4c04480d11408036a42881502004004200c00d081075002040401070a1644141100c1103404500e9490040314401e0002540081000140400c42d80c0c0444903050407151106141000d80002c1d40e6007034082e11144041d40002d0810a042c8181c032481c1009a50024091000c41b003060012a03c035200a018103410010301d104130170801d00da08038010f00c00c2c08412082351113a142c107401100d842e00024000c0b5002c40d650f440101e0942e4810001162a1001d40b900a80403500303002840342520040e80014000d81c0079102c10702c0025008402c1c4010f660608488589070740041c801250341c0c010079403100d0300d80100d03030060103418887d084071481038a02076203482d211403020501d0000244001d00c0354500544040c42450042400010007a81042c1d800c807060407425200c50015045171103460203180494240d48003094503082c140050580c2107000c56010207258542070000e0b10940840780c0c054200b42d40080c4d0402103c070560300140c0a1500500179604801c8280b901c44081201d5a00765 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 95531097 1250 95529847 95529871
    0x603050405060906100e06130612140321060324010305010501080c0105030703020703021c0c0b2401110a05070b031f03050304060c060b0402070f0309061814030a0506070206 76
    0x150020f94001205400b401c9501140c00d081450700d03820424004001e48115480030003190403141c2c0921030700403400549042d10122202da803a1789026050300100c919008503681080c0041d210326200c5001c04100194402c841440da40e039000c001a04112000321a4030b049142c4001c0c4542011681c070180741a00d1191008001d01e0341c0318642c25943c1c0000303541040c0001c0c002c00001d0038003880f82d000340504034403030b004680c403082070005843c400e285003961070800600342e84040c0060085002180390840710340e05004521700044100b03640c0e084120f0704030038140b0188152a4518a8042200340f14060700a01680c0c00d003911000011807070b50040c0c0d8855484491049901d1010200303070440000c030f99109009600e02890b0500a54585400e04002d440d40e50b80c40320b0640c000d4440d070000308207017849020b40c0d580311541c40c903001d0207100c600e802640802c580b94000c250340c000349841c82801e99201d03041c0c5480301d008501c006450305000040041030b81c000c1c5c205204446e500021030b940581002001c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 95532347 1250 95531097 95531101
    0x1020a0e031501050f060a0c0605090c130b0d0212070801020408060403030b09151002030405030f0d18030b04110d06021306020106210b070c050a150501090207050c010e0f0307060305040506 83
    0x1a00100354800e0094640c040c00c485c1200280c1d141000c0100071001c65410f04230413542042e150441200c20032502085070f5080180002954508507442e240d035454034480802002140d540030401e1740f8400c10009002d10007105407041c00490130000301d0003c0183c88001d43d90b4949650049440d040181c1e002c0380072034105082c2e10054a000c1d58101e02c81c007442026140111020810404410341420825095000c10807004c0b4407510207024024811490b54010019070001d03910040c6601d5a41c01c4eaa00c807102c08410078000218020303000c41d00143c1000715100b80d014a800042c00071000d8010081a251002900c0d04401c007407600710008451481c4c0081043c50b90b0781840148003d070031f401e005002d50407100c032400002e107511a070a8000b85549032154440c10640c0e10305262030801003068400f6512001c05190407a40c41c02124007400c2d401c40d01754180b4443d43c0c0e0f015a6080b40f0190715050040d210164411603c0d911104607140d04010125240c103230b0f6490001c0c008180c26642034030a4095800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 95533597 1250 95532347 95532373
    0x112030806040204031a0709080111070c06111b03012306041d030f16050f03031f03020d0206030714161412030115140d05010915030c05010c06060801020a0e03 70
    0x3c00c1d5000c82e9005a00c041c00100340854079408085c3c002c02e60414070502030b902281010702482a4004883c4680000b50340b090345003000391103100700d41d00000030003104210301ca915620104442c852002000040c800c40d03444e03200041d0142c25040094016411142120a600744241c82ca25000b0482a03070100240c10140e1400358a116a41074240c1d0a6803041040303415141540d00141070600700000d0b0445504650f5603841e0500c1d42c1070a403158542e00120500c8220031000b501225014210489422140d1031580414000941d0a102a108000c040b0011b8400c40c001d00f00e4448000c007c001e11a9548038009000070f06850b62001604d40c009190701c0489030000c001825901e00406608c0241142e1800740240703100d00038080710b03804001440d402c03411008400005407512054940021034190304203844071046131208006a08001e10000c1c0030004141410300510a4400c20320b00814441c0b160f003402405040241d0283c0d00c6580300042807050198440a840f2019804500351402001d00003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 95534847 1250 95533597 95533601
    0x6180c19030c0324120501020f030c070302070906080c0d080c0d1101060605130b1c05090a03301808070c060201050f01080c010804031101050702011a010c05072903011203080604 78
    0x8481081d804c3c401c820711a420385103880d98100ba10070b030000351a00030540040d444580094905411040c0c002c00d04e0785c00c05405100f5440540202c51041014038900ba50031a596050420f1041c02a20304070a58400d0080c0403003242d02407170200045403120b8514440c0200362480d100300d003900c15460490041101031040b000c544242d0300c8000602c5003a42055a2444580c4c0141000b01c002041031110b5140c098081c0074240c428050840a455154018200940564144001082081400c10503d11202c9101000c1100d2000741d14002820490901c04174034042d600340d90103000840045948401c2042640c907140940b4016070080c00f55880b01c240210b44002d00b8014040e841d08441d1888496512582d0800e51080c0030303103440318080c4601d68501d42100c80a80f803400041c0d45850000082085442c40710401900c00e1910203015503064484949400c0c0134002d410051041001c880304000c05d01065484003001200f51036502e50303460503610360340140c8080c01c030302080440c40041e54618143c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 95536097 1250 95534847 95534891
    0xc0504061d06060d090f030c0606050103022701140c06011e051003110904110a090501020c0303040905060a031a010602060108070302060a0e01170c0a0e040506180c19030c03 76
    0x88003001150341c403a02c0810080360080d488443c842581d0380070700c0c804103a8107025200c41c2c034040d80301e03440c0c44242401d02c1010388549411103814540100000b10007505003150b52030a10b5002c50010344240d95220049441506008001c2d903000e001190074500182c01040040c120341c003042000d15102e603801002d10034114517124103544208002c200c1c0300d015000350030203030a00300d010f0f200628010850000804035810600c1070188031101081101c0125001a541005400240002c01c4a80f29141c0040d07524826406016403064503940460220385564403040042c48e848014559a13444403030410050381e1091107100010b21519000040c8160046028001e80350048d040e1898242140c00a0340c240caa01032201c3d042251108882e41940f08061129004501281c4176654615000d90700800102c280c00b01f051060341b410040c0300d034503690989030f0410012210a208019500c864406580d8003c030030b0708080e94154200c0f4014043d40c0b66110000400312610200403005030780c0304c6410382d00300c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 95537347 1250 95536097 95536139
    0x23031501080c01080a0605130209030d03092604080109030c02030d0c021e1210050105040f05060603010306051905010305070f060203030f010e1315050a1415040911030a0c050406 78
    0x100d082d070000c65510031202c1580c0480f11032404280c940e5610003282c1030203415244407110541c08103001420f45810b05c44c0303641ca0349540c44c051007200215121418440c003121590480c521940c00d1070244040c5420a680040003003030000c200e41940f034200501803607040c40c4200d1185c002c8001d010452800744e000d104403650003500c00e00d104100c000d14002030401031000c644c1d000c00c0c0c100b0b000861030001c105031840807000e01804103041d4584024003083d52046c0c0543c940d0141480304024240e2504030580341129000f0720302240303a480f10701058103828442c0c091030034070604250011080c40000242c0c40102c1c0c02c1c5c1880000c0301070381c0d8a012610381c0030230b44400d0603600d170320700040041c0d080340106a038000d5208500460f2425640c0d0300d041800840c01c1f01c0a80c4035490b8020013100c100c0900c115042598840d031400060716008980085000c00324480b2071044e40d0f5100b48c4011b00440c4400c181a48001504492003021a0f040250303a580c554452035200314109040030982203499008908030f000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 95538597 1250 95537347 95537353
    0x406020303071b0b0405010c020c0102030f09060a030b090f060117041203090c080a20030a0203060103030f05070605070203180a0f1a0f1303120c08070201182303150108 74
    0x803107071412502e41c421045201c90003c084800000450003050f030320303030142e407085d00005000c2c0700154010741003003000318100d03041d900705210000503540408200d4004c031400721402c1e070f0380340405d181c00c0d0010026001c0c09504514842d00300301c10098102c8000303004400c2600c6403115020a90107d210314a0122030007044e40e0104032208164038080c0d003200c02c1c00c510030a041c0c41c00c0398540c50810300d800d082d4642511070359901228040c070403201031a08062004182c014011940154021903038400040c8030007010091110910040c031440b507401e81c0d5842c4d41c0701100380300c02d02703056600941d20f0300460307100303202480d90747d29581e030b246080b0300500c0071a1000e1000d008203d103050010141d0380d101c001c4032000b11404000c0c540c041d1010310000e01c0c62012022000c4805811401d04901c940f02d44030204c014042c0451018010800316029202c403a64240f0b0400d14008070001003d21a000307030b503c2928001002d900010f02c034010044c00b108000340903001c480d1841c642941c40459100300380b03d401c1ca150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 95539847 1250 95538597 95538601
    0x10506061804050601030e010f0c09080c09010b1309060f0e132001020f0604051e0708070504020901050904060e1803070f06090f052d150c0901020a0f0804050f03030406020303 77
    0x100740b5400090f0b01940504000a200151802c1d07a8290b03409820706415541c1d0352421a56046e4000002ca03000e4860130004194000303014000c2402c0b000e040c0034024203402c0c04141e0017203400810b103100002e04550b44050100ca691200080d2001c50540111500e210175400011424000c01504030042508440c402184102408841c080307054191555170442c000c98031260030501003040058083c3d4851001480041b0103c500142e1554510f44040c10641001508000281c0c00042001c240e8100b2640169240011f400582d283d12414000540140c1060000110314440c80e1466100b0b0399041c160f845110341403000291684a40c0800505410840b440380300400c8581c0d0040c0303003844c443c0d600a13009140640b00c0300d14200c0e050b8400c0b40f0111552030000901c0107502c6001320881061001021007403a09030300f90b1410000205500c0b00c1c0c40008c036110009a04c204031070345c501c90f08800d1240c0120614101600c050b48540506401480110040c1c407160400108440840320107502840c116 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 95541097 1250 95539847 95539849
    0x1050603040f0308070c061e0e0a080403020f1309050d0f030903120f060e040b04051c080610051b03070204060b093d02161733180105060618 62
    0x151348054184805c1007802d901c0b500000345a0301c581c050010176140122032004019545106507110510411016081811401300103000c41c0c0659080e80d90466601007600c0b08500071400c030660102e41055880c0c100304007101800700100c0c021100e07691956688001242c040300a0b0b0550f00c02c0d550060000c0e440028400040403d54096214180c1402d00415466560342c4181600802038030241c0302910b80340c0600c001c00c5030802c003480c400d00458889410340c8084450141c440c6d000104160302843c1e5040c840c2000f50320420803a900c45a104101c1c41003586400e400302d680c0d41000c64228099231030100d010030101001000e5130b0345104003c1a852201d92600327542907000c0c1210440808444981d20300e42090030b01d456003181e500300254024003828003890b59658032000a94400301d2848100040644280d102040e1402511b00f1800100f0582c0c0c050001d004a00418100c65490840e4120600404c0c03001e103d4462112140b2800900c055200c000800c2298407840541303620085819880f0005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 95542347 1250 95541097 95541107
    0x20411070605061c03081302030a05030a020c0f090a0f14100509091b010f020a17030a050f010506160302030903161502070509010302010c06150b0c01060801050c030408130f0f03060501050603040f03 87
    0xc40380d0b0758401c1d8001d158055000c4ac4c58620042821511a08081044020943c0c1000301c2c600030f01c000c861a45032a2613400110340d02ca400601400501e075140c0d910014424001d40021020b00c035050020b480c00d00e8004a00c11180d070103400740307520031070848020840c2d40340002a28a04904521041a03580c01c50340015100301e00c80c11001801e60103800800e8010510140001c5440481c41c440c841c5e8901e06075141034102d41d4010001c21114071400014403054455205580c0842800c00300e0748042061401c00b03924601801840c107070b041c0300710f586076402c0c1c48120f10b225084800b21044412004007202c81a0b841c0c3e0740e140521a000107100b00100050740c81024030070f500c0c501440c0d000602ca41200002012891141c1040083d0000000c0c00804807400744035040040510000801450030405401c818610000e8800b405d1918040794807401101d442544a00138078071940c1c1e80b01020f070380c0d04002184c81c680740720507160703140342c1000062507003001400c882c0b227550300181f0032060031074555054070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 95543597 1250 95542347 95542351
    0x4083306180a0f0c02030703020604120c05100204030302150f1603020c060f060102100b010509060f0c15161103031602030d0204090e07060e0603150409020411070605061c0308 77
    0x94004086841d07800d00d6404505881d000c0c1001d40400b25592441d84419801e55002144860855000304002c1001c2640071a40c0c1d500254407400c0410354010508040b00d8110a04074007074240c0c0541800c06104405a50090040360702c20340984403400b461900c6040e11000c00c8070480ea40b0702102c0002800b052088d07107104416445420014145004036110514041e41190001e01b03202105007031190035a01040104400c044083c018013440305418002407460055000c800d00484010440035030590001f42924151143c034030844400600303a10540c030464a040e20140c224500140c00381c0c200700d03c00d04c55031740b182503240001c1d451500c0c0d40d03aa4280343d0125003143c2c3c0460206002240d4070070b24900050004258826000c0303200c0161400d0941000345035440b060900c404001280043c0e203504040d0790b030141815400c12401898a404600600140c6000035070140ca0715036502011144e180c05444524040c410030040c0c0c0d42e840e4140010100b80300350554112840c00c1d988030000e40300d401d8081d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 95544847 1250 95543597 95543599
    0x50d0308070c081215041506030b0d0b07020a030e0a050f09060307150c0512130611010f1104080c0a031104020d0e0303070503090d050f04030209090a0212010204083306 74
    0x502d41c520b803902c6010b801c1e04070710b1901c1e19414060303044c040000e000300301c0c1c2c51050204a03002c01005148006c00302c0e510306035120f0641410745444221800c3e035075403900d066410b50044c4408285241011000b51240d042c5001107000c00d4071a0b42d25811420301d44110380507140c010f07100104082c48082001960030b0018022681442200ba0108003250444c1c4a40c04a0f100d94881c0400040b4600d032460508a80700c82e05250310f5018050140811910048030049032840d0600f000c03038092212485001d400c1c502d2400503071a040c8601d848010101034000c2040700c0c4003c095543c4810340740c007001108000741c0f0000e002c14204c50b1154455152036402000e00108900000600c04840d181fa2401c68208440d110081080803040140192050141c000100c0207454200e20709880746084542034002c50101900885c8603400103078030801c1c20000e5414042e001080c00419400c81e05105005c0e40c401e000300d05090040c00308000340048213619944882d0903410502d00c0c5400e200c00d040c642c01c08001c140f1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 95546097 1250 95544847 95544857
    0x30f021507020d0303020a02120918040f1403130504050609010b1b0a060c09050102060f0a0c210b01030b0301061406090a170c0405060a032f1503150406050d030807 72
    0x490010307694441036108081c861703207015840d1081c0072030183c1440801504910169020070603282079a541d442d282c0041ea000381003d440640382d03400c003410b011060400050003250198881c0203001000800b410b52555142d504d00c0c0640d40750340a20041e40c1e40ac0c0c84850300a21004014450141031001510404c1e5407031810040109207004860b1400000000135522644e503164000c00580d4898180000f600081c0014030160428810500c280d0030010b0041c500260b942c01c0c0018210701c54041d005001c034413100b02c111400a0106888003c000d0050340d240800d10b800c084c000b00c0e0406000b09000c5480360781d4500a0144e10005000c001c1d400205901e5000340c0c1c040c40812a107e030b16696035410142d0000510341307000c0050920003141c4010700001d1051114203001c00014404480001012000040001041c2d0143c00d00401d4980d071038004917070080b00d02090b5020415000c5c0698400c2e03070042d041e14600c2c01600148002c4030454016250080d41d2000303507802082c01000810707044203491500e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 95547347 1250 95546097 95546107
    0x201050f0a030f05010806040b0c090f0406030b10060809100207020604150503040c060206190c0905030616080a0b0102030a0f12051302010806040506060d0c0e0603070225030f0215 79
    0xc0200c16440032051a010a60310064039000750f007940314241c0584040001080c2c1d5061684500c18440d400402001900710300040510054030740310702d16411560094000c2c840303182c50345407000580030115507402250103010b0000404c58030940c0d451340604140340142403403211155242c4040d6109003022307070304100100000585d000c412250720300c00c00385556501d83c0f42d0402c0d14261902600c164130000441d4000c005012a110308244448502c0c01c69400c009800480f00d03030261401510780e03209640c58002d8000b0040d031591064404030320100f103070361008a20703550036091004a514440724280140d00a004504034103000366001c00c030741c030a941000e0680514031102c0000ba50411038007071250b00d40a0f85145e0071542c0080725290064400c860a07c903134079041000c00d1090003860305900d502500d030003a07540128010001c41ba08480050070706940c0b0f280114010707549520104810404001d5404820f024003200e000c0d200a4030743c010322010004240d502001805c20740d42105c170016000400c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 95548597 1250 95547347 95547367
    0xf060f12090708060403080112020319060e150c0304020d0302100c0201020913020a0c06020d0609020c03040e0903040807031104180309080705120601031e05060117120403050613020105 81
    0x54558600e030304411540600d81401d45500380100799009032201d42c44203080c0000250802e03469030540301c41003103110b41d007152030000a181008025280d108228551401824032006400c10744590701d00c50110790009020f03c00f140c410740d0f0110759800047c007050002ca801441c3c00c011240840d4000e20496030201c000708409004c40710620005000745c4c4d40001e420b40c0c1410a81802344d40c80b200c500303085040c001c1884c8041c00320701c200000100090381c0003412240c0072402c1c3d407080000d02500c80045440b040c0d1502d006a0703e034051300510441851510001700a0380000003200c095a40b17901c09006014510b80d01c264200d4004004e00c2d62007901c070b203503c80101200c0034005044900990300d1400d028588004282410b20641080d4010404524070f21024500080c0241c1101c0e841a8610391901d03400c8100000c407606500018818000c402c00001c8503002c800c2e0140104460740c09856078400001e4030240c05101d5403000074102d80011000a1448154881c020004d03401070400c6403410507145 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 95549847 1250 95548597 95548627
    0x9020102010e0f060103031707020a0318080a06050415060b0a0813150c0306052d0303040506030405060709050409031b0c0801050109020c0105010801201b0a060c08150901050f06 78
    0xb8228181961044c1c0042040c16400b000444000b0640c00d5090914203081d880251254140c0a026052050750308021501c40c80d413203c0200103040c801e003a00d10840c0d940c5800000750609072400d490420038040c00e103124259030710698048030041b4040620b02039680206440314140185a05c801003c03103411400800d41c441d2007040340c00328440000a144030300c1580581110311907088035024500441c118807203500211401c0d100c8021999403100c0050700803002038694841d50b007110340c002d000801480700304000010700380c2c010380c0503403140506161501d0911007185d89103103018000030780c440c0c0303020030158940c241c1114003030140d10b0700c01c05262642155401d5800a9014460440d40000c0b81c2d00c5e402004e21849000d821184001c1c0140e04d00c18800f164210182058541e0985000031070005410021203240f049100706015914107150714103000c4001c2602800850104a9800003e1105034001c07071910311109004080d80d10b5a420041032280d60002d1100c101c5c2c0182040240c0c0d44400659 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 95551097 1250 95549847 95549863
    0x120809040c0e09180d031505060d0c0908010902010801050904020f030f060a0627110d09110a05330c010614030c010c0b0705090a0302041a04050c0c0a020409020102010e 74
    0x40d0b02c801d10a40099001e20100030b200500944820241801c1c5440691000c900448995510310300414074000015500c03079644d186a0049902c1540048d414aa0411640200310b161125464903101160755242140c2a5007030304600900141426005200a10303000c690715402c0780c000341500e02c000f1a21008039107041e00f90669500b49510200400184a0700d40c016000985842951011050041c540d601140c500c000721504880b0b0b11130102c804184050b5098480100500c0e405101031019801c000ca10203540d1fa89840c0203000680001c07502c1d007000890045030540502d98215101c13a419424070380308003111910350ba060400c1020b01c6112900340600300240000c000d80042c107800d00d90400d40f500c1050080107044c00241c0308801d01140340003840070f60280482c200155504c0129002510a030000d4000a5019181580342c06c240d045907003404401c00810f54003007045413510145888640a4402c800ca000e502181c6950300506042d04088500744c411700003c1001ca4014030307001c0c284101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 95552347 1250 95551097 95551121
    0x60903090b1210051c0204020306030109020d0303050405010506060910030c02070f0314010c020d081f1206021903021e070609060207080703030b010e0904030807110d030207030e090601020712080904 87
    0x150000344003880e040350790700303c000300821240e60407803119002e0502103400e81c00c1000b07482964040300042064400b90030501d107050380142051400c14a501c0c001d4010801985e0950351580380c100041c0070b6040000481d10400b4000300468440c08000700124050640c1d90641030840c0140d4200298190130160a8000355104331209146400308149003400c49620142003030031540300002e01c03c0055000000c0a4001d441024119030540f8286400341c4400503035400780035071400ca6407040d024403100303502510050010203000b910098450004500344e000d10701e40c3c000030010a010000720312941d0b200a2a503248500c10100d6030101d03d844a0b0207e8004520550394240300184131000c259052050754801c600c01d09140341100c40301e0012407507050b0010402800d1000e9200420406409054401e0851404004840c040b96805038000e0180d0812131084020603e40d9a87c0c402e07a24050300003d110706010b90080aa0514040d01200070001c0b05030103036408a070810034540282c58074000c101500e02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 95553597 1250 95552347 95552377
    0x1905120a0201180b19090b0307200f0d030b0109170d0807080103081206040e0d020c1809100513080403050d080901021e090402250b09030c0a060903090b 67
    0x1003140000340010b80c00321000303540318401c042c0c00e000381000d00060303441100205005c110044000d0320140c40014498210349140200441004401588035140d075000700707040c0c1001d400100084512503644c03c030a11400440e5002194407504d110300c245d2207601058014980000655614540a084030014540c1c2e5140c0d9000451814115034101e412940c000800746800100ca615589400000e8060000c00154051000000c9402c558841d0400c619600d180001e4030080c4100b00f03806559040380d2100c6034010440c20340c0c5103800319140452107110b5100c103400303801c08400841c5441c00502c0001c000111980c43c56401102107000d16001c2c0004c3d510650041620344080c4401030034034000100b41040c00e0b0b0040090b0700c00001c07850f0341ca400c9028030b09007494494120348000380284c0030341280c00e20f55400d0300c000b00110041980441410070b0040904156503100c008416032a48161a03400566600090b003110001d80030342c0c071110400c0c1c024948544415118005ea0106600c081c1c10143c40c68 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 95554847 1250 95553597 95553613
    0xb03070215010b040b0a0504180605030d0509130b0307080703030503060415030305070209060a050607081206010903172802010e0d02030a0e09090f01021c0501080615190512 76
    0x503404020a100000128411a095624000fa00c40031407245006464aa070000b00d9010304145c000c100b43c8002e0070014401d842c60314404140000203050038428103110f0702c10000342c940b10501500031281c03400300190105500c54890250700340949400d4042c181c152285141c0001c2c511014046103014610076035a070344c1d803810f01e801044182c0d0110ba02e00024410101e0082001a80020459818540c1503601d02e40b5980c0394000105503240541c4807540040c00041c24034204019500240a10f0035401050207954803200d00456842456001c0144941045140d00e80720302d0b6074502420042100f903403a00c0000e00031031103402100079410180c0015070345400510110241c107010320b40703d40046200460038140070000040540011084450056940c000070540c420070600442e400f045205c0001d55079080801c0b410107031100e04144030b0703c85900c2e0000101b440c040100700345000c0c0100c1e44244012030300f11405c021100c204002500c104c65280c1600103115100d80c40015010300150001d42091 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 95556097 1250 95554847 95554861
    0x250905100e0f0901050c0a0c0b0916060908070f0302030c120109050102040923070f0f030204090606080103020a080303010e1b0c0601030503030601140306061b070902030406020301030c080312040602031e010b03 92
    0x14883c00f40c4425098042442601c8045170b0080118010580000b0403200320307251030b4035403170405030100400e94bc24a40090b0100b0748503040300f102c404613950002110440c507078844526a01c4e0b107050200039819001a0204100d5241803031603c81da0f90100307000081c040700700b9920282240c0c05680418038840d1502d80107101d52075400040c2203d42c0480e000d9501c5458401c0300200303400750310442030091001043e1a52181c510a40c1030720081c10000c44e007084283d0f2a0f90303000c0c11100091204074070803403008501245454001c030550341210f8100340c403a503e644510030701002002c0303069003440c00d250060001c508003600801a190080d80a20055a641c0c14003070001070000340304080c02181020304005101c003644608045440c9074001d03803600b20b440c0000d011a54100780082c0d01c40c41d401d6001105100a11a1079401107048030f00c210f82c04650640c5d5081b62070340380c0c0922030f12068040783c804000b4002c200c0a8008540c415603605030808861a009404409484c01707030001041048003204110701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 95557347 1250 95556097 95556101
    0x210153c060e0102010c0f031122140d080a0f170f04110102030c07350105010801200307120b0d06020d05090c030a0303020d11030711250905100e0f0901 67
    0xc030b04080c8000e0202603907558002d0302d945040c0018408041e610b050251340e080c6000159446d60116210305007400050340d444e142d4800c9a8052100140540280e010303140c501903032150350715903111002c40e003802c9061809170341c100f07804240d80c414042c1c00c008030340c3d8014004181714811009541c00301f0f040e08140c2040080002c00a0140d410755004000a000b01d4400003443d40880c0d82800f40c0d8800b003180c81c08a020031066520620100106a10908940700e0303064001c58182e0700741000030803d6a0030034210301d00c140f14800d0990340c80c80040020903801d03071092102d02c10504580d44040307260f2441b080424110702190300d003aa242640450446003200f42400340c1a0410b81e00c1c40217101084002c800030342c4400c1050380060a059000424040004c2c00b038003c2c00d5901c00d00e22100792645040c10000e026040040008220390190b03d108002241803900341c21248440b0003c508005030414201d81c00805010702a91304030100e840f400119152000d42c018400c45000d844d03a000b03400d1040305103003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 95558597 1250 95557347 95557367
    0x3020105011a0f0d1d15060a0f050f0301060b030a02090f0d0803010e10080703081b060709060c031103030103060b090903071502030403030e060108010203070210153c06 74
    0x104a038001030b180c0d1150300c40d18003922a4900c03141895942c683c07804207260010308194a114014080d261010040f001c00826040810b00c40000b140010b0742d01d080070881524114011004004000041806941040d5814070903c880180000600035243d045044190f00210307040e40c4500d400045030301c0c0c50308207003641d055900b6094401082141c5e041e500c0082d103020500a00e000302210301c0001e1810021901e00500915400095071481c640303d080c480050b5120350004e0621100c1c07030410030750b4900c0000b280c9219031b000c0c1da0743d1035605041400440e41a80000c0050b020000000e568032408401840211700840c86040c0c0000d0a10074441400503008000301180036070f800500c0302e140880c140a40c030000c68100260300583d01d549030728080c0c0007000515540400752140d100003051381c0300154015401801c05400701d441c01c1102c2500b00c0180c803800382480f00420b020030820085038410038155900c100840c41c41c410b1050810600c5c4600729418a01c000d051a2200d608012203600114110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 95559847 1250 95558597 95558609
    0xb01081c020a08030604020304021f080703050c07030f0e04020c01021210150f08060612091b030115090c020708030703020102040936080408010905060a050702060402010207170a060f05040302010501 87
    0x301614010b92543e0916000040001d4092900080054110368400a1000c0d400324581c0713031403010544010006180200403103074900400d1410000c01c02c042514400e503500c10340c1c0756440344003809054508440496410741400d40141c2c0a002c2d0a10000007070018003598404c5c204000060b00d0500854071002d8038942c4034401240854203803050913035000d902100c61585609021046880d031102003411441400c035003c1000700700009001d142c0c0030120342e40303030001e150058401c1c8200c4c0300c1c42014200d5944044250a0284442c8100109803440d000b00c207540c05140107541d0045e81e510741e482d00b103038421001100140d500250038012000c581c4141d840b40b0010a0740521451310840286880c2c4d20101701501500c224141080c041140c1c0904860261000030300a00000007540382c104ea580c0c6098901140316400d00740040c40c41da1001801e14410f60b0140d0003001070500d004400d44540344441240203090080601e88004990580119040200b8107a00000c40d80b8140c14003e0031100107030401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 95561097 1250 95559847 95559853
    0x1c090203071703040e0c0f03150a0902030c0d11040302030a0c03030305160f0e0d0624080f1e0a050d0c060f1e0b010309150e060106080907030b130b01081c02 69
    0x300e1402d840000030b0710709950112466405a031507005504000d0b000d0044090f07000c1030004200110035619144142d10840f050300c0c1814495250001e0600b81e0004891514041c4024494a20481000c0d04a10103255600b008146000c0e201c2d004241451040c5a051340c58a1203c9401c100b010f9061242540c0402e0b800400f038103100402000400440140910408001c10f00c0b0300c5d4041e5603124450615540d42c03100081202d0410344000e0403070b0081c01a20800c29200d80c1600013002000171440d488400612000340041c2512154540180207060524607400d10400503141d00080382000944140d9045494580c150384461030030344160341c0080c02c2400224240000300c00409070160304061000c6d03041d40301040d04076071000120b000b4001c82c1e4000c0c0c0203440007040d241280295034040d443c40700d00c081c1039070302aa80742d0105039081039040d2403800541c1e104c1207080011441f40c0d80d1658001c80354051041846483c0d07141c844c07804074280c102c041107070012801300580d03000608213130b19000034074006 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 95562347 1250 95561097 95561129
    0x15020d08090d0c020111010f0e07210b0a021c050c1216020d200610030b0c030408030a1107020d0c0f060903020307030b10170312010504060b071104021c09020307 71
    0xf00b060381d039038500905002c4510100c2403007140a40241400500c3d2900c100700e403074012100150303512164800c02c403a00c084101440c151022a40304000c11035001105048651190b4801b00000d60040040c072140c122500c03000c504444081c001c1c01e000d1007205d43c003540c441c400304880d0804100c024040f0580e2486c050130750b40781700f60003040305071483d400e500b01002da140c0d642c00107400351002241248924003442c4c0030400c0390741c00320b83c402c07043d20b0050300458907940c4c82200201192009803030240417040d0600010300045910380000c50110f510004481c10001145e0210f02c40680c5081c040b913034512440c0040c054010030f045102c0050030285018054540740d42c01007500d90070300740409071424400704000703907000a05d00c10680041c028413856130800b4940c0d1180d103445c0c1c3c01040c002003590410100011300791400d030050b40181c2d800340101c00e2914075580d5400c10b010b000c4002240d003007070b0244048821000c0c141318802c040c0b081c40701c0c08508030701144101810043c0c0c581208480b4070f502c8103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 95563597 1250 95562347 95562373
    0x15090b090703050406150e0f0f0c04121a040308041a01050d020d0507080a0b0a0e03070c090203060d02090c0a0306080307081207050705011506030f1a061315020d0809 73
    0x150303650800c00c07a050000305612213040c0321014120030754511132030b0b400030100021107141807070350503120703007880800b400300ea4980e00a490f1204000b5074a4159110081c481808450030b42111890b07018441c0c80529100105c04070b09040c2400c0443d425808689410104424003081103500c3c803488014803000d145035814100090079524440502900030207406990808008007000181c0181c11010112000c104091400950940c0c04480c0c134540349041c8418640041c0c00001550074442d4040f5100c440310b07091118041c000c2d0402868a907100c0a030103110b101684401c0f20306c0d80103140c8440000d0761050059005000e0340d00c03941c02044140e104000c071364049903da40035a21a58400d02003e49143c885280c00c48040c09000406000c5500c0d00c010344d0301403441c200c0c030b86045540760385090010344d4480c0d06050840f5202e44850b450941c010030f036082c65180003001001114400c0025144894803140b6240f1860010716105025038844666014500e800c4064150f102c000c140003001d5400c1418 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 95564847 1250 95563597 95563609
    0x2040b0906150f090a03061b0c0804050409031803080a030c080f060603070c080d0c0f0e0102100f060b1603140c1009080f030f0115090e0c070816030315090b 69
    0x150009500c02804202c2c05150026141100c64013070008021813203440e200d0502c01c0050170025258180d0060903070007840003501450821078043e801c4541c0c81d0600e4034100920003e8a0495011401c0010151a8409818050302d5003070186000d880216103820011001604580c1c000e0880820b0248010810451011240300f2592240c400d075091a200d40350309034240c80d400e070080c4008250b044042560b00f481c0440f40d00480200c0300c00d950f1080d03900300c0d109007601d09030440100940107030400492020340700e0183c0c204165240c81c1c182c00090343c03590340c40300c030440e80c10400351443c3d003150a61481c014540d020400c0d040308034940d88010b28142c000c20300a130742d800340e6410b40d2400703e44901d02c02c014090104240c1d00c40340e1041014954900d01780c0300c0c24003552400d00481404200708013202821902c1214440d0a84801101c00302c1151240c10200c10755400100c0c0c110b5034034004010302d800c80d11854101245462003a01c1c0440c10320442581c140b24920782e904001070b1240f0306981c41145e03136520 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 95566097 1250 95564847 95564869
    0x41d06100e01090b120d030e010506010c0503070209090c0a030614010503030c07030303110f040b0a1706181f06090f05040917070f08030702071d042a0305150402040b0906 75
    0x803140004403021300e1008100031000050491090380140d4103001c849a8141c0c1202c4010016000204507035501e0400641d802480c0f40405000c60303000f80002c4005050150886e07422843d6074003207892082c19080020410616500304681d0342e0b803120122101c4628040300c180c0545000c170080c506220004000580d180c0a80c4005070425898000c03c101d1845010110f50000f03800c1410345540e9611910184900c0d070100d103010000071203020203001c18413043c4401320b01698008080200010020446803001100075214401c1c26005006403642d03079040000c1500100a69200c0b03070035862500561200002c096440180a00d04019460001030301000c00f000c4640c030030010712915084c0d5800d001042c6018414024589140003007442090340d00010803200310780012032018510009420148030b0003606907030003040d80244003800d1014a1500d2030480f084500310800200240c0c0da03031195403400d900310700f412818840b070805000650906000f104900074058074010010709004011800440344 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 95567347 1250 95566097 95566109
    0xf130b04080909040f021806011407061103101a030c0a0813060f06150e06040b0a1202040f0510050a0905010807050c0106090f0e0613020f0a05041d06100e01 69
    0x60000a4100005402594891400a4003101003880c01d850301c07080002c0b841d041a480b40c2e1050756180d9220301c20003015031003160183e451040010203440b204a09420101c03007116241d4480100f804005840d03801345110768182e03282c03031400a280480ca0010640b640749070180c0c05100700104180f42440070106c1d400c0780814501104280d6900b41100480c0714000c0c0014801400c2c508941d4544d103068020500ba076610701d21a00c000c0140403005c4c2d81c41075106200640048040c0400c02a81514001400f400c1e03040b402c0403046070b03125540c000100d03407054101540441458400b40000e041c81105011080d9042c140146091905003029014600071302c1200c4c1040300000004141030302c15400d071400c8031040d10007805400e48400084000c1c0803034a070f000130706914159650241486c0001d025014454403c09078044540da0703024001708114910300550845000070000849490b01d20a40002041035010b40141e280040040760510740041d001d08202c0c01c1441c001d03c400420340c0e20490460340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 95568597 1250 95567347 95567363
    0x6270316030f0c02090f070905030304050a050409020a050a1502120c031b070504020a0503091c080403081f03050d030b0102010b031207050f0f03030702160e0103110a0515120f13 78
    0x100c401012140f40021840080d00403141e1818468107039070012400303010380410b031103081c001c3d40c03140306141d500d00551003035560042c11003404008600b456070100500c14006405a0b03003ca44800100389081d003230354010b0100c506220b00f00c2c5030bd00e0b410f114100101c1d154a8403a03181045426815690b8000d166121000600111140da01c040c41048603d005000141c419074461f140700f00054640d8200701c44c0200c10b40202e034410700c441d0041034420aa100d0040d140d114094a86450460345054000c11400c407103502450340d650316140748200c000c0154468070081c90582d507800c0c801016140c410840906580c1030018401c0c155501240700e0445099100d41c031619142e140c107000389402030091042c1031340d004541560704039402c00701c011407082246800b203800015a40c145503100003810320856424400d034800500005800c1000ca0346680700041200c40000c1d102d00014144d00301c0ca8020000c107400c000303241040e131000e41c1c10f029800100c00d0056105031030b0001c0c05101c24010301a005203100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 95569847 1250 95568597 95568617
    0x3051c0c11040912031409031201030314041206091109010510030e10060905061207060f14070b07180503070b040605030613050c04180e0c040c0504080627031603 71
    0x344030381e4441e046140d0030031035200342c000030804040c004084006c015607001450400281c00300b1400400c0355540307041004202400e07842c0da28116542540c1c0200e07013001c6403042100156201035290b400550b10f015190000b050f03032082c41c5c00e00c01c17061705008090081510304010889a581c0c4141901c2d00203240c1000b14034010180b15080c03d00220301e0400300003514202e408180314040d0f0744007a02c150340503119911125003240c44241e8600b15407083c8030010350a5103c0d500c0d481d11031294464500f8143c016681003105981c1c40c1e000c0550100e882e54000b50020182c1c0382c00c0503031a0204801400140c0203000c030907050a00641641c821400350400344040000850215107603240c0f00a00070103448410069070500544521081e0310a1165505ca0300070b40000240c0d50885120f80013210307070700200030701101c1d445809000142c42d002c442c0318203001052100088480c001d04c00f00340b140132050f9500203200d0750003141901031a0a208490101c2d8001e01c445d01c000002200b48031601905814910208 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 95571097 1250 95569847 95569849
    0x30c012001110705070f0608090a0f0c05060705010b09100f0320030604200103140f04140d0503100f1a030402040609020c1e0c030a030305090f030f0403051c0c11 71
    0x240c00d080394440807000c000583d000900078086010029580d143d40201c10740799443c60700721a03c242c150342540c05a000031311100c00044001115040c040d2007050b01100b550340d0b90000800d1a040349005031126511f40f0f0310301d400c501d82560700c6a03000040c1003482040340e080500c035804a402c0350000400910300c02d0100006010b43c9100460002d0005003120902d14040c0342100c950000c11441c0c40c08064440c1e0f804203258000d0203490070348180c4407040c640c180c0c0ca0300310100403910094016201084680c80304040c0c507030180304103200d0301401d07140d182e560304024078404640030095010702584100307010180441c035404400c1184d1803c0306d03c4401d440740c0b15800050010316081d4403084a00744009030768401e081c40890085c10780a81c00b0507007288100120421a2104641050f0541c07603000003060b040001d000b64051504100241c04481030000010b803414907542c07103031800c20000750700883c0c2001003000400000740b07080304081d03080c420028a48005401a8000c140c001d2280c24220b00e44051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 95572347 1250 95571097 95571101
    0xb1b03070203030a050a12140f070e060a0e1801080c090c0d05010e18070303020c1c06140105120706020d11011503081b060103150b01090806090304060e030c012001 72
    0x594008043d00d81e10210741001800c980d00c96411100401d5051419580071051803140680c0540b9121001c0066502c0500d000a002e1006048005000214034009040d84844020300200c01b0390ba1501c400d0311111a04105000001c0e44104c0d95001c520780041c002e0240c085180b4000c86003d554211640c0c6075041c10310000d008040c004140689080000075007101e107441d44e1030040c420b10201001c3c061440c1ca0441e1695039600025025a001c00004082030408c03844000d12507580300258078400300d903959003c0654000c034103030107211a40391380103104d01d141c990500da14610f40c1c01c005049a514101010f5110090f000d4500184147c20029004190082d008034010110001c043da84031900c074500010b094101150114180401c001c0c20250400300090240c141c9403c90b20854a01034501681c0003c1c04006492074104410700d0700001c3d04000c01c0142078041c24980020356101c0d82040360007800302200805c01d5200b40e11420780c0e410302d03981040301141004203a080c24074200486e811880c1c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 95573597 1250 95572347 95572357
    0xc0503120a05011418010302011d04060801020a0f021506090402180703091506060813020d0f030c0b0604060b0a03151707170706051603030603080c060a1103010b1b03 73
    0x4000040e108105040c50395611150684001c401d0700c1d14041080403d1060412281003402d04a00704400140003560243c03098186660144a10079400d55941e03020506848195205c184160340100310440d00b103810030300440c0d8405540c80240129850380e1140c1440140140c0b07030a000d904120702080944d00c40d00500c031100d50150014455504098000a000700320b808000d5400403100060380388010900e000e042c048515995804130141c50300059103204007000d83d8102d9001c1d0000105074002400f20b034a1854075030194455640340c80807418200c0710544001c01c0644540c1c9050814840c0170503e4050702c52000d45031800007404d401d152204003c45001e60404820003021422124500710009125000d84040080389815a4588040182e032040c0d1405113501098090010b40907056003401b04020b0540030b85030200d944c0340d8a466200203540513294148060f0801c104108000c0420301440c15000a01c442180c0b0303561416500d03030381c94020754078400c940c0f052900c42d20480410400c00c1d28 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 95574847 1250 95573597 95573617
    0x90c09040b0901080f060c1306030f0204031403040e090715050304060b041e1521030c1a0f0601020c011d0a05031c1e05070201030504050102161b050d020a0302010c0503 74
    0xc03040d58498a00c10340c0d170b4109481c0309040d4416100003d02124100094804900c03840d0010348010781080d0007a00900301801813640403070390171702001003c1420b00440c0a822002000910380e25420f02005c40c03200300004120f01056405240100000040c87c680041c034072034145441d54807a220b916198028180b0b10310001e91043c10032103604031b150141003600465000740c20040099402c40c0900c0411003c0c6031140300c0c004030400522800751140101c89582e25403003440c3c4640001c48035554812141c00401103074046825082c10000b03200b201450710385e00b11000740003c00e00d02007503a0000702031880101199041c880a40c0b440180e64450f50220070141030010266118010760003c1000c00081d902d18445c0021582100b00081c8105251442c55000d00c59481c2454882c02c0e4006402410005d4000c41d42503500300881c010410003040121103251107110700a6003030300000d4404e0411107039500010700c501604c44c0030800598800c2d1180013101c0c0e0a09207000400d0b494101141903002d0000c040f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 95576097 1250 95574847 95574859
    0x603020a0c050105240d050601140315011e14090408090a030609050105060103050f040f020904151d0d0f05030f090309030604080901180b0d0b030102210105040515090c09040b 77
    0x111402c0020659040282d485c11000030700720102541c10441000310403113000d03090782c00110041c0414442c01d00c0881c01c81c03101904a400305100d501e210852100240e000c3c0c10080c084410300c074210f1000b88007034401049480600f442c007030381d4000018014a005800144215030000c2c1c08e20154854162107001150040c0c000c10038407025003007141c041c240032513029000a00c0d020010f03041094295070302e805140c1080d885540c416442c2e0a02c882160301902c103072501c000d811307000c7c002d9822501414030203d0b90302c000c0c4a1240740c254502440e0580c107400309400d20031441c0303010151640c42070903281d01c9018110501301d5611003442c118118820700017804e030035029410410040c020507200800c01008281e90710407050500c5000f07901003419600034072041034410418103020f01d629400065418070003c0005240408541004010786054840d10784c50080c1403004002c03503c9e080c403039aa444070041c03108019000740f890004100a03001018802a04804103000156484560107a03026100250070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 95577347 1250 95576097 95576101
    0x818031e030904140f040b040206070f050f100614010c060b1009030c06080c19170a140901020304020a0611010f021606051305030928030308071211040603020a0c050105 74
    0x26989a501c0b554406014a05003101501c2c051440d1980340c0c440c0c1c00300c5200410365100d03550303440c209140180007231340c2c01038081c0710314804034594003a1050304512400042c181c0c00501c03121070303080c40700c44000305d41100d00d0600c0070004201001340029030801c013483c2c640c41d90000d52410384000d150910f90550001c400d9641d00303d010f5040080c040540b8002e50300c0c004142c0c0d460b01c04440040084500d4031040d03505001c000d21300440304080020700718103410086006000510f8004141504850000c3c00c0307515885084180d1503802c01a03034001400303000035403a501d02600451011a400d10400f02000031500c00d101c400b20007035204508118207080c00355170b034000c010860a404001000182c40c1c06117000c000c212104c846003508902d01e0f0344040035508280550040000050719081201c1c030348078441c0340095400c60a90f010001462094a0b51401802c00c800700170800c503411104c4d5403140e8078040340c8070784640202c0243c1d01215103902d000361360b6a12401c0c3c215038206000d00c1c020048d60030141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 95578597 1250 95577347 95577403
    0x6150f0c031b0304080309040207050307050f1006080105060906090415090c0501090b030f0c031302041107050d050a05030a05070c02031005010e0a0b090a020a031e05070207050607081803 82
    0x1000c405040b00405160306070503025a540344d2141c1d02c10f400c400d03801005401c805007000e40150030300500503c10341e0b0500c0c07410303101e890038010400780e12002600b181e1404c800b1200c09101c1c0e400503007120b800800c42480c002e4081294640083c00c0d02c0e05c40d01e0f550000034100a00418429060000d400090024484a1a0203c0880c4141c0034090205100000c0400c0440100003924825402e906410305ca41c5c4403040d801c140355001400e8003d40b40600c0b0307512005600e60b801001a0300e10740300441980c1d085e4174286503007403c007041c040c0000c100042004594440d44482601d4021240890000e1a51582c4c00d05441244a01500941602408242020120043e44400e040b1307180c0c07054421080e03540d0390300c000455240040055000043c0b001069600420358050400e184050900040d4031001841d101e074113030110070740741000d02d071114100624264140840d40050a059034200e091641075078580c88140079106450880400c48142c041c00395602708442003042c01c54a280d0b40f8084a02c3c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 95579847 1250 95578597 95578603
    0x30a050d050a021e030702150405030d08010f0510080a05130b0109141501020d1d06040b03090106080303060607112202090a081b0108071101021606050f01060806150f0c 74
    0x2958110144c007401816042c162124003c101140294a000d1460180300d0360821030161030808644050a174180000b140b6034808204001e400001521101e4141d031400c2d80038000160150800d502990010710b0402419802c46506a0010307450304011810b9500c81001503002400c807540a011030343c115000103907040655000f80c00d4403070441c901c84031a40d11881c130f0715030444803815101d0040e4003030306260042501c80c04030600c204620010103207000345110001000390704580c1080242c10300c004103000e000e4000344500002401e9180c00703581140360240000382c281c010000c0280c0110900c008004a55440130700c14440c800719841c0741d0400e644141d54100094100c0500140a149000e0300490400381c001a141c41925000d04403600661181d80110b4000102401c148140441c0e58802d809400080c009024809da07007118003451400d003401c1603020b5401c080e00c010100040d010060100a5000d50340c0f0381e1200c01030f54a81190b82c0e0740d040401340c2d481a01441d524190020840a000709008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 95581097 1250 95579847 95579857
    0x1e03090405040803040219030c120302100e070807060e130b030c030a141203060d03050a05040b0705100605060324030307050105040c1a12071803060207030c021c0b0402040b030a050d05 81
    0x20742c0d4951f030030364003c0c000020308205404080d00c4007002000c01c0125808a41d55400110701c2881503e444061240c7c0d4903065420070004480c0c075030001d85050058a0082102d04002d040d14070b0000d03804554100410b6540c0b407a03414400d4102d44844043e00161400c00c10450808030140c21104040d10504059038400c00c00900011a80900c1076046075042140382920300412008000884c5400a980e054400e42c0c06044001c0c1441010b010008074215500017816489005602901d0842c22064940c0c04a424507001a84203940c180b081c4915000c00c04543c84021741c0d01d100420039554101d0010b840d500a0070310051482d802e15042008015001d13401e8030031641c41540f0440508003981413941c0a000e1f40702c0b6490440b91000c001981c05104860326004e80d800300803101c16881c1c0b20b485403804daa1014071709401040c060044e60085007024900c0501c0c00c508080804004810f90341c13004211203025102034800e54031951318441907a0244015010182d0243c1150110811101c002d480c030b4000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 95582347 1250 95581097 95581099
    0x9050d0c0b01050303040e0a0504021504090c0e0d031b08040f17010501060212070f0f080d05060f0109080a030503040c0803040f060e030106050a060513080609011a03010c021e030904050408030402 86
    0x41d400002600d801c001007554243c4480d4183c00d21140e6500c1c415100078140204260380c4201a101100315503010f050003031003d4514140701049500203603102500d4042e2013044180294010b04c60007020962240045269180c180450440720b92242810001d0b40aa0740100700d480421400020300010100d0409070320f03a504400170300c4a81e90b00c00090340c0303500d4002c0440d0700459007000309000081000309d101500e10700c6000c000360a20b034a912002015005051800107241d0307103c084c01290b10f82400c02c0740008000b4039040c180e082c01e10001d43d44803419020010203004012003c9401c200c0c45082010140c1018022039031515550002c4420a025500c12100841c8551041c41c01c541011f000b40300a07208081c1c0460f0841c0c3c90214100c1d900c0e800b9102800701d0502411011406103010b114540c0169512070003c50120324600811808114898031a403080c2e161050301c21105030003203085c00c2ea100810410022544c0e000e800d40e07086114400a80794007500d00801c000030000b00502540c040c0d40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 95583597 1250 95582347 95582363
    0xd150b18060a1e0201020c0d03020912060601020d03020a05071407180e0a030509220b01020f1606050313050109060903030609050402030a020402090105040e0112030225120609050d0c 80
    0x4242446000c1c490002d051000441075044030791200400d14240c02c955003544001441c00fa115030310a41081c0c1d1000d01c450009800090031089450030502400b035a02108010300303d00c2c100740c8000303907490480c1806141031540128485003064010019a205150032450140c0304440c052100c58444116008840841042086520a03400984924108486180b0082c40741101c1600e0564454014441445d48040d4000c4158290110400910101c1050481c04900e0b018254000780c1480d4030f80e900705400b9805082c0d207441003c01c4843c0d04048602a0610507560340700d0f400e81c0c0080000c0c0a4001d0019800d04201b101002550f80c40140742038041c0d070f030030406ca030b0300d820120058907000c0c2c40c065455071150103120090300d0154014030b42c08105040c11441d25070307110320a40540500740d1240c1d6138042d0052004090540600603088800c20100c091a400b200c0e01d02581001c01150050190701003214141004001456001d849000d03080300c12900c803807041c408000c00a06240c50111000a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 95584847 1250 95583597 95583637
    0xf0909060109060b071109060406030f11030d020102280509061b060709120204050601030f1505040b060406090b0a032307021005010b041406040e010b0a08091603080d150b 75
    0x44c4021059850041c1e216020b1600302e0548401c00c01c03400c0001e002c6a50081e99160000009880c00c203060121500c075504a21054114500b054203084041c1d21035819640104060034580c5195002e00e042101c0600e051020641109001c445034042c1350344440c3c1014000420b4880e400aa030749116030420b2031000c0f0b50156940c060b0403942104580320713100f2403d095070302580041c0b829403c40b950185040c9130012303a4034110b00c400420f55081e04c811035103620141c24184503d09250080b084070340800e42d00345203000e240003402050103086120b02d00c1041804181b0f80078151080d00710b00c95a0199154030000b41a00c0c20700c01200c09001c4d100c840251141884006403c0d0150040724102c800b0f0320441403e251500c030700176940d02d00955540794044420000401c3d025003820201c2d0291000f006040d0311001140702c0a031000c1c90140c0101e015030f002d03a030105881c0d0101d10201058a5004001c00c0c1c503101d030030f1003210280c0060040151644040c00c0e010410221140140016058240e8800303025 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 95586097 1250 95584847 95584859
    0x510050316022d0a1b0810050f0426031006080a1a041104030506090102031e010807030201031e0e03191d04021c0c0e0a06030212150f090906010906 65
    0x200c1d81030300b1101007441042c0e10b010810b00b4040c586414040d0f168140d65141490307a40d0070040d0000180c141c0b14101d80d03001c0620514000b003154038111021014104194140b01014540c2e220001707200800c00c40851420201c500c51031b00300c208120300c00050690312802c140ea01551600400d0050780006882d003800070300456498019100404034400001c509480b4031030606c001351480d04a60f41c19031400300300000000e00c08001d1f65104681041c001a12810800a01e4465180f80001d24203000e18910040c444e40001107410310440f60f09081c0011421840d0007414004500c90361400c80c507d1502d1000503080c08044010721904080c00c0c00808040b84014090711312101514990f680480030103a42a62401d0590041100c102500800c030301b100200b030310030000d9400040c0210000303041d013069241241000e694041c0580030a05065080c080c04402e90074903030750020452800c09015105002c1c654603081d903d1007141030081c0251400f460803240003540d401c0203103e0302c410180307442000215 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 95587347 1250 95586097 95586103
    0x1a0411030102030403090306150e0f0601030e0f06060f150a0801180920040204030b071110020702010c020d230606090a060506031303021f0903030b01031109090a0204051005031602 79
    0x1316650646803040320a04580b103d000525400c2c0110998200448000c61041c10844c20540b02e034000540c50011403520074001400d8808004030522158814084000003c0e804205258021403e4800448e50806140094070002c200c00440d87d00c030307100013566500961f0004507107060383c02900300c1d10000036070b8a4005044512040020303084c00d0205113403010080d10030844445503800140003600780741e1207450f1100411000c0d2841400300b043c0079a00003813144103100040541d90116003c600b0031140e500040c0880c0e4036418028810208100b0810820800300d03081c49402d1540003042091105110342039030b6440301a11224441c041b00000103a40c2d021a01070b140949401800302d504507142d40c00031103100c901c202c20440950049183c0300c2a020001e81071941800301054000c20800320130704028080342c070614141c0f4101401c024a0300c011594903400c4945c01d20081d101000d5965441152500034011034110a500000442103075180a62120146000d0441c064401c10b0081c1410702c140e035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 95588597 1250 95587347 95587351
    0x110304090c030902042d051302030601060f0e0d0305040605070f050d09030201140c1905190b0a0c08010602061603090b0f06030f0a02181f030b070e090405070b03090a1a041103010203 80
    0x450706c9204684402040140e4000c190055002c2c03403000c4000308154002030811500f40c00c01c0740040e0001c62641c402d141d1001d08190160010344000d4044030490300e001b06140304034083e070f20500070001082400c1264208901d18915005401c0d581c0b050b101c0a070050141e83c961109900080c403240100d510424074404030362254170401c006001d401c040214800c0706d031104c1a0143d9943c06020000c80010401544c00c40c907462088801c0d01603850300fa450313001151a60642081080a00c00040c40502d8000070101d8000c0741c2418a03054086c1340000490141500c8440107240d0481c140c14414a02d01145015001d11021000d82e0600f42000365000d03511002040040d500c110f12030420007892250313200c07690700940c58200d0f603003e40c00348400c2c80020200990040301c0c17031034402c400c10501380d07406050101201422103c0000c1c9040544070a543c42030385000d00280e07641e0010206490682c00c00c1407a4a80c0e502c0150b40303005c01c0d405800c0017520303082118152102d1590072200350191906201310781c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 95589847 1250 95588597 95588651
    0x7200f010b01020c1512040213020403150c0201020327030403082205010c240209091603060f050d1506050909030d060902030f040b0c0d1e15030210110304090c03090204 74
    0x1a01b04100d10040b2041010054020703a00403161000314400e085650004102075801407803000d4131240000307452812241109050b81c216441070045c07050305014840085081500201001101031881d907044c0c0c00c51103140d1004081600c0000d88241c104000d0414180002c2c4064a51080550302e00064543d104004d0000308552000c074650074944039400045d10803400d0703032040181007000060100b41c92201c1135400e401c0e03401c0382818100705560f050080030041c18070401d4a03d080740ca420086400390300940002030062064621801c0c2c524801d81c0800e005080060850340e040c204204002c1e140d80c81b144640003c0c0e0300717018000c2240007050003200d000d4014215049003035030751612103c441d188040c1115420400820102c198500300d406140000d103045404138001340820034980c011200048802042d50301460010405aa00d8000403002c00a0900341105c0202c41c8080d4241140f00c0e03034206044541c54440e407085566410b40c49000c1407482564204220001d40700d10900c814800c41c040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 95591097 1250 95589847 95589889
    0x4060305060c0c0705130504200f040f09020d0b100602150703150306110c06011d07050a02010917120a2702030a0b010305060907090903020607200f010b01020c 70
    0x1041e6450012401002100006025200c11a44820001b21191502d00051008030345030802d06c018000c04030104030002d164800380f10010601d040100d01801596003001d80b00702d130b860350326a44808881d0004200140d000300326075040c6c07280e4548040024419a050b0482d903881d460003240041c00041c4281001030031040d100d8a170343d42c5403411409004400341c00c3c01050910000000096110301449842165244480c0e407508012400075180a40590243c083e000d0300f20b603003000050fa2802000c2d00848070f850800e81d600702404044c0c0c054014400001c2c140403826101c0128152680042c1107070311244041d85841c1d48404200c0c00a456041c840003581006429042100302c0da0900c01c40049803000d825503260342d00603228054052000d0303000b921f280c1c01000403c00b94040600218001d0506100c00304005400d54800139580c0100520314800d01c0225803802005104c40303030002240040070021200d0310401d400c051800380030f82580d00340c0075200d5922b010200c0e142c511110030b1061100044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 95592347 1250 95591097 95591101
    0x30a03021213050a1e050d0e0112021606051018150608060102070e0702010e01020f070c0510050405060a110a060b01030606050903060c0901031e0501030c05040b090412050d0e010e0c0406030506 85
    0xc2c4419143c0501002100d17007228030032550001c2d1051100d0b0000140d207844140c1101c0401c400508480040e00c280c0248520410800c11907590f10701458414175042032000500740d841c200b9005001d100c2d0741100500d0302c51085d0b403411402903a00003600714540102000c0042e0395079081925480825034450b070268101c5030051101502d803c42c0d5942c80003840c40041000c2071b4071385a81d801c90f84010354100c024440085c5060900c003594640b90300500c13090310704104400411710700901c1c034080c600a80e80320b52400140f6601c154403600c00f8404d210900d106903038125070585000030081241c0b02c0da840c042420124001807181c06201503e5889038040c002e40025a15951101a580e0105488a046c143c2d0f421040705201c09030b03159528004949000001c59505600f000c240f0704c1d51a6001520650520b45924039a403910600c10342c0140d03200030890041e5020003820750b058040c0e14034400c400e500e010350a100ac55015044076401d5403002d0300340d41c81030301e145050109070740311740c0005000c2e0760100c40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 95593597 1250 95592347 95592353
    0x50903061504060e0c070f1110020a020405070207081f15060509030706030e1e07030b04030f091211060a0e060c0703020a051e1002030c01140109050601092103030e030a03021213050a 80
    0x725541c245205960048c2074031020b900003486d07501418000d00c0164408032400e011810644900b43d0072051a00050051a103003c811540da42070500540b40980041969a072410086800241d00e0303600000c0c49041c03042d00c642c0000c1c91b540003500411310034072508000064090203407040b00d04c41c01080000d01078050365800b0010104c501c1d8100340c1c01c01e04c940c1d0f100002241c030340b030384e9a8041c520a41c2c038450810388122004003180504d1b04000c0c003025007007900c80300007100380f01801101310f01a120140c0300c01910509480507003d1400c15508120001401c1e1300601001c191481034070b100726400050f2988400c1070140c5d02c0c00396895920600301000360004240b516154181d101592841228a089500b0000a00352105000d030130540c0002400144502c2d043e900500342e00c500d080c0303030030030980349000140d1900103030031180d0003080d190308a8039030103041c8a60004204801c1040071203680f550050342c010001d502c10109105951412004545495000040c1c0c054486d000360080016070301c961 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 95594847 1250 95593597 95593613
    0x1406100c0206070602041202031c0806121609020903100b1309020604120308040b01211b170601080c0a0b0d021804050403020114060d031e050903061504060e0c07 71
    0x999121078103106540c00113400e40000e0000c1d1090001c0c0c21a008514414546481d8900d40000d512010302c1c541505030380d920032140baa010304101c800d42c046254241d002e60038181c0200c00f14440c408040030100b45c1910b10303001005650002e804070b0b400d45c8203040c03219003110011307001d00f503202810b000c01048112103038106403021400144854681540c4488901a03801a02012804038089000304000e1003518140c2d00d004120228152040500c00e130051804198000e41c0203005100c442502d8049054200c000301c01340c01c6444003103000c855000302081d40e03031500b4880c010040c815194154030300e0a185000a040301c00408016050032010040c54020b500803e131903603540310344a028800150b840c0d01586000fa40250000200b11605c028010710000340103101a0061a14450180c0026448401804081361140e000039440e07100b01401c55240c8603191042d9172520480d01400704511001d24440362001c4115810041180c3c0c070b03000c403264403108440c44100300c4021300c0700b00c010441c50f07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 95596097 1250 95594847 95594867
    0x4050a090b0103180605010e0f0402090711161d06040b011b05011e0b040c020d0f0806030c0402120a0f0b150a0e04020315090f10060c05030d18030201140610 69
    0x5040104120001d61303035003100c85592500580786140ca4400410003840c1d044403003900003103a43e0801d291450560080350a908028110b03904208004081c10502c001c00d00546002c40c04441c1300b0380e030440d0750700005144110b030700301c094441004500c0425580d25183c407030039182c40301c10307101d01c09900c1a80d802034145010103e070a4801e9502d600542500c124081502545400c1041002890356a10400d120890b447d100c628015907006100c074620302c2c3d8100c13042039652000303450310280c40e55070b240111b420040162035a03600a4000700d09410b006990242c000c0c03060141110400441c03809080700b5082d1342e01d08410716044080740211420361031284006020076041030a000d80c80c101d0a0001c00d080380c0c0304440001044940422449a81c030b02000d409400a021b066078181d1400c01100d0380007a039456214480038040c61203007a908204060007a103440110b012410026201d800e2500010744003207401c12001540f0380729010002885950105000d842c0241c0b9484c940d507203080782591400c1c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 95597347 1250 95596097 95596099
    0x30b0c18060d0606020d081506072d0314040303050304110d0c06050306030114010311040e0a06020301060206040b240618030304090207230303060613080f0f0f0304050a090b 76
    0x200c504111159110304004104540c0d503044002480d0b071078140000c1c11b064204602e6001c02001c81c0900031041200c8950f16500d01040b104250703103003030600d0008210b0b4040c0d100d0301855204401c1c080035107551600095281f50181d1900020303c406808141d900c0d103d240001004204244041001310742c0b4a002d049642d503000d04030481c5881e007911400c900405651008000610020030807185003002e0198604070148500504c6517941581c1e83e814816500c900420700450f0344a8160f042500b00b0805000c91a0304010110742d6540c45040094607120110b40940c0e2282c041004290282c1c40310000440c0b0095030180f51007102d0a840402980fa4000d99400000710002c0d02c2022240c1d90910081c801040300c03480043c1d40c0c51952070000c4680c80c0241206080741042d048602403040003208807580710b40d0448140d580d8882c05260100c400d482908801514071035401c41080034940041c0e070050000861088828408000d00c640e90345e44034a008041c2c00c5000020200a0b0509030303000210b030f07000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 95598597 1250 95597347 95597377
    0x1c0813020114030a05070306050a0b04050405060d0f080c010507050304031205070909060902091507020307091e02030106020a11040b0a1a071a1014010f0c11030706031e06030b0c 78
    0x8545a60b07000150410340b0645540c641d101c09000b5410307010b1141c03000411042d1400341500d0316190b6100c00324000c2c0d115103400b0302e449800107001582d449410030b82c216800384410f42d0244143c20031030801e42060280c090990301e03040c00f00e4011170044092301d204550540d5201058a4601c002c2009400007600e601c0a000501c2408622103d0601030140505540600141c4030b1660300c00f0802424204419851901000c1042002680700403034040c0035201d2101020607000003541000e0036681c0f148003a40703109072020002007100c1c3e6020031107a40040c007805c040017115243c01c0803c003c48800b101d00c0c985c130440007001001814811707519542c143e180c3c10f84960804500352104030b18200140908400001c40e03504100d084000948840c0117824070040400102c40440000b80808822064000034400344021940800816a988038101c07180602601c402c2e036907618028002d003600764100d0320105284d00103000030030503d20451b4200d9030003a0703050120b91182c0d01e0000003984000c81c0707109461 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 95599847 1250 95598597 95598617
    0x203011214070b1c1b170c0712050306040c0e0306010620010603060b01090b0307020304090908090a030501290307030204240b030a050106020105060d3e031c08130201 73
    0x10040000340c0400600052400c400c038450f5500d820803502c64207040039802c4441045d121065a00c2440c40301c03080701218020031562030b1001c800d446c038040c0301001040c0800e07619400c2e540b56488000f540c080d520540341440500d107480002d68072521102e4959130107038000c80c01001036600c1207600c0d104040c8170700d80c0800120091451142034807070581081d03860507100c881c61a07007564001642c03401440b40624507800c50070f0500000b9224070444c824000b000380c44002140034041150200e0f0120100101064411562071400354082d0405240c440c820005810100c020840c4174a40a1000c1c10010080d10381e090031582000000c100c914411020a00c4102d01c101c2c0f1003540e0410358000c0c3c120410015240d02d800c079018020344105800040031a4140002c0c02403170b80312000c50500696001d42d0419100c0360700750225495156642c01c0101c060342c45e01c000488518202e8800703a030107005800359540c110100600600441445070060001003020300000c080380c0d0003040c04840c9130702c1450001ca00b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 95601097 1250 95599847 95599859
    0x80f1216080d06080d08090a021e210601081207020603100302060301120b0c04050f28090204090b0904051f06120803070207060206010510030f0e0f03071203020301121407 75
    0x5a0012090110a103583d94028018000104120303401c40704186009211032904000c425264081c0d004028001c4401100d044549028210040f80c0d9400c040c1c034140c0c0103c1680001920101ca540d02c900c01c40c00b0360b03c004214108040391000c1c00c0048a0350741881d00e00d155081c00030079880100204a150081c042c08001640c440340118002c01c440118410b08402504150500e50b201800001141034200001c00107074440c02d0405650729821a8500385125024840b044204a42d00040922410080c0082103038442c070b6014100f9680d22010800207010400301303010b1002000e55001d0703d1580084c80780042001c0c0800b10809210303034540f010505075035902c85000b41c0c0100100c2158180000320808c50b01503410810003008124032320052001707514000200703007500b180bd03909408140d11003850201c8059160803a0710b11800e401d007104c28090949803016200d4001d04402c650507105444900b004a1190080d28140c41007007442c120600d103240e40d10b000c10041c2114103125170040704c5000802c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 95602347 1250 95601097 95601113
    0xa020405030703030f020c0604050d0f1103060702010905060105040212010e190f060603050604090818010203071208041202060705030604020c150708150109140906030a0803090d09080f1216 83
    0xb98803d80790b41400a170a0403020381030545420603d40140b0080c8002c2200c2c2d41c8403214071b4000c1e6002144600320729510705000450f4501140740580501c030300e609001c41d1a070f0540c04400300d54002e506549c03a42c0d0303c135410407040c1e02c01c039200200c2d10100c0700700620141c004c003185184c014001c0c40c14a801c014410f4013200a403a0341800c0c1c003003610f541e6030040013202d0f094018584d0003441100c0802260034656510b0a81d80074004510302030b020b4103e017018041e402001281c00c002d4101110301040c105240340100711800859040740c9904144d00300b1070f03a45000041d014002c812544034203081d551000107200081d0004c0c0000c15881c4108a8a000078407009520503020300400d41d6800c400e403400d60b20504106c01c0c240704150400078000401c10400d110902c500503507240171116003203ea02ea040c002407030b0420340360003c0c120f0280082848500c01002410b82c4010b41d007900d8140308582e80ea50071030b0701da940440f070150140d04110010000000400700a2040941c00380d80c00b58480700e140c5803191 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 95603597 1250 95602347 95602349
    0x1b080a0804060306150903060c09050a0e07020c0a030b0f04030c080c06011e0b09190e070201021903050f13031e020106030b0c130b07030201200a0905060406170a0204050307 76
    0x60300000020203205182d03150158502800d404d55501e00c1c0000316000081c405441c500c8040d060a82c1e0700003842e00544608045801410000c0c002c255a1703032221245071181400351441c0d000351041c1d1402d10002e040c901ea201d012039802c5040746425030f640245e041b03815207008204804101c00c007000000051218800380201840000081c542981058004601421013003010081ca241d9002c003040107407090f80458014030790607a07100b0110608224003e01011407a00304240340355080041062999055000d000075100032005401c42070f007131200c1502110703006e560b088006514500010f0441710608070701c8517514400d2429601c510244101603c690102580c0c03000140d465502c20000d108501503102d030403000f044415850101c00340300c1d0ac40507522900c00c0c0041c121000c10f003601418000c1d070015130b1850100255540080070048684426402041c400c0c0110b244020081501c1c00c291094030207070740d007507210040d6a9070349002074002e0311001000411925020000840d00f03803024041c40e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 95604847 1250 95603597 95603603
    0x170a170f04020307050103110f0904020d0e0604150203010303050405040e0a0c0b040e180a0311010b0901090f0c0201050702061f080a030306060f03090317090312090304150305060d1b080a 82
    0xc0d000342480d20401d400d02c942684081c0c1054108a400584103180c1002c0307617110442580c0a03650f038090345010130041d01500a4004090389030164501e402800465014492445900038007420a000f8002d04e04900081c003010b00028410300c0140540c2c105540b04078214800b240c04c817030724260303c0d985030000e0f1440c0390411241c544000c41c0c00c0201c240c4504050740c1281703060740790103c0020000b502665407545800054100000031b02c1e1382c04800429484207a0b002d2010307041c10344941c0c641490a001d0030030100149a081d161802c01c016241c4103114660150300543d0290039503403140b91201401701e00352034070042d12105402001a400c0e00c200590300ca0284a500c021071114a0068042c25400348074000100340360410100f00c0001c0d6001d00300d460b11414140c1c980265848894a4500d0f50151428810725409004140b00100c0c20000113401100e100d080c4a001003009030a00701c0990b401941c005401c00c200d51100c00005091100044204001c46141c600c690f517100c500750b290030104013081e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 95606097 1250 95604847 95604871
    0xf12010f0b0f01030513081b010606020a1419020f04020c0a0b04030e0a030b19110a110d1706060a11060c030f0f07051803100f0501090b0d170a17 64
    0x190741e25040100d11904802d1007400c007080700e0718013009160030120110304010700c050700c0000c02c81020300c140300110400030a20002000655200d0f5000b03580e5400c1050306039030f200da140001d14110000055144a001000070b828260b00d41b13190b0034020340e1a454618680d00c50b40a100c6050300b41d008200d88101c10303001d6144640030303080070304000d0040340c4800c004600460f0b6199041c008126036201e00342d0402403a50135540c10300000c0415000916407207040302021032000810441c0700758001d800521042d80c01007a030b006000c0000d400d0700c10030441002c450400d58524001078161070844044c01010300181440300c3e80300408080c0609210044030032044005000c020700070315a1100f864180e0000c2e000040340c0e45414540750180503800351001000785690500c441c04040d442c14444103040420511080c84000e501c03c01d000d000c2e00e0240603044d0110700c0c0614400281c6401c105d4040310503000000b201450404001d101c220f91701511038031050003480b594000c021843d021520f48100720204c25 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 95607347 1250 95606097 95606111
    0x415090e01050a030210180e090c0114040609050103021c1404060c03020f0315040e03131809020a030308090705131b030c02030301120f0c090e1c08060f12010f 70
    0x30145041041c0c22032030040240307030403d00c01a1200840c44050840d01d0400900300148000d0105000c125070f0000414041e405080c0071611200142004580c0003d880e00141d040c07810b800075090340524400c1c100014610f800c1009954000e81c010064050b841c10703c004502c603d41c5d40c401c04d5403c65260807017503418007010001030121600c01c00c4401c40240c0380661070105008811425400043c1418070100c1c0a04103110065441ea0302c40c05600a641040c0c030385501020701440940351071445400f0b01c1c44103407121404401914800d425401d41d00a01d41c400050840d2001c4074124030050007031841388185500450b007a03507500340740b0554104900010440e01854102d918405036031211101c189800c1c0350480b03281031b0300803040c0c07030640e21030302103840b12800281080c01b0302c0024007030007620719003541e04c012074801c1068000700d02910302902129001c0016042603c0100102d01c0074200207030080000c40d0a515148280c0942210300401c0c41c80c07800e00400469003114500780c1c132021020b0391050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 95608597 1250 95607347 95607359
    0xf04080d0f020102040501020a06020f070b01060519091805190f02070c330215090d0906090f031212140402010e01030b030303040b04020103020f0c01050118051614041509 75
    0x1000210010350b20003981410318060020703507240b500400050490380c0109038038100f02409003c1c0e840540d0006010b54480d44e40c1c41e0302500035804500c451107100d00f0703180807842160190590030102c482460101d210680e01a425000800001d8102030090002c440c0300019140c03d4004c214214039007020050380d48803585070509184035264040c11402c40c107144c004255590982c0c00c2c1480d1880b50441400c040c54411040303040110b4000c400700022406018401072650015055441540544a42013500e884000c10340d20041c0c0c501c24842d074500504001d00029100c070740321a280c060181040d0700804040d01e14130701552008102041945c030000200810b5607031081100341071010a0030100a1805103402103500e038480100094040c03c2d40c00045001c69201e80d044400a2600e040030503254200248218040c010a01c141b100d1100c100820401c0c82c02140f142900035400c40d4424000b50041c00300c247c5526500d030890041602c400e01002904250061303224400f040c9690758000c030b03281065 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 95609847 1250 95608597 95608607
    0x60213051e1305090d0f030f15050405060102030c0a03050705011107060203100e240d0204020c0601060921061503080406051218070515190305010509090c03070605090301020f04080d 80
    0x3010320b104031802c09080c0a0300c4000031610442242071442c1c6001d50b20a802d20580c003400349501d4008200745090340f5078081d211800545425118111000c0c4101d07110807004991f01c2c000e80d00115032035080380c0301c0c10000a004600901d01c6502c0780300082107812860300480c1e075a23000703202c083d1403454000040262010b07104038080007400082c0c18048541c20440700030005c400302c202e190f68205840d4103011807a03685040308a103400c0c3d030080041d961825080c002e546c46030b400b0311990011031510200850707a0386a0f010500e0001d01500c1e0004010020f0f0780f12040a03045041c04c5944041c82404080080b07401c900042004e000d0381d8484550302d480114613140503240041c8140144021800b02d05d5a1140200b90801180c90440b0b080718003025035454507055101ea48080440c21110844d000d01c83c0390550440c904840c400c50f8102d600d0364884000e5512001d40b00c0e080c0754140c00080c0b082c0602401100030b003403500800303800181060541e40b0315510a03800b81d0070444d82a80b03e0007001803915404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 95611097 1250 95609847 95609869
    0x20a0806190e010512011103040c0e010b030c0304020607020103020c10061a031306110d02282d1b050f0c0303041d0a020c01020d060e0603031303060213051e 69
    0x8089640074652500c11481c0b1040c0060140d50300c103000e00b1043e20790040c2d003500694980da603044811543d9041c41d14040d0803002d444d1056400e01030a031740001a64041c1c0206a034031420700c0d0342000b843d580c0e40303a082191070350258500324141075003840504981e0804109155417809140c10000d103c508140314071100e5980d6400d5800b0818007001005100074055508084095102d0000300f20103090000c02c0c0941c0c0500840e10980718800301e121601070002889003202c50052032962076141c03846800c101e86841e80380c08511504c80715580c06100308021941e107003181c0b01c0c180c0382175030551542e51010801c0c006401e0080d24558440316030f10402c107106001010111500310000d5240034a456407214103035525140d0031004461400014443c2c581e01e4040300c010b011420000c642d1000c000c03260b03000400141c0155903450100c040043d000d0305000041b185401c484041e407481c101e195685501c081d41c8000101c0d05079401036030000400ea26500840f50031102c20325203030308110544505102c0704001c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 95612347 1250 95611097 95611129
    0x10f0f0b03030a0c061a060703051c0e1b0109090e0307051e060a09080f0403081801050405061204110316090e0304061d0312040b0a030b060a2c04020a0806 68
    0xc02103140c1030ba070000000714045501117030204180070140d54101307101e5400815960040d20003d072440070154000000c1044d0340010440381103104508003414200c7c3c0015a180f02c0c41d5111082d000c00e01c0c01800e004290300309052402000322600e801054055400246030f0100c0c50b0310106914080080904c0085010120072800000c0f561156041c81e07a907503005030410b440f840d9901610b1341440341d0982141c030720b10300704e40c80d16994958038036002102c0d0380329009004a6014044040e00f056208a08484c211240106150700700840307108100078414001e4411902000f4110f52400b00361800d00038104641c40206482c0b0241e4a0130b4281c4040d01c0195046826540041100340016900f2031425911054151400070b00680441c000c280b07802c900320303010f043d00400401c001803422007002c010034111a240d9014050640c02400b0701001e0b001d6070304d002021940c0d491042d4480260390007541264808100e840301019180408541240e100c44811300001e81c81c04108881d5047c051180441403207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 95613597 1250 95612347 95612353
    0xa02070e06040b060712030908070b0720060c0a020102071707020928020c030d06080c0109060512070c0503070803010803070209150d0201080709030618020909030a050409110408010f0f0b03 83
    0x40c51a001620a11480d400203003c0146d500606100c2c41c4280d200c901800d500610b11666126507052170000c5500880380343e40020094003408401816081c00c05095007061401405641c0310402201000d0704101c0283c0304541d82170005001090350711012811070780d10b80704000d075aa58540148400002c0c010712002030440190130707a2105100c0c0003001a14507541900068a5a8523140d040703046100d150724204015003081c0c0702149640d00800c4140c8a00e10980300d100c04556210000c0d6040e014160181d0180004907001824090003030500c0c1100780c0c880c0c7c05403841c00a0a230740701381d0a60400e23006443e0030340c4041031400841c00d040d400356800c084803a000d00020b050443c0020904071141100a0411003a02c02249007a0300403024600555800001405007581008074101c0c014610001a813203074500c100401c145038404411510140d001c0e544d00340c034140c00c0603017210190001488044050310100b03c00103100c0c02c203100d06a40a01e4415011403128104007001c401c0e680b046047c50300c81c2d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 95614847 1250 95613597 95613611
    0x903140a120209010c020d050c0a060c03090510170103050309090615190504050a12060b0d030807180308030c211909050106030807150e01090209060904050c060a02070e0604 76
    0x240c00c600480c81c0414003910240c3d60b0201000100d558900340e180003508481e41d01c0004d001c0100108010115a00a40d4070030000c1d60340c0e1004581c429104000540466a40c4809000f5400c000e0040e103040c0134181803405450303105c980a9044190300364000c0d503142e00081030080291402c00d02003600580c1c1121100c0f01e440604500c110700d84600170851040e41d03514910141654080c03000e0798000c04c0c0040030000e0659481103c44c01440c03a10b801190102d20340024141a4036060312107143c100c1d015580c00445503181381088d1110301564120040340d6040e1140000010003801c0114492205500c1007501d482d241a211001c04505160001480f500141004000100410300540e44008440049105031007424594010481504013809121000480d4000c1c01001101102c140301e221100300102d50100074183d01b25521031100a601c0042040825150300d00b040f409600240220107655200d41000005503a503403001d05408003580200d4003c0080c420717000d040b1070388001c0c240c80034407542c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 95616097 1250 95614847 95614867
    0x1804210f050c0a0219060206101a030a11070321140c0a1101061518050108040201030903020c0a170d11060c1303060204060e0a08031e0a170109090314 66
    0x10400440d2510200040820303010082141003050b410203075005420b44210b0903100e111461000d116010b10000b501c10790b00800c5c2c900d4402c4c80c80c07400301e82c044c0c00c05814900d06014049025070019154001161301d445043d4514110b1a00600003d8401d8440310000721040000140c24000307107101103026851b142142c540752801d038410b00d0b40151082d10590781c5d4040e10b5025104600c501c2500301080d0301e4044042a0341c645040718040510207a250800464410320441240c00705074010640001e0b0010041401540240c101484092203070050b0390400c00154041032400d56030380e1001c1d444030190000100b02031020712083c099900e0780c0c0742a820324200344001ca669114040d003408900040060032071242240c002c42003010f503034844000c3d95500e50f100002440403814810350b61245040060000d5510350000884004151344206030200f5481c07012400e0300b540000d1071745401d122200c1171440d10442b030385406c54060004550000340c2c3c4003040c28000d00e1f003a9201008611108104640381203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 95617347 1250 95616097 95616107
    0x40c060302030f0a0b19080d09050a080a061119020a03030b100c0b13051203090d080103030e130e0304081c02060103020d08180904030c05120421080702180421 70
    0x840340904c03001050008005001c9500b042e0f464120104d0314410701404202d400300851158182481551032010030f54681c4100891680d4a10413504541d100700f10100018a880d08020301d00d001915009040a9540c3c00c8040340100c01107066005801c4960783d20200740c0c051084941078903041d16100080e010a01000d80001e2218030043d201e030442c40300144504600c010010783c0154800301b0360f00061445544807910b41c1040d160000b40c1d00607004040101407040d46000d040b29019501c030020441d14109004030340d001207030f1020340c2e079482d0709008480e10803c00c0208020030400d0014454801d810b02030030307025501c0e104003e0840d00064010005a518007050721007003504034a269030340740d00c00812a00d44141002c1ca8940285040d0104018503820280402105000e4030070743d050982d0b090703544106441140142e948030050005100e211410070716100c0203441c464107a0910b41140c3e03400103080700b09440b25100400360b02900704401c101800039151142c4100189000200c07980081c0602 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 95618597 1250 95617347 95617351
    0x906050f060c0f011418011413020a0302040614041a01200a050712050f06010602120d0e03030109060f0b07020d14011b0f030c0203040f1205030f030a05040c060302030f 74
    0x100c210710104080810000030310500402443c0c3c58005c00c5400d169030184a40e004c01107505000403400c20082c40b00c51380041c014401008450180105e09980c2c02c445407040c25020328050360420300c500d80100068555100c0d00c009000e00c4010307150070140c90305c10001511500402c042039181d00100c071607020798110360341308022106c0303051444003007000d072200311319013802ea14018001c0d2150880010b03010502020710319079280194142c4840000100005650700820b200b80c20060f80f0400302000d0255603c80a0721058644600c04584548410302c41d51541d0000c0c0c218040040e640c4d9000c001500300d180c41000206100880380b0b04050054000401c2d25541401c0a003488079864003401200d44290b0010180c030700d9480d0300440440e01c3c1d49006103456445140803011a280001a1550034000001daa00711841e0131700102c1c041d810880340601085130014100c0f41c40c40705200c00b4030f4072500d45010b1885030358180c00c0008c080c6881e040048204826902080c10326204105102030081180c04441d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 95619847 1250 95618597 95618599
    0x105010f240c0305160f02010806030a050c0f0102031c0501050f031b041802041409010b0d050307081e04140f0d0b160e0301090309080c06090a090b010e060403080a090906050f 77
    0x701d140c1c2ea50a041d00c2510031382c80500302c0220403051501c1082a42507031082c0280c003c2e40c4400050b540d0000703160340c45182c00c102921692180c1c0c03207a0303041d152079800c0781380403030041c1305880c2010080c4101c5040e00d014081941d40304ca0f02d480040c00241004c003880d42e11868100e00500b000303895110a441070401a1030094001d90b1a071000c1603c0b0b80c81074070500344070390303000d0010000c5001038910314980c03020648041c2e00325402c0c443c1d842e045207085080d0822040c4c000703000d146460819a690626680032100c038800083e0000030300e422904001000c3e000502401c0c0e0143c4141845008211880500d180c040784550320762081840030550386034209030f03c81881c1c0c002c00e14401c0845400e80306a100700380942c1d410743c2031518400070103070302c04054400c071010701c4100c03850040480c0c1000018081d03040d486400c000c0b0002c04010750f4001d82c001c012145010304000c04500c0717610021400c698425001540c00d40e0000600c08010340d03100030302c1001004ca880d020060340f400c2c40e00150402c24251045 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 95621097 1250 95619847 95619857
    0x8062410020a1e030503070e010207051c03030b031204140f0a0602030d0e072303070305070f18020307080f10080a030305090f0d0906050903030904090501061a0c151312020105010f24 80
    0x1701e048c80c0d008100380d0019020007850340034203a8031000449610350030130404400003800e14030300074070034100056824403609404d002a8101401c0201e121131a100344d6008a602400911070b040c400e4076a1400c8e4405814140e004d980c1d10780c05003100105aa01d41920084684d0168034100a4425401c0909105419a03100a4505001480060301c1c190305608050500e0040e041c0008400a5100e10340013282ca00c0c864200e61100401c131000102e000480320340000c0b40074540004c400440364022076911030707000848800995160700c2100d00e820070015048003c00e80d10014046100d0f001c0000c0c1c08684d0341000280030301440e0090042030500e0a204000034404045440480f0360340601c2928610b0b800940200003030081030900c103002c5c0100d4400c1001401c0d2081c02c003032880114904030750412090800400b0010390605d003850050701c0003010003000700540c005100005000f0b0f41c034442001016400490315504000e2840da021016a019010303940344114080b44e51450f90500340c4a1144034203007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 95622347 1250 95621097 95621117
    0x50d080601020109050f01020a02101107020111191208090c0f04021305040e03041d0103030503270102180906120a06020a02010e030c0102070303060605030108062410020a1e03050307 80
    0x42c0d0142ca101c0500030032901921031513044402d0154081c04d5001700301d500326071640920704983c804490001c525100005020001840554007400703541718410074003030849501c2c1c01d034600c001a2000c0d038000c0c01c41c3c0803104100c1616001303910400c40b5070050f86110290034109021400221401d40c0303102d00c18092900801c900031a900310340c054400410002c1c0050214840407034031a9101c0d03005004454011051784d0a1103d58042443d225051f6945a202ea40c0f460300c5102d0402281c5900c000c2c0303007060701c40f4110a490149001e0004c1d00d510a1104004003040c2c0e500c0040290590b80100b04c1401009a010b050803071100018951101541068005a42d0143c59008030301500600907140d1451000060b80c0298010540c01040024042e42e010060141c032030504441c1c41c0701c20300ca0500f1950190021a481103121040d0525545a010350a210b0610b040040b81090b0b284090400158112005100911454100000c28881c400403096001d008651700942180800307400e641c00c003c00050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 95623597 1250 95622347 95622349
    0x50402060d060b031b09090a09050106050d03030506032803180e01120302010f09080901030b0f30030705150709030602031501020d020f03090f04110301082107050d0806 74
    0x31100d071010664014000c0689581c844021640b081e180030351514201d104031480b02038440d00b034a0100c00e004046c0303007072a1900c05961010340b115040c1a02c4a540e941000036103a0f0710340385460b040707074802d88000c5024a060020107051007526180e099444002c031110b45a0080f5001e25801c20f194142001e0326800c1036016a0340c0000d2940d005078201044a40002c00c52031500541159680c2c420350082c00040746043c0c4200641d440040010001c12040c0101c4888d58080d403c0702800f41c102428406681d60864005508003060081e162044060045803012402c4468100706090004e84011032404500e691030703e45d074040c8882074500c1881040007003030440d40b00d84410b0009540184041d5200e00380412640d09542081101c0e90261151008905016001145180050041102441c20722441c42c00748031101c12103d01040c0d005580c1c00400000700c0b90300000e580a001d85000070040a0030403842110080c90a8801740c075000410b010500014400040220400166140c04201c07030311804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 95624847 1250 95623597 95623609
    0x61805090d18150804231c110d030605120102030c040308070201050c0607050a030e0606030706030203060103020705030c0715080907030206090f060313030e04062123061b0319050402 80
    0x43c1201060301500700030b6543c07080d40800045d02450080142c08400c0c0300c510f1410080615035201006117420240c0038006069010b903000301030035000d040c0491804011021541861680c402d15800309507078850034000c60030100c030074200c241d01000007113180d81411f049000c214011880000c041c03403070001c1c1c00021a4032a50a0390015070800084072900d0a109074064810303000040410006441c1018260080400044450044101802400c00356040031012000380d840180001d041c15000c214000014100300000d02c59210035501420300681000c08180950258001e4041041001400d22283e4400880c1c004202e82d4110765456036518260040380320309950000b0300364031980100410800001d114407003484503100741e03920b140c01004d8500f0881147c485000e03c8001c183c2c1c0107410501c14601c1c015021980d03000e9046405001d194804a1859031404100701920343c003c10244000d003c10a003039907840038040181c0328111b01d0000c40030326011180710242000c1d035031140045015500c502c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 95626097 1250 95624847 95624849
    0x16051e12030105131103040602090310020301060e010815031e060f0103020105041202130e01090204050702190204090c03020303130f0b18010f0c0204060b12060a050120030f0409061805090d18 84
    0x55178094592810b07052400081d0818100540039020f841c03c40844421244222410b0b60150340300c0c0401e4843d500011183d0950050110790324902d5691081003a6401304034000445003071451698042040700e031500d0074103c0240440c84550030003801400142e0b001030540b0195000103840c0107a90845000246605141e2003012004a1178464000083c09064010040050088ea0306000b5a00e440f0012a59a84125200141d10700610581e400604c0d04e81c00c8203a25600072209904580d0f16600002c0c15941711400c00b540c001c1c0c001c001000021001c1050134010300c0c0881556040000030382d9840c50103036004004504100150329820843d0703028120b03400499401410420205403580c8082c0741e1540070f0751010740a030150700700140300c9190a5001e401070300c2041c0d44060361518045001c055511000c04c0500d1140818460007100d21a86006071000f40740f0344002003040f910b01922408008640c400c0d01c814141044104542d514001449201903481490010442c040d0003a02d85030010403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 95627347 1250 95626097 95626121
    0x306010518040c0509242202070201050c150f01080d05030103030f020f07080d0e040905030904020a051903062612160b04050102090a12030206011a16051e1203010513 73
    0x80c603000d0210b2508213a6544965040c6c1c810282080c607030ba502000341e03100e520004500208088002c20311140d14503009442010710604001d404d01c01d0700800c0504282c80c6450141d0030720380c010100031340c000c11241454010601c0c940079084004041c40300520902c0305001c007506202042c800403918038400c0100000c04c0c864001070301d40b6951030b2004261604005141c15000603000100b115080c40c207403181c16600740c0c1c080b00a526111120080c0006074000c0c000c01800d01c84140802c1f0400c076540c4500d410800402d940028466091490340d0700400031800c022442d10b0107100b01d030020107030001180c54090b20084e07011a11003072140460008101c1016000f40355a015100307010401c03005402402007690704640c94206103441e0100410310440d0110050b0050740000010000040551045c250041600c0e880301d2800081011140712006c0500080354242e200000c0010403483c480080c1403049882e01c0904007500e003200c3c1e00c0000d40418000c6e14890001581c034a02c02ea08a0350100c0c4034120307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 95628597 1250 95627347 95627359
    0x405060f06070b0103110a0503072c0a09031403070c0303050411040e06060307091413021503190b01030e0a0b0901060f06090617130b1009110c0c0306010518040c05 72
    0x141600d0950040c83d002e200455507409241260a00c0c3d25120f62928251040900189802880c0c28140b9640d103080700740f80c2c900e0800c20b0800700340d80c0941800b000d1045003044800700b0010a07900e0002c0118013200501c007241c0c401031042c010510b90000316540707010f40500d404542c07915182045141d402d0098950341d4000d03d0052081072603240862402d01c103160440555000c55a2824004113a4005964102110300c5120006010303030020380b24240380301d0002d00f100d81e10307802450b4000c4c0d40c0d030b100380c803007225103107006005601c0302c489802413100c6010286400c0c03040444151307400d61b65516445009041c0603204c1e0004400400940c040c00080c00b90a20301e03a0603d60f1400050b01c0200310740580030020704e500b031400440d00c4000340c0540c00368030225058103041c8000e803121400c41c44e0151007100b0b0040c000c1000519000c01c1c0c047d01020402c0320385d94594802e00000c01702e18100741702c08218040c0e0003000041003c2e40d20080614082ca000c0c1c0c4070201c0c0c039551468203c0e00d18030240c0140758445 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 95629847 1250 95628597 95628607
    0xe010c02010c2601060f030b0402070f02040c0c11040905010209030604030806090a050906011809170a0318020607060b06040f1214062e0302091801050601050304050c0405060f06 78
    0x280e0540020748112a562035485103428001191220f0000c00348000c03680c02c803c0b8004100d80b51007544513124011061400285211008002038141e0380028015510707400c001d46c100c0c0544c5428895254011418104030102801d95641c42c0c031300d880300c844001c0c4119620081071050020a4044818000008098072060328003480c0c0984200b400741d900b9030064540600141200c0307100d20400340a0810340380103140717903860905003441d802004c945810310552502e0b41c0100040c485070040c00d02c924541032003500c1d10340c40c81c001401c81e5050490341c124080d0000b200009a100d000440c1c82d200d0b0094000306038400f407100413920a21669012082862200900050b0301d4490440c040d007603881100d10b201c1034003003007840582c0c4280913504603d929242084c0d02c40d03204045041702d51903ca4031880102091703626000078652140440310154002d9035400400f40d400030a200e4586d100e2400d0a1040c15410305840d081c0c0c0e01c801580e1458022940e0358041101d0755581181c078280e03a9001011640d0361 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 95631097 1250 95629847 95629871
    0x3c020313091518050f0105060c1c1106100504051302090f1308030c030405100501140d060e07080303150604151b0b04030c060c0807050a031512030c0b150f090603010e01 74
    0xd200c05c46840a11035005800400c01c3d00d072050032946c07940381410007040900f003011036851030440220059402d004904681190701c080a002d15446090500c29640d5043e20344001e105c03e4801c020a100c0f00312814199840040c1c1c0c3d0b68002c0c44e0002102005402c0030340c0d61051500101e90078030350151284a01104001140940400541c0700e02d1040d01501c61282d0328031302110039a5800c2c00f0342010801d64000104040c1043c0c0f500c040d2031401407101140e000002406181480d48541000250340c1000041000140300c02540d4900b4007000e4076081d25052a10444411900c1104840300402041e1003c4d1030101d0862144803062941201001c0600d061924025258881d4194100e414606000c50540f80d07a003d14502807080c0324945801c1d14009007500100c00400841c903560507510040507000c41d56110520743ca0820503c80d40300d200c001026820b100e120918000c100102900741e882603035103641c50340d54800e0150201030700d00c515641c079940d00082c00741c208020000e1041d817070704107004d1207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 95632347 1250 95631097 95631101
    0x108031c151e0b070b040305030601030f0513110907020606100309150903030f0b010807180e0903041d0c040b070303090615150905030d0509013c020313091518 70
    0x58041002900440b0941e03440050900307001d5034101a15803010303500001c000c64003900003541d2140f0145070001d250441c01c5080401c0350b5080d0340e03154441180100c4070301004150030440c1c01e50b6008070f6040300c09117460302d0004d594220040907107009645192245060500036000340901541c0400001100c0e2008404100103200c03030001940080d09000d5420b010482921614001070010b03034a10429030349046040d241c8000740d11184614a9001c100001c2824800000f070b801501d0180103555510700d024100e1580c64039801074601c4a1050300c1c180600341da01c031802c440403515005030841c0c664038103007019801051307526000780c401420300c914500d4122080300d02d0030641d01e5110b990600481c032a00101c031120396034060150181e201000350b214190180000c1c0086110514201c190505102582a50803084c042451209544801c50f80708a0041e0300603c0003100c0d80f8030040d414000d0104000c10341c45010701c10401403d035142d007022005c100c1d07050710f0009480c101050100805100700a400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 95633597 1250 95632347 95632379
    0x18120403060203061e13051021021207080601030f03050403120c02130605060306091f090e0706030c08041520070b060406030f06020a09050d030c020f06030108031c15 73
    0x110500341d280c05d0b4007000c008481090b40b80700c4082e0010449000500c0d4aa0007880c014007405a220f0340c003807001030071009039403600c2d2040811045500c0401030510511081e0710f0b850003480074030781120209001e11500000d8060440b0b4010007540001001410155442d201d240c00150640760500192404103800c242d50002251094031043c06145180503140110b0300c035409519801107080020509070b02d001c1c81c2e403541080711030380f4840119076065003a041c800300c542e11050300385447c3c40a0800303c03141489444002c01080c01c0600c805801d011005000d01303c01407008095110f40400b246048100d507001c841d1004a136040207002c4a00d01d010313010103402042d400c0301e020456800282c1d940c103003402450103d9034002980c1c440717031000743e4980740650022500c2d502000b00d0941c0000f0b030396075842c007040402c80c02600da02a10b10030314018095000d4000c1c90860081c2c20400041007007240000c1101d208080b907031040c00040710740102900140460240c0c10111404900e400300e400125a02044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 95634847 1250 95633597 95633599
    0x10207050103020a0e01050d020408061f1509030201030504051510031b05010801061d0301050a02091906050f07111203120108010603030c02010503040f14030409180b1812040306020306 81
    0x2542080d540d4004505038425913203040005021030702c0b50811035000d400504410144804003504007912121018074100d070444040c14481c1c141c0c1041d000d8030b0351185c0c1c840042c003040791004000c1012850040c1c14452107200c020304050392070b000a002d0241c2489659800528940082c4240c20071800c00f9144003c6404180d403072051307280d100c840e5981240b100c0300c1110010784070201705030f1800e90103869a803d0758268143d0884880007410b4a0b0b6020321031548110409503005844800c030805114112002c040c0e07161120b040c05a0601109812000741c4100d4000a001c03c0e54900191414840d0840900c81480d00f00342d015900c044c003150702001406003001043d00d11002d40e0303603480310306081c0c0704a448003801040c4070302e00d0800994412030056034424081e0b00c0c1c8038042440e580d5071032180103d0300482d2140c0e40010800340100181401411604070440c0440311501c0d415494200041c100038000c41240d401980126803d024140040d04030800d0200d4035948681c0d0b2070428101a62003200c101d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 95636097 1250 95634847 95634853
    0x602090a0801021917060909070e070906030b04090302060a0e030f190806030a080702040f020408030a17070f090e0a060e0c04080c06071a07110a0c0306061403030a39020102 76
    0x7860309144102d405024042401800c214507846d220140700020401610355000d50217183c401003107510031030f01030724003d120039034038001c03054584180181140c2c41101c6075407141d8104154040400d03400140700b50041c0002d4000241468080071003440d40c4144070500c10101404250101d088a1505c40300302c0941c2c190300d400d03025030b444000301515480b10b41c9001348a80005c0c02608050f06080d801550001c040711001460140c48141452954108816410002d84405800c900c000c02e0142010740141d81c50810030300b40c10b000400540031002502820105100400020740300741040d411a178010041180c50b000c090074180ba120000354806c0c018500b040c401c0c0c003050710381030800700b040340c210580042101c61105000f03107900801510142c5250100081c0c03000383c0303821840038400d242c040c0d0320901c0d032031149500c2c0d4a80801a00c84648c030903038110700142440c0d1800c2c0c81c080101e48040021b0b2602803591401c5040034840c000041d0510100c6010b808058922130200c1400103070624000d80031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 95637347 1250 95636097 95636137
    0x15051f0801091709030a030503060d0614190c0c08090303040306022a060f2d071d091302060a020102070c0927020a15020c04020c15090d020604020d0602090a080102 72
    0xf24244a1140500c0f95030140e2010010001003441040074603044140248400c1c28613502d0703100c0c2010340d00c40c01c030034081107000384041c0004400460390525504104a1090042c10980540501900c1d00c070344014208207400a0001065a814401c41d00174651100c0e045444400700c00800348607250500142074001d4210300ca41444800001c0c10328403848c070000c00c2822940e00d003030008c2c0c5071914410003960303240791030001c0c0080d034660301c5e43c528401c1100d0396801e842869403011180702c15880b0a10345005000071002e10001000c40840450016015108613665825400c0221700a10641d00082d050f031858120100700610a50400390304e8100079900c594070100d2908101d842d007504004000d40c40084440200484450000130303040c0e034500c0740103035080d1400b09008501a40e004d000c540704c413600461043e03502190402911508461340d1300040c224000300500203540c50310f0140c0040d1103274207210090b80c10081d85404071750340520054000c0034119510500c2c2400b03508107040e002c8003540c007203030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 95638597 1250 95637347 95637383
    0x140c0a08030c071802120411100e061e0d0c0e040c0503060a03060c09120605010305070806070212030a090f050a050c0609090406090516030302060402090604060315051f080109 77
    0x41d140c03a4000b04015044462034503140b030103820740d0318203d010901e03002e200325440b83c020310301344501c00c40c0a070003001c074031840500401001220300b88a4405114004c4c01002e1245c85190940d520418044198581034581c031001d07025900992001c407007002e0030038520b1500d40c1d50008940b500c2100540b01403007204107080d030a442a00080b42c52075005a0391b1101000420840d4206003e04082400c00105458031001113103411242000151041a250401001007003400c0001600801907c0b01520b01ca0400c1e030030080d21601c0130b0308040082000031005c503a48400d10342c404605070754840700c4007100401c1441c102c2d8860300050340030b69072801403c103071004a080201c100d8032150350041507100b00c0c0e40c460383d90344020030010505a80c40d2194886e0111704041448180d0081c42c002e07001051240fa01e8810029507800060a4602503400d0400400018012004058405018440c0460b0680d40c40c0f8140d501d5580400e61901100300303910b0000f41c005411350005c0d4035036020310b02d80c00001944003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 95639847 1250 95638597 95638603
    0x302010f110702040b0118060503010f0501090503030d0203101706100e1302011d04020f0301030605013002031f0606020c030307030503040f060204080a0305030618101203030603140c0a08 82
    0x30700c00d01e5012108100c440c0052510364841c2d200302d00c050420100001c880d10000410150310307041840032404c004014814440c604500c00700400c0e0901e080c2d1895820100482d8582c040c200911494503004408200110308608003a405450304001c3c0c3d04060011840341641c5c1c00003640e440c00b101c1681000400d50760000f01d0294800d42e040b25003003490201079401110001d0090140b0384000d80450460911580c8500040c02d40b00459070030300342c0742d5045080500445806034422a00c01e6902044001609240561450071000524608a2580150010070f0800600d080a80c242075200e00c11105280b0b2035a2051040c0c0e000d46d401c4603034244440080c0755491162400280c080b800500004001800d2080010307002482076a002d410940e482c2c612030302d012416182107003c03c00c003204005040c200b5404600e08020348400c20314440c00c0480b03044070865114004e000a01490030015011701d402504000011540090074110311809074402684030301c00612072501c00c01a2020010b0160000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 95641097 1250 95639847 95639861
    0x31801050f0c0a0509042307091a03130b10140a03080712020f100501210b070302030601030e0601030c1a120c0304060605031c11010c09050d060e190302010f 69
    0x2004074503151049008600e07082140000b0800c18100700302e500300e49031401030302c0f944451304244040c0f11001000c0c000385810700800080401070481c01c1044498000c1d14005a00d240e540007840d56a280e002d0451840300280f1070182641c0c00c28001c0c4004045034580d45d2040b2140c030b40165151058000420844115911000d040c14006101c51804079401c0380302d4421031400303801280c40c66070750f01b0501030070030741d20310440e00e0300a43d1000104010413055808a600000340c0358a10181b255603074480040320800383c804001c240e8080001420b9074007a5000707148019a2000300c3e2520f61b542e2030514602e1030107009102c0c1c2d281c003802c10b4612801058090340e4080d1600ca41e100d81a80c3c0315150408103070802031003036a026440314400641900d00340590880103090180c501c20144d0742700005040755490541580e0030380e2500f00c203030200c0c2d80e110031500700f964801c070307501c21031200181480f40251800d5040725010b406036050540716034140303040a268991094000307010810030055014112011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 95642347 1250 95641097 95641111
    0x518010302030106081b190f06030903030b0f0d060b040b0d050105060f030607120b06070602070303152103030f02090a2607140105031305070803040303090506040b070305030a021e03180105 83
    0x159a50b42c0840c074111461150000440d111410084d42d1412300e000319100c16444000840d60b5034a00c1c0701855803500a0703804002c1d040d1130790b4031058107050101e0010745444c038025083d0b030343e04c81c0038204c1c0d80d46607005014050f00060500d021441241002402000c05442c01480341200304404180360401103101840703140c146c1c275208500303481e00d0300280c05400007051181d40070404001e6000002c030039202420b0018040e83c0c0000c2c201c07045110a2180000070b070840740c401440300c111040c10410100c40d17050429498074000c210000d8003583c00020780250813000d5070100d00c000c17006c80c03008014500c41c042d0305003441034000181030b4540510b80356415405848149020503001c4e0f03c940d400380c0700641c2c0040000c0400c4000f40c406890b240d0400c030080e0420301d045e800003d000c10501d035000000c01c001d0501114458a031034542030089203d4840e10400600344000030001940221580d41620700030302c6072818124000461141810135035200b29080243c00f41046040303400b10714144112441011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 95643597 1250 95642347 95642383
    0x7050603010e04050a05030d1b0207030507270903030509100504020a090e0c0a170f01020408061308120903090a08010e0d031a0316080f03160f0309051801030203010608 74
    0x400c02d14080b80c0c00e88000d00580c1c80e4402c003400c5400164003000142100c1c0e401c14000180b082c844070244000c1c1c68014104401c40d44800d1007880842e0000c070b022030032200c000ca41c0d80d900110441d4004e440c00460a600010149421044414075130150003445c0f050400200b500c600021418080e8101c3d642a40c010b501f050703803d07034140038040c030755403140c11480602d5080301e081312085800291039082e0794000c0002403482c3c1e007690090700401c1141c100d003203090308025030a242c1020341e4550b84080c001c2c02038051600c40031400042c403140c1740c12a844a0106c1031400600d00d801214076035a90f0056102c2030040c580518002940d80043c446c4c108080c40400241c1080402d540046001c1d081c08424406049080c4100c08400c1d40c1c20040d800d01c03903414502c0108100e2422140c542010100c040821079500300704410f110507040c0c03559400e01c65038403241e030000c00b4141b07080c12180386c080c5030403054229403d14042010000c1407003655048901c210020300150340c85851403a125a662100790304099 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 95644847 1250 95643597 95643599
    0x30d050708030a0906020c0a0204060504021c05060d05060106210b0303070213020f0a02250501091502030706021210350c0d0b0405010b0405040b01031b0803030106120e0705060301 79
    0x1450340402190400f1030b5030004100b0041130303240c02003280d006164814041d4440c0302a1401c60600e03014200043c42e04072000c5003014081000c40307802d50060003030021b03469511f600065041d03442c01c003044621900841221907940e150f85c8060002c2130208901805189400c440740080e00c2035010314080903030701801960030b040c8030384c0c20301054990441021940c01d800b0300080b0f40601b200070140c5091503050b40140b54201060034015200118440e2110320210500400e000690700004030350304860b4070000500d00f848010742c4c128254016101e00803d0385000103503031220110706c810114090781d01400d45100885d070f0f40300e1454408015003e150302b0590f2441d0b00c4000c1c10b40120040c0e58030541c8a0681d019a411040064440e000c1d104084880d0400c0c0c0741448107100c42441a4000c0e240c00342c1d01080f41c0d041680f10f041c10340005100041000c3c1d55030008030039994520340c04000410f00901125101c1d612410060200c051003411841038520f415002913640f480010200221030000d8805895a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 95646097 1250 95644847 95644853
    0x3081312031a0312070b01050d020f1201090501020310080c0a080715020f0f061b0307020c04020f09030618160f050d0203120307050403020901060c05060a0c0318060e010506030d0507 80
    0x2400307212410541110044640e02c40548060081141010000680658540c40c03450f120058880603004240914104554000180c440d07208065440404a400c0c0190f100656201d0f8090701e00024020f04650002c0140914240780244e0241a180c0081c01d903000b03803808406001d9002020b115814440c0d00c1031204004010600c00a0079160b10184144c4100c6125180560320380a01e01d920710602e540494100005140549000803d1a05030805540303181441c00c0025600c00c4c80f60031040c03080d90300081d202d14150003101191282000501941c600d07280a000340d01160707141c035182c030880e030090010b0100405207014180e000c0e642e040d11f0036080c06050100b031020704949218101d807d07110355042900c04040d041d01842c8120499035460395a94250310620110a078180d0142041c402140801000100c0216180e1307400894180005181c0010100482c060440101140303120a005407098051101c0c07900a0318030804144020302440d220901450303520305060351041c00248007030040d2400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 95647347 1250 95646097 95646101
    0x7050706110a0206071208160903030f0c020405090a031209030c12031118010e010f080a090c0909030c020307080d05031f0e09030a03050a0c2321040308131203 70
    0x1801e074000c045803651011907021039807540c48094241d450440100301d91440c183d0003200355500c0411381900c030580c0e1010030005000303046030b0f0200a041c05500f1030144203d80c8100c4000360700a400070004d019030701b85080f0740c580355110f1440941c0011740b400d440d41c22081960165032690b035810766071100c0000640d11000d081580c640443d004064032006072820441d604005000c41c81307034501d031842100283ca40003400310092030001506004091101d1080f003900700111035400100c0200c00301d01c0c10190b08d000030401c049070300849103407894807200c034041c140e200045020a85c03003074003200c41d010b44032120030b0b5072505074424200004078100001b0700e20001000b100d841001e003c4044854050700e40c00406d618880403501c036000e981c008075441d0521503050042d160003041c010020407104621030001441740c3c0c02c2111f01c01c44a046100c6000d00b00d002c441c112103a0180140500f440503074041e003000354150050314140c00180e5039401064800c1c6100000450559005c0c0380c00c84140920001940 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 95648597 1250 95647347 95647367
    0xc0915080c0f0a0206090c0a060905010f0c02030d05040311060c030703050c0304080106030305030915061c0c0306050a06030b010605190e030a0f1b0807030c090e030d140f0c07050706 80
    0x110100902080001c204882c01a00315003460b6006071000c2c4c502805518586200e10010b07070722446400ca000c101440d080b031040300075680d00303203003240c40710019141c2034484e0602ea020081d01343c0301c0c5000502007180d005000d4810749100c3d0f010703c111500d030b840c02c210355402035801006c0703150000c01440f030000380110000e001c0c1c08640026a410296540d25a03421600543d0042c0c002c40c00c00410401001c0e070511010703000080d81103d903009030030100c01040800040c2c0700e13003807141141058801c0a0184e038140b1580190760000040c08a494440b03040d2026205520003141c00c43c0701d030800803c07120300402c02c0d947c48135520128454400211401200c07904034542c80709405000c1d00881002255412415944d824000c40d0700b51030380c0c800300962404d00f90070b40d0b04c45584c503000710000380f0004240e00807030f100f1564003200200c0d410907000c0341a42588101d0319803081c00c0780741107152814101100e032031078400c2d00b40180d010a10390390820f010303003544038518000f041c0e500107600600c041d9009901d1b42c0c2c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 95649847 1250 95648597 95648611
    0x522180e03040902070f05010501260a03090608062b172b0603020603090c0f03071208030c2b2904050a02190e040c0f020a1104020d1802040c091508 65
    0x21b40010761f02c0e4103003110b5003a0450342102040e00d01580e0b1245d00386c1440813048540b200202855034007070324021300c03002650140340d0410042d20003240c440da50303c1c045500320a000c41448412107100b22100181001004c40440e940c603035420015001840602c241e43e00c0c0c1d081e0007000a0018504080c002689a85241c01c2000741d075561404005626030201841c858000c0000424034044590b00708041065819011072007035000003024060700c2e206404401d526a80081480e0b2241c442c0202e070b0707090b8065648130340f07142d00c0c81c0081c80d42c0306a0510a10340ca0744c00c80a41c200640302242c00c1d1081130007500160500003041c0300717002c50b44504007030b0302580d4008220320005050800071070034014440c0301a8141c800269a0708801800351400c0e00c5000c0c4064000c0c107145075000d60100019490703190031400540000f0321410312040c80e40b00c0f501208c0039194002010808900341d0112441306d122100f000382d00071881e0030a00401e07280540c1080050728024030075601d503202001d0302102c1d400320017400c1d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 95651097 1250 95649847 95649863
    0x2070b07020303042c0f100618090912031b0918060302060301090f050a060302010212070f0b0a060602010b030706120e01060e16020d02030a0e100522180e0304090207 73
    0x40d00f1504001d90810700b045c40030900096044869403d44412000d84101480001401030000809000054170101e60450170404d0032003010352501d90800d6902d80c07081c911103042072002000c00600301243c0090702016101000110041030040b00754a80004683d40070400e02502402041a80704503090340c50440440072508513141e81c042082d075003080c0d0080d0502501d071001211030680c07500500ea40420340800421445107580c00007541d48000a4512200032400917624052203030355542c0d01039140c0c01c00b12a1155090241d2100024882e511078000154a4003600d850540b602054a100b03c400b0340e940c0c6555941201d8848006115040d5500c2c2503660300c92002503410b40c4110705c50b00c41c5100981c40040d100710541c002e403d283d540c0050700115002005010880b5402040714928604d0580394040310b985906400e03a034070720540c008416000000d0b01c1501c18481051000070680c1d1000c0c040c01400340ca440c1c004400e5620745c04201c440d54000344404e020740b042584c060001c10740140c0d02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 95652347 1250 95651097 95651099
    0x8070602190203031005010e030606010e12010c0e01030e011506050d0e1605010807090e0c0304020d05011503050c0604060801030605100302210d1b020108061201060603061502010c02070b0702030304 87
    0xd00c0d4029407075240010301603000801008000d182149070880140800e0a000044080a40029841c0c0070028800c1d03060041c680519842903d43e8480345e0b4211079194020022510b04150103010b00e8403010032140000d0401e170309040380020600130b10b0740311005a03c51500160038200150f805400401102c120503035624104648000d040050048485111088120003810180010407102008000e01c041c040da610003001a0350804a040d6071101900f160345490351031324030008642200c00f03800a0704a60a0001c20603005203812022030840344910200d404554600c0c00303200560280d40f00c1c45003c00c20403401040451041e4020941c0901c1e50100c0a000585981c00980c1c00c240b681011b10702030038a010b02c0f01d080c40c0100507045110110b07040c0034031102c441553302c09600021480090400501401080864072824107400e1000c0070351000740300103070316000010f00816441c8502a410b10003c1e45070307080c0c01d0040c42918100901a805810540d04100e111280c0d6440040226010312007008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 95653597 1250 95652347 95652367
    0x7030504051908040e0a05060d080a050403080a030e0f0601080c0103050a240e010503062401230901090e0c16050304030f03090512011a1c0501020301090603031202041208070602 78
    0x401c0002c240c03081848036101d03400c1110700004200b0081c560300b5400c0ca05802d00c02d40791369001e00401d22940c094080b6a842d18007030000c40d1140900d520040050102051345085541c0640201c0d0304940348008961040149040e40f0b0340d140f2003032180441c250001d080c104100d511030b4000f10351003424003501103248440c60091070421040403800c0400344414000038031009824080351401800b0031402040070b400c1070110742d80d040405103801201d4800c60a220290769009420710202803080240ca0089407018402541150b07200850017800915043e0000c20241e02014815000d40c2c0d02d241c0090415014000c58550340310280c2040c0c0742c51105110010020b4901c00315404401d101c1c1c1d0b604038a60b85000e0170300646001c0006000b00c40e03410000d4030b8071405000b861095072842c081b249020002e4024910a04134081d0a00c041c21550001001042d001490380041e000c4030301c41c0c0c1e00d032880c4045100c405012800f882c020b03069002c05031001440410125405000001d0080c40300528041c4440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 95654847 1250 95653597 95653633
    0xb01120b04020f030c12090f03090d14010f020c01061d0a0b0a0812090a1401020607120b0a080d090f030c180e0607020f0c1203031b04080307030210050a0902090703050405 75
    0x840c842c00400c07000070160006c01103008141d82102c05c0e01e00408190600c000065103d000725a003480c000c415203400301c0c0501c290038186a014200c484001c1005403690503141c1c01940c05010300c1c03902d540c00c2c00000141a030012100c404001c3d100704170500e882c3c88000e14040034142c41ca505581c0304500d1000030504902c1440481c4a4126110100d41c1c1c401c002d0040c0090188d1941c040307400030b02e050f0320440302640c01190481d400801d910384038604401c0020204020441c40d0103290304281c00540c046117202e00081c003c5180d5040d510788154140d036130000d40002c52041d01000b07101840c000790030041078014034070100751040012004150603d40c148a986408400c035605001a4091000510100c40908c2005e013001c2c41901c04d0800c02000d0400316647e4030014010840d87c04448814001c0c98214100313880c003a01e410741c00d0703e603181428207000350380d45501c0040784010f5180002040e201d030090b1140b40f00300395001d0030520295a40c2c1900b13900501000304141d0340f9008800071105504199 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 95656097 1250 95654847 95654851
    0x711061302190b04140402090f010810080d020102130b030105030a120203070b1f080c0612041103030c06010828060b01090e01090c0201050c04210503130b03040203100b01120b04020f03 81
    0x100d41d60f107845500c2c0c18000c045020200007818020340c4100041840c54a41034050b0028030b41c00e00300751a042c1c840e222200d0542c0303602d41c07210f20345014103101d652005906400405100300111100920a52a600aa94039120a01c60154181d2105074020001010a8030b5102008110300543c3e05209483e21203da942d50111030304a1401d41052080e107a180020700f01501a01c40c903401440c0d13802002c8046100703445031030448051040341c44006405c1007404a9042020a8040c1c1500d44500095000070755801081c012500c0d9401110303160003825403064240c4401030001ca4540c0400c0c1907030744941005100b1b00d08040e042041440e40031230140e45aa0049008200203900000c0c0b4241400c402800c50b000a48655050078040004110b200d20715160201c3d210f48032003c1c0103c1582e5450114590704c1000c20004a401c62000c00056010300722000e54440c43c000d4051f0780d940800507101c076007224440d07a10325011541e280d88003c0d42e50302c164008140c043c0d0240006240c21a1021a0150303a001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 95657347 1250 95656097 95656109
    0x6010303090806070201060506090d0807020411030f180307080d020706060e0901110309030a08070507060906050f0a02030915060a0e16031b02060a0c0912050601030b071106130219 79
    0x7541410406800304200c0703554000c600e0305c02008004e042a00060841c8141d0030918032031082014280d060100710012038000c664010401c2040c0310784214260803941044507112510310b6071500158009016142403007814220300c000e0b51421180c1e54810400d42c109107001001d1640c28081c020000c0c07000e2181e0001342020358a804118501003041c01d00f550404003100c0a03442040c0248400c1d00e000209950000d203090801c10080d07515010111201d004446018100c41e00b0712242c441480941ea1101d4001c20719201e80b0180c0307a8400704960243c1c84240d40c5000d05a00c42c0d06551002c81c41030410503000325004113041c0c082540c50030751900034242914440720b0100c1260344940c086801d485401481500ba06024503c208100006511240020108051a6125130404043c684100007000c0070700b207441013451300b0540c03c1c1031443d90341500740402c072108407108003c90b9599009215030403c4001d0304000b010203550f05540c1c2480b05500340c0080780c01c071550264480c55480c0090480000e001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 95658597 1250 95657347 95657357
    0x170106030605070507080906300f13030f0e0307080a030305060405060414010902090406170f0f06060d14280501060603050408040311120105090c040f050907061d0306010303 76
    0xc00d508088040790b9000c0e143c401804403c111900c0040c01c2007058030040c4804a4081c0d07129112506007980e04201c0c7d030400ca5149601d40c8010007250000103505028502090701411281c2d5031004a4018080d23964020b408292007203001640113104d485a00110754000c0d003030300d01c41560f82a00c40e10700714694004402090300c403810080302d400c0c5031180646c0440c0444003404420080c000324501841c0600500c1c40b4071f500064080030603211500f100005200000c0b001820178541c216080d03c484503000c00030124020a20300d201c016500185c8a4040c410042c00c0121a40c0e1a0b51101351601c002c5603224960b0154142000300301c10b41c00900d88184085600260b2181039601d040760840d00c0a070402c805152600c01400040b407041c800b0343d825250704c18491083c25440000040120700d50000150040d803d000c100914840d02080300103580300180e9040c0254600c5007000c41c151602100e00310f06541c0715076010000607226a220840640301c021514804400c3c0780086030500703500740c006402243c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 95659847 1250 95658597 95658599
    0x506090c0411032503020708070305070605060109080705060a020c0d0c06081f050f0102010b2d04140a18060c0e01080a0c02071401050d0504291501030203040c170106 73
    0x20800e806036540c2052042080d5143d440c101e4094920000000c074424182110031090014050282d8102c4280a0308540c81075280c0c41c0c64580140b0a03400180d04a40c03480c08e1801041d07140d40904000025902480040c1c00707075034186004d024540e001482c4007000c500c0344030100d5525071102060204118050040aa60603041142c01340c452070000d009a04800c00ca000510b00c500081d0ba091801c0d10400c0f07401c3c01d0210f48a90041340500030011a0550080160305072115400e2103001d03101d10700700c09108030003d40780301604000444020b0303001c080c0e03042500e078001614900c159000344000c4071482c400b0790a26546031151801c8030768507440304020491000e6080e01d80d40e000700e41541d10041c10031052000800041c4000c4d11810b040c891455129422618828180e00a80076110030080c0d46d40204514900380c14800310190f040302a17001030303000d02d00e04001c80744220300d000c41c07251420f1034a07000c905580c00d004400039800248151041e1402c85404500c90a80d800f04c05000c0440741c001207030007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 95661097 1250 95659847 95659849
    0xd150b0706060503060c03070318210f0309050c0d020d0506010e1e090d0f3b01020606030a0f050102090409050102071202070f0b07050c040203010f090608010c080a020d090506090c 79
    0x8600c2c5420140c441e900107005c0100e40040502101d5211000340b4011954050742d02d0f405041d07aa8840c030003021810003c7c1c1e50391804c200302486030309a1085030380381c03008680040801d0b81100c0007054042d105400182010405041c94101c51008902c050310f03070300341604140c99080c2000f00a0700003140b1040b183c8e09101c0c074981700c01d00c4001c902c00c1540c0400e9550a0003030b030681c0e0351041504e000b018400f485a00b2407220b0300030003010416800c1c4480f01210508140904840d80d0f205118001458241e1103829486520000390980314100140c010480740720135480d02800d80588034000c0740d29640810207126079484500606206074401c0d000942c845010740340c81900c8014451601d011548a42e400300243e41c90300140d0400c4941b410a01903a9445a06045041800e501070707503a000b6000000000704654036020380700071103503110010081d0b551a401c886003a41c41d150340035000100d41c032001c01c10b0a40d0302e030b0050083c3c14854200080e60748481e40c4203420311a0407a0780588a400200c2c142101d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 95662347 1250 95661097 95661101
    0x403110609040e1f02040f06081314160815071103040305070608040b06030a02030706030b0d06051e010b0405011e030e010903030f06090b330d1a09100306020d150b0706 74
    0x104020f510005d5080c2818410304590404051240e0020803182c5008618610103036090490450340103a0607140c082c03100e2041964858a20503c41c4488030f810308001000040030031400c1d4440c1f18008036040c0740d11049000c940c18014041914054001048000001801089644010049611581c110785060704140d0030a080061031107000c0c2c1c00000ca00320040c1d90205105080e24118103000584418000124601d480e1840004001600e06400d015002c1882502400900c0400c08040200c1c2e0302d5080c101d090f4022440346c03d011465400403c803044140d4000811204110f1400207200310150880500352406c500301900070a03502c42c541c84d4410014080c41c806040c2c02c2a092200803d1403008c5415203122100c1d85901460a901040d4130f0040d4000f00d08804020703c02c441d448600c05103403c002440c48004a0a60740d40010300c0148605020341c00900c503c04a0510240039455500d4400123903201c140c040c03402c0e641d50740313203516110850610480600360010140303459022600d01070741 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 95663597 1250 95662347 95662393
    0xe0f0102010c1202031807030507050418120f05190801170a080f030c0f0c0309041406130905030d020a0e03060a0203040f1106070807030804170408030403110609040e 73
    0x20440e4103040100c41c42e203400c2400169507079030a19005950f561004480c99003072220b010088502e026400d0000700303100f00000c410060714401c0f030307040040030079407245451038201c421741c0107141000386820140990302400703c21982101c0390611900d0840303000604c3c41d20020413452480483c822000501c050180c108407020a6441c0c03500603c880040758448030820300855018410195000001030750034580d150999060301081c031141d9441b00085900142c403608130301c0f003440c010f07494a0440760b20084e408a80c18016076018142c45010003a241c100300140254200aa400e84010000c410785880b00e84028209480640d44120003510014109800c20102411500e59140117009020228610030f42440303206030310140303074454a0b18240200f9501d0103200c0c0b02522901000c10748100b030513002107000b44250f1040b1000c80510480c4480c486071406140586199544140800d100140300300a0720001488003d1804e41407100000005050310300c902e5a0110b160001d900741408908505a0a1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 95664847 1250 95663597 95663599
    0x409090b0601050a0e210102070c03060f0504030509370503010e010203090d050d09080d060e06100e06090102070803040602011d0d1209030c1703010f09020c06070e0307090c0e0f 78
    0x51130050b83c05801000c00014030011441203d03070142d12000c00d0818114102100c55940007952690020300700540a51580d200507540036040850303580c5400c90341d128103071081d80d064640d61704005511040c003040c4502c0185c00d4502450050003182c001c1c0709903401141c00300c10304954441e03171401c001c01d160a4621800d41c4003561380c0141b05000a034800450303400d070800c43c01c1c50140c0d22010a288140d01501640c4d0703018184034000204032443d07480700e80100b0141c0d0038040300389903a91100810310841402c1c5850b00340010341c5440c2c1130322403840d12070002c2820780b805204482407151100f00700ba0641e070140c0d12420140c2e40d540c0d41c446030401c000c2e0707440d22901008805888200c40201011301040390f0301c04c0340741e4140c8c1d07505400400c01d4024850b110449410000c0031000155492451010354400c0c0940342107510382c00400100f186090084a05040880340500f4903512445410355490907129001903050144e00d80c0400c03203900c1e6100e140381c580c0d00745c0d03583c201d003446820234081d5002d4036850903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 95666097 1250 95664847 95664857
    0x9140c010e041b0f0c060c2607080105060f040504060b0702090105190501031d0a03030c1b030509040c030b12010225083106020606091305150415020409090b0601 71
    0x2000c0b141c0f0442003408209480c50502150301034000c1d004442d4500c00300c80c0141102e260201c005103084c4e0140c07040b0b42144150401c8410301103460450b403001d45084503c0c000140030800184803a00b080406491a410911755441c1890b440d003000a098500f160845034105101107001001d46c5401c0c143d080c01044251018880d107880e00190501d118060f0082078185600c1d40095205c10618441c403d8026580c0d07015500d00102c00d2500030044d2105c15201400900090824150429824204500b031a81502c4541c600000001070001800b40d04003000b050543e550910f0030b072030b1100ba49405103075417404001603071610640200594544441c400c00130280e542e400c1c240c00030b528401101d41900d05003c0036510000580c00b8030b5120039142c0a0000c80b403003d5080012030580001d00d803401444119100b440700c1d40c4520400107406803841c00902540c0c408850501140168905c00d03410034028102281c0c04c03c41d40d207007101039034086d9216100103980c1da8904020f1004084456030400380920744 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 95667347 1250 95666097 95666111
    0x1c02040503060103080a02100501030f02031005060310200a08010314010c0c260a050c1015031704050604030b06011e081b0d0509070f0906051003050a09140c010e04 72
    0xc26602d0780b0501009019040004600076541e000b00a284800034100e1414441580c592914503034224034054124007902c1180381ca21660f4a0500519102d81000750003082540c1c262074424000e000c05000d00c900c55640300110080d00d640f680700500c440b20103034031510701951441c45c0210b02001050a50350240c1d242000040040d0b502c501c1c884110f640201c014291403003030303c400502e10700f46100007046415000501d0011141c02901400001d80c222040e0b03821a030800440005075060080fa50701c031055824810301c001043c084200603c08890505503042945500c0407840c036074080e410030754250100030b00b04107296070700541e40c0301008202e0100343c5000c8c2a00c80040c3c046100540300e000112002c8590848d204060800d540d040344a40c132050000c0d00f0603041444e210002130162000801c20b480340894198124010041200c00140026607421110b040440c01480d002c1d2074010110b07115940d85000c600d14441d4203102d01c0400b00a03290b160104000035000000c4568100c0c000c60518003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 95668597 1250 95667347 95667349
    0x60308040303050c0114010602100e060915250507060e0a022d19030303060501210519020c15060a0503071214070f06090608010e061519051c020405 65
    0x10a035012240d250902c10303111300302c0d852124013522540402c1881720a52200010b0403503030010f80c1c9031815001c0c01c001c0082c2002c41d14016110801120101030750361015000c1ea1040110749451035102944801300c44040080f03200201c00c04c400c03104074200041000c00d0401c1802410300c11074050031001d000030b248142c003e074045415082e2078514044044071303c240394045103614224030851148020101c007000c4005a08100d5a803001c2d00003680020301d011000f0480d13502483c6950b4455a000420260b842c080510000240000a2000720171240c100b4000e483c2c004a40050002c603056180540034645460b4002d408205000b00214801c42c00021708000d5a100071840c5801d454000604501c000018240b50b42600d00c0d80d46800305c43e1113810360024142074050b012a064a000c2d83c0c0d072944055640c0c0003140c0044080c060303100e40311006008518103141200700c16120306c1c4104480c0b0f0403e10700e0390000302c0c5c04030088010000314030b00144220120340c000010414540c1104030450501d42480 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 95669847 1250 95668597 95668613
    0xb040b010e010b0324040608030d060f0e070c0f030c120c03080a02210a15080607030e0c0a05010f12020f0c0f07030b040305030c071704080607031b050a090e091f0603 73
    0x40040042224070840c1700c100c82d200c98000074084c06044007282d40c0c5191708050172006103640c1c400c00b85072042100c400300e00c03c021990240c1c0199160358401ca05805162a4043c014074080400c50600c00b42c251884000b1715174440a090010f82911030902000d02d03401c1c05040f040008062441580c8100a883c2e289210208010840307482c02241ca04c05544100144008010a0b1640307a90f400c560b810000302410700084143c800c8078941d03810310950342410940303075544d0703041402c4591041c100d030418081548150300509411540380750202483e96001201402c9034084000d58907000c5002582c039072140800c0244030440f00c0c060b4000c2050718590b440b0801501e0340600010100a000004074003202c1e4000213640196170402da0aa031f054002c0000004141e0061260140e18050100001c4009000c2d10a4041e081150705680e8501400c0c000121050b500001c0181c0a00c00c1204010500d010419000e5205286240c028103000c034466480c0090346800074541c5030068101035003031000070102c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 95671097 1250 95669847 95669881
    0x1101050f06060a1d041a01020f010504080301030213200405010f1106150111030d0b090106051204081b070311010e10050901080402120a05010b010e0d0c030f0503070b040b010e010b03 80
    0x5403034072020a10806480561008584c2c8100754024188180004800340046203524000401d8085032a481e0380c00c0340d0542031320000c46010b03229440c14030040000d03080c03044d5503014000050743d00107107002806140e16080d03031100804030f024200c04103040c8500c3d41c119800c603d24140a0503d070364040d004001103661140001d0161150700b40f5900010f0301a40a0300040c41e030b1000000a881c0c449690000e82c800034018240744511440221b000051000d005008442e000300d550901c50f80c840d900c13502c034014a44d0150707a0011030150b100f0203003584c3d00010700c6a00055407161003000e8001c04a28001005002d040d00720320b2160b503410b5800c0d03420340e030400221070600a0a0030100c44940d102c1c00001e488489208611156000d0014110b08100f4107510043c115070382603c3e81d1100d034117104140030300c4101d2260010318501c0b1803581071011030344814016081c98070039000c89103407800d0360340e41151b84041680c044840218400040c0111410302c0061070140c440f40115a00314038080003070110400c0a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 95672347 1250 95671097 95671117
    0x602071a0c0c19030c0b04080a0906050901020a0f05120414030c030c0307150e10020f07060302090102030d050c0c030c0703060f0917090301091709010e060702090402060d090b01061101050f0606 85
    0x3442c03c400301809000701c004000d400c1130030b00e0841d1030107040c440002c0d403001c1c419200180b0240700220340c0900030700c103a580001c410381c0248440070b4540c1e070302c2c850038494034400d460600c2a12550a07254080300001c0001c0e008540c210801b5040d914145403401d0b4a601d2100c0c80b81e00160003420b456140002c050703088414a140150080e68002d80a86566010751141608954400c15042c18036400055042a141d17115046a070241c1d95a50218220b0240181c4079006800410400310416840c0c0c01180c4c2000481030000c1c50030303024600007851a44103003c501d03c1c03508041c00410174041d06100b60b00d4224625034040c8601c4520b81e69150003100700c4401b40e0400c0101141c0800140c17425803084580c598480011022341038981480e03041c3c0e40018643d140083c008250003089403c268054803000c603405010707000c0e980c07181d0382080500d82100700000000e41e42c5001c084081303040350007201e00901440d10f8454801d0448003040b820b45000070000403a13040100e003400070546845085644200da = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 95673597 1250 95672347 95672383
    0xc07080f0c0909070302092a0f030105010e090402090a1d07090603030801091103060103230702010506100c1502030613050c03060a05030123070302070b011d07110a1106070602071a0c0c 81
    0xc8051032004e40a208c60486001400714041d4415070100b00118182ca0f0240c0719251004101c2081200d8200c040720001c0d00304e450348022400038a2590054070540320101c44890f21005c48401c0c0314034000c6180c0c056842c103074843c0000c009068002080d503000d4030201a051021503000d07648601c0a05c8090001030405548003030050010741c503400250111352a134206000c8606000b24000c0c0a00429101c1c0c500c14403003d040340d400b180c05200c5d201400d03603100d03407281c151102480d0100002d4200a185640003280d91202d440c00d10000c1c461107200ea2a200c424a03140c0c10035106000001e95a5000356004ea89444c804040f82e020305d0907244008500c0c01030a0a6560b9040401c0340030f0301034140010005240003001186404841954000051484030405c4041c0d4a10500312072107031001c81101742540011001300046603010302c41c0c4c088001c001d000d03146043e03070b941d881000302d074001c42d0240e508034071403083c484800c0302d0071040c184c120003000070036420052000d0080c1d4440c44184100d00c400c00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 95674847 1250 95673597 95673631
    0x61803032106052d060711090c040e190c0908031603030f0603081803070e0f0c1c0510050f0f040b030705030607051902120702060c07080f0c090907030209 68
    0x140303540c001c0b0020740406420092200400184000c1c04070b9810718015402c0c0d0354010300e620381d0408005454a42d030b0030610303c40420400c0350900008071809842d8200d00c02040002181064812605a0094208a080c040c0c0b042014241e03004580035012420100040348a04002003040003099541103020406030f40d5401e649881d081d00180b105100c4d51150a007825000810302c000100900040d07042a03082c0c0f0458925a010151141e0704ca000d503280e04c12001c0080f9043e20244800e4039402036030001102d2502c40301d0040d5810090350140d12442980e222070401c0600300c40c10740060002e15058414928405c11140007030842da00c0710329154043c541d242400c8241d940e00f001107400820014003a580f190608040080a59105030300b00b5110b500c02c4084128080d00c006100d56152130035054080c02c2c08159800c000d660b80c0712002010851007000c0001c5070b06081032248415034009000141200c0c0d030320b4020300481490040003c0055041b080c0304001507140d40b5090b0360300c403036240c41c1d0100e0b00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 95676097 1250 95674847 95674907
    0xa0c03060801060909021512190e0610060f11120901030906020f120f010501050409020307050702030d020f07060201020414010302070c0801140a0b03010209010c030806030c0904080406180303 84
    0x60210350700150040d8203014000032009080d034806100c050007071790245080c540300b0700f882c40d0a214000d120300702c10240800240d60f0301e4a0f28001c100c0f80d031908401140d001986a105840c08109445203041c2559254040103115040750004540754103a041580c0d2540c0c050700f00607102c02035154090038010000880365034a80c46503024000c2076611410440d2107001c00b40d000d00030f0741c00aa100c10071403204800402c080e00007541580307048600513506c241c80e084c242010781d40079400141c0340c203007407110a1040c400140c0c2c0070b11040c4040c0c1c010360300410804054460300da151450310303403000080d079104110900100204444007540d0010a01300941e442800d0302d01000715101980c0222417651808a1a00d5483c6140d503185004100da81018490700450702c003014200d105d0031b03401c1c602240c4400024000030b80070705103296000700e00400780d81a1507050340200b002000c2c119008c40c0c0c1c1d0100003c040c00b42c07940080d603441e56540c0f1900050496811a42c0c00350004005100c0c01f9040394031800d401c0e02d070b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 95677347 1250 95676097 95676101
    0xf0c02131112011d06010504030b06040903030905030d0b09100e040f0201200a021503010b070212030c0a0803090d080c070b09030d0608010c020f0c06040e0a06090c020a050d08010302090a0c03 84
    0x520314005040b400c031583d440c2c50400c040300406403800b0151450b0f001141c0785610640940d001d5940041d000c2c140c2d600c0d100200300c02040b1707086044050544421002e0042041031000d0040505171201c00b04050520306c0802400140c01404108000501c41c02881540c405203503540c0e00c03540c8000c100c1240c000314001030f40c03807044220f000b400d2000a626401100300020075581d100610940b01c0b82100c03008401a0000e90000b402140d414420034043c1d18007518000800000e07440c900c3d000d0324548000b110115003010036940c8140e270b00c5c190020501ca4464000c2194004080c00c3c0e141070f150b981064041c1904520811402802108007840030400c0f4010910480341900c00c13188041020550303c00d5440e010701102c001020142c001c5100d151b08030040410080201d100c000d0030b0514190502900b191900400b0f4855007216a035980701180440540c860303c29080015001002140441c2c039085291071b003150103610400001c03100410050300d602e40c80d1130300180010004554080e2103081100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 95678597 1250 95677347 95677357
    0x90612060103050706110102030c090409110301020d0c0e0f0a15031b0c0203060702010519020c010908160c06030c021b03010e0607030f060b070203070911120a0204060f0c021311 78
    0x109501886000104120f00061407004580da6034840310912070001010500300e0000300d0b5414041c94041006e05483c2c41e00ea4885446d19115111f8031040c1040b0002007400ca804c5031407505102a85c0301d24012030180c024440324949081200d000681c10b01810100301202d0303007845144404920b4242c96038030301d40203070019204810a00c80201a201d041071b00182a141240011380c024011580031036800345c41070103091302c641d510540306008001c468003a40c009500c0740700101410356075180c1101c00241d00c00001c2848443c00d01c85c0040f0b08640d410210f040b84143d40c040c6050614108102c1c004c25000708040c106c01c40076132103c03446050244042800b5087c0402204424017a90041001c01030705984195442c0744c0f6403000300907440e10340b13030502d6941c8a4440c000c2d505900c0007000700010180d070b4014080c0380784a02c4095041012002501040301c0044e50080102038001c40c090003010742c0540c9140c0c04d01038500d07000b504c1888507004114801346080c0768203d03840c4c403100305105000fa1401110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 95679847 1250 95678597 95678629
    0xd030e0a1806051008100611030c0601181409070302041d0f06071220030901140103032102161205041203050301091802102f03030f010e150906 63
    0x800011508544030001e1000780240c5105130071481151140c10300c07540c8441d2195221400c00412503003029404e80b0010807803c11100c01e880100704141c081c18044c4030b29030003000d141411403480b81110700e0b528241c03001a0058141c1c6006a000c01c00801c50004e03071602120b4050f14002400010803400e40260407003000240030500c07819080100e890000200140324024070b0b501d044280c8e0259000340255000c00d55039220248040000c50890603920009603084803101000160000c4500002c40140e1401d91003540440c041400107070001054410340c803210301c003004045140a080c000081805115003001520a1a001d0703554400b84d07001c2d800b250060b19542103480004074031490000c04590090040000003400c00e80903060352070b9400303001d180d516070042c0001106119490704803034602181c41c0741c001c010841401900e0040b441c0c0384101024140c40b014544d2440c154400c1c00241034180e011942070a030710000c204140d20701303c024080740e1008862000c1141c0b82c040026000c129812408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 95681097 1250 95679847 95679869
    0x190b130b01090504080d1b0806030f10020306040605040e241b0d0b1903020a05060f0f250303050103060c09030c0b0a020a02120303070212030411090415050106020c01030605030304050d030e0a 84
    0x48007500300000d1507c80c540c41e141d40d446c100c540d0740c2c1041c903483d2150b600b07050340b1580c031841c6004001001500a164000000380000492070781d5070f40010305481840425440641011030002c004413018059807103501001025040c20b420004942a5070700d00d5501a503c0f032490110362400c60b081590801c02c03801d900103001690390742c0c1c5804074400b5030103107102c1284200d10b810400145811b01d001500c000030b08271441541440d4024503940c1d410f0b80000307024440b0a032a03d20644414208008640065010b070303500050960661401303504455044d480641406040b103c204001140100c06209480071091425143d8180400591404604e924000d44c403030b40c200740c0d03070941d0000040a14401e00460b82120004406400140014403050b0307000351901c2e000c80d020511505200054a070014400d000e40c44110f0000038041c82114003e070895401a00452040c42da1076a15002c1d01014003400c50103140381c03d28103800110441c201100080a101c525401c4035825901c800c0c102f40203100352040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 95682347 1250 95681097 95681111
    0x170d0f0501180e0a0519020d050f06060909011a13060b0d020a08010e04080924030405010b1918050c07050a060c030606171b0c190b130b01090504080d 66
    0xc50204190804584182c0d41d02d40802d0150050b00021218402a0081d000d050402c00c0610202c400000b011804c1c0d0700010780c0103000c00025400c00240620790055405068503003001d00030803440c2040a040000560304084025003000314420102411010884a51032611200309503500502081c2d48802e0550302c000c201003001007450340040917850900e9454030134a070380359055903c00300425070300034013452010700c004640c604004c2c000c2d2405c42250103a21403003038042d80c01d4200340c0c2d000b120202c07900d94560302c0c0703802e0909240e01030302c60f05605040410100c5040c890408400310480200b03001b0a034482000c141d41c0ca004504651030300b5040403ea90081c030b600d04112020740003546101d4000781c034101c00050058407600b0054205561410005501d885082021003000102000358146840070131500551803020040c2c030034200040c50005034150050f040004c40b581c1e008244110088031001e40c080001c0f200c80c85141900c2032a040050380da1990f0511210a002d050320294005280440f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 95683453 1106 95682347 95682359
    0xb0108030408061b13060518090717060d080f21010312030504030e04050114040e0111030610020705040504080903011803080a09030c0206070b071209170d0f0501 71
    0x220050805c04c64002c4440c016840d6030215010890016070300820284198110b203020714121010816440c210350068161403d9038103141085c803803007000420310340e60090342c80c4c800c540001c141a2650030004001219520101e50071109860f100d210028510654100d541682d0f8072042458a0007861402900604800f40c0100c0a00c900000c07420240e499601c1014020880044080a000d02542c10304c070441d98501000c4070a03904140d0111000e812410840741c204005482d0801c6217032582404078101107054000700e522a00b0001803106200444000e440200070480c020850405495000b51340000c09a90040c00720300c0c1e00c0c0000d1710440407580507403034039030180c10311007a440d6655002034100d5011050440d28400594240040264003007100301c600100d039441001a0329840d04e860311340c07107aa0404858501c200140409082c1d070750f500068440d010b9500107000ca96180e00e = true := by decide +kernel

theorem cover : BRFrame.Cov 95503597 95683453 := by
  have h0 := BRFrame.cov_init 95503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 95503597 ≤ n) (h2 : n < 95683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
