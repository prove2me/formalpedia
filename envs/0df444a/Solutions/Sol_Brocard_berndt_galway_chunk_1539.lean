-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1539
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:28:20.038801+00:00
-- url     : https://prove2.me/submissions/19593922-09dc-4aab-a212-42fef861b3e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 276618705 ≤ n < 276798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 276619955 1250 276618705 276618707
    0x5010209040f0b060d020f130f030b090c03060c0c1f0f0c081902070309030f0303050f0a021602060a211b0509010c0b0601110706080105040e070317070f1a0a0c 70
    0x1039100840303005001c84d40341000b20f030b1242c0c000f50b0000c0c051400000d4103211003080c1c01c0070040014080d24503944110b01a5007141000071959400400085040c1e0010402921079200402c446070005071241d02030303444900450003281055444c0b264082280306000f828808000d02d90840c0d0249403c4440412013100100d40807240c0c07101c04c81c3d4101914840000d03c41c2d00000580c0100000360213442c02064998485d612100c442803071210580019480320180300b0031010006a523504850381c030104500d011410203480780c2c4011049006481844080741201e4620f00130041c04004921402c1031290f07a0f1801e0010b04000d08503000191603000d4001e1240d25080c0c021822078890205c161284d4160340d1325a520300124910041400e4100904680d00041c10401042088081c00c41c94a501c0447d606003024402100c3d00380c0300400d1664009102000070400b840141141074920114095490556003000c011410b001c0302c0090100031884240305213040b807510124091000030b03030140100401010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 276621205 1250 276619955 276619961
    0xf0d050a0e0c060715110403030e01020f0f0c0409140616030f0c080109050709082d030910180f090504030f0804050c011116151101021201060804030203070f05010209040f 75
    0x1402c15003149041080202240d0440030302c3e00054000800401c160b1409a29200d494026500407004a4100e40010b4419a018000e84158400260040c0b034103500c5541d03081e17541c51030105030a0249546182480a00608103105111000040102c1e400c41c01c00740381c80c2070205034007102400024941403004001c904a80641400c40710155a40b00e100d909012104000b813401800000c00d000d10000c000035402d90038005072120741c903113403c40c1a40c02040000006c0302032501d541305107503410401009845a55092046182e0032203882e03d49030362082504000c8011182c0e410101580c0c01d020b90000d00713013007260889803049201703a030f6481445408840030350390780030309680007052504820105400d55104031034118005140001710350204044e42038980b002d01440d045408036101c0c0100b102c0e1080d41000481c51400d4260008525140d0502488a041d01e4107018070740402488a0100b01031610070416a854690032030310f03c1d40d007080280b600758000d41c0203144860055084c1010000c1c01a210701c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 276622455 1250 276621205 276621223
    0x6031119050618040e0a110a0509040807030c03090e090715020105090a0204020306040b041104060e120a020103051e150306011e0e040c1220090103031d060f0d050a0e 73
    0x50000b034100840400043c1411021a5100f500142c0c1c400101011a40c2001035600300780c00703003500040c401c0d0450148680d17038416420250180108070148400103a4490071208265050329042c10220380390f00d021103801055501c49601c080f404014007a04040100340e15080350400c4904c0ba0040101e400140d0903654202e80c04192900450840000360074150015548000c000700002000c80c100703000a03080303d20140c050798802d80d0108083c058150130100d1459070b1041114050607949140030001c0e952003400390000c1c10161130700046100000b201262210121b54418650090300c1c1080220650640d44000540300b44100320000400e18400344000f89800c1d0303104200b490300340c1007982203605600d019100b102e40c0792a0320800909000d4520042044c103101d13019052840e0780c080307817180304000c25020403403240c14508010000250004090200400b4100c10b1410f800c08690000300540a1104804c44c900b000181400c900711056200c40c0c41000381610811210107005136203981c0320011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 276623705 1250 276622455 276622459
    0x6030718090b0f09100b0f0705010b010311031503010b040513030f0f021b1203040f0e070509060a03051b1615020c0309060309030d090602250213020901050d0603111905 74
    0x2401c001c03040c14a804156403004031741078012051544c0d0f0b02c4044040d400141c001800326804504042000000c0c002d1290241c0c091900b1301122070300d10050300203444050682207030130b00c2c0c1d220400340a803170a400480400784010010092403070700401d00c0b0082598110120300188140700c400490b50b01070904401640c009900a10903007144000c3c0c104122100c1121a42c4803030f904090700c940002c200014000707480400d41494521f468036025610004000e001081800014405441e1f941c546e6816290031103d5490041226140c0003c41c0455110030013055120302000181107003030401142c0d000400e2031007408410281e817078603481e43d8224091080e4055075030b0010040704009140c02d401071504614840281c1e0710340081c2101200850300242403c40e40584c0204104a80c145440245010002c0360206a8141501c0b6400658201c1c45100e900041f142e020a158110341d104201b0b86035544044d01040002c65140d0802c051008840020f480c822000c0d0301c604045d0f000e005078072070f003110b0b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 276624955 1250 276623705 276623719
    0x302131a0f01030908031f0602070506090d06090c080c0312030609011a041d0612030705071e050909070521061909050114040c06050406091e0506030718090b 69
    0x4840304124440440200d00c50406498041080101701c440d00114000d9081510000fa4901035140341c1d00e2541c00c43d40004155080640104901c0c0c440f6030482d0552241100c840038240100d03d0060024441d810020b041c01c81020008604407800044040c4000c1c0201c0c111035901c9500340b40d1540d039100031074030203420800d0f038001000000c0e4041c00c961a4641c4144038182017036101c0c410040c5030540305038201c11420909061042c14100402070456404114018514010303042e00d607207135190841c0c4600761450342c042c80b09007810380550440b1405010003c0c007542440c03c180c0d1103030340d4401180c01003d10803010741a5209019074101081c010a4000d0383c040c3c6003655401005400300b510a00c41d010301c141d110440c100001d134080c495843c9461000d110300720a03041600744145980b80a40206060220801091045d40e4100648008a80409002068844500842c44000140d0b5403029800102c048280701c0380f10341000314901d203050640754042c0070a6460721600140c0b924002003941040b5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 276626205 1250 276624955 276625001
    0x70c050603061804030c030311040b07150e070308030118060f030305030c070f140c4507050d0f020909070e01020f16170c0109121515030213 62
    0x30640003859001c480182403d02c2000e0b100040e44100d14210380440004090031040402c140d018401c00d0f01020124003094282818401002e143c0e101e80c02000d41400803013a10b40b0b94450454101a01040310001a203400940e240340140540d0428003c1900d00c41d10444481d8250340c4910691044070310400c08901010710307584007600c1c550701c083c00c844c0b6440810004040801da20541c51804030744284517040079202078001030390070859500d0b50b451040b0542c0d41c61140101640810060069400c106011035019910030012074260424031030001d020740f441040710f0325800001030083c070729500c442440010b10121030842244503100440d40e11510035008140004d1145c0001030380000306004450b03849500100040ca0550400025014a8020a000e00101007000303501194050014010150300340c2c145d0020341001180d00a4402100c0a04501c0c07042c0103900780b041464440030441003001100b0a10780d50344d44020750005a0280d42c11100081c4041801c0c810200103882e070f0444986111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 276627455 1250 276626205 276626209
    0x3030518073203251d1e04120f051b01020306100903020d0b1e04060b01030b0102151617010e040c082d010906050a02090a08070f0905070318120e06070c05 68
    0x140a03107101d8007848418100105040607141e2000c20b401e0010341c480704240c94401c0580c030401c0746c80407040b03056451200500002420241c50304140201c01d00744200c18020019080340c550150160882c03407410b0411580c500c3d1001907008500855058602600010505e282910600c015100007900040300102290100e02071284458110b00d1007403000a01c20003a1885270703002c4100755010f807819542d4201d204043d42c0c25109041ca01e4100303001600c00926500304c100d251240051003404d4808030510b140e009203120f402010b0410060f8640c83c0d80950311118440030b0a0001ca804440340c8040b0031021451480014000000360080003000401c15284d200143ca0090856a02c442543d2600c0807140092540d005031442a582403c0040c0c80e001e1746001c0081c140d0701c551003403086800c05103082c4241c410007100441580c800c10320100d000e132a5408114001c203002d600c4a008031410300f09100c1081140c0022144500541e550760035001c0d07000042040038800c10704000c01101c800c407001c20041c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 276628705 1250 276627455 276627493
    0x40b070206060a30060f05150f0a0e0402040e0307031107060903050d2307051f0905060f06060d0606020307020a0906080709110c061801060603061203030518073203 72
    0xd135810501c40d50740302e2055480c0c005403011800d11010140d00e82d010031482c0000e001480080700d10458581c55901804408038161103101e000b5003003016019000582035449a0f00a200301c4980c58040740d03038400103810000e1807290542c0c42100d990044c03160000e10940305a00000c25039410102801c3d20003003410090714140e004092408010300300d101c10020a1f00310001400348180907c002d80301c0090f1000054000e0309030354503440c1d82940382016070808030b440090040da02c9444415010102e0301c1d04000902c081c0505003425101605083c0c010894640c084003905c0302520039590f51808030f0b01c07a034001041c0d40b07440c0500d1101e03501c180c50400000070260460958001d0310341c200d41c42d000d1000656400e00100300e03403210403c8082603910180700d0f0240b02d0b940082983c0d15040100c00d040a030040317983e00030f41c42c0107001c050300d50003c41d40081c40e4210340000c280318001181e180607907460040f008000c460300c0c060307504d40301c04411440700804101c00380480240180a4080c2d10320282c601054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 276629955 1250 276628705 276628769
    0x60103051905150a0602030c24010506181504050306060907270305030408010204080f03030f01090911030105180c04090f06022104050709180201080402040507110105040b070206060a 80
    0x10f42c4034103418161150311105200c001500c03890740a5680e515080321a2460444010520040700b501c030713111a0405048191100c3c151081215802d41c0c8000707031072440303410391482c260700c2d41d00c104e0300d0490703818015510000703000304c03141641a1012591880100454000211001008501d4103042002d009045601c03030100c4110368080705489030380b252100c0d0701c1d40d0801d07009840140e40c00142881074074400c2042c4003e101d00c42c1d000314518503212403640000c50b010311901242c00d40b41c40901c0100800c0e40d4581c1c8041102070020005403421010001d1081d6403050302010314000c1c10011880350800d07010f01c00303c0c86d4002110380e107009016034038880290320990801c404901e511a401d005610b00901460182c2d0040300201042030030095403104940b4030b1a40001d007080b00e40070510041c0d8001107100c2d44603404850014103561052010364145034010740c8900d8a52900b0100820040c61007101030084000c1c0c2d08607071442d5262030510001d4042801000a0402c2440e01c00200d01d15500211170 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 276631205 1250 276629955 276629971
    0x11010f03090b0406090b0f090309270a05010e060f03031b0312090319080123040e010609060305010b0f010503190912080a1a010e010302130b03100608060103051905 72
    0x6240e203065101e40500682c143d9046030341300c0c1c5468841061001301c6030f01c4c6801008000301d10f04241400742e5559924800e450046000303076400303207400182041c4440d06082802c2003240c100202d103070001d65800180400d006101220403060081120303030a00c00041203a111024000350f150402a40342a034088a40800c0c01250784010013200e85000020010f080c060000e1600940d111f03d6115180640000c042503150104500d4400420010a00504082e03030940103010610400000e50080740140c410001d04104039800c01a00281c108080d90181d01201d000300000c0040c03900940400c035087c050a0641d03800a0b0040c80030659016144460b841c01c0c0021103000500c0f60820750b56002806010300c41e52000c288030400304124030016014403d0450800c040030580f0320340910000c1d04010b5079911450400d640420150030004406004c64080d0200480040e1245040c00303544480038514014140060b05543c00304900d035001c0c1c05118003824505250416800040011100408004007990 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 276632455 1250 276631205 276631211
    0xb0405040f0f0e07030510051003150908031801060b0702060417010207120806100903050613051216020117040f06022d032403030a0305090307140703030e01080411010f03 75
    0x102c1101d1148180e0440c07920000c09061800d02c1c6060083c142004021420301a074100810484200f00045484054907845080c0800444202d00c1d004010100d1500080c0901400014447d0740043c080c0c81d00603130003007a0300910001d0b444410005841c029240029004074003403100f40000c035240d2000c8014070244034001030600e0314688942c2070901d00a0000c40225400b10184400d50400e4114014a1101030078004e81c002d25503030780d06139a55001000c0304000001e9800d601c00b08541404594624201e00004c070342c8990b020a00f000300b01010420032070120314800d020340350540c00c031036003540b06913080592582a039205440360030180d404800313103500703400c0c412021000300d030702c2d9620313510504c43c040603000d45a143c556520a007488442c0c00c01d07100d0031200038450100381d0b0000308440c141e06c0286004100d6403150802c0318514010803100404001455032060780d1034100151980407a8005d0762495240c509070001920848801d50303002c0c0058010000c01c0800754040c1900d40e02902c9185000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 276633705 1250 276632455 276632471
    0x3040302032b0b0409050706051809040503120f07020d050d02090d030e04061a07150608030f030a0f110d0b0316120b06030325020d0c03031106010f0b0405040f 70
    0x1403000201c0e40310034000e81640603911241660b41c81c0b01d006144035080c3c80800814026448035030303903002148140d1003001800a00c510002910801846210344040c0822802d81001e240c0b0a4507500409200700306013850302c0c0000d411548a200190080461760085c100310b010200d42120fa5601045591080d03d07020460b0340b07029186c0c0c0b41d51280042c025661514482c4088040009030b418030392100b0311394001a1058100da0444504464003e03070f21504885600c160041510060300040d400001c042c0404101100f43c5180400150721682814070100960703001c00c4840701c1101d4481c100e0025001c0d040c41000e0b000300302136100750b000c014020210348052499082d12048c10460342c004501c3c2c0c0d0050b587c5001080036079648103400c81c1003100554200a110f04041180e00c2c0d00c0030032a407040c2200241881903440e402209011a504403100d21308050326030030054a400480d2510032000e1141c400000307071000c1d9014540040c0d81000003001d00d018500340402c000b0b001d6030020030383e80c3c80d076500c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 276634955 1250 276633705 276633727
    0x80402400c0e150d151401030f0507020c120a0807050a14061b0a0905040e0106061106060603160c0f0b01081608100e03040f060c021011100c0e030a05010e0c030319050304030203 78
    0x5c0c15000303003420381443d40c20900401c00102a920012030404001d4248414059140d03000719080042110076104010900c1840d07100031b1030301101c020003524100c00040c40005110002c81d80d842e085004842581d0740301d00b0704601d15910b20307088441c450300031181c840c2d05604141350030042c40080150f2600030003a0b512500003070110350300d0b6058405241c0d0358140410500340c2003001c24500d41542e001600d80b5241072004601301c0d1000600a000010203c1c07001ea03481405500503040c801d0304620001541d000914100c0031081007070003010140d10415907817441908c007045140c000d4035441c6d00902a03030030741402800080c061503034607071100d80401c0c000031401403284d03076a5a0003011159915405409180144803030482c0c6464001d003000760000ea01c41c507150001401000d400c948402c0040c50b00e024000464041e003200c408164180542d000c0c490502405402900155401006075507000140b00c040541e00e10030303052403003401110001b042107250f00510245510602038010740385844074100b1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 276636205 1250 276634955 276634991
    0x1215091902131502070605090d11031006121e1203021b16030614040807020d02010c200405010602010b0d12090308040303081015080402400c0e150d 65
    0x1141c103c000400506001c02035040040c800141440c0c200f1614200020000c50300700c40030244090003940515020040303645003080710810f9104041000c006181d11203284948181007500180c61215112807102c6009003040d00b40418140e2001c0303058941c51120206501941003080c0c030003003520b07015040004d10003040c0400729211105c0740303618441f2400e61611104540c444ca0310640319140090810000030703e0581111142501260340190354511880120b403001d00c00d110042004500c0d0310815900b4180203259401d01800300c0f41400160b0f00c2d001d08a088807602404141c1c460459150080401c41c0303c0303801d441038a802d2400482c25500c036150041a944141d0040380011008070030402540b06e010390002c058100051942c2204000020081070b40101070030191007181c0ca10f04118180c151449680480c403500f01e039014482c60141c820402c96201c0782c042c2d54981d8100b881d260155841800d025440d61001808111403104d14103c400c9607801091403807400d10380e03412000c96451a548 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 276637455 1250 276636205 276636209
    0xa090804080307060f1b050d020d0b13020901020622060b0a080a0b07031104050d140c12010f2003010b0711210c040507080106030e0703020405040602121509190213 72
    0x55404a504640098071808540d80d481c02130086c0904241c3c02000b180d40002150b4902e001500056112144560204003c0c1450405658426440c80d141200e0000c15006010341c070400340c00b61995541c4825402140c1176050550001780c49255048a0014500707500c1385401c09805000c0d007642a4071001014907240c0d41d103074142c4083c213400302040b0580d6410f000b419950b90031004e40381d050030316000200d4a4080655401003c1c4405206c2d103440742101041032441c501001411180c141003088016402040091940d5848504104a007a06a103054400c0385110900d60300d03541c0341d0f0303103041812406a0080d0030308890303058010b103600c92242e032020360305003030894000c1e0034118507807585265038506038007242403a008601b070400700102d65800c9140a030440d001130602040158125131110704040c04c17504002d62180c544030500c402d006282d40601008204c8640d84840c40c1c940080700c8200c4824042090b40c06101240017400d002114804240e034007001f984090708000401150b0b96510740d00e6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 276638705 1250 276637455 276637463
    0xa0903060f0504140a05030a0f02160f0f050423220b06040507030903091415031006020105010602070b07020d0804030807120e0418020f0d0b07050405031507080a090804080307 77
    0x34424041404000702c04d0089000c0c1c240001c1c11086043d42d200d64803030040414040500c003220441071200c034020320942c2440340590794620700150710b581e208407652640380503c0c4804808548042594145440354444d00b40d080c0b402488085080400360908007001000404c070040300c0d2054000360904040e5600907140b186580c00f000d0315214050101f2500020200d00c2018200140398001c203030407a015070241d80d141001c2d004000581e00100746030b44091801c044a0420010800a0902d22440030b0b10981c1c1080e4024412030340e940204070781d111602d000340100c500f8104154001403030700c541c0111000d4801d00015080c155252200340361074001460640740900700303048500155900144403e40c04204842c2003022900e800b105007000520310000074040e40440502e52803c1d81c4110351040e0762a485410416140380c0040014032a80051227110300a100f403500c0380101915103c50240320341401d6941004aa46800318180900100001035502c0c90302040013107841c490a00081441c4c6010b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 276639955 1250 276638705 276638711
    0x60a0c1701030f0b06010309020f1203090d05070806010503211e0f0a180b0d0203060f04020a110c0108040b060d0c1802130b0306030c10020f07060804060e12030c0a0903060f 76
    0x20310700f0404a000c4c0c0082905042500d849200e10040e0b41d01d40890b121460203403602840901035107443c03807541c030440d030f14a9440000ca00d58a801c0000c0020081c06940c038210580300d01c1e0742d8480516507140c011603003502d102e030326485110545090b008058010300c40211080c040d03419040d2443d1a450b401403c0c528010200041d200c0e00c065000144115412071070794041c2d24183c0b800c0b074100214045c00050460b00e0340c000000c517400c1d5880c2d542ca0201801c0040c011555441489405080c130103900308561450b008001c001101513000b03054a522494101550480c280c1e18101041164001b0810846511882110100348010f00d040502040c6188040060f91041094220300031101154449141c0001c00c00c10840c980c2c4004c251043c0154098078200c1200024075800e034104040209402940d00c104070001900c03c0d07020740000d001d140501e10401c12429440e05403915007000c828842d50061003000070400750800b0400a0001340b5062800c0c00b000d5403242e40b240103803045000c4150f11a61 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 276641205 1250 276639955 276639983
    0x1d061603021b06160303061e15020c01020a1101210c0306050307050a0605130801140609150904030509120f0c271b0f1c06050d05060a0c170103 63
    0xa01000044124640080e100080c0c070300b03660000d003003403041611001c0105241c0c1ca0280c10107000781c01010180081180812401c64011321256444c00584a500019491040d4003a030003400800c403000000c0b01070307024003160010350f01ca9103410518440043c2c10401c04940c402d00100c4078036060004c4809041002c90134214100006096031540c0d041103210b504041403c115a9407000e8a44040712004d0070f10700e445003019000f100401e00c45600c00344e519400c28080001c0190800c1a0b14842d40080303c0381c00150b100c50191a01d0113220f0000c01f0b8000b0854004100402e004401520b0244c8006191650410b52410164281074003610b80c0d0200381c0c42152082890320b0200100d090020510a9174252502c441c3e61080d4400700141107044030072500d040011125038010700f115444114071001c0b41d03030b65003e12103074921f282c5001522910b0500e00940450b45242c0391404c01100354000c0d00805458a40d5007005000b0908d00156000740400d02020040c101034403c0b03c28003c40c010107401442074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 276642455 1250 276641205 276641207
    0x90a0201031a0d060513080a08100603090b070819021303050c01030c02032706040b030711031617090301060f0603050c03060a0311130f090203190f031d061603 70
    0x80c0c42c1c007031155030807a01492040d11036100c07005071503e1a07403c0320b40030885840c3c00900c4030301c429561002030035042001a02800310382d0803002003405901200c040c00c50300b954860046046410300b690090100c841d400104407007a10451059421140d000c441c030009146030704900742241d1103046800c6c505840c0260030020b010302401011500c180a08041c0840492146c0c025201d10812240b00d8142584201c0c0c0a004c1290381c440c01c0c101000030780700c5607945441e44101c4145820444048000a201280092070f141c00801503508100741c03000824942c0449640700301c0c05201460703810030030500602480f821a41c09008040040013108801c001d03040c2050402400e4540c000c00c80c410a100820030300805464107165503007203981054400c15024491070014103020141242eaa01146c14a112402581d500780e00050300329208600f1200c03113a0202c42100355114405c1000b40c82241c02c0302c8a100402d0243c1c00200e06540501180f28400e230f2010002511904842e00d41c3c02c1494035000010101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 276643705 1250 276642455 276642461
    0x90812270a0308180a0b070903120801080c0f030c010c0609060507030b12070e0415150f053c0a0902042c040507180f02040308130b07030806061b06090a020103 70
    0x100101c80704c01c00401c4200702d00342d81d0b903240c496801414082094001048180b10f142e00c1c8000c2c5900414071642090035040041020310203010307003400d500511a403028140380250340190440f0b80500601407442c04c2d58010b4884106d10101950526218152140000e2040c400e052050016841c005080755007042803106407800701e16541d1041d4800710090020705844044c40e6406988540b00100740000710070540080c00e50300c00150901240b06101150110603440700205880003698950003030119010805101e280c085814411600341242001150030141140680c0d582d007d812000842e6507005010101c0e44554803100741c001d81c115204030640c405060403103881810b0000c00c4c81c3c509098681d243c0b00d1400744142e48460748000e020895210b05608940c4200100c40011034855540381080441513016000b010313606801d044002c5440c012041c2961500b5030035a44414041d0303107132000d1000a43c0124031444141420f1069009400010803055125250b024068a03003640c0500c000750503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 276644955 1250 276643705 276643711
    0x31c020d08010e010b0906090607050c010f2f03042409090902060901080901060906030f0c0b0a020d052b0b0f0907020c010305040f0503031315090812270a0308 70
    0xc01403210700400c40c1d00003241410f81035680d400800c55603000a503000681c2d134410944407a400a0004c255034007400008503400b40c00e480207803114000da0580c00d50460358494022800d41000c034100311040c0c4841d8100c0b01600c5c03111107950489251944078210401e950750b44802c0d0f03c901400800d0842881c07030780032050350004c20032001e040c050880154000381650103100b2101d1304100750f000000c2c0b00408250041402040494804c01c8035a40301e042040d1088000c510a840c0b40c0d006e240300041c9150040700701e40d038091203940900f07401d0700c0f524011910b0394021020340311600ca0190312801c40b1400b8403d40455144515000180d0340c100b00c0a002c80c4070280e000b000d2041092000b000b4142d07401040c3e00b400c0c2c0409190020720703550796103080203030071050180192140c0700c00300400c0071700c00300030800d140342c01e001d2652122114040f2003004192440414010b100c444248282581c0c1000c0403901034020811141c100301c0034141010441950702088018061917210100403c2072540254800d90 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 276646205 1250 276644955 276644957
    0x51f02010f060b04060f030f0c050d11031b07081e0301080c04060302030c060f070503030403170f040f0311030c0609100f05060a0b07021807030225020315060f031c020d 74
    0x40903d02d4030550003000d02031407090005020f00301d0b020a2095109901000c80c0c0030b465001008803107a0a9001403043d0031495100c1001d83c50b120f46940028428810f032842200360001d002000001c51404400075007013208100c41e82c80003406081c03a0360350681d00d41082e801c1040482620b0b90725100b50107152015140b80d007805035103400418800f50b1404038500c03485400c160303011940d50380d91002945d4603116020303000d40381d03000c0441400105903200c2e0203158000a60400d00c213454031050741c007058184050b90000c0041414102201c0000e0260501c402107444000c2928100f500300f0110600340407080714215800c0c2c0090314004000c10652051000f8014910700c108102c1c94409c0c0421700000803400790755a440e8003c1100c004541d107105e240d20f821141040c5184103400c00b4100940a034002e1601d0034040480041035001c1c540d00400c1c0381b0381d000d4000340144034007400b400031500500e4003d407159400162050301d200d211385080003846c9000c03202450240001e1b2442d003000b81003900c0441100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 276647455 1250 276646205 276646211
    0x130e061905070e010509010c0204020409090b1807050d020f040c0e03010c1b060b0622080c0d0b040201030c110730020109090c0203090a03060f1b1710051f02010f 71
    0x60a82c1e0186180b8a0f150003800e199a44d40c66620050759501090b280003980030b80001404126401990480040320348941c03c43e401a88820400035000c10014140c64040d40c400340c01000240361217802d00d00b01da4001350031480243c04802c00b04040d2880c00b801003000c21000f01d20f0000d142024400d108010b00140341c441420140361001b0fa680c01e03d0510040e1409850b056000c0c0156141000c4070684912031546100c2e401c0c29007440070f5106114840d21409024017100e4140904080811112480d80050000b4240c1c0c0c9650041d0003e205c8140702c00c080010350400c2c0c0c9a0040d0402400c1e0181008083c000c2e2a40039082d80d01900d51420710846a0842c201c220410050740c0107100001540c000180c0031a6800d0304400482c6140600002c0b01ea00240c0380400000f88400e40d40030340c0f40104900742c24042d5201010100348480c2680460200040030041c040e01d50042d050302550700302a5041c000e1010300d07603550000d0750004850803001c1e884240900b01c040455024842d100b50701e4551b00041c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 276648705 1250 276647455 276647461
    0x3200a11030c0c01111c0c050c01020303011a16020306070203070506010f0b04030b041103031b0d0c02130c0201020c061510021c050a110a03020601060201060b070506040f02130e061905 81
    0xc3d103c540c614034032818401003809042c81c2000030320402d20f4506212220840110407038400402c0364080800a403001d000f449194a825440072013128182c2d80555105d00640d000140c010111741e12561442106640020b640b10042e41e003448407501850842d0300840d2a60f6142c14018180001030307100803042e00d43c05900700000304003601658200c0380c0100405d00d05599600385141512440c0c0e078551307410700000070998203d540050300700504201e40340807602201c80400c2c0958025800c1400a03503c5006c42540840038500741d001955184501d100140c200010568014904a000e807204580e0400e90100041c690800b12002c6203059114401080071900c44034400c0c101e880c0020310b01d02000030025003d5a0706016030030300b04084904030308484030f0800d00e04000b034980c1800e0103071800550a02500082501510040d504440c0d000405000c50340c80c0c590b00c100c40c0303c45405040f0380100c8103291b40c40e800310302803060704420410000504031502d85610400c02540006601c201d0782c2d4070b0300c424 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 276649955 1250 276648705 276648727
    0x30c2d220f1a070f15050106020c010c02120c0a0b0304121b060902150705010507021b150706110f070312020a022d0a06060f1502060703090303200a1103 67
    0x550048410112a01c089030b00c1d480102c280c0c501c0f90400c0a800100d1908100742044428900315030782203801c0f001005180d880341422600c0b880f60085c4c442c0080c40c0804801c02514008a0700ed489143c0a0304480313100744d444001c516a800f0540c01500300100100800040c080d00e240404121182841c0908607030a1101d59450304030007400010304401d40d2122180c046441d04280400700b003884e01d1100d83c44001524040380030305401c843d0840140150381e05022020001c0d44219000f40004100031092001d50500e1307507458110750019981d1071788401c00c00c0d40c5584141d008000f0340f8100c580b050f50ba0030340c5041c0904508020013680c0c00d0a441003000d0300700f9540c0418420b02c1c002440408001040340d4001546601d5103440340c0d0b043c14000e5040340c8082160030b501c220704907001d851900d0300316503480001d50280c42e113010141015800102c00181518400c2d800095200c3c824240090003051600c55200c81c0d07680400c07032161103480011030030740d03040c0c0207130700c011000340940021882d11a1000ba = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 276651205 1250 276649955 276649979
    0x90709150f1e140607020a0909111903020108090705060a0906140f09061303050f0703140d02060106230d050a1a10210903020c13050408030c2d22 64
    0x1003103400c20f0b185000011030640d1000c00b150344580c0c0003415403050541b9400100010600d1003c1260b040e400c02d0810b0f1401e0a01841c8198488249412008070038619001910341c0040202580158000d2040108040d5980c1001d8a4110f00a54030907904c5801c1c1030001e441c00074001d5200b1070302001400007034204186801100c05504050703500c60307280c1a940d0810702c9140340340e400091090040c42000240904000303100c000701d80c000c4100040c2040e004c1515503d940c0f040300c903c00160025030041c480c190048212103090240090355460140c08002d150a440e000f0061811286403140c05225a00b0f4150091400d240d08071043d10800c001001d00140ca8076500c80680014018034500180c401c403a46402007280012940701407002d10b48a00c2c000307413680c0000100600c20801c503050010310744024410b0030f2090b54010807d61854542c44542d8001c0c0e00014459400030300740c601d241d2200c90080c0c901d10a0091042051521459a00070900c07107020001c00c070075800540441e00b04500c030340d000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 276652455 1250 276651205 276651209
    0x60e0f0f0a290d0515150405010b0706180f03050a08010608060a0302090604090606030606170331030203030a030c0207090213090b15040b09010215010518090709150f1e 74
    0x8410282c103030508804540301050046020b0400d020300000740b110307411840c80342c0d03110301c0c0300010070140344210100b00700031541e0030300954660b400140b10000c00912181c1c40400d5141405c04a00d8440003035946400c0c2000c0c0340c21080b0001600850725110464000c50700501402c0c03907081205c51450b01101086080c412407002030710980b030392804a600c41d140c41c0e1200400075041102403100c6031b280e04241024212a00c12643c803440d4550380b59200d411f000c0b0984011550b55000c0b050f01d41c3c004101820400480309110001d80800c00740040107940800040c035a1080d9504c1c045022351074007a000e410a00301c1d50040d004e07140100108014580b24036281402d594001c100014428000404035100e01041e107150700c8070540006011540c3c01003a000f80c070310070703030260f0884c5c1c0324079a00184150000c10a00c202c0380c03c160341448084101c0f0350b80311b0b007039408203401c03084032401075507000d8403012744e210a030443c4845483c9541c14030507a00c00d01d844801030401c001e104509500d03254076041c1c50003614 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 276653705 1250 276652455 276652511
    0x40b0d0303150906060302090f0105360603040b060102250314011805030d05071b0602360112200703020a020a0e01050108060d0b0703020706060e0f0f0a 67
    0x48042203541c055181c6200080d08403c1e20400c9415181c81014000354003128201d0700c00c00540c142e0031425031041c3c044641031581c072542c0851100304040d10300e041103004040307006209100c0b1200c200c00d4a500029600c101e009000d092524100b08001a00300506a4650000700001000301d6040c5c4200401c0102160361000380401000a0901000d0042c40030500c001c007151140a44202172160000c041e00600300c1d061005c100b2601c600c80706480c00d88403940750041035104c2180c107070701003003c6601a104002d00355043c0051801592041c0e5000ca4103821014040262040880900d503484001e00d1000b44003680104041040314421345600c1040c4800e100301e00e0000514901054424043d09800e1380d800303071940600030b440740f070185030018003400340ea03001494480004219181180041030701d0781d0090f40d002e0054a82460840180d401440240d41140c0c0301d800009020701e451076051300c582c42e01c41050100d41000396010008840103060b072030344542040d00130a0040c0c4044d180014092403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 276654955 1250 276653705 276653711
    0x50a051308030304260901020a021314093403020d020d0804080d270e060a03020306100306110c06011e0e09060106090504181103031902010b0a05040b0d0303 69
    0x80200111054103054000140d103000101c18001003007000c604035030340c84240c004182e04070020302c0580f40d21130144184482c0103900801a200142c208000a00180d0b00e00e50b40124200d080301c3c442c00340c212002e46158580390301150a03c84140e980010600301d85040c01d0410540b40289040b0340c01c907034510302010748a1070740d40282a0443d903a0001d03058116600001850300c1d42e64614080d42c882d80743c000c83d40046007030b61154500e1805920f12400c01e903940302844901c45800c00d0303000500c03d00000d0000380c0012500c003011026076010400131340715900343c0085141c2c0700c0c2107140a9056a0010103c042c61100900c859420184042102030640345141c145007201102412002d4080308240e101132a65a800350510920400100f4118162509a103588580c0d83e5501d05210072070f4410000c1c5480715010303e641800040c1e0000d541150804006d040700d09141c100724206020860030b084100140c3e660f41038060721401c100d40090001c0204840c100052412100030034084040c2c40d00082c00c140e5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 276656205 1250 276654955 276654967
    0x70909110603180a0c060306060527040e0102041e09062103020c0d0506040506070914091902160309090b091618141503070f11010608030307051207020d050a05 70
    0x210040d00b01c0307411120400c85200789200d040417815224503015010000b801c18a011a01ca40100200e071001031202809503030740f41021004401c070355000601d81e5801a1112420f40c2880b50900203440580000103070f80e10300c01740d0340c0e0041c0303c008129440081040d04100302049500762240c0c04c000c8070a42c1c0c1092400110080ca000c03030520840c01031282e40140c06004c490280540001d80d80d102d2032142003100c64070340300c82c00b00380c505e07281d18030420030504032a40c4010103c0c144810311076009902c4640e902030f050120341031141660041301000c5502220701c1991022f0640c4440764200074940564104091034440c030100b500e81400409030044c03030a002103010b045900c20715001210005241c0854070150b250705680d01005480114188a980a01d42da454145401401c580c0940419120503010707181c0c4000c00d44200100219140965503100f00014004200b800114400e0750740f55180359407582800c4000200e4400980094115400b10504081039600441200c0c1003489030305147c2e0b1214 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 276657455 1250 276656205 276656221
    0x605030c280e0c07050c0d120c0203101a0a0b0f07110609130c1403010807210b010806060109080a03080c090a0503010e03030406061d0112030e0301020307020f070909110603 76
    0x20742035000500d150744030000c00080c609a4800307000f031140300740c1c19900400c103614100311904140f49005081d05450501800d0314900994503803d200d480581a2034500b0030b8850854206d540c405034554070012400b8003003c26242445080e00502002030045040002490f20890180200c0c0001456500c203a0840d144940e00e00098491040005103807902c0b1503004510000a08140d04180700804c3c142c812000e28404035500b581e05131004040180034061810f181052007038846000500c481a82d60310f0380300071030442261507000e040140300030442800c02c2000103003507004503401341d00381d900b01d4500100000d900c51407185e0400c110f14045034503280c000d40024404281d6901299041d0300c0c01a00451120020001e54030540c0105000c04c862581c98044465010222080003001c086010040c4482e50780000040c10803402403a0400d160704030200468220f074820b0300e44a0150303000c40310001282d001007060502600c0e84010030b02c13950060703950328028403101164092180c20044005020f40c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 276658705 1250 276657455 276657529
    0xc030f0c070f03031505060c030d0203042108010501090608070f030c03270c0e0c070b07020109060e0c030d0f14090d02041d100203070c08090f1011010605030c 70
    0x654020040c00c2c00b41801d442c001c0c00500c0c4000001c0d4205c182c0610000302d5203401400d8982c0341c0d01c907501440c60714005011610003940010011144d40114003081c4940100021540c00c903109039469000d03084d4101800540110f4440e4440c1c820441030b0010010020f502071a00070404585046c04502c60b040c2a82c280d01400ea050700140803110000442c0541440d43d8224050403030050402251254688000d1103007000d003160301c1d40c41c0803010069000055040e0030b01b168030403030510001400b000301d655a80183d51100d0301402155201c0300e507400d2640b8062100d1101c032041828010a00c1841b41005000e85148690314048910081004031a82c0c9900c0e1804013402c5c0d008008000014842c1202c00c80769080c1920112148602e168035095681c582c801c9078041e0004d5103446100200035500c01c0740341c1d40310040c81900080400f0140030981c89008a00c01d5059494880103c02506155140c4c210742440e8071080c42540003180052041c0c403111007004c902c5001c0d141c020803441c0810005566 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 276659955 1250 276658705 276658717
    0x903020a050607050901030b030a031b03030905060a06050108090105010e01060507050a05150405070602010605030c0915150d0e010612080f041a0702040608030a270513091205030c030f0c 82
    0x7032070045100f04500b4560107801030040030802d0701d040240b010040181035550465990003400302e007032488540600b120602010380818817030718020407015001ea0340c203800c00d0030a0b1070702c050503a11a40140002d43c1c0083c442c980c800d8080000700302641c03401e41080700c00032040c420741c006c0c0200090900107001041c400003513659048001c0740e070504c0903600c0855400030200c034255003e008542020410910601507003003160b030000d00520060162400304038000c4005800901c680100515482c50750712600c07506201001e410b1003460325a06000003850175180040007008099150217401d0200c601c00424a0010f1904115015202c40c00214010f10360710403174020201348182c040d020b203089030b04000100b841c18030940d000c0c003840e541c42d501c0d40d5490040032001c0c004108040b281d011180034410740c090070030308001155502281c4d1341d004620714480c03e140341607807143c44031043d0382482501c410103070400034549030152651038a01c45c455424080542641c2240041401040600d14207005a9407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 276661205 1250 276659955 276659963
    0x17010212130b0108030712140c01090c060809010e0703120504080f060603120c10090203010b15030f010e01050114071109091c080601050d020d02070807080c01110f0d0903020a 77
    0x61800c02414024580c030701c08008685007031428002068003000841a100b04030350001410680f00403c1200703603090f110607414070b000c109060042d250984000d01440c0b0100f0f00801d20202194280700d0020145100181400103c0e070401080070707101c100c0095220126908042508035804811303404590038861580512801d00c01c01030b00200c1560003140301070046604030101e0b04806a0501900300d50b01844c1c81042c86030304455118410f031441a08051fa020307200900000b01c61403ea00040c01c041004038003590041000b004200c04610311120903405003c141080c00000e61400d8002400f01d06000403c00e0800e8002c9107003010824620195010000010300b80711a902d048005c06136202c100c4100d16540e83c03c00b8410441c41340c0107501c1c01e0702600040c0c0d10140b820088015a402a40c0100c8040c00c6180c0d00b045590b0200e50f184001d080c1d00e0f48075a02c000d40d00d08121100d1400d59981d002e82000145080089a4000300c8050440d0409030048901050060f014182030742000554413001d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 276662455 1250 276661205 276661237
    0xe13080418230105061b060a0207060f06120f052b02061e011502030f040308040e0f01120f21050d140903030c1b07080307060f0b0a170102 61
    0x1c035010511096820200d200340c4400c0104500c00409440100160305640302e1801050740103000303504100004040c6200c0c04040f05042c541101d80e6a40f81080858480c04a40e40c04600e10040103c1c41c0074081a20034004410304c0f25a0500c007000040020020340103000200c2c070156041005414005101c0c001400480c1c5001ca8007184201c032418181048903030b0050080360b0010303504184080000040080007440484181e091940d401001118400c0c4141544014480158944000070050024600c11080c43e03440d5440e190f0f020001d44000707082ca80b103100b01e10b00140071640300040343e2803a0b10f40002d15000c484a032401c0c402c001e445a4095007400d40305071b031003070750030a6040310083c07250307007210f0800300910311003400ca02281003c26285085181c008201190348050030402402c044040c2c1c40311040809a03241400d4603052099000d0103050b00040b41031010710656101d0b0703094180c0c0d021414810a42d82c10f0010f00b50300b0f010b014000090344c8900c11200308440c02d5064030b03240c540d462906 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 276663705 1250 276662455 276662459
    0x303020904060e15060f040806182802220f060509060103020c030910031401060306030605060105031306110f0c01060302100c121d060a170105030f03040e130804 71
    0x5019600050005000e20306103280094605402d5468a100d0070420440000c44000c0300108500c07030b0303c00c0c40d40102040c0300380300100729620301f44807180c043c0081c0001c03655412000e0000c0c60404800c40c460240305040f50310707071000215068243d0f040d010350494100c0381c8002c0400c40ca0780740c04070f100140541ca038901004586000391550144041da041150300c9101a41c541e80110180d1103040c507042e245410034000110a070030600300d0104220707018200442d00e558603840030301000d2026131288001a80b122401c1060050a1050310742100007841e0a80c91b514028124103a0301310b0140c0018003643d910300980140304046420355084d800c4840d40c29517075121680c1100d0103400d460102b640700d55480548100140d000710b031140101ca0303220500c1c50020078901400e030381c074100f120400c0c03007614108079540141d99601c0004000c161076a45406140807100d03007036295442d4050704010b00039030084603583c00c0458000182d0701294000e4000c6601580d9549020524541074400244005808140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 276664955 1250 276663705 276663707
    0x8070c03060f09031713150209121507020a11010810080118020108090d08010b0318010c03090506100b0d0e03090301150810060b04211a19020c060a0203040f0503030403 74
    0x1c60320509020350340b03a10300e240e00d612000203030310000d49064074210881c00386c50b0300003100d401d102c030008001103600606050401011454040c564000b807205a0081400c44150310b55504596130403440d644002d02e001c241d5640c0c0c500c006000f0b0164076040c049100001095429a400210050201c0000a004003801900000c488a40301d131000c0f40824031990000d81a0b00f400a8281e21081e0a943c07105041d919203d0340717600c1603102230900760310382c95040c07000402c5202c02d016004c0c045520340d03030008151109041c00c506011028001c00140160410200015420709040d01da400d48820030020300d20707400c44900b5246100320751140e6019400d1034401d034004851006040e040f16030000076103585078448111842110f00034080c40c4c0303801d04180014000b440403136600004045009140b91040b54070b070784444000035a03c15442d943e1200400c104802c1e0610380c00044090385004201f5410158141c42080d11140010804041d80d503000c40060305005c601503c1482094200c4240c1c0d0341c908150030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 276666205 1250 276664955 276664961
    0xd060515150903011d0d03020703050c03040e0f07031a040c090f0f0f0b04030312020a03020d092102030a08160e0a0605040f050d080a030b040209041118030f0a08070c03060f 76
    0x341d814825460040b01801400c0104501d404c0e104900d001b40255480544042e002908034250540403c881800310b041c0d000c4040006102921030907000c1d002528001003030301102c030001401c0394205428000320b03241c0345110b16000c1c0f02103102200c010421140405084401c1010769100039184030000500140c803400c0310791014292011600f00e5009140c4070b400c59a8188201c0c48020006044000c01d816101c44543c0a41f05c8240da03407401500d01a580c0c4803890070703204204c10603034101120480c81e158040041c50f54104030f00941c0069403c281040c54007500841c0d00a0000b800e1000c18003056100a106205039204994002d045800181d25010700801b2500280582d900c0303503083c1400411035203407960b0b590307440a83c000d10041c03512007a07035030480182a007180600e4203d5000c0c82216000d0350703140500c00c5804040001c040d104c6500c4000c025400034440d90480c026009030a5540c0a8140850b40c2171039035410445466440a5a04d4400711b030b0341c4150f1001d42002d160106220510509070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 276667455 1250 276666205 276666217
    0x60a0302030a0b0919050a060b030a02090112060b040509040609020d0f1a0408070818031b0f0a1a0c0a020612090d0816110106080607081806060d06051515 68
    0x2d2003002800c2c400c40901c1405070043d20b8013065060400d038107444013107070703030b00204d9004803070300300100d40c4950b280f00c9038046800a0308c110001d02d802080c13282d00755a200a400c441c500441c0c0003070106520384030084040d8443d601800340140e841c5000181407080719004160040d50142c14507240160504042825a1030920212159010b0480041c20100340c21300140c011034015110919003512a640c5124591000480384486482400080f00380e61b0f050240b04254070800c0030600742c15491004110105802c1100e603403140030b03018002d1101c42e070310180c4003804014107006250358043d4080520314103540703040025405100041c420420601044c41f1074010300300f0700c049840e1310365078140079960b41104540c0c2001c003d100680005403d807181a910303070792041510000034500c1d2200c503400d06102085030400017060919090100901301210b403900c0c003000300800380105007055000030311041c0c829503010303058503110808201c100c0340b803660034600200000d04030000c44c860100700080702c2d0009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 276668705 1250 276667455 276667471
    0x5030f031b040305100c110a03030f0b04110403020108060d0b10030c090903020606150c010509070e0601090e0601120f0905070e10060207050d050102041701050105100903021c05010b060a030203 85
    0x51040d1007900c60400c0160350503264810080c0c4040151712503031100400c44048104100410007450004030388080c000300501c1802941d001ca45414444c9208040d40c214501c110b0041e4601520040c0041ca484103450030f0741d40c2407814040980311000080d250001c41440070b44084028001d012210350090a078000b100d10030780c0031a003460b070703a2007417281124a10140a005a04240300084079450b002503103c40381c9410030341c0315003882d1450300c855003101c00403100300c2c80b5580311000511038500c1003c1e400758480801d180000344541000c400494134140a0000c81c103001c005125444100d00780d07004002903c0280f2010000200f4a0030b105540d81c40a00c02c10f2403c0414401250300a0314001181040d076005400411802c1c0c80d110030f008800e504080140c4a0395400d010120340c11800742503402a0349104e00000c502d81d4100000c100a49083c542102c4c01d0145c250300400058030740a1200d4590000300e10803090011641c2800340c05001120b800c1070380079a000600341c80703075501680a58014204 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 276669955 1250 276668705 276668731
    0x20105060405060619030615051e03100605030601030921030c0e150f070b04030f1206030c05010c020a1701060303030506060c28020306010e01030b0f070905060c01060305030f03 78
    0xc80041c8800c842d0140c8034030390454030400c054014054040000c01080716a40380c0043d4a550741c58402c0d0030010502c885000003500080c10541e400d02440d12007803060f804005403840c5060407540940c004102e03126a00c140040440045e10710303070283d03001581d0140c11540c107a8507005c140724822941c160011862010900e4101e50851043c072030305020540003030150040b076414180c0c0107a10100d41020150084c4000100b00c82d0000410f07079001c0d240240d1090b102c00282d0b082c1c126010702101c03890042c1c44d03a2245403243c10004100c10300c5014085030000c2c00c159651140038008610b446915400c90145131001070711910540405601c50b070200c038003a590421490710307441c0c100140b6108051700c031421607000e0038070800c105403901444002500f00d00041540b5002a83c003082c1003141c01d0b804454540b000100410600540d116102e6001054544c10465403800d800c01901c0d100702805000c0c0100808252425000c40c07d500010281d5004011691036003c101180b0900d5401181c030040e080310 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 276671205 1250 276669955 276669961
    0x603140f01061b0501060f0b0c060708060102100b0112050103050606130912030c050c1c080601020a12110f03040b090111030f030a09020406260c010e0901030b0a060b0c070303020105 80
    0x5400c1a54506a545990300c0c02209495980c5140120780d41c03401c01e503540c0d5030f1040b0006210444002000041c01160011900e031045240c03d0790804100a01860074400d90004104850f03078007140801c8406100040000c507075442c040100c403070145a40035080d400e4600070010060200003d05144201c13000c860a03c20004482c075880c040d90146440105080d040f4900740c0d19150007504031900342c0005103003090034004e082682c1440d10380b8a00c481940380407504100c0c230046a100d8480b6903c69030a000a00071600e66a447c14900f001240004c02002140d580c03103002e00005102110140074814105e03038030f503510b401c115809a4480d0848030b0110f0750101e003048420101005590302070200c0103010b0b007541c2d100e010765000f400e060348040780e0050b0b80c0e84012880d540180c0c04164401c1c800175003180c0c61502030f24001e00c0c24540c0010310b814824020b030803611a50f40c0d09400c9064a0f805404540306071203a5503001c001d080950007401851a0201f00c150058400142d0304003164000d5000740440c2d2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 276672455 1250 276671205 276671221
    0x2030d11010513020a0b0c0a0f0602071106040308181c0302071403010e03040909020310020d05040c14060409020f040e0f101406040506070c15030209041a0906010c050a0c060314 78
    0x1003c0e0002500510900e004010325202140941801d00e040429120111800d58900034204407a000c00c0301c840c0e0f07000c240d410078085c500e205100b20b139506a4030545001d00b1603d80322788600030b215120802d0000d1440c1e240450720b41503140c00c0030102c9005208000061454080d40700c00081c000c0e960200d541c00c00b00901458140a5000b170078460707502561403c1d0804c03544401a02e15110180d8043c4a004804c00c495003481c070041c122140905000a548d081c01c0c50103400c40d07000c40e406260008003502c0c0402d119513640e0120790446081910060b552202121014480c0c041c80d48420300d0b08408908100c807600402c81d509201d62102000d05040301e8582d4110418250418404c641015041c0828002403c01340014070034a801303842d0174880660754040e050303541d070040070017040000e030041a224090b080c907010300c0d40d5808041f0078180010003061701182230f071b2400610260400c8180700b910030a120050064002d46900300300032003819601d40380090050f005070043c0000203000540080e00c48 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 276673705 1250 276672455 276672481
    0x706031407080f0c0c0a11010e0102010e030d021b030403050c01021c1409031c2a081e070c0306021201080d090506031504090c1e06080a02030c0702030d110105 70
    0x107180035260036003141c0790b801c007440005100422000760a4410444080300920070001c6018040c4a0b03c039010207200b400c0d0004210012400459055a043c82900da0302c42c60044203841480843c2080103859604068806080c2c5085800e40c040a0000240c044140900803078502d149903403e8003150341e004401402420001c10800d200750000e000c01c003030440244903010090845480040807510010389034202ca2404800c18240d20740490b02d14201c2c41922103510001c51244240003115640364442a21040058443d030424415041d522800c40079480326902e06035800c1c290040c40c0d2031219170303c9181080095114415803a650b01e88030000091141c00081c03005441d4819170354078094903140c0b41c01c0c412103401c09850100200c403030b03960a414503101d9104041d002e501800003030401c14908042540c3e405004c02080251b41d8903031405010140c0c20903401d6030400980640185c1c0c964450a100030f07107010b52400254103005040d94401c8a1b540175920401e07080107a40208000d490301c1d0400c42e01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 276674955 1250 276673705 276673711
    0x2c09120c0c210a08090d0b07030c0212120609061906021b1e1e180a1104080715020a20030d0e010f20030301030b180105060a14010201091407060314 65
    0x425441415008009642072010f0070034200b011b0281c404009a6980303c2000e980102c40540000790f0b1401c0c807010356507041110480054518a60618069040c800c0701d080100041c41580115400d002190341c03510b41c0b2555690110310352800f060b0003a05c0e43c4000351940c50b0000b04608071900c1e500c41d08061b00d0080c800c03001094220982107510015401881406807019003070480710a00c5e08049074080c1c540060000c140440700840b04010b180c2024100c04030399002c10500030900f024001030040f090002200015200341c05440c01a2400003802203250001d0b40c04018030015110700d0f035110310038030f804a90310040811000e40e600002e030100c2c1215008101d1200c02c0c00501c00142520a00e07000701c0c15042c4200a07a070307841610303590141209156a1007a80b0840d07500c2405420440d14241c11030030010190740b150024408e41c10000f0000f00c82002c18001e103280c00c0302c0590002070701e078000d41c840f12045030b0208040030152440b0440d561103c6030351150801003801e101e6200c4a07030140398071280c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 276676205 1250 276674955 276675019
    0xe070e010e04050a0b03070b071b0620101a040b0907080126151f0b07080309010f060f080c040603020d110a030f0c0f2c09120c0c 57
    0xca500941d0082101819016003007601065451456150f183c8091086070b020700006c1e60590f581d40194a441213514600800d003001d042071350310040c82490f600400740f10408030f142d08035580300050311109508001d009000d40480c60301e0803007a000180309654825500e49821501080030342440d82c14808410b1003158030000061101c0014415a518030000b80900c4800c1c03d000351031080700030200c5240c000d802c12846010703400003007081600b9580004120300202d4030f40500000500c0c2c50482c5d2014000c064006004400100029021000940c4070071003080035550280100d950762079500d000344d030342e03801440440e02450a0000c000d040900407001201c0d80503003119800e0030240c03220705001483c0c21720160f1181d0740c0c48000003c11000c0450880d6107028070a006217491400e0f0803040340746074640c05904280001440171741d00d0340480401c1e8955901c030490b5844a9030344c4120550806c1001101a0509803001c24080b40d110400642d491140c081500d85900510310034550105600900050314 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 276677455 1250 276676205 276676217
    0x8070c150e030705010e030d0605030313050f12060712051b0d02071703010f050a061e0c24050f0601051c0902031504060209041413020f0f09040308010e070e01 70
    0x1402194035039100500c0c0542401c152400c3c64100d0703484c0d0342500c1e55603070381040d668000f00320360041c420144100c00007000214000e610304440d220030981e48400c5442440d100d4190340c844d0410395180d100350000752803401c4003580c0301480c1c800c0e00070b0304900e543e542c44040d02c0e1138503002480180c0d10003446034440038400441410003280242c414065800040100c0b00c1005000034242ca07944810081c6002e00841810740b048541040300303200e082101c0782c0c01002040304001c4103001c1c0e101d03950014a0749003260300c0d103000481003904021807071818021041c5e114205030a9403040000c5158811400b0b007200084401007619031100441c3d490203400c004642000940c0410200080180d00002c603a6201034250b1b803001012a4a503121040b0486050351907030b4001a810940b49400c0c031030816091810385640d07100b8240f100f5040703000c2085000c02401000c4e0295500d1060780c03040f03085a05041e005114042500c0c02e8a0014641c071000e110b040a00703d10140481c000e0740c0500401c800d000e2044c0c1d46c0e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 276678705 1250 276677455 276677483
    0x1090f0308070203030c060c070501150509060909070510050a2003030f0a0609020703050d0c080c041a070506270a170a03020702330316050a12020d0b0108070c 70
    0x207421036901c1442c0403a0b051004100c54007200b601448a90700c00d185c1604220385500c51820001c6c25545010f22020014041c0e00050000d036840040c030540000c02942d8800d00350f5941002540b40041d940c200c02c1e0b0207035000c0001c107a104d03401802040700302695981c199146c91520708900108488a10701a8181c001740000740c10325178900181c503404450b118010404513503440340241268042401500011000100c42d07043c0c808034050b14001c22114540040e075841c1c544000d030340c07601550260104003040403514180340320503c01529401d94012080e0f84180c20001e2402407600031143c8045d800c3c0c851000c4402e0711003000f203410111140c10802d9a541141008040d000590013580d00d03805040d828404400982c44070711502c0c0842242142e5911303070400010482403010035031000070664480420402c10040020468500d181407a4248180c45251401c030643d030511801c07121042c918070105100322801690b07003003814502400c1c0c880c414203403180300c011607080d100000091300180e111184 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 276679955 1250 276678705 276678713
    0xc061206081504150e0706030507020c1f03020903070902070b060618060304020a03080a020d0806120c100c1a04020108060103050405060619120309081204051003050a0204090c08090c01090f03 84
    0x154414400d00b0604502c1444e6280c8034112040c07404003003c1c55010100500001b9014450590000042d0005108003410100010b521007a841c01c410a50407000840d511418060340554140c140000c0070381d0805c40d1a204d04500940145d4400e483c03000002c004910309050201c1100c800d01c0790101380145d41003024041c0203c50380050812604030030090400004108a840580084101d81e030261545451529008040b000040c0070b4502c140c0300800031311014000020900001e02c015a1340010510090380140c8008454200140c0429030050640c004903445941d5a1320541c800d884001041e11004011800c961044400600580c40f40d0045080e42c503280c1040403850f404040b0441010340c564517100540600c0c00011400714a1151062006d80001d2108440c414072050300d03241400e1500000a01158200c030541c41450f50314004154049520707011a4041c1846100a00010104200003410f500045440d82e41c9802480300400203988540605011180318040c2c0358030303060964807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 276681205 1250 276679955 276679993
    0x11070b0f0c1002090d08250807020406060201050c0a030f020904021603030c02070e061909020d06060e03031306081f0605071b1802090303121510030c050f09030109020901030c06120608 81
    0x7000c1000200c51f001d41e01c060529509105002d116000060301c0d8002c0b80f040c80199480c6801260569040c0001c11901d000e0940c161031454045203404205054001800da000b82300e4403400c150090300001c0c10010b0b040c1c540d0843d844a61003030303404100c1042d004004a840354141e000e0340d40390360540c00110b1f981d40f4121006480f005010010741e940160b03501c09004c1264800c0145404060f181d07030003040303000d820880c3c0a4400d4410340155151500289510034090703e00c1c00b03042c003401183c001013204460a5401c40111801c2c04041a50b900d450350005081a081f400044a0f25800c40c0e03d840b81c45001004803c003100c40020034049011458011540650090300d146a0141b005011200c0604400314100340540c080099074203803914401c0511000c80e502c401100300b8541015820030011307902c41c003103640300c1081c164065280c0c2c200200190241950038400703948130b410f8a0022044c864401c00c00303070841d0b09a0325840c084581e1109c1c10b0b020f440d00d40c441c440e00c5810a290305000b0002ca10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 276682455 1250 276681205 276681217
    0x30201030f0e0a0c1706160f110f01020301030c0b070c060806030a0609140601061103090f0d02040c03050a0b120c0402070204060503030414100c021011070b0f0c1002090d08 76
    0x8240403646a80c9108010f00d00394202c8410b950a12814070104610070201c43c55403c0d564004010b042c940c1fa20311b0780c00c807031107400d2842c810420052100c0700c15041d10661040715039a203100c0694500328040071400d8044e400030300003030b1407100c0d0820380007400b80b110b6001c541405900c40c0e19014140d00c0d20b242038444240040c0010303014010040381200043c80b1b44a22402c80d48100b541c048039541000000d460110140c01001c2030012400491801c0c910010561b02240b0301241c034500504440704c00304400c5862000000d42042c04c0241c403d4110386c160300041c3c403584002c141002269070580400c0380301c46041d015150070341c2105180034018100f0380c00509210380060320200e140c03031343c80005c40d00d940d00036030000c20509058921906a40350481c04c110180c01249411400140b01350000342c10505081992001c0c403041348600560385c041481804020181422100c0d221843d9026030402e0394401c03003080d41c440c05049036041042165200755046188041d014a144820558841c00258412 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 276683705 1250 276682455 276682481
    0xe0f04060509070b13030b01050906060f070302030d110d0c02210d0b06040305030a020c061206130e01060915090203040819050909130201080603120904020d0902091015090f03020103 80
    0x107480c02184c10440180240300c01c20400800b02d079550b18604009a1b000c4040c0c10051180310ba00d8140203242d0384450640d6010014040d0030ba41d039900a00e0160b1a5100710780c06112100d082000c810502034082c00509014161000144801e241d02842240c4848540c88101c00d004800c101c07510207942018013802226000c01d90008413040040000703a070b160420f034003c464650000520380940c0340d040c0304603c651030059a56504241d06110368078082c030002055940100d0680e41d81242c0c01c00a038100d841d803543c41c0802003260750340364145400640f4075404030981e0316400d402c0020b50783d511031007100e00c0380f900014070b5403c0a040d041d806844680403040300c01007100074401025156503244c0b1031030240c0c0b0f990900154024183c40054005840180b85511907000742014001030b80001084548200040341e0040e0b0f078060244131000248a000806504043c0420800460510368038190003503426985401e02e0101111800316402c40c694000c00002c1a003142e0100010350007900b00c0d500074084 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 276684955 1250 276683705 276683713
    0x80d0e10050a0e0a030524091f090209010e100501051201061407060e030307030506010c030e01030f02070b090105180f0c0108040c0e090a020109060212121509011401090e0f04060509 80
    0xd800090074413541e40c00998444d00001014800d03902c0c204849401e803a0740c1c649900701c034a0645e02060300c4e41e00b0050124602004d080d01c1098421a66001c000403980c01400c01c4403a5844402c550741b4144200c0394180c010100c0c0001040c10b40c01241036030505078171480021800c2c3e080040c2100d0720407904030344001c203030014401c1100089160103080140c05444008540701d207406000103042d11070103007049043c05600010f0070b0200e50700014030340c8204000c1c00d01180c0c05004170701c404d0003482803040260140da501c00078090344d2503041d00942d0107418000780102220041d04821526010550700400d1190311040700f48034554050404550f006024260301401aa600c6c1010800b42c0d00481b81c542d000e40055421104540c0c2000462001d00301e944000c0407105c0740d00814500c14401c0001000e115080c00300080e100b01d25415a005001c1c002903c0e011711541d56550100c280c0f5a020001c1d40481c00e81c035404911070b800d400c4078501c0754840c51491525500c0e0303a1500801010064814052402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 276686205 1250 276684955 276684977
    0x9040e0a1202010506010f05070218071211040806010e0c04030f110a29031b09040209030d05030121020901140d020301110703080a1515091509080d0e10050a 69
    0x80700301c09095100740d40002c5200d242c41400188010866003440040c410140070810141e01c03941425286d00e60700c00070340281625003000984d49202190205251030781080a22030358041c124018004499440d000c90f805030362203841d10380c1600011140400800c0c428001000412962007e02880602a048000c0d07514801030102d070032175155820072070943e00d403603c4844008404c0344a41c0344000c00d8a80c51170640c106400141c9180095100000c0c0c00c000c0422013101996841c0d0442c5d100c004001c1c100e540c035203030311400a419a002403155078542010000034488121b404140d031031101d64020704072401c5070700f080420311181c40b0440002ea003001c0140c2c01200141c40911401481da128419801d84800d0585001000820010320060b0b40c41c1c1401c1c450340141e040724580e00c2c191900501500c0c004010040103d880504560040600080700c400d204005078001000300c0c01d5654143c252694401c0a800a80e0075820628480780c2041211117481d5410b48200c0c041d00030050700745000a1080703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 276687455 1250 276686205 276686213
    0x160f0f0806010b120406064a180705040903080609010801020703020a0201050a051303060203150102030412080318031804180b0a1d071e05030d050904150905070e01020c0303040b09040e0a 82
    0x3a00341c0034407108802e40700e6011084600180b4698682c4880da00b0020b010300b03482349042203035800240c5210003004120b101d810200c20240021130180101400400c00c82d0540d050080c91040103660780e900400c2d5280021503400e1040c021550b65907059002461205100e0f401103c60b80e12030002d0908010007031140000c0c0405e40b40c0c102c0c00031800750001607281e0520301105e40541d50001d107090706651042004000d820b69081b0b60f0550240c100c00300300e440e540c505105092200300c0d00640c0e00c0c28080010f18405c0074525005d000080201038504004149280b002450748040e0108050002801c0c8000110700b1501c80d04001e107110070985029107a10b40380c0c00c10500d8801d440d0408a0700040140b43c0004c4d202c0205004001414101c004214800310b600d0702030f003241b182d0700d2440d0042d40c541c02030041424070f1018180052559410400080c6000c160003080500b95580090050003200c00e5003e1030702c1c0c00030607141039414202c036a918014140c802c01006220320781e9500c04c00d00425441030042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 276688705 1250 276687455 276687479
    0x103050702070e16110f010e190507051e090717060a03110d02060d0f02040e0a140a0b06071202030c0d030c0f11010e030304030801140301021e0a02160f0f0806010b12040606 76
    0x801c0c2c00740003c0f07236000722000314034208503044101c0481444000c20344d070040b4600250b041d003115019505043d41d204400300c8078441c0038100c4c0410750042c40031400e21081642c86000715000111a200b01041600c6890400000c04012f200c0a41100400c1c60300361003610301100716104842c030045c8143e20b8030784903d00c0752081d240c454000c8291542d010400300568000300c04600c4d403020380d240702044018600c078601160704c0006000a402580e80d01e135603280d0303901e0301e1040341c40c420341000b003c078410707022000300950342da00a8500d40200d0003000c0c0b18545480c00303801a174603241d189485061070a00f80703d10841e0784000d54000d02800e9901c5000d4240880d40038002180a580039640b103100d250305203111100ea040c202c04000b40241c0c410840195107503e840d02e0400c00410002e038040c0e40b6040910101d107800000001c801c00030230040000134105605240410440b00e1851600b18040d58405801d519020300748200880d942041244103121190b000000394818030801000400c2078495800d4500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 276689955 1250 276688705 276688723
    0x504062105090f12070201021f02040b040311041a090613062301170c0f0721020102031e01030b0403200a0303060f09051b13030b0a05060103050702070e1611 69
    0x100383c0250010200c08001403100c500e040314400241c5180080640c0002d41e03e4440383c003800d000a42240c4200780c01400d90b011100100628400c0540b5103813a030030160000310080291503c514913010400b4418880a07140c0503200100811815080c3d491100303208801c1a03010b004802c040d0f0706d0002242440c0070182c2030b01200150040c0f0310682055000240c24040b5410050040b480900c0070041110400411519a855a02c6040f034a9083d20701e07001d040c000c0403400e400070004821202c565441e50541c055440340c41441142510b40405140700307000d404007030202070001550b40c4002408a8003500c066084900020044550b48510a0005040401041040300040e07143c00080040c100c00c5040740010340301c407a400704510b00748889800c80e1005a00042003280c1c00102d084507440c210585c00000842d00206503200d5407601c03080314001044100c9105021a1420307001c41e92140c40002c11030240c0e040003241c40d03407030348980c01e0403844242d00c040c0400c208a001d469039400c450701800a402c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 276691205 1250 276689955 276689971
    0xc0c020402070606150203031b0a050403140a0c05120c09100807030b0a0507050c030d0b01090b04170f03160b06190305010c021506060909040203240702060f070504062105 75
    0x2036484d04217800b80d0011010201c11500310741c0180280031003140f03441160041d107040d07680300710760300c3ea0745160a6415000f40c2d800074111245000001c007035202c011408000452181c0180c66682d520340f01003080800180040c547c00754050350760055282040804190403086000d42c0f09040340d601e400301031608280b60411103220f500310301072045c2d6810b24090b0702e0308800d0904155040040c22180d00e0796a00543c0c250f49015501c810507190541d00800d0400c2c00340c00380407c0d89a496842d12841403101e4241d0750310840c584582d5a08107460364002c0251792080004540410b944503540d103544000f14000740c050340d03100d0b0b00c071003107000484156410580118403680001c5010b810850f8040e0400c0002207030f40440006110400115035140c0e800c940c0411000c58002c600e5446a001081c609180b00e0010f0510000c00f144e1826502424003400c0d01c1080d0035821541c0b29965000c00c009400e20a9900b1008148103000c14441c0a004000234807a0180e80705880b40504903016050055860507941d40b8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 276692455 1250 276691205 276691211
    0x2d0e0a050f0f070e1306060902030a021e031608151c02030c030606030c01140c06100e07170604020705013305030304050303030a05060a0305160f0e0f06040c0c0204020706 75
    0x5481d400342846107214191449010b000102d241540500107a1070041022011078a0400c1110801c03a0b56803146000d0044c049085403030b860203900d0103001390301041584880440294501349803100210859100302c072900c607665484540d40740f007070f40c80003006043c042c1e10142c2c01484184036120084a591031401c4100048180c081e98010300d8100000c440d1410301a401c100304001d03185e01e002604599262081c80c042d1090100d1041604190081100c05820343c0100001d201060110134002d005440c055010383c1601d44440d402661001807003007685e03018182541c001560f9241c10f50150018a0003107001140e10307020f03441c5a280ba0704032200d4041841b006105090905018201c0d0782c1c020b4081980114905410000040d540e804000d100d40380c0d42c1c1e140c10015400d92295a4050001e51f03004003100d0340b66140320004602c0d500c07280180341030901c485200203901444802d50300d014040400703013810141c42c0e4105101c0600140540401400410800b15005032103d00c000c0210344c0c003441e000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 276693705 1250 276692455 276692473
    0x2030f0d0e0f100c08091305040c0801270623040606031e0201050d0c02280b0a09081801210e010c0c051504020a362d0e0a05 55
    0x20301107440c400d015103c0c050301c40700c0850300142c100c1e8070f00343c0142c0306a49078aa400e00141c810b10300c254000c84440c0c100010701c0304210400103104185d44440c0000d0025103001200c0801c1280309140303005c0181008038501010440c603910428204070094400c65000700c0b4485454010b20703040d04d088030703100e64a00c802c0080c03010720f2503080d403a000240030341c440d0040b090700002c0c058010104004a03440e030760a20040e03c0d5000300400c40c50175001c0312020340c18005500741042540420b08050711507026035400100300801c0ca1050340b09681d4440c060a007000c6521034440310000801a00c03d0502046156000b0b03c146050003440070051100804106c20004c44007403400e580c0160710440c24400e154540b240003070404100d40d014909000700c000b0081c1e4031800001c02007845c651201003c000d07000089480040c811018070041480111940025103042c605401100c02e200c0c01c00d0243c000040ca92080c0010014240011a11402002c1958110a80200d081c501c000600700d03125809540300e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 276694955 1250 276693705 276693709
    0x80c0d0507021006050406050a03030e12010914060a051006031d06010f17030702010e06070602040e0c040602010e0c01091403241b030402090105010507020126010501020708121602030f0d0e 83
    0x10000600300580b1b0600643c1d00c1c0c500030a0501500e408014284500004400e00d180c4818101d04403001c0b5400091211000c281090020920200000081809000001901190607008050140100c0c3c0180710b40185410700440007824541501246104040c0c80344440a5040013003502821110985038011403030503180728146c10000c0301d83c0d40c8a400038000807003d80e07007003244000040c00581d034060307841a0503c2c201009100b40d0300200001c0d00350000f40403141060b0700142060310710701c0e0020824240b489000035034805a4958450015110290034410203188103158204590054205c5401c61401c0500d40c200b00310b165252080b0b04941d00030400c14003660428000440e40c0d2441140c0345040c030742c0202d9201e2105000d0b507810701030002811800c40e480b07801e000140354441752240010800908149540c80802c0c0305141c0144501c5d41702280030341010405e0b84140c0c1a0458152400c8111200284418200003059905014202075004521814842c0c08800103499803107282020301c40003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 276696205 1250 276694955 276694961
    0xc020a0c0b0a1715010507051002040b0d050f0f040210170108030a0f0804030f0c11180402090601031811150c06010f1a09041e060803180301020304050706080c0d05070210 75
    0x1d41d41d10941202080c8903e13001d90152a400d109001e00e0800d030360f45640e003030080c0350940f16071231034400c144001000180040707000003804103208a00802d204580b125134441c982006e003620301020056581c400f20700103107030040c1c03118000c41003414076180d001c2025290300710300e202c26884000c0715000003540b0860380350b020244005800d91030511500301c0c20a610000c091170700c580035802c18070500d00419000d2140030340d480c1d00340c01001001007450300c07100f51320315001803015138003207004802c28004200990b004e40070b4022684d80d5440030601d080c030b6648494480711501030b11141c1003002c00c40c9528005201000504e00c10280748010911545050007441980401c1d60250b10b00752101c09002000350241e000701c44190034211008103200f148151002040d01034a03d410f04203c0c5454000604050007001130104460880e0706840c141c4c801c0010316082c2c2c402107900503c180c00480c000e10a00c0d0140e226143c000111080050500d044000180121001902c1c554096032056044a1900600740 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 276697455 1250 276696205 276696227
    0x605040203071505041203020c04020f1206040216350a0e0d02010c03051305040204060c051006030b06120a0503041412010603111002010f05010e2203080a0c020a0c0b0a 74
    0x103c03843c0c3c5902e46a00024618002d6001d1040140c1c030500840080c141f08110490460400a200319681c00740210120b6044d80710300940d6500000c0f0f00c0000d0b00510300340c400d56005008a804910705109190340e51070301201d001c51004003841c12851075912641c141c8207011248a503803449c1995880355003802504607200441d52502c603000ea20003a0005076440074001603015490f042c00c94031150708107203070486d09140741c0103150010b1010038006411640300e00c0d0071132464040d80a89903171411129101041d284a4017010305296517417004a10f850030070281d685070038480b00059885c400301d00c1d0389082c1558050b501c080d00d55040c43c600c41080d450621a801450240c0d04000c2001e9851983d42c140b2040300c03121080d214402492100c2c035258003e4216040140c43ea000030005582c40d0b42071584664000c3d56541d260160280c0e43e181c0c120340c0140310540c580e0b05174071041d04541d180304810300600424458201180500440c6c400050641c914050242141540d015110760501e20000d14001450b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 276698705 1250 276697455 276697469
    0xe0f030d0914010c170402041b020102031509091e0a0f0c03030f030b031b010212070b01152a0c0b07030801090f090f0b09010e030a050a03060b0307080708180109060504020307 77
    0x640408402d17002120b000300c4c9110641c0200040c3d80300d00001c2c00403c1081001d0812038200c0310391403103e9078194000c51040b5407500e4440e4030910840f003408007808040b944169181d01c01030104900411101c603075152000050100c401e1180e540d91003c051004d6407000301c1e501440380340c0078420990000c291345011201c80c541000b04110540000b0b0391602d54141d048040c80c1d50a42d49011039209100c0c0f0408801040c085a0350f84459240076000b440007480390000700e0050b5000b01c100b440c411352003041d882c0c0c180c0059002c4500502e84102e510518403408035071506c0c407004005105032000700540a0702d4040d4a8a203010340c9015440002d0303403c0c0032111100e032840c0c030b200b502c001945034007131803070840d00301e00c03800740300d50f10641c3e52401070842c01810030403440f0109640000340e601c80001c082c1c0c1900c9640602c0103560307910b0042000e0006817001000306d54800c0c0000c5110348200c140d80c0d0301090825510892140048000307085400e00711090300c040c1d0b1204100819030a04002860040000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 276699955 1250 276698705 276698711
    0x60603090b06090a020f0a18060503060102070e0703060f060c020a09020f07062012090705031b0907021011070b06030a170a0201060503150a0c02010605060405040e0f030d091401 78
    0x4541d61a025208014003081c4140402000f06a4a00940d41a6840202604600703030ba28131803110042e22905044030300d0b108859910344003107092480740050f6400354106800500c01142801740440103448010000420580c0d5000c00055560914424000404654036008042075503070040c803800442d940c00640315a4010021018980c420384100e07112540c002000090011849010601211244c20381922003a0089040c0d407280c04407011850054503400d08582046030344000b4507440b50201d0103d6071100d40d803402c41400070f040c00c00d0a240d002c000792042c1c403500c0400c40c00c5d60781200c00da00040c4a801c0f0002c10244100424190482c7d04640304070018003010400790341c3d614503020190144060708501003200340303c641c000d40148002e40002030075200160625041c0d50180e003000c942c0d04040c03030300b821f00c1c4000c40360040c803c6009880001d004c0514280c01d180901015110319017010240b80b040c1241c0c00ca20300024030160903013103182c00c0c0100750386546052846544243c100c584410ba45 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 276701205 1250 276699955 276699971
    0xa2c0907030603050c030601150c0203010209060408010c08090109020109090c0e0a0303020d140705252304051503071406040906290a080f0c0c010e010b030607020c011718030706020d060603 83
    0x8009d10007403400c8078908644000c107030b0f1010030b029002e407440c21600304102280c0800c41c03074410b4001410007a456900e4042d00c0c0d41d02c000007400d81307041500c040e01140141c01c0030700a00ca480d801910100c1035a003407038a0704142e840003086000000d130744113800682000c40c421070090351051200c1c0b00c047c07175000c1040c10708885480c1e5030f441c2c12403e460700420a020003da4481503400d00122001841500c0903002e040002007102201d50360b01c042c005114a1904000640d1000030145e80d542440e006801088440e040c88400083d60002008107507101070244800501d11845001c0d000c06000180d048025080010122041c013055030340c1c2c002e10400040c4240100c0b03503806070b40c2990000d15401d20000036151014807a4203880b8082ca103203107550030550700302030550054202c24001c100c2a001c4403003a941c0c90b0701c01c03a101c2151250720390000d20000700441c83d441c0c0c2403003529000f103001380c2d2403d41c0140a00045140da881448210b6203130b40c003c20301c1981e02c5082e200f540000d10442c181031003030f04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 276702455 1250 276701205 276701219
    0x90602070803090a06050606070c2102120115061d0427060b090c030405060c13090504030f1701080304120203010b0a06081608070e0618040c031505060a2c0907030603050c030601 78
    0x1440e0780941d001c02f0b070210040c2200403080458228585030094504203014603080c141d180070707012914406500303010400000070308610642a05a82030108100b00886012110808c005407003440681c08841d8552003000000d908071180b10080c052154000081da040d0103801d00000b2a8018400c3d4400718050003000007184010032096801900f11040702e80e41d540782403112a043c01c494028944281c03500d010801015045550440c3d0386000741c0311843e652024140815507008240a80680758006000130400d004815012004071440103001051061030702c008030701d4610081c0c0c81400096140c40a00180a2544855040000c0c16103022643da2034100c001420300301e402600b2a018401c00515200c842105004410344441c005005200c082c218003002005450240c000621520010b200010145010000c482101030a91030386d910503020100195280d44500c84881a4501d000a4180c1d40b42c0e03911102a2141059440001d951070460070718518041a4940c024026800b41d80140480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 276703705 1250 276702455 276702473
    0x20909130812040f150203010806150a0603020a140a02030405090f01030b0411031c08070905010c051504080c01020a180501020f2109090420010918090602070803090a0605060607 78
    0x520b02c0d1a0b440c105480c0d51400380802015000050010790341a00d180720025082e070000c6048480341e02c103c407440e0310344a1900000400c14076013035901c442107000030803003507010f600580050461824840306251072035020320b2996001d00c60001c016007000900b0302071842c10788a03e0790040080600b0b010650305665420348030031000f401c00390041d810061108143c1e5400c02030740da800c0c54000c580c81d404006030301c0d02500306c404c240c3e104004200115800f1400d548111200380f881034000380200340701c55071815201d07000c041c00703801611850f0f02040304020703200c401d0009003103050700c543d900000c60840b0341c1100c016420a420590454200b603a0fa845902e0000602c40d560081200c140400601420145c0d40340d4803c10222a4102041d4000c100502ca00c0c1d03240708e051817011050000c5107030380d070100440d1610707103074000c0c2c0135062500f0aa030641d840082d40010b280742e2150301d0042c1380c500786450f00741e01c1d031704211120009030348900c21b07203c100400c7d4011560880026100303e0b00b80641582d8007424 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 276704955 1250 276703705 276703717
    0x3050c031933031707150b04090b0f06010306050402040e06090c13080a060c0513030807080d0f09140f0a140106030212030403030801081603061e020c010209091308 72
    0x410349400100100aaa01030001128420b010b203040140351a4415968001c0103480240c440d22041414601c0a03000541142d038140d90148440b803610202d0500a8020541c80c0b1841350456234845c068800075807000e01c0c1d2070051070300c4102c1030640e01d44407000409844807030b004640242d0041c081008000481284a600114100d820300d07155914255600000d01441c99182804420988002401a004035170000c18502441e4240062405803009540703a20800e44272400c1c42d440c075001000800c0f400e00c054038a05201d200064a4417500b403504006852803c0b00c44964103549010000400ca5800b540031f1500c8102000341a520b0113101e1003039140e030941d0340003401d0040c004820150402081d4409406035500420b6815100742c1104000d541c0c0c1c205002c02c9000c600010b0012442c4400000d100d074114038289983d09466085a0382d00e400341003120074408040d0741103820003a0280ca0350010349650f40f8584c0005032074154440421422000240601046050b000c1d038a9011035040d000301c401c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 276706205 1250 276704955 276705001
    0x40b09040207141c0e180402060c012c0f06070e0d02150a080708090105010f06030903120906020a090906050d060c140c060403090503190314160b0103020103050c03 72
    0x6211040b42c02c20b00b800c1e030a44125903002d40151161042c107840c10040c0c0400d6000b440e643c40760000144404d001c1d0007030400c0314034100040c1200001c0c0061800038011724002500c0300c004111012040f429140c41e2100016000004010800d400700e400410003098602d416020003c3c01942060304014051102a041c3e0500660304110014155110540390858a044080c91070741e07501c1074528010003d40003990001f00140e518404070349010707014060745044e00c041e003500e040c020349400001d8000b814803070710440920102d606083c00042c002d10a110400b0f0044802507070b01c4081c40401060312600b038006030074091a00d2014452515100c0300700d00742070752001c00010042074880342680c500c01400040c4c41951400250b1400039075002c607034640036500ca9241c9038600c580742c1c0109501c03540c0d114038130040d00b947c408211010921440301c99000c58280c00060b4034180c3c50219100103003590800542e000c50040c00108115685807164551010b0080c40042c103505150b4126045450301c802050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 276707455 1250 276706205 276706207
    0x10506030c041706040c17030d0f090b090a0c090c050313030c080f0903060f0606070339050c0d0c03060203150402030a0f0b03030306181005060307180803040b090402 73
    0x284076040200d0458019200c00f0a00c0162281000c800c15601c900859007101d900d4107001000038550200c0d200841040442c0b400382d81400c3d420100e0b1002480311030749440d1015115035001000c10300001c0c405c2d0240040b60080c0c800f0f007000b0300304625008600c0d400403a5403842d115040200c26400000d40390040c0b944210010b03030b141d440c24102e03190480050080c0450700e000601590f2203080c10001c03c021a03041d41a52403540c0e914002c21280d400072603806400070b90030017040c5d000900c640070811140400000180000050594158040030358032902c1d0980036800d0f01c0c200500104018100803e442250030f01001c0c01d44c0c0e51000002c40091000030601e58011010840e1750018040e00740d1010406001151246030004c0c0f4600074003a1101d2a902207440c1281f6088a4203000c4110303032003590080c00404071035511826803618004000d000e600064034041d000320f4166180001540641805d0382c030034a5030030118000140401044c1e00c480c0d025402084200215901401601c5122404072401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 276708705 1250 276707455 276707461
    0xf08241501081009021303050d020a0809120f0d0203120f1012080c1b01180f050d080f070f030f09060903031b020a090c17090a06020705150702010b0f06070b01050603 73
    0x120181c0441340c004000160010401d01c5011103520780c408200c9000c1d004440110940101c00d0340c0b101c04000000e00703281ca0070484030301c03c0d04140021207030301000581224017400300a02d0550800c0d600c0c0d4020001a0070001c0c11040d43d140081c4035035000742c22010425607a080010a0504151540c41051811840b01801c0030920003201e040c0d41034080318a00780c03070010b0040c1038030710b13851b080c02c5c0310707007808602244180d04061141480103415941d4090480790203d04090422007103403010f0b40115007041040140c1d0310004c508601030142c1c0c3c3d1080b00680400c50403860080e01101e000142c00c801c00c190789404001d0b01d94803010b072a0881c0d0b01800c2603803220300c551001c43e0343d4140102c03020750806041c0c400041c1001a030741c032030400f0385210b41e19095454144880c1c629480410340f24002c580d88142444408111a41d000f4010a44128100e030046e8001458031301344280c0840708080541d54925004015003003031112481d4a000480300c071803070b1400b16a286a2005010302450703000d82804400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 276709955 1250 276708705 276708721
    0x60902090303031b12010b030106032f0c03070204060306050f0708040b04020409030c051e120c0a11030a021906021b130c050c010608010e0c030c090a020a03060f0824150108 76
    0xb101c0e8170300c4212412490310742e103560341031415600078804d49002900c2d00d00c07598404580102c4c20390942c9603410b020745038581551800b130a10b410070458a869408100245801a0382e5882160f0045108107000304051501080c100310b0340200501c40410300c00c03c0d0741004006100b1041065225a04550000d04810f03207003411541e40529400050a83c400d124008611130714030000c0b01540c0c401c1000302d80c101c04560324101c80c0c3d40030b842d0714901558800444c40d00065042d41a031003d0001c007070200c8040300c0558001800c2500c1400c0d120441074107003d42480010341c1408034010000340d02116603030790380c810008240070311400c0030400c0c202942ea6090030b20f640d200300101c0f03900300301c041d00070710580762208000d50091180e5840104107219a00d1010150304011840d01240c42c0001c0a98182d03070740d1401014042d522450000f003c166440c20b001c25880c942d60b440c003020348000b800a0040d294000007072a0b1020545411101880200080003001516a030182c4021102840c10070729540311094 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 276711205 1250 276709955 276709957
    0x816020a08010906060501020d230c06040c08061308040306050907180f0b0a05030d12020c0a08040e070e030304060c03030f0603050a020a090e03160f05100f060902090303031b 77
    0x100035805400c034100000e4084054100c82c00140c0191020492640d40b00c0040e81e4405d03686030f0180204418540740c01c200c07282c1c4240190070a44030b860340c601c0c003103808250500b090303000c271002c07104280291400e100c084010050545e00400d040d14545401e1159110401f040c000c5220050120351030700d00050380b825041c4003002c000c00003c5100480c5424000b0f40c1300141501d02020849140b0300307072400c0b4061808219110858001402414643c5031039441203c441a0708800c0840c1950204201f403403c0360100050850345001d10f0300c603600c0c4c9040c2840901100c0000d0481010001e0351a101940d40c1c0d004011182142c40300d0400750290111450164007401146400350015481c218001052120100f01c06142030301c211280404692114428011100c1e0704801c24002e520a0109802c6d0044407407018850600480c8900c1c21400302d0f594443ca403101c000090920540c5504100c0b0032202e2500601014101045041d400e10020b18003181c1d8902006183d2529038540e6400c155452143c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 276712455 1250 276711205 276711247
    0x5030a081821090d060509010b01050906090d0201091e031502070c09051e01180b090f040b07050f1909080307020f0904030c0507091b0503040b060d02120d080a0b0a05010c08 76
    0x19012130010a21402c02400401003280d2028141d400c10000c2207096205508460a00c4d000406860034031140005101c0c101d00c001030200c0c1482011200441e062460869010910040590078081f1034114a0044014217002d10740c2da5406005005d14000a901003514101340c580c0d04000060941e0b6010380c1e4000d8280000c60421900d000c41c1c0041489010b8160301c0c1c5a02c80c1141040c0a81d010141c01e000c01070740100c4d4000c2421400c40086400034658250311604522941341c00c5007028940104440c8651005c5101240d801158002140440c5c0106000b030042203d1400342d070a1240a40102d0200c10a07905203521038182d840000b03003018003850080392441d8002c400c44240bc0d07220030f2004002d1a031412908220709a2240001070036110307100b00d034440c035448542c0748000c0e11001e09101d252400100106d030b20074007214941003407039410003841074109025a910951820000d200c00b04a8404150b05c40c0034505a6900b030007681d0700120809000d41e4815000359442d07071120300101e68142c0c80c4e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 276713705 1250 276712455 276712459
    0xc03110a050d0c0216120c03021503090601050901150e030a06060b0a03140c0a051806030a060611030c030415030e010504030c02130603020f060708041205030a08182109 74
    0x20a086080581c040040c102ca025050020041c48440da041682c0c3e40e01800801042c0c0003204000303114051480d8454080248241c2075000f0040c3c895000541705a4190648204408044200007415500704840d600401c0f09803175074003c07941803440e010b6000e02c102038114280030301082c00005a803030800050300102d810084c00c000c210b8480e2500c03281a0303c640510740003e0300f417402c08100135269a03a954000c4000c90201c502c0c114401e44180c0e11904080c020b00c4040090901c03490003074070b80c00001c62045c00700b40340006111303080400c0548441e2014610504d994014001c200c0c00d10030000c115401e40b02c02d0240e07840350000c00701c000c40c003800d00c101081000c0d50920080c07004254110002011840c42180d42903400340c0820030b200e044910900c40a980604202000803090604800038290580500c1e4128945a11968900041078044008850580c00041c1c50049030358020b03000c50708259100c4010100101d0409102d41d5102c400c0c2c413480d0070059801c1b90385c4198107a4800c848c428400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 276714955 1250 276713705 276713707
    0x11811120c130905120a0c020f03030909040b070f1701170703050106030506010f120b0105100e180412081302060a09080f0c100512010b03060a0305030c1b0d030806040c0311 76
    0xc0c1d4a03444081c00e1500f500703d07501d00c2190080350078081990290f6100003655520020070404070340070460990140004170b83c00d40020850348070715448840e850b41c801c602800000c195820050802400d2508102070501040007103000186000c040586050451b94503241c0445403459401440b030a00782e4035030000300190320f054000420841c011420700c1c100c2d0760460b01c0003841d5968017588058680100c0300113042c0c3c0055030040c0706911f002c4008030f4995103d0318143d241110300d0f80110700e4240042d0160103d4000038810002004190000e40701d030004546403050756401e100c0f150107113580106034001d1050101207004035425120b00a44001040c01030304440000070302e000c401c2e880d0084520b174140540140c030b80d88c40515000f8002c1310412103900c0045140c0d42c0c600250341c40075130030141285601051482001020030010800380801c0400d070340103840e150503034407208400d103007400e40c0042c0583c4550b2041c001081d013001d0300e03941c428815600415203c2e6024003c50050200707481948903600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 276716205 1250 276714955 276714979
    0x5010e090c0a0915030c17090d110c0d03020106030606120b0a0b0d02040f0c0e04020a0504180204080a08040e012108030619120c0e0112030f030609021b011811120c 72
    0x80d0580014441d42403980b035542070487e10044e860000e941c100c3d092550344d0300c11082d40130510722411310002d0802030034050364028400400000c5003401d08050540c01070391914414400e001b4588500d0004111410106400d41d12a039110756610300d008003c038120998075628070501da211141130b000d80550040c810845078201c100840c2c01030041c0351003e4000382071511840e8807420140700301c1c2e50650580c2c5910341054502030700881500d400e003d882c1c00e019000e000004100e103040111f140d0103403090804c3d030b4072141010b4050940d91416409620340009024080e60100484044030b4640307600842c030706549580d5000450618050110b0f00410114a00703000209070805031b00000c0c00500c2034174510691942c401034070484200c20300801d490130008010303803800a03005400030107490040382408503419036242140790403030f0010ba0240904400010000d100c0d00c0080c8500c80b0012a46100c1554a102548a900c1c21500055046019401000004500c22000c004484000d0401804040105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 276717455 1250 276716205 276716207
    0x1f0605041d0606010c0506011e09020304060c110a08030109020a051216030c02030c0c060a0909020c342114010903020606030f030a0c03030b030a03030b0102060105010e090c0a0915 79
    0x6240808005124028a400308043e0342c46030f0131304200135422800908080e400c0c140d61220004446100000034510300000091003c400e00245224a000701000240d0500700702010702881102a5240202c0e0020451080001e4004050340e042da28031036001610341443c5941070752503204240200bd40c0c00b640c0f804022200341d402007170007610201a40c00380904219003409070396030b00607440724907402e4202c51041708072400c1c40300140a01c00014034140c101c60303a480b912003080781d0044002a40c10380042c0f001182641c0c0c10b641c0c210110311807608014034900071540303180044c0301da070190380c800c10504a000f04050350480600710341a5003022041c8542603044d202c01d8000e19880d80300310094010500090924039002c28800260009407002d107241c034030f0981c3d0813915802d05c000101c0034956958076407142e58804001ca0201c4c2403084d140011000c01b5080068036042d4144e0082d810400c9400c50050240c4987d144141c20202d070092a40d100e0000301002d1b600d5001e5078010200b0f40e07507001e0700c02d8001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 276718705 1250 276717455 276717491
    0x100b07060603230703140c0a080105090d0507050d0305090c1203043015060e040b04030210060536040807061a090606032802130b0702031f060504 64
    0x120f1242001c001ca0b25640e024100081a91041c3c3c085103401c065010408122007150841028200409503050301c0c22400004010140f150000788a0340e544900300f22010008110100ca0214241011800d016641d510300f56a1031800f94100c0c100b54130340c400706070124410070213a50504002401c00b44100b80c2e140c08180c0c0ca80040c0325026030800e603641422001c1c6d81c1c012805c45000d1000c0c036542034154890b00d4081813051040d00b120969944c072040080d40c40000c5103a40d0150f44944000300e000e00f040e042c001d1500e0304000e510741566241080400503945d03420b03071022170607a09003521181c0c010700d6844119a0407e07100c112024145010400c81007010510040c414140b003542d0412410413088100d4003d04c401c814030540200303180000c030308286040e402840e800404010904480078880c8001e8451101c2c00d550901d080d500846c200c41c40300b146e075140b4005400b0700000f05003403618503000a0f6503034000510020200c1c0e0210700355100d40a203504240701615000d0801d22078425401510011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 276719955 1250 276718705 276718709
    0x11041a0301330503190f020402030115031a031c020a0c0906030203190503040b0906190f02010606020c0d020d0318030f060605060324030102070b04060501091103010f060305100b070606 81
    0x400e54058803041803880110502c4010348101400808503c400c80c01c54024954402205484405049540f800180c1d250700003907011741245c20651b001d4201124020381514144210304404e10f03c0c0002041c41c1ea100065506c2090300f07242103c210f162041d103000c0c2d00303007652420050004009820701080400d40c036004081100d2083d0112001c241310002c0407221100c050030020495001000104241c00c404405040a0000282454500b100341050301013141000c201980200d030091112801c800d4080c42071034000c140034005801c030060220002111a041610001d104041c0098184145031090910100007484555400080c40e02c0c1d0414110480d00c081044401c2820404080b501e806c2c41000d580c00f0300e040804211070001d05000303003601031030465101c079055075080c0300903000300c1e105400c0c26001d603002c0c00000540e5418108503c00b40c400081a030a82400c080004100c0b18015940d064100c1d41c0c40e28002666454205407403c0704241d9900003020700b04003241c20b00070311100e07900000c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 276721205 1250 276719955 276720011
    0x3021b011517150601120b030307030305150621041e05070810020406020d030c0302090312120603010b060a0503070215010803030709080d050901050705070e250201020711041a0301 79
    0x30961441c642c07502d6075200301c4200c0c0b407804019500421140c0d40100303225410380080d00c1000c2802d00e4002e02080c69508004010f500003510740080c48000c1c11005e80794508a0343c2078a00c3c03842e1040d20f410b91400728149041c440d0064078210006410b12038520946116208224500c07c1035030028248680d50f80854003c01000e40a81164181c3d0200a8030855044996507000744c0141d2152a02c141c0044c00002c086000303064007000010015a000c0c00601c0714124513004190315600c003641d184c04a000001d2545010360315290310004c443d80c1e2501a52009040b5140031592903a410408230300300403c104605008102c072800118000602101440c4500895665202d4980c0d0b5034070b5142d520010340808001059080080003820351144008020031401401240c01c0c86585911000d1911001c07941c2141c00014010842400385210b1001411001700784002c3d410f01d5031070b4403848007214100c0c3d89a03114a0b580da159190030901101002c1141d04010000c2140140400c3c1d400b400418a8103003030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 276722455 1250 276721205 276721229
    0x9150703030e0c0906010c0303110423030601060206010506130503011b0e0906060301060c0501060f080d0801090207020603010b09030a050d080907060207030b04031b06110403060507110a0303021b0115 88
    0x306200c2400280f1421010001342051041d40b00c4070019260395440380c40503010103841e041c9180071020f0420090000340302d8000380c000c03032000e5000c0e041c0060350440c103070600c40d402c882c004124540d40040d005064500440d00e035981c1d0905d4100c1000398070703007071350199415508011400d02c461741400407507070400c0880d031900074404020a041204205c803c4078030301d40c498824401132007410f124011413150307240320f0000001c4087c0c0301c6c40c084460001640c040781041d80503000c0d40c03040c5507100e02214010086104154141540e0742d001030704074041402120120704022410303000c41d41d010001e0204054000054826441030341d440184480c004031070700c0c41c0520541c18009185840010301c41c0469800101c840d6003620b0307175075044a442e00c41c04620745004000b07a0382171001c52070520400700070600e02400a07070744915600e0040d003035420042058003030105c0300b40c42c2080200c010136100f400f00d505280050f91031a8024191907a02c0c5203019110b241c0d0300e811824044101780340014020365000079904 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 276723705 1250 276722455 276722471
    0xb07030c031a0102061b21090d050c030a030207170d0906060f08190c2408010b0307171b0708040e0f060105040905090309060a0314060f0307060e04020915070303 71
    0x18032001c0610390b0b549006074400e0000500101400100507000b010001400345001c481c134409552001000300d00410013003410080c440035000c208000c19041c0000d003019801c0198030600c1948030300445160006142d000294141007250040d41101900035420000b0b4403100380130007034401444040c0c1c0880704079242910209180303002298000c00c881603078009100c030003000d680036800d41703040071421159403501c07080206140445808404900300c1140c01d80c074a01e99603803001040402c0681c0b201405000c00c006200708540e002104840d289070810380284d00c0d1b11900300c0c2000144452504001e0120301040850400c0301d04401082100d07a129014071694442c51200341901c402503a207640410800c00c801c209440c003540020354402016019a0f050050400c04900e556000105203c002650345080ea80c56082c44481e090f00407400303a80c0c1c1c403071903ca100c01080d943d41c1c130f0707000d01810b000320603104842d16941d03601191101800901604540042211903e038103401010080340442d0400c014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 276724955 1250 276723705 276723731
    0x30f0201020304090f02030a060b0c07060507110603011706010e0c03010b0310050303041d060a0f05090c070f08030403032307051b0a1101090b07020609010509031623010302030115110a0b07030c03 86
    0x142e444c88060040581807444c3750140594a90b404480121004071000710504002d980d0703c0f001d50300821415009080001600d2600d03400e114058116800c10404038003030121b034820f10400d80341524805610380740e0b69100d4149035034101740315511080d0315200005000c41c08a0921403001120104181000030301d8a40f0820000c103081c00c3e0044074600d0a00410800151504840980d0042240c003100340c606452502c416442001c402015190540008180803c066061007000d0b01d0000a642c18a0010203081e2031003003140c07014280d1270070000007140d20b41085c1404402403c280c120441219410a4146007000c034018a624400780407840c05140002c0c0302d03040d201183c400560003080240340c100c9440c0107442c5600200101e642521400d603039034940f55004a0b90318054100c00702000d940c2c00b20440e0090444501c91031180c10940103000402c540d60780300958107000000707070602c01408803032140403600c1c001c800320300a841001c0007428008660381581c0702510348070099030140f107520b5240003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 276726205 1250 276724955 276724957
    0x4050c09030f030c0c010c210c0b0a05040b04080d111605120f0d0207030c0f0b06040e010c0206220c0608010e060406030302031206190b1b070f030f0201020304090f02030a060b 77
    0x181c202540e040301505d0010b0f507200d00e044178109131050f440c41a84060746000348400e01c2c000540c4201242c2d04d01031441c01e004111040075805650980107009601e02079440e042d5010b400361004100400103c0e03940304003019a00030303800c200512400980c44400320090700036484030404094940d802865840340191450508880c19200d4240070a4580400029420002d41c0310701c00a404008122005c00005000316001e6505540290700051031401c00b0020482103401d010a0400d503a0f15003a40d0312601c1e500800e06a5204d47c43c0c40180c0001c040b241c014901100d41644c0c01000c41c109250f01058464000c032015068a0345030600c030350341da0307180000d000442e06507000c0031300942e2080c4600d8081804800007503500130009041e184031410711400b004107034403854126140500001c101128055805070500c0303200c1c01c61400410000c0c2c949000440800e50901024000080002c11407080da40200119002040b0300c040410401420501e00c0d8025081601e8a0400c1c030304110000500d011500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 276727455 1250 276726205 276726217
    0xc12060a051308040b0a020102040e070c0c0602061e25020d03060b0f25140f0105060405060d030f110a0308090f010510090b0103090206191103070f0201080a020904050c09030f03 78
    0x543c3e6840c10b41407403200c002c15009507024504640d002c01c000702d0071b110785540313042c0910f0f4161900b406139091490a044101e04035007107102107500c4802005044c0003030460096081e0750384a0071321000d44405090074070032245110041031003400041c1903031900f43d0000c0c204416007420f507400c2207540d423594a64aa148a4501100c00c01c0701c0900c450b6008a0050041d550541d644502c190801c075000d60f20b882e054121025203509a400150a0324038101080c024181c0c89003088508010b50724103240002c00b000c960f0780c8042d08000c0d04140041806d0300690307000d103810307000700c0840d10700490350718009000e500300702c07a0030269015211951601010501401d40039424580400307a07600e0070132030b1075801401c02a480604141d213540340d02c809078a8201c005c1a0136490708089000d44008403d000d081603e42d1003208103544c0c0b0400c0404045503c207102030501c0c5a091900c111181ca5949500000e40a82c500d4a64404d1918052140d900c4080e40209002403050301907403030400ca0400d8154a0740144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 276728705 1250 276727455 276727463
    0x1b0105250f08271e01021e010e07090b030d0e1809011e0903080411032118060c10110c010f0e0d050702030c2403010807090f1b030e0c12060a0513 64
    0xc0104103200716400313070303280c01044040c0304131080d4520503061840440f000c1c2c01400442e035518010094406814803981e006030800180500c088102100420798034040e061640042006500c0c0303a616584d5080f45149150b8020b40140d0441e091010745207008041d0303e1400904254219082448010704e03019001c0299059110006139981c0c5e51501c41070901c00c0c1b02a141d15006031280781c480c03c404400f10800a120b1001140d031503517040c00c072098294502c1c103281c0d4800c001c20b001078601e10070b00003042012060741140100b40001d592610001c540110313901140b5550034042075506051003540128800c1c2030303c1d022100e5458000000742e8031449001c00294164201600511842c06d020726000705110312081792480117401c170744174001c40383c100382c0101c0c00642141008000c05800307401485801c404404c1c041100c3c40d04560b1450340344212941c0d8070145500e40d42002c44802d4140700205540001070b108100d4003e010040549900048a181e40920b1900f030200310a80d40821545100d9588 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 276729955 1250 276728705 276728719
    0xe06090c07020d03031803020307050d0207080604140a0c0b09091f030b1503010903270e0a05060a050406060e01030e0604020303030c0f0d060311031b0105250f0827 72
    0x942c1c0c00f400440c41c40d250095052548412080c40360074262000008094000e502540d00c502280c5802414070018000040441d80850400d100350007001c580b40c0d07006030317000b0346501806030070450803800c086400c140239140700d081207000073f5078201e00320042c45481c3c0708444040d4135566182425403030204406882007100000e00741800064101d1266640000b02d0301040e0034140644030019003900c800d0f000481c0041c0001a5100c43c401c1c0702c403002c003984100d004c21503c140e030510b0380a40a00304001c0c03040100035180e801140081d2200081440a410702070720034000c032600c1e0b51025022400300b00070280041e2510b4984c1504540118036107001d241e000f40038501d1600d0303ca0311851190051100c4058181c0200004a440349861103102d00a604c161030401400d45504101418000782000c503d205100b400301e00301e550f80e130103007c650000305900081449120400070400720100340a03801000304407220214418012218041c0c1070948c00395600025110b05200400781c8040001c0280b038200c54 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 276731205 1250 276729955 276729967
    0x318080915090d060b010f1b020f0d0b01060503011e0f06031d03030f010501080a09020f011818020d060b0c07030b060f03030307030b010915020601030f0501060e040c0e06090c 77
    0x341c100005907030082914a03041c1450b2a040004040604820088070850f0341c88500b258a035030401401c201c507500d14100342c00b003003094040f00020b2a0000c0c400070300c14485403481003815510f02c440d0350792440c0c00403c031301d00568480d40054400c3c0d001303000d0001198620b0035050151803843d01e03d801a10381d81448010840e180c80f07401c3c0c0140412105815010302c0620446140722403c01c040c0d40b1a000041140c40203514000014103448800341c6004161030030600e00b407025031542c00806000308003e07c1d00c401541d80075031a041d400c600c0b42e000082d804041c011401c0c82c11519402034000318001140c100180c1e84d441e0351190040c82000d0180c041034200040800c04a80c4c15120664880009055000d200c681c0d9800a4159441150480046170340c0710120310403560301011400203006032590550316660586400303950341740144001801145401c2e034a00802c04d081d0000c1004140d060b100700c04909051030491245103080c041d07034881d0081400001e0192400207080f43c040d042c405140c52402c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 276732455 1250 276731205 276731209
    0x231207080f0c010204170c090708150f061308010618060f170709050103032303100e0402120703031710060c1e0b1008010b04050c0f0d151503180809 65
    0xc1c00c0460b0746102c0b5542840001541c103400c51440c145a90040050a070000e1460100001100080c001c08200608a000c02135041d483c004d04071102c08040790f1108800c00d42d0400036500b0f12440302c0f584601600b407800028100030541004041e240c040c042c3d49044402c056501d01110120b00c1000307046490b08a041100c200010202605200c4841c196900191102c88680c03d8410a9104900041040d08041d050756400a000524441f035004c66524600300002901c421075164041c6680144594011404550303c3c1d20400c03c0c00d0030003d0584014581d00e09004e0700d61090700c0a007840d8001110700140301c1c2800c0180c84c0017514900d444a4100342015111100680c00c40e100e03039243d46c3c0350306541c0404108001800c0384644000c0d0403400140e82020300840c255140004030a010b030f410701084c01001c502c01e005071065229076058503034403035030f0b030a090b030000e4082c201d60b103040c54900708000f142ca0b803402c071403116440807152020b100c40d62061019441503130031503c01520541c1c0503c4041828 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 276733705 1250 276732455 276732457
    0x20102010501080d230403170d052a091f0504031707020a0b0f1e04080f03030112062a05030601080f090a0b10080601090c02060f010f050418231207080f 67
    0x240300f45d01005080c00c0d1a990f8208502c049584009040f034004210025010918051140c1c42840c0030b0008900c600200e46501d07414400040d00c000b091004600090183c5039480b4000c0c41c0035480710150160a58944090141d038400e0109032645d6240b12100321850741c2d01e500b110382d10b0785c0c09001018050700c4c4c0420022141c006107010703041c4450070040c01040f1551402a03000840007048030b5980c40d03183c82002442c0c454590f080510341c0d003041c801002080032004076a8440c90700081c0115401c01c010750340907194200c10801c6645100c05032280d02603240d0100140d0320402c4280c8501480b52525404034503406011a10752442d0f610002a03140010050a500d40d040201d600c40c0007019610b540c4c040c2d0421000f41c019140903a5030b100300605083c0c1c104400c9030400000064203450b941072040113240b20b803040c050140210340791103200d504102c0c5c010005c00d10b00d40143c406080182e00003888803030040000c1ca0b4200e41c3c8030340340428064180140407500d506a0112a803882c2800303403140c0c0011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 276734955 1250 276733705 276733757
    0x703060b04210f080c0f0607020a0305120a2301051e060a030b060408190b010b04050105180a090c0509040b0306151c05160602101b0e041d0a020102010501080d 70
    0x14031511034082e4800100c26102a000f05d8018402070300c405800d42600a140c0340c0001c15010171075005d007101c540440d80145c01c89002e1603070b50816003025075038483c4034800b03042000800740c5038103140500131145190001c00396068910844809100f9080c4030710044403a100321004903031040c002c0010b4403d4074000d80c065444104040e06950401d50f5030500380b41400a051011514140501d4200c802c011003207806a01501c0c2003002241000e08100001303200380103691221002d0300104029a40301d580e0600030324020600d5110912410108510061454021125241c0291700b40303855035005240210305a03111702d0031011f000b041042c40d2002c0201c4240240340b0045840c1801c1d01290125605000c41e008585180d01c102c190a403a00384001e290401f450102d40845250860002403a0726201c01000c45007a2490324950080500001800620300100307180c80300c90030b0110000e0004004030324010614000d8000700216a80c0c0c00b41c507a1030f0520205144001440024803590b202111220175030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 276736205 1250 276734955 276734963
    0x210e030d09050618040c0201020405010809011404031206181d06010e0a091104050408091e060405060307021501090c1202040b030c07030908030f070b01060f080411060f070b0703060b0421 82
    0x441c0207244030215040b01c0020340c000c0010303500021b0910bc5543c2040c142c5030400c1d0008020040140e54481034040018094801001c205084000c800a280c080d04404c000c0c00005810b51416541c685020f0020722212651190100c40034514840d14200414603a04a81c0c84d40300c500350540d0f0303555681c401484149000c4440c80300100b100380c010f80750f41c8111031045108600c0d0a0380c83d150501080440104036001072401c1981502c040d9080c2c13200c01c01e0b0f400f1100151210381d10391b01c031904181d05002c0707000c0507100810304410000815a041340c0090303440030100d032a0040c04d01e4803101018140e21841c02104d404a40030400b007484084800010a0090301900c6c142d4109501c43d5140ca0859104c03052400d118400880d5080c01d221500030030700d005003124140000321078564035003d8555000100302920084100e0084080b80d252602128800c1c2c082034105a0703105d00c01d00d42685c116009595080000f403901d0b00108004807400c007100c0030748203d00080b0010010011a00c402041800c0c000c036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 276737455 1250 276736205 276736237
    0x30e0d030c020f06010f05040506030a0c09020a0c0204091101090801022502041b12051510031d16170a03090e06010504090f09060e030f04050418210e030d090506 71
    0x1031242d00c401c0c08198046d040d040890801186400b0401058400190620b846a0045030a00700081c0d0f1440da22001c4500070400962249111070040e100e26132485406500141440344800401c01c4000400c7d100c5a0b00340c803045140c40d00d602d103c5080380079660688001b40e50a004101c12280300b50319282c0424030040c80414260845559604255010003002c004a101441729803c600b2090261607480050501002034602380c60002400801483c0c60380014155108180c1600094140070420015003403011981d18101d200100008500d481c0310708450000d010400022599020516004040d09a90f44912290401100107200c0c000640280d0500a08000024004101e402010002480c1010020b444000790030114281d6180b50000c4015801c1000364101d201d072041c0c1903c0c20784106407000101e03034800c0f0101d0b000248607030708040c1410320002429080303651100507807194a405640c60440f09440c01050554616021146c1004181d021605201e103051001c05800c1010000640d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 276738705 1250 276737455 276737473
    0x91404020f0c0604061103060a06030504110907020d020601080607020606060c0304180f0b0f0a15020a021201020c15010b0d180f0b0108010b060f0301330e0907030e0d030c02 76
    0x24107000d5000102c1e0a4050308640304000501980c0e204201c20004400c02540c558508100050750780c007428001e0405041c2d8480c003003420300c6101c40700000d010601822928050401e0400030395119031700c2d09641c0052054400200d521038022400500406541c0c00903d019190308040000035001002000100d12003032100044182c02a1100350b0040081200040d08004903092082910454414980602185030105500f0b844244104084801c1400c0c5e0420b46420748104a0a105040c1000b079400100341b0590711200328194000d2130400e40d03101c115540c0c03400d20f000307848034044d09209803011a003082c00340f42c0400076540c00c00380404681c4145a400350178507584190100c03b2034001500d013414058018442c0050901c070704801610b0490392241000074016500c030301c0e440140198801e642d0b04501b488500c110008a911400400002002442480743c44c02403140f4001ca83c0b8511074041c2d440030400b482d0007841002000f00c0c0101c05000d55081d0110700348c014003480705200c401c40c401c3d005070b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 276739955 1250 276738705 276738727
    0x702060d050408120c0a020703060b0301020706020f03060f180609181606020607020109080712090f090e0706030506030a0311160f0e07050f0301030318030812040210090609140402 79
    0x1c8611441c03003000e8103a1505050101401014130080c4405c1c0008020402803840c180c0010302d010803a5800000071500c6030031040824064040c90350000c2070640085030b00b11329020000c010791302c02e00e016504038200c0340c43c0350304001850f040c000031424600300d40c2d80881c120f0b09022424980c40751001d984c0d0401d007078545000610300340c0b60700a06c042c010031700b02051001540c103116854004407248001c2c48643c481d81c550140714414050001c1c044900300015480c458081d2520000410311503107103072842e80c0d6800707a01001c0d02080c11038604074054500f010a265003c0d00c6607074050500500100708400055a0036601000c24080c002c0091040200405078a0104402d20010344040060001458074027960911055005860782003840b0081c46060318526101054a04603078041c40c140f8461130401903000c2e495072640e0005031043c5800030385400c034108028101c0d40610b00c240e415995000d008202101c1c01c1500e402584009454042d081124104207000c0900c0e4040080005280a1603888 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 276741205 1250 276739955 276739961
    0xa0203040c0f0602010b0901151209230f0c030d090909030e04231006050a081b04030804051c0209060f060c01060e0403080112080d050403021e160b0705030409020702060d 75
    0x40958010f0707440380315000706ea041c40c1455a005048401e42005a480c0e454800b80a4042044c071240c107081e5204040390512498003022500580b14110840d5169482c04065855004203c2d00703010ba442800440006401c000580801921b59551404285402d060704c4801604040101fa02005420b042c0c0b203801d60360302d1285203a806110700061021035850080440c1511008103040c0c9451220b95017040740ea50042c044892040313051802180036078540400d02c0f0040013491260b00a6400071030040b0421964030010130544e9001c4403040c00a0b191420741c040843c202031002908400382e01e001c28118113004200e5034082c10010115800e1840e8040311500f122101d61050503c420240103101c149900700000a014041d03100b01c1200e580c0035600c41d08020700c990441c0402150342c90000405040c42070204251008445034182184211000c1d0f0030358902c4481c1a0780100d000f200382c0090403105a000308e9604c00d0384500030318200741c90307e1503420094000302c009030b820120030815203907550120301c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 276742455 1250 276741205 276741209
    0x1e0504120201030f2405010903021503040314040b030103060e0c030706081306020c03040f050612070c0f050318040b0402040e040204110403080f0a03050f0603061302150d0504120201050c030a0203040c0f 89
    0x44040304841d458038a031588a811703a511850500070941020b201607200d4660501c0c40300c4461000c01c0e0340340c0302d0380f804448455015560a0042034003182c0403a40301b6080c00103504a034060300e001d012425444a0098582140c03060581d459400507a04101d1035018590141c0e21400b120f007007183c0d120003501c856069a02c4000c240003a50400281807082c0e02803007090304041c010076201d00b400d2545a50111034103100207800d41081c4040050400708111244807030807801c507400380640743c50f0384020350306e80031000c54109850310980c280000d8000c18140780c03007036408946405100f0200382d1a40e80a000c010b040c1c0300003031002e584c010800072022422600040c0004814014500c3e698160020001c08445001c0c0c00e4807410204038050003100e550000d085504443d040c00c080741d024180d84000b80741c3e800120030050304801d011030080306041c0c0c59408180705600500d43c0b0210105c107020204d080b12401c9401404150042c40400d00502456006d1503103d480f03503016203c5c4e141c444c800600500354076 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 276743705 1250 276742455 276742481
    0x2091002031c02073c030f030b01020303060d06020c0106050a0e1014060702010509180a0b01020c0405100b0d09050601181a0f040e03120906071e0504120201030f 71
    0x2041515090000c046002e003020401c030440c24500c1c590303075280007403c40ea507400e050240110004412a28800c3e44d00030304c000040c1000c00701e03048918014051503049074040010078075044000380d50354008401c59104030001410890071004568501c0000e400200c8140095940d40c0d0f00441c9503102c2190003000b50074585c0d0f036450780b4a443c2c0131050701d60030396402c01500c030680d0340140c0d0019100d600a5415003542424140d03210b10203000451406552603041c2d070004403129051114640351030f44500c4220300c0070f90a44005241100c00d20041e994281c41c401010303803108070104014058080504071902c0d0081011506902030f80703501c4c0c0392400c2a00610041014051440c0720544d540c400d4076101a41d040c0e2a0703003031020700310008101c2001529140d000b540c031151415051003040c01129081000d4100031109400e0a01d8219a1031038111502400f04a07401c880c440f005040310401c0c80c00d114a90344161509041c202105d800448901049040c90b445001c50f00c0c2e4240c0c2800b507110400c0c54 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 276744955 1250 276743705 276743707
    0xa0903141b0607021b06072a080d050c0d0809030f071208130b0f0703060f0b03090c0607120f03062d0501090f090b030307020303030901021309140a05040302010209100203 75
    0x6003640240c10b01d080642032809542c007110440c850001000115071015100301c445039285c0b503e90410849945c02d5441c4643c0d08504440b050f040c500700c0502202c00c1d60944411100c900308650303820340c0c00d403240442103080340e03000d015200d038164410001d03e03a0100d20b400030b4030304202d100706c01000c4940007840100d46a02e420300c640c2000a41c0710300d44a40c8005101440c44506469840c0c0c81c40000000d46440d001e51440800102e426001e600248001c00b1401d1400340051354034540320005400a890b403007450b010701c80c1c3c420702614010040d0349003070360486940031034040010390580f80e11560003200d84c03c1c151110400150703000e41e09181554180c1c9400c0c40540074940307260b9461103405542101341488044441801001c0701e1041c0401030303401c2290002001001313000001c0c518003508100a5041c44000f0410405907011340103040459584d6151805068440b50300340b05541c0b10101c03600407207100b00005030b030800d5540c026641182c002c6c00010b282400e101e02064100c15100c40d020003581c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 276746205 1250 276744955 276744997
    0xa17060105120c0405101e180503120711010305060a090902040f0c0c0515090705040906020702030106260718021803191401020c0a081b01020a2006010602060a090314 73
    0x81440701a1035a200761f1604480c54244040c1e440c05020880300414104520407106400d1400b004003040d02610000f001c50310100811180c0354415480740008035140b40840442c51010b500a00a89006d401c0043c0032954040c20605950010050140700b640d0041d180c001c10000c0e441140305144510340d59503161052003195003409445d26514046150b945100c9100b088100c034404207440d81562030441e03010031200b10038205a003f900943e0000b0354154071304003000802590803100510308004070440000107800d11541e0b00d03202c001a1003840350704002e000c80c5003046441c0f03a009210344480800d04400e0b050704200400d103404083c40c02ca13650241c41c0c00c40e000130700540c80303004044020010001c5d4548400e00400c25100c5402c480f0003844842c001c1f900c1e07100d01b0114100c1981c00d94480c4000c5440388102d0f04000c00b41c0803141b1822460503911014508000c6000c54030a0584541d900101115258048030a004001d9180d0680402030100c1412204051200081c180c0f0000440382410440c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 276747455 1250 276746205 276746209
    0x1c02060d020705061311210d0f0801060314040305030c070f0302010b032b0503040507030b1014100212090604030b040f0201081305060c0d0e01050a060f0b0a17060105120c0405 77
    0xc00080c01c00c030241c10010545c1030000d501c15248040d810801d58010b1403464041500c00d8052a0400401c000e0780215280781d4965907200742c1824a5030901e50310480c80e640e80d02402d804990b103941c1e40c10001c0c41020009070111340604002d50b084030110740007078603040aa0b112013481ca6402001200140d441d0069488545401c110642c140354140401c0304001c0800d00070340c440000000c0401d014400c0c0403000400744401400040015508164000e0700c3d0326000214181d00240c0e4014102191016012040b181c100800780072031490309500100502005440403095640180450541c01070f000c10003c0000740d503545881e0b02642c41443c182d215160244009801e51800915250071028002807403000b207100081c03025082010b10241c2030740c6804070302c107803405401000503000341c940c00c0c4800d006e0403500369481181260303100c4600d644995280c000d403070307090700c21107103040000340300d0401c10072403220b110b520a42c122005040140c5400d42d141003510400701c04940e80c4e0032405d00400d08000c13034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 276748705 1250 276747455 276747463
    0xc0d03060603060f140102031605010501060f14030612070f03110a0e13030305040f02100f170613020c030403020409030c050f0a021c02040b0a0b0a090b04060c021c02060d020705 78
    0x81d2069082c01d024003420034054072901545407064411501d480200700d002a4020f0088a039596201c04903560001d81740d0402034042c007400c1c030036440001e0710040c05204291203140b881c000e01220703240c014a19103c100c01c100104102114048a5000f503003c00a441c05060307007101c0041d480b4041140164010004002001c1280c0d40b00e00d003900e200704104400050038001d0020324a03407604000426803218104036000584c5010001c0d00601d45240406006402070300742c0c908076186541e48130100d9540316900c801d601c0280c407890b070002c110425400da00c02c2c140d000b411401239a10200e82c00c203540c0ea000a402e072030001c04240c000c174001d0034640c000d1003014000b201c0e903042c0c000c000782141309881d400315004a070642c080d044104c040c0c0454204641e1540c002090040b002003105400381d480300b050710403a50090030a080814404500020034540350010f6070100c494035200d03140c4602d006d40910091001c1c070b042400000361400c41c101c0040e51114050102030345000360068842d80580741841c0740c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 276749955 1250 276748705 276748709
    0x10f0f020705070b0a050705070e16020a0308060d052119020607080609060d0c1e08010b03030f030403110706050720090c0903100e1c1407170f0c0d0306 67
    0x19004001d081c0200b01e0008550041380c0920840c1d0381e8901855108950501a1150080a6014801c000203840c00e000b002903028821800d02e4042004100360180d9803604194802004502000005651403138283c03403401c0500d000b0420340d040304105a40071100351420f50808110044040f44503408054040c02c4203021012074002068075007010303400a01003000041c440c80c4102014400174805885480036903003d41c1c0d00906900749a0384400881074244440ca1000c44407011200c03001480880c1401900c1701c0b401d02030061440d06010403031071070a90780000d10a500b48020144549416803081040d071008150607070301c007901d882e02494038013100c1090004055400110380301d4140c10b42d8032554040d811118100b802655640d00002107800c1590000042d24428a40141c900b06000040344003003401c440150700d1054030384007810a4508031104600d03420680350910200000811310314402d0f102125840200e420468100c4480300b1991008001c11034a03008210b0ba17012154040c06180c0c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 276751205 1250 276749955 276749981
    0xa03020c0d050c040c03140901060611071d13050703080304150515190f0e0a05060301050106081503070f03050102070309060f0e0103050a090c2301260603070b0c010f 73
    0x70710091035140e25581c0d03403011020a2040703655030700c2d010001d03010758421004200c0342d000100e414a03050000c5402841684a4100410013071629040c0c0b00002040220686580d224802180c5810030240703100410014100e0640410101c02c500102e40100201c3d40110302c80c00c031182d5249020301d0005400c1400400003100307a0700309003c3c800600301450060300c80d0710b0103941809044118810718107606d402d91f40003900381c00b503148022849401b80360a1500c43c0621400c1404a0745465080c1400c8032000d1140b41c0028000f00c0c041298400398480039910b043d0000c0132120b24039110990202c0d403c4007540100c4043e980040c8010400d5040321243c4003c00c0c503420070526118030000060480152950600c1c1010b60301d0700003e1120f507a55000d960307100c1d00600f0340041c1584032002da004c1600601180310008240800191040d031181c12510303104102001e0785640102c003184813004980001c0c2085601d070140010105403c4195400362174840012000840d44a0b0640c0a650840700c010910354 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 276752455 1250 276751205 276751219
    0x3010e04110f1c02040f060602030c010b030607092304020a03090308070201091511120907030201080a060b071103010b130606090512060103080f0403050a031206050108090d03020a1107080a03020c 86
    0x80d243da0703110b03491007180780700a00060364030909100040c02460b511074883c50382c525000c0c0c003207901c5a0000141c60203040410003084030074806010903540d103804980c41c60001d444c240c0d09002110101e0f07030154013299004180350100b40c100700003c09a8100c11a5400000c2c2d6400380c1e001855030040002d9004200f40c0000c0010001c0d036118151a22012144000003d40318200b13998416030714012a014401200402c1d0518100040084c2d2500c2040c40207a0000b1981c3d4041858001d481c0310f0711080b140c4014079a0300d055840d58401c0c0c0c0301c1c811040070f154103550f54a41211181c955012000401010301d800148150500c0f00203000095103410260003140f20b0030b9184140900005c015042d07070f40214010362942800c280b40600761140350070007801030080031000c2c1c007010380005844041c9d9011202c140b04180e00d0300300443e164102140c10b103d003036000300c01044c81e0500960042440f0b00d00c61074410041d030602c2c5d202600e80341295204034081d503c00f03400c05090642c148101045003204860070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 276753705 1250 276752455 276752479
    0xa020f09090a061a150c01050c04080a0213020708030a05011502010c17090712030c05011404030c06090c0b070b09010c030b011707090f080619020c10020702060405040203010e0411 79
    0x4107645100d42d000007483e640d80e40c1c04d0440b28002a44080301101401003802003040d15111801c2e001d90000ea0000303c8079820301000c40c40074a90301e015281503554120081c008618244c08005107802c01c010204a915400c1140402169000009610a1184031000b207400c2d498550b1803444540388000c800b08591402e010a81015031160311807401c50110701d01a00140c80c0c2d184440d0400450b030703028210b41000d80c8200710805801c040703c2445140540001c02c41c10040d103002240181c0101c1c1c0040004102000d01700c0080c21641c050004039028080c0305880c40c5c1c0f500e011504a52200c039041d14a01c61500400000c048240210780e114a01031805000e20401180080d12407186082140706078080710001400c40c2c4d00c81d0700428000c00c01c0f0802c122180d9520302585854804c00d030794922485c480c0d5181c8004461060007150960030461002300b1010144680c440000e42080360101c0e44050304120004c0c1e181d5560000e5406081e025240c07030a941442c1c507000d00a2840d00d03841c240140441e10318 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 276754955 1250 276753705 276753721
    0x5070e0307140909070803030414010605100905040f11041202040e030403020108010b0d110f0301030308070c171308070602060106020d09080d030b13050f090c010c15110412050a020f09 81
    0x1049807200543d048103c40c2ca80c0c0880c1420400d00c0d80162800b0311000c030820003400340360080f004041005100030407186444000348030300c544c00f1076111030125030700d0002000710303051641c4108101400600b0006449509103150300003035205610240c030280110521000354580342c4100102e0403400300c01545010f16607800a4100e010510840c200018040f42c1ca01100201e90480040d00c800409030640d9107491112101490f00b084c001907000600b4040003941e614080d0400c90035440e0000c03408800185d070360686021a038000e41130290008107513000011b05200801000d80070306038980107072401c0c0d07041c600f0080c40e00c54001d03101c40401c0043c503020404143e010030624213440040ca03000c20b00d110014081580100d00e0000b0000345450300f000c00569883c015a107e000d0040c000940daa40c0149000447d0200341118024100e600222180c80d6015a075038000140c0182c034155490509585200300e580d1005041401e98503500561b152030304614095100340740c0070b1003c85002c4960709107058 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 276756205 1250 276754955 276754979
    0x9011119020d020109030b011d0601020f0a060b0a0806010902120c0a0504051302120a09060501270c0c05060903040801060f23010e060408010905300d0f020d05070e0307 74
    0x10340640034030060a40300096911540c56a4043d5402904060540d6581c4000d550f080d4250420302001c1411000030402030762011824612040d0984010b0010b44d03041d4a6001c0101060070105510410003840040e42c440280300560003410948001038881404800c10584440d00070b007100e542940402c0302c000160741080a036401d8480a07655403441c1d03c0d40c000340c007000380716980619851004240400c845003025400041d5490b10462003803140f1391341c0e0f1440c4070203800c074907404010814442c0d5149110641650080b050361195140014207d100b5440e0305052104c16203200030181c000180601c042e6400b4040c4400400307103500e840b92418070f803508105100c0c00454580008411400045016a21031000000030b060018203141c0d403142d480c0c80303603402000c038a0000c4a250189400814036080c0d404441420325a110803d40d8071030700b00301034418443d844290b010a10b643c1e00c60030190b00104510140214907050343d00002c160510380d4014010090402c2468842c0e4003001017400365003d491 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 276757455 1250 276756205 276756253
    0xb0d06020d050907050108040311070b040b1801030605010c06180b04260a082403011d010f09020901063b0916090b0703030905030c010c120209060f0304060b030d05090111 75
    0x2b14020002c00d1340c548482d4140305885d44500040340010070301040801b4494010524030450440240b0040880c400640c00c1e64010f208a60126444030008408034490303401c804502c4442184802002403a547c8110781d0360800c0d50b060300c48880124040301510040581401c5040c507154031541800140040100700e044010000c101103000c0450102c00c190480e40f0520f2a20740c024000e01507904049007194410040c029a0866582000907415500c0c00074858810140d030050000d810b20ba08101d41501d00b469100040004003981d004401002c00b1240350b044020300c0404521422100508100403480b50702606051076034014000d0440d0703180c1c2129240080394014a42d0545822541c18142c00400354a02c01034244e02000642c2e0b40d0380d250640c0401d000703090741c0d111048030041202c2606e08900030240c0c140d03004601004070b00c001e0103043c400b42d9441407040001240d0b0203200d0300401d0030444240000808554042104107456801c040d01b12151540c407070080000c07900c5c01d00d64100814280d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 276758705 1250 276757455 276757457
    0x1060c02130e010902092d040c06110312010e010e0c030f01090b030f100c18061b0f02180105090a0c0c0212030c1e0c010801030213050a0b0d06020d0509070501080403 73
    0xb00302516070340c030303080d040000040e80043c4411000c0c41c00034444201c0b050b0100000b4801c001c6000b00544030010b03082c1e50342c05142c0200c800481d0303500301141078409620407020500b180c4002e0010719000443c0306100342c040c1542440384805c07945001b5001602400207800c906140b0b009108000900c0f0403044400d04403600b0a40214901c120000842d0034418050840e040c5405404964804d144050704030311100740c80b036a1000d00304074140c4092084000d4600071000026016050030a00b184090002e405a0b406040480c114a1282d4001389101801c1440e05820b21044801002503240c0092841c2d4071020703518050001d10758200009011224250307000b8860361141040180780d40707041042e60b02e0180701c0c00480b200d01d02e5451078029040e03501785800c40d40380b040651a107403e5200707682c0e483c12264080c2c00d9025410354086a0000387c0001861590515a11180d031a16079851030350100c5298017616005a55801030f40041040d5000181040d005506c1014208403e0b42c0c80818294410b0309 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 276759955 1250 276758705 276758711
    0xb031b031006140904080405060c07050a061103070303050c0d0207060b0a060809031c02070c0602060f0604020f0d050910021c14011a030c130b0a1205010b2a070e010e01060c0213 78
    0x60703454110700e2030047d030b00a5504008007154261802100080a9096a0007101d4907042d440e540c2e00100c074000750028407880982c00038828031001a001c0e420482d04840100081428662202c0b0600c04030307001220152403594a40358499098180746a14201130001d5280c850300c81c0c034150022a03500d126a80300b5034403c0142412003081200580c1c15035500d0380d480680808400e94640d0021754403102031340e10441450700354001c00d030103150502c00c642c0310010307034102c00e810004043d003900020039004003018914007030320010701c103039100b04d00c014012183c5288003100140202c1c0c1c84002201d040784007010001009038018040c2003800e690000c81d240c0c18209240d5a40c4d03614200240c0760284007071030311404540c7c4101144030310315000940034441c0d103940d4908009050451550540d01e00780b080b202c042c10304229885486910390710001e40d49000c0b0004030611003450110781d00e800495440540e442604000600003044000207060040c05989068280a41e8640000380c110800c0301020201950f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 276761205 1250 276759955 276759961
    0x40605070503070803010f05130b0109060323090615010201180b130615180203070c080a05122e030c05061309181407060e040f0b031b0310061409 64
    0x1004100721120f8540c0700740510703103d503502c6c8684c03403000560380600781c85040b1201b5480b00c0702c80d9034480c00b0021403050390781c241ca17030f032034084c0640042241287c0e841c1805503083c5074120b01e0800014036805000710388001c01c003501d401c2d40d98101c2204502c42e0f0504590400783c04080390490140f2001ea0389400807580d10441d118020001d41e1740581c030400070082410305c80414580c0240101c0d44c0d0440300c0c00300c001e01c0d10b070b001980074400b00c3c4811286400420603406030307800030a01c0d190240201146905001d4581240140741d5801d0039011201a807036240000f15a000101c200242890381076020302c155103a0504542c3d0300e407042c6c4c455000f5103014140101c0e0490300340003c500c0d440d004040d5090104166010700c0b040902d0041c180700103540c0c0c1294021000b04003c40000c0d180215100307a80c4440044400c0010000605242c01d04820101e88400e102680e030b80d0280b10b43c519020ba1210403007a1114600285400c00b0000580c203840185810b0382000303000300c005900d401c400e00441e80084156 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 276762455 1250 276761205 276761213
    0x1020a02031c02010b010c120c060b0402160c0509280605060c010207020117060a03080919060903060608060f060d03020f07060306050a0b1905070309080a0b150901080304060507 78
    0x20120100103585440780c08080485604203488214082e0071a034000e0001085490044d01e8800012500914580741c51130a989a2481888030780c0f440c0b48141c3c40404d41c03808420028040c3c0e042440500102844c124100040101c0450107100412061b903601d0741e18600f58103c2a02c038254028611030f25400c45c10322a130810420341c0068080c04c0003c08123030321017180b40c0d501e6000390001c2004a004c2040404c180701003085961085200b20402010b00728058159a0381d5051900040c005940007003d06862a04003068020154003410083e900d00d20000c0ca542044000d58005c1d50004c00b05801c440e05000d4950140b440550340620103589212000d00103140803440d00c081c1540b008594000c00b0404101da41c2d064210f0340446604403410102aa228180d10a9030300c00e041d0001c40200803c0840703601ca50160000d00241030103418600c440d1951501c101703003080f880c401c0443d9440303100d20802040500400b44801c0c034040948880d01c080d0305140c007143d500e10940c09407a00f80080410342100304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 276763705 1250 276762455 276762463
    0xa0507030209130b011401110f120a0903050f150a09120806030f01060e010f050108010b0a031e110d0c02061e15040f0204030209061522151707090f0308090102 70
    0x959405500d084596075111001b8504000e030349429400240a4104200d65500008180344803051081c0544049151500440641d0303000303400075000d101d01101c001000c12020700213005c82e0300386400942001c5503d1401e00f500407800a1026017101d19085402012540202c0a14080da0490801840300c0e112800028a0215031880b40b079442d608180b8041010b0201f01300c814121036209101c043c0c0310380c48030019104140b09004106814a084c44402d4500344203070012481d83c0400081c0c1d2248980e40d445000a0751214002103201800024441e5200c21240c8030700c801c5520390707101520035814600300314200f402c100780100302c5104c112800700b03041148072aa41c81c02d184000b8001c001420032504000041d411070712040e0f1241010600007101c0e81840381526502110036004507183c030184801c00315000e0340c03801070320b1000c00c030f902c001150143d031564a030b1316802c90584030000c00048844410316810b40c000c0144041000c3d1103806c00800341003403042c400f902e501440064851440900407890 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 276764955 1250 276763705 276763741
    0x1321061125080d0b120a0302070314030c060f04020a0302060316080a06060e0118121110020d0f11010207170c100c0e0f031606110607050306010f0c06060b04180b030a0507030209 78
    0x10034010718006c0c00030140c002441030100c0780b048445400007402030780785a8490040d5840c02e4010b4000c240080c1d12181901c40f400d40c042d100a150700660754030b9801007036403608112080c0e10070320140e50440342c10039000290250b000c42e0030300c0c0c14066542030100040c1441c10301300d902414041612404400d2501603190b07080508030340303440013100c0c0b0401c2c1051a040003422a55902030b6031307035190800b1098404121150003542c1c5481d03901010000900c00c4450b003418041c101c069560034020079000810507011125001081002c043d10b038002504154280410b12500c0b82d22585003040c1d04800303907003080f142c0325817400440e03010080c0d00c2020042401c0c025074210102c030a801491000c02e0091b000b01c0300c901800c1341401140c050340d590590a48003031100740c07030b018040790200406840071485034a5009a080c4107481c0882c44c107a07a01a00e0241da08aa0024881da40010110020f501118468030b011200110010401c0085680b00d2039100c0100340000381c0501850400129281e000040e046d80c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 276766205 1250 276764955 276764989
    0x809040c0306030b07020a11060928150801090f0b1e0310060308190305060a0302040903050d1109040e160317070f0609030806061321061125080d0b 65
    0x70040c45e000c0300094551210f488100c8181c605d0305030324600c9050074400d84100c06030203400c00703116021401241d4400910700710800c074542d043d90b00204070600c091880103a070b00b50039210b400055040c1181c190544010000105405107004220151656101410344141000b0603030301107400c8141c00402c0c03e08144954203004036040c518000100411a0002c2c44902c40c02844e480c501020148200c041d40d10944809500070340ca90001c1c005031600307510001084d84a82071680c40c00c0715200d1140d050341c029070b400b081e0034880420b140c0042c2c18039000354890354a504028080a0201c0321001c41c01140700c0c0409401105001c50015032090b00501301c801140c0c00410fa41e03d1990039281c018060002d0700c000b02d0015080748085091800c000c01554545d26002d981024482d0601404141e40400a0a5209c4005d01101400086500e522840700010350032001c0356554400b6960b680540c100a0200e01e801e003820f0b0050300080f96008003512507501ca0500c4c0072600d41004e0000401311402400061 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 276767455 1250 276766205 276766223
    0x60105090a14240a08060a2c161401080c0a0c0b040f1a070c0b150a03050a11060c070311060d02032508060303041712030702060916030809040c030603 66
    0x1000c90034520f01c41c2050602d20300180322002a0040903c14145240d106511456014601103642d000481c0c014803008203050740403154a1503007146165855a424811150a0b000b02c1c096415000106075040003a00300503002110102d60301c0002860000014841003090310003243c803442c0c8501c0b0b04504a000758101c50001c00da070a2600b052015103445d84011180408075000c590001910001c03c01d01c21030086d240d0403002401c940391012100c50003050301c105083e045e4075081081e514200c040b4041e600450050401c01c40a00d0040d03038007003c0c04121842550280105400340000054403400c3d00c1d40000090403030121880481c1e0240103446a03140340c14004020010b5594240e005440d10814846000c03200792040c080070b4902460647d0f040c0d8050b001000113000045110054420000b0404110340c1c1d504041d0004076180d400640e404c200581068080c4500c0e80350800900003c5c004403125182441d01c2c5641d101402e01c02c444401c1d02503030b101ca4414603118000e5000c40001c1d50014406 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 276768705 1250 276767455 276767461
    0x305030406080106020d020d0c060209030a05070b3001170c040906020702100306030b06060903120c01091406070f0305061309081c05010503100902030f010c0e010801080609060105090a14 82
    0x10302140342c240142801445052401204188005403004044009450b5070315242d0050b01d60a010b5801042003075018800c1d00c60700f10004d0340c20000701c0000d0002c2c030007290715038811988013054540317050584030720351846580c0d20071100d0010010b58110740f00d040210210744418441a828900d00d585035a40c0103103402d50301800e02034903030001c0184503c00c80d040f00c55201a0803099003107420500002d00869901c0000890500f0201d009012400005040720b4500c0807511403403031690303c00081101c40365104c5c04468100007a001420000140460203401036143c0309100520000c601e0451808064450010401c6611017401d9030603800d41c600c0381032100040c0d6040c000c0c610740c05400103000043d40700603110366030b81c800d2003014140e49005000e01504140d201055010384040c1c00e09aa2600540b182c0c1a049e01c802d210741c00e000076641c0c4411100c014101c0000d07043d43c0059120b00480d411440810248140c08180385055403412038181c0b82e1078880c0780b00304c0000c14903051448410050720f028 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 276769955 1250 276768705 276768707
    0x91e092c0601090c03020c0c06090103020c0303010f031403040e16090b0a090806070302130e0705090901090504020f0d03051b071211030609070501091802131404050c09010c0b0c040305030406 84
    0x81d01d416158000414407040d500b01030101c00703d101c2d03985c080c100c030341204020b244d044c9006401454140070515015041c070442e01034403400e641c020f03800000c8242004008008000c690b01c201a00952994055070400d880d050b58800c070400002c0c041d00983c0081c0c41d020303103981e000743c01d00000341c54038054146c1c540310b2425014007104520f00034a0014030400001826170741c8203000b01d400311211181e010b14050f203007604002051001030407107000d01005111444180d05c500032074a0003005000780115944c100f03401132205903140921024011481c1c0344240c40440e421008071100c20004089076501281e01d52442410008190452816004111150070500400e0510040081c070100d00340d41503038440450460b501c6a01d0b12417107000c40c0c41040c080020301c0a40401000018022101602d441c040001c3d101203000c0c80e421400500031180816000384c01c0c1403040a901c100d0f480d17903551030060000c001074100c20340120000c114002101c0015031048040c010355005582c0407003200d884a8460708 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 276771205 1250 276769955 276769963
    0x5040611160f05010627050f01081207052e050708040809130f1805010e160e0903070602040e1611031902010905010905060f07080f0a020708090a0e07091e092c 70
    0x94103d601810903021500d420000023103907040780c140310300522194032143c0141c0460f8029910640b514000e00b01c8181070700030050642c12a41401268400c4140f100410240c22214050070341d804001e42d4a0030003002442d20740840d540b2103c202c1c0c120700c0c1d030f90100700c809003d0030550301c041c0201030900d15440c512040101c07040c40c82c244074400900c070010a5a0b1020789da21003004a0450b4103650440c10044202c071154400c0c2c0091408040d80e19090a03601c03643c00342d82c0140c0c8051714035190754080206003503540358206d00b460454a032034400e10b82928501580e034000c01c00310130407903410b606800051074000d40c0984480c542c444c0080c00f4410711414100d807200e40444010441c0d031946000240c04034462404079115184070080015540c5901924100030340111200300d50031202000172003c0f42d03650f07080300c000600440070100a1071030000b1009005011503401030b2103041510303184040084001c030114050b608402c40000701500302840e02441c241a04401d0140118950802c2400d908040707 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 276772455 1250 276771205 276771269
    0x160522140a081c050304020a080a081c0c090302011412040b0405150405030301060305150d060b0109091109040b15030f06010f08151201060f0905040611160f050106 72
    0x165540441a6603054158031528194284808600700c1d0807104240c134040c10265070001c1c0094030b4031104039142c0d1740780b03031504e03512003010389042c0008281c0d83e00c1c6000480118002c0b8034845024040f03d1131041001e001c1c4459404000d061000d41581508113100070001e4500754a41904810840e04140c103029500900c01d49056031140130707007505032584903a4100414092940080210700e980c1c6403240850050001905003000116000720040040d42d402c0703c1c1d10311960150710300140b08000340c400580144581e80c4444002410055400c050038a09402d03903142c004140ea010460381079590004142e04124011380c2000c40c0040305120305400c0e0014064410308082c1ca070808201c0c100c1c141a10601c504903008c40e504032010a4040142c1042c0d2041503550002c000081490364485082502002081d0020040d56645004110900c00da070f02801d4419140c400c0b5207840c2c40380241d82e05142c5503103007401a0402800f0a5004100300c03003544010000c1c140440c2e0740f650000d80c96880d1010001c58 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 276773705 1250 276772455 276772459
    0x31e0504150c02090115030f0c0509040501170714040b04060f06081f0303050c0a050d0c020f0d0c05010c0507050310050109050a0e03160201050904090507080f030316052214 76
    0x42480c500d400c40c081d03080076542d950001c048034100c0e8030f80842c207880758890352404010562240890500020325001e8845507100e140c90301070b2103074410b600740300c100d0781c05a2001c041e120020807011140c1c00089001c0b01a200e0ba0000d10b0290075035000450b010b0311140b40001d400130b02c0e2010000c0c541c0800003800040c1c5500d680d42c4441500d442902c448d108101480b442c0d042d40141008000007801100200344030031303101003659000c05140d02c1d400d0400301c2200c1c45201252807405024114a001e000c10840d641040b103521a05650030744440c00c0d03590a0b4000c648c140018004400c0501c441044220010f080c020211041c00102c40403180c0074000a11840216605080c081a89c020b03007401910109811040110b08181d03101080e21681c0a03a0f25059052200410030092152628003c0300d0b03541e4007481c001e201861400361428a03000340070340820300305e030024410301c01c058906000f418841c4200346420781e100d8000c0280403113004102c01c05010302c3c01e0320038000030728105014402c0225103c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 276774955 1250 276773705 276773729
    0xe0106030e0d03020a1b020d0f05010615021c0e01110604150c020c0f04050a061229010f060c1a16110f06180a0b130b01050f010219031e0504 62
    0x248075003a402d9024813201078000c1601b8002c8003503c28070036101d801299000a201c00c140050907203500c07229050b05e076002e8070700b65180c0b00c0c10301c4108141943c1d003802e2851480140289000c110745450f0396030300450850100f0508982000350b5a128692290b0201120b10940302c441c10580b07001620b40c508014010700b080d0078160050075050011034009804100500003550820714082040020304004209207071003640d6860200c2d01d00042031521210074440e030090b842c082c041108000c00220141400d4000790156070051003103409080364041161600d0404004603440c43c504004003130b0a568040c84491158401c0010540000f00c4810210900e604c455920f5100c005d00c694403011700345a035441030350148002c2101822906030f40300d6029000400d42d007514170660741d4444070b400252215103440c03000f002d990f400c3c49102040140101400c50388443e423103054100103500d83d42d04484058429450201c00030a06005688800c2d4104003141c00c0892a01c1451000d00143c00c00d000f085e0940b41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 276776205 1250 276774955 276774973
    0x80d0f0206010e010312080901021608040e0a020403170d2a08100b1b100c0203120906010609060827030705121812030f040f050910061407020a0e0106030e 68
    0x2400a141c2c0c1070717a41203480b030070110300e0040c4251080000074050071a10340d030800c10300c0e440d84440302000c00201c2c42611080e03581c616003502c19540318405071025030300340c0c41000100b0008442c046c0b10030101482d10b05841c0c40c0e050040301480105500c4003800703200c0030303812044041115012706001030b9104640314070141e43c480d004444520034040c000e1544051040085400070b500d092400c10085035540c040342c0001c11401e184000742d0742c0280d0104096413020402e1440b6280301a9500d03481100980105065850288000c20a00b030320b100c0c51050084500100302060a270741c007195980281c04403000d0f0300350000400341d80d4941c04554142c4960144004403401140c0300310450700544d070341c1c07540501030314441790812650450764014100c1500c4108200c100100d8424003420041048000726114036151001f0710007111001000d4106002c05c903101400915080f5101d106d1100c22041d24685901c1548040317201d40ca0325800000a40341840000203800e941a0062029028100c0550746888 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 276777455 1250 276776205 276776219
    0x90507020109020307050f1207091e0b010c1101050c0d020c040b041a062128020a0206191401080606041b020d051c050a090201080601020a0c140109080d0f020601 71
    0x100301c60002541a000104100040e21f00740c0c90140f000304004112568101c216000f882c40e200c190b038051020715480b500d034982030001e400d002c03002c000c4d280c4c4024825040350000080c002c2005c5c040080c03200319000941006079101d18242d178903c94091040702ea4050f500700c0040e50350940301202c0ca104070f05050000155007800e0182c2000090710108207000b0100f42e0b41048102d0700140b51481c0340070400f214425081c1c81c0209510700881941e03400042c98840e406034140d10528594480200c9801048034001281e40010081d50002d50098183c1102c58080b01c51400ba0081403ca507652000e0708001080342800401c850380901000c66017086034042208001180c039200200500144c0c20850b104031485004800503c1801c0002030f100c001c2c000000103d030111502500d140c80041d503581000000c550b04050040e400103404d00060506001c1690340c800d425580d40500070500c242d040b407051881e4002d03a290800351400c4070555843e0801010018192403081441c0700051054500006002d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 276778705 1250 276777455 276777461
    0x8030a1107030207030c050a03081c0209091806070503090c0d0312020403031709120a0806010309060e03090a06030509070323060414010c14030c031e09030409050f010b071515030c0905070201 84
    0x80e5403110082c0d04107409940711075085103011b06d000206503020818120746a43b5a1144ad108001e1121280220b200503540e0a14000c3c008000c2818060b080060141d03001000680000e40002101c40c800f010045113803c076510000c031007000782100e002240c080201508200000091412211540c0c1d0300c2c2d80348189580d4801030060001c00103c01008141034251041e20310070341c070440604000c42c001d481d42d074440c0304403500c044149802d600046103541e04da1505041c410020095854140319604000410300d49403042c40c0b100408078901c0141c48a0034114400c00c6400130251003007a21b50f1403405044c1500e1202400805520652900e400210400d005044640c40a0b815034501421552000c0d0f8022581d803001c0d01c2c3c131b110422640700c01003640f0200c5400b54403030861500a180c0702ca10300b20392030003916805880204410490401880b1100401c003e0702c0c08160050b0100d80038495402d041e40040a00c203c0d03640c05004280c50100a008a85200c0c1084a0031410100301c6595406c10803400c17 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 276779955 1250 276778705 276778709
    0x14030106060c0803040c1203110c030f06011412061501140a0807050f1c02090a0f0305030313032106030213090f061109090a0c02011503080708030a1107030207030c050a 74
    0x120b58642031000119000314003841d4414424031a01462540b640c80148090310040070403030002d900c12403841c070301d0401409840341c00300b000c2d0001c002400500307040039110001401081010310340c4948015040e500c1e2400002216041401c2e0381450070080760301000380303070039401d1079010940d000d0000401c070030f01d601101c0304c8401581d84d40a00d61250081241d080e4050400f0300d02d80b810a0250400b0030b503040c0001c0200f1040308a005940f52598828440443c01e903034041210843c50040400100340b0103c00c40c1d501000a80c0c2160360b10300f0034030381a9400020044610a1185480c480116420641e8071481c1624001c03504140c008078a410346030300766452040010410750066040400140d4541c201c1132a00d58022030403410200c5036400708904040c1290810340c05500e03048807040c4aa0207110312000b460881d600c3c0c00c08241180c640f0f010358418881d0080444900000061503016603038040401c0085141d14560346948906009680c3c6060b400166030007a0382e013030000fa603450881540c0381 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 276781205 1250 276779955 276779957
    0xa0f03050402182e150804150203070905040227040c0827070b0301181b0e1f0302070b010e06060313030201090206070f0b0703020c0d081e1e01050103020304020d02100c020411041403010606 83
    0x503501c2d4083d44420207502b01034401c809200303500001040030398a50002d80003104550384c040b05100010000d601d801d51003452494062032401c048455010f90294100f9444008102040c2040d071018a8115917426588140801405200c1d004100f035a40c41700214100c50212440005451008400400701d8880c1c2203903c42c100d1314500d2181a55018800c0d40d0b08592006008001d040c4800d0301c1500d000c10f40c26540d80000381d000502e1402c00c0082c08845000d040d240f0001090b510307140340401c40703511003e080368140c551240c002c90308042c403d402009125034007a02c0d0544840742c51a240780649881c00040312000712850001d48101d01c2482641c659650000003084041c0d06001c0959480074080c03e14a104552809400303480d85000104502070a00c41c809440c0c00c10741d03242c40150300c1030103800640c1014010414070016a90741080d0007000e507011280c1002c010024030b41075907180211900250041d00b0400040030001040380540116918440f540142c1580c0c0703800c0500721030490103000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 276782455 1250 276781205 276781223
    0x72307050f1003060801051f0e060a12080403050a0803091e03030c0a09080d020d1824020f011a100504080303010306051909080a0f03050402182e150804 67
    0x41920314150b111020700d010181000038a440e11850494207641c8110380380108134a0000c001c0130900703114002400205950310760385803141040b80020b003003140541303d1b0a500d4a40c0b58090010b108000b4202d400940c3d02c0011607a001516142441158004503880d05007401139103202c0145241c8a2214400300d600c40b80503612750b6851150f1104540c000307100b010104281c1503008500c45108102c00711004000303030020210112040b03130081c2104186203d86c940610101410000a0380340c04030902ca1001020810000507142e00080f842e0405ca20400030183d82806070b8003d400300030800403032140c1800c0d5215540c80300c0c171003c01e4406106900c01d0800541c030800c0100082060f580c0132940140d00b5400303900c9050341d84001e0805540c5414000c0d2068480080ca094940740c1102c4030002c21346c901d04041c042468682c0000e0126900d034030081c50204c1800c000607c108000c8174409500740090a03103222075158034107080c500001e40707004061401034000c600150482c098440b0034030880d8800488 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 276783705 1250 276782455 276782479
    0x6040b01080103031229211c210b0406050f0f04020c0a0209070302031e070e040b13020d1b1103041e180209150a02070b1c0207230705 59
    0x1702e402080107205007030242c0d0b40d41e01d0003500350212400c0c425001c02c06510700102105010810050440610005550084204061802c0d400104160a00044d42e80d040911129190b40c1907a13040d60b0a1882d0b18210b1000c1e00d044404005c84d848000050740c113480800071141c0380c0050014000c3d0b00340c805a440758020146c2c00c00d501c3c05070010f0041e00090009d90700505441c3c1e01064010205407001801303c4d4020080005440741d40644d14040d0352004804565800c29400c0504a01c0708080418000c42d26803001c00d10760748500c400005a0b124403001150b990009030049002030545000c105c807240044100141c1e56481401e03841c00c0428210003840c980f80c034000d80300ba840100100c400040048003039000038080525040308010701d001a00150b95a203201c1c0812801d03a4015145c107854500604c480c2c0032566000410748183d581e00300e103030b9950703001040046a000403118940e0701400d0000482400304a10b059040d10360003900301400140a0080795495140d044c58000d00b070f04418900300d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 276784955 1250 276783705 276783707
    0x90b04080c131d0a0302010c02010b10030504060b1207030b0a09020a053102190903031e090503010903030207120503060d03080718032306010b03011a0c07030f0b06040b0108010303 79
    0xc2080c508100d082c00541c107282c0f211101aa0480703480d0310060740e04108030b24000d154080c0506801c900b481c0c0f00070002c084000e00000e1160403900c1e00e000815949400080800005a0044040503c000d261905082e06c0c01c520355507518960104940f0b460194000c1000440790b4083c1d440b0b40c0381e00400d17000385e840c03e0800340550082e40c0f10b001880780c1c0c0fa0f030070707180140700340030b4903030854203180748400743c0c0c2d80c40c1e040700d022620a0900c031540200b1036040010004258028201c0300004045000080c0101d080700086406440507003110387d05500c2d110300301041540550041c50342d06d05ca001080f81030805004190703200d000c11900c0c81d400c005c02c841c011000920074003140c1d5010341d441c00c00407180b400e119820a400004c41d041103c40f00c2c0c5050640c2d01e035030705000b4001c04011071000100030701d40c14504841c2090006114803007111140d0106020120f11140039540c58400400c00c84444c55170343d040c0343c4200030000e98180c45204004020810314103113405010301114060b12140345691030b540e8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 276786205 1250 276784955 276784969
    0x16030e0610091e050703020405100e010804020621090706020616020a030e0a090e0a0c09020a021b0d050a030302040504060603020403030c020d02150f07050d020604030207121a01080d090b04080c 85
    0x32000e4007041032039603001c0054403281316090003108a41c0d07005031114245010b220011400d036a03040f00b444854045440c0e240c0e4400f81c842d80c032a5060b1034054568000104c0301480c0010b48802400d1034a5907000c110071f41d8400210070781110300300da084503926160650360f10040340e1030700d00301c000607001780b15a180480e00540c20784600a0010b4007143e0110381e41c0d9010300484000c40e405050940280c03040000748081c64041901500340100214640481c01c51702954880c8200391001e80d15591225202082d580e00b08020030a980150988410514501e0f0040095110340201407285243c1b440210b0300501c28420ba0701640c0c1d050706c0e0030384030515980805c5013900074107204aa2007203ca0a90001390792512002d0842680140b41140d00c030283d40c54505d0030704000301c1000d011548200704000109900140300c0381225207000d284003120f500d84c10094051126000041140c40c54400005180b540010b0502d03e03801903039642c41042030310341800c1d0b41c50303200e14801c0d44c1c1c040c2d000300036001d807501c1d02c90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 276787455 1250 276786205 276786221
    0x306230c1b03090d05010c121509110f12070219030f230a1107050d050a03050307030e030315030f07030804051903050d08011d0f0708060111010516030e061009 70
    0x5002c503414640c004000074482000c1c5041182c40780d4480441a15407034000c0c50071010380076184410300119012100301c0901203014400c03c10043e0b2241c943c4e1800004020858030350300264400250303903012017040c4010302d40050768910010302c900f611702904400441d2000c4a07440e490303940c0d441802070085040340c800b2408011000303541c8030103480c5047d00260700300510b0b8403804c580710707001d010900c84000d504010346540014080c2004003c0348000079404984000000e50508000381c0301c0d101c0042c200c0c014203d150390008244800401c0c4002e40f0b401c100700c011440c41c21011074040000c4002c05a03110b21161000034020b00d07080c80103200901d065415003240d2a0b00e520758001580d541d4136520726002c50035404001013046800148411921400440413402840080b9402800d018000e0340c19220010142c5041040c00408541c45a00c542d440c1c13000007a010000f88128280741c5110040e456030489114086130ad0710082594505010803060320600c85040c819a074249032003580c1015000300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 276788705 1250 276787455 276787507
    0x1206090303150f0307090f06060c020f04050415050f0f0a090b06040b010c06110d050606040612020d020f0d0c08132d08030a0911010809060601030e0f070306230c 71
    0x400f02807156201005048020101c1c00004075076248505100b20031030742e06402140401403100c2410700507803165465024401400e560000c1d140c2d5460030542002c0074894240d80159042406110703544209014483c00b0b6000783e1001c03d03054907010042d10071103541c0d08005000642c144002100742c641940b001d26049410705060416944640d80c600840e040c4800e184071858000c0b58504400000e44220b0f07901ca03200b5201d1615081c10008090000006654480541500014a100c100540740c05507845500f6520304a07448400d042e22850161280902c0440068000000240c074002e020b44001550f98020210142c1446410380c02e10000b4503c2d001411561840c4850100003000700c2c00035032264400a10010364101d1a1901440364005014131a04100410080c404084004070f00b29411040900780001c0000c0d0300310445080039007040c13100307840303001d000400410700c1110f0300316900307824204c0e002d4100d00f24a04801d445c032580980d01d1210391030040c4a81b80c429406282c60b81542c05031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 276789955 1250 276788705 276788719
    0x50a051c0b1009090804150806030304170a0c06020a020306061c0b0603010228020607030903120b0a150302070b010506030f220b01030311060901110a0507030e09040809120609030315 80
    0x12000c5103c00d44003407103412100e500d00040c040158502001100c064046a40780c100e52a003072050000b5900e0155000b10f184004002141410b8500100403c0380401d0b40f0042c08251f007030b5903190107510750070111016030280c060f0a0004442c0d24215607403008030741d1031411625840e01141c6681708001401001d80350159400c01580c9407844201034884080821960603a00680c600c0000038200300016203210300741801c00a950300003a801104400a0a182503400610713000d007800010700c24013071980400103400c185400c0084646d070540090845501503072190a05903a80d2003484114032045403440b240080c044040f801020001c0040300080540345642c0b6a840c2c0c580d2598242031000381c0c0214040f940c0c000000250395014801d03168000c2040c4001c1024400401319a8101d1040b1020142005000115142091f0080d040d0040d4210042e1440c100ca10303189c0380c19102941300050b540d220b00100d001d0b4900c840800512148590610406076040d40c5403500c821709051200107085a128103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 276791205 1250 276789955 276789959
    0x2011e0209010e060d1d0c030303152806110a0c210503120105090c03091209031608010c200d030f11070609030305100501230408030f04050a051c0b10 66
    0xf4480e00500502e005c170b85400100001c0303001001d45c40c07000740f0a04100d03d030070205030075501d541d0210507650301001c1d0849410004003000d0005220b4018038140a8000300c5d42d41d944042031b05241001d8003600c115131501040c409080410a50f100c40c00d40c00101452a0300009020807101c1350003800100000d251039001c0c41d54203075590f40c2150401403001c03a07000ca62100400407454030011990b003101b0a100c0c010b1441c1058942542c03141026510f10f8910340c0d000a40c80072035101007141018003192a80c1c031101041e214030f9030902030641d4483c03000c00034609046a0340344030450f240c41600c04d000b0034020a50201410720582c046d2040102c04040c83d91f540d110300003c0e0203600d0041a12a20500d0b000071009000e20340542100d031301604040310315195140510003079130801c0104c51000d040c5260b98203050241101280c00b440740e60441b02c454080480c811500390490320240c0207688086075070030882600c0700207111205011568803000c0040c0310a800011039907085079650051000d4100b400d500e6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 276792455 1250 276791205 276791209
    0x1801090503030d0c030507050f1e0c0118050f0d1205090304090c020a0b0c0406170433050108010b01050313110301022b0501080d08070c0b0c030403030c02011e0209010e 74
    0x2401a1014801c1c42c4e881c2c0c015400140ea152003015440207150034071a007070011000200196019a03c0880598040c0c2c60105c00f2290341c0d542581c40c8420608000d000003004901d8510610222843c21a41486202556015208081100c0d0764a1002d42c0e16954900032a4541b440074107030191008005000400c40442c485219002d2400b4100a036001020660190b24042c1507003031006125054114050106024a550040380401032850913030b0110243d48850400350021016008088403c04211282003e07000b130310240906028800441004503070781e151011400d07502d106405500041d000c200183c8507200d4050f08000342c2e40030b2240000c0c1c6003c590301090881c0d1000884402c00c94a10850082490450380000ea920240035000c0c03145525000c442c1d540c4071840c030401c109101c44840014442c0d4491220b9400043c2c00c12500a054103002d0040e02c2258001e8800387d0000b410000c0c0f082c006d82c014041c003132608032651181d05003a07542140383c4c4000d4100c0c0d1005410402e20918041e0b0303076 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 276793705 1250 276792455 276792457
    0x52202092203090824160e040603051c020a020901030b04050115170c01050f0a1b080d0c120510031b080304090204050901060c0b01050411040512060921180109050303 73
    0x244030361a81d06200e42005644e43c6002e542c881048030100c050320340980d00000360000c250304028000817900780300182810540e8500a07158003a5046803030007500105005000440c130080390380b40940419441e01e607040c200d840781142003020350031810780d034010000141c2d41000355900900482c00002e2401c1840c0b060810b40e4210b41c8980704103200d0950000d503600040c0170266080f242402c160b447d08008a5401c81240910b141e28410300c0312310781c41c500c108649500c0841c0500e0b0301c080520b45d281c00e03102c8484028a801c605100c00103015840e91202c0070132a01c9030a0054001014159000e441c690300c0301296504d800c12400582d64240c8009030352982000600084c01805002507101d41c1003105101207940140d10040401c02d0720400400414110840c460544006860200701455040c441a0a0344074691100e07402c13904800610710f030b006011a015014401c503100b9512a0400305030361001018510319001c80d114010400400030392280c0c800f5000029040c144074011581d1b1b0f20000b411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 276794955 1250 276793705 276793771
    0x10f03210c02120105090c010c0b060f0102071a07110927030408070303020c030d031119020c06041e0602120f091809071a031506071a1905220209 64
    0xf042c0e448105020100e4400e00081140300c42c00e1030402c3c50392005480b130000c0c0002c06010140900210210795030164424000e58029054005400050540e011031008840e4014041511401c100e051003410525140d00f2181c01001070b641740d1006001ca50130f032040d1154268401740194801000000794840c13050280d5001540241c0280018641c80341c280340c14a143c1c05031000c209482d11400450307003262042614002e1001e42480e0003c0303820101c00764681a03c0c020b0035a03003c103010600103590b130302a000700518413080198010344140e440f1810303a0384147e6204e4100c2203d4061040c08160409000604201c10000b0010112901440e00041c03104a0a50b00084260170405091100e41840030000881c903040d5400c0c41c1ca0340c0b0701190040e801403c40825035116242c0000c0c00014001e1101210b2909040d501c2100c0b041e00b8240c4400d0700540d07400484e4020070341050300040080031100448404072101c0c4001603980306503503003000325412009240d04c000c1100950781649103201e119810304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 276796205 1250 276794955 276794989
    0x7090305060a0c021209150c070b190e0a0803030a11070807050c011701060906140912030414090103020d0b040f0f110108090604050a110a050310090605010f03210c02 73
    0x10f043c01c0207000207050007405002c1c254070540400c24110244c0b117000646002000c00710400e41ca07403801c4211242007018a60012000b201c010411083d200320522400032109281d0b02ca0340340785000c160901c1800302c00d510640300c070f030b800520000303404108039045100c80e40d0391504440d240c034069035038071501d41d04a181c040e5166400055080b6907541c12144502c0d00d4104444142100e6161036002032068034280102000c0042450100f60402820b4043e00e4140200400305078131012543d60381952a04140306404a0340c112050004003401c20308100ea05890b00902400500c4003240c441240490000d0401c407168407600008001140090305200585403140424000c00c0d404030300010031452002c1c0c03003030340f05410041c01d200010740006002d81c0c0d13459001d43e60441ca0320808001424400c11030740029010b004205840f5044003403584a4440359109010400440c0d0f00d030040c0140200071800004c0040d600145010b522051304040300d0431081c413902e00024001001e5000ca02c2c0c080d07200c040c2d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 276797455 1250 276796205 276796211
    0x10f150f080c090303160b01170712061e1b03050106050a090b0a090513050108010506040219030e12040909051b01020706030f090c030b070807030e030403030305270304080105010906030201051207090305060a 91
    0x1009209e801c40407011104d80c01e034028054642024807000c1e001c11000c000a0242d40e40b91100c00c2a0050f007103403480030040400042025100c0c2d003020b05251142c0f000d10000103480c010000c43d01c64040c2003a61100d80e803075650403820743c0c00d11070307440b08950104c0440018030240b8080021a030342d41e03651030341068629010204035035241501d20342c05d40394094907440c4558010301c01500e010440800c08480c441d00362070081030018203600924102001a405400c0040b0700240201e50300c21a5080048168492002c0301c1d4034a01010088210200016103140140c004410400400e0710076040391010806842001403107807040d94400803001e006500c04c4400040c0c134010414041d40000354954401d007903041c1807003200e64091002e62280320318000241410355900114560340c44140c1d0304e081c0d6449010b00c841120719003080603641c2c0e40003407140e13074115802c0c0030000c036010b401401103e00b200c2d8107848603400d040c498503486045440003401b0500708050349000001003881000664041d0b44025000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 276798561 1106 276797455 276797459
    0x30f08100902190e04060b09090a02130f0e09061b0a05070b2502030901020d030c0c170307030b0901080a29010f150f080c090303160b01 60
    0x241403070720300c049100034885101d060908200009502d0f103a9000c10150208025106c5e03500864004100502240200342004a040f17500300314010340250400c0242008000c0d002e409502c00b00c004028088100685901a80500d8110080f00c0c050b003124900510058129030b080944040e002c44005480450a4420000c0d105080d0717000003050014203203522408902058001d0702c07050003000d800c000569a000004441c1d80c80d01c1070300603100c007440f440300950040071104001401d00c210090b1510000303050303180c5188070080242e0820707124144908000c00321303070180140394003440483c40140081c280010f8261042e60b40b0a941040301b504a04404211100c10716600d0741280d0480008903a1401e100300000076103c01400c00c0548a502e048200c62201c0b0031008040840d49020105141c4c03480b600c02030410600240840c1e240406e003230800b0300c0c4101d1041d000e8403103031405001 = true := by decide +kernel

theorem cover : BRFrame.Cov 276618705 276798561 := by
  have h0 := BRFrame.cov_init 276618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 276618705 ≤ n) (h2 : n < 276798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
