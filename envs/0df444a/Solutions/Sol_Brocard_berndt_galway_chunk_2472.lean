-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2472
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:49:46.144976+00:00
-- url     : https://prove2.me/submissions/3922a342-671f-41c4-b57b-2f8cae32e6b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 444424460 ≤ n < 444604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 444425710 1250 444424460 444424471
    0x28060f052205240a030c09020d09050303090312070903030206040b06040e010c020c0a12051203060d0b10050a0e070215150301020c03030f090f060a0c030b0d1b090c020712031e1205 79
    0xd13510204000042000c89503006440142d4030140e25107040c86240700143c494610010030f00c0c0004405c00c2802d038000000742c90100c4107641d50b0342154540080507030302c0d10401d00010f0010303040f4030b0000f0007082140b00c845401007009080000c0580900900d282144c0c5020040710058000011042071841c00d500c80f400680001d403180c84000c030b816910a03035941ea80ba822039040400c04000100190b442445503591079821004944403440c00c0c1d81030442c942070901655100b4625220085000c44910441c1486145590020304240388290940145c8078402000c50401c0020b0101484058030203001500f0001d41340401182c80c1d0034040c5c08414008401000b1100315071185030707451980b03c1c000a00303a400c822102c0000a04448510b8110044d10214840c0341e0041c000c95542d8040114041304002e0821102c500030f403489890f40031041c25106502c640c1001039110010134000c60b155805015156032280c14540c49034022403902070441c0303400a46070b0b408a01c03c81c26013080202980a107980c401c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 444426960 1250 444425710 444425719
    0xa020105100f0518090c0909010204030b011a0a0e060405030307050303100b0c1015170a03170721090605070807020c0f0108010303050309100528060f05220524 70
    0x2142003c0c007140e0207282c641c207100c614401c1c481c085401e40000f80055507184002610082991400d500b4490217548240b104031101d051600001603c00c41d012181521441d80011440c6400d007002ca0489603891803081596200c003003000009042d9900708010110988a08051034176442c28400b122001c41c06940180030002c0f04000118107442c000c50050700d0449800b4002982170a6000e072203012046907040020f544603040604610b94800180c201d2110780311380c2da840c05041000c0380e481e180080a88126000c40c2040724003034070080c400700d09043c41003d0400001100e070090b0310303000181e500598448020904010900c500341e03505104090310700509807808001168698002051144140710103010040007001051001c203041c02160346055880000b032040381040840f842a040481003140b000901001021110001502a0320121004100d00e1a17002c1c4c0392005101080364007100c561440300341405140c1e9400300c2c40c8500703409100d00380841c2c04481e55114401c0f03a080c244100382d6104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 444428210 1250 444426960 444426989
    0x30a06030b0615190915050304060b040911040b010201020706051f0b2b02070f241e0e0319020d0908011b050a03060308030a02070606060c051009170a02010510 70
    0x2c1d000800c11030b0540c02132105803403100d2040003c110390440300c40c3c00000c842d000348142d20501d01d40c89070241d13010b54001c180800495070030030700700b104803016804010400040b240100c850b07842c1991040c2441403041c000540f506081d03a6503402201c50841d682052211510411003200c00c1c40b14050018248081056180030b00c1c091b030b034180c083c1c541d4441c544e0003600081c0404803c5410f40580309400e6022803105407000452030444000141d462084105035110007984401c0c0c0310780d000c1c1d030086002c60001b1441070700312429241d02400b640740b5040710714403080009640003050b42e0150390500c026680503140c13000b1444030040c0501d0302a4801585a0b0406500c24000381d08004955040c28290a100d035890020700415406008035074409412444003000700001081240c0051000c43c1c070407502086440d03142c090945145c5201c900103803043e0701100841480544547c071500380705000d01605c403002c0c0200d0350300c0c8026922548003000141d440703d0034001d0a5118400840142c498040222038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 444429460 1250 444428210 444428239
    0x3140c010c08030112020a080102070b0910150509040606050a0608010509070f0219050708100b0307080d0804060f020417010f0c1e03020f040b0c0d08100b0f070c050402030a06030b06 80
    0x21a01041c0600842220b8145d940821940c492442800500940b4001d54480f0441e04100c40e1b000b604031030850440c0a00c280040701452148201c208041c036904103100b010342004140000e003840180100c898940d1240042802c2e0784181d01c00380241840d6542002540c10030050002c09000641444140022104040601c0d500410084c2400030300200e2507894a00c1420b0440c5080581e500492040c0160b5140361300d0720041c0c0d00180d00001040d411221195035400110b5075901d0404104000a94514089000603a050f08420042d000e181c1c03015041540350b44d0412b400040d010003009280c0e550701c0d403030700c0808044d0242c000a0561030800c00c035000c1a02c1e0b503031103202c1442e003600d030b00301603000648040a0034028240c601030244045019102c030846c40c0b502d07940300800708160002c50003180c00512411044004641941d5441c80828201240061030080c160030500e0b0031078001c8401c03900400d15407524409103100700d503c0300c1c011540d02d1660a00c2140b618019200b20300403e0308100240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 444430710 1250 444429460 444429473
    0x80f07052d13081501120f060b1009030b01050d1223030106081807050a1505190224070518030a330e0a1407030f05030a0306090b010905010302030712050103140c010c 73
    0x2030342580048040340c20b02c100b031400200600c00d85132701d25803200003800c4102c00c0c298040005c005407841220790040c90791700c407020031130b00c3c1c505018002c140d0007044441000c0c40d8452082c0c4081c3e01c41340350400c0c464070300400a24023142c100b43c010304000307101001006417041031a010400c80c40c5001020349412814100800e901c01000c2c0110403011070340c40032002481d489503007180c4501c00a0705c03007480e00d0010440000d4a408031020107d501c2c204030003500101000414946024000711703100d0f50324050600c4c401e60b120010322400310b5414016042004041640c5100c089907602421640e201540400c100c0d100c02101420b10344401079240c640341d12a60740e00010107c40c06030304040325100d50145507160b2894409907401c01040304d40094090400c1100000c0a010000469282405050f4464442c502180d02040501d400154461000c20071540079034000e541000d030520f044469424484000c9007522402c2c0e004496a400c0d910f5582a901000c0c09031001201c402d18002c114511951034a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 444431960 1250 444430710 444430739
    0x9030c060b060d060e04021503070e13020d0e010c12020403110f120a0501021c0509030d05040318060c0c0503120d0b03072301080f07052d13081501 65
    0x424195549003034078015507035201503d0104003408000e02661707485114200d007a19040e075049014010f10220b5991420108050340e110b120304e59903030508176240004001c20011403c41c2d40110130740c00c0201207141c00550241112007024100085880341103250010500d0307030028840c14903540305000078070014200c0780e0341c0c0b48001011076000e4210703803050000801c525010f101d07400c454401d24210504116040d0060058031441110300000c0450398140300065406c125080141900304202d0014800d200c1d81c08a40c002c1c5c0039251062000e661030f0040c01d0103180c60341003800422a01c0301520f0821080060364009004c0031b5021340306501e00b1880310503d90083c0340403203607060786803030b4050142c0e1810440d40d0000c0000301d030031100c0403445400000a1819100c1140c0c0003d811720001907400110280361030044285640b01c40c41e0224021041c1d503041a41d1010410341d44840e1600a030f00c81c03980028200c0301004c42d400342002440c14404a00d04652071402c030f4400c025103001000400c903190042c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 444433210 1250 444431960 444431963
    0x80105090606120c0909120301030308010303110c150304050708011d100204050306010b0a1101020d020c0f1203060f010e0a090c0207090b030705060703030b0901032102030702030303070311072f0409030c 89
    0x154101c54884082c4a400c0000007071f50740d0703130f00c040100002041c55400700705941283d009440d1510003120800b14140c850000388010b9070803888800d8180d09052a1034001c6500502400540b80403c0c0c03500c118600f516920741040c02010a40d001e0605403000502c0a10010b5056410451519107000042a216081441000104030700801c907070304143e0003210646a4118a80003c540e00e5005000d0b200080d00040d070300810901c074059080a44180010b41d054841412030650780c10b40e0b0f541c2c03040201022a1030002410400002c48424250300c40c14861805481e003100086154541640020302d4101603074045012141480c25107405500c020442c2010b941c025140c4e5503480016082c241d014021140006800415001c000418003d0301500039144040586003000002c0d1805001c9a41e4050325202940c15013082010030405c034000d83c040303011f890411400506014150320352450403812801148001c3c1200c1031190310356004440c21000310801120200b00143c0d10b1340b0001e2100c0720381c840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 444434460 1250 444433210 444433219
    0x608190c14030a06020a080403030c020c010c082a060a0c020601292802070b09010e04050601020705060f03091e060703050c0408010c050910080408120c0f04080105090606120c 77
    0x155241c548083c40300c0200f031138211009550f9403120790001002007500b100e0070780c002403a188a90f41c0d058408101d07101140760507036600708450040d4840320400c3c2d0040904090f145e0440c0740400441c10044004041c051b0000064140c2d4500120311006403200c0240c1d6a0440d002800140b018508550007403041e10707001d240034060302c101c9900c0303003d642c8602a25255526200c001818100c02041400c040c040c1565003500d20481d542e01e4207a481d4080e81c0f140354045845580000c0003400c040c1e000030350041051040311099030b900e0f00410501c0c0d0201c210b0318100c1f40c0000c10030554507000c01260342a42030f054240400040b0600b0307080c0e15000007800718020161900003040c2002e403088266009002da480007044441000130303015003e5070110007680e00860891204180c107601400400b44503541010103a0724010680440300b403028001040c0c131500800c18800780b0100507007003019101602c4070b00000142400d04062042c500070004041900c02e106108040da00c0c80741c0800c00d5000c40d20141c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 444435710 1250 444434460 444434489
    0x11e05012d0509271915270c0806070f12060b0a0f080a0e1e070e0c03180a080a0c08070f0804061101020a05040608041407090608190c 59
    0x142240004112a808107074028015000c1c03042990045101030044c0c110102c880440c400480072554035040c0500e04083c030300710042c1c080d5001c261003450300d0a5070860100002000101d140c00010709203415088045180c20901b60002005030101401010f004000000c042501d8103407401420703141c1100a00c0100801600f004110403840d400501c041c0c00c586c0d9001d500e032040140010440551482001c0000d102607010500032482842260341c041c1c190406000004040709900036a900854028941c42c03103000d07030014465103c082454001d0760f11441c60f81c0e590034204110094070108007100041e43e08035900395400120b10b0011194010890700b4071416203202400c0042107801f80043c041c00143c1500000002c02071031800600c1529840d88643c45080c9007503441c0b500300d0107040540c0c0007050042006200060040001c1c13641310340f24440704100c10082c540b00c58100b40c82035100e0031015031640c4d030501000c1c005100130710414940744400029502562245010420b003445440b07a0b0403100c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 444436960 1250 444435710 444435779
    0x101202030a02040c030506011d062a0a2906010c02090c07061401051801030b011a0424080a11091002010e060112030813032c0a08011e0501 61
    0x38000740c20000c1c1c00070000c124488641c100a00500b101b124194009211104885540d0624568200c8202005000c00b410711050030401400480c83c601b40900054000c0d91b681401312040008400c1148036070080c900c41510040103080d0a048101c030f518240001c0c07010071002c0d07684034000d130070080e030100c13500380598940c14041c0c01544140400030380710b00d06250415403440741080306641243e000340c8000180b0304a410001168100a000052044110000420144000c00c001040c2005070941080c5019601c0c0c2d9100400b20484a0040707021170340c08a01c620342500f05500c070740d000c55420707020300c41741c285007000345020311805001d24859100d06002001d01c81c400d41c442c030426010f4904503051540c4030b21036142e4001000200f180002d000344002400c89101c02203084c00d290f41a200c174105a00902c1e82e10300c001e5240521144056400792103c0c5980c0d8030681d51000400c082c400011308a14064034100d83c00880620344000c1604120040044945c1c07100840e003003a04070309440150740e950 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 444438210 1250 444436960 444436963
    0x4030e1203220506160f05010605061209010b090c0a0c05190c0f050f010909090f12110c0307050604030b070908070b0418050f13030c0501060608090d020610120203 72
    0x840032520600c00481d60401c00c0c540340c0144507001441c40241d100d02a503036400c103d001e1246014120a01081a003180d0020701940040503075244108000b08420341c4841c0458030030b400061079141014180014004200f80a00c42c80074403a000f650484240c1c90107146410031445088001801c010b05858020140802070018005003d15000c41e003104003c941044e1207100007900990000078043c03000001e040c58110803da403010300603120801c1440ca000c03808001000100c40540f94448044000e80025840380c0c020703948140503071503003000c1c103543e120014031300f040c40d51070749020b540042000d00c1643d50700010b4a00b00e1390b2100300e80302039548444040f01e000e4000e605c01889485044c0c004030305540b450b8003500c01d913111401c462600031041c121f17040c01d803403041c2c450b60f0078101c04801080f126400c41c9042e001a50090a0021005500b66119421104c50b035000c02c0006514130140040700d070040c4405040d21129100801c80b5007055207501c4440c0381c01c0d1040c0d41181c00e140001c0c01c11500e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 444439460 1250 444438210 444438229
    0xb031b090402070809120106060e1507050f160b0708070b07020a06060b09010f170703020d0b061204030801060207060503131416050a090e0c1207050a06090302010f09060804030e 78
    0x809407040d074a6041d2841e0000a9412070100c05100350812803500d4071000c3d0521a860840720160f40e541c4449004206111040c0c54030003070342c002c1000070001c07580403800030001d00e0461684140104440030040c0241c1049505079045803a16600030000480455100710503189044d402040250301510b40e120160314186840d08018804c60030003900007003010320380b0060058040700783c032040d10f84050250200c5500760b048007403154000e034003804a151345201c0c1d80900445031841c0e200180d01521711000488503084100c4c1842e01080100401c000c066010031403030300504c0680000d1568a040140c0540cc900005004003103070b84d0011848c40622840c49440c558000d051020354004543c0c00506a110b40014010240948812503001501095601c61000e05080c50303000f03000034506e02c03020000802034107021803040380304032800403409a6500818070005c000c19111584494618070000d400201c9018858080c03040c2401c0030040a034000101c81c5c0e00c2a03051400700c000c40d020500041c0e0000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 444440710 1250 444439460 444439477
    0xf0c051203120a240b030405100506100c0606050604080a060c0c0b280f0209030601080c010f0e06040504050108030d230112050a121808060601020721080304080d0c090b031b 76
    0x151500001c20a06010007140201c0c054802d40b1150b000f030b20161410740c0cac2c1c243c4505801469505400000c14450460b00c103026114000200b0016600e000223480d541194001030082d070888120401003141034403c0601851090402d051240060f446180c104900101007110b15441e41036100030f83c9050100541051a60b2882001103040c4612030000940015207117600a100d4000007007407940740010540c8600300305a6940206408500d002c036007904020950a4110314203100c00705903660355004403400303025200e0041d9113030f06a420030082074517040400459002d081c040910700381640342110a05403040ba0f050a0900040d42c60b100345001c2a03d6005017032005403a03260701089900c100c00c22034080381407020a036202d480b0003089480b1581581c803035026a200c02c0341040200142c0006140540f00411103084a00e056150000c080d13008450031500c002c00040d05d9000c24980d842007030010030321450005245800d09c988504184006130850342210352922030080c0380600d210840300c541 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 444441960 1250 444440710 444440771
    0x605030102070c0302210714031c08100b0309070b0f0c070609050307060203040f0905040309080a0602490e0a0c0e0f0f010915030f0c051203120a 64
    0x501c241c2c1084840f010060000700d10800c00c629a40c0c00f00400302980107001d412a101409060b4030b00800c8007443c100003070300c07550103001d8a03c200110068003510b40442c1d0505440398092803074814a0317401c5117582c540204135400340034004d00000d850b000a0801c140c40610380c1e00c0340e41b044821841c1403540a2125510303031910401502051b525444130b0540c0c2125415021928480c1d100d12043ea1a4003940c06680c0040036030001c108000031054000030780160003401c08000a5803141c21301418590320f0101610b0305600028030383c0075224510410000003544100c038007040c90740d80802480c44c1d1070b124500020001d0318100b0203d84141540060706101200f01211802c00040c6082040c1202512425120805401c000b600031000031044522428480b00c1f0000103070308207000d180c010485c1c540080340d13086c0000d41c00b10000d00d5901c00c0b501d049001d80a905100d615080411003030340d0640010400ca030704148412598040c1c0d40c00504d8001c068240302182c1c0d003200b090500c2c3d02c00000f04000400c0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 444443210 1250 444441960 444441967
    0x110609030f0703173c0a0525050c19050c100315060e090a021e0c0a0803090109020a060e240d061205010c020118030c050c03120a1107030803010b0d0605030102 70
    0x85c1144080a042c1110b504005a9202040100c44030701c0b440320b06807002011908500084c1c005003c59004650082c00c4654550080344401e4a01c442c1d0704452000c4000b24400080030481c40c0302c00c005803030314003d040203c1020b40a403943c49580360150000300034040c8210b50741341003646010f0b0301f02c201d41c0e034602c0c611009800d5680c0d00040051b00c055603403902902c140404a480a0f0711070080f69a0f2903079400e0381d4039042d2501c2c46401c095034820070020031140a00700c0034600042100300298001c54051002040100742030040102c0312040350f100b0b0003801890728a41310721f40c94070032810801826144003407146604610248900b849004071030112545041000315680e9228081c007010303180108001c0082d51141501070b0f003213403041000380c2035015280d80a180000e2084d07015450081c4150180c1d0324508401c1c000c41d107498656840800d00200c0446c000115a61100040b4410510b48000b420900d06e5501c1d03440c1d40b88018040c210213076400060359500c84003660807100041c07070301900031541d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 444444460 1250 444443210 444443221
    0x6330a050703080f1b0307020a0c030606050f0118170102072a0f06080f09100504051c09050a03060b06070c0308070b0c07030807030c030b030f030a110609030f070317 73
    0x950741c4012000c401040070701c2c000c07864084044103041d209000303038440160100c00b40411414680c100a04007011846003403011800109401c00c00341c0114814107011078a40d0a02d82000401c0c801c0103555810800c0251800c0604010400782500b118012007090507007901015000b40a03210b81013000d003903c901b0740c1100e24050705003a0103051f01002c00c05103407a0b0f940c480c03410580203200c1c1c0c0b28210000f4070a0000c40c0101c04c0008145070840b125104485240c00005909030964008031010790f0690081589110103086990030100f004035a4a4404c00c1a4280400509114840e0101409150b9200c1c000e00064030f07030404031115503800549980c0b080e962494500050344c8414003ca80c02a990008292003000000036600d4286d03040d141c2e000d42d5610810214000e0100300080000c05072a210501082d441c20b00c581101c100000e40030756a5221102000b40c0650031034820b04429034401c000700b2803000c90200075541d084012240301581c0d0300030b43c04c08840002c1d050043d18298804a4244003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 444445710 1250 444444460 444444467
    0x70306110307090f0b030402040f060e040f0302060c0a02150a1118010905010e0d0201110c21010501120f030309050709050114011116090b03010216050607080f06330a 73
    0x42c030520320350707a48100079900d450408200000c1c40c0315440c58204140b02003801841c05400c210040180460001012603558142c040000015030b4245c41540d4402d00507414140d051055562204500c0081e9252444480d4004e5031101d4010041d05000b00f1070000c101181c005400a0210072402e000a5440f0707040c0000c08000d80c804250b1242c089940000d001075954015680d440501030002e11059a4040c29001942c6040e810b04000c03095004545200c02107503903071006010f002c43d40c3ca1150308030b0714141310041d085030310682092140f01c03c1d400d044000120b00600c0025410383c580303004620344059151043c60718000c1d4204210450600c0008610f001c00700c100c80503050000d9850351001460b00d01d402d03440c0c070540808e00c0404004a042030000703000d650040d0a10040190005203010320b101c00b1640c20300a641801c55180c0c10603018000c2695112240c0c0c1d41110f0030803c151b00c241001700020b192141041040e403101d110300705080042e01154010100e609a03a60005940e651f21150005c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 444446960 1250 444445710 444445717
    0x3070b07020f12061006032304060b09010801150b04030804120609020a06210c0509040c020c0a06200606030c04090201020f060c1905090d02061e0c010501090615020c0405070207030611 81
    0x2906117a58510001c0d00f144603010351200781d988510303458080401d081d007590001c4030003001642d0050301c0700c210f03040b03070b80341d08220304e0007024a0f4000144e4690b071120b1000203481207500034070100e40140b00a0000c92201c0c4100c5007111004440700b80c040c03410b49001d0000d408030b484c01030340c0f201e1203020000380b658100d4124880d042401700200d030f0031b5a1001d03040c42101c03602c0c958000000c4090080c2111420294401141190070340120f07550340884000050350484107400030400075980d40003007042180000d100110076504c80c1c01500e040e1501c000031903564900c6101152160380c0355010907056900900184d01d0705480881030f02c6a5251050f40c03079039594030480c080302040070310220b0701c2c0f4500c2c8103000362042da440007070040104200703a800700800c0760022640303421190301c01d03083e1b0440c0302c1d6403500a018110090001117102e40c54030640b4411250f00703034040781c080d094200700740c01d04a90205800d440f00104850001d029101c1d071000700d24001c15500010300d0540351011400c011415030018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 444448210 1250 444446960 444446971
    0x3010b03040b160807050d09061b09060f050909130b161b0b0604150f030c0303140f19140a050403020906030a0c170c0d0602120a0b03070b07020f1206 66
    0x82d00d00030703120740603071030103590b6106003030400142e03101c2c04075141c03900c075000074030307041c0500d22021a20b05025182c10080711a4141050000c22080d40500505900410440001e12050070b0034408a00c443c031001d003d9200740f103e41841500381c4400541c1003c14804106102500052084010310f4251041d040e104e00e100181404248805550a110386e580001e0b030609a40c032684120403902d9220078803025103802c00c1c08201c004001180070809000315190341c00218001c41c00010150320310b050260864054140c80c051242c0d04100304040300549030112480794400300c421140d000d081800c1111104055401c07030201007400500f8a2920780e11001500c140c0e8007c0700c5103001c6803280e800705591000d480340000c00b00070089004000003160300c82c109030261050b1081e10301030b4200c200000c0300707003a1400084805a901089030ba040c500f611506940c0200d5032002080030491140020703035258031340e2058003920980041d800c011901c0d03400034000b140802030400182010000310172a142e40d000c503403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 444449460 1250 444448210 444448223
    0x20712020a0b090f03040905040204020d0c0203030a0f05010f181103151e010c0b10050d060e010e0a0c050f010216090209010807020a0206070605072609011a0a05040513050303010b0304 81
    0x2081d840000403495580d084d02200c01549080c0c5400c1c903803009400d0042042e17038816424807074008010002e00039464501101c0e400f445c0d230703468556542412070703101e070400018192404006121049040f000c60003070703039002c010805c002e0940d58100c901508100540e195203080100034001c041000040f01101d04000300e81c1e01d580d140e511043e0f01690005c1004640c0010491421200400c1e9560034603038200e480c0320051312060380c8030f00c0400d0700d2015100d41202c007203680e0001c90503006000c0c41400d244580620103041640495103644034246501e00542d1711a402a0303c141007560700070070101000311100d0710504011550303030300603070029004404003d01040310440094005480850700e081c10740e07401021207050100030b03290100105001485c0c0001e0201e045880380e0940980c83c0702003004641900803411916189007160300355107091079002442d4058103603034251503541c07204c03000940f0810345001480c1d64460072811000c1c030107e10301510301d000000010030480d4071100254803986c011017 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 444450710 1250 444449460 444449483
    0x1020d11340e04050c060c1905030d0c020a0c0b0a120f0b0906060301030f06050402040f022805040b0d0c140f0705070e16120e151b070c18020712020a 66
    0x2802d441014004480041040e0014000d5907440d140c100003a00e4009248002ca40c110000d80c624012004244c45080d281c652011034001e06504d072600030220901100c4c8090285608655641680c0640b5401800b114101c08505680c2c1940304486103030228032410702c1400b2a10b0481c024030024440140c0042c05040b903000080d60504100d41102e04890b4411616207106245841c0d00004000181049a1103910b42e25040780f1015140003174041120f000b02c103041c1c82000c0c0d142c1035480400044581d401e010043c48200065145141030b20f0b091102c40c007000c60076580c451380458414019560f98880b01c0808241d200600746d00c02e025100e00d500c10170896200b2921510724225000040b2002d417606800806c40350007a80c46071030070650000041602059200d0744640700d6040888160a0851070103110f01001000355111300040303580085594074900d012010740340e04515080900a03e11080302807103040c0302102440e412980740c0c83e0804c030303102041120a00001d454000c107a0058540a0661 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 444451960 1250 444450710 444450719
    0xd08070b010b1921020301030308151c03051303080a090312030203101403100f0b010806090f070c1b0e19111e040806011d09070501020d1134 62
    0x244102c1e03518000e0f807006410f5002c4821000c4079100c06600400c03055200d0340c405070944100c0b07400038501951194440c8429860620410014003440e280d542c0d00c0307442115410304d00b980e114481190510b8141c58040d5890509801a4000481c00d610040089078005403405820743d0004407002a2840344112405100c40100220309a00040d01c415412800d007840c1001000f000b0403c0d4035083c80e000d801e603500c3e00203265000040b1110003035805601030311414181c25640e800a0300550040007250030707080504005074001240c030802001041801000c1040809104221a100f603038401d015208403929901c55000060701e00702603603440b480010145124805150754001c900c450031003504036a05002c1001c0d900c400320090500d11140c500c004002c041042101446030f24040d04020720580d0380700c50100b1a021040700c004208400c00e401c140024451031b07a0208900c60a5010761800103500d0300c1e500b0145081201d2056040d42c620411008541a800180c0a80754500c06000c0758840a40e42c9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 444453210 1250 444451960 444451979
    0x1009060521210d0c05131e0902030403050405011704200103020d020c010c200303070c0206090d030206092e0e070317030f15011707030b0d08070b01 65
    0x980100d07640000d1001111812503070705000500c0845100c02194100c0400b82e15603080785122005502c40c0620006010280384990301902014075802e217860703850310612a8011102c00380601800c00a6007074032144a8200c10000c8003070010b414810400c40da01c0c02d180c45c001c0c115074860303c1600d0100340c0900901d0301c41d00040f0039141c4242d030000038050401d030340d4510403050b401c4a5295281031550038400c1c0d0030a9403140c07002d400d982c00100700028689880c4103015081600a0061500c0050000c406641c184800b006503a00300c1d01c9800d0001021703445200003100c034000e004820344c02690000c0b090003455400100702e40950028000d0b10b40103240c0500712980c1500d160100c06c40170000380d20382880c101d075a0380204800285c620582c0e00e919142c1d960003540100e00ca41a620101020047c820300700d280c502c8c1d907a01303c1000440024441e4000c000603000c0403c0004402d48003c3e0307400019000c2c0c1c0641c01c208440710000705034086c521524500350182d900120015100e901c802000480c60882 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 444454460 1250 444453210 444453221
    0x30206130e0c070b07030e0c09060307170a051006030309060503070203040905040506160503090c190b0703050309010b0a05010c0f24060303020c1e0616050303161d0f0d11060d051009 80
    0x10005023140f001c2140c10702401e40c07005071035075407d84600ba20020300361418a031007841c0c44841a018103601900317820550324101140c28888500c5140640c2040042c0c0c100a96a003141c5890910702c1c1c80743e0f501c4000b039086000f19440200030030f0911017044104038000c81c280c0c1c4110041c10301d41683c041d0080c41107410340400c64800b004d541c01402d034005a4031700800d0800034442c2050302c031084a80c40781c4241e41640c21910044002c03c42c04014000301ca8828020103100c20030503034036145103500d403000090020313610744c0001d0080e40c842031411080c450b07641941c481d150b848040c4001e80c144045842c40003800c06110540050152030421701c40c514080c2c80030781c15003410b000ca000f41c0b280c00304208000c82d4444070701c82480d0b0208580381070000d1028400f440c0b2a600b4229003500d0400142d4001e02052148030f0030454143d20207104100700c0c0d840309010903001d281601c902007039404904c0c2942e40340b0070116180703612140100d00b2110100154124512411000340082c001e03550350081c0000b600c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 444455710 1250 444454460 444454481
    0x2a080901092f03030703030e070e090607031e0905030406030f230903210105010e0102010213060809030714010501030311060c030613020702090f0106031113030206130e0c070b0703 79
    0x20800141a9150810100c55000022802d4a801c2c60402c24000107440d6034028a001c60100e80c44401d015a0441c09018201c0140000d1165429501d000440c0c107840e000d000f842d00707013455a14400581901c00d150011070030352032010403c215010b10390925940d690441d11900001908043c91a4010045401902c1c803107144075200c46690340c4412203141d117125001307025076010300c014008050380c400c0c01c10003803001050000c1941015410b100004080d280900b000b181560b0041080d204101024100c4030220360107890031800d0f079211000d1890a504c5155006412501310000c41e81e0b0f0400c040d03101a04880c0b290322062103583c1c4404030103441d56400c8900300d510752001d0001034440c0c00c0c03401900200744807041d80180b0380212039002403440758041d0b9030f41000d051100018400d007034042c402c1d0110800c8444045041440c620442490001c060000034041d42c0c0c04160480c1c0749110040c864080c2207400081a0f0b207252039414018a90083c0c20701b034503214a040b000c14004e6019116101605 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 444456960 1250 444455710 444455723
    0x1707030f2408060603010204052b1703060f0d0302030306010c0c050a1806140d031209061d0607030203090c010c05012a030f0605010f030b12070801090303140606030402132a08090109 80
    0x5410248040c1c1d582b007144004280346540310b000600041c0520380d25050011200c20720540b40d090000a0080a01a0320003290284590031000d0700826000000e5962005091800c840291a58070b0041c150385066400b16401c510005c0c4007003020080c05000440c00210480100244c1d60350705420074518942c044840e8100c40c0500c2c0b030101192103a2000c0003c0344850f0070119120754076658110031540480707170645084c0c05c0c60325166040c03141808601d400508134a025411402d00031045600c80800d400202c3c18031010003443d000f0441c013034000fa601515504050303c809500c00034030804240844480d180007070310b880100d1030303020181d10401003035030010307904c14a05203416003081d00141000b2203210b6111500c01d11681e0071000801c11036001d400345100102d04401c0c0c1d4500501030390480690030890b40c0743c44c020803040c3c1d1121300076280e00076011518040c48400d500705440c018403014071045003282036000c8010b030f5084640c00e2a24903003101d640790000e59443d00940c60803142c03031000007883c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 444458210 1250 444456960 444456979
    0x9040b120a03081f1712070804030b0601090e0c09040b04020c0a020a0e090c01030504150903030c0306090536010e060709091a100e0406090605030d1707030f240806060301020405 78
    0x54101800b445c0d205400604120340340d02074a41184025500840d004592000c4000b40a108000c104824250041d00038200842c055003000013840f0000030080803000007100105001e1410b540c1e40c1c00020308400f010f001103590302c1c9203180e12915010070801c00ea0007006001c0000410044002102c1d10584c245d2010b00320700c0b01400700450141201420507a5081c1c40c0003514031003c50140b00c1c07003d8243c42520300044550f050301001d4140c4450340e10243d200d034646003c20880380140c2c407060680308002c000c0205240030501028451200c140340c500e0840d03181c42110113008100140540c0982025107860201540d9036038a0426110002100d040c020f01c404203250050818014109075403d06050108802110070081170880e82c1d9a0f03c00c481c002e882c3c00c002c100c14107040c407190b007802c51246000e4101c49500450540d9800d0081c0c076200405a4802003401120120b03072003402000011500d00758055103d0030740070851582406032444601a00005c64954a01442220116480941904c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 444459460 1250 444458210 444458219
    0x6030203060c13050d080702031b01180b04090c0306150804061107020d020909010f0c030605040e06060105030c0702030c0a15080f100b0c07090e1e07060c0809040b120a03081f 77
    0x2c0c203817684403048815a0080c0520b000507601840b03034001c6142220200740448050000050401102e03c02c42b4103404006130041c80015241c0c0100ca00340e550201c0c000c01c030311050443c00c90040c83e840c2c0c80f0341d480d0100c2d0f0484103c85a030048815000b58002c10050140c200f04210002c0b9034466104000c1d440315940d0a650f0060400406a0303171b20410034000041c0f10788640946c0000d03290040340050020303984401c14000d5140c0ba1180d02400c400c250010003103843d24070000381c007505c005058000f10b0750020440d10110365081003200130010b0b0160098640e159102074900104044c5411040896640300004844d03440441c0460700ca9095070114001c5107140c1040e0038110b900c40740008005000e030312008501e464090107a50340c045204801070441d00e01880300c052030214603060017441a04a400200190344d4001d1400095942003019966a11011000540248800115540c00038505d8030b04002c449004110821001d0090325259040d55401080b03544008021003500641c6011410620 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 444460710 1250 444459460 444459469
    0x60906020c18070f030b030102031806011d0601050d020c01090f0b1807060f03060e0c0a1206060203041a0c0a060e010605030a08030a022208010615181406091306030203060c1305 78
    0x14603035105810001042d901b03401c00b082c01c0e80d00c122844407265000c0c19101115403000c0161070300620002020000e418103600c00d811842c00c002c0c1c6084c6c108640410307508910344165040320b07440d0360244000c0100314600e1402003491502000152018122040003070848065420b00f0011050080081d049440c2040000c0d501036510142c950708055035072002091620a05103c280140d40b1100c1d26911014140b40081885d00055050040c0301c0c2803040812001390000159015111904000e02c0e03425040b2550040a0140403120707a81441502101e105101a60b03010444c2006594000c0c4449078680060503a070b031800010040c9440420000180b40312000ea0203885030304846148030700090384100d4201025030003a008911141d55a0400700320b00d052148212615850b281090300c0f40f142d010400c4001c1400078411200c8044030425081c100c0c1c1c1c0c2d120700b04d6001c1a40100a011b000b820744641100500c101e000c220300074443c56010440d000d2111080e101181d03180e25101e140742c1c1c1400d0901 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 444461960 1250 444460710 444460727
    0x90c2102160f050a060c0f0c03051e030a06081e03032a04180b01080601020606040507020705030a030905042711031518071703250c060906020c1807 65
    0xd8608601581ca140000b45a6445040d45a80900c006185590340c60902c0000c9900500c00d2500384003030403818040707543d003104030302d0245074050174441c2e15052402614a030030040c0815240140c074000080207041001a40480c083c2d0710341100320b0b850a400004c01d0720130120542c0307002005500c2800080e80a100b41c40016603003101c0030082060304605154000d101d80c1203a01700c0b84240420741842e0b030246000b445650410442440c0165050402c4d00020b519040e0141c952402162941c0000342030500030040301d4000c040140803583d80e01c18034203004040451a0050a100b40d04246400c40e03415440d04206e603074018900c5076000c022040d9070721070f509100080c1441e5018003078078405034225170207513030010303c5014030401c51041109024409403c0003000c1d04001d5a201d030761000501d16080000543d040009a40120501820205480320aa040d4990014407030000401c020480741da00010b031208450182d0216102102180d080040b80542021100700036000c0c1d030700052242d8801e02a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 444463210 1250 444461960 444461977
    0x70f06140f010b0f13050307080a060b0d120e0d0c0b0a120b030c10140f0705010c1106060f01030b030a0303140a020717030a02130f140103020f0702220c09090c2102 72
    0x1803900c5551b0030110381829110b9120a6040d00051820003e00c00700307008080194904541d03a80340b600040d82c401031029401d1030342c0c008000d0006800b4442c0e45a80441012086d082042c1e030300b05554a9400004907800796038840001045225814401c01c0540181500d81d00010301822180c09260700780702c2e08040321080f100030042078141e0124141c030200000c1c100f50484c018550b40d00c0c100d40c1002e03401c1d1651041c04800300030390b03103110403400640030030250740002c0c0880711b405040d07415600403800742544000032581030082c568040105605a48241c4c09140d01d404041d106c1c1ea1081301c00c8040740140d4401078440091145070484000c0c4003001141e100000850050a101c601046503850321050341020b000d018905506024044130151500d039205400d182c20341c940328000e001510940140200280200000c00d0b1010540c1030744c03d8a501d0304c010400c1d080080f0448005c0080020a0310312640607181d1030b01800300241d501c15046140c0502c14552172364514101c0001290086d44003015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 444464460 1250 444463210 444463237
    0x30f0203132402040e04021f02250f12120c051c12090f030e0a0b160302030403050f241611032718130f0305070f06140f010b0f 56
    0x14030210b4a1161002d13201401c0c03420520076243c9000c0c810b00141000345141b01d100c002c0c8024120780d580380c1c00605807000a8003510f45500301d18907034030700c0b400540941d0010000b02c080010f02064034190811171121403400780311819800528924152000e02108902400e243c00c50301c00320028214004851541c01603500d0074070004041413084404403a00c00750111210084012600706141c0d00059a40b40340400301c8a000445180c03800c0d41800d0301c90700b802401e5084007030088a0138540288161801190030000f61006130321144400c6807141c00180d003d40320415030481e0b54030340014460b03e8038070500c0c4459001489070403421080c2d070780b074400742e02c01202d80c4010440d00300c4000c4182c0e4800107198101031105003040003541005484246550818a4a52924200103072400355a0842003810780103511403c403440b880c00c0c00c807811300c1403440c050094042964454100071403a4040489401c08012074001c0e520340c030320b880504a1081c41000010902408904601d2041500501440c0030020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 444465710 1250 444464460 444464513
    0x3090f020405070c0203100501180f020d1103040b01080718050a0608070602010c080f0403020d12020405061204021f080106030c0e03060c091c05030f090f030a06050601030f020313 79
    0x140000e094a404595000000b5901c0c1303c5502103060401507040d00c4c00450301e090100e981041c1d1030410345094404001c008903291405030602d03c00a41c101da403054041101840030404840c0402d0040c1d10950381110000d0144000142520780403a4403c00d03141c540351160741038901107030703c030016110140030b084c0010358550300010640760801c414002460b181d00007080740502c0603006051541c0090451604c1d6054008110000340c0c08580b007514040c01d42400c101c080d030b800a040001f4001d07a040603401520028a0b030102c103240c1b081442c03245100300c40c021400ca000e402c41c0070707040c400345114034003090030b10703005101490181c1c0240d0315201080c94a00129000040001d151400942d0b0403007000c9000220703424141040b6004000036504005800c1c8216120313a03034a81e0f06d1096880086092102007010425580c1303800c0055440c020007401c85e602007885d8104070b00140f10503594280800d20b00110380721822000d0003980d10070074510744902c40e45840c0e501c5020501d0180d9881e94112440d90 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 444466960 1250 444465710 444465713
    0x4080708120a1d15041704172116080306040f050411030105090f030d050709050301020a0906030b0f0306040605060d120c03020c06030103110424090209270703090f 72
    0x1c1c2100c0e4480c2d4035462001c40c2001400002d000c07003850b4210540400d800122010a80d190101015900070380e011155a122a4821413500e40714001c5800c10740c441c0c0803c1054a103015400945110900a001c078239810255122203000f00600c2980e2400040c51001c14544020441c503038080c50380704002402c0882c10f0301c0030611040c112a01120111140c01c0c42c03014005003400c00b4803d159000008400602d1040b80400c0d240703550380103494031201c2e55621900001c41c0284215a5980107010140c002e6444001030740014011703210074000c480000340751030f0714010345151049100001c144003901500f41511903407214005000000d040b00c2d0041032500c0180c000440a0711001d038003405903541c04e45401d00b5403400074200504004c2140c8500d005000500100d607500e1911090504101c500150822184002020342000c0e20b450070924560304030009241c070642c2d0000c10440030200c840000550001c42c406c00e00ca049404010380900540d000603901e117000b80d00c1281c000e405102c02d4444546036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 444468210 1250 444466960 444466987
    0x30e0304030602130503010605151312060507030c0f140d0b060c06040507050301050403081528090e030f16032703110a06211b090807060806030604080708 68
    0x1030380c412039040f50f001440d01200154603400b10064002280284031300381c03400000400d0309201d91780007401c04000165000111170842e404000810040441c04241f60507400c0800081c0790460f103180c08030742002e20442003144141c100440c1408076485034540c0b409040300503083c0d40c000c5008805403c1c2e413284030794880d0f500d180c094001c468454000b803d50f0714040c64103a0529040d81d011718000d030304060901000a800c85038203640015100c211071a410b0000000582c0072030598104652545070320180100b44500c084640c0036074041500500c0710001d40880103a507032044405904003403005201c8011440c000e00000000386000c4e240080700e04200000202900c961560540f203800e800e850204100a40022074040480040b902c00e200b642c0317401006040040146100400003440c05c090011140340d50b400302c4045507901c82107154120b021000a05900010b008000561041030400034485210311b04e513511501014002e007a050b00c840c2c2d1404003580000c0000c031130610040c0300710b1010a16 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 444469460 1250 444468210 444468217
    0x7080304030507051306060903020603070203160b0601020c0d050a060506130f14071b12020a050a0b0103021810180b060d0603110d080702100c0515010503011b1e030e03 74
    0xb038070160003498984401c228640d00240c00c0c4090b5181000c4c000c00610381c201c015402201e406950141e540d50750745100301d042d0711444540e00c8040d180d48090030107100703c001e48148511020780854000080c40010002c299800c1d000c010815400604501c0018240743c1115401020180686004d0507000d4004c030700760b0300c0b2440e081401595410703d65148100c400700141d000035080c108800c108007244411910103440150103841418441043d80f50203100708900386141343c020087c1ca05403865850041042d5400f0300c01680720b551070864003d146071a0810503405426191035208136540307040c2080c4423210000902c0112141d07540e180d03925945501c0001c1182a054080c009a8a4194070b000c007038202300313445028005c804a000709400155490206e0341880c3d0110b542c01c0e81e008100b0400c50309130074a01d8005026000d4403100120a8410002690580710110024050aa202144150024920040e450015909165501d441c250340c890699180a5524001c60095040d4280a2840d030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 444470710 1250 444469460 444469463
    0x302060304050f10062102060f0c0a02031e0d0e221416050a030216060204030305030a110711010e0a080607020a0507080d2c040504080306031510170708030403 70
    0x8010b00208280010240043c000078013011400f00300d05ca003418441c801d0501002c4604100703046d1203005000b59a505019507440102100c2901d6403401450f48c4c032920750662000480c043e02c01c0750000740802500d122200c00c5280307048014a540040424119030314a0b04603032554000702c0c8100101e00354520800c190150084000010550444080d102c4200340c03002130801880c20702001192852030791010860700c02c41e03110702c2c0150310f406d422510b05000071982c40004000d1480054000101904a00550f11a4611000800c107540160345150310602c1a0440103184009c180c02103980d07503008100d850451400900b003400c03444d4541440e14a845807d0b94040c1c0980e0108a5079003c0000800c000000f0348803c4c40503040346000440040c100d01c000540c40041c0c20402140110702443e24440d8004000000348140058181814000040ea00c1694020702900488d42c2c014121400c0b4012240a580300343c00400c1d18600d0501500111521090400324900901c4000103504404001420155 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 444471960 1250 444470710 444470713
    0x121502041a070c2c090d05040b09130f09020310021c02031f091517060105090915070504050a0902030f06060f0403050f2d070501050904020904020307030f0f1404110a030206030405 79
    0x10403440e82c00c8284c0e078002480d2603070640c485200100e9142d40031040e1000c4842ca0602543c5a40382000012000b00880d1942c64010b4a848000c24561000e9000010070b240242d080d030302014105c000304020380c418101d50388000507001072406039070203442e801158006032035040080301e041103494111840c445584000c80c0152640d0703140980f5003800f200c0500030400620906205488202c0303e5440303403014441c3e14840e014200001e200400706112101c2035540320400c3e01800c0c90024009402a081401900e004200a10303022540102c1c52080301c1c0031b120081c3c0c682c180c0365902000c001b5540e11117041c110140b40300303109c0040002c2080140c039441c540c19001400721111075a5002800a0042e0740786401e11080c2d8191140094002c2501e505890080ca0302580e1000100302260107840f40d031a809130400c1c070000030842e90551650003006480d40d503000038442000c02c640710106030780d0810079981c9404817401c0481e000030b511009011018901425030044145d0300e80024880750021102600c09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 444473210 1250 444471960 444472019
    0x1715041b0e040c17040503071a1501030908030f040c050a06050d0e01020405010c08280e0406050f010504051c050105040302150f04030f180807121502041a070c 70
    0x1903802450780749040a0a0b101081440c140311801440018148003440b9040804404641488004e01c100d4503002e4015510000c00d0300e100b40701c03501c0d408003180c900d54040184401c46200e90302c01c1c052203040302c0d000003d041c110745518946418868000e031003240d8404078050001902e4480b61401d90040481e500c0715520b440b001102c0f0381c1a5100d11200703000d5030f40304000a009980e04400140121034024841545a00c0f1146401c0a1003485202552904403100034001313100750f00c4038140142d00401c2d6424001c1c4c681d1041130054110261142c0e9000c02c600340400c0c000e605101800d60190040701c501441100c1d81d0b91180c1c7d0071180d0941e02500103030459401c8910307500100280c40d42002a081000096140c40e0703c0042c04290f403114400704116400500d030360011860b4680d4400f40c1602c0c41600c2c0050740c1c03503204400104880705d003181e14641d5514640c60100c2c4900c01e480031101080c1c80d0b2010740d00300355110715003640070100407104416040d070045001c0711840d503640f69410510b10010340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 444474460 1250 444473210 444473261
    0xa030e0106290301050315090309060d0c1701030c0b0906070b01030f0b010812040b03070e030d080601020708060f01060c020d0503070605013308060111031c1b171504 73
    0x10808402c04a0308000702040004214136140003422403070980b12010701d00c1058070f64800283c214450800c42d039505c400d02040b080303000207013035009000b07040300b9407580890301c240e48600b40000710b400d10024203030300242070041080300e544200809c00c122000301000d203000304507a0b440071420700a8206580104c0485409030403c145586131a01504030710000b441c0c018800034401c403082c070540c090701c40d00040110100c5d40b06400348001da160242c0040c265010014901c500034074001c400c440b840d005104003c0002910980031459900464001d0400d030300f1a0708000c03003034a128480030012600324039002d15010200360f040c00900390b454825400411154900300c1c410f0b500c0c0140600780700742c254001d018000300340c0c11030b66800e0300001d090500d0640703592080c006817000620300e9040c03131807400300159055200f209100421401500317044100710301204070301c2074803809040040e400041440c10500074000e00049500741d501113142051140c01c01a408045003c0d545c1005890400c40140c031500ba0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 444475710 1250 444474460 444474509
    0x6020405030d05070f030e0d0f1101030f0605010e0f12190c0605040605120c09030304060309140105060a1211100e101b06182f01050304080703050a030e0106 69
    0x100c94420b60f150160500202d5143c0c07500d14180d518004041c0048071440750019210354a20300f00e1a81c0061800c2031040040c00e10001c102c403000810342c0080d1400f1020007c848041c0f04a0007940e1060355100d0703000102d4400d01825003d030902d25a800141d540340d07200d4821003080002070705900d0b03400045118040d40b0f00018001040c3c1c01c007006100c014441030103120b512005032102c2c0b8042c650024840d86031049541801c0c410b401d00f075901404002800308815403d500100501c9200f410501c202915080c9034500300c460503140264099540141000310034140c213242c4800324008d000215980c1e000c60300103030303018030301c8504180071500c04070203034201c0d01c0c16448042c004203460400c0d001d02e482c5140d00c58100700b070801000745004e907500140038030610380722090040654840403100c0320071000741d200081da8a02149440341d50700d40c0803412001e544540c0969001e5540141824186421a60b0603125a00000072810405603556003410384043c0c2400f40e10000c00c00d17141051a1030346100f5025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 444476960 1250 444475710 444475723
    0x9030b06030a12050711120a170322030201020405211516050a09090f0603120906020307030324031407090608100b0102070f15090e160305061503040602040503 70
    0x188240c012854000c04114000b43c000c000311400d2805a5941e01681b0b04640850020000207401c03c1c03c000c02d00010100001e40e8604950064029283e060354080d202882c0b4403080b9520002c422086006120200c8a01d180865451107400050f007000d4485020500321408643c031003c61406420046d0003a902c1030046950654600e00503400301c1c40c00c0d0400850303611580c44103408000002846030b10851040c001480034042116051103d868002c148001824081c00142c414103c05c0e078074203a030580103a10348011100590080c1d410002c0540341074000f000c014008000380752890041041c80300120102101541c4109a02c000c04500f00140700d181030680c5d00402079503071802c50207101503940000d1241c0030031254031000c1143c00c41c400040b0705042c010340c080d1040c03c80700100400c00c07641c0d1710380301c4004083c69621030306d44541d10008000104015a449001403040500b2590072900c070b504290785c86100580450509030442c12620059441110306036034103030f400320b01030000389014400d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 444478210 1250 444476960 444476971
    0x601050c100b09150102071509030b0a06030512040806040f1e050d0f03150b0d140403020f062d06010201180b0f0105030a0506010b09220b09010e150f190609030b 71
    0x4044e010110700081e6458030540101c864596603040c0c400380c01485821040061940081101824106988d04c900904a2400101c459014107001021159480c0c4255404c681d00400288425181e41d04ca4040541c1d20701c005a601031781500c09000f14034039085507001a2842803000f0098075400010080101d030407516100c0805051018000042c01ca607071400b410750b810440055a0303683c84100090061444144078001803107c901084141600400d000d04038080b4902900d000b552401d0906505481b85c0000540c010401c0d2400c0a4014411105c80c0e400035040c0000074080100c400b44030104030480c0d1048400e0300000c2c0030403d003084507680e45401850150700910019010b5502c030340d00c03080c0500804c00e96940100d0070305556a594401c0d14401c0c03882402c41c801d581c1e0b01100080103440d481d08440e00810b40c03000002903404800c2910342c03180c031007041740743d41c1c607502901000880341c0d90a5220354072100e0044600c0c2c00c0d104008000d07006019549600c0c884520310306e000b00c09007030002c09 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 444479460 1250 444478210 444478231
    0xe0a06050c1b070501020714060c070f030c0605090d080705010b0604090f1a150304030c080307050703020c030f0c0409060b06030a021b010911091e1503010e120a05030601050c100b09 80
    0x1010001a60002540829540c236544400781104950b804500c190003083c020010500c1043c0d40009c4200500d1482d2060300d0080408050540c0c5a14050700c032440b910368203a0b003180741d07003a48c1c5022902c05800741100e10321480c000f041522100c0001002a04a900407142444c2d4400c0740b584240d0b0280300394107200025a0040c02c003240000002040e40e00e180c4013041c00d41c0e1002000a0405204900c8100520303848604282c82c0c0c1071040008106800c42034086001d032083c1c4168900030724000561200c0c04a4010042190b0003141040c00f0240001e0340c0c003101d041d5291980700740c4542d111005180700d41c2401c1c10050b1224906a810307500c0d400e01d00d030384045a034034101540020030040018003030a850241c0c0d0000c00750f01c890460130b0b414121a000780c4042407007082444182800e1303440c1c241407000114001d000d26071400511548481003a070402564142c05c10462480c02e005001035948602c05050403401c0078503128030241400c1a0116103140c03665a04540f240751700d045c1c049c85401c50031084 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 444480710 1250 444479460 444479473
    0x6180703020d15120321020d09030806030a020f1003020d061427060904111c05010e0304080709110702100503040209150913081b010e0d020a03120e0a06050c1b 70
    0xd483c4c0d680c25986000140405c4540c0040341004107042e82406c080c0c91401070219600c10101e41500c008243c00f503412030002c2e0700c2d00041015481d00069080c10350b85c008100400440c10001000601806061080181038080c4140548005140f042400410303c5411300d150103001102004041c5020036000d80c10401e010320f013050111894107a1310b5201c502510f03182c2064441d41014100c0c82d0550340116030041202c3c0203241100e600c8490340300036601c00d40081c0030503961071103959102d00032030098203120307404200d04101d114459000480c48500c2d5286070b5281c80c0d0030b038001c00c0e280c0301482d240c00045a0000705010450a00745ca20b40d030310100903685142440c0a001c0080c2c1d4484000c0c082100300d4000318402030038000da5104850700c039550a46079400c141480500e4601074060301068244038025805880d6080c1d00103c0d1000e08160b2580d54401a404000f01160080085400c0781d16144901c8400030b0000306940710f200e00441880c42c00c0340e116102d244000c2c0004132404542c219940001703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 444481960 1250 444480710 444480719
    0x1f030b250816050d06240e1302161a0103030f08041a042d0501110f1213060f0605031006050109180b130501030308090303070903030806180703020d15 66
    0x240090342c0000041c01c00180d003030403000e4221000d00461001040b402e2901200060241841c1c82c0e40d002500b2120085205110701e400a40b440c0d10100340494000e03c9021081c000b65080c0e500920000d41940700300b6202c3e4401d900c9440301c421440c0840c91401c00d0b540010b1040c035402c0401206000c5246c03400c1d190b245403503655402c25044104141001c20300020100c0c08000340000c0da60040722031316045aa261008039880003d1700051601a10b465203080304001d1416409002c459a000c035221185183c460041941084814014603084410300307140700080004065004841c0c202d030301c0d074030081075490070a010581403d0340014541c05007480c0000400a503608104858111454001c030b4141c5955943c004101a00701d020780f0035848400503c0490581e17580b5807117181640d010ba9200500d580d113400405a80744416070704507000c00c40d40c0104100003446a1203480c1d024a000d403440000ca8045031892401520540d8110042600032440c100c05c0c6105101302c07105502d04200348640350307150 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 444483210 1250 444481960 444481967
    0x9081603050a1215050603090316030203090111010515120304080f06270d03050a180c090501060504120210031103070309140304031511090d030807171e1f030b25 71
    0x158805c10b80680c2c408400504100340900543c1c085401615040c13400800300d1400a4403944482500c50101d0b5031060940000c54051244501c25404103003080e00006111042100c45040700e000d0290b00c4c07004020100b90144140085d490031a00c0e83c0007801542840d000c0190101c110042c0c84018243d40300662041c91000200c4407151102ca0a0008164417100341203009080108407181c0702d031203030b00021420050000d60150464298100420060340c85401c01c41e45803045205404006900100c204051b01d0700414049006a0b1801c0006103020215a0051039800c120361200c040380e681c10401081c005140c03035031054030f110f1401851030941580d613011070825000828014503559609440305c1d40d11a0000c8a0340ea02c001400e140040c1c4440c5130003443c05d070b002c82e150350006201c1d50724007070400c1101d2180c40c06200a880103001488010b00e88240460b00140003040780d44408010000d13106421840c58050f5001c1d42280d40c0b545854a102800c00104180c2101004600c10f11b2002c0b2552 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 444484460 1250 444483210 444483251
    0x4022a06061005180a080a081308070302010504090e10051603060b0c070e0402180405031e0403080427060603060311091003021504030b1513090b06010309081603050a12 74
    0x6041d000e041c00f135800002041082c400340d00800c03164801c0d055030800744004a00544400014124031148042d21281555110341a9201c000c0c00b06034140300c00d101d81e0780d140d0001d012042450086a0b44100e508669030103445003980c00d4420324406101fa42d20325030345402048003401c030041110b46400007100d0000d95030003161107846a10110070000c03404555800c0d111003a44001071080040c1c81c00c0a04185841c1c0c1e02070348402c0302810141c0392411340e000111042d1802c031f0b600031619030304003403409403c0030b004508042c9985031611828025082881c0922a22014200680c0e001510600f0741c5000152002013205076441003540303c3c10800c00301440d0fa20b0405803070381075803002103032131800381501881c0c000c540004200306c80010820181810381498400a00317011a56907110100f80110301c4121200c0d00400340030544542c000504d154026000711041c5882000807919101248182c10742d03041d0740003412000904001485808294490400748055030f10510030030222010224207500c005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 444485710 1250 444484460 444484477
    0x180b04110313060905011103250c141006080705040f0504080f0c1014100501080915070210110304060b03030f0304030c020a0e07021e03090d060b04022a06061005 71
    0x81c2080c0d030b04100b015003000c0c030019030000c004e100100300303820b140d1150381045400c582d4950058111901000303081049124003e42a26640c0c0f02e4156901c810034000d820384e181031800d2003194400d1111150a1117650700a0130807a003c0c00125040c50100402d40c0d0340c4030324406000b4205000e11010400020032142c000da051001c83d503942e03014400702414480d95030020141149050b0721200703c486c80c101841e1103120200c214010180e125001514101c40985000c425507000c06110015a991031001d2604964540100da0410200b40700e900d087d101e05810f4441d04900220070f0200f040b40900650504280480165080c5502c03a000140180002040541001041c005030019511a4081d80c8040c084110303082c0800c0c600008065520007070710240c1182a0407402140080d00b001200750741c0c082e040140a010800380c503440380e1000e02000703045954000d81c00c01a07400c10f603020480154090034000c1027541c02d65000c4a000e814203e004040d5800380d08025240041154410300300e03031805 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 444486960 1250 444485710 444485731
    0x5091603170706150f050405010603090305120907090c03060f050409050307080304020d12110c0901080c010e06370203090a050d06060504050a0f0506030d02030f031e01180b041103 79
    0x4420604180c00503000c884000c0c600b0032603a40000c175441c603400c403861003030366000c1d03405000076640ca400440450f10683d0380070300040c03c03d0004401150880034403580007400c440031210740c15120700d0400201e890b00101440480ea540c0b00400481941d1f0710140300400d411141007142c02c0711601c0301d54030b901c01c1d0701c801000d1000010000f000c541c1d907030031812185600441701a410030302c501e5024200d000004092402c0344201e81c2d0250b81450701c0880d00d8183c42216000c3c22007000303110b0043d6a5000c100f600160710090611905850098001e40c10080d00d0781d08c8015081c100060480c42041e000203001d00d01150801c0242000745c1c2c031020703548021183e091320400c0b0b450082c0c0c28110000c10041c1c110315802410704052102a4241d03410224000301004010007260712448205907552f040b0590600144c0c100388000350f07121903c1c00186500440d12141106044441020590102026080030101d22042d10b4550007120480c031540420100036501007000c0c480c0404840181d010040502c82107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 444488210 1250 444486960 444486967
    0x5010c030809010213030c0905060d020307060c08070501090b061005130501050a031d0304050a0f030f0b18060108100608010b0a0302134206080c030709080a060509160317 75
    0x500341d013541200c0c203210000600452407504e0f403404010400081c070518002c981440007141c110b00e0072000380c08001e0350050040124910b44034081c0c1d4400b268a00540300e034001803001300041042030191041251007034100340c04030b14000c2e00b00000d4110425015042210600a4400304085038030000d00f0b445090038220b4881c840003008501074900799400500075418240c07610012180000540f0a0310b0084440208480c2c440d1a4001c04000e01e00c8003501100388110200d001c20503080805811601791400f0101c01039100021034a4036070b081e401040664841580415040316501c03600300070f0030402c4020b00c01c204008001510021441c00041d01c5007000c100c04200240059002c503082d94035000f5a490b02c1c203040a500f1140c01d803400c1e98003003400c148a001030703e0200f40001c2c0c40d0a40341192a1090303944c48100800f400f03604000c003645e0030700c42c07094004240c100e410400122414401d490200d03803498498103581c101700240a50311031040c00306a0500010754141c000004511140348120745 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 444489460 1250 444488210 444488221
    0x305030103060b0d05010e0615010f090b0a110d020c041b08040210260103020a05190603020c030717071109010506071709060f07061a0904230d051b0705010c0308 71
    0x9030740510013006041d90301e05030110702c0351030380032074480c0c480c030304c0c3d00c9540c64078100d641d00645030112030421280c00640e8115003031101c00c203131501a1804948914004000140789802203207801910107109025030b0111114515900e0107008440da0182190413000110400f40f0003d0640c01014200074412107a601e1a0a0410700c1200806001c0c0c940180d51481e2103d020074985040c0402c0c04140d009418081010916051440414000481c00103030401001c0c034000040f4029001311542c003134140030420070f0301c020400c514810005049d203003580c1966540b041c40c0c4410212440408240500010303801049140e58410580302c40c036401514124081ca190601480b40d4468401565808080031501c445044004c0e400f808006105d8181040310701000001c0c481116490346140340d0006c41072002a0004034002101c04051510000888003c28040d10840c10000c0c8c0320307800f10004030046805142008403a130380c60301203005440501085400e200000b4280c1000c18405001d002c1442c01042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 444490710 1250 444489460 444489469
    0x601050a1e03090203160e130c120c0509060406060207050f030a05070806042303030c0f0702090a020309190f060c0c080307021c03051005010807090506030a1b0c0305030103060b 78
    0x201c14034103000401d040c8100d680740180003400e0f5000281c1c028881e0b4503080200240008840c0141c070105800840d03a0307079441a01d980d0260602400311450001c0500019042013030680020481d8410708040c3c2085040a00344840c4c3d0800503e154407540c2085030811a4580114007030b4283c17902510780c2c0718a814003d01103494181990801802c0388501c640c0000e5111010980c240202e105203400c14180c092101140c0515200b080c03020481c0d00100045a00c80c11128001c14505032051010343c200340040d000190000c0c012a00b8100b820780000030000c0b0500c00b80141201000d1101035081e20801c95200d41c44410b1301090000c21030340d41da024103c2610700910f050000c1e542d00c6060b00f80d80e49001c00d0001c2d180c1034000b2400a213410101700d8a040c2034064040c00d445204114001c0c0b20b020318000045843d0320000e0407504c00c0c810345941c0442e5035112940114420041e0b904e01054000380d95032111461203034001c3c0d500400068600c04400a94004c0480741101d4100e580800e0a0b0030040019 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 444491960 1250 444490710 444490727
    0x917012007021f1808010c020105100e0106120615030c0906050c060c0702030f0303070e0f041107020904060f022d03042102010216050109050c06160311070b0c0604050705010c0b0601050a 82
    0x8410140c00411300240c1715005400016440d4080d50080c040d98417880314074030101d0141d006501c0801c201c4401446482e10815101c59142e5114101244403a55042c81b50010300c148490000003a03150550584090f422041c400024001460082e103000140c415090b02c0700e20182150102d41000607208065640402201c483c945501c4145c80e0707281050342014081c684000c66050003a10503108005d5289001d01c180c540c5880c400304030a02e059042d80c01c0259000c1c000b481101d94541e24052250b16903801d1000e007034108042e0001400715428800c1401c14112030503808156400d080080100240031545140d45101644070140c0654102c40c1c010707400b9000d202c080190b17140c030480042040c00310542017a42003d006400340d90341d81c11200c062149500c83ca80340c54040e0380807400041c0000b4070405000891000105c2620121525103040d5034159002003d841c965a000308184800d021052005000404003401d005c00d04801d40c1e03982c203a40520090881e410700101192207050903010f040300703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 444493210 1250 444491960 444491987
    0x215121816270c021b180a0209011205180f030406020706050703020304051503061806061605330702010509070909030c1406190b090411010917012007021f 68
    0x144502414150001d5440c11700c0f0200c60303c0150b08032204038150400c0c000402a0b841c21035180e2001d60ba5195102020b548030364440c904100c540700300d0200c154442d01c1003c1c0110710850940c0b15440740c0300041031600b40e81b41d0708044946c00802007042170325000280c0000321481800c095440d0511400c080e400c5004503800315410004440c2084d5000d0fa00070003c602c2004221442c8092101c0d200c021a011705003111801d800c20381c10017800004c200c1101d40300c1120b40c42102280e074903040340c1c40e01c0b00d020410b2901e40c0100502d201001941707003a01d500c42c968004141d03c003c115500d0f0a00e040c599544642c403c40340800da4549505042c544101c4080074026003124550a0b0210640105640c3d40002c494002e0341070450481c00d03803566594059880a810003d0031184151115110b6406506039510350a0610001c0a0001600c43d50f52494036240440310000103550703a2034007115102000e0084469001c14070801c001001641c0381082d804074030400c90540d0300130511801c030694050002d01070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 444494460 1250 444493210 444493289
    0x1509160e060c0d03064713090c020d1b0b10050405040f0b0c0901050405090a060e090102041509080d200109050303100501180e040215121816 62
    0x10400d50040e0103800c0750b000c41d6031075400c455008040d030300000044481118200303a00741200049031138901d01e01e40015010703c1034400c01c0789841c3c4000e4102c2d98501740ca03423048200da51280c801a880a4050150207080549420100b0035100341c18400741901c44a014000c0846185c44041f03101650764480740e002904000d0001c20507401c2c1406c0808020718140021901000c190000a2202c0000f45c1070f00c240880685a0f01d040a04000406c90040c0c4001c0164400d11f0f510307540000c24a40c003280e0035000300b00c100001a0b55a04040311501d130400145000c0c02800040c0c0010043d40300000387e00203103140300e40f604881542032190620614185812119030079030a200c3c1c100184580440194081d10805040a064584d0390380151660103046071400ba050000341010401406060140c5901610050522501070999221000d0341d40201c0c4881404410703020810000072003510040084448881c010a001010203850100140c10390080c413640407410031400c00b1010020051000030403a0f143e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 444495710 1250 444494460 444494473
    0x9030c120306030b0f0609090c0604060e0301020c0304031b0b030601050d05070c1b090515030304060f03060e0406020304050d3f02031f060c0308040f1506030b1509160e060c 76
    0x908003174030b44429030f60a0721801c40038001c81c188803000a00e80000700f8024018034101071802e0400c3d20300d00c2e00a8070301758065400f04004031188000707000410181d8424205541c8000251754102e50141d580d07044214412020070a100346607810000b51110800c4001c408140b60f40e2b814000c654400f192107008080300003401c51211030b68500125103041da145010f08001031764404683c2400e030b00303207219201d405403c100300a01403d4031620070661410b100e81404540c1e5a82e404980081103c100da05031812903002c0181b000b0010280201b8110421910340b500c140c200031207600380507100c0007001c400d440744c81888241c4a2009145541204070214a0071900c9190042804100c02600c850f8030380d030b483c4185000305002d405500c410507203075010b942e42aa555038560f14100c0a80305260181d54401c400c01440300c021780345024400c050342c404c0d603e03ca0385040892100310705102210b00c0381d101e03c058004001c0030b507088110202d544a04ea03d0304140303601240011641500c6281c11902c218020300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 444496960 1250 444495710 444495721
    0x90f0907050309010e0114040308041a01030516050906010915090b0313020a0605071a1003080a020c01030f1109130e060a06031211031902011d0a060f09030c120306030b 74
    0xc80910310900c5404005d100c8104649502c0c1d08850150700a142254600350109002c41d204480084d481071044840701e001440350303c0f02d100b50308000d90044440d5409007080c140607010070704004000303040c241d6160040d800d0540020301940303841d022320907560400381031409903180304a00c10380c020714000c40c400f6620304054005480406044000764003c601542000030000e10a2089688054004202122050390050700020200001c1c0c03d284000c2c4400310041b010070011002041e0001c0d06400508520210600250581d030280030911082450184c4040d1541d803810110789200c0300486c0e00443c0031906840400040c020540e081c092407190303804020300098140d0141382580e000700041c502d41c0d080a1812200f650f65035641c25501c0e00180510458251021351442c145111400041800c50740350f60f2400011018a801140070740c8603003070319410300081c0e01c91408000b405210134070030b903540e80d00c024200c1c1e61284001040601d000c01e80070043e030703ca5030010740030715842642070701c960824 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 444498210 1250 444496960 444496967
    0x122706090212030715050402030703080406020d090621020f16151103060f090405100203090d090b09010e062203140f06090c10030f020d2a0801050402090f0907 70
    0x20090228081d106202c94421191400402d691899900c041c45440006174002040007900300a4001c80c1c040c400c820000c00002d207014003400203400070b40c1c024a1000110701004280584a5002c941401881000d6810400c0d01c101e00204584405034056a500140c200d80390340c0740302d012821494205802e0100007081034429500d402c800740d4800c107110181601007050120301c005c0d1960755020070281007444207410404038466000b8000c10075620300004030016001aa44100e82e10a1150003031032084545c0c64104940e00d002d4001d54050390f041100e48400607000c041d2081d01d5520482000c034400142d41c1c490701c540d4410074900c044080000b40c0c0c2c0d20786480d0507040003082807070718000d2242c0a0306000000500724400d9903440c00400751202d1800a00039140b2141c0c50031020107844940c040200d45c0f0030f000038000007400210001741c198503202119006c895600704000380f8602207000d1400650b0103200d150540e001150b0041c0c0d10600ea000103445112100702040d0807151030010010481c0d007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 444499460 1250 444498210 444498221
    0xc01180801150608010b03070801150e0306160f0806030d030e120d0b04050a0203090601030b060f030316050c10080a2a030603030809010908120403090512060402100807122706 77
    0x3d5140d9407410f980304c01483d2514001150320750005603440d80100400c00d00040b2110300030403d400d00060034041c07034011a09008084840309003500304040b0b0324424540c01141420001013a1614070100d0800c40c0003e51900d0130b030030100040546030407012414840501a200141c11064119991100c0445140d0050501e02b904140310760302d00b030006000003240d4000c40c1c0c0705540d410003610940e030840e038070401c20180141007180c0141d007100007244142c50400007040040802c0310154200d25207413410510b400504405140036040c806102299140c1052003a0703005020400042007011044c200180701078110385c0000f0300c1044070b140440746c1c181c150740b00000b52400b07586e545075195034ac9802507080e41c0f0070f14001480c030403040184e4906800c514841c150001d1107481d0440d0055565000114a400c8907808030b0a290814424002140b4005d000001000341c0c44c10a03c0301498442000780c090b0002c800030303000349a05c035480c0c40d41c03c00d1421800c000e815030082c4011202c0440307080030001000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 444500710 1250 444499460 444499469
    0x905060d14010e1501120b0409150606030c051207170403050901080907050307050d140102070b180a0320070f120311010218120f0304030b071b050c0118080115 70
    0xd00305400854081050b07660a48140011140c030181d10051320011076101401058241659640342407400650341e490040f541c2e0280901ea44107181140b5281020440d40294407200515180c0502c0d04105030300003003510809890404003003003564901009840781c40c018030000d85210a03403810002003641140203005114400e80c4c8251160340ca80700865541c1d80a03008103a03055118040400844c0360807800000e03c2480380d4000f03240b144002a1503401d907000b404041f43d0300b240c11340401c0b4a804442c0b852404a1442600410080e06281c80c0680f1026103203010301d0442100207242c02d42118100100740007460514001e083c41c941d40c6415140c00503210070107d0006105002c136134400070050080d0f5111b41c01062440020010500030008404044041d08685010342c0c604024200300c00d0003d00000c0d405500c40c07402614108400500187c118a80207035611206000d2601103071000498000c02d41d000e08015400d0003220000c2d0180407900d40c00090306608142090100c440d023014030382c00b142e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 444501960 1250 444500710 444500741
    0x30403030e010b0102060709090b06091807120501050f0603061f0e01020d1103030f1e0c04051f020c060c0c0a030c05030d051e0f04030f03081609080a0b04030905060d 73
    0x60311120049880c1c0005642d079800148c5070403001d000e501c800340e00c0150005c000400b82e600d0080c0e40c01c0881c0c400402a44000480d14030002003100450308085010001d0400d020100081c1d03042c0000640c0020840301c88a0007802d01200080781170300d4084d241c20740005104090145540c0081004090a48074910340d8010b0250080503200c01e4024615a036241e039001001d941940d4807516605090203006184a0f403e030710f20020950521101c00c102d42c00ba06100c007800c1e9585092506215080c0c2900d4040032088a040c1d528243d103e5007c94221400c0e10211810366a071101e141c4c0c11890f18180712541517000c207440780000200080b00820310304070790040c0c05407582040602005d680c240a08a80340001150301c420201c0035108a800625402c030040701842d003401d40301d81303031032541d8007100200f1800b065440c400c0c40500207201680085240179440c0c940d0209042c40501074843d02c0c0e03200001c0289070300a01040805000d80340070710150001074000b0f50ad500c5c00200b1075019181d001a0391445 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 444503210 1250 444501960 444501971
    0x290103060f1406150708030108030a02060c0c0d181503020702091806070c020d06020318151b130e2706100b03070908032b02090f10090902030403030e01 67
    0x58000b4003840c2d001c0c50b4403908485190b5546024030807420059503a4501006003005807000058445014601900031130000b9034403500031200191500e94054003640d060750080c03100031110480016031100201152406804818803428a0801c0c5482074000e0040b1000507002003084642c1940501149402203d00c007409840d00005206982208620002030b600524001298a4040d04004818600c041c0090782200c44503100c12040707800660700c0120000b025840d03c00c900078200202d0f82c003d5030012100045003840303a1486600e203c0c2a44039115540041541146a054420101c0042585502c0b8401c245881c40350091000e0b05004a20682411243c002a52450000d03900d803085400110401c20503082c044403070071a1304020510000c11801d23040125004106201070b00c1c01c0b006000503000710030080140b46590408004503214039910500c00c24007513685100024604000c1500c45601d0019840000c80f400074464008074501800002840105603141c3e014286034203510008100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 444504460 1250 444503210 444503231
    0x910120f0c0c0c0e13020d170a0c150e030315010e0603091509010903020714030f011b030f020f180604031e12030207050c06030a0612050f010b120a0f29010306 70
    0x544c2031094900141111510148900609201d005080707000d000f101a920342d080e2000600889070b000c2c0300c0ca03800140100c02c0b008100114448452014000804244599550b182c01140d42c0d0100070b012022035541d0140141c0580d000c1c20000480c504090a0b082e624030301080c04a40d00c109104a800300e013628000001c01280e03040c428400c03200d40c9035001d481240e00c0c194400500400c0c14410700d81c94090703aa5848001d000901c00c140200b994000108a8212000c0f8040c04440041c96210141d40c01080151140c00c0e420081380c2070350082401c4101e0061070305c400b081940c02560801048004100c404101000d002d005442240b0300c10451500c0c09144203004405a0041c184024100e510070000d5000c5850101e0103140d11000702a070015015655041c05a00001011700558498101d05c120030312a034403e000f00d0700c0710003050704c1c826400300070200b42c00d40d1003900c0c08024011007510b08603602001417011460802d000c41c4285c6c0c6c0b035064542c83c64091950001e1000301d410702c0c50100c1400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 444505710 1250 444504460 444504479
    0x90a02090a050a1208030402010306050409050105060f0f01141e0c030405030118030c23030a120b010207031203020307170c090102010509070b071e0b0c040602010605060910120f0c0c0c 81
    0x40a940044c104403200400c50b0b0740e000e16640019201300d044c542c0b1100082007644407072040f00301086c06840046614213020701840f40003565104c0b20350158003860740c80d28160f40c104c0b4802018584100c10640c1d640002c440c002110014090402c0c0300190000e050621501c0010240080d12000c40003009040c2c510404150b80b00c2c1d0ba814000d01045034502e203d4082042548820b91402d80d07008018042d00201d60a9811984450050310101d401c171442e00715030090750311501210041c00c1c0018101d083c215194502e45801903142d107401c040d000000205605d106080c0d00800c1d0289041058045c10600c11400380c0e6000011110b0040d07207880002801d038130001034442e00b25110911501d14003402c0b600c4800380d08648140704643e07000b00355186000210301c01140c900c10002c0580a94032181020340007420740300c455108070b208040500445110741d9462a6890514002e802c0c02c8841004e07010300440546030b03034807856845500d07001a000505800000302d00002c1d214200704001c051301e840101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 444506960 1250 444505710 444505729
    0x50118050a0317190b030703021201020406080a050103032102040f0605070312060e070c02030102160c08070b041409070c05100e0c0102070b16080f0d0903110c0904030806010905090a02090a05 84
    0x220081920400540040c500c0c0d92124400c0c01018007901c2c441f5840e500400d482c04107100281d40707280e50009040000ca80c3c44001c507a00641e1180c0c06021651441d280140200c1450900d1000030b0702d50040b0440e00c101540c100c90082c240c4011404042e596540060170980092400741c01140004201c4040380165105000a513814a25412802d48408030300f2101d0164aa404036015035081181101010454200302c000c02d11038014810441c0c140b298031800c0c0707a1158407201034000c3c14801444194a00032504072014000c0c0ca4084555490450403180910501009400e0f80691408184001d0306038001022080002003211007610003980126660f14941c800c00b4000b1a0500c000c41103c81071400c421101130003880700c141048003084d200050b0390712140e40402c03002e42d10a0440708250308240d8001b01070040d4405044808805400302d809440010030040401480c1d00011300981c1c00303444c0441c00340001134a18501d03403500f1801ca900035407180da000d030f10a00411400048514021001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 444508210 1250 444506960 444506971
    0x140108070516150e060f061c0b011206060e04060906060609030305090d0507051e01020d0504061b1e030c060b030303090703200612060a06030501050f0d050118050a0317 74
    0xd0800b040019201e4020780c03e00508000802e1340c4610728190808020000075003e070004c0301d90344050342001c104010301289440803882d2104801400300000c00c1c048400681103c420900b000140401840c10400400d510b8018981784c00c51030082c4000d201c00c6500036101e40d0b05c1154100a1703a85c503403405540700c1c03201e40f0009000540400510106041030240e2045a07072140c02201c00300d5440e100040e400418890700d1407440c10411488410b65a81044842c0c2d4400850614600c1c0a09000d80240b809170700201d040c62005d0b44581c110304000c00b0b600013070f2003007895905403110401607140080803000c625a0a45079142080c003508030920740401103c4c000e1007010010080302d49155191156a02c0b81d815030306013403401c20701c3c6110940314540242410941c09068259510f400c10402c40403424981012040500e0540144019203503100e81c2c0e28504401c4820740e01201080ca40701b400361202800c1804074800708943c550410a0024490088a219449050608542100d1070602c2d801c12140c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 444509460 1250 444508210 444508237
    0x10b040b0f030309060f1e0703030c050a0c080702010e03071806170c1002011404030c1506211b030803060109080a030c06090203032208100219140d05011401080705 72
    0x90a0007031701e001c4000b03013001300300d144000d41064039149203950100403120400003050f40008180080560520030901201d0081c2059401c05005500c000c241d0f040c41c08005005000004100095a000784c6440b070540300001d04079207440e5100d200ca029800c1c0b500404040301814404040350b40c890448052030004054001001e2240e81c0c041000f000c2807040f42d8144c2035558503c40e035041e41c010040c00314850b6020780c035030240c4001c01d0301d000c000c444203080c440050303185004c0341446010301008540185a0000702c0d110304d000d0042c2800791852000c00c3c90020325180c102000020841860099441034509072507005d540d50f40c03400c0c1d641d200c9a500c10001e00007103018191000251584c0d20440d08680050212401c20b42202218540321810b15441189000020f40800c0b00480400400300401c582d07042c1035042455245d000c0004441310000c980a2107000014008052842c809079403078410b0315142070045582d5880b0342c220350610400640d001480140c0000c908500523422121109040c12 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 444510710 1250 444509460 444509467
    0x3010b0a05180c0403140d110d210e010e0703140601030309150e06270609010c12020102310605040e040213020903031b0c0910060807091502010b040b0f0303 69
    0x4245009000000e010343d0198005010200118030300c15014901640020b004080030b00e244140500b821000b258032a00700c3d4400c0b0307008624164030140b0441010241c00103c45803484c0c084200f805060704445d240100d41c60038400c20860303400021400c04880c09203821843ca400d183c0652030700c8610901028001c039203030403000c1000e0a9803c2c87d0403903c2101d454078860a0b0410070025042d948603501952100308044114a5112a07900032072900c0c100850303505203031040c1c02c00040c1c08002d1058010700b40d0f9445d4039008140174000c1d0102da19100c180490700c01045001d894405243e68242400c0c50070121846c00426518050801c03103040d514554015070407543e43d5401c0100a100f81d1040d00d0406809110011603500c080000c1c09801108007503030400c0c2000101031929000d00d5154551040780002c0501c07400781c01b4010340070b054454134906600f031a901e40b402952204030783e40c0280e01c00c100b0649050341d900c2e819030042d030041c0c034121810300101c40d041c0d080014000c0c54518442e4581c03c00c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 444511960 1250 444510710 444510739
    0x309010504060c022202030f10060f03051312090e01051c0204020304020307030204110429070f0f020907200106030506070c0c0e070c1202030310030b0403030e01061403010b0a05 78
    0x380107043c0d110f4030003842d02540c49841c000080045c041001c40d451a0754012081c40760314403040c1190350740402a9820100502d01c0e0400040c0301c1415103900d40149075561010a001400f04130791400303613a400032544602d03c08142002031844402c1c1c0305441c1036148940011400b0b01c1c00382c1070402901200c450030a00d208107502000001e41c40030f0422079051080311400801030f100e5004880811001da4455510740b4079010498551809003d0f09000900180c200c10780c444840b01c003610b402030341250303010610000070b01c1c202c00d15529249029620110400403c012158000416050f040c2c4410b4126402c8c00722084d0b8500360f6a05000041003a0407803c001955079200c1caa010000ca8001d450110046035521088003410b007042c1c2d002c00000f41c0c48409102400101104e80000b01d2252000714603503d0000340181c4400b49500004050060201c0030500f4503100340c0080f044002940300800440f80d42d400900d00307104a0340e085a01a50a000002c1c0c581e18003140554211000076000e000d80c0d10302e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 444513210 1250 444511960 444511967
    0x30e150702030c07061809140109110c01051017060601020d2f0f011107050a02040b01120f09030e030a0b130f0f060b090109110a08092e0e030901050406 67
    0x148540c04512081c4840c0c050707500c040003088000c0c03000e5115041c9103031101906491048894100c1340c0c5560411101c100c4c0790940c00ca4141c111144071000180c9800b9010300903405110383c0704c49509a41c00c200a0003035030780d03040202e0300441e690704040c01100e40307681c6031294032810308441e5680035811881c1c5a40d801401910b45a01c190000c0015411a082c074819540021500c3d1103410700360307408a041302e00e44002c248240d041790506100b2440c1400016030b50207540306003a1500a00490320388403400050317401144800c00c4030a40c0745050006207014519034005042c50344040e40000c400a07840d0741c0c18100890811117940d04090004040d58442c0311401404243c0201202c00e100c8008101011444040480a02d02d20521000ca001c0c141c190030440341c80c070180c1108140c0b600c0c2034140c02d020001c0e9012038500540509084d51155140250783c3d04120544203c0358103107030400000c420500061700b116609103036008080280310348a0140c0c07543e030300405030843d0120341c3c100401d0104c40d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 444514460 1250 444513210 444513253
    0x1106061306050a030c0914040c09020c070b04030f0302060f090a030e0a0f080d2705040b150301090644070929010c1e020607080403050319030e 63
    0x80c82900818100d03a69000b00e054500c05074003e0f58910315801c400e01c8101201c2c041c2089020b00ca075440106400e281d120340b41003200911500300d00941c0001c0700c10381c03124180161801041204d0255490341e07940d0920f01074204172064110018020140054507070400d691101d4015181c1038000c003026030070303590103584c0c481c80401c800741d1010b00c0c0c0500180145142111030064841c010252040301080d0340c0140503d9503074159241c046402001c0030004d14076240c2c45208651003100e01054540b605000f003240420032031008009044000004560740b80d6540024080b40c1c209400c01564480101d11013018400c10540c0b845a004101d001904007450811400b00f040d9480094998559690030280c2c11121001c10a00c1c803070054910241d131900d48442e43e170740c15003420f007064000c0c501e055441190404c107a00a540d00712510070a403100b03644034503082e40d902c10340c8844503540d6151a030074269a20707007109000301c294501004106040d035100b0700618a050b40c0c41b100510140c7c50b0710300008410039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 444515710 1250 444514460 444514489
    0xc0906090d02150919051003240b0405031207080301030b07050d0203040b04140d0e0111070305060406020301050a050604030f110d05060f0609070e010804140a150e0607110606 77
    0x1290081c41c00242c2e4a00c1401c21420144100e076035504c041000521569900d20307041ca41001e0001e22080000f92958903180400306440d19000400d240e52a2020450b841c41d184c0205102c1d82d9000041011b0640400138416560308800b1516014182c148004041c400c0c24002840304400b80010000100704003450317030300400e407420210b0038050b8849107030040f40c00444e030907101d5080b9441030005001c0c0b000a0300000c0b0300010013800200340c0e80782000d41048510316442d410030014800e11107024000b40001005107600000f640c1e050705050411001030340007801954407500030f803140040c29140ce882114207d81c3d002c82c100c2683c08c6141c030f42c8032001151030030781500701c040c0c022401c00080e070520085210380c075152005074440c1814014041402c0000700101c0900c400700c82c00e2440b982e0070000303880d40240c0c0000442080b0f000c511402d401d010290742c0083c60711502c455417031701c1e00000c2d030042c1c3d003170a01401c00c0318010740d0790403011101000f4007203014185801440108246007070010810f091503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 444516960 1250 444515710 444515719
    0xe0c18100e0603040f020109050f030a0f1e0302070e060d0209150f040204030b0a0b03030c150a15080304080d05040303140903120f0a02010e010606050a050304032c090702060c090609 80
    0xa0301141c0441c29582c41100e003295100e03c1c06404100b10368003e50b100300500300654a612804082c6400f103030b0740300c41d180d0000d0030442c45501450200204e10610058060107070aa460346841d4030300d4007942d1001c0c14011560100c1c4000001515820301003d000c1040b50005c0c032000440c3c4403445003a503a041d4001e04241c010041e1210001140c80c2d0380000d000031841040c2608192402d00004004c8901d001c5070184207400400004c40007170030014040e03110700d140d076407802d40c00e0720b60301c1c07000d40140080400340e41c0b01480200c001070141c0c0c1c040041c104885824041d507141c5001c080c001c071010703ca14040100861341da2061703642c0c0c13107140c0300180c030749140003074101c81d0300003240041c95405070451181c1030129140001c00b03a401650a00919256840c2c200003404014205103000c0d22a01402c020801008000301c005011b1501c034003c0d00e00d4a210904000c0c074080c0c18000e0b078205203c41459010300034481d00020a022510000f0160b1064211001a81c148100801000840d0744a40b1129510 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 444518210 1250 444516960 444516977
    0x201090b1c06031217190b060d050403090815040b07030f020d09080417030405030309010302090d170a080106050307080402040f0f060f030506010f0b18041b08010e0c1810 75
    0x500c0c0c0b0607000a18040d001e80c0c030362540050001010130802e0400d26007603540d64824000111480414407103010745c0000e0100d0840c48400200320715009405c00d40528904010a0009141e0401101016102c82d541981c182c5a1b1840000010b00001d440c024140748201c0c000071600c5100c0c2e0b2022001380c0d980240035240501410044003070320074041060300c80100000d420480c0560b170300103e80c030352200840070b1403c00c1d18000000707480c2d0241c034003414149600060488065030710f620711403d01d01da10036500c0880b0070f1503c15240c0c0c1d50b00700803074040100340e0903030001c00c40e07074000c101381d034401d050540c1c50b010159519420702018000c0c0803601480306032941010440242d10340103210181004401d40d01c02945036003000c910b0b01c5010b83c00106e545200b00024420515040200c80d0305220b15848030480360382c502c0201c7d0040c02c90003000304104030f54050140509500802190403901403e00800700e17030302c1e140301c48013a91269410303203041c0c441329034100c84860401c00600045107040741000c80c503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 444519460 1250 444518210 444518257
    0xf0f1b0207050d0c1e080d120513030207230904200405010e13080418150b091503330a06080606090d230a060507080403090e040f150209090c070201090b 67
    0x90080387d0003a00e001724032480c14440551085206880d0300040601080c0e5980301a514041e4407001540617800c000c0e040e441c1b1001031200c2c403940c66592541c025068070828541802c1c80401c492086048a002c82c81c6200340341103070310b030600429058510710781c83c110890f1264002482008a400ca041359a00410300000a803403035100040c1000109045010801684000e03460000da00250081c0c11102c0c03041c046140d0f03584030700180100c8011141e6060780c5d030342c1351121042031424a50400c00264041c189000d0301002040c068900400c0d402d80f10300030250f0300c60b0815944e54a0840350240c1042c1c00340029903142c40c103e110940c500b0300402154101e43c42c00050302010310088610000654842201e203410014140319017a840585890844107a041c103a5004000741030900c07489100c00007030f9010806001c440e480e0141159800304020700c0b4412030281510180d00102d00c078074490001a400075201c1b40f124011111100c0d416507400e02800d04001c2d10550981003030304104030078850810a00e8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 444520710 1250 444519460 444519463
    0xa0504030c06051e1f0b0c070504020f040e1b0f092805030706031b122418060503031b071508040c1212030f0f1b0207050d0c1e08 57
    0xb400b13440180094810401c12000503d030f140d00140620380101e0303d20302a09075a0200f140c0e08410364005600045d601d044215850b0b1400001c0d4100720b40c80744c030001e00701c007991070032000510440342c41c6a601d848940d100010a400e080030003220026003902040808001c00b83d481c0100009000102a02a07080021240800d0900b4000da0504200718580090140e407400300300c05001091f01d4501070100380140d1b5282c2c0004041c02c0c144900b444003110500c10111070980104c0d02c00c0750305160b94a074039498803e03813100044441c42110070340340d82521100c820500c24002c240640f04040d005500d44151294852020b100c01003140c2c040e80121800440c16200c000303040080308030075079603203400c80c02d0904000c400b105495100382c408540030b1030b03030900041031084150350300c031a2402c0001e420300c081c800440151010b40d01c003140e02803800c0c1495600102c4928001c600a03038660840700c1680d21101800702201c3d100402408441c20302c14204209264607602040940300300d03580111441d902c0030300301e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 444521960 1250 444520710 444520721
    0x503071b05010e12070302150a060308030f160302040f030f060b1002010203100603050103050d201f1503230309060c011d03041a13030c0e01031b030b0a0504030c06 72
    0x22241651680c60f03c0f0444001008000200c00704c49103801d00d401c1c19594040e40d03607440044c0701b44240000400003080f81000341d000000954000c10f900743e0b00d117080c00e40802d003e0400c8603c1843d0a00b503801c5a00f4043c424800d4606032100070707a00012103425925950000c090a80d4112000303511120102c049448142c80350303006a81580000d62a414031032244262001a40c000c0020549854010004100700140c3e50303010b4005d03403c1c42c00d18400030590300c1108002c050380ea01007521a650b0a000404902c251505440e000d0044c1000400d10b10000e64245245904c0050034510b80d641e022500c0f50b0140407000c8001e0341d81000c5134034044c01000032440395080b840d86001580d6441d20032041d4910200f510ba0452440580607600d401d04010350058001c0721596403051040b00885c0e401d20340b0100058010255401c1450b103440943e070b074512152840d41c00d01088900000c16a44440607520024011040d80d60083c2c2a2a4956441e11800d00400f4010701c00e904118075990400d001c90b156100341c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 444523210 1250 444521960 444521963
    0xd02060c06010306050604050c03161806020304050a1a03040219150809010507030c1d0a0f030506100b0a0c1e060f0b0f010809030405010305060102030714011e020702100503071b 78
    0x505059807644c1040001c45500400043c0a10f080c9810461004140d0048a5029006095080901552080c1121840c001550309100c0300010f800100c0d01c25000005482169012501c040315103444101201d40c081000c12444000642070011030018581070301e2000204240410551100782d44070340090447e00001c9407107012480308801c0c468500c0d0203004041c1c0c0b103030660509115141e100500102480f251000c0c814a109694080d0400c039070b91101a80001d0960603d8101d14a88070300300562110001e50f40380b0001540404002030301c00042043e00c100c4111500c841413982c059440740d060105241400840c03540750580f0010019215110381201181c1140e00050010b00200500420b035802c1400581170246405c00c000555000000315405d44100307280200341601d9940050b450760146850044c048100307400c0c4404500815072106105c82617584003e03408041c6418500201c3c468884003a404c00a4205c62080b401d00030001542c02441a283c80080410041103090480c0b80c00d440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 444524460 1250 444523210 444523213
    0x90105010f110d0903120f120b0609040212090f0601140d0c05060c010f0c021f0f1d01050402040506090c0a03240e0609100b1209010b061b0d11100b0d02060c 69
    0x414070600005031208a443c44031401e040c1654180c1f948040c1c0140c0403052604441d0b900c410348580d02e502c0d00d0302030740c120716800f0b0015500c030f1000103085a80b8080840e41a0014800d40482e000310013800035070039040701d05110b03110100d046082c00344000d81414100c280d50809007034000095a89460005001e40c0807240000200b1011140308ac405444200c8580000c56200242d110881c80540780180c61004032640c00013480c0302c510401e400500a2030b4034103404049180c56852014074190411441584211004c01c03099a4120801111030700a407103101301180103000300f000c9140250b00042e403858042e0113032074a0070220007103074030660320941001e418094800e00b88103075410040d20075a000600c0110072030049051402000040c0a00707502000c109000402091a01c40d0070740c4200341046000c0d24040d6685d88400c1c840302404162003405080d88903440c46070346424414107151070342c1308031280038000c0b04036900100ca020f803d0840300c907a1f00400340d440b070f9001655800010014951000d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 444525710 1250 444524460 444524477
    0x181f0c020109030b2d090d030e0a051609050c03011214010e0706050c07210f0f0c03080c0c040903081605130e010501080106030605030d0507230c150702090105010f110d 74
    0x30201004ca004c1885d120000c91100d83c10f02090590120f0b2007420600240350000d413844c2c41d102d469140440c13a2401800c18002c500c100441d074a5100b00a40903150a03c40502c00350322210b219078018402480b0f400041d204400740100098804040038600404c0e4500105415400c0001c603410070303089501000c00b2440001d00c21443d05400d01400c00240700780d004152a40000520451800c055200003d00c0c403425008080200800b042d500c40711990880c13041d65009450307107440c1c42030b40e10007010b0340410f108030b0900c00034501d0980a000115a4543d81340c2c100ea468080c1020514864003030703200e0030302000384143c04007030045403221070040c0482905040c480d450407002500e0048107800410405082c0b007014441510b0001e07851000005a203042541c44a1a0501c0b40003034141030f46400c5590701440d0744954501c070005102c10054001c035001c504000100c14864a07074072540c50001e42040d5214010000da600545030607a0204c1242021307010070150400f81400e1504440110004c40d0054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 444526960 1250 444525710 444525751
    0x2120c030714030f06010e040602031806270c010c0b07051b0c12030403200109080a0f0213090213051f090603120302123702181f0c020109030b 63
    0x30894504e007000054040c050f075505082d400c2c101070800800240c410b0381c0000c0481c2140202e803c1c90320b080000c0c1c0058422909240200c4521070303081a48a44840c850350402c00d000040c0410804140d68050b12030070441c48207079881c8031030f03424010802c6044c080f090061031003e4034200d00002d1011a60b0025041160307900c401c0044908180154140b251b10038403050001860426125600390290781c4188103503921400120741d08480380d000740030107018141c41c1c0000c0040c0c400784c40c802c26100715139019914600b1350081c0211490000e01940c40b6000b00c155104040d2968130094000384d003120321002011a000d018408030344c084d44040e00041d500d802c01c00038406d140a1180c0c043c00d0b01c0c41c0c01e5207001c481d5030318401c3c00c0380c0c040e0a011640c000303c0c8911840130207212202d5299005001b00b130103100f070500000002900006007500c0c0800c020100b00e001d0b413401001c20301000958400c1c0e1204982d46220071030f28000e0100c03049050150540c00030000c2021003401078800c045015541e800018007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 444528210 1250 444526960 444526963
    0x1208091005040e0a09050c12060f09010b011704020301020915031503060c09010f270e0a0c090e0c120a091202010b03061305010f020d060303141602120c03071403 71
    0x80114000c1040014801403128600300080036400c4120302c440440d425030a400d0142c10918502d00da1a4000301d424000401c0100224004c3d106880704264150f2a0f0764400c08079003a1160300c0c0c2c500d030005650400f81d207a001032100c0384c4c0350418000b400050801c003045000c43c0d0508501313004221000404410059401070403044d900303d05c00c0540260980e81401c11246250b8040c04d0a514140300344071420082d02442380580c48444030400c50040170340b840d02c1d0311188800d50345003e408502e82c17103980000c09000b4103020340e000c6000d039640c03207109a500c5d241c0000e00301400074140e01525181004009005140410102d0041241810028103c00280741400196039040244019a410722070b0021141d1390101c2d41c50f502ca0f5500c0e2115195415500d0100c0c01001411a4000745900c08590415404216032110090780d110f134a0700c56100d02c00750903030a00e600030ba0fa0321000c0b045a03003a035070005041608865180000e542e0440303800d541e1140000341464115041004180c1d109449821107150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 444529460 1250 444528210 444528229
    0x309042310030506010f060801170a061103101205030f0309210a030c030b030604141009060b0a080a15020a0c05060702101506120c090806150301060e06010c031404120809 75
    0x304965261b4100c0c9000f001400c1624148145510084008100c031010241400090051a480b80d005c00940704401000300b11078105850301200e055801c5004501841740c058800d000b503400c00700440c10480c9074018a1116440241110308602036021030380c0d95800000441030070316030400c9540b03407a8802d65400404903072a4102c0d0404250400c20f598009440214079070b60855000400800b5620070000803e00e491142000c0d40021842c0c15000c8090020a0380094840c1d4021522442001e61300c0119507031b110300314000070f0150050341d0491261a8035031740c0103066403881070a25103108d404075140c540c10311034116130b96130161f0062140c100c0e14440c10b12a41c0e42d41e150900000400d00d0421400501001c4079149010409a90b469614820780c02010b12400510344600ec0740d502c3d151a41489902d9021a40307414040d40c01c00c1808641c0440028201d881f83e04117070745500001c44652400c41d800c06c50780788100070b044004c020105400c48010504030840f40501022556506040305112961a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 444530710 1250 444529460 444529469
    0x301080c010807170a0b0a08070e0c250302120d0b12070605120606190c0302060f040f080310090c0f020c0a080c12120d0504030e0a0503030904231003050601 69
    0x140401046903554100584d828030080c41000f411a5603540303075000c402440400500e6521400318040041c003100009494400c0e10910220b0070400c0c0c4071901040b4540c0076503080110300d46a07030740001004d11000da414241722800f9104841c2e400300c51000314a90307507221052403400d00741c6460b000d850342c3c105581e81d00c0c210110f040080203100e1401d0b200400e42e01607807003c2c6d01035203d0f06011407440c1d900d650541d8010162051032083d14215038070054220681e01c0310890240c000c000005040395200c41c0074070310850300094140d2071490255202860380e84010b00d18551a181004041080c00c46803103000044009600d800400c40e07410f81e4040e103496888020345200d0ce58a007170a0200c48008100c10101540c261203161a0b0004090801e050035084d9250020407800400d02100000250304100d00030381c025180c2c02036804d45c12040c07020025050054542691040141202c0c504240c2d0088903081c0d4a04c4031210380460b650707603c151910302681d29a200070031542041c8288102442103d0052 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 444531960 1250 444530710 444530717
    0xb04080304051c050307050901020f1203040c060309020a060c061e15300c080d0e09010506072103180f03140a090b1b0a0c03060513050c0d030e150301080c01 69
    0x1010b07001002403000a1106c1304101001c0343e07528036030b402000340c3e803108070b926000d0b100411034140c148401e0350011602512200b44140001030042d000b4494404001d40141132114040d0800105940103100004200e88550350b80911000d499524030508103140b10400010035a811810354981d5150915040b900c1000b02d441c0090034103c04041c6c2c1c081e091104480141e50b006181d06184c0e00c080b615901085040c02000c600c0120a6841516101100812501c01c90307681d0703c1d402844124001c040c00107185c030703200219000383e40c802141481e080814610f008601e0302002d000b02d0340031080d0314034201c484891400d1004200358100f1401949a44000581e605095110304018580d020034800e42c07100d00000145200e40c0710070356080200da0801002150345410451620140d1031460740f0099914514010109910210380c03050b520b130380b81c0c01c40003c140c0b41186008110300202c11920450502c881d1a4000c43d454440c12603904281007070003203e503180c0d85031075005820002142c8800307040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 444533210 1250 444531960 444532003
    0x10b04020c0c190308040314060106030b011d040e0d0302090906061e07051608060a0f0612020f030c041805010b090c032a0c0718021e030c070b0408030405 68
    0x500d0301c00640700500c40b10403611901102100070380030380f4010b50360b00003615031840000c0102c00d0080341147c10008401000448905030b03a201000c40403034184841581c0044c600031414040b400c0540100c0d6101e5a005000141000d642440d052070200340c42801004a9008911501c0c2d0385060011658000c60940c3e00620300054503880c2038092050304589190040b02003811006d2200400203040c1945c2195040c00c0b0003511100101d50341e074001c4a03003803200c1d400c00c600750032811441d00441d01250181c0d03520030204100d0340c0c00c00c08020f80c8044181d4161060340d445011f555078074000c40c01c005000c04615003400c0d00c5030405500f503698440c0c40900441c0c40381d0900c6860102c22044035804058a083c640d0b0581441c25107440c588a41c0141d05500407011814000b0b014001c60b44404903003403c040c0900900700c103000903082e40162510082841d00d03240b1111038250364800190b43c000c10401550745080f401b41e07204950300034260350076a0364900202c100000c100b810032046c000030301200314000c003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 444534460 1250 444533210 444533227
    0x7050411070201050a0311030f15030706020d050d021909061701051f02010f0603080a030614060403140f01141005243a051308090402030c070609050d02010b0402 71
    0x240c1e00c29900024100080003410b060000c2c07180d88260a901c642d07460a43e40c0307042014000b400f021055400c6031040100300f0307080740b407850005108070403600f15401401d00340c1191801500c9030303000311a0351810b880d0200b0459113514040c901955a0241e603407900c905243c04d00e0001043c00f4144002410007074408001485159103a4110701100784a405071140c03030300680041203000d401c030b0900c1146030f0350800c2004020840700d0006800003042c3c540e02000195500c6480003a0300d05407604d2035801810400c418004034010302c50f20f05502031990700f01d03018420702d666035a08480d2114400300f041103032681880383c0c051614400c903000341002c0b10b40115094460040c1042c15198510420381703094005036000d602d49516015141c460350310101c10740001050310070319000000c50700581588518000004802d01042915903d055400c445041e040050380c00611000350f10240821082c503034288030040018806008501da072600c0340e00a00051007030f960010703080d640e4507150507201c0c074014080f140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 444535710 1250 444534460 444534491
    0x3309010c0311040308041a0d09050a1b03170c01150b07060605090c0a0e0f040606020322031a041a0901090506010602071a030a0b0301180c080c010807080a060b04090e070504 76
    0xd0070787e00308a02d0034041810b0302030510840d00c5580c104885480c103101c028000e1140c0440c05c0c4000c0c500820303120441980b010781103805c85c1c4d000d020050140c2c0d0f00d80f41e01d2009000700005410310302403c0c0000186903103490b0214485009640c0040218400002c2c0e20040003480d00600c0020002035584025078100b1545003e118022200c09004000543d0b000c01250707034070411251006180540108245603c5200007501d03640b242c0700341005000c081140085203000c40c024042100d4210550a07d0340380400d00394409a14043d10a0ba240d922880c16a0254050030729010b020760b000000000344106246001070070000f0580c04102035411440041043c3c0b15892445c081031203100c880c243c0c1d6655100d00d140002c104c0342744082c1e0150300e8540d60724080c000c400460170319070f4015941000d415549907681c650b100c0d80360303010350b001842190104400c0c034001c0b010340c1e400c4483c031207001c1381c0c4546450420318a6005544030200030b5031151035502160805000e21009040281c409001e105400134505 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 444536960 1250 444535710 444535717
    0x2406030b1504060614031005040204060c03031104050d0b1905270105060a090207150501030812150d020d11030604050d0f0309080714100911040b01113309010c0311040308 75
    0x1040c0072500100042c401001c1f00c80c12030240c84020411521285c441c0401805010716500c00c40120740350985865500c2c080000740d904480000340f0318620030400340d40e0317059030400190540c50140c1581d4003c0044400754001ea134412646065141500220344d15801078075181884030885030f924100510085489500001082d19000200540e9a02540c079085c10a80c0142405220051a0030000300c00c000b1000024409540702c17001000f200d8862404900c5051903222217140c0c03114440c3e8038a0014100354596070301884c001d00c3c0c00007031030140e20082070402d501102c080398103401203003c800c0c880e50082d001140c1d070300103444e04100d0004140d54030321080c4192000604450303403898008044220411a4409640601e101804210140d142150022034500d64141c030031401c02100011a520032000b402100280c80000c0501038080100d5880c170100c06101e800344c2d0414820f2640340c40054000c8240200300341400010410318035075000f01298001c2c0345808254408120400c0854221b1055 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 444538210 1250 444536960 444536987
    0xc030503100819030212030907060e0619120c230f0405030307060e0c060a0e040c11010c0c020910050d0b0c19020d090609122406030b15040606 63
    0x125901d4036401c040a504140d15400001a4800e0080d40803183c00c60022030f0152902c80d800300c884170881c1a406da5100e0004503001407141c0e0040a040240d00d10600c4e4900c90040050440e40c500302c490900000303c1915000d00f2404a003408801c200000e0700307803088070a00c0d2028a016203189400c04611208905020002c00140d0404143d1403554031000701228014403005040783e5840f2928a0808050511001072104900801d0300c041700c6400d02008a820300012641c55416540391a41084002d0880d80e04100401802101c4810012024440d10710604246d440340c1d201400300b48104007140e04014007190701855000b90400c0142c0780c07540b0101c4050350144e00064940d5405003540701500075501c0c0302180300b044083c443c0809030040b48402e201151990b901c5802921120f0031f40e484c0c1114403415441400c84440c0c0e40c04103040c0a41c0340003140b18a0b6003102c1020001199030159030340b40e0400d551a0341e946060011294244820150000b0280e905000c0b6030b141840140010300301800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 444539460 1250 444538210 444538217
    0xc03060a050609030a02060d02092101060b0406201203070c0b0a0902090c030a11280905030c060a02030708210a0e03091c020d150e0f070b09010908060106030b0906100c03 75
    0x204403620800c2901580d201d180090070035030140c005000c2d0f022000c112f001200120354039008000c05d40689040031101910395a4030f0794099404c4031035115844145044100089000365900c00e400d0940540007140190b00d1680d411a0805c00b030700708000d0400c805080c403107082c2d180a6a21005840d02e4021603801855801441e44030355860f450340016088102000050000c00135003c820386103101c801407039000080c0003d00c0c5a120519003a608407086005265040d030001100c00070610b881c500611040d0504d106880c140180c60361410340d10740001c04407010411110000c814000c82003080194410712925043c80710180003c140790722441035a0105000e00200c0d541501d407110050f400d001081da0292001c81d02110300c4c186040e600715501c8007808461700302080700c00480760014000b43d4210160018110701740c40c1c11144001c0d175018103e50390502c45186030000e94140280a881d00038007079501c003c9202e4001c03000700038010000800007445441d10400720391240398041c1004890070b41c14207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 444540710 1250 444539460 444539467
    0x3150913060b03150a05180604020a0b342904120c12022d060115031e0902030105100e07080c0c0f21040e07260c03060a050609030a0206 60
    0x140400c0c113204040e460765442000d00c2c2d040c410b043c026940030701e10845c032244400d001004910305050f114001503a01951003006000117100e010b1800d001424074500b4940810024140f9604800311505408404a491403a1003100c00030302c282c070342e918494061980c11f138903100d00640c04845130b50280540090007901d10346160004490141c0060740c0059001700c1c002103540e0aa9100075a070301100c500304400c3c034114001101c40a00d10f004010145c502c0480035006580c00d001590b15643c184130300c100101b6499001d040100801c984140700d100004480102d02c00c0414018142507805c003505544460750240d0301000169200120240c002104c0c0c94112113945038042c442585010340c01010020340151403da580c040c40020301007282c40380d242e803080381210380800c00040b0b0f80201c1c0b1800315044224400149510304c601d00c22030b0340342d1965014402104541046402e0f040d001c80740c44505260001c1401104d14003c0785640c02400102c0d4140e01d4115440d010948038525040d00900440012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 444541960 1250 444540710 444540731
    0x20106080709020904270501060506190323180d0503190b15131a030c072405191d070510030207050f0705120102040f05060f0d110315091306 62
    0x1600411b15100c0b150384081071500034200040b5002c44014001c0743c55628180c000202414804166040140400400b18404942c20020303805491521800c0050f9803e040910a05040100040740104983d2000703000940034454107910340304216000d1414410b043c8200003c0369100c44041c00c42c68903071440851b03181400c40106503110450b4014aa001a0205105601004460803c41114905000409940e0388a5520742c0d15100c00d80700ba03601020104100c4e03010442e960070480c1ca06840008600346001c1810b492000c40f6800c1e01c0c00703000c1215410b0b1010003e07502d0301403030710494000e08020402c0441d8426095550130144511070240d00b01c0060b0501c824000d5040c0c588054000301990780340c960b048409070f1101c00702c0c040c09100d040b14100704e1303540c00014401c1d80e00341c82044401500860030241008200d0308240340c82c0e02c2c0407104019129000c20b50b40aa4688aa50018120345078113200b42406101c031000444280584c0081040050100d608609e142c0240c2e000040081e080600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 444543210 1250 444541960 444541969
    0xc2c01030210110114071d04020702060d02030414030304030906030b032e090512090a060804080f370801080a050c0d02040b0303030c07150e030909060a090c0e100201060807090209 79
    0x1088021081c0f00c0c00c5c4010801d030366802c80c0800410901862804441c440000c080200320b00841d00080e42001060000c020268500c0d401950800d010342c00310403105009a000c58a940d20440b403c03070000d02d2000080082c95054040c41441c08070840140c46c0181d820f510741c40d01c01817925000d4440d16400181510321900e90f512a41440b03400c072040d9140050401000c02e640d51201c10740500540e8521710005000c1d209902d1a402940c2c400c0b001d52810654004a110a030040e5a0294150038513621035400403100f0000c04680d03040000c8420182021160302a1050300142d001c08007641103204940d00148011071001c000c00341c220740c40c000201040c004a402418800025034140c84000305000040c40b600c00a0000c0ca40704117200b144100440320f00310103950104021940b15402800500070b6881c021a965a00241c094140307458544d07180d180e0360a036272512220704089056031604140354100000e01008020550000b800344500d42101d155803818503208111700ca0740d01150038503c0f640c2c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 444544460 1250 444543210 444543221
    0x9010309022403150108190b0a050d0b0711060c04060305040c170601090c031514010c060501090209030f0a030e01140c070b0405031b090a180c2c010302101101 70
    0x20001954403540802c800b0101c1c1641c015200b8074084448805020507540c400e0041a100340b1020000d0030800003610b007070002800c50044c8080d0300030408000840c2c2d681b6540061400355008200d240034909101c10003508ae4003000c1c040c0117258208504000e5851001d40481707080740d08074070300028103681d18240404140415080110440c1c1a4082454410000200b0606840510104000051400100ba41102d413150b80c0743c001010780ca5020030800c00c110315030707600c112010b0500107407200650303030745500b280e8090308041d1010f0390104105a490170200b003240c8080c20b0b84002041082280d4070301803c40200e004010f410880920b03c9181a85400c1d004d4461160010301125441d544130310b2114247c2c2c0003805400d000e0b210715102c45540700ca81002000030990017038040c80701511040490005054000048401ca20012020b40300044426010034010401649005084410452907c010190380c140c0315002040d140010320241c2e890a5441c0401e08507400c3c07030402468044101ea02514 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 444545710 1250 444544460 444544489
    0x5010918140703051b120c0306030109022101060b0c03160512120103030e0303071505061507151b1e110115060324090b030f0703060b0a050a06050901030902 69
    0x81c0140e05100c90b0036003640106000d614800c213298070104072900e11690720700406800c038010055010110300d03107080340e03001150001400380010840f40b03515004580b000c1c0320344403840242c0c84031151a00c1c41080030b2003164042c054001105181402c2d078822141d07680031b03040c00c1a078800944d2517402d041010400c101f038010381d140c145407610344d40d42e100c4488941e0000d01c03040c0c021400041c074114a602c5d01004513103590ba1b02111800508241c00b4002c2c008100003010182c000291088400c0c100b074201000d400030b82d100d0444050401c08140140c030a64100c841e103c0901141d90214841c883c0c1c1007074555024100002c080b9525031741c0090103d480401010440c80340d07520b010204071300024960022016141503071001d100f507541c2244044ea1105070200421480000c0352018021008203070050422000014116911200305511050601c101644200e0b4016030314480141282001c90441e002008200c407000102c510301070014105105103552a4100342c1d442d000c0004540e03888821000d2030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 444546960 1250 444545710 444545741
    0x30a02040f090605240327031b070602010903020316081b03030603150717041703010e0a0f0606050f0d090b191401121502040503030a03091b05010918 66
    0x40340c0c2d51090100901c510301903035004003104008483e10110700400014404ca010b80700f2441d41d501e0240440f1190100204801221511240080d0400382007000e01035809605030340e0304541e400c80c41d6051a15038298048130559043c0300121010907004819101007008024101d51820154604451144a4440d80340810f079162150149a0580000514810ba00944c12649504580700441e07411030811500c640000b00021000306a4450401d42182c005100e01107080d202085042050341c1908260010244120210100714100d0210f00440b0164200c070310782080024117120b0014403078400d160200302c4039100020420b00b074010550003c0c108039007101840074282080c2c192444500ea01c468099104e5050080c0d00140c0140ea15200303040f2601640d103292510035596031034110b18025440340da0a16420300001503151401d0006203100661580c0014039400d00d4a8078803100c0500070754482c0c03842e102140c1440140d0b0003016031030641d0380141046400c05001d1355640081c25005604c0300c0c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 444548210 1250 444546960 444546989
    0x1c050f0a05030402011d0a060f030e01020409271a0c0904110319060f0302090c040e070504030c2111030f10020415020a0506070e0f220f0c020a0602030a0204 69
    0x5154800042d5002c3d80c802d0380c459500030f43c10b44e882c40701d0011442c0480e51050380002d0401240b80585456411902d540c00d011a0322a59401c006089030450751105880d1501d54100703030b032250341c16644001801021b00150842d601c1a44855050741d83c22100070880400a00100e017680328035406862411300700810900202070305409108183e081524200400c0d001c0d00c4000c1c90318800b50242c0c5080d95100c00814690030b28540801c60201006803a08076041800c000218048894a0341584218965102c0b60fa0303441c90b5107440c0104072480d82c02809001444110982c50100303180c216801c9075041165a40001c807813800190030140742d4080b8544501c50342d2584652010950064811981c00034001e00c1450250340e001c0c1c0c4c48101c1110010600d030400c0b0002000300c1e000c0c0d401c54580e5040540b40c4000480690040f40c0c4443d10124064141c1d4001c0c0504107004400e40a64a2030031108081440501d100034006580d50001810007425140c000c4001507152445606540090004420303c082 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 444549460 1250 444548210 444548227
    0x9020f21010617061902070b070e030c0d0f02090402030304181a060a0c1e120c02030606010315030f080904020403080a030f150504020c0f0f010608060f040201021c050f 74
    0x40c16854451020300650a1040014418a845407a4014080d411000d408aa940c41e242d0a0301c84001c80c41c0c1151040d0300340018000f103080044194483c0c400b51300c84d444d0b0244d202040502c0d004c00c0c90016445105a1410ba8002a100d68814206254103981d9680b45488c3c0e840042e0660003180c0024402c0c0410f0300c801900d8101a030010102001c001204900703c009000500005200301103034200411a02030040300010704030905040b40781d40381d0312814407105241d0345030040c03811640d48600004098500c401c003903280512045422a00909080104101d800b4482c0d610100c0b03840064601d010340da40080600c40d01c4401c881c201d010040c01150366540f60300d01080c0c540c100d004030303100080c5032820040441420780318400c440d81d000d10041c1025841c210402c000f030b50041c40d056540d4010300c03c086442d80410480e903410a600324001084076400d102003140752017002094054140c1141d0280005030341c0200b040103007448c1052160102c00300c06481981ca44c807a040000206541c00102e020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 444550710 1250 444549460 444549499
    0x604090819020c06270a0303080601140906030109020301170120073f05031510030b04062402010b060316090b040303231813090b040c0f060516030309020f 68
    0x80d080032010ba40704005d030510f40c0038090364450a00008000c40d030701c41e0128080c1c4d07000b031003400c5401d80c1145040303140010360004034240790000e03400042141d170080014000040340040181026591100822a0316a5040c03048404483d40c03c0b254880d58001503030506111001c030910504c210304075a00e00419541655080280e802c1c1514200e01d0181203880540b1389109500300d070301030b144085042c00f40341c038140c04001080c032034402d01b2824140c0e10402140e054a0324010300004041450f100c401035400d61114080314000c0d03200420031a450402da25560f6510740f002e40360003158900100940d5034003808181da0514058000e1141307494049800001c01d0380c030200040460400b260b5840e552101d0400005e40c50007000701008100055204c03245a50900c2111000c1d80402d806022500707400d00c0c2c03a00c03449070070103560940392043c0290040c0003103503041c5c4141008010f945480342c540b80101101a203170b4102c00c81c0041c200354aa000c80d906559400c1c0460303407541c00080001c0c400900310300350319 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 444551960 1250 444550710 444550747
    0x60103050a06050c0408070509070512090f01061d011404020915090315130303091e0311010c0203040506120402030a060e0c0906060a0210050a23010303080604090819020c06 76
    0x110b45080c20000011802d0310110199001c03200300c000200b00681c00c000c02c00c803007480020a204100305040c0122124242003e0205000790402c0c4041d100da128002211400e5410b180c2001d0b84401d00c02142507032400440300700504443c07401210100ca08114000a40a0b115182400741c0c040100c840110307880c41b03440014500220308400b250740704140c901c031010800e10100da15120040f1004500720100b802500110551032054a44200503060b0303030308008100842c4082034000401050b05900a54824400d080701d080e40341c0011424140b4210002d41d8510031a003c1d00380c887d282002003021920100520301c01075504c250280304040650142c9039541c81d6144010f0b106081000100b8058101403048903000d1065602400741005800070000c090400505404003090761544200405869100801030300705010b000880d03207500d07604005113140405400c2d03612461418104e24001091041240c0707048040005a02010700302c02c03026800d1075001e88140d82c00542c002810b140d0b041051211 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 444553210 1250 444551960 444551963
    0x50a0c0606171b03070308070f020f211002091c03030905030a0e0f0a05030d0c03020f0a0c06090e090316110904050c1302030f040215040909060f0c02010207150c030608060103050a 79
    0x100d002261090f08241e514034080c0300142c00c1020412904001c86c001800d8440054000b40010280000e00c03c0414200d0b81c0d00d0a030514001c0d49217000708070410342444644980421a4400c4d03080c6681f071000211500b699480005181702e1091488040600941040241a400c0826240c580401c0840a03040325280c448030b5100e00c80d40340000220f4604030b4a044140c51002e001400302c00045181940c9100764064103605520034140d413140c41941c05c00001e80030500c07a000d0340038201d2408001424210880d005180104100c2c03003002500c44000066803038148101d200b10300920109c1c100400c4100f03114800a80018600d82088280200040c04d012902070a660f205820001590040124002903917110808401000810090300e046030b4650702c005981000c080c5090b5070380e1810320858884d120304440e200e840b03002c80007940100d07201b07170310078510f81c0d00095140083d00d8be90341074100e00c01d580c1c11140595078140400d102d4070a0384030102601c9417108440455840e4104259030f40e181b00030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 444554460 1250 444553210 444553243
    0xf0a09020a0203090a231c05070b0702040b090712050a0f15060f02030406050909071b150c09030510051f061133040f0b070c03080a020307050a0c060617 67
    0x702d00d481403908200c8952100340d00c4811905250401a2201640120320301f0f054901162038045942801604c00070405100d066503078103000c0c411700042d030b900f40c0041885041c4180030400e2594001102084019000400140c2079591a050720020b1800f40c814010003450201c9109038600b80d0002c0a0585559460f28910b104200608990741e204500805c800542c09000d61000c2d801d004c2e00180c2c01828a050940003080403440440314001c4a9005848049540c07424905a40c032901c5003030506107803850310103038860440c2c0b030b2207950380d08811701080016603401c001105a540e15030526400e403111100d01c1c500382d503264801032000000c240103900e00e021f08000c48040c5041c4120f40745548100c20300c19002c49405140806000ca001002607444d41415a82c8600003030100703040c60701c80c070416191100a0840ca05000700321301001064000c2c09841007050180194100042d035003144018a803503028045039103048400b40c86590b12601512a030503000c850301c40004540386007180b00032507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 444555710 1250 444554460 444554479
    0x3020715050c060a0507050901260709030c0b1e0309160609091503120c030201110f03010905090d081303090515040501080702030f030109050a0207021201050106030f06050f0f0a09020a020309 84
    0x2130303030408488054401c0004510104445107295020f00d402c0b880307135000d03460401008a24900311030030000003100c030440010b424400a00c10400b10305c1c0d1410141c8060514a400c04210390f03121440000b0601c191402000b02000003800088200900c0211150440884035410f50b141e901414204c02030060940843c18420300d0b00c0109250182441201e0300004030090300b894030321040d50010100782043d4215500c80e000050061180340c001c181c0c0c0407030040d80036920761401652000b160409868030036076400500e5100c40865001c0e0034903801c42063745020001d98070901d000e0342c2c284001d600c000c3d004050f10f00301802c000c1240f00504200c840a0300d640c001c0f507480070f0049072070748686291080301c03ca0134401442210040c2d4441c80e8004034041005182c103400d03400042504400d48010402a910380d00180b203100ea06010344a842e08410a050004505100008000220120000d07020b040742c102850300542d9403003607100003462a28011942d464180200944070390005100500880045 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 444556960 1250 444555710 444555721
    0x6010327080703020f0118120804021509010504170709050f0c1804061d010303030b0f0609040207061404030309020a1a030a09020126060f0d0c060c03020715050c06 72
    0x829140400c0010803400850280580d440e0603031030304140010740440c0302e10124100118424030544c050114030f4000aa0030310044d28010900380d1421040504200b02c50b810300006844900c44203100354020b2800301e0322410801c5c0102e030240503035804090b00d41030a22000303540c100007051000903194250310502240e521030f10b105040e03110960713460901480400c0009140080310181c20301c1706200034004204540c0d100321100002089058481d6680745000040080641610948002a805991b10000c103514400005c2030f90083c100c855011380d400146d0b80042150660080d25000c401d854242e940d07003020308004004207003424080b030250b1204080425082544174100d036001904544091841c0d8441d08040040d140030082207051040940b1225a10142c04140c01c180c1e569071140c1c20601d01d4250104a0004803d0500d80d000c0c101d04074003e0301040820340f50500395006c505205800380c0403132400b24984800e43c1c0c010401d042400004900c819848002003018400c100110341840e100e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 444558210 1250 444556960 444556991
    0xf040f020d0501090c1e080709030f120e1e2205040803041217150f03010203010801020c1e070b1e0f03240307150306030c06080601120b01080105060304050307061103060103 76
    0x560300e000105910311104002914800c040b4554012301618026201541c1ea544071421011540c4084503240c2590201c5080107501030310f60008544101d565011030100c00f0b0207d840c4400301c0500710700940d01038503105c4070600240301e42001514401c1d02000381c0c1ca81401c0c02c507081e8100303031001c0302c50b4050300b121209a00d216040600620143c40700c141c101e6141c41050300b00c2101e10380e9116130801039403050344c1023944c0d007880a107000300312007000580d9612400c90114203150704819140444006030b04042c00314131000800c5025144200040c80e0b60386001603001e400a200307160681d030010400551080c0710344440303000e9801610740d400344a454260300210b45070303e144042812a0150f0140702d08100300841031804034110306242c180021100d40701c1d00e0309400c9030040d030080404100307180184081c03035910076848440390780c513000108590450840000e1030264184540c0e0b00c07505021000c41d09004040c011101c160303a001d54100035071051440551155002201c881c1d010034a01042c0e00702c84460b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 444559460 1250 444558210 444558227
    0x10b09090d0503271006090e0304120b1801090602121315020d09050304080d02060f1005010c0213020d0501030323071e02091003150c0503060f040f020d0501090c 71
    0x306074580301d0030f5a48440c0b60301d4090050b80a0740c0c880185011903504000801d1081d80c81603c0503200129280e401c10700e00c1000e6a80c14429148568010082006008040f858440c0c0e1264001d074200b21075159000c05404802003440299895445c01d0345442c01c1154990051110f10500808010659540100c13603480d04003071007000d409024951104408500c16900420301451400702c00509200c558903424a150002e4001c40303413542c07200d103100780b0711a01007010b642d010721040858007140c907000c451340301c0480042c89a5818016018402d0b02156900c46071034442c01d0300c3e041d00315200c0320303c4245480a082d083c0700c290046100c0d500e07910f10481c2824001700004049400307191802020340c1e141034900140006c0d1000048003080484010307074076640094041c4040d070000350090b50031070801d0f0041d009040f0031001c14900c1c15050440140e0018292644844120784440094860001040140043c2400030300030a100059130000f0003015441903041c0c9280740c408119400d5118000c1e00c8521 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 444560710 1250 444559460 444559483
    0x4020105120702030d061d060906011b150e0102030a0b01030b030d1b08040e07030c050a0c020f01020f010e030714010e2a030601180c1701150e0a0602010b0909 70
    0x2441000301d40368425001c020340e604a00e143c41141d1420f0302c0d80d00140c040356035540060020041102c0048080820a00407e42000c0101d91003501c3c1d0601500203880c0720400c07600383d0451181800302400b800070742c0030ba403580c0769820b610601480c4804601c140c002d60040310800c081e949482c241d00f4541d403091292440d1640c2c082d0061481d08050704040d20105402c3d0284500b07601480c4d150750002e42da0101910040c41c2c078109841c0c0c9801c18500150a442d0020301070b404022061011450203a0300094102c1415015651b00795081c000100403410b09144407103d00466003410444540c140000004041a500541a803d00c072200040206e003620b010002d1540da50b400040c2c0b030700305035280849036001941c24003080344032000c0d802c01107420400c00f6444036101400310801c2d110801414042c0b461a01d0072f5182c200c0306140c4004050541e4841030061040c0e980700664510740303641c012100c218800754010a00e0000d2617070307404024080c0c048210b03520b01401e1a940481c048000c00141544040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 444561960 1250 444560710 444560717
    0xc060a0e1903020706050d06050d030525050d0e01021504050607020c090907060503190905010b150c060a1e050405030306030f060f1501261807030308040219050a1502070608040201 79
    0x2490090125107540047c80c044044556a80707000400b582c0f8102c003041c100380b0a4450603102c8044241a198005491704201d4443d000815201c002a1011890080c4070700542070103403c409000b07004030b107040a003680200c05202284240310900c80c00107160351040f400360382150314004d000418803010f0441a0380201403688400d1050010074082c03c09154002c078046100400040c080080c4c0d4142d0710010015581030359941001c0649003020f440e03006000010081e0f41d850b09501c4c00406030755001c01045100016610001403124082100010794885a8110140000d0401e41842034480d071095401521038410505000001d200110b051849920410b02d40300f01c0b41c0c5c59003504002402c1e54802a0304000420304116244080120071002ca000d462003119002c1c40c202580141041c41a045603c3c01e6009017000c00010345d2101c00c05510030350544400c0e4001c800c1e07000e189100b82d020381003164014100f10020503980e0400306100d0003102207908a8050698078001034603510340070345011303001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 444563210 1250 444561960 444561973
    0x81909061e06080d0f020a0b090a08041401080a1107020103050a020c0d080a05060301090f110a1a090f0a080a0227010b03070e0a0e072f03040e0108061302150c060a0e190302 76
    0x10548421402d6840740000e0f01383d40e50b05500754bc46002e540e01c2500000000c0c03658802800c001d59111444942c06008540200f00c20715660b04d0990480c090207100038100340c1c40e000007800301e0540303805481c4980888401c4078644242d1610103841e2060895100b00001d00e03060025415190501600b12400d41048400c0482101a103c510031180086207c41e00100c0c181c0c80020ba00702142543e0700c13005076007a0440d1315010403900700403040c2400140030788152017503e024011910003040403510103a04803020203800040341c0043c0114020f80018044800041000181420a1800644c42141c403079441028a102030750410000701294010b0002c0640e1513400542500d00511213201c1c00400010105aa0802c101d1001c001d511800009541600049410040070316900310042c050840e000c040e11241ca414088142080e2240c803020b84180e180c1000e40005888020880708010010707000e540c55071410548040c05043c0404100c0460b12950900030102c03ca11450300c4120395041d80600728 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 444564460 1250 444563210 444563213
    0xf090d2102240103150b210c030105040c05270115140309060c030901020721090b1c090804090c0518041415120604060c0906081909061e06080d0f020a 66
    0x603501004400401c0c60365105400c2e0816600e42071030300c06400c0444034205102c00c0e007c0d155801c141520050703c2c001da0400061100040b50540c0d07100c1a5034090741ca22a05051991400039428900d401d17040380728070740e01c0001c1045504400b224170300d5841c648500d082e00002801c800514032003142d4803200744d080074000c600441f03c07200003160401400000507042c003c00c0d488815602a025201c0ca190b400041d60300f614454009410302c009104420300c0ca401d1002000b80340c916040c000102e100345903600d20342a01000034690640d00070b0a080c0c0b2041000070411300b409419640328010000c4090303030340b070103c00c1b031440c082c0148083e4040d0640d50003a151a02550600081c1c400c840c01c81d4014018413020f000284100700c064451405803c0100e00e1401d01c04001d012002c15800c44410003101c5000c2000c4050071941d106070f45004504001900784c6182411401443e5240c401294003070503945110340f0740d03025081001594441015180a40a200c0302070300c0a060300c1040e0300150f00007804000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 444565710 1250 444564460 444564473
    0xe090c0316150c2102010b04060f1223030408120414010e130e032a15040302010b0406031a0106231303020d03081b0306060f090d2102240103 62
    0x304200c8030b5041ca401840001d54480d03030a811804100168403141266130001141e090041040581e020b5a04010144c01e001c40807400310780600492000c100c0e0860740f1000c00c81c507034030144520110b4425000d801038294002ca42c032a0b1061080c000a889000c0c61803482d042080c0441d401c8865481d9618068036580300151908038102c40b405501030115101e90709c13000070070702450181b02e0145000d1680e03120454600b403000e242120b2100e01090003410080e20190b4002004030360300090611031800b81e136861804130701400c041e8000390f401909142001007046181640091a0111002211140da0729210111034a28010001c0d00f00c0058521990040c2d0700d00340d0050000c1c0c52071001500141d82c40b0380100716074640c0540c044002900303040800c40c0d090000582c0c2480b8084030b42042d851410020001103850081c03c031207a401e55000a544d81040da220040d03400060340c401c0f101c944081030700c0b000440e010511151007000d80148208108c2c0b01d01c270040c038846c0b1041408041c000c03690a40e01c405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 444566960 1250 444565710 444565739
    0x5060403234b040302090903040f03082808010303020d0206061e01020102040902070308010314030a05180f0d0606171606030b030a0812010302040f140a0c050403020a0e090c0316 78
    0x20281608080251046800e038051405608040c2611080c0d45501d0345c4140f1190b008003e000100a82040c8414041c524012070b81c50100c0e50030420f405d480f1000d8200114211803030115000c001364012000c0e00e1420713000030400d4100c0b4002e80a41f40c0c020050742003a6140d640807211a0ba2000d000c1d58503200143c2080714200301e0f841c1c1071000504164480300040100d07400008103901003010309004100b00450710802d6004003144e00043e60400510302c5019000e40101c074001c032660709907802c000d8015195001582c8000300000d1100711800110b0805000901440c0900940c10080018041c050103000900e968100e80e041c50f080c08462900b07004800400204220561500032140342801080800c0082c085c013103104082c000c59941f6610405c0116924003070314503006401c1030302c03c100d88031401a0b10f640c450801381000c94910100d000032074891050380c200a40c000d55000d4007090b442c092802241c4105813000840c2c1120114004150350740c1d003082031214190b00b914905010012905142 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 444568210 1250 444566960 444567037
    0x7060f0c140303090f030a020601050616080711010905010c021c05070e04140c0d0f060f0e0a060203040b1803030a180816051015090e0a0506040323 65
    0xc10840c00c181d510310040340c05201e10403085910100078031a5042040c003c01001c140e4503c002e51620088a1003e5121041485400e05c26000403802c4503000c001d107a148248158409032160741c41040e0300d040303580304c5000030b107036030006080e0b400c08039065014007204c0301d1084e00100010020310341d141145c000100503003011601401040030004130b040428040358083c4d4031442582104600f00300f819440c116651520b03d201d69401b06030030000c925a0a0041103003504003a000c51002c03000620304000d012455040440e9100307403101700e001c1c0103e650195005074414070b00340c4460340769100f440d0394652010850307100c10307081000490034099003988070380c0c2200c6120020400214564592083d56004080d0710200946070654010810100b803101c4044c40c104100100b1203c55010a901c51820307241c0500c41c103036642c030540c1c00e102c000204400340000b6885412a000340c82c0c81d00c1d00904481483d846040c0303281d05030140c4618000c0d07180a5844880940981c8001e018555100400d4403e45010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 444569460 1250 444568210 444568217
    0x40506030a06090302030307081e061207030c12020f0a05060f070f080703080708060d03020d050a05041e030c0905070804060902061b01021c0207050c0103020912030d050a1d07060f 79
    0x400000b003160040700c644900940145869180880c8041d144040081446150060407010150b0ba9500300701c84540214060360700440b0b010019203039900d424000d410141c08503030038150004003d02440000d10b050303403085e41c807030084e402c0784014482c1c20302442c0159171f40140148000120000e4640180035401d0140c41312a0728180507031106400c0e82d10200c0c059000030760500412030b2880d0441105a040742c01520782c0e10703c0181944000f03403a08040181e40d41004030018034405058881ea00b5076001c0c02065802e0030f45411403003c01d801c01c0f507803480104c404150860002420712598490030744243e1a503159454035907600d9982c0f100420b49a50103d034840010302206103201220b004840380d0004550006a8450840c4d549150001d0508020720760180100052000203c2c00b041b03516a0f0002803d001d620740c0c8034200000c10040b03654085035000d01c000309a00d00040ca490300140d0050f588107008010b03610042000104182d6550041880e60380000010848144511040810010140b8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 444570710 1250 444569460 444569473
    0x4030810090c020c0f030f1f0213090603050c09010e010b07170c06010503120703050d0e07030f030806090a06080307110f0d061d030a1209110a03030c031d0d0204050603 74
    0x401c1011036105100d942c0050b40005155041803d02190342c0c4181c2000710002d00002c0d212600640d070f140c0f00c0004c40900820b580c800880d00e14082e4059410380c050001e80c0c5c001c920340b522041001088184404e0f60700b4440d000314078650f0300b03142d65528140c45005c140b001860303003812200c0c1d4a48e481100d0465420114003840c410008600000d056203900a40c0a8034031545031008041c039040f0911400d0304003880801070f2000081c0c00ca800c0f207210503c45d65000c201405403448190034404540c1c40079007040d8441d8031003010150b05c07046c0300e0f205080c00c07100c100c000d40f0f422011408680300c2c0d000742c0741164020070095000c00e43d9200c0c0f80480510051991031b0000400c0041542103c1e0a0b400f11a180d480303072000500c3d481c0d04103188a4120303901d00254200420745000502e01100ca101407103013031381c1c1c40d200e00060104400c4560303140f04002d003520801030f03500d203802008010148030030b40016191410320320000c9108010b031801d840000b840007042e600c203502003000804000d81025407500c510b1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 444571960 1250 444570710 444570719
    0xb031006260a14160e1c051903030e1209040f15091514061e0c0319031d0d03110706090b0609090c032814030301060e010201050f04030810 61
    0x1c94840c8116030741600031402484960560924520181c804510210001a40c1c04140d510924200c05218126042d0003c5164030030f6100007407044a0001c0c0440c01900084020310054010003034800d071003035404115207640e528000c0e8541c441c41040c2410702d68100000c0c141e134545a04070980f60000340300f0000380000c0c141071040c00004981d110303024081e103c06605030078403001c1d01110010b1018003100a00031010303d000070b80034410310045c2c078203090204e11090342d100c68a005a0301c00d138000c042142e543d040e0422402c2d1800c003030b50054100181c28903550b40503000301600460135540c186030040c54450040340f001d0f00500303415070072144510b070240074a40c00b0444070b00404c810746028200103c4203003009024800c03000390042c40080030342d000c03048600310754500140e20320314405a075010011344c01070050490100780e401345000e4054080308295040c5c0c017501200030343c1203861070b80780d020b200c00b050001a03003030710b030102c5811980c0c00640c00000c0101c3e002d0600b483d88110f40f00f906e0345955454 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 444573210 1250 444571960 444572027
    0x315020c0f1e01060302062b020d050a0c020f0709020a12090b060922240f0629091215010303030605090f041119230405010b031006 58
    0x441105155105a00c00e680b9540880c03000b40080b150301000b400b4180c03c40d00450340768030400710b0001441d0b260301552218000c000200310a00c40300b208066641e001100441c1c00a4201035410079225403600d004401451700010714454003528110141c072005203010780d004001e40240e404201407084010703101400001522558002920507080440e01d401d100d400d00215039402040e81e0005000950402d0840030041465a000e651003044290b0409543c0c18504107051441460010581400702c0480c02441c1604403c060b01c0841c041c4800e21440200e5410951800840c00782010404010340107a5040502d4a00c500907215400c45015400035803d0b60280c8500768425070000356a200c1c240000e1600c56081c80d0441003041740075201d810603407030b0401c2c56892090600d119811019004004061400d48000100645250350b2007101c1010203c0e00500724054050f4400e51424002161100c040700c107a034007890201e940c8408031400c0080135070b81480d00301d09511445204d0480390303400040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 444574460 1250 444573210 444573223
    0x31d01031e020d0606020d0930050a02040f0510060e060403050a1a070e0603150f090709032306060907050403080a0e03010c08190f0b060c01050f070c0c0315020c 71
    0x301d0110050360b41e4540f82080701202c4e00340d0054011500428000c0f84c416034814030324419a1004003034480301212608081c00c0c034401c20700c09203a800003042100d009000022a600460314000d90303052185940a10703181080315012180802101c036104000d221040c032aa450f480701d82000781055240544a4442501e010b80349a002c6071a0105111034910440203038007441d40005e46828480c0c905800c8a00044107804010161440e1800d42d2500c506140d440306a0a1030036440581440080d043c0b9420080c010541c500090300c1c89142c660108420480c9070b5007918926405030080c2c401c41d15450100300d02d1480240c9030104108080c48003101050725030f00140114091501c0e03040130100c03a80b050500707554004024105000c00101001640720144070903041e483d5810380c0000d000c0d010142c40c04014241500c00c10340121000c107195030f400405600050046244007400116951f8200040b5552244148000c00895010508000240704001c040000c0848070300c025050046035007a00e0700d06003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 444575710 1250 444574460 444574511
    0x6030203160303081612050a0506100507021e033a08010806010b0715020a0c03080a23071101060e18060106021218030f10060f050607140c031f0606030603031d0103 72
    0x280e4489c1403003220301d844003034040201102e00340182000e203690000796114210b42c80314006900703000e4a002c80341c1e0741404030703180c594540c4c00c42e400c160000d000115500300b0021000e102c0c10080b07001d549103040c041c03040281251010b0307004010380da0800342071413016003150300212080200c014076908824068006001461b0581d41d07644981416810010303c008005011110700c0340c6840070640a03203c43d0940d01c0c3c9080313502101048952107002045031080130401d00e450b03040d4a00b0718045981411010038a0203091002c6441040039211806a0f4031503c0030720404026900030000d4110b901c0c4035101404c0c5411201100100001c1d200011905284c00007002000c650403a242c0303410400e9552180794041d000c031100940400b82007a007c280144190704001d4184480b0484070394113028104090001610b0240c1590240c9030440081c0b03511102008003046a2400d1607800300714144030788551812240c0555595003040030304030148960444040a141c101038455503580002d0051200694508 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 444576960 1250 444575710 444575731
    0x61104051320070f0308060f0a140f04020910080c040302120105180613020613150206011503020a0c0609061d0d031a0a05121009060603020316030308161205 69
    0x4241958011011800e020441c01581d5014010b00f404144628001040a941818110040d854000016a1072680009510f030700691402011038202c0403481c0d40740c01c08000340d0b00c0c802d4203036080c410403007640913000505420100041941d17204a215099050308080d01030009840c084c3c594000c5616502400fa104250b40e456200380b0140b181040055480e100d07182c40a1b200340e091591f503800f1b9025504002a02c03e01c004100034003044024248035004040b070104c200b003c0c00b00b900b03001c1e454078030134030500c441140025610800030340280201d0b00c2c40300e00c40e0f5903140868042c0c1c0e103100091107441e2050714800d0b079039080300d000449d0b4210601e0311043c640005004100c1c850340000d080e2500c890719010010154102c00149403500381c0c140040d43c90440d1098040ca55500c00c651401c500d08451100c00b0f41030051348018442c1035404481980e00031b4040c0d540d5541e080c80c00350b43c0d10622b0300c401400107030707440300050492600c41c2075074441240520b4607040582c1500c003d2030a4031810f4424032141c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 444578210 1250 444576960 444576971
    0xb0312031f03050c010f0203120906040302060703060602030a03050703090f05030d06080a08030106030b0102032205041d0d1d090f010e010e071202070204060b0a1205070203160611040513 82
    0x4849002800701c03a2219106032005541c01d640c0c610361036240c180203031030601c89120102d00c180b5009000361001c0108540c180d601d94513042d04aaa69601d0a940a40140c0035810102e10102e1180c010b8401756170003a0015460681103d034101d00400c0000c000074101070751810b0250009041101c104002ca0040004644031018290900120ba50035070240c7c0d5250b00405d4010002603103076007624115081d40c2030008010010000517030842c440c0080c050300c01c240a40c00415003911200ca460151a003d0b0790405c01520918094150046080c075566000e40c09880c4c801c5400388034000441c0c2040103803c104102c00c0c0010041594182c0a46001204140e180014410420940d042ca40140046241c042850a00200c090503c201d00c003070038441c554000070b5132419500c03507820010080c51641c40c1c003940c072131144030018100040c13490140e50183c14200480da001d0310003c161040d54403070380550700d60000c1c6a980e02008000051801c01c40d00300a110005041e9141c0c0d0b800896060b05890100300f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 444579460 1250 444578210 444578221
    0xa05060a0f050a0e04020d08030907030b061806090703021c05160e0108041401380103060b16110312070c05150f07031e020f0105090304081c030b031203 67
    0x8140280d40020520740d0803040100400da40f10481c000444410644041041c1c45e24008118298060600a04848400401c0c0700d4008000075881d07080300d00030780e40d02001d601c40e00c08101120300625000400e180b00007001c03504600d401c19003540c0203486c0b42001494403150485000905424442d8441c0c03c603038803020000908034190340c0002c1d01305540f600320700e0409c3c400c00180444402400242c10b00c2c01820035004600070940c03000686540742400030b11514034480c4080c01e080d01c0c02d1036240200c0150018140c095010340603d000f920024407440b400d104e400380368054440e051490548440c001030754100015101800a50400009120b01c00d6940b100c6090585806242d0342c4100d0046594403401550705a40e8016101c501c0f9194a156030f458185080442d564080c0700000900c070843c48940d00809600000c030680201030f004005d01c05541c51076172041d01c0b03002d20b2040e503540e5000610b44a400d8038034032440c1c2e80d808566080010703106c2101c00120b0324041c14800200700c1c11740c00005201 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 444580710 1250 444579460 444579469
    0xe01060909020f04050103051c050c100920010806040908130609030507080d120b1f0504050a06080408070809011107150e0d020f0927010c080702030f07021012050a0506 74
    0x500350710180e84c10300135545035580c2c02c1e81d00d0b5920305c605140101c800c4480081035124000700d0700c965008a0031986924000c2035580010810004211070000b0500c01c2d1907140f4003170301c008605029050712800b426955040500000d031940c5c0340e044644180400461482c0342100c001400580202d0303881c100104d065203089441c003402e0f038100740480c1d0700c4054180882613000840e2120036103060804140c1800480100e60002400070704800c0c030011162000d1000c640c001c01400454504682d03000c81281c0d2848160750000003a100135260150070040c05000c101e8000c01011100300c1803500e102000b40c3c1e00f80050508a041e00805000c0400c5006003080503071081c4000e0700c01e00220f03050214000241d000512040d8540401e90050060350300043c01ca649440d0074500c43d04c0c8404404005105080d08a03008081c021246c1c1c0125400501140c0b00910010544860001c249d40c1180b809209408002150100308640f508103c01200c0c0300340c1d0340d0842d0042038001c0b0b10f130000128650078a0130400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 444581960 1250 444580710 444580729
    0x80601050f0136030501022206090501050304020f0613060201020a020706030e0c12010b0d0503071502040518060a030f141c231902070e060d0f060b03010e0106090902 73
    0x4a0410286502c400d040740f807418030b074a40011400030107655008402d1041c100302d0030f995102501e154400300d02c9401e880c0c400c1c01c1110298120310440d100380e0703445400641e1043d41601900740020402c1c030010340182090000340200d460000c100700c1c01c00d03001d00590010005903070440c00c0180d4002c91150101501001540c004d0b0009003820701041a08140040e1749048216140740705031000200c503941a00e0a40c4035005540015006010040d130b40e040160f969840840c003124900c0084402c07000340d00a40c8280c0341038a00c02030140007401d010500414a840e4090416940a81107100c0040040c0c0d90112110364903106000800103140c05000c0c1e00d0034400d81100615001e803200b14024a22a44401001000401c04030205415a007043c6050001d008041c0030b4201e401041c810352010540000b110003c03910308184044030781c1d8401060003d80307101c8020052030000180b254800050311a0042e060781e80303028000003040c855501510f030039240981c0c805848996614044415418584c0e1103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 444583210 1250 444581960 444581989
    0x70615081f0207080304060b0d0501111c05060312071e060506040c090b0307050a0c08040b0c1b10080411130506030c03280f0602030103230a0210030c11010608060105 73
    0x46080120f242c41d5504503100042c00180b038265031750b034001465514141050401d036005070003005101080707200c085a036400324001800210070750a1300d5224a06c01c0c01603034820440540a0519001c101050f51890b80002904541c17204144101d585400d50760a00d503041c41c0c2c0110320116941c20441c0c00d000c101c1c0c2c2c240e0804820001c840100303010000b00e40f03046070380100b842d2901c5540d031455004201d40007030510800800400380040d0010b1010400006041104a410305554910b0f2000701d00c4505008a00c030443d4020500c0c4603c0501c1c01c1c001d80005e41d1190098407050020300070100060038102846907040d1016683d9070500071507050811110075440004d90041020407005070703c1c1c2c0100d0085030759518038049446040b404008035105810304251784880305544a50312440c001400c00c1140c26013103141ca00718070b180c07400e800e800241120600c0d006480140d8100071808110050207e9001c001c2c2800030001c5091a512030034429840102400400381090b07505000130440c5c1c0c140c24626 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 444584460 1250 444583210 444583273
    0xe09100b09070e01050c03040906030b220c03030807031e0603060515090a020f0c162306030a1a1305040c0902071a07121811040c120207061508 63
    0x80108482d042584203c44003000d092160319110025241859407007150000207442c0e0404500004012120300454020303600070b041d025003e04110160701c0d001c041071304090009904502c081011a00070600c8503003000d1507190204610a04000350030700400106c54000c4500da554400b001480014421180c106c002c0d483e4814043d000c400006038031510141058406590015241d0341c0d40280004880c50651420160749040c1003400000d180c102551142004000741e407000e100202e19042400c48680798014001070850f2520260207004021515900562b2100700403154665541d941509d19040d8040c034000c02c2c07503e0985806d40518031213902c00160381e40140a610001480c8840e1a2031010500078500c0290360742440449442c0170904402d52424a00704044a1b032820151140c21500d005038415152006040180800c0702c20405028001034082c82444404004c503400a1124030700441002c82c07540415840c0b809103510b01d0b4017401c116884039012500400462000d680605003046 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 444585710 1250 444584460 444584479
    0x1103070509040f0207021504180209060a030c030618020a090e040c0506071b1818231e060105010206100e0105010e191502430e09100b 59
    0x210064654000e1040440c4960707255107001d000e1031501d81c19a800b843d001800911050400400208141e000d07002d103c6542030388010740a005804c81c000c9500c0b6040140c1890b140c1983c001c0c1c00c800401d01c0419900c1010785074000014480210070155a081d568a80d00694814000d20082e00c03181c1c95600030042e01c01700c68100b10214208078860000c40364150341403a80d914207880c1950102c0781c0741c02c0d1f200e441150388101181a0621005150140748026002c114070f00c07020741000300d800450301c40285001400d2420482d514401c0c0c1c16002070340982c40440e990b010007655400c0c2c1d00701c940751001750190f020800402c801d41e4104030350f40e040011090500c0d07680b070402c1d400c80b9590304140640c9041c0f00f004031000c00980c82d484030b9404031950080400680729261003241c05c1c03184410145c480180724602c1001103000481468407140441e0002400d103c08000c5141800155116183e034685011400005641d04100039030380d10880c1208003510100b0500401c042c2101c0c07511001c14081d400e01c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 444586960 1250 444585710 444585721
    0x40b0d02030a0323040b040e070527061215030c0d050a2d03030b09011d0118020c030a08010e070302032e08010905062517060a0e0106020d031103 64
    0x2c104849010340600d821200c0050340c803404001c6071100b09907401e400000050000e441c415810181080c0c9141c084000e8207900c440328211603600404003075800d08030407654203d554150b82e4400c0c4440001c0035185905000f40c80200e80164102100c020360212000006103c1d24030341030140c0d0301060790031501da030700310261178031104c3c2d0b176442865001340680c0c4075068000c102205070128114414030780f00d22003110305c103510307005028040520f0b415001d51b04840000c60b00c03032041072407805107811340c83d492450b584ca080d10807502440b1050446089607400c1280741e1030001c1c28002000c524070305450383c520a5141c99040c03000080024035840070144188203100048911a0a0309908030b2a1200100084a89130b050340820f11144d004540c0c5600e06030700c0e1020418081101c5206441004d02c0d00001d840c1d0800300031501e1600d401142c00501400710b188800c25119082c0e07038000002400d0300450b99225010815280e0003030b002100542e0050100d004003076894050415244900c120139411401c05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 444588210 1250 444586960 444586963
    0x503030a0813020a0e07030e01060b18010305040f0206040e09100b0109050d140d11160f1503020d0603080c1902100c05010f02191206030302031e1c0209040b0d0203 72
    0x760200b034a02c0082e440d00410f40d92903c403420701070000b000302042e007810801d41c05802801283c461107195402c0c92000076882000400b95021090b50509500c026904180110028003000b4021618104906800c1d00942ca078900940041c0851a03000540c509003250182d241585d4540c444c4c0701542009901615a68045800001c84e002034400c0f450700513031858020a03402420a5001062144c05100c01c03010354091031400c3d004001c1d03c155046031080743c0d042500f5508074000c0c21038a60740b014040140315003840d04041c0280702c03860b0040c2401c0513154030506407801e50b442a00c00300804590031a00c1c841c10b0100741058014902850000402680460b912102600c480f0091010829019042c0304003074010014015035400300315030b502e0841000344903041100b50010001490013000c0600030070a44200030959800d80c006504048266000035002c00130116441d184000601628a21a0941580c0c00380032080080143e1603100e10030600040b614040001c1e0b12440503414400c002d0f840 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 444589460 1250 444588210 444588227
    0x70e0c04230301050f070f0e030d0807020a08070b04020109170a1e05030d0c0801080a110d02011e170c0f0706090f0f050a020301110301140103090c0911090301060503030a 75
    0x20308207a50114031a001140444480c01500342034055080c001040840250308120b01d00c110101d4807105c032007500c6100200c8034600409040c0b9015807000c0c10f03d480c9640640710702548002c0c030b84102c9042240c655100c400700e80018031308a0b001400a000d0100319038000070654041c258640e1100c510031042d091246d80c40808250180034081d482c0080403920070604405100d468100302260f0380d5019240890f40280b680c00801c90008404e20f00100e07001d0270100302d1424880d00140d44210001d030302020044d050840e401c08a0502001c0300f1204400c80c182e4015190004070340e1203e07054407490f506c81c1c5601300401044003041c108100701e0166010781240c203480c81d160b085000095100d065150034540e80380e4031800605200a405000e0081050000d09020001e100f94002c5c461098030321365480c69400700b0f004511001061800088072944203a000c44071541c02003100580c001e81e210f02050465480e80010003c00000060f000301509003401107100404050300150324150310030100800010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 444590710 1250 444589460 444589469
    0x50d050c0c19030207091a09090a12080c0904090809040e1204032604080f0c041503020f15030108280f08070606081014090606151e1902070e0c04 64
    0x1c4010b0041410725108001150281120040802140c2c0c0b03085011101c250b407002285224005d200c001500d00038010880702c06c0690b2000d0307515018030400409a5035894014441100302c0740603c00550300750b460b801240c445500a0154554070b40b980003d02c0142d668a04a507038142c0c0c080c1d841071506407448030031501104c1e080b0006169900c64000074600559803801e0703064080c9e101040110b0742030804610245851400030488407000c90340300901040e2185114801003048201c1000c10240c10603031040b1802c010300420300c01c0c0046000019003541e070000c0e04415000c0c4d1000181943d04100ca4240c1c00362000040100c94840a8694907240c2da01d0b01c05000510040c0046070703542c01c0083e03d8001c07601030560786060741c07004e1a001c24030800400e03001800d02004800c1002250400c0c0010404c1801500d01070407403001000c120040e80415030101560b00782040140040480b02c400c60009003407142100d001a400021940340001e1800c085d80c0c001d035004000e49400d0007142c6a28104681c1101c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 444591960 1250 444590710 444590743
    0x6100e01020309030f0304050108100e0f04050c1216051f030908070803010608040201140310050415091b03230a090303110a03151415070c050a06050d050c0c 69
    0x41961000403800e50080e0f081c466090305c107161510f03011200200c00b800544100381d0320308106035075041410341c5242e641d20a00f41400a0701021541c54548007504603031003400f1390101c0b0344480e01840071030f040680702585a02c80350001c2651303034003905003040c0c0c0c6001028221142c88542d040f903038030722000c0c0000c1d00501d400e0654a910038800c0210709402d84081d00e800c510103680b2981d60b880c01401c101411503040340003074259102e0780900301c110000c1d40c1c0250584400540410708000500009001110700f4074021030700c0010009011205002d103800920075003840381c01c803400c4400064143d4001101e030042c0b024801520142c5000c4070328600341e0180102c1c0300443c48400904055000300f94080c2303800e0210342c001032078081c002d41580141141850425455107103958030f44001c3d103500035144000c1da0100300c00281050b0082d4a9016284181c014441400705036501c8000692100660b40b08a000c1400403c1c50f40e45a0002d12031641c2c814600701d5070768600300e83d06c1e803401e44960040d1805000c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 444593210 1250 444591960 444591977
    0x6030b04050d081e012c0c03100504112d07030207140103060305280c06080709080606060d1d07080a1e02010909200309070905241012090305040603140610 68
    0x11142c1652070701c0c000041039000b02003400c00740308910165004031945c113030040c9c58002c00107071400c051140703c0c0ca01090500700c03401c0c600b651410f15002110809000051020001d11411070b01002c00202a0f03a0b100c0d0b0002c100c42c92a002d40040d081001a6001c1c2c189442d0140410100c2c00110794003804200060494080840d0031549010108000034060407081403440b01150858211000e1401020507494000e002603030344809581d03480e01190360b01e8000e06c0c28403150f02e09600d070b504403043c2d0389403c1500d03940c2000e0a011440c41d082841c1c1c810700c51980304110079400d0001d10302c504481032400c2c070015600c8003025000030300031038114070546064595032000c6095a03035030012107101c1c4042d412141c80d44c908100e041181c0c0d810060082c5900645000e0124030441940440d00b81c01c952168203c0c06000341c010704202140c05c0d181c0c070250070300001409841c0031550798070650702c08521035114580c846003040c50003002c4401c1034002100b1600c0b00300030301403a80d032910002603548000f880c08a01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 444594460 1250 444593210 444593249
    0x80304020d300e120309010e0a030209040602040e0903191d100e040e03130512190602040e0702060601020a02120717010204080c1009060806010306030b04050d081e01 73
    0x3001114141c4001e0301c030301d8044090704041c01810302d0002101c1583d180c44941c1a24400c018210300e040410b404554400c000410055002d0308000d00d80036402000580402d82e41c0d0041410200c04480888a5aa000400b0300004000142d0150020b10940041d400c1090440043c2c2030b0018400f840c01c10300405111000340e244186095006800001d0b140c214240c800b041e011b04510900c0c075200d0f1042e400d041051004100010590700841000d21056003000d1501040c040218007a01c4001494020800e00c0012610303107007407901c00d9520075030005030b6980c5400c03100751003c100605030384219000682406000da80c0015034108550701110902030200550852514103492503100c1c080980c5515401140020194080e00840c1c00d4031b01a526002820400c2100d60900f0b0440031002c00c901d420244001743c401c0b8a4141c0c0403a040c1000108183c4a41b602d80901004a4040b64603902000050390015801413456801c04900064403000300c11544c0c3c0100004c405008090400769240001403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 444595710 1250 444594460 444594473
    0xa05040c05030d030911040b0d1704030c06090609140d0b0a02091018090e030304030f0e1c1704060917010b060a02030301030311060115080a0e0d02070302130603080304020d 76
    0x400400c0d00070300f00c5016000307026024000d8403249400b950f010803003e404a00909050003807502404004241c201644503d030340f90b111782c84c03481901d10302c0c1150038000030000424584144010700035503103950001c10300c2c1690040c00521103400c1441d10503c0c03206a04419103480040803c5c555000b5410780d2555103070322440c0024021100040c1e401404480308072610354008884170402403140f1020a00c4944030034411090f5100c07402201015801040001c0100f4450902c466032422580340411542641c0070002c1c180c403003000c42480d10180711000600070407910010f42040d10000606140c1020f00e010005810007403544500c2c24100501444908000c070298410404c56074010100340d00c606911a00950340d8000340000c40c00704140c0d50a207090b005000503094100c0b501c08004038644c10102030220f45004002c0d2407560500e844449812026030284209100d990310b943c010050145940100190400c42241c40030560741f4121007071000c81c14440c02c4a600c81d806880032900f6110f6480c105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 444596960 1250 444595710 444595733
    0x50109050d05090103060801020307080105060d06050d110916050d09020a0905010909050f06010b0d09060e0d02030307031109060a0804032c2107090b0a03021207080d11060a0504 78
    0xd080d80149002603024a400c0009001580c8007a60308221032500d0f400c2c158201d00c015203100020543c0000100094a860402440c6003c507507080411041d5982010912a9030307050f40803102c0b600101420181400d01a010030350021002d2404901c0018680c40500940f05503401c003010a6100d0401d10b007517413220304a4000410820038200030b1582d5400310b4000826041404941070300030340d54030203910140000e4240c165680310190780e15050080b8502c04c010800c01f0001c845171a02c2d04000685a038044c060010b030032040340c01031035070ba24107508001c0403907040c00fa003941010014401603a8548941e010303104024040c2c2006c24030394545050684079010003021813010080c00c000d00d514084141694281214416105400e46e80360540d48102d5034016112a116142e0202d182042018000c0c0c000032110000540804500394880d0003040c4200a02007072180180e200e0350007006031a2003040100d04be40454a0103080050b2034028a41c0c8801003d8000044191601c0203d018070a568402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 444598210 1250 444596960 444596963
    0x1050c0a05060a0218060301030305091e0d0b0f0a060e0c03070e1f2a020d060b1903021002070b0a03020310170f06070318170d0c09080705061c09050109 67
    0x121101c614019070000040e45c4010b2050040c2280360802d10214101441942d050ba070b81a00d6103401c00c032050701841841c400c00007440c281d00c0303041d030340d5098140c41d004d503441b811a00402c8946010b1400480c0f01203c02c00282840c680103240807000c1040d154800310346070b04940700d40990396883c0c6403848100c4000f9102106143c2c00040d500d02801e0407410084421100d15194680310000501e03160781d2004e56000c01003061840c0443c010700001850004500d0f82220b04c030b01070008201c01440d020500c1c802c601d8a8580c0e40c0045044140154600700c1c030003c0b10541e0500c000c082281c1000442911400ba5107100000c2c1034012010655034281001c500015004004011a07070224140c503032036541c0043c1ca102880c1e80030310004070304507e100e4007aa944402940003a90080b804560740d090600809000020b00700c4001d002d400d101090324022031070402d43c2550790103c82814102c0312418880c0a50080e40b00e903100300f0000100142c007061041e02d4a1168600145150702410b009025000300b000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 444599460 1250 444598210 444598213
    0x509120102210108060f07050301030201030b120d050403060e0a2d050303250e013504060605030d02030313170d0609020a1206080c0904150911040c18030201050c0a05 73
    0xd01c40d42c4000d0000681250490000c546a035100c03040c04810b6440c06513440742c00950100300510155000790052041950060f0116601c1c40c41d0480c100d0505440129010008030f000400b003051240d035010311442c0101110103021032000c182e680f03900b0400781ca0740020040590b4806000c10440f01d61b000701c201500801600d95074a042d1081142d805207200559843d0454200c0a006082c0300b103d006e030b400201070b1600b0a4a1044050780b024860355240d0102464010000d50301180030140d80c194021071246070042401c078100006c06090285a0201c030302150f0062041125105410190b0036040d5040030050942690013452003078a8842d02010800039406d000c0005201d180787d500030803000c501c41c3c0c0c908108100c0c9800d80021798440b840f074054107500401c9005018a030170300000f60041d1160b5200e0007020b1151003804207942411005442e030310220302105c002c82c10305015200e41944586005010345244d140809010307141408041d041080208244ca00428104010003400c1e41040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 444600710 1250 444599460 444599497
    0x608100e0109050a050114034b01050112030c0f03120c0816170f0c13060806030d0804150f1d06040c08070e0a050c04050909010518030a0509120102 65
    0x500b810003602e415500c020102c0c0c0380c50300000e140c80900d81c180040341d500802500c10021006100d146980030742105030150034484560202c2c0749124900e8810380302000801c0640d004c1445115421114140e001c0b000f0b0041c02c202c03400010354003610b50758603035501511781e04031000c40b03040850709a100e00441c2406240b178000b90012003508100b2161080038860049024080c40700700032190803002d920003290109805005c070303010641c0f07402004d6000d040c80b450b2a040c41d4125880b040c500c1100d60054000c2515030f0b088c014241000d0085281c0007a0a00340000350f0b003040e0b5074400500704580310700b42c019070b86c0f84034900f50440da580041080704101007840c5009000b411103951900d0302550101c2d1000d903907020000d51000c0202c0e031842110300034550344c1d2450761500c154101a000c0148240300e01c010130032011405580340340c4018050075031000001030038a001084400480010000f400b4244c5c0188002034404c0d5014007100c8072101d00391114002d4180c1c1c0e480c190b0190150030380400d100e40611 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 444601960 1250 444600710 444600719
    0x3070311011e09061508100203041a0c13050d0201201e300702120a0510020a0f17070e180708040302100207050606060c031e031e100608100e01 63
    0x3a009074200f2070180304200149102a80312101c0c868540c8120220b076081040304c4a89140e0541c00755a10074011020800401c1070100c01100c0700d001281c804200810205030a41c1400e0441a04800351905442c0b04450410035000641481c0c40c4096202c001290812480c2c80300300300307001c0b01100101c88000c83ca0300102c400850f80c2c0b1038400c404d0700f030102d2035041d26030720f0041244151140344c203680390907451800c00c07541c003401401c0c3c603514010540d030322510b025440050800c00070098402e56001e4016210240d10380010070042e40c010100007008a050062000703092030210040e004401c5003001c2d540c405222010a0070f8099443c0490900a1b4820401496075004924203124901c43c0d800d48905141c440d000728103d00980c2d10150441d4071400000d009030034060001d1002e0942c8000b181d04025000c80903003001c00c40464070002c2601d001c01032050640c44804960417000104928100c40d1500c2081d180002003d44111802c00030302002060ba80004c0c103040c03402400c0080314400086d0b854 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 444603210 1250 444601960 444602021
    0x60901090321024e06151b010606030612031e0e061b060601051305061602030609070509060123030601090308040603092303090f04180f02040606110307031101 70
    0x3110a850b000c0d91845103607180d00800301384140c11210440803039283c45e181c0000b0b01c400780301500080c0b04c00a201700700000c0b0409545001d01241d20010b00041143da040074001020b44805500504242c803400c000e480020781c0000319644018800c200700c3c40c14803c10a0300311801d00710154a00e400480014602070941119844080789510038003c0f40c800c3c1c0c40303000044965100d041da0700c81419511450520840c540100244828010904c0c4000c80d00195000070f42000070988400f007a0b6405084108060708219140d580c0c05042420241c020320500b01400040200211810a040750004000b0716242c0c09200904083c0d80c10094480d11030f921418041c005044080d41510644c0040c2c0718030341062404c01e082e000036802a4083c50504a0807014040400c50f40c420b0150b11a480f40c0d004198204598070715407919000d5060190041c2d820b00521048032081d4000c070b0200011460742d0011802c000007200d00807949890480f403140c00061526004000c0101c030100c102c04039681c0426a580d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 444604316 1106 444603210 444603277
    0x150f01030c03060f0f0e10050a110403020906150705100e010603030e0d0c05131e02090927070605090f032d0f070308030906090109032102 61
    0x9620408419170700050703030b6920141c4c030456042c030844203a8088d0a0b0003420540c01003001d0000c83c86407400500c1140070283c0201d0380d00c00070641c162941d20b01030800c040454400c544803821807a0883d2124880e0007520010f50815403408810801842030404a0f94151103034100e5034112418012190b2506005440285240038002050344924007036031041d0040d070000003851400c1081f51300214180200824500740306004103103440d12214803040e00840c281c52040c62513003000c00194100c080d000d1802401d4010380302e0004529030420301401d07400c00c04440c03401c111544da03c20315a95503080e141252104c4503c8180c1400195a1050040c82e090b4140644000c50f0900ad103075442c0001ca44d200b00c912010000401100c802c00780b0102d45c104284a0082c0003c4080c1d481c01440340c225032040d440c0d42407a840780c41a24542580c100c03400011046a8070303004508401c41d03064a00c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 444424460 444604316 := by
  have h0 := BRFrame.cov_init 444424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 444424460 ≤ n) (h2 : n < 444604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
