-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0501
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:07:44.674088+00:00
-- url     : https://prove2.me/submissions/98b2b653-59ca-4c83-8831-f409fb0a11f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 89928058 ≤ n < 90107914 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 89929308 1250 89928058 89928107
    0x7020307140913171b0f1609051005030a0503280504050609040f0e0f011a150a170112110103060303120c03200403050607090305071202040b0909030406 67
    0x460011075004200c030100400390040f001c144150502e1061940d0824102d0b16130314903640e911500350b02c698001c600c10300c0c0700d05d100c003a07440a0081516074204c030126a551031100c1c581010709014140180020442003055200451592400d201c01229680900300869541c10452114800d12210750401c480c88001000e2040030241e01c90129030031100100c50440d12403c0740400100100b00584a0310045441c0121480c458200030400058004010008020440400a00c0348044070520911a03001601d08e511540c0c100d0030a0145c0304140a52400242031a0f0000113541d1850b400e03084074511076203000b072a8081103000c0d80900d01c03640342840d0a112813891994085e101044e56100280c910303844100340e2125520aa00c410b40d03c0c104850b405280740321310001000300380c0c424001581d040c01203400084000f40946609001c40e0f90200c0103100c481d02c4d0042840030b046490100326442502e030601103455540f0001d41d90300404a14001d160f596240c02c0c005441c000020b56505804400c001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 89930558 1250 89929308 89929349
    0x60307030902010509132a020318130c02010b19080703120c050d0e04110c0d03020c030c060f0406050106020d0c060207110d060c030f060f050409060209060f070201090608090615010509060f07020307 87
    0x104ad6656880b50004d501004100c020004000b1700400c442c42c01c3c624a018039111440d50305401c05000f810054030300c0e155a011a440c01310341441103000c1e200403a40704100800c000745a0118008502c1c03034624050159000715558039040401461a61002441070380a40c1c103640361510a00035984464104e003403814660180d21a2034852100020081c15030104219030780c820103008885036000c45c00e0a680c182c0c0f0380242c2041d01d000003a00c0035114946403400124502d800020355640302c1015485003080f501442e030380c17080a90301590702200c038140c40380c5d03810046840323900401c9a8a03204603400b00b03c202801d18010115980844284285810594100b01c1403c44c01d4883c1c042d648266000b10380c5c10040d0410300003074416049046e03040080094072484a07404000034005c0513200340c1e1500100b1340c0d100012502e803102903445a80640000c1e0215010502c148003c2c0803e0106040c001d09106040001807455007164103074010301d4000041c40700452a0501550000d0269014185840c46800b0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 89931808 1250 89930558 89930563
    0x20010309050c10030b18010e1305061801150e06040507140702241c0b030706080619151110020a050a08090106030f060b09090606060307030902010509132a02 69
    0x310b81c80ca01603c3c4541100400c10721a07001a4503560003d801c4502d504618000b00c1c0c51040300b44103c02060f0020008105000382d4840101003c40c0c11800400a6840740c5081c81010140a1040111590313a0040d900d80e88200709000d074014108580c16603054500751040c001503400c014a03036402c1043e000074102c0034515034400e485035590140d45180c2c9910307035075505e441c0940660454020040b0003107103040d82e15881b00f605c06500030b0000401e0080702004018560b4540d1640210400700c3c20380720008010307050500d0011465128044d003074010ba6512064041c450310809010f40025480030241c4000d4a810000e04007041d8003c1400c5240a95038400207045000d115105020030180b503012a8510b442500320b80b02030340c1c20542600045201d032500000501d01400000c0c040c10f54800002e00e885008102544164005000d152440e514103904600501411034107e040c050240904411900c2e111400604e6007289440020031074895415a144140790035020132150a00e046450b0009502 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 89933058 1250 89931808 89931823
    0x3060503010c111b01050705060112020a0909030507060b0301090c0b13290309030d05090a03030506010318110a031502071e120503060a09090629031e0f0a2001030905 73
    0xf40c103100c1d000351940e28012551b92186410203015441854008a540d00302c0020400d042ca1085400a29072a0359256032801e031542d03203001a0200c0e01c140a40c801003000c43d04a1541401c1c0140005403440055850820408064102050900d8045070b0520362051110022000e842d11445901015802041d4005654214000c0e051f0081c0c0101c007003500030030b041040e50380d039200301c10302840b00c4d14010440c5691245610001d50004e42841c021401c5940a40308806d070300c08101130b060780d2443e515182e4000d40c400100c0340c0c541105600d20000003184181c0701104000c101d400007d0780d030350f400b410420410803c0649803542801c4222b4403000050400c0c2c030003080c00e607513820403e441c1e035518400104d4141540e0b0000c01c20604000100b004c001850744040c01086c6a4000340c41c1000c401c0034400700180c0e40721461509a0300182c180045410300b03290048254000b102240c0c9442007200105040192072503003190212040440940200150a00c51420400a18007000755200580324113648401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 89934308 1250 89933058 89933083
    0x141312050109052415211002120103060c0e031509011506050c0d021f05060f060403230c01080103060e070801022a0706020c0105130e0703060503010c11 67
    0x2415141003110a4101030240c942080c10f0710302129215140f125485010701d012a59904440001100b0480d5040c600d20042e40103002074640450002200c41901801c0e011003841e03220308542130407241c80d50f00003403560203425901034010354550303e00303041074503100200d8806100c03440f0700c802c00f1520001090324004444c08001d40e01510780e44038003070040c000c4541007a202c440c404404100780f034004d0000c01b23940da0180304a440c8075400d00b008903103400881a04410901c7c10f442c0b401c096001d2030b00119001200108080f0444010b580041e50320b5016510482da50185028698904c40e01c40e90f41d8640340180c44060078441411400080010f001408018491a0740705030400c03500b881002401e02401340e03080219035405c039096403401000f0350950f690400b199894209416154045010011540207400404522407400019a00b0790040300c07500800c0500d911001680b4440621014096105a01d000a00c0c03030500042c10f09482c0040801d40600c04101180040d121000489461104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 89935558 1250 89934308 89934329
    0x905060f0d08070203010501090e061b0901030e01110c0c12010203040309050d0311060403020f070614040e0c0d2f07050c040203070507060608160806041203020a050403061b1413 78
    0x10751522400b01d02510310043d4141d864100081400c1c0001d9001d031902a0701d9004940346941e850794040c07a0150380054050180b0010300032034045500a03000071040060042c000700e08881c2030306041050307800010004480da4002c4d4400b19075420118100040445a40020340c034524198901400203003081c03044c0c50007080d04502c40700901d88a0b000c2401c6200c4403c1c2507c0d901d01706424000e545030402114882140030b440700024041e8010030840b1040340c445c012403400d00345805548074400c04018141810828100001700c0340c00c031540b007001d51079141c2c101070f120600b50340c101044a03440922200c1c4640201000b191f400b003070340012004929003048401503640d9480300000c94245c01a142e0060400d42442e10100d0100703400710300b02000d10641144000c4550799044000c3d81e852090710054003041484a160f0b50083c800d400a200412a42c01c0c0245403170b5407661a02c0444581100d4030035809100680071140e560301001909188444d0403c1742d04110b4900c1c035940710b0710b0141c410f00c0e4411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 89936808 1250 89935558 89935579
    0xc0a02071401090902030a05040606050307140f010219050d02060604020301050609090c1b071a071e050312010602030901030b120d0804020d120915021903230406020c0102070905060f 80
    0x141c3c401c88920b0702400c0c803180e040d0b40340d0904a00c1000500130558084507054200321000c50350741000190302e001c5990280c20703080016014020b1001900122043d5411409692103500031080040c03d5050000d120f0b400808a1181c5c500000b03003045000780c641e9209a0040004100aa56100590301c1800e0100e42c510b0300c80e01c6000040c0140d00c83e642a0007281a240e08071201c0904011400b003007122520302e03480a080308444d4494406201d640e800604107822091701402e85d0000c03002201c6090f2081041704d15003520740800074400c035001d03484400140d200041c02c55840d43d040c0540c00d1042c406940b40d080500180c900e030791b1a003103546015020489d415001505540e035a5140a1649420621400c00c0c1d82c0100c60040482843d40100203140810305445042c42d80300103001e4100c00c49100090440300b1081c1d4007141c2d20800f4088500e0040442048850a80d0180c4010401003003240c00a1455800c160000390030103180750310070b180c0580b07403104209007612080c106201002044032510b80380e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 89938058 1250 89936808 89936849
    0x31a1e011518080f0d0e04020a0903080705070503010f05160e100f050d09080406090e04050303040b090307020907030c0e040e0d030207081b011a04020c07140612040809090c0a0207 79
    0x100515a00c5414244100000313804540310101d0090060300392541c0e81284070303491409000507482840740c01c4000405110042012481c0d03100600055440f038410382b41403e903035000090070f46011015849006503600140103607812605001a40450141070018001c3e038924000740490b4176060049040c003000032962500240b080c82206e040c00f00d80b9508000c034104504000f10b59801502176440810031103130000c51650b201c1816075101d1790b8000010f510b0b564841e940c042d03039500d0141208200d488240014001039403510b05440c890101079800107002609084020920b4a5070206a8040c1e8949042d505810740c010488004c0c400c3d640c240507950701070a15110703000348070704414030726043d00d01019408050419000f1100d4100c0030b00000b2903040c90401000100d01c166107594101394443d2000300602c007007004003030004050040066003045000220100072500c1110106c83c2da000001d920f048624102c0f80e6290483e40d051100350411a075140080d642c0c900b5800ba02101002180420b01c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 89939308 1250 89938058 89938097
    0x23150109170304030b010611030f070602040314060f130f0b07020f0304090605010206070e1c030e040606030905120304031b020409080a020f0f0f100510031a1e0115 72
    0x4000d44030401c80804000004079407280c110b03000460b400040c0800014105125003440e440400b0188080c610701109042804d10701d5203c01412100303590280b0000000c9402080311a2800685d880605024075101c00710001400c002003407201c004001405801c04510111030310f4200079400030002d0034a0b124200264513042c00303d10302081500c800140410f0082158005000700c4100382c00f218003907140c00707a06a5011040b11707006900300c1c3d0410601043c10740c101d8061a9180c0c0241486032081c0312a00100d01a904ea50700b02001294a40f41c0030300030444108240030051300040c00d40c505500b400c3d0b8004240c0c1040c00c510f800100b40842c001c00a650b60f6611000000d5845843c80b41e035a02c001c64003070349400d036540d52075107079000b159500c2c82c80b201c004c544000b84400c5140505088012000324000074003016002c1c107204005960040300043d0600b074130301c0141408040d20407280c07529985460040000d05c4c40c1071510000302c401000007800d401800c83c0c9403007150a0240350315006408084 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 89940558 1250 89939308 89939327
    0x527040212041406070c02060a030b0f030706111207111215041a0901140601030c1b0501090b01150c020603150a0e0106121e151503050109231501 64
    0x20507440c03051004000203010b6200541d001c9400b9106240c3e035140c1c041e242030860850180d00207004001c2070380058440c1d4080c0400c000010706007008a203040300070a141c0030440c2c01403008a6a080050102082c08119030114040710032070451400004c0c0c1c1da0860301100340c546050054400d03c2c0c4654000b9001d01c03d204001484142044113840d103803c0010500341003106498045440d0b1012580703045040c064100c404003003540041158441100460040043c141030b40e007040181e101c29001007003801a40b844d010300410010441c3c0202c0c1c100f1f07021120041c0c1c04240703200c003580c11342c20300c0319001441c011304960112b81d61a2265200c23005401c002c100714002d0355010036150808200e60b101c404815060741d40d640c4d101c42c0914029980d090858080744c5112450140380c0142c4e81030300b01d03035130007810b0060b03084a00701c1407180e9036203055441e945503005410701080c0c44100500003141c0c1485564000c104100e0f17000b11600400e0500c844010010b03107030107a000d20403408010164081c10b25031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 89941808 1250 89940558 89940577
    0x40e09120f03010510020604020127080714100216061d0402030a0617010204061d041b02030304020411070b270a0516060e0117090115030609060b0105270402 69
    0x4035a00c600207075250341c00b41e2090061a110700700e40005440054800111280b1956040c0c480310212024034030301402c2860000084260a00b01c41c0700440c641109120500040c1524640d4140c03060140782040400400030301100b08651002111384003148a0860780c100310352950130409d500708060200f49848034030545190380c1043c0000103001504005a001104440f4101503824540c68208c4145080c3d1049206400000d40514800700c0681e44410101040c0c1030000c1c00000d0b260320b08504183c04070141e0b890340015800100030001507003418005e401071800c0081c81e9614040f050307a5200100c1e100a0018505100c1403040704e4002c840c007404030191007286000300d441c00e1200f85880ca50707882401c0c0144404014418002494074003c601ca1700014005844844208403000300c036050508000300741144564032518100b543d00311410480300998021800410400c10b01e05103082034515841000e13040100401101024080d03c124070050110b41c00c610790050000400049d0107401008000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 89943058 1250 89941808 89941843
    0x21218040e030915041404020912060106200109170c010609050108032a06040312060909080306010f02280c05040f0b030706030507080a0207060e070602060106090b090303040e09 78
    0x14180c0128004050803845008803000343d900501d040d02c103000c0340220b1082c06080c1806d0f0354600300a142c590040c200d20400a44400007040341072119900d4030f642a8403500214096a002c0c20f11283c4044211404281610090050a6980d5108500e640c1400018100b110005c9180301c1c0d524400e40004000348000d843c03e0001d940c5525004e0b46a0707000c031811092034500c9121030303450000e030f090400c90b031019480c01425495481d501c0554043c0b00c1e03c98208051640c800010036150b14038402c1071800707401815119180c1c90408000f40c10700701030103620019540814582000c034100310b607043d01481c0300c0017901c00d0101982c0c40c200c2c42900064104540c01400c050a501d8203844940c82079000300320840842d2360140d59007105030b01320360081d82c1c0140022010000030312040d100740c00801005110300d5002a281880355421814000d0a40120300142c0100004010140d0b1040c01b510180086011642c035008200002075540d00c2a4420141d0741c40c0e80000041a264003801440c3c2c2003181d0011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 89944308 1250 89943058 89943071
    0x30c18090b0102100912030203040c03060218040e010209240c0f01050610050c0d08040819080414010b060d090507050a06050a0207210b190f0509011b02121804 70
    0x600c880944580d200c09070052081c11000c03031820625010f80c400546c0c0002400f070341081c100f00700b180a5440104244c52005103500008000b502c0c40c8010903020482d44260f0000c4003085003048103981c0300601c2540c1e141e0061055456554072280d010064404000f402c1c44829a158a1414103002e0000c001d0020701403940001100c071419003080707104100c11202c0741d100000000e025a4540100c0481c101142d011400380c4540c50300600206030402d0080701054103000c004401d208140e0405081d04000417213401c02e010400a0b41050900c0403080f01000707220f6220607201082c4e2a01801e0311800207144c03030b2000c00062000c107000c5000a048090309400d001621014003500d19849a20b0040044c81001e0002501a00e0109020651001c00360040d01e003000703540b01c880511102405981c0400c030113000c61110a00c43d0310516130b4a1607000400716103450082005401c4551018410300c264000d802c003045e00e95030100e00c50b500603840945040d01c1d2040400484550820ba40209410a26019 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 89945558 1250 89944308 89944319
    0x51b190609080c061e0f0904090f02040501050901140402090402040e010b070c0b0a051602040f020d0e0106140603040b0901140f040b0901060302060d0b04021e0705060a1803030c18 79
    0x20380c00c1c0150b42120b01141c43c40320341c1605000e07052003004c0c8852449602000400c1c01d1030400801401c0708109480494140392845c0009812142e0301801117600401000700703d01141400d0140c0745c0186011a0006819031600006c030b600c8900814500c0c0c0701fa03500156004103a500c43e03054038060911540090819070311030f0503150300395101002c1034031040c000302000a24800324031300311001c00e1159640c2c2400c0074658a50b0159050810904030384c095103d084a4084001600c060244001a51408510000458400750031210070750001e1040d4018a00c100155817240e00480e90441d502c02c0034100e01c0d564140f456401040c650031000041b0b0309040900a020220728001c5000e94001e04040106444410480d0b0803968035120003500b01406024034416100550f101c4600c000c2d028202502d03002002d00c02010036020340b0400b1300e1807040415468140b041c00c000d030030303401b054807182000580c00542d072144005c2d01c0e0040050030161144803180409110350a4a10164801420700900f50b4842 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 89946808 1250 89945558 89945567
    0x10e0c10111006031a310605070306090b03070302030304170703080403050313060206070e042309010e060c03071706011412010801050c0f04030809011808030c0105010e04051b1906 79
    0x1840180e6815140041044800c0701648486001d80225425003e640004621001d1000701c00d10400140362403640c1c000007c2800b9000307003071003483c40e554000ba030903007086040002c43d090581d00c80c1c000d0b07000030001e10061700c0c0002110140c034840c0c10031203407e021400d80140b82500310340008045190104001040010001c00340030820100b94841c418540c030303000304a035a21400c031401d2001403900c41c1c00e60140e0900e0b52150200414580c3c5500510a00f05000f24803075005440f14802a075451061003c00b410a000300c83d040354005080d2851800c248400800c006403003050074408480d03a81c08203000381c3c05880601c2500312501c84c100e4440d501c03000300c0d04002400340300e01c0f1005c0d400c040005640401c01c1003100ca01c4e8001110b52401c16043d0740300d00340550880302031541402080340f8907900e040c0190f8181e0b00200707110300c011a55402860700030790a650042e0f00541d0341c0c5403c801800005003010071000c0241c164501c101100f40c0e07092001500c0b61040c0250131301500000c58010a0040c0d10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 89948058 1250 89946808 89946821
    0x807030509040b060c0d200a0b0103020a0602011b111903080901050a0203061003020c07080303090607091217071109090705010e090c0301120f0204150e09010e0c101110 74
    0x880c2c00b0094024078400b030240501c03070b9444205050f0000d4581c030600030b01407809400002d21078200300001500c00c0700c88500d06141c2207420740b13900c0540d9004008501e045e0858202504191000f80903601415484000e00d0f03505e00b0f513a00c03d00c07050601d010107c0300104000507540d141900311030000882403c0180c81a0ad060300c1c5142e4950800002034071024032030007100e000d08005416490042c1100360210002d40104100c0c25407401000400601000104061800b441c13080010384801c1c01e000d070001e00302e6035035a4000307050300304804008800f0507006e01d0800c0c2c4000c40ea01040e039a0b0080f624080e039400540032803c65000300b094042c402801070014001c0c00b900c0080c3c0702c1d824003100101c10030a10020071502040c90030f10400040c0b00456080120303816003485100c5180c2d90108a80c0090140c841701902000e43c401c8200d410800b80c0e0031120b01031b4000041c000200f00d21550404025125101c82c02107901480f404590108070034800d41c00344011040d0301058959010740e010003d170141c00d9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 89949308 1250 89948058 89948077
    0x70c151e0b031f0b040b06040305030c10050402030303061e0a030305090a09060b0f0703090e091606181703070203070902030703050f160e060d020309010509070909170706060308070305 81
    0x140c145159070078280054411402e07110990f00e007801c2e03107074184010041c04c4140d411a811580f41d1010340c4c40da03241c010103000618400c6000d941c03a143c0400c4060301d00300452555010280c100014030000da10080100e0b03030030400070f44050035010080e0180c1224400303040189504582040c0c80017091540c060058424a6400c4964000007035031035402c2d2007526101e0082002e0508104043d49480c1522001802c03424801e00342000f5079030b40d600d103035034100c1c50495051440d40c00411000011208000182000d44100d0901c1480100640440c4000700d5071402603423200c2035124014080400108180c1d51155030003812164484c1e100d08522001e074100b60390340710200c0d0a100c04200c80c04958265940b0a500d904541c4400354500c6104603000c1c5905041039400800420050409000c41d0000f544a0000400082901d0524644191400020751304c48800c880c42e00100d0000030b008407807280c16015100461546900450920704001d2201c1d038002400c103e00054100c0c109138101d0058000c420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 89950558 1250 89949308 89949311
    0xa0507020d0311011506051602011b11031606081504060b0c010e1e0a060b0402070605011d0f06011709120406020609060c070c0501031505030d03020d0f0207030206070c151e 76
    0x1055206107040c00003107401244c0207e8004d10445900b01c111415415250f4014901481b0703480c00801c40c400740810305107040e40d1500d440540d001480c1010440405143c41c00c001e02c2e0352031440c201c001401c04c0c0001e000c00380c28501c414204149035a45800c41805400c851442503600c0c602c281c1e6850086c440f42c500041a4010282016118141150700d105440c1c01000504010030f041e0341d401c002003812100950f80654240400c0d40840e04512400e40078103045010b55909110000a82144030002084070721403540c80030800c50303182d82c4051001000041c090480a450310f0754044241081c140d00e44ca154804030204000540503130009903540651a6002034030403e49440101000d203200307180c0044c10070b490081c0101b00c10352103980814249410381b016154015140d000080c28500ca520f484000240c0125065456800b54881c0c080080115041140f401075a660082d454284c02828001407203080480c0c081031002a00c1d0b40c10760f124642c0e404120009080002c00304540820319040c0189 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 89951808 1250 89950558 89950571
    0x3010c0e12060f131406010b040302010e0f150d06030506070e090f0403050a122301060201241502030f04080106030c060503100506030903090a0807050f09010308070303020a0507020d031101 83
    0x1010412038015400d12109088941e607900305041340c0200d680d0700b103c2541c80e100c0c1400d01d20703605011540c041e017004915141e030780c2d03d07500005000c84114141541301c8e800425803c4c01c170307039104001180c0141c0c1c0781120325100d050038017185c001012182d001030164002c1400b00a45c01d54000b0b02080ca042d0b04039001449900e44841007449035004560083c00b107002002000c11560140c2103030300702d00c0278422001c5404030202c161503c14000e0142d140c2207402c001e4006001c220307028002d00c0034000601042ca0000c00310381000b01034200c624407400d643ca03251106840d035035610a02c202d0b020358566154196845680c0c140441c000c0ca02031200f52042500000f0100b0518881c1c02240d0140c0e180c0d403c500d9802e0300b0321003001b581e5840076010b006640300802c10714200303483d083e9800000380076800185c0001072501080c41410103540045a11402c1c1080050001a01805c01d480e03c1503098540141c0b51412513400740c40510440350301a600040038805182010380c070a8030b55103154103a10003441034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 89953058 1250 89951808 89951839
    0x20c060408190c03171810050a06090902031902012a060b060702010e120304120302031209030906070609020103020d06090207120201061406130e1306060503120d0b0f03010c0e 77
    0x450310f9102d0000d002031141c00f19000d4950154030720607000051500e030080d0144d503102d005407070031000040344195142c0320300412001c103450b8400c00c8000d0440741410701c0303101110b81c0003031380303c02c02054400d60b83d003881003095055903c254802210140b0141241205030404064540100602a01203540720f06110341042142002030580d011550306840e0f6014250600080250009400c103502c3d9040c4004d0000180095940c1c50031a4100d0007034002d1039035501000107a40d09140c00420708070055000300000403c80e02ca500840303a800c0e810400c00030752807142c0c0c40120064468227400e078030510b08000700030419100f50790080ca0018030403a0800540b5a54100507800e03551548114414181950614a4a420300b00010198510001f00c0412a152124201c1c0111101503680100200c209078506040000522840002cae0104900401c03400f004016031a580d4440e030032515581c1078881e9892103060f00c03440159081500000c00070700c00034000d640028040144440340ca4412001c2106541c0e2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 89954308 1250 89953058 89953067
    0x9140a032c0d0609020d02031b01090b0c06010605280509100c0503030604021c06060305071b0b01141210150e1605030601110d0801230f0f010201020c06040819 70
    0x41c9140301800a500c0a001ea0b1241002001c007440240d80002054891320700607901440075413119454a80c0303d010170718050340010040d6109400c031041403942002031000c00200001c18504455403441c00f2070381ea0301c01c8040204c07581162840c442d849500340302400b0b04250404c01820f43e05030f00ba0382d0505074044505080710040b078024009805034200304040f0300c1d1400c040d001403102c00071000603c0c1c00100c205c41c49500f100c441e03a0140001a6903502407000e91079010f00700e001c00640246942d00c2d080c40f079480700e0318241418400d604d8015104070649103240c4030b01468a0388107881c0c0c0c00795010f54201c0300740440500b01c0c1d80c150b8150544e0283c2c01060400c08141034034001e0740d0307070350f08410111000300d42039400e0b42c4050141814014004009440348408002c401155051030b51000502d51601640702c10074080200c4500c0ba420500d18000301d96111582030f0518118200c07180c1c50401c601d100140e00a10884442c10003e0007010304100c01d000c0c002000300000344808003400307920350108100300d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 89955558 1250 89954308 89954387
    0x406020a03030c0e0d0b0c040b030a0203090708120d0902010e090405160503150f1b030403120b040902030a11221a060c03040902030a0b060408150f010f050409140a03 73
    0x16804140120214081002003032607d6008800c40460303803a164030707000d040e84960011268240c170303250004200100031b1f609000f5903006100d0f01005014201454440c0e010a002e05858100f0407640d65650009580c8120841c00880b00050400c5600d4282400c0c010f444502e000039542c103001c00c1007400102803d00181c94440070020080d540b00503240d89500101203400030303010420190854015040c0381c42480300a50055100c1d4032011045030080c1d15044c1a201d858110b00c2c400e515044200c009601e000c11022655540010080c0c03140a9210000e80c4148003c58980e1034142125000d440b00ca15030303400000d48000341e03046d688050342c03da01000558861145080c0d0590070074841000440c080350051500a00130b06404140d90f1115404108c298110350300002050748001c080c071900e2076a030252a6000124004070750000e41c18550f0000918400b4400c3e00d000769541c450340014001901201548068514103888a5410381d0a000700b6103842d50401a240301130200010941880d0603801d078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 89956808 1250 89955558 89955587
    0xb040602120c0319050a0b03030408060702070f030b070e01030f0606230703090e154203010611010207020306070e10030e2a19210807020607050f030406020a03030c 72
    0x280100c1c19000340360001c0c0401501106c4020388a640d9200103650a00251001c1c100420042c1090300e88010020716040c0e00d03a001d01e001e1010010f0138004200c0c000f940d11781c405e80c1d506100c0c58213060000124000d2441c007002c1c00f2a2031a15102007000caa20540240c440c4408850107000c0149003203444035140714009009020490511041082c00115040c1c0341d400319002c03840c0004985410040740d0918000140c02d02c079601c4410310300d0031900c90405180401000c1c507081d40545615904030317180d240b2060051900303100d40c401c08488011303000d404507005039a020f4240c46140c109008040c09003004c08045500c074442114a80820364824481c150030344030000c005000c6018207507031710b00c2d01c0e8104802d1101e114030700d0f40c007281031511b0340f0005400414024a050240c2480c00b003201c0690020155000d003007040400c5c80c1c801003241c07003050350549074044960319901c1c00b0510300b292601101c00902d030520300000c140040c005401054600446009490034061340328807180441e0480194850f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 89958058 1250 89956808 89956831
    0xf0a0b0f0d0f0f0c03031205010803070201080f150307090b01030507110a0b100306140108010b06040b040b03100e070503040b06040c020d0f021e0a0203100506130902040204030b040602120c03 84
    0x2484080340340b00708001200c40c0a4040b50f01c1811a603190150300d4031a540058000c076611000380d001c400d906200c0c0500601004000e1400c15120358002801c10304081c203000604159a00406c205002610030401c85aa000382180c069603501c1400030040d0169426043c08240341400103a1b00e103000d010000d00e0710003044094914070601ba50383e14001c1c2409070080c500c10000344004000941c10748203011710510a0303c0d000b0055032511400301e0941d14056201070140009110420410b43d0000554050300c1242034000d85a55450003445040d4075070340c0c800807400c1590702c2403180711904000218050790007401340111540c2e8203402d00090769082d041c60001a0301c0304002c440002d01c079911040c83d080e180c1c4140c0c2d1075041000800c1803a120b100030398100540040c3d42d048110700d010482c09548055a000620152030312100145201501551041445807183c0e0404115580c5904540140d0b91220600c7e840d4109410040000d401a000c900400d103c0d45020600020503d0241c91265424015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 89959308 1250 89958058 89958079
    0x10e060f0d0f0305070b1305060604021911030d020f04090f020403020609090901060905011502010e0111033103090e06010e060a030b0f0d0807051b0f04020306010e04050f0a0b0f 78
    0x19202002d08000e40709030f042090078030402d8001016122114000c100e0b0038000520081141011400d107200a0001ca00c00c0d4070402c03182d8112032407880550080807090501840780b400100c20642180704401d40314284030310008021b1501c00c41c2c10058130641d110f81204000880c80c104540b42244524003010358090005d0100f41c81a28042800907440850320303002081e815600c90030002500c0c1d080c1c20551014a031140507107880f513424400d543c9000c882c10001e02c540c5050aa040c08079100181c0a4114495402c06022030303492641e0384440861a4071444440003100e2f81001440318001e4016104083c1000d030100c1c007150700c00d18803070b0414540141040d2619050b21810b500400c0c0c00d2044a80100030040c42000543e13079804580d0485004200e4207603241140d1425078100510551907841c1c0029110802e5010382750205001c0040e1429680142d40c3c1d2100e10058407100c0e6100007850740142010104900d903540e0100c0c4070302640d40c1c01400d114000038041000450000702c0c00e080d821130b51000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 89960558 1250 89959308 89959313
    0x711071413020d0c020102030603010c0305040b0411180a051803090a0506130509130b01060804030203030109200c0109110d020616031403070f180e0403140f12010e060f0d 75
    0x210300204410012800600c3d00c81e000007003400342c4070b90380c1c0d600300913035400b1040040303a040a00890061540c00d160800c06403405603074169000ca0f014101500300085030317110755860340715042043d1030120a0102800189014440382000d08012030705000b9604400700c82a026000010543c1e803040c8000381a0b441090419050202c80d401842034050b842c41c504030700040c3c030307129415041d000d02840c801203100c20b00581042c005542041c0d22040c00c00801900700004a40e0110a0b43d06550028030b0101c3c00c080b01c94070710240c1c4541003034a12100f003800586403501040560000680900c0341c0b605280c1d21843c031081180d0134441c0714010390030403420442c00c1e06200f410301407188100c0c86424060710074841d4900586054104650940100b6101d0715403224194102049942e03c002c0d042300c2030116418100300310721f40c002c00fa000505112100b900c00b0030080d000c90139101c4d61100b440009803542030704451050100300a10500b0039000b481c101048050400680780c1d40700c2039018156800350000c55 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 89961808 1250 89960558 89960569
    0xb0402010e0d051e030412080d050f040309090506010c02101709070f030f05030409140f0a020403030e0d14060709030303050903090607021311030a020301031211070911070b0406020307110714 84
    0x2107606a0030b01041001046c441880c014009015000706c828540f034030f40d6649c4990480310041c0803400c203a4010420040020fa2003407200c4283c882002006c299600d0703d100603181c4084600000b90702420038100340082583c04052a074401110040c6401c0e59110810001e451b0061400b8041000d030741a01e00b40f02180c501d8002070a079521a108803072610396070341d01507800c64101d511140d5440c00800144808010a03032115904902c00c84000c41c80d0510b160340151440c0c0090a0703a03406000c40c800814288423100000c1441d00e103081095500900e441903005204204500003180407901d40004664401e40c004151344d40c0010140c4281c1c90680b0a40810149500c21085110100d480b0b81112014201e0341c0e025500a448114016841e541585012100001e50b40c86590800c48254000c402c000c0c0000b170210212881700c1000214851342c3c5910310002e114000c030140c031303410182d0141300c20424141d008500c51140d0340c1e240c0c44a0000c04481507141e40e601e06c600c80209500628903070706841d04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 89963058 1250 89961808 89961853
    0x90114030c0a080d0c241508030a020d031a04050a05180a0209040f080c0a080d0501050105031003020415081b0411030c040b03060d1506060f0c081e070c030b0402010e0d05 75
    0x80b0b80d60803031100c1480e124001d440310107041b01c44058440b0f541040e44041003014801030040e48010794188141c4d00802961b8407402d03062031081546030210030002e800410303000081c01801601c2400302d07242c0100c0ca4006030105035182e0300c00003e041151082c41e0300c00300e610b0742c0140c0c1c010102852030f129030704d41035800005804262443c0c2c07401c0010840e6080204010000144180e8000780c44030341c050721040840700140e0119050100400401100220306800041070701c1d4100d0b0002000e030140154402c200d16a0b80003802c0c1e030322480925080c5c0b00f4100341e0b91900c1860865040c0500e10050000040038001503030305840800090000340454034940000d59400b1101038403903e07420714191500801c1c2ca28500c2c1c0c0c2e411060382c1d041c050007060f6210b00d0480c6c0e00201c9003049203843e080d42d502d0305503900c280007221410640c0a128101030031100ca040b0348a2580080c045000c00c0d1301d030f041900710540d00f62030407800300782989a4000321b428030443d00d03850756030800040c02c0f8a8604146a4014401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 89964308 1250 89963058 89963063
    0x915060501081506120708010302130b030a0f0510020a05120106030c050d0b01170c030708071107030f05010b0a2309041a061f0201020a2d0c060b090114030c0a080d0c 73
    0x1001d1082d40d0045503045170080c03213810300b559145129451801404140000700a1440244e420101c1d109041c1e20700144145103540e001a02c0c11503203955080090612030707443c3c582089140009400c0d000c0b1307940b0001030541400348501f22400c5907601c1000340c044808000d446004103c0c207000341c124008132035100f43d036102d106040c40210310b1046d8400540920017159000c1e02c0300d40201c02d212181d0741c03020304c41c0c3d4040401c0c24295000c5860244e10ba5071044144002000388000303040801c01c000c000e400c0718003460703005003104071042d45400c40500c1d0030700c1c1444890310008950610440c9403410307541d685e02482d000503496085a00269140c54615401020503800207c0d8481a4241001204100d0f059601541c001030301ca040d184070041411500c84000b86400024bc0310b40c02e2481e2403150300045401c41e07424031a0102105103010005800201c1010f03500030794034030000903500d07415442500040001c809440c00c940380d400400100c40400c0c081c2c09003903403240000081c9980207407003061030b1741d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 89965558 1250 89964308 89964319
    0xf060405060c07110901060f0305071809150533030403210e120d0612080f03180307030504061403041101031137050a0e04020913050a09150605010815 66
    0xc850100303403041c03407e0380080d00094882c0480344000340d040c03044a400441f07900d44014101d450780d402500d03c400900a0102c059540d01002040128250005004020103061101030400c111080021603c049010319100c58490095540c40311254007102e02c90b80c0d2613140c0490501452a0001070034150051550016540d040441e030040b00c20800c0c0b001d4001c8210f82160713140e41782d0703820368241e030740552180365000c602d200c140d03001400c01000d0b140300c00c1c00840882d88a6450f1741c001000c1301d420b0000e010071404005844428140d20000410548451f40c03a8045018004030040c0d805110496000e082c003d903a00c0c90314030a41c800d0304604844d00d0035017101410210700070b42110152039914000300444010024040354500c662400443c02d00160405a050892650024041c86a00010315204a500183d0b150742940c0e203600b00f2005101c00003081041c0e15121080720000c1c955107205856075240a0344400b06a4024040d041c16158180c0d64000c46448541070041e00f00301c90350f0041d07400b0307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 89966808 1250 89965558 89965583
    0x1081f0e060f0610020106031e0c030b1609170307031211040b04090e03090303161a09010e010605041a01080c04090213030b0601080f010b0a0201110c010b01020f060405060c07 77
    0x145810480503015048100c40c01d20b00d820301500700503c20461003c90410f40e414628104045444840b12000c9c442c2e200b02a050442c242e403403d4241100c46420091081e85251b050013069101c0c1a2008210300403038861403895030311101d490110f1350046078003030695801000384a00082c0304104410400c07010010100300a150320f400c501454000c0e4200314030800e80800c04000b8060700e03001c4d11026803140c401640c5003c016401190f1280715096900512401030303820901017240140c01448207500340c3c200e02d00c00c1c0c2801803003d80a0700c0c1c640b4409440350b00b08140456180303014030905026071f000c02c0c82150001403000041d908044001d0203030010a800380400a070260090008290703c1042516020b40141180703444580304070040c5c0070b2030400100000700040340c0d000401e410306480440e240240c4a00d00c0500072401341c41d4400b00158450000308000807045070540001084010907001e5400312800010f24a0351000c0841e0003034001c3d030101e00131490f04080700004191143c007800049003103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 89968058 1250 89966808 89966831
    0x209060d05011d01020913020702090402150c0a03030504021f0f0f14040b0903160b03060d0f1a06030723011b0f08070201090506070c0e0601180f050a080601081f 71
    0x80c40d1442c0f10b80e03000e03500001d94144510304107421280c58417070b4000460501c2c51301e4001c10309800000300000d008034114008401820001070a482c40350350810220380c495071547c0b5008000d400c064804a00800040a02d8514050000e2000031030b003995aa075080d40036140b1b101164980071510741e09081c45204192405910b5002c0c008101400b105282c00d41d8460701c00d41030510b01010500300d04441c14580d0402e0003909046d4040740d070132040441d070183d4060554105601c1c800182c000003030180c4030b900000c541d854035240f4424460002203041c1c0e100c0c41d90795214140380881414000c3c0095400b0001d0b20312540c0210f24400c031740360102204c046011002e66a92000030318035081500c2000d0089900700840d0b80c4111000301520b402d031001810032210b90f4540704143c40b103004049601c00300c0800903203207034480c41140690240b00092400d2003136440c9020764680c0740c5402024010f031101100450050800900702c1e04130b950a0b4020500c511035030001e241c51022030200301c0c203004e48803030a180f40c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 89969308 1250 89968058 89968091
    0x100f0c1e0f14060610050901050a050d090609030f0302070804051e060d0509071517060f0d0605060306060a050a0e0a091205030a0e1207080309030904060312020d020a0209060d0501 79
    0x1d503140304040300040c008000e00000e00c0e00e00010125441441010b0174000b0700c3d90310100742ca85200007801e20070f0b261003410005443c0381c080c4513060a0100c0c036000d10345061014a40102c02c50354020b44513514801e400d06022000e910a118028000000400c0108054103056040c03503181c00c5242040c400414400740010660350040f14040001c903222000d03c08500c0062201c2c1004041c0070324054090002000041d001e00d9052070f89004c2440d103840020541d0700e0303040c0c403442d810400600420000d0b030b03249040001884261000340c02441007200140250805107040c0f030980700c006201c2e000709450320040303c8040000420302c0c69681c0d01da42a0f02c1c0040c4c5901070b48d0109a10740e0300d8981d1a071400c003a641c3e08440002900c41210b60001c0c00c04100300041d08100c1c1c00890b049010541d41c1c1e42c8540104d4030f140f059442e11600b1501d06403001043c407082c5404a95040029400c2e5490302c017030072504036030350000c04802a5100b582c030404540f03145860780944039110700c202e0000c83d000340e0708140f402 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 89970558 1250 89969308 89969333
    0xb07081b0105040f03090f030209010b0c070503010e030406030b04050105031e1f0b011209170c010e06010f0611031201090504060f0905030310090203010806040602130902030114100f0c1e 82
    0x4070f900c2e818440032800c05130041b454601030031003102d1000020740740d40c0000d099080b040c4603841ca00000000c9040d1154070600040d0084c4c840503000f44108800d002d00696a03520074410400003a1406041c3d09161400d405214101d480040061003c01140d0407543c80501901808255900c0b038100100d01140c400303010201200c21384000080c2101d103460014207100d4013105c00035201c80c42c0030000800101c2d003403502800c00b00d0303012605480b0124444490300401c40000c2440f2503100710740000600300c1510720220195016540c0b41200c9204004038603549008100706400058441001401001004e500041e40f0500415011492040d1406d80340c007115034030442520190400030030401141d00242c6201c00074003041a0031072840d80740241017615400040c200800c2250001000c0b003040302811050000750034a14800c650360350f03543e0500091840d4a056641c01035030744840d1340030400c0c000c1000c04c3d49a1110b0b140c0c0420104035903a00056a5890301001030070301c0b108010000420010113050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 89971808 1250 89970558 89970563
    0xd0b01030b01060e060307021e07050a1503060611060403030510031a0103050f0a0b0c0d02040f0b040302100305130f080d020406121803050406110c090901091109010b07081b010504 79
    0x1c0107950418200070325118401503020700a400400c240140e861f40040c40b000400c1c01780c1a0030849a440c0c1441c2418401503070300456000603100000b05144603007091440c0c169a090714100a507980e50745050f1015191004c01c1000b5402100003d00030030f0003074200c01e501220b100822030ba82600c0345d4440701c1342085d8149440b5000d50140041c410000100403400c51201e91900510203060710f55140810100020140c03211420003244490b19030a190b010b4070041c140e94000c54000035165203100501c1d410030710059200d1802d600002c1c0f8000d000c0d100312801002d54019101785002a62960440842011400c5070241c1041144c0711404090f0b201400192815640342c46680540d5507451007529420700910300803020003801d1400294101084608550aa041c000b0300c100588106a00f401d012011250b0401c0d4864100a2420010b5011540f042c0c4a120340300c03034451007081404500c83c424050007491110801c440004100c443e009021401110021002c076103011840107401e6a4003a40c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 89973058 1250 89971808 89971823
    0x193519030f0903020c0f0108060d11060f041203080703091109130206030115090503011b12060503070308030403030c08010f0504020714030a090e0108010b0f0603130f03050c100207050705010e0d0b0103 88
    0x3042c89506e000c1c0c5401d10000d000b407030310213843c0c282440011910112124010182289440f08e8800c42d03c0d002d0545d03000300107010010752036640d521000d01d4410041141140090400c00014070414000d1084100c00e54010966003203510701201400841440908019107010f51071100000680d507003c01980a400261000c0d8221681058080d02080d0b132500180d102c3c0e4101541c031204c1460b200d0403035a940318503107040d2010b144840b0411000700f0650300510b0705400760a1011040c4420900110b0096102740d6082014110101084800d00c6081c020180b81e82d5909000300070910301600500625401210300d10034a10407010401d1455010a40c0c400210b100c40c24108000d0303074918460743c0145800302c0248140d101200001c1c000003405004148100808404034141e04045000c02d82041e40c003401c2d1011440c000e081c043d01d980c201a000c002c09103c0c0c0038408498003074500030b0754441903010004102090802c00159151424040c403250070040b0342c940b02c0b01049079104294000c6004180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 89974308 1250 89973058 89973073
    0x20a050f01150807050d0209101a041a12060112270c0b0c030f03041401090b0f100602060a0e031210030b07030209090f0603193519030f090302 63
    0x29034151404a5000250f107410036031080145460b5603016003e220b504075650602592030506c03800340c28869810204810801807420320b26603113040010301c1600c0654017524400402c261041106100b125102590280c160000c64540d5000d98403440984900030008143c0b02003101108100484503c420300c140f02c010340710b2105000c03211030383d84058004450030701d2420182c0007a01d03540c0d2265590152207000300000040078004004500040108548028402d01d0040d041528107030000380c0d10b2000e41181a030204000c2200d40c0341c00303000c03901260042d242e01e982d40c10380d003001410046000f844600040007250401c011060280b44180c8030100308940440c00d5050088003210002e001c20300781481003280f204075950b5202c445900c00500710300d113119030b40ea034400b207402c080003c40c1340c1594181b540130700000c1020024111440f003540081d1444048400a08840c50003800070188004d600300300b143c0700591151440200c9020710900340031444041d6001224115a04040140c0058000c200c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 89975558 1250 89974308 89974331
    0xc0310061401020601150806011e020109020f041802010804020607021c0303110a09031112030d06081513080d06030203101e0504050706050a0909141006020d0206040b07020a050f01 79
    0x194104001d41080c8010105581000c003994101e48000d00740b0424030146038000b450980c440d41440c007551412989105102002031006406052480b00482c410000552450410b0401e0720625944518082c80a20504d00d00d400554500b02c01070002d03a00a101005900050380700d00c548003400100503800038540940c181402400c0b6145848002c0c40300404200c61030f002d55002c035840c800d82c1c2d0491a41d00303501d070742040010a081c1070351440d400d0900010603101c40c003c0d100e9110001b2500020b040e0b03182c1001c1007490421b005000c030340c020b07404401540104081175082001c1d0000070300801d000a403841e12500040c0c035010703031035419040e01511180d0903041928103809061141e003031003605101904080c1d4130240c030303405140507040c10001d0220300d07511050720888118009100412007042091100102041840422140b410680c2d0400800060303070361001800460342d420581c0030703050b01e40300e95466002042028005004511411001c3ca01041b8240800c180800b0442d0001881880c0e20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 89976808 1250 89975558 89975579
    0x1009030f0b01061214060603072d0201060611030a050f0c0a06050402120d0c0305030c0409021303022b0f020f040509010603020109080a051005060d0503040b03010302090f0112030f020c031006 84
    0x24103c04d0505030819000341d00c00d603610001e05400000c221001516541c40300000c40f8003119407101c1c103031005071818200c0840004540d600b891582241e000b40602a26840196001500701e90580490b50041102003c0284504040d2507100000301c1c0d80e51a07c840b1040c00c602d031600100059903600d80e180180b01c03c616107101004c4a03203031604c000c1d0188504406028020941c14000034091020000008418a01c408101c50217881c0c20b441c219194200302d4420030300a490390100303e0141d0140c910030018105081313a100c00c1c201407a03210b08100c0c080c540c0ca5000e52100d03614201d03040488102d007443c0c10766650040504c60103201000055061450000400c19441c561003480303141c00044401c00402c1022a00d56405040f40d0070214140d114840850442244800007610700e020102d00464105ca611008604807402252011030940318180d204080440c06c1c82441042d800340800c18001901840e4603800d44409801a40c0c001c401e0700010a08003840f018540b5100c40d6208010722203202078 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 89978058 1250 89976808 89976827
    0xb03040b011805090d0f020f010c1e0503190b0d0f080310091e090c0b12040c0807060c030305060a030b010f0504050c070305160819050c061302010e1009030f0b0106 72
    0x920b5000d0140742444210180c0780c4008500c100c04020380d0401c0340400b41e000b0045007846051460081141c2c0c0c0942800074080706580c0b0714804069100c45141070502d1103074007528028580c0c81403460041e04c2d0405140000c02d00480d00503017051b401000c8201291000340107950036401354200076502d287c0a0700160291007180c00580c402072030b140d407684c1600740b914002ca00c682103600b00000c2402545c00c0070302c40c420b041c0d030000d04000302c00150640c03040c0c6882c45144c019881081d0042c2496280c0c2030f45615420300340a00c0c00040c0c040200040403a10a820903500020b01414490030705841e5240d005440d10b090b040100f0246400000f00325170706042c82441c0c0e2015085401c00d040040c141e40c010428403032814803074103400340c58000388180032040d411a0201d1801d030a07120030301140040041c001e038019241426030340c00b805c000a10040c00c1c8400e0080d80581c141d54a80015406204011900b07680311045420441555400300008a0007442c0b010480c0c040d09201c40c4961600300c005155484 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 89979308 1250 89978058 89978099
    0x3050f070b0904020919060302090916020d0c03051606021801020601050f121207150506010f0207060f0201020c0708011a120304050402090f03030307030504021f0503010902090a0b03040b01 83
    0x5000401ca03070000002554003428007128050781c0c90741004001074070b40c4085600c0152600c1840c500080c0103415500600b18400305030344062641e0b91b00d04442c9c090002c580e0801025070482c0980098680c400c2c00101c451a109041060800e0600c0e0566001551072000456950f64006403280c0d410081e1140059255424402072043c2d48c1008007240c08482810203450207008004142c102c2c4800c103000c41e140e140200307144152140400d0400031407040d02c18400e04560791400f00400e019511440b250307001199150020010356140110440e05d10380e07a000300c030702155828000341400d09824455038005040b140008a02284a51070000043c0700c1000810700c180b0940040700045400801a10111a4220340040e04e035800c03040400c849a0702e003018264540400001c00000603016842180035500948000041409059460f030704094426101804284103000400c000e454940040c81900d4024181656983d581ca40cad51010b9002a90101c54180c03030100144086640b00c41d44009056 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 89980558 1250 89979308 89979313
    0x608030a0203041208070210030f0f0207020607020f040b12010e10051603021e03090d08090c03031e07020402040303170901090c0510090509090c15030115050717040f03050f 76
    0x284203010103036491241d803189040f10540e400d202c03020310000c0c4040d913035101c0c0c000e44100ea200c03c0300c0c4001070090900c1d0f219100902e02d804c1c0d03442200300e51442035541c20b950191601e0314100060b001c004480c0b01601d46181e0083e03d80d105014151106040340012072480c20001c52100b690409090511016500b1124503d00d00740c1003241000d11524000c40300d00c130906005a0b41e61950450074031555200c0c400e0a080900002401001000090664078203c07813a5140e40503a1241c11403240c407800b403080d00d035a06503c244240322000524403100150100701d411220f02d800100e501040903a001171344107902181c00c00a04030b42c55a80410301682c01030a10008110182c1c541ea900c074422021382c00340c64050745501804911641c0a6010000580f5000f00300d09610714042e0398459483d051840464040c5138642d140482d0354034a20242e0b4140c4101c00401054051285422149500310150a031a42600a03090652001320100140017412003038154481e03640c114201203217000142c10340182030f517 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 89981808 1250 89980558 89980567
    0xc06180302060c0304060605030706050c10060f05060c0c040515030d0504080304031e060e21031009020f0d05070e01080105030d02300c070512060912070c0801050f0109060803 77
    0x7940480c0d10b5a024000100c440c0d00c85d116401e1520041005420040e090b04c0f407600d0100c0d02a400034040e044c209841d80445032415030100c00503040d54a1032099001e11201e8002c18040d0f450a03074090880c0881044c1101c1c0d8503002b440c00101030300c03005d688016000c11031070700c101650f0a09200c880860300140c04c05618180c540a030345ca030349220b1484060074040380c0100c0308e01d58400c88040c1c1104250880c5080c400f8005c0c884495444034003180c2044042101803991040102c2c3c0441901d2040022042518503207251051000281d4095602c3c1348400d48100a4041c140460703105483c020105540c80c9562129000000750051006070002440395010495030168190f00140501c070145000c8102d08040550041c103603c00c0b1698002c5020a010121712403049610000d9020200c45e4102c81c94180364100800890f03d0300c10681302d4040c41c0e0004560707036150280346802000e145110395900070403540c0c0d405400382121010394920f501070b0b00c4007004203c4400280a03920141040c10065480c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 89983058 1250 89981808 89981813
    0x312030103050a0f031110051027050601030213080106051302070816021c08030f07050a0921080f0903120a0e240307080103030207120c0306091b060c0618 68
    0x320316507400c004144085250390072003014406c002c1040ba04501c80220340d0441d030175444032030150000b110100700911606100043c03021441185120014880c00007001c401e401816250241100609040c1416005c000400c04001031081100040c5108000010194102006c10044841d401c41d200c42d514014003216010400c45400c4440d8580b2441144070907036240e1010a24010070300001d0704103070410a28a03414800c1070303c000d41c860024a50420354503030751142c0550f080e00600501c0c3c800983d4140060020682c44034410309003042c1042e0444020b001c07561282c030a58040296403407051404144a89a0304003005031035191912049601d060081224005002051195a4071f12440e841c40400c2c05282156080d040c4111450b5051640ca280240010301000000e2000b10018880d48070000781d5221004400031b11580d024291612161841d119200904111b0302c0580f0091000c84030b2421815015040c40004c2070a0b407a000600c89143c100300c81101c01104190486400b140f001400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 89984308 1250 89983058 89983063
    0x30306010503010b0a1e0504030302060f070801210503071a060a080606040c030b042d0507090e07030e0f0d110118080c030705070e060907031b050a050d02070c05031203010305 77
    0x10b5034064400b072522034285c240c00f210548120408542107403807441000c412994003000074800ea80c001c3d02110400d441e085002c0a000c48100c0314140010500300051004031140c0d4150002400d4070f208404020580f40c4640303080d6804600c003141e0005c4000991900c054800d119164010401c80303030500d400d490103c98546072400181054412542c800f900c1004900079800718100203002b803c100928191161507420440d900390300d1014801d100c200707070114900e050052521a0b485940c1f42008640390528071401d8841c045d1000061544681402100a5003004008a1407512030010140152076003c040c2c10050300da10b401505905068843d10310410400901e0b00142d0f210803500d54072100b0201e014150700424030010000d0003001740004120201d4116280180f1013101d030b2888984900109500b203074008130101000b0001807507081000390148015041d0507800d800c1251400d2224203140c0220f03442032504858001503100180030b182800c00c400c00241030200c1c0020324550640e2501c1750f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 89985558 1250 89984308 89984311
    0x3020a06020c10020d0203011406030403020312041a09072408060609041103041103010b040c0e10030f02041214010b01080a1109090412030f061a07112701050102030306010503 77
    0x424980d00040e4022214000700403108000c243c0120854a6001915501001c4c0d8001c0c410f0800502d1101b0b00f0240314501401102d0040d541a00114035007124844440141c80f0020016180d01101c11001c00301c80c180f1110700d070311032041c1c107000c1d083c401e042500c1040d00c040c114080c180588407071720f480d2081e242c1164241d81c000318119062510b811540000901402c1401d000c010302d150301105200030405014018040358074102c00034056051820b09000c2102c00f0244518000740b100808010780c1e007000c40503818020020f24011940012a400400c160303840382c0e200c40e231310010761050311041c05440e1104070b0340c51700007200a200980180340000c28407400a0091b8400a41d91000d10795440741c50340448400210140c2444103e00e0a802e0014042d425800b1041c0820300741010300d0002c0982d88903010a03a00301d502c0614150852001008482c1c029142c229180c441d048000d02c401c0d0b48a44025600b040e03129813451001380f44550460500c070b0182d200c24199801403003401034a0f0b81060540707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 89986808 1250 89985558 89985563
    0x30c030f03091207030207081902090a0c030b04020a170f010308030f0c13090501031103010e030a05160b090708160807120206070609150b01091404240605180d03020a 73
    0x554507902c504140505040705407a001c1d990000000e070242c20141c020a21a00311000c4500b9114458505260041464a2201300941c429929800100321025551022200860300c0c03500050a80b04003011604a0340f0482440004c01c4030106600400141c000c44a07500102c2c40e0009070003545555642e00e000c1c040505007a940d020b91600060043c140081070710342020408101a8031642d5a02141004102c03e00060b1101034589400400d503003014050240780807020001940b074040189400c603995000005ca000141d904461101c000c550030f005007034003920040e4050003143d49401c050b24901072000400d855820800e0908005440c07004c510001182c612985100e510844d51000811a1040040007080985040100c034140540d101078120354140c6c40e0301c1001107090810064941d952540f20b0300301d00f202103003040c03500790400350032801c0c5035201c454240e003091000014a00c0412602c0c0c0220001070004100e20343c1e000051001c0c1542114141c0d10b00509822948000b0b440d81c0081101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 89988058 1250 89986808 89986837
    0x30402090c070506240102030a0f030b040f0501150e011d1302070b13061a061602041b020c031c0507032d0c0204050a020f120a02040302040c030209030f030c03 70
    0x1180c400700d010880c0c01040e44801500c60605d03254400140c0e150342106440340c510201107081d9015400007080362030303140c8907880f02c443d0654140000c40150504207003182d0082d840d080920f09410766800b40764042d201940c01d640b04104416001442d10325907003040c60410490b001080004445007428801c071903001d5a4400d000d0400015140c043c0c0f06140004040100380c1d000c00004481e08001c06000d18072410080c00f414850f104243c5502c1d1440caa410340c000410000414220400218400321510152000c40c139140480074100ea59000c05100c1d070051b80081c0ba000d6158602800100030880304417050034800203000d08000c0c400d0041c60b00c020148620112424040d001e5050a0700300320501c42040071010b481c080b0024449164184228007503410103002c140192013500a540c121030410103058200001c000d4003450441014003003401c0103508010110240c1c440d80281402582542c6000d60b40e0321100040c507280414130f818005150300148003440880344017000b100c803c1d20b0207454 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 89989308 1250 89988058 89988061
    0x40e0411011701030f0c0f06050901030b03070905280216020103020307030905010509030d0e0f060601050d0609110711011d0f0109080712031b080901030203090109020d050313061403040209 83
    0x507101040024103070140034242c50000420007050010302c8032a24411602200a5503075034000038035450b074074003446010400902a20500d94482c1e070003022340641c001e040b26a10ba907944046411140296000420b00c060440d03501c0b1160010714078400c1480031031004624258900702850808c1c080840e00a04041d000404204003500c00e4102e40075540d00f1100800050030100f5526603243c1c400b602c0241758a08206104560042c003088400305444000301622050380c03401c00456899104501e940d003940d03964800483c204106200e51902d140c41800b484d030350384041d0b05004445410104030070313041100c6a03080c115000100d019150140605540b041400c11402c801a01c1c0810140c00c08401d91244100c006004070000d000f8095840c06a00d489101810032030308080c1180c87c1741c2e40501001410000c94410f54820303030096605c040e0840c00096041d10743da00048080074860004d81c2d142e40041100701082003410780071382c01040181880900d40301950011091400000c0003c0e00c221190300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 89990558 1250 89989308 89989343
    0x14030c0706090c090509011503021818070b04030201030608030a0c080c010b12010f0b0a0e01030f14031803070603061202060304050703050d02030301080c100804061e090b0a0c05040e04 81
    0x4204209240d03000280c401c0b0340391501e005000605080306c554000c2d60130f10311000300c5008640305007025070360040c00c1d620030f182e481c021445103120003403c0002503170240c0800e12050003040c40740002410340c00503007550b110300d54000142511560742050100380c10421038241d0583c2c1146041075060703800600b094881c030164a20034010000c000e0034981040c0c0440d203145130346030194051100303e0700c44a01080751842e06002e210b101740c0c0d80c0c0240c80d80510b00701c00500c0410120320b25000c00740c0c40f405a0700c0c440c000c01c114550854000d5100840f91247d2803010002618080c44518050580c0780b40400200d403138080780d0a18210b07401c01c041d001d0007000001c0341c2400310070f00901c0007440d00700301100d0080c280c03d580259203500901c1055003500506403010346510f8004412141061244d89108941e10ba98881800414010032a228146051411001c2c408801d02440070070b180201c12081d500d04d4602104015540354144030402c2110400040c000c000304507800e16000b07500400480c10400041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 89991808 1250 89990558 89990561
    0x60409110a08030403021c0302100203090c150d0c020102131814010b040f080c060d05070e1002030c060906010b040e19060b0c0c091006110c0901030501140714030c0706 74
    0x1415400100303880d000b242000c0d000004004881c42502e42211400071010a403c900c010945c0080060f004583c04d8044624550090b43c0c11003001000e4986416105d00064016031001c03500148840e001708144040703000a04c10400002024002545401007108420300c0e00700f180c0c005d0403038000c0b4030001400e40071001d501c4209100e20720341c1e5105113940c490a0317800158020b44129101c000056902040c050340c0411083ea0100c0c0203000d050900d040312100f000900380c000c000c1000c21042c0d40c0151515500e0005204850303880d600a1640c0310809540d1504001008000d003c584c4e214600400600382030724220350071900c4490340020541c68811411002201282080312003508104010500401c000014040585540e003143c81d40d4500c0030070302864080440e4070005050400034100451806925011200300c6a6420740340b00314814400213500705000c0c0c0054403160b56075071503550a16101d0031201d40121982c104143c811150708011074542c0b0000344a03403074401c00482c040041041c075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 89993058 1250 89991808 89991833
    0x1609270501060302041502010908070605060d0609081b06090a08030414030c0115090b210a14030c0d081b0a0306030203030703030b010e0402040e010506160c091a010302040806060409 80
    0x91110502480d60756040080c06904140a6018009a684e01582990b4014440c449a0aa114815a0811059882e55401018018500c039040809040c00340005021031040104030707441808400d4640d805400b4103029800c01030060031641c3c0c442e5060100030100080c1d5107a403164030118160b40c3e55502e01d031013061491050307860b00d000d05c800305018004541c1034010300c45203c0501c101c240019515900502031302c0c60642c0da40c3d0444c41c03e1000b290808a1b050308986984004030444040f04859a00c80c00314010b5004100025000400d440c1c042c501c0170320522000d48503a180a030303110b05003548900f050307001e41c4190481f03031000080c1c0c40c083c0340d004c1d4020a005640013403e0b2502e6002505003e0050484a6000d60020b07560644400061509100303a505684002d058200c5981c01e15080c001151b10540c002814180803941c2c2c540002c420071050030241031840340200c0c0651601b44200c0c3c10f06501404d040c140f40c01408284200c9034000b80260b0f1104040b5404201c034600c9091900f20780c040e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 89994308 1250 89993058 89993129
    0x13020102071e030201501210060302040312080a060b0a0c060606020721110604230402030402010c06091104060b0405030f030403030203161b030c0501081609 69
    0x891220b6403a48412507100459000303032209100c0c0d01c0d50f00c400541c0c410754103800c4c850068210f40c01c800b201c400300e22822148510096000c00110012503100d8207500300b01c200d8000300c00030304100801088074102d0300004103034604082d8242802c555401291001d810303813070002c00c08000002500340201c1d802080c002e100c20f52503140d6502c09800001e1004048100c160750450800c040040c25600c0081c29408071000100c03203074045015180660240701550200f51407609603080070550590340d06004000424148003040500341400b4641500c110515070901d21032071041c001c000160742c10005084034680e10260010703c03808185404054020100141c6410a1030504081003081c61100100700b5118128205c3d040d40b01b4840d411035480c03069001c010300503002401400c1c0f4060380940c100c0c8120b0710401e400e4018075841240c338100200198420303258031a50311010401540c0150400b6080382c03071a81c07200000d4105001c0908034003800e100748034640301c3c1ca01080c2000c41184006200490 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 89995558 1250 89994308 89994329
    0x3070e1b120610080c090105070507080d0207050102060106020c0d1202101407090e01030c1710020f0d0507030207050a0227130201021204030c060f0504080d0314060f0102061302010207 81
    0x4206103110125a404581d01800b440720818003403070050013040b14500c5032100d1103c4078940410728004680641040c507080701e40c0e00c2404400718611710180708031f540e000c15035801000d6031442c0c20002842c00c135047e0f100e0420340d00100180f449607125809a032038404d41005031140034102020040b4500000303428013245861401910300f40c21800ca1810601504290b81c9a081c0a81c46640703000b00d0702c50a100040010600c201c0820210012482c2c041249000e403007594a4420b24500c02c1042c1c1c3d00001040c48050030005081e0392852252044a80060140c07504608141c06659449c0d0785902660780648504002c600007440003551841000410050005240c1d20382400171062782d144e940c150341240540a001d0210310490341c0f00007514100c82e00804007861540c030b05402a10b40490b0303030101c401000402c010104080d0401c101c2c030048104d10742c0e400103007200d0001c1d8100c0c9180021703204900c55441d848201605070b90000d0708540002c0185500142c000305840140d1902516501102201 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 89996808 1250 89995558 89995567
    0x70c030c0515010e0a0b0607110f0d050706030c140d1125020a150507061104090914101a042c0d120209100804020d050601090f0b03030903070e1b 64
    0x300495000b03040319004034004d0031546610403104e060320b044030100313034005105100c2980800d10b81e084400a05002416005800c01d403040840c1c5458001c10054545030300c032800c10820b188d49845628658541c43c901011407018901a640241c850391440800454a03000c40101074019681141c0c00b4100f20b800c409010056007007200580000245c00364402c0c140c403000002c0245000c01321042c030f2501039035110b00d000d2041d5240c0d002011070a1025503004014032010442d40756920600000c00d02500394045034030201d045030340c07030b00240b19400c000346410b1010541c808103d1700303900c10079154100e8020910350b03141c00f0801146d410681d12a61001400800e9130014500425500c11501450343c8064183c0f414100d80c00a074820403210b0b6070040040c110008180e8801c00080d42c00070320041042a5506060300c403246000d600707812400c06156111010303004010a0703c990102540240c1c051420100340000290326440a80b10342c50404c4400000504910781e40c8880a11785030050200540f207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 89998058 1250 89996808 89996833
    0x3030e0d0c0203070f210c0e180d020a020604090b01050c07090c02150103110409020310050708090706110709050402011106070201050f0603031305010f030621061d0303070c030c05 79
    0x90750708158240d000380152200425040b0101c40400107907142060700400815001208080f4040b0442e41526900c260300e4011410010b1020f010340a101c0c0c0c40100f401c642c400c900e1490810728441405419544507400c4000140c4171f0a06a80844440c2800010070035400c00c0142c032903102d42c0e09015030300e005851000ca5a40201c0c1c0c441881c0c6030940d82150880c841807402c046405c0c40a010241c42c0084407102e13400c4030300d09500a9041f03284041e00b901c030401d800d02c0e010800d440d0103a51030800b00e9010001c108181c101000810010240c51800010054203032950310303190715031401004541d40c1c4490004081d64001e0249800303441c041b104a55071031400c114024000c10098503408100c3c50380b000401c807580780000c10b4032400c9680d840c0705840c07280b44c6070055401c002d003200000c090588441c80024040c442034500321401321480c1d030280d04460a8a003107011200d149000103150203180902c0c0c010401d0010540360300202509003900c034103505040685078240d207140004d00c188070f0b6140d88001c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 89999308 1250 89998058 89998067
    0x302072a0509090105180604050a060203041e0501051602010207031710050d0506060f1005091908010e1e1c14040b0301080f070501080c0904051806160207060306050d02060703030e0d 80
    0x810b13006d00c0381c80182151183c01700b6849a03420f80340600f00340d00100703151001c03402c0d550003150030921850203a805036000594007140741c1500b1005540e41c0c2d64904c1044240071040503140e00c030700b031144021842e15001d50b0340070704040c01c80003013680c4001c014400148406008201100988402806904803c80c40d107040d541e00d82081340c8890040c51007019400781c50038684a50804000a80c8130141000446420f100e107501d04084280380d100d01307001e000940484207100b064181c1045202404404950400c8807810507107001481c031050f4803000c11424480ca001c0c103110520403591601d280350790f0710410400c10300d00071508022070580001000150003000003d07420305900010058403261070b0f0b22001921440c00032034903262103201c10004410a45825880581c0c8000907d0b603008410079410310161a102c404c03079a44502c00712400907842ca4940420a010050546240c10301c51103007000049528107844500080c01003401050303420800d0f00075008004040201021100c503104441002407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 90000558 1250 89999308 89999311
    0x15020c0609012409050603100c020f060f01030c06080406022208060601020703050705190801061d0a0b0607060e15070210060f05031c05040305070303030506100302072a0509090105 79
    0x301c40e90b191510100411020001d00021412218010040c2510f004003a0740501001801554140503990011080e00e613a40b19030307600c92000c0d5006101260102c6451450501c0140214020300010001040010035240c115003c0d80d80c540380905154a6078541440a4018403501c102680c00702e0600a10201c48031085074202c0b03d8a6040f141c0075207585006a807180303258003000e412900001801e010a06007503840341c0c040d1666101d48850f0955400d8031a003104d60607000314031002030301501070419803c2d11700c41c0b541045003040308001c00940d240000d80caa1140500c020515503c6400c1d45494110500c03075601d04100c038482190340e43c41e20080082d103c03210070421a1100b403825401040e10003401000f03109032840a0f0092014030480046503400220300c419a400b0020104804000190103001310f40080d4840d40b000704085c1011020400c0a0100312000010144141302c4013012034180300c80c0c0080e807090080400d004101d0280320038034844094021982282424040c809139002c15481b16 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 90001808 1250 90000558 90000571
    0x702060406030b1c1b091a10090512160b04180b011704110102010e0d09031b0305030d020408120306061602030c0d05060618040510020a121a01091a07080715020c06 72
    0x8038405901d03000e0070012201c480701847d50300702c60781c22070683c642881c2c2120036000340381e41443d101c1140e403040054020064800340000c50f03048210240c4013444600c1480001e80381c0704041c1d0b0f0400e8201099110443c51320440c0240d41511004560760a90151240c07483c0003403526151603d80c500b5007803a41d003601c0e101001d140198030301034420b0840304020403110b145c100c0940c0c864544d0340c50b5440300c0c680306248000755030a41c0c016002c0000000ca04100801e400704840c0d1016895601d0004e29078100350460001a558802c2001001a159101022035030f544d04032031402d80c04e10b4807a0012920300001185c0c1c0d070360041805d074040310510a00098a5204042c1280d02c1c1e05031140500d603540d000b0342e05503401031244d4424070905204040c1d5030060448540e1030314000c054100d203c070002c02134824034507a0358030314110b00c0468012564004d4540c005480494035104c0142c0300b0005c00001486524400752001c0000318a59040103130040641000b0006a441991a0b450b803441c4a511040e050300c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 90003058 1250 90001808 90001853
    0x1050f01060912080304050c030604050a0c051005090603130b01090605040f0204050114030a0212180d08070e0418020a1e08010605010804020103020a0e18150103020702060406030b1c 80
    0x7606074450001d5800342c41241041c40c014600580d51035110b6040908202e40d1409841c85c1d030750241c5c030308020007407080b405400201181152820414980051070304102d00800340d0a4180070502e40000880e4054281070398001c0d036a1740e400308849801108400003c01140000000289295141d01f0007015a0b504039020411400e040400504074402ea104190100700311410021102c0045805180c0c00743c1105809860401024440c2ca030040049580204071310068059100304001040210625003030ba0608408900301070301c1c0985008940041c040c42591942814510308030003a8104ca00150f002d0103901a8039101e5059100e038401241c2c910400e400700c5040001d87c490140101d10840314180c4402034503440c0d540044000e5031203140300c0c40c240001c010364407181b0b445007200b4010382042020f44c511a07042500e04002510035a03a0746504050052201d03401690320759003120300300d80c00c3d41030000e044040031000c16108240040c001c0c03260741c610030400d0203001142c01c4010700032410004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 90004308 1250 90003058 90003061
    0xa05030102070b070f050c0706030c110f060402090c0706050c07030e0306040f06053d050a0e010b0c01151e0603180204050702030405100e0f0a061202030a0605040e01050f 75
    0x1810300700e0003009005001908040c011551590240384214400101440d000745452034100655191404991004001a503140309214036a50b0000c640100440d40030090408001c0d55007480d41c0d40c00c0003820103481401c4400202d203080414400b100c10280d030102c418044c5250000311750780c80b900404026408142040c00c05060343c0340200e1800d2180754845803010119240751900801480000d2a480540002c6c0d04406003485c81c640154081c0b680e80c1401001d1403007011a082100314665001e203000389013580c0d007840103041e0690254103440c220701909840e00302c81c4034820b014042010581c280e140a9100126014206450509038400180d2103440041c0c3d56102c101c0444040100c0e4140682c0c0e000350000042c585900100e0308031038148112810240c072000050850110000000045014087c040b9600c0c1000090222190310407200720030007034a00031010344451220702082c4ca80581c0000011401d070304030790103800541300190040081428136400c0900070442a40c130310070328411940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 90005558 1250 90004308 90004319
    0x40c091707080601060e01050d0212042a03080c030702040608030c1212010303120e1902040b030303070c020105070614190e0a02010f0c080f0c010203062805150c0105010303020c0a 79
    0x41c14821150458020718440c1e00c2d0000840340c500051102c2810000d0070000682040054005021031016021041c2503e00b00391a00d214064000c81036140c110114581d48403134482c0800d121b20840360080c6019507a6401c03004482e0551040602c000c1d4010329140e000f041048001024080c007803054021600401c10303510340d048490280d442c650b004815aa8010b10009209141144080d11301d100042600a410030703444e801c108c1305101024010a02c44150025840e0034090010b41a0055003e54a5030522907801010b001200c0006411302000192881c00c02500754000790501917001c1140d182c6081144405074507401110040340424100444010308a03001f060450001c0c0c1d05071103044080340191002d07104000c0d580700c207850400381405411000b18885c00104039000190f800142d591402404000384000e4081c8810420b0b0f20035840d005044048814210540d801200c802e0313480c18000040890030702c500c044203400c03942400000020150000303110001082c013140c25180198850 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 90006808 1250 90005558 90005563
    0x4170304020307260706112406010806030703050106090504030f02390d0f020301060f0608060405130203010c0c0302070b0a12020901030e0a051b04060e0a0c030209040c0917 76
    0x1038401a506800a4804200c03155150300d150a200b082010a8045203c0202d055400d0034099885000030452400c00340101c0344041c000b4050003c140c100e031041001c4e040c601402c0078100240014184000714020404568003000803c0055902a0080c012140c50b08480b0002d001c0230342d41140451f0241003000d100500200395071640240ca00b921003084901c1c01c0000226402556070b50000c401c110303029103050b880320030b0400034007800b03814203120000341d5205042c21920283c0c4000c0242031200400e00810b40d01c03802e05a00820f0485000c1aa91a82e248031080b0405103038000703616600c2e14a000300b070703190030400692100e4025025141450350380d0f0741c584c0701d52181414400025000711160850202a0f9014044583c011300d00042c8111074070100301c1c41c0c44242241510603510200b00307216080040c2074460891081500c0c1481460724000421900440c0a08041c01c56a2511403c01c8101e00c0303a41590540340d8010024050410912800b42ca42d613010700940c1d200d03045284051080f440e00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 90008058 1250 90006808 90006811
    0xa08040515070f03032a0918060f063009060f020406020c06131203051e0702061b4905070210021005100512070b160201050d020a08041703 61
    0x1082d003d107840909950201e005110401104080780603003520a24001e41802880b24503441c1610f80c0c41425050885030b6603030140307150662405900b07055040c46000b5151915200311400c0e070030041c151000d500483d50020003008007580d080640c403c01d030381030a60150004481c49000301803c00c40c070701007160884264800d41c000c0e0705c05030b80f01050a40f1513041a40052030310300f0300030621010050312170091000c1e0581d03100040c3e0002c1c8002c83c0c80d1003480381e102c440901410b20300d1585840d201d51580410800e005484400649202c0c494030300204072002d0200300e4240b40b45028200d104c9080c05c00e48100c41452805610483d440700303000b84c0311000c1c04100b070b4881c0f00194484d02d090080319804c011210390840d50b40382c114028020030080c0c2140314010b45014044050440c90070509042c03d0007180c045040d40c1e0074a07603206940400c009291402100d02801c0300200c0302c154040c40e4001a0b440e48207003541c0000f030501c00140403c8090b0703c1b002c850f009600c00d00340d5103038144121402c11501d000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 90009308 1250 90008058 90008063
    0x606180807060c050304030203070b0a18210812091b03060f0103021c0506040302101103100905070201180b010e01050607080306040b0d0b070305070e0402130b0702030106080a0804051507 82
    0x401081400803e005050341c111892142e42160301e0151645d02003810300034182d00180321b1010203d90423036040d402c041e40c00385100c01499800c0007545403006062640c540c0d8a50303000c0c20f1101900300c00521007000210340c11101c042c0110310460400c02403460340c0d103080c9408289100c141803a6240300c0d240c0883d80c103000b410820b5404080d6401c54081007403403d020b46001212042818003800003500500506111300e01907005046c1d43d5888144110942d003a010980d001810100200301080d0903100344e11058a044080002e80d5030b480c0601a40100031081030098800090b581c1001009100e40c0340c2e81c11b8030510400351110766a10000d01000740282000140245030510004000e8140366000d0010302c0c00090404801c4c881d02e0311070212004040c2d5955002903100d204200300035820520100581d8400d40e021860020390202280011005001d030084800000403080b0541d9002d41241d0007030700c0280103548200c0a940741c290013603402031082c2402009462040030003602d00e001514034854 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 90010558 1250 90009308 90009313
    0x10602100b030606121f020d06050a030213090501061205030c07060201020c030406050304060603080d02090102011d0705091f1e0503030906030a02131a0c0f0304120b070203070602030a06061808 85
    0x499110805c10f80240c500340f2582540320304035040d00030420030740c64a54801e400e1a00142d48201070303030812050351b0407900101d0042540002c02c200688400b64520b81c0c4034001003001035032192a1034058050007107540300400c103040b115814400c2c050040000c021183d4000704649020307a80b494240e090f0b008843c0e032074071650000e0004014250050004641c03141c4517000000e002616592403032120340101070f050700d0349580824040c0c0c0d996024441c21500d003c041c1c01c5002d4101041005a40d039075010f00070907010318102d0000c944025290310400c400218401a080c0e040764a8514515040600c0c1e480010200c0d4507103000191400c0210850314800c44c0070703040500d941e4941c80418043e5000f0101c507428145020300c001182c051828025104500d4120005d90f00d580910040b4503040c02c0040e00740f0181c0003000100b14444104402400b110f6104007407024542c0e42e44400d80c154022180301800d034a0000040080c841029808102a2082a1281d80c040500102d0041440495000390402c44c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 90011808 1250 90010558 90010561
    0xa1101150b0a0807020c03120d05061918020f0d090b010f05060301060f020f250501030e06040204050402130510050111011b18030f0f0b063709090506010602100b0306 73
    0x5481144504e81c001c0c6a40100c40c4242c201c000400d240080754001400a030601040d4141011a54010300d0740140701101c0341d080c41c0c5c81007a240740c04200244102c10310002c0d603da003401c015810b80c0607210320aa0204035076844650a000c008054070b46050101d4254404c00004a00654100210705c10340381e01528aa085a0919400359801a800d408140540c031803a6034480603010100300141e4034000d0b034000c003030a407482906d19117844402900030505241c00d00070b210411410020b41c85901940448003c00c03181c50700c3c00814210a81104206001c6060000304008000c01e6410081203c400b0303602c2d200ca02d00c074581154201d440003003070a19984407501c8104036032403003070009003250b84500d0502501d55030740340d66410795034001000c02c84680c51550814424003105960301d42d48480d00b603503100c8510700b40e80f04038814041c85030f01c0022180811182000320116800c10b000c09000e95040c2045140e0860405070b60fa402d003481003200520840d0b000c161201c8842c01544442c120282c000c02c040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 90013058 1250 90011808 90011827
    0x70e0105090c0712120b0d0f03030509010207030e060901031d06040b18030d0b010219061d030405031207030302120c0702090901060609030b04050a051c020d05030402060a0302090f03030a1101150b 86
    0x8a45c071030741c01081410b44940ea844941c2c0d403414400c940c401c1c42a02e03200b0006000345005815124002c0c4880c1c51640f0621003200841c0d04141d0344c012502c3c08960341980d41c2070700c0c00180d0041600818080d01c80c806140c0c07035410a040081c00034011401010b00714002d9941d43c04e40c0392144100e04401c03007141c206201b29003900c0d1868100443c1030b04140107560450a034000c0d0070201d06654003003540d13856102c80c1d1420001900450200301045075070065480c260400c00482d03614140e10304030840c8070000141c0501410b100e40c2c1a5400203031840304440c01d50070700800c4550140c00541c401e9114102a101080700424148141002c17102123840e4201d0707052941e26145950840140251550300404000707000187c0140444c0d2402c2c10380d00c40d290140d82290b10000d28050790a03901e841840002c10030310000d43c1e20241502c0d480f410a00d405650b402e0100c01180101c40c644110a8240c070002c120410000c0c0c102c04034420015602008025842850041d07081c10b92252064800400081100341d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 90014308 1250 90013058 90013067
    0x9020d0608030a0203040501200307080c0c04020a03020415082a0c030703020d142106040e0d020c040b0402090d110a080604030519030b280305070e0105090c0712 71
    0x250016411800a5100d0361074403800d0640e80851030810040c1c200040500181d038000c40c500d1401300c0800c240c0c5041c1e003c806440c0742d40741f0401d080070700310701d40108045140b52001c01a030714018002500c25905d4640d03207a8054080d4019000d0030010444884110128511402600340700d09502070310103056034042c2c210304111100c0b07031303450b128001c90420840c2c411b81c20400017004058860742c020b2801100050000741070745c642c040100b0008404001e42210740d08000c82c0c0802445d0078000000c440c0d2540301c0010018216425104101d0050140c0d0411481d00071410300000a0103441c240301c100b0199003040100d1081c0c0714a00c0c1c7c0712605600343d0003c075070302c00220340d00d80b00050194038283d030721185070314036006080f10100c001403030001d140b100301f020001d624901081c40342018092410510006846200d4444814550415031080003003549540a41840103541100559000c2512090b00c11004002406258024403481002c500400014000c54506517000038090000b03003c1c1c85d20449 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 90015558 1250 90014308 90014317
    0xb120a03030e0102040f12030f1d10050405040f05010608130b0a0216080705030a0e09040f0b06210102040504060e0928060f050f0a0b15070614011d0610090902 70
    0x100303076500b4000401c4501c0300030080c0000c7c00030410806400c1500307181c003c22000f210940403080201c18124501a59804001580c4129080701c40007950400720004481a010390340c0305541c403a05201e640101007040782d0145044e54825a208801540c0d25000180f0b0a0302560f03004000e0400f84c000102c80c0840e03079001e8a808100c001d01031400542c0d50300c804501d6040300e4015101c0d41c0001811000c026040001c1540c901000d9501d0461850b00b5216180c8444102c0005003c00c0c40d0320740003410395507a003014200c0805555000a190611040d4880e000f908103014050107180350000c0800e583c40384010503442281d44400903c1e0050100c000c180c0072860f1080d0005900034003c0d21231001400d640a030390b10114201c2d4001410b8a82300c5d51300e12100300050000d0380030324038040c1012115191107103144070240c1543c4826a8540c0300d450034400920700502d1801003451600004982c07001d030806400240e58403540c5c00d514541b80c510411036800216212407000c280c203102d00b04140c40345030b009803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 90016808 1250 90015558 90015581
    0xc030f050f100b090109061803020a03050607020d080f0c0c0f0708160503010e030405060c03040807060f1b030801060e030a020d0305040302100201050c0304020f030313180e0606030a1e0c090603060b120a0303 91
    0x103231a42d504c0d8042078484860380c01c103c0e2203400c200d013007200305581042406038903045843c201d851820041100c0f01a0b40c000303003100d80604400204400704010070014002107086050856800a075581e0909448842c0c100c544005c2d0a11282c0000c2c00e40b50500800416251703c1c4007842c9041d00e0a800c000c450b0784a4a9070ba161404140000101c03240c041c080c01c0020480354032400d4012054040c020403c00d4040910600361171030410500c0465441a41181913452600b040740d5480c0c11100002d141c180301001c003d510107010001c3c0020198402d002c0c0c81243e10a4401111001c5914400d9003683d804540c40300f2034100170b04c00100985002d404c08900401c0242c2520724111209801e103100c200c40d030304a180b09034003851040394110319511a0b451280c801d000501903d0130418000781d02d5040c02040038052155200c0800503070040c4180b845070a6501280311390144c4e90b107082031000b40c000b038072041e259039280c42e0b010f6490742440000e44c4502c104000260a5071146942d0075802019100d52a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 90018058 1250 90016808 90016847
    0x1401061110050405030a08010501030c0f080606120103050c030c0102070608060f060c01021206210a080309030408030406080f01090606021914010c03020705070506070b0a0c030f050f100b09010906 86
    0x40351401c54544190b0340550b004001860b503c1c03041c0d00300507103030003010390045041501d4000344800c0d066204030280f40b030f12100d2401080e55100c44001030114081c1c059041038080040e000001004000038220350904019400d07100039006c02c600598490201d032145c6030100d80c144001030014030300305201e60300c41e40d0300138012800c080560381610708a13080a403603071286900550600181d441c2400c401820f081c1103500b120300501e1340e840ea8070344500d1007090050540ca00440800c00501040c81510040c042c0c1204594940303903101001402d121041d103010140340074010010844070100d0144c0010b5540f540c000b01241302a041d4446c22403000007001ba030300c1e80b0110f200d2190124080c003a0904083ca41d0f5405a215100c1d070902c0d9003032508a900c418454401080541c2c0000c80340b41e00b00e640040b50355000640c0003000001940130b8042d001000c240c0300d140070108030701b85001030b043e10701503446a00071001d81c0d603c0d140a155123100d01105180400c00c8141d0401005106040c0c3c000411040102d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 90019308 1250 90018058 90018073
    0x90501020f0408010b131a040f061a04060305010e1b070203100e0705150307200c0301050415151a180d0b01080607080c070f020105070209090c03010c020114010611 72
    0x268503007150400e42041c076003651034055042c4d592414512500d102d1808141c10000e440080c15070311040c901c070b80319450181c1d80301c51201001c180d09510401c028000c4110700d021140401002c12000d13405800f60401281ca400c001254210308909910720070700384520703020501074140070360381019005004c0c02c036407510820100c5620790f080c80c094000c0c203040032401888400e00301020070801c803c00c801500d41c880c42c14010461080e81c4010703012072a002c00541e8203462840206501d0034000326490064156003008244003c12803440160041c00c84001010402124a400701f50030880b00362158403d07000c060050800d5100c910001880441e8611703805001d0102a000401d040521102090b0b80c501c0c0f034074004014505007804056030240701443c080700245070054203000c0c507000310b9030b003c1e1050054503803120441e4003800440b0328494000b0700110251608c9054917a4545151303800c540254280240e80c251140140a811507096044201c0d03c0c880e130a001d0202e821100303039020003d56220b410b2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 90020558 1250 90019308 90019327
    0x80702040b040e030d0b010309050c100c060629070209060609060408010f02030f010f030f0303150810060f08070501170a09021005030604150312030f02130909051203100909050102 79
    0xf1075100d4280a05014545808920340f45408a0350309544403170502d420300303c0780c03400a240418409491601114850354284469208566149800000074000352400304040703041005035245800c4000c2d11702c402d424404001c0036005075800b5001e8001c4d0001407480101c0c009140071005026103000192205062564a0354002e0a41d40d40600e45008554004240403580480a2606002d01285401882490714558940f08225040c80b005400c00d0340c1c9003c00741d5001c0c41c0d503000000401003e011a00c0318100303c01d10000a050b584659003c0c80c507100da0016540b0340103c0c0f60300c1280c005845030080100100313481c06030705c00010800b00455544004501c0140eaa4410030210806142d54903900d07864460140700c00c45101c0502c0c5d203c14044003034100000b50103860b21468219040c500425298040c8001d030010b4010810320003410500f964000c0b074046115403040d56814001d2007100d015074002503001605200580d000801c02450285c00d12100701d0b213401c080c1c0010311030f9000514249040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 90021808 1250 90020558 90020561
    0x150d0507052106090f06060d020702030102070c0803122a091801030c030b010815041101020703151a041109011103090406150807080f070e0f040203070f090b070503030103080702040b04 81
    0x310100e40c4030700528284401da05005541a0303000c880c0801c1d59425080c0300300020043d00912305041420754000031b419045440a4040d42c0949611013100001c503500c482d00e19440343c0168409403071a016240005030b16003e480c0000c140400702904042a041e00541c1480e40c42d400400c0306900203200008803c3c00d51102c02c181d50003540100200401c890561a2000f008441a480544107900c5020040c602c488a046403581283c0d0000d260081981100d00507805c1032010392020301050070401a6400090301c82d0011505000c2440417640040312141c1000101d46178070050a807006021b00030400745501600c0c0d44d614440c903850449090000d02c0c4001340c1643d11030f410050b0500803101d00140c0507900400341c0340e00402c03d41404802454180419091084000c00e03070343c10030101d040000c100c0d4440c0103d4045d03483c0003400542d541e1410741401f425448402c1190f200145c6207101c0012100d40c5c58041e500c5107036005010314616480c50301d0f4045240c0201c2030999000750f5840e8a040241d551703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 90023058 1250 90021808 90021847
    0xc030525090b0307021c080c0a0c020301090b0703050a0e0609030f030c0409060311040c021912050405040504050a050706020f060103030302030615070f06060f0b0f16020d0f050c150d050705 83
    0x75a0050600725080901c0e403440c61098886e24040c441d0400074031030411008020b444413181e5515205415014a00000e4054468904058004040c0d070003400f840a915070041c03880b40c44040000c1c060044a400302d40d544000441d400d048a803c1805030001c001c030010010b50304040e00c0e12419003015140e0103000101c5041d9802180e017040c03643d100c40e00c00e040c42e000c0c2c42ca8109440c005800d01d1011080d05040c290449180180414200009151018001c0c0f0a50300a0304002e00100458600741c581613039541c0000906070f51501c9a4140080c0e118030000340404400290400751406910b1039400b0741c044c1d003002e0300050f803043c2d01c0414691403d846201030107030540654030020012509040010817214903402007184403d00d540103219003030b020000c841c0c0c55a207400c02d040c1d6503400c00ca4400e20588225030000c3d4080d10450b00c00c0280302c4042d800c100040c0c01007017940d01d40e0201c0000c00c800380a28440001080109011048080600703601030740d400111403c0080c0f401c1c08802e4800905041d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 90024308 1250 90023058 90023071
    0x3010533090102160e04021011030406030204030212030f1215120a0b180309011b02180703050a05060a170705060a090602070f0f030f0305070501050a0c030c030525090b03 75
    0x1004140d0300020360f410403800416014a1607034560a50408084043c80031004102170700480c04180c0000d44039124581c41e074080d20144040e252650303285c181c014081d6120340720980c462140360884c41200078000c411910030080f92000759240c4410590300740c003448030040c510b203550401d450b10300c0c685441c2d51070030720604d8845034050a41d1f03500074902100303400c0018103045c40c401085001800d200e0400000c0303940d84042400c0c044c01c00070468802c4230000c900040d000390098001d8140c0c400c407405c00e51549019000e00d8805102d01e54805440008507103085a4959101102c03034001c001c145180c00380d07090010801020391b0700117911038000c1a00742c2d100902c0d603000100d003504100f100950500140029080c210049080d06103071a0441140210600000e8006500b4108079010580240222035840f98810700038007040c43d1021820005010003070700c441c0468101294145641d00c079102c4c031403150440940c0c01c1c066240800d514100740e03018002c00800c0c081964004568a0040310107544110f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 90025558 1250 90024308 90024409
    0x30c030b06030f010603030905040914010609020702010f0c0b01030609020f370b1e04170102030433020a030905100509070b040303080109020f0403060212180304060203030105 77
    0x9218003410701d0030340a058080f82d140d140510078800254071403640e0b41222002c50307010948a04601f0400384150241c42041082d40c6000d900040030b55407a00a45843c9000f40c82c0e080155200d80c00a5503a000000f0780103120717030414001440080c80940c00598524000b505e0201c02c41c2828000c0749088003c01c9180745840c03101f0b07008801511014500b16800303500c82c03e841c200e040c64800e51903107601511003912a5000c516107001c0ca03d50300401540c2c010301e80d00d28003e040a10440c8414004e500c05e48040c0c6501900c05c018101030401d40c2807000d4891f04c0c0504030114480407402075402504600019020140c0b40d109802c0440d80802c9041d1000e19011302c00a003605119800915200c07856100440c406414042000469000900c0034111041a007015a0f261040142001d65100b5600010411480410900c60390404d44010f10701c10b58444007001405041344a0003a0761340140c1c402d85e00160700800041c041030a04071080d2003134640200c0009181c0d02d82e462481000f4242c1d111004029 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 90026808 1250 90025558 90025561
    0x90305010b010309020f10140301030c060e0103060518101d0a050f0c030403140d02030f1b04080307110406090507020607020c0609010c02010806210f010b040c0504030219030c030b 79
    0x2420310070740c0301c58682400e040103421a90360115180072080d8810910030f01c618a803010146000e404082200440c1042107a0b881d0786030310700000344210500a180c0040c900d2031125070194003a10409040d10401008034106080704c8680441e5084020100000c507680540006541e040e004850114010030084281c481d10b0316820380001c540f0024003180700044140f0a00c0038480000e412a80c005405141c03a11424841c028500c00621820415000e0b10f4400001c0042030894550454090700740031440c07041040c41804070b060503000314000c40106810420a240004000b1010401083c0000d800410281e03a1282840101d03041200d8000150300203e0030000b0f000e034103001c0c0d40714013101100c0403810204403a00007001000d460310001d042c8040c020101d61a0340d40c0017510300003159054044120125050b8106840c0c048008280c202903007040d50503070151402d405003450356a06a0758450030726282d5000c00001b83d400e40f2130702121041031107001c000f1880b4002e0b000043c602581440509 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 90028058 1250 90026808 90026813
    0x705130b0909030301030317040501140420090f011809050f032104051011130807080d0206040812060a08060c12060d02010c02060d151203140c250509070903 69
    0x207440d000307000790038540040005200007070300201c0b804a400c07415101e0b40090b40d10b51410b0350041150010b094046881041048100107410040186038120306181c034007001004018032145000c141d82e8039000c684a440140a51064036800c00e40c40c0485002c04600110503443e0345040240b8840c54200c00d40000030785038241d0052094208660441003058081c0380307055241c040d25002402d0414850680343c19005c6181d10700c070070a50b1050141500300d060002c0c2d550058950360002031166030024000c3c00c400d4400030b4008111248901e40210060b4500f010300c0503001e040500042200c2d50040701e21001080f100000c0041ca403080c203059440950300c1072154013116241d54003c0c59180705029402403180142d900101303113056254140c0c2c10741e8580014400c4134000c0d18003469101c4d0107081d00712000030000c2803410403010150080d01d60640c040c080c1c0d65210300c00d01c40c0c031800c440306600646d2250008180b1013000103102481e0000400e400e0307107a80001d240e041050362441c0000301040c2e003d109 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 90029308 1250 90028058 90028069
    0x50306012303090f120403031b0204020d05040201021908031303090f06020601050f040902030a020108101701050103140307050a081303080f0a020c041e0218040905030c01050105040b0f04020c0705130b 88
    0x1110403010008000e8900b00500315660340c401d1f80002400c11203000301492003000200300d0b508030f4950090055449580c0f040c0c030b0a008120895050780184503144100d0030801318a2440148240c000c141c452a59603042c800c4281d8807280c1d00218204000316400040c500408080c00c0d020b440340e580503255079458001004080c0e100342d68800c4c4200d1400b42101c00607a400942d006010b40d0a09044100342d44100030120888a164400c500c0306501d114001d10410045d030209040c0c2e8070404a0a680b0785080004a40d203014421006080d580200542400b1520000c0905444000c0d64441c940c00c54480d0b85900081d009100f100305240f5000c94611101e42d014840340030042415141040352003054400d020b1402181d20450760260740c0080e417010a00e00300d03d01400d05100140041c4826441d0785019540e0350f020340d5115541e5440c0400100320f92400d4011042a2000200901100900d410402c0025800014610f5140c8212000050785407218081e441a01001c2040003035013002040074000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 90030558 1250 90029308 90029323
    0xd090314070608040308090a0611130e0423030705010912020f1f02090a031a010f121104020f0705060c030a11090d060b03030c15060f01021504020105030601230309 72
    0x45550700290414400160f0040b80b9603403064062a014589031640a4118100310301004090842414040810848040f103001022000006080058031581d581c0998144213010744000f0094918452481c0a803121822485105a2041c003900e00d032100541c1c0380760840b1031003581195221811031006031455014440440d4034042140900100300301c6e2441602c0c0501e0110300303200c225602249000380b43e1540c5540901950b0f0000714080984001d01c1081b603550424868800c2d1001c41c0440819400824135125044541c02078111000200140070000a50072400c0e035a062a1401d22400000c6501000568002c2d1500900c80b590380c10080c19950507500c44c400403815a20b000c10050701d8580762805c50440c0f45420040c005414036052000908500c16030500091a02c1405501401944640300c1140100021141d0b003038081141001039032a100702c20302154140c0580700009025501510055034010303014940307a244020100c540a08042100350b0603903403488040b003000302d510340800c1f510 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 90031808 1250 90030558 90030593
    0x190c2003030d02071a130b0105040c050d02040801240f1214032a0c0306040b06010302040b0307030203070201060e01060503061516050606030c0a1203050c1e0c04061509090b0d050d0903 81
    0x1030342c040700c0c1c5491f111582c1d4010311645002d0790b40c0791204c003985481941542c00c60064248103556907956038031300e0703401b8095140d140034004811641070380c1081b602c4c00d031420442d48078a001c2d06086250a29088140d0301003927050307031880c0700da0207481c0c1008018002042c204c075140101c0308a105100b910071555074001c11003849164000d0140c40b50a9800084441d1300c40d51000840205999050040300039000355400760119101c048103000e081509600a18410005035008104442e643c0c2074400d41414203104810110710104089185410842d41c1507140110b4202e005151000d500a140d00c2c1c400408815035458018005008061805000b082c0409800312241c4040300e0034800003000a03d103502004050000000b10b020b50110280840c180480c5040985405500408045603c03540058900c5100d1481c1c108080f03000380d85a000c0600c4003495923207006115003000c051000528010403060390242940c210503002400401c0310b030300407600035594401a00e10314a0522441c0000d1740c8131 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 90033058 1250 90031808 90031831
    0x50708061914030115030c080c04020a09140a0b0a0504060809070602061602070e0f041515060309051009060e0f010b0f0f1c030302190c2003030d02071a 67
    0xd2040407030540c010607003a02d00840c804201d40908400080c0103000880a02c03041a260400c004240449908000c045825940c144c0301c00f1140c200c1000128480c454034200498000c02c0b041c403d10103107601000501501500103c00162121820080c039040486408001440000c080c071589503c0300c203154001e0300101c01010380c6401e042020791a03c2004003040d9a050b802100d0200c02c038403c000d00002080605000c1c2000e0500801c208070813007003110701703032120080800319058224041c03040704900d0307000712044c0604606202d422000b8150001c02074a407449081090450481248101075540d485410001007490324040c030142800c12802c14160f60b07074500140314180e40c49480390030120300e00c00c4841d82c071000c420400041c0950300f5280124056229030841c441019015802808510741c805608100d4811f849821104100c241c48014800008c0708980c560300d02d052144030402c0341d070040c181c900707000781160360004176000304074142c45640621001034003c01c80c20034802e4100c2c604046 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 90034308 1250 90033058 90033079
    0x61202090109020724050403030b060306012708120910050c030a0503040204020c0a1101021b0105040308030901020f19122702030f0a0317060d17030606160605070806 73
    0x6903040014461485510f0300014244200150081c8030500a00303185030482c3e5004a058141d0004c000496044000c41c1c50103c41c1e40c890324001003564890f00c4140d503111541c2d01700c20103110070114840c2d045025491000f1010600304d800344000070380000c404130303002d440f1219002082202c601d40c1e0003041c14000104042c0c102070001004441c20010039041c4140d40782c0701ca01c0401c009104030f80038038200d80140b5003814208a0041602002d0040907800c40d92070a110785038840c0151042028540480c1040000300700041181e07000e1507000030316070300040c00e2002c0c0c03c0001d08a07500601c09203500d5011151180700d102e40160550f54840200c03801001030b148152020381c6001c400f00030904954048456800031982c04020a5449410040071b54041d6515481d015286600b00a021320021640d14009209810440e40c041f104581005003da03803051400701000e41c44c3d00240207640c10600400c0003041e0300e808803d5005070a07105000c0041c0c130340b810610081c440d14003e0426441151401c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 90035558 1250 90034308 90034313
    0x1401090606080703091a040f021305060d060e0c09100f14100c150204061110050903030f040609020d0f1103060108030a3e1b06030403080711060103050601090612 71
    0x80045030301807654100007070300c0c080b1750a02e0710240700280d01040c8035860401c104001c001d813111009240d50310956856800101207042202900d400f01e0b1100e4120f0310002e1440d003c07a5403500140c0c4d00d01c11b008192151002418040350b50b0100440311503a01c40b4110000304250003162210000409010a0080b40d007100c410014504404c1c11701d40c0c100300140744100400b4403000780308010b6030750780030b0300300f1551a6503404000d02503428003e0b848169008a0002c00c003030803140d001e41e51088442074003451a554542c0c006001c96180074000f502e48a61310b2801d900103880309014440c1c0e5600a89040c15249018501321603804010701c0340c2c0380603800400040000400020941d080c018241c24025245400c2001c0d5190300200c50351004c88100c107604072035947d0343d80709041c0711940e102002542d14050044010030b030344c1146640300ba500144100001404a48503c0e6034075003141c0f06180a1003541030540c592850000f00fa001076515400c00401008000d25070703c14000284201c1c07401280d00f1041e034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 90036808 1250 90035558 90035567
    0x80705091807050d0c020115060215070c1a0c03060f030a0b0109050a0e0106180e03030705030114010909050717090d020a060f020403080a030b040b060405030a060c1803061401090606 80
    0x5545040030a100002203082c0714000c03001d0b610115420302d02001940700000307000707018203142c9180305007184256001143c081d10100d8120042104c1c4604400d00b0f40f21000c04035a04100c0c40000c0d920122094034906145910002c540c0c0100f00b02000c0365200e0410004101d0981041d2894911903402541c14070300203001101d0040c115000780500003415994140e03090090002c0e00390080147d460b00385c000c1041d014161068804d41006081004481d061b44a219641d11064650801103001400104032890080f0650070480c1070614280403000d903101044002e554054506c203010850001c05a00b4250440101c1503201c40304071300800b02c0c031400b0000a034030b034040c186001c1c001c161036106903100ca0246804480c011544084003136a10142d4041c020010607a01c6a031034441c60500e8100c8000e03142c0001543d007603850040c090718031004155150002068224212818031070600c12400c000510042c0d04002540130b4100880d10103181848d111345200140c0106001030316061040c09a160b02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 90038058 1250 90036808 90036829
    0x3091d090c0f010e030f0703060f060501020601120305040e0c0c060601031a0909010b030312010e0123010302031b041401020c10080126030409060501020c04110f0901030b0402040e01030308070509 86
    0x141c6a00b4000d11241d0012200342000112058151048200303002c00724400003060703400ca030300070b0b80200900314885a0707000607201d642c4100c50069010400620880c00c0ca03004000340540300b401c109103016510340304910381d01400c0b01d01c240c0c0550045000c007003c3e8010b02140c0d0307000009280411403040302894030111001c00c010403500590f8284c0000325944025441a8031008006003103170b403150798030441d000f6603a41c24041d80070b401402c000002141d00a564204c120204143d0782c001505030b06600440c003e4000501c3c034411007605040405070326980000230300140000c203003003103003818042001928003201419007174000c11481026550490348880003030b066600c285400002035548640f41050340341880380d03001d0700c1c1c00001740c0000c1a168540c0614200c1c0d07420323002d40d450704444000b04411100c11400096903114108100c844480f0000000c09400d401414002803500501c800b1408a800603001a400e0051b820018024160400c0001d60b010105280c0b01740380c6103400c404503448142 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 90039308 1250 90038058 90038083
    0xf09020919060b121806041505040302010b0405040302030c0d0804112101020a0201050f0f09120a18080c0103140c04090c110109030327051e0705060703091d09 70
    0x840700d9444903008054004000400000c0300481e243c181c80c400006842034180c4407101c94244003900b1140411010070214403460b04030344c50310780038161400320401a0034010310450031550f0380c8018100319540c40c400c00f80602d001c0e40c0116140c2d8240c800e206c3c40c05085141420034041044100320000700140400318000e403054500c1d0096041d2382c284005c5041808040321195400400c61030000e0b941584114400c200c011a248500d46448001558024080c0c4140344540c00904401d0030b20080354000300448161460081144030b410401c050b5088502e80144425411a44003200c00350303454007803181c0b40c419005203500701d410200c4c4800c069103d1482020419515080c0c0710107002d0140e14a8182d800071800248100765003031800a0061a0b10504e0f01c55000e400c100c841115584642401e1b00940c1c41001001402d240341584d5299001c41c18001c8018420311201080e551110009840340030302c01e46480701c1550900c900380f207146030b050a5960b040c039200400c004401c0e500080301c0d9a0000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 90040558 1250 90039308 90039331
    0xe03040306090c050315060a060309110d020a0f2d24050d050a05060111061303080603070504090818010c0f030e010c02030706090302010809070e06060c16180f090209 73
    0x60b0245044441854564007107903060188041d050034081c2d83c0e0a6061103a0007c41e80d01002545031201502124003840c0702803c0c0622180a0207180e0804a40c4200c00c1030005100c0d4000c00c1c0c2e00c501c03e40140000c0d0300203d1002e06218810384501901d0949580d800c0201041c00b040142042c103d07032000c007040300e508001c403100d141200040301d00605c02c40e9005042e11000340708074505014444080c20342074910500103207080341002442203010803424051040d11000d152141c156413002c40c0c9030b000c00b400301985400b94020004166840c1d205400c1c2e810310450096441c7c030414002045204004410141481507080799940026a02810f4a284660505000c2d54605170000129074000144030005e40621841c02e01044842d0000405011039100b603880c0d04003aa1000600d9032944090721419101c182404040f82c5030345040809040c161001d001129418880c110749140c104130301d030388010354000302c2101c00220940079004031148250b0b01c1d5028401c454656000c120303018402401c948249 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 90041808 1250 90040558 90040571
    0x1020d181e0c0902030c091306031511162307050102060403110f010c0909180b040b0702240403080619090c020c060415031d120d020c1b090a0e03040306 67
    0xb1038010500b000d803146a1046450b85460204d01d80b143d4000c0292502c10810369500300c2c040002400780710181d0341d016140640d812000700c1c00c0c00103017095421810724000103200170720043c040f002c880c801d9280608016020402c0842c1c00d40c030f0001441244803441c0e00181024051303030b600050040e41151349898110246103050201600748070000040e44019400d1241c91280160302134020426124000010851140140c0801155054411000300040c00b000c0c0000d002c121981c040c2c6500c07400d5401078903101c05ca00c0184905240c0d5140d90403c407101c1d404184001d041d03010301c0140e8421010303500303800071101108549042a1003031088204060b1034440c0201c50718401d00018030500006482a601c413a01c400c6540a107050b0500c1100000f0f1400c50100e82e0b0701c0104400d50420074440d0060904800710344089403160b8401c40d00a020381d82c0810100310340440800280070f41204412919207000424801c01000540c041c140c807084508110b0540c10100002c011142120740c04140003640 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 90043058 1250 90041808 90041813
    0xb01020601120219050907030c030e030c120306030a0b0117060609151917100b06070c0909080f0307020d08070203090a0e060406080f0f010606020601061b0c090e01020d181e 76
    0x10130005400c0940c000c940c841c00d0000041c1c1640115500b22401d031002e02000a00c6255103503a4065084208600c0d4822a10801c1c0c160130710008607088903000e025144504110745542c03040c1d0400307a01800101207800c103803003103080c024407005030001400c40d854825402c00340d001c068840b0107012468891101a1892400078401c00f4001c00102401c0c0c0c03d840d10f40d4900040503407a005642e201c2c07001a4205000660b080c946682107828031503000311300c00e01c0d060511504000034001900200c80e500410014200d07040b5041d40690300c260304950003010b011030410001080c110010b4818002d42d881032058148681e41c8081c40026174448410136000c0742d03a00d00c00180580400e40c031187e1540548904016609804140d140402074054000d0210503034035401240d66213001d1190b0000039610030f40640307503d00700c00d0500c0d5040d4001c441110880e07031100444400c407801d503015140b45a5000407881052092030140740d00e0040c000b0410d000310200c5440b0781038040c683c820000259040001390008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 90044308 1250 90043058 90043099
    0x60f1509030b07030e0f0319080a0905370213110909010602011b08010e0703110702191a07080703051b0a05030307030609020315010e0105210a0b010206011202 70
    0x85401c0b02209040307042410000d402441d4225601405029114500420b00d4000084070441740c203190f03004103c11107020040f5003104028202010741d689071408800070980400c074281c03040c62500758540d020280c0344208050705070101c0d004c128801000c2e00380341c05665154440307480d918003c13001040034100d0041c4000d0f18030842480351740c04405070b03001090702503055028440c0d4422031000004010703100d000075500141c0910560a01c00650000152000c1c840e8000058030000c003100107040c518541d0004604140d0080d80d05c121119000301000541c41501001007441803030080549454250b4540916a00c076000c00a42403040010311001d03062450380442e5030140c1403005640d0420780d54a0507980784c1d8070a0b581d1000090414a000c41c01003103e208490045900c0c640c0881d100d8421030040d503c4014481e261818050188440d0443e0560b44060280d042401509a2403510f052030541c8101c45074151818115071200c4014402c600c000d03aa5220130a4049403080c071080d51042d40d826 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 90045558 1250 90044308 90044327
    0x20c130902060705030d06050d0c0614090409030f020c010509060d0c0504080a080702130209010c110310020c011e050403020a11040209040903020a0506010608060a171e0a0b060301060f15 82
    0x2c0d0010380010f0030b1001e001000c4007600d81c6c40070501303080c4080c03039071394080100c0c0040814003c0e10901e1341420800042e4090b0000000781c0811120081c10001d10341d0000703048400c201c0040c0c000c111000c0030b400c407003a418014915801b5090820790304142081010a0707042c0603101c3c0816403295102c0c000e0701c4050064040d00c1c01070541000301d6011584500c2d009102d600075104c100d001d07200107031074880814824000e0781c1d03000c0c0701a9181049802e0a80314a01c4034212084200c0d05405503214542c07114030ba5000a00c60300e003200001280700b44250b101000e824400070b04100045107080140b1001a50105030383d80c2e516000301d000c40c4150451030000c3c0c000d01c51501640c0e4040e00d040c1850f41010340106000317440300d00031803d54680380e81c4d40c90250f90b01c4ea011220320368096030380b0009108020440820b84c000f5840202140c04d0b000103480401401e14402c044180a54450202001000301d20170b14103a10440c290000d10039a8500100310322031032507a0040324201d050a038106070b0740f81d00ca0006130 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 90046808 1250 90045558 90045563
    0x20102010b150f0c031e07150b1e0d0206030106021b0303040e010e10090606171b160602040317190504060e0d061b0305010504270803040311251401020c1309 69
    0xc2a02e111110711904258429101200c1480d030710905072890119a1041400050010705902d80b08ae283c10700c5018181031442203075071702000c0444150096114080070f94003808940d00201030740d101c148101c1260302840c0f0703000d51003a0b00030081408403280c103005003811102140700c055815128012650f5284030250000c1c1005464940300051310756100440c003002200048084200d61143c03d40c90007142d440010b64070f03651340308101c1d02c80100074200c241e50403c0d008200040c10142c07a50b944c030401d092031070301d0010314200c0803860240c50054003111002e138004d14103209142610300003015002c0c07400c3c00c4509110790140383c841400c0c04401d40280b207050001c401c05869514054001800400c428050300c0e000c5d0b450b1064140102450300e00304038104a82c1128070007440c9442d55203d6017548014821410030200b405401c800640030400f140c0c82e400039400c3d510180e86a041040c2c03c900199002041e4154024060300f1142d030085529014a801031710209400c060162428000d007103441e400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 90048058 1250 90046808 90046837
    0x20d031818060f0518011e05090901060801230708040f0b0a150f08030d1a030708061f03020f130b060a030f0b091b0703140a030504020102010b150f0c03 67
    0x11802035102030344110140c0320700f181c0b0700b96456142c80600518445010710200c0c0c0e201c04500501100c1c8012061018800c481409580d12a850b2000b2852540303003507614445d01da46403213060110517401e0264244120010030107130b0f11070081181e001101d11001d131044003132040904c041424444459261095550032003c1c1010509203c10420000c4c040fa8140030740c1d00400c004d0110700d20088a40e040102d034a108000d50a0001000e90200100758045455107a000a021301440944042c080003006000f00d80c0070b45018a03111400049210411043c0303283c0101545003400103a03901c410280e0303042000c6d07aa0420b403080c0e640400d03005101c11300f6000d91010003c10820805c9915070403e45c07118588413018440005c202060154900054807140407502c043d200d0b1750381151810f000b40040c9800f03031030050015880144220065484a0174244c0020707100d074208819941c090185064800c015111440c2c902844501c01150b4021404507403250100062a10311340a400c10035588941c071104e94 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 90049308 1250 90048058 90048089
    0x7050c0406031b05011103120612060106020604060e06040c09020a020f060c04050a08010203090a0f080405150403060c020601140f010e0a1502061b040512150405030309100207020d0318 81
    0x2001600b0782c50880308000f22043d42040410380b035121718040071656103500020340c103100141c04620321380d490043c42c41d5003140a0001c0b20326516810403600d070003030501d50040e0856080c2402c08100b540c08960000149500200a000006541e03103000e2048502000d001a00c903404020100e050a0800124500d80d10400d4244000f0071502c000a0040381c104841e03031207250f55210481d500342d02085420a03015001102c0c940003182c800e07281c0e44a49840303400110304d0f01d91948001910405076008064401d50003040510400485200c2c070a00300045000800b070541c50450115140710500503400d004002085040360f007640508030010244e0801818000141d449401084040b10307408201d00041c440c803804251000000618440080000c0f000c1a18041c100014480a00c0707000c10803240c0d0b8403921090032050388010aa01c3c5c00b480c81800a03591b2810329460b924500062081c020785a5417041040000590356040c10a180581c036080080e222424000079400d521071991010068904108 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 90050558 1250 90049308 90049313
    0x3020c01090c170129060c060c0d0c08040b0a0e010603020a0305010203070e100e0907120f0e0c0109050603190617250506120606040b0d140106051204030507050c040603 74
    0x524141c140d800c01e108003882002c40525040c240d40745d602d1000d030040c0707910901c0010050321503004102c1c15030180000340b4140c6150052031901104542d1880b001c540845c0c1640b030001a400b580d201d07080685001072180c20641c40c0c000760200702078011401c4942d1490200b00348103003900704c20000e580050a4a9151f5a6424814040d44c000c55030301c4001880c3c0b8441d04000c0c40e05418051072104a99a003036134003590b81d0280300c1c082e00040c0000d400e000e10132005c10304001035170103007000160b605c20002c1001440c1c0c1c403106190030240c60429050040207030061016444900640f41d10682a403c1c0b045a0041070900e0b00041c01e035504120317280c590400d071822424900103184030205400741381e040841d0f441c41c01c9500b1400030030701400750700c0b0030200160700948540b040e010707400c500020a45450140c0d00d52648015500c40388100309055190022449103d42e14000740e4010861343c02e04a103000e00c1c1a40d0b03516200001003009041c884013182d4141401720401079400200f8025104008850712070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 90051808 1250 90050558 90050573
    0x4050f0a030504030605010509010305030307270303020a0c0602060714071703010e040b1302150306010201060807060c03020c03010b060a12060f0b030402030d0f1e02030c03130816030201120c03020c0109 89
    0x2030001707694450034240001140c0c20880500f40c1200d4101001c5c5007107859140080700c6d03000e1013204004040800851034404014003281b000000c5110b50000c0c4504035991038962540001c4e03034064001d64202c4000c00145a811170b030141c0301000b0218003d5517440301440e201304101745e002c0180f030007054040004645404411000e50060b40103915031038680d690f002e8802c03c44520520020341181d818000b0854200c00c0c0d10146801103414000424007a846920f02e0f460001560b125400007074001c0d01803005c1c16018840345000c07103015402440b51540301c0011842921a544003001080741c2100080c2d003415150384200b0240408100c1014244e5540102d028980c0041d1000e03403190041f4051010340d1800762181207000c01c096200e020008691170489400c0390b801500d8541540010811090011414401014002010003500c8210360800e106589041f421a000501d100d00961040c00541e80007110380410302030207034003c03403190f045500845c041e0041e4005103d0315800c006a400030002407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 90053058 1250 90051808 90051817
    0x7170304050a080d0c20031c030c022107140109030207030c060f0905040e070803070c030b07090303120216050f1c0e1c1a2508070f0804050f0a0305 65
    0x4641d10080183c903004004e48030204000032002140f052218000080e44c00300e0074512044480702000c103405d5081c0e000c03d06000903452101240c4400d0356040700029014450001551001e100034030400111440e140c032200422210400448800709092040041490521a91401c030345c000340900ca40f01c1c500a0756980c81408110f603100d13940c07500400c07190321031154101e4418642d40c1c1c2e051071310b14140621004050030a04450140500500405c0c5071104200030300c24035106a0003006e02600e18180501c030340d200a40458104150136030200f000c20b034000c0440c1041d02e01403d005130b0780c02c141c88007805150780d2040d00800a0203900c8140c0d5030107030081140441590204864034110000030340884007001e40c800015071201140460b28089801c00710036604140c0f0078501ca84018152261644065200300c03948018040e80e140c0710380d0f039031400c00c0c1d1000400a5031b041002032804c0c12100900782c45000303031003101040303002d90000e8140f0108106828000001d2000d41e885064942001842c0303501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 90054308 1250 90053058 90053069
    0xb040308010b0a08070c1509031110050702100e070509160e0418080904020d020f0408010b040903080a0b22152102090a060302040c0306031b030b0c0c07170304 70
    0x3540d0001580566400858610407040d13a00c0051a40d60303840e0660380681643d5050f01d070640c8841c4d0701e000780980c2e8031075600c00318040d0b00d40307080d20f1110a04517440d00c42a0100d50040500b001e09101e80d941d00051039000103034901502180c0341403c3c0215a141006590150b9484400b14040c02001c030300c800c16505400b03600340d85140c800b0700300409010a58000c800c2180040c000400c01e0404120b10303101a00b0340f440020b10240c94481410924001d0344c102c0111614404030004007041042070074410003080107030030350303050011881d944c03009400001c0c02443c003418075484040035030140d6079028403d4034041540ca01844d0384202c0640c02030046c640f45030650740c003510b051800f054080064018003142454442c99a104129075400e01070140c401800c0c061203203444000100050742c65001c0c48803003a09669001480b0391442c10310102c00d0050501500c800813100300e0501c003040003001600d91003203d0704181551041100785543c9010f80542c01a001060072009101005202100400840f403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 90055558 1250 90054308 90054317
    0x20c0d08070f02010501060203092e090503060109090206030a0903030b040c0f090e0c03070509060f04080a060506040905060105090903090a09060f0e070f0f0302160501060614090102060402040f0e07030b0403 91
    0x180240d40c10f80c220b40d003e02034a40564410300061076140741c00050502429a00418181c00c4180c812a0340c20b5586000038a80115005039010700c41c0d82020840e01d1700421000070180000c0d021500428001d10018008040e0a51104e0004051600a4102c0d030b0b00e600d03002c2d01c1001050b86841c00248a900c0c04440380c5e00151802400040c43d4041c100c3c52401100515105031441d182c451081e80d1542c4403800c01a004141031010300b0007005d00d4005840109650000f40c0342c0755825140000860f040101400e1003586445054000b10350001002d0381500c2c002d9800780700b1a1602c0c450140f8501484000c10b9021501d2b11b0042141d018603004041100c104807147d0254139164841c41c0e181c074008075604000180c040c1c00024219105101600d0a88040d0800500d030840c3e254540070000f91151054603503a448038001c110007030f403100700b0000d80150110110300305140c07540000d46a44018102030702c56511a000e400c0080144d902c13900c800d540e0007086030b0318240d580c0b502034100c1108882c10780114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 90056808 1250 90055558 90055577
    0x5061e03190b010527010c0222050a0624090b0d090b0105010c0302190c0509070f020706050415031a03011803020610060819060e01090605040f0b0901051201020c0d0807 74
    0xd50044d4291403190000c601841440e003200c100110f08034030030001c014100102103d4800142c0c0768210142004080100500d10302030781d0304150800e46d07a02508034882686040400c0017007851042c000a11040e900c0d25981c2d02e02001c00c411141c04240d600810b982520014000d5004411a4072032400d06108410081c1180c0c0d03204015218840e01d00800b5015820001d5028020455450380c04200d52040040140c0ca44e01c03240407900003081114210b010170f0728860460b0145804102d860010320961400d0783c5000d007800f4452142003820b68450b0709068031510007540c001c410341c0c02480c501c04060001c1005034024030700b201e145181e001c819000f601070580450482056a02a00d003607031803d81300c4040d66154210320f10700d200c1807003d4501e650f544c3e588020482403508d030000c500a0004c62070101e5558240401c10080390301403001c111803207141c01030907901601d0b41c0800c0b90441d00100c4d501050310000d0520180607101da0a0041c02c04c1c0906101291b9103500030000700e0080c0c2d03540c0d40f0034028 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 90058058 1250 90056808 90056831
    0x20408210414090717070305041a010f060509010507290705040f0b0705190606080c06070c05010c05120703031e0e0a06020a02070806010e07111605061e0319 69
    0xd100d64014401400850840c0b1600741c201504030075003048113031424410242e460219148505030640784c480002e40c50303505010612103909002d0f681d8081c514500b0b4055450301941c5010003886125800c04e11001045128150b03000343d055840b1580c2000c118115508001040c805a00c0003900149540d540c3c10040303a207491141080c5c4e03080d54100a6407024a5050504800c45500704030800c4a0070b01c14000c0e0768608000800f0b0b64501d10b44a884085040c0d414110982c2c200580282010b021300c00a10803000420040c5080703c0c21640c0a0070720340285825800d003941007040c004040c40d00c8100c00555038081550541c85100b10110003c001c031034407240a0048025100c1801c481d00c5294030900c1c0d0f0802207001e0394001c1841c59407600403102c584e5039824419091510982c4009261302e0080d007000307000b80d04045001907070689600030303015061b2920001401207440e800b503140102400300d840f209440519080500001c01d040003030342c0300e00e00400090018142c0c6071140904178204400c1010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 90059308 1250 90058058 90058123
    0x1302130c081315020f0702061201080f010902010507110a2303010c11032704090f05120406090303180e0117010c0206130206090d08070b09060708070c03050a0909020408 74
    0x41d00d07405400001006009007010f40650440b4540d40aa014100b2118005075a807034014111501111440d0029615058900b41040c0d17203070b005144164107000301200142e07800001c4a0200c1d0b4005414141c2610302000b04502e140b9542224000c05940025090007180b0031001e848241c10450003402529014942151712201000f105001c50348213104405400740f0803940580c0c40d0007050b440c2109801d1601c00076007511a507020903507181604c100c540c420f10805115080188601148075450549000c0c03008080c0d250714400070341086024005039041e1006032607800000d050340c556a0b030303880d40c4902070105404102108605036610f0420440815800805e0051042c1d144002004040c1c0454091004590141010036401078210302d502000900b030501400d0b0090090600c104035203020250145003900c00f5000c0303410b01042c52f08000d84590302400b04600b103039044c54000d40390440721805039080403041c1c21814040d030011802192881000038400b0b55500c7c048c1000314100c601da070920a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 90060558 1250 90059308 90059341
    0x403120c08030106030e0a150212010504020702030d0c0807060c0305061810060c0c0905011e08010207081c0207120e1e060405010c08070c030b060907050a08040201081302130c08 78
    0x51003a0341c01d100402806019170701008a2001c04130641d040f0000795a0f0300100304080300c5183c40341075804190b0119154030503030f08a02401064408500d003240070f4001aaa40080442c1401041101004039041041c05001d5540d02d6901ca44140070207003400201501170003044035024020301441c00703900c1c4d54201050005e40038202461075000303198104002290b00c80369120080e03036502c080031800640d07a000361094500030100780469402c1c01144c429800d200300520f40c0b080c2d03071aa0042c080070000c00d00380021036400c0c45c802c030300e02a0706100c0c4014800180c01003170b0f00030f4443e00401c1e000c1c0300b5a503007202616031200c4040f94446070060208460404040700c41e26040c0c0c00c21340600c0188055401801c03642c1201d402a01500d090050903036600222034601d40040300c1444800c000d211440c2050014242c00c11500c1c10403034100990702c180146588802040641000316038000b01d90107029241414241d10b030040c0c5080103620021000c6005030522b00301003000200c040d0009040b80c90245100c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 90061808 1250 90060558 90060563
    0x30f04120503061e0105040b0304050706140703080a0b010e030f1b0a030b04020907030603050d03020a09060503070804110f03070306020903061008030304140709050702010b040e0c0a030b1b0f0403120c 88
    0x84228040380031204d50442d07010065036040c4001040302040590465024520540c8a5001010102d0604000403c404044400c98039a0181403000c0d400007500040010350110000d00001200c0c4400401242c0c4012902003813901809072103080362000300041162400b03900c0c0c0b000c80c0c58004518909200d102012840007a0203a110a0085030042c07510342d540b190000010314021520f15220b403a0b0a040007041c40d803400200f41e00081441101d41c118041d10002e1545040ca142103140807130000d458050002c0c00101803a00c01d00c08040c0e6a50f46000d044500e140c09404c98036165103d04d4000025804014a03a110340704040000305250002c442d0001a144418003a50542c0c440d55100d02004940d51840c040e20700074900041003001491250034859484d507030012440201a4045c04111100014010102d4100c84a0203540e03840303150345001100e0340f10350903981d21364500411b40c85070300654040a0b08400c00043c030000d0000e101c0081c1090300c1c007510400c02c0a411030709007614800c4886200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 90063058 1250 90061808 90061819
    0x605011d04021c051f0501081005010513090203010602030d180809011d030a03090303030510080309010e0f030a0303090c0602030406020d030906150305010507020708010506130903020a08030f0412050306 89
    0x4009541400d401070104401982d104070b075910030f403c2c5035006844044800480840122000301100b441a011100081c103080c241022181400c2000075821704e01e83c003c044c144400041c941c0c19003914001c1c401c1c001d081d40c0408545a584031040251a5070103241140000c0c0e04100c80752690140d4490103020707050f84598050700c0c00c0750040054644012003114000502104010868191018000326250a100755039150700b00741946005412030b071000d440c0c40b041021609061242d01c0000003103031044c1d80c003404d00070030b001c03841c0380000c02c8000700e07500c0141c160007054211020990107030001400c0701e11818242d050f5944076171040b41e6070b000f907201d001c0040e800012030743c0c8024002e40c840d04807039000d80d030b011405000ca10303049940b112440e4801c60707080c0e40d98003c002d01a603050080340c010f01540b60003400346042540008043d8003450b0450007a96540d07540250425000b0041c01a889902c00101034491600c00b03140c00c100007007143c045c1d8000c5030080030203031050b100f2401c42c0e00c1010002d04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 90064308 1250 90063058 90063107
    0x30909070305060a0f030308190b0d0209060411040e01051008070c020d08070b090c01120b060403230f030a03050601050f031605042d060804150c0c060c0503070201060501 75
    0x8110701070903000d0f02203500142640300200301c040b04061030700e0146019407225040e41c241180c21260b040703905100c55900601d00b03100c0300c0d401d030383d014180d1400303540446680b00591204c0000400410b04000381e0301003110700050000d50109062000790403240203d0342030003144510802500d01c480d0881d46400061380e001540c000501e000094046000c1c005c107010b500f0140f9540d02c02a400304203482855030796005841003c510340e80b0480d40340d842402c80c1c034184007015120022070150701603404020310001075034100d2900a04c11030310425490017958102e0b5800e0b1501c641c0d154807a4800000140040e05040000d6510b5000c1c3d411616001c00d045406403455540d80320300c80c6442d40c100190410048100310010b4980100600c0c0240a231440741ca42c0e0611149038030f0203040c080e85500640500c4080307001c1001003140903030020003594141d1008150100540c13001c0302c83c64407000000301810301d400d240c20005903000c0702031032140c055a0000c004481e142e100643d0120319010280040380071406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 90065558 1250 90064308 90064321
    0xc03040b0307030204270f150b220303050703031113062615031902060702060705011509020415020a051011070b0c120c0a080f040503120109060611030909 68
    0x4006542c0425035103001030409450f141c086555903c3ca81209a40c081c407010b000d020a0841c1c440c140300c07d1220007003017042c0e4190b81e600c2e80c1d10501c0751069611104000c0341c10304c2020b100d070081c0c048a070254800b055945071685006460b9400586040d40080d18001030701003020401d0f011590b0010112200c54030481c502941250030781c099220900b0b0141c00490740c0c0180240b80c4d086180558485c25030b07540c00303559107414107140211441c02d41d050741c4102d110502c05a01c8500469003041e40554248da943c1d0b03043c1c14480d024048403e9070f48091014604d00141c8614039501400503903400d01c440d8680b8034422a801c980d52400118080c0c20394120010100e105001da6210b4024854a10100f5040c2229900c03404000c2100b22491401d009000600300b078040d801100507684100b15456080c00c1500280005000090082900792960580b4010505100c8200160307034105d01520350300c10b038968507892140e016003c288500004140781444000840e070303001c0180c407261140601110480e03175481 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 90066808 1250 90065558 90065579
    0x7051002120117031207020304090e01020403081e040e0112060b0d111909180b06060a08040b04020117040615060e0d12110a050c03100b0d030c020103020c0d170603030c0304 76
    0x40c43c20b403410302c410001000a04001c01c50b2502ca04c06540181d500e442c174102c0e66000345e0395480a00045039204110600004d28540e050b81c0300703031083d03242488030310342c030440704c90f2882c8101d41142c8452201e00000288900156038400030301413140f14144403039480320050020704040400c00908041c444412040c19090001d18401021071402c00202e20303964a51600003140c8a14010440c0307a07070b8281900c000e000400389a590890350548003589002d03802403004003c804041c1005011070024400314041da03200300c08a000d0400120540790b030304d00345840c00000608044a5a01d5070481c80400080c40c98007801c8a1030b0500e40c06082c00b0f118510b0341d550400c40781541e980d41410701401010010701c82030704000a07020644102c0c0244140403510042501e01641c12400e000f02c1070404080c03a5007620b906103440c4459038542040b4a082c5000c0c0700680283c00781001c0c50400c0d124074a5001e0056a0080c0481c60b8103049000b411541d4898a05040d1288980d08580140da80204020802c21190 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 90068058 1250 90066808 90066839
    0x504020f0904151a0a0b03100f0509070e040f0513050c04050106050d0902190602060a050f070e040f24050103060e060901030f1b0603020c0d02010c021c120204060203070510021201 79
    0x383c0030041801504c0d000010800011a086403015100110803c0b40c0742041010550250021a00722002d40c0d203003000184000c42c2c024508010042c101542003400d03216504591a0142031b0f1500784000d00d08004003030043c44a503c015203132841038104034203c6003441d101d81c0c1e0603101d0580e201440c200745140204080c140b0b041080760003240440b9003c1480c40c010502e400a0035103076024103047c2c03d203507640c2d03000d45401800c540c0d20700360780d1020700900c941c12800c0c1c1d1042d4002503c0203d0b00107014003002e0024100041030700b03191400700000345406540da88802d0180c803400d072000c01c0229152408640705480803607146820000c1040184003058007440c1800c121445034200086060120100480712950340c2d11082c08a5008959824100c0052180801c5402c03288020016907140c40d03c02540c3e00c619420340d48402001e68140e61005108062445002c0c01900d410741da12565560025500e602c003440589803400350b0510f02c038007408240210b500c0303103a828070120030507401c11810880210b00f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 90069308 1250 90068058 90068081
    0xb100e09130206040e01060f27090504030203221a070206090d02120a0602071a060307090203070311041202031203041101030b120f0604020306010803040605030a051302090a0504020f090415 83
    0x381840001085d00c1c4001c039036400380034142c0d543c4042c01d11044000d002c014200410304405100d80b102e0303440114100704104101c69180c000824036444908041c0e0440c030840390142c2c540e51020150850054001001c20f04a41444520040e05c0303104002c015100d00641c140254022001c0001c50b070f42c3d1904030b42c0041403500003040400001e4004d0300c4c0d00e2522a0300182240c1580e00450340c4428840301c800d6070380c644605140ca032407062602da0f002a4641445000745000346601101282c0403a01c2684543c18030b0340d980e040c1550ba19180e110a48450107084400ca100c1d1084604100e12403850100396801150b006624000d1701203441c0c010f60151034003540321030b013020708014950b40703240041020410040042e0090012070420740140340c102081600080c0d41c903481004104240c903400707003c495100340e0f202c50029071500c031102c42801c84509001c0c043d50114001d070a2108048850340001d00480c8200d5803000700c0c00c415010b11100301400c03900505400f41e50341c0c4544902c0c8454121792128003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 90070558 1250 90069308 90069319
    0x150a0207030213180605011503050106080a0507020c0307030506011a0901020d03050705070204060902030411040b01050702040911030d021005060f0f0f0409170a14041a07050115090b100e091302 85
    0x150720b035814050341e0804001707031500c1d501c440040060140c038907640706002c83c20303203818451903040050191101c000a0001c1900c00e5540b000100003600c2480403051582c0c00405842c4e809542c1d081681d036840003030044103d03584c0c002d003c4450300f0090030115200000103802800c0d5200081c2d5003640240390042c241d0f42841800c100020040e543e034070829016200030703e0016101c1c18141041050032010002543c05140f4050145181d6038011090321005541214081410b08884c9002507040074846051390301403045144101d020780e0003007070500000c0c0c03240900300103954810040040183c10f0b15990f03500712802007210701c11030070107148064510101810201e0030550b00d0f91000e01100701100d11105481000c00ea80700000c2e4030412030701d0201801507141d810103081c924050600c6400c001c010155110000302d9008001d0290445040d0440300000c002123542d03900b05544c080e01d01d0750f03100b510450341c2c11a601c2c2d00c0f90144c4292140d0000141075140107544080c09190100c100407004c1c3d0380035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 90071808 1250 90070558 90070571
    0x1e050403020703030c1b060c0605070e06030622020a08010e07090302060a050f07140601050316030503030c1608030702011407030e10150506070c06030e030c0d05070f060515150a0207030213 83
    0x3000c03540446d100410fa07558076049a8055828100d04507440a0054400c00c018441e616a056891409480d004a42101c8001c503513000d0704919004423681840200400f40040f81e801015508182c100d0304860301c03101c01c3c6206564000c011155002c407800000c0d8021010b100503c085486400500680c40c13803440d106251180a880c1c80d034807032000380201c10040d0302c020010b000c1c5007410f124070b0103444400c1220130051030070360f0741d4145c1701c0c080241090060940428000001031076000680ba4554000080316924100600001d010b41921680720b0030f061000c00104108910034803c07a00c80040300400340c485e01564500701c0000d841c4c4401d8a00e090f540004010442e40d5950300100300c00c5225002c04501c09107080c001505940340048074010640050044000d0700c01e0104580c5091001890800c0d0b071844a41342051036010b41241c0079000070310700400c01051210b091190703030041c030040360001c191200340002600315202e011611001030700501001c1005041002001001080c00b41010660 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 90073058 1250 90071808 90071843
    0x506070f090b030a0f060b0406091403120301080a030206060607020315040305190315080a0c06030902060f0414030f1606080901020c0607020d1803030e010503060a080d02011e050403020703030c 85
    0x460f001500d440c00c0e110f680e4034199010580c1441800005c142100046007400d1828001501500b0b0b684140f030745039043c40c2d07000c0301140c1d001d0040b10544204000ea02e52a540c607100000d641d4425540201d001d4031a1703201181180c50000b09441130154010001c105442e52554401d4a070b1001070012020720206000009680c1500c5031003d943c0394007994001142594048003904c140002d5000307158580045043d0310110303100045407426210300e03040102d401900fa1000c20403074400c45a02c0d11484074003080208000d21a03203003c0c560b5001c110204c45211714003090f07054803402c1011455880155115040000c0740c003070001f0561081d0780c40e0005062280662406003402d01c1290204016000010603000c07943c1c0000070800c0b501c1a00b02c10117181811550041c00a0100e04501810b2000210004a4681e20300d4a0840034144010585000c5080d00701c0281c007815641c0495052641c1f0b085000300e441e540c42c4521841560158000d00603103245440641d40512a10f000703843c0001c14009403901d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 90074308 1250 90073058 90073079
    0x9050f0112021003090b1303090506040e0f150a030b010618050303030612010e0105160801090903020607050702041d0313120b06041d01060602071a0307021b01050715020705010501050d0506070f09 86
    0x2c07c4180000e0f5088021052600628208c840d4000364881c1c0018401805462810920b00e0f40c0141c8261740c00000c0d07100e01c2005444e03100440001c076804402518040b0420205c50300c0603040303480944640a40014000801108003030301d000d40ca40590007440011a98640a042445148407a9000150090301c440d04c190941d0421208540e07035002c801d4006200b21b0748441c00500410071480304020850740f17503134001e4075010003070302140030400d0109080d1f00703550315036204500000c40c9540f001d941610508101c3e449401c0180d00c0100c4503072a0000048007003d140f09802c469500044652180c0c0d42c040412000b00313141e00c5e828000b841c01c0f410031203207690309220321000751489800401090f0326202d8490041d0001000d00700500d407040c4103021121760001030700b8011180e0440c1c4404070058034001203c813400b841c100544210002e01e62201411001c0d402002c1e414080c0009008503030b2038806100c845020039000400e2036000301e001503e484d1050381a0000c42d001c628210101550b2001100c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 90075558 1250 90074308 90074311
    0x91806190906030b0c1201120c080d09060e0102010b0f06070602040e01120203060a06030201021c050d0c05071401051003031407080a020c040b15070303020f0d05090709050f0112021003090b 83
    0x244650b41d561030520600001ca05030551008010294500d440420742c0120308415040c071600400c0b50b6640211410004682224006800d801003100c0703025044480007400b050080c491007010403442c8003e0000b9510600618141000141101d0100300c640024041c2c1c0d076228100030790303c1a0b400c1c8004135800601e001c8182c0208510a07100201c1c852900415040501c06003590160510f0a6002c0006076000b08038034041c50303015040c400e440044c1e6402640d50344585076480e00b50074030b403403080415280c00c5000b4080c01c41c003540e0040202c6401801e15801c8880990384d04410b10301d038420820000348180000990501d50302e1440f4244190740c0c0d107100c80ca421507036240e8007503080046203c455003400d00c90107801c800c08841e0b10708c11000354030807041684107800d405020150001920800e960344002154060900260b08129903e003c049590701c44201d40501c650440c2880045200001409442d078186c41d41c0c1840060072441607420400c803c0341082c008030615854082600100d0000171405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 90076808 1250 90075558 90075569
    0x1e040503010908030901050a0203190504030c14070303170903041e030503070609031b21020a02030a0f02030f1f0b030c1018081b012609010218040209180619 69
    0xc2e840317060000007942540d100410091826105100300199516038240c42a10a4203076200080c10b074589050440f80c00d01c1d03411019007480c1c00540a440e030407800141d4201124066a20240910020360001c0c40c403d10a40398086668424801880746e00c02080e58a40111460109650010b659076245800c1d0381010005030f0b040c0d40d43d80009000e154015481c0d0801d0500c140b0000a6418507503034000c4101e44194100c1410100c2000900c0710074001c101080c0c0494008045402800840c80c1010018100c24422030090184a044d0349540c42c0010f481454009100110310500c0d90601d0307038800802915440710742c07500c11a80c40b01d1941e112f0200e441c42c02c004940ea95021000700305146100501642d00240856001380c0482074070b6100203400032100c9500340381010701c400f24580c2c2c5032610114944001100c500d0718051118140c415070041181d90420300b2901d070280301e24030800c4101c1c002c5c140001e8002c001c51304036612000301d03501c54030750003100204226901400d56010031025442034004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 90078058 1250 90076808 90076823
    0xf05010501030e0c01170a0e01021c0b0607030206040b07031113060f02150a02070c080d0203131d0a0f0f02070614010503120d11040b0a0f030b151e0405030109 70
    0x140311959250264801c684a4900144200a45040000c140903c0150350702c80c0c216aa2021501c0204175405c007a120440102c000d64440c1461009001441011038a96840c50f01e17103d115a99420544151885503426402800060340e9a4650100ca204018254810141d1b00c10610311051551805800243d55001c2d10480c03180c00c0080281c80815120040020355010401004515080c060030543c020a800c10142c0c6810080c58404000f4459800c07103206030081002c4114544c1d400000751030032500740d03580c0a40e01c3c0d544406d600c800e002c071603616a495414440000d046100b1640003003181d40000c00340001e5511480c03904e20200e0300700d050100c503181e80b1a144038099845444c40c9030302600c0100c0107400c2c0c51280d030541345110303c14810301032401511802071105244541081c1e400078029540c055a80d0342042000400c030451800c40c0034086807600488041c9400c01090003c8840036084803240380244880c411095515941e8100300c1c11407041002146589080c05004060f51080c0d81 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 90079308 1250 90078058 90078061
    0xf04060e1216171e09040609060803130504050c07060504030e100e091b070f15061706071d01050d060f06020109150b0a0614120108070914060f1009090f05 68
    0x10030101000c030300800700c90b042c8011300940c0621070324501108400c9041019041e5110145030106024120340d6000844030303440c0c15000200541e02200400c003c61001c40b0600b4090345400410007201c1d000d94926031042c0040c0485000990680c0c05150090701904210b0420750a0100248401154881000004c0c51050380101e4a0502c410981e82000c04001030a0140000c0c1814841c14040c0383c401602c20720010119106010200003121140c200c44541803014a0300c036040e044802c0700400301070041d44181c0000540142c8109030040340070f5008501010030341080001100d1903000490400c00700b541e2540e00041192000540c44024030f002c2d0004100d07130280d414104906006450700e8105c01c2c1c100800101c1640c0d45201c0a030540c1c400d420302d100c580c441505848103501032003400b10451822140007041082c40090090100c9002c900188041c0b048486121440e00c025122140c0000c185400356905250460300c9815802a43c904002c0d41a51074072004140d0711b2130300b0314900240e503035070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 90080558 1250 90079308 90079313
    0x110d0c081c03050603190c03080c010b010e061206091f090c02060f010b03160e0d0f0507060e1c1113150b0c030703030b12030406090504140f04060e1216 67
    0x10040c030080030b401c04100a180510100b034944104070000c0c40c2c0603001e000e85004111107804050090368008182c44c4d00c03044003040c0c003802090f1070900c0c240485c0d00703003450040d5450280c049a08250381e0070490592500d450061240c008005029010389526840f40f550358018860400001407180900105010304074070000380c1000307000f4025200400b1701c04010f00c1410895030072290002e40060540d00c0d81c0d0b10601c0b00320707000b010083c02036034011501010001070191109031246803501070350580b40c0c45a511701060701d10030b0000b07040a42202e40f40e1806001e0201d41c6a262000b47e002d99a00521f44c41030303900083c40280c1d14007002e80c2580d510256950000707042aa030740090400c10315144e00c0d26851001c520b07130300e00402c03000604042c4c4407a03038042c107500c0d0448c140d09182c54010840f80c40b0783d02c0300c0c4054865110b82c00740741e001700c0c03409465108041d000e2100e180030b0750030034030201c1603625261550400741c020072a068190f40701e01044140980503800052642240d0100d00b183c5010161 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 90081808 1250 90080558 90080593
    0x91107021c02100819140a0c02010209010c110301112101080105010e0c090a080303010f03150504080a050a05130b0703020f0f030306040b03070b0409020910050f0304110d0c08 77
    0x358250701085003491040001603d890660810100c003a003082d800b25600e0481c4040150f01454070a501079040c0328240740d0042507040e029002d040041c20074429403040d104200e08074000c02201e0350015501180d2000405c21030b00741c0a10504025001244001c0f4030200c01c03c20380d000c040088400304050f191040a8199807030710a026103400790003408a540b4240d9108060580a0045548c200001401a50640d15002108002c04809082da43c81c3e694890119956000601c002d40b1044094009440b80d60418030907148101d070302114142c01c04003d4030081752a600b000781030390240001007240c03500610072455450010020380e00c3c11542c6c2c92103442d000b410017011900d80b00346179200c4140342039061300102c1a26802139082d600003c0016090000030b1400c0090350042d81550400280411202d00540080072070440c25203040d0f42ca0351b01c1c1113040303440344100c00e00c007e034000e400d0010800050500b00a0f42c11110010040048220790391a10082c02003c0c0d0302201e1154050200c988070504103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 90083058 1250 90081808 90081829
    0x2012a0f090312030b0303090d080a09051912330606031e02030705120405011b0c0c0614040312090303082215020c062409070e09040c09110702 63
    0x22441e20159451840d5150b07900c014211100c903060548030400d054803034030200191100030344001c09504c42c086031410400e95541c03102c01c2800018002074000700d15418075407034100c00450a601105401c0c0d1800c1e001580c10302062400701c8480c4c0048251034003648618401d81121a035100d14614000c405810420840350254428402e050900312118196a4184078207142d0103c00e4002590b00d6a410300c0884030341c070a4150b080c0365107800344240402e1110540c0001e0365454030071729407861321416520944a010041c0c4000f40901d20804051000602c507201c2c0d030404500c0e030f0014a081649030382d00c0415810002c2e0b58840042c109540800a056201010302d400c40b0590100501c58401c1401803100c506e400900681541d0500d0038101310000141c0c1124100300382030f0b040d20498140304242c807048460015248481440d0b101c03640c1081e00c0c0200c42240a12a81d44860307507001c45890912882d090f0080054600040d06000001c00b64002d004128500030401c02c0155211400c1c03040100c030b40321 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 90084308 1250 90083058 90083087
    0x905011d16030b031207120c020d0f03020705060a03140105040204050607030e060d0615080703020306060403030813051b0111010b18040f020303040e0603010b030a111002012a 77
    0x49454600c0382105200510307800510200d4551a4941e8059060700030709a5200e4481c0c25214010301c145008030030782c0151548a00c5104402c0450a003500222981441541c010703601c0444101c0c120001941c141d44900002c0c402e0055071425075031900010900d42000303c01401082c0c80301880c1c1c00a80044060a014000c100c40460601c2d00b03100204529001c0d40b40024203100021130110001d58030b04050340e40001078010b0500115440f181c8400c98800d064840c4004a1514400b2034801030284c02034a205c1c10300038040ca4203051650b1411a0040c1d00a88420a20311400da4080041582401076a8040c1c2281c0c0034608030002a05c00100218001d9056003038a0340340c8a80c0154030b81d11514407030110030f40c1a0201c1c0071601d80e403d10040400c5010002581f41c400003d00090001030040301a100f20760850080040750032100605840d6894070400500802001620341c50750301d48204418804007452000145c1e4803840d03800c560190700000e1408414403040d184d04481941d00c034a010f40a00c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 90085558 1250 90084308 90084329
    0x6060314060603060c090d060b040905010b0907030212130305070b15030d05070503070b090f030408100b040203040213020a030e06040b0105030d1d040519091b0b04051c05030705070b0301090501 85
    0x941010fa1041c036018480710544a11f00c400d030101c081c0b181e40d0700242c03003a500c02881080154041e1030b0490081c0f40e01181180100d04110024041e28024800c2d5060708102d00c030450100c0d581d02c080c0682040c9003407021000e00c0424008500402e0910807458800d03224003206070450b04200d020580b404030202c40301c00c20007030100114800140044140c40c0b159a03c03111000880c3c485403910340c201180e040444a06110200740042c040c0d0b00001c1138040d03124007403020450448081c09100076440101c8029410880b254101c10001003598001c0550708540d26000411009150705542025000e98080e14050a05401440300e86802e0091001c1040c0e6070600c00610b422042c1000c0d00480c021b81031610590390703500080c4081c6600710140c4202d000d4400b0402001e00b440ca0034280c00002c030740c40941c51381c101c1000400c24034809400c407019500001c00720f06010307003000c90044a06000440481e401d001c24010000062020400324001d4407407040fa240d00c079810114440101e0344168854802030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 90086808 1250 90085558 90085561
    0x5060307061704030207050603040605040b060a06020a0b091002070c0e09010203040b0420060d050f0106050a022a0d080705010c1b02060702210a021302040302030601061b0606031406060306 83
    0x1d0700424085000b100905a40800307a0f55400c0a0703040031507070b910040e0005000070803c020485180d11183c8618840c102c21501d640310801803010030b000a009900250748403801e16804144c40c2401d03180e20101c2c030412101201c8000d1442c4040e40c001c99000c4032043d0f2400410301c01d480c8003400040d0302100c444021410362034a0707110b500210002034809883e40b04c17040c0d480715034440d06030044104600080c1c12030f590f07903041c0848000206011a044905101c41d0740c008590503101e402240d8010b17070140e004000441506900c040d212504011161016012100300811501d5083c40310001d103004800182c1c0f20b91013410541d007554100c1010300208800505015000c07aa6082803011150301954a207803500303210310224810910f00303615a901d0340311140c1d40e00e81405000603403543d203510035900c00080807030700c6042c0005e0340501d000080d0300d6084000180102c038031400100c21012004003503001b40070260b84409044403101d4005480c041c02148008000c060b080210725005a000c0d0001c00c185d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 90088058 1250 90086808 90086819
    0x1020703050906030c04091401051206010f060e0402040302040e030c06010608041e050c040509061501030603050601060c0305041a130b09030607050306040204081606020d0212090609040908070c080105060307 91
    0x140700c0c1c0ca40b69440f441c004404100420b05c00d5090364043c200402040000560440402c0141c1409100e920b215200020140d440007202282d0141250b89904000f80c0030741c1003070401ea40c200c1b40c0b0210950881d81c00d01002025a603507008020031000070f02c01555079018200e00c0542007100503004070b02484013900c180400203a00d2a03481a101c0241c2c1a414010708281c80c0550800001d100e0302503000d42460180004081c011481e0342c001d0b000d03450094260580e040c010f5058406c1d0b1f100251417904140d00400c26540940c4c000c04034213200f0b107411890983ca03400c0c7c41c1c4401c0b10848542e80703510030100782c0b403400d074181100e003402410610380c18030b003000b01c0c41c000660b0b0340400a004100f01312002c00070480720b40382c40d0151406012488242c6014214025442d1101c1e000c1c4e1007a01d0040c466046882030880c0082080a0042100c0200d28070b005003044c20f0040e198031030040542c0040d41c41111710041410701000e003880c244a2082a5640352a020700203007501c00240000e4404d40010004014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 90089308 1250 90088058 90088067
    0xa03020d030f090b040c050a0909080412020d0b07030501140a080303060d140307051c0302281e0804021212070b060d0c080d0210061401030905070f0602030a090801020703 75
    0x4044155180105400b60031000c4640901142500141419281c6080c4401c1040c612005030a90b4010384d4402022695060500d00f61040000d0181c43c06508000510241c003081d040d40c00000e0002c0d2030344110844c241c2d28000c04800449010f40025074507001403260041c03c45080142e00811610200c065040c24034043e16480043c0085204544801c1d4600170018180072034510080380c1c0040e00c1e00ca6202e41000c5440e26440324021101a94030482d214159009100b40c41d80d5921418414042000103d80d6088510122071120705214050100d260011906440444c445103556a811000e040c180b041c45440f140900a1a004c0d402c00440018220044016280c02580000d05c8660310340360040403540c1c00d000e0040c0a04004504a800305040c03070001060121921954200d5018081c0748100000b00c07500360149000505001c01d42e12502d61082d000140c03030500440c26151003654032020202d030701000d1750052001d6040841c0d030003441c903000141200104241c400a42c48c1c1001590010f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 90090558 1250 90089308 90089323
    0x2121005011a18010e041b030f05010b0906030a0f05100312020604030e01030f0216030224010b04060804050c0d030801060201060b040807030206160606140405060f0102060a0528020c0c01020a0302 86
    0x50040b005861100f5a0301c44c490f45410900080c10422070456500801041001003104180c0845d0400340051107410b514460141210f90801d501c904018030182004a6680302402d40c800d0291540c000010119907440340500800364514401e200c9450740c90030310010b40140e40c1900c10b54118208200200350440c030a44600e080034038000611a000441400c000c4c01405a1091090132458003c010142c0000d01c09608810910305a24201d030f102c0c04004030036509008442c01904248000c10019008100094115206100351041400071401080428070343c150194000703082d0400401c080c030b4080c818503014010000c44c4a180506024103a60b0303502091000070300520340000c0c07032400014000d18403034885c0d510504c1400f441d561071507030a80b0710250307000503840f8515081c041816882c0850020400c440306802504aa6a901d400760008000041c581450140465881390366070b1039030b45440ca03416881d10f10058554181601151a090401d00201e066600203070204011a0b000a40d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 90091808 1250 90090558 90090577
    0x110613030c09021e070b0a0e12030411123c01022106101e11120304050714030604030309140d051902010501030807060e010f050903070302060601020d090b0f0702121005011a 76
    0x208448c0c48080e515440c0c031641c1941e0031034904000c01400108110381441f5101355170708460303002105101c01300d40c40c1ca815481d02d4aa540da802c8182014445000d06140820303400e00080060051500781c24503800c7ea80040c0483c550707180c003405450517401481d2005034014106441c20030002c0c07401000585070307010340241c2d0400b00404500e1844000d1049104403503800030314040c1c540e41041c00810403802e8100b6902240c03075004101c00480e0405e40d00b400310700c1c503110040c01071072240c0b92a142074000340007180c02034844030410107505501d60820006c280c0403410035510705036141341c1000d04a40c140b076859444021a4102001003001c40d58035810342c0c070382030b0300b0060025040d081440000d006102c03081101190302d040108010383c036440032001d0580310340690256100c5946031401242c07280c0d100c5450b803011034034103002448480c202c02d019103042d50248c051a031505c9119000a40341c078101d2014849107611480321403640c005140286801840d044090000c000c02c2411140701074000c20800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 90093058 1250 90091808 90091811
    0x1050307030b06031e0a1103031c0b010908030a021b100203070b19050c030429010b090a030203060103080310090e030f0342090103110613030c09021e070b0a 69
    0x10816550713051100100804100343c5140c5c45200d080c5080c0d8a070268028151501115550554001c2c240401220340d036450354102d6140000d4030310120401171020110031410031003100b0b0081440c1f80100024a00702e1010b400a224007202d10b004007002c4060311a015000b4000b5400070340c0066000010703607440c0c544c440d6591005688081000070132030540008100b00304d04000c2880780c0002507200950003107019400e003441c084c652604c002e4000c404d12006001500f0803100400108032190041c0c4944c0c64003c24642805603241c0009150207000e80040c1d43c80c4a0001c280305803007800380103420041002e04814490120010307290f03070301c0e40501d92100d80070804c0000003490f120444032030810545c081000d01d503005080032491041d081d01f44030503130280400b810300301000c51400c0b54085049a501501482c0e48600250510940740c1200309900950104040040001031240e82031001804400c1c0d0b00503210390024034044103c0c00e00d5030b132009007004204a07a8010800c11403a20b035015548420 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 90094308 1250 90093058 90093061
    0x10e070b0702010c120306060f020610050f060408100209100809030d0f0b0d0308071d0f0424060e030105010905070e12030405120304091103070f030c020304050d1a0a0501050307030b 80
    0x683c1d0b50740c40110001c24101c070084091700f0058041e8095070581e03070b05580d03036800340c415060143d07524101039620100343c40c000c1000304418031f004968166038960103825282080c0e81c0e05075840c80c00641c1b2074030380071032a008600c1080e5070518481c17110000d240d62400c0132050809401c1d551320703032040213a00b203115520707801203084070001e9400c101030014001d02410b10720f03032083c10001c04142040d9803410000d1b525040b020340c4a501c01d0340031100d08800030113100000c948101008003c0c0005840e60060140f4403031112a6144a060b00100402898a0707400c085c0040380209403c59005070080c99100b80340c07405000302c00350b00030f9414518090940f003a1044034100900c203481c60007160700c2540d11a40c00f144807005c1c3c0e0808400303041200c050605c140030795905c00f00e04101c240011528100052111440d0801c3d0b0b40c420f8004107000452401642d103400c1d110400328142c00483c203010b84040d440c000b04400101540300d9020b40c0101a401c00700419410314001903210b9509210213401c5940303000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 90095558 1250 90094308 90094313
    0x60702070b030f070315060507150608070612140702060a1104180c02120f0d0b0904111009031707050c0a0b040513180b0420030a0b070c060507090512010e070b07 71
    0x6d20060143e0111804003141566401000300326600c44181110070120342103c1c0740c1c40d05081d0140c142a0b131a14400341c100d00341480c0c021600081807021900600e5140d0618080011604484502465141c0c6c0034086078500704040400340c451100308445009000c0204101d901440c01103000d4150f00c402003c940000c5041341246040c00d48400200c80060016894441c448503400070032208001c0407040c0002000c880800c08100011070307015000501c841411000d62400c00819030321011a81002d0641035201c2d120300317014940c85840124086c81c00140c004c24024204804481c9120458100c1d04250824860340ea5500a52051600030300c810070400155120540248951171181c90500032030241900b00300c94402d50554056a00e0560070b80104c0b400c02c0d00080b1032819000c043c3c01441800403d81e62001840b90081150040000444501c00041c195003e03680c050005a528484914204000c010030492540840e45080c0c1c50110a0400c10001042d141c00302c0e10b01c90310660f19420b190 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 90096808 1250 90095558 90095561
    0x1a041a2101080609010e1c080402131e0e0a12030c0318060b01090510143a0b010c0209040b060604120506010602060709050306240307080a0203060702070b030f0703 72
    0x91512191200c5400114603a04005503181c80f0384203100c003d00134408100001c03034441e0a51541d12004101c491101c22071607011701e5400d5081840a0000d102c0009441c400c903080b2910f04a0490004440d400002d040780301c1801169030000305e100240c048000207a803000803103440d1070b01038828540c540781c01581c2103000354454098441c5000c00c0d25081ca8071490440010442d4001090101c1c042680c003062504080c0c44c1c0302c149204139180d008191001c03603480c40683d00198210310300c032101000003501480ca410f9443c251a1544460500a0f0f0281c8010754203481c0d10380403403410030800340c20600150f5105603946070016048080d000d2a074480c01c2c040758803403049812606240380d24009010800000042d55412210150b0a4807003c0e150b0f4182210841194499540d26074000c0c008242500c1281302d15180d401818412108a202e180d03003c0f0742442c1045d40900d8498208802c06415801d080c001d25910012a101501000e41003032040b40403804054030b8820f080f1040400900c08134001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 90098058 1250 90096808 90096847
    0xa050603010f0c021c05090108070e0a031a100509060102030901030e07030b01060503010f0b040303050706050a0b0406090b0901050303120103031103120a020a120b01090b07020d0f0501061a041a 85
    0x102e00144144140d05901a540b000b194101d0324510a064118010780d9100703005580c042c000503580e40c01e4907242c6c0384044410b01c046003015a800211044004000740d01190400c0e99154a001c81e8a90b900e0303c801001e42a80340d0360f002600440a1508014103680e0100880b00b07080d0017400c00003149070104034000d1800c10700f80c00003402c02030500000309a158001019604903a04040301c0308165882e442406101e0064ac400200032a80506c074800014202d174218035800004041c0c001400650304000030f05a90030380d80024040c50b03541340c1040b03407070030000c01881c050a0180c0085140c150300402419a007030b01444098204030404e42124003041c028401c40c0c1006585110704034041c103020003000d0083d03000301c10020110307400583c5076055408500401d246400141c650215140c601210507020b0750126508981c00b44c500080700000401101c40302030313114050300c00090114202151480d9060140c260082400014030080142c900c1c02c8a81803480c520700b04415844166803500004200711 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 90099308 1250 90098058 90098081
    0x50f0a1a060a11012003160c0206040905071101052d010b0d0e03070b0408030601090608040b0f090a080c0106030b0c031302130209041803080c13090504020f060a0c0b06060c03030a05060301 83
    0x5c049007400481e14565001d18000c071500340e40b6645c81100b1810039506081d040900940284c0d00388820408002e955000951180c10360500814200e081170303801d0b003120070440ba1f0350b0101c1c1180c24040102c24003c0a03a80250381220070200721941040500f1045010700200c0001940d02e540d40880174401c280296034070180d205070341110034202490b1800954000301c071424000f81485070001100341c0304510590042e50808000b4240d03031103902140f410700a008000b030095100b032820202c0001c584030004d00d50780c00381c0000026a20b00f1442c0204d2940005000720410b080244117000d003001c03008406404440e41250190f41021110510074040d000c0d181c1d106a10614200c00d00810103060708001c2ea0482c030030307641c0c20141d903200714000000d03010310f004001c1003802c8094180701020302e990186410a000600030510440b805001a6695000301030740400035074003079150300c10000e040004075084030080300c16900f448540c4032555507030702008141810300b03500e41c400316595440a5114070380488 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 90100558 1250 90099308 90099341
    0xa05130303030204051c0819200106090e01020f12100e04050a0c080318090c070501020309030c06010909082b060b1e0c0c0d15050f0a1a060a1101 64
    0x40d0349040207802500240703e0f05004011000181580941160700c0302031a0f503225010505101c48200358000001080b4041001d024003450800c040702906201803803086c00366000803510500b0301001e01b00f500c1c03440105440d00ea0040c020025100d010809592004095410710b10803951491040f141503511a440402401e03140401e00042c031030b01040c5000b869020b60507a4068568484a41c1e03503910420304002540010b0451005161910310b0300380c0c1d040310342c40c45800d080a20503200c40b822071340140e54201481d80001852008600c080c401d042c0180107010041000f840207864010f014420302c00301210112008100d5403010600e810342140e0041d2044003009110340700da41ca80f403254844a1201c00c500f2004541c0f0654205c038500b00c824803500d0401034039a01400d170003481200d00700c0010446280d070fa00030014105130510310030700d44140225104130f5000cfc00c0801d407007400c45050300e00b1860708000540c900d00e03c44d01c0d070004a030941d01c02841c20340c0c00154540651401801e90b401200d0240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 90101808 1250 90100558 90100597
    0x50705041b081b04090c1211090915030304030809041b0f0201060905130b06010c050a030305100902031b0901020f0f060f01050909060408090f0306090d080c090f04020a05 75
    0xd07100455000803071103991903554054031919400b1500310096503080e000848104001e00120100c1d4118498188071030605807003911000090308162055202c2c8800841004100306400d0f250244046821407802807001c28001040001b11b83c507403007070740400b810498000800c0d1039980c4441d84410380c07258009400c10146035410000808845c030340c204200040d8204000402d090446124490203418461240b110404c52980c8280c100d0000500042c1441070a603035480c00308000303100381c0123803901c00d41d00002c1514080008210710b0746e01d5003102c10f1251040c000c00080000b1032504035612400740040c96140c8603501c0040780350001146040c80e007401120b40c05c00c1c1c0380400040235801072130040142c110b02c1c0e80760010700900d11001c0300c800c19545e0045000c100400c40b10b030002e0540c0030f0b0280c00d94803001e03c80d001003460205d05850201c0e0a07840380401d0406150300040c001c2e002000c0c1000c0c14581041e05001481021a100c404c2e031081da0700181845409003d2800c560b0101c09504440408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 90103058 1250 90101808 90101831
    0x23010c11010302072a1e082a0a090b01020111070f0b2206020c0106080d020d0f0509120a03110c10080a0f14070f0f09030f0507050402040b1b0f0d0c05070504 69
    0x30300050311401b41c10000e5060031203600d04802c8610000c1d14410002025000c01c802c00162030000048894042c43c902d124400185896001646000e06458000442c1e80e0341c1c040c0009086030b0520344034280c0c1c0c640900c210b50014a811820002480e000039141c8c1c1540c43e00704000b0b020300180d00201c40081c6590b001c441c2040a0b41d000b800c1c0f00c0480e00700030848241e44d42071050320340c0340d000c6204006811820300c1c0c90b042e42c05540e121a6620b0382c1e141040c10b228411001c00e140105e030098078001513218203115030405911a038094100390f02080074200ca02d401d4004030b43d105d0b80c1414800140900480012041c1119078003403090f507620500c0610108090814a6180c442c0c29141440003440240360786c070750740380100c8084d07110144558440800301c0c030316281c03140019401e5404071064020240006031640d1540042e2000e01341180c07000c1d41c1e80d98509d840211403040403403503140717035000074181989074000401c0d03000c0881100d040a5108a95629049045c14001d0b00300582c080e15240c02c00a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 90104308 1250 90103058 90103133
    0x90f041e0e0a03050a080a020408100e061b09010518030601060809060c12010506090415031113110403060b1206010602030301060809150105011b0c23010c1101030207 73
    0xc1011810408101c4005060503071600c4110400020b00450740401c201c4010500c0b4601d5194080440c0c1c07401401d003a200c4403c3d90a06500041d6091400d4662100b00c0d5581d40a1003c9908501500d0348031010303290528a108850003005140d6040c800c010401c000e403030348017100716001c00000a042e62425a100e0801810f070b07413825214102c051250b000000e003c03245010441300d68175000c2095500c10781c41d040070880558018500960002d0300e5803001c0c4240782c03005540d0f8018612498400c2041541e0106111003901450421802e20341010802a4148034140c03c41d801d0f41c4d0040d501040060225000c00d541c0300c01c00001054602c2044000140182d01202860513030b0784d5039603410700e1604d80c1c0c2501540d03024501300054500090000400c00f07903014802e0280205888800f0303a820268a40301c40e14143d005500c0000341d00c07801d00001000d49041c441ca1064024242001c40300340e40d140d118103403940041d0b1100741c1415070000c1c40c4414000c041801c54a0606038481c8c10400088070304480c003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 90105558 1250 90104308 90104351
    0x70512250905010b0708030f04080c010c020601061404050901030b100e0a0605041406011b0507082a0405040302030304060e0c040203011202030c090c090d060e070b071406040b0c090f04 81
    0x2580c1d16160004c9255141c99084880031600481c0441c210340742d4a0308903280250150080350726080c1004100c002440030302821640f0038481d0080c20f41e5624020000c5c010144034885104110b50402c028130055039805031150540e60440401e418568840414080044980e00800c10101d0760a0030054902c41581004043d26001e45041c0306002803404281c3c04888107a440078003145031070a148040c2c805014824800c24040c40072240d145039903894607030600780c2205503240d0340c800c605202c1c801c1074031350b002e8415000e4040c0c3d8104007510b0b143c0c80007912400003810091904d91034000f00c07040841c08010802070107800400031950380d603698141041d039a500010480c00f078041c1400940c007501e0813030801403083c590f507541280341012641c20011600382c4154102d407160350b52480310b500c4080400250001d00094a82c580d07545a40c3d0a20500b481d050780542642540160308120020f1107000c20260080c100c884600c1c0c848070380d000040e14191011000c15081858401403103000b647c0c506981 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 90106808 1250 90105558 90105569
    0x714060405010b01230a0c0b090c0916090618030506010e041b060503010902070c0f080a03021204050604260604030e040b06030c0910020a080c010f110a0207051225 72
    0x300001a03e01c1c005441043c801145640303072058141002610b000184c0003840b0140b075a150802c1005030396030328450041801c0d80e6013501a8499100035046040c5820704a400c0040c3c2e00117100c0c040c800fa20300515042d0340340180790410090000d208000c4074144000310203150b1200590f100c1e582c4407101914035050071a002e90f451140387c00544c55030fa04a503440820b131103143d40e801d49107031300304121403021350f001d20005c9a44900d050300024010421000240c06003d1140141c11300031424140246888030712250100f103403804100c1080696140e000700d8085455000240b842c0c3c49032a408481d84100130075842940e401038104201c1010352001e20800845011201080780741703044414400d450200b1961501ea4540400c4581d4542c682040e00f2400d40390b207071040304c155203519941e007085074015041c03c8a41d41c0d1a01c829100c208454056074a002c201040110704200daa800002c0d900e0015110b104d0164a003118002607203003040c05040803000c3c9504c5200050303000104009444440c1384502c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 90107914 1106 90106808 90106811
    0x17070209040b06090f01060e0d02040e030a0e030709060e180307170307030b010c0503030a05040521091203090a03110607062307020d140c03071406040501 68
    0x240e501c5a84909200403540c2002000d01102c2078015041d00d2072401c2d0f9000504c0346540c000c01440625004590f1005900700900114009003c2280442002d02000500e4440316411401030424124180c007201c8030a566000b02c90100c2e151800b44040710340309180030408040400550387e10740c80c41201528549006555000d0200040040300c0b81a901d0100420a0321a090710507000c05000c00c1c00c002d4088041395450548a1000904600e4007036561400324003409001c0280a0102c5030552013000180300440007030845130000c603155031041244581d80720b840840481540c60049001e0f0604100d981956a080e04204061000c2900b0038014088500072500900605c0b06600050314514402920b94121401000c0300070701840030340d84010700350b82045a008180030034400f10746d51003d031150301c007583da84e045104189001e0000c2040d08a50304041a000c40c2103400b07030b4841c800 = true := by decide +kernel

theorem cover : BRFrame.Cov 89928058 90107914 := by
  have h0 := BRFrame.cov_init 89928058
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89928058 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 89928058 ≤ n) (h2 : n < 90107914) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
