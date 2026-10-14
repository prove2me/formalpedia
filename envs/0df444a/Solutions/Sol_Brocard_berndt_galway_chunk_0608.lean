-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0608
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:42:47.486223+00:00
-- url     : https://prove2.me/submissions/36a1fe89-cb80-4659-9376-051d551a7a21

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 109172661 ≤ n < 109352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 109173911 1250 109172661 109172671
    0x91c020c13020a1403040512030408070204060611190c08120a030e012007030e04020a05120c12073609140108070611010b0a0602060115030c0503070c020103020702040911040e0303 79
    0x2c4c110610a40c00418001c02a40d400341c01002110108030350f1148140040e40305030313001d6541150014414056003401d0044030024961481c240710b0140003404071740d840c0d006108070f8441e44502441c2007070a220350307501200083c1209000383c031103012050444140560090000d0300c04603080c03500300b010301d46040c492500c0300740011000300e4501014008000f0f040d482138000303c09200c0c0495400b02a61124400b81010a20740d40f41c1990b10084020b08180105d001401031400c2d04c400c00441000801400c42c8a4011a0505242400710700d048002c407038620411095075121f801c0082e4440c1c08100380c4200e0300455400328020821100c54030484211248240210381480d80041c1d810032009214260240c100101307400000341103400c400001c0c81e2100340e58811401a48a10018801207903011407001b003490725410304016428011001400f40d01004000a0900400343c1e504415079000ea01250405035000313004204d02c840301d103022241107509403900f0f8052440d000d00c45000b03110000469000d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 109175161 1250 109173911 109173917
    0x5090f0c0304080c2104090e010513020603040302150403090e0f0709050906030a02090103050a03030b030f0a03030c050c01020d050106020601080d1e03060806010602011e06060f08091c020c13020a 86
    0x5642c4a4496a01c0c44c1e00413840e030b031918440c06052030181d118a820500740300c2c0040f08003aa8507840d050403041510000010f030b15030f07a498042482105c4544103030400c005581624060340342d9441e0b00301a405c14000700700d402c0f52402031008000406501021a03016245000450b0030749880e5143c8000e040c1904880f00c00100e03a10001c00e1069150200381e01c1d0344500d00500302c034119036607a800b081e0080e000781d004950315489809084105034150140d40007110050b00106150044100b1076075a44640c8000641495503e0700f600d8606441a400c90740d40c00c402e80c00a6590780e0403403079600000c2009105040041c042e100001c2001840410708502110060790795036031400403031640c00600f41c0001c41032401d25680f6200001d46050038040d15000300b115030000900540044c0c0d030340a02209500c814906103242000621241d41c2007564800841124500054543d403070505d02480c0c61145004c140d00000094004018184c2c000b44032010241f05031115003003019480c4400c0182d0164141e68804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 109176411 1250 109175161 109175167
    0x709090b07030f0204180902030d08100e0a02070803090d0e0604270204121a070806063a06050109080105040503270d060207060e0f06070f0c050f030405090f0c 70
    0x6a62090300308440240c0190001464184e51b030001d2140031005004041e102d030303103032010034083d4581444020920003240c14080e0756803a08140c40b8910340d160f405910000e10841e8003080201f503850381900c02032540100c000c0c0e03403420446a00740d030314034000c0d04030300c0020000c241c00303652801c1040665041311a440005210f2090700e040c840c1034007410301c288140e000d90a11000440708105000d44548134010005c54040840000c407002c2c0d40c140040224060052070402d020781070b21040126801c0c0c000884504850118031840d4030301c0c1c2400300c2180b085804409080c0208000d4503805a8100c46090301c489071002d0f61000402e00ba56401c503005441508280100c1848803101030741500700c2c10280c804034403071588600010710414118003055500396401b1600700c040011070f220380c8494803c0b2400030082150034601113a41c91070008c1c00c5130200480e103055420102e015440d010b04c0c0b01d62002c01e0380c0c082c0b8a0348031015501d80040c4108c0340308a04075408508041010030701c00e4002c407481203560749 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 109177661 1250 109176411 109176421
    0x7030311030c04090513020f10020c03070314060109020a09050f03010b040f020a02011d060406110c01060602010c1101020903070513020409050108060708070507030c0f0206040b0c0a03120606020618070b0301080105090709090b 99
    0x410101c0d4110700f1080d40992f00302d02c403103607409000000c0903500c51000b00c24605d0078140040c0c40c044c2c050f00440299481009154111038000c0080c001701e0700c3c205c8010410150b841c0211f409408480e203416002030829540b600c41c5802034001e01180d4aa0754002c100e00f95214070404001c040011110b409070304018003003000724015801c020344030036210940510f070128054025003100c18075800540181d648a001400385a070100300c001d21071142c10020360400d002100083e448507850702c1280d2007080c241c5030703004403d50543c0580e0020301401400300110b6a58410254413a4800c0742d28100081400000030030184c00317001590041501640c4412400803180d655880c1070341d82880581c0d0140c0c085c48001040c0e081d000c001d01ca115080380c080d0450008038076000d0925803508600000b618100355003805641e50004041d60300c51000c00e2035803600c40082da0000d0900055030444a4103650000012904d020705400c280d00481c1950300301d5806603900d60010b4100d81700c0120040421341c3c0080451 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 109178911 1250 109177661 109177669
    0x7030c02060705010e0f010203040c1505120601030e16051003060e180312180609060108030904050c0909040305070c0902040b040306020a020f01150f0918020607030311030c04090513020f 82
    0x100b00144a5000040c580b0301c030308011803034204005000c1c11969000003c02041281540111000300030001a184662000d000082e101d80100e0880c0315a8a1200d000500d180c4c0c0700307400000c01c00e2800425514414444010b0807003286840c020f01d400791300c2903589100c84034804d2081000300c90307108030b1801d0b030b6448103507210401542160b8210603520040c0280400301e4513590602d400383c0d0403816215130307007a500648a428084010940c2509800040041001c80d101004852101d50110760005807641d80304c0d10300407507001c0d0001c0b443d0441d45807001c00003050b41190051007403d0040c060400269a02d04189007688158024254500c60a010420000724503801800e042003990040e109810640c0c1d500d6821501c100b210503205034803031003041010a050180b41409880a11000d12079420100203000c03013200705e80b400a008440c0004e107030042c9840381e444030902d4900d4401903036817820a01c540b142103800c83e0040c0d401c103906d4a0041502401400821040e0700c0d4041c0c0304090700001c0400300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 109180161 1250 109178911 109178917
    0x240e030a091701020d0510081b060a0c080412050f0f0a05070302011416122607141201060f0f0302030610050c10240e09030702060f0d0903030e01050601020307030c0206 74
    0x160b1056400340036200492429005003449840c00b100c094010510b0690298038002c3c10180d041d204030700a030481481034558100701ca401c40145d04001c03d51403024034089076540b04551041e00400003040c5031000b0483c0124401410340703101011101000307180c1c00510307250100c1c0c46005005900114080006502446004055080c849409400d1000c3e8580c00e1304640d0756508125540f0f0025043c000110b60804640250b4032107030b404c029108040000b49074442d09000d0199014006100315295071f14032008104d038032038500d0b14894403482d43c0d1a08050710845224581002003000c03001a00065071007442524840e20f8000e03e01142580d0383d11060b03c00d035001c06a0054039000c0e0008070a40240d460088001c900001c24031954682d045907a030350303042c00c442d8000c40d000c445a181802500c4000200f99901190112a040c0d558030181034560b16922481d180040e00d6400d20784084103240d01540240d1200d01030000a00c05035640c800126120f00c54850010041100380450b540503003030980207 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 109181411 1250 109180161 109180199
    0xc2803120c08070f06060909050601091a06040303180e0f16020708010608061803030603120a050403140303041a0603030409020c010f020301030803150d0b13050703240e030a09 77
    0x1e0060000191600c2049510044080e1041010400b03c0d100300851445400c0040030461801c01201c01c040c1d50f100c1e100c0c2c8041c41000034443c0c8071080c1c41600005c6180460001000030021941e07a07549103409083e0b007a05003449207a400e821800055500c4031042d00c2e0303101d19500980390f1804e94134030f4460a405005420307901c085100340311021900c1102441440c029021080041019103807600c02540d1342480a80500c1c07280c2c0082c02804001e4400003203001e0741101c0c0c40c119a0301c070b24000004a401b0300450f40094402c0081d92082e02c1000800f1004500031801580d20980c181c1c188a01d80c509600306840c019010762040104200c814016405003007040c0701d042c00071a0020110380841c00faa0400c0e041030380c0001000040c4000355900300440b400008054902c1c0020180c2512801c1112030000c0010034180c80c42e0b4816020400103001d0000510740c00404910160004521f12800045030521006118500104a0365a0000109881c0000c6250b41c2e817251184c100f002802d611035076505 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 109182661 1250 109181411 109181417
    0xc0a030e07080304060215060d020f0913080304030504090b0f01210213092301060203161e0809030123040624060c0b130c03060b010912050c280312 65
    0x81c0c04a50701a040c8000d000402d000d034024440414299101d185c030350809405284105034040303440005031500c83c81407404003000c440c3d00709199a4412a07030b01031401c029004000140003c10041099003020180041d03d035000c8003000f03440c880c1d4040c8070300c400d650103006010414100d10b4001c9054080c10182507070306003200144c108180e012400341c29448a802038081a600e07803074203e0041d1440480b03440350140101c5140710b15450450041d40ba8880e4040e1580303542143e08844080c00580841905a958000c82540c81d2002604007e00700e0780101c603000c0d119500302a8081181084040e040350000700301a81078215498540d5a200140391030150381d500e0030301c10b1030b041000d61500c0300c09200400f1291140c4c4000c50107450310300400c031402488003031500000c0e442203000c1030000107600c040c1c6e50f2024000540b02030050050303400d028194810390400c0c02c8403c0744001c100c404180403881050541e00c2c1c50402c0c1d601082c614079140301d11364032b0210f80160042000482c040140d182e6510605023 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 109183911 1250 109182661 109182673
    0x905040b1503151c1101080103030801050d140610090510030302060a050702010e1e2127030706050912060717100e07020a030816050703081b040e19050c0a030e 70
    0x500030642840d080c1800c105029160002c540602402d121781441e0144c00f4604180e5640c111f580140c01d1100c18007902d03004038403c0c00c90004102c0310310541c400c08a501000c6482c940f4000303880180464071401201c07035036800c00010400b0b10f40c41c54103d509032070341038000c0c00e155a60004210000e22009007101c0c115901d600d01c020f0303164011311150300031203400711780d01c48c00040c500d13030032440e0a0f21081507420f0781d81c00c0030250460709404002e0301c180e010003007148810807002540d0400c2d02c40400803803650601070610009a000d40090040000c0b000981d00501e000c550340309083d41702c201c11200407022400d26001c19034401886140d00d580f0411580160002580755007651801a02c2220400e0240c0d00031201001450341040601e81d104100d411280046041c2580091107030007800001001d00441324041821080340e1308c0300e02051041a0892910740c0e9581c420311402a6003900d010072403c0c4d5040e06071000ea000c81c0505031081c1c440641c02464000050802c9004003a00620210980148 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 109185161 1250 109183911 109183951
    0x101b030b150a0f1b11010e03010608100905070e04020105300a020a0206150a06050c0709020d090311030a0e0f0103020c0109060203060a050d021f020a0516060905040b1503 75
    0x11001d44501c5040f81d0310f841c259010010040c1c0065001c6510030030a0071000701280018040100705101003e00703180c41d44112229002190150520343c00070044c5000303040f16405250641d501c03806030640203504030794440740c0e1960030340381d1322006590103030000f60f08210410300c00c0305a0290701d4070003900c072050440d503641c403880c01d40c0d9040c0190390f4031210940020b00c05200543c10000581c100003000823211100050358001040024544030300014030601003030503000380d44240001801020440003e65507000d901c07030b0020051002d9101100811514a000c0c1204a40001650304044080d228504100c41c6c2030b0401a0680902c90028109902008040806403003030143c0c0d19a507100e4500541c49080490400007202c003140c101c0e9000e00c1900c2c160801507587c0528005103020a80341650007181c412074224200f18060744007502c02d12a01c0400c48100000d410500b08641d50380da10710700c0160300c403000c0005448004159591103c0e10308030b44880400500c0c02903400408400842d10b0300203003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 109186411 1250 109185161 109185199
    0x40212070b0703030b030f1b06040f080304080d08070e0607061e05090111070807060207030908031611040c020c0f01050d09050601080d030b03061f0e010e09101b030b 73
    0x825045a00d420300042694000c03d50540101740003440101c016080d20707014503040316995100a00e1b0301d040000089007a280d41c9e12240700b1580074000d0702540100c042e0710381b04256583d621510071200d4070f01c941c94514240c140301c2d1515600480d0f05584141001e41440304210003500000d5051302d023142e0342d145041c0c036900c00140d1440c401204c4a800b20781c03403905d0090b503402c5800c1d00315080918a0100300c090005490101190500b1f540500016180c0c0c005003021249008035800190307c91000142c460031405099494032401c0707124502001d010500d000c01e05c400e0361076a80d102c60140e40180d084100b140b40069039040c60f002d0624200c1d040082e40003903641a1041d1034001d8416400140051010080c1400b40640c1e0340120305080c40003a0000000c299078441c0140340031311404442030070704451002240c0d407000a0000e0300c4140710303950310b41540c1c0b075450384242c40390b01c0188140c0d0a00b900d010028080c4d804030780c0c1108d8584000c090391030019005050020810765001820212010749148 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 109187661 1250 109186411 109186423
    0x70312080a14091b010f0507030503040501090c030503070606141507030212040909050106050a060e0909031603030b091f060e01020f010908071704050d1104020705100e0d14030a0203040212 83
    0x1000ca0300038030841d00342c544a5130420700710791241410010a241d08100c05d40d046170444191981c0352500e04c0e940d50391405d0a500402c25420003c0000d03c09080010900400102038450b940c0524401c01c5000e607160002509482410802030708042c0d400744040c200740e06c900180410074004c0c01600e0300418100a000c50a501c140c0051022558410020040c02800d116031005098180c800310001418400041c1c05611050f00803441202541c001801c020428000da44254010301c100c0703c1842c50510700940640080c42c0607900aa030548000b0f4090008030040d242801441c01880c0c1555041590032229880303031844280c103501c19403158031440c034001d20480d858140194802038a55400385407070008182403003040311003460300703100a002c543d40d00c0162024042d070001e0340e6480c10a40c240860040c0c01800400f400900800321080301e0503070390350000c1021148070303425a82d0792102a00c0544808402081c5961800824070005414a01075801980c00c940014810030402d480340ca80545404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 109188911 1250 109187661 109187671
    0xf0209040c11070821090604030501050703021b1908090a080604140d111507090314010b24040e09071a090a0614030f150409050102040314070312080a14 67
    0x510781202c0800a40410b1200301c02500d04000a00b0b030760340c801c1c200f41c0308516985c40341451501c8000350b03041d03056407490100d900442d80540280814603040d0405402908298a80c20150300945880300c24901c01092031041400604d001c0d1541c0005500d0750200364005a9180d60095004040410910420800e142c401c6101c0d1070f82c007014621003c0e4244c2001c90380130000b01401801d114251a00303101041c00f0008485000f900720f1a6a509202140c21038150ba1014101c80060b042c411080c00d01900300d141c03010401c4d03c805601c44401014845008804002e5082c0c1c5102440140482c5600c000810342180121040f246019200c0d04ad00f01031445050350000ca07882c0010b03114089080403891a40100410f0a19454511024601d2030b208e01c001040015203802003c001004085125089561004054410410841189401030003035000b80000d840c1c41d803805080581c17a9400040d100140c941c4100106040c505454040d101d50b00042c15100441c0d85a1060003100446201900d200b5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 109190161 1250 109188911 109188917
    0x2040213140406080f0d080403030605090a020a02011419020903240901050106080708010e0912130905010b13030f06020903030a0f080a09050303070c1a0a0c080c040f0501030f0209040c 81
    0x720000030304210480300c40d50700120f06a0428407201964020103e1010120500717410070022554075817074101c00800c065085540d06c000c1c10740a03c800321156a026045101d00b58008000520f6290320350f071401c100407580030403800c407905007030600d40745981c004e404203843c003034200d81c031502c101c14100c211071000f001c40b58034100c01c6101b0840d1a550901410b030040156081072202c41c01c0010004000000500032100c2040214001c81c04035030707040044000c001e55480003030740c035810344181c2a084518035100e09208141040000b003044201c1204944a41c01800c8140940e180343d41c5d900b071900c0d0300b410000c1da45181e0a202010003038405100510301c1041c2c6503556036840c10303142d0002e4040b09019098039240d070700c0d1041c0d1500280d07001003140e0300802142400002002240342030003c4042c0310390508015220302d0180700c112400d6800ca071044e404c0d01e032502160341c1c9e1254054a0140218030904040d6040c5000400865000384d000a02101140360050700c2d202c1d0280c082815582d10000c00d03000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 109191411 1250 109190161 109190189
    0x3010605070c090203060315070e0a0b030709050405010b12090a06060b1c0905061b04031a0f0702121e04031b031b03020f091f06050a030c05190c02040213 68
    0x1081800b412180240c02ca8032070031810350400001081d92664aa041500b403165a40040744255001b21450465104010010300000361551a200144c0d0401e55491011524084010034580340c0750103814169480c0d1072503603062071100d0341000c07024a00500081301c28060060060007040d000c1c02204c010700041002c0c10340d13561200300f4951030301c13142142c00030b0390601d000c101c900052008280300350400e445012a20301c000c03404621500b14803443d84010301414110007041203500d0540c141c54450169002c14002503a20300b030382030380c880c1c0303c0c0000d00c0c035581030030813200d030070b0100d8100d145840480b402c01c04e030300f02516599a04c885641e10740b624a04008200010001c101c050141502840c0c200418006040c0c07550780840c1000702c02d400700c0c174400caa0340300014110a41d00c494080401505040c20720b01c0c5aa1810040c00703c2d44107240400000e81088052511b2034040c10840d4418005409080104003200340c0403110701140d540120b0384680c08012440c1d261903245840c0300509100061990 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 109192661 1250 109191411 109191413
    0x9030706170703050708060f03070b07050705150901050a050c0a1202030720100e03010b09100f0b030c0301060507050f1605040609140721110304120e030303060d0c030203030301060507 81
    0x11940c10014001c404141c20b004c204500e059220082c1608a0026211040803034240d10000742080700325081140c603a48003058400030700100044050490b2400d9611065032845888074001c58480d81041501069041003400031240c420401407506036005801da9042c858207503070b00481000d219a1500c0181d2021640006116604660004210199841180c2150024003103400b04000c250000d0070312201d800c1d0b4004070384080d0090301038050010304bc3d42140c03910031102e001304e00303860041c4100f4102170f020116450f081c1c10100c034050140d42004074210b03031800c14100d0f00c80d804444211541e00807040410011001004070308001c11500130300007a103504000038032040340e0240e40710101c0c45003041c01440191000e100c031603404c940549000f0319040000d40310003082920701110740e00203616210704040c4103030800c0080c41c010340c4104200864100c0c3d259040354090103102c0050ba042d00200041101b603d0120940f0b24002e1041c03031003503542a581d400081c00c5030002da00c500086000024000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 109193911 1250 109192661 109192697
    0x702071809050d030b0109140105040b0304050d120908040302090c0d0f06140a050a0b0a17010914060306061f170c04030c0503060c04090209150c0d0201050603010e0c06030c09030706 80
    0x103e1698a60f00d420000c030060b00c0d000a128102c0c510508a80c6102c82c0e060150302e91040d011070300580490003074181c0e40e040038039241d55925007210440f030009062880341101243c03240214031f54150001401c1c0d003840d0458080041400000d800c08041d10810000341c04d1b1030241e07004803408042036039000034642e80307018001e904203031090156501c91103818205000c107648030400039080c1c55585541585980101c2c1084c0e50800400007600e80100201d000050440180d40086076200082c1c0e089800340d464000c1499038445055410700c0e40090459200d110f03544102410b558042c1c0145890400e28907140c4055241c1c2c8e40688503030800c0400050140140225070316100020715042d00180301c180350100d44010075001c0c0307005030000c407600004d10101700e5079031760b0443c0302030380e00c0001c119070390018240103540e2500d100960380c015508040024400345010b12030b21030240d1380c0c003010341500c0350724a0400c0030984c4014903c10102c4010f1149106d1520104200300c06801142c4070500c8480410b5610 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 109195161 1250 109193911 109193923
    0x200607020d020d0815011404080d02210a0f02011b020705030c0108010810021303020913031e09090231092403020f010e190302040b04060e0609070207180905 69
    0x407055601c1280180c0d4480c3d80206029801190f030410100280241d600484400400b00141e041c00300c0003040104006601140313040c1c80f00240c1e02110b00d520031a061080b00065013008001c12018240b1000c02102d0080400144054083c40001210790a001401c0d2a041e101000000181d00003541800789003001c01020203808002d082c0741000758909801c45a407584001032540c1120340114280c019092080000c00c040c6a005042c088a807030514070211003003d101ca0282c00040c14001103880100c403c8007a03038040c4138181c0e14030581d103003050200c0001c0c2d1300440e84e07802407500d200510b030f02c20a1190940c030101823030642010079952402280c101602c28842008017003042003090248406a4203080c40200c0707605840c10041d09071414010398641141d0140550400b00b2201002100c1340e0300407400c0c003903030310864007004500c240c0700c1840216002d03801044075849000b000b00d071f41d500e0040900c952000d820720455050545a551340210805211140c10800742c4500001040100501c0740d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 109196411 1250 109195161 109195183
    0x3110f04170114070c2f0102010c0309020109090213030b0106030c0206100f030b0a090605010902041809052e0608011a0103050f0a020a02250602010c020304030b0c090120060702 78
    0x1c0c001444403800315850940080c00410038000144280006c200020354070401085564078450000340513441c1040c00760042c0e02540303006502e01001d52200b64028400e098031580c06948034a02d00c3e042101c901c0c000d50100b0000c40f158500c02ea80080005c0124103030501800c85650701041c4110150740203071400d1800740c0981a0000036620610542800207400811aa0002800300b019140c0f40090401440200d50140c0301c0f03420000042481000da4004000300d525038084c010640c07591200e08070480760b48001c0242582c01014010504a020a42130303401140254000304040c40d0038482c4c002107030610340c4142e005944425924401d2100c001da102c03003049081c00d0511407403071724000c0744215810052849010302c0e03000c140c030015a0b10802c0361190320640080950581c00c2c6182e02445d4034a814441e041c015030900c0c201d40a000e10100540b0202c1e44c2c0260442040d0b1078000854145402626001e030400035035000e0034208900070109600e10550010181c4480d00301b069009003454440e442c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 109197661 1250 109196411 109196413
    0x11802040b0901180c1b03020715030213090b04020903070608040201080a02030402060d0e0c030114010816050a150509060f0c0d051602130b09011d011401120c03110f0417 75
    0xb00401810851a002d4188030108810000d40c541030300300d096030f221078201e110f807242100e03882e019000c02d0303000a1440c0039691620381207041c0314008542242030340301c0c02c40402030403008180100509103181c1c00407181c480000703102604100001012914040e440d40c808000289030300140401d40d41c00c00c6565811180d001829840d5181c2a00824541d1280381d00d10803034550344031045c0c40590000d0154000c0010010000c0c00704600742c404110640d2800e00a40c0e54502420f14095802d24110138400100c440c060203044010b0328000a5515000c002d0585030f043c00410422204a41e5030300005060b0700381e940c1626901d51a660f0000c0d450030303480781000070078000c042007071030000c0018013803007001d040d0304543c1525400c0d00c8131642000749c5035800196400100000001c24101000084141d148428080e0000146e0303a0309220884d604401c0851404a0705c1104004401d082d15002492114047d0901103030b0206010340c9142180d00007540500003850110f401d000c9541411055690700c080c401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 109198911 1250 109197661 109197679
    0x3021c03020f04120309050604080a02090a1a090c0f04180c02070803040918080403140d140a03020708090a0305071404050c030a1d0f030d270b0711011802040b 70
    0x80042e03110f00c03640c040c2c40e81101424440d8010184a2200c200141038003508198440d0750b9001c4140d41c03000c0405080340b00b41080c0000030b5400000b440307a880d1441c8000d0310804a0ba20040a0100300b00002e00400b14458040101800a4003004020001403ca216084220025040091040790700400d410700c21501f090034100a044000000e66042d2921007400081c0102c09400d45450784801140040400402050010500105c2c500c5848200d291005443d441c490207a0304035001d48103a10b40303840640f0306000340c448040c0720364050283d09201c0c00c03070103103024800c4002a826035501c0c0e0088500d54010b00e424042d0b0032441c0e64151100c881582d060009042c003040501d8940001844201c800d0394a0441c0c010303500b0160074108100c00d10307005884210030800765417070700c035802981039040c0d140c1450100340348203080b124400780c0b10441505c0c1070b40900e01c0355155880c2c07100181500c0100031000b041408420002c0c42150f03030080d407030b040c0030054601b5441404160364200e05070900c299281 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 109200161 1250 109198911 109198927
    0x106170a1a0603070c0f0f020901050303040305030a030515041e0c02030412020f0301140703050a051b0901110f0304060c0b01060206090a0f08070b01080102030f01050906100804080f0703021c0302 86
    0x445101500d07824111105a1281e035406412225003070002d401516429000881005000c60f0f40d10340d01015001782d4032003845a80750000d043e41d82c0b1950bc8014000c0c4d00420103144003070f200e90f01864005810120110100c1e03101ea0005080c1c0d145035207400f81c81550180141000d80a0b44259020140140080c504261401443c09401e041101e0040c0c01080f0752401d0407044d0f5420341c81680c0011000105106a0504c803000078000d0500301c505044a42c0780001268140300c1d0301c04c074108090102c8401c1440c14004000444030107005040d032079154403840b0000c090410042c00940080c1c54650344603108007041e0300b061000060180e11000035900f002c13041c018a1203020454034002e070340000b5505c00320704043c0317800c619500c03c4030405001c40003042c0c000308008406400030360103400090048403469803240100b080750319007940c40c03941c81440f0641c14212580540307840c83d0300500903000305c2d0a200100807000d41a500c080380840040e00801d661254030494101c4105400c510307440c0071410f06e40340c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 109201411 1250 109200161 109200191
    0x20606010c020d0521070507050301060f090b0a050a090207030905040506010807050a02071e0602241609030602030c090307080a03020d030209030316050d14190c02030a0b0106170a 79
    0x20391000e406a40c0e00041070f07040c0030003081001c074946000048402c041c2d510520381d840e2a0000e5904440314091014006041d1030705010b440180c48020110107070310b610340080f040c003d00c0d80400d01604599529400501907688582400060541d600c015036100c20710324001704510480d421840c8558a007030284203480e6171254105910000b9405e11030f650780301101083e4605a002c2d030003601c1d00c8004c7c8035081054500d042c4808210b0748036400325280880c1510314212034a40c15145480500c840400180b03943c0d4503080741c032500e80b42608010075403603200e4944005913802180c29000d06500000e42d0074503800d0030802c000041046802400701c086071035070000e44640345d5400b07400c05c2503004201440199010310071644002e40d0106244000c43c2e035032400c40e882d0182025103501081b085d18010034040600021038230940c910300504d10244200680a50b036405800e2020390f0140b0641c29a68000383c01207560798060212a10b41314144040301e402c0c01c0c810000100708006090030300000c0a00025 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 109202661 1250 109201411 109201427
    0x301030c05060c1501240512070513050a170d020a03020c060d240602010605031b0907030902190e0c12040f03050c1506040506010201021c09030519020f0d02060601 72
    0x1d0110b86441e42c0e06060509185003001020030040c2080701640002134100c501107410080444d603601103050f0705030740081500c141c001c0744014140071050500090701c840c403440050409803c03074841955103a480d500403d4000f640c64029041c0d0384080c078a150604401004603200181d03840c4010040a009994000c2d00c0d0b04069851b5800b4140c04580003d01d0180390b04040d0540e80442c510a008400742849000300741c407284119000b55203002d00105646c10080b40c50306e40705043d54449000c0c40005c100380b0030403200052400d000c040d5519080030059a0f48610300762041b0140f10503404150a11030000001e00d0060302018032040104005d4202c0d07c1c032060f1f0f49a006402c03a410645180c00d03814103440b41c1c0319604030a92680550f081d401002d0700540421801380100340d40411503603072603400682c200d115641080c034100a20908001050039150400f0401078406d00d05541030100c000c4480c0100c205506501d400b40c0c000010804144a00708100340c012925407000b05000c2c201032002804c460 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 109203911 1250 109202661 109202669
    0x3090708070503150a0b120a020405012324130f050102150a0e0f0f1e0606060318030405040204151b1104110f0c0c01020601060c030503010611210409110301030c 71
    0x1030007010002d408685207922240140d07001901400707c0b2003481614544800f24510100d00c920b140900100d0341000d80d400350300c0c0c10300c12140007640300c9552004006000203150703222909069001c0100740c01b44e030050050300c0c070b03201e0210321454260304119603240b10b079207039400c028111351040d10061144054111195003010314408001443c0c001c1d1006642412150100300180d44a07070311703101400c0d43c0c0001e201c2c034146032445183c06030500803844a0b03890710002e40e04194801028400709024410241c0d05030010440e000403685002d07900c20106040ea005540010f0b29402c200040604c0b1a41100c01951070b210746d403070710030280e0403240d1343c5440d100c0f9400910303802180c1d43d8803903103001a0385c202252001c070203007011030380c4070700d0040700351981c030501401c80d98014001c10000007005400781c0800030040b54940c68860070b42c0c0c01d221041340c1c503905035000701c1807600c82c02510b00e004045150f100e01d080c00940a140d84e0301d80c10500d0680540c0d8000403078000e00303001000100089800c0c600000291 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 109205161 1250 109203911 109203943
    0x2010509032a0d05030a0e01050c0919080d0914010206100b030601090b0c0a0c0e070c0b13020d060b0406060509010219080c07090203040605060d02100f09090f0203090708070503 78
    0x80000074000d07140d240c200041d80618828151030f5100e058101c0c0c0510700c6000701d000280540341c4001000c9084c1c03581501c81e40310301d01e000c1c8501c0003149070158900030050380ca141c1c000b00e002d50300c9159134038001580d285031001c105441000e000a10740ea940425407000280020a41c1e8101b04040c2d040c010081e2095419000000c4080341d0f00780e10500d81480182686d8070003545820481d261151107071400c16003102c4c0c4020f03018002550b00442480c1c540714280548800350b003110280c0300d8000e1003a00901c09102c0f038074035820b540010f0b0344036111000028041c140000d41d0003222004d0008450054001c1010b021080c01070307012980c1d0000e16600803002442c12811000c8480c03500300c509000b03003030306445140541d0002045500b0140c1c00f4500c100d0040700b00340440e855100911666694540019410200115041501074007607240288003803030a00d4400000355a4146542c12245618240501c00e90000f00744003411000304181c80150808201414a641c58100060342c0c071181c6404282027 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 109206411 1250 109205161 109205197
    0x206070201110c0d050f070f03150f020d05090105070908120f09120114070201060b040f030b180d020a11090106021c050d090803070305090c130902030f011a0109060201050903 77
    0x342d4406002580e000341e00a800803411035603900d4410f443d034864900c0400e6620070360700c00141608480f0003000489800150380c00503030144000c03a00180c6000c01c142e6084139020003400351341c1181482528403e800a500000d820b007071143c13000700514200d078005180340c1e00200703264900c032188404071a11807901040640e0703121140f20104240020b83c1040c103907694030313004d502d12041b10f039103403414400e65060f030007000140d450b0320050b6840d000d00d0041c0fa9550103040c0041c00000c0800d000d16420240c100e100b01c1c481c41d0b803900c0c2e09150098100c1c0800060708a00d00780c5080108130140d2148401080340d21400560400138000e6881c0f2002c80100f000301c90001007108001d0103002214415103c0c41d500b80100d1205042c081d08603801541c0d00c1000034500400201e180c0000710702e40c6032102c40204000c0750400d040011101070903040a050b03a25001d24070000e002070809200d440180d1400034141e0100241300e000242004080d9440f10080da4180010400912030200450310b010980801d0748107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 109207661 1250 109206411 109206437
    0xb091c110c0303040b0703140325020a020901030501060f0e130605130822211106130f050405070503070e06031b0309011e020724090b011203021006030206070201 71
    0x31a0101d11040140c050100103800308941803401c1c001c04d03a0501a403100d07498502402c0341d429080c80100c038985507101100800d901441c1443c1260800056184102c0b070110200350005600240b0a3b0300869050b95510380821081c140100c103140248a50303c03c00c040c40c5040040441ca0b10b810700e100801c0f680c0e0300d0340005c80482d0851a4404072540000c1382c0758640b0468200c080c82440500007a41403101407020000d040309800c02030342c64110200f440c0c18203e0401d039880380840011150030903844a0144583e201e9066808802c80090101c0f40d001c01e401c03403400081c84211030002e82020104481001003107030503900030504804418003039032107598903924102c40d50510010182050081796000040c41020441500701d0a10b000c81da442e12240c5070000c5000100724407440380010219082c0d0307100d035807100c103503e506400c8a5000c0c1201080100c029a500584404241c06c0418050361821450301410b50402c0315004550402c1410040b0300d040d030300007074100d01580100074100209810030b01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 109208911 1250 109207661 109207663
    0x90f060a03020c03160201140708190905060c0105010e010e0609010608060f1305161110090c1a180306060607080a09030b090c2d01050d020403020a120b091c11 70
    0x80c0803c6610094a460350a0314074100800f0041a10070b80c001903250400c000524011403c6441460344685c0848c6840141012001c0400d00c2d00c41d550180807101c0b40001d41902e401004000c0358940100014156040000b200988c03030041c0c204042d500f801c0c5081100c00e0315586040f50548010742480002039032045c00044100c0000500c094011302d0302100c910344048103410040c002c0308c0e103030300014031003854220403a51103100340b514102a0340100290010320300b83d584562065405207145c5403603542c07500b0000090440030032003034407180c90014196a120070310104034401c4c4d88045001c1c1c84541016000154140521800613184240000322044480e00603440d1600071940907600d610b00745007500701540c4880d05110766501610710395000b2a0712007484052034510914003494071911782c2410340115103a07007085a0108a082d401c000c04400741c1d946054400040014200300c92044400d0b14164204000c0588402c44035400300004031004400424000005030152070600d4004144031003070307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 109210161 1250 109208911 109208917
    0x17010b1602012a0b0402011d030c0f0f0301090302060105150717031e0106050c0d11060103080307021e0606010306050306090a062f090102010c0816030c0504090507020a0c0b090f060a0302 82
    0x3860070f0b01001c1d0f2110200400302c0c0f07086108a000340c860200e1301540074000d00e541d40d2603d060603459040302066024030300e08000318100d808400380801d100017210340081b0307003103500d139280035400b5900c88801001986407510450342400e888582003401c01025603544803445820600c85007040d40040001000f64103907151406104600714401011540d440c03101910a51000c180c000c224003a200d4480c3c8031f0350182c1f0303282c0031800780035000340a260f10f9500d551440341c00c0035180c0800c6004015030b0340320841d851011103170558054409000641010300014084800315030005000350400000c0202c98003000c1481c0c0001e43e0440e07000700308102c0c2d0350181412004d542c0748190880e8150441e08224103051405050000420380007040a08071707460041d07a803108229010084041504810210544a40c0005c0c4000c540d038105941481e44030106282566812240b00c0016401040050103104100340107600400f00544d10310b1070014024081401c0081070907043d802886c00140d1400740500c00d03811 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 109211411 1250 109210161 109210217
    0x1b040911070f03030504020f040b0303090405040204110307090503060601110c0f01020c04020406030203180703080415021e030304060f050907060e060408070f0e09011103150307031217010b160201 86
    0x1803400c20285180250007000240e1b000da019041d442e0307216450f41000d108202d0b142c18010021130403c0a0750013004080c00c0c00a1049800c00e0301e43c09600c401d407611001840c02035602c0e031501c000701c82c10300381418034186e0010101030400110003011004030a000c03515000c8983c0036900003546d1440c810040c4d16203030000040e40d400900c0000d00051003036044d4044c6010f1005001060103104403030b00216580d00060101a114020401041003c22440140d10703c0c4403501d030058070010880c10890703424401c142043c9050b6900000100400c22009201d41511400900d008000e64182807844541e80d039281e0003110140161000c1101c020740c0d4003c192802071040e00122048a03880b2005907848100b0f921407801d4841042e40410284801802101940c41b0035410713031400c5a603402500904481c5108032241c260042400c00f001055102e4a240900202e80d11118000740f19562070170803441059000d112400c00038000138071240f9a0345491119140c091030410800c00000c094403051200a4503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 109212661 1250 109211411 109211423
    0xc030903090501030c141317010c020309060304060f0609141f0501211d070b190806120a1b060201060503060103081b010603050c090f06210c090f040b1b04091107 71
    0x240341c0b1552030189815405a03045241002c058043c9588c14500b80c46c00c90315401e015070000d1200d040c05040c080041c541c01801a000440c415031003403100c900f255001d070004060151a41722800c9007016112400e80c000100440050421058261441e12500540911b504002c0a80b0000048003c4041d23a02e07580c0d02050820002c070241c1c107078a562101440d904191a41c05600400580d004540050340c0c400c44400c5c0d00c0d21141b02c81e25008951074003004000035404441d0b0110f0880c50071041240d8800e0f5881440c1c100c0b019461054500412060380d44100210ba0510806120544000c07554904481d84014102c1d12100c1e01140303100c00b46000c4030a8a9151300e04031001081c08400101d40000307041c03d030744080081d11030120003a0410302c01c49443d41c02690003050310243e004010f0039009165040e20640300c070707a10401c001034401e42050744c0490200c80340005100601200700c01c06a00459a251014501d030305000da1b141e004d01851240401203965002c0c9828080311b41022102120750000b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 109213911 1250 109212661 109212667
    0xf04020d050103020108070c0308010510050706020304050a030e0301091110031b0e2b020f040e011d0f030406080f0601090f030605090606030106080705040f1d060a0c030903090501030c14 82
    0x10030100108000d20040c0d00044410340481c407203a009034800340c081d40d015580c007810750703007407206101100816600c10070811034200100c0011a296101550150b4800d60151010982c00c0c140141803058080c0c0140c07003031749400e0280380010039600d82d0400000e0180d0391104c00e40d0000d001a80140740d00115080a114010300140030b1603440107241c428044110340314480343c508400c5515200e41c840810a191403000d82c644005454248402c03610303060014804207031404910a0355003505c0381c202c40710000c1010700180ca50101000e000b10740b02120280011418035140c80e4004041c0030b03000e0209122602d485010503d01d9202d1155200646040c000c0428000d6a9103400c00c002c200803140c8250501071100070840501d1f060240f0000c5500c0e170307401005118101402c01c03004202082c0440821607403001c5c01c0003c00c100e507415105100c9008040c00701442c3ca900c0070001d440c1d94005074170815160100000c0066000f003140b00030b40e0384c2840c0004200c90000f5007610510001e4500070381c414404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 109215161 1250 109213911 109213927
    0xa0806060708040f0305060a0506090f06040603150b031905070324050106050306090601110c010f050c071202240d0b0d021906020d05070f11010203070606030534050105090f0402 78
    0x4881c4c1c103040701c2c4078204544481d0340f14011202112015903c50b9444500140810340d00f5407584500b94110900130300c0052213642e6591241a203e1000060843c030a4450074500014078086c072055051482d140107c0c0050780b400c2d6140380d00c8000c58080140705000411049010b10b801d00c9074a11081c160440403c40c9503107030080038259800866941c0d00c9801c030403002600e55480f0341145684241c0140060818180400c0191600380790703041150f04218081c0a400c90390002013280c14020031041964506041d154014404102c6568004801d1000a0540c07011403c000303000320f0320b00110700b8400091010311440014080c000c0140040c2d800502075190a070300015031086c0c182164096021107110680381c89007940c42d4040c0c50300c0641080d00b00300c41f490208000c44801001c0250510540c0e1a1480d2540c6007404c4030b141e50400d0760941c5c0702010a0400c01c142d48501046500780b1035501072000701e44043d0b1121b406450044604001c800700b401c08098552410455091000602c00d40d00c54240b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 109216411 1250 109215161 109215179
    0xc030c03091e0901180905070b0306032a040c0905030a11090a0c020a11041e0603050c04060302031c120905031c1116050c0a0312030507030b060a080606070804 70
    0x102211849030303200601c0203500d01c900c01e40c140302c60304001d81a511581e1905032030030308640b56100d01105d0f550700da20f1901e0010706c1c1401064003400c0c05d4525030f526410210f05051929411440780b40100b590000000f02410074124110700c100310458022030484c0009004640141e2640e200d0341e003500c1072500e940f00b040050150910240c0c0150b44541c00c0745e550540f000140c0d0740d00c118500c00b43e0413210201020031035540c10500d01180c06800858880402c1c400e10340141e21495040c3c0005540c1d407005d2040150038401000101402c41e028041079045800098441d40356440b2024400c00118491608034003d0941c1d840b404495102013001030803500380692241e0004882c000800708e01c43c215061401d0b24450203a030707041a000058100240702c401004c00700c0c039205060352030303200360003988099941d60340940b0080c2d88034028110303505621541c0a4161100688818181350602400f822913883c0e11080d618a810549840100d035110380000c51024400c542029102140026020850081d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 109217661 1250 109216411 109216417
    0xb070503060f030303240402130303170603011b03020a0212040902040e090d050f031302061324230f0705031c090203030403030e1801031b1e1a0c030c03 67
    0x1805860802a03080303800b0401d6120300c8200d80ba880c0ca540e00c0111260311108060303241c0300201018000620b4003014100e1819001465401140055601d085038200c03120090f403184c3d04014180c000380442c80c00e401000382c00e09a411f462804259001c05c00c2c485440c0700304003c2d4191038501c5545079980341c5036a0148045d610600132410f900d03010030081103c0680010b80d40c4070f01113050b075806042c0400845508440d6102400f07111000c5481828800941d540c0d000a250160140403030440e12450700c0c60440040812440300d42d035495120368003190f8640c1119000b045041160a01e101340c0025200101d5140203500c0801d103420310100d00031042080c000700419610720030200038070300d16100c801d183c002e9034411000250541c005000c1080028090a4059041b41005002880c6000341401158580400741e10507915603c0034030200503603040c501d003050054110b101d007141c108a4094460300c2d054125100300c00c1f4800705183c02d03030380740000141074400c140c01240030b59039242079101c0110340e690 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 109218911 1250 109217661 109217671
    0x71106190f170c0307051303081201030c05010c020d0b060102070e0109050a05060a08030a03050c1c0c030e03070507030f050a0206041401021b18041401020f040312050403050a0b060d0b070503 84
    0x40d51100c070800c003218440302c1281c440c024104030186581d4039014122955000600061000000441c000c00050085806000c03000850280720b1130540c954180904680c25a610090500841825100142c0c640c50401c4030040c0c0c00c4412400d00b601c5043c0100d250481c160301c1005048449000403a42403074603000315003d580030000901981d10b4034420096084654441c549544c0c0c8100000c0c900c0e41c0c0aa040f041d0b1080b02c00800303504240003d1025125605500494410305585441c160328464140c440c200b501e070303550b000950070100542d40d12941e13501c00380006010380000c26040c0b0104181003207007419540d4068042c984659441200710b0111100c0b054240c0580124036448100040c2405200c4450000070100c0c500f2181040c0c20b40c42042000d00241c8a41d01c415000071001c1009000400841d2204c100c1c00303030740b1469800e1007507400c40300c4c010f51010840c01b08810000710b180028500511908200e280e1655100c020001e0051040001c000b1700c00c0b8010000c00c00301c02d4100c40954450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 109220161 1250 109218911 109218917
    0xd2007060302092713080d020a050712050a0509060c0f0a030c0b060303070f0605071206080c0a1d0105010f0c1a0f060307030816030c020405100611060606071106190f 73
    0x5040040c00401d41310070910300ba48400c46400f0010b10048030203920040081d00484d0140d1422250080f104180e920207402c10000c07c2c0001100001c108001e154061440a0303480c01d10300342004400010200c0c0301d8581d4941c843d001c0802e030010394150034480504514030080803105015942d10300600030b0721628006895500c680400160141000705c129a04698404c1da085070410b00e0395150b03c02480f010304000204082c1d440c0d5a05040c1e018441d4101178210480103100d07a040310010400d1881d807035000148401da818072002c290745100441a81900c0f0242040c031220325100c041240e814600410250040c0d8140088095001c40703803002c980250001d511220040da1107909160b5107059034130000702480c400700070004000c0a06501d94a00e14402d00c0c004044008503000101614400e803101294109200810000180c01c50002e220340f0000b02c014104a150140020740a030042d6030000d09202040c3c000c1c001d05a4030002100d20340d103032510f05411310410740103004101b200b6106041d004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 109221411 1250 109220161 109220179
    0x31303060b090f040b0403031d06010e011401020102040b0a081906030b060108090a030207140604090e0303070207150207150302042601150509041e050601080c031c020d200706030209 80
    0x101c10701c0c3c01c009204c2c5821011300d4000342c880f691b08900604801c0050700b03204002c003550381484070f81844514000c11111403080915410b06005441e541281c4d102a41035a104200070031400020324240c40d0040d00b941041c001036a10300c1201821282508100d1000c50b141c500040304210049440c1401071388282d130303000d0f00d07641d0305009150f071004071030000f90250344000010094048560320588400d4030203400343c5e003071560f1400340500341c1d20103081580d0950400302c01c00569a031f04100c2c0c00002d118400403503442d2a00f24001039100c010034094803000c10080c403003200315030303020342c044400804141d030310030514800071840c80c5c0342100100d1200501e035080410260704039000a01010540d00f004141d40220749171a591141c2c4e10b01c1d04490f0070300c1c855820380300e41c0108100340f001c03900a01d096070152028403070716820141005404800c158404290032000140990700060a2014418605101c2181c5d07101104030b01c62841405846003e43c868610040b400d968076401a1644040544803126 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 109222661 1250 109221411 109221421
    0x5090a140a0204031109070210150306051e041401020f0a021b2202160501050f09070f0b04050103020703090902030705071a25050706050f1f050f040c02031303060b09 73
    0x41a0b1140e4031000d41204c917012030341640e82c070300070007a240c0004003401210403408084501c00e080c2c8181d114414414800f504d070400c184802e2740100399220344091000d10501075003c24041c080c20019002410504001003502d8040c0d409504a40442034030440306900c40c0d82071080295074050341610000400d804480000b0b250034480240c1d00c402010b0707402000b0980c0b4040701d40c4025000202d240581c1070b28421131001040e820b1044a00031002c40b44000306501c0c00c10309551034240ca9601528441d410442c00f000003104480984040e0f6100b403030050b80d21001030908032030510090f000f8000f0b9503c0002071005080d0070100420f009842030304440d007807100b403011044003814100c5040e4005403811205080120b00c0400711640e041740d0707081903800c10700207444400846008490705406078410034103000040844111105480344103d0110f103205040c400030030a020f440415540c080d9440f100702c060303854000d2064a030b4650342c0d41c0e150300c0030990307034241040508903141c1924003800107130012070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 109223911 1250 109222661 109222681
    0x20d12120c0f1112071109010b03040b010504180605010801050a0e01021806030709150e01030e03070f170d020c0105011e120213020f0c1f15030b0a0605090a14 70
    0x714101c001c540b542c020364614484141e500303402e00780b502109030007000c0d2800840c00381d0714050002e49000b411002009000201030004401c0181c000c5884c01c0d0003401040002030451102606550080da00410f5040608080104000d41910003c120305d0a040c00421200d10540c000c1d0720031900940180a19884041207034200e02c5101d102c2c184001220b04201e403d82003803002140c10003031b01d26000c0743c0c007035640d20304420740929a144d410010b10341c1d40d4091095a0725020385005042e607000a140f800032990b881c00c000c0104100000d2048000b450540091031080056035400000b100080d50b559072401900ea0081000340900b004d064080c003201c8036800f0b2403900000990300c0001000d04e244006808008070321842e400c10706a170356001c00c61081e52803c1c40000c1d00103500b5070030080006a43c0d901d030503054448000c0e0308205c22403410040045062030710039110201c039003010842500341c440d200080b015115680242d034114100c030090021002c0d03a40e101c07078150620110f20303040e652141c60083e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 109225161 1250 109223911 109223921
    0x17090d0807110a0f06080f07020715020f011103010b0702040903020f07060309210503011e090c050702040e010b030703020111010207140a120e0105091309120c02040510060c0f0c03020d1212 83
    0x110001905200014228841f8804100c0d00700e201d80c011506040e940724a10100402054100300050700407110440d05c89409000c0c8801c1c3d004144101c50031581400f803509118014a8406071080f03403100340346410b142c0244005400c40c0000703002d88017070b5900c521028000d070052078030447e4030400040142c0441010114484c2580310540d0320b1510b1646402001464644072800b0580c0092204500081240c114410764043c2151600d0301605ca10850041208480003d40c484c0e0890b4180119103107142e5021400b03505031395090803c0074100300000f00c03950082c024000024628010640b00b49000c0d000010380004071880380c030342c035407070002012012074040f8022001513012400c03d118040c10351a01d103520391400c8601201c0002e07144842c1d11001ea400150704600c01c00b00e03142c658660298180382c001c055205400405000703480d0700d480c0c4020b26160303140b080540044102420b801c10440000348010003541c00801aa039050458148036040b02255000c1c5e10100e00d1040fa11800c440e418061 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 109226411 1250 109225161 109225169
    0x203101d100e0915180609070b160606050901081c02012703031e06060207050d0206040b07050703050d080a0f180b0a0b0409110a080a17090d0807110a0f 67
    0x1c0a1101d601e0700b6512000e00320003610380303034483c024160402980040400501d10a5480d50b04d0749252034101c444141c10494054841d03200c64126030018800700034440122064100103030908103003400c2d40d045c600300030121034022642c051a4180002840310340000e8100300355403103500c0182d400c80c3c114030aa00300c400352102440440d8188070100203695407030035010b4616020742004100345402500d00501c2e88040510108001ea070f941c3d050010a80c1001024080d040a131202460b2052540006000740130324402c000c00320700d0010319401080420300800000b154858100d40c0d50b0340700d003400501806c904581c0301078802d01d03195181700c8000d02070040c001107034400c07400e50314045000d490301d0800c4140100700070000c40c1c4482400d00682c03554400c032410035000d0180d252821032210300b0012025025440a0016846103e0000224442c100000b4001ca45182d049a4420100700440c03c00203800c0c5d00540f403140e02044020130301081c00c000030b000c40001c4410003079040e203810303501d90410405d010b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 109227661 1250 109226411 109226431
    0x703020a03083022050105040302160f030503041211030f1513021f110f03030a0c020c09070f09050a18050601020f0c060306040b0604030c0906080109020f0f130203101d 74
    0x404d100c07100766044029030040c00c540020300d001c3c842d11010b0940d0025101180140d0184003a1f80107826115a154041d0916a11040045155880340e03666406540140c3c55103014110b40101082030034140070075141e2020341603e020000075207086444814103100700c40d000300c007140003402901c2c0300540c1041a80c2d004050180a00c19466100c007039055050520060040050804000342410010300c82c0810301c0b58011a9030b454800c0100c400e03500159465010356100c00102005035407000340e005d522002915000000241c060802c0b10809a2075200503001104000003040c8220340e070b109140314001c00c2000313002e180c88074001241e80d6080c4a010700050b4210540b95105441e080f40116000540104042007011501001400b554480c0e4000c0f202c8100c2a8401c1001140c140036401c003c02c0c1c40c5008126603021034000c101c1880c061011030344110341040d41e80e10640e50b0703000c80c0800c00c241c1000071034030f0345000d410403150b0301502d001c1d5082a0f841c8011088565612510407813186068030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 109228911 1250 109227661 109227757
    0x115030b03030735030109020c010b09040c0e04081909061b0b1305070302040e010518010b0a05010c0501021308100b06090d110d080d02031e0403200703020a0308 71
    0x281c007800d414501800b440c40480240b040c000944445001440c00f171f00c441c41005a50300412000d0742e08403004040c440d0b026904680030400440c0201c0103000c01c0b1003215010f80943d64882c904208148106e1903417510402c502c46101c5880c40e4005050406d8071425140e000c04543c426003442174200400b1402469900c1800004940105400d040d41065200d0403c40b40b00581302c0d0b00003000da65101c080e00845079540c03001c21072410101442d030f0090014101c02004a426a60041207220015010f803505003d03c80e82c841c41041800d5044441c550750a804100c0b400c1c3e1610501c0d40c840b0f074030090320440e040c20001c6c640c5240c070b440c408a60400030014201c3d1001040da03a62624685440880d0981c0101c454904401281c044001810b001c14004401660f070320b00504c0c050781c90014280c482501e040c0036002c00000a811560171910300000307156804007106011a514604491500000d40064960800000300007104026282081d1041c80c124040c24600348041d9407030b5400024010359174403c0e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 109230161 1250 109228911 109228943
    0x6020307051c0203070503041e17070509180d08060103060605130311120d090302100908031c061701050910020a020706030b0303040306050f090c04050601050703030e0c090115030b030307 82
    0xc000c00e21400b20250041e2410308140f515181d00b10340041d401044545075030800145d1507440110340c02d01400c00030b02d00c080e8410074950b0311541d03100203019450150000c031002c5100e00d003a03030818104000203082192074030180300400400040c42910791601103802c10201045a900600c1034800951052900480c420b2943c1c50307801c09400d040c07066a420032001c401d007e22000090040c1089891503840c0c00c0c241034070f54070501c105035511001203010086031280500c050103021044070348209451407420203840400d0316940040440750303c1501240d09454100d1040c0a064000701d00c100c418500303030781c3e203c5904ca01c858280c0c440d104441005070015001480040d000354849030040341c000d0100d900f03240c2c036079961100b114415204d00e1b2481001c80d080180c180810042202c84c1d9078152400c0c4141d080030030020344240503420303005040c16150600d20060250402000c41c1407a4001d103500aa9656080b844a4450705000c4a100190801e40712427010300f800400c07141d51079172040d0385420030700503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 109231411 1250 109230161 109230193
    0x2011805150f041a04150507020906091005030d021e010c0212071502070f0506100b190302070807210e060d0e0307050f0d020114011202240c06040c0602030705 70
    0x1245114800360001800b0101307011403201140e002c01a000745100b56921700705180030205614450b41e400c10010b040215900503150643e000c0c1e00008141c4900c0f005454415800d0042039143e00426003500c110181c8807581c5600240855002c1d29480c1d9a05c0508182403056080c0d42800341c1240160740f010100004007102c80004044590088040e185602452007040c2c0a03a400410181d660340d104040703140500409100c0d042d00030081144000b481454170a006160340034002c95a0421450b5040603a00c01d8020340440b140c850748404580c1e5120007919010412007000707011404090074184010705030a0240e05c5452109900500315030404583d680c603480a05207140b00c282d80c0303010602254001030800c010440340440316101170091240e10380c41c024216400c510800c03100d2403180300100314565404818030b00c2d0035010b80b80515034401750303440f2032049481c42505420900001a10740041032011409502135813091010314030550340d822089940b030240b0280a08550000c04481c255422 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 109232661 1250 109231411 109231417
    0x1801021305010c1b0b1207020c01020601090e010e01020d02040819110d030309051005040b060102010207030c020d1b0305010e060f0403020c010c0203160303020f060109090c03032601030305070201180515 89
    0x1116402e0642d0b510713106009030020302d1855000c88200b21020030b0038510200a401e101d64040308510003480c680070070200007540d944040c4100903045507a0f911a100c51013080d00442c8060309004029036644402d9248180254410300c80c0c128130780110301102c48203135902c0c4c6000c03200303d4001c624072030440e02010400c140c4c400f0b42182241455070740c0100500007207050000300018180000d000559151034180464511710081c4454111b910400c135800009400c16902c042d820f4056807490316100d0342e480e02d89140050a00700301d505000c2203200004100381500500030441c0d4580c142c0b146a00d8140c0118428038042d0750040150b0032414092241d948640004a0164001000c6071a180e50b0b10801401e01c4003540c0058005800100c180920000100035042c0108500c883c20800b18840351509601d504075800700a0400c46503501e40103140a800c03918559070b42d4400c0f242e080a5a480c0340280c220360104504138045982c0c00340340c0120400c071229070f00481d0030140901c00340c04503001c0c0040c410341c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 109233911 1250 109232661 109232663
    0x4060609110c0705040506130f20090405070908210c010501080d1202090609041505040c0f2703030810030516050301230703090201050c16060908210a11010c05031801021305010c 78
    0x2603510402e594882081c1032a000c10b00403442031055640e501b03480ce00c02a52402001c84003401240c0c0c20804c040c0704001502c581c02d66200c4500c40d07500d500c0984410f0603101d0003c440d411076080000210328540c1c081551844444c09848521055101d0f1241c0001c3e8040d4040e5282c0c01700341813081c060b1034201a0001e0100e108040302203e6410749501c000750450726150703040e80c001240d40311a0104140c0002e030002040030312646d803075002140c0128407190f900150000508110802012810341c107007850b4124084c5070b001043c2e5221040c4900042c420944500c00c141c4291700302503041003090304012010008141443c0d44000c559130b4030b0000d80280c020504207d0401c041009000010207041c4800381c290608404c107041e130140741134802442c21810f07410010790b40d00714807042c0341ca0b182030700c6031208000c110181894030b501e1010320070344007d2809500310407a5400d140240c1d0b5565804001140316010300f50010a0314400f2041c1c5900703e000b04041e00031030220b0410180510b6000d100f54020719 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 109235161 1250 109233911 109233941
    0x50a0b0f0c060c0301050f0109030803060105091908060f07050a090b030c090a0308030a060812074205070c110f0409140604121d0904060609110c070504050613 70
    0x125a00300050751404104542600b4486801300050105242c25108034aa8800900e020700d044c50454641186a1201820b05c078180000001c0c0c2440c1e90f20345040d41c0161044070b1803c1d5000700d9840d61000d0322444110350b6400c05184500006140d00e00076000e0b610762a407160b44c0c940700385040810070302075030740081c10302114543c0c14440c80300075644103045a400795104403031441e02ca04121207841c0503950070350045c4503180c00034103d00302c00348584170a44a10b5a00600144960742c0080c1c3c21b4545000c1400c58010700411034000b030b4544140e0a03840c42502a101441040a940d0b202ea04464000c0390503001020043d08d10f10886061a00c03509240c14050002c1c40001c4002a50303949101070000c6030759840d860b42005041109114400c5588460800301c0d00b4403052340380e94810b8a80440d04040b28041c03050382c491700401c1c00c0c01000d81c0038401404644104015924041041c244150808900c0e03100754480d00c1000301e80745c18140107e40c0500300140c161038603007240c5c3c1e15001c0540307184200d107069 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 109236411 1250 109235161 109235167
    0x20112050405030d051504110702120123060a0e0702060402010206010605030105010909051519060810030b0a02030a09050d1808070803040e0c07022214010612020f1e040501110106050a0b0f 83
    0x542d0741e501c44c8010442d0f040108e16942c0503d403051151460204640d075045915100d031102803030481003070282941500c6010400d4580c0d404e030000f004420710350807100031a020351041251a40c0c001841c0d50186000f43c08071003c982c0da55130201c4251200f40602c0340041c00140040040c14a030360005600251070300041c0d0501c4043c00082103c285503445250b00000e01c41004200c80383d001426280c220220003a046a100d00710b488509000c20081c0660154a50000005103180403d91010b2812607101c8180c40070518904401850807400114001040051090005181c400000c1150858105d80d014604180c5010305407044044000c01550010804100d500e0050355102000c2500c40c03c5030504140c404a15241242100c22081401410b0b01c007102c01442020b41005681362a904100000f50ba034203440420605ca42c02403143d00031002032803070041c11a0080035405481540c100303aa0309001000602025402d0702d07001c0c03107140e400c10341c2d002051201810301c8004040c45064840d507285 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 109237661 1250 109236411 109236451
    0x190903090b0304050304060908060121050a17030a0b12060105010e01050f2d0702090103120c080c0604050f030403120507020619020705010e0f18100b07050a020112050405030d05 78
    0x98140d00c122404c45207034100260500030550050403c1b00900304540080a0365070515401ca04205035540d202000d1003400e02d245001c2110401188003001ea2019800b0214800d54100b155960030a079050b41d0300c40d040c02c01c0061181403030000c00010421140041065921382401500c0824102c0d42050400004000f0312031b100f1104001412844030409441411840c200c017000b902c40342480c40b441200d00b042103580d000d45c0e00c40c40c000341529008a155606203400e8002543e412000c018010810000411401c1180c50040748451080303000d1010340d00704000e40127502e82c4034482c602000700301101c0c0d0350207511900d03c1800980300b4207101800580c0b400070100401c6400002400c1c5580059002d044280801d50b40300c801102c07034180688843e4054140304000a01810486041c841a2502c1a00084450b0005802e00d002130210301645550f03402c0d28200307640c035511810f8060b80800c481070740c481803041541c85614825900400a14100310f283c1c03001001130640544294011104050020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 109238911 1250 109237661 109237679
    0xc0306030c120c031e0307150e0d0c110913060c03020d0218030c15040501030b0d0605010807060305010b0f07030503090a0b090d120e060c0d0f0c0518040519090309 72
    0x1120540414000c003d98002d4400305450000d100c0341c03d0041109042c2c1c2d025502200000399440c0315400050101d04202100743c440080990030000141481540c00705581079400c404c07800c281c0ea0181d01019039050300003040c410b0302d0000b1f0700c1c411041c98443c2082c00110383d580e4082014140d2501d009860070040500380c0c0103030780081041e019150082c01420016107410031030052030b184161505c8400b030b451b580543e0000d000e1441100e040c9034441c0c3d28291141d4802c0030307180d81c445c3d10840411540d42c40741152507440703516000f8100428900000401d01d040000165414003445884841c50290b0355036084800703030406042d4520520911015000152080107070a2080d0311a40082c420301445c28001000034080a0344041154900030704040544000300d0429070180c0b2400c44aa5a987c400c1104802002c0000c001d0003103e20741a403400710345501c100200301c41c410b01368680b078229000400300012500241c2d1192070300360402044103115207030f5401a0400c1802410000d820b60b603200802 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 109240161 1250 109238911 109238929
    0x405030d0503040804270c0c030503060f01020705031203060109060c0206070609060b03012906030f04020f130c03020301060e04150501110708030408060906010806150d0819030b1311030c0306030c 86
    0x900341320006c80303034140c82d07038107a44500040b0036150711f0032804c4003440e518080c2c07407441f0103040030380a560044201861a402000740100600000d0304980603206640203803401c07a041a100180000c000c0c003000111280310b8140391003400c0e001045030749445270580d100401081466411140c0a89030384002150355000c8c41b804130052655680c1c0700810214940010113400c928440603c665818014082d04c18041c1c16000d6101c0c1d410341c3d00c0103440d55104000303014403814580c0c0103085410042c10019895068026504995031500c0340b101000d03c40d010801034408482924000190f400c00c100555031080c1843c403580c8901e0790030740c0c001d41c1d140d150450840d44a500501c902c0d520a8080c000500c90410500340100000c078041c01490030007881141443c0400c81c205481400143c00101c140120f10044442c0d100402007011303407200c0c000c480a0083c00580720094454005c0c2202c0a5940500340075469024440c0070351585035580345c0303004e246940c00143c01c0316003512840701d000203e92503480d88 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 109241411 1250 109240161 109240199
    0xc0201050601021603050601090c171e01060309120e060906040902040e01051f030209010201022104060c020d0207032004050705030405010e07030f02010c0303090b01150e04020405030d0503040804 86
    0x460549001c0d0000380c94440b00005911200b03842c00020008a900803a415064030444000422420140f003411500426449603d51840441106221701d1400c50a9400501100304a40071650380e603c140035000c85440490150001d0301c02300483d0340b007603c40c6481300800140140164242030700305010483c42e8120707400100e0602d500240900801145c050b5042c0141402c45e10031001003c2c4d10b031801c4d072003803d40100209042e00031650081d180e001703405a906203415401e110880e440411400c3d043c03100c0c03d403001d640c101d01d80408555921301c086071800040841d500101404c40c82c0d035686801d01480b149540c0741215082041880c25a5a030050754001d01203551515140d00341400c01e01e00711003002200d00c6440e0300085040000030040241c0d0f026290702420507041d07000503410f056014080f2100c009094030201d10001c5a034800d81580c43c2441a0035070703652500743c01c1590034801244034600400341d0540c8944040303002144680015a44144251245401c050340c8405900c0c005a148074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 109242661 1250 109241411 109241413
    0x807020118151d0a05010903021c020d0b0a050a0c0e0105090310050109060f060c0f0303020304050a1703150a080304052e170f060109050f0301060e040b06010201051b0414010e040c02 80
    0x2030002800103c00d00303110809481180d2400519217840b00280021280d448024041c0100e6919840e15040540080f00310603000f0b02010180c002d640303040302080b402107410010081c50034011030409000c0b8800e0349200d000546070380400d4000c0000540d5213402c80701c492a8584542c921141140b0194000c080c001c000b90807021541d241401c4100c0c83e0400c541e0403050412034122000d0002c103040701011040c49405080c0140d0303d481c1c500340542044420f500140601001303000003003c80c00100300030b5219100040040012404403020454200800e209015a40d84180070a2203180b60a42c0300c5d030388640104251441c02900345281c0c80c01c1703146d2001c0c0900441c07501e1000101c50001603000d03990000319910b0b138010f1031070300c00000b91000c801805114020b500080d402c0c840341c0c80961001d00074129191400c84a0700c2c103443e244003540c008640703e82c0154202804101401044c4601242c6242c080c1d0000d0304060501c0000140003001c2c4011904124010701943c2c16511030b1307c22880420390540c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 109243911 1250 109242661 109242677
    0x61306090e06011508011a0c030703020a02040f02070b0f060f09010b0306040507030608031b01110d0603060b06030402030604110102011103070c03020609060705090f040917030a0b030a080702011815 87
    0x400c607241440c105a0041075204107043d145103e607030b4051420b6064954411140b04008811403001195002c0c0305c8202d0214800080c084040c150002050314089108440611074400e61071082c100b45d000e40440101001101c401040120784804000d5602660180c0949143d40c40c1e10001401f5000c20303803144001e190b000050007540d08103806901d81c0505103080600441d0300c1e1209580d0741e0311408035500505500101c2010001c075084d00417440080280000f00e8903040c1c1a44450b0003001580700c12500d0602e8050102c401d4181201603a126030303001405490305a607180c031928554646904094115541c40d9412500c0c210320202a42c090a03050396840030b07884240c40c0181c035001001c1c00e44210b41d845201000a441c0d4004d04880314214181d400d411041c0200c408100a09010200100611910520007070b40800c0d0310051441000900014040c100c480b6062580355241e0302c102030305500d810842c0d180554056441c02e04091002900c40d8092591003000741d007155400000d44001540c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 109245161 1250 109243911 109243931
    0x11030c0c1504020108010b0a140406030c0e04050907170f03070b0717220303330608070e040b010e031e010b221d0f0c0108010603050f0f06130609 64
    0x2000080e100c0c01207801e01e2203290034241c0001e008503005200307008a00c800002e110805601c500281551000c00c108000c0d1a56155100900907000d81044000040c02c01d0703036030800c0c600d054044c403030140710804040d182c03942c24403100765440c40100b8030212107840340d1003541c092414108000d000850280790315109609007070300020406e801c0350005580c01142401440f0304940440c41c2001405051074159035190070500e03040e400f90605511b48c0b02265041c2c003064449295644280d100e0309640080c8460040d1148014ad8403481c0c07d8484d01c0c0003c20710340400700c0500b01540f00250400050604102e40c000b10b40c0060b02e03108035058002034041c144020560129003d001c0d0700c035500e0007282c54000d4494000c0904141d0a09520b400c0e4140761110103c2007a00c0b41e50144140c04140407042d00d4a02c0e21005059903503541c3c592080f400030b0910340001800520078400ca0b8060703105000c03d4195a2201510f10441034805031080d03274020400110f8028001c058800c50740100741501c00490315400f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 109246411 1250 109245161 109245163
    0xc02090a09050c06180901080d170705070303021c02030a1b050901080402041808030406050709090501030302030703030c02070b040e01080c0d02061209100609021c0b01090303050d11030c0c 83
    0x80c2000d44100c0c2000c05840000b0300214401c20f042d14140c1d402c503244da0361801c00c00340c41c0310070356504d9030081541c1001280740707031012895041101c1c981d00c0e010355814055a2039248400102c4000000900600034040020b1180c0c009080b880000710442c01c12425800200b4201c0c0d02c151100403840342e0b150f45030103d8101c481c0e0b0040d0300c9061424224100b0007101d002805110000380f00922665484c0400e145007a00e1682e0052043d802000054803450207280c00030062601303464410201d090315030001580b1045019080c1a2039041d80907600340402503034141e0107800000d2500742075016102c00803c0006440010700000e00550303508584030351400021906080022251901034603040c40700700c003d40c48190464041c200c2c0c00540407072590318440c48508000d41007070480a00c50a001c0c00148100980d00070b031a0440e09104c94800b03403021715040b0f508a0b1490055039004c1a0707003443c10400f081c0980c000c0d00b4120703032207200400d145900703089000042c0e10446a140f20810041440000294 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 109247661 1250 109246411 109246429
    0x8030a021e25060e01090807061a13050915090d0e0402090904080304050309031002070b0702060402031e1204120b0f100b07060e0f1b03012901020304080703030c02 72
    0x1c2107210710716010206041d840000d052104069281d0188078a6108100d4035501400100035500005c000700030107441c103034019034000e0605803052410250100310003009840184408040103060b8641c0e14524420200170340070040010059006425481340d140000314603080c4241c42070800380c5490700f85028094440e03d100112180214418400400319894a44440740c01a42001c241616555149440762541c4100100346415004a00d540c0012100030740141070200d10900203622140c1c0d40c2c01d000ca0b0359040880d0702075031503403006101c3d41e0311803098404602d1140c0c0d108155a020314140c2c1c1040d04aa22030b41c0070100b65182c0300c100c1030501101c518199003102d16070804182034108507201c1d42e1100300e540280c078004040015050304011680d03014910102189096880b080c1c08061110344035901110700e41000d00c02413600b0790883ca03040c801c100950741c1d0f007070419281f9001c10180f07052040c40c80e8540341c1980300c01c110100d807240c0c0c104000c3c0003c5100769912601890944140070580c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 109248911 1250 109247661 109247707
    0x4031413060503010504150b0328060b0315030307030e10030e1507030c02030705070603020307030209190504060b0c100b0604030b040602030604060906030222110d1b0206010510180308030a02 84
    0x1c1f800c1e0800b80a00c8806d1000c40b41c002d0840c2e120320950f1940b07490100d11095440e408411501c0c600300c80001c18a9070038018500c202440210390815070103034410b054691050902c010002400d00d41814000c0c5024401e43c0d1a400d418074000400b420b5604140385803043e58580200650010b00400151702d0f4580140307140305031948095800c0c400a039460340c0d640c1c95180240c03801d15401000207140c080c405c5c0c0c1544c18007600204580c1e10a048000b51220402950081c64011424100040b8402d00000100c84690b5070314801041d040c0c2c2c2c25031000d40102055a50346511040411000010511621506008074006e00d0b0060b981c0c1000d4041004071a4140e0052a800342803080800150381c9030325500b0046a42e40d00c500b810600310a1005c0000d04042070f50f08548800498580f1039124190b100c2d69426007004000c0c42000303000c0c041a40e440400f40700d11a4020040070600010381e1086000728a142c1950542e00655070300e991754444282c000300d501c101e000d54041004d01e044100351000504207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 109250161 1250 109248911 109248941
    0x30c0c081501090507020309040606050703030c03051e041103060705120f04020108040305091915031a0a05060c0a1a1509040507051203070b0403090e01090c050304031413060503010504 81
    0x84080c1089030007100500c6900c0c0402d0b9500f002078007140c000c3c0201c0e424204020800c200243c0c1b540d502400680088074140c0000b0302d0111440c41e400d0191013514004c9900c070503949080c540c054071000780c0002c014401c440403160611055040d844c100210ba004e80301319120075442c4c40d400d1501c6290400d00034040145081d464040c400586d0700900c0080e003041c0c2500d8410b98030a8400041441b454800701688002c0c610141c1c00940321400712428030a01c44181d4040c0540d51511021951040540050940c8402e10200030006440d10390018400649114261130000c035481c2c44620a000c650100c03540002091002c001030340c480c03402d182403802821600301c0320b5814540c80e070356038401c2d40d4000c4c9801150750207000d100280d82002520002603124020003154903003450b0060104070184220740070300300100c002280e1407040f030180c144180c41c590740300c904582d100d440071141006244144240c40c0c2d8100489000c008101107164050000b81e00c0b0300d075036075240406010407584240300d40406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 109251411 1250 109250161 109250173
    0x3120212011809030c061a0310020a02210a0e2b02090708190c02070b0c0705010801060f0e01050702010509030d03051816050f04060b0d06090b0603070813110a03030c0c08 75
    0x41c1d000812178603100d800c50800101d0304019000102c81c45014621f981c0e03d80714507644100c404403203400a020444080c0d095a4400d56410043e200c0842c110b000320052031024011000010311403443c2c40e00b04907006112480c02d2191103a4155204101d104c5200c003690343c101c1c084d0030350070b1040441d50400158500f000140c5407000c0d4400e02c24880b10b03460382e9a580c071100c160700030758420804070020300701a082103a500d4031800b580507500c0c940c82c402e1901050f8020000903120f800f07800000c001c0125500d4102c0ea0090030001154154043e010403814000c0500140c0041c0d10100010081241c40c0e17200000c080c2800c00b4144100c50f0140e17000d450b1980a0038180d100d80801a450300f084540a848402007000b060b80020302410a5400c44254108042140e1400c030149070404000c4801c100d0007002240e4001091280d40d00c002c64101d001304000002248115044c0d03503009400d9401030841d100e0060900c00001c4d100e1100c0d034026400501c403900180b050040d0404a1401400002d0007010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 109252661 1250 109251411 109251413
    0x40311010507020d0b070e04150812130b160c030503030912270d06240608040b0f100305010507050a0801050405070206040201120e01050c040e070801051c03120212011809 75
    0x8070804c40a500400e04403031240070800c02401480070f0b8a003c500108180010602080c0c2c0c0362521149200305021072107a0290000040102011180c0d840040d07181d0012a82c10004000a6940002e8241318610070310410803000c10765100e2944051071184018503a6410481160b902e810001e0b8004820301d0020070898880440d54214168005050b100d645484064000018855080140c01516650a1005251070010150314071650141d04090160780d940d1104012111303a1001c44004249950a0300410342c861014481c513688884403940503500c660f246d0b52824259507060f03c45d100030a001299001ca480d40100c01140501400e540c2002585040800290303112800b410107814807208540042c0f505000d500a0120b03803003004000c1c001410b211074110103e038000d200340c6003507041100108210610441c03125040389d200800950a503c2031040152643c0160602103040c020442940c280070070b014005040d0b907200303005800101f58074048400c22f0045904140901051410850b00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 109253911 1250 109252661 109252669
    0xb010809100e21031b13030201030b19150e01020f1504020a0305070b030703140906010e0a0923010c02150c09060409140709150c02190510020304031101050702 70
    0x400300644141c40030900824080c241424007101000021407081915610714007080c4078001140030726404030100342020070310701003003006000b6101c0302411001890010000340d0b109401140c50220002d180100341e402080d802c0105080720b03403258602100301c00d80d006910750010401041c4071001e0020b0043d180001d058941c60b50103070080580d080c259200400c0540d21030003800f1001c0c55004003240c44540d00c07107884035940e800c1107528100003428014003103c241a428580340c0641e503c2401464103900b0b0840c0384104200042451140390350780c0361544003007803c04580c041024074080d035501103030640e01001c0e801c0d9000c00500c1c5055502c05002a1050480c44021a074007000c010341940d100c40b41c074400a6603c0c41154469075446007060b1021f00613141c0d0390f44c5980240305a032241031503140c1d101e40b002c0c02c00841d400c090005c1617194a811000d410301c888402000703604680caa81b012601c5200254500504240e2080103900c08a0144100300322041140040d40c02424060f0a02c6120741c001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 109255161 1250 109253911 109253923
    0x1050f0a1212020c130f0501050a030809010c06110a2f0601060507050a020a0b120603120d0509012a0201051b0301060507020a0b03070c0501050c041202061b030d05010305010b010809 80
    0x8000866a04140c2d800c00d10a01401e618540018030f00d03084480045051005443c1070499241c0b99031418000054074640040110201c0c0d60112885041030421401552a007901c9101500c2e2991030b91340c8101000c141600511a8429035101c0e08240c90300e0130100340101002c8882c9104030042058000207075800001e00c40d04444c424035010f6550401c03490014241b424604c4003d40102e4094008119405520091b01840c0c114090a0322140e031000700300f654608525014a01c00340040284c40c100510603000258840d909200200d8422070290f00c6403400310708003201c20200203000710b6060314180c0c207004054200c0408181c400407900c12045805591006126007414481d0005d076079000c648420300c000300280580e050041c1c0340e2801e504058904480c010f411245540b0381000100710003240310641d815181880040c3c49800c046500b400035960101d0310005040625a82041e0911010130041500c0c0f20381200c04038055142d490b00900352051102e581e418800903100304110000000fa003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 109256411 1250 109255161 109255163
    0x10509031b0f01020403060b03101a010e0a17010c080702210306010c05070602031e0309060103110a09020d0f06060804030e13020c19140303040b040f111801050f0a12 73
    0x307109a0040303010550345006203101608807194004680041448010b911201042070b040d400d03252004c0784005a0030448510955a40b105490903040b16002d5120710800109440040e04801e0b0090304c8540d40c481c41450740791042420f83d1900200c0400079030249207103410080600007403000d004428402c0003402134440c903c81d4800700100003e00315a00c259000c102140c0c120041d05c10103522800d00944950110206480c10326070a090103c420640c07204072072044481002401a50b400d582e103c0013201003092900303502c5514401c000c604003071248010641543c040c00005009901002140240e86140d0f122000744034030501000086904140c00f0006024102c50b61b080103c80442054024061103050440d544203007000b001d5141685180010282d00a1100e0311000e144045101c0e030701e100480e00208102980c1012400054a2a02e08a4800c2c4142c140014411b081c10100b00c0c0d035440807031500b075002005070040005003401c2c0091100844261605005a41000c6c04000c001c004543c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 109257661 1250 109256411 109256437
    0xf050705060f040510142109070f12060e070612050c07030806010809030408010c09050a080609030a1b06092604050102030f07021807110105091603060b040f020c070e0901050903 78
    0x16002d6102c52003540d418588400e1046d10f5a21090700349002d1600300b000410000d0f0050b0514081050f101000466804841191080346c0400e07003440454922100548421900b098880700c140c1000d280602c80a000f401072a91150010a403041084054400c05058a05101820410100404d42c00605d4692040b0700382055041511030754181840d5110b65440200a5480c100c00c54104561214071801100c4048410313400103501c0320907041d283c800c1524140700941c801c000002800b4000c03001e50a001c40040410b5680e4282620383c4019981c0d40c07241100e0020107070301c2d940f040c540a04170400302d0b03840c00301d1050704247c06c284c0040d40d60701c911a0460742ca8003005c1151002c40d502c20300c280038100d40c035110f000001d0134401000342004101c1c0c880c0401035421b00c0001068500c000130044c150030746d988082c481052035516050014490301020981260b125244141c16078110300050516809031001040343c503281046142c044903000c1c0c0142000d074105020b02111000000594500030240c00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 109258911 1250 109257661 109257679
    0x2060703090308030a02070b090601060917030409181209030309060e03100c0c0302150f0a0f02090d03050c0c01140316051908060a050102031207120605030102070f050705060f0405 79
    0x10809454010705035000030300e0154000200030501081d030300540702c014880d11101c10785850302180181c448509024200004546c2442048000c8440070407844070200c000c280e91625455000040035503034501103002d2940b404c0403511041061a07048007005401c4c038a0036039651419581c006283c81d60a204c0e5504120005814801c40c2d90184514461040318040403c0701c0b00814201510b11200080e054001d80a90b4800f450501028600948103203141e100040b41551240700100003130000c46003484c0055801d2041c2c8049854401d14050154003c3e22800d40354948010b4251800038030b50110b50410501c110705566050144050302c0e0000316624001002c404000e00845080c041c9040040280c1200300950b2550398010203414018001034503922a01c88c1c5440040e07a8910a003a4142184019a400104507610800320500014074402d0041a81070b62400041e003a600003000030364101c00c00040e4501080010040000144401d580117420110301c3d1400c803400e80614401c0328020100c0d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 109260161 1250 109258911 109258913
    0xc06021b0609011b0b060109080715080a06170a021011120705031207050408010606091202091807091a0405010f09020d0603020a0e06130203060f010c150204060503101d04020607 78
    0x36104a288a4030b004e10294201c0c0498140884120030954805010855103140402c019101161070029a0f4207500ca4140498641d03200310351545000300143c2d8080d554003408501000310501d0450314003100390080007026018010040244030103103a640c00c0c8403140d0780000d030041010500d41000c0038621400d030f0b00c0b0075507428003e04500c1f4012810f03511611010810107642d4210f03000c1c10a44404d40700801805450301c4064506009070b004500c1564040d851600c0140f8002c0d0b1841e90040301d600b4107a0716a00c400052034580b950720b42100703900f141c9a800c003045500c404000710140200840d828803031545480104404414503000f0080c0c05500054034641414480c1c03c0343c001194050031003a2016900c5c0c0070720031414429541c11303118404c0400072000c103c01e18000d4a001c0c080062042140c030521000544503000e4149044440d08d03400c91100140c04807520140c0b000f80100d0b01d50903560b00d440c0c0d500b017109000c2e41d040300c04c07030240d444c04407810022105041a48a5416210340756520b0103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 109261411 1250 109260161 109260167
    0x9060312040f0f06032711041d0c0a030209010b07051603080a030f060f0b090102010b1512071106040b15030d030e0d0e03030a081e010e040c06021b060901 68
    0x188203403480200041c009001102206104102c49035030301e040003281d458020440580b01c1d0380a010f1200321100c2d82941c1c0090764000c1e4031203c2031054941c01c0c0307d40d070038102040030f0b2440c0f50a080c01c0d81c00c041c11100c6005a0a004014070800d0455004100714115070025804600c1030064010301c00000c1a007a0810000f00300031a00d6192084003400030a0740ca142c049210b0340080c42860001e42032107a8114032856074060b020550b0209100f01d040c050a043c00c003c2039410423002c1d54110364888a0310b10030f60b207402103005c00464121256681d50140c2e0084030074407840240404d403c210101038501e100c102c000c15016000f55100041807203d482c2e264040c900b040c45640d0255040c060412002c410380d4040d44030591501c8a1300542c0d541f10340c0050f00b514001c00100540d80c040d0410030504d2a414031030721351a5400004405031083c500880d02100c142e0300302c01d0b08080c1454078039a080c0401c0c000d003119502e000f41540d20007010b0a401d030310145130704034903c2002c8500503040404c00400300d0380 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 109262661 1250 109261411 109261423
    0x412110f1207230c13020708041202040506062503030603050d090806090c280b0c0c041a03030a031e021813020a0206131a091e030c070302090603 64
    0x10001196008000408081460340c00b21004031a0440c1946103414580f5505400c420240c003a54003600012036000240051510030400c4002059800c1140c0000030b41e440e0302400140260300c134030b220060440d00c144003c0711009444035205000038003000c00441030045000300505585107003c0707100582c42c079066003e4003050300000c0060061a46103200c030350b0300ca9224002c0f1174100b81250610b40750003580c0341d00e95406900542c2c0040315045d41d02c45078884004014001318405183c16813490307071001c032003400c0d8000140440c2a6000030b40008858038050084042016100824520740103200c800a0750ba80b041c07144980c241900d5440850010020840b00b02000314819015075444000304c117458422000150910301c1815901d0321480d2014213842038170000309098004100c182c482481240710032042600440b81e00c1d0401040080400100300000c0c0030790040c9005010084506608003281d038082001c815056006001541020400042d501e0072a90152040005600c801011a003402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 109263911 1250 109262661 109262683
    0xe0309040203130c0504150b0c1204030c080601090b0105030f0601030e0f0a02090c0903060106050d0b1905031005090d120b04020412120804051209040b04050a0609060905041211 78
    0x1d1010003001010348a43e000251150f02c50302089483c3d68545003008111118640d41c44100c0380e03c042c1c00c0c048000408010101c0300d85d01002c50300f240501102e0b040351688540c104071070100c80a2002c014140c3d08010302400b50600e1082844130b0070400e400200346000c01403040c4645041040801c5840e4002d62100301c0340d0505d48103130784040501c0c050241e6105864001240100c2400001442e40610030f000e0312001034005025040c2ca0b40f078580c007103a007a040358202c1052199a01241000355a80000744081e50407840901c8007054986001c040c20186041d00300e0341814241420012180c0000c100881d50070110704004006401701c030380920040403804811500148009000705240f0006107140c90746510816140c071031118140b8040700da42000360390083c0290700044200403465280c00103031207d22000b802c0015506042c40c0010269407040e200303500e2107030350740e070051010241c18041d40019004c08030062049041550300c4400040d81d0340039000800c4506a205039480318184480121a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 109265161 1250 109263911 109263919
    0x9060a23040b1006080603030a0e01140a09060e120c060a1b050609071e05041e090318080312040204050604110d021c060e0708071e030504060b09011203030e0309 71
    0x1441e0602d81103401280c10380c0d0041d20310300100ea000651314418030002d40f141d00094080c500b001d810800555407011000d417428140601550710084e0140c417100035000c2c501080d611848018a080000340c5040c181c1c041c0d060144a40c103c04006110000464094100c02910b00950b104030012080b51040103542e4584100a1492500404d201e40041c146020705c1c1e29a064408660ba100009801c0002001001c0042c0c3d0444904200340c1c6442c5c0d000340f09403040c0e840c1020500038498150070485090200840c0030841c10107984003400c1c01906420003900321600114941100300034174000c079100c003e10081c804c40e04c45001443c01d031910b80240042c42040c06220b52900030a00c41da0002c2c1d004003080e1039000da11409540300310040343c01564101d941c8001e0910300f540b11600102d40000008080070244020f040d400500c0c2c60703c0c8802e405c6004010341d000a0705040510340801a5070275661000d1285074500014044480c2c51203075880c0355541420b0018070350345150364490030f40c0500340148d0343c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 109266411 1250 109265161 109265231
    0x903212703020f090f0115020712030c0501050f01120605090f011e200403030c02030a05030a0309113106120804050f12030d020702030a06090302030c1509060a 70
    0xe4500140424020340c1d20845440e80784800d44000d0041c1460121401d400d4002c111004000300180c0c103500701040c0034140705135081c40d500e03007101c0c8614013058101100020040341c1403030305122003803140710f81100c050300082c1140c1d45840b1103000500494000644110358030400300e801030320208200c043c4500744400074011106a1100462000300c4021039413811801c14075404041d00004c0001000481c110b61101d0401d400c40e1022600d540c022a03040b60148104400b202c0861000c0002d868020416035000c00c8416092404640854000d031a02c0d0040b5500d9100e454607014a04181c0020844030400c0c102d0380011000020140806a11441e00260784114003402e001c0f41500030001c0d19410b4032144103e408030002e1140506280300d06035070a8005000380e10340d41505400515006000070225528000d151b1203407800c036810008110050b90000890710b800300018880c01d00404803610301d00109180c0070b24904d072201e00081180c41c0c1160313070312a403e11000b5804203046c114410071450a070313 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 109267661 1250 109266411 109266467
    0x6180b1f0201020408120f04090902030c040e01050114040b06190207030b09070608010501020a0b060108071101060b0309010b0109080d050706021b010510170304050d0606030b0906060907090321 85
    0x2c000e501c9405005454003c903100f40000c0c0211000311070900c403c42c00c0c0b040c603062a01c582c610080c031642408a030306000322315440d40c490307803a40030b0500b04105444c000244d6514002d094090036500804048c0180d0400b48503190603602c1d44151030344800341048107413089409a6040b420840243c02c02040084054140b19802d400004c110041d44c1107504d07540b003a80d03210401a42d45840c4404018910401c4800048c3d040d4490820580c00a04509101c4e1b448510b049a103401c3d070b0308980000c00349400c04003c00107000001d0007100508842070802e0714449041081d20b80e12102c1129503d41031081c00280c8008201d01c03941120000a56465208244400040789a019220640e1070360600c0095442c00314266071a101d42040b0208a20025440c00d8030308400c1c40b061308415207041c2d86403030380c607200040881d00442c80c1c944603424000240060380340180c10061003200182c46081040704150017480000c4080c04501e4401100d031a01c01280c0004c607030119601c109288030313011140b4120708040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 109268911 1250 109267661 109267663
    0x30b070306050f060c100b01020f0f06040204270609020f0604120212070b0409150e010b0d050c070309050603040f02040e0d020f010b100507030e0a0e0906060406180b1f02 75
    0x50301c0007202d0a5a0075080366040000354010707200202200d800c11417459146c03604c1c41e8802d140514040c016288950b01001a45090001000d01503159801040130001185007034400d100c9116880c180c5400116400c00c05500c1c08030402d8030003403200b40d40740000741c29907860045c1034008040c0145025a03d540700d41400c1d10000c000135040340968041d41d01e803910018042000c0301555903820403142024500109400030f00300711072844c030f81d4480d8000b0100d0500c0550f15003501074210504015030f00d00440c0d80c800121107000f0300d110b10440040c0048400aa8412003510440e90101c40d455120385035428a14172041c3e6610700254440d28024022242e05d0b40030807003d170f10b0035542d000c3e18020140103052a0a88503111603841d844800a40004025030044025102050117441e0552800f03400070701099401480d03801c2a09150000402c0004100007000001d900c03c0d01a60f0900180c0d2410389155124140703e240001d41d1615a5460400c940b64105214091680e0340750981040000f07060103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 109270161 1250 109268911 109268921
    0x100f0b070605070804110f01111b120706080f04030e1e1305060f010f050409050f0402040b100c170c011118030a030206060108070306080a060606080723090307030b0703 74
    0x101c500504000018284900035440944940d130800001031411094401700282001800c0d9000e050100c43d0010004149082100b0310b0680d4884001074140b9508900b0440f0700070229400e180c2c240c2c4000c03800c3c8001548404995000500c500d0f88604a481c0e42c6800d54182c0207824041d80c2084802a082d0300b01400e24009150010302518000494607062101c0380584200300d90198009018a00c2c221995209401c0c100d410300d203c0c5049420243c0711112030382614001d80d60503070304d1914442800301f9403800d4422030720380e01c00031514070182d9005010090018030076000058111110300800c0c3c042c002255048406181000008001501c10008110301680142000888003503101201804500707001441d11041c07509034004012698480300110f0b03e00200419000c00c0648512000079500d508210b4483c175944191008540036061510051017031500400c0941004003881c002c001c410200700034504840c402002860759070640740e000c240b03000301d0703544000c0000310f2140030491119415842 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 109271411 1250 109270161 109270163
    0x3030c0d030518033a06061b0b060f04110d0218040e120c0102040914071e140c07030c1e060e010f051b0607021e060c0909100f0b07 58
    0xc02c03032a110400480c0c01400340c20741c143c965034010015010b900000d121140041444085801d00400030060039591300140075044001481e240c3c00180302c20b94021010018504810200301d544280341d407606040041c01600007130044241c0024a00b00341c4854011000c204c42c0b14907016524546ca82c4800000e50081d0024801e0f900c810000707807030610f0310313000e80451001071a0007000c4042149100c5142948500400d490700d40d030800002454040500913010314110382c107010703907461800c0c07403024020140450300c1305694000115180e21040c0c100420005002d50110b419031a80e4040d901146041c205400c046d020340e0701d56900150341c80c0841d41c4504d007040a00050503c6540e030702e01c15906000f1a42c0850b0220f040c16541030181d81c030540c040c000034001c3e405610341e0421140ca001d42041000d03651303400140c11800303214241200302c01a080f404500716000340300b20329190031051014007404400c41e100e904024080380d4244204602d6602030003d1000744d0521a98600001440d03500c0400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 109272661 1250 109271411 109271417
    0xc020f1f031a09160e10030f0f06050102190303090b1513020f0306090a0207060903050c010b19030303110409020a020d0801050f0d02090a1e02070c08030310030b060d0203030c0d 78
    0x10504052079102c00403041992405080007503182c8480307041c3c4c0a40d1450808400401441c014072032510354980102070010407a42c0c400046071180140c0743c1e4190b664107140803880b2804c00e4003c00c07140c0d0380001d10013007039452035800403250110f900d41100a04030584014101003d60003c1c0080240003103a40f8111100803541b00310b588a520192006a001b20784144d170506c8000c0c40000c00c81d04003a10300a910243c1048014a4800035903280c6003101e80ca4481035001410120b0079003001402413184121600d411503074440b11404021f84121402600c3c0030060403d922802d100d050745c0c40c50310a032006000218400e540f02e560940c07009550700701180c1c4002c0018070050002802d0b040400c01c40c840d110000e071801c2c1001082e40c09000c0030880c0503000000555451171060305070f511007140d101d0450440c40d030142c2e458000b410f1002e0860785540081d000c85c0c008100780b100041d050307548882120340c0700030006581d83c2d41c01e00050103c0b21105010390180000550000311701000305071402c02d050399031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 109273911 1250 109272661 109272671
    0x9120706110f0304050603040303060506070605100b04080304050d0206040e040b2401051902071a0d05010f050d0311210d06080303011a0f0702040204150201050a0b100c020f1f03 78
    0x1800302d0341c1d241e601c038003150950004c0009101c281051300085a01901909010420650394000f10310136510001d009c3d22516a81ca040c4108007904140341c074000c1104040c418101400c1904464480c400c0f80310b42403103005580c4042046403070780c80070b4600418021103039030810324060400061410044850b031811192074a0080340c7c0c00d0945600200e0f17503106942e15800c2c01c00d030100590103000041c3c50707a0306500c504500081d10207088901d14400c103999611054131850900b0a030016640c041c0c000246c0084990303400d1066854030039209960780d0701841c0c804480101817240314202002d0710350354909000380001e5030304a038903000700401038203504010800c0315070342d603802c800d460380001c0c068210307100d06204040d810700c590140034144d8600030012540c600309446c0d0000d001c0380d00951000a420b41d0001c04503900a40a10405622009001084c4040c180d410300044681c10160940030520602440180a41d29101b6180c505c03040c000c1e083c103401c6d100d002aa00049402c1401d403070300181c105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 109275161 1250 109273911 109273937
    0x813140604031107030f031209050d0210200f1602040501060503060102060a110405060d0f05040501090209090102090a2c0a050114030a02030d0302030c07050706030f1805070311010509120706 84
    0xe880340490390001182c1024006d10340d41107846101103014a01c42c151203414490200c1d9080c044d60082056a40050100010055a80e01683c4034600c1288110140910746800c0310803036030131100301292500700281c0da000441c03061790a0750116000070303400902d440300208865030408019030040e00d00b6000c0b10388907550000440e050302e101d98041803903503070b05010402641c10303e2000342a91862402010425015001e90365048410441d0252280d2f91181042c005508200e86001e805c18540300c002c1d45045e0060b001700742140080e21404c000400c510300e91a0780d00c02071044031043c0c4c1c0b120862050040c1407600c2d18201902c000cac00740d152451600750b0342c1300071450002040002241d000e03000c0c0180d00d03c9828190003d4000070000e00c504c0600f00000800a0001d2041502410198a00154501c601d05202080f54611008a0750700d05841ca56200410300004052003126131000448140841c1040100c8980c0148038109030003114031105008130003408036000e000d46246d0780c0c038070606c0b40700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 109276411 1250 109275161 109275163
    0x40b09010b030d030b0105090306190c020f0d12020c010c030e070801061802030601020c03070905040b070302030402010c06200403140d0507080d0c0e06040602160b041508131406040311 81
    0x203a100e500d070b4140d00c0300d6594140380d401381d002580842c0c1305040082c05c000c43c0c600400d051507812224030200600041c007186035460302e44a00180c8105910080c0b10303000301c5001c4565078890861701241031050036102128000d030340350129042c2034070400003071090030303840710300039000e000b2002507000e00e40110703500070030800390521560003210360354561400c9003d109240f80c0d00135070020381490b04501400320204896103040000074020903810400042c0f600e4241000b201d089409451181011300410030701c400b41c0c1c2d0200c204082c26810510005071010031801401c8101070701500e111544c10045400820f110100c2e964296a04000040d00c44101c07003100116000d12030864010a551020b125101c1440000d03800710f103141205c2c0c14824003424030a400910103820a44c071080c0140d00540064070300c2c82c140501e080007403080b08241c40c281418007540108210035002c400d02001480f000203900c4048162080d612260000f00200e10028440142c036100c2c4030440c0c0031350200e404240c1000c95203030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 109277661 1250 109276411 109276421
    0x1401110c011a0609060a080603070902040303050309070801060f0509100f06030c1202090123041a040302040c18091503020a060e2403160203090306010f0f0602060f0a0213030c06020303040b0901 85
    0x3000411852626011b42400e40d00b620001d8a525018401c2074408110700d085407000744065402925040d46034038110f076103140b90000c140c1040c140d0f6410220308004000044200c0380c155401180c041e80c01da690202c05840c0144140d01484c1c40314602180000c03045d070541e01511086038a9682e1002c19441c0544034020307481145091800606180340420101b020f84820a0031008070031103051409590340c003e80d070000d0310700f000d081c20007200050070130443c501803150007010903150811000102102c2c025144030b0603103205034a01c072a182c00c440f404096420781e008004e50b900410413210320b80c555000920282c0758060b954080c60300d0030a03141d42c1140407050100c0c0b50350200d080c546035558400b10b0141c05030342044034006520003400401040c0d6000e1107028081c00a09414450b030514003200c14440002d660300120945d000f640a01c08104900650b05038414004500540d03190741d281c14413480c4903c0e81c2c0c0050b181c00507004000c104c507640400118061805045000d000d0789135501c0c0309080310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 109278911 1250 109277661 109277677
    0x110901020714030a020f060d090602090a080d08160219080c070506130b13031a06030606060c1b06160b1501050a020a06050a1107080403022106041401110c011a06 71
    0x64080030b01d0703400519103110155081c1b0400b41165003041d070034208039010780d8103044040b6041500410016010309080020800a00d1100c004240c01c49038030201505540d000741c01168003150b07440c00c20146500802810755031201150465000c007056040c0b0300b2a60300003145003405409031060000b0607107084410740744804216490090958580562800b840d44002c401041c0301d42a4203001022407115a600e41c51007080b100034150034603007a801c25040000040130140318010502c01c01c1440c03800003c09241459900c20400e02d940702400019000d80221040b00c1807164500c14242d04110b261040b890050403001307034140c1100034031001900c0328001e032a0394a006910202155001c615583c220b140c205021000000e1a0f039000000e4202c154410441960b40c100000340400460414020b015031315840f1a03a14442d1901d40000c00780c03035642c09400500080c0c40e13141032106210080d844804410594114aa9210800070380940607025404c0340209030035102c5d2a000d024208242158019 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 109280161 1250 109278911 109278913
    0x406030b01180605210c0105040f03020405040501020c01050705041d1b0306040e0304080d14030f01060c080f040f0e06040504120311040b030708040c0f0506070602030402011211090102071403 84
    0x1507800c0c03a20300400902c0340440300c0e80d02c03600c0303100005a81d114943c20310340044440c904210700c2282d89400e54545030100446030704000d02000104448410f0744803507400c0c3d0358102c1b030124190300d450400e41d003e070007000c605000651804007071203041038010300208100d40c41100c08208120320080c1d0309100480c04c64508082c8641e9002844040c80700b0001036500407001400040c112104841851854109400c01d0701e1031390020660429260700081d03400c20f01c040c4401018554544401001c2d041441881042c086c0042c81051004000c203100c2520318aa040c401c425440d25992526400d01007051711502c44040d0708030300407038034604045c046c281c4540d400090744580d24803c0d4004030000c3c051840d00078100303403003800007145a0080400950040c0119a541106c030b0034141001c420076061503014440a504001c0200890703110b10f4144c401460f040100180c607a6520700040c2c5164201d4843c054190f40740407045411401d80d4805030031660001c0c3d0031100d031262910040004c0000c40e880700362b89 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 109281411 1250 109280161 109280183
    0x70f080a020d2d0b09150103020c0703080d02090a09090b220b0a020c061e0103080a050c06161e080c0a030219020a031803030f0c080405060706050a0b040603 69
    0x300d03241600108400003501100040c54034001e6920001098112030591036001c003920b500d41440820700580c82821403c5891590a04102c6441040903603005043c605168021448044d00001401000c009582120721580c0c0e8250319a0f44400943c0322100d128440e5041d100b01003605411813003845045607011000c50183c0c1c960160919100d8071449048100c0007a4101803800510694102800354009000c007584035171401040c45e0401000601041c8074920304011240c85044020080d0304480c3c0003650b4541e68420104111a17a02c00c41d070082e181841040107104010398952608074031300d003181d0344a03422806000c0b4030040740f800c8240800c000402400211b01c00111010007405d02c0401400d0061803c0c0340842220752542801d01100c0160300501e2030a01815000001c4509030415120400c0080307041d0754001d407a907440c1a50101c10880030120741c0f410000d59000f11006008010004c1d07882d241e051401c1c0018120440340c003621103041221000d1142840e001360002c0d0380d8081007203c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 109282661 1250 109281411 109281421
    0x19020f1912020f1b0705030d180806070c0303020306040b0d11030105061c1509060903020601030506011514091201060909060f1808280c051b03060c1c06060c0506070f08 74
    0x4c00403501034849540b03004d4070700000f03183d0b5400c0010f40b40f003500c50380707500c20741c150b420100c0001613020360b1040740b00b50440b508101c0c0f1240d0012816494690504005803242c0f1039401140040040316039843e000740c52454280b003070080c0760303071901c04468044000380820b9440d0800d01c000e0351030013405e02c80307400601050400000c000c1c10a518035090348103400500300600da00c40d00107684a07140c044d80582c001100500034002e0601915000d030041d036907040703442089144020502100201c400681c02c00c0854030311555030760b0b50151030030340c22040000d1041585808010000303140102c0200c900a14006290301c1d6001103000f000b4040045007a0003a12402d641c60b40c0902c1c0e800780d0700505c01c0400040d02c1e1030641c41c0d441c0034404403540b140c2c9c5100d0003a10714540945031201c2c00070100344034518000354060302c1c0c1e0b00003001da5100404545c1d85407655502e045400e00b06031403464422440e0305120001c145c1c2e40d800204014002d000b0000c07941c09440b060001c1c2c03408450b4503d414001500c1c40c0c0012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 109283911 1250 109282661 109282687
    0xf050d230903010207020603010e06010f080601091406070501050117010f2912060a0209150304240e06010902090102071e1a0705030c060411041419020f1912020f 71
    0x41041c00c0c0190026141030100d030b00145550388244c10092a246140381071002c2541d205455045070709aa04021816081c07500000c0d21b0302d00d880c07046844d61903030b041d00e11100c0e482e49010359905552200007480556115417040d00d200000c0041101151b28017401d0848402c81c1c0c2c0148454030392400e05140328400003400c1c0781c0965100d04502070b000004100c800b50058820007000e4812461070200588510f8003c04111a1101b12004204034120a0040c800400c0c07071045542e0f440d04140040d40052520701d52210050f2031651359030b08042c0568000000c42008580042c03050060903801d403039000e40c4070b02c2c010f012510b00c55481040320441c03039402d1100401c060002c952541800410b05d050910990b40c141c50359005c04040b5085030040c2051004000b240b140145010604603000e1144020344400c2c2200202d000700031500d80a4003018170a980d0a6940c120f074001e854500b07032150344074003612100c7c88045456000e6800038030024060007070b6203214809e40d44c0710308515043c0c9240a807120b0035a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 109285161 1250 109283911 109283917
    0x1080c0307020703051005091618050601020c03030c0a0203060609070207090902010e040c0302091503071d04090c17070902180609130213170d05340f050d23 69
    0x784040d88280d02d40400419030400041c0700700001650042101e19040000701d0400003240d12111800f00341c6c44092012194802988040310940c01300003c45685480c0101d10b042950780405805020004070a100c0300c0001c110380940b64000c3d02216010744984082c0080c48904455807001604003030303001e0040070b40ea030300410b2502d401450043c00d91180c0c9000141143d41e60040e640101c2c0c3d00003a00040c500b0f102890368284c0605042184c118680b800c2c5c041e01c19110348040c01302c043c0130a401c47c14030b03a54683c803140e482600f0801221324541c40b41301c0010000d058241003070f00740c0308040c0c0c0020088a170340200c0d69007010000c00e9410300402030060044540242280aa0140180e0b810320382e0958203102500c1025611a0341036000c6140c410a20a00000082c41e001540c0100d45186610368102081ba007015941400000e12000e44444201400030701aa80c804585c4031080400d050103c0c1058050710a80103000703a071400821100140c945804211580c0d148810b0400010305000d680409 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 109286411 1250 109285161 109285171
    0xf03060b0603060a03240f0e010f09080406120e060c03180c1e01120e16050301020906040608040507090c02010b01030c0f0c0305030903041707030302250e040c050402070c050f01020304030201080c03 87
    0x41644001295000d0162030315400210038a88d0fa5141c03405540001b402040c01214900404008141c0d158680c3c1c01c1511071400303110f0500c203940c2413080c120b14483d4052800a08040150740c0e0350b0400d103d81c40f1090f80103441c607454140100511400c00040440c030786441d142c000b044558403040c40c85100f40d4044a010b030b060b05100b00074510760404040f5010701c030102c05c1c1b10b00141540010900194905c3c0603660003c0380268414404a9006d80340c050423503050f01c52030f0a02c005e2564035468094134141c156001041000c0c10a240c2d0302266805400400f40b501090b2014086030382c909a00300d8000e0012841ba8002840000c4a5008240101c000310341000202003030f030385480c0c3c40304003001902018001080b550ba01000040080c50b6041c000341050122207148614400c1c0503180401e18861240203c8401e0110000031808008064840d5001031501610035900d0f9032650406058002c000d2064500804001e1405807040d0300c0401102c0a6940c142c490711000e440750402e507900382c0c00c0286 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 109287661 1250 109286411 109286453
    0x106030f0f0207050c090703020703050d050402030a0f060b1804020f013e0106060201060803030103060c02430b120405010b0918070614070809010e0a0f03060b0603060a03 75
    0x30000c052a0000b0303e0114010f000406600780500d041c000c00310380040400007051300c140128000240e005e4101c9080e40b44004e80403e554a0f01c0c00000e0602ca0038140061040e410140c84104100c942d8101036070381d07002202c0c1c0c91410106003410301d844c004101c40080d131080b4821116416580a00c3c10b003c88094243c0c56465115810901002e03180b0040750800031455401d5600e01010000340111000380c9007500c000e1200324a8484040e5030b034001030000a1405840d07240e60302d01c035482044803150040c1d40e103c2c0d000c620311102d12800700c0c0040b1b03a124415240d0340440c04501208090701320800312031800303035902d1070301d0382c0728200d4008408041c00c00c40c0c0554a92107455090f90700c444007503000d23807000740d0301e0b00702e020f642c42c0d069150941d140d00c070780c00380125000c0d02d0315180c08071003d556070580c0003241c0c25a140a41e0380103e82c401200304410741c0c009548840841c454021011103019207228800270842c4601c4001044050301040311040da01c4020f0200034800107090a41400c1505507540e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 109288911 1250 109287661 109287671
    0x120a0e192c0c090d0f11060313140a021f03020f0d0629030a0f1e1e050105060405010305040812091f020403020603060607032001050708150d23010207060b24030106030f 74
    0x3000100258402d540244040b8603002782d0906102c2c1e140e500c5c0300740900040092601d101560701241e003416450f01d0a00c61078241140d50099680a0380498070301c0408000c01030390b00c440b020040c6000b083c85000302c4c01d015800ca403114440300843e100c040c1c46810226a0381d41540e81e240e42c0700c80548220300041440d203031a171018420301e8a030b4002040b81b02030b20441c007041007080a50171000380004425107480141c2000c0040100d5118402190152403007031a02045a03651401d040a4911480004040281d8450304110700f4183c04950851114402e00a90403000c4046000906078025400701a44c401c104101081c800d140950040081521030f05160310450b01a80652142105a1080c140c259448004108089078420758585e44041c80d030110684040c01c80c80803a100381c400610040c400310810750034031800c040804a00703c2c412140d20003907603501ca0915100015040f802810340c010f400024600304801842d1a005408d44541ca101508603840d24400310040c1c4032122950803010350328 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 109290161 1250 109288911 109288943
    0xa050d0e060a090e1f1d1b071101030b09040309090c0e01120902150a08090606060c0c0904060e0a080c0114130f0303090204020f0309120a0e192c0c090d0f 68
    0x24a1780080100000c400110340c650186040d02e001010081811035842020302c3d0303008810b0140c2059038540e542004034074000e00c4a010050b801031101490302039000d103801040204255101e059407081e118000ca007400682001031060314074042c80c241c1c9601160000c140da0b4550402c5d40d01c410000b03030000f403c2020a400c0302c1846400c540c807881001c40000c00200810900e403000b0800e4130742000007507492078641580105003035181c0f030310300e8076040c4580c1c0b8550205050210b00d4008003d0480f0700c900b560200141444c01d641a9030050b60300d81b099500344955179020101c075400c40c070303c5800701081381c0034074680c0c84e980c5a2400506074811024940e554902c0d50240e280ca1016123905c002e1041c00035501e0628010080c6001d408140d80001c42d4002c000820317089501c404075900e00c26096403008480502460003d2000000e030700503206c0d6840d01c2c90800c00b90141200703203c0014a01944800c05030f121120480c0741c51003169001070b000041c404044c400500c4610229038a5806480e80c01c80401072 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 109291411 1250 109290161 109290211
    0x605010b0307030e15010605030a0b1509030c03070302060a0c1a190e010b130c0512070302030f34020f010e01020301050a06031506030506030f0a050d0e060a090e 71
    0x4280c014012105010040140043c0c151084180b954000750003085440b00741001e89820740814081c040c2000400310204842d0940f58000070768030a0010250340d407607240d098907210540c114059682c800d104504401003e030602003100b03020b40740c020b4101c5240c210303060030959500c1c980080440d50326200200b488030900c00240018040d8080012250410445081c0241a41d10400c4200011b034504402d41416a039007062145030311401e40c001203646110407405031024081c8203128180c0d810342504100d0080c0d0325070300031445280302c160300d80c10903100c080a01c41c540f042c00c0c00c0d18802c500c95091030100642c14610810361400c0500c102e952209601070b5141c00d4031030040203a09643e4022006000b0b52504100e40c002800340c0b45030070003a9944840d0f803400c2c011110f02c180f2090641d04c80100303034103840c107000c100c0d0b400b26400200c426105591818955603000066410002042000d20003000d1402d41d00f22440a44242d072041492424520342000c0040090021450140c900091922200d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 109292661 1250 109291411 109291421
    0x150b03010b0406030c051b0a061406031b0a030206120a060b070f030302090411070b070207050d03090519050d15060e0408030403030b0609030a060506100905010804031b021c02100806030c1c06 84
    0x8207401808001c00075103030180c292000d440d881d40400c820034003001210340f0000341e5213371310400e92420014540c5001001c1790b21a001c942010b9080708000503281400059000350b81c1c010340c00b8940420005a982a070603c1c24010a1030060040b0a0500d0160110303220307401800e030501006000040e00b5003c403203c000d1560148070300b01d440c7c01e0520b0401200540502004004102c15508289681402ea0b0010015005401240e2142c20365540d1034a0307140039a051100a04400b070124a4890141c0c11f00c182d02440d003114160042c0e007800c2001c1622008681954042e90b88203540e0703030642c1c0351a42d00781d0103001c07c4903c20b50444001c0c045001c45035010030071001d84600401000030070341402e81c18007101e0030708a002c110501020315000c0145990210200f9030280d00b40c40e204c2c004c0c100b91201d02c4007500600b440030798404c2541000d02c0515a45890b0310307400d6442191000190b458610301072f00c006a08a982541c1500030400120507414642041e00108100e124280c061000c04c3e903810048035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 109293911 1250 109292661 109292707
    0x80f0904060e01090f0c020613140705060a092108040e04020301141501030506060306210708070605030901150f090e0102070b01120b0c041a0702130c03150b03010b0406030c05 77
    0x140c0c6a000000d0a03121781e20a10300c2211040c4080c0c0001d240003020f10a02d1841444002c03c1c1e04080d15840d07088060034042c100103000014130980e92040740342002055803040c1e00a54900c4409284801c5581210130f4034029500c1d4403a1481d820289001800220420018802e0b6015521181e00712691303010307001080c0c4500b090026900c00d240440c400142150002011240141c07000c000740403490b5141c42a44880c1031520400c141d01e0044034102e503082c80b905da0311290b00d920800c6400300c0c800303400070041c5116224020003040f0040186400d9442c1d0320070340c400c24100000c1d00078148820710040e0400c005007080d201c005440c0003259500c0c0048482c09034840c0340c900300142d03a4903007004010201d035504042d00c03036612070400b8100342c80224038040140c0c0560380b50000148102c21922034000d120000498080c0800021000f19805001f82c90003e54076203022841c8280461841c3d040310550781030304e0741c404d0800e041c5818003409074014076060307500205016050141c8051540d905140901c21 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 109295161 1250 109293911 109293929
    0x5060403120606050304211110050a0b09070e06030907030b1003020306070807020d0c0f02031609150303090915050307080f0d0906270803121b0403080f0904060e01 72
    0x1403440040c10411181c107600070f0b4040040070020f11010441b0360000c070700808458681d10f0700d61004101c0503102c41c6820740b485159030052a024001899082d888684140f01581003803200c400c10108010448c2411282200428204800b01c0702c141800303000745600401d406c0c21034500603243e4903010750540c800c0310040401c4003843c50a00c2103007010f11042da0001401c0c1003043e0303142880348000c0c0d1034000f642d0a4600b0008100c0d594010302c03080d20f020b1482c00750003800303617441c42e1640c4010542d98002c038041c808040b0304019413103400300100d10703001044036015640c442100b0700307010f00d400141800601c0304082420310b403404107455a06000c802c0003010400010001c0b000041c078220b04015104031010180101000c04010441d00a40352800c1016030400613183ca085070480e00c1d00000d402d800a240510001c100d0b0343d003641c0d0001549000d010001500c0022030310603a404901d910407400020080002400344000c001c1c62980a01a9550300070404070300551a0001c508454400768402299 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 109296411 1250 109295161 109295177
    0x4090204030618031205040809120a110a050102030a18031703040b060409021005030a0f0c020a0201020705040615110312040c03021c0206160f02030105070206060a060207060c02120a05060403 84
    0x20001c180c030941c8800d00c4840f5140c80303156807588014000e0040c843c0ca4800140e00c0e800041c00b0024050115412403900800f40399100c4622805a0390b00ca480d000219049901e08101001a143c90682d030030071a030f4160300852800c000000200c0380300800c0c40b40d40c05080b16218002c000144c1c2c0c00d40c001c0c1c1c0c00012020681e20b134030300740c00c010001d51009007107140210b181020007000358680000000354030b00306050250f40ea82720f180918004020040c4907550b01403030f00306024449035022a101c00618001d0703080702c0c1801e40b6034080108440c15442165072840101000e06c80791802404071281581100c0196418030140c44d280c001750560480d0119140d50680c1c00c05c1c01107203406011a2a500b8019156120010555003c10120f02c41c4109143d11590803070340a00801005200b200c040075401b5000b0300c044d041c03001c8007950300c8005071510b620640300090041015440000c4881c112245651001c44105164080c003540000e1040b201c0d9090143d0020303074021030401c1081c68000d510959400c24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 109297661 1250 109296411 109296413
    0x2030309060f092e06030507050111060c03150604080a12030e030909040b06190b03070e01020d090303050318010510050109050d02010c150219110601210303050a020c030409020403 79
    0x1c01c101006090028030b4030482c0c1071003040c210018100b282c1c49101042103802c00c0c0150b0b003081c06103480d80e0905407041c4c03e01030701200304280410f4040032580c081c1c0b5004550203107156459224241100d480e008100180300062100c01d00c09800c050030303007016011500d015261591507080ca5080c10041d01d030302c5903007440301440307507070501c90350041c1c1178084040c50800b0100c00014101d514060005816041103002007501a5503c0600079118499403d29482da00d41d2911a980c103600b0803585107011515600038901c043d400482d0900e81c5038802d0341d036a81c4480c2143e030151400d400180c0816001d030175500c1100020302d004d1140e03038000d60030601d00103107051414000400c5159142c11075800707400155103200050740c000640c0301015901440c08140300001d020310354002d01030401042c45080221400f4860320350005030010302101000c00341d48150382c0307400c000e07416400d45000b207074040c904409003070010a11a5003c0d54105021800140c0b924003000c280e9441e580258105c9a0415800a0204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 109298911 1250 109297661 109297663
    0x80a0203090117060315070207121406060d1a0714040303030510080f030409050c0c1f1104060c02120f160f08150601050f040308030109050a14090618011b02030309 72
    0x450700d905500700c0700103545403840119842c0c8030801b4100d03110072812004942060b0083c4810405403c1007412001208186e060143d450445214820360a002d96404111141004032410b402950004460500ca00614111200d080c41c001e1003003080003681400d0903015641e0390b0080008500984e804100d0b4140048d000b0800607651b8040160f681c8242841000600044240d0b0120b85501100150903500c42c1035403004c0740b01300b1400004502910b4405100394200c0c014240341d11032481380070004030100c2c0400d60864819400b850740895030314420301c001460007040c1040c901c05101d00740ca107c800500380c0d90345091020380b0948868001c05406111f4868034000627002812950010314180181c3c940340c001c5481c002d0421410010006002e074810759001007100e008592001000e80d5941e5075001c107000910301541c0b1194500d0600301f0302c0000c2859955201c0c024603002000d0308041c1c642201d07040c920365800c00c2d50000307552640800780540d800820843d800300c4140e000341d952840d04120072 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 109300161 1250 109298911 109298927
    0xa0207030336080405030a052506080f18010c0f110c09070e030a080f04060e01020c030d030506030a06090609020909060c040312050903031b070f050d020d0f080a02030901 75
    0x100b0707407000302d608801e5010303002400040001d808040d84841000c0850500c1c0c03006100d03903001990103206560b02034041040018410910300c01c00c1809203088010f0052a041413003440c070900300004c0f00040071891001001e00290303000555040103c41d0040c5180c3c0340e40c04d5a980140c0040401c0c1452008440d003034110412030403002004019050b104080c100048460401801c0e110030480440c0030107006450801206090b5030300440090380703599140703401000c55441405034000285100c4015242c40d4000281c1d030413134060060240224041602c01100285801000700b03500d4421106058003242543c400c4203c4603000b4140410303420124018080341440c050420b401f9644034000b0040101231400c240d40c00e0b0707035000c0d9541ca003c800e03c020848280c000d0032801649400300040c008080c0107103881014652841009480501c3d07502cac1c4410343c2100c002c0c030400b900612603204031001840c10311a23000c0202e1041203100480c1c000f640300e005064001c03030380c60405a0b000203024081580c001c444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 109301411 1250 109300161 109300181
    0x4080f1501050d0b01030b151807020c040203150906061309021e0a02060403030209012d02070b0307050d090507080a0c0e060303030c0d0c270303090e04030903080d11030a02070303 79
    0x269900010795495103000b000521014103610b0b503120100788c109020565003000305100600784580088400580d0510002c16150203015115800902e0042d00b0030b4020340c1e00c00e07144039003130b0481410480d05020840c8001003030164001410010304c2100510801107101404442400603142e2012070114a001d00581c0b5040030581d000340301104480303a001421a0b4066890b20340540c861800b1001a1035140960800382c0410580c000110140e042c0140008140740b03695080300d0714a9900c00c1031403030a10040d1a0000081e10801117443c0503c45504409505489402281ea41da60f40c0c1508c9401c24251b42d404030354001e903010302048110121541c1c035400c03503011030146245040c1614402941e11802840f6100f8a0300c03000c0f030f003010600800750400740015080802104c040c1f00003507a5289140b030f001c02c6010560081c40400c1100130094214410341d4503850390b45d0554210340711050950040110305064035102d182c0c1044103029a00a180201e401c69409a11950b103450f0117000c1c0c41043e0a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 109302661 1250 109301411 109301419
    0x40201090f0b2a06011206020403051b03061003020a260607021e010e060103021e03060f0a0c09080709020f0c0703050d2c040c11010e10060611060109020a0504080f150105 75
    0x344a1903d03007000701e14241140c603a1080c80b90301000929105010b40507231f610240c0140a03e00c0584e00301d18070780304030100d42001241070319100d0f41c414400000321420382c00003a40002e00440309000c403280c000c8090501100d140c15605101380d000c620a40b03089011a41840103800613140c240d0f071a42c400c1c3c0459042e04407070000340078080350408110f80c0d402d0140300c0644540d40400503042740280b8542031028980016003074031141c2c45c00c0600c00c0080c0b41c050380d1100f1203615020100c030016104800c060141c88501c4050f102e135614000514003e90400001c1c0c20032281c040086070f101000400401005500c07980c040c045580e0010005402103040c40203030f00314400d0054841e04002641760400203920012100003502d16401e20341103d404100640c0b4034400e61030282500c502840008001d2664004d111042c402161155001c640201820aa2900541c04400140550303415074004c0d00c645007881c0b50a50500d56142c0319280743c459408016460340d0010600d2158035240d006006014050543d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 109303911 1250 109302661 109302727
    0x51809150907050703080613090f0303060f0f0f1a090d0c03060c0305090d0c150f05041502040b030c0d110f0705060a020418051f0b0c06070e0d0b040201090f0b 70
    0x5d240038000c0600242a140308964035243c00081c17680b182d010941407504424104c103001039526010300100031074025803c2450040700001900703a6032a072002c0960312002044124685008280c181e01501851100c1001409001278070142c2c84680a03000468003500c0310440a0380b030350070910111480300803490201400c0000700508010000386424040c40346180c80040c0940600b0500044085581c1030388440b400d1610f8051442d940c1d0300030300d005502076414a43c3c2c0203280075203442244a14802e018071082c1c10b10000d035130041c140300603190701c02c4a580d01051001d402d814a20007a400030350901d0400001241443c24800d04101c455400649924118074042c20300b44d083c8529034520541d0b0356407d0300c42000890f407a0f00710204443d6003460306510302507240c5510f00c01d03083d40c00c01c600324141485060000b0b101d05225100303001440c000030780a207401036003d40711208501070040c403e0f4184900400c1c0060070b001c1c03950142d0002c20760074650300d844101c3c000710000500070842c00c0c201036500d01c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 109305161 1250 109303911 109303913
    0x603010509040f051f02130f061704211d03070e060d0606180b010212031911090904030306060219080406030c020a061401061413060518091509070507 66
    0x1d1440150030507001804a0f1424040e0328140d854500c1c018a1040c4e030303000e002c0103160705803242c0d0060006405040b203c525190740740c1d0000085035081c0d2191600007000b032800d19000a00742111190024007490f5440321503480400b110f21001144c12102000440c0d2000080b44c5000010f11034041c000700310090040c0340c3c40c0082213144150b016003490303c18440c0758003641c10010700d40d215a004081c5c4520a250903111a10300000a08903c0302c41c0740540210252040440c0321070048a01c2401031181044503519082d001c9002081e0321072500502c07540800808049a507040451441544680d0f40807507a182011402414012041440395003152134080c020001041d1109484c01d60b0f02c1440e00089a8914040403403400c01c3c0c040b409040b451400303656069100c002c0f210381c0d05031050303500d4000403c400c84408880310304c80c50440c0e000302403202070b0a000d218400d100821685c0b10009484440d0800c03000040c80903103007954000d400c904001003a18481c01c2c0f504080d0b501c00c8040c00c0c0981002e00c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 109306411 1250 109305161 109305169
    0x16050a11030a150f02090d0c0e0708090303070f051c0608070602030c0307080901030902120a050c0603090a061a060f070204060b0f030a0e100203090f070906080a08090a08030f03070e06030105 84
    0xa01d941070f44007a501c407080410440071680c16103c5810b40100b0080d01008181000c1c41d028030180151810b035101c0790001101c403801251400d004112120083d4076503607903000211440e80454010408000d800c02807130450840501440b03079000e841078400140c1e50314021100d0300e09401a446403055400910031048850030101c20780c1c0c40b280d044810b140c0d4420f02000100c00501c0034401c000d42c0301c80c889641d0114a4800503400c0e06480c81001203401003100703a000c00c00340e8001100c90400310f82c400003030b01c40020082e401002684180303004030041c13640c10b80700103006900201120083c004000c55100154902801003200034034002c52614541020760141495910004186100c465200e40200920f600c04020410000e4000e060440d00c900340043d2483c0c1304d403010030503003429104400d404100041c0c1c511a08048881c004010070a441550b541c0040540200780c0d0f055000030044400a40c05106100070149540381007146692440c0486d005014441a44c5006009200600c014011a11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 109307661 1250 109306411 109306433
    0x6020105091f0e0a050a0b0f040b060d03120203071809060605120c07020310020315012d0504030213020306100309150b0609040f0510050103090503041401020316050a11030a 76
    0x2c0346250441201c0b00741e180c0043d00380d283c400c0010b44141007081c001d0013000700d200b818141c0300e0341c0350b94500c8e240e122040004850684001d4a01041040450003515202503501100392103420031042c03010710140b421040f40c1046440401203481545e8203c0e810b1800c6240308050940700310204459420aa4000d05a0241184195841010300d010460754506a0243e600742c0c1d0740282240e010303000740c1c2c1c01c1c180a0740094620000000c0701450300300d1039600074a61088d600c1c0b00c0c203c000340240184050328040000325070961007440410030022002d40c4520710800080c0c42280c03070241c0e8a00348901801395066180240504052400b1340040024402c511100b18ac058902800301341c416034400000c1e100d106080e4810760091031711035000400403482e003001380318841d80c1b00700202071b0340d580005405642480f90020701e607410810041c800d00d0804509a011220103104a0f400d00c1c9044016107038140d031002007a5100d610011441c403c001e9002c2000960410079009030010038200c2e0b940c90038001d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 109308911 1250 109307661 109307683
    0x1b03030801091d030f0f0708070c030c24030f110c1509060c09040506040f05040c0501090812071b08030301030602090a0603022d130306050609090a030f05030604090c06080601090602010509 83
    0x10001d00d02c8100e0f0b010901f070720141e94200d0341c06a07490003a880e00d22103503091440200c0b014940502c0014081c2d9404502d6458442e9109034a83c0d000c465000480080002034800d945c4107540d041c00c1d003242c44000b8060b0160762031840003090040c42e0b005145103015402030110040e54888010000714a641c1402e0340e02c000341c01e841c046a19110100000d000e05110081803038070515000412060140c00007100085400030b80f00c0581554131140c005031900c1c401455100c0c1440100b0103100090303c1c0f14034120240742d40c040b00040c81030702c4004032810b40e482a030094485a03000304a03085686800b4034030320020021410110b107040f22008048801e40c6d0384070785403090346003c44202500e8803100e008072540744015442201c200d0761285080710041209071550307801001000c1c00121860400140c0080d01e0b45c00d0380319010001c4803a00c3c11580c13680010300302d9400c5511003464034001110009031030090101a2200d14031403505100042c90f801d142d600600840e81010103100d292000455004500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 109310161 1250 109308911 109308937
    0x3030809031204060c08010e071b0203010b090c030a0b0a24031b030c02010609021201051002100c0e09161407020402070c030c1805040209070302071b03030801091d03 73
    0x540d44400003182540181078108a40045090801c4108001e0350f00040b0301c0b1081d17443d42c02446c1d0b02d400781c0700b80f120000c8901c14081140c00f01d132089008a841d8092180501c000d001041c01c040140102c4d4030610181c0744101031120200034003560b02e02500840c1c508203402c1c0c0300d0810003031a02c0c1d8002040f01d04400249044041c2402c0d0a0f00244241c12042c00307c0b0752a24001c03840801d40d00010024540400c0040040d443c01c500400c0007059802100d840d401c4981d484080e60742020f04000c000301d841700c048000d52040c445221007007000c034042c1c400703c640075445d107056104c0c0d5103043c424800070040883d9401146019081220754000510012400441151548886151000c200284a84400a4140c0540e00400401c00c111f1501040958450131941d0540e0800131810409880c4140c400a602c850b0490018071124800d5029040c0c0d607000d0724500c3e2041031080d10090018005400541c00148407000500048034140034006c0c10b19003080f451800f90001240d000d4407405601010780744 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 109311411 1250 109310161 109310177
    0xd1d1615110a0b06030c0907180b04120204020a021509010c030506031603030e0f040608011a100804030804030c2003060610020a081308060c03060301140c180a180506030c030c01090303 81
    0x1a417420000742c48039640141c0218454108004068424140e2103402052505014008542004e02c0320130f5504039015000780010144459007000081d40001e400c0d44114030400e0070410340030b540c5074840790103070592800024856540803c01000e80d48020030300ba01981c024140440e180804013403d40442ea0945000000c00c1341413000581501d00e11144141d101c1e080640100b42048198081e100700031180c482e0808901d100384c284540c510300707854603401040401d40000c0c00300e8052101980d209200b031800c000301d44403036034508154411064600e42c0080101404107014142004196009542100c14103400c0000c0b410084d035860468100400648000c0b4000a00d08410300450380980f004100361810f0740341c6012845a95001166080d00c65820481e4000382004641f041d5400350000f0400c05250a04071000a803441034140841034000d0303030b40d502c001403003010301058010300b24868002080900b040d90805282041200d5030a11981058860b5920390781c01c00a540d00b100e03854241809 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 109312661 1250 109311411 109311421
    0x812090f0d060b0301090309170d27090f02090103050c0c0a0201110309032506030207080313030c02040e01020d230711070906060c1406010b0d1d1615110a0b 69
    0xe00b0f03180e02102d403d903003000040e204058006000e0002d8843c1c0c4514004000e050860807581c4020151007040440c007010440e07100d9007035050040f4541204030a110b55080d641d0702c204822240c0c0c072844d50410ba580415104000c0da0f15000e155004141c1004190624040c640d005480d00100c641c000d040c881007890b5501280801d0040d5060780c0030050945034584000508030002031806c000140f46c0501c082404103045019209480745140c02034003850075a80e0345104c6402c6481c000509405015001d0354401c01a0b440d0701481d040b1549000002d600c4c2e26484100a0036682214082055a02503e0842c107241c5400080d135980400d613450601c509181555466040c0180340d00241c0ca5241020310100704540c200c200549550f2280016001016003440780d107484010a0140e109004c80030040d0a80c2c0b40800c1d0880d481c00440d103d039100740001c41900d280c2c90000e8180503030860200c0130404000c1780801e041c0307002c408506801c0107240c0c0070101d10328503160720120340000d01005002c004071b8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 109313911 1250 109312661 109312673
    0x1504080a0c020d080d022a030403060e1e07050a06090510030b06070f050a020f0105070f080901020f1501090c02190206160605040f111002030f030c1603090812090f0d 73
    0x302000d03000114190340d850f844402034044e5107d5050200c00781071016081001d40c0030080c5000481200401075410141599100000750903c040d80c241580b042601003101841c80d114800350260000c4000c00155103400c1c288420104075604c41d1043c001ea04c1d01c20405600c40c04201c466000319407800052925040000452038024a01c020b000c15400c620448200000000c020720b905008552854000d000742d0011038032403246410082030102c2e4207031000700049121020707010401050058840286041e0300c01442e00030b0b4041c800281403980001000200b1051245110000307844c0301804103090620280c0b03104203280700009000701341c00155903008907858580136900c170b81d1109003070181d42014100900c00c40c002c04000c6e104c0744044178000c000c61410314008401040107401641c2030480c42805400300b600018600c01041c00100400041c0c50700104036000f90794440d840da146402d0600030a1440c00c00c048805440d85802000080c0141d0341d00000741688a0b42128038182041c0d0034500f030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 109315161 1250 109313911 109313929
    0xc15100305030406090509060d0f23011517120a1d0d060c080f07090302061602030109030c150605060403060b03010e0d0c02120a0b04140a1703091504080a0c02 70
    0x19001d400302050215105500090a02c00c59000b1280f039140b5880b00810000a00c000a4004103061044040791001858070701c200b68013088804141119044040007440c2540c4540301c100074540c9040368107000b04100301c5031070145014624010000e161114903810f00074822842d007030382072040542540d051400600364204002a010b490610791806a16001015010000995010681140010303064690440c01c2c240300b081030b551400040c03440d5070240003003a446021104010300080a4130000741c0c030240a4428454402c0da2801501c0060307007403500c1407154500204205604081c8100020381e81e0780250342c2074942010f0700248007022180042c1c0181003102807001c050107120440c1428a4101c51824a160300039148400200300c03105245450f0210707044020020a060808140410041e174a0704d0b0034100c0314021203c181c4e4007a261702611180580201c0c03600300c800410480120424040030050f6000e004200300b0b2400d05541d4900745000718568481040b00c00104501950383e18001c5c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 109316411 1250 109315161 109315163
    0x50720031e01180803010b1c02070f02010206150f010f020a0c0902090a080a0221030d0204090c110105130308190e0109062003130305090909070e09030c151003 70
    0x7119141810310845101c0740da0030780301c0c0d040c0329440c0081038900100b51202141c00c00b94011070300c130b03d143e00b03054560441741c0154000c54015144200650039404e82032004000d080d008010440c10803910b440024500700d0002c2480b41c0c00110b074600240b00380c0f070751914200c04040074205400f0a41c00030710124908200044040d0500000400c0082e03581c4165006195071082a2105c91800c1e440c4c1c03109903650001c1c2d40e0000c3d080303072a11030105a00102e01603864030400746501030320711b000c0c40300303200b10141d801941210140743d036680c000c0c600b442d0b00311610303610010310300303000b071003140703042c41200320b0b0000c11040150902096400003101c4010007940e20803402c1884008002c66007418140c07a0080030012400c449503440c00c074030040380d0309008000f00e45005440d2041032a507600e507160080b005c641624100e0a000e000c1c03060f0100fa83d105c0488a208030b000500510540d8a41103800303040e6a00980350b190250400c2101e0700070400b01266286001041e44084035032a120b85542ca003070303a030036948 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 109317661 1250 109316411 109316413
    0x60f190e04050f0f06011805090406091b0f090905061513061d0702010b0904060209010e0409030c0507050f1c1e0308010614090109031104060f14030f010c05072003 72
    0x420800e0850901d80c81d0241c2d248110651041d03070317040300541e41042c4501c45402c28050041c0304021515260100c294054450b20f00230644e03200d50303a44c0c0140400604400000c4141700c00342489030300b01403030850004000c48003041c8840001c40d11f41e6915014082e0201d0300403103e201c0900d241b601e454040020350080d2003410040c03507940ea9074a101d201a460340c0d2210840c03040004c28034a40c0705000d0700798002801042c503503154a403513a0300c0c00250710443d59541800b001d0f4071540900c0e83e80703110783c1b510f03240030751121800c1204919109041132055048180302d065207400c1c410068039801201300400700840d860000d40d02484c20a030494510400c4201c1c65501c040e0380c80010076900403001d0341203443c1600d54182a221a00100c40d180c0250311146000036000f0301e0810200341000c0c4510716540c4041c00000740a5182c000c51181e079070700e03030b004101c801184198021250404201490000306800c00070003660020310401003180c407036a41c02800700c441d00840c806842c0c1082000000d0308070010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 109318911 1250 109317661 109317671
    0x5060f09010902070605060406051c05120307030912020114010605090303040302090c09090a09050a150b0406140312041a030c160b0a05063a0f06020c010b060f190e04 73
    0x9400c14003944c80050110f88090030031010420724145405541c0581d0002807040001c0f860303640d001284a602902c0541e030b0b0380b0072008660b0701c2c800103600039030103429503035000f1610b4040c1d42444a03c02d040131502c0d038110ba1400000136485012124018195002c81c9042a41c6844004c006451402560806940140e101c030034020305480301e100801249205844501c0d40e40e50381d42009044541c402009003c0e90001c02c08000000d554000ca005990104c0b4000a41900303404003140490700749400c021051500e0a042e5100c6140410959034070140f000c15541c5400c0c10810308294049054410b40b01628021001c6405d804406081d5400612001100800c0e00031070f042c50311145405a51050440340760002080860811441c18000d920000400c071807044030000c0400988206070001d42480c01501c1c5030340300091408000120342c507000d14005612400203002003400c440043d202584224800c0112010340c11191081e03889880448500d04c0035680450000d403aa200d00c040702540c054504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 109320161 1250 109318911 109318919
    0x1060e01090c032d0b040603120f141305060d02040305191101030b010e090603070506070c031e0309151202210114030c150412030801080105071b020405060f0901 71
    0x340d11034255030030350355002e210111132150b402ca03084028010354609203415400341a8111002d030881c1341415009400000e01a64070f1700e4002c0c050000b0003213280010110002c1500d40350b4090400d40000358504902403400b1010842c1d080280080c0c82914000c1d100880c4d6035800c040c0c0c990681d002140c110b400e88050000304400f100182040a42c210b0324089c400f0780c0d105d03095109220b00602d0003410384925a47d859141700b00a04c0c40c500908c0a035151007041800700381394076580c0141040c1841080200020780c15450080640088813000251805041e1403c80119a000d5100c00441d8600060000314070650481200c464280242d0041102d000013542c014120205011865a42890321560126605c0381440041c1c0c2215a001581c543d1000c0c801902618010145500c29071a1040c072520f81940c071100d500c40901003078030984c04200010300400401c0800e000311548100b59140880503414192405410001c00140c003902942d600c400191490316084e800c42800100141842e1b130540e92 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 109321411 1250 109320161 109320179
    0xc0705070807060f02010606090902130302041b0318030206060904050102041e030b090706050d0c05210402031506060d020c0f0109051b0f060a0309081b06010e090f070506030901060e01 81
    0x40c402c1100040405044104c024811702c107003400c0d00d050f80e803654545841c1880307010203074106103c8100308002c483c10000041e507132485045000440c040d07a01e08481d0340c200b00581240c2c1c41da12140ea01c00310003592400026804500300d0b5000030b08858082ca95181c0e800c0c03c030300900035074005003076000c2e4146c1d1105810041d0282041140e1007246000c00a03a100c06400391501014030032341d008190300303000d015607030180ca0701b0018403160b01e481e0081c100040300e8000038a08204440900f041d000c51028001541028000c40680181c044010002400e00301c01250a911403814204407103a404500340700c0d54002071102c08013140070b4000a002a90190519641302e08200d942041e40200d07040502070f150074480d040294880d801000d180c10088440c4040d4043c02040d4000c4034004002c1003032482610900b07150000317902c00c55004180a604081c4500c004000c060300603030250788001107068856000040d60001e944082d0749081c1c898544a010350702609042d080788081801f01000411541c003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 109322661 1250 109321411 109321423
    0x21070b0f06040f0e0601030201110f0a0602070c080607050706022a010f0e0a03020a020906150412052b030915090312060b1201030620210c0a0905090c07050708 70
    0x1c440402c02c0c6088800014112604820004d0f81c2d03030010b02c01040550f000301c0c190908a03041c01c05440400c020341c0502400c089185108480f083d40c0811920203214036240c04d480600032440040056080010f8090094050008010400c0d07400190f80921004a05d842c501e01a07071164180140c7c0811200c42d601030305041000d119000c0c9400321030039a1800c00281d0b51540e1b0741503009824542020303024003000c400300401c0c468000d04403081034030480760010000e0000309102581801c40e0201441c159041408000030344c8103100440e1490078841108400c000480c0541e1b08002404003510324201050034540002d01001c3c51400c1c041c40103040d045902142480c104201c01c02100743c4038440c01c021030291a4035880c0004030000144001381c503941c0800c20303055a030194040c4412452a000704294003116001044404109401da00c40b405d00d1400ca03000400c00507500d04015248000516101152158a01c54002080131800140500303003110581a08401920f03000c0b5160a0b425503180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 109323911 1250 109322661 109322671
    0x14031006080129060901051305090702031e0a08010e041406090706030b030703030206180a02040903050910080603030306060a030b030708010b0a120b01050d060f05010609180501050321070b0f 84
    0x5550303001c40e441100c1c60000ca10f4240c24000d24070340c2013442c00c100440d03044e0062807010a2a40b0000c0020805545840c201441403182c0d6009665035a40741e0040c54001c03007041001e4170f6404082c06000d4103190407952180c15100c980900e00e60541c0c1e54100000c01e03d90409101826020311030500c0212680420b9071026202161424000b80d4002418159580c1940c400900144c1000c408191084d00034014032652000c00800c58200c10020b13000a8121150703918110003243d40000d40811905242c03010141280080c100014549070813808207889201c004e000d03a114800c00540c04c2c040d80d0007075025101000c000340842d812103807900c403454000c1002685007032041001060000381079060400c20042d556000344002c0b4213074a03240a002c01c80144580856146484e145401380114542c4103141c000c4c0740540e0f039606402c0c504001c00c140302c0026400a540c042c1840018480e90310002481000043c04886030001035460050003002801011002032604c0c1062043c032500d80d000e15a141c1c05a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 109325161 1250 109323911 109323941
    0x9060801141e0d0320060103020d110d0507090606120903021c02030d050109060303020c103002030a0516030b01081b0c0a0305070203150624040b04080f010b060a09140310060801 78
    0x414002c0a5450b8000d2000070b6020003042c0603040040d124103a142f82d542005010f442c01c400b5140e031694141401130300092482941d40804000007648000e00400d111000d01081100b00d00544000752510703081e00c2001094201c1180e9100924030800c200c900d80c8103000000c01c40c82d41c456201c04040d000c030348400e400620905506003010725101c1d0203100822020b0311103400503954117940280c114042007100005403d40111040c2941050006502c6115540d030000b9040c500181d103565003509400c944003c05141041c4145545d0f001b60090307401140c4001095641b0701041c2c420041407180483d1640640100c49000041640103809440424400c805541a0002e101c0c5451340041d0201e90b003592102070b054509000d00c0e40710100e4014818401c48442c40e1540310110500190701030b80c002d035120b80c00041500b644581c00e10411500305421101c0c1454100c40031b5005150100d0307401041c1280c00200360844607654200440004010425414000c0d60764450115008102940b07030b440700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 109326411 1250 109325161 109325207
    0xd020106090f0510140d0b0a0506030d0e0a0b0f09060406020d0e010e060322020a1214011b050c07080d080601080f041203020a0302041706010609060801141e0d03 71
    0x40b80c8590f0285921401040100d402c0d818900130380003862a00200c05c0319080b800010320500030034818602240b02c0c0a280c180030419042080501d454200054900030400114408040455079405c03034040480e921140c5c3d5546541c40c46040040d14460a104254801c500080001d00c058000c1100000c0d200e07107482e000300142c645030054544040352410b0503071180701000001c0324100c80340d9103000e262110f6501113007001625400b00c0d5080311035070801880e081d030700c030314110400c0454070000d0314030003200c4002e1203070f06500209a4100b01316044040e051100c0810741c2201d0307000410250009014034411501c222140400140040d0000e554480c0002c403004001051002d482181c90f0007503a01c584400c4c0020020a0201c0007034101c0b010b86d104242d000c010014000d803108100e1502c880e841d41c050182d03549441d07005040c9502640c4103e0a102c0040c00410040320481d000340e03000c0303030203842003100f80340c0c45000e0b07400e8880c448070890307440704034000d600040c968000550044903058040b8410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 109327661 1250 109326411 109326431
    0xa05060a0908040b03041b1e08030c060609040201020a0b0106030f110c061f1205030301050f120c0904150507020c100306030f2a09020909070c120c11030d02010609 72
    0x30381c0d9401101502c4100308000400807444050700443d032003401a070540030f40440300364400310081190b50000d1750455462400c08402c0000d82a0b181c01440d801d40114601185185000c0c2c4407000100003034420401c1d40006000d5900a009406155034862243c50041d0785541025008080350815000d081385030014000340c800300f4104845001c03a140b030062602c0ea5403485042c030f00e00319289000e0300841c0208030002e10300341c01461890350503114101542c1c50b503042400f171000c5901d4507807907184a165842c05c0d0001d807160201c0c0650210400795a00546540c0d1420300350580c1ca1140b1060b114203152070b01700311603150b002c02c021201980440c1e81d6100d5440c004012030903118240406452954503483c0034000980c90040038280c480c5d140420300c0c3d404126044118001c0b0303980c0c00b0302e00150300082e5000d128500301c04030b16031000d501d09003910124090788994181e49100c0c0134200c14000a00440814802c0c4461014281c0c4002002c685907401d40f200c000b80681010300c12b880704581005260300c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 109328911 1250 109327661 109327681
    0xc08010506400803030a050606040e040f0611161a090304050105030612070e04140a0321060911041e0b1c140103060b031c05030a1a0603090a0506 64
    0x4a01030a203048000200d50300600d032410b14400a0005401025403042c000000015542c0440080c84050040c0d51207180544003007040d268010308480c401d110420043c04112105410160807503001461703400741200c5807519000410140e140344500400114211031001c0758102c0119401c0d1107514a00e0200c0c0c0c50740c40c5192041000e4884444a0b00144018040e0f94807481c099540490b0041944400009619615080451942000d00751070b404508000510980301141c2c4080110200100380e400780307d880007408041c189055407a03800d41c908100586051940180e001740007180420445800070b51420b0105600902c02e4030100ca00751410101c00c4a64a8299001c0701c803203000440c50080c003a03031740b0605a8910800c911125076500c160284548128040350301851055074000703a01e903400c004151030101440d00010072680d48400b560a100c3c1e01c00296908420543e81c04580c07182410500c800076641e10040e5500002c0100420078008400225446014010400e403195511104508 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 109330161 1250 109328911 109328917
    0xa030c0311010806063c040e0709030309050d03030e0f030301090b03031201060c0201200a020f04020a0c261c050f070203070b07090503011a0f0406050f090403050c0d030c08010506 79
    0x180ea400f90040c0079010301c1e0107501642da500744a02c1c202c4d12124155842407100f803006000c4600c80320000211f01404030140d40317050581c010019007450314902e861607034014589901c0d400380c940240c1c5030441d002d0030180a0380140844181c1d902c01e880044100c644691b903071b80c209202d529516420305401380b44908002c811a07044240f480c2092031182c1c2801415900c50041c12012810451008a030002a80f51500f0b0042c00c0314100010300310840a90040010901a076140f0900c217a20400040200b41d401040b61452150302c02400220864080303031260303070600e1074581c3c2070075000e0002d0f402d40006403102411700c03061001d410401c2182c9640341400d079210030840320380025903c10410840410403214041c5d9000b206450a000c6803511a000b081c291019085d20344404050100402030718a0700340e0001d8103041c0d041c1c03010000c4900c0e001c000f480104e0500246402404404089014180710b43c08072400810301d1070440b00740406c1d91070024010100c0b41104030020702e440001050601c0c0600403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 109331411 1250 109330161 109330171
    0x10c0c150605061206060c03070605040210050a0807030504030905030d05130e06090411030a02040606080709080d0c0206090406030b0c0301030606061e180519080f030910080907050a030c03110108 86
    0x8104e0030000e4030300744618030100190400d40d202405014020840710b0410041101d180700c0c0c0c074041514102403040c041980c2d0441c0a20082c806c0a00c40e0814180c2e00100880e88234130b4501e0003044030303292400c00741d8080b002e64200a4141c0034011380c0b126216007242c002c3c031098074660001c0490540d1420343d4507044006461055020f4a020701103404950154104100901c00400303440d5041c1d000d03400a000c9404580c4801d0100d9803c41c10003800b0b98005c84d40c08000c0107848086c00d90314407010401450100c4001e8003d104620115100e4220788035507109001542c7d008813000c0c0581032603002540160000d2000300e8149007003d00c040303881403240000307203542c0b407012103030307041076642c40005641c0c6944404a81d816244010320009545d6101440c040691404a41c040e810a041031707001418900d4047c41c00c1442d52041001da1165220b50407840313440851703443c1c9591140c8840a0160415880b42d103e2a40510060008800c1c1721640e10340a044a102c0d40180406001e900e005440e002401c5807 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 109332661 1250 109331411 109331419
    0x60615040605070c05090a05011412060135280209070c05160b0307020c031506121501081c0f080604020c0307060e0c0f0117010612020c010c0c150605 66
    0x1c028070740c01107010f0a19603110704400030710240c0700d80100710138050031514030b400941c98100421003007100c0d91071007031b0219003502c5040501c0003080d00682d641c4018445c40402c41e00880c0ca8840c000608a00c2ca003100c2c20410400c030101181c80c6070b0716a5280100b124160003031145452907805e8055a0403403011a034043c12051507a603030604207813507034002c550017501d040c01100b4154155464004841002c1e000e154009500c0741000c440003840d0210480d142c9002c1d60004110146443c4204540341d44410100c071400700005510313000034185906070241c6064290800004243c44101103254020400740c5c059455510845003000c50b078150524507a5000f084d402e0b0085401802c0a40042c28401003280480703180c2482503841d070007100ca9440020006400144049200e03150140c55520140d0303092070501c0c1c040450f0880102016810701c01d0b42d042c0800544507007003919864056806205040c1d008000041a81d500940614000c090071a8034250344d4100c0d0591a065105000613903001030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 109333911 1250 109332661 109332667
    0x601080c04020901031e09030923040e01091205032d130309081515030114191509020d050a05071407050102070206041203020f0c0d1209090204060f02060615 69
    0x80d050200030f50014942904040c0ca407220391820003402c000c4981c060029072000100e985940c1001442c0707460903041002d03590b00c0c1659031118070300042140018117034101d4001035a55035070840a40103121402004001501e65184504001e4102000d14403c1c21580b80003582c0c1d0040c0e030a070800000070b0205000d2440b00040c041071210101d200071007281440382c100000440c0d02da014140c64003c0000040188404200420240c50843d43c03100c103c0c414160001d105e09100207201d00004200242081003105440c0f0300244810120b0700040c0300d803030500030324120013520b414401000c1d62100f2200030050b800c1001090001c081c0b40700d103601c6450719555904044c42d850305841c00704e0344082408c2d5000d41d024001c003805603450400030300c018050226040c0079101c0c18600a401c14208003030111058100032015025526240e040d00012940011040000c43c002a01660210740c2c58000f5501d4520118011401c80e4106002c0180c0040b0f139000c485c070a076142c1e410001c81b00150841c40c00300520034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 109335161 1250 109333911 109333933
    0xb0a0e070f140c0a020a0f0305060f0c09060a0e1017070f0e0603090106180507051614060a050a11090a1a07060c0804031205040b0105150c030408150702060108 70
    0x5452285821051442d01600c1144144010769041d00420206891a00079400c100210b10300480d41000a202c481040300c01c20303103503858103034503071800030080c6140440700d10000c0d101302c8128080310f0201c0b0f0010300042d1240a4000000c1490059091f00c0b80208400e010780445980a841c6510100d03200c60018000b0740d9810000315040100070038860148901130104203c0343d9074007000707036218400f4500006001d62078008580300c2c0340c0d0744400543da0f4502e4102072081c0d880c2d01400b110040c0140d0640c503c0281d0042c81d086c05103082100b8658854020242030001c0da04203030b0001d80c024950404d051007900b12008040000b0303c00c140c019640194411410029492a810b0590254074910b04a504003409900c400c01035614021152001a062200b00010590440c7e5801c40c1005100810007041ca0316a440110480040c044d8a1080001d20489200207001000304c0785031300c4c1d010090320385580d50f03001842c5d83c0c1c40319001d81904035144040000da01900c0007034114103e80d2840c006050a05c0c003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 109336411 1250 109335161 109335167
    0xc030f04080d1808030406050c18060724050402040c0207060e27040501020d06240c060b1305060a0605071e050307020a080c04050a0b0d0204050a1515030b0a0e07 71
    0x20b9000d14040741c0c60f41d00004044048403000f644950003802c0c10307541c920341741c9085003c0b90001000d101c4003100074003100220f48440e54000200c0e580a0352902d40e1401c003410400781d405190b40002000b0007a80c882841d043c0c156800081c0628821341c0c05000800039120180c0c1c0364035040c020880000c448070030060709498409007400c5218068644105c81452030900d4020340d000460342611540c3d0005404c0324040510301c5804001d240002d901038402160178602d0458841a0600318100030702d2200c00310512041c1c5e80411680480144140e8661840b5807075039001d00800c0703490f58421060300c8000600f40380100d0844070425481406006e01301c000455503090340c440c010060f245848103100d041d00689982d290240500003450040403504201010842582c900501400d45036040103a004500e4442100c490710255040b640450641c3d20001814002c00d081d507541c4904140302d8100140c44401381a0084080103669014803094040c6000d000c0c6c0401c89108484244c17204400041c146ca01c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 109337661 1250 109336411 109336417
    0x4170c06090f060325050a02060106080601050304081b010203091b030111091005040b0d0e0f0f0706030b03010b0d1115040e0c0a0509040515190b040611150702060f0c030f0408 77
    0x368060160340300c014110b592520969109840446c9000a440885e25010000c09004202d1403610340e01e5403400704002000c03400081e10003092001c000c1031000300444680c1c3c128010480c908021034681c0b40680e18183e075078a540c00c070304020f16008511401c0078181801103400c80c0f0007800310b651800031074005101c000043d17081c0c60020490203010125020791010002c044540c1084004290180f8012074282010b00302039000c42254840540350000300c10100e0b500c4110b4400b07041c00640191983c011034050001584155805805c02540c54100807840c90303000ca40120981c2c00303c01a120b01780c00319103240300321700440c0c501d5980240000c50303000c20840101505000c9160560510b1900004107046c0c403c00d684100000a6500c0300e0051401c102e041c080c8031500c176141c1d5150071071814810000c60b1043e40200750400001d800e85e00010700341000700c07800800d0b0708428207403540b4000e0030007034035000c2c00d42d031032030010b9120700200311100d001c0f105682c000c0c51465494110341d2159500c00c4c2040d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 109338911 1250 109337661 109337671
    0x181222052b0b01061e0c02030c0405091207060c0801060f0903020904020a170601090c030903091403030702030303010e060913021e0f040609050a110a090e1b04170c06090f0603 77
    0x945003464003070000d0780c04582c0d5070003065680c13030b012241c2500d810180e01c12001038440b60208640e4102d51070150340c001a14070118942590001502c3d10b600c40c06905000c0d250005441c00c1c900002c0c0d00301001409c1c0d2002c40d100b0aa42d507a240070740d0b2500000c0b44c1c22800620054001540c03040117001500e0040b0a040e0014401007651030460390702d10030345c0100d1030070f84140d901c9034020000411006045004213030744840075141c2040140c0c1180c0c4d0203040c8140600610344141c000070000c403800c0c1c604108480446c0d8004003100d84075a990f095200110320100c0300d2a006455400c081500000c54100700c4d4101c0341e005141180c88070b00d1407008107141348049403d9500059880c54005c0b04d4490b4421a009442c1c9104003013a580360000d0404169605907814030740850042001d0300015502040f01400e650070005860301d640c546e01c2c2e41781e1042c510b0114081c041d120001c0d0000b00007a040140c41007407882002510000000c500400002d80241c0c0c1301142c011010a400f280c040ca4800c000f50b5001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 109340161 1250 109338911 109338979
    0x31903060f030f0201021c090909020420031005030705060d020d0b04060801021201050d0c210507060309020102060618152e0810180518122205 63
    0x245079200c91920710060300340c0c415200c2d5030b029500070081d5681446106550075840414121f03207810000000d0000020340714581c4c10f55564480c0c0021981c41d500070000048d00103088450f90a40740c80c4c1843e450b441944c1940401d4080503000500d41404a44c501c03c0390401401e042c203200aa20582000c1c0d800300300400304141e910406e04855980380d2260f5406014044001611802a00c4858204503c1030b08034510810341480d2100001d450303404100282c1d0510002c0ba0030f400d10821045c0b1100c0e00003c2d004105006020000c140294164801c2c0c080a000340e089540a0b15044d09000c040547d0541c02402d00289900103100c20b0b0700c0680440641c0307001b0300028940e80e1b80000c02c50300c0345500c01010810a41a185141c0419400705146400078210b0012016540c0b409419440c2400503110703058207584c03600300040360212280140c038284210402950840400e0100461860340411a0141111030150445084130051340481040d04c0e00070344603401d1040e00001e40045942008040848 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 109341411 1250 109340161 109340171
    0x206090111060c040618050303091909020f031e09280605100603050105030d020d03150803161b03030c1103070b0c0706030606050304110f1504270608031903 69
    0x507005040000ca4402d180c2800100d072102d00b4100000c00c4a806100042e001e80320021003400940d40c040210782201c4404c50364080e1915051160b080070800d80da210b841c08620119040c0d02518001c4000d40c801e62482c0c003040c282c1c528200031030b000c110f000d491140302d582c0041c1c0744020604100a4200304007503021907000c4c510501c0d83d00d900581380700711031005940c00d15900c1000429010b01400b800362604070082c05982520540003503440c2110500702040540f900401d0740f40c8403d46100c81c0c094441001503907941c0c0b803ca10300400c5000074a0302156807001c89604684d04040301411041030f03945c103a0781e410301a8000c2d00e80d011941e800e008040c1e41409400c1b00041d410010030001c004050f48000503080e294608030016003262815441b0605124040003000002a90303c2511242c0e200100c81ca103803100d98130008180c3c100700640391070303074600070005000c51409240d0b4103c08010041041036018040401400e1054030075a11a13403006074014040c0522110710b4004403510280c451500042d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 109342661 1250 109341411 109341437
    0x70e090601020c040f0e01050606070305070b0c0d02071a010b0c030a0e030f03030403020d0806010c0b0c0d09060f0218060c030405150705060f01050301150f050d022202090315010b0702060901 84
    0x2048403000c002205c81c881d60748401e114140382c280902d5030b01901c00c079804c50a050103520702510758441c00318001c02d000350072000689000303100000e948030030300308400854036802907150010413040400d81d400d000d801c007603000042004465080b02d501c41d0000c00503600b050441c3c0b10553b1840580504140d0600414904490b90102000038600c0355010f60b00405070444032000240140d50007600d030320304001c0030518020100303404001c02c030b4010442030b00303e559840c00d9030402c030010001c20b60024001c90a00301c9201a0300c000e5000342100e1705410741c04040400b460310030440e661050f4060303000c15400c107000412151030502c02d00043c2c900d015029501e0650513070340b15401c0c8541100c41140c60b604400c01400781d410244503140741c0c8804010000111030070300580706440001882031600c1042c0c01d407a031100315187c203030440020703800d54a0910341e43c46e2603001020103900b0407183c840c040d1203000303040c81018440031402c0b07040302c8219000741d142c02c0d915020320001d60700c510b660b2410b114903084488 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 109343911 1250 109342661 109342669
    0x10507020315250f0c030c03020a02030f010501080c06180120061603050a05041110210605011b0b07081e0703050403121416140f04090c0305070e090601020c 69
    0x3031081c0b488110301c6038034050500ea141ea0f1030b00481070341c00400c64040e400161282d086070b0943d0710690513040c403e001500c00d280482c81c02159060081d00340c010400c02d0340f010f4405400040c180c1700c2207170588030316103490010b000c2180a0034585001c20072840c44805023b5008488104092070a4852900000c0754500c20a15140061b2200782050351000359070120140d25118654115041d41c900b80054102502c58000b107900d000c89451107100c030007038580c1199004451048984d101081f140610070101c000c0315009050070b04c070b491f003c9644035150050820211014030034032580081f8083ea41e03183c94000702c40104005080ca545501010b00d2009010b2201004a200300d85a036000b19891903c0d1400070441340d00700340320403112821714541d808040c00b14444154492589413170003105200075041107540c031500080c0030344903880c002200e4901c0000c40009000380d03007080300c007030002960006044080fa401107450b0030005030354140155991030049813003504210140b04403460500072078005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 109345161 1250 109343911 109343953
    0x120318011803120b0a05030c0f01050c01060e010810060b0d020307020a0b01080307030e0303030108032209050c1201081c030209040b150403060f18021014031603050a0603050c0105070203 82
    0x2e41c04906009502c800c810928080c5040b484c03415100807170482c3c903000100b540c454401c910742d0f1250a01803140035490340f25030182c03000b500c01500203110041ea0381c1c103414250f103002e002e400d44500402c901c440300340b81580900021140c40100c1c130351800205925540c003c3d000900b01070110b020b216000404941e20b888114080c0000101850303803050180780180c034800c103112001e800b941091004000e01031011060b181d00d2150320452070b81882285a00c096400341c140c0096011610340014000d0900c00f9201030456407041d0700f81d11040d6603c598285c1d54803e29405c40e5060424100924a10319101e5006003450100260001c10b900281c40002000d4190080c0c1702a4003040c089401c0003409160b00030070181c40301c9031108003c0100e01501880c03401040e52406030003800c02c114032807004d910030b6400950380321204802d00d03280e0510070000d0b099888181840e400190421340820280c0b142031291808aa500500802c5101e08000056907681c01c4010160780c18000c2404010300ba44003c804 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 109346411 1250 109345161 109345163
    0xc050a0f08010c0c05072d03140607080103051b041e020307020d051903020c0f060403020d11010b01390602070506131709060705010912030e1203180118 67
    0x1034101542012a0a4211100c03100c04004020a1070102ca021407400300d6004140c0e40440d0550b0054100c540020780305e0400341407500312450b0614800403d02c0080ea2410f00e00849220584429489001080b0390448003800f014180c2e41160b240300d00600740c120030000560341d0291001c220303074040790075184d020800c1c00180b2440c03d400004100c80c0c80c0d03052100107034280076400c0c40d5003008010900084034040504813a028946d00080c0c03124107100c00c20450890a0261040306e55515213850000d46074942a4807240101d404001152160360041c01184060360042c0e491440c01c0104100d4800e801c020070380b00043e0080745200034480102e03440d0694407818066100507a88003858a4030928040700141411044120b440b0010005146110080d26014401207007a440d40003070000100709210340071000304258606070080042242c0c080500e00000d0003030320b0401c01c05e2001c0d4102600c0b107560780801c03a415134040000929005000002a600c210814000a08036a5007105404101c1104c08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 109347661 1250 109346411 109346429
    0x30905010f09030806060f09120c03060106020304031a0105030a0b070318050604020a08010203070507060c05090604030b0a0b09130206030a0b060a0206011e0312050c01091b080c18040f0c050a 84
    0x102c0014590000c071104c0e00640c00380d8000e850079003000342061241c050540414440c1c980c5c10612003a0010800c241d80c0003d0380101503e0f01e030f50b525003011b5a01e90081c071048502135001120b0188001500c20200c3c101c0300054040c0403241250781e6805090b031001000300c02850381c0d81c2075041c0c410500701c00640c0000c0c40f0380700030141c50509004001c01d500e0142d012940c183e0040080140850788441543c10340c1d41e210001140407d880e6405a0300ad01070001c146800041c081400414405010303401809800310440411218a0810070320640880440b146076200841c10a03810041c1080401198001402c8400054450300000090000d40c0120340c610010b0b0703c20703401400300c006000301220320309116091201d0b10171318598440c0140c0785454043d0081c0b19003c50007601e40314080d0020b038140d66001010104056143c006842502e00701e000c0c0d690340f031081c4200142c4500b0114031560203500011044000e940d02c035500d100b583c01149030119094410490000b841c0c1c2c41e20b4580d4000f0b000615 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 109348911 1250 109347661 109347671
    0x40f0218100603110307021903141204030e030c01020c0607060b04020706022a0601050d14070305030a090b090d080703050403080d0515030313061d1f080f160f030905010f 75
    0x902e004050b18541c0c1c0e400b10711040304005128140343c00252603c9483c83c0d20300c010560303c2e1281001d43d6245010000e00d02004d00001e04810242c1c40f07040c00501c2030f4800d454861b0b584e903002051594442e1680c4032640564400c202c800d01d1890088080c0c90114072503076010441d4030040300420141c0e08010400c4039819004590b948405d2070300c08070b6401101c084c4c800250b80f00c0d0200c600e15651030781131103001d00481919088100f40a81075400900b040c20101c00c50b10b0403a602e00d80b599403a0f01200071513000805074900032449520140407140895030003894148583c0c22910f505c911580010000c50501008000010018084c44094155000320301d000140c0d0b813400b202e05228029101d20107a1007600b0401c1500c041c52480c0100d4400d545081c50407189540182038801900303840314944e2a8007810360403d80c0c8c003040f080200d200003111107a4400740a5100d0300c040800c10f00f4190b0311520800f80e01a900c00c0c805202c1c0c01e44a4114403d40b401061014242e1209400c5403646203d40e5011340d160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 109350161 1250 109348911 109348919
    0x50105010311060a08010308030727081c0507060216020a030807050c040204060804030e030712080403050d050712050d11030c0702030606010807050d0b0307051011060a14040f021810 80
    0x60001c4940b09102a14910315100d5940300c028944030050000518520008c0045004944104005400c0c040190144c0c0c14a039000303081c40034070108134407841c01207119040201c000450b4222340d410001180c0d4403210700300380e401d03620000a90402e8a5488101841c02107420241e81ca507030b0300c00003c5020780c4140740e50f01c0490501504000e003041a0f6030045004101c10070005a026040c2c83e1311079054036003801ca01880c64000303030030054240e00030603a1030380c0b14880c4801c0c800140000d008692255003124220300c85804181d4070f0703004140018208007c001913000140b400303803006101c84030b010000002c07030888118500f40140c20607280ca0184400110f00e000440c18108941500070609081a034078034980510000c02c42e220707110421500036111000d80c0b210361002c0103400054900105005802004440c005160000484485809100c1c00c070205005201c03a00c03402079509600c00c4204101e43d121344803481c2d0741c0540c0d0310890308811400007810440780e040d001a40244029440c01ea04a464 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 109351411 1250 109350161 109350173
    0x1207050a020c0a0b0a0c0f05030d1409010504020d0f0602040503031305030105090721030e060307180e06130b220f0b01141914030f0610050c0d1b0c030501050103 71
    0x102290707040c09042883c200b804841101c0c825944400b865181007040c5240a1520300109044840000c040d0b10000c143d0724001c94450b00540840409005a01395036079442ca20142030326400c1c0c8020b902301024400d00c502041f110340341c80401c43e00803180589025600d82c0401d10f1030b40011a20004c01c040081c05201c103140078050140c02c8030104d8010098a42004c0441d5001100300c6800d81242c0e030702042c52030416015034400381d5009401407125890b86440c18019118036144c10700e41c0c54203c42d90101059082c10603082c20301030b05014154607074008100300c10b00c1c024400007032031a0340074480c0044104486000300d200c0b6182c090200d00810140c1c80d0444820070703580490b507514140016940704040c541011015560b2116030840d80c0b004084009200303a4403002200c0704040c800a0000411040b1303d00420030301d026510507030b04001914030003031088030b260103140b000c54550b0300f051001d1050305116040c0c0710080e54213081c1800c2d80f05445c0e0f90b400081551540700b1103086e5150801081400f03e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 109352517 1106 109351411 109351423
    0x2061f0b03040c210b0601180503030c16090902030a060504020604030f0605060a0b180d0302030c070e09060601050f03040803070c0605010e0f070509010e0d0203031207050a02 77
    0x201810100c4441c003250186070130300d03001220f440d01c1d90000d4005803050302d50416045a020f44804004407401030080c0542011070880345408103170340c3c0d4144001c05402c61030400030810050420115480801190702114401c0d280500d8000545c030041500449550321000c0010f0035034407840005c001c0c5c0034640001d00801c0c106450141040110f91000c0d000b214220b40e40210241d8500d2000390f0b5100359203040052640e42c0c503010b046420b240c503486035050710074010750b41000c3c4201100707880d00031181d00c20216a0226400d000c2452824007001e82c1003030b402e1900c40e150504104c03100881e8880070700b000741206400000146060b1254a1b600f0100344e02220074417683d6583c2c0c0b81039548041c1520f0000080a40c10301083c0c60034000d03002c0300d001c424181c4070301d086041603a042014100054000341d802d80000c000503000c00e4860b08059215142c0341d11190b483e001001e00c028a0b03d2 = true := by decide +kernel

theorem cover : BRFrame.Cov 109172661 109352517 := by
  have h0 := BRFrame.cov_init 109172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 109172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 109172661 ≤ n) (h2 : n < 109352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
