-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4112
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:36:28.808995+00:00
-- url     : https://prove2.me/submissions/3cb6a6fd-f93c-459e-9b3c-67d395963569

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 739388489 ≤ n < 739568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 739389739 1250 739388489 739388509
    0x1215020a0f0c110d140105180309010e0f04090b070906110709020304021c060b0103140621030f0408060a0b01050717031003140a0b060306040b070f14130e0a020414 72
    0x4000f081110051100030400541d141482a9030b140031081a0941510302402000d41c41a108810380e801078140f8210107660b40159441c05041c000442d030680c0158440f800134141c1e600e4003d2007480110281c0c14840788040040c0c86980c00203050b1000440c40f2030155580044035100ca10040c00030918200380b0200075003000c0c00881c0d02c81c0a00503500d04460070034403400f1a8a019100000d1150814400901218403400b203a000030000401040b00607a54115444420700544030301a409101c0044424254868010a030090f500046008034039400000380942c4180d5020400304904420800151054002c950000344402c006a0b0503001c16130402014503044043d004850310242d44a5644000464150b410002503034020b01b0080103026002071050b030084c00903000b0300404d050540300e940c200c0700300400341014404c07500c08041c2c241e8440e1480c009442602550540c07101ca400c003513090444140d03c03d42503a28456030101e090f8016901c00c035022034050b82c2c603408080c10420280100d00303207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 739390989 1250 739389739 739389743
    0x90b12010213140a0e0105100e06040e19140a1505041a091501080c0310030f030e0a090b01091a07050a0308011509151b05071215020a0f0c 61
    0x229144041000400340003404003801c0c0e08050490352400d18805055080900c1c24543c41070806444c204804000c400f10036040d43c9040c0e40d10580c0d800d252409030741c40408840c1540d0801e01c00100016007004c003d00300b50080c49000c40360b412180710075001c0c0c0d0503035005500344105988c4e50782c089000382c0b09aa22206081d141520038045056981d0005000c507401d45103040d804822407905541c00f03240a402d07035a4021001c02a40007901c4510300002c01c84078000300071b0b07189400000085805140814001d200842d8440e81d0010240590720b0018640d9910542560140d60b4521001ca980754681c05800003111040e51600b42040c6040f00308001c5445107020051701070f40070841c2d400402c80501c20001c4103402615016025450b0401d001a800c1300d9408002c10403413032500600000f80440d0154440040c41e1922011034805801508502d84401c60001e00622a90800250405040d031045010703c0c00b907040c03400ca2491890058090344101c3c05d241001540041461503190700a000705a01c80e8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 739392239 1250 739390989 739390999
    0xa080123040510061b0c060815060f0405040b01110c010c0f0b0a0204061d060d2a030b0a080109081b0708010f140a09020d110102190b010302040c0206010f090b 70
    0x2549000306086940644220b00111150141402030540000c04002c582681100d2180701704815100da500145945c0107030401c028041001c1503400500790741040c80602c00a142c5569070a0b102001c0000b0760041c401c00e401141019050a4298000c88503411010f6004000e0003440c81c20130011281c2c4124506d04441901c41c004000001c642c4403d202c6100b600d0312200103942e14104180030700141280b00300d01c0500b51400c040c0d02c40a8942030241c03410814403060110310030090b003860f44400440c01400300d01c1d40071491300482c0b40561541103001985002d9601410183d240c05a040c04d0311200705010f415028104030140d850381c510080343e500d40130040251450300340c54900b460300f0342d03030240c00300103200383c1750456803166480019495130445007114040090910319400700765601e0250802078290301c1c1d80c81d0b0056a40e40203102c0c0858000b044603440942c02e80600d48807100701030a010070f0b0300541c644040300c4243d80c000036440b410384030018030419000b0320386512140641030240b404d581003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 739393489 1250 739392239 739392299
    0xa020c0906041518110c0708150903040515040305010e010507030f0b06030c07020a1a090102100b010806041d0a03051b0102090105271804050d08010b160615030f060608030a0801 78
    0x6511010241800b1b8203800302600c3d415140c030480c240340807240c8404a2030841785205100b0754040000c211011140203075103030003070003080340c4408215000b030741c1c0090815420003040c0456900194889842002282c074100441c940d00c0d1454001c44840f025815001036041011440804022001c1c1500301d02c0140a4485281c80e440c40100c070340c561513150361840402280c4400c072581c0612150180950b01a010400000c400c00003c0240c44050007480c0034a680348140c50181c00200300c0840350003141012030300d040000f03180081c0b040d40f007001c101a40081182d40d4078a250018004c07510030190507564603080415480207001e0905003100009082c001d00300c0850030303a8031040140c00070220031030036443d924a03140c02c050f8186100d407810002000500300047c0194003082051380d140c80c00303607000c000801c40103140140003803c58040e881d003070001c020400420000144904110603100d49000d002d0103648403480c1d6507a000b00b00295001c204008014040c0310003c01020500716013022544607a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 739394739 1250 739393489 739393511
    0x9080903030c0a05010b0306060f010f17100501120b090105091009090b090c1009150e1f1403011202090a09021f14090303030106050a0c080a020c0906041518 69
    0x5154010344040c40580c00c085000001c2c800e00f0303c100c00c400141a0088e00b044d1900100096800071016189030600120001001d9114401c44004082000000320312543c1e080050864203c5295446890b0004883c0ba402500c404000d014000d4005005801100a642807504110140100034500c01c801c001420001820062a003d201c1c03c040c0500790b00d00040c03d11503100c0342800c2d0000c0307420703024100c8041c20413401035100c45140110385603039012001c626116081201c5400b56106199801040e0082c05100c1c0300d0703569003000340c3c1d2045031a004010f90151164482a000c244503400082c0c2441c804030000d414401003559111320b0074600044c0c011803d900041e1085210501d040340d441000d485a001940c010500105401c01005500d0604075140c1c0020340e00c0c0300500a0008202006c910029100c0c000d04079103000340ea000750398079102c8443c000c00035070795010140e44503c114140b07408915141054032a41c1074000c280041c0701da102e41000c000261988080040e581c12607628191909 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 739395989 1250 739394739 739394743
    0x62d020a050615120f06061504050a0f06030e060c0304060c0507120e0405072c01020c060c030d050114060a0e0102160906030204200d0c020a0b0c0a0906020c01050d09080903 76
    0x21054030a014a038050050a4040c0a41c01c0d003a08501d0314182d0000d2900d40d8410400500203a04ca48200d803003040c02460b0700808d5180d8007032540040d030410408680824180c0e11440e0040a8604c0c6903010040401a103085542d40c0c001507441c424034403020000700d80410155005100c0f03200316420300d280382c060305550b0300c19107420f6407400350001440c49000030154941030103565040040b6282034140080c00824500e4112258006568844034038030342041541d0003840642581e880003001e40d40c4481c6100c4050b516513000b01d000440d141c0ca42400030821554018419070f60f008c01805190512074640419140f440399545024150f01c102c01c1091400e21009600c00050884424082645450351050200b550b00d10f80c0c040e1240d55a03500c401041c0004001642c21200b810360740400c3c101c80c107080990030304c021060060102c0e03082608200c0c00003041d500030400260541d0340d03203c94070f503208001ca0b1695102d4800a00248041000014a0085400c88500703c1d000d400d01525107030000700024 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 739397239 1250 739395989 739395991
    0x1230a1403070807090801150509101715280e010b090703140f04020906060d1e020a0206060f032d010f060302030709050c0412080903010c08010f062d020a0506 70
    0x100c0050b00103c1000a655409611240100358000c02480310400d40c02c0e415803203460768000c4501401d19800012003030001500740d44010410701c001c82111342000c3c4a80e40e102c92010030110012180c8202182c4501011120780d100450540e81801c1c0368501e401a90020785050307103144130302d5921481141c07019540e81e9119030140200b52000651744040c0300c01c000c2c004100030f0403600035221510410016031130f00d04c05941d110320201c1309159264506c2d10311000406081001051020015160b1502000554010180307084240c007112110303038418081119245010050707d40640211141d80c020400303a07841e038041c07081c001e092900c0f040700383c0300342e00d0071a0b8010514000d01a05c4010030019410305211041c003810319510144042d00d40000560181d01c5148030745d40302a291085c040d000d11503410b05440a110000b402801501b8207007c0003044070200f0301070501d2b480d602c6407001800c2c5005a501e210fa414540360f0164190200a0018201e034010700c402c9810340c010300c00b464000800c248030706 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 739398489 1250 739397239 739397251
    0x1204020325091d031602061608090906060901021203070e060f0d0e06010311091b0711010801050303071e08042c0a0605033c0102030f0601230a1403 65
    0x504031500c0c0c5030382d2005440d80c0c1201405200024a820303002c2c40c00210840f03003000152002c44458800c030740f020440c2c2c0d02c540120340241031403d20310710080005490042c0140c10b011900f10869403545410052903104060030107015074000a0200d1100440c00701035075006410341040ca0b100404000400e030681e00c4521840300c010000900e107040c18070244101c5200e9810700c00100155819580d0303c001058110406902c20ba242900244440301894520b041c0c2c041100314150302d960b85440c01c1200e0f000c01c4400340d40030801c42c1d00046900d0500000342c039401030308900303081c1d2010f0160300702c1d031200b41000c40d040d44c0e010020080865401040010248000340031010f1212403003101c18030920040d009081e69400a0408030204003a41d000600e0b4030140007a4400c0c4507540c02040740703c465011011031070000340ca401c0d400c0e1f01c800d0201940510302c102d407840c540c410607950b648011200501c82c5035007006891074000560301001002d00140050100d036050400703e10690743d1031500250411a10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 739399739 1250 739398489 739398553
    0x30a020a02090109090305030c07050c0a08010906270f050a0506130605071b031209050f0109020103050c09090708041a0103210f08011202010c0c0e1b0a020312040203 73
    0x440c404605254900c00e006111842c41046841e846a074020a603200140007010b242c80302045010074000300b80b042614030400102481d020650f284000e5000e0880540b007516440d161865a0b207070b0928030740d101c0104000b4040307201c900c4500c80d40c0e07604412245181c04d8402c3d105c0c0d1140080010810018240a400f48030a0403004264503d483d00584400a01100030400c141c2c0741c04200b141241d074840c064960504204141210302c5100c6c00003441415805015449202c036004214401980302690360341c001e9800744443c2e175804400d004075102e0091580d8004910200003040309104410281d00648901395001d91500c070010304100ca0a020781041c5d030640c00c80d940e00c0310210044142c0810b07603001c40c1050100300b484540d02900091051203131010100350491500116807190b8026100381d58040b41503860a40c55840300b1040c0d42c4102d4080c13040b40d0702140350240044202003503a140d0b400940c02141390104106800a072650040c00498040c452440745180c004103038110b58000b400c000a0f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 739400989 1250 739399739 739399753
    0x52e090510030510060e180a0b0109020a12090807030e03030d0e24152101020301030c21051b1c0b0601080c091c0819050403030f03110a030e010e030a02 67
    0x109581061500301061314464500542081032038405144554040c0030000100c136806850b041c01c81c24184164001001c190524002295200301c6501400b0381e500e89a4031944042013181e640400c41d564898050000d043c10300c14500000d11440300702c0040b00010f01036904014106440509a4803c100103034a01d80100110b081d00420952507084010040d1a159095042c00e44808542c41c5520351610301554805000007074180b42c00b081e4010b09075540c0021552503030f40e42000d41d0752039564007909000e503458088400082d00c03a40f101403070803608100540484d03d40141c11640c2c00b41c40846194000d00d8071804000c0c40103410b206001030500404182d034251400e0b400040810400500d2450301001c140600112600c0746881c100341401c0120749210a42d001e0308201e50780c0d0051070508003a140140f50701da1003d69116001d0030481e40709454240024500c0c150036016a0b940c5c001c1c0c80b000403000c2c062011200d00c80d81058000d00941000012510b103103010803802c1d9400b070f11100c0c0150703100403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 739402239 1250 739400989 739400993
    0x403150e0a03020d1b0b040f0323030618010612022805090306013005160303020d020f0102070b0c09130c030204031103060405071e0e13021201052e09051003 69
    0x44001700c42100344200a501c20010b0b5036039003848500240000e0000c4401c072110408250050b503100c00703012030350900302068803030445540800740d0040b82d0700c9024040c0341001c440c89007900c84a20b41640e205403990030920f0000c009450003500480c2c0a50a9101e202c01004240035840000d0380401c1d40a03034800d542c0d410b0700300c1410705d0520180d000800200182010603c2d1040d0440030034961000103224410110827400c0c030601d8400048249011903490035000810160006190501241c29409544910007190152800c0780a40c0704040c08120610b00019480042c4a00901c0d01d018000d049040c0c40542007a4042291000045032000c00d50015080c0b0a001f03000064212006c0202c0007864a1300d855514143c80d030300d60348101800a0140c5681c1e003d07080c5100d0320040035121440301c0703402e13524280c1c1c1046029241082c0a034010500300146040310b070b006005191040030f04d2290780060044c5d240951000c401d4650f004030b4810090700c008540c007150780c083e036802602c20038001c8081c1c40c114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 739403489 1250 739402239 739402247
    0x60304110d142506050c0115080f10050601020a020108060315101e03020a03020f2101060611060603060105130e060f091216080d06090221070905060403150e0a03020d 73
    0x242c580d8070800c2080b01c400d034804200f071044105646035440c2581c2c44540301c085440c090115a0058103003400321030701c0842e00045c005160804c10880e90126007100269480300c1d41210303001c1d80c0241c0141c02c001003000c095406078100c55004140501241c0403200f0304800002c3c1410140e480c01e80001c10703450100141c49117490015900780390300038a075100610f5980051202c4515200090207800b08043c00581695280c401075650307004c40b040040d030b07052015280d5008051500416003c0b6030203170229030b0400030014525110301000303401800035908010030000c5c000701f40d0780303002101900d0b9100503540000902c01a801901e9030145180a802c080180504180c00c401c8198541c500a2050b080c103c001104401d440715000301c0f10640e2406105002c001400c0580c1090301101e0001841d01d44a951a401c00030480d0018020303e6a41e84552604942c4820301d80f1034140d10080900041c004241c05c1100b4000040f1700300c0c80003954880940c0c0180c03e001584909401580200220308074240d08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 739404739 1250 739403489 739403503
    0x20405070c02310b04021b0f0d090b1b0f0a0309031509050304090b1302040311090a05100e180d0503070311040b03010605071403030a020904060906080c060304110d14 73
    0xf01c941d9004560301190703030700d5000c040e116a00c1955181c00c2c1240642c4c07a0ba83c11540041002580041a10100c021403030b40c801c4004800401442064005030216100c0c500341c40c1542c12400140780742a010507032101051503118903142c102e00a000000100203001c01040d90030504c2901d803400380728618142801c617840c400c0046a004e6040107040400500c01200300d81c25241c54540014112020301d001c82d429040c001444809035100241c003001740a54904082aa06003c54003c5610b41d5040314540640b102034881586183e4480c10038000c43c0c2c401c42c1d0055011510304405c2d020729845541007480c01a691000300c0100360000280906d0f65498015000c1568801c1c1c0b0291909141c40307035a413040e100500c00d100030480045880000c001900d02865904d0646008598880c100800d00344d00a51001241a01c07031890036100140c2220240074000c100c8040c180a061024201c105124441d80020412945003c01c07002c0c0320250350750101c0f6001c049001c0d8000164481c2d03000100d500c2c00c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 739405989 1250 739404739 739404769
    0x41d0c0a0819031805190e0a0c0206150d06060303081e25120c09050f180402010804080c0609030318161811070f030306121106090607020405070c02 65
    0x10300070710050710040c5448a40300c0343c0c1c940fa001080010b80a00c41241c10820b030001a40b041030030600c5000c1003414854401650041d0101010725103074400441308503110010564050303040f01c0e001800d102c0152541c075100700c4001d4068801d440c815034400049940580048001c0b4944d002880a519480c1d55480c088010040020040e4104868581040c5007100355403003418246500c6524513502c21020001d08928103070061220055825028199080f00d0246501601c8411841c2c1c65519040406071858014440c08010a40300c80d001103400820081c419682c50b01c0070008600809801c005551143d10300b84050340c0c8074281342c111a102c503c400d081c66412036005d12554011003103d0071030501110a044441d1161100402d021000762001c000b041860348004985d40b03042c0003031044400110340c40f81c2e6007081402d455240d80344d405040079a0150140c901c0341d101e80d4003410080000c2c24143c10041c800740c00c02281d0f50004003903070001c85a50700000c056510500840c2002d031600c1440308 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 739407239 1250 739405989 739405993
    0x2030a050609010f03170f0a0804050c0d1505040501092f0a06120911030a08070611040e1f090c110106090c0f03090611030c120a1104050f041d0c0a08 66
    0x54900340e04d036501c02000d80005000e00040080701016042100e044803494a12005920303104d41d40050040c240e0b01040700e0540b002d000300d5100000c80d141c9141c2109400b540440c0c54040e00014004c10303002400018030403a019943c4002500114586da0741500d82840c0b03500426403e66200072a01c4445005129098003d0072007890512869420512909142a41c2d400004000340c103400d00c03004003003d020b0f403181c06029201d0001c00340406c40c0300500500d4003904003881540c024017070341429417040c0d1044e00358900c9080086444480c640d91464280341000212505031303512104114120307143c01c0d030a45c0101d440813007500243c4030207000f000000d0942e0320040000b06e0036004084e00e00c1036401e414500701035803a402f001c100701c05135204440c2c020a40a110380c171385c130b08500ba08840f50303c07140481d40031800010009800301c949005103280070915040c55810a882d200c01d1044429990300351a074020349500e08141d00f089080c0000ca41c10840e50000d021040000092000d02078094110400507 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 739408489 1250 739407239 739407241
    0x90f0a0b040b13170901110303010518040503120a0f2306150c0601030501020a18030c0603050a0e0d0504090b010e15031012030e0405010e090628090602030a050609 72
    0x104034600d080d01c1d4040d8122808812036510b10051210080c03403400003c02562612807441800442ea0002d05031581d8280c03140e101070a1030f5050340740c0d03e010034410158080c1c0c6001d003030800c140b0540d5505030040d104804880c1891090b070985030201c80b084a000e4203075990344410002c1c513001d5001d082e003070714079010702001c07442c42c6584407030040500184000c1c000c101c0041940385400d443c2084542c07403030040c02034400650f143c0c900907000c2d6004141c800c0c0010031401c2c90112490110340360a0031203070b228402019052601800364080d0070010151051242d030303500c080c441e02d00103011900c0400203c1d80c07003a9617103050100c043e046400a0501e02d04001d80e403990f4800f0780d01c0710740c882e201740d034600b114a0f9120355511001150b065015040507004c18030101c0d54208040d04200400e40071442100c0c07d2050740c1e2030300142c40d008242110b050400c0d902400201b000c954610140001e256003628200301100007044821041d1400090111495580001007027002c0001d441015000041241c4401007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 739409739 1250 739408489 739408493
    0x10c0f0510052e0b0f07080304081206120a030e0414100302120c01090b220605210c09090703150b070606050109051e0102030904060806040308010801180609110307080303090f0a 78
    0x1055084d0241c110011400180d030b0a140c503844040d039070410350001c1120340c2d80c0b61500e0b0102454004917003403a10320184501041c030038a440602100850703484001849800800c0d142100c0280d01d02550a402940d5800a00f801c0048104c1d0b45110f817494852140b0640d10703600c1802150500700489101743e8100224070b00040c0ea121340103100b1102c07140070013625202c080c102c4044442c00082e0882c01c407426030000140003031700f1502422165418010751109500c54000c00790b000d007170898a1450300c031020000c0280c945413822907150090f5003840c00040d6503421064002c55829660066800341700c010410070104120303802503502411007842c00d406894604404200c135160420f1080307003400c2101860a074564420802e42e01080002001031042c2a50740e0442d584910b800d80b41900082c3c0301c0b10010805410502030401f522201040f1030720340d40c886c2d131110802810074010440c0d40c613101190b28240340ea020402c0364007800540e405550b8034144050560300d840380c1c5110280f00d60f041442c502c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 739410989 1250 739409739 739409821
    0x160f1406091b0904050f1917071505040c03080c1b03010c02030306101e090311011d06090103090632090a140c03100606030b011b02010c0f051005 64
    0x10360841920f200100b80c65614085007010000702e0525141d201d8500d04940c1180d94100c0c054509024005200448000b0071012440e8031621802414100114048151190a80d40030a9005024180b00d9000a85942e58a04290b01032188030580d54040c5c1a0700002c00d00b5607030a001040300c200c000304140528020007a40701d000050016128981c030300101400507001e14010440c24108404001503452120310261201406010588201d0b0700c5c107140c81c480354001d400d00300d042c4110b00b060320448030050042000383c0e030010710b1032410140c860310749000045c030f075020382c905880c0e0307100308003658070031101761107250f00b100000072410100074206010400c440400c0225540c0c1c0c110440c83c10340703003400a03114a0842d9240032641c00d0301c070f441c40c0c0c4840d10070a5413101050314415a4103100200280303004640c101c5140001828203840c4040100041d8011201c0440c0b40344215105080c0f26115100c9600708404c9c10f0358805100d07140c070f04000b043d41070341c09800c100e800b002507a0740302e0000c4000e0200c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 739412239 1250 739410989 739411033
    0x209040605060303190504171518160e01080123040213140708151509091f0305010b010909090f110f100203090406060507080708160f140609 62
    0xe061140e846001c10301d40d0320b0620444040b01282c550662040000b590010115441407003410281107200c28909402200481d23a110130300c145448030241615284944950120460740c04440e40c410b01c8994980c4800d0000710800810201240290b00d615041d021400d5620720848103e0391164424803030300e84110100706540194068841a2205042020302001032024031401040c8500c808104520b00340c0c44040c461007090400381c81810216400c1c02d1000134064108503903440340040c0181e038036a09001e0401a80320240103000f1003081c010319113000510b02c040e00180c03016516a104410996040601180101074502003040328441984525242c60458070f8020a9402000c2c0f4090140c0d0f40c290060300c2c6040010040075a508000c54065569800495464051403d1600000d0030a00030020b40d5a042e030062011403808415030340e4014164400308030f0321030320042c149400380864544003100c481c042c4113007040b680101c0400d40e02481c0c54030040c82ea007000e03070100421042030b840782001e034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 739413489 1250 739412239 739412243
    0x60304030e15030a0219020105090a0611040905070504060306060e01080c0a020c1306030209010b120705030a02070f0303020705062a07060b091509090304031a060415030318050607020904 82
    0x201e04551004000282c01180180c9a078114110203c18081003a200743c1c024000303040769444030400d0780b03070f180303016400e88000f01e480d003901d9040202c041021900e60380042c241c41520504107458540c548000c1400c0325019600031001680c00b01d01409030707680501c6107001520b1241051251030100b071000a003001d8004201007240f04010500d42003442c000c12214251410042140b8800034111000600402c414030060340f06011407400010383d1030f00300c4100c505003400d03a100b4042541d114079056949500241400c002d07245c0c2000314501091071001143e001d1440b1b81e8025a032550241011031a00f030020b0041c1c0039031600c200c8541d5480205982d812020790b01d0100f1700340c803100c65060400080c040a180184c000c4440002c00204420210600030108402c6509011585860701400d682e0300a0740002004036544c41c0141c02e402104040d00359028000820100303054503012412140300e061a0b208a002c101905d1040c480001d4140e406070160000b66602424510103400169142c8006000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 739414739 1250 739413489 739413497
    0x9060a0e0301020c0105010b1c0204120f0507030f0303051005010329010302120112031707051611030d021605100e0d02060f0711090a090f030f200a110f06030403 71
    0x1103800351400e405442100e001030300200619a51043c01590503800f0b00080c50b2005515584400e01c0703c500e100f6142614094410854413145680e81d0713481c0f031050b0543c01d5600b84508500000003500c0240d00c0c1c02140e00c281d4000c034480c1008822240c039807105030440790605080486480c4900c1040940c40c0b0800c0d12413035850b070701145050041e0001c1c4510484010300129903000800d060401014240156100e036544c4a808080302c400c02e054210240ca0b0ba1000401c01c001c0104119591f00c2d02e421024001c240503000d101c24040002d180140c001c4008015030041c201c00c10260020242500c01000140e4002d8010316080701c004100b03501d40d07501c0320302c60142d01a003038041d504c8000030b454451002d4844a07940f1402070501c00a1101c4000c0202d100c1c0740003100261405540d0b0094510300c030384c00410003003021400d55055809070003082850003005200c0202c409001d200300c203421581c80188024011081c06400c00a01c0200c147c030700d0501a9a80b00444100b0780c0b95141266805a0903140c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 739415989 1250 739414739 739414757
    0xd060e0d05070615030f06050c090d0507050f06072112020d050a0606022d03191707090f2c180705120c010f090e2706010605030601030b06090306010602030403050d0509060a 76
    0x50804400d014054440d50028003505d25442086330018108007601d5040318001c4a0050240401c81c4500c598030008184140302c0c401142d00301c002d5211420f44103102c0c02c15542007072002c03103400700700c0c1c005468819400d9180c0c404e1080c400d17440d10919000c0c0072188082c01c8201100c40030030420444d134076205050051100c42d07034404c5010910a9070004003802d0030312000e810100c60000c255490300c00b800038030142460046482c2500130642c5200311950018001c0500e4078041101d45290100d200d428002e04060f118024001c206101440c4140240d201c800d26800c030b01c2104500e03181d04d5801060083c0003400b146600e000c030004000b06004024a02210003644014045660103425440007082c0400301007800240551802405545d40b84000c6595410801030a0717559240310a10660300031850820204066512980042580c00d6010300706a26050303074100070a107400c200b6400907005030404941841080f10601580d0903480380380c0341582c00e00c5a5203001904501c10744600e030f824452560 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 739417239 1250 739415989 739416001
    0x70f020322030b0a050708070c110d020f0d080a030e030702032113030302010b10050a170a020403050303130218070f08310309060216050d060e0d05070615030f0605 72
    0x200100c05107520400e0f1103401c0c1003030307a5040040c0c201912081d001c00c140f0310004a0303440c032030000301d411160403003d00c024041504040c041c0484803500180d80094400d5090f440e5500c8031214102050f110311580b55030341c000300c5030040469902c9100e510891300108001c0000d40d400040081064221250070b105404140d0001000d82c4121a0b00c5101c0140d44a000403d054040d031209241e41c10549100341c040701000801ca9003403141c2002030000c1403603407a01108400c814185158031184003800180b0700f40d107948540d460754200711112155101c5d10b8001e04210300b00000d5503464020901c2a0f10304074100003e01402c414484070652013000420b40014601c10801040e41c4017107244080072460310001ca001502d03180e0b0650700d058000c1001454001945803000885006140045942940107800c1008200829003456425280030351100c843d520381740400e001070724224400d41c58996641101e403818005651156000002c00c801e140c60030000f0801b0900d8040c0035035480031000905907160 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 739418489 1250 739417239 739417297
    0x7051905010c080901030e0a08090a05090f041203020c0f0c0406090e1e0a020612100e0709050603040f120507060e0c0a0b0c101b02150603120f040810090b070f0203 72
    0x201c640b12100b8820590440184200c2030000d00c0c4582080d00c8bc020400e864800380f0401c100c003504d41916070b41e56040001c004c0742404281c0c0b00c5d184498074000d031600f03285110a42c5066507124032031415420909402010f2314052281c40d0041c02c80c188240880720341c6d101c009817622000d00d103001074401d61800c4000d40e80c60030300c50402d00302c1d801440c180e10703400402d402038120b01d0102c0c0c080102c52402c04002c40d40c100100c02c11071107034205a039010502403c0c0030a02034941c0010b003044a110207000145000a01c80744c0300c4011800c51a61003035141c4c0340030304119060b0340e4244000c14698001c6400941c59448071202c0e82c0070f459103d021695550010034400d480c00411102d04505989404074a1030000c124011314103010306260b08072040b03c0b002440100801d80103a5090368998098481c0d410ac049650000c0e007003002d12000b07114142907a4003011410400c03403103c142400e642d43c01d10798042115007044590000d1191400621004003464013a41d24070900c0100000c1041c5045650f1f4a2016 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 739419739 1250 739418489 739418501
    0x15030b0414010501020c01020a20060f0c161a1e0702190503010f021303240c0f031103070c0602090307030618030906020f060403200f07051905010c08090103 69
    0x103441046008030028900d20365000030b005250041c060191250001d41c80010440400c81d0042e540d004c407070fa003031102003151000c85c825181d0001710501c20840107405240180c94071034064800340c01c10040b01942c42501c501940c000d40f450114840550b0311704030054040d6036102d400c000800d000c011382c824602c5240d01070030740000d5110100001c28881c100403c03041c042218000e400900032002c4000d01e9905900a507603a0301301d0f11740000020008907a0600e120320940303140e040c10817040c004100f13000f400d8805411424010030210710b9441801030345440b92060b1404919401425401d004500414031007502801800180e00802c820020b5070b0300348030250040d54000810003c00820b44841107107051b00c20f80981c04140040d400142071400402c81c4140340007040080c0c811951150360599805036290811550300314024007104105000304814402003070290002c00341c0394907210402a8a440c40205003448400014041100b40d0f00b04103c1080d4650042d001a02c40707481c0e000403002841 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 739420989 1250 739419739 739419761
    0x801151d0d140c0a06090b0d090305090a0905100e04030e0112020903010207030305010f0b1309050c1b030d0f020c190809190e0109050f0601031a03100c021005101503 73
    0x40001c60001010781d0000f84065000c1e015101000640d40e103140a9402c00b1803032084490f02c00c0104507405030002c90740d11000c0b91522030f0816605195014010900d00d42c2d8581120b0710f040c2e41c0708144200328250b03010701001070002c0b0361510030700d190941d001031586d030384026205d05110f000c8204500804a50f015501800400b0b0021502c2e1805030400401504017885198010101070030041002424003040f90440507401e181d295100789040108001040c00501e050301d10001070103400241b8040b00403280c00180c41c04021615a00d0100700e010803242c46040c0000118410015103080b06c10100d030300c07210f007640007107480c80d0480d02c0c1c2031858252040f1a80d05d03600c145c0f90154100c5000300a004c00007031b2201c40c103004503140c0c0c80e40b10f40310480d601074891291500803500001c03901c0d03109411800042a590104484100c42130010925200042170341180d003030380f101840c18046504116031101c13012000d00c20310071800d0000d07000d403800c0780790301171f2150358241d80001e0a0450301a4000c060498 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 739422239 1250 739420989 739421003
    0x270f09081207090b0a200a0b010e04060f0f060510090602060601111005010b0301060f030c090b07110301050106050c190b0402210d020a0606150801090510090513030801151d0d 77
    0x81400000100b0306c0e41e520720b16104003000c880d800448608000707568140d040d804401c00d281d503403c04250f1094a00010021075480340c036402c40f8002038a1900400c0c1c042e408402000c81c5d11401c180800c0300c603000c141640410040c440314200002a40050001d411080c20b081860303074400140c0ca01800c00110580c2141404d0400b400010303c0c94105004504a43c150303500c01e203d9494010084054802d905021000075201c0c075030500c0600c42050041c02c42c1751180000d042c010341058003007030070341d14240d01140124001203041e00f00400140b002c121080c4c0c0140c0c04a0780f684056690428612000c2c0000e4021040e0303540f8216861107442d40800d2a004c10400c0315040c0110b04002503880c2841441151000c1c14030b100058102201d2202d800c982c051621681610f0f807c1065440040000516401004a01b428001000c00311031255501401c0b8980b507500c0704505a0034041c000310384c180d105064804c141c08004003490342c81149201c01d0150203000c0e0201508581c0010441e07000180b02429030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 739423489 1250 739422239 739422247
    0x9030909050603120d0213032303131406090d1505090d0c1403071e061104050d1b0b12152704030e090a020703030e070b07020103020702030106270f09081207090b 71
    0x8005003501100705002c25142141c1d0b41d080b483e0555882f4000c000490b40303540101d910900c5071030301c2d843e61a1003101001d0402420134800304001020300401d0007050f2540c01c407000c0300001140e205d0041f2503001d003a0f2002001850003a150040000300141c4000c0c03d1000018090102d400c0b0030b0080760392031074104500079400c090101e414502106080411600c451030940400c2d0849a15001e8608407030006244d0400a8400c0e00d0f82c000d030035080a5203180c004003609000c68283c4582014001c10711410029009a103081c4140551030800580420710035001036104640c4030100401c1c030340c142e003c944821507554a45103801c3d20340d1985a104103500009013000c11002d40582da0150001d607010b503905004011404240d035469242c103014420181c0c41c10003115000d94000d030010701d0294400b60000501c4c664440301800f4501e01c2c6040c015040c0700080f035050100701680181c0d5018441c4c2c03c020840f8140e940c0c0c5100d280d10900f00c1d108000c1107100002030543c0d0080c18400014540d84d910103950f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 739424739 1250 739423489 739423493
    0x30f1b010c11010509010605011706040908030a0b0f0316030201050f0f0a030905010c0e30030d140a02090d0b07030b10031b0e13020c030708040909030909050603120d021303 76
    0x65881000c00b04503266103008002911440305001c0c0208580040c0c4907400949882c200002140100801d104c0c0c0043d10b44490800160070180118412910203100080260b070b90010000480741004c1840e20a5102c046504a56074820034003008503030342406d101d076844038007407041d1486018528120a5041011484a2400740c240c2c0142100c0303446100200101041500f041c0c6800c1020080356030044d19081000a003415240d051501c0b64181d9460400b072245c1c084516407442c2c0c0300c5800f0448ca107480e10003c440300c5c0c081b188201d410100d0280b0030b500700342c1900c003c141245c0703000744082c00001885000c100c502d4024dd0213072003c010080c0030010402c508082c0a0090a002c8164001e00c1c10340142c00c035400ca00c9515500c403003440040141520f9495800080c01a41010404042500080000000254115004000034000140041082900360502a00401c103e502c04400b15040c2410042141d4002c20301c020a90501211142c82e8200c803c201402400f070780314100d203103d00700440442 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 739425989 1250 739424739 739424747
    0xf0e060307150503072c190801051006021606050304120908030a030519060612090515010f0f0b07030f08041704092009010504121a0a0f0b0f03030f1b010c 68
    0x44a01d100c0e032100c0003004018902c800d604085074080e05d82c00d000f002103000c51450041080d03010040840da007c10515103548110303084071400d40e118494901080f000700211901446400d02c6480308030307120001039180040c043c00a00c4001c20042c050041420602c41c050301511007000588555000c4a4480703281c0c1c00003400802e000da500c1d030320241c402c00591518038900e0140318180c40c43c0d4ad840d10005103584000502410004408075100e0044609038120594400000c0c0d00038010700328504c1e1890300d000418820080c0981240408410402100f030101e500605490b0240c100380ca090706c10341e03480341068800142101d40c0c000220900140008070801190010400d144400304400302e1001c861006203040e01c1041e04842c0821000d03c41049062040a13050303001034050304d0841341090919650041140084501c060740a5a84600c6088410350703100c0d240082405644c01007181400000295407802040a030900003580011000d00301d94803544c4008800c0000c80c0244159090341703a02170 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 739427239 1250 739425989 739425991
    0x40602011e1107080c0f0a03120e0715081504050c070c05030303010e040b070e0405040c140a0501081f090905010b010807030504080306010f021c110f070f0e060307150503 75
    0xc0340c8050000350849034000184551644082c2040c2103900d412030558400c03111390825012000c25000395950120585028031103201003600c60755551b40360940d0ba000703403411100351030007100311070303016240a001801040d41c01c1c1d030000b202410410441d5441280d10000c2d40306494903240c209041906002c114001007020384411807054081e605095200c106056480c0404d10802d0b40107100703440030501040786d8890300b41c0c0184141c17501c0d11302c59628901040640d0b40940b03044410940c0f28100b00182d04a18070702c400c04580455000c00038a10b0540001c0004101601102c0c0141e0800e503050010400102a0402010201003d21001c1081d0420a00074040c000c100b6020600d0b910014001606c41d1240743c2c404d0303500000090a6407514801107540018041d08042075224110f0070500d50f010030460b40100845582d41c440031034a142000381d092040f02d0450310303203a9110303541c2403141c09540310100c01611030404000d00a955000d0000f85010800d40c0b00022000c0742043c001d0030140d000c0025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 739428489 1250 739427239 739427261
    0x10f050f1207350606010311040f03240504050a0b0a1409033c0d0605090a0f0605040905060103120c210201151404480f20011104060201 60
    0x8040400445002040c0760901c3c807540b100140c10603000194558000c0e030000411504006055080a459505400309040d0f546c0040c1c80300d18001d02c9440b500c05154212034201c40c01d000092141d8203013517480d41d40c0c0ba01d01100040014580c4070000c0d00b021160380c810204074024040200340790400e410601d88a5000035480502001456500e18208000801050b0030200c0380b00000524008a17124409507008240f00b414400c1c0c907010006404e944e15040c0901800c6041800181001d40500000c211002d035400180a2402c0c1804800850070110f090340c11650414598806c20188070011210300f0707003182d40241502c550002007001c842c1e240c4000d00342000c4680081092a501095807500c9001c0c17071140d0f0b00c60360304d0149c244c00142855084400750b00842480d03034401140104d0003031542e06010b180301c081030050704682d441c2d0103c402d40d2444410036608140019400c1180300800e006000343c80c54141c182c1c0003041015240302544064040302100301e895849a8031004001d000e00110089 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 739429739 1250 739428489 739428539
    0x5060402121614030c0409020109061409061c05010f2d08060916050102060402090103120c0c09090b010b16171303060b030616090611010f0c020a1406010f050f1207 72
    0x5e2000301c3d090510030001d5168050b129007140a01d040d00c01ca440d11480c0c0da021074280b00c180103580c01510713080082c001d10200c007541c00b10540c1800c000041201c505a0280641502448042144690300c070804510b0400d0300301454004001540400c5007100c29030300903012480307020700300f08568101140007103803c0c030013403101490340d0394a200480e82c80105960107940101c03600b004000113a100012001000424100b030000748002d600d8074000d50200c1e510001d952520f0310344880401150714131040c09442540c00c0b4505140000d40400401002c000000740545581020070703503440c4075002512921101e0712a080380b410303224074000c009041500c1019029104240101e09214204808070404d0300c203544d40d01d0751842ca0700804840300c2410903051150341d5641d0804d22000c0781d05004048112802c1d4000f401d0300302c0d6034542503000d1250010901c1e41504108010301c0782c800e00080040450b20100c840d0b2112241e4900080c62042000380c404125200341c4100080981e01e4012050080c507228103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 739430989 1250 739429739 739429753
    0xa0b03060f0903300a0608070806040c030b0c1216030606030513020405071110020a090b04080d0f052802370303021b030d15030506040212161403 64
    0xc01c408540e1819104541250030a00c40710090101c9081002da040f20039402011008840301e1440006500c1a0752a46041d625060140003d460801c10341c0000c2840000a10103031416842d441c5100000f800014001d24120000c01c5044aa000642c0c90800f2591205070050500300440444002d00100f030f5000300e03040410001c0c0f0940a03100b03880c819044400f5000c1e0465141d400c00c001810014502d0b4207102800c071043e0380e1000204500d1243c0011200016904c10312158040c0c28040175902241c0701d03081c2048240608200424403100701c0820b400c01c0843c00d5521031068446001c3c12008009401c41c41190301100e03500103248000d03041841d02601c0000b241c903d0701d0f848540340300c0c10640466507442001074100400d8440001d049019180060405079070f07040d03800340344100312134424a07980302140035802c1d0342c054891041c44845441c4a81c2206d4919aa035030f88807000100080c0c4070751a03c20014145620600c00d0b2000c15000344613403102c0985038840800380003d1281c4050003071003200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 739432239 1250 739430989 739431001
    0x20c03160302010507150e0f061b0c030d0c020a080c0309210c09040f0206040e15030703030f0c050a080307090f0509040b160c060525020715030b010201090b0a0b0306 73
    0xa45031506036070301a951640b60421644030980540d42c070080e01c0b0030185d03a64580b00490030081c81080c1b0580d4a00020709410f080141d2880381c607903203084042c0b02007001000080c4107000d0010071140d5114148101041010f02541c060781403130000c403405404280009003440c9042004401020741d107070200c072003d040484102d0780c01a0750343c000604100d5648803605080041c03400c441e1007a0b2003031040780b01800360440b40d4007103051a00300e54440c0320034400d400f0a000b07801c000d54403c44007622068009202892950b10000c0290074202e800308280020700d00e104040c424140580b0704005d80003042103a072414480c800500811603031040440c030455000d80400c0c87e150040c00603016941110044000b92035803400201214001d11400703003844030300c0340750100050280c05024420402c0d107034032942c0d17591003140004202251103202d204541165100340040e00142459410601141c45e000640d02e5501d4010703070040030403110140a00302c00e0030030884c1d555007a4000750400e04c0103409640c0349803124 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 739433489 1250 739432239 739432273
    0x405010f05100611030d111b01020a1d130e07050307060507050c040507110105010e01060816350a0b1c0314030402130f0b0307081b0d0c05030706020c03 67
    0xa80e000d0440c08141c5004211052241d0b40300c0b62a070803c40700b5a0700d0a1001c803240812584c11510040c00b00e000808d00c4840050005024641c801c40103009510703080342e10000a041e00070a881c07111072940106510510b40c2c4507072405c4104042036820410403d00b40c0d00b481e81d500c02ca40e118092003885807400200d40140b042064030b202d41d911200a115082c03c1030308000c003801c5c00600941c1004003024903011401c100b4001c6a000301a040d100f403c8550400d0001025040018840008488542d14541019603c1185001c6000d20380702010701c1c07c52511440b20400360070100c41103a10f02d00c0c105020070002d803039025001c40c1c070f0103e03081c030454208800070000304d183e40b10001e008540c00e885c1d034914410010005541c02480100b0b4407070702c080c0c1c40d14000c3c103c807050021229450365800341c0300f216090800024001e48a000010600311900700c40c00c9a1206800c140140104100365081c810405030b54048070160500505598840342c0301d120082d1394200c0485210321910985006503170128407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 739434739 1250 739433489 739433491
    0x50901180818030c0607031215180902040b1306240906080a02040f0b0703180f0b0f090a03030f08160f03020901120507122304140a0503040308030405010f05 69
    0x40846254203082ca01e001150000382c40b0791180340c00d40039548011035590345881c004e0160358440d440741150300f1018a000011269800000060240c00d1941841100c2d1590758030070503a0303400755000c99505528400710340681428406140c10111000304440851065000101902c03081850072000d170442c40c21800404038007810600114011520600c1402d01c140e0b055648800151000740c03416030b48404200102405500a05c80d10b240070034008100340c0d100e280c2103101000c2400c060652403d1907400120b41302d03a40308000d000807001403102c070400000420751383c4081008000d045003c0daa810064040034400505000082d503c4000a922141d2000c000000380129a03600c00c0c40c020043e4190002e5009061181c140800329240503003d0155001d91031190440f5a9808110006038407804c05540c182440301c1d0346041c0c904411420345525401a5500c203800036076100f03103501c10784085401d10488400182043c000054044140500c01e002180101e104070002c010500c4040755220440d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 739435989 1250 739434739 739434743
    0x1805040804030b1503030406030e0105130b01050402090d0204020c0f100603030e010c050109060509030a02010c0302041a03041a0f16020c150a021015140907051903140a05090118 78
    0xc0180001d001040901c00c5959202c0030804a1140d2044e2060010380b850300f01d40c6c020800070f901c40500080ca92000e0090b90340101d1040114010030040c1e948000c8100014041c42d4041c81d40405e03555000d982d105e203441d0380350742c01030011561805100303100f80d203070611800f0101c107511034150000f01c224440d1140201300c0741c06664514180007441c2c0112280f04000700260b81c15900c540a20b4041030143c85410b000d1283c107070046030350b000d05010281c00e507005091880d007454418081046064a9403040e03243c0702c0310340c2c041e5503506d6a03075162401c3c03c11411500160583e0a9000300303d041d60b078140c0118040c2c4000c4812090200b107040c0100e1303990341c1d8208010342100362416800e44050140d4003400f012070142c019902c800c00002ea104049860413094031400260088040080e001c014103e942051403c0e240d0044503d05540d000c0d040c0c0c0328001310700044110b000b1721007444520070b600c500b480c0c3c9030101940300203040a01c801c1025007001e4885144a500c0c2c14600c46811052900314044a0307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 739437239 1250 739435989 739436003
    0x6010e0c0a050a030e0d021f0e030909131e114014100b191b120336020d06061214010b06030c40180504 46
    0x541d5030004031141d4010a50b418145615011240e130000390901140d04450303801e038000c2076041c0b407036209800b080040808114000c4d00e810380b407000c07034213022007111001030094840e90015183c101d10322400c1c0c100b00c40d0161030b090300413004012800641255004103030007203c0e810b00300e112580420006a1503050510103241c0300a00f82c10031403045202c02d40e0b00521103040c07444415a49010003095035015441e0304d40b06000b00c0200212003285451503000740880d41d03252800c00583c12600713501074070600c1c0f10000344032564516203000d1801d0030030385806513032003804004400245500640076101d6000c442206448043c1803501e07030340304001003a41c148010951a86141816001d01c084140c008009aa10343d44554001ca00070b80066050f54034a4407411880450100d60b603200c1e821601040000c1e840750100b0401e00c00760748502415207942007246a469114507141810b42a0740601006a1065100400d50844500051303000000d00701e84174142400380c49129040c00d181120002c0790b0083c201 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 739438489 1250 739437239 739437247
    0x4090e01180b040212010213210b010308030a020712050c150912160c0e0f0f06090106030c2705030708010207080d050c040e090c04140601120c02010b0a030c0806010e0c 74
    0xb02e06001071554000780043e005040200768201401e0999102100344039010390706039010801005000803e00718220708a10300082205190341d410a01081803002504007500070001c075001031056811100265481404542c1c45041c51401801035040b03076242c12458000c0201c071308030b0700c000030980c1c5220b5400c0e1000340a2407040c48140079056000b01d40d410200d200d0000d240b07000a5844034500c000342240d0300140d0302c01d180a01e5215141c2c03138014640040800c4c110248100b94840443c2d41d41540c1c003c0c140841c5d1050400401c9074107024042028185004222181e180c0241c10400001543e4081c0d05940c1e00c1d54840e0400b900380e1090000090502c4400c0015003007503000b55000c42d80152492126a140c1a40c036044900b0aa8003980c0510300394025076903010b201d10349842402c0c0040036800d400c01c03640c684000003801100d003da94003100a61036101d0825410300c00e40c01a5401c5070002d10300c1c2c00154030381c24048884c400c0c034064159240300340ba00105a030041c2480301032082205000c00c6281c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 739439739 1250 739438489 739438493
    0x1701091e020a0302130b030f131136040b01080d020c060d0e0607080a15061707021204080709050f090a030c15092f010c1e05030c0304090e0118 63
    0xe602245182c010964240145401c40301d40d010408020001109250340380e0070a030005101c808005401d4501c980201c1a000c8002aa0680c0324520503a084602039000c030782994075040070030071f0790b0340c001c0d518055200c18074209034002c12100d008078000c070382d01c40c0242e0300c0e070b4a8241e036040002218000760b4499600c07410300b0b1404c01c0041c5000300c00901c0215a07003012400c07a078603120b801c1e03034107070042a002c4041041155407032040c1c080080e4058841d60106150a501801e4445685113403400c0c6502d020004445500070800301902d00ca15031107440d0f40b075a8035812161510030a008035130a0303c2c1007801040c0c6a08101d915240501e5103d80a1300c81203d070f0b580d06a50800d0004003c49480c1c0800314286011146132280d0340e501400b440782c04070b0ba100d680142e080054080f20700350420036a030401c60304243c1d81c80760810014590040010b05512003482c9a1100400c40c10740040540c400050706214000340440507008030340d0400b1050011070120080b40782030312100ad03c145041da010181045c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 739440989 1250 739439739 739439741
    0x1e07080c0607060914070602010b040209130209120f010b01180b031f1203031a09100506090a030204020c0106060912020105030a050601051905130504050906010302010302070812071701091e 83
    0x41c0c034801c00c00002e00720803d95518080c0d1017000400c00300d03904000000c0201c01c0d0207004034864a8030403a41140b4140e80d120010340c110124200a80c0759583c0488c0c0c0c186d4a48424004981c02c0141108944001c0480c0003000d000e07001c441025400110712250420003c0320f24425401a103520098642c1550350302c075841005170303c070001c2001e00043c8400e1300240f114644030781d8008140c043da501007034400015882d0985001480c04013800385022070100004515415006003d88000301d4040740e446038003900280c000381441d000a580241300046840203104154401e0703088940030384902407606d07030726940310000c4403608070081d001c15820400100451000d90240f5031200c0141000c03401c001018424100100105a8400119030b0004400701c0d02e2100c0c0804000408040740c05001c01d2410008207511601c0601c0000d0505401003881410411079500b03845c540d20740e5011400c4145809100144100700c0340c510345008242c10800410b10600300d00500d103201ca02d011407904e90f413207800c9002c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 739442239 1250 739440989 739440997
    0x27060e0a030b070215091b040c090902120f010e04051209152209060f0308030601050906161118072709052403250b0703021e07080c06 59
    0x650228440c08044001819251168010106540148042005200e072485131a002030540c140b0340d030002c01d420700341c101283c003800d48601d000d03500410885081c21064540541caa045014402c2c00460101c411030302102201d84200c42c1404421081d90381c8054070400340d034054070050002d410840100c1c0b030100500d0300616605030302a04041d2069158036200c0741642140c44c2500a0030070318541603685020313100e0301c00040c005140007005000d160078a150091610703440010f0003d40c3c040700142c0d650707010b141a20700c000006403120342d5841d20214511075a000305001101e100b50400b00d814a83d0030030303601240d0710100010462010346c85090050b40c82001140754034100e1404072403087d84090f80350b42c1d01402004995400300d95814509881c2c4d41100c0101c1070400c1c0e0100701140c40b6002d58000411090707176121846c40031a980d03591007050801506039000340d10030a070000b55000c209a80080c101c00c181da000511610218404e242058880355244108545c59101d60001031562511034010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 739443489 1250 739442239 739442267
    0xc180903070b040516121505011d10080109051507050f0f0313050d020d030509060f0f130503040315150e0705160218011e1802030405010902030a050601062706 70
    0x441d0481450381c2d0494100005c5e410041c041012074412100300701011800b07003000c04451500344802d6040074801e440c0b800c8011174014400e0b01c040e000c150540e2480d81c0c110003420641c0000c2c0520701d6241001c0f0b40d00c0b048400c007003030000c20200021744141d10440680701c5c85e01c03000a84514103840001c41440d9a0009070100043c2d0700c801007141e00254081203035200c0c1e0701490b00904907002c1c46001c0942203507402012500550408405c102c80c0c1034015030140d9110300b0200940502c0d0310361410f25510b4140c0c00d1001005031000040100a1110707040030a0002c04400b08140581c100d000340496241c0524450000d074081c6e0080468003150003035002d41550410a0184600c14806800203007483c0c3c590071403803600c40c0120005110201c4c0301c01d819249103c01c4107424990703500d000d006c00c1c41041e42d521f500300303920b03404030104007084800c0d000040742e50b8009003290844500e50815035202c007000e11500020a43c0045c06014894000044803960242103000101c89880c05106946584100f900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 739444739 1250 739443489 739443493
    0x5030a120906051921060e180303010e0403110f030f13090c14030c0d090c050103050606030f0f040317090601060e03070305030909040f020a09020711061611060c0304080c180903070b0405 82
    0x5585d0100089201d502e0007001c1c3c00c0160f130014206031501d0040500e40e52917007400d540042005001c81001414050b400c9a030501d000b00c084030320b611805081400100b02110340e130100144401c1603c00c000302500c1002c0c203d000d0300840d00d542d18490030446d03220020403004140050901c205a6642101455001c1c0410b44190f15051150105904450440b0300480b107003200d200f0144629681445811360100081c2d40755807031414050320f001000c070401051fa08841d45418001410184540781181d14221760844040305421b2201c05691100c00c03d0160702c00140100388803c0305460009911001c40c0c0d0001d02841c03510340688203100c2140c50080003907518502c20844440140ca40b04542d20041501007030040c0c50301458034189038058200d01d080c40c4107400c24000310181c074100d15504080d030340c2c4c03018003a50003128440c08540d050040b805800d08502002c10001203182004c101d01d90944401c940c60b84502070380350144980e2041c2602c08100a0340180809000214500d20050300b15000b901 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 739445989 1250 739444739 739444787
    0x405060f0409060b1207140d020a09020703030605221a0d06051b0f031504060e07200d03090c090c1b030509031906140708060d0204020405030a1209060519 68
    0x42000a04261170711102640300070300170003210645440b00e5402c05001c885001e848406500000e07220427a0b8014040040d034005019003c1502951101009080c090403002d51400603405000c0d40780300080c0b40305004e50030065030144007c0b0108011240102c0105107202c1e03083d160b110b010003070200502c25240031110303e215045584114002e40f150304990301e1a2662845d02c03c3c8025400060100818051428000144540d81917042c01a0b808450762401c000404c20f0a09141401003240c0440455402089045514190b2680144030014000c051015005684200c010125028451058002034800c8031140e800140c0b81542841103002e4038140d401c000002c130020b03043c00456200d011940101d040c10034208002c600070003104400f00c11134202245090f107009001c3c007000602c0395104000d210054421547c41e40c0c1614040c010140032142c145030240342010450146600c007501003140c4040010300548220304480105201c00b100310540d0301505030030f031242c0825203040070b8100446d0b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 739447239 1250 739445989 739446011
    0xa02010e03030103080324010f030b0121060510110703020409050a12181415090d170d0e0601080a080d090618061109010203091513030807020901050405060f040906 72
    0x101443c061801841580da4a0034102181f1010090001020000300c1d080c00c84154660303004250000300d207100c0d08000c140542c030800101da02c1074803010b1205040c0c0c000e1148500101050b03010305c003921000c0d615100882d1804d24142d40030059000d13000d0241d031081c0002d00041c10704e60808905944180704440b200501c80d512550281e50120700358001814501042c001102d14070407a070010310881414464404040d404074035410b8594040040305d000000e08544580c0701e10810341840ea07080404400044103c0140b28042c2c1d0200103800d61541c105000001400300c046080340c101c039100801048064420b54403142c89410040c0b4071400550394821035808200c040c026914544003408100e904d203451803802c10121003544010280d520700500c40440141d800100721a506001118001c5021200a103840070520071640103004000707101c0400030420450b00050000b00c0c2c82140d84984c203a0303c1e0400d1204668046501c0c95118440000d4030119052590206100c1c500410008c42c64540003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 739448489 1250 739447239 739447243
    0xf030a080a030b030d090617091608070e070e1804030c021e09091204050105030c070c1527060c0201121d0610060f050c07050a0905060f030d050f0a02010e 68
    0x1240c1544042611403c1041042c902446a008240c1043c28840c144904011000340120b01c07000382400e41019500101e907820808000f261b4030b200780f8000c22907a05864005a0b919045a8803e0f055542d56000120f400346010b902035a07000b003c09807101e00a203c00851030351500a01800c1541441b044401450158580300c8510348800e0101a1108000c0f180c42d050103030040d070040540240ea0400710f400c00940260500b281c0c1100c609182040d120b4950704c035041d420348100c0d0750080c540c0c0e90300b010024901c044801403194032910f41c1c03030b5600000c0210f4000322410001131469045021040018000c10b801030458403149801031400310603a2400801e50001c85d2820030081000007901041448040020848264404190010000e000349051005843d95030600390004c1445030128040e0305482c803c00c003440c014800144020a519920326502c0c5c01030001303880310380c00f55103900745001080c2800600a94843c0607552654940b525403002800b482d0001320f030010441d52500741000401e281 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 739449739 1250 739448489 739448497
    0x40c020d0503070306050402181c05102408010c1b020d0206071103010e010e0f01020705070621020d0501170a0c1e080a060e010c0f0212070311060a0b012303060f030a08 74
    0x404031b10144040106081021810b04ae1001e0002c0c3e010a01582c0c0000c2c81c0801e600e18502083e02011400d070101c02407050302c0d98000d01980598051f00303e4000740d829415005000c0e03221960b201d1100c4018480c02c144d44aa44180c4040e40003401031140c800142010b40003440c0180c0100c0005a8000720f010001e401d4440442c161105691107000c0100c0b8140b00b40a00c0c3c41c40700407800210f242c1019642d07921f031904a148030b620180011902401d0320034441e05215890100c03251005c540d40c9040080002c020542030151000044200309654900040001c43c00e16080d00061510061880c5c119901c00d04d2104080d01e0034a00f441d8a030002c0c02003810010000b080d840f500002c101042e40340040ea0071600070b0580d160400c1002034290740e1440d00860030785514681030201a0b510394280c181a04c003e000110915224881e12040200403c2207502c1a000100300b44c3e03400c094200451882d052030083e0850300a0402010804102549840b010300801c9040190642ea034104103a140c42400d500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 739450989 1250 739449739 739449757
    0x3080c010603051009020a05360708010e0106021b0103022515060612090201030b0d0b060102060106030209011d030f0304030b0f130f0b1312120b040c020d0503070306050402 76
    0x1d1aa41d0510402c10240404c2459820f21401080102c0c03140c5c00103031458510388580341c0200f10086180c43c0c075224400c0c94040080c5000d10181c9010403404401104001c12130302d0b4400180e0071400812034254940005040340d003a40e0050080344480051080b800000d240d0007070505900300505c40c4070700307401d01d10181441902c0f81d4247c00e00241c1e0800c480010340941440100c1c0c0d00c3d0142c2880301c203030007a58a01c10756040c400002141c3c1001e10041e001040a6581c103a48820320940c10010030001c0740065124030340a0342504c20303690f6181800e40070b9009880200e40451007100030b0b40b200c540f044007180c1c810700d401400c85540300482100326085501039001a24103004000801c0b031850703452040740e034100c258182e4905101d500e946030140050040c0e42c00030300110001003c01e40100141c8080c1014a0708580e1101203084e4054000d4080000c2c09400c140e024209034400c6140d2901d07110f01c1441c5c2c21503070068010b40c20f5007401141c461b8402090300003407559802c1c01049640726840a0500c4403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 739452239 1250 739450989 739450991
    0x1c020706020c0f102106090507120c0f050706060b0c030919080c0f0609130f060911070308100b0409090303060e242106040611030c04140a03080c01 65
    0x2414100002d00b04601420810300031800d1099002003074582866008103c0c100385040400e00501e1401c44124807107030050828444c0c100b820204580501b070380151f000d44c0290301ca1003002c2d0801e0b0740440994950710745280204070f2000c0d508851a00a20040194134030a0b07100185030f64860030f0003c10b542040d110081181e00c0070451161605250322100003425900032074010840ca1700c4d88155590000c00c650700d005d00281010704003075450340d01c1900c80040f001408001c90640b100c41d42e0000f05814400940094240500000c21000504c90300341040303600c01c0110314006aa84064842030340180c90007010b005180d0001500c1c010700405440034142d17064006c24402c8250600500396980c83e0011180110200248020b00600e480500c1d00c8842c0d84948030101240b0000040e41c01042c8020552003801c0c030000d80800000c089031031032103a44501c400304010b50492b079007504d1a00046508410b8100b01704014400340c041e400040d4000d160003400f500103a5102d55484110790061600c04180d030f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 739453489 1250 739452239 739452253
    0x1c020d1211010f05090f060c030c070c150c030932011106011206050a0b03031902070906270605030613110d0807032a02010e0307030b04210503060618031c02 69
    0x3401c5c0c10f120a200359103480d40204071038140114140440d20024112500c26040000d02404200c43da01e04840141118111600c5a4242e00701c0603260750b520010031400070305020000f0810000710010850041003070404980011840d01c1841c010707001101c800c5061000000b030448040320300b000b030385010381290700c10101031800600e4940305486001d0201e00e119400e065581c5c1064400000361a00303181c24201409980350415030503801c2203c1500001c00c458240600805c41c03400655110421602a00d0700140d00700c50000800c003158241c3c06801c2d41600f0100229000a00c88a40d4142003401843d221100c103804100160740003881c00300c01ca0345c5540c0030542d1030900d500503400307200070046241c11503d10f01c410100400c800b50b03000c400905100014a16038001d84040044902555101c2d8018001d03050904000c031a9826030a8070100c080310344605130172250f11400c03d0f6405060040c0c40c1c0c50500d130031558095541c091506000350144075a0741c0c01b594181d5082083c1750811120303009060780f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 739454739 1250 739453489 739453501
    0x4091d01061a2809031b030209040206030a14071808030c060106260a0c0f08060f040c05120414070f03030516021f080619051f0c08040308091c020d1211010f05 70
    0x14040ea0341b44098030851402c102000940c81c6d05000ca5031081d0b044030172035560382e0341d452450020001d000005124039244020004010307040708003403410524090740b1004540c0e03552903041d564480c0711120340342500444010480e150040305065a1140074440c190340e080010070302c014009004440722505552601140c030605900480420b107401800d2030204074501d411404203001361050b502c01c502947e0741e104400210f500c100c0c1a62481e800c804940362090501d42410646c410720100721821500440000203407680308400000c00f182e9040e21451b0406200d5420f460100c0300c0441d0aa0300301501200144820746121407190b00e19040c4c0d240e44110f400c0803000e004424111589505409503000710a20076a5100f071107051440d0048507d22240103000710044802c50840302c40140612070100d0084200b10030380300a01540201a40e4042c8a0307201000c0d400001820300c00c0203900702a50900c1c020201e40c104a203070b05651110305241000000c030740101d40c211354030060411880390340c400c00d00c20707 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 739455989 1250 739454739 739454753
    0xf270f140603061303110f07080c0918100207060f020d060305010e0c0f04090302070e040303140c03131101031805061506070210080907030804091d01061a280903 71
    0x41c00030400c2d0b006018130703e40007012161035071005002074180a1035030146946001c0c00c105800b8207201c5142550511030742c820b0956598500d50358070034400d10661000503804045c4807180d07601c0380c2e00c8400401100c1c0615100c40000c0d400984181c0381c89444025070200001c46000030030341d140c000080000c10178518149103003141c504413601071858011034040641d90b0340300d4401d01084901110001b171284060f107010703460940f00b50302c03e04485003114204800c1c50741550114500790314400840d10603903180b0728841d0491001701c4020720b852014603004008510000503404442ca0181070000380b84214489008020b0f01c0500200e9881d404142040038803485000002d400060541d0383c241407400036800168002903040140b010409240d000071b51845080040600450b04076038050b60310383e00c030301694000e85a1207807161020310007038035802c90040d014481c1e0f400301e0f00e1081c004401c108180003501603640c0080c3c261040e00305031000c070310840411a00c0310140c102c01903d4214000b0f02e0b6291181c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 739457239 1250 739455989 739455991
    0x220e04020a091e1112071107080105040210030903020c0603090708121e0307030204180c03050915010b0a200616030b0319061803020c0a0f0f270f14 65
    0x209540d07080090304400700052401c0e022020355030035400709003905265400581c50040440b041d19807101c0380188401107802100c01101002c120098030823031a00c3e500c0090a88509a40082d08940c0c2042c0c0d100c8a903100364028000d03148284140c40d4007c14410000c0c501d44c2041d140e541240d0084203080005510401030503100076910010541001ca1610100b03000c10350782880d18204041c00000580000d100b503040310050001c04207180040c0c1e100000c8100140f100074011808645000d0209100c58030018107071002c0700d42940c911900341c0c02c101800c4410341003003c03040f00717000303206512724090307408041003182959902c2c0040c003192800248071a100e0720500914024146052440d05241d180400c00040c0340f6a0108441503040c0c0d1444c0c41d000503d9040200645120042e4558003007640c04103000004900c215045a049510703910400704042441c420103400107054070702044214071407010310358070120041c0c9441e00c0e0300c3d01800c504180c481c070b8260b1802c11680c405064040a440310121 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 739458489 1250 739457239 739457249
    0x90307031104060609140d210806040f020304020d03051e040b0a091512110f19020d18050d05030f030a051f230a0909060e01111e220e04020a 62
    0x319200c0d62034054000921b040e220140b038000c41900740014288186922840c0304081c04945d43c040c0c140002e5001840b1080c01c0d102e0503c5076041a000307684007110b5000340d9000e82e80040c03d5902d07642d4581d8051f039095102d0140b180b00102c1c0e00343c2202440d62400050402003040e1304141d80e6425480b04028032208154104082180c0c980064050352a805a1035204401c00c4c4c51002404050b9420003100307900505c201e1440d14200080d84203400c034120389404514481640031182d060302c442d00c0a50707404034071b0b10301c110040040a104000601d0a000d8202c0030728000d400742da01c0d1080c803d0054090764021242d010000d0b44400c240942e0060900c152400da80d0910508101e40d81003e8221290042c410841c941000340c4d94080c55040d90b803101d65100502c035460007000005030707628280c80034142c80d040c00c0040d54a4105810078004000f0304a414080e91081c0c600321240e4130903100d090365000280740e1000c4d4101e03403011525155070105540c000e400c94043e41d25852505204104419495804c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 739459739 1250 739458489 739458497
    0xb030f1b0114030403050304032a05280f020a0e040b090f1504031d060406031a0901031a0a110d140907030302100216050a0609030801150e040f020903070311040606 72
    0x20200144032204240e0390005c3d854580107540380c403103007400c40d030445c4035104600c1c403082c462044843c00382e1035005040d800c41c4140207440c407200440e450000b40c040c1c02020500d0f090700304a0716500042070440c0c00c0440754402403140d50480d44031061940d0702001140c003110f19003920303028482c484108000d0001802480e600510320201d41c90341c0003d0346030026200030103100044211124800c51101d80f42101100a0981da450355901c03032000740545140030304000c0e144000c815444172410a4014103050300d8001c0c0401c0360071200c0e100c5011803103500404802d02c840e0b48010f000c19145002d0000e240d0b41c1d44110012850307445410b1464808000940303c6811a40310000400002c1e402286001781140300c204011b844030162104041c242e18141d01c000d01c3c40c000c040310341d070400c6184d030301080344a4083c0d51010001e80e21505070305461070150040c0801318120800708402860250000f600c4003694038070250600303c891000c0303807070507203141c00031603003008040c8411040e4140340c802c56000340400e1074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 739460989 1250 739459739 739459757
    0x60a0e06010c0b2a0d0c1d09061804150b04090c1a0409111902150a0f0608030c07030213062102060f0d020310090c120f0b030f1b01 58
    0x400030b01156101400202108440d02c0018051100b094140180d680030007000025034055080311030060303002110115200d40313002c2600194511641000c3c8119540060000340046401d0410640300002040c90740d1180d05003284004002001d032985000c0c5226941c0940109d042c02c0e2030505842d420000c460080386040c1c0b200f004903074118560000c5400c2c0240402d01038841703032a0403c030f07842540c2106c828a03042c0300030003a10000d100000c1004101410121206200301c80040340c0703d40c40a80c107032000c0d00e440d4010402203c80d6a11500d0800c005000c0010f4440d601c107074060071500300b090403c0e10b075040800e0070825800c2101812010000315402041014104840200c10211f544402030302d1002c0d0042400840d00e8580c00c40d107043c01400981510381c0c4400e041040650300c121200c0d01401d070140c3d00082d5400c1c95008640d0085030540340c603820340e01c070602c4110050404400c1c110b8201e48800c400e0034503440501241308032800c0c0030040c041c8030781403070301101c0d1001038409100c0c10452020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 739462239 1250 739460989 739461001
    0x11031f050c0f070204110c150a1805211e0901030b061905090d020604030c0602070503070b030106050a0221040509010509010b041e0503060c070b1f0b07020406030c030b060a0e 77
    0x1007100e03002135040740e0020300180d001810059a0081400060b01485507624a0500d05841d4428902c211030041081c0401701411214101c680d145000080480d40580d400050025040740004100e0f0315041800e401c000758900240c0e185511f440940030b000394000780c132130700c07950b85401542170006090742c540c1d1800b009003640c003101c5c1140340c401e0402c1020205490036140c1d140e202800d095500104010303104c41e140e00700380b4040307131080c418000540321f80140040c0c0c42c200070494100300c9241d00d030a14150703840c0c1380301072311243e20981181c0d0841c0680b102501c40f0000190b944918010b00c00e8000c1e071602c0c10141803052118068120310320440c068001000b86203a543c0c1164269100c030742d003100802c007030182e4041c06000c003a046964940034200c00c001d9030144040181c082d02d030041c07098103201d4443c0c051b0200358401c52018148007860203181808464100002482c82d18805407000420566a0315261208840c1c2d82040344c5035500f04090002528000c0c0106020308503201a0f140c15050107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 739463489 1250 739462239 739462267
    0x120f16050a0f0203070b0a020a09061103040e0603031303030306050307080c280806012913271514030607020c0103150503030c01053c0411031f050c 65
    0x1200c078910400103550840c0d4591842801038858a66002000741d81d40d082051940b4041d4014030300941c0020842d900000c2c03200d00c0750a07801d04401607040998542811301c014484242d00c01030046406110401042d80282e10091440300118060343d00050b1250511342010b0900700c296101e8400c3d940021810442c1e680c58849090301038480c0b1985882c2072180e00358072a40801590f0040e030300c074010b1800010f824025641110031580c2c1060080c1c5421600302049000c80c0a00c94070f000908a01000900c1507a003000300c130b001d910500100c4800006078800c9101e00f520080a0156034540e4203100801c07007004160303142c1c1030a68048000c1c09080c901141c00170343d60011020100e0400d5100c01300e4509129000442e00040c100240a80e5951003100b0901c0e4003901099070414a100092100c40d007075501010740300c0c84c40c0d03600c0d2841c51614841d28103103034103161b0f4040c0003a0707810300050000c285160360401110090f107030400d1460b0f60940079406000100c0d0f8004120100c290320400040d100b00e226 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 739464739 1250 739463489 739463497
    0x41e02030318030703050a080a0210020f03071d030703030e090a020f0d0209040605090c0901091e0905090102121e011505070f260d0b030c061b0a0206120f1605 70
    0x40114606001140d03000040d140c504c00398005001c81c041e44222105100d4a10000d10003449103070211a160303484101e12004031b1148020700426124280049560340344108100c6505490301318850f0025020340000071708200150380100c020410312a0001f1050411b001c4041d441448100110b0501c040c8440c185000c0c0f140c05003001c83c0e99400202202540d40c1c0d03901c040090724003e051419149170030b440c124641c0e4051000540481d0520318001136442c0c0d01030749601001806644616924a8030407850080e0202600f100c1995400b4000c0c20188034038181c09911590742d4107400200e8100116540718200c0b41030700542c001030080007001c0c880703541107000c41d400103900c803516a600c00802d00f88402500864680011540006210360403200850b8000c2c01d226440c0200070041d6074500d004150751880000b5034150041014031524594000d00c1c2c0034414284103d005654803100f07154001510f980c80401100b44107058034080c412070210300002c09030702c1814a100c20640c4011224060300c1800303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 739465989 1250 739464739 739464757
    0xb030112020f0429033a1b0c050f10091e090c09180504051207051f0617070f0b1e0c1b0d02010e04050a021c0204060f0906051e0c15041e020303 63
    0x11030341d41c0c00625507118005845003140707881048141807c1c0c0c1e01c1c3c500c0070305416114031441021091100480d600d00b620f030300c4019458640340e01c5406441c0a00b0441040013034010240c1c82d1220710350001d081000c1d4040c10203443c0140d5107441e0350038101030270b000034580d080c20400e41c179a28000c10030001441c00168015842203444030341e074441c6031038585149820f0740504400084443e0502c042c00801954010806403100b010b0006d403014000c1411070f175075520521036151007609412040000707401c0f800041c200c144020340c9003613001c88000001d01c0180e015002d07507a40756111101c0c1418030542232300703081075081c422522826030507801c0c2c000a04100c0c00c90049880786594202142d4151103603030483c1ca1000c1104c0c007248800d00e00400c2d0320002d401600c200008109004074404041c2d108031200710a807450b07034484e1424001c425140f8070b00f2512580908228420410005556034010081c1d91000e0786500c1710a030044c605440d0417040641920900d50b451502e155203040103a401100780e0307180003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 739467239 1250 739465989 739466083
    0x906032603160e1f031b140d0506040605100e0112050105031e0304080d2705090106050a090f030609140c180a0b0904030c0303060b030112020f042903 66
    0xf01c24000599010900345800d40c030300b40d00780202d980c2d503505a04602c400015141e02989445e00c000070640704000c030340a109060000421580d0320140d2107500954001c40094000280c164482d804184000710508407880404da080d0003a000799070744007084901d089582c01c0248102e500d8040802d940f403410460540c1001401e2a009400004c00c00c15a070007480134038101d039100c045103040549141c0420302030718400c24511201540e0200c0c00707500e0104a039000b4200c60002da10707112044450303800c0000e540e010440c0090000810b4000f490000c405540508000200c0814030310342944074518861600c0e00c82c1d0401d500d80c500d60f98a107469080100003821045403607640b80007130807004003088070100d5804800002884140341d40138061906852003a10100a070545034209425a400f0900c500100304441022850040c01c06100c00e110510020f4804203180c00504080f04804112500503540d1a00b1090074a0030b81c50308003c0e007210458901d91002503840c0070600440140100180c040d40701d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 739468489 1250 739467239 739467257
    0xa080a050702012a05061e0402061c06060e030d0c05190f020a09051806010e060607062a030605010305011410020307050118030906111005060604090603260316 70
    0xb590081c00c00d9500c003100558000d844050351280071a1401480f08155a984103910000390f0402c070b014600e1145407103200301310005a030345508004c1c156100c02d05115032103100d1101c83c105684103002c0c10002c0c10342ea44480240143c0305d0140b514201510014000f0044042c141e14081900481c2c0b20021010070140444414202d01b02074401419040b002904080d68500014004010354046406031061503906000010303c40c0855580725000c0c00354890150b00100442c04602d8040020040f503440f400010030514202c50b0200500403040e98030200c0d04100b001110712142e418402d14000e00001d0034100b00e154140001d5010300a03490801500404601d00c6641196008005880080d07a01030300a211303170011400c4182084011000840210f41302e2140442d8480c041c5020301e00300c4c21800024095081c071869040041c21024100541051042002107081003a6000b240f001d1801140e400707a15000e02d0600301408a43c0291000040718184140440c200c25071180b50203a02c0e46280600342 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 739469739 1250 739468489 739468493
    0xc0c06050d0605060d0617060103052d0a03080105131406040b15040306150e1509070905030708070e0705030408120402190e07030b010e0f09100f08030c0f0a080a0507 73
    0xc00b159048103a21150100c1c511030840e403150042c0c02510ba40d00420840d8005007a29941d81e07503001e000007481c64024070042c0030f481080740864607044520402c4030700071038a801400c0e400c143c000780c01500092007110040c002802c10208401c5901c0010000b00641400a801008c0040d005002c0034421602c4a0201c2c2a5903603d40e203000321182e0b6001303d140d84075580c1c43c003900184000f8000310704031248503000003480034041c81c1c2a40702d0741c002410f0104001b1034004024401400a001c00240050703103901268940301000300402601410000308401e81c02c1109007150740c103005000200304102001007000044c1044180c07010b08841c10003080c01d903111031000903c0e20f101881e5140b00402c051000040d272622809005000b234015880410103605280011529544c080324202e41042c4c10205290450400c5d4803255841640d40781400100d9072280100d1394014042c2d40209220b510120340c8a038070250910560384103003c801d008111b0340889030340b02025401032003000c4040c014045002c0b01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 739470989 1250 739469739 739469741
    0x18040b160f18080303090706030e031303030c060f06081501051002030a080907081b180c0f0904090602160314040f0311010318031e05071e020102030c01060f150c0c06050d 75
    0x4060070a09090305d03200e141c8030b54007075075414017440750b10006814504140610789001c4100d40e072075500c4c0e07038240e000c0d107080d07807801c0e10040c2582800300c0b4040c0c0d036100080300200785072242d01c0261101da030241100c1003007070649501c180c4060f0440e601c20346d1580c110010094000080b80c21084080c01c2c40105a92003036080b40c14140c1903070292180f07000e480300d59100d000f0b440d03000c020440d2045401e4006030b4549003004c008064105c4121840380020002040e181c900e02c0003500911f00000d0010448003950713640e88081e0781181002c15a0740c12256216410141c02280d0000d8600031a02c00500b4540341620140b280601d80c84041c1c03c4c820241c41e001c205134420740044200030030b01c1480c911101c9141c40c0052004207022000701c2600030280500c942030340310380c0c2210011038101c2c0b504040340c450b186100110340054001241540b2040007641c143c44001e0007004010240701101136800c0303280801010038507072000e20b42401c1007160380c010310004c0e00d04409401a90b125181150300c52070700030f080f14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 739472239 1250 739470989 739471037
    0x1306080c070f110111010b010c060e0118150b0607110420130807080703050318040617060402010e12030313080409060b0c0c060c03040605070f0218040b160f 69
    0x181c000150b064803031050204220114a8000081e81c6842d0f0700304000c00c01d5801c0303a10f222000c1d0b00040070005010f003c104243c001203245001030b000080c851643c80c00300301c01c4005c10b00003101c8498100618892030f09491040001018003940c07010700d0942c1969039440001c51100c101803107075940c0c000080c1c0c008540040041c11011407144266250181a43c000c40e51405100d148441c0c031555601254024001c24003004880e400310045040201d1b1288071915181024aaa50031a80c3c0f010700140182d000112017502c8002e500c040c4c43c0c58100350000403c5800f400c40d2050003041075401042d0140800022a5401300484c002d083c41c0f03814510701214144110381c00301e0002070501d0800310700c0d102003800030082040c6440442d490a070000e824010f203030085103105444d03078009100400686004800410031948140b6100402988940c000351500480e1b00d4003c0c0041d000d4005c0000300003c0869003a00300707000e1400c41000c0d80a1038002429900a01c04034400c1008140d074a07207104003100106 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 739473489 1250 739472239 739472243
    0x503070305041703011206052203030e10020a11010501060c020924061309060e07080415020405031e0d090819031205130b100b0901050c10140601090b1306080c07 71
    0x1551340c0e50303451000d840c904840e020140d48480c0340501048903002007076443c515403050f04c2d01308180e00d6100e0300c00f640203199240e00c1d01c1142c000c1140210a000c0c40707200504011031131b91194120040c0c0b0810880c21504141c1100050090b14090704000d40d40c0c50011991100c05c080d0400300e00c2101c82501880110015041c0e600440046206540f542808440400b6182c8110042046690740c001401c00c0034015a4840d0200300c140011801103884005010300c0364250403030142ca429a60300c04a440c1402903040007003420160207007840504c40c24010301c1140c0146d403905418540c2011004d41d100c258244981c0002000e4003101d1042601503110b0091200810104210a1500072246a0001502d0204440b0110708800051440d000b41c1007000c1518048200b050801482c1001950150310140f103840c1140f02c0c48159070409840e50250042103c0342d0b4129183e613007084c100250070f0780b400c1d4002e501c00c07103c01e100c240180b12959500d002244c00c1403400030543d40302c0070802c8085200e080c0700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 739474739 1250 739473489 739473533
    0xf06070e060703020102360d080304060e070803160c0b0a090b0a09030b180d080f0a0c111b091b09090403030902030a080c1005070215042409060c020d050307030504 72
    0x403008a641f03480400d00c495600000c085101600007401c008501035000c0008140351003d0021801140c900e6001c51010610102281d00b62a2201c05051031a008084400c1d10500d448107000100414140d1001c005c1c03903040d100500b4181c0190002e441d00a0038011549000c00106540a807540700b500700d03a005540010740381a0300d0401040c0d00300078441c401c10404035071080c8548440614481d8200511823070080b0f04450043d2903020748040500a100101c00411103002c60b0000c101d401801644050214106400c404103410000c0c040e081c00f004010010b0322021200c5104034243d48c0b000c403100041c0448031410241d44500d0183d00505071aa00079404d403192422a0082022280047c210980460100d40e2034078031405540e415940100e400c6801030700f00c4032071402001c00c0003c815070007910400201401103034078018803402c0c2c01c00310342c001da00c01d881c1c4409405024031485180326407115480613060044803814098010310000c1e10720001c0690701c500140a01600e01d0006c0460100070b86 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 739475989 1250 739474739 739474777
    0x13020d110409050a0c060207050d060c050415030b1e060a03021e0a020f010f05061309060f150e011d1603060f09051f050a0515040e10080f06070e060703020102 70
    0x42550782c130403211004942112100d000826200d00024440c411544000c042c02043c40450f13407002c0c041c01c1200c441d641806802d11000c110220702d240108503607841c50347e0000c3c80f1038a0b00200034040035a19600182540302c020b408801d92580b00441d041c0749440d003400f6944401e01c40502c042c541110401c0001c040d40440c00d008020740c04510940000300c804001e2090400d0358540208861081e6809548815105e803003111014181d0001c82c01d550050307400040d094040300c4450305070b0788144c0300c000384d0342581041403110800e2486c5450140000752104040502401d03441e040701e22020b040c0c4001010110071141c140fa1194001300064920784004100e10340e034812070b22001c5c05051b01c0d030b08000040c4010002030740c40011105002c4070001009240c00d6483c0c0341c20700800c6440144001c481d140100b102041184802d0481806131100f90402d16000c1d00d000c0f00725040400b1044250303596007012042c0302800da40140c0b040c1e0411412940c1c542e44003d686012ba0092291280d41640100d41c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 739477239 1250 739475989 739475993
    0x70513050103030207060201050709090c0c0f0803060406091b0e27010e09031c0f09021c06050f13030e01110f0d02100e101805072c13020d110409 64
    0xa08001d0489100c0d40032113100742d4940c40e0a9081c2c0e101143c000c00001c415213401c1100001039080000c7c91101400c041002e41144c3d11904039150010030140e6801d24000148811400c05124080003850100c00c104500c0d104e401c04054209540d442040400c1040d01111500c0e039509118102088011140199100685801502008024030895401c40b03a503034001032801c0c0e004401c0707480400303100b0010040e0b01c11a40c94400142060701c065995181d4815414005031a043d420800580d904100a010704000d450908180d07040140345081c2200c1000610106841c080034515140d60b060400c91040203c0b000101c460001c141810340c4640b003941d0f50889207020220b00d494511340746070b0aa41c94546000e184c542525414030854000390702000e12004001d66980c005040c1c00c00742900310b0043d040310740307555181c00f9058000715504280f88600704401c0e20248101a6540315070500c0581600c0c00044444603a0701120010f0300522074182190304110f180c0440003140c01e00103200b040024054 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 739478489 1250 739477239 739477241
    0x40308130b030907050f0604080d180b0a2304080303040b04030201020d060e060109060201050c040b090a0911130f050a0e04051c12060e09060417040902040b0c0c040506060a03020705070513 83
    0x11748038850082c10300c4000741151341815400c54040e81c0ca00001805500d801c14012503d000d02103519146541e80102c003c1400da2150340140b585207030303035135440e4002245920488001e01e0508070701c1442e0701c1c08010400c030b00c000110a5980c80f503000401c0d404165218103050b4060710409182012191501d0004204900c240004a00409080c1c1e9010740d110388401e0143d080742e40079541031076184000d2004001c05c69452008112014020b000980302e1661141c1441c00e0350503043d2150b04151001c6800d0f1070452460000070001c0010840b0301c03c0e83e03860301000c00d03d030003158000d00c40d05403440c1d400202401020003d58005032409900d08091f00720003040145028a8140f0707050032142031582c0000c4805440034040d0203400b0306005083c550b162075850205c0d0802c40400c1d2001c0c44024040024001070500c0540000c184c02603c1c1079844003000030241c200340040e5001481246804140301d0700e81c5581701a50b030300115600300166184200e0034801d01d4a11280c0c8066440001904903200f20049 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 739479739 1250 739478489 739478503
    0x16090203090c030a020604230a0e071b080d020918010303050c0c120607080709271b0207030204020306131e15060203070206030a0f0e1e030906040308130b0309 70
    0x404800c1e030390120310030b1041544808407181301079440101071109000102c0441540d540810a41920481034044d800110b100b4002660124900d541036100f000010382d0070081450b417060715401c0c210600c070307003d54560140740103002010300040e40c046600351503600c4200c2200800d00340200c0014866030f5a1038004c0c9654082810082e00340203240c00c203001c505100001031078118401000e0310762f5584a0104444500004103000c04121b80300348000340f441d4079007064495041000c4410350260111611520565030035104000001c11701118810580341e0105451080d00c0d4100c0300943e498540800041500861400d010714580c40d000b00070047c0c104050082c00e40c90b505007824080c1e089081201210f5020610a14001d604100043c00041c60080002c4da8402c1e08800005031164000e8074100840c0c0000503400d111b54055081303180b0780c03144030038040d000d4502c85005500d0060210082415030003180f00040c0000004650680040e0135a0140e401401d4444462a128608400907550ba690 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 739480989 1250 739479739 739479751
    0x123030102130602251502011107050d0801050d0503090f0102010635070f0e0a1805250f06050c030c1207060f061d0702160f0303030e0106030314070516090203 70
    0x202d4a0000305c140300d078225680b0510382d42d40720000d46075490b1000e0b650100581c4003a078030455603105580c10106500074042c006140c041d00080051031007020b0054400d44068120310b101e00311400103200010000801c4030124403066401c4103243e040c0304010f034050510b541100d80c2403041d03841e140d059040004030003540b000030200b42a0450080f0390026440d41010300400c410310407058030a01c80300b4000a2080c1e0801ca20603030009140080e1601c010010420040c111042d80202101c82c428040c2241202c20034034255151070310243c0340a4020129011600c07035001406008102c1d41022982030083d00e01d10001d00080d18164554a03c1c0e03842603034040312003103800d40e1414039038080c02c07052485100e05a4408a5620001c541c10320b0444000820050a032000c42c800d081e4215142d1314003000e060b008020306910138a10506501d0041c0030303a458803001e808180c0c13411404002180c0d04c06242040c202d1110359503540c81d84241130050901741295814014168050b0380080d10640035401144030350 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 739482239 1250 739480989 739480993
    0x50f042009070f030617030702150d140403030b120616140f030106110106050306131b091e0509061f1e03210c151d010626060123030102130602 63
    0x1076141c068030030f11b0003c015024181c1c2c0d0b00501555005080c1307515070728142e40355400a5803c1560841290b0261118840c816000380f04980c240300808d90580140c424908044402d810b52912441940d0355500c4000d1100c241d426440c40b801c000c881c0101380303c54100d921a50314031f07966800224031040c07a40c4288a65000101d10300c00b03846e402c80040c441c02e404e8880050241003681c864141c441d102340c030031042c2640c644500d20044150801c02c3c00f55030000f0011004c01007a0f010440c140f5440314038201c1d1401017120b003454100b045170500410104d070702400c4e04600026104090b00100b41d07403001034000e1144d0b0311030040031005040c0d82c000f01d04112845003100c4440d55a50185a41d00d04848a91100104082160364000110141d00e100401c03020717114001442002d20340c180341c40c1c3c0c0c844403080b05503035598502808800d02d04000650002014241e00c08229440c06540359134440510880e07507980d00314040f050104204079100c0d0888100107000f5503d030148030110302440000b6124410140c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 739483489 1250 739482239 739482251
    0x90e060d060f480e09100e04030206070e120a0209040503070c03030c060f0209030a02040b0301111611010e091f0e011d160c0f0f02060304050718050f042009070f03 72
    0x2d00102c0f8941c81d890041e911080a6003040c8107002007444050300041c403440d40380c140400c10402c1d0405280c4558000d500410781c6080400015011042d9040b1450158984020300c00042c9400101c603060190305a4400c60190b84030304140b0b00354000c5903401000c0c0304c8541000030a041c2d001d01d41d202c559000f0101003225103070541d00c1e50201c0c4201c0d45240e0301504003200000140c0780c640c2c000c0c0e00003c801b0300007196040141407a14045d078040075182146900d4614030304203000401807102641c6034203080c9062150045400a0940f080060000762441c441c0d85120001d0314510300f0b050010720800702c10340c0390755845002500e40c25483c00115402e440305000011544159481002c078000340d55111030f200ca000a4907802241c40001006456018000303080d0760060321450001c40c85540a60080d10342c0d1420130840c0700c0d0114030354501201d06030600007800300d140000003515805c0350b80000d0041c5802c40601e21007904c020724400444e4004030603010800015000703901d44008010550b020014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 739484739 1250 739483489 739483601
    0x609080a020d02010b102601080f0c0301060e1b0909070c0b0a1a15120c07030f021f09050c040507201f180f1101090e060d060f 56
    0x700c68500a07046d40c410348289424080d180034002c0c2015001d440d5800e0503400c1e1807030303c1000e120340003a0300003400d0398000f0030406c00003c4103110030800000304900178801e6510f0081603451440001c1c05007002d1250040d0183c8071030400104035062a0400303400e03031a00f03141c00d482c00340000142880035254620701100143d0400e41900c20221603030741400d180d0925007604814031035000c42c011000100900704000b444a050344180c0d0244c070401401c045a5503814080c6001003d1790001910700081d54014080c01c00190003082c1c6810001d414250b0020f00c0d41d141d0f041c514a84a00352215a400c140b402c014802d04030350004c03403007030b071002c901c0240501d500c82c21801070703982c400d11170200100510880c4902001c02103500300c94150520035a152a4504441d15018454507089804841280b801c038010442540c0080c4010001e0182c0404003c0324030b8a9804503011014410005084980d141c001c4c4200040e6a4441101100b40c08000002209840c0c1c0c812204020285204c807950164110440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 739485989 1250 739484739 739484741
    0x50f041a06010c0f0b09070605180d02040204030204140103020a44030c03040e060d210221090a090e0a0f020d02041b09060f0c020f0d0609080a020d0201 67
    0x402140d00030940e0860203100951a12180c0000d0030031410043c400d40700c031004c1194403100700300c03260081c0c06010701418600f1007185450111347c4070406015080c40140e0092546500f10040e000b019501c250080b03000344002070082c03045400007540646060380b00018400030340c00040c1a079100b03407002908151170303516007002085828024580c5610000c0030b01170b4101c00b06944002d0b03005000c420201c42426428040c00d54000707004071035150348081820003091011103c85500408140c40104848896480311f1180c0184411034071542d1207004441c0100ca4801c0180b082c2c240c1450ba0000c080c003c52110342c0c0da45a205600140c0f2841d525000400c08400c01d00c2210a0009000c004042e0311070b09603107101040d41c00800580c1d002ca101c030784d03107000750b00d0354080c0b88103d0dc1180e45501c070281d000c90001d0441c00e06500101d0810481303851110040d50801000c900154046406103c2c200443d000109811001c0800404040c10120407034108510302000d490b10750316075002d90b0b02021107038a00300c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 739487239 1250 739485989 739485991
    0x80318100216170f07031106071e0f020f070909150b06090d11040504060e0d0c03141309020408010902032401060e03012306030d051e09031504030f03050f 68
    0x44120020a00b00341c0011840c01e5102c100032000050749050110408813200141c100d02d00075004145026800c80c0c5401003401403541c00f540c0d0b420204903030040103200e9110514101054014030030103500034143c4500810503660842401c501f01c0e072a00e61240c40328400303403c041c40116102d0707040004c0303034980241c0c134040d60400702d0000d4081070800e8084010040d403042221020f68094140c80910b1089403114010180b040d405403101040043c42d01c541d1500d42504d0303c8840007003041d500054000654840d40d60454003d0102c1d582c0e441d10440744e034240080105038411040c0600c00500001d0490040d042881e066000f18190741414155150549207000b80b09810b0001c003030350a0060014500555000d08184409800007d44036410900c0010f050f0010584400c800345031000c000042c94100582c10550401d49071050425003001c04c3d40e885d180c03403211441003c071400b08880d030190300c00308403103076003130003444400c2140d4107180c200a04a08154481a4002070806001030340031111140c1c61 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 739488489 1250 739487239 739487257
    0x2b0c020c09040f02010c0b070e100816050d060e130309080303010f0303030f02070b150a06020c130509032208062d07090b0d1d06010302100c020402070803181002 71
    0x1402540d910780e43ca4000c80d00501040b41881882c0300020040394402c4000c0f44218182c0d1108447c0320f440c00d04100012038460103140800118104022070723a200944802881c01f000e050041e110b074088003d0001808040d00507105c4105028100215846002c2080c41741030300039100d1455468032000c0031501c9200074010700304129603203241040000e10940c08514050305205c001800c282c46c2c1e5681c003030400c0082c0da40a4241c1200300b900c0c2c520b4641225a080141050300045c4482c1c402c01c80818450b4101c9a20310003065981c0300022100d81080c03040b654000d03000c41c201e10354401400e083d044e15080c1c9002e4089540314580c00a2000d40c4c030104545010f04541e61440404600280480d504000c01800c0b24200000103030000748410720207001c2d04a240c10000c02248414100044100311640d40e070040ba8164400c03001000503031504c0d114078401c40701030302d44440e98a4150006c507001c3c2c804c40b40001d0456400008201c103a030600403c65454800b07403402e48011031001c04142007070307001d26540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 739489739 1250 739488489 739488499
    0x3090f0f01020712050c0a14030d052a0c03011d160b03150a0b040f06030f140c0d02070209070f080a110a0c030306050607050105040311160b0f2b0c020c 67
    0x2480400b5413842a07181d00e80c482c104441d4410060307800320788040700550211a40c20010641022245000d21080c1010a060314102d428104a0090240e51030b410101b1040c40c06e00030030086070585028460031301e51050240007030040c3d412440d41c80307081d0390152440480d070b401580c0542c41c0b82c1d9006448031007180c1c03084001a0858545500404500210600e129440100b001001030302c1030070480600003e103180c58040e110640350410103025104a0140c52a03918a0700c000c0d024641c1540c0342194211450102154072400e180440b18000e108500e00a54010f0f040020810956030044a0103410f0210b40c0d41c6031580c2d1104503085041d9801c0c40d0a01740805014400442c1c400c0c450003c1201c070a0003894081001990381c1c1c04111241d1004030151210303511a0100024150007000359a1009006402412001d254856040240106001c1c504001e50300003881c08050328460207480303207903900f4041081160410100001030047d00400d211200c2c0c20038401e16001750012460300003160000d41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 739490989 1250 739489739 739489753
    0x6090509010e160503060d0b0a060614040f0b03040507030c08071401180314150a0e010c050f070605060d150b010e0409020a05060306030f060112050c2d04020c01090503090f0f0102 79
    0x10b02a134054000500150700b00c402c0c582c0040100c0d0b25a007405009a001d250006034190400c500204030084d940c210f004180300c00c0000b04001c00d14003924200701d03043d05410302c3d129107c9141c15801c5c14045e0340050030704d000e80c920208a503080400c580342220800c0d0b113484a4813613058019650101d80400c1412000201001000441c082844111006c080c40050f99100d1258149040202c201540c141d845103a9480c03c860b1400e02c04d100e00b41d100301c83c90034828108260081440e40500c200b400c000c00440c0c4800203d8103d48410380c20103091a4850150303459800c600e5000001000241c4c401400100841c3c10b81c40c80d82400d10814905540207041e10050301d0030711f0b003407041c160300151a20750907220701000302c00000410321a4a010341007403d40750720403031307901d00f030003072808600c0040c0d140710700c51740d18946a8000020f00741400304600044084d80400d10100007600038020031032007580755428020f4040810401200074100e6680480c0caa100e1707807580e08103000ca613a803444d16050141e03100310 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 739492239 1250 739490989 739491031
    0x40609050f061b120d1401062d0e121506120c010305130f0f170f0406030515060307180909050a0312061a090330070602040f06090509010e 61
    0x9034030f00030140f005021038207180b41019200b2100d030b01c950403980b00381e076885480d40c00004100e03520740e0040c10b443ca4281c1e085514001c0841c0f140500f444021070041c100c509d1003100902558202c102c2410040c100d140000410301040e4603188407002c0e4014070100c20001070210315090105002d0640003100500d1780b001c403c40150018880502483c4194801c8030010000865180304154800c4c0318030030700c02440c1003030b19242c400c00b400c4d40110381c5808003d10040c144854090162021141585004116511160314100305e4010030b00c01c154004400008004038541c100c819005080c1c0090310310b51103603039030b0904030040b200800c0000f41342d40c001c4103401001c03074800c183c040d03100300d22820002406a51004116444c0700c02c0700d140d00c8901800301c0c003282c070743c81c09000101c0401d440c40402d5008884c072500c1e60030105c810b0354541c6000d000114a01040c0180f503410758010700b400805403858551140406410807019204180c07048580c00008507802520101d1035004442c8051400c09100e000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 739493489 1250 739492239 739492267
    0xc03050f0c0718380d020f03060f091009050303040305031b18180f041e0c0905040204290402070f05060403080402040510060c020d0501020915040609050f06 69
    0x11002084035072040000109060303c0b254000c0208600c12200029420341100920594080d0b96106006410489060074030342c4160401c5048402c00c111034120a0340c50038400a9415a900a0720b140c261040348100309510468842c494000c002c524110b035100c00481d1084002d1b641d00703181c024007a40092022800080c041c201640d0400801c150701c00d420f07030301001c01c0d88094100c540741403160720b58040c1556090505104404c484600c94a00c14041e2a281480907080500038100a0003170100403030291a610781030800c0742c3c0c05a4480c406069160361040c021000d803106a8040c3d1040d440d040b103500c09200c1c0e11030000170030352501e0450700e010058102040300941000c01c1c1520014010401640042e0051120902c203611a4a44250074200340c010300080700d50007004040c207610909824000e2640004214095590445800400100914186019018407501a50081d0003c078104040440010203803090350071690710071020350f83d240b0810440d091901c0310790b41c02410800c60486032040f0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 739494739 1250 739493489 739493497
    0x140c0f0d1a0d05030706050609040b07080601051908010503121e0309010617010504060b04020a050d0b0303040909050303070f141605070b0d020d0e0c03062e0306050106020c010c03050f 81
    0x8200e01c0c81240d2180400440c0d0038141914040311141c200060b914100801841400e800c21016242d181d82854030396160204820301400078428045a5400203e06a100d030b000c5440907810345910001d540080c400c080d042803420f005082c428051300180710548008202502c800030504010035400c845a01030100143d8406420076429540b80d1354042150342c0200e02512207181b1410002840e49014204942210f4511034201d200c0c1d4010002081400d9000d4103031401d8007800f040000c0c0d07c0d084800041d01e10701c599407140800e6402d01e1400e0702848004005984240150344800855550304031013110080380400a012031200140702c00030325101c0000380c0710129803060040b00c00e030070b4481d100ba8440d0340180b080342c8002130300000c0416148245001d036072503400ca0200104804842c600c00281c40f014010054003541348d031544000400c02c005030b00c004980380c01c080c003188599141d0a10102030842401820090300c9030802c08484c40d40b0500352001d006401d40e98a6042401981c1802c90540c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 739495989 1250 739494739 739494761
    0x201021009231912080a0b090c0a03060503070b0c1501211a0c0a0306060305090c06070219090b040e0f0703081305120703381009020706140c0f0d 64
    0x86100000401080d80c94400f0321040d0003401200d4400741c0b00385000b13040d0070001341507812050034100401001e880d038070510394114500c0c0400c40c4d111480f481d4120018201e81c2c3c012a41485100030000d121100e00004288001c40001940d42040801e140c440c00701e9000c2c0701e510007202c02581a907440742c02020350440303c1e601c0788900704103020900311041c0c50818140c1c1c440455000014010b480c0c507400d80308500041c42a41000d00c16460110012a1110750401640c1d0250000041c108c0c1195034464001c0451380030380701c2e03030035500351224095001482a4900d00c2d02451506510b10542d200014034102841d0303030400104405030031a514065550810310f22940c0382001000089002d40c3c0f41103080d208010100001d01d4940d103582003403c1c0720356a101c04840c1240303148411000a05103280b8072042d000006100075050f03160800b03408c403840b102d0b42c040340c0340c0380c408a4502c04001007500040100c80d6400c44010660302e43c0040030b5041c0c4100d0110003e4560104032401100e0a030b1780180c00005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 739497239 1250 739495989 739495993
    0x2120601031d0705061e0c07061b050705060f0412030c2003030304060e24060a3002010c200a0645030308010f1208090103240b07020102100923 63
    0xd10f030741c5540c030425040011f84d0032594112140c00c1c02010307840f080003c0d4031300c1c902d41d0a0b004481a03444154485070140100e600490b40002c80200056200084500903c1391600d000c0c07a4042c641401030028942c11130440341007032210204200390701100d5955400c070900401440c6540c9950340d0b103200030021966521010300500d03a03000c0c013450810000c2c3c03001c014041807030405460032400304140e444030f0b41c116440c49083c42400e01c0c500112310103100d2458042e00741c07603510710b030803800107848026203010002d02c2d42c07400d070681888202e0700a4918004d0741c0181c80d450712042d03c0d000144c60000b0500224003c00d882029500103151070004042009401100b500303200c0004415001c1480d00c3c1500b09502048080004001d50a81c0741c604c10010400c0ca1039540c06511903982d030b03c9051040c07095413410035454480d07010680e610b03c45a10300310058600318203111a995042d8003d1703500980c1c0141c0c05805200d1822082c810b1070300400002075407084400d2001e0b03000708401c00b64407041c0c0141c0c84840c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 739498489 1250 739497239 739497277
    0x9040204060306050109061707120305030a1407110d080615160b01080f0f1612062408070902120a0207031106040b1602150c0c1002120601031d070506 66
    0xf0511900c10203019004142c40411045c3c02c100e0105408501075081003000d90007583c0400c0700d050302c61039141402e580f41c5062680c03038035401600809000400c0e403400d6991104010b1250007900591000c134517400807001c0e140120282c070002da82d525801c40310240c214a01c84040180015408000e040038007076a81801d809052a45940040d014241c21881c0f00d0341c001411070750300710001c1003841b14001c8424000c1502e218000305095040d080762090032070050b1680011000c1000c107401031040d040c41240c000381070f48503140707044c80c218070140700300441c0b802040d10110348130038140200d4400013140c41801c00140c44031817003c0300945c0b000d14150104000113410b100e18440074402140102d00981c2c0e0b01d40c01e81018500a0000848120b001c0c3c1035500ca10840c0b00040030241800e41d020030412030058440d550450100d05050032003003015852403001a1070b5040100040c11513010b07040a0f030701040f010b2030602c401c400405500480f03070902d60000d14108a0303464424020842e15004448424403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 739499739 1250 739498489 739498493
    0x625090e090309091003080706020307050c240a0605030a080d061a03090705010302041202090403090812030a0609090f080306040f0912020f0303060607030c02030c03070617091506090402040603 85
    0x16010301560001400c0e080040c0105251900c4500c654100c8400302c03c5410803842d41d070b140c5a0350310941074001c000310f4010000a200724002e10580300c82902c03c0054946041d610004551040220004117200700d1013180407569a2034640302e05d41c25504080c00400800009071518080307500300a19a08582c0e0f2600804901c6c0c0c42480c0640184600d041e00b5036031203040094100b8144852500110304040c0306002c10011a203055810301015501034a6092554490341400c664241799900406024440d01e4160201c07c034120000350700c0b503d52038004003c103545540c414000d0307502c1100003408081d0300e0007030078010130701400c015900903100820000303207588031140c043c0503918056000c1d199485010381c50321030300d0707010300036407164071b1038200070b0b40c59403900d00b000465074000c200014041020070b108a20440d181000b21644c01c000007011110442e64456005200412803042045000e0b02070000c03070010003000031000b0508884c203281c90100da583c0814496400c03030080041e41e000d0348136000040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 739500989 1250 739499739 739499759
    0x90a1a0417070303110a0b042307140a05101e1119060c09050603010b0a030915020a170105030a08030a090221010b09010509042405150111062509 64
    0x307550080000034000c0c00d441c500b405480500d5200ca0088039402c4242d00c08005900c5220540c2d01030f5101480181300c202e80e4440c3c42050b0500c01c2160a00e11401e4401305280626407500e41d0045012514850f519813900144001000e03050550b10204010140349011150b084c141c144c080b00c0c00349000640e00d80c0000089141c00b61007103200380d85003003808103003080c08040d0003100030520a60074100c0701d080c50a00030482600c414461010501d0000c241c4401c003c1c4070390840a0a283c02000e1415840510300c0c5d150000d5010301103410105041d00249855000300c0e4030894100c500c004e002e00240d1003e83c4441509a01c001c00c10094a0b50f1550383e0401641ca00300c90300304003050500303620100a4440340c05400c441c40c0d4901c10348988404d1004001940d502c1c080294090341c09803082c2c48180481c916010850200002c4184003030501003002018116504013480740b2800340d0320380c650011604c00b01030300c0d9030056a00d401e82c070080c80708106004d2010503019440c4074481c070380000c415a803681d4042c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 739502239 1250 739500989 739501019
    0x3060203090a05152e03120c0605241e09060a080d1106130f1202010b0d060c03050615030a0b15040303020102030604110c060420040e01090506070203090a1a04 70
    0x303462140f049082c045c10000125085e00c254403444050080b034000c84003008990314951000420701401e00840c24059445a4610318103c0e901100511250408028046a246e4108040300003807813840c0d418a154684481302000c10100301030a912116103400c10310180007001000356421808030240010380a90402c02031110402c0e6568448804a0240f0300609000c0302a040303941140c0f0414005010440400c406c0c1d10b03c552109018200c0a02c0e010103034050991400d02c254844c10211044061008907042180c0002041d0b42c1006695140d0041041070711074200e001100440c140001000241d4070b41c802202034000a01303040100c0342002c2460203035880341e041200180d401206020032820f01c0d0190982c281114003105007840e484004503561180d00400203050148407400840e03480e81900040d912901c000340040c003440c101d2140060203498100e03800c841c0c6125440000c3c0d80944040103480b0310300c10003001c61040c0c2e0310300620480c15210b040078516a80008210000d8a1102d1000f26 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 739503489 1250 739502239 739502263
    0x303150a050a0b09061e07061b050d020c1e0d1701030b0408070203070b03090c0910082508010c0f0206070804020604090908090612070f02070f17010b0409060b040b06040f03060203090a05 82
    0x399611f803034a142c6042590445440c078040c01c44000440d40000c2d801c00140d4840c200c250b807005890b41100c1c400796190101c41d420b424600094100340d0a090000464014801c0c0c006444003800d0f444021145010744400b4800030b0000c1d0a00b8011030001403c444c01407040b140010215096a600c2c0c0d0300340c0000d44d000f604c0039406640702c040900480c3c2407510311254060309114541022520380907203151100100d4001851045600700b02010b6141c1d2030100c41d0162441900800c50103a40c3d01024000c0300e15000514050b1090b000001e01680c40780d61314502c12640941002d041c50325101c24100a04034981040b02c115100b4411400603884076400340011492b41010441107040041c8060110b000b01180c60085402c03002c4180070200f102811001200c440d03e1807543e420030400e0f1003e0041c03c8002c0451f41c41403c180004c0c080c0840f03508548030000b0100d908010000740e502c10440c2d140714074858003102c039030a204100042000c0d540074640c081c000109441d550009503a4950501314500c882c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 739504739 1250 739503489 739503547
    0x4080a0201050f2218020c10091b09020d050a0207030f051608030405030909070c030e09040c0905041505012115140405062d040f03110f0303150a050a0b0906 69
    0x20882c0d4105031019003005c1d80480000c519108640082d603071299603052840945544a0904004102c1441e0342e0200424000320062040c948400310a0b019500c641014004a42440085005128240300300c54003683d264491130720005507003200349c9081e045004050303c01c1d1101d8600b200410102c030021445640300e4405103aa900d8040208040303440094940010040e040c00c00301d0010303030001c5500c141420121401012540c41d4942054400b180e90001e0f06164100000c4c0f03c204000b1418800b80c0c103100040c14403031680c81c0e0390111814000c1004408440380b12420f003038081141c12650402000004c000401c03640142103100c0e10f80a01510102e40e0b9074400c1d010041005a01da00c050014170301c41d0841071140c850008010001c81002d400980b04811810402c008c0600414040707400480e6070050700c20b00c21803007414079100e8200300c0d040d0b00f90142e202c044030120b10b021942402a42c000501e10b4040d40e041c0b102d40b0301207400504480360040c8081124141a030960354031220303030141c00c0745 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 739505989 1250 739504739 739504807
    0x70c0318170d030b06030a0b0607150b01090608060d17090a122006070308071e020a020a080a032f01060b0702121c0c0606050406060c05060c04080a0201050f 69
    0x46402d1034a800e0401080030075103860b4140c86259540f1048903000100c0d17000101d402c40b0310000103409841010300c01050a0009211480d10840f03542019400b084241ca600c5061035981c00c05544144049680c1a400001488000c00103405504a11070b0217151000d10703814010700d540445e494480740c4e0070040e000031500140d60200103c880611401c00003145d600303044015040c011403080d0041d000000c040c03065450000d4141d520a0141e031446600d03e440c64200e00b80010f801a4a455090905902450704000c021803028000560610915030666601c02c4194040700101d410303548056000c00c0300148040803100c1e031f088c24040d84001e481103103c0195504502c1c0304000d4185510b1070a0010f54100c1381d03510021400710b0804800700c80c0c030fa040c60514082d8a151400003001d12790030907640f25240603404680c0d10751000f1010b10740351190044810548030310180d803145004500c50b1182076841030040600551154025004050020705401e04043d4400d48032202d02c410388441c200b400320651 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 739507239 1250 739505989 739506029
    0x8180a020612090d0c110607080d110c0d050f09041104030803190b010c0506040201050d0608030304080d0c050c0c0118031202061504020f0403061805030c0a030206100e070c0318 78
    0x400144c402a8890408500a1a595640e500183c014500e11482500c0100e800c80c14480198103c840390700000c1010804c140c20008050a107030030007330200b0104e2065100c000081401081140c0601c04140c0c1c00030304011a52082002802d682c01d00010000424000000001c05140255020345030b600b0040c0c40900c0000154000c581401c81c0c107904100c80003495030302045004c2031a6410036020710340541c0c1e40688204050280007a944002c40740e20000007044140050f2101a0100304036a94082c0589511680304480c240180340d4100f20a4004c90b09541080d03004001d08206808032100e990000c90390f903190310180c200c1a16441c009a0460b90400c01d00070300407950400341e040101c40450030a540c01500050724000c6000060005660f080c00301d6040107111502c00f481e950200c1125540c000b041d0600352074402000b0214054441d1601040300c00488aa925050305d451a06440c01c9940d210002c0740d05108842c8181d0a20540342d1400841c0d00e0844140710160100140c00c1410340862 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 739508489 1250 739507239 739507243
    0x1802090906060406050d0b060c1b0f190902090d06060303020109050606040c0e120f01020a021b03010c17070c0512090a0e0903030601110f07060e090907050108180a02061209 76
    0x40405220b41e004001c00c2c0050341d0010141c5000c0d280c1050001280101000030448900ca0f90204d0100c0c4d2207445000701d02600c1100654070704420030381d40001540180e9052207480000ca021450b600d030a0084280035070712555001d003000b950300a02104101e41240c4480c0d0858515400a40050b5100c9030004140a0200401e40e048002950b0400070f080c2242d40007007009c042212034510803480802c0a11451408008050f41c1558050003156500884000651b640c000402d50101c81080c0c5001007046203418820b40d40c04003a0358851910008204190b51402400105100203104807142a040030840400c5800015104079054030b0340c6424242c104049848103038400c0c18810304000c10000701c000040140c9800500030308050b003820841080a900346803044103540d40703070701c00c1c81c80000341a0ba00c207a4500d945102680c040606440b01e0003000c2c1c42d0f80307076400b1f80341c04034000780040307039000b5106000e90f5540f4070b942d0140c0341702c10700c07035070005040b9484002c9100a1030501801c1c89801001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 739509739 1250 739508489 739508491
    0x72c04050603150612100510050321040b03070c0b010303020601050f0402070f110a0b030f04060e0f0705090c0903151609060c080d0f180506011203080c0a0201020418020909 76
    0x8124010f001e2001407608880482d04020440c6002c2c28403a440a42c2c010400c00c40742200c10000fa5041c4024640214850210a071510400384248200c080305980f650801424905204858041a10f030074100f07080b1003465803010307001c3c1301001119000d440100e03441008840c0a0351207a400b8102c10b500d44020090540d03403003040a44035901c100292000540115603e5682c40c0e0320111040440a80c8000a10b6015083c2c1c80b070010800e00000300034610109085080c850341c421030040108074407690f01d840d6103016100c140505540004001d210900d8040c40301079201c003000035110b00e002007803000b007401c0c50203c20100610110b01003e01c9801d040240b190018954070785449041603103444c1000303020501c1030401500d5004002030020040079603030400070311496100c10074041042002d5000d142d9030010502a0f849000f1100003040c8080c8948200f00402d030140e4441d0941d4503240001051940545d805005542d800c020001c0d034101c008201c0c40020303441900041c2ca915241c0248000820 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 739510989 1250 739509739 739509751
    0x1020c06240a05100c0f11100305011d04020a18060317120112470603120d0905120d0b09010303051903060305071512150e072c0405 58
    0xd44080020407070749403490a5411a1800c440c0064003609940e0181c840074500803001d090aa54a5075200a1241400d021002d4000a0700c401c4000d0b10403c804404030350003802201001e100c04460741d12101e41401080e60054002880002591b50f070b030b00d42d09807880551a28045060301c5000420900c401803810f450f2110340b040b001883e001d1490f600041e003150500500102c0d10480c03001d0014888583e100754009d00f54804403445806040741c1028080d000b0407c020340d15199400c03115030440b00b02412078041d5034090000d06101d044102c010802d500103018007550b199a45d6001c0010800c10072080c010040760500c596a943d8080007c0d80680380e18000075400f030401a001000040e034800c08894a601c0280051a07211181c40740c00c601519540d40041c00758401d1b910702140120b401c540160041d086500e03005403980e042d10050040c4c4000c02c402080900c10860f041041d02e10100803a5440751142c6001c07440c00e0741d90310070806a04030342d440402c030000f41111034400704c2c1810b00c100e41d0484 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 739512239 1250 739510989 739511041
    0x30b010816050a200d0507060506030109030f0c1506090603031803080331380103020105030712020f07030801090504150b0109180e0c09011508100801020c06 69
    0x414240c002402910400030840200100340b010318440134103541c5080c0226808800f500c0c0e0014411500400c283c01588081d90802c2c40d00001c24402d28052040e5401c0640c9a1641d1810b007052003015206078008032000e54a081c100d90403429030008034403404000e8506804001125402c1d820002c0411001103141444001e50f18018008100c081050360303440b03c01c84144115100c11581010441c0d4441400c0ea400c94007000301c4001001035040004400c0d00b444504104064041c1e501a4810102c4842c2d04141c28203400c010700140d4422001035902c681181055800c24062421074405ca91000c902440e0001c0045084000c041d07010b400ca900400a401060041e81802c0d1140c07514038006a428040c2c06030b0b640d002d0b2200e0b0340100c0c3c0303440c0205058645581458002c3c0341c0c0e607010f840c107800c06540e0342c01965808c10013454200c1d00141a140401301c0501c100d8841030090350050700141c81c5038280b145003100000c20a10900091034041ca04002810440c00d000740003006140103000e0b650380039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 739513489 1250 739512239 739512271
    0x50604030f1826060c2505061003140a210318080904051b030a0b042403050609010203070206070807031103010b2701020c1e0a0b181f030b1f030b0108 66
    0xb00d800300c155668002445412911046c0080a100810510103002400d030700a0a041101030b00c20b0840d890304980c0911490400400d464480688452000400404808462001003110b22181c8c612440c0c0c0e56260400140c1010102c03c3c410750b600e02008100d50340304000800341c1e828185402466040408400c0010582c03500c03188507102c0380401000355150940d0f5242ca01056500d0760031549850048101d03080341403417100ca10041100c0036010949484c8140d00104400000510840b03208425960290140d52a108004c40342d03100083c0c640010075841d1085141d203030205100450080031b50202082d40c4055104d501b4081b0a4031203c0f51444210040c08000703940d801080c008c0c20110220782a20740712002c640d0310420214100c1c01c454010000c44404038080d00580001c020802100d441c0180b1241c03843d003044020140d54a40c40c0d54114068140d0718114060742211200740c01c002c02540031024040780f000d007142c06d4404110002500e0341002c1c03070306503001040a03420a420221644003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 739514739 1250 739513489 739513501
    0x3050f1204030c0509060301064106070b04150f0e0d080708062209080406140f0f070f12020d030b0d320714011209050604030f182606 59
    0x500307241c0d10138103009022100008890341e83c290b0003003000e00019960143e200501100d46412404d1188920300d01500e864060820111041c1052228080081400e45010065911000d40e040c02400031180c0036000740c4880d103110501d000d12011102480000189214400304480c90424000011402e10134180140414142e010303002c07503400032040c1d03402e08040c800031a4a800280e540400007125610b44491482040040b00060085805030b41e550000050100c40c121540d10440103040074840040080758070104550014140541c040d0298020610458480d1a44031a0013401400140c100c42210715005070144190203000d030f0107481c0302411440c250340300d848103000300514458400c0c849141068455028400840340b40f646419114980d54403408400203500c046c03507040c0031514907030820364283e00500c40c25940030b805c28024141e548940d01d0640f03605050f07502e00000c000c00c4a101d0318100789848404402041fa031000d0101080703168100c0800c40000020780d48954000005001c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 739515989 1250 739514739 739514753
    0x509060d05010636031e0c0f050103110f19050708072303040305030f090d0c060201090620090111010b0a0f090e011119021c0e0a090b030318040b040603050f120403 72
    0x1068070b0f44400e0940000f00f4008040702005441b010061010084100100b030340c00380d8180640c05c036030080c1c80901494401007035405180c0240143c000302c0080c14800b082101c22818911910080c203803e100d8503002281e110b852041d481500309449009102010a50a01940c0c1c0da001c2003941c05405941003504581e1101d40b24406d04600040c0300d400032542d01556640c08000c2c0c2d120300e60003e8101c1c2c40558803c0042e02a241c00301c02980c1c11490702c150209101d000400c00e2034015800228145405103440c0107540b81100c11505814540d0b0721500107125440d00745c20071003d0300880c80310320f40441c501610881074440410000d60756174189880103082c0a006410f175640e1220b84201d2a503031070041c81040b450481e034500c0c00c295842020030308030703606a004141883c641d141a0380c000c100e42d4480b110070301654000404c40d90113520400050072603202002401214000080000c07540e005000009030607201950010380b41600600621a4248000c1054191101c51021024142869070700c90071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 739517239 1250 739515989 739516097
    0xf02150f1c0c0225050303040608151e13110c031309180b0403030f1107051e030307050c031303030e011b11090a090605041b050409120509060d050106 66
    0x5400040910440e6107400c1c1503541d0f40c017400d00502182d80322540e07204018410f10080e50490300409a507071803181d5608040b0f0180038031803a05601d6095030782056051102c3c0c02c1803841484c032441e03901c2d0030030610f20b08903400038103200050000940d22511100c102c401d03401071f1039100d0b5049505d042038034048026060200301800380c00501e41103907592541025805802a03054100140e4135000307040d0100802070b0301404c186030040d070407145401000000240d45030f0050003400031503441440050f14451041c1d00801c1c4020b000400d8908000884100d00c2001c110b41d081180440c00000d01110503580c0301403205084101c428616004680c180c5407800500541d0240c24000d1000100280d8804001c0c0c02c18040c03160b210900308100d1074603042041408041001803043c3c0042040c0020b01c6240038050f0b00902600720000130350101c1c3c4080d044da00c41d8408001290881014060f410f030300059445014000d00c01350b122074202c0011500f1651801646100d4103c01001c00c3d1290100d42150071045 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 739518489 1250 739517239 739517263
    0x90a14030c0f0f1b1f090f05010e090a0b030a0b1e0709150c030c08070f0b090d1d01260106021204180c09080313090c050301050306040f02150f1c0c02 66
    0x4d6050015080031981c0c0e016401401c408207401d0780e481c410300a500400050881f801c81c080209400d445100460380c103890141c0303150b4001c0c88000820500303c81d45d8090000d80c0801001c403400e103031441e07440000707040c4100c0f24400049401d0102d0b480c04150043e0040d0302112503d8905c80315810001d680f030041169115003401c00ca101200317542090300400d0001d80ba03507000071169844201c1890001c40c0316944500c2220500003050205003008400100340b0500c2e10140c84d030741d000c0d0319094100c040c480000b200350742c1000b4001d6410340121040b19022a044014040c5070714056040644c061700d0025038070382c1c0c0f1440e29002c1004015481c020401c44180e105005000316070f88101803421078040c069030304844480d000010f42428040c1c2e01d050103400b11075009106001503015a04251102d000074469035402d03410950009002407105656000780d144001c00490810200100c0b080300e5800c4850322041091000520400c0010080c01d02800c1909801092080c00000d03903000351201032013194 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 739519739 1250 739518489 739518523
    0xb0d15090503090616030e0105030105240717120f040206030c09030a1202010c0905040203100510020a0501060e0108060a0606140c0102160c1802070b0103030503090a14030c0f0f 78
    0x4460401405100319050003d00500040d1207031282d4540d0001c03041e01e200300f10081a0300584450295000b0403d0720f049403002030011040035031068030400c1d0031034600b0580c403440c4410480900017490580d031452250410300c0c85281c0359443c29a010340f0319800903145445800c9401c1c100801070303a4000440703900204100a9548070024840400d15041c2c1509005200400c018511048543c4c15402010480d500e541e49460701940c441c01d01c0b08034403044d5a1012049408403050190382000881840d086009204a41c05c0769016150700c0e01311240d40d041308841d03402c16001084118002c1040c0758000000d80c804000c010324084000d0f1000361803c0041c07031454400309007910090820340c1075911318210702540a104401c6031600c10066503142c01800e0702407262242d055920711591003690705640d4860032403410341c0d096840690303d5070401000009113120716806140065140312541110902000c02136071500106031649090022103d02401164000300401e04400f0300040d0a10310314000e3300d2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 739520989 1250 739519739 739519751
    0x20304050d0309060b0a0308030a15081903020a170403061b080f09210d11041202060304020622051e03061f0f0f05040b0619030506040f140a0b0d15 65
    0x50441d000e4403081c001c5c4c6510426012001041c00030b440c0065106182c2c0c5035080080000d500c448a6a00896000f0200f00c0e07406100c00c1c00602803002c00c6403464500a0040340c0500110340d6801c4451500700c0c1510085100c0860f041080200c00d0098125410344620800c1010708207420091149900402d0100b02c00020701c0850b8100c1340c01c2c0407581c480d00701007480701e012624104030034aa591064080c1c032840d902d01400c0a80c01c0603441d050301c081d550f52440c4200180c0c3cac0ba408000c802d070009041a0703031001081204203210410540d246c00c8005101c0410124146400100b064026403103240798406415410121005d642c00701d44580d0081c550703180046041f850500f600c00d2002c1c950804031508115601c0400d031100c0701c00d80d840c01c88904031000d00c00000c10b5800d1001c54007800c41e074440f052201e03442586025000707801c510340c400b4000c0d000003400c0f01405400015a16015520094070b0010700620042c82614082e80b001303101e09076900c4a5001c010f58400f0580c0c4968075141d00180d50700c034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 739522239 1250 739520989 739520993
    0x30109092d0524191b02060f060f0604062a03110105010504020c030d0f020903010e060117070e13110901060c020103050a05041a04080d0c121505030309011d0a1710020304050d0309 79
    0x43c0c400000c17031320701c00801c545441200802a584200507200c208170300060f4030014480d440c00b43e0b0786207d8490040c0006003401d1a1050035100c00d800c041c1080901140b41e40d0802c0c03000b58065050840354003c0d911310309810310400d00e46003168410303002503000e18010803d610b50000004115010300480c1c2c4400075000804003902c0009001d91011643d15500700000349203030301c4d40046c5242c1a11030040d0301085010903141c01d955510b96500c1100c01c0e01481200080c564401411042c101d04e0090414250042e03007000003604070f5109810102c003040d8220303688401c4d56454800d2591207a84080200080d04250319800a028104459119900c01d0f050004080004100c15106500d2024070180151501140d001d0002d0300090941c6d1001403400d054000284221525442250000740186140114207801103801a6030344840c165448036001d109400e588a403500100104070f024500e41205d41c0100480e42032107200001244038a00600600001c00d40c08910b0394900c0312181800210183c00c0c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 739523489 1250 739522239 739522241
    0x151802070804140a060e1c02030c090106031b020325080708040801020405040b04090f03080601140c0a030f09030c09052502011407020f03030109092d052419 69
    0x181030040003600045400124462001d0810080500884802e000d064850504466000d041c181300c0c0d501ca0f880b0520401711941080c03040551500140907a203200d01c0303c0010402c071400c280e1003c0000f07596103001c0d486482d852402e2301c0e2400882c1c8003031450f0941103106280c90848055606400110000381c07a4100810a01181c1c4a203900c901c00c59103413135841103868000c1d000352180501031414242d04041610701442905a03040c1d111203004c17805503d540f0202c0c0d41c1030006140506122030807a18407041c11804014148640080006084112140c5030080c003600704403081d8024071048110500c0069040c4105106031015420002240e9403611f901d644c0d07160149216100c415281c6940041142d81900800101105144012180d0b00d4503802207950300d0340c4001c000f0305034000b40300610141102d0341190607860b00403030003500e5001c40c1042c0000c0ca503810b0b403400041101300e50020010040103002030b0440d0280346d201250200450740d110341c1600d40007843d0302488604419a21003403091 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 739524739 1250 739523489 739523497
    0x121503321507020709020408030d05090f0106121e0b070c08040f0608100807080c0f0f12030c0d05181c06050a0b040536011b090e0703151802 62
    0x15000403a0030540025141d008020000e450710001409140000b141c082070f01d00880f001c881403a8011481c01503110002030051001a2003030300c0e9800341454541e07100c0800d028040c060580d07204030001c00302841c600444d800c404042d4461007180f01c01d6214010402044907103078401094105074140a03da49020880e620441d00000411007107040003081e01c661162000e8400ca115440c12010345884803d0241c1d01c84c101d118800041c0d00202442c090390400d0035120b090943c0180c501c0c04040c40010006041001014601510b6403000c00c04051206080150b480294001c0c1041c51070042811407244d129860110260300401e007055644040e45900f1241c20003142e08030300308010301d05081d0528030140c401442c5507407150b4141070120308198120000318400c007210a000d45e685040111006a25a604264840955590b00c0310120310700c00000420030410100d13a20300d0030140c1440701c6c1d070800401c06031041c0c0c2018900f202d4510b020030604e4090701075401000300340703200782400c002c03213000707481 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 739525989 1250 739524739 739524833
    0x2a031110110a08060312030604020901051c051906050a050f030f06070503090705150417070e04150e1b01200304030501020a08090d09030f02040b0d03121503 69
    0x12a0480440208184001420b0107080541c0d80602030f0f01c07000e040640d929000000000c1001040010038070501e05030340249080394060509900b80004c584403000e0301d80e040d184c02d8002545403000c1100e0131000c02680e440e40b01051508201550500300800c591030054000c5038050f101c00740400032a42d404210032030040e4804030445140b031400c07280007041c030780090b0392a0229214050002c1240e1600d11200000311710840425070405150800001e4400301491911005000381e1001280c989009010745101724068010781420786110b0030500d040341c50003085010590803c40029942c18900056014008000d203001e1030a1000c0b00010419040c1581c0f041100d03100c00070b07000081100640140041d0203c54540100e40e0741e0700c81c80151520b02031050741c0300260760f0503000c1c80055407131b41d0041c04070b5001801c0000c107042c031140031600c61054124260041081c8110041c0b00c4041d500407070001400e4050100d90084c40c1d036403141c2c041c1c440c0d26602d020340c0d031600310969645066103c002c0102c1d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 739527239 1250 739525989 739525991
    0x61128020913050c030f2104050d030c0213020a0c03031505040e06090f0312040314210f060312160203010e151008210304020307030b0a0204062a031110 67
    0xb04007904404101ca410000459560158050000c01440c02151040c40d0030b10b04005030445007030b203107800b580303131035082c820f2201d4010300744004905600c50700351824107184240c944000c403100c180100240c4040d03a004400d0300b02e00410201c1c00d15a48244c0c010a03140d410704004c00c128900042c602000d032040c1e04a035030090310f059a0034030311140c005296070003103030507a05071980c2c0b40c0202d1031291030f4420003500d0106140f40b080400d00007440740c0489a845000031803020300700403184250f100c0316035110204100358035502c1c041c08500324526594a8201c0411801006181240710050a1034007034001c1000c0c0d6240c10324100e200b951070a4002320300c1010b21400340c4901c1400114100000c150565403040c07140704e500c6011814560001c3d00e0a4481840a00d1030b806441c154503840840d0300086c002c90301409403440020003d034000150078040d0051100c00b40c1c46c1d0342011001402034108855440c0000701014440003d2070140d0000b50700c5d0350301450410030000301849428601950700b64000080c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 739528489 1250 739527239 739527241
    0x309021002010c1715010f0309052e06180b0a0302030708032505101112090106090e070f050904080408030c01090b06120d1818060603060611280209 65
    0x307074103511601d040d03003158442141420310b22241901c50141101c1c0c81a000d50050184000c960081c0c1501c500300c20145004184070f200c2e036451a0070038442001c51080c000c402c0b0000010580c4d440031010748090319400400031a0710b0040c0c051500d20f0302518103200d19582e80201c2e0300d15101c102c1800047c640107421194225540d00c4565035030b81c4106840f440c2e41041c1000700f042d008414204d45103007900180182011083d0f502124000e28400081c030b420010308100b044c001211900c26a40310340000000003c165107007a0400098032b030b0320940701c1d9140e00207500c24415012540741c000e007a1401030300c990b98a60344500d0880c455116580114455220120300144e02e26815003000e100d207031081101c65000d4544400b40051100c851304180e81c1390700100c20000c0c440c0c1c42030003000d4155200201c2802c0181d510003000f0691064840500e141d1500c4810901c00141c26005070b4008140603d084d61039000c0c81d1484a0f200c0e40d44164040d420950100040b05054521004c1c0500d150010306c80701d05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 739529739 1250 739528489 739528519
    0x40807030803070311030f060f04240f1409010b090307120c1d040305031f120602040e0f09030406050a05040317031803090102030a08090f01050108101505011d01030902 74
    0x82d4000312841c00000c1d0803c0d99141c1751884ca281900c0c005c0302c200b00350800d95200d09040201501c0500505070700b20b5541d801004002d600184403944041d01b0f95041050141045c607183c00703400103900141385214860800c0906600c1c0c0e1050315045440d2441c02c15104c80c4031000103410214030ba4485080b00b5403030352a407000c0c0302c42c15405008464210400a90700072000540f4100f101c1c04450180124406100150103005980e40f0110590404030741c0303620f6292562006610030a4011042d1000e550109043c0041c9a044109940069603c581c0603040d14081842541da407299001c0c02081060100b000c0d001035000740c00b55006981e01840c0c2c03520524001d0141c5440d038000300c8131b1210b812540e01308403980c81408000c031071a500060740551724004c5080800d079002040942107030403e01c40c000203207044c407600380305542c0a840c10201900c80a80f00d408400182c0700700203003901ca41025070500700078680e00a01081000b02c2d00c2a0080c05000610380140d00030b210a150281d0004034940c500c00c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 739530989 1250 739529739 739529753
    0x60313032717010b090c0a030f151d0a09020303040302220501030f030e101e050c01020c0a0201090e0702070324090305041d0c04050108060d0516030308010605030f0609060604080703 80
    0x20701140401d00802c2840d00d02c4e000c0101c0310301d00751440501c851081080003400351184e04001102403000401040100b5007030f04401c7c5285460303001c5003420146074400c102c00c0f4599080c203504a08108410701120056030002a10ba100d644402440741c0510b00100b1121500c074400d50004044502c01040740c0e40c0d407814914424500b6100440002e0b10400c1c03511090326241e018140007070441d55440010003e10701506c228444d4210b042000e0217401e000c0000c9502d0700b40002d080694500d00a0306648699100141c0780c10b0550304201401ca8200b400c0201081c1d00164000c12650007103040c2c802034044031000d80d441c041309248001502e00340f2034a00c081c1600700e002401210120902d403401041704000784111030f0703402e884441d02c040301000100020340c404c00d06e040d04504000c281100c506150340d6100e14280e007400f100010101c0e890303000c006042d00b0a00b110300500560804e5031551510740400c0c55000e00c002c211610078001c80c000b186417511010160b4019050400c00c407082e0b80d03103a080c025 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 739532239 1250 739530989 739531019
    0x200f0705070905040b040b1807140406080102031053060f1006230708130305060103030323070c080f04081c0e1c02040f020a030b0f0603130327 63
    0xa07d800016001291069100648408000905001030710046051142840c03900300e0303460704180c2c840d880c1c003000300d41994284000c1d4041d0307959801c9c001a05142c83c101320441c0707a04024038070700b2000e44d45807100007007100382110881408504043c0c44500b0701c040f40050121200300d80328214072402c4100084400a00d5049000e04d41c6120100021507440304111800c1980740d581115460181000c0590b99584c034002e0501d06208180441c00e1040034040501030285992050f200c613404500100300740350305441001c13070890500180e00d0818a408201094442014010310304000e8008405000d0100c040281c030118800c1c442c141c2ea442e66030f1120710380d03940c10300304021091010b1240405051801981c0030300320840007070281d652180c0310915a000450700c0c5042640c016844586d181c0c1c4858a0f0700c0101469010360300e00041e01c08440c410701c04085150920140680c0040042c0b15583e030360380d0489404581e161030030810b03c51010b0060f00c054880005003600d0203004440110314514011450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 739533489 1250 739532239 739532243
    0x80706090506091609020f0d0e1e01020708041403011b02010c090803090306012d0902071a040c0b0f0d15210b0604050406020c1f200f0705070905040b04 67
    0x10b0b00c0d151500d01d03840380c0380e010f004083c840040c02500c04002e00700395500601204001c1a01007800c01d40048440307010717140e05030b05625140d00010000030300c000051903440d0142600100071418000c0650b10040f1510946c09590702140d0710320413040d12540d09420a9681001000d4a059210808000a03002e07090200b100d1012075140900800c0746c00c400802d40300d81220090051039107905e440c1000c0c110115a4a51030590135094400c0116980d030443c03010000c00030000300680d100c1460401a00c101c40c40d0841140c041d0000d024840840c0041c003c6a05803850208400e54921807075150b001c1c6440340c0307282245030b141490005444a00b864252104035816000c03000d91031051906488640011300b24024010018003000c034480e0308103503200561241c49180014a0032a12408403454880d1410544030910900c2242441e004a40c0c01004260f03040034110898101c0d8020415000c2d00034070038019101078011035100240b200400460b0001c01c5803440805c03603801e080c01d080c5e184140403a41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 739534739 1250 739533489 739533493
    0x102030123060c1b15071106070218040c0609061b0b0c1b0609070806070504150c051006090b04020412080904060b030c190806030c13020d0204090605030c0a0e011703070807060905 79
    0x60941041402c000c50b461945d1001c00d01f940781e500c003010440d0541142501360381050340c40d0040d94480070300700c14a0303014074082c0c1000c1c107406103407200007040c1c0c1c04a900041c1c200110307000c1d0085041b208410b41c2c088154000c00b0360344a95501400c0c05071500400d8036005242110340181e0040d0040814201d010b00401c0b020341b0a0151903280d401c2d55003030192039030400540c1c00c010802202904544003413030440a0304d000441d001c0c59031030303580c40c06440035950028190303a104108859900d134460001300b200151750a43c14145072100310044808160b10241c24041c0006510140b40d417590700c058050099003005e2612418980c00071041d07900004042c61320005003405600410b4003070000c0c81e02c03510707005000300542100744080c8406034103640d00d0103400580078811400d502c0918006040640003840d0001032482c40c00703041516182130a10028017800c403000d0240080603000d05c4880c1036a404032042c40e00d549a0110365840c601c203804000d450010041040d00c100070140d000000b01a0003070003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 739535989 1250 739534739 739534759
    0x4050406090504021c1a04060c0e270a18030507050106060503150103020d1b0e012c090403020304051306090f050c1803031201060203030103140102030123060c1b 71
    0x19901e0226a0180e4002e0740c0508848030003c035907412458042c140074800c104400040044001c2d8030101d040540e400c03a00e8944602c4c00e04006688103c891078111001c8038401410307502d940c1d04031030050142c0d95001c003ea404034002101c0701c0d0590014090300803004060000c42656040040458102d08000c50303040d400c091002030f4591160041d03070b00618501e017900458030305a800640c000d500c0141d203900c81d10344440d010302c1d0041858082010900c030903122a582d40948400040c034920340c08a4406034050a01007120b80740400015084066400350b8a01246480340d0409030b145000300d5120603488008001145448462904058110350100d1803d01048205107200401c3c3d8000300c03260311048070140688480350000c660101c03105e4102500f5246003100340350000c0002c0c4003d070041c402680c4000010010000c84036445041000c0b41d000840c00c550410320b4100fa1444140c602d069020710458845c0f2042d60340702c0455220305100c1046424040e0186e0b101804800460303202881b46400700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 739537239 1250 739535989 739535999
    0x307020f03040f2d030804260715050c06040302011415220f0e010207110d0b06150d05070f0e010f090e0903090604090207050c0a050f130b130204050406 67
    0x50b5000e5800c1c0d40c0e10280040d0902920415030007400c070005401c2d15400080f484540d07214142e56026600400c0c00e650340c0c1c0c0c144840c020a688038001519104580b040c0d454240510210b103501c280e5000307040340741c124000d02d00e0450309801400380f61316140c010b100c148000c0603015440500650342d1042c01112598a610080d02d0352000420f0b4142c000c1916800505000207615000f001384003c1000020281c4003964048100c0300b00c603001400c030360340c0000d4810500c29400a840465042102c014541c604150785000b0700640251801d80144081024190004070003026a0081c0a070204100198580701c44000d003203104ca00d10400100c0e40c40c00c12544107520501079611301ea006a182c00d003c01d40b4000c4446a881002040001603002c1404010411750b40d400040c0001d000c003c0c030140e00d40709a4204141840c00c0d01d059603105031b40b00e134400c10040c0c984800c0c0140b041001c8030b00c1011450303810300c0c18010f040390b0120942e006000140c01060401603901030419220180d4040112540311 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 739538489 1250 739537239 739537243
    0x804120807080f0a1d0307051b06070305180402180f0103050c0f160c031506150c0f0203010e120a03150f05130e070e010302270a091b09020307020f 65
    0xa0701d801000401d200c0000d5500b403101da540c160000942840090890901601a4003c1135426007170070031500005154018000c00700000824039540224414038003007250001185845400f000030700b0f0007004140c4040421403078902c1c0314036240240c0103650b6101015005100010160b0846114282121361101e03154824031130140700365150541a1702c0c3c1450316800388103d400600c04000300e00c000540290005070000d10b40130003540300c1c00f141d4001e10f404060303c0c01a20501d822128490015200241030b4641c80f61505501507000004c11150b90100d001181c050121203266034041e2240220740d4401e80825401030082604564040000e48400740e5803852105a40c030031414000104d10b01800186890307036010001a848400c0040c06090250510f400e10f801c0e0b40c400c2c071247c01010010001d500f00100981c031010111850b8035107581008003280311104000c0d00b403803035455550130040100440d0b00d0760409125210202400243d40d10700c10007010b0f5004a43c0c000050207810780d001210b240c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 739539739 1250 739538489 739538491
    0x30d08070246050601050114041508010f06050702060a0f0c02030726071a0a050d050106031d0a0c2105010915060f0803070b0c090405240105070f0204090602070503030708041208 78
    0x88880070b004c0c1d9034a4040111404101070a00b441b070030030700300000509441d01c10000947c41000e81c03560901585030404070309103e181c9070b000c1024841d0402030b0313100690f101c1c0100d070102c02035800c004c0c140301346140d01120401200c400081d0544030748513010030400c00304407140d584401c0200820180e081c0c010360031901d81e003003486800c00300c1204003060110480e03880040c20810083c0d20380f42d03061450700d00c042d0041d11000e074042e101082e80c3c0c051100c0000d4034004541c2090100c4001800b0814060340ea8218060562140e41b01c40441c1060400f0003a444881080324175401030024410b0b14041d00b00f0103001141c403e40003420510340140013030b08000d0040c00000f12400340c00075500341007090f15040802d180080c0b5100b0200c4c420412818503548512608d40500000e0704820011946005148040c005000140d41400340c14031020300068822210f0b80c1040364141d401082d15a402d140c10800f034001c616000708140808010000210f91080b1210311450094182e0800c1c0c9000c100180c4000300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 739540989 1250 739539739 739539743
    0xb061206150c07030209070c0c09060509010911180a050d0b060405060328081605211603262e12060b0d050303090d110c030d08070246 59
    0xc410f50400151a00100c2543d100c5580e05080c80d480c440399451041c0c1c2c010746d4008040f0544e42d1542840503041c900d000c18090310b1142f004205100101403441101e000c0c80c030640810224a0703403d60700c02c0d2281c4003100000e0001520403150100780d8500179062510444569000d18036045c002030080c81d001a0102076019041c0d641d025018410702e4840e452159404c040c3c800500400021940c3c0200003807121000380108050142e0b5003c02122401c0d0b407259030035090010100740000101800e454820402c020381c10f081020144601c0c241c01c41010541041149d2402c0e00001044010581000714400e140040c59489040307020b03e10b40321240c040d8134090b9001c0703c88003003040300010b02076034402c4852000041caa1290307480250344261540d4003c80b98030003150004210500c8250b00314162110103070745040504004200100030903035034600b40300044100007810000c00e620500034800c00d00b1006000703400c40b4003600c4c021020001c80a2480c60480041c0d00f80c150030042d40c6621190300095070b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 739542239 1250 739540989 739540993
    0x110d0905060a03060b16050607170726090c1002010603053406022a030a0602031b04060e0f090601090311030c18010e0c030408040b0d0b061206150c 65
    0x2a0610007030110340d41104038001d090581c1c8910110ba08810200680440610100842408401e6103000c1c2c3c18004050030034014403000810100e0f0300d80300140b030b05910074082d1400c14107032403000040226a95040a01120303000700340040c0705c601600850726000303060065a04000f00102c800c0e0032800c039152440050310a4006c14104012031880341c00108002c1c4481d10452181394010b80c0d1500040c001c2d40c400f10269214081c00911300503d072440c0000c009031190f40c1c0b03000707060b401c000c0b945441030414001c0086600000040b8680c01510108a074408503250958030b4503286c4c00e000d00601807080c2c50611491494410b034006203460081144200c0e410b81d41c551303007149142da903400c019080c20146075060003034121010840d100c0e00030b03035110071100c2c0400e501d00d54504841d1075040c44010f0210300101c1c1c0b0802c2000302144a910840e0b003142c04454406a81c0c0c0070080091b401400210b2106500410008206404203200f4083ca4043c85045600701403104c004002c040c114401c2e07807200f047d19 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 739543489 1250 739542239 739542257
    0x108060624070204110c01060929060901021e0304050306250c050f01091b0905090307080a0903020607050d110120070c1a0c0606011d0f0a08010516110d 67
    0x1d042040d018065552024002050154074800f200314075401080c2c1d5400141c0d560340e004c0001d90340a02a0031981c85101e404001159403d1501d542c1c4000c03840d4010303020700000241c44980364802c010045480000c15030184480950300000c540740d5109100d00c1d4400d20900c4040f03480e01c0008185413500d202420907030716988989450a948a4052280c241c45900541c0c4180d44200402c0c09295100e5100d4400d2261481141a4008803c503280d00030807100f0789040e040040c1004008115041140c001010b0b94640e145a18201c90850103030b0030094028801042c4001000000a43d40703210307802d0b54980ba4402500b01c460304c3e08072054902c071701e07404049170380c02c3c1b8061060100042c40e0060284041224942d04c400000840c00c0c1a0402940e0042000540c01c05c4c050b004e029460300610240307403540607100e002c03d01c0c028403448240154810414466424074513912402c112008207034140c000d00040c549800760841380f00c0104810408a480e101c80108080408a07030003101c1521511160300c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 739544739 1250 739543489 739543549
    0x30b04031e1d01020f010e0a0c0f050a12080c0a060207060e01200f1303030c0c0f0605030a230a0b04110c061b070c03050a15020c15070c0b040b01080606 67
    0xba140031100c1038158001d2190300f61560a0a0040c1140d16041c43c0082501c081c0900d004800d01c00c01c3c1d0312050151402d80310074043c540d00d2028040442d403a904098030801903e04101d44a4459030085941910403840b070141084080c0d00906140c60003402d0410001c40c03072501560985000b200289094011000c210f40c0c00c0341580c0c064501e03101c0b42100c982c10309801000303200d24000307a60015030204800005078010000e1440199000c1c00000802d84205885e00901a1080c0000f4044003000c64807500340d8a05d681e11591001c00800c150381d09615542070074400d54004112801d0454003d40c01c014440405254180c200c0d248107803503c0083c800d5554413105000c0c2580d0718040c0c840d01402c10000320010444514a070806580584090314140300b961410030541c402998280c030980d030041c0060400102d000c5840c401e41c814010610361240d030745845c112050f4801000040c41e6868010501040c450100c07440342c16a903480c0212162910f49030b081005e015000144d60340640080001c6a030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 739545989 1250 739544739 739544777
    0x11041404020102060a020a0302130305062d010308090609040f060905060a080604060f06080d11010b0a050d0b150406081f0e03160203071508060915030a06020310050a030b04031e 78
    0x50787e50243c1c0750050400c0d508210354040701101d030344207030780950011041c000000804601400468100d808914a41c00042c0070316201d10b00500c8064031903040403403211070039100c04e011200c42180050041080404035012900202410b0085060480c5820000789050600510300810b84603407500030310003903803199241000b42c901180c0d001f01c400e846400010780e00310201304507200d045d05503c4080c811100305904608503058040300601c201c02021081111303446580701c6d410344039009900d20182c0da49441c14844c9014a81400c0c0b03070081d00d0520700207602c08011480344194990b808400c001402c0b142c5029042d90036002c03c40041d500704104803062540c0a140b0310046a1014054039100c55032811030901a281e0525564040380c0c4010070003990745401084140d020107803a1850110304204004640c2d81d0b89940001840668008041025140700c480c10320001d040c0180380300c098a4030303403800e1491904242c90450215800300303034a034111028017505884034416035a030034507001200b0903528 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 739547239 1250 739545989 739545997
    0x260f030c040902040602032d0301050904051e0708010506063103152304030212090a0b04120b0c0705060a05040807021305010510051206010f090b030411041404020102060a02 76
    0x140014010070001a1003502030014000901e007540185071140c0c1c12003031000012000400c00141d000390f15040f074454200b0141928156a000e0300e0304e040c140d403030745070091508060319241c4202c002f8500034111008070020340380c02901c0c0c20900034072003601d500050092601890001c004000904844540f0ba20720f81404001d1445e5514850500c107550b81d207941e018035011071100400261030f40e42e1034040000d85401d04c0d0340c1c2080c502c4081c441d482c140e10000d446405020101583c070f04001203404075a40d4034803400014000705e1000079a207650b1001030040c00a0707907580494402c0540c5e00011408501e4105803401103070060041c05190340c03800140e1006220060003164a01d4040c8809005078079174441e000e645481560b00001c030765040408004144c40740d80b4a16042050070000704d040c10010780c034966002070003802d2500c0050751a94007900c0a00350703a0031890a502021040006000000b03419529514095604002c4881d82c0210070700f14000465001e03000d80e120130045020954958014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 739548489 1250 739547239 739547251
    0x303270506010f170318060d050c13060f1e09080f01020403032a0201080a1404140f0102070c14030a050a0302010f06060c08031303090f0f09050711120306061306020a260f03 76
    0x1f00e484d121003418a84203d400640358103100e1f14011907044d00d404a8144504050482402c3c4001584803001c0d004042380050121090007407102542c0c09640c030f000340c4882000e0507043d0300703a801d8442406001d41c000d4201c3c0c4400e03000992440c9040e03401c9451003000d25494240400011802c82c203603001550200c034064440c004441d61030307103e640740400381c001c00ca0140d4403850844031514040b44810b86444030003070312505c031648100408000107100100300011151f030441c07580b8851030f03640002810324040c04000782c060702650344841d00309641035001c11b11410b0000b10800441d9210b000c1101c21504005004254181c00c1020900242000c464820030740e1191804034080d0361034800c000c2040c1955840038904280405003880619290b0003081c0c1d00c607403a07150114410380e44840785075170381e03101001c614980340c00040800c405440c2d100841d82210181214200d00d80da941070002d644d80d02c074034800d584d901c54031504c40000e44170044400783c400c2c0c44c0043c0141002e45000e0b810515074805480703 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 739549739 1250 739548489 739548499
    0xa05091002040605091228060b0402191b0314180a0f0306050c18150f301b0919030507050a0e010806040303270506010f170318 56
    0x3080040a400104090012035944a40f01c550090502840f404140507509145e0080031541d4000030150f8130a5185101c03c40d41760551016500b481c40050001c0300440d50020b0000400d9802e482042000a00740310003a80c41c040c41d10762039612400c082d54019002000161000710352400840b0070f034050f00500e02c80c3c1d90b00c07488251001d4006500a030380d0743e002d801030b0040b003001041031101c00e1084c2e59001414101c15864401c800410762044d000503076025120303800170016904803908403c255140c960041102a0391140018100d00810705001800001d04841c0c89503015440507011303484d07010b60208c1c6160600e1240d403070000d100a0300300c407040580140302509054420591070b0700d03600003180580040c1c1000c5061105025800015801a49102c0011001042041d41c00101c03603038042d4061500203029001d21101c201c0b0880700ba4103000c80410654555002d110010500070304032031030102c801420a60326040c02d9041c001614603620b00d5001030114140b9010a0044400d01500c0245 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 739550989 1250 739549739 739549753
    0xf010806070806180f1012050a14070909060b090919170c03040320150702150405060a020d110c011b03020106080f01021c050f1b0d0c02030d1b05030a0509 68
    0x1344440c0c07880300481e07105014481410900410591900c1c2c50340143c589084200360301584c40e11602e9a6508500c030040507003041c000c2c40c0c488541c0c140500e102610311010184081c1c0500e0820a0190140d255098400c482c0c10b8080b407116080090184802c20b04150101894a2940c0702c504460072503c0021080e460300f0000302001c00414401880554810f240403181c4804102c10800c41c0d60520741c00c2c600500418200303511240e2040b050340c036000ea04503510711f18030380c02122104060286034071140d00004d0104160f4811500822805082c400c10b07a1403401c1018400e418541c0ca4040d510a280400c01c0107501440003441011900c0c0e0300d0780030b4000419032680d2048540e103014945030540065075404100d03000c40301c000c442040902d0031040c506010506000304e004400e9540030740740000444d01c40d4000240f0400e81030a0758401d81200008024644a0341e82c003a44a920842001d84100d00c1c0c50740310a8505400101c181560460b80e44071803c40c0da40764141802070001070290502441008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 739552239 1250 739550989 739551019
    0x30f16031814070506070201170a0204181b0503100501080a230708011e0506071a07030c080a06030f0305030a06080106141f0503060d1a0a0e060f010806070806 70
    0x50450450703031007004001d12a03250003101904044107504040d204001c01c000d01c0c0d0241c0e902041721144102140f40a881d2a26140e4a0200911465008215101c6c003595642072030004c0760302c101181c3c6a24104500e03080d6a06800712000d03c801c403200c148840d6600010b02903544110381441d4405644940094101d0b04040d005146a116005005600703594000304003040e0b40c44031035640100404440c21500312101403411004d00c0c601d000d5140900d601103001000c0c4608070b0b80c5242080642c00780390901d404c020030010040c00c5400296000b28802c0f0003c500b40710300ea44250b10850307070484002d00558003a650201d40d1680003801351200141c0354000420b5260082c8644001084034a51900307003090028103000340044038031071208100d0404898140038507000000c40b035214100310b40c151400056031400c25810413203205c01000d0007525604110130802030fa13003e42c1c00a082d09044480399620b49030070700603040013405002d03220f03080f0801080003180280e1006401603401021405158007135 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 739553489 1250 739552239 739552271
    0x403020402030a0501081e0601090507170f0109060f0509542a010908010518010e030c1011070b040605060420120702010b0307060f020d0302030f1603 66
    0x3d07900b070700b025a51000100403488040184445a003901e81c1052000700d030400181e601c0d00d5051240301c2e419916400044c803858802d4400707000103965840c0daa411418a80c2900c8154a807d025410b41946810008100c0da80031404040480320000d240c501d00b6564400390400c10312010110208080c0e65000001c00701c040040010712003400b66003914482d00e00c80d15004401c4408154958031900901c00c2c0b021070341054514040324460100100060241c07010040b184000c05501c524000c0d4070304802c0c0215144406c000c100314102401c000e01001c0502100280c50744250034034402d4a511100e03150084205980004009161041c05141802c200e41c40741200805c00b1103040754006e917108200724291030181300b00500d586e03280c100a50b488140f103911088038840d00a030351200030381c05000a17141500c02d4220b00b0885a015017581c0c04903581300c001a180c3d401500703000025024082c0c116074101d1092082e05d10440700d00821040503102c0070a141c0e0f01c4c40040c8400010513488040d511490809 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 739554739 1250 739553489 739553491
    0x901051518011107090c02010507080103020f0904020f0402040306090c0506131403010f060b1b0708031b010b191a0f0403060b040e0102040f0503100e0303040b07030912080a0b01020708071406040302040203 90
    0x4000740105111907146c50003402c5400061550040c0400700005201585510a0705a100d400a880b0005251607600000380c0c070411410341740c0e50080c0001008010004107410150700c01d0301c6200030346921030310f590410441d400381c0c00d00303403090200c441010011030188c2c3c282c512103810041c000288400c2448000340c196412900462107158000a4964000402027495a4000581005001f0880c100300050340c40348510700b001149142c800074004241030007075110441800000b0702e414050103080300c001c800001180300d100c4a20301450780800c3c005002800301d8418010341712181d803509065a82c0c1400405200c003019400540e2030340d5901c02e007903007440100003401c00c401000c681cae40e15020402d8584000340100d025820b0908113020700b001000025030350020b5001c60649099940c50034120700800a0074406800d001c44c5c1c0a10000240e0003121b080d010303a001e404107024081c41c0c80010380e95046580f080c0301c060390041000f0000007041c001081000200180142c0c81c00766250000381c241e0700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 739555989 1250 739554739 739554749
    0x80405100e1003110a1d06030f0115020303040201082716230d030c1a0c03060109060c050c12120408161203170612010c02060103020901051518011107 66
    0x180c1d1440c014840d1400e0070345800210318501d03052101c15008107914080f030003000104402e20080c110102c40340792216201e0098242d020b40790755200d141c100b8500d060008213105000c2001e8034142c0d2019054800b01c00c8030700c038680684a10803691101c8010b03500361440b400c158002200105000350055106201100380c070300044c503038808824189180300380309000401c00d2140080a1210b840c0c130684540f803100d0301298050406100480c401d0520b0861010085108007180c0d50290811003201c0f1044040c42c056007003a601c00140548030181580c0300e0185c0600034140382c0c0401500d80706c0c0d01d040b81c11030406400075020744443e5007500514103003a8000d604420140d4221a0106508480f0160765170000c00d02d0504801541c01c031500d0107801504032400c155404000e01d00080c0d895210885c042080e91001002080001a0741c2d00c02900c90030f086c00221710503449070000240c40d2501c80c100198202240e0302c4985800c0007082180c07017075400350312854140002c50104c03000c101d500780030b2500140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 739557239 1250 739555989 739555997
    0x70c0204020c01200c06130812040c0303031d340b070b090102030c0a0302090a05150915042709051c0201050901110702040f1e15090905060f0408040510 67
    0x4083c1010313424600030006204280f1606021115000400181c40303074000a4584061007103134181e05007142d4503c102803034076640b00294018002006000200407003181e00136942049902c025813501180c80c1d401e80c00c0b505096000c9070b149078000d5032178440c15003034524a00170b5030700000310101000f9407201140e01081c1c54100c0440c0c41c1c2c00703201001a8655010503140002c514510308140e050513140501800c0303908055010941c0406038403001008000b0b000e000f0325002e52081070164031580307070741300c0c1034018000c484040c140800000360f50240d40c00c1e074544200404120910419800d240e4a0b05054492400d40300c030300020105000f40503800c09440440d18401d0541c1030510040e0035107200bd810544982e25140c00e414005024201362204654101d03000f00344030a68403580005008641d041c040c104144080c2c41d113042c0201d90205803a44070092140c0d131500d64a882010441c0c040c55030140050700180e0000d11072009880c1c0e20f5034040e00c280e0009081544a40104940b80400d2041101007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 739558489 1250 739557239 739557251
    0x40c020d080906040b0708330f03070e0604020711060d0c0f0c030c080c0115080d0f08060d0206032703180f01120b04060513150b071a070c0204020c01 66
    0x80d0751119006901880e00d400900031401e09507074072111288004e00c01c04c100070f00200851196a00031041354070845070401942c10048071001003404116144a41e14801c05040991561504000c120401140c1d05140341c030141d9a2408284000f95004110464200c003c01d00030108d280d81c1c03c405494900411407000030740b001a0980038200a041d10f00c0c0034103011300c0e8298000080ea004c010305450541c002d40c11602c403c00c0009907409840c501183c0e0103210a00030004c07072507080c00100e400d0131503001d0f6118224031103d960252480720741500c000c1d0300800d4040015000d414410300642d00050180e112280e00c61130a0744540d141d040c00c0c2500d410503000000c1c0b05500b03d907803003c3e00281c00c104542080c58018440006040b28072040360901d0300584940c140c0b1900e9550b07500c0f01009000151400b40d4220480b00070100408180201448001c800c3d20082210301801c0140c07030020740d1240100c0500c50011808105000d402440201080803011000c00140c60354006001c1d0184858004941 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 739559739 1250 739558489 739558513
    0x1c0e120706080108070b0307121407110d17010b18030313050306011d0402040515130f0501120305040e0415140901110c10110904090b0109111207030c0e040c02 70
    0x4001410384c0b14030000e60241005000b501820720441c4e80100c01414407041d03c1000b1803041e0301034691040305a18250301c04080016603078108000c0030031003d2401c04c1c2c40514030044029140b07061071020341c15081c800175006015203c0048000c040589d40c9120105401c940180001d145902c840d07141c060284e2005810041070030304010490140072100c140000c3c1080c845901e000340d00c00140080d202e0b80d110740200c2c1d220907200da041c0c0c2c40c010380508144201ca481c40100000380110350f0040810914010000403205002d44501c40e050364943d56007450503217002c5580180e03d001034000e031040340b0403070000e5110f80e11a1041088004050090070345c1c5142c004402402c407120300c0a09011603000300700d007a02d204d00208401c008240c0d268000100e600980300364405ea4090007994580261070142da003c280640b50461904803244040140483c04d50602c00300000e0064440b541507848280e40030031002d0303010350482240218a0310300010510ba08400180541e40d1030140032025811289203200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 739560989 1250 739559739 739559747
    0x2130f0905070c020105130e0a02071e1110030e0a060606110a0309050402130504091b08120a0518031b1503010b040302060c1006080d0e0405091c0e120706 68
    0x100a00c80d5410801051501c600041c0281e050010300034100700300024040d03044d911008140c0050211032449044519003d54100002d40c0000400eaa1403202d150004245405c1e0740b242040459003c6082c0344200c5147c803c0c440050001e000ca98140754071008a110940410004609483d0040d07501040d41440c00310041e1075000c0c024030900c2c0e00c1e00404221004241c00c000c84008880c0e00307039001644c802c07000200e035a140b0b42d10340015601900340540c3c2000d101c0e80d01852500c400001c0c098000300c0d544c400240f6501da10300d00b285404081c040c020348102c103014030b002d00f03070801c0c00c0362404a1525000c00000d0a00700031101c051405d024003082080e49050061800a64604002c04540b865052101d9004540620f10000340f0680d0f000402007048202400b0001140c142503074140413603a00c0e1800b158448506500b42400034a007035090b048940b41c140511400b8030f0422000e4004820f445030024a860308a031618001c1c028030004008070790301e601540d07000801d45000680040e504000c4020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 739562239 1250 739560989 739561019
    0x110a050c01030e060f010303180b070c0e010b07211106070f1b050709020f04030f141209010e010f052110050406030206040920030a020c010b060408120c100213 70
    0x4050303504c500d0421201c080b4144415041d42d406041c2224280b8a410440003207040a800c40d110690022561400b0400c1d0705100c40e055859040701900135a8035800c060300c0302d001d0054041c240d07403076450201c98190030000340c454504410b8a80301c03500c101c0e407d0800b460050241c90310b40008601400002076264448603c40b420f00642c00503511400590b140e465035030800c0c0c043c0441c003540c00039140007101502421540110b5003ca40c41203003051509205051908842c03500f0010b000342c0d02c40420996844c0111824404142c440030150900302004403043c0d0b10500c603403428058100011801141e07040c04031561110001a92046450400f241106801d1194402c500840c2013900500c01656000203980648240d00000920802240ca14019000340800b201107503000c00030074881540819001440d030804400700030702c41c02030b0310011302185100718816220580c102021804600125000520780710030184110b941054010301420f00300d84c4442c0e00241d01c1030340d00c01c6c01c1004030b24a41c144 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 739563489 1250 739562239 739562261
    0x2010b0a05030a3002150a05040803041b0506031807050a0609151416050c0108060609040b0f04061d07020303010609090209120708030d0b0901030203070b0a110a050c0103 75
    0x310001803074040401d0b036a00c1580d50007040c1c0701205203051201e06115805000110303194841d07414402c5050400b82d02d4000c003840c040107a108403030016080c1e82e441c1c092103008a81c00303105207241d0303507858030b4040c0c22441c48003111100f82015000000d5a56a40c400b039030140c03100740c0307d0480040c1d0b0708030040d2510b107565004901801c8442000c00061340c22000a40480d2107400030145d0403148034504803009501025456400310004c00c040c084c1090350364030310300d40300c0c45001280e0071034610600541c0d0a0004640c416444282005041020300b41500300003428400501048035002c1020002400d541c260341112448810180600d0040301603070040c0783d040801400954595418104000c200c10014000c510682d900040c0c46500794031005103210281c0d090b0001da45041e9145d8000c103480e80e000700d02c601400b9080c200182d40301d1801c0c5d22480e0489034000c0007060014600710b800d070040c0e0044880c0314240320b030300c4c0443c5050701410b1001352991407084018010581c0402c1c00542101c102e0448 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 739564739 1250 739563489 739563499
    0x4060e190b06030f09070b120a0f15180b0d05010b100c080403110f03010207110a080c090105090a090f080c0d0822060f0204180b0105090102060a020705011104080303040302010b 78
    0x1080140d601c2d0001107a4000904040804103556140c20040c5002c1241e4082ca100c0070000400d03050354600c00d10034900442d82441e05004811051780000d06582010091312001d5540e00810803400d0180c419a1001c4000300402040089210340090402d25071904240c41c00d1751954080030341c92901600e907601100981c2800c036503004268981107610f018074000202f8501c003080207038849543c0c1100a20038004010000c0d980c0722031a1070a02141026000d030726000b072541240c08101428080f0314000088070281c81012280c0ca880100001540090001e1031116501d40d80280070440c07200c518000e42d03014065855980b000f000d8400d1a080c00c101d018010001c2c0c0d841884002000c41c00a4401d002c01d6285c0e0030100c947c2400c190004040c003402d048801840001d00040d109000440841c100741e00940c00c00000341402c0041d102c2d41709c3c144101e0f0050300a44005a46a110350f0302501075180103200006142c5003148021001780c1c0a0f070405c00541d0f1011080100b00b5909014003070350010160740c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 739565989 1250 739564739 739564751
    0xc0601050105120112061d0c030c03030913020f07050f0f0c010903121d03060106090303080609010e130f02090106090e090f061501110109120801080607080105010c0201050904060e19 80
    0xc3c028400806000e04a403420901c2104010711009400c41031402d10445140c11202001c1c00406640301c11070701c0400d01a0150a91404440c039020068a641000c0600401210b1140300c218000940c0408003043c0c80310420301c481000b2030020408000d002c81c0290003001c50f401026031252030181002603960400840e0a0288001034408604c9110f1102d5401c1c480e404014240060780d20b0384801c0e510070307003512030032000291099102c074018048a01a40f03481049488640500005c08000d02895460006010104030000e685050440d402c0d406030680c003040820f150b00040541d24207910ac5400070310341104c1480f00320000c205041c0c00ca10740c00001c3c5802c550710030f1070a481c0c1c000200080b400206901850180b0790160030700d00f4160400d4402080324211618000c80c0142805a164001800c1c050011485400018a01d801840b254940704940c0c5e2030080111030749145110202c4c10040309100380c800d5500c90740a9030700900b24070401030348245010070007820312100001e554407400b07007464 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 739567239 1250 739565989 739566007
    0x30a050f0f13021507022d4905060a0f090c03020405100f030609050d0206100e07030603150c0318020114030a020c030f1c050915041707080c0601050105 67
    0x15a400000b550684800e54a01004d50a5003451700a51001a41040341074030400d491003185460400c140444403d0780829240980601c408400c00305200780b40b1303411b41038250003514401441e0707074268200203490b1008958400c10312001c9558140741100d0350b600060074840e02901c07030701403504109036125003003040300420340390ba44200c2c84510010b40501d03a1800170598110742c4440c02c1c00640400c480e0310018a1740c80c60844000c10020740b0548090061901980500317201148142c00703090360644900312242042e10401c61641d0241550090503990000000001c0880c2e1a0300d0034005803e01c0013503003201800000d81642c0604140025040c4110358a0740141e03008000c0301c1c15515455035482d10b0f0b81d21881184028400c1e031b0800760f518400483c92039044215000200803015425018020500041d02180240e6006648131544c070f4210043e11058085110402035206001c2d9450030b0110442c5605110749a004540540e41c443c00010f10749107024081000600601c003e00e13203585805582 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 739568345 1106 739567239 739567261
    0x30f12021b03131202060301030308090a0b0117060a150b07020d050a1b081b040c4118060705010908130315140c0d060b030a050f0f 58
    0x1100130954012880c80511041c1c3c0c041c0044d400d5908503542500c64640080c408012440b5038452000825030003207856008200e030f02180644d50400f0817800c1d08003c4000c0c402c5034120b0824103c50452800555010f00302c0b000c020109403940c1803403001988031908590054418401c0c0325141e4140055180141340601c0c03440d21108285959100440d2550004440024400800d40204580781170540000450584900d0500703200f145c50842039000030300081030105c1c6001d40c13203c10540550048814500c10304858000c60424000d110010b0000f191600c100d8054280421210308005094004411995108000c0e50311050020b6003007404c02454801600c252182d0f0503501c6440000b0304c0b8543c1c4007440f095203400159101d8480118a40c04060100c4880d035a0741c000080d03c00114003d140503540c10703000802c417420301d0480c980b090200500304000c03070220801408856568 = true := by decide +kernel

theorem cover : BRFrame.Cov 739388489 739568345 := by
  have h0 := BRFrame.cov_init 739388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 739388489 ≤ n) (h2 : n < 739568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
