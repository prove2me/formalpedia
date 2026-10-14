-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2133
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:44:29.674041+00:00
-- url     : https://prove2.me/submissions/2561c4fc-a02e-43ba-a4f1-aaec76f17a66

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 383453237 ≤ n < 383633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 383454487 1250 383453237 383453243
    0x1051b070b0f270609150403120e03040906140306010815041401140c070302210d02090a080a0b091b0a141906030204090522030507150603030c0519 65
    0xc20380d4690454803101da800c0940f103844003a00588110016866514107410849020001009603040024403282040e030a901c01103001c0704184100400701e904a0f490903c48845101c0c0090001c0101c00c03802d04500030364201441681c1070050000d942e44840f581c00003401300131810340f00d090366240c2c0700565405100181c103125010800028000c40c0c4c5058180d41c01060010001c01d200403402c0a00300d15003400c4502050010b808120f0310b090560400002504041e41480040340000f6401007010a00980b01104400f07600020410144e80b0b40010300d4008008840444080c44c505251030070b1003100440d100303003a92140d6881407030700141040f000d5102900280a0000007400c1c144014104007040d1000c90304450040680c9030901420404440281116900183c41d43e0903d80078400350380000d00304558010421802c0c070700031040c8820a80d070781caa050810607a01c09903031415031240882c181a00342000e182190000505810014a0100d584100140e800d60f00c840030080840701c0030b180c03000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 383455737 1250 383454487 383454503
    0x20315011d01031220010e0c120a11060c1603321f090213060312020309060f0a020c0306101d0c09040c0215190e150106030e0f0109050c010207050a1409040212010e01051b07 76
    0x9070bc3e050810040590000380402da800c40b4004410241d0151681c5d0f10407500074820703551800f031100c40d1100401c4500050108080700003146d0751000e60340c0e102d1000800c03403101300d00c4006010710070940c8910500703a4080e0400903070000130900c460060006210540d00c142520f41580030351440402203c03102c0c01d00030400c1e400c0210402914619400625408055204605080c03240f540d04100f9280700e40034404040b80401c0c14140c2410240080d80320303064102d0b50308414040608480015a140007030282e400058492307050390102c0c0b90420390b01210708491b00903c2441600c403036500c0b0703205030341e80042d0f000d02252a0040045d6690003680045400c106101c50061041e103100380c00112440500c01e045528006030418100e00310f804c0c10004442d59803110200c3c1e8400d58040c003c00c80208002c0311007044662800c00004940c802404044d44034074985800a011940c4003100d22003005c42800003084990b02c0b41c03069034020b1801f621195444880082e2078a1040d0503003089030000c03940a205 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 383456987 1250 383455737 383455763
    0x8010e0402040906050a09030f090e0402040c0e060a02010c0f090e060d05030904150503120a050d0f0f06030605061801050307061209020315011d01031220010e0c120a 73
    0x5601a00281040340d1003070b22a22444045802405010b0165400400c000303200d00380b03440c01901ca0158620340c1818841c1e0901c04100748022078070710703036403054040d200032138060302c180d000300c9802c010b401e0015880140070480054159055210000340c00c0141c4490a1550304d10710162004030040c4134105c030404840d40000c03e282030442080d02c4c1c00c2d12900c1264141409000040d0640d02c0b082c0104101501c101001c00a528040080841c0c2c6241c41030003500e064130700c0c0d50007800c5200313841785d103070f05941c588003105900741c2c09e13a006500122204000b04507058072441c105d4080c1900f911002e1190b10380c0780d40480c0b640750040038503040791001402056000e142440949042802d02000c0f40741035951202940075850611101003520701200012103d50304003000740701403121001c5850301122a40c0018030008041c5004c1c0c096005550400c0d46103010b010218603000014840c1d011182e50900e07a0900c81c1c5c41c40026410781020301100c105025002140240b0b540300d901c11009400c401d01c03409 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 383458237 1250 383456987 383456999
    0xb090607080a031b030b09010e0106020d051617120601030608071707051810080c010903020f03190b0601110f0a020616060c0903022b17040306050907240801 69
    0x4018140c2005608000c00c1503008400b84150000030411340ba40466150a40c0c2403840c038040005901611411010080c035504101c002541c03098100700c6036007072101c002010640b8145030340c41615181d030300040440b00309040f800010125003156942000c11401d007404100300e503009000301020340e00ac000003010340b1b034a05a407036040888850308a031458041c84078003103041d8403084605030710001c441d82946402d00300010408020300349035100011941200c10701040c1a07034030040e19421a41c0450b00125100904c2c0002400c03c810420207004e41c0c4000c0100c0d0301005101d40056125050980341c04d40c02040700660740340c4034100409908002c2d0031500d0008014030f0200081c0070300c00b546a050061251030355840e01d01700c3d800c001d0b07940e01203508640204110301c1d1009028038402c01000040001d00e20400007000000b0b512030b001001144048200b141140703143c0142c0e0011504598184854108003500c1d03900c419260280040c4c08482c201d050080200c031481f92503444181781d50341c00c2c03c0c2e882e002c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 383459487 1250 383458237 383458253
    0xd0f0507020d1d1201090203060106021908030a0605060a0306141c0b2e0317122a0d051e010609090c030f050403390809040e0a030503010e010b090607 66
    0x82109401c3d000d4035903445141c440c84030031031810107403100000303500f2010300406142030343c160300a008560205142e040040c20088803c010075034040d29080c0c907504c410040b000a400300fa04900e030005c2010544000f01941a00003a040b20303d45807218841981ca8001d100085a4020b411031a11029607410000506001101c9511122400c10b01d8840100b00302d415210544c10740b40050150400c000600a004400c982d0300b2020703d51543d514a0076104000c0c00d00c0140d0700400c0301c1aa80c0c00381d404a01e0b4800e03107140f0002c03201009512181d5070302d28891084011706082d2000c80500311001400c9002106585046041e5101074903a03404107440c2c09620000b8091701040c02d0200360312424800b12039901030183c0c6004d64443d845100c00030601e60144019002185112004103580070f80d981c20107140031030702c4401960800d40c150740d500d25200114000c0c0c00a4510000248a400c0f01b900601d82d000c0040c44c1a241c18200c0e151460f40e89460807000703401080342d00d030f0f070140082042c100020000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 383460737 1250 383459487 383459507
    0x120a061208130515130603060f050613090204150909090201020303061e1009090b1e040c090e01030b0103201e03010f1a0109081b0f0a090609020d0f0507020d 69
    0x1206035650302c82e4076a400b00300151800c0720207070a0044041810300b01d0500b0310850700c0181c0300500d420812981703051400c0e4402006c912800c0d0140070002000c901c1030b40d24035440c501402400006541d03540d6500c46403080010501d6807540012200e910201d80a83d060045102d55034050b801941951a0001004420b008454076848041900e08170410386407a08403560b20307401010f031580e034007079490440c20a00303850100c0300540c82095010402c00414144090381e00804d80c0c00d4074001024000c0324010340e07040c0b072260084008a44160000010030003820203903816248164402c012140081f03002c050948040b940c0f0707903800a4825a049035904a61b0180441c20000400200d400c1507a441000e0882e00d03140f0003904083c030404501c540301d50300220100010240040184100482902813000c0f0048002d02d036881030440c0d17001d00fa80b80e41e4aa0a140c081e0800107010030000e0307682e80c0200c0080d403242c40603c0005080079803181050043d1b12485110310103e070050804e01f542820100c1d00d0320300e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 383461987 1250 383460737 383460757
    0x209040624081b160b070f1d1807020a1a070e09010f030206070819081512190609211b080714030c011107053a0302090d08120a061208 59
    0x54440c950021601a40040780a91845c1d21031f54502c00c0b0100004140c01360500707c10610081089103c802502e43c0148404865000001081e05445020080f410b04c401c114000e008040c0141310180e100000c901028024038107a2540190321030010103000c207000702441610341d14054040200050b080041c01007500d00d00c41e540207842c11003560543e6540c2c490042c030750000034412030104201c501c0394014042e00254100c4145140c0030094201c140c1e80c5034150407240016111440000401c6015084441d65651007440c8050801441c0205900e058410003548006612240b00140d1064400a01004241c1066900e480c044043d00c4041204103980d0074180d041c48100f00e10301c01e0480a00c11a03030811f200a91722035940141c0c4c00c0c007614111414a200508000b0146034034030441e000c0b0100000d000c4015583c410507144004207400034060b46050680001003c4101810032520710014126840050781d102c486407074400c200d030111030640c000d10010200c80b10660001c143c204004d8000014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 383463237 1250 383461987 383462017
    0xb180a0c0e060f0f0d02040905040302060603011118120d020d02070b07020603070c0f0206040b0703020c03161214030a0c02130504021e190314060106020f07090c02010209040624081b 80
    0xc2c030296401c5c100e91050f03200d00b10b6035556105000030564140b1905812034002c40c0280301c0f8a259035000c00f210712850b41c8210720140b00003820040e603180c0c018420390480c0340c40d05450102208050103034685001110399001401a46d40108011403250180d4169540250250341190f5840905a4001c100101d00f5180038001041c0d0b03400503640c0800074000f44c102e80c4402911000c452401a25108110800702d100e500100d8500300601d4180a92008441c3c2d1010520b60608284c2040702141c03a4400341c1c031500e400001003079141c1a8100b0030490131540301b40e943d14050308003088620112042074600030750025030128044035a2015a2500000c1c1e2001840210310b09000c401004e10014164821610041d2803c100280048144509401850f40703001400784411500c0171030352034146a00030004c0c4980e4580c84507a045100350b047c0c0f510884040c1c4200042c07515542d14201c0c41104485070103603804984e0348019942c0c800c80340c45003d00b0401700401e1855401c024070a9642d00f0241030421000c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 383464487 1250 383463237 383463247
    0x6020604081c063002030a0204050c0c0105100f0e16121103090c01030b090c0702060d0b09090c1002070501050d020f070b040309090507260405010b180a0c0e060f0f 72
    0x1e40c0c850300004240c142c0320148000c440c4100c108500101100c4d0001c04901803401c0e40c00750f00c0120b0401e211581c129800105075446204841c428012140083d500c0d42c60281004080c20032404008190b84440c2480c110441c1c0d102c180c0324000c84203c0300f0040c0e02c1d1182240b01c440340d024017000c26280001c204003050780362200c2e46030340701038000700c0741e2020560262942c403002e940c052181c6003d5140a44007032405241500e050b000911403030310300038068100012a0105406158041c8000500040c90300025050035100d0070b076214600c20180e031060409403420040a400010311108840f4107031181410440d800c17400200a4215020418a1007010030400c0009607429200c9481288a91510041c06041a00c806c0442c0c000804c0b40303040c003100e4010b00c044e010249100c291020310503100480720780c1d118a03285001d0140840d07490307044444248281ca005108406c01c0d0307c034401c0b04070200305000341d03110b0032034810395511480b6412a4003008001002c03607221000b44034000f201c544982c42e00c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 383465737 1250 383464487 383464537
    0x1308160312020c07090b060703020601230406120201030b0603060d020d02120f030403050d080103150221090114091b06030a140711060901061a0c0a06020a020106050a0e010602060408 80
    0x41da0000d54000c0c072a4010541c2031214080601c1a44071b141d00503a99103040440f2176901944d6034406018a5440343d200101105420700f1072001e8809200d8098414480c0f940d44e82c0d107810016040c1841240400e04008a9946600f021800c0e21302c906070003440a0704140c019028852108280a8240c0c2c00240340940d002052130208640001050008010b641d0365145050103400e000e0440103040c2005000343c0100301050408091031080020b40c10016502d20106401015815600c1c4802d040c6501100802c043d00c4810b50020802d0f100200000032143e1390034a0f10b640301c01a80403c41c111001c00e1400c0441d604142c0065980104000700015445580d80003282c070800013250030f480080c0031003054403a866014841290003e081400901403d0f041a000750a0701c07005604c08403104401040c00800c850007045000c000c66040701c1e0842d921698540d00070701900d01405643e0144229110002d2400e4038105001d04071840707580076041c9500c42e139460021a501c0300501c884100b154060903825 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 383466987 1250 383465737 383465741
    0xb01020a0c030c06141c0b031f02130504020c0a060e0a051902040f02120402040c0309080f040e070801080a060c110d02060106140702010905040c0203071a010e1308160312 75
    0x2a40c0107000c80c3e080145401d0f8028941d40d181281c0c524614400e00c003142060a00442500585d96050300100d07a03a0403820100b441c25805140003200f1a5018100f00c0300c2d00c0c0c2c141d00a010340803290050650309519a011300050388161602d03c1c00c0ba138410b10501000c21380c194400151003420b4001c1cdc50000c61a51245440d0080c02c0c800680c000004404241c21840c280c0700384c04c10f02540030829424030f8145a03000a00300c9004001038001c42c3c85190f0418820b2080d07018404443e484138a40f41c0300d2030140c1a101590300300307000300200a411600030980e4540140c440504983e1884003c3c00003e60a43d1203802030024010a00107014001030040d05904040c41810807000140e0700615907503240a1004110300d08910049000590400281000d81d074810152070503070f101074502107440001180228918440c6260140460805403030183c00d814080203250304859401c20f40d8030103601c030343c8501448080d03c0840203100ca14200204100c3c0c0345000c06013070300c2c18003900703102000700701d0003402c101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 383468237 1250 383466987 383466989
    0xa050f100c05070b0301050f1e010c05031e07020a0501030908031306060b1207120e0a0305070c0504060602030a020c0402042709081b010e0309012f011a030d03050f06040b01020a0c 79
    0x2e00004c2c080700501840c2090340c45188140c004940000e41c03085c2c0d0000301e110150300301c18000d040012007010395081c84003c00841d4625a420f0450a007040d62240b64a120344d00b0246049100e564442c0e0009104d40c801e02881042c01d42006005256440d0380c5030885102c1440502240c1040d00c80c41c00140500540000d4107405100c491846c2c1d282c905107800400c1c25005025080307a161412102100c04540043d1a0001c550b06040c0340fa50b40b41c05013030036640d8111a600103a031150034618081001c65000c030140904a007907030200c8003c11504070800c0184d0040e4010041ea03110704c0d29041c1141d00080c912528040181c0000094032212071b158503040f5840000d140e07060316002861040c44030383c24800c0483d41d1011001071814600c04e01c00003084031610306c1103218181c00c040200488a0590045140c1044240e8020081d0701000b9203841e006080c8034629174403d0051003c840a424041d004082c4900501c1d14015007503620181088018040410070604522a040d5040700003521806014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 383469487 1250 383468237 383468249
    0x5101b06020406031d100c12050c07200d03030b1801091a031b01030225150e0115051005040f031a07050a171306020a090906050a050f100c0507 63
    0x16035181d0074a000901a1481c110b195844100c0300908560417100114042c203211900748030100d02c800b2071100444210402c02014000e1904e00000e001440038814024101c8500c24040c100c501c08000905031000304117034940c903801c4807500c5158400684a50704c0700846140c010440c3d1204016a130a0340d40140d400d0b00440303865503a03030015401c0144100c81409211500301c0050640340500d0311fa920624246181c0310381416008603040403240c20010f0580107860600706018007101c803600702082d40e03075500f0b42c201040da80781c0081114440b4043c042d0951920040303108600c120310b0002402504070000010744104001800003280c450721402c0d8000c001c5000b088181c070760304102ca08802c5104400b4020800340a0b0400c440c000854212610071160a43e00c220013280d41e0300c11501450f40c0040030740060002e0f1000402e1003400742c0120704801034131070358942000156280e60500070782c4011406040e904c00c8512080e5000e42c544034100030044100c0b0b20300041c2c1d46500744d90b002d01d0410160484 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 383470737 1250 383469487 383469491
    0xc021633090501090503190b060f091302040c090303020a1b0b0a0203070605010902210604020702060d0f0605032a0d050313080d080c160302160f080c030303090705101b06 75
    0x100b0a540e408032000c00900743c128040e2a9058043d950718200d5117806000420010f90b41c400150a66035450f5180302c1184007921012480c600041c0360320743c0c0b951690040f0302ca107240500d00d210161182d8090307000e50340d00d90000d1090100c2501c940304002c0040e400340030a4902d205012481c00100d50140c081002c90b50000c54941c40c55140c1202a80c03c160001ca0606105108203040c24401d10084101240e01e000e54500c151103003004900a4030811002075006400090400348104203a4054040c494115a003084140d0f180c170101911011401d0020310514655150540310b5814045540388201000b00340c82c120030001d517109400d503000101c8010032599103500400000e1428841c41e188140d8518183c001403412103a00381040c0164111060b48001400321a02098020000d102000400e980620b40d40307983c60912404030f04444c0201482e60052143c0d4003010304000061300d01a101c1140902502c030300301424008a07900d0307028a501044082c0304070550b182e812803201d04005001d4180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 383471987 1250 383470737 383470739
    0xd050a0626010515060301170111040b04030210020a03050a05090102011806021c021e0c0a060e010e07080604020604141f23070c0e0c041d09010c02163309 68
    0x5803a0856030020314003c040c04000000c00455618081100e054540c3d043c114001c54800b10f04403070050010700384101910ac0e0001d00032811a0340000a80112842254240c0402e01701c4103040b41c03903200d9280b00601044050200180050191014021082d818800016003294440309002c2c03401001c441034a804c1d41c0010045803064001c1d50669403580030250942c505018070070011072054035410815420540403034000b111910071300c050f228168001d9014440c521442d54558001d0040c0c11010b078091250510014200c0d00c0410b0b614483ca0300100541c0c2030502d45034440c075941e64079001041c0c2c009a14108180a505282c81c49452224540d65040c036003915038203401103106c007000072402c0200c030610015001179680796042d81030301c3ca000340c0d0f00d903182c55070040c0500c14051070b0040d8601c049000d201540685d2220717902c5209001203402442505120791041c0e0b281d0001c1411040c500c0c01c29181808001c404800e41222001d104c20400030410a83d0740c510102a180103111000400c0c1d030300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 383473237 1250 383471987 383472059
    0x605070305011d040303021e2110050f0405040816050105070f08160f02010b0d03020a0c050a0b030a0b0616120806010207180e0c040e0d180b0d050a06 66
    0x1c41c96015102219074100c1800c0064681c9100d4040201300804054002510450011480d060407a8400540c0109620b5900740290460406940c0b0400d400c91101880001d00c50749045081c00c0c210f403006010621007143c078009002c00b405000740181d40900b010800503e040c0703810a502c8440d54000c1000080ba400e150100605021010556004000203202404110112304212403864200e40c20040784041201009074054500c0300c000d9a07010810134052400d254012903045902c603c0344070440d0b282500c50003001140c42c2d00c2c1c042c240d0418020300000d82d52070010f50040450010080103076041241103029254400103200d42111154542c00c0045507140d0001080d9404c40801d0010703114040c20a462218006180705250700b464bc7c990352610045801031240880d00032014200b8003500074900c085903034031058900c504c40012000809116042c904c001000280c800103c01c0303628010160079000060680901075116407682e50900151441003065902d8119a008010844200c02c482c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 383474487 1250 383473237 383473241
    0xf08030103051506090601231b01050a020427093806030d0f1103130f060203040509042003100618050f070f02120c0a150c0c17070203070306050703 65
    0x380900469a034001c2c144403d03030303036101441c562201081c6055503035004c0323040d00b405600e1054603080c1500840014112035009810720f501805510042c001d1016803524602682244200d205015250128440d01e041c11100000c030b1104001c0c98a602080d0220b0580303903c040f0440204e07020b480d00c40406c000100180e4243c452011100362003c150701580b40000c00b19850302c0100b4010000c10885452040da09030103030b12071103008804030003180d031590001418100c01c20114020107e1002d070940f00010514800400c41d4141c60026090060701d88640c0d40d184140d5030302c504071006019085555051945003004044c103030341034581c0c0205140f0718244101141c804260444c603005800c0a042003450b0030040305103901f0854a151400381d918044204904104483d010780442d03080003c1c955081040c0040c071402014040c03a0710a0501c140e440c1000c04071400950141c0104485420810218603040c0c483c40101c8080d0f040d2500d019541ea001a080c881c9070b800c1221516034590500c003d80da418 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 383475737 1250 383474487 383474503
    0x901020106080f0a240e0d260f2a0c0106050a0305150c0c0d020c0a06031505100c080c06060f0a08060609060111030a0306091805060f0405070509070c140601141c0f0803010305 77
    0xb10014152324851a4500c41b00c10000500001c459019174000c240440d2084084d0040302c40140f000f52a08128000086079030390080c001d002c02c56003040b202080701d2821480000407664400c0040c1040c00c1183c40101ca0355500902e000b6400c0010321400105038001c0c4650002e8110507405450305200d02c0042262504040e00b2000825280560034504202c10240b8141a51402c99141c0580044a2011150381405610040c0703c0080802d0040489800190550044800300c66040e004011074061003031440031441684003a50100c408902582003110000342c204c54181340407449043c800b80000c1c0f86034800c600c10400650380c0c85041215100720303c40c214142c12000d0700068078034199140e0b0b82d6145000340802c100c103400d440c04101085010003803440241405003000b102441c003248058003403040580151100100b1903240034500001059040c117aa1078080480040680344041c41100c2085480070000030301c0c80000e15000c91003400c10000c00e14070070078819540c0d40c11440c000b0300784442 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 383476987 1250 383475737 383475767
    0x507020c10080603191a01060f0507120909290307080a0b180604031101051333020408061e04020a0501050f1b030901020106080f0a240e0d 61
    0x11114410050391a0180715103516658a041c14007038a0f02000a41001c0d01c1110804046000f04041c034200620500c45043e000c3d800ba140c1031242c1c2c1d0365002540c0c2205a08090400a00100000c4000882031468130300c01c10414030b40405650340f210600300458048003010310b182c04000da05506403101640701d1450800081d405050058075003000c0680e50020040020b0900c01c40310006060b07500c040c01c0381c110384100c2c0b8080b0303401d1b4200350038083e00080c4182d441031003075402c01000901048645110030551369001c031550485a40400c41540d60410126500c50a4589a85450080d180e41e0015001500e90440a80414140b5448800c440350035144613880c0a094401040003603038071108502c0c00c484082c01c0840d07482c003450517001c0062042d11802c00c04040d80c042800c60842e00000540304090f420b8008101c0c3c0c644030702d0680d40d64548841502915071106450b40d002400503a20450707128070504160489030001c40482058900500d9040c0c03540c0d110b40950042170f03a000e9a007058100e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 383478237 1250 383476987 383476993
    0x20901052205071124010b1c1505040f021c020333010f090305060708060d06022703150a2406050a02010606140702040902011b1a0901061d04030c0c090f050702 70
    0x50141c00d0614050510602c50701e50701c08039140540c8c044140f006800110b50b68410000d41902c10291000c0303210500406000780c1c030308a14186024540d03c00c50f00200504e05070078072101580c083c00700c069403004000c074039400c0c44c0560f0354021200f070026012a50320b41c8030109003150030300000100f000903502d074070304200044618200b011030408100141c00c48040d140544855550a02040b100b0b124164010042480003d00b10080000c0740c03910811407a550304944e0440c080300341010750740c0040e20b44090b500761801d408103007200341a60040c0c900306004074001d520681c1c07900962400300819840603011400005101e00700650a1041e5000340c15542404503030180c96100451580c00361810003801241da0b50b0101003960b00403003224902e0701070700000a07040843e42c80c18409104980d000600015050404650140018092072082e59100085102a03508019601606840140c8198213000c200c1d8035500108400b1010368015003211440815044045084a000c4403801094842150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 383479487 1250 383478237 383478283
    0x1080114040305030412021f140604020a090506130504050906010e0601030c200a0b091b03070b07020618030d03320a1e0504060c0f0c0209010522050711 67
    0x3a0448281c82d01701c0e4002c82840101502e04000317078239200a400702c0798826400516040c00300d23840345d004007001020000201040741c031003500340000d038051510420081003508130180181e08100020f0400d0584070700150034516a200e010804503901510300a84581140d0010701044261410b040c0d00a94280313003c00032000e074400020203440100040d1540c0001050120040324410040f550480b070b00708803213110a060048080e9681e07100b0700f076064440c5907154008801072401042082c01c40301d40200991400583e40c1c00c000c025030000e070b4644c0d101503500034907074410344041101c902c000e061134400040300c0343c0d150100502007085160000115800104014804221001664000c090240c0102c0c0c0c4148080c40d5500c0c1101c0c0800c4c20741594070b0002044180f060641085c070090041c3e0301c81c881d1800840808856044183e10080c5d0842c2215004008a04240c1400344403118003450001c0f10303003500143c0c0300039124151060703000641200c0902c415510f06000e0b4440344a050703000c2200701 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 383480737 1250 383479487 383479493
    0x605040f030b04030201090b0711150f0c0f040f0603090b0f070906030b0d0203011109012309010f050910030501090c091a03040f0b010902030708010e010605090d020a0f0305060108011404 82
    0x4080d90000820044640d0040380405000b500034801c040da009601140d20b1804d07402c000c00310b2101c91148100d51150303403001207500004460160140400c4541e40304141d41d2100c0c110816840b500380420b4640041000141c20780c070a800d006c0140407142e501045403450707400c24032207455000c1c02030910108a84c0134841a01e800450300382c1121014100802c40c00511400500c0707804810340080c1d019402c0c03410310500d01120340004d10345544d00340c0f5079141c540800708005030202406030400542907001c000b4506c0560007065600f00003900342c0790883ca403240d50001708050281080d10030b4040303511070005003c502a140074000c1100818580148400d00d80002c02c510414641c803100307803130480040400c09010343c1500c1d61030f007150440a02c11082d695108134100030351085500000113044a40081183c22000d106d4604031075503590380c1410410b900341088400500404203ea00004a11000540d50a00148070000b140600c019204941c98034040d2400e440f916030b1844982e4010314100000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 383481987 1250 383480737 383480759
    0x1020405150405220b06210a0b090c0313120f030b0303183a12080f1f0e01140108090c0a18020705011b020f16090c091a070c060504 58
    0x5001c50702c0784000c00b0944c8298040d0010700341800c0302078114400041d464244000d2500c00980d8404602c0c0054069503040c40c030340c1c210f03512101041e07400078440d000f040200c02400d000e5038029030704030000b29214849075120205041600e80c0358010490799807000f42c0031509403040b021545001d8001d103190540c9071111a42d40c3d041d00e600b0700c0c807031344040f41c400c1e00c00380302580c501c4001519030901050306c0f840c030031160070314a090400880f04104040305010040703210f600100c7c041d980e00801c0c0129910303070418a034407001c0c0300860300c000404c0d160780021350540d00c0080d490003082018152041844003000061807000014440c1840e036124410100a50726404030241c100c80c241403421401d180e03c5d99810340a031055201c040c210350309102140382103170121414020139a00f59001c03210782800c001001e13911461502054540003100c0c890421111745190000e070003080c005c1c50124030480e103c405a01d041011200c40b02d00300680490302804010003108401c02420311030a0207410945840c940440d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 383483237 1250 383481987 383482009
    0x403032703080912030403080a0e090a0e030301030609050a320606240418050a0e0c010206150a0b031006020c0910030813090920060a0507060c09031401020405150405 73
    0x405030b0210502650480400e000b81d030701559011807100d03554510b1f09d0005200d0410110f04510071500c201c007141e45001c56120340c03040c60b903000e0055815603103191540402081764038026500c5008115000000921001036148100500b5441c14602d09121484003c000c08403603c820480d17200b03600b800000c0c7d55220490007803082c1401d9446543e6000302848203a4051540000b900381690f034021988111680c00640c403907070b80c13100c0801c60100c400313007015581d2182400ea1030258102c01d0100348018038107206060600b41c080c200340207607a40d40c0303110003090344102c0d6801003010f0354100c02d102069042c005007420201c201c0b0b150030070f4242940110784004407480001c0031400002002c84103100340303482c40707001408407803810032000c14107041c01c003c03061004c0307030f006004018140e0080503446e21400f1765156804560b90181462a40c2d80c0c0d14000308461400f02d414044a100c0000000c0c41580f504003100400400150302e807442d003400e1203451405c41c0095080520103102c1840107803107180480c3c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 383484487 1250 383483237 383483239
    0x151e0207020913050f030d020705150112030c0203160b0d0c020601050102070902071704080c03060105041a040b120102160308093f0c010e06010e150105030c0c0304030327030809 78
    0x1d101c1d01a40c1c541300385072010380c294042650002240b10720304810700b94040d00f222409201990a680841c0081641c80102400307a800d15200760304189010030700c61890b20740041d202404a42100040fa11102451456580322506045002483d9003825000d80140074241400d4001020107505140010751641e156025441c403140c0c3c0071030010b0600104452448409048128842d95152a241645d0302d560950203081e0185c42040c00004041c20688104174070072027000c9841c1840c0d4403c90410024005510000b07500072690030400c00030769800c2c80141a1121103803404440c02089240241c04448020048070881d001130068000000d061825049501042086400b103005591040b4048042403102217034500381c08107000645d00015400703201d509441c2c004952150f030344c07202004c3d22400100e50301204041a0341180000e540148061134108400b00c080c1e50a00b0400d100707851451300154820380026091074820401c03640f07075002c0041840c902e00c64441d030080c215218000342d4400c0c030341a5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 383485737 1250 383484487 383484511
    0x604080d2d08060301140f0712060e07030203180d020a0803220b090106292a0d030507030b030c0111070503151807180b01030603151e02070209 63
    0x306252000203001c4800302806407150510400c0600050040ca41103405500961030720040f0400b00c40c6407515a8480d4410703416041c595030b180401120b10070031440b50945450344407240800c0e400c0c0304409091040c051070b5001a03d0303141c1050b40300804441d10321003a40941080701281071050f804901c20990a03040300700255640c80d43c1c50054030b80da48800c0f0000515000c49204010400c86202d207e02902e102d034006e002460b11540d1080c04070044904032607444030f07420700703c000c03401c0e0a001a00420f40d580301c070341444030130300c0c0c240c0c00003061100494042e0303800800c200b40009415205480d04003405181c00c1040030150f00100e9a6803040d8030103181404001c64104209180c01c100e80d070301419018003600c000c1802c0e0807a02c84111350558820031030b8580c011010403043c20002d009011110400030541c058020a04101c00808442031864105500c3d1000400480d040000304460003040c83ca0009a1240304411032a0300301001c041542101c0c0108540c0000da51680030729604201d042282e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 383486987 1250 383485737 383485757
    0xc140307020d05160b040f050705030d05030a0e030f0403030201060315111206240717161403190c020102010506040605030307140123010e0901051e041106040f03110604080d 76
    0x200711050130f0079803000300181c6440c000c00c401c0000c1c01e08140343d598829002c0301c0d641034481082588640d0800b0f58607001600900000b200c20617540c212250f140300c1e00742034a00d0f24140100c540300b9548142c00a40160f0f443e14410000c00c0403c1d000e01464045558041004604001000c1a9403088107240003c10340b9800100380c4a5950000c0c1200000d0b00940d89020b42031184e58540303854102c4002543c0425000c212b201c5446600f50403580c1294990619240e6900d040c0e540c206a80124907541035648414424402d140c00c0505000e90803c6071760b2203132181e000d001c0c400203094071001011a0b0266041003410040385d01c0010030b5030702c0c00ba0311007022503148210000c941d004107084400750344074031500c006050700c407840c4610243c1a03c52600a43c1040e64900e01c0c070b9403e076002aa070280f20021103000c420b0002d2000884260054492040b550028200c00b000a032260425049074400100301c071000c2040103100341e40e0050903642a90500d0503d4174040140e81c03a1070700115201c0510943c1a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 383488237 1250 383486987 383487007
    0xc0603160e09101701060621140403080f1b09013c02150f180a0f03020709061a0403020603040c09020301090203060f041a0f0301020d0204090c140307020d05 69
    0x200d841c0c41200050100d4203a440c1001e440e807075100c00c1e0f200300803289070613045a50030740034180907020580c0c6103611880d0780884055242d10000d003008031401849984e070707002d02458000d4480d40305d01440c001d2b50742ca1401e08260040d103415080c043c01c4e04000c00459034100001c00f032090300307030344044409080c010096110a51041200042080d40c000160a03624044c184414060001c100c4006a50f08484012000104442d0256015102d41e0051000880010700c03206003403080c00c1a00c3c1d03040d42036500c402542d0351031010f032020303404084000d43c00c02401404a080d40d886040b000305091482100902c0d50450a90381c24441e9000207405841c0c00030000f000d0200640700c8400604a4070800c5540b980c0d01ca40701030007900182e80c0a403281d9000841102c0502e050301602d001d210310b42103900d0883c01038a003001000038640301c003142c06540070701440702030841a10160000340b04e0f540740031500d240c3c03090000345141580f0400880383d00d800d0003801100c44d40040c5010b1401c10605203169074440c990 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 383489487 1250 383488237 383488247
    0x31b1003110726070804030b0403140a020114151f140c0c030105061e220612110409030f03021612020a0b090c130218090907170c060316 60
    0x3014000701c4640099002d04024814003200d5a00c07030b4040c008031928941400460fa41d2103050400b4005040521061001c1802c0030903980c2c01c1446810410f1401210444590f560340100c841600035075518a0002d0001003158402544441215844030b002c00c0d002d40090360510380740c0b0101c1d007030844240c044d0800600520390b21030603042000180d07842d4040416095a140105980f1500079401c0c040400c50781d007802c19aa60400520b011445100c08540d41400603416014103001c000402030740b405043c2100e5445100d001d8440315100c2203200050b8244003c15407824402140640d140240640200e9400b070741c69411044289005a40c4842070180e4403010b40341503001034030840d500d20030000d5154000400e400018482d03e0f186240c0d6445d524465141c000c0090701c03540000c900c04868aa019460313008044440045103c0d4802c080c5410216500000498032000305602c81c0c8010300094801d605514829148000104404803840c40072824a00001c1c0060309a103800082ca01300ea50302407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 383490737 1250 383489487 383489501
    0x1050c12070c17160f0f0905060f1f14120f0c040308040b04060f020106291903020a021002030106140903030d1509240e0907090504030507020f031b1003 67
    0x4034094070f503008010409070b00c0d43c1002c01c07142002420300b10b0015441000e202c0010848240d440c003c102145403603407400103804000d004a900a80c400c0031050b4940e5010b000210155130307040007003100707510501c01401c45601205035034007400303041c070150185424190b581544101c60001038460f5449080c40c00410380101d07040146001d0010601040e0103121401078002c0310344d00d43d151680800c05010990072200c07103000703103d0032500002000d0700c0000c070031034160840c3d80d103440d855180001c0701426400c0020700b0381071100001d40000700710078401d038100001941c05500340000c503e1540340c150301829041840303051109503030022403449600c7c0d40610a484000c40d008500703204583d149009a84455540d004906a05c0d1a114515000c1c45c030280300154940340303200c400d1242170b04280504000300e000819001103403181c1c040203d4444454001d150040d40f007038403025101c03a018410000342510640d5803074060340c4102d40c03410b1124500f100340000d1200640342c400c161641000124050204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 383491987 1250 383490737 383490749
    0x6031807031403030403080609040b010b0f0f0d050103050c0111031e0d090302160f0305060c090a03050d020a1703070507120509033a020304030809060702040501030f05060601050c12070c 82
    0x11040242d82e91202000a61146220b03070ba4280d250b80c0c81c0c03010440108429900500f91800f800c2c014440002d00c14010400800d00f4102503007040e94a03540044942c3c04013403002c4410340c9800c010001c11108000c1186181070900700718400e00da0b19170001d80c1c0ca00a102c0000caa918142030044417507a40b900444051805064041c42210640d044c0039503101c100c882c3c14448035240600c0052380d550741d4800b800560360310901412036038031114038081d0b840e084980b14650100781d00345d000000a4041015200318041c03900a400942521b0174829a04584c2828141c1151010020012090342c0b0004031030143e0313440f0103040c1201104150444050194046554141c401e03031820000900043c2c8080411042c45404c80d5004003410a000c98040503825815016a005010600c0011402d1000e051001c9006e840e0314200758654000405448007a4400c1d0f0f00310b000f007994601401700501ca161703132000c000e0030714a2070620207960642c2e484104850034821803202107016410403811b08141002021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 383493237 1250 383491987 383492003
    0x60a1809090b0f011a0702040e0f0307150c0c020906041503050607030f051f0b030a1112070e0a050307050f06040506180a06110705040e010b03060c041d01050603180703 74
    0x100e24030b000c10b50080c040c1c40070f16290503d1800004d401505048080745040700160860401d00240d0074000a0031251b24403042c82e014030240d00c00300306001c00c0504451030058400101c480c08000740001110040405841000802000c441c0541c680a80b42074001d00c0c141ca0008041010345201450071201da0002000741c000c420038043c1c0c041e403503081400b0f0000610010806901e5103034a0001e40482d400302203185451342c0d40100709040c00c40f005190300903072021011824894403d02d07010540c1c40a00c003006404000814840a154800890000c3d0304091303518442a500300030009035998450b01c120f42c4145e420308000e080302d48607a0151001400301408941d15a207442c181c0440305003191274402d00400d4510b0b80003c8492280081500300398000f0040e181c0340c0c0c14402400f020305541582503000d0340d00d821800703480d91800c000080c843e071415000152200e003059180034402c41c43c1000c507400c0d4020040140101d0f41c41d4000c582c1c103c480302c40b0f8001c2c0c41e03000f0540c1508041305a070000e81489 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 383494487 1250 383493237 383493251
    0xd02061303170910111c08100603020712050c030f13141801090509010f1b03050f010e0402102a0210170a0c02070509010609090f0e1b040b1002030d0608030702060a1809 74
    0x7c3e0002c0b02140102e160300b030101c1c010f6458140480c201c0c0184a40601480f034410110340000340a900240410b00300e29055902d4403c10004d041c0440c1d0000e200c00c1c690284160041000c5a60074500740e0704d6400455035420048102e8000000744441030150001c043d0780e990202d16074034001d6100a41c0303d481440706104500c580c0305400700004008034083c000c282444001189071886113403085c140c2d0201d0007640d0f07190b201d41d020710043c0c42c001500941030140600c11850181100c14014541c01068140d401038614148188001022040307559400e0003c620343d458142c285a0140d950b001d40c5041e40040c048141d03203012403500c02a40e00032130f040302290002140f0141d101ca0042c00303842d441d902c00d000140250041d44100c522006080f9510741101e20b254620303c00d40800500781d014000c0c404241801c003076000542d10100c1040301c10240e0700014002076148098000d020041803050051401c010198005c291184074414100c0c0820081d0501e111510616187c000060000d44400f00311075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 383495737 1250 383494487 383494543
    0x60605030105041505090408070206070209090616020607092705090a1704140909150703090302060f0f040201050c100c030e0f0705060d09020d0206130317091011 71
    0x40d8030038020300d400385060103040129181074044a0040f038401404802c1283d81d40c1e180c0d81780f42d401c0044120f0703002d50304210034000b42c1d0752005502d004125041c01742c000782c1030040f0044c1d41c0d0020102c1040030354100c10204224160801c644904507900c5c42a035000500341829600d19080c41c000e41c10307100ca443e02040c0405140c000404c07400c060b22854a005807415018010341460007180f14005d40d00902d08010ba05500f085030b400e54004040800702d0305040500403000c1058501103820400180d51802c4100a065040020075040f0030700d50725205450034445803028030030780700130006030501100060781600c00404000807144400d00d0401003283d8006c125004000d0315160800040620130610140005840403400c10201d5000400c0b1764640000480044043c1610180581e0b1052001440f4405031710360380d0007081a0107240c810a1415030461600b91902070100c540c508071814240032014a6407129808845100c115041c4442411200068145420180c0b01090304001024000b00f40b1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 383496987 1250 383495737 383495747
    0x40603050d12060b0a1103130b031e0103020a050409050a12020c090c03070905120102120a021b06011d042102010504030801050103020903031c181b09050621100606 72
    0x1c10640d40c0c0860602544094405880d2107004190070040100103c1d00c1050003425000c01c5c80e5030b10004e69050084c940e404140c060411f602940c19100c0010170842c1c0c1c0e01511511000c480146040c8000355415600441c481c015540030fa5070046070303500c4d80842030060810800c95943c0c3e011444003101404403070000e445000c44100ca9006082e000041a1102d46190643e40705030403655030070350841c1c40c04080008628030f04c2d00001e900d56081204a02100d080c9003c9486485005400750350340f420094500d003600070f900d040c4003064205d24014820a0b0140490a6030034448441c048090748403030604400d06a140d103021301204940c030804610303698040d00501c1c1704a00903256041e15a0341d03900190140e10864901a5140e0010059402d0a40e2460f0342c20b20b5224800708002001c800d40203210311003481d085010780b82c001100694810306400c4400f0140540760ba803c041c130450030030001080e01d4101c195490510703000c214084207034112003005480100000c00e0300c140b04070b07542c0d0440a84 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 383498237 1250 383496987 383497003
    0x31c2115180c080f150604080d0905030c01030219050d02090607030810170709021b06010b0403060e03090f04020721170112080301060807180303120c0306031106090d0204060305 78
    0x40140d0804882c041418058011a03200b480001c100e2940f42c2c5d41c0c22040fa0100c110681e80d103a0101d004e000104982e81d0411889a610255498202d0a00c1c284800c00d803405c0310003410141014010802100c4031a620442c4c5085500c607424419280c070034030f0030329401034050281071a0b004000810003c00f40f5034001441c5000c1c0f61500007400d007860300c0715607400c2c0046a50091207113a43c44410200700021003a4010200d0b1095003501300e0400780c02d040047e01304507003a84500c2e00d0031000b203402d2040c4905403207002c1d09500400c0c001d501d054003030004100b04180c03840d135651060741d002c40c004c400d0292001c1c030b03182d5081014071441d65407034502d000540b50010701e02c0840319a00030180081203080205000e00c0b812034000201c01d00f035070702e40302080f1807121004098a04001c1401c080e02c110f407541401d80f101540c82912198141c04010410718121000e05c45903208150401f01e040003c604404a481c04004080e0b882c40c1d41c4865030004a100718403800301c000e41247c0382500c00030900c800881c1d030074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 383499487 1250 383498237 383498279
    0x2503020d08071e03080705070609050607020f06010603020a1e0c0237030b04080a0c140105070e01020318040b0d0f06060602010b090c04050f010e120705031c2115 71
    0x4140d4043c034840c0b050200f40c0303040010089000c05d00400c044a02403005401064030030000440c138034605658541c18203000751180302c0075a02901022400348401c0c4601c034050806071604605011110308010130510300c1e10160389400a2806440c01085e104150309060307107401a101c03810141103c03180e403921000b80303202e06584503000381003180f01c100380182410880f0342086140b0300940f101d03200c9508503401011020240245440780c407000a5900914060b0f0784c8404000140c10300c1c11203000741052030000e00c0281190410403503070001020380306081d000658180e4000503607034000800300e482c0745004240074200000c848080d80400040f41c10110949110758000d0042d00c01450511040d11000c1e2582d40c0000c400340400d2105041c070744005c40083d6014940801401c100d000400c01c110103c0240031010341060500707111604040040210441e640340119605840c42c140c02460074a18011f105d00c0c21103010125000c4042035000242075554280d00400442d0341c60017240001c252500c110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 383500737 1250 383499487 383499503
    0x414281406151216211401020306010906090501200f01020708071a0f040b151008040c050909030a1209080a0f0206010609050904030819050703090309172503020d0807 73
    0x2202c4003c1c000c189101c202c55078040002e415400e06140d02a001030002401801103884036a580c04034600e0f4040a04843c036100005a485c00c10a000419205a54108009220086601b00803999000041d50b0381d80041ea00c0417804444200701607030038400d02e408400795560001c9014014400d0101c0205601e620032a0340c0300c0030243e1060144104c0404076248000b080610000502140342d99105a43c44204004c0c0702c0c00c0342984100040209002d000712500142c0b13520104020400d0b12132488000e083c04544441d403038684a2341203a96031180035070340c90402c5a00800e10310342c04030a030404c009030b0b41d1007103000e03848403034030130000700032080342243c0e02c005104440c00007505174000d000c0c500c00d4034809454842d10350707103644065985000181030240c4013000481000200745044c45440d0042e90199008030f5045001d0600900c2d00d05680c004ca400408100c400c6801d04600050300588030324420920f44110031880c0813040e008a041d4006900030030182e2000c020004420b008141c243d11403240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 383501987 1250 383500737 383500759
    0x2a0115050415170c130e0607050c010603020904060b1c080315010c05060a050f0109020403030c020d0203030d15050406051f08040f12050a2607030510050a0b03041428140615 76
    0x490707411b548107041d542180c3d4000720040f905d602d1051004296103d801c40021581655035400b02e500158201d90030350741207a030744404421500d0300c5c03092005112880c904045290302030342c035403100b030b03103c00380c0002205204c0e0410190b007039028205960b842034100301581c0c100d1034807000c1d510181008031281651241c1900001c16419407a00c2a1000c2c0d80c1c141d9910444d980352582400441e1071910b40036641072105010301400341620b402012200f44007c2c143d00c00c410b103403000f07200c180c0300c4507000316105001e40c8a200903d04503103404503030110283e04c0d00b50107a88039420141d10350750302088003801c1081088507001c3c4a40d000740080c0300000c01566401d1228581d200013812040b040c1307240142c008058400b00d405140311383c002a42040500895140460740c400010b000401168030840007030b003011042000780300302ca00d00c581d10801c140c00a40312180d140c0c04450048400c074415480584852030004050141d004e02c000a80b100c403500700e81d96414000c407041304c901d0309220702a125203031034a5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 383503237 1250 383501987 383502019
    0x2071514100302150f0712030c0f0522050612042120030d020d1b08010e01060c050a02090930040504050405122a0115050415170c 57
    0x30345481155005030074451a42150300700f081482c06505224000320060029000b132008100040003014441c168a11162840706030140135180691004001e00c2840601d030141280c121080302c2d0414951035070720700d0200000034030040b04965500156040003002c100c500c41c481c4040e1080d400f4a02801c9200c09107486081080c2c0d628000315a018001803100211f0f01c840005411400e030451b02d884103680c140405512144202c0e00010811010952107100040e00c0c000c91080c4081c80c03409520b080110b540c1001c58030510090188030325010081412802801c4c00024000c2e0b02000b070740104101c400382458854541e440c2c0c3c103000120312481c906030000c9404910845114901400c0b6402e490405140c442008000c000040090700c8a01030140c80503115140310f001411000d02415030492030a816411005000c00c0703d2100100c50781c545101c0b1404440d01110b828220348044a000c1102d40314100f8191924100e98013501000b210140b0448407100b02083c6005805000d846103140c009500c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 383504487 1250 383503237 383503271
    0x911040810200c0a0212010207150204030309230a090212070c0b01090c05040b0301080f1b0a0306180606080c0310060509040b0606040308130510030537020715 70
    0xb540030b02500c404442d001510002002c05005441c204406681410b40c041c1c02066410704201074a01d01b82e5800250034007000307441030007031713074040c42d4144118281421913901a000345941d01a0950a001180d507050040000d2040210f0f54070014221500c0c20381e64221207070187d040b1015410b95013500100003820b043c0b06113544a5965007007010403e20381d00c0c207090341c1e0050086008400400070100070201d40c2c0340300c0d2402580206405c4000700344100900d60014208640b0110405229030801c004010b1079888984040070f607504020000740140403240040380710344080c10b008101505018000840101c0842c00c04451101a03047e501501d1514601808603406070050917404801400450041800c0c440a142d110b40d001c1e000c2440c2589a440303105803500540003060b07035603440c00014056410170480e90904844941000d00c140c2c1080c44410190492810541c0740b034491b0b28080c01900c03818010400502207150a0865444240c3d041207840707105108071010300d031800c1100030a1560980 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 383505737 1250 383504487 383504501
    0x108070516060221150406050616031202160b0910090c210209010f050a0b0f09040905010609090503030a1a03060a0b130e0606090f070504030f0503040911040810 71
    0x344059607440003555400c0029001814098182c40001410380c1181c030400194a0040c020b662014004072500310420040c1c40b0103800180c040e0000388a021010030700ca2023000e0078541d160400910304d05161031080028003405040400355523021030000e00307000c0c0030800c1c03038041c0904800303072000709074100464016249842d4000340105c80b02002049a06040c0002288040d130f106982c800d5030b030103078000a1107441d0a0f045125421b41101081103285040014030008147c00510715040680503130a07045d01d070244d06951800381d07441c1c04140082100079484040500210441040069210b0070f00c00e80d01e030002c0311401d824034541442c0320907090321055031082e44140180140761035a211000c41010b0002c00e001700360040c00c23500c00321000c10640e0003008010900a401840b0526000c010024660b20160841542c0341c000710034030884c40e43c01002c50b0143d940118007015000142c0c40e00d60324520442e8451404180740c0031204150b001030360010710442c0d074142c0855507a010300114620071a140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 383506987 1250 383505737 383505757
    0x90828020d031106220b13080c030a08060f090109200f1806250f0210050307020c04050f1501090f080d1d0a03020d230102030a0f091a091908040501080705 68
    0x415803071000082c901d4064035034015121201c2807c600410b98402005070008010303291541c00109400402a620084995010b20101c41900501c00007002140060b0018040c0942d241e4031109030707407404410840c403001d1210050003440d03501d14105007515000d400411840c0d10340c1c41d81940f128154035110040c0c540c2402075600710500c50041e001c5d541d03102c0f5406401216a101c10b0a00000075981e454601e65401469450381692850080717402803d040c80c00590314411450300c02400307581070840388466030050018002c3c0d104d041c0b1500050f1010002544840c09807105104040341d03010700400d049403205415114101d401007111032120b014810784410701e4000352081da0400140ca0400c0d0042c48480c024078540d115844d410b0b080d0190b56600903405001a90000144030400480e07101d00110381c003460400b085055a10303070300c19400015a4840303000c2c035003903800803642c500d40500c21f54004444400b50a222400207180502d03040e0400d1085078040399140340000c103001c0c0501d04480d0700c1c0344 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 383508237 1250 383506987 383507041
    0x10b1504060e010c0c0b03010e0f090706030203130b0115020609150a021e1303020f031b06090103140108070609092c010b13060302040606090828020d031106 69
    0x814240215400b201c51000c45041080c4001d60102203071318602c036240545031440a8694039818440310700e10b03070100900176107070542d01d0208102007600e000c0703001c2d4162000ca00e805a03480d22495400c011040c002a009000800c4070030000481c0e01b2841204004d0074102d809582e25070740c80c07810f06504c0d045003003030f103d0300e8804110000d038001c80a40c0c01031042c5075186084803000b0301140500e05190b0070018000000c0e42c14140140194642000300d42445a400c80080031922100c503200442400c911074003900401c404552252182c1c02900f01c0148000100d41590384e0b0f6030f41e018655a42c00c1c8620808001c92425030300410188000d02407502c100200311880800c1100e03a00582281c2896800402059541c1c0d000703501d0580c4c3c0310360551420126104d4041640ca04500401c0b00f01c405952040d800d001784a14104040074000c98003c51244001c01804c40a40c6025506030303100c1d078000e100030760003440446034100b090b0700004c84000c40d003a400212951584c1d414496051001401c1000c50411 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 383509487 1250 383508237 383508239
    0x180d030f030b060418020c07080318060921030a0809031e0307110708010906060b0702100c062c0d0c0201050d02070501060b0d0c0216030b0c1803100e010b1504 70
    0x24000d0b04003511030300c0040d00ca1031400341da60707030090040c0381c140d600c02e42d03000c0d00018006041c007001c00c1900b020f8a051405946000d292507100404a00b5401e416406960042004c080c2680c5d0000c1000b1003806480709917003107140d2510b04903200e0f8404540200801c406501198140000006036900d03500350701100001403a0400c00003c07180c000400910400455081000d010707036040c44031100415640d8004030344c1042c0c43c504038055890703c0d0800341c14400180314540c0540d4032441010807050150408424066403411f192020f010429050389440c01000c10b80c1c0c0e1008003480340340050200c071805445124501e804125511100d40d003020303000030310500488201c559950b00503c900c40c810000001e50b95551a01c0c00c003c2e4000d881c03508850396840c4402807051341c0502230340094100074a0000d42080c02c6554801141c84045c0c0391100c034000100d04c00100d1481d00d03001c0034103c2d00040888800d1140341c0345030b101400c0e007003101580303e5007000240c0605082c820710550f41c061800710094181 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 383510737 1250 383509487 383509517
    0x1020a021c090f05281401171b03100803070b040204060b0901020a020402160605100504060f0b1611180114030c01021b0f09010f03030305010e01060c060c0e04020c03180d03 76
    0x1814454400342a01d003d500c03d1400c00384001c4043c00c00406181c2001e1b509882800f0001d00403a034580402800026010104003031500c2e00403440030700000e080829a00e0380c445614a00c120032207904621254400080c00800b800380c409075503842580300f01d60600540f902c800b00c000190003009030760f5001da4405200e450041c5000d4020308440350f540790090007401c5050302e500003034880c1030741d1045031000c1c02c000a000c2814107014881c007a246c4000303042c82161410800d44098031844007011700000505500c0000c00284000c081000100284229001801c1da1100d01402d5028401d0294048010100f0b40e040e00b004100b06280860507000380010403107143c400200d00c2c2c080000c00d0b60002240c400008941e80380710310140030b001c400d130f20810114214034014080b0b0310181c019506840180c0010452a9880703540062650b60005000c1017885100100b5a4198000910b55500500116007407071a501b002014000c20031f10904c15100d41e200700401d01159117258070002c1c1c0040c03004400026a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 383511987 1250 383510737 383510749
    0x40b0f031009110604090506090f040b010e040609061407030e0111250b070503070206060405010b090d05100501060c060605040207030e061b01050f01060e0f0102031909050301020a021c090f05 84
    0x186034064400c081c00f034460708001511580c03007074000142e4150380340f0a128642c1000114160702454043c0c02040c42d0034151902030700900144169500081000b000600300007507508a20070940e070120043c004650b50b85544251300c1400c880540c002482c00c5e0b804000301d1014001d0344a0701e01c02000c0503103007000d04105260401c40300c0c20b55400383c4041d1f442c0a000a03c140c40c14510076602a541c05440c0e04010400900700f40d000f41c000c07481141801c0040c415410b0080486a500d0012213100820500624029040c0b00ca00099229540d25140c00021510f13000348400284510583c000c00c103843d100c0c1c0400c0120f0188250140000b103c40c00302c9041404c0000c0113141822514803507041108080c0c00f5507003035a40c22516011041e81c1d1200400903550031011030310003100200c804006044400c40000d569010b081c11040b0604044489102c42074011076003100509000340082d503840520b14400707995180341d14036038010300401c1c50100406a00c40c60001068482004100c03105600d00300030045 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 383513237 1250 383511987 383512001
    0x308070215060f010e0a120b010806060a1203030e010905061f0b2a01060306021201081504110a080613120507080d020d060e0411040c02010c0905090c090a06030506040b0f0310 77
    0x410700649445c0100c00e82d0701d10070004002c0c9500e1070303840482002440d101703020540c1a03104e00303480d921040502150340e03503012101c410b8074100341c092140484181001c40241c003907511581e906503e0629005d040c80341c0880d20301e02c6280e4070105141602000c1e41401184d00283c4140802c80d601400704403c2d03c0440001001c200c2c104510114005201e84d201c1808c690240d40b0441d002c5034001142582c011800c002ca500400c1181d002c1c208140244050a100d007100400051100c60002c0c007001c4555941d10007500030f000762004440551501c0e0900d2406a28400d20558192205000140190384150b00703c0c1c54807648515000e060005007842800a908100103840140d6240c0c50040358268080340d24030f00c00da00842e9159038464480f02444100d500c285404400c690401c020713010714030740100144084940130360307100105580b0f5140c0720310395000300c0c6500d66000038011000100035505da0441405958112010045400e045080001540c603a000e4540c042e00148054051038501d075100300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 383514487 1250 383513237 383513239
    0xf06031b030705060c1e010b0406090b031009020310020c1e072409051f03050f060a030f020a1a04080f0a0c0603021308070b1c0513120e03190308070215060f 69
    0x150758480240c40c401510074a06d01036800580d07558900000c00d18060169038001c00b20150f0400000030170101107612001ea0000d17200b01c0b5901e40003004115202004031942c8503520343d104540303524076100714584038160745407204643d130344a40c100000500041802c2040301d0800c89010304062000100b1340b840d540700b001810a0045650002034591950740b040c080350071400700c103080c000029080c050110b03200034040b0f1a81203400400c208894503513056000940c0e801005a44201c03400d4400101040b09036000740805845550407607046181d402c010340706a840c0d08080d64520102e02c200c850359001825005440c00450400c208003482c06a8001c110f0450001c103040032a0b9142d050061500078103512000120000080403110340c1207001b215502e1490054061005080500c3d801030202d9000001502c2c004a14602c10207450040840c4a540207028041c2e41100c01008001d0810107840e10040c1c02041c605400241d03218400300704042100324072900c0e848181c8665052101c1202001c00345 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 383515737 1250 383514487 383514493
    0x150301080c10050919051008061005070503072a0b03130b06011b0302030d0b04051b0a05070b190b03010c0906030e031e0307020d021203012c0f06031b030705060c 71
    0x40c451a880700c00d01040c0c0680f000745d030341030400e14100504c10710500d0240c41a0030480000300703100755542d84040c00c40c0b201c86c15190054335501141001425885400001010003907012136070030a031b9207000180d1800b1462030401d4406255181204115840102d9942c165044014103030310004019413200d540112041c50004401e1114904405c1c0341d50503800150050b1b07001017a0110f680c03a6900a00a0708403050350188910300300203440c100580442800900000c2000c40c100a40900c1402920500c40c0c00540708141410f028031903901c61658070580c004080c3c1070003084001820140070f00481c0012503614005598a40103084004180810101d0480d0200300219071080f008101c8003010460304075041641c0f4248844c01a1070004081142420340d0480c40d040a154400c0f0340a42e411a01c41008c2d1841802644082c2c180c10202000c1c1ea40c1c1c0c01c1c0d01c00e401d00c90050300c0400603a10403a0168100ca00c5000092914890f0446442113030b603055000801c00c0c401c3e4103051020385100c81c0d202c822 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 383516987 1250 383515737 383515747
    0xa020309010c1104021218010902010207050d0311190b070e010503040b0604020f0a08010f0f0e0a0b13111e0c0d030f09020306090a030e01230c07080d0c02150301080c1005 75
    0x213400d81e488443c0a00d50000110300b400182442c0c0f886440c1c881c241d1a000704100c01440d070001c1d41303c02c8144100d92203031260320904000d06024400d1204d81c0681441618000d00030561080340a80405174150b5490a05200048240c0e008202003d440381c0c0c140c590609658686d6981e06903280d008290039002602841101410032101001d44000c000c04c2e114156550304280b11a8850340781da901c03810340c60030548000c104031141c0d1012990441c460b807501046800c000804078000d5800401a00b241515100c1c9070489101741030701402d240c2c2c0000b0481e4502422000414100d409216000710103600a01c070030300282c40c0030f0703440452428540840803421b5230081c1c0001c1d0510908482e00c0b4030f2034000c45062800c15510110900d4068400d0a0820003201c0410300018401060f1030b0a41011000180e00c400c0e090703040186000038005101103a0000c122400c00510403801100308900030740c04083e4550420154400f528144c079071000080c01070030011401c0114580325008007109110307003045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 383518237 1250 383516987 383516989
    0x103081606020a050913141f0305030a2106032f0a0b03090d02191e020325050609031207020105040b0d06060e010c05070e1915030201140a020309010c11 67
    0x50200d02445458094175921041e003030180003ca4020680c0c20b03685001c00f188402916400c60a42010006203030800c0d072104440b4031802c000c003642010b0b08902c408206640d020b5882411841c0f12095801c480c0a00c4400c0100e00d0140e41143c0402800c0141002003802d52500d0712071005010766082d1100b00090b6000c0001c1010310420380c20100221200108101c44050304004600f4503002600c0108100030000f0410141c003501e06c00d0040a019203403030341003200946110002c181d213400505446072808001400a14640051807100e040c2d040c09100040603c2c1080030b503801603070b02030701a1404681c0c01402c0005507000c1001207042c0300040c0004125a0018005003070034001001d8009206414408003900141c10740404504004600008100241c004500901181c7d440405c00100f601e5035010201010584405a40b042e4078095000201900caa080401264001c1c0c95203910290f284000e040284608980400564420411002294494900040c02d14010b42c640c001c00c0302458 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 383519487 1250 383518237 383518241
    0x1b050c0c0613050f0102030a05041202010504150207030501061715071107030606060e04020f07030c0302030c010906150e070203221206051e0112030302161e0506010911030103081606 80
    0xb9031036103201582e415007071041e4103046408441e07000007400218204050000001e245116074007925100d004408104021a400b4000345c0f0050100c3c0e035103058100703000a000951b00c460502c02521990b003000303000140380c5c01c04001261480180d03005003030045a00c0708201403008028200200b009044010b610001c042480202c0181d0700c030726804101a4601180203103103000c0381078094440c44c41000400040d129100860b1038281e49401c0c0740640c070300d00341410f07403d5001301007801103075508100c003400070850154880304400c513102482c001c181d0f40f1410300200c00030044034910b000d41c0c0100001843d104013603260702917021028444a007110380b24905003581d900c8020b8129a4503403038500303005100ca01c83c9414628121032988801079507240210480114220050107002d15a00181241071580d501d400b031101c1c2078006200c01c4c1c45880071041084141d94403541030ba05c6001d000e0000c60a41554050111001c1d02141c002e8116402c44d105c154a41e031040310aa2101c414540a0b1400200d0714 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 383520737 1250 383519487 383519497
    0x50114181c05010501150f0c0515091614062512110607020a02030303070f12141f03021005030a02190203090a300503040b030a0b0f041b050c0c06 64
    0x1114540c1c0a0030340070b00c0c2250a442040e0020748900385190315201d441b962100115020101c58940440d460b0881c1c04c040307040142840204c10880143c0042148a49000800c600d040c074000444680c019550084440103c400b0b8000c41d9000c42c0801c10045030134150704035500c6040c0d1038840440c03205c40664a40020384032a0522002103460800c810103180020700c80c41d40d12014030f00107062000c102d0390010362a071100411460030300c2003001c00c00c45194411004040c062030800420054000c04420071440c500d001c54070b108045081000c03a5940c5084421a0403c8075405442b0040b41500700105a55031342004080c4641d103030b801c0c009984084400450010790075000c0d00031f16910004803051003040c4006411142040301d21007144031b514425295480703d0480e051410f01c0c2200c18904c1c142e070461090364445800e148000c030134003c00780d20b80d07444400140302c12180540d030f60b01c0c0354082c0401e03211100700107007110b095450a480300034041c4e4010204500004260f6907104103405c0016400d03000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 383521987 1250 383520737 383520769
    0xe071517010611150712020f0702091008060f0721050f01090207170c0f0312010f0e06030a0308070e120f01110405090a0b0a0e04060b0f040605011418 66
    0xc50050821548505840902405091400c4904400900080341da40c203a00c4003a481c10b04448000252000e100f1b0880e807a03500701c034800556488004008900302c1d6003040e5801e900c683c0d0b2100c08107412106080c4000d04440d0031030090442966109400d1503600802040c0009018115038444940003144c0e0012070003581400e00020b45050080195007a400160080301c0182d104003c0c52001c01c2a1000502c01981c400c2d02680d92044181c800604040c2075071840e003228840400c1041c104c0701c220940700d050b1211043d1008140e030303441011484018040d0f4042d85c054104400000200340b0807916640e018000f400e040408602440214580103007803c40e020322074110100340c40c901c02081c081c0e0039452a40440141c185802c00c0700082d55540f001e4a070040d083c0d65a14013140c82c1d1169103020005100c0d04041068500e03140c1403020240100003421482401b1103028001740785014441c80f406d507401a5a1030322030301c5500100c0101036016106030460705020b00582c1c491039407017401c3c6041e4444 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 383523237 1250 383521987 383521997
    0x4050106030803180120120c040906030b0925050108040c0b0f28020d0c0512040e01030212070b030106050d0e030a020a0b01271e0507051c110405040e0715 68
    0xc02c101320600f1280b0640071a540c0a214030f1344800c48003544410780340040140003041c00551280708180c0e4507481a68444407110b42041030000c1480070005031540705a00810548800302500d40101c0c1e0580c50300c031903080c2401080344007485a540300c0c0c814a0707445441004ca0001098032010f07698400e80040c00c40c0170042100089001903002d5105440040461035403048032000303000b9a019450f02500c1881c04100100d003880941488810840c0035004002e403071101d55150344a0340304125002c802d0101f039008040c1040c0b03004003018009100000c55101100480c15a401c0100031141d80d8802d0b08540501030f218240024440c42c18402492285c0f0f4940090030000c02a2900320403142e0142d00807016203128186520002d03141c1c1400b808000313a43c800c0000c01800e41c040c001d441a14404402c07502500c0c0004020300035801000500054820341c80800d4052480342075042503a035003c5000810780d00a210070005410103030007410348103030480161503200c1e44900f038180c08000d040b0b4031040068 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 383524487 1250 383523237 383523271
    0x41205160615090908030106110313030507051005030f06091f09060609150c1506080d021011040f050f060c12130e09031b070f0308120906071704050106030803 70
    0x4016030704840010f201e4184180040343d81a11a03008a010510514081c0005601070b5440300d4028403c5990312402d00c01140c0c00c803078407030402c2270351401c0c0e6005841c000c1440d2001c0340381181c09001500d210b95400d0140c511a40c6e01e136000c2c82090f08000d040b01c8000d44c0e5000c6001900900000b6450140c040290700045036894003000500c10401c40c2d0100700c11084d08008800f03135591055070310b02c01c1908030f07800c118203a035900c0c120b90080005502010301401030780301c01d0444603808100302202003150401444111078a40088080344514841c22103181c80f106410401c03801d220640909201c4010300040c24061460702032420031401d40581281003000003101102c01422810080103810b00c030380c8018142c07904c03210684c2d40384680341080381112310020059034011410410303140942080042c20100e95130740c1c40c0864058120030217010310441c560000820a4000250192041440340e48083d003451100e10980c0001c04043c00540b542d5480311004408211000002c5010305001c1044081c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 383525737 1250 383524487 383524511
    0x510060e060310060e040305031e0a0b040b0a060e0f04060f0f0609090b0109030318030c080f060a2307090f0b0c1006030803010b091c031107080601030305030412051606 74
    0x810382c00303c1d001443c1003414130250f150131401ea90311541c1800d02d29502e4555401c85501d6080c03111100e89451091300c1040084e00141d000107a0300c03101941d05120b1040c0c414208003050405020760350000d8650340201c80586031040c0c50540c04031001d8400211940c4070039004c0080d058035006071040c00c01c0400100411a070081d132030b5009000c0080100402c241002c0000c00560040c0300c080e04200d01890409052958128042c00841e4869031120480d0350f500000e6032255000e840315411782c0203002c000385da041c4046c0526030084441e54035554020458030300da007000d0305000d8041402c0181c00d180114402407030504800141c981061107036194440390120920300707070400c103400d0409828450204001140703401030707a066481c41e44049848518680c042600c54280c80c140d40e00c42da000080650038950410740f011541000403040e140c0480d100d00409603120000c1c071000340055401c0000801052500c81c6c002610210791802916042e0f40d01039100c0c2d9460f540f101a9038699903541c000200b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 383526987 1250 383525737 383525743
    0x2010903080c1c0f0e07090617030c100203092103100b0a02070b0c011e14010f080a020108132418020105040e0a060b0706020c1216020d0510060e0603 66
    0x400700c50010b070103150242c41690f492608040840c42032402d5160f074002e68500045801c002c100b510000304440c0c43e0350341c850b044006000c030b034812000d030406020551141484080121901d01c08800300500240e6150301302d01e8003d5200402c4125603026103043c1c0d009004501180f90300403594455026100c1c108103149111680442e84050014002040b0621040360003046201c00c40d0103580d582501c89107250a5180501140f10780100442049401c800c0d444425601072000c0001c00890002643c0e2640300d030565940c0c40f4092010300c0c1e404408007100540c841c204456000c05594000d40248006545d0925280e0406450f1440000c480450701d064010f68411660420340f81107180d45009030f03540020340188034038021404408c0c040800a034410b0000e8010800810400c0c400642d80d01007418007038002c1d000041031107220b002d2000e00306584190300b41940c021251014600048410907400c03c024200344600481380f078001c1c801c030111004081d21036040100f90601503000c0038908a0200b6003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 383528237 1250 383526987 383526991
    0x13090f060b0f01031811040e0304091b05030405071701060506030405030a08100b0904020705010624170103021e010306030b0c0d0506030a03210b03030d140708091b1201020301060201090308 83
    0x1041510f13000002d610349900300400d84055401000711a00c0200c400d000c2005081c8c1141c02a50900c8006000075802c030f000e500400208825500c1240d030004284002c481d1484143d50191242e400164203004000c6600a0f00701c018048200000b4001e41c1c0f0070116103260402c035425203090300086110050a0b4200010b50b80c0195044855840b003400c02d2603296941c0a607108980c000c42c1c3c08140030080101c02d60220010f03100c1d001600740034502281022100c41c0b00640324800203502410000b0205041d00803007816281d00410b21300070070754400c40d00c80041544030003c0d4101f5840d11000004070702c61031802801540c1844900360754a01d08008001078400c0600120300a600c400102d00c0441e600141c110b0301050205d01006800c049500e10720b0180500700c2450b41d1500001800b0720f551510383d0f102c44192500c001c001e007100e0b03540c5441695101d9044408560507040340748004402d4500303600062001d03400911070b0784100003a031811800c9070026041000548e54a09100080c0b54020f80781e19 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 383529487 1250 383528237 383528239
    0x71707020f0a0602060a09051e06180105070507060f200903010c09120b0711100204030b0106030b0307050f03010617011a1009061b02181015050913090f060b0f 70
    0x102d02c0c1e0710700b0800964480005007540c001c2076444440700d0800406001060007109265100d070484000003004c82e4036006c0907256990440600c944030040f405042c020315100c9d0b5041d40320b0a04181440c0c8542018bc00915134108030070b43d8500c04460104c010300b04a00304d0450307681410792a00100403c1c1400c513000e0304145014460125420800300602d4451860380540c00403002030710b0385900c00151f41d1054403a810071814013404002d00c44500c8a40d0107801141e01402c100c00391030b680c800c4203800320307002c411031590141c11110085c0068140b840e6212403600d4050000a40c641d51092020310318124807285032956511100442900380c07480f2071100c00b4800c05c1b60400040041040d01500100300d034807401060001c0310300b111035030080a186c030240058000c4c0c030107130f01144801d10381a8642402c54801c4064000c840c40485d41c0301c41e0040804601c407054441c580b4008005c401c100700c41c0c0112280a110644405415000038a41c0a410319110f00c50300d00402e04481e010108808005d4048600d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 383530737 1250 383529487 383529499
    0x621010e0c030a050a021507081603030605011103030f04030207150306050f0f0a03172703120901020a060209030712030f080618040f15060f0503190b011a071707020f 73
    0x81d50200f940485c40c40d0180b981114850104000144a09114043e900f800351810310302240300440300030b9000440f04003510a070390801c0155240c0c0b00548032041c98038404501648280009203100c0401e8404642003030190044030502a40c4043d000c0d041d082200507000041e866040412090810540a03090040c044070080d01000c103140c04a600c0c145244409044440310654100c0603615460454400f1040d0f10b03502481e0007000380034801d000007120502800783c401da40c188a1700480c8142031318007a000c16406800080c10b01d4072881c0c040c2d045982a1545801220700c0018201d07000d80c181c00c262442900d030b00401540071100584040001010540604101120007c420341d030569410f510540c000b01000c0707924410305000680103500c14410a50915280001c1114052004501c1c1103480c12012650b098401030180701e840c80d0120b40041810280308010311051029003001401d0308045030b48241402a0341d101d01c0c0c810300c0b2480840c01c52402c0041c2002c25800d02da00240e01d164010b07510 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 383531987 1250 383530737 383530753
    0x1080304170f0c1908120c150903030a020d150f0303020f06040201050d1e06080303011a0c03121b030c0d11190f05040801050a1b0215040b0621010e0c03 67
    0x80d05884810040b41288100c5070860010381300140500300074007400c001c0f403c4440e010f6000089801035400052a6005807017039882c0c40c40003c00601e8494480d03d203d902541c02d545503914140e020390054075807680c0d450b8a804003400b424a04104906c001c02e411400a0f901c50703d5420040c1c02c2c9804c0c0511040329410090411000d80d0300181112825101ca003400502c3e41d0000058800c41000003584501513810081d0004d03041c6000000786058a0081c045a180440755001702522803050001c451102c1c0c0091000200c0344230742900c000d6004402d034501c000201c1c030f8044600da043c0e00840c1d554106102c00b180400815045114808000381c00d2200d16160584c58512048480652080c0108118407a40f802d0040c1340f051065034010320300c2c00e0086c049400c083d0481000b03011008481072181d1044143c0c409014400112064401c0260000480b030351100e403981e43c0251070042110390040c20318568099012440080904291400f900001c0c2c61100301d10807070704221408070642d102c0d038804c101b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 383533237 1250 383531987 383532013
    0x23061c081c0e01090303090b010602011806020f0909040f05160501020618070f0605070b06010912080f07080a0206040203150c040918060c1706090403080610170108030417 75
    0x22101448040304010641c1c08504074144050400c06004070100c1d420580d0325402c05806401c5400e82510030030b003c00303040c0c0c5c862504908952940b41d00b2140f00741d0600300030b804074503030b94020140c540407200c80c1490320050b040071070501c80040d43c1c11551b007040c0e08021003d11a0501158240032200c614904040d0310340070000f03655410181840505921170100b43c0c006d04010000400140501c0c40480c1d40555111000303060384c0c0140c007040d0707039035032a40000440c0c0390b214011490a5444205d0408807070345d0305884a500d1034021403017442503507078100030340c1011403140c0c1c01500d070f405010360081200e413606105140c100b07080103160101100c0b0342d1091001d01410f00c0141ca05440c0c201000048400800d0700c80403850704082009001c071407420004100d92540031040b103138043c0e030001119425886040078840309080c1140c014001412202c0072501d18034100030003415860f80e0b403402000031450080000303090f0340280c0c002c021708e80c00045d04005400d440385a40c05401e9a40010f030001000c400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 383534487 1250 383533237 383533253
    0xe0109110301050105090913140106091406061b032703150601020714212b090302060a110d05041a03010f140102120d0606030e03031506090423061c 65
    0x6d05107110300494000912410004400c0f0f11016400842110b082c806601401d4001c0900d4010401c202e41043d120044102c1d4125415004000c0a811149480a1003c01c079614066010b1881c00710302007040b08801d02c01c91204400443d0f04030001902c402107060040515000d012000c190032680e501c03040089907a004562041240c08480e1002d0802c940b4a0014000200900c0044ad1080c411468404002400103803484203985003a03003186c901007000d2008881410051400c03000400b1810140010b080c02c801800c181350301814254001200d461210b03007461052a64540083c0c0045020485420814401e507452502d1803545c074030319410300d0244a1200c101e8010f54611503403120108a29920030800300c00a024000030807900d80d5103001e4440050071242c421400043c1c1041c444802c0d566012044030b0007500504521003030440001c0c1441640d07040800c1459000d0b5a4840c4441e40c00f11113425940fa27052810304219013072a2050400c00e10003a00f160620980001003c0140015692 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 383535737 1250 383534487 383534497
    0xb030a141f14071b1106091f081308030c09041b022508031819061d010801080309040f0605040614040e06090d03090c03020a081c02030906040302060c0c0a0e0109110301050105 77
    0x10b040c152007174240004150f05101d1400386a401c00e000c028001c1c2ca6202074284112500807944e103154460715640348600c030070b80000343c01606000c01040840c1200d41050014444440041c0002c12141c8861900c16505120784080102681003c2611003400d42d888024034002c01220071440e04090800165079601e00800340e182c54500503020260715242d481d0317410110440c1d90510100d801d1911440010a00460807040200f05e1006191218103580513141d018180c071030360002141094a044208000b0300140b50303010b00e0641d620000450607840d05d02170310340a003411407001e0000d18100c6042c4400c50300940090031140d0031010510036108400318a5284800841c1744c0032400b0102c0341405884440c013071780b000394000320400c0f00060001d004200c000c0015005810514034180d000801c0c1c2c0c4034429a40d0a41e80310314200014001172600201425101100004440c0d001340501c0c007040940444c1e41010660b000c01c08010040c042c550f0140d5110600440b140c94150351418002814600032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 383536987 1250 383535737 383535743
    0xf0801080a0f08090d1b091109090411100e03070902070305041a040e0115020f0105010e06060706021c0923070302040513050106060e0f0102010b030a141f14071b 71
    0x40100c6441400f01400c140d882d0118010403c9052698034605018501c0c4810356420800702502400a8541180d1050000e04610f851100340b62805c83c034100078030090002c1c01216081d00e4165001000d4458070320102c0100d03025203030b80c2c00c1e04c3e814200309481c00304154010811107004114100009600c44241ca04890842c0034652030312041000c0020076001750380007501c13049804000062074030700c80d0500c06806415602500c0d1000e000e600d1003821303100c0c03d0042141160403c0c000c034446082a80040001c41e009510040c100203845407450f4910705a07070303841c07200e180c0c940100c0828044803494040b40048500c80c12120050400fa0f46900e0349106e1002910596860000800005c000141005d18541c4007008002d03041c0c50b1000a040280404010750058008040c604d040f54014416041003040c02030080100c1600381d640c2d0b403180d20902081003110f014409003103428540d06600e03c0c0e811618140007060400c01c20000c52086080201a941040780c1c5419030140302901241040c21950 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 383538237 1250 383536987 383537003
    0xd031104150e03070b161a0f0f090327090f04120e01110a0c030c1a07060902030c0316050102060c03130312061d041103010507021002030a06050604150f0801080a 71
    0x2001000007070030102e065010510003100006c11240d40404155030b982070764440d00c02c4954800130b06000181c1540200d507503801e51208003011494400d03512201c1e40d8440d509501300c82c50810504400305a600d0455902c0c03600c01348070440f4460701e2a2240925900c21b100f01007440c164070b03050300d889484d140b190702c107032062082040d251021644142e62080b100950134045440742140c0f86040c5000c03920502c4146c41d15001c940e0007049450f40d0a0342500044040511fa0f414885242c44407001468070403001c03645445004aa1120780d102400803503581d074240c4100c941400c2c03401d000a82001002401390080c0b510820400008900c140c0800381455010302c1d121000b800b0b4103c405000300140d4110039050075101c0d00c08000c0c80920300391f051003544211182c1030010700c80b2040c14280d0301e041e141040546c102d40c20040304068a0740c065a03000140c0b40c4046907041c0d4405c0840d4031640580c20401c50380910369400988a038000650114a11480c6020b80466142450399511403100c1d4800400d00d003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 383539487 1250 383538237 383538257
    0x11180708070e04050c180402190806040608010608150708100b0904090507090b041a0d0206031b030a1a03060115050c160605070c0b040e040b07030f0e0d03110415 71
    0x42c8a42e40c040140702020300200081d040180800503540c100a0a01c3c0c0342d40940c0c0f0140d4151f0520b8000c3d01d2903074243d100b90942c54006004140c0c1c5003a4010460382d0841d0fa25200042d0340c09003405110014006903014214007003c503174078240103a130000c040c94140002d110502440c540f12500444c115582003080b5a00ca95002000402070701c0010000b8025200e014004607850030f151380207407010b0004071800c228451500c1c0607145c1000742002003550202c603031155a000b5040c0380c0700039684a500c0d0501d1300c4c035000003038520200c01e800a031410324405030b40300505201c00324402240402a0003c40042007250b1411700340e41001d000c648501402c000000c01d0b4540003010402040100102840403512a16246d0500504a8000300010354040200000c0081d003000c7c40030407907040d0b410104035020a591141c640040391100500402c4c2050341e15200c41010110a114407201211690094500928a900002e0030364440340c04140c00548200010802c0c0041590a0b000800140c10b2403031060b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 383540737 1250 383539487 383539501
    0x3060301020c1b100c0c060c0f1202070e01090207021018030501060312090b03150f0f2706010e0f09090111040608041704050d020103051017010911180708 68
    0x382c012084049030038490583c0c030308010303103d0408107402c09409840010020503140070440b2200d180c604050072100003c5400c4c0b05403880703110305a403424040c0d442e8205031381c52a0340348800c1d00680340350140180c0100f60288002d00c4001e021074014a030340c402c15402e0040a800250300034203000301440038000c59510442d0305004a1344c2c128011070300000200481c039500d0600d201c565a01c440004001841c0007004141300316004103407800754564260700ea14021040c0e0500c40c119021b100300c141e0010110f400c40e401d941d901280e00e00307101c000201500754500c59980061009001501c024140203810410b02095111000c070701141c0708040b18030405a40b03a1004180c01000003486007820307450001008691650001c605a0259200e4417a0740b5101d001507004211034004ca014055100c5079441d851030240d8443d0704010341004c01d00100080a660300c42c0785440d05620500c005120f46d445006010900207510a11414010195042d1045030511101e0f040b24001c002d000c02c0c28440201d0100d425 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 383541987 1250 383540737 383540741
    0x1101021e15073507020102070302120a09030b0a0c1e021513061d0f060c0301030f2301090203010b03010209060f03070314040c0504180c0911090604030609020a090e0d0503060301 78
    0x20300440c03121074400c03d07114044440c10411005081241020207010500c8140705100b291a020780642c0609220f40024504280a0b03202041c0e200820140020100210351491121030051a00200028a61280000241c8120f2404030040d035078158400f1a40443d80d00818a08038210320110855015500c07845500c10301e11144901a1000d031030103040c50280c0110f81c0300420a00c1d500d4044541501000a5a59a4000480b080c41c024072080c40100002a2403210042646110714045000861a507034200780000e002061a03603145c0d1244525001e5040a03c584001c1c1304068009502d0107006901141c06031040c2e08403641e42e0003000002641492081d4020b007048a0340c00c40303042d22800e01e400d146a80100d1400385078440c51410091036100ca80752501d41c0310650b0300004100c0c0c09450100300310001c02049800041d005000c004840c03c1d503072a000208041c500c01c5e40c0000e800100e0340103001038032540384c011150882c40d142c92443d0540d400100080c0300342c800c1c90100c0c0d0ba60360304004240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 383543237 1250 383541987 383542007
    0x6090703051f0216050c0909120406031d0a03080a0c1d0d03112506110604022815020c1203160f02040504050a0201120b3a1101021e1507 60
    0xe80000d00c0a01304100301d400320b181c004400b4203c4d078860050329212007480c2c4601c8201e109502454040104108850081c3c000c1e1417101507a001c80803c01e00c11080660900500c0d00089001420203410019080c01031302c40c0700c0e9030013860310f050b243c030703212046401240c02c2c0c0d1900081d100c1c40142510b102054440c5694034a815080c8059407950110044c20607050480d80507071481a00351510f01064040c42242000d04179400034000f007407152641c0c0c080c840038480030035481d940406102c20500841040c00342803402003c0b400800d62030304038241002810464040111445500300058448000d4000070549010790f0300782550800390809480e24507803a2a10010080d04a0305010070001804004950302030418000e03201c10240000955540003207039403540c21280d00c02540310058401450900240540c04c0d0f505030654001401e1012a4002c00c1c41d04000715081c00d5180d00003038003540d05000841c11412505e04006140740a07c107081d0700c80840c10360034402c480c04803000170f02d014401d04501c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 383544487 1250 383543237 383543257
    0x16090b03040c1a030403020706050c0c041d07120501050717041401021e070204060506040b1617070521030c0a0503150406080706020c0904080306011d0415030506090703051f02 77
    0x3c01d1411a900d21101500100c40c1a800341c0100c1100160303150040c012a035403104aa030140081c0c403401d00801c0001c05601c40103e1728400302c07040703078a2011020040e0b00d003c2c1118410150702210689400c90039160014028001c005190308084640a280c0101580003070f17100d140f00018128a070070090090041290b03140748403581282c0051700812140050200d203000f664203011050301d403000d0000c244203512600300d0803101081013210001081c0500c1106511400710805800710025241d03a203a0444ea20903101a0001c21020307421501e0305410f1350001814512641c110700e440c3c0728945541c000c0321100f00901c5030000004500020071003882107d200c0051003080788544603090f581d0b684e9814054400588918144111149800c0400501c100e9100d0900c51070369803440d0045134442080031000113407680c00c205001013a5120b002d060414403402d50051340d114610305100d032030660090700150b40f0341c10a007810300c08a000811a22041d070b46030b607aaa81c1044000440800030f11501c1408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 383545737 1250 383544487 383544509
    0x90301050c07060c030501060210090804080105040803190912110c0907020601061b0c03120c06051302042307030507020c090907090509071d06121507030516090b03040c 74
    0x4920300c581c0308040c10310280a00702c100a102941c6206500f00d4034280200000750380059003003d00401c040c0c114821491040c00e2090505649a00d01801e5036410345003140c17081c2d0040100000b896488039003851001c58090f050061803491703161410010501031500c0d04200509240c00751404042004900c80030000d001c9080d81e24008500035200d08081c09084005019090b84034285800303070b251290110b4008019255451440d0742e6185020b0f080b001d030700300744400012268046480740c45458891075a040542c22100482c0c410001141c105e4400f06024040d00110f4410f03c04940c0301c6198481602e09002610780c41e0341c00b00340e150402c5111081ea011008104101c212040414154200c902400c2c0900c00d0340c40740301d45642c50f2039070380c00cc400074900501860038100c064081002c1d00440f000e03022840f082040c0440505100550950351001d072410418040070607030501c500e940c41026220120000a200400102000094841e01503841c0d00440070500f804a014148002040340c0250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 383546987 1250 383545737 383545741
    0x210c060b0f0d0f0b1f0e180304121101170a0506060c03070501021306051c0b01030f020a030212010e01050a030206091309050d02070504090b1303180603021b030406140d0209030105 79
    0x48400718801c0b00c0f02c01c543c005030300c1c0c000c104440980c060401d280800c4801002d4010301300090003c4046000742141e42c0f4006450880c0406207052000700050880d544070001302d107041e810192814030004400604000030200c1c000c3c440e108000d10f25401090410010506490b07401c002215400b40c0301e00c5040f280800500c450421170154020418040d40d01103c0e440999210f00c107442d5030080d1000c8000d80e5a0710f131208988081d403039000c03459200050400007011481c00540804a0700f040011401090380080c3d802d00104040901d0f50041a90b10300452496040c180421040142c40c80300a00030180801c10f038040e5a01c4c0901d22940b8007071060100720102aa041c41e5942f080f24a4218001d4001c0e00c10100d03403800c041c000e1020a58102024604644030140c01c2050783c0c52212040d400c0050111600c200507011410790302c01448a5600580c84030106500c50180d0718801c51303540b5296200708810401c482c1c000d80e824005445210009855060071201c3c0b030040d2003039030941e42c1c0c10f51802c01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 383548237 1250 383546987 383546993
    0x30f050c0319060605030a0b06090703150303090303120504020102030429070614090c0a031101050c07091505220504170715050c070317070512090703210c060b0f0d 72
    0x2101601c9103000e04400e10055640785c1c10f2540715002240054110514000000c2c61414203040302600032a291a0001c2c4900160901c924038001c250070072000101c5a02d410400d0517480300b00040c8800403440d042005040070790010f0342e01c0c400c910460201c0465404440e030b00d52044401e03808100c905103a01561011036207880001481c0342a070b05d082c0e0341c1c141c03004a40104400192070f4600e01014000042e8141162100b030314207524140c2040c1004002c0003091000241400300c01c008003800100868002001c101c2c2c00c050b030203941c008900941c0001c4a62412528200389040071034840d03080051280c56500300120141c5400c035030021100c3d80080c04404100c14014140c0a0b155000d01c200502d80b5060003012052041c070202800041c51100c0071078000300314580880d0409060308116207004540804030322900705c00c8030f18000c40c0d04042070400510160b0b128020b20f01040d003800d106203455060014010054814020b494141c1c0c40d0488055074450f42c03461020100000c1000407800c2e4546 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 383549487 1250 383548237 383548273
    0x5030610031b0303090b1c15080613020d320d0f0311030712020c01140103050618280b0406020901030f020301050d03050313020d030203120f0c04030f050c03 69
    0xc03104450903215940c51035a165582d00101c0182c3e41d1580c2c400000390300d80840426160451100340c1c211004403401d029110038140f1a959164603003101d2000d1702c1d0f00d0144218140701005007440203d100c030340080350040c0d4510245500c0a039004c516800040c400318100d103620000f10300558101204820300c0184035100041000b29107131a0303610314a0315224203000b2810385035901011080d968040c00031461b42e60080c0c40c0ca526240c04610018101028443c0c41c90948400c0004001404e200310b00620a1000a00c05603504c0700060b64005a184409400030340c1d03036000d04400c2c5504240c800d040b4444117400c0080119901d4100a035100075090504001d002544602c40c00703400b00380307800d07000e9110803564020741e03040b40d6004145030074115954409480c140d000500c1110050140103400005964603400c034004103000c0e5008546032010107810950800000d01101c01402348281009011211081140c0603633501002004c0e0b420a02c1c54150301e0110003070303c44d642c1070107044646c4240101d98 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 383550737 1250 383549487 383549489
    0xc0c06020c0a0f150b060406050d0b04141303020715020a03200a060621050c1302040b03100302100905091303021c0e01180e0c070f05120703080a1503060c0905030610 73
    0x3013504008a41029007008024802c9100f0305c00462018410171402e66000c0c0e10a03880b01201030b101003010390b400c5400f4600c00000711040400049100c07402c900707041d410010741d0094280d2620514222405020296441c01086c00017001c1020003d041018245962411010008500201c3c1c00e1944a840c05001810031800b0f10220300d00710130200700f9140603a0240030b00040e0803101420b600c185540600505810094070b4070340c1380d0340030000000c4005950700218800c1c80055403800c83c241c2144100100203c22000510070460140402e2006946010401e600050a13903a207254845c00c43c0340aa04040600d08816103115041c40891005c9070480c401c040000070907a5491041c01060030780b0301160317402c0e01900d444181740c107000a6942c10410002c00280f8003c0500d001082032580c5c1d41d925040540b00324050b030711404200801019004800550880c0344409c0600c4060b80380300140c040e070109407001a0203140c69124101d051805208604090b200107000e940b403518120705034a0380c10b603139 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 383551987 1250 383550737 383550773
    0xe03040e0702060f0a1808040e0f0105010c050d030504060e0627010c20031603020703110907080f060126180102040b040306020d0204090f090b06040c0c06020c0a0f 72
    0xc8003000403441031020802d24882c0c001c842c40c0c030300c003502c0e0910b00000401e01c048007104104c0901c4290001302d07840c2405400184081e00440580d40707003106012000740c01c180c4c801414000382c8581400010004a032807020400140307000102c50b51307103042c41e2000e0702e1b5840c1c0d82c000307600824040c060036101641929040307244401d08036500e807110484c1d2600300c0340544c1c1140c0009050081d54400030314901c00a1041e40681000c0740e0801850040c0e02c10342412100742100540d010000410800503603540701e109828088a8600b240e02d4039040140035140000e000a40d81024480028402c0c1c1c081c100f90301e28402c2c0b0b8000c0740c09120148880d09411801682d4850707a50300400e8241c45c1c0094140211000c1d2241c0210380e42c102451a6501d0002e5001010b44500e40d0381c0078003011900341e035603214038803d0740c0d0b00490218000c440c1d400c00580c103100291006014604100c513100c5041d80040301c81c8820303a800b003001a903c800c0d0001c15814099008802407840901c42c08060a01c11a0340ca09124035030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 383553237 1250 383551987 383552009
    0x102190b090105091612020a030206041e0b0f03060405370b030c010e060c0f1b0103240b07020a050307080a0c090c080a2c1c05040f090e030705010e0304 67
    0xc43c01441e0b5519050034090303e0405c2101c1c00c0501021890710f141c1c020941c40034041c0d5102c161258001107a071b80003504010088031419488025001ca1001540001c01e10300d141e141c0380c00031500c138001e041e2000034401402540c440000c90318030b501003211003515070140342e030141c43c0152446c070180e46181c000d00c0c1c0b41511801c0984000e0146004903e01080050584818807150803100c00d110075500040c80c03903201401500d44000404506000c0c091000c451412a1030903486004005021592150b036552204907054115100e210002d122031419900d0030454507071200b10130b02c0040c44001060308515018081e1120000d454200040e600242600ca040941d282c9612507034401c0485060f440c803100080c1c000408164814041d038481c800083c20950324000140b040403800b142040080141c0e021540000208030741c142c102950341d46454001e00d0840d02d01341c0340c40242c03401000700c2c1c0124289a5a58201002500f50400480c0d00c1a83e20070000d022010700c2c4440982c80e038019100d00c0d05c01507 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 383554487 1250 383553237 383553241
    0xa050903011d250302010e0d05010e0109030807031b03020c030f21060312070b070c230601140a05040c051608030415020903060f1008100509160b180102190b090105 72
    0xc02c4107100002c4107070003105101c0b0f030310300d1a001110744000e04200039030440c003446a800086002030280320001950b03a8008201200ea9140041c00382c1c01c0144214100b52030000300b107808404400e0700d030440902d6413030050303181c02011100c54114401c00e444400001c00024190607840480c400651188194800c450315554448044c5510343c10810710441340300c542001580c00045c140000305400a0407403074a03603400445079961540e140078500c41c018080c2c8040000340c6014070200f004a000d411070503080c0d10000c1140c0049011588280200d61085464859006243d4404c2007514040828100407814141c0300b400e003051158815901907840020402c000303000ba01c0a40200c0b600084c02038000c1906942d1188a462587c0000e00402100b080541000480c10310801034000705441c921000202c500304801c94900d400d200e07506004c00032121020820207045180e080c0e0b8100040403644900107280003004030b04108018400130700c030400c1e80c0800c00034001c00b40d490601c580c4212000f04190b17 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 383555737 1250 383554487 383554513
    0x1603081009060b0a0c0c050909030903060a0b0d030806041b120e16030312290f04060807030215090913140c090c07020114030a0c18030209010b0a050903011d 69
    0x10b24a81d000340d041200e0b08110100d0410711a400b200541d40c05803141c0c00d401c0d030300c0383e000840144094540400583c0003290103540f51405004582d007100c407401c0c0401c10766103240c010130b241d10504140502402507810000303549441d02e42240d00405122101c12103880808040500198a00c0b4401c10f40f4500e400d030700408a000000388280d80c6049018024913442c910f5034200c0d000d4411100d052a41521101b2010356461400072009448052032200000500c44109000da25034039030f131845120350700349071041065002c082050303800d4036015110340056194125480d07166200d509005500041c8070300802c0100421412194001417003080c02c41c01c2a607803c035182d5681c40c4405444d03070340400044003092070f0625110090030514410704205c1c0c4030011407440c1503600e820482c2c44002d0280c0b40c0c2e20361615127174049200540c00113400707494010307079056801042d41d0403414044e146045000140300c5032210b000740c043d10b42c1204010000d2080380b06075a0859045400010711b00c01c0c0d80710700c000d0b81104c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 383556987 1250 383555737 383555741
    0x501180207113309040b041e021612361701060b1201080606010f0c0308040f050f100c0f02030d180c1d010605030402030a060509031603081009 63
    0x70240c0c21030446481d10320500e040190400b00b12581941caa03241c100c4000521940d008500d80550754040c40d9500c5113403070014041074038205485903200e645040b0040c9569200d410b0042243c010658006841703000140c05451042c035240780c041c03c4a034506040155040c1d0101448030300b8501c1010200b181c044200c03a51103095144006000f191320b81e000103210440d0765003202c823100c448c0d1340004207200d50748004206046d40080b40b0b18240f000e40c00300500004408000aa42002d070a01c1c0144655980000c003d01e014a111802400c00000d070340414244460140301d41e51311034019041d507490040b1340501035640e40f0200320f845189801d02c594030404034024901002d00321401c0d0055803402d20311800c201c00a041c04422443d049203952090804580e01000c407030003030040005640e50b15254901d030036024003030503030110007000401c2040100588010132140c80ca254440000f140545416102d181540180c020004412946141c0003080c076502c0310415000302100c0a10404842d00d0f8880706003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 383558237 1250 383556987 383556997
    0x11090f091614100201020d140405010b030706050706050c0409141509060d0803040c0b030106050403050f0309060d2a020706112d10090b040204050a05190b040b0d0605011802 76
    0x10b03901c10214030009900b0050b50f00d6080b04501c0c030006181c20001080301040b651015401010314980c60204008c1150920840701014011402031501c6031a044008000748156640207200c1e130307207400c00314002c0300d15401905d002d0b1854150034003005001000012024900712003240c804034440c590301d451405c00c40612030060704045d0807640703079420039251095542d00103042100ca020740107078006613000000e400345028065541d1090340d5075285d03007041e615010344498288141c1d08200a045419a42d101c2201d166860388200840c01d11424040c031441e060000c2d01c407841d03a0314100700c40494070780d000c12940166202a1031f52602903803d007013600c0d51525801c260004810042151096440081107200384c0d00f0950b0f0101c90400c030019080400313517040402c0440790340381581c052100f1441c02e4001c0c0d03540500c118004101b980351011070b5400c904405410b9003c07aa81e100f500140d1610b458212100d44107028001100721740503490010f0090909100e802e68441400030701140e18842c50085070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 383559487 1250 383558237 383558249
    0x70810051309020a050d03050301050a080f0604170c0604060b100e031e070312021b0102010203100e07140f1206060705030403030e0a05040e010608010b0f011b11090f0916 75
    0x408410074055024028151401c099a01106144e0001013540c0c84044034440c452090b582c0760386a524190038029480700d03c2d04115a580c000002d00d040c180030026455501907009042d18050f07041c00d456004061084a04101c1c0f0341c01080c042100f84080e0790441b0740c0d034400958070042d09420ba803c04646038468909581c3c1c0c19044244400c62980c400d9003401007898031170b420340340001d9480e036404404003140100d100150f00300c119401c0754107884094048040e002030000b545546820114103101c108940559019502c803400860a2244a4a0311031281519003c8060f0340340c2820004204030782202c2640f900000501c00080c03045c3c1002000d94041a601400650401d030440d50140c0c0c46030460703100305402a1900c88002140d84d00c6001f034204507403d0703800005a186c20801100d0942d20358105040c0101410411000641d900055003220381500382c0d4078a50400f12450142c41d03004210054039031126040041c0140b240200904a01404842d000c03078410004e088108004189035104030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 383560737 1250 383559487 383559499
    0xc0105072301140106020609060a0c0e090a0b271501090308071110030c020705030d020d110309031c12060513090525050909010e030a0507030302090402030a0507081005 74
    0x141d070202094110030485011880003068400c034810190110940903401500142d200100744081d04c00140400e60b0491464030083c4110040c042010b4901451040030070b004070b04540018000d4a40307540100c4802c140100668014012102c0caa41007859050f40d100e828458000440c0c1d403113003c1c80c0c070305070b07101410385500c195503285440b00305007600000016100b440094841c030525a803045040c009007151510005800d03096803400a141200a8000d140139501164400031a42d40001e42c50181420b58030304a40320120916016080d80240c80503260580b103100c44403148400b00803040b4004107610703034481540c0c04000d520403050311030030700c540b64200c02900d00c4042a243c40c3e030011000180903800f2224151000700b21100329244039055214907518001003840729107011519950000d107090024031a80003642d052903280d12a0200d954180000003503408109802501942c810440041045440f860440c1e000000760000300e514000045121002641c181124850082969805011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 383561987 1250 383560737 383560763
    0x10e06010509013b0121150207020f181902070c210f08030106020f01290a0b0a030204090c0518011b050303100302120d020a08161a06030c010507 64
    0x662000965400141c00c98404003260f4040141003d490f0b822083c4504c0e14182066240c42480c207018241c03106869040d40d0341400190100d480140280515240c400740180e50b094244001031150461840190b0068010650013080d100380700e0340c0c94412403501e18440c0002a20329404401c9210b101002000ea40303242c4420b014802e201000c81c0c00a801440ea00b80e08074145c0e442d403070104040703c0750071510003100000600007207030305101c0400d80f4089440240b121980030700741d40c00b446401041d000841c1d0000c0c42003000c141d84030703003203d0010801480c0c920341d29280c10170700901941c841d000d08603699051441040046204008890841545c3c04515000300d04000045411795410140100e01c20700100c260408640140011401a4002144015040e180d4414030002d4802032000c600381c1d0b00140003589034030b500030421100080d400140c5070b81da002000c004085080c03903014003410080700f0205107604c20701c050041e1400740f0320440458070820b040b60b0044030544640040281202000f140b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 383563237 1250 383561987 383561999
    0x703140403020307170408031c060f0506120c1b01050402090c0306090a0b010306150507060501050f060d0504050a0807053d050604061a0711040b01140307030f0e030c010e0601050901 80
    0x400c0051401aa02e105d0380781c103075030f070503220318503003000c01d0550140c151205641b144608600c41d80d001030010110038112989407400142c1903029404a2040303584c00342002036040c40c644002c46440300e80300107884103581088110703103009190441c0d0482c080d040f0341001c901c803000c0326400d40340f0070031000782201d80e1640c40003620400f60584840310360505886100105070100305220742d00042e501981d4050f103800c098184201500c1d81030340158020180b105100081d41c46990445180010f20200403891703842d0fa1610a160003443c0740d010708450004141e40041160108122900c0342209103d40c06854080f00b1581c0703031b004600540c84c003044d410003c080c03481c1880d40240d80c3c4900000c2000600703658460940186980748451190203c10016003542042001c00c2441c909034030a52701080002a45030003c0c02000321001c01050b0400080002007042d131203508030210801000a00348549210490419545c0e084824060099400e11042e41c015100015105048500092070350f00e09034a041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 383564487 1250 383563237 383563253
    0x50103030513060306031518120203181002030702091905160206161e020a14010203160302040e0406090f0510020306030c0f03190302101a101b02060327060703140403020307 76
    0x8028020841044584840424402c40c0e1280703903c0c00a4001c1d50364cea4079440100b0803c001c41e07000c0751040440641c2e420020342c0c004290390469905a40c00e14442c2c03542c10440060200c02c4103e0f190880c1040104048004018141c06605445400721072a940311700e1681c640c038014003100c2000085400c4001001d20b54402203548500800d0700548005a01c0d6488050092400c0d105500d003d070f400006201c041c4407004084901200300740360460a240c07c04c00c0c0c1e042101c0026002501c1642c80f00462810b014144d504040040d82c03000032108035002c01000138000e90812217502e07103c1c0c0141400707100309003051034501c00180c0380103001d454104601030f001d000030149080203908511404200c1041c1504a02c141980040d80c06c45c3c004144800b04200503610a00d42c4140c0c04000300405459406442c0c581c100010300c1d41210749980300e550380095114990300c0001d003491080001040d16240400128030640240500c0e541800102c0d0004003610011000f520000c005074010007603880400c8000f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 383565737 1250 383564487 383564501
    0x5060906011202030705160b04030810060c03030b1c050a0201120603020607080f0c03161203090818060d0f021b0d09062114061f02031812010501030305130603060315 73
    0x242849400e12a87c01038010025024903c2210165014030034071080c180c0000d20140e1084e280021540124184400204103c580100003420f040e01d03204480b00300d649840000d0034480721006041185185410400d070f44801c2000240d02040f110520300c2d4000f070031801003005480d00039240314a440001e580c0c8214640c0b100c0452540d00c201440340408914041c002805d00144124481c43e82c0511814000481001c002d842c034240b610704000580000e03401c4042d141044074040b0b5840b0000400c0c004201a80b054101010703040d4030b0700101c11345000c6180e0107021178103125a0052a000d2145585c982c0d02c95121071402c01051000d507040050742e2045034601035039a5505c0018081e03620740e8003150705680300700c0007035140307901305104100007400c0054160012020400c5414900132449070041d440f0300c203600140c1d010f852210050885512070103442c1090040c03040027040700b0340c0d49040040c0150003005440515040c03d807000580c6a10a013700d00940e03410400038030507550340101a01c014260 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 383566987 1250 383565737 383565751
    0x10c08030a060905041a0606070f02010f020a2405060f0a030f1106070303020307030e011406010c03020708030a020c0102071e0902091c15060614040b2203150506090601120203 77
    0x2d8032804a5200601d008030390080e80709a100814079a0071084104020744020b014501400040c0720030307400f1030259510300d400c083d02800d020f15502030000040f424450056005003c1031241100c501c004108403104280c01d0747c400c001000180c0314801005000300c540714000368401c1c1d10090602c0030541e558001c001d494410708040796913801010200e0780300c0e0010035090780070940c04010018000d03018050030036440c4200008028050740001501c040c180b02a00e01410003044000c0c032400c060080080c0400f40c04041c0c1140d89070500888000d5071441079840c01070044c01054000282112410240e200302840003c01c003d1150134601d040d0001d420200350f0a5204114000304040c042c40341d4607800256014421040344501d80010310b1040c2d078159071004c4208200440314038514200c0005032000e03110440c0100d42d03100c0d6503c0d4110309400004c2c010b030310100841d170400010020f40307000f50840d0400502043c40705641d42c50422407824000c03140e0394041842c0341c5d03e030340d24403540b98011684191 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 383568237 1250 383566987 383566991
    0x60f0a1206020c0f0f03040e060910061103130f0312051c02181905040e030403022803051e1b0306040219121410050108152710050105090105010c08030a 67
    0x10b0310703c2c0c4e51450000c4610306040d0a07080000d0034020300007002042540310405880c0031149047c03086484542074814031912082020b40e42203861000e07000e00458074075460b1284010503554660750b40c201c039482a40f100701c6900507021140c1d05040c0c0a803040d2040607446555809101e0380400d11580a54440d8681c051400400300c0b240b0070640c3e50b0700c2c8030700e41c5103050501d0400313580c1090700348001c840c0c81041040c0c40b903205200820069072486500200505910301501c40c49011301000b070100c4940d40c01c020014000c040000c40c0c1002d0794640822400700b10000c81d6415043c9002240303521600d40b11180c0c05411400010b405410f007402001c4907500c040b6251070615503240000b46050b0f030200c80480304c8140c007407600041100c0c00c1244500c820404101040300e03514000003103030380b25040001243e038070380ca07031000408074010b066000030004100c10075811524481c0100549035070201303422641d940e01c1c040001c201402d2001029042c0c66043e103800c1c21414113030f02c0d8820320782c20082100c0000c42d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 383569487 1250 383568237 383568253
    0x10c0b060a05130b03070b0f0405060d02090301050108030a0f0c0f030806012d090e150d150609090b180d1d041802030f060403051c0f05090303060f0a1206020c 70
    0x600d91100d0f00c00780200300f0b440003402d0002c8070100350802010340e0116452105c00d002d645440507444048074200c7e00c0c110f80310390b43e072030303681901c80085d000c0c2d02801c40e410b5180200004030740b04080010704000d40d40e6503443e00c1e80312580e070096420b1080028082c06504090351404000307402002040e4021405050016615404007800348105860030b1103201d01e0a01c0080550b000c0d50801062400341c80304078039000082c03411011039045040c01400403072184c0c001c007841c10b00b442840303451603034481a0701c0c0c020302400707072940080000b40c5114141100c43d0130340da0001a400144d05544280165000409040070541d00c0c10115203c0d0541d034429000341c4560640c2440d261740e0752144d61000501c0c44484000088140100f60a00f0740c004a0300d0395580002c81048002507100085945554486210074241d42c6181040801006496840303402186080d00303000c8075020000180d4411103013219003035040c0d80e40c0018801c0056062040844500e1140501400034a40381c010b4510a6070360740c00c4400070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 383570737 1250 383569487 383569489
    0x1703190e01020c0601031b230607020a0e0405061902160210121e1506020703020103110c0a0b09010f02090607020d02040b060409060e07030e0a03120209060d05090c0f010c0b060a05 79
    0x40902a401110602c0c4181005114120315107080c8008100903000c400c1030501e5075615064242303a00c10780602c603050020300b02c0115511004004003a0280111841561925180c0103995000599034a00f03c043c0f8022410842040d6000f10352801113454562265045503a00780104014620880030a10260340342d8403c034007290340b0811007100c1044102100d01040e0b90f9640046814500048070117001ca00c0040c0412900003860758100d07582031800007944208200404618000d5456143d10350054411541c1400015404d49004412482c020403038501d01202d00422881129480c1d90000014400d5602515194101c1140980043e2012940b101e165000603600d5000d6008001c0350707a61501c081c40041c042940703e50f4001c141d41001c0025072084e0300304c16515140c0c040010100711405c0700b1081c1c00c20540d019200380c08c5003c0c21240c2c0f50500580820080c007000c03500d14040303106050303c011a928052004082c65001070311210f41d214115218810030107001404203800c1060303401c0001d81 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 383571987 1250 383570737 383570743
    0x1101150518270a0b060102030405090415060b0a050c0c01091d090a12080f010501090e060d0309051002070915030803010e1008030d050a0b090105130c090803070507031703190e01020c 80
    0xc401288060700f01100c0030303d40014220300c0a071075a41194000e1005001c6503c0d14800310f0342058005803612182d0030700420440141c01c41d60040c3d03044850204021400d40e400c04040e0a002c141001134032407a280d0140112841c030450302ca2411300c640b15010740078524148088181e0410144000e5505c3c44200ba21580701501010001500090300d0f402084504c19001c00311038098102460280f0500e480c10814400d034000c0600700a22420700340705550101400f0300101001080d021700844140a80d01001035110070721441107916450038042c80c0c031050360804800005aa80c40045207040d6402c1c0318030f03402c0c505001000581070000114012900c00800c00c00342c802c00b4940ca002107140c0c0b802002040a40f884210228010f00f80480103002607a0358800010030203c4207040042c0080d01240201d48030311315a8025046408002000d07414400d011032550190790083c0e0762050349104c0c3c1140040035100403200030035609003840d400c0210b1602034025241610f2403100140c00c103815161b5180c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 383573237 1250 383571987 383572051
    0x30c0307060f140304050a111305041203060603020c0703080a0909020d051017150601032034030815040f0506030d02032d07050604031101150518 64
    0x11a0301501d50b44039040c1e0180e0352144454104514a00710304255a0b0035948000382d80004000d090008240034060300d4802500800c00d045150500c0300d0300309418184507101d401d00303c11001900381980030513003034064006c80b0840302a00c4028155580303180c48120301e5400210400b010032101c00000190300e0038900203450048034141c000a01800d0889485040100b00d42c0140051605058030300c4d418074010429280305031101f074440740c60380c2d90880105d000f4102c0701d00b800381e170b451000500703d40010a10064220300d101c004603540400203182102032403803502e524038403130490b01214000009120b0301140c2d4006040780c0622000da1404030015041d100d014500300145642d03a0b041142500d8204500b2030580882d0000c0e614141351003681082e01041d583c0d10140c2c0380031460701ca01c100081c45c0c00301c40c03901d074100080d140c043c2850319004040380c078080e08074225503003002c100341c0b45150a080e4050843c0d00c014915581c42507900c0c8414600312004144035401a81c0800e80c41c0351400d9401c80e11 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 383574487 1250 383573237 383573249
    0x2304060e010b0405040c03051e0405120711040f0605100c0309090905100b0a05060d021602060c060109050f071205100302040f0b15030108030f0705030c01021911150a0b030c0307 78
    0x646640c04e1606200484582044110405050030188040e20034510298102c81c006d4801b000c2c4550340e039086c102e241100d40c0e60040104000041c5a4060265042500d010f500007181c05105400001802106890071800780a6105030300405101c41c4c3d070702a07071001c049140b1a0500c083c025544000f100116a6481020355040e000900c881c5030321306451090030a94801110889440343c1007c0c0401c040740a1080d040700280e500143c092104000503038a0b4009550080c949941c56061050725a2a00001c2c41003071003072800c01d0040755182d16010307a25440340e100c84c0e0b0740310300c0d9040d01c1a240d006404003900c48940410743e0203001c0302503102c0d80140c03415180113400c0810007045030403e005000c404148401e6590a042c4014090003130b002c230454041c1d007191603809445040b9400d1560541c40f8002d0b10140d190b10005410800c040c0b203910100c80c5841c01d84503207000700c0a140341143c03102469185150024450000145440556841070034103502c058222505040c3c0700340401c2c9001e034103402070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 383575737 1250 383574487 383574509
    0x60a020601150c0f0317090111030703020f040902180306011211132309070503061506220f0306060e060d021c0b15150a0518010309020310091205042304060e01 70
    0x400303680c0310b520303800c0c1c0c02c50103100003044101c1d4651203c270640e000c0680f808041680010303c4103040144401650042c00c1e134200110b548100d61441581070b18007161100f0302a000b03000c00054410301c0b42c41d0000740a2b03002030400340c0b00c140302030803c01c5510408002035001c50b82c4d81c1070710518644110f1240001030001140440b5810b0210350240303006115403001c1c0c826804402000b0115007281d416072808030302070740c00039140c1881640b0390b0301544001413641c00e18800d40400241911b1005080000c03039010303000c2003000d2501c17800e0080b01c881c02150a035820a41c50503054006050001c4907014401403181c401002c5c05499491200d01b040a42d08446c0c48104880c4c081c200e840c1a50700190221500c603c80c2e860869040005015401502c0c50000390320940e401e445881c0c0d01030781013401041d40c002c0c2580d40401044100d04000c001d44241507440f000060914040e080c0900101c0f4203490314204007884a0705503a56086403075440d904015040341d1140b20019200c0c4444010340e0107448d80c0008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 383576987 1250 383575737 383575757
    0x304090209061b0a030228080711120a02093106020c2406061c0515040c2718020c15070906080c0304030e0906040e0d0302040f05060a020601150c0f03 66
    0x3c0245800e4510459640d400100310b040c00000080c50301207c03c4075400b442c402e032540240c0c18000c482c0d8440c10b05c0580c004140414803001000c02046210000b8400c65401c526030300c4004080000d0040c04c1643c0341c2d18014140d001001110540381c0341109031040901501e00058040007500340300d141180f90f00d000102d8684004121103a02a1690140081e00c07802d0501241115891151094040b0326031055900c42c08600a01c0031501c41030342d4181c0103070042c000660701d00f030018500c031340c0091810486803031058025081000740b027040044070480c040c046503c01c4c018001600a512902c58900b1038415000230303102c99100b00010354840e810036107407a8a40f0703181000250151500415410300c3c0207081003004002604038540400340c1200b80d812402d43d6035402c02090040024140c0e030200380c032a5201c0826260742c550020401d42d800100400000d0381c0c0d41050203c9030040070003040258108500500640303400c42500015100507181c0a13070055900e1300c41500600b040c5d28268001100170311 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 383578237 1250 383576987 383576993
    0xc11031011070b060d0512030a2a110c061b2a030607020d0c0b130209040602220e070302161406070809060f060111120d0c020c09090304090209061b0a 66
    0x4a41382d106100340d85001a0080a40e105510381d001e90803040300e0820080007080b581c00319544200004400a100c080703240c0100c0d1082d001440c43e412100c00040da8000c02ca550341038010a4103144540d003c0c04aa0030400805000139032a02c000001940e107220303810103440000c00814001455084030314090585060365000c2c5801c1601c0103190302e040d0340c00f210780c070a402076025854401c4141c2002c1c0344c495680701d44820807011480c0c528040d45c042d4008003400103001d034960040180d1080200c42801459036032a011002c0590b80c45440c94071840500002c580c54041d030020a01c91064a0007000c0d400056034034840519000400c0b60180c0d0300100400202c0794014031200d4114155000501843c503000d08210b00401e4001d020b141040703046c0000038000282041001d21a00e840d82ca41e9131209684040d45008081c12036000b801032050820300c0b4640c1c142044158041c612040265103094209141c07180a50321400c43c49800c540c04100590031605030602c0440c1403110070707000c2d0001c010760703007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 383579487 1250 383578237 383578253
    0xc0c0301020f071b032105040e16020f21030c0403080a08010f09020f2a010207031e091a03070509090c03040605180a0201080c070b07050a0216060c1103101107 70
    0x541d002c0c0c100d1000d42c2c0600118014103403d10401644954070f80c1300c0103c111003110139000d10351080340300d6964902803016849014450020000c2b9a6003115a8142c065030b032180d80d403500a16500009070003d0420004c0c0c501e0400969000c10001030903407a217032b40c3c1d54460140368046017200000078200d10051183e000c0c0700d000c4000803c10004198100640240014a0343c4074080c0650318811404400d02603803280d021f4650290404070000b10740350900c0e4207018041c0d15000c12100350483d020380c4800070303541c060915501600c3d005111a00002c22045140c8696400900b24200340a001e10000e18030382c1d141d0380380d1442186c94040c06502c1c2d0509150140030ba0f013003d000d00d100b00e40002081d582d810070001d1040d1a4940902e41302e0100d485640950001c0e1103007440261a00840000300284907030010300400f82c506007603088503181800d0b060303520080d85642c020342c40001d80c603900e80000704040f020f02884d610350003400d86410030050842c010480b18a90301c1401070007408105081031007080c1e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 383580737 1250 383579487 383579513
    0x8030c0601090c020102040b09040b041e09060b192120011d240d0f1b02030403030e090a020c010f0501060e0901050a0e0c1303150e0a15020c0c0301020f07 68
    0x1130700080d42014140108090240190310500f801103584210348801543e480c1c000300000300c9000031031740e00114004181d0020704500001900c8590804000c050030342480c3c1d00138000c034030b000001c462003d400c200015402032516002030020040f10248100410070180010b043c18014940c045ca15009510024014074510180300710300c040302c81001242605e400020356440f1801000002c0c074490700604020300e41c061490419401c5203007201d500550825540807803070000304640c6952080c0b6240d43c0480c3d0780d118501005000402c0b0001c444081c0c145901c1041c0c000e04d05000160510041e1000b10742101c1c4102d043c100180d40365401042010342101d200e486d00c0380d0943e906c483e20740c14603020401424580c81900d0005c0b01920000741c0000210040d07500126004070101031840d0783e4200001994421070310746800928044050b40d10b108009003501071a5800b6409820300301c0710f03102a500a4210008525030f60048018a81887d5428801804040d412009080e20f541c814100034403c0040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 383581987 1250 383580737 383580761
    0x21090e0f07021c09030c090b0f091902090d020603130c0f1d090f03030405070914061c05010b1203120106020c01023409021e04060c060902040608030c060109 69
    0xa4080c444060781c049050682e40030712000303e034169004107104460a031400c0e88090320507280c1c40004103500d2010381141040120231641d1b4200c07001072100700003850070140e40c0140c10008501c40b10810030580d401410440900030180d14621180e0303004183d05038411644540f10003c0d480e000c0e010802ea04190074040d107030003603210440c1400c1c5144400404070111401240805d00b100040035514108104100a9004400d86e6224205450401d03945c202c1070065441041c10003009001c10384003c540148542c00052401580348c8400c1d540d10451000d100742075445540781d500d07000f400e456548035000c80201c02c0300215529104c1041d09000c04006070080011034000c1d501f40310381a0317400900300310380100c030544000305003124a02100e40c82d03c013864510300c245040440017038490780d43c0c0d0142500020a16032010b120301100902035091089000c2c1402080b0780b0761462000c10030769800720031107502c050800100130f62100d0141c1d15541004180722415030010005003c2c00e5103502449186102c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 383583237 1250 383581987 383582011
    0x30a210201051f0611120c030c10090f06020a090510020a0b0a0203010317030a090c0608070e012f0a050303041211010507050a0305150d0606080d0e150721090e 70
    0x1040001c0552903441c404c45041101c0e9030541040c40f6818000c03000c2d00200441d546545c0ca0000d81000d03101e800404821301380f4010b1401040c464074080c000d0842c05d0380e1000c1c5598841d000b40da5190001d4010b00410f204002d00404041340c00e071943c4600d100c048582d074000f48a0a00b4902e0f040b2106100185000c0e100d500600040000840310441800e030400c07105002a00d0381e072900d400c100148074180d0701030540403140384000b4000d90071030801c0340685103581d0b48010440150f130065076030042c401c0c442c2c03140202e22043c08440411600111205603103420941d030b042d02541d1642d41c89d41d0019102038644100c07280081c40043c0e080440d1a0b00100f569000740224500110090414000c000b5a170040c0743c0c0341d10000d5182e081c0110204c90f882c10040a00302c1c11800f50030000e009060070b02400b01c417480746840400b0454090280e403011048000d18071300304404450004c00246c1c100f00301c12268641c5901c403864022031712044d03030f507407402e019900c600b801440c0c21840070600d04040e2000072210 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 383584487 1250 383583237 383583271
    0x31e1204030c0501030c0c121d0d170c0f0f03090a05030601080312062107060f02030c120c0111030408090a09050c07020909071502150f01180902030a21020105 70
    0x10410001c2c0c2049070800d080c00121b6500100003940c03035121550009012400d6255143c00203a0032424039403012036010509102e40c828a000d102c000b03030f040800500704001000511030400340041c000c10400b00107000742e80086074654a4980f40000c1e5611011643d0004126400d42c1c0c00c00c60b010303000401d000c034002e06240d490180c01507202c0c8100140741d000030300c4400000d8543d448a0321a203c010b40c0c005480c4444040b1686c086880300d50318041e0100045007803160039080307813002090300c8100c010078000d4100c0d01d2152401000580c412821035813155201c031425002c0681d110302661185006406070765075625a041000b00c0d0b0b05240d08484070350740c9400241305880e00d8003010b413044a9416507031044507480e4045520310313000031540700505120460401008956002c5a4580c1c5882c001e24400141d072035515880ba880082402204050840303a541c08a406515030440c0c8507050000c1e054859449a9844001a02d071041203050f504a50000100c80c82903824800c0c507901408000358050380f6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 383585737 1250 383584487 383584493
    0x91b080a0209010507080708031803250f050102032a0708160204060f080a031706030319030204080105040809030f060129121f171e010b031e120403 65
    0x204101a044160541d80416042096405101154901a0018040c5890b8006464940440e80c01202d00000c450080d05110b62404000403e5580d010030103420308841040e00071040807038200e02c4ca0161620b8240290b40d0340070810a100441c0a032010540e000b0107000c1610701c201c000140d910411520100801075200891150001d5422505c0c400d16030342c3c030030700050000901406050304800300c103400090b07001400300c00006582070464465144c6c070302c000030708404508642c1012910307690540c20421561031907820340d0992115480003410700500b02503c41c40c1503402c55204803404c40b08018001a5015646000c21103120340e0203200000704079070760401204015400780918030701e00d41a001528151400c01110503a050f40c0d180c00c1c1682040d01d0840e40c0d60141d82403a24051111001c3e01c0404500e82203842450100d10303000305d004040504107100d100d001d40403007106240ca95540c0b80003103105560140b01c401d1152410380c83c0c0822010280c0d9603e8185500355641c0507000303008020030000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 383586987 1250 383585737 383585747
    0xe090a050c01050f0705010e060a0b031603020105070c090e0d030509031305101205101e060507020603060a030b07030c08070306120204020906120108060103051b011b0201050c0d09091b 81
    0x103200d0700f03281c029111801c0841c120110700a00c000100325500302035062943c0031000030214403801844c20180519040c1c1c401303040d1901340801c6e0740030780044064420b002550040d00100800c41c032031a0601c8200d580daa101201b00c40010011a4464200f441c203030a0103507140c010190800e01c81009145404500403190300b41c0403c0b1b04c1071500942550800c401d00ca8042c0c024840d181c1c92800040c071043c41d009003424101d50b2503000c1c00070400c0181710912004007000b0103400a4485c140c4545103480d1980d020000c06803c02808681c0c030170700545000c0001182942040d00a4460342ca01207820198040050031040e0010b00e50703410140340c560100302c00309208035401c02280e010f95005035141c00980c007003102c1b4403451000c0400160002e000144100000071920b040b070340594203440c00b0640b0381d01c9046000141c2c2012038000f42c0c0f00020f000100c0f40b11510025900d20504000b850000d840d045e03641002031034210800400c2903150308201c074100784d000c2d80c5024000070441c0b2418074007445002e44 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 383588237 1250 383586987 383587003
    0x90709080a02240a052107080109051306020708090a060e060a140c060c0406031109060d0c020c030d09050301140c12090a060906050105040b090c1801021005010905010e090a05 77
    0x8441d0300400e40401a5140c001a0300c1401c182076003c60395225600706029000fa0f1018882c400000240061207400c003007a80ca80e1405010a03698003d0b00c2d074a440100e20140c017003d8074115400c1007100540c40002e00c180b00a14a86102d078070001c3c0c9640d41c50080054802c095030108007031061003c000c4003281d6a200446121400505041040005e02d0024034101d0081c040d480c0d00c0c40c4030303c10502c00c4060003240500308a0701e095038140444d4581800301c100318003030a08030385d40006090108626120f034503003140601c0311841c81101d0301c1e640d50500003841d2094540840000c18041542805141420b00030120ba40e586c0c61081d03140c0c0d061560401d00d079407240c101e2044c6040852000325288131020320603d0780250b0406400d002410032030034940010002840f89503c00c034508904e06041e801d0286c030302c03882402940d298504000010020011441e40b6185482c1180181600c1442940c40c43c42118080d0402030000615581803104d41301709020054441c10880e480342c4030751b900203140014801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 383589487 1250 383588237 383588239
    0x20f03011506030207080c01090f02091e070302070501020904050c03061804050a1b0e1603050f1b090a0b0315100c0c0515070b18011b0c081b1506090709080a02 70
    0x1a41da88240c184680c89000385a13040190f542406d440c0d00c01d01101c041c10b192b41900840f6002c28584428140d201601607104000e40940b441d03000080c980790103503028021060054001601e8911404002001c45500702c841c002100000b00030701031a418102d802825102c120f030346040a505090f164180d46002c3d25000400f0700c11034540c44500317000c001d00c104000788860340d00100107080600c14010341401e04107680c0d000034a040e0006540b40300d04901c60b40070343c51704260124101200340c0700460796400000011b030016103c10000504021500003144550302296202140781801c9080011341d8044120b09001c010160360403001044006080d10100ea5003100c01c02c04c01310f6039030041d90950198000141154007003500f045070504049200094041e144802080300c103014500c6003200d00440982c00001401003644803000908a900030a806c0c1c0303c1d1101484111524103d0318502070650300c0d50640110031009120090a022184a8002e21541490007a180c14060f21a9641140c0240a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 383590737 1250 383589487 383589491
    0xc090302190b0f0c0d17042019050a1505040905070207090f020a02061605070303021303120507050c0d020d02060313060606020d080a060311060f1213020f0301150603 73
    0x21415007148401c91500424900005545030522080d200c602c07600408001107860240200c0421858454281e51101030000241d0307038000e846546504880580c079500c0304008000281000c00c01359100d014490304413200318a504a42d5052a0034030051407580d03801041c0d018003245801e4040c0340c0040c00d0380c003520400300300001e2565801c4002c07440c5c4021580007044042c5800460303458031120b138000781410300c800c3e0200c900603128690b0081c4041c28221812000070b005100000000c7c1c03180d00140050b02c0c82d0780d01c0512481c1c6070b84508980184003407803000403600010304841001418400c51456140c100d030314408e008980d8000c640d400702c652000a2041800200150411000e100b103c011690004400c204c000e4076044003a641e00c400c401c3c0396000c560001e001600c010028010704065a034030903080080c0e078909900b44000b030340014030b0f0040003900034000c8036040204c010f800b900c91a00c01d82c034054030301c5880c014090450b18000d2424002d034102440444401c1c010ba081c00d00300c81c111301e00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 383591987 1250 383590737 383590759
    0x50106080f06130519151506080a0207050a05060f011503020c07050409050129010314041a0702070e0a0c08070302122d09010501031a13031b05030d09050f010c090302 73
    0x100702c0c10701d80509114080000b104408901b80100710040380401005d0708010842da10305041090201c1c030403417043d4800a1210400900e04075465000303031641c0340c4660f0880303103020410340d5401e0914104640380301c5001d07101001005403507010791540c0b4400d0940e0400314a003170365488820761034030600e00a15014a84600305e40040201c2584890403908034101211600155080c0f103404002c207004d4002d00180c1403030f510b400c0301c40880080900035030744400c1010940311403095081c0040ba0051517502035000c2c070640000c0030110880a81e1188440202c006010411054041d0404c040a0403800c1051f00c1032081240c510041103da6401416001d06141e101d5452242902040c2d4020f0f040c502120100050008800d81500654141ca12815201b000711150000038120504215140c0040083d18080c110229008201680c01040801c0307600384440d03890340f9007524690003c10a00b00c2e80b0703030786c00030402800350034480300b940341ca04400203125220b41d0300e0008060742e2460001a1080c100300007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 383593237 1250 383591987 383591993
    0x60e0105133302182404050415171005071b03080c130e09100e070e07020a0f030c02031c0905090a060305060f07090e0c0307081005120a050106080f0613 67
    0x5854650303400e00b060705555800611508100c42c41c110303a2190b016480b20405032158004264017146038004058581c6d0071b10b450841003101030f105607940e81032402d49040c40401c00013041c8031140041040d080080216001820310b541c1100e07030081c103680422109114500c400780c98440400b01d0640c05103000541c54403800307600696441840354194038104580300003c3c4083c40b5032010344c814408401500c0b2003010f0400e02c503003034840c031104248807500b00300001d2081110b0b0442941d0086258030440b00350b03900507550582e001050380400d9010400040c01d6070b0852604001004c800e4000d0740d0520002e15034040090145049030003a10702c1170110a0001d01c04009a502c141c1c01941c00908071103060422498a4258a109544880c00200d4188022694000c0d00070b2580c0501c051854552865981d83c5040702c80140c050001c1102c03000074800012199107040d401840d003140c002c0a0138081c2c00c0780c40c1081c21102654000702007600003031983c0c0d5105202081040c0e000440c10f09040b00340d18246 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 383594487 1250 383593237 383593313
    0x50702100f0e060a0f03060e01080309060304150908030a38010c0c060504060908070e0c0327070501181202010f12050a050106030e030909040305090604050409060e010513 75
    0x1860711900003c0100d000200386a001042c0a40b03200303107031000c004e0b05850348034408000c1400d0003440c002c1d6108006c40a03071820100001c5a200d4041d054001c1c1c440b00703001e6444181c500740c060a48100c8000f00512580c006a4070510315104c5451000343c1011081d9a40454003100490100700c0482004001c84c00d16405801170a604981c030a0002c5500c80d2500320182031604103009400020740b256401042031040080c02400343d0381103000c01c40785c554402c08610680c0d4801840729404540d649a01403c500035000e8120050190401901555003410001001c803c41c031401c510318841e50760f40170001000158002c41c400d80d02840c150491b10750058099805011220081101901d400e0400c40d5403181070784008e0594001d070f0341c02e000003180686125500c2c01007017003184c1d000d039103000400d000a004600810a100024201908243da2000010200c1d010790303e0661b0460f403240030840da880003c0c881d070b5038030002c005c2803012030300c0f082e8a035100e10121004181039400b09000700030080c8507110b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 383595737 1250 383594487 383594507
    0xc0902032a0315061204080306060705190615181a120a0b06090403021903090902072a030f0605071701120b0a110a0e040204030803180d050702100f 65
    0x50450070611050344107101d940303034411503072007000000420424425252a0080f500298403841c00c0000c80d0300e482d100d410b12544041c0599503c100100800b02c0004c07010b0124050a00c074900044c5c40440017814010166591203091404002d585101444405d0000302800c90b101220000006d45c542201701d0307002e0052140c3c20495000109045035804954009031501d00b00d4469a03518a20391516402c1c00702100301502d00030b002da000465030000500740c07008031504072400780ca082c01583d541d540c460f400b26413150506407042c00c510401c0303420061034400e8150b00c0d0380c400038207803400c140b8540750341507071841c42c0703d000f413506031940d0205030010b110708031817480500c1032502400c0c156940c0c5801c0031101d5240c80102e8080b0000340029003410180d2160340700003102418141d1400c21003040454107800380000840e03006509110200224103840e0282d480b480c0c42d89481001407950781d8900d407a00900b0801c9400b040070401031400103841d0306c1c1070315604143c1c9042004441b50003810580da58288 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 383596987 1250 383595737 383595781
    0x1110703180f171c1710030818011e020c09040305120c09130b090c090a080d05030601020f0706050f09031c050901030c03050103020d02151201030302160501020a0c090203 75
    0x4016001c265a8000f100c41070421000b10121100741c00e5602c9001c164403a40f2140e2400300789485184040100300d1a511640305000d83d11164580383c981d62404001c0d00424a074406025940c0201031403941c001d54060001800c501000703450b0b11a500009540740407a448250140520720081420540164103440d00c2141c8004002594030305420041029048000003901c11170003000c140c0307400402c0c0d110b0701401c0346000c0e02d56052035481261040899120160080c0c11806545d40017a0100c41030040c506c101141da13440680d40d08101000904c1c000252034a19015041464100503854201084522030800c0300c2e0100d4640c512180020f0510414006030400500c140c1801002035034071200400c800202600c0400000e2010501201191000d000082d00501c090360103402500d445e054807008034248201d80b07454070a01c480aa1103110080e4012005648041500c1d01c0150282c0346c1a4003400c4284020292901d641c0c0740d000500081d4803601110399400004a035612a4043c00c20f150060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 383598237 1250 383596987 383597009
    0x120a06020a20010c03050c0702090103120c060218010e06130909020f13050601031802011d2704050106140108071413030f020a091107330903030b030111070318 70
    0xe1080c0c14580603006901c0c2900010f1301d046d00281c1380c0c1800c2429507414680180941265a09595030644802103030314020052102c1c1002d0000020000d00042c000e801e01030890400030000230001501110764100c4d402d11803401413001134003d810043c00d0300c085036041c2c03401242141d050f0010414201a0820700d680000505030000c83e40740e025001680110000e030780c00c0042c3e03618000ca88581c40f40d07141000b4001484140008500050b0310340c6481005e2008140400300f01074440800d074012004644000e80e0f040c01030070403042c00001e109004c02040300014046070610403000090a9200080004050000032042548400e207464180d42c204407040c03d02003980d546a04101e8a9120318550480c424400c0c40c6004c18401d0103405490b00039818481100c2c142003140d9911409002070855030038a25050615009280103481101d0b12010b0a50381c00094100c51802c00a00380c03000925428040e0f030626104151031140708046843d295014501300c501c1081407018480b6000300c545c80040c1c87c0d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 383599487 1250 383598237 383598287
    0xb030303130b071404170d0f12052203080a0b1c0b040609052a03030711011b06022809080303010603091403071202071d01150507020301050c09030c120a06020a 70
    0x1105c00d6200d140d41b500312400c41c1c03665501c0240440b81481d9219001002404150003098580d000307800454220440140e01d41100050921070310780400216802d900081040c4180565070401d07102d20044204191100745805104600041d82c0341540c4d10300400224940002034240b2103e80c2c00a040035078024280c4100d181c0c003020108070007142154050703800e070000c000c1d250f80d03140000c11140643d07071140c81042c0c6601400010360740303000020700c10041466503408a40000c0c0942c402070000041d40319005080c5490218074041c013a0761440480c0078004500307014003820b0000402e50b41141c3c082c0c900410b54541501e4104410240e900448051348800b0403e402040360300001949031070f03029403c8494540e940c46c50360360f051020071a46101090082e0050140040014021545c50300a06020707207001400da011a00f198070448040150140100b40400c03146418005021108801c0b1100d043c49009030702e40c0c0b6182c0005400c01080c842d0300084603030300f05001e003072007400414005006030116 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 383600737 1250 383599487 383599499
    0x812130f0605150a080705010302090d06090b100b070201140c071d040b0f0c0403030c020414070306050a09060e0f1305030d02032a07031812060f0b030303130b071404 73
    0x182c002903503e00c820380c54240c00b000c4181054541c2c84100c8480c00000d01e6040d180c0b8006400951094a40f10b0f040034007038608102040b580d024030405070303210740302010b40d9283c841d009100004141e0001c0080040400020005d030fa80079112500886c1c0e4aa5030981d10142020b2082c81d0030721039407200c2010211940c0c480840400107aa0034415030050741d51025565032110300c4110440708889010b15481d00340418000300348160300748480c4603c05000000c02c0704d418210700c3c0d080c80b000ca50303003000281c45d028144514104500e1050091014681c24001a410b0900381d012598009094003103601580d000202201d50380c0304c01183c5c05070403105484e510100c071900700c4007035801180c03904d1400058500d0b090100f03480e881c0090080c1341c9080740c6800c0400507a008c4810042d60300d6400e0060703820140115001050b1100e10f22100e03ca40300000390000c4d0580e0b9203068455035400a44030307800901c01c008210f000d40d0729009000f603005440404075074a401060303448c52941044522110350114000c585 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 383601987 1250 383600737 383600741
    0x606020a140f070b0d110414040f0209030d0323040b04030e0f0a090903020708010501080a0c050d0c0b1c020f0901021b1018050303070c150c0812130f06 67
    0x80314081d009200c042555900311990302c2244840c1e00469034030404040000003280340184c08511032020002c101c0c0c2d403144080581c01e42281d08108180039004d01c01c54824501485092429204608290b040c43c20504c0005e4607a41e40034488020306846140c2e0100506501079204050034100b048a1603070706040c20300f8001301d10f0850302200464400b119060f42032818046640340300c0d02c02882440081d052010b1040540b0790103604400b07600c038000d8040307480c030700c01c0c054240a0181000103000c21505410001701d00d00b15540014062250f0121401c003060b1502110001c2e42c49200443e82e03a441c0380d900928500d554004002c2c080c1b480400c840f0042210301c001001c242e00240d00700c501d55031102662100814451100b6a48046801500c580342c1c0d0244402c482c0399220388096440441d07607000400e00b99442020202d07003001c1c4005090100705400d903800009604145400712007180c203583c3c2c44d03540d4030070041940544900700700002c41c40b91b210340c09004150343c49100802e00d20002e00e09140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 383603237 1250 383601987 383602003
    0xa0206040b090106030c031212060803030916081e0f0313031103030c0616020705061207090b0304050a0f02041d1b1903020910030506040302030a0f0c0521040801060602 74
    0x2446a0101d804110140d80500448058030303006003540301c080e882c40d503c01d0341c02c100610070803060041d00b00f01602c0c400341d0361003400c000307201d07940c05180d03a482d0114010307003007030079424100481c010750400034401d400c0001441c0c6940940800015061000b81180f18035000c980b080060042c800065041c040d10b640e056031104403882003501c4480c03c0042da04058907405110b003140150360140300019003201d400034048200c00c1a03401511f884544503030100d001540000541400b5013840402e001002e40d01c41c48103c000c200c1c0d01419801c0d0300b441c1d982d194a5843d10b02c4003410720009030840809550b2290f12151072082c0c51a0010185d10070185101d8076038503a1245152110b941607140c0d1036501300940101c9172000743e01440329106045900700200e62101500051030300e401c055001c0300140d410061940618060f030010354444080410091180c544040d10a080091441c050400954001284014405d58603030034910218481c0c0d81e08541e0150340e1142040e90f00b081c100080310741e000f0071400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 383604487 1250 383603237 383603243
    0x2301020717090f01090b1206120d020102091c03050304080c030f1b010c020c0d0b1806070203220e0403052b0b030106210f03051c05010e0a05010b09010c03030906020a020604 76
    0x10200252007001511494460300c100702c1c001008000001c0880d04031192032342d00c0071000f80103003503111242e03441c02d1a2020303041442015030740c0000c0d420b01d036207084100009801c0c000441d1781c05000480e80c0c010258000500003d0849a0100700551000801d000b40c618020b00c842c1203540318188080a60420b01a070954002c02d94600b11021060310f10106891022540141650703542c0103032030b42d90424000d00280b0818803200e50640b03200340341600344640e0b0700070100d07a0300840c5c40705072880c40400da0030000440039441d43e01982040150b000b101128650040e0541050782d210300d43c51050a04e56001c0c6055a03c0d213511004000d41030480d0b59004e0a0800c2c0705800820503c1d4660448a1402c00d0594400d00c101221240303420014240c41034040940f48a803400500340100c10086240c03a4102d01e400d00345042d1108014001e54000400841e88802010001c1c0401e5240480c64112840307105c1031355040001d401131044c14180a40c01a00c1125800001103542c0c0c00c0485000352a1002503d0072 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 383605737 1250 383604487 383604499
    0x9032206120e1902030a0c06170a0c020a142b0905030a0c05040e030d0603080304060f1b030b01051c0506030d0203120106050a1710140607230102071709 67
    0x400c103000024401d440403942118000c2440d502c583d81d0a8041e5002804102d92600c40d0780308481c00a101002c822004040d00c0c1c43e0400100c0218035020042c06000b801180c6403441c046441d408203900142c0b08048a40040b901844c07040502c501d682001c03098084c0c42120131003800301a4482810200400d04904140c2d0380020b40c5489104054846811040c090401c11f1005014006c030300e00340d4007051080d06d804c03080b40e280c5030507070840c4c8041d101c4560042d25040e401100708020710075103025405a16009010810220f80381155a501c91785982e01d100080596406050031180d008004407080e15110f220070001d10b9042d92844805004115a007a00038056404100e00c0c0c240000103030740c2d03251100075114140c0e0f801c1010480b090742003010401c041185815168080708501c040740c1e406010105032041c101070400304942c40740c011044807180501400c215540201c0c002c456640698020002000203114110303c6240c0079014500002d0400340030001002c44c010313403850040644000030707114 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 383606987 1250 383605737 383605757
    0x2303070809010f0903020a0b0a140415050705030103031e05041d091501030b1801020708040b03060411030c0a080411042a050703090605070606030b01180509030c0304030b09032206 79
    0x30070f0b01138402a03500180544d0004001c807001030740400510341d0000c014075000071420841500c071603514509030780640d102c6600b003481b810440c505001c0c1d03591028050070204d140d5455603030010010803801403030342010f800d1041c0c2e65503010b1060080b10010302010301c281101c04103d9020300d01c0c101055910201a110390084014644001c10700d80307040703d03080069102c2d42c0da103959095141c050759403030b0034041d55401c10068000503204130103400074107859002d40b607c03451704005000443d5507040307105080500503c100305001d14840100d8001d540107203001c4200f034446140440c030800154a10315405424400d00010484107289290103416606807540d140d02000d00003550517205030000035001909440c2c00780070090141c030081c00740e1485400006070382c0c0d54a03100d0700083e10003a00718010301c0041503209081d10180e4043d0715013059400001c0c6241c403055060007642c80c895480020215a00da20000390000f80074000c0c2c800c201c41e220b0305128000c11070361400006121500801d808502030f280 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 383608237 1250 383606987 383607011
    0xf01020a050d112a0d0c0f03060204030506060108090c011b0b010305010912080408040e0c070f0b150111030405190812031603090f03050903011d0303040204060b0a08010303230307080901 82
    0x103000641100d000220100002c001307002d01001403140e034000c1d13501c1e0221250014182998a44c141c005500a103401611070b800c5241580c00c0200203009641002034030317010300031403c00111b420000c035282400d04181840000d1001581d19098410103041c960400e0000014441c064004200382c9218a0f0440003100031140c0c01d4074181c60a40e80030345104800d01003804040b024070422900015640015402c00c0000d0b500c2c00e1480d610702c3d4086a041c0010024803c418815a91180c0c0d141001d00303204482a40c01e400c120f0340d034002c1d03204891041800e070f440750f008a41c601080802070640c46040d03548808024001c3d900d55442600c0081e2260103111038400200d100e44074441820790710071030303000d0245207540302210300341c220243d41e65143d540d482201000301c2d014114603049074000c40180d41c032481c0c00e0040204862950b40308162050041000711400c0d98070003d0305040d44d905003802110300032921300060102c115524010251000003003402140c83e0404030a41c8070700e111760020b01503811252 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 383609487 1250 383608237 383608273
    0x11101506090803120f041e0c0503060907030203031903020408030a02010b15091305180706080103020312030f010608100302060d020904050114150304050f070303050c07150e0f01020a050d11 83
    0x4c003443c008500400f01184403048030907500d40d0018098001e494031a0203003005030325488010f4801b11100c0410500070401418140083d56020181c0006000502d00e16004070342c8a208120000d0940450f0702d00f51a0701c1806541a44c0240c0314440840751a08042d1030064000c2100304403a61180c2443d0810f2480038070b50f41c0c100c400028000e000500800004584000540005002803200800d000c0711406242c0c0308204042c024100c540d1021000d514500625080001030701c01801c07001c0301003003041114096071051130704540c82c51070401c400d0713550481012640c0005800003548100001420000c1c401c003500a4102c1d03070400c540400c42030341d03100300c00502c01200040144d0440313402c0c6d1403c2c541e0f50713003072005d5940140180d0958620442c1581705c1800d05030590001c9010610101d1407402054081000501800314a440942c54613000308006e00440014a40d00c2d1251b01000010b4106034428403080d21800d0f480011100c94401d0b400c0041c102c1109050b0030716191081c2100c0304e070282201 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 383610737 1250 383609487 383609497
    0x1061206050a380a120308040309090e070905130b06010819020a050a030f06061202070f050303070f1725110141060402030627151f11101506090803 65
    0x212150441c5e2040d035019560504002c2040c1c050200310180010300314018011b4030015181740005c0d00386281044811b004682e0f000d070801d07219100701d40003500041e40b218034089e04000c09080440e03043da00c1103002e5192042008a501c01c450011a54619407030f0420058024007040e520117003c0c100c00020140211145441904001540740124690701d081035401020b080f800340c80e0700c0c0d003d0081c9484944c91070f88182d0754400054804024240d441303500424062480070311600c05080c0741030031910810080b2840760140c41c0352000c8505c060103903000326040481c0d00500c0000784060240013580c4c1e90001d003d400005054014260040640c0014004540b161101d100d50f8400a444d12400d11009420082840c5d0700a0b0410042c0e0500226180340c2c90741c52000004601ba4529000860b04c90030b0070030998640c0103202c0c13802060303a041203500c9241341d0070480b890006001c41460401c14034120b00e6981840310035180840d4105041000c508102c142c49036521001c0020b5654610260f8910035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 383611987 1250 383610737 383610749
    0xb130213061e1706040b0a030f0605011d0c18030a0302010c02070603060b0d0515150a031503020303030703091b0b07260f0d140a14010801061206050a380a 68
    0x70800b11140d60018240c54a80c01c840d000c5c1002412403030100219621211a8105440000684042c4070810216000b683c1c050003401d4071a0a465035640701c89494510f019101c04090800814150b00d141d003070710040001d684005040301c1502c0410300b000b80c0200150345146006014500e00400d00d603009008400c12035140101041c5040c4502d081c503401040040c042171092090001c1d40c48040d668090010b400030141890196134200410000e8100c032014050326000c451040010005642c002c002e4917805191030402281d000039a14004c05588413107035443e07941b25544080480c4880161001d440018451110020500008420742d11458200d0050604d071340802c00242ca020340b00036001c0d01f44442440d001064410325160502c149000c101c80250800380d0b0f5032600d0424045d00c00780c4030f004004010003004600d0403d801501c2140d01180c01511007034030755010843c200d65074ad0050600000401c580c0c42c200200362040d1010413601c00414402c400b000041602c00e14114010000319070f5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 383613237 1250 383611987 383611997
    0xb071101050907030f05030c010e0601090534120f0207050609160303050a05040305100b0f040b01020d110c0310050403081b030a05090f070303030605010f020a02130b130213061e 78
    0x1c030390740c1c0b45e4400301c000c5070301140e040c0000d1042d8410f8000c240941d0441e03000b0301c1d001d0821503041901c1c040407201d00508400c041418024a50b0005480400e00c01660044000c100c0001100030016150b200e10000216202443c29051000100301580039141c840c3c8108256041030311203044e0070742d0710b40c4c0380032815060041e04070040001a0050000f081008020b003880b5007066134135150f150411202030b80c101660798580754803500510341114820201d65003207800704588042c90000039500d60b0035054060521500c450390b03a107030220402060900030402002c455000c102407003c10042d01060314102c001c20142008194402900c0184076000c1114203003650865803001c0900c1d02810b0064000d640f00d01900c0d0011032004001e0207007601031070094602141248c84e0074001010213400c00b401800310b400c1843c00308016611180401c601d65054a00030071001074a500264541c01106900543c503071000800100010100c059a02204c1154460801c446070007a41c203c41e240c05003045600040e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 383614487 1250 383613237 383613239
    0x150f0b03010608090a080703020601181506050d0e010e10061a0702010c0c030b0702060f0c0406120b041b0809150603061603060816231507020d0204020301030b071101050907 76
    0x2510440c83c0b03561010044084403000c4030a074a42201542c403011050f130041e04030f440148102800701028070055460214100702c0720f40c0c00e803011440130119004041c100400000e000b980038460b40c0090741c281c0e01541c002c0201808210019954120000020003070070f0034400002850801c40000001089a1100c1a40741401702da00451f104040720908403021807180c007011020a8000304841d1099000c2d80040045041003c40d500c682040241090f40b0940d00300000d214036030384402030782d440c1205084082441382c5c1c0706001402801d5039a06d1782048120088080002d10342c0b00e00301e940281100010344a09220842840245400c11115503406510440c041362a8103000c00c4048402d00052400140b102d445135011401e10000c4211003150422245017885880c420300100c20307102c4e11844011100140860115508890321071000c00409404903c100954407000b216444035a40140700b19a25a101d03e001800e04805a84500c001101411a16030059052086600400841c0010602031f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 383615737 1250 383614487 383614499
    0x103110403080d02120408120c041d0c0d1b030e010c05070305070c090e0c030c0a080d080c1306050c06060102070f0b090a180b0909120f03071809150f0b0301 69
    0xf6448541a010074503400c10141e80f0203808240c07468000c5114809180c5c0d1500254110a0240e2014003080c120060801042104040c2402d0008458030003001d0b015140d6958a802015409a44507040d09141015081202c155450381c20b54030045550300c1c100002c1051030b0100d403c0b03440c4c0450400210310108041c90208c0e0080b40940ba11500c2100042261030302c1d90308160540ea90714000c0c52140d440408030142c6464180311600c9508000d680b0180e0a074901748420350b88280002c180300c18003004601144c2e601e0040002c80c0c2e0f05030040004a5512036031410300a0207a482025004c2c0d10f4000e02000c04e809600c00700d030a200f112540c03801c010005003040d0407000c02d984180913240c0d010002072000950f2041124062907542560200000e455103c0c0007480340e03141c0000d0504010744c10100c2c1184000381154256100b4408001c8000e80b2070b90b50140595500d10302401380001c41a0038100001c028078190411644000088009049030350b4595401d07107004694020708000600510052101c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 383616987 1250 383615737 383615753
    0x60612030708181903151409100b01050d110307140c0d1202040911182209060b0613080f0d0210020304020303070f0c14090402010206061212130e060103110403 70
    0x34850082140080600500d202903034211280d000720341c406c0c0f440402c01060340c11071280d5042d024034030b0b9034205a480c0032004962520219565840309580e200403844269100310203450b03d0880c2c40c0001c00c1349803038851036581180c10881d2a075002a01070780f03c1c042506024030035640720744024030080841080b13641c4252503201c0750781200c0c0c200c26801c4c0000210384450b401680720355044400803507030301c5018050b11824a0520b10302c01340610a0841e28020300c0307900e40b5182c48003c0d0352500004a44507186010b02c058001010b016512003004140003081d1046d11410000325100201110f20008059241d1a19084100140c90140c1c002c0c03240d148280b42150015035220344010142d174907041041c0e0790b0200102d8140350a03035540881c060140109041e145440f00700c18011286042e403842c0550000b0750350413009198502400c0c00e403040c814005020080c41450761050000c00d610740d200d40c8000050b41c1c1d40c5200301103108000b02c000c500554081d00c035080b0312950308455640350900319103551071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 383618237 1250 383616987 383617027
    0x818010504050f010f121d100509070303030902150711040605090709180f0e100c0302090d0f0c091d010b100503010312091a0705012003190209040608060612030708 72
    0x5108501e95000c88141061140c003c00d011502c400d41e203601c1c0c0050747e5910381043d004044200601e49010300041150019016085980c5071401040408851010074481c003212006c5a2844d0400f003000010420121605503150038143c904018072641d03501000000d020a903003840100e0018002444004003002d4800c0c24582004c4012800e418501069411034210703c00711000d680280b80451000c1203a03000340594040d2614040d428100d004002a00810020300001e04100a1040401c100025445001c0080030040b504200000c4925607006521342e0b0001d2008044d440d04807150480d1900c007084c40041c03c403507520182981c1c2540d440030030100c01d28071500144480c62000042243c0407454a500c80480303400710365103c0c02185806421345003c0800c3c200940c03020015100e02c4c00e000420760703510400301d05c001b100c410401000301009225800d60a6001410000007081182000400034025901901c9440b01c0b981146103d0b030f201e019843c8010041c18040007000d540c45c3c6040f801c12 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 383619487 1250 383618237 383618267
    0x204050f0c040504241203020607030b01022a040c0908010b010503011a0307140309070f120f02010302030c070c0807060809030c190c1203091a0a050d20070818010504050f01 76
    0x88045d01c10020403802143d91035001103140c0540140b1101010b0341407101d42d8210241c2d040610800c011180042d40f40c10100403a81c0486240544450000742c54451520480c00040e108111408806030300501310b45032030160341200c1d0708183d804213480d4460800c4030b04a074060100942c5000403521882d040d940060210000c0000d00383c1c40403150814003000b14041d1500c08000d06905241410740d820745507250740508600ba000000ca4800305501c1d05118a07c10390928005943e0341e640d509254040c010000d024000b04451b0402240340310000071800140d81094075080f03280c0d0f6034014016074070300c650b80700384600e80c0024100041c00300700e24414000043c402c0310b2200c04227496810310a4071000c100000d800045620404010b03a40c0c90300c0d01d180c400c1560602c480d02d8030090308005016441011980012142d1740e1801c0c0302030001c02c0d5500008d880d5056480c65031a1039034201185960001300a075a041c2d134075110840c0c01036006d81c007114101c41c0c01401c00b110708207841c0c00545042a07511081d0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 383620737 1250 383619487 383619521
    0xf0302011416080301140f0f011704060609180b0f0c04030609050309091f050109050105070b1005060f0715050411120a080c010c09050a0f120303021201030f0204050f0c040504 77
    0x880001d0f0000c4060350103401c0042074440a6241170307003000604941007581501400b1001526811a42d00003466407000005160f100351a44a501d000c0d4010310307050740700c2158140b80c5030341c07503258081c82c500d214041d41c01503401240c981ca52042c60320128105485859403c0410041040011903540000c010a070140041e03e04040d111301c0462849481258000780306020030f07034850b00c03000c240010540502000e28244018a04082c0040d051307102e0440042c002c1d00c00000082c841840000320100a448d002d0122900c0343c00d0b089524280741c114072011142121440e4a2512041180c461544900c2c0c0100720250340203104400d20408422800f02d00c4a50b009400844000c600250002e100c2c41000d40000144031000d650000c2c07414030240c005601c00e05a0b00b41c20800c0300302680e0403900b81d90000f090200c00601c2854140c001344500b085486080e08402c00020604c0030410000f82e419009490a0040c0e95460350a2080d8080854140d0f903c400240018403003810264419241c401c0e0791125 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 383621987 1250 383620737 383620777
    0x120a0203030117160f051c0b06060c19032109020a05010c1119080c150717040e0406150b0c0d180b07080705010c020312130c27060f03020114 62
    0x43c0b00400c10b034001c5e0518501d660010011070401100020428058415000218405541d00000c0c5580509068410078012681c003600403c1807000c40b800650079100c040a1400910340a4120041e206224000554031900c500030000c2a000f9000e6060b40140810400e41c202001900d81580d0780800351824080354031410040c1d110341c0280d00c042c074008041c0800c00c0d89007807400e0b864075891101460140c104501c001d603021661b2001e603416146d1003510704131021404581507005010301d6000c26031100120043c0814044658070400c14000f114000d48101516201c41014070310555001041c160b2294500f418014403900c0e40700c000c4409542324408095460792000002d4000000c140e40003000002c80700e00b00907007441880e0500c10340c3c0c006503042c060403d03191074030a68014401c00002403200308550030800d822045001402a0f80700c52007015250250020b00d801c51a0507000c1d000d480c00308003080700303042403d80008403076050359036506880c0107100c45141078000d0607601110a1007905 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 383623237 1250 383621987 383622013
    0xa060f02150408190c1124070602070503030a0204030c0510020a03080601120c020615120709090219031406010503031903151d19060e010603020c10050c0408120a0203030117 76
    0x140b10510180300e662030781080104c41c03c0440100342d0500c143d502c03501c80e00102ca1f035040d01303200d02806124009250f80b929540a0b052401c0a480741a42c01084c1c0d00001080012000786640600281c9000b0702d6100015510354061000701c07141404210050b070310410500b40020300c500401903201006240c119030381010800080191069200041c0268002030100309444265080175000340c0411248072600c0008660041e0325082c06000325002181c03503002081c195102d031041a200c4298030401030030001d50300d00740b51b8840c1400030140000e03801080000600c03441c00000355000601740c040090030f0f5088000054004051100c644642c0924191002489511003514403119888000701d90307915181c01d0702c004014203188495021210b1401d541880400050400581510308508005a41301c24503400c8503c1c2804014582e5003d6040c50204660030321404051b100f1038104034105d48070a5550268113000d402040030100040e031045c07004100079120400f6048821007171400795580569100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 383624487 1250 383623237 383623267
    0x5150118051b030a0f1b2303060a0506030c040f030f1e050c040b0a05090405011508010c08040f080c1c0e04050906070c030908030c03030601092102010509030304080f0a020a060f02150408 82
    0xc040003140c0300c00c81080c4600c40c8000c01030300301c40ca11f0b03541c1ea20314500000080d4980c5402e000e841e016910100000d0102e0750040119009021300250201100b40c0d00e141c0040070407181201100c0e104942822000c80d40c569a00c0d0805041d803002c064200700d5240d50610000303100c002c4100d50701c6104030100040ca03889000d9405d000754041c00001c01d4084c000c2000981040881e8400181685041e0004070516070045580c1d4000740d00140c440f80c40c80c003900304101c02e4000d58181480c01d01420841460301d0440c0d45c102c0c84451078503124120301c480850208021148100e5260f42190895030000300080e12500c01504068424103200804a0725010307000d145401001c00980c15a0000040c41040d42c5c009114500900d40c03000100185410588030040d0b810346d0481c0281404004602403110340e5050050382e0150624808a403440f2040641ea0340d40c6096a03001a03001e0300b03c082001c20451b00c21802303103400490b1a0000c2c41c0c45034542000301c0d02144020002c0d00c0016061003052400b00c588 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 383625737 1250 383624487 383624531
    0x303090d05030307030b0316031506030602180108181b0117040515010e01080d20010c0302030f130f1101090302180901050a0501080d0c05150118051b030a0f 69
    0x300010360b00e034138048402030120380d0060b00080c0f04c1da11209400c1943d0b0b210351700b190103807540142841c1c01c0d0703031640c00306001405042e04020433050000c00c083e40d0782c4200402034a8120301c241c4c1c0d802210380360702c8511040102d150b06d07040d1080c0c00a81d50068600b8460b01500d000c110180760402c007448a00340310032441c0405880132107040d0484071481155002c055165030142c064211110925494902c01d0b594462111000c40d00380952555130491410321141c1014403011508000d200030400d00c03034014025070080b140107a195540401150030080c500101440b6035030b200020200e6041c0c982c64800c4d1803004240001e04000c10020040016100c03c510341c00f140e1b4248250125a0901c802070078292000200303440501441c0400401c0501d0001507121000c03d16800d2492080301c282c00d10500301400405c0400e890725211000180300301c80312880d5110b0880d40441040301e92140103000040316298414007460510174004101803c00681c0310384140080d420f000146000c10501c580a800c00d6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 383626987 1250 383625737 383625743
    0x2091509010f090f1811010216081e01020a210f020406090602011404050705060703030213082d10020d0b03060403020c0f0906060a0c05070807180e011401140303090d 73
    0x450042044041e94074000c0c0b004051201005000380400b103410244591040080a006d4800e10511040781d41d0003404009051000c82414010058440d03441c99078501d45001d032001144100900c00d6a000c00600c20b0300c10705c40340d070340d190b03488006601e60f01c40e03c000b04606068a2b840d0b8486405406582900c01800204501c2d203a000381d00d032820f0b00290840d000e200c58102102c191008000c0002d10200782c2034142c4500315940354440c00e550504a001b4011401d180c1e401300342c0031070041510034000403450310418828094500070701e1442c440c00c1409051610250465100c010b02c50400c03802c0b900030f00b140501103000001c90421001c0040e03c0c05205890a6015800840212581e81410b0300030185010081d180107540c0cbc00d1507004503445106402e0f0050420440b61404c80802c1800d000c80402040000201d070b2050362200180040f4206c1c114500b82c0c5a0b18180c0c08110f03181043c007600a40c1380c0c41603400012a80381c4054030105d0b5000170012981404100b12108003550303180d03069120980 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 383628237 1250 383626987 383627009
    0x80304030e130e1c230d0209040501080a050d050f03070c080919050405062e030b03061504060611100b030f030a050c0601171b0d0807141005130209150901 68
    0x413410400043c8102103da6100402c05483c610880e007042018060030300d1a10044c0007035440700c0c0c503581240280a102d1a46a0090400c2c0000410000010340044100e010341d0655085941009081d03071640300c0c2202c00600ca12007132000441039406003c2d441800342c0a190f0740d505c0c2005550004040d8050811000480f1804810501440c189841460380c421420b8518000340e80100c0100d44414555186404901c0b41d88203800c031849100b500603217640700019003141c18504000c851110011014403000e40200c1c508240019090b110311220003610041d000a001014400c0d010100540b21b000025034141c894165402d40d590000c00041002606954425031901c003640d10640c200101030303208181969448410303201000d00400c41140c00034131103803001c02030400721010462542e81824080c10310303070f00824a42d042c403d0700500c1074001000801581e00c038030150030f0480119103094503900c034a04141030b03a00006041c24100d96130400e0030341c1c95904583c00440c000a43e100800d801c5100d10007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 383629487 1250 383628237 383628253
    0x7060203090c191211100210050f01060e0d1a0109060609090e060c031e07050306031501030b010501121d280b190e060403050a1407080304030e130e 65
    0x4003040c4150010303a001240c034903076111120304000500a00740d000e031040c10306242813114100100710f40590000e1300301805130181001c459501949442900c002192454200b400060040b038070000090705803052a21242118682d100501603417119400d401c5420f000301d03002141e5184800b0706030600070000008040f4a440c00e1410003000c001c802c1d44040b03081414081064030292000c2035172079001d8641101140c0b01d80c1d40003542c0e81000d001000d118441112041070100b416803140045114070015030446040450301c4c0c0104e035070f40d030091001406c61410080140859880b400ccd006100e0020100007040600500c41c40c412a1403011005442c07075441035921444105002d1168011548188140d02007000140c84550351550000e010107404004011031100311021035005846864070070301240c1c05403520346800703051540724290110128080408000c04110628200ca00040d44030511904548071036800341e40388002000120340c005140c142680884c095481086800c903800750041c0401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 383630737 1250 383629487 383629501
    0x5030a030e03120a06140103060e07030c050f0403061406090609040b0a0e1501030302010e030a0207060f111603020306010b0a0c0210090b0703050315010e030a12031e02030108330c0403060207060203 87
    0x660310f1800c211f05150070702004102010f038204e1266408541400c001c54080d2278480100c89a114500e50039568140104022050004560080c3e1301c00e40e58107183c02480d00e0750f0042280d8550304961481c1c2c000c40030350000380040c20048400760040c2126070041841d0b0809013519080c139003420b40c5502c40e0010710004200340350342405500142401c00b40510f141801c000e9000391101c00d240920410704c03a203109488069071140394114000f180d1401580d00010041a0500e0842c0f50b503c802d9120f03100303400c000300d0340040500c02c8404202154945040805c0302d5400e104250f90610814810321141d81c00000718450034000400900e8400c1d0b0303641c0c1d524030781885114805804280150304200200c4031244e51a240050b0012441303030402031001d00469604c4085000c0c010070908901204008810940d00f450180c001c0d5060321080d4090360040d0340e6182c013065010320100203110030002780520144a43d0012003441e50480200e101452519460b51074002c00c0c0e03448204100c841d154000304201103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 383631987 1250 383630737 383630759
    0x51f1d010221090d0806011404080615040b010e0d06020408060906070306093b0d020d08011a1b10090804290f0a02011e050f0106050705030a030e03120a06 68
    0x20b681e4010441915007041c0003010380e00c0310500c54600500050102150607030707014995420209045401c03643c2d60315200d0b140c540d1a808141c4000a12041ca914040c421340742600a03031900920680d41d040d040c03841c220811808240b050416075000d5801c000c081102e180600c4428442d2104000815881c10050001022140715a21850010b03140a00c07580301d200d0f0800713481171440304010b4a04c1190b060f840030752042c0700400014107076a119550025200540114000309880d1280e00c4d14083c036030382c0b0710000e0342188410500091050f810044800001d11007082402000e4021044526138606d00d121a01110002041a9500007010900308031450140110f2a049071500659100d10600b070301381840680540911160340308400700d82519820b2003540070000c804441910006400203141484006210540d180202c5840e148004103040f4001c00480700141d43c014029032408104041c110000c00b0f00580d03034586408204503d02d126803440055078000c01040307000003441450a880303446 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 383633093 1106 383631987 383632027
    0x806040c0e0316081e0a06021605060a0b040507021c030216020901030606060e0105040f05011202070f060b011b0b01050d050f0312010e13051f1d0102 66
    0xc2c05083d01880102200d0500f0281d81105c0b00c9840c1c81c0a040b00004803481056104940401c0011350726030040180d812103da04a1031026180d40751801c161081d16042d5040d515002081e6003403510f0300c5030540142444c00140f40120140c0d008202d01c501d801c24940605502040610566510700c0b146220164002c000c2c07940ca40c5c49291400050001d401080c7c002091007020100550143e02102e06132a4012056132407107260400443e05100b0b9450703440c40054090281000041181c00e009085038440c3c1d01c00310301421a0b02c0010700e0465150069010754840e01094808100d401501505440c030680d0800c107200524148039142c204100e070403003458440021b944c035114003460b0300c0d2030598960101d0012983c0b1140c0414650480c6064080d010381c12410508880c14105414020750f0103072070902085490501001c1c09184490754a51406a500020850703030903009014400 = true := by decide +kernel

theorem cover : BRFrame.Cov 383453237 383633093 := by
  have h0 := BRFrame.cov_init 383453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 383453237 ≤ n) (h2 : n < 383633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
