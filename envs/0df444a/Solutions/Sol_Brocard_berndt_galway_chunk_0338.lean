-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0338
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:17:29.777859+00:00
-- url     : https://prove2.me/submissions/2cf225eb-18b2-49d8-aca5-16659beee0e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 60611513 ≤ n < 60791370 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 60612763 1250 60611513 60611519
    0x31009020a0c06230f1305030c0312010905100b1b010f06030515040305040b0c0a02121c05070201020703060b0d021503011401090503100b121606080105090403080105040b010513 78
    0x4000050b03107103440354109001d444000d280062112400805603100c2c0140303400007a44419081010b15480785140d5846070340c0c061162220341c915007040308126a542d100140c1e082021003101c00c114010f01419405000c00d00d85500c10f211401440d02c0741c800c48101c04a5403007202d5808040c0c070401ca8503110001c124069591039010042c000c070f480140c1395401005001d90000e04004e1601c0d201e6501501d603145498949000908a03038041240d0841e10f0184101506c0169140300310b004200c90044000c05242500b0f0046410b0b0450402c100018001c0c00c121a13001070742c004c0707144021217411480c0011f0814400340456444201010700a500009001a0003e210304c00c9000e1030580d03004001918110318050019604107045d070103030302d515034030405456a038903509400000038400080d1a01548020319440680303024841b45025140403640034081c405281d00070035070ae00410044401c0c407018200360300c0103828200e060042a000310f03102c801540c4981d010301c040301c5011010118015695503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 60614013 1250 60612763 60612767
    0x90e06060108011d041b08100504050f0d020c011b02030d0c0302100603050717030909040f0b150d06051b0d05180f12070c0b04060309020102060703061a031009020a 72
    0x10032910540030a6140002080c040c120b401820f096244a614241064540d5110b020300d00541c03c00790b10458941200104043d40b00380001440340c170040f01c010465040034640182003588070407042d0503642c41280c4440c001070707001551040d00403003800d000b0034076040c40c508c115905201c0d890194061242c44034091895a0105078111000c4c001d03425200b9a900e0b22403c44240c1c0d595110141107903005010500440d1070a03440d180400712401d007120701d071030005004211143e0f401c40b400d481664045480300280310801c00c2c0c2517880300e0325a41a1144003081d2000a5000100c0c1001030f0050355a9030005205000c00444600c603000c0b000505070301c0f4145110b44001814089a001440340340c040820125280001800320101000a001d0b02c1e58020300d1000c8241c07a0803901082e903000c040381e000010303840c1c3d20000420182000d69000b01e1180c0250001900c2c00001030406410146895010001d0301030b204c104022030081d03002003d030360f5103914564170b40c140000d030848551944001201c20100b6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 60615263 1250 60614013 60614023
    0x90b0a12121e020c0103020d0e0703030507110a0506030c09030a0213060915030305030c0c120a0f020c01180506070201050d060620030c0303060112020d061e0902090f0103020310090e 80
    0x14109940303102c0410340c401491910700d55051418000342c3c0c0061104201503000380c01802c0d528404c540c0008858040e200010314007099940103601058001400d001071006500d060230045000f900c16544191a100120301d4500c001441c0002c50140402d10348025078060005084058004000d0080302000305403090040603640701c0c08420f02d207401e0146102e0803480c00b8850480390103499035400d540d904a01d0f485240e120f808030581500a41c48002030840e1100080d0182d40b525a40304400c464030b04001918090305051210b040c010301c13040c0442252545210340003914010350b045a21106984010b82d414020f4110002000307043c0100460502d501c01c0700d48078408a5406c131100a1500201d00907182c3c400c620f08040c0f240c001304009156540200110310380311001000c01480c2031100911002126444d403c004140c0580d007940046403035245000b603000c1e0041c00e01c11898004d1071000180c4101420050506060f004800030b154900780c80100b0b001009810002d121400032540c0c4c0c0c80c0c40e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 60616513 1250 60615263 60615293
    0x9030815010905030a060b03070f0303090311060c0d120b04050c0d14040c1208040506070605150402040605030a05040f1205030105090a060608040f0203013801020102070c090b0a12 79
    0x9900c90052000d515031103108618101d50001d4042d03c00460701d926544042c00f0003000c1c03a500f510030344c07100146816952540f04001c500035515905640d045107800503200201160203486400c091083c4c240412003c1404c9042c038182e41002c7c144108103894020140c80340e202200d500034030b00030401071076045600c000c090a2010f4601041007900d1441911100e1000340ca0182c50b098100c48140101e101012007502418010b0102c1810b01d075440c4001060303a404602d080303e015071a40180594050300220b0049500411581982003a041c25001010360000a001100346070700c810100d002d01c907403000d082d038080b504041c1c201001c24070088080c0c070340da00c28801d4500a03044000060301904603482840240c1c1c02a0ba5880815200d86e115190343d11440c94060b6455580c605000210302da100440700000e20b007603079110516250201548840e230a646010505690040000704002a413020598080d1049101c002818490403000710b41c1003401500810003012110b03810b40c080c0b005400000c40c4c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 60617763 1250 60616513 60616531
    0x1c0504080705060715020309010b040509030a090b0f1c020702031516050f03040609050c030d03091e08121503010f0b0f030c100c031725032a050904090308 68
    0x301c1c0e0380e01c01c0c06600d114903e8060640c5c140142c0b40c03caa000560011a040040030f40080f80c510040c10001d0116a01a44e880d5540c3d440050f030b582d6000e4000102c0001003042c2c01c1c003103040c4820b40b020420f65100f0041510320080183c09600c0c00904568141d5200341d130003404075001c0c1d9031008040000302c0c0041e6204400d04007030020780a81e0a1049007160f02800c03000c800316040d41c6481c6d49141c0074107000007084403103001300405180305440400052344e03150303c0d5640101e04041c942c1001200b0760050919800302104d05109140400c14581c12940e65001e0820074062036520781e140c9501e044c4ac2015102e5140d401d01d0803400d00740b40c071900030098410003100e035a055008060101543c5031140207005030400c0803070f0119a4600d00441d10440d1442c0a400c203400c26844e81106203a1282c401ca582c1c10700fa8075804140080c5042c034940a001041031418104061014014030380000610241044a90302400035010300051048060700d16000340504240b1241980d4a03006d04180822142c480c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 60619013 1250 60617763 60617773
    0xb010e0f090102040302030a080f07211106090a020f01021204060305010906060f0207090b120102040e071115060910030b09010c03110909010b070f0c090f060e01030b06010804051c050408 82
    0x1020700601c200c4044a900900408a000c159030b00c21009400c049e580408803102401544c002c201c20315074a84049981020505084840203006002000c821409102650000041140840e0005104840355404030740c0d4840010030b09004034600000000940c42d844400702c0c00042023501500010b060714a243c90074460551201c000b1a00b401141903140c1c01a80240020401c0c035440b50312100302c030440540800103806640d8000c90980c0e126a004460740d41c1e0120412040da6407110100120f42d103190f025103c03550001400d0108020040c0034644252140004035020050b0004c61034000c0d0f07400402e02a940c45d01464041c000e0454041c040c02003030814540300100380d0300600704e8141200040c00c041069081c00e0240c03405811810045407003800b540340440201d90180050001440e00742c001241c87c0341c41c000004166071865128002c0c403942100107100003040f210070603034400400e19000f0f07419504e5090061610395041030900100655000306085940d02200138020388494008484c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 60620263 1250 60619013 60619021
    0x105060607050a060509030c01020f12070c020a270c020105070f05040807140301090f0503030a0b06040b04030b100f060c030311030108031603050403060f020d05070207140613030b010e0f 82
    0x34880c41114002802a00481802000290154450794214103420200c6e03040c0710396100900d089a2101c003966221110212700040400860102160301c0359080c0342030280040303aa404540e19034214007a80044e01c0c2c8900000c2b2506000c804041c5c1218605d11040c4502d02034203501078000c03c02542c0410001e018601c1150025004504980446400c0310050100500c2c0c6520700c4070311000602c0142d815526078030500007081c00030302034021580c0114080c50356414100b000318100c3c1c0356031002900804061004001460f5031005a17000c03260003c00c00d00e6640d0f121071402642c54480e4000e4440074103c0c5030081140caa000041e151080c0c440d840400034640b01d40c50556940c0800d109410741580308000b4082e10200e28440701d05d40394841d0404905040c0ca903581c4a0640c3c018400042005a01152060804000e0302400307400c14a5400500780d05070810711248034440307020340f0443c050000050100070070905214404000c54000c40d02c6040e65840b40010300e0700080582e03044102540301c130042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 60621513 1250 60620263 60620269
    0x414010f050f070f0c050106060504051f0c02010c03030b09010801020913050f1501110102040803030a0c03050f0402040b180c03090706110a0f0c0509090a0b0702010b060403140a02130e010506 84
    0x8a00844854007040c03101c1e030b5003d40c00c0380c911151200100030090070140c01c0c030005400740905130240005443e281e440c1c074101420b1080181000c605542c1e5100605050b84070b4541000d0100441c0e5020321b040007401a060805070301030f1906001d0140c12405050001a41810660141c00403810895010340c140d84111000825038100b40d4154034039000c10000708d45105020b5030040d074684410305200a040d140b8450003400c80e040b5078020005a0000020420b01e80c60600c10a01c2d039130110b0600b0440340c1000c588800301d012000b4002030103950740d561032925903039896400808269800307041c4540c3e8039240044d088150801d841c628004d102d001c0c4045402801034860800007828140101210700d02c5440340d402c03903514041b0544280c20701041c0460203846d204a0305124014520040c081d514036031408032040c40b8020140310459150400122140c1d582d401140c6c1100c1e0045090742c0101451210075081844180d4020343c02030425508150311300c0541c02030468482080001c224581c0d50308c040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 60622763 1250 60621513 60621521
    0x60507050417010903080a1406040207050115031103061305030306010806040609020f07020a0e0405150709050a0305060603060705040b0d0f060503010c120e03070807020909070e01091e0608070302090a0b06030414010f 95
    0x818041070101d5400903940380ad145c0d004d050281d0042001052040c0351900d0303c560540e0701d40050322288485018480141402c1201079040001d001c4605c0321400f550f190a41c42e8000940031504014509011070501d581e84d80104c0003800703c0341001c5503660072420300a400742d4003da800701e0043c0c041c00b00000781041d6070203545104a41020180204200c0c1034280b5004003c01050501071000340f0320089042c0c0c40700007103070024601ca0002080741d400c0c1407040601d0240020042020080d08000030700113000c0c80419100004040c0340003050b00b1a1161204001d071905030881a0190b2030f010140150b070794405076600e00c00140c1001088104080e4900c5503d80c4940074000d000c0c0e1904001c080010304045981b40c0d4000045001d8494698a81d130408000807000e900855951362240e0484080740461042c214951b21852810800140341030745140e101c8445100c064464a0780800042404c00e664000c0410300380c00a000c1c55903468249080103c55510001001c1251b1800007012014170162003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 60624013 1250 60622763 60622781
    0xb0c040e090d0206040f0c0e01030b04021807140d0e160f060503041208060612010611010606020a0b04020d150207060c03140709140301020702030a0803060f06040b07060507050417010903080a 84
    0x4040c124170366690b100d4065800407142c0443d00c1c21250580014440307004e0001a028500c00e920440e03450806004020680074106849400b0041420500c590542c0101c0409484140e200c41d068481c606048030703000421016030041d042c1d01949400350500c0500031802000d6601580041c111640c0310b6070104c615000031070300104881036400700b0340c40c0180a0409140e10070001403c2c0da280c052841d840805806080e802140821a60401500024030038020900503018030b01c010105805070740c4503401c2031000900082d008542c02c001e0503051022100c100c0e410841c006900755a540754500d44003004010f501e050900203460040280b030450303020001203015a581d0707661410700506110444545401c50301060f41d05643c204030640060301d040c0104890b06025201203910303407402d170003400018180000f402f031056404000c1840300308130340c03030139101b80e0764020740005400d5442c02401c2d81d05105540090241d106d811034006c544c082c05400041742c0c24840c0d034500c541502c07001c0c41c0e030041c0e44c4d500d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 60625263 1250 60624013 60624017
    0x2031c11040302060a0c03030b030109020307050402031e100f090b030d1107120c03060c0305070212092403150109050f0415030b1003030206060607020d0318030b0c040e090d 76
    0x29200100845801a564089011244525066581d0b001031082c0c4d020394903800104810103440b5040c16010f00c03c020003004140c00901c22070049600107030712008980225841113a01001240a220540041e52940c1c80c0003034480030079003045502e0b140c000078a0710130101311040071440030503105410300601080000140040181014070007041c2d440100c14000841d2510401030b000800302e150315070b40280540194040c1d4142815420302c0030582d8084034401d07040c14200814050b04503400a8462241801e0080c140d407142e44072400505c01988200c0003031110490b01c2419454400c80700015801075034005500c4070b00c105140010344490b00b03284070b081d40c408580482814203040c01c3d00448800700d0380303082c8103a05585a0307503070a07245801540c01c0065500701c104144101501041207980041d0f00b125236a0034840f040e40001c4042e100c0c400003e0400001d0a034a61445038805218405980c1c0048040154600030000180c6600130303200e0700a60405002c041140c002c408070714050800200e03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 60626513 1250 60625263 60625297
    0x9060403080f0c0a03080f1f06210609060302120307050703020d0807060203040b150a03241e090c0609030c090c0e030109050303060f01050301050d110307030c030309061409030606100201110403051501060203 91
    0x1c0003052b41c0d8030640c5803915007000944060884c00031041d210b40b4018044007000001e09500358010b21814003405818031205a00800410f00400e0300080c034202220381c110745000e43c0480900d07050b145801410760062241d070012090000704120a16902d100308000d255058104400717000300064158240320141803c03101e55000c40c200e0315a0322590494250744440899003542d00b143c1203100107169800404074658610b4204200710002d00e0b00c6006203020300c2c1085403a03045840e6184044924406c402030075950f16584425a40a031161a8900000034000c000310740803410119265401241d0030740c07240c4862160303802a980038030300303607030507aa0007415a0340b03610100da07180000c08640101503a03151140080000c001241d0355083c00c080c511a585601ca91454080003520303628a4040034001031905002540d40e5031400a2030980c03001044401d04130118619500341d0061001100060303407860700180100074000c0014541c24404e0f015244009541c2c1da8030412602c902a410400350141c0c85 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 60627763 1250 60626513 60626519
    0x207060b0913060b0301140408040f1502030f0a0c0b070e0406060c08070f022202040801050105060307121104050a0e06030c030d08010603090206091011010b03010209060403080f0c0a03080f1f 84
    0x20f242c2c03200344424405800060b0301045103400d107881e00c100f00c0d022180064005070030301c0303c4030400500c100284940c0c258900102c1c2c0783c5501940380d004400c4042a441008a07030b4020541c8503050040f800c6401400d00c5001b81046076006146c100013410301c0380280c4c14040002130117441902280300c0c0c00e4003c0e130a1400c12003942d80700c41c001d40d0641000e0b40e0080c2440540705c0e00803650440d5204002c0540c1c1c005a03558071340710745582550016402140300310000d004124240e80c014010040440031030600046078601072a100c55540101e4200c6070700102844008105051480300e100e0003104210b0448003100c0d015420150f4070a5000134443c000341c00a001000041d0290308222407682c03000701824102503000340450b03540b50300b0401c4500003030000c41c0142c905d92802e04c42c07201000d40585c003e600c0c203502840801c005201c0e0344001400803800280100902400c0020f607002521100c00b5103030501c005040c02458010f05032000030315200005c02140203001c0100c055030040ea0391071040a581c0380307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 60629013 1250 60627763 60627773
    0xa1103043227010609030803040b041502030106030902120a0c0b0c07091503060c020a03021e010608010609050103230a080f0705010509060108070618120201090305010e010207060b0913 81
    0x1d81d03181d007200300048201d45481555881c40700c001116410b6004210300340e0041d5a030346103040603846030003800803840060011544071811298401d81040090845488525100a001d0a54400207004134070100000c5600c0ba4980c1000c51428000c541c0200c0c1c03441d002201a0301c640e201c04c0b0040c0040e42d010800c001c101d250802408042400d14240c400b041d41c0e40742c50000303480501709242035032052400144100503c1e44502404100c1c90302c000c080500083d6006543e40444140c4c400c0201031401c103200104409400c00c0000d84060802440100d640e1107080c1c01603c002c0c00f0407250030350090802c0d4880c030304402c40021503c0c079490080c02d00c4280bc0d220101a03600c82140d80781c0c4c03010301300001800300d4401d0003041d026801150003440d25614190406081804a810603000c120034003400d1603041650941c844240c0f152900c1d0b14a4803545880161140780c1c06600c014411750034151401708201040d400752864500400c414010519018208410310700c00f12030205e000039034580880c002c03503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 60630263 1250 60629013 60629069
    0x30201030e03041a070b010602010c140315120a06051f030609020a05120d020715020309042307050a021b01080f1803070b011406040602070e071e03020a110304 70
    0x5601d06064900d05602e8040041c14880c061807501d01100e00091304004001e0000c2d049030040440e40b008104118190f14024001d04480e81d000751468004404248072105801d0303013260701c90000b4400303841010a011180e807140480070041d41c40e980b614000035209805040808803444c00100d0500c80c3c40d095681d900c00518622a09a0708070700180c07004180f9032110309841410b40b80040040100c582a144000c0c42c11580d074120382c041c0c14042000b501125000400e403101c02d0b100f1580031400a01c828004008541094100e01d102c66618062000658014000780340c58100ba50a464022502a02610721480402c065a0006040e100020321310b041000086400c181420b8507c1c400741e4860302c0c010f1035504240c00903260021404010484240b1040d070006128005803040c6080c2460a10003079210004c92140740741c0c1021250009800314410740b034003104802c500b0b00c000c0641050823130082c000e40102d00386034046199000c1c035018002000094808070b4000d5038040c2c189078080d19006213a4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 60631513 1250 60630263 60630281
    0x509030d02070807020f011803060203090c150d05250f02010e1e01050f060a0b160c0306050103140601080705060d0209090108030306090c18010305150a080610090b0a03020103 77
    0x6400140008503054280e4002001000d025020700c58540d03240e401009143c04030b45642c035040c84041e00004010911564a1500b185c0e0042001a1039595244140e41011840c240c030700d0f401180c200081c0c542c6007090001e050380c011490b000300840e44d204a40c103010070401007011070202030302001512075a840303680312408103105403002040460005044038a011040001c861240b036502030b07200380049003403050a07407000104498041905198012802d614228082ea0080940000301d903030111034654403902d1400d9014801404140c0d99091020003840280400c413440302d0260600142c80320002000f6040e20ba10a0242140d03610b004204007090703118200841e4000e4081c8180c3d6035541d00c5518440c000c0619070080c2d640c1b450600108840480020070311401c80009001d4058844040034004100c01001c1c200052603880d40203104aa049002d044290b004101c030702c002c100201d01141490143c0c1401c4408000c49440d0348105041d50680c9043c0340e04103404c00001c002561090f0042e92603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 60632763 1250 60631513 60631531
    0x5040204090c030309090e060c040e04020a0f080a0209010603380a0801050a0b10020309010503070504092a020a03080609041a010e010303140f0904090203070b270a0f0905 75
    0x14580041d990a02c80d065107a00540100308500420007225640303011b4400c1883e8082c1c003500d440c2c5800000d9510902460240c1418a0035180c0050219150042504080c02c000b010043e40c29a903100e5503913880039400c104a001d149803600000f8001d00034040e8800c0d0a03800c6030319008407a003880f90204003d400f051175002c80c9030401d1500701a0b40b1600704440c05001030800105d01450141e00c0c040548441000c164040c0064003a50f0014035404001d0341c13100c1c071092070700e07903600d03224214119024003c0fa0008000b407450003034543d6038004207241e02840f80502080400800c1844075090381c03074149d84070020300403400201c0040c00780d1520710040c07035100b4891241c0585501c046889544039440980000000010690041c024140c2101d403065041e4601d00700e6610309454420110228001c1c8650702e8025510780103031004554052000e103001c0e000e00c1d003407a511901c0100f11010000d2002c55500c0882144028413030450a1006001c1c0a441015040801319403a00300e0400040c0b0000b000000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 60634013 1250 60632763 60632771
    0x71e0501021902010207050118080403060b040914160504020408070605031e042a0303050406120b060d1d010207050a03050a020f061501180f05040c020102040801020a03020408100b0303030a05040204 87
    0x42c07950080001041c00c5200d580010380350f40952600c1402c4925401030580282d08071035400001801a40031039054035070003d4003040350f000300b10204018100400c2d0003001140280d9040e100501c0000700a01800e03031400c3c2440c11640e0761800c1c00101d20445c012000c458016078014098580a8801160012410200740b140d04c5183c80d508641040240e6086400300541d03040c1101040c1001001044030071070303d013074949061859401403c0b5100318428102030005000b0041440400765008125101001c2d00082d41c510381c0c03850040c02002003104140e000154082c403089840b134148251400c007079008004019408403900d041c0e915800200c42c8004520800d60b00c01d048039070900210b401281e1152a54250190300340000d003030071055250391844041112030400c0341142c0f00200108841040d280055a0042c0c000101d029210f44e4128600960000560820b8581d0650042044800d4602560140c0d240001c449060390b0000c1c241d00e0303040c0d200340046909244944c0c8240c1c1c0051005100103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 60635263 1250 60634013 60634027
    0xc120a080f120106030b01080a1a1e03070b0f030f0402150a05090120060117121305030d111b040e01140a050702070302060d0c020304050a09060812071e050102 70
    0xd5600915100100d0311000c1891003900031607001d9035001d800903003401c4c07050000700c000007082c0d07880c020b2203429410780320500c00030710311818150005000c0000e00003401a0800001d0381c024801601306c0d45029202d026400566040c40c40d00791044a07816510840c0f0f15122034130312140c2c5d0a0003400c02d07a032041c600125a017414010000a0506103c04d4903420344480001d0009080f04000f111400c200d00d041000415142101141050554072007502c000010800c401d131300c0d441c10200316400d0413001070008008007401314103403214085036021011590300340c0e06c00c4011a0f90000d00c13060034500da8400c0c2c10b01c0a2544642c1034000015202610024410307212581d40e60a40c0c40104003880032041c0401441002c001a0203250303030182c0d960006008451a5601140881c4501880b80d4032840d95070050701c1433944240212001408024000b518850f11220306400a200314852070907107100d414504c0550429003004c1e00e920640040c101c0c4040f02c0c092203a9019091403c0080b90b00395801c0100c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 60636513 1250 60635263 60635273
    0x318120304120507060302280e03010606020105010e1e16020a1a04061b0c08090406030b010308030907080d09150c0501021305030c040615050c0a0812071205090c120a 73
    0x2600c024168a05840010806400d1143c02c2c1038542e00000c0070980100300c01c0204230004540780d04404034510009283d800080c404440c488900161298036500b807200000c2c9941e41504128141c44803521070020907120150000d01058011311548510b48100d030015100850303050b4a04070203030b841d0044c0c0c0e038100b40998954448007100140f804414480d40d0610040c84214403c0c0040110301000c8200c1a40e45850050720480c4002e03402011600700165039000c603220394000c20010f5902410f185103558480c07601b081a0f070030403500f2407038910419400040740d80e0002515a4462620380b20305102504080c0502c00007072010321f00c0b0341800320800d2300b0b01c0003540034802010f01846c0d44103540134107418602014281004150340b03c0c861400c0c0389040c44068803648100040c0101c50912503540d4004e441205c0c100000c90001905a440c0441c03003003030354048414000d1040744107640c0c40c5070b00c0170303549481c80840d0b40503a0340e850260703c200038101c42c604080031901000d43c241003c46a940e0810350314 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 60637763 1250 60636513 60636517
    0x5090a050106020c030d0815040905010f020a080a060e0615070510020307030e07080c0d050712030201090b0612060c0f09120a0b090a0b0402041503060e01092303181203 74
    0x1041801640d20303001004002d80c1808012070a12040b405860304410b2003000500311100079000d84561120101c0e01b1030fa50b035456001c2d600d2903501a000340301c0a5001100c80c2d0003900504034031804294564002140f5114520601003640c4605036048816241d090500901840d0030700c610318404030410000021610170450303030710703072001d0704002607900d00d0031a60003002d4400c0b00440301c0c515848010305204001021400501d010000e45680d601501c0c1e44c240b030741c5003611031fa0090195400c2c41c0b00c1c0100317140d41034100407466070048406024545902041c0204001034556540b16900100e0203e0001c0c00340c24020b103242c0154214050030054120000f4102e4801071080b510160700200c012010010001c2815601042e260040d015405664a520200c1040140024400c035982c0360020220740080d80762002031600042c04010020108240600a0540b40e60945007040f180c14801100080b0318006041c1c2c0d842c4c0c0000e90300741304003115511080001710300c00c01d5028102d0700048051100c1080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 60639013 1250 60637763 60637771
    0xf120620070b010f09060608011514120708130305031305010605040e0309040e010203060603160c080714010501080d0507060207060e06041506080a020f0d02010c061a03060c09011b08040509 83
    0x100e603255140096070030744901a50701c041045d90810100700b01040d00f003d5a0350445000151400051031604000c846000d125070a40f601c0c180d001c144500d5000f401c0c10030342c0c400c2403a0340303808480f0344407160782d41d1000b4440480140081c1040000980d400e079012006459103201e0400421515100e40000e000c3d00c048603604e02041d800811104518902801019980380c4a440210315501b01301001c5131403844024903511a00f41031a001108040c0b144c507400c07509507003183d501e6460b92014a082d108010181ca0b40644540c00c1200100b002c00c03011071107903860750068076814a080c00556a00c00030f50002802503c005681e20843c0da04c108040c0140340c4558420010040e00140800c09602103c0303868004094680c00b180071040180c44424021b0101c1000f16607207901034140c0d00c0101d8081c0c003510002010300d400e109110310300d520040c2c05440b08000841c265000c039070326503405404031301a42000600090040000424141d0f0404807011a0b500802c0b0a5141585a40200328070180c103403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 60640263 1250 60639013 60639023
    0xd050106080f060a0e120a0c05010c082d01090e0c0a0602010c09080f0a02060c0c0d060b0102010609050415020307050f0f13150909050903040f0308030f010f12062007 73
    0x7820301c1141c2c0405000c156402003c1900420050b05907500d11940c80d0000c510b004450080040c400d5100350003030b101100301c40d9100000703004106d205040141880815110054001d180f04691019081c1d51107032581d804520351000d4106a10303001440000d81a03c00100007607014010004030191503103240d000c050b000e01c0e0004646184103003130041541a00e03a010a100e50052240880c5000010900c40e0009030116040ca4403071070100c9001d802c0c040c0b4844c005510000880042d82000419000b085101074244c008100490303440418900b81c4000322001032801550100d64100580b8950107540c010103035190050601444904850184d4009204100c01141c00700d90b840121070014500700180c00b00c0021804445048003015282a06600501c0c816988403c005040c8000403c15a070080030004041c4240b0b03642c0f070801c016160300a80320080050806400441c0c3c2120340160b800c102c90b040444994290750702d44468008010300300759450350a00c10134004500ca070781c4001800f201c0d07000e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 60641513 1250 60640263 60640273
    0x90a020a0908030708070308062704020909030a12020708070f0b0105150f0730030207060509060412050901090f090c02060901110702010e0f06070302030c010501050a14040b0d05010608 81
    0x10640180010300300d9440002c85600401c40c50000034001025038089942c9402c0c40c500030340f41c180000d2a0540e00701c00f03a00c03030b01c40e02c4090380114110b442c180034090390080d216032910f6114910030980741d200344452200400c240008420203088c840d40101f84042c051500541091159540c40b040380000304015200000c1c54801440945003182c081400040803d0403507150404003010754016010304003000d8440a1408092501c541e02030901c102c0700c400d1405000459001a54064000e400121007503e040c0e02e0540040d10020b00000c1481c003403a00300040443c02081c245007125140e008a5501d030410202d0400001c0a403030300030000b405410380342c801184000d80040024075041d80200000810381c1030841c841d40e49901441100d03841d940a28000005005030f1010840b1041c2c1c841200303402000000701c201c28580d020000e444240007141c001c2c406645c1c1d403002c012400690340542140000b41010780100751410f9489066008009840f020490006450b07050031900194850780f190307081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 60642763 1250 60641513 60641527
    0xd020a02030a020705092806080f01091a0f060607060b0405160206070305010608160309020306090d021e0d050c0c0a03050f0d18030b06030f060406060608070201020a0e0103020d0b090a02 82
    0x50120401070002a01e04000c40d00c0d0800c0b00102d8001c8547c901915800d490f4075030105070310581c110001030700c981e4080341e10341d201904145000700300302c0074141c54103540f071402168180d00e1202802c0c018000b03c1c0c509a001d845d901c0800540c1d51001c502100c9440c1d0380d509900c0907445900034940300e0021761010181801c0507a030064100343c0002c0207a0f04162800c0c0060010761f41001c8501c3e0003034072510042442098450058000b402e040201070740c58420b6400308094034200051451a03004580d00341d4030b800710485101c46049103100c5051038660041494440404d2141d00a4030007104800d080f6001c1d2903810000c40d12114403074005a0742d43d08642140c1c500a84100301d880c42011840c541184101264455244e2505890000a04402c010313404aa59554100705903036120760010250b911508107490b000c0c0043c241c2d0702c20000031440260010703401c0e074010720907100e09a51940307a0210130010000118000d40c400c031060110203a48101100c12901d6020201c0d2007084d00140040c4d0342c00c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 60644013 1250 60642763 60642767
    0xb061207050301090c1701090b0102100f1a030d0e09070314070c050105060a12060e0a0b01080309010201050a0504110d02030f0304180e01180b0606040308070b061005032205030d020a02030a 83
    0x1c0602450f024031854400340031b8001e680304807450450301d6080b00094800042c4004034145202d00680d0f044150400400000c5c4c0c6e00d595003c0d903403407043c500c0100c0301c0388110000c2c56281c025507140315003c6082510701100508200ca0110f034001190304d00050380c50041900b20301c0300700c0191100000508107114442c1006401d104142c8c1080044500c40c0bda6454001d100c030b548160400028012506c40d91586c80546041108221040c0d0102e82402e4560312903110540c1d940046403094015030034400850714a0856125030307401260403000c3c0c0581d00390300d003050000802600200720b030144543c403100400246c05002400c0a081144209040010784603a60030544040c482c08010a900d46005921034001440070300248030346c42a00811203a0b0b8410014089018a5202801441000800504214461417800d10036003007200d9201014110030021202030000300e801440a080004124607000c1559100e114464800c404481c85c0480c0c04010f002030740c0103003071840301503440424440c1c2ca40d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 60645263 1250 60644013 60644021
    0x2c12040e150306060a030f0602040803031f050603060f04051509090109020f0306060904200d03090e0f011401110c030a060516030c02100209030309040504050615040608100b06120705030109 83
    0x24070101e00920440c105440054045113861200800a9544048907010031055806585c0241185001e680d224900b69822100c1802d0010040186101810022070741c5d2401e0f90a880c0260303000f41a1450a4014000303020080001a1003040112894041104584e0350700702c01c2481581102c0000c248440944103008100c09005031443c800d4010504028071a29505c201c250302c80d8101149505207600400080803040c4250103054010790240c1d42d1800789038000c141c400c104c651014405d201ca60340c107150b001c0c080d402030140c21072b070307445810143c103566224220601903903d03c00c056840f101e07001c0c000603190000c030f450120354054444081001c0000071081c00044200c40742000d201c2600401c00080d11140f02c2c0090001569000c1807406003a1410003c0d9410500080c0040000c0d05080c1440e940d030b04403c403501d0304103d51051480d229400c244c0111001c0b18254401080d81000490440014160780310428fd0080424840c01100c122104403640c001c507290384442c3e98a5051500c0e000c195 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 60646513 1250 60645263 60645301
    0x90801060506030c03130c08061015020f10020c1203011e0501050a022805010519050106030204180f0e06040605040201080a06081902041e0b040f2c12040e 68
    0xd640d00f0b1007080090904682180e5000c0405e4441c0c851410741d5160007a050318694000c01403520515041015204000c4600e40030768068016405018060080490741d400044000812680064090b07221503084d5030080c0004400020940704442510b44025070305030426480150030000000c41c000700681c40c5403541c0042c01e001c0c81c01a00d002e2540001940e2103450740007181d50075049844c8040d400c2c072007101d610661039110780240f166041c81481d102c1d401030084000d01c5c0f4140740900004101e8002d1088508844100900609481d00d024002000f00344950100302ca03240c07150000c00c94890240b1260b440b444c49048005101d0400780001820200000d080c0c4000e1440c1c040140900340e0000307480200d5161100c940450010b0602c04540900340030000b0a500c44584000c62004180c144c2048455207020303101048084c4e55403c800f01510154000c5281c800c021901c0b04140e89007401c003003c0025090000c9852809902086804c90ba00c40d5111483d20b9401100f401b00074200d5080c3e011407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 60647763 1250 60646513 60646519
    0xd0b06030c030f0901060b071505010f051e03010204080106060206040b130b0105060306010e04020c0f060a020304120f05040b043c060c020a030f0b060306090607020304090b0f040c0908010605 84
    0x80d8641058203403124030000d000b04100502c1000001c40c1a4000d4208001403d521700700e168455190f0324000400d40c0074248850409414807002040d8040201c0a140403900d00521441c002c404061503104040900d420a64040d5000c00000ca41c0c80424001d42d4018412980208824034180c14039002002c40948031411074500c036410b84001c40d8000f041c0d141998000c0350900d03500d442e00c03001a51911050709900c3d41090000ca004403511802082c100480940c4000341c60156440d5041e4004a1008407002450484c840c9c004014152261901a01007280303410658903158442c1d18034a0715400c2039101003031a64940030710350541c1c21050682c0c40c200314400c00d9501015070386010461041d5580c021340041101011881096640e892550300040d50080800700d40300c903060406e0f1007120411a0304034000e10a4001150000d540001c0c0d0910550140e405107003014180702044000d018080001c660102c0303081c600381ca0350340d80d03445009603403a86915840300031440e01ea1440d0030741b0700ccc65210900c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 60649013 1250 60647763 60647767
    0x110304030915090b0d021621030b180a0c18090c12020c0c01050f0409020301090501140105130303050a0309120801030201120204050a050d02060708070b0406060e07270503010e030d0b06 81
    0x40c1ca13240c41c0581e07610301c409010260311450842204081c64950003009400e030068261040c0c0b0401d0080310360301d9103503590b0f50180101103020303050090b402205850010707035038124000540042000c5c0c0c07000d00a084146480440e00c2c6a0050443c1003409a030427400308142e40345001d62003242c001e03a07184491a06003406504019001b80320b40d40350010b49110906200c00000d40c24441030790801210050710403c1c908545a503155200c1e4001007109018401343d424035011001c55540c010303420340788121a1484111920303415984d040ba92a08924180018961604541c1000840400b03020307500540d00d660704403042d85507000050092070868018004a841004140071175100e00050105581054a650218440ea031001c14a0762085400c081d14103035010900104004200754010301440c0506400d0141c203882c0d20040c1da10f003106495810100e01160401c0c00440c8110030a00500c0e5044030030f0307000c000c1d45e8402090035a80100039005940d0000a0400c00c420b0b0745200d100901c1f1070540c0c2c01d034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 60650263 1250 60649013 60649019
    0x306061115100f0f050a05061903020a0c020405180c0406180b0a08010e06010311060901050d0b1809030703121503031b050a0804050909010b150a0311030403091509 72
    0x41d40301c503034000300114040110740000b2070120518042d04010701020340aa60100c2d642c11800d00030308500d004861082c1840d550018803460508180c83c10714000c0c107105020340c030400401781c0081d4000c1030307040d05112421013520701596031403050078828894002610a00141d0110803402e08c8111000e0500c241d18009040c04140c0e16040d0316080300041160000305000c4c8440002c2c82e003a600e5100456075820700301d40403008140416581e0480707100b100f4542070141d000042100d14058aa0410700059087c000c44101213070035005901d0301e9001402d9000b21090b40515201d0404007111480306a5100059044c10180d014800c0c40d400904580200049000604c00c50b449018911000e810029480081540b1404244c51000240d6001003100c01000280c904002190000d104440c401c04e0b2180006040c0001070040582c2c0301d02c000d20304c03200680c00c0071a03109541c00c442d1070101059038802c8203900f40c0c08c42e14001c6001e00c1c0aa1111f06031546444d52610300c0c200200c034900c040140c190010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 60651513 1250 60650263 60650297
    0x301050f0405280b090c0306100803030606032206050601020c010504140105220e04030e1c0803100b04091a1503070f050c060a0608071406070f020f031b01030606 71
    0xc500c4081c6200e02c6403c00301100c11000f5003000500c007420f82c0042000f4040307030b1180000c0c10741040e070041e03084e11010781c1e414400000715107030361240441a070410400500903141000007198000300c503480d124040b040542580c8100c9040b100203c800d96560f000740600d540e01085403001c03460091900502e050705100d050141181c850003100c1c10322001143c4034401c041031180b0b201d019044448030840c003680d00c0080c002400310940d4141d0200c0d10900c00e40403d418803645005500d20030300a041c811100d1a6501c1200780e00007002c0c00c118a6140d40d0108450148400500c014030b009031002c180f41902d0709101d005c80184140162185000b0040260704880010940341d000341503040c0048080314440d01900c891080c0400e0250a0186200300004008554030807c103031400041101c0916031914001e9800180d51000c1c1a400740782400340d0300000340380c540c08500716407016040c80c00c05120040403d2174200780c0c0205001d031240c0c2030146203c95a2500c90140104182e2402c0f050301000ca040d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 60652763 1250 60651513 60651523
    0x1503050a0b0604110a02160e07020d0e280504060905070207090209030304030c18150b0702040b03121b1203130204050604090c060c051c050901120b060f090301050f0405 74
    0x10080c07894a01000203071140d0344960001c480707104100d04555907480d80e248025100c28124681c568424414440403031680e465160301c61088035030760002c0880f00e41c003403001d9820904804489500a40b40001400600c5024407007086462148070011006801d150403c400d540640d00400e0090b881c20301000040ca0380000c0703100c21100a17800050343d8401c004042400d500c12504090907150300c0000004000351a003540c01013076030458104200c1480c40289140e00600544220919618103100e10700c05482c0981c0203c2c0b0f0810300800b1503000c4071100411031823503000040402400b0700300782601e0104080031312400c09140c45400f20a4594038201030140d100541684010707001c0e0781c3c0c940004105807184e6021040da580c10a02940320b541e85c0e0a001016040721200441c0ca500644080340c60700800c100c2215004e0090362542070a1066803401110b038541c801c0c1e115a01c1c25283c4078190030303644840008001c1c441c001c2c03025a940c0d000b200181030a40d90060000100910364000300300204001043e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 60654013 1250 60652763 60652783
    0x91205070b030709030b040308070206070c02012703061109100e0603011205010902031b010f02060402060d050405120309030403120c020906061b0f0f070f08030403030f0507060e0105010603150305 86
    0x40d0715103940700c0d86400c6446066603040180030710301c81800e0000b03050f0401c0c4050b116000d684d00b2190250303107200040740d032a1941c0c00020701007509031400c0c038203245c443c1541e081030001d0f40f5840b4003400d0b03683e1240e9007542c0c00e15a810415810002c0c1101c07585c102000c0d00349205200b800d1501721481c000011a4161105104a0101c800c1c00d0b00080200300e400e4005820341a001003ca9200c021b503ca9694042480c550359103000c2206c440c2e61900050000c15140e10880c0c006110500346003204103800c01400740144121810f02826203282c40c8082810040c50240a00348001c640340e908500e005280c0400390300000040c0032a00071800c0040e950854a19403020054a606031035003c034070100707800e0074010901c41d90341c2e000e030800021075120300141d245080c49d0301a00321240d0b80d03a60000e046110084c2d015050491700200420b001090045a0140c85c0c2003c0d0b00d8440c1c54214a0303243c071001c482f030901940009075181c000402c20940d0500451041d00451840c0c9003c80349141d64046e95400745035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 60655263 1250 60654013 60654029
    0x10e160e1509030f06060901050d0c0b0f190c050d0e030624040c1205060d03050a050901140304060e071410030b060909090a4d03011b09120507 63
    0x4440c4058980301c800a440007884081c00711503000c2c4844180c5a00d540f01100d029010b01403100001619140c14064a40104e801c400c00444c03145c14111248080d40c00303412859061001007200d407841200c4001c1030745103140d950b0348043c2a4513543c41c120f03081c0b00c02c988580081020301341d8440055540410640c4e0080f14030820400884007085095940c46410f09800e82e0040c0341c4a0095041a0820142c1340c2e0044030400402041da601e000708451100c1d0048080e0020b402031103011502c0380946c0003401840e0050410000210103103040d0350240e4800c403400c490391602d0341c6413921008800c01001014102c10001001e94000703a1003c80c40aa1400309032204142c0c0f2010442c80c1501e0703400450300008070262840b00d082c1707420103501f90342d81405401210728095180c001140c4800007014018440c003050500044443e113040ca03d5121309040e00d40d00c84441d002d51401c1d6a40d40d0921400c01c1c81007401c400c1c40c0541c0602031002d042d0030002d40c0030810140900011000003240070030000c056a10007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 60656513 1250 60655263 60655279
    0x203040b13060615030b040605060c030702090c0903061305010e01050106080c0a1404151e080604050405030d05100501020c030606210f01090609020f1c080d09050102040e010e160e 79
    0x82c24690043c018652000000d41d098000c8090095803542114a11150596041c44003c0c3d448c0244019445070741c5400e41c594005008110042ca054012580c1148400c0411428411f0510009041002c01c1d6a0600c020310030351002c80411038280550a01d2080f070400812156140400150401d5001030a602c1001d41c000780c0d02c0305160051103900c090180200c0b905072a191200301c9480a410011580800f1070300c03a04189003041da0082c50301058101603604c41c2d1031a02c1d5542440701800c1c02410490303041c041400510002459441064482d032040b080916102d46004006414140c030300b98000d00a41180c0e0400c074540e00c403c084006441d0300b59101022130704600c0b00f80c42c21701e00c4140f07442c50700e035080007150b4081c0001382d0816040c40b8001c840280c0254100c004024001c0e90150044d09681945104d0001040c01640900116000c00c44040f503109500d0b035a0342d007280c0c01900224140c0e83c0850041c070040310603200131a403109030713910321113551502d0120140a415600f88214851000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 60657763 1250 60656513 60656551
    0x20a1509090f09050609150c03011208090a030203061e07030606021b2103030118050402180403180807030605010503010209031b01020c13140601140a0507060204031b060201050a0203040b 82
    0xc40da20103c9001d42040981c0c0f180e05090380a02e40700c4218004807644a405d100c0841c00c1c4c5144141228121406240e200c0c000b16090f5031851050713001545000e500800703445002000da201845001e10a000741c841d1201c80880062040000400103001d4104142c90a2000d0256031380000e00c18145175040c500b400291860f44c40001d501844042c00320143c5503040700d0201c00303008000044c5050320794814181c4403021224a100040740c00444000e03500c170040c03000c8654488100c144440d00b041c001c1c40c00d000c04000310550040c16090503400304072994440041002030006a1060381e000d448201d0095180c501f03080b0000b40c1d100203400c00c212a90b020160701c66401e078001c0102d13014109000e418000b01060741c8145c040180906c00c001c06804480300d0014000f50b22903420031f1112113103260075a00380600c51740100c0701c0b900f00380130448405500300000310205120034082c84038241c1d095900e558450400348000d0940c1e40107045000d00342e00600c2800001041c60240740c1e40030480104520b08660 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 60659013 1250 60657763 60657791
    0x10e061e06060705070e071706150304050f0111070c0b040321020304050915040c0c030807030b0609060f030106021905030702101701080c011b05070b030c120112020a150909 76
    0xb00c2c840c0d004041e8405c4c10000542d0358110203131184038655503142d0201041070007405000c281c004603040c40c0e00883e00c0c160704224210101c059a0406d0082c801c0310003c0d184182a41d00f1101040300e041039800e0b0225011007008040d1203c03001902201000034145891070f5030b0150300c40c0e4800d194452480c03600b8034000c0e10707030300c00c105071001090001c10121180c14448070390007815080c40c003001e00890912008030a4280584600019107515a42d2030340c1a555042d0200c004051500b06598801c008010303c0360307142c0c2e920000d884403074800c0d4000c65032540b6046002c0d10f403d101d01181840b51a980da000e002184010050700d84098041e50064100b10300ca450448441706202d920145068440c80045403103800001c12894a070000c1c0ca903507181040a1402c01812000800000c00980c0003000510008001c40051900702c000f50717259604020101c00e1074410071030260000a14115000181019407030042c1400b002000540b089101c085d8413030b20700505000c060702510503d952101a5118544 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 60660263 1250 60659013 60659017
    0xb0925091503110c0105070903060c0206090604020f010207050d0c30030315030b0a0603020406060201021204111c1b060c0f0210111902040e06090a0b0601120e010e010e061e0606 78
    0x2501d04e07402006940381403078000d4102c4005010684a881c80e290300000001e00024040d070160241d030000f08003a6580307900704100f03480b41d54441411070007241400181c0380c03213400c3c0c89141c4912480740040742c86c1c202415244640d94108948011400030021f00029080c00c0c0d02d0907400f00d800d80780200704041c3c428103000c4040e0195000416068001d001c00105503046c4e4014002d0300c0c400c480501015544103009c03400d078000e000c0c032441a10101008540003607103081d00600c40c05030183c80b008800b1518a040c8100035000da00507140d8801c45000c60f500000041c01010180946080c007140b400629290140030140c420b01c024003c0e0040852448501c1c05175091f0390349200d50740c003118034030308116045080051048008a02035800d10346000100d0a011404503c070b81903070001400f5419154554941c5040301a16107810b00080b00c540b1503004181d4015205c44440c02800803411500c0c00c5441401c4078a1000f802e0541d030085014440486a42002035078017815460f4481c2c00c58840200051081c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 60661513 1250 60660263 60660277
    0x20705070b030703140f06010909050402120f070f1508070513030819020c0f090f150a0609030302150906061e040207030207031b03030c080c010b092509150311 70
    0xe0318044200112103138140c01141e04045c2900c0e03401100d803a070b1440104514800d440b064080b4145060038485e01240d07501c0300743e003d07000400d01030b0604082c079111403c010102c10a00c0b01c82e00982424402c003c0c46d00144401071504000d88803110101c20002005182d01900d00000c0001c0054400c407546000a0013401940d000019650380324a091200e401c14101d05842d0b20240c01648100241031424400040e40c2e048040e0160115a440c1410001c8604c00109002807007105645e00b040a40c8501001d0320103440982c50b1401c10340c1c1903080107481c1096452069900c102c1120400c101840081156600704070305480b011603691a01c80396005071403604203000e070007610100d0f030b00e01410743c0010398900b1607020f803503050502032602810303800b190281d02028011a4a004070300340041c45c04401440b0240301c4c0340000424a4182e000a0f0380c0160548034217600d10010003031500301c6c10140c030b0105454166401c191201600d0480b008040c42000e0000006050b80d480c0b4010010340074030201c5e450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 60662763 1250 60661513 60661529
    0x181218090c040602070b070c060c03050f12040204180c0302010e01050714010c0305070f020304030b0601050702040912030e0307032a170c0c0a0e0406050a11070302061509130602070507 81
    0x220740390405858100b50414800c80c001886003080000e03100030b269040360300300b41d046000d10300124101407003510020b011030380071820004100242e4800001c004003908114035944814045801c0c54010001034490030b000b0718800c080c1d007900c4000050880200e80040701e0742824a24400140680143c40390301071074201900340401c4401000c42c9102c107601160421406840c00c0200746c03201041101c130f8a02d000003540c05a40100020b0020807282410541d11000514000d0f00e0302c50f480d404101035402c01b500c210703940d03144001407004068041c000c0c1c80510079584015801c000003500c004040703101880c088100d4148104140c0640307a52081d843d0322850b0022034140842a00711160b000a40c0444d040c80c0c0e684c005c1903200f0b41e5074500403003814119108550011a9074a1326100d0b0801000080d025014856070388501e100780d0503112014016140c0650090001c91030b20400340203a0190f0018064442c800340d0f4108008520034420700b00300190041401600d0b480c02e85000751506101d42c0002c64 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 60664013 1250 60662763 60662779
    0x603010b131407020d0804060f020706020d0e0c0613091a030a03090812070b07051c0516170106021207030c0c0311040e0d0905060d060506030406090209181218 70
    0xc4210309500202c28849003200030804550722008200d80300c040550300070780041d40080114000ca0615088000c454440ca0801840d000b050b540d2075089902c90300c411100c0d0707901c0340d03107500c5075202c2480f43c180140401d0f900c15150208248658040c08418003c842080303a803800e071701c5d126218018000d140c1003070140880361040c1d628200904907160a100783c5905200d281c210203049214001500c52882d8402014442c5460307206041d10f503034001210f61595504401481501403c090240ea401407050200342c80c1ca4200c1c541001b00a01e115550050400007038400420071282c0c002850b036030301c1d00640304040e180c032410312302200c1d2821000c06c054090001084040300344030200c0d0340300c3d075005005c0b01c04004a56000c80e021b5180c00c01c0300f403000c3c00f14504903420011401d11500800401505100020b03085403204005040c64106490a641c100d41c1e6045000440c140301c100a50026a464540310040100301d504981d10601985c001440940116000b003c248140c01c04252004004040e81 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 60665263 1250 60664013 60664039
    0x10050f070602030f011d0406091e03030e07060507120f0903140601061b0210050d1104080303060a08121c020715050405010f0e0c0405091204030f02030d03060e0f0603010b 75
    0x34041d400640d0b411a00d00c030303400c3c00003421103141c0c0305211801b12031b450500c0c441d580700c0c3c5699000b000c1c8018103039100b00c0c80a04001441808850440006200752000240315603141d0b8070038503008881c0c1101082c048100320f068080380302c9202409201c03100345002000c01105d40c83c110340c00c19035a88024078180c880740500313041c034001040c41410b95031141c0d222078000703030350310f04508851030101006034201007000900607401d40301c2c0380140400710300302c88003041c10035010039041d1641c2c0c03280d030006116400c04014800d03946032040001004104200060601e00403044800317800380306407400108807420300031903517400d9410394040c3c5843c0c680010224030310140c403003d030382c02034031084404991651034101c02c51919071070352241c4404051100001d000c080045424800201005003061080d8460020018400081c9000410165101d01e010f5101100701d481403614000e040e20340c02c0d0901d0306058051050b40ba940020542c00020640024015140e06000c2030040484007500ea07041b6451007514 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 60666513 1250 60665263 60665273
    0xa03181101030b01031802040b041503030801081203100e0a11040b03100801020f0a0315090e0a14010203070c030318020301061712070201050307050315090103060f05070201060803040510050f07 85
    0x118030103482a01d0a0042003655401101140d4600700f1008902c124a03071010058240741c0d0001280d801e028000080050482820003007400541e0300440000d440b090041c800344509025000d4188115840300d415400c0540401100a03490300070040c4402c0ba03100002d00040603074001c0c200d41161030040c1ca0b5169107486245821f54000c0351070302809904e5101c0000c01002c148221011070100105280c1403e0500000728082c02072004510421804d41901107406003d0703200d20240e0000c2ca0000f4080c10250785081c00c1d207001c040e011910941d1040c010406966049840c00d80001c6d41450f00207141c101a1003801c000410220020303401d580381c81e07008129080035018404400004204445840c0300d0385009142c41d200c3c2240080c0080c10620224407918019006140c00c1091038004a2072506114007084620388264400c1e0342c1d031a220030784000c25140314841c031500681c89100900c40b081c1400d00d01790f41c80c8518828a402140c940c41610500c6e8411803d8400704c06090b0841c6988100030704117 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 60667763 1250 60666513 60666533
    0x905121204061d10050f0a030908030c0918010303020604080f120c0a17010308070b06030a050f01020315010309021807050903061006020607020303070c120c1407030512070b0406020a0318 82
    0x80307000d200d503943c80301c4905107441c040d800080105652414036200c1b80d04910a047c1d040025408185900e441d0b02a00107441000650712529030704042c1034580d180a410817428080380e40c03011101d0030401005102107a408035040b80c1c03098100c042c0325940c1d0040d10720300304140f0404d4000062540201c0034001004201802080f4409055440006a50700e405040c0010f003428803004207070100c20005000041c80841080f68002d0b401010344005482c00e8458900344044d104180a207030354004104040c460a412581c0c8035200b0a1904000300c04160740032a507a5610020b40c95504d4407414002180f05104008440510b00c01038140c2d90305092802860504070ba2a0103054094068040028621813000040e680320300c1056aa404250402c0c0d1200710080d0756000e00310b020006400588030102c1e0840c0c50407901100e0950040020500e1428020300b0540055a416083c0d50100f0000c004203000400c0c658105400c110010303990700c0d90010503401042d0038410950300d58a0110300405000324110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 60669013 1250 60667763 60667787
    0x708030f070e0103150e100f06020601030b0a0603081602060d090b0a1b050703050c03040906030b0906090334020d03110c060306130507090902130f1401090512120406 73
    0x107501d8140d00707482c2c0066042d5080e045c0c011001c42c0c105001040326800c04054039401c0301c51150001d46194450b084503241c011a90802d00150340035100420400101e1081107500451103002000f01c103080d40c1d201ea01c0ea105a480c500301084100070f101080d55105002c540380c2031386030241000703030044520303002c1e01d0410125924500c4a2801005d001c00d01c404412880391910b00d991120315044030ba9400703076203a803c05105100f03103110522000c41c2ca14118412400514000c54581c1c5242c82c0502c030603881c14400611300c01c807a0f0814030518000c0e41c5040d001d170b0704460b14100c0c181c4201d90402d206c907600094407034010303600500705140441855000071101520b40141021340308600d4a40c02403110030721055038165003040c0101c90100d02460f46038040c0343c0191030b86c0f03400d00e4419500c0e6500c04c02d9801c130000c180d03290390400304104804650f0080400051010002e081600c0072001c00103070030303007000b889003034080c00d8900c015081c407171414032012411201d106071031074607a515000f0080c00d07049880 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 60670263 1250 60669013 60669017
    0x31201050102160b090f19170a0c05010f02030705120403061d07060302071109070c03020613020a06030c030e060907050f04061d180a0305090f01050310060f020f010609050601080c03010f0e0c0708030f07 89
    0x4154071849803c0402d96004868001c203803050ae461411004541d4a00041002011030005200384da0020f2014080e403120018803503145900c1d20b0450902c10200c1d9140007000010100004507110480c17801324400e01103a1507418016140e03076090804402d0201002c040c543c1c032000110030803007541d4021200a403450701a03070031203015585010b800811281c1004020f9803040350440308204c083d103c0d411680900481d0328000c92052280720741c0500d00a8240e030020b0140c0c01001044c8001d00300704a12039101c01d022030b000c3c001c07980b0f01082c45120050640c1c0040c40701440c180061422011005a042c00e0030300e200403250a00c002d820010165003090001901c0341d82c010075030301c86940c0700d1025240900300e140c607103100b82407600406031440442c010041040d8010020711060ba02001e22a0000620038100d0104231854074000040c00550010300342d68201000780b005006840108001d070381980c01c04000d030302060310b03002c000700030074002e0400040841000100704060041ea00d1103960180d09c5607 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 60671513 1250 60670263 60670289
    0x90801021206040b121f1407120213080a050a0308071704080f090a03060b040605040b0f10110717060105010c030504031106040b0304151d0a0f021201020c031201050102160b090f19 79
    0x10700b5107c404e0020136502c0c80001881c000340d00380b02044540c000c24865850302e10701025036a5800a40703060800c0100191559082507415006064001c10b1195010200d46481c4d0300320141807482c2d140f00070026001a00590000c1001900d000d200c03c1155965038004211401c00f9580b85030a5024003420b11100d8000d60422100003442c2c1004d0041c1064400020484048030407650280140c0608a814840802907001d603a010368044c148001405010796003200c4150a610013403032858124107a000c5070401c4811180720000c242d200741581d054070780c00a0614004032603a0001000c078003403a0806040408000107120400019480c1044181d001c03c10070b100300c4040d5050351040c110002410b584941101d01c03c1000560040b01900c682031008141d41b1032458080b07c1242260800410850070303620005001c40404201d00c02580105401d10082070742d4164001d00c200030000c0d500c00d0074180130300481e401115580391a817411803142c0c081c0045140ea204c00c0040000c968942c455a2000204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 60672763 1250 60671513 60671531
    0x21011502010605010c060207150c0509030601050d0803010522020307050c060f04171b030304030809190f0602090619030213060804050c22020309010507090801021206040b121f 77
    0x1070051000716281610342e644001703403648035840607620088040b0303201904914181d0051215100383d0744071142e1507032426112620300c8241880c090f4181c201912900300760801000050b40301045070705550303054800454030019020520a0521541c20300e03060540044104266194400e02601c00700300039504895054485510b501800c20003550064032951103128030341d040c0402d0000030900c41181900546251503e503108074215002546c0481c0040c2c100000c0c0009004100061074072aa01c2d08561481c0e01c145681c2c001d031250f2448002006c0c80c5e0003090300045950340e036042d0f4a03a2102d0000e038030440708245400034020b5001102d055184e0601c4540412154410326816203e554400c00a01d40d0318950307400c000c0300104001c14810f5071202000c0035440c0712014005140941c24000001c940342c14618405841244650040324080c1c0c418000c11583d900f910f82003a4021341c1c02e940c00112006000d0100d40181c50f083e11165140c41000005004d08461046004012a90140030800105 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 60674013 1250 60672763 60672767
    0x50f0f0d030f1b03020a1b06050402040e12090904020f060a0c030912030212030606131805070c050c0d11030a05030d05010803130b0d0207021201050613050907030f0206210115 77
    0x522080f4003080c034803102032881e00c0e4502030742c0207000490a034108074a092089445402c00007105202c2111016141d03401e0204600303047c0203d40d0b5036600f0a0107040002031f60901c020741c5000781c0b0070306442098480d001c101036464404618410f220040e0036039030b03282c0141c800900402030300c0804800081c21040c0001d44401420101400268580c0c003410031032031100c0c1c104003241c00160900350301c0b007805c005281011000142a200800211070a41e80d440d812510180c200c960040401d0148000542800300040000c6000314890f00110307601c2c12020721394201040080b00454459405224005210040c42000405044040021a010f20140e03813100301c440e03120300800e004101c2000f0704440602000c2e01c08000380005000300500103040844c0c40c1c00080d101c00740704001c66010396445051280d6030400305104040d2003000e00090219003041082c2c240c2d601158400549001c4014030403004541c0d4440803208034501d480a100181c064280c40014011000e00c2120580314080c856203620358 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 60675263 1250 60674013 60674021
    0x60804030e0901060c02060310120c08010c03061a070c030503160c14011e05090a030809041d190203030904240603050c09270403080105010314060a090207050f0f0d030f 74
    0x35010f0741c5d44004011142d081c84119000617000b5140c0c220100380118099114000b9104518004c1c030324403042510705a0214212107403c04080c0406050400c20b0188449100d00d580b5402803201e0f90030f9688040d030070074031201c54140d00002c001d070000003003200511800d018008069405034400c60798a650b5142c88a000c4d02c1443d5540e0701180030080e14940304400d92140804010090074518640141100003850170b021580088940381408560042c0c0750410b40700e00f071740112180140c0c0070807207a4003903081d5036155585840c501c502c40b80b08803101152014411f07a010700310081e1061103004032a00e8114600c0d020711283d040c0d140c0b262100001d00d203101b402494060a03001c121103103010008014021540d803400d000e6400c4500d0301114811880800d03028920540c0a0317030303412419504110005040da645115100d43e25444441070141a0b036034000100e040319900c2c480142d80da1103d190140c00e110300b440000f005400341c204280c1151001150040002c002907504010b2036228170702d108111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 60676513 1250 60675263 60675269
    0xd06090f0b010512070828230603100e19050607020c010f12050601050c030307021509070501020712110901090203190e0a12090801020a020106050a060306050105070b040f0c060804030e0901 83
    0x803071003620125005e10f00400310640c000e0351031034009840c40e0b10030558a0b508403117025882c00c2c8680d207a100c034205e84c00601040703030007040100d92a800c50501000107680c9040402460240a5890b0313640303010036004000a040300824900300c52291207103414220344845080300c2d400c026010b0a1440b4030b11750b108030700070b10b5191880d80300d8201c4580e41d414800e005040003080c890510600704039040c05a00c00704003a41c42040e050740182502c000f40c01741803880d41303405003d0320303583d60003c041800039a0b004603141e4161450101e06100c8500c903800e2103000400d1811985400901e03207800850004840d40040d4800d000405000c10000b41d07055281c000c07600c2c0c40b0b692140729040405000001000380041440030703540340c0b900c28401d503210355510382281d000d40510750150f0b550764003c00031070402040030700c001c00d01c0381000c04c40c0c1c601e0140041c0242c4502c95000b08400c1440c00000c0400445018000015402c000b12158042e1540e002920b01c000c20b6174146e000c60040e42c1084082c0c5071900038241a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 60677763 1250 60676513 60676537
    0x31b06010e04110a03080c0f0d0509010504062723060702060313060b100c030801050607030e01080403110d0302030f060307080c1302070204050c04030212010c140702060d06090f0b0105 81
    0x4240c1c2c442d00c8003812030b220040c0196010302a803030004040f40c0301101400090700a000507102500e011032105203080c41c41000306041c01028003074188540c0e000003d0314115006814a400c920f4004600c00c14552120304070200400500380d008903c2001d41d09a481c1c0310031928520f002c1d070701050170401c940e6000b4040b00071f521203400c00000b100d03404080c00c4007a00b45e1246501040100d40000040e6080d15030045e01d100090780301d10381d5014154030400f400c0c01404203444041c40c101c407688005000030900c00f1190f040c4446400070908240c400d4011111032a100400c7c1c512031780030880024080d61069801d102481a010041501441c000c21220222021803005000f060466002e01c0b4280180c00700700340c040ca81c28415000035803101d00403076210b00001c680e040d80d03450443c410840202071202150603e685400d203a281e071507810114000c464a94031402030b03254001480041c0c1c961152400c885e0b507940c24064001499901604001003203844814141301500340740d401107500d40075514941c02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 60679013 1250 60677763 60677789
    0x80d030e0c0f0301090f0602090112020c070e06061207020303150f3610060f0503070c02060d020d18060e010c0c02040209030102090a120507060c0206030f09031605031b0601 76
    0x29540381103240c0b9808088040c00128074029951a00c804880800b041900c10503000117600c241503074880000840d00030003100860038402107003050795542100c2d010307403014102c2803804a50b00e0b607122820398000301a4030300c50501520304400000e4807900142c5102d1042002c40002034030724909900c9051210101410711000c4034240b40c4204c104030071100640c080303c080900b80b00b54003040690364170b00c6200040d986140e030030b1400034010000200311000300c2c1040300900070312000a90080f511000c107901210503588501000c010710300244201811560b0303241c94840305080c444120020300b044980607003000c02088210b400240d003a50613420130840040ca0300c0c940100140350543c050060a000540014141140704e0046000078140d40c01c60b0700d09142034206541080800c100308800b600161404070450342d02035000c2142404094001070510001d100051132101c0304200f40e58810383c018240c1c0245124504059499600540303900401011600038840b0074040029198101c07418904149 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 60680263 1250 60679013 60679033
    0x12010f03031d1201020d0504170c0307031412070c11300703060203100f08011107020906030f0d0903150605090103020114070803070509090a060503030d0903030902060a09080d030e 79
    0x51030240b00c2c541d034542c04060f003a419196400300744050040c06820800c001042d05150070200500c03140b804007818004004c00980003c0c00001c0300781c50365030f80c0c54101036105e20740c00506000b0f00d0050500b80707001100c1c0d8008000c010396100203131300d030814012480313070000302c3d0003070203003c1c48580412850662501d00301003c68840590700c080d0004000c0791301035900042d1680d440c40140da00607506031045445c3c00e5002d0181c01001d40f281001004003e0080210b03421a00210030f89018852001e48516280400242d468030b041c440c04409103155020750354154607449010340032031410b001c00c1e21404440824001c00100c01d211394000e40e80c0080c02515140c0ca07580c011140003c1c968051038000380c0600407100000d8104019500403ca1504d4607511403440c0ea05010280c2e500800d01d0f890103041c80020440754070048202d07440c1820048011488404a090940c060807168400a40205002411000d5507610002e00402d480351101034411025607100214141c03107240e403540f051504200c40007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 60681513 1250 60680263 60680297
    0x14030604110111030403060c020d09080313210209010303021b040e061303090b0a0f1202031512070315020309010b010903110415090207060b010e0109030b010512030c0604060212010f0303 82
    0x702c0182e00f084a10b05612503850b841990f0541003040c001da44520000607000380c02000c1c10000c0c24044d4019800c0c100a444081d5110f422485100140c03a500742000403004012034145407142d030003400503c00c81d607403480e0003556200394000ca20b40540403820542080e2409000d02d005444500c0020701c00303a19007109000042c01d000390100c0901c50a40c0002038900d0a1202911901e8455201c4e49003d601c959030141c407200980301c0e0109541d10400030845504460012000820700c10346140e24010f001d80003c40c5081459040901803203504031072605020016002540300d000d0301c0000f441099603682c0103440308041804000c00030000c10b501840942044c2d0710529010301c10245020303c07145d45816a40413648141001d4032225110b1500032000d58100100fa00010030030700e804483d040c038545520f1010401800303043e114483d820017820100c1e20400940b8017029249055600300d00705803030301c01d009600840149941d904550000106d416100d00400102ca030940c641d120042c51034044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 60682763 1250 60681513 60681527
    0x203070b280c02030f060f010f03030f0f20030d0605040509030d18020405072c101d030303010b070b0109060303120203043801050a050604060f020a021504140306041101 74
    0x1c00300b003058120380c40016035402c100b06008546140041c15143c205201e01c6000c03000142c01034919003018480800000b6404400c00100d01b07075505d040c0130b240c2d1340032504071400b40c4041e0325003c0c0d40b0711401c285021048044004c0907000b029407420002940d403202404180e4100311421038480c0c00c01c0c0300c030014441d4190000003050341025088011011568005003c849003951040000341491b1440c1c44a07000340608080d2041c20900d010b0b80411030380e00054125015100b400c0104001841000308403403042d625142e0a06005007600d44a42e10380d980f1001e540c00c4200b00f40e6002d0101c100000300404648902c1082c2d98250b13035440034001a082240c0042c2d403003d042103412000b644c031802c03440d00c1d50281c0464014246008000078180c0c05150645c0300406030441e61103003004200400840c0d5071001140c08491181c00c200034041003102e400d90034030022000181d000803d40b02803d030001e1101c0c0c024416500c0c0c514400304150144000d0550369241114001d080b03c03c440b5003c280c4d0741c05101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 60684013 1250 60682763 60682837
    0xa14040e07030209061e0301090b01030b0906060906060901020a08160201020d030e0613140d031b11030304020d170403080403020a08030a1202090a090e010c0905010c0c03080d090f0c030203070b 85
    0x46c1c006d41d0418040403900b101c440c0c0300140d854118080050040015603644950004651401044a41840000181c4c205005800306200d03a000242459050b402480340040031504400f0181e03d0746a40015900403082542d1300b00d005009059020200f14007a03c0351000d007802440050540d40d807041c0c0000701081e0f501d20295501c42804c8000401d000003001400d0000c0555580414224055441e2100d10a92070b8050010b001240728503007401a00007055039403064046502a0030f48190b03042000b00080d1000b00038a00180004012082c0001701c801031089a100b80c604801e0107a903501a140c40e800303600784403000562508003010714030110350064003a6141c010000723054141e9880d00c18040380d2580c0f01842c0b00fa510350400300301a03900302c1d6103400208400e081c000c403404400e03650080001d1a601000384013040100b81350402c1140d652044103c59403220603903d006c400d6081600440701c0d140b01c1203103e449803842c007040107042c0c0c03000e865040e00500c3e030a0303d01e1145440000010340d00d4403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 60685263 1250 60684013 60684049
    0x110d050a0f0507051606080a0207020102060420030604030206040c0f0e04020f030c0303040f0905010918080c0115090e06071115060f15030417090d0201080709050a14040e0703020906 80
    0xc003048011407400d009050301715940000c10081940b030f004001d03143d000014141c1d00740e144180014805070341c01080c3c80340e1196101c1120300009002d503502c10202c048901c40c0a405126000401c0109070f000102c01c1e00540c042c2c94059105a42c611104005103030601582c44860f24000101f0010304201000d185100d1004080d46c00d00c950703500c0824655000b03584180312500100b10104041c010a1003aa130140608203018014041a01c0740300000c2c120404000b407145a00103114140c1d0076007907003d2003201031400059042143d4540022024051140044005000360404501428042c0f01d9181682c4c1054018100500a0140c10300e000c85000f0b014036004102200f18000703940c1d0340c0c03a200030060300c48007043c0c0c2c0741d0509003411422101a410000280d00e4200501c078032640e2107484038901c0c1d85d824070740700d01a640c41402c12030b980f07000d0760f12041c1c10000c0900049a040141036002c4500d8005940c20000700800c0617210350b40307420034071000e504025104049400ea040640b00d01072500b240e2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 60686513 1250 60685263 60685267
    0x110a12030e1f032f040b0d020706110c0105090d020d120e0708011b020a1106070201051e030901200a030203130507060503060907050309060a05060301090807060903110d050a0f05 78
    0xc0c021003101d11440314245000039955000400c0c02d0201240a94100f16140604c003c2a08000100f20041c412030040c400329004c0458154000d03105e5404032201d203070388400103201740d40c24400c81850980240700402215401e120010709480c5000400d41d100d200140e0081001508818040d03412215514510007400d4807040408031504003040002d00509282c00001100b006ca00100d68030249060321040454000c03080b8080070954060354089009000c4910903038803019440144d6a0748218a11520821000611480d0309a6100051441107400c200240080a616200000041a080100c43c5014014012100440c0c402c0d405542c0c0000e000c694450812403507141c1c0c0d840e00d440384e40035000140000042000f1801c000e01120303040344850510a0550405005054440400502c102c06040e80c40000402965094221010081d000b810440d510700e402d0504c4400b4060041003038012601d8038041c003001c0040065181d509071090341d5003e09001800504440000b400040e103002c01c882 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 60687763 1250 60686513 60686539
    0xd0809030d05040c03060615080a0b1f030608070f05060f03040302120705030a0221071b0518060f010215010e0402031606030c0801060306060c0b0c0d020406050304110a12030e 77
    0x4107220b280d000c0d502401d205200c491a5182003010303034845e1b401401217001c44402e001c00b4503400c110030541110002d80003040050b680c00c0800c5440036644450602c0b60b01700c4c8403000100c2e0b0594030110540790004141c41d0b209495102548402840d0b03c10550005800c01c60310a90340c9102c0091340d0018801d105075201a246048c940120381c11602c0141d038140c00000e94010384a80400160310b0302c02c1e8111808004500a040c069541d002c3e20b072029051411244072006000d008103140c00107800002e02401ca040d8020403081e09910b030440e441c0f03002d084050980f042540c0000340c00c00300744900c040c0710035107030b070a24902080034203019108981600c9168548440d24011110003005451255400124583d00790801400c611041c0d20640c14146840c405006180c0c0c8003a1400c840d540241d1070300907984482c514001e0520038440815096131010401280c0745038400020360041d8003618400c020f41001c2c500700680c00c0186d10440010395201460403001034003910885c00c90300c00040950b0744441c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 60689013 1250 60687763 60687787
    0xc01110f120702061006120e030406180807120f030309080f09040c09030c0b0a0203041701020408070e01120b07110607030506180405030f070c1505040603050c0c0d080903 75
    0x820409000c0200d41c19a01e51140d041d016480302c1684020802400d1408a04070302404a02900301002200241100e802d011600700313400d0342c2e1010088036507407a03481c04002c280403c4d440b0380c1d450400c001c4400140b01c55001501e482524000d082c41080c50019a8400684882e111003c03401d05071542c0c54140898030402c064a11034940c204000d03540d010b9075040000326880c4c1c080b02410702c0024070080c004580c04d103400100342d80c100410a0340e1103c09407016451400f4a902003c01d0242071841000d844406401070003c40d003ca0301180e01d0151200c43c00003038000e09014900041088490034408200740c450b050350041c00c142406419452003c21a9081010440301034020a4542041c070078141004032010210001a420403207031410310b40c1d6066107a1140c106039071500f060100c3c0480600c12200c4034000140586c80c1490368014a400014003290418861440428a4a80002e4540e00c841d002c035204040c10402600103000e0540e01510124400b51424005110034070040c2c000310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 60690263 1250 60689013 60689017
    0x6331403010f180c0e04050702070b030c1305150f07060f05090d0f020a03091e05030304080115050103090213052809060c2604050a06110306210a03050c0111 69
    0x102d044001c01c800d0800c08000d44034503002845050071440c0040c0500c84039844003040f040b1074070864002c00c407030325040400c078a42540d07900320a02030f503000014007032114140d00041041111b440701800706c1950351410401c61b1005551498202c60381004200014121800104011842121300140281c401300e0007101b1268100c8010314103034003d00b42c5e401c0c980c1d04a826102c900c580d41c4014400280130b40d03001004e070030403885a102c0c4600c950303d11130503205607441d040000e80800341c216034642e9583d038103a6010302004940403180b07420500000c1880d5209000c0c594540b0f401410554400d030942041c040185401401d8044201502010f110111800d907000400c01c10505030105211600303062810032900540c02e01d8007070050013140d2644004130078126600340c28800c000303a881a41d03182002418200b0080000b0700340c80c03518580c0100007240707802960080798161001c0c0d400002c072072040c1107041041d0440c598a43d0280227080b001034440c0740105034022049001040c03031514503290a00d15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 60691513 1250 60690263 60690269
    0x90106090c0c0507090c050405060310120c0e060303031014120d0e0103050c03060d0206070609060213061b0803010902090303070b01030c0e0a020403080306041a090108060105040633140301 83
    0xc0302140c0b041c0620a04000d0003001c0c106054082002151060015103184124410103000b01804000101599441d00a0710300403c01c00b00800b510f10f480c2c0c81c2c05020b200c51030243c0440003a15801003402400c0010649104030045518652544e05000103485450740c5181c0e1550322000d2406c4124106ca001c3c415100e032070700707962030307481c04048524001b40c00d8541c010200005094140100070196031510f905907411070b019104287d80d48000d04218016141911024014600000d401d0f6910074040000ca01110300300d5549402a82407030300c0904040c542172201602c0080c06000500407040c441d03004200340c3c1801001c8a241000b2541c4115200d2001d0344280c07230081446008005590283c103240d50b0100346587c08524260079542c50f0340150001070003081c0141da88001300e5500a02108071a4608000100141110f603561095142e0f40c0a00b400f40c1400341c1e042000000b85000500c00241c04200c41c46003003404000450740200700003950030f44c3c901c104030001544102c5240103c00450107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 60692763 1250 60691513 60691517
    0x60f040609021906030b030f15040213140106030501050415030210050d1d0f070602030406030b060708070c03020102010b030106050a1202010309140307061d150603030f042705070804060203090106090c 88
    0x380f07518200c00030b0221100d81100728000d800c216489041c440011481940b01c500390022048180c64a0021441000181140c071404900d0052403140c0200341c40700d0203049a0702030342c0a2220340c1e03c2d2000d110507035a144080c803038811a01e49061005240a003081501680a032801c5810008848410000e407076506048003181843c3d0f41d6600c0c0c0c0b05905000070803140c04500000c1a60900d03000c0029035920a03840307441c04042d031300c6800c841540e60300d0f000ca07150150040d100342c0c3c40b84c030581400d285680da1888100d0140d8648100e582076030a040c02060120b9000515140c01d40340b50600d0003840000c0787c60103d0405a403040248001146043c0354205c0d00e8004009513280d1000d0b01d4050100d40c840f15074500511041803c01403242c0001822140c40c0c203c5690a050644406021a113503002e840e81d104030100010038046401c0c20180030041c10007004801082d42e4280c81c0301c81000311241030b03482d040000d08400015010a08503001503401c850840d0000a1003a0744003041c4040303508c4211030b200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 60694013 1250 60692763 60692809
    0x911061206100906090b0306010309140c100918020912030705070810051506090a360e030322020405040b0f0a0606020319030207052509020c060f04060902 68
    0x15a814228440ba07800c82c0c070350400383c4070141005000f910b000c0c0c5074807500040110000c00200c0300d91007030300800d222942c000c1403940c107010301542c0c0350f0b100c0820f81d1a45000c0c01044100541051007460010210342e0640c090040c0900b03011092006980110840d82c0c01184c100e041000358a010801401540e02074000341152078200b0304030380d04114429039001074039820542800007140c20005603541001c4100d545a03a0340c0c6400011072440c095540c05885000303102c2c1918000040001000780980c0a1560107501c0b1401900c400c06c01c80304c0390044810303540c0c02480090310b0b04942010200091018280040030000c16a00040513541c00b280c046035a45070b00c20a20003824030107110700350401c0f10f10009101c842d050000003940e070b0043c0c00c000008244140c82418069020f0350448a155401030300750307462031060500e2000c040464807050350010044580002e1034600700d109560020740031a01501d41034079641c85090002d880a40f003a20303c0da959094207c0169036007001e8400707403684090041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 60695263 1250 60694013 60694021
    0xc0f050901060503090316140109031d0102160603020717030114041812050906130f05030f030703050a0c0c08010e0604030806011805061b070602070302031011030a09110612 76
    0x500c4034410303440358040c80710074001e10414040200a41703403400030b0403100c0c06080340a41001c000d0100740a01c0141d05518204811040c181e00c00018903860451b0a0107031802d000442c0120703034a42d400d100c0070f0483e514004052043c148290001e00782a0301130100b104614090030303c2e0780322070342c000e912070b0107000e40561803041f09042c103000b070710138100c0100c4c8010300c40900d580f034070b40381c10800b85c0781c40342002030020f0010b130269229001d031030180da80c413048503504680311280780004050780e0080038407074402d841000001d01b600000703e85215a056490506100481c030b0309030307440340c0c201101311150b03505c0c0240403030200c0c4248590680c002090703006000c2802d1904000d84403a0740034100342d040280035107108040003188100101214402c4d10704076500e401d09801017400948445005156000d45140081c2041e40003800360f094a000300d042d180c0700710410b400c1500303d840c550034840201d24107100040f4404c841d0f6110a42260103003599000d902d007880005052640a8400d01d0a0800800240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 60696513 1250 60695263 60695269
    0x2060a0c020a0f0e0f07050c01020a0905030f0d050a0f0504030b240915010c020f210105220f1104050a020d1401051c052b020c010807120c020a0c0f05 66
    0x10701c01840c40e45111041c0f6403c1c44881191850014100324600003003c003c1500203204800300e030307009040c90f4021505c030074010100800e40201407248130f200b4810f108104100c12004200300320076a0668813802d180001e001416104c0000f0f1403012030500500b488004041210302090f00d00ca8116401100441c0c0c00c00c03400024140030059a0f540215120010001c0342441092411500402400c0c64030b5504d25620000e03140030684039217583c10015100108155410003500a0421805040244050340e40c0d4220f50080b4220060226005401c540300c3c10080b070351005402c1031540c01581004107050007000814103039076003612800003940d800200c461511145114201542800048503142545003030b00140000901c2c01000c494081c844401d01e0030804200006007032510074000a1101c415010b08801e062480c03804010054080d0f900820320641c441c2e002284900e60a403a150010000c80c3d0301070b8018101070000b2819441401210408509024800b000804880c24210f17411402c040034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 60697763 1250 60696513 60696529
    0x1203090e190f060506030a0b0d080408010b12010b0a0b03090a050d050c0f010920120f030d0606031407180b0f0405010212030f0121210e030706021203060d02060a0c02 73
    0xe04071a42d4900304007440540c0e5101c00b01d0f0f4011105030404680c0c03060300d0b400110319103c4000010310105c40091300140300d14040d00100342c0360500300e4003c00c02c5080c2c02c00c03e40c02d03903561402141c1d200e48041000d01c600703140a0007464000d0180310840f541a4200e60717070a0310380710340140307050040303000072606030f440d500200405c0c5516100d4034002d0080c10216070f1071a502a0ba286400700c1000301c01002072180e034840810f040000e400740350403a0141c1805200950302c9a2155003126002d504018000c40d210b40a4020a6084140300301601119074070b15508590a03a03850350503000c0d800c410341b4009146002100605040300e81c048030307160340364030b071400180c80d0032401883c5030044d440c18000c0000346400000c01c981100c0007240c03031105400030351910000d00f501e600070003803078140704203481500382220320011540d1455684480580500210401d5a211518498640140d00c44207840d8051a000c41c082c0d03400c60302c06482d09102007029800100d01c0e0300009450000100c0070001e440a624003090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 60699013 1250 60697763 60697781
    0x61c1202012406170403020102070b0a0b04050f04080a080c0c151f0501022e0c03020304020a0b03130206090f0306010b03070201050a090804050907020c040608010e07080d091203090e19 81
    0xc070310920343c40c00c20702501e40312003800d03e1007224261078009803e040c000e404035100d4503800040042c20382f611250070402419140f00f142c0c015803501c40003401d28008510703091f0180e900f200d500d41c00c01c4480d280442d00004d008065043c1c80b80c040c4980d142c02e280070010406040c0140d50144090f2030500c5268040340350003450700c51442000007041115907004501180c504890843c602240c140c03d10345111500907801e0401c00881c81c010380315020950590246006a100b00d865000c0c066641801c0f01c514001a200b034481c030400b00100b44d0042c50000028486040080e041c52140b8403030314006410300000360b001410292000081200c455420310400360300210200c001c000e5200381c0d4a40d101203000e14007406010b1803220740803400c0380d8000c2101c40403201e07000307009100307254071401068041c100865000c18035108a11000c40c8200000c44c1400c0c4011482c2d0321741030203926044820450342807206c0b050342803051204001c40c11104c26207a82b446044221060755891321030081800483d0007000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 60700263 1250 60699013 60699071
    0x18230301021303080a0302040312030e150609060103200a02032203030e04050c160c0911040e060d020a0e0c040303080105120a060e0106120f06050c030f061c120201 72
    0x10400c45402110b551102c2500d80000d5415150a0141c00071790091095030406400d202c0b800c5c803101c204035410307000b4901a07410030080c1ca820311f0f07502201009981068071b51b00d5110200c5800211654402d602c60b00800002e40c0300101000c031542d1128419038810300e41800140c1001640302a5070b920300c2a81c00c41140134454850340340b4656100100260342c84104035202c0d41d201c00100e0b1650982d5000d40f203d900d2034030108210f91290740f0304480000c2c494030503000360300d08040380408010b4582e0143d601f151280b04022440e69034200402075400380c1c40b0412a4815004000801c1e88044a5045441402c82c4511503a445086060251550205a114500c01c1f601c401c01440301070004104100450b40c0480041103004810090a015000a0304050002100b2006510a1008031420401d1840c01002c0810150b11103540300d11061004880884111614102184a40c00c00c090010310140c2d507200307070104c0032541c4d07558904450b40344106800142c2d1140028034250780c10083c5004610041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 60701513 1250 60700263 60700267
    0x20d0c0e160e01081005040c090501030e150406090204090f060917160b0901110a02160509010803040b0901050904060909020328030305090304030b010b0c0706020d08040803071823030102 82
    0x4140051280300b003151000c1c1007041000c049100c1a881a04620141c80000e0050001d00081c61006200c05198819603000900f0b00a680d0303800000402c45c0300a260110020750300950b144d4a43e900646408142241c205030b8651400000c614614070210041d4410003020800021a050201c010404041380c40b01001007001030112010078074a501120039401102865190303900c0d4000d90042441e80905009203000040c00341040e94040368500f111040c801c1e50390300b2075488000340500504240159000cce0341c0b0400007030080341d07040030180141020501d8140e1801e512a0013103400e880d01135004120150b2036685007411440d00b845100c0984000e00b050001004502030200503007000d10030081e0505550302d011803e9050203000302d40c05560059224001542d48107a04040d030760080c4a0402c1502407900082000740c07020440810001056492400329111a11001c0255002402003820b000a1a4400d0312960020045100415080c24803a910071508900d920300b00c0300c4094503c0c8030342d02c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 60702763 1250 60701513 60701551
    0x20f0303010506220306050901090506011a0a050f0f0d0b0102011808180a0801380607030e03010b04090809030727020304080c0106080c13050f07050903010603020d0c0e 74
    0x202e43c1591141e000320401d4004200c2d03801810805005181c0019118604100400c10340d208150000020b19205204903425a0b036106a14440703904000d0038203940f604108400048280f04a0140c903e20804402c0c0340e00e01411f00041c04803c2d805282020240758850f14407011a42e02071244102002c00551010750255080c0e071070407040d11410610103003140c0140720b2040e9035102c0103000d0014015840c005c014001d40003c290900b628410b01115900a505000d1a00f821000c80a03c21501d000740c00c090405001d50742c16155a541c2000c40c40d019940c4071140c1c48540d4a9008400d003042c003541031641d94601c840d05043c00c00b40c440d008001d010920440001c0102100445442040550b000040e241d880764a01600c4606c56072450080710341c00c009000c2008600803d103400d1420003184d640c404400c41000040540d442201e52600c00c41034040050f0f8018043d40051032220401000003844907129800a2010030350304070140e030910010402404078801a6164130303003020440e02c1c10105694 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 60704013 1250 60702763 60702769
    0x8180609061f08100203041b03050c0d0227160e0a1203090302150a09060c020102060406090201050c12091201020913020a05040302121c110c0d0c080111030403020f03030105 76
    0x40c0000c207602d00060315192010814200301c201500f4550181d511101e440c8078581c2c0a908241d805940302031400c403207103000400300a04101200e512002404104808508021005604103010380c0c00540d80013a00103010160000100c1214076400440c9031070503c140011201c1c03080000d0b94060003841102c00290342e690f0302d20031b0b00301d40031031101016009403441c044914641e543d000035000030024601202d203141e400060500703071880c0e5407203e04581c3c0d964001c132808064248041c0c0035030400c074041000700303900390030100680b4018100710b0b24103c2154681440d01113a03a200c2c0c1d00241000c1407a00351850f1610043da10303249004001d6003010034000006807942e01410890300d01a600007200709205000f00c090710001c0d60002e020903c0c11002c10001e6071135400d107803203c42e601901180b40084c0c15008214070301005109900038102d114030001400000380600006440700d401c40c0c1c0c00004d10403000d01030350001d08048100759407241410b25010745032418a000911480d0028001403056407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 60705263 1250 60704013 60704023
    0x30d050405011d190605041509050a030e0d03050316020a0b09031b073c0f0608100b09040b010201090b04050a020111060708191e02090f0d17030603190308180609 71
    0x10341080b00011b00b80c4a038a00b48869400076000c40200c107081410304014000d01040e40e801842c020f4403090205400c0c0f10070000010302c0c140e0700401150b010b0021941e102074030140452401c0c61401202c00b03100403a1034401e0100821105040654030001e4104104100c0301018a03030024030100510b400c50420f00c803001124403001038480355080b030000c0c08001100c901640c0840c0104011007088541c0c030380b01a2907000c000da000718400320b5001004503540c440c141a01c0d9040b00d1003109000d00746240402008003170a01000720324111741d00c0303403090004105203d2510380114401e000505030304520f0710000d4264051300c1c90100080d04070408120186800203c00790b071111106081c40044c2c0303c2e0307204140040680701c03c40c903250081140b12183ca20400d9004000702e10007114030201040800d0100044c0c078100700e90007000240c07101000c1c4002d82542e00619045030004080d1a040d150a500415403441c02d4402a40047d0702c1714140070502c0c5403041034045042c00b14010300403074503040c0c994a41c1c034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 60706513 1250 60705263 60705313
    0x1308060103050d0c1703071211130e060406090f0e01051f061b05061005040608010c051801052502090c090d0201080702100f02030103171e0705030d050405011d 70
    0xc4044c265581007000000c1c40c01d8142078080055030344c0c503803c00c200b00408000141d8555420546805120100c070101d1400707403a400e4202050203081d00c0c0c00d200d0750b0702c0c0c080070103031045e50043d031142004202c42d01c2c14002d00e018650054000a001d0182408490a445001d48042011190350b1403400c40e00d00c0019150050b14400e04121511007641c80d4001100c0c05c90b96000381941c01400c0900041030120340300307842182d02c1110b0901c03015031120b002d01e080b078900d03100d10301c08141c1c204010f203418403d00403074034281c60303050606d42d0400c0e0032502111090031070260000c4080201c01580401c40c40c10341150394008400340c0c5c0e024200f5800710041040d4107500140641800707210400a19013520802c120a500c9a10600500034142c04405c00c0011317400c2030004032042042c0b89850000d140015080d503e0241c0c2401644000300380207045101251b21001090381d940c0020408100050f0643c001d1501444c0305100015040c007405000c0f00c030011100207400d0301a0882c41010306c00f80c802198501c60 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 60707763 1250 60706513 60706517
    0x105070605040302190302030a1404051809120a0203070b0c090603010504050406110c0a021518101404060906120c120c1215030b0c09030712030507060f021308060103050d 75
    0x705880d01d0905a00d80700c6130301c441d1042c4c000d100501004055010000d04004040b5803680c25015a07485140090390040c1c0c000c980e081203100407a10004806441e44940250390f5a007610007880e006910700d04243c0c410381281d00941e20000d4090100041000420707400505584940e041c84d83d1180091f48520042c8a42c0303208580721400300d405d0054660144000500740f446550343c820324030b0546a12124602c0080c1d2054071040c00c00c0303c41801b0502294440350000c07003443c2c0143c08080420121114a91000d003c20020030b0034a40c410500a006001510b200c3e15020201c0b4540300e0000c0220140b1200064624240b04094940c20b0b00440f10b191094600f103004207024030841b07c1100c100f003940c2402548030f030802c1d0441e807120034040005000d407402840c0901d096500c0d00e421054900c1080e140d181c0540c0101c1c2e042003180c2506404801035072091900f54a00315494880405858080320604010307540001c11044200e81e1203080e50041c00400060f0000b0340c03550721050744685445164500b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 60709013 1250 60707763 60707771
    0xc130603050915040b0114030c0d03140415090f06031a1e040609051605030108060601080a38030705360a050609070804111203040503070303021c08010501050706 71
    0x141e001070902611040c3c2078a055441d816252606110240c00c80078400e107140c3c65428106032480c2c0c1030210702d40c1e001d10f03800385c50510700800b90383e8104d4420300c4941c041540d510041c0030100341060013100702d004686190f980c40140c00d0802c08007405031180c03948448141480c00012541011100d62038161483c01100c0100d2551201058411410082880154800e150010129050b4480d5000500402000f81034820590701074a06854078402800f40c0c5525612850000d601588a40103440e480100c0d14800b0509100c041d14280b0b102d0304160b84d6460304007290700c0911580c4005100551012003c0380181269443e0002140f030054070481030040003803218840f003802090060903149888080304d15482546400060308008105c00d45286e0311131100b02012a10302889400d201d80a280c20110f45104010350f442042840806d5155002c46400705103c00600ca54061002c0c2001310701a4000e007864a00c0c01210942c280360703040c801c400780300c2d41c1c9005102690f0300c4419a840160701000000b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 60710263 1250 60709013 60709021
    0x70201120b060f04060314010609050a030b0a020f0c010b1302041503020309070e010b180f010f0302130509070207060801090e0606060c0f060a1a0d0201020d030b01030e030a0504030b0c13060305 85
    0xb5441e10506121200154001400042007036241c1c0c00500c3d0b030180e41c04500b9969886030021140043e40b442035651008003c8014800b0981c2e4001c2290040444000145010804134000029421403914461107941d1100030b03084608102c421114100a200d608520303040c10201401c8450b0700300420b14041590200001c0c0307058000700010000b408401034404243e6a403001001c2843e4040404842892011000d080300e80c00d01ba00e1441580605841c0e80c2070111058500720b0081d045030300b01d01c04680880d800000c20707841c0ea030300040c001c90042e0b015061039410280d001c0c0c82c3c0364040c1e105018291400325220096500805c030280c03c0a07049800982d10f80d4902c00395450155282210400c50203104140415a1303070340d502c14855a02c8d80030b03004415085c4101000300310544524003a0158101c649141126032190b030180319160b00c1410000b92107401011518650b8000c01c00240100b280081c0034018400c02044540d844803500402ca0b01d00408145080c841d0040c1e48142030034503442e88049 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 60711513 1250 60710263 60710269
    0x91407020f06060a1e030204090507080d090302030703080304060207120509040c0c05060f060307080d080a0c0507020a03111201020706020702010e09010305070b030414061303080109020f0715060b0705030301051005070201120b 99
    0x1600951f0010018440c0004d141400c9450b10458030030a4420701c5644610340a1a00895001044a40080113089181d10310b071900151640014021545250300700002800615101c00d902f0300708000d42c2d0307000c1e140c03401700301030000b2185900d405900384003c8051910028a0000d5030785da01c03204050120b110307a1212800700e4545143e5402c02e80041c012000500c00b82c0364410055440744072114401d100b5030021000c2540c8900c600c0c4e8000c7d4001280c12020f101113014074440850100000d025114890241100303a400c90300702c40002c0360500d80025855041d5030b445103191440190071101040c16500d542e41d03040d9035001a214180d1400c01c0440082d042c0072070403ca180755246100192421803405d14103824000d1001582103005c07076100710000c5102c82c80c80c8241c0348100c0c011000246440d400c1c0c0c13103814010030380b401c0d091200c940303688010648140100140600b144228011030300c0754100b40412405040380c090320320030800f0074464200544c0e03100810050f0300e0703200d5100145882c004404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 60712763 1250 60711513 60711569
    0x10c15020904290109150e280e010905060a0605040e0403030b040606020c0907020f030406030209060c0d0c060b0102011406040b030106030b01080f01050907030206091504091407020f06060a 83
    0x184034415115004030300601429680441c8015034241d940c000f070541c9500c0c03100e2420300030107683e0000449141c803120407428194401c1d48c0f440000040309040f0440d10003000c90181e003d401c49035907207a19000412032901d072405003a4004500b00c0e001d030910342c02d215004065000e203210b0f060005e04444040703070605019620084e00d00310301510a110003601c42a010f90780e0147d070b40842d030280c5801e00c00510340f13078030204035920f60546a50107075182c00e1070100110b02a41190320465400003003007000120030340c4104500190103600c1d454510081d580c1d4101003086510303655005042d03904103005440c010f0100e0344d4841d070120040300c0018510010318042030041c1401d81004212282d00e0002246a2000140201d020030300c02c0c0081c019941ea0000950b2a032559110080d0401e0060080e050380e031a2075615213040e2003012240d141041e0781c0313842c800b00f55400c0a80080d00749000d68140304840c1d81c144800c805821040b0010300d01c0d41051004204e03030608078030034542c40100800d04500940c0001e05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 60714013 1250 60712763 60712781
    0x70914060904140111040501120b010e0d0201090f0608180601050109091a0904050c12070506040603021b010504080405041b1d0102151e09060c0a030f020f13090605010c15020904 78
    0x3000b0070118444031782001040c2d00c580205030210f0071080382d209070f48140c2d00501c400b816044c0e50350700c02c040454083c000307803400f200000c0b0706004801c080400c00311550310b41c1d2001080107030380e5050340c0d042a107003a21143d0864041d803141a001000103002698000121001b1500da465001403262000d4104003401070603003400390b900161000500091210000d030744a616001140c0d090002d09204107440e588003203520030690054000c0c08104030481c02a805801d81203070026402c1058807032603141d10f0858404640445a002002c00d090100303003854491912001c1a51100c00c1c0005880b803c0a0402e0b10910020318410914a04004140c1d01c00c1c4400e0700b0001610701e240780182010361358141010003580b10181c01410b80c100045010500140d072074061003190002e0f40c501910100d00b20090082540e540407003d40801c4120480b00c02200185030f2903812002504e40f483c1440290000c1da81e15512240c100400b070300d1342c200803440010509080c6101110700507aa000082d02040140000076 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 60715263 1250 60714013 60714053
    0xa0206150607050a0507031e0f060e0307050a03050c0d030501050d150209040212090607080f0403050304020a030c0b030708160e0415090501030b01030309080105191d010203010b040503070914060904 87
    0x210404c010800000380c0717007060300c0c0305402c2d0030310f194161901c0b04940046544050308600746590200049009030344485c14140c1c52405403403810032692607043c94080503000480c0000c0000900341847d12061224103d07900e10f616041c090385d403505001030011008044060b040b03400b503000c400c00014007036048508061003c1d000755204c89080c02d1000c03c08008407100c2e00b003406030300002125548a0248140b0400c4282100440340d101c58804450780d4000030012070b008904102d0104c01310707080405600040c80c404180d00d550340390203600103241c514090902d90350103600c4040405025080107812083e404184d4001445606440141d0115040c1d607100051079841c1500102c144102c1c080518180c82c040d86810f0b11241c0c3d20b0006600300e40040b5641000402e01080d00124402d1350b030040000403200069580803800840f100508982c42a480500006c90001e42045141014024480203000144080240902d07520000e00c6401d1300810f900e10079000780300040d007082500e52481320203880b25 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 60716513 1250 60715263 60715273
    0x2010506010e090c2b0902130e03040308180604180b03060601090612110301030c1a04050108060f03010b03010e03130501021501060e0a030f03020607171003020f0f04051510050a020615060705 84
    0x100032000014035081c6e03401c1c0d000d0400c001d00c0f54111207841c041c1c510410b80c010000e500e401d1868641440c5500041c0d9414030400107858191100d56944c0c000d04064800d1080c456103404130010b40104460070b0802c02d6029030843c03000c0045980c1c1000e0403000300d0740c2034105000c00f1905034a13a000140050710b640900321401000100030300c0702e0f4910107130940700000d14440c814041480800514021880b0341c5000072a003000181490a05001e00c4007035050243c004034085c0350f01d00010382511502d5040141a5001162880b02c1e0b0701d284490310300814013800900360860008202410500050041310f06021159200000c3d68883e00c1d07091009540110601000c00041d1030000d40b9048103440c0100002c082d554849220340784a24028090381e110841407104924580c02d020040c028a0f070202d03804216040b24007441e840d9400303028458410b030b180401c100014141000b00800505a1030410400188500e07030209070002010350304225507030140d00005000c02c1c0029844c1c801c0e8080100b0038019 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 60717763 1250 60716513 60716587
    0x15071707020405010608010e3c04021c1106070203070509130320150604110d050a240e09031606020a0305060102010b0303070b180d0f02010506010e090c 67
    0x2084014251241c0308590a000503640c410b0111001c032028050741141c44960000704030f014442c03800401186103075500340d070303884001c880d00f11256105000c070181c640d220290400c821441c1940010202141d10980c280c0744a10356220740404003450b04000c1e014240000703101c0d0555504100e014010000240705164924100c801e81d5490550000101c01007804030b8400441e06010180e203403441c4028000600c0e28110040c8941e80c00c1d00040e04c0350f034015944084648411800c20000c0c80b5a000c01403010449080c4868040215440000e0381d40d00c0031440d000030f260520607050b40d0812140d12045400258031441c800d1415480784100040c41c6000003c03050040003219000340030003a440785c07410081c0c5c1d83c5075001a42030340c1041000c0c81e031503081000104001b480c8110619008007004118400f00c4598201c21850180740b01035250120300c0c80025400074035424041c440e440402883c0031411980010082004100050b1443d40c403220301080070701625181e10307131107103080444002c420344100c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 60719013 1250 60717763 60717803
    0x608030a0801150f030f0e0712031e082703070c091805030d021308010e03120117071413052a03010305030d091401050a0605040b0409020109051507 65
    0x8040303651940814044400010094400a0301d003090004076260072070303035142d803c0044000784240030400e4007199031130100340c11b4400b081082101801024291022240190402912803000d1101031981c01c0440b44181450a40c001241c42d080910204507880b000c0300510210642c22510301644003c3c400440c07290240032621806c09c0480349902000c1004080010110034400d502c5031002e48943e00401294410407a507030f0060070b018405045c5c403800d02d078940c41503c2c290382e004441200213a00208032036103055034100e0000d004203210a0039401807100440e4154640c80303180f00d5840c1a5000d89a240d62940b0303040c03954216403044400c200710a20b02480801e00d0316464403041d140210010021169400291302102d068070b4004000f1820800441486d1026240d0b4000454103c1c24051655028141c03d00400e80650304d0040c0c007060040c10201404100e400860000b44254201103124000d41d030000032000c2502c1042c0e0707c44000003080da48c0c20300305100d540e1004012808031881400352231 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 60720263 1250 60719013 60719017
    0x5040806150a2102090a06050d0f050c010f0f050702040b1305070201060803090d020f011407060537090303110c0c0f01050307080705070f061b0e0405070c08090f04060803 75
    0xe004540c1c41c4001601da41c0390703a401d08508802d446440a43c00014030143c90a6113515030310003418407010840d0717078542010408000094400b1254000c2c01c41044041000600141040d688280390406183d0074846006001000b02030f844428858009682000c3d0749442d000143c0406016010354050844600c5907001420104d13032000040d440c0200100c0c1c1c4207030110480c0c03201312000b404246003100030b400700561000701714a003074140030a44804400030034500d4044c2c46440e0103881300141d140b621a00845000349902d44000444451401c951241c41c158001a607090700c1a0400081c0444a481c4c00c0c3d0080003400368031444050301040348130074800001107000842c1001e45413500445100e80040d2860300060f00d07010042044480001c8d90644a20b014066550240302040c41074070300350f1a55008c454050000c8441d4001d990000811b807500410740302000301c0e050b20100700501d08010300030446009404005c00b440c1000865032240c0d1b49205000304d503c0300c001d0081180650300c071203190741e079 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 60721513 1250 60720263 60720301
    0x6050a03110f040506010e060d0204090e0706020c10080a05070e0301061839050906031e0f0c18041e02040501230a0807020316110310110403030c020105040806 70
    0x464403240e1104140c00c2c207004403401780d4070685803a0100038001c4200312240e040540d4920800343d0074040018640e04ca80950030107000d04001600c80d4030f04118000741410346401180340510724000c0380c501c40d40d40c030409141d8000c0340708200103003584464a00b216414032240c1c0704ea45c0356080000c0407d0101d0002201c1c0746101002c0c2c42000030000501e480e852000c0c880741d0448007031952603c801c1940015400030700d0005803902d007542c80c20689600040c2d242c1c0054402021100d901001000c05840ea50380c0a80c10a20740000e0b00240d1402c0d4070404e0090dc280c4208006403c000c421840c0207481d940c025141d000c540c490080c40b80514808100000c0d00144900c600281442ea8005e46504240200c00d2102c000b842d8824617103101c000094510110180111045200c100400725120711200d041001080c4a00d48000d00307010710400b0075103082c00521250f030401d03180007681c0e618418610100c0301181e9060400c400c0e803500500069800380540c1d8030043c0140038950420009000034003084c405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 60722763 1250 60721513 60721519
    0xc030605090d1b0b06150c0105041403090307150203040806010b030709050d0503040b1806070c0905070e09190204081002030106090f08150a06080706020609060f040b04080a0306050a0311 82
    0x2004203280300440d44043c103034038044450042201e1107404544040ca01d40e50040c000f506d00404000807002e1311181c0c1d8000c201100e000c0e55a4010305c402c0180f08900017002000c04c400841c2050040070001e52112801c1c0700e0074030070700c14072078a155101c1ccc02401032742c0091401c0415035441d903940d0b181d00301040e07104413414400100b404501281b107285c0030301d0780501203401c6001141450b09080d035280d19a848561582c0d2024001d81040c001940c0711801000040e02c15148a0513943c600080c2c801641d0b0064901e00c00e11010604000c00d9440c1d40c0140783d40802d80c1405006090381140d491f070700910a0b900300d01d005010b06080c3d142c2441042e00118100e0350b00c0d942d00380c4181d0380d406e0084a111102c3c082c031f441c01c1d00401540483d01103421500307038000e081c48000091031555240d03400c0c0303088006c2e444000940c20410801150303500c1440031543c0a00c144d4255800c0e0b1800340d403501890a80207200800500004c140d0128540c0b085d0300c2040900300107441203450b56241d0410f010700b840601d16841c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 60724013 1250 60722763 60722773
    0x8010e0708010c02030f0f0a020a020636030c2404060906020705091005040c02100c02010c0e0f0307030308070210090803090f120d020a020f011d0f0102031e07020a0c03060509 77
    0x15544c40001140e5004840b410a01d050107203419202c004d80c0c0c0b01782281030461080340d860030056540c0310002c00210502c03800300e100e24401082c0e45007100c00c989a00351101007008030f001d421614045800c001c035900071a01c165941400030000800d4000710340b9070248035030b404540400d0300d41d005030109040c0d03070740ca07002c4596039991901007044402040351201c69491007403004200b103041c1900410100c24880c01610031502c0030741c0c07a00c01100e84a103907400041c4c2d155444824515009021290fa642007622401d0b41c1c1c0d0300400c0401d40d100c41700e100080804c464280041e490394428014030720b94a40400c01484a0003079400e20320301c5500103581015407401080d02c44000c0d03020000d80001c40c3d00c4402c0072a0300b0031b5054940c2800a401c840d641e00b040d4064900a07200c242c0007032081d1105c5030281d240302e20b120400f0b4010301d441c102d051030170110241c0c0304105220300603600d050141c510500c010341607242c60780d800c10102e00b80004400d00802c100c15070100441040020341020b440f42d68200101c0d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 60725263 1250 60724013 60724031
    0xf0614090a020702010215060d050d0519050c03090d0c080a0b010e09010b150913150306180312090204020f0307020f010507030606051e090d06060f0e010302130f0608010e070801 78
    0x402c80c031458030002d001d0390144a41352080512901c5481e4410002090640f4140701519558144a500344881c400908002010b041c0a001d03540c02c0b4102001d140f80c014140f668804141d6600e10aa4031840e2092806210f18006c02503001009030280c0404010b0310b0002c20689408540407800303000b69020300900d500016a005014801e091404400070643c2d0700b006400c030301541c200d51100900f103400c11903401c0c0c0b280000d09580100c69020880d8244810920f1440c104a0300300d4981100c4117400410f0500683c020039840710101901e80c0300318400180034180d0340b00140c0248203840400a9182012081024258010440e140c0c001d1045000f804503a9400e002201105c0300340c02250080781050140380e084060f501d140514100c0815076840c40c06011500047e40c1c01d224a0017110001d4959000784444000c40001e24000c018607400c03e42030307505503170029242c0c0128612084610340c1e1741000c2c50800456400c0b4000a01c1490000c001c50440940103680321000b50282592541c00c0003100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 60726513 1250 60725263 60725281
    0x3040b0609040807030c020f030a050a050607051207030f0b0d06020a08090d020706110f0a1b08010c0909021810030902041401030206090603090c101e090b090d060f061409 75
    0x20301d1069503c59129840c00900703075010344256405a1050381c01282c903280485c0a62001c00c550160701703002c0c0c1c00034010b030703c003a12b0064608000100f5034020020240454410b1071404003805d1340050150030041f07424060034035000300500444070b1659101102c1500c203014400164024641702899076101860f41e0754002546507211620042d04005a0010030200300c194450300b0100c940036100000d9400d4051000c00080c075256601d10f0503100031840c0c025014000554413042ca0041000740001c1c81140d404004c098805440b511482c0306064001404012a010900b1402c04007000103060020020340540001c0007000b0340c24080340624a0300400c3c413010400c00d010313a8102d030f40c000e180d14038001c941418001c2a80020700500c105111b00c2040c001e5a948680c50024004115035400c9040c402e0400d030300d010f400c41c040140082c0a1907030740610401030700400b02c0340146401d0b24040321100140c900b07100100031001c0460720883c0b40a80204403084a0f208140140100702d40d20310f0301d511001e842e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 60727763 1250 60726513 60726529
    0x80d020a02061608040b0c010209011106160c031707020601140f030304061b08040b030403030606030c120c1b080a020c060a080a0b0607020301051005030f0304180506030a020a03030503040b06 84
    0x703503005000307128198051950805a2200c54840d25000c1c0c2020303a901c060601642000f644080d050b500031a0001302560321036100d0801801800080c4002c1c2014120345210300d800405071001c000303d1401020a15020b119800500540c600414001d880c1110001f52107550038000e030380207084115000185490000c10495016200901030340c98a846c0c0542603800d86038171695186041c1e0200c101e0004070310103002500c024a489441c4a680b49410714000303040303828940019051500d00442c060b5050360002000002d035540103030000700640e030040161071031880c40c1c2c01407221700760003140c1e0010001c0e00c41c0506507041c4141c0032a072007422440f08115142c0640c00040c0b000410000005212102c01d8002c400303041f00160920f403030f100144d0042801c1d80d404a030460f80301e04001c00100030b54107040104620041007007001d0b41c1080c1c140000c050444126010900301940c444011800d03560b01440700b06c0074030394024481c0d00740c03582e20326002c6d09a400c00c075000d0302c1d00c60824001441078104019 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 60729013 1250 60727763 60727783
    0x50a091104050904050a0803010806060405100b03060904110301110403060e010e2a0d0b04020901050a06020d11010b030a0b0103060501050306060105070201032412060b0d020307060c0f080310080d02 87
    0x30558106410b08080c040f01c0f010082080d2454400c826007240410903d00c0114064142c40026100d54074016040c0019100003422840c0340850001081002c9110603096039004001181d648000ba162130a00051040000000c1070b8103510303102219600c03900c048010000c0740d03c2050700703000341d1004030400f500b02d88003a2120145600200000d58200c030840e9220481203402020880c1d080c4c0418000c5546549039000454020305420300740300035890420781030f03401060100c400300403060038480004c0d11a00070003e000b09200c2c226000741c5441c8820b402001d2800340140454005807004e0910111801080c03006546980ca40701c00440c940c1804510180300b9841038588500d4000c5aa0044000b000005241208402c1c12000342e001255061841c00040c00380a543d205400802e0070700404580c0d000c1c070514410000b200302c03c4c005840101d201030482e25581407400300f1040c507040029060a0990004220040000030001e84c400358003410000e68000104441ca030110002d800d0340e41c1da00b144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 60730263 1250 60729013 60729041
    0xa09051e1903020111011a1c05010f050405160614090a030611120a06030b06130b040c030c11190602030c0d091a01080a030c08031f08030702030d18140609060d06050a09 74
    0x4208000d12300340240304034400021580018034503070450b1182c60840e1030300b5081c400c002c0e80711001d10003030100400c408001d401c41041101045840d0003806494135800103241308000c000891455603030b0b5100c03503083c4003d40d007041003480400c0001c0105001d07a0b001c5104c9c42c482c503402c14042483e00d0081d106174000d60340d000308400794130f4591200b0001082c00540004c020180c44030601d0f2619121030180966101107a100441c400345400400303420290810200e40065210441c0c15041e0340c9401e810144807a040200180d072501c030050100c401d40300c0d00000c600400e0904150381c04200d02c1100d80c1c80424291001c440c1183d80382c40c40340392560844c10b400342c002203001c0c41c5000407035003000007190400c1d0b0030802d0801000502e074441c4001142584402003030340010801600f903007401c0c0040351450202d882c082c09440280030341c100025101d800707101900b2503017040000b0181c451070100c411a400042400ba101c9010090090140601d03000c0c2500590b0072000c0020312145501070903141c400700c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 60731513 1250 60730263 60730301
    0x3090703030305060406081b03120f03010b0a0507080301030c14060408060a150f09061404020c100504080702130203060f0f0d0303050613150603050c0a09051e190302011101 76
    0x140c0703045000d0b0501810644e0f109a41c0e0000050740c00081254002500404106010040660040608025141a01c50070708001013100340032000c4440f0407241503e1110710710a44481614a0840708c900034568000d0110100000210520095500307d000b2a405c40d462411441c0110b41401010f005034490320b81d4907070210002c140f007000203805c04103e42d14152226003002e82d40c0d4601138003244417580214481c5039500d400788084041d000c5112541780e0151420351138010701c010015030f00c201403400110615940d4021a04014001040f5070030903070000c200c040c5031070340300300301c0340003588199207580c461100b82040e031060342012980e03400f042c003000705168160700c000d8409a0241c040140324980c030005401d4152480da07005c0c418810034160390030540c8840c6042800140454802030420a22070105000e50040c040e03004881c40e094440c240c5003454031000c81c0da40040500031200c0384a90002c084c080451000031142580c1085038001d98400d524860006041800c035075a81440024031503031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 60732763 1250 60731513 60731519
    0x100221070501060305030f040f09090807110f030618070f0608070507050709020304080a0201050a0c0503011a1603020726030a0f11010903081605030f06060c0a05160e0f09070519030503030a0203100803030907 91
    0xa044050405401c02500d0fc07a940e031100000642030000440c0e8034002030012141c42480d54604110b0310021b0700f19400c42d410740c07500b00603000c5c0074110300a05000400000084043c1080000d01ca070300f0007001180c0c0199120f041c68a0504000d412107807114005620b44000600c08501c0d6000b424074458090b100c0758611303402c001e14664902c202d10b01d10448280100650001520300403040d0001034003035030107000720390f084c240c20000c4910541e004001c20740d1181034500343c194001c42100c12410240c01c080d40580000c0c281a41c0c5800354a0b114030700707546040b213031809054100d07039001c3c440c44146607042c81103000740d0000c0d03490f40802c0e07540c400c00c140e01400194890a041c80100305940c400412100c940301284c3d1600c3c94689030740c221241440804804101020103108001e8000041c042c201c0d505241942c425a034540c01440303014860484405810301e11018920040081c5410805076540c900d4248a1030010b94420750b00c201110300c8091000410300b41c0030003035a024901c200d02038002c19103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 60734013 1250 60732763 60732773
    0xc080f150303070f08030405010501120b0c16050a030c0c09091e020609120706021b010509011d042306100207090b04020d050103060902100221070501060305030f040f09090807 77
    0x601011081d05403004008860128941584402c011886003000039620f203002c5c40c083c0c0c01d480048e0b100c00c1c0c247c1111148800005c2da8041c00c0b80d80602c03ca126541c5512243c10011206251203174003402901038681000305050303000c601e0385900ca000385520241196200d041c641241e4009001518800d0314007020030142a84801c2c6442c0c06000030f0690341020f09030400a0010302ca07858100300a41d000c40020010182c0600518414980d4228104460242d62001901e00e00c184d148031410003102c960100780c0c9408103e108100c20308050030401050078800c17420a059040d241288500000000c009140b6240100b9148450300140e03024045503031501160070041c010b038101382a8419001e0005035588142881081c2c000d500820011071620014010f1004a1207000d8580342190040000d0b0314491102e5420b629120080710319140da1007030341c4d00308240101403581004001c3d0100249041d40708800030040c2c000c1c4d9010f0070000074215503440c2440211a83c00341c0041c140d80084c407209000c11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 60735263 1250 60734013 60734041
    0x150e01050312072d0501060f05061603090b13060207052e030204080109060c0f08010503030a0f0507050303040302010b0a120b150102010e0d08100504020322021906020705040c080f 79
    0xb51050803110002800da07600c0003514002004003400e0036000035003013003d10000340500e03001462a02d0403183d445080c00007082c1d051080075402d001001c2102030b16020988100755000041894050b4180c8401141c07102050350f0109203e84401032141a901040301c0c6403c16205a00340c854080f5040d2820f00da0760079840c043c980b110414145642400009031005085c015501d19520a890005502002c1c2c04090b04180300201d405041101c60307001070007203490000884080401c9070030101c02d849a0365000b183e07144907021005016020100900c03040640541007050340038002c452030140c25454030f01d00304200c0903444001e080d00c422900460090300e1241e11f041c400031418400810b0b42c01c031086215142c00d10142158000940001c10400881c1d0030420100142c04125015441c50074181028a84003880e40c0500c0483c0094841c3c2030215690181038076144031440761160074103646d40340003a445071828801c5600550401c501d1046203481007080714450741d00c544074074105440d40041e10f5040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 60736513 1250 60735263 60735277
    0x1141512131b1a07030906051602040f060f0b0a0c030819140601080702010e070e0a0905100e0c090603190804090e0c030705030d020604030302030a06090f150e01050312 74
    0x4240942a0109107402e18107441540d5607002d9a01891501d601c01c40040d0324018a00b8042c0801d1100d600040e80c81000c8000b01c03055860502c0d2075440c01050181c8240d44910029400b6152144501c2d000c15250003c10031295240540b005480d52a10151300304c1c410107480c200000c0c003840041c0c001a001d1142c0c180c021907542401000c0ca125038120300d048039100e41004101c02c503500208103241d07901071b08081e4480c0e1948000d121201440444691f262214080c480088058400050640f0900e502240540d03402400b1501d10079001c0030303c040140a2946040c07090301030821840124103110604d40d010704005401801200c500c1030704032074a01c11080701280e60340c0c0100800540050303640580301c1c4140b6070202404540410008040c070b04100d40e0700a5000f50080803106c4074840c0c0202d641603105030075040c00369890f036481c20044011300d0581c11000d040c45c50130b588400a02c44c0f40d4058015400710351541d010140d00c0d805030501c420303000d2040940c5035000010b008125600a000b0b8145 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 60737763 1250 60736513 60736531
    0x20d14030705041208030a0e031c0b03010b04020f13050603010506070204020711040c090503060f01080304150c0b070903061505090a0f0204030c060f090902040e0711030c01050f01141512 82
    0x2860b8480311300300c003800301c141000d848401d004824003c0c581c0e440c0c49a09004246440114540b0700028000034000c02e00c881070f40a220307541c410301c4e6500d440a411650311810001c208540e40e0f400e0311404151a0880b003130b000c100c0000300310081031a0501100b102d050f10300041025040045a60811019611000c0c013210380440501e20000c40c1c1c4c40364090b21808400b55100e0401450400c002c1c1441e04078020311806600000d40700401000328044111020380f0901c000100103100c80b103100b5243c001e240b100041c02e100f00b01042044065201c00c50f0b4099911a05050052020b0201e102c904811903014651b484041d6001143c2c900d141f0340c1c0300c50081e065003e409400d155407134032404505a00d81e80b04071b011940072110030071291350004c0142c0242011031011418503007403010381c00e44001d0051000d0184022041603001010080040d110388401c074500038062850401090f42d840803082c864401b401500b0720000f65640380c100c1d030030001401ca0f01e50701821305072050109240540007808003c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 60739013 1250 60737763 60737767
    0xc0c1103030d0e01052e060e03070b0a0306140609010f0e0d080706020306090f0103051c140307090503010b061e07082701020d080603030307030903090f24020d14030705 74
    0x80c079a8268020302280c02c200500004842c1742070320340e07148500006e038400503101ea10b074404074080700d444501142c140d506034030300b07003a40300c505002181c600202908648050f5902191100c42c150381508600261070301c0d00240c6100c0842c1c40c05220841c002c0e1000786010500309106001084e02c500d00299044800400324402c00c22036482e00141a4010b00c2e042d224117400008000c1c50b410850603898100d0f28480c60950341e0361540e19aa034072910603540b030301c64000803050300d05e1000780701e845a0340c0000d1312416165500d0a003581c0181c0844041c0c400c4900950074001e144449240c00419030700031a800da141d4145642c00c50f91200400e61000008940780c200c14880e0030f44101c4800303981000502a15484528090404006423074030b0340c042071640411544404000003520044140c9400540c2e0781400304012141e85015111300340507401c01284030f81644000a1740c0f44480032154070600f45002c0483e00c968800380e04913165440c80c0c95607800b044201e24410001d01d040c000540d445103842c50118 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 60740263 1250 60739013 60739027
    0xf04122c040f0c050301140a0302130209030309060301170d140a05070c080307050610082803030b09090307020a0906050a0b0a03110307031a0d0201080a021b0d02060702100c0c110303 80
    0x70103c0f400380303101d1400220040014420314442107120f0450810880c1c002c034425140d80d00040c1d0140c00954080412600030500350703007540302042540c1865600804d4180c49603182c810540b42d1990b440391050300e9108520306c61000741c1c000d00d482060035503000b00240ca851200c1c4400e55a540c81180204c079440809180000c4480050024026903031041000d03001d076003015556054800455040002c20703801c124903601c0b0b507a12040143e2030201004912030546102c03814103070020010342003a1a0005966020090400e001100424a0610858190b900300c0e446182d040e08a8125018203504850141c0d01071040e50740f0800500308400d82c80c41e0205102c00000e040c144c2c1500191a00d0340400d07100c00e0baa180d1041c908411640c0c0c81400e07900c41c00001101d0300000c00c18200a4041a2155400207580030843d5500c040c940004600d14100c42451001480003951290212042e00040c0500c0c07408050b0301260380299008041141d9880207049101e03141c0343d0343c005050205551501c01003080b4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 60741513 1250 60740263 60740291
    0xb0d020303040b030f0c040807090902060d0507110d020c090f1305010606030906060e0f0c0d1508030705011503050706140d0c020a0203010509071809020a0e0f04122c04 74
    0x80001d0f0010b001c10036140d080c00507202d410b000c03014103181800d013414001840380c01d100143c640200c030340018001c5200080760001c1401841003041004100341000104074455800c0000e00106000d44004c0342e14441c4005002c0781c40e0640941c040340e1081c0c106021400718050a002c05c4e40040055000900d0f4600d00d5513a11b0854115038080c5010903190b49401c01030000e544540300003081002e40680701441e20f480e1905040f94001d28070848041c02140300c802ea10002e52100c84c0701101402d00101403500d510109580b5003001030101c48560a0800c0401381c7e980c4021004101c0317901c58020200a030600300706071000743e108940241c0011041c020307d60b01146902680640807065005000d04048600606007926002003d4808560120300c0c104400c0e002d0340140103407407031101000140c0114501c0080e5005805902003840c180b803050501c0041c03940c4d410882c0c021071007611060650b402c410781c143ca500e184181c002c61001c00c07100c14814a550161110003243d40020000101241000301c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 60742763 1250 60741513 60741517
    0x3071502030f180108060402040305030d09050309030109050a150209130f02090a12051510050d06020405040c0504090e01090f020607030908030d06030b0606091039120e060a030b0d020303 82
    0x400d680703095103107000f070110750b0401e1046410003405d540c1903180a00b16140c103a60fa202e0315606080543e980c009000c140b140c107205407501c604008000b40503410240c04d115a890300c281e80c042d2001c0b40c501050350b0107070b0b44500c225003442402401041d01645485c2030303900105a0300c142441c51075001c1010707102c01c0d6200707801000501007900080c0c0e400d080741e050662a2921400300c3e6082840014217116403a40c008000c101203030b208a61a00082d084e618000003c1d00865014680090030140e80380440d50300706000e441a0344e08210100201883d4001075820303035080c000d02030400311480c0601000f50800d00000d0080c41e001c0e0620019107691281c0c504d00c1d65000000d49008180c0d150402c0c010010083d002a401a8040711001e0034440301000040c102540c45d034001041c4100310310003130700d20500c88040110042c181c4106072048403121001c203501e00d4418100b200d1007a01140983c4035a4020b11101d6030b6000003401c13a80c01c100d50114182c005140400110b5440302c00704654100582e01080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 60744013 1250 60742763 60742777
    0x30204060609140307050102071412010f0203090d08010b030105040b120f0606040c030e03030f070212070305040504050a0c1e030f09050a020f0607030c060506010c060e0601080c0402070203071502030f 88
    0x510b180401d880c05481c0380d0b00e00c0b02d082c6614484c0c1c0003070f0b90800150ba80090485c00781c9000300c04c041c80c01c0c000c0c400007642d001c0170111645c20b03550800b9071207030030340400d40e000c1c500c110040029110020f600d2b000c101c8017103000f409140100c8106000502481c1450380c0800c0850401810303500040392241291442c1502100101382117901c1001001102d0403d401840704203801410117101180c0c0702000036881c3c2c04010041030a038078800c800152001d208200c104d4503202260031103070741d89640e1300f0010016030050080c1c501442c00c00001c03841111040c41a1103103404e0b01c1c0e48071803a004000b2146d0140c0394004845074105500c44c0800001c0c88a248074154603e0b05c0344006051310402032040c01850240d003400d5510680d4244a00700c0400e400c48480300f96903038004c1c0000b0300c83c0c2d25000162904800840041c0419103001400f003d04040080c2060695000c40f08403800789410104100c10f030320500800030b4050300203c004100441004400c0d100c00c2c0c403140156070602030480d89090b42c50308588 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 60745263 1250 60744013 60744017
    0x9010803030c0d0b1c020411070b060d020301200306010305011a160501020c0d030e0d021504030f0311030f04030306080118080913020c03040e01060302030f04030806011107141e01020703020112060302040606 91
    0xf00c03c5c001185040d11580596901072480d40381054502c0d15201c208000c0242168021102c03000c00100f150340a5108a900c00740c071020208602422190f203190700d0b081100c0003404030745804004901c014450a040c43d224000030303d8103151900c40309045605081c0f900b402c903110343d0288407812400c9020300c4409842d05c0990350014400c01c10700c2e00a45130a2031807601d50b066400031080c1c401c82203814050325070b000703416041c00c040600084804800414811001081c001404018026a809980156409140030f0340c1e0510400b03895080d000d080782c20030040200e80445480c811800982400090042d101d0300074000d46142807103400c070034182c0c0c1c0040c04600858000060502c003008140c44601e000d015545811411071804103020500c1082c064800340a0118032400034103168810030098092401e0031049d00c401c10364912524001c15500da40b00340c800c6007190700e008068481d0310000521082c0503801081c0c4245590010b42d2801e00c010018075825480308000700141e01c803405024010200c039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 60746513 1250 60745263 60745309
    0x219060509150903071707050312030a0e010b01081f0e0c04030201080108060408093105010602070602030910030e0a0609030503100608060d03050307050d0603060606080609010803030c0d0b 83
    0x1480c100500c8014592201040b45014050301c8030315140060014142c48100240389004a01c0307001ca2480c0882a07440141e0510400705244440301c6118050b5026081d1041c0a200700c94095404030300340d0b0703030141006000800c0700d0001003c10010000f504454042d941c44d1100c81d50301c4488003005001e08031454110014000384c100b0440d41d00c610310f2401040c540e409802941001c6c1e68014552054003200752081c0d40040b1031910084041143c04c221601c54514002c88200c017003800d00107003000b4442e22005d40a14800090000d001008480b90004018006068200b04d0102500100005110204507101d071101c03100000c1c0d040d01c28080c29034000d448403600d924040681454143c02070f000320b000c02028509101241d1a141055a15264035040c8140c490351107204c101c0da03500981c0307105c04000e414038030700009012980d030040c8181d446070365500355540c0d035660502412000a1065040325402040003842c4080b80802400009034040001314800f02c240c80001e40b0001a5000e49400c0c1040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 60747763 1250 60746513 60746527
    0x90f100c09080f2508070302060f04051806120c010c0231020319090f0605040302010f061202040507032901020a06060b0c010c0f020a0201050306040b03010c050a020d09030b0c0702190605 82
    0xc280200c11944a0a01c513100030242009040d40c2c80d00da4074440240075590109191059690b00010742d8050803000d015001e41c1100e10802411800b0140c2d021030180c09c84030038040003004040341c0f11540440c1a101c03120f00c0f048550902080748050403100ca107800403a050050036060880010401080034000540c89050102d030007049000b1960800104901c5c0c28040d50000e500911406e81050700702e807000682d50784500f000e0340904894030940300c103c2c0c075102012400070b00130810f000d10540265000c02240d5990341064003203ea40a203402c0c030840c0044075000380d421344440e19080e15401071056901585460740c4481c20b80318181c00041c88038001180c6801a504244605405403140c0c2c60a82000200d894000c0d4480012a00290400c1400000070b803681e04c4a41102550310030142c000c00004408a000402e140c2060f400c0341c0041c000c00b00c0300000c1070b10a100c01c4003503c4d00020110081e40760200006203a90101c40d0403a0441d00d0b00b24840180d415a50001c0020440b0382c44055079010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 60749013 1250 60747763 60747793
    0xb0a030501080705150a030b0a080f06061e0d030e0411030601020c0102071505090a150e010f110601050f030114040b010f050306100e0705040801020a17090f100c09080f 74
    0x140c001e6060b07684404030812880d904e8803d040d103404601d48625664203c180c608030007812440d014150031020408000030383d2003000401d80508a030380400c0c2c1e1150345a03401008030210ba1b8181c2001c5540c5030072042c940f540b03003503040310b41c245100b404c0ca80b9005241001040503903d288980034003030003003c800c111840d40c05100e0540611000d01c0a084c2d601d0400207040b0380c427038401d2424000c200d00807e100031682c48041f100c10140001c24550340f81c1c0310802c88001d1000d10019500350000b801c0201411b211401a44201c00b5020548003a100d40d81c2010180000508440b40180e0300d0342d2506103580d400c012030a140380c0124001c003980040c039030504816040c100c5065100750301a6004604014444200c0d03655542070750b4103000c000301c99031590002120030b2702a80d001030303c140d4800102c0d0024150404001903005100001d020040c2c0d588142581e11503010044084c502e411483c1003041d20304940c2d104440300d05103424401a080d444244a0745441d0001e041001503a100d0b600c0c04040302 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 60750263 1250 60749013 60749021
    0x3110f19060b0303090306040605070c0f05010c02070b04060e0904080403020423010605071a04020109050a1d01060507020609010c020118060320072004060312180501030614091806010b0a03 83
    0x300143c1c01503241c03018120119030348440040c009070100741e841c004a86454810b21600710aa0f40100c543d04c0011840d050050007005001c0303801d0050b2050030b4000038041134080075102160403039166100013aa4181c1448240400140111402c1c00c2c07c010100050380e86100b2070310308a1003024101c295400980004203901c0c03044e002482403060900103840022140319500e00c164002071035a21841e213681c801a00c82048d90b42095601c00b001c4140071401813400d0b1448500811301c0700c13100079180d90b10782060f243c901c14071780081d400c640d04110403580c65000304d0b502002e180c41898001180080ca0841e5442405241c0091000130789079042440d40726641c0341c0c101003403c08140780c1c91511038180d44600140f110b00c15110200e804488140300a0380e6643d010000030768100c440c4805c500c1303820000070081b014541205102d060045408a4079502c01d108900aa4010100c1224161040400c1041c6594014890701100c4075040480540750380038401c40313000341400e02c240c03915940000d20140a403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 60751513 1250 60750263 60750281
    0x703020f0106050402390d17160503040308060d140309010201110c070312030915230f01060302180613030c09111219060f050102010e030c0a03110f1906 67
    0x154010302c880d038201c005801220381c6c803000a0103010720b0321414030001182c41e05801d0003040a4050f2070880d0280c5900322050001420403000240b000d030303581c15000c490b00301c0a000018001101480080d0002e8095018a50040c000a02c0c00680305859502d4000c8801c111150300610380010035400a0f5503024010000610720701c1c582181801c09400ca0591b0742c00a41c1300285c500b501c2070030704021160299000751030707454003c000741642142c101003503000741482660341c104411003d0481c08480c034901010a000c0d5042c403c440850b03920300740c1d045000e9004030038101c01d21007400004402c2039950b0304c0100298500d245501c50303070501d10b05011601e12980d9200030443c5052030b520460881a000c110b80066100b510034110300e4032014485c000c440f1242640d0798200b45003180209000d010000d201003113a90990090180d8442800c0c0140c490103220305000151f1b00007200368001038001c183d64424802c1e41000c0300d150050032229245048840248080010400d03182002032081d5030082c0042c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 60752763 1250 60751513 60751519
    0x52502030c1501030510150315020702090117060f06030c0607060f050115020606010c030c050102071401050601020d0c140111040f0510050c0a030818010903080a06050d08030c0a140703020f010605 86
    0xe43d8915107689440b04c210070340502c41d89944103240560501c0b400b4401c4059600710301986522440c3e07091502c02540b20000503403180364a00d000258a41d14000d41002d808a08400703070500b621140c543c00920344d00900016894044d2081c102c00c0c548030035000e81181130103134170042900c500059020003210f01c1a08200b0440c0102d5030300e541010b40018106030007020a2802070100301440c01d0888d019010000c0051065000050391030920050800c04031117100c1010007042103864a5006a03902c0d43c2e041002c1d404078400300c402c540441c2c03108950030003600804001150b480d201d0394030b0015590003904180e1017241600414001c9003441188c54070f440c4040e0420a1421540c164400d58403004000004d041083c1c5100144036081c950b4051610720351800300074050220b6a150141010310121015101d19240450000d50f0340f134090241d00e806070308100a107140d5226001f0410513070744440014000e00440765042c61010b0805001000203901135400341c140030f078041d03a10301c0c01d40390141e2141d44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 60754013 1250 60752763 60752803
    0x30105010203030103030e0301110d05060a091e020f0d0603140709050c0405040507090b030106050a1106040b0c07050703050615011707020c0409060b04060603050117031606052502030c 81
    0x260741c000045038150f1ba09420100380e21868040024003400300807481000000002c180341c8207545040e000b040c054a011030300d08810540314a1008100c541035a41601d50b01140010580c0100c0d10b5801403260003001580c003454408141c0e002003d071519503000f01c480229620312458130001c217104410140902903400d224030b0808007202d500c140100c0c00340d0351045944034081043c20303000380c07010002408c0e000c4a25869696582000d03202d40c200c9021500450150382a075010130801285144c0b055a1040c407007050368541c3ca0603441070380c1200b0001c0b100b030700c80e00c0c401001213141000624840c030090080d004450848000040076200b0441c2e411a2820740072050202050700070900008462041d140022070400d14101503018160b85861660003d2410501041070f641c190040da040c0d030501e10b0105180c0c80c9080046a4900c40c1445021018845814040000b002600003541124810b0100d07048040882e48040c0b070750407084120780240c0c4c000540c1e5051a8018003418058200213074080c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 60755263 1250 60754013 60754019
    0x14030708010302040b130608030a030f060b03010306240311120a0302060705130306050a02040f05010c050706080c070b0a140907060507140102250506060d1509080c01020a0e150301 79
    0x2521103441804000d1103aa12001c4e2160341e0b0725500d804003415040c501042c014a035072615000d07280d03403201c01c40d400001d05140c10510154031a01844049410517954589141e01c0d40d11508024070b0300a03040b0f4020603c5a0756085001015046000036501950113107951200741403c2101c921407038024040c240c3c212003083c00200381c000c40c01540c040c10350b0405581c1c0e070240d54280e0801440f5034000030201454176007402300303c803041e40c064000d07181c1003820001d040c2d0301c6200554030f4501403a00244103600c000010f2201620581120307030003103860741303140b0308000f080d58900201d95030842d000114195039441080d19000310300708945c0c200c07107401e014000340360820600030200d00c075060018200804450701035101105c254103c441a8007018104962118411071001980d080000141c4492081f0804101e0a1508680071200503502141100500c114559090060402c0c14800c2d102414107002c4403030380c002d007070000740320020080d80c400c01000719075402c2158190b10742c480140551010f00040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 60756513 1250 60755263 60755267
    0x603020303120a0f09030e10020f070605070204060b0a0c020405012414070c030311100c0903030e03010e060a0608010608030301061407060b03030409061419060f0201090f05030703140307 82
    0x4902d00600440034801a54036a821040a0f040600581d03121900d400c0c121814035501481071026482d0840366011106450903040380e503803200c000d80190300d030403524080208034015402091014405007010982c950788841c0000399400c20020038000c24a8403185c141140f070140700740f9014151600782c500c10800d0703208044607010f02c416204001e0000e592700400345115440706527880c0707035400240042c9240e01c03071a00412803d00c804c2d02c04200c0c400c40b0580401c0342034034018668088800c0c1d403054032a5286880807031f40c1c101c1d14a01940c045d540c481081e0b608182c20700400780314200152002ca440e0707182008240c00c54400b503001911541080c001403003656031080c90038a520044550168559001d420b00030002d06041d240300390725100000d000510148a5080513040303603034402c0482c00404c0c94905201003244120815007038071000d440107010303140c003468401000ca402840001604071055542080180d01c5000c15100d0303034070201c4c0e0007041541c400d1700c0f01940a868112981541486200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 60757763 1250 60756513 60756517
    0x3050703140d11060c0708040f240305040b06100c05010e03091305040803041106040b070f0c080a0302070611010209030615090108120d0f09020d0b04020909030408030f0f0c031210090603020303 85
    0x1605005c0540060714005201505064402a000b0300b049190040e03544c040c0a00c942e0b0078810f401410310241000107042e540207208082c400c54000685403141d544810802000d05459051142807002e80c6800401090091140c80803044060004594a1080004224480d0382d02560319280d40c0c200790401c0001134810b0f040e603402651003c11030414607016800102c0d140a1504a040c1907038001c00c0d52403e0010300451884000c1c0100341d0109026214408180c84c0c0c4a411406030140e40b00d030504110307592180e641c0b6180030494100060908031007000003824100c00391122083d800503560909000d2030000052801040e410004040b5001c51021f00d6170507000c1d031002a10401c1d5900e0700311034030307810682001901d89c0e1b0003082e08580304014070340042c5d00902514103074001e403003240c000360350540d00004642c1038482c0f0300c000b1400c00d000d6802c800c249500c6803e4201d00c90509100d0705401c7e07003040000e003c00300e10054103074032140351103074101281405a038801c16000381082410000360300d000c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 60759013 1250 60757763 60757771
    0x6040311040e01090807050606040f05070c02011808150a060603021606020c0c09040b040506092d070f0305030301030b0c09011e0c170405030613020f100903050703140d1106 76
    0x6001c41c40b1002044080d0050458000c00ba0251000003544403c00c0400320300944141d80403581000407840741c112000888608036007034804107080390883c00c05513004980442020207921140303000613807965851818466805040701f42181107106210540549000c0da41c0940010710301103042804040e400101c15500607409442c08e03500141580004800748101c940d1105e010305180560b052a181025600004603003e6800f4050a0302040d0710b0b42002c00c01c00508151090402c004080f5400952054a55203007011000d1040c1000055500f002110850081d40a41c0103980c5962440c107100303100c0c0c5801400e075031442a08005c01a026a00190100c40c01741c1c0f6044e26000355860007800307a81c242041400904407804800f103015205aa0b0341c020030a41e83c003903082e5856601d81c03042014118052078402540320078110300d149500d06050705988621107003032400b0284545e41e0f444a504001c01504155841d0030003040008201004110440c1301800c00d18149151070550540c168036003038054 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 60760263 1250 60759013 60759019
    0x120607050d14010609090b01021605041805010c030b091315020c0c0a0305031e04050d0f020102030f16020a06080603070b03060103060306020d02070501150f06030b01030f0e1b06040311 81
    0x49410004912103521210680c00d6011050b40c1650b155807001c2d003035030010720032021150300f40003178080c040d4030201d034561401c00c5040e596100142840c04020280008090040500c400d4200f05004035209002e90f0f0488829900c0000d800c150010610428007401002e441c545d0780b54408160000d5400442c0c4145034a8802c0016218140741c10601d00384000e074010386912400349007011003400004402044044518a1042420030001103044100c1c0500e01c01c59500c11911901c41003c240c03015449040c6610520540780b130310b02e561940e8080c036004801d0040340e80b140c00300e1440071820720518078400f418040c1824000e034605100060380d11951400360b040740030f4021000c503003140d02a402440c06954429001c2d9102c0103085e5001009400400081d22150f0030000480d40350059032a281055825004001c22260308244068002e40420300040381055030700e4021034042c42c00b92007800403d1203034030044d05480840000781c1812065411b0b000e8440c401c10001040080e4580700c2c00340c4040d0081d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 60761513 1250 60760263 60760267
    0x70519031b080d050402040204090e0606030601060905030c0f040905060a0f06090209031902040e03120f060f061e070f0f020102070603151a07230d1b03050723070306050612060705 79
    0x1440840c0180c0119400000004e0a00c0703100200c0860100e0f03414480c0d0307370540440c0c2c250380c0e031200c0860305201d0500c03405406030444151800d4508180224264940d406800807c40c03402560300c0ca850280104d550329811682e40d000c60b0044802c5020301ca0003015840c2c015820b021b00c94000a45072242490712468251208042c07008548550304206459030580c000e0702d854410502101c2ca024400310744050309840d03c00f00203031072840c101002c094640f030701230030290420f01c0000b240f805000001036403480707030f110038800d400008405104203d00c0b01d128032200483c0d08124800a46031103002c6c0c00c140d00303042c10314000101001105410100301c41c02c1c01200300d40843c08a00b01180c61041d110043c10310004080c29041282a00800003001d00492003204e00c0e8060a200843d0303003000c01e125002e03a640b440d410f03480111703203d800a410745500a8014207000a0103501221a4507440d45803000c007508146410001d2025600c95154866001e4038502e00701c3c00e0442060752a4100244118140b10740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 60762763 1250 60761513 60761521
    0x50621010e030d09050105101208030411060a03060612051519050d110a06020a080307080705090409060b100311070335060a0512060c030606070519031b080d05 70
    0x8250000c1c1480303160300040ea60703036240f0500a0406082521000d40b115070810002c200484501c4851a04440a402030a041d01240b5a100d101305e40c405001640c080385040c85030b010b15a60000102108121030b1000103401c2c1c0b902e03e0142c1980900c04900507810710344002c1100c070303a5459041442d069001c50303010403440340c600320640403480d103900942e802000b202242410400300c1140035082400440300704402170707070703468081380d50740521314005004803000d2001c5140d85020f1079126030000c4881c201740c0c0c01d0820b80808102203900300401031794400d41301d030f00c3c014503401c0c20020000e07994a540f41c01e0043ca075002034811032510400e40300408100b0114400c400c441424410141440b0070010030b2000002c080400b44408202590950304c200c41e03407440024503141500c24680300e440e4180c05006140c0e14103429420303d8100904464208208200308000100b090140c0d80124604d1400b2144007101418002d14078200903031005c1c800d013100c00602002c2018a41504c0d002464003c01081a42d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 60764013 1250 60762763 60762829
    0xb010c170c071d0c0403050a021c080a020601060e01020c0d021509120714010809100506010e060a030204090b2710030b070809060906060d020d0609170406120506 71
    0x12032032091040c1e41c0070301100458480b1040c03840403058100c040c01c2e40100d0300e490505900e00e10a80c07100801940c002c00c0c1e075000500f007502c0c811020844842480b801001c243c1c484101c0303a40f00c041d0150050704410300621031560095056442442c082c401480f50085c0c107070102c1c070f00802119000c2e121704c85070040031140080b054115103002e0006401203690305010041c0f165120f5090280200d440d4486150308455485801c8182c8110410002401d901c80001500741c01403a000d0003481c104031012008804030384680c8014503005980c1d940c01070f07030b45280c10515412150011030701413161451008a0031648901c0015425007141e82444103819100c00364460b41d011042ea00045c120800c550411400641026095224a00c0300d0151451641c2d1703011342c592a0b2004881d00c5c0e03484440f074658031000d41014a401040c4611825000890b0066500c900d01240200080628114000501400500d42c000c02e01000004418424441070504000066100d159401c000c840302d1945504020000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 60765263 1250 60764013 60764017
    0x30c0e011101020c01090309060e03160509060102010b0303130f0e010602030406050f0c070308030109051b0313060b03010204090504050d02060f151305010906050f060f0f0f070605070c02090a0b010c17 88
    0x1202800204003103402031a020704048c44034407800c00411b00c1480140268200401d40021005c0b185a0200909050804000300e00da80504240c1c11903507210103013895910100f00600000c44048030107018107261010007900c1c078540741c00c4500705689000042018540000988050391018100f49850391900a458041030041030041d14491160302000400d00540500039410f84800000901071941d50680b00802c140c0e00c02850b04011804000255a5100e0700c150b5002852290700d001c6954a228030000e401d98009800c0400896541d8041c03004210381081000e85826850014089a1400b000c4140d03440800400c4010049550882d01d10140d9a030382c038109956540010400041d6103641ca03a000902003806079a0103000744150750807052030a0402d07121400d030501ca00d01d20b00343c0c05940c40c1d061b80d04444544040d00d8000d0280c2c10000d015802418400c084941d14625545804d0042042d9400040c10070b0403071500d0002001c10a0740d1000400b200245c000c1e944100c1d54811080c2d0341c07028 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 60766513 1250 60765263 60765277
    0x3070b0f071218090f0f0504050a03030f02040f090f060608040506070e06070506040605060301050109110301050613030203150402030c060c0d0c08130909020f0a050105030a090f0b041b06030c0e01110102 89
    0x1a920040c0402d6002c041e61081c411600d17100c408000c25078609407031030211081914007038042d600121141002907c260000d400c1c0000100d000f43c24240d41d070b403203040265000d0304189605916032182c00c95a03e010711405004241c45d1801c041e50f800c140e05c40310b880c3e000c040c15040030854104864200307034881100b240c1c1c5075680501207494919260808100030031095508070720950806000044980b10327030159120280442c0c10b040e01e50b07468101002180da00c0700f103d240c04806c4000c800000360340d0504c40000d9504101c02c0512440c40c04c0e10401d41030008588107188621418000d005446da00011040402c2c51942444180c00c441401c20440381c2c06040050340c032081e8400000300701141725030890440544203a455644522001080120030300f0140545400138200b840010070070403164000d071104500540c040c1d1000101c2d41c82d81d000010301111305039685440c501610402035250244200104150b2a0402c11001104401440f42120684050400c100c0031145c99407000c007075040743c02c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 60767763 1250 60766513 60766547
    0x50a020d080a0e060f120a090507030c0303030605060f0a030b01200f070506070b1308040902030408090906040905030301050d03110d020d090b0c0709090317010f0503070b0f0712 78
    0x1840005181581e11039000120541c005040080c185050b4240842515041c0d000b4040850500003840b900e200481002031291803e00e40725202c010100c1d03405e0217030031702440c020641080c1090450038007800f44c8400c0c1d408107014420030042e01c4000302c00b9a0984602180394078000c41c1104041c80100c424604121345000c5040f24181898206203000541c0300301510b9100c2610402e1750b94004008460003000d1018180070344010015075045544070b140441144103d0149082c142c40707000002c100e030070403070302110300140010ba004c40518003610007951020080b0340912242c900c1d84d8590f0b40320b00041c4603080c081d40340d40300301c40704150054081c401007418850445500c0c0c0301d1080001c0d6551600d5a20344042000042d0200d407441d10203089a0b84402c40e4402408094606005200244112841031b010040b210402800d034240e41c00c1024020081481c0c90441381d0b0a041c109420b0844a0344406844402002900c01c040f80c40c0094408880d08140107441c00c114503602514402c3da01c08210f03503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 60769013 1250 60767763 60767779
    0x10b04030b0c1b2112072003071211010905100c03060324290603060a1503050108070807030506060d050a020a091b03090809150d0e070816180504050a02 67
    0x29052900182124582190303118144c00450140d1511006115418007001800d5031080022101381c0103400c02007280140e01d03407944a010510000b00e04503000810110b80500e02c0c030881c03010107544654040400d281c1c80c0020054100380307039a0180c0c0d5041060200c00c009854400d44801140254000d100642e003100824000070305031030001240d10200941d010203185405803e2610720898140b40e80c414541c0044020300995440820180d074000402c4298030204002c00400c4070603008000031440c3ca1030f518082095414028401d0a00000c1c0e0004d1120b50300006040021801c0091901d80244040e80c80b444107003181c2c14041c0c240800751001a4210004150020b2408003550010091440380120000103500741c0c80100e090b42d441d00009412100b040c04000f10314940141c0000802e2100a0541d1070142c00c0108407090302d10041c480c00b11074200040400a0312000e20606e0400d2000070148001d01d410142c030030202501d80310004540681c0c440014040050400c018441c1c0c580080501d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 60770263 1250 60769013 60769057
    0xf250e030d1701120506040f020d02040603030e13020f040506030615040f0e0c090108011401020a050106080a030305010803031312140f040311010c03050d2d2003010b04030b0c 77
    0x24000030701c142d45a0040504440000606420031150f4416265000c009001152a69114149038101605060781c0c804c20442c906401aa0349204140041d80b1a0f1195141d0a4a40f4104100c0841c1020101c013000e004202d001b0302c1242100442c4c081e2081202e280c0d8490300c0304d60110b84080b4880c46810210800028041391241e10b21444c442140c03040c10180003e980e0341d080c4155940680c1c446d071808119103000601951041d04088503c510041c81250a983c1140c0c0310a03003560b0640d440512503800445400382030650500910380949251b0780110310794142400b1003c19083c1c030a6003c0c1c004101800d11040b030380c0c4a41c0131501e004e00c42c8150151180c00404041203035a0003484215500d01d00c000300300c2c4042d405a4400030b84a03426456050a010b07a1134846005030000c030301414407a1000808400861540241e0550203050640b00015402d5401c0b4450b80190941850403809850a0004002c0040c40034221410f0300e50050540f00070740c4514140d2021805110040b541c0316111680d5a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 60771513 1250 60770263 60770267
    0x10e06030f071401030504110306040b0a0c0e100807051b06060f040c0806060f0705030c030a030e0a0c18020418151a030a0507050f030a020405090f250e030d 69
    0x45016800032015141c0c41410301400a40d030310414800c80f01a0102440008540d40c020340c88150302c5400b408002c40456201000030b418a0f104880894542c1030304414400044c44a1007407001c0448582030000014075190b0020b000d1031f296185203003c10880c0070002700da082c422030a480d00c81d441d5002d482e1030000007642c0c440d20b40300e086031213900840180301c60302c0c618a4280140c0720b0310781140d00c40301580d071107280074840e0704d40c010320441440e507070104001c0000681c20402403c4000700c000c0915180c3d1400c00f00101500c9040100b2405580100b15050200700e0090440c401c03110742d4507202021007111110300c0c01034003490744800b0310703074140d004080703005c80498000c0520b0041c140701c11a83e850322001f00000d00c030721150a1030401e240a0000880f0301090342d1103590807601034140750742040b01184103238034550300840e1011045034012804100c40d04195003440d4216101d051100703c0ba03c5d090f10061420650780c3c01e0355003060090441e031290140541249004885c020b070170f0301c010000d20307000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 60772763 1250 60771513 60771539
    0x507050a03080129090f061306080109060f0b0f1c050c09190605070f150203010605070c050d030509060a170a140903070804030f1707060c17040503032d01 68
    0x19403c290a13104080802001e04a009500114143c074041d80c2808094000d0000c0c0d0090f04034403a411034420441c0003100c001c236090328001041d480d61034032460343c105205002030362895805603800070b500c840b05210405120f0160b0b007580445681a644503040c1c0390003d400900c0381d0791000d80861403c014010101111002050944001d446089110041c126400600a403902c610b900040c020b005480004203092080c003041c9014190444400d0f290312604804c0386c1c02071703000d00081917000441008005070100050020303c0c0c1100d028003030401030384001d400c030310070704250328401c4c1c1000030055006401841c1400a942c02d1039102d01d00d40c81c1c503545c0c01000b000080b070340240c81041c040001e80e80181c00811950b81c10350000c0f4040c1801d203141e46042c03150b007010700200c84e03001108041c1e51002c40044040d240c12402007501040414604d20301509101c070419461802491940401c00840d40002c200c0c1d070840106083c070406001d80a030300d424002c8008013010070f04c04807130300000b480c029003000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 60774013 1250 60772763 60772769
    0x1104090b090916120201020f0f0c0120060a0e01020c0a080a02150c040504090812130308060d0308010e0604020f0f09040b09070c0b071b050106060e220203070507050a030801 76
    0x24040400b40c552042c1c00d40c0d02e00780c1c8142c80b091040030050074041e10b5018203000e00c0003441801111820b054158030282008000c1a00d0061039220b0103900c6000c1d84c0c0f000d40505910f14410000d130301c01c9003981c107041d1140b8000b010f44000e56110301c5105c40a00702581258405408002039413041c032024940445645d110100a40051003201d60b0003101c3c0c010461000e02030070f99800c009250515100501000d0b040341c81040e501ca42c0300307015814440400c0710345103105010845062011601b5850007a10020015000700d000d040302003181c8000940100c042415144020300d0716207980c0d94940014064810a580402d81000206000712440d00c010050000c811089409012510804090210708803007101c01c9030000f050b02d1030100107c2e840020740d640101052525454460f0883d500800c1c10000c0041112641e40d6100100310066201c103484400c407808880c000340d02120340c1e0301140300e11a44190080110b0b400030214074000d0242e811140c1544d80481559512140c500b0082e0031020244 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 60775263 1250 60774013 60774019
    0x30403031406060a0507060f020c060c0306010210020c06180c0d030504091116060902010207050a0b0703110102040807030305090f041104030b010503060403091e09020c031e0705030307050703031104090b 89
    0x60100d02e8910b401000d03211007520f1544d44034103000803504c94902810b58085030340e040751f5003081044182002440f80754440d45d00c2c444036655038180b02d03000900c0c0c40b2130504041c51481c41401070820303c03480444c010b50042c0c0100341c0032500c188041005800d01d007550000f143c8c0500c1d1400814109500600648200d841c00c2c00200b00c0280c0c15a040c41003031145415840101c252008020005403480e0b1140032664010720454130803a40f03c4001c81c1e1440702da50005421080d000c07600d68100743d44a40e0400690b64505d00a600307007840c20100503940c9007580401010702002089569583d1100100361400c80c400802c107211400f584580e503a030950040c0001c2d50000c80309400800d10703040020b011409a51315a0300d00ba100c919081c0d1081590894002d48c0058440c0c3e0000014118400c3c00600b0501141c02d01441e41c0307491560b40305200c403442440e8800391a40034010103000c85c030003005071384e4040760b036040940d507844007850b044008004254880d410b010b00843c012881000c5540b16140d51031040d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 60776513 1250 60775263 60775301
    0xf0b0109050312090d0f02150316030c020601170c040501060504150e0604090507110607020601150c020d061104080a0605011d041101110a14010e1c05120403120203040303 75
    0x21028151109084400b0403c000810484620039061548a28400310f000d00c80000311510a0383c00124584c00512144400440c003000740182d03200c103880034140c0c1c00101d0501304503846020401941740c9a0501c40c0340201e8080640d40e002048050046c1c21808034010410802980c40e070001900b0b941150081005038980d0b05126401107000d154205807660000700098142031030f10b1084030103410f0003010042081205ca145800c41c89042101d5405516260082c1c1080e60608014460101209140d1010010540c99400140e240c0721042c0402681041c404904500d107000106064411544000d11a1041c0c65026042c490b0590080d4103031a00d9071900041649640808a0340e04000c3da000b070000c03640003402d81003642c000c041124980c4123610641e41040c03000d40b180f840b10051800a07011694580c1c020788111901405902190a280c906035444e510724900d0051090041c080035844240398000403405250150f039598207400207540d4255900e00e01450010060820320340304071030540603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 60777763 1250 60776513 60776519
    0x2151302042f0c0705100302070b071707030b010804080901020a050a03020a0302100207031205150d11040c21230a1406010f0c0303090f02090412080c03010509060904020109090f0b0109 81
    0x907000403641c3d41402100181802800e04d000c020104001101d02003d2540c20010240000c040d100ca9510a18040d00c42c440c0071072012041c08550107000300090205031801d025001c10780c1c0c1002a40c0d4006410001c01a03c404a12005038909140d05101615070310407000300c1c000301540090b0311380200f031090382503030b40a84202904000341d01440d41e0042c040340c020941c00b01680d07941c2e44401d9108020b00e4850042c0181000400e0030030f00c2d40c01c1d040e00c0041126110b02c001d4201800b54141550700b03490314074144030040000b000d10040f82088910710584404011858640a80240c50810b9023448060380701e0070300c02000001031181038154a0b01e1906100003031999030262034a081c83e40790300e40b10244013940c0b940d003c40041440318800c80380024507080c406c0142e12102d400900c07a622540c02c41c0d1030f41d90940000b81029100074414035841504000602a9132030300d1011540000095407030230321607196880142c80a0815400100c050342c5001d5850b40d8049182d00300320b0350303104203880b0303030043d151 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 60779013 1250 60777763 60777851
    0x307170112080a030626010501080303010317030a060306050c0702030d0207030b0a15080304030f0b01090905101d0a060b0111010e0601140a090510060801090c0215130204 75
    0x922807040c000000c005607001050301100107000d61059480c2c00641c65884041c0304070b040c070141400818012504440b035049883c00d103c0c2a015003922002181150700d0344d86da5444410111030b0740410541c01001003400101d0b103802440c0515480b8100340203510701820010703065000510140e11902c1440c0310f01c00d242e4000b06544060f1f0b07400c00d20b8020030340e803a0454400500840141d0f495080d8480c00c5c0054140c0d41030020707001445c82075506807103168107070904c1e9120800681005035146d180c0200c200000e00d00013a03059030049c0040c00071520f000c0681c03440b005100d001c019000d080c0140d000407010088240e121492940b0240c0f110242840c03c0c03600503080f0b03803509484408035800f0100501a0300d699a04400a402c0c0003000d007a003044c2c8620260742500c40a5401c01c800c207650710401c1c0f0149801404850243c500b84130b08010082c0f84010003540c80c282800c813960a07040400214a0044448030400f00440c0c0241041c0108101035848001040840008180c4021040900050702c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 60780263 1250 60779013 60779057
    0x10b18060a2705060f030f06010206010b070b13061a01030c03090302100b03071203020304060e061c0b0a12140f01060e0705030703090b0a0b0a0509010501120f060b030c0307 76
    0x2101903803031142c4020501149404500c0c0c2c0c85000c018030040ba50b0016603030341c0340e1008208200400d41083c0d10b900344a81040300c000d002419050640d01f02e00014082c10450f1019120f9a5030000c079611400d840341800800c0c0107080c1140600441e042080d001c0403072280000c00c03800d8070401e076070800020800300822070459140e894000c0058101c010074176a00700407600050f00c3c511005060316089035a5550500000d80304e85002c074007503000031808018a81d0020040401c01105443d81454810f0303400b000305056141c451048401952800d003840f082d201c4181c1038014202d00d03c4030038513603000f9042c100d07441c03c0344c082401e056102c1c5400c42c0315800410b0140004481e0315180311500c03520346d00b01c00c0e03440b5000100020101075440d01c031036022605c01404e40d4001c4480000c0002c07000c00031003d00c2880d900c0340c0c002a00603c0c00b04010072175a40d000ca0001488890f01138005403a9104c1c501103006464241d0000244040100a01112500000055001d8240d43d204c02c00e21904c02801070102c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 60781513 1250 60780263 60780277
    0x109150203070c0b0405280506010506040509012102060f0403020a0b0f16061104060305010e060d050712170a03150e0c0403060902010314010b0c160e06010302070317010b1806 77
    0x103100f107414140050207075000d076a001881582982c00e2a07503c00c00741801e046008001100302108405a001404802c0c008640508400d9821600d818144800300381a51410b01c83e07140c0c50b44103069110186222034410203085c2c4d50040010740c1e00d07064004503407856002030109a201d5044841d0024020f0b0b4041e044510301c2c8407140300f035804d14201c50a0006210381020741654400e4817103a1042c8100c5d038840041000d8420741e00c002519504040c104c4104403801848640079011811941c2c000c90800252072080700c0e400c91014492200610f0002403d0024a401c0c441d02e61001c500070200315016045540005e050012100b8403640c1c801e91002e0004d0191042590844204003d101280c1c1540050b5080d6006050102d4003400a4401c0b00131048264090740f008800170a1800b041c080a100c00c50344945014007180c0160706280c64034958280140c01503040c1640040e90404141c00762000403803804e40c07074884840d15a910071080b4600e0380290300b0310350b0068050170003004620b401c9050b2420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 60782763 1250 60781513 60781517
    0x80415030501150503090709140a050a0b03060103110f03010e030909090d08060402070c0e042004020c07052107060c1509050a2301060320030a02030d0309150509010915020307 77
    0x210f88681e002d4440794000b0380350300000c4c000d4240c0424800658054500303100940340040e5168038000200f1380840c0e2010b03040c0782c00c0700e0801c0c01d04010795400080640c1502d8002580000882c542e42c000381076482c0c2611141d426509081039684042400300141500d40300130b684c0ca2085aa808100a407a10030801001d404034107d40d004c02c406003803581c050207a5512442c40e490344030381c950542c000d0200d03084408991007070303510311944060f032641490f80882c9401550705605050030444c42a86500031409018000c0004900300707903602c900032a40c0717120b201c101c200741d901c041c2c0c81d40b1300103094801c4004161100401c26000d102d0380c070b03201d01c07404141d59000300240000420a0303440540c00d4031310100460550811006a2241ca50284500e0340218400e002031030f03048980e1802d0318225444c03201c42c2031007904500940740160310082752218144c83d580ca0b001aa4515510b05015650822440840180e1505c1d003000a044030552003e180d0364028214401c500a04518132020707440f040300c003580 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 60784013 1250 60782763 60782789
    0x1060e040201020a06020306010e06160201021b060403060209030102160f03090e071205071e1d0406060509190e0c040501030f1b030f02190504030213050402030307020607020f0d080415030501 84
    0x42105e41e40596000241407500740214280000024450b0f04000218071002d1201018542190f030100000845200b0b850f05154281602c10000f900030f0181b44009082181c000441820650b02907044684074529252042c5480c0d01e1820706046022682500310046220380170301027800c0c8103406226104601a41d41c4c0c216010b8aa1400c401a08002d0622014051aa045d290710040c4031040c00100c9042c95881090301e02098500c08481f0074161f100d140190b180050034820254414100c0d66030020541e0b110302d4140c441500c1800b81d00d2154840003001d1480b0050140c2c4244d440b00800498000f44d03028451410000720a108454110301c00c1032074104c000b070310381d02424002e410104400751400001428002c901c000351070410008083d0800103a80080c0510461621104030041e041c0444801c00451402d540445d0b42c0744100c80000e4400c490100d0710760304560750506500881c3c0302c040d2074140607540c5482d0940c000e401a01072030318805440203088a80c0ea1081c070680b130480d0810702801c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 60785263 1250 60784013 60784033
    0x17010203040c140d1425030f030c15020c01061401051305120109080c0706090e010e07050d0b060d05060102010e0a03080604090602131d0c0f070b07120908040801060e04020102 77
    0x10002c1244410450f4002680542460105100440d01541000940d0181c000107a14810020790300e8001b2000c155000b89004050011461100c04000e51a40c0350404000c82015400c0401c1c030b800826006d00d0450740006520038400740c041d00a242100c448041d203a500c06200401501c440c025031400c3c103403c0404070000c00c11440c00001200d601c1102c500006107800380c41e02c1d00400c550051018403280c1d03100020410029a00002c0e000c000c20f88402044070a5040c07801d001c0c2282c01c0a0025010018003148007a01c500180e80108680705000340103951710303c408007404c00a4003046460700c2c05546811001c4949001c0410080046645996507101030ba50f1942048010030f043c0c041616816424000b442c0102d03500442900505610500140001c050741c110111240004000c40b081cbd44081c420101000c2050041c0c506299001e08207091664503020b01b04d0314602d41042c110301047c2001c0018041c02171580c000c02c162103681c4000c3c481c86803034420740e846140301540c009005911034443c0d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 60786513 1250 60785263 60785279
    0x70f12030804171204150203010b160204020405041407091e051c020a0602030c01050108070e0c071506320f010503041407030b24010f0509060f030a02030117010203040c 74
    0x45a840341c07040004510a07240c098002600342c001401e0f950404c54042c00748003e2000c03100d109503010620550951466060030001b02e500c0c041d0a160b00080344624035440d04660b10fa405503006028060810841c0c0100d0750550001d4110540d600380104861540204079105500002c80e040040f54504210182c6130034240303c1012805043c0307028800ca40b503084001070769040100e00080c80b042d0700071900da11301a1141421904107074001075240d488103104000d09501d000c0f0700d5a21001c0d0502e500d031a90502d0400a520102000000380d03118a45000400d0300301d004485100c1140c2c4404480d8920228030000c004800b80c9050f040c0c0d4020096440d1480642c482e1000356446071013042c6250152542219040c43c100320340d04100d4024408074100509200241d0400d08070400c07441e004500903240c800041c048070b80a81c481000c0000001d842000340d11044100e07041d820b40c5440082da40d01d4a00c9102000750800c0c060303400005a100120b02c03a5010500074bc034000e81d04042000c40c030624003900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 60787763 1250 60786513 60786527
    0x20106060f051804050106051e13050d02041b0305150a0b0f03180a0609060507031802040509072102040b0102060106080c030421030507020c010c0314130b0703050903070f1203 77
    0x52000365900f0046120700ba126406003c2c002d04c060b88450382c0b01c2980c100d2070034106400703403203120014205114001e05811201c40c600d00f180d40a4480b040c406806002140240c40d01c8400244c2089400c40b0199100354035600091145481441c0c1101401e1010108444800790380700e400745001c01805404400c1d41d5000c000e5820041c000c2d003404121001a001c54242040405e0594401da80c03070940c881400300a000c7d1942c030143c9890200511401e4030000704c8164000301700070380a01e0f5250000350441008001c410b014203280c20070422450340a2908072151501d0002c01c07402031342031211500d02035000140c0c603810b843c0b00c0d44034040b044c1c0c2c030034a0625151300020030030755100c03030402a42ca9800c03040c110f5441c0094000d0394041198900030314040d241c01346016549041203501008000071a902c00305030301e014902480386642d501c801c010b0031400248190042e048400001560004044d000001400511820740c291111130b0394401132104200507604c01c00e0102c041c141104800240f003005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 60789013 1250 60787763 60787777
    0xf060203070305031b090a030b070305010b0a020d030c02031312060617190201030209041d0c01091404050a1506110d1404060f0201061e090b09040201090e0c19030605090601020106060f05 82
    0x40302901b4444068006620040c02307500665803d000c20051121035681401580c2c00b41921080241c9040040c8400039503410101c03109208042c1c4e15000707220781c20b100340110746005e003d01e02c0c00210980c4030401c0031441000e04000303d41f85440c0071400125100c50590302b1045040480207030a10003070401000c0651200d040c012810907a003088903060310b40c1c583c42030800c0e41180080b0000780480301222030f480d06203000e000f50305018100c50200500348000c45845030b6414242d5021540b07072a41410b060140c680c401c0540c24005000c00b0100b02030380d2100110311071030790003021a0400304002c07806942d1414400940c120315071082009022060042c01280710b40c3c0400e10001507074135552400790544601c1d5500440c00c02d00c4400040041c6410f501071440490402c560344410b03414a5070001c0c02c11400c5204071043c1e40c1c0d4980020314603c142c2d0b410703982d804881070010303008407988050050081035240200340c03042040c200813034410b510510036031043d15815101c4100c3c80b900b111080e41c640e04042 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 60790263 1250 60789013 60789061
    0x1203040f0603020403020f030105100603110412030c0506010e090601030b19060803090114040e0114030a12020a060c050901090b1e04120227010608130209100f06020307030503 77
    0x80051440038000e082001848580d03030040e19a07046104100c441d00100c07141d6031003a0f06013800c1c04031103030b50201220200c510341e050024a004480007040114012580f203200015074080808050580091b4011300580c802c0c41035964036a21404200f0700b01200395400d0503254082001440000c45d4800320507004111026010f4003031498201c400c0a840b002c1d0000d003100e030000b0801001741c1d40c0220302461400c82c1e02c10010301f407905103c60040303183d03030520034a4200c101002c6520440d4406110015980c1e40089a8114407481110003a5503012074901c110f41d800d1a01004102032440791040d12046032050b5501202a890444007189542140300014017101800c410070541c050348400400060070000440c0f000c030502d41c01084410010f444e80e09013490803000d6183c03001c284a907005415101310b4240b0f1482612008494010800001b034001d400440c0309080c00489940c0f096100101c80b42e440d811f414407501c0d150100d0701e078080c0d0140100841d006001040d001110f0600004c40e64040d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 60791370 1107 60790263 60790267
    0x8010b0607110a1e031a0613050612031605010509071d091e030903010f0e0703020918120301080f0307081215040203010611011a010903021203 63
    0x89607801000303420340300300d038001c1940c461001a02901441d8024139081c2c0c004060300e82c41c1d5069000c00d40e43c0f00c0c10201c201541800d15181c442c403403e00030b045d8503401e06600d14010082c110207084203038171411503600c2658466040016254168040e8080100c00c100c6040250869034003414141c0c0c103421015087c0000113480a03400c2610807241030f10899541c0311581c031402c01204040e44032183c2c20021145521030030010244c20070240842c000c0120500840c0f058003203409040c0307085e0698111078810005440c0282003d503201a102c0105c0131860b055030391a0341031811034100b10a4a0740080018440300b0320401001c1c14541150004519140c160384501810340100d80261141042d9500040c202c111403c00c094226040500b09645a58407540040e0040e200030031854100d40c038140035048021596409003803040e8040c0c40320200c003819038003402051184a5031200d090300c01 = true := by decide +kernel

theorem cover : BRFrame.Cov 60611513 60791370 := by
  have h0 := BRFrame.cov_init 60611513
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60611513 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 60611513 ≤ n) (h2 : n < 60791370) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
