-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1420
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:53:51.321801+00:00
-- url     : https://prove2.me/submissions/f2bbaeb8-853f-4d3c-bf25-eeebe5ddba6b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 255215827 ≤ n < 255395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 255217077 1250 255215827 255215881
    0x402030402041e05070912050c1005090a0803070c0f03030909150906032301020c030417030408060106080f0c040315021318020403031416140709020f03061f0206 71
    0x1444109004003d40c0c0d1240701d20610b580f030b403c1c85034840d40321102c100203080300d104016040c100707030310341c181c48001c12210a40320f080003040c2c030007115000301d003511000e1a000744003443d01c540d42c0344556180d501800c02100e14150302d02c030100d4240768401548090301d4050755203403070445c10f050400c001410030609080701d0781c40342034001980c4a01405403c005d54429607080c0300384840f90308000d41c8030141c000c5070100c0d640180441440c1d2071001042e10102c80030420300c040d80e0b08140a8241c11032003107400c4031105010340c100220303074150482c00160052007401030403034480c1d0782d0343c1d04e01280e800f403400014420600d610440c120071545401800310502c0d0340c0541710286a6074107070085180c070140b81003101180c0224003041415040b0801c44500d0300019281440c01d15031501d030200a0040e07080003403000c002d24003003003501041007180201070010501d0855a0311450070318410160401c4404a214100c4a20b5660580b200415080e1b020480ca8008000c544c0742d0344a4003241e00d4041e501508051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 255218327 1250 255217077 255217091
    0x9040c0f0803120c040b0a1d0406090911040c081504020c0d0306290403030e040e010504031d040510030204091703010f050f270a0908120103052503030e0a03151505150702040203040204 81
    0x256843c4954002411a900d0000b8080254030340000040d0b80001d00c60301c224607203192034950326046850c090f8810801c011555945101d0720000b4000d02070031049550700e2055070382c02c540c1071f501503210005075031115a140d140980c9424024071040254501c9034007101b414030003040000e002d246503003d0014010008110303803042c000300310308440c1e045034280c0018401101d0503020030071a08225003022001c2d07078103102604e002d58003580401564480240295030762101c40051101a0025460a86881494075a40e50303440c88066082c103100e0003807511070103142240c1c3c0314502e407a4949559142502c0a6494050814460381e024050000c2c50601c5040c3c641031503034005403100000301914458018000358650450910915220071102c030f0b0589406280f819441518900c11010200d0358540380141c0c041c1098400710b0003000495000502031601c05840034154629500440320000580001584181e41c51040150840d200000320019000400000f005410182c00540d403050000d00b0200d852 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 255219577 1250 255218327 255218329
    0x4050601030e100b010e0a08150403021c0801083c10020d0204091a0618010e10080f0f0c1c02160b01060f0804030e09040c0f0803120c040b0a1d 63
    0x1020300001042516520002d84c04150f81211009181810503550700309580c2c208085036513100341d409000c1340031000034000581058820017500100c071807101101240241414405041c0440078010010240a80c02142503515003010a03135800041400203144240700700c440b01032000140310b400c185940541d4048081a10807400240941c0322074100051780c83d4a00703101700d01104c1d140116814100881111400143d607282c00340c0301c40c20700350b1020520044e025001a92641034140c04950040340c00c80f002025a80c000100c14411260340f031401c1c81c607582c0c15803a0318030200c04440552440d0010b01001c4c014110380002040301941682005161142900850094403c582d50450741105804014080c0b6584004007000c1c9640600b05840e55090a94000d02070581401455002d0368151000900380f01c0c90310607843c000c1460311642205503440384520780d02ca602004900ba10484000f002c80c08486880d4100c4080f45c1d020307444030703040c21105401210b07011045e907951000b800f6194803040103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 255220827 1250 255219577 255219583
    0x14030714030c1308010501140909010204081b01030b0f01080c0703050c01020c0a0c0f03020603040b060303070f0501051509010e040803090703120e131a0603310b010b130504050601030e 81
    0x40c5a0300d0102e40d1a031041c50801401c1811a40141d5030710390500d0010046440102c40080281030200c030307001d017140d442c40c4010b40280110390104810f40b1a0030015240c407a440c4000c07441c02e420a90382845034445600c1400395100303607011114000380070b260018402e0030320302d806010320038403c2c5003d81c84c260361031480341c1c00c0e07812800703504034181c0107104001c4c2040b1844141800900c00300d684910143d1850700005e0b80b50100034000342c201d942c4400006c0c942c0c1c1e000d004070398190354000d04c00040e072411814628020074048900d01d00500c02c00380720f0401403504205a5040f40e00910341c0101035274407684c0d10a0590000f030848c21880c4910440440061040185400541c840da50703032040210702e502c100820711207140d14200c40240b0b882c51995290b104002181c4101005440e111342c0d9490b844112004500b425000014140308035100c1d8184021440e10284150b019100d50115a40c0b50b5400701450b01c1041828410350040c1c040800141c03c003604600d90241d41410006520700b41c0646030f0741 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 255222077 1250 255220827 255220831
    0x1080106080a14090c2b03050d020f07150b04110d090201020c060a0c0b10080309040c020c060d0e0d180e0903040e07030b01020d14070602030604091217090a031403071403 75
    0x49980060b00c41030707201c1c105a50300c14051286c076481c00103014a8141842d56001e04c0150103000c201000032202065590758040f501e8140449a02c00c1c0d840005040442441c098442c074400014200381c403803021460980100100f1a0589944900c1c09000d41c00140c001d08040b082203040d4052089480c1036541c0d21006414000ca01d0380b140c518540301c514042c03d0303d04000b000c40039807100045041c451313040004250348402e01d041c3c0e03001a0700c0d518001e09138900090740350b21a41c0903000003024140c1800d550403c1d0b02d04511003044404803240884142c03070601d21072a860031801ea80d806d0810102e180d65100302d4100320100c050302d2502d51104911015184111070483c00310751550b403181c1c1b5a59040220b080e0004c2c40c3d283c0010460b1100c1c1c041602d07807083d444040c080c1074010012881599640c0c1c09003180650183d44032940c51045c80c000350029a40b030610002e0783d00f0788800581d1b054000b041c0d4420185d0301d0341d6440e02070300c6030b80c0400102d60000392a110800540881c805540390418000b14 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 255223327 1250 255222077 255222091
    0x1008060a0f03080c16060c12090b0406030209120c09040f0c08100504021c020a061211130e070507080301050d050c030106140f01180528090c030609090201080106080a14 74
    0x2070354030803402d0301c02450b00304501c02d405c0341140b145200f004180c0e40402d48050045d44040c610440c40d1250340101c8100805401065422030f00080000700d0340d406d540100504a000c3da10402411920842036844607141e045031a040755203400003900003000203e000015510403000c55007040d4403004404c0c6070019030b411105515644109000c1545007417020510100c2031010803401138481ca501140d0b0007900e900c9003d0a102204c2c5c2100000d0216804c4500001017403034080e170325994800d50bc0991030366644a00000d00344c014010904851088045a4841e40c112204502c3c41c0d02c0c2c4014024030301d401400546490040e81c500f90007503a002e0140340c0040c4407402d0000c8803084420100064640b2000c2c0750f0b814030410700003400d0b0041070001ca85049460494050f1303401036aa42940300b05590151a00009a400c0940803075260b02e40d03440540d0055041e5410010a034a0b00040822213682c42e0300a800700d040b00004000d5107118001680e844004801c012500755408194428101d80a40e17202d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 255224577 1250 255223327 255223343
    0xe0313230301020702100e040905060c0406031b02150406140a0515011b020d1406040b010f050a0e04020904080f0f07110108010f0b03091e010203071205061008060a0f03 74
    0x4425901400420203408030120002c501c1c3c8a005e43c005501000d200c074124051080701210300d6402d075903d0b40400d04040d040303800c2e40d2140ca07000440c003ca541c801c0c000c520100380303496544034002c2609029443d9080142d00100600c0c0751070300a04820b200024812286161a02c120310100c405981c6150700901105078080b0350760501300401ca1710714904120b60ba04104018810182c1600c0d1600110700241e0156400ba0700030841d800d02c94040d03046460321810320321820b0140010003150301006412111402c142d00100c40e119000c016100e6028401c0c5d05600d4421000708001d131801c2d49516402a1048115502d8449200000d40194100d00380c00e031a258070101e4190280311108101d03170000802403074010b04642c10406500c0860320361f40200443c028000c000607038110801c00690140c20360700e8041149007945402441d000c0e500071640700000030101c0c802c1000701e40c0e035401141d0281c04000c02c03242450400400448800d2002010250b1203210040002890303060481034001441c028905 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 255225827 1250 255224577 255224609
    0xb22060e010906031104091a040905060a05090c1f020a17090411040e1315021b10050f0a0b0d12021510080d0c02060712020708010614060703030e0313 66
    0x9480d049290f407040e0181800d2122050741c00042004540c15a81d244200003248a5454510300f009243e10f0103550b0460f1030900c80c602440000980c1e00e1144440c0c5805000a0b17030344030340b06a200c503001c04480e0f4100d011344180207045540d14500f2140f0303600620485489110ba0348030601154008100064000800100382d2a030381418000c0c4401494400340007454149041c64010340300380000c0c101803104680048039020824081510060307485200e00541d10b82d07501c2466034000c01082c0c0380c458a64400d24465020f07161250180303a205460f000d800034215560417100401802950300c520760f021f2605022680002c9051948441c0300c01030303500400c6211800c00f02071040120180246049120100c410414080002113981c0620014a0100700c0041c00f44045003a81c020a88020059201e204410070071980c00103004045600c480c00034001e041e51071034503211003c3d00c414002d42104081242030701190081c0c002404414004040301e00e07000503200c0c3d0684000468004c2c140d15544502 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 255227077 1250 255225827 255225829
    0xf0b18010f020304231f0501060306080a02010e0405060109080615101b060b06090409110330090109030c08062d0402010c11030a0308061305060303040b22060e 70
    0x224080c0740401d021421482c50074191202800011503101d180880f420081e81e22078210001d008140418100720f07a0003482c00c0d14000c91a001d00000d01524002070b14100c400a0405c03400244aa000d68040c2c41e0001488001401e000241000401c0c1d9030502103902800101e00c2d000300100c1c2c2c03092000341c1150030444842d0301003000062000c4e00b41030401117200e200c0620780800131090608503901c06400070710034500d0030100c2c5040c055220030551091500d071050b001d0250244545080c05800c6041e280b400b034000001460181148003402c812039900c2008a024102260040c8151981410a820030541c0c03507450300b414510a03044226030350042024040c0441c641c4825209000c400504025603401304041c042004c280203101a041251083c10300302070261801c0340a0300e010001c0c05844000e002410041c0c101c1d003051301c1c020b0041c084031200203081240c510680c0e0203108020065483c04e841c0540c1e120498000e264801d2400708000c400980242d1001c035404000c000039210f048190403858 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 255228327 1250 255227077 255227081
    0x703060c050405130209010e0a090b0102070b0c1e0c0613140d120806040e0102040f0f0503060405060402060f13060e01111f09060f060617070201020703050f03040f0b1801 75
    0x30003020501405010a00059813144482021410402401603c036512100101c420148603100c41c0e030010300003180400c1c01c0c802500410702014081e0200c070041c1350b80301c544a030b4921170040c0030010f5401c03904030341c00c3d2000c22540e031815070580c0e0b800326100f16140d04006611a407000a1005041801840402507000a40740c0e10070300c800c04840d180d00700c0c1010340380d1036446070091012004004884000852959403580000001140c950003151119101c1c58000120031050003400c2c01000c004100169901c0e000520034070455007d0064001c030348542d07080c40b407660003004440c2903a80f03091001c000521103440e0f502c40101050768401180b025000c00260882040d580346441039000800070010700b80c0040302c120702d96003401000240d21410790031f000303008000100b00d00e0a030508112002454503440f100515604400502d8507047d51981d020581c00c03841284001000706d4800c0c090a11804c11540c00381d903000d030044607404592400d0740c6c1c465940e0441140c080414080c440c643c3c00041c0070034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 255229577 1250 255228327 255228341
    0x40b07140f0601092406030f060b04030510020708041d0105122e020d02030f01150503160c060618051609050d150209130c0311070b0a0b041805070306 66
    0x10000e0040403a001d0981c035240c10050065044043c0c03034400c015880405240883c03100204000d001c1c030400d44034174000307018004070070300414005d08016011400c1d600241c1102c00700da50040003000c2004440302083d01035045800c081d206442d0a0000140781089240128209440b15903c181d082d814042007140c18461300d4100c92690b40f0000c00b0a0a0480c0202c0c1004100100303940060040041e49020000e40b00c0c00d02e0890b54180007009200250040007602030603904c0f030203094441c009255000b16081c1c0030840710101c0e640710015144a105008440502c2c00901503c00403510a4561540080d020f41860030217a1140d40d0300c0030003030075107407140101850641502d01560b01c2072030100000d080c040001c2014012002009002500903841e038121211400c02410681030281036510030300040c02000340c1e4001203400d0080260b4a40c0903281110754490307121740c0704c65464650034010401002d4510142d6003003590f5060510444200d004010270701441800103140076420b41c60660143c41704 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 255230827 1250 255229577 255229613
    0x320120a14070806120a030201090b0702060403081909021203030601030501050a1526040f03080114010c0f050109020618030c04050105030d1b0b0412021605061617040b07 75
    0x41c1031100500022028041900b00ea814036281210703484010004040901d00e00000b24644100c4003c1c0f03082540642018140500408034140303d03a0b5866400ea071a96400c80d40140010030b0070700014280d0182400b80c00403001910390006280e08ac0f940400c6032899402000001039202104104903036030b160248d54007400054495204180c0742400900e2036029800c1d47e0b1b424802d581b080141041c0c80c400340400c007410301d000302c000181098200201407501802c0e00744c000800020001c03901405003481c60359500c00c1070703503404298521901c861240c2c030011442251955202c010800150780c6000c098102c042086408100d8105100105450300381c103014000d00503801c0000402455802141d50b1145021504000414031710121040224058070100102280c80802c03c0c0028440d42e0074035940103071541c2d000c44100052039aa8001c07006110300c900d580c086000c01c2044000101a03102650452288101000b0390389850ba06104a41040e00900300400c0082100020f10a0803c41070780e107448 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 255232077 1250 255230827 255230831
    0xf0f1c110715120f1103061e040c0507050d030b0d0b040206130602160501020a0512070c080307060c030b0108040c03080a03150b0c01050705030f1605250201030506030c01050403060c0320120a 84
    0xa141722810009000c0184003d104003801001d104103248030784100040c5e002c0040042100e0494000c02418a4101c0748058a032440380451034000c40303001c1d2041c10103ca500401880d1440b00c03a82d51261040c0c00100308a8200e801031110181000c542c126440c0034007042c0e0094244480300c00c1f481c194980e5541d109a04550000700760102150020070160084c80fa0701e801c0c40c1d40c808241c145191026044e074021901032000103424810b00c54280c2c828100d803107190380d00384081110600110351141080d1406030484034600c400700002a200c070f0013040c0a0300e4905000c100111034004160320500c2aa01480c000701c00000c081082003c20310843d540203d007400c000b8254208005100104280103142d80f084220801c002e08a440c050025550748030030503504482040c0075803214107a00c60310130304124003090400021802a140208002e0000141a0346003400c04c0d2441c3c032071101070f03c03c00d0386541c28913940740d1a00110340c2d1602c60101441000a0780b255032200f210400410f098401800c01a25034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 255233327 1250 255232077 255232091
    0xd1b031b140301050d0201090b0a020604031e080a0b190e06040c110d0c030201140403110c040501080c0906040e0f06150901060903080901020c0a080f0f1c110715120f 73
    0x214410141c0f41901c0c0152603070f90800807a8801607544084a0300b240645610225030035450590000303805228901c0303542c60030350400955480c401e02ca203c40c80c800c0d000ca9550000a094100d459011112815000703201207000340340c50307848600500040e0132070310101100d0410005242070600804843c202c040ca001a00f200b00c6107901502c2c0c0b0480d903000c40401004c01d00f00c4040c0341c400d411400040200c1850b0a46034103140c9000b5024141200c01600705018209207601e4500c0c082c400c5a0495101c0000740c003581c80e0010401103850001400d4a0f40555100f81c0c0c42c002c00780801210f03486a0206000302030314100907034001c160051082590348280d511500601480e45e010f01903508581e0f10030309040d01d8a403800700507420245d001b00c24681200c2080e50009481000180c180307030050200055680e0000700006150700d440c030340c1c00d8202048a43d10440001e41c1d00c9099041412030481003a00c608035140d03110021101c0032840100005168440c4201c0c0c580c1551103407050b91510140c00304619 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 255234577 1250 255233327 255233357
    0x90601030b060d0503070c0b0403030e01021204060302070f0b04080306030f0a08040e04081608180102030f0f09030f01020c010b0a05010807091401020a051f0507050705030403080d1b031b 82
    0x1c124000d1001d409407416003000003c1003c100103840309264404034400c1d00540b03800811406401621050300000c141d84035036000c0754000b0442280003003c03a135541d4030301410204260042e5028140403582d00c0058829130000c02e0700e1a0b0000d00445c85034482c00c1e40e0b414484109440d03c40307444c0c0c0741702140d001401e840c00051400c1e03040b1303001c681500120100070707030360f030304041c01c05020703d030381041405582060440411004600804085006a05080c070014400d03004aa403802800c10b41c02020300108000c2404810386000b900407442c0c010101c8010b07010544030182a60042c60203c19180e45490031400645040c00c4040042d01082c42c10554038900404000c0807019144280440c88605a000d5461a44240f01b0100c1082e080340c11501d8035070160070302c01401c607201d50044540c5890b050204800c18420f034100c50025402400442c20716080d82c03582480c0303602494000d4000d590ba080142407a0b13254080f2146461000c1d200000d10000c824000000c504810710383c0401c01890040040c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 255235827 1250 255234577 255234593
    0x7030506090a061514090606041512050912030408090402040810060503010b060306092a1c11090604060f170109020703090b19180b040e010602010c05120103060209040b0a0f0e09060103 81
    0x440008846d440225160b03400070848a10441c0c00c282c1c0b031138030785c42288190706070800d214540c10b40e0001010890390340e074504c4440c0c039081010328041c40030303404001003004541520302a09100310001d10052a29a455418600e07080b2001450301131580c44400400071868280324101801c1001e485192440c03a21100080300190006d00044201c518041040c002c1d81d0740507041c01d600a15901201d944a0a00106114407042030b5600300300f10b402d0840c0c80404102d07020954a64510150140b07040c035051030815540f00c0b801e000b00d1010071503000d80c00300c680807407444170b00d00a03c1d0004006075141d07050309004002482d160008400030000f040700c0e81e0741e606a080c0d00042c44119140c40c040c0003007042c040d41c0f403542d0700b5800a084c5800104001c92244030b5003044504840b21034008204c0c03283d00c1d881c00d4071103000d0188030b40d800c1130046d8010070104100d03400600000400910000d41c40c1c405000045a02e1001c1d0000614210440020302183c0c3c00c41d02c44079000740100f0028840740d8510380d141c0700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 255237077 1250 255235827 255235859
    0x10608070e09010b150f0706090204020c0f01061706010303120b0913060b01020706090927060e160501050d0f18051614060706021b060103050c010f0305091e07030506090a0615 77
    0x1b50350300f00040703900600085600440545038000d0096540341d4401ca0700e01d0741c8102a20340441607519140e00024040f0a416110f4018581070002e04040d03840c40d201902c075065110056651117483c0c0c4c21010741555442116407240740700d0325846030a00240c0c14050202c80300c02120302d0640d0310507401031041383c1c1c00c08202c4048447d00e80d00825a0108080c0c40f148002c0340c18058031046040d145540708115031a0400140c0700c2d111012581e954035141404d4041c8101c1c1e11510740420070401580c0c00d00706043d0000c010100341e100c004200303601180b2130240c10103440002034400350041d125100201e207002c54201300070180e90020044030b41000c0001942881001340040c0320b20f5000900400001421604892407080301d42034558569407420140d440d5509206a40d00040610101c450034a020348900350095046a000304581c803141e00603038040054402e1500c0c5c080c440c542e00000014000c01c8070798405c0d5030304406001d06078200d00c0c082e0305903401d00520b850824113458041c081c030040562006c07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 255238327 1250 255237077 255237097
    0x80409090c2c01170f010906020322030503060105070f140d0806060a05180f0a0b0d0c030903050a0e0613260c03030f0a1e0809160503120309010608070e09010b15 71
    0x2840304c0c0a0042118902101440740c0d220355404c10714080140802c560146110b0140e40c10001c0440c24440f05500542554140040101d0014000715250354480c0c005404e0b500d2290014031031000942d00c40882c9910420012119941f00009480d05560300011082e0041e03410385446042091904003c1d06501500c600b1203406400845603003819a154480030101e40e2014060584050700c0342c41070800e5901404019000a0402401c03959031480391003115500f6400d50344890800802c6075003121084082050998001b20900c54280c00c1100c902000300200344543c54503210481010884040440d400201b00b8a50030032000c100f00c0c3c2d20088200c3e041165599062503464404d540140c81100c8624054062540070085550041c0d40212070540100d191034101c0e0403800e40d280c0c8031100302c602030044d590540c000e421901420340d5103d010315004011080041591a2100b001510306000d603440440340c00c1c1d401003446041d90b001e202e040400001619030300082c6400789604074035441460340da1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 255239577 1250 255238327 255238349
    0xc0b070c171f060504060b04061e0e1909150521030a140d11040509060405010810020702030c0d060603031e020c0603060d020a030c330507080409090c2c01 68
    0x8100501c03903030010000c4c140040c000c00405440d01c2c0e940342d142e0000e000e0180407590810b480f40321107100c14250342a4420707594800c01c0c9880300c0070a0010301f1140b051010303800043c8a00200f1000c0c550f0013680908040d40c4004500d1624040c00c2101050030101c0c031940811082840d41d40e180300200880305510458204040e40d56a001c105050030701c03544480c0016140b601c40c2c0071121030301e8600100200e4208980900403515000100b00407101c00384034807042035025050441d01303114680c010300035003070000382a51100081c08002c101c5280c40e09004035031003075691360180304054001c0d00e80030103180d8900302d0401190080070041d64440554035810712803031000c00010419641d80c02003041039030b8050326401c2d07100d94903d00031420303003000e0140d07800e0643c05c480c031400c0040c0300d0449181c1c0000c2c41070301109100c102d80d0040d07036140d00100050321164010880031a0301c0a42c1e00a41041c00d101e11010310419140c04144e05910010100034002c066109000300c019814050000c0d05440301c9410f2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 255240827 1250 255239577 255239623
    0x80402010212120a063c0f08150f04050606011d03010c12050112030801050f010302070209090a11090f1f080f0601030203070603060608041e0c0b070c17 67
    0x140d10345000307811602002c01000075000c842418500c0d50307038002c1c04041028010513480e01400c41c00060900c5011000e0410084000e1070390780740c0c8045a5040c50302c0c40c1444416503d0b070110200130b0038580c010070f4182e405086522460790b030b0307541a540c3c410700b10300c1c103019a81826500c0c1c9854903806001c0314108821b4a80402c00780c0c5c00f08038850f041d0403004000701b140104085014000a20724248031000714507140000503001401c1010018013980f6640301000d036800e010800462109200e003140c1055420f0011000584841c1d002c81e02982d1128020684c070395070b07440c1c0b9580002c103400f8982e000702480030502500115000715540c001180007054441b84200a032420411501613200a450344909016910011004a03150b0306880c0240c0950351210b84510341a01945c040e441168005690000081c0100303c080c1901100050f0300716281202003eaa00d6510841e2141c2d04081010346c00000c0e060100710749100d101d4020441c0850f200b81040d05504015242c0b200712290481d107481e0156 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 255242077 1250 255240827 255240829
    0x706020d0504110a0605090a0b0d0e0708030d050c040b03160c080d06030b0108070e06010813050a03050306120c0f04090c050901060905030d0e06030a180f0602131a0a080402 76
    0x585514180c640d404025600c0c003030501c403202d9800b804105000d04c2d50301e0307000310b00f035880380703080360540304000e401014101d00d0100700c5240c0d030f0300c08403003803802d00d680d070101e96000107050203004020103000d0025034849480341044002c44001803c85623107110b040100b0000a0301d07001c1900c2d031159000c01c00712162002d110094901079000180100000300001d070705c001c0358000364404010b0305c0c02070b83c8115050f0b80f0350002c6540ca2605014462803401c0210002d0391a41c8122480d0b27611094000079a0301d07090f8203989061a101400c01c08170089400401000418104043c183c8018030f1000300030720030070003a9404120480c1800000078059030302c030b00351075040c040042d0240300184000b6150305410f60f0340d4500246114880d00590740300b4041e0038218100184506414119150b004280b1407075030304c58103c0e260041c1181442030b0b0000741e0040129000c0350030a000114031038014000981c3d6012944003841d581121908254001080034100000c0501d4990944241480a0504001710b80b6a40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 255243327 1250 255242077 255242081
    0x1030b0f04060b030123060d09021305010b0a0e030a0f021e060705010506100c11060912161802040612020306040204080303160e04090b07030f020c07120b0c03010f0306020706 77
    0x30382000d4200703080480001d000c04108004504172021409100550300d640400848003400c14801d05601c14428080b0703060f1a5411750110704907a100030032844c0400340e14448242510f07004d074002801d9080125065079441d400a40100700700200f1400340c00154042d98459150304001c0c08042e00503000e00e2002c442c0d00007003044407400001d00401039500c42003580380143c00ba100440790a8007a1404041c01010140104201c0c1340040e809180d505091286409201081c1c0020010703c2e84006410040c4003801418002e0300c02501030405020702a6080812110702e02004080b0b1851462040008014859210350821007200b078002c409a50b07a2540f0000402a000700d0b00000000d010000c01d000c40042d00c01c141a0f035107080d5486101e4200d202c00d040000b04d1307640c90300140010751000d001840d1540710741d000030a00700c00f00c680141810640c2c07030100e10308030954100e0941a400c400c0d84200341f0a08028050b4445940d036041440c641c1003034800380b40b00055120041140c1d03000b1416104200880e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 255244577 1250 255243327 255243349
    0x15060b0c060103021014030f15090106081b030702100b03030c061911090d0206211528050d0c0905040c03061a150a0908151e1501030b 59
    0x14400954480e04840031140d201c031800c1c44200e22948888407071140e8640030b20b080000111440003c24203503a03414084a1407840010283c4e207001044445103c0560340f2b00d10383c24040c192603038071b2461602d40b52080045003001901d90801cac0c50740600400039807941c000f40d2040000d04210700442c5807072041c804a49140550b0380d41450f5800780c141000010751812680000c01202c0c420140500149400311300b0f1240324010b40303170b5040307181a00300c100542030040042014050a8052040d08900c001f4505216a01682d0407200c2c40030012040d215032800c251074030440c030707a1140b840030381480019003495508090300c1298060004032084001740107076170700d240c4001e03c0c0c1d041c400c1c00540f03018a05108000c1c200d000071543c152a08130003141103100c9008851004402600c203030701210058007056104d4001403105001c2200e170b4078000c10b042805003c00f5004020700c0e59460710030304000e6500c140d0707a8280c1c041281c0704c50003801041030360000402c01c030f8401c1e4000c1c00c1c005020391031035001c90342c0340b014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 255245827 1250 255244577 255244589
    0xa09050a0b0a0b030d090602030403020d110a091a09010e070c03051201090c171603021c06080c040e0607050a050a0e04150519030c0e0c040509150a05060c03071506 72
    0x45101004000d00664000c40c140c14011010344005c105104001d60b42c0c1007041c055030340180c0c0700380418401800c01950702c06c0d896004000003001c40030f046000800c206a26080902041c4e198200303903022084100340c010103000d046401e89e00942c14102c41d461820002044101082111070510090501034070480f00ca04e842c90541c0c0d1825a150000300018000c900303030500014042d0070404400d011600c001c580202d850502c1049500e1040b20220041c1d00109016507000c01d05a003030042580480c4100401405036070b019040791a000344c104001c442d461a10400b1a40028003000398644c0d105045400500c0c1d28288641c440c120700904507a601246580c098210307280c624469514102040c1405c1180c41c22601a0340043c14802c2c1c26100800070710008002c40c030060f01c1400b42c00d84c060403a42e403009148040d642403940c0c840c001900c11030f05031841c00c4440d6a080000d111030911034001000380c542507e4007442d1103034003244d003582c2c1d114180025040d40c401e00181100381240b904820001c000e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 255247077 1250 255245827 255245843
    0x509150f071e03080a050705030601200102071a0105042d0b1002030d0e0309100323130605060303070809010309050a020907020102180a0f120f0b0a2f030a09050a 71
    0x21041000314000d140c04a0b00364086600ca0001442100050041d05d114040550350f076801c0da00c940d8015210107222001c8810400424101c14214031000d1002d801000d005140d501680d050042c2c0411407080d0603004940241c0c1400306a05141c11201103041502d09000000515080c88044a1000380105403031542d028640101a10701c6990000280c9030030b844c8443e041003c03880c0c600f940c60383d07032244040c0ea43c3c0100c080808596818025440b031051194802c4040e404220000141e140014040718000440030180b154542071150500c2050350140c0180d00540c54a1410b40f01c0741d49900890304114100b54484101504101042c065046415800380240c0040d05105902034080d40000b80071000144080000515525100e41490100c5622002500310070b07081000000c80304208090555051007550b1440b070000b840760310400d209000d0081c00183c100d1212004054089005601c5c0b0041c544401020701d00364001000ca903001440c0c4039002509000c1494000d0501b0f07116500a88044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 255248327 1250 255247077 255247103
    0x140f0d0608060601021c050f0c1606090e010609051c170324090c0a14040602030a0305010801050615030a060810050709050a030b040b060a0312090311010509150f07 72
    0x649600660306580d9850242c0d04a90f5641c03004aa80328000100d42c50f8208040021485c00b0740034000800b548c0c040f0f224100e180a20360000c06181101200b80550300d075011842c10840d035a840160440034005100d0200b540d1751405c02d0062a0320110f0082902c0f1703034680c180f0b030b281350f90702d04a0b03080340c2c0c0e039000036001040e507001c01e081040354004460b980c0002e4030b2100300c814003d2142018900606008181d0140d580b1105104070f055005483c862080c081e0b52000c150b590320f55036002c1c2004103043c0d40156501c012104004040c2d540685c00407010341c0c1400117100150784d8141e9100007406613054000d440f070f92a41400c0c005801c55912807000d174083c80210b4201214960442e602c40c040a48841445650723a00601039402e0540c40301130442c01d01c1401180004880c581c055401c11002040030000541b2611280341886903004c0c4600412008001007040010584540c141c1d05800d003002c906101800d000720306144880314154058180000740c0c102150003c2090b03480403500850300000306 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 255249577 1250 255248327 255248347
    0x140607050a0b07081e0109020f0720040f0209030a0f0201021018020405060306010303080408070204090b0a050411041109010c08040b04030f05060f10050907020c031b01080c070203070303140f 84
    0x2450b002d458401c00140c01d680083d44076000c0c1c074034100c0b04481c070000f802c07407580c130340280d480083d0813000c510000078030104900340202e1a414040d00000e18513032111408241143c0420040b80c4030310b204041198014000700e415a5001300b0404492608a0046400c1080b18030040b420100c05004903080c081c50520720020380d2001d50030aa410b144207580410070b84d12381034105a81c881017440002d00083c40140000e0016034498064208603202a0010800c80c0c980e60396100c0ca4401107500c0c0d000650364208020a00003a070922000840d0107036400c0042c042c59002803402c5116450641d414016401380002c104900441203400400141d00303880d4855460b0700e0f01c0030700ba541c074840542d40ae20504010038100021a601540941d6540140781c0c4103629000902012440040290382540512684544907840a0042407414518030010800400134100094244800542628410703102400080c00503180040c110050701d426040051b8181c244400d0031401c1d00c00c40017084402103010602c8d0102c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 255250827 1250 255249577 255249593
    0x70e0d0b010506070201091509090e0102070b07120b1507030f230f09030303040c030b07030606080a090609050d03020d0c05040b070b06130c0819180212030c011506200304140607050a 80
    0x3d850ad4090107000e8413820700c1e2624281e0003040300103000c7c400c513100441d00450050402c0818940303410740120b0440805030004401c020004080400500d0008861080580c001c002000d088c015042c407a138400070507100040e10000c4a5100d1b04841c81c00142001d06090310002d07118255001401c4030368138501351401000c5412240300855600341282d01185d8000e0190040d0815212280d41d01044c2d40c2e0f6900100e00038003443c0303000355078080d07070b90441708089a03081c0700512181025450240c0da401e040c410a004560052600c0d004011040c0020312014902408440d02c06810280041980c1c0313070300002030080004141c0d0004041e1034424120821034002900350f03c600c8880d5202806120300a924500b99582e44000d41348049140c1e424100601e0820100d01400d0030500483e03041003001c030710150864803040e0300c0090445503107030100120760303205104c80d4880c112425440b0301100c099407810ba6a0203540a0b0354040c0050800669550b2110010b4440c010341040880d60807503140c0c201000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 255252077 1250 255250827 255250829
    0x11070201030e03120601030b0409020409030314011d0606090307080609060103050d030b031c201501120308070309050c0a090c0f090b0a0e0d02031203070e0d0b010506070201091509 79
    0x4080382c1000c903880103124010041d100c4602154130101c03090360329840110010000400344c503074081e1751001e820740583c40728131800b82d5981c865140014601e01c3e0740c4034bc0a00740016071150402030f042c0242c1001c00c02c4084c518079000b400c00e641c000d03160050b00d00001e08203051500240c9035407054008002c00c60b071000560318103c0f4052420388020350b50095080382642c014203c0c0540650005901c2c4a070000c85000d000750b44401464502800040900303200700485040e419841c040e03010f451644d4025164080c854010400240d00c10401c0109550207000c20038000d00c0241415039450b48c4406001040c080440048001000c0d064800c1e00c3c7e01c200801003254101b49000550340d83d0189901d6400703582c000081d6420b8607881400d00c0d407910f00403110b8a03205051642c0080a0149410040e05c081008503c01c0d50761000294036458006da004081554070011140301d51800480c10000c07414124201c2d064500c280c410655811580c00145d6100b540d5a103c130008464800091740d183d0f0740034003210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 255253327 1250 255252077 255252079
    0xd1b0503072922050705120708060a051e040c0e040b040308060d0819020c030a0305040e2401050904090b0103051e0604080901083d0509071709030d110702 68
    0xb030000d5a1114002100c12021100ea010094000c6034021203001c0200180900c14410300498072000c1c1c4503000301da90700c040c1040004256001a00600c49591700348074190b4800c100040401042c80c145614500c0240c02d8541c5003400f0711a0707070214060181100c2c0d07420141c451403100e010746041ca071a20400707218045405500046040c000b098040c50039100d103450a9420100d81030411600c90860002418100d0f07258056120703110309580140c40a10482c2192402512101c2d102c3e4170700010740700400b600400304881101c070261460400017035034114a03c030103420b07e006601c411000c8007041c014102c011019299000103400003040000000e03412101a005007000c0c10649070054625541d04015240141005c4080c003007450f0315446041b921b64801030341500c103a000002c0d1400104400c40070800402044e02210900c03440210181182000300300681c3c0315181440c00c3c1d0341c002e00000b41c801803071440441e4003020a2460f101001520740c0c00421070700401c0000303085508107a450344900f20403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 255254577 1250 255253327 255253373
    0x31605031315140a06140307060f080c04030b04050609100903050909090a0f050105011a040302033004090905010c02030301030b0f04030507061a04110c0d1b050307 72
    0x4441151048090301d000c0c0712441d002000d03078080d642c1c8101c420000b001001c5001da50b2555900142004644054001d855a01000032140c1c100051a2181e0340400c0071039000703a003c40400c01c58140d0001c00540074000b01c2c40e00c0c202d5501d44541124142c4955400500110420800c1c0001d0001c04180640a1000340b0203d51840002140902c180c556585010700411001d00400d60303d0709045000e07175808600312081c3d600801450392016484906e040056074141c1d0340b00014040c0b4001200019148079000a81c0f41c1003c0c9960300103aa2031004500310121180410680780702030300602d40b0b01000d00c56444420f600c880e249d881003801000c0b094025502d560a2403d03002c21030740080120f0307050342e0300f14410070443d603200c800701d4800100151045080100c00c011190120b050741c03040400f000d0304000700708440307081c0f0020403090f1540040e000031104030400000f01c01c2000000c81002c018960700f0031010864642c10352550001e6050809002d81c000000c1800070000082e441c0044503101803c2c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 255255827 1250 255254577 255254611
    0x10050a0207090903050c0129061308010903170603060105061c090c170c04020c0c09071101090614060111060a09020619020102031f0b07140f0708100c030e0318010c0b010b03 76
    0x940030780362300c00c81142000780604107000c1001c4d0400b2001804446108186d20020654940189084507040a000d85c0003415031030701e124003c542c1c4280306070044001c50003000b0950521000565900c511580340c170005c200420050090615904912401a0402481075125a8802d1816514650800c02110031300070ba015415403480d140c0b082c1c03050203003910018203024900a06215103072801528940c01e2007000194038806071402d0080e0f0340700314401c40006c03c4101c80c0006c441e601101c05094903062104110710303001880c80001b0310726403001c0b046601007002d01d8517001096151052034100c900c4410b00a4050101c160150006d5014001594040300c0d002d6800c01a0125403265025441020700d0402c01d00e00030620b40050f110300d402d4224140c40c25685455045072400381c3e103502119954020400c04c2015445901c603107424a40103081c148256100010095101e100300d07906061030480d0b41070700c41c0d166441040c2c2d61805580c00700710f5107600d58582510000f50740085410300159000c64134 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 255257077 1250 255255827 255255851
    0x30e09090f0706031a09131e02100201140412170a200c0a03120605030a0b01140a032a0807090e01060b09010c0f020301110f0918010510050a0207090903050c01 70
    0x220700d001140b84c0c1c4045600e0000008208146c28001030504401ea40b48503a010011400c8011201d08007041c02d030310001c04170719074414802e28411498480f803d5900d003044102d007400a46030100d40c13242d4008158501d111076140c0c1554800450499070810155100400101040d039611621010211400f40d00390072079a090a08030522030170f1901721a40e044110f80ca00064041e4107806016041510046071198540c000710b494452507041c25200f01000100410801210841c811007590782592665a000e0654480344160315a0249810035180c00740000703500d460006d40d203840500584419203c21a80c2e0f04800e0b0050070600b910f90f089546004400520a019502124101c44041e11050b07c8020300303454602c02140240030580c1c05540700c0071142c06080e4804020603004c509842455141c3e00e20909024032500384545064116148100600086c0c2e0b0700e00010035402d00a01c0c1850b540c150b031030003c030704083c40360f0710a807002800c00002ca0304068001c0701506803c041c49000704682c88140d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 255258327 1250 255257077 255257081
    0x8030108061003030f0e27040309060824040f05100816031e0501060f0b130b07052a0a0e0105241c02070206030f0f070903020f0d030e09090f070603 65
    0x880001c010030030341716260b01d00c2d50040540441c1c04d500202104581c030071140a28402c481c0800500c01383e81029020041050741007003102c009000d452030403059a1400d070340316040c1d070442201200600c00b180c21869a1595a5801100d094249803400b0300c620b081c040361030400c9191901884015000e500640a0840078010307070141140e8004203080541c0c00c8043c0c4941405180c00e1050b61a95250301c404264500c480000700c00a002283c0810317501d820580007081001081e030402c1c0c10340302c001c12004000c80d000040e5420180b294081c0e65041ea92024815a5075540c075100c0745404c903900c56000a081418428880d0480d08182c0d040c0d1740450050522460807119500a050441010b110094040020b59010041c01640300c1c07006180134a5600090010b41044503442d01c0d032450034041080a44000030115044040742c10002040750440d400180b004030b0b207410442c014800030359140c06140c030801581c0c0c1d2201001c0c1514240e4100300641544460350044600c16610840070f001900c3c070300c07034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 255259577 1250 255258327 255258329
    0x901050415050601020a050a051f0915110c0709060617070f140f040f0311031207061509020d0b210a20090a06030c0e04150c02100207080301080610 65
    0x10071030010008010308580340080001030903980c114480c0c10201800140d0820010b14041c1c040e1000384100380651500d44041d8016540503500f85042c0b4040c400003600c400d0491800541401d00840c40c01c40413041110b00d8092500991824407480d000040e08003a1588500d043d20380b6503a9560302000c815846200001081d900000003c0e8004004416648105010305910548948281c03401500383c4004845400c290040c1a50a44030034041041082003c0341d400a051700f58044c180010b1180304069841c054a4400b8220907124041035213040c0003041c88c40d004e4150351350210b450b101080802e00007410540e080700c3c00362041c40306141c10070b0036060300c1100c105006002080c000300695210360f120403840406d03d02000c10b4119039185030341c03220401c2c1d21504c030b0020f00142e12490340c201003151143c540e1010f400e4803054418040845c202c070b0350301c00340341c039554902041d00c68014000301e1625001d0301328894040e1010502c08204090080118104c2d0703d4541191000c0d22840300300d40e0340d6591 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 255260827 1250 255259577 255259583
    0x3020c01091d0c090618090604111e0706020c0a031404080d0c0206040e0115080c1606020703021005180705030606060912012309010515010e0409230601060809010504 73
    0xc08410405102e050a501c1980b20020b0381070b407802d101e03000022490035082840c0c80000000a0348684102d42484000c5540c44801120184484802d2002181c942d200348560044102074030104d170034149520703500300d4034000d41c400307011540c0e00104c0c00c180741c8944034040214001041c480260118071054019207041d10941406420100c0c5141015500c0c05451142240c000304140f000041d04290038407800d00900c03100c203040c0000190000001c0c01c42c50014a05808200184031059007400e000710030f804202e40c402c500503a100c0c8141026840c1010002018a14908100c10852440e004030781c0c1c840f0801036034048800480d141ca0070141c44d4002111715542100c001c0c080c4512510f0900302000383d41e030550000148104004034402007420801c00003000310340c0e000b414400740e110b09101d526030162003001d401030340b064a240002c04c421019415a8403d40d00e4030074200604c40300c00e010360505a9008060b40040e1812480031340c0340c5800340300b0300001c1140354001412078901801031a1085034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 255262077 1250 255260827 255260849
    0xe16030c0815010c08030109050906070306060c080c0f010f020d0b09060f041d010603081810270e01030c05040e0a08030f130b15040b01020d0824061603020c0109 71
    0x614494220024222646154100007413100c560000c615201c00940c040d15032514041041e24100c50880e16102c40503002904242c81c00e0420041ca651190f80c508016038482100342d6503810051090340307040341c4001d131b42507207510340781c040e8502c014a5030050030050b09020082c46104114010000c03d08011902c254110704403c1a95200b0b181c03962203c1c2120310000c200d00c16143d0000f102c83d003102d040e44c108503031002002480c060b0f540034513281554140d0040305c941808100400e0b004050507050392280354605030360750b12100a60382a420f010040c1040a5481d02c0c0d640e0b4a04002c0940c810520503940100d1078504501a03404012500180c3d494000410a1454803006a07046990a00500c0b203d0403140400000001a90007907400d8001d8410442041070940600200000c84d190180c00c07a0555100c071510b1f40110742c0103030459900c1040484802d488104000003900210030f040100781c0e2000d4001840c44107156031001410b50386000b582100d80649440c40150380c0b0501c940540960f01d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 255263327 1250 255262077 255262081
    0x6010b070c090e1207030507020a0b0304030f1d10080f100b180105040f09090213020c0a06200a02070305010509071202101202030108011d010c0801051203040509010e16030c08 77
    0x81c598000c208001c01c1041190034201100e4101113480d044070b082100003076030000d540815840e01003107400280c541d08055600d5800e2596000e0420001c1d040c440c0d00b4840700c8403c0040c1500d03080700c5450b58036000b411100180000c50710007441c5080482f000c0d00c40f6440603000c564418030840c0c1c01c4040d121000c0e6841c0c074024650082c10f0800e00581591030400c08100004030b02010b5401c4184d0051107050400f052101d101d104000d40c0040f00011804180e10611052412100c0021401804c6801c9a40007c480c0007902c550301d21005e441c03280c50b01c0100d0004401a20a41c00195035040380d008034000c001540707640003000e03101c07a241d110b0300e100c4052641e0b41ea005850000f055911400c5141419442070502010a50590304240d0000341c07030742d54a0006000300c2161241c0841d04075000c0001700480341258101420401041c0107882c040e00c081d5000d450602003c00486028010040c02240303d980c0d11134183c0700b541411202e518009070841b08403180e060190040e4403004256840360300c010f03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 255264577 1250 255263327 255263339
    0xf230705120606102d111005070207120c090c0507030f260c0c0615150306060708031e042f0a0608071211070519080423030d08060306010b070c 63
    0x303c0350b8058501c020386811070506600f20007170b6a1001c0316a4440d1110140c0404000714a8240038001d500258000d04040820004541c04100f46c3c05031007078290024108546400d04e011244919001000e21030300c0c0005188605401001412005200b0780e65404846000e0504841d85514100c01c007650840d0356030310780010680600c0d600e9000c64103513400341c00c4c07000c0304001a180160948006c000c14203031800444a50410107043c0f4848900c501c5400c0c61802c0047c00300d0381502c194080074007610030201c0420324582050120f0306d01c01e80c5407403c00c0c14038107040c14034451295503180d0360428003440b24030007100c05074441a401d03a030030310050a07103011500d025401d1b100940000c00360800c100c0940300840010310b442c41642c07600c0c0309183c140ca4589003a45411898600082c0700c01d5451600e80a803840056141011070303044c4c68149002c41d15440b0525405201100b21044081c0d060090401b410991548210754030b1264100300c08a888590765a0101d880d18403a04a01420300075075440e090000b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 255265827 1250 255264577 255264587
    0x61f03020306060d09140106060318020f01020f0601060932010c0302010b06070506040c0906050607080901090b0d02030601030b0f03100504050a02040e16051005070f23070512060610 80
    0x4885406070181e443d09071101c54907001c031012801c5c2160b018205881e000c00001091060201a000c00c1c1006c2091400184000002c0d0558010007441216030b84100b140c0ca034400d010b141c4810500008881140d40c4940000e8950403e9001e00c04120365444501c2c14007840e4100d40d824001400f056401031030104400440c0c0307104500344184c09640d21590511103944030300c8004c003400c89c0a40d01a001070300742840c1201598482c0d40c00396517078a040c48400c0c41140d07907400480703400e6a4444ca01039a92444440141c4a140070340d4032801c034050700460458140f1100350015480350500b43d900b000f40007035000c100050390018074401742c0c1550009500785421040303a0b21035074010740181c04844c041c81c030a80c001000e0706c0e10000c0c2c0040740c0c0c02000d02e15041940040c2c00a010b001700319860340c07a00380500f074000c009001c0d9070400342c546280d00441c01c050200c0340c0f2900c00c4010105890744400017040c0341455a6060920815000ea00104103a00c46c0c240e01094044c00342d003000b0810801d040c4c22400032a2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 255267077 1250 255265827 255265831
    0x702011b0512041d01080610060f0e13092603010b181203070201020601060504181116050c1905090a0207080d0c02060708070513090e070306060806040209061f030203 73
    0x41c036200e11802020090902c001500080071a00760781101030750705103507a54001c801a4000d007901c2c2e100340309010701065a0094003042d0f070384915004402504540c1d04071849800d03c1d24540e00b1140540c060303a4003103200c4e00140e22541c010010209400d100c00340c2c0c41e8a052030b403c0500700d00390080c80140f003034201400003041722500c11580072403c1c00c91040017901032000c400e605d0099a100040203400c55806025450041510303003001c9051a00c1c0031800188621034441c0e030b80e102c6079250420004040c01300f050310700b46c135000319030340280d0005c0b03207070035503480f17440344003492140301100b02c03101c8051616808901902c030060108290f5031103092010b0040d4000031004c603000342c3e040c051040784035454840ca03045580c46074000c1c0b416003810b04001d803489074007400240401c1030812188500c030348180d5441f402c448909400040300c2c541020214201140d907000104003500b00040014102c0001610b42c3c0110f0003142c0748a05915a0b804201d0141000050b00c80c503d518031500c2c1c0710315402036010355 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 255268327 1250 255267077 255267083
    0x909040311010f02040e010e10060509040902270106031104050109030210021f0b040606080f041211030a020f0105090c0a030b0c070206070302060a0b030f0a02090903190818030702011b 81
    0x401c03181240c40ca071001380c0e0050782001d9002132812004101510b10100741030b410440d024507610031076081100c000c00f04d20070020303982d00590b19032600c8070454036050010440750903a4070b0300c8071401d500c5801d0f500c080507082c8240000203091582c003080c081c00100c121400c9440507107400085915580c00d0100304841000f0780313410740c012071402070030360b50f1072042c07200036203280b040002104400042040101c03101c5412800820001c181004002c900d018404c0360880e2b0070181c81074102e00600000c80e1207115050652025000110b13010060b1500090031002c40c40c200300007445690b540400d032035561411281c130306e0b600005020080000c242030101c150b070041080c40d03800d0314100640d0086801e40c1e004410440050b80601d0400002040d980301d180c0b440c51040b0050111748414100d0706555590200c8064411504d540210b00019401c00031a04071820003500003801c14150700014281503c1191252250501c034082c0c000e101502000711840f00e40d058403002d54205e02110700742200822840c0807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 255269577 1250 255268327 255268331
    0x70501120f11030c040609080109080403060e0a08180a050d050a08160203011d1006030209070f20010b03100509070e13020a080105100906031106160f03080a0e03090904031101 77
    0x140c0d038a0382c1c8440046100340c2c00e58050310b030350307502c1c2c140018480e18840c0e002e0381c4640d140500400000b0710850442d01266045007001c90320420b282c6043e804c2080c01d9400400180c1d0014a40c0d07007900242d80340580c80c3c1d4085a011001c10f5079003080c040000d14120004299070010340d6004002a490310141c45103442c003050103100403940e5404a421142d1405030703505008118100d5502180c400c0000c03070b0a8400d0646c1c01e0040c51724681c045411044054072650901642d8182c0503c014032440308280c0c0020340509042c44c560399680038600a18842686501034040c41001501140c01801503030b0058040f000140300340342c9000034200c030358800a40000300340c04080710741d400541e98601404003d0140b0740b0002a203803d242a060000b098141e0212806a0901c0030420204119810100303018130103035180c582d1000d413072400c2003000341c907900003c0c0380c4602c0710390700410f02d507010801911038241e402e0100001d07004149015a6030243c5614594000c0e603240000e00040e100700040c1100748026400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 255270827 1250 255269577 255269591
    0x2030f0426041805060d050c04020d0b150306090c0c0604030c0f15050f0a09110607020f0d06091a040b040f0302070801140915060105071716050c12070501120f 70
    0x1212005601a60021250f480310403903501c00000c0c0c500c511500048100d80300766022003640c0d03c40307803140c0c00c0c807039450301c143c2d4082140400c00319160040c0b8501d0200402519142c1b0660100e200e941d0020744445014401110008454981280481e4050307d416002407046540381c0cbd90441d4642000030080314520345020a00c030000740c030522840b0481c0103a00b000b007501d151161129035400802060b5160417070a28081002040e85081501081b001c00d40e00f683d0f0b108010b0005ca48000192924503822207582a5030800b03010465020704000d0703200d03020b01c0030700381c03002903990300c0c40e5030240d1300507003000d4904010030005582c81581c901158440d0040c0c038041c980d54403000d401c6414500249240109000c1000340403841030007010102ea50051150500b4140100020064018440c000307101030720120207030a000e62030600340c41d491407407803144024410b206e1a003207885480c44800c0fa0300841c2c007a40c80c1d0000c100c010030268280c40040c0e44140c01d0514404503a0040c2c400a0022440340b030b5110390f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 255272077 1250 255270827 255270893
    0xa020a02070312081b0a050d0f06030503070c0306060506090604060c03110115030c050301060e0f040c03020d08042112030902040612030f0906111b120d0e1302030f04 73
    0x40ba01e501001070300c80130104d1411032107006441414100f840c1103a01c081141000c420342102c2a1160f658501200203140b501e10307070003580140003980000c1d100d4400402e94404021094088909988c400c000a0000981d1036041c40118000c03400c4c4c0540c003070030510051010307a02c6044801c480a0283c40e041a00001500400342180d480c0d1613112a00d00314030000f4010b004440c00d07000c00414040e802040705038501400803e80306406808450140c00e00e4000ca420300040852074005550000d0440c0c0440c9420f1400740890b0b80305118150598400410425070f020807050303807154480d000f40880d0b0900040742002c0b001000302c618100d92040e07075105d01059009202f0030b04681c140c865219081113142c0174001410401c8640d0003402000301100002c58120000b05000031070080f00c024181c13680c0741240c000f41581c2000b00241c2c08520645a442140c0f0f40d005440d0b241c110019174000e21650300750340300001640310803036061248450700c101040004403800d6440d505000051202214102050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 255273327 1250 255272077 255272093
    0x90319020619051e0c09010e062a0a050d020c1c0302060f1b0309030918090d0e1503071e09050307031401090503030f091005060904060504080415021c0c02090a020a020703 75
    0x3d22540c22415001c2121443c82d42c002508d03030600507007113070203e05040d04d403481036190003031400c0f0300c203160f8401c000521840001003040d202407660100654074100200340000356541c41409990388584003101d140b4110030706852805400607010750160140d5603c0d80c40402c2088000b41ca0000e221040200640310201c44e0700140d406000030a01541e6601c0022041004040c0303034900f1988082520780c1417080c804000600b5080c00315090070100754544100001820300c00c484500c0c80903a8100008100d8a19070002850134444042c882111054007000783c1107454007124000c1940562100c0d0090000c0b44001510400d001c00d0b0740004140c1300b07440e684042c10754006031100040d0803030000c240080d10905103c414984d4038210740800c4249001000201e00200240014000320354030740109092005460854004e0285560b412015002d0100700a58072080303c42105685561440c1001801e0700c50046035201580040840c221034540186860096209212403000d500c81c0341000000101c0038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 255274577 1250 255273327 255273331
    0xd140307140f040314011d06010905070210020417100621050f0d0c030806030c090109050703140717012301140d150503160303051b0a0209090319020619051e 69
    0x194051452043c00d031651103080d80c0042c4a80003003d011f0307040b041c00d0800000788a5044540d42240032840d516030100076410540c0a01c0407c0e101d030700000d00441c030b01000525403400d080420044a0882602061f00800c40d0601d0141e6844a540101c40c0f14a8800740c1c4a030010140c001e070103450854407000003040c50041400c01c0c500204050321000030034182c2103040c0301c0c1c2c040c03001c8e0003801e5400c1c0303c10009201d0305414040e80065556501c0071a40362442544000d4070703805042c0e803030f0310281041d4401034403c94884850f59a410012000451580700340141e2032485003d039240e5240c84a0318400545510380d0740c000c00e4082c41400d00c400c914840c0140601034481d00c030740000c0b1101c44d04200030300d414480b4078a606085c0e4041c0100800010740e00038100c4020780c408103005001c140d10f8603c0c882c100f11800070302070b502040039014810660380200c01071040c0d001c600c0380442030030142c1c0340990316620300305d94506600c4009400c40c0410304450b01300700c0d4004d0000101c604150f001010b038012104007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 255275827 1250 255274577 255274583
    0x21507030e130b01050f070303020705010504030e030c12120306030f03191b02010206010b160206030a0f270f15021803100614060c0106050d03110d140307140f0403 72
    0x1c002014500350420b1549404420141c0105010103982c000010f44a4407032201c1d40307107200c0d0000402d0020b1622070780c103984032158810001d011074145820000c180000380c0c40418420b0107801900300b0507203003451124071581b10b6080540f0380c2034080c10b101031064100401d0a901806184003201081600344004d00c048503540f030b02c8030300e1034612070b80090400765055105c10700c4000d50860303d030150b82c00149240c116072030320761113580c1c517804080070b4040000b0300300c0f000f0b42180303011040c0406641786802c80c800c40003140310208803e40e500b8112080b1804d018910f000305c3d41c0d000e00000c011401100e6091341650080f000c0c07800b03d101880d40f20b0700302da12841030307842000c0c0c884448200900c0e082c451010309900140c2e09003c040e0500c0102030481c0c1542c45600e00c102d100055143e80001c0a4116400506005181c031424200ba82400713012460043c43d140c1e628000d040e88110014091503424590b0070b01503e449055544908090300c00600303140444440c1c80091141154003800c0300000c101440c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 255277077 1250 255275827 255275837
    0x209031608070e181504050c04020c03040302090c1204110a031709180c04062001020a0c11010503040b040b040203150c2104081c060f170f0606061602150703 69
    0x442c20500755a20b02018200d0800d41310700520208000c080041d0116902d8520140c642d816143d918100c0d282070720080045400a0010802c0321402201001400803240265283d201c90307512000165680c1c4200708020702c4004008000c03078082042d440310342d10204406000c40100e00c5d100d8940b8407907440c2284041e20008400618810142414103005882c4844101d148071107041a0307102c0d15250203580980e034200074240d1000610300309103802400302e1503072100003195107450303510004001290300b0005681d0000a0b00d812040c81d4461400c40748510b8000300082e5140e161343d550b06400c4000540240e0703141c4581c441140c0710300203c2c007040d2300035440802d03116911500300c81c1d03a0859400103a454005448808100404203842204403120a50b1080b102a6100305c418032034401050355030043d004504003640e012414410f403810024440380300c801101c01b0b858010111039520007080720200c2d0095028419903800c20506804152500d00c001d208480311491134080d030095400c40001500003803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 255278327 1250 255277077 255277079
    0x40b070804081c0801140a030c0603050612120901080606092e091214071e050111030702011d220203100e0c030408031008030703030b04050109090c09020903160807 72
    0x6003042040502200200186003010307243c0100241045005100d0201c00d4035102c4502200d96079190f40b500c02856024200c01181e030380751140200105012604a4020850810240044000050176124400031408a039241a0321040119a00e140150455403c40d0090122045581d01d2006a483c4540c008203c1c00001c8480c20352000d80c0c502200c1d100090018040e8140082d102ca5001c0405068110b0010200202c59900d0305141c411a44d000340d001e00108070703544840d200080e00f404100e42d000da0360809a407002150311500c80c81103450083c089000c3c440f040205e00c02076111450221402000d8072100d1929007803818420143c0a0078240c010b500004001c2c02c88901c404480107001034503040c0c0e62601c0c0103641d01c1c480d44006080507004060105c00036040503154200c540181401c0703401d880d1210f615107409000303040d03581007452091341480000b1901d00b905102e1040d0640c0c200085c026024a4541c0310002503004424864260007120350f44c40300c0002da040120024460040100102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 255279577 1250 255278327 255278339
    0x9080604030c150903020606090c07020d1239060b0301140414010203010602030f07021903150b030d090b07080405040e0f0106053703140d090b070b160302040b070804 73
    0x1540801005003042484c0924038030100341d000909541c8910156002101e507114816550181e000300c680080d40142c595040c0d03c02c001103840b078007002e0798658a450480c440d40703007140300d83d641c0f00083c41c806221a425580050006540c0c2920110380140340004d076000040010900b51303032800191055401420050008100341c010140d966402441c0085080d035040500094591240d860b4032090500080348440a5581d100156403800c1d6408005a0b0701554914102501600e4014001841e900d4610170061904000c41c034141003040d0343e0f07208580e503820b0400c40a0318dc0c008117400c2e41e03100000c0c0000b0030706881d944a14400c5801140c0144a070500000c6614251a140d4012038040d6403c0d0303d01e14211061200b966843c0a00b0702100100f044103e01000d20100142d4030241c0320380400004101e9081d00031407116030364151a40d4140c442620303071140701203034842c03214000c04400c03075240010031740310a003045641103100514002d0301d407940d00c80086171030390030901d415500326000140400c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 255280827 1250 255279577 255279593
    0x4080c0f030f03070b1509070305040b0a0c02070528030606080607020a03090e19050412090609030b010e060105070c090f0b04140a020c0118060605010f0503150d0309080604030c 78
    0x340100440081c0300c454030700c1d105151240102a4010114070700c1e103020508102c0c00c203e84242c11200a00100702902c2d1000b0300401400e0300362400e590309429940480d002100d140130f9001c804400707400a0859515040a005801c94048032204c1c100728082c48200b5004030032003031130000b18090078012540e2400c020704503050440141272a019580100201000a43c0001146045400d08081500c07590b554108540c1908841c3c441051a41e181004110411030200d02104011505580d101d0b60b07030f41c40d04020313682d042203400094a4000f070000100910410b000d00303032354481e2061415504101c003d5891110f1410305030001c1200c42c1e250030101c0c4000c2a10301c0f0389101050206d40c18070900702c80b00c0c0d1002c4030710400781c00d444440b900018080d0000740e00750085515440200d061400340c0590341000802440709006050010300700c0c0c5a0040071074410010380780500e848000e4500380e91141c504005101c0e8043c0300403024801074001c00101404240407440c407507400307034807103204240d111f1800004d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 255282077 1250 255280827 255280849
    0xf260708010602060114060a11030d060f2903040212030a0207090506060f0711012705040c11100504051c030c02060919020f15030115080a06030f2604080c 68
    0xb1035103c900100078618500c00c241000c0041074401c1948e6a0321105c0440380d00b00210509402c0b407100050500c0e9038451740d485001140c1c1149000d58045031106050483c1154200380a0072410100c11000030a60029008540043c802411750b101000117039031450a54201010304000350b048407500300501d500078054183c3c00070089074880d01d400d000800c200414007a120015260001c0c1074445803060740903418810f800c400d0300c0b010a0f0605810850980401114024580104d0420448806550040721120b10074202c9001600c500f40091f2044801042c000f40159450b02c24150114040c850b00d40100c032601d159545e01180034071864101a18120000e07080b400141c1c001c0c81200c3c8941c02e8501040711003603049500c90128010080000c0d00d040d103144102100e418000000146c0b6100d4074101342d103c0c0600d071185007080d650a24888221800b603c4042c101d400b024603181c0c00560041c1480c2d48482e03d10480150b000d5220350803070070039000b580003c40b40d078bc0034000d00281403600c011402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 255283327 1250 255282077 255282089
    0x2100f050f010303050705010b0301181104051b03040c0302040c050a030b030606010503072d02060105180405061501051b070f170d030915020c01020a09081b010f26070801 75
    0x8001070908122025480d841484003404110002c0782950400c002900040001440100207004541078207141400d00c880e0130313030200d4424100c10318019003820240901031007803000c0c1c0c0e03401030110302c10a002c2442d039100504c2101c00d04600c640c0400140e440e84500100c54141d50390700f5441710744100000d01114440311290307200f503021804005440c0c4c0c1c444101c0b640301c02c145c0350103c0d0303283c04c25060849885000c152605007a03210341c1442070595002960758100d400c122901800324041100f03002c2001d005170f41c00b070b04c66048403002074134444c81d404c3c1d0988041c4043c075240386001440c00814016100d4207100c0e0a06400c02c1c1c030700b008251205030301c0034080d080700340322200d03201c500040e0655940c0074400b420080c1515000024103002e1450807151400304c90344800c6d59212040c0141600030341c0004e810701c010440c450b9020450400008074100800c1d08401030807070640d1030358010b680040008410004222112051184291055100d4a21b0521028100030141813040e00500312081c140c00c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 255284577 1250 255283327 255283331
    0x712080f0609160513030807060c0e0105070f0618062a0219110f13061a04060f0827030306030c042007050307080c0a120503280209030a0302100f 64
    0x31000311030000c00c8640c0040343d80d05106944842c5603501980c08401540050129031020662006010f800c0d00040001c1e00907580c2d050001080c8001540d0501031250301801328610300041400050503a4000150000754990101c803c14441d40c0720400d035100c4241c005d01807590f891811f04446200011a815156640080d103449241e4040800040c003007000e01405440200f1490341a5856001d00e182200d24050722100020310080d15903409801d040c46007203a040e98007151003880d6800c40042c0d900b1740f0075940c0c030748a030320000396011a440000030700000c1c18960740100141c01640c0058469090742a088080c4d5180e142030801c041c142807020a00500440c1800c4800e46c80f11000110352043c1c50304000300d03a40381c0845041040c61400361070f0707000305000780000d10070381003100015899010754420300c000c1c003551540540c1201c1502040c0d44400c50710802c00801c0ca0407980c1101100105081d8100040c01c04141c980020300e0000d12400550250b04850a00d0007988440d0040d81c25001d00c00c401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 255285827 1250 255284577 255284581
    0x1b030105071205042102031801020c1003050a110c010b0405010504140f0408090a0609080f1203060607060f02030c090a0e060607020103020a02011d240114150712080f0609 75
    0x240480000b103040c502d4040e0340d28000340411002d001465140c4050154000240002c80030182d9282d0002c88440452407040e070345403d06610001c0c0b182c0d034210010742410100006110264040c1c8005402d1414040c2c9a42c0354501407030000d40604251300c03070000003042040102090208803481178100e20300a138200000e81c00342e42c07410b080c9185c1042031001050015a224107210041d80039002d055a0b04c91005100007c07480e40c0010180c0550f0304d018262032001d2001c2c0c0010b50390300c036a0b810b4190040003d100056040c50301201508900707000b844082200c01e506a0614103da2040302c01d6008150007107641c82d81410f01c40f14507401340c00c2c40032080c206420040c00245c1e45004017030000303040540000361800e5681c0b003034000346e00c00d001c1c0d00d2913030b40c0d00322002d000503485101410301c500d08801103000d40c0c0c038140c690700910390491314611100d00c43e5030740c480c003802514001304010f8400204100302590004201031010840904107a0b251325a5040c028000e1038200c00c05800c5038810710410701 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 255287077 1250 255285827 255285841
    0xb010305161404030602040803040e0a020901023c030a0206011502100906110307020a060c0302071119030b0114030d0914130e0a080702040e01110f0c070510021b030105 74
    0x100107962880a410300e15010181400c100000e0300c00c2e070300020512800030500054031000080544185c5140d08208055603031030155600490040216080c0164030107003a071480d408900c10889038000741088540e00008007044030072030b41000120804042c0e44006808180d0580c18442d07031340540319240310080321802e241c000075070f10203444441c1e000172a604d002d040704008140e44407031003400c40443d6031612450302d040c02035142c14003200259419400e204000c0c200d540319200f01d5401991044022041401d010140510b1151901312030340368030384440f0301201040c02c20a1450090486981c00b4154a02400625081c490303103841580a00100100512030301c10131460401440a081d22199110460711030078101410051100c0c09541c06941c42000078045890001c0c04641e009440034040910541540c5080350800540c051403c00300340004003c0340008070040a41c1c802d0ba4049500710790300e481c00500088044100200540d20405100781d1010104c00080c800d45000c034002c0143e0f1510075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 255288327 1250 255287077 255287101
    0x1d210705100e0309150d14010b160212070e040312060605030a0213051e150301060903031202041a09030d0906140a031806060f08010506030c01112e0b010305 69
    0x10804074009910341c00d59181040e000c0090b100c890f00c00911103826400030610101c81d50f440b2652020180b814824801079145a8049840c129401803910364a00600a119985a04006181280e00c00c11900600000c96401c2103000003810002001c2421030900d843d005d1300c0140644039003038000342401020000550800c1c1902c0e80075050301005a514840c5c03030b02c0f150191955805c120390108100380c103c1c0102603203512610030b003001940c000d50181c201103291442030109105034070004481400520010344107887c94001600350700b50240c00d04da26014404500184424040d00600d8003144030b40241c9403c010801c83c4a100b810216071060030000010038030308080c03c0031520b0010004104801d540700c1d6110000180641c80f0100d01030501d850300d00041c1200340700380200800e1402000c2449801842030381d0040300004d0050184943c1400103650070348441c69400a58020540740036041d0100070310f011013005c9800d41d007508204150841d002100c4a4204a41c101483c0c4000c00840364045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 255289577 1250 255288327 255288343
    0xc0901031103030c0105090d030e030f0d1503080c010f050601170720060c070317070c0b0c0909090105090d110a080706020f16060506011b060f1d210705 67
    0x45040d030034004007280042072440c819034000392001c2d0302c6c01301080645000480e0124900340c0699040c00050030398883c890b0f0b01d000702c0c000b030400504100105078070381005030701140314441c1565541014950b43c2d03c4882042e080808001903503512944a20007110182c0714050b4048000d0a02031440c651100c02010781080040502042c015800c3ea41c09095209a000001b0401303130008407091482d00148040c540d810450003100441d07050f00c3e4110a030301c11460743c20301c61780003a51144401c103040d49400203003580141000e240c1810810018489442d0341c0030307441c070440303404e4000302e82810a4003540b80b804180c0da088004100c80b40c41168107020300401c0b410000364000c550b003515056a130030601d0081c860043d0f410030b41103000401c0074079603099643e803040c0a40100320800c03944c1c0c2d40800540c0e034502d1b2007030080c00401c2e90074141c00c0040c00c0d6500000d0140d080c410001030320074000e0303003c01480b2841012196160b004103607062044019250510b4242c090f1406030381495480da6403a0380c2d500345 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 255290827 1250 255289577 255289583
    0x60e06040903030b030d0e0f0922021c060c11010605030c13180f05060703020a0827011802030c04112a0703030c0b060915040216020621090c090103 65
    0x5a981c0c54061520941003841e81c010010150386c40d148403171078080c5c0035120b07030b82125000703100c0c0741410300300703464411007552040c51015044060b01d21045c5001040303040c1601c04980c0803da200c24042031141840038510110f106000000300040d0111016010782c80440300d40c1c0c0c550303040400034005034802081c5030300000c00c1518000b0342181e02804800143c104011155a01d1016410410078001c1d0800740076080d6024a01b0b650030b40d21001c01c101c069110303154000000c41d4841d0049610310b18044510844042c1c10790181e02c6101f0040409420f4a0f1503040041c500c641064124055140500100c1440d0000702c408011140c0000f41c0ca190ba40600c107207881c007d054010880d45210200350b078070460b140044099880403034603407a001e00604007500c0f0642d40390403803900192142c1065a0708030b005020390700c40c80045c00414002c200182d48900c491030320807204c4458000050304e503100a8000d41c504100d00080e0b0003189000800c180e80c006062416a5101842010103501c5d0002001d0541350 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 255292077 1250 255290827 255290831
    0x203091e120f0903060a0c0f09060905010c020d060e0139030504140304030b070e091b0c0c031b041b0e0906060712180812030a020a021906020309060109060e0604 71
    0x1040100c456240c0030300c0315000e416004034130401990b59200e40c020740da58a41c1d41c44103181d8642c234520845905265000302408141802020f02c840d60081c0340f2000c116100804001280001b0340e07c000c20785506650b8032038161344402e811031030704906254074803840d507042100503600c0340c1c040070311181001e111120b0020303d55a13001040c10300882465180341e10100c003040360b540301c7d48ca2425400c0c21038111074031b900040200c005191249001b0520a024403040740310581c1c01c401050b54980654003500c410010703072281904001c100d440502400c00d107110303070742004884505c010051005070740000312448188250f45100c2c69a0503000700e190070360208280c41056a60380e503040401ca5600c03400402902ca514540b096030342c4580d20521004000c400310b03100b000d00ca03071781b40000d0ba07955000c01d001c0308000c9424000500c2d0005903a000d0200c04126104507082c5803101c01400d08282070b050410368183d6000420048650000c001d1940108418401080998a401042403048201400c2c0a210716 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 255293327 1250 255292077 255292087
    0x207030e100203120f0a060b04050609100e0a060c0c140d15020717090a050a14010c021c0510060f06050a03021806191b02090f07020f0706030203091e12 67
    0x140c42003058805541907a072080b65130f400d20080c65080c1c0c84c1c044414100c10b50420324041b50b450104e03c19141141c0003e00020308111444c010021500c1a020704030381048401a80000f0541c1c40c805100020186034136405480a110b0a0010b80c40803613401c0f000702d4124120321041591a002c0400401c0d64222480c40c501807440b120081c081c1c416504040c101b640c4450301d01068204220080c08000340c204d0700315080b142d982080c01007140841c4944046034050183c10109035010300901d8003558401048444a0400740302861209a1030020540d1141c2c490813860081140302c1c45140080c1c0018074608518a01d0035070018268030694261004042d00410f150300c00030880c4822410070540100b48a03201c610410101010a15103e0008001641c003a50350326042241da15020360750fa0081c12251880d513442c03002c2c60003010007501a404600c0360842120617040180445c5014000c40d0f41c0140c3d5a041610a0034503105041c030b41402000400715503013100b0f0800041207440e240038020351540b12 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 255294577 1250 255293327 255293359
    0x30524061c0501090c1701030b010501110a0c351914010e010b0406090204050d0b0709081002090111031204061a030a0507050a0605070b06010c0f06020c1b040207030e 73
    0x30480d00c4094400700d0515001103009442c0350000c2034001c2031680c4039182d9800240c15411403000071300c000b800704080140180300652140d200c194440034600c080301da60030300664a40c59400602d510011407550f41c000900c069071380423501d41220310314000c100e0700315000e4004800e89a2001c56000181c42c05190405c50401040d01004683d066040008110b0403180c2111030303001c0e04ca00102c6134815464243e01003902502c9200340c90035500c0181c802c078004e848556400032400320141c00b010a019100d40001344c0b1000c200708016601d112883d0240c2c44007107450000d007600c0d6030380894541d40d0308140804100c10380d101014a0307009420990104d824080200318600f0b80e4400808039030140282045441400360005103002107030000e89054840b15903880c4125864010b01030010005841c06010480541c41a041c0d45422400f03101855907641031079503200d040340d005007407005843d00511285015611f0328681c8a0180c032044e6425883d040032907500501c0e0039603281c081441001782a0808000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 255295827 1250 255294577 255294607
    0x9150b0f031f09021c0c0302041d0c0f0109080a0c150509030a020d030311120915040312020309120711030c01020609071a30090307080f1c02030a02070303052406 71
    0x940209a01917030080c58060600e0090400e25000903800781d403d211a0000c0400d40e10ba0070700101c41700c2c8014000c041c04810070030034041520074070103041191440300414010790a02c401c02885200c1e6a80f142103500e032042c0304180058081d50b50003400f005100089aa44010601c203001950441c1c46491440075850141c0042c00c10b000d1590824a0104401030110060407010f0700172440c01c4e084820181514400980000040b903009000442100346402095a1a00035540150000301596600094103016150640203a0001d4a20071074154001d4940d05052010000406080c405041c842c501210311556502c118811044000c1c4c481c20100000c0c074042041c0d03849031014403168000740c10350440913544801c68401660142c03a004011804000b030000440d0a945d44c0701407218142408408000150b800100310304006000030701c03100b90b06400610003980704500480d00140c0307400e02c13400d0007411600c0003048070f900d90340c0008040c4c1c06887c00700350560780380c00200c40300c031f64910781180c0d0124 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 255297077 1250 255295827 255295849
    0x302030423072102040608010603121103041a0a0e0103290402040b13080706050306010207030b07020a050d020f0c04050c300438150409150b0f031f0902 67
    0x405000384180d80081080401100f245082c0220b6060120070f454805140c01c896a501c00184041c540340f4100010900a001502d8980c68071804d03203003010343d01d02c44964160900071208082d003100242c0b064402d030300b000100003105001e28007000300780403c0d442404d0f10380c111100514203e0407900c1d0342c80a6940c17034040f900641000135000b5110245134101109056090141013a140920000803440382d2142080e41c0c4a110148d0040641c1d61541d22203009a640260503001140a169134603408524100144002e1041d194020074981d80c03909102803d02007070910080c41a410a03013401400c805040998030404102039140301081071003a000204c0da0044807500e407051461034100002c0c404c030030f2950303081010440303a100340c5148104030703401050480000200c4810b06080c00f02c2d89006482d4140103070020040c000051044064035900c00c0c402994201400c60342d00d81742c101c10340703003000c0703425490b422000e40003403101c2c000702180201d40e143c800c0010341f205951014503000790f40d258078100f1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 255298327 1250 255297077 255297089
    0xc200307061404050708151603060e0f091618020310050d0503090906041e0b0609031f060b0a02070608150d050109020118050f0607170307020609010c030203042307 72
    0x64450514142c09080c9811541a1854003a2090020b4510030114000c1c000c20254080c41c1402c2c0d4403d26000c0024450420b88400c2503501d2601003641100b60b062240140146900d0704407628203200075074a400c0303441500d000d09540b40385082140c810000450f00c419260100056169600c4100c0d03008481000ea004650084140340402c080c004040001c018001c025142c640d207965072241408150f0344a0b007160040154802181481c589a683c130900d80090020402c0c4d15110000c40003a16041c00360880301d0303441700c1083c4200d45603500ea00c10200105031000c901e60a06110040103910380801c1c0c03068005001d0040d001070710441a500e4032800d0007800401450401d90941072503402040035a000700c1c01300d001401c081c1d105500107000d06048400040ca02c000c940601c4051007515080410101c0d4a0041084800c40c85081d12000c1e5211391f10030741c0184a2444d003c0080b50a54224014810525204000b40300100700881ca50340b01680704480b0291302071628079007961808600d54411 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 255299577 1250 255298327 255298331
    0x100f1107030f03050912070f0f08130518100303080703020405040908120f06150f070b040b0601140f030c0f1e04050a0915030308040c030f0305091002010c20030706 72
    0x3010140c20a516441064140d039041006030f5806554640c2da44800740a500841c809020072000034241081061043d840340c002480d05c415540c0c1c610540e42c0001e00d5600c80c1c10078244040c0701d0750810041c8801500b1401d91a80500d00f089a2944000411804040c040001a0b4005800d10313000b0b0301117030b00802020f44104007030402414280c038070303421401ba1282000041008109260f80004c94617010300300052208924000501d0381d40b0040e4030221f0307080d8020009100403808144491112441203010f40c2d880906403070035000041081000c0090000240b00034000351030b8101c001e60903240d0100c81c0701021035481d400c5400b2010315000d4095070700e81c1303020140c10094140b52010058130445106a03080c2401c2d54452880300e05030342c021443c1c503004c9072001400f000440e1145000381d4106018940e62107446450751640d4008141c2c0000c01d60105074001904401c40c24210103000c00d004a40c402000201050304008201c07440748114541c1030721580458104500040c012109015442101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 255300827 1250 255299577 255299587
    0x605131203020304030e0904030e090a0b1914030604030e1903060923070308030415150b04081501080d080703111b070501020f0709090c0e090c1003060503100f11 71
    0x8000d010f5030044500701c00080c1089100380450070b000da03d590203203a05032212540d1820f05028099540001410015040c0e10360b00222440c1c0c0b26512080312100c000001841070608045c1c55443d4420003101c900c0c000e5100b00c04010220740e0255025076140d004541081101c2c0c59000c02c000c024005400140c42103143c500c0080802180c0400c1c0c0541119880e45e03600c54003000c0c006251200c645102c0609901820000103002943c130700c01e4480786030981580040d4407821a0541071144070550400d202c000c0e4005010f000c084000c02550244c9044040304180e02d42c1451405621603800d400e28405010003040400e060074080e400c848107043d191201c650300d500c4c4801140303c05550758840c039880c90041c01800300701944080303818107007017051800030040c0b2454001800d006054103141600c0e24112524007040b40d0004208484c0220501002400440316803400c11a1070000305803048245032625030b0403c030701d841c0851940d1408810306400100c00440300f02042c0540402c0c0d5240b82d145600140c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 255302077 1250 255300827 255300863
    0x30d09090513021c0201020f03030c1b0106120b011e05060703050c15100f3f020a060e04050a1e090f050604030203040f0b04080712020102010e0601091b09030b04060513 74
    0x3c4c038410028000da088411142c4408a2140c50b4030040e2907a85011000b08850342d10304030030380100f0359806107400000a800365100c42030031508460042c100c50401020004001c151040a00d07150300742d4038010001040ca00c1d2500040b03491103407003002804d000c00030600542c0004c0c127000000c00201300001540892404c82c03841031b1041e03494003030320103c2c0341203580128400c054a40c002544400981c060301c104640c02e800c0750384d980794025010603903241d4158814016203c1c1009840100900e07200d1001d15251581000305a1307030000d11000030743d031400c0ea120b0b402030305007000707250007580c0c0020006883c0c955080c0008101c8141c0409041b5104010900003055400001042168156414002115200d510b40502480341d4440c0482e542d110300710910403540c044c95200710980c03050000042c0c00680120ba2070902000341c1c4401900c4e55181d9004040031112014401c21038100d241c4128403500316a260b40310404046d0010b07006a40d10400280c0c0410042140c4102c247c1080701450690760400d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 255303327 1250 255302077 255302119
    0x30e120f010c020303090a0609140d03050f070e030d0e010504050a0b180d03020c012f0d02070b27040e0609030a0912080304030f02070b070501060f05030d0909051302 73
    0x600305048540c42c00007411119440402580e00400403d0040c0801c460181c5841010300342c445000d40380005096144002c0800070840340070f25070030a44001c42c4514181d810103089007030060040043c4280340e03807050030b959800b043c3d00094140a09115000720108401200d00b402030b40c00464110704a4000071a450110801811800c88034019018809050205010810341d0b04440240541d216600b08103640d802121204c50302d411803d81c0ea4a943c0d4a40e501c141d40300c0103001d01d05110381010151005c00c0741c2c141f003140c016001e04d40b911443c214840d0032459140c5041c1a1102154002180040c1c4c1903646030000c112040c9070604441603414490b219503103075402440c0030008200740310000035400c1050864418010b803c003c205007141d5540c2c4003070b65640542a050700860180200104d0178005600150541c0c81c001c9000041301070920400b42c040a49a4101905c40d40c09a8907030040b00360b10400c00001e8480b4a00c02007010b455012000d000d001c10504003d500c28003001c0601061100c103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 255304577 1250 255303327 255303343
    0x40603090c05040e030d05070512010e0601020f1605010302031003050102070c3609020409020909030a120b090c1806030c03041a040308061221070b0906010819030e12 73
    0x18101032000d00d5a50b40802040b9101c0040c1e541e616001840044007034480c680c01194403800b5401c03c0c0b840e040149205440c1d245c02604402e041c1c40c1c8050074003500756030408c0711903c82c4003401c00402140c66000c1100025541c0c600c500f40c109500040010f810b02d8808122000850b800320003951a00300700c1c03a205885414901501144c0303200700200030501c407694815581304000e0342202d01101100000514040c3c58203c0c000d0740c0058607200408011b03101c000340240701e02c0c0904061510303802980c400900f459004081d001c1e029007010000d1030550703986078000307420081d10340b002ca0791503030490301d0b11074421400c0c00046d0b4042ca021040024503c0d50000451066202c0c0460041b02c00c0440e05088440350262000b03400078012400143d400e00b001e122908244007404d044488c1c030714400c0c210400a0404010410802c440801d48804000c185c2e45000d802c031500300041c0c4055810502d0181d6502c10307241c04644c2e45c40c003240c8080309040c054815106c13290006081c100ca417008070380d2600e55402c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 255305827 1250 255304577 255304583
    0x911040f0203070f0c0f060902120708070602100504120806031c050307030b031902150717130f030b04060c050d02160b060d0201050f0306011407030201050601021603031707090b04060309 82
    0x84c00d04902030244608058000c0c10303404000c107024100e158548030020230016104980281c12400c071418807480070090300d13000384500801080c600342001e10003428069a5061415110300304802d210008200700011090501a880d00c0c660301d070303610000a450b014178400709420120a42c0d2000ca0170341c0e0700900551003100c1d5620180205000035003419912000c2c030070701c04d070364107140c090b04801032500004000e0840c0381e0b625900c0c20319540f604c03420285501d204260755071031000115100d44824070b0300004002c2c041d0042c002955891500d07111955400100020452952040044e141d14003d90540704d0394080c20034115140c007407683c00280c0d91524110166a80104400025107900d000f5100400f403aa040c0c1d11035051600700140314001e0742024007841d0600285a00e4600740b1b0401d680131300704150003a4001314490500c400007900702494001648451003420070700b40042600b00021404080c07480d0300c00741c665541e0030f07412280d0241070f80062040c2940010005000760703054116180e2a80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 255307077 1250 255305827 255305837
    0x209060d062115050702030d06230f01080406020a18060c03110d0207090902041b080133050306010905150403060501050f031e03091f02010f09080301090911040f020307 74
    0xc0c01412609042c40c031940028034041240d00c2903100740d5a43d0304080d41040300c50045904004c4807503540000e59810b0740014030142841c81101d80740c1640c0c0500c1c4001e10506441000c0d000505200003000c9180040020705081e40001d1803640d080c0c03152040c000c0f0f040030718400702900fa0701ca0000a200034400321007500000e200f030384e51a0f08944081045d800e0b0721201d80080030001e01d000310040180203200d90503a400760380e50100c11006094235481d40891840d65480028560420108034880c00f00c041c072102241c2e40011180b807005003280e01c030b0685401b01e4185140c5a5890300012070300d1a4841e003165801c1824000c441081c52051409001600d2190764113104c0c0342e0304c6030103000c65103036505000d940c1607004110359280c4d4a803000f440c100d2403100101381ca107404015800f086020381500015804400d40c03181162000764203100f81380381b07880c0da2182440920b8403619444840e00041c040d800001d5602d00700401080303450030304000240d02c0503200341b18002840076200b0082d0000c441c0304010803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 255308327 1250 255307077 255307109
    0x30609050f06100e2707020706020d090302060d09021302030603070602060c0d05100b031e0f04020f06030601051b07030b0603150412030f021c150f17010209060d06 72
    0x115400c01054824032014100e01e08121034200111940080b09180b560001c0d00208607020100b060403481d07411440020445e40c00c1d0414682c000d190001a074840402c6402000401e035580381c1c06404c070412250101c4017207448221003852080248400100290301c0550b485010140d0586a009544a20300171400e80e8000d55448030140c0e02d9400444003405c2c221420020801104095480150803090051254010300d443c0d130404201c6038003c0ea03c0c22603161100b811401d4080e50a45820381c450500c2c4280b2801d07040c15400318060405020303607144505008400141203034817400503601189080d800b031134540754012451503100d01e0a030005031200068a80011b0850400080d440103240d004240b03103410b0394840c1c650044240e0007103031301800c00d501e5058a10000070346d8000f80c0745500b88651815800c1c10721041e00c5088445400c42105405110001041940707203150ba01d1048660000025614954402540d4024410300444a5002c1d101007a00010303c546980010700782ca810800840640b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 255309577 1250 255308327 255308341
    0x3030c07090b0a050612090a0f150606170420130f0c0804150207050106030822060e0f040e031210170a0b1f0305030301140301050a06030206070b070e03060703060905 73
    0x4118013800b90401000c0219680300030300d15030a558008450400d40d208522241e03100f211141840780d00b50fa800c5040040c00080902500c00c110040009040c141d50585043c0c040e0200c00900920182c61014805100003140703026440ca486000c0c0d0052000e80050240780e00c0710004c01411003801c0070645000c1c010305803140155a002d006070f800800010703070302c4d001a443c500a5882440c048546540301c0703a0020001306a0030140c00c42d85840c1d081d00301000580070030600541c11a62040040046400c1c1c403139031948071804810703046103083c2c9000c542a41e441c40154914410950116040400c21081040f0b00c802e5076500c170180d0301c044100e55800d21034000b0641c0d0300c240340c650281c1000740700c1c0082120900041c210742d080c4030038010400032040d52902c4480c02d541099000d2241072012000105840c5000e116031640418161410048207007950041543c07402110f04c01420841001d0115070344902a61106c07081c00c00c020105d800b02e280400008010705420310400d00000d0500d00400d882d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 255310827 1250 255309577 255309589
    0x2010204080f1204171914010b1e040917032805010f09021602090a051803270a12060903080105010305240f0d0506010f080a050c130b03030c07090b 65
    0x3103070100e420140c0c1480d01700b0842d43c0d00c03101503605115a81c800d41d5051904180b00014108005000d04148001400000c11203420360341c03840a614070821744580c180300c41030012034504140b40c40c00d440001e0b804250b450100b8130142e11070401b46418138040b041103101c2003418180c103032218030010400a80a80300164600742c500030300075080e041c0418003042c80265070b50360207469030705042d042c80f40c0daa0580b1b801040030014281c6001c12200c0c0c8070010002e0f10b1150f60120800980031100640c900341e603100c01403d20078100459190850142c902101e095500c0d10a10f002800c45507502c1c0845044a140010081c03010b10001c40c04641c143c5d00009040d07000303200711482580524981145080848603000c88201000d44c00c0740d0140180314145071948403480403081451007a00103205c10b50600e00e00200c1408281d01480c1c240d070060280c0d20009001043c40c0c1605481525a49005414840c03010003030908e502c031241e094840880e40c560b1a07840040d411003110300044007000708505100501603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 255312077 1250 255310827 255310843
    0x80d051201030201030b01031b110f0f190c080f0d0201050105010e180406060b040e190504020a1703040b0a020312010501020c0f01051303050601150f03200901020a050303010602010204080f 83
    0x240440030500100055400b03508402c3c1684030502d000141c81d03c000b100c1c1d5814000000340000010001c40b6405118201080202c2105100c0b20040819445040e0203076601d400d80c0380e484108a400036618001c10107950038490142042800751103a415103800515522a0310204003001982414000940d55004560b02d645101c40035220000d00901d00002c01d907522000792003203404950b143c00c009004842d0002610191550318811099070a010828115050b02c410190300d000740b4203018000160388180f581c60850716080c60300c001c1c9054010010b81140910745c0005001d0328001002c40c1b1950b0301100401c2030000000051140307980390001241d4503c3c019032002c0c0c0280c000d088142d0300c1d41c05280034054103a004402c01d00380c940c681e81c8890400000303900c1184040e1920030450503458000d107011b4140742e11403070708000c200e0f6a290b03207801c500764203540c1d02e41d40c40e800a40780f009a40700780500720f0b006407c54100c13503a07941d403450001d000b9406481100128020140360001079140424506 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 255313327 1250 255312077 255312097
    0x2726030a052d0721060806010b030f0610090302100c21051806070f060c140309030406050702040b040c02071502030c25090c0801030b280b040e010e030301080d05 71
    0x25002e8500000c0607081400250240062140900803000d42d60030065405400c00590900030807114900300c4144d20700103042e0481d041ca02011310802c07000281c41d60240740d00000c210f52001e020503624100f80d820403c55000a900054540c0c0d00700011a0003c0002d070005214420841e240050300380091840ba4000d1200000160108040ea001407115040b6001c4000020074040c9404c849590305040007070250b00490380705440d01c20041809411a40803c007000c40d41550340d1840c40d00d59410350b181d1003580070b02e000f40480850940f007036440c2e036400400423142c054000c001d000c88090020b961246580b10700504030700000c04101e507507440802034a82e0081810018088003411784090291060171179505c41d441d504ca0708001030744084500822603038004a80340d41070340e94103500700621020b00c0102601071103080040700c0c0f841981c803420103900c0e2404004000444640d00400a0040c0c1000054404c0640c2050207107118000301100440c122211402240e008001010301641d0902440301c600c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 255314577 1250 255313327 255313381
    0x90106050c061603110c01050714040b091003020409180b06040b0f040b0609221a010c12050c0f0106080c03010e0a1103010603120519032726030a05 65
    0x4202d42d00700c3c10300e442c00c03030604a05010914050b4801550001c0e0080d0590f600c41c0c2c1c0d122400d10207055001402c0c0c010320562005001d1815007003a5035540d49200c2d0003007142c0501c48418016545a01c01c0d4140c5001d00140345d0142702100c109407280700031404040040c3c407e44100004103000385030a100c3c0c40c0ca112000340600ba002c4000074108402804d0844006800c140704125078405644d40344040e1104000c8400750b8180b001854140300101c42202c94008040119420702494580c1c110310061070312a80198041c41c07070009402d0848050040041940007480748091004500034190018400d4440d9102103510b102c180b40e081500743c43c51030304840c40c41e80142e40c0f040081110150903401104020340003181050342c90b641c4038414000000c3c4000020b101050381003050311000140d4009c48072070300d0b00b8400c52004e262254500380055140c1c0018aa291a1040c100305120a2124000c00900351229400c510340900c0c11040d07004039219481c1d80e01d0304000440d02d4130110120120f9a60441d03c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 255315827 1250 255314577 255314581
    0xc08011518090203060c070c06260702120a0905240712020a1505060306091b060a090911070213090b180a020d0309060212030603031911010515090106050c06 69
    0x810780016486404404460b500d030255080542c8003005200e00031300d010004141c0e00d802e9030520f100f4079080d54101004100702c4008070010740072400400144000c00d401065299115404168984030540c1c2c003e41461002003274180c001508200d9032021150103443e400000702e041d80d03602044018034103441c602000240000310200d0505e894900071628240100c941c22411912034031028841c06050441007501c1d203041203020b050501c1005c0d00320410100920304458910b08010540880889030b5019000110b080c07480d040c030a540600061041c1e510070403010340c0c030001c0a101e0394011907003a4028031180314900070410b158440c02d501c09410460001e1a0784800d034091500040c07040251416200f41c214020244e541c0f4400440228403075150140d00340e243c188043c2c140001810084031101044c4104549503c000c82120b090340030000f00c0003d48122282c042d0b0f80c0607020803080650b5032a0404010007080e44c84001d0030380c034104542d0001d02e60f0382e801342121030384a01d1521100b0b6422400c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 255317077 1250 255315827 255315839
    0x4090203041502040807140306190b13090b060423010312050f0a020f1c0903110118060f030b0406030f0f0c0510030f05060d080a050d02160503070c080115 68
    0x2014542151103040d0120b2051254514141682c0098000c2441d42d00650310421480d10314228207009440290064841441d00001ca001e0a055490b8000b030500e407507001c2c01c000e96035102c1c00d450010a41480c1000b4181c01030500b5203262400b120030b1401a8076107040f80b21580341c00117001c03802c40303041041410325a00b155580030b036400c1e0328203c0700240302080c0004803140d000c8002401403030710316600400391b0003440780c0c001d440d080c1000480035034007803090344121510398020129402d9076000210744514001758401201e401a0400c7c00b43c4405004035004500164440000e55080380c0964060081003140010401241c034248030081983c2c8249140200040c1c0b00745c001c030011405441d401e40425a01e03004912802580c180c03950010b69600e4046880240910450b504160144c6039010350f5040b03039076039404501c91503c0b148144803011841816414035601201c0c82e841c90700e0310a804601c010b10b0040d070740e03800c194011603006480c031001051900051040b80c243d26014402c0c545070320b24100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 255318327 1250 255317077 255317081
    0x4080903070512011e0204080d0c050c03060f1501020105010e07030e0a02100c0b0f010503060c07050109021e04200318030f0301030f120e0f12150126120409 69
    0x20005405000d00c450000e410798030b04641d200c5048049001180000c8212030310300800781ca15005084c0c00e441070000f40038076000010356030a9204682003502c0c440b0b100d410708600d40b00840e54071039454401d000402180c03240c002d10320703030048442e400f80c206000481001a401c1c1d035001d010700e110340e000240004425600c240c104044000d1808192040a11550040790702e402d045420351b008680c2d2105070f40e04100d5005001e640c400000d11040c8015410900081c6e203404000d0024110391201082c2c100500200b903114800040c7d000708042c0b0529070904140c44032191142507203110710300c0d000b28000310391626400c0042000040d88200c1c90356460180030b01024582c1852404144014450b5000c1320071218002d6010350700030365014510319841d01e40201c50003203452044040040da2410060b00e40c48072521407400004c201e49491141612190403481d004180c2c40c1d00400c1003002d800060415001070019103103403201e851623a0b08003002d00d505580e410328200c0c0080804001c000c1040040c91076 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 255319577 1250 255318327 255318337
    0x90a1212030b011101050f090d0c08040e070519080f060103091208070201061d0a110f03150d0510090203010e120d09030306080a05160e040201052205040216140a0b0408 74
    0x141014004c0d603486184007421900103c1d00c03014080004030610008400400212000000924014824500c1c80c0e41d1186140150300c10403451070b40190200e180a4050000d4540010042c48020001c01210a00514503801038454405000c400030200303195500c240160040035421800f00c41039404030b00000c6408150040c8100215544d440c004034141c1042c12243d181580c1da044c03505460709040b030543c8110383c3c1582440f00c441d007040042d00003c0c016078099950140c4a003500c00e11542c0044041504101e00640017401c0e030240c403250610180459110000c402d009400810002d00740c4181c040d5107602100c4039600800b42406044085d4103103400a802c1c1d10300c40d142c003140e9203964030800c61404c2481030b01214581c00c91b10051450055190760b0100400c4041c01e02016810b240e00068440d200d2a10542c007074035800110280c0010b481191a80100b9000c0d10841d40d03009c60001101418149040032500c2055031b6132600e801070b20010704150b10603040701c0c513145c0075116691500502e500c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 255320827 1250 255319577 255319579
    0x405060609150409030315090903140906120106030f06080d09030b0a0f0c230f0d0c14041e0e0103030e0d1a0a0608010e0601060f0509031908090a1212030b 68
    0x38402c0307142c00b6403268010100c0c41c502c69180499200d140013140628080f0603080400081e24124100300880c0c1d200050580c42c8070002d00c0d0a03511581030700414480d100b82444103c00416603000000d03440d0f0701da4004400004004810003507207817101403441e1030740900c000c1c00002508802c0244089006c117001d854101002e50380002e03070003481c80c0c18501680c188410320000304801110303200c400c41c50380b0903540f40c08a106da006403400c6110040c0714903500540c65203060469481c0088044d0900a1107001e02007282121081e1310369a82d81d9003a034941c01c010740d0000b022101c46900003903036204c001c810750591740e054407018400c031120b500748400308000c4c18042e0b442845c04020a405400d031042d01038011003900c100816418103202846003541c0d805030340e0049581c445001000038a500038031235010045c440c5400c40d43d9a407007000203482e000c034116484800046401d0984200410030009000420064650b001d02540d00e80c0204254034030410081c0ca451040c0c03010030b4145d442580144d2113444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 255322077 1250 255320827 255320851
    0x2d0f020f06160309020a06080708090304051806040915020417010209060d110d05010b0a09080d20010b031f0c09120605040303020f03191508120901020a05031603080a050405060609 79
    0x1080d074000a580c0c0d1b40039480f000100754560300f0b000085070302c00394156000f01c800d001140b80600e0000840d4180d418a10b441b082c0301c1138840403c0e40b641d6a60000c494680d0001040514510305c40410f00095100d407041c000852407801c8940d0640c0b406000351014500020800c60409880e5186680070f09146042c9244400041202d08248501485201d000c0d0114241d403a4440341264405409904150000441980480e40d50040c0d01e50080c41c84030f0420134880354400c01c18510072482d000d00f2003485110b505003d48c414240c41e03055141e0300c164440c15484400e11064480c1002034960804038014100700030390344800400807501580216410511030b1070300500c1c206001d4406c2080390010740d8481c80484201a00343d0808913180650b120400100501039002460403500a94821213090812080500800c40e81700c40d0307000340720645016400500352699070311003280440d806620800214049171016000c1400f0b505070f44150b6200315401001440c490b214482048004100180f142c00a10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 255323327 1250 255322077 255322091
    0x15080d0914130b0a0b34021302160308060a0603060b0409020702012f0c091909140d05040801060905060d0308102601050c090d122d0f020f061603 64
    0x521424010001020030512103078481c440d041c06484001b0054015400d8506400c511aa01c19030380002c0111080e4102c0d000c80400c241260b03580c000e80230b5410030480780681d0003a82b0081c1a080f0700404d201e190308507089820030752510720940c1218030314001c86220300d1042c0000e100580c0381d0350081807400e005051810120f44004904030008142d44508407020010401150403824100300340c20b81d5603000c840c00c0b80c1b01d15154040d200059100c80d00c001100f502c1c1c11314030060100010072002d003e0f10203420340c0d85038011110090300d2580544100030083d841e042000035946013512405001d49401065800d4003c0716071021110810003034508510151040c2c0b000404036120741d0365090701615500040c3c0d07460811500c01e8215000103104565488003042410401c0d1385081180e1030f069805013108003001d0301407104036004401c00ea612104105881110b1030702d01403544042d006601c13150f96a06d610807100400302d03141d44c1c0790007905059034401c00114101440301c0800c0d00050316a464006000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 255324577 1250 255323327 255323329
    0x50d0207150f0e011b03020f0f031e09010506030d03020d0b13061e03150e100c090302040605180c0c101508010b06130306020f0d15080d0914130b 64
    0x740980c54102006542c1c0c603280140501824014003200b00a03c80080190b031280000703581d060218000000c00b0907034002201c1c985183c6034001c2c1d51001e03408001103a1a8500f0180c0b00590035506803601d00c80101000010710411014064607100310405001b400c80480b2100f41640070750400440c1c840b07600d842e01004040303601ca40c2100d10401c8241880413a040c0d181400f042d111095121041002040206080c0301161000306510034a401c2c940c4c0c002098034003103000302d0404180042c00c035136007030400c07964517000c0380e018a0030802e40b4000c50f0304000c4599900c0030810b802c802c82c042c0f03003407106000d8000781c140d50300807019028004582080d03802910240760400704595900c441d00305240c40040d801c2c40b01c80c0f403d2140b03980d0403e00751001c5141181c104e00f40d140d03403045c80c40001d0102d078001580600c0c2c0f1141900f900c0c80781c1003084082c0800c4003400c2500d104660580a400d10a1103107020506120703204800e8441243d080b640300282040c601011304c02e901d040361280e0944261608000402c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 255325827 1250 255324577 255324593
    0x2061305040903020a1205090f0d0606030b0403120501050603040b0a0518030f030f0105030a030c080d02040e0903180105031003030e030f0319030612020609011b0b07050d0b03010606090303050d0207 87
    0x84980702e6405800d540c05d81e40390a5202c40d00b0300803480308112043c0551800c0ea120320102e4848080126220b01c4140c401e40b8011028007100e400c001c02c03806003481840304150700030b0b100072145200e840e401e01c503030380e01c030400d10507030307000031200504650000700c0030846481c0c0b15444590000e1040c0345400100d000d0381907191440d40b2840c40030000d10340000c00c010040986080f918003504040340984144055601c000382004081c5101030000f5000088641c40541d4541c101c4006002c13038180c10003589032141c7e240f9249d4112000884030000304842c440000d40c0b04000f103a1080300e40143c202e14490850f1800c80702c1c0d0450744031058140c800c0c0c0d26000c0d0f450b40100054614482c243e40d11042050051030010140c4807603030701c007501d800e0340d40c0e942c2c4005a0341e800c02d50300c03c01000c2c41c0002c0580c2e03054001c000828031030140500b07a05841e02c20301510546c0040181284a0001003d101c0564031304c090500300c48041c4202c000041900d081440041d200701e0081261b40006180541490120385802407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 255327077 1250 255325827 255325841
    0x5070507090626011401031b12080a020105130206030a0b03011d0105061806030a03030c03020d151e050a06201506090109020c070e091603080702042004030206130504 73
    0x303e0744010a0020700c5101c1154250003c0c6880c02000780109007540640484440060200030103d00700c54071016045002a80c034900285002c4048820060407030078000316641c00800c0910055013400001043d0114a07442c08295684c0035101600c1d6940c0c0500e41d000420817071800e207505548074160001c24540e41007d03c0030741403141c800050b450420384100310700300c09014601d85031131805108100060f40c010584800381a00b50070080750708800718600b01e0091040c45180b14120707207085103080141340c60750250300c1550f0322107440400360120030815035000c0c12141f02c0c050740000440c5003803044a00c6200c400316200c0403950040c07031a00c2d01c80070b91400e101203415041c0c3c40004400401140346800d21110b0b00420070244214905044802c00f25210209030048441c0140f002d404275426440c108800c0d80c046444800003606252039241c003500c4e0707074007041060b48602d0034402810b445d810320110303020050840c204038910f020302e15400e00155030407841c02520001c03000c00c00000d080d10303640201c0d2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 255328327 1250 255327077 255327089
    0x5090d0c0914070801060f03020a140c0d030c1b1103010902090109090218070210050711010c0207080615010f2601030302030d11130509100305030c160b1207050705070906 75
    0x100702098a040902c2c002000103010408002a4900400c4946d800c00401c4514206c2c61a0150f66459124401d40314000c14000803102000002800d041da00c1c0c010a06060381812590140800003001c44100c0d410307030a464402042c00802c5040b0780025801c90740403204050b001e00040b0f161402500014082c0303c090788a0b444e1140c0b244164800c52420013640c4050f0f5018903400c0c101c80c149013070000d50314000c42001c15040da540e1404034034294002c1c072403140000c2d43c0c88024810f44020074002510b8500c284a4203d45114541c0401d504440b01e0780e042d542c007401a51601e14510b80844c044800700803114040b00b071007041760030440711a00d182281c103000c0d6000313400075030b960050908000112010780f07108001107401444030580200030148110200c071811144040903403101441c04400d000c0b1a40700415900c800110013071041c202240c00701300c01054220007400256140400880c40c40340c9100c110b5030360ba918000500c500d0054000e0110240a0350848000c0c42d25403c9180c110b0f02c480c2c0000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 255329577 1250 255328327 255328331
    0x411070b0604020a0804060b150a03091e03171003050703030e1804110607052401050108070311090616060c0201020d0b0303120601081e190e0313030305090d0c09 71
    0x4202404080c44120741c0105003520704618114641d100145981800343c070007400340d6228807000341e8550760324844440c15110003800d82e80c2c904009502800408000004545103441c004846015001440c50400c0c3e8a8150f101d02502c003c1420814214140082140d90303040700c6003101001040c020440c00020318440d4031084140040d580030894912909104042c1e0303c40d8000800c03001400c0d03014210180c20b400d561250302d0300540e15250342040403c0506004910020094050a101c0d60312518121202078903803031859140ea0100b20107440b01c5c0511550140c1c4200a4050b840c20407038010603a03140300d540340c08400b220a03034645060b40c80ca01d51040060b900031420081a00303440c481d6038014007084004510f4015040100c00c90f10000070b001d203040c07001c000c001403484804600b01032000b82840d003144000c2c0ca096a01d1007109009403904440452801909082c030181c00000c541d280e03810544080d4000d07107156002c403035580c00440450303042441592000b001411403c01c130000f5040f10303400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 255330827 1250 255329577 255329587
    0xb0a120506180d09140f090a09030e060c0303150f06071a0108010b030606061303050f01020c1614100915031e02120f1003020d080c060a050606040b0d0b0411 69
    0x44100c0c2400344021074180d00042d85035040c03d0b4120b40d0180c00c4070350781c94150180700d0403000007908800c11680700540040782c800820170524825440a5940d9200c0e4803144580c035140d10902c4000c3c000c81c1a4242d681d4810004120780000040540c0f1007a270f0000d01184050f1030040111b1615049528211401c4040a50035903000b52940c1e1802d015000640c020000c884c54203001030f90340c0310050048c1c0d028070800039255010906034500c103c069a006021100088040d1240318000e5000c90708044582c012242203035841d001e40d1807042c0440300019441050641c48104002c4d00c0800340102030248010780100060102c3c0460904910800c1d41e200019007503800403048542d054428a00c440f031030700c104415013402d0761014880d9082258410060380c15580c401481043c80002c1d00b0103036214030300e5101c4004110b41e400052426502c170901752030617070b12032601c0340703055450554206078000401c0c041805146013a60180100640320803002c9604810900850101d41c69030340b441d1800540054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 255332077 1250 255330827 255330841
    0x807030305010812070303050a110a0c1205030105130b03010b0907020c0102060f04050607050715050f0612060405030d02070305040f06020303100e01320312090f030111030a0b0a120506 81
    0x3098034014185034010b081c07034130715895041d4641d109100000303080c5541d94010503000421176201c442c00c02210010956100c05505d806402040a40001c0301d060201027502310500d4480d1090b64100c2d040036048207010035105002d00041e141013040c8941565903454a400240e031080306403400341da1141c010b0803094103010002410500010700e81840a4032460074000021000030389664000d1075450f1607900c42c00503103040550903210303240b107440443c00e01d42406860200c07141d00c14000d14086070f1030000b41070381443d2241c407007c049078041c1081e0000e100c0702d5003800068000f84901c1d0311034541640b4003921500003154010302d60308050010f03840402080041402c001c4408040d001e5080260080c0d894801d0411041421541c600b808080791034060002c855154019a4030881c001d0507a880b400142c3d51001c060b800805a4a11811101d003d5082606042c41160550742850352058a540e07a1001c43c140a0020400740395080790344e000300022042c000e180ca00e1002846400680302d103040c02c0b5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 255333327 1250 255332077 255332081
    0x151809170301051305060f100903290601110a0b1e13063c021b060603101811030309030f01052505090111070513091a010e010e0402040209060708070303 67
    0x5a11301c03901c145400180302c065520804100d40742e4804440c40851307112030403402c4424002c5a4801080140c1100105160345080342180100945280519003075950760b42c01191809a03c0b00403800caa040b6000140c089020200d4041d8800b000c4005004201c502c80c01d2803500000440741d80342d1503488441c10b082041110301076101c0b0090329903161b02c1ca240c044212b1540c0d4002d030321402800d01d62600302c0710003d201c154040c1e80d50280381d404d840502140b01c2100b06d40343c8900300c550714070038003510491104489082c81032000711080c1070514218108640e89583c0360300013039000c45605101c144040d0b034280d60100a00d180d43c00361400089034909080c114110a02c050480d40492488040c00fa408120b9200050340c144840918015408407503040140d420300c2c5a942055400100904011690303241c96002900010b00c2a1742200c98200c0300910207500c01003e02034604c0c00c40200004114440d0f040c0a4960010b000070001854207000f00009481588010000ca84001c408511340007403607018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 255334577 1250 255333327 255333349
    0x80601030204050c070c0e04020f0d030f080f240613030f031b0b06060306040b040c05121506030105060c07080303270a05100e1204030303060f0915180917030105 71
    0x20203400e4281070f115a103103682c142e00ea025240307d60750048001005c1d03681d02554030420020245c04581010070504008110006441e019004140c00c44045850352051980c40740c82041101c0074540a15610150144c3e452103040c00580c0c42141031021003100d00142e250a0011481150000142c0700c803460003901446030038003586240c0a2111100002c01c0650b40701725403043d0100c40340ca5030b0356200c0d80014002d0904e09a204d82040c942010a0f2010b41c0100003001c5421080d5034004250703891007041242030650440058000b01c0c01d000411a40c00e04801510041d1955010f4982650f164008185103410440b4100d201094101c284145400c0740d12200b49200a55409008205401d8641c541c0c0c4080c207400c0c080100381e0b280715028440700c2c02d11030b034006600d0200341e8658031503480c10024003501c0c0700d0007022148415140009065a00f500c6000148110130060640c250300e0000920020711540d810a8111078540081c503002511440601591980180a883d04c0703506140921140c40b9203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 255335827 1250 255334577 255334591
    0x60b0309120f030f04140f010515040207020d0f0f060c05090406060e0a030b09030c07030516060f09150e03190302070b1c150e040501090203012304111908060103020405 74
    0x410002000c040c0c071901c044030f40c44400c03004c0b50501600da41c54070700104250003145c241c49000e8600e0341c1000f403170190401070141490000a01c295482c04042104a01c502280290b000c54082c4071180090601c0c07074112103090241c850100e42d451a030302c0d22000e0701d02200c076040001e0000640c0c0601490103200c2d141c09840145408400926840b002ca00d100c100380c00054051014000010a4071000b04229890b8030700003414ac400da260303640340c015904c62200c0d850268409503600080f8405100d0b2000ca00121441c0d910800ca80746800d408201b201e1694241c1c40400220ba054401543c03810070214810b0000300802110464003800c0c000d046c03542d01d400441482c2300030800c1620b82002602145481c140c002c1703000502616107003010780d0000055200148a0480381c1c100400d004d419403003a09041d0007a402888004140c8450f0140c808900401112410841c00407401041d0162000a030742d032001307000c440c0c1804092400c030301d840d801c1c2d5010420036403000700103104509150082a4022007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 255337077 1250 255335827 255335863
    0x20f0d080114090603010e070801022d070b13060c02030a120c140906091801080f0706121d1603060b030c0609060c0a06021201030605060d0507120201050409060b0309 73
    0x414840c42c10703442a8040a403038402c9102401140d040c0c1e60a50102e44814101400c50360595601c890041c0070350003894070703820012046107151101203034084403100d00c0c4900c0152185001140e64a0591021024082010404207141c18a0003e2020704c5038542c0cac200c042d001180c0f20740500000400808a100102010390305221650800c15040141d02c1b582d44004100d09869000c5c076008284540504011168031a400c003210303020320002d9400701410b030f032800c20a23155035503200340d40c455990300648102800180b54405a004050082d80188155900c10382444440c0403090391380b0385401e081600524111500700b0301007003041500e2060f440601e0066010f460441c000c40d0000300c681c05510703039041c002d00000845501d5031001f070010705181548140704644500310f1048101c9500003d00089464034546004224a1b1074170302c2c190f0240036409001805881d0401c0100d40d46801d030004200d040c040d0600000c9104a03141c0143c01c0540418400306841e4500110058502030005500d103400074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 255338327 1250 255337077 255337079
    0x50405040b090f150c0d0e1209010212070b06120f0a0819020105010b07021002100c021c0810090213050402030405030c011104031505131b0608010609050303030402130207020d03020f0d0801 83
    0x94034503448942d00401500c5842d840b419078886e43c00c050541084000524001d0728440000303071024a0241c03c0003502a401c481500034a601c1e40c404c60721480d003015103604c09020024400d8581882300a80306e81311a03094400b0303e441d840413986080e0844804a901400c04601c1c0d80018482400000d0f1160223807000b400310354500151510144070789070000e40241c4101d10400071480c020009031200d088414020001c00e207100034003c0d207800101004900381403800d907c000c940751085d240d15000d20452515848480d10340b1070000025809007036810a40d0000c0640002e0650342c51002d14840c0c0e004170041c507035415074107554030b003110802081c003400c03c4014001480800c400c00b40030801c24000540001c3d0380e40720b40701000d42000142c1c0004020800e204003424028a0008001c001c649168441554690302d4000948900ca941c0c081c0e160503a00900000303016260400040f1002d03020458010f26200c0f036134010031030201d0741681c1900035034001c040000a00f482085140502c02031071428a54035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 255339577 1250 255338327 255338353
    0x15060a030b03061509130b0112030504030b0f010f0906061b030201180b01090f0204030b04031209120c05070b0f12040c050a0806091903050a0e0a0b0d1508030f07021009050405040b090f 81
    0x44d10600449100249090a109c105809401294083c1d900185949101d2070008000c410389502406000c10801c120780001070041c01a00a4401f0340d8445d40f80d03040700c0c084aa82000c0a000b001405408540d00c641940f180d045920007000c1c009406609820041e60401800c41e0036502030725411102244100020404a54004e2180b074010b545882e0801400046c1140000941f544500292108840c0b00301c1c082003c1d040300200010328070510545040315a100c00f01c11240c003c64444901070041008a4000c894400d0809580284904410700080e03455001050319140340d41c120f40c005a0003081031184200e4108401c0d6619500100724500c52503a0360380040c694060f42c03403100203100c070f003440c01500c9640340344102012700303299102c1607290740000608201500c440c540b120901030490034049031642000c400c84a401d0b60070550b8900d06406a0700b031051a0400001e000e040000032400800c1603a10f03801a14041c41c05202c04100c3ca09142003a14102016511009030680c030000b0707561a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 255340827 1250 255339577 255339593
    0x6060f08070509090d0c0503120a0504120903050c010f1205010305010608191a06030109020d060c0e030708030f091504082d060c0a03020c07170f0615060a030b0306150913 75
    0x5c54042c525102c804600c4510f0203500c0c4d4011500642c40704128402000702001c49603002900c200d005410a288842c2108010b50700602c4074000507105800880b003031300865006420016a1504500d03048420280102c04030086072000e030000c0b14142d454550030441c014040080c1c003500740c42d003400c0071012045552002020a0f1102d85c1111410809002982669081d0320401e0170f180c000e1701020f034154030b0749003d600801e07408401d800481c020b012000341d28200002d00c502035032120001140380010b1500c00f031809801c0300004562160b00c1c401d040c140c003400d0788041c00c020a62980102403030400c90b003096005440412071524810742079004007600039000103c1c6da801003005640960758141500b0f003207000c1d1007060742c0c081040c03088400c005101100103000100303010322b01d0140c51481034803a1410303440e4401501e0140c1004815021b401f0149490b00081c18042d65a040004c0e9800d00c07403011a0500c1d104a45008010f9000c0301035105c1800c1400071580d2202c411003c2d000d81c5c0030240e0361050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 255342077 1250 255340827 255340843
    0x204060f0b090d0809100e0405010b04031707140709020403050601050906060901120f180c170d030506030319080f0705040b04031709151c02040f1401090306060f0807050909 76
    0x210483e0f00d440ca0340103100c881c3c011600241d1000d0108034034101139042c00741a8420922069004901d01400007030504c0070034040d9000c1e242d0140c55005407a903030920300440c9030440c0b4000c0d15131010b0200700500a503401c114000050180000c05038850f4a1814480d0510034168009402900e920702000070301e03540c0340c04440202400342008007801400d075040d540102900f882c501100c46c0f4116110030b08040000c040401c04d4030400420640b251500c000322000f440007040d10500741d00c02c03e507241d80d0318003c0d0011a48958058100d070306007421100d001d074200e00003070350340f0011030060401d000680520b00d00c5140e2098003818030614080c9090032800c1180f003248405003095090018540040100c0343c21506901d40042c54448607103048540050154031040b01d684520181031940c0244624a000b524222008903001d602180e1421f1104200c08140c0140c40d1704001000c40d012001a0300d600c0b0381da000d040159a29081c027405c3c5418245062582d80180c0c0c030607202c15041242032540051564 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 255343327 1250 255342077 255342079
    0x3150506070f05010e16090f06030b0c07080d0c05030103110a0302100f0c05010c0e09010e0c070602090127050a05180703020702011b0524090c1c0501090c030204060f0b09 75
    0x58501180e410004d005081895a2054900840340c040c42980800400307034081d03e680d20000c0200107442d0040c0c030102c0c0c60b144001401000c42000087c450001100078218450088081c14504546a4544002c9802100020000c214080700501c10302c10032003044040b2184c01d0300e40c0360141c0d0450300010110840b111040041089003040c400700148031380210008580c0c064028030100c4200e20f0007802c116034240d400c500035440e4000000d003240c3c0a860f040d005892072303100d4a180c80c010f511044082d52010141c0350600c40c842c890505c4280401c44004216100000c01040040c140805c001119800c0da00c20b0348a0110005001103138140403640581180c218100181e98180b0b0f8801600e000d94443d0300d8460b2418003980344021f0046c080740065800340e60400140d21018800705156040343e0640e0f50855607030100c03030034082c1030034800341024484442404c40054000581e441c94250780c503181084950000a907010400c50a0038080c20001d03241140c80c01900f0380c201150901c8074000d181e40f175 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 255344577 1250 255343327 255343343
    0xa0903080c0901211b1e0509010504320f0102030421020a060206090d0c0b06091b1c0b0306091b0a03060c26090d030e010f05070f0315050607 62
    0x1280c4030b03070041d0f88005501d0142c01e248100e00d40d030015180024085200d80c080a540155920159544600d00494031115144201408010002801c40b0260040141a81402000c2201092133001c0301c040311a0075512001888049001614240b10070b4a04003031039024017050245003050303a070044260313401d0340c500f01880c0c4120301c4040a106442009001c01a41044c0c4003c008140540c1c085900da214440140403580394014180c0c04444221581030054601002000420410b1814207400ea800164062190f04040e207c2a032405960b841900580d00302d010a4040d0310100e0144e01500d114610118060070440c0b900900140d1581e0508598000035115080615803076560341035200050341d0070084c10030240500740d0014000c030000000403425542140076100e445031a0081840c882c05c60400034280b03981d802e00f01900a0402007401c013030155200d982d81584002248640e500c5030340b040e901d0114041c4c100f580a4110344540301e8a411070400d0b20000d21458581400321145180d0000301 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 255345827 1250 255344577 255344587
    0x714070507030b04080703020f0d14030604110c0a06050c16030c050f0102040323070b090103020a020309030f0102040314011107031d100503011d0f150a09050703060e0a0903080c 78
    0xc25418481d05420081980c030302c280a10090042c0ca001a1010a11039000c5034409091000300e00d9481900114000000d44103044900c8409020005190403000103000171031103040f8442071082c903411016000216601c81c036003440a020f41c034007505820180300040c25252250100c00400c903a102a00040c083c003440000078030400000300240c0c4111003096000719200c80c1c4a1030104100b56102c0c000740141d041c4401e502641c03103c08103a0700e08850701c01c80154a00f1402c04010340184d08006a91303025400280407900090b00c042c4420000c49409900044ea81c40c1540341c0b4905000080110111503803400c0b800c02c54410310380c0111800d00d501800e041c01038007201030500e40f1100c6007030120764011811407441c810003600400a036040e2008264145c2440c05a0340c80050301c40c40859280d501c200c51480800c0e40c0000440c0d09078603522019000f00b154945488080c01174a405903021800691348010411098544200068100302c2a85041c826000d507600c009100e40720141003a08540c0f00003c07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 255347077 1250 255345827 255345833
    0x30705060a0512100f060509030618070305060c030a200405010c06061d0108010f0b0d12231908090c040e010609091515051503070528090e071407 64
    0x4150381c0481d003562000826854040002c0030207a0080c481c40c1c005e50716440010645901400c26151826400b800411a5546001c00640e4600c401c00500a0034041c00901002144007848100d02c00c42c01c0c0d0012030340c0d034145069400101c840e0040c0f408200c620f07003410858071141c030030101c07000c0320024640405030500c00e0070410020001540320500102c0c1e0820340d40702d10b402505559040350000c400030000790003a031070074209555400004030b40c0040d56003901c07000542201c8980318202200e140161101081c40c50b4500103204415512081c0000450a40140440516605442c42c103510f480360503800c1800c003040e0703035104c884e001d40d12030394a405507807000342c038250f1180740100380744a800d202038241818134684c210302d928600200300741040b43d030085150908546030300b11400a40880c45010010303244031000e0300007800d50001c0000410030f6641e0070200480c901e46c0c003020320541011103007a0f140090080ea1051340510b141c5482841081401a0854190031704501044d4900b56504d40c149 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 255348327 1250 255347077 255347087
    0x2090301020d061202040f0e03040501080a02070f0c0f051801260303100f090204050108010e1008011b02061e06010f0323061005030103050a02041815020a090501050702030705060a 79
    0x2041005880c40d1a0f4001868801c0f44d02042595000741ea04005040205070300340d0548803c44082085507204120800095125020540d406008450010f0231702d01150b850342d250b000a954147ca0f004421502800f00d407000c0b400c40c00007010203d500034010b104032009100304860501c01e48131015400b03402d414045c0614a03ca0546050200c15a86d45c0d00c0c5c02c41c0000002e940602031010300c40c10f40f490100f0110014400c6a050300c00586806045a180c0091107154900c01018840d040e400e001d0005100b442c00d0240340c442001000703220b2240c0c05080c5000386807400052035003c0403c0c4c01d4400b03168158060038038540100e403e103403017003000f0781034401600a0302001e614194032025003401131444422a40c6240d00501c8100c4244150384000c4000b19a940000c0c00082c01c25044400301c03c0043c034259010103040309045a1424502a40d41c4589401501030101480e4071383e00020381e090010b41c0041440064502401d11504020107500400d40c4d400b11805040d0003002d002640858540c061 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 255349577 1250 255348327 255348337
    0x30c1d0103331a040e100c1103070609020405060607020d03180e090a060605030a0506010909060b0405090604050105010909170c010b100207050a210f030905040c0203030105030d05040602030403060209030102 91
    0x8a01c2c0e900c4201e0340c14100318010059603003008102c40c1c0b42d00c103142062926000c0c10598266140040c0765103102c0600e120024035a440100003841100002c00d040c94070248080e102c01402408000340c200300b07500510098800003000c1038826101007002c140180e441c08190801ca640514107440703031819180001120105903040305071542e06c07074810071100e0f050001c0c03646043c3e449101c0c2401002d6860040c183e4481c003001000f8855085000144124000f907445460b00901402c80030800e9100c2f000882c00302d03501a030300c022281d00040100410712109004041c014100360104000c154550749500050480c45050100b41c03580000700c21850003001d42290001c0500100b0780740c4008906000650703910554402c03d409100500700c0082d03610140013044610703c4607820307000d1010721296580d543d03490500b03000701e040c0100d211003c1041e440701d00c18000e03005c05035001180c0c0ca5041004151038600c1200348107080000801c014802d2550100c140ca084035480381002d61280d07681e40001b400b900030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 255350827 1250 255349577 255349643
    0x5100f0305150d060c20070f080303071b06060e040803100806150108100e0f1e10140406081e01180827130912091a090f090907030c1d0103 61
    0x80c3e0a51200f0f080c6c00811400300300c0d40d130103242c40c60031a0341e14122034681c042160004081076210320007444848240c14038640c55403052034009111501e898081d103458a003618251698040481008840c2030154090f030040c12015000b40300c10b240c40c50400390401e10740c0c2d031110304101c0118003007651448529400340150502440e200031502d40390100c0030850304202c60402004ca85010503400310704040454030301920282c2c094000c21030400383e9140c89114007054054100d5503e02c80014800028000540e604078054501103200700c0c041111400e44d5124914900011280d02a00700081c00301c104807800750580c1c2612150000c01d03040354031042c000200c0d010390002c504012a170381c820038940c04100303410700c1404009402644050100d5a511960147c860f41e080340485003081c83c0f020030040d11220344024101000c940036040030507008441540c2a103841d6000c0c210138000c02c480e6465100c040d1489404c09514902c0c85845170760701072070620010b00030007003010b00302681d0040d0b41309400c94550 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 255352077 1250 255350827 255350867
    0x14040b010905030706030c08070c0f111801060203031006052a100207050604030815100809030d230106050715050604020d0c0e03060117060f1005100f0305150d060c 72
    0x3691700800f0b00a001130041260000f4121030000c1c0550b40100c03400721116400441e40e2103034031020350300d24440c0c0c1c10300408290b010316800180c140001881103504d020f420702d903002e141c9030308103001c03004042d24440e00700c801072040034400d201c9041c002c40901e0480c01d0b003014800c654a0428a10541040d45400f0303410319290000a82e00d0500000041040c00360f0b120303590b040681d50380d4456900308d900005109075400040800b11400e460b1080b200950444405401e880c6400ea480003005c045582100c075000402d50a181800e09890700752076102d0060405044c401c0c80c00140361f940082d500c0307001c1860f2880d907035200c1c00304120307440c0c40d8141d801d0240e10310b0080000349400c4101400d00b0141e042c4844c030078803c81b000030038642c8090400c0c1064610b03180c01810107482d00b2035000004400141000d0512280d00e500091035030319040c03c00c030780c100184c442d07190701d045402c002400d03540001d200b030707070b0100341d1050800f050b45a007010289001d410403800900312014540480d022992544104c4d0030344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 255353327 1250 255352077 255352079
    0xa0c23090f15041e0504020301080a0f0c0f06021e030c07120804030210030f05070306081207050c0604060914100e09070c080301081501140a05120c0a0e060102010b0102010614040b0109050307 84
    0x44400c601c0389504244c8015000300d940d58000c001c26880309000b1940307590419038030040001c0d4040c04078495144030b007407410140c54440b040c1c204004c5540c0d102e00d00690100c260198450000c056900c1e00541c03180145141810b20301945641f5501c52052195151138580c0400c1886008401c3c3c0340034685c020f010098a08031b02900402030031898460b07100440c40c007030105240a00a101390300c2101c810074044c0c006601041541c824540002205440b00d0040c00350600e42035448500810162000f5204d81680c00c3c20201070010b18405003918a001d4192800500c0305981c0144542c07003142011144820f0b01c0d611a130303007103440d00c0c8070381401485130a020002141c0b01902080d41445a0141c88800710031342c0e80e031264000700c3c52601600d0b58108094050a01042c101115592161248201103900e01011540811420141507016000f86c6500f03000307125480d81c3c2070041d102e150100340700a010036424801e40c01d410064140b46039109a0b910099280c803640188084801454020305440b003032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 255354577 1250 255353327 255353339
    0xd0c0302070b0a0503061e01020c0418050625020a020303030f1f03140d030b0f040504230606180412030209010c0204020c0109050c0a0b030106080606070501050a0c23090f1504 77
    0x2d40003a15454403647d070f01c0c01511813000100f116501d00a405034014590324120710103100040448008940c44041004001804220100203190042c600282818000b44014414030304046042c044903085400840840015030f82c000140c94004c040004102c1c4152130ba60000a5045000c2c0c0307a00001411840000050020310360301c0d2507481c1451000c0c0e03142421a01001c800f11965220b0302903100300c00819401c014280780c0d218551041c441e441303600070014400c03400440d6507042e074041c403681d500003c2040b85030300b0b1140340e40f21030241d071404901d528189540d0360456585070150701406c140c2d004c1110030a03a803082680641c140c1d00600110f54411030703141d0950280100c00e03000d072400c2c402c0380b20704592800e0010303000049460b101001801d603420488110362014020700526400001407102d01c0c04107000b842180d0280403428800154510385030806081107003044005503c00003000340401650b04403404841d1046411074900c102c051035940000c46494848048108a4001050100345 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 255355827 1250 255354577 255354587
    0x9060c0905030709020a0804060c0c1a01140d0b060f03120c071401140d0b062106090f060307120206120f0a050114060a030216020301020c01020d0e030307020d0c0302070b0a 76
    0x259a800d805807600c00d130301c1d0384e4130209921482c0d900e0f00c002009180041d001c28001e0340114210800341c40c0c0500c000d12207803111401c0084261050001364008001007203a02a4007541140c0703c2010b50b00100750081c0350311503044804000f0302c614024031a403403514100ea40c0c1400800c200d81007000c5410340300c1c10b640c1107495a41d400c90051541ea40783c1d40d001d4244a6010f403100304000071490380c075545070680c40c017a0030700540107150049800c040b0130310861507590b480983d108070090709020403403000c0c03409108124101401914001d42038102c4001c1c000c19440c085042810745201e503250305280d40940c80880c4036031095981c80d460707000d580400e100010243c001d04c103003ea0a030b240140301c00e0740c81c0d03405c00c024000801219540104100040c0b02c0c1c0c180250050b00c540e45090410404880480e0040ba0a90f80444411030540c0d6002810f08201e007410301c58075031514070040042d41189496100a5560f1520300b10002c140039000842808140c803c00250000c0c00207524a03644400300024045c01d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 255357077 1250 255355827 255355829
    0x70305250e030f060105061e090303031312030501181518091412030f0702010b131b031a01200109030f141207030209280f0503030a051c09060c09 64
    0x4801e002d103010885201c40c3c002041030503114000c0c0243c0c940005c0c0e8040304180e66114105514564050000d40f00a0b9400d0000d14860202c486122200200610300510200100d00c0c2e19824180303800d005008101c440ca050f140c0085581d80c000482c2c1409180040d52011558044244082060f494108009031a0440d00c01d903031007143c46600c0000303941e201507100c207824540003039000c1c0d0074000128509203441c03007260840418000094240ca08001240700314040b05d848141454480b400034103894210b6003001044001c07441d080048503085038a69900c140d5804130181000b41d1460020000031005010001080051000300044e112518010340300c104c92035265800b194000b00504072214880f82103401000e54034201b00d800b075640502c20380003900201d908507040510409604c550410111a0300c4601da000c442000034103282c200350300d400d441d0a8110078000d81092144145040c0c02c0400c0e13070308881d40e40070700c1c150303101a020b0950f0060028040180a16040401d0b854240360402c1c4000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 255358327 1250 255357077 255357079
    0x607120e010f0f0e0d0e010f030b03060906040c0b07111009120b070215070e010809030927010b1603081f180e07060c11030a050105011e060806010503070305250e 71
    0x2001d442d80b040e44c0701c4c0d25414601c4000c0089110403d002d00e1541c031805c108200312509080005d07075000c451010038984841112852502c0e070011040c001030201042c40c2e40c00034080034150f240b8000070f83d60f07520181c501504840317000381c102000041a082c041e840c0701c400303081c2541000084030740c207040003015008282c0310000507005800b070010040300542c034070a101c0c090b51f843d0f10401031002070044402450090240d401408140001429035980d20300c00c02064070342d040c4400c04561300b07070101c444400741030303202c4001140c0401400c180e0490b034400c3c2651041c1c05003004401c40c0e50710811242c034445d4061156418280340d25000c148225015009a51f88440700410815a510710000586d00c22850049202081c010501c0c80001214007942d801c4411002d4192400d008090303031114255802a0000040c040c00c0d2202003548031485d2502200500742e40c42c00411a0070100b00203803081c44003a01c20001c00d5116800111555515900388585c0711550444c40004460501e000b4141108451f0103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 255359577 1250 255358327 255358331
    0xc060705072306090d050a050d050405090f04050703080a0c0606060503090618060109020c12070605040b0a0204061e02150a020a110705090c0a1824030e0607120e010f0f 74
    0xa04000003040400c2000702c4003074403281c64070300400200035000c07410a000320740038852142c40750005034062061914500c095203c4580315801c000801041d4407001304103c55130300c0e00400708804280d0010751501101d400180007a66407100c007030102c07184050941c000d0450380c142800010300300e91020055101c0c203240c10036900d072070321a0f0745c101840c2074020080002d180c1c0320000610441049600a040d80c0c010b0404880b02c0e503120b0000400a60007142c0141c0d030140c2e40b401044244444604080e500c81d004650840c0383c58201400544100350200c442000c0c9443d274007008213824005c00c0f901508115000300f0100c00e240000c07000019601104070000001c203419642042060000344c1c8105580e00103101e80c610f5070710285c61301140d41101c5001d000b000310661140402d1102d24803c1c4020300030341d41b1080303017200050b0301800503440b01c120080c04041c585810a015500302140b031a40101c5145810110383c5444d030303c2d580181003090345020055290010080c0c42d00c40a6000140340351a032102 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 255360827 1250 255359577 255359609
    0x61d090402010e041107020d080a0e090c03040f11090901060510030209060f03130f0506070f0813030f020708150a0c0804080d150b0309030702041a01020d110c06070507 74
    0x244100014292030090115140b0446614180b6168122110407049181410300f00344c6e60b03400040b10502e1201c0295098640040e8807040d407580917140c0015440c080d6140f462609000201030742e203120040000d0035042c511900c020400c400807020300c40b284801030041090303041c18501c0500800551068511804c1b4403c006440140a4000c1d9001000020482c6d410450040901003103035100912080030041820510030005502e0b0001e4040d090081d0b006004524100001900204484441c1028802c20004001c0c10068403170016030715591516140140345858503081c0d00c1d0000d00e400c21039540c00f400d079a0440c0312108079442071294030481402c0c03248071a291001d580c44c00c030903100546130807800c0280700c24590701a0401c40e1404220200746082940e103041429183d0825580f04041e0740002a901c0e05625050180f62244078100d482c45520b0000d081c0081d690b5103400c00142e051050445403035011103014886041000c801402e11640e4400c1031400d00e407519603501504404122a40d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 255362077 1250 255360827 255360829
    0xc03060405100602030f0f0c0703051606081512010b04020409090203100207110616050109080711030c01020d20012a030203090604060f15140f03010b030607050a110601061d 76
    0x2800480f070f5190055450400c41141454581d80f12051b46400c211007004411401082004044000c6015101408040502c101c0c1e00e140b0500c103610000030440d2007800d001014003220200c01110108944444158400c1041c41d0302400c1003218031a4014030100300001d140495400c40c4507800e200300e065604010601c07010700c0881c0642c59020301b0400f0415601016400c2003002070500300b03041441102249040d949003820744e440e0100803074422034049064400c000400700c003c031200fa4120054601d81e0b041c000002c0d03641c1881803070b0108214000d01000d807103000c4002076a000e486d8100c0280b0010010311101032a5104443e090305507071391071045112100c2d1182c400d40c0d0003950b01c04040c013041c2c0c40355100e8001034a0b1540005e403017980c0c0c8104507030502820090340f00040c41e00d2816000120001420800a48205190180245d040c6103841c1d038142d90228001d0782c0441c0342e051082c2c43d04292a81201c3c1841ca407041903000e071141030700100b455500b1651000c0001c02074a440e00b001d100d644 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 255363327 1250 255362077 255362101
    0x60e090c0d110f0111010e070f0506090d06050a020c030f09030f1c14040e091e0c030307060906020f071b14060316140d1413021c02040f02030c03060405 67
    0x6902802d01040120a07180b145410a10900d008030145404600198500101c85c00c648a02210a0503a400701c00200119500c2d20810b04c0100381c00c9600a061444da50041100186018130082c2a00c0c0d031000064032800031a030688000c450b00d442140d4640d400a40c01d81c00c19400fa0700c05600c039104810868022250010704180d0044136030100c42104040b0003000c1d00c0c215842c0c170900d58205814800410035003104007025228040103c020418400400410003001c082c00b5050840364125400d010318644001040300d041c10b07404203000951030306a0610000074028074500518140d8000303081018887c1c004a80003011344817a03000d65210345ea4400d40b141c1c8005000b81d00f0b810810034400109151800c41105082070503a042c00c80411516000303002e05980140b003416411569030804018055500d00e42e154401c0444001c6000003c468001400e42243c82d031a6112880c000e41d24003045440e40c1d0820001004c284101759100d04091030381d040e443d0400c4980074055840c08000a0904e6000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 255364577 1250 255363327 255363349
    0x13030f0c05091314010f180b07110705010e0f0409030f0e040212070e0a0503010606020a030215010e01031506031b03060b04140705070c0b030c0a0f0315090519060e090c 74
    0x2000d49000c3c0641d99031600c010300401c880d0707110b5540c3d070075071010021080d00a5041c10701c50317a60903440da030301207250864070b86001500c04d10800c800c249056042d6030780081c1410036100c007400c004020306010400100c0d01021600181e0300705d4180300c6403104042e00501750143c5044291030305041ea2455401b40f200728040d114032942426150070101d11510300441d0f10703a04041028162269a40d121004079003034a42c0355004034010f0384a5442441416410f00498401005c41030103001207500d0441c1c0e86001101c180400b5003110b44c560600301e00301502d5030090005580c04080c4603050608190702d10100442840306a607147e0408409020b10701d042d21917903040c03041541d462107d0752140d0b42d040ba036640009000f00ea4181b0401e002066070001400618403500c034a00c0c3e41a1f440d44a4031740201500c4c003800c5a28140360034000c00240304560344542c43c09481100310006002d40d81d4050034010501da050404034401c0c0f030450080380c602c01d90220144a60301c0441100d004045403c00e2180345484 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 255365827 1250 255364577 255364591
    0x305060f070f0c0303021c0603030504051305010e040201140717040611160e06040e0307120908070e0a0504080f160201140f04050405070e030303100f0609150305060613030f0c0509 79
    0x3d03070f42045000070301076805003d16045500ca2100303910a00100303c8210350460300241e021a1012404100c3c524000b030b0005212003600005005a51401d01081300200c1d001d4002414800340341003108210b60b81c4400e841607150014240c00c130b01058400300d141241d200b40610305c00510346c0d0307010000052001030050180c03c1400041d510301e91400301000340855001c1c20080d48941c41e80303250720b0030000410203001c1e01750041d0546100400a08806010085168020541c680240004228400d60074046a90182c4100b00104841c0e865281542c002d204169101401d01c802084120724896911007256625100f03803a400c04e49035505c0009022405a03d0f403015000380c00704001c1c022410660012a040611403c103c0c0c400c440480004e410741e00100d54a51200545640800c011081207100030020600c4d0309004000905004a4031085884821700c9418180c4403004102e80751941001c440d826409102d0003030b4040c1d1289460004450100019500951000782c04035440c50a03480c0d0b2409180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 255367077 1250 255365827 255365837
    0x4030515040c05030d05030f06030a03020a060506060706051927020f030f150405072c070c0b100608090303060a05091003060515010809010902030c1909060305060f070f 74
    0x203200c44003641040040003120724884a290002d41600c0c00c00150700203a0690703e0b05522131600040303400f16010000c21170fa12a91141c031022002c290040b410784413203600060086119074541000c10110b11030b8050080026141000f0803072070080c404000300b121000300340300784182c0207480310304e08400034508041c0450291400c42c41006141a050010b41903d005d02030358038802484080505041c0701c0303e030304810144a1400c11042001c2445204090202031040c245502401d6104104400380ca038003416510a140c00820f281500480c030203000d42e903016219138401d140580d68100010780c58412100403d10407001b0481c00c14002c81036034440e0030050308100c4268901344c104200214054019101c3c00d00c04440880481c0e464025607125401040c903a2006404803c001400c4000c024210341c81c036450102c89200503a80818030500e05a0100c5071413090000c0d140b41c10700090010740c4130b5a15245881030000030840042251840f80d451a80c00c900356a48024007598410320201d042c4000070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 255368327 1250 255367077 255367093
    0x41211120f120c01090b101508070e13020702090106050c150906040b0705041a042c0c0a2d0305010f08060a11042313020708030c03070302160b06090606040305 70
    0x4035110000c0d03c031040015002103420b84054441e00400e90f4252010a26480d20f5134090144000e541008540054545450303455840c000b48020504801c1a4859110741c080e804215080419901a18400e940043c048042d5594032800940703640d120541d60306c1240174140c03d5584050083c0c6c403d520450040780941110b540301e90f58680780e01030082c09503040c131500744404a060440043d21030042c0c0c400303c1c003840d60b507404d042070007494010b202e2658084c00e0300016104040521546c04913001041503180a40b0340c0c102500c1a682c03514070700807052200e0200c034100c4440c0b140f0101115010601c0740c0b42040f5503601c1d2104e68650300c081d801952196400b43c40030070a401256800400184800071129041c5500c07000e40e095108200e5181c200f9001825607040554908500c0f00c40d03c50240c54030461800740550f840417840e01008000070013500001c4006204180250111003401c10025060360320842c00e46480c488200e000d59030035004420140020341c0c103052107000c94044e250404000d00247d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 255369577 1250 255368327 255368353
    0x507140a0c0b061f050702130605010c060f0b030109110f0409121b0f0501050f01060203090a0e060a03020402040e090d020c0906040c1e020304050f03160e0c041211120f 74
    0x910005031209130428100441c490f15084020100c0700c1240e410b0395444e1313075100765004000c4a4031203250171504491030f04108006607138102403181d41040e4000c40126604080c0701d0a000149103803541c0c0d079015420507682d00708002c001c0e0444540200c0172981e2200004881041c0300480301c803100d00600c0348030069a441016400381c2890f000281c81c02048078a00d010913075030b045070040480300442d126911001404042800b01c41e005015018501c001c2d0f00b4118864009a041070891003a000300d03c1506011411b591514003104020351b401034001d40d034450b51047d0140d940c11007200c0d94081406405044510188046100c20842e0002090388155441d00810030004101c1c1881344414000c44090642d01140e00302d03081d196105098001e5a211890b0000f808424050309841c03c0c805d07048600c0c6080045011a01502550506c644031607440d61441d1844036140708a4100b414803190300ca180d001006a10f9842280301c40d0300f9501100e040040070752740c41d40e03250505200c1c012504101c44400311 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 255370827 1250 255369577 255369593
    0x1a030304031407050a1203030b040c090b07081204080c060708150609060d050c031b030c0d0e030c0f010501140117010528031406060a030c0605070609021002010507140a0c 75
    0xd46010388003594007031035542d8002808104968000c100c07038100c02011b0003d058052050911300780007a44c0501006158200062103402d05014028000c100440c100742800f0050041d1003e25030351342071510300d85c10300b800c20f4041c0fa0801c5005102e0361190500041e412441a403285000d800c0c0d0700d10548200c8807090412a06400114500c0c0c0c02020612088415000741d004241c010f004c050b058983d00d080046044442100c115421014050100140701c02c61540700c0894000040140000851480c0030910504521601424a070301c1c1c462007424240c80e21042d48064100c0e610344001c01c0200c0c8881d001511403196910b18140300b140c0090042109003403600b003c090341c0b244040c0a0038440300c6a0380d46c0e071028030740350004e03107242c025280400d0781c2c480c08104c081d4003d501101d82010721851965101c802200d58066281007250115280f0104569a048060300540c0241610031b00c9001c0c40c0020b00030042190642c000400309207547c440300640408407450410107641e202d000e48003c0c0c8401203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 255372077 1250 255370827 255370853
    0x80f0f06070309030c050a1406060604030201080610020a0507031203060501080105010c0f26070606060c0c140d080c030901020709111602130204060f12020301120b0a1103070c05011a03030403 84
    0x505c21480080300000c1d5080c803c48068902c00d4402c02c03440303810310b55003e20300f04004204030b0080702c0c104000d1003d41e030060a2141d002d03904580344210541c042c98101c0c01c066005100400380e10405c24040700700700484034521000384239a5401c0020030707682d100464403120284561404034194191040208041170380141c0c1c00380c0261032281f03007015414050040c500e900c0e000c105d0f140d18041a40c104020f0300d4001c1000074041803515050500007520740207500c1e803140c841c203101348d000c08020030f03450349402c581c096246801441ca991151070007040320f03850b07601c103418090060241803404115075603d41301d010003095480c0b00e05410402e403140e41081d2100d0b0300b07006030b910229829000c050741e48940010409402c0c29650340940c00c0003540c010700241c20007416901d07101d00600050100035000d00f004050240c01000e0310f006602d031060603c000b80383c851414811554000b0411030030320340054113858110301c500000c100c0007044001021050010300d41e020b0b0306400410041000c1000024100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 255373327 1250 255372077 255372083
    0x507030305150a0603091104020f040e09010e0a0303020405090708040b190b03030a05070c0e09061605070209010305070501021e03090f130606080a0e010504170307030b030115080f0f06070309 84
    0xd110348801c2c50004812094542c01100006c2e22520403c00b0031202208101803107400380d80542c14202034020082032801940a041410001c0800003508030000350010107054080005403401d8452904004010754014014180074021040119000a124102a81c0b00b40d4120040003541d0711004a81008519010711680d2040c0d01c400a40116640510040c890070015898403a9199110300d8161480d0109611032419141e0000030810420404a0406d9025540760140107544030404425a8140103940d4080e4012042d000044100040029218240d40090f0211405500c000900c101c800c0802848002c1d150000e0000010a0030039403110711705408020002000101c2d10f00c000e404403020f540c805000150818280400c10800703208903000b14078218001e00607468952124141035817141d42c0c00740c001000000049619220740d1060b44a01d000600a11130246524108060242e003402400c005020304c648098420000042c0a903450345510040e04159036180e205800410f403400081d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 255374577 1250 255373327 255373351
    0x8130b0316110c060c0f070e0903090d170d0c11030c0307020f030f120405040510211b0603020c0c030303010e070f0507060c05071109010b04090908070f080703020c01090302010507030305 82
    0x1441d990740c4d80090a0300c5660030008040d81144904e800c1d26100d01070303000221000e40700041c002e104a02000319100400c00303580f0440c0c0c0041500d0b1554090540456010341600c011910802e821000e03003002c036a0305465501d000100c074520030340503140c1c450940981c810340d100b0403002c401420030701384401e5503002c0182600d5101421840b4641044220000c01d4071071600003a05101900d028415150016032503490b00e10001d04050f41e2031491725003141721052840d4140380440800c28103500316520184d908241c010000d6076880007902030740107a0030180c914040c4d4440d16089041c000103030b03812603074590f0b400f00d01510b500034142c411206100da12000c000d02000814081040d6000d603071907001c82c56580c00d548140b1401d10310650b840140d4418807443e48000100280300026040d82c05450084100117404078542c03514040c030f807060306070091600f8101114041444440b20243c041903010360240e074074a628510044460306d00c240030007400304209124401c0800d10903849290302c0b070300028072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 255375827 1250 255374577 255374593
    0x11d0604020d020a09172d010603060c110c120607050309010e15040209060103290604030611040618030b0112060e0a0803062107060c0503040f0308130b031611 70
    0x210350166801300035924080380c10043c003000f807880000010082903031320201610800d01c10201c0c0400307134043d414494034626021007403420313104400e600040065500c070004002c003902c00d400140c0a070003001c00d03000140c041d620b00b0005a040c84080ea406030810400500503c0d0f0b20000251109d0b040500b01219039035071f0b905204040c1204005143c2e48003c40344003141e01d0300c0d00d441081408100102564109070500c1407860545440c3d20600b40c010301044217103448200001e011036114022544040c0c030003802c01c1c01c03d10075501301100803c1540d0a5035508d1124a070001020000011140300081004036801c00409c4444c01440d0200045032003a00c002ca00c0c803004020091800c6044d00c003d60765400000180300390351070260b4040c446007044001001440f0a070f030350074a455250504c104010312440627000701c1007140500445001d0a1740143c00503000b41c0700d0416200640141940c0d03044000120800b061120b4890192446030703843c40100d1010669000342200e04600d0318130409198803030260 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 255377077 1250 255375827 255375847
    0x60a020304031514091506091f0e0109050610020d080a0906020c07050910061d21030408010f09120311041503050604150501021509070f060c06060608011d060402 71
    0x10308081102020b01d002c80d413048a02c4401c07408a00c041c19031600b0f40d000740a11007002d19606a0325038002c0007129100350540c2c416405402d03038801403c1103152600e40711000300d1041c13400f0790544c0c1a900a03203070800441d90f0380c40074041c24210761881200035070700c6140b04459046c49000041d510820000300440c1007011a92810141e17001000e520300720b40c00143c02400700e424a03c5006900a6100c0321003c03c0c18980400170700203028410610f0794010300700d03049080c1902d41007139200f55003414100d046044289145429182e411134000c1c0180e9500342105000c40070010b0050081e0141c000c1d60004071200d00d0301c03080d00207001c1c40208070400320301400001104404500e040c0300425044d2404071b142d2130304008110450348a000301c40b000203c0d915040c002a6400184010080110114001c0c035880b0714407400d103001e43d05d92061642601d0f0260115503070b54440c14103480144980c0c018000151940801e0720000001d0052522140d51b00c1c0740441500403100c1310076001000500010b162200541c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 255378327 1250 255377077 255377093
    0x504030210031e150902070f08030f041401090c0b070c0807120b090105040c0e040c05030105181b09130f050105010308040509100b030a0b0103150906090f020304050c060a02030403 79
    0xd03540c000800e544034a040c2d10000a03120340a000c83c0064020001400841000120308203207000f0701c0190ba9000c100c220801c220510b00e655030642000381c284c0c03030740381901401005040031034088030300121880c858030b064601406503c202e160b01c1a5030125203801d00345000b00580144078240c442d54801c000c001600141841020080c0c2039001007408298502c0c10040000000500003070400e030300d010100b1000c24801e40d602e0703098070710f082c442c0f0300291942e080040e04051240c02c804e5142d4a00000d2060180f41c692804521140381401e6800b00c58510b50300c0d4005282a0042a403c04101c40004400c035802e601103005051050200406030103050700c4041c2115800d8000300d88001000806010320314210150030707030004070190f10740b13071040c01c00c520b00c0414000a000402c0b00382d10741c01c1441c040c0e800b07904411210100e240c02d0002d603039510701505000d008948900060145030582c5080104981c0c022207201da50010010114040442c09000440d80031403508801c502081c00040000354483e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 255379577 1250 255378327 255378349
    0x70603051509070c1a0601020111040e012607080304030212010e070e09011523060403052a0409060902130e06041b05130c020705090609040213020f0f0705151b0a05040302 75
    0x45d213400d0700d0a01c0d0200029084a6070003450402001d0144010400c104c807403040e050550310030003501c01c0704002e00060388011188100403052a400303100030224410a0000250040b02d000301c0360b82d4180215481040d007240c90510b550703021a0826001400b00300f83d80400b26810138070f0715000140f840340074800002d21410541004101d0074249014080c6004002c00c2000e0407681180e20a242501d90381d00c00d5038910500382a111119000503240030003180207001c0e4403452002800500c402c19640c03901600403c001641217100384503c11003d0322200301c0d8850410980a50f40050101e9242ca85480540c0642c41041c06d40700e506044010032251900300c290109102602d902180031031304101d000c2d08202e0180c0255001340e9005c402c00c80c0740d95a4622098106070141c032042050380340b000c0c841d8060302c00d41a01c0c0303030780e4107000030300074410a0040c005000301e0303010f401660780c0304444030146030100d00140c0d0010351b11510a107000c1800031416008103203650503800c00c1d0307103041d9507a400714458800c0c07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 255380827 1250 255379577 255379613
    0x9030304061805120303070e0d0c0e040204050c03070905010809100c0504080111090a03021c0503160506060904111003060515030405210d0902030c09010801020903070603051509070c 80
    0x1140702c0c0e4203224010003006440e04a4400d0320b129070444180d981ca0000506060420000a4101d101510f500c000c641032030341c201042030300041c4c55101020864005907001c900070392a01c000111111803003c1507a00420aa0b13a455804510340070044985010203030030012203001c0c0085001034a0a144100850500c4948810362114a0188010f0864101811240b100710741041800200e60700e40c0c00c9a02903aa0403620481290f044140e00c0000034902c0030000c20138030000500200240d0050400c408003803040c030403200f0940e907000c01d00c418440d003038500801c001560580356056240803c41210660703803910b0006640e07683ca0f00041c42401204075900008400002400240072081c080b400481c0e2103a4034041112040641001d03540c402ca0304000c098681d10714504085640501c00301c500000003c0800c1d440e940c50710300302c078000d42c00444124481d1048a200107a418081d0050502c0f40340f00302e55070380108445100f44002508002e24034001c00c0250884d904c002022030461400742c0031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 255382077 1250 255380827 255380837
    0x902300109090606170c19031a07201c03060f1a1611100c03121d010504060e011803050d050a020c0604050601030b060a0e01031401180803040501050f0f1303050903030406 75
    0x40c0d06c00313002049140e4004074082c0c21801c9002e2000c10305101d440c11005440b00c03035903060342d0b9500e802102c41c0c9040e41c0c0c0001144c242019510400c0c2d10028500140d9411940800312400c4903c205504952081c403d1603032500901908000c40c02440c0043c24441c82030801f0f203458041880f51500c0e1407000410200c6840e101030205240300c2c02d0a10040781d2140d0b0301d08202c6955000754401500c0c1c2400f85180110711503d868048030b00fa0754001e902918016420001c0c0000c1c00d051a100d405009400454160396280182d0400c49070550319143c154940c0580b2500d14003040141c901e00075010060031248242d40030441208455401c1240d18492030140000c0c1409504503e400c440c1142c01402c11480f480c072048050050302481c03880a030449502c009001014103d181000e4054a1070103080d40e84070741341182000c20701414100643c41103105a008010541d1101542e110321281a2241e00410442900182004400c0000d4110050107030030558209142100064619030250b000640090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 255383327 1250 255382077 255382093
    0x1c091a07080f180a11040e1e010f0501060903080a050405060706020306040e0c010f0c0f051204090e1f02070c180b010e032b110601090230010909060617 67
    0x8842084555000b42c00b440751005120b00c0318035061350714a07510070094650300007110140610754841d40954040f407024002d03101400c0160400d408401c0f031f01c80002403035508007aa40b030180300d401d101b03582c1a51410b07102c00c03496a0643c0c1b50414580c200c0e40c83c000a000b020040400c60703580d88806462220f20501c405a5207142c614180700c00d4807440500000c0d19031180028482d01c0c2e800c07a100045a040528141481c01403904240002070b41c0100c015010f03000c0d00c400740580c03d600a00610a440e02c513a0280002d0705148822540e030115000300d100c86c100c080340314520f01e8800f40c00034903d06000300f0741e04440b1901e409050f11408240e81e420500140d45215450803542c024080c2c608500c0220040c11001c05ca620186034076106140c000749203000c0c5610030302003036030086040a241a0341c803012200e5560715594250025440904229548100c0702294050003480c1048412000188054011140d10340007481003d00449942110000d8031800c000c20010700b0308185483c1d0342010001441c0c54 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 255384577 1250 255383327 255383341
    0x706060f03110a0323030d06090b1008090c01031e05010602010e010b01050906070206071703040807060b06161b03051009020f19121509050105040213021c091a0708 72
    0x318202c020300e5002d404690000c2000ca1005000024882c2ca10030381000d0041c00c0340205419440b80764440441686040c0001c105480c0070340c8210004042550007501c04014254203560703100003140c80c0c942035401102d5034100b030752113500700c828511142e0110103103080c030b030310301523002d94500b45c007d0fa0061b90b58000da82591a024010740da1828801c2c206540b0384034820020544034840c80c84041d006080003d0071400300f01102c4101c0e05040345417035115450741803a240019035680014020350300a403d14052240519080c01101c0e0540458850031041804699818150507828988807551a010080000100c1c2091260381903400380c500000548074201d204011041d1102d100041c0901c507141d001c0360080013044c09984c01d4550200c0c406014000c41d01d0240c0e410520183c032000110b00706119001005170540080e80514230881703840422420354601042207028024040c0032410080078580c17501d207050381c01281e00c2e42c050340440d8a8844054440340709100c0686070440004d6860041000c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 255385827 1250 255384577 255384593
    0x409051f06060e01090515090306330306070c0606080d1214190513020a0e060a090b01020a02120703020910170c06090402030a1d0106090b0a06080f0405030706060f03 73
    0x1a2180d400e0078082400c25000003003901d80b0700c0c020307203008085803103480000b4000c00e0305450f048c440040c200c641c140f4100420303070701402035002060744003021400c082600400a0240503200407000e0018a8603649241d4111940d0340244401e8a40b25039a131400b05030407105000c44002c0c40c8194440c28600d1081003980800c0f5501030340320380d90340180e5005000244c01d15543c10006070994002c041213541390213140c54541101c0d41c000a41c004503c1c900000ca8542004455106802c103c40024500e9956860001520b04011420b4010307003001c20610011319011103040801d000300422642200d03240d90124403181000c0c0c0b03031a1809401244200309078410490054400c8100b0400f03444030244c0c2d0004140c0d50700402d45002d10498010002a481442641c0045004c140c0010404000e8485240c0c2c40d00801007805032626060800c20031010368144040440226801c075a42d015090b40c0301c1b501c42c0b00da0840a48101c4084c0010032215001c01c445001d1003000c3c203800e0800300ca040b451803400c045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 255387077 1250 255385827 255385829
    0x1005060f12010f060c030810090203070e0907020a0b0c071e111f09090f0f060e07141801050703050c03030108150a09170f09060d0507090b04030c140409051f06 70
    0x280043c3c1c400900805502000400c0415810b08055030185c8480a0303103102100650840810648040208485568000707558400c100d0203440c814101c0e02c5502080703845110060300030b8215902e0038081290040500010300380340740030780d2003001501e03480c1c3c00c402d60008429405a41e0701202007a0783c04c591414194840d09100c1400d910002c0c12a29000500140c11902c6a000195903840d0345450301c0025421000841b42018030401c0313503d07150303280a408080141c80d040000340144440344401491641156207808001221001c0172a00a004482c1503019074002c804014003401070101d4440d0800195003c3c0400c0300260045407034102540008000c000c0c074114900741484945004104295603042600410b4070b00107a9074005e581c031b6070b01c040c41742c2d00e181a001341c40052900c00c0e2501c20350005000300300c161341d4205180c0c1c0e5241c10840754000c071300001d00620030202d020072481990704c2003405581b00180010401d1401511460b08000041902111240e101c440c80e44185400e482004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 255388327 1250 255387077 255387089
    0xf050a0203090114070e130e0d0908120412020f0301020405060f0403050c010807080f0c04120b09160518270a03030506040e0c0906030f25120b0c031005060f1201 71
    0x190740307407900e00c2d03000b410204030703007046c90103140d22011030040b01c0010f401c410780d8011454100d8080e0f2420a0004091406501c00e914660080107290300301e8076000c40880b01281c0c4507411501030320006070200040140c10140c5241d16660800002441e501c07028044d0103105417207003410780c585195041c103600f81140c0705013807810024850100000301d60400d0241c2d401c80a1a24100510f58030018039500f11310594201c102c000103242d4403070007001a0f1b509400e20072004041543c901c0c03a901040c610100000b03008096001c010624001c4030b645225880790340c84580184a08050803070044081c4100707117444848034a6400510100e404d00d0340500825030001419107007081000c1107100e82580b00c00e1002000d83c0720742011004a5495602002a000001002d00560f61002e03011500010915019810b140405100e0440045c500c024103030060f04140e041b4181c00956601d8010311409130348000d01d400c0c1c4030702c2e0403000882ca54503a100900218002d9000642c0c0e078250301038208a000030164095 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 255389577 1250 255388327 255388361
    0xe330f0c0403081303080c030a0e0d02030a140c0d080403020f0109140d030302072a080601080601090b03010e100501050406080a02030d18030b070504050109060203031510030f050a02030901 83
    0x111280d41000412a001c0340d42100410707855140e8024084c811840b5a400a0031044020030701d544002d0000c0300801000265803103101030004c00c8001d00ac50b101c201e0344007940c50707040010002c011400d400d000300d00300d00c0c20005540c0c0260001d4002900d41038403420640c5c0c9001c011605100f1420500c1d642590507100342080e0b0102407509000d1111485c0720003407140039000a21014080500030b40580300160740c480402040c008860301d009604007400e540001d4011400d8400141030b48000c88c0035816540d4441c081e2106a00307244603000a00008850b00f43c2540d80e482c1c21085404040c021907500302080f860100e01035250808100c26a459600414031940040c20a14016940060701140d28007060500c1110403a50102030070540c2d26070f0f40040d2100240e10104071620390b101006009480b001d0701c4821420f03482c0c41c81240d03240411107160070100c0a0090f046510720302104000440c28203440e002c02d00c0348c07503a5000c03015110190f40f40d02c2041e40100501c281d40001303016000b8410240888 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 255390827 1250 255389577 255389581
    0x2010e0d05090105040b0d09050601050616030309080d0516020601060f0903110406030203060c07150c0828020408010209030c030f030d09080d061d0702070b07060e330f 74
    0x6540e00e40051034260000c1c8000041d0b010780d503074041c109030b030020040c01404640340c1400070b9142000e091110b6080300e0500078280045228648107055802c50b481203400720440105a80d82a0000c1c0100f000554030350109115140c4081c5160141510410074010743c080f0f1035509003000703441d184040e04a2030a114000d610550741d00e6100132898116030704003495480c4401e119012a00038175003908084d4040c000e8030304109001004a00400c00b442c441c540200744d40c0c82e40c416030380864180400c040001644980031403040d91048000540b103800c129040044100010f80d0300049a000e603004202c183d40200c2d06601d10318081c0a0341d000c04c107060300a48407041007054001d85921800300300301e4507a41d40310340800c18030180b1415540c0c0c01d0301005d010000591102911b41d040d001a100040002c0e01650015a0091010407080c049135030010034241410917a5484c0b00c080e04d503500107149580310300d64078110f400001d10084419240c802e11040450480b4a40304159020014004600080c20b181 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 255392077 1250 255390827 255390851
    0xa05030307170d09051c05030f01030201081e1501090509011d04031b061a120303010902070812040b06010f081005040905190b1807032001140310060f0201 68
    0x880300166408886181c40e002e05442c40001800380f54020341e1043d2400300444104140022016003411081c1c191510070701012a00321441d104c120ba000d00340d044038400400055000314146600140ca895007101504207600b80c000d1800b0045405c941404980301541410b540c000402c2809080300b0b030b0f0440300c40d41c10090448003050000301c2c0d01c01d00b10302c20030014007490301c905000c0000300c940d00c1102001ca4030500b090805007422102440d14510742c0d6900546510b00603140d0507003291039402840c19a032070034805000a4105050540300100100180160040e00503000e602c660f04c1082c0c06050740c00e02c140010300c034070003480803c4207000e080000d01262540b000401412114219070115141344dc070710701141484101c400d60041c2c107084090220030844000e00c001e202e162080c1c031000380c0c130809100e91941c030011880050603000f4040042c010034410040d4015540c201810080590010324038800c0003a4812500c06000203290003080c858113134080c0300c9148078040c0c0c5c4000e000f0001925 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 255393327 1250 255392077 255392083
    0x1c050909040f0314041409090d0e011d060c061608130b0415021b0c01090b1210030f0305090306010f0602031909050307060306030c0501141902011416020c0a0503 71
    0x50030107407441282c0011502090710400010000c840402141612641c1c0c0317a5061348002c6040707508038451101400011a07040002074082c80001d4035599000ca00001c00b401520080100240e884014040d03800038006900c404004008441c1c0840c001c250f2890482d5107a100c1d120705060060400038160244481600c82205000845070025000c0640761918641007001c1d8040507032405940d4004507010104901c04082c03000e84030000d4050300c0e03084680d8401111602c1c042d010382409480c007441000d80e15044800b0703050f484002408140c8441d034881e10340705d4905545c2081180085c02c009400d82d11414184002c600421000000d5000d003410a08082e459016a015048086101e4103642118a110354a145c004200280580f840c00d40c8800f0000c0107040e01e4001612441c501010001c0c103035228895001c1036410b0400b6540c10642050a52402e020700c82008404545d2240030481050003d4907280c0d0040425002c1d010303c0100e0040042d04207046030034014426640a00d041103252408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 255394577 1250 255393327 255393331
    0x2070b010306020919080109030f020d02070612060506070503030a0f05100b131a040905090c010f050a1211120906040206180103090b04050a0312060303020c010c1a091c050909 77
    0x12420143c0c9920601000c00c2140e41485c1220151410100000459050641c40582c115019a490070242e0b080418280d95800c98601500700603801350408021140c410914427203503004164002c1505c035901c4000450fa500502d1080ea116080017040c4091280300748184449510000c07010f008510b01542040c01c15241407141540d00800010b207201c4540750b00910402800c0a1002e10940945030025100c5540150107001c0040385030402040e080500000c804842003070582d14400b0120104000b00c8041d0041c010100c240503c0840c0c200580000d4003411031723001d4164064a498485c1d41540a0311521b0240401c0519003161041c0405030b11610201c9000750492040c2910f080445030040f00103140d00000a007030000c9080506c000c00c01e021401e003034440e000340c1c0e0b01c060b0500c5039801107088038141e11004015034407501800000f0750145d00e1800016000d03080da44d410403034640c04440910b40459690495070401c1402c15035a44107040d0301d40300744030f503460944c0c2405003500204140c8100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 255395683 1106 255394577 255394583
    0x17040602190e0d02010f11100504120503090705010e0d050102030108060906060a060824100f120213030605040c031a0703110c1e031603021f02070b0103 67
    0x441c0d402405a024002e042c120140f0050340151801ca01075200d5209010310203005040030f038000e00903000d1241e000e260200380f620b401d18003000100301040410090100078414001c02207000208803064403001c1c02e16042661404002480000548200400946c0000008036484601203031041c0118818400c951454540d40c00700022030205000d50b00004a1080c00120200781649181100d82801c03403808212081c40b0010528500c40800b010700815000c5000150a661004034201800401c1808500700040d03111500031000f4684409071016480d50082070070312014072510740096510802c112072aa42c0101c880d10084401c894100200785420307840400c1841c03641c03ca0b410070080c880034007c502c080600072030041059806484041c8800e1080e0304090b1b450040001c00c0501039002851075000710310382d022804501f5440c075aa0740d401880301d0000100314281d045d0540c0d41c = true := by decide +kernel

theorem cover : BRFrame.Cov 255215827 255395683 := by
  have h0 := BRFrame.cov_init 255215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 255215827 ≤ n) (h2 : n < 255395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
