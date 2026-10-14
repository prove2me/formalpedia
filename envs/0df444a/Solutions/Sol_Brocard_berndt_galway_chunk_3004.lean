-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3004
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:22:48.004019+00:00
-- url     : https://prove2.me/submissions/9d1a4a0b-f6ea-403b-89cb-25f1a335719d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 540107913 ≤ n < 540287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 540109163 1250 540107913 540107917
    0x516020604230a11030615030307080f19030905250501050304020604050a031a010812040608060d140c010908070b1c0915050402030f010b09060112090813030b0709080a020108090102 80
    0x390312620f010711a880c0c018070148100c03044082c0000c1e011515184d8884102c200f074001c0010031300340d01d0380003080404089800c03000507105511000c2080c61038034090081c5001e2802c1f268507801d0100e61038140106c14414144148840b08081e17030110076814580d501481c0c49920700740600c0381030100100216056403915002c1d076016100107022881d030103840c0d08000f0184448a411098a1095440007160410740411091070502c440c0181ca410315080030010b464045001317110542207140140d170040450b16484402031065409400b4000c01460b5500050100c2d18640003003420f54082e0208005031140c84044440c1071800c15000305440145a51800107001c0d44800500300c00c08401e0825003454080e03201e81d0003640708070b044405e0422641e441500740d90b207210381e04c0d41c00104480006c0595014052105011541810000b2550000e603600c088031b8100c0865201d0041e09220240b00304045220040d410000030f04080c2e40c22460020015a0707012490b4000313042002c7c04001c6000d0681c2501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 540110413 1250 540109163 540109223
    0xc1012060303050c3025060b040b06031003020f01020a1515090b010806040f0905010e030a0206090f06130305041517150a05040203040515040303020307030516020604 73
    0x4800d100c02030356400d004040307402140d070100103801340d411440d42030318501c038400c90101092404860348000601d600030058019101c9012246a03100e002c010011a8650300b0080a120320000a4034040700c100744821030358440503017402036500b08244410000c0841c0900d00f203950488a42c02c1903c20a00100c2c100b0600c000000c03c0003108031040d20300300c1c40c03070341104801c0506620f04014a50344e500305003055452184501d401300ba0010013040040c1025005030301e408114290110b01058a0350700c41e0b00f1a0030349604141c2e0307600041244880c1d254144103042c0c00001381c4000b0029002c21000054488c5400340c0101c4046040103c01800c260085007910014620340c0e500c500c05966508003e0896044070240b00031610490002480111400c5452002e24001910400c085400c02081c132000b0b41c4040c0040d1094481d0b90102c40881c4a00320030a88a14070030399007d44c0742c2c18080d0024065482c054003ea480201d1542e842c0340156000464550258129010042428006010000b02c0e05004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 540111663 1250 540110413 540110447
    0x90203070303211b03051503101508030306100522060203030703060e010b0a03090512031e3d0e1315110a050a0905091501020d08090c10 60
    0x2030000814036030059103504601100350081ca541c00c59181c504400c031011160119414486070010500031380c82940426400195118120742d00300d25480064500b00186885030304c03450f1a1041d8070140d0308140c15034001410500000d6007541040d0b0001030b520b0440d0130108041140c00301d00c9151f1080b41d412140150301c032690100000a03101c11000351aa44100e0b00c100209040004c00605e03c5d40845400313040358400f4442a092a04200045003d002c2c2c02006841c184a401c00784000c0c00001c038019405003d001081c0070b0707500c2c0740d013860740f250f0035000b41100003896050080c84560788146a284a8400442204068810503004210400c2d0340d40c0c0c00c1080710394031070810000e0f6201c229030301d1400f03030f40035080180d45038402c000c0300703400d079402c6020b994001042071260030000c500a6000c3d0142902c5400c0040038541c582d000f0845c08041250400040c7d24400d48802c62035805002540f0041080d1816501c6031422541540c1e0301e450a40c1d0701402401d6070070003d01102d1003150f550005040030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 540112913 1250 540111663 540111673
    0x7030c06060f12120c03140a180602060702070e040f030813060f0b040b0d080a0804210e010f0e18062407050f03210a02040306290d1a0703090203 64
    0x9500041c2c11100c2c00d41c01280c4104c1154a06040305004821200c1c074158199510440c903100c20220800507000071041005000709003100210103d002c28504024040e103034010711080c54118802803810f40d5903400f240000d100038003848046840341d41107100d2079805080004003915400e09811080c0b40684000e040c0c546442c00c0d4000e00440b9821400000204807000d02558465508102074500141c0000300400c00c2001420001c900404206034040d000300f1030803500c0091300520485100070861040001100803101c40165030700311171911550407047c40c0c0703000c40040720300101d900c200550b448030004c00c3c0c3c0240065041c4d81e4803e540004c40f00e0a600402c40c00c800b10303900710060381200d60100e545002c2d02c2c030312941c409000010b82d800d14104241f40c4a002d07107903039041d03c450346001d401207035619000c020110204000d070043c1c0d400610707120b900304001146c0c501c0303500c81b041094085034800c0b461542141c0200302600c129260f54003122032001c8054480b684150021b0003013150081d014011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 540114163 1250 540112913 540112919
    0xf05070201140c01051015080a0b0a08060708010801050a0623030f01020406050d05010510020a08030a15060f02010e06151327050c04050f160e0a0b04140d020607030c06060f 76
    0x41904800d0203542c2951010b85050344610580070001f800f601c542d80021080c2000034842c4070650411403401d00e01401c500c4040d6100c1061509143d002c46421003c40c044030010006a0000d1080030303030265408004004050030888038413030855540402c6060000d0340c02510085aa0a0021810f2130450340e000315952551007901400a422044006121034034280000a0a04090161920102e9a98094403400e4410341d0f840007075030000380c1455001c0b0703a00c040c10314108000c2080407010303107420307200d0000200301c120000342500d500e1030000343d00360081c8080c000448420418003c8121046494090400340c6200303110090041c8054055440c45503d001c1c10103140e4075a8410700d441c011f0040c1d442070f40203002800b0603a03009484085100d5500d40c0001c243e120b418104c1c4550302d8103460454442c035001000144000400e400201030000e000500301314441c0c444003410100034003500e084000226540008400d401178070f802505210f2808084801c203e4581d0190000c0d0104a64080007291 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 540115413 1250 540114163 540114187
    0x907110f0d030e01110412060b270703090203100c0e04060f0302120d091a070b1927030e0a0312020606042405040b01020c061908010e070f0507020114 66
    0x40c2400201c00443e14100c00311080c8030f41801500061003c2402407440d05180010603019007036411000e940c0d070307983e4940c0340c02c0607510190000001e02482611042d18054800ea41103240c0001c1c1004007814646204c140068801140c2d8088290969100143c0b034140d2480584100080c2e03e07126521920308100400c1c5424030f0001c104c2075034000d07508290391921642c1d4080d500d001c140785c0303040460b038090410411281c1c243d1140058200220301a0f080c00100c0e5500d040c104019103a66810303901840402c03080c41d25510545100c0321040b0068000f40200c20b849401015100e00c010701042031005140d0490b4940001b000025a4050400650200c081100948480c0107840c610b100300c3c2409000310704d00c1c3c4074420702d10303820009040d100750f410714000402004200501c00d09040d801085c031105805c3d0780300400791007e20840544803e0070424000001c007200016042462030307801040911000070b9200080c0c0c500c002107814801e44c0d595550005996001c150010801c3c464000651110111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 540116663 1250 540115413 540115423
    0x30c0909060f0e0f280915050402090c040308030a0f1d0607020712020105190210090605060a35030405040f0c09150203090d140102040605031b090d020907110f 70
    0x60355441c907580540e22401000341c1c2e1040c0c00e441050802c404103c440301d0604e402c21081105d41240c0c0340c0052000742c50343d01c2403c3d029030504099070240d80d035030401080d4180055840e81c00030685120f9803500c0c0c1103541d941c1c00c07408094555050a56101c10694251002e640010302c82d410340840380301c44034189075050307a0b46c5c007003150f10030014060072900040d001621840d48010650523102d60b41480f846081104400900b00e11150031441a031100840c07103030607845904d0003d40220000309a610f0514180907610f41150320411500040c60f43e081805c0311444c818603420300e0054980c442080400c1000d51a42c0659008550f0143c40c06e0760503281c0401c01d034092181810107482c1d01943d82d9035a00316840d032007000e200840158100300110845490414001c0241328442c1030a103c0440035102100d0890b00180c0101001c03880000600c0500e80020307104000c2e05800c40d038400d00d07040c80500480ca80003400907000313008204181c0402c7c0c000e40188a1189191000c00480710100c034a130001d01d07a10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 540117913 1250 540116663 540116669
    0x16140a0e13060609060f0b030a110307020705090105030a0f1209091d010b0306010f06210c0309051618090212010c0906180b03060f031e0717010c020a03030c0909060f 73
    0x24605000050010054083c0000b20f0300034030440706580b0b10f01f00910702e1641c4010016078196540d400700c2d041c03807981007001c1c50080801d94002d1940303904100a0100c01c08043e00020f01c01c1d4491456140082e0040c83c88400c5a5805402e05845400401c0f0965071039446400c090061420000802c5100c25244403a07031450700c018000740012420320043c15215102030040100001601c0802c1c04003602071801d001000b00090080300da07003080d4465801c220b421901442000a46800c188000c0c48001c1214a070811200e440700c0301150b2802c4400348008250701c48030301c0c0141c0c0390201c0e1015551121041409829004002e20030f80c4120100204840210300030703000850340080e02c12440e5860140302c02e06640b4050031003803031600c40038100411411801c0000e40d15200703041c44522461948984080b107a40c0c28001010090304109903800600c2c00c1c0410004240c2c07500101c4000710f5400160072000c00c3d010304001074900c900e0031080f1004091360304084042414041c001680032000c41ca89011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 540119163 1250 540117913 540117923
    0xb0f06090a0917090a0e090106090c050a0207050d030e0612010503060115021b0d050708100b0411030403030b04110a05030f060108060a18140702031b16140a0e13 71
    0xc0d81c0d66032089031003101c141a101415000e280e40d4499071400c141001004402401081880f030b8969581c52824146800ca0355000d040e5140c180c100400001c81c0100902e0001c1810f10321b052010310f1000940d580901d204451150300b002e4403a4080c540900b1001100f0080941456a1540c0302013411581c440c00780b11b40b6020b031207100000240004200009107011219a01500c14401112026109219130101c216400101c10014400080080203600001d0100001030448601c0085852080b60091000035005904113007040c08009907160403658401c0d13260800080711500503000ca002400074030b5034554842000907091003500d070013101661049001642030000d5a5401d001110303c0382040c0e4440f50400030103101403003500760b424591188421542c0000507850600d0301c840002e0842500c10601513000020312903040c0040c030304d4074030740c0074100c100400708024048c080c80c803842d182d413150700201a02134480079000e9407042d440d6801405805003210395030038000141e21411032243d0007203034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 540120413 1250 540119163 540119179
    0x90f02010f03111803030904141605030f07110705062b02070c0524040621060308030601030c020c030303011e14030a06050720070618080316020d0b0f06 67
    0xc52083c0581c034a1240480c00315418482c21002c1c001c0c4044581c1c030fa40d80d05d07000911910405403202e1054105c3c4030030340a05129141004030031000110408005c200400c50200204800c1540307202d01c143d00b00703119141040100400f13143c2c2d64144852900410f078868400105070300c41c604c0802120060b0380b048101e04d420604009002c404911603880000c11545101030100018a050101510050b55255440b8400000c002c00c45403d68090341081b00412036044d200c1c0181d40c400502098002c5080d5400c010150860701c904c0d45a010041c807c41c1051b49414001188500c24840d6035940d001c0030b4212030f12561074501131213900c0508103030600000420b1600103106039101c0c05041400700064050f051303410040d22448040c10006204009019070008088140018080382e481c3c1414054003520581c1d04118006040208404d51000c5200f0309002c1840780d1400441140e0004a40a1441c00121600d1000c20108074208001808e49031040b000c010400350070188032845040222a044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 540121663 1250 540120413 540120437
    0x30a231005190b06041710050f0609040b091914010e0d050406050906041511010f0b0a14031c02011a060304150b0415030807150506010f21090f0201 65
    0x2001c0300d0085a00c01c101030089210044409400d6000d101e4030340000e01120f20f0982c59402e1010456440c40703402c2d07645c0e84282c150303002c0101a0b108154101170808540300c03103401c4c45000070348880300c0500040c200c81001404506050382c10016103070107105807071a5107490071003410462002041c60355425a15400c00303441118040010403281c0c4102104d46a40d800d0600b055030844064000d00583d40d00008100800f2901007200340c40c503262400310f603990041d2481000c1d0402d00391202840300034601c80c1441a02e030b50655403644603005503040100014100c3c403514001a20786445d204825100600c140400c0e4401070703064010000c40d42d641c000c90a0025456824414640300495000d011025105500b44850322a80c100000794000200080394016160750707860a10070107130380200c40d6004002040020400403582d020318100c04008200301c40d1801c0c60010f0442d07030840f403001c01000f842c5010314055529203461a07042c8a0a07143c01c011007100c03807510404100703003000c0903030208810421013 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 540122913 1250 540121663 540121693
    0x5030d050703022a0a09050405010647070b16180b1b011514030d050f0d0e0105040809130b010509010c150507181401080f0402030a23 59
    0x66003040c2d450307801004030030705a0a00c0340c030490314286038503100c80c0307008030000d004eaa4140c0d142e80a404402c2d0300054904091600c40c2c00c44259178025483d10001c0c008183e03590502c0d01c07400c20045030030719400305d404185005003810024940301200c000c900101b00304081c27282901c4210b110346424034224030a4400440280e500e0303402100b0381c080c91000c040041c0042014900078040b01500514003114940030350341c0d0355080d61010841ca1500b0414124100001c06010042421303420b016030150a100d145d0040003400c0303100c6c035044401c40742c40014079035602c08200d51004c507629445000802042c1880c1ca04080e50740d02c007031102c80c413514040714288a40c012903c602e103030012050310f5440c81c041c0d4110054462a02000c0291200c0e242410004040003031801840e00c98030482d039442410030b125114800e00b20800c0e4101020307003500e0210304440390360003102203a004039400d03080038940d96582c4006440c105100400800703141241c01101500e03c0ba90502c1000c001100c016560031503a1a604 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 540124163 1250 540122913 540122917
    0x4020904110309070801090f11010210060e1902040e0112080c0109060b01260411190b0706110403050a0206160515040309171518070807050a0e06130507030209120705030d05 76
    0x8d4000e40031658008001203443c240d0f9644800c042c010398203000d80e100c040c02d00b200e546501c0956071760101ca00b005002c409001800295001c416011804d16040032030118000005006100d154032503528000144443c0c0c0702590b0071603817510028402d480039440c100c0080c0c0a4001894046030b800204003900b1441c039607021602d8042c680300d102040c2d8a9440b02c00842007c40d018603045500880c2d50915040006500c0000d04004d40e4201e0b500d010360314140048070b50201c40c00c401404148800c0c000988042000c0c2c110039011101070b5201c021200e485a100303000200014120710459107005150740c10054014400c40c0651035542203259592000b08a01900b0350504410b40c000d2230b20854000d040c280e0454021144c5c01903104001d1504d90868600010b50300300f040ba0b6449040b04100360f1400c1030002c0d0241c0007040da1440d4500301003012406010300d6107844036045454400103042d45103e41e0583c2c0341107400508032599810101c04a40c0c030b0345043c2c06054000d0085001280780705010f941 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 540125413 1250 540124163 540124181
    0x2030c120405030d030b0111240708040b130312240e13141c08090f15130201120609290f0111070f151b020102190204020904110309070801 61
    0xf010300148601d0034001c60040107102610f030705004400c80b4282c10b454042044030342214a82c030941c0007050940034601010b510040c482c0040021a500300030000d40c101200e81e400107a4649000c10407020352800f40d40798241e04228000c4907150220691060a9282d18809601c0c82159a8036959449400010700c440040381c0d00039041c078000b0030200005e0905070980045102850603614a03002001401c200c6130700c440d0700400010f08241c107000d1564001d010f40d021440c0d504c0028080090000066003080324001d06207080950500720361015a4020640304500040048003040041c3e124804103004003241540e403070005201030503a011180080f44590340300400207102c0401c5000200045035128000e0080159134020000e000400030321103681a00600740c01c0103004000c0c200f402008102d0b684950b50f107150968500901000740c0d801280d2030180345d403042d45091003112540080f501909c5001300c1160403030b00e00f01c00c4075510f8504c1c2d0040c5008100100681c2c640c203541d100000e00341c2c0d003120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 540126663 1250 540125413 540125419
    0x5090c1507060f1b1e120b030a030e0108150f011b05010c0816110c0402030c07050601030b06131b0f02010e0a080409060b0a080a0203130f0506010504110406080a02090102120a02030c120405 83
    0xb1701c040030f50194441d444242d40044d80420102891404642403401d10b0030110003003200804510619a001540315500048020303051060b500d1000025281e0b0150300c000740d0500c040c140600a001859030040c440158000000340301d8840c101c0340040c842d5204540007000707600c0310425140d6540c41580c15040d8074162100500741c3c1080b00003000700940c8040e0140c00150401c010304c40000d0b009010701070003140500706603100b41c0780c0394080c8243e40112840a1a1f990f10b880d0241b0728800e00c1d24903104680b5454030b4403c8540000200682c01010851070f086102c0c400d0001d11030030000d6000081059a10742c80050110f9580ca1f030b1019101c2c05440000000b10b0441c0c0c00080e00e0541c0c036400303958080c4654803640300f03d0840d51500007001c45006820703940c0b5003002d03006000d1801d140c01100344101d5500c000f503150501d0b080c5c0003880b455000c2c00c84c08809400081c200300507032013042082201841a214a40e903104940000703960381d0f01c00d4907806a54020000401e243d1040401603030225030001d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 540127913 1250 540126663 540126707
    0x90106050726070c0f0504111c2f04050a0803030c0a1812080c0c1c0605130b01080706080105010e01120203070903080c071805090c1507060f1b 63
    0x21030b0106249a1072000400d1540c2024081c0c400803d542d42c1c0f102004010010050401034240f0703040c801905e0301c0c90380320702085504100c0b1894054010000ca129080c15040c0003a104a00c508034032005030354140c01016007030464a5240007075503014000e03c102c0300115000da4219580713850803074981c0403c45000042441c00d0110651040c010b0949100b07035840d191146440c0ea4480a1500300c0f24090401038400d6070b03000c00c0c10044103500708030021545408a9000790020300d841404002056600d2005242948603004940800401071001c2071042d40540311740c1440d81c544281c55035901551180000003071360302d000003c07654090343e03004070101810b070f40e90440445001f41510282d400a0501e40802102e0000000440c04a01c094609180e01202030030925141040d41303202103190742200d01d40d6920b0442802002d61703001504500140c001da542d11840340ca10150b11025026083c4060902802e104050081e01810b07407111801c0780000c1d03a00c240c44a44007a040300d05007102203003e1404110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 540129163 1250 540127913 540127943
    0x62d06150a050c1903030b090103201c050109020102060f0f01030f08130902041d01050a17071701060603050c07031d0f04060311040b010518040504060e0115050901060507 75
    0x4044000d06001c0710506007189010f00e19102e25142514003600b400c0e011184042d84410150705004201d12030b0340845130398019506648619040c119002d2000c00001c40a4802c89866207508094072182c602050340742021041600b41603029040140b0708a0041c041c0c100045c11821560b0401c6003d980c04250b0b41d0440da0075a03484140031010703400280d448d400d00b8000b564107d0a0508503c01030034900034090303161880c24842e80c4113400303c40401c005043c3c1c080014809911520050411501c400c410020403600002120341030002e40c0d0416907103011406000d0385941c805401840c02c8425541e0200940c0d034480d1041181809841d00c001e00103000c0702c44c0088d009011031141202860001c0582180410f880700103070440d40c5982c8100c507a004850b8000450b032901d4480c80110302d800382403480c03400c00740310307004001200003125440c451a03030b800c042018400260b1001341c06103010002081261a1000c5030b5403110315510400d4401c0798040004160544103c0984411b90350041d0750b00000e80b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 540130413 1250 540129163 540129199
    0x60a0b0909060d02030a030903060617210906180307060512070807200109060f0e03040306090309030f050a2a0e0c16030801060e03071d18062d06 64
    0x7901074a81070b03008007140c0e1043c015980601994031146c0c42500c80c0c0340b4040c80c600d00305003542c80c1c0d540885000507411032000ca801d0800300d0b107500300e0503001c400b040c1d142d5903440d4401041d00580d80d90580040c000301c1da0121140400c1503614102c130046080302d1005a0340c00c01211644191400d480c0b401c100f00010070b01140c0280c0342d154100f900c0e410108042024690000000d0050320b030f4100c0c1782e80d194a1000700f403101c903100314034089021000038048003410400d0f555507441544402004136903240011001d05d40f040101780080e6034030114070fc10144450030300326550402c0c03c0041d201010400300108a070700010095404000d444a1803007c0c2e01d10703000c429115144003c10000c91074100b045400c02030903841700342c048030300d102c4d44582403a0b50500303500504d13500100507440d02071384c010311051041818a40c040c0461001c030009403445a17998590384403d1860380c0120391200e21a103c01e00425982248010511461020b45250003110f00c4c0b0018800200655529800040080110740121 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 540131663 1250 540130413 540130429
    0x10e0604080a0e1f03150e06180705120c09010806030601031104020d0204081c0906080112141009030201051603051005121204121401090c06030f0608010203040609020108060a0b09 79
    0x4030000303201e103207080e81c50b0701108500628441c44c0320009036901c4d0b039080e100c03030858100ba010304540c5032090745525100001c6908844500ba40c51204e214040000e1031081c842c200312000d06880301001d50725400c00b035a220056410040311140032031040e0f0006003d6043c00036055040325000081c00c02003920900c03d010007980104041600d6035000c20010070800300400c80000000003800c4801d4044030640c10040c00440345800c024100b110203001001040f200103041c1181c1034110325000070000403000120710b1b182140074558403040c20480804207158065100e0391103661942802500c00fa01d40100b1001c5a20440b00c45503a4080318905000c40d040c0104103d689460250403034010741140c000d1050f40d90026401110000c00d071040310020824000e0b500c0c0c1c0c40c0302c08140248843e4a180e62070b604038040074001c00c070405580d00120180c004441d00400c3c01050303680c00855481c101030904a02400700c441d003c0e400700342c0c10720104620782408a1000c0440c1d2a055549040c0f030142c2c41084a40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 540132913 1250 540131663 540131687
    0x151801180323070c03020418080d0c0306180518010903020a060c0c08070b0105011d21030412150c090e01060315030c0e04200d0809030312070c05010e0604080a 70
    0xc4514452803842c00c500000202403490107010408189440e502c100019100090038410900754441c0703008000078040c03400d0f95280458000301080110306240210000d00b12503010741e103407000c10804422030701c00ca07902c8a40141c500b060401a240d0028907064203071480048014010781c4004801c101054055000301c030700c000b441c039040650341107907111a00310b50003210b0103858100644004020641e000741750644a001d40e40007088035122402d00080c0e0001c1503182c20f46001000e80c2c80786510003000c1c070417140544620020150001298200815003c40c80d071400e5014900d0074061064203800380d42d160007104c2046a03500040d82c03c00c18100e01801644982001e460390500300800056204640a005403442e0036420201c0d03d82800c203200c0c4000144aa26004070190394000e01c2600e03034051052074103401664040e501d10489000c070785140f01724084511054900002d000c00103600100036030071180904024016203002c088019142e01c8140c0e002002c412040000c0e01c2c01c0d50044a480c400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 540134163 1250 540132913 540132947
    0x41101090f0905180d020706090503070b09120c030d05041a0309071512020703080603011505031e0c03070905061003020301060909090f020904060b12060405030a0513081518011803 79
    0x5940d460080c40c6045c1c007000c004009a0425182030000d990b00414070801848110b005091013480e000845202c0d1081111050003402c03070042c01180c002d802c200d040b450190103000c6505c6a014054001d00325040740c000c41c881074481c150844054850b00d8192401641528060035010303240071700c40024985100c03401c009104001c401846003801138405402c00e80d019840d0062149820800c25007140c41000d00301e5114403d02c0340c180320f10b840005106050b031075800c41032070004a4071810030345028030000c40c2c0359042c4102c1c080402c0b00401074210601270342e02030b0740b11650300305050400d805a0200f40103010000713001113410045121990041e44500340039902050100200b0380100e0108081203605507448c58032203280c0c03906400c1c0b048005c10b074a90508050103003800c01d56141030b100e200311100082001008145441c1e051481c00c1800c00900c42e02c001c5400345410320400f0102c003a001c070b4088032072810700342c02200c000c1d40600401c0b50b5078085150444003540381d5034065410040340c05400d62 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 540135413 1250 540134163 540134191
    0xc030403021615090e04170c030f0d0608010617060714161b0506070b061315060903021503041109090f0709051b0708030415020d090308041101090f0905 67
    0x101d1400000707000b502a0a601c440b080d080103440601418001d0785902c41c3c0c941e9549201000085036021050303800400b4030041c40c41c0d4030305c495244030307207107005031a0100740e08880080d01c0da150640907071010049030200d81c02070001c5951200000c18241c154900ca03c2c903908402d00040c007841c405c00036002282d111044079170602244540b000191081c1c5941100c1c45140c9030030100110307440c0b8080c0001010300f1140da40c0b0740810303565101a05000a0038490185070100c0b410a507d82e8981c00140f00c0240000b082c1c4541a5100c400034010111072009034041d040000303403090241484d50450f4407a9411040001c02c108400707061290400c001041c2c6000307400344c1403e01e5109801400603800801d8a0354000c0f034903041c8101c060440040c1014880e05090080000c08002260482035075405500146405201404000200041d10560864980d00c5240424907410550840e45442c0958040c241442c541d5001000648815005008090900c01800000c105d5a003441e00229408144c1e480c40390 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 540136663 1250 540135413 540135433
    0x120a0222060b0a02030901030e06010b0d0b0a08030c1b06130501050919060215060303031510050d0906140a05060a05040b03100e031e12070c0303091203060f0503010b090c03040302 79
    0x2c0258002d191a5030042c0c200151401c119a40340c040c1c08010010130015002c00d5141010022651042c600105039490302c1d0013041c04290f0f95503030b01100801c000e2099035600c1c0314102c3c0301511842c17644d141202810114105001d5418a0016180e0045110000022041c145001985c442d001188d405511101029041d1480c04071844071000400325074008140d891955061030540e0a0700808840c009d920510803c28075442c4500100711030030040d5580c0700c1155401d1000c9690b4401c01d52520141e41c20315264030104282640082d000103208841621151220052a42a284182d070215400144441e050040d86403940c0034944244006007201c0007480101b110070165210b40107940740c60b810205900c0420407810140541507000094943d1828042950303080e0303e0307807001e848801000413800354502094003aa00403403030309030000e00000d455440010005e01808050191043e82c0c1d120120005090405004c0c00ca60403100a24141440d643c6025801590308010415411440b40000b84 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 540137913 1250 540136663 540136679
    0xb03152802030921250b011e05040b030709050601030e1b090c0717090d061b091a27090a0c0206060a0b0d0c110318120a022206 56
    0x1000d41404681001da00c03480c1240c0030134140002c02c031000c080009011030f641240c122420031a50b0b0308621241c00c030540c01d000b081c4201400441c43c8000c045030502c0780081166603c3c0b1020071942500b0381001103105441c0e074140425036035001c12041d0583d100710b41c01e020100c1660441c81d400314041c50700103040703100750303050302d281c40c1103900603e0503000a9003480075181418902c00d6400040220514a0401256140380d413002c01320320349844c1440041217001207550b9281088000503001307507060180c0035816105c3c034041d4040b843c2280210f51207841c009000c1d4425508820200c031310024990a01c030540041c1c201d100c01909850a03044c080c80204002d5a56103001d41d8090503400c9000030305c1044402e00a858040d0180803c0e10030640d900b010003c0e0640300c011a00e50440f440030210319503503604410b4850000f440c050740206c0c04041418004d88000300c00f0000c4000c8110f07004680e180c4145991a10360065040181d0010601c8140e4112656841f0f003c84580c0300c40c00001421640e52501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 540139163 1250 540137913 540137971
    0x30d0e0d06241404060501031e0203040503130e06010f110d0e0f0306091e0307020a03020f01030e062e0509130305090d0c150f050901032412050f010b0315 68
    0x103410f88104110603102c1070400348a1000500802e080412415072000e9400041d00e850924007105d445d000070004042000034000e40d10440300d4030580343c203a42d480d0748c3d8200030500100c1d2158005215001d20503a2a4807070340c01400510620750241840740c0c81d01c00d04031242d1854015140d08542101d42821050f10200040ca101e0501140901030386041d210403102100184a80a030440c2d005100075405a51820801d0040341d81c1250606d22620740440103034041c05e110060b6004034014201007180c0d0a4001425003113054640d107064000c01000c0b101070700c0240150140c90782000c1641c0008403254100c40d5040500e40c0641042800c01c01c01100180008000b2002220a50800501001074420506d074500140d509810301c000c0500c03c400004156005503c0d840d03040684503409141518400b031400180d5144005105440c140c950860741501c401c0c2c0c0768202e8151040346605240c1590601c01e0b441902c200030050015400c902485040b400c001401e215040300c180c4154078844428588 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 540140413 1250 540139163 540139169
    0xd03110a05010b0307060c05120307110d1d0117040210180b250f110a0b0f1b07060f140c0105070e10090515030a0e1902030d0e0d0624 59
    0x2002040c9042d5003c10705003400c070154003c2041c803541850708400108c0100b050401c503240305807480d807240c0d00c05108075021038040300042071a000740c4104920745540007070008030ba1107034240300d040c030300c411800110303025040014000f17019030414000c00c0043c645400b0250030f6408500d48aa110345108030140c80c4645154003114010400040041e0400743c44190f15142c124803810485109140c0d80350f000f001844404020305d045c0c0c100d07013004165604d1b09140e001805c2c00303485d0380f030300c0382d00d00b5404400a5016007042c0400e00024000e0031007000d0700144042c2510319941c0c5003180322290b1141514800340c10040044403030803d03c400d108145092049a1144c103090340c910280ba0440f41c24000b00e00c0898030340e00104004880c0034083ca807208000e80b542100048507941e620303910018114018000b500d0180c1503170190200780f9504100e411340590f00907008a055400d281800c1c501034400040c4c4e2001c15411090044520022401c0c0da8014240b000d4800007840350910b10030001c10709021150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 540141663 1250 540140413 540140423
    0x3050c060708071e170703021b19030606050a080a120e01022a0109080105060a03031d0402160b0a02040320010311030a0204082a13270b09010b0f0d03110a 68
    0x200a0700074000b0a00c8940403482c41468098900072058031f000b03445076203480c1c00551101f49aa10b00d55540c490480d0005240040d0fa4003184c1c00b900e03494030501a050510900e4868808000003042c1d4603008a481c0d00703003036800840303001049103088040e607011032890fa2250640c000d0101c030204c0020548a000c1c01c030f200580e600008140040005007495a0302e0300070709007030380c0742800300811511941c00b07542c00c2d2905400c2507888100c0149a0258241040307050030341240c00841da540b03510f07071040070341c1c14024492144011075660b140e1300a0100c1c00f071407101500c001c0c40d450036020140d900c04456514501c041c500400d0480e114a94001c8650041d01e8241c4090303400201004091420b1040d00d450800b100c0042d0700d40075002c03041c44980c0000003211403181500f00b100480f881c42c075a0000b80344007a90781004c0a0a0f5800744081064a200c96055540818a500089010b401072040c904803400003400c200b040000801030000e10200b206d41141440101418904407413001c01c14489100c2c412 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 540142913 1250 540141663 540141713
    0xb2a040608070201140c07021f02062a040603050a020d050708090c010206090309060a020f01150f0b16350702012706120609090302060103020405070903050c06070807 73
    0x8002049008002d16660441e40b4110440801c040762040f216040130001982c90b4407481c490000651183d501004140c2018500800d2181d00d034002c6910341c4185109044a00070105210200d459680c60340366540003d45c04100601c6810b0095000b5500601440001818504a40300107002c860b41601c01e180403414220420401c14820010601190428405040030f03042c40c2c07800b184d5a003e0f000c0030394410000850001d540034402c124410804c5640402400b0072440710040b155201c6403030292410b000c000f0071000c0f8580f0380d1075045984089055078444c4507004141c441200704205003004c2e03440c5444400c22080c00900600b41040f0f462005412159100f402d40300140c08000e00a103840300090704000d800c0c00c890216451401214200d05120103501c0e10710200304000c26540d000000003030f01e00052003003416400a00349050740c0c401e540030404c54540301c3d030581f1555118880284283d100c1c000710f034803505000d8040e0201912801d48a4144001603942da0300007100500304212010f28 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 540144163 1250 540142913 540142919
    0x61b060703151406031506070c0b03161d0d050709110d0b03060c070b09011104090203100b09060a0302130b0319050f04081803072d080c09040b2a04 65
    0x35002c080b001030501550000d08008060040760340340c0401004031298000443c5921480d844c0d071b45c112100e041e4040500402541c590090100540080c0e4002104411507005d09a010b800703065562811000e825407000740d9000d4004002030100005811502402954000a03417100c1c0b501035580e840b0203c8811311345034104908e10000f03d405480c050703407007548100140011100c142e0f046500c9650000c411f0041070340d031140890302404080c54840c01c010320004000600400c05c1d4080d50243c08400c0300c0000280c1d0700c10b4100418002e48034515401001000101c00d0180258018060303081801e01d030850751a03072a49085d40c03a800031107010b021004140b240011030343e01489090b074800812001e41341d203424107454020080c0200074180810104410b80c00007541d504001c5c000050103242007a22107010f10740700d0714881b52120b45503111180e80403a008602c49002040c0c58840500c007401c4000981e4450300c881e640303040042c1640c002c1e010062408440b84885415040c5035980c0608415613481c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 540145413 1250 540144163 540144191
    0x111090111010c090501050c0712030e010e04060806010b0c0c040617061003262701090602061b130b0a0203041a07020306010603020a0e0303030f061c050c061b060703 73
    0x100003401001d00b079240200c01c0386000e800030601e034103881c02880c00c2c0c3d1702c4032603c0320345502d480c4840e00140907550303030400c0305c508040d801018048200d000b0390700e005031020f4450030701060b03070086d01070143d5a800c948014800b13104010b010300075901c048c004940050f014000442d0855080f030304065a20100c042640310840e604124141c0c02441010085002c20700c0d50b116248155442c80515901800030b4691a4036644000c041d02e40c40a4504c01c82e502140e41503000381c0200320005491804100d900f00002003290001c100c1c90720136503c1c00c060250f41804410001a00da004c8003000e0491161f2183c0498041d4035580903180094464004540d20390030200800b060485c0043c1522612100f040f070000182c6011a6541c1118420304001da1221990f070800e90340010000006a0144804000c010200c615401082d000d46020b0f10000302d101d240f010b152100300c00001c40030b0010750040000341d60500f000310042031a140410240c0c00405400d075621814080c0035640c600000f40c50340f4000c220f0a0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 540146663 1250 540145413 540145427
    0x160b130f0c1a0c0d0e040b03011e0e0d02030304081b0f0709060e19090c050d0b01030212010c0504032402070b0a0c051c05180601150e04020301030201090314010e01110901 75
    0x1c02c40d5203609040720651560360b9000da11a05500f0000300428400f40354440c2d400400b02094010b0003072060742c0d1030740304400e0008a00c2c6090b0b004241400502d8522a4001c2100700403040c0c50f40c0554516030300c4d501e44546a500c80300030891098001910210030140500040a000c45000003604078603240102400540711160820f40401d0782640c2070100c031141d00301e0022807910708002d01240c2c12445d801c0002c2000802e41c006a0000c0740780399640204800284100d06913803003220000c1904104006850072609074803510408a202040140040340c81c0038a8020b10b06000703510651303400b034081d80650a0307800c110821074089003a4001e0005109503405031040d101c07028900642411041c5a000304039041924001404a50b2000894550041c0e044800303001010341c800c544495030741d010582c850707003880510003000481d01041e2829a1600d40200d034101c0c2d4050b034075010003a00b541c9580740143c5804402810541d0f80d071b200000e00220130301825604d80082e035075141c1c41f001001e00240002d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 540147913 1250 540146663 540146699
    0x1111902060f01050904061b0201090201080f0402010822080703200f3c03040f060c0803070e0f032508062e0e1f080102160b130f0c 58
    0x1541041e82004000c040c00100c0c03a0444508449001040d15070b4100600101130030000c441c1006550004503254903015000047c40c0c0c0e100385d0b5225002e9403041c901c3e41084405490003400501001c0208500d010840c0154140d00340c0c01c8404c001401041e07446004a42c840700040b00410295102071146221400241003405a050050000c01c213099502c25150161943c0f00541044170800c0025115a22901d640321100e017241e4100b00781c071070344801030703640c0d00184244004005012008600107200b444001d90b042c3d40513544900b1902e9041059a02100420269410803100310b281ca200307543c00c009d0408071300411001216001e9441c000007810800d07503003250711142e024030148094441c4400a900820001c4255184076200c00750480e002021917502070743c1d0315000e84041c400040f441c2c07841c04010004880b940c8000a42d5100414282d01075041400881446c0002c10008034580d0300d84290701c16208074004c800c0f4881070342c40a0000da10000241c0d00e84034841814400c050f28900340c0905 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 540149163 1250 540147913 540147917
    0x9060e0604021204080a0c0f0602030103050c0307030c0b21041202010e0c0108060f060f0c01140a06031a0703020c0102040e011509150c0f0611090a050f0a0b030903040305011119 78
    0x1821015003006a410b0f8000b41c40140700c42d00004061500368800c03000310035507945c0254015403458480c100300010f50401c0c0415a102d0040d041606464a00018600100ca50090200b8503a501c1c180c1da110340c80d0003a03400d4800c400006449450782644540e8500c1c0708500c103024400c94a130341070400a085407000804a03030b442c1d0082c868004142e030800e0a00390f11200c00c03140c4903283d0f00000b0200b140d60103007600009400c2004030f00008001419002020246281b0440014640e2080b60b500141c99203403201030403400b01940341942c002c41c40e4805561110003400e0151a040042d101c180c22a44141c4c403040c0002c0d040c00060144c40c90000c0d80ca04240c1c001e182c8024028100b40c010300d803c0881980140c240320091002104021054803441000d235044603080240b02074264512803a81d00c545d0b089882203000180208151620042d40c2c1c407402006805401d10b1410140b40c032045500107011032a1520080c0000800078800740210059003205158254442104003c2c0440d002301050845017 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 540150413 1250 540149163 540149167
    0x3030f0f010303090303030f06053d0905040f02040803120108120301050d0b1005100507060b0405010e0c0307110a060504020306060d0305091201020409110a110a03140901050c01090819020f1b12030409060e060402 93
    0x1700096000c2e1490701928800c4600053f5080e2181c200802441581e01800c0c40d8000825030502034110090b0050481e9040ca040c1c50725641082c909203503e100901991380d01c1104030008502145101400740d80c40000c000303e403402292200000780c061001002d1800001d003000075580c041101c05c0c01a81c20060095606100c0d5506003820a140340300c00a020001c025800300020702c1c01c51040c502d17050214049001c3c0d5240141c1030500398040d04044409078003e200b4a004210f59041107030304585c04580595682e428001424104107081360b8400050f401ca6400340404a40240b1501c11a10b0b41075045950b41e6882d42918400341901c21009071740880c3c2d4012140d100c000c26041120b14030500700d0181801e5650380b4440060324103005031002400c0c1986041008010400440010b05416121035440304480000c0c3c0012a035500300b1680c0c2e50b20b0303604074a01012042003d0214012030003402042c114107000c0080e5610314580059100040050300c9010801c0781107000080507030003840c1640c2c158 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 540151663 1250 540150413 540150529
    0x3120901090f060e0c060c0709050c13030602030703051e040201180b1216021209040203061302120405010f2c0124030c120b0712020d0e03030f0f010303090303030f0605 74
    0x40d45030030281c4142c1030740b01d0b12240003e0380b0301c0d03407001155035248833800c2c5211020344a08110307000790002c4502c04007091411020800c98102d02c0101650120306a4405000d0743e11a030045400320b44428801d104103040e00c001080a80f0111301070a28210317440c035130345441c2c6080c1360a60303920050344000c0025500803a422541c0b9002110407a083d21400362005a035039240c0c3c40c04201d01201d1125801c20092012626452110303000c021240651b001d10024402c051600b070151044840019120560340c0444411104404149011442d606005000000e520507840401942005164241558101c140b14180b0411007041114400f92464000842c401c1440d69901400460040e0014040c02680c8200a0714190560100e032001e02c0501028014040f000b007900307a40c0e410503034070041c40b402c010700080d03c0082800816070407aa090b40da80da404901c0c43e02c050b0001c00c244c0320350b401200d0b100d600104240e00c4024140e03080c00d8102402044504804030941445003001104201383d0b0022103c01c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 540152913 1250 540151663 540151687
    0x302130b0913020f270406240320120709120317040c0503010e100b0f1c151d0f0705150c07030c030b09060a050903120901090f060e0c06 60
    0x4040c1d019201480140d4544000700900e800340140380d119000c11081417200c20a44454400360308100c2c0e0192004e00c2155250b080c91000c581d001401580304068004501e0041482a00b041181c00100a64039040081512800750385900c00d00452100100e1070007803101e0180c2c881c400b54002c101c014000801d00314140d400910710210f40049040c503c0300e100114060100c2c0c1d110100c01408003c0003003000d1004c13a151640c8542005603445e028a180540360340303840c1080710081c414a0b0740100f00c50503000d81c2031000391000647c100103507080c950901c01800040a00d2043d01a800040c07001c44080e005419103c1d0310740441503410b6142070304054030402a9844800c1118240000349449507200c450b807170350072031030b0400030b900291650030348910001c24031200c415564004e01600701561016030340c035607460b0140c0f0ae0035130318009140d10401c601c0f4030b030401c41d007000d0740c21501d5180041040401901c440194810f000c50a42e1415510010714020366400c01a111110358243d030110f042c80f10030165 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 540154163 1250 540152913 540152929
    0x501091e02060d091104050901051603060806040230030423030d120207060203192012040f05030c1b010f0903080309030c03031003060501062c0303090d030302130b09 73
    0x196460030f9140c4c03200070f00300403211708120035070280a84108120315003016004d0203042e096455030543c0d40092284038407140303c0c0c0181d00030b5800c0c100050a03985c032280c4c00d100100d0f8850701142c02c901052000390001c051013034464161615808000c40c0c035035041040703102c1c64010b10346815100490b0440c1c06009600c01050000c0c0c064407508054240c4420340700703000003a02c148a0010061440001005088000c0585104103048100c00030062445a000754424503416000c00c803503d03141c2800b0140c40f126003c1003c1d6400340c82903100c442c10310f031190f580c907245810440b0031100f1504402100709005400000c6001249402d103070020400b03425020242c8010150b000240c854800080010640c034810000c41e10320b910340208490b680d1910074080e0351000c106001c200c81c01410301000103140c1d4403401c00d1005803e04180031111108090849008500d0084071141c2c05000030700c81180940d89220b20310440a000c1d27100940d83c0c01902c5e081e02e0001505412a031340c0e10105014403800c50700c501c48 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 540155413 1250 540154163 540154177
    0x90f02010804031b0507140a0b04140102071502010c03051006050a08090118050a05070e010b03011e0302060f0c010b240c0a05330405030d020a050909040501091e0206 73
    0x3040e4a20340ca990074104d0300c00910118800c54403c0c00c080034410044002071030802c450710700e080a9000300c0c0032410800010114072405a860400307100c04e21111070040009442468140101e54100341d42e000c040c201d540c1169001030160750b4030100c080e40940c143c01540d47c410b0741c60340120b803e030f0305004000e4140e005002d0a102048000d8000600b11002507000b486205220603040204901d01d142181d0f58250008044840d4054040e001419a00c0c2c3c080350380c1a01d4001c00658150303828400c004138204141e0600f00d03004403140c0c4001016071907020041c41102107408200d50354404c95a506400d4030311702d0300000d005121002403c50741d581001401078040b58014140781d6558080c0d003010303141100008020b0f100380a94440c40f0801401c0810800c0002170810b01080124085118100f051100719070262181e0000c22800560000a034000e012034480750820341d0402440d507000c608103031001c581c22991695200b1042d000e200020b0851402025010210340180703106901194150160030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 540156663 1250 540155413 540155417
    0xe06151507170f090114070209062205091b03070b0a1407140c01090503060f040b181c18060e0d06060506070302010b0a0b040308070b060d080f041503090f0201 70
    0x80341d10420850050424464401d884500a48802c0c81403840d8680c1ea015690300e5002c19540031400401a50381d8080d20525a002440d007035243c0d54480038440d49030030b01c1d1042c5d45000000d41400c0305d00c50061245a00460498004011350040709214080403002c07a42d03c0c0d8820b41c000003081200480754400c40c2c0303000040c0d02d020310760380354510025581381c01983c03c02030240c0004c4428030707020800000d000341d15001c240e0350340c0c0c005642c0e101455241c90054484001c0c4006001c00500812085100729400841c0140061072308000982d445003000c044043d01c13310442c4120b206081940e0106008040c500a030700d9018825184c000058a50070b54010280e005071581d0320001d050007600da1051001300380240800e82d80d0381a92500170b00901654094520032044c0410201c0d6130b980d00002d5070103595000c11181e02c0c0101c42c1c1c4482c808000010162035005038058560300010324010080c0038040300b0b20303451684450828a6684041d07800400c1d01c0c040501d003c080703001040000315820300658081c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 540157913 1250 540156663 540156667
    0x11010507020d022103060d020d0b09150a06050f0d050319020307060f0b061c0207021020071401050c07030f03090801050603010506010f081f14040509030a0504051513090e061515 78
    0x51022400f027800810018100709207000030010800c1021540e41c2135545904005225507442042c0c040468a10b8040d540c1c1200308000f0324030981c2810b543e003841d03240c0610205c90500c81b0034074080c0500c5031070f0013144c00141c1003c5014010420725004450380c140006406206801408000c00d07000d000c2e00c581040c02e00d11005240725610410350464900d240c0182110640d00b4550001501d44408400c0c0b940074103041d01c004008000c00420500d05807110400008100c01c1a1801150f29800c000301c81000d9001c0e00b1000000502d030740d4000c8030841d00c02d84030300811618010384242142d070010000c5009906113010450030380c2c1d1003461400c076100603003441c3e240398070b442d8079014601124000700d40c0e20200b07004010981c8030300d0f80d002200b070300c00c111014081c1d99545641640c403030240b80d103500301180092200340850328003140c0303802e080344808006500f003102c050340f480c44480c081e41c4004441903a900045500e21030512020b540310000b00311103410342c22818085100311003460361042e042840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 540159163 1250 540157913 540157939
    0x2f04180210050a091d041a04110607110d14150915040503160302010b100c1a1308030412030507020d1403150315100509040b01090c11010507020d02210306 68
    0x94030341d0001901581c42c01e00043d0842c540000e0100030241d9041c1c0300d00c078055647d800300d51044d003a298031655000741883c000510000c00d00500e134100c10030458401c80b069038014565203030030441d40d0f20389024103204040d0b9510b102c0c070a030030540612003030700382014800c0400c40d00380400240301200c02d0030344110048030340d0341d0f003411415401403240411a40c2d203203a0301e01c0c0c2810303415000f84648180445114200c00d40004e0280c64019021800603c0510745601c0b40f1601030032508101d5000ba4224100302c544492580c03854065402168111801154400c0140f80150b241c810181d0040c0d0a000074240841c20f94000b03032403503078148403c41c14000000700284084c68a0002e00d5201c44020341107e41d8070011801e14a804001155101458001401d0000303862524441d4a070249802070980030b007a03402c00703401c040500001003140e014043c140c41e4105200000f441030a00c50982c940c09040a0b00400318000d04118140a001801104502d1950324144601d000c990300010112580142615 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 540160413 1250 540159163 540159167
    0xa1208120703021210080f010b130c051e0c01050f190b120304270902060d0b03010209060408030d0f020c0714030a1208071121072f04180210050a 64
    0x10441c5080d4201c58406424004c5c2101100d1002d0180c81507181a641050001c0c42c0c0e081c00c80701c140756103950141d2110300008080c10154000085071900345407091038004407468018038103070903151130354105a000481002085080c8592500007246181503001410b001c0410856141307804d4005040c0c541e2010120b0860303440c184d24001240d0b44c54180e9031a25a58000c0180c0301142440d2605440d00542c11116082c182d071040c1c2c0c201030390080030766040c050b0f0b03507011030000c207100030086030035640c00c00c0201c0050750380d803010308001e00c02c000c0103696460324600e182c016070b100c82c00725408080c011b00541e040740001190520640300301d003c0840c00c001c6004000ba10b400c950400107810140b050561200716036001501900c1303034003180c0f1a1726001d4500c12285a484000303040a80c9010b285440c41203540044c0e10003001554003843d40c858401c461120f025550207004c00f0420010072440a0320009424103003c0c609000503500c01c003481c00030315900480d080c1c500606a84082003c0010040c4d2240c4c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 540161663 1250 540160413 540160417
    0xc0c0504020c15090307030305090a0b040b0c0d09060b01170708130203030418020310060c021e03100f022104110d050f030c01140105040c1403060604230a120812070302 74
    0xc1003841148454280390310001c1c1c17a82c0c8050030a80c0004d00f0007000840751040043c400360300d1540652a8a55907a45888040301c9290207046090064000c0100c040102880d010300005640500c1001610702e00d00c00000d00a601086410103113a101ca0f410002081e03040020164051444256520048842d10020303080d44503503000102103200c0d4042009103012154081c40c454580b512501c0d0003d512504186d58500c040100203512481010711517a1100034600b021400c0600603007102c10240c40a204034041d45c0340f54103080d441030741c0403820329845104010f512046600b02014100b00c0c0c101600e45001250f41860000d004071041c100c42030401c101000480d00201c202416641c481c01035802d224082c040620a181107801c60900110310307232810740b040071030400558031141d90000980390091003940004043c958480f0b020310001800040703c4081c401540b81035a0488041c201c01400c02c4108040e070b4011428080c40c0c81e80d20400648c00d4000c83c0d4440c102044600e100742e941c41170880180c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 540162913 1250 540161663 540161683
    0x1c12141603020f130306050603060105180402011808060916292506051603021204030f02101104090e030f030c090a030210020d020d03052809080c03190c0c0504020c 72
    0x2c0c001c0394000044c003000361f0026015441c05c070140c1c1d005998907020402040c25018070800700c40707028008035005600480310041d8019002400c4c202032a0f45c2c501e15410007100f00c48000c4070b80c2051501c1020005c15504610140900308100d5903154160358501c40e070b2941400c0015200400000c1022100941260220b821042c50104c2d4200c540c0c03600d0840081d200646250340c1800300b60590140c030134024001d40e50a880200d030102d0750b0795156182102c203803981072072003410350161710030b00028000d00c1c1c002c07140f01a510200b510f66032880c0444c507404641c80703180d42c19203640050080009085942c0200c83d08003451900e0b06882e180c044000414952450f0302c002c2d4414040b0a4002e00d8640200d4a00c620901ca502510f0065855400680c03e59108403000c0b2a030014951801249034420140902102214003001840740c03000c0e0b456514580c4050907a542c1a840850700e8481410740344031180c0c03915601d1500c0302254000d90f40300c46170140c3c03901916205940100d801d0146201c10003c010360 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 540164163 1250 540162913 540162937
    0x712080a0c050d0908161a010605030c030a09060920090f010f0303080a06050307030309092a0c0f0b04062f1b1f02040501140705070b0703021c12141603020f 69
    0x4041e5185803031244001c4807019108500da07607c00000303401e4001c0c426030348142c00c0b4141e154510b681e0614544e004004a0104450360766030b072109540410408010000c00d00d400c1c56000764101d000d4410805200002007880e00d0020f40d960043c04100300e030340405000c40303905042c512003a07110322804202a040c00d400060f0507101d41c18000086c076500840401c101c80007080200003d43ca4407510240c2c1d481c0b4003400200640115483c100e0640c401e50031015041e004c1c009400400c0c01950b601e003840d1200751010345100ea00d81c64079240042704000903000315907150080844a0030481000d007420301034040c03607450201005180709031524090000a00c40000490300d4000c1410800c00c50300250054002d03640010031b00402d018010042d0001c4903036083d0888001c0003140c0c5030091010a41d031002204408501503c8400b40d01c0e01c07501d4110f00b000c0d603900e031104103c0b0b4000544035001c40e42d02e62001e2078986076400912050f1030018103e5000790b0041d24015a40302e422001d082c080e03206580300009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 540165413 1250 540164163 540164197
    0x40308090f120a05060a11090a05120304050a14010905030a050d08070c050f0d0306050d0b011a0c030406030e0c0d02010e011808030a0504170309130218060712080a0c050d0908 77
    0xc0244c0842d00d24426884204e01300001909444442c3c0280120304810b03070000300c1c0321800d0100d4075041c501115900d003c0700c01c80f4074045d180c0000c10403400c402c0d4007c800c0030700d14680700c1c8480d607004030300f4074003508096004107610101501c0d1141c0d5400104080824800c0d0710010501107841403030b9141501b9049021510442c1602c0204d0f6039031003c0701940e0300020700d03094011490345412502d902910343c0040c081c803103a90814202c0141e04a4000d04458a5041040703c190282d4050000c0d0000304a55100010b2031442854061300341300c4005645481a0781031188540141e8000230000038005081c6406001c3c40e01c1d41c0112a00c062036034000d141d8610020030007040c01c2c1c0e408001042540c0d100843e00c0721018061071a00d0352401a451071030b501540c0c60302c4103c4c1030100c5034007400c216a030321084805440c07086000719090340d01c0120180d07544444080f40c02c1038540c000d4240c1744c1044819204103d920600d1200a12501402c0c9401302c0316911040740c40140040300b000d8a400e01980344c0f0500c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 540166663 1250 540165413 540165433
    0x7170402010509090c0705010c020d211506020d030b04061505090d1b030c0f0f0b030c090402042c0702060a090501060e090601150503010803180315150a0b040308090f12 74
    0x4100d500054006c50301c549c03c100c03484062038030100f424003000c1c00c10385429004180014049954482c3e02040407001d035640c1c072290110101c0d0b00d510307900409464018082040380e1082c010103030707181417103424003907401e00d00d040180c2c000c0541841c4940d040d0389041c4c0d4030344e1840800201f800308000006400000b1880017880d034100d5014040c0201c80c85441c0031144285e1b40c107164154103106110f030000150b4142c504114146003103004540c0020b9901c55545442804070010301240c200340c01142d100300120b0400100c0f510303038444010046082c240814081c3c90092002591204014092441a07888003126410407a0940001000c0c000626102206150900d4541c0d6201d02c248a2507060724440c284010b4120301883c101ea058a880601a614240c1013043c10108150900426034040c41303019a0f22411010a8080601401400e81c1d00345991015004101410b81142c00501801b40c0822080001032084421503007954030540e8200910060740c000500700e90b620710185a018040c0b84444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 540167913 1250 540166663 540166681
    0x20102090901080c0a06140d050c040e0103060b0901060e03070315020c060a0f0c0503070207030209040c080d0903020f0f030a02041d0f010b010810050907080405100f021308060717040201050909 85
    0x240c3c461a000351140181759586840440f00c00d22500c0030500502001c021055505046801441d4400c001c0007020b8035160341c0300740d00f400d5204240c3c02581c0940d503902042c24030745802c480c49c500500b00c07880e041500e8984407001940702c0d4407070310004154003081c60990310000301ba03030141c4440000c1c2c0801c0e0342080c81c00315100b4000d06180c0005400c507170b01d010300000c00c1c1400780d02607a001e04083d0b401402010309590034446030241c060000c1d14103200400002880903410045809500300e1942e40304412840c610500030342d2140c101a140c411101101e802e0783c1034500080d01c0100a404403400300e100b84040076004822014500044038034080c1300c04407050810150007400b250107080e600d0844983d00c01480301004a02402260b6000810601184070a44910225038005000b0710a80310304070a45c80e440002c846404988000d0680c01040074a4a10b4001c2440c42c01444004050311641c0303080c0350003e044041100100c88800c030301d03002140c00c0d64031440075035890303100152518106091400310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 540169163 1250 540167913 540167923
    0x61819030519050304080d09020631090c45030b0a110d020306040f0501122001140a02010603050102120118060501081302010309021302131406041502010209090108 72
    0x80a00c0418403180320b8001c1c280320b081164840c64002c0a01d90407d6040d165100107007803942401d0741d01c200d0070320444050001100032802d42c0303140326080141156080d210f50500c41f50650100002070301c1c20481e41007043d0401c0784c4030142c040c144c1121112603c41407240e402c040031401e001521002030405600f011070102c002d04180d9000d03085200b441d50f501c2c418413098030207400c1c10424500c81440400360140042e0055500880d00901c0030405003c004540c504640c1d00341e121482007a1003408110500503c4511840c40140381600c0307071260040f80c00060024107040070212000100012411982c40c400c0d0b0000020b5035000000355601c1c110410000003d4100380500c10703258014801810146040d40300c3e1004492041c0c550442c95503422002074600d040300102030781496120300e110300c0141d60300d561071102001e520b0001030700c55040490781025103030150002c0c090108907403005102070399400c2c107540c100c0d182843c419240c0454038a08a019002d210041c035001500c0c0b2001150111001c10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 540170413 1250 540169163 540169177
    0x8010f051807120809060d050702030a0e09061c0807080313140f0c040203090f0609010e0d140d05040602040e0709090f0204050906090402120f0304090c0f020618190305 74
    0x200c04149103400081c0107032a42d040340300c0d1441a40c049804000010f01c901c0182c004900018617480c10704102c24012420307208211402d00060b04001000e032911070b000f520303989240b80d00303450201e41441d184000c5071180d142003001c607410403a5100440c0412040070125040254001e40041e12810200c40c042040754023060101c44410260500c010038200c00600700410b01c90b07000081021207000010b010087d40003400403407103805a8507684080c0304d000c10649020f07062040000902c0707490007404a003030410181c4103108000e10024400d1006032580700341ca14a00650000048c603481c2c902d000d900030320071a40b045960075041741c01c10094a404c581800102c035036a0b201486402d01d110951002c901c620300a030b50b804220030010952500300003d140e5440351010f008001c04140e0707403d003e4649203004800c40700641c40018140b00580a03401003a40244aa0400900015510300e001c2d40321040140328034549a4801010350313040030304124240d600c1500b00034101280030a802c0040c15507000709 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 540171663 1250 540170413 540170431
    0xd0507150c050d120b0307033002060c03070c020a0e070206010806060310020705010204030209010b0316021902060702030c0a081506031605010f02010b0418060f09111908010f05 78
    0x2845255914000d040348558594010058802d88502c2001603410050b120500c1106568031003c1680d552810171018008e14041c1e0074907041040b40d0714640c000c00822580000e114500040b504021a4001a08d19080401c2100d401d44951315204201c400301000c08000c1d502296030300000a114505007103ca0068415038291100350ba00c44070300c240c1e1100c040d60910340681c8640c1020300f030100a0760203006050312400000d840c0030354a40001d00400c10a81140d00c20110001c00d000d00c0f0700128100d1450300103e070029250030301021210722030661130038078042e0192000103014811588e0900640006100040c100441e03d0780390000141d0b0b40668450340f121b100544408582c3c3e074a07000031b002e124a00300c80041101141820011600c4161b05d074140700c01e542d04c560307461300155240c0c0540e020003840340820030038000c141e003440d205882c0c031781c0450f210720b03407031300c540300005c01c64030b6809003100141a91844201084010030845007042507200c61a903502e081b0b004018400741d60400f6000300451 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 540172913 1250 540171663 540171689
    0x408100c0f0c020112060b0306031c120b1f030209040f0b060301150203120c090109090c0e2b050a060b10120f090501150612140f150d0507 61
    0x4400101129a400d091201045031444100c0030345114181548070544103243c9401403d007102000c0e01515590b40141e50005000310801a503824200400148001c1c2030081045107101842d02030203022003400369415003030701d4240750050f907112814000460540c2a1443c0040008404002d00a400032401507100741d043c1004e0710b1061615016400010100074201461646005424011000e4501e140e41c1980402e0103802c2c3e0340b44100441034894004030344c00c039a48000300c0340018040a216040740d0445407600101d4400036a20400100d00e001054507403010030511001e100540d44400d050341000386659071803c00070080042141e4840303510505060000d22024010410000803038103d0340c000548001c060044c19101c0e4100e42c200140500d03002610300007070b485183c295001d44000507098074286d10104403043d070100368183c4100641c001001000c11004100c20f001602500c84501d0000d91400705800e107031130ba40301d0280385100401c0140100b0040c941941c603100e5a101e80700c41c480e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 540174163 1250 540172913 540172933
    0x3070c0b060d0c050d0201180e0103052103040f050c03010f0b1003020a05030c031b191e091404060b073801031b09020f0d05060d0302030a0c0f0203060403050408 71
    0x2c40000074059406220014101d041c07006000c3c0c01c0c16002020f80c1001100366a41401c1c0c16603000540280842c40c0c0501070a60450400e1032403c100d0241200b144031040186015003080c44050301d4100350b02081017604087d55090443c900b09441040d2941075103405043e40740b488060b8459420028141c404150503c280b0300d00750100d006143d10107000c20800c00006600e06011070045500c202010703100242c903251040e803450290808510718440d140d4807007098001d0b50f0011b41548184030040000d800050310c140006040312050321801c62910b0400c0180c0b4200d95454101e580506200e400081d10394141e070900381102499410781048140140c054580c03403100c100d680d4080b44040c0c030141079082e441c603a80e0098032105070b4481d4188034407034180071030400502d00040095291204e405032302c89044060600c00c6a5015024510170500c2804600c00a600801900c142841d01e042a0036690b8007801d0001020b080208029411b019400c204010143c01c64080c20607950080211f54170008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 540175413 1250 540174163 540174169
    0x20d1a0a020703180803031f1d0a140c3702030a0f020d14090d0f0309060e0d0b04030528030204030605010b270f0904123902040209030303070c0b06 65
    0x4114050451030350000c00001e4200d07031780350100c0c004001401c0e030964001e55071026944206070142c9c1c401c5804d0030081052182c80c1000cad0089040e5030980b59a0302c0020f05155450741a140300341d0040b0403005554007280403403814269641c2d100b0301042e6180c0d004003e10410002e4483c1d2103203815001040704616100100d510006055060fa2415100c0d041c88101c580c541d0030701c5030415420b0315817010284001750001070286804c010320601c00d440d000d038100d050507005040107a8003400d00d8083c0b200004200c0200e00c80b180c040d0340007501810000e60f5211100e80c1c241d200945020621b5510212100d0b000100340d159004004807070142c00100980d0362070760441c1c2600d00c2805d000c21a551021060008071800d84540741c9074800f401482000f00ca00407c011920407030040742d003034809132500100b5544140e0084011455000b4860011031401000c0c01d10001e618100c2d400c2c800440c05110100d0215107403541102d03c45440107044036160300d41044010b04604203043c1c11a802040e01001c150641 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 540176663 1250 540175413 540175457
    0x2090f0c0901051602100e120318090601021e0307030305182a040f0e0c0405042f041b021606020c010c020d02090c07030315050d020d1a0a020703 64
    0x2408211032903282240c05401140c9907046214100c1041e480d4182203001681c40d421240051070300750b11030035564501d1200b0818051000c41c1a151260020005440300c00006140100c0200c4100d0b0840195124840101e2a1901428070b05421161100e40e074540e09070f000000e006810700c244d03024030035a0b0b500780354005d05500c4450425a41e6208028039a101c0c440d058000c0822042040c1204c807005075800010705851100011030612a42c641e54295411070500203448541019a01440303141025540d1011042d085c2484110720a500141041c002c8103040029200c060000c000780076416026a15070b0700c0b9484102650058401d281c10100280b2405203403100311090b42c0c01503c7c014003600e0055520841c0e04030100da004000707070749000060f5100d003c454050082c441c0c0c55070700c0d01440c0ca005011150303801645a0b943c10380e0780c81041103541c3c2c2100001040e42c10740b0801c00f40c3c0e0325883c02a0040d485e800c1a9040b411503502080f20040d51603000e00b9115000340e866426960300c24160103000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 540177913 1250 540176663 540176671
    0x809040915060f060c022e0c061b0e0918011406010f111e031306030507080c07023706110c010908030a0e2704141902040b0102070e0903030402090f 65
    0x11071707000c050407130240c51320a01f09030700020795000150b11041455118180c0c1b000c3c00d144040458004201e0409000d1070740708400030a514003500c0805800144405024052928005441400c24200154900400442e442e0000311810001d22140400080120703140d84103c4100c0d0018207250403841d9810301c1007030710000782d140900107018100310a00c40d50705135011000c4903010902c001c026000c00c484440218030003c000e60341d0002640c1c01c200038001c0420b0405020901e01031001c2c050301c0050f81d03405036000201c014400c0080800c0700101c183d1b40e001801142840c0325589140710001e11203400000705184001c039001660284400360b00152605000e50280e0704441d4400d001d517141300c901641604c844514000c0c180068400007000602d40c1d4150400944120309110003444100b2805160816080d05910b01904490880c62424040d91007084030283c400e60b1150035070301c046d034000c0c800803010b000410203241892801c1d0610b50f54030b92065404a000c1c4440300001402c11441c20805405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 540179163 1250 540177913 540177917
    0xb060909032a0703020325172509020d0501030b0a02070f120c02030313091d0a06050a021b010506031b150706022109011104060c08070809040915060f06 67
    0x10540c2800b040742c403200d60b590030442440c0316000020002d41e40411038100e05da28686004030030515001c5500c402e80280740c0c4030112a408009041030011404a84402c80b07411a100c03c103080c09510502e02018002640038052042c400101859000200e80046040e64011180c58805403162440b9404034800c0550140680400e0710420000610700000051110314510b040590100c180c0c000901356400340e604000710703d944d10340802031500940500c0301800c49130b4805203505c600c0e0105141c3c840c0307440036001b0700c0b90342d80d0000107010314220b60507240d04503054802c400d601401040d816000b0702d0142c40c2e4071f120f44a1a980c04001c1d00502c1a80d141400c0041d000b0084000392251192043d00700341c801310340042e001c0c040c0001d018a401e90110b540c080740d1041224034104000c1140c211400113040200040c81040103101c1203803c5030340e4a440f2980090784c2c0e640c0c1c07c2c00741407852450081008842c7d0141c10100c03204180b015955040350084407a00040100356a80c020101e0301c0d031064421080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 540180413 1250 540179163 540179197
    0x201020f0c0f040e341401090e060d05071e0909080909040f081614010507080c0d24180501030c060309050a060e250b2a0a0b06090903 59
    0x143c1c2003d820950110f100002190f05120f000c0c01d10030072801c000c5000b15101c0c203d0080700c0c8100041d400701513004258008004c0210080000000d00c14100b41c002c101560142d42c0c040b030f00c20780b29111801102d03034005040d940110303116070258410401c0b1181555485d0302e0345801003403000541c480c0441d505c0d400b0380050320700803169040c0249428000d006503130307007848a46604003180c0c10400402b0308424122241d55500c1d03d6207041d69091202c415500040d07031502040044c21608003480b00c0d00007001465554a0f0f64281e21040080c0c2000d01003202512804502824100d5a4100c00400d07680980c40082495040100d010102d039404d20028045009244007005a103000b903102281e01ca00400584a00e0000382d101d00058a00b4000055120f80c0003040c1c020410000d4400000903507004104542e05503d029080c041c5c3c1e0203118406070740424003507802c00345928013412000075810040300350f904110f01800c001d6000301081740c04601030500640050102c00300402203e0704181c480c40380074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 540181663 1250 540180413 540180439
    0x5030d0c1a01030f020a14030714030c03070803090319260903030712030c03020406080f1f080c0310021c1505060d0e010b04090512130b040603090201020f0c 69
    0x190200140c41040d00d120346202040400040c040c01180d01942c0100403021034840d21344148000380b15a07a011403469224898030605656001c030b5040b0485c3c9801c05a40d11500c07040300080e00300b0710300f0f00d82158180b0a5440006810700080060406c81c0c004400b0307540355803980345410035421400380c00100f400c421a0040d01645074142811b1041e070984c2888541024049008a481d541c020841941d404010115003540c10307505014218518400e4075096003068580400984990000760040301c41e091007000081034581d5071401100141c00c04000d4141851ba14044551144000f040c81801ba025640d03c4803d5154107000f04c0341415180407600b41001c0008404400501d01d80e07644024168100c840040c6903520710b006400d1078091b400e000584032880c051201e00716003402110761300032803c2c155013001133080031a25400f600c0c40019426603d0766500b09403101410b070b5400c0030300b5495020902140e03084d4180d1100e00404d02c00c1c0c0031103c1110880203070541d1420700804195204510300120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 540182913 1250 540181663 540181667
    0x40303050c0d0614090c0f16080c190c060503071205070903050319030b180f10090501260616030b0d0804170d030b09062e0815090105030d 61
    0x2294410081c2001c0380c1002c82101258054420030782c05804100c0490080103050324001130b007039800400c605910b030702e81a160140075100340540210f511080301124040414020b88900b00d45610301e605041e6a51001070060b40b644002001070180c1c1c3d246000c91001c10500c0c00340084170f0051041d40c941d103076503550010342c40c4050040140080c0c01c0111150001002407000c00280020031222042014120210403004080301c0c044150740380b0900c0d004e40c491030030360310b80d40225070401824101c900a59542c2500300d005407142d64001c00c5558030744400050054003010b420080f448061806807103042e40b04075a0b075034902003980c1c3c940b04030100314031240341d2a0195100d003643c13040107412103040764219129690140c05c2503200e840c9200d462108894800d60902125070034245504007001070080d0100818403407200107044902070704080154925521600c0194001e56443c142c2d0380c074050364041002007030090141c64141090b5584800e5202c58035001c19900e0603a04094000c1422405c00082 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 540184163 1250 540182913 540182921
    0xc170a15110d050c03090c0f09040615030506040c031a0403080718030c0f09140c0909060d0209161107181a12010902010216050f040f0e0318030d0f0503040303 70
    0x124040c000010442e201d161185805080d1083d1040900c11345c8070b1501c1031600342040318000d0500d104102c04004240c1960b640c102054005d0f412040015002c0182c0002001c0d030100c94002810b50700c107000c00c0108010300705004006403441001c0300c10503068041c2c0500541340c021b46000380070074101c00009504a2059503006000c81600650400c0c55a0b20344400240b107090b0b4100d1284d9580d40c440500a0036000d01410200c0391020031401001e20b0b02c6040883c0c5030068500c058480c4040d5000728400750384003620031325280d4000b840c0100f58200646403103080320603055804041406c0340c09031074507981c0c041010402c4800c40000c401b07074002e0f0424990010101420803451100740b94480340c180782c03512200908a5140c0600008440c8492300029103000800303142c60b144d00e018240280315680300c0160800211000741c90208416103014609000b034010b04521207580e12010a00c490a20007101d42e031240100140e043c1d91500951601c00c5481c2c8040e90305003004601d04001040c0000d2203030744 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 540185413 1250 540184163 540184181
    0x3050c0304021e0604031b0506040303020709090303060b0d05060a0b030106090b030405030d0e0604140705010507060218190e0604140601080718030c081603020f01030908160c170a15 80
    0x2100105107001c0000080310741d0030031b40040d00d2103802a0601c2807c0003184c1901400390608668440c145465650001c0da118801d011b100c4c01035448011040415010303170422400b9201c4500c000361100362440d010001450200da0180c8541d0040340000380394030f15082104c0c10784020341ea80485440c1000c6490f040d50b40044c001721894402000a04078150541c40b03622044540c181c0070707065903302400e040300c0b080c01440c0c101103941c1115200308505d07070b003000031190345503400000540c07075000655908449020b003407100380e000017805c44100c21600042d417002043e0703002c2855020140d142d10f002e000448a1b01452224000c0c003540201e680c80d0f004000d05035022243d40b42180c45c10400880080100790994401c46080c1030b445000c2c0a0800306000280000d038081103102141495900041c00312620f01e80301d10305040e640e002d06818094204101d07003c249411529404d0404181380841140c035140c810b88a85828801c014203502402007004d0290b140c100d00d2108410b500b5031452401464420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 540186663 1250 540185413 540185449
    0x70501050f160305040302120601061d0103022b1401030203072d120b011509030204050c0f0319060816030b15090712050c270a12051c03050c030402 65
    0x4404101c040c00b002c6a0441c03058030030740e0380e251218a10700c1441040313003040400403510340060300103000060b0303c040304041d010b102501c072414001c41100180c0081c80b903012a81036400b82c40400400d0351030410400003030b004850310700704541c488407030421403e080300303006c001e6040e0010141080312141842002000300389104d0342ca150f5041d41c2c2c4003080060715035401482004d8440f520300082c080d0a0f600c1c1401081e900d0365070240d003161283d00070091087c48c00028031480c1d488011036845444032098610300d100c0015015640e0402000d00ca40b01c031000d94964150600b4000f010481100100d040e4078004809110760f041e003070555407101d80108004081d00c59143e0a6a1902c6450341c2d9030007801e0058170140c1307490459a100041c480d0540704000c03c203c13503502041120501e1844035003943e00d0308281d0f54060003011a0302900240300c080070b0b6406210586441d2007080140f02c8045004041108007096462140c0955402030b01500c02c111901202d41005100140240c10300790b02900c038910010f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 540187913 1250 540186663 540186667
    0x30b13051203040b07201f06121109010f061d130603060b0901060f051611060c250f050d030315170106051525020409082505070501050f 60
    0xe0741000c40c2c2c0044400761160450101030100190700410031021104411980c07983c042c0c049503416a44000ca0960182c036072000c094146071814150307220b01d0140801c000e405403031960a00f448644c6140c0b002625209400b200e000243ca0142155550120765150300c500c19207803101499880000c500354034640d0040d00000c80d5841c40509445410003840c410701700040c3d12000341090100316001600100140880c0014903c000b5800100752140000000c0803900f40141a1500c0c83c07180c0d4041950980108000c202c8a078240340105680e8400d000c001101c0c04134000d090300c00c5800c00703202d1180794941c03901d0750014850303405c11105e000d0703902d17000341004244002c140c01002c010103025031240459000f5503194030450a070030f0290000814084502003250000550411043d208090000d0f440140f07aa5981c0c0f08015080791000015800400412448016080c840110b51101c01000222000d00e011864803003204008041429007000013868030500701001500e5030b07407140355222001442 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 540189163 1250 540187913 540187933
    0x309190807050d080901200f070c08030f070b13020a150e03060118111809060d0524010806101716080109030318050d21141906030b1305 60
    0x204200701041d1803c26540c018007854219009400c554980c6078011803c0d00340e0f84c0b04030130000c0050a50f1128500c0061545c6d0300c101503c1d00500241040d8019011804045280e4410b000040082c0100714020a44410170381e036000c0c04d0004803006079000a6110b20102014401c1c1590200044268045030402d030704400c810100103843c1c0402684201503580d03001a40e01600c142c00d005407001740700010356440c20030070441c82c005c40c0c11003d000e01e1070140582800080b05903503002c00c001d500607041800e84d0020220f040d0481070144047c0c80c08110500400000a000c0031300107642c900c50058042010015402c15010741d0740580b000c4060a0644210f00e1303054421070428132807000900c000000040c280d2164070700034013075500358401c400c07070a0003810b04071000c00d03001300d4404600280341c980460b0540b1802954080d0809101140301c41c645003116401c4d00b150420301c02070207062000802c10b81541700c03500e11416183e042c04001c0c2200e103a1000300d40445107500c03004020714440c02c183d500b1000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 540190413 1250 540189163 540189173
    0x307180b040204081605151e0f131d180a0b0405010605061215150d59031210030b07080709050f091303030b0a060e03060c0309190807 59
    0x5c411103041c010040b00b174101700100d00d02074400181c0c2d07007018040a4100710100d07181001c210310001505808410008488100c2482901100c868094180030101103d450310500801000000c00d24070003e03a121006c01c1c07641206188501c013403500c0c0c000402c0165660b07564a080014081d00480c1c00f51340301c43e4007240681d03e13030340075000d10350304d90380394401d14500b00980030360405a24a2550080d01c6646204c1c06000050044490340640c1e08804200d0b0300c071064403081c140c0e800040301d50822102c0e420182e1a640d01c200019111031441c100d803040b1a103203481d00100c2c40d40c040158503107680300308030351500100740070616039000c0180c1c3c0444007401d50b2500e580c11921400c651050000310321004001132290045100e00c041c1030159140c410300010f95002c61200c0f50003400e48605103403400001c03400c1610a4010501c8100e025103022406a82e0b618094000c0025038116803003030182c900021a024900400e032441080040d00501e03100c0c0740510003200000c40b2900c1a9203840080041030701103a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 540191663 1250 540190413 540190423
    0x40b0f130312170f06060a0c050c04020f041715160504080d05030f10030b01031e0c1701060501080c030a0917030103110907080403081501020f010f050f01050307180b04020408 77
    0x1403648440c600149003000c01c5800754002030104024050f1390782400364540302c2c0c10035620100483c0c2007446100c42d03141406843c1c00090449607510500028440380c06c1e100010250044511100b903c00c3c0c03c0d840d942c03030070345c0303e485082c02583c503045a800011805049038102c00038441c91401c002d440d19444804203030420140c2c80b60310f40452000410322450321a0280580d6004100a5225150905541d50011071040600c00030704034140304542d42c012040c1c4010062039081c3c1c0141c584840994a284104140b01d10800400980d440d07d800083e695000c6c1d0382051007800101d2002e8030315074949800800800300450241c445103010b40d5208050b040c044015406503005050090840c1c00c01820002c580c540107054404005014044c880020b40040e055074016103400d1010602000c0b460040f45401120b80507078840c1d600f41511400030304a1a4401809002c00d600c14100503a201c005042d17503000c1510420f400b221105401d60310100c201e034462907464100400261403d80d40d589540d1400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 540192913 1250 540191663 540191693
    0x150a030b270d0c080912060f0708060103111c060e0a020705070603020a02031207120906150501050715020d0b0a030510050f0106091701020d2c03040b0f1303 69
    0x1a071040c0220068101c9150000103034895240c0041031801d62149008200305604400205100c40c0800c03600a15954003000103c0030410300c1c200c541c41d16010400d0384d00c0c040c05a030b0351004a62000045001540b0a02640c981ca80038050311528102c460441018008075109240c44030310355a840118402d00d85078960303400b88266a802603220021402c00900f803018950051050610400040c2c08050b00070007a2829640020080700e0349540b51481a038810071400480b80030b03140784c11001020081581d00c540d0514038210320500d107554503500107464522a5801c09020261108841031101520360000d000340381840c0c01c04119811700e00b0106042d4040750300200c5164002c25200c45c0c1c03540c031503c40c0c198400c06603550000c49503d4280040c1211800340124090304108004000f02480250100c4284008a840c20050004000c5d1500c681b2400c5c00e13001e813414030b004144a01454400020707a402d685201303840d145409030782d241615017580807000b84980c00d10311000c00408203404940c08800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 540194163 1250 540192913 540192931
    0x30a050307060e07030f020d03211a24130503190614160e041401030b010302180714090d0516090b032406120111190e0306150a030b 58
    0x1601c1007840d1150644400c02d000668662201400300049a0030728095003696406407640b1001800c1810304441141034400c3c0d2443e02c0c480b0300284048c0940c950b11034951000502c0102100e500da82c5c00708407003c1010005250340901d15426054024422801400c200080c02c0d00d48614540d03480101e801c1c00300d1060b0086c40c0d881074851480034001d0714001c14070324907055005445146041410131011402d0901e412080103030360360114416031556885000048401c04002d24990703544c0c90145e440e0351090001720b0007a0929081c04d83d4154050820b02e0290420707071034503034100c0036071809171046401c10103485a1103034820074072a010602c1480780038211a050012507a986041c80d1201054404c551041d9010b58045000d180c100b210072180d25260307007819410394805882c0e5000140c40501a0390826040754a03140e2000c4140f90664002e040b04101307070005415004505400b130311026240305c101a00b41e044040099840d00035507480c181241d034002c00381355203561291500c3d0b4401c4030850f88924 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 540195413 1250 540194163 540194167
    0x321180d0804150c0f03020a05040e0406020d59060601031a06032a040603020a1b050a020d02040213080102071106042d0b12190c02030405060d0b030a0503 68
    0x51000d01c1d201c103c806100c0090a02400824540050034600014050700400d41d0210b0801c0c44240b150f4102d800030600c0a5003190603007000d052510080d80041c2d12000d00d14946182e48904401080010741021a4840009101c080038501d001909100d003401803000440041d0450140403601b0180c001303c10311000038116490400005002c84100300c0328612818099407003241d40e0b540d010100c030341c0090380c0c480b942503a00911f5000c0021140d09401011071031000301d030200d01550f040c1d003e0120701ba625582c9248070320f64a440d40f0710301980758101504c50703000280044054140700c0504205544058070052500010417101c0c1402d100c00d130030191490350006403007000d00100301101150304004079841c5140c07924007107183c11441c41c004001504030203c202c62454a50025906070002d082c540b8604bd41c1e18140702c611000300c0c1b0112207001c1440c0c0c4440080c109d00c02e152184140750003068005515080c106410401260055a100c0403c5074585c5944c0c155501d051045200040c4104000c40d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 540196663 1250 540195413 540195421
    0x30204090e100b0105030c07080f090d1511040509042901080f0c040e06060907020723120601050109060e130e0d020d020f060403050c0a02100504170321180d08 70
    0x82c299070b01c44a105040003024018090410000d504a0b2000e56204048955840d8404a26101401110040c660001d80510f601040c0103800c070b1642c050b1100b407a003c104800440c071a0034400d0160f802010b40000c900400540001c10841c20782c42681e0340e21040300d40041d2902c800c1600003c00741c010010542020b032190495640801c007a2043c804111002d000c0c0d543c242705496a10b00000702228032030710100c404107205174001d01500000d07050540070341160100000d07400010040d203118080c001d8030b04080000e03040002203100c034141d8005a55003a82e0a2030b004048402204076903155034081400040c0003621000c0c2c2c401c052044956001608c1c5c4001541ca0203411b0010b15103d4906541081d0601c80a5a0000c115164880e03410b0801a40780d4151290b0700d8508424210f000350030064048094040c9034111010f44100d41068071504448002c0d44a000d845e0b001d80400740d490340810803034500701065010781c110390209003280082c1a1110050905e858140c08503c0c0302d0115480c08140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 540197913 1250 540196663 540196693
    0x20309131d0303060d02091801020a0305060a05040c0806040c1205091b0d0c050d0c330504030314030912040905040c05040903230d020408010608010f0902011d01030204090e 76
    0xc203062031001d0750540c900800464034822104178004d100e41440000191124002181c002d81e00603514000c40d20740c201810098010042658480e201c1e18844500190921306409a03c0650744903545001d826100c6800340005040845011030034400403200b09011214544203031071141001c00020072201c06a40b518001541050000d00d0298a6030242c41000c070303010000c200101e0b107050320501212101400d003210354881e150000d1262410b4010fa40c90301c40ba141d03814a030042140890710620404001003510644243e22005011500303040e1810354140305000034652113000c000640b85c0d10140700c00407008680c00364200d00310f16642d89050100b03200121220002409050794100103054040d00e0280c01e4000030500040000c114441c1480302c00f5404040ea01c00c243c1c000030554584c8c0d151440103010f03014a0190107000c1d1302e030141e020282c200354003a601c4516010384a0404500c503801034034500d481e03100900390515808100c0010400d1052246907500d034541000303048404403196030f03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 540199163 1250 540197913 540197951
    0x180d0815100e0f0a03120806040209040c020d0807031a011d0907020a1a0714090d120509031002040605041701020f04030f0209061e010318020913120503012402030913 73
    0x581e400384204040170b000150711085140c082c042141441da4603070342d80d800060042c4c4240b4030b04507001800d08846c0c051903030700045e000882c03104c5900d60900355a50b21004500b141e1a90340340c4c0c0e80c1e44118000f09401035020b90303002020781051030714a5950a00243c08613041040079280d88006070300450724581400002149070042c0f0300385520310003403400d000000801c5000024001d9a2401c4002607400155942244507480319500000740e11803c0084040070f80103402000f1260301034000e410b0407860040c154800c031010b694840d150581071604001805d1201c500011248000351b508020041c00145888003800040d07204041064800503544180204a078002e884036002c1d1755090250444c0b000c100b0340385400d80c0303030a1900048200d01d2404122040c40d43d0346000e9040324200b0b00303004841d01c0d118004031000d0b0240030103000034441c5100442d107601c001d202d0307810009001a096020707200c64101e06000c0351100d00c11a820150680d000500c1d90442e84036409038641e482d0202c851480c11004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 540200413 1250 540199163 540199189
    0x5041109091015090609180207050a050705030c011713031701081f0213030303050c1b0a02010e01080403020d0305040c080d090504060501020307030c12020111070602070b180d0815100e 81
    0x241007030b00c5a14100c001b50034181c05004403145c100c201a09004c507982d065064640894116085607911f040c00e00303129441c0ca034140a828041d005540c40304142d5401000003016010600c10750100d2540d4101001d2070381c0990310821400c02c4001d20f21220b0800c584400796001e0712860000e841c40c0041401003a08016110a04500560041c020700700380d9604420020203c0e81c00d0b0a0100e10384d07030341480b500194402d50743e501e400c0804032031100035421400200c80031528401c0c0c0700e401061400c40b0054401120441d40100103174041070050f1410b0344240c01064015208092620290b03072544480d9007031002d036038014000030710000700422507490329014132002003100380099481c02c05191001002e801e100740010b803a51905420360708041e8400d62140c2018094003050540303070031043c940320019620030a402c0e81e0388407010010403000c001c26404d0b1052400c40ca130040100c100d906006503102c0c0c04c002c0410382500d100c4004900c2c507071643e040074040e1a00c070b9503c20b50b01600c0e0000b00414030140741 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 540201663 1250 540200413 540200417
    0x9040c050a12050d200102040807180627201215031207020d0c0605041e15030c1106011814040206070206131e0510080601020705041109091015 63
    0xd80d000403c5001c079114480c441185031134440950840c0c00c02c142080c401d11881e405600c00a800120004081114030035280e8000300385034280804440901503440a00030b410ba50180b0f0301c0c1d00004000c981180040d641480000852020b81004440711905220088603442203000031320441602d107402c21890f8844984444101940c4074900800d584000c3e41e5040444403000050000641d076580c1d40607101d1a6104101c00421510f0b6031000b00990460700c00c9580114090340e0460034000c0c0312101e8815284c21802283d481220400300320041c08041002034244030010800c544502d50911640d4007030311102100e800d244500303024000c00c680b005800452000080c00c00d000051b0303220400c0300d0031603404843c0542c68a50f0343c40032083c00301040d40b000745001402d4222220900b40032820b90110344080760701140070b408042041d04c848204850040c0181c004040038009440c2036809503046206014146050107440000305080a50036602c03061045a030341da082060744040d012001c01c6c40414 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 540202913 1250 540201663 540201689
    0x518010e0f0d050f070c0602031c1103150d02042412050a170c0f0c130b0a090e07091d01180807080f070f03111006050603060d05010b09040c050a 64
    0xd40744040c0c440c0c248441490410500140d00100d401650041c0c403009900318442c03034100c2e580c500c0040c2da0384d4070800d0803c00c1d070103810044505c503540c64401c240103c04540040c500d5640c0e100031040d000768000c184682e2240d000c00c4010050303140d92050480b81100d000002c00000d1007244941000a0a0303446560300402c1c0d07100c148005280400c070707542010ba2000701c1a8404010707202e4102c60b030082080004607071040030110303441403000050150060100f9581d1545014943c594001a204c40e00d04050700410b12984c1081800c5a590110102a400d5415240d07811307111418001540c140640b54640c0355854100c0d00300002e02032040100300072042043c1545004d160b0748100c0240512071003e402580f020a0102034400140c00300d41e10315500c40300700c202e10103032403501800150100304051203034030842901d480025128820201a00d41c0200428150b90b03901c0c0401c0081030461108942d02e540b02d4103861a1a11400304650050341b143d0078010b1046e00f024244404031050b58448040603081c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 540204163 1250 540202913 540202933
    0xf09050f150a0c12020c0309031c030524240d1a010c0210050c01150909050c0a0602150417210c03070503010504090f021003020d0501050d020a12030e040518010e 71
    0x20013040ca418070307055880540c9400700000c41908601aa82c121601409030150b400ca00342003000c0d0040e039841098908003e00d0302c9020024030034114000d00a102503811107403910f00c030300c0e021204070707001c011107002401c41080124019507107400c0302c564050b109840342c44004040c0c8101c07000110011083c82e014003d80030344c0d00019140705008030440d0030b0000008140c0b21040c070130340042d2070304040022580508d9640b40b01c144028184454142c0c4c0c68080d0840c15203252510100700000c07070390541d000b8821a01810700f206041c0001501c103c80e51860a07500000d00180d0502600c4d51a840086c4131028203a00c118880c040d440040401842000420070804001c1c2c110081d20706590081c3c90020f005002c0b8036180703070004045c52000c2d43c40760072403030019220b0780d040d0000c000319100c080d0207000c566a01d1003030054880ca01d45e002076014403050400d00c5092900c51700200d4843c02843c000e1100854440450200ca600751151407194000742c120b0101c19100740201492217060034018580414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 540205413 1250 540204163 540204167
    0x503040f03140c220e0109030e0f0405090c01030c02191406090606011d12010e010b041a090a021e0a03060617060f011d031902030d0c0b0a0f09050f150a0c 68
    0x925031400c000702002c58000401058180d9102c5c0c01ca02030820000c001c01c4100d8100034040146544699204880c0741c0030041140c02c1500400f80605000d40080c242c1045107001500500001b13010031085204500303070803118800c40c8007080c1429008013401ca00d6020039510250400f80f0003403004035150301c02070510106903031201808500310868000c1500d0703c0c00c0d00001440b01c50f02c00303695140543c24a5106003030300b0410b5114001c5005c044404108070401520981a04258441c602d5070282444001404030b40701e540091001d02d8604c1c01c0200d49401c14400e0103100c0d04940340f102d00295442e8024003c45030020b149521600b0b905151010074a400780000320303040010461705040215200d03140e86440507d0070760102010740141550819140d00e500c1c13a180c5180385c64240d100f48140f20200c0071840c003403222007d0480d041007030704400e5540c106000b405012900e88a064882e959004000401c40030b00801e00e21461040c0504400940340e9003450184001030141248036240251170014a5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 540206663 1250 540205413 540205429
    0x1051f0506070206040504021209161a03070e0910091808220f030b040b07050c03040603090503040e04030302190915031a0405181920030a0503040f03140c 68
    0x35400c450181c1e60307000a2020079224080c5078803460304140007141c04000080101000c80c41143ca000417210894000508020300600f40e20030040c1c400800b80300d001c8803228800c0110380c07103800e40c00c00c0d040c243c40c0703c40420486001190541c1000404003402d20001c4010700515001d461110050f904e502040d0311003801900c0741c11900c070340c0950050445034883e40b42ca0118401000d1080c2d6005190b40d076420b22a031b4a0004484c111503908240d0001100313240101d080c2c03110088030f0f5006500385420240c007030300100040c04041d0780c1031105010005034800c941202c0c910451203590f0143e1103261400340c4d103480000c24000c410078028028424404203000c03200c000014101032a02041c01e00d10701040c85441980c099001ea0050b08007030401800740c2407040c00031070011055080b50b05601d205400000041c4c440c0b03000402c0007840c074402d4021004a58000c94440e00001c0581d04009115034a90307186070b00c1a8441c1c060609148010400d120b001558081002d0715000980214040600003d00300c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 540207913 1250 540206663 540206669
    0xb010818071809020a0b03010b09060d090b07030c110706052703030a020d090b0c1e0c0d0309050a0501020718111306080a0b3001091e030201051f 64
    0x120100da08550400c05007082100010624000c425031a00711400c2c220020b801003aa050740144101580090711003d07050840b8100c880e09a204d0742002c212a0412802d82e0014500703405098581030240b010034180714030503000b001c0e2343d140000d22043c0c208001d0502c58000700c0e4a80250414401085075507005012901c62102d282e10b040c0580315401039100d8250600302d07801c1c0c0c0620000c1141d80070a46c00040d10740011442c2c1d01d0320042183e071a6001822441188070480954000b0b100d1003001465210007481082c22240a0751140510240866401081c0c0c81040c1d000442100082000d800d00074450740141c0002e1010300225402c20f141404401801d00c400008103a540000061840191041d100d010718044100d01034180e440070700406201043d40c02c040b000d0318000642507585006510400ca6640c950500b264600d0142c0c000d46407803030020b1880c0b0030342d501c4082c0750000840c101028030511500c03000c5044a1110780c2030007400c44500400403e0301e8141e260001d0586c1c0541ca000d01c2c22 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 540209163 1250 540207913 540207931
    0xc0509010210020c0f120a080105090106170c040519090513080316051306020303010501120c171b070302010f0c030605220603081b010f0c0e010818060f04050d030b0108 74
    0x340d504c0e01c840c0c1900d048070b04034a25000d80140344400b004440d011008040c00000c6903207580969880d40700f00103000d94280f0514011641c015210400c3e12400040135610143d40d91240342841e1355100031403690508000010403a8045c00b1090120b88194410320b074110100b414001c2c081101503443c0c40c00d920025207140700107201480350003461446241103d0313640b001c141801c1d11040e61204041c0d0baa4200307014841c007040a0000500c0303003894512503020303460620358030340c244c040040c0a0141c404002408007034032400d6003046c0166100005c1c00800d0f04501c42e600000701d018000100c08100c4a40950350400c15040c110304202903602c03a034104550a100242240018181038400c1c0020061540b000f040400042a480f00b05510b07030718020480c1c2c1c2208001c3c42000c06960010041f664180940d0740031440c129a41e400700d5105070b20240e400861549058080074204030503514042c07088a240c00400803041c20042000410311003011003c0e40341c142400307400790350400a064240000d142100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 540210413 1250 540209163 540209167
    0x6160c080f0d090b22110f220e060402010c03080901150b070b0c07020a0510210c021005070f0e0a030203030c06010f0e0103080d0504080d090312140c09040915060f090c050901021002 80
    0x44655154000300380c0c1c7e0b4000822009000503400449982080110340c40381140380340c455800c144034000b1410700d2095074160348450403843c10340d0b4145c2d869080507004015940d07031028681c102101c0c2d2000c031009004c00184403500c8003024034216401c0a0010048410707140180518030041e220000700e042a142c040307540079042035015404039075101c520f081e0004001e40140650b000b50380a036201e0450a0096420340b22058081c244d4801900c0301543c0c1c120029204452014481e48207141015510340000c10f0001c0042d0741740c000070b1440d0442203500300f09800105c01042440030320034018000700081e0410000703030340c55629498640d0285031840710030980c680e8006030800410034111040e00340d15040400c1180080d0070018403140072000c54600c05450901031382e600e00f104565091190001074150351171300c003a41c0e00744405040e01703501c12500050805484440d80351603004d90b40151011413911a55a1b00c1d00980906880100e0041018000d0410050003142da000c10700e04060b10000e24056 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 540211663 1250 540210413 540210443
    0x807061e11031e0405040e0c011d060c061005040b0a030b0403140909071106070516120507050d080402030c0913020f031204090b0a060206160c080f0d090b22 69
    0x1d8154820032541d21030340004a04100702c4440c0300006001514015901041502e1410007040d541e0401c20690a0100325480319410040c50340e039006886110018260740d0902c3d40130002c45280c103109488403101002030b00002c1c84203041078481d07403d01082c2100c0c40d00300c0358034548903070800c6280a4009020414060600019418804121920007102134422509031a00d440000c0a0110b5070300010080c4c0589008200140e214a05030748000c000442200411100c40d40c601910f01c400c003d1100c01d002040c4400c202155040c0242d0380b442040b52901c03200c070b01c1d00e84101410014a400020311070180c00c070500c0300c0510b22100110146a040d5154400b42d142c1200181c5011010040a43c0d00e074000038000c00d600301240c22100c1c1c515401e40f4800d045d01c2c0c881c0d00a0340c4840c000c40b00c00075400f400d613141d000014444c020704202c00740590031071490400c07000c801c01625807140311414480c50300c03a0f403044200071905001039400f0140c41c0010714468a80030515442e6103c9080150246078181108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 540212913 1250 540211663 540211697
    0x60f130e0a150e010518121e0304050703030e030d121508010c0309150605030a02010f0c05070e0613060503071806050405070e0307120809040207061d06010807061e 72
    0x169890380c1100107284501c1240a80c00068643d03900c1c8041294200008035064801c01c40b540740d041602840a0a502192080742c0314490b082001900e03050400e036a29220340c6403085000f07601460050000d00340305821820701034082080c0454040c020780c4410614182d460307000d000030b210b580b0071580210f03e03202400310402c0c1146d0141c0200150b546480f00b00304002d501540003403800c622a401078070408a109a1040071244540f0415415400410800c0b00541c407611400b01c0c00780c1c140c20b00e8500803120b529400d240c13424541001d0b03480c40e540f600303000070792078012040707004190184003d0082a04040c0801c0e16a001449541d140c0c0d0601980100c460565802c40c4003d0507024008000c186001074006000b03024a2034014000c2c055100041403001c082c1801080d000e4112038914070380030242c810b010003588031100c16610107594a101642c800160b59040c0c2c500c0510301c0c014030321541000203840c00c0c8005a406107042c004901c944c0403500c50032803041102c1c65040c0c140700440050b00809 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 540214163 1250 540212913 540212923
    0x11409130b031e011b020c0a0302010e1c12031109030a0813092906070c052209030206060405060d0b0105060d0618020d05010e0f041209050d03030f05060f130e 70
    0x500c3c1d40c210f8900400010b51401540500100b140300988940036101e60076003a41c4400c0010a40764126600201c24400740d400381c90705016141020340006c0030241400508100000700b4201219a0345080c1c1d00c42c4038440e854001c3c080c00000c0321031114074102103d0002540d0b00003c003001401804081400100101c0f1100e0b0b610007843c10305c40074401229030109400303590b0f504a500d003042c41143d04c184010313810310100f81c070b090a42c0714044e0b0081a060030100003494480c100d402111480c0140d4203104070606018440c0c0540c801d40040c05103040c00c10800c01a61801801240500c0b040c404041c0070a03020000719045a4080d0358640d91181e8442004010f4420390708822208042500c80c4e0030b440780c2c1c550081c850741948180030890f41c1d88030124040600d100b40d07100c50b03c030880f03000420b000c00c1085684401d02c4e103190600060722607885000c259035001c004c1c3c0a0300401c2c0c3e03900711200d0b56401800f501e076001e0811070701c5100e10305c22180050079040e01140e032100304a6407881120314181c01080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 540215413 1250 540214163 540214183
    0x40b130608070f0807080d030f0b0a03120932030a0512030f100b03391e03070c0f110607080408010b01090b0d020a0302090d050c011409130b03 63
    0x8024415203031104522580c40741c41d032064400900003014001826000410f000c41544e40000c05030082d03440050b421000b40c08400f6402682540c1c031144414103590340ca2110008520540c080c4951920140c80942000d03070710350001512107941751508440460101801880c040e000356580c1c202d41e51440400d19203102d0704c4c40142180700e0005640c20100103400914803450b4844681e03c03072641c0700b03c448036400c8075034800c9040340e14003030010511980f106141035100b080d505103404d00d603032a00b504040100100194541c4036410000310900f0203001c810200c0010b4021910503482c50820120007070000c0c40702140a0f2800500300c19031400c0044003401072070501d40c000c124584034002c50405554691003031180015643c601013201e100355006401c42001c40e95125140703401c0040324194a006988a908070742d042580c02c2100003000da4410114440250041006103401e16902d03002600c3c10314501c0d12055050800d0080b83c0082e0750300c0000710001c103030800000c02d1940104000c81d10b84003ea039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 540216663 1250 540215413 540215449
    0x6062b0311070f17010218010509040915050709090b0a0509060a0803040305010c09240f180306090b0106170a1a0904060b03060705130311030a240b09011202040b 71
    0x2d0700020b42c044071419840c156141340b16081c0309943d001400302c1c00c07031040c040c41c084141c02c210180419503000c0c0c4090070b402d12014001003442c10740c50307840e200e0900c400b41c0078120003642d88081c09140750740446807101400b0111810020103115a00107407401d441442124800c80050000424030340390f100080c40244800822a40c071f13241c49103481806800b1503000f1f6800107488800c00203025064030090340001c40a00140c400c4c060070230704125003044644601c030091010f80400701104500e00b4003a600154082c8000149a400303616040b41c1c00481030340040104840202c0d50b481c0d81825002160f00104407110004007100383c03005d0301c8440c01c4480311080d8040a403000f00070502110b6001848403400c2102610240ea507025020340d0103000300c15201800019120091001506c0f40c40d821002500c000c08480301030816a071241104201d40b12140241c0c40b07986041080103911380289945031204550b002d00d40c1d07040c006140b0880100e044040e1049440f5112110306407121050018110502 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 540217913 1250 540216663 540216673
    0x42307020d17060d1202190f1a0601140903120f090f0406060c0b040204060b07080c01110703121802060327030a23040b0d060806062b0311 61
    0x2600040d44a4420811903808208044400840055000d00c00c600c6907200401c1c12540e15500e403505941100182118800e5228003164034240000184069810611406a54030000c29900e08081152080010b0181e0500c08030148074580ea00403503030403901241d0480c0d80d500d030341280b4002854a04400034600d2600000a100c418441c03200340100300740d01003550300e90742c0080c3c0301c802e200c03c651031446800d002070341c03e05100d0006101148413a40003400240086102d40d02d0300f06e2340c00a40d0050300203c611202c00100d03a00541d40a001d00d200c401100844103023010300945010301458200c2c001c022000e903852610764051061640294007480e00980780680742d151201820850292101c0300342e24011060420310114a0000101d4460b100390703980d901254100600d001c1440b0400c04900714480d8400e0001140b01485203014120410030b41c80082542c80c0303804540380c00c040026024601a5514003a8450488070120320200710341040c1c0b03610082c6446908040f110400066200c45a502038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 540219163 1250 540217913 540217921
    0x70e011715060a09150b0309160905010b03060103091e081b06150d050304090513020a1e0b0d0207210e120c040506040e060717100b090423 61
    0x2030300400c2040300c100350044070320152000d50941c04808089569a5000880e5041401240c0d490f400c00d55505100090540c5401d803192016600780d00115072006856100c070303100e000c104c08900049001443e030504208160750500f0300c501080d10000307258034181358031010401c040090020b201d07003020f400343c01b2519010000f49007100d8154050b03a54100c202550700e202d0b9802d03600200301c290107007450100c1c50341175400130703418081c91100010301031303e041c0000d000c0040c8044541c000d0360301c00ca080c041400412041403042051601454000e401402caa0641b000d1071060082640b100703841201c02c0b82902e031250382000001900c50884000c00c0805040c0480c00c4d103e0030310400c24142400c1e92034511080701080180400c020170707400152519031240e0150110307414039038492030704030a0140001c21190700e0540e0725450842d0035034208000071544203004000c06002ca06050304420302c500c601c0103003494069526014000c812196105503a180c02d03016140003100c070005080b02060401c0d00e00c07498 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 540220413 1250 540219163 540219179
    0x1b03080103050106080f060a0b0a0e10051906021b040b150309060105041518060f140307060e0d02120f060916090c0504090c0c0b01090b011209050a080a02070e01 71
    0x6820310040b6081c3d030a050010624110110b1a00d840ba90501e0061880b030b580d015803000070780b20b0080143d030012001d1102151808030501031a2040c101014007d41c440e01e814240200001d81c5a410300c800b10b1500c20602100750b01292004c0600b0000c0d4064907020320f0480010014040d0801d032a81c0039085685241c0a0400f81d00654414004034064a9076a070b82c41d0140310503980d084640720428030002c8010310900d1150718405082100035040081d410780c882140e08610348094014104420f540d41c0710013114a010040000074044a1400d0748071100008041900000c0400300244034080440143c203080c0800c010800e14100300c0c0c0112005030510a441c151100300700441707021a00d29420011506038040c1c0502c8680c511242c0c1d500345060700d031052182c01428030485a008021501e00b201003c50085407001e4080d1200c02000078048560500251101d4100b804500960b81804032040200754042001d00209400410283c4d96090100040381000720341e4001d0701d690b069003800424205 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 540221663 1250 540220413 540220427
    0x1030f02040f1d010609050c0301050105361002071a070201050702030d03060503070e07170a150b1305090610030504080d0504061d0a15020c0115030b071b03050a0503071b03 76
    0x42a52002048410348030388540c425661f04031102620f600c1c08000401095209400502440100702c460380c030303031003402c03047c05003130400c034127003102c0b880d004e58010011610703012000c0110140036000602d200c62802c000340d103000350702d5071801c2c3e20380801140d030030300b9a4016011039142035801810f031030030b0030b040740780160081129008a502a20581c00b001c60301031b04022426005456079140d82001c0109132000303201c1e00400411604200f41c4601c8108030566486c044100502034070000551503800c500403c622249036607000c41c6c460303d0888144521900c644503455001c0c80039150104060340c5604040780140f02c0c88105410451a18082005003e0300303622504198070f440340700202c0500b818120650302d02e54000094900703000f207150020b40c4d00d0785c0e41c01858114074110022581c0801c6258280d03005100d0303070080d246000072408001c0880d0b4841c4007401c00310030241c1c00131007801c5580c030010101d02270480004217010001010501150080462800c24003401c2042c0400d240c3d540360060000f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 540222913 1250 540221663 540221711
    0x4020d0219090815071403070201050f070311071104020f0d1512050c041d010903080609090a0503031b1b01020d0507110a1118010602161a0301030f02040f 68
    0x110079200100d20645119074200022598014018000500301c510218840c580240401c0d05201c610204913142900510195100d505140c0000035149487c121365020640002e200204244c43c018008109a00e00b000380c40d00c60b504007414100b14491003003c64000d204980000701603c90208101007920312603044101841208440140c000d0394602e0150200c01c0d01d0f010007011074110040300ca80c17900f4154002205003007520803000c0712422549004c0c0c21034a410006070009098a000c0021500b00140000e8006220f20001c1c8541c00c46900c80903240e010180c11541c0c00e444100142401901c003100743d034212a82c94a074603a18041006006001f075004800740c45a2078100b04c001040c803809400d50202d10030707000e40541007010003a5200700c400281141c0d080e134050f0603d0300100c100c1c180c3c5a0807a002e44116001401c0c0b1a102034002c0110040b00e42c8411904a00340060a465004a07030907281140d5001c030441c1d40d264501d20000300a4000c0c0c0d941c508959190801d00041440440030520390 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 540224163 1250 540222913 540222937
    0x3040c09150609090b040924050c360a0b0909070309020a0504020f0f16021c03051206030a050a030819050411010503090f0a05071505091003180204020d02 68
    0x30110089071420700c1c101082c4200404a4900c100800212016402c1640101d000510004480040340c0e00d420307000740410001038510780d00011644d1008280d11800740c1005484a619060602d221640384102c12100101d10f031a080c100341044e9010b0b10303400c400200407002046420b10a840700260151900b0009016100c0c2410394041034105009116400a0035006465064050706010500010f0b6100501b40354424404002104d90070b066600503040b8641d01d001c1601810926004005c1c0505e41d13202100d0810900760390410000350018225031900a4000090301d2580c0e034000068105420108058035900421200d1010141e20000c114840c500c0440c1018404408801e0b16040f00c0381100c0003001240c0c0c2c250703170390403660003640039640c4100c000c1e0484401c20403c00006041103082c0000f1202944480c1c000d011b400300241c88500380505520b0010b06004080c00014045032502e044030081c59500d071400302d43d2407400702e65000000c0d0082d2056503a140c0011180d00254018032003562 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 540225413 1250 540224163 540224171
    0x40509040f03090b03012903090a060c12090b0106110f06011412010c0e040e01020901122007030210050a2a021204120c27020d1404080a03060f1505070501020d0203040c09 75
    0x1d0050382c1202380c0340100c01c40002403e80c004613545100042c0750b00c1001d141848450104a00140c2c00d44c0030304403003603100b0114400d440d40f601a019040c14581280c11105400c41100c00d0f842e85000108181140c0000c5451004200a88045180c850711156088115401c10202400c865080342000071080f2050354108280c4600c0c403e1103080740101c0040a00240c040076100b4142d52942d0810f5805400b16104c60b942d400b00e030600c4000b558407510084015800009003190001010301c00c19a0240d1420002c2c00300070700c0d80b01080c801b407014400307259500305410407521525108006440169520380d090640c2c980d2a103031144003000f0303203641c04c0721040c0d00761902094100804203000c54405d01002d51003400b0040201c2c8030060b40041480b400c0c50340da01c030700305201105028000d40c0114001d03a0b20390765400090034001c00742c4195810030720400080702e800b0071076400041c14041007540c42d450003645407091850080e0280c03086040341c090090010050200740310040c1624002c4a40740c600401c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 540226663 1250 540225413 540225479
    0x60f07090b0703080604060503010c260c04050105180405091b1002071a070609230703020306011806080a030509010f02150a0902040f0f02130605040509040f03090b0301 74
    0x100c500c0124014100d04210911a01e400280186405600410300800104005843d4800b103402c45446a4800001581c0750303015608404144103030840d030300c103801694101898a88a4910944290b2140b079041082c0029107286201035554012441000140180040d040551b00103654200c0d1107411034601054802100083c036201d00e40460000640d00540507403454400b8000f06000484002c40d403009041040c0302c002411481074007030552203a102080a40341c5403000c10700901a5001c0207131590300102050002da94005031340c504403000c400c902c1100b664001038540203080c2c140e01002e0140b28000c52281010340050190045103002c3c1c2e20b08200a403148400caa80e5095101160f50544540f0040340307540302d6a0f0869190030740080c00209218103a0000ca2003159803041d003a03410203902081e0100342d2403170035882000802c0300d407810a05060a140001d10b242001a00082024040078441402c1500480700c0b5402042800b14030307501c030342c0c1d00c580c22079216030b9000f51030340c000e50320b00b00c62 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 540227913 1250 540226663 540226667
    0x303070e010215040b1b04030b011a210c09060c0307030f0215010e2806031110020309060c150a0209010906030e0a03030f1104140306010e0c0708070804030b09060f07 73
    0x9070410f4001d00c07500b9110b500c46481d03c20300d250001d03010354640c0042c0c000035501c01c00b01800804c0154413910003150a589484e00c406c086d5039010840101c074800030804016583c801c290705500d84503610b01d02003082d4030b604101c0c401078030074020515044000401c60100c00c03003010000d420440c1c0a511002d00d0300c0a40b0030200d854190f001d81c0d1200c40c1401000501994400c6a00360b40e011410307082d400110700310f61140c5039981c4c8140c9920340780c02c2d450311070a204100420081d200c4412041d944040c1d000e0000340040d4480c040c80488900481d0041400e203642103040020000328520b0b0001c03074245040c542c80f520040c2d0b00240036035002c038540c03c1000544612a204070f450210080014019011030b0755000ca001c0c01191210524858951005d41c01d00038032200200010700c45100340c00d405907480020316050070380503400455508800020040460501e07401c032110306a01103e603035559a66803400300c2c102d00480d04060f20070b01c0c0e078100b0490084800603100303000302202d0360000c074156561785c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 540229163 1250 540227913 540227923
    0x3904060504061d07050423030a060513110105040f09090203210304200607060f0f05130203010f15031b080d1205090607021002160503122203050a05031e01080303070e0102 75
    0xf130147d0400c450300004400601010148204900c001c0a41d40d08001c90344900d0700380c41c01903404086125a03c803500d01000841c0700c95544100081c2040d604251800c40b850b00301601611030b9041031074668807100215a0244000c006c1140142d907040310705108801407504a4204890442d0803400ca81c420441d070090bc08121000403400820491902e21259900c1002d054042c3d0000c42c1d981e224008107800d4079080c001c03d4405c4c00c1d4003041c03400000d483c0c01054292090b0700e0b4160b40e541d01c0e01d8891111003140b0b80c4803034141c98001d10009080d401c40178500b0303c000c5280c0e1240c46c1901900c144980d4a41d03120001854547d281d4070140100c0d180c0188454480c24240c9401e805a801012480c5444080380c020700301450641021602e40308603500d815013154052920003420000c52010064285600c80c1808025410540740341c0c1101841e0303801403c03e104516455040c880040f00048241ca18541400d4210700d9410b0382e01e64950f50303041095902c0e0016680d00c0f000c25003592001c038183d440003507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 540230413 1250 540229163 540229169
    0x111605120a11040f020910120c0810120507030b0f010f0b2b0603020307090207020307080d2f031305040c0e01080c03070c0b040302030307023904060504061d070504 72
    0x8200b18811101020880140b0712800c502d070f00c1c2c41d02480780d2241503603140c14552440d0507507102c0c0c041850b07030300d104d81c42101c0d50b41448005004540c0140b01101c840e4000b40c005503a24444a91000012070402c545010300590005007800e04182c10402c500c0c1d10340400314103c0e0020180144100c2d12468400f00c02c0c000e00f01901020800c0110248420011040d482a041c00c540c1c8002061601e0b5000b00c3d0500301d140d00054042500000c0b02c4046003010840c0000402d1950050020030403070800080141e03013081d8880c0c40c0c40d4120300c0790802204484940c20660700c2e01100301c0f643c8428007580151040d51610032648100d01d803610420980e402045119203002e0140c0d508581d555510402c00d5160300040c000400700b2207401100030010301c10384013a07806103000e5002180c40e8640701000a143c0384043d2211203c62154100321424020189240440c0c0b04000b0204031030401c140c4045001085281d00840e0b000d41071510006010008180245500310241111a030715566800b0544142c42030788 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 540231663 1250 540230413 540230423
    0x1805060112021518011d041811030613030305150405040f14060606090613080706181a1911060c0703030f0903020307030c050703060911040b03010903050316111605120a 74
    0x520301c4150320502140f000c1c40c2a44296014006e00c000104017101da030340600201a8880b400c141c03090089d40c1080700e03c11003044004290b10701c0c2402400f410074900c000c000b4181500e031404107941c070040050030b5528a9015000308420301d06410141c4003250340b010140c507040b842140b2040c14000202d074562043c40c000c0c266910b40110401804840e071b0190203501c0d01c907124035a0215410f0810710210000740aa0342ea4242e030205a4140b01109400c141e20080740d102c080c0c0d4803200c03040032070000e4401801c0b0801c25095140c100c240217480c080300b8009480c0180c00380c02e003003202100c00c40000e810341d80d0103543c0802100d610380c1b842c1c20444d2190a009005603005101840c0047c1c40391181e50400b038070500a5501700f40c1e5a42d208001d40d00e0b2031904607845613102d0b44041c07160409104a03484200d04400a00c0b1941050305d020f407030741c400644002d4035680080c416145550090f46000f01d4088820105d8a010803074010603030030a4500e000b1240305003109248901810400182c0c0f151040e004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 540232913 1250 540231663 540231697
    0x40501230d0c08041407032013140105011218021e1f091a030109051801020c010b040c0201091119030803090a111206070f09080f1c1407020418050601120215 69
    0x860303100100d80039948c0c00541d00070100340840c140824540103c51034200303020001d55480d4107003000507004010861440381035a00c0d106005101080d600a14988103030140e8400c468100c9040d245003148003204451f641142d03648510420461601d28000708400c50741c0c0e5184242034481c240c0c90840403c1d190b880d659900203000501c0800348a6001c540c00080301d4410380c2c1c0c40b101110040742641c008808a544903596405154014109401105a031641d140700800a0001d070f6650030040780203d1010f28015210461040f24440302c01004601a60700100650f4880c42c0034050315582e00e0540c02c0c11a940168a40c10342d4280c1000064110803d50180203480d407951ba94104032003441c0340103151f0041003920640069120400d0018806c3c818802002c2c0c00341503003a41d1101c0f1070126180d102002c001d42020141c08450840c3e0507660116811074000c100148022242c0c0b0100071400e901404038054000005074401d00300d4645c2052500c00e81d4200c001440f10b0507280300300d02490359500b4107035a070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 540234163 1250 540232913 540232943
    0x20604030e03010c0c0204240b070c140108190b040f230f0703020304052d07060503090d0c0221030a1106060f1c12050408010e0102040501230d0c0804140703 69
    0x125402994070900d1004008d12580040031010805078943d0f808001c01c480001480c109003d10a01d400002c2c0c148000d80130b129101d04030000300fa0900003008160f1450811104a070030321060f401004958000500a00c0081503010044004000ca004419002502c24411072804140116070a120394074118005444d40d07075080e002d5000e940000e0040701d05004010302c00102861440600005161020b5418501c0c02c8045645207070596640280050100038010070006400000344c4000111551800100549061003c2428020880c603c00c800000040100c0c58031074000000c1d0070700c0180c1f42d5400c05428099031205407101820b0f01c1c1e05400080c0412168006c0c00c0040e44a1300e40c038401c010501d42215552126030011251048180006900140030410b1038000d00400f45003240400085242c0391501001a141d02c80081001e4009001c400010301c002c908003003982c1c64100d503807109112103038490000410a8404a0742103841c1201c003500c5258611002071840d01344ca40c446980d5890141e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 540235413 1250 540234163 540234169
    0xa0c03061e0614090901230d051207080408060403020c0a0b04030c0e060f10020c18190b011b0c030309060302070f0822080f0606030d050904020f09060703020604030e03010c0c02 78
    0x85041044803402001000c031385458107548507000705000010090000e800d004840c58005100304814400c0810303d04060100e14042207044510800c1c4012130b99404484c41c1a08660041da400038145024940c1048203040d00881e401e40c1007001291117501c003644564401201c0d0095000203481d42050f400f00740140750b4000d9000da045a03008185801e02004400000d50044001c8007000040c0c02c102010703403603405d02d80f2480700018503a0100789a00d28050841503c2c042403911881d420940300e01c0341e0300042e401109000c450503005115144030a419050480345100540310840c002681080c000503034511a1080d20523481c2d01c140d40c800c2e0107103a5180c18100c0e801c110b401c4419100d01004100e0100340c140d159000800710076001d0024030908da0007042c100840104082e009401000101c3c05c001ea21404903104030204a40c01602d8800c5910100114000d800c40c031600085c000480c80c0900da00002e440303210b6442a951010b6001d0103600340740c05c1e1441042984081078035001e06500500d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 540236663 1250 540235413 540235427
    0xf1e1e050d11220501050607031413080313060f0306211515031101020a0503161104050f0a05240d0f060504200414041103070e0a0c03061e06 62
    0x5001e400c1203110802e003100010001480b803544101500b40e285500350828016014450043c5411074010b41400c0460720050f10800b84030006110075080011083c0e02e049074103132b01401070480712007100e8032403100342c1807034078000c241c0d01941000c43c00311107a19102500c640104015624080c080100d4100d0440040c0050460b51104480320145203a61090a800034881d00092829260401203410b00d0740c00d141d8552024411042d046400440e80d01c4013107640041150704a166030407504118540d941030400741242c010b140c081d40079007000244101020804986030141c91105d00802450b12500c40c402d4045007031400020729102e00080648661900010925010303010702e410305803940d8260303035244c02c0b500d046400700c0e5007070010f07681586d4800030740000c0707000d04205640400c060000c1081d500c0c0750150092006009482c441507000041d1010300ca0f0800400041c940d900250a040503003001400c864803c0d003002a10b089030020741c10702507100d90304042d80441c690460090618400702d17152 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 540237913 1250 540236663 540236689
    0xf180a080924030705071104061d0a0e010c03020a0206100302090a02090102030d021201030b0709051f05070c0303030e160e010e070c050706170603031309020307090f1e1e05 76
    0x2c00d2401c01020a0001e05400952150190303a588a0b501d0380700f442c00100d030820380d240950240d4a0088140006420214590000c0c41c025851034120f54070341c880107010340030081030022036508224090000c5034041c2c010b0080391031550240d0780b803a03403005084002c0344100d200c044d6000c40d080012030744a4945500a005501041c4166841d06c0d100345400b00684c0e002e0702c02c0541d036203600c000400a0190040a6541004a910340282140c1c035010003e01c042400103140f840b103036207002c1502d401038080e40c01c46510b1580840c0c0c00700c01d1541c03800d001d030082646000d018058004c011031031851018040c031050507901c00040b211440d90802801d4120480018010b02c107000a110314080402e008010b80340013841282e444040344219201240111346015140d01c0c025481404129001c2040500c0c82050361400000181c4a42c3e4540c2e044400f40030641c05030030028441f040c0420b178005000807100f02d0a240c86186040d441c1e650780341040d00c01640e007a5003286615144103100524000030707007401c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 540239163 1250 540237913 540237949
    0x91e0507021f0b060408070f0819171c0b0306010510050d0b060f1308010b100e0f0114040f03051603170a030204090e0c010f020102031e1e0f180a0809 66
    0x4603d940e80108035140d000742c1088030a94041042003144445002d41080540115005004a040481103244441049040091075400300341d501400902c1d46070306032034510b0038904003520360031a1700704860010100702c0c01c0035010b80190b00001c00c140c00d0020150b10390405c0c13961031a01d400c142400c600010301e803800d030450f4443d40411403020100300110150107000a001e2441e0180381c50400c0082c00c40d108944018000d10301004015052134000320304d07000d103480648041c05c03000c480c100100c58a11030507400c03d0502d03002080c00b2880152081610054a2041e8111540e0590420300000c520450f840010158100380c2541c0301140c0ca003101400c400041c0b03060160406d611400c000060f21404010140c82d40e00a4000099560f030080810b07461100d54002149103007801440c0c02501d80c05112010b01403100880810021509081d0702d19a00b142242c200f081c40c00e2081a0240940058800860780b400c0060402c00b000c0c00811900180c540c004001440d0550903410f00240030041550201c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 540240413 1250 540239163 540239171
    0x3060618060f100809011b0906050a09050a080a0b0606361305060f040c050a110a060e03030403121e050c0d05040302070501020d050f03072007091e0507021f 69
    0xb09a40700e14a030203540003460b881d1015103141c541585403c448042009000c8104035400c1c071000103030440f001d8415a00c06181c43c55852145010540314002541d001a811401d520382c00200d91030003140a03510b4a01c620b104002d203403030b50010001715001d080090b4200c448401381100490340b401c1500b281d65040074076509900382c459000180e170003501040303080d03059480c1c0040159601e407003008070841c03c0e4221401c00070001550b0000700389018811a01062184019440c82d80721400c02400c1012540100203000c14444661a951241c10654049001c2500905840d200038101d0069011504000c10119001022190504042d100140c5901c0b01004204000460fa131a80e02806110b00e000343c004003009480c2200080c0340081803101b0701e0411406021078100d140d0400d080b25000000c5280c51030980d08030b01c1e0b401c0032a00c14840b80c50402d10034140d00156130f60721904103400d00e699010a05808070502c194000545008075400ca0068200b08000300c0a10159102e0401c2d60700c2c0108001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 540241663 1250 540240413 540240439
    0x3130605040b0f0c1201030201110709021306020d0f0c0b070302040306020a02071806063c090503190224040f080609160b1b16170c0306061806 63
    0x48210340098406407207110040302040f9458002d0940150000308961000740b400e880da0803c00f030b40a806010090401019080d44805c01c00c0c10042c05020308180300e000c41d46c5441c401d0441280b80082c0c4a1030000d03001c0c981c142040c580c0550f800e54010041c03511a103e5141e55a62400c2e0110320041c281d6040c0360b400e000220115000d880034210100058005018040c1071100a4203003182c190503035001c0c5420328606210075a07000709080002900312403007000600d4405041c000b65007114000c40700b443c0c00c101100c1000c40d8032442c00e1088607810781c2900c088542d103440e005c10b001d1640c42c0194002400034090303001c484002c5001040050074103007443c240b540303078201c20b08103650315440361b0701c20b0303102d8001c0c0100d402c8140701ba510328000c90304d9450310161601c80040858012801841400080d0b8617040340d880905200b4208859140c0d040b5014140e242e0b40d11608120103041424507a10510040780302a00700000e00d2070040380c1c000e12411098034071814040e01c80d07070010b00c0940c01c4107031800c0d45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 540242913 1250 540241663 540241673
    0x1020f1602043c1407020604120c03090e06030c03120702090f0601140c01060f030f0b09061005040b030c03101409150606070201020a050a0506270c060313 68
    0x103089001411050038003140c000340100001d88500b198511503500500c1c2c041442190900c1d65100385a841643c04880141c202c071800d00144034034500c03410700344407080c104030640e41d010409a02c180d11440380b1116481001c8400c469816241c0303001008103031300c0c01052040c40c0c0702d0041154015070043c11501c28210034404a8149020800300040c3c0c0d10340410a9003c6240000c01c0e19030000c1403030528035041c60b0410009000200c00500380805e13000c0005ca0601104003034002001404070704451262640d034a03e400015001e5400d0b050710342e281d1010215072005c5c00460300c14003405500900406043c141010480181095030140f941072145003000342140c6c5080c0403600710714280c048005400740800c10084260305005003c03000a41050400c80001004803074243e801050580d1483d48514103480140e10302450303040040d049104080084041010000340e081c0329501000904845d191107201c039420100b01440d880c031154000d070419030b42d90704144014541c040611541034001200540b50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 540244163 1250 540242913 540242917
    0x8090a0609080901020f010e0705040908040317030403031a090601081306141b030c031b1611120708070317130803040603060b0a05090d030329030111160303050901020f 74
    0x41100c11150100c1d401183d0f6805221840b14600745000034080043c1480126071a0290703406224480e0707589442c00c200348118035040c1c80c0039540c40107002c20319400e110903c901e00c0e0002c444c100c000038100400c90881d000302d8070752808007a84c0641120810345036900150741c3d100e40149003082428050141e080452258082d61035007071a0b440100280f070902c0101040c64601d4000491601c080410500c5501c9030030303000700c1e941f25105001680000416112120a0b0712400e2841051b135402c42420a0612010706065072010004031000f1228491010405444844a2084203615003020f1000c0006c907540d1600102d1900c0c078421b210b032034924682480c08200c1941d421107143c642c00070400303016150b00351050390701406001a00c9030403d5801500141580b2a000b004e6000340703400050b50341018000d03040240d050130000008843c2005914410b01c04071648a0400c0c8250700b0f21460144c8040c6540840303d1280d00010322090f401844d40f010b81c0a4a0081c1041e049503500b040000200400040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 540245413 1250 540244163 540244181
    0x206030402130219110d020102131202010e13051509010815040602041203080906010602150106030b0a080d0c15050103030503062404090603060b091005130207150e06010e04021008090a06 82
    0x4034508080741017500540f1704036000080f074045d6841001032000014664040600311040b03103050100740040381c80100c904028008415802c50710741b01d411641d00e810340e0450792240345240403842c0e054031050f007000801d003000e106520b00303604040150600000c88c0d40d400b542c4503014503c00341c5000d40e1100f040707203000c60f07074042600018811020320180d07030024071015004088a10040c00062107056900c65030220611603901070503540d030340030a003d40350011000c0c01881290241d0303c04c1840103001400340d481912003100c0b0014042120600401c051042d24140e81d05a07480030b0a43c1e44040c1400900c400054946a100840a25403184807650230001e202810311848080390f4a45180f518105071403094290501c6181e40b402044401c1a12007011421118200d030060304d6006882d440134001d20943c08058110814144050b523884619000174002450103401c4514903a43e0f01c0c002110401c090324002e511184003201195528420a60603800201ea602500c0b0003d083e6502c04048038541c0c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 540246663 1250 540245413 540245417
    0xa0206031b041e0312020105010e010b0304060e07061d030303090d05160503030a091a04051f06052d0a030f0f060f0e0c0a050a0815150d03050919030206030402130219 73
    0x14414010030860307005954200b04180000c2c8855410511101b81802050181c07807410033004c80040c041c0314854000e0b09441440744144c418041d00c0708030003400101507803251590510388030401c0c0c859040020444e4800c402c0748000e02104c400c2c0100845003540000d04001d20020b100032954003140051006601455664000148003c850b2402c10045d20550387c004080000710001c01c004942c01183c2c07130f0440c409140c44035184280c14211040102031541045400c44201c180074a09804031b40c036200d0030035229a00122541843c14104801c80c20640001400309080b2090713031000032241c1d4408661203108020100e581c051444201c8212120400e031003007203600240078100107040200c803107009000150340c10894141401607131a03860a1001a260484004030005000001c64401c200404a4000d0000d00d80c1050b5083c0240550001d80100c0d201d0030b62486240c1000c1039101c0c40100f141d5028261600316500d907000c10000c0103124242c18a5603800b000749000c00c4903500d441c040512107507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 540247913 1250 540246663 540246719
    0x5010e070602100f09030f0c0c1a1201090b0d300e100801051c0f021503010906081b0d0f21170c07140c04020f04170a0206031b04 57
    0x103c40d05100f9034006003a8001024900451351010a0780a00c03400149061030034000c014120901c2c190303013400c02c0c035801035402d64a09031030304000300031060007007200f144074590340600c0341d881d43c149204442c0f0b000201c951008040d1909030005400c0101250015185034111803a01011078111401801c1c00c0c0c9002d0014140a42c0060a0b1070300003001d082c44c03801450301d10150360400010554a8141c41010620180100f2450b0100075684034181d0203294042d11070050383c0c100b00061a0303070f6003080c0501d61f065400c107000410840701c00200c900c0003580d20f212540d601c045036000d001c1c03080b44105c41030b10228815142c07000843d000d0320080c0a0540306130755180c2c3c151082d400c000c020100403064042d040e8450381c24020000c80110036950354a030050f44040a40a180382907510b00070110001541242c0007107aa020014000c1c1c002e0411180c070078244000061140a026464803c2c526009510132014030108000043c03500d00c101c100103581c00203500e01611074014615000c1d00742642c2d40024030b1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 540249163 1250 540247913 540247933
    0x1012120c080a0306181a0d050f030a0e0310050c1608090a06050a030b03010203190b0a0909060603230d0302090d1403041d040c06050a0c06140402030606060c071205010e070602 77
    0x882c1c004c040f07502e41c000400c06c0f80c03100100000c03030090507010940744035010b030380100ca09000d02404074400b0300d89190103d82d510340803100e000d07103078464101d440d62290240807080906d680a50007241d100d20f0420102615040e8070003582680d02484810948040c00103010044d102d0b151b900c569000b51031a920340320b44401c08220002d003036031510204140240d00510500c24a200411100820300780b0394100454003140c168041560b03440c3e42da11082c0c159050121020910016502510a5034002d1103942441c18000010b54108103980d40070b0581907000ca0401e01902e8400c0e03000d02100070f00100960701c15886915412282c100c00102850b03079410020701000301001e00d094915401c2c0c1071107101c0003546030035290343d44406020311503078061280008010b0300c882e205454240e5034542c802010810800200070a00910404a50481c004d02c5031b0b001081c80c44c82e086050320b09059241740202592030500300c07500c10340001202d04694a41d241e0381c260048000c24080350000d03040b543c0c024005054 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 540250413 1250 540249163 540249179
    0x302090f010e07020106050a05040c030e060a0902030c011e120b030a050f01051006020706030509150405060601030606030515120705042310030807080a14160b1012120c080a0306 78
    0x3000f50410041da8035242d4100804d80742e031180d50007200c004440000c1c8089900c1002e0300508004050840c06004403c10009051113580c4a0400700b402030f01121071007100d01e0019914495003054031403d280c907003c00c0042d01441016407030b4500203881808103a030450030010070326007943e120003107039260407801803401181024401c41e41d00942d50001031003007030314000c00651142c0c071740c1c001c90b01015212000542c12900c104030084c04030030821120880c40c40c0505045440d04025288540040c0c00d001c00095010f109010351801343700456405040c008000c0c007000a0038040c0500251203000704c00c00019503903100d02c25881105050742c0480c200490035071081d0400c640040c0a01c95441403a0018070115102d80b090f14006d980c0704801d10760315000100b06441041d90920a1041d40f0000242c0c240501202140c010781e0390b1043c11008500c0d103c9607582c00c0c0d220060700900d1155245151104080f5001000e000e601710315074200f0080c90401ea4642d0800e0394000c2204002003900c4610400040c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 540251663 1250 540250413 540250439
    0x111209010b1c05060f010f05010c2a0518010b180d080c150f0f240a0b0a120e030a0f050f0a0206070f0c12080a0b1801061b0b130c0302090f01 62
    0x1000c2c807a03007031150350704003d245844447d0303d0152504006995028004000d200d040c46404a000744043c0b040d40b00ba1003600c810070007100c0c01940d0054071040d0000000411003204281640c000542403810000d0001c800001030942402c2e203540700300300c1c0c0c030588081381815000b8019441c0c00005408540c03d140310500161401419030720142100c50208540700980703054940d00003150f45c0b43e0006124030040702c00c4200350354811196200d44140000607443c0808802410f0035001030711009803802c3d141d5034944c00c8908219144025400400100351501d10640d2001580c0c0b640f82446800c10340d103d40d00071540e030040441d880150b400a820710030901d070000c400c08040d00e03891a0620400c40c0396900e02244c0c4501030812418801050003044500c5083d030444d003440d8501030300010082013070f204800361010080c48ad55022072125038a6000c4012812140c00500c0c0e081044580551a01e20507400e8402d1654405d4501c0014400040016503900201c04c3c0580586885040300e5410003550384850 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 540252913 1250 540251663 540251671
    0x90f020a0602150a022a070f0b1303080703032003040201230a030b1c030206010504150b0a0e1503040f02040b060a0f200105010b190201111209010b1c0506 68
    0xb540c000c1d00d441018114040038583d00003100c0030056142e2001019503032000f16801801a800c0310302201404010f10001000f0b41100d4028180301035241d9210b18007507040c4141c46010040b8400c400c000d001050403800104074040c401d2400040302140e5002080303101c042900e40580001002081c0810f40d03030310070701014800981e5040700e1000155200e02404a102d6400710b6001c1c15200c01c014512644c5980d00043e000c40000710070711040c005858000c0d2100310900600c0d202ea480c00c0e1625030a408200444c00c2540d030740e0100725203040c29007501922403072480202254400f400b0010400145c074007c0c007850289115122a00101c84288100400e03207000110007401000305100e00e0015543c44880701200742d070719080a440c4c42c003d813200d012040201000b404229800c101c000100303c4440c4000700348503c81c0707014007400202103040882c20790302503502d28040e051051100280111a990401c0d4002c1d14890001940d51282c0000c5184226130b8030300602d00110521240303060000c184996540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 540254163 1250 540252913 540252917
    0x7050301050109091e020a020f19050304170304031e0501140c03062103031006090603020418240618120209040b04150603080a1d010906051c090f020a06 67
    0x290360416000030030405040c803800240b143c0f40c0e480c14801c40600c80c1c102c030500060310f00a65036143c01d0038002e56101e92644004400780b02c2c440f080030180c1c0303102e1450028598040061440c1c6484c204c420050102244490040350004000000002c0d118110014027003c07001442003405215003403190031181818a5030b07051810346000c0010303100c1020100c1e544403608688500388200307820394a042e0141030380caa0110038032002090003000b14500000c2c1044501aa07170b5105844c2d11414110140d0103140304003610f420102c1d00c2c81f2420440d070b130007c0e11162442d0307580c071a41c1da4042c211016080c5866002c031010030f03071140d4901c40700c12036000d080014180c1c0c0210022000c2c820783c00308050710030040c00500300d8044800461704000c900c240d5181d02c2d401c60031050180381d407a800d100d07400380e1200d1004404035116503803440701c4000c0600b00324803001e016140e5119043c50182c00340d806900090041160385040347c02c072310089e0554403c007124140a800c0c5404000018414040203002c65080081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 540255413 1250 540254163 540254167
    0x30a1a0405062103070b0901020403061d073b070f021504080315030d1e0f170a06150302091201270f020406170c040b010c06110903030c10050705 64
    0x68a0300c925101015102035510f081881d404052060781c250f009850008140070500400d000360100705401510a59004070010440036000e11100d200350400d18030300702250b400154041080f110600c4020546000340302a5550010850078500d40d92407201944107645040c1c6400d10444030b0b4480d400304030b00303145400180780c092003460410490840c014002070841b4000400074500000c00c1028812245000c0e0840300c44c10400c500c05002061502c0c44410f900c0c90041d028881a4840c1110a1030400070361202c1c06000100c011a44801600810303d040903501c0c1c13480000c8124008034030100c2403903d40d0300161290702c0031003041100b41106805c40841d0703041590302090090100008002100032034541a65440c4a14040244052854000e0340c002d20702200001c1d181d02d485404541c1c220050196004400c01d40300f00401c4810020300305e40000c0240c4900340c0020b0450740500c40300c0c1e00c15420f182c204400400000c0c0f4580c460b00a5078400d0304202c5240300c42c0e006a0041903041406810414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 540256663 1250 540255413 540255421
    0x5090c03210906090d140d080415020315061306090b0a0e010807090503100b090a060f050d050304080a031e020327190b1e040503060408091203030a1a0405 68
    0x41d811034001002035020300001038500c81c030742c0c0e50008540c3c0104019160620440c41410010a07102250765180e840780525222103a0091090784094411075004200c0070b4100e01400e0980029003009190304500360684c02d001d401c0d40c0e43c4102500107510880350f03607540c16087c008010150042c50340483c400340010b0110303416554110308160502c0c0d801703182078032103559010011241da030100c0d03102c15058041c45041c50104152a084031018031000d03036251550f82c0b41c800e900022030300c95202d14211403400c0c103024469443d0101e5582d549070f0040d400c03030341065103c8400d00c4c1441c0038408101c5c041001c40c4101101c0c860020000d409406440c00a5070901c107004004803072072158103000e54151006002c0c00070341540c464035004280034044046618241d150b5847d80d0455001d60302c0454007400c400b9822154400000c1185d040c0c41c0d028024101c1c6844039654001150003125140b5070103080980304184c0714500704095485418101d1021604034020590140444200ca02050096007490104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 540257913 1250 540256663 540256693
    0x1e030414090f06270405030d0c170601030c09081504050114220303020705011802030c0a0f0308031003080c0c04140105011b03030e0a210201050f040803040f060f05090c03 75
    0x1c0790b0180d41500d5401005242c64410301c0c507a2260b040c00c4c0c0403070500c076003070209206002000e8012540502c504000905151005a0704081020020784900408070005285540f007030b00b19100000701c904059000c2a102d402c03060805000c2d1103080a100c005804000512409010b0700006c1c0038181a200041d04155028141064607480f4201c0d000798425034100030503102c1d82c101c5442542090003040480f00c503d8455054146a43c4164402d00c40c12210440300c0c81e04084100407241540150300070076103540d855817941d800c000c280c91030888102a0010109a10000a0541c1503052010300184084a81040100c3c0e10302d0015520a0b0a840018025660080490402e01c2d00e40021280501c21914085000d0842800300b110107010b480541401c01404100f80450703012415005000050102c2c0100d00322078080358407041807004c220100e40400c213540001e5801c140145800e0f100c0d12800e0f05c1e60019510703445051045280c3e184100090076000b0300840154003011800342400703140e66149 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 540259163 1250 540257913 540257941
    0x90605090a05270a02030d020105160e0310020c0307150b010c0201050d09020a17011b05041206060503121908091c0c050f1c03091509051e03041409 65
    0x1000c403000d0307035030011584410000b05070301d51450543e40365a84544107208159100c83d402e40e0102d01a02c40d20102008441c0107003d00c1c0e20a501422801d4610041c000003111305a01e44446203805005441c0380c2040b0182d640001c00e512901c250085a541980c3d2074000749c100c07071611022584620b401900131035070fa0b01c84150b14031103809290071900c40c0d8403049128010065920000d601c5811000005065000444c0007544940040700801203035241008207403c0b80502c40030b410018400300828000f04003000c4d091002940a0361000410f5034451020903e01444a51000c54000c00807484010100a2940610f10b1001074502841c940c181032000e1503a80c0814001c40c040312400007001d0b0031943c45026103a0b40030360403604550ba20700d41d144603961a41d10369510208000c0d891002c1c501041e00034000c5807e125440740c440c0203008104a6404001e040c003840894060040c00100001c0c1c2c03a1183da082e80341c6002c1f034082d41c2d40318075021081181015088520703005501c42c03002c100c04400f030151 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 540260413 1250 540259163 540259171
    0x711030901030b0105130611010c03060323030d050f010f24050c0307020405010902030f0f0717190207050c0a08011e020c1c02071e05061b0c100201090b0109060509 72
    0xb000b040100c0f001d001641c00303004020181050902030000016410b0340006004d41c044101c038000c00003680824003c83c00e84405000c05480d0780c103090025444249e5511040140d00842420f407820803217981031003000d494069492030341840010780184040b0b40501c03418001001d110100c0403403400703056600c54011541c031680c0d1003404000309100c100c01405004490304a58014410081c40d07844080c0d01009401c02d032900103540700f00000040200100800403400384442c1c1e15040a95481c00c200c6d008401c000412845581c0200b03c07061000955900140460314480c1020b04451007020083c020404981d50142c3d1a42e03041034507800841e26400710850010404c514007603903900c06201e00c0781c6001d21284031902c541040c440d84003200795011034950305445450b5001146000744811214441d001070141030381c040000c2051601b043c11119012011154040548181344188000112110300f22441c92000d42d4441c207481040000c0e4548050243c100c00100700001c07400d145c00f10f5450302c0014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 540261663 1250 540260413 540260417
    0x70e060c1009060f02163e240304031101290a0b0a051206031c120b03060a200705030a230304080d0b2b0c08070e06090711030901 57
    0x7215038007805a5504407010f51813082600b55500c07140441090303404c4200349000e480014403445905481402c3c1c2c02200c46559051044110080ba0082c02c6820300d416401d48640c04140450642d80504460300c4200911303004c0e402240d207070311341030034003500fa003500c0300c500c19440e4900350f4440d0301c614107101a012101200c400c44070400f000718001c0f902c0440c86401c0062444004540352181551200c0100869000c0c030000700102d44a4a040c03640c0e0703442d828451228a2400c401220030584102c81006503914520b4002c9081342041001ca03082174019900340481503200d030903d84040000c0c100c1088030441c5401801c0c41c0843c1512500d407079000f40c421080c1000500d100d091004105114a80b040400039400c640e07807418036280503070030342d84042803070f004142c2401002c0c4024604071800c1d10585c1500b21402400400001c0710303040c11184041d0844283c1516403000c19201c200300403000240c4105041b040035428103404002180c50010858820030a501d101004000400301c20b031240c1030000c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 540262913 1250 540261663 540261671
    0xc08101703070605160912021503091f0b1017010303050a0215010803070b060402070f06020903030409020d0e16060518040f0c0309060b0a35070e070e060c10 69
    0x280ca01600310311503100003500700360606040c00b60f4000403800d48030b0035551030388504120640e1040180300c00404008069440b034180c42420703142c07081e444015544448013100750340d01c1c2010f5200b4181c0d07086409521816280c0d031228403260500344844074000c00061801c20f1400c00300602443d42d80d603041404010208080495451510350080210820083c01041c0c601d60543e1252203071130343c0341c010200a442002e082404912241002d101701c54915400200504051289480d0b42c40603500203100c3c6034051008220001d280800c0d44050a207641412401003103602da10b202c190314106072041c810308000c085520400020750040c1c11102d0060301c40d07034041035044517800010014400b072644400e41906100c020b220b0543e15501050060348540c20401040f103003c402e02980070400e0240c1501040d000c40d84c00d01005600c1100e01d0800300130002e04500304074189155003042101d50101024009407014410720540020b03025005010030f5402500300800308080302d941e0f0fa0308103404c413101e03a40d07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 540264163 1250 540262913 540262949
    0x912030109320702060c0910030902120d0302090301050601020c061b011416090b0c12090d08040308070b0f0c030114010c02060a020709051003120f0509030a080304060c0810 76
    0x160403158000344041d5144003070300b0b08400c0007498003220119a40d00c01030048000052503a480ca4041d901a5003000d418140f0f10210341106400501074200240d03404040c002040101c44410000145000d50326900981c403a51000c050500751a40900000d05641103000302110300e48030001034400c4004d585456a401c039100c1030265004108441c005100000b4101c204060415020242c2d07100686d1540c030510082d07690307105004035008801c440045500080b4018030b0819081c0060420130400402c4c64181070100e50b95801c1c1c551050303104942584010650070140107841403030940c0403060400581c154070f0074600c122160711050207034522016000c01840042d034403640243c1900741d4042d220030b41e40c6d6809880a035a81190b4400c8a180d1400c25001a904100446560b0100ea0703125503030a01070100801d0a48110b180760000408104d000e1005134401d590801c83c480c0e00c5401407802c65a04d0805040410603102803030191000e2001990a0240d07019500311080101c680410318101c00c240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 540265413 1250 540264163 540264191
    0xc1716030e092e0b0f03160807090b1c0911030706090311040c031e02041401110601030311120f12010e04050a11130509010b09011e05060a09150909050912030109 71
    0x143ca401c200b00c0c89801050340364800001900640c00742c00d640c60041c81e180203c61048413903440c200c81c9000020040c0d50100a0410000e000d00900e9540300c490303065401201c90000101d07503c94205440103030701e01500360300c00d0070309001a001520040c0381401d04541951618800442d60418943c0640d548207403040c01503101e41d0000207400d2000c0b201c20380c903403400441c8030702a4006001c0c1110036216a14030061030b40c09601003502d030b07500c10790107814035070304c4d588060312203064104c1e4040c142d019640001840c954420f0003051100c1d07030b80541680302e181c055041b00303800c24140c00c041890400784c400c0c000400d000055034860f00e0781c0169030140c3c103450540481c0d030240642055102423401c100c14070124103810341041c1e4045c603055a8041103a030b6500f0707201c0417200b66044503040c6032940358414032050400c60024070750031003c0e04000c1d02480d5584400304040800000007000034520030010720a000007030144d2a00600500010700c505440b05004081d60f10042c8240c400d0365070f4580c40049019 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 540266663 1250 540265413 540265501
    0x1f180806130c050418060c050a020a0813120303020d0615020c1302270f092509050603070305160f0e0f0a050402070b0a0c090e0402010c1716030e09 65
    0x3003c0030f403051043c000340c483d104503140c0f00660200c4509050140c0110700d40d21034401e8548014080c4d000f002d02c0d02c815200c01850b507118108010307207000301003004101c40c4c1203168065115442139500503610b010644980c000c0358800e400c600030508131000048885540015003014010b03003243d0442e004415005c09400910988140703199800074800c0006231044030151f99028040c00341c603071450b960034100030010040d0045030100402c203800406600f4220101540d120035031010f041c55059152604001400364004440d0600000c1d04d030b42c100030300071a540030000c0c0c016180d41030419507031035500d001804090940b0441401400e01c86c44a0501e980c45501c1c40004000151003150b2325041070800c507001e02412140100c03410300340070b0401212031155a0503402c588515640700c4c05034130385e0350044504c4006100250b901144180b491b8005104031030050201c660307038003440da01c6e840c00340c40c0103012003180c0e40c1c006110390040070802c000c03401c0ca4807820840c14442c0440221030304880d41e50780185 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 540267913 1250 540266663 540266669
    0xa06030e0f0709020903070824070207080303040f051c0f0e06040510030e06100b04030303050711070608070f0c0b010e18060106020105060f040506150f0403021f180806130c 76
    0xc0c0b10700310000945514035401803803158015030a4401c40764443c0e04082c0d882e429286007202c04843c10891459a540c85041150040414030607120324a0b62160700300c0c910380080e40c041c0e4540c1148801c00c8101b040170041c80391150200c848021401ca00340708080c0400041c40060814800400300c103a0321903a440782240c001c0e00005120404100029a004000708580100e64400d4130654011403c0c3c50000e50044080f5030000c80000d24041c00d560341180a03010148c0308100380156900c1c0c03040e11074001d1000390042c1040c0d9580d44103501d08040010700c03605410352440103000040c1040c00c042440c5c0b52400b810744a400b1210401a141c00801201070407002e0100745280c040c2c80004950280d06402c6203010380012a00d1908601d1280b082108640c2d0948400b6070004598580112410307001015019905d25044083c0c1041d6507034021515014283c0d00390305084000f02800c05410b80c001c00803c0c020111000c0c3d082400c0e0801542640e141c0000d005140b1003840d00300203504010aa04040c805 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 540269163 1250 540267913 540267943
    0x201081602010b120d0216080c0609040908190f0f02061b040308070b240310090309050d05030316020109021c170409090606060e0a060e06090d08070309140a06030e 72
    0x104c051a10a050300d551380c43c0e240000500404540c2002c144104c1c54080a8850480c0541002903441c0c0401c0001d92055039010782044e1180c002c036020a8400303010740000c0282c80d00354041e030407620780010301e15403c01941c1406c2c080c1c0c161511402c2a070000c0da15500030711107900c2285150141302010218011640003c260140015964042018490314903019500b4512140c4080f410030003111f488402d031500068041d030110b03600b03a0300e01206400400100c2d000b030070101079942e104d801055010041c07202c1500c241d84000b082c405c8482c0d1900d4110504411440200318141041e40040c006801a85040e080d1444602408044c031a4110f009100b01c001d0204c0c15644560382c1841d00081c102d0030300180c580e2803406c2400100103005400150084d00002d000340069402c1c00001d983d08048440d00e103421001c103001c8510b03d610f030000070b00807880c0140c4549813584c0c00351900802030b03003598200701859240e8105d84801520350010541c1540c04608000c21a900d090302c01c3d40c68121200342d8011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 540270413 1250 540269163 540269179
    0x1209010b030a080d0b0114121f08070612060f03080c0313060309030f090e0720070816150c030804030309020d030e1905030a0305090102070b070813080a0201081602010b 74
    0xc12011600620b08113180040500c810030849005466a2100d42081851030310308000104117000314130001580030480340f1040340c1d0142603c101d80400541c58000b4482075000b20424046140c216082c1100101091414400e942c102803030305403100401d11005002000c0444c60701500a410b00c20741c0c0d003189030f43d01c0c4003820310b43c0c802000700601041e01c130540200ba421441040482c3c82041c4d4641550890800d071405620b6509007240c1c031079840c24507549080d102c01a08400d4280610a110003050a48000c0c600000b42c25121a8a100180e20041c0c000016501203001d8541228010400c0e03a050b0a00d28066515070405401810440200a5100114010240c201500702111140101e019900340e0885002c904051410480d50b0103107a40c035500001c02c58000034455801454080c0041c4103456540c1d5898211103443d80100030304903064600800c111128401a00071130300141424070091440312103a0b00068911140601407095084880120740e0380c85000350070400c00d103580070b4441c2c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 540271663 1250 540270413 540270433
    0x306020c010b0f010305060f1903020301091202070501050a080a20191d0a030213110a0507021003060b09040515030f1614220f02030403020d17010b1209010b03 70
    0x5000340382ca021024440d0040d2240303102e80d5446881100d215040292040d101658031204000645952111000f0380007840d44022006071002c0c06182d5a151080c3d220b0009501001c90103030500d4400d80009041000c1030040b600c03043c0d40107040176040100382000050358020441000b0240d080c03000b2082161100003540d00010950502c6080c0415003a50b420b42d6280d500030f07040d02c2070083d140f5216446103070500c0c284090326004c003221a41414070200000c010514400f80e13003540e00f0200d108804504003058036000d40c1070262104161210350310b030400c480c4d400d003080700302c0c0b0b40140b40c1494003450f500c0c130014044c0b030300035003042499150007400c4a10116542c4409a541d0854080d820042890b0490000300f40c24100c0b4464500c0000500c5031800703218056004454090806400001e1503d8040c0004851003d200035030056002c0c2e805404070030b10700035016080e0001c42086040c41003c1c1c20042240c0c034a01000e40b80c01400c440e92041c05e94481c000d8585c058502107a48640c58041c42d2416 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 540272913 1250 540271663 540271687
    0x1401111803070b030603030f0c1014071215121a010b0a0e0607020907050711040c08010501081503100c03020906040e011a040806060f030a170a1202092404030602 71
    0x94031103540480072a03070b0254444208500314041602c84a415500500001108440301009002c1c5207103e80c007241e0600c507994250105540468500241c003540500a2000d1594080281001190401001e201070031030703542141c0ca074000d0341c80345c030314441a605110020000078440030011410ba8586444440d61502400780b442d52111088030081000c800c8521702c642403800035a10865001000c2c0c036600da030b07005005d8610b507011a00883d2002840440d4036901d0380c0d688507114850308940c0e0741011540c10440050400040a4417480d11441048901c004980e0009aa0103510910301c40205880105c0002079010740070b440601680918041004140008031420351412a14400b0f1a40c1401c01100348055041c881ca028455154009000080c207900741b8010021009402070211006203e0603101e5401c4400803403c1588078820000e100c000b12544445121605018140114985111940007404c0340c02c6101070300c04444010f0f2024a002003021054030700564201074159620f544210070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 540274163 1250 540272913 540272947
    0xc020d0302010c020f011404020402030402061e0706231503030c0105010e041a15040b0a0e040f031808070e101e06020706090605090409060e0a0804050f0913140111 72
    0x403d00113220360030808540e4981401003008901c491881d140340340d1501c0e024013019610080041e0780040f0200048505186045418011851142161030300d0b80f4451500e1415240105d82005e051040348088501c400b80640005400201c0c0700c01005522230902c0100b8194003070080c10071341d103500c1e14000041c0f003190b1405aa00c07030340c8100c4404500c031a0181c0340c50081c1400351100c4005221705000c0c1c24007030500d0b034424084003030000c010046480d0383d4542401944000c44040b100e400390700001c4070800d034100080201625205070819662030030b01080326542d4a6511401200070a5040030899206502101a000e8046000f00002c0f00c10048203007403040e002071207407000511410900040d0980300d0140c107000d40300030303540745480c01c3c03004001c010142c448500141c48481d601c80c82c0ba995501c00300700d51355045218144c01a02c540c603001c20018142d40c484a00c0740581d10a8041112031050740031100241644000c001e2455504164880c0c0104041c3c000400e00500000d428140e680d03400c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 540275413 1250 540274163 540274181
    0x41509060e06040903120f1b180504020c0c09040807020a03030c0c0f05090c0702030c190305010f110306010503040f08070305190906140a181707060c02030714010c020d030201 77
    0x42022400e8561500f40800c070b961100020700014480280c3e111035500e90703044800030006c0710b1000b28a8200c00003c601d003d814100109010510f90030541e44a4560001c02ca40200340c1103c0c214103260042d0307551500c0300244071025122714008400a401c0004407415039001076000381506c02c03450344901d40035191170203944041d68150f0701c8200c0080d01152000400041c0d134009004c032290383e11041d00c002c6864101d02d40c2241c5c5401201c0d2503002e151900212804100048a0020b20261850602600f160140c440700b114441c14000c00e4001e001c480402c6030b81121080c40c01a907669254100246040d03424070f001000388000161050602d60b00c035000e4100c4014070b0040100c10584007400f5140d074600f500c6200c011414078504038689520840250910b07860781c2c2413011031507040000000e10402c242c0c0086810141c460400c00160750104554405000c403800c2410700429140c00284c0d43c0c10f143c0c45031954004009480103c81e912443c40300b1502680901003062040710751034040c0c042d01703000b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 540276663 1250 540275413 540275429
    0xf09240b040509130507180f2a0c0503090918030309010f05010603180b0711011803020d0f0503060d0305040e0723040b0304150b06120f0609010b03070e04150906 71
    0x2030041344485100344840000315600c40020601380340707005070403c0ba0320218800e60400c5943e5403603100c0550700ea030003207155400c41c01d288524000c60002000d2206003500216604101d0b0540980000482c008200c440c0240112080c40c0c0341e5580c0c11181e801c0340c00466590b2000d00001c8103110310108150009200241d43d8402031002e0380e03c41208900f1035681960054490400c0480c0c4004281040061500b000345c074604034103c041a4803a060a440d90508000a5058070120b1401070681c14403204030351302100c0c5009000e0f0003900b0001065804094070343d6120740f1300390100d00c082501810440c3c00400c8292004c0000e403910174009030111000c0c4107001460310800c1810560f0584160482d410b03103c2c4960b46a041d91140d4650705801d50020701140038003035560b44104400d0380c902000e4042244800c90b8a0128603301012004112000d0100390003100854014407155071b10710143c81c0d02110311710f08101d001984c407000401400d000741704400d03441f07003003131000c17075500b117542c01c1582036503031742 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 540277913 1250 540276663 540276679
    0x18030216140f041b020a0b15010c060c120905062e1424070203060f01060c1b0305060f011d07050d090c05120106080f0c0a03021210020406080601080a060f09240b0405 73
    0xc2c096405022543c88c000701c1c0043c01800c1d0380c01c0041c440c1d92010028901c2c43c07411144080d442c107188000c0320014103040d911680504204004a21074500f02920803200200703501c10840d01510450310b0420900aa503075a102020b03800403280c0303d60204a1080800015422030907180c0c00007541142d21001003a0301a0054100190240d000070031290704a03009a034550328510401d4680207800d40720308604036108003038203100102251041207018059841c1364281d0b4540c0d450240e02821618000d0442d80d1074841080410203015085001d0351048000000040f0301080381e4600761808103005c4e003046034003051101034401403000541c84041a952907004840305d0326002e03a0b0141d6a60300c01c28030030350300c0110000f051005051845141c43e82e580d026040f120f5401c0a81000750582e01711390000c100040d034144c2040701c07039a40b00d018960401400841085154104080751591800380c0c01903a04060b01c1b00c044191041c82e244620218481c4a614928000c0d1904060403e0780d125102d840e1064801c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 540279163 1250 540277913 540277921
    0x31c05041a01050a0b0c010e060c0a0807030501080d11030c0d020102090f01030504021f0918090c0501050c0a080f0403080c070806010e2a0d18030216140f041b020a0b 73
    0x7200505034107983c0c0003092808410700e82050a06258080c0107400313a41c2d500c6525201141d00100000707805061305982850b150341d5904801807100d41d00518540070541020700401071b000000c00e03c82102d012500e0a540c9014005843d60b10b18440c85151440d60301c580103501052075410b6002d06040802100c0282c540602d0f54011819100203440203540080d100061124400c59901091081030503418150324031940c0d190075a4100602d991101e0310151500c200804000410030241c001c0d200908001e07007041120103009640d8280c500008003400c1000900c5030801c1c40c0c03102541c00956200f000542d4408206800d2502c44e0b03d1403050385c07540c0c412070b000411045081a00ca500c90784144140401e040500d1211f0b403100d12000b8200c140c00b200400403801e01d840c050140f459130109405d40031201f402c5070710b0001e01e0120210304040022001d550203000c1403069008491704280d013259220a00c00e050b600150003050a40380082411140d42c0c804880c4980102d812007030280203005440007039407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 540280413 1250 540279163 540279203
    0xf0807030b0a090b0406080607030b0301050c030103080a08091f020c0601080a031707120501030f1101050a0507020d020f0a170c03010b0117150604060207170a0b040b09031c0504 78
    0x520056441d50040b03081c2070600041d540b0758000680c41c1402003010485690b580005030829506503010000603882c0c0b814215541001d015164201e0481c0000d0743c51985591201c280300d01880f003040040080e9003000c28001941041540007041c1c4000600c0b03c50704441d5081c1c0001e510184000c0307102c0c0508000010340c60000b080f411032080d05501d448249007e010ba030304040f00801010b100c2805084d610800346100d8034441ca0780654828a00300c40000c2190415103c00f0000d00740d0701c2e0402904009010304694048262811140e055a203545020f9071031000400030387c0e4100809400c6420b2030030028406e40420606008484e00710140c920703e8030f501051600761403841d590580819118100c01c0181c0d07183c076407c5036020060714020042400408000380055115900c0240140e102900602c07075076002c030407000e01c0c0105800041071040b880d66103600b19001c002b400585070b40400800984442d08c14011580341000c4401400880107014140e0001400140d402b41c900303000e51a02802c0d400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 540281663 1250 540280413 540280421
    0x6120603051b0a09062d080a0311060f0105010e04020c031204051e15040b07110a0b060a050d1a06030a0f0c0e060103151a090901030f02040b190302100302190f080703 73
    0x86101c4080001d41c01908a01b00782c007036a00c0c040c011400c500350800a0540002d21000c110036100341d40305e80d04208010001803030710341c026226480c6174682c2c0f070040280383c0c0c1040c05140e45c40401c2d00c0240e15207801c00c00650440c018916a00c940c2901d4104100400c81d0118000c01e100c03041e811f01d40103d14501440681e40d00070314024090003130310300b0f000c80c0106414400c203170741c002e01510f414034011181c1c10403a402c06505400403251580f154060210341d1070840c15050180100f030b204441d20b4070080e2980c07a26041b101000c1015048520301040c869103090080d50300140e0000306580e407805407440c00560039204c600c5840502c0b040800821100e41c0301e40603083c41c030120b070212002024100220b1082d1860f046e0340042600c881084103c039036440307441d9401d00035401058207405e403e245006010540e10b401034600d20031038000860304120150081501d003500e80585440261a4011000340c00a00c1040f800d607808981951420040320380c49600105084881d0f0340300310f00ca4882d00790660a803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 540282913 1250 540281663 540281669
    0x90303010305101a030f0d03060501020f100e0102041a04080607030207110108090f12090a14030a080a0e040501031113050603210403120c11031606120603051b0a0906 73
    0x207900f09005420307550859810260104641c0071103030100300b0030f40c000203140c001c040100200030b07002010b45001da25098841d900007007000b8001342181c114294141034484241880c68124a07035202001c0326584000d50503070303015029004030001c0c2070503c40d4180701d03a500180b0419a180c071400c80000c452a00c01d00070380d0f143d01c1c1d005000c008010124401540c80800c010020f075154400c12441864000080041c51a14000004425034030800e410078041006c1c9941c000072a012036800c42c54507152000a81040e46941201d4401d80794264840b04482c1c440e0b0510b802c1c1c3d4094107110001c800e114816405e8117035003c00301c841c5201d1402d001c0c060410340c0e07411102070764503811024036204400c2a0708152944000216640f40c5407684070b40d0741e145581283d948500c00107000c8a20f003000c005840000284030002280100941084d41d000e00202460f40d021708000c0048400c04800403c0c0181c100c1c4000e560b204040d241486901080b1200038042e03030454510070a00381c48001200c0320f0610500c2c1c19 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 540284163 1250 540282913 540282923
    0x60909151505060d0b0d0822050d0201080c0307031808030603010b0d150903110607020115080106210f05010f0b04110301030503040504390314091e0708030f040e0903030103 76
    0x18144c80115004c02060791400d01c0790441440440b0704000391102e0000c0600d280d170919039040300e49090901c0c1c3e00e64141ca810030341c0556042c090407409030b80c125003e19400504d19140c076981ea500c0140c00c03009002c4c0e055440d28081417802c038003810000400d018621912043c2d000700704034400d000800c030401d403000c00b001d404c981065101070020b0b01141c101e12480c9010741420400314484040881c5017540c204c4031503005075920003c0d54440034074172411070b00401c40325009100050070300344004549014181c4403480c01c1c4006155004005a404c4084010ba42100003002004500c0242502405500c0801d5100324545034100b0081001541a82e05894100c0c00840c01d017810281030200601300b0300d1207618089440713151b107c80000361031a40032400102c83d0798001d529164090180503585c14804203d4524100d004001940da000217150001c100039500700c142e88054000090704110250b04890b086000000c0c0c036811540e042d00090048640382c4502200ca07030b850200613a120300080c000101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 540285413 1250 540284163 540284167
    0xa0b090403090510020a0f29070203160c080115090b01020a05060f040204090503070606030515040f171902030304020f040501030b0a0b2b0303050f061003050a06090915150506 77
    0x844c1400d42000d02504204d0040318503440160710b85150030400c0c0d45003115001e4003607410b9400704168001003855200003484501103400e20710000780d12801020489803a00300001084c1092021000d03908004112010080050140040e036111125a9901640002c5400d00d502d0204c69440003d0805441e40c2040180603580c0f603007011043c0d503420113031040e40c0c440e03218500000442c10a000a04846100f0b84000034130b54075501c4c001d414030801004d445800780010081102160342a002150180e40c010304500a2665501c1c9a02c0c80f03005a5403121a11340030382e825006004d400200843c01030307008407407918400c40c40c00704000a40f03000740001418900b456000c00e80451941e0015030035820010010b14101c1003010444180c0b01280e00301c150054541c0d1011420b041d058401d840c0c101c1e000e01d40c0000315207010700c042441035110343d65a40c01c0680da940010a41d02e15035001c8005000e08600a2084134190b00f0800403450440e60b008840b02e282420b1070104070b00007500001220380c0902114 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 540286663 1250 540285413 540285419
    0xf0605090c0d110d02190f0c0807080a0c080c0106050a080106082104030501020310030327211b06021525020114010321030b030a060c09030506040b0a0b09040309 71
    0x5020f041050401410071405210f0303260810818006000306041241c0d5802d580c11100c64018a060489841901440080440000442e041300116807010340c203c02c5441c5d442500180c01c40c0d102c441103201503c492804100f01c0340c0080190003a00c100c0c2d00c2211070510160311034035510f00302e8810b8407980e4165803000c0a040f00c0014000381182d54114a07000031400c6c10740d2520b416083e64022600c007484051042c0e41401015080250b512411201c41810000380d03501d4511000c2401c02401480a60380240e0b03804001c21004900e06008140d000d91064035180490700842d50703254880c020600580030b900f11422000d9900d00c0f02d0340c03240c3e204028540d03603110154050848044121031a0045540760703c4034401314007041589034001c1d44181c0400f402c000c07038510443c1044400c614190101402c00c80340c3d030340c160307800a00b055240c2d81000c3c00103140019405c040c0e545109607440144140554000c22080c400075a0001e0320904d82d001c0d052051651501c1000513200080300c00074007180f0100c6c414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 540287769 1106 540286663 540286687
    0x2060d06030303021c14070e13060b030601020d020a051902040e0f1b0a0b180d0c03050c010305011502030304030f030605061602040c03200a030b090a0f0605090c 71
    0x8218083e21429146e8210401802c210100042140d45501640d04c401c803e03003032100440010880c55540f03a0114505070000c070341c03847c0940034500080701c41e9800401c11043e495880340142100302c5202c5019440514807030016038000b40d49000801c043e000030040240018648002400100707051b036001c0008441b01040b444c020700d2420420000042144190f4441ca000c0403c680c02d0a20f43c0d201003481000812000b0f040c0e58401040003040c09004501680540002c1c1c0e0240003a130303220841c3c4001540620030340c0c401a0300410000700400c1c45645d001c00c03100708600d00400c41c217984100041c40394112100079060107030324580c28021440c0500c41e102c00c007245428284804440081c5160302000e6160600d500d0810005109110710b21a81c00002e0040340104001200d0a01c09084c10091804d80c220b1542e00e03181590225440c80e083d403109120b5811848510300c0c0601d03003069 = true := by decide +kernel

theorem cover : BRFrame.Cov 540107913 540287769 := by
  have h0 := BRFrame.cov_init 540107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 540107913 ≤ n) (h2 : n < 540287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
