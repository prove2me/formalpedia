-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0761
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:38:12.981607+00:00
-- url     : https://prove2.me/submissions/79946906-9982-473d-9106-533c263d5183

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 136690647 ≤ n < 136870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 136691897 1250 136690647 136690667
    0x8030909090d0804060f140a02092e200a05100501090902030705010e0d050604050c0f060f0f0a1103030702071707080c19050d240203010b0912011128 66
    0x140d0345403c02681d580d030355100a000742d480300013081500d0340884c2c1014429020200d120310581e40c00103803681c4050f07080214841c402c0862076000d51100050f810007100040e1210320741c51460901c900c1065950b28a400c1038040c2c4841c0f0503250103000e440c44c040140c04141c0c0c543d5100500d0301448241d8039842100d088410300040291705a010040411840d4051181d006e80740c40003e11841c0160f0046d1038060030420308841c100d8450308025203e5403545010207180c3c41c042d10a031816424540b40c0450891588181111031800d84d601040c075410b0703548100c03098004a0800e809580d101d05103000041d50f12071060080e03074082c4c0c80c010305595082c0030014070b050032940880c00410010401d54203110082030381010316001044024400304994550784030000c007441c45600d20f604507880a01480500462000076541900e00410040100d23500c60707c15100c4246089600d603480d00c02904425006004030300300c2006003240429800100204912800c0c0d00c0244070302c0301da0000601303500c11100c250328 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 136693147 1250 136691897 136691923
    0x3020916120615030b040b19080d08070c030e1c110405160507170d020c060a0e01060608010b0c070f060c02010215010308070f110a0e15030d09090c05040902040803090909 75
    0x81c5143c1202a1081e0019950210081e000042003a01d880225100280d04da0403144c098210900800501c070f01000b85070452402e61514060504003020000c018546855014080003c0d00c1d0503201d03035681303003a03021414261614480e01c29126518140e031507441c02800306c6224901e4080050400344c0b00c031a9034044038034a65203980c5458126601c48180c410f9441e010f0701251018051000e201e16030344010310180070340000509180c81c21049550584400d40c10410b8a40d042800c100003254121039407034195582c2ea402d1545030304101810320b1400307a247d070040c001a21000700c001113031034102084e610014000c0e400e560300190200d1100c2c600038020b01c4010490721040100d0341c0031070b0040319140e548a10519040001600c004000380381212a50445080d4182c14005c1c0400d440211600e00030381b400aa010f00b503511205100500000080d10030034480e551103000c0700705160300c174004a402900d0500411511207072500c0025075207030403804d10180134068a80208041e1b040018014030810700c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 136694397 1250 136693147 136693169
    0xb1507032a120c02030d03110702030f0a020910030b0a020a1e11070605030f01140d08071a0112110f0301060801061418010b0d180b07030e0c010e011704020a030209161206 75
    0x92440120001c19031640040c8d80840144220030050740d051203002c0107600e6090041ca10005540100072402c1c501400030207200c04000da040000801c401c100a51080c0040c1005071180080350090780c060040b981401c3c08186004030203400729800549508008156804541c03240e500c0e00001c0d14644019990b08101400c11001044000300405124001910240260012a03002c2c1e0780c44526412241040f02c4004d1740c0a4840d40180852080070b0042840da00c0f00940c10415444400c11422905010350140705c1440003146203407401d4214900900c200e100070400140e50784000d500d160749031406284a41d2002d400451b80800060800381660f0410840c1c2d441d103011041010300174102c00208100b404403004403440442c604840c0b03644504200d850100e4040b02c40c2e0840c40c00c2070081e4820b03c3c184840029040300c070303990114030300301c1495003887c08000c40c0d02c503400050700c01c0c070290748000d41c070020000401c410300220f0000d044019005855643d0011700740d20500c0c060341d9541c054590450703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 136695647 1250 136694397 136694413
    0x120305090316060509160305030a0f03060506120406020c15090105070306150503040201030f020a081806010b0a05070c0b04030515060102070303080a091104060b0714010b1507032a120c0203 83
    0x1d02140e01c15500503d4900844801204c806c0b05181e551641b580700b542c282e0030200781003e0080d08103640c180207440b60b10307041110a080900241240c0540101c040c2101c2d12000000d0400c98107034101c0740d031001000222110b00c000705031402d20060b801c03181104554246000f04415500034025441580e00c8201c400c3c42144034064211034540005100760304168503086116001c083e00d100070030404409603100500c504d4614020041c02914120314112640700f54010000c80c0302140030744040c00024501141c0d160340500301450709200ca500124500c2d080042c2c0041000310014032500701903084045510a99603400041e03032520050711002d40803824280006400f030205d94841d0550b9072081c4468641c40030b510300810100d03009600544a140c01c002480c03424401e1a003e900e940001c020028804400d171900890040c488501941611100110342c0004040c00f4042d4100d06c00c0b41071514032181e98a0002140d2240c181003000d5540440b50001d41c10243d1107121200d103800e4014004200038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 136696897 1250 136695647 136695653
    0xf09080412030212070f0b0711071e0b0a0801051e0a09050c070609080406020106090204230310090308061302390a0804030501110c070509150904120305090316 70
    0x141c00944012011030280c911541d50010003180684800350249507040c0300303042203181c0034030348000103010001403180340400301c04000c0c40060710405031203010109895807426100c800499100940142e01c4d41c1d040400c1710948a640540164100d41c8104c0e60b00d102e8140031001c81001d80c000d800d207036400c407000d04000c1c8886000b54021507000503500300041e02d803010b40e49030502210a03120301100c100b5000982040340075424050b02d0060000300c0030462030070f8a0200d00b564404c1d54107200c5010030080014410040e80c06004038000822800c0c0240000b00b0b00b85402000d80000311201c40c4030308081100040d41ca1000d00c280c3c2c04540c40e24a0510000c00103100740c003e2240442e200c1c000c138404c3c0202c008030408050001c002042d102d4001c80da161070075403400d2401e480450103450f031900003e000007092410700084140071224142c801e84010f45600500d0302d509020612803a400c6000e1006000c2045081404001071241540d810407254503458002512441307200610078004010744180004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 136698147 1250 136696897 136696919
    0x110607080411120604030806100e10052203120e010c030e03030421050606090910050c04090903021006050f0d080c0307050a03021006060e1302090a0305030c0a03030f090804 76
    0xc0d004030303404000e002caa00300281044440c5060000160480c2c014403041603009031500d81c10131002c40d010541c80d00300081c001c01c5800038a01061040003d0f02c102c0c505c840c00b4104582c81c0c0e440e05042c104a035001c2111000c441003161004640103082c0c5c180b01c542551081d0111110120141d40311464483c294404a84225503609025414041017000040102e01c0311080a0a50328443d0142034814241c101740e17083c0140281494000d000041c1000541140420441c40210000c0800945601d1f9055000b0990040760443c00f41d4528040d800130070305400182c00710001040b10420701038283c485040c0304a06642c81c0c070700c0d9000320104920750700080c8445c0103800d451046c2c030102c9013821010b4448914201e403a000030b90241e000445c0801001c109801044003030403a90600d5140d4080c1e5401107845e041c1042041e1120306d41c0031a124580340d80e4401000010f68100084a40b0350705100d00c110b49a0700c40080c21070121707150003604001c0d038165000c0c0000c4036030056900e604051504c005c0b549 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 136699397 1250 136698147 136698151
    0x607020a03050313051507020109171801110312010e0609360312040303020c070b03040203030d050402040e0d0932010c05070b19080105030f10150e0a020c0c0111060708 74
    0x1024055540340d40e444040c54806d0700d104041690010851031180d040c1424855402c0b1740f001c00c8a0070801c03c00c04a5229440c803900e0041007860920640318450100d40d040d4002d1364240040d0384d084000004084580301c07070350750140c001100e9242e0700342c4865054407110125584445150141c1c42085c045d80e1550280c40141039003c0400d613844c184842440b504030a00469080340401c1d408101040c0c0c0c50305c10000100549000300714545142099000030382d41380510668401c078191204001011500c1d1600f02070381000c0b00c1784c211985191120409440050903018201403100440c0310340d042d4035010110310390492110194501d4810f0072500440d0340859521080d034080c0f0440d40000340a00b50100100300d912601103107100071086002d0003d00500069120780e2080c0d208031005100c200c00843c6400e0f84900314600010342e40021543c4180400903a40104400d0129204102c007032040c42d00180a10307280701c07050300c030b039681010b00549400d010aa04002d03658403c07400140614010b640b259 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 136700647 1250 136699397 136699403
    0x9010305070e220603080415020d080906131716030f0224040507050a060f0201050123042d0501030c08030307080103080310050a06020a0204050a0e2a030f0d020607020a03050313 78
    0x204d20141c8944410200c2da02c01d0348007102c80c80090011249156040c040e40c010785615280409060608001c0d860740c681010b40b4281040b614408440308010800d0b09140c1d00710741e06000191101d082c0c0308451120a0629001d0b070105000c9810820010310214528006829026000c0311000259125500344a00103100700c4440c4070785180440c142d5030703071034040f801007600750b0705c1e08240e1446040c003d09407072060740510380000548007502c040d10021b40740046c17801d0b019900003800c820105410a44100041c41e5440307050014541078820030307820740003281aa0700500110b2400c0b9036410416540e444100c80c8800024920001440000e1801d0011a00007100300f051001e00ca840304005580c10354280d108a026a200c2d4014008505040c05400d6012901c03400800900d808a11a03e4540203140350f420044903c40f0703401540b1402c08500340010100c040d080390005417095007034a42d1070045c0d5000c5005440b6442c0003c94151000481148003541a0303515421511695450718801850400c21 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 136701897 1250 136700647 136700651
    0x9090105040c02190212070f0305010c0e0609060d240302030c0603060102060f09010e07090f1503080f07030302040b1207110c01020706030c02150f0712021e03060a090c020309010305070e22 83
    0x1165004040001402404e0310800b082342061452401901f11030709811007006009440340d020000795100384c00e841000e00c0c1a51b480b13648880c50654000105050909002084400d004c100341682ca220101300031b4a100394102c8240d1b294910030000540411070381c050050303008100044440310008222508072251a00114102d40c2d941c40140c14024960050070080d03a80345402e520500040c01040d00300110b18900d6021142941c8844a4501c16000e51404042d070008491041520a90480e0001d000d0001c1c4183c583d80300301c141c414007401c103031020390000e21844042c5584000109612072840c9058002b808a5480c04038150090b02e0402540d10070740c0980c1d00c030032040300d007481d284a20400c1a50003114051410320000740944099200c100310403807060000c41282c541400340203803000c0140701c0741c5850341c0e24100010210400354010903103960a009650815079000400341541041c2604c00b0702043d03a03502c0d02100c4030b010340c86c00c00741e0021880c0420f151040310085c1d4080c501c8a10740700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 136703147 1250 136701897 136701919
    0x10311030601030e1c0e100c02030601030303150f15180e0105090714070605071d060f0c0307080403050105040b01050402090618030111120f01080f120309070e070509090105040c021902 81
    0xe10b0819824103a04c1c4404100c00e00b010500304d07d8001b4a0404c8a03c850514074000302058000c00e94401050000170b061698800301c0780d401c086000480402000c184817410442a2242c01001403000d0b8401c2c80c1c0082007803a0071640075003090388a941c059a41e0008500c0c4282e01e04010001c540c00050040000e001b000c2400d41d242e019128020010a40110804905801c00783c000800059100100861040740c00c03068001640d501d004460340e20347d910741e02c0e40c1c030341c178102000500318403500100500700280014008200201900014483c9004061040c050381c1d03500244020f0384544c00c1400c1d0b024008004c41d8514884802960409540c050700000d02c0c000c4c502c1c0c0007000381c0c2c401301c07062a0101f500f02c100a804102d441e40340780074240c200b011f0401c80c040407030119030b036800703d0010540350480400024445001041550020410012084043c2c00d0000c0054a694055038040740103c0320400086114141801441e100c48510750041c0850222514180308225461104a81c80070301514 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 136704397 1250 136703147 136703173
    0x20d0f020304080c07090c021509241503060403050a231303060612020d0f1505010303030203160e030c0402070809090405030a08090a0201091511120306030c010311030601030e 77
    0x80514481c0b44101c0d003d0b40d840c82e82c81011450801954454002c2e41c2c200501c01c1d01142d0701080d0b03203541941e400c00034071854541c3d0a01d07508001d0007061100e00c1013104010196120400d4511900543c03030f11241290b40c100020606407542c00423980a400f140040000c8900d8070f21510420803060005090b2a58010b0b0003400890a82c1c040103484502c1d441103030051040c4207161190304002c200c0310103851851010f960200310580c640140281c070010020300c04106025440c1c82da000c0c1c0f40b0300110300b08442d46e120b1801034000d400c161418010043c280c146030703040314040c206105100c00020010810242c3c2d8000300000380d03010300700444441c9030512052403a600c030504614001d61003a4042c60b11050000801440c080c0001c1010703402d5800004d10001507608401d130303401945c900380b04441075190180c5c802e0310244001e0080c2603003031140c030307480c17860104d0303120041c5004200807001d589000700c040c00110152004c45408600d0b050040002c03c00300d40c02035120000b0f241c03500082d00e4078400c00070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 136705647 1250 136704397 136704401
    0x21201080a0f320d0e0f0d0b070c06050709030c0524030a020c03070c051504140f1c1208060a03080904020d091b18020703170403020106080f030904060e1306020d0f 72
    0x383d1410700d81e0040c4800695036802100100340000c0a84d1407803001060000021803503141048050070380714414000c25041c038416070200c2d20b52900300b10f05000d14200a10020100c85180c03205450f040c2d54000c012505150540301780e2041d00d402e12200c107a08140c004510200c0d030010340b065a426900300030000c02988103001601009014518144bd040d02c1e00d4180b11310000642902102c503202004144910190a11040c00c02801610040b41550240300400c0034801001013422900d0360901013141000f039001c24400818070303640c2e640100c5032144024059034420a000c0140014024002c41d54182880e501a00e40c0d081c1324500420043d001b902e907040c0510001c4000101d4022440c07043c0940041c24160f01c0070000310140840c604002902e0040c0502c1002c0a555a42c040480114003414400d400c82c40c0505100400d90b00002c4200005540d241d22508000b40114104000004e510603942e000c18454a200c010956000c00c075981c1c1c0400035849405019580780d0340780e0461420800da8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 136706897 1250 136705647 136705733
    0x90118050a0b07060c08090d0f02210315120a020d0f020a0b12090307020901060509040608031912090b07050307050403060c03050a0b0409050706050915070303021201080a0f 76
    0x111040036541d4000382449001d03624541120000d0150319010b0107c05500065145d46111032440d1a00c0b180282580480c1400d080300d1101c4055409408910300000d031540c000c60050034070351a600c03070004195080c03100e191411b600c0c103d0f141d081507402d1030250800c0581c4620042c411040c540040140d40d002480078011900002c004040203d41301c03d014041c0c00000c1d812040c0c8038000c1d070a280c515070000340030341c03014000c040c1080300210f00401e254580d0380000c8080c044440c15241c45450000143c986007402a0399500001c542c806601d052207058810100c8154002650030000c1e601d890050f54142c0c4060909010068100300000214105200d80003401c60607a80c0031a89003000c07040c80382925070b1105c080344201c0c604164400040c400255640c202c9940c0e00b007154642c0d0307088000644d0701c112942e6243d424240050441c080540c164010801d10b6544407902c0990303603c2d04403440d40e0704040400100000074004248000ca00c0700c08001403181c540c0c0d200800c4d41c180101c642d42d010100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 136708147 1250 136706897 136706909
    0x20c010605030f0c210309041a041103090a0605040305070507030c03020a2c0a0608030d02070b09030c19021f020c0405070f08150d0b0f0118060b090118050a 69
    0x920082441503240a100c034102400459004001d000c10300c600045542c0a001c080c1d0303403100c00c600c041405c1c0c26000c2c01aa841d450004000300082c000715400d864001d06004001c034400c62074048141d002000c6101a240190681c4009081e40996540c8840090802800c03e80900806220a40005400300010b801440c4239102c01110a2715602c107000080005420881d420b01c02c1400012500c0e240001010340400342e4094805d464882c0b83c0c0400007091990805205d9000000d000d049001e81900108040d07403042c2d161200d1030359020540346d00c03030080e1402010280c21542174000308161358240b510900f800148040500c01412120b14001c5000425540258010810102c940e00e0310780b1030140d002d509820901240c00c1c007440f0088c8090001440d400d50315007540c80c002016294030911109240c0d201e0200d04050502d00c10b8408001e409119591300300c9400d584900400e203440c01640201c030b040400c0c0d10304140000006460f030840c2e1011161607140602c0001540741ea8100c00e40c001000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 136709397 1250 136708147 136708151
    0x16050d050a09170a03050c09010815010e04020c01020c0f16090b131404030e0603011412120a050309010c0c08090438010305100302030a03120e1c020105130819020a06020c01 76
    0x80300788000b80940386d0007001d107c007008051060b000075036080101250722203d0010702c00e0300b18401c00016a030030860301e00e8180c3c1052001c0340c60521524158020710040307924030202d50f080341c1043c8240c0e07942c0000810301c5c200f0301b154040c10040d5904a401c03400f400b00c4014904500416252030040460300700d02840107804d022402400140340e045003c00d4a010b000740d03041451581003124205201070b41d002c625020303003101e03003000c652030200740040510025071400c50303942c0303c110700002040e503002503610f00b51139440c140c9074441e0303280076899055045503c003842d1420009103204200040260990340d107000c4400d10080070120601c00d60301202800c84540349101c40754900c000400f2144006c00b40130345004154414400760b90001000902c40d076043c504441c00c0c480440350000681781c1a2564001841041d01d0144e50301102026511030100c1c40d8002c0001c1d40e08c4240d40e03801440e0024015044400030085013501450000e0081031104007401141d5990b0100c0d40d42804a034449114803100da5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 136710647 1250 136709397 136709407
    0xa030b1b0f041d01030c05130902120a12030203011505180301050c0d0f050c070602090303120c12071803020609041401090605030706080403020d03050601200f0616050d050a0917 78
    0x2010220540b2100c80c007201c0090f1081d819075440001e0403441d0b0003918826401000d100c0001c41031608280091035024080001d000a200e40859940509410032214441c040f8080c101007482482942d0480d4030000d2030341441420500141e6003075101c84611200d6030811190941036403401d009490140070b20441c1d007540c44d034805803204100d441c000c00020070306080405129041c0d5201c401d84540c190021001aaa445640d002902d9071003602c200f0f01d002e048900801c02e8070900c92018060300e002d401c44607803407517941260484802d44204010003030201100340c10701c050304091010b8004c0000161001648030302c010940d2000820980c4100c0038240c44160a10060074188480002032405080500990416540180d2a003c510441a0070550703100002201684515154002c1d50480c2d205591250758984c44503481d00140103803042e15114840100f03004203454080205181c025a0304e040c188140c0c0d1003428080d0002524827107443d42c0706d0001001107500001c80c034610300d0342d008130b5a07591 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 136711897 1250 136710647 136710659
    0xf03110f030910090b033103020a02150702120304060f0302030112141f0b0f030102130e04020f09040609021002061009020c011113030c0b04030309180e0313030215090a030b1b0f04 79
    0x1681a031403890300c51f18507049040000e0740000c1c0235280341e41d040394a98900390300310109070f031903010742840603600c03005405004141d132b0004001002500c50603540c24004e44807462082e803d9120a224001c41c5d05049031041d070109108170740c0c02112000c0c040c29034100c00354800740e80da8001d4a50402c01c48150740e41d28005424038158945a480c02d82c190025410908440401000040c0300d2240007030fa90340d43c00020b130441d5102140c01054000003416010541010b04000000b0411280101d0151a080344640141e41c00050309a00c690448480311200034149026400a900408000c6031250b40300c0c1c5003000c0c84281e29002c0c00b903250381003009484840c59410803808520099218240344101084148040390380103100c1c40030340740c0c900c4d121150711240101d918024800d000d003d04c40d6000100300d0596000e01c00c62218201d0b03000f1980705030501520091050680728051a242d4890b6003c8000c01c0024208d0b40402d0f404074580b250011284d2541100c220250300588218004500003d424464 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 136713147 1250 136711897 136711951
    0x4020a0c0507142103161509030504060315030b1501030e1203071e020a33020301051011060a0509070305070605030a0c030c0c0605091006030f03110f030910090b03 72
    0x10300304d20b810060182289001290b840741304501c0413241d9021081e40e04c109005800c40e50803603880301003404110750020f5040c01002500180204400241030411500701d25034051220400c0e01c4e00031140702500d031900b050f0100c2482c010201c240c11f054459601800c0f01d00c040c00342c01c140f60b51000b0400e41d21b2400e40c00c01003035895040408024401500902c00300309a00107040b0b903e00b07a200300b480c09001030b8002062091600c0303c2c0700c1640d58408480f030140000817500658120b4805441140134844625400c3e20720350b105070780c54490b5030300a40000d0040420b0360441c0380c0141e0a0416160b4540c3c1782d8032058208501500080301081001051081082c0c071403041110001a5182c204151800c0e03110082c8003100000000e444030340c03540c0c08200240303800d1060265a80840e2000c205155807454000310300003800b030301a030100e4071803107004510700c0000c100161b074180400701641c07a00c40c1c0e03072041041d014203410b21902008904031010502c41d000100441c0644039400c1c03c020351f40300700c02d41420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 136714397 1250 136713147 136713169
    0x605090408030a0c1d0108040f080d0b190b031f03020d03051309090506061203040f03110405090d14030a020f0a02010905061605040902030a020f040b0a0206100302090604020a0c050714 81
    0x404c1100c032a1030380e40440740400b24645c11401c02d190050303d03034440b8100844800100d000c050700300f00300060721500b852910360089108580554000c043c214131022400a0701c3c03140d221729080c00c6420000600b060326811303500c50a80f0b40d48584008541c4e107d4020511042c440c0760118041840060314600c8026008080001801b00340d0b01400a10130725607070952208c10250155000e2044000550014401030099038090310001084007200c6560303082c40c88446402d200414020f40c982000f1881c00301011401d81c01c3d20300707951600500038a03420401e80c40d5501c0100030800c0e20380e0074000001c043d030004000740903c0c016503002040e012850b0518908200c1c0117080341c4401201d5a014003400d80e0040241c50480701012001a226658800c101b8003910075505498000c00001501140b0000c020010300701c4006250f00b02c0d842c5030b80310030340800012040e001c0030b940301821800250351843c1c5500180101d10702c40c40e000201140640d241442c0c490660440361034003641072181280e50400300c401c24 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 136715647 1250 136714397 136714421
    0xa0311040f0305030a140715092604090609020909160201020c060f061002010501050f060a0c080a02011509050603190203031204060b03010e0c060304060903211b03020a0915030605090408030a 84
    0x103152050710f80d035920000020680b5004020b885901210512405545500072070a0360310079512034200080c1e40902b1036105010303501c0403034545000481c02000610a0b074101d1880941941200d490721128030800700300c058200f108641d005c102280c40f0040c20301806000d8803803039204074824100340d020404c0140c030444414045a140100400055032030681c07030f031407594040c0d5a095482070300000c02c4498035405500a84850400141d00185943c1540320381d000c0341c580c070b142280c002d4031080304400ba00c1080d100aa8180d12560798643c0c00c10443c6000d0f46100d200908407443d14900c4c04a4035560601190f0a45507243c4d519580c1ca0941020301800e2040e06031003000c1c005031708040c0d0004941c3c0c00094405045a41d0f00c0c1c011030100350159910140000e039140180303019003610406d010290506500e0040721a083ca0700d1281407038001e00079619400030a413a580306d01303824103007801d8580078071a01440c10561100750008460300d4440b8043d00503030203a1003140d582c0c5480e411030400c0da4803504001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 136716897 1250 136715647 136715687
    0x10e1b1f181d010302010827030316080408030406020310090f1b02012309010b0612040203070b03010501020616050d06030305130e010b03240a060f02070501140a0311040f0305030a 79
    0x41c14428601450403810340c5e6090914000540302c0c0e1100c4c1000742c03070301e00402c0ca07c2c0914041f038191285002001e588140d200b02c01c0c0311420b00e2040c40459102c14142c41c001c1000406002141c00141c40b0b401440e07100c080542c4a41d805982c4003030300d10030b65219a10090000765541070010302c0700940302d040102c3e8010380c0001d100d5a00f042d00c034a01c100149a00e00b4041d1038403100846d130403038820b4120312900d1030002c020039224038964000031842502568101e11030b1080031030014003c2c04040c141d03812600140c02804160780e4108a50b4283c840c150081020010100456500c080c1e0324032414001d180a580c54035290403080803182500071540d00440c0c2c55030360b050010080b6500ca6030880c5c1d0302022480c080c03821001c5550010307000d814041201ea074401d03041c0002107002036200e5034072400c0901c00c4d400c4800b00340c0d848005507210b561084040e8842d01040010b100c455001707800c8a44000d8a00010074941541d85101d4655104240c204a8041c4c000240695000c0e6000040d030000310044074503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 136718147 1250 136716897 136716929
    0xc0307030e210d060e010b0318071508040204090c091d010b0a05010f020c1305150114090d0807020301090b012402060105040b060d0c03051602010e1b1f18 68
    0x30354008402c0803461a80140320001d0315461100701ea80080d03004281d81c00000703c155071103130403215a540080741e038445441400c00d1201c110350f02c0050311404841c100c001c5c092041d0005481124290301c000d0050f6000340c0c440011301c000a00500f06c44000304030002c400a0445010003c4005443c48200c0c0311140d82e040894880f6169104051a421684242040d00030900d03003c00590030082e03a41a01903222001e0065408503070344c03d4024612944100d001c0611318600e150043d40d241c0d00e5500c0c841c135400780a000c03d0318203040242d548401c06010f0b221190418a144c1c1c0040c0c2513403d400c1d81100e80c4080403004011207070402803800303984209081e004100500e10800255101014422240b0594890051484a4641034125000c1b003c0100c000e020b0780f90103030b9000d806400300380c5030161800e19a2941c40726441c4103104000d840700c801005000400900c2e0358a0aa08440c1e00c180c0382e008403242004100e80301c9101d800d8020345981d480b5450192030f0040501c0800f83c0b158441d82c035500612003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 136719397 1250 136718147 136718173
    0x207050f1b010e030a02092d15040c0c030c1104060504020d0e06010e0f070305100302040c0309020102070b09060301090b010e03070f03030801050909150924041e0203060a020a0c06050c0307030e 85
    0x203519a010035000d0307040b44409a0001520512440e040c0780c40923480240f014421101c01142e515003500301c080ea0184101c5e1118102110703d051600c102900150b01c200124000580716040d104207028024800708030329461790000b4040340e200c0100940d031940d541d0b151949085050091500401106100e840d06252a000c46100c580b00242210200741e500e80c000344540943d4007101024580107803042028401e07802c4058001c0180000a85c0503201c0c00c203000440301c0c0c0303500407640c0740000901041d04503403a205030f4001402c8150480c1b07050041400760303801940c90030003c540003445000c502300c1c105840c45c02c000c1e05181042e04002e0041e5250000c1111200c000105002403001c404200c0b0b4440d034988400a00341100c1804000c40301001000508010496010203401180904030992480301a68440302c43c2c0c241004000750941c2111002a4407810107034080d0201c0019420a051640000d41e40c080844c2c0c411101064551000710500090b1941403242001203000a801051501d00100f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 136720647 1250 136719397 136719409
    0x501050604032a03080d02030708060a1d06040906050c1305010309030c0b19050106030c110703050c10090f030303020a1d03060606090a031b0614041401030207050f1b010e030a02 78
    0x41c0280c0100e07030510b680d43ca00d140364207144800843d048120306490312002906207010350300c1079031854006941c481c082000c5182c18217985084a0b014660351840c1c41d0b00601c0c4407207600005200d00d6001d0707030f108200008169a805510b115480c015083d030b40d58070f41646414100881034000c1410140341c0181d03400069040401c400801d41c208449884503504d40e00c440c1105514424102d2150f410100009070070794154021035281a5039440f0710388503241c00003403d0742da001140310103485903001102000d070500b85210601d00030205880d148860700d854206046600c04194012000070b507000480840c00343d4040c0c40310000340004074540d15222003180000e41c1c1d800300036002500c54080050024426962001d5001c01598031121a40b190b02e110604011083d004e4842e0201084034080044042920320381181c0c140c0f61403807111007004241c840110002e40000000b122140300d4814031184c4540304010b451080202d40c10f8030119241c11000040881c0e042c001c5450007035000c401913400581e0340b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 136721897 1250 136720647 136720673
    0x1080705070c27240b0c07151202120a0b010c0b04060c112a030304060807080402060408030d0911101b020315070e09070e0d020409080f040e01030501050105060403 72
    0x7001c502c2d0003148200030200340c1c0f6208040040d888900d406140302460710006281c0300c040c0c038030361001d642c003a60b070b18240c000c0391140e44520a03458220340c90900c500b5180b141d007900700030614079148008402d06025502240c0c0700d0781c010014002000100103c040c458041c018241200b8a0319050b448102c0da034032000390001600081045403103050500e01d20303110741c140c40742c1406c007042146c0c00c1006000422003583c181800c01851108911441002410000111780441d5110383d41c004031640d0300e40c0c0071a075542014204a901c00010880081c0e01c81040001e4841022174100000d0b10510f13914140780c6042000405502443e4840019520030f504420b104900c60741c0b400052030307007080c0d600c00281090180c0450130001081c5800303005485900c8030008030101c80640e01c3c15015203490300c0c01d44d5001c0b000101541d1103105040d0400041c101074000c101850710840400e800c2c242801603072411134100380c0214005015410040003400f401340100c0e40180700c143e41c1145010304503129808a5440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 136723147 1250 136721897 136721909
    0x60b01030219140904090f02030d02060403020316110a080d030e0d0906030b040908030906010315060e1f0806180c04020c03040302120a0203030a050a1101060819110d03030b01080705070c 82
    0x884020782141c0ca0460301311484814001c1003002648890b10707001d4115120520143e00a10840ca00030042600001d01940103642680045061000f01c8ca0418544104050100d48071031007505c00803182c3d159400260040c0140c031000c0c0c44181c2c164080101104d0400c1308000e440e0303125900d2503841715004440f480581d442c9107000b041504291020401401d030101008280e05400020003d440801089080c103a9100742009017421103596092420b81701c2c640944842160707400d002c41c0103c6072790b0755001075051042c00314105480d6111041401c1a40403070703244883c24800d80302c00b00060802d0011101c40c43e0101c1d0118203085602540b10303a00e018030300000740282455604003a0a4008000a01e403960740142140c0d903030003603094024900d402c8a613806d004603980034170381e0342041c106000369025110074800900e03420204001c8011200300c4480c040c3c440558040f0710038407a0700c1da070001803145070107518003007079820001000401010004000a04004081c00740d000000d41c0c1b00020740803070f06 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 136724397 1250 136723147 136723157
    0x306090305031f260304050d030c030206070903050d0807021005090c01020c1e190b0708070b0609090d08100e090601060206010f0f050d020a09020d090209010902280e09010303050304060b01030219 86
    0x11441c01e03142c40c0d0710487c0c1100d548401c03034288440805600c0b66841072194801d6090742c000d9111488140c958510038000100590010960855290300c80d40079140d101c3c4182c0704941c00007010f9418481100c500307407400c10a03908448241c1009580402c0804507219064462151403000b141c102c2c0000001c0300b00d09442003019002000540c500529050003070500050030360f5546a95182907625940501c00c00ca42410312030f00041d006182542030b49115609540107003412016014046a641c0070080403d54030290480002c00d031004424812889650144010440c5506001303020b850301a051740100c0c540540e040d814416102810f001808864080c0c40c901e010844a100166800e1001d8101080291011031a0004d00c905500000041d80c000d451104003070f625403035410141d100c0e840d040036561111030003142c07500da001300758842145907a24003664292030960000321400e04c2a84181d00144022061100780050340c404e52481c90000d080440c507240340d01003805040441c0215000c1801 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 136725647 1250 136724397 136724459
    0x2070e060312030a05060102100902010f140c070303030906150f03111809011a030d0e0904060e03070813090b1c060e07080d17011a0f040306090305031f 67
    0x10300e0070000500b852a18a1007039482e480d008910790000d050848119005200d69100303280c0d41a42c5100c1d070400f582d01a07480c0c1121030501072003903502614604140325450410004524070784401c0c03084e400614441d940c0800c0d10704030b6041c03450584001c111800d184180181d401c0114681c2c0310303d40320840b07502042d642004508100051a9165624007504d001410001005905807041d4401c10211140301184100c07100800306041d40e498070f0f00304440100b55000144149450b285100b00e500c0361290f140840c03100d04d14411075096402c14a42151002c40104010022041203040703c0044c2c00c142c0c1c2c0c01c20114102c41e002892290030205103540340c83d001000d580503c0324a8200200030443c440807180e16680d6050130555072602c15803000f001a00c01d1000e030644440c103000007030407918207445c61212400c04d0303008034000364000d181550b1702c1d180c20000007000032402e0117141700440c0a51100c6807030745881d0b0120908800540f003034074140714031003034180301c1c2501502907078601c1b0307440e200c07008068 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 136726897 1250 136725647 136725649
    0x11210f0705041a090c0909151903030207060c050c0414180a0308130f02150a030c03020310090c0909140a0b010e180721020a031401080d050d1e0e1b0102070e06 70
    0x1512511b0b1380240c009a915040011000c071000030002c1c0900291f401e03071202c48021122106400321800010016080603004010320b03485507018a403403a02036820340e59503000e00000901181c1d0350b054003030a010385031010020796484040030000c1c40790030307040640f0f0400901e54000300707030040c01410001d03881d8006025030f0900560410716440603a002e05202246440344a0805058104112510000e42480d944403111442402968022281c003800d0150b03c03402c05000001808800000c941000f020f00030004000700980541c24628001d052602401d08104c0c00b4481903589002c0001d05111400300803904540761000d48040c1040d030100241e099488031541201c0d60469101803086030703412041a1031049006e0fa005042d080b45a49003040407903400020801c2d031540920901415800c01c602618015000d54000c2010901e0343c040040d00302c0c00180e58410510101e5412451035075221100c00d07182c4c8003041101c0809412805030307624921a100003d546032414021840a261428041501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 136728147 1250 136726897 136726921
    0x6020a0c02090403080411040b010815180a05011a070503070b0c0f0705011409010b060a0305090106050d14010b04060b0d15050916080708060105030411210f0705041a09 74
    0x20640d000b070030003640e81003074240146074010540342551005c0d0b10a4100e0418a000e1150f160104411386400340030307a0318640300d40049079070407040c550440e01c00180e4035158028049942c0c899404104005107550610854192071440c0b8090003422610820410021440000903100c002c0d511040403262030b0b4801d241d1051070b00030b07044110740c0f4140c04100c1c5002c01034103411001c2d02041c0c04500001ca40d03a8030729400d098480074409650445c00400c024501503120382c10941d40a06c5c6c072000401c4140d0780c0c80200d21114108903013030302c0234046030840b001e290f00c007805043c8607503030200c50034005142441300048292003003030f0443c45000d907a4115100a440c80007404801403c0061044a042c45d04c401c10383c10800f00c051460000030700c100000754006024018480c0910010f03980e25045039142c0c0d40b418501c0501e001c00c0d076071022500607410440100036142d075014962038000b60500044041c8120324182490300320350710490905c03202400c00700c01400c0e840d00c40c04044500c1d14032034680d141d80d03d403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 136729397 1250 136728147 136728167
    0xa0f171e03060103060506030702010f0b0a0614030702010e0712050f010507090513060506030403090f0608010602030d05040201030e0601180b01020f0a080901120f020a09051008060f0f1e0907020304060c06020a 92
    0x41c000c4400300401c208543c06601c52000140b00330024000b40c5402d05c10007040320a41e0080c440415907900c0c24140840c40d8001640d4018954000001d40c5983c14454520303060055002d52a81c10914002030b0400030140b20702c10880c581c04000f8031440c10080c0000d84540640d000705400341c0c0301080b0821108550b5041680285005400e060f40d03070905003401450903040340581070f8207070840030b40040c1d010311030b00142e4101d036060b0b4055130400b6041a00c0300041d003400391040e810192200c060384001c0d0014854180200902892403101c0c3c880014140140c503944850709065400c0b40302051a044008915852040d40c0601800e945503c2000180c1b0110150f1407404038040c5450240400144903078001c0c05648455200d04070415640c40c10054074520b107038254000141c0010208030306081541280000185c01403000c0c4008000102158109000340c10a402600d140c01545280e4142107000e01d4101c44180f002d07501e810b00b00000682a01264400100110360009440700c50138403c500d030790 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 136730647 1250 136729397 136729399
    0x115140301080a1106030705090d0c0b0a080405010606030b0306160306081b040b04060b1b0c041a0913030203030115030b0a0834030209060d050a0f171e030601030605 73
    0x95100e503100e000603551070421503421101c000784000110075601e801400c3c1c0b40701c1c55107951a80d15203410503007408502e400004080701c20012900011235a64440c3c0050240c0c00000d0743d0348003031032030541005429181c1d968400c1052602c0c0c40b2a0b2081c5460114000740d112040e82544445544100b030b0403001041b00390700914050084505003070380005188a0b140121070115400d00413180700741c080208442051190100400c01005500100d074013824080e0100c580580940d40ca00d55880040b40c20745540c1c420090001d200c840d5031040504c0c02d9190703280c11203401e40a0041e40c00e000e60b40030b560b80c4018040c03ca0170740d01c4020f4030b142062080d0000c071060117024202c0c1400359656004196256862603029050000e07905000b030034050350b071402414a0381103c0c50400704514540034410365960190000f50403180484d21200411410419800c02c030f4822904142009540c8c1484007481601c0c0e812405050010041044607024240100a070b00c80e094443c01e640c2c0e29640e0042e002003015074000c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 136731897 1250 136730647 136730687
    0x213120507050301230702010203131e02030d0c0b10080c060d09020a030c0611010c140c012003090f060f06101701060819021608070c0e090717010903080115 69
    0x200720b03564103491924600305d103440502522038441d1841039003030b0702040701e49840f084407142c04600854403000340c0700404040a10810280300d03e5801003401d0480a00502010038060200320f402c00c00701440380c59000300181801c4950a0502c6c041c0d03a183c1e10a0920984140e030040703030000100d82c05a100c400d03080c2d4011b0210480d55640e03d0200e4203809144240342c040307900e0810381c0c4030300d503810701581c0120300c410764078040132500e00c134401c80342904201150319056580d0440c010005100c085500a101030100b07070075481e440c01841051410f82e500e04403100b079800660070312403030215007004507400c11001c0782d80902543c251003089558502c0300360a400c609500100000c0c00b0758000c4250750154070240d04019100c40c801c21035400b82c1c421300f4050b60900c40c002c00300d880072401150140410600c501d901c600d01940d1940c4010203e802074510003a181c20504003002880c3d5941c00c0c0f24590458a802480480015140a0807103901482480150301c0002c1c03113054100e209241440b031001281e059 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 136733147 1250 136731897 136731911
    0xc050307020d02031f091103010b21190507140a0e010902070f0b0708040c06051201030605090109020a1e12051b0105090a0909050c0307031502070312060602010b01080a0213120507050301 82
    0x1e81e17000751a400301c040c2e41c0c1502012500b000c1c1c0c00e060003140c0107007801900501c20802d000c2d1100e045034054403085001e501031a1040b5148101c5813002c060b07014010030041c109103040c08554100008a0703061700c0e210350304ca510204a07900750801c1c1e460448982c40c42c0140c070350100f130038080940c41000c18010041070303510040042d000c3d00100003030300640c040c07020440308580742c09003903a20b4420007802c43c00182842d001000042e14940189500103a02d0300046a00009540420618800c5800640318403401d02c0b5141040d142c0311041303000803c801c509a20113084a62200c0392150f130600300d5100480640b21070301002c1c2c0d010303100300d03627a80780054041284c55599a000c40010001c081048480307001d801032403003291030000390700001e8980208410b5806400e2413180002540014412402c0c010510680744040740c451143c0001082340350000b00300b0002110004005100040901182c2481402540f81d40c0364032038400400c2d151507986441001070701c0d00b402440d10b100b6903c815031640c20100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 136734397 1250 136733147 136733203
    0xc0706090f1401061a090f0a050a0803070b13110402030703060f0b090f060a0f1b0503030f06030105061e0114271314070c0f050d020714010c050307020d0203 69
    0x600c10301880b420003082a075480d00c14115803943c0968841c0170008050040395424034041482002e03000700140020b5090703035a4004500c084c000f40d8440d2040e5000420881d0512a042100c240d00c00c0c4541c00e002100e880703c0c1d682e00141e00c00b06299500841e030200008410501035440700001d0321544441150f1203a0704d80080c5860342c095080d4502943c420208007070681403100c251031002e050f82e10398030b40540c1401411150655040c0125960342940b12014020400502c0254007902d0a07251001c06032504074180340c02c0d2000602458007070501c0701045c03036030f0700c207840d5000e01c560b6004d03c5c0030b1071101040042c1d41a68001e010000340080d014401445440034000c00b0001d03006070940b0101101c40354204031604480e00c0012111079040d0010001d16040d12580418207414419210914054610388a461a00c11800c48280260b4030410080c000d0341110808440300d0030091804074203540036131383c885449003e0702c10000e0046100b403a410046503401e0110300f03d400d140164000c0d150807035403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 136735647 1250 136734397 136734413
    0x50103050c040e03030103020d0b0606041d160c030f030b0102030d060b07030305071b08072405061203132108030403020a0c1203051b0c0a060203030105040c05120c0706090f 76
    0xc00c680c0d214a1400f840c8800c0c801020090724105c030340040120307412203855126000c074810010b280650007801040085041804800100b070240c2806c2c00403500707403070500151220720b00441d55420910518144590002e5032043d07004c0c031400864a800705016245400607440c40c000c401d0507824407814108045209201c8002520740e0f2406a50280800d0302c030b0000554503050b198107403d41d01100042400701045140c0300524840d4070401c040b854034030318800b184084480b144102c80e1016190030920110b854584074141c8030220780d40103145800000c0d404072608401c148104440101901104420241c0e8441710406103900628000e6484c0f5080c17a00948501c0424012601d040400e440400d4030b0f10315040491109034191202d034908000c3c688040030900d484107450035248600401000c154803501c10080007403030f40303400454803075040c0320400054540c0c1055120400c001840442e2190081c80a1150003002004409507030f0140340c20300c940a45070040002d8104c400300b44106003001004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 136736897 1250 136735647 136735663
    0x1b110123030a05060910030605040c09050903191103040e15030a0317010f05150d0b03101a040506030a031110110403020f0907050901031a03010606020102090315041e080d05010305 79
    0x450b00c104000e43c0c41d00100300781404155180c3c0e5440042d510700384000707081903100542080c01841c042c40c1240c0d540c40e20740d086d00c0d8222001d5809400114003500000355421510b0820042c03820944007008880c040650b8070302881c131403101c4000c030b15004915201e26018003111110b00141c01c1d14030907074450902820950b125180314102e2031101d000001c1d5100604000819600014468280200314543c0350b41c80d031300300003006401607540384003e00050b5820442c100c03621800040118a400410b02280f030504941d62134140580d08207006c00490b60703404030301381b0001d9a050034105204603003102c1041c5090540d0301d00c5c1d641d452a00b101102c0802c002d4000d0002c60b4170849204140300550402c0c05500d02c000e0b00d4810118005104541040d8025000709281404c018030545031300004900181c08e4940316486100540d50000e40070410342400d2054040e801304821541c4014100795652841d012505400080101070785000b9008001c607400c1151000c144a51040c082540c407810130726211404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 136738147 1250 136736897 136736911
    0x30c07050a0e01080a080c1e010b010215090309060313060203040f12030c02070902030a09020a141503070806060d06030f0506070801060906021009020a0506040306020d0c1b11012303 80
    0x1c0722200141010910b000341e4180c50a25000d00448130590341c941390142c010125403401800b41c60201000000d802c50050f6410901c4070000c18007008520002e4105107003a02c1d00c9002c0b403001e00070040703416000412a507a00c0030139144941d480d582d070f00707001c200c0d4070307036564008c1c9100d00000601c003d2081210580c2c0c0c402d40540403901c41c0802e00c08095003200d00000a40000da0400b5108120720b0040307501031a44110b10581c0410341e11180d6001412003400c54003c203100d240301190b038800504001e8a028a51b010400c2054a5820035140141800400911a034856500000c8882e41030755160000310040d940700340c05a900d01180d2401e191500c1d8102e4030603000420300e80c00014421b2260f035000c1d00315006500a44241d8041009090240031010000e0342c210420341d00028141d10380c00001c000070740c000c40c00140ca4000303861003902518840d5072410104440d034041d1030031800b0404914000d003076002202411104005005070342c000820304e141000c0d000360071014903484081000851003200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 136739397 1250 136738147 136738159
    0x50a0e040507051806220f020d0e070b070b040f0c090209120106060c080304020604080d051c020403030813170c0307020405010f060503011502030c0d0504080607090b190908030c0705 80
    0x40c0b83c0007030081c525650340084003000700010101d5441e04190700c5042c3c028000100000c810040110214241d808001101c10681c0e03001070721005c0c0345510300c03402001482c200050810b40b46030018442603401345420150440303c01901140400601041c0071084551000c16102d40598880742c0c14000c0d044071300030324024640c1c580400c0303001006100c0c107004e0f900c2c5500c542114001a8590341082e400003403003203811210410011541c403008020108444040daa181a0745903032400042039481d4440f009505001d005000c1440000d400c0130300c940d804039402070076102d000840d0a2284107000d034030f616074440440004403030321880004001808001e000f4ce5062120fa41d807245c0029207820356116520000303c091005000c95141108045254641c52040382d003888003501c0031906000808203104041280043d040048034404d0003656031041c10703420305401c028907280c1b02c48a1441568081c2c0105020326074421181402802c1880140140a08503030b25158101c000981c0ca5806000c1c0520131a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 136740647 1250 136739397 136739399
    0x190201030c081b0a0210020d06170a032307150606090b07020303030a0c0504080619060b0306010206011403070b12060a15021c1106040b0709060507020a120309050a0e040507 76
    0x3801600c1c4207000d040c46501030403503880f440b00110825040040203100b1405108130064000f0050700203080117007884000082d2852500c24003c04854901228403010340115250720003003500020416640041c00e00c0624000309550f031003440e14858160f0040a40741004141c6182d52205c1e4000026585a9100d001241c4d0f200e1202e008940141303007000707505600810014402040302d8001340155000350504504003516007200300e080510442e040ca2800d03540e511416030340039040c01104003d0144080162542c03c0c00d10000f9211a014091aa0240d03900480085d4076101000108c00500d4401501031302c07103403007040d003000b00b403015688544640e800030408a900d20181c0d043e2000031003140c005140307224100005000d030082c0ca9224109206404d042144d00820502c405845280b203039003141c003245011540078200250503007260b020010103204c8100181c6411001c3e500791905240c410001300418a0201e58594041e001030390045108a000100b0400c1d550100d400b49201d403099071506 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 136741897 1250 136740647 136740671
    0x21b0c0301060b160c08031206040513050d0e01120c020f120c03032406070f05010c0801120b0406060909030519050310050904050c09070c110901080d050d0e19020103 73
    0x80d40305400f0b9403252040c00c00c071104081820350740008400d0301c02c0f03c049a1040d0386401c01030035500081984044865001d00700429480c091244941c8212640d40301248402c441c1c403400d948058070740b030807014040c200020150ba40e000d080304012402c8001c8061040f030070314010094507180d00406d40340c814480c103891080c04a0855051703a03055559100150300310360751020710782c009081d00103c0c100c02c500c0e002000c086c141c4a9800408c041c1d80141c400c0e040301001c0c3e1401c0ca085a85c291180e00811900c0d5006003d064418118104081d40100380c82900b41c6543c2450030041c00e20740e209080c414508003a010030541c0140180403c10440d01400c85070307002c01e94080d07485100c21925080c09080000c0c051202d450302a01071508a0702032401c5036a884144400f14260a40a54040c0042604108600100a0b2101d10f00d401108107844105d0154034000841d591416a80d403101c051150118498050003a254811103205075100308640e054018550708800e00d603180002070f4006810b0003841c03071403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 136743147 1250 136741897 136741901
    0x150e040903141c05040b04030e090f0c0903280318052b020406030c14150702270103060603030e0405090d0e03100501090b123d021b0c0301 61
    0x1000d41540b00c03100001c00d09040740e03581d0741c40841500d0708070204200048503500301d031142c0c500c1907114210400d260f04060801801e41c035180a800d030f1294112000300031318015a02074154200342c0c6d40501c0b50700c54071160006810701141c529242031125141d5450071040080755a8120080e0007500c40c03400782c59507418564501c0e15580035094110300c070700c2c141a07070000c0c030300035000e600d00d00c80700d07128100e428540e00180a58646078010f480e5101a28410b000c0300c10480300354000280200c421560350020200e20442c2805495006842031031175036034140000e070504800356810304100f0002d1480d980c4900d030510080400e0b0005400045c4a4070340b000313a60401d0f00c540e074010541d1200501001120b44011110a034456613801c0d018066289001c5980c0c2290140c0350207041c03204030115043c600d8070117024910042c60a646030aa110344e102c02d1181c4165003030003060301d078510300b04449103004558201ca413481043c0f00c0c5200910004664186070303200d207201340d6581d2801040d0784844070f40904141c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 136744397 1250 136743147 136743161
    0x110d0e06161515080705030a0624060f02011b1e1202130e090a080304060b0d020d120914011d030a021906030f021801080402010e030106150e04 63
    0x118080510805980c0303010000741c0800682509092011501c66640c003980e5000040d481c00820b07181c0c0181d4818014012030341020704a040003e0000070310f0000003a0f511054042c02401c02565241c4101c5078504d44481000b80b07400104e955030316070303a40e80d070020b20160302c0703407a484010352074110b40091041448080c0c0d5000003040da2000029108141c224442d0a106281c40c028003200705651040081036001514801080381101c050f050310300003140610900c018523200140d00801e4203000002c501c1d40559810a03007041e4009180084440800c035401c0000e2800780d4050f10001e030a101b045a0420b03406001140ba42d610308509541d008410320081c460102c0c140852144c01da0420711028012004031450b000400b203809001c0141c0110b90219049070000007030b40d030102401e10110740c140c003e0541c0c00c242608118a0a043c406034082d40844060b50b0604000c0820042001d681c810f072981500c10b00000c00130041980d480400c000840c0b140c1000d000820002003c5000610f000d2045007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 136745647 1250 136744397 136744423
    0x2060405010305100906140111010c020703030507030905040501091a0d05030d09030c0b0c0408150928060e030309010c0e061602060d0c090906050409050c100504050303180111 77
    0x141040e05010040d805010028440396040512502c0041c15050034040c000080c0860401c580714040c1c680001040a020f000100c407a03681031011442c182507000490408a94040c0b1b00242c4580c1d8a203811145107544c1ea0202d640941454008201d0f0300e5507621402c081c07000141344110420f456024050010758035030000d011380c0c00030302241d0450241600b103025405e00c20302e000081c0494550b00c403c0340c0141901c0e40090f060010505000c10a020800003600c5600c80ea080540b51030b140402e2580c510049110120140510900314070035554001c8128815030300c0141842040710880f06255a50022540603445600301222100501e0040c0b0003042600e001814a40c40d264100e16111280000c0c0304040703070072501c10484800c4203007081c82880103c0c565641c0b2055240e00c9c04126005954158210750710031440c0c0300c03002c000100b0014401c0c03020300d0261003c1c900c000a0440586407801140e002e1905400000380c4601c252104244091250764240c8a0091500808680950300c3d09120002d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 136746897 1250 136745647 136745659
    0x612030a022b020a061107060f0905010c080c09150903030c0a0209010605070b0604050403050903060403050705011518050604060f0b03091e030a21091202060619050d0204061d01140d02 81
    0x80017054054000d0f142c1400100c00651400c0791a0341c0e80003c075640009003c0b100390303880ca24481000b900780078034940c044981c0360407030103820701c07040084140c81920f034654403426145150314035904101c0103860041000400fa29201c00111500390744480c0c000700100e10031049200081109070085003a0b500b003030303008078061100d84e66100910000704400703001a020701800b80000f801555007003001c648198401d540300303912079485103456400c0d81c0030b241180958121460b8144400c0018184203400401b0720040410603403656001328000701080c0e0040003000c0030240c000300f01c0d401420015030046034904201c5184032a4412078424400c00d400b141003441d00100000080a846001c00e8054a031400902820001454000200320b4070082c1003155941c00c81a800c80d0140d405214440e4025802e0301e00c112070030820361b0440310089560060074490150803010405649aa0740010060300107a0000c0003202e651507640416101700740300b6548842010031650015007400c40100254a90181c91 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 136748147 1250 136746897 136746913
    0xb03161812050a0803010b040e060402090904032f28050a080706060e010f0303030507020a0804050103091502070b010f090b0901150309050a200603010f0b030612030a022b02 76
    0x30722000008012030580e07291007090444000300344820000c600038451070409660316440d01d0300e02d50402100600c040e224a10500a825460b10356411896000d541407600c0440c884005a0303024a001e00d8082e0304142045222085102880002e1038801115440c9110032001d080c0c0215450080b4881400a245400c241080e20018186d840548150313485604d01003040b0f900c46900c401c4a540c241e02c10700004500400400070700d030f014070030250403544501c080c0030390380819101c410b028415489a5810556240408801c0c40284c005481c82c00c0d4000209555402560800c1c0240c880203000d043c0b10f0180071140001c500c042d81c0301c0e0f640f001c20084c0400034a41c0c40d10703003100c815941c1101200c05140c1c075440203c0005009100c5116118440c040d01c0009900800d0341ca421248403204a0780206010001030068100c03100248046840000d14180c3c0c075502c8a020400ea1407080129042c103101c041882c00803507030041002c401b01e01c100b009001202d568000c2802039218200000005a007210903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 136749397 1250 136748147 136748159
    0x70e0f0a0b0723030703080106050702150a020102040803031f05010810032303070f15020708030105120a0b040528030518040e0f100614031c090905010b031618 70
    0x1800d4030301d0059200300c0001c400d804a1580849501c1d81181c500e40001450707008054100045a01408040c5050703030510072f0507404190b0300703150178403c045403060118101020a00c00d404440207810413a05403038590900d106441089045c50000700502921100085503075449004101e1140946440d80c807801c900d1a02ca00d07002ea601402c51a0800c001c4002d40101004104000c28005104045500d40107445042c0ba94032036040780c2070200c141e40108040804947c0e248240c0b41515400c40340e5440f20300c107800b001890481c00b100001e003068240c0c0c0810062000109440e0919080d842c92550070065040c62900c42107082d000060208009020001e00c3c004803d000780c00e140ca01800000c0c9034002d00b400240740c00542502c8059035488aa8070908980f01030080800410a8510110582002e200002c2d200e4040c04250340000682150741030b403081c803600c01100103154102e4200290350310f0349090a0182d00444042c07a07201c0066031442e02c414400d005c801c0036004890000781d5101d040903 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 136750647 1250 136749397 136749419
    0x30509030d05150603190501090b010c021c0b04080307081b07030810080102040b0a1b0f03140d02070c0305060609041e02041e0b1206040c03021c0b070206070e0f0a 72
    0xa4140f81070288581503118040d00c5540045001c0c000d1054040c2680140400c040284d8a050300700a8805050203d541016600009030005003035045402c403410388184e0015000c1151204c601810180c0246c2c140800d0106c944015405104299a04441581e611240310302c000c02d0904003000303140e8100700d400f01085c483c040c0319801254200c04880c125a1f03540065080e60880d030018103848000054072881180c0082c2e200d0a1121444c4103814100711a44443c4182450f150014091202d404050122810f107070007255500d41d0301c44021910344000d4181901c40710040c2c0411500d40c0b0a09000c90801d1520001d094443c43d40300c000e00342d002c424203014075208000958100e81068840d94030720860324000000320b80c1100446800143d94a05000b00624100720503142c0d06035400000610010680300c25000b0142c0703805551000d064000506900da80390f006150280860a0b8201800344140cac1c0031504a004101c40d0355000011000001041582454428102e9020f202d4600402003007101c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 136751897 1250 136750647 136750651
    0x1020a09050409111206090c01021609021303080a080402040609050f040809010314090a03090b07080f0f0c10050a150b0910020f0d050309100605280f1e06030509030d05 74
    0x161401e07008004c013150114080301c80700d880380e860a82144080081c510810805100007002c248020420700c0c241c0035885103002d9440c02800b51180e00090501c0309880044003070401594071030071159540c00c0302107000b000d00c402680c040344241d080c41400070f0981600d014460040116900316540380e1100d81c0e4a66081d030080c00c40030305164460118405400c1c202d400244100c0028000d0901a40710780750003002e21810f600083c440c1e0310300b4040c01010ac2c2e040320550780401c115218050b55060203621245140c02143c0000301c2d14428107804140121407508458060914840c0503c00c2c0285070302c071081e60803040d0098007458401032140d003106203000d40e08054140c07801d0042da4007a80906550604020003c04c80101180c00042400900d60081103004065001c4213020040641810001a01100c500b400c0300312000a025401c2c18030007205003c08001c0c0312410746025843c0e40c3e1404503c14400200ca800d07a9000c103682d0002d107844c01303401224070810030480511302d40003d401c2d800004101c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 136753147 1250 136751897 136751903
    0x504180c0207050d080d0f020a0206040303090c03080309150106031e0b040f0c020f0f010c1403090f010c0909060504050127110409020d2313150903030b011101020a09050409 76
    0x1d285000801d52030f44c2c420000c0c464010304940b69620702c9070215a05860039440542102841001024061036000c203d81e40c20590510780401c041c02e07141450555180c06803c094407154000060000b40702002940381c1d076008036064000050fa0f41d4180c01c2d4112002803074142c00320810000076400400d480e901100d80054001c00011761255218000e00c11600d2a450800159010655182c3b58500411103d6540e6440400030301803103820f10002440c44c0078103041d00c4500341000c0301089100c0d906004072003807a8580002044581c0040c040140311140601ca9266001c0c5401004545401c09019550581c0c1044000c441c14060032142d64901c145440c501c5041e85a0b00d41c40309c5a00144030000700f008091070701000d80c80d8225002c0040032030308000c0c14a0070045c0680079030504005a00e0941d80c0c800111844880018000d0500102c010b49552106800394034014a0310105034040e401080c681c0002c0c0c0e100b04030005180301d101d0817032050706802804540035030342c1002580707007540140f50038500c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 136754397 1250 136753147 136753153
    0xc020102040b0a0507020307090204050d150b030f011505180c0304020316030c05090906070c14030c0a050601080d020d0903020f040b030a0b06040e01140408030a0e070b030108010c0504180c02 84
    0x65502480b03001074000b42c020a001600024040c1e00350310381000a0700c00b170641d1160851800b03203800002003805101a4000b401c40d524001c100c01c1d1100141d11190300c40b0409010745207103242000d0400c0c020401038426508144198201141e40e0034448132804000340031145100c4c0517281d44c0082400703500000c00413a858841c0f45480061034070240d0b01c210003503208050528107141440200007020038002c0142041d98030a00802c41042c0d4010302012029400914160200081011050640c82026401081c510030a0071480800100145050480b0b80d03640a98030304070301d0280d08a80f21201010560005001c8001c14405803070441c4000122400081000480e0648100440d040100740c03181500c20a42800800c811800c142c042d012000e00918000c0014003050742c2c1d000002c600c05071024203241408000a055400719620101c40541d1460071105201e80d641d0640c1010760003400351510039401c6c0718800901c28003840607101a502c1d901c0f001c002c0c01c000303145454018188400180d0440c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 136755647 1250 136754397 136754399
    0xf0c0302060a021f0c05030a0510050409050609010e0102190f02030d110705070803032a07050a080304120f0c021315060207030c050f010e130b030303073c030c02010204 74
    0x41e0340c0070000d01c4000116006018070115041c3c0301e00c0c080000764003141c0c0742418014030760340340f036881001c803540500c51200c00141625220080b440c01141d80c0c06c2203030410b1900000c182400000214640305d500d81100900c040c42c04c07042c0040c281e003d12406103032002e82076094014000d016051020803c04035204407400d003a840419101543c0015040c1c080342d01d00041c43c4402d110040c000303800030307003d824015491810112944000c05120074010254102900c40f42e640f503000010440304061741041c05c0ba07030354440c00d06162100754410f4400725003501e0520415240f0500840c0031401003212038071006150700c015001d00c4024802c0b11a000c80f0140d8419480c84900030300d40c901000b5092550007428418110b140002c59650142c110030320440e941d8003d076049a03444402501c0c41281074503c0c0c10218040250b52000d011080c41e40d944c140004010810901c0c4e2005400b60a9071240c2a5526420081c42c03480a01444140b035042039403102403031440748280281c004441e01c0000b440018602 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 136756897 1250 136755647 136755649
    0x29010804060f020a110d110c04230c040e0901050408031b0d0903080601020706020309030607030b0102160914070c030f0509030703020607080d061e2c160906030212040f0c0302 77
    0x21391000003407102240541e00c44c0300000b0b90403c040015000d5a00744181083c000c201c1d52943e0324559800f440c420f548448007070030000000e407001c1c1d403003d2400c2400e001c54144010300b513400d40c0250060b220880414030020354040014003d6078020741d0086001840c2d500d480304048c03007103500b540004844120400441c3d014101074424403040c07e02a80d201015818840002404c0140e503074810411035106000700c0c0c2c00d66501144180d0400303228140000c0e1a441c1c000141e0400940f503619031000a00c1507000103107080c068000b040c1660b50100b8442503560303641c0094640c8100c1c1000603000400c40103030f00b421075005800800040030000d00300c2d00c0c2c603175032540094965400410100c40300344d00894035200c05074040c000c61020f880c3c0205442d0b440c41c40b0440072080c03c0c07014401c0083c2082c03d1418000541104440c43d105401000b1003101e00b032429102c2e01c02c500c1d0a4481e280005084407900080d014841d109036020b0000c0352078803900981b10b41d140c1800342c0c4e43d44082520380f110851000801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 136758147 1250 136756897 136756901
    0xc0224040308060f1305070e0103091e050a17090102010b01090e070c1103070314060604050603031909050405070c02010f090506120a020d020a0801060f0e0a03081b19050129010804060f 81
    0x202d456074000c1b03420300d0302c9940100a0b00000c42135506240c201581c0d000041c02007a0103d081d000c55501d1004251903a0909520344070710f10002409003e5424404074008440c20f000305070200003a0000d002204609004603010840ca1151805d203224000104090354448c07000d0800b894001e117110740d1a182108000380c1030450030f5104031041c0c10510224414040b003807140355440702086404024a00d0000c1c04a0b8491080144411074880983c1c0d0b8019100d000f40e25500140101070010411403038050000385c00c01030385003c180d0116512804000c7d8440c031071240c40c400d4907409081c2905007084800007421114001c0c0c10000e0701c2d602070080c420458038500c098164003406a0740d6030070035498808041c0180c004075290004014140a4030fa42c1511060040ca0480381d221050300d40c0e81e40300da100c102e42907060202c1c0c0217850040185406d50226424604900127008600030004074210442010180400f0401d42d0440030b11400c1d948019801034500c258464000e05000c59a406e07e2001041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 136759397 1250 136758147 136758169
    0x301050a0b040e0304050f0d050106030c030b0402120d09051003110a0503040c0f08060f090a020d081306080103150c0c0c03060c030b06030405060610050408100c0224040308060f 78
    0x841a58445081c41149018000d03102c1e0b038150003028514140c20031000c203404050010101d07001e0049045e00c0010044d09500034030046400c021700c01000764803460403105900303044c0c60a03441111949011720071480045a00c0c12180c0d03a0b0340f69101540d140c00c00748682c81e40b40c40441c0c0149503985184040402d50711006000c0b500250382c5440e9245071510705231100e06031a4214082880040e130081c031a4000000c3c2068101c104049a4620b555520601c2c034a000d003c0c103002500128060030480800c44164040c082041e07642003106038007900ca140c00c881e4070314244009014114641007450702c5d203507a64045582c0060320720746a5601e40d4240c0358041d090713506603c01c40f61544c0e10f40004c541c43c2da00d8814a03069080031900c003440c0d428035441e1155180c0c1d010b0700c6a84210200c0500f000340038003a001300c60003000000c0a46072100890030880340280340d40d4007204054058070b40c041270051416030b2495603a2600d183c020040f511103450494010200501c12030700301d0a103080605084d40c941950030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 136760647 1250 136759397 136759411
    0x101814100302120601060509060d0204090e010b010e040c1b110a03080702091302010512060a05120c04060b040605030403050a02011508010b032e0b151b1203041a07020c030105 77
    0x15001e1561060158090010840c3c40050b00301c58010304c20030360310600315803c1c0541150f4468076521140b5029009100b0395005200040c03400304480ca0f8901e0640003c0b51054090700d40c1c2101c803400300148002d441d00e8060020001d0421450350031655803503c2030b103002c140601c0000540b14a03281c041101c04d00f454100b622004004921340b400c40c50488a500d03440880b0445401c501031043d0f001800d540185154046440ea10b03400141c980d440300c8100344000e1400070aa413003038038542c091442e1185801e00045004030305103840811440c114504403011039030f80360764081ca56070701d0351002c1310f694100c4100780045540b5000f0118903d906504a4000380c0001c900004804404004052070580c08c440413880c4108000203507402071944052903041c0e42c1c0e4001000c60207114081c00550f03440202c655002081a001c5995400f800322800e5400f440000302e001c80300c06800344a145607050208541c0108200b10503441074420903a00b03a800e40c1c10207842c0c0121070312491007100280c00c0d50303400c031004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 136761897 1250 136760647 136760671
    0x20708041d01180c0e010e030a0b07051309020702031f0b031c03140c0a0c0807080c07031e0c06031a0a060503090c06040503030a030c0908010203090d080c03101814 72
    0x1840001d03200d01d03184940840300d01d001c20214104130405452080481c4ca20b50510282109402c1e480c2c40c00d2020100c00c81d400384514030035260600d406061070700b00100b200d122040b040300220314104144216106c15400500a00360002c3e440c01445844850044a514040d11030010035003a840801003240c100c1594104001c60354812840101100e04085642da5030022500600405000d036400f00e8102c2103951501ca00554903c0c101004544901e0500922422001801c1201d45001203a600c0907a4464001941300c81c0b1200552100c0400c0d148010b045c440f6008010001140030340c0c0050072500360940c900c09804000d400094243d6a02c2d80008003050000080000b583c5041c0860414504111152404c1508100c003090340c0380642544081030555503001c4200260051090130004c1014000035540ca151201110b84c554404000f248042580b03100811002e0705084140c91080c018084107801080c030302054114401c4280042d841c9165907010604d501d4004909601d00c100c841c0c00113 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 136763147 1250 136761897 136761899
    0x5100213080106240e01080a0c02030412120f0503070806090612030d0c02010501060507200607050307030309021011152d010e090f030a0305060109050603090a020108010e06030a020103020708041d01 87
    0x800e104408913201ca46041000740200720000e41e80004a00c0e8010032409000549194032101c241d1451207990400b26031302011140c3e28041100c1c1031207821250390316a40d21040f00c1280601600e542c04240d90b01c50115400c0c20000d411410001c6909602160003003d020204ca0040703081c0d82190310070040701096603124030100e500c0c29024041c40c0c0c0181011b01d800e925100351a11407909910402d07100c92000400c082d25490b06645e5081615078640d04202030300d90320401450081c006060420041b40202e1a403003030b0110300b80c06240d90115040c44031010700b454401106c1d000100b40d030003c00030b9012103040040c004a610740140400144008480142681d5040114521086200030300303840c02079200035504503001401005a4001d51b0450501103001d84070100103031244040c3c2e07001283c01903004000c04c01031800c001030ba05c00707250007070300d0f030801998880d000754400700303022581c0300d070540e02020018006500c6070340208802c5014140c3c442c202511804081d0000c4506203489540c5692980 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 136764397 1250 136763147 136763189
    0xf020a170f01060f05071a07080709050f0a06030203060a180b04060e040302030910020f0a0b0a0c110303130c09050703020406080903040302180903070c090203090c0a0305100213080106 81
    0x44035800000d280103960003585441c200910780d42d00800004100940840d0900c100109119815180701c030006844103207107403508009105100842e144000244124000a5103003010380803a0001d40c07001d04030a080508120080c0e01940c80600980d4110080b540000303030b52144806a11924500c400002c29024031031401c002c147c551030b8110302d00b5010f543c400e00c0006a0000102d41181e07a09a8100c511a1071408090703007082c5080303201545600030a04010100001076140c10b05c0307900d8000c410000030a00c12802c0f6201d14a010440c136840c2c2c0104040780c03c81030003841c0400c003548201318403130031907403900940800d03242c050300d640d0702094010805000d0260402c0345c00317902c05550301c0194101491600040c4a01400c00d00c580001300c10040410010ac1d001c0c401c44a019400495041c60300c1d80d101d1003c2c0003940708031490541d90040d4800d41066281c0f0b13075000d10860ba0403a005040c1c102d00c01c1e48a600940c4020340f02001c0d942c038444002440e078428082c0c94014001e2281d201c0c54003144032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 136765647 1250 136764397 136764437
    0x705031c021c0b1f020f060f1b0903070314100f0204140d050303010b0304080c010c020c030d03110409050a09050609010b040b090910090302101e060801020a050d0b040f020a 76
    0xd1080790907003803c0d00000c0e151a84142c000b101d0f1850050b529005a20000503800c0000d10812506c0704d0080104018808200c13001060069200e55060314540e2400d482c425000d004440109506d03412180040021540c15220162075982200a032000e03108804071580031200c0e10007089128507000b080c2041b40c100003808060031240e050b00c4a05240313405541d00f0361244014000d5442c03002c00880070505008a9000380e031060300c0c9448c001c0210840d400c2c4040e50300c41c1e0035900144280704203d10f01004034482d0160740d400704034660045060078205030010000c5c004c0103013030070b151554620099011450401c12607000e0803041c40000355a52104082c80241d80e41d110200b401030348880c0c10f128000c200001c0d5410400145100007440d002d45103012820301358a400c2100445081c00611107403d00401e1030340c4900e0b409240d0030009207a4810220b4241d0151031402800f281e003d118082d00004d00340c0110504040c0100300040101d48041a40d089812205c7e282e8000b509815418400c80018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 136766897 1250 136765647 136765687
    0x306040507093507031524030f2105070204090212030406050a12330b0c03090f0901030c15140d0b12010501050f060708090d1a011a07080705031c02 65
    0x120090842c0c2401c40c6c5595915040c1c030005418400e41d501d11245100c200036158039041d8554005054200396a801e09410400303424401f42c0c3d207081190784071a00d108003c8a20880c058144d101c2506100042d001c0000403e01040160b801244c49000401c040d0410b10090019000d02d841741500e950701040000d2007908003054401c0c81901c1c000c901d03110768021820b51511410301180c1154098140752515800301e190f9404000b20400c04594211404008405060181c5040d0b64032030090300c008040180c3c550080c0310141040c040d816041c010035642d00342152441c1c005050801c10249070500400321365100004802642e9036507009a8114604000c5c1c07204c0703204920300240030b02d5041100280141036803d4500d48614400102d0804100c4402c040d1807070020028000c04600310300c0d04020016031607a10f403c0440041240010400840403100d00c142c1401c0d002c3c400341080d4540d91141540e501030001130700d05101c103110441c2c0348480001d00501c040000000076840b211200301522000c1c5103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 136768147 1250 136766897 136766999
    0x3080d230105010504031106190203220f060c05030f0301030b0f011e05060319020705011508030c060103110d0f0c06030e010e06130809090408070c0506040b030604050709 75
    0x25800100250f0f070b88a020780d010341c1d4214200980b00b540403000184d240c030031804544400030000d10f40f00601c540100160015051050111400314000082c2c0e5030f196000c0d018603031660f10024010300c42c0c1031045960340c500b284120212480c05045e00c41141241d04240d1048680c6a45141081147c18030000d1190040c445100359607050901c2a1031500b41c06118020729010b200f0100c00642e4200c60a0484211014940ca0456442441d8103150740039141840800c0c000d001110380004107000d001040700c50b0340007030303401401d016401c5544a0120150550959034040d490410303100c040340091000c08629407003400103a45480c82c00c80041d080c0c440c02e4440d460070f42d2605030070100e011000b2401a03400340b294440b04420f43c4482c90050034074050341104d69000081042000104594640100340d501c1c00b4801d01120760b980c5108121551240d80240c0c2c130b000ca0244007041e4281001d4010365004015070a10445054840c034172407000c201203202045052841c81c808180414001035149540c2e04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 136769397 1250 136768147 136768211
    0x1002030403020a110f123d09022704110901080a0308040f08031602120708090603180303280507090e09010e0706030605030c010309020a0b090102030403080d 69
    0x505614080e480d40c1c83e07100080c1c000180c2048031101d070f9840b020709400702c0000400909901c140c0003120360f0b6600020701c4031060b40400031441c9040306218108001103480d030050107111082010018000740c454540100e03089015800074100e4003005041b4102424082d00c544025840c00717080c0908400c0100310140d0052100030014002709034086480084981c05040c10b14490721039203048207007840b440002400c0e1640200900c1000d1050310042e805d100b4150b03003100d6030481061101c100d54071072504c4c0289041001c21000d442824000701941d800184074484001c80b86c3e6401286046900c100e840301c541c054888541c2c00a108900c000311081c10a0003001c0000340340220000d400d0044038002c030070700101c1c81e0002400f400340035002080401c11110a0318001580c80740050007500c5c9500569120b4040e01c0c1580056501c41d02c9400009030300280305481b01440e01e0241001903018103032103411800104808400310751048000e14840100100000b804080d9102a500c41441c4c142d0440140c1c17 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 136770647 1250 136769397 136769401
    0x27040c0e03010c11061b0c01060312120e060711010e060a0609110c07090504140d020d030f050f04030f0903061d0607020a0506060628030e010b03120f0a020a1b0602100203 75
    0x10a000816640c017140d10509596000411b100360109070045c2c09601c1407660804102100700000071002400365209500c400c0001c03490031540d0025a00c0e180c1c5a4842d03603010800146a00c0d111318900c1c49094082c034000648441164599428138400300d0701c1d442e4080e2640010054000d0520a04010110352a81681007a9400903013585581c2d4610030b0144080d12900810140001040ea00707040792080e004883d0083d0301c10310069100c40c010078500c008a85050407401211901d030060a2050078a14007060b015a00c950b016141c2d40051403641c03080041a0300040002016131090800a2a8030041c510b01e5001c00d4500c58039150b801828042103402c003000950000b180050125049a402c6914503151603640f100f0900c02c09010038080d2400c40721004c00c3e81c03441e8066106498440480b8000d120307801c040030070306940d05402d009012800e0010003900500e04c6805019244800c800e09c10303100080c0d13540e240c07800d83c4040440d0800083c900600200007040d0100810724494604400550441c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 136771897 1250 136770647 136770677
    0xe090c0a0302060d020906190f08150918010f020702030106120507030803090a02040f09020a0f0f050409050c0a150f02120301030f020f04050703090b0c040b27040c0e03010c 76
    0x149503480003e000f050081411290b0710420303015144500c0001e07100c1074540184042c0780c0c1c114640e00c10703c8000300d401d1140040b42c182c400e0314034900c580502d901d600c1005c4d910b041441001c020041c40561180055840000070705002c2c000c44228aa040c800941c84030424010142128201e40c4a403003000c016407a40800210080380204c11a900180ca10b51aa03072003030462401d04d5180c180096005241c03e01d004403c0505503c54804140281c42c031118607074441c0d811007107801e206c0c000c424010510200400079440c00f50403c0405034445c0040d680c0244000f8003068504d54680c100c0400741d5407100d80450f400781c0c081c0c0c0500c54a4580c1c80104090400c0803064000d901c0180009000304180c0c0040ea400e54503003a807100b04e1628060420005864803600003030082c10640c10071961010884041842d015680064509882c900700d110f914200031524031030764a03416808201c1e40240d90140d4140d1503580d502c02e020b12001031762244084100040c041508642102412205126440c1c004850b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 136773147 1250 136771897 136771909
    0x1b0c06041409070309020306010b0a11070501140c010b091018110910030207120809190221241501020307170d0204120c080616080703050c090d05070e090c 68
    0x701d0001035403056500c0c0c80c1c81c00104d0140a48000107501440340d240001000342c1100010119002142c4e904040341071600841038540300e0a1044600145601d40300d82030341c108400003402c58042541c000141415140e01142c01c0d014204d07042c102c1c40c0c41c20003003001032840041403071480c16403000003000400390004802c2003038000c402c1914000e0311002d04088030240242c0c1102e500c41d802c00031f80e02103a41000d000030a01102210000c0c4280074030f075a002409418112414503d5500801404c0f42d1410040071030150a000b05103100180301c1c03440c0026a0315075521569580141e0800d00fa807641c07821007501001150f0750111039046500030005480070a0152802d00941c0b01107002c100e070f941d00a450954041c2c0100e0300181d23004a41130100707030300b007143c9050741318112100e8000380c1d107032a9205226865917403004a00c5001103400e003c00030309124440d6000e6640210103080c914100401003010030700008034103604440603481a82c05201b021a51440c003580308051000074071007c0802d20202b48 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 136774397 1250 136773147 136773179
    0x8040611030c151b0c0f07050a0506090616080d0b0f09011409090309040f1e020a080112021302030403020606120d0f230a0f080a02040509042003031b0c0604 69
    0x3e1010080f40c042004a0f00080b40a0504030219800d1a120301145070300c562181030b02c6042a036030303124800700060f050078620b11039011108002e0000c0d003040004800e1044070340c004d40e01c42400c0d5009a280e00000303007018001d0009070400c50800030700411110148524600c0e8008a24422013a10004001c055545501d51000d00d6013965030910a480d250040c03480c40c0108085964031505105420940d0011588030558a452800c0e045000e400d565081c041248100340e4880005900800140461001c400790b0b0007110f440a003c0c10782d1151074a01030310803a0001d541c2100160071880511480b4a01000e01080d140b0800c805040080c0e9511800f0780a5003082c503110051000c0c1c40002058207442c0d444400005c6c000d0030404c1c0d594030341040c00424600201603880e010400e00b90100d00341c41041d2090741d003601c0307001d004d06490380c030f642d12407050050500340c1c183c1080707812216240301c9480610241201280e50a686070190700110030302401e04107000103842c0a440c082c0020000a034010040f6a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 136775647 1250 136774397 136774423
    0x13c080703151103131b1d010b0a080601050708040b0301030f02040b010e01020c040f06081212010b03191a0a09061406070209041b030f0302030d06060f17060f03060408040611030c 79
    0x5400b1003040c5090140500042d1320069425022040007c14545404e002c580d14800c3d84010724980c1c2e212680741c40035001d4034075000002411200068400d5004500614015006103021424150340309180c81c000d038002d80084032030300000d0341d014086060900403200d80c200c003400c16502465480c00000d503203156550901d44115201c14201c000c0601381e60107a0060006034040d102441d154406404c040c1c2c1c003405004030005000d20000803501c44c1342c002d0783d0090040c0700a880c50303404000c030380b800031f815244501102a080d07503081c090103070303100eaa0f80c0d4020300302c42da00400e0143c540018011071211410707002e805800c0800c00f150041c2d481240465001c7e41c0801c03003095604143e462844070540e01c0c0c10060140c1c200c095007209150700007010380607198003072006000c01034440e40e007181c00802d50f0344018046010800040300000340d401c00c2561142c0040c1c030ac000c42a2521002900c0c050b8199000d48cc0c1040009042c054154407001004119107010000c51910207000b80d01980d50b500c170007085e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 136776897 1250 136775647 136775671
    0x306151409040605030a080316080106091811031008010b0414160201110c010501140a030f240c051e0322030c150507080906013c080703151103 63
    0xc10721a5070b19802140507220181c00c840000d0060318001c403481d40103880614609144074400d541703007445034041c4c8d03058901c156100c1c4c00c024a00030b0600701034804c0c2d08490914907240c0801d400540c42c0540074511442c0c00c030b00303440d41d007a00e07191105003110071490b6050301550508483c0300b000440c3d80000c6800010940d482030800005030012130040c0341160b140701c000d010028464002d042d05411540c140c2e184018088855204801040f00040d06484014140170245402a0101d031141b0301c500210844e400b003407070178841100e404004441d008007060b0041074000c0b402512580480202405100403181201c0ca1410721210f0a884065140c1890003040300058960f02054414114074200d0390b8400c4241d4182e0b960301d5007540142000300d90150000741d5a4000504403440002e0040c1201c200d9101d19100800d0030101d40b0031449100214402d50602440b6842e02141754803006e8000c21012001e00426411451b22008051450007480307545400d00e2000f81e200150031080b41d420046c11920 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 136778147 1250 136776897 136776907
    0x240f08091209030c0901060903050c0f0112020306041506020d090503010c02030405060a0311120405151006031508150603060a1118010c02151902160303051605030a0f03061514 77
    0x43d00c0c1484ca180d01a40007107501000288107030b08201d43d44c0649200304113480c2c00c0d02059090085644034010300e01d00282122000002a00f126801036411040c044c20125024a15080700d11408210f54803400050344109403084085510801281c05803108a0081c486030f5603e8100a603a030003207000d00d0b40f0032000010a000c0e0a406580210900414030b00c4440d182c90b003400f0740c400003400880f4160303401e0245444885c1924410440c440c802d451424034802500d04041d0304034000c1c04407400e4180c01382c868220110320868104020007010410200790051868020141410030700b000e4000c0121504200c44543c4070f41090090310107456a00703101c1c40d040d0395240012900311b52001000b9420a40c05e0b50074102e202c001d01e0007440d444007805581c0241c0d05078440120703690030428200221150b403040090000070b20403001010f00c50160286000c610815403503890440d801609404045031207400407001c900d8050083c4802406083e00181003181103a01c00303028480c030301c401d642c03024000043c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 136779397 1250 136778147 136778149
    0x712062009010f0e030c011809110406030b22020309011d010f06050316090c0915030603050615030a080c1216030e060414010806030115030b01030c0b19050d06240f08091209 76
    0x310b03003001003500c80800d000c240e0050360242665800f40c00368a002138203006001c0e02e00e062280380c1005034000d3f003000c00300038279480c0d022314029000503000c0c1400e5500c0303100b0204524603400d4002c07442a96140001007550905603424111411a03104a0113034000691700601294a900300c2804c50368801e01c00f14483c2c200001c1116a15440d421411015844600c90180c050f4558403041c2a03c1c03081c41241d00f5501c03141547e449200d603001c441a89a406070407540d00042001000d8240c000ca201c040380c2c2c0d12001c0c06c11101c0a42c020400d5540c10000d0160100181948283c48920264040d10342515107030900640102c18161118880e060181000c04100030751400d40c4202038020480e0301520a0584a1030300b03034000b0400707100c02d032100c94840744003150340e26002040301c03413502d60380f1403180525401d1300b02511150401d418280c1810350300c10000483d00001401e03000031041190b40210307000c40100b00540701ea61001040d000b0030103514200600e8080010b050090107030106103d940340c0d18848 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 136780647 1250 136779397 136779437
    0x501051305061c1a0403080a0e01020306030307081c0e0d27090c020708030a05040f050a08060f1f090f0e0105014704060f030504050712062009010f0e030c01 69
    0x1071412103408004d101000181a07021503103a0150581c6a003d0250510841180d401c0c2d01081c1c4080b035058104200031000200b91000400040e9820392101c195041c01506400803a0120800b0042c80c1d04810b1402c54400e9000d02e03520f010b04d6800a00b0b03c2d0a11403d209600ba0003075901400d5045c40c0d4807820045102c0c001c00609000301004e20480b40d450b694514001c00b65003140c402d41880c128602404190fa01c1c0056201c404e4030742070b00060000350380c4e2113242010040c0140800402c8100780040b5410300c180d2206120140c62810008519250ba0715a00000c50780060174005c0c960b49080018401516540340303094000680a00c1070280345aa02c8001045180901030008003c40c2460024135900210001e402154550745a1521501050100b5000c0c0c403011100104103400200e403e1080e10000c0076601056401403070300045408018010071800b800704102170180f1000070030b040c01a582d10000e55000344441e032038a044241034070004607641d00d440c1305185041c0807840f0304034985d5003051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 136781897 1250 136780647 136780673
    0xe04021c020d150605010903080307080c07050d03140c09130509031b0606091006020705100306030506040f0b15060301140609090103030806030115080604020409031e030501051305061c 81
    0xc042c002e5003031041c5000c00003058803184050007103083c0400000c681d070152894000700c90b0011001d61031a600da010407a030310f00008083e40081c1c6818032004c80440c1c0200309210080c03010f6100001c0d0414a04001c07502c0d0039008002c240720002c104003500301907c0d0360829000c240150301011611ba00c915492a003180100503803400d5119030803502200c0000005240e50083d441991903400a8070b40305d60444502446000360409030f842510308000d50b082104181005080c1440c000591603183c0d5100350405a0540d402d661103c4556560300130700003c0c494480e0404003900001c10f081c8041404030b03070340b4001446101401520074003502010340303072403045070f104001c01070071405103603184d00c1c015001e084183c1da40750083d0710f040e0140c0020307224600710b6002e82c0c02840c010703c45555242d013044003902d00480105e041107a00c0822461154180900d0210384c01161804507056044c02c080c003042000403059050190f04010620401e40c0362035a420140c040c6002071090702c1c41d081d0070854414944 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 136783147 1250 136781897 136781899
    0xc010c18051003112502090105060306060304030f02210a0e010905030d030203040f0b01080706120203060d0f051002030a0b01030b030105040c0314031213050f0604050c040207051c020d08100e04021c02 88
    0x2000d442d8000b4451713086400c0b455039100300d802c460141d89600901245020440b40541c200c14100080f4000c24054055031740711300560310480f0b500c5c030008451407803026100750001421306000f06181080d103030001d07516811200280703400007005141000080d5a04006c507116000d255001010500744181c068015540681080342070500e540d680010640d03d058034400c000004482410a070700c1403105008a03406010b008007001c185501079142ea08080c0c010540440d03107489007503c036485030070860000c3c44c4501300001c000184100710034005025500906072091190345000f0800c0006a00c00801c0b609130703500282500b24011031507030800c3c61482030b28080300003251103d00b006101d140c2e03052905011885081604da00301503410050307a640c3c4c01614000e02c65048021705503014101940640402c9000e03008544184000641c3d40d82d00340c10022540005070004c0600086094102d0100c039044011821642031440c6407801c02035100310b01800080c41a05030194214410303581d40c040d000c0542d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 136784397 1250 136783147 136783177
    0x1151803110108010902070c030b06030139030203010f0b090d050a0609020f0d020a06030e0c0a0b030105030607110a030c02010908031c0f141501090305030c010c1805100311 76
    0xd124146030010040001c0954005001000080303400c1c5020f000350395003103074171070324084280e82140d68001c1c1031707400109501c1e0159a40e04ca40111004000300801d840d8195800b2549186150b03003071054140c2e10620448185401000100320440d80081c0c107100311580c0700000350300e5800c154006110302d008594064461f2250701c018000b4854141d0142d804507100300c4d082c500c3c059400c810301c1070585e103160b40a94001200c2d14100241c0d8022f0304200e00c40c0b074012055602c40010300c0002070145000d40c02c400c800d04400301c014070850504100040c2c0091190802d44101d0001805c803590f50980c015009041081c030318494011640142e0240002d401000d0580b42c599140c48414214005a0440101018100442d011004e445841844030001c071030326940d103d03a41d8500030026a4040700444604016056030300001149051004d0101d050402001041b040c00c2140014103810b04451000d140c2c41126400f040150f8403460740c030000c61241c0c140421034108865442c90b4600988d019510031031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 136785647 1250 136784397 136784399
    0x703020726060405031c1a040b0103020f0403030c05010b0103060806011203050d0c030219092607030f05060702010b01090506120703140703020405090f150d050703050123070c0308011518 82
    0x44c080080e0480780008400102d200f004207040c44241d68615039105c2004a240c10b0a16050038650024460000c0c103040142c074040c04502981c49681c011382c8103034001504640c41c00f08004082c02a08280402440d05203d140d0401d500e0310380b00c880600c2103141c85114650790204050040f011f480704468180020400c402d40d4150140203176001e00700c111320031034140c100c1016090145d442c0c00c080d1343d180311002c40507190b011004000903d02038040e61940c0718032100040026101c4c007032040000e10420140004d41081c02000c0e09407051201601d0500180c04c8082c006512988180c0b08101d81e10b10050b481611041d4042c0e006040c121504a0a40c0e4030304208900c070781c0c258004000719401070702c000340c1035034a43e1004080c0311820340b103a03032a00312205810300d0300b803400e0565003031030390300402c2039808003690303079070349908450b003151540000c02d41e0102d03098410380840281a9206001e800d0046801080b5a002000f4800c140540058452600c40c00d14095105124076180180786900800c3c0c11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 136786897 1250 136785647 136785653
    0x4180908030112030f1103090d11030d200615100c0204060f15020718090503130303030524030d08130206040f09050105010c03170408121602070b07030207260604 71
    0xe1503040c20260702007032117400e00a28461054808048103540c100c003541c03d01002a082180186c80c40c60107880c040b0301d03411040500da0b0180000e240c803031055155240f11a18507404207030380d114050501c450781c0e0800c00c00c0003800c054000510242c102d0032950710982c0b0142620940e1244500301000e50000c0c641b80011545039a405540d10588281c01d40729010402d41443c1260f40b03902600451040301900420300040001ca9045088900d20802c1a60300b050012002d0980d02e010b95801940000d44030414060303071038070140f5540d00d0b0000008460f90b0316030306400421b5550411101180401041c00c0c0014142e154424800d02055401030586039516900c203030302c40691020b4082c0c50350291500000090075802203000880550b80754446048541c0042062600b4640051041d220a00d0802400c1d540a0a107a840c1d4820100000c2064281c005e2400082c40c2007042e03040039030601c3c420800c080c003182e00020380c0f00840303581406c5885040209001503400c2101d988020050344651001c0c8010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 136788147 1250 136786897 136786919
    0x80a0f1502070c0317041502061b03010e041515090212010509071202030a0617101b0e040e010b03030304050d020c030a120509011112070c1208041809080301 69
    0x10650003140312504814010250008920038144014800040c940081001131581440b46100040c111800c80c00c20350348410111501010a04000058015604102691034030b041420860508070b0515400c0d507040c8544140c84800261016180c4003600300028141881134110403501c60b040c001c02c0703000c195244980c0001c0e40166124168195541c0c002180c40e003441d40b1013520a0180e03070703140725004030308086000007940060900500300740c03506e00115101c00c2e56600b007a00c04504800500607c80080e689808640100c0800107106480e82c4000b4020b03603118040d120501001c80d00090b001402d100d00c00d0050030780314031b4180c150101108000a02c24007050700c07082034846400355181e0000900c1019141c21800e0402048804000041e504452141c4060094103106050813612880c240003020b103059503074449042240c1e0001955000c2040305c8900200a02c00040b0344600c200f5183da4810030344c0a58041c1714000d2481540b402840d40b00f45d085034040700e40041e03100b44c0e296100c0d205061 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 136789397 1250 136788147 136788173
    0x100f0603060512210319110d0e061b0a030b1003050405070e070c080304030e0d060507020c0d0507120f0c082a0f0906010908120a27090c0504080a 64
    0x1214004038100740a0700e84011600d48220f445804241501d0240d1600340b09103504041c0030034214546c4540000000c0a45119014080403100c138690f4480c061403541034150361358000040c045800040038040b5411100791769680516416102e5a280c40c80c104049000381009021160f02010b2680c006c3e50094043c0d002502a03030003a400e6640090315a0701856a0172015520780e00000c001c00141d0700400c2101001d1070b0800c2c805e140c4080c5203100ca800140413400510000c1d6070155541040c0080c2a0b01003040005203082500c41023809030701602c6440d141c000b14450008200002d000541c10410003c02d103038640c03944000c0c00450151034482940c0e071640c5020441d0904091a07403009184454101205100c01004200b40c42580c07925060110f6018054505818040385660209101c00d040c401040d110003a00a40c644030b6082c680c00174034084001c000d03c0d038031099138844103070603461007503c1d04140e5805030300114010101e07000072501442264006d09490088801c1c4008020202000803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 136790647 1250 136789397 136789399
    0x1200303100f0501021204060c1401050a0f0507020c01050702090403140310050f0f0609040b040e100234030806030a0c0603150e090a0b1b0301030309030c0803040b0f03100f06030605 80
    0x20b81540c2c07036078010b9946821030303404d800000030148410403031107100c2c8980d40c0e030f0184035943d11345642d004804028255030f030903501c5200c8a600c41c2c44648001d203182c41210360101031440145100114000064510310483d507000c0e008041c0240024141400741c04440b02c0c0d114403400700f075074900d428455240304200d240642c600c1402011a0200c96141040840d00c00540060440340b801c12401c007004014400c801a00707422a845810403040342d0b10a10490034450b004060141c1d803100d60700e0f0348040c00c0c0255144020300300b211803003101c1d01c00d032106800300690341d0504001e403198465100092030914030450007007a4a42d00c10003c40c805505030840201030ba018103010071420f480704040381d040c150444208071140d0105840b1307008202000c9070b1a0700300200c1d241c6000c4d010510030540300d49a00c00d070030075000310710217440030020814461145002070039141c020b9820103042c070224401610900d0055080104040007080c04c190b4030100c000c000300801d01d05014045d43ea40b10140151404d0b102d03407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 136791897 1250 136790647 136790669
    0x112a120d02070f08011e0903030e0304120209060405071425030f02010c0c0203030f2b0203090f0a021305060105130905061c0b0703050c0409020720011d0120030310 72
    0x14404c0c80500070f100c4004400007000c42c020140c28107a20092004050640030107482d11420320b03020009000500240c0314003041d009807004540144001d0b8140a070005004078684800c2103001d0741e00900e100c9120800701400b40d84c40780740400000050102c00e0201e8030000c8800c205a0400d07400c80010103013001e15030024400d601c1c1c000d0041d64160040b11000c0d4143d0010000c608c0e044041c54020040320011084280080d9401000c01d08203600e13891801021981c00000d00c0a00304080194900030f441c1c1c03c0007064484a80d0307001c06d950810107400c0400c55600c034804100c8a0b80144296460014100c06082c10304d82e071212200c001e00303420b8a1690007414085039082141170202041c07040c1c3d503003109000d5040d84811500714000e01b40240212009c0e00d0070301001c51490784034001000c1d418041d048401d08503001c6122840403100c054032440c14804d401000016240101180e240c1e0b0940909201310300d091148207040082d602c808001a081c00000104056404240301810540d207200e100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 136793147 1250 136791897 136791899
    0x801020d0c0e03060402011205330307050a18021b030705010906112a0a050d05120604050114120f10050f0603070e0a020d02090d08030403112a120d02070f 68
    0xc3c10f80780d10041d07501034001030310203241740482c1417581c01c03040e0440c0100416040e000200070300510646800e00c01c042c400c6100c4041c8200500d800c0007444003905c403c6071050b40b00c4c3c0c17070904100000055191300065640c3c001c0740c1c4250455504042c958a0726621098984d90301c1940303000750082c596400304540541c5016000035800c02107030140c50038889903030101610603444d6070b00e012140e040c02211400e030340709549104001560504c0a0481120b0589900f03489400e001e00381d40f4080341c000c140c0d9010b43e00d0800100000c1c6440345512d00c030700405030794216002500080d182c1c00c100d04003900b17100c0303441855080c424996044d4072043c030a5403402205101a11130707208048e11001c0f81d00c5444811500e01c00441d10400241d402402c56a15151006281c820000003040006550017001c0d074140c0030100c2040706064000944507004039085000e00410036a03405000c4008003c1c201030210810040380c0b218440c1c07180e854003804005040100e036200005510000c0d980c481720b00821844030301e102c170 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 136794397 1250 136793147 136793149
    0xc060509010c0b1308070f150504020a21021c05010b030f0303040b1504090b01050108060a0f1802070606030f02030f01020c070b09041d0705031203100e040503040801020d0c0e 77
    0x5480245034140d580c0c10b00254251104580c2d42c40c0640380c1004000a281483c0c000f450400040c03820510075050b0785801d00303aa0070101e0b00070184050702d44015050001308070043e540c0084441c16154400887c40c110507030000380441c50001c90f00c2c0250000072618001001010542c0d10180d61403240000340415101ca03014103407125410246c070350159205001140008521282c1594061403015000c014031402c500020300361002c80c20140e032480320020051000d560f001c003200c2e520070020303103452a4652a201c41d0b444081c6030b51190304d80ea664444058206000b0301d8044031221900a1010f1015039128104000059209242244a4429200c41a19110b418001e0707071074120344003010f071000b80d140125140c00c6a2041c2d82c11580304e40d403140e40144e102140f06003803aa2011010040c0521030800060500d0610810000034544000384200410141640158070980b5080c00d00e074445900c462500a240d4011134002c03591035400400d0940441c0b05a40c0030300824801075581700d0114941c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 136795647 1250 136794397 136794407
    0x9030708010926190513061106010b090f0406170106050123030a090b09010509190b0112030309080d05060108060603060102060a1512031806020309060a0f03270c06 72
    0x88000f00320b01080150ba00c0c060103051099091a8200300c1140d240c590b0380b5409034841c0045000100100300d004c034051180900c1c51040d0780182c61282414070280c00303071403d038640d604030520400c210348200143c90052600d510002a200e0000a482400200d0301d030040040041008d402d460515031801d5000512584691407050402c0c41c1c0008076410490203642e4000640d100900c0e082d1707010f403900715805c00205200c0e406231289801000001e0642413120070f00c0e042c2480c50740d0100e4241502c1601c43c02203108070907030504558418058045048103031074183c018004144004c1c1c00b45402150b40489c598964100c90303c0386001b6030310900310303a60341002c0058502040d00c082d0700590100000614040c8150301c0b40071380c0da056070300c8100711590b0780c0b40c10940780100810407000200200f40780f20326980182c4d07c00001c0d1406001440c02d00702c01c032022840ba80652882c440030803091141c900301403030013030b48044604d2442c15090891414441e00207c0500300c0d0b10f000f00d030419585000059040d21070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 136796897 1250 136795647 136795661
    0x1050114030c060403060504050a08120402011d012f060405070603060602071805060f12030a020c040b010804080a120204170c0307030302030301060c1b0e0603150f0105042408030903070801 83
    0x40900b803e1138255106c2030700900c0c0c020000c50380c80c45a5020701010440480242920941c000e040415525213407000501e01c2111a0071408042485030428015a80000c880e10300a206140001445851a440845a0303400241d60800d140107080c144801e1040200781d213403d0300c84603282130010903a2040200d03500d003a544141e2200c1c40000440d9100c00c07000b50041e64000d10b00500c204192a600b40020b104241c20010081c03550b271001816450194040c0174030010b90321b08480030000085044000b0f0007026004100802f04200056950701c0c09000b124201c8111580c090210b48413031315800d0000c1c8896110583c80d01a220300c80045495140c006441d03010780c1e6140e800f940c00c503443e00700113a4416a4200341207130891080c1a001300e0341004160820f005010145852603d403c001040c141801400101c80b13481d05403d5040010b600c1142180c02e04445054400041401e0f1802d00181e4000928400c80240014030400207003c4c0000000791484500c11415140156918400d440c22103001d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 136798147 1250 136796897 136796899
    0x616020a02060f0a030e15100501030902060904020702011218020a0803180f0102010902030105130b010512150c0d05040510231b040e1003110108071b0611040801050114030c 76
    0x410031000e5004103600f4082e21018105040c081681e4484880550400c000454880c0d0685540000c211221558142030001000c0038241008442d07016004540103102e1468580d000304c0d00041d0340350459100b802450201421400100062242c1c42882501c04070711510580c07060843c004042894132012003104d012008006090445620800030701c20180e0b80c0c00740c2c1905555032800c0840c0076032003c0c01003500c0707585001c0762802c68981a2428611280301a00000c0c0550009d03454203102d244005103030700c220b407542003003021955550520400c80e1720400e007490a501c0e04210a12040100000750340e005922602414850050807078100c41c0b94100002042d192214900f0101c1e1400c400040e00c43c024907090f814491805440e49025443d1005c1640c080380c207240e16020410034403101d440c454000e0b00003480d120b00b65086c2440c001303180124011381107982c241e8110081f001c02500d50700000d210240500f40743e1b03c0b030b40c0d1070710031500030a400d12585060a00711a0041c07440d20340072480b0010110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 136799397 1250 136798147 136798159
    0x1b0c18020306060d090c0b04030804170309011205130c09230714030c1b0714060315090901060302030706110601140904030807030e060c071103010902010504120804030f050616020a02 80
    0x800e4000b810080c1645c03400940b22000c100d400030074590040001803000d1406030b240c039a43c032807401000c0f103050209900f1102c1d0b2904144a40003180ea802500486001642c10010074662078611110321034541940000303044030903501e00029515466000b058029502c0c2da00c040c4443c0c002c0401000c5007808460040c00907048904d180e403d566603502954025000b01003141c10304141d100c001d007501e03400f0841c0310104e6205600401142d090f290305a0140c42054aaa40c11410001c030f03511000c07802c01c58640d2242003410005070018400b540314500079500201114a1550b81d6070005d40f1501c03603032004400a018030000804d0950740c00c0389801000c9406852161180daa42c1c070110ba0480000d4081d404240c0c03584000258070008111140c0251a08605145d0328000d925115038a4807169503494000d074100240100980e0b00b080940d0211848000b001e4004d5003240741c030020ba48aa13410007440750307844c07140400074860001505c0d84900000100e82030420390700c40d0103917500c1d4084400207500407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 136800647 1250 136799397 136799407
    0xb0406052209080a02070f06051206090a020702040c0e040b0303090d02010e030312190c1e03020f0c0a06020309070b040b270d1b09020a020a0b071b0c1802030606 71
    0x200721050395040d0141420400074000c0c44580c1c40c080c0e81c3d408801e5910042c1e000301c0d4140001c00e400c03d81c400003010281003036860100e00c0c54054141c40c00080c542403180e0002c0e8009040344607036030104c800c0c2550051040240070791949015101e000030015590280d4a03040c0c0c046040c0c01d00008884c0c075058010984024142e0507030046a04003000b61102da0503000900a00c032060303061020540c00741d40507003044030400d40e042010008454003000c0c042d040000884031503000c031919000e00c180d440b906141c00359980001c60301d21540c500c50403089104138410b03894036400b40100d5a0181d40901e881d0b1080d41c1120b90740b00804100c901460003124203ca5040010310143c0000654101c0ca401c4008400c511000e4448000350040d1040744041d1601e01080100052820110a05502400c1400021403c00c011050003d544c1c0c03580502c0142010042e0012030901c80c0141d0000038803548682045400e40368900e010341200e02507210f801c64840c1402d20b41941050340c0e0096a200b908040d007118241 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 136801897 1250 136800647 136800679
    0xf1b0109090c02010c0914030c0f1503010305030301180c0e010c06021902060405070510142a0a030e0319020d0501020d060803040806070f1b030c02040203070507110303031314070b0d0b040b040605 86
    0x12b0000d8240b45502600c0300c10a80b0000c0c81d40d80c0030310b00840c0100041d58480d8903080c9191134030406a200c8405240c544860000340c80c1c2c10045075a1030740b8007880c00d00000d030281d02e800c800074800c4a10740040c10105107468580f280d40020707191303c0756105034182c3d04059525070901c61a401c20981304e4000c21101c95804c040102c000000c1d0a031b0002841000c10094030720314143c00d0241c44c500c0c05000c280c12110725034043c540c2018288540d50800da00a10000620b5a40441d5605000c1c00080c401c1407550b5000081c0314003501518030b0f80c02090402c001e41039443c8842503a80d0700a21030640c49000306000140081e02480350750140000544503180b01028030307501c00444400d44007044083c0710744901c0010168885102941c8aa40d081d2950340d9030703502c541048440490b884410074400e41c000c20420260902000c208030480c4c0d4028000085c40303d14110f8075003426a1074104103c00b08012411a5200d8900d401c04007111070195420010000424244404c1c0d449c0d5000746600148412040c03440c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 136803147 1250 136801897 136801909
    0x60924030302060f04110a0306020a1701030209060d0206070b07020d02070b04050105030403210501030804050319050d032003070c0b010b21090109170c0105090f1b0109090c02010c0914030c 83
    0x48948034080c4106d12545150000748243e0300383d0410f40c0d02603400701d800075145400803c48503980d0411240f580056256a00007500458010600b5000c0c01d00030140c40300315124101031310f80a036032140003003000b071602031002940c070300f00f0390300c1030005100e00500090340394040d0301210207403241a51b41d5450340c1d413280c805880f44e42c440c1144400303120b01c0c9801c09011500313600c40d85d4080c3d442003040316504c5240404052a241010050b14440d0040c038114500041d070010b40085980c485080c0816003600c0c1ca60000a800c0f031000765906103a000000704910300341d01241d00304101e0700c40c24001c8007036602d80000b10703803902900000c0c031125690341c00c00e10100808400c00c1d80c2d0002c8010700100d610b41c9255101010420102e058141820700401ca1040c810403c0c015298131281c0800100501c03543d03585030907500d46100e84429524030380078034154050792003659405c0291141700e40c113003ca0080003000038001c3c103030140c410340000d0711400041260100e04414800c4440000c0080c54070014031010000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 136804397 1250 136803147 136803151
    0x60f0a0c11210c011b030c0921020d120806030712152018090f040f150b04020a020615010e0a180e07030c030b010b12070302091201060924030302060f 66
    0x7011030b000344104144001c0074000c00c3c0c5d5142180d904068160f01818020b0705403030084424400b40007403a081880f88800083d21032040c1002403000c1c00005001d400440c083c2ca075a604d028100300c421100b80e0b084c05800025060051800703500b1600103551701d4805115000a041d40200090000105482580100d03085960f070035030003405241d5204001402c80e0303e00d50044c88681c0410faa0000b11850328500707143c074281d200c05040c8200150f0b241641c5c80c1d8448004540b401031000854503d50003101e00e550340702e4003003210b000e0b0045546140c40320003e96288401c4450700641c01e440d01030550194440c10703c0d00150710f405000d08100ca800c2c1401492146010743c04803001c181d445510440100041000030001e60044000c01c050300d040d401c081040b61416000483e03007030401c01c07161540d00d010141c9640d103e5064500103840c3c1140c03500040990342e210100760284d45c00d0840110f159103256020503540c18614621800345144d0f00c46040844505220140241c0c0182c0000364442c84081c0c0074507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 136805647 1250 136804397 136804453
    0x30f060102010b03010608150f2e03020306010906030203011a0906060a1404060504030314041d0910050a050105040c0e1318081c0506010e1e06040305060f0a0c11 71
    0x810040840f50100c0e08403001d0390b01400503a40010144000c8519a0b0030f410307001501140717100d940e468190000303000704008401c0b0902c20310024050280d4101410420000303554010f0655075a541d580313a52070007401d064042a84a546404421072a58003101d28881d22148007400300d242c150740d1441080070b00d4109410000c14842d652504030142091403000b003002d0440c50329600d407128114180140320b49103404090400603c2000b09001d080d440d00c41c4c820301402c0903044000c0e0fa543c3c90681500381101c15400322a01d9040c071090180c002803642005044c0d81c0c0580702081010280d0074220b070a81000001160054480c6142c01160402c3d072700804021800b100038422209820782c0ea075096a4400b403a0160716060004019001a8450042c03507000b0000f481c00c5481c40741d580d40011503e40b06a40320501007010640c407291143c40380c1055034001c581140039100e045c500145001d400c0078044944141c00c83c540780e00215044d00900034090f10014213030040490920031700282d941ca101228a00d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 136806897 1250 136805647 136805651
    0x603010908040e22080706051503010903030603060b0301020f04030b06060712030903081b1b120409051614030103030f050d02030106020a0c091e02031306022b060b030f06010201 78
    0x1150101e40400000c0000f008000302403c0f6034136041d0384070031000e03000c07980140041c8100384950000c105940142d80380b068005800050b15240c84400003c6450a80384158055080410707032014180c155110408490254400b400502052010503080b8405d0030b06520154109100034000f1548400c5e00503406400617010f5450302907541c80b03640d5070212401c00f24000a4840d0b624008045d0303c4201d680d000100c03d042c02d0b458040b078200e12840d6004413260400d441460141d034105402c000c000e2140e1503036510300410798442d107851b0290054038003119101c20004039000c043c02c4292041d2807800301090210805411079080d950b0849020104031603c40404c1010b2084101d4540310388020340c001d103844c1c2c00a112a600c0c40c940409109456888200320b11f1070319101c280c3d40e42d000d480d520072243c007480005940f80d80340c1e000124032052004020700350b1440865051418034480c9400c552031107100b5a10f5041c0100d032416041602c419005a0343c05240070300204101d2915000c200f50000014000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 136808147 1250 136806897 136806911
    0x301150320030408030103060c0c08031f030b0a06090b060a1b301b08030a0b0d050d0f090f03020105090f040e011415060403170306060d051302040e01090b01060305060301 75
    0x70704110340c0c005440c10b44051000100400810485209401414a0758100050700c84210b40340c220490100070b04540d0380c0007410b1400c01d0801c1600090001540d8000004280c6040c0306e20b24000804160007180192468400941d03003e1a100e000d0310715103210340c0e940f6035803110b0b80b002c12180d1120480007121181d2540100250070402000c850110524114036075400c2c82000c83d00030600502d013140c0c1005891440d59080c0460300302e0b002c503580276078100004100d40707188402140b80d0903c42880540203000382c01c003407008198403003075500c42ca07611943c41420807a21040da40413047ca0b2031200a02003801002a58540d05182e41240e1102000820008040d0a1540110b095a0900103050090045201000a5600002a014158542540c4c00c508150550ba10710101004074848210554404000034400d692028111400000c40341001c0c0300d981801c00010044c40364521040784030318106103030300d603000314144100c0440c80c0d045002500350343d1030490141c00405d80613140513050354880321 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 136809397 1250 136808147 136808201
    0x7110909030c19120f051315030f23090705130207050f0d0c11060405040c0807180e01050913021c050d0f1d010908030c0601090509030403200303040f080d02010501080303011503 78
    0x7150b00008d20010a0384505100401001000c413900310110103207044c40c021880d81554150b039404440c4000d401605920741e20341c0c5194070303d400780690005500a8000254601e012035603005449030301d10881c00ca80118840d08005a100c0004055100004164066042c041842461080f0900501a01544c030701900ca80105091301c507406400c0d004500c1450a0060096000c0c4a0065010321001d44640705410100c0c540750000045c881d0622a01e1100d000ca040d080030b4109142005900600194140c003000714220b40c0f12040880c155031502505842040490245200c24480c5130f840e0358502d990300b803a55003084401c001020f003038104542d250002c140003404000400d10b401126005192542c500003c410944000a10031541b03030b00140810000251000500c4001110b0030242e030207100e2002011074518001c3e0b500440c0440b112040000c2c80c1800130403605150f031a030340c1c000e00150b038072140050354a00c402c0c42042504520b8040d040800d1b8403960000d5003185150004c991418010700c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 136810647 1250 136809397 136809427
    0xb130f0209090a0c05030c0f01030915022802060c040e0915010801020c060c0c0d0c0807020402040e16030903080c0f0f0a080709060c0b06010507110909030c19120f05 73
    0x2c501c0d038256402665210305026404500c04005c01e000c40052401d0b190401c04203800301c1890b007940b0305158554120b00c08101b80e4001a4841c410481c1003103440d22a41c0100c070213000e402c00a101a4458500c40641c4810b00c04500c940c4900c404040c82440c051800c10300c489030b410700a0001100707008980300024111070b0044424001c04410001685031070401541c5030420102800e00c418801c2c2c10000401704840200da04603806405050800f03481d22a4104072441e8422004000d41c03007031001502040f10405104800c1c00b80c4490300c01c0103400b0246000c00e42c11510300070800f0f004245034000003000003a00c03030002e1117918105800706041060304c41500c070181d0444c400e0900070441040400c0640c0d6844400d00340241000c0c03900c0350a505440c1c5811a01039809070800f8100040080d40405011005064064000025014088031705e042054251a81c201c0703a01c0d000035008007083c078101c1d0821200d0b141d800c16001404e00c0402c0040c6841a142c064680e0090000d01209000c00300d008d41041b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 136811897 1250 136810647 136810651
    0x200307021302030901061d0a0c1b050a03080a05060d0204020a0c0b1611071a070303090b04060b0f0402120115030e060103030c0b07080c07020d05010e010c090e060a030b130f0209 78
    0x80142e1613007401e4038414299045a0800100000340d84103012045019100542d0840700004000030801c2803088220b5454030850100700c021041320005d0710800000242c08000c1d1800303070340d601c2d05549580c1e40300341c1926010742e40c0340d501140244415000d440e241d8003c0c4401051802c01c859960210395641840c044107e5125003107100d1b0070846050590066030300f094400c031040241040c40e0a00b034011410300814003880e40b021501240080030180a42e2001c0e800316044003c081c407914051410001030020b4402040c066181d508022503030b030030280243c82c18101c1540480e20641e0820f41079140c0e84070406a030004241d01c0d603510701588801886100c0c00703940280d03074803014400e243c1000210a003000d0310034400c01c034248040007020403032101940c9109904850140c1e02c0d600c0c41c100030340942180312001055500c2c028000b811150000e07450000c440c2e40c0c804052a941d07030241001a151a41d01c0701a000308189400a90b20264990f01d28850505c2221121a5045a50007041c048901 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 136813147 1250 136811897 136811929
    0x10509150c0105160210111215100908280b09101a01080402060a030e01060807031401020f0f030406060f060f030515150c010b19050a0e0720030702 65
    0xd00041c51039020f014480d880803139103494007911001010029950714007624240340059803451103c40410a80c0200da00392042c1c0741c030f108181d084c0340100d10f05c8200e050001d10700c0b40415038500d403403072401203540c02d04035a03950000e0300240e240707104242c0c01c402d00c061080e181503210515890008400440d181c4c05010140700038509205804001c0003161000c906050440003030f00c0c810080342e0ba019021170750040c0e0640342ca0741c4400d0401030903806040e010b0f0384420207500302400801c1e80240043c00b8011280512405464801034a111608070301c02e117008441a0101001b0006040d407148d002503030031a00c106000220a0b40d01c0004c1c68900e0002d411000010b9105240303070391718a51501803280c01600d0f8111000f03440d001080020000f4540d00182609000301181c100f40141003903200300d06820b009042c10b940640c0513210300c00700125074050305204005165000c150140d0f611000340c4070382c03080c0d101d80021013030800e114806018400928840c42c030042025400580303410440e20003040d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 136814397 1250 136813147 136813189
    0xf04080604030f090e0115020f06091b090c0307030203040302031309020904050a0c0e040b0112050903040504150b030c0f16030e120f0a060b011b140d0801030201020a02040506010509 80
    0x4003440d0040c00103036001c1243d0104610040d080c03082801008006045850300c0101d400c06400c4100140d003042c80c070280c0e96502c0d000340d0081000d0307820301154a03800c0880910650b032061052104100000c10700b96103031a400700040c40080c00c001e001c0d03030046801c41d01a0040301d081402e40203000d40e06001c1500421042600412240c00394101800b0b102d8105c466074605010ba0700d10020000c00094031208201d12640d03d400803250103902400301542904109502030003907280c4400540c0e03882c1c1c05803044da800b407403426000c81880a100101c050640d10b5401100d80366807108540d45c070303203a00540300c1246061402c00ca403040c61550244540d5640c1c0c0f00340c4030301c51490140401c21803603102c5191441e503250006206c200d1034000100d10b03010070b1030340001c00203075650810004851203d03c1c00c501c151904c0280d0341000c00d228104001004548912080b580e464006d45002c68901d20b007807200a0140c0d0210401800615050300580c0d03001d4018545641011180c0d0002081e019500048400c0b580c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 136815647 1250 136814397 136814401
    0x50607062a020606010f0e0406060206090f06010e1329090d0e0604170c10020a0506070f1e020c09010f080f010c0e0618030102070c05010215042003030f040806 70
    0x80003581100c803922074038041650030990514003a495483c000d1080d0304011890941e00440e80c01100c0d510701c07900001d03004001c055203880b4007075992072040d0750426252080080302444400005101d60603107401460700303c1a40c4070700c0d640e460100e00c0300004031541c818040440e4100b0b070519a60030f0f01c48102d0702801c0414207021031a01d0070090080012400c1000103043d0764000d480303000484040b50107120786048090640440181000f003c00c0c20342e5844000d6100c13101c1925400920a42d00c503010310305803103d030348810405a031491a0800c0020101b044c0e44a1004200d81e107001160040aa5005413181d450005d4000b9001031030036003000b00086d40f001d0080c440d90a040200443c20792a0300000c1044416014014003114000300c0d007d031140400082802c9058502200703400004009402551070b50311501d01210140b80c2800740c1030052042a01082042c1c00d908941c601a6800008000b42a02a8100442c868103254805c1e50140300800440754550314040040001301418005001a8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 136816897 1250 136815647 136815671
    0xc030e030d020d050c070806093307050306030109051507030f053702072904030c12030b03060a0504050106051210050403091e05030c1e040b03030405060706 69
    0x8108804401030081c0d021100c12a045a0009107807040400a41016a21780041c91407151400c421174112480d20b00602c07003405042803002030380403510001041d82c0300044004aa50107403a61003003007180d20301015200400c1e02c1d0b41c0204002c40d01300308042c0000ca001c51098132454a045a520300b5190122488403c200140340c0c140b255010321103046a00380601c0c2060701d508400d120b424801c08031503005004d03c5080e448248504005000200041035449244a062145601c1d4100c00e19001c0020503841c2c003110407803010159440303903506480f03074929519184c580e19030700c41e40f903c6d0003000e1503034440c81113905a03002c200d11072103244542000b0a44d440e0510307180727003550b00b5a03101d0b900641c005084000e0000c00816904003803001c0010001d0255181e0a04480c440055403000c883c3d4119549800301c80c3c203200d04500182c4800380c0465803a16688002d124442c06180402004c1510b000041c07a050b1a1580084851318401021682816242d6001074002e0b406408115529035403003c0200c51 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 136818147 1250 136816897 136816907
    0xa030e0102010c1803110102030408060a021312261b01020304060609060605030c0705030906070f060e06010b0d0209060706050f040615060c030e0301091704081b030c10050f07030c03 80
    0x206014034540a1040d402c1510132020707a400d02e01008103400c4600c081e8101e20791082040d5030080202008450701810f0031760202c0025030150390314881c14408004003045501003034040c482c4a03984541c0c910712505240c025180020300814180d489102d04109000c0340c44100c80144010b500184001079885c10185002400c45000c1c2d40250740c0c02d803e00108022168001e01502c1c0d00c1413001a5070b940d1403c907450000c2c00c40c881c07403404681c4100040780315414000e4107600f0808261081d039042084200d52040300c0d54a150920070003020401c10044c801140a158000e40300806029102c14105041691a0020381d8801c46e0002a801e419004001c24000580560503e00707203100900b4004a09060000780391603901003001e02032115540c007911064500754006030042d07400c422080c01140d50a60b540a0781c0e8028401c0640030721076029544002414910303030543c1094003e004004500d640c1d004c1c808100035541c0b03000c0622005212000303c1001c80340007001c04511959442951103440d11f0080c0c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 136819397 1250 136818147 136818161
    0x30a09060c260601050f03130501050c0a030e0f03030115050405131e0605010c0609050f0d0f0e041503020f0a0e01080c010f020d09030b2211010305070c050309010c140a030e010201 79
    0x10045005000c3c00f200d0b0b6000001c864950059030481e59583d52450b90721001e200c0b038120b0040c02c1b50701c1c203000c100c0100341075800341614030004e5900b84550350b0350315019075660404004000ca603400410041028202c810a031500384005410040d003446d41c1d40000548040c200052001041e4454920700e07540c10003040c0c515002d1940041c10091030742803100091203103520f8180180f21540d103012702c40c14070174104100b0495004000c211140c9604010300180018900c40540011410501d03110400b0701d400c2c025881200e070301101d0701c000180b46408001c0d10105108503240c014104501c041111074140041034043c1121078010882050b288000412a00022a10000b10341000c0074030244140e01030340b1607003100d401840d118502d031142c3d9061203603581405802041c1104001400b401c011340980540c0904401762000c00407075841ea007064400803d049801007441e00100404000c644c00703506090001400380c60383e0001c403054103c000346400413503001540401c02124250725a5070b0309015410b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 136820647 1250 136819397 136819457
    0xa0911090a170606211c0e040603030e0405041704090b0a0e13060f06080a15060b070803010e10030210020a0b06040e03070f08090603100602070b0a14030a09060c 71
    0x8000401c0e4841103d4a42d40083e007414810720300400d0741c05007040380f81a4213030300b0201c0d0303000d0310305070200c100403005110030700b005c294082035241035110810b161030720030001165016195441103035244820440103090080c811555040d0368030a0201c2442790030040d00140c440f098000560511000c200f0240e1040766000c0722031a051001084403021061000c0b0300750035400b44c00032503260002d0b0b041c0c5010300300d0b90300704540c3d0b445491141018043c41b0070420309a01c196040400030740b522118600228442c01002400620081004000c000100e43c07106074050014000c01c07541903241d5000855a1089802d8140140d100b17040e5513003805507414506400c040304440410441c041078034020b85038010b451000d040d00f0500300c178100902401d0006c0324104080181103640e2454120181000746260740610001880b84c0303480410206520b200301d482e06009070f221412058460350256402e50b1008082200e0280c0b503c50910002c3d01c20701462042100c5910f0b0882a0140340300c86101080d58032101c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 136821897 1250 136820647 136820669
    0x31205070509060705010609050a1a03060135030708040905060a08100f0b0a0801060314061003020d1b0602060714182107030c090e06100e060a0911090a 67
    0x11146058100044580c181820b4880540f5000c0500f00203005000941c0500410360409e01000408281680b0a04041c0304101c03950000c501070006143d940c190034011407505400700010560380c1e80b0241401e0000550720650303c5016010490661b0443e0042c8804a404050108061101c25558003405d51300600545031070820a140007942952052011510f510041e40c6030010400c41d0420341000c0071510015004940090b980c0002d01e0003000340303101c26103003052884600e80c1e100c0320109945008030078414000d21058199002c2009488428400311184042c42049184020f103a43c95000280745517001381c01285801c01024125400440c000704514008104400159075440e1841c600000140c2d01101201c01d1000a9203004500b400b41c4909071181c20b800104108405050000b40d51505100340442c1d0705a080d620b40d5000169000500030034030600902c040040c0c42c40700740c1d0100d0002c007000f41081d035900784801103079a559000004810005014001401c114810340024101d103603403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 136823147 1250 136821897 136821901
    0x2040e160603020307022e0e0a0b040204020306010507021201050609070e010914030313121506030809010f12230105060c100c050405090109020d11040503070306020d06150903031205 80
    0x8140400240944002d0560210110300024401c1143d0501201038462000614040f40155005c14401e0341d03a12078118208040c00340c1120010541890043e800044050617440f65401c0001075040280254100320050000c41d0159643d1003c6070b540842100c000580303810711200380030304404020911410f021804001d03400130790f8801c50110481e00c00a21059544460600003829403140c100300f82c0c01820200004142805080c030090b6420303204440008207450700c00c003c0000e480081c4000f51030080c00b40041131240d4090b41b070030a44c460141c640918040051f20404084030316542203c0040056071340600482100d09006902600044800c00d040c8459000307115602c2101005820a01e5105e1b0a03c8042600031026540903200041c82000c0543e143c86a10000350001c00c00c41d0342503414120310502d4000e850b01100c0a0381c90250160001c0c9095840e13040280d848101d55000701c0799601c000003044819801c3c6080301010340c0e80e4203a6010314500f0014456104014010001d41c038002c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 136824397 1250 136823147 136823173
    0x203030d1d01050631060f03080c1006060e040e010f050a0e1b1c08131706060d020603060409020105090d0809030f0d1b0212010e010509151b030c0d02040b030402040e 73
    0x1c135203922016099051045081185c580038003420041d8007003080503910b0880802000590b602801d1030720318200c1103444005035040c140040d6a030b070344a080080f0782003c43d0202e580c2020f0700710001c10801d000010a050801c03110b40403c5840032112028080c0c0d03078101c00344a508052048000780c0e0001030f910740356205042c00061090a01c1c04209280c030b1030000e40c07101004080f40a4a103903105802c5501500d650b100054441c54000103d40400d40c010580011101c1c07810007040070816401420090555441c1014030008040265041e818000305000c60001c658411030b140c100b251190403a26264042202418030340008148619101c3d0010822060302e540c1c030030800030500b52902c1c1001c4000b1a41e00229503d0002c4100084542d400d01c5104020314805410481c05088a082182c0c1031035500d5810008000c0152000311048400001d00e40000c2c0d1302034060364100c05208c1c002840c03c101400060101ea00503400040349240204c1080305518191140815a5940d00e000d4100030750159 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 136825647 1250 136824397 136824439
    0x50a0f05031b0a090e070c060e0303090d120b130902090c0f0d0203190c03060e010803070b0606030403020c0d0605010326030a0c1b0b0103020301060b040e130203030d1d010506 77
    0x6002d90000b6402107405049288180c074071070010510036000800134182240c006002c01c45005041d2103480c20301040100400d000012240308000c0c0d01c014000140c42440c0c1220300c00743d26402c1601c064ac96402510300766460241100003e00d004100068400c81c5105008191400402c0d10000314801e00500c80307017059100c21100800c02c4030705d00603070780d5407080027802d6450180a03a82d41074a140c48840174085806504c900d0964801014031113403680e0b100b17802546c81c46810720060005249a000c6217035400d1038805150041d100c1e0050303544482c002d074041142c2d00c0a01c082510141c1c2c0340c0c8010010300890010506595140c241c0740d9101c40b0004c034204080340f0000e0852014160b4032400366408038400c20407030b030350503a00c40c400074100035aa040250414100780400e9100e546401c80c002406a0070904880803511009442c46c050b556141c0760702c03090034130f141050b60540810066003442942c248600107000404072442c0f20a0b941808d21182103c0c0005c00d140e00035403d00c00c1c142501502a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 136826897 1250 136825647 136825681
    0x509030913021c0204080105090708010e030d110403080a050d0e0102070201170604090c080309040b091005010f05070b070503150306010f090e1203072c0904080c160303050a0f0503 79
    0x80c0c940540e94140c0c542c00d0055011448482191252005c1004115407106410050003001c0c110100c4602d15103404115080703c46a0410035082e03801007060140500c01d40d000030499200c13820070f280c00c181d1383c1d80708c0103103580c0300020b62000a0400035140c2c1c1015014800c4100d0110742400131400d0145503400a09141210000c071010848d86100180d0706599680103407124985c414500b080191340d4000e2983e4a07040000031901c901e00b000c0540d0828101026000c2c4a002400c1080c01003500e4003005650400d603040201d800c00c5020060f0f50049103d0000d006d0058060303a13038a95480c540035028038014004546164441d401040041040302c20082d103540c103807001c18100042c0d104803135170100e00d032a0100c1c000020350b9101004201d41140c0045520000c0c25942641c100144409004003078440100c0700c0640e4030045010104001c524240042c00c0d4410a20048891a0a4422001180b42000c2d401180040d00008607410107992103401c101003203d003800d02a0441c00c0c145007802c034080e40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 136828147 1250 136826897 136826929
    0x10512060115030b24030a0b040905030f03061512010303270605090307080703051b0d050d0e01030603020918100204050102070302100507020a0321170f0406061a0d05090309 76
    0x46004108545da1015001c514074043c80140c4520314554410245d11034004640b01032032a45002d400340f16608141c094500e43c00e51040146141000c0301d0702041c0a6000500100d4008d8000740b44c4954400c5c841004204454120071143c4841d07165142c0200f01904182c07006585810210407100480329844a580c1900c0365400c3c0f01d51120300c4400030038030740555034fc0401d015106040000060010106001c0c07001091a10b50000c804045d41c00e00c88595950b010042103503000000224510744507406138915054145400b04d0941e41da40c00185448070190742d9541050400780148103400d508000c032580345c504119096042519020000c0c1d100e0505100c040e004081c00b5401041c13440c4900215944164000c01c24040181caa00f42041d48114021407410501d0384c012043e85032074050366071030b0740340002d0101c20806650741c080545107041020b0400c5450a40f2220041030640c0c0380341d4000442d44524007215268a09070605a055807070260520103150070800281c17255446441032032141081c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 136829397 1250 136828147 136828151
    0x912030c0f0c0f240e0f0a0f090506030c06070305030a060e0103210806030a0f02030a05060106051b0622060e030a033306050a1e050903060f060105030105100c060e030301051206011503 81
    0x8401041c40006043c0306c2660140c98560040303203110150341e4607019a102c40030108090b588200c1030558421604014aa1203041840b034940028845c200555100c0078030900403429550711042d40c419a0000e80049400c11120701c03a40601208420403840b0721076941c07801c410345050000102e40c076408030b040064070b500e181c0502841551010010f020a4aa201e0104ea1003980d41380c2000b41035400184100603e0422a401c0d6040d5080000700d06015410203801e418440c814a4040c0d0aa244000030842e041c1c1d44500180304503440a1025201503012500c0100d4017040c0c45850313071801980d82c09240d618400d904280c42c1180d9080b81c01e1400d03520b4500f00342e580c40d014040300f600d0701058450300800020300490142d0302142d110f0050198001c2c2903003110070380d0311030300030000f000401122010700041040c00100200d15118140c0341001202c0d082868011a079529001c003030750401c6581040507030000004102c1810310918441900e82c0b41d40c0030707103000e5042c440d16901030340401c3e41b2401019 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 136830647 1250 136829397 136829417
    0x3060518010302060319092102070803040e01090c1b0320030c1e0a0f03020c040608150c210a090b130302030a0f091d090d0201020a0912030c0f0c0f24 66
    0x1080641c8241c80d115003082c4050030340061401c601245042300b244203001400f80e00c0e400182d14200009581c1510a880780680180c0e0030410f5000051480820020410a60b04261181154000445841c0e0f44c0242d0710281c4030680c0c0400c80c0c64142c11511b9188166200304103c4c00b0500010410b001000400c0c504400c541e895078aa4600d840da1051000e800c0701c500c0c0c1048030400d500080c807039218003009d03181800100d903200401600c030010400848000700d404e000050f83c00410000502090304c4079190041c02d0917551080701903041c01200c1400106580d90000380502c0103a02d2b1060b40f007903c2000e81e2403407031419a0025104d000340e801007428840941c2c14001d4640c0a1010718001d0148141d07a1200340c1101c51103040546000d64182c039650050303034a03400320a44103008884030b04015444074503a2900d4035800c40d480e4000d0400030340801011583c03400010300d010111401003405100031082d00d6040000500c2010841c0d4041929442c100b02c0105006040108880195899080000d034038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 136831897 1250 136830647 136830691
    0xd0602090111031309110307021902060c100b15070c1a07020607061401080d0203070314040803070c14030a0b0a02071103121e120f18070303030605180103020603 71
    0x1070040120380d08403501012402c1600f400c00800004c0842d0040081071142d058040301ea0749072440140e540f0b800503082151402140b05007080c03818541440030384107520301301407440b0b078600b49151111000d050395140c001c420414074011322030320b541004020485141070700590740c0c140c1c072010500c1101d007210903118001a0180405060311191500509010b60319030325403405000404200c48403400102d444000821888400a140c1c013042146030001c602d003082070b4400385c41500e11807462a8800d02c040001064940003400030700000c6203c0d52495108505140044016484d54283c0e540654010350900d0b000c03c0140c1140754000a07031110060b554110750a20b582e0850010003c140c140c4103003001e042c481c036414002824040040c0307842540744240c5902001c0c00307103c0d001154810045030000700c0e64012100103e190405400c2020342e40d1100403200050502142e41c2c02030b404256282c004116505080042c0c50381216200382a000715030540e8002095400b000d030030b43d60088a105145100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 136833147 1250 136831897 136831907
    0xf0f010e0f010501290c15071d0f010c21020f0709111602030f151006080405060612190c031e05101a12030d1409070303030b01140d14010f03020d06020901 68
    0x81c0c6c2c410481501c204078200440380441c43c4d0103075908000240090100c90b42030390b00c04890505200c2c028100700942c00b0200044800070304500e400e441048040c50aa0f00810141807a20886200c075000b07010140d800c0d0a0803420048503901c008406824103c4441d00700c0902c00c116650030b950100354002c010b00c42c0c0042f0345021600c0318140890312807012110380300c0c20441c20b61481160000c1441503410303106d00707044402c44402d0380c0050460740101c0c0800d045107015407581c0c0341c160350300b41220f0f000b04515903030040c00c1c100307084140c1e900f2898107410f00900c145048404100000d016024004144660b101381c0d8880341e4400d1106110754500c072074008000400420b083d100d200805c0194864800d4098070344907880345000705085071810203078006c0c40c2c040e4102c09106500c15405080c00341e02d561415005041280031702410030900100740b40d51500408040c0242440c103d00c00035203540282c2101103440d0701a00121540818040304200580e6a1000465640d0b44040c0140c4c8404a80006a507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 136834397 1250 136833147 136833157
    0x1050a06150f0c0201210e2d150a0e06010b0c011a030312180106061d090601140f250201030b0603091e01020f041206060b0f0711030f0f010e0f01050129 67
    0x1b44282000c00380c50f502e100003d044203224400e401001c1d014101100082400241090900655009102e64034511107404100e0b96014401080100e00c0d01440b01c08107042131801d1704807100007400400c0c0f4240b14502486010b043c1080d84546200c01180c00000a90341d0040407041200c10f41d0204c0051100514402180c01c03090010000340005521080c000d8403421a185944194502c0d209240b40d10340b40c0002c0c284d001c0d040c1a11480e282801440007001d11b03034040000b0030300030706080104075a138004419400c407260120404602080c900f0340300040c02c0e154203490640c0304030350504c00d1020703440740800d1410008015007049026545014803d60190181d20031080105001040001d02c2403001128500c0d5a44503800411002c2e40390702c080d0b0214010042c03c071030b001006000080001c2c0f8012a900c602d144020110b420558102075658603150000303901300010f9440e441200c00021040000700d29003508807000340090340c180000e650a000d420250185080708203054a041c51501e10f0442d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 136835647 1250 136834397 136834457
    0x3030c0627020d060f061401030e0303070c12050408030f0d0510080c0d0321090b10030305040509040615080d0f03090825060507031e0c020606040b060c01050a06150f0c0201 76
    0xc01b09030381e240c0402d0307503060301ca45140c0d001ca0b0910101100003c0c1c04022607200b001c040d06c58540d00b1090752603406048659520210600c01c0c100f00c0800d810008002410440d02c1c007149140c0e41e40208200b02d0240d030b03000342501ca0703582d9014906100303805e80400d2482c2c00d1402600d0070508008181021180d82000b5400009001c01400082ca848441da0b0080840c06004900380c0f821070312200d4200302e4541070703803001800044e4244014040d616000d00629005809418041820f004200320000c1101c0c042d4490711096224030040b50615400254000da4400c1303a00b010401902d0b01d8880034064807034104e1500c2d109401958112964144480071003000c1e8000d9400c1100e4a0312207000303001800d556a09800c80c0900700031041410407180140d80c24a6240ea020f4000c544545040c000030340f910303108203075002e0024018032a003c0e50912a9900c2002d464001041440c68103040c14100c1c0c03949101d103401c001444a40600e5076070000f514082d05607080c03038244617814610380e12428001d0303041806 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 136836897 1250 136835647 136835651
    0xa050604120302010b010f090e0a0b0405070201061a070b0406020307020703120e0a0e0106170603030c0d17010501180e130206040303080708010b13092403030c0627020d060f 76
    0x11a01e03100c1404240e21440c480c3c0c000b00031641200d4015103001c00054007400005100c0807040c01007000c5140c40b150819078048000ca0f03010307000c04c000340070fa4404841600c0143e6440104019100f402c2c038905040c1c1404041c1546404243e444000b01008002d0000d0f0041e0380003c045544607100300401c40013560410580000b140440b1001005910101c5001c0c0c13069070b09038000308940a08400d000e0407281c00d51900d090513409a102e410407030000800640e45070006201d0725110120603c00036120348440d5441403007019070150809030301030040e00300c9410481c4618402002c18120160801900c840032210b030b01c1030352901c800c42c503c0015158020342222020600004140d084411503000d08902e032504841a80c03a0300800f0b080740102c00358541c100826402c100309910080e071000545480d00c1c8070910252940030300300c804640840c0c1c400c03000515100c00398070a105a42c4039110412a2651610401c0c2c1d0714000c40c00168600144040e1003494034200107020000c05d54804035101113004c100b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 136838147 1250 136836897 136836899
    0x5280605040e0a02040e070309050c06041509080705010e0607050106031505040605060117240303030108060105130209032d06010609180506100e01050403060212071b0b04060b0a050604 81
    0x240907800501ca0b064038901c0700e10100301d246040b8000e5406481180c0341d006e110750f035110b6086001d88a2240140d07813500586000c52b58981f03d00c0c0003400507190000003450703a030030a00c0b4020092803144d403011001d900305040910150707900c1018028461403c540d0540c0b10010341c02d080d401031125070720080100c800cac20100780c00b03440c039508110b100f02d000c0c1c01d00b0480350303803040c0040d1040204000c00e0071044452000081c3c2c060611807045804907160b52102407040d18170004285903a0003a08000915809600100481d1400c01003c1b5450035003d4425824420b4040120303940300a0300760560f1210b10b40c60160410107988100041440b4503101c22a100c95a65050141c03000156000f14422405554105c1e104140d15010716030007450701030103400810903022801c540d02c4084909040c1009020070001000c00c1890020380880c0c00b265030b410255062009024188045411501d500c85982c00e0850003ca4003a003041c40c1d01603003001020a801e0740d510009145419560810303980243e0202d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 136839397 1250 136838147 136838159
    0x60d230f01090c0602030702010c06020a030902062a0d0504151b0b0403230304020409050c0a03030e0907090e15130c091703040f090b0d06060b0726040528 68
    0x403074042d10f401501c0031882c582e280c040490f124881c0520103808100d0501203c80010959802030a4016852600040810340c40d8000744196110009403a400c021002c100000d01150004001245c090344e00208010f20094a0113402801144601141d083c50311503403440c094058052442525280406806000020b142064041800359000e50000b1294250290780052a0031440703001e000c02c1c42010700790340e165400c1002800c800c84040b2803d009001c1d454485403640000e045c05035100340c40780c00307400385901d042c4040950014942c004000a0a0003017280d40d000c0782c041d030b070080d502c2c44814102d40d1041000c01d5101c039605e48031080c400e1416541011041d8040048000d4031845a030320a442c058a225071342d5030380564042c0105800214608201a000a92150681c030354080c00031400f075085a00d40c0c00031141140e0046500d5000016001d0421030200564848141c0b0804021b00d035160703442c266806401580550b41c0078055072504c03008250030b400c419040f4940b000c4804c214441c1c17120 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 136840647 1250 136839397 136839401
    0x13050607060f0b0103050903091201150b0403030f030b090412020703050f030d0605191206090b01060f020d0201060608071103070b07020708070e0f061513061107060305060d230f01 79
    0x48442e4032501c3c0c5030511290b5072003400b0741409403240c20010350404400508010089980c510070340d01c0c565a0b030200d2600010f00c400400024100a0103007500d0b03500d581400741a28a0740804034040614150030707000d403940d560031440d0300f2603003141440340a0300d02000f00740e14180c5a40c101900c01d00c5003a12980b00f02000100500d0b508840c0342c0b0a1000315541c005002c04d00c60b51568042c0e204449840501103455160201035007980240383c045105085910707030038034a8600780c000d1400112030404030b8490640403c00030000d0b8500c3c0c4002c0169034603044c0b00a201c80b101508000811450020302d109000041084d075664a0b0025800500b9003441107010355208001e200d41d14490050000000301c040b00300c0042841034a1010140c941a07036070b0b01c208400c005098030b01d22030a0300c09000d03103c18002c0720340805014007001d448060214106400c00703841c3c079507940d1025040600340030402c030194950000b050140c641c0282580542a42003406100514200e4000c4503a0b20030400c5200d00c0348415 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 136841897 1250 136840647 136840661
    0x7050d050c0306030c0f03060c0a02030f0a02060103060605120a080903010b06030a0b090708070504290c100e070305030f2d070318050603072114090d020d0f051305060706 75
    0x4074205c0303050340030300400d02c82030549040600f94141c001d0b40c002420414071000800d0403c880c1c3c41030b40e02c2c0c0030504c0c0c0c08070131b690420300d02c100040c0c0c0000018020007500340b10b1603001d40802c035035101900c07051094950380d40303048001c0100780385004200a0382584094010850035600201483d40ba2300d40095003100504076491220311840200303000c60718450140807414040c1c241c0f83c1c0c40314030302410112a035050081041055009050300c0c000c0c01c001242440140600605407005465541c810006207010f803200c3c2d00c00542c0e2a000b0100800002d0300000883d2442d12007001280e0300c84116125005054686500551800541d021200300c194040002484494801c0d01c0d110500048140a051008140d0195940041040001c549418080c0b25000401c20a044480000f02c4441403410140c8050f844035000f200300540030300c2040c4800f40084003c1e200c0503c010080d030507490b900100305014817802d10741403103c00100721801c80e0b0007450040180401074189551203045140c844024192 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 136843147 1250 136841897 136841899
    0x20304050d0f0207061103090406060305090d0203210402150f04081504120c06090c0b071103011b0c05030d05040b18010e03030714160f0201140702061207050d050c0306 74
    0x9007401c4020214002c07040312149210b2036004040560504005541400000c4000c40b6903110600014215541750702503000030b041c095801003120b080c0b0701c206c03d02c5c02c528201205c1c02e40d00180102054001c500e807005c0007000604507409040c0d152030011441c100128001d0140c482400182500182c040c03500402c2280c4040040301c400c1200040115405e41c019240100300325410880b100805104141c042d001d24015000001c5018031999808994007955200680404002c640c1c5410702101004a40d50050160b000344041250380e00036450726840c80400c0c40c24041c141150b441846801c100352a40b100804804200c0c5041c241055a15080e040f905101e1002407881030052840c2c060042003d140c6900c0021403e5454450b800e442e440700403985401c0d41c18003070110120961618400692984c003918030190044480d0000400c11030442e510340400000030440000140c640e1811548d83c0d60004080505a449482040302c0d076100c0d4075440343d44581002c0601492845000080d80a100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 136844397 1250 136843147 136843153
    0x1f0608070b09100309150b0303091e1305040b07030c0507120c0b090a020901060807020c0d080406110303010b0a050a0e030105040606090605150d0c03090506072c030a031404120602030405 82
    0x11600f9801c40584229010042071071003140002041c0b20810781141410700001001e40b810041a90041296a05051400c942c041d00320141c500050829050345134120944510501103071916454000d0304d841c02900400400d6682c1c107542508a110340d0aa4504a500044480745110302e280000c24a24404070152500d00044002c20110300c00060040c03103456000e403c0c0d60b000c1e071800400f5504a00f004046c2c00640c003511080c1c40790341c0d541c01e01440e03403a4452448907803102e0404100500002d081c1004401582c000c2005001e00000c4405454040e040c0c0d01d40165601d132181c034122040010f25444681540c20801070108100450f000b02040c0c1c0c0100004112183d03a400401103205c6606c00d40b2005188200512103a610341070304a500d0310b00603410089040d00490f0343d064500541200d000c80000c5004040c5095010042c1010b40a13040f1001c0030403003080d40c000001d07100d4a402c4e4000f01400602040d10410002c1c030820b0703e0040c50384e980c074591804502c1c1802c90280d40300306e6007220980 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 136845647 1250 136844397 136844419
    0x30e0904020f0a080f010b1f08061f02030318070609150c14060a0c0503100515041502100c0f0806010f11010612030e03070b0906070c0504020706020d0b0904051f0608070b09 76
    0x1007011110358811140701041000400c860600276200b1000103401650802c9801e2038501c2c111840c403400c0e05d0000c0741c90b030007540d5030b01d0034a1012504270445942c80305a030300040001c10105520900110035200d08801c5c3da81c0c1901c6009007039031041c44810000740400400800300b402c901c4003040380c034031034002884180b10346200320100303c0303a91004441c0811607503c4c4010500c004e05002030403807603000710424590300d802d0700c81c02480401c080b80b4800c0d20042e88048080d200c110000c2c01a05400741ca641030200e222190340d0380140021100410f41e90400c00440c00101c401481901c00d51340e048000300003040000e4950010b901e4004550341c054020804e210b80404480c00e00082c3c04080300c94101d240f50a0148001c10041d035035000b003c01740c50f82030b40c040000c2502e1795284010000c181c030800d4016551f20004061030259110110442c0c03142c0300241c02c21003c68808035500c0404074201e40320750180c8010000610040c031058000f02c60034491344401003185140c3c24014400c000017101c94040340c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 136846897 1250 136845647 136845649
    0x607050f1c0c0f020d050316090b030c131e05010518040e2d100e120301060503060405010504051e13080f0703091a3a09031b030e0904020f0a080f010b 66
    0x5058101715000001c108000141d0f81c076808110207128404a0716103000810b40e10b05040c07a0503001542c41c0d2010440c0060f445402c0c12000e10014010008654070f4807241402031243c142d141510301c51075040c880d0004a01e01e54102c10b140280c03404800400c01c00903010100348060391a00c41c0c06d50382601511001000d180d04041e01600b040070301100c40103116480e1001c06420280954100c070320300c0351082034000124420342002441c0030b42100e0707540d070f6100d10744282000107845043e803046009620348010b01140c0f40c4d03a07208003083e40b8103c60f80c00130703241c031250410b03401050062009414001c0106c1e082607548070030700042c50300c58020380d0362001031178540c4a840c4c01380103c5441405d001c9800c1100c1c458084400003010341c5640c00300c0c02c1e050360420109000700c205207014000c0d01100d990701004410140c00242e401c80c80e61a900c10711081c050940d401400c1e0001c85c0003c1031003807007214006004c641d2030032000e50707038a4006419025600d582d01c0c0e4040d40d034640b030440c111195080403084021 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 136848147 1250 136846897 136846903
    0x71a22050c060a0c350403030804110a08070305031315120905010f0e01021b03090d060b040b0d03020307030201051312030b030a02120304050a050f030607050f1c0c0f02 74
    0x2150040c0140414940d0304041144603400161150148650800c00c08042112008915003000d074200a0000386040081c03c80c10362000c030140c2c02c0115a05000c10710200c2d600010302903100d5449024800303001a00f600003001d00c3d009501142045c0300c4c2400100070024040040d140044008000d030198544512040802c081c40c85000c4000607841c41d0043e136010b110340c206849081c006c00002400400b002c800c401940c0040060401680d0009440c0c0700044581c028081980300302c0c005141800303440b0000400703800d4428800b41056481e6442c02e170b2156101d03400420b170207800401e0b089052156190281d142d4000c022b00341d001d5443c0000068044c0b204000e40d20510350300070010500524408000d400808a0014854240c8038004010005031180304e509440207104070021a1114640b008014100e8441d030411400303586002088034090300c0005040d50084598204141c641164803040102d6014400c81640850302103981c041d05540154084114001150340d40c2c010130220030000d076a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 136849397 1250 136848147 136848211
    0xf0b03030703170c07060c0f120b0112020d0212040606031a060906010503041a240a1202040504033c05030421090f08030306010e0a080309060d02071a 66
    0x8070303c0c0c00080800c8920f403401c46030f41c0100450300351401c120450311400c0444500c09003910210f0b410b480380c20b200a80104801c80c6016000300d0074804c00380014002000c155103085030a9540da000704100c103c20002ea01540c00003802c0031000740107440c4c10b0034268040c00302440180c40c000701c000641111140442c5000f0710070303040948604503940b43d1030011103940d44000c0c01510001c5041a03c80b110b583c280c1c142c140280c9000655000d80e141604803440c1103280c012290f4826a0401c608102b07000c85103c0d0500700d00d804440016080e6501d0406803240c001100c011a080d003901080040b080c0341404890649074039000ca11104c060300c03950152a02c1c0300a0758060040351110aa400f0100102200c500c41e10080307140c1550315a50700c188041480c081e03074000c44410b4002008102440d60305c074404618014007110b48441a0f881c00c24129268070603611054054540010510380601c6d180d0111003829031320450302810041102c4205002040685406001c2414022031429070100c0c800000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 136850647 1250 136849397 136849403
    0xd0b18011a0711030303181e06010302100e0306070c06061413050403050c032106030a0b04030f05071a0f01231e0406061106010b04031e020f04050108010f0b030307 72
    0x344000e2a000c1042094101001c110b410410804a0f00d84544050000d14000d0b10580510b494403040c900c081c0b4204821150403d440700300788004440b5440000802c1811a501a25042107209480301c040750340440f64521190544903100902c0001584a41098000d1780158410001a82c6948030304070540c2030a94080e5022410f014000d84c030407255400b16800501ca0704186213841c02e03402c000e078115080b5410034401c0c2801e0a000300703820380324448400e07449a01107001d48207802490390f4035000b0490203070029041059072042000c203140650100d03001543c00641404c6406041065019800006c8914400c40c507440800011840d41c4040b003e07150142c801c004060110505007840106075030001c140c1400717100d40102140369161361140c20090550781c0d031285510341511058501c0c0c0b00d01039210b1000c6075410801000425540c05c9882500e403105181e641c0c40300840e00024581c08140400e66901c5841c0000000b203480d0158880040c1c120800c20a000c11200d41c000c154072030140e15030107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 136851897 1250 136850647 136850669
    0x1005040807060522240c032a0f0c03020f0303010f06020c01030515010309020103020906040e01061403060307120311070b0a0f03020c1011071403070b0604090c03020909070b0d0b1801 80
    0x80c00004a2041c1001c0c11703200d004038000e11006030300d6000310030344030842188408a5550420b1090f03038040c0347e1003000d000c0d5800c80418480494040020031203c0340e0520391080194a01611381094820b101c4031034098040c00c2100d84958494100440c0b1804500c10b00700503115200c03550740c680d4064004c0d107100b44852901682d86050704401034002d4100240c003281003650030808084950b48140140c0050103410a2040b19581800b001912106000c8101484a1414020048a5070300081c07a002a01c0502c4005005100b86190a80e0a051124254404c078050b1440201d402c4400001a0880e060700d56940c00a948889030160b04a10800303549485680000e00106418840b036005040a1050403003882d180035410344816054480c8554002020303040010041c003446060540503400c410104e804002c1d071005981c45089a190a100003805542c4600018030104814003880b4014a4a40c0a46940303c40c00d115080042140d4441e6910414051070b4420707401c10040c0b880d9058500c242e082e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 136853147 1250 136851897 136851961
    0x40b01050108150a030609050610140f0d120201090204060b090604030809011103070308010e0709051309051603050a050d0306030302071a0d020403080d111608090310050408070605 79
    0x110340001d8018000e41c40b480550f42403206544800b02d400b070003180100d400081030000f91a1035810302c03001030501915602c1c07140b070a001520303200791400c014110840e243c280700706822010941c0b640210801605400b8031680d46004550190005070a20340300b240c1c20400c607600c5441c07104d90350190000058105005210900c006082c003801482d003040141809a11184c1520840b407940d8003100044000490701070041102e0703420000202e4001c003940c20000500340c1058042a14900d078003044141c642e84618448003032041c140b0504045252100710030110a17240e0030041d035a080f60030801c640e00e1041480ca40d140703d221740f00c1d640039282e16038050140a81b400121808005683c400d408102034100006681440d003032004000461051200d1901c400181030f428013101c01e02107a619a981301002003010824080c02109034455001d66216200e4200c500400c1c034280d1381c00c000c072040e0ba01d080c081c4428406c925010f0024244100002d01c00d07513079100c9908015808040b9200c1d00740c2c4907810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 136854397 1250 136853147 136853149
    0x5060603011a01110a120f1106160f0e0916140c060f07020708060f010509060103110d0908041d040b180a0f08070515010f0503010501050d0303150807061d09040b0105 73
    0x420b0f041381d01c14402250441c0c42191615000d2003980c10b1840c0100b40c0105022402c0b58200c41603010540c2403801805503460705410404056500b14140410032010340350065100d8000c1640c01000b9070054020081d51400800309010810283c58045c00309035000380c030144035140c80080310005030741d6034007a107903e803510584800d480300d001e850401075016903440450005800c100342441b500c1d2a030450b43c1217525010900c04c54080151103e4101400c01d0154a0300700302640c21160042a242c00005285d4a1400c041003603001e650040c001c4a0b4468004081d6a185190450f000d030f0300461031880c40380c1724980703da0015901d40c6000c0b200b80e0420003032180851100b8000d20b40e107501a43c0040c0c600710705581c4103030074000081429006480000c005001d5030040c0c007040006090300360002c008550400c0000748400d61104001010551900301c02c44103402030309100001000d648c0115030016440b01e0002e8802c4009403c02600380c40c80451828151500c00702c0d09004039001800b290381642008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 136855647 1250 136854397 136854407
    0x3041208090a080102070302150705030f15150706020304030215090c06032d04050f07060e060702030114010e0a05060405010b07021002010b030d0801030506090c0913021302030c0705060603011a01 86
    0x3070300182d0700c01075440b0009a8000300780010244140309a0140c407200d07120581c1041c1e010405400c04003000030600402601900c40760455030230020080c01601401138440c000b41c40c100c40724906ca011001c0114019081111580195001e14402c0d003d80d03510107416403184070810390880f10681c00d540310420842944c1880c80046400903095010100206607810031511200f07060040d40034110040c604100a010040c082d0880c0340c040c00e030140951500c0e040004040d2081c0f00c1266118040029401c0e0840d94250300c4040100c014040200496a4a1304040d2542c04100c4d011704e04642004005810382c501031003111f058840d400c0c0001d04148080e024011034031130044800e0190365803035881781e00699040241c2c964080072aa180c0c620ac0d030452401c43c1c00c0c80009400c0a1040e440a140a20980d40d00e800d0b41313900c25041c482048500e621400001d1020b03400c120050b105510001c188403584140d46d0040c010503005800310f400d191560402d00d4202c3e1003600b1950319017940c201e924040d0392b2140d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 136856897 1250 136855647 136855657
    0xe010e0312010f051f210603120e0303030c09120a0609031215030f06020d111803010e03090a05090a0912030c0f0e0a14040e0613020a060903030203030703020715111b03041208 77
    0xc00212440307406c41c50008129141c5810954140403422100c00307a690b030101c410641440d042d0041c41c254286075040f10524022005064031070840e12820490302c00040044101007034000e1002d100d04115400c015004010710809800f0542c1420480001d85610510400450303a000c0b81d001840d11158644500035007125201c0f0039025210444040c4140b01d02004c1d000c05003000ca560700c0c07001c0a1004141c03c480390641240d205400a000e40071550740c401c00e0701e40c1160310075100300b40d0903034403695020010710021030010454507a40c420001090707855402411110034030f0f11140180c906103c0f041d40c1c48210308007459480044c550007884004440013000a50790009480850041003010f010750078980c048410b00d10500a00801400754508101c609004141c0c0d410610605411a10000e459100c014040400d16800044000c01c1200307601c082c640a86c45d43e80204211620910010041d80c840b20304003006000c3d150b980126020003000b1a1708481c01d03590700d41d0340c3d12a96a0b8683d9a5042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 136858147 1250 136856897 136856927
    0x130e0f07090e0c07020d0308060f0904020607030807020a05010e070510170a0c18090507092102060f041d010f0906050112150e0103061407050301080a03030e010e0312010f051f 77
    0x8103000720700c01625a02e1006c00c0e2103219445400051a08209100d44510100b0b80030344030700d40130303c284400f68940d40102d908088c0c05262054485e0350b0070360164500781054100900f00c2d8603140c20790200f840085502c5064810882c0c01c1e4400c01c50300d250490309203008100f06a00d003400900400c600305034541c000c4032140785a0802071840d82607420b4800c0242031a0f400007040d141c070b0b1010440c40b55031080106002c0d0102c520503401d0b000c4000040c00c130600384203a0081c0500307000904041d480c88090240c4008000024909820407510b010328404141c080c0301d0007280220703842c0041410f034024060034058440680d58070b0380000036a40124081c3c03102c45005070301e91a20500110b0104d40c2c14403642d02945c00f490020a91010a20b024000d0a00091011080007420b00050050341008a07255500f1605450042100d10041c86224010721081d40000e0103484006040480c5441003200f45049515804030091015030b281d0511109925000081900440145d14180b0141c0508454440048 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 136859397 1250 136858147 136858171
    0x203090904140d1e141213021c03021608150402041413051b010504060309110402270301051303081b03151903081c11130e0f07090e 58
    0x52101001030a0143c0000c031000000d2039074044040d0380745442c20000018201c2e00d404240714002ca61018100e01038100801c00c9012450049080c03c1300c5643e015043c0703034004000b80c556502541d18400031064415048000d401410404e421004071420b00c45d003140d000f4005020f21045404807207842c1d580090040f68010f80d190031102d50030700391b0014284100303850301004100810a09025203020000700d0b002e01031501e551106010783c1d80c010161800c807074480c00e010601400307515003a0740c01411035071202e42151010880b908103590b0b12020b8080c0c840d009408000003012002414240c0f00c0440b501e4140f54064400c03540020703c203041036980700c969621614800030454101c20155401551a1000d00c8024282107600c0d107480300038010070841e20300c020751640789141e4641c0300c03a006000c2c818030840b500320f0b03011044d09075903000030f084000080c22841c0d407200110140c0c0c0e440650b41c0079401d1a5503014002400110f10a680c0a01644881d124000460718004030100500300003011705032422 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 136860647 1250 136859397 136859423
    0x615080c0609030a05060906071b030e0103050c0c0f060105010e092202032b030c030506010207030206091c0b01031b080a1b0b0a09031e02010e04020c12040306020301030c0e070203090904 82
    0x18401c2c006c05001d2042c40014100900344a5170080c2407804001075640614800070507074000030b0f041541c0ea001c208007070a01051030f94854040e000720b40150103034804540074082d10030030b10540201d181c0e810b03a1000d89034401001019001c0c480340d007008607691200c403910041240c52240d404010124000e10060441c0c0d804007281c003032031400005200b0240701500c61080040c4071a074040c044c1b000345070300f1454104018500740c00002d41d50307030003884040e0041c1400203075001286c480d403540c08426070066101c258030406900c0c048000102c00d00c026105864186d241c10075006406e4000c4045030007200c001c26804506840d00c180015400b040351090020b800340000703101d40407001030300d1610203d40703a00406501d541000400b4070341030a51805988140408000141e80104103620340d440140c4006032100b0008d400b5034079003007003070801c001d003c40007040c0082000895001141660b12402021001035610700106901d060150341960240c0c20500081507582440400281c1c4a801030040c1c1a000b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 136861897 1250 136860647 136860653
    0xb0a050a06020303090118051b030106170f0d05031303110712060f0b0301061a0d0b0d140c03031e030405071e060e03060c0a08091204060c0615080c0609030a 69
    0xd0300650001001d40c10100c1085400002845005400c4c6940200c1f2400040c990f075460b511280740303401036240090302c0c100071400398800754001c0001d8410020980c0c642e802d03112001d0340e85c821200c440b84413482010700c0708110a1148080d00d0145214a07801002c0b240290f400f40c510403072f00d4880100600c903a8130001b46c1030869030701c90310443d402690002001c05040289000b0368a10489035802681444010081c1d5510b081c8461349203c1000b207050344940601e840c82000d400c0f0352840b9075000c814619a40c00f8882604002c2c1c3e26401070b641140e4170b8000c01401e05860740610103010701c503c21042d43c2d5045c401d04440c011940288210203460f4402c0d1119400754400301505040110203200c440c0600c241c9401010000c400d00048008151519215190074110b2046002c0d260130454840c002c1005c00c902004040303040681d00305590f44580d100c21008048585095040d26440c0c2070252860a03004803c1140003910f5104014002168009080c003e003a440501407541500c1840c800d8404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 136863147 1250 136861897 136861909
    0x210702040906050f15090105040f0b03060114010206070f0503180a05070b03090d0801080303060402210a02190507030917030702120a0b0702060c03040b2205060115020c0d060b0a05 79
    0x40240b0a010019190400c20f841a4003644010000c0424030703403003460440295100c078290741c11201d0444006c202844005c140002400102c5440c17501840703a0000450304135000070302c2d0304801e1400e030308551141c0e41c0d03040c0c11a84900c174840080003081040021a06418140641e039048104010407551041120368805142c180503a1008a000c0004414800003c0c0280040c030141d16091070260025410414000d88078400a00303450300c41c40d0300040da5201160b1861058590b060308012481503841c00d42a0705019500504520b20f08080540502c00c42c51f014600303981249415a881d41e61644c10500744901d450048207130724509210910040700180e4403074480c01b49508038680600020ba0481c81e141c1940c042c05844407080d50060010000260009030a486e40103401040385420750711100301c0b040780b42d00d4a0644c065070802282070748090017000076119040314148060b03440c0c50240070108a807a0388a10b41032940c818904d0305400c2c08105250400302100078010900300f900f039658000984 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 136864397 1250 136863147 136863161
    0x11010f052a010b06040602060a021e04090b1f1205100909061b171b1603080601081612020c03040f030b07090623210a09210221070204 59
    0x94114290110700c0c5603000b030180c403240c0d60b01031380c000e8103203410544007a4582a004140b132801a5003c1420312505410700a49522418481600d580e6192221308200182c03032048620b9000c1c420940c00d1034490103008488240d4900b941c2d072800c442e021542c400c8005010701030000300340000646000f180c441000d20550403c284155030000e0250110521402c50514001401c42446446507800e071a010000803013039406506680c82012103031b0f040c41c895001d0b00605014499440302404413404054006800f2405654240c0392011a90366034070024001c0129000b0318800500030f51300b9030b00c2209268014102913000c60064038201034a88450104c0d010507039105031400170f03084040c44040e0350041070402c040c1045151584001d00d41c101d1200c0718841010b02e4050380400050750130f41d070420b120f40701240791001e102141500e05101c082200540003110b03060f00c950203d00e81c4d080c40b80c40b002c2070a0244581e290081e0501c000f83e22a0300450b01029803040c4600c8204010384801a035070b6104142d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 136865647 1250 136864397 136864447
    0xa030c080309040509070f0303260106030f050901110d0b18040c1a030405120c16030c09110c0703060e1c210e0c0405060d0209040c1406040311010f05 66
    0x1d52202440010402610400341000301c5980003404203001d004401c41d040001c3e207401d07082c542603030710071249101c43c80361030042e11100202c40d41002050075035068204402c40c86c0b0407081401641c42e0301102c503080300d901441c0c03160f000c3c20800042a950400c2c0e000b11501c03040040407013549402200480c0b0103c0380444044030400e441120034801803401c0301028456110200b1698118900703643c805a40d0035900012100038007003c42e0120303600e01d0800407500318400741201856629980c0c60011040e400b80c1c010114004e0400c0c4030b540c280380201007594070800500009000c01469a00e40310024504071890080502402290110301d00f81190681008442982d0f5907443d044681c1018040c183c07034254011300982000c0018107045400252914800c0703080341c0014094942c90002201c260f0130450007900020407600300010b01099407802811991403482c0044550105000c0108900c03507070100801082d4a607040e8103480d441000d08642111440c2081442e10030118080203565000307450030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 136866897 1250 136865647 136865653
    0x60506010206010609031101051305040914060703090c030803060a08030a0905010f050307021c2a0204060b0f03160c080403050a050708010203090706031104030b010b070b090705060f03060a030c08 86
    0x40181568104001d5005001c07903e0040042c0e802c50707481020318500c6501c0391303042010100d00d0402142a04104100400c4000c200700001d18081c42c04020a07840c0e03080c907a45ca4052200081c1c030450082c001c1c0400a68007201c100b03116402d5664030086500080e1005412814801d40442c052004000078006001982c58100020b4604000101186e54200c603000800509000b480714043e00019070391100405c6c10b8809961410300391044802c0020b0190140c1e09116145003896811500700480d0a140d0080e1014071a00391130301d402d03030064030444140329074084c0100005800d40c0444a012141807031689030000c01071044d0303200e40d45207410542060b11756821402d21501081410000e2000604600b0001d40c210701e0310b06040c43e104c4446115040500d41c81d800105952090002210f02640d030002d150b6441c3d50b1201502c0115400c030880417280d000b43c042c04030f44c1c0c2d41c40c000ba4410844100a01841c98603040351035525003600301428043d042030500f030001c00014002c03613a000140500c1401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 136868147 1250 136866897 136866901
    0x17040f0f1404061202011d03030301060903030e10090b0c10020301091d120a0c081b070f1208190c05010e24150d0804170601171b091807030605 63
    0x8946003550204915128a20303148040100304040c44140084c0307502428800c00071040b40e03601200700021010b0940d0301d0b001c00400400ca036030f0032955803420f503030103561000001e83c00349081c440c0340034082c140100458442c00c010060000010000c040305d00749402600d0024241424180580e0000e03080512625207544030f003c1107482400c8000d180d440c1e200c005168078050306c881c04410340318010a030400c1141c850048001e020442084411a00394600c01781039020500001c10340300e076804e0007901000244420000b5081040912080300e458201214030700d4900401c448240420b4042d100038180712450701c5a0021078804e1103a4041c610844018015030400c071222451558401c200c04142503040000f441a4440c1141c1c2c4245170a2095400500e803600c40e040c00b20752809254400d02c0d82003000711001e01c1c3c840010807a58101c84126000e10403412920025684890301c00f003501410380300f0a000680355140c02d082c015044115400380720210079242c80c940f42442d0050b00269226070300e07142 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 136869397 1250 136868147 136868159
    0xd0204060c1707020f0f0402091306060e0306040302030a0302090103060302040e1b0a12110402091e0f04110d05060a05030f160e07090b0306010512070e030601140102030717040f0f 79
    0x5200503040300b5500b0710709901a130000f5020f100852040d40942c44109241e50359071190b0781200d405400040c6191490b8111501d104041c0a80340160000584642c0c0620498200003981c24000c0360305401031410100f080c0e80403002074002c0c4825038100350f150741d000030140c0c5842c03040c105403959000c054005c01503100c0c0d003080c120f01300401140c00342c3c411403010410380d141c5c210050880c540c440341c2000c880018800290203030195449066100da8010f072185480021000c4581306460f080d44c204881c1c200b840d0402003113400740d500103c000a801c1081c481209680e40c461940701c0750003400948980d4480340800e00d060301001c0e0003a810350290044030042e00c0e082d61001c00500b040d025609941c40e046100402502c010320031000300706004004240701e40c1c040e0003507540c02140301d200c5400e90315154000420541e240d4403958007900a80001142c491101c21a0f4103014006030019417078024160b56034958540c02a1600c0e0512400303000200304c4c0103076400c0600003008081111020107013071070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 136870503 1106 136869397 136869413
    0x6010501110a02010809012414010810151103030a02120606040302031c11030708030f181903020703060f0905070f0509191401080105180708060115050d0204060c 71
    0xc448c45030007134095210b100c1113401280e0941800e4124000640d0180001e030780f0100140040101440b045043d80394000c2001001c3c5008002e030f134280485682950401d44400b03806980020303019401002100300d00e034002800b01d804500d42440c642c00a82d076100303055600d0703050b45800400000028010204880a1811401540d544401914140f07500e81d000300d8090103c00001004150b107a54190325040c041050070006008150b038550b40555604d40502d422401c600c10a0b4005c0b000510307030700034400000010354012440303800da89080d504290064202c42402d801070a420030503036584442207074000341d20b4a046070400800180f070402404180700012001600d1000005050005600041c030a40b14200c80820000480f402140c982c3d42c6840342000340d81c032940052202e00c40314001e280c170312112814518501415000010281d030015481400460054002e04050160705 = true := by decide +kernel

theorem cover : BRFrame.Cov 136690647 136870503 := by
  have h0 := BRFrame.cov_init 136690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 136690647 ≤ n) (h2 : n < 136870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
