-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0924
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:58:49.244988+00:00
-- url     : https://prove2.me/submissions/694bd9cd-ab7a-465e-bdf9-911cf4420864

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 166007194 ≤ n < 166187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 166008444 1250 166007194 166007207
    0xa1223010b03151e25170a0914030306011202070212070e07020705060405150309030d020c060610050c0606120f03030f0109050705040b03070f050c030318010b030304030201080610 79
    0x4150140035040c80c0e480f00b0414990300521414074110415020704000c0c0c04030610302c004451110902c60200300304c0300c045441c41400c1c61800d01610f0210900e00148030100020102642c91031031065a904625007002401d040380155143d0f504055819450132100191a615010044844603030707000030100e0456641254100401c0141c404450000c1d481e0302950790003190a41d4007070058030a16000080d146050001c5500355440a40160000289815520b81d070350009000010b40e80003d1040406a803103510260010b84400b0000b09400e003804070501001c0c410911841017040000c1181104041000490b03540001c0c00780c40e01d06012460001c85803c104d403100a6281c1404000140716000c0703443d001142c160340403c00204081d44071600d0603601c91165103d015000c500c188000b4045034003825100c0d00c2441c007414240d00e40290152407030f085500456880122484400d40c0c02c41086092054403c0110260300440c941400c40e00041c03c01030004001c98031456140b17134071010492041c0f6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 166009694 1250 166008444 166008461
    0x4110d050a03020105180c06070b0a1107030905090a0c08160e040f09120503090a03111905010903020d030e0a020f1f080103050c0409030e06030604061a04050a122301 73
    0x420380c0c480c01c100e881c0090203050103648040c11808950700c1c0c6203ea40022400d1205e903640149420328146140e901c0c0c5006040c014020b071581c0f82d4518083d15403c14010007820480d20a66500e150301d03003010100100f10030081d041c140c4507481c202d0b05900306600000311b07680158074800340c00d403040c1e4110401c644c00400c0c1000103801c00d0803d44101d0300103100d074200942040c89452074005103118400d007110540411036880e010755000306402400700e401003e042184900710004c8d50403540c200300c0c030301d00e9402502a048032161b542d0182101810350600c180741d422601841d00b400700003180c007822035450140202c0680306501d07080e070b03a200954a00040740b00100c101e000408034150320b1100074000c051b09100503940d40c0180c030b58030803c905c2c140c80707900c0c0010b5040c0c0b5072b00e0422100906001d038a400092055412070381d9280041406845015000042c03620701a209598031709000030711244500795400880801a07500e06c41000421604030301d04075a400c11200342402c0c65002400d0701510903030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 166010944 1250 166009694 166009703
    0x2130302060412150b2b0b04140f0109081b100608030903060a020306010504150c02090405010b01030e030c0307061e050a02190c032001020408100b0307050306040b04110d 75
    0x280014441c40c4000c085441a0142100b443d4038071902d1401003e0742c05d503000300f40d80081c00b018000d0010080da01c03140c9140380344411400044a26036108075000f441a138003a2418040e02d0918030100008102d00044804680002d1040801a5803490841e016510b200801d1403a100119001184208490003100c1c000c17503014401c1c40e40d10041542c490740540c80f054003a01a0500003140124540200da000f80c5042c1e40310b6107001d241004000c201000308982c4000c01070004500800341e600c440007680100e00800c00050f52004240014080390100d40b000c400b242c000780f0900e94006c40100c103981c0c0031a04a400400c030940c0d08020155541c01ea6440310380c01a16280900c210041154090891501504103000503002055415603103146124030080c00151503401ca0f13054440c002c5420700d06440050009403c0584840420f41000110202c0302c0026a41c1c0c40b02000c280f400308034410003000705501402482c00c0c2525007060408008001815283c1c0307107140c01132142c461840b400040da810 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 166012194 1250 166010944 166010947
    0x9030906080c0c0a060f11160204050a02040e0928020117070207170a0c060302090d0f21020a0c0603050f070305040503160515060f030a0f23031c020901090302040213030206 76
    0x462402c0402005046c1140d555149040c6000001d070001d001220301c0c0f42c0304400503050441c242c0d800c00c409010018004c08255030207001c0080c80c2003401d21501d00407060580a002001c802003805070301301c0e41c00d4540401240001d4030800160341c000c00c1160b01b0403107070300703c2c0d9aa598408200743d03d040101c0e40322408030280c90002c01e2801d4008075512004d14400e40301c5c9101142c5da0601102a40a0981080da01005500e0204001940d92245054072481070300103d030000300d21910751013504080d041310400350b08183c1d0030401300401c101503680504902d0408110750304084194100207480200440185070740c610105050240030015154901360070381c0c40320040c0400e4034010351106140d2501c04040d01c440004070f0000e00d01a0029554404080c0082042c8031694031040741c40d010440054800f00a038041c81000d10700000c0d1050f080d4041c0200440d41c0e0450382d03200c030421400c0105903100040c0705015043c07150781e00c03818600c101d80d0103c45c056142c8a90351410100d45102d940003c0d4813050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 166013444 1250 166012194 166012213
    0x90907080a1211030405010e0f040f05240402030c03012904091d070b09060918010f030b0906010608182a0f0d12050c0a06050a0506090105030109030906080c0c 70
    0x60310000b2010440d9507a4503000051035403030702113a0702d003e10301409011a031940740e508407906080ca400344407540c00a20200d181c0c00e13400100b10072194140c4606065000c03207c42c88007030500c000c04080034108195011803440c9401c451042007400180501c2169030480d000d5540d40e8007202081700e107121404800345a58940c2c4102c000020580601d007000c00300c00b413440e0801e03800c8000c1b0381c0d0811911030340c40040c50614820708016076540a0401e00c0d5024101101031090181c0400c2d159010b000c0000040107036a003182004031610400a15441140d4000f50050110640c0040c806410410035107028610100310800242402402002000782445d481d5000000480e89546841c101000f6211010610709844c18400469604007014001c0000540d01002052145000b80200c1ea004000e07a440203031b555407001d05684040d504003c11584403000d00115203031040c892401020100e000300710a9a46560140c052006e9101d018180003030640000c1808461000705c0e11071642442c2a42c65144 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 166014694 1250 166013444 166013453
    0x70308160f0803100f120b0703020a0201060f0803120c030c1207030b060a020d110102040308030f04030903021309020406140108150301062114060c041509030b0406020c0d030c0e090907080a 83
    0x4a54496980400458217000456451425040d40c2481c0c0110424070a941ea00d08207034065442130142100315980da003000280300d080c4c0d05980018291000266503602d15210300710240c0390020300660f0018004109020041050400310b8040c045030585507503590303507070706401d400034142022859003220001031040860b0303601241405048103280c6514645000000301d1070300300d010318000102031a80800114122124500140d9402032080c039050b0300c580e440c0ea0100d25424610014460b4194031183d80c2d2045140600520028002d814110038400312030100090a420f8042d0007403543c00500012040144c400303402c00c1000d0401ca50003100b00c0c3c0659026000c442c4a508019610102843c0c020702e503d24011500b203001d44880b851450420307040c800c103100e01d00844d15100042c807030a0a00040041c00070b54105105a0085900684410400f80c440741881c00d07400e42b0780109841d0809148419030803070b020140d0000250361120b82a59101c1030940b03042451340105c48030b44580c1d000c060411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 166015944 1250 166014694 166014721
    0x703060b0d0510080f030405210a0803160e0a050d030c3507050c010f0306080105190b0406080304090216080c03210402010206060603090c04060f090608070308160f0803 74
    0x54495491150f00c2c0c580d14078900b6150b0040700c007001e4540d0000c0104106501c0d20711200784c2c9040c40f03900d002c0300c14188644000d2030f04510309070480394604c01000700002c50302c80c800b4040003000c10381050800c0840c80000a207200009005040c81512441c5008007498031896415684961040c00303d91440c940301e41d540b1407031529880d107403850340b103031070710b485a21030020117541c0038551103001030089507103000041d603c11041c81c904004050751094009030b244130034090540034400c1c1d900405040304800076401f094078054904140160f003444401c00c401180041100c003100c089000042e1242241440c44000700d000c44805065080d010503004880e030b20210040807500800400701340142c1d42d0b4214600314580403107000c3e01603001040054121308000d40110350080c5640705031218030041c800060122040c1da000305008801c125420301507280c1c03520424014002400c01410150700d507903240341241c8134000340184180340c01c080071000c01458400f801e100603401024140c0300d1401d9a0b441c540b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 166017194 1250 166015944 166015951
    0x30702040618060611030f0c16150801080609060606090111030f030601030615120c030f0c090e100e01120219030b040b0c0304050307060e1c08090d02010219080703060b0d05 76
    0xd8900d04040007135180e006072841640c495600000e5400e010304030845c06407a822400308140c2070301404003002145050440210044e03d050f419180c0c0c203100c4081c00410b80d010507045490035900c000144840080001022684a1f004450556680c00306000407034401c85482024500d030710000c100c8414816601d0302441c446c00080ea800c0040303a070349828840c1001038201000c408298060740802c00003c1c15007114014161074140414059150700b070307043c1160a07203011400000e8079004188016182000095007048401c22007580550605000700040e03941032140c0102100070000403021502c5000303d150390480c80301c8181307152960324104010081403c65084a00f984480d000642ca0304041c400e07640a580c0110045051070724070355800004001f89114181103110703042e10926001003001600c81041b201da9200c0816051000303459150800680d00c5406590041c012440641001940c2d0404580702e80741c05102515000020b4004000c250010700c540600040c554280c05016001f0500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 166018444 1250 166017194 166017239
    0xf07050405160f08100e09030306010807030510050f040f0509030d1b120e150a0c02010509060c030c0703030204080a060204380711030f0d090e0c1b0307020406 70
    0xc140d981c08101040102c04009000109094a040c401402d2141003110340c4480c3c180350300c401042d214117241c09500400c0314400d407240c3c0008100901c40d42d201011035001607250a080c01a414082e281c03188045890113541e0103500c589003000c4595035580c201030300100320441e0410660824514503500da62004140242450070303c840000035404010f1200703114206039541c02c1c001d412503401c2c14060716a4440604040c881ea05d0490319401d89a241c0c28001c1e001910002590b13064100040e0030340d28010305507106034100c6401c201020400e00100c1e60301482039805182c4e075107180d00e0190001d0240d900103000901c10b000c004020411281d00510a0741c1c013490f0072481c0f4480d41c0320701c000395841a0740804010001c0101c001c00100c42c25020b402c000b8442c1380701c040b000340b015001c2840c1c00101c030300310030540e800030410688664000b108040681481000180f6600d481103015006225102e028841412228624021658107205850545034001d00901003590340d003081d008040301c400a0f020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 166019694 1250 166018444 166018451
    0x2132a02010c1e0f05090103091a071206030809040c02030706050708040b01140a09020a0e030111030a050106111207060e03030a050702010b0111150718030602071a0925080f070504 79
    0x4610007184401d10341c1030001c681d18503444080d20041217800d0340260042c603041c551108098000a0103000c0c00000c2d054100c88102d200c0d1030900001820081750301d066204052401205101081c992400c4512101c4103072004a241104d81d4000c0780f552084002c0a06180e15100510060f80d41c0720704d48134001c50041001c40c0c81649ca6000b9800c0c1c0095000c02c0d55880030034940200182c04554029103510300c841d044c000300e2840c040010a0039100c40c2c200072040c92000004000c0580050700ca102c0c00b43c41e03a0f1500c40c0c00b88510801300f5688201c01c40c040750702c0840100302d00c005c0010540000d14844c840405690b1a41040540c142c094441960100055420810b00c82003552240c1b4400d1b260080380f80c014000c900c00500e1160060384087e0022003088412400210307210040844000114821a001a41c0d1409820061070014225a07001020f034504028480b88038030001d5074801044414515040103c6006461301c01002290302603205400740000f203070540507022409008548080d101403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 166020944 1250 166019694 166019717
    0x30c09050702010c03020c061906080118150905031b0c060408030a030b01110a2004020714010e060417090d021002011d0604030503071d1f030b0d02132a02010c 70
    0x150300b80d004030001460f40717170f01c0752300059000d60411407031900b04000e000c000104a0b44a803a0f01d400e50310050b4030000c04542d01d812501c200064081040020b200042d4100090000c5649440e141d03c2042c050690b000074800e0480700550341404100e240d010020081c41d176840d550300005840350400151080030038070f4800210103550003004914644800000500405034855580c0d40890140244403000340d4000d21444140741c0307440c8028420a4010303c80341d01c40504104105007900e8640d03039250740300d401c40d50500c80018690002003001800e50b800090711003460b42d0202c0c07200c0122020103035100001c0905800300e41d4040d80700b21041003080c010b0412007000035000a588210681d8000e00150742080002c00191003001c1e40d4091860301e00c110380c0741214035800507055404010709540030362400903810304201d8041c40741aa98440c2524080c607541456000241d0000ca10744402003410307141c008003001c0640381d032000014030440c600020307041c01403080000c1c000e005024100b800310b106003015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 166022194 1250 166020944 166020947
    0x16030e0607020309060a0302091804020a150807200601030602031b0909060103090f0803250206090c010e0a031e1101020f030d0908070b160f09061403070504030c09050702010c 77
    0x5442403600b40c00440c40c00c0440001c3c4a40350703000c03580d02000c1586c03c1c0040081b0b0340d03514015031048003000040c11380c0c42c02e00d4010008180520f5018010b8800a007a03050300c0190082415548012503085c600003003818141c2c0c103852207110300c5c5c000007680a500000310401c0b10729030166002c0c0d000742c0400c03081c109414034190510f204444000c3c0c1e10003040d100081a0f580309802051302c0921945008050303200b2a40c51003010340095440300c2d078040c1c0303d403184065881103d643d078540a0981c80189501e0504000c016200c2107000015410011084072080c244d481d0300841d01c2c011588400c43d100401c084684000f41402ca007002260041c5004160303280f60b40c400549014100242d2000d03524245114907200002c00442c4411508140b090040320081440c00c550030340305d18828521074101d4000d1450003008548102c0c205418850a04818002d4a81c414800050f00c0820701500f9980d4460001c01d59480c0283e506c0140b008205010109803040d181d00080d0007020a07400a104100d4500310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 166023444 1250 166022194 166022203
    0x10c03060503030715020f1902010c09051f27050a050108220f0209070806030111030c07030e0a030609080406080c0315010e040e010e1608010905190c0b0316030e 71
    0x181c80d8107500601903030004c100a0503603c1c0410742440001803528000d101c058509401c50301c610b925a1890707c0c10a10580d40a00845822460300c4c6000c0b107007076051400241007401d22020200040811640c1c8221150166035040d8030520347c00300c5020354148a030720925010300c09000303060007015413850002c2c00d94080d90455020312b80c4205041c18005903580710700340d040e8085005994080c00094810056104c440b180b03802031026a8554210307180c020b00341800d617650002c1c00c600d40c0b07800300100800c4102004c18bc41c0b116526180c0031f003184004c500001d20600568101a001c207240640110030004d084d4028404c880244e00d5000090ba281d000c10403003030004594a12089001a6101d0401e41c4640300c14002c00100800010b48150341000d00b038212401102100600d52004588802040390702000c0f20007811150000d1040392425906e2035180c5062407540001c5c24481d0541d01c00f0008008120406080001030054891501c02d1017030820b032008100e1103010a18050f83c50180101c0841e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 166024694 1250 166023444 166023449
    0x3170d0f0506030d0f090510260f190b030d0c1e020a03080c032a0c060309150402060706020705030d060b09010903120905060408030a140406020a02010503060d1b08010c0306 76
    0x10f0142904a0342c82400780d0307102903a0440801040f0201001140580c1c031146105600c1002c0d560300030314070001159990b645540302194000000341e400411a840d000640c00d90342c010504901e40300049060f4940401810700305595540c58000c81404032195903000c800c041c8414020380340181e00250303490307550030301c0d100002000e50020541c00d002e01c0464400c100030000781c181001104d1400d40e001724094000000d101c036490190400600205085400300540039004000702d803a2803460802c01d480568540b4030383c01da0b24a5010401c0080c0075992030400faa110150880c9081d59103504072f207001600e80c1e000c051102000b502d81032002c9000a44217080e50941081031315200d500ca03080da02c1d40715100d5400c02c00c43c020084c40c8500810b490321040050002000040e000b1601d4020085000d000b000312040c03d074410203410f100410100c0d80c000341e0300c40c5054080c2815a6661034a03030200d41800c80780003010302030042e060701035030f1080c03050000c03402128601c400800c11403030a400100c06565152 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 166025944 1250 166024694 166024699
    0x510030c0506180d11100e06030f100302090f0402031b0607170f070606050a1202030634080403080702061504050c12090307030e090c190903170d0f0506 67
    0x45005000e2410010020800f5210b1001c2044040380500e000502c0005008011101c000a4880c80341c2242826400c011100d4401d04040c41d83c0c42c0d1003400310341c0b50300000306050341c2c0303036100e002085c84203000c0c188030b4004d10340140a01e0810303e0200d940c0c101c403081c03e0758124020300c589004a426590040100303410001d005120340d2500016845464110341c0350410600b8a803000c00500008406010081528610602000c62a2803070042005480059688413098080c0c8000701c00300140e9010a06a5000e045002e515001505040701640305081801145114202600b0005446900020000c0c130580c441e54400400b5a10f10104984482c01610350040400c9000007030480c6241c19041658000c980f80e089504212003441a0525080c0c1514141200c0d00300140305018507901001c1400c80080a6501007218203181400c07510324490003510403260a00b002583c5200b40c400c444210045030040b501c00311007074800d0540c0340d003035100076803080300c09103046803010019059008079480344000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 166027194 1250 166025944 166025963
    0xb03060f01020c130e060a02070c0b030c0708031305060a112a0a12080a110d020715050f01080c011d01230a0906030e012903010609110904051003 64
    0x6440600200e0900158864190b0198804001654032103424900182d50503020102d42d0100d880081400c110707002c0c0116001d940104a803070041810000c8400071260380140155507075503260201c41050050020080088100000b4441c045050125440403180030f5000d8032000c0c0c0310407200404607411b100c070980089405001500c580c001100002000c00300c03121819003108280400582402d1503c8012514041d078000302c611402c1d4070161413580310348401001c110359240204448410f008440030750300e01d150006032880412843d01e61540221a1100f0305120900700307071400d004000824084c82140344030712801501c5640c0300701184110452a11603a0480f51104001100c0c0000b400c010243c8250314400d44022009446c3c1c010140800107903100041f041c140100141505d01d0b40108c100c0580c10300c0c01c0e0740b004142d41c95003c0c2d002000840c0c0113004094403030209001d899a58452800c0a10f0203034000700c0380d40380c0341c020015110210340400940d80d408041c60704aa009000c0505062103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 166028444 1250 166027194 166027201
    0x60f051312020c04050c0c07080d0203041404020c16030213110306040b0f0901090507141c0b0310090c0f0806011a070218070f0206100b07151503081c060b03 69
    0x100c84100c01489405072065442c0000c0c2d40021a0036038600351001d6070346d4403000500d000c4589003802240003402101001c0d20982509a0f8029a680240d01030881c0c07601420300700f62055660b80d8100c03401d0604c8681900e16014180100c00394a8540303110036402441c0781485114124040c5c8543c046102500700c449080d900d4403010301c80100b610309000e43e040000c0a4802a950b42d03141304440c02408580300203d201d20b8505401005446088043c0791110000d000703141c46100081090010424a08000540c03150040c000919280d4168419821103141030f2083e014000d20301c8007401590700b818003000c042d0340c0c1da00520fa6103000c05d2056140c40e0100c1d5140c258220700c601d00504490b07000410b00d40251024000101d182c101c140c0e240341c0400e280c6a0540300300d58051204a40c0036503a45966898203142499560041c40380d604002c04022500000101564840d4412015400e0b86e409858059442e803401500c03940c0710b8221413003040d59100401b507030f400050103100b095440c2070032050308507107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 166029694 1250 166028444 166028453
    0xa060f0f140a05040204080a0c050f0d06090219260d0203030601080c0c070b0d0506010e011b060e0601090501051201110703030e0123103302070b1303060f0513 70
    0x246014001d40c2d1228200034002240d035035600180c00500301c01405050052511f1800034034401031980003c1c001e07410790362103201c59075610251144490308490081407080503440000d66005829142101c21032040300d0100751051418065038442d41c2420461007288007225601da90b41c24905003400c0181e20400010b00c0c1548120081070304518041c10403418224880082c0b0304001840d08000d1200f8004a0310200b1011940112500113000b8207124502041160008012504030032080e55113201c4c0c558200200300700c90344240d0500500030103a41d09540c6507080c3c2c1000d07241c00e10a09128004420300d081c414081840703480080c0c070500804529002480d40c0c04e0740644111103000c0b540355a128020300c0c4c004920401005401c2001c0d402170040e1811154074004049035800c00038121403500412201403182c0c1000049070184008480c0c010040740300d0407450042c06400c50107003100c0202e103000c080c0d01c1d40700420080c0d91080304140032000480700c121044401c00c0b0345c40122209000c62000101c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 166030944 1250 166029694 166029719
    0x806100303030e070911030f0c21130b091509060907060c0204110c160803090f0f0d12050405030d0e0310090611070807060c0e0102030a050a0c020d08030a060f0f 71
    0xf5002c401680d082c40e5a0f58018411a2804006405080b5000003040b540012801d415a0302811314103100e41000802844401c215410007140031120492001088200c4820f444e0120746650140049040e480c260303402d962100b07905c0550b606e5164844020542d103940124003244189400b41c01010600c3c9008012101c1c04400d25007680c00c07503540c00e0010724143c500f5008014000d46800104601c510315203400341c00300550b81c84250a6001400180126920005e5980010f002207410700360403110343c000111f85c00800c0c00014440c107052190100c82a40000c083c0049880880950300030450094007950b807030701000802070781500440f117030103500005c2d540240c22045c0a2600014503920f8420f42c624161302924003aa0000e4010810004200943c06000706050251500c9001200d840001030b65134013888505400784a0041801c50400b44103502c2801c00d180c0040c14801c0340f80b400e041c11242c3c0c0d4429103825103468105400850034504000c0d01c2e00484407039900d00a02c5616200752220365 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 166032194 1250 166030944 166030961
    0xc0e070c021002011d160b3406020a020c090a020f04060c08040803070302250f29180411120105060315090a0203040302060f040309050d0305040f030305090a060f120f02070f050f0106080610030303 86
    0xc000000c0f561000f01d10203201074035180d0a036800402c10840c5160400010600003800d040d3f6a80c010440701d5a00205081540c0482d03101d41412105034410749030418003405280c01c0f2180760310002c21440141940054900c0d43c4401c01c0c04190100c071000c01007040e46000c14010082004844581006002d42004090f08801e196100c45c0c86450303540381040f40c280d4002d4110414810b1007141450640ca810f1054148001400307503135500c1e242d82622400100001407007006d11a40011000942a0000441202980030001c14260140c03802d0942e40c002904180e400b40c0c018031403400060001d00001c0b0419001c3c40e0562903c0e42a01d241c8030400040d10210003080701005024800000c81c9010000210003652094646030340340d142000600800b0b036540d6108508104c804108105a281c00145041404180a0021602410b03110100c0080d04c40d4074002401c00a0101448080c0030020442c8281c1c1c09a10000f800386e10341c0d50401c150b481d03030180c4840020012206041001074041d40c03100d40c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 166033444 1250 166032194 166032277
    0x4120908031b030c010906060617150d050a140a06180209011505130e0403181811040e1e06040b01270e09030301030c0e070c021002011d160b 62
    0x4d4802c00c41e14180c02d440d03a00070f007110926102e0509001ea1a0041e4040142c0228400c401c1c0017864101d100c0708041d0854080b290054040303030b042c0401e1001c00e100564005802c02c411a076051003138004156100c14030b0600b60f4405150041480420000803480c000094000b05001816400d1800003400310902581280620500f00403c22414030300b031918900401840d400322147e482c01e400c0107030440d40d03404880e40c20826940e41c180910012000e0325200da1102503800100035106d9244d0051620507504220b070303100182820009101e0040b4200c8030190081c3c64562013580790305081c003054500d4a6506404951413242210240e00880c0308200c0030880340820322179031651002d0410806030151440c0c517103500008014418041c94402c0030000f414034210040c141c1c905074000810842c0403980080c030440543e2050b41406100750001015000052803030985211640949959418400d40300402c1142e003c80c001440c1c08101c003521051510b44800207103240741d144400d856418002c07540c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 166034694 1250 166033444 166033447
    0xb070e030114010305010f02121612021207020d030e0d030207080d0903170907050a060305270a05010608031206060a0c0f08030f06030a0804090b03011b020604120908031b03 76
    0x29166600340908000c4500c101c904540039411420840d00f502e030020b01c100300d114010000b01c40408989500306034090008c0307180c06040c0c1e035250740c2140d11150050703103040d08900100e19806107d0000a400307004644c0b58085480c1c00e64000c0c410b5040d621101c0c0c142e00700350410500444068021380051240c81d1260600d01d00e4031303906480c0b0404607004641c3c01c1c2c00085c1e0a400a10b0590150b01e54a500264000001d0061a10701800034000c005240280030405454802181d180035a1946682c02140c170468010040307002895040e40c1c6010244041e41e0640c01c043c030010f68a140407003100c10704034a0203000c607180c1c3e07100d02c2170210590200010008002c02e60002d100800c0848210040310b9118850840d41ca0800e403e60840c001c10260040303200780c0000c02908001600305041702c08607044a08041403c0041a0010340180018486040c600e84080c4c07015840943c0465000d2040744200580c958408441004441d54643c0d0300070407040c3d80c800c0208007141c1114014080c140c0c020030007100e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 166035944 1250 166034694 166034717
    0x80d0c020c090a05010303080c03060306070318051f0c0504050907051c050403030218010806030a030f0c0f05060106090e0c071502040b1801020c0105070507050409080906030c0903070b07020d0b07 86
    0x142d8612012104099110f07a100010b0081507031028846401c403a011862034118101840007945610380a4115800c0c15598403550144205680d14104940d400c98159a50525103030900d03010601c449014540307907407411121501130f034014000d403800d50b80098003268455558072000e0783c0d0f542c030096221440d4000b501c145619401d01d402082d114900c42e0b07030007589400041e00c0342d038800b0703a200c40b030141400100717420012191070009800c0d01180d010b141228908804680c19245007100850260102505149000c00d00c400051450f0407200141c3d15030440300d079071315074401c500b070010341d44220215400c201c6203010a02040700b051100040000c01443d0641d0b44540c00343c0341c0c0c03002c15505103900c1c40c030300c0c0e441c8607607018080018030980070300b49686800d090b0f42d2403c2e1541c800340903680c8910307507441c06130060012402c11b40754aa40050021130f5603051500c000c105503001490306900ca8482c425001c039009001c0c0080c1ca840750b81c041e00040b800456075440500003000200a0b02c100401d0075201c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 166037194 1250 166035944 166035949
    0x13081c0801142803020f01030b01021f061205031b06100e040501060509150f010806011b0602070210020a1209030305030c0c12041206110414130f02030103120f020109080d0c020c 78
    0x20341d07010f10507a0b9081c440c61481400541c80a040880f41030516144c040d48140e40c0208075010602540b1000c0d00a00d0b440d440c52000421803030f085010110203500c901b004101c4004010500008413410404a1000c030b81d48056641c04221035440c2400c1514504100c1c1100d0640203d4100b8450000402c1309a183d801083e00c801c0c045800b04800c0704410301080c00d9003401c200300c0c060740b41c0070f182c520820b1078068000b804002c2c60a601035903e40b00c40d00d980c0c0038010385a054505d00c1f68000d1500c0382812800300005d40d035284101050781e240441486245984c0d0040844008980d0306072601c0b0f0a6648542c546102c90704140e2030f003100d6000e007051011001c00b141e4000d20192003080c40080380c0184e54140041140c1a1007109040c0030b0041005000280065034504101e0004947d078146014a24225901400701d0b0400c0340c00c200c0c00400044100001084000071062407559aa01c10954502d012801d0301d14600c0003030f00861003004500030201e401e400000800d103e600482c2c500515082c003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 166038444 1250 166037194 166037239
    0x30807030507031b0b0708070806031902010e040606050301210b07120e2a06071e02012c040e03070308040303180c0b0c12070507050108061513081c080114 68
    0x105c969071100003c0001280e0000186904454a46400107103860880003096544c940010803480d07a08511417841d0440e80321300c2d44d04080580292040c00707025910070b009041d542080c020725240c224000f8040d6440d12400c4801501c082c0c01c06140c00081d11190410794254901e8521841081e440707103120b403d1410308000c200341131030030751650078805c0e60300324031180000c1089840c0c9807060760100220008038100b0790150b0380340d200000c84040c40b04910302c010780f6401c4440356001002130152010406070b0401c480a0f00380a1425101407010407032400d0019120302c80c80500501140c60303034020a020078460307030044000702400c030090440342a131034132481044011a03210104040000591004080062040205041102200c21b051001a549070751b210842400b0321810040400001030913030340c0c0d218118440540c0904955030f41c00454070300170100740040c0a004881c0c030032812003c610642e18040315254420382d54272095242d007802030540f24030311150040e640c0a5102280c0c1480d400c0c0081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 166039694 1250 166038444 166038497
    0x1204081b01021801030609110f0c010b120115050402030103150504020103021e0c070b090306010306050703020702060a121109030706030e03071a010e0903070b0a090309080105131a0103080703050703 87
    0x10f603d03842d000310b010004050300e00d00d42003100b045007020040302c00c0304005000e03142030f05d606e000c449448282014001d801007011014040e03000c00040c0c441c82c9219019401440d40b1601e1444c04031419846006100a80c4000c0c88000c0c2801d407000013500d840c11381640030f0b5400510525016242003c0224098103508140d00a1070240c43c2c0000e4262160f402040584020005044428200100400001d4403644144806080e494407030b030006042912950480304016402801a80c44628030704009201201c00d90900c0a064070700554542d86100a01c103039031824200400501c4441e00b061004c9000c2c0000040c100310520050250100198080d542c05000340e8aa0103490841c1d03141800702c00c0361400c0641080c115410401c120b01c08100312840c5203034081034001004c115100c841c40d04a6503810140e0100c2135651804041c0a04038001c3c0071550341d01d5000c0c3c84a1081c0d0120326403102c440030020312004141150811540e40081d0141014000d4603009040031180700300c5d0035854542d40c14012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 166040944 1250 166039694 166039717
    0x503180a0b0109020c1501030b0718030203241503030901030902040b090c0306010801170606010e0d12020c030d030605030a1b0905010603331707091503171204081b0102 74
    0x110341020150402c01c0325461b00d82c4022105222949140c5a01081c460060169001c001820041c41a035038000d0548800a65000e0300310740c0b03040d240988244a0185044048441d600c84ca0041031842140605802c42144000c0c003039440c0552610041d0020100260300700d03000b98660300307144002e5a42a02503442107500e0520300f5501e140c902d000400c0060142c0104400e06a114040000c0039000155180d00080c06c0c200340c1c130041d007550005038420701442c400030200740042c40601242640415070b40401c16050302200c81c0380c88050380907000c3d260b060040301d401d9809041c6007004104c45010380d414240c14400e68000d056240c0c403d40017a200240c100c240800d40300d0102d0700d21507004a040101c0d6543c490500c0c0041c5566a400c000b110912b481303040400d42e020004132b01114010f0092200030b1003041300402c003140e2509003489407109244802d032580e109501402a00c50004004c4981d11113055100c0c40e425955a0759848594101d100c04180110380c861150403581400d00c001c1c40c828540 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 166042194 1250 166040944 166040947
    0x6061c061401030509061302220203090f0d050c1c110f0f150105090402120f0709060e0a1407110a0b0109020d11090303070b0603010f0c0816030b010503180a0b010902 73
    0x700001d0252070000e000808594440b00c2000064500001555119581190200380c0c400d00c4035584101e036402c420400e008540b001050042c1070342c0002d80341c80d189401900340c94119644403030a650500a0000400b02d0b80c0084440580200003100b01c0e40002c405c50070000d1702c2c404188946440e21030100e10030500d43e8407229060551501c10814045a904e89010403845903040c200032030484c2c0f102800c001e0242d500f0035101c0f01c0007003050204420706c200310012652034940e42e08816001d446c031071052182e0100e002000c2001a0078030300920a01100c0c1440c1c00e0555204c0075001c5075031603000750036031040d4081c02c5405000110f03a5205540244603480c809070b1903800c60101c103002c5851710885020b08980c00c1001d010251004001e450103590016010b01144d9107420200f405002c1c907a0303400010b50f240103610360300548c001d62168000c9020001c88040201005004e0b811a0700b60120580421000d01c00aa00010306103600401c03400d9481c284c9440220554624038480401c4e0001099030f0340 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 166043444 1250 166042194 166042229
    0x515010e01050603060d02100309060e1e01020307020c0d0f02031c1b030909180f030305090d030b0901030b180706050a030e0102040b0403080c1204081006060305070806061c06 77
    0x3104003099014041c00c88a55185040520000d1805012a500203008841d083d402050f0b16010364064483c080c0c0080091201482c143c05598580c2040721544445502d40e1030862055001442940c1c032071210303034000300200e440c40c0e4200100400d40920480b00300c0307041c0d03000c9401038505000ea40c0800d01d10441d4604841000c24010b002c2ea10366014a240580c51150301c10b002c01e0f4400308400440700745500c0014603140040b01c8030342107082d034080a442c880069540d00101a8181e00c4548200901825219401c410700c00403400d0721803200886922400460051000c14840008140c1000c1c003604080710020703111080504014150380314101084000c40d0900101b60107000d080118005a002189401d08101d003a04450285000240003150003213200c07550301c4000c00800034000707044041581c41e107586140f01c43d41c0710701d0305515450843c200300780043c1c01d500030302415000e100704d901c90036070a5030703182c05000705500007000044401c0703880002e29440ea0380c40d10804028040d8248100354411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 166044694 1250 166043444 166043459
    0xe06060418050607030f060f0f060e09010305030a0f0c06050a0b13110d0c02010608070f18051302010e01021c051201061704061503060f0b0a0602060606090913051501 73
    0x103101d1141100d900c1150324165002900c0410442d03802101403c0008481c88041c0c0884001c00c42604a0b44900c2c04603a0041098401002488104c0d00d055403032400c49100304050080f21102848014040d6105206468403940217941c2c0d1200c01e4141c0c50311a030595070584a82043e14800d6421082e11695007103401801c1c02d0100030b84480c0b8154080038000b0b4410110201503034415450514190307607441508584081c400e4001000030104001290802c0340c0310920b06001c00c20a108801c84039031088a803280f200306034090940316001e21021070030400016001501e402e00401200c1e41180240c0300071861a901948044481c064581ea5080e00c034045030103403084140042c5c010000380325000485025010f100350b11594807941c450008910050b0345c00f41070300819980d0304001d00107402c04002da17650f515558800303041d0100480b00044101e070b07502020381e1151829102c260304044100114111401e003607408a4001c40c61a00300305241096845041c200000107801400e4940110010801c64 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 166045944 1250 166044694 166044701
    0x60711030c0301020a021009020d0b1806011a090f220902030c1c0212010f1a030c0d0809012102070809010908060106020703030c11100207090e0c09010e10090e060604 73
    0x7207002da008620301241c000001c2d5840e404e03407441c1c05c1019150307001d400440d10f0b14500c1030003403503000d000900241000300441000034001100c0641602c50040009040002e54080b000340ca1540c490301031a000c802d00c10300160380c07100f005003600044a6802c000800191044902c3c0c03054944100244800b9070748101030400001c0c0382c426206100c040d03e83c2c1a016840b4040e02d03811030b030450f180700341e50000016403030141c031b141d80840d14070618000700c5c0084404407003802480e0041c1213043c2c80500ca0318004200710405d000002070106042445290401c2d4001c0d03a03c2c510314510140302404000c5d44003c54000c1c2c0e400710b00300322440c2c100450b00201a50f00141103001801006c405442950706054009644501c90700c4050204041e40c040c101c00d120421400d80c50a40d000ba01d0304000000c103403070207942d801c0d00c1d101c2c101c002e44c500704041c0012240458545000c001c004c1500c0000c1e4680000002118006090070b05404143d03040069444103902c50032100e084000d014010504d0210200400c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 166047194 1250 166045944 166045963
    0x5090f010903020a05100210090515090a21020703050322120503030a0c0e03010c020f120406050412030905180105240d050711030d0f0c09060203040b0703030b06071103 74
    0x501800d0841800103030b507200c1813202500c5060701c3c03d043c02070003140c08910b0880c450090405141c503080303000040c40004034040c80b802160840c1c005250b103880c405d10b503031407a00c3c0710017170310b28611340c051480502032a51074880514000e10465001d2070b103d031211800c580c40f041c03d404d41c0e0782c4044215081e8484120103035000b0705200d40340d21403e05103034441c0d64407480300900c40d0508540d502d1081e685640951030f8949903110140007000704510109020f9070f246900c82030310340c491080070901c03480809103600b03c8080d02c0443c0d030340e241003601c0d0040458120241c02000c0b0140544440c011540752242c008078004006400c010001c1940360905120300002040b04101199200c28080c0228a640c01c0480700320f100103880010707140d9118102124803a8404102d11080d000024200c801500960011210f0380d1400c4c0040000404d01881920000940c1c0700300405600180010030160000901400103035019017030104902e0000c000189a5500c80c1c0d104460038070305001c0c1c400a034101041005c16 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 166048444 1250 166047194 166047197
    0x51c03021803010905070b0724050906060f010914060f03101809020f010c1a01081b0d0c030201110304092c0d1d030106030f06050708071b060209041b05090f01 70
    0x3d2080b841d101d483d04e0b0360f690b014500c021440041c5500070032020144074240c1c00340d41d214150322518127403400f501400d419120001c0d41d10502004c40d255113800c001800b0f01c160140c46070400c5900d0490490015103885400300e921801c01e21035010b001103000011840f031000040701003d03103401c03d10b0b80b01802220f440072011492400e0076107401030301c81c4800b80400704070034240ba03807900d0103525001c850800703000c0c0100740030b581c10340002607448400036105080311200700b0482c02118460051125079881d007075010701980c20b21142000503500030500d001075101588280c9241685071a0800f059803581c0d0541d110005011101c4490002181201c20000e031441c0050001d00300c5903c00141100005404c1c040c0a000300050444039580075030025000f59030182088074890a1810090018230b01290704202291710000000d90081c82541d100d8100c0509509510440b10300342c0b5000006d40020946540282c1d0b1056030050324244030000e6281041c1c0d039515159684200c4051184100e041a111030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 166049694 1250 166048444 166048451
    0x618050f1c0f05071e061a1903060e03130f090507030e0a110102010b03060a050402040b01020307150504111815030109020f0f0103020714150f040807020904051c0302180301 76
    0x1c8126600c8890061514160300c0e01946903821821308900466524082e0001160800115402c01600c4c0c1c0003580a522a0788500030748440f10030a00c50a50301c4988420701e41c00314a01c060002074990350101e42928107000451b4100041250101e5451000c0c0d0400d022040d442481042030107518040d00b94071203d02e140600507210070f4030980b0b03a1507032036203030003403901d110704100304402e9200354407000c0c140398010102c07290f50400094200c01488207540a0740907078201800d40425500000454603000e5024151142d00e02d0f11804902c010140a8812142c035800040500360035030300d1640a04024a0b0500e600306103045c44a000c002801c4044c02c1503001c0d904207554200943c0e0b85625202d20480161007546d007004207400120020311a40c44014a42012501c01c0d1422503000143e04a4600c4405403000761910749030400754a8280840317004007601d90800c001c0005050003080305400c6849070702151600059800d03200c07140b90748420300b900029404915007442121240b1910b4034204240e0080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 166050944 1250 166049694 166049743
    0xb0a060c1101120c09180203042307090518010506030105061012020f0309030711090c0301120c030803090a0b0c0906071b031a0906060a051c0618050f 66
    0x2500246081801600004072100401641d90050b415101d254815210402c4400580c0c200540102d1440c0141c001040070814001d4400c9640d200b120b0080341c00504400034082c6488d00241311510800c100703011801003038000601c04205004141c0148054200c0d00c00806504d80404d00f100c0004040c1c5110f0380c1008144202c0f511010b03490364141c0f40ca03103040e81d030a1100e0014000a44103000c2d101904850010070008624008000340c80c5081c80341101e242c80704419401c101d445a400e0340c00410400301000100041d8070500e1043d103402d0303c1070003180b00055890b00c030142190030807269150142c10441c101030411685100855000e40d01012a07824440d081020540b24006d40d0401058002480d61600c03001c0060b00e82c0c0c000031175001c0e040d940c2040103008030078840d035400c0d9410609031040708089500791412483d0322083e42c1c00601282c072491500a04400503000d507134400d450301c96039401504c0506c0341c01d40d5440541070088005014400c14617910612348900c0040a055a20700d42408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 166052194 1250 166050944 166050947
    0x6020315091618080601060825080604020c01091a090f1f0b030f030a02160509090c0f04060509090105100501050a09030210091203020606030f030703090e0a09020303070501020903010b0a06 83
    0x2c0c00e9201c1c50b50710b081c5032030301c84003030315410b0b00105030304110f126104800002802540c0400d650f80b15540300c01c1600d52051700d08142c880c0c2025021015000b14880c0c4000905904241d4050702110841c0f000100e02420301740c03610030705041b000701c4a2011040810801c06004020000d44440051940040c200041790521000c0005420b00603940280c1d140c802d000f800e682e04100b05158251004142c9070f568100300d00c065031f110074280e800001040600700001b000c0c5041101e1b24480d1100102034000b0356024802c00882c42c42d12502c45600c2551100003251a03246c17894018400c500300e0000040e1400d02002160304130000d580042c6c10002c003000124981c990092808044960595080b115042d0510050b100c00c0c070260062841f01003000c403110181a8000360340d500492058007a10700d0240500070300da45078440c02a0150211b504048204410000700c2c0d20103521101c2010f0000e24218540d00003400c5500c0910107075241e030740106400d030662500b031242940b1110100e9049100600c2c0c01c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 166053444 1250 166052194 166052221
    0x70519030c1d1e0d080a0c060b0405090607081f0801090c05040c09090c03060b0d0906060803190e0a05030d0903030201060e0105090f09100204061805060403110909010908070602031509 81
    0xb050f280810300d019200300d0544850307100039111079112201303a85846800710020501e0041c4031003540d10b0780c2080c4d41c0ca9940d00f00340c41524042d841d41d40c0500200d99844100b907440440c00340c2503001c490300041181d11401280603c0c0e030040c041980010504c25580e0801091444290f080a48180c0c80c0008950000390080d03280c6040b00c030f08560200c0c8542103268150010310913940850041c01d00029a0b0485c100c403680301c194240c1c070a0204010294403800c0c07450b520b0007100c00070210b2001312081c900e4820300500030b84000107402020001c120740c80300003181c10300400000740740200d84505010320070150280030350805803900324117044043d07251a002030b105442c040c0101c00b0b6907c0203808030700584410300c040c020a51048400b950707034981da00307401003044114030b402054030100040041018030b0312108030740451750003c11441c0304540d0307001040101d0030003406c04444c941d0380300b07003c80000701c0c440b003e400390300e005000041e01c3c1c2c6001401000b4441071010300605c281708403c100302c401c0c902d804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 166054694 1250 166053444 166053469
    0x14010809061314150c0702210c1e030f2b05040b18040908041706040b070f05070b04080406080a0902090106050d06051807020d020304030b040308070519030c1d 70
    0x202043c580e0403218025092101c08000c4d8041d01011004010f0007548802c01450300c00c1c800d0b04c5505c04258481c8a4083c00c10321410041401e80040d003400049180c9411041803070200118140007640380e01c03000918004801d0707080c01c003a03001035142c3d10b8296419102000a076030070348e1a40d0f45120315600000c0103403149003d00a104440490a01d0100b40c0e80303964400411000741041208000358280880250800d1103502c04840c3c00c17201c1c500b400c0d803001c9002409154407072403045058903286c80903a0500c04a920366810440d0a000c40070108504400f4203008030301411001d603480d400e01c04020003110004007421817043c2844894001602d503140540e0450700c00b460304640303500c6460380d1400540090f40c40181d0046803130118903500024a44407901504550f0202c0c1c801074080c44040e61640603c0c4006494202401c0000380464001c15000d64001118909107140080d0b1fa20907403114180580c01900003642c4030440c07001190048002c464850346001c010032441c0c2d150000410701e0076401c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 166055944 1250 166054694 166054703
    0xa05010e0d120c090513140106020d050712020309090f0402150405010203071b090e07050907090f1818050a050d0306081002180402070312051501080c0c070e01140108090613 76
    0x807882c80c2c44042c0310305081c4c1e016180c0145400c03050f44400d04480b010f02441c00700039a0b401460000040c01600001e1426218001034a40e40e041c0001606c0f01c8601e16034a04402066000801c80c01009503503d040d614400d446205030034031a814540188200640020140901c081c0200001d00040e03800009449260381d201d045a25a0f000902c0000c032007140e90b07801084c03450700303000081c405800c0110b0704900755801903990340f429503210b150480d0001618480e401407103118402c28410b03400b0700641e1012442c6000f4001c04c29845007500b07a50100f80c1240b041e607503600401f400c0f2007004802c1c014040b211b811842c0c20300c1842e0614042c40e84a500008440e40e10650000300c42c20345549109030300d0725112000344210344680440c00c2c0909000d60581551b01204d02c0d21000440c3c00c03402c880400240c05040c0d640400aa070fa84c03488803c0e6a100900d10002c40c0b19242001981400b4045494060282c84050180d80c0e5441700014005400240550705250840b00c1040212004007907113480d000d030003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 166057194 1250 166055944 166055951
    0x5010b0706180816110907030c120203060604050d0305040b0304060902240301261e06070c050d0e06070605010f081539031311010e0d140f0106080a05010e0d12 70
    0x340d2400155401740c05003030342d400103170003010030600541640c05210b416985071100d2010518011302e4a00328030040714145d1f44070600b444140102d061041031900c01900c43d040482c81c080d00d0b20b08000c9581c104540031100035895018040071400d04941110700c000b18032091140080d2902450915400305000b0200d600b00cc6101c50303040c081201c0004056a402c1000b503498130b003402d10040c2010159030380300d10180d200b5040441d032041c5c0b00d40c41e21440150440054125607101d0002210b484981462040d4050030030701152012803000d100303060091030070881c7c5010040ca80101c06040202200c2c400306041281d9080010410361080398140c7d001c1d0040c200800c0c90303101c00f100310300200000700d0800d20390720100400c90441c20492203840d0b028002d038a1882044074800c01105c404041c2e444003600101c15228400000e00460005c2d05801c41900907a880c000110410a00310380166200e191181d001101702024800e00b03204a140c40c07407290000d018258003403403000d40320188000c1d01070055980c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 166058444 1250 166057194 166057237
    0x804080a030b040207120212030f0f060a03020301020a0804060c170610030e03031003170a0f0c0303020910270e070804020a050a0e041703060f060702060403050105010b07061808 78
    0x4660b02000074407400820464503242d01e81000c407540d812102d4540c000d4425800186608202002600d1203841c01d03210204442c1d440f18601c62140b10090202900039032026800f100581d03083c009450300900c80d5903600881c2c03a10782040c01c165400384c21500184180d07141e0f401162004040d00c20ba20110a07540f010000420710021001003030841030035000e6002c01b00502c841200c5042c1c4080807a402445028450340c070207200c180e603501c5213180340c00202d449880102509802880c03841c030b4150007403c005061030a01004203114011a0b04000000b44040048240350b4030706401c408404040d00c00c0c9800790908044018041c2c0202a00003070500200c400044c045607900110800035160180c0400d0600342d4642c090b0700749030000e0b20101c45240c1c0c48042040014504415244101401800001e8224050703085c408540e01c2524241c6c0c0003a0200000f00109200740140344c02000c44454044d03407500381e810010101c400c000022450002103420380c10110300444141c80c054503820644090011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 166059694 1250 166058444 166058447
    0x14071403120f1b0610080127030c02030d030204060305100f1a130f0501020606091b072a170712082508090f091b130812070c0b07030804080a 62
    0x182c540300c2040000b89141d002c1c20150040b42503030103958210017042a06448607001c82c203996007c3c0720075040c0280001c029401e44175200040c1103103402401d20110044868000c00d00f00f1100d41ca070031022a4001400700865a850f10640d94455060340068015a00b07140b021003030705141c0d200702c4885542868030039490030030020469100484070b40c0500303007140d921021240000300c5071080f28058014040095003034144000d25a1190544200c55200e00003590580340254015150641e1042074141442c0102d41d050781e01c4050002482c000400014907000d13031144c4e500c091800e00700c40d03600035900801064490704900125160f00500c2591210046030304418054a615061089003580903d90414414000024102c1010a84001c02c02540060a00c00d2800d819245d84071851141c0810b00c092695940c0680800018200d140c5041665207a10720716240420038451890311002580004000c1a05110001007980d8403903070342480750703686014060f6940288042d000010004d0a0407106 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 166060944 1250 166059694 166059697
    0xf0d151d0f070905010b0c06060108181006151d0d154d0a0207150e03070e060f01030f0b0d0b010905070306050607030e150714071403120f 61
    0x2031524821620000d640c1c1007000e948284078030507515458500000455403020200c1241c007102c0c03080c002042151074550045802d10001040c03120792048405404a030082c0a000549040c410075401042041c04d010707000d80706200406402d0240045e0428070844807000c2d440d01e00912104842d600c01102c200e0070320010a507040c0c80710100661610281c000103250000124418240d00d014004c18031000c1d0350f080900c001c403440351034026004500414800072400707008150401d00b600c1a180107603568a5113584035079003030049901091416200c0c000d54203042007a20001d00100c1410071490800c1000f10308002c10385e0402c00e04146e2100e01b030070320710300480e040300842c41405050031601d16881e0034212080802801100c000e40d0030b240218007a54803a0203400c09961000384000d240580658080e10000d021072613030b41d003049541042c995a6104c4101910302c0c1801602d10000400c030060300c4c14180449908082600e00380280b1114098500190034030400540086040daa094461001e02c0305 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 166062194 1250 166060944 166060991
    0xe040c210213050f18100213050a0f060f0507030e330a0e03010203061513080304090b1003200c0c0406240f0c02040908091801050f0d15 60
    0x1203080100700c40000050ba00040c42000c904c1000c1000e9203032944441011801c581080001e58440030404160410680c003d04285015100b2110815903d9001c9800042a40c1c0002100300e603034003040124982000d4100083d607100d00d0700f00d103806016a005851050305601c030724050780380c1940310841820314900001d00784110030140c0030110858007a16440c1d90000d803945000520400e5116030904050003946d001d030b10010460720442c01c1c0700c03080300019084542a0060f01a45003000240304500313100074000740c0f541d62404640602e1010034040408a40c2060400301442c01840d602201c1c081921207544141c0743c10a81d5a5280d84c003103041c5005141d19050307500a2415000250070003004202442c85410052010400b008001050718281d40c206540c40115004c9441040189403da1000351003e22030396007d07003494401c0000c2614000c0c0304034401c0ca03280c41400140440e140c140c9030b218011800700c50250b540142070351040c1184041030440d10310161184410444106880d160781d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 166063444 1250 166062194 166062199
    0x161508100320130b011b1e031b030503010905010b090d08030621060603070b030f01090b0105040e0a0504060e070317180d0c0959030309070e040c2102 66
    0x3d02d0803183e4120700c001d041518203d804140c01c0d0b80300f03070003a007030900c02c2000d4560480b101902e46c41740c07a0046812102448030490800c1442c80d0250b070050021500090518040e81d90303551650f042410320001c5440c10780019a50400c1481064807540d914101707441a9640406e95544903120b050200d030300b14051070b0340d4103503003400c0d5a000403a841c2c00086541c8036004c1141111f040315601e180754030345840140c0d200b0300a2074030303500107209800154110083c1070f80d0602d0f081d450304d03554036098100804e00b95030341d41c1440c1e240d10a102c144686c41c09001c12070420700c0090510380f4950783d03520010a0061882c11f00f401c001107a00410b0304a034150f040c4a40002810881a11503280b420110311001d900030004031038035140040304903810807030015401c1c004c110301c4526034a0b104050500f40380b0383d0074400c0300040042000510ba020135400e43d0061494181d000b55200d04240c4d07111420090103800c044002c102440c100004a81007030441c01c1210b84400c0d1006410b10a101003400103503c0c003402a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 166064694 1250 166063444 166063459
    0x2010f180e0a050708070f0c05120f0a030c1812021206090f21091e060c010603051002090603010e07030905030310030501050f0402010206012303161508100320 70
    0x3415070807101c0700d0b8400d640000c010803d9507030340f480a84001a0036a0118009607608070000c160310701602a111400d4041c600f02d034194400c150000025501080d16001c48220104075098103540500a000c2c0c0c4c150141800030250745040180030212055100305a000c002200c440402c0d500c03120302081d080f1000e00e0555100b07107003a8005a40c0d40c500030380c2152403807260030395455110089604503148200324851252600380c8120800100700281d26400b0701c3c1d00f6101c400051a44e40790301c000c08e9020030b03480000c14034515505041d81080440c10884401e60700400041009a07214003c490540707044030003030144c80c0c0b1003100441c0100f250300c03001400c9110010030700c010041e0340d0340c2d000c0480b0700c1240244900d03658940d60311310031041580c0090141e030001c0018880d8a008200c402010041d000d00c2e622081a8400003e1038122628a008420381c0c00280c00e20582c2044003110b00d042005041200351420020f6a6400180440c480600322030b01881107541c04920480c003424000703130f0003002c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 166065944 1250 166064694 166064699
    0x60306051003140c06191206030b1006031109041107060228030b0d02120c030604080c0c01050f04120201030f050f0105242205150909010b09030a02010f18 68
    0xc0c0059020340000e0740c0c000d83c4291520341c40b050000d043c2000345805015542014004c0c103800c40f00c90444000d00040c40b0921400381c2c1e42450740d00c074070402140103443c04c0e40c8034107041880002c40311a6410503403c25080c60321070400c5104d6003007100c01c0700c04180d800058070f50101d036200289000ea940020b010b035000180554407100204c0c554441d90240f03590702c84d10707000480c0094084071156940242c00120415482015140402d1145440d107600c20036121446500c0000909001d001c8404566280300400e0012a481007080654800102800e0091810790303841307801e0f0080d0241e807050601e241000c1c2d000c6011a44690010704015010441c10300407424640c09640d41c2041c2400741d1070003007a8030003603012509462031000b49003910b20728601740b0b4201b80054803c2c841c0501d104142d911490b0200c0041c140d1940100000c205540403166515807141d1410403120a6040c0c0c03001551310301c144818903c5a402242d1071940c41c2c0e09003446100740c0b846400640702100926180940c140402400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 166067194 1250 166065944 166065961
    0x70b04060c0c0e06010e0411090310020d05060a050d0f050c060a030b01020c0604061b140f03070c0e04080a03020a020f0f03180d0507032603010f06021e1b010306030605 74
    0x1081e6400c2c4a0419082d0341c0307884004408080100311034150004101005100c0391b41440d912980004100c05400d82c47d00d06e014000c2454060390000e00d0b190b0540c00180c0e4020b0907240c0c4512034000000301e4072811198a080c000070f4040601200c0074007441105180c03201041170030000e0300b802d550040c19242d1503000d0010045c0051042101c0d50b030160048803460202d915142088070251813403501d4003a080800e204410300c41140c00d00045800c0c540c4640381d032091840070010952080f881800031070391184146083c034549600341e80a1540046840300703002c00203400380309541003c0918500181ca8050340e0a040b850041004601d040d64004d01d811a0040c810100050114880310300b54200441078030010700c8120400d00401030070540210000380300083c1d449440032100210001c04941d150083d6100c00f0540d4020317803100d80080d00b181c030200041501030124800318503035507510101d00302030080c1d04c58407803014101070014811100304024840e806035202001851300a9810416807829540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 166068444 1250 166067194 166067207
    0x12030717010f090e061605090301060f03060504260a030b030a0c0906080c03060103080403020907260103030f1704060c0c0803090d02070510090e040f12030903030c030b010c0f0302070b0406 83
    0x50031480ca414005011303c1d800000950b98000c6171414007041ca91404443c0480f07003a0820212241d25548078140011031103124442600594000c010000e0141080c1c9049a0001040c81180110007003e40d01d401e200003c10382500c403000028103011030000a40c0d0002070501841e4000140035031080c1502141d181c1c0c0c03a6010384161808041101e005034010003c06540f05c1c030910004184035020030084c401818000c00700d6400141900b49401e00c1000c94440036806890601501b807a42c1500004000340760340b00c1d440219951150500e9100e0066204040b101d01200900c007034440c2e40c0300d40540403418440e03a4a80032003600000059164107101130034580311080800d550005209004000c1407601e004410007120894035102d0780c03503440c0b6140c0081c141850041041e101100d160680310049480c24009250a401d25640001c0c03140c03147c40c0c0a400c880d03040300d1890405141280d20051a6000880c5184141c2c20240030041c21491307140491809900b50021100d590703010600107a030542003030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 166069694 1250 166068444 166068449
    0x230040203010c02121e040806040f1a01060813050c030a03090503060105060a0f0809010f02190f090b1b16173319060b0a0e0d020312030717010f 64
    0x300280043c0b016004100ea4469078035506840c5110700b08a0050249103040071419003162032030015082541e030b021741e281404021a02910503187d040c1e00d100c100107586400c407140368420b112818284d410b0901c0100301450003020a2200c004c200409410711108001001c500c500c02070031200c000c042464010010601c610440e8000c1c0308200010a441c0382450036526100708565680c9140d440800040311052009482040d20303541c2c800e50350402c2c084900040040981c6000a8003c4228070003004020b03203412003041e800c000400c001400011b641204036010201a17020581100700d4034842c1c80d0510320304000f40b200d1540c6a4400052224881414060300d060041c19609580c4203e0100700c00d5a00300105032100030161074410003d400f170055010381040c0e005409000051000741007008890b40d42d04030845110011420740102c6511031601c03101801c1c10741c3c1050303c042031503010907030b5503c0c0044a545000c07170100028107101d03c91840c8003a031540c082c5d40c03600e495039500090244a1401e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 166070944 1250 166069694 166069699
    0xc03031809160f08040c051008010312111b130212060102070b0a020a030c1b0b04090f090b0c0306060720090f040507030201050c0a060e030d0e07080c0402300402 71
    0x400000308501252440c032031603451207494051400301400b0781290200313801030044919900c401404981a22512141c800480352900e52a51550440c20000303000042c10040310f0030044921104c03012010040f4081c0300c180c0600300d90380d80005000c000611070300c01890416172203610100d11f0750b220700c10044685001307810a070280c416040d15050b508030b40344114014a070242c1d0001007040300007882031440e600054080c039200d5a1394954011518410710496100710110100420144004400d512907407648040c4820208540702441c2d48500304c1060040a60101c003d011002913104e4584008032581070b0751040c4001d40c07480d441c036800389000c3c0c9035005560107003084000150888c400a101c540c002ea03001703001400d10b1403440d8011121680300700c0c1039001e5070081c50f2410002030101e0240707019512500340595101c0d0201605072003110303404880e21030b85604c0f8100422407500089082120964246c4006d6a1000f42e080c80081c0c800c07d0aa06402d10708002e4107a118076602c80c09414003c0b0f01c01c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 166072194 1250 166070944 166070959
    0xb0a110a0f060b01140f0a0e0d030908010b0a080a11010201020906040f06030c05030603100b03010b1c050f010c08071d10020123060604211b0e0f07090b0702030c030318 74
    0x604011503032070101415040340c80c01c0c1003007900b680a00700d40c0900800400b0785806403602c544103021440e0741052507020ac01042400100303102c840c1003030180542505060303031351452440c5802081d542d05d44001d6800b41403007050207124078090340300303404507691b8201c054041ca6545583d40441006200b031071140d200003a10340b00c1c981c03260074402e108890040d403005004208411110307a6660090101c0c2c072020b1761640d62482802959250652003480c00b030b06141d1000a04034050520a003800481403200c4496490040d5040036903400040580d001801840c00321203058411103880001c01d40901103c1c0d114020301c0240c91040c0d030540215050142c60601244a608030a081c41b4424400340d402d1075000d01c06000c18002d640403a400a8001c1065180c40d900c0b000c02c5807100802c0c09001c0b0b801c00c40d41164035805126045201d4480c41e0000e516152006030f51a1925008062000c64054010030080c00039110003550350810280054100040c20390740d45121000e42d0803056039100f41c1440c0111203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 166073444 1250 166072194 166072211
    0x503011707031208060a030b0c120105030f0319110a080405100e010206061c0c0603090209070503060a050105161401150801180f17040914011e0b0a110a0f06 69
    0x101107144070032264440140c483c04011140c05440204e001000356030000e00c1c01c440040815030b80c400c0c1c5400b48800502269550181c220781c000f07807040503000b9501aa100141460f6044400412111201409502c034168017054140031107442080c81c912001c907109400500060141d10070007402111000c850507501041001d2003524003215041c107983c090303088000054003d0900020641131301c10300c0410003c000c68030341d8940048441d283c001c0800660b070707100d4040c114201040040d800c0009401c140d411480c0c0f00c40056074a1900d0b006560400001048401da1521642c1c807030390f000d9030700c503101541c40407242c4c04c41c070300805c4d600c15000d054008125000170100810b03c2541040803405d60080788185d07545c0c850034004280054106c0e1900e140003282444000307440302030405840804804030f0b000c00074a0340072000074410f03000381ea5204d109102c5a0450456119140c0450780621070041d00c1d2100c9642c25140e44c0d0081008201c00d008000c1d03070408100c80756207540341080c82060304220b03100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 166074694 1250 166073444 166073489
    0x50a031b180c0f020c210f03120105010905150a030c050c1005040b06010c080904050c0c0307060b01031a030604060b06090a0f080f0c0105042115020706050f1603020304020a03050706050301 83
    0x1c5109042a00040e101d41c84c034083da050510600341030003c01c001c40d4005108810f030180385a018038178009844030b0300801881038cda406a402402020f00315000c2d100d4010010b10741c0a2031140004040500d5560a4589242c501074816107a00450302c8090b298810101301034000501800c0340c1c1181e0100481d0009541503005030007032500c940d041401c1d50304106449042c04000d00001d001e0907a0030400740051803090504000030400d0501ca402d001c5141d102c014000342c15134640070070b00c180c1d100003240750030840d4500042c07417075002d03030811000b03d03000d102c0e44042151446400d100e03a800450350078011a502c54285c290304125010101103401119000c400356451307190a488140c00070304200803c02142d104680f80800001d0160780740100125580d680c0c0205424075444c040343d143c2c003ca940f009100f401d11449a00022014400c1a149054201154046c089200304801d069022006c1000e544130003003a07401540d4401c088030501600c2c0c1d503025210390000d1050041400305107803801e0611 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 166075944 1250 166074694 166074703
    0x3040b0306010c020d050f0d0810090504020d060606020d0e0102070617040303140705070201120c140c0708013902060a02071a07021612030503060d060b031015050307050a031b180c0f02 81
    0x41c0c80300e82b0700c606c0c0a0700301800c0390040c1c400a40141da001112800304000305486100303500c001c0c0080d8005120750b501d0341030041d0403105020113040c15500300382c1c0c0801600343c0007800156440900390704070725542d0b00c0c1d24058001302038440040124031444810001c10a03000b8005095450007600d9104001440b40c500c20300781c8458103607190000d181d0000301d0f0b010101d9040a403051501e803000783c0c0e64860b2104462421102c82c201e410410302d0060050300254034098003084207421640c038400c410b00340710510207580c0b003001910704460140d0000340d0b0020302a07100703c0d0410204001000036524185510000c1d500d00c1010b00768048807402c0000080d1030018192140c4045906881d59411650b03408100079480340c01c0d481c1504d0b625215540841c0d20b03a41402880c0080000074000240f00130042c1c2d4807e01898141c1005020741d001c607101380003d90f1a120054216540300594411482c600c007000d41c002102030f445000e40e80c15403d5440e401110f15000030054904507500e00c000741e07002d403204030f0f5035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 166077194 1250 166075944 166075951
    0x10020403080a080603150403020c01080f0423010605150301050a050a0e0402012609300315190b030402030c0402030708060d321c0203040b0306010c020d050f0d08 71
    0x400c608001074070b492405010b1856001900400f55010100d91b0010000c0840d002c5508800503000014000d40079a044440d01d9082068840720310640d10303240d070b09d550083d429600d07400d4207141c0396045c1803a0f408007504054083c000c00742101042c10626500404560001e001d4544103684030f2002050782d040c010680030807a02c2e0000340d801e5548507a0015200c2d07100400385c24200d120000c10140c00382400e996128002c0e005400182040603000384051106882a055103201c0f240101e880d05450260304c0549070032828941200c041441ca600003d400441c00210094406420314800241d074510705000d184218025020303500f51a45684c01c01c4200c0c481251300300c0214600b40d0226035981005405461003c4c4600ea00100e40500700c8230300240f1000d203402c6a03184004000d001c00580c034091003d02c1c1d00d0307842c60950509a1544001c00b944901440c020000c90f4000440024400ea01c5940c08948058014108144142b661309000c0e480f412100340038011032140324020700d40b0600c2007403070a01c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 166078444 1250 166077194 166077203
    0x30309030312151c110406050a060c0b060405090a03052a070801060b090a06120902150a09080f0c01050307170403050714060402090a0b03030904020c01061703040b07151d010b010210020403 83
    0x130442500c0d507400402d2034124035a10b4201d42d60b00008070740b5484600314140a0482a11292880f0415141030f0082c0710009009500880c20082400302c03c510001e00300001ca613240c1003458032840c0c40c120450483c640c1d00d90403502d880760400d95028007100892113001f650100310081c40b40c561124101d2296205090205030084d142e00c02c108000b0384103c00e081b0012010b0304002c40c1807049600050320b00e106410010810040001c0c074900400d4115410780003d1021394003900505030280001a00c45010f0841076041c03050000005480e00d1090356206503d100c1415a5420340c241070400901642200c0411a01c118001c3d40390310050a0015210b4822903005086641c2030766094002c0e400f420b4140c4001d0380600c424001d04416031340718009008075000e40382c00040c9152401080d5206401c64880001071900b04210034000e030466001121020707500007400c00000207044400380010498580d03c0841070340c89003d50001401c1c1034201c181d8808099085881c4481e00c204613400b280b146110041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 166079694 1250 166078444 166078489
    0x11706070216180f0f0218090618071205070f030c0e0306161403011e05010503090a0f0f02131406040204050a050f030703151b0c020102060a0b03030903031215 70
    0x400c1c101e00c60310080902e40c4080300032600e0000040000c00742c4281c81420211701e50007159001c400c80c60030000c1c48012104441c50f40c12824604042405481c000c02400c202d0545900020385e5a801600c0b90380521a01050403c914505040d0081c01c402c032814845001a0a0030328800c5058030030729010b141900300a000e800d03540c41312007070384030444802c0340340d80107118010b0100000703408804040c600030404840c1801004038000901000b405a0390805814050300b40144a44154000340c040c076032690200c0c04d047e40307580d0340c280500e0355410003d000358004608000c1080702038640e040202042c00303603000820b031713a1200300800050703001d14010503030081000001007201c0e251107011080100e42c040c081d5151661a81c031040500740c42e005200c515651a188508070007201e02048851020017490281618002540000e4950070040d00303820700ea40d12584001243d5400b402101c0b880c5800070101d03592001d41c04054600c142040744c0150803013030003121041d1103007400b80c071300c00c02c078021004500c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 166080944 1250 166079694 166079699
    0x5070806010c0c1805060a060c050307030315030b0112020f040605010c0305070c0e0403020d020706050a170907080105070207080705090408120c0c0a030305090d2a06090506011706070216 82
    0x445200c140c1c82000c0d03e85141640740040d01080e2407000010b55184200007240c2c0340b4018042c40070b559155072110b42081144081c0704081000071069912940c0c0c14235000c542d441c28542410420390440c0c20143ca43c521450002a40e00014102c42200500c05d544c4091a500300d441044210303500c0d4801c07240418141007400001900c03840007041220b20410036004c1e00c648641c21039810344000c590403005603003c1011900d640d03804120501c0200545d2800c20310704416080c00400310f002c00303c09400300560707860118040200a2202d007000d0a4904001c00c400d20307000030001d645041034401c240300d40c0102d00c4c0104050030150605413040741c10080003031419100307045204e00c441005041941c1d6000a005591000b081488000c000c1800b9540120f40703414032038443e500f05056045044144011601c8402c558007480421180301445881300e600c8144050508402074107800070020514016a000810f1035206998176000715040b090484201d0b40d54140c0a995600801807180742d19540318004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 166082194 1250 166080944 166080947
    0x190509010c09060309021309030c150e07030320100213060e28031a0f01240806011202030a0c02120c101104050301020c0714030703031209020409080c0105060906040507080601 77
    0x9002c05c181b010f800c003503054060031100c40031a0314594040700061244040c0c04103010603890b084030341c180c8480b0100031100b00b80003080e0b40c9102d54800102400300e24114054800d010340c0c8094280011081603409074801000c04400030f501104aaa8048020540c04258144514a4a5468903024215440760081c003a03249a10506110348840c00c5814994040002000380b40201e0140440c0192403d060906071403400e101c1105803c10010320108801c1c40e07079442c5070302010b00c115000c1410a9102d684807400101c510303103210a0484401e90001050044100c02c80d840400410202c2d400d484601c0380842c0404514812580d041c1890340c00800c000480303151a900c02181580071200540c6800c0d5548082426070f00408030f03446007070300560801c00005c1c0008030488501c40d000c8000d0418981140c2e409420150079048010b030f42541c4030300c101c0854465074418940a50850010b58031030004840c414040c00e400c0350024056503190001c10741c1420304d401018040d06194850901c1507450400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 166083444 1250 166082194 166082201
    0xe040206030603010e1f0c0c050c010c03031104031103010615090e2221020304081005090a1b03062a08070c08210108030307050a0c030504050405190509010c090603 72
    0x10143e8107550b00c11076100d02220411000d65201c5042c00c10707a0142c40c545003031508581307090b40400244101d8405010004901203000350440c5024200f402c42c0704024103040300100301094044092101c0014040148a240404568039901c110002d02c0762680700d00500190000c000440700200b4200b00d42403100311410061660f109074011203c00344c900d1f42070285c0d80281d5001400356242280c024011280d201c06890441d81480310b800214070305880c011440c0d43e40c01110100541841e521710104420a500340f001c1c280f50360b0048940000000b40004924100140e488101c800c0c911304117044007100010000c00c980354800a070049200309103803e042c3d54040000b405081040b06e81c0072180000b64181001e02221669509004680d1700c50224002442106801020301039105008100060341c0c0312040b01c840001c00d141c0781600e00031518082c0e8032801030f600031590080c1000c00b0813841c802c88040349840c90b0900c281c04c0c05587c842010745800ca50414080f10002204002c0034030410340a40c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 166084694 1250 166083444 166083451
    0x1005040e162d0b09031005010e06060a0e0d0c080d0f0504140120101107020604050f0a030f120e040b1003050c0c070905010303020c0901120f0206121312090e04020603 73
    0x8111070742c4a842000e60b040e60302d190380c0101d41590b4001c2602c1900f400d00b00071400c15180700c01410001941002d01e140040c031002886184594030018645401f50700c6803610855400000d400440409a0ba2900400c003081c18014624540318007068034144a00c9002c00c41c13103504640e214281740c94242a1550012003840d000641400314092120041c1e00c1a0105081c0d00c5214902900c1850341d214090f0091351210981401c1e05682440310301d01590381c44084900301c03641250045048401d150208500c40c0003640003800b00da1188840800344145132001c00d840c041070f40c0d16001011180303802c00023110200ca140c1a0819084444114218000e52107281c200080d40c121034200b10100c0341031441c00c0c11942082c02019200c3e03004000701030301003080d03d24507682110710ba6020f48c18095120b14900e140e0002900011110008809545915081316645200d40c2c0910005140864070680b08507480c000482cbc2e62a21800107007041880303081d1420680d140c2880039500ca4031150200101c5070000f8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 166085944 1250 166084694 166084739
    0x60905060706060b0d0e060105030c0a0e0a090209090303070f08010308190509060a03060e072a0809060423030615040f0f060e040c090b010f0c14061005040e16 70
    0xc0300045145104c2c14050003196143c00d0000c2100c001c3d00072020308021040e03100314001d9007c40d1144030380d40d450b03ca107281503031124000313a14941d4424030030038040d2404040194200307401900307201e00408040001d40c461406a1100c14842c514140101c0c2d086c6024400505504014480240071142ea404001080b10305494818285180e1030005070080d0321a460450100765034031780030018107a03c001e01c4d0754000090304041d0000c40600c070341a404000e038030000f0156009545400c0c000c00c803412080c1c40100c54050003082c2c0300d0741c03070304106400e0220303600f0350708401c41c96100e80624524001401a12508400590100d0300f0071000c140000343c0100e106a07016161a64003000701b600c803030310800c401000460440449030400341400480d040464100e00e0a0300d00b04080c0512598200c680042d0400c8540b50203110010a41000480b14003407044440540c0250070900c0400b07040c040b841c0054940c115020003980c140c0300c1ca00d5030380304181038801ca035180c081c650030403000003e021010003e4221 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 166087194 1250 166085944 166085951
    0x904030309080406021b0904051908070609080405042415110d08061306050a140f030f0d020f0c090c130b0a050703090b120c03220602030718060905060706 68
    0x72070340c85000c15000743c2c20040c01a40900c0341092011845014114070a105131210801e0341020f8554540300c0c802d02d41440500003800d003004003040900c6040f5452903030400d4080141d01034500d402c94541d0f100c0e100311440b5a06140c044049800c84043d200303900d0302c89001d902d403580c0c6406044080c80400c1c10068050180540859194200500041c502c100b06c65480c60242c3c80c15008110444040d04104100d1506d024014041380c0c0b903004080e010303140c603a000800d1241c3c1220001d0b030240c0b42c02c038040e5014041c8010768071021400045500381d000603174095500140d443d0030700540d651129840258000305041c08116072070314000c01010100b00c44840010041d440e0f07100034266510a00526001401c00644031044c1a44884080058143d06566614042c0b120404105450f409000600301c1040003003c2a5441d10010041d8000903000c400c00118500c00e08100c0029042228004007007091600c0205810a00401c1c50b019552541c50303407244181405c040c010940c10a11049600543c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 166088444 1250 166087194 166087211
    0x10f0c06050a021b0102040501030507080702060103082a011401120f080a050c0a030207050f010507120311090d0308041a0c0307030207020319120909021602040e0709020f21010302010c0209040303 86
    0x81480f0540351303009550000d40c2d91443c110004086910040143c02040b23841424441c0a507030101d090743c11a0b4015a186858002d50354210169070018820a03200c207030010103400d012141900001c40c1e0000012207200282c0c0d071362000100300980d000d0000d000541c0c010000c030000f8580300c09046001810325100c2c0c01c02c02d5002101d454400f80b03110039070250744140003c21540c40c069040506410303084c6081402c051807643c491440d00414100c00003419101c81010860140c8e010954540c86d4001b00208038031202400c0c00740c0680000c2c0c4007920000e80c0c80b181c402d441503040d004140141d0306907188600d50707900e990086001750480d42c0201c1e40f6000d210b91134403c0a04503410140c007140a41c40040303c80a08050113024560107512501d607490052143e6070107003401881d50005e0a406a42c00724128480c22805414410207801c091282c07480403c107100903580d01c50107041c2c440310586010700041080340e520686181c0910000b40010000c0303c03642c006086c0400c0060300305d44242004914000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 166089694 1250 166088444 166088467
    0x8090a0204051f0603110412110604170601080c060319060b0315030c0103090506070e012717073b040605100608040c0302040203090f0723010f0c06050a02 68
    0x61055464191403c0c41030100191410302c415001c00804080c01c0410540100098542c160300445c4202d1160f40c001f81c0d03480051002d040048124003c0080a1560f01c0d40c0b50004140001404007494501b88120400440d40303450010340d400003081d008000382d056035521590310754405609001e4248031600c621001803400c042d0000b4502a01d40d00e070320040c144400300309040c90040940821410541011a81d1002c5003000c0f41d020340004491400d4806201e03440e005954100845800c2c0c03007401d030b40070740e605c0c5100503409071310040d03030420200b0301d2401c1c41e0340000e1950380040d4014054140145800c40c40c940c6e5020b076041c0501d100e81500340503005600c0c2c0c402d9059200c215005d035222510b0304100b02d83c800984902d82c014002c01d04003c001410b007500c40c4010b403800c50100034052540000494542681008155180400c08003200d0f001c5841c2c06541003181800d04c0c0302015811032252880c03503503009842c10401d0003416a00e1404640f01a11030002800010301000d014507801c01c880c800b80d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 166090944 1250 166089694 166089701
    0x3090a0c080106050112140c0c0c09041a0c04150c02120a030e09100602030318070806010315050106050a08042d060b190302061204030e0612070908010c0e0108090a0204 74
    0x1080d0081c00007890710f28140014010340c000d07554083e0160314040b50340c00040f80c440c4102e0703048044071000c10b885030300f1581c18518014440c0c2c0da040c5e0100c803500c100003c01458181390300c841809500d0000c2152a803100ba0381050181c3d0244420b810348400c1c82e28241403103006580181d0b40000d009080305202e500d45541840151241500042d90180e50061142001201d1981100506095081c03040c070b0454020740b02d010283c00d06080c4039200d90400702d10001000500054200441582e401c0d594074a070480326550000c07109421607003030400000b0300a0083c011b0f20303900b130815102c2030790341d80e541d0355400340144140b400300c507041109040d440b59221008000d82c028a100c6c10300020728100f0a001c10022280b03085a2144200002d502800140c0340d00d0300b0340d54003c014441d40c8036a51564030701901d020f825418043e8000d40007003041c182807000240e11174080c42040c2c503241c4490740c88070f03212400c0e2040506901c020a0300c114148505500c42c3e41101d60014400094428895213540010142c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 166092194 1250 166090944 166090949
    0x90f0604032703060c08060907110a0b18010606090303030e0c0a03081b010c0507061413020d300e030d020c011d090703060302100f08010e06041d060a0e0c03030f03090a0c 75
    0x84106d020890582030400c0003c0e040785c0181001088a0b40003625140c0c2c0c1c8000071001000d00c0010300114003a000040f4611f01c407071410f0360090000c03a45500f0002d0080c02d0310f11043d80000d0070584100814900801c00d002c140748003510b44c580071411516503829a40c00603030844183d81c0c0c0800c0c0507004c00310078070408100001da0b5440d940d80d41c0c458104282900d280a1030441c08040719010700910030991a100485a40d042e0350041305441c56080c16408040d2240603480074448507810000c40042c042d01c4901c20004545407032545600001c1816030710450386001d000560300c100742d0a82658086c0308020010221030725458a0411046d0200e03440080030340350500400e450301c0d02801180f4010480e243c400140c0d140480c2c605440c1c1030010110302043c81003c0d01c2c03c40c54400714181b1349480d0080203e007108400b0341c450844142c140f6070345e00c13001242c680c03101c1031410300004049500030410800c25240240150b062020503400322141d40c1c0302130000c3c20603109260f0500c0001f17000c070008100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 166093444 1250 166092194 166092197
    0xc030403200d112a12010f1e0c020c010e030a061506090602030c0a030c0f0209180c0105070807060b0103140c0a0806010905011205060616050105090f0604032703060c 73
    0x2414031030450058011100f5500400d007070b811404803c2c5000c2c00b443ca4800d101070356402c090f2288105840401c0c2d0404d070b08031a8003080d500708101091010b400382c10003134001e20300b038855a407042054264201180c40110042c40160088941025250310450301c5d9441000d0040903110b102000355501000c494026001c2e1003c45030450f000c00c0b00e15041152040200341a0001d1841d1000d40a18903466100350a0003c09110100225105004000c142160030950203031200780d03141095400c000e601e070600821901c2501ca54492030001e940705101b0389061503444540c0500700001c641c0c502d4060001103090307904140c2e41c0d6003807103a0b41804500c0035008003d044205581e40c002c242e4000c200380801856541801146c0a0801c11642e1080ad621020400024000307655161303000024258800da600c00e2844100300d0300504284403065102070300038031811041b034101e8002c0790007803a1103100071140580400c0072400700b509441070b100b1404038242944201c900359a0303100d5550303800f11051f5601490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 166094694 1250 166093444 166093453
    0x9011d1e041b030b090a02040f03081c0f150906060c0807050145110103050a060503060705040509090105010b0306090709091109090618011a04050312030907060905090c03040320 78
    0x2d01030801170002038110a00a50035440c0505148016900b5405444001c0090000141451080040c07ca154450f41c50400003800742ca41e00d0440304020341091104d80c003103056111000503507903500d4401c8c07004490198803014134000c680e03110002150440b54040d00d0075500d840c3d00242d000154001e03c0a50070302e40d01d00d54007036490400680085c0001171840103494000d40000310104007a91060320600d107003484c000c5030560b82c0d40400800b6261640c40345402d441144280882e03160404064002c1d03400503200e5072003e40da071040c3c00c3d00340c440078425642000c0042003c110b403410401d40c51a4001051b09120900c01d580f400d98408990300c49039200b03100840410803010600c5e103004000d800040c03c503101072000c14410074038100241d040c4540c180d60030f0121201e80d003d5001710282c0f002020f005042d00c10444000005048540c01141c5003811406a00c43c04120640034019102c16100054170200742da0340c0744403000c40141d00c081c00550a01140c503805104600c041da405144140740702d001350 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 166095944 1250 166094694 166094711
    0x1b0f1e021f050603030313020103090f0803011502060c07030c0c081609110a020c10030b030f07030624050d080d090f0302060a0207051005070e030a0809011d1e041b03 73
    0x80019106a40300001c4250614050112590740082500d1300400c100c21158030048480c40142c005021003400141300f0016000d02c1e070107009a0717001941c100c90702c10b03111008412601c201280c80e020200d811440b510f00922540001c00d1007004600e00051040010307040d40d54441210519050035189040300202c451401032121240354007801c4a15a03103030850505280340c42e000a51111401c0320014062030b41036207181900c9100f500020b000c0391018090760300030030b81550b4964890442d400b0980710700313040c2003c102c401d0210b1900b162002c004a5400e045050a120802201c149400f0066611041c248142296091241300b00e08655105d6903841c100340e0110303d006424000001c081c0700f805441849440f0126501040d5445110311040700000d82c0d542c0e000d419106104416860340e094440c2c50504020004840002d0452030000d07200d204000070740080e242cbc106c94406c1905900500741c4405d10035100c003030003140e042c0004020004030708260260443d200d42124040210000380e03c62211 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 166097194 1250 166095944 166095973
    0xd150f0602070b0702220b120c0901050d0b1620150106030204180209040207050d05070c050d0818040603120c0c090504050319030e010609060302030c03011b0f1e02 72
    0x2d00050074081029403c203a61500040c0c803280c1031011400403642c440d0805104449903900101603218000c041c00070403aa0400410b58071021016003034014110b020001c1024641481052079856001102c1e01d070686d5418260240d05208024550034030001c0c401040c00060091000741d903820801c00203055100700441c0360101c090069020f5414144100020b000101c0f01c1103a441d00d048680801598615814010038024032030070038003074201d0098129aa003a0359020000b480998000e0503d500b010340c54104001205625000c018020780c0d02304000a402019085c034040c1454000388002001c983c1c0f6218150840c00642c0244005152511070104002c03801520601411806000b04003070b18107555411741d64402c80c501d06111030a00019031144510030340110024422910080c01032a03602d0003490040c00542c00100d12a018520060203075040500c940c1c0450807000341d58152098541c038044c0e132080519501c6108006425402c2c3c0c0303041d03404400707e040b01c0d10198000e00c481185a8203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 166098444 1250 166097194 166097203
    0x1509051c150b090703110d0f02030103020a060201111207111005092a04111309050f070e0f010e010e0d0506101e14010e101709010e0703080d150f0602 66
    0x180706451840c0207103a40c6a40c503090f1600381d104041d400c000404900092203030741030780601031120688500b07144000d1000c015a402039170417244262254009039860701c0059098031030305500152003a90900101183c00c4a014246820088900340041c11203103591000c0e08001110114401d0541c440041c44004102040a5540706103820b00080b1100030600203d82c1040130004107034811034032030380e0000b600004e110849241c441c1444901c14115507411f0048040c150481d000b0781140c0d400d500040d21180200181e0015410003080d2102d5400720b40010348a40d810801030034104030301c6200e9184191030f4070f41403031000350280000f080c40d890f043c01d803c050b514160304003440780351655554007803805040034a0010b54020406159040465100407220745036542c7d0174540c890440321324608074917000740c080d9040d01a2030b0b182c0c02d800c0c0c1d00d000b12380b0b0036506010040f0010b54044401003011401000140c170720b501107400b010510a1886c400c5085e8408150000301d0b4400c8803003010040f1540411 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 166099694 1250 166098444 166098473
    0x30c0f19021608031605030f07350714010f0f0e0d050c030a05030a18030804020a0509011a0315041410050d0b07050304151b0905191509051c 62
    0x107007909990781043e102940702d000e100024080040900b01c410100007060090310420300300d11500546801803401d242c0081c0fa11400d50218101d00000400181c0ca813001c483d249120050083c03500d02465503480790342c0c00c200303c0002002e5540e00c0210f62080c10369405010100302040d03101144611040078118200550582c100f4107008040002c8031752002d0100c00ea0302c5041c1e0038206540c482c1c0c1d0f10108800074021809004140410300201c450400d6007040615009a000355141100c281d210401e12490701c0342030180c4160050072036a000e046902c1c0e1001154854902040404100d0139100803c0580b101d645421008540440070071190461002040c5c0040c001110500076000c1c640e111045035001c050140780070014000005802e102110214080d200c8000d80100940c560700d0000c600348a400b031120800250409000041c140340c01c0400303100c0307000340e510218012441c00580c0389060340241060f4040c04411400001c00e9a13802507503242013084c0c0702c154008440704d4a00050100140d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 166100944 1250 166099694 166099723
    0xf020319050c040509190915050a0f050907090c0306051f02060f060d0b070e0904050106050a0603060b0405210d0306030b0708090a0b06130f0b010e150f030c0f1902 72
    0x43c401000140e8030100a1504000c1d00c500002800001c0d50504000c0c0851901c00ba0200700507001580d4400f010740e000902c9600200780030400088811015030a88005031041c2c0c2081e40084018000c403005a84442180741301c905000440c10740d20408035021818031800c415020b00800405100142c0520000d548072900000414880c90510b0015041080040b00508242c11351000560303154040c050024011500414041c00303071416140c84c2d8040c0c00280100c81c0503031034a4400046441c000d006003002d0b03c0b03411030010704240c141428441c230a0b17082c00305481c10418600c421075859605124004441c1a43d0f40c0100e045811424151a007200150042040109400801540d4200444c1070a1010340c000c0c24095542c40d110009a141e0781140c84120b103803450440ea44d24001c500d903014520900f0280c990100b2015400b0410001501d001810036013040100078071041d1007000c0c001160300c480a4884181042880b01000c0443c0c1c10010100b4541d210b030f04451011a501005490809030b0507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 166102194 1250 166100944 166100947
    0x40e07080c12060a090905070603110403020a090509030f040f0602060105151b0f101b0c0b0c03070201020f0301060e15090a0b07020301020403050a1b06030213030f060f020319050c 79
    0x405000d207424071840c9201405203a01c038000c1409644d4039002e500050100d003005001000407401d00076185c1d0303810300c42c0c080440e250521484801c03000c017041c0e41c101c03600204525445072900b80c405010308402051036043e4041002005000a0401c0150001d445140140e4404d0343c141240603141c0081a08040d01c210303141c40d1044942c040c040126a19601884c0b1083c84c1d414804207407034503105076111480482e000343d110004601190b6407007110a081c00c84170b0883d41d2030485038103a0b8070391401e40024286810000006400d400341100440c3c000800d07100040c40c1113090b01c0310b0807082e0001e82050000400210f2080c6461900400507000b120358181c0482c94900480000741da8206c062040d07400701c25003c40d000c1c041d59001c2d81078a00854110040c0c4070607005c1481c0006403012a08080140b080d501000411445d20900c05d455001c0c280c0614119914190740301c8180301ca903c060b0844141d40c0b22000780803096000c0c000355014002488150407035048009200c41620001401aa44600b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 166103444 1250 166102194 166102201
    0x2120d0f1d0103090c05061606060b0a020d14040806011502010b0414060d020d0516080609060103020a05062d090a1202130504020310090308180a03081b0c0a0602040e0708 75
    0x8048060710200d140900700000d204c401803401e901c2ea01c60562000d40d11010100e6216245000d05411080040c807a44c1c080051a44400c0000c45900580111800591000f0204030b055800b41000c5803080f2484003915090541e00c001d010310b8014240c00c2040354405480c4108071558090103049100c40040785c050203400c100000810880400410152040c45080024019511804180c09000b600a401e903001c02904540144601080d40b040c0700c11880f5410010300c4005012503250306070baa00a115000041c41e0504114923138020200000521011030208034006684103841c0308460717454100c80d0f07141c20200f001c10041c14041c1d4001144940b603400f50700010798500040d161015000400040d89071103070b001007490041d035404001c3ca218a451030301c80c18981c0190030305100340b1103018081c031104c0c0c80204c1a034a403400490018042800b0300c010420450468034400a821415600c02d81000815000c2c14640f404643c0c040e15415400902408640d1006031b40307950001d80790514903164113 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 166104694 1250 166103444 166103477
    0x60a021321081803070b070c0e0108060a0507121b020c04150506030c07050f0601090b040608100c0203161124070f0606030b070831150902120d0f 64
    0x700640002010024001880d004990700c100004850a0780502100c01d002e44502c040303134035070307104810950f01d880c2e09500c000b88210102c00e000f4140c1324010046d1803183c13509000840942006800a41800346842c1c070b01c1010400d41c4a02001d40c000d940303045005145400d03010303061080e00c1000e0740c0070341d003840150b07219440748448860881341e00703441e031560766610112480418003e4010003885400f8201a40010903000a41d007416580b502c04100501e1a014081000320b070160310800e50950030103586010034480f02e60003a4080305050041d2454250365a0b80c00c030984802010032a40448544a11802030a01040035064101181c98000220812070a418503901503660000c100b1b100c0030350200c080003015006400216031101100800c0d081001000d44440e40444010300ca42031170744200d020301100c02e20030240e042000080c0701c08210842e201c4840048901504048041e12040e4010040c1c5400d482805041e59040152122040710b40008000078440f0803800c0c10450110300110400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 166105944 1250 166104694 166104749
    0x320030f0a060e1e090f01060312020705031605040b0a030b0a1a03010501050d021201020f16030e040c1409031c0201090b070c08030a09030e031f060506030112020d0c0305060a0213 79
    0x1c0c8009020713840b00d95130001050319001c148a40004154200a0004100701032121042ca040c0340d940c09540c2c00c2500d4000b456518515500c0101c80045940001c02c0203080c81e60109800c1d0a0140504c1e55083d16500d8500a0359010390310701c10700d103a0395205030f200c4150040405003140360440003440305501d4140041c21050403040d0291180303a1409081140e004c0c00d50498100c0390ba440542d54841c41400078001116901840990220b4440d039441d8406203020722030b00c542e900b4039072515548907864207400003840d0403000c0c0454041c820300d04840c220259a40008030300c3d0100e03038000f103031604443c0341800030f0440142c002001d001c5107003078a0000510f4602682c1d0701402c29100010089a60306040343d41c1c500004034180c00d805070b03442c3c5030403616001030f003140121500c10003072001a6a41040c08109d120034407904882000724900c610051410f140080700c058050b840d0f6419490b200d4032058280103050b5080c1650981c0021301c100c12400d042000002442c0001200e03403015a10040322440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 166107194 1250 166105944 166105981
    0xf010c0305041a06030a060c090501080c0c060a15120602041a0c12090105091801050a06020d020a06020a0203091903060f0207030c02040c090f0303050d11090307060320030f0a060e 79
    0x24100f912001842d6510100052480d581e08180140120044c014028040107010f00a01d4005410701d0001405c4d00760000c1102c4c0c411018038000e000f203a0383c90101100038802d0106468085c07504180015006082038498401907005120040c0e56503c5c0c03401805142075140c0301480e0390202406000d1041f070000c502202050b20042004c0c2c1e172400c0100049585108440701d50303521405c6403105c0d82980b20441616816600d003030302c0c0e075001d1945602040c0d9a40711a00a0100181c2c810200c031400140d4030f8000c1d205001840c0101c03030400c0320003000503000600312114000003d020752004c0003888045d01515240010200d004c510b40102900c00070908000480042e0041c0c0e190680c210a0500c100300703180c010440d80c0581e40346251a494010807560200c2c0424102900f403462182140358042c0c12540781c10002001811424900802a40a42070680c0c15072691052074109003030703072113241008511030300209480028a192035004001160219041f142100d01100d0400c18080002003040342c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 166108444 1250 166107194 166107233
    0x21210060309050607030c03020d0606020c090901020328090b0106020303100e04030905090612030a21050705090d05070b030112030f0926030d02130611030f0415020f0f0f010c030504 80
    0x207e858030040c00364040c2c07040085c0c1504282c031700540000c034140d010581032006007040b90504015203541030303c83e00f82d000c1664100f581c8610078000a40b0150460041c1d100d2008440010465240d2a12087c0540900740c2c0428090b070400410800701c81e004080b09006840c0031048003500b07003002e480043c540c028a0050074003540d0407030003040701665104070f60381c0403e10f134004803a070b0b0394240c440080c07080031600d40d110714038032030091b0005500701c2c18085c40e4414441030391940e0400090301c04124001e00d5200c030a03126801341c42d01c04924140d080004502801c48180185d116119a140c01440d00c1881101582004800441445520541d440e00100301c1c1c3c001014400141030020712508500c980301c54400b05034400122440003203182400c0b501210201c2c1c407022921036400a80a40740c0c0f08941094042c0d030700c01c100034041605100745102110708184115117030440383c200e01078500b2404806c1c0c859244e026148507000c80c40240108040105140780c14070150402c1c2c0c1d901a1164210017407000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 166109694 1250 166108444 166108451
    0x20f0703170d020c0a1101030f1a1504080a03050304140f1002180a090614060f030415090803040b0a0e010204030c030b070c0f0b011d16031d0102121006030905060703 73
    0x101d011001d5010b1303507108800442921000e200342d14100c080860600100c6020134180000c1000b00703d5244203210300c80c1c110760a0b00d04c040d188002049001344401a102c0013051041c00003141c8a0f00800c2110b000307910075180e9075502d00f000d04158203440345d9400181c4042d4410a1b5248986070007203911012a03805500140e02e403121902090b045460403819543c00040c804d4000480c11082e07005201112040c005500000c0481030500041d481a803c003134091800030004200058120300300d00f610071030102800540c00c4013075030b03c11409038026542a41d01d40801c006003c0803074428840c0d030382c059400200071454589160303201d02c11505240b001801c0d04206034005039005d4043c0002010342640201c4010302e4000c103180c50100710400380111400c00c50500180000c10803110b99550081c034184140c1c803500300d070f103407000c8000d404c4075458600c64030030500341030080702400d00250040b01c4072100c1e081141e250000d40607100d0340c8594484000c041c101509100030820101c1c0c8144c00000364507011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 166110944 1250 166109694 166109707
    0x616020d0201030e01020a180906150e030c13090b01050909070e09070e010b04030311120d0903090e191b0504150306030503070c0303020d0305010b0f090f0406080a03020f070317 78
    0x1a030042620280d0031404c0c3d400000c010307101b10b0f0b212006900054a107000201703100e4948000b001100d4080c015140602e200c1303840c03030400c640190814010b01d280101200c00d040c0e0b50801090b40421141c58aa02c0a5150a0304500f0000744665880c05400c0c2900c13410301d1898100341269907080644140000c2d02c8900b0302084444a0030710898000d000311348002c0c5015695401c085080c0d40c418802540000c000c0803005e5108080030035020384c1030300850441404c222091550a0080c803c03d2000c6040c44814100000c07001c091071243d91046900c2d060400d0b8404142010a0641e0048602052846210b043c4207030410b80200030799042d82c5a4048001000da80c1020541c014401500041d180740300200e0f000342044100c1c0c00260940388254241c0302e144265500907010f5510038040c0705041c107010f00c803004a180410010707101c0c50100401848590454001260891350160003020040d0800b591403810706404001c0c090318820200024411035145132507070200a4104454086c5410000458 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 166112194 1250 166110944 166110947
    0x60906130c090e030c060c0405010909111303031e0201050402030a03050702030a150c030c0503060a03080a0c0f050a060c080c04050118090c0f0206060a050f0603040f05060f0103030e0616020d0201 86
    0x600c1c01500c408002000014030340f800031956504840e40620907481100300203006180311506541c211380040e100c0441080c1061005009420702240314003d0400034020110300c400410030b05c82c0114001d845840d5100000c810b041c18100a403030065095a0502c2309010040e00d00146d02d880040d01841c3c01034a0300701c41d10000e4104010458050050b030f40905442c5020406580b1114106200d524200b02c2800c4011007582e150108460061740003598820030804220402c0080c40e6130b502e01d1801d001641c44a69800d0105010140103903299070000104d88100f0190f0321a17003c4000c1e541c10680395070328100022500d54410b501646040011854103030f19000301d40c94195001d418016004e00110040708401402181083c40c068018803599010540394105129a0703025250054801d00361203850300c0074090681c0c030103401110344071b42106218012401c01e0000724010150441002040e5156041c020210307210400e80600c69441040380e5400e8040d0910030b4205268140d40c045200c0100703000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 166113444 1250 166112194 166112213
    0x7020f04020310080a0605070e090103021003050a0b0303040303030e0c09130f060906020a0e040c050a0c03030203090703050f0f06061504060e0d1b170f03030718031209051206090613 80
    0x403203161445005c00f00340400030683c0106108110503030300c44031400e000e2010444030400030310010303400103101000c842a05100c2d0300714a91029441e400031818056143c0400d1541d80154070640004c0c1d41c40c2c0800300700940601038208000000c8600c10328a041503815021907254503030340200074151108900e0304021450f002800c00d103810501c03c41d162900e40d0750140c02c1050741405c0314822440c080c1300c8a81e85010300103039400d5142c0e0351f607015036955030750381d06a000750f001401c6100613100d544c4c030010014800f000700012500f00b020150650b9803d401000e407a1810103040144a20002c0b480d0022060070101540c0c112030040c075180010303090801c082581e00381400005004000030109041400354800c002c1800c41d032501404803415403000040d01c1e1103403444224071501d40c00400200c0c1d5500e104281801c50312001089181404e42c1d207035070f880c00110082c5295000702d6400402000b56241c11324006003080c4110015242a1a001c0070164403420003c22208100b106644d0b90b0040c40000007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 166114694 1250 166113444 166113449
    0x51605010609060e18100b0111030301080304030c0e070509040c03020d14010f1d060904020109080105010f0f081906020d0618050f130b1504020c012d0207020f04020310 74
    0x8000c020080d00c034129500640014080d541084103400042010120b0103074a507000014440041d110301031503400c510014107140507100e4108038100c9a2810301407002e00045008100510007107985030300c0c516104150480c0e991001c0f140b899290104a081900401210b0180c00d0844000403400807002054009002c0c00c039809a44a25009040320843e02c0e00e84814103a03182c0040c4c052116603980b20308060502030f034000c034400b8080d031004100282001d940694109105040070031080340c072940800d08441d001d0b400003501d40100c0e1810081c01d680f140e042c0002d40120009460344802030413044099424295008055a41c00651402e0f0f0403055841800508904401c0641c1404551220380c00f501d8180d07010303140003512402050086000186600701c440d401070004002e540c039602c400d83e400c0d041149841e0400d07020080c04000c02001e11407401120072601e8030708002e01c3d924200c1741e1100854110304400c0c0d481004440c2c05642d406c01c03070342c040d9442290301594039681e049000c842e090455 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 166115944 1250 166114694 166114703
    0x14100b0702101b030e01020f0a0c05041805060a06030c062606060412110315010f0e0a110a0c23070504110f0307080117010501050901050909070f060f0305180c010516 73
    0x101040f070403d580300304110040e031000d9084808201d044a5070070b0310b81004600c01070103801c2a140c20061824150002820110765141502c0c00d2441501c642d41031210841300341e07003580c2c0d4945007401006640b55403035002c1c1a0070b1420250300c42c180515001c02c0c1c0c40c20f0b4401c690040e004000036200d5a0b5142c01c460141a104042c1d0301080d916103807584c00c0c202401d12840c840d02071449141075242150880d40c0c121003007103203850405441c01038418404070713006d810800c0e140d8030b644072143c02e01d10440081000b100580e481d5142c140f010f0030685084030303007810001c0742103503a0b428068100000040305020713610101c0300081c4500d10410083c50342d1082008103100d800c070200420a150b9040002d05040362103000f09083d9203e00c0800481c200d48090140d907511480d040c005128a00300126800d80c480240310844850a84071205204508402e900c24000948002c2d0390030800c2d03038103000d45600281c20b422242d0100071620300051710f42c1640c00445040041c0410802c5441890107250a4156000b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 166117194 1250 166115944 166115987
    0xe0c060d06030b010e0402010905090c0f0708091f020c01110c030a0804050307080705150a0e18070216083c010203070e0105031b0c01090c0914100b070210 68
    0x4900100000c0e08071480300340d9000d0328980000800e00c1ca80c001842c41140d050751880c501506007001c00c8460320b009001d0100180003030008070000140d001c001c0240c3c1d4001ca00c8241c440c43c1e1041041107a0f45c1c2480c01c4142d25844c1c452040c1c2c4685c00158401000c2c1c024200894940d0000010a162481d4000c407164944a12141c1005000c6114020000d64400340d05807007209403140030080da100440d00c0b03001d41010084034024020750140c0301411880c40c4500c4c10044410b001000180072503244488504880a4001800f0095404010a158110507180324045403454400d045480742078201c1c5c030718040b04000f5040040d08107010001e000f4224000c1d0350f04031441c08091114001d4000311032850110f01801c160001c290b0090081e0380c424003404001a4070031160668905903034102070401c940d19904c80c485100007514030665280a0b140b038501c0050030b0b9603100e03030701620100c001d09004005c0e40008002e100e86400b070b8084404258054650140e0580e0070003045901103c10816864003142 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 166118444 1250 166117194 166117207
    0x51914041109040b0a020904020c01231e0a020d0207080d051f2303031e070204061a0a050c030d0501080d0f020325020d020d0b010f06031404060e0c06 66
    0x194910501950058108041410854040c003152041c140d401402150121001840040c0c2d29001400c040e0005403003d409c2a400110841c02d6030000409000190000c986c4525101c1350074072042e61059810004d002e0311031081b84c05100e0042c01a1107061620380005080d2070848898048618407680004c403103940308809060000103140560b110000c2180002862140244401c8410180d034440c4130403040000e16982e803844a6406880a1505800188070768202d80c00304000d91580921046840c40c2e4500441c41040b00300d07081030300b0800b642104803d40041e079243d480f0544103081554184190f0740c08000b82c0071465809424441008142080008210500040f80038194180d45480d50f90100c940203d007603840380200091104c03220b508000c1c1c10314031200e51505030301c640d0018100c4450300415401044009107040c5041d5001ca40701001000510f0040e0b00540042515140400041c0e10b604c1d844032440c08040c0000c0d04250b00d520b8404401c0005001800c00c00d00c00501e0031381c1d60903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 166119694 1250 166118444 166118471
    0x7020622180c020c09070806030f030a020c01180e070804030309051902030d0804020f060906070b0108160b030f010e180709050907050904020f061c05070518180a0519 73
    0x6289141000e80307141041440964a400000c5080b0f403507400501c84034036030b40d40300000c03904d403000102201d60501c0344001c0701d240810280300504c290021a4082c02c80c1c1d5448000140403404006444001c482c0c00030703410030200e03020000c0e150300302e02240303494102500c1e90b040440c041c203400c40025006019000c0c210303248480284200c1d5256109805030b40001809070420390315514201c50280d00071a07003018812052800900401c038042000341494240000b9480781384141100760401e88a03a846880043e80da03035411400000108008803d682c40c5180c500560300e003102e010700c980041523001401040ca58824244492900d1202c00210f0b210907a4454030702c0701031306060315185401d0058070400b103118100058681c1c411174010b000e5800d0214070780203205066209100308403014901c254030481d00901401080c1c0158525036403152a0241403500c210001c40d500301080c815419042d102c0c410b289003c214550000701900300003841e41c0d4401d0350318101c0c0710686d103010b80507252002904029 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 166120944 1250 166119694 166119719
    0xe06030a080a0f0f081e130503071208090f0304090506060c1006050109171e0313060c03080a06150c08040f030c0f0602120f030709030f06050403020609060c07020622 73
    0x42c09030b070313a0020008542e40039160310764160b80380b00100c2080c494010040c0e0040000f5a0000d00d82113100e044540d044d02d5107419034200313030001c48805051841030020700d5882a803054000d00c1840142c0a000d50f2412255543e01c2a031180a00051300e801c0000c600780c0e108030966030081d0240f401d550740603080c0e242800040c9130364001c003800f0038442000403440c1c5480c60340502440404000900c14201c407254001c2c54035444010701601e51104005880070512203160b01070061010391112200c011152901170309259004040003d03180c070300001007012030185903142c52541d44504111040c4600d5090440c1c19100780c0c0c1002104400200000040040c1140313040125280800d45a00158898804070784401100401646101044c00b0444584405400850b00480d40d82008140d040c6d40b0754680104600801050390319550740ca00300000d25406204159000d45108041c2c030315441e10002009c03840c0a03120000e0301075100800d00d9010007440003806520752541d031182d41c01c05a500c6441c803008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 166122194 1250 166120944 166120967
    0x6090c09021c0c030209030d0c06020705010e0d021b0d140f030c0a0c090603050c1c12120b030705010504090e10020705030c07091e090503070b04030e040e030909010e06030a080a 78
    0x450720b00f0300d2008000c0e11a2081d1204024000c000e001ca40e00100004c840002ca031080990345940c1c00c001c2240050800d12030301d040060b043c00948046030b00b1400103400c00d501040d41d511315102d400500b00142d07480307044031200c0540c07242420284040b00d602c0c0038074044203c060b50400b8407002411512035000050000d082c00c0c031540c2d002c08851b46030500d08040d28601d11008100f58031400200060f0b140c0b03501e20300304840c400d83d9541c60b400603546031130740c84854181080010501241e4005032014a901805003014000c0c0d0050415904d40b60000304144a01d1081d9040315603240040e501d0130f0b1040c014818000369040c0d05545601e2541030250310ba170300c40c0c00380d14424481d10030005041d400c207016088980c80c504046220361006502d0b00009404130040c1210035010400850000801c95000c207401036001c7d82d121100444910140403c444084541d0213065105025041140e81c0e15103643e41543e050f0840d0051903184c1c032000c24074000c0003a00003891010701203031038254190b101d04000075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 166123444 1250 166122194 166122247
    0x90307020405010e2703090402071e0c0e06040207020a0303030b0604080f0d02070f0602100f02210a06090608060c070c080303011e060504061e020709060e0609010e060a0306090c0902 80
    0x15410882103400305c1c60703402c0b503603001038a4005020a440c3d61500380d01038031405008448100890b91003049102000e42029001c075500141c10b0303810710841604c45802e42e40b000b0f055070114074200036600000c619403401d200080c10103450302420705194a0b88030070b03240100081c030111000c0309020456251580c040c0c44100005200341c000000340c040c0300f4105d00c8101d403007035009012a56901e46504010b40002038010a403183c00f000300d0062400c1480078a0404241d1030755145050501d180c000c1c044da0362a500c0035680d541415018480f044020820343d42000d070101106035174000350b00e0700c0c070114101c1c0d500204d82c601000c000002c941807814a502100010701056220060b201e00302911140550b0080703000240c00c9200341070780100900030510601c04a401268005580c0700b07414410344080350030581200001005029090030545451405441000071080283c5001e10106003204440e1002a059540f070781d604a040c4070202c4c140101500681c0f07419503861029030100b080600300d006c2c03204d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 166124694 1250 166123444 166123471
    0x3030412120513181401060f0332060d0b0c0a021603170c07180b0f03071d070c06020d0c110c0109090218030109030f35090307020405010e 61
    0x741507104904a425400ba01d0703600c05506820301c03801e205100108504492104d40e2203404040d440030607003556008011550b40c4040005802400406544451040083e6244003c0c0c00b2094401011a0001d007050500c040c40003c3e91082c0001b801c0940c0444d01411a01441003070005141a440007481c1c08083c1d6021140e61400d00642d400343c0301c43c9444054140b03420740910729840d40da6040105a1315907081d040b034038843d403a05040f100303600d00b208404082c55540c40500b5114140780d0024440f04108401030880d05142c4810140010400e9405022140302c1c4c0c40014083d40c0a03d003104680da0300104110f4075521b022400e44020b004a20f54030000c07950301426110140300020700040102030607920446020b15181c032000194100c82c00681408a40146c04401510300348a05e10101d4060b50b01e4003140714044002520b11a00c40c6c8401c211940801010002e541910b0b40c1e6039849000f040e442d0f40ba80d035820107240c0c194021020025030040c240800050314050250915005144403000074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 166125944 1250 166124694 166124723
    0x509090114160212070206091503070906090b0f070302100603080d0b06030412030c0e031002040e060a030305040612090605091005071b020d08071203050712020405130504080903030412 81
    0xb124104070710560b90300582c00a40116092030b5248050440241b0184c49281008a2400007880c1c04030040c050380c80c420008810842d030990b00c00c1d840001402c490500c480460308040700d5912901c200a4400c002c8040012410200340c42004203980e030401c000340c01c1008545a18000505070b00200040c4a0b06083c00050a898a090400c4900540c0e000e554001c0c40810345070141e000e0103010f60301105119150340e02c040b09031002d100b0b08917410980b941c0181d8550a2007101035020f14041c0c21a0301444c2c4006040c030009400404507400e440e11418100e03007032400c42540502414180d6001802c840c1000103018168000003005d005004418506001c1a6241c41044894009485404442114007070703051000d410110860011316000319402442c14225407aa481c0c0d0000310410000000c5da2a000c00000aa211000c11080c0304000310640c030301442c008c002100079000c04000c0d0b24095450012804120600741101c44420001e010717a0388456548500c0e03142c06841010a40b40a00844d003071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 166127194 1250 166125944 166125961
    0x406060b0a020a1b1508040b0708010e0c0f040f03031106360708010212010e070c022803050118060605090105030d0f14030103060501081c080705070c0509090114 71
    0x251442107105a005002c0b40300b040d2540c00e003051510544c8a12800d6219000c5815504a0140746040038143c9846070785017428580234240003001401e800801085034014400f0701d050ac0001341d013010720301d0800354072980e003841510068403035948031079000d820b40b2000208068004030450b505500090a680250382d03000d003c00301400c550070ba4040c0c0c49280c203a40b900c40d80080c00300e005a154035042122040358540403200c0c01ca034400140040c1103980b40e40100700c7c1e125000840c9600215514000451040f50b82c04103000e8012403122110000c180c0800c6401d164488030b45400a5411100900021640c1d0103400e042d80354180d4150784090400b6404606030a1000701d8a048610142c01041800300d14101210124002020b03e002c01c005c020602c9100000312019601941c05000c2c00a4254540415203250041d081c030314001103000d0001c1d038009039801040c2c25501c0041130410940c1c0d0840b901c3c0c414030140d4650040c81d4080c00e14401d010308107005622410701e28031000c070600d641e503c80818 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 166128444 1250 166127194 166127197
    0x70806031b10050c070b03040c0314010c0c29010e160e03030702010f020312011805070c020d23010906020c010b120c040c0c0605420d03020718050406060b 68
    0x5200b6008400d10111161040c480d400a0500304189002c0d10002c98903840b0464a5910954081c0c0313026941d41c3c4140140700d0120002c42801c407080d002088500070303c10002e84003844092025003a01d0b403006a01c4030200d44520200005502001d540c246980c4441c2c0b08402050140d8051f801c0d00d00c200c00c01c2c24400c0c01180700b10400c04000b07008506081c8168011108100c010450b4070441c0410b10041c2d0100c3d0a13001d155000e480c8a141c0c1000c51203102000202304d41c00106184c0c204003080d42c24001680360344464003581030b0418080301481c6181c42c01c0100702101400c142030310303602e00302504c0c050019940c09030040c0285103000b482660761400800c030399070104002c600c400e500041c0045405c0d2270580d10640f80080345041c00c541c801d02a4460808442d030032101f00800b007580c0d07c415110070104111900c40005546504100c400702d52400c00511814229483d0040c1340f808460b80c00c1c1402080000010910b000300030104070090140e81c005014241c41c00c803190b5040100c0402c080f0440e20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 166129694 1250 166128444 166128493
    0xb07120315030b01150917032113020405040c05150c0d020a08030109021303060c020a02040b1509010c0807080c0703030e010203041a0a11030d0c090803090307180f0507080603 77
    0xc2e100d407030703642000080c9034540301e030005c05424044540c40004d001c40c00d050f840f503124000000a1621009501c0e40d140c225401c8100811825141b40200001f00051510340e00c3c41d1501038400044a030750b10301d0010901045a04010781c02119400c05524581100d802012500c0d059011b581300d80d0403c2c441643d07036046074003000b01220b1051005110142c07040d03000d441d10b6110498003442481e580d8072680112030b100c0d010240180c200704041c10039420580900b0495040585252050300c80c0b80c087c1030b07034500078118224100b00c02d2800c2a81804122402e484100380c0120b2000e0fa590620620581e0b02c155074481107001c1801c41d15199150f41c0044140c500720394440b050008190040c82a020082d0710000180060108524040e8900001000641382000c015000020707039807003a140c003500701c1d803180e40b204000354020070550400e901d001c0341c41c40c1203449151006e915106411a0500688000c0e840d40f1206803825080080e420b9002e00c44500481050f020381c4c40401d2008080104c002001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 166130944 1250 166129694 166129703
    0x150302031b0f10180b0a020f1b0111030d050c0301051212030411060d060305011d0f072709030215060f0109060509060714071a120c0304020a0b0712031503 68
    0x1c40d00c8a941855520400b840005141113501080c0c030481c0d5048022450704040c04c0c2e41d60210b0521242601000900c50103203003800284007034031740100407031041c00ca2805038504000c0c1980081e1a46442003003568801e0f144481e0070b004034a000e0383d41403d00d40092052600c64010000503018240000c82d40f0500c1500342e040051031661540c41d60b422400021200039000241040300c60407580d05441084d014520540020400d1444084030003614210707044200043d8001010000080900003248c82c100c2c0c1a8440b03480c0a09100c1241c054482c14100700f0402c018100703a040d00816030f0101b141c140790010118a40019200d2005220b04e141106580c1030220b440c481e41404090b01602c06440e09103001408640b906080340d841141804c441d070000c40311640041401d1248614088841100e202104a400e08001d8440c038000100000a088811840c1340000428159190314000e40c0242c5152041252b5a050510309010103e5030303d0340c2003001a01e81017070002c09201c0720318a90100ca400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 166132194 1250 166130944 166130959
    0x80105150403061401170c030a1203020c07090903170f0f04110d03020109050d02030304120c0c03061407031d070302040e010605041112160903110310150302031b 71
    0x20201444400c40055010200d03400c010301c0004005a001d020b2103209070f81c0107402507200c0d4544504407000c410702c286002d219401c00c04d60701515850000b414000361740c00c4041c810611701c001710154000c1c80381105c441614041c107c4081b881c1045c540000402074030a81c0d41862240001d4000d0a5042d4142c4411001c284d002000c81d410104003e401030b08076005882008004e000c0c800044c80341070494000300c0150f5101e9101c601800012f1040132101c40b4640040c40c0355150903a501084031050100074828800c2400e009000e0104a080d07a401460b4003440801000daa400d00048198504403407030000213080a042010344541c1070b4600071280d40d240b0050403c00d080d80d080101420003400f05e2009590380741e030009400d56460051070844464070780f80564441e04500b0010368280000d040b4a0107203000c1d43c01c02121507200038003500700d84c0c10424603075100800350002030518001c1802e80c01c20038280301b081108000f1100e500400c8a01c2202102c02c003462465942e04420302d581c4410b80d01142 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 166133444 1250 166132194 166132199
    0x40b0f060d0c031103010b06180913110904110a140f010e0102030301050d0f020604091d031206060c03070c080c0a05010c15050405030408030f0702040513050c040c031401090207110a03030801 84
    0x1042c070800c11613444000c00101d44010b00001007603490300041c1d540045840003801480701c5080610500350050703140700b0561410345164075103c00344440c0c001c405000d8401c0c0e01c005000d0004104131009456802000501002e50301d440e10442a80410781c2039100fa20404501c840701e40c0181c07880403003c1010f80183d03046070f00c1c110400072031020000040d607014054040440041c0c0d2504010400390441410005040501c1c84401000b0142004440314550041011000840081215603844007040360201c0e80c52500404007425402550001003050300001d03c04a90750102140a0284440030754280c01c1c860f41d602c00440b038445010b080501810170031444624102515080550f004d03020f801101e16155544054500e554001540d1004011022894000310702d02801640c0d000098941c0424400c03a0580b1a1910344262440f8584107503542c101d00401940a45c000748940f00d414209c082e0b0700c0da990510348002e503201346411207011070410b8025010745002c076001d03000e072a050f030741d0320000d80e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 166134694 1250 166133444 166133453
    0x608210901050f0712090b040e0f070507050d0905120a03120c05130609060813021825090e0109021e0c15130c090605011202090a0e040b0f060d0c03 65
    0x501541400d410030108101e10f0400c922010b0007442e4552280b4411102d1407000780000b442d0b14950740064041074803c2008016030702000d01c45640100e074806121003182c403141400d442501c190680100103026101211406640129500d0107c503015601103000e01c2804400075203c0d0742c500d60041c04192014200040c603920399010f44600304140c24420b1414560000800e803a1041758403050020b942c03c181449240d0b400b50000750000302c58950350200c280c0a50020311003a01c00d1640c0c0e40e100c0c03080000101e034201c560070912419602e0303c590050036030110070000c01c204078a01072038000e50030001c000100f00c131540c0b084550302c044c0071309850f03004a00340d5652403031903006080404583c4500c40e5801c040700c40e60501030380a4981480e40000d88520b40c90000c03e81400b507071100400071300c0e140040101d82d800075800502c03526040c0e030041c2d842c18900c0008040101d81d0f04802209056103041108100c1544503480c0682c104088161280e0b40e0034003003110407a5140c8000b0f060107145102000082c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 166135944 1250 166134694 166134697
    0x616141e0319031506231201090b0d080403020d0c0918030e0603010807060c0f05010203070f02010b0102060c030a0902030106030b0403030b03061503070504050405030c121908040812040507080a15060821 89
    0x9501d51404100304c1c039a21b0b480788980c0001440140103104c1b540100007002c00c070f01c01d10800107025112a9540c800c030385c8900809004500c0040e000f541170085043c204500b20356443e003c0c02000c901001640d650307010200718206030f1071080f404504503003592001840c100d81524100d0b42614024900c150801c038003160b140546003000c90381c2400c1c12104900149007800514410000d42d82c0315031040200003402070960702c0e5444100d040d03400840c10b0019045c903001c11641e21000407400411401498030219004120a81c070180107040302d5020301c402c243e41a04141d100e02001c0301191650345800c20b50280360f0200914007617156010010410890034507410007548140500c081e6420544004000d600b00700350a28140d60040000605800c50103040c4200801032843e442d00074068545a9a281280d05c2200101e1a140810900140c00c0010412020000c0c103119000d0360b107454032926200f22841c03880b410803144503090444c0408d0b090000203014030181c5281551000c20025140851000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 166137194 1250 166135944 166135967
    0x110306010507080f16210815030c0d110117090307020d0f0b0403020f06010b160f080f0d0b0f040507021906110c03030a0b0616141e0319031506 63
    0x190f100501c10045902010320260180c440c0007412818800014544402000d040c1c0070341030304590310008240c140590045841c3e5000c18546a1501d0360299440080e00e03024207051400e0b0b1000c000310600b0100306008200390302c10b40080e2203c0000c2e50620030303285590581102c0c0215a83e00507c500700141c5015868400c0060003a140240181c0070354a49400c81d200403141900564045400c500311100100005401000c5010141d802c02101c442e180000210312400980f54880008480003882800d00844041c2c403c2042020303518440401c400018215150015108901c1c1081181c020308150040307902c12415680a00102d01044001010542401000381c800070b03a64802e1840509580c0700502c040c80501000315201d00c2c3c40c0e0701210a40c3c111101c510f000714814001c0c3d10083c4e21804030350700c6450344040407052540513409100d00c1c1080403d00412040e8500011090b03101011000b0b0071520030b001450007060312040d4054098aa01c4260150305c0c00c0c030130030708008044c40307488421407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 166138444 1250 166137194 166137203
    0x150305040c0b0a1d10091403010f05090604150c080105060310050a0602151605161401110d0e0a03050d02090d060f05060316050112020906070f0308060a09110306010507 74
    0x725445400075003031600109080b0021031000b491559204141e0300c1a0070440904403a40c4180c2e096103803006000c441e05100d820044011403d0b0306c1380036038080d004150f13191a0540308108034613214910f19038400e000d48054860002002d404240c0001c5402041000030031a1507941a90f4138120611842c1c1e0320007801c86c44011010302d0f000c81e103039031b800b480c1000400542d8001c0001c2800504402c042c0031024140641350f501e4800072100c05500042540d0800c0104141c00c500c0340072606045521900c030030315642c80f95180040300c04218640c0000707171000300100081000082204002c480d81c170102c4090180101f041070185500012680d002050310100243c8041840e1100341c5e10350058451070003200320220b40302d038100110b80c1000c12001d190740808940d003441582c40d00d00081e01320901000c620b20160b8000500740c21a0f05d40d00d088032841584910280940c00c00b50030014090403040e0358207840b6100c0101e000820b035106000d4450040c05103c02549551299001950141c3c8800360496 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 166139694 1250 166138444 166138463
    0x30a08071202030c16080d05010e01062715110f031c020c1b0d0203060c0d270201050307030e0a120905040209030714030c06071109060103020307020d08041b0b18030715030504 77
    0x84007e80c080c080e182c000d01d00215200c0302c1d541001c0018140c00540381c11400007000002d80c0354146102c0c0302800c800c4a2880c1c0c5401054013401c4e80031a0304010030310064800c0c0c03241e8049001c5810001004010748407c02003010640100c1551550030f911a610700746429504c4076a4410880c0d2849803c02c2c0451401800000440895404281800812101c0a81468010aa5400c1a82079020300010302401f6912803549040f6080042044a540000a07040060110000e41c2c00343c000e502101001d00d8140c110382c4290090328200000284105003540050410600060b1908180c0260b4154100c0180035103010343c140103240c1d4882c402e4800351507242c8981c1c1400d6040341c44040080040c103004420003041c0382a400706001101c007020309034034105441002080380c441d90210300d4034440d03501e41c40d0540c1b0315191410215035982e903070302d0b08034a200804800001c0c8803a901c8000d20803a5500403a062003040d00004040e1034420600c540d680f4559000c0191440c584280e0095610a1056003040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 166140944 1250 166139694 166139707
    0x30c0906020c0111030d110403140a030210020d0212090f0706030513020402030c0919081603021e03070e0a021b0601060c08030a060b13090b0406080705011b0203030a08071202030c1608 81
    0x70051f112043c440c6480007800090a1040c05a0810380d91000c4182c18000d0686100341d640080d601d481e41026400180d602003003445640c140ea40448401202c4002004414188210020784030781d66030488001910916100054403802400340d944680c202165000d95448242c00b0702c8041d61008061007080c0c4000c12044815560f18880c1200288a4400e070500031414a240245020074000303596810b0381c030a03101000160781d4070301840008081007050841801c8111b000ca45490381036080103c1584822041151400440d40a4003200c1c00712003101440840070001d02e92070340700a01a1000040b01002140c010a91075030003181c108852a50001d40766917140341c428110740240b08540c20601044608001080303581c020140404e01c21038003006030b545400071841d940d000e81e00c101d906010094005100e2128072010202d06540c0142c1035075500c1c07036003440040007017604032007213004110340c055518905403492083d44d00c2042011009442d142d0034844400c6d80c500030341e20484042c02c0070030a0703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 166142194 1250 166140944 166140967
    0xd020d0e0a08030105031b0307060e040209040f0f1805060606030912040306060e0901023103020a080307020306091605040506061605011b0e03060105090a1506020d030c0906020c011103 81
    0x14101c054003900080b074032941040109820281000c00d0700012a14038006800155000710752002100d11a040c416018150880800d019002d03540c40d0725401403801c0c00307450000b291038000e81d0703007044d629808000790382e1100d440e020340200700800600a64844000a02c02d428218000c44e0807201c58400c032902c8140e4042c01440640c000e4000301c881d9520781200700240342844441e1034001505000960034401c400e04500310784420a0901c5100041031039000981500c407002c044051078010382042c60141d100c0f000955a6400281c00b00c2c02442a040090105100800e40652407409001a0b500a074640020000a0b120241100754058410041d560100d480540840b1520f4414000403070040c0b1008a4221603000d101000004c0c0f060f80c2c0001078a41d503010076082e042da0011240304d001519401c9200000740210000c0100625211130046425600024180c584002c01e0b40e06015100161000b121640c0781c41c880c0c84090381c0b10300e40c40d07140c1d903004403501601c1d25007813821a410101d04114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 166143444 1250 166142194 166142203
    0x2010e0a05061b19020a120305070e040906060513150506130902091302032706010b070615091d01060f14040b0d060c11060604020301060915050c0a0303050703050603120d020d0e 78
    0x84101591046c0c1400b000c000c01500c070f400011541d82010402883c103044081d00c00307900b0301086840303a9641d0040764104601540030070003030000074100441001e10508100d0050020806103400000c148400240a290a6084a1295811800c080360b141e190442600c0a5003101100320762000c1e070075215242e130485a03c061445500c00c948a4448202014804110191005804107143d0003100c018050f40a0110855070700755031182000402c0caa86400c0071402141c01d0704074a9000e070401c26040b20382100c90844442c0c07800c15400070040a80d40e90070140c0c81000b540304002c00b018155901d6541881c06a00441287d81c02405450b607092155454004907100c5c2c4040b0000b050f08005140c0a50070b040150340c1d031004040d1011442d41d4188040500982c1640c0b1031000840c000107899401144600b09a03a1101d540900301d6099801501c1c001c1d001d850210b40302400280381000266003481c0020314482a260707991071991624106070241d00195105a6403200c0341512842c00302c0d2945401c02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 166144694 1250 166143444 166143487
    0x40515040312020a1110110303010b1908150d02060d050108163002060c0a06021902010c0c080a0908030403110108090a0b0114130c02070602010e0a05061b 68
    0x8015540c03400e600d0010940c1e1120000c081c2150b01000810303000480003616004140c904803441c911511012600702c0390020044002152400044000600700182d6009815268180000c840050721401d400300d4010034100c071541130300d003025031204d0740302e0522072441c00385a030029080b1460806070702c51906c2615404e80c0009025071008443c0c03445110400240f00c094149020303400f01d54402003a070074101003034000d420102d207090414290304540c0c91104403000f011014040d50b104504600f8203c0c025006294100040c0300f0a10f0858806403061054502241c100c0d01c07012030b007810541301d80d0015000b021500060144881011926280c10000760000b5442850a00850b038011000113090b02c1d005001049503600000700c400000e00a01e1080b8155040d4902400c65648038000155180c0c0d1000568100c681c41c2808085000d075010403082c0030385116030001c1c0840030401c001159110600b24000d001d941205010440d910203c002c0100c8084526400070305044443c1f041079404220f80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 166145944 1250 166144694 166144729
    0x109021305091008060a020a050f0901021f0506010206070f0f0e0f040e03191e0e0105090402120702072c06190803040603060f030c0e090a0b011412061512030405 71
    0x30020413001104100d042d070310800011055003020b104400140490061042d030391607101000c541c4004613482085607031000c003441640c4560100c40d214101c4002c00d03065171400c0c0103000302c02c0018200390280881070401d0420b59907030200c04054040803145103411209065004081002c00102e5a403140151030f000070308400a1503441c0e600070f00e2942a00c843c018480188104041d41c0c0c01c10407a000451184000342d418914194503045004075024815000703a00d81c0644042101b40700d26105000c1c07281316400c95021104030607180c441c041449820410307074000e240103004400540f585500c0180f038101031b01510001d144e034480001c64011500a40208120303a00120701041402e525004042c0100340400e0782e60b0001c0d045403234480315400d01d805035038000321440000c030780c107031000300300b41c4d68402d0700300c0b22035a640e5841d40c40509548001c03a295a101c0c0e082055100031004011500600441c4c1c1420404aa45206024003003084015114800c050000f0320001601741c60328218a510170000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 166147194 1250 166145944 166145971
    0x3060903040918050c0907020709060f170a05100c110109050102090108150913020f10030c020d020313140d1b180b090403050c07230a08060708010902130509 69
    0xb8120024201c4180e801040e0806010000c04030200341c002c1006121584141d070151410380c0e400c24260325094041d032042c02054035180000829a01841041e801c0d124540349000c59004064122541c44500741d00260841e04041c3d640c909641744c0d0b910034580b200107070a10fa8101c4544001141c00c44809680a55541c1d400050805207581c2c0540d05a0380312000d250804101c003900f1001c0b904862000b80b00320050351f802404107041d1741d00d208035001c80100c01804149500700d5240000c000e4030110000001501c0b81c203620250541c008030560300d0700152211005400c41c60090000310b103111a00319950869120014100840c8908040104181768020103418003031030900d02407400d07801040c802c07411138503082c4d0710202555103554141e04035070140b0b0300c140c450940b800301c2070900d00030f503000703040003c0c040c0d40b07c18510b000c0d480b4200c0101003c03205807001300d65070036506841c0c80d41103e9080029003400c0040c800081c940d070181441810038110111500e4543c1c010900c90801941c1003c0e80344103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 166148444 1250 166147194 166147199
    0x1503010e060106020c030a03080f22030e0103180b0412051b060103020f01030c0e090703021b0c090c0306030a12030b220c09060c1e020301050f0a2d0c0e0306090304 72
    0x13010000844030f00340a030000c210181c005e8400410521b0007416070000015101d02081a144851a40301e0118070000441d20354103207e031802030320701d07034417051a10f01081c01c29100003d00806c40d4441e545040c0c00c4801d0701120781d600c1e600d480005420515840c1840814840e1b40b1400150301d01d00251181c0c11001401e5950450040048032107011220504040c10f141c1c241c01c0b0b40750b00c072021700540441034400c81056216071400794040e02400c01082d40100301540600c1215400162912294900341c40740040d030f46880011020521086840c540c040c2d0041da0050005400600c076001c00d101c81d0302d03000a115102d180002c1145440010101443c0002c5111000c00c1c8252b2140e2140e145060810358084e03460030802816940d1800e00c0900202510416905000f1002c1c0d4000314a80e401402044249000030603800410030680c1c1110269140c00211800d00d0303007010907942580958000500400c606040c000046d09585040340108080d0030702100d0790307071420442d0038090000c0c000079588890 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 166149694 1250 166148444 166148447
    0x30f0f050609030f0a08040309182f040303050315090a1a030705330a030903020f060103020306060d0212010501030602090f09040c03030810170705090a140f1503010e060106 76
    0x10005000c1e01c446030000c0014140000d43c1c04e040320000007880c14007000e41e5442d824142e401031034a0b40003501e0a14940c070000d034488180e91004408a46000c48210a422000a0340d441500b20340414281e00b0001c01c02440442d0056014540c881d0003a50499015030b481808980201d1080e43c43d0180a611001482c40318100a402c60000d02d0b0280c3c001c01d01d040ca01400261f1031002640e841e0550f1101d072800f034a00b0304102d110020140614104980d0b91600340b20010020007410000743d00502545c1c40d40a8101e4001c601d060489030000d00410040d00d40d0302c01c20407075803030320407040340e1010300703145070b240e100000b030103020f001703501588005807505862010b00c440c0c0719402d4405807040d42c802c2c0400c030003c3c418490305c03c02d40e601881c00c1d10340396551000e040c40d81026908a00c2001c070050121034074455001a400050b11001e945c050f40c2d41e101e601c14042502c14400d180300c0446050307c002039141c268404100d0740302103007991410090750010701084c00c660310f840e88001140c018800500036907 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 166150944 1250 166149694 166149703
    0x708030406050c2b090c08070f06050309060f07170f01180917030603190f0201031505060304020d0501021306090314030a02030a0c0303060b0a050c0d030509070306020310030f0f05 79
    0x1500d4114075500e0b00e00d00b214140c40c015800c0181d01e40c00e802c011441c0151311216031001142640c03200702c1140141e04c1d11038a5a0313450480c400c0022107210180041100352042c1c0c1940c0c01541c080707000b048039458040085c07402c2c100c02031a03036080040040e034440e004920000b0040c06040401903000065040100c14682c03c2050403428402d241404100000280030407000850000c10040382626a01e0381d100003401c0801c240e00001321035039202203680a100701c06e50031080c928803d8070100042c08403d407256803108010703c90ba6030300c104140002405030400c110490381c031605c620300051400d0340d00350500ca603020045c0c100c0310004040f60024020041440704030418144288011401c001004070300035902e211340000d94003080050408581018029041030000d002e82504c0c81d511a1300c003050041003034010001078075652041c8480b01c410315001e07100715030280b0381c181c000d01649400c44d210700d0040d600c003070058224403002640c008007090620401140703151050840071002c460504007103141 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 166152194 1250 166150944 166150951
    0x60b040b030316030507151103090c0144090a060b040902061b030c100903020c01090e060103090311030f0903070f05011e020109020405041407120b072003070803040605 74
    0x280e00411008608041610250003a02d9140c07070710071b584030007520300010030007451840458400e00301243d80780e0303d07455200074601c92031a01d4125107080200b8401151000c0c1030b0302401c1000d04010141100b880c01d0044591207000781340f14281c0d519002142400a140401c48442d41e0340d4000d100c00c90200071090140500301e800c00c480500c1350400540001d20948a07100d441d440e000c645100310540b2078018401e484c10703104035006450541a4006515000d007106030740450060043c0280c0322019800b40c1918820b803120504250310640d01d140040d0300401a422044e0240071380190020b900307190400c003e000c5084c81024954540b035a03c410b2600e4000b10703422a07406510b03826024070250740d003d03490f81541a51004d091060301503a000580c0107104290019400604003030402060024011040c042c45400300304480c0401d9441c6c0200301aaa00550001d068410700c00105859a2150a11211100e144044d408072112036070219403640c3e0000200702e5800c540402080188044d61040030390 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 166153444 1250 166152194 166152199
    0x702120d1112030105040902030a0b070504140301020c060c0c0a0c0f0501090e0702030d0c030e010207030c0212010b010c020402131e063e030904060b03060a120f030c03020a0f060b040b 81
    0x804560b12070104006000c14040d80c0e020b6691006440e0555a0402c18208400d400a45040c9030b4200348030002c10551041c007549071984c011810100144c01c0501c00c03640808130303c101820494a40e141c001b20254041c0f00b4463301ea10840750031030040381c50400c4190007407a0b80c45024001c2d0b440d11002410100a80d440101485464010030540319008400c403400c6040507440017907403246041d8141e00070031020066079440d41c0301003242400c25402107072480c8558000c0302c4980000c482d819881d4242e40000e9032460006030200701c2c05c4014202a000303848100c3d030080c0c840c0705407501c40c1c585005a071243c0d8103400385103c042200b0032009801c503c1c01c6110380310000b0041c09465080c0c40d20b80040e0945052030b021039400a601c103c1c4c414040c0103840809400800c18448259601c0030b61140d03400954104d8030920243c0c034001071200000c02c0300d500e0140e2043c41090075507900e403003e40d0754500440040d001e5029200113080001d04d0844861400d03407003880000b440c12105400d10003243d8110080c40d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 166154694 1250 166153444 166153453
    0x22d030f240f040b07030603080a110f070b0d050c04090203280b013204120209240d0312090b160827030c0708010c020d0905060912030702120d11 64
    0x2448810030441c03d90103500b10303507540696200c0c41401c8000341041d500c0031b0705070302d00411114900d075401490300028480c80d504032010f64940c05521601e80c0804e201d40d181c900020010034038211000d81125600010080e80741d41404c1d69901d03440203991046500d120013600d008040303c8041e0070b0560305040c000c104c26040040034038410018002100503015026081300c1640700c1e05002290b400c180442e10050410607403a42c4c0d035101090072001e06030508a05c035080860000d244094103806d11300c001620794103181e21807135101050180b21301c00001c082e0b00b080400d6821600300c103524014400340b140b05200f01103661528070010a0075540c413500c0901000501e07018818610090071052403481400076a4952026610342e50074510302c6400d00c0d074501030281400004001c0010b41c01f8555020140c1c00b07440150140d10b0086078120040d0061650020090111040720b00303019900c82e01c450181012645401d4164001913489803846000b048194041500c100c42c040c0d1118201061071501801803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 166155944 1250 166154694 166154701
    0x8010504020d0201030e0f010614010f110604080702010203040312051e0313020f0f13050115050f1818040f0201020706111c021c020303010503060112022d030f24 71
    0xb0080791400300003030704040c3c81e20400300302007506102e8064650344090081041030369900c400e04c1c0701100d158246011842c00e46001e4026401010b90901d41000000600b505031303070390b50311400903070044041130b811440140000f100103000700240d022209041c0d03c0e090307200c00c0b107150303001059102400310440f054001e005024418031040340e4101e0341c0c0e0f0304440e480d00203001da401140400d07010341c01941c2d220300201c03010600d240e000d0748618141c0d000034005c03000d070064520041e2030910610350b9206107810200070094020f03c44403e01000c100300204501a024485074407948542011748043c2c401361303ca0b210300e504541c3c04102000040c0100d041820b41c210741c103170040b501c8080740c448007400b070070b0f80054404c041882400690511a20034140307804c0942006402075a0f60024064140030b40314440000ca040b5952403d46e40c840e45d4028002040924a1012030000c5078805ca48440b4090703004595241aa0301032154884041c80c440082c402d004c4c0e4400d11380c4484c4e4003a0b80c80c5000c4503110060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 166157194 1250 166155944 166155949
    0x50703080403030e011b03090506071e080403020c04020d0209090a050c07150b030a0506090d050909040318050a0b0a02071410081504021303140d020616030207020406030303150801050402 82
    0x203a0707001e034041c1800116204089002405401c00440b8800004641c0200502d916055409002150700a00460350070f07968080055604400b0074100300c81c09038440074501209441000c026070b2251092040c4d03158804164003290a070307001800c1d088000d07a00441d40c0411030030b000d001d441e0300030f90341c0e0310600240c200015203400510034181e0203821006605003405411983c0d420204002d880601219456100c13400c045848100544803e00306019030744031703490b205100d1416514070a40061140c28161110b41c5c00342c0350080941d08425403030072200000602580e076601002d008202d21900b030780c0d566003142e200030f04018141d0024040020400522811921041079030080c03100282031030240d60710340c80c205001c442c5403c150140d010740000b46440c02d06620781c542c1c5e02240e20030014401700022400c0010303110711a040c5244016031080c400074030040f039940c2e0003040c07203409424014500520754010400792900c3d504242c000c80d032a05c98400c40c110b00000100001e0401200070001c0d070030190300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 166158444 1250 166157194 166157207
    0x907090b0d090f050a0308060a0b0702030c120c0907030c020c0402272206030c06020604151e06030b0601020d17060603060103020c1f0b0a050916140c0105090706050703 74
    0x2401c103119540d0314075410802442001446440d41c00004580d840c01d07091a000380702d02000ca40090061b180264000b690038500400d0710100740c0d0080c041d200d05040d00042c080042d01b00e80030005a417091a501c50100e45401140c240501305940c4c020407200400d51f0301032318220811000901461040080c2141a10907400f0305024205105208540d0300e44240000c00d403c002d070103480c190402440c1042424042c0703070300400171607106818100415030b6442080ea25800e00301c401822040c030380365405c0404c084c103500c40c0ca1110341701095004840104103000044540d6a00110380340302c44c0c0c6050008640e0100300385844d015051a007882440810751100c1e140f441c002d0b043c80d00442010020441c5a070081e015141603006480490369510443c8007080c0c000d0040003d0800310030300c0c050213444030303003460448001652005401c402c0151510200d100010aa80503541c0400005810406620414400800901d805030f000031889041490b8441d04101c016405036050200c200100c0300001d80051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 166159694 1250 166158444 166158457
    0x10318020f040e03090306090a030e0f060d0504020103180602070203010b030313030b0712110d050703060f03021302070602070b2d060f0d080a05120604090c05060a03020d060303050301050907090b 86
    0x60700483c251840e09182403441c01816035003607041c040c9204005200f100020040782c041d020740e982e1180415203100744254881400900f68100c881040740d400865940e8010980192040c03500080d003500200c0030300e000d420f040c40200ca40c5034000401d50705503e02400b8040d9003c004801071860007004103010f1028905501c07000f80071011a07400514440e020742412801d038140c0910500083da4038600020803030f40030a103040395061510010030740441c07191282c0c90030303170b44c80c01140d8002d1802c42c0c00308200c605c0c04100012107190200180c00004005001915070705100c2d00c80510241060084610710301c1c1c95141010100301c0d16070380c035404e00518040d80c9070054400d86001040c17031350002c0030803a06102d1a9019101040004041d9445503120004000c81e914040c40c500c0561a450f0402c0240c46880d1806000c0000400040c801c9160140040000800a0a00526080c0003c0200d0103031030302c2c1d0340150089503010004020a08201ea140340c0c0c8041c492804d15089410a1074600e070900412 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 166160944 1250 166159694 166159699
    0x60f06010f1103040e04230712060b060c030a0801090902030a03111c02031902010b0d03080c19020706120e0d0e220b120a2f060c010b010318020f 64
    0x80d9803159040c007400b440d010b0158050180d1383d40b9a00d400b00780780300401c2558119103801602103a8641c1e04c0c1d6000180c1000c14040010b0494286000f4985480e0114071806480040c0d941d80c0c0b1660540c0c6030002044ea0b041c0a0000d10b48481d8010401340805005030320445101c0d05045000005a40201d4a91685540741c1801c0c038600d481400401d1414490f0780c2c25907440040b6102e480074264000000d004094040c0c0102c0f01e89036071919040b03090750342d1413a03442e0304448070314030000000e07008042c80c66008058086090802c0b0200b0707088240c100c0241208000750f00004000c1c410a544030301000c40c0d00c01945402d11482d21030039070b0166070744102400d0b4020800b0f54501000c80d0356869020514681180310500361950300d118640e0001c01c51100c00e180318120031980150880380100d00c0503022504284440c4e00303d00101c001a05460302030100c511200492546601d2550300c1c000504500e004201c00060648401800517084030004201d0030705120000913031800607504c20380c0203e001c010a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 166162194 1250 166160944 166160957
    0x91503020904020a121a1e19030303020301060201051e0609180f010e070609030c0b070c0306060905040303111e0d020c060405030a080109020906160c0504062303060f0601 75
    0x415404800a0080c18000c65000d4000102c291000b40e000c044c000803100f0550080060401501c001c40740e0b410009039168004800d03281c90310080040b0034a0241c020b402400101860080d506244542019508204c01003503021005005440e824400e41e6808040c501050a0300c103040006a844040010100391040500c400041d41001298021080c28200241141c03071080e80c0441d1507000c0c00041e406a01c4c02d20810703500044680c4640000f80450303822a10b40341000341441003098540d44045001d858000280c0d200200040852082c90024120780c1340000d0745061a2130010b040c1d480442c0d040c00b103d00280041408a901a001007030546100c0c0e410b50303511803e00403000c0103070003069212581c5004000422040c480302000400310303120f4540c0e6202c3e0760b070380b1540c0e01001c038000e40070015080030050141654159492a41e44002030150741d10000d25903903400081e0940340690400500b0400070000140174035240102070941c0d03e4200e018080c0c0e0f00d00341c1d5000074040c90080c034442c100700704c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 166163444 1250 166162194 166162229
    0xc0506070c05060408071706060109031202150a0c03230c090a120804031505101a0c0d0f1107050d0219030611090907020c0102060403050a1218030e0a0609 68
    0x1403480000042c00c000e015591604d40c2d50780b041da1640054891b1491400b00055088212840420030500c5018141c4403403a0075401c540b182000c81d45500450320035440b40600f451600d440e001d034600d1144010740000b00d9045001ca078024140d51511200000200ea45112a4080f040f032861440d40242404550354480c14800c000400d80903080d4001201100e1841c110700510074008018000c0d207001d841c0140c5107092096010301120b070120b801c8000400c0e034510a000e131348052642208101069911a0b0800300000744107810400100140c07408600d240b585481c00982060b00410700014080180c11140d01c2d15001c81c0e00001d200708002e12401c0c5e0302c22502c0c03a0b1000b001042028507045501040a0228556070004a5200040941c405d02c1801c0010304898070010784a130030218107034058952030f00d80d07581c103071540d0304504001d000340100400d00741c42032800c3d4424036284403000c1500301000142400d028003032007100504035000c0c0720204070900981ea00410400704a641e40090401d0100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 166164694 1250 166163444 166163453
    0x30709050613060318050a12030b060a090608010f06050d05040203010204030f0c03030306241d030d020c040609020f04060f020705090f0402090601020c150d0b220b06070c050607 78
    0x25040e0016644031001040801e080308100c40c0d00030607118a0344080009020b050002040388104c400000c1503035005202c514006504281e49940444460802240009040000840980040c800c0b0800602c10070401c00007240d216072070a005050350440440b6990401000811034416000c4080e0201c0d02c40b8049421500c0940c1110011500000c4013407240c5054901002c43d03942c280302c141d001a003042c03c00b0504020b10010841c0042084c0444da40740743d10400151303000e1302402104071500b4800c060000503514203000c02184034845a0141c42c401c0d0032203080100300c84e200e40103015034510501030300c4401205641240c06403a01c501b050441c00f610108100e1030303c5c4040d00000e400281d620280305000c4102e60006000314802c44401c03a1594400c001241c1d0354540c0440c1c181e004500140005642c4111320007020042e14400e0040b80030310700d0034042111403d0904804900d09807481781d40b001407040b80325040e0601001c0311420314041449c3c80e607144404083c0622032040100061200030807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 166165944 1250 166164694 166164707
    0x6070215070c030530030720010f020909100503060c1615020a11060705040506090a0e04030509120f151f0303030e07061403010e09030c03030c090f090910020307 71
    0x215880080011a1034603484c1c45601c07000c84058a6060050207203422455003d040c199510104003080c43c181155640e40d011922080c2503446040301c0a264400214005802c1c00b480c0440c6c2008440983d950790b070201071201c01030000306003455030300c40b00d1018052550040307001600880603003540c039200c0e0384003800844894207280d0028001020b82c07030f1107080e441b880e401030034104501d41c88850f2801d542c040465154a4100d5080000500401081c03249203803010280c544a0000f0f020b00401903101c01401d840f2440954054002c10300100304402189800c00c00301e84140a100094108243d18001d0159205500d641c1d000e80680e0f64000514400c01060300c1d50b00c10b07080d403c1c5403079400e680d80c01c018009282d240007400a5015422011a000340640d07015a68455960b00803460b6078604070940380750380000360030200140010812001a10700400246002d440e40c5130f60155260200410444441c0c40c9900e910301607604482000070810001c107800c186045024400350b0342e582d0342072044600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 166167194 1250 166165944 166165957
    0xa06050601120c0e0f01030c3002030c07020f06070519060209030114070305010b0405090c09061606150e0c031503161d06041104030312060f0801090c090b06070215 72
    0x250b51605400c0741c600c662020381c50013003140695403032600102c42c00045041d180a440d200022a9101c1507a1611001902c14480c00e8007810000307103294690b100404041e6030056400041090300843d145095103844521084a403104503461841c18400ea55195207800143c02c1401c100007150600c0010f1168a804481000034000d0081107128198207a0ba51108801d40d40800001e2409002140c90310308241201c00381c51004084038020340c0e8074540c401c5181d03c643c0130160042014000303c1c1c000c0020886402001c0c1c803640d408506449808020384402e0a00c1d4010420f400ca4002030100703260003001100e40086e0a0710400138850f070f180010a01d8910412409101d15591400000394141c100c410031140d80151200f103412603da002c00c101c00d4034104000114504020802003000038003a0300c03584522444c2c58400301d00341d95220303000c01145400d070b442607900e0f03519525100100103010ba14200034050040e020041118039401141d10f60080020082c081e01e88030b00a824208184000d071071a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 166168444 1250 166167194 166167227
    0x9050a020f030106050c1501060215130c080703060c0305070507020f0316060314010e07200c030604140606031b040b040e060a09230d050d02070c06090f0501110a06050601 75
    0x75256903807038000708154401c120300b0886010307d026040540f070013082510304aa200c3d41c010240507900c07012141c92850094400c1180c21240070030000001d0880000380020450301f40030345000c600d941024819982d1000300030342058504001c00401c03d07080800c0e20a5940c060301e001c440c9009200c0800c0c40c180c4040100c1e0448410b41200051469042d00b105d01100501c2c00700e08020707680c6001c001c00300f14054803c3c2010900a0405122204036034103441803444506040300ca41d0158000400d0a00781d09540c00d40d01c020a6400880c8a014108100313504000c0030341c001c1250703005182000700c500140301c446d00d1141d501ca91080070941e840e908269026940801601c540d420020410380081c0700111040740e034800e1030881c695003400041603c2c540800500041c0005014105e0216002c0e4408403800c20751550a00c0b030100414900c00c0711201078032041d21807060a074241a82d65907031032000d41c0441c0c10808405150070b507d40d00072800c80303046176001c1004074140e101e4030010f880107811140e080b1b8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 166169694 1250 166168444 166168447
    0xb07150608060105041109030d030209010203070c03050a0b0f10051003140f01050a0e0f06012d170a151211060304120e010e0d020d170c0102190c020a09050a020f 71
    0x510381c0d00116600c2d04884003158204480c82e0303605100038030703030103400030300c40d450b40140a0b04402240a03400401c100740e0148192490081d0700e075030300d4441e402c09400540742c0380c3c0200789100400c400c0d0401650018a0005000c0ca240b501d0120b845503000d05d809414003400c0c1211a40340d2140c0a44c21098a00ca21500100c51919141070a0f000d03071842482036522911007003a0003d0030010031040140103207601442c2d0f130142d588480056488506200106081503a00d200e804407075071001070761422140340c07943c44100300e80401e038407141c0031321016062100c0c6514200303266081c0c00b0b1050160089401040089007000c5060420501c8085801c9125400030400410401003011000c0f42041c002516111010700b98100001140c46a048024040c1c1050000c0120805481c01a42840915228041d8a0015203004a42003c1ca401424103d01160f40104680c3d00701890100d80303100c03800350b0b0b10b0300350000702c440e8000500300d031494811049072655410126265a02c00d40450715400c11812456 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 166170944 1250 166169694 166169699
    0x12020321060f0d050a060b03070522050a060819110604120b07020a0201090909020d02061c201902030d09030e01020607031b0302180a120b0703050405070b071506 71
    0x44004450841e07526109208240d264481c61500340104a0101e80100003031040c6280f554882000b00402a2407562601c225013001800740d079140c1c0950a40321005900000c1000400040d6041d64405007900f80d600d4240b013018046420001082001d052214805d0206142e1031b081c2441100d002140c65a002140058045020168101d4581c0c05a01c0b07150450450346da4010200d8691900c808003c1c0054200103081000c00c15580081103007900050a0083c044510350004210354098016400f20b80181c0d8240000e20160388190041890390b80c8440c07419400000158040f449a058011600c1880411070725045108005a03070030354540490810281c903450402411a1124080e80303030052145c6000111094800d00074401c2401c201ca80c0180d10845565081e000713034100320444607190065030365070044e0303581d4071200300010080d0f0703a6a91084122800d0441c42c03400000c00d228141820f010900c00090700c00240c0e0422640a110b0700c540720080e40c6052516000e6024810900d0390412601 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 166172194 1250 166170944 166170997
    0x606020303161404170309090103110f030a0503070305131206050f09010e07090c0507021908010501050d031d0f040911031b06030a05040201030905030f0c0d0504050904120203 77
    0x1180101c9024450301001c0d591590111109020f100703031482500e40c02d21081014141c0b0100d2003800b5103004065030306084a000100350703400000d0b4425112034215580426244c200119030222481086d8040c091281c1d442d1a42a62846441c400400b0050700184160801f04007454070700c050300e60981c035134075481210b003044000362505581600b207212190b00860400201445055040c87c0c81c1005000420320b4011240020540d070744000d410700c03804011800044e66540c08503c07410100c58143d05082e400c0c0400142120310503000580502180146900440d030840d00707000c42961544096040003880d50041005004000b241a4010f4203240130b9208218000308480d40c40c02c026000c84094483d1130021101d400f02c09105143c10a0040001c6410b685468001c80e91060040c1400b0501851907a01e09180d5400314143d20300880f00440c500003500d50038080040410810300c4c2c02418681000006030f0940d034003a01c005c000070200c144100b00c0c1c50003442501c0a1013000c02800c0c2e18180c00d11711 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 166173444 1250 166172194 166172197
    0x307080c0102010c090302010f120b0d060e12090a03110411030403020f0f120409050a0b06120a05060402090a06032a030b0a08010e070e070903051b24030c070804030606060203 77
    0x31258003650030f00c415413000c00c3c826039417801201c0d0140d55032803041c010703c2419a00c820481412000c0c260b03c0d94440780140d155039501601151142900044076503120380020306200c1c0104002261071010810300540341d85203500e8100303aa8104c0cac0701c5515a11704000040c000e0034209421655200080100028941c001c01c1440840c42e040c0c0c00d4401c4a034240302041e444480c80880c00f80f84080a10013030100307144030303403105030b000b004500005a1078601c800050050b402061041c1d080c040304c1010003418007032601409801c94020f45041d42800e2004c80012681502d034080e51042503a03400603018810152000244623070a506900c150000c004040200640318242d241e90044200d01d100007001032051080350102c51001000d0701083e4144006812207410140a100410590610105c0070440503c2489180c1095820310707065040803900340101c2c05100c14962704414030301740d0724544c60303e0450b040780d5100c01500b14056843d02d0a24222055000d02d0700040d050518011300843c01a80010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 166174694 1250 166173444 166173463
    0xe19021c02190f020d113f030601141621090506070507090b0112020f03060a1508040303110706060b030609090a1208040602071b05040c0201020406080f090c030708 72
    0x15401050aa00b200d400d0b1400b05440100e040180e02421503100c0852050150040340c0e950001610044465038060910282c04290482c01c9a0204044241c0c04500c0d002c540748541c1400940a05518050002070b01c0341c0002490304c210441300007042582103c4001c0742d40c05282c0c2c8013101d01c050400110642524846044040380030031181440462507103041e07400d03901502c1d07001c0d0090040d1800d1007912030280c0340f00810307107050207030180c0201022642c50000e80352482805c8095601d928001041101e05000f03039000f518803c00c10940315504c5c0c0e07405000b0940c081d8060070013180001d2851150180d5228900c0c015003000e207400004551050740f4001140142001c648201c070a4845807100d82e00c2c1c05264400400400f40d030451003607454011101c11303500c180603100040c1801d4054032035910002c008009984140080c00b420f11151900d0301c581d40c0c0c3d041282c4004c5040c14241500070f424650080c0410160603110340005c0e203030440c104040314100c540642a20045641d07410046d5840e003108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 166175944 1250 166174694 166174717
    0x1e040f090b07021b040b060c0a030c060b0a05010816090b1605070b0f030f090a02060d0504031206060e0402131a030106030b0d0309090e1005090a03020f070e19021c02 73
    0x760041950780b840040d4009440014280300050540340c1c10400009103000560030350800010300c40b44000c4407040c0180003c183c021f4961150742032851800400b29a403d803901403152501c1d00301840281d9010042c2a408001400b00100b1042c044c10180ca04299a5006119060b0001500d402d80b1110030301046210388a1811109440c1d2500130f02550f41c02450b1441c0c0c80005d06100180101443c00d8100d500003540c8402d039150082e198020a6003036111480d210001600d0318184005c140e400350b4904c3d4010301c42d11007081050709051000b0121415950410320840c0c0110f103020900c0b00d0318001c4001041a922138560801c0010200401c6d03030000d2040c80086480c2c4221602075007084030990a40c90390694824942600b8604020010644c1c40303c88001403043d10a06130320100940316590040c1041c0340101003181151130f00902d0034a907203441d0421600043d00400600809021058000c2000c20030b032a806c4404410f0311009005180440e41d28560107442c0ea60080a10340c0100f00c4101c90 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 166177194 1250 166175944 166175963
    0x7020a1202071802040812070c03060603061a0906010e01030917030108010b0a1208030c160c03060501050f041404030c05120406030b040c0c03020c0f1302070602030919030203091e040f09 82
    0x1402050f504034042c40c4520522600050344c0581d038425407070000e002c132034411107100c645c0503125140c0c10225a503541085441034bd40d280c1c0d000c00c5007480306000c1030310031040303c40e210305142c0300000800c103822418185044c035440c3c102c42420080100d441c00b0465400700c56080d201e40c0d4501889000c0d0a0b00380e583c0d802003410500104401d490313650f0780c107940303074200e10660b10791f442d80c800603050b0f0392102001000c071b400c100c4017440014003002d807603400a40c0540320100d903d504000030481c2210b805140c242c404c2d40742c510342c4403d22030348548182d0b002c3e4140c201592240002d0501c036091802c61000b81301031110000c0d01003038198041d400a0f048038000c1c3e6040083c4445040b0590b20303a544218064050380c46034440d20030318030381001c0104840c0303800b809141c50741900000c03c4e01aa04261822105560080204400c0e158200018110040d42d890407010121440d14060749900c00c242201d4012608410700b13000380801208048400308002c0c00c10080401e0f805944070003020f4015048442418 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 166178444 1250 166177194 166177229
    0x20a0908011a1905091003060e0a0506011e05100210050109020903070314010b030307030201050114060c03031303030b060d240303091701140103050604031d031902030a050d05070c0e0f0a0507020a120207 89
    0x100020803502e01503002f001064a170342004207042401f601303620900d205e00006003010645445084411300d120340b0b00d400410751040c540502c24141e54058115911003031040c040e20f222035800003840401c032608007507038103c0006920100b501400001c69000c0d0988000251070042660560065048031849100241c000c0185e8081004a01c106c044541c6c040c0d20500100f00c55a40500030114054803a040015070080c1007404a02c1c3d0740c2003035051548642c4e4034000c1c402e92090b110310709070a100c0c0700d41461381c0190441d94064130f460f800340514001c1054228810524030805d5000302160314400c074555403503681d00d1030040c0c1c0c1d81a0444040303000036204101040000009110b80c280503c005008d0301404298141d2041c20004c2601c050341d15224424080020820500205444070456500c1c6c1d0340c0e41d02c4070305121813052096801108807414175010000080c5400042c00d4001c60741180201746605c80e200101d1500140c00da01500790303c00303003218980301500061407100322a48507144e000707600b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 166179694 1250 166178444 166178471
    0x30c02010209092205060108161505040e0a02070f0b15090609070c15020307180f03020d08031f081c0c0203060a1d0f01020a0908011a190509100306 65
    0x180c8040641182416001c28058184481c9800c04003074582c4d4402002816510740529008081e400300903190041c98030001d40a0340c0d0660b44015000741003043c2c1d20740446150090880c45284103800914100307102180d000b90040c1c04032091ba03900035103800b444a14506081d2003240c410359004080319030028190b503144c1000c000c807900c40c01004203a01d400d40e50b40502610902c980420840341c1040c2e6101c001200555403000c0c3d40a080c0503940c241025100400d0303007102a02581120b402c10004100c204010faa8540c0c0842e40c42d80c0c48800c01da200d17150a501c21640c6840c03412401c42d0545140c0700030510046c00982c40c10a4501c0014501c0554903070f400c1901e224004610194240c1c01c0800010310301c03600e940201004104410130f41c9144450215071500b40190346559640694000580010040d881341040018049410081080d4440441e50395885e001d40c6030355500803640d40d0304c0301c03140c02c1002c40140700820015140394510702d0040c20002e4825040d002c01c4500602d000204102c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 166180944 1250 166179694 166179697
    0x13050a090915050601020c03011503020108010b0708040614040e0901050403080c0909060d0503041e030204150e0601030c141204020a060c0803042604270c020c0f181006030c020102 79
    0x442c2c101c400280810412aa00b801905000300154150300c01c10800c280940c40910844038400400008402041d04503c0010814041a030042c44c2c0e094080c03101e40d001c05c00440c1154202c41ca10f041042803403084d41c0801050707015a07440203502d03030403c1c010050b41d4074040d085284514441d85e43c6400303541c2e80000902c0d40d4000d120010790007070366010000391542000041e00091602800449040079900c16014106038410070130f00080c0d0020300d10420031401d09000e1100620350b45042c840090341000c1041404900c0204018109500d840001c14168041c410b042a00074030004c1c421b81c0d900000d209001da400c41518104d004256210002452620518400c203886a00050481c40c5440741e4580440b220148070080c0000440c00b207120b405e40b00041e0041008004100044101c2420f2089003059110311100d01c11202f0304101104140a0b0b01165601c0c0c4404119407200d1030f0b03110700300812890f41c02140c0540c400020f00c004d00c03108003e111780e0001183e40d107a50070700040401d40c10881c240e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 166182194 1250 166180944 166180961
    0x201050a020c07090b040f020a0f171b03060d0b0c040302031212010b2113060b04111c0204080a0812010602010207470105010e06070209070e130213050a09 68
    0xc1e00700203c24041d1003100d40051100180003072000c80c0924408455030120ba102801c40f001094040c1c655407011a0451404100d4042c0040c82221602c1c0c09a0120603100455000415080f40003000503029528092501809078005500c0d481501c2d141241000940c41070105074464483c1416010310445802c04a401d03086540102c00800c0e4a0400703007044582003410b091341016102d007034240f20591183c90380c0e44030312003c00c682c1101c2d83c014140201210700d84002c0c2d0b030040741403034408562400c2d031404803618101100819030070100ca00345450001d00994105842e540100040c150070302c8a04006090a0790035804018040e9988500a900300d2141c0d00c0014408440714a5064001000c440e1a10110443c0006030361005103442000c00c00740003051140300b00b00c941c140103000d5540e03c0b110b10640c01c9004d85200703251440d1a00003610840c40240340c0000c02c0f448040c1c00c010f03a11201d01f003411540340c2000c1907440e0f10100d0040948141d003070195a00985481a000035040c41038040c0000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 166183444 1250 166182194 166182217
    0xd1d06040311060304141002030106030e191e06091109072115030501090f050c04060612020a030902031501061d1003050408130e011404020a02060727060f0201050a02 73
    0x2010350b02da400748841a0402002992443c40080810650340c1040c443d69141c03264440006927298102500a811948581441c0b425980803604041d41c0c203090b0240030443c01e80182c800710080442030030840a1810700b90004060300d0404400b03108100040400c648801c0c01140c0f00480759480c000203c4110203070402412514424981444058205920034009940000300302e04200d80c0f207860303007400c0d20400711013154100303010030742102846000d02c02120a50070849061003d2840e005d80201151030743c211428100f0360029441d03015a0081d0f01201029038050300340c03001e04d43d44041c8407165640902c1500c1c045a8a0151208060119a000086000010959010904040340c202c0c001c0c240140200d40e1003004008107182411412101c100514022a019101d0b6040121080340007080d00d15080c042c50040c4242e0802070340101d00103901100911340000c1c44d4400020450704c05110f803004580c01100e1000206010341d000c82da00c001d50500781c0003070005880e41c415800892168100d04c02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 166184694 1250 166183444 166183463
    0x102030309120304050a0b01080c01180b040e0a0204050a08060f090619020310050a09060305010e1203040206030903040308030a02030603010e16140d12020601061d0a0e0c07050d1d060403 82
    0xc0d0680082d01c040c5030490f01030300c12150804169074501040e80700c203030001550303071703000454040c00b6603400344490300220341401540b288140751000d0780441d800380e40a140c400319007040c0001c806850b83d034103840081c05c0090480e48255504e0000c9a11a03c055403c0ca501c4094800054003182c030000d240c81c020650078149080e48800007045000941002c1c00d100d1003502c3c0300d0000145941c034164444003915190500051403403649c03400500f1150030740c9c84c0c0d001541051407001602c58000b0182c0380e00580545501d41d881d52135443d01811031285030002000b1034004010302241d60807507030245100d454150001c122040b4884d5609945196500b810700d4420a500740074808161000c0e410300300450702405800d0b555000d96201000000e9891042c0010780c0300f01300411203194084a480e007501d844501943d2000400400300d2444800b6000320006142e480307012611901401c0200d4460795000030649002c04007145008180c241c400485101d215038240d07100e092403a16808450481e035104140d00d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 166185944 1250 166184694 166184713
    0x5040804150c0204110a0f1d0130060320400c022503031416050705010207051203070f1b2409050105090420070b0103060b0102030309 59
    0x320340c0310076140803400c110400b2030002c0140c60f10301605e0120700d90080c4440d10b9120f40361000380042d038045500c2080114011400045904180950715021001e280425000304a040f01c05140d2070407100b00481c8048940354041c204d00b5551104040d40e21800000070700200103088141202c40d0f00040a038031040c4c0ca808920426a01000e401306203448020528048440321800d055060003002240c06050720345a94015440c2d0500021840740c030000c00354408100001000b049040b65804028241701e00440f01080001682c2c05440c0c030140044440010345403c1e01e840c0f43c0b40e01c200d105140c090310172810080303035910300002d10700c05240d0240001c505044064440c0d62444555000c241c80012107142a134801246600001001d0280f400305201003220b00c0c954090300b05d28141c3c0500400c014803d040c00260703817120841300500d030100c0d804980080e9140201034052003411001e180c5400c00a011401c00070950710b41412039000e51410014084250010b81c0c41c1d101c201c4160003203410a4011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 166187050 1106 166185944 166185959
    0x10603050106120c03021303080909010807051e041b050c06010806070804110f061801020115030c15021203010e01031b0311040c030f0504060207021305040804 70
    0x30800e030741c98140e0090045000002d903070324860300e41c1900800c0781d201c0d40550301c41030070700701d0010103041e501d00d0300807056408242001c0c090b5222070000107000320040381410481c0c0d8044c00800f100ca032031260100782c842103c081158803641e00d101105801074540c81c0c0d0400a4113a40b607256541d0580400301d4601101640020300e01d03031200b0100040d45a0100810350003d038804020150402c2c401d0000c0c0350b204410480640045020038060b45845190740f510307e41035801c2e00200300c5e603074441c610f8089124680c0009460098604410800308461185800e1425400c1c81540c160503619110f0178195802a40714010502d03400006100384036804100b00b0707070002440d50b038003041450342d0b07107410110070901030b42d07446203641d4000c9901041c007030b8101441011020f201002146800d00d0000025048010168040e5a12400d10484000c00707100701409503402c0003000742054a04a035 = true := by decide +kernel

theorem cover : BRFrame.Cov 166007194 166187050 := by
  have h0 := BRFrame.cov_init 166007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 166007194 ≤ n) (h2 : n < 166187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
