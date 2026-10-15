-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5527
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:09:28.18019+00:00
-- url     : https://prove2.me/submissions/a7cb434e-d5a4-45bb-93b7-1b7bb258dbfb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 993884892 ≤ n < 994064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 993886142 1250 993884892 993885001
    0xe01021204140712062c12070c031b060305010609050303120405030405061201090501150206160e0307030c17010204050d1509080c0a020103050601050406200a1407080f03040e 77
    0x60754100f21103051a1b41d002c0e441d2050ba40e554103600605650350855501119070000000c907012042c0040192141c0045400c2036840022940781408100c035070f8424081e50000c03a1a0400218510703200701c00c800c013a140c01a001394a8500ca080710031036418401402200e29110401c0086142d80b80c01d0050701008141c60500e044550406e401c91050301c0050f002440f1074070a000b140d506081d40003c41540203803a08041200c20b5031618002c45040001c001c0d41c58140c89000000410401000400c8003250b807000f880b6080c004130720300c905081c0c0c8128840c680d8415014540032020458508808202008401000840a000340e4604010b41c00c40c841d11305e910781201781500103650700345c02010380c0700c0303c04d00c0d02c0c1c0e180a0030610050001405904442c070381c1d50304500000600081082611036183d008030680100c00030b0041d0f21a0b0303400c098080c03009140292007480d5084c0c2000801e903400d80311807503140c01150b0b8448940380f1803070b070b01d211000c21000c4890541c480c5400510301e000d0004031070715 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 993887392 1250 993886142 993886151
    0x40c150504080f0c0a0504020a0210181106280203070606090c1227060b061207090b0a0e01120f09050c0a0e0118050702030712020c040e0102120414071206 68
    0x10494105200250f441c1c146801c44184101c3c5a134615040c442510000ca80041e1110f0078818128600001020701c540072501d0f0a106204098042d5a14042c1c503100d64603a000390a0071074280300c044e0141004440c03014010b1400b41d030f9441e0141100c412441c0341481102d0519440d0b80b150820768519910941c0c8071a42c6c0c0c02c40413030300e0390301c034607001d03a503030140035017030007502c0503064240104102d200c00741c01d8011210607607400b0045107801044030044010840c90300c45854100e0071a000702c0595100c004034940007000034519001c0350a89460003015151071a042103400c0c01982da0300c3d041038015034001d42d10b05045a102905201d0743c411503006000811150114030140810061030b500105201082c0304010000401501040001c40d40d61401c003107000e0310340ea2801c0e0b01d517001d4104014583c208402c0195030541d40010840382000c800c85052010b0150710480900300c1c810041070003455544180090040741914414505170841c1504465449558503880c034003446001004a0b005a20f8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 993888642 1250 993887392 993887399
    0x62506060e1f1406132312060615071b061d0a05040c03090b0103061b051603141e040518010b0a2102040b0703020f010b01020312040c150504 62
    0x6007451140d212442100166010010104512030700c10740348540994218000c4a0141030740b1500140c03451020030720315144446490f000c00a10182c54859032020700c0d031410611081500d000e5400350b000312007443c0601515240c40c818005a64220741d80360307034844c2c8104607030b600241c1505080c4015107208610202883e040c050001d01d1000c2000302003019030804110411180e8aa007402c070201c41d02110006002909000240d000d8a43c1540c098000156500000f06100c003980058843c0c011900d1440300d40d10340150180c07102c0c05581c4c0c04030401840d0452040c006800f480c0018081610400d40c1824134508258802c10b42161019070f1b130708400007040400c03850a1107007481c1031200204440051642c1801415884c0d40a000d040c001080b5034465200c0f40a4034281000052518203481035645545540c08071680745c0c002a0114014824000400c030f8001040c4980380d00120140c0c00395107400701840041e940703018060030507074200d0201c1b440020300d80807005600b040c401140d00c0f4a40c40750b26 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 993889892 1250 993888642 993888659
    0x3110d0c020106060f050f030a0b0604060c060f1404030c061e0b190b190e090f010608090d0909020706021b0d08090d0915021009030503060f0102010e0a0206250606 72
    0x1a13000d80c0500c80c2036284c8084c802d401009a80c0c3c01e1032544c1800791a83c1c2c1c0c0350074440252040c102c0d043d800900c0014045521907104804036191340c06100140321501c400d00000302100d803401803000c0d020782202d002c9030010b03100f0712003281c00303a0141e64046001140c1803005045040e80c2012008400d035034106061a0f81001c0c0b007202c0444d4845100403c6051400314003480c54814a6142002c3c1c20b001000380c4100c7e40248005903035101d0203040707000700745400f00d00c40026074000e024060102c2d5081000402e290400901c000b2156015512030183c02d01c2c00d804003000c1e40010340c0451780c2c030741c003172200c150303650000c50b00c02529441c410000c017138080e005035002e001100041c24186103600a01c2949501e02d8210720444211070f1103440440385241115022800d00c0210481c80c01e10b80c1c10101070360145940500914001c0714222042d004281d4248010388c01c07141040e0182842d44c2140b40c642c0c02618092015282c01040c440810a00c090f0b5642225010304054408031010707580d0b41d100b84240310 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 993891142 1250 993889892 993889901
    0x201092a0602240c041706061309020a09050a020409050c041403060106170c0d1a1f0804060b0d050f010903080105010c0209040b15060a0e030d05210703110d0c0201 72
    0x30a40050414051090100d403c04090f8200c4814401c01c40f03804500500c0100b0111001001c0c1c00d02406e8041d17012003400c645441050303c0c1580300300001c10691040b416184101d41d41c0700c2d8010000a040b034500044030019110040c40561802c0d800d100001d180180341c025148200c02d0700c503106544034105090101118801c00e8141d000b83d101c0740062200340e070400b400d00260181e540300001c4642d142228254984640b068070180e448c00c08070040c01c0d542c011902e004040c001116040700d02084100c0c55103d51841140400000310801d000c40e002c104264007802161402400b10241c14010380c80b900d14210100a4801d81a07540d00380c00d0b07050551202c1540d016250910b005026040190000b0743c80e008007410150540c0c4240010600e80d1a20107900401040040d02300340d118886448007410b140f082d6000036019015501034580b03d07902c20400c503040d254840c030400d40003800802e02c0c07030903c0c1c0005043c60245070b6254240d08140000b40c015181ca0741031142c010030440c2d0414002802d44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 993892392 1250 993891142 993891149
    0xa02040f090c1a13060305060f03160513020d02030408071b0b040303031e0c020f100b0a17030d050c25050d030f060b0406201b09070201092a 62
    0x349440c5007440082c0341e1294101c11190007255a410000d400f081c402e0182c801c002011307044400e204000944103030144c111038480c001c01c45d01c2d1301104240c203080c5511489180c80c103e501c8102c0c0d0900340503d2616424601000c900c165005080c402070000c000100d034001d6030241c60001d80414480100851011040800e94080542080340c3d49815001c0145000e2400014103064480070450b50003d001d0281d0038851b04224424454511030410294543c414030242c04824004c030b00000140c40712600502c000300c0d00c080c000e40540c62500705800b440040d60500c00c2194041000b40c52400034007070150f5401100c1280c1c6d8140e40d0815100300108144c891050742039010018480c4801041e00481d030010201003070308020030044d004000050081030103400001d96183c4c003080220329281e205406007040c0c0310340e03207020704c480424000d00d40c4e4595507407003034420320506404601101d0904c4240103801004500001c00c0d03100099440d401e519404c980d00a40030141c1211814009540441c0d90008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 993893642 1250 993892392 993892421
    0x304061b030603081207030f09080903100b030a110a03080315040b0913150902040219091e060513151e09050109090e0f03030a06140a0506030a0509120c0a0204 70
    0x80c2d80ca141c0d02c0d0407960090080421000c100c1100140031103010790442e03000ca042e400400c000b1010145000041c540200c02031900a00c1480300703102d00000306105a054004c0014010115003895544041101d8030300505282c00c0304030004000000303402a8095400303040c3d0b0f036450b4421410010305201c120303120082c2440c4200d03040800c2c03045641c800100c0035815a04a22052444021540c012000d40101c000c02900244001400e42044010762940c0d01301e08165561102c0442d5a00c0c116079405105200d00b1030605240003040003854040d000600048560551902031507a40b410714142021005006c0c5002c5202041e080803000503200e00300f21000c0050611555403400c200c002041111580507012269a558811450f028010010028030303900503c00c60399a403402c03d83c10005000c8510601d216843c1110443c8800e2410303003c14000c0d6a8041c00040c01c541e41e111501d405810040c28030403e40c041c01d0208130b80d10801400402802400c0801020099054811f20080b9042a03002c04130 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 993894892 1250 993893642 993893651
    0x8190203040305120402040e030406020c0a05040b0102070e10030c06020c04110408190614010605071406040305030403080a060f1d090c0a060c0602040e0115110a020616030c02060304061b03 83
    0x280d084401d0300d01e0050b009a01c240681d0f921b01c00f003802400d4541e04012548004540040c1c131542c001583c4081c203d0640c0d503440310039500e40500003568031140000c1e0158001041c01e02864000d6401e4960143c0007400500040317a0301d880f01c58021205810640050f000884282602c3c1402c0c021041d069807841ea01034901854080a20b80764000b50f014140e400d0a07903207441007804083e40025050001183c0e5108880d40c3d5000c016004c0e43c440c0e00100c0d8842c802032a14914910b021a2052107290143c90303061070760fa100d9404441c0c00100402c9140b201380e41c0c0e0350115000300180211000351900c0b00d41c91008500c62400414100300c0104407105650020320f00005075160310b002c2d00c01312070a9041402c81007405d07142c010040e0081f40c12950341d65081c4000018001c1d15803030014450076454407880b010814070035989450f08420744019401041c2001042012058400d0071a2031a00a00e004508200c260340000c00c15401514251b48098a41188103404502d2421220409006060410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 993896142 1250 993894892 993894901
    0x30105060925030603060c080412020a1a1e070e031b030a060231090c26060427050f06010f0303121d0708070b040509060607020f0d0308190203 63
    0x385580006004004041144401c840358680603800820156901c00c10600145550307c6004201030411035065034451440240481814004240390f15525003000d40c07020002a244190f840082e00540062501200301d484c450310840112075003030041c502691251850841c1d4000c041c074060b0000812003120f100c000c00c03003210341e800141d40300d05503500c10005030b02c9410a04501c000d07081d0400c02d403d00b81002861540d40c030786510400409458407081d0400c00c0d540c03903080031504803511090389041d07840c0300940051848001064a507100700300800104941c5840c0d904c0300e0703005000d13551b403055902c0c039404100304008046c4440340c540d150b8100100119031420140f00a00c041c144009400d001c804000300041c03220300c3c0c000c1680c011600c200700e000e0017001e03010540d8a21003403107403513900e014000380820009c015500701c804548004020b0000c94803500c081040356030000d14126801045040c020311680c80700850315030312a0203916440460314005008607011031091248144840c030400421 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 993897392 1250 993896142 993896161
    0x90a11100905040e0c180603160b070311030c0102070c03060e03030c0a0509151b0c01180b13050d0b091209010f0c0c0801020f0901020f07081c0c12030b0301050609 72
    0x1c00c5a40c12035000c0b8001022102c5642080c040092071030304a145a0710400c03040c009802c90b58047c0b1010350440c0c902042000350032207812404e014071060100704000e01c8003c05c0c4200c000381d08030302d040802d07a4034041074480c006089074003a0904a0f1940f100302d2040013407101c42c0c45260b40c6104484061841c501e0f10b03981e920301902c60070341d04000303020010078141cbc02a00c0300200c1c0d00c80342021140e100d94480100351142d141c241c031312085c04031a00c10b02c05d80310b000c1d5105240903003c2030441d0f120704070058140b11845181c0d4000200d00340c15031503034080001d9141e03942495044940d0044604c48841c0c184001805d003401e0183d007120320078140030005243d6503603101c0c09902d50b89650b8900007400038100c0c5481c80710402107500c000101d41c0041841824407410308010102c800c001d0b022618050145040243c450081e4811407150f500030302c100307989060303088009041d02100d83c60700004c000f41d075036600d61444e2103516804000a0f41c40d43d2100007810248105500324008540c20140c03880c201c00c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 993898642 1250 993897392 993897407
    0x150d0b1e0f060f0705060424090c0620010612021e0916050702090702030301091404080a1b0812160c0f171335060c07030e0405090a1110 60
    0x140034030b10016007889001001c4007911351455201058031503506041c1480c1100c092452515039038500b100c5410100015580b080b0082c40380c2c41038010750345074500181aa075810304042d13101450546c10001002d205401e00c10000a8071610344552940f110a0043c411222050005200000401503c0e44141c0c2d5030724030702a074881d420400030144202a16800c0301d0074000d0800094000d00c1042c2404805030b004800366041e201c0c843c104000c0005103c2940c1805801505c000c2c141000404c80d04032414032a000a81c03c941010311814124201c0740e41300e9509134440c0784a020352400a1050140100740d00061010300b14151900c0080d403081521400c615184020b801040007480751030444040b00c1c0001a80d480d10301034400c51030003070f40c0d485041c041b0049800303002601c0e5149960300e5804001843c0d980c001146018001c00c000d40d0303020345030003080d402000190240562069241d14640e103038000d03240f003a2107100150868000e1840c0c444016a158283d9503c103a14165008108a41c007a65 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 993899892 1250 993898642 993898669
    0x3031103091c170a0603061a090612011e050a110c150721051905161d0a140103061a090103050c04030506091e0105061c02150d0b1e 58
    0xc880310b0802806041d0303148140c82c020f00301c1c910f04107010052642801e03481403081700c0c000e5500740000c80d020742c1221409030484910715400280640803030000d050448242112481d560000030302c44442c43d201940710150300b103040050300d44640c200000c0443e40d001d070060108582c1c2440d81401d0071086040c2e210100b04050b03000103450a40003071300e11482440072241107601819424020724906c640103002d0101101d04090400341034664800454242c0b05062244112a543c0045003040380802c45015292203582c410b94503518000e082075640f6001030100a08004c010107101540070070014041d07c1d12070780407150750800d00100b07101c0c40041000300d550388142481c00043c141d032800c1004081d40916040505540b081c00b08100b200340d40099410f8100f200502030000050200400e03034241d85007101e460fa0000322001005291100d2101508122440104004150104450810440c1c0c0040e11103403600c40c1c899200e24a00c0c18551400c1074006000b5442000c0c40380c0740c1003c00d5642d1409103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 993901142 1250 993899892 993899923
    0x61109060c1f05100b0a090b0324100e1302040305010513060e0f1b012c01080114030304090f0e060f0114031216020619122406030b04060f0b070303110309 68
    0x6c2d035040c0c43e600c906144406410003002d010b0b16400c0c81c059031a4004052240048646280300c02c1080c24a003c6061540c00111603079032100b0660800c0500c600c031030060100c40d083d0f43e005d10010000030030078050b080c482c1e8102d0071404004540c1f424010242e50481000f000035401800d40d2401d400c00100300a00740106003a08802401e03408001200c4400f564548000140e40b0303240c08004004100c4114907070958240e030340d009c82c1c1e600c44003000404a000d265041c5d040c1d00400c01005686d915800030707852003060103000502c00f141d1444050a04904803400420901d280c40180016805040c041010034801c2d4010899082000a043c0481c440d0035144104001480004011951018110385a000710343c0036809950f2030a0341301900103901d81c403c0844007400c0c202058040503a810403178044d01c0d2a8040440c24a203000b000b41c0041c0380580d034080e04603869107404038410840c0c0e20640000c1440000ca103645070080d0034004e04991650b803910b800b031481003041c00745c0320b0700000e0000c006d601c058 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 993902392 1250 993901142 993901147
    0x103030c0c150c02010e030f160905070f0c060906020702061207121109090405120f18040c020a0f02040f15081e06072601080307060b0a06020307061109060c1f05100b 73
    0x214000780c5131140c9581194a0340c4030b2021a407001004006270042100c4809405100ca600c0d0b403c002d54250441074001c0700001d0300703c00194007085107030700035094a40c01820018034080c40d940100300d89600c030300046007040c42d0810910061071f50004489040080d030b0741003000030540b10201c0007001d120703490410384a101c0660111b801e0200c00e00ca100d009000032117149940c2c10b000e00807103201d40c0100e183c5081c0c0d800151180c0015080c00d0107030851000d05c5601400303008510b941c402d001030b20049810303600655110140c032544c01062084443e60030740d80c0c41c584403039441c2c41c2007a03203005083e004c00d41d1001203404036080700c0c500004e002c0c3d821100604190082e0000540d544a2215401a107080c2010903034000240e46280031004100307407805401c00b8401030503844240110b206103807040780c005a1040024002080d07040d8403600b03032480119543ca00d8060070200040980e08094918542604a0100351032071895580318540c040d0944c110034043c034600101c0c1d1a0740421148900384c3c010000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 993903642 1250 993902392 993902417
    0x9010f0b0f0f09060a081b09100813050106090209091e0112141c02160b0a03110412050619050106080c070516030c060908030c031b0a0b0103030c0c150c0201 69
    0x8803010f552800401518160f282c01090f64000c10500e03054840216008840e404481040c8044003100c1040078040c00b000310810100c2c00464500748000d0078100e52402003040000020304c28040ca10090201e4100540c48040711002c000f40300e0800340c9410b0145c65180c0d15038090103074900308281181c0c50901066100d6802e42000210100c074981c0c0e10b0040d00501b0481654901c0e0a515001404000e6080302da00011503444100002010700440701e200c1c2080c09a0f07915188660860110300c544d14640606280c0d41c1c1e42240000380d47c440381124030382c11003010481c03080241e0000303031190b40c81c80340c00b84070a51500303002800812002d010060300c440c0014201042c1700c2c042103554489100001400c8503a0340d0390030501024203207801000001050701c0e80018040300c00000340c1b181d80914a000c2e41c030b400d0f0803e41e44104200d034034101054030b0182c1d400801c027045181c3c4803a802140a52038000074514285844002e802c2c0c03d0304003084040c500701c50610440d50220101e15400d50a08165140c00070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 993904892 1250 993903642 993903667
    0x30e280206070b010f031a2421011422030f050403081308010b0f0916110f07090c0f080403031d0a0f050c120a06051e070c0209010f0b0f 60
    0x10448083c0401c04030303200004180e108071003201c007201d02031075142c0b204000c1d88680c1c0c0000842991448080380052540701c0b006c2010f0307203006801c000001e1140f281492500181c1800c2d10014035180c445035503d043e295074030346011807030642c40310100c428100034000340c0d441c0b012800144a000703030420401d0285070340801c5c01034089801840c0c1092038541c9480301d9510324110001741d13005074000e550038843c030380784641001d0035003450a6070300400700825a5122102d00e4080d4081401c401c4c00c005084603c54022030050080c4140b031807820014002403420f045084003940c10380c03c0c01800300002d00c0840c0198541c040581390300302d5814640443c1c8040b010511524080c20740e002820540110f4048804210312124181d80e00761048094030f041001c050100658450b0040e00e00d6400d070083d100c1c250000d2070a07448280e101d410781c001d032810b491070003481000f1082e089902d080811941d00319801586410803003103004155a410f200c0d841c90810440102600a50061148004021820400110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 993906142 1250 993904892 993904897
    0x308090106030f0b04151109091906170c0108075c0f150a062606090d09090f0204030b070e1002010522061b080106030e280206 56
    0x150000f40c800040005804c11204c0d40c4800e460450300500000095104100c0b03038011400d0031700d5403c0c0313034904000c4038009110816100605204140d003954600046188041c4610005031000308081d250410103440040d207007695403100c4074180005c072020000c0c290340c0210214802c0d000c1c42c800043c003804260010000c0c05641c000a2440d400450902c9001040e460321380d40c60445821a404034100c1d9054034544406190b09034403041c0e00800c0a0020301254589040d422070342c0a42c00040050b91284003e01c50010005281c001c0b480c1c0d06062400c284003088a250411143c2002d0b041c0e89458000140580d05184100000c098841080a20505e01603040d180119082002075140d072602600051241c1007001d0600d00c11402c00c40000c05540c414802d0b244035070010305100d982210082201c11356544c400c5021500542c65143c210031003a611101780031882c0c120b460b110300e154101040038007610440d42ea540c03800c0c0d04c503445807207035103440d566448003045030f28100d444070240c28000706030a407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 993907392 1250 993906142 993906149
    0x70e060c0106140a0b0f040506071502030f04290f091e06310206030408091c122f16140108100e0f0919050c1903020306040308090106 59
    0x1540b8003000011021812042d403800c280c8112810560952525402d900385e0140f80040004410103000500c035904007100140590340c0120310745008203020b4545003090364021180042e0038040c0f1010310082280d5102e0110100190085080c100241c0000210701803100410744a50440c113071010440b2040140044080c2002c0011000100481c0d100c800303550710810754180d41d14031a80f84251100c0c880c0c40e0035680680035902e05040b00c43c54650200501900701800c140c1c0c04000411008110707584110084580225400905162242c181446480d0a06186030708060240400649003d810100c032484000c424140300d807407140c105218a03038600000300c1c1c150380c412082203401050b1800031034071780e081c0ca18099070b5120a070340c0c450020015045141c810030402240003000318000c69081c3c0301240d4050048401c603002a090b154448241076030030a030036246504820b1040c9002e0500c4c2e481e02c007410f881010700c0c0034032500e994003203569644001c101904110b6454040f41284c4020340060004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 993908642 1250 993907392 993907417
    0xa080c04200a0c110108011a0c120304300207090e01060504060e190216020f040906020a03060e06040e0a03110a12110609210f040e0a05010302090a02030f070e06 71
    0x40e01c40904019040c0000c0d100140d4030700c1381d00d0850042d0f0398418049181620701144800c0c50100e4001040340140e0440c1e4640d458038016034441c0d0b400d0b003d00c2d8000d140300d80d0181c030040004205000000314841603121812520041171001c0d8410309400241031412105032040020b4a200d0301190f460051001340c10940d4018244940022086c021211403405000380000a500e207480700c4182030101e01c0380c10320400c0190300003100000546410100c04030020390140004c15031a0751961508103d070712501c508000700b50749000030b01103522504130b11584060187d40800c0540300006019a84a41d8a00003d080203424070344001040c100344200c5500d9035000a8811180442d0400070f03001e03200514085056105100c0050340800740001e03d50924020440d41103202001503008481c01d600c0303040c00005110741008002a907520352140360303200381082e1070001240d5040d0302c1044000c1703802601b44030441d4014030511090484902c011500850030b0305001c0810045a80810243e00400000914 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 993909892 1250 993908642 993908647
    0xc1d061606060602010209010f1b02221d190b310b040b060f0a09020a110a1115040b0906030a0b0405090a0c0f230f060412020f0a080c0420 61
    0x920ba41c054018101c80030027606e41c40c074018034024003180e03955078045100000701004520a800f40c205007139a1701002058032154000b1581007900a002e0714078050542000c0940070510151342e4805002d40c00d840041c50b0003406090005031145851182c3c09040454a228480034801701402125220070040c0e030341e40c1d100784c040c0c0e01e5401e24030581001200c09039154052070002402d24a0080f05021010800400418080c1d00300f4100900940041c039030f100900c2460b4008002002c02000300e020700c2445454540503d059604c144120900205c1c11b0410501080c40f003408403010309003e8851030309094400507141ea4589460102400c001c01c05c440d0064034200078882126030102e040ca032014020b10303000d001e0343d42d0350a02ca600790403288100d4001c0700c0d40010f00325144034451650003035040024080c50740703002100e000580c1540300794807c0b0082202020b41e1411810281c07069503150104131906202d01d86001401034507a2102d4440c54400c80d615558074010888014442c814501039070445034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 993911142 1250 993909892 993909899
    0x10030b0a0c140f0a1107120b04120806060a030b010219030e0f091909061424030705010e0d0320070e060d03200c030d0504090c1d06160606 61
    0x40080022407038100006822100e1468600300500c101c858108010030501d291200c5000c044421000001150311a40184040004c84d24a4480074440301d50052180301d05a08040c1352040c0d04000c84c1c5107050911203039004002403550b425082d1009280e05040115202d00340c7c000403801c00307c0c10101d001e10303e10b1141c284014154081c28040c0760707071001d540211500700d404042203190b020032604402c01444404901007044c00a81240b11b540788a03000110300b0140050011240c00011103a488525459001880404801c8204422915400d4018041250400c40000d001409074011980245505441c4030201841001550180c010040741c0941c0810201040354a810f150710800e00c00541c80030106031a0301d014001c20400c540c3c580c481c800c0c50700c0c8100781c445500c0610440c0780d405000c0c152001e9156101803003850812880c0d951001c0e5502d040c801014115440d440e401300c10403e4400160058041904400070385050454a05440d00c04241e181d11351250742840083c000b504151000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 993912392 1250 993911142 993911161
    0x6040807060e07170c01030605060409090503130308030603190201081810050c09010908010203101703041802120c0a080403030e010b041503050105060d050309060702041415130c090e10030b 83
    0x1344d00d00d901e81c40039140c00b03503130450045003918242c0c05400d034040000c02c41042400d034594050614148184141e9007010400d4071402c06049056006484004000003042550b02d03090001041114820841c205901240d4000920345c00c4003d1160b45c800103d8203410b1143c00e01089103400801006105101500c3c2000030400a50442e86005000c01c4414a0120b101031041c000e076841820545c0308420300320314002800361070200c4400340e10000c3c0010400812000e0b9403c0b1200300347c10410320090b0351600c1c2000314003061000104480d20080b070034003203104800e40c00201d01d80c010741c040c9400302d0386e0280c4685040c010420004c11075072141c40d1140620291400c00d081758201e07030285008025030342da48001e0109000c500b11008100390401c101c3c00364941750440141c406540080c10005103020800c001c42c11a0310161214150700702059041d5019190003541c45440c0000701009001c541d05d81d01e03024151072901c0c014414001c442400040c2a81c8000c0100402103800013a140168102045c0c407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 993913642 1250 993912392 993912419
    0x60a050d03090504050915041104091a06030d0c021f1e1115040c0b0d0f0216120e1e2e03061a0316120c0225030506040807060e07 57
    0x43c24041d900b4240000d0703880304081180b08603080c0300826091181e44540e030310b918502d0440c1e000780d4001c0c0e80e90700ad007010a54169801c0204daa483c140350785a41445420140382682401c10380c07003042819510300c00142c6520780410207080da143e001d1402d04074002c40554400891600009101c482c00c00022941603200d000c99401020010940d408080a6480e503071081201b00c0d00541500c5500d6010010151540d00074108420508000203c2d540390307404031426039000b1000120244800e4920400f4807000c22202c0498408500700300044012820101700d48141c0042a14000d00c10f03020600b60301e8036500008000d86201c40710005509290090f904650404a010b050000e80740c6240801c1e40300f4070f2550303283e00002c1e444003281190368a810400f04011600746203010001850355504084c166402100800f02d00c54003e0100140a01c900e21849041d94264550001c1d41c101e007000410404103205805c6504140602e503100100e042442c0500b00e0301c5401407042c40786c1c0500180c1404050300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 993914892 1250 993913642 993913649
    0x1030f0b040c020c0906090106080106110c0d030309020f0928020405030303070306080f060705121503010614150306150c150a140f040b0c0a020708010e0106210b0708060a050d0309 79
    0x1140c840e079840388010700c1f6076070209000e24808030f900700d401485501d01030428801c00400400480303101942050204202e00c203506021404686c46004e900304520b450b000301425580141d40c01a16071070462903408002d00b140c0c8641c054440da00e903915020890ba078040307801a04001e412a40c5c1c0381003c0f42c005008103018490307803000d80641200c2a04c0d0342e00108509015001c00c0d601c003401d20102c2842d940b09140c0250000101d00303a44038001040303840a00400e0010189062420040340e10070003032001d0600c09400841a5000c01c100b085140e036680240301094251041e003250b00c0e0501d14031403c1c6083c18a0120ba001960322004200200c146034100380403039818145004440d031100d02185080180030b5030000d084038403000000305901284800750004185a104a5500c613698401c0d01d421100d120006c14040d9459900501c103d00c0c2900243d210003204186114020403241c8410201c13a001805150030016a50040b41241e5521192400a40303c01004600a42140d140150102840b0720 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 993916142 1250 993914892 993914899
    0xd06080a1b0b07170306010c0b0406060f0503010c14030c12010803041d0c1b031c05100503030a090603020a030902090f09010f0501140121180302012901030f0b040c020c 74
    0x1800401e10016032000c1c3c1c0c14095014200300c102151040800c200381c1c100926060411041c442d11402103002280c3e158096801307407200250761421301d03481e411001182d400a500907814172060b64504d1381e00000d018108459026107640300d48410b441d8222034424480d001e8805440328002007840000440284201c9a982c0c041c03480240e9142da18010420040310b40c01108142400302c07507030310201c0070a06442c0011140a803860040c040d80714200c60803003000c00c4040c6645d104100042c0c01065641d040c040d2004900840c1040c4641e8801420741659005460030140c000c07444290341c50180e0021080c60f030303004040009030302c4e007072094403034501080302c41c2c42d155828100c00003424000703441890705944180b42e40220280842c80192030152451244803090300c101c1e0240c0c46142c2045c4200104a880c002d40d8102000702414001d00b03580040d002d08102c90403108202404007002890b07540620803c0c02c000c95400104440c020084c40c1141525800c242440e90b1109410703070104c0e00505050084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 993917392 1250 993916142 993916193
    0x503091006031a0f07090b18120a020118050a03200627011e0f0210050f010f06081006030b0f04050c03010f090501030b010e040c0f060203090a060e150d06080a 70
    0x248400d84c42c004262184408240d401c50280074074030210b0001d2054a46401c8060004042d400100b440684085002e840700d811402c600821503910890004540070050f0803958401c0c280400a00441c1c500c1c440103059072800509680346ca907009036041004d1074028101c0b9200e41d03c0c0c1004219034512941c41140b0789444840d5000c5943c001c0014030203020384007603042c0d043c811102c0142c8078038117000002401d521454080c1c0d08550a07074054540710300c07114507081d601c551400010400681e140c3d0489010701c102e910401c00307503044040c10002190720510700490079085400200d844180e86076000c0382c0190034242080122002c0070300a43c100e4203440710010030a99500d070307280c04a135420b00000306401c40c090010040c0b0708216083ea6005401400441c0e071943d550b031100c402d00702813903114030b0160304081024107180c64030703108110042410f41003084910f10303035200044182c07411002c000306070714001c2007800c2c01d0400c0350702c0305025120340030468890f0100381c10810405482d031065170440a12a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 993918642 1250 993917392 993917401
    0x70e040308070908060411060f0405040207051b10050a0806010e09090d0e0103091707080c0d0804030e040e1f061a0903010605220218060304030503040506091605010503091006031a 79
    0x85c05c40c440c580200070b0481c041e29401c10070a255100c040400245601400041895a240c0c801880307010301c91401803401880208040380b9400503560410b21400c00240da444005400804075000300260b0301d840002603540341e00503250703599184074550304071040300c0401802640001c2d010080c0c04864503401e001501c844011400c0c1d400282c0d008004680300740400c000101220040c0c1281c910580d10241001c180b81d2120340340480444040d00003c0c0428280800c0c9504020925000c0d403050358203004440a803140e80c0da0310343c5035001841c0e61030404000c0301d800740100c1c6d1101c070141c41d80012001c140b2070003a031030850f0768010b410440d109510f4a00c2c0003c5c1071501a0b828a43c00b160700244101800b2504e20a0b0000c0d04440004e40504e00e440f0036035145640d655004605c21440b07621130079100d00301410824a4858001c0132040c1c207920240340c040050b00302c15240c00c2129400d00c0c0007076807640c2d1040350302d017081101e10303104408a08083d4003104001d008821041c1c500d170340c900748180d03d40d075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 993919892 1250 993918642 993918659
    0xb0c0c0f0d021b130e0a1502030f010b0912070f080f030307021c090b120718060e0d020a09140105010f020114130305090a0b0c2a010f02070e0403080709 67
    0x2040712561001d80d1144281d0b8958814800118000c41c600401800c1034040c004410002d035000c400e802009070700001c03104070400c9030151081004a000f000c04608614121001210340c02c0c06010300d102140b030210303000546680709034030304c0c400503c1001038421043d605c003d580b40c407003281d005012032409503021848203050b001040d248910705950080c21460140c09408200c01c00040750841001207019010400c0308075007004019110480e001c640803880c2c50300d4014096814000d40b5401c4814001d410031101d5803002e1105481c40048840c8002910188009060460560701100040d0300b4580039448511542c10418125102a2201500c0d01d03040c0b07101f00c0c200d900c80094882445406800300ea05a034201c00c1030740d2114801c0c14018a0041c50800040c2026150b521070031004070001580300009038103228080e54440b40020894030f184c1040040d02909240720241c90400c40301e110fa60480c240308000d0342c0020140e20084000d42e0629040082018100711444004a2203032040052500c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 993921142 1250 993919892 993919903
    0x60f0a031410110a0c03140a080711160605031509090a0203010b01020607080f0a060330050a140d02040b040605090a0e01080307260c1c17041e0b0c0c0f 67
    0x800c4450084c90410046000c1da2029208281981001501d90181d01464002402440d102c42907403583c880c20315054100414050300c2e11100386c45500614a09803408208400e075605031825400e145071071356103061140014202d2812100d510002001c06d0114015003c114101428001c0d030090007505002001681d07102420b1310700c034001445910004041e11051b41c00d0f030341c00100081c404140c0e00d60340e85400e61000100b1203483c440a40c2c0104280b12540c06044801400c1c0c01d90628a0810807002005808080c0005280c4083c2000281c81095000d140c0d040f240038140510180d92180d480c0c501c010000d401c440c150a0080e408094085442034480080604880c00c2a0085207083d807642e54201160005127011a941e140d050443e940d100c40c080060407103c030702c51004180e031288003010301c044288002402d005003e40040ba081110300c00c24912944076802031840c0c0f414010340b001c01d290412502c0406004c0510840a0203201d89000004005107140c8030102c80400140d242026240d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 993922392 1250 993921142 993921161
    0x71103192c130507020c2d0301060803041806030c03051f14070c020109030b070c030305010e06061b0a0209240103063c0305070f0b21060f0a031410 65
    0x10000340700356420240d4036080f00d5031203150741c4141d8040e0100031010038a4820707803080c05441000d1480e042a0811407101016081200860080c00f280349045201910b83c4514003507203d00d9200390590441a201d02e404c014003d6a0201d0036101240d52406c00c540c4980144a00409112102c825000e035022213000d03040040454130401c1106446001040e80c0c07642101d4012810b00c85000000000b0074111001988a8003a54507142011100b82c68000d04031001600505018049441448000c0c0c46100942c2c45204640e14480094905800d0140c80c2c15001c0c00000c0d80010700324100f002d1180c00200021013150400c4030482c1c080580d20040d070a5801c0c45c090350680a110200c800d04c01c5810102c03802101c1c0c0c4288040e054444071000300c00e0f0892258106070342d07035404140104001d070b94ad174248800401d52064070394108002c110030394030201da011944000e00d5441c80046412031340d404040c3c04617030100410315680a81d076443e2100584182c0d4024000b54000c01c02c985032070484901510604 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 993923642 1250 993922392 993922399
    0x9090c070c1203031b080a0c08090c01050703090b0a0c0309090b01120b06070507090902030d14040909140d0e01020c0418080703050f07060b0a050d0209071103192c 72
    0x8440c14018400b10501e00c01c0c0707007601056120200c40071200c25050303892400b601166120210392a14480d14001c4c0c0700b040041c0c200f0050000c082080501020412020301e0009180c40e5590744c4050504460021854115050b02c1c0310025600010036080a2080c29940c030035198941e9050340d0340300c0d582c00c403030b0345034800d90200e60b1145201030307007080d035600c82500c03c04003c1502d4100055502c40074500310300c94001d4000540c1d940c410710294a0104500c0342c003d0068034100324800b42180e10349034a809103101700700c50b05071603894501c10481143c5000301140941804c54490f0a200000140074840000006001d03000b0b60f034402c00036041c50b0284280411001400c1d480541c801c1c0d94507205540502811307000c105003072010240c4841d000004061040c0501d00119801c01b901c1c00b001800f145550100e03120b91b2810484a005817140c00e022540710007903041c891400d00e075069146003184111000e400070002e002266402d29900448018034083c5c0d1500da40400c02041c0d410180c0d0075850704180d550 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 993924892 1250 993923642 993923663
    0x230108010e0f040501110c0106030213060609090b0a031e060615020c01110307240e0c01121a060a090906170a08031b0d0209100806091b0c0703050309090c07 69
    0x1082002c02c07140640061013000000340401c1c0b401440313005504040707044510340c2d44070b4600300103501c0e051a03502c0f03400e11580004c00c08180ba103031010302034900620440285030703180c50400d003071a0740308074605008580200314540320106034510351380049030949048804510f007250216215400d40d07070700c00b041c0d02c00e5001403428400d070000554400014110401c8984000c11409001640b05680350b0151240040308030a49000042920160742441000b07110660009224100503030b0b1003550200c00d100901e00001e88107440504012444034072030801d6401004c002643e40c2e8650b8403000490803100102c0d801c2007040e4580c80b481c15880d4803908007148951244410001144c40e40d00215000f9121a613407a030b4500313070780d145242c4580103207400d01121940420f00ca0718030b0034020011038140c80c036132410303071a80c0c40c06038000b0311035507805001d007034440322540d401083c800312603401c86105406140441c0c2d04035a491500b15070741d910407010785d809452070b05e0102d24008603020645003602da02210014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 993926142 1250 993924892 993924901
    0x70303080105011101150830041802070b070f091202100305190f0f0e1603080313080d0501090c020a0804030615032306240d08090901230108010e 64
    0x45040d84100b4038000d055607201d1b81701300303101c85102c0700c82c0081006201400c1e004100703004162024102503484800c4820004483c2c00e5009204201c609a0b8035031821200c802c10f44041c100c0080c0502200240681e00040900a80315042100590300c034429640c0e01e07420726102c1d2060710602c1e000d0b0034000e4110054110b10008903020303422540d404103005403440c2c05040c601170800192044a000044482c0c0d45442008007000c031401001c1640607000004c103903004006807041e40f029150311014159060102c0800e0192003604240d41c1d021f90001c4159407225001d4402100902080c400c20642c24600f103140c820f0140081910700b1200e4011494500707203469910f0790405080c500d00c4038001c0080103d008030005200b5460001024204003c03680d0b51004200c40394549074000e00141011030851007210a44c07010054110038145064945c1d200c038000c01d14000d80280074910001e070340008041c00104070307950f08441c16031040000e00c1d80407010312039000042d1031004080c013804184021490008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 993927392 1250 993926142 993926147
    0xd05030a02180306011e0603021216030e03070b0f010f06050a0f0c15150605031003060207020d062904050c1b0a0606060215010b0903031204060b060711090907030308010501 76
    0x10031181882e11001e0000004500001e42410803d0300000c600180c8a802c43c040100c10514080150850341011840c002d01480750145a1000410480713001c0c0c1203144140c40301d48aa0046502c07100004c0032241c0310a25031030b1180d0031120807196402d1010302d60000240001e1005d00da04100c44803911490b1405c1c809071070407500810004c11117000d1102c010504d40c001070040001c503190360f846082c000303401c064402c0a802c8103d40d030340c0300004015091080c070520011203240314080301d0303100e10010b81d6000e0520220b02240c583c4440504180d251902020044181329880c20810b60110703c1c070311031044c80904010803509d0075034191030000402d2064182c200c0200c580300d0449400c20089441900843d40ca00b030a80382682c2207034005801c103824010300700c05440384660151115849940c200038102c40401d699000d001b44400344174140001040a1084507804001d2040c0080c103640d0341e4100b0350500403403000c462550035009000c28800280c102c50040395070b40039603505035070703450560b464003004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 993928642 1250 993927392 993927397
    0x9010e060306010f050c070506310807050d170a020a1401020a0804060e0307140304140102030304050d030510080703030503150612040303051909050a2609060a03021c1401080d05030a02 81
    0x40510307600c04d0847c04a44c1d80d40344d1000c3c044001000c1c2d0700340d80c0f0285814144002e03041d012541002807038542e000f40103501010842405075078003a64504080da419013440c1e64407424025000f000a440001d091110b1030380070807808039050040b41d0748201228035140c52030807031040410b0306000a1036080410700280581d0080d2a0310f018042c212400c0188a0f1a441c651961514907640e440c0d200190401500f11082080c80c41400c0034005181107280030344440b0b8803150350b000d4001c101592100020780d01d00e0308a0740c940150030558200c0b0710740c507200c0c640500264010340d2041a28501c082d0890200e107018021250389840c2c04080d0b610b01e07242c0765010b0700030340340c041c00c0c5800e03401407016500d820b00f000b40f00b1030a01c540a0f600801c42003089050a0448070340c8018400b00d0b60074003822032a03615a1400c1103c1d0703523560a40d4000d58651481e24202d0080c0074100642c01168a02c00c103035909802c40d0707001002515550307070b0340e90320a0340d8550754660740702080000900800e0f420b10014010510340d601 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 993929892 1250 993928642 993928657
    0x803030a0207080403021e10140f0c0a0b0f0a0f1b0806150705030304060b0d020303180f040c030e100b2b050307200306130219030b0a0209010e060306010f05 69
    0x82d507a040c43d80746e43c000303422051200f0265095500c00c2c51243c01d00d26010070b20751648000d41c01c0c181005070301980907aa1512415501c6940e0000000b03000d801d64600300700c0c402a094100c1d41202d00c40c18800e41e000b68440040e150508098107195034859032024074407451070400891400760048a802030020381c0d1000b40105460b038040d130329112105411045d0b00040201a12a80c061544c902e8145800401c8a24048131640110007004554005071000404c50f080300c2c102c00e1140c1c04c0d9414050014186010124110f904182011080841326800d030b0059003810320b882d820340e035601c40030301461021580001c5000c1c4c0d0002940c010300780a080e0402d0100d8007a600b901d40c82700b041c22a0f032542071855004030401c4031009241800425495100d424107a10404118003900381c0f8182202ca02000180e0701101901c103800c0b091940c401c1070320400204008580c000200c0e00030b80390800d01074000b90001b918860104401d01d030085298500902100c2c819a016158142c18003440e803c101d80360b030400c94 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 993931142 1250 993929892 993929903
    0x70609031b09020c010605011107030b270d030b09070c031413050307030b1009020405030a03050313050a030f111212130f080d060e04170f04030b04050a060c090803030a0207 76
    0x1c10101e03040c512800146541c0c1034990010800c21b240000050403001401c070b40203002e8110103000c0c0001034202007007e400210a1101401c5071104c0f01520001e15600004a20603100b02c48800541d543c05400642d0303001d408680005403503490b16825a4a1a1501d900900040c02d0266021000c2c8004018212054a0040c28103905890702c000c80d1400c2c1041c0c0007507581003416803c114040d8069030620002d45031001d006d608081c40c040101f07980751403400740241400008000030300c0c1040f4011070300c0ba443e9003210403600c2007170103070901900900b900302c40a030024400ca035108803594000245100702801c00c1422626101c01002c9248100c0c030081c0918080030004004800450340030071010102501441c50341d640d543c120f10340078048600caa03100141d580484810040406c10b0142200c0500340f281c403c035580c1364561000d5401a204680004001007a240207110610000240401489124190400c87c1840100c02030700c007074116210750840c0794800c0000524030701e0b803500034000051181c2d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 993932392 1250 993931142 993931193
    0x11070b1801090503030c12070504030c03080d29040e150406090f150506010315030308070c02120a03090503010f0204212603040201021b030a080717030f0f070207060903 74
    0x2580c03040c0c10741d0301c00e480501e186e14020441c50f1500091901064001801d403d14a181c149981e850104216803488040c00c000740202d440c5c51140090303001407902216582e010102c199096000c0030b8000300b61001180120f2500c4007038014a0b100280c032407107440f0000b080b8500c039625903940d10f01400c54441e0465030080d640300e4000000e82c03070449880030314200603800301e03017490048001000c91b0144000403092041c507110410209411010860b0402d41c13a1902c081081c105001042c900c0d00001254a031034840e00301e5880170704d07503c4904003080c3d8008900902c0708a144c0d408239400d81c0254014030465001c24031660091700100244245c6a070711807051440341c2c25042451150450220700c1600c1c444a000042104541e41403084610700e207601c4001c0180c100041012a07a42ca810100050901e0320000c0c0402c2480a9019074174400380100c60550341e42d01c2c0208101600200594100a0202c94100803e48150020680308160b800315564075800e10319549407042108065295900b006134103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 993933642 1250 993932392 993932411
    0x51b0102071a01080607082401211a12031c2a0f020106030305030a1e0f061d150d110405070504080d0315060e0102070e0f040611070b1801 61
    0x6803455624001034080040803d62404c00c000f82031600080c0150b04005240040290300ba210076100030350101000d1003504d4282640340140c1c2d115000303910080c460101208a88011192504541040300411820741d0005d10500203000284c52510500a20f9801c2800234112040e03128070041c1015540d1800454007904c110701c114800340b001242220f8900590110384034140c5c02844400ca0551544002c000091071a100105240809008e013508292280070b040d8000c1ca210140131450343c25450100310204000903031000502d2144580c0030104003480d030280010402c0c1040383c1c81080d600e6007010500c039602003084400603000b103003207400b0090b40540e00c4039902d41384152445100303961500340d034540c140240d461410a0143c0501c00301030034180b1008160300e1004141d000c444190529074005541800141d0400e480da4000c0c0c1c4c090040c120801c0751071140020b8050249020f00e408002026901404034600e1003824070182002c803d84000c500a2843c0c483e190003c024090000180f2100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 993934892 1250 993933642 993933653
    0xe07030b0c0d05090c0a03020f01110105180d0c05071a0c0f0109111905120109050d02070906090b01020c240703020f060916091a060d0c09090c051b010207 68
    0x409075048020700d100480c2c601d844014911840b40c0041c4284001d0131494034503c00200704080030b0100901511404a02900356409920000220300240001384864940348d200d00c8010414a140f00c0704a2103070791941b80000b4016070384081007503001400f0380710040c280304450030640c25100f1708164039039081003000410401800b40244c140f9104002141c03c2038a0f040c2010413020344a5400c0c03140307004035225102150701800d40301c11030b141620706005103040b600300f0900400740c51300054810b000b0001e00c007411640c045841016103521100c10130880c0d44810300541200c001a0f20180543c0c4455a910b42524115210404588890700700d40b8042c5108260151107401c407100c03c6000d0784c820003030398078804c0c000e002440d1710040f1030004280b0030081e641041031000309803080f842c05d10340e607507170316110481500300700704a800c0003070201540c42e136801810f400103100e140c400c0b20005050210100c1c1c501028040c00460702a42d1f620300e1309042c000c81c9401d007103400340240105a5942040303400000340d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 993936142 1250 993934892 993934913
    0xe0a1712040806070f0e0d1e0b25020105100902070c050406060c061811060706020c06040b04151e0209060c070603060f0803030c0d0b030c0904051b01030905070501030e0703 76
    0x242c1e9030041d10840c03d0005010303100035200b44c070600500124881d005102e40781c00f102c501c20301d0742204107019080d640c1c3d01e100c0200f01c214400500010880400c0207441002c1d1176003008580400c0e16040c14030381102c0b40480c00c85005031821904024014000c1140c048190060a4594060100502d02554400005048507042d62009010900c040c181c402842024880c0c01100c110007190780201501c0342da0f0340050490203402c82e61003040b010031110240201c56042d5020900c05100701c1d0064106810700c4220325808032011034070b4507810511180c00a655000f130311400402c1c001100c4021300031840010107900044034060308054240100c420050b42001031400030602074030006000341c20001400f000300119088620280d00030030a100807102e6040849402513a45c050000e6181d8120002070b081500c0b41e019150b200069400b03000070b21401045480c228ac5840c4074060490b41c0000041d025901c0003c03002e060354214500411455000b50061440340000005884815449684104400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 993937392 1250 993936142 993936149
    0x2030328050a0e0106050d020f150f04030b01090e03190819020d09030906021207081810030509010c091202090a060b0307020307060b09220203031e07060b010e0a171204 74
    0x31519030340340140c040c2e070a01c40c100c0548030a4487c00101d415030780108142c05109510729029080350204103100c52160400d0303a81c542d0301801201d90b180d949060440741c0110071700521170b80c1482e200e4800e084203000411202800b01c9050103000e1240d441d002514401e0b0020304141c5084040e40d61404031020302d04c010015070888800000d03a940c11400c00403c5000c150300301006552141d60441c0186007000180c945a071703407101c003840e0b0310740c203000e8504040484032800315000310814042c03500c07898140e0001071080710b00100030401c3c8801ea074022a0307034080604c140c08400709140300d00000350400c079039100d80c040b005010101d18142c0d80c04039150300384c0c01182c060006800101d452000c0000c14011200031802c05c5501050364100806000345415030810002030b81142e0540305421502d091013520b5036502d036800c804001c02c0207525100f19542c0092002c903299450103c1d040031541c0240040000c0300c0010705415000707410709003400c0442ca08030744072003407138131600ca640300000d0603500080c07000c2c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 993938642 1250 993937392 993937411
    0x3010e0a0b06060708041403030f0412020103110414011103120412120506060405190308130f05180408030a06030c1502010f06051e0f0618100f0203032805 68
    0x50010609001071101d00280c0600d1049000300b0441010900441c00e4406840c040103d21b001d50f600c1200003880d52040c00c1d41d418020302c01050005500c00d04241005885000781c805004040c1701030b014000500c1903010310082c9502c0e1071408800c551007211102c22002e41e4800f140d2a0154803027240c00c2c0c0b080c0440b821100208580d0b00051250307400900c03204042401c46081c050342c104400014000e02950090600408074205000e0611411244110040d0b030424031040d520b0030740e002d00c1344482c0703490b00440d20b00e4031074450001403030308005500740f0014850803e001840d40311513803105090f60000c2c0010310740b0ba40300d80b004008102e00c42191001000c00740b01e040c540004c2800083c0c01d42d8100350320101003d01d00b606c100120748500e02c0710440305c4402441400c0d0b0300b00c100000742d8071200c0703541c00030381145020400c18a03503002180c0c14400f5a03400c07138260850000502c0c003110360341400444c070001a0010b00c04038918a008602030a04440c3e24041c01ca03c0c00020105181104c1e03007140c1040c01c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 993939892 1250 993938642 993938653
    0xc0105010b0735030408220501090e06030604030c022409011b051f02270307080a110405130f060605090c090114090f031207110405040f02090601020c03010e 69
    0x801022100c0300340791401010488222441658401d0701d003480c0c03403400c10550f40c3c00000140c00c10007079201b02d4010007448501c1c031041d40d8003503030301d09981c101c0d5014480c08252141c00200c0d00f540d8502c2c100384038a40080040089550359501210304240c0d08034102c1e04802c02050b0098003007690585140c80858019190340c0300c8081c0800113180800440c4404a60082041c0d68408900c012980c00c0c2c402c05083c0306003c1010140070084000d1080e8201c1c80c818800c1c103001c2d0034070002c0250482107088001c404481e20a038582d5070301d51704c8024010340241441016034141c40d550509400c0a6484030b052400d09210031074585034554081d14041c0226a40d517aa40020711030b13440c2800015806c9403201120721f042102c0040043e111051740b10150703001180c0030400001a1382c901c80381040602002d02a42e0b880107080c50015802d4018407403c54080c142c50003101c1490409100d0070784582c0d0441c0032500365000e0340c0c00b8071000e450007826082c1103020700000881c1c551400d00035142d61841c42c00c01081c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 993941142 1250 993939892 993939907
    0x190e040b190b0603060f12011103040c06020d0f0c050703020a030f02041401080a030c060b1f090b0306010504060f171008060906040305070209190f020a110a05190204020c0105010b 79
    0x410700c410407150201d1142c90301c0c0c4088582d4682a01380d0380e000000f680c10540440705903000a00a40e0602c90800941d800d00403c404689000c5024500580c4181645920f25803a40d50070b0b619011034401e840300044c4180c610006031845007230390031039190142d81542c0400d07440340c012401076041d58000340e88414086081700c08509040c8124800c0c08841078150b44994101000070341c6031009800e02408008030340c4914014402168018604013900814a11080b00017154140d0003050602c111000314031040700004407080c26400320ba124080580d1081c0c5003505010042e00c8047c800c00c0b420040211040d4640401c800b50803001c0d014802020b2110685441d10710907a1030b00d00010002402074115001344400250028281c0710031950480c0c5000803591002004e0000c2f2404d0854814100e080c00c0307141c015401560300031301401c40c0b29a1000c2c0d4004800ea0010785d1514a4000144968003a42444241068186d4a1100584014000340c600004641b0f29801d60b1800e0304000880c01c00040c490 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 993942392 1250 993941142 993941161
    0x105100536030f060907050409051009061e0b13051e040302030d0c0219080307050f030a022106130b0f0a08070f05090411060d1b09080d030e0c190e040b 67
    0x40750700740c1643c00203040c00d142850312640c99121074407401d03000c1c07901d4072058405c000b024041c0b0707540da440c405801c00c4020524107008019040741d54818120040c0d0b40503c00059116001e00207042c0d0303025101c050380080c4440c0d00801444018150641c450952101c07030392019841d400b03140140d019a000b1615402144800310480b0100100b2400b036504c007001d08510000d400002c2d4441542100c2441e8480d600c41c0c0050344c13244038818400e00300c000000f0030030048411581c09030107103c41c10090070103a9000070b140b104404005965040c3c4c0000c8180b6210110701c0b150300006140e0360041c2500e014041440c000c5aa00091a044403021341c11100381801a10a01c0c0f03581d800910301202e013a0b049080603100c2c212084459614a8003403a40041c3c2c10090641c1604403410009103126003106d0032000394401050142e00d405181036a01802505201841c402d0194141c40100c00e4003824400000c2e00130488142c2d1804d6041301c1d0070303a418000091501f00f54096620450082e845039000385000c0d980d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 993943642 1250 993942392 993942403
    0x60f12051009060f0e0406110c060103031e08090303041101031b120c02030316050c07030f150c1d120f1507020115030f06020a030e0106060201061409010510053603 72
    0x801c1c162580c41381c003084564400c12100d50003a42000000030b8144070100b00c007100b4464035000303d54910076007000008044e4064200e000a80198510f5245090b440e102100c01040603903c56210368400d0020502180d01c000703104003041014100040c030f42c00d03101c212485150f0180c000320080741d03441c4802c554207000740c0a0301314605098400f842ca18500038401c510014011543c1c903003000000b044107100c0d1030007005060040c5400c4400b22285140d03900d4260061200701000f0082c5905104125030103901410380207100c5040407000080d007092030010b110b440c001070410076605100302c215515a11109001c601409014000301e80201c1c40d000d44040e013510301707400d80340308446400e45081010680c078484446207503502440c0541da440b142d0701d04502034014014a540b6039460060009041c54055005400f1624210351041c0c44000301010000749000910505070000d10840d0765142c101e119a004100700c0340085a250041411180c0743c620003514021041141140d00641c0a843c0c41c00700074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 993944892 1250 993943642 993943649
    0x912011e05130308010b03041506240f050f070f0605090715050301050619051b030918090604080a050c031809010504020c100b010302090312031e0907060f1205100906 73
    0x1079041444483d0390040403054140b0982c0001c84010000c00e04000b02c2c10241d074010b0001280c1070086589882030304405401d80c0899003030608550205514a0340541c1001d06039003038a0300e4090424000001400c1c2550229200300e0343c4040010201000501c640b0400740107400d02c4c00141035150906210a40060340c06110310240282413004100b1030b9103140407076000087d401c0303043e400c0400c15201a0707081d0180c203d002c8481e039007030180c0e83e8031108000090810f100048030560345035960a9480000d00109651001041d040000050b01148112008180d0160280b030002d01c0c1c5065240c4640c00d50f0271600101c144d00e60804858185403a00b01095800742104660840c6801114541c0c0d603503400900508420803030312001c004030141e00030781c19218141c00c00340588405490094100c022035004840f100004a8003407008010300001180c440c0c03254807044020010703e81405001d0301c039100d41e891088101310303e01c0c40f40c9203250b049000f15800341c0a030a115000407801c00c2c1d1030200307445082d003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 993946142 1250 993944892 993944911
    0x60b090c070f0f0f06050702061308090622080705090f09030306010e06040f0807090e070b0315040204030804090504150e0a0308060301092f01170c0912011e05 70
    0x50034410450000811225a6a80810040290719041c41c124440c101a6070707002e840101c00100500038040e0641000388180c8456080e10780b203a0b5280d510507614680b0302806402036900f40900e041d1810700703000816110f00c00f12142910104810201c000507459504151855003011008100c10b042c0040700c650080c0011500041910340b0b801c1030340d07907404010141410800f500304e681c042510381c01c00300c0f409424008006e40b0f440d5250043c040d580d40b01e40c0300383c030190344c03070b00d00c40341980c40d40441c03000d041e1001501c64a1450b25001c80b0000002007601c0318a6000303a0800c400400030303240b80c1c018001000191400300366032602d03003099828004110000d02c0c006041c8202000c0c480d901060001885925050020030b680b0380c4000300e80101800313040102140708541c0b404000c440c1d035407a5000e640003110001106103002d200110342002c0d10105030031880740b810001c610907015910240000003000f17440b125510050800c09401d540e002101d450045100342c3c1d40c0305941c40180501a40203c888 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 993947392 1250 993946142 993946159
    0x50c031b1b0402030408031302040603080d020c1902060708180d11010e0109150f05090a03030c0b0703021c0f091505180606030705040b1305010815090c010f0f0e0d0b0103060b 77
    0xa0b290744031188001002d8408d0391f1f4805031124115601c03544500e02840e0003071820798a446c10300d00410000d40c4600020703d030324416241d005000b07151100112605560251102e03040441540d60304640d60402100c1c40000c0060021240c1d254403880140180345000d20b411340b103100c885600150150b9103002d041e50401000907414071801c110080410410703582131811210b10a8001cad01103445004020740e0503402408242c000081c554002c664091250148020420517141d0000a07822407107032880b001c24000003808188144040c9500021a5103511140400c4d500715135503d001c2d400d0300b4080020910741e038074414450701c5c000d240346070342c0032200490060a8a05001000981e5040740388039461040c0d03111038619116072210000800000380c414400e2200f96128a100340d1504141d4810f107038241160b2001540d00310f00003c001c1c41069042c0c40b40c460030404070720200c43c42c0d00c8105c080400e1004440c5454440e4440c0100c01c4030090068414105a506500e40401a40c3d030742d1000b40e01c0781641 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 993948642 1250 993947392 993947401
    0x1509030c151409010e13020903060106081312120212100803040501080a02280509030d0c030e13060816140a08190f0f0807030e090106090303050c031b1b040203 70
    0x1080c1010307074030002c902c030a4403100328000403030740003006481141e00801404103108004201e0307006454070740012810754800b6a01c84500311000035046550384045411201c225001c81c1c40303640412008078203403401000328407100d2031000c00d983c00300494200c0713142e85500700001c0417940c10303101001d800c02102842c0f5040c60500000c000540207043d010301a940010000f00c0b044924249043d6180304c0b200c2d0410078004441c0c060f1050304250803682c007a028516220812030312605019480729415110280080200e400381b20030001d03550300e0a880e4a541d88030206101c10308205c0304003070000300c982c2980c0c200d0030032601c241440b110001a034056a10007005005c2ea40b40411070900003082e02051095103d46400c0c1034810b81d2481c5805450348281c038a0000030311480c00001c0c03070342074080d890700b0817951030910501514138001d100300c90019900d036000b800024490b8009000c0141c40780101d0f81416071a1428803912203a119000700140e014040c00300200403034011141c8003110072541142145132 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 993949892 1250 993948642 993948647
    0xd0b0604050d2012030301030606050405040f080c010b1309380709090507321c090c060f0228081605070915050319080c071509030c15 59
    0x1555080104800381c903c0c84404003c00f910710201c0200d00c001c1803152001c2042914036244d92086c001a1041420300b0740101c5e00e41000e000d000d010b6a400680424462000d071a4044103810981c05c484c0c00b03541341c2070a03111958854019542c0080c0f110800600d0125516107070342c07040034821001c04100c00c00308545c400858240004981e0300e0411701000b4155031000c0003182c1c41801c981042001d54a00014868030503405403295240801c8800d0003800c0000c034418084010244816154451b0810840c4002d4000c07500b80e01040745014010200703052445903603c600720900c58010b100002c05c80040020001d074100840308a440302c0a090907002120188a001d044825440260100d040000c0316480c18144107072491085030840b0503a89541e858032040301c064802e1020012a4a06c6d6040c041b90502e404120707150600302c2038600500549181d590f0720004d400c0b0b07034100305450082c0310001900c2103007000b010642102c190345082c9428110303d40040685d045401150030180c0300d03800c42e1603064 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 993951142 1250 993949892 993949909
    0xe220e0a110418050708010515031515121b03150f010308030c0d0e011d030901090e0c0c100b04060e0402030d0311090402070807060e0c13230c0d0b060405 68
    0x40c82620702045520f4009411024400400d078002d00c0c6100c0d07000000f500c000113501450180b810000c004081d059040201955080304102e180c0c038154075540800c40003641c4130348003040060701620198862072000800307800c00049140290442d48001441035a900c0c00b401805401c1100c1c05c09181c0500740b01e07080480395041400300a02c103240001c00b043c2030300400002e0356401c0d001c40f24180908880c8002031406001026a03a00200c81c1c83c0c14030b03810001000c000d8900003c0103960b03ea0b20b1a03d00044844426000740003403802c4481000301c405030103000c1c4a510440b2180138030111701d170a180c0302808201c820300e504c0340754038480c2e0405220060740d01041c2204410001c0c5404141c10142070910981031003182001940144001090810422110041c081d803d0080c0010004104003c109580300c01130960b09a0f448035a0014009102d0707020381c0305070000015500e01d031154101e4289402007604c001d9801000c244d80200b0080080380c658000c1060480040c1c46050074a45003401040914 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 993952392 1250 993951142 993951173
    0x7020a05011407080703020a06020417060109020309211306050a08010b04060813020103060f1202090108010e0303011e080304061d1008071211120103050613050309040902010e220e0a 80
    0x3042c002030320011b05100300141c04145800000456940350340392070120318107050781d1500106019a0000182c0043c0e607100f500d10400c0380c6006031049900d4a00c0402c0240411603070098650424003040c16001544904940505699200d00342d5039102c0d080080c1004205038840310b0903c074204028843c044e4012511508480c800000c81d10064861005802408440e003040e0707403000e08aa0001410041c51550341c1059009032042e082a90701d8003455402d894800f031102442d0781c010801008101e041290040300d0b910001c80464200d5200c09486040d940700342d00100000b100d0100d036807034005140c0040c0c51030900854a000d4400f425640c0074000c200000e20030002d2182c80e11100040c1c1c0da0b6a0440c6411440c00a600c9960320040e43c039180019000380020f075410b108200c00181c4111464541c003840c150420021824403012404000260075051400c90410840c8102c0120310b40322202c0747c1414001104002454024001c80101182c080c040307120b40c1d80d40024002d00c08102000c0c40880314 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 993953642 1250 993952392 993952403
    0x18061a0306062106040c020303010320060c0303070507021201020a0c170c0106080a061404050a060225140c1507110604050904050a12090608161103070807020a05011407 74
    0xc0390384000002c1c02c18010142c03414a5154034000c0d602e0742004180c00c50740700307101c11102081000c1c1500402c0341c1d00e000c00d000040001007000000c4c143d012001402305415040280b85c58544403181d410981150000d88944000c02d0340401c00d00114900081100c4c0c03802d20b0301c4021400c102100354010030518220201a181122440c6050b05d82d101407000c603601588043d00038414159600c0302c01da03481a5006d01503078114a00032000d031000020464090060390484020441c6c4425034454500940c020780e0340710382e68509480c01d0750311400c031b207864850030310300903803041c185100210496414008007010480c440d00e106500303000801c20034019524a240c001c0105842072030300101046c00da1140c0c2d00082ea02c51603202c20082004000505507050038401e6501c0009202c1110307081d40c07074100c240501c001003080c03c1c00085100503020540c824003441131800c2030981c3c8004034503e05544c8000310669000c000015540154140300700d0f4080101001c4c03904007404c06404001003014059440004d01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 993954892 1250 993953642 993953647
    0x206010b210604060504060b030612030a05030705340506090304081e19150608010b06190201110f0706050606090d080f09060d0c022506031d03040902030118061a 71
    0x2c03511540d00c21006040050001c111503520760f0f030f240c03106400c00c4440030700c41d9048207980b000303800012064400d103807075940745c03d82036031104401a21a40c202c03664007250003150380180010040300600090700c8150001038030201d500075050141c2003000040030004280d00400040103103142c00640012005545001360310b42d00f03100400e460414010910351882c19070740801c52010b00494210382014605254010414560703556100c509035640203503010f90100c010301030100c1e034010405901c80c072282148000586011981466581038002c07680300c2c001c8201c04034810040280303601ca0203401240c11210241851040300c0080e006180c031040c01050200c1c0892101807407a1a00c0030341c1d600000041c10705841c0d0381d02810b070300002c0c800c1940301e500500c142c203040070444500c02040b5a035102104070b20700070641040340c00d030003820460016250b441c03800c02101800890910180002e0f101e052005030352549000c640d0130004284107200c68402e454464104010240440e141d04480079001c0043e4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 993956142 1250 993954892 993954901
    0xd081905030403031b270f062a030c020f03030c063309160215041118040b0402120c1804020109081f05070c061505130e10180203070e06010206010b21 66
    0x30b06001b240d800356a8403208135401003001900068022646646556180003145900e041c1010b8080c144034003030081841d0030705010141c1010070702066642c4001e01117230b161091000b0381501d001c00031105801d54100800035103d080c504660941e101000004e03610440b14010000241103100241041001c40c45281c0103c0e9607a0081c00642412890300c2040f0040346420304142000c41504100c40b0b11400e1707101007071401d01c610311030308074042c64024500780c81554031a401e015850101401d20b204600c1034080902455443c4408520004116603a00c0c001e0308052002600d13031071940e00020f00a810030b216015895680d409110f00da041c6411000c240c680b5118070030b42e040c580030704c4068101410145031414051111040c0c50444006544a107100580c05a480c0110703481103c0040c81ca07000304560882c2000550071501c203400700e5000414161a240d4000303440e180c115030000198900d44010400d03c0e40e01481218018181c000b9040d01e03104070920b0726030110701d413001c910070440119408135 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 993957392 1250 993956142 993956207
    0x1090b011214060114150c0c01031d0703060e01050612150615030c180a0501050d0522050703062a180305010507051e040605090d081905030403031b 65
    0x24040002039070160759241d40c6171580e0b0740005c1c065601c610f0141007166101c0ca03446d007855003258145022800074104074410300c1c0c01100a407114101500c034060755815a0690503406200080095118401c0010000024802c0500b500d01c01032905119150440340e0034009100402c0441041403030640800440c1e03100d80000d40102e00400c43c0101e10758011040081c9583c0c454000e0820041c2e0300c1d01d01d103403103412004100802105010b07050000b1310601100581c0c40b00c507040349801104101c10905118002c004806c844640c030382050707540307901c0380c00d042041c44180d00c40c4003001c140d000b0140041d1600d00c03410181100c114102c0b0810410360702e10045000f03d07040030910245031f00200074812070800020003401600002c010b814a21035041c01500901c41c40c030201c6044450503101c0608280c109030411140100008013581c8a4008208580803414022100245000c058031595101d0030070b41030040486158000c3e649001d040c4003030050506400c11a6801444c0c2084880c3e05180c1c01c5c0d4825 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 993958642 1250 993957392 993957413
    0x22110030803010e060118050102030d09060f0f1407050f1602120d020714030601030221071206021e0304020306010b0306010302090a08010608060f010b0a0c060b060c0a060e01090b0112 81
    0x74042050100012506403108200140140d1003640c40210118a81750780d14040c3c03069100320760141c3e00c01c02011100040360f80010b9140c43c09040300180070082200400d080d01d10031840809869030390031015560100ca4032180d81c1103140380c82c049060900c2c20480542511420b54030b6444240d009461004641e10681000c0951100700c05482221402c850069035840d40787c01240710802042808008a00b000030709941225001030860144a2000f03100000310003100342510702c5802419004201c02c8503d00c0c0c903c50140c80b0740c2d0300595070b030380c24040f1580003010386183c100102400c100344400b581e000070701141515184010310341d82c0c0c0c940b0001079009100e40703100e05c4e41000640e800010302e00ca040d40100201c8400d1015900140e5401040c1c1d06502804d025800341800306000c40c01040d4403801d00f650f000e81c070820000450001c0384000400301d400507441ca000a5105050420800ca00b42c0140203802d8881c60092204180e00c4c0d544001d80c55050040d14070b104000ea40b00814051005c51 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 993959892 1250 993958642 993958649
    0x10302090f100306050f1c08130305030406050304150c050a0f2a0204050105040e030304030e240309010e0106081b04090605010e0a18030e0d021f03021804022110 71
    0x2010b02010194180500a80f495100e81c80c4140c51695481100b818900d07601701c403421034040b203c0c400b0742c415680c503445608140813490581044600c0880001d4082000304040c01c1e2a455882c1c80b403801c1c0c609026948011701002520038140380c1c5001001c3d8010f0280c40081849041c00c0d01c1342264003000b00c41c4001020080005400882c020b4640203180b40c4030300003024000d5070103020716a01e84051005075000c8800082550707108000240209106019401414400074801019645e19200c1e21414003210001c600003004004240102c428091085403517904200700240300030b528044c080351b00c81011400900c080e00401c1c140d412295503550285081a0744900c041003035503141c10700000c00007022074300c84114070701c0e2076120030148803850110f45030968035130f543d09080c840d140b052000c82150158100d800c011008107030551800d10021010460320300b80c0c0d00603103c16900d4840050b540a80744642e00552040103001c00b01102411880030740c0c00e010f180c000d5952240c12510070326080070751 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 993961142 1250 993959892 993959899
    0x813050f0d0b090115150e0d17130504090305040e1005061b0705060a0302030403090e011a21040615091b0507020607050304060c15052413090b0f0709060e010302090f 73
    0x180080380b018103100580401a020359555917074111b0b60b60601c910100c0400d005010b411001c082c20f442e41c0c076927a00400b900c0060b04e1482451540d148046000d9400f00c080490100d0030101d4240a202c4a041c00e09511518120540106078501000314583c0d104041150550490013100111180d0003003040b0740081c0030103096590b90300f0748084000c1c029041503404400050584c04005101040403608a05884903403810b015054074002001c81c20b42e1106e00ca803c418405064108120407950001c80d108500442011544401200c0c0d00740d500340c520380000100c0c42c9045448882540f650004038410b04941c200550348a0590000407010302a400009007144000100407400c154000c001e0b01c0800d01c6841c0502000300c0035a80002540c004980b210a0f081c00d407075513610b24442400c1c6800c04010050302c56030344038903c03076440406e6600000c02641d1008540c1d0511061008620505500c08000e140a0a856041c08030050244c0c41c04940c0d281015008508040180c5d546090981c1180005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 993962392 1250 993961142 993961181
    0x12150506030115140c100f0902062208010908160305040b031f1a07030c0c0b0c06180c010f0e01050d050702210c1e07080a0813050f0d0b0901 62
    0xf602880c034000908840d81002a600041c0349038820310038030a4a5001122002800ca1081c607010004010300e959102c90182179140c540090240c1c84d80001095a1803805d01c2401512550803104d14110b03400d68000d40940c1c0c940f0840e403000c2607000c1d003507039541c0b10340c0030408081f0496400c0c02ca81d580a01c0d00101c405080000600515040d403080c0700d504d02c0d900c88100c60714243d441d0211951250b01c048484080d5004010040000784101c25200311203101c0c16918101ca0b85070b0340840044c0d080300084100b40c2e8442414441e1024484003000e100c40d41c190b00508060781404002450240300180c21f1342032001d1207104041c031703030f000d481aa10b029145001c1007102d80341044000f503039000340c41c0214000b0030b12098082c00c4000315104849510003003000824505446001005030700e18290751100150190070780114101c14184440b1403240d0083c070781e0b00e8071507407500d14116101c511503200901c10609441c4440142e00c908000112164021510310380340c0da103010109002d411844000950001e42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 993963642 1250 993962392 993962399
    0x81b13081c0816121e020a0207030b1f05150c060a050f0901090519030203270a0f050310020306031009080c0f0102310305060f040b0c0a121505060301 66
    0x100c081040d010030307250344425a0ba15a01c8125001190b04089580050100e1603082814481900955860b091428203442d03034852100702c000c1280c10200c00c07500140c020481c20401d11100400580d0040e503031300401d0546038074000d007600301c000b000e114403405841c00316141e482d2201204142d80c021074402c000d0316068608140d6000080a04a0321a032011a00002240500c2014403074110601c0d8008010000f0110b141000a40c144200800b10b04601c000c2080c8e44182602441070b030002c0750782c80d10078047c05602c20200942c90046070131000c1e01c01d603082d078100039507500011722421106810b24016030b640c5806001c07906080170f05544000c140d0030708401e807080248042c0107000014002c000d40c0d010081d6207408609030702c2100507000c080242c08010010103c100012810b03484485405180c10070740e23035500c8600741841260044640389031a420482881594030303801c0e0388000c01c00c20180c940181c800001c0d06818010004034800769490300031603200f500d030032501d0000c3c020040c24603882c0e60f50b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 993964892 1250 993963642 993963673
    0x5010801060611060f040b060a031b0501030b0105160f060b030a030806090c070f2901080d02120406120e01150e0a0f09020a12060612150507081b1308 66
    0x603548180c2c00018070440302c282405034045a81800f0381c51740c01000b035542c0c9650b01c40112030342d0094100f41e802410600c0003c006007902500043e50002e040200796010325010001d411603600000b40390600004201e0240000d007010106006190b2019080740b503419a410500300400521041c6038041c4034103d84802495005030a55100710402c5a01c84c10a595504880c100c90240401c01004c1e1083d0b09452000590500e5541004400c8040c2c054109040c1842800034400d00780c0c0201000c3c1c1081c59240007555051200b4400700e01c503090f00500d0145000303801000a084111544551a520150504c1461080d013014103220701302c2c07901d600c80684450b403495001901b650009905480e1800c05110004070b402000c242540045c482e6000c1850a803610358918820f040841d50ac50f911940420151041d07100040d00e14064131107070719081d42124540c42103da01808075024004298204040d01e02070040c0f01c041642001403242c1c89802e202600c1c103000c00e56030012512801850030301c54040c403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 993966142 1250 993964892 993964901
    0x1e090a0c030f02210a02040908130f031407030809061e1c0b1e1903061517060c0a050d0209041404120509010e011d2e08011d04030504030605010801 65
    0x500132a038560304040814050010603042c10070400e201c1d0407500d020005491f044e8400340c0c40034004d40600f86081c01d00f0441c1c030003900d0f150f0010503000001860a200744031444504512280c004002400194116190030429000304ca02c0f4030310449000512841681400c000400d2000010f41000d440d21070004111004515000000d1661868900c001015140c211420300201001e07086822181c1e103d403060260380e040c1400c408142c0c000790040000018490700c1f40521223508002414802401c000c0071303440c404138a00390380c40581d11420074803001210606c201d898040399828031590b03c2d40f9039903050b8082d005107048a039100d403800003040402c49015408070300c254850130004c07000783c49042082d00d1700c0c000d50b59514001a242c0070b2881c141e500071a80389501550030b0200c2056059458001841582c03d60383c4012a040d0f995403554250848824039038190103582802c2d1060741c10144001c140d100341b02c0030400503000d05404102490f0288007198061030b0040303400d0142d50f8442104ca4082c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 993967392 1250 993966142 993966173
    0x72d080903010b0303160201141c020901030e16051314190605010f0815060706092d020105030c071a0a02120a06121511070c0504050f1e090a0c03 64
    0x9500f0700015072443e280100403182c1064040c100b898030440d154004694001861001c003140715000c0112100c2100380c943c0741004a554075a0243e039880700705000406403020a0081c0c40c00d64001c2c510100d200300300901e070400382c4030700ba200310105100009001004e0300d2403803c140f0103ca2044c083c0044800000100c40403504840c0c0c1c203001d9035130750784011907003c80210700010010344164040340304d034a981c1012540b4554014140b80c1000320030b07102c5108968a10b10b0407240b81d4243d4181100b0a0b012040c99040d0010a034840040e80e0b07882e40010b801444000c2600c1d40e056070000c0c9503010807480482c6240da10a400362030540500e400b45280c402940102c03904102c0c0100030002a04120250180c04156420000c010001070440d0781c0e00c203d4202000c6010140a4984003e0040c56220001510405005d948114072492401f002e03c01154006405019a14104000c000320700403104200039042800c50384481240d61010110381c03d002011400401100c10305a000050001d51480003491 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 993968642 1250 993967392 993967399
    0xd06050402210708070602071a0304020f04020324150d05060307030b01030b090f06060d0818041a13232d010305010e06040c15020a080417060109050c072d0809 70
    0x1510348406d03050340d55610603c60354880751740901d400c18007941c3c1c540245402904c05040d4506241c864400030b4140d030030403520158011540c040e840e40440c00e200030130350819070941e405e01002440c0a2000d585109001d4005850340d03d48011400e1910104602001503400441c4601c15584a01e06000b1411040e1a251040c0c890b8145800c14614082181030013103200030076409082c2300380d0750f5007402500080c04400000400400c1c5e003501e40c580b40600c2140b00813130300d85a031450202c001080044040e24041d9040700d444d080c00c000075499005980b20000c20303950a107441e0f5980e10032400400c000f1002d4a6882841002240e445c0720030301c0300300c0320b06882c441c04c000d00c0070030003000155136511310441d006019540c8017142045640c850240012204440344107680320518140c07038805203540311f40d000d20100140b400503444108000e11200f800f401492005004d9414800468040c0d40259071014040d11490500c0d15101215413007c984407070980350505842000b581000d001a420185c407083c00b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 993969892 1250 993968642 993968653
    0xc08090102040e06120f011b02010f1a042d1508060907060f03060801061d0123100c020306090a03031503050615120708010621020d06050402210708 65
    0x201140103000340e400303441d4030881184240c4d50f100308001080c0d180181c884100c0c003900f2105e0229080030f002d1f88400500b14480744400b054041002400c5400000d201c040741e0703281c0a54207600c0c0c0c2500300340ea501620200e902180043c80705810b1400b00b5004802c040002c04050311020307052044e03070043c02d91956201001461a966004000d8440000701c8600c681cad50448a024422180500c0741501072041d41d140001d00310307886100f482c0c00c544164100701628100340c480b080c0341c0220428014003400c192100c0e0700350103184490341054004198541d62103031a4441c07902c6c6019100306181c07060950020202ca50740d08010215a1703c505004100b900081d0034801c0010b0100885826541101e62000c0100b500741e448610001805400041c4c0070342c00441c4440420130750301c0800c40400602412400000c03128544115000c2c40210105550445401400c2700c10260391000c0302c10309031035041040400c666071180b000442c040000b0b554142098515030700c030018007030300268050569114008441 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 993971142 1250 993969892 993969901
    0x10501081003020609100504120c1a1e0f1306080a05060402042105011410060801060e0a0504051b03090109111e010c17070b1f03050c04110415030c08 66
    0x241d2440d041c040650000e41c00c0007200000c0c00d1207148406155040d280c01800c094850f170100000301544082038030400d100c0401800801120030485881034403960000e807602c4100b00c21034181e40120b40380740d0703001c8401044401d801010032040303c003405241c0104004407070300d5607005060b9a0013030304c040404070b15107c0020f005040a2085400f51101c0309034444061114644440c10701143c41011241552115051045000001949400b0300c1408005008150905800a10340c0c60140e002d802048284d49004500e03407604a0008280c60050320041041da48840d0500601c0103c4001e5416101c0c00000b0050f860310198800ca802a104842d0300c03c088000b0000c1000b064036100d8240c90084004884840c1c544c01001c052911074882c1100c0400f8007000140c3e0283c503044520140e13141c642d2001000f42d191896042c41000f4180c42e5000c924090541c0c844c0356480c1e40e00f052180c060303955115020441c0356021705a4000780000d112503600c1440c2d07058000d024180c85110040811003000205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 993972392 1250 993971142 993971161
    0x307050c0c010e01020304140409060509060f070309020a180e070801150503371a070807020a03020607110c0310060e0f090c04020a200114070215010b0901030e0604030801050108 78
    0x203c2080c00142c0c015402c01c2d0420707018902c05003850402c1a030050341c680008000070740b24060240716940c2007020b01400d103040040310011100041a103020545402d00d0307500181e40d0010300400b500d00c034030000c01c801095100d40000038024030f01d66140511407180300203443d190540110340c0d00c000c1920702040d51713903844060583da000c403542c0c150070540440c501c00e41c84148504076800440c0d204c140100e441c10a60300c440c0c0d04201c4c0d5801c0e800e0340111040402038800d410130480c0d50071151510003003e45004030f4074020b4603202c019000300308208840a510040a0003008007091098004080d100000d035104c88810013803142d4403074810000b180c800018980a41c1404541c441c03080390014000c03100d010030420000b5800680d00d4020700c03010031056191851348120803420f29480c1c40000419500807054600100d00c01800c480c11540980d00440b1003c8914440a0440350082845900c0d110b001d00103070040c1c100c803d8040c1c0d040c800d400401003410f5001e08658101c46080e01c030303580c05803100f0320716 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 993973642 1250 993972392 993972407
    0x4031407091a0d06020a0504050d110301060e040305091201110406170a020c0a0b0601050706021207020f060c1e0702090c040e0c070305031306060306020f0a0e121c11030307050c0c01 80
    0xc4039480f50255141101284954004107201c1d0313602e00d4039501d011f44450001d900f003d66010107445004000410301c8280c242407094402034252100008101e00d0142d80c000c0a5204d05002a17000d40d09280310103035503c0c02500000500031089034040c0d02d4644030f0400070081700c1b22415042a0310344000125400c141a482100d083c1074081000d4102e1060540382d1040d0841c000c0c11440c10440b00300b001d1004200c0e1803020f050341c10400c400c59a02c3c0e08014100078070304285901458a55002441401107004410f42111440d12807510b0742500388c01950b01a01c550300070000042e401c905010200110034a400005205503029501c0035803c64452425561460189100044c0407a20400218480c1d900b00001103480364481c00c4040740e0140c580c0d44c0c0d8001d0380c1103e2107011201c01c011400d0100103802c080320704182c0d0703810340700e51114044015840c0d41d18030050399080c000002d40707a101d64600d48075075015000240080c040305d1762402c18201c0104568480d0001e400180544104040c0c2e542c8100720 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 993974892 1250 993973642 993973691
    0x8100204181a1c20091305030d1a01180b0d0f06051e031509070303052a1b0d020603010e06030a0f05061603091515030b012303060f011a0403140709 65
    0xa03c14843e90f500c401e08907066401c0d06c0c180c800e0b2000b4090b01014940c9805101101d035005a0545400c2b03400d180090691302c003881d502030501c42140c1c0140801000e12050301c20400311441c0100e60610008412001443c2c250032150b0407801b0f0f240c24180a02c1030348003000038031601b6401c940d59a510121440006603003940c1c011003a40110500f00301092140001c9d040c020031800c0c9120710b01003400c0484403403500e0f0100640442d0450506900e031f40d92440e185091002f41a036000000d0311680d800165184814026400c02d034103941c0111355242c80821299071007030b501a00c154888a403508000d642c41d41c3c00c0b01e6044c0d100090220862445100303000744c8d10600e07480908401c0103035198030404080c295009031111507450300712000001c01d418080c510300800c3e81249040e203d416604c1860742c0d8100320115076002c0d901183c14010701d10040401581100c444441c0b21154039440b007514041449560b00c0036100301d41010368500d04207000704808040f1203200004014040300c01d50442c00c410300407003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 993976142 1250 993974892 993974899
    0x1e161b0323030d020d0e0d03060905010b070c03140304051c120c0210030519020a03140603070f060c110915040507020f0d0c1a0f0108100204181a1c20 66
    0x40f840b00e0410781c0151a0341601c10402003852203000180a140110200c1020000398640c0070811050117644610b070b000d031503801310303d5281c90001e07120381c800c880203880014288c00d1196010001c024050007942e01805e401002c000c03c90788502c104206043e501481a5940c49803034025403401401107010700f84031940a41000d541d80c014130f1080c3c00a000044c2100c140310001e40400f145480e49100404501021351400035208421040b20010204000d0402d4000e510110040c41285070b020140740c1210721514084800f180700e8603001d0b4039016244006a0010082e80500869510410f2a6690303188151810803030b50340c4000080b41d44208084400d00b858001506035000e09100c1c00304a0078482c0140560840c0402c0f41d640100003c0c0110780080c648100f66005000829042c4290800c07649600c20950510b4105004000d4208880d09c41c460415550040021a0b05421082c1400444000d20441009000071814519090011001c84040190301c1d45000400b641e003000072609036016 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 993977392 1250 993976142 993976147
    0x18090e0718060e0115120c090905060a1a0a09030501060f090c030515120a050304060309140303010320040915060603060503010e032a0a050c0907051e161b032303 71
    0xc060640401d200c805104d08000c2441b02c944200501030040010010140d80c40102d01c2d07107400c40c2c5400300e03840074201900c00d50500b201008034101d10b2001081001c449049150b5845040c5416030300d4a002d40e000805a5090150000d10740750003180010484140003000d201641243d40110120f83c82260340341c804205032040600c40342070980486171a00d1000741129404221500c1d5249180c102d6840880000c0d00c030000c4c0c0c4100400746051020141613a4002c5007035505595036a6224910ba0000990301e00340740310a400180d4071a00514040f641011000700c041c1506d002d01009445e9900510010a003440c070006054201449036210007000d58024500b80415001410007902d003020f5602030035030310a822001ca03000c0c244220076606100b107005000c00f051380c406210001e0b81c010990800d1010038000341004030b00c280120072201c1280b016165030b0301458140c04910030a03002c40509104241d0030707800000d88020f031425007501e006254103440900c05260800d001d00c43c1c21100f0071903800c203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 993978642 1250 993977392 993977399
    0x3606115d0a0c030327060209030f06040507091a120106060206060d0308190905030f030403122c07170303041506150c051f09060e0d0f18090e0718060e01 67
    0x80d4802c1d105d00300152050054005074a440d5002c03000454015241c883d0b0000c1c000c2d5251030100031028030038500e40c015003101d25103500c4403603c41c622403044040c40740d103402040091510b180e035000c05201c4000d02d03016140380c86d40c6040e4020542800741d07001500c07860380418240d10784200d14050642d415a00c0f10115900c08009001c0d01e031818070244540ba4482e8490710010750144041d081c1e014042c0c10301e540b01d1500f41401000c038008212130400c03007441c14041e114400142ca1011030022944041144100200301c50345203411b05542c8080b82d0b000d0007550b20040d41401000450089000304035400320700b0300900e24501292075034440c00c2c030710003440c00703c003021b981c010020b2450590149081d5400f000c1840030a007905000c48c3e081c0c0e5400341d035480c104c6003000240e104009050b40b0550003441c8104520f030000d4003065a481090f010300143c3c8154280c0d0788134122420b0302070000d880d0140078240c01c03040c07446d03528081c030b000d02026800c44240402213001184201c000311102c0b01290007881c1d18 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 993979892 1250 993978642 993978647
    0xc061e090a0b0708030f0703060e18121303030210020c0c0112110a0309032304120f020d03110708011103070309033606115d0a0c03 58
    0x22058403a00041d070701c0710019030140000080c280041c01505480c0c1e882c40c10100007075807030200411034814189407013020711001186076010f0307030310008400d11480c2d4040c0c5804214540100b105440309110000a46200408502d003d18800c90707201340c013114030141200700304a05130300a0040610701c50f40004800c0c4e28a40c81444208a510f104590000f2a01c041c01d82030300c034550016000d440800e4a51081c10205a401110b50101d81210025030b4110006001c1c40717035680c0b19034419101001414006541881440011805010341c0182011001200c5141c007030032a4103008402a600c1c05254400203d240040c050320b5000c11908810502c0e540c0c036110160000c11103450180c04009586076900c84803651a0481f07081802c41006100340070b030b9220303415030408040d03070059401c001e103002038123546280003d1502405041441101090b203c09040d01440c02d20360034103580d0700c0c0003d0b20b880d400c03020000c1e001c800d4400c10864844401801007d1314600b03101d0800c50703d000030903503a140000f191 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 993981142 1250 993979892 993979897
    0x5101503111e121501120b0f0f0f09010306090b060909120a050f0d151a03011202040b06071101030c0305010321110d02030c07090903090b0309011d0d020c061e 70
    0x5806002d1a402d1140440d62580504000c031100880000e8012440c0525070300321001426a00407518140110800740e80400d141e0038184a500340100394040c084c8241d070b0340c0d941c3c005428070303000f80c48010650780d02d040580140c2003130f02081c3d070136100603001300b00300c7d09108407194450b010b26002820820416404200590300498074401000300c103029040c1c4451047d030040001014440d40460b20b081107a1140c0c000e00e001e5405074418509050030301e56041596000d9a0454512840c1c03100c0303221560011601611040030a982d000d48002110410800c400481000250007a07800308446002d12505800302c64003070101800b01e032903400802030502c0401e800c80c403514041e4501400814031038a5090b1506200c43c1c20301c03001d60008144054034000410901004013a2510305000402c80e07500d015000b18040c1c0111486400000005419030009401454070040e100814030811a241c092464075101c1d2204061300500440d02d107110b040c0340c80000c5c1e42d5541c04190240190080513007421440e41d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 993982392 1250 993981142 993981187
    0x6030f0f1504050a140106050406120f150303020a110d232a01030e0721030e03101d1b010e1c030203030117070305120904020d0510150311 61
    0x110101d50035812585490007a103010720b006034400704140210f007039090084401608501c0c00c00500340020407401c2d900c030400901d03184007034400203a4060700c618940003600d60b2081841da44005d0400010406500141c0c01460b07900452010300303104407500030003202d40a50607020300740d80d0700172080040d00340720700f115140c10b4884034046501110901c04501e01c3c82e460009201e17410071017140c480626503014060954183e10880c007502c0c0c03032400c01e500041e1064080c0400044d5200d0700c81441c00f05400f400d100351541100070101c500c8404d4000304e2102500c1c0220210384408078a004002c1440c00c0051107600000030007030106403100c0c4250046641302c1c071111900340e004460f00c1c2101d03500c080d14469078010301e0180d40515501e42c1004e0a1fa550170401c034500143d16444500300b00003180000c08c13006003214102150725500d1001d280050064001d40d038003200300320300e06014094038090540140c001c4402000c840c0b0740e002e40e909016007c031b900c881d1802a0340ba000f00011008408007540b0f45055 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 993983642 1250 993982392 993982411
    0xd0309150e032107020405040b0601021002040e0411120f060403030606080601090915090234052a030f010c090603020f090d0309030506070c0314040b0703030c03060803130e0606030f0f 81
    0x10a0f2203500003c0c1640e0b1f0542d000c0c1c038042003440c180081968140000302c200c40722804107520300b0f807030a5039140b02800000d001401803e044840180ea0b07039604a43c00d81c9401c19a41282c0306400c9070070b8201e407201820340c0d0490101c2d14042c40002c03442c0c095509180304400c143c4405005e0340c98049254041e004400103910b50010064003c907204505101406038143d803466104001484041c1070700d1303040290b006a0351084516598800024000160b49a002d508500b442c0e007460200038140b20921200310425030326004807904c0510529055000800c60103080d905d9194032583c86500350224451002a002e9015007005880e8090a200c1e1405110500ca4a01580c400382c2d07903180d407402c0c548143e0310318000400700b140f007005041c3d00030b03012103d0302500c0c1c41c2c081c0b500740341c5802e8aa2030300c035041c40281803640704c3d580c0c8030401c1c1c00303640720340010304107181640c0d42c0e40882425029205214094000000340c9000455820700306103007524440c0082e42060340e0643c13107160004000c2c0314002c0c43e803050b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 993984892 1250 993983642 993983647
    0x3030905180c0d0e03130b0711060405090c09010203070f1110030b03280204240911091002012d0e03180909010902220e060405061609050d0309150e0321 67
    0x5070389203050506d00040c4050b0304021f48410032454211f4001028280051040304244014441590789010240d0080c008006440e620981c2900607810f501403040007908940000b42d034107080c080e04140f102d0b11b040303045864107148110800300313804683c0b5501a542e0503610038100045040c4451407503900055000c26601c0b1044820f500040580d0700a410801181444145646c00070b28101c120501400c2054014020b60f000d40c0702c51515801a07690b4584034805081d0341710301d064003c0d80000c003a80070b000000c900e1541390030f803185008400c61142204c6503180054594074200701000b0b441c0300c0010010710800313140e03494080182c42c180c0030f04018055541c130800c280040e501c8011500b00d148210400301841091107038080c0440e20f98080b02d41540c4c10174400c01c0b00041c07000ca1800c0c7e202c4c0790640250b032801002d070811076960545401840d0488141c1c400141031541081100c0c044905200081e800c0b900c5100041360100d1344410351540540c0002c0311000c0b0303116000200d03c400c00c40395000e11b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 993986142 1250 993984892 993984907
    0x5010807060c1a0901060512030a05090625060209010f030516050a14040f0e061e04110714150606041a0a0e0d0b09010506010c051c170103030905180c0d0e03 69
    0x1e855842644c20381d88580d560f030010402da013880700310a11106520406103007803514812010380644610240d20344211310000f89d101c0c10b0403482c0440c0d5000e0b0b609d000300844e03041952400c0002940f02e0391480340421407001c00196240d100e80956441403001d03104000407004e151901782d642c3d410441002c0b003840b84800b1114000c0303079800043d1004110443c00e9035215858070080007200301000e000140038082c0e0702c007180000700020f8841d4501c5503007520000f03414504400d08444900075128020710300c00000c1c204000070000040c5c07000340423190b906030703c801c1c1e203504040180900c030b51310400d420412a0964000c5008581c1c1c0580380d901110f007050031140c0140d100040d0b070201702d090200c410310300d03041c1840030000c400d2203103a03407024080c2080000d900840c1c440c203907221a4008502c8200c0c00a41c84200c0302c1d881003046c520135100b02c502024242d6103d1901401ca03d509000b143d0040e040840c0c00d00030340e091050090b005a02c900c42291070b080f00301c0d10600240c8160541076103d444108100d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 993987392 1250 993986142 993986183
    0xc080729120c030a0f0c020d120f021b06071e08060121050a0e0c011b0221150a090803040f0c05031212011a0306060d0905010f020408010f05010807060c 67
    0x380b00d05a042d52241d036070b181c070312030040c00c81d01409003140140c1d03d04802080115000a00c2040411a5051655000020800d4034018011030245a20740e5400469544880301c280824aa5039141c00c0080d504560f440c0d070740c1218810b40d102c0b6441003085440702040085805440e000e50041018034260030504600c0604d4660003d5561100407419642e80070080840e00701d22900e141c007500040070701502c41041c2e00080404e0b00418840703400442240b83c0100710742c0d892928207010651420f01c9641c02c90814203260b150407048840303911400c1c4020015818003014403603003100307592101005003540c45c0e41e203c0c25486c2e85500c100319410a09600046036a40e0100281500350361808140c0d40c0e1000301e40e0412500e00f0741a4800300054550315280c083c1e1160403000e8035030004068414549800c60700c20b0810107468114000350095183c8201c482031407155400820580300f04000a01031128808014021074030b0920540b14940c00c446c034244109031107844000d00e1603004040f4002698006c0010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 993988642 1250 993987392 993987427
    0x50307030b04030221030a0f0b120f1002090105040e06010201020c060c040821071212091a011d180a0204021201170d02030f03040f0b0703090c080729 66
    0x181d80910703212041104056040001030a803250810040741c040c0740e21407404240b40400340c034183e0a19101e25140d6407408044d0f00280f44400000e0404010054000d05a61112040d81d499500c600171755030503035079002c2540200c84210f681070303580c68038203440c100c5030200c4550041c2440d41155001c01518140f03010400c02c1500600290b40d01c01d9566241c00401450304d03503103e4080d12508400c101421200840a09442c1020340064401d910f1a00d0701c1811184a2200c100c1030084a28048c0c1580a1210070103240114800340109044566292041a0300a0000c2c6c0d0301d030008051640c00003240b014400c01c80b03600c180440c40450740c5810071580000c090f6004008401c01c03d0360707890f00401c84c040d201e45800400d5040c620282c840454200300080d00c2e44682c03c030340c049900000020504020059180c0780016400c15504900340c106420001c010b4400d400d4181d8a04440010115550030b020a02d6030840f0340300510501980740780540c10b0700204c0410403805e4040018480b0407520103c1c0d00c803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 993989892 1250 993988642 993988649
    0xc07080412031106060f0319050a120908010b0f030a020f0a0911070507090903023a02010f0c050c0c0f0411030103030f02060c0a17060d0507060504080f0a0f1407050307 74
    0x50300b0f0811540d551981e0701d044002040c00d8883ca00f4402d0000301c1c2c1c0c50109021208100c2d520040b1000d00030360400b1031400010860040215074544000901c082d40020000c2c10758134624000e000c4441010100000c5148425041d0b5060700303c540184018502051790140301c10010700782d0025181e444e8003140840d521b19940c10040000040d50f4000c00c80e042c04040041c20348603504225120181c2c400940e13403000c08901d00b8022414400d0070076040c0d24a0000c210348a4060001c504074a0039140090180c00e02c481040c10f040d04194611500c0d0f03004600340c078800d015032001002c680154000700144004410541a00140d1303454403140c4d400e00d00380080d4040c50294441074001c84507d04c0092500302c1c01030040a0410302400300c3c0c40c240750310648102d4a405240c02d40702c00c0761a2440052a0f15261610040452207100c0c00060704035085006402210070f180d059409100120203065125111351000801c81c01c884030854002a214464040700c03000c100c030480380055190381c0072a01c0e01c100c940 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 993991142 1250 993989892 993989897
    0x301e03011203080f01060c020d08040801051501030b010e010221090a03030819020f1b0c0a0f050118080d20070605040e06030c010207050411090306250908060c0708041203 75
    0x4014900b815008844213402609100700030031603614202c0000c001501a550003446208040ca103841400304400540b40901171a038000c01941c20700c40d025908a051882250780801e0815806000541c0100c425071807004061300604143c524110003265906441402034412000501c20760003980c41b002c64041c09144607480d20b00e0345040c4160034002140f503e03101c02044600401c41e1002541c0c6080c1640c01e0720000c91540e9011090602c0e4590500c0b141d001c1194210540000004414080c03040d400116002a294146c95440384426896403030227030300410132103070300c00114800c45510607104121180b100e40c00c0c6845020038400c04038100802303070f032000c00007450101341030185001001ca2950040c0b0210010015003010000103902d41c5a82e102c0c6078421640c070b2401441c080022070480e5507105009003550080e10703000c2044d4842d02c1d22544030850346020140350100c03e90240f891a010b40300050700810b165034410200c3c0060380d00031041103940b44010b00c000101c54001c3c1c030492560303a103c1d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 993992392 1250 993991142 993991169
    0xf03150601120908131a0a1b020a090e1b060a021506030712060605150c06161103040e0415140f0603070b0c01020306030115260f060c0a02301e0301 65
    0x241100080807000921408400e05c10800f0741d800c7d5800145090f1003c0701c0070300c01d2a040d6514000600c207070b0000d03403102c00e10500b849040e0039008804070b490703c0c50060032540e181c41c2201c064280072031401609940000b5a1190544091800c02d0b421510342c040070040480741d095861303940c20020403280d800c0c1112a561181c0e4240590310f003808040ca41c83c4400c1d801c0a0600902e01980d0ba5211000707418500b042140d65440021544252070081c28606c117001180ea40c2c65440a454410b800e00301c4007940c8504407003858003c003070003502801d10892a8215400b40a49035010400001203014150541c940300d1101c00040646080c0003412480b44407000040c0c4034a400b10502d42900e0700e200b20308a000400d200309200c9040004006083d213400c200760303c0782034008081c40c585400101030780110a40704000400c10040402d400501c00013003154255010314084040040c03403440003c080084036445110307a40c80c4000468083e0000040c0c141003a00b00c404040f24039000c0303600a0300143c103201d031017 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 993993642 1250 993992392 993992399
    0xb0d060c02060103050d020604080307030507030f02040f05010201050604050c0f0d0e0a031d0301050709060f032a20030d020304061b180f05101b0b150f0315060112090813 75
    0xe00091b00c451400d400940a10f2a0969640c0e880d0302c4010101d00c1850341c0d441c08103182030312950040903600c6a0302421556541c50303800384071762a1a07034418240103600b0480040d07400e040600815029001c6e05880a040540005842c0e24940044541e010519601e018144c0c00ca0009c00000b800f55000e6120f024003080e041d601e0700781c600041e0039441e00982c1004c0900a125502c51038040484281340341010409410140c00c030046c00c00007400035041404940d4000c010030f080c14030428442c0050300c2d040c0e126410501481008101c1f481c080588e81c000340100080c10500d03030010366002d4402e500c000b54401901c0c1d801e09c000314110201c1c90010f0110344d0184024100180d004001d40003251100003182d1510000489805481c182403040104c03134002140395450600310351543e030341d010401582070301e0007909000030780000c0307010680720b4241c1c0000c201c854240403d00d03c10350058801860b0407655a40010b441d128215094101e09956500c440b0000c149500d000d401120032004010700c02918 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 993994892 1250 993993642 993993653
    0x10051005040c0f090e0702070e0903340b13061b0f0c0b132310060b0924090301060801050411040605060d0e1509010c032d0b0d060c02060103 62
    0xc82142c406205100001440d0190040c084104840e411120a1000c4c0c0d5410000c0381003800c0d80e40b01400d030044060921002d804040042c01400c00391207001c0341c402c0c103280000000780100811004880c2411100400421000c4906a41c8024061b841e844607c00c15034481e4200d030304041c0c0340b514800101248101c0e003540050314505076119880e0039202807402c0c0c1c0b83c1e64080d00d005800310030203100c3d218552040110540d003000c80c0407011086144451541000703036440303a0304081031000152804001044010340e02c41510702900340540b2100c0e41c011609095041e61085400113607980d10284000da03071947e000d000d0b1780040e00d0b0181c00450a400c0603e0803564624244103054807641c140802480181c17511000d0310600d84c0d80b9080032407824001c9030420704042203a07620544000140082040c105015044141004121354080114a082072443c443c02d2a145034505084417003403010f078040e0155900901151030000b064541a00318903940d0700122002c40305c800c000744c5c02c032400400034401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 993996142 1250 993994892 993994901
    0x3120a080435030402030a08220501182d2705042a03170a1806020d030209180103140d020a05030906180310020d2f070201021005100504 60
    0x20000e00c0c90304a502d03a40c0a0800001d0315021814104403004030004003996001c220420714260458000c030f5850760000790a0418010701d1500086000c0c0c40e2000040b1544203038081d0380142301c2c0b00801c01400703040a02c01c1905030700703401c4200407108082440103401c050740840003006103951400361414165008601a42c4400c0b00f42c5100c01618010811000c01c1410000f001000382000781c018039582c084961031048040d81d0005440c0001c03a15615001070385200091082c00e2058842031400001b0702c1c103118a0b01c1003802990010f03048099100b5221380a0340280111410007000d80004501ca484000d007a44001d9000b9114007048000d1401481c906102c1455000f5541c4041e1140300516100c0303035640d102e441c000718021100080c05015aa1809010070103040d801070540350101801c6a80030065042522511021071515201c2019602c0920024245600144e0940c01c0c509044002d801d40340c01040040c1d0560040c842038110300d5160303204891142c202e114440c040903041000303010445 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 993997392 1250 993996142 993996173
    0x23030a030f02160308131509060b03010218060a032d0e0708192120210d022a070911180423150f01080c030603120a0804 53
    0x100d02c1000b80d81c00d9a12400c100d102c0c0e490701414818040e840d800003802007240350032000741c81c0c0005500071108124254100d02c0e02c0b82e0040340705000020201c030800d401c034480e1000c014000800a4003c0c801c42c10316101800a803090380c100041c15440c00918070003c0d107200756120f0381e04141e0340e202c0ca0321450944201100d181031140105280c5040541881c4e070b13440d04003844121f00b610130780c0110400204540c0c504210721181524200e00888a07009003d074400d15401564095540a0442501200050202081051310082e850038601c80384c00b09a00e60140d00c1882d00c0e16020440044680c1c0c84642d0315048901d03280c1103802c41048800350038189001c0e41c0010340060b00f13203046c000d0301301c640b40151640241848400402c40100200080080ca0b504038003441000f254000b100e0740c0721800390348a1013200903800c07850300c0300380c40c40800840950355000e090100c1c1599001c1030b865003c030030255500c040040e003228000150102d03600b200ea084187e4400010301031070200001c002c01c89003070a03423a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 993998642 1250 993997392 993997421
    0x30c03010c0809210301120204061a2a0c0120010c020a120e010c122304030606080606100807030b0a12050c0405060f121204121e0f02040923030a03 65
    0x200b42d4000d02c0380185c8810300c0390850160405003e030065681c0c55001c1c00040071003150011801604501d42c04c819007188030305a00da10380203035034844506c803e5008500050084005000005841e02c010340c1c041e41c0f10481800c404c2c2c1d040b01d050709000340900c60750140028540041920580f030346044211071119007076180800030001040c0c1c0c900e90704200600c84040c0d1201840e9064207814108580ca408404641071000c650328900c8405520500700900540f80241c1c003d100076616241103c3e502d04050f20380307540003008602880031440c403d256554010b88549030220348409100000340490340c0f1034201c8802034428001c800e0410004001103040080241c4050000345847d000064107019900300346070041075111031505816006010850100044142d0941c4540c0c2301d140c404500d940e500d1048500414030200c0341c1c014078048500d48a00e65004414649010440d030a1102802e40e00e91308640b01036201c8610a441030000082d5101100c03403800a6440f05070800006068682c2d94640350300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 993999892 1250 993998642 993998683
    0x61803071e050307060c03050a23072f0c040501080a0312110d0614180c07110d06090f0215040b04030b06060f0d020408060a0b03030a0e030c03010c0809 67
    0xd60006049075404400c640340c514a5102800c1c82c5003540300e0140003c01051a19061144a80e09940320314001c041010040010016035824040c0c41d60544262a400c01c40705030001f0020b0b8490034820a840701c000010420743c0e41c690500001f0104088c01e618480d4000013002003050030315100315801043e004006000300c0300c164501402030025040a07640444c1c440000c100b0f99072188040794018011400200610390f5603000d000e501c01a0354121a110784490360b48900c0e85074510790918010100b084d482031a007000303a5122a5440f190000603608080481c03086030205641f0b1050400590040d0780c0f01c00141c1d1a441000050307107200c2e1000e61030010900c005e0003681d2240d400c0e034060301c0c0c0c810b5640841da00d0b0078001500f58050124060b60700500002c1144c2c00f00010340142049a0021044980c40d1301e4184a110a4918a02c1d00c1c03905076005104455109100c0c00e00c5240865010307040d1004070280c01c012a00751681e44401c2e0000c01c070444280203603500104003000422502019404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 994001142 1250 993999892 993999907
    0xa030503180f062a0f060109140106120b040603062f0f0708030603071e061805010c030e0103291e0f0907090b180f03011e020a1b05061803 61
    0xd0641c001e84e44000d2103402074840426401e82c2c03003060319803032068840c2103c80441e040d1900711b40d5640b09000b000146410500c155581100c0043c0d4035060710b0342a01c5d610038000701c220038a0010407a0080f1568805e8032002c002000c00c58500c214110342018810101040c2c00c08c40d40340040c03e298000c0710060315420090001000380c00010740f0f4510740d01442c0c80d50f0340e460f05400249042541d0700300703040c0c0c7d070340c05022190450179204007907007110400d4451050006a01100c02e800703400314070400d0702056003e0021400240300c1d1440c0e4040d071005043c001381d20180002c403251603000c4c3c09081d03d0b14916445806080b49440c140b11a400100b40c54940d0742202030801180d210661003888074010b9410401040b0351601502003200070300000416551140d12100650640c141c1c1e61040c0c60080d030130b0305044903044c20706000c0c0140310206410b402c0015090100454025032041c8814000c0040c00f407001c11703441c80701804a8401c06e008100808140c209100202c4500d482400300d5075850b8410840c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 994002392 1250 994001142 994001149
    0x190206070e0103020d02040810090c0e0c091201150b0a03060b090609121c0c0210080405120d0e030f180a32061615060303210b0a030503180f 62
    0x81c000c844080c40c2c050785440e0210300c200040d0107a078005034414016150401890400c0d6030011510901070405c40600c01d82c1e461150205e400c068800501d840e004010802d01810900100368541d810340d400007071012451004503404515a07000790780c001100042d48900c01381c1c14000d25010b007403959401480e000c82107000414038416029101d005030b007045800c90380500144007551404a2042c2c034804850b02103003006081901d4090701302d128282e54003040100c42d00c911091803150764000010410000c480011320101c3c0c11041c030050589032107151007440440288083d201200c1c00032100da84428038101130f44440f031070600c1818041c1900c20010410b8041d0260f040c200400c0d540220508107900720b80d007141015184030400d0704240006415107242401d0440d9844907401403082d40040901042900c06942203444040c0c00038007400e41d122030031700c500380310700c155500c80d5000080c14486003408180c107900c4a0b40182d900e5000410320303401c200005100c0e400708000803224980d080c070401001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 994003642 1250 994002392 994002407
    0xf070209070c20011b05070f0603061d01080d031a0a0e0a0509010c092922090507020a02041d1501090e031e2b0b190302010c120c120519020607 63
    0x8140100c141c5c04007180138800b003800004081c00c030f6061036039200764983d03102a01411403841000c89655501004100e464a1119005c0c140c0f10b0213000340080d248400c108401407d1048100d2210f0841911512055917170404a00d00425070315401c84060300e0510034202c1259002420302220741d0400d942101401e0f4040c2d40078094404e1600b004180c01c1c101d41c0145500b10b00482c00c60b40e5800f001030b040c0c074030001500f42c40f02c3c465182580c3d21501c541301d0109105403241600c901016910040c110401881c154120b4550480f05004200d9241085440580303040070000240c409502500c0040c066544d80f4056036602600c40c800852030010185200d81c10340f050610b1a0f0117403e0042000c83c009100e0307100010102c0c0c1e00020029001120300103600007801c0b5000c049200d0b01d100d003802c002d40403800c890313035003220b405031188240a043c98403010310180c1400141c5007000340790303c00700c070015500081c1d0501d0001c0c00e5481c281c031100c80c1d806401a4081813802541558000e0041240750f5911150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 994004892 1250 994003642 994003667
    0x1709190314130b040e070c03081506090402030a020a090b0c030a030b030c030a1415040f12120e150109050f01170f070e07141e0f070209070c2001 64
    0x700161a00d4800324840814040c001e1482d00c0e001650b58002810610440079000f0703201c1345040c2e15000d40307a5540640c7e0085600382d0040200c1e0f8164002000d100e03040005208400020344901c0c90425130000040c120780c0120360407951a90702240d180821503107c05200c01030180c0e480b1a600d0400c1e1420401c0d96405040344107010503072a141d40c440b4a4a0a105c00c04100340090200c0d14078400300d00d04503207072820346c050404c039034800c0031501014152091201c1340119044070910340403502d1521110213400c00c42c484181403100346440311080740007611500094401c0f41c1d0240403041c0502c040b00080d80d006a2260449600b814140501c03a40c0c20741c40381e81112504020402100301d0340c0f9980e410620340c4000040360303024007400014114000940b0503c20002992807808000707508010f9103450042c042c0390b640100c515403172004e07075108910050206001c84030342542000c1a41d40000c0f00002d080702c08200007003400142508003d004203440904034272001c044000180d001000900341c005588 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 994006142 1250 994004892 994004897
    0x2070606030c270b18070816020a03050418060f12050606061801080402011e020105090f0706050a1d120f0d0305071b140d050304050c01020109020f04051008060717091903 75
    0x1030750403925a03101c5c45c00c1d90b07001e0048492080f10349020750001e0400703401250149112040c1c03903188001c2a2000ca0303850400c80c0d064407803604190038020f180c08004071552000001c03a9403a500030840c04450814003000780740505240700050381c9071501509104015060b14016102401140d06001c042c03150313103030104001c2ca40214507981e103000484903003e1020551400203040d2618081c000d90641060744121000000c40f86820000f05c01d42e13940350080e1054000050088c8032000840d40300e1881c4c2c83d0b0b20441440303004003101d1841f00243c0248801200011181d0108400450880d820310044107040c0060070104080d160030000580628130844e00d0300b6170459051340c03035400c0003885010300c0f0b00c682401c421540e085614010140030340d07105480a85081c450350b00c1400d0158414014041041d5018111620b402d401300103000c054800580510032130410030001003a00f0a08009951094a00d03039070785041204406018007040101800b41101c82e00300d4201105c071100c1d04804041882d40c1031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 994007392 1250 994006142 994006151
    0xa0302070e0c220e0c09180714030c090301020f0309060717060d230a140a0c0e2a1b010515010c23030702010f0e010804141002070606030c27 62
    0x401140d90403c000d0740000104403600c105020703910180001519141e20b05503840301242110540d82c0101d41c40413030f54800002c0d295540300d01f01442c0340000d1504036004055203030500b44010006400e90700610b86601a9400c040704000552400300500c58200040e81403000f180c4001c40411291414000c143d2805140c81480d4281042a00c442c155040c0009000b8044004002c3c2c4d070441c0c440c42d02d00800c0e42d121159800110001402282c18006594800000b80c4140d14004c60000a5140209645030229108043d1003516102524074501c02c940300d50300075610700f000c00c00042000c1d900001941982c2c540400c00c5001b0102e40b4041c1002c0c0d400f42004035a1149515000410038250031502c1d41c0150340d049640171104000000e040030f10302c00d885069078000ca40d142101e004250308406400128100c0105020a082d441007c1030303001c50b00155208424500700240580c0e03c2054101c500715642c0c402001401080c52040c4090420010720100414291070701031885074051206000d0a80d45 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 994008642 1250 994007392 994007437
    0x90d050c0a0b1f06050a0507030e0d05060a0c0801060e0102030306041d1207060b040216020f030f1b040b01020319030b040204090603110a050a0513020c0c030304080a0302070e0c 78
    0x1042485406540415002114907140c00030040b40b10f0803440508419403608404a40c0e80d02810541382a40d0985c0d0741c1906207112500c0480301c13044503030541c03038200c95a0000100070403002c1c4243ca110741540c08000c07a0310b10384100001c05026050380a40304115510341c01404581c1d000c41100c0c0c0011045a0205030310a11441450021426095110180c82801083d202015015001d0100e4034000e0b070f810040311038000c0c10310003a440790309540440000a030340210300602e000070406290040280440e10b00204170004c40d40b5007202440d0700010910200a00d00b2286004c0c0240300c01300500384040d5090540711030511010104c10740f0710400f4140c0314001541c0c25242c035415200104440c01c010710a5a030740b400d003100032601c1d00e0031060107980900130118090070200364460840380d000d08000113500198011344000e4005454124445c081d070701c18000e0944e810005800a00240070103441c0010b183c1c82d0291406010394008140d00c1e40701400c1001404034801510030f2a5104070032190075a0b0b2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 994009892 1250 994008642 994008667
    0x6070303021806220f050603010512011103180f1b060304030c0210031e0507020c12010e011a09010801060f0b180409111207230d0c03080703090e090d05 67
    0x2039400c500307401000c0818801032600c0e40c0c0c0710501c130701c92200313280c4000030341c4400300c5d0041c056260040c19009401003004020600300000c5071056403c0000000601211403d280b038003d51040c2c410f040040c2e030508061554040510664841e440c0b240000e0104407000d00c40c0302403010401d914035110b058040001410f160044050b0031090303a000b051000c4841224401500070700c03150050076803c54468020000e0081e0350321406024000729002084030101c8031082207101d40383c00070081002c5d52501d807a5801c81e502401072040c1d42c003001380e040500003c071070188408104142e00040140e810140204048420100050180c40059800543c0c0780140c40e0700b05030640443c0c09041d0040d10b400a1182448018511a44d03450300c21144010000031005401d030303803199103004941800c0084908440101c580b00d6956001c0d54001d03001200c000d03456154030707411040e5035000340d440120014414040540c00103013400944425111140d01e8100b907003c1301d0382c880171500000309204001a40202c01c14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 994011142 1250 994009892 994009927
    0x903070626013c18020c030403210518012d0c050f07030308060402180d060c08130f020d0507050a0f080c01020a2d060f091106090607030302 62
    0x280394072200c652550352a11400111500300203210380906445451140e003d00020160b00b107040b00400c5910b425040c1a080d440d0130801c0104c5002580d405c10882c010248140701900046004507603145c080c13002c1d14160742c2000d000e034209a08200d4204045400c200c04040e4000c010f05003072a0410ba4440400400402a40300b00c50610001a208031210301c130a92107540008000d00c141c0c2510794000040100a5032070f085400014085507602c1c1c00190b040c00d01e5809480070420b100301d04100e0101440100320130200c101e1003620241d8030360400741480c2d50442d5100703400000c0203125000f0307040c07140c40f665803090403624001d01c01c01c420320317074442442400c2101201800004016a40350307039641c3d805e1090341e400307481840640c3c0200035903038400d5800424030140154100300c91f408150440c284003400902c820184120b40c9061032030708408a440c62246c10200754a40e107001480717110f14185207080c0600b90b040144641130401242c0c189494001c00c3d28100c6506050142c4c50740b5221003c0348818 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 994012392 1250 994011142 994011197
    0x11407060917120907060f020c130603060903020703061103010b03040605060d05120d14100513020d020a0309060e0d1b0311161d040c270905100f0209030706 69
    0x38004100c0c2c1e0298001c01180c540640c4000081702c0006076540020780b41d40c0d481d15040d02c0941c01003234903c0c00a0510505100704900c0c04400082ca650b101e0790348508030f80e070000050b40180c0c000c5800f4020403105115030302c5040a250710590030342d803400c0620301c0c00d880002c0c002800d0544450214031552501e03210400503d501106450700d1050008501b8015004255507141280c100030f179442e1108410100780e801342d8510990300c00c035241024140b1600e850244030284510342c0c204000e0010010034030180940c161a540c010440445031305041040c2d82000d09084a6038105003000311525410403440c001c02c02c000000c0c04010405414260758620702941c20104601401c1c06c0c4445010250048406030f4040c030221714501c256051624100081c00c4800400c20710024009000d1a518404030214001d140c103c0200780181c0b2511100540e102400100e40d180c1c4401600c0d100d0007414040c0d08641040b403107085080145180000c0d40e15115885001c090101c503030218224001c8010b0b0641c5107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 994013642 1250 994012392 994012433
    0x6050c060606072102030d0c1b0201080c0d050a150801180b0c1b15070801031a19020d0e0c100c0f080405150a020714101812061a0114070609 62
    0x44d896904040e450381d02c00310380f03050590324007003858101134000c581032858044103406480328101d0980c019640322501820001116105100105003422140112441030b0344420000c26440882c406920b1516083d410100c1964184060301c6900712080341e10821213504080f64003c030351100d10001c0c2e000d2150b0b103160140c009c0c000b08110603000000680b06446202c08075180f4070399031540011106c8010a000c000c1061074103041c10108031040e100181d80007800c40d40719164540d0408002802c070b0b403200001960140d02d0700d1140c6265201444441d840681c01d44094050f100c403088000c00001c9200b1005103902d40b46500c03101445601400d0700c015001c003608e5100180f5031501a2aa40d030046114100144a42100031a44081070811807011003805001507000225185d425074102090700c0038010001c200320000a00003408440451803240614400114020082c19200202c0409014141404039255001401c0c4400b981102c0134513401400000c2c00009a1800812088145045400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 994014892 1250 994013642 994013693
    0xc01030f0b04060b180301140a02130f0303020a0b0c03100b0d0207170c0c03010902060a0e0f03030d0218090709030f03050f03040b0f1f12030c050f0d0906050c06060607 74
    0x380000013034000c00c450015900035510300880c00701014262001038683c00802c580c1c1202040f0301c0040c0303401610700e002004990480b41500d035100c2e425002d080d90300c190b006074006a40300003400200314000b50092120140ca601c1d6180c0591154a4142d99100d00500c5046c000b0383c3c600b5036802941940ca9090b4000c1c03100000c50024450b0200036080400b8080d01409850a0522146814880d05401960103400c039410050a4101a180c000460b1101e0345c2010510300207071f1503984d00344010525000d624200680f2000c805c01300c010001004842140140703c0f020a0000258005006e039049a50040c00e00c4000b000d10314007111140106190604208000302c00e02c02005a4100c403a84165080a001000c9030303690000704504841c08a000688003848000510010140c50300010410780282420340440c801070b40d540c0e14000201c440313956540c202c409400c903d00d500451040c0200224075056007031100074595252103c0b405803c1922551002130b14004014000c0c201d075031400c04000e01c1c440f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 994016142 1250 994014892 994014899
    0x5120c010906050f04140610090911030f0303090709060f1205030c010507050702091e1602030408150103140a3f080702072304110f0a110d0804050c01030f0b0406 71
    0xc0500f1130955080b0b64103103070034500000d100e00020700e00d1f108040c006000a1660700c1c1030000b100910050000f40c40c0da101003400c18404d91010802c00003421800402195240b40c07040710507091000a0b080784450754180003007003140c01102e080c1001076811003030a00c0f54402151812518510828200e085a94240010002403641010240140a0081e6080c8240341c0d50411802c00300300d44030340c0c0c140102c4a0000800c030100003c40400007140c06500403a441e15446507003d51074a072903041c000801c60307480c6c4014000c02060076460508101440000d03c0078080581d124044010341070108000c0c50000c60184002800104c0d00101c4124000007600c002e181c844801080e041c011070b026005441b501c00c0014190348041c100000d410400301c4130501003c402800c20014001035180900450024003c41400b0b80e145030003400000d03a25114045200b03039a00c041400c1182514800c0306000d003420030803020800210303218400050901e0b0011b005050000100014140b83c0142600036185c140c012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 994017392 1250 994016142 994016161
    0x501050f0a1817060f0108030a1805030a0b19050103200406030b0a0c0e0102030a0c1b090e0d0f08040f0201030c090f08012f040b1c0911091305120c01090605 69
    0xc040a40401611415603031191000c171542400c0c80380c007844e50300c104402c0560301e1151624020f00c4d003244960800d100d035600700192030012605420b9907035040880611045900540c440c0010040c207580500881d031440d1105d04a11601201c41e50908401c001c40c0e0b42e6030794581e403213400a0360748070508040074200520002d000b03001c1003200e000850480d1410700d40c150700000a81d803a95046540f0520919001e9a5040150100000944124039021000318002c00b16018400250139100020700c80174503d21402071540700c0013140b800a00c8006018000820715510310f04002c2754080c00c0c01725440510b5002244c0c121100d5120310103058091001090300401908814203010182e450310803910130000a258901c01d50100c5106280000c1004000c00c09046014042120f00040741d0703030f180780b103410940c016101640421103410002d0090b100c228908200701c00d4000100c51155445110706644103591600800c450752240130340810503904c0400c003500491417042d0320135014406801c228088 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 994018642 1250 994017392 994017419
    0x4050d05010f23130b0105010c05120a030c020d05030712020315120d020f03030c030103110316181d0c04021b15070e06031005210102180103060801060501050f0a18 72
    0x901d54020f2034000424800f1074a01e0801c42e80c01c2c0c00c803045091a0346400015101401f40420444142c001d400c014040518200064000c60341c040c0c1307010401e01c89190f0006c2c20442c0d441400f80c140b2100388184040503902ca116102000c03410200140d59403194400c140722808038450259000d85c42c030720701e4000d034040844d40c030081c206290225101c107905402c2c0a6100d02045550346440c00e000c0c00100701040000c075620003a94800b07403d580b181c42e0000e2040c001c840141d049903a614401c4d60b0215940d4100b446910040340c01c404400c014800264030907a10789000c05410740c031554010038920a03c020920541515044071000c9803a40450101030041044080b02c201e0040f030404031401701981081c0c4101c0303114400480c0881c41003800d1404108002c50340c1c9000d0144c00d0781c6020030782c40c0309ca403d10003014a841044c1d0100c0801032240001803d42e0a590040400b59040c1081000b032a600301c025501e00405800701113440f01030b052001c030342481903440070010520300820009006070801e4103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 994019892 1250 994018642 994018691
    0x9111804020703110a14010641060d09170901020307240f050a0b0d05060a0e1c0e151908220f150501060e0d0606030b100603060906060504050d05010f 66
    0xd002c08c2c5e58902051305410300b1440302a59480d403030182400c0301050314161211410514000403546c0c01050007042d415006032511340882075807000c2043c103000b038060141c103c104254800501d0400c950700003d441c1e001e6658001c029142040200ca502070380c030504600000c000340d504100d0003800c0d05640300501029550350054900d4940c012030f99003003850b00c3d510000e40000013400203807201084000248004034007032003c0d00610081c114210800174566100300c1e02c1d95034484d1410300340420803040001d0050349459492041000144201c11142683c0741d207055410b00c1e0515607107041034540b8006459082d40c0c0c100c02c140d03d100b807c000341090170302d0010340500c0c07000c0c103403000d500c0441007158020b0040c1d0010400e0302c0b4005400b4079011580b040c41a2150f000465400c0c1d0f255903000203290180c50b1503422030750a9006000d1950305202c0e080040c61001400e014072843c0080203042c0c1e00c00d900036140240342404401081c08001d40014910000b00942006041d40706c0702c0348403d0103801c54 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 994021142 1250 994019892 994019933
    0xa0e060c010902090a090c0512030403020310050906070c030f0e0619020303070f05090f040908070c03201e0f0d0b0c0301050a170c04020d0609051009111804020703110a 74
    0x208141505d01c0c491034191340d601c0488040d00d07030f0610080102114902c2c45103002c40c0700c00c100c00300050720305100046180c00056008030f9503040c80d015031428402c00070034120801008a40b5000420360150260141c0c03080c50400d444100d20060128a107841402d001c0031100c0002d44c0348910060b8000025803040610380d840c0281403080403411070b003d200381001d0b00d512142c0c10108440510346940250b02051080030745901d00300040e515120541102d40c010342c3d108a0039243c0005c10301480c0d13101d45040608a8008004000c40c2c4011481c030600c00c0c4007940100d0b4480c0d01d0400513120780c031a140100d43c2003d0055980e03d0415070140c0c03164801d010b42c1d4000c40b080000019414403403041d40344010340305009000c03001d07400f6041c00000d401105940b0001d42d01d4010005843e0410f204e40c5010740c0112100c00e441ca414641e901703080c0d40c208005000034190401175424140d10803a404a41e0800848025030b03070355074504040310a21606400030700b16000b40d2180000704501000100055000d21 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 994022392 1250 994021142 994021159
    0x16030b091f05090c0301031209030f0204050a091b140103021611030a0b0a1a010906020d0804081303140105070c0507060f02070b040603020307171302060702031903021624050a0e060c010902 83
    0x85c8c00441d1558100d00c4011b003035a00c010410001854150455a0320000c24800050702800d9070315860030b42c010007001c55004012124082c01819201400c00c94010800e0800750f03c2c01000901c3c0301444025480058071420000080300b04a40d0140138510415800c1036080319141400c00c03600c0c00404440103100840345481000040a500503000c1c08100e8020b0303005840c0f00e141078070701a540034100500440340d40904005007180c0403880c00e4000007960140d40e280010f1890010b600b4215403020b00301e10103000503071404800140340020254107885c1d40b884e1984c8102882c00080c1d14080a50704041203202c408100480e41d01e0785540276510078845075403150789036001c00c5c02c410384401c01640c00c08034818110008001608100004000c140e201070110303400074090b1002d5000b1120846070480050f00580d03500d881403c1070702c81e0a005024138030740c5401064140d011032800342412030405000d00502048440755030f8014042030030b40c40c074081c100a036030b25014041d107030080409030000c034810340f0003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 994023642 1250 994022392 994022423
    0x35061f0908070f0308040e0612160e0a05010506030402010c1103030301090527060c13080f01050106120b010822050f0c01021605060a031104080a0b16030b091f05090c030103 76
    0x283c2444100b1640c005941c00d24007070620f450007004000c01881160071603810104002c00d20030030046140410355980204900701c1c2003501d075a103091000f44c44c0c880036038142401801550344032412280c10541c2401c102450819034603005100000720200941c1c940004000003440c1c0007a500f08030701c5285510b40344101d624000c94000210901d05040030200ea2203d00040d0354a20f1120042105100300302036418515600d0a10b185062480440002565180c500400140341c114a016103d0301e000001880b441e802c28000a2400320000c0c003039200381c00030012103a00d46104032400f100494100f4244c44651000524042e925650384007100d0041c810030003d165402c001c811848140d5030014005850b11190080417409803103503669a0f04031610801c000100e981d420480000c08501c030b44504201c600e410409062030b40d0048910000307050410500541c595550b1040030381c04060344c2600303440e001c1481d101541c69011a003000b50468203d006001041a00d40080e50480b4444d0004802d201d10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 994024892 1250 994023642 994023659
    0x42c01201303060506010e0603040602130b07080909040201050708070f150c0903110a1707140a290d11120115020a080c121935061f090807 61
    0x24040e0020409003007480240001201d0340c01c1142c220505251001c0310b01c50741d4000580e29402501d0488103940c1c00251542c104090300c4204c4000c0000381c1409003010407c3d101d12a242c4220b407507151090201800242c216030042080c0d034607c940001d00c1607190034aa00c2e268845609003002900c0c00c500000c501450540c9070300400c00c00d2078140e51140005403850384c0c1c90f03013814201401d99074010140c84012854020034401c48083c0a24600100003203460450401d03441a00001741601890000d04140602da0901060f2001150001c0b0401c445050003041212603006189060901c0f50420030100c00f039815001c081d1208513581202c0d204141d07602c180110407114410a640050780040d0901400300b071140307014103c911500c5d0b06480c5029511860515940d02007098031240c2c10518034620f440030b900005022017888045c80c88400002003400841c200c040c240070541e80d614083c000980c0707503107a42000e601200c290070104d07140380c203070503001a1001d01607000d56062880340c0b0100180d40d51 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 994026142 1250 994024892 994024897
    0xe04020301050f0111010e03121902040f1203030b0909011e020304171b060c0408060a0c02060a15210b070f0c02010c03110601030303020c0706020c0f042c0120 70
    0x82c0000d02c0e0300ba46604440064a00008130203155980303550b100c0324800b40c400c003071005210307817000c42a081ca4180391122002481d41d01040a500406105020600c40c000c2c4c106200707800d07550048141528103a081ca0120041e1420b0103142d5080b100220500c0b2892005402c05440030b030141c1500c52407e50401441c1d0100e005c200d6018014607510800d80080002030350003404402e544034541907840f4032821110f8a4040c0650701400c0c2c0010000b810841d010f0180422504900340210900014203c01d10082d0f80705d0b809800000010350300c503081d80b100203800403000003e02a00101e00c60000c0c0d901c81b4a00e503d13084990641d00700a241c8009083d0303030321070107550715800c140b61036520b41c2002c0343c0c004580d045003201080701401090b4840006007641001840d0095101303650250752120307041c4100b070a00b601a800349065600c010b444003075558550010039030307840066500081b2122080070405d10707520960102005409402c1e1030710203449040d000510709902401c00d0300da41e881521070894451 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 994027392 1250 994026142 994026149
    0xb1e0316170c030111030c0a0908030f0904050a0b1806061309060f0e0106050301030b1003080c0a1101030e0c1e150705070b0406170a0219020609070e281104080307030e04020301 78
    0x1c003170801c00140c400e4602c030003622003005146000300304180c440d00b02a285030300002400d015900e01150703d5101e4074107801542d0b404030340c00d9400d0201c10084030100315460070312885ca03259030680e01d001661580f107200640f80107d032898080000a40e07114107040c024902c60040d02c40f4115a0200482c254014962040c12200c95075200742c030350703071840d01e440c581301c00040c0612800501200c4000085101c10000d00144680175014100100c0d039450b0440100008c3c03440345041c0b40c03e100c0c06500c09003010428000c02c10b8141c4c0ea801804104a50b1419481100070300d8030352160101148039a204500005858054418004c5130703070716a1a800741c00943e000d10b01c0340c100043c480201690705800643c20140d003000c3d844001504040503102c001e03000d80050f80051005030700090800c01c101c241002518020300c00384c407040f43e442c10034034480c003084002c44000c400315220f0000340e0900c12483d0360104800051201c200e40e100d07604c80042a0322548140320560000c0d1080c0303400307001c3d85028404c8078100e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 994028642 1250 994027392 994027421
    0x60303030e120a02190206041203020d1106060a18142a0301210606030503041403071d0c070c120c08010e06071b08120103240b1e0316170c0301 63
    0x725805c03200914081d01c2c210b1005c981004080c800022040c05913000f4032a8907200f0f8011300809020101d0081c02d82c0e000003103918a07544402e0a01030951110920349040d9015039038850245295488054054444251161ba0355500242040b0110400b8080da044c18600080f140c074039001105480c2015000c01c2c001c0448030041074920014840028120315040c91191001080380c50f40d0b034813000d05582055000c0c3c405823403207401040c0246020b102d040e01030044282c402d00305a80e5a203083ca032403900142074900f094000208841444600480784008003280c0d00c07220f6610340c903464400000820344c4034080c5503600704200610f00d004080f803224441c0700c0315a90090180c06008540264003280d404c1030b1504d410130400e885031420819070703284c045c6000d030700140880303d005da07202058031590506e1288040e00d094030030702e45903840003904010b40d42d41c088000e1502d02560001390500c0441c100034107a90903405400100846401c2d5040c00ba85400c00607503518400100a040c20b0301e1045401c1c285 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 994029892 1250 994028642 994028653
    0xa1a060c07152d03090b16030b0a1206090807060612030806040b1f030f020c1b0a0f0e040804050301022110060207091a030f0606040b12060601030f0f060303030e120a02 74
    0x1210844041c0c00b142c043c0d21454081481c4801d51900e00941034140d60900b03da07a11849072446080d014021415039030b030203840900040d490704504603000c02805e0381c010841a203442c44001440b00f203000340c490103900203008200c4c90b640e4890b03109000201010072008900a80c00043d518546445180c8210102511410b98080701e440e43d4900a1540446401416520118001d154034140f010b1f0502411001c01441c107036050b00044280c5400c5c0003800351054445103000c1c00303061040d00c241d0044410a00750040c8640721460f00304681c1c050b64004980640c40807030341c00d0301603d0880011340f9081c2d4810001030b042c0c941524000d02001240140302c09a48684d07004c201d0301456911908180c03d0712408070101c440e050340000c0c20100030020104255022406014003460248241000e25104a0395a40d0080b1081c1c0542e07207810004058034140356846007551a40c41454020104041c0c513103030100070140c0c90345005001040c100b4030b500c0051045407121a10288007000704c0b4021403c2e90001e00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 994031142 1250 994029892 994029947
    0x803040e0a0b130533281206061a0d06060e010203122a030f07030902011709120f12060d020102280c0308250b0a1a060c0715 55
    0x10180030054600703019401c0030f0132180503034084424481c81007140422036031800780c00c0800704001c08580440303400c1540c6c015030280c12410180e810110464501c5445080c402040d428110010a000d501c00c5420100001030300340e83d20400f070000d006258010804200c1d881d1610800c4414510390030380c10703015900408c12801c0258143d02500e501c0300041d1400701c555030300400e1100c1007490004014050550102c103000e03150303010342d03c1030b64000d19030b203001c10030500541c0000f41818004200d06034000c401e580461448141400b0617408000c030b6035147c0399030b500c420003251910351211032180090300e011004100a4036050004041c42a0140c1c000c021060f41140040d15042c0f003e0700e0010713901034280381940040c0441c1c1c0e00c1c000079805040d000b81c030380c03500e900322003000d84000175804400c0c00c1c4000e40d04005044420041d82101c2e01401c0041c0341c81c2c1c1d01c2424183c5030030b03080301c40d0751088001c01c072a40c00c91400609103050314008051488456510305041d501d1440b41c8c0c8103880d0300000054643c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 994032392 1250 994031142 994031179
    0xc0603060402130504020d02071e030e01080415090503090102010b0901180509031c0203071407020108010b0a020109210f1707031806230c070c14060f040803040e0a0b 73
    0x106110701d6109814040b00d56908001803c81c1d0100300c07c4050145c000c5650f1040c08501c10003c3c103102605041c1d2076080881359401001051551003040c1130100d9200410140094004001070340350200300708100d40d4146090944e901d801117140580191308000c140e05541c18034964060490301c281640c422a9298000302c8006010003c02e8004944814082070450390702c03c05e107801c10208030980043e03a9040c50341c0010100400c05442800040c820441040141da10142040c112066100026211504c07600201e01521000401a200d0100560184120740d1200316408501c0f150781c442c402c003070001d03c0c000d0701e10321088055002d411002c50700144810740030350407402c1034008080c00308647c0b03d040c6c0e0342d0350300f02c5500142440f202003c50b039182d4603403003500c1d29880d004080c148050782007010a0707840c070343c481070640601441c190b1802d030203581c0d0352911401d4030742c40644003407403946858403189090343d20b4006106440c070000800012813a01402489a03101c41400600750449002514080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 994033642 1250 994032392 994032397
    0x405010c02031e28050415030605031905122701020105010303020a0f06061a0705061b0a031109031c14130509060f04110a26010608040614070f0f020c0603060402 71
    0x402504d1003010030101143c010420580d088a075180c880649075410050340d0b00a0301d4450a0308400d15151410500032a90001041c003218150b1941843d002500c500e4010705081442807807942060010480194441c08128504c0080c010300300c07442c5141c000e81d0b00480c01d0361b00c01c0c8000740258108506c4c920125140c810b000310301c01c1c0a801c0100d00b45175242c400850100790b540d100250100040b030250108a010300801e600040e015600b44038803e2000148400c6118080302181403503520902c0910000b810300c140e41246500174251442080a94000e0842c0f4104441141c009019600d800c480111b0f42800d55016802518004250700d0405040c00702000700a42001d6000140b124801c0e2140c2e224050306800c5030744070000f04d442c0d54030040094001140030001c15641c18840c060f8980503a007240003141150100d14080c220f5451314284800205100700c105500b0307060301070401100310f4020340034070307415081e50751203280c0c00340d2080d000ca0319641c81108a6503c00c40130404940b41c0d146c140c02 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 994034892 1250 994033642 994033657
    0x3010c030b031c1b1b03060c12062301090e0f07080708010e0106030203150a060203040503100603080706020f0d0207060b0a090c0207050f0f06220b07030206041712040b0405010c02031e 81
    0x10f05c80f8881c0941da01c800d104520551045801d643c85611000d8103540c0910158108042c1c40800e000807803c04e0b1380050226603140306402507040c0500c1c40745c411b0f0303c58041d90004051013448100c0341d003482220a400781c90200d404401003a4440301040d03016109074040307030480d0351f111070fa404640d08180044000c1c1d84040c10302030350340c4d0801c211030002e980d03039801c4840140400c0e0019503640e031030070090500308080381e82080c0032245172680030004141c2c410300305c0b14096800040181d07940c81041000640d40554407680564502c04101d14041007050784c0108602c9400320340b40c148042e9141d00007420741d0f41e68084900160031000080000c3e0034020481c500d12300000b072141c1d070401c1280000c14a95082402c01038035203000e1009080107020710804400c00790641c02021807078040941ca01940d0f40101400041c0702955140301425254902e5040c2d07107110068008404203810107042c0740001c2e06082d1403c1d2015445c24009800460001046a81c01c0042c3d003110010584601d25000f00c0707800401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 994036142 1250 994034892 994034903
    0x2100902120d081501020c03070b03091603060228020d030c090527090d020703120c0804151713030c020301112b150905100503010c030b031c1b 63
    0xd440040d10714003072041d02c00c00900e9079100b2410b813801848825602003404080b606540158010303150785d44000c00c01e80156800344409036601d844c0e115a86192098420320440c400740034070380120801142d60001c1c154040003518041d1a5101c1903c60006040301c1c030440030140c4d11080d18952801d009400980484900e030034440c03109070f41c032004a528800c841d520008005084200d5040720040d000803690000005001813104840010000e03551701c1c403500021705000824501f00e10201d01c070f01c14000020740d00c1140c068a480c0d8a9402050800ea40c04412020a098001881100c1845c103d050322902c003850350120041340b142c0742a201007520460503070700341d500c511200d031403d540300c0c00408000800428010016000c60740d10341d91011465034007000c0b6410075006030a509003442c0448103482e00b220000030755032207641941c2c525640551006405500700300c0001e1040307070142d000d0030041c442a0161001c0303c0399001074524500d40e13211031314007240444144402902c400101c4056203440344 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 994037392 1250 994036142 994036159
    0x106050d15061a0a020f0d0f08090304030c0b0433030b01052118030a052505011103220c09050702191110081006050c0a06022106090702100902 63
    0x10f4070810418125000c010000d10400603004003141e03810000c0309988608280542003454800500520004d8141071181c20042c0d60b1010960050701441160006c50b44445445e140c1950b89605e0026500148a2001c803c00d051640144000c4160441e55201c191303004095060700f4000320a40061103003003c614100107081c42121451010071005213030b9880c804464141ca46800054000007540d102c4c11000160800d2011540d100e401c034041c0c0300d029800060b0404200000804e06880260881006d003046d800c1c4079501c18200c01141c025401008400e0070b20a460203800032a0744400340511004028001400c02042102007960061350010882e1054a0890314981441781490078500340c161500d46180c120701c4402d140c02ca03101c00081e0b0483c201726000d89003c40c8100300780d010320b00c210018002e0004442c0079000080c0700400da076640c400c90454440700d502d03e40030208854615407440307400c200c4001c1842e620f001e100d440d100740c1e2160700920041e040041d107803000e0602200102d820100701d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 994038642 1250 994037392 994037399
    0x14030d09060b0303400b030a05160503040f1703040606050109090b090415020c07080309090a090f020d0302030c100f1406150c0c091906090e0307020d050f01021b0706020106050d1506 80
    0x10740b0b805c000300b40003002c450701c0c8d01b40f070385019003100c90181c01c41140c0780425941c0f120302500941601d60041d0007070440003c45240d400c00c20108825810320144e03038440002040100a04c9a104d0320a4490a903111030403c0c3d11070105000301c0780e400307640a0344141000300050000c0c0012103240198419070f0405030070041030a008900c0c0070299040481140c00200c0c28045130b00308070203059071290500b40140009540c64860b030b0001590400040e00805107680d0070b500b40744c000c01c11240001c82401c2242d80542908918000800d41d01c0d0710102d646044c05040800c07044018102e0f4001c0c0b000034030750714070030346996041105a408100f40c0b1413140544034503100c0541e61b144085100c0c403605071807801c0040006a084048595640210800600d03180d0301da8480d00d800015181201c3d4103441c035001104090820601e0800306081c800340b55800001e20a810244050300c00035220300440840b111035803643ca099080c0e81c443d014198003c41110041d1020a041880d108165004860700080381c90304c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 994039892 1250 994038642 994038757
    0xe032d0307150b0a0e0c07060e030a11060603010c02250803070b0105120d0e01111501080a0c060f0c080a03090b040c1a0906031314030d09060b0303 65
    0xc0301501c0d2680c50441103031503251940500201003c044036804000f9013000401c209031751020341500500403020420360b0801c0a07591020040406440032603895802001d0010004544085d0625050207200c001c1003c50805004d544040b400a40241c507982d0f41c42001480a482050341020701200305e4000080d00c9202440240303849030051a48490303541c14002400454880c1103804000350740822104055982c1c00015800201070902c2d0500c41041c0c4206100d2400c3c00700c04410140c0d296a00000500c001d000400ca9840f601c04d91407103ca060783da4000350b03a821486000c2d203010441c418000313000192034400a00ca07040003403c00003000901a101d102070143d040b02e00321400a03941c48180140c001018400101650424a8601c3c11820b40041170140c00082c0805102c2d2500405480410891404c008290444442140e8985040441c290060880c0c40c106540d071034540400700708541800310032201034072500003030341c3d14529458103104002c084140e10261400000f5264425241 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 994041142 1250 994039892 994039897
    0x303010602010c080c0301050f030a060507050d0b190b09040e0724020303040c120f12020a0c08070506070f0606050310020a2006040f030e12150a1415010521090d0e032d03 75
    0x210690342e0b00791111044407880c41103c21388072020b4851a480043e82801081c0b004020060741d90034800d440d29014d19001280103444254a1142140600c0380302140070350414602c4c0c0301c0804130420304002421300d49402d90300c030301c030613280030305220250f003400c0c09040c1c205a05114014811500061511400e4440060162100350300308016046030032078400b0f0003125030441c030140007028042c2103918544400a9a41d100c0e20300700800c030341c04130122001070010030f50088008050203016149054030081452000354000031050000c40d410f8400c1280c141c1e4103a0a03c2039100144000701510340311a01c840d142503165032012010488103002d00c1819880d0303420b00345e85200c4840300400034550307141c900300c03101c0c0070040c04000c000d0f02e840c1c081d880c0d032103115188581008c2c41e00382070982c1505250048400d0310840c54486403610040103560048181210300070b200d00c2c81c0c5019514010800b0380308071207030344501c81d240364194071040361004c13a0000c1071100c0c0f0b034440c4620355820000050100007030071074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 994042392 1250 994041142 994041151
    0xc1104140615131e050a120b09010b010504030f050c12150c0c0c01050f131d09010608060c09041401060801030c09050103170904090c080303010602010c080c0301050f030a0605 77
    0x80c0e00d5202440070707504119980311000301404020320300b0024450051407121100f4854003030100300582000384ca50303101040d144050b110103015001010b4496001041404c9441011543d0b4a91740001900c140410321800d00c2c80101691030514040c03541e15654401c03003103c28151060300440d1101c07036860b07583c0b00e42c0200701154034001d0041c030362840801c0d040ea114000c2c0030080305d100400980665a04c0401c04030250007007420000c2d150300140100085500620040e5040c00300d00d0742000c03408003171110741000c00c801020850390503503841540c0c50342600e403e8800c031281d0764800000305e005c2c410300c0ca016045480c0060400180080c248141d024980e600780c0c0580f002c5080c080c014010302c86100040f030060591040b0510036175146035903011000b0440c0350102c05422000c0f1311401295a0341c0c200541690b08024030b4801035464204240d140da2080c4120809580b8188040324164080e032804ca2142851040041c1035a2804040c030203c0111000e40a926008100800002030700398890b140c000e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 994043642 1250 994042392 994042421
    0x80910030b0411070c1710290303090a090f180f030801061d15040806250e010507060f1e0c030b062b0e0d0305090c1f0c1104 55
    0x58000c200c14030040318400d240e80880c8640410651002c00c0c581c030311010403100c1b210b0840762881a2032180307a08203049403940451090415445540c51154014041c0c28410f00303c2c0700c2090104c1c01d40c205a620700c500c801d9542c00c140d54540c204013001d0280d01102d001f19002c03c011580c980c200c000c00710740c0070702c03d0070466030030154110309014198040b42c403501400090404080401c00c01c9600445410550303401441100d482a00c1b1000441003020b0b10000c024050444e051800c16805502c00712070b08282c029003802c42d407403503084040d200d1180c4650451040c0c41c4e45242031883d0700c13841b01504010101a082d15100c464401c210034031a0f58036070421f03460500028003080f9a0200606079000000c0c8a0321030785040c0100c542d0341610404810018071400345c0d5400c0b2000340390105002e0004240e546a882c003405103815000754064008901c95050704068403c1e0b0865001000101180c1040140d500d4102d05664244c640c040d050310030342c003070150f0480c0749212404000102620300d400c070461003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 994044892 1250 994043642 994043651
    0xe0a1220030c10031e0207021c03090911030702010c0f0e0d020d0203060c072f0409051509100501210209070219080d140f0a0b060702120706120204060f0c08091003 72
    0x210800d2400c491207140e1101c4106507c4c0c41d0481d00007412000810b52801014010800b2540803d4060f001080c010700401c0c2c0144004060b150400c0700304e410840b041c40141d401d081c0003000300d0b0700c2070605510003c61900c1b00c10054201e18203110910324840ba040741c00c030b6802c8503444c0c0036a40811029103e1600c1d080307205d030340c2c03102d910f0800c1e0102444280e46d090956160040d80f036041c0280c0c11400c801c2030a81c3c0c00582d80d65142040340c6485540d01b41615010b00c01024000b030588045159104215400010b004690b650400c04044110800080c0e00131483c070401c5000503d0182400742d001822481101d0000380392082c880f580d01942c00c0101c8114400048a8100041da4000c1c8422031048a1042101d850f180c4c200b40c4104000420501c00a0307600c4030596103550310141031b5480550082c02031801540c040c0c214507a1814280905004100c810032900f190410303e008403810b5503520b0ba5080c211b010b128100ba070b880140c03071004507908c440c00d101c1d40016032070b9294a09182107082d80c0228 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 994046142 1250 994044892 994044911
    0x7060e03270105041a070606091a0316030605100e010906030317190209180f0403020f0a03120b041e051504230c13060e0a1220030c1003 60
    0x741100210031a000d84903a09009208160303044001c1e5011218401c0b20780200300b082c44044201840744410080410f0b14240d408540005d9a80c07144c11042e541c5400b60394901e032090304056540c3c20080c89020810b080e0a001d00c00140281c2003d078000281d001b95820141e281c855641004000340c00810005513111004c209040e480082e8031480e840d0002900b0050070326525083c103d5003035250201d5440d0b00016441c0454440034424007030428147c81c5e440240c00d294020503d103a0080c0e50030380040c4035103181b86915a0b070204210300d6196050300e031900041840c459000c0500500c155003980240d41c0c5013000d40b40c543e1b407200000d40007070b000c50000e42d600e07259022800840300144130074011842d00e60f00c9202480e000001013100707500c040214001d84d650101c00045803291485990b03003407407040030005126800c0103451140c04c40440784030660390b0b2204000320805208540c090a1003202806030030f08016030810402d003466016050300c100b1000392010910180001d9100e400296641a541 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 994047392 1250 994046142 994046167
    0x70f06050a0315050306072a060b0f010e090712090210030c030c03060b0703050903030f04030b0403030612020603060108070c050d050a09050d030c02090a0b03060c09190305120903010207060e03 85
    0x8168110450358220f07501c1c0d050001180c0d640800516460501819443c03002c80d40407080d20714034900d404008130381c01111840c645035026094005070030b4003915401d0074100c81503000780c10414480c01d000e014810303581d8564100329982c1d00d19280480006580c0c00c51140035031600c1c181c0701e0006850f9240401d643c0c03c039403002811039050f5040b0108061070701105200c1c142321502140c0380c007509071400c292540010320000e42103124141c1c05190a00c800540081041844e243c0030740f0035130003a01c042118607502c0c5880c264118607034000940c450010070029003c2c1d806245015000314091070024601c4e5040d9850340d2500c2450481341022a4000c14071000c4184d000080382c000d410705031180c503d85145580c0141990350101c1000b440b0b500420001101203145900c9001d4a82009045601c80e0403c41c4c11403106500040006002d4000c82050185000c20310440004070ba50210040c40d4032050f060030302080c0c0c0c21200015516540030424a00400c9140c000d0003072051038000076658a180030542d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 994048642 1250 994047392 994047401
    0x72904061406090c2d0d1506021b1e040f021e070b0a0203060111370515131a0708060d150504031b121803020604030f05070f06050a03 59
    0xc240f00701d9100080065986201094800c104a01100440c1c440c881483e01d0f80b00d0040d40d000908000c9012840000f00f070352942201161072110001080030325280c00301280c544480340b07400c058184030040c203000c2c179007041c040d0050140c0c0341d0b2035945000c02d0400c0000702074440b40d4090745045a00421511824070010304000350111000400034034100301d40d03580c0d0140000042032110400d034040000f8105900585136881c00c00b1051081d522a080481c8402c250701e80d046c0c280d007105d1100c025080590381e61142c0c0c00c0488903000790041c043e8000405500303490700e20003441000054402c042550006640c90144e04a116542219100510b0101d0008210910080040f031144404001d003d01081800c464030072120b262100110700755455080076a88442c0642c2d0340c1c00c0b0725000d110070b04280b01a02185480c0301100c2d5545406c2c8d003039405078000184000e800f0196012100300010000200034002ca0b0390b0680c400d41c151001c59a8905080f03018a85a6000c44080340300041d6560000340e1521a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 994049892 1250 994048642 994048651
    0x2030f040c080a0f060e0c0d0602070501060b0723010b0402040b040311090f2d090105090607110705010503041106160506090a030c02010f0309080a020106080f0c060729040614 77
    0x41c9440c0c019070b100c007001200c81c082e024017129590148201d141000740496000c003034000e001d1110103c42403421b0b4000b035110403001d50f8a0351a1034170109d1100c140400321450160019025106014581c5c950b442c03484590480340125942c5030815100342c0c0b518005440289105522a915a880d6080602d5680510714a40703200746803040c100b062070958a00b29940100d900d1400c00800c090340c00703120345850355801110f01c00d440000e00700810074105401c098170a800310801c0c0c0c0c0540d15449401c0c3c92070a1034810090709504412018001d40d441140516803017401a03400400e81d600c10b2002c039610394065202c28203801c1d00c3e40c91204c18081c04124694210311210001e00c100d040036240103208140b0040020b04000b1480e000050440c0300f41c01a915983d0890031445e601e06000c94041e0083c0f20b00e100d41d000d41d01840c41c3d6496a041301060050b6283e0016000c180b43c03911a60355600a0b0041103c2a0400d03585124101d07801c803805000d252081b8424180010000b01031a119044c0d02d40c000c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 994051142 1250 994049892 994049909
    0x210c0702090603010b062b1127030706110102091908190c14041506031506030623061312031707092102030115030c06050307091503020d02030f040c 65
    0x11542c05592a0b1b207044440038100d01507140200c1081e00e55000445600304244079019040040d10020300340c01e0001442490f03c0040e170b600f00700004806007505400d10b551320507072640240b002000b400380200007038004006000d0005140c1100d0f0800180d4580402c404481020648401441042c00411101d01203030080c4174003024003901550f40c1d0303484104a000743c0b048465010401001a10f45070000920f000e8401c041c49041c03030f1200d100500910750880300081d41929244009101e5001e1b02c074080a07228481c481c858062100b001040c022500000c62903049a010085103600d07250f10907812022f010380344c50101c840c11300390800800f084500c40c003141108508100340118107400c0745078082202c042e114041c00d1590700807a416602031118201a415500302610782c580f039030480500d40266480303111420300603501c0d020100ea050004846a03804200348400510844a11100300750007059146005440c181e084a407240c1681c0060300c8072248843c059083c0400c01141035061405803d810 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 994052392 1250 994051142 994051151
    0x5070503070b040504090204390c02060d1d0a0308100911071b1205100507030507021902041e020901020c12191112030a1806050f210c070209060301 65
    0x4100700030b46100e58810740e4031440d0f898008204540361508509940c1101551100320b003600700c4c500703041070420885040d00c0c40c0c95480303c00c000540a1080d52030070301e4003c0c0956040c0920010024000c02d203002d808001540c104280018246e420060542140c3c4269108015400d00c130070026000300343d0f6001034520318240821400c1445400e01a10341c2203030818034160301d540d5a210301c050054041d8206040d24401d00c481070090010005005100c050000b40401450351122000c404035a8180d8034240160401e0f603486003032041110a5140c254002080090541581103001054201c41e40304044402d4021a80c500b0640e01413003803480318002555080c0503501e1011455464580210400d1131b40c40d0013100b087c050014446920580c0b000280400082c1c1440b800d0840d0350790002003119000441160f0302c84507501a218a01045a00c10740340c490401c0ca0700317110145540c01810a00c61011010131402c0070741c003071000c11640948030101d00e0540d5844140140030106030b00920b90740c0260b041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 994053642 1250 994052392 994052399
    0x51c02072406270c120e010608150609070503040809180402122d030d0f050f0a0603032c04141e16032406120e0c01020606060306010207030c120507050307 68
    0x11460505101240d000014080c1400913090369480820040042c03250720707000c070030321707200e4030550000c820b58107403038129103d51301000e13840600d1103000c480d103070f8000c951000400c5c816070181d4083c40c0c200303200c3c0c4401410039a40c00302103540b90f66080c41c2d50039042d03000d00c203000550600302c4085006600d02d40140042840103c0d01c844880300c03c040c2c0c680c101c080e401c190440b030301052040c0e03034445042e94411700044170500c0c250703000790406803880000b55800302c0104241c0c080c0d80c450b001c101e96040d20303118600c061044403800f8502002c0386031089615407075041c040c9540c4500c10b40d00032880715000c503002424040702c0e4001503441c40615002c4540307040140f000144540d082400304810318940421025202c2e824080034101c50441011401240304021a1003a0410440070290111540410800c500244500e40c5c81506003071b154056004607000c120b103820031038000d551141041c011203e00ca552030307484115420480d400703a030f029084405103000b00441800160001c1204500800c030301070a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 994054892 1250 994053642 994053689
    0x150a0206070f020c060f09120a150c0e10080f060303071a040c030b091f1a0d020402090d111002060903030112052b030c0807051c02072406 61
    0xa00791606019400380300400143c820040c1801001000c1c1071795844135590260303500c076900b06094043c81100400c0312070b240500000b441d03080320780c0c005601f1b0341e240c241c00c20000004c1012031414010021902c503030f20566110400a09603600c003a581d01070551a25817010000c4a002401030740c42034104114030b4010441044541102e000c8600c0c0c0000340d42c40f81d141c600007056941c0e20052410748118200200c03900301042100711810602e4020036128444070101f02120240710284180e14080c01005943c0d0a010894020551000e00014501a40c0314006445286040c1d411200c01000c000c582c034031420a42510201c1400a0004040710b061221129481e80414010601c483d601d0a9106043c40000c002000304e5815440c0c001c801e8ac40031210881c880140101c03032001180c2000d03c0080d00d00c5c4070b100b0b800e22540c0c7d290303030340d505100403064032040390003070124510020743d000d0003144003085074800c0402c0c0c4074004046440030b01e41d51180b0038054403266400b41131202068030b040d120061 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 994056142 1250 994054892 994054903
    0x30f050427090501060e221515090204140a05040606020703031202041508010510090509010b130503070b0306120706050910030e0a0c060207090203061f050708070c05150a02 76
    0x1401840c03070449001c0c1c590200c500818041c030028141d982081c100081a001c91698140540340b10130504440201c3c3c0d000d091016116084c001308543c0c90824048283c03200d5a02807500f580354049501c03d001e660741c400c00140d0f00940c11803094200c2805900d030b074903c1c00d80d07a400000e00e005da40500c03482e864454041e4031095a4071000d814440750b041e216003007400310f5044401900b40e0580090300a110150002e01c12a0b00b405018007851103483c1a9a400d401802c60348212500104040d01c583c1c204100140b0076000041500880140d214012031540c0c2c3c2440000042c2c001d90050030b03200d00c0c0500421162140d0144002c0d03c03500441030500010f41d00004a80040b8029108186403400d4144124002d01c82c1b007941c045540a200444802c010003890400b0071100390380c0c201e030181c6813602d034030504a10060700c40c950b00c41c1d40103512075256075403019150b40e0b80d421030800600b004540e8480c0ca05561005200322000036092405020521f44443c074046403039800c801e42402c1c03204050010750356a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 994057392 1250 994056142 994056179
    0xc15030c030402010903211710051201020c0102030c09030c0901061d18130204200403020d05030f07030c12050301180b060d090803150111060406181707030f0504 71
    0x1450000000d415039000717042c000011684207042500c0390780c2020a82e4000c0c007880500350001611258100c90030707902400258010003410304800e442c0c61a10007080135420f182100d9041a540078000f101c0c55450a2000c1c500c502044907019964501c0d1000305070504c02d0021700c0901c50501d140051001c4c0ba4800c05803805074825104e0071643c01d0141c0001102d10f44898140c0a1031103c81c001c0000c1c0d41200c00030b207640e0f01d00c00d9030140111034400d8122030a001c680e00510070300310000e11080015281c8007000001d928001ca00b5a898000140702c500004e510070034054010901c116103180c02c00c0340404020403440800d140c01801e41d41012864072030b83c0350904582d1400d58132840303429102d81d5003c04442d0901c615801c10810310f2030074602942c00e50411100f40603001c41c2d5842c4595954042c2c2070b400c0709014200b02a00f80d0395901c0d034844000342030001c4c51841c15101045c0d0200021020380b2803008220441c7c55568503125140f0b4028441c9a015400c1030030001e0500c01041f20030140504003208 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 994058642 1250 994057392 994057411
    0x50d08030112061803050a080603030906161103060f0103140303010e010b09030c040c09030501140f0f0414060f150a0b250b010f080d0519080402030f0706020f0c1503 73
    0x4110583c204000601580415840b15a0940445204042c0c22500400601016403220501d942c1c6039800c00d0b850340200901580c20003010040460111800450705007124420001c00442d40200d01c003280c07415100300da285900008030740041c41446551810504c1105000004505c0c5604240c00058100d80601c1a448030302c0020801c80e0041c6e805001804000002410820900366040d500810015851009882652038850301010301402c108116200e81c0c520305c03204445481e045565040c4d41c900502c191a0190404030304001c200c0c080c00018000d40c40d07440c41640d10700b0503003104200444140b88280c80348800769010070054101c40107503a801611520010341220340340395020b0148012820003004403483d03800201d1440750403500780c4181e94024048500002101009079100d00c501200091007090410b80d20340e00e5449181c1c00c42c2d0103032010b41507402c0250048002454541c0030303041900540c0108084139081c00080028120700380d0215240c1154144000103001c603031001400c00c400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 994059892 1250 994058642 994058669
    0x103030914220b0427081303050616120b010206070809031c06032f0409080405030d09061e0801031b1d09011404050316230a0507050d080301 62
    0x7242d0344110440c4000c82d0242003040400b01080004001040e4454109100e507244c08002000e86080c9420441c40d84081c580001080d0346940b07a00c0050f8100d120a8801030105040200005406100071405058403000e05100d02c00b00c0030703001d00428500303016011182e00d0301d58191008d030b9001404580140d203d08203800151a4015014158442c80f00d000713119036102d102025180d10142d006104580c081c0b80c58145c01040100c01440d1020301d5028483c0c9051110355550301c9241c90350090500d47e11030301602d031074542e403600440e040c08207042c00940840d005580030080c00340c01400080380c080203510551040c0c1019400540404810300010780340040200040d0f003002d8440031004003614541240f01c4e007419010005600b84d4508841c03400195080040009100c01980c060038012a4400d010b5810003000c480340c0210707603103088026511a40f41d09003032001c01d0000c02c004110f6282d4500038087c04821400c10b107284c04110b501090003088911040c8000c01e0103031040d64195451201d4803070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 994061142 1250 994059892 994059929
    0xf081b030411010e0d0b16020606010915120501030b0f070e15031503070f0314030304111002150c0a09150905120f0d110c100906030b0111060c0901080a020301030309 73
    0xb41c140b8800c0d032850b031704550911161024052001d071a0752180c480d440c80b1142019844008036200c00c800d907221800300e4010401070050000200c0383d00000511450b0034103c0740580401102591300c00e17841503404c0c540c0901401009800b10b407100740e0144490818555100310f0703001203003000d18607040b0751405c0e50021001c104020750107400c0c00c52403e0010101e80304642c842c601c910290f9131a1208540b070140203c9019842c02010041c0c922854101e0b0f003e01c500c4099900b4001480100d080000c214010400903100c68070350225101c2c050f210f5540d2082d04e80440c40c2020303140c4132440d040300402c5814a54140110740d40405164146e171320544231814454900d200c0c45152401100310102d590240545208045600c002e0041c00650070000710ba00428000b428010340c68000300c10000001c100e14002d201c0c503400b135007109171540c006240c03045a5640540015082038000d4500c054001d1000443e54070540e4011780b40b80d00600000021451540340d40c0d005030140107d4403403224a090040c0104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 994062392 1250 994061142 994061147
    0xe10090b0d02160f0629010807110c19050102010c090b09100c050609010b1e010f030e0f1e15150405070309080d060302100c1a1f03030f081b03041101 66
    0xc0c103182d0380319544c88014403052929001511a010203c00825812000400d14a0000541016404041c5c5802031180c940500480d481c0421039400343c0e9074441c0f904503c0007a180e04141c00109031144031a80b040e0b5090a00080c203442e200c01c01036042014941e4203005182c4190111003080c90100d071035005035800d4400c00d0300d0101150402070f140340500000c0010040303040d0403039015070504499190802c008840c0140c80b48403050706183c006a03840300e540354a0750180e07004030404500b401c1141d0300f00e01c00341c1c2c0003442c0c503040c415040000360303503800c8001081d00100b0000c0d40043c20b00790881e00781e02c1c020f072903001040070540d50144159101c0380881d0001380070341d0280b0400c0e074005481c15541c002404030000a01038034803003203000305c211680481d007642c4242d414182c5194816400c0c2409500b44200800c0c0e00301c09090380089041c00440242c0400f68a41658000c510a03141e404c0c90340c0c003502000d851018000c0c2245038040109500380044480c485c00c6036481035100780c40c000d0702e05400004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 994063642 1250 994062392 994062427
    0x1d10090e010b090f0108130f021f2708030d150f0806060102071e06030504020f061b06011413021b0102040f09051006140a0c0507060e10090b0d02 64
    0xe1411a24888000304000e82150001c0980305016140403813821820700046603011412202c00c9081510b00e0300400005503500d0030928028001060003071044189114010716411a03000e075804143d0110001c0c1c0140c003d13803207070f40b85a01d8089401082928184020703440c0d205141d0910b06c5280d580141c07110790030541091401905014038080d00c00e540380d1285645d11034041d1803480c054461102d0018101d49001c3e03440d65000ca0350ba82480c01d50385813460076400303010301601c200d90140c181c0d050060070b5200c0307001409003c1800c80d42d130040c544001408508064043e00a00010a0380c0c1d0002500c030b484103c021440d00744800300c0141c0d900440d0701c0c4038104050801d0306050035400010000303014020007005030f00b62165000d04000c9a00d0384a050840b84100f881010049412804d07c407032140ba013070010340182e02c40c0d030524a0040d05a9900c031401c207a11904110046106880c40320200e0500300780d0020503170114140101d4031410a8080c40040c001d2020943c451600022010540c03500d5000c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 994064748 1106 994063642 994063649
    0xc0607210606090b0a090e0a14010803070302121b01090b060a0e0105150a020f060a0501030317091002030a110304080406110318090601030e0a0c05101d1009 69
    0x4c02a4641c2c00c00d803100c1050181c01030b000210400d92104980c4602680031b400200c0c020300520100103500c040e0440704142c0c1c8103000e40e42c00250002614540343c206803541c19100d800b064594510200d1400d441038403942002441c0042081e0070071400d0081ca0100e4050048036203440c14160b15600034130410368001c1d4807250040080204100600500d06544180c81880e02140259464240e0549103203400c150790320300410a041d8015090120341c5180c0b410964141040382c1c0c0e041d680c5501400b4240b10b90750000201d444510300f070b07101c419500380702c2c03880700e490f4a2b02e401c040d036103a006072098a01003800b00b5004000940c022003114a9080c10324403080550000600340000c10100401d03240c141650344c1303021400040200003010352544140c44c6180d0441c104800c1c40110075524003100140540f00d144070034003803102441d480e000d43c0c1c251040110704030040ca080351521056030 = true := by decide +kernel

theorem cover : BRFrame.Cov 993884892 994064748 := by
  have h0 := BRFrame.cov_init 993884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 993884892 ≤ n) (h2 : n < 994064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
