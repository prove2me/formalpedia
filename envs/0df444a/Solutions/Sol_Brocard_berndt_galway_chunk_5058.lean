-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5058
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:36:39.308073+00:00
-- url     : https://prove2.me/submissions/f7b8fbd8-36e3-4e8c-b0b0-f3b843ca9381

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 909532374 ≤ n < 909712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 909533624 1250 909532374 909532399
    0x4050c0127090905190209070c0206130b03040203070f080c04021c05100303020c041109120c1e150f0a1209060212040b060111030301120f02060309061e070806 70
    0x800050389801c88251001d451480000b400424a40c050045644560142d0b52101c1210071702c002810303210310001e9003000100f0700140b507031440785590b01f002c07910041096041422054070307490310602d40d0700320104c0100004140b001b540350030404000104501090b113040c84c0e081c007102da1745402115040302d020725004943ca410b49011803102070484640120b08200e030745049401c40c00d1621142c030040e40175005100e8880441d08250083e0030ba40c90090601d140f402d5140d00c10702c00f00c01d160710aa5503980c012006641c5042e07543c6940079460104040c0700784404402102000b500c003680401030755406d5410808d40494245140940e448581c20342420049038071812142c1003c0c000b480e8001f00712500c00107044204501290400f4022402502400b446a40307050055400070030183c20540c0c1f55200340010071001c940000d005000c0c61003003004001504003a07020940300e4001b50340004140d00000e04204c072900e801102e4542402d01c0e01c4200006050070701c4080c041034070160555025400303944c3c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 909534874 1250 909533624 909533657
    0x4260309040230012606070e0102012003160c05100207030c0b090d1d150f1c1a090c0412140a12020601120804090914100203160804050c01 61
    0xb1140040b030808050000b10b20703d04a6100409004000700344070443d0840c1e110488060203804c3d500342601c020105c0d0b03110000b0689050044170b54582c11036403103a040e100600f0186074080d81001c10402c10071707180d080c036500080780e0f040d140200c4070805c0a003c188002003100003440101c28048207000580e54405400c045660002e12000603109500d0b0409200400381c00155900c243e40c2c0c1e13551541d443e480000003102058403004010717507110614076049201c0f030509500601070740501c04d0000b841c1c90303004141a126800d4580101c2121581e82546001e005002e2055900181d4121a40c0c0c0d11841c00c045c0c1d5440b80e0045005a5464504000b003003000c0207416248810300300c24000071100c0d00480e5152143d40d400c0d400c20058018000d00b80002414402c007000030595a80c007001060510b82000500402081c0c8207006070307001c1c50305091400080c0018401140c607940c0442000d6034038a050090740341e04214040003001001010030802012403000719803a03503c9070013481d0290348000040c60 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 909536124 1250 909534874 909534907
    0x912010e0a1b051e09070210060f08060a0b060f030919060203060307050f01120f0204120807170f16051c0c0510050108060711030f040308042603090402 67
    0x1601aa1489200750507018091a0072009986000d0100c05042c0c0c01c0e2240b052200c00e120607041c15440c65030903c00001245400516164024802c0c4103c401d450400c100c1401a0f540c568005141c0e44410707101405152028801c40360b0211000105114912042c00450024424101d078511555004800305002ca201846110344441a500140c00103000380d00306400254419105280301e03100f90000040c1c1c6080c91203210f0343e100016100c4c400d049090030300190151031962040514543d0811001c281c160b240e04808680307034019030380161944c1007031802900300340c0100c01c640c100410601101c0c03401d8000c80c0860310504004030035810141083d1a08920300311004e40d642d0321740c0316141e402c1c0400e943d0022012200c24015400c9800d1882c2001002040f60020b019081c1c1c0c036040300c2d000841007070050240341d1181e0130501c21240391115000d071485407a0459041120030090014041025a00200b00810200e20420110940c81e070030301c1d2a03a80e43d110303959080f8065600401d240c00752200e03800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 909537374 1250 909536124 909536141
    0x9010c030314010608060f01020a02132703030c020708030708040b0a0309061109041d071509171e19030e061308012004060c170d1d1c0203091201 64
    0xb20115065868400107000343c80c040b11810b0003181040c0c0c03c508650310001d00d00003c1e40d000f40c114a40341608928180c054404614400f9020340c007a42c0c00141c045040310b9041001c0e00941d4000f501d0000d615000741004150341c881d10243d40701340460408030f611101141c08450403100300983e10301800701c0640c09441140c5029041034580a040206100b026009110a020884040283c154003079055a203061a03a5580f031b081742e100c800705105071010711034507000640c0d0318101034803155520644500021401181c81140380c1060300c981b043e1840000503100744031845400360140b030302102e2680e0700400d880a400f80070400ca032194400b85403100303030171515880302405618407000e444a49260281c43c40200074a00f4800039002c005490a906090307905480c1030f56030307100821200e62a0300303050300c000c5400038548070420040818650981e200722a80c045408055454040d0811140383c10a500d04404126141c0c0d001104600c05601108584100200715454080300007440402d90050040c0c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 909538624 1250 909537374 909537401
    0x90312030906061e0e060406061e050403020913030201060b03280f290d020a060305062e02150106021504140607080a050903090607030305072708071a09010c0303 71
    0x2680e6601504010710500162105441c0721740321742d241c5105100848066110323200010340d071030703400685220f2030440c1c0e04001e6000713240240c2040c1d1a6000250807800c01d49030882c030380501400880400d5020300a100080c5540e80c011419443c00e414400c11211103456002071810803601c2050350b40c1c04503809080d100c03c0d055002c200808442503039202600007107080c0c00040c01c942d40611703d01d02c1e10050510b203103940070344220401840c280040d400360801410165010868002030014540d0f410503010301840400e010301d1412810403c080d040410351210301a580005400600c405500050410041001d084801106540f9030070460400d0148010304a1079010b11400e1105060340f0616450103512811410170a5032207880c16295648205825250041018010600030038003a9100300e51003810f85c00d0110901300c1003410b400036507806a1003582c0484c9540b006015806041058002401349140115490021200c081403240113024410741004030200c2100d040612a810400d07062180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 909539874 1250 909538624 909538649
    0x9060d090b09031201170703080a03060b0d140f04050601060e0102030f03100e0a0e0a080a120903031a040513290f01050117041a0a1805030901030c09031203090606 72
    0xc2c0400c0c3e141d81c0034062a802145031980007140e403059210f840704852503908000c1c03020300d165541d0101c068101045041c2410b680b400d001507902c1a0b08000c00c0300f200c144a0002e0410140c00710b4828007000580112011322146003008001000017a065043d2602414042040050280102d1a51003007a01e1f0605c007143c0401071000030000307621b03048103485000d0400d0620f80c0d50040044111603030702c44590a00c0c0d010300e0022000c42d0000004000082e11490015111008800701d40140c0c4d040b80c90880c0000d50b81c14803200e15802a428001c0040390441d024045801c0c41151042c40050021004e0125103180c00040c015892003640200301d4105034404150074605050b611015070000d10440b408512100180031051038455880c86c403680d0b20518000004000040305140303a40002c0448010f5642d8100e40b04810012000078540c00388240010366840400e42c00050540d4483e801981c01e000c04014240005484942209440f00140c07a000071044628208500604025445038000081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 909541124 1250 909539874 909539881
    0xc060c020606090406111c0c0e030d1d040e010e060406150503150916080d080a050c0a0c0206041805100f1206150e0112022b150b060a09080d030b010509060d090b 71
    0x9400a4011081c542c50342110305154000703241d280d20b541d00d002f0001a04c40360840c3c4c82e075086503a2448501f00040c0002540100400c240c1d030031510a00d1144040d948140100300030490036008600e001120414018401ca00d000b010942d20348d1149001c407508202c4200181e90f1030820012200354003030104071021700698415109449080d0030905500240100c0001501003605004040c05905c2d180301d40f52800a24074005c41e030628010740103d1b401a010400000d01c45205c0808403c504654100060a411700f0b010030901c0750700c19840400c00540a100410850a2408404200c140c01c84d90205404948140380c0e9664400c6401c0041038070360b00800461001100002c00000038400d491010070441c0520300c407040c09103603032548280c1a410106ea84001203500c154031801103411100400d0415110303000500302c1d0055115500003500b800700c10007481c0b0013045030015031401414200182007444000030b1031485004070980c09594005540303908600554040c0c4280390b0001001d200c6410b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 909542374 1250 909541124 909541177
    0x30a0b0d0b0a0b0319030c0203161e090603030206070c08070816051009123005060109090204030209070c081308011b0207121712070c060c02060609040611 68
    0x100741c039004075561500380d08000e58200010018440600e102401070340c01110386d021203050303a903c0000c9805000e1444280c56000c1c030b5242e014050a0360444c034105081c0045603180740d080c880e60005802c0c03410110f081020075008104d154000c001890042d4001c492810140070038824050020404040014003868810b81c8041502c1141d12410556603510b501d100b0031003c1d1294030801a10301011035500159160003000440c07825403d001d030520910451030203403180c603840780e04403400040d2200c081050a6911095190181003416800c6041c9821034010407040302d0010010014000b00045110501c82802e0584008a8803035090f2101e0a441e10b00d01030203408003220b030f81100c40742101c000b54064000300e039803819103440c40b000041e003441540314100c05407014440d0a0a0b40001c0110440e0316803030034481845a1b1058445441301203151070600216440314403100c0131500940c06001065481060140c1c215801030004505d041f5000f034400700e0b6120361000380d14801000d49040c40c266 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 909543624 1250 909542374 909542393
    0x603160902090f2d01030f0612050616021504141f1808090d0c2c07030b1e0a091802150703140a1407081803030a090b030a0b0d 56
    0xc0065405201c081820028004203011803054402001404902d49400d000c2544004044d928145004a42c80d0103c0c140d00d012111650410013000b1849003252080c02000c008043e004016500d51050140100f48000d480d0a080c08442500d07031050004602030142440544040540c1e81c02940e040c0c1400c80488a940350303d0511003084c0310305200d204c034601c0c103800f4060300000d504482081c1c03406001d80104000041ca40b0011940c0c0c09401c01c0208050151000c28070b000402801c100030300340554201000800b00003091102010708120032801d83d034aa540001490044840a5902c060780c00400240100040c0d0092502186480d0030580d06607824054540c03844e0095030f101017800c0c14100624054410044040c000c62142941d80d401280010024100c2400c1c0f4503012155070300c4c0103140c0440340d01102065038403040120340c1c0b0a54040ca01407490a40700f085000714504a2568009800c1d82c50310720460509090100c001204204076800605408400a00340d00030fa01907444c184216 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 909544874 1250 909543624 909543637
    0x201140417012009010e0d08070c170a11060306010207090f021e03040f170f0706091b1a13080f03040609090504110d0203150903030a1103041a0603160902 68
    0xa41c28101c0080e03c1c042540b02d140368078000c0070742043c504940c00c401502c000007002d00c150f400003080e01c0c080d8086900030024110346031003407880b5a05140b42909500304241d00c5842c070300841c0c120700011030001d0340d0700010308481d000c1a200c03183c4a42e61140142e040c0030041e84000c161509144460200b291a41d00401060f0081c440710480340c0d1440c40b4070040742c00101c07402070028080d19070100c0410542d5420000601d4488103035450541900c41c003840070f803c000d208440c41511400304d80c08022401c109a01e0f40000070303418081583c5030080303100030362101c05c0440072100c0d000105641c04409550b4054042d0410328105c500c007140400c0c0071a5684c0c4a4410500040c80600703020401072164050305004503000140103101903004810440c1d540b0000b5000c81c1e1501c90310444812303601d10003080901c229184130207192240340511600c2d05450754204450b1204000300200000103089800320004038001c824a150789554100110b4680544905100002c103402100001e2418098008100c07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 909546124 1250 909544874 909544919
    0x2030d030608160803090103110403060c1706061c1a041418070806041506031a040b010605090d060b0301061701020a090611151504060305010603020a06260402011404 73
    0x1030001010201102c1280034004c850703558000300083c186561083d00301d540f00c1c2e000c040f0020716241e520342c1ca010440d0000d10b00d0001240c40038600044408000701c806034044020754506140150588040407095106040e241c10b140c0c2e40c80680038803900f5008000318400c0c001c0d01c1044000c1c2e1500354503a0540b8101e606000445070242c0c1d6071038040001c56040d0032101f08000410311601c466455003405100009003c0c566640c80c1000130104000c2160f501154401c280000e9a60601d03041505100034140c02203000d0080400c0780107072644070710300c2916025400110024244c5605d00010b809440641d01409514502024081c3c2c020010360091040000640303032401100e5079200c0c142c484a0f0400c0f15600650001c1014030140b10542400940c040034800280072400095000a01151482e0300b00380c8141e0340d2440240308504000354280054261414000d1190280d0440c4140c00c910702c290000200c2d005038080340c11a4090040c0000c0303c4045840c003030715031341c561104c660030141a0b1207c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 909547374 1250 909546124 909546133
    0x51f060e09070c050d140706060b071403040f0902130806090d0f0311040303030c1101050a23060604170a05011a031605011e020a17090a0902040e0604050406020702030d030608 77
    0x446080c0944035140b0740b10f038400090304ca48000000c081d9441c000e603862206c1800400c0000d50b0000b8100e2203203c2c040e02c8480c2c0341c83c1d106c11042c18050307111600c0c0508051181d1003044144840050708205a00b107648400780075aa401410034041c1c0d5101c1142e02120b4544102d00500c410720704085105054200c05544109424101210450582d80c0e036222054030400c0c208400e10100b8800d400c2456521580e042c41c550b003105100300e1908540041307404541d00c5550314000491000103c107440c00403403141c0849829070601c4070009880348a80e00c62146510781c02c00c000c4036020401d001c441d1605400100070003024500304805c0401460369030358a4031a006003442d5080807010125514180d038410ba6902e084803081c5101426044150721003c001d52043e50761190018280b011103d82c0404000200d644030b010070800e00003c80c1d01c5402140505005100501101e10054101a4000402c690114080e1120b0800f10002d104580b8041e415014180c5501203190705074004504a580c02c0e800c49 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 909548624 1250 909547374 909547381
    0x7030f080901060e010b0f0c0d0909110928080105070c02040e0d020c010e010318050d081312050a05070b0435180604080a120912030c06051f060e09 65
    0x71801c0711098002c01c40724540101c014041e0313042003009815205021281546400c80d005915403a28a203c1c2e09400001c1110340280200d58013405407001d210620300410341400c001c18000f8803001140c10b07203c07101c1000c40d21400d03030f020306043d03081000b0f190000081005007407040000b0300b06603000b54264003460400c584001003440015142617460180d07800b900b03091001000440380342c40f02501c01410151101c03a84c07140310020944030003a0b42d2241d001014502c10040d0003405c0200c005241d0410119403014180109150f81c5130485107120b24940182d80b40c10001c01034800d0b01900320040c00109069003000100040840105409803141401e014800d140c02001c0c2101108003072072690102090103c19001c82a14a1020300308100601c1c00f400c4c541c0b924502890865510303000d80e5a101c440c980400920b4100c8401809841850200e040c400c10a4074080d00454658200500c0b45a44500007994118421001c2ea5088005403281c560250303101401006d0806901c42540b1a00c80c26010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 909549874 1250 909548624 909548641
    0x30a020a020d111518011a0418150c03060f080d0206010803180904020607020402270d030815030c04060b0406080f040b0105090c0c1515032109031207030f08 69
    0x24456000400020a00030f03144046130120442d02601031616030b031120204e9024890280209000118140c440c0060700c2d00038001c0109607041104a26210782d030815140010078840e220750b00404410103404606680d000c072088004001c42c0d4440400710f02c0618000c9a003810204543c1040551a03003104d609981b03910400703403a445208400b480703146903051100c92609120f800c0c103912900046c10242001401d80204082c0d901450440341100c23591070040020070700e00c02d00c0c4d030a02001962415040c0200c3d41c0d015009180180c4101c906411940d00281c160b07400300001e100c1010064000d2107200e5a8420808241d04139018000208801000140c1403c506000103881039800c01c904402d940d10b0007003405418540a0400d6a5000c0d0401a6481d00f00e01000004a803020a09404480d8901620200c03a1010f00305c000034860741084240d4020955550980b010b02c066041e2590360704e05074400001d01d0011000d05041ca400d40200304542415041070000311013542c980c90326400ea40d2040301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 909551124 1250 909549874 909549887
    0x21020301060f0806090d1d220204210b06040f09140105240a050f18090d0f0f0909151a09030d050703120207061811030d020c011d15030a020a020d 64
    0x107140d0005083d8540d05c400b2007d101c0d0018140c810090419200b140122180314540d617015a9051200398001900300702d0a98040740821640600e070000e8605a00c1d15907480f01c4103000549101d20881e150510401c00503e42c0c3c4c014100e003948015031340b41c3c0d92001000076018001c1102c803501d000d0900c080d107800301c855035a0b480800400c010100045941014100001c80d80803203402034000402d07031030ba520f241c0002c14819003d10642001400d88094000e00103015400b86007217a010003007102003400c10749800040c5101540d061540211300c10110340e0304540c4944842c1d1101100854813500d40002042c401d0040c0500304054054903030010b6141c8007a0380e40d22410800400103850f9036861580c5c410140e015025443c403a01010991500322680c03109101d001ba44196000d01407007040802e146410440c00784c0228103130000d80080c00000d4006043d030300c40181014441004055003c550382c1e10102c4025402c5690020583c59040c00010580290070605c1450b0244c450400e1400071a40501d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 909552374 1250 909551124 909551143
    0xc15181703030a0213050909010902030706030b1c1707141b010f230a05030a0605120c0906030c0301020703180b18010c15060605121303050421020301060f080609 71
    0x4000c502e0350b141e00c1c0d00b010096004105035000c588140c90040785980d10410b50b02e0050720799000210340c03030380c0714010141480000e5215005161521000020ba5210146000200e4810409400881c2001c8c00c02e080083c0003003401800c401d000003403400812204005105245044e8130894644410081d144988042012040c41c0410301c4841070300d484d03501c9014140c1c000400710303600c1f4084242c0c140d1043c0464001184003800b04be008820002c071507a161041200900003120b000c10380c6850500c840740c40d01902400140180910800100d0380d4800300504820401c1c003800071035131000f8070700b0010f140403140d00c0c1e41408403581c6500011141115801c2c0c441550a001804407151440c40054503034084000c01120725070111004250a4002c502c14407004140b00d454903a41c481c5030321880180010024001d40500150130080c0020a0303010050b1015913542c5801c040e81000c20080e4a0800707078aa88009500d50708101000c01c1101103641000c0440301c1d00c904651150301c1c0c041c403481d01d585200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 909553624 1250 909552374 909552419
    0x1061715010c080d060803270d0c090209060708040f051f171905040b011806120f03090e0a060509060301020a0f0509041103180c1c0209040c1518 64
    0x71000c01280e010750007004104c050390f0000a2107070b5901211411500070910003e0a41241c51004143c030410340000e0200e280b0440f90118494010b9503001072090b028050328100680c081b90003221611110102c5034003035000340c107840c1c450782e5800030880085260300407030780035010a0041c08043d19100e000c40386142e44a40300c034103400704c4540801181800003049020055209080c00d8250380c0c0764400c80b03001c0c60140030207500a40c108501d190b00d071820000035841e42c5180510401c44c0340d000442070800d4587c4605200e002d160f40c1c6c20101c888020641007603c880100702c05011460750f641d48400d0440d6000c0da201c070780a50b0b824041500700c2c0100d01182c00030441c1040c902c2c252610507801040035803001800090f94282d12550011b81d60021108611b003414180c1e0324800313034182009074065100040329600d410b807064040f8203030030440c0c040c070003405880413034041800c001848445002900e01c0b9490440d101a69000080c0700324040311810140380c00004010aa00a040b40b100f502d88600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 909554874 1250 909553624 909553637
    0xc060a09031101051c0b010f0c03080c0306030c18041106040302132403060506030c060f1c091703041b08030417071a0c0709050f070f0c0b0106171501 66
    0x1d6860324540c0e404600012810403104004080104c4e1002114002d07500e0410400950200755000260540c100a0310910030f21422649a1000961256140c1d601c82c1254410640381d4441002103854000110f009540c000030a4095021130075451506c940701e18051001100303000001000d1103110300c26400081c0d007200c084c4440724091220342c0c1218008440072a070303400c44444005040a100070a035041225100d803618103014807072404010510f80c000003201c05502d0041417a51082e407900c070320710102c043c0449103401f4180d4003c41e0740c13003c0c200d01d8100c0c084080d080c419410303075116640100c8044440d482c50210100d129088840c0c40c009680490006500d02810701d000c0d40d400000c1d10400324250b101c0c5980c0844c00d8260010362031007651a503c6c25540710120024041e0500315a03401c005040e0b86018101702050700003e0300e135900a07034141441b0ba00c0002003001191a80502040500b000400800009001c1d500401d40001d0301c6e4800d00303040003500c950010050030b21102c440d039400244d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 909556124 1250 909554874 909554879
    0x60d090b092d0a02220b0f060a1b06150602062401080919030e0420030a0207020402040519060f0203030601090b0705030c1e011116031808070905040606080a020901090c11010608010209030c060a09 86
    0x580c010002158100b003101d41c2b81c1d00ca9900e203802c0c1c2d00010020035188100300001c00589404004481d00419420076248210144260034400c41b003c6c1d064050400c06400c0c0071951102c03080c0320b14054040b0054410514003881d05014213540c0a512035103016034607219003100a080300e00c0744548005810180d451440c0c4840d981c10029400009080c0d82c0a60b00304000a425a900102c805440505040030302c2000d02e0b004015104d030308000000700035900304204002c05070780e001e2507480aa0b903001d40455211405800d00919500130100104030030b100d0a40801c41480213501034150b0085120001d00c0401080007003011a0b01170205584a1500c81400420002c1c0c040c2607010303824010740080380010750340c49d0f00701842c1c0300c46a0b00451902e0340d00d074180b1051006501031034014005c000020411914268007190300140305101d40000941e95240703015299200d04000700e00181ca000c001d10402c0d484080c910300035448849118428410304140c0b0842d4100f110030348010b0316060312020707642072 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 909557374 1250 909556124 909556127
    0x50f0c0c0d120e070f0509010f0b0304030516020913021201020f0306090403050f0301030f0215030c0a11010e0f0606030114090d03020c0309060d090b092d0a02220b0f060a 75
    0x380340a003207a5154460f03045040ca54402c0210000a02c0da411100c2406850300d01400707005501a0002d007841100030b01c051120748014804c41742c22a6251a145039201c242d02c0e03084440300c0c01d03800000d40c010361100500c003010103c000d40b55101030007114201e0361901880d4801c1d00700c1c403e80c0366641d450700e420300015400303180228526074842c1c080e003051032812030300303441d42d040d5544241c000f1240b0444c80e442c1402542031a602d40500071280c102041c0c0346003000700e8014164080c041c80f80341001400d85003034041000030b410001001291008a078002c050007c0d8040c0ca56500f110064069840c0650309144016043d103001e00844100002e080310251030b0804a0195000008080c1e551004025141e19034859000900307400842c0318000032510041d16000c0c11500380600441450381c07090031b1450f80c18181350844a000701d80c111039201c2048420813000d0a01341c0303914000c1e5000250540d9191010364600c113000645c078101070100004a170550421103500038018001c4e03003000c8103114040078107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 909558624 1250 909557374 909557387
    0xc0f0905040917071208060f1c020406090c020a05120301060e090408040f060503010617060307120c0b0a030207140a03080126070f0f1d0402150f030a050f0c0c0d 71
    0x2c6004410a500407141070107550441d03840258215880313400d80c1c9888007072a078040f448036003290044507148104001000091006021803030858041185070400c00115079665014900400066000b40000105800080c1d21000c00c100241d0b5035004035403c00d006c0300480012a0b05030b0700191144041d070b030742080500003992001001103030303085402c001c04641d0008900000700102030036540d1650300d60400200800c800034241060500c250160280581c0d641c0125a800980d451f80c609030700340c4141401e01440b5690103602400c640b00000400901d00d030342c140c006020807401055407601c402d00c02003141e661100c00e2030025000800440051100900e811005036225a0560301d11003e58942c11380c0a080c4146030303000e20f400e242c0382402007000900c542c017131100420b907e50407181a03a118004031074503954000e00003441203603901081400c0c8203c4900b65440f441f10099031705c0d1249030020b0100001c08059400761043d154000005000010071811203070181c803a4006020595100311003603450 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 909559874 1250 909558624 909558641
    0xb060f0d0209030a06390e040b030a0609050c12150604181b08061509010b07020d050d210b010219030915080117011b080a0b04020705010509010c0f090504 68
    0x14000d20082c070001c82e095004504d004005825004506800641465801408806404108141100a03000c1ba0f0741114000c450160309440206203c00f04800003030a05654000003004507203002115814050002050410480c01b559140c40c54000380485035510030710700d2800c1d641c0b2506031000608608240c1c100780c44c100000c2d14850007118643c0e039504261200d242c87c005209002c00350400141004002180e00981806a502800f0540c0404282c070703203205000d006907a10001a0100854503014014039819410205888092a565000070001c5a10318000318441751140c0e18415420003510556201801c160003c01044440c060110300c902c0300e90301c05400340800c4044c0050404c4040409240d8130700156204141c1c1c0d81086010141c04190103100090b42c0e1518044409001e40030810800820103403c0001e0790f03a4074041100080c00c80300d000700e42c00a00224123142045070540280b4011909200240100c0c0d0900310201c400b00341d00307140d410018400d102c040100382010703031080c2c4d007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 909561124 1250 909559874 909559879
    0xc0f090c0a1205010603021e0316080912030709080f03030106090303110a05013603080f0a2711090c090d05071a0304030f170a0c1b080a030b060f0d0209 67
    0x81e40d02d14054a80c11900c0907030280e0080398001a03501c00c0307042040e03203258807060b80385017081c11428603c0c910318520111452550901c0700b0400030603150b000804c000384501c42c1404039155685040b603070040c4070300051301c00c0c41042c3c4281240080e031100f0100542e0b043c3c1c0c08603039030840301c00d1541e1011209420304841110407401000141070200c0c0d0280100500704400194100180001000d2007191980706460440501040128440080c1e402050306e60440d01041d0300c3d211507210b15040800038074207980c0f1020f100480255842c41200000c410094681c01014003180d00442d10007489a00041202e0305e1050840404c01c00304c20f403425401d8001107500540489807d42e465030103220030b418141003150101e0101204200030164807000e0603807441c040f1714004000c080c1e000c0b000b00c1c00b10b201818615180d6250166007480b6031003555440300328000005e1016640010342008412030b48500c450b140003074185110a00242003034011074506810b460078540c58405e803e040c40c0001c3d00483c0390541e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 909562374 1250 909561124 909561137
    0x1080403030f0c3c0c051c1808150103150209030a14010e030703050306010c031e030504122a081204050c01091403030a03240b09030c0f090c0a 63
    0x12014648602c1d0b509011031344500012184070701028001e095000400100d800c0601c6948000110381d11310343e9000e4950b070610319a40001443c0003418071000d440d100c484605c0c00401e103140300390b0282824400820520302c0600098079211556228a004c01000c1a07003900c9000400001d0a00e07403c0c451483c90f01d00c2d0043c01d1040e220002410250321480694196038540e40081117400c1c2032041000d5412600021858025036a40c060300c01c9c00000c140310305100d40807003a0024580118561034840c0305130703100b040350410a01e1001c0d0080c1002d940c240c2d0b005503100395143c43d0314025504200240d1840e030424480300c200702c1c00d02c000084045000c0312015400d01100301003401e19821980200d00c2007002c1c0500380014000180141d88a602c1400d8110310b100c03c01c415034501000300c1d0a031040b03d150101d8003043e4240301c94a079804e41d15080c2c007000b00f85030000030315580110141c017018030200c0544d0706c010702c0385d002c00404c000104c141031f90055500f404100080b40d003100403d80c13040301c3d04010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 909563624 1250 909562374 909562391
    0x40b060405092e0b040f0501080f04170f0f0310080c0105070b0c0f07080c010e03040506301006081b04210c27090c06030c0509060301090c090801020f090108040303 72
    0x20a0f00c4001c03540002d1005001103801d1003404501d91081c00034100a1800d00810b03d810110b0b001000d401400140403d0070402c1c6c0083c04c0b0202d2005c99810b45024195a550350000c4c01742801160b004070b80c2090107034200e4101062614020034001003845050707403000d0420340a5201c801c814031024200b000841d60810402c000030100d000a02420340c003c54840d91035010004001d401d41d291260012702680003008240959503034030040e29215150610f120f02e5403480e61490710040b050700302144039400819020091408943c44001c4c00b070350000d55072040241c44401c840303840c403011101c40e4044c1d9a07090005120042400e13049081c000c0300070084441c40c2103940c9801c9030011880d0401880132007100c0241840c2c0d11092038019404003200000c00c400e03c0961105481d6500074016141015201d070981d5140e01d10580583e020043c00400d1030350382c0e59603100e1020040a50300741071004210410400240880c06101352603181440001c07041c42d1000e200300456242000034021400d0550b9168030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 909564874 1250 909563624 909563701
    0x8090d1409063009010e030a12140f06040c0306080d080405160303090603060806060f09150a080c030106150c0204091401020a1d0a05220603080711040b06040509 71
    0x841011541c541c903000c80c3c008051100c011400400700b40b2160304182d010b8880720000001c550300f14020740b9080301d08580c0c152400d409840d001183c880c8442c0c0f240d0910882400c0c00c0112400f0f10411141046840d5840b40c0646c141c03405d6100c3c031840b40e00015007174042c150141284540c010700c6801070f01c0f1b118082d0301e040c1e5032115540e0000d40001d140020b0501c40c1da6010710540c1c000d0925000108001d1070107400041c00038909145007800354502c00040f0350488155003d00d01c9500307000300038074049604c2d03081c016a01c034801446184a036080c000005104030212030b100c08500fa865403420080e040341e40a01001d0807910703100f264009900007503030101802c03c2c0b000e000711b10025502c40c0c00b50341c2030599448844a18400041c46401018002c01c45603680d08a040005a9100c100c007545904920400c001004140d001920f00b0000013014010440142110b0241120440d0200b104c008824240310460049005050b000010784000c110842c0307240c0500300c219690710301702c020861004401e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 909566124 1250 909564874 909564907
    0x909050c0d060209031605030d03200a0c050706090501120e0a06020703050310080631170301060206010614030127060801060e0f09030f0c15150108090d140906 70
    0x801c0d0b90740782e07001c1103120040c9000d202800e88001c1c88500364001e1810900080e072140164580c4400741541ca86d132198482880e0f03000c047d415000c4170000c075103610400c00041c01c140203890045800703004107900480c14500540440d0141e07801070303550300e10f0f283c01c034480c24005081003541e0030214401c80800000040d02c5000911040e48284c0e01d00d07450303081000d14002181c0c0b2079041284103030008410000c0c03e10354496949588915941c044c040c003140400d2204200d42071110252240c5014541c040503c2031000c001c50484a0681c02c55600f0381ea1014112800d426188503134112000c00c2004000790350341c0d034800d034103a165042c07001d0324900b00018021017280c0c5c16610100c1182d46406040114a031044840c5510414410040d091b17803506485c2d00e0780324480d88100d100380e4000071461305003801040141207040407007824a820075040000944082c01c4104580754001601e180000b0251440401c80e0a200500f0303440f483c4400c0e14048440d84140c214061094121005104c0c101c00142260f8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 909567374 1250 909566124 909566149
    0x5010522030809090f01030201020d03091b08060f0a05101418190b010e030303040f03050f0a0206100603090f0605061c0c0911040f060f1e03050702100b09010909050c 73
    0x4070116550003074641400f40000b00241080783d0703106170000410160b6004180520011894680041c65580d9803034105140856440c0c604044010070038041280b80000a10500440400d03201142e03a5843d50300d400150f6500b11080c3c1c40051541104201810080c2c1021011920003444c04c0c02c6640000e1203a0b20b10401155034171601c114194013180d000c015403040300715400c000c2c40c1543c0600c10410109559201c080c2c401080e880c0e41d2151034040c1482803050382c01107100d0360256aa200d8400600a50381c860640c1c401c00c012040590000300d0600902c48c4c0c020b019441030840c400a1859241d0358020200180415088081d00c00b0030088014501141102b40c0d01c00c0605e000918180008942200d401100303a48248904000c01e01c845440003107690200d4510b03182580c00081881c0c4221034940340401200c4890b1040500c0e030030010303019001280714604e26422506c03615040c501c14000c3d10810642682c1042141c40140100d00560700141c448a000b0001c46109112110101e5107190300b03071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 909568624 1250 909567374 909567383
    0xc03080c3007050703050715060816030b250e1c03030f1422020414181c090605090d050f03070b010b0906120601230409060905100501052203 62
    0x11001e5070000200100d5000215403074010308084560354043e05e98441c258010b00f0b51403041c65055254035070307030700400090900e400544484040102403001658298002100d000c115940001c0f400d505802c021440fa051840e10b40c11844040d10003138814005001644c5d4116103400603100440c040e100092109600ca0f0b640006e0500e10040c12800f290f240070100d01c0e05142c464140101030001d0000c51b02d1094211410040501c07103480024010910131011040703083c00700081040000041d44c2210030f174400b002c2030f21400a28080146c089400002000c404102000024842148104050104264060140e641c02042619001c1c07620343c4026000f01e0a41c400a101001c000350980503030f0041141d065540d05100c99540040d1980c0943c85a0030710b0306e00c0340380004140ea0f04c1a144180707951404603440782c4402c800e10803c00a40d0003400b401d04014200880059048410712a040c401d0700b8444526050070b0400b8011030b4158030040c1145c80038403518624403e03403905c080320f950045215 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 909569874 1250 909568624 909568687
    0x3080621070603060504020708124b04020a06260c0415050403020904060c031410140306010509070e19060c030e0103090308060f0a0801090501020c010e0d0c03080c 72
    0x400c403000f000d4801a4018901490040c40b0610001d03d26806542c004910004205040e03640d04041006042c680d44c40c040b20303812180807a0301036442940c070201c80203d4030701114480c54110480440e012409550081d000410b01d072003040101e10811400e0031104890983c40b000c0b89a0800b090308503a016503883d69032145c0020308002d45c00c0748020030400d6600b507080440c04c0a00c1d42d0001744a9200040000d00803d4456050002151090b40800b0304846094610401d82c10b00103464030f1042d54a0069100c7c1e400e5601c4594801d1174001040c9040301d200a01500043d0f84002046440d92481c1004a8000e200b0700c2503c00650381c0140c0c8400600b141d5a03854103c80d0040c20000c1c11002140065414540b80c641d40ca80800c0d4403440f5154480c46c240e0f0314044403000740003c0360104509600c41e209a51800d95010b040043c10740080c10040b0a82000340040d20280680030b8840c2c040700c180001103400030100c000060702903400194000780c4190414285110849071344081d500071502000c11008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 909571124 1250 909569874 909569879
    0x110d060f06060e12070b1b0f070302030d1110091b141c0503030601031d070b13080708030a030b01120504080702030d0201020f04030f08070204020f120603010c0c0308062107 76
    0x30702c801e080c88901c0f4103c824603000d1100560868960449005031200c480000441c400c410300c070f500348002e01c2107904c0700310b50000340b641442d03903103c1c0700c0c50004134480e001c0c501c045140c49104615a0442c1040310003d00303400d0740c04126003401496a000101c5060884e40c0300004619501003030000140191044160006900420054500b03200c0c699842840c1d11328101da00424000030035207500090a09002034078420040005001030401c110000d041d101e120000700e20141018060705c9a8200c524010305925110b10b00240c544040d802003102952083c4031035002c0e40d101750085408141c041c18020101522500c207a03042d1201200c09071854480001d4400850904202c840e928014600c0214203040c2807110071800d5110b9484050001d060790381c400740c1071041c5407007151003099004000319910000b1855148882d0000604407030704001550002e141da00b01130260035008800380d5a0005600c00355901a10305000140c82a500201d40424004802d1000807110041400c568018103c140c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 909572374 1250 909571124 909571127
    0xf0d0804171603021c080c101b020c100329130608060106050a02070905070806030d0302040e0408070f1713080f0601030b0415022709070c110d060f0606 67
    0x79204514904298480d019441040e9002c4040034103a940c11103c1c954103213024040400c40381da80840203040c050700081c09140004000030300c01d4440310500c00074400b00800751502c650000d088c44005000d600040d100106c1e074035004943c4029001d01d400c0c0012a480c00407080314801d034032228200c6031000208524500c920348000400b0b892100030300248603035030400d800651560018403c02c4240200410703a01d540500a1082c1c20150542c1d610410183c50122001400f000041d03401034000d00030400c01702c404521900071141a58a0002c0141a1751603517034409055030b200708410f80300b1902000c41e03d0006482105280100900d035100d998079000c0c0c100314205846d4495004503e65407000510f10b1443e03401080d400d0440340c02100800c110340c0d40e0305050a105404d85c01d952081440050069610b18150a010f0441084001c10707800d00f01c1c850b02400f15443e8280d0780701022520240e010070001e114030247c0103240c40b001d40541540c5449648203c15111409000d68605460b01010301086 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 909573624 1250 909572374 909572399
    0xf1204061205061807170a050f01120b071b150501180e0a0602220807061e0e10020c13061d04150203060109030c03120f0201020c15060f0d0804 63
    0x440d0541c1c08000b5810160b002075280e82100c04140c40100102c4005217009010700814964003030024250401443e0100c17401c0001d000403070360005c0900340100041480200ea00d010169140d0210904003940c0703c0c60b0b001d0381ca1882c1081024840c000d1a55200002011045091001654800081036a50500c4602c88a50a100502003099803410511030341c19240042c04004150b0803d400503980d491e0f01b640c0e030b07040004002c48202100c4000400184013080028544102c6600359aa1980d5280d4400d0704030140c940040b22000180c58152041d1152600409010342c0c0000c5004035801d2039074400120742110b9249402040a6507100000c1000300c80300485040d0302d08400c0c050701d00781e00d4595500c480c596900e000c503440d4140d0100005010303900a0080c80040e540201148040382ea0740e14001400c544c44034031b5200010f0a480c10140300c0c0d4014001c3d02d8241104002400c60308240b0308050300300482c0100344d1640000640c1e20010662a0740400920003806440929500c500b440244a00c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 909574874 1250 909573624 909573647
    0x10b01080a0218150c061819020f0909070819050705060705032a011b0e0a1401180b0c0106030c120b13020f041d0f06010503030403060c020f120406 65
    0x2003401006000c0011410344000024003070100c0f8102d04c06816030030224003031300400b6101c1045109060a100003030310b1220364508400d415204480c21100c1c6900700d00c0b402401c59030020b4100d600b80d25001d032140f6240c1031f0140d00c602107000f11113445a80b00202460071008210000d454500540329005100c000d000280140c035068403403500c2c28105942d481d03528031800070413903050301000d414130700c58072070cc3c2c0000030302008048001d00c80c28124198509403000c5651343c02001c1145000004000c1c03c1415900c1c04030781440d44000c41c42e2200038019500541402148030040b4142e80011580b00d00d1b52002c0d1502c000d812000207800b504615054101079074940052080d41490392030100003d43c0c0f03012180d8848140000304204c81c42c07030301c003060303002d0800c0c00415070250900403c2040700a041d4040e1800c00000d81c122080000d00080700b68848000703000d015091b030020001400814a20340150302c1007a034510440e03400c244480d40044c1031103808070068004800c00902080300c01d51001c000c258 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 909576124 1250 909574874 909574891
    0x130f020702040c1e1d060a020709090b0a1d07030b09160b03070305010602120304080901051603170a060305100207050c03030d0e010c03050106020d14041e0806010b0702011b1502040305010b0108 85
    0x1038441005d00750300100102d40c0c1c0924810500003a10300c1d9010710078480c00000f0040c0303000070302100b04c651400781004502141c60245ca9860b291840c00102e03e0711202568808110029000701030540e11055424100104a06814840c440004650601900c8070030028281c000c042c94403410054401029104e0681c4088d04542c40034a0301c40c00b00c0c00c030104891308581d020b21019528050900160f07040d0191501d1905010391841e080c100b4160004c400d03c907000020b0010a410350343c1d05801c03d040f1840fa001c00b4040b907004c00d190b00c580d01442c1d4020f0100030300a40c1202c110003c030200191459001e011704e80801500c6403841c800300002402042456113450a040c0903540c1000e01c029500d13078510110004215202040c002c15061400886001c3c040b0300ca17506040f0540f0030348804003030f2280d10400147c1e1280c8000010f03540164025038140b140d0594944281000e13113042400d545590340402e8a40c1004540c00380c0e0890300c94401080214800c2d4008602c2184210000d070408400a04800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 909577374 1250 909576124 909576137
    0x504080d083408040c0905010602100e0d0f030203040c0b0a021623240a0c021203030103020f1e030105070c05010c021c030f02130b0c120702130f020702040c1e 70
    0x4803201610b440c0d500c9108014603040302d5554a509003034100180d640c0c440c001061138035001103882d0ba400b14020328109400101480030050252002c0e580d00b840501f40c1e000241c010300d403c40781c1442038004542080c083d41510040e0b544a80340f8804035481803841c040903038001c07148241180745d910480d034004c141401c1301c01c1c44441c060043c4460b912003400c0c0a8400c02800a2002c0302c000031040c024800d4481044807070300c1d00e04a02c03000e454005d1449060f4895040c000c1050303500400041143d05032540a0916606040395038144019030b1a41415240da40140300442109602d091007014422002940c0b11031154481741001401c48007e80e0200003190800c001d12071845403100320902d80311400c1c2c900059419007803c0080002d011312440d40044d151110350021300080024098a1007101c0b51064601c0c41440c80c1900c10f440c420540025002000d10340d0180100c0788552006110000c81c081c00341c80c14120f94001002c4640004151000c145d0003000c55481c1c0c40300080c440e071130382018103260 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 909578624 1250 909577374 909577441
    0x1090c02030909070c0c0b09210309270a0516020625020c0603042105041202060d0b062205030d020c120f0616030b0a060813030504080d08 61
    0x2501ca01c40d004145000c3c48643c000320307502522811a03100c1c0a901704242d89190b544070700c441e045d01d0303210307560561003080340480540490042107000d031034488070603004628002c81c04040c0321100c1c43c0181008240160b40c1c4401d00d100e4100720020780b03d26516000000c0601e041031502c00c4119464200d40c04644c010010031032113030101c0c001c003000c1415016540c598150300c11800ca182c200079031003041d08030102106000c200900075400f00081c40240903100c0c216541c003441120a40243c0c803543c921118090308007005070a100c0c005100785422500086100e141020100c1c6141e0311441c0d43c0c0c81103801d480100e40340c03c2e0600b040748002d0081240a01081c1444542c029992850444c0951041c00107010100e001e000802c003840440381c5100644c4c01c00d10313042941e02507620144013100007003420441001242c1c50036008000954499844910640d1a0810703400302202c1c0c00c5070100c0034004100004240507030208400c401485907903407220490f1030703c8442005216803540740e40440940e0394418 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 909579874 1250 909578624 909578627
    0xc010201140606072a080a150908120405031303050c12010b01121512030f0306050f0105030c130308190e0a032f180105031c0206131103010c02010b010801090c 70
    0x807508200d4000000d00605d82c1041c1902c00000400c0051011045404000140d0b900021440b803203503500449030307041782c20b071030400c06070a03141c000c003009290140c100100280e42e9500c24219070883e018004490510310a00c0403502c0e100001d400648403644216036041c504d282003205c4500118180000340b00c1050028000b03040d442c00d44140d481c1141d103401070303281d185800100d00c20041500054000c40801d460601034404ad654000500010b400c000022402e070070400130500d01e029041c0d41d00d92460343d800303940ca44103800c42581c003649003400e010300002191901c0050003804e99404540345504515040260003811140c01c5680520020101000440c00711880c611101c801c04040c03202d001da11140302e180042d000350b612640003500300c0c1340c0d5450100c4100c149059507815001c40c0c844a8a240e0880194000c0c914030000580c40280050000d89031154000c0e20301c0d01ca8405400c074400c04000290940300d103001d1440050395a1003008969681c82541140140003c240070413810b541c501c0c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 909581124 1250 909579874 909579877
    0x1701060e160e04090b0103260f1b06010b1c20220815070c0b0402010f023306101209020a120606240206010509070c05030c0c010201140606 61
    0x1207454010101d5280075003890050511882425005004001c846003c0c0f07815140c0550a0005841c45103d071906081c82024012079100c1d41a6100103550500625949280b2641c1c020950342e03403031426484a03044d01440411255001c3c21011011135122840c1d010005007207068581114000c90800300d003c00f07800d0001000a4411114042c01c981c0d411103401d90759100c0030129840d040c841980240040c1504000c10114a4103c4402c9001391944640a04580ea461084400f070300d03c04100010400540c021210306c20710000c1401034491030151940241384885809900301c1440c80d02120403220403401d085490b1b40410200c40b44803010702d2a00005000a402c0e00036061220303035820590055544115003a002404010b074140304008451a205010b004644262aa194085003000c464410140701d400c103001c0903503000704083d0b0718000c10401d6001d0050082403e114442c8040c5000c1001400240950703100e0000500c0154010400242107646075180c8003281c5501000f4410745690786d40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 909582374 1250 909581124 909581131
    0xc01051315270602040f0603020d0501063b1002151305210f04170c0406052d030106151103040e0a050a060b0d0c111b0d03110607091701060e 62
    0xe8050b40341d5000d80c90004002d12868000c280341034084c0d0400030300c4035810380090135400c40c0d402051110b42d0b038403a0192042c1140c94030b4620540d42680c104202c10701c289082941400710b0000a08884048001280c500e0307001e00704c1c00c1d0040e0001c080350400c44840d4603847e50001743d01f640100e411902038a0307044d10341d008034540d148200c03c0e48696070311038003c030350548041d40b1b0303040303601a80c40f0781c0c4002100b890b0340c2510100c0890300031041c055078513145c5841100c01301d80c0c0250403d00c1c40d480c003c078160008002d41c0d030601c2c80d122090004098645091050340c1c01f600c91400c0c140003a43c000000501003615142d0104074076402004240b007920103050403960040e500d81c8010801e0740303c0c3c50b01c01014220507003121160101c04641c902c6140c1450b0009484800c05440768114080d0900743e15469030408106407042031581241500e00341010003030403690a00a14184c50000703403000c5180c0c00c0003c2aa54040042c0c0d04035418040c411070704840e004042000c02c020001c941c41c3c4520b007140101e005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 909583624 1250 909582374 909582431
    0x9150c110904051c0c0c0b03090105150a0b09010302040f1214030c1b061909061101090209011e0f0f031520030604150803220e06090a020c01051315 65
    0x8010404410780650000d026103a4050241b080c0c2030b0320b601400034030b40c004517200d20080d8202400b05602c400c00d117955054210006c1d0850384c4843c1803001803002580807104590405500f0400028098030a48900e03014040144a02020001c203080902102c0d03038225403a00640c0007002007103034031103001070b0388400142d0041b1000c1e85590a200051914010145100400e01e2104010380b01e041d03122000f84203441aa44558131880600c000702400c0316031109000350000c1c131101c01800a241c200c001010b08501290043c110280c940ca240b001d9003000743c1c0000442c2c0310140b4148104122540a0040300d01e402100700001e05140c01d81e824803009000403007020340d10000c0411180d07152900441241440c4035180e28410385e950700714075666400800748900900d0a9035a21f00d00c005209003040840c1c46404e807041c003503291701c8200b180f0380c1800f40030860207983c204030358038a0304002c0c000c00d80b145028003e42150a8002e061503060740769503031040c402d0203107020034958103654005488620b00444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 909584874 1250 909583624 909583663
    0xc10080106091203030b030d08040b010f0308040317091026060306071103090301021b0705010207081002160b01090903030b0418080d14040c090f020f090d0309150c11090405 76
    0x310b01303040e8000d0102010b400d4140c0200401c0c0188507800ca0a0f25000f03500c1040109c0301d0341e030303180448203181c1c6c000e01000b0b0480c00e0420082000c6107608508015405000c02910315018001c0c1c00502c0b079540c0d01a40b4404525550b904044484c040b000c030600c0034904400110803440c0400010f521010001c0c0a4400c0c0a07200301150a50f00341002a42c0e9101000f5000719590800903102003003e005800c000d08952040c01c2c0701042652010070f82004440360800104014a0700d40707a2407029410a82901e00ca410b02030a000d80424010b1201d180204111680020140542d08004055131000701e800d900072800d042494451071855000d0303890340c58001c4401c035150f401c1005141e0281040101d400c002180349030034041400340f54030000080300e0814404000c00c201c2219450241c1c0181c00b81084540303014000d4900c14148447c107025050712030310f410304109803541c07800000212983c0441e0300107400300d41e90504000a024118100340000c446c001002c1c50a90f031196540e80c5520104121a051f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 909586124 1250 909584874 909584909
    0x1e010609030f0303021e030c09091506040e280f0f090c060e0f03010608030901110109050c151306080907090b03120c160e150f010c0201030c051b0c1008010609 70
    0x188580304c0704862401c1410654034284019583c8c82d640110f031286220300d503814041400b2021800001c10307000c4c0042c0c0050f05051920070030b9000c003900282030381c2500380c0b081071000c106095001c4159601800203000107091682a02c3c0104a078400d44c1603102e501d2070a001c8001041d42000340204440e202c3c030344100c40220b59400b1689001104405681540c249000456400340c0400540403400003a41d9049846261049190030307100c0c815000340094108050601c89401c01040d07400d64507410b80c000c185055080801d000002d2625400400000c800405101d9046010b0241c04001d185003802071211081c0c0700002a00e501c08140e90060403000043d40a8140c03030203120001e80e600303440c00407800c8030b60b54016040d4480b1048408001043d49451403d586150002c1a40a081810307901c416204c0290350041d401404103600079401c0c0302007030003549224203c0c50625494014524098000808200c092044801d0089106800d11030080014482240c0c081104c2c012a0004100318050b582c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 909587374 1250 909586124 909586147
    0x2032a03070e010608060612150d08120f01230d03020c100c03080c0309030304030e06091e0310140a090f020904060504140705100e03151e010609030f030302 69
    0x4110014154241c0200c600000e8041030340c40d01241250034544559005540303800401c03a1620603600a014814803e40111b440140b1141006240c041701401c00f09030008180c9651609411180b4501800c543c03610410001031440c050203030040240140681d000c61098440750b040c4800700c0c0d28a4090b040c00f01d507040a240c800c03c02560007110250900414050f5103000400d40380ca083c81c1038011807102400300d481c10209000b2648100d007042c1c061030540d100c694044801012090310150b1040e81405448941d0b40c0750605410b201a501ca0071044c0030042000785030400070f140b071072260441c2ca480c1003406001b01c1544000d9203d40380000c00191070704580303080e108003004504041d421402d00402c01c01004483c0d44840c0c01140284001160008021a0305503a054203018540c2c0000205040021060042c1c1000c242aa8010242d60410b04113040c5060100812240c6c4040303000500388000b0031012800c481805440c2514080500324116110300d08100705110004080590000c1d0100505 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 909588624 1250 909587374 909587443
    0x306180c090d1203110906070201050d0615050c0111040602060105130204080d0905130b0a05190e280e030f0c01020c1c020f010212060f011101090b100605070203 71
    0x204001007210040310391900740000410f49840900010030702d4101c48505100105040e1038410400429692503c9099801155240c1061411402190301c510000ca40d48141d000c5211840c0c0ca6680d501d511664500704150079544e00320103140069802f00014000d0ba0f901003181c50543e401650141081036408240c1d1000384030f540d01c100e1903030140440c40202545e0040f1010101c0da4122509003200800c00341450403100708e084d801341e01900c540760400c06824810340c01410000d010302c045003510754461081c0c586005c2110b041d0285100420074048a6140358014440d00d218100b041100040c1d60740aaa501d00c24010003ca1119001c00c940340c655000750112610711000d602555103800c0740e059050809000c0d21881300140c010118001c803034140501c203035403840040b41c001c41503d4440d9018000350000750500c0c03d0402ca225141f15070501400d02403400300702c0c458078616500303241503520b080c00401036404c2a020030200300110f40150f40d00155000040c6908205420342d82c1101200c450389 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 909589874 1250 909588624 909588637
    0xa0605040606030210020d08150105070c0b130b12010501030f020c150702120c0a021e030607110d030b0d02040b010e1216060c05121c0908090a0b0306180c 68
    0x509081000304010000c1d25002681180d2003030f105180c0e10081d03840180d031151074140400c0d0008a104000543d0f000031880f1500d140681030618602d010259122620320209075086003c035800000703420048001c2c40e1407000024580d503220380c0e090070030b0030040c4601c1c02c5040c841c550406489000d15819601c1e558115070034402e00c030381103500c50540482850001d841c01c45021025005296000403100c041400300c611011400e4040e048060090342086040c890680c01c04c1c00d9110303118650745043d10f0030000d041c042c000c103440c0d44507051080008c031450800b414601404060410300100307a81d80320503900c03458a0344d044501041c0c0391200d10040700c100c80100300c0980e02c2150b0809142c0842e0b3b000c5002c031969174030001038103805074035440291100d0043d404000c0413944010034004074440c0b031002500e15041c3d081d407a46500803030004602e091303c1c00542c042d02e061000240c0c1c3d001c00c0c90110308000c002d12941d02d042d419454111300095004280c62844024200341d80000b0f0341d00180581150301c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 909591124 1250 909589874 909589883
    0x60a0e1e030307030c1e060f0f0203090a030c150c081005100906051c02031303031811060f0d110a080610090b09180411011b0206030a0e160312021b0a0303110a 70
    0x906ca1305504202c03010306075a00c84171900034a0003a500c10070459a000700d038414802d190080400b09280d5170102e42d0000e04510503035103a45044140615001c403400b6119010f846540d0300c4a035824004a0f080c80004a40d00c080d2240da4541c82d10020716400c0640c40781111001d0a1160311000300d154a80125165100b0000800d803000042003000c00541e41a0080140070f5134007000043d518814a1040030308805000e8400000900d02440c68030340705009288041114400c0f50400d0703090300315036040d141c00c40c40500c000e00c00031410000c100ea200ba4000d40c4800111414010031031a608040c0c842d00903400b4043d12841e0000745102c050702c2e442e4803000c01d6070100c3c2104425103400d0509079803918035a1005400912070504410705840035404c03070300019400400151440e25400125001000c0703103445054280600034460807e0310a40106d58011402031128020700005228024242006003214030001200c004001c01c0a0300e64640190907660b0504049420494076580c0910786100da480040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 909592374 1250 909591124 909591173
    0x8160e0301110d14040807020f06040906180c170402010f020a05100f0c05030f0601030c0309050607020a0302071703040315060b040305010e121204060911060a0e1e030307030c 77
    0x2482500c0043c5080518201d04101c0d076400b00481c20050407054502a0182e1401c0c042840035182c1000d010b02d5130385000b081c0c1c03807902d42d5807030030442034400380e900405010450250340001c5840c2400390302843c01039860580c0e450301c80300d804619800e50242001e070400800380e419400c054020007003100881c1d048001c0390b12150003042044003500c0c401401080950a040c01c3c0d21205006000740e07402089005a0381e012139999200441c01850003080000401d9254407003c1e0200d00284034107030282c25194082c000c210510300700a0701d080041e5004203440c02d280d07140e6840c074038008415103007580e40c40074140070740c1000c60900102a10058004400c07100c000640001001415070156034092200001d4880c0d04210350540f952030300801207002c2110f40400700180c0014038070341c02001541d10a01041407410f41c6900401e846821600c0c3c0074011031089441540540381030b860200c40700020030100040242000080307904c900071404018188000700c0b203072004021844040200001c2c0122511 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 909593624 1250 909592374 909592391
    0xf062117040e180a0222020708040608040b0106020606150c15010f03061b0c060504020103060e1501031506020a031101060302130b042414010c08030f011e0608160e0301 74
    0x286160000e40f080548034588071084440b000000c40e125004079001064900c041d100090402c0114070141c10741946160701700a2100018020006400905042d80c1d6440d05032500d440d1512041c001078110303000755403010b020001c180d5503032407d00078801000c41c08243c50b0b243c4240002d1501f07000c8804101d441e480d100010bd00780303040c13151500c11240120360601999001c0440710300812041d10380800084c2c07690310070801040340e0350401604544107240c00210582e039144614803200e0142c8081d5034404150803004011342c1d01d8050303840105141705031070b85401e143c128040d43e14a00300c03000500340b140c1c0c151140300420082d8401d41c000d40d0054592031654010481e40c378010320007088900d11035860300c28142100d081611a684840100480e01e501303080c1405042c01e004076010800c20304020f183e00106000400b55005075014203003021403800c1c50f5040240032104600d0b10b03200c104106e0303c4c9050411489034800031b1150840041042c82d491440504030032240f00d0407c07040c290300f41d030808200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 909594874 1250 909593624 909593639
    0x5060a17010216050609150702070902180a03081c110a18080a0503270109051201090f081e0703170711031908011a030f0c04080d020106030302010f06211704 69
    0x1070b114106c2001a5806200d48002191003d001960408016400000148040781407513004101b040315002318241150f1b401c00010f415290035801c120386800c0007003a0328460052041201e20314560b200f07000d000c005101c02001c20341d4052100f00208102c4820500c010200004443c5005007c0c5403054030030080c581d0402c01d58940c006801c2211107400000d090b1400101c3c0340c020307508a00141c0d80d20304620b18080420103078507030034640071045560303501d03001001603249200704c0d080310b124848041c0c64214050301e614000c11120703802c0315603241c00c02031400040d901c500d41c0c800f503003583d80c244c249a0725031100071514165400d2038400e49120000704884901c004001d0445540741554901c1556031300c0d03840d42c104010625001564644003807001c501c070300710040815980904140740c02e509250351107240724580b0441412220245c0d40d20b0700103009140d8203010f0623040c211060001d200d05450196407080c04210302145402c240212003d820400100c15104003010b0440494107840741c0d12a8003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 909596124 1250 909594874 909594883
    0x9100614012c030604121214071d0303160c050a050d060203190915110903100b030a0c0f0815010311040c021002030a0b0a050a0803030f07051603090603050a05060a1701021605 77
    0xc0c0d06001c140e200940900c400800e0280d4007082155000d02342d4281c484031400d0b518045460b00c00b00000c3c612507000b0000f0740381003001e00307030304c0300c21034124180c1d060507040031001d03101c42c2d40200d8060400c2c4038040c411902e41004524842d6413280005039660360750692560013030392283c648800c42e814600c9030014450f2010b800120040300321001c0000381220030160506d41701f40c003030841d015084841180e442c01116401140c7c200006010f4802c200f00c255903001207e94a03400269044020200900035410104060420700c01040d400e4040c550658491001e003441c82c9101d940300f00e0f103903c0000511882440400b1900c0b20100c01591a420947c8e1140054014082414068840f600f400a410f10700750745000121819440550310f141c403803200140b86072500a0284090003010010300c0801c2e00c1d030041d10702005000742e4030031003102e01745240142952005040004064108000c2c040f503a03a40d0300c005000c6503510b400c0840e04685d2481e20a019000316102062003680b07a82001301800702c0480c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 909597374 1250 909596124 909596153
    0x4031b230f030601032a0b030702010203040c1202010509062a0f0c0414070f051209010b090a0902030c0613090501180c0203070f02010c060e030309100614012c030604 73
    0x981c0c2800000600701455030b144001d01c0041d2032034510400c80d00315281c00069039407a040c0030049580d44142c485107107161981c07007070f00d0510050703600004010900150b6135018029000034041c00f0510001500024032600886d00018412080003c00104815200e40c048080c44624441582c014500322500b60701e44403c182031490728003944000d1803162800b4482d400788002c186c4480a9103403140a030441340081a8013071401402410016002c1012a40740000d106803000f80c000314516030114207100003c84094400d0702454204420200140e0700810b41d8201c1c0c120a41d085038840110903202c6c2c4036170499500400f0300901d40030010640a4059405459480d400c0c41d040c0002441d010080f86c0d00d2080340d102811038159805480b00541c071030702e0000c244600408010030106036000446003168404c0d02d0105269112a0341c42000391601c0c044d45000f0880d200516011102010018000b01d041e1280860f080341c070074203048041d540c00070b0403c00d02c01c40602110150b00d041e10703202d001c031403490 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 909598624 1250 909597374 909597379
    0xb0418030f022404170705010501090c0f051b03040f0b0903061003020a06050c010f0507020a020f0604150c051006080a03110a080a030f0f23010e070504031b23 70
    0xd01407010942c000640a04001c40c0464291001650007940006142c400380003211480340790700c4400b5200110714054851540178200001d00c65241a110404680030b0303050110501103a50400c1d080c02e50002c0179a401900c00e204460f4002d0400042079056206a401150447c81000ba0101d007486007040035162090040d0110340c4191a000010424003038503200007036102040300e10038054140b00b000a440740004504c00462031764508105401600c6040301e50b800140d021002d54415031408440a070365015013590f20310300e09030030403484203d5600c0304440704041c004004032200801c032040250001d946240401002001e483c0c0240701c2c1c5401400d44154001902e5040400b40c0d00c8000c6200b2181c150b000c1d0320585402c500c02000d80240c0f038003501206500d552450202d00f01c644130300034a96010070a0005140c00325080d1041c034420101078200244040b8460100400150010b08a4082c1e0b90081454030b05c11440c04044100c03151990042014051900c2407120b030550090140301c1f00702000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 909599874 1250 909598624 909598637
    0x2010608031c05010e0c2b0603080a031b020606151b0c010f09290c01140105040c090e04031110020a180e071d1c12170408040605030a0b041803 63
    0x1c89100703c038000806da406922111042000e58021540040b04040c0c0102030f180c41008455542401030460321503a0041da680701c00001e22000c100c1d49441110010450318044058014054000964512004101c02d014000350a15029084103890688041c0c4070109015100304100c1c200340c07900e950311350512501041d1181200103007a4000d960407001d4070800c1d082c20408142109000c000c0142482001d00185410020121002401c0c014214440c04080784600d0701e502d00001d0000b182d1682d4a020204000c000d0103104180c5841482038010741c2600c0c24203407400503c00c0d81c03820400f048007289032180c80092048581a00300070450701c061380100d6a100700964a0b103407031000e418100c42c41c0000030820300803900007000151100342800d41c081e1400100c0041d00e60351502c407240000003030300c000c52020404500c1c59800b840034022801000542410740c24565109000381c013481c002c9c0d4051203000300008141b410b0359030200d40351100040052003244019004c07030083c01031400050300058807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 909601124 1250 909599874 909599879
    0x40e06030601290d090b040302120408030f030406180302010902031911040c0207180b091e040807020415120c0f0f18020d0204181514060a02010608031c0501 69
    0x40c00700754103040f10320003004140e151080791580d900405101c16021030b540000c0c080383c542c001d010b01c1a082c0c2140702d009400e2150030a402c0c080e02d4405090356892400d441004144413803c408400d84040412102c00180c69460f1464160007918180c1d44004019049050074014990705421a5003554025015694902007590307081c0603462101e1005000d207440e21082c0c1a40d804c10f9401182282ca9a10503546600d465140c0003c5802a12000c01c640f5600c51190b9541483d10303282180d0403003548828403000541d0501c070030181c840700034406401c0308800b05000c8159116038004c0d108114090102c0c0040c51b491b050052a040c0741c05001f541c450002c8440869682e0043c1c400c4030a440318201c82424039443c102c10303900c00d400c59499a0040d9a0203018100c031860701800600050500c01520540c1c03040640c0c01c0380116102c4000c00c004c19810540b00300b1010021003c1007400910645800342d440c181050300760302400856204071010710000924100d07914021403552441105030405010a99 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 909602374 1250 909601124 909601129
    0x7051b040908090d030c021f0908070e2706010603090b070f2109050706030209130b010c061a030d020105062e11120d0902090a1802090a020f0f040e06 66
    0x8212003030081c6006010482030302d0311314048041d84000c610a25240e80903c00ea9404240e16600001800141b8440c00041c4a407983c4c009240002400540005111040c60b00340000d030802d1000c0d1150a05150000300c8440c1300d03101d0105400ca400d0518102c511a50b9070f440001c0c01024801c0e0203031214610440030502003440b5500741508401030b691242c0d01c00c8490b00c48000030240b0880345801c0300396102250400902c0c180083c1c0c0050205403801070701c4401e24414040c1c40b0501004859141d8a0f1401080a580e0000003020ba0542c01c4400000d2148006c01c503000417600c0023401550622030030009803242581504054800e0000381d9403241c0440c10f90b2451855650500010542d888d0200703010306080e446885031b0f12004c050b0724200c0b90844e08410544078260312882b40c1c201003030780700d070b80d0034040d402c06004050f00162210806c0200d03c2ca00741d080401440c1041e4001e1141520601140c0101507503019908240b41580006594142c1c0120303480c0e140d030040c450312000c0229000025540e2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 909603624 1250 909602374 909602381
    0x5040e0c09031209190815060a1802090f1309060f0e030f03090c090f0609010e1326180a080616052215020609010b03100b04020f07051b04 61
    0x880540142161144450740d90900e8203c62822900f05d00100c04200f198540001c81c64010400c903005400f58000c0001c00f2141c005c402442c2d9030141ca4051410822041c0ca6520a039803451140401a103850100f1300048a802c00c80a660780d000000540c0c50741d2200f00c50b4001081e40b03204280800c07032a1040348100303080d220a007502c62501d401c140542a80380560000a540c000f040001751907018000341c0005910340c0069403140c0028010302d00300000d90030181c000d05d0261400344110710302c519000f0000c017030b40e002c11003000b400004a440403d5503000448040d1010040c500ca140340c40300b601551000304060030070700c018425000c003880007410700b601194941c09220341006a00d01e41c070714207206440d00d9010502d2003500c655600d8281c3d11440520643c94040e1684c511820003455298400900d8141c0c007400141e40d0b0391404078035000700e5500140c1c5201e074001c042e201040f0040d0920003d4002e004880080d590310600191542c20004040307040d400c401c0c118200411160003103407d11086 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 909604874 1250 909603624 909603637
    0x61308012f04032a170f070f060509130c030b130509070519030b010e04030206181c030e011517010c200c030a050708010c08040c062d05040e0c 63
    0x42510802c418008981c0d4100740b00301010180003c0303600c240b107060158200b52003507480707098a0b03040d0418000d03c0d8101400100c039201a0b03c0024204542881680c0450303000314855001400f50004055070789031a0500203c015180d240c104008466080801030064400c55049911071410305078026039040c0188507042c001c0e08800001e01403541080144152603281d108025405142680004005005620a14003038905800340b503042d1300f01441c000e850b126001d840806c000050207003041e003510000407032010b242c1402c040e400e0a801002000d5004008800003220341703500388407075082d5062110301007108450301c9000320503170300c0c081c420312608a8200f522124001504103190720800155050301d08040e08030742c001c0e243c410210324002403030169429801c81d515045100104018a030030301c5850b0400d82182032900041c81c2075030b40d441d21105580505428170503401c50b89017020111281c00d2203014a981e00000301c01c6017580380500306400900c0340c08041c42c003403c00100039400d00000e8070003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 909606124 1250 909604874 909604961
    0x608150103061401140d090503091806150d06080601120b010b030c0d0b040b090f01030b1302010e04090f080301030b1f0b090909120d02070606140306130206130801 72
    0xf644080744011107116542040f19040c0d00018405166001d03014030407100c00320300c41d60066584101c4a014005800300490074003001e50844000c000580d12811030600000c1c0074014500e64030304103040031400401715900070b5803407486550f00118150700240a05000c1034081d4110b11156a65081c0305c4156100c100c1e0000341d2013a01388100d9441c90110340180307400010051003c140c4100440100e00e0003001200e01c2829220310200400030300601c1440c070b541000b181c0c00318100000a03030b0006401d240301032501c0e601890b5250030540902c40c50b880103402456002441c1c6e5540d503503030304008841030030507a11181d440c0e01111440d03040400f403115034412907250a804600b04a42c20013007101f5100014134404203802a010303031a4a0040300360040003111040c2d07800588401c898207100e000c458058000e01c181480c40d180c030200039a00003d00951000fa1103881e240340c14081d2010901c0c07802600c0886040790100d40c1c01041c001419008106a01d6007030107040704684158055a02c5d10b1500004800c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 909607374 1250 909606124 909606149
    0x8060a1808030a02120f1801020a0c0b06121c0201051303092c071107050f0108060d060f09030504081618240e0103030f09081009060b0901060815010306 67
    0x1070114001d141c1c050b070700c0e48006060514503500014004811100c0c06603690411041101da035854104200c80e40c0c1c6424003c50401204410180250340f801102500e820403003000038200fa9240300500800000311015507000e031003010f04011045130200408400355080c140090900241c4c05412031010390542daa0507400c42c07800041040030008212114145011780d0300d007110040c080c40c2264003882d01031381c4051540c01060249802d010080c0c0101e403081460840d481416a031180c800e40e08880112212101159513103445c40090203190000308030a0304101401717090540017806442260380d25000c0e20400340074400c01c1c0801c03000394000c00c035a50360025100215440a82d0004202e1540b0940204c03a125601140b00c940c0d0b281c503070240ca410030410740103104040d403214201458104500f00800c58034289070301d00392542d8080c0d00080034a03035100c019005008094100620f00080a0010012542c4074000100b600c0760449070300c100c00703800000c4941154400d200b401c0848403c4078011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 909608624 1250 909607374 909607421
    0x30d050f0c130e06030109140c132c0f010c030510050105070b0a15031b060e03030c030405040906110d1406010e06120603070f060203090306070c02010509101206090608060a 76
    0x2401c1d01000a013145806668400301c440c00a821010141c085030001802000400b40100400400803070310303a0324401030707070a0104015101012811440b140a08200448005910000b40380e15140001d8040482582007000071200140c01d980326074044d8105001e00410390b6160313401940e0611542400034092552800001c5010780c01d039000141c0c1041c0b01004c100440c0d034a03140c10807003444c0320980c2a0329150000301000540d07044500700b05142c00544c040c60500141c0304487e602c03405103114403409940c031140024100003040d80031002803031509800d640c4a90011030910000c161120344442901c02c1540444c02940c0207582c2c0320311000c401021240740012520840303000b02c0340a402c19405101d0704e000810520032020b044409031a4541c011622903001c1c8041514090001d0501824000c80200f032034050f0341d0100484441c09000d90f4494848a0601802c85042c10303e50302e80003880c0d29101012448610a400c040d0807200c0560072070b1215260340c1c201c4001c03610b820318040c2216162101c0b9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 909609874 1250 909608624 909608639
    0x50604060906060503120c0f1903081909060c030510052b050624061201030308070e10020c0108010504180f03020309061201180603080a120b03030d050f0c13 69
    0x1981c456220301404112142e4600200b80703088502e80c00c02001c5007004c201906a40c8040002500d000340c65401082050742c0001c0380481001c2c840d80140070050b99800150b50380814040c06c000d84551048100040c0d504ca0600c5001001e15014440000781400c01280c0301e41400c1310305505641000707040152050301c1c200061030b040300d141c001d810050a01000000498002c1c042e840c414444d03060309001402035084540c43c1d8401451015101d004e051150340c002800c61100581503d40c94200240592244401901c21810105040e507110050800c1103065580c04160703103901807001e0b21045d03483e980b16010441030300d450400e011030207440c0410040118801c90032060081d07001c4c0c016280f4102d1030101185050344040c04003404409031800400c1500c00706001c0507880800088104081c50845c0d8403040d0901c544d80c03135a0100405480c01c007030b0f2a05154026030f032700384e4010112903841540c140700308041d010803500c0c0f0480c10a01c800140030510304000300ca90800350364014075280c0d0f052148 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 909611124 1250 909609874 909609881
    0x11160605092403010503070b031501050703021603080c0708061605090a03080304060b120d0c06051005061c0c050c0c130b0301051302130c17070c0c24050705060406 72
    0x5840c0d034008800b20382c1c40d6146544190101420000c5200e0660b02e40c10b0105040c9081c001d0791104150250400401c952002d0100c072040e40c0c0036091a1a90ba0742d109401c0803841c00e002001c82040500d00c9880000811500780c00501c410510001a43e00050b41d4030764181d26040115a103040040540c058403a42600c03803001080c09103801802c12520580769143c0c06130540044404075446035503800c06015624108080320510f15a050041610804030030006015003000c110003441e2644400102c0c0611280e00c01c26070107040c000c0d0185403280d0310741c0f01a1410030180154513203100d150843c1c03540442d1064044030707a1307948030310300506800c69580d060290001c00064a540c13550365417008030401d94bd00f8042e03640100c0c444121048403030003600400c4102d030041041007d040d450040443c03d40c07600300c48020000754245015182e66070b0fa215040d05d05952120004044041164010656410803034220700c0322100c010320304604440281d02901c1c0e922500501501ca03501040c0054002446900b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 909612374 1250 909611124 909611137
    0x30c0605041a1003051902242205120607050a05130909030309060b01090807030221011401140102010203070e0d0606180c1202041d100f060c0311160605 67
    0x260301108220990105a40d110001d0b0f5465210480c44442002801030421100500b1100300e880078048449503400601c0840848481030f0300340c1c0c0c01150803448020503206450352498400d01c00040e040681e03038840042101030158038440c010b5120306040004000980c070340f04030740d69101d59141c11191130099615402c220a140401d414030701e0041841c50460007252409031007920b0110b1542c1e56417a00c0c00503144242e01d00c50401c4074960007000304d50000200002103d406440700c40070301c0c089900d02500f101440c0e561401c0d641c28200c0c1c484002d140c0c010a0b5049907100080b492002c03015a004a0903440140c40642c006100c400e0050a07601d01135000c4010313079104910000300c01d41d441540c038800701c40200c600344080343c2c2c85031f0400900d500414682181544081c0840ca02401c016926401c0c580d881071012205158900080c6d050480c0b048000181041240050300c072070b511030000702403407124402107002580078006561240e5001511210544641584d40281d038102401250150006c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 909613624 1250 909612374 909612383
    0x630090a0f110607061e090203030901030903020102040512070f060302120a1d0d081006090b031b0708040b0901030b01021908090402120a0605040b010c03020a020402030c43030c060504 81
    0x140040070780c2d00d0f2402042a60301c16003000c10350384401c0d005e062001c103406040c00501d034100040c000059030f000c130440d0b441182c01d090000b20500c1c6800c08a0080c090382c0c006c00e03000805400100440840000c02008070780f40601c40e40b01840c1c50b081d048099004d94204072890705110700c0480d2121202c0d0300019440c04150031104420140340500900d030404000390306011804082c00c0c407000025864007070000c0c0c6454184503400d1442c2200d902d250341f0009085d1078080031b00410100c07900c2d082a00302e520706504102101d481d0354030f504554600e40d101090580c00300c0c0c40c102d03220880d54000b052a6076946402c101c0b0402001d0303952201100c0b0307440402d0300c5d5070250742041000c0901008803500c6003c0c000913080059441d0901090004a40d4140c1c20303241404400c0c0503000c0000d03400101c0c40701d1103505803009612500e9a1700c00007405d0160084051504d444941c2190104400d98000281d103190403c140417000c004c0f1040001000515030041c00041103c1404804100f0507040241c1144c0b19 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 909614874 1250 909613624 909613643
    0x4080a050c0a032d020a06020f0408070303121d0d030c0e06070c15020708031603020c090109050f0114060409150909050a0507060207060503061e0630090a0f 69
    0x2038a10030b040c07101d000c104070003090030b503c0d0903100c0c0201180340803880c008540080e0412559110040d503900903014005240c00d4001507040d0150101d5015103008024090480c0c296a440b450040c014080d00510f040b1050314100e044003203070b0103401c1d00f00321282d1044060013400032131042c110064240409104144103055244800503120380c401401d145000d0f03114446a54200214640e0355000040d858046500629050000315004000c07102d070444448003013004440030f490241c0c104101502c0c1030b64000000d0300000340a80c03041d045035104e8042c01161150584e03c2e20a1180c215090300c1510750000c0c4140001e002050488c3d0040c04001243d4007001942c076511802e5500350740710300c4401c841c00d80003200c0c20420403174100700d0000a0705890000e04200780c10020300402500004101611590300c0c401060781c40480b084818078039002c080c000b80da13100c40078403454031140ca2104a80740c2842d00d14400100c1180c452400e2809820b9100141c14100016210950502550300381501c10024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 909616124 1250 909614874 909614887
    0xb0603010b090c0c013207090902030f010503160f0b0f0d05090c13020909040b0414010c030510060206090a080c150f040201030c231305040f02040503070f03080304080a05 75
    0x1140b40402d441041101042030b0b44040280d00142910352420300040c0300c52144403540d124000c0c0c1072515000d074a40b4145001a41d40d4100300300c890a0540c0e01c88001c0794400030604c04059041c1c440c20b416100c082c0c0444070710221300d1b0014445604070744074080408139000d00920150102d48002d11111600a414034100102c45082404407003050701c0355141580401e080301018280303280d017031609100720361085081860443c0440c0010500600040c1088802c01c005004c0004000c80300c1100c08860008110b00311031448003400610050310b036644040082e0a00003440ba00c002883d0b4864106135016007414040b0740e50f8414103410011501c0194018540e0210601c0c9210b145d0a119a034428a8084907041c18000903040f5080808803c04200210034100188880d03600b040d010100d034400815038401c401622541d400c92250855036001d41854240e0aa1480980160058450440039601600d5940031484514986844002c0500c1018000100414540300240404408500307015140c83c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 909617374 1250 909616124 909616129
    0x309031020040b221203120908120415060b09121f060609050a030320010e011107060c0302031303050a0e060318010b091909061b021b1504030b0603010b 67
    0x10041e4120b2081e2240c041a070031348803141c58901c440c1071014018145107040c14012901031490b401c913806800d1145060200722810029406001a5908406080d0b02c03014020030b20030401d0b0090750b040d1030456860a000810309020710401d030803542140001864003005000303201480050424a907010f0062821001c44241a0071400044030f1001d040043c0d41801c00c1c0014003915880d4200740c0c040e200c0b4400510000e84c1000002034030048034001c810040000c61055405015100100086035080000e10410307012148081d281c6644140c40c1030000300c030a450124124042281d515804145c801200c10209010300000c01a0030320903d4407140044141012400700d900960310355001341d0310000c4007452400d080c80b541202541c11604580282040d0410100d58040e4200301c0d6806640c82401004000a55000d250301c0c80314100c001c01c51001801d4040c2d2a240c020304041582c4100804485e4a407030b28041c1100d40c8000400b0550409003540c50b11101410b00411494041d0350307a050444040c0e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 909618624 1250 909617374 909617377
    0x80606090d20090108030d060b071109060d290603010e0705190e190c031a13021b010c120c020a030c15240906051c020d080c030301050a080309031020 66
    0x20321441c4c00460743d03000c020030039004580d542c9c1c3c042c400d00e0005000d01c8001440b40e080c10368410408690803009074443c0c200203920320428850051001038a44801440c5c884072040c2c00100e0103015110424950350141803600b611840283d60342d450704111000d100a1600c46034103156a4041b1222000c101c0d2204e51843c8000d00c01d480c2c80c0c1800d080c4040d502146d441500918100d0700d03481c50103201c000402071a1881413441703003d245120b100d0000140c0403809640e0b050707945d02c3c0c0c03e24600075003d03480020f19030700916034004441d001490080740c4000a0600f4040c24400809583c020811541c054174101e07002d02600104880c61108158600c00c505064040c0800c07000786640032521500707004051000144540c3c0c00300a5090400ea030800543d9a2104010307030300358004d03056102081d2148002081c0142440005200c007a01003030340c001750b5900001560581c2c0c01610078503219501c0d4100c01d03580340221181c0e1a0325501132452030b16041210303000300e5107091510758040c042c202500100c0c03045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 909619874 1250 909618624 909618629
    0x15051605102a0909051902070c03030e0a08030d0507030b030d09170c0102190807050714030c040504020603130302071208070b060d0804090b012001050403080606090d200901 76
    0x10749407190310b66505190865001a82021140c62402c1c0c680300c0d141c0040d043e00c20511036444250359034000940b81d0301c10307104640d0507000c0980c1c0440d5240710034940303945151014041a40001c0002c0441a4541800c001c60801e07190309100441c248100619680e0240c00300500030800c250b00e0300d0681046031400c01c220113205041c0d88032130090340d09001005c450a0281000c1c00b445900000b005411039801103002880c0b40a1036554074003000b02824029458030036100011f01e00e104025001074144044403003100149422010345003860300040030001aa80151406076000804101203231803125032006502101e40300340145d0b01c1440e51082981d00d400e4080c0d00c01d4070707401c4000800746c04001d070300c684042d4041c3c011a40030300d034100e00c3d40b00c20046010301d0107048000d90341c55401c3c40f00e503801544178200900c3c000e81ca07019180c04d0001c1c070324046c18003540c04402141c46400450309528211081d5091441d020745060000c44594031400001c1c2005051600e4841d40c080c0c0715100d0b620b415214a01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 909621124 1250 909619874 909619903
    0x1303020604080c0102010c0230040b0c0708010b010311090d02131e06240f050c2b030603030509040c0516030c0b01120b010b2b0b030c010915051605 65
    0x1842c5182c40c3c00a8250303020201110110340100818101200b40c086000d07c10241c52486019602d241c0d0105140e0b51045030000b0342d0b54100801e0031082400005a0003041d40c000400921040d03180c1c0c8015010b54584141d03c0a80c81c105000b441c1460500d1564010240e0009000040d07020000c1595000ca500d072510451b242d080c060310b4281030a2480c0500001828090103801109039039102d04007501040d40300c08800c000300d1040b070f50300641c461015039805a02c0d180c2a92601d09040721001880c54000300150303c0100c03440d5800e00402e01a205685c100c1e509625141c0c6400c488008100081419046020901005011851602c1102031446805622036101d140820845090009054205a006520404500322880000b40c81190350a04413204102131540382e420001c1c58502110b0078030000180d0701d0300766040070100e041075004907114107402d40a4400c0c210b0504011500b1184034092004441d22005d880c4010a00c900c00502c9040c03d002c190002c9421190394150900c004941a41c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 909622374 1250 909621124 909621133
    0x1b02060421120f06170f0303070e060403140c04050705090904060b04020403051501030c08060106120911030609011e02180f0d0b0a060f06030b030a021002070503070303030f0f0209030a08130302060408 88
    0x4510344020304961140526940104040038100c01e1103547c1b0320000b8005401c00c444110404101c0d1592820f0b5000345030300c513584242c0d04110b001400c1e611400d1080140c800d90601e130108918034091002c4500c130304000b8109020580e11521400e000d800c4100000da005a420440000420814801c010f10592400650605549035040420000b481500122810340045004100c0503800200101c030103001440d0100d044d00d0340c1d080c040002040e2151303c90705400b038a020459041010b521203220070141c40081c40c2c0700d0134503a50f250100d0150b40ca403411032920220395180030745005110f242191400803e0703a0604904c0b81d58070303136a03204250340c8444615161070050115440849403103000e00789928003000b0060901d00040c0d50b545000c10042e025000325190411194802c2c0068000380078081d044840c41c0360b40c0d1070b008009015205170340c40154600304100d200000399000300c0d40c01d0351000340248440185605c40d010654411142303241c01c0d181d076160000040c0c0310b00c40a000180081130290 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 909623624 1250 909622374 909622379
    0xe0a0c08030408060a09021c0b091e0c01050d0204120f0b0106050a1407050f0609030409050c040503120a0210110c061317070609080d1b02060421120f06 67
    0x4424045840c0c0208003a50000e10091040d401d0000c0c04130351000ca100404a030400300c41c004034181d0b84003541b28001e41000110440c042c0491001e005020f0a403140464441e801c1c0b400e0021400c030405010030000d60031810300314a140d07102d50082c1c2940e0000e000c00501d06942c802203440450320f258400c80d076000483e00035409101401100381d00401d81350034050300d05410114000c21512508047c0c0e140ca000201c0d40c0c2d4107000741005821090a18241143e030b1034244009181d41c2c1c1d0304584150380403581000c001500da203c030102603504840f0094024401c0045898003504650452000001184210719030040c125020703000f030641094a00000d69074482d8203444143c2800001400c00c10306000e4921108002900440301c0c10541752000d044030b884416515020015156410b0041c0501101083c5040510b1056002011541c0900340da903070b41c6070f0940030682e00c0703100c229800f400b100d110001384003810b2204c130324418261490786481200a0142c0080008990141490b0491130f661403009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 909624874 1250 909623624 909623633
    0x161d03071508090f0f0a0f1b0f0f05150f0a02160e0a0b030105060d0201050c0102040e0c0417060408070f0309030210030c0224010312030912020c01120b0915060d0e0a 73
    0x91040c01e1101001030991403d000103c4e9a466120702c10041006200c070031f2071380c1800000320000c05400c9403645142e484a0742d4400040d025402070080e100c0032517030000c0028091411640313600741856050119802d000462410700d40c0c603081103071121705500551000541c0c5586420406000e080407400012440c1404002002183c0b00c00310018000ea1605041c06150f90741c5034000c65406609281c00d0303580d00c89109080780a8000d640c045000c01345920144030403000c04401400640c0c6ea12000c00d800480c041c142c56507211819900501403440411078207011030341d50050504014020308000385030300e0b5a60b02190000103000680d1000980d19030303048401a43c11b0141000070050000d0741051000803041d40d091015040c80014034420f00402c0e05010b50340a80c00c0008190703005001e140e6031907407010000e51103451004182e0b00043c0041000d1400003040d1190752015400580f802c5001e07603507080c0c2c0e01540320b0150b100a61103402840b05030560240e81c003501880c7c1001602400044059180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 909626124 1250 909624874 909624883
    0x204231c0b0f0f1915080106031421040b030406021605031b07051806190b13050108040b060402030a0b03160f0b03010e0708041a0f0708161d0307150809 67
    0x120107558461078044c440356034100c1c140c0500103c0c1030030000803001c04922080001083ca0340c407401c000d50800c0c0c0d0001c2401051038804403902c0d4008107884454500005410031005081d030800e000000a100500c0b07000d446030061a41305200307540c0145040c8003000919200d40d00038404680d41c0e80b0004002800004e03140e048000306004038018401a8203010001d122200408440c18041c88000000340e01e039950080e0f1203d8481c900074444410799261100741e8001c2e804659444410012000f00080c6544180305051040303420840c1003a00f526414108000381d4030190036030501d551984458251940c003403187c0e200684c00341150501c0780d031400700e15480c0b50400b940405550750041c80100050728106140301c0d480079241c688000071b960fa5184c04904420080c0007042102d41c40410000d0f181c01105001e802413102c2c0d01c03184400d0303a8440901011404141440d0002100c41622400c0d803045080c0c1139004180040544034100d440b4060014094881004440012840340520450364014403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 909627374 1250 909626124 909626131
    0x9100501050f0d1a01170706080105031009050a1a07020f010504080306010c0812040620070c05060a120905031216090b07080f030a090201030608010204231c0b0f 71
    0x14005503150200281c02814140d000b64041e0f90301680100c10000e1101841202c110407070780d141d5103942c41e480c1c0c0c11290000c03141480b40e01e01c603100020648601800350641203800c01002458a0704550b12400040c0070b992004840511400d001c0c003000503d044c02600c821191014000e10a180042e40240340802881c404181c41e450714041c00302042201003200e80c4107200382030424a101003803401c0681c0303110309082d040350a4020414081005020b4115a0240404011000e1100141d1070403400320700c80c51000800d0340d00480c8082000e401c00311b0103058000e00d682801e00c02000d01d00e80070006c1d04e0450310125165000064075880350001d80e0060360300718002100a0405030134256010b000c2000600992491703900205814040004150484070b80c2c204001d4496100c1c101010f01c0005004a04422800310b81400e00c0800d030146c0c14801c3e2001c80345e00429107881100249050440610b1815a0a07040006a81d90040302c2000c000075514841c810075200440d460702002c4403c103014080d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 909628624 1250 909627374 909627403
    0xd020c0316060914030c130f0507080106120b040e07030308011a030613020d09080a11071710020d060506030c0a03051b07060209030a060509100f05060109030f030e130509 75
    0x6000141d0310002d4141070f02c4003c0b4001601c84c610701c0000b850007602d036282c66400560400030544604003a0040190307296040000d0005032194079055414032401d0064400089050b0034966020140d5045400310000c05000003c0200d204a2603d003004000d400036008102c01c0b01c0108440c180d00c8000d006a07403100c03500c0745d0441c103003040020341c908183d204401d449034001c1003100c100321a035889180070b6540001480d40e60042100080c140c03a1103080c03124024040c2200002d51100d0100c9da4840c1802c04802400c80130141031b9a0304025000b003034080081a607100c60100703068407030000860080d8068580251600d45142c0010150380b8020407090910030301b402c0310018101140e00b91007000c0d900040c0507031156980e401080c90440a8080586014240000e0103c00400400c4107100120300d04801d101520201103984183cac3d40980e25540003c00c10719080010810403507131a8211071003403411140c42c00034540042c2100c00c40900c81605943e80d0000d225004030100090f26a01c42034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 909629874 1250 909628624 909628663
    0x216080105010311061e13061704080a1d0904060203010512010e0d081f031113090506010b0327010203010609120f110a0914160c0507060c0c05030d020c03 68
    0x150380c0d9084c0490380c03000e01e00e401070714081503240c0e515543c0c50f650034642d00300c0c031071103510f401c56070000c8614203446114900100c1c0324020450000040d20182c1ea01c280d402004403407030030301d101b00c2c111985d18101584010b03403610074111040d1035480340310443c0158050440981c0303a50620003044114000e03c0c00901c42a80740c8503010168800101340c40840c2240390a00c0c10729561580c5007131300498840717600d40329030304800d90000c02000b0345c000b42030740b00060a41d041504480700d42c1c00c020842d040d0020103810f90b44a0320040284a0542c4001c503800031880c40004000905203c0c8080c00250f07941d0007840c0c5940120040c800c40382c0c815002d000401840c01143e03142c801540ba41050030140d810050030003122407030140d080b030302d0b8240c190b0700030000c54208000702200080d443e0407141c415910444104a15458211014454084024001e13000006040090325240041e80c00c582841e00442d900312000e000060f003982e040c840035101c540150081d0440801200406080000303000041162040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 909631124 1250 909629874 909629879
    0x319060e0f1b09030a050708011113050d05010212040c14040507170606090a090921080a020d2a08160e0f060c06190501080606010c02010c031806021608010501 70
    0x111000303998000c104501d01040e0b0441c060b550004911610203080d0b01403040984801c1084000113061045400c840000c202e510144041100340d441051011060482c1d0303101c040c49107182000140503030511408c0014905101010842c815040403079003034038000000d1804100074842c4540001c0c0314101114100806c2c9003440c805841405014682104114110300007031840e200d150840301d4549001f451141030356552840301c000751559007400c4929800b8401c005400c2208075910203d40113054550540c55541c240c9404000d400814000303841c0c1d919001d022a18081009498254806060920014901007034014084240161001441802042810b80c4107584034118010460040310007038000510180091400e0082e000c601245014800a100c1000001c20300403007800c020700001e203d1030b030341c8465036a1501c00032103000d40800c00c110340c018015031043c0d05400c5810310a05008013000c6052818072208081a04108056801003551075a68254400c507200140040c1c0d0081c0800e60 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 909632374 1250 909631124 909631141
    0x71b03121809180b010f061806021207031b080306040e06012d030501050a0902100c0b0a09050a05070608071206210c1e060e010f080c1303080319060e 66
    0x10800d2003440e426642e6481c0501c8400601d4000308030f003503000000030b44696110451804004d4062007100c0124124030309044186d1215641c0d40d0458030f040c0c02030a80e01060041030719155000e61070480c04c000c481800c101c0103482c00080c4510603401107000e5074403450a1404e010865580c2c010f0031186030321083c01000080c0307000450380c0700860030300300107006a9124228000b4041c41e981008110354200380400c03a407036100b40d001c0d000d80390084030000341e090ba4001d42546d40803144400608030400c1040011814002d40d0862500c0704c1c400e204940c417030211f41c0c039130386e0a01d0055000400081c50380020b000c00307903611101030720801540800400600e490304030030381701d90b0000c42c4040703240c481c0700382c1143c0a000380c02ca00381c0e00801da0200748002080a00110401043c5640606c5011403011408621703694440c40000e00c100c0c850b40c0340e40c013142d119407100c1c0c142c07a00301e88030885e10444031041c0440090b408802450040e1031408501161504098041e0140c0d00c0703540100b0001c01c0070342c0402c0b1800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 909633624 1250 909632374 909632417
    0xf140a081b040b012f0115080120180d030504050612100506041202040504111e1e010e01030902040f020703030b0306060d031709280506060a0f09020c03071b0312 71
    0xb841443c0307442e03100c250696400c4c094400000b1480d006842c2d00350005640e4419040405021a03040500000c580704000c4040e44c0d004480c00c502400c60b546500382800c0c145082d680440ccc9000b41406c80c1445d980da400a034040d8400120b0b05050f0b032203001032052540c890844900501011034085003010b041841c07003d0030451002c0c0c003034030668598001c58280034104960801a0744e02034241070140417401001109040a060403500550442d10091810a6441c8141c020080160f5131840384c00d81c0c0000441c060244048140d0340141d88580315a1b202401d0f1000303045092003a1004105c3d1011041010708080300103008034050001302e00b40500090780104558242c441040d990506501d840d140c5074540540f0164034090742d00c54030340c00e030b00d915011607116070510700c107400712001c40c0c2ea080107005980305030348104a0150904003003408080c7d0243c02528651024900b00c0f41004580d0b220081a1010714103030031052101994184244000042440414880c0303043c00b141c003060f901c0ca030794a107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 909634874 1250 909633624 909633677
    0x80d0c02040906020f040b071406060d121e0f0221040e090307173016110a03030c0909050408070b070c151d070f140a081b040b01 57
    0x340b03603076402c0101008059030550703004071510b000240d143c5440341c0d0380e80c20301c0c1e021071070550b6800e20070722402e16401c07800035580e882941c01601c00210080c03644d4544600103000d0a03101c0c140048881e07070ba003000c020810203581d1100c82d542d034015401d016a0000e800e100444861102c0e01c00d8240100314000f4441c400c64040b00c40c0061441071a0303480080b0039045005840000303110059180b01c00364445071600c050645000c2820074580410b16500000f0090304a0b0304101c0c40b4035800100142002142507100c0c021030009003410008203800b603081c02e04140240c1821004a41c3d02c0f85c59950258ac444082c10182100000401450609403036454481c0141180103101200a000180901c5d01c03929100d0210345d485020304080c203c400c8600c80142a00041d8041c0c500f22140c01c02010b140c00094940482c0c00300c200300e12880e410840030089081c4406541c0d85c00618164001036440c000708220800303041441c0c1e0800d5021902000c110545038a40c1d0003a040240c0303030403185400541183c00804 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 909636124 1250 909634874 909634879
    0x210906053c04020a090c05040f0b03071e030605281d01050d1707230a08030423031210050103060501020c10090527180303041119180501080d0c02 64
    0x1650340e0b180b000400c0022660040c0080301d0404980b94401ca0300031010300140c0304e201c440d00c800c00342c840e00295000e000844002c8009007100c049050384108804ac4d50015030ac641c40e0100c0c5854503800443c0400200d0b140e0350300400042e07c0f40104414440c5001800f801c003094160300182c03021000c4282e0310006000309442290303504500d80410050714452003908404000442c0c850200342898021041240000c8151020f80c1c034004484110202da00340e6a02e034040301c03d0b4196261a203404400c040400d00c0280c02c2c0c0d200200c545184102000506801003007409140381c00e2806881220702c601d101e52021b0f0505041c00340c184a80d0307070089403098441030140d41e0035284968588040343c10f11400d900030303030f00105a0032a40d030580c0c00464000f6202171024254020544612041c10080c016581c2002e085403c18408a40007403d448694003069400030000c00084905684001ca04006903004141101c0082c40400e4864040c0c080c150050001e00051b0041c1c0010301d00150603041c9900f030092 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 909637374 1250 909636124 909636241
    0x714030a060e0a0504050c03160902070503130b0714011a0111070f1508011a03040f11150304050d020c0102120f0f0c28080a21090605 59
    0x4a011040d0340c404070040001c0c0900e051242003c1604a00a01003590103a5490090381c0003d8071038280090750081e1a55402c11240201c1e1a105a03000290450142141c40d03001c204012415a44041c0d040400307042622003ca5070b8000780e02d4890701702c01d81c62070f690f281a41040071458401550781241013100d0401c0c02c1c269582902e068103142000340710740244112070102100803ca054001d401c80c070300001c1d20f4541c007180340d0320303800b094409074500c041c05056080704000003800074805045e50740040784030380c40c00701000c1c00c1e440000b9454444070443c80c0500b50003104004c140441004500d00104450018000c2d901903130000070b4032030000982c0c100f020100060b04211600902003141d107281312840e460307501e4000e41f408054503100382071242c0e900e47c0d1114526900170244204081010355101030154a00403a00c441030f01e00107a0090481e02c0b00d90320148020b8001e00600800764031501c1404000b6441c60300002c015900d250003180501940401450396121490303442d81144038585862441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 909638624 1250 909637374 909637381
    0x30206270c2206141003021602060f0d061806050f010215090a23010b0901300605040f03020607110712020604170d1202120a0f0f021201090b09071403 66
    0x1403441000d0a03080d00015880d00f0000503614480120100d488401101c3c594044803005004401381d014800f03034038101d52083c5c0700c034000624101000700701d114441c054075820b250645480900300c4000354000043c1060751003011040940b24071541028103411155101da00f040c00d40001c1d03131492a00b800281c503020300008245007000401440703085a61000d114032801d00c03003104e0025018044401a049503003054402c095a01d012614181a91046400c5440110700d4030500000c0f00e020401803410348950010b4100030070954050584668090140c00410035040d1030001c2c60007500030490020000108480d0040311390200e40801240c41010202c001e010690000038118883c03580180341c00704148540c0741c14850040741031100c82c8500d4980d5005281d2014210080c1d01c130710b18016042a04040006829040035070110701c005080a4000880e503000d022008102e910443c0c13034841402c3c2100040040d420940140fa40e0b003042916514000e080c0000050800c010301102a0140e407c0031001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 909639874 1250 909638624 909638659
    0xb10030c0f20030a020a050d08040b07030c0318051b0a050604172d0d05070c150207031e11060403080301270f052e0b07081303030206270c 61
    0xd0780c06031810f40c0c0d692112004044d5840512143c107e03814040c0c84c44d4540c2880c040c0d0b0310740d4800e80d044441c8620039038820000303c0c0201241501e01c0241552110b15509078810304030f0341702d40796200720001c0c50300c407260f01c8010000c900c0040c0031912032b0408500a100b03940355142541c0031244d06600e6882e003240c01818076824404140010394a0b040311201142c0a100c101d84202c1d0b050420f40161890b1115540088406216140b0003401c4840c2c195020840716000e40e40d46100c1d000345105a42c03445890b030761611410400030511285c05c00d20754250310305003d1203062012102c0b02c119009460285181d4440003940014401c1c1d8070981c031706507906040109208249440d010443d4000c12800e0100c5000c480105001c0c2c4078103650a4403181d4101224800187d0726681c0401a20080015403811144440c260b0213064100c42d01c01c0f040c080c090850316080c403050003a51003178002d409103181c100c828010010526442c0c09500283e008040c40044022400c0341d041502603401000d41c1c1160141d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 909641124 1250 909639874 909639917
    0x904020d0e1006051008010b161b09150f150f120906061d060f040b0d0606030614090304030c0501030911091602190209010b1e0d0b10030c0f 62
    0x45040780e600031491401d07103028080d80000c00f0f4550440f640d081008012038216448032090050044190702040803214865203848403446403440f0f54002c0001c548500780c01c4013440c2055120100140d00d0f49150380400540c0c0740c40340b02400c100096a03020368540f038442703150220881d10000c20301190200f498003903442003403020301441308030909201c9501e03030346412801000503229210b640c2201030246e500d00b54103c100c9600410300202107800349580c401c100002829031062480e4860020711074000051140d02a28008502491001034a07200200d280d0b9603100e001000d001854108210500002e100080c23010144c1d1400e20300064009132520b0510758108081c6450b90b801440030040182d10500900742d800365040581c00e584800383d030400400021018050f000f035010303441c1c82c0184440d0351090040c1c0940b103030100d5040c056544003034040c1c519500407100c81da0450349403214a141402e01e80b4081c000a001d52404104400000c50000c24049940d0b4030b980800800b0002c80405000405 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 909642374 1250 909641124 909641141
    0x61d0d030512150906100509041e2c0304060c03050a02120f270303070605041104180b071715121002070b060f010f050304140a0b040201110c060904020d 67
    0x3400d411543c00c0580042d108010f00c8410340380318070200400200141003070070290910b00003640706c0605008002042102034800c645c07800080f207451000b5482c05c06440d001d5002004014080f4001858111020b0702124440000b100791a42c8100070030484c161b40054140c40d002c2d0186005900c5101e0703858224100b03803088442600804000c58180c2143c40c0c2031000303110820480344030742011007980780da9120750012051050b43c160424800b41010070b015400c03240d4002d108004180070405402d000030211500c00030401d481148000608007004100c0182c0c0c0e8010310746007002d00e80f0f016208114141102d009020014010206000240b2030f1203280300d00480e4007140064850741070740c000800d00250420340c4251160b50701c06012518905190b9841003241c441030351611000166a423058a0651028004850000c01c4055031502c101040c070007907120911803850f4014509181c0001050840c0d42003148660790042a40642d440d0307102000c840035440d0a450140c2c8445480c0c055000909010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 909643624 1250 909642374 909642397
    0x2281106040e07110703080406080f06102106181b1803061805060a0b0a0b0403020307030f03110708071a0a080402010e15121b0a0e060904020d09110a061d0d0305 71
    0x8680409e02036000706690384540c0310741003849038598824040204a074075500d01c2401154042d10802040c2024804a200c0c140103072001107402c0347c0c1e401c148803415103800325010b00d407030b52047c0fa15680c907600414050611004c4c64034000b5610200131081c080001440000d002d6607580301f08003507c40c28038206030b40045c1c1100548000d0b10742529407d020340310500c59140f00b400180408201c003010001560243d0360084c00810595042d61b680d51080014131030305805002c4c4055100d080b01c40c04000b103902412091001c1e0645070719100320401e42c600700c00c1405000310828010016040d500c07880d100d50107902460808214401c1102080406507500034010a03136000042064000b100602010700401d903400c01510039480ea03202c107135614000e01d802d08000602144100741c0c0c42c03074000d001c1c02d68010001c00052801040100a00c11a50000c0d011500801010198801c91030803213904d01c000c0c48581081441c45101001440c010b040401c2428803904c03011100c0ca05141c4104166402c01144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 909644874 1250 909643624 909643627
    0x20409080d06060f18031b150507020a0b0301120b06011b0302061519090e1204261f0203043906030c0e01050a02281106040e0711070308 60
    0x2144490070151049010b91004140d0044d408248a4410b600c80050024108010740b10300d402d554500c1200001e80003010401440c14801050701c564600a500403000315481d11075440341644140421450360350b110001904c0c05000412000b0609441d600b40c440c0e010702440c0c1e4690718000140c0b08050078000b030b4860b4401c41c60342501059000900e5901544031641451202c19008d800c02520782200d2282c01001341c1b5048003080130410580148010180060503150180080d8405654a0704140c0c000208404955680d0000d240f400001160206112006d01001f2044810488100b8202040c10038000c0c1c0c000001000d1282038441c100c074024040500c3c1d19885ca2500402202080700b6110140030404208000f880900901c87e01030748032800d032a4404d204013081c00555640d0402c0b1269015030180002ea0707401141840d4040e1b1000003c01c0c0708002d84038040c1003a4009501c2c001c0e40e6030180c1000c001c02e00c0911401c4500940c0719540740382416020155400540c02c22074241d1009103507400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 909646124 1250 909644874 909644887
    0x24120501140a1418040f06050f01051e0609011209051009031202090a060e04021306050a090609050d0b0c07050d0807030c081009020f0903071503050105030706051602040908 76
    0x10021030036540241c08031040c04000351590514004100142c0003e60300c4104c2030300c81000c1441040610b80c1c41800b03013590b60311400ea036444800079210b0072502402001c10080061156240c0705c014000000000300f804c0c402e913400140869aa8802c09400394184a9005d0070010081e681c1d030892210140d00005440c58460040758140c09005512070460100e00c1c480d10b00200b0b44c6d014130985401c820000c0c140c0350103500e05042030b540340000c1d581c01c170742254082104441090000040c40010221a42c505595249501000300341840341e4000038108405090704002035902d1007c84c0b82c000b82c001486080540b90a44400f1140c03288400042490240002500701c841c0c01c00400f6215007050b4800380414401110100c0381b00901715a00007404020010901c900116507000d040e044076143c0c59145440380d05030000380740c046540d000c2540082d105042040381c5501d801120700401003034000b012124146080a080d0740500034600018407a8540080103640e21604203685590300102c000d0703600d24 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 909647374 1250 909646124 909646139
    0x13090603050606010806120a111314060a050301090510020a090f1413060e1b0c010603050c0420030403050a09091109190b09011b05150a06050a24120501 67
    0xb03d94060129400d14000b0304141016007668801c5802d501c09441c01e40015940c001c0e502c02d10030100c90b0080e50320020450503d0442c0f1602040841c9403103140c00d10714100003004000d038502e400146c06a410503003101d0000303000044014000d03c3c0f800700580c0f2810303614811100403a403580282e08018100ba030024115003a051180342e20784060740c1c0740c00c4c0a220650550300b521000e101d01d003800e8108000252032416400c00340d807094160314003900d00d4480341e01c1f003042c203541003a04240c0712b5410a03e0a0840341c5014030a101111500c1d90490707290840302c24029100c0e000c010000307003d021002500c501c2c458850080c040160020a400700010024a501103501c4e1300304402190044010404407145242c01401c10340c01c1340c4000c43e00c0c1d464144035100449a007800400300140c0398459852110010f0800d100c01c04250740000d1111545140592402c1c003500c000343d020314040d5050b40c2051100c10420400040c040c5020300002407030104090701107401035085c81c04540d0080c43d1a0004c01c042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 909648624 1250 909647374 909647383
    0x2161e12090906060504050d0b0709030506010815150901030312020409050c19020604020a1205070e011e210605041406040501060602100527030d1401030201090e040510021309060305 80
    0xa0b000c5040400400d41c075208143c500384603a020741c40d80400003403000c0c4001802507000303c1c0d02c41054a4000d0140d540c940c1c0316491300c0e5080c0c1044043e030708492410518286c1480d0502c0c0d102d0510300c001ca000d800000b010034002e00c1c041c0005000c00009070314148180c1113940441e001000000b008100900d001e50302110917401411650901c820711a44410120740700188140c0916001003030a00610714000c504c941c45001301c80101d400c0d0181250015080301a000d000e40208030320305120720303a0300340703000780850526460300200700d007045508070005111140030841e8945a482103000525071104e040c0001301e20300c5c041728003145114040c1000104401900300004545540d000c4604481c034030101a01992400c0b2201d94003620100400300341d8600c07050b0858503161128054a00d00038051090106075242c0e00c07064018456094010011943c0c40707800c2c080200000719500d8000e0800c0d03030390107490b00a001c55981d81030303170041440301021002c030ba03000000701446881040b44c6580c0e441d05544a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 909649874 1250 909648624 909648629
    0x60603061903060c120203090c1e062d03040b0106121d10110f030a02070c03050604060204030219050d02130e030a0c12090605070605041a040516050402161e1209 71
    0x41e00e009440c83d41d1786118000da80c007a008001c00b07410410106014421614440664400089181d1100c83c80a4031000010f10074000082a407110a0404000103284803060b0514500c182c4820020800881e030000a202c0c152256032801800b4803111083d240081c05010414402c2d4011080185003da500086c100541c00407405040c042001036091485050003101710001c00c1e000b003000042e11803d1964010080c03248202d002d461020345a8565524283d01140e04644079603000800f8401e51804000b12a2011a000715540d1914280404076100c00f5107444020f01034800035a012143c00c80d80d130010311254614100f00c0b5110212141d00a04070032113180169410790040000755a007611440564040c0c035070a8072041d14000d802c7d0740f01c80c000d08000f8002c2ea140245660360720000c05207000800d01590140d80140610f41020079070398000c0687c0e40c0210f128501c1041940b8403030f0034041e01a000c080d0060000b21511034481c110a5200c090312400600f440340010740d43c054190031114403000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 909651124 1250 909649874 909649877
    0x30a09030803103813060516060e060703151406070c180b01030605030a030507021011060403091e05130b010309020603090102121003051002030601180923040b060603061903060c 78
    0x2d0b070781c5554809018a00c140c0b1617003022040700003824020343c4e002d2001488080502c0c05000c0a61082d40c40b10422503080b51040649904000280b202150745800703000408000490000d005501c0c1514070b40303c544651100e54025400030509070b040c02000b26215005104000c8400085000c0c44008401000c911840e5408686400c00c08640340c20000750340c18540d03906844140c40c00000b6004c000020f03000d000d9910400c01d4085400590010034050300780030364425161035003641c0c2890032090786200100041e00c2c088207445010030003031791150003501841550240001d0300c0d10240300120090034034070901030741102000081c0140ca83c015802001c40400a0010001c0f035203501141183e9130b070b1284405400361b1305c40d903200c84001c82e5a034020354008105040408001d003542604241d5a4000d0b07001080e1155030b640710303010005480125504900c12007c0100c0c1c40d00d4550f58103881483c3c043d1000f40291070100c00146c141d142c02d6400c0b86140c200c00070701c1101c580d9074600074000c1d103101080c000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 909652374 1250 909651124 909651209
    0x6060103141e22031808150c0c0a050a0b010305120309030304030f0e0d031701090b0d1202071a09030705010806090f150604091d030a0903080310 64
    0x920008641d5240c094401d9507118509032001c400403640c2c240d4058514402e2038443d0003030118960044080f045254460384a403290020301d01c80b0440003c8042e800815281c01801c40003020300c0550301c156030b011909080310f549404400840c586410f180950050041c0704000345c1e14240101c0b0381c00a4100ca00c00c50450b440e6100a4801c904a40402c0d00e041c0710550041c0042400240145103501c0341e8185480c00f00c00b100c51450028541d4007a6420503070100e0310a0381c0d034000c10100b8103030050140040180600846031480041562105d6410020f0915000c5004c101c010900c203008030001401124481d88988002c401000c06c00c3e84008000c0d882441100400182540030308078252103000c0c000c1990f20580e9a080b4401b10000c40284078000d40c50b6944000074807907a6240262019000400c0b0000e6001d561950b02050408014110707401c03070b4014444280b005031f000001c41d068a620450080d140e4a640f0b010010b8180d0741d4210703070001c3c8054002c1d0f1002c40003c0141170710f0f0450542051 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 909653624 1250 909652374 909652391
    0x80c0a1508010608040204110f070204050601020d0221040e010303021f1509050a0e030c0f01060e0609160309170703200c0d02010507050123070f051c0e06040506060103 74
    0xd000c105a524812000c140d1800042080c24090002c4503131150020344049140403441e09080e01d141c6c04014941a0442c01041c650203604181c40b03641d50102c400c0c001401895201178020355109459280024001d031700d01d00c0240054988002e803001004081c6484599584a00d4069102c8940c04d2a810701000300c5852f0b0001c40703940d0f0007a505c600c2d03268100c105042d4208001e000203400028000f1010320b88a841c440cbc03007030744108008c3c0038050a29018009182854100c282036501692180c600e452518091160a076102a00e00d03400a2444403641d01c10120701c80c0c180c01800b03003403c0242c10f204071070300d1030658045880000c1071128406c0c2d446248074210042110b801c0361421070000c4450384010b000c042c2d103007022034032090024014100301e4281001a176910742590a101c807180132400b22005010040101446e180c0e030480d446040c22001c51101c100000c1c11400340140a20048915200582e1154915400541c00301c64400c00e4070a145800d00f020355641e8420703280d03680004d140c0444c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 909654874 1250 909653624 909653639
    0x21020604141603030f180b09100203032e03050d051209160512100204030501020405100203180f12010e01050f13110904030e09040b01180b010e0d060e07080c0a 70
    0x10206050030780b030700c003100d032415528202c0e00c440c00c0901c91018000b02041410070100801c0542004043c0080d03699940ea10b07080901031041160640c1c0b40a5600c00c1c01805400440d0b50141c0d040b941031440c3d10715039907014003140104184180d0001d032180c0518070642245c1c550050003000e0342a1003112420840d04c41245259459103503178044113081e0105c20007402107181050303c064151144100301d88050071040c044504903401070340100c40582d4009401c0003103041070100f4000103960b0740051810221241b0020070094003480c00b46110341680d410005150b42c032608412642c08200008010420754000c0d814000c103070a581030b600c0348520100089411041c87e482a504540c0420310303584c41d58001c0709121115401810480900c040c0f83e070103601a4a03011040382c0b20f2802500f5040681d45055200300354945a4081842118100400c0c2041a42c000000703807000e0724140c0f51108407050f1070400c1300c0101410020074503180146880010a840000b54500700500101c8101c0c00940e41c0381d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 909656124 1250 909654874 909654883
    0x7080106050d0f110a09090b040501180216150b091501090605030604020c030c0a060b061602120a02060a03150503060403020706050d140403080f060a212102060414 72
    0x514000450400c541d0252030700302e8200814424074241c01080d1140382c44d9400e11182c012a182c0e0001402519040080100c0d034003429100c1703081600c04200740c0d410312041041042201d2000805680c00140340c403560314a80a00424107a040805480e0011030b5618140c00761402c485040d200304211004508482242d02110400a205031218904280390103401c0e1010b801c000c1045078000ea09108537880800700340000d15849400341c002d06403080c81441c04030116020503107003d000e00014410303041001208140032003070580465111804003c0800c01a02d0303d00074040094002e10081a1305a505030590400c951544038201441011501e5006160313890b04200d078068010b034009501008598056002807660300c1c00d078003011540b00e007803c80340020b0207002d80307003140020174035002c0003003102005115513086981120401c3c0c0443c5000e00340350010644440c00020420038001c03000800c0710f20814103020301525840d000e0641c080450113502c404040310162686c2003a03c18505681e600440e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 909657374 1250 909656124 909656129
    0x60905070e09070c050a0804090507090b19050930070501030e15100e0f0a293003030108390a03150b120307020a1806150305070206070801 61
    0xc00b408003c1d600d2010072901d40c42c16040654041c010f0794660b801080d62034006202515205401080904080744000c00c2044e86a00480d602784007485100c000411806a4102d1107406190154407412408002082d01c408210360481c2c00da90030603141c00207425000e05416000c14038050b80d5400760740384015010b84510514000341a0800c1036600381c6c01441802046e00601c4000042070225182d081151034101c056940b494115045c00c1040b407407805502030b03125143c106504000c91102d1650620100c2003503030700c40c98410980d8805141002904030865000d4100e41900c0000c0200c0c91f06a0b1074903648203014141207400780c0501c1000b0004d0f494000b415003124140c80c0c94000a6080240071840020120941c0c80040e1aa0010201e00e0068200c038810f0314080d4000703000d440050402202004869403121643c000b448000c0c056528080c58104a4207902510101120400381b0400101140c1d080304606286c1d0b0710812582035496409a84509035a808903030b03240e21003900a8032028402d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 909658624 1250 909657374 909657379
    0x5010903030c0c020a030f060209030a060f060b071a0a180809040c030219030b03030d0509061807180513020402030f19150605090406150507020a0e060d120e030105010306060905070e 80
    0x180b13170400c0019120005220090702404005051091030400039040085900098075025200d0041000003001442014000d20000c10440d10b409450768400081d9000a85450310482030030002480d800b03465040200600c2c41031501c101c0c20442450030607002d03000160b1590150303152001c10b0003001c4c003030701c221080344009214160204d01260341c00c80113400d0810010307405002c20301104103054072600856000790459005000c1c00d2410503e000e029460080170b201c8154000380e0100071050018a8110103201c5c081c0e0b022500d2b40c0c2c3d120080d501840c0102d402508248000100a900c030640a5900e0180703040600d8245200401074040041e03c071f5800e459002c18103201e004004c0e0301d004000a00034000042e102040d11035840081030407804c0c4400000010440010303014046180214044000d007a00500c01c000504041001c1094000b2182c00240399014084507121024009d00f082c0c0300d12000240240903d43c1c480c9080c50203000b592082581007030610700480c884a0140f4a000c1590001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 909659874 1250 909658624 909658639
    0xa061104050109120c180228080105040e212214040207020415060509040e030c0a110102071e05040b0d0308070e0d232104090c03020c01050405010903030c0c02 70
    0x90004034500f9080000d005c441c082e0104100080516014160560845d2aa00c005071290b2004844c01c10030a0700c0819450100f0035180314144054100c01558103492080d540059a82481d1000ca80307400141144451a064114840d4810144c014000d1841d80e0501b9211500701e001840a0040b20314640180210f0160f402c900c5511030625074040c255a6000402c0810414400d900d860321180841d000b582c00628001402441c60400340610321050030f000300114a0540c50f0302e04181c451244060040a50442d600114800d81c07081290343c002e440c0c40d00700c0da0320719030741a1901c41da84010b9200c0da44c012404c092a28240307182071068104491380540f10010203558a0707100b1107110030300792046a400001040c482d008141c402c500c0b042000c1d804519400700c1d0305130407812840c02a8505154803580030500078885041c03e2a01500c084404499011550403e070074800c1d000380c0030b4000340584540c070306007c010074083c0540050005501030f80301040f0701c030b0818004482c100003c10020b50400381 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 909661124 1250 909659874 909659879
    0x20c15030403030b040b040c030e0d0c0809060a0c140d022b08061903030206180d051c092001141912060803030118061401140a11030c0a061104050109 66
    0x113508a01d00382c6900800c0044c2c0010310701e002400315044250703140c0020b9a1207a510204c01c03000c000500f4401d0407400c0c5900d81c06025a100401841071004244c09181d01003048a06180580b0440390042c1d4012007a510a10802c0000b0b80e880d00703600f0001006228200300c041c3c8460b00111418195200c1c00c4018000c1d44003200151242c55014005540040351700c0c12613155000701108503006188603902402c0181040d060782e0405800701d41d9441c00340e40004a0030302c5120380100840b00e1605030b000c08040090014540344008000c0e240b00600822012410800c0c03043c6103001395040f0318000d80703840d50486100c00001242e4080d0b50004112001171501004c14a07000d040d5a407184454403e010a40b19152481c69055030020303448111a01c0d1080541001c0380128010390000e0940c0d0f256091801c078440e00000d14001e4131541c010b40101c40000d0f20b01050b4825200c00f051102424100d81c0e80e190b0b40c4044030703990741c01c58500340d40c02c07494881040d505480d001e0031601198416503480b03614a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 909662374 1250 909661124 909661127
    0xc06030b0a080601181a0901051302070c03060203041509021e04020705030c0d0f030203190b0d060603030f0f0311040324050c0d060b070314250f03020c15030403 71
    0x154402400c0d90040d022480003603000c40410049010306000820000300420041d042e0b030685540b044140c2d400c40c3c1c885203200050b01c682800c5c034112001180c00c232500d07001e0749150308001d2191810141450f0300000740801030000580080d800340307108450300394281c400c04500c60111803403190025408a405111401202200c90031404840d200074001031400c81c0903661245160b00c000540340541c0c20080a01030865008204001500100d04096140d071902641e541c04d03c1d0188030b00156034950391021044c60380c6845941d582180d0b800002000142e8480c01e000c1c0030380e0783e1403a0403800161040b0510b000c8034132a0044d1221180000040c5040034110340e01c0c0c0342c05880144001e46e0740443d40001c02548400c41c01100d000f04000349200e85d0341c00300d498040040e40c0d03a5402050000b04204108800294080d02c40f40040e1210400251181590f03058000d4840042c02084c1c105280520f081d01400100340d8000d81c228425000c40d14500c01c07205c02d100c1e15071840c00f00c1900007542800004d012a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 909663624 1250 909662374 909662381
    0x6080f0c0c161d010b030708131103031c06080a0201021902040b1903030f031b030e100603061a0a06020a110a15020a0308060103021305010507020f150304030f08040c0603 75
    0x50540c000341c580ca000c018040909601d020351242c0030b85000c8025000c030710f04001c01201c0c050000819001d28507d848800071f002030901900304600000c00c03070030160900c070000d041c5103a000c2c0010192541c42c44a00240710480c40c1d500c0e401182caa1604100040e6090002496941c565068000e030500d100c25182901c81d0a4a0050590f000750b102d100c41c100c03a95402034043e42160403480107960582c21401e0040c54400c0515410b0285460f0400c00303100d000380c076050100d120342e0394500800e9005260705514148100042804a45400d1007004010812300390040c0300c220090743c1030700214180d55020013904120611601000da04000107a401103243c1010000303200740d0192903806039650310103250000c80e02912025005030040c50814041580c0030700c42c03a400c0402403030705600f4000006a1210594601e00c115414048000f4501d003c544a10105552001e8018103000c01e45001c07220086e0198011a021000254019803a403111402134600500594220040e543c40354240101580207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 909664874 1250 909663624 909663637
    0x20a1d1f0315120803010602060f0714160503180f040606050a080c09030d11010c020c0108010b0a14031f0b030103080414010c02030a05070503010b090615031b07030c020a06080f0c 79
    0xc80c01000032410f0900c0490641001e84500901e680d2585090402800d220014064030682400d200030b12001c282d00251824104000b080e00c81c1d40c61032018540802603402440041503404003041d04003920079001c0c190507003481d0a9440c034800c4440c0c002000101d070500c1c0203410200c2c1c014806000150301c00d1011a0344282402c01d038501d45100300001034544400348500100089038000c0c40d803940d40742801410501c821500040c0000800c01c00060810b101c1405030312450324002c500135030704611402c2c10340d156806101e00180c1c1e034286920603040181c003400c000090640118000506040c0450449040b03d40080e18241010b00b0800501840f01c0d00440542c100000102c10802580d0280f04090320f880c0f05034001e101c0c1d13501d488285429a502c0c200820301c070711038000811405032201d0510b0320303200264000c0142d4a81e6404100019000000444010000013062041c10140c000c001598240c9c0215a000348e81641c96104546c0c0715011134002c03a80b401091b020030912038403100580f18 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 909666124 1250 909664874 909664901
    0x21e121b061f0504090f0b0709170a1704080a0201031e05101e050d02280305031c05071e09052e0509091305030706020a1d1f03 56
    0x10208148501546407800c00e41d8002c1c410b01d8000304540c400c1440041c0c00004120999003880f42c0c2c8100d8440c01848130740f41c070300640410000c40014600c0f62040e4200400341082d076141d50b0340c03850307820380442c0d0740c59108000321201c0760103103100f01a0b0020720342a6411910807100401501110b80e0044018000c150540c9a6980d0340604a101002903401058840c21f1190b804640480c07400c160859040d030705900346589a40444030030721094840d090411817007030b0141c9000c22040c818000c2d981d006650340c03110108034480c4000100803c40d003c001040b0a80d00102c000c1c1840910300d6000c000c50b40152008004503480c0101039040c1d41914181010b014900d061803109140d072400491046c182180365400340702c3d003403090514002d2584803001802a035919016003440c1d0550040342d40c418000c2e0484034200001c0c0920010090708000310348010b50300c400d0654503042444006080340001080011802c41d280707140d110b09042c40f0000c464080d44160304268030450099042d00181224102e184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 909667374 1250 909666124 909666157
    0x1502100b04051b0c10111e0a0c02040b0f030102220905060a0920041203030509030306010e130b040216060c0212190903080403050705090f0609041e050a12021e12 71
    0xc840c20320506c600b100c5540302d00d03d1290b669912400c3c0140030340300201e085000c04000d010301200309034001002652036505072000200354040100041c2040c071541d00031903156000049a180440e5a07a101e00c942944c5030f480904a140c540a0b85425900708a400c40e42142c030441d810440d03000d03140c014481031010785a400d814403248454080056029030005e000705c1385d00c103000c3c1003050b9262084030350061581010b50700394208440000e002e18079061116105103082c1c1d0242d14801c0c40f641c04085e406000420866645892820741c0c1a9031118000948005251124001440d4000f01340030007001d4120300003501d40750900314811043c42800e6000d00c10171004420100000300390074006c3c8042e500403001402e699151200300142084001d0200e80c3c0c580031107040c040c441d11035020341504142e12009403150100c0720500c9448100c00c0b00c402620510641c00e91800b805103101030382e203120381180e003580c0c02c01890b4807130140c00e24075a803082140c941c44840c88051040d1444040d03c0240901c1c1c0004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 909668624 1250 909667374 909667393
    0x14030903030601081e180d03021819090606030b10031a0118121b05120705061e03040b010f090209010912140a050c01201f061502100b04051b0c 63
    0x4619071207048640c01d5006c41c1c01294405082c2d010425502c2415152800390316000030191581c660212020000d8001d00b070507441c84400076400c4a80d4409000da5100822400390b49601c010702519406100034040c540f0b403c4030300d0311244079005400540e07000d400791414442c5503c00450f154000982100080d05e003290b000b10b41000c18114080c4140c0c058180050442c412401081d25080782c0d501403403041d4003c11440d01005000300b00780085883c2280c1958940b82022100003058500034029030740c0703d000000b0402007200f4a071140303043e5040083c1c45001f054586003980c0480c0b2440d080b65010440d80e100800c49485411a001d2980e40b0900b040c0e00c02814101400c3d01d000c400120032145900205904025943e01111882c00030f031a0094054104400069041e1903006041c1c0d0398001003036640c200c16000300380b80c100b54003d10b090b80350500c2e01401c0480007502c60f021030031b07990312070f50038080302c2c118502d0207014190040003544031403440b00301c0d6020400030316800044107040030702800e5541e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 909669874 1250 909668624 909668671
    0xe04110f12061509090601061809020301090c090b2526030414070620120a030603030201050f0412110c04230a111b0313090204061403090303060108 65
    0x102800240001051281080f000c81c0da640d24904500c14081c0c03014404002c642800058024111384c80342c10b0910300d401400540b09541555508041903040c000400001c06020035408248400410781e5503d1640c0d40358810b0b0101441050701101c20580070151880d030110381203c1608500d0711454580c4ae04204400c074070000d96a4929030015821404001c000602ca04501c05180048038030019010140c1044c101501c00c1c01040d40c840e042c10071064010040f01c20401c081d100e40003152030b01d5a2102403c200c0100601141e000440040d42020085102d2454001c00300f800b40d5030001d4411201c0040440442d2000c108925900ca140705242c060801d60300e43d8400c00c641d006c002c1d868070ba500d040e8250540660040a4002202c0300d1402082c196890096000d4984816403010030078260307240e0f6180c040c43c502a00c0440c00c900c0c15004000074800c2c031940d00801c200c800320749540092502154091061f4002265448039607081000042c04a42c4540d048a078409110b040314040e01c03c21810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 909671124 1250 909669874 909669889
    0xe090105062523010603021003020a020c03060c0d18082b05042f24070209010f0f061b030e04091e0203010b03071d0a09050d022103010e04110f 63
    0x10303601000c0060243e52103214074001c40e01c01c0e00e280c0740240140b070b10710307404100503800054502c000c2640c080f600005083c42440300149510303004003114542d0170b100121260582c0010000c1010900c0d11142d4ac40340b0104250038281181c1184e02641000d18070f13590301c4450f00204034000308015440d2444400640030f072113130501690150702d400701c41c114620100c00341010194041842d0006501020807665074015040350080c2000107102903030010b401d106207003405400d4000790310000300d0001148142c03901030f071035088820360a02000c2d036030b0355450252030030390140c1c614101c0b10f04040c08000100e40608600d4500c000c2c0900b001465035110303165000320101031080000308151080e80d4a0951400b4000c0e000050001c43c088d0201e14508883c0000b03000100c20007800658501e030000399114480c0e8410b00d60540c2040c1500d40c40648c6800007502e0b201901c2c0c400344014081c46080c0e50341c0c88803800366411b0710012007540510f0b0b1240d4071208481030381100e007507500c11400030724120191145030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 909672374 1250 909671124 909671197
    0x50d05070603050a0203010e0604110f0a03020d1107020303030a0e0a0f030e0a06140409050a110a1e1805011101090501020f04170a0803041e05011a040c0e09010506 72
    0x15140003810204002e0564101400030301c42c0728010f200510504010f044141d0704888100d0700081c003030400a84060311030140500c803c0500e02e0115405400030b0f01600201081c42c82e00b08100181e01000880340c1903800350800180d0580e20903c0013620040131070340403140285490040700c0f18441c05170340d4002100ca50043c11000502c4443c80c10b9030030304060800c0c0c405000c0c1400c0c150703100140c1c1034180801d4092403003500415a20b46011500780b48180e440b5200d000080100e050342c644c1a150b001e4100c5180041c3d0342176210803000c0d5480304900c25944501c00030000003001d2724a07403070030004440369101c0b00889501035585003080c1700040c100340f004001e0340c0c9041c140c1a0301c592922558240440c80c1400b50b007003d411007951040000c12403c1200e41c041d038000008034140c0700a000c49000944401780040c440d62034604080140c950290440200080031902800466190b403011105140416072084c1c00004c04001440a032800d01c0160010348880240801e06101030141d9148804245 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 909673624 1250 909672374 909672383
    0xc040305060702010c1d0103090f050a02090f070527220e0a050a022e030f0506030d08060907050d02191707080403181205060f0105042c0304050d 64
    0x1010400c0080c1444890307070008081c0005c1007001c01c00100030303051185c4041c840343c0040071100c2102c0300c0c0c0c0c020b51000c0c229641240e60558481c4003454116617590001500341d00c111880c50000d50103a0640f80d010344640225078a00d03060410462100c0035012024082710b508604446545010740c031804840703140703441d1039001e00041101000800b004c4807214400c107080c1d038000104aa011400024071a4003203541035548200c04612103031040015031000050740e0f443c181020b0b00c420a258590400d419034105600e04004035100c1c41c1c2050354504410950001066010000400515189410640c480b100f030a10034a401e0380048003000300d0380500006010795013918203800c0b2040c0d000000d1520420000d031040050f0a08a0000c0d1010344010401400c011581c600025000c020101c41070041c0b00c20012a14140118030b804d6131250812201c02914480074400001c16103854007031400c0c0604204080d00365040e240f002c052840c4044501e00d42e2504c010800001c0700c0d152142d2460b00107014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 909674874 1250 909673624 909673627
    0x30c1b080d030c09152102090d050303060f0103020c100c03020d02070b090f070317090105090a080c091b0a03090c0e090f071a1b0c060f0405090105040912110111030c 73
    0x20000034200c10f07134a410424644640c20b02111280350480700c1c409241058903281d0b5510700c815500c04010b480748048842d01b05900c10005000c00c8000009140201022038441206a10350401101203002d42440e202c034540c040b4030200d01c0c41d54079070b100100f011800c2ca4054508062404060706a9100b00303000c0310769a84940400030b2100c010b224004200d4080380141442c14903549481f1906c040158000340c1045001850080c1a03000c0c0307045074203100000e4210075503240d407655036035141c1c0210400240103a40400000c2e450110b00724844c400f044840411070b082c0114110102c000740800c0c04205c9054240c28800300b41406c0c050842c5200d183c01c40c00900b0035445c45040d1038144895944100c201680081420750700e0301420701035640010680100100303001c2220304003031809000c200e000d80c0003c00050500309403a03814008100b80d400a8030142416640c580500003180d4035644080c000c2810b40c41e501d80710601c101380d2501211900000810300e07010140e904c500590081d5108184c4050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 909676124 1250 909674874 909674891
    0x70504060f0f0e0702031222030509011101060b0301060c24050103120c11060c0114071d030a0507030b04150e0c0f01030e0d050c070e0a02040503010608060103030c1b080d03 76
    0x9140645000c1e10800d0304000881c00c02644c00303592809681d40d103a05580210b03000581c22243c00d0007015041508111240300d604550402405a500441405001903040c042500105034140a14011a01403524062642c0e1030400c00f00c0d900c5c1d201d00703402c490010000105a42441c0d02c001c5c0b140d041605040b00080390351461a280c18841400c4a140c07041c007003a5410b8002040542020307224080080e50a01d90f00c80c4118803003030041041e50540305d0704170030303030402d04c0803880c1c1c008865807981d03041040c0f0060141000c01015524107c807c0c0042455121040034000100f0302a00150050301c240170004403c062543d0380300546030703007040424003503000b01a144d58500e40b00d6081000c052082c20104580710781441129240c1017411005010b02c68001520200c4100030040440100441221300d0200d0804d040d48801961061040310b21a6003000310100b05403402003a094100d036070603201c00740e88054650303d18420300c0c00400080049084217800040e01c0c0d87c24403405405c10195a0002140341 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 909677374 1250 909676124 909676139
    0xf10050601030b150a141b0a0b010b2a0c09160801050f01020a0b0705091009080f0f0318040209270702030412030305090109050a0c0306110304020f040c02070504060f 73
    0xc2d580f000e91840749600c010440c40400480040f6540c0002038a88803962030181103134084a4881c20f81e010114009495a03800903450228154040354032072007040f4816683c0d0981601d55000d080034011081410180040b0b6681d800d81e400742d03012a0b090150382e8007805080004552050842d00e02001380c3c13103025607000f41544030002c5409001300302c8403641e8404440000075658101ca410051454125a002c100601c2c0104103980c3c40001c000c2c1060f45404440d070340148048018458600c60b4440c600d20310380b8900c0c0c0451403c519030a520011810036400c0c1d94211849100072120642083d400c00400710381e9113a10040b80045070307810200b080041300140003000c0c0c424005000707400710b4105110920421040303004000c00d098040ca804a800e89595042e2801080d21b180003c04da440b640303504e10104100b1803006400c481c01840d082107440c0541c0b6800103644004c44009500c01c2154901e410030f440d00d5889500c945e191807044a80140c1c82d03a01090840d8843c3e0410903041c0c169480403c040ca = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 909678624 1250 909677374 909677381
    0x1060906031401030f030903020402040b1b0a031e11030f04032a0909050102040801090308060a12121d030a05011a010e0906060f07120512010e0f070305090f1005060103 74
    0x61819260070480b007030341201d2142e841141070200030f0801300700d40310708002c1c10700c01c0440d00042e41d00204119640c1383e580b0f1040000380e12030f0001107917002d403040b130880002e00b001c181d2080494260311901188001040160f1003800c0005c0000705000207016a40f0102c18100003410038803108030007141e584c50560134445801e80c0101d090070032901c5044c00c0c1c44c1c0d1280300c3c000b03890122480301d08003051030905450414068021508850595880d20b402002455031003807a40380600d9056904101440d2140300789610b00d0070240b8003411140102c00920629032240405050700001c0d401440e40da00307400300001e814003a034004180c0e81c623074580002c071039000031540416003940c4090800750821340552000c1203503080010b1005118031400306094000c4a10941224002c0b03600104454481280f900041c01c560400c01500742c035042c0b0b600010903486218103e0500a0b420650440784aa0f20722204601400000703004d40e503140103c607004510b48108120001c41000d503001c0204407450700000040c01c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 909679874 1250 909678624 909678629
    0x30f030901060531020d0e16051c050604021504080d0e1003140105130912050c0c01110c19080a061b0906050a03090f02060c0303060a0b13120c080a0308010609 70
    0x2401040c80b861030b0f02580200340003580c040d40c4c0c2009078688081401040041040c403041160314010280f03034144802c003038890503003500d0084440041010154480b203220029801c4014499071017035020502601d811104c00c50b00c40300b2594094903081d11005c140342801e002c004600007207003440e2545601481c00c0703203c1901800003468100549409000c4103a403501043c8549400740042d8529032010303240c240c03c5158940d800c0244840c040000300b20003030040d80701c0c1c050020780f401044d4440b0325a41c4680589074014600714010561011b2176800c02c01882035154802c44091444400004c02050910098400300d00484c0b002038000d00c103451800e141d440034403007107081015041061081035000300aa644c00070480c900060340d40d0321494240701e0320f8490100071b54401030116240104540001c01544540310645160a03841c0e5150913007881405280001d0943c0c81035500103120401281800501c03c0e4052056030b58080d0740d0f14001414201d2055041c0c000454060060144c140c118849600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 909681124 1250 909679874 909679909
    0x110301020310120204020c0d0c151103060f040b040507020c090609090a120e03070906090f1514010e06070b1e040201020312060301020c15100b04080c0f03030f0309010605 75
    0x1d1480c20920841c0162041d004546400c4070910b0040c1c1552281d5040e106086041400c4620200a541010b4410b40c1c000c00c08a0700003111054015140041d070007440c0c80da9903807000351411606c1d0355042020242070380640385e42169955a08801a03030325402458041c0745540c010b005184068424008044001030103180240305110038000d003a000000c2c0e04400783d0f008010000d40c201111000c95240104210582c0d040c4a07501001c0342480035948200300f2608540d0080007003902504060382580c0c000c2c001c0c0a02c07002e4244081003081c00c022000001903105140c01c4920f04403400c0080c41c5600700035419a0540000400c01c50800c0c2c45080380d401c041072008071007801340303000da000030742c1d0707218408056401801070303408540c087d01c094050300d8100c082402551803200342c82c090070500c842c3c00c6500b0500092003000006091002e00122800c1e2000311001d4501c0783d40301014001e00940b0103100d81e80511042042d00140200380380594016680f15002080d400e10305801c2100c46214401d5049 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 909682374 1250 909681124 909681127
    0xd0f0b060a0e09030301030f02010c060912122c01060509040f020a0605070b0a150305060a29011403130b090f120c0a03081506041409011a040b0f190c11030102 70
    0x520003c0c00000e49045a50118130000d04030790740c1c0b00480d208548650004c0040b401d0a14241c1001055152400d00d071619545080007818036080034401d4030b10800e16008403c010b03600c91882030091040d1141c0e00510b0800204905640b040406c40320102124260780409080c81c0366030841c94112004d4004089a143c80b07410500291181c0c500140040d2640070760f0b47e5034607035902020584511071001190804142c5076145000c9181d078001c2c0c901d84280d4140c2107900103015040400740c0c0044030f0700c548181d41315404c55440c2a480401580040c20b00e0000c500c40c82c3d0800b000400386c241c000d21505120000e48644201040c889141030050503400544680034420515403100000d0f01503c0180c03d8500300149884940b010382025038602caa0540003140014045070360f41042192755a000001d4841f098141e907920360400720800310384c0400d00102c004210070411741c1e840e81c014001c800e02e500c0d110f61911024110f004560404000101f02040b60500b4130b0040c000c0d022446c0b640c1040640003035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 909683624 1250 909682374 909682381
    0x306180f01062609030306090f10030212011b0504081204031a13020907031a030f03030c1e04090902010e0a0503070b0a021e1c0c110f0d0f0b060a0e 65
    0x114003401402003008122100c0a8015029102014280410007100c0c0101e140c3c20a504410b80760f600c01c0318110f01844002c1c02086128000b580c102d0702c1204d0303108204009a00b980d00f00805811180c002500942d00c1e40664984100d030b5425076203c1300c045032121942c661a10304c0d680c1c00d04001900a000002c4144030070008a00c1c000200301036501032500203150b564480f008850380701040b00d0702a4020301c2800c02c0101e04e58044d44951242c010740307850f107843c5c00c0480c0200741d5111010583d81550b60414404900540c00034405000103104130700b0300c280300c05d000000040e0305410550104088580fa51030340c5082d9604880400040d001c1030383c0002400b41420007007651280c07248609801c074600000c1c0254100c1c4240020320980680c0840308400d410900440e580d140d00342c007140c03011251214200204d860081400c0b000b0300b6804580b980c50904140100035000c81100c28241c0c00036003000c1c80c1d0000955020302c44580b40d10450060501d810030382e0500501401ca604240810079032407060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 909684874 1250 909683624 909683641
    0xb03071d060a030f090c09060f0b0f0a08060a2d06020307020a060f02010b0406090603020414160806010c0227060d0c090c0908070603020c0c3021030618 67
    0x1200ca82c0c120b1810003160340304101100200414019001400b0325280c054042010509900b01d0021103000a0800c18040d4452546c1a00c078801c0380021032003020100a65100c0ca401514000c1c0d101000510303081e24656948980c25054840342603105042d2840f400c10f00d4075a0702d41c3c03c4c3d4405813109100035400c10b500390707010641a81d00c43c01440f05020000800d0b00921b80700750060030742140b01400603c006552003480d440506400d001c102c0c411801e002c903000c02c007d801000d240c0300d056414000ba03400d00714a038041c0c82080018000d20304000d8503214074005a150a19901502a00c4141400948500c0e0121810460015205c5407103001010117401c0881e0304c901c81d2030117580303a82400194098222030705807894800b99014060900640100180d03d54066000c1c01200386824181c03143c01c2030280804c1040d01181801901c1c611008500f400118160201007122854410454401c46c440d5240c014a07050b40c0309450302d580701c00008100301c1e41007a01900c1a0141c0c018001c40543c20190789 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 909686124 1250 909684874 909684877
    0x1090f0506090405190e0a05060a0203040309180902060a0f0f11120d1805101401050901030b060f060c0a0c0e040b0609070212120114030f0319020a0605010b03071d06 73
    0x188148038944070401701d0300100d0300c03409500039040f0460080100c0004440360980711070201c071040d0785500400b000107a00707003600d0084038440d1341d00d55120070001d030400706250202500c850100354441e41d200391078001030300e0b42d2000b0440c0044540702c80d407640445074001007001100c0341c402e000300403400c2551413640000281001003052000b1040c2c0e00d407035200c40090014000702e0744000f03020215030b01e81400d02c42c0229600062500ca454140406400e00d0341c840e11f0314000384205600a4000401080400c007481d10594000c90003c0c10401e0400100f8002822a0420640c0070040d4008507001c404204114414500074034034505044080e29054803043c4131010010015802506d0400006a0301c034800e000c18001041641e6100343c072a0b01110005400710801d0280f00410701310003194016034580000d0f001c1018414100071890b1000d0040d01c050811101440d400543c0b04944c003150000f041c50003002c1c007030b0084201082d141d14020200800c250034002003841001c41690420b0710940b200d10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 909687374 1250 909686124 909686137
    0xc060806030f0c012c03070b0a09140a0306110d140703270b04050f010908030a0b06070c05010518040f1b0c05190c1502060109060f050a0323190201090f0506 69
    0x280b00003240c00c1010388544440003030b0b03500c5c0755040c000c00a01044028100f40a404d080c2c0c0f4542c0c48000141c2c5490318940425078011103e44d0284d2882c40400c0019400c0e0415484041529000d900b031554007040030b400e076044030003511340341034009040014403076240c0324500c8010034841900318001c01562440001d450034180c042c000050f15400941408001c00c075100741c03d02181d000300400702d02c50516101980040ea140141c072410000002018a031003030070713a01142d4120440001d0645000019141036018283c3e41203001180720345140d00d070741c0350b10403d001c00d400640003142c7d0b4103901d1400c2101140c001d100c82c1c2484603034640c94000c2800007a802e20356000f02010400303a4400d505104510252580c8050070703a079185880c01003110743c0441c41c98100c94142105121403a1a03810400b0f11205601455030480300013682007020940d1062400d0360750340c03500850140321540e00011420303c229601181d0850010303142031011942d200900304000c0004001c0344040508180004049200f9507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 909688624 1250 909687374 909687407
    0xf06061008040215040b0c010209040c0801030302250513060e0717011401020c131b021c0305131b031103010b0108070e0103060e130c090c0207030f0309030c060806030f0c01 76
    0x8060070120010302c4e404840c0500140120f0a80755110060003d010b540031141d4180110300b0400100e0140d0300992145050703c1d819000790807440005c40c0000646001c0007109882001c0c00c4200041545440290f20240001d109000c80c6031801d0a50210310440e018000208000007011640d150b4840c3ca030170141501d2103100c13692014041800100c0c03a08411518a80d4090000071664988010030307800104c4d5000325198a4243d908940c100382d8441000400c0170004140d68100041040c1c800c0d40700799440301c0c280100d015004519202c0052040c104502da0b001c04424807024801d00851100101000100b00c1c020300c4000c034035400080140e140541910280b01e00034100c001181c7c0a50400000f600c2520344d80602403500350408080d000c5006010744501c0c0b032840340440c0c035540c540281000703025642c004100d500c0c40c2da59641154006004180e0410204800200004544c01184001448240d54004060819004060030314842d001200f4282e4020240c000c07840e60001841d00340c00040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 909689874 1250 909688624 909688639
    0x2090a0e0c13080c222304050f06090309041d0f0304052b230a030905011205010302030a0209092a0a1215051302061b010e0601030b0c07170703020f060610080402 71
    0x2e01c030b40050100c1c1c0004404003400f9844c0000301e0401c06c00241c0c0304a0052080b603a02480d1001c003a61101030641d00320b28207400400c0751150b141865013000e080004607040881c0c1d40b50303071210028204078942c8a4142250000641080030340341180e41646040464646c08405482c030107403050310b44825910080c4081c00c209041c04080082030742c0a0a140200415140c03030b034107a440d000b0321010362801083d004c200484280203508a481c450641070780e501400401c920013013502048a04d5600909481007407042040c0c040c1e1032002d440343c1d82240b4501d070002842002c200c400304a2441250381001c200008181021408100c0408102e543c407c800c10700002c141e1903000c410b08056440c060301030f41041001805d81004620500c4410300641190000c02400308110311140e165403080c40003030032408440010444820402005000c1c2030311038150148041015011610700340c000c0c52050700075803c40c209010075a2018072400c0d61081003240c1c560b101034a0244094203554010b000a03024022 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 909691124 1250 909689874 909689929
    0xd120906050309152d010306050c2d0c0a050c0f061207030f02090d0b040c140a03030513170f060a0e03071403160b04050c2202090a0e0c13080c 63
    0x2d0780311071503050a240c0c800403071400314a0814101d170310403c1c4811a243c0b0318100c0010b45804992056824610b43c0d050124000f90440300594490100d192580b1400070f001c00149038141810040c0d89a00d07171041c0c0c007821640d24131800704207030010455456405654100810a00410920181c80c4d016900c1e04000601e0010503080f580280a4a400350360020a03000c0082c09100081c1c02c07a612851052001c01009034407070418942c3c00101c14582c9030403005000b414400a8015005030203505000c2061030304a640d15111500c18070b540160f48603a58100860103074820780c003400240e6000700c0c901c50620411158041d8550303a0b02c502c2002820103489100c1c0c0c403003410340a004903182980e181c0c1070080d0304040c82c01c04050518055504644902c41d076040b441c01800c100c800c803500c0302d6a140c40080341424140381c0e203029500091200d0b600c02c07000c0401240003950704c6451805000d09640c160f4a4400351907003030340a04001d0308220450303813014245038150354803041c2407520041e0b0102106050382 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 909692374 1250 909691124 909691141
    0x6270b10090603150f17100b0603063d0e010e03060106140c060f011509050102060a180b090303090c0d0b01050111120a0c060b042307020c0d12090605030915 69
    0x3e80360031000149100d10717000501299011850800e20012a0558001d010000d214404441010b00415081881800014444c1c500880c40741640349a05018401a03007070301101180d4140024801a0401c0e8003000140d500b43c0e0081019491352000c0c2020f00b03405c5a5400000d9650f8014802c1c2c0041080303980200302100070950660741c0c0c1c0e64042d002c40300c80d41001500c00c2d80701807090140c0512004221440012944902c200c0e01c21030704107801510450701c0d003034001030141c10004588042d03020044a1107001684050000d03115450002c09592a8101035002d01e003400c3d000c42880d445600300d0094030010600d88a2410304540b42420000c01d4586040941824610552500782d01000d021070f156202c1600b10314800101441810b007000700c9241c00b8204001c8824903c0342c418060881c04580b00301d0310a207035005030800c4103401219041409600010b108007074041d0102d8003801a0080c0c1c1c2c9125807c040c9102c05454641413143c118500403001c0769550940a0110380010141000301c0d0800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 909693624 1250 909692374 909692411
    0x11101112a0c150702060c0f120708092115040b0901060305071e030c030b04050d0302030114041e020f120a0e0a150b10020f15011a0d06270b10090603 66
    0x15030b011b071045450304170b031a40250f00d41c10480040441401040315114820308540c04070340d852540b10307a2450408201c1007d1285602c0329400380d0005a030740703c4401d142c849040000020740c1e401d02040510515062620401941000d008806541e0610390b0a200040001c504c000613104000c0d000300001e40c009105811034810b40e807000c0c20070700d901200232040c800b008002d01d1245004604880d121003003200e08600700c0c4400d104010070004a0200d01c8421300e402d8200c034000003c10b1450101145442c0000c41c200c1e40b1100124840500000c1d001c2c640303000003246190f02004000007044013081001d00107840380c6d460f0000a107045541d02c404010030b403003079001440e802c2d00503000c564007088401c0003035078503000f0004a0325988150f4048108207003410125505984400341d4108200303420300c42541c40c40d005491100031103902c88070042158100c0e03948410148082200058006015900a408a43c3c1d208200d5000303002d100080303801c0329000b807030704011104507240018940040d42260b0301c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 909694874 1250 909693624 909693637
    0x100914060405180708060d020d110307080607030c030b040207030e0d080c0601060e01020f06040302121c02070804180204030206120c1b1608150403030b011101112a0c15 74
    0x30110584241071008080c400d075215120503264045162076440c1000380303615020400a5215910800e12701c0082c0c01c50b14440c60050300602211019501c5041c90303404d00c41c04035003410000c0e0381c860f01510003561602400965210655085181c202d050314010f20145210300d4060044d00784100c54001c200b505401c85002d2036840c03007603c5195844200040503002a0301d00c00b8014031814284411034a0040789847c0203984c035070001c120b05581b90610490a41000080c1c03600e02c079007101d150202000500040418602c6a010075a0b00c9003010b4200304110750303403424155494030521060005884040496401c040c1c041c0548405030383c2c0d402c3c8884248034400690b00a0741100c1c3c20707146014400500100d4141c0d060079058440394403070050310747d00d0310000040211000c4420106c5d000c03030700a501880c022481894400f102e500080c030110b081d00e000703e101d8203100000040e8202003110807407458200304c07000c0c1c0107820581608441640c0e111402e044552090071501e800d48107100034801102d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 909696124 1250 909694874 909694879
    0xf0414030d0903090510091e030209090a05070e010e0c16082106040209010e060c01090b071107050d02030c1509040e010f0501090b0307121509110f100914060405 71
    0x181c07102854584030103441c0d04282280800c2850f8400b04842c902203e118441210035130707401510fa0324207072441868440006044201c0c80c40850040b0258651550040c031a00f0b04200500128003030303103401d0349419610b610010200c04220700601000003031407230640d0018092511a91100c00601841203101c3c40407100809419001414004840d100b5401c603101c00d000c5002c1c0b5119a8a0b8018042640300310009640011864413168100789403010140c0300b100c41c41800040c2c0c0d00c61715903600e80d05070020365011000c180034071304100781580200203000140809550550002c4165404640e4038003040000500c030305580070842050382102c40994903102c0008000340007500556041a00920715070140340407803800c1030004503408805001d080c0030002c002d0001c0403514500f54990711904071ba403e0444801070681c00300c400c100200c0c025505441d0062545400d0107a02c041040003035078000c0100c3c0d001d94001e04000c0c21168001c000c1b0400c036440c0c1d0380c0c00c020703c0840307100040840c401c5800a42c9d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 909697374 1250 909696124 909696127
    0xc03070206010e072d120c020c0402030a060b071a010504090c03060e0f03041202011112030c0f0d090c090c0804030906050c19050c03160b040312020a02030f010c0210140f041403 78
    0x8103500040d40c1d90545440171500c8014550101106440998030031111000c00340c1d028600508290400b54020341e440341c8a90000580c5985888440815512a01050b07d50403803000d80c1003480c035240c103051801428101c404105070300c4540c3c1c0300414145513120142a141c1d840081c2c02d5600307c1030020003d01081802070f60742e5503454042c940d00f000569a820381c00a208070040b101000000541c0301800300381d0b4090f00b820b685d244920741c0c4141c0e0000b0050007403e502441510b0400d01c080c01807480d0f46205100001c0d049007810f284800b210b65030000d007420070840105100100c2e4002348003009036112460095501d0100320300841c50a034600309100501103900114100340302010403a240541c004806482d40402a5100388446202500800050b10810042000040c209154002406525006460200c4e0321500040d04061541d0a9054941d4595209040381d0f40d0510800c449802002410041c10300101c00001007074400400c202ca84240e1800490140101248401c000c0358003202143d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 909698624 1250 909697374 909697427
    0x80907050d0305180d0c171f1122090509060f06060c0106270e16050103020904061211030f0d0813030c1b06080105220f0b04060f0e0c03070206010e07 66
    0x2c01b04a8a10803504070502c2501c0740c0c41e14900202d0a0120840c1d0b90015040248981562400034211140d034003900710350400980890800b941880c031803240e041f5a091079140d241443c054155a8024098901c50300103004200c0f03850037041802c1c2c1c000340c0a0f6891500d03490705495090045c01c03903420280d601c0041c6110b1110480868a0501441c0b10b0041c00380311000340c4208556446a4a64240b0494903141d50b042c001944242d010b05441c110041000ca1488d60360b11540c01002d040351410b4800c07860400c4c552181c3e08040119203207070030440000380441c4060610040c102040504000e01c030015261210342490710916161840d41c3d004225a14030341114040c04180c001d403031040c403020441ca0350000600d46000c6003603045100c41903050440c0315041c04660002400310344000d8680035034489016800da00c030381c884c14014103000000016000d041001808920b10020095004001c1c10410410341960120310281100c4a00381c10b81d20b1911351002c01d94103159a10282c01a6481d0030020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 909699874 1250 909698624 909698633
    0x80a110f0706060f0e16230c160518040c151701050a030b0f06210d080a0506030705100c021305010e06090103031b020102031204050607080907050d0305180d 69
    0x1c040561042d00c04015544d59400303486a908094800d06900010040c009030b0310000003000250603585a140c045040e000c40950a5281c090b150815024550f0114210328200420000d80980c1582607003403520741c40c549800200c00f09880184200e891302f005011804110051590340068084040c8050030b40e00003c80052500100300c040c000110030300c000020709030030100780030829681c202e568500d66580300c0001c4c49001d036000e0b040360341003001008a813505440d20140350240f05000d00c0a0502101d884100505c481005060078129614080c01c0c800d0a60f00011488110340c2d003650444200b42c42c1800942c0c0880c88603901a4004d500d03800e4500c00040036034081070688800b41265075264803800140064040c09001c0180410010f203812071005c03a541c21100075251051040764605004a0a0307070143d424265011501030340000c050040598020070325590110080d80105079080c03808000644660309010040c06020000466400b00c0c20a9241410b10030009440e22030500043d181 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 909701124 1250 909699874 909699877
    0xf0d0f02060f031f12060c0c172d16022103040f121a09030d060807211110030204090207030c200307181e05160806060a080a110f 57
    0xc091000b041620712000140c3e01c60080030058551104030210306400c940e03a014010b0440394010000d01048d0010b40c000500326504505e60000c404400684502c240350415580d90912104901800e0000c0e0b8100e0381e82c600c07030003550303c9500103160701001595a40042650320045c801034441c11f144e00d8141180450000006004682e03281c0b03101a00695250850200b61054090003440140c03000740e0041e04108102c0000d800c914040252480c000250f26068122242a4010030b441e03080401c0c2048958038544000c07441c4400000e400c94120100e548895240018a44c05441003a200401da1304480c400c1d810340d0050441c80c0700c11907a40b141400c001c0c2025568000440700781c105e086000d41d4035038270f0b03d81d0707107d41c8074010303004108542c1050f01861740010005082c006403682c41003200d00718082061505203000d0780140c005018100000841256100350b040c49003031013203240070300c40d0300d848405c110740302170f242890002459151031407544040e04118401c028000404550180441040d60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 909702374 1250 909701124 909701131
    0x201290409170d0c091208070f02040f020c0a050606060a021c090f0e15060f0f07061407080106090801050403050a121506030b09160c0f05150408030105010305150f0d0f02060f03 78
    0x101d5208101d9591740e01c000d001b0b081c0b0140245481d100348800c100280042da03c6294040c401000402e0904101c1684c1003280c00c048000045070303104085142c2441014001c0301e4012209445061400095a501075039a810800c0081c20744203d4490403819144101d801a02401e20290003c0c1c83c29600c0d1400c403030300740e0706483c106014040d41e400b1111525000c0d0442c0d05800101c4012420444204691401a001254150b40031901e80206a0811040d0440b451003180280c5402ca4554144000106100c1041d00304242d2030707140505004c0400e8006042d10002a514540407202500008103c00500b208403e1103000d12514000420000d405420400010b1016141010156603994007070740c10301400c0b051b00b0045507280c2c82e8000030500b018414802c05015000321802096000c100c41d01d40502203805991581c0040010300841d0f0b8140941a0082001030b001440b40301e04170b00180b140761002491501c1440d0f0b44000074100040c0d40b03c501d100e1500100750036280d0808410410b139560088 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 909703624 1250 909702374 909702377
    0xf030b0904121704120f0c060e06430e030109030206010924050d0f050312070f0c0b151206010b090418030210111c0c0201290409170d0c 60
    0x1041141520340f600500c9101d150018015101002424010f480007071010002d081080343c0c000805000c0b0f0301a00804410a030a0750003070503240340c285c003091001704101c040a541032010401130300303902400040211180e1b95640304030284481d248401c0e0b800302d880c100015055401c01113003205050300400c1d150f04036003d4200c00c0c444c0d00c07050b000920852580700038031886841c070008144094100102e1100b92a8071801030034041e185c40c1d0b03c070207245800c044480038039990710340c3c20000c0c101d521a540b03901c4503c480c100100e440d000c03680c1e014a40d01009084894141c001000c1440b585d40d40c0804003010359001041c0c803000e50311031040e085664080f05125028905080e1030300f1740c6000300044800d9080c1c00d5405010205449074810000d81b510500c000100c84003881140100a0850b405070300389003000380c000810f03500c050006030070341d03000400341d098480c12486a00c041d48c01c4400d07803611170341c0200c0d0f001807614070740d1600c0d2406c0000310307030b001c8403414001c210f4422028040e40000880d04c0c0d603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 909704874 1250 909703624 909703637
    0x2010e0901031a370e07050d060f060b07080a0e062a10060602070e0903070507091119030c030e030910050c10060b0a0215130201030b030a050d120f050f070f030b090412 74
    0x102800550310000c1f441000c1c1c000719a5241e000110f0042c0e482524503000800e0007050f01136480382c440e000c5410080082e0780b482c500042602ca41a08400e01d00c2c81741c01c1c2664454200102d42201030066401c07426080a180d8800a080004000a0020111150081508000154440c00300940e1010a40202420040f82c0000310311000000000c0d00c5c01c05500100422141c0e0030400000058039008145241004043c4105010b400e9107441843d10040c850780c0000f00b25a100800500760740c1e0704411980141c104008517103003916102c0100c0094881800d150360784096241401c4d06d01032035446000301c014688840480c8210140004000c0e51410782c2c21540552111034403011036103401c2c0d880b54001f010f020710400c0154084c0e004103400300d100a0907503c42e0b800f552034140c104240300020700300050401c070050b100840144288074010f020303894100102e160034540c6243c07400c13024200401b80701030103001c10940d0f80319030013000c003001e00a000f81c1c000c0d0a151400c9141c6490854200010480e03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 909706124 1250 909704874 909704891
    0x1603020a02070e1006112b120f1406191406070b090a030f0203040e01030b180d0e0310091124040b030703060905100302120309091302010e0901031a37 66
    0x20000ba0700003660801c402c0000d000740a0080780094a007040c8204e405008400c235110340400c115104a6908030914040480e0390860100800d0901c0d200628a9101c0e40b401140d1022503040d001415080c1c586c0106541c0813219020001201e074040c10034014030340d205500c104040b007400840c1c0c141c1d0b9a0b200351160212081c8a50741079803a401540103410039503040100400200303c05d81c12082d08074040c01101405021100e80076400e0068080210300894a5400e100115007820480111080d1043c1420401604142c0e11980c83d0b010804660348144010300c03e0340c1c1075520003810012a05080c0309101d07600c0341d89800003a10398004a4403c0d0100745045800038200d152801045d2059411040001007039046a017001501800100e0450451105008030f09080d228003180324051540522040f80c0c404075440010030b2028110341d21400380011a0040002503000c00084265600410448840e07680e009000a5030700c1040c1d00304511104091401e801095192522000780c200001d0248030554 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 909707374 1250 909706124 909706157
    0x60d2a05070b06090705160c051c051c021c12050f0402010203120c04120804051306060801121104060e040b060f010c0b0411190612051603020a02070e1006 68
    0x9107510250403800c80340d0010382e85251540181d030b44505a81805420030b80440e03101c412841c0d0406040310200d5281106005510f004e040da0140101610455080c207c51507803596254030030700c1c03091840b00c503e448020402030300911a0640c62390801c12180704c01550100c000740511030140302500c180d460140031500c161811000c55203c2c54040c0c00039803420082000f151003100000b0110800d0b1402444082024404405000f00c080c0c01050072a07207130750914080044882d06a041c0d001a80e280c01010001a50071007403041c11548042c8106c11b0700324850500c030b48081c0d442a03140da40145851004035124003000840c40c00b075400340c00c10010942c0c504c000d100c0c00040c02080b0b14049651000352100180100c1c0c06903a00c54812144502142c0b0000b000c2041ca51100900422000c040b000501940340c2c84100c003602450070200600560270202440d40301c01c400c1d000303c0700405400240044416000304055030050500284445091030020f80400041c0c11600403039000561030001c205020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 909708624 1250 909707374 909707377
    0x70e090d0804081e0a0504090f090f120309150603120903050304140f03060928030c080304050c13060501090504021e0a120516090e0f040b06060d2a05 66
    0x40c011912803aa0325201e41d160303c40582c0004164985031520180c04461059003034010b0701466140792641c03600d0b6402c002104050340c0e0804108055545401c840c1400310f43c841d001002001c1d00700004840a00c10b1035811006071088407809090f0500302100c4014000d1240e114008482c019252041c0c40042008112800d101c01e00c0080d00c03030780c02840f05200300450025960b103000401440015174035800c0001c42d0900070112000120340d0400d040451281c44001d9030300d500d0002c0e00910304010803042c0d401a2075000d95500240c807442005c0001010060104013800c00500020511207550711064076040c0901018096180020807020300010142428002c3d50f144405140c880f9403128015000041c10750025104101003040d204040103501819210311401003020804602c11051a0705018040044c41d5105203c0d10400300108121021000c40c126040b5500c24000040e07911424000b404a024006000345902d1802418820b03183c0c0d4a900003a40c440040c20042c4071320905003050f90503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 909709874 1250 909708624 909708643
    0x2b1205040c06030209010201021c14010f0b032815030507090e0307170909071806050f1909080d0c110303031006050a0909050a05040507091b110c090702070e09 70
    0x10034041410b208107030294001d01084a0b040c03000605140c03103800440c108000380180d5070700c45581c0d2021181c01c04d00302900c1ea03000d0404603842404c07607440c00e012540c2c180310003022314042c0c0d561001803041c10200440748020b5207081038014000c0c16400a4226207031001480300302e43e54811100300041c03c507482e008291490340f9200146041041e66100d800e00360110041103c50420208100d0b10180d031a070344800d02940341591521070001d845042450990072a40018003805003d0040d0380e00144d20f507049a48110a079031725105038008000c4203640340d480b2500401268002c2180042e8001e41c0007903140b40703050165a18036403560012040c1903c0e44000d0351900107100a000040c02180e000d40010300001c2c8140c5800d040c11a6a100c0c0881140d4054820030150380c3c035034040c0b101740b15081015a0240c14000310403c4050f003244160f41d004030418200400380410720102c42d4566406108085050340e0190880c3c4e000d207041d0341c00a4441005004584e110500240440d944103030000d0007411 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 909711124 1250 909709874 909709883
    0x150102010c0c03080a0e011509061202130b0d08030c121305030406051e040902091216090b04091707030906020616050c0a0c030b15012f2b120504 64
    0x5520502c3e14112011600180708800c0c05407912000d030b060300382c244034000c0310703050b00c0d05442c0c0070a01b400301030b1003a1203050b80840c4840410300d0124000d0b0751029103100c6050190200005c0132050503021680020a41a001e068080080b040003800d001e00c00041031031448100001000395a6140d0855856100d4400504103600074081800514012402004034500c02c80059154450304440314016078029000082c80070b40114408500d800c201e041c1103200c0886030017503c0c0400f400360400381d806034144104081c250312103100d4041c649032644851041c41d0040110440c030458040c6100e09584890402c9000a0341824001006407010a80a01601d1008040000090807040484058002e6444c590f0703940520082c140004449600703110003035108080139092464160f02184210340b8818450f818005030b150100c00303410900081d48842400d08220382c000e548418880c514043c0e5641c2d4128010055403100f040c1d40411003000900c900c3d42c1d6941070605820a0b80b01c2c001e88100342c50050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 909712230 1106 909711124 909711137
    0x30c030b07110a02010f0516380720030a08090f01060b12090a0219080c15161b030b060901050f180604020d090605150102010c 56
    0x368481c420b4100084259801004242c5519101e14000e0401003c2100c40440501132000d44803140e51405200c0c099000e1464101d55100d548000b03000e031445054281806107400b002541000031610800010680340d168068402c003540c006000f620300c10480c480318680ba002c201400410003035907200005e43c10b0140300e060601c0c0c0b802580c10320507414001c045c0061402d82c000c0b0781c401c00e00144c016981e03540e80c40c141424010500f4009610500080f00c501c1c1c981a224900425102c1c00020350f98241c110307034208204042006603c06200d401488085a400060303849402190701440c03175074109000c80506034072800e07c0d0340c06c1246da20420070107008003400c10700b05050160205894402240901a0000b0000204000401102c030b6001c0c000419503100c0340c05403841007480c40000d012511444c41c10710003400c002c4444078201079801110010541c030502950311030400549403407 = true := by decide +kernel

theorem cover : BRFrame.Cov 909532374 909712230 := by
  have h0 := BRFrame.cov_init 909532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 909532374 ≤ n) (h2 : n < 909712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
