-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1257
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:02:04.836713+00:00
-- url     : https://prove2.me/submissions/5fb09608-3f74-4295-8c16-ccc93e26b6a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 225899280 ≤ n < 226079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 225900530 1250 225899280 225899321
    0xc160503150f0718120f150509070506180604060f0201060e060d12031e020705120910120608013e0307030e0f0f01050f0a060f060804080922 62
    0x322441c607030000b0341c00350f501e161204201c600e0440006507031605900141800700c42d00200b8040c482c944000c038101c0d0340100040c680140c110796004044540440e1824044d0300300c0c00041c00b561510300001c298051130b01e00701c2c603580d41d0700f040002c010b984147c0c040d0300468030041d07030720414a070280074000c0141102c0060909510309072003c030b103026003139040080000c2d030900c400d0500319009602020110004090b00d00d0700905050081d80254040502034517503126030340c004400310b0040c1c0cbc11226040005802c0041d0ba41c0000d03001e40381103100700070703600c509a2030700b4001c5107628091081745020310303404a100c0c0a1405031a1280c4100000c10f8102d845c141010746044503200c4400100c83d00300c481ca1400203410a000c110260030102041810001401224000c0c0d331000815040580600303100392040485803a01c0c92010110352461084407115680d80d0010061f4502078000c02c1e60103401203c41502e80b110490024013003407400e084510509a0511180030402c51510854442c554805004080f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 225901780 1250 225900530 225900541
    0x132a0509030316060906060b04080c0402090310090c0b030c040f06110a080c03071704060f0c03080103170403081c050a021206090a02090306040c0905060103140403140c16050315 78
    0x840b8030550fa00c0ba03045482d2440c580c1d08010301548140040c2da0031840400c100707134840c100d100082c1d10070302c2901d01c00d10510003081094a442e20032941c070100024020085030b1040030203e001341402c00030903a041c4450780000901e5001c03250045218100308503000fa91241030503480000b008041e0003030340c00c01014005c590620070300081c82c4000c0030b402440c425242d2840091041ca14401c103100288614040c24184081d072032000007030419240c10b5200d0303040010000508568000c1c2d1401d01400103001000100007140c0d05e12034048030f82840c00d90240ca803d03180e446000082c0e0244552034010b06a04100d200e02c40b0061240355080180c010007035250840e1060708082014025007014071640c035580118088103035582c102c0e0703100103004c0c007610101c5c6050300f0b02403100d0002e4400ca003821810107000418540c420f1051084202130026036066a40702ca41f02224040c4800e2001e031a240002c10440614075020020415500b03440d0802000c40c40c140028141481c520101e40c110f43d0303200105005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 225903030 1250 225901780 225901783
    0x40204050717130606150c0c0605092209060516020607021903031e06030302060a0b0402070803010621050a150906060512100306020301090504060e06060303030a0902132a050903 78
    0x40d00b1058003c482c8414100d1810310313034010030b110340c040d000765159446601c4d080c0d504000e03402042c1c2e020348041d4001541d07035803041c2da10340301c4c4400e041c0d8415050500d41c10f42001030f220040c000d040c8940000307032400150740d40300100ca0040d05c240320441c18842441d00501d0741000030547c06216803002d03000c003441b00d40c030110b02d60021000080500d07844041c40054451010000340d40740590940c28003120b43c0d6420041d44410041c0c964410080c20403080040900b42402216509503020601d24510307071a0980450f0002180c116181d00f2000d4590a040801c00318001c85000b48080d00000401d9180610500b07c403100550000d43c080b8141101007110302d40142c15941d43c48050410041c6640d51406a144801c245800003840d4610210001c10340b035205602051046200703400802031a480d02c030981d03a84040849159a041c0c0c81040003034081038503908001156031001d007014005500028004061740c0c0b007200c42282e8001002440d0300c100300c541c0d100400002c0107061030b524010078540842e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 225904280 1250 225903030 225903077
    0x115032006181503010f0305070806100b0d150e010f1205031207120e0d0e180106030b0f06031501020c1c0206070f1e020a05030102040815091c02060402040507 70
    0x341d411102c0000c008015200c6030400d50501039125140d540e207603120584100450101e002c00c0c1c03040d00c128031010035038000001d81203000745100d00407d001c0614001a00e01140c0c0000004444c00d80c0f150103151424000c1c5140c000a00091a9000744a44c108843c2501e242d903140c0c410042c400c000d0702150301240c0b012040701c0d440340c507400c1581c029540c0c02c2020b603801c0d10441200c107103e9191800500c0ca0b1000880c902044c060691b50f1030305505e11890030064071103a018003200c1c81c0c0e40404010440c15000340c0c4400c480050107040c00c1d4044d100380300007030312580003118800d48907940700310021000c1d0307030502081c40b00321000c9601214001010038032030781102c15060002d0260500203502c10a020b0074104058440d03621000c200e07518081d84010144a0300c0062049002e0901001d0100c0c182c60107001355015190160700418200300a940745001d00907000d81803034194001c1e00c03051090060070055190b400300361a001440717641010300c18841103480041440c0c0c2086640001035102d1440420780 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 225905530 1250 225904280 225904297
    0x50a0c0f02150103201c0c0b030403020607030f0e010e03030a2d202205031c05180603071d0d02010c0f03020f16031716140705030115032006 62
    0x40c3c010070070384121200c109291403510785500c003260404c403071420301511042c1b0311241e2040000d207110941d500025411030009481c01800f5800110006050340d01c03030381c4040c4855015550224030b00d182015610300311005000b1941258100008200f00046240640342d0405186c0403405840d01ba01c0b00c0200007403a0709000c19a049898224140d07680200140306034907141112440d540c1c0d000b5110b0f00c0c45509511458200c0402007040b000a01460040f42c5c0c04407204031541c03a03800d909101c0340220307201e80c040755012002144c1082b090820342c442401851055030755803185003007181c0808150380d100700503102d00b80c483e00300d60381007800503680000cae504c82e419800180402e40010602e0140d00304115554101068411a00810324450130503006104684c0500042008104291140440361040362601a10035810342101400581c4280103030703d21455810a440d00148c48400003400c0d076598140c00f40c1261120386040c01408000c0c0501203002001820318040d85901101103003850090428 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 225906780 1250 225905530 225905543
    0x80708070503091801030302011a1e0604120b0106120e0a03050a17040506160e0f311e0e0607051305030f1509150f0403090504050a0c0f02150103 64
    0x250341041050410a0741d01c8400002d0814454024407201041030714002d11054005600307022072504545581c0030b4088410318043d00c514a15850300784114a4800c201c088160052810080001c1d40c194020341c80e0000c13440380b66510304951404600411000402401180709460004030f201e841c100014040c0e05580c0c14140f854603241d6006007a2001012071004c0007040710154200710401c800841c40c1440390000f5891814000d083d084200c800a0001c3c410503081400408a071455180801c1e03444591381c0d404516101d2660300c151b0100e0f8030351a40603641c0c1d0706070b00c49500c072400e00341e106652140390110306010000c0d0081c1109a50703440d003015000b4414404000340b4101c504102e80409000340001800301e401c03044140c0c003034546c5d0f00c81450b14a03842a90300d001094000202140740f03060f220203110345580c1c076104d580012a0111001e00200c003407006031200013959480d039000e00392061480d040000380441c0d0640c005003139400c0c1c0d209400b0454020840c40c6203000f00844019055a0700a034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 225908030 1250 225906780 225906787
    0x306111314040207050a050d02241b090a08010509060c1c150506070309031103190b1f0b0706060b0c07030609150501030f11040902090c030a0912030e01110304080708 73
    0x100b0020710030030001a002d4000c42505600b4400c00150070f00c030018007542121100564061030b10f20f5440110344d12a00460305d440420a20211410304505070407000c2d00007840c114120000841c1100c44c1c1e40710403156512403003013101c020400d11101d64408200c1032118a000f007180406c01a0031900405c000307440fa03170355100300c80d00d0600001c0c10300034100281c000760b940c00d01418050941003552100b03c8131001c0b40c1401140b41e050200790400c081c4c10046448d0660000d03a9a02d10403081c0c01402e00e03080d0300c08000d44500c20a4070060f94030080003410b00c925907540040c01c0080c00e591060f0001135002204203c1c0351040200010f0034000c0380c0d001000040c01700c880d81340c07502035100c0b04510420013504240002c410300240741ea410704039600c11404000030a507100300380700903590040406588400c0c9000000d181140210055a01ca2450f12001840040550310840750001244421001075661a203401c500b0b902480307614030441c1c420746050b0540c5055681e000242c860203600410788003020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 225909280 1250 225908030 225908069
    0x9041b150e120a0b090c120f03070b0c0d060e0a0b0d0203070501050c01060801021b07090b090c03060d020d0501021305040605151b010c031a0105090a0905060d060f050103061113 78
    0x6002c1d0102c003644c41034404415060100c1c20303c1da180025401da600c14520219a54660703200020300b401c8528500002c0c60400312241c864800c0100020004011404200030303000700f00740c0300d1090b1006060548489a041d0070503040c1c0c1801c480341058028040c440c00030584016a034005a4441250824a0460759030326130601554098038070783d400b040041d800454502c041d148400e4020323500c02d600070100c941c0c2d959106080c000307940708915001c0d003101070200491200c015020045074050030140c03030b802240100790301080d40c821101d441594280d42c08541c5140004030038440c4030060004807010f0004609050001d01c404034902c3d405c1d02400000680c0c0520b00403442a800f00c4208654000c00094007010b601601820000710600c400f0825100003201940c0104182d07040c0100c007074249038000381846001002858040e19242d03001c10354161540019040340a88051501e00c060046055403551503c1000d030b844007162024150400d1001a100209208002e412111b6400700001040307400b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 225910530 1250 225909280 225909283
    0xf0112110f190801050402090f0c19110f0c040b04090203030405090a14011401200307020f060d0f091e080a0e0411030403030219030501050607020402030a0b09041b150e12 75
    0xc4685120b40c1081010005040b800652200c0c0c0720714001d941f103522903a00d5408035800644110f406242c0c2a0081c4009140307111000e05001d42d0607407a05207041c1500201311002d1410640400c1740c1d481d540110b21840c2c060030180070301440504155000d001d480e20a034000b80e201d00960041902038a02c090000710510150741240300142000f002103016545c4401d484020801c0c1103c101d400300c0c11701c5000c0507050707a0001c0d21240c14900c0c680a541440140d900304810046c0c1c40c10603e038070034010700c03a2203d030720700d5486003400310644184006444d8801d440d01948040e1200d4601c0d110429040d04080881e25610031100c0d01c9080785440311b035440440000400034814031001c0c9a0080011082204160b01742d80141524a04101c00308218aa481c10860990b0b00034091707036411101c02d0001c00d0050909401541d04081a1130000c40c8001c0401d0105100c210111000d82e0205e14096002000140b02039058000e0083c40c403204a040d0550380c8060500700c0540c284a015003084008081d05240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 225911780 1250 225910530 225910549
    0x1c0c0e040f14090312090715050a02070f080304080f030316050705070e01060f11010c120e0c0d0c05090c041215140702010b030d0915031e140f0112110f 67
    0x64403402d01d2540c20202000c544e2070b0002003a130030300c12031180041049040d000801d10101c41c0c3c1c03001c0c120070000c0c0449086840740c0003641400258440c07140d022540c0c494030000b0401a0440f240110f0b144d45c6001c2c0d101d4034048007031802101daa003080090080c140d100c02c00107045038500c1d050207641e44142c0d140a0340341c40d8107540061a4041c6060000c510298000450a420701841c3d40f2416006a10002c8074200c07882e074082c0710046048003c98043d84c8007542c004004000002d02660394204105012840d0b40000300022502c004a00405010601d050001182c00c03030039a141c2c0702d0415042035030350300c911f4180d400050b00700d01d100300200d84000e841d9000608500c500c030310700b00d00e02d00309890041d020f0b1819003d041d10034024a0802c5c00e00da44168a900125400300100c01d910000600094008000304d50380ca4044c1c0c4d50144d080c0310001c05900a100d1003c500b00b948060034942420a40d0300c0301c0040c0c03c021012001e20340d01700d0200d13005000c0100100c00c00c46403110010175a00010341c5410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 225913030 1250 225911780 225911801
    0x100e0405030f0f07060f02041706061e0310060e040302070602030412081602180406110f190201180804030c0e0403051206060409060f0f091415010918021c0c0e040f 72
    0xf0705000e42c0b04191b1455801400c00c8911020540c181c8202d403094064803548129401d0380c002103564850000700c05124200c0b4240600070b000e440440c5a80f4001d0010b990080d00004040c102d41014031042650401c00e50008200707c0c8007660820b818402c1402c0011005c0c000689440000304446604180303031034003400038550040015809054081c008074940b41c003144c064500760b10703080202d04128001000c4070444011648214500840551030740400b26459114208566a604e030420f030f0740c10065810031980340152800c0340c89516519002611020036046135440307903030034424000001e40080030780300cfc66007100c10600c0d401d5840002084445c010b40c0e2005544034108680001d61f880e0030300541d03050750289492520895101d41c402c900703540c8000305148402c0400341c005020a600c8440c20b4690003014506003071015600d07800c4003807901c1d55824200d030640d40011403400480311100d0300001c6600c1030000303000511b20808090404880400c01e14055601d031508426240c060b80c0c044010300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 225914280 1250 225913030 225913043
    0x1030b070c080d020412060605040203010f05060d060f17010507020106060e010815100f03110403080403080f07080f04140a150e0a0b07030f0f0c020312160606030b100e0405030f0f07 80
    0x6540c2c0d150440e038058800a000d841076403408d400030900781000c0c000c40f810f03030341e4051036400110720701000d01c90554800d40907038120603a5180c01103252100704080340010084049400640c6030f030350008608481c4060310120135a89007040403c6810b4001500408082003401e0851107a503880c01c0c0700005040b080510360b40200081d0001042a4201c02c80c403903580020754080000a080f071880c1c0010340f007203010140a41406000803c001030120006048418924500c2410907085a6032042c0300d42010f24425036011002ca0300b4055200c11002403840c26800701da00001d101c2c07a201030f001c00d000f5051302c40c0301000030760411342d20141c4030b49010790004e0032024080b5030b5030101800e00900300c1c0b20354034403813000500c120301045a01c0c0c0700b1a1188000b6400a0142c08881c854041010351540b1880015400492840b90700020a60a00c500d0340118080c916043c4980360503611009031a04503000074810348280c0080c071001c2003002042d10041200d11145c41e59540b021290740721940500000140803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 225915530 1250 225914280 225914287
    0x90b0702030c101104051507050d1211071a0a090b090115050108100603090c05130f05070c0506130203030403170a030f11091302091e09070801030b070c080d02 70
    0x4440e800002408410b001e8400c0e900503941e4000541e054403114424440b90400034041400300d40ba0140700003c00d101504052803804c0d032030b0703034845003000b080c02c20003c0410303c041003180f00b0b4441c0f4081d4100d14080b440c1c00c5842c1003042d588030f405100c5101031408a2041e000000354844550358040c401c41608100580494542203009502030440900e84407001d440f001d400003000d5010f0700c850b6010300c105414014501d810400100c005020212060b0ba114480c9000050300f500d03048410841c0021548000c00c1c2c0b105c8070440303032080e40c01c040c0003c0100440c0c8420103000c44da0108402c1d42041100395081c18510040c00002e14602039a0006449a0702220900b1f541c042e0603402424926503e84092000320307401b01840017181c96581100c641514204000300061600849020603910b140744018280b0050307201083d4400128000c40d41d14078801900440f05141a681013a400001d902e03108100b0740c1560b4450204100c0a05681c06000c0e10592850410000005403100d4801c08be130304548 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 225916780 1250 225915530 225915541
    0x40504110c0d170406020307020304050907020c01022a060d0b09190501060203030609010306020a2c2e081302030313060e030708030a0f1814090a0612060c03090b 71
    0x2031507009081406480c8207850841c0c242d40d0080c02c03410580342d00045090100c0d502da0310f41c2c4004e9031000b0300f0001140010080422a5030f54452814015801a0700404c04590148006450001c0e01407460348c61080c100ca1400107900401d1070440c0c075000559020b40c0f10010f00100314068800102c059502540d800c08020000c40190703a5015078616801c02401140d81c0c030a810780c0c9910064418a4020124000501c0440e42c0394004210010b2285130440e40e0740346220350b10248105400880306040016041d42c001403600d003040c00e15140f42c0701810312081c4101040804d48601d005804000e105840300010008030314100c9000f10145c014060360743d500080ba602d1949651030740580004582c0d4154004542d00300040c0e00d400341e030326500c019441d14252800903182d1480c0c00b01e440741008400c4201041d0040d0710000e507001010910342005642e03001c40100918410000c1c1100c10440c58103a0030040d0740d40c10713600381c0f04544e000380c800240101e445c241240585070200018010384c2c484001c0c881d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 225918030 1250 225916780 225916811
    0x90203040b0402150301030b060103180b04051b03120d09050a08040909060c050c0a33050601080606160206280e030d052703010e070f0807060c020123040504 69
    0x20b00c940c0c401c4a101c4612070041010000c00d010a010280001c050b1f0400516654029070051520190070b61f904129030031142d030b40396001c1c0c0c41142d04407095001040030081c9a170410042c006003101c21000303003e40003064220080b10f030042c5181c002c481621042e500c400d00c80700340400a4120b8122101c10354880e2a030310710001900003000c04540359072a040134103038810301c80c0003034070724045203a4080c0000c1416a10344560342c262610300b820812882081e0718036000328500c0001c0d88401404800300d65441d140001600b4040018840d41c0508820018030403030006140501503c258106c0744a0344a1740c251901c80303184001d8640310303c8401c00d1000c2e038510700e541000411442e698202c0485881c0d64001d00112142c0c01080e04010704042c014885211103c0c2c601c0204400130800380c0002100e40700440038a1807c881540048202942c0d50018046404140400c03806459642000d0246030307050fa0008100241c0074001002c07100f000c8246005141c1c041007100c00030f1000400a020101041c0c5415 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 225919280 1250 225918030 225918053
    0xc04110405120a020a0b040b0d1a10020a1a070c030311090d05010207020301060501051908041103061303090e0106080a0203040c030b01151119021002030403020a0f03140705130b010909020304 84
    0x40c0d204d17203081500006c1594180084606491400b4521070603c0015041c41011f050000402e0585c107440b55800c01c0f482c2c44103140c0b000c00c00140d034005c2c0003284890909100720f0280006290032440844200074a003034000043d410601e41c9490002080078004038403103034502980346039507030200c0908210400e00038150064507895000300d000b045510b60710001912507204000200704030810100c52100f0041c06411000d50182c05000200d00d80031101d4000307803c02d5800c4619003039142c4d54801203c1816400900d98001d0041500314014075410300361b010f0500c00e002030500c2a029000000a41008000c0340480700a5501c075112900130f507180e00c45401c060405080c20000111311100c0a19000c00006511004c0c210030020089046107580070b2241c041515040141984004c000000041c7c5600c4d0482000740f45001c07171000c200d07084d882e1100b88113264402d0040980d000b100700744015606d01c2c1c58a000c0720b0070700d40002045070440c80180c5051030503502040c0801c2c804000c000a1000c1d11411 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 225920530 1250 225919280 225919283
    0x70c0c03030809150115050c03160b10140904020405130f0803160e0f0f01180308030a0b1e0f040e011406040608060403050a0c06020c0604050a12020c030c04110405120a 74
    0x507540c5500ba0804c80d625458400d105501100b80e44039094004240a040140030010389982070f01c4c0ba10920f0400d040c0c4050800e801215444213100c1008032144c0f1030340110015000d800c21a14422201c83e0000e40c0c0182e015202a00c150759440108aa03107015100514010f98414001014040c1c0707414400d0a642017142c0c1000d5440384d0a81410f1780901c241040c41d25000001d0008240140c1d070014814114080048d09044c031500a000482d90040d080d0484025481900040c0e0b4ae450610980410354039041000c900840304500c0c244100400c07503440c03040d900310544904038010b40410018015145074046040d1552801407510105800b0060803132280400390380521000d680c1e450440c0e52201d08807005400154207104c0c41d64054030460b403d880c080d00901026050a0125220608202d81602e003110a030b8026412841049030008503e901c420701400649500c00040020a488449901c0301e0340c42966200f040385112401c60b4151005000c0103080e112000030710486a5540c0d2001c0e020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 225921780 1250 225920530 225920533
    0x70203060f0a1a0604090c0e03100f0b090f070804020102011b0228081602010c0614040201030e1b09040503071209060201111306030906090b0c0d0605030102040308030f070c0c03030809 81
    0x714032410340070900000b0860041c10b014030305850001013800620f40d100921f070070090b59400b4020183c0d02040315110940711000006180c4d5030341c010fa0802c55501100c1385000d215035808005511004050055200d0450305002ca4690f41d607100403801041540304c211841ca03031070034a0342081e0750300003941040050390002880400d01048602d00c1080c1c50280b004101c64010407914031111948011140028418100f80800c2d01c10383c2d40350005d490841951150300d82401c01044195a414092840136051034805080e00320400b649034011000c141401c54080c004040200b0100181001124145034010741c0700d20010034000c0000b02131400340d2144100540c00c2088040c0c001d0b004100711103c9001e2240c91007440c1d440c1503800e03006044000d02c2911260b50380ea10507004914840c100c2d501c1203082c2d170b4800e9981d080c2e0344141d90807919190807441c003980c41440184002207604041380d42140030340e910150284c0c5c1c0d5250460b589c40e00a44001e00304c0081070000802c01d50000380b010b000721032010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 225923030 1250 225921780 225921791
    0x6130e010803070f021c151406041407050f0c01050106030e06180c01080c2701030e070e01030b04020a0305010c02010b040b0306160f050909180f0a081905070203060f0a 74
    0x40d869590303001c2d2140180c1380d055913902c1c1200600d441030080c0c3c1c10101c185181c195000054a420031a071840680c81c54402d0f803640d80f2042c401c1c440850455221200729410440c8030611030100d00355080c0100100300f80200080c120b40c4e6104950180e8080c0d2004100a00203517841c0d0318000c024012900d4448454410000420300400210300000201c03214007000344040c640400044800190160808040ca0070400c00954992001012801d404000c80744400a0781c01e66000102110322424032010a0780010405100742000500e0090450707411500030982529540001204000c581e0300080c461340c6010070780ea840700c0d0190000d0280c800102c80400c00b00052030145601c0d6501210715040703101e9485c1c42a02240d014008102c0840c040d417400e035080c59402d0740410142c800070b031140e5511502c605504400f40108002c1d07003040d100c0c440007510400e103641e0380c0d014882c001d040c03410400000f01841811054841c0342030f106075540040440b030f00350400d082844400d10f01521141d42550501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 225924280 1250 225923030 225923039
    0x4090603111c0204051e04031e11031614030c06040b010b0f030f0a201309060b030c0d1104060c020a060302030106020c06030402040e030a02070f061d041a06130e01 72
    0x303030524806800a580d1040ba11090380e82040001c102c003c00b02c00241000303e105046519081101c98450f62094440b4410130000140384050840c00c107002004100c0000b600fa00302e030401005460403403841041540d034192241c507240307801140e0061180c01c03911003ca0340c1c0c00705040004045005a00800d50780545988541d00c0150307a11420449144600d020808a001108880300381644030340a01d000094000720181c83c4041003080c241e8094a190001c02c041c41c001d107006c2c824100030310401c00204a06840e2a5046040c0d000040160340d0600003c946001551000c1d0441e425140d00740340341540d1a174448401401a904215040e40203240138070740031071038034000c0c0308a9040e00c80a03002824003032034030070030001d1aa01c0140b040b60001e4440803c25100709081002c0d00000040d40c01905049050444119500303045511120805c1800200030103404104003804d014100140c5000c0b03100740401e210078010400070070b1525006240006e107004000e15000c031460944080c8072006040d6640e8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 225925530 1250 225924280 225924289
    0x5030714161208311d04030c060e060a0902040b041506081008060705040323070b0c0f0708010c020f1c110c0d03090503160b0409180f0305071122021e0409060311 71
    0x1140701700c1d1001141e1901040129020704800a002403007813502150400c040005107042103002e861000031182c0b0383e00341c80218600350044041e4158155420016444803480d4070a011070244580000d0207007507004959280c22008414020b05041e10440d0f00e281400e0300001c0c940e81c0b19104c16100c980da085075058010803a900c1854101e8214002072058a041001e42c0c031050b446600154154032688036514103603141848504002d0040b034000051100d0081d802a081040820b42000c0ca900001c85107041809480403441a00c641842d01544103480141d5148c40d29026030280c5511012450801b402c1591240032a0181c9000780d00303079203800041012001d60361089005040c20207905000a105140d40e80d40700d0440b002208080d6001082280c4a120740000c5082c0d060b0002240003401030248100c0d5440c2c240303611070541d500c18801c0010142a07030004034072b02108008540006500e9140c4800750445500340000700d4803240e075195941103080007000d01d80f20803201e00c035040e41060040d05c0c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 225926780 1250 225925530 225925559
    0xc050a030e0f040218101106010b03100f06050a0309080d09121202040b0412020303040e180d09050f040b010e100215060301020903150a14040503071416120831 70
    0xc1d15641d451442c41c5c804100d0a200140010020403101c0c45821540c2042005124024140340c0342d410f03640e041001c401800504c80d81c002c5d43d4100c0e24070301d04002c00c950050880d040350442d03280010301c0038054a400d40d002c0c81000780007600c060510301d10303105024140a0070001703079a80741c44141c2d141c030108000606900a6100c0c2c210103107020302c010044450013034291031030701d0707c010292441c00f43c5810300107560540a03142408a038030300d4009207448440400c5007800d915007605003402200c0c0303010000b82000c000c40b00c14600807601d07000d0f40703d01640102c02128021200414900100c60515402541c5d1106003000700410040c1c440072889509061007211f0f055100a0090411100c8020401c3d0458001804802c01c0a0303850341c40540e0420f0300e124040c003440c4104081c503941ca2090400c0212a41d4a044440f156000240004041280c0c0119142243e41d146400500c420140c10324044a0007280c482404400c0240c031000a449040100d8000e900d010101c107400040c0c540d0301e52400c000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 225928030 1250 225926780 225926797
    0x6011806020d0503091015090b0102030414012d022401030b0112030e0901030311100501050f1c06090c0e070206010503031c1806021804020c0a0605070c050a030e0f0402 74
    0x20402000025001d116400841c5c1c0203210b24101e49034402e107014a841140c0705135200c03c0c0804828070040c08508014014103180c40d100344011410f042c00c107015044048010b032030303082c14444065102410010350000590f1080c1c41040c0d0002044680e1a0103912411a207541011131002d015030517402071340740c00c44030307047c3d0b60440b04100c1940c2c00c041da1040845103450301a82408510705004900303696002c0e2080c040d5203e81d851840403070340c903c00c0038506002e00c46803406450410005000a84031507040d094500d504441c20031400c41c641010180982070000046c03c158203101c43c0e0018031100708000b800311020b825280c0380555030384174100d86a45080c01010b9142c3c004002d510000381d114450079030840041003000443d044c10381000301c540819028120307080342d00419200305423011401e0039602510169070540c80c008900c5c0031551600040800200b034507a40d1030125541c10b00c6000d90f007103142ea100c01203a26041c003d00b0b0142202401005c514403441194240b1100340c2441e0007a0380303000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 225929280 1250 225928030 225928033
    0xe030409270803060a0807030f0b180c15070204090b060f06041206090309210c05030307031e05120a020d0516050304060b01182601020c06040f02010e0d05060601180602 74
    0xa0065030303107200382da6102a000701c2d404139101e88041030700801400150001c500c1401009000e024603c0d0256205100800410b83e01c80c01e83e00c407044010020480340030300b00302212050000c0c4d0003192014198065813030b019400c14642843c0c8020480c04044a60040300c007150708030401450038042003414400c5008100600760545600360002e0300c10b802402c030403442820007103049622a65040c403c0352a9001c200300b15901c009407102480450102040501001d6003d0b5241a003142c0b4050088c212280d1004841078160350400c113001e22560036144280c03014103c10700700e4100a0100401703500b00c8811501d590b49803102252100300b00f141c0b0050b83d43e4054582d28103555507619210024444070742818140902c002c1010030f0b01d01c3c3c41d00c54030048c00c6c7c20000d22030701803007506146081014408200c03599a1040100100600001540c140d00c036070f11480b10040c4a030706100481c0c0700d03d09030802a8010103007400750300410801151680c4200f02c00e07642e0b000b60341509401c00084000038894027000d07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 225930530 1250 225929280 225929351
    0x30a0203100f06051206071e05120a2c0d02010207030c0b100b2706030402060318070503070f0602060f010b0d0c020c1201060602070806090303010509040311010e030409 74
    0x841002e4014010314800c1c5000040c07800ea88201098513102c81001c240c0890700041d081201d01d9401501c403035924100c8101d41001d010329140040d11034400e51341c01641c090341000c0003c0840c1103980101e0320280d4203440c02c0d41813045141d100b1030b4526210b88a01d22500403038410503141032051084c7c58585802d03590302c1e05034000584134000c0000010740061442c60b075046002c0340c0007001000420b0001a04042441109080400400c9102c102202640f0418041080c440540d4684042c2d0b504030100501501002455040462070f0016030b50204d60980160b000000e00d8003141079110b01240c0a64007924181d07a03584a00c491060024010803c82d01c0003409104401c4105500c81d00f036500940c01141c100b10880c00c000f400c0c405c0780c02102e004903911000280031159051240c5801400440020005800c1a502030b0340c684c00305006007406040c20100290030f0500c0340005e115010100b070001c10a2101100b904d80d00c903031041c09480d040ca07090640140e00080f0ba009020303110390340c00b203c80c5203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 225931780 1250 225930530 225930553
    0xc03050f12030c0702010507050604030503190908090f030a0b09030301060e0f03151e091b150703031109040203070306090b0a06090b03130b1617130b07020138030a0203 74
    0x43c3c1e130440001a41041402c0c8406400180c00b002080c1c0542e0103501d43c1c6850707280c0410f00c01d00480800600300400c90030000d07107400041044094415450b821105510001060f5010914004249002400110208050090441004c401103060300c40ca640c5072034900311440e0a1113504440c042c02d0a0b010f612000402881150f604035031500020485000a54041d03800c16850400743c00f44c4040c8081c0c0c004200080d0340b0352420003103420742c0c1d60507a48100c6240d2180000c2c2d01600414001900741521080f55881d041030480c04c643d04a0350007001107403241000c4000600828141c010310908901d4044804800d20b000001e80c030850310681d444581ca6800d0001d450807542020304407050341524101404c5c00103603400301c4148900c141c0346030042440c0e10704100406146010f0388203041e40c0c00050920540f050860100e480060300030308000c1c0540c03694003080f8010b0101c1410080e5802c80e40001c00104030700e250b525215860051b800071355051000003010745412007450000e5060344858081034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 225933030 1250 225931780 225931801
    0x1a07080f060915040c2f070815130606050d1209050303030c04060e0d020411070b01120f11031002030a15170606012001053117090d020a030c03050f1203 67
    0x105c168030f914201042d1514120441403011100604600c40c0f0081412141c007148200100c0004140000041c105100354020f00469600041c0c25003501c000380402200601000d500098009c1c00007034254190030226041a8000d0001c1e6000c000000c0c41c08000000c2501e400001d40740583c190242e4145840d140c098151402220849441e4200e1400d1030036102580ea40d01c0340d40d2500841860942c0c2c1c545c11842d028075400d0050708000607041042c11003202040082e806001225071204107a100c6550400010b0710784488603402c1113000340000100704120f48160400c96140008140e910300701d54661040c090a14001500c85545a02110008405600c43c90042100e00d0300300d1541901c2c2481e5020140c2035445c01c031401ca4040c4072aa40901c0e8008080c0790400d4600f044801003000c10320140c0e9503c6184540c4001d10700f1040011031600515a10b03446004165640180310f684061354924000d00c80303031103600c0162900d0258402d0707030440a5011500d5414505420080c916594584000300c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 225934280 1250 225933030 225933041
    0x3090105090d0804030609050f0d0c080315120d031103091009080c12040f060f0c0611091c060b030d0e060a17250314131a07080f06091504 61
    0x41da4840c21001d8804081042c4800610141d07001e404049420590b5080013031401700200c4600903a0384c845981102e6860780300800c0069170f031740300f038030303030b91350b03031a80311106070419401241c082e03008000c000011244100020a0403a1440503101070000600d64010495075020807070300d04803076400c540b524000902540e442503420030b11500e62a8103052303c201c00649486002d500d2120141d0b000502801781e000110010b000610040c80c0503607840f0a0701e180140000382c0d6500060000303884240e05010f004042c4c0c01d40d0800800a4882107002d00700484c02100240c0c3c81e001581c03610314007404803100d0705010a5824440e05075465002003c0ea103001401000c0d4030160145003082061005102c0401c00a61104c2c02480c1d4100541c500c0611841c80e00c1c44888c00c0ca01110503d840c0c5401824869200c1500c668070031409460010702072044d0034601a00402000301104010076481080030080d000b000d07460088907204000c49990751144180400d001c0c09881940d01150340300c51009091034540c010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 225935530 1250 225934280 225934297
    0xe0f06010306032315070203180f041802090f09030711041103011d01050406060e04200309030a2703020f0102160803041d071b050114010f051201060803090105 70
    0x591558a84620000c14802c400714891051405410743c420542000402645c0e5603c18484540d130401e100080c1d50391003002c1074000c1100d9031098060096031380ca0030907201080050410300200314207808204000200c80030891040201801142007003000d05d140d24401c002600c011071808100381c41e224044110648078607407094036048041407441803680514000d05c1c0301440d07440c0e6020480481d2403a4541600114040c5107080420003003103602c0141120341c00c8050340c3c002501d0074040c500d00203d641911485c1094040001030026001000006203e20320b046c0c0d68100f1029052003128040c0030202d0603c0000c03000070401803000d0b2400480a20300707220305004440c4244075000d401c42c000b5186920508494101042c10000001310b41076000c0e1940880c20144990b29040c14003800c40081c8446400554910180350340400c0401d500501c8081600701e94130130290782d03626045041001a001d07690158040c56042100c0d134030305000b6001543c0210001e10f0a040d0104011605904072004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 225936780 1250 225935530 225935537
    0x905010b310203091e0c0d060603050d0c0503030a0b0307030204111c0209012c0a030506090c06090d031b050601090605010f0509011211040b0304140607020d08070807031409100b0402040e0f0601 85
    0x41b01c03007555403420107607184c138401c11003c90147d16504015040c41910322000d400d01042918400001302c021040302e901c10484040010f400f46004046454040d071034200a40051404045085514242c00545503a00107001c0410b0491036680c1014141c0c0182d000d6140443e2201c131003040500601c500600d030551030440f4411600e0303125400144140c02d40e6000791869040003052100307915050180e00b141800582d0300c1460001d00c040401d0400f0110b01c00030701041086201000440441980312042c1e0b60080110f4002d561144842401001c441c40b03194089900d401440c5c0841e405001580c0f41c100c8141c491040c41031180c4040809040d0101302c01d100344004110214505a060000d540201d00800340044410b501010b000e10700100a01043c00351740c004820140c080c0c0e170102d55240e01014924040015449002c8294087c004c910340c2d614030070210804006010790002191899050201c80600003818510b0502c401c0748207500070700340c04031041c1e000101c5c01e90351410000e80006040c075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 225938030 1250 225936780 225936793
    0x2409040e030a03061509030803061e0d20090c0d09080408030f071406010e1602010f0e0a030815030a031115041506060912060905010b310203091e 64
    0x4200d58250b62000ca44030000c00d64640d402d210f4604c04122a03000302d1441d0808400706030458482c4d501074000104410b2107907203040260509002c012141d82071009001e00340e4140038a03545440542240c10300103448500e046000e0b0100d0302c2c5040c40b0014055003490801078035181d40810740d00d02800e1401d4055540079801c000000c0c03d00010401403104144903840c2d00d0302c414091a15060460061035052031542c04800107010318000305240d03903003201c010810510b17494a40c00301030780501030151706151344034584418514108008603441c540a032003a40d81820b80d6403040e0600150805851030140c156000768103e90019003d9048204002c988800311400754031000341f94244501c048804440c044000c40340c2801505441c000c90000d050f0300e05050288504021440ca03c1c1960303d200580031589a82440041c000c1c20740c00a1811400604112260f81f00140514585a60910b28503292101c0020b1003c1800303041c03003541d00407100304000d003080007046405c0380548008078901003c1d0b4002d02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 225939280 1250 225938030 225938051
    0x3050912030709170a021f0c12030902010e0d110d21021c020102040311060f130905070e010311030406020a1202041e051e0603070e040203040b0a0b240904 68
    0x300a544690b94607901c801c07031075051407522090404421142ca1040e80011440001640d841c401240000e0a54005c95141c801c044001c50b05402c00c580090404414030490109240e4140c1010181c107000303803140d21282201105020303800e43c0300040684100c28100f580b807500d02e001e540351740185001d146035241254442d200805060342c0101c1c0300c005607000d13401003100e00b00c810700c031079001101303c4c00214101480e54641403030030300c4818031151207180001b6180c8055144001a01c0044407500c2070011005c0c0c642250500519003035446102041c4c0c450442e180319803190144001421040c2800c40c1551216602c050107504244016001c1c4a01c4600401c40240f0a1000d04000c6c4869891100b0380c0e080c5e0f04900c0080c1303071150083c80c021604566107282ea90000020030000100c00d0744c1007980ca6407486001c407180010041ca01d0340c814000010300060000c01044140108020b8404100e031000030b004001a200541c0c140501040c6101582c06202107000060444404c000c1e10109810910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 225940530 1250 225939280 225939313
    0x121020a1107080105070e030703110d0309180501030b011a04140f030d120515030a0f0827030c01050c0607053403030605010e0a0e0406060b07050a030806030a0c06030509 75
    0x10f42214006079594420005521f41c450128040c2c0c20054010b025090b0440e00c03104422003c05090328010201c148008040601c1940c015005000c80303030080310072913201c10101020301320a10058230041c91040c000700300e50207101080e8040c103040c0601c0c546858940a00d03501d82e658541021507100040d5803803103515072024890f40603565041e40c1da0380281c03000394800b081150409800c0120b00b2004041e000c4403510005451100150010186a0494610329015200d4880d440c441404c4030101690104000303106042d840360030300300f1001c0d80c9407804010300456960141e0854854240d0080020400c400d024070020322900c08200d142003120450380744002c80c1c2005241c1c03425280d20303c40b05030750f082c1503062140c2e00203442c1c00d280400c6003427060800641091254080c804510401002050421013070303510403030040018000d4142c5611040c1841034072121090400d03008580c585000910380c0c83d0203e042400140e210b01c40c5c90046003004000c030010300008060301d482e480348003100e17840c0d00c0c0d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 225941780 1250 225940530 225940543
    0x1020a020304090c0801050a06080910020d0f061706040803150405070f030c080402030606040c051312120f1e0201020918011d06030604080a05071514060121020a11 72
    0x9190025907507a0b1401c50307094201da68601e2400200507482005000b6030b959020003404807400c0e8540034640d51250309086003483c8841441250703442c030000d00c803d80c3d00c0340350f04000408049460100700c902d540705100e410100400503401502d400150000c4c001420107006190801e4510342061035100341640840e080394000e40e0b803180420345013188100d0650f40b41c066860a0b849610b050780c00c03410030340d001c00d5a07114050b1013248203603100d665582032644502c0c1620802c0024032401501c0f181c1e6000a0f800c01c002010381598604d603003004544100f4007422600d4400f010315540d1060000900000d003003544900c0101c0c80455400f0400880303155500c1000406e0603024540a031113651620140451101c29404002c005180355410030883d6900407460380c2e4030a8000c600503541c1d2500c201d08070748603c1280c100421012040b150f00420300309542c80b08a99200c0201c417007020340c03204030054926000094424007117010001c842c4001094a80243c62600c05238141207a52400d140b07403042c2001c0c0b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 225943030 1250 225941780 225941797
    0xe062a0f030319050115021509010b0a0312020610150e0607060c0e041b020c04020901020a0209040510050705030c07240207050307021315030303050601090b0301080606010807110304030f080c0102 86
    0x2490f03403480c9034080007501c1081c0c010421610f13141640c00302c940c0065100c801401c0601c0c42001000b0020301d90303030020b4108070907020300184886910f5840e4600800c12095445400c130051203a1000102c4440c02d03031007003070183c8440a140034503611040c441104e0707400707a4201c03154210320144190000111240912400310302152a911190b1018100344801c03189452007120072000d1840714842e5444c2c010401e8061400159000b595880e02140142e2402121307500081d0804090b4040105201d400720b60300c4000610035409001d5616441801c5800f400150303450f00350100c04001d6000042c50661100c44d1104190514440b01201c0c104100101d802070b0405541c0e80e01f001521504510344020403180700c400c0c000042008120000005244840318040102032544d940e012401c01e80c001c200b2034004140040c81140d0329078640715042e440e0341064a42130302040f1500081090203000e91300408804407910011400d25146403203800950041d600e080c2c80307100d0f0070801400c1e08035003800209540d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 225944280 1250 225943030 225943051
    0x23040204050d11060d18110603240d0803180601090c050a1805060c0703020a0803040b0306060313020d030507021923040209030f0703031b08090103020705010f05070e010e062a0f0303 80
    0x390200d050000c15206280e0807d4400d290400c00c01a14401080011856915001c81d01d403400c07136140c0101300d080358000000f80801c1004030130014000240c0001c0807440408006580b01a6a07441c0b1b11000d540104000300c0c040b88082c082410310502c074082890790010009020440744e640c817008103003150310080d1802016001380f50305105505110182c3c0c00203200101c0154649032030032890b07201d280805804144100000004a001620403503081c541d01d07600240f0204c507043c4540b40103401c59005070b104a003d100140d01000e00144981404800c80319042c486869403407803a400c2c03441d8030540218443e0312580c00d1090310116102040f85807204d1003000000c1c944a4214203004d086021503084c403111202e91044a40001401602a60a01c2d4820300740942c13602e10510341640540000e0f00c2c440061850441001751180d403207250050a00c40070780720300100c281c401007032040b94447c03290220244e40510302c44144c1e485400c4112600301c0c0f141415a894504070300c5036103003541d000341c8400d8540c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 225945530 1250 225944280 225944321
    0x1140f010501090819081c18060b010509220e06010b1b0703031e0c062405010c0f17040506040303030203010f05010c021804150623040204050d11060d 66
    0x46507045100c00024000910040c034445e1200305041a006100d100000d0000c600400d0b101322442c0619008884c003884001c0c28445001b10b1a2161003c03010810144c5289081115480003540928100d4007200c8000e4551504039040c83c1c880e0014003161038090410550300c0c2844183c4040a002150103804008001035035161000520100001c04154420042d0098078080001942180000c0c1c000410701001c1a0889017182084e03403080340141c0c0203403035a424810b02605100510700b10381e45941051410303c96580e202c174011900342c0802c0c10000e0000024584030000304100114038030f400c5440c3e0401e103140c61703220b40200d51180c20079030046020170340100040c800072600d02454401b8103420b2a14104496140d000503c40403501e0068400790b130420804213050100d4601507103000b0f2042401440169a50000d030001d51003da45c1e40307201c1d40703508942c0581a00e0700d0b008480c22641d0040004945500c240c4403801414901c134203d681c80041040350368200d4855014080c4805402c0d42074220 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 225946780 1250 225945530 225945539
    0x40206162d050601060306180906061703070b01060e1305190908070501061212050c0c030d020c150309120309030d090308010303110106150c02040618060f0b0c06010302090901140f01 80
    0xe040c0f07040e0805420305007412018001ea115815080039890b0740c1c180c02040c044450b0600c4402410075800c058041640c4000b401249a070000080400b030380b003082c1c000f40c41c0e03076180000c5170343d8000c543e80b040d4094490a5110203180d415040746800100c00385c0c0c03409400703602c0307031440040704d0242400b180d0a407804506d0340140301d02032040030000c0084603409803041c48280e030348120000800e0144801d10001260401e0150781c1008410010000075017290701580c600040a035980400b0190036100c1d410303164514807054000d2058900601d00103008020402c02d1440c04c802d5908014011001ca05c01441500c0c0c0310440c80c004c02c41d1150083e119111654118100104082803400360b0a0950303040c41410060701400f8000c000a00341d0707510709448134032074610004020709000d9201e41a510910400001584040e5001d002218a034405482005655009025190060f80c0340c0c4003040d0002c3e001003025080c070701d03030b520b034081520000018070030009101140c0b041c4003900c2809000318003000520 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 225948030 1250 225946780 225946783
    0xd180b0108150601050904020c0f060118060b07080d020901020a1e150b0d0201030c11030c010507090f03050703080304080403051603050c191203050c0601150306060503040206162d05 80
    0x81c440b81505010100c28505180064502e10034219200c0c0110343c000740030002c00340148188007292180341d06030360b1296540c8812000ba502850100c41110703103000d100080c655410390448500b00e600904a03400c0503034180100c4025005010014154014009200e00150382c0106250901d009035010b030b10750025034280b2018040742070781c820000510b04504003010750b8944400c040041c1d42440c1c00f0400406080e0700321044500c4071111809480301103041c41540c8010f4225900c15031295940300111980c07556030724040350541c4400b52032a0850b04050000c249110300540e8401c1c0126002c51400b40d07241c0c0d441d8680b03039448160440580710003070217004000b8207100296200404940041b90340022030398038100c402440c030030350030840c240181e80d000b0140940107560440920304196900c42d1307561620405c0f8002801e00b034000281c43c190000c503841e4007840940780140d40140c09282042450004007242140c1801c06803103007203114084084883e1866016450003048025000403810340d4074019 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 225949280 1250 225948030 225948043
    0x2010050712050702010c0b1023100e060717040f06020609070504020315040f15061e080f0705070c080106180b04050609040f08190c02011e140d180b0108 67
    0x1074040000800031000542e1340046280107150f0007a40c000300701c1c0c841041405038138400d0340c46000c4421444d14200c1ea0941c08a003080c07202c810a031030300d100251603a0000c681d10404c051949501640500c01400850711300c0010354503029503500114501900c0b8a82041c03119100d80c0118010b82c840010042c01c10400d04c842c0000740810341e400e508608140030708801da0460505c183c0d0103650390b0b0510310182e80c0c0300d42100740c10408120484003180d0300c6641c02440410502101c200000d0021070000c0700030f00c9040d1003441400d081400809580724500c04841c1c503481840c2c151040d401030035001ca03060744e003031094000400100d01c080130030b0040b014042041c0e80b01e000c4502d102d94039000070420980c468928041d0f021f07030b002d09010f505418516010025000d100350b003644102182d01843d00301e5400810000150f4000d0303c4140c0b941d00350340002d446100203040b800303000170842c0e800502854050005000b00842c004404203c5184c1101c10030f95a4000003402e844141020004102800050092 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 225950530 1250 225949280 225949313
    0x303010e09010e0129030c13020415021b0d032106080106081b3a02040b040b010905190801021614030f03130c0314010504060c031820100507 62
    0xa00c207801d0095124005548a041d100110b00307140c4170041460342e020301c5910100c0200910b080480b04081e42204002c0d082800342980442807a40314110f0a4000584142c0506600307103010581c00c40c00c000c1c003c180c49188821020f00c818401d80c480107070010301c0201d4805403010400140f40d881c2c8203d0500b520304a610181864014994a0340c100502000107100b40c9800e54090954002c420b281641c001c4450b90305181c07842d40300da04804610360108031104110f0085400740400503503c030400080704c140024240c007258500078100078605104800720070100078100c446601a0f034034900103007641d00030703521108000700d1144540b041080840c416044903419200440c100f41e40c0709030300000f5100250445004039480e00541d41080740241400c030240d45d002c2000884140c8490f080390117410b06880440f001030801d11b44200b45403003841980095201000b254003580d40d03603160352400c84140180f11403004410814041a0303140c1d0349a64845406583d669580c824031428100c62028846a2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 225951780 1250 225950530 225950533
    0x3021b0a0201020d050f1210031e060507090b0a08090f03040801090b070201020304031b080706020409020d271403091207031205030606030c0c1f0e121e0a09080303010e09010e 77
    0x1115052000d02c41030341c0347c0d0044101c00c1c0809484003540c1d8030920582d580b005001035008610426000c280484007032a41c1c9c8548400d120070744a001082e01c03000c0342402080c880c12010b201040e000d600ca03100898001c913034030050380c004e8152420740034119881904130200d01c0e134441031100c007004003810a013035100c1c0483c8021411402c1c6658020000500c5050422000d425040050284085c48085601c0290300c14170455640303540d8000e05010b5000b51811041b06482d00484241513224204120028203d106c2c00440d4001c1503a035220904910210a00b064801400740c0c1e60382c0e80718602041184070301c14005104041c5146002940c84644032110010000203005000d00d035110341d0306507500983c0c040002629402d40444884c40d144a039600c90030b011544194280040305e0b65440030f40304070188003e5860b600d8601001c5503003882440d10442c04240080c102c0118017560501030a050324061502140e0659904002d600d10741080e0000c2464440b284103100484100b4030910039240030780b00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 225953030 1250 225951780 225951787
    0x609030304020f09040819030f1b080703020a170406020405090703090506010b07020d05010f051b130311190303050306010813110105033301110312010302060a03021b0a0201020d05 79
    0xc2c0400d41a20800007414010b42040c40400c0400c08205d0640e8407610075800c449061440380140203001d080005103032494546001e0080c2c0c0c000307980d054a403812202d1034481061a4550035012402903200d0b103540c004210150709111018948a803042d8001c502840c0b02680700ca051808102002e000549500c003410700d40030607040028004500c2904403807000c20141d0b00c072215400425556851450018915482c0000e400d9482c9895403086009040ca01803541101e045054075005502c10b81413007500c0c221002c40e00b003001450f98403115200c5a000f07061484640c030b440b580012450207540040740420300200400c00c0c40d50784410102d47c080c0e8111242c0010f402a92500482148106440c03410480000001501941c41490f0580c5001d83c03103041c50800c448000c80f00042d4031210348500d00046420144504080002069540c003580b11400b1507116442c5508102c0164004107010043c16024441030140c901c2da9444a000e206400000d00803604542c0300080c00d00d29111040c0d8180207050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 225954280 1250 225953030 225953033
    0x5060c13030f063902010c090902090102120409050a0b0d150b040b03150915160509011b03052d071b0816080c010c1203090c0314030403050609030304 66
    0xe03200e840032039800c4800e08070b05404905280001c3d2810031040910111100b03a0600d64120094641408008480c042a04682e444004030700ba1000c0381204000110005014060380745140d00030414500140111000d103003504e03030712540a0b04141c2c44401c031540d584003004a005114010315140b608102c85440d60018103644000b8200c3c2c3c030300f0411036029a500d25410540c7c607582d0082882210040803507458010915962030b0259081300d864030940281c869101c200e6a0f1004032038012111603070803105001801c9000c8400c0d801c014095030400ca441241b0305081c0301482501c03d0443d000355034241e50791200618854204912019803054140707414040181711002000b030780c403031550011903540b0425810054000130480d5400440f082d000b01e00c5043c1407a49002d14110440340f01c2c00a83d842c00e011200152902611010080c2494202080401115100394402030409120b00d080d8010345887e0b40780d900170291102d500d50b0ba561b100207018800d202003004642d9210304094011465460107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 225955530 1250 225954280 225954307
    0x60e031c051c09030c0807020d0501060f031103010b15031b040b0408010b0f03061909050102041d16050301090e0f060c1b060c07020909120a020601210b150d020406030501020705060c 80
    0x85c80780140808001081400c21990380548070314103107410100070f0210603154a03440381034019a200c1100c003490048803d40143c00c040c001c81200040c0100404400d090350504214294001440c419900019141e0282407030164030140014105d1000c0d4951140d0505116608507550300c00400d10034000c155940300165400a03c007030b404124050030445803940b0200303ea02400d1060030003000c0354004140460108c50440d04800641805c0c140c03d185038680743d00512800400b050b031400003030010801400480c2d01a00000050030340c1900300d0749084480c0b1032040c2082000d481440101400043c000c0342c208220008018211000b401780c49241031615200a00707125000e002805628104000340007130509000400385400a00141036842503007140080d1280030901880460340440d01c481142d030038013010249051540f0a4080b072054a91100e242c10052221006d1075010510241c2c010050b20340d0300800f0001c5100e00000340e29a082071604c1c0381000d200801c42030034001c081c07002503d140302e0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 225956780 1250 225955530 225955547
    0x60e0103050910021606090f0b100b03010303032a02070513020a050403060b0105120103080309060109050411210709050a0515060a0c0f06090b0a0606020d0504060e031c051c0903 78
    0xc100c80016958120004031005500020345c0140001c1e1910310741c9000d2000b04850752249511440d503400302942c80c20005060807009018a081320007080c1f00510020780070303520801a0303800348042d61800340107800e07003800404225101c500060b0840e5600300528188143c052441900c2000250b00300081080001c126000b107100252142d92107088a80451340100f04072480c000100320320b40341640e189d04148a41c0c0e8025203803159207101c0c12000042c000003501c103a6000319480381580b10080001e80c02c00c40c0f0068002c8940e94004140440c1c0e81101d0310030000030005240318100403560b8603089080d002115002029841d14840d004a07480c020768403081150007a400307078105003a0200c29800c0c1081c0b00d0030324180080240b40b500d0144804d002c014100240b052440c00340a1000c0c0c5d484403400c90f150100042e80d0300214100f440140070990141c1e840401c5500007038103c41840c3d60085110f030071480e5210036480810300004030000400346d0385c004c45e0075050881d103081c446009a0b0383e00500c92407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 225958030 1250 225956780 225956803
    0x15030a0e0c010e36011715010e0c0711091f0806150d03020f0307060605030d030618020d0b03030d0207020a140306010e0702011b050307031a06030105040e10090c060e01030509 77
    0x183c64012000c284c00b00c0c2030310f0110803810402c20107196071903106144c0340c40c01540c5850f810340b18103140341e0005824903114505850541c41124042d8994948001d01904150b01c06c0359540300803d10488652a12180107101d114950354001c1004410000140010030f50b82142285810a00800044845c202114040885c00b070f40c0d1480ca04545040882c20030441081400640c040007502c0024080305402003815207200b1015a01030001d85c1406800b121014441c0c508480c0000e606480f40d10003c0e4058001069101c00206a030f484d0072000070701316030100c03109402c441e45c04141c1005500b0310103000406404801d400c070b282000030000007940c40e00144221440003c0384000510594402c0d00078405070a241001030340050446103024215800440e0000000703032600011903070880c110f6403690300702c07900038260f18a96401c0a040c8000b03000c00d150440c60703038410b5040d400e202100383c2c810f00012600601035066482d080c500c005248281420000c0d04050800e401d01085442c007045c010b0019 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 225959280 1250 225958030 225958069
    0x11703250c03052b02060f0a0b01030f1e1d0309090a0e0a0f03021204030f060906200a123804060611060105040603030c030e15030a0e0c010e 62
    0x80640d0320301404214815000108039009014406040b5180707500052800700d041800f042002d00550000ca903a030100b1540c040144102e080030542d60b00880d03108501035003041c54040384840d407100b00c640c00d8404d07141c01002920411000018110414030409001110a034520000815024609560f074055840d10910682c0d0350000300e0480000360f8886003801f4010360035100c404070302d4180100144001c0c2c9040c0c000d401001c0d0101070705800101100c1c10703217038003006030342051005031128401000f40d2102210381c01c0ea5140441000154a04d0101c03a40380004440ca5485201c06401008200141c02d010101c1e81071403403804150b07800e00c6249020241600d48003c0c8103450440401d0360510903c100c0760072907d0560301065080d4008043c0d15440700040413280c507a42c3ea00144000c4501e03a100240c00584400c1e0b4900000340310340b07250100da10b001409211400700100d021503c3e42c3c810380e03120070b005039500c0c3d180b12055401c0c8600c1c0407074202405c1075a041101d402c04a000050640e1440151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 225960530 1250 225959280 225959347
    0x41e150305060a03020a06021501080105071b0c1214100207020105030a0f060510050a02060c07030c080f25020306060406030804050d0f0b07020109020a2309040213090506011703 78
    0x125100c0d02c080d0030040d1740051a120401c1d5503001d01035150100c00a03080c1400301c20b003001081b03103034050081500070200e5607a206607076044944000f40c1100e032100c1c00c403000070a60100040415254003903015080c01a0740d00d0f1aa076800d500d1341480d098812480400300d5006000300c03000b42c1c1e0418152a4040d60300c60001c01c2542ca5a5503440081005400c100d50101c82c1403564510503078014040d10342018107408544050701d411040b14414014940f00130001003030344048200080860300a044801401c114160810303841e291003450381c906402180181e865058240760961400308215900300d1400c0c2d6080202a0440c1c82e02c041c2403041d4015540584c9020602c00d00300724900c400402010b8201c05c0c0081541007030304001380603001d00001070f84074000c401d0010440301290000302500362055000d05804ea5100024402c68810040040c1c0c0c0c811001502c4500440755405089800d600c41c0018240039814076035003020365000355001d8052544240540303e800e8640144a107020003207421065803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 225961780 1250 225960530 225960541
    0x4090201050c060403050d060b090906040b0a0e01080a150b180907210303050606180d02060c062503020c03040902090f060403120807050703170a020f040b041e150305 73
    0x503103104240d49110b8910a00c0100400d2603070050107010000c07011241171001d141d444100d100203000d944441a03201d15520007049071480c0a070b01000d21814040e1401409642e1760144032803540c8246c2c0400e01a801400310807041190140b80344c20008001c20f41048144070510100d01d0100013070f590021a00100b0010a443c041d003088814002d00e1044494002c02400b2403c0203c202d01d8101b04178042402c08002c07074250310703010302a5800e108807200000f00292204040000201203d40180d80066041000c2203041c030b8144030441c4035a480903030f0796403803c8510740b4030071007007002200c02d408140c4180011090401c0c00b00489045451f20540540c41d00c105400150040080d011071b154049d100180000170481c0252030f00d1000c11803622105295a160141603825101d19480207002a40d81105801007090703d08a00342c211482020040c00c0004044003000c90758041c0e00a100b014030b010500300001544d00c011380071a145078000307980c0d1306032a2104e4142031307910940045090549500000c0c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 225963030 1250 225961780 225961787
    0xb0412021002220b03130f1e060b0f01140d0f0204080f10140c090d05011d0a020a1205120705011e060e0a0e0d0302090a05030105090d181404090201 65
    0x1041c1030031452045555003880320149850b529202c2103481d1030900d28600041450303400054034030681c80c00710b01200c442c5441d80c6074003d00c0340210044541074100d505809113180c0c800300000c2050300c580d4000031720341d0010040180b18665848201c0c10072600354070481e020070b00707501a2149040c0300380300400c0d0409412014000f0380a02d4005845611900c2030071071620800056555002c00508000c000c000c03580c0d50710441e00401164030404d8100c0030070101030141800c0001e21003050098000040e8030350350307a00c10400459140880d022692000030310206602d4684104d170020410004002038045160b0f03078458440e0f08411000c1003260010582d07405210b03080d0855140350180740900306101d0001d80710704000313000700d020321840c0b440301e600000c406900030301c103542403400e840d0002c0c0541007040d44100c0181d8418440381d504222844800280e6860034010380f4060000400030f40382411011038024008860860001d03504400004204a0318800c40e43d40061818103940c08206680c2c80d00058 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 225964280 1250 225963030 225963043
    0x6010303140a0e0907081e07090b0d021308010b010306170c120a14030a11010b0906060d06030c090902030606060a0e1903080316020d0e03032d0a050c010f05040b041202 74
    0x82c4c0c000694400300526154442da11034400c0d8884560800c2c0144402110720b02a8030441d404004210160010b01c40d6050410140a01104440340940707803104510007281442c095501c030115036034684103603908560b010b0082c00301400840d00c81d6500d2180c2c8001496485d0110258180500b1016130320328802c140502044410a400481d00c01041030118061980c0e544211803c08c00200100413220070090180512030008030300415129003521920308010031035201107181d0b01e4103079560000000151002c0a0348004040f0407500040c00c2c50075005150a000000306410711440b01007015101442e01b080003618580c00540e0390150b10040c80c203035684906038030f802c003030320110002c0100300c444444071144101c038a0b456400d48a1481131080241c40d00a0748105c80c6625401c24040d4200d200c2140b40c0030440c0030300000403103000340e00c24040d10070710354003000c492800240005190170f081c171400d000c0da00e101c4003005c0c01008907103000d844084d80e110001d030001700300c041107210142940c2e1003003200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 225965530 1250 225964280 225964307
    0x12030504050f03601503010f0501030204060f03020904030311070b1501020706112a0a081605060a0806010513080d17010b0f0403080703090e070302180306010303140a 73
    0x81c078144198504410340d1140298428503140403400c0c02e00038401d21920142146001c41200385134611034915102d000d01c20001c00c941703007254031018003041d80c1e903007402440003560138650001a6941180103001c00e59805401000f03c040e44a00704000503102c2a003225801605440c00041038860b401c00d840c500d224481d005004c07400c1e41c0f000c0c005070341d03815100e00ca80c5140903000c884105903601010b980c0c2c0e40740d0380e09003806600801400e480444040c00c60100303001d94000200480026440042c0701c040d2280c0000156611903050742c0c03400c54204400d08050002102c0407801c5c0701c60f005009010101c020300d146c0c1013160100b000310b0f448010321600d1000d00880001c2d150f071518500c000400d0240d1440c0d40f07801400e80381000080180c098001c5070302078100e44007900e2819082da26600700380c5c1e000c800708400b0484840000548410810340040c0201d88a58000d45c0c1d0b8605116100501c50042000501c41e0300200c2c0104002902304d038085105180c505070700c90700c8066400c02500c120026206 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 225966780 1250 225965530 225965563
    0x606140a030b2205061518060903100b1201090b040f030c02040608030309010c09030c0b1b030f030103021002010e0d080a0b06040312031503031718030c010c0912030504050f03 77
    0x46004450f111003000c00e00c0910881400c000d2a5906070800c004104030b10f200c14040c0101700209800d11054051544419001400039460301c4500c1700820f14244118602c464003070703640c0c5d00f035a80c00d140055000c1800700301500203003c039013100e895140c2c8141010b40020706005036400624201409800f041e010250024800c001d010342d6131000545940c0110b0b204081c0e54179051441d90303054080c0d0809000d4035000350804102c681801c40c03402e851780c440950b041c00491f5018503a40b02c0c44003003005146240c989000c00d0b442e5455441031008203c0d407000054156410110419500c050000301302c40c2d00300503484c08400c19118941c09500410010b00071a800c400d001030040f040c491140014001e500d910f94040000724900454018074107003a01004002a4032b00000102440501e81000d82052503a000714588240e00000303d031540d44452520724403a51103500075145c0c40e0700070701008002d000c0041034480c0d003d07403036034024024400d80c0140c40c45030401c0e00c050388040e18204407844032a4500b88 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 225968030 1250 225966780 225966799
    0x60b0d060f060203212d070206010f0e01090509010b06041202310b01030e1203100503011407030c0504090c021c0305060102031611061309050105011b0201030b030a05100914010606140a030b 83
    0x46c03201303201da2045032010051310960000140e1500204180021122510081d61441c0d01f41103410001c0d05004d80006069034039200b00d5030b25580c0c4d4000400c0104464511460170031034901c140407034000500400c02484812040c141c1010050991a89051080c040f0002e11080407400507001040d00a6111469128540b214035450030850011130240300710280c1e0700c50007a81e540030182600e04150454143c03482541c00310f00202e020343c00a940c205014100142020f8541c2c601e2021111031508100c0103a2002104018165070b0b00090203142065207424071141c1362030800030355a0720584441c04d03401601a005081401b030b0300e812448617500f00400b02035072030030226412414a050350054070f45003868140000313910360284d40b0b000e2401040c00e90100392040150010740040110420894140c026590100c1c001a410b020000c5500c5080b0f071300003103510441c2410070641aa071490b907200380c3c0c5006814003480d034001d01d14042c40c4003a40c4c003d45c0d491070910012400b40604160b25038210303d804 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 225969280 1250 225968030 225968101
    0x12050a0f060b0a0522033e0102061501020f010c030204080d051e09040e0106170c120709090512040801060303080604050601080c090103060b0d060f06020321 69
    0x150049481411400c0c0148259500c40d41d0042c0705120714400480407402c20000300600c803400c002c944d41881c1070303042c40c3c2a42c42c0e52520361480f2904007500625101103070800c1404000c021540d0307d030b0402202001134030314030f0341c542c0040d50340d801c00351074188600701013407d03e0210ba100300162201c4101140091080481c1c07001d010700603410501503c202070040191003111903201d0000d4812828120380c1d6034600005e0a001141594070185440380c101e521240390802c030301004d014241c020b2280e01100034420702c0400d911400c00e94a006100c4c400d968102c41c04524010000340681515101600003901840c00c0c988030303241c4507541a90940d0190007141c0010f84031340650001e4100e074040d0b220307022159078100822040b00c0084400601140d403000114070b400300c003030b0058025003006041c0010303000c1d210310754402c20740c20141804441c142c8468080c000c5113504c6807a1001480240019030920043c092032419a00000b5045095100b4000001d40d41c085620400c42400074400700340c0482002c00e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 225970530 1250 225969280 225969301
    0x70305091e01060f080a050d05090d080a091410020303040803071806090905010b0301050d111c060902120102070b0c031509011502250519090227040c08060906011205 73
    0x114480c0010b44c0c5904100090204c4010805401869001000d01074041c81828144ca042d0480108240c00050014010000405190003880d0460a039143c0c0701c512490700401202922401e01031f18010510615428007103078000069a401a51007e055501c075070f9808002c4070700c54030100b80704141408d01d00c400190984c115101d03109850754a6000c1c0300030703030700c1d19001304c200c2c8003c1c030605800104913440c01c0007181c115a200c46201c08014105000ba00c4409003040070b00c03000c4030301038450316a180407200c21480e049102031800c61404c0029420300f50551a08403207200d00030200780a150b000030000300c50302c400035038940c500e200c000d0004040e941c44060500c0107407005e09005000d4810300a20010f41b0400c407844012001d09404c6000d074680c100001e02c041c4400701c3c000ca13000300408034808103000d401800500304d1940c205106428080c0b40261081c03240030441d280c18025480c04462086241d4000b030000c1d406034003030741e8405183d115407004131280004042c41380001841d0005118544c9007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 225971780 1250 225970530 225970541
    0x70e0103030e01090f0501050304020307090f0e0c0319020616120305090f1f0228050705070909080d0c170901020d0c051306032c01051914070305091e01 67
    0x380d0780d02c2905040c082c2c01552041040c0c01003a0103480441e90801407584100010340c2e00620203001c0d41da8450b0b46900200948030400e4494250070384882c0356044448041011390030000c400c4000300542c9080741004606000e0b00d85000c0d020b8100000c203c0702c1005d0200074013032000c1c1e001c07203403040102041000034001c1000780da0b000e049010349540768440324000100c240f251580b032000c47d40c00c004030701401002544002d2055288407548006001030045101468070a0b81490715103596900c2140740c007508100c8a42c10690815140075501c2022035042d50607140da0444100001500d030104001c01d50b05071803c1a4008444d0b0180002c0009491064000d00107070300740c940c420302081100407c2a1114080c40e490980a000720304402c2040390700c80e4004000003091030515109483d501c1a010703040c9a00c555401420b40c2d100c1c030174064043c5041c030a8442c0d400104200300300b14800c0d002c511400d803d0240441c0c08041c0c4800100310b0552050000300f080180481c0d5011ba12400660740c14040c20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 225973030 1250 225971780 225971783
    0x40302060a050903070b0a0c0207080111041706010f05240d060e0903090d0f2d03090f081f020d09051605010f1b0807020d0308090105151005030a0e070e0103 69
    0x24100008a80c185100105684c03100d684030b01103401a0361041d11100080c0f002c230300102d0442c800e901d000140c20000384181c41000891a4207150b4603401c001a80000c101580c00c01c031000da01c62001080782d09140d01103141902d01c2240c000050708500484005050b0303819908160340c6000081307402c0c0b910007941c490f03412103140c40181103142d03603200440d6440b401048800e075005122520700d000024170310400c100206110300900342032915540d03d0032026806249017090030316100d0600c40c060641001d00d80c401810b00700c03400d40284c3e042803200b0352204580303130040d00700e021380052040000000b6019220705003040201001700405078203102e5514494201d41021006103200c000c80c0039481940c82c00c400c1e00661b10340d103030409401408004017034080741c2c0a0711240800e100110060356a03980c0062114066581c2c4c0c0e41034284800c07580d0031110083d00b40501e4915002210f08144c17908400000d1018090030043c0d1031740c0d1003803804005801c0000c14003005010303c140c04104090804449810703603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 225974280 1250 225973030 225973051
    0x5031b060406060609060504180f050708180105011410020c040519050a050705091003020c0a0b0f100f060f0915020d170c070b07030b0d140d05030c0a030e0a05030304030206 76
    0x4640d1020142c401741d84a008510014408000501803070b58040141d98004064500018101042d0031850080b41ca06503503d00005402605204142880c076407103001400d400c800030000d5504d000d8410040f000c0c8000e409000311650004114900d00902007030b6403084000e00709000c00d1a00641a00d207120b0204062a9254034010101c0c200019600c600e51084183e911100d152907190f6040180d40c85507a02c103c401c0580821140550300b100748002d50302c1c00c0c0b142401e4886424141c00410b00000018a07400c24080003900401440e08110410300c1140d0032401d00c200095180d003821100119280c00c61001c011000c0d60400700b1039400076038005440001d990700c0300a4010107a201a901c0c01c01d8032032202c045014441d620114000c00d25241d0001640c0c02d00050310040800030400c210000c03001680c600f94107590750b23036650006001c400788100035403030124558900040304c08624014030b16280105a5a145511203282c002c0040078135958110040326107910381841c00954a071001c55800320207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 225975530 1250 225974280 225974291
    0x40e070c1a0106023702010c050703080703050414040506010c03081b07120e0607051c050d0509150615031602030c120c0c060f070303090206040510020303010905060d0b040f05031b060406 82
    0xa0760241e20301c0d1403070703488205400761005d0541c1c00444008560040c16034040c05031500010024040000800c1054401d1322020780b11031401c261009154800f0003032500460520b801c125403aa0f11021a01c80d0650508002010351038400c8040800c6000c92800d03141c1d504002070b864188071445d6000900c10403681d0300c8003014000402404a680110361300180580d2002c0c07c6c040c005201034060083c503020a1801134100507000310b07184c051b160705456901e0950003072052803244545180415500490903100f400450300303103440d0104e9a02c4000e01d2402c3e9502c55406100e4007900c280308980400c03a8079130484212610310781c00b402075172340a10006200b83c410100c601e07120341003a20648904284400c12a805d0003050f071416805410000c00c202c1c0c0c800400c000c0869039556030b072210341c000c1119a0003952250b0420000104449000d0541845400c1d80c4581c0000100d484802c11381c040d5000d20050303410f40f2246846407560042d19090014122050090541d030400000d0542c426030288809015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 225976780 1250 225975530 225975583
    0x50a060f0611100608100203190c11060108191115072003060402093d06080105120304180b0607030e010810080709020c0304050405040c0e0c040e070c1a010602 70
    0x204c0307a04e03100f4044140c108050b00361841a02c0e901443d8414845403800a05156126106084500c3c5281240c08504000d07561414100e0030040c00b405002c1810003020380b11360b0b140041c0700785440c0c4c080003003840340041b05008698590050340d04613110321061a9460300308a151421074099440b2400384101c04041d8078410600d00050b0090055801400214203500d40000e581150340d0701c60121840b84441e01c8100d0300c201c601e45141ca0340020100d0500f1941d038180341000709812410b1b800705209042c8410a8000607002108880c01c880e091501c0003c43d000503520000a403d00d026910b81c08440030880505040d082030603020007041c02d0342c80c1c21040e07503222030505030212240608005030744424018032007a12154002c02c07034030009400322824241e8a400280641d58220340c21240524002e408204071240410b40c00c2c0c0024031038040905083c1004020784036660000e0068040080d81904102803100140c41191000c52031050a0fe172580c441d0006550b0310000e220b481e0213501d41044200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 225978030 1250 225976780 225976813
    0x30b01081c051206030c0901060f020d05070206040506090d08030c04031101180618180b040c050a14090111010f06060813030c02060903011d0a050714060d050a060f0611 74
    0x18400541d40e120541064203203e0303625490740340205400c1d0184110901201c407503644601d40d5008040310b5a420b040b1014104000707040109003e41c490900405201440050740c9800c1510207654050741c0c2c807611014200c0003d0958040201d010701540703030020906c03649040c014020300c1a40d000d581080822841d0f07100454070001900100c00b4060004072041c030480b403180701d030b019500c00f00301405148551a91010320203e5008101c8000c40b80d07551403d0b40b034600341030056204900342c0e800c1440c241080c08030040d204004060700030703051550005060354680c0c021040d000f4600100d50003000440d0b075104143e801008280145000b150440c400515a58050402e0501c00d0f503055035143c0c40d58000b5030910610f5007004104a44c10354840019040100b00d401a0020010114000f07100f4441d0038100345081504035004803c13100d1070144ca28607261076400888580b81c40d422400034442c2d84401c0c00303034000c3c20309410145250019410004100c0c1d4801d44c0d8220781c0c807102041d039406624152052 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 225979280 1250 225978030 225978073
    0x822030c15210509070503030a0c120e0102060a05060607080d050403080a0209030c01030e030c0f0d092306091201050a0c11010501150f050409150e090f0303060d0507080106030b0108 80
    0x200442ca0354819145440c020358000075080030003031084401c001d8440c0002400c50b0460040c100005080303c00340c0c0c3c10300031840c0c8990500545410030740e2417040c04400003034803108000c020034210794075080030940646a500c11642c050390000c03180c544070242500d516015141c2501c0540000300d01c840070440303000b0710303208035942060002c0040141c0e090040040d4050200c0d01503800041c0414060048a480103001d43d0b4810b5100c0b002500c210402c44001816044040d00080303e03c24207580c0110115102d0340001440610031108c95032140f074040d0015140107400c070382162041d4280740501000c2e44003a04100b6000f143c80d2110101c00009900e41800c0f140248101a99070795150a038940480c0904200542400545031052400e91500501f0080e0f400610f820980ba140c40342041201407020f400b01034004d480140605102500c55000d00e81d030340000b60074544070f085101d1800c420400d041284000401c0d800703000340140781c0e8a0802101e45102481204203d01880311451303128a01c20f2002c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 225980530 1250 225979280 225979307
    0xc1107081c05040302120102030105011e02030417031b1006080c090c030c0d02031306051602070513060f121b0303080a1e0509060a0612020901030822030c15 69
    0x5107038041c001040071841c07562803800c007424400c08010110258603074040302100340040074005660b0354500400140f03071020200c54100d80340000f56101100c154044119411201c80c6000304a4071055114454150f101e0384203042160050616181c900140108802182c030122801c108040c503030355480d0540358a0100d190300d5006e00410009200c0f03940c13900143d038200401c070703501d141480080e045130002c980c819210201c500d00315805e200104403550107050307403091620640140c0c1c100d0620003e0740d42c2c0c00d1401000e10940c410205c03100160100c3d84180d0040035000a585c0c145a0784a46000d41d114140000b501ca294801c2c0001e40001d0340840c1d40d13030441c2d0b89a40d8060803075480c04c0684005040d00341040300f1801c0c0e0000d40d50101145409243e0080e6801c6010b007034207040c11a80c46044450070f90201e07c0c8000c65034071903c050380e01e814850303044a8000920f0340d500c0107080f0010f0102a0160b4507034a43d200f0300074020060051400c0340e0030695901054482d40083c00c81c0e01901c134141d0184c1c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 225981780 1250 225980530 225980533
    0x9150c0d020d0f021f020a0903050a05030c1e0607110111040f05190602120306130c0e190501140906070c0605030a0c05040b0405040b0409080406030b04050c030112080711130c110708 80
    0x100c5943d1722144e83c001d0054204038900048100c3c0c40c2c2d034500d41803002d8004e061380c090740f01240a0200030002c4c0708150300c9181440c0c501820341221140b00d80c40f0b140003010041801075881d2801c4a0360401c0d0490170100c810f040d002a80c5d5905c07848501540602400303110301500e4828050100f550140c09087c05840e00d0390000c240000c180d584002069100401203900035110802003000450785016400360581d0b144c03540d503c1d001500d0140700404140303858109427008035550802c0b0907600b092084900425800281e551000e1440118009100f4000c0c010903201d0078030000100254014051401680c12803028013440703001150480e114040ca004003000c00508100421007460154009024094050004030300315640740c6408409420982c811008a6160112200c55140c1442140e902040301020241154142040b4040c07074116150001d100c2640010250309200b400c0c0f81c0c5004400004000803411600e1018800c0600410350600c004921000d0070306000030804112617094448550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 225983030 1250 225981780 225981823
    0x403061109030a120c0f1a09070f18090b07020c210607050706091506080d020a1509051504120816210b06030903070215030c09150c0d020d0f02 63
    0xc83c0d4005500c82d0131000700c14081c1134944800022421140001120300034222425680704e25640001c3c000c2004090f400a0b4002c0d40080c800404001c1204041c3c41c003811f00401403031a0301e090710b0014a4482005001c03003040314100040c250b4001101600c6d09001c4c0c96540100c0304841e01c0710b0020400900c5000c1640200000481d1644210064030643c2d008102c0403880c14041c4d2503101d2042c00c08030071101134a40b0740600f03000c0c400c0c04100c0d07510ba007070041c070041c1141314494442c518181c0c0505031501403562078000d0303881030200c10000001400d00e40c2c1c0c0390000d642001c5c5088600f03c504890040c1c041021240052203d18a0850890405030f0136110321030a034403100c5420124118050701000e80c0d0782d4a07194000b01c7d44450015610813105c100003599207400500400010003110b401424018104004101c080c401c441d0640e4407451081e114200e410074102e86842c000c1c00b880300e50101c28403510700ca20000e1030380059030428900450f03d0b1610500b01d003680c100d031150395880c00c4109605540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 225984280 1250 225983030 225983033
    0xf030c06060319052a06210c070c12030903120305100b070308060409150608061038040e0f15030606010c02121c11060702070f03020f030c04110403061109030a 70
    0xc0c1414041d5006081c801c042080794040040c40d150051011a2450300b080020f10b140f1740e1f01c1e96981e47d001180341c01000e052000700c0c0d407103400081c0f1314042e8549200312a1a0b503000c0500074002180510780c4842040409a101500240144401c5940c026004014800040c2075031200007103d2400350156184038107648d0380030510000c0c0c001044c040303c07829040e100300508031009200341d030054005500a0f00707042c104484401d044001d00d4012848061000741001248482c00c2030132100408011007001c030b20303040c0c0e9070340100502480d4000c041c11f210500420980d0f400403088240700f10003100c2c00400c803146101c00c0c183d07100021589507003c2481e01020401516040703031030300c00300e11a0104030303414800c0d006514040600014200c1011500201046074000000d101c4141e100003907100400c2c80e00c0c5071100001e150b8920b80310181c0588080c0040d013a10351018031410b01d0720800588140b2001050130503540c6261310900c011f0311810315100011001c1820481144d01000d401002061502c410703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 225985530 1250 225984280 225984313
    0x20105060f0d030c170a020a170a020a03080907080d0507020103200307030b0301060f0308250c0302040c1101110a09060206100b090121020702040c05120a020307020f030c0606031905 80
    0x520601780c64210803c113000d4480500c401c000c00310228183d010303101402c0c0034940803da901d076084c5c00c201c080d007060014010a550004119106507003514180040751907140000741484401c1c2c000012a008041d80900082c0d001070042c46010b200fa6804c00c5507002808020444294945100040b01010004502e40e82e20a40200c11001401800020a150355030403a161005503544100c0f14114003280c01400702840800081d0200804c110b034141e5900c3c25910411051140d000003403045955038821210144a400c402e00d154140100810180380e22030b491003100e0300a8020400090140e8402040007440442c2850040100414600c0c0c1242842a64003080d002814002c1c1003050516480c200720240c6040032202d07140e04000141d03945142e0041c802569414440784040c0502000282c0c1900c140300b0f09150b100d46880c0300140c40c0c0e190044100e0030980d0b0380110300014400030034001104180465014040c0c0c0741101260100c3c01040381d160107840c41c081000e006a04500401d40c1020034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 225986780 1250 225985530 225985547
    0xf020f1f020c151806040f02060a0302040806090c0a08010b09180a0c030623090d080a060513060f080a05030a0f0203090d0b0609070e0d021203120c0307020105060f0d03 74
    0x900098200b007000c0d00305500d41402c20004920000d4000f060040049a1a0030307080f803007000e08083d01142c9440d0319100c0c4902d65254009008800c0090705a1300c0750b2007581900d0140c00068160341640c00e092100310390351250300c102c1a01c140400800042c2188051103082c0f4944806000341030140d855200d08102244540c0100a071402a00d0720640003668051400c0e016500c80e0b2000125060400c072203080ca1501c03240c10900b0400c64006001e42544e0024003002c10030340c2843c2000503590341c842600080c02c1281e0080c0c1c0c004408a4034601444256000641912112207184151b542d4030001c51fa03607010740c000c0c007a040390810040b000c1d80ea40329020091105c0b002c5d004503490030b41c0060204a2481200d03200b40d90701e00701c0d041840f050307103840007605800c0891071800c40207903460200002d083c6424004002e1048881c20b044082c6448c0520a0702c001c1e42400c10b01e9151441c0a4614603070316802190400019441c00d03001602c1890200482d040c00c0c0400741c011004142c03541e40c1958002e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 225988030 1250 225986780 225986833
    0x3040606030507170f01063b1302030c04060f0509041b0303120b04090213090f05060f01050306010b071a0a020d060305100b010512070e060c03030708070f020f 70
    0x140c40e180c0100104a08001200080216000040141c443c6481641c180710443c1854100d59041c290100481c2d482028015120890b14400d1203501d40d080c007218007a1141901c200070390807104030801050b010b02c001182880c50080e8140c44801c1841e07000c10003190321900036619a040321020622403401c140343c030654841e108140301000b01c146241c5540d0380c20401d81c03040b40020381482c0c40300c2608640d402120071100c400d0b541401f4400709a4002414564502c0f1031520044d50b40c0500420710003200359003600207030071005840f40c41c10541d48218460f035003400b40714028420500001180d0310400c0454104540101c1c480400c3c40c1c01280d40a100f103130240c07110350703010340a120602c404021480391700000d500c02e5008146580c05610b01c1c800b9120020380560621030148802c522610f4004490355004129103406207003440c0f03541c00070f001c900548409100700e21012081041c526001030341207002c2c42098650000d4103080b0704040341d036418094140320745500024080d41080c4844003a08407180d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 225989280 1250 225988030 225988043
    0x30d0503060d0b0903040f1409010614040308070c0e060d08070b3c1303020705090c0f070f06110702010203180105160c21020306011401090509090a02090c09150304 72
    0x1814161684507403034006844c40342c090303000010100320100502c0c00c0c00008003125a4041079800d0320400140341782d10f0510521040c04010f02c111000c0401800c1102c014680c007540d51500c400050501142418240c000e010000c1105004907102e85021500102220340c0030131036616000685d070b51400e105a0103002c0d503421800443c503001c031000e528941d0018014601341c56640c050546d124070300c5c4061000d0101c260b040c08507000c4a0109a010496100343c039000d030b80414090b101d031034801500d4410070040c48010313034003c292032041002c524540211603014140500045610000d0308a9610811000901603441040084103002c802c0b9a510403059050502c1420840fa4504c85200c801e2212011a14503080200600071a881600355504446107035030414902001540403d58544040c05848030354161080044440d82c801c005400140c28090011241c50500c495401d0303a400305108104d220b10304040c0020450501c042c150360011100034504030b041c11803000d244100d5400580140c502 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 225990530 1250 225989280 225989299
    0x30c0602090603090d03050105010e0d1b120309060e03150f0612031804060807050105070b0c0c07060c0213050c04120203030d0c0f180305120a020102090d030302040f050f030d050306 80
    0x81d915034000d144284004d0000d8a8035071031540c2d0080803207005800c95814800d10f80b5008680303454000000500a5009111b203046000018020b10b907201d030350348181c40c5503010500120400d9441007020040310907688032424040340c1c0300304140c1c4940400070021030b04103120000546000301c8000c000d030070540103400c02c030408404044050031980452122000071540d4000c031100760070540300c0d40d0014810a0060307c00141008002803142c4a1400041d0040e5801004540c09114041c00c5400d9205550210b40c3c0352651080041c00c40c2849030710a80c45000c05126003c010700f864064644150204aa590301d00790421011100c0d15485001c1660544020b21801800d1036061150300f0f5403000071303100c0c00c0e810f00d100c1000a200309080c001d04900b580201e602040040c01c005503c000e9030000703045c1785482c2c4442c800b0407802405400c90103588041000c03841020700d81c040d8010019114543e0122040c1915030742480280004501d00e5500b6510502000e0300691140020716046070b802440b0307140c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 225991780 1250 225990530 225990547
    0xa050c01060b04051003020403020303091009080f011e05160809070b0409090b0c070f0611071506090f060b0d0c11030f2224180801090c08010b0904030c0602 69
    0x21a8156040b41074058030000d4244554034020020b101040c981e0328007980f5050a540c0031940720700541e82c0d07880c000c844043c06003c5082c0512000809090b5600c2210040120f40b41514081c00380c8800c2804051440380b4688410340036405011b1181c001c5000464120700e440000700ca0840c002080c40480340a00440030600d1502200204024000c3e18801b24824020b03060810701010050496590f062040141c0030008a000001d00d5201d500000300150fa1003450210707450707600c180c5400900c610290b900030082c041c0c0c0d41d8800f0341035420f034032420801d24101d040982c00721b4205010f04d076400c1800b4020558800903031b0708820b0200100380740c0440244a026203262454000c0b0204903d0040c0108071000d04264090700021000840c040c10464246441d0b007020800400a800d00d80c5005540310704e100c3c0c2030007955002080d0b0541d550110700640d44042042c002d02a10808491002d4000307800141e413441401803206001e401410751011351916517081c0d41c3c0354007042048440c83e4090180d8034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 225993030 1250 225991780 225991783
    0x31a061209120406090e060a0303121802060f180901050a0e090705030a080301090f061a1803060108010b03060604051018140a0c0806040e060106030b0a0305060103080a0906030b150a050c 82
    0x20003103a10303028400c03810001800c05046000705240d0140c141c8c11010004250b000061010309a01c1d414001040c600c2218441e00086c01c600d070194000c24002020100310350b4080081055001c40800818519014030400411250030700c076495005140c80028000c81c00740c02642c0390010002411100029079400102c1e0804621034016550b141c0040010480d880160081000005503e24104015410708031001800c1180d60801000078502080140030700024200181e022a4010101d400715a51042e0550280080c840035074040d00402010034076504060180f1030103000c02a4281c10043e00f4002000038007680040419030203512400c021034100c2c1c16902c1c03907000d03807100c0c0c06c00b00390f510f410b92002d000c1ca5400740c40b80340640c4c0f5105200c1d1010801143c0103054030501c1ca0b011562010b600e0004e08074009581018109000718800003003045800001080c0309480c1d500d500340203d80d80c3d82e0075021580e1601d186074000c08405007000805200c40c0003800c0d0000c003803d11908014a005075103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 225994280 1250 225993030 225993037
    0xc090307032909010504050d05162301060b07050d0318081207030c020309150d0e16090506030303160e062a07150c020d0c030b1303031a06120912 64
    0x80c410303560700c0452218040c0b9010349555200783e84800074000c2e806c1654550744c2d03880d1550158002c000000c43c258040681500c1000e03081e981045400c400c0041840398100f130a0701e03402074080550701e0000300007440c50440003501c1444c1d4125001c0c003d0303e800403400f540a804840c3d00500341c0006111920001360022001d0020054031246c404031030b190502c0c0103001c03914160003034010b6500c10f00c00403414ac1c1c0d821000e60300489040140c0e07a202c160a42a00c0050601c046c40b8550318041d0b8003010308001217080c0d4082c00c4410740e103400e200c0d030345500d001d058507440243c815448800007055080700c2c0c14080c941001c00b00d10080c0203140390400080440800840c0103080c0c1c031f08c41850f00011502103a00300000c401605034068110b42d0381074490800341030034900000003406818000a68400d1005002c031003c0159048421001d00745440b201c5003d000d42140c1d403c8022929180707810041c0012030f008644c0c6800c026240c58507041205e00401d04000005140d6400d1340b00702c0422020440440d40607 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 225995530 1250 225994280 225994313
    0x4020d0e0f0102250803150406090c180608010b071e0b18160f06080a150803030703050a050721060314030c01141510050403052a0306040201080c09030703 68
    0x41e160b01c01403807980e85811300384012011070039821110201141c003d01c1166000191040e201801c1075200300858042d202e503034804e100c04c0d8544000501c2e8a40c202964050000d21600c50005140d21140c00303940e06c210a0081d00302201c010720201001640070061f0f5041d4070403400104a244003075541d00b046544044403070800d000c030007205180d0302000c104001a01801c10581d0282182d0400d0b8006d4003406041c403810003003146c004003288480e0b0362580001e40f10a41c4088080308552101082c42c2c2e030b0b80c8242c0312000007130b02e40000110300a845204981c020b02c8240e803079980141c0c4136000c4400b84c6002184128115903a680c00100003030140b451102c420030024041d40c0c9482e00310710713207608403820621147e10074850304ac00c003e00740d0315810451644880c00c41c0d0300c0040c55480324007251107001d9a00014454400c207000300b0105403100034520000c4c4025a00f601207240e4101c28541c5139807094400078086031150b0b020855002c1010041c00c0207040c0038046030351040c0d90340c032100c4031700450341903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 225996780 1250 225995530 225995533
    0x30f06020910030911040902060c0a0309150e030a0609030e040f0608010e0c0d1b090606030b0f0d050c0103180b0a050402100c080a051809100504050601180504020d0e0f 74
    0x541007941c2c10581402c0ea01421a810b04002c0f1111944541c80741d566140c19143c440c40e69090030100315601c0005980c200c142400483c0c012820615000c0c1c0150268051300d4085070458041110940c491107400f0300d0484040d01802d050350aa85d60740c0d0103094007031012400d2210400041c0e42503120f511032020090300780307640442c9a524040185007183ca40031028030807a0450250301c10592946500c103503501e5440301e000356003206104200c682080407038000120079810020f002920030340c51b03041689801030032102c0e40704074a016804c226076840d0700703240240982c01c00805a9000d6000e41e02030b082000034620712071140c038440c1e80c2e142441002210281e442658447c140b0096042000040614840074140000c01903034a4444000c1c42c02211100403c100c000120445031380c05a000d00341d141c2001410b507504600307010740242101c403228000d03140603d140100098480d84a0201e0391917107201100c043c440c107428042801b0180d400b440300141020b4503000d182d24081c5d000c003c00c0d0004c0140700c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 225998030 1250 225996780 225996787
    0x225080124140315060f0306150913050c040c02010f0f0906150501020a0611190519050301260c060a170604141503011b0c1a0705120c04030f0602 64
    0x482580c40502503045840780d5003102c900800580c0340026480078814500080c00000d50f6000d00258240518010744c1c0e405001e074209114800a640360b041405103802c036000342150b550000c100c105a06440350191040c4e215100a1307030355041ca81d2181d04050b9042c40046075940310652900c06032040c920103110103554503040082440318900c500304800c1c4d00c1c10940e40d60f691034100005c2d81e844025601a02c126940c071208a44503150600f200c900070b040181c9904451503141c001342041d00a1900e2440c200346400000c10701030700c150100c0b41030700d420760641e061102c01c94401c00c00740c1103600b1090b41d81d48a81104034920350340d20030103800103003141e60b111403047c0390300d50400c1041d04014203110700442c18044100d801100798240a5030050350f101d4501c46030130180001074050900e00c1000902c2407003010550045a5103e20803c4d141c1c0c0c0103400c540c6e81076081c03140504600c8800c42c0c0e1000000c10a115035004445a034040071703000b000c0d005003181420f44030781365140e82801070941181c0c3c0c20b5000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 225999280 1250 225998030 225998081
    0x132301022802133305010203070321050a1b0c02010f1b060203010b032202130207050102130303051b0f0a0807050f0601060309060501060e0916170f040c051002250801 73
    0x240d0204010341c4807061a6071081c0e05d0100080d42d280104000202408038180d0f044040c4031a0404d0080c5d2041c8410b000e001508223041c1030300041c2006100b9009458040c1e0034000c2841c0960302403940141d041c0d46201c441c0f0f903103a41c110f98100d0700c0c08881a215a00c0368860740030402500255000c1c1c400859940e6503410102031260304411820080c01d6413444c0c002c20303a409651024082d40101c1c0050748090394580042c503042c2d00a108030003a450040c22090700110525500c000903007810100043d002081a01500c4100ea803a03842010f00304041e40720481607000103c08001400956104508481c558901c2e0b520040c04c01c00d0903003000380001e584801c1326041c0000f40c003d80e401442e0a00301000d80c0001c00020400340d800c02030488000020080e0501d148034071032000e0728010740c00d00b4244c0109041600d40c03104520b00945007a1307092115404086920b1405002c444007124103a001030402d0b001409002c00c2a0460b000200790f030201030305000680c0744c1c0038020340c600016240010b91040555 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 226000530 1250 225999280 225999341
    0xb0a14090916060804080d020a030507030f06120807050115080307031e1e050d020d1508010209010503160e060f13080721050313230102280213 63
    0x4150140715445001486050b1151001c0c0c1d0007540d01600d0a04400ea0321030402c041548034030300008403201d2000030701804c250b5055100500072500c66409202020000b25241c0644019000f044440d000b032480680004041c10000c117074440c071400c000f01d09028443c00c0c403084220700380c1c0201459040003032104105175101c0351500c0050300800c008841c070001d030200245011700011820219510744040e21003068050410382e0800b00000406550b101c07070f07090030a03000d004d0441000a07103000c00000811204018000e0b0b40329500180e440c1411a036501070090a00032007100f10500380405900c0c80003940d1141401402d41203441c2c82215652211032040c003648141c950301c903121941007850f0620400350344119000e9503e42040110345000d95078200340d4158451001d00c41c08141d2000d40c002100d0103c1c8a02d0020b0605a60082040d5003000005985a0704d03101c0c404131351070b00031058883c104006010000c0e422400035020b00045200828900200c8000c081c82d00e048001e03011101600416 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 226001780 1250 226000530 226000549
    0xd0e010e0a1a01061b15020c0313050603070e0d0c08100207030e03070b0301062f0a03080a050c0d0c02030706090b06030d170109020c0a150218060c06010306020d0b0a14 74
    0x3440030482c0c010350b2402000910b08014082e86001c0c942c0c010540c04140012858103407000790036031038210b545260b030044c940d039258044609180c0f0315a0000e800a40c81c6000c00c162440345c1707115250000c810720403404000000b51100b404903076280400c4030116040000f00010201c4103421100140d030f800307040c20068441c510910f2418480c0d805140c0c140940e001440540e4119103880c01e042c51482c4036041384c4120504000072071001e03d048440c1c03e40744004009800c01402e4041d0301c80029645661a1903c20764404488116040c00100026280740e6580d501201c03403e000c61069030f041c000030b07554200c140d8505240c25500381c402c02003442090701e004c1c049685500c5040c00c020300070070f02458020340c140c0720520805491a43c045003a9800640070b000c5101c03410350000460041c001c000944100075080418a1100e040c1c41a0364904141044804c03202e204078179900030301143e8655500c0c0c0000e50701a11400354000d4980d0080c40494490060348400380c89401152584460000305200d01b200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 226003030 1250 226001780 226001813
    0xd03060513090320100504080307111b10170f10230d03180609080705010912060b010207052e0f08070c0c05060703210614060d0e010e0a 60
    0x2441c2081100010b500152041d0750a030f64551412104440d013894541491404052013005908000411041184500045204101b541c944000e1582d1003554a9a1800188201000108594103443c0c0c00e1402c202c011104110503c0c1080112680a40280b1480800d41360b00700801e44c150240014004c1c19001d40020b40110000312090740c0b40c1101c05051040e0503915a401001c49880c0d0f40c0a241c8100040303c899403448110710000356a5a0004044102c0c0d0312400c101400340d038102094541c804c0113030004482c076601600603d8a0301d500c0300c0c401000080c4c0170034190301c1580030014880e158000341c00c50819644042018140c5000140c01d40c41c040688003a0412481f82c040054854001900c5504000f840ca0051000f07d40e5242088481241c0c0c0c204980c803e074042140030402d41c2c091851460640400c0c1030054907a01c140c0250f080e074401d4058503c4403080c2c2d018100350760800704080d007444110a0f07400301307025404203040c900710b484203118030704190000280e160030f0140200c015070718103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 226004280 1250 226003030 226003069
    0xa0306080609071403011512030306050405161d04110a17010b070b040303060e0f15010c05101a1c02090c0909070e0d050106091b030603121407050d030605 68
    0xb850600070700c6495140a02518102031000959240c2c544c0702507000100d403940d904031000e05e154603403030203400805401700100c0000303040800102c0c5c01c1c01e15000b5180503880c0141005150325100b04192004503203040480b1688181d4103500c11a541c450040400404a00020590310207044e2802401c4215107040d140b20020305000422192100740211051160096001000750301d0310b1030304501400d81907121072555401002406032140006040c180264415400c401000010100550380c0c05070f141006071458000843c5944603103199003082c0b104d220b00e1459860100d448400240d00c441c0340e92040c1030401345a030710b640210704090124581041800101c6410701c00803c00043d92660018046010884044005000c1e600c450803c00c5070a54050008d004070380c0c460300c4d2100180318862000c4050640950825032041c003a10500b01940e8120140c00100031500c0e81c2900d106140d03889d0005c4c83c41c020820200442c009005441c1303200f2081d40c020403038034a40710030400314004c20080503142c3d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 226005530 1250 226004280 226004293
    0xa06060203090d0f080c100204050f010e010e060d0b06030405060702120304050a0305090112050f0415141605040302100906030b04020414010e06040914010801050f1006110a06020a050a030608 84
    0xb507440d0314580843c0c0b640000284c45400e080c0c079091110703000718071180c40390384100c04c4012a003618a402900030341c1c000f0b50304402190210340044a8520820300c1c0d95001c24404441c131200c0d0705008000307081015a071391000c2440c0c1e1030500407441c103620894058a05422050038881040d80c144100c1840001c812601ca04506254862a4443d56500c00007030a200000030001942d9002e0012030301001180107041203e4540308180038041082124111402c0c0c03080314a03030106204a2040c02c1308100a074581c0200ca64949400740100c02210b000f090a02c0000e000000059441c06000034005100c0d5a8032070311207140c603001174162220096401c1c4502e005000501c124131b0100e0030100c800500340f0305003e0341e244070b10210710907100e1a0032440300780d8103281c140308506034001d542034100e030f400a0082000d50340705101404000001d90b200c05529414240c00c10040303100350a001d20940212044d40c031241e05c1741d0395801c12a44071045101c04920007082c2c90f00f0482c0c26224480003070910758080d0ac074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 226006780 1250 226005530 226005547
    0x60a0c020a05042007050c0a030f060e1603111f020a1b0302090a020d0f020406030902090105040612020907020c1c02031614010f030603080d051902070f08090112090305030a06060203 80
    0xd84103100480040f00c5008145c030018010200b051a55402000d4030041c40c007074170707400d2502c0c9580d40c240c2d017624028103111610107001c00020303441c1062140b181141100c20304640c1c0d202030702030301030268560016034412880300340300007040c1d00c14160619400510540129143c00c040080050b603508070162170800381080540c445410003075220600d11001640d170240070450400601c400b6a58202c4280b01190204445d41c0660104a031075008540100c03003070381da440401083d50054029401c0c01c2c1c0c0850f4800006007410540305400c4255801031300d00300d01c04d04021910380c1d1302d05801e213aa40503802e0042c500754201803124558803511611007406140c289040d015a0259400d041410000c40621102019100340c2c03003c40a16070007100240d54100310765580b406001c068904001481149200815080c4680300300d483e1507600082070f40100300a038170381e155030380c00416001c0e05001c3c050b0560010709449214113010a13201c0e4a400d5280e05181020f81c0442302c43d60000000e540c02080545c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 226008030 1250 226006780 226006811
    0x60503100203160c031808070f0b0301150f020a0f0614011401091403031303080c0601050a061403040c260c030a05280b0702070501120204060806010305040809060a0c020a0504 77
    0x14070942e000d00300000440300340d26041b5080c2107148507081d5142d11084011503010b20100d10b110496880001c0c464482e903c45500c890144000c0c0300b41e04460303181200e010401d90041405449480720360050701c1441840d0b4464202d543e0140c942100c110342e6800c1072040e0b03074801c0b0054501404002c800481d03600c15910000e042c0c031104d0302450f510501d00060818440d60100120b91502d51190b000b00300055692030002ea442d0464102030740c07680070310310000c601810031004880480b14265503515140d10980341c501c00d10f6001800554151981041c0454a0240406180322201c210501c4500301c082d0342d1b401c5401c202da00d80190b031080d081080c6410100f1400540070900a0b030166a000440c400705140d0020b040000d0402041802d10504101101ea00800c1550486400380c8448071003400624440301203200d9406201d001c60b40c004003184c140d501c00d5102d0342e880f1b0f110f4143e4510340034500c000102150001050000010310801d030000440c1002410303e401080142c400388184c94481c0c001c0c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 226009280 1250 226008030 226008061
    0x3030e0106060921171239030c0d020c060405160f051e0307060f020d022802030f10020405040b10050a0c050705150a0216060906030911030d03060503100203 69
    0xa01ea0540c0d10b090070113100760601d2020102054066540e41e1305030302110741c16000411255112481c7e94401034840e0b100550b44e40b003002140c40300030003201b03501205a034107650300060100f0040c207800317100c036185420341440145042d5080b50001d05c92481c00340f40092a18104903644078070044445000c018940c0ca11a0000c01d40d00c0c00c42c0c02014110059031050440800c8000746035040c801c1102c00980305411103002105800313242d0950340e2800c004207069079a01c0070100740c1210115a51490b81c04219440ca80c440d015100506444c0300111401030103103404003401c00c11040503030000e0300f0007082c64a0320074400700b10000d0b14151040100040090114003904030103200f4403181ca0a50800c03c201403000380060138000385a0b4902030110803100100b0381001e4142c6d0013520501203c14490b010b1822128100d4009507140f408107814514100e001d4024250100c5090040024507912070b6410302015040c48145d40d03000450b00e00d010100340c0b07080402c8150b10b21061040050040740240d00400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 226010530 1250 226009280 226009319
    0x1103070b0427060e04020901090509060411030c0907050301150c051915020f032e05060901050706020d240308030f0c090904050109061a030a0f0311060403030e01060609 74
    0x111035003124681e900078240ba060350150500c441c9031182c04621120526034884c080c6009895003e8540e8075001c0c0c4800310b50080e1200f18030f0b544010b00103000143d100003016044c040c050140d6920004940c08200000301c240e0741d00f07000c00d00210040c802014100c00050140f403051900c0c40c6600c5064840c00d4489180760614004031f42581035101c00d2041c9003400b201c0c60004003800b1541c603040141011003a82003038a0281d608014841d000c4c21081448011180301424004690704141c81d180411002d98042c03d03501c0d045c460b0621903503001c2110351000d0004be01c0f50034400309082000290382c200360000d5a0f40500c100940b80d40070f02c0480e01007420382c3d92020007810003052035200d0070090b50490180d40011a805980c3b181001b041240c1900950601440b481c01405002c808150620300704d10f140401c0e0f03400d40d025904c841d000c6030814428121042c040d080080403001c0120304507040c010101c401b82c02003500d03942041b8100ea024464140200003a1800c65251418070102c98070801c00d140a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 226011780 1250 226010530 226010549
    0xf0c0a0e1b0d0203010302090a060e0a0902030f07090b0307270506010309021e12010209180c04030b0412090603050c0d09021207090b1807020a0209091603030503041103070b04 77
    0xa1030000c0701c41030101e0394036035203514680703442411500300060342c0240000c0f0f00845810300456605840e900803c2c06941d0182c480c041c540d952001c81c50000c06805209a030315109403050701989001c00d012100203048420303130200302c10048006141c41c14003140c0c45a000c810000b1794840c150110314100680311a403910707000c28140c40d101c0049000e8038440ea0060350042d19203003026803139885400c500811000988401109841c8614824200c0c0603800d100c3d500603000100c0400110303442c0245075403000440d0303100303410540c594840710440712048070200c410300039040e40e503070809400c000400b004200d586428444c0b40b45c110110506401000c002900752500c650103030301155209040d170f0349090308a0003100c80b155560080d42010781500b500c0d10307000b08002290b60240034071140f540c503c04d2034540c00918100c0791aa081c8081d00e0343c014081c0078180100307000b10301011050402c42000354082d030741d40c685070700707050504c4a01d00c1c0c052810148030b54800d9004201412909007960211060b040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 226013030 1250 226011780 226011809
    0xb090102091503131722090e0705010e061303140c1207050d02100c0b0f0709080321090f030f0304110d030c1203020c030408031209120702040903090e10080f0c0a 71
    0xf882980399000340d800041c50301140882c03006c800000780510f00d049582ca003a05200c0d1445010300300b0744138002d9000f41800208030700c613130400302d040c1100240b403054094241040700541d241c583c984040d69400701c00c081c0c0d412420b1007002c00d190054180020b10b000802916420f443c090018030703e110302c0d400080c0607000f0f41c039030780400a00821042000641024403c041443c00281d16183c02d071044603003801141c030b2101c021640850010035510ba0070b200501c41d508015030700c40c40f4200760400070300c80f010038031608451b005030b0003052019202100c280c145141d100e0810f881c001040e02810720566010300b103d860030001190707024032480c04454202180c1d0309102a40c0300114068412290540031074480050700003107018001009204111081c1440d80710b42c0c03514800d06444141d182400b01512030107004100241c94250702c02e1032850310030306049420b66070700c0c021004084021541c200f40e17480b02c280200400c3d2001d010020074038404074040e00440c00031600180d4840102c0c003603249030509d8417 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 226014280 1250 226013030 226013063
    0x10091d2404110105091002010603020a0909030905060706090203030408070302090f1e072f0f031204151b0c060507020c03030a030b0d08070b04150605010507060203040f0b09010209150313 82
    0x200300712445c0c5403000e81408261054408064080e001c42d1004030700078904900002511142413045c008120390555401c02010b180204102480d00895001e0780c40d580c5e02d010b80001a50100010700040904c80e025002c00c2c1c0c07660042182601d00140070540d1003450f0b07410401d440111045541c44034142e00401c0e03403a07445580f02191036008954016a9400300c802c59441c0b4446a2022a004100300c4030071102d1201400d41216224001c150241d440f0400104c0070800281c03003d0300481219071130f420700048a6450010303584140450035182408241d00c0c910301002d21280303000c2d2640c8445140014406402c5440c003003960f903c601e46040d0b082640d258000704a0f55540c00d8a07142141c1c01c400a6604c410741d50a05102002094900310742131003c000780f070041a03a40f4010f4100f11030050b1901410841d1545814010354001081200d503e01401141d900050040e401c50340903071810000161248203610078000c01c140003845e401100e170424810840040151181c0c9985554081d0402c00d0241c40d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 226015530 1250 226014280 226014287
    0x30e01020f0306040c0c060c1d0406060801061b06021323090c0705030d1a01020706020c060d0c02010e1c0905031209040e0304030807030c02010806091e10091d24041101 74
    0x600034400c508018881e07200d9580400c804616040b1a000e502581d10340402b00002c0710507030310030000440c91704001005001e00070900200780d00552030300e9440c41203581d6960f0049034404c00c80c0c030200a0008001348101120705141520901c00310064000300303a02c201c00980f4110004000c1e040d1145d0018154003046803d00503260110390516060120110306200025a0081480c1040c0148100d10000400c13a20006001d28503036070281c1694a000b004609250151030350061800540d0b40319a40001c0d500010007030107040c9960f001980c406004c0780c0400802e09845680310030300c03e900c01d040e0409040c030110202c8100c8401144c000800b200c0000a440c2940160f51001e003243c0c40105041d002c0c50b810601600565100b680c4144c1c0c0f41d5500707000c026a8040030b0f564016607605518170460034403000300801e504035415020056000f6035030960704003a40c01d00c0202c03603010b00e4441104100c9603010803462910420401191200301400d90806a811000600103005840780c11581c9410342d01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 226016780 1250 226015530 226015547
    0xa110915060319020c0102120f1603020d020405030a030905013e0f0604060e0c0405150409031806020304090b0105070314071a0f04030206010b03060d0b06060f19030e01020f0306040c 80
    0x7441411340d251040005114001e40084051078452801d901c0041c0c2100c0c004581c85115614583c04141c100c0ca50030303011030007500100c14140542d07500708000f081036a0100300034214580302c0d0b034076400300740c1c282000180746210542c50640850840b440400c2e103d000c08000003104250400000104038040c464285008450040354105010704000c0c00180003142d0092000c0d90310441c111a028102002404120307641200c04141c98504005110228502900320281d464024581007001d5281c0c040305488038800c550040e80940e000090820410285000d80550582c09003840740c1400203584011301007202030521219594000200d8070308000a602c00c0d200300c42080e5a07200514030b82880a0103544100303607000d07800b5100d00800024490754000c220713481240007030100181d1140b02c0c0d4502c0c1c1402805071500358449410700290849100d5400500708402c1e102c52140b90002c881080581182e010501a080c036900401490b0700c42e02c02c1d402202e4000c0b000743c0c0c0005403490b02420880e91041c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 226018030 1250 226016780 226016821
    0x100c0f0c08040b0c03030103110a03230c030319020c180f0703060b0d0204080c15040b09010504091b20070311040b0d05010501150c021003020906070b07020a1109150603 74
    0x7807011079800201c1300d00001540c10399115100101b078220720328003004407400c04e521005050038040b15680700003100c1500e0034034243c0850002c40703c90483c9400000d04540042400c0401c0d808024298010203504100800c06020142d48400800c4d00c011150a41904028040800010f156010407000e0f482036010304000c1004412280c0c903103094000f968041c1d0b0041c400da42c0b891092408081c114074126401d1a8200b803000d07810380c0342134034004180d40c21740c004a0409041c09014480010fa00c03c2e94001e92030301d80f616241c040303280e81c0410300241c030301620101184810324203c4548a030303548000030310905236904060b0342c00d404001c4038006400b60044481244e08000070035003603010004150002c070706845842000c0207522081c50421240440515030295006d4240160412100c1c069402070a81401c007521207450200e0544590381080c0080c0c440704d005a100c0ca4920050108000c07200906100c116541185401c0407070440301f0000c00410038501c101400000714510700d450780c3c103031100070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 226019280 1250 226018030 226018049
    0x120105010b03010f090c02060103110f06160c060c080304061808120f060102030c0703020d08070b041a06180a0e0304080f060109051b0703080408130b0a02100c0f0c0804 74
    0x1036849205098564000384100c10070364144010124682c8594064440c41401d9640245083c0e031950311481c040c1c3c5081031b901500096082000201e03610f44200800b400d000d90018420105214900007942c40d08591000d000c00c070600c1004000180c490048079007080d00450041803090103048071006402d0040c6000340070740e10010302c03240d444d016005028071400b44229101c0150b95560f00685c2c8900ca5041c51684039000f1400a000529200503400040c6020303c04032820154a07954201c2000b509650564000b103c21000c0041081898410740d40200d041c2c4201c2c140d00c0380642406081080a00001409905e480030342e03c50b040c0800548009104400448401d00c0c031503100f1380d403603200038091065518180340004c1c1080c040601940b0051009412079417404542d038900301c40c1d0702c0c00a8000c6403040760822941680340034102141d8090114908810794410400c0e01c06407030004140d6401050034200101e19509030340009403411407203007a00300050380c40345d40d140c6058948595000744001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 226020530 1250 226019280 226019291
    0x3020c0709052d0610050c25030c0504061406180405070e030f2b03110a0f120603021e01110a120f051e0a0e0a0602030a1b08030a09021201 61
    0x500a4103088504031624114200401000e0414000b07903002c070840c1c0c1d04d5080000181c5070340841e445140100349106034501078546280d0b185005003600f4203442c0703060400c860760b40c01c00c3c03041c0200c903100800104005c03201000000c3c500842c0440d000c4a41284520030b10002c01c00284000305141000c1402c01c000b0000c008900e04260301500c1c2c9008030380f02c28040d00c92a00c0043c1441c0340040c140704030848070601c03031601c40f054000109149040d2a950020140c482c0b40301041801144007a00c0301035059110707a404040e00010007441c0f241a05204422641007440c00c00150302d03000c00d01c2d040014400d50003000000d08500503150074980f41c180a08034414a0b0b007a100b4040440c001904020b643d40d60084c0b20102000c0c01c407941c1c0220441c600b00404048441e00c104041a40289030007811414081d5140000800044da0301545510038405608006501030401e40c0c0008003000070702c02d40b00000d80740c01c0c541d103c903a150b000082880d44660354624072032042d582e4031801d0786400e00c0050002e010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 226021780 1250 226020530 226020541
    0x30f0504060615090b07020f030f03030a091a070f030509011103090d0908030a090603090c030f0c090f140f040c0f0b090310090209060d1b0618090207020108040303020c070905 77
    0xc02c2075208840a20140c00c0e1030203821445501c2e9101180c11000f202c0341018a15000c000758a8080c140b010383c94840c840095001d69414000340d40300d0084c071200001d455425042c8840c0400a0301564680e113500a02040740882c0c101c070340c005140c00d05290000301d6594130a2254010400184041d00000c1b000c01001014a000a803500c1b00b291690b60b214004c0ea514191140e43e401400c0d10360300030840f8440240411351190340400000c50184c2900e00171560340780c0307a0581044400c1425078201c0010303801808131156a004998000307076442810003401e1020901c0800c07143c809006c0c40f4081c072400010405201c0302c44040000b0701051031400550301d43d100540040b40e40400c200300e019020b07006601000f0201441a5003441780c02400c54407240d81c0d82020001088188503080380c1a46440d40d81007114248400103402400c5262103102003c0303505600511426825480000054010019080103036442640a40c0047d0f05080141c0c0341d1403000245c1d0700300040c40d0040849607103007500304003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 226023030 1250 226021780 226021793
    0xc050705030a0f0c0602011103040b04050c06030a020304060b0109060f030f0608030c03030907093605010203070908060a0516050f04030f030c030305060901080601060507020d140604140606010210020a030f0504 92
    0x2c030051042c4e9404007000c0c1d07905d0040e400c0e950800307126540f0560a00004000c1142e000724544e103d8401c0d400c0d241c8104401c4005a0590010b031103407800d00741d0120800003000250300c5076109580090900c00342003494488014000320313010510101305612039003c0c800d044801e8000101401c0f006c0181d0351281018041c4a60325002190101e031540720f007000002c0c1d201e400740306000e124407182c01c0c4034403440c01030034404150818541000c800000c03848071250100b10284003450140607650b031180c5495103001d9065140060243c07401520501e41028841252000d60b07208040c0c50880c01c149856101e00740401126005a40c00030344150f052280706410181c0c400c07601c00a944c400c4e24108040e444481c240b01d03180e0004d00a900441d4040340041c0103050046018101d00d41c40142050101c845503541d841c02070341d1494100c041a40a102400200107000c00a05c4a01035118028030091030b200300001e58480420309841c0c900c3e0360025680c20039600c243c104455a11500740280400d007003524146 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 226024280 1250 226023030 226023053
    0x902220905060a090320160b0a02210301031211060c091c0507090b040e01060902090102120a1e1707020a02030d03060302010507080f1209010e0c040c08070c050705030a 74
    0x3155070303015520000d4451046403160354049501980ca8480085045403205e116a44824480c0c2652081c00d01094502d42c04070388640c007800300500c04c0e03900d8a5013503901900d005012011800c1106101d0343c4c11883d811360505a0b41146c2c1c1200b61101c032203c50142c10348101c02c0c0c40407990700b036002c1c0c1420072104546007401480b40050640b80e0070b1701100b1100d600c000407919900000d19980101c001000160003d0b0007180034400010b00024024140c41c505d80c1c2114003d40c044048a90081080e45007584c0505c595050741040c00000d40c5001c29607034000b8110700580806803816008c0c0b80c80740c04094461001060442c00b624800c40071810500800f0b941e4080c0e05000b24800d2007000640740202d0f1181c0280c10403240e060719440c5c1042c4184d9074040190300311002e4062210420702c00e03080d02401e001d85090041c81d4500001030199100000b081c144000481076901581c14070b00b1506c0c0f150b5118440c59405002440c20702484003142c5842d13414104194071076903142c42514103907001d000d20081227 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 226025530 1250 226024280 226024283
    0x20d05030f10030218220b04150e070609090b0405010803120411040903020615060a02150406020c01020715150b09090402010c140c01030e0613030c03110604060f2003070309022209 79
    0x10711074100d6400b1552000804084801880700306040003007400149e509440144c00d980410b00403480e840c00500740c526004403503203c0e40000392002410001d0440302d21071901244016034060040350f06080c01103a4a21400c903003002d05019140000b002d0040040c840743c04448010800e00000c076003420300035500c80055031a40d06903010003c014005245c0781c0b00315811480d494002d44258400202c000b800010018400e554bc141c0030401d44079800c03800e100030038013036114404920482c106401c10b28100e4810001002e241c03a0b1100007880402c3d034007000c1e0382d01c040301180d03400820354492004a0344801201c200a054101c820300c1d104a503200030984011202081e41c04205200e80ca030304555403414207075894561a040300030404040b9221b04540d60711507000741807003800c0c14003d2080a160610480d0300384c0306240e4991003003505d42c10030b0140c11703800a08584100c070114441c2104c94460700c0050040d1092664484401c0708545400c9000480d040d60f06211380320717034842050000c0240c03440240 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 226026780 1250 226025530 226025551
    0x3111008090715090305060c130614090409061401091a0405130305070f0b07020106090c02030a093f0c060801030c0b030a020405030615010f020d05030f10030218 71
    0x115040951140d44040e01c00d04014000301852450952921560100098040c0800c168650b02201041e801c0080c41e000c0c3e12180d400c0c175a25090541c00c00b1004109400010400040180081800344160156503185c04115000a0425503d1401e5001810b1504810070016031000c00003424410980c0002920001c4c00e00f80d40f00c50084204004c00c03070b04200d43c281043c075a115003c1000c02e06c0354000d030414501c1521012039800207a00d940c40140d01c22201000182c1d1034560a0042c8400f6000745450314589000a604004e4054405480014140204c20b8075070700300b440841c4090412000f450401440031892541983e9902142c0c40d030050200054031b1060400b00009500c610036440641282d4002040481160800341d51012603070010340004590368081c0000304940da0b051005a0040c840d88401002850140c40050940e6030703082c0740c4d602503400ca541c00c1c410031504141101e03800b4807050a0000c2035918803840d41c0344111a5040a50002c0c441415101c0c6664601a4180901204003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 226028030 1250 226026780 226026799
    0x60b0a08161505130e0618090705010f05190e151809010f080319020304050405011212030b01091205030c0102030408120a09030c0209040c0506030a02071a060105070210180311 77
    0x1030103a4442c032034004100001003003543d08026a44011031000d81002005111744510f98147d40380f0031980c00140c4070340c01c16800c5154104003540e009044003800d1145824070314203008184400a10303480310440b600092140c0c41000d51003035030b0f41c44814420b901840c030200351103aa072000d0b002c0101084d45803860068034948008141d0004046c6480115411032004514107800b600240c412007115402013401c0d4881400003268a98a6001d4a40a820303200d415400344641403e0035580e040320150417905042c50b103401e074801c3c1e981c4050f01c03009496001540030080b06851604c1c0f07145200301644241c05500c0072041c0810000d4440081030715002c0f2960410540d22501c10301000c49000040007808206d0348a421801820a03616040d4440d00580c00e011030340d0348d5900490456802111404000c2e07a000cc1c07080100803031031200505180146d80c40c4034107031400701c0018015120307200000e40300e1542c40078240c001300d00c920700c49000010841600494969249090501c80b400342c10303014415007488 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 226029280 1250 226028030 226028069
    0x2060a0f031d06010303200d0f0318050c010c050a080f040315021c0504060b04090b0a1410030609081306090303120506010c110f0d0f110a060903060b0a0816 69
    0x10840c640c110301c200c0c00f0746030b079920359982070326540c43c11080c0c1d50072060380d200e40d0a4820390a00c0010032120803a102c3c4119119220760040c11130f0b081000429201061a10900100f003000503820501202820b1032002d200203400c0451501404440c002c0a2200000d80072b40f1121040000d00700702ca200e012060010f4030707003040c01d4080c2d0040e400406904905091492302c118000c2d0400d43d04180070b01c00c002220001c500c041015160040d1042e030b02d100c5110709001c035a14481c8162110030032610f00c401c0041c10310518043e083c40701740c803003c0e0066840300040e500f0300c078024084810444070461a81c0344543d4409000d41101407a11042d0b000c1500d0800700e400c40c0b041350181902c690416075403501044940d80d40d100020441522803030300410882103522032600d9a0b1074244010780a00d0080410030b00e9071922900424001d4843e42c06a40d005400300b0202e80c11100010941c2e601071408200c045031072012070413204103540310084902c00c2100b01c81036000f40324406000d46983e1062412142d080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 226030530 1250 226029280 226029311
    0x1b0b090a140a08030a020904060305012c0f0606060a0203040509090c0102060708010e180304050d08030f0604020408030f0d111902280f02030a0f08030106020127030e01020a02060a0f03 81
    0x1215000b6020f84810400100102425401010018001000002c94548a0311030b0384c21511450310f20455a10301110590b000542c50900f004940c603501c00a0002103200c1150341d484003405010a0b0090714041260b601090007881034402070600170388165007a00c0c11400241d43d40302a010014003600030303500030894144c0300301e0007181039a00e02c40c4070036032640340d00004040f060a0310740d154a690009000103c3c0c281c3d14401a031f03401e00e00911000e6120700300304c03070b141c0380110000e06090301c90b0b84100820002c050011064404160b00c0ca2401c82d01c4501c084242400b41440241d910441c1c40c002940b079001120f61315102d900700191ba421a45041c070502c2d500d02075200c10740c07023101c0e4022150400100007100e80f2070000350345101030107a0328209455503602c2001602000100c940351030100051040c2d0741c1c24451444010455124601003104078510215000c900060103420004038600c0700c80c1c0c50b4000c1020500140c0d014020f0350780c91482d10002011010ba408200c00000d09005900000707006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 226031780 1250 226030530 226030543
    0x150403060c080412050a11101a30030d09120f020a03080105040e121305011803030c0b040204020c0a0c0f0501090521101a01090909121b0b090a14 64
    0x91142d5140d040b200c8a03038017929150407011740b11040001d40080c0c0c1d03182c504180b01e11a48078002840229400c40090031b0b0380c15000403500c03002d00442c110104208602074140032044080c01c2c030301843c1d90380c42080c00c10905510551040a1145080071406030412404010f0704107044100d1744c0c0c21180510456040741c940541d460081e001510305401800140307829485550140705c008210787d40c1c950032400c0a01c90b60850290b50045e2085058100a15600000740642090001c04490b02903400c682e0064405807010401504200c84e84000400b151280d80c12546c4100d001000c0b104c0942551402c02d20744140703801001d14400c030040d0009203c3d40034800f6001178400090000080e0310352040c0c0c6100840d0848585291481401041c1d0300c4640f42d4450303245808a156042482c0a803588005440842a80e100440c410306d400741c664085416085200d245442a14120b484641944042d0031001803001c4090095422602840001a00020204229441110b114000499841f0740d15100c15 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 226033030 1250 226031780 226031783
    0x10914010303030b13060312030608060c0403060903030b130509010605030f1005060409080a030609142403030d020c1005010b03060a060f0212031f0b09010c020906060702150403060c0804 82
    0x4808014000a030007a045840076a90242c640008100160903010550780b80394400c1e90201c0340e05003100211039060080da07010340302d039600800050401c980520380601c81c500c0301604440e0307204158020144a90031412004070000d10f09090031441c0c143c44001000c00b6510704a056183c240700140b0f030304000c9046810a0b000c0f5010b00b074864420341c03c0d10003400700200345560103036403120b8000c0096502c1001d801c4064960740e000071a1828040303820704840b81c0c2000852440300c21010403092808411500080d401078000c460b01a07041d181c04207145001d010b031001c1c002c80c000304c1c8031101880c002540c0082c01e00d0407102803003940d0b80c4100600d081d10094607115005045180140282ea01540d0105e41006481c0704407170050350342036140d001d640c1040e15010ba00407c42070b075071420701d08480c0c81c001c0604580e04919181c54100380001c0d281c01e68040000b03004055000020300a41da035807003644c0a06802400206003000e944030724605660180c002116040c0c601000ca542c058446c00d1442c1c41103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 226034280 1250 226033030 226033061
    0x415120614060d090204020a02030309070504111c060b0309030c0709050411060f04050913050c030d210207170703080f060a0501051623101112072a020103050109 71
    0x52075541401150b60000510000907610380c8580300c0140c03114401020469003990280d40c4a04180c292503052158580c0118400c038101807a4014031700c0403104444c2094a840d01040d04a901c1c2c507007243c0038041a52219450a07004010007148000c040001c10308080b5490a4400864407001c64008542c002e03500030380800300050f02c03a84030b410080700a120a0b03020200700ea0510340c0c0c030400a04509012a9400c200440e145019001c01c442001101e0b502d0304124090411500040e200420840104901d41441206554284142103040d030468888607000550100c0e1118105107125540d8400001100000c40d11800100c4031913460030703014000d4000a0140d280c3c217151000441d02ea130026a10f5400c44400400d030040010309003260f1400700e00350101d0b0800c100c6000d6035068240341202040081d0030341000000c03040d4840403400c86500183e00e00c00ea000c82e495000302210102041450b2a80c48522801c0921142080840d100b01340c900c00d0760107120b030b603072076249000c20b5400603132040c402c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 226035530 1250 226034280 226034309
    0xb030a111e0a050d0606050d0b370509040507030b09070b0a210f1b020312010e1b030a1406040e0a02012d08040b07050306180c0f04151206 61
    0xe041c80e00511428806143c882c1c18100b40820030401c41e10168407200105500142c10030001c1f00300d00038580040c0088900840c44401541c2c0c5600881e09900401500d40300b40b2281100c11681c04841c10281c0300c054092207080c0b23003501d82640d903013500e400144c40e803120000c001421400000342810a65480f0840c20f81000700152054900b41171a04030011006211544d00e2413440e060302c96111405004500070500710194400081240f000c8034440c811908100a40c5003219110740f0101d04644510f080100b03075036150000c00c200d5254000181030030307100002c14481c80c4129030300800455844014844566210641048201ea081189100031a0004c1c91480c0c05580034101d0900c040102a191440ca58040c5c6d8000d1034640d241c20503100444c003560b00340828405a03030f66141e80008942041451030134020002681300c6102d41c00b090343c0d0322203030f03002650f010415400d45044d0385211400b00d07121902d800300070180c68506100703000065284400782900111600030344080386c02c10040e0401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 226036780 1250 226035530 226035577
    0xf06061710030c0314071203030f0c020606180402040b1507050c06091503090708030a0c0308010e091e030f071103100504083007020304170f070504020a17010b030a11 73
    0x40c0340145d0300f1071712180d0113a21000903903190785144200c4083d1007039030f00150300c100e6109000300316550340f204201150701000c1081207644610016050480c00c03850390400c940d941c3c5c0700050140190203a483e0700010b0f440060040c800c2c00e507001d40900c81c800c4040c0c0c1ca285a0800a000d0030740580400070364402c10b002e004120410200380110380040ca15003e46805c5a10740c11001e241d41c2c042680200010f0b000942c0c40103140d1300c0b2580c40d02501c50300c14680d0b01402d140b031030a96560000014002600c50658510000c6030003081190048410b0485568482989040000090700d403c00390602a0103034000f040809042842140d10855000101604149410100c07103040381c0355030030313a803601c1141c1b003000620154030846480c4030f802c25a0041d640c2e641040c41081c5041c0310501054a140d00043c40c0c100703c0c107404240c02c8185d40003a0340068071422603d1f400c4a4016000003416211804480085048040c0300300031441031024010030300c440c80c404d0002b45c10714890102c602c12102d0201d450040b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 226038030 1250 226036780 226036793
    0x60b1c081204050f0a0506090f0307050a0809180f0f0f040c090515061b010e0706020d1b060203070905041a1c0501060806100303030606050f070f060f06061710030c03 73
    0x350083d01990441d00c0c07450240441c6444c000350100306940079031110040100d541d2003001940700300700c144409182400c1c142d5443c0c55a4285420300140392001c04510403001c5e45941d020702c0410008204000e055080500c222285041d0030b0318007118041c40040002c0d81210492942d90285a1059801c0d0145180015400041c07002404860305031030307a10102010381d552440542513980404075225500136500e481c1500711492400d95607060382050504200894010440d51049c5138a801c002103e41c02100304110151010b803c018078191010040c0401180e020300c45034103448040d00c0c1080b6104503001c003a58450300524005502c140064003000c0f2a840c10101c21a60b035201e0000800c51588038030b000c03400c0c02d00482e00000004103902c400c000781607150103900018803503810306514203c8018a10f400ea481028406000074850190200420034641d101020303603040d1300d400f00203031038952000400840c00095002d6500f0800e0780498100c1e400108245c040703d0340200c418500d036245941c0e06 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 226039280 1250 226038030 226038067
    0x105180402010e040c020705030f0d0c03080907150309050d031a1c140d180e240603090106051201061203120204031b03030807031a011b02040207060b1c08 68
    0x202c1c10400240120f03d4940c81e60b001c0c03000e81580c40c3c0c003d0328110b424001411b06d0003112250340404d03640111201241550050440390300250145004002aa81c0c82c50041c0f5002e01c030341c0302c0c031030756031070082490300d400c2d80360388400d0840e031140003138a0324588049411015200e00821605c0c040717016a031400943d00e01400064040000e101d100c448800c0c45403189a1459000a804e20040e08100180302d00e140e070044442c5d402c469500009258242030603c00720f542e0314024101600c600c82d01300214100d402c0701000f1480288010165562458408202c50180c0010720030b040c000d90a5419610b10b03004180500815a1400e035034084000800348c504a0342e030710140b0009040c8550801010020519001d805a4030015006020360b074030b072461900501d01035004213388d040614125400821108602c2c80c40800e100034a820b211400a080754460082101031000354498400a44881004103a82020782264800c940049828042508a8504140c10400100040010080700e10307040440b40b2103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 226040530 1250 226039280 226039283
    0x30f0c140a120203010b03010305100e3307030c020c03010b03060c13120c180e06040809012703060612030903020103051306181119090509010e07140102060106050301051804 76
    0x29020249821040340b00301e90017a0020b400740c0d00000018000d0150420a15040e03c0c41101c0801200380020b0013207403507480703d10840700791580c0c1d140c821081d07003040b4400c3d614219180741041a20f041850004d0010002000800094010244004003e1070306104074510100080c018045a0f43c2e03043e0045070a51204884030368060402e54042491621068120070a03407150342c0c0c54000030308200300d9a003a81244001c1c10816410801500c4407060085070301c80d00258070204003901c41000303100503101e003450000d582c040e480035000c0100c1c141241c0d001410440c1d0080d6001c200980c0c85d40c03200c100052100300c0c00390116405100c10401035102c0d601c03481d8001211405c1811400e801d54402040c0c0c0d8940d090f041200710400740560074442550202400c10b00c0c11555607403040785204044d06409418482c000981e6a0b901c0064400d1200b900711040300306092081c0c0d1203039510748140a120f406500c1b0303410300501c03500c030011407141d001d0360440303040c0c0300002c2c012507104070342c4c40340d0903c5000c00500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 226041780 1250 226040530 226040537
    0x30c040305152410031e090303270b0c180a0915050f030a060b0f0d080c01241701060b180405060312030631020307030f0c140a 56
    0x1001c03071401d00406000c0420000c03849068100750480c5104490342c00810303428032030844401c10607035807082842010300c0c4090801003880a095401c142007080c3c8000341170700302806c15403540308069260340701600c4803032460000f00c0180e4842c242c10090000c01200200843c03d1703c0c0c08148140d4011018124611985c4002009070f8615808240e41c03000550081100c01d84840b810704180300300c0c49208010700b1042ea4001c0b0054107280009980e102d08203400b40186903907403283d5031141c40b006121501008050034120780d006040ca084149603109821030074455180625241d44000f042c1500b5404500803400218550701f07084448903100086810710031350390350714100028101d1400020b008800d0a0950400343d01c1000c1d02031000781d590061140d0f20071380003814981e581180c1c07001945c2c2c1000054500307001c0c0c89194842c40c203d4035224030114044c4100d1800186c0360300803d0300103500c20f40b03603940d0501c05c0b8810140c080c1709403049039445901140b8a608900380046c9641d0241080d00030516 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 226043030 1250 226041780 226041787
    0xf0909111e15180f0907030c03020c1204061803020a0e0903070507080309030c030a0c0b0c100501080606120606010807030510050402030a09050712030819020708120f01050307050114030c 82
    0x30001d507040202030b080c4110010007050304040c4140c03040c041807554900351000c1110165450000b074400100500600038180d40300080480140f2075810340d80c0c90207038002140c130303803072090b00c09003003075401a200c1c400002d1003c644020388040e0880c2408200d0340c0c09403004c00d4441c1020441c0d0280903004100d40c80512080c40710b100420400c11101004200e84000b540e52524108189410300c0c064812840c00b9500c90580030300029042d102074821504440712142d10750015000700390400e001c1002c42e4070300030b0400d000410303885070104100e07001d100103c40d4418803500582900f0748070780c5d0489105010072189000142e000c0d019400c403540c0691000380c01a0300c50b1300c074000a0126001510340940041d694503004d010088204048000750007203d000c00a02d1a05640080007084018401ea03501071812030200b118140720f8064402043e400b00609071500002a0503980c0e40d0b070102c8101e02c0d124001c000004007406c0c0817a22b0019228107944138814618030504442180d403001e004041030a0040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 226044280 1250 226043030 226043089
    0x150306060f0b0a200303100303090506040608060d081231050616120e030c0609010b060a030b0102010204030b0117010c051e130503060403080403170c0a0e0102010b04150f090911 78
    0x84c8021481032402c030011f91403460a5090081408910b504818041c1c0c500304002d20900d608821081c1d0300000403141c1140c0742c2640d103440303680e9024080426003031002d03003000d01500c15a00103003100461001070500c040071902302d948078510760450704090029040040800d000c854050101d014000f124204070040c21044202d290846003070f4018448150170224a1070000300c4107019071600214040001e00c84415240001100c601c2040003210034180c0d05c91403072609074000e4060341c000317503004602440e680d0780d101402c000404d256804103440b54646803c14031b1142c026015070310098410000200d140e84000c000f110664401200310b281007400030000a4141c0e810000584580e109955061307441c1450320f00a0040f402400815241180c0c070300c00c1000e403807a040305a4840a02600e02074000e5458040182c0c0105407000c1069042400c280d0300500d0070b16a160103004903561418581d000039907400d041c0e0100e940c440001091684070b4030041c51545442d81201d0800d01c16465248881c1510303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 226045530 1250 226044280 226044283
    0x80103080307140301151805090c0c0106080118110414070c050109020d050d09090c020a0803360c0a050609220903020105010512150a0203100801150306060f0b0a20 72
    0x2603001d60317020130b414030768034040a9100c1403400a03008001c005401f224281000589040ca0061143e40c2050000c9001e040e408070035040100284255402040320480d496036000d240a0450800c1c0d6040e102c0c1c0352001194180742c8103081480e00a00210311403904c400c9003c48203441e080c0410303510b640d00d40c082c03240903a843e2551444120302c03c000030000c46031200409011012550b0009200600c2c01c0220501180c01280010b9010740c043c8005940361f035141a0103c0e9402c2003a40820300507013515a003900750b540b0070020f2000017125030413107100100010411030701241d04e0080c00d070044c0050200d0450342c1025055500c3c1418280b6602081e100c01c04d240000b10340102500b600180e44a10040165040002c03002000e240d6810140821503910300b5490340401d4080e020440080c0e00100103110f40e40740140c1c800c05444d0001c024414240001c4009000710564041628580d141c42c00004681a0030b5642404880d002d184007030410990150079251400e01700c4420340480c800c510100001d080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 226046780 1250 226045530 226045537
    0x4030801090f09240b032107140a0b010e0c09030705040207030c08030c03190908030601080718060203030a0c02010c171e010e1e0705071e02060703021e03070308010308030714 77
    0x46500d102000e0b80c0c0080d0039200b07a0b004100d10078020382001c0c08a0284411802c1e441f811500440784e1207948103090321380480402d500900316016030060381070400400040944441c101c4282c0920211180c940c0c20b80c5078550703c1801c01e4103078503501020040040d4107081c9c0181102d2406401c090819440c01d0f116500075030300803034004c000c0740385c00000c10140c4080030206030038200b1074500c100801071035540e40d200c0300d10001d02018140000400019032407441900030108440e0500aa00503550f0749103030107541e9400c2542d0203a20942000715000340d0601c140702da0b5200391110741d02c80b44070703042c1c2e5040303203002c2d140240006074100012140800520b5264401034000c007081c9138585460710700784c1c00100d01c0c1d0011521912104840d9014000640e901c00e00b42e800c500d400010501103031f050300c0141d185402032100004e41100c0040b41d20340c10b05401103001c030b818030284419601e008502140708c80d00c0348240310004005c65441030051000c0b61003400510340c800d1140c10814421001320320304101640 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 226048030 1250 226046780 226046813
    0x503190804150f0207090b0d02010507020f03011820010e010c05070806130308161d031504060b190e070503090a02030f070609050118060804020613060c0209010e04030801090f09 78
    0x20f00b034201c042c4096604202c00300007010703280410407080c500400000c0700c3c0c000035840a8104803005c0f420209554a010a50b071103107800500030003c8848035107103812074048141080c0c5804c40400e004004014008103402503421059582901d052800801943c13101003011041da1988603124011880c00c078100b20241c080e0343e40f4110704060200e40d00d0010002000188070a0301081e100101d24440c40c2c010014102d010310f8040095404000c0c50082840d00070324070810130380c140c128000c0c001440140da0146030458429101c1c040d0300001040400464040341c894101842040000165034510034400386030841e29950070b0300c20540341a00040e00e003204000b016452500901c504011031900550381100500c1c0030f00301030415510b0400b2048101103248148c905110000c0d001504554940c0c04807000308c4100c94141c4019500d48800a00350314840c4000c03401544444008100a41001340f16072040d0303410360340c0c6c0c0842c0e030030f02e0156405408a4258429400d859640b0400000c2d1b00302d900f0312000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 226049280 1250 226048030 226048037
    0x212100501181d060103030e0301090602070804031208040f03030c17190506040c0e04090206090d0510060b0c0613030905040617010c030c021005130602030412110304050319080415 79
    0x100c601c082d41d100700c485070000c2046195140340351400940d000b04541c0d046a405040894850105130042409098040401008a07100150300000c0000840c00381c000c1d2030182d160300f00c041191650a4540700030549001d06801040107050000034440d402011030040030b85091a40399402460070029004141c888070103541161310f103e4040700d0248580303a44840121010300558000000180841e00f81d556218006c6454400300419500e40c0c0c0300700c4a1101d400380c8041c21010003801c2c81a15203005603540c3c42150304250000900940c02c4003a206a420503001400711a11458035500020020960850521106800000b01662103106e0ba100070004000c0210313070208014405404c5a5155095506041c0342801c10025941d0000c2c00484540317490000141d152560950b02440c15492000181580d000000308401c00030308840305001d145e00ba40394805100514540f294403400740e40a0250103502080e036642c000c14042c10003040040c020b481d00c902d0251a0b2a610011031010100c60010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 226050530 1250 226049280 226049309
    0x40e010801050415110a030e0f06010b1207020105060f0d020103200703020106330309050102041805250f0e040f1e0203010b0405221b0e0603010506070212100501 71
    0x38400300c410150b00804c01008100506801c1168203110781c000c91906a08043c2d50f11000c07031007008c01300800d82180704408119412580d480a00c00f940d03902410840d112000c0b548080365081d80140203207406160000e01103200b1046103010b12040d541c1c03ca00c207904040d100c000c0000e940504030f1400c8121900501065551030719802c02900b940c3c070350307448a00c448a000035140021110088005905a49602e44181541c202003084014100c07046001e04507520006000135041103040c4102c2039141c00a009000640d1181380c0c2282070402200038076194800d420a544040d44660740803444a0401d04102009804900c0800c04030b0700e401e04ca07000c52540c0e540b00380c040301541610005480c8803180c010741c503641c18400c440100e4002d6101c1c860242c8208801d88102424120341000d80c924416420000c5483d20006050504a01e2200001007030484801002900348503080324141c40c0c01a001d03526181c129400e01c07540301090a40050240625105003032001d07032601a043c0202441c1045051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 226051780 1250 226050530 226050533
    0xf0303091b170a0b060418050f0607030f09050c010806010203041d0f0f1909021201020a0201060611010606090302091302030609030a1b110f041b05190f02120d02040e0108010504 78
    0x15150044007140c2d115070242c10b5120009402c0c010080d44403100391004180e004400c0c925980d880450540141540907a100f082d480500020b0103510802039681d0601041c0d040c1201c4100f250742500d00540644c0029000e01c040d54000c40c20541c0105061044a2a095580000c203900003c0404000e28942c0138205001c24a9504102700384c01103a8507030602d80904101c6d00b02c1c0141ca00b451079007035420f52103049503400c0d5964050488001300d1104025940c501420300000d000b4031032030041d507001c10000e40d06015040340511400c01a22074680302e401d10b40b030568080211280d030061001403010480c00b0307054016101032100e14003403025200119190b108104014100d040c5003640e1013180b01d100548180030440c0c0c542c00841e0786400352244200a4104030100d0b000e042e482000c0401074103800c0c41d888072035502a0040c80d1a02c021542c0d03040760710a8001c200d4007a42080011303001680203a60540000c0c090100078100840220001860107907a0001c00c1d108200036401403155954800c00c000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 226053030 1250 226051780 226051799
    0x100815040e0708010c2c06180d08070305030f010b04081506130920090f0406050402040b0402030106090f09020708041a090a0902042c070e011101050906040302070603020c0a0f0303091b 81
    0x102008000759041b0510382c05807021440500450b15280034151641110b40745a403500030103100ca213a0042c1441c0e6a07541d0605001e00950710956210200758255400041d83c1e20b504d07415034060b44d07580784c054209440744040f46841d000010303003010f40c80b00c0c3c200e07003104100ea2184141a04540325140e404100202c1610520040c03081440c400c0c024038104080250340c8a880441543c000d81c041e50002c2d0584450020030014030448401c01d40281c400800451072980000d034000c111161040c040d48440d458400600990151140c0200380d008140700038012006603100402d0820116940c490915074088006007a2550545c0b180c0411359001406100c03c01c51002000c00e80c3c407220843c01807241c80c40404125118009010f130707082041c00340c61020540e200360101e2401d00740d094000d110b14204500d4058039450f05940c1180544a4210006260360090090b21043d03201d80000c0c1042a190b515284000421032204400701a0345038548000a02c8012104004510304200f02c0400d40c207104185 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 226054280 1250 226053030 226053077
    0x705071121061b0d0c020a0b0a0509070b120103032703111c0f0201180b040801060801050718030201050901051c240b0711041104060509100815040e0708010c 69
    0xd00300c0c80b54002c0c500f240c1d12192412182080d10221002400c100542c078100e05020340141c00400105c2a10b0511403291101d41009010b4814541540c0f060740e03548081d00354034400c0b4240c140c5d40d078403907900410100340200d01072030f40030b01000280700c41120044081c100b404520f4004958000c03980c4883c1c40705050404400c0b8003004142d900400510f034540382c58258051401c3d00a0401c4074014a070754000300f00785210401030250b00e4609840b035480c1c1a0703241c080c000741d0081c0d0140b907203404006940207206131414071260980c064a02c030348500395001118154040c0e171b40c079814002c0c10841d4811405030400d80c4028450000c1d80010030004c540c00105111496925a079000383e200c91092084a50769000c503101d050340442625103191080c404a80500740f0a10803460461020800041103600300d0001c3c008403e088030300308000c00d120381048d11500e805581c404140480e5041011a505003988100064100c01044070085c66540101c0e90039155583e02c2080001c00c081428840707042140c82c403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 226055530 1250 226054280 226054291
    0x20904050616140d0b13060306090213060b250b010303080402030706031e09060e0601080d0314010f05010c030e0a0b120907050102190602040e042a0b03070507112106 73
    0x180e058498043e801e07002501520030442002c41d61030003014101d50364460308151101d03c00009004182c3e480c28040014220194140c3c01005641d0390396030b58a595100e410b00b80c40c0b44109240c1454016184040482c41c0e5603c642080351b02d01d02e0b0280420303c94428640298842d0b650842d9618240c810704d800e1280f998407200925080c1480c10071014071a0040c1003071750165000009102d0090f090172000b03444070701c8942001e4040c4400226003041c010505014071071f0300791028811507080c12940036964400741304444808403101c10078099903104a4419507a18040d02c1c041107048503210000355440855840600004400a14a81c80b03003c1d91503025408418000905406490000081e44034000c123100506804000240d800030001c03645d041e031703015008104210025141c140b400071600d184080d1107442103c0c42c1e040c1c04018900d054110000e9405146240b42540c590082c1503505401659045800010902c0d103402680c83c0d0020b1130121000b20001e6884170b0802d140c080d810100058070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 226056780 1250 226055530 226055537
    0x40c0b07140c10050d0b03031c0501060807020a15090204090c09020405010e0a05033309010221040321020906070503070606050907050f0703030204080609010b12010b011b02010c020904050616 84
    0x1c2110101e900001905d110341c8901001182d00003070100000e041d885544500740c0040c06060034401c10420540c01141600d900362070303c641c191074058041e03a5601d11a00000c0c0071a40488819140700c003d6082031101d288080e20108035460381d0360313070700d6444ea480d5000403200e142d010408000d0b030340c0e11611b40a40c0c418240c48000c100c0f402d107070200e619172031448101d1600000341700c029003403151154a042c14030604002d4010313280c02d1a01e4041e0103984803000c0800b120800d1f20300c00d070f880c0b02008602c0e809964151035a000b4004580c0190001030011030819003205c1e03003403101044035120301e4020014203104001443c0c1d941002d10b0650102c0d0000d0700914041d4000c10100240300c1c0d0004222044403423003003d00c90f10341d5085d00e0100c010707108a400207103035400f8080a1000100054000302e500c0c02003203076084a1070340300039502c50032100201006400980481c0003070410b00801c080d0001c2c0b490043c0f50594281440d5008110070388001c2d00e045909500410412450189071140103c0c00c500524 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 226058030 1250 226056780 226056799
    0x60501060c0b0412020307020607030215281a060711090f04050604060f02040504140405070b0f0d0b06040f0b071209050f10020c13090b0606090a0e040c0b07140c 71
    0x80b60304828890061004001c5481c1d010000c200d41c0c020400c0d6140c5039802000c099686681c0e29009440c2c2d69034801006d655080c540218035515104c01c40039800010780f100b00300280d5030f00c0b00b142c8040e04803c10140c90750500d141c0c10b1030791511010300401e1710301e000308803907072070300780305405014081100034190440a0041030602000407008206a030304541c00200125070100c0c11025000240702d0345e44000d502078035140d1250070804140007503e214500070b6055882260780c50b9003400080c8120f148540c6112010800450020019032006041c1d040c017802460402d91202c0321103829039410740051100100210301d08080003020360301101400c80740c0c0350009090b842c00d07020030f60515841080d0f6100d100855800c403000741c4200a140240e00780140310000707120062900170000d210505050707450048440005045041000840300c40b5003026155031140c5241c000715040800c0e02400490700e0b02001e000011300c0300c0380140500354035030003a2440c00400300406c100514154080e4401c6000300250f1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 226059280 1250 226058030 226058033
    0x1090213120803010506030709150f08130c1215060b0c07081605010809030909010e0a0c080603120c031c020a03060909020d062f12010e040f1106070204020c010504060501060c 77
    0x342c0559044501c2658850b44075100c03070006440f0b6204907040b03008440d50a0040c0801a40d021028100c003481a03110070700d0a072a0070550652140c40600043e0400268003801c205601d180d888020100740682500f00403052250130401c196400341c1c4c4003162206003c1074034406d202040c4034200003051900c0080a1104620200d0150190188a0b250501c6010000248260b03000d0040740c0e10f010300180100d005607103c0300172642d02c003405d899001950f0f1400f00d005580340e029108541c0911b40003001000d1405c082c0e00790842d682d00c501c80c4150180428816150341e11034020350a00b5101c150038000d40c0768808001e004040390360396409a04c0030b40c00c0c249140050b0720360641a808030b40c0c0000f000f14407030000408020503c3c10038400e8001d095061501101c092169602400082807204810b00490740e0b41e03400b206400344181d40103009088044a16400590510f14449100c017000e032407182456040c1d000101280c03c0310080e1100b07a51034000300300030030071a03120b254090f000b1418040300c02d6019 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 226060530 1250 226059280 226059293
    0x14090c06041401050906190807030b0a120809030708061003031812021203092d010e060d020d110705010c0906080c040e04061103090a15020901050a03050613050109021312 75
    0xd1100ba03814030500058000554540c402100e600b1413a120034180b0990285c0d82c001c05c601e1003244c404e000286080200e40300761a184421030211034440c80900300c1c20215813143c02007076014046240c3c0c1845052b9002944130418020a44110840c0f02d40c291200e286007001344c052551000c1505046032011000d218900f00800700c204055015103025651200a02d4914918462003c040b070744454003007065100320609041d0254641c400046580284910b2001510850302801482c0e80c0030100788000f08910fa1180c4c0500075181c4504400300f40700a69001230011030b400007200350b5450751a070660000c640d421030a0080149030f0f6290403d0640740480c4020924051030080c6080303520110085003c4c071030716411a100c80380011061507608d00307003c0c180943e207510f80310f0704541c02d005880c41c075402400d031071007070b91254041030311140e140c00303003030b00e012001084010305c60f035401222600c0b410b03014825485010701034003030708c24010781d907004104855224034490b5210441140102c10300900240a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 226061780 1250 226060530 226060559
    0x18050a180b0702100e0a050c060c0a0f0c0b030117012f0705070b0301060e01020708031309020c100903030209150705031813020708030a0b0f0d0809040b0414090c0604 73
    0xc1114001c00141c039241d50803401d00100d85a5a150181070220013115800007140c0d00010500c1003041711840c0340080d0520800740200312003045036800859115002c01c100241c0510040d1081155551480d104c070750b80192070704281c0011223100c684001c2d084100d2003d220351945885040d1150540618031041400301080700c03140c80401380c1d004102c1008000080040d81e0107004190382c0f04d9125a11001c004007442710000c0124014810101c0c0080d002d0008400c42c2ca208144d41e105000f21414120107901a502c195a81100f40c400c0a035640010b00880c070510010500ca55405666540c1076001c001041000710085682080100141000182c0000444291064402e110410f00503180001038801c4100a000600c00780001003c000f00100b8000940c031400100404002403448001800355100c032000c0130f140c00c04000350101002c2170741c00028211407180140042070740800300000c1000d0b0340c08000810070002c180c0c414050241c2c000d0083e031081f60010703075034242458034103032003c1d04042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 226063030 1250 226061780 226061783
    0x60c07060318020a0326030f060d150507030b361e01090f151508091e060604050106080f07030507090b03090c1906090b1b0718050a18 59
    0x141e803103501c1080700042d055614032040e0001c0001c90f40e15500d04112000d034024100e401c56103003940f5040f56001005c1015030340242c070200e800002d595034040030b024060180c107000343c40034480c003071500d542c1c0c507100d0040303a00ca204a554085038a0340940144204040015591035010340f00611b0184202818001001c2d480c540c1000800140c41d8005004564503606180d403107040c035003c00100342c840e0305800c00420310314600d000f001100c00000b601480b2103258010035521480580150304100d2040360200d40003030804c01038520781740282c03060381c5c1552003190a04039640c101e80b08008542c903181c4166401000d40d4102031a00d854160244408020002c001905260741d400200d031456109402c0d0310003901e0a400c00769668100420410360b280001e41e082440390190134044000c00d84c0c480140000c80d416910fa07184820b040080008294000a81d03922104a1000030200a203004001c85d9000b41034000341c101c04102c507100000c003925002802c082c030071810300d09141c0d0004001d911598026 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 226064280 1250 226063030 226063037
    0x23304080c030a02030a020610030c03061d01061203140f16030e03100204080d210b0f060f090a06030e07062d0e0315150402070f0501020c01020414060c0706 69
    0x1551640380c10240e6000d81d4006045038030000c0b40031080c468000000304010308841c0c007202c650796145481004542001e0000030f042105913601000004d40941100c041c200c00700c085c69407020b42009455007101d01662100c01c0755281c0c0c0e6641800e140e00190362200981e2041605854480d903802c4a610921843c0598080405001844c03010705101d1680320609181c0242518211545c1003000350103500940a56400d6005035800211054080d80c000010340e49440d80500d07185180310711080041020000305038101c258080010083e0b40e44100030240700c421044065250301c00402405107142440d0018014546410303901c0d000c4600005201040344c200385840741c44070614a410743c1802401c0d8840f10a035882c0614a811000e410000e03000704c0d01003d80454516408150a010709950155184843d05001d510b807801d041c1401c0d0000c20b80c0314003d030800441a070307140d41d40c542203a00c0307401c100c2c80036540441d042c04800c03004d80d00c2c01e014401c200c0d44241460000303880d4940381c00440c030905060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 226065530 1250 226064280 226064383
    0x6090a110a08070605070b130201120c030b060f0c0717030702040b04060b0c010c030515011b0f0b010806070e1210050a2c15010f030b0604020d0f0b0102 67
    0x541e03440802110141c031003003003500d203080e5481c04064503541040b0400c644e54883c600028410701c0014206045440c0c050b034501d005458080c1c808001003c007900340d00d00b09915503440c0c0086464010040c03403500c92a07001241e403824400c003520301b002e20a400c000c8002a840c7c405040e015400410b0361442501110b00040b48200140045c0003062241d002c0c500e00b400c0418618070444065005400400321518144203544e10220440032103002c0d4000785002c64084092402d22030250744141c080e05102c2c01803801842005d4440010400c03090384005802d0b030041d010043c800c0e5210889110048040e0789900e0590b14080c1c1d480d07201d50100d000302004550310000100c0d000460f821808040c20078010034405030140d00d98117400c8650243d90750510341f040880c21003a10041c5c0112074121440c00880c0c0c2d032590f041d9614440380c52000b5140c0c55100d9024010b4080d50445845800400b01d120f250000b05500c1600001e802c12065000700725151003400683c2c09406060140385800003141e03081200c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 226066780 1250 226065530 226065563
    0xa14070b0a2604030203070204060b0405150c0a0b0f0106030e030702060f0901021f020a02010501170312071e0306060e040911120102130b0702180603030703080c09030a0b061206090a 80
    0x2828140008814000090b241c180414103402200402626000380c0d4140031590f2140d400400700c0c40b440c0b240c1e41d08940c1200c88100e040c055007000c1e1549412020a40b09000b080d6168901010340986241480b80c00703090040083c07035054030504c00c13940d418801860038410140c0004141d0b014201000444e900300060829181e803080c03164288244c1c500d00400420248000d111009400c80788110000d5031810001144400280000307048800000c002140f50141400c3c81d082c6014003c0c01d001700b03005401e0203248241103400100d44000e0b0030b544c1c0000d03185181603801400d041c0303410f150600035407410b41108080313200d600800c51045000d88071003000c46400b2040170b0082c80b844444000382c00c5103d0002c950005440c000b01400e5000f21490210b00345000c0c10800c0c4040150703285070785540b04025440010f80140c504540c80040012402d040505910110341010240d1f103044520600c0f003002c0040030724081c0304204031064000c0041c8007510300b400b421a0b880f480c070300000c1c000090302e1450f180c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 226068030 1250 226066780 226066817
    0x90501060c11030c0d08030106031116030e06160602090a0b030f0610090b0d060609080304080c0d0f0609030c0209090304380c060603070909020d060506120307050a14070b0a 76
    0xe48441000d00500d00c185d1443c100754030303070350401e001d8000028203000c8803505001c40d000560b03042800e00401c660b0300201a65080d00c80d1030b40c3c0111780d90040008d124216040c1c0b0003505200410b8043c100c090380d503502d074408106106582d07800c4081001c0c001e00602000c50308018401d0303407266041d03451908914004c041654600c0f0300d0b51154080140001d00209009200c1e00320700704985881e1664107a035078984200b95160b00480c010074941d584501040c6420307142005590f20360718060704034040006c2d1035860f80015981000c0d000d4001c00c0680d20800308504010060590250014002d1401e19080a0300306401100f85541c5100540c808905180041c00001050f020125110000d0b075030b0303101d00d820403503c822045418610902a141c3c00203203814040c020011002e80c0100213001c000c201e60344840040002174003154000d84e91003911100c9010400013008640c0c0a0310081004481c40d20b44072000000714601da07801d5030018070040005502803c20b07124051510305103070f0021414000920f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 226069280 1250 226068030 226068043
    0xf040f0204061a09040c080105010503040305131a03090c1909090204020f0a1e03060b04180b03010c09090b031c05030718150f02010c050412081603030510090501060c1103 75
    0x1241d071200704050f90489080d9840c02400c1030b2070284c0b8280091202803500350790b80e940910640303000c0758042000900092180004141e4500c3c00031000e0100ca80754a94800224158412a034100703a000090100c1100c08000074540c5546c211032a115203d504604169030b440c60748180904075441c1c1ca114821075071507030196420390740c0400185865100f460340081c060000c081d030200385081075111009641d07200340644410740e20402c01da6440e1918100140210b0f400c1206508103807a95a48690141d940a0060103150611aa108104141842203000448034138142861183e401b90b11007009000c800d46240c10800100c1c00c0054076a0750342d60058074008a0081150340025034100f011501c030860400510092105540b1149104500d01c0b06030300702c1e5805524400459014001080480e03402c1c91611340e018480e1000350300300407280f1507148030400e0315003084010075102d804001000c00c40410010041c216014180829458204050681e082071040580144030715480480d050320200b050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 226070530 1250 226069280 226069289
    0xf06030a2a030b0f160e0f0904050f060106020714040905060402190b280f09050603060103060902030901020d1104060e210303090a030f02010b130f15030c08010b01080f040f020406 79
    0x9058042c6880080c002130910101c503144000c0b01200e1021524600c58601c11b004060301031b140c2080319007040c003085140310004104540c54410b14680180c0030318144040c0c1d000b013030603400800141d4148107000c450b1440d90200907001e6858207000402107100028410780050f01515a01101410080102c3c1100d0780e980000c140180001000d00071281c00c40401400e0481d00090f0021007440750000b10f4401d62000c8907400081c0704000309014901c0c2510080d50440414140040d0203661492000c059030411206401c003079501041a00019446004010039038a107060041d1502c0e06100024000d107000a9900703001d44a400c4021500744030003007601c201f0001e14400c036912407915000c0e0b00da03640c1648100310300140408400c06103160050240c1101004018803102050068400f52801040c6548644052a0700c4404a04213003403d004500d000c0c43c0a54000150541060301150a40d4000d112650410040e00e04028400e0420041c1c80c0e001980076a03510302100365400041c0140045410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 226071780 1250 226070530 226070543
    0x40e03040609030b07050301140405060609210d020703051207021305012711070312060906030b01030330090507052d0a0605251203050f06030a2a03 65
    0x9012450741e0300300140d403045038880d031040030195440c140c0840300f0703000078404c540c192560012054810b02d072036000594005c0c1d01a1140381844030310000901c0341c0301a03d90f494482c0034041a0040901c400b4000c00395a100307540002c01c05145503075142070351100250399100c500200030030b030345086544550031117000d01100301060040d03585848240300451280c0a800c010006038822042c4c990728a401148c095840416002d801d00d50662025255082c10900b1220f116903900d00200704007000340301da0740141d4001c000da0603243d0f045180141030715541c40c4212070504103110b40306200c1441c5d9168400052040600170038182c2c12850402e14201040d080541d001d038901d0b10390040822081000600320b0030755406118061000c0084c130071001d005006540005004000200e1096004107000c0c420000e941c0c0d903009030421645031100717103d084240c16070009459034240044604a454202c1e00320800b200540ba9084159440c801507001030b00c980410100b071b480703023446051100c00e15800250b41018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 226073030 1250 226071780 226071787
    0x15090c0c120310060f17040b06100f0e1c05060103050c120f0715110106060f0f030509060103060905030c030d090c1d0718240201110a1b061d0115080f030711040e03 72
    0x703090785044904594003400b0340c9000c66500ac00034403820035080b14801c503403100d602006085040c001400078008824014440e0841500000307001003014500035400b031400fa02d4890b40070420001054811410000030350f100c403000b4440120041000c1045031070f46c0303d005000307102c0501d0540d84c03030865000c103480c1546814000103609800400c00e07850300200d59114001a41200c0080d0b003120015900c21300f165100350300520005d2101d44c0f200d20004d018030304503800c01d440c1c14022451a84500050188662a411200100311200700020080c26a000f01c00014107100000d03030010752402825113080266031070188005000300300c01080501080038100c458144803420310b508845c0f05140701e100649c40c0030702040d400742296080c3e96650120359144c1c0e0100c20059a406e001e00383d4600d00341d40e165a0351032a00800f41507070920a04160089002180318540c10340c00f880003000d0756100c4040d58004003085035481002000b1144155441300701000e801240b10041401001c045034089003a11000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 226074280 1250 226073030 226073033
    0xa081e090601060e031f0b0102010615170609010b03130201030e0a05070513020a050403110103060e0f1801020f0703050d0b0d1b0501050f07020915090c0c120310060f1704 75
    0x4140a41a160a030f22001c405600c4d82090650340d407072107009000307601644070a400d000301c2980c0104040c098141300100d1b8080d160705118242d100c0ca0b101c204045028051042117030311000c0200c0c1e40c4003100300c1c3c103055191315000c1032090385e00c00103107104001d98007100c41c001107a0103648502d4400c10803404681510006251031580c45640c1d001c4c4502c100c02044816604d03080b1402110724074107241d80c415043c5032840c0d891029075055940301c0c078189600e9a5020030711a008007522031280c03205c0c102050641c00c003010391a1400a1400001d035142c2d004020885c4001101c804949810303506150007681c1e0380c05000b415005200c1c040c0015803101e0f50702044402c0c8404000c51060401c110100c1e0615159a84015134141c4218548800064024400d076030151404509880c6d001200039094410644940d0024001d560308544061304241c002c0b4043d0074840003004800c000e03c0e1510f14940c5181030003010362924108030322035101009085207104503800d1103083c0804441194048008a81c10719 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 226075530 1250 226074280 226074283
    0xa0c030315080a150e120304060f050703050412020703020a12050102190302250c0b2d0a02010f140109050702100903091d04150c0e13051506030c0a081e09 68
    0x8000d0b1900c0c568102181c96003203041c1301e0403598010085c02080502d0080c2c040b010309420003041600d0072640d400300900501d80a000d0700d48100400c0d600098249800e1910801c0d02150441d170300215808880244016110400c800e4190390f40189002c064a03103601c1d0071400b904c104075000c426801d503102c40070700580c2c160300901221150411411140050504218114405ea00f00a800c8407010b150820036044050000c1031031b2403850715442001c4901080320010a000c0301c10020010400003580d80c0e06683c20700c01c840c1e084041c400280520000c2c55000400090b041c001c0c1e0050603a40c03004103003aa070081003020440515184103000146035130070b0160948800e8030403075500e20381030485544452414444180304940c0408003240c29604102c51038010f100d540044400e21460030040c0490756070b01c007450081042007010100382ca1a128450003503004110724014017841c000c0c002e0040d990490400d940402c041450b115541d1b90700c1c00306062015031914802000c80e8195014048414030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 226076780 1250 226075530 226075543
    0x20c06091c050d0908030a02060118020d090b0603120903060a0b010203071a1009020304020306131403040920091309170712020607020f0307020118050901060f1806050a0c03031508 79
    0x643d5110040320654a0450680703030701c036600d5403030b0041e00114018041d413007801030514003204071014010b00f441840c0c5001c0085a40710340d81500c003086100f040000c2450200103c5d801c14400e800c215040240f00e02c00700c0e03505d071005491b4504d40d44d00d8503070040c0c1e036903c204140c903542500002a08c00d841810030030150b100c0815106211065803c40c408101410783e40200ca00459000d4014401a03954001d00da03403902d41542c040b03440142c0c64500300d4405000300054406440d200c43c00191110b08414100200b415003800c107948014180003441c40d56035000e5802c003400540140c007003103841c458a00001d0344000350307080c80c000c45004600c0c030080c00b124002e020294592034089030442d440c0d030041680d5540205108200680c0300704400c10065106030400700100103c0c403116149140c603500011804007098019500048485080c0c0d22f10990001204d0004c040e100e03500035100b0300b0300c03400030554460382c03e9a81c02d01ca506400352080500c03030340c04603920b00c88c0a54004801d40c0c03203420150b00e036407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 226078030 1250 226076780 226076803
    0xe0d0c02122503061808070f1a0a0b0a050f0a05091009021809060f060f09030309030f1c0c03020a080c1908030108100608060f090a05030705160603020703020c06091c05 74
    0x83c6405e00540c0d01c406111110307400c19402150050034407403240c0e90290b0800031414200c1d40a8200c00403c2c400380e0880e0500e0740504030400022807030b06071000c1800480522a0b11440c0f0800b0304414900c0c650700c94a24820075550141c9442c48180e0b2a0860303081c20200951050120520008244081081134903840c580500c04680280803500e41d90100880d001e40107001c83d42c003400400134045400d680c034005000303481c000b506807402c0c4211500001d04028091711080c0c8150031840303400e4406140d10741c0c020b0441c0320604102c100c0800c1c07074800039958031142100820320140001e800d60b01e00c00410941c8880c415002071103550026078901202140c0003881840c2c100e1007100c02208803c00789008100641d00708500800942c0d40303004410741950320140c0243c00c04e0041c1d81c0f0450124005200900c4814044c1c0d0003050515098800e10b13001050544c030003001c1500c148034400000f030f400b188030200c1c40b00442c0d104d62510f054900144035526034008400f0040329540020082080201e0102001c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 226079136 1106 226078030 226078043
    0x90d0203060a0509070602030a0203071b080303101e050d060902061e0301060e0d02131d07031401050606130608040f08041403010e0d0c02122503 64
    0x5801d0b240c40d800103841c0d004120342800200100c000406a91004605e000d91640c130094407802402c20007004207410000c054440445d10500d20f0242044030b040d290340e0300f461502c4029046561141e207083c6a59032008007404285a0303101d1003290760241200c1d800d5030ac190784540042c010380004903840300c030901007000c0243c00e400c50100a01500480c04e41d0301d50401002402040400c15118403421380040c1d9040144c491000010210724040700200b10145021060264891a40003170225485505400024005c95043c0300b0720103d414402000141c0720324060042c4d40c0b1440b9588030316070b4450326040202d6031143e51005da0150040712a0295078200790f1754203800340d01c40e40c4500c0c00c0e92810ba0300340140d4079003846980340740c1041d840206440d00441c0c0f40034101c0654903101a206000720a284000304005014100d24069040c582160144010b004a04051180c2c04192480c = true := by decide +kernel

theorem cover : BRFrame.Cov 225899280 226079136 := by
  have h0 := BRFrame.cov_init 225899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 225899280 ≤ n) (h2 : n < 226079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
