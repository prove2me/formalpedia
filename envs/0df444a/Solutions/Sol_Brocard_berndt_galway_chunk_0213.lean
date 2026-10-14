-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0213
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:29:58.092611+00:00
-- url     : https://prove2.me/submissions/9e7682c2-2363-4cc5-958a-9336f8853d14

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 38129501 ≤ n < 38309357 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 38130751 1250 38129501 38129513
    0x1210e0c0103060801291201090602090102160b0f1323010906030b06090603040f0507030c060e0604060219060f110403060b0d0804120302010b0907020a0b07050301140d110904030507 80
    0x50004c00451000b0003e01a8141c820350000141019030b0001c1c0340d00d68024a156102c8401d056040141c0000821500c2c08518051021b0340c809000c460051140945403203800c1d8a002c0403004a03540046864a06580d11094030410b0700710760060751258203882000185688080be100d0000d410262a609004090f00c0016001090325080141010f00d4009041d500d80c540d00125031102c8803c82d126904c950719842c0150101001040c001d02a00888900100704050070f5204801c1e10040d4644d0340d6650070070020b00005024521031707640103034048000b001d00c45860705401364003580a04000b04000c001e045d601d40503101460701c6a6041c070301c001020010b00c40c8510443c0044c0c0c000f124031462f8503006841d0b501c0030b030245c1c2c0030307459149540c0031250301054001d43c440e81030050040c0540c08035262284010751074040e4240103584200c0c805001862a07481001164140c424a01d5404520f50700030050140030500754100b12041d0390900040c1301da65a81c1d0038468482c91003651015070721a090300e008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 38132001 1250 38130751 38130761
    0x207050d0513060804020a03060908030403030b011d0f03120a05040503060c0406091503090b0a06060807020a03090b0f070b01090905160f090b03030d050403020d17040203060601210e0c0103 83
    0x100c400c2200a20151264100c1030984000700c401c685001d526944480c00000c41c0b8201c5948010b110520b8803080604104031000518803a134081c1c0c5042140030f06010040d02c100c1800b4a03031000c01603241032212010f20b4078041c0c207045884050200d940c2110782c512103451540c0245c414401007540480c5c10455440d04004c0d41c0c0e8040c81013025070f0b0601d4a000400f4142c5d034154090340a15440310411031154500c00d40c45611b01580040b035819850070900d031940700402d40ea0040c440056810707400240c2c0c1900000b80c0c162401c2d0305948800d055032814003078900d103400c4032444414403030f4104161804210326119881c040c04d442100010300342c0d80307440e0031441c24038404c0d5805030a01c8402c0c0200050035142d8040c0c000c42e84034010104401c004079000901307500c07610440501080c40d000602c801d140d400100b02c0e8604000d501c17100003082d206040d8200400c0200d40083d4141d0200d80094000d521516904030390180c4401e4141e8040e121003008801d407a400544c180080e84069a06072003907a143c011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 38133251 1250 38132001 38132023
    0x30f06010807080a0f03030203091204090b01090b0325111621030203040e060406030f0b07110a110f04140108061609120f2901030c0515070f0f1401020705 68
    0x500c13021606941d030441940080c5070280500d035020000509400040c40442c50308401860002d590b60f881d4682c481c000d01c0800042400a0300010700170134925030340d5080340c0c0142545030b000c11441c01c00b00c0013040c04035400205001040300d030000d40320054008120042d40e501030745251818050a14240304a1f404a0350ba00040c130100e0101d2900200b5000300451701642c1c1d0b100700c8403400703980d10404140039003203550005083e01d811012681c10720681d0180d89005822070750342c14559030540c0d881140d44103070921024280352a040b81c00d05491070500070020b0182c0300a00042542c2981194000228000f44d00c824140e4100350208500d02100700c40000c020200e60400e01e207410304064031040c0220a0150003041c0e20b00b040f030444c09001c40300007583c026401812000d020403101c22503244290600b88030440da02446e10310042074a00d000f00740c108490507602c0b401c80c185031042e01e54400101c80d404040e141024000c00c41d4011a00c003445801c5514580400940d4800c61440c200346803003886a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 38134501 1250 38133251 38133253
    0xb04090e0c061207020a020a03030503070809010c2a06020a0507030e03010903090506031305010c020a050106150806010c14010204030f14150105010c0501021b0f120702061603020c030f0601080708 86
    0x908042d6039588181c490360f40718038410403071076a10720109a01c4c00f80b080d100a9403140b0850000410076034410011441110a6a1090415100c501c241c0c0d080c1c460b1070600342c0c04502c0001c00c00419002040d240ca01000b9080b060030010903541d00c4503002c03070b40f04184c007200044000071004249500840041c900700d138150000c020070001a1402441071100380103151203400c000021030440121003c0e82c000f01e54000e002040320301c4542102275500c06900b08101d420f0f5003031400c001002030480e20f003008814920703181d0f903456644080045a00c0d032012402107507422041d2101e2408074500b48068006180724801c140c8504400303040c000c913075000640d0035102c158000140c044070b8903041985181107a10030300701145686541c1c03500c180607014012656484038403200050038001c0000070740340ca210300e0041c01d403903034004c034076034280303240e108030600650011820810706c9001d0040c502990030320380c041d105842e03504101070000b80c2048507980c0c840c200d0354403c8005000c001e0040c0641344c010000d4034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 38135751 1250 38134501 38134513
    0x3030103170f09060309030d0c2001090c15051c05010303031107030f0302090d060915050c04080a1205040909030905120f060f04030e0a030602120a0504080706050601180b04090e 78
    0x80e00708902d4400c208106000380b20203c08215a41020070a81e2817080950005005940450600501410403618022070050403c800115008410302c0b8220034990040c00c598101d0303042c5881040d140c907050202c1010800300300940c0b81e08044100d00c505581e4210000410194998140101601d0106854000000c8200080400641c000c038586104d003807142000758440143c2000102420012038024000ca814809100204081002142c070303014521001001261a4098040b00b103000f0b5004500043c0c0c00b509005010542c1c1c0b1a004407541028600b091606480d028410140c070425a012804198a05018400c0e45003422480900d0440d0500a1481500584400344d5854000e4207000c10702e45036501060a042c8038502c0280d5451010348440e45043d56481d044009501051b04014076901c1403001c200e11100301d0051034002d50b0010707a01400c001460311028014140940198140080b044480c507144200200e40d900406400e5409516507103403401200076182c8244540066030041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 38137001 1250 38135751 38135767
    0x602070f14010e040b04021204051209031b0a090e0c0102100e10020c030903060405060901060e040309050105030a0605040609150e070c080d11030c040302100c170a03090c0303020303010317 83
    0x120318401ca5250300346021070519801001040c0100107900324150420b0001a6001d44007442c400c4407401148941c0444121030307402d48040c0e03000c1c0142c0501550603040203080039180c0c0c0f49451502c0d040d560041070401f4403591a2191411604800c0e1042c207182c1041e013000400c0d40e010701000c0103c1201e4032003480080442c5181c2910760f0b1120b10300c4184240d001c1044810010200280e54050300e02400312140b5061130705201366240c41c220b58440130303903081c054089402402c0b016054021036050b00c48840e2142400015034249d00018424140aa980d003c0081c1580d03840c0505c0c0010280e03454001014111302c4100c40d1000700c59000074821301c084400740600d640d80108000501d41e000031940b80c6460f00c40a03e940601103421300108410404014044100340010041044078402c844140c034080c801d4500740d50300100703200060311074120b0300d0760080da02000308000d2506010524002a443c42c481d0f844070400901c540050380181d00c04001801003100c0d0a0014810a00070f2048034141409 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 38138251 1250 38137001 38137019
    0x3091208010605090d060b03030c01021c0b01020607050304021804080912070b0409180606030b01050a0503060f0c030a0b0a12050c0a031101030f14090a030e100206220b010608010602070f 82
    0xa500d00781340c0541c0d04076918000b401503907130080d642e180c00282074940c0d8040518100c0e000c4c1d08000703d003840146441c1c0300303420800d000b481128410304060b000381c1100d40c5e81000c16100c94000900590b0440051303d604c81e24040c40c0c61105100e180b2401d00641c03a0101c038414010b40505152640c0c8403603006032018440d0680c140c080d076085074448100814200a110b08010700031150160090085042c80c00c08020040200a0360381038402c2a24007030640b40d501c0f010107a640e141030721100380ca020410081406005070070015070307100452581c081904122030011075034450a6921440418040018503010080c0030301000e00102c10440700b010200c0d0450302c0c0d030a030f1080603145c05030600da5039107010300381440c071074200b20055040300c040c03020300340780000043c0d031501c000d01c0e4100c0028070140251010303031828002c00300d84945942e0040460759505030703008480030b0940c90002c8100101004d0304001038512009640170349801d94aa400c40e5140000c068a050010303004170903139030792814040c061080c3d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 38139501 1250 38138251 38138257
    0x1903020607050a0515090c06041d0907080307030c05010e01050705220905070302070506071d09040602040506030c070b0705120403052a010b0306011a091201020903010c03091208010605 81
    0x60112500d80d030318401450602e16054404400410760300400c40b07007060f11310384c49a14510400340c0c20241c5155003d02d001b00180c42c0b29500a00c4001c5a0350f00c10085244038885003103130b03c01c40c1300003210000c42c0c13a51700c0c0350300e5600188400c034002685184180e007081400c2c064051103e0322003000f0f10182c10544005025402441425402d8007140c010400c1e012034003500100081001a80c00c0041c1c1c101610024043d603c1007009454510440012400d00c0d482003603500c0c04124410303030303134030304002c0c24000c003d00e644000d40306448241c0c00344804260740c0c1d05e030700043d80111191140706588806034900761808900c000d000c08113004050140c4c0c103410f520ba604203580035615203002ca6854001910100348084000c1c425840d42c2981d00500d2002c810542c0201b4002c0021012a486070b83c0e43c4401d407000c04200d650f500301d8004240443d003080e04001c0c541a590241c20310016080c900c2650100c0c0c00c6440700400c500c0007903102c02d032030800d014494801480c600000c1c0f51000c0c80d50b0410202034001d00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 38140751 1250 38139501 38139503
    0x40e030306012001021213060c020706120f02040312091a0c06040209061c060e160b0d02130b030a0b0f0f01020705010f05040b070c0e01050604060c080a0e030d020601060e1903 77
    0x1c103c90100303007100744294121082c050000c0302038192804c0454424403610700c000000c46045140c560320602042c000a0035008aa5160380c4e891072140200703460002401d0034244454a0640a02c0b0220000d1003483c002802c241c050b5541300c210a25060258984500c800b180546401c01001080003506d808500203900175010341c0c085c4e001c2d8032203102098000030082ca910040d000616020010400241c221310701d02c4003503200f02e031050050b0301111b1820450a1040c084810b40c10003038004240d4454010f81480c0e801003182035041d5035284420314580c2d004480030450141c0d20920125680b404400c0d0704d481e0030742500e4541e507403464500040c0d07542e120b5000b0681800401018031422174401c40444015180d20101940c80b81918a403480780075205000da120204c004030300125081c200801135174201c42e0981e40300c800c088810785410b01103500c103480392020407101f444c003204562410480000c180c1070300d6006101c9985011001850000c4180d0a1480380c7c0d11800700a1024401e141c00ca010b403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 38142001 1250 38140751 38140787
    0x3070e040b0f0408070204020304060b090105120709050916030302031c020403020603062b0308060f03120414060d14060406230909150103050703030215010621060302030f0c040e03030601 82
    0xc3c0c0b0707541000090390054181c0294042d00000c00c00081080d15000a54220016036005403aa42c8440400541d091080032828582c0c3c0940820400304030350b0741001c2c3e00128148140c0b520b04c0480d0402c10841c031015041036000d070f4030014420b00c840c0c1d40d910120701d40c00010001103051070b040d40d0010b942440050f00f1180b040c1903d241d00303042e40440d0005c4103040c250191030040d4102c0715280103080751000b19085172003160864800a902e00b0080350060105600c0110316140900341001c88010401c0140d5141e0080400e2010b000c2d0780b00c0130302c1407204000200103102041d15040c0b04000564100d41c000c8480ca410503200351a407030300d83c40013081141008170703490701882c0c2c1c40114840c035200c4c0000c00c00201001c594000800c0c000e0120748901034a020303502347c0b2620a80e100b0b403070207806000e00c90b400000e0f020402c505c4151041814a2040808031640491801d9894001a02e0400c14111440303054028071080d1606107454456000380c0c15454001d1425031900b880060840d12403980c2103044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 38143251 1250 38142001 38142031
    0x17030606070303021809070309060e060105010804150b030d03050a1a01090b0d020d0204030606050108070c0b04030e030a0b09010203071b110d020a1d151804120201020f031503070e040b 81
    0x30170980342d10021001080503040340f100b8034108800402414010380c0070b840c41481d005080d500c1c52404121a81a00c2040c2c4900300f10f921550703a8402c5252829004c0c418190f0b44904080c0c0e5650300307001802c04050796079004100d604003600c0b0841100c030306021500301001c02c0d80d4001c0079643c000b1001d40444592103402d41d00c4883c460301e0140a03108401840300c41c0c03840024040200318169000794107581c4282c0e00c1541d02e41e56217400740c4000701302100240c10f84200ea000213000900c5042240d080c04409807d85106d00802d175202c001000c3c06540b0075201303940100400c034181d90711040010805030008039205510345680c84401e5000750100c00c00e4015075040b181d0030295100c80700749400030030003201012020901c0b007180703080010064428400f00010806050954589075116841101700c44042400c81c2c0c58035501c500e582c040110b00380301555000c0c0300c0c0c09900c42c80301002c1c4d17100c3e0302d42400010510b5543c904060030422039800c0407602c10581401c2c840410300c3c491310158494038203905081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 38144501 1250 38143251 38143267
    0x809011817040b07080403060b01020d052505030a020609012003010e060102011d01020a02011104050306060d0510090c0e070203120a020711100f0e0f0d080304020d0204060b071703060607030302 85
    0x900e202e0750300001e9050a0004008080008600080048a001c0d5404100b8010503800490b128541400728100184062044002851000295082080c00130304103248480a994480e4119000841c05e0805030b0401000c0011050003070042000c0d40c0f081c03040800483c449010707018844d0006005a40b8042007403000585e46900075403180b14005021206448000e41c514101800307540500b0440d80194203214400800400800075181640c00c020040c0c807041e82c4c1c02c01031000d00d082803070042c0c0e03c83c4a4032201d480000c0103481540d401500610781020504e041550014051801034401c90441d402044200307084246178040603008a0030b0400981e5542da6410004168040031a106038414a005501d1b140507400240041c0d10441e1511172250204006040129a482a42e182c582020040961400090307500000350743c010310082c1020310045564020604882c1c0c42d40101e0184100081d400c002c0c4020180e1b504491001d41621600c1e6240080100b41031b4080c16200505254011030924 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 38145751 1250 38144501 38144543
    0xf0605011d030f03040b03070906030c0905010503091203010f0306060506030405030915070b0c030f100501020c0d0213050106020325031d04090b09011a030c06090621150108090118 79
    0x38046040321801c0340e171a6502d4101105080d4010f58120b000301d0751200b400542c02d4041c0c0140503070315401c3c0c1c5802d1100d610b070100658181d80300410b41c070400c0c041c002c0903400d4035440501940c00307014000ca14900c1241186003000c00c58140380c0006100720024400c020014600204441c2188010f64080303000400b001c5c13005001d405100002412600c40b40200085060140c01951280f00d81c503042d4501d0f0b80b02c1d01d020b4001c280c094020715005800c03500c10710039907003401c4030f5180d0003610242500190311499401001102d0081c0c00110060b0000240d01c0725080c42c0111241f0540011182c1c0c40201c00c00d0354010705480c01099205c4100340182c038100715181c3d6254045079400d9040840d0450764604000303120700910400b00f101000152420b4800450f080001d035406000501401643c548400c100400c01346810a408000d110a1700000b045503440030561958020964003a4241c3d0500c41d01300090184200184483c0460b0700d040c00c1d00c3e201c3d0701c1060100d1071170b9403c00103400854003501400303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 38147001 1250 38145751 38145763
    0x60c0709020d0903080c0a0c06020a0e0301090c030501140108070501030903030207020306040506011a0a0905040e0a0f0501050f0c030c0d090c051009030b09190305160611070203010f0605011d03 85
    0x2200005202040e80e084400b0710303030404405180f0035600c0041c03d03610108140c0c1180a080c0c800800101e07113401620018080c0c0d40184040c5415040c0814000d026400103406d550f000c0008841c6000c01c544c0801c1080000d0003004502c094a2513a24400d40c1410481581d0300824440c032810940c41d40021800e260299044450307140c1c001d8203450340c0e403500d820402d40c0c50100b881601009500c0000110300b20b900e850a84404180300c3c5d440382560f520f01002c00010304a408896190307030068603242030004403d10211800e05100e80700100d180c1c40c101c0005aa000c40003082a0a045010404c1141b00500f0004803014020aa60300181940c001d04000b06d00510740d03041281c02500540e280e4403015001201c480459106d85101240b42e41c4a811154032a207034810070584506428622000007405040903000f05510040d42c00482400d5854260944040005003c81008000b030740c032040d07042c02c0c02030f2544100f200009010b02c40c6002d00081c0400908007081c620560200640d0005507828042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 38148251 1250 38147001 38147009
    0x106021f0908070f17160201080411041b0f030212010501030c03110f0c0606030304260a0602120601260601031104030606140102060708071407140d0f030b060f0306060c07 75
    0x26050f2180200e14110041e07042201c0c090700d00d001c40080e05801c402c2404111070000c40d041005408295060f40190f40c444806041103a50303001c41c00000301c071912644591910182c02c1218031442060785c00001e4121303200c650b5154105801001808040728481d40920f04403030003803030002501d2124031400c800410004a5070140038100045103a6900540000340c02d608100e0f030181d9541e508c852080650300e1090b480b852840c1c010387c2142c0804004021030b150401c07000001a10348001d000c2c0c1d41c21040f6840076074400d080151304c000b40702140d41e02240214024015507040030414440000499805400826040c100b43d08c1e190700c2d14650520303034290b50045a0000d4140a0191124600311036005004400c5005220f0000000e002a00c43c1c0c00311400780382143c0b54086a85020392114400fa0300c0700d0000d45038408100c000d134410100030041c1c42404410303981e411000518102e40201035440020f040d43c86450140701203814552030340d045035001201202c900c0e980b403800103640d40c208031aa600c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 38149501 1250 38148251 38148263
    0x604020312180d120306050a05090703020c0f01050708011404050403080a05060f0402070b041a070c08030a02092211040501050f0a02010b0607031e03020304030c0605040c05060a02010f140106021f09 87
    0x4000c00c01422602104070030044e520140080c2d0f40b2002031001c03280300b40c420254000d040e240030943e070900071b6009060840c0c100040c1c490310080f001c10b4500f5203030117640c00070001d517a0000420020b195081142c0b500c20b0704480920040c203058400030460340e07000d450031044581c2d40300811007030b681c0c40d04840c803000c4028000303540b01d15a601785115105030464003070b2544038904406488200da0b56040394419906502c0e134484621440d15191441c0d00b0082ca80c0403140d5080051a01c2580e90350718440025080402d41014003c401e040801034820b0a000600840c00501081c445680c00c641079903440c140c41904551914070080c022809002c000e040190001c40004858061551202404100814880c015040401c1ca110100d0803444200c5015002030104010240060602d0b0092034206003d58000c04266489200180460f445018049c1c00750b0354418117003458600307501548008100d4801d440388658941700000e9107a5843c010f50540d00600c0700c1e54a0000700403a440a40c006401c08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 38150751 1250 38149501 38149519
    0x1404080a061b020c01020d030c0302040905010321030225051612030f020c10030e0a050102040801020a09080a02010818010225021306030c090e2103010e0702060402031218 75
    0x41020300040580240b01c1c4429045041e5840d51203000151107100c102d4182e0040ca4a4198448210020b080161000040507000c1000143c981006e0092a0185005c0c810500f454910611051119001d0040e040d09250040c060000c4002d0484504101e210688011488154091803c5800d10101010b50444000c0301c11011038889032962a101c1003c1c407940740d1900039460901c3c203982e29000303080c146d548a2101200e51100300d1003a0400b00130a6401c40803505030407425510642a80c02c00d41180c07036141e6003c60001c050591240449000f0301c446c070003601101c0b2641e0002085040010101d90340860a03060400c507040c02541255100040307541700c170001a81403881e01300d6008028106900c07a00610714155035420b510b2150034102c03640098101e00c1035180081791381c0982464260030315035006a034403e0710032150400c11034441090004030142c1d00d6042c402488018200580036100315440f01e01048016100050440c904122203001c5580702c1c1214583c010340d01c0c44e021105078001c1c02e5a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 38152001 1250 38150751 38150753
    0x105040c0303020d030905280609030f0e060306030616020f150709090506010804060b040204090204091d030c060a0513050f010509010f09020607120315080f0607140a1404080a 77
    0x84a030035030740720b982680e0000940c540c088080c1d43e4042400b0f0000d4106004040140c41e6402411030b018000c01043d2912002985a0804540f21050240d02103402420390364401c5030300c960707a105244400c6a24505501301040402ea079514010002d1104000c01c9101182c0c01b4002c120f80901e0b09902e008840a121036070300009040707102a603080000c80c1c2c0201012460381e42d18003581d0b10418060f55850040d55403030706d038840034150200c80b644d00168200804201b400c82030000b400a00b2a042c004106030a4031b03608400400001030344001c8070740081c840c1c039000c1c01d004144580c00007440100802c180c2c0380d80c8510308156440d007500070070a1041d110103070019201900b101e446007180c0d01c020802c0002c00646107045d6621010000c6d8820b0007040035000242c1e500d0240003800d00c2a260001c5c0d103036803a40705601da42807581c00007034490344424800584040200f0030241d0011080c0362030440c06000d011011540d010f000c2000043c08007083d014070340d840409003035030020035022040b2400895a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 38153251 1250 38152001 38152013
    0x2906130f0801020c0c0406080a0b040c09060b0c100606020d140412061a100e04050c04080307151503020d02120c3003040e1602010b030304090506010e01030e1009060b03010504 77
    0x30350001c40d214005d45021000b0362405224110445103900c0190140c0545c0340d860741294078000b4021911002c0000020070031003254813544c2c000d003048018065130349400300c041c14980101c800d540b88455050000501c0386035804130700090300c4915810001190003411000c204c1c2802960400d610050020002d1414454150006000391020104103150852884240540c1c01d40010f40080840c81c500c00012f114281640101c0c2d00c10040760035541419110b413980d40c150b030f029040035100e40d0004046007040030820300c00c801c402d01c070301c54020281d00c4c959804a548a40504000f17803080e015291091a1008144901000d00000400c1e010040c02d0280ca4107807034424404034201e1510003558a507000d1100002110180d41410401c140d09595489000c100107610800c584119507d03868000101e0300c0030009480541040c410100385882c000c400149988c411041702c40c101341c00c00c00d0761040c800b0003084840368520016404920b4111a050500c00740450100440d010342c600400c10050000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 38154501 1250 38153251 38153257
    0x4030302220e15030d18050907080405070b03161409030601030605090c0301050402030330090114090d090312050702090a14010519090903141306032906130f080102 72
    0xb181c180c2c0da103409988001c0350b100d14140c150598440042c65200700c1c0698000070348450000007000c4403940b15004280300035016103551012030040300c06d1000f0090140b0440c0040c0410000f40c0341540b0340044080c4502c019050840103100c03c1070307007424568500f1b80480303080d80710223411612903513500d241280c01481e08a401c00700500990710000c10618041c024a40102d0b0001c1c0150f0802050b00342000394028460780e800505180340901004000c070081905100d402d840c0c00000f684040382c1040260801f0041120409030043c0039030b002e40c2c0d81c10215400c141e07604154003c0c040d041c0848166528800c0400c082d500c0900c0c1d00800c1801040c940003103001c02161410100d06907a504240f21120000c03080c2100380c580c41d14030521220225a01207a0381038028600215640800307005120fa5a0005000c0030300031000c3c410078040160180105600d0391f50021441d020303c50740081c559500d8003c240440d200303080000e01000102128401000a4050941c610740d2156407184024001c0d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 38155751 1250 38154501 38154509
    0x90c0e01110102040612111611040b0103050628080109080c150c070f0206040302040504050d0305010b03060310020f0f0f0307081308040303030c0c0b0a15090e0d05030403030222 78
    0x94041c19a080040d0703810b009542c00c48190352580562180c525803400041d280011f204e030768600d0203220f4514103800a50241d0720b030b83d000b108980210700c07100040c00151229404080e061504082c10300100f5203c088588401c2079a2412510b007980c0002d9554901e1011740d07200300384940c24010103405014207000103105118a0b401120aa00313590303079500a0f942e5048549400a520900011700030542c0c4515040784a440103003414a0140c490f0b0000e802c581e8155002c2d252544014002012aa09882400c0c0034004800649040d0700d030460009580e90b84085020040d40d40100e10f03003094426942c240c400c00301d04054800d0f04c41c0c2c11902c00740240c0d003086a10300009401c0001140c0d0b50fa01c1c0650f01c1c0c1d03416400140d072500d003905544069002e8000242414100041d02c2105c2001c80c101c0a001805004211004100d0305480e1600c1c259152042d0014205540b070682468006440080d04041030072032810030365100d59481c1800d800902036a4903207c5c1c03a0f8407d440d0043c4540d0600d030040306071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 38157001 1250 38155751 38155757
    0xe012f0708010c080403050a0509031002030108101b030f060b03011205060a0204031709130905060114011403130c0305010501060305100b090a06030209040b0301090c0e070c0b040b04020406090c0e01 87
    0x103150380d1040c903800e0360f60014010b404a01000041008a44100c0040c4009619414114505000200402d140c2000c00d456507240990100c018000e400051141000c0510b1051084c0084071000050304850b2141030809000d2540d10b040c07400100502e0f03003141000340800d00c41192a580e4a080d20803400b00441c100b201d050140d040000c01030500c07442070b0340903203401c154401080b41c44a800d0080c16404030214950007042c03400c0d065201c0e41c65019540310984a0f0010304215450000e001074860343c54110141800300300300904008403c80805c3e42c0d0300c5402e0880040900a00b03080c042000c80080e000540075500b004004034401c0e030542c02c000d000e0590710b10b4203101d60380e561410040600681c0c2c10194042600c00d02080707210f1103900034284c940801000044d590303034030303000103821100c20007000c0b40c1d4003a0401c800c000f076003d070070040e95000c62a42080785003803406070b1311610943c070000d1000300081e07840c1c40400c05640303403030344010f0240100040800c0030f0011400c01400b5164074405a80c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 38158251 1250 38157001 38157013
    0x201030507080c030402011404090e07051f080a050a09050a030e150705100c030f0212010e011406072603090a020901050a1d090a060c081008150402010e012f 69
    0x103414400e044840c402d0f00700566240c02c5413141d9004449100c1900d00c441640c480500c800700780340101e403164000e402d41e49030045c0050380c5000d09200700c0c8049664084180c40d107810318030202d00e401864040d440840700300000742559881d400e000080118140c06041442028586c2c820541c0056174060085000c4460740700c3c3c00400391928203148618031000307045422264011030b0390b0f21540c0051445010a0a010800f01c0d0100182c1c0100d030003040c0b0801a0303d03020341c0100b180388040e104450240000000d440c50031140702000c90310a12031150010035035441080840b00f0440c07144401240c04241120b490350301d051a80000399202c01c00c2d51705030b00c41e0000800002d01c1b80307020f204080403507150440c04c400c000c00404410020b1000100355036210b005026400c030002d0140e100fa41d8080b01c1e540c8903d0360304d0a100000c2d02000780c0329000a04681d01c0040d03034441e095441e40b090b9078060360900c3c050000500d5840100daa0554643d105206550b054a10040b0703620102185116120208200da034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 38159501 1250 38158251 38158261
    0x30504180c0c0b040609150c140c03040b0703170a020702011b120c030e04060303080106020601080a0506060402071b08010b18010509011202150301180b0f0a090509070503060c0702010305 82
    0x201d821906079a030100e15282007810005200d20159513109005000008000460f900c0708000c0c40030322000303088070381d0b070714101c1d0300c120354000b00c030041019032918805040107040d000241c1d4900c10750144401202c1d001c02c0c01c10800d44109581d8803003081219040c2803078102140400b0180d0411f01040740441c81c0c0500c254011000c1032000d600f120341003a46413040d007220220603586e0224100c0290102700e04021001c480392200d00403c0019840781d51030182c90740c50004000d05028040c4c220301c00715000741c1e06100201c0ca0001c0d045070007041c102c6c0c0c01a6580554500a5408003920301030032a00e40d40e007070300040c49100c10752105424001c19103010041d62502c810113441c060090258641c0800c08a0051100643c3c160b4900c80052015258140b4248000300010351a0000d034400704101030101e60285440145001d0740d11050130599100c1e001980d080c000410000e114050041c81d10b59580004d420101c040140600602d00502039401904190b000c00c1040e0b800640144c1c080303400c000200b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 38160751 1250 38159501 38159549
    0xd0605120105060a14040b18040b06030610030308060604031b0323060a020309010207020d0f0c0b0408030a0f1407060b0901050d0209010608070207150c060c11030904021b010603030504 81
    0xf440b4000050040d02940e0900c5181041143c00e002815000b9903240944410390319121030800e1a4411b02d8101582d51070185407003450410014203160103038200a00340038051015080c410f040d01d0741420300032050b82d24034011075540c1c0610703440600361828200384a001c0034107040030001560702600341551140040c202907442003040c0c0c611111264040d800040d0101115805541c010741e0443c00940b8005e0340e500014890340056005880308800500b00b002000382e0722486000900c0030044a0381418a0700002d03d4403802444e407140c060080d001c1d51030345054450529130780740703680b98407405440d00d500e0f04181008101354aa220300504038500007007814038098026181b40c680c0102890f802d03a00300402222200301c041c09000039445039034400304540705a5150030014029641d1412041140d600745034054988010194052140700461307060304c8180842240c8200720181c4c3e000d0f0b5a8940064400310403059042d14100780e501c4c1440110416038840010002c60b1900c1c8020007a244400b0070300d03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 38162001 1250 38160751 38160761
    0x40515010605120405010b220c081501030902010c0b07090501080a0b03030415050702090f0702010b12060c0703050f0d05181f0504060b1210290111030c030d06051201 73
    0x200464070030f102c05890314403900c12241d0303c03501c1400040381401c01100400d41801d00c0c0c80b25202d03c09030002c1103441e40d2080d4801c00c44051388a02c1c4c0040b40b81004040c10052070560341c0207504061702ca031600025a40a2900110b1590340b00b8105d82061071321a0004060543c02c1c040c8030b0001c1c41b450045944c19945000c7d903243d94000a020310300d8145045109090983c402c0440d1041c003606000c05009039441c801050700c10340400030301c0d070a2440c0040c4001d00b142c0c010610b2038440c04070140c107000281c200050495116903009a965514016820300759014020360050490390030b4002074018140724180c019038060343d111402c5006402c030704600c058448504400c001d819850310844204e00080329080030341c0060042e140001c5041c020300119080c0039200100c1c10281d8002404110018820310a201c1441d807401103c00c0c20114915541076880c481080507410030100960304032045a042c011a80510b902004990741c0f0040c00d54004050215032087c20311510f6115180b00e02c5203018050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 38163251 1250 38162001 38162009
    0x6090910051e1806010c0f24050f04030e0102010b1309031b0b0c030402040e01020d0b0a0f080c060d24030213110306130e190b0606040b030403030f091203020304051501 74
    0x80040f412040d00c01451038801d00078016410448044c002401045145e980d03091058050301126614101d50818008001c8580e154429501d240404004a00b003c40203105d401983c1440d002c81120001c03c0100e0240c9141410340c0d50207407110f00301c0e4034120900d0340b05440c00341c441d0b00d07540c486500602c50451002c1150740003901014200000400000101004560140c40100300160381007920844070300b2a0080c00072102e00c16901d206803c1d1515004082e407000f0010304942c140da560903d0031071074554000301d900900a8002150381d900840d0b00c3c1e0000980c12111602e05205541c5102d0000440182484142c0c000c100c001041818611507015190815286495040c61074483d6000c0c45641c01001c920810344540d030b0f48400e42034030001d01500c0340808034090364030859101800e0150031600041e206601c41d013030070401081114804000c4e81d07401038041c1400620221103140c0d0501070011030303000400143d03c0300c0703030120306907096800f03180154022000c030b48400e00d441c99034150081c001c0c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 38164501 1250 38163251 38163259
    0x105040203010b1219020d060c050c061609060c15020c0601090c020601061b050f0d05091903030c0803190207030809010509070303020715030204090905030c0f0601050f0603040206090910051e 84
    0x54540e1500101805d601222440907003000543c1206496581c01c550078030644600090002641c000c001001704009600b00408a002d110f03050504880075042d04400c1c0700d0070062042e6004d240302804162403140000c945141815940c4d45030318128661600801d004043d41c03a4a000d64100da07962000800c03d05860141c0c41f00d00c814216000b00d8500a610008102c0c0c16208200b04811404814042134078409110745419031a50030520801c060b010710b12a0350028926485030400219600001600c4000e402c001d545e580c9464242c0702e1448480d14064124a09000049400070544d100400c244642e00c079400810a90b12604040f030f84a128501c000340040e0320142e0107010440440722900300903505401c005241c50303a220b010100341e4465000039030301c81e040898000301001d018450071500a620070060512581000001031801c000101ea880c0900710100015085440300422200d012000501d10303ca24503041c580c0e80788400190040e64003806200c8400e055200c51100200f5103c90300130 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 38165751 1250 38164501 38164513
    0xa1109010b03040506040201110c1f0e04050405070e0405030c0d05070c0b0909010303050a0909050903070b07091a0a0c020d0609050d030908090d030207030803130b101202040b0f120105040203010b12 87
    0x140044a402e144101032282c9c90155003505c0c2c960386e039520000313404040d103c04400e80c421140400a095072100701480ca000340d05180c20000012004582c041c00d54812081b030401e41c8d101d03420200e285010b003940420040c400c1011000301160410064440a84203208401c0910344821014906015001d181c64004008070014000a030048024211072512131800f0110a951941041c040d107009841e501c405d60070000303440e41441200c2c840030368400700300d041c9040c07118030380995914022008020300441810105c0c280c00010700c80c00c14910b125400500c040c024031014103140c0f0003031040c0c42d022146d0348203401c1c850f5a103070b0190161081c690f400209c42c038201070304001881606494000218118082c03600080001103802018500803049034103c41d80550841c03030501c000d0880a801c882c0c0300e18100303600701301c900001000000d10690503900890f10780004004a07160b00c00202000b0382c840108030321445035840540c4a030b44950300072002803001560343c40a2103465007440b244803210750848 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 38167001 1250 38165751 38165753
    0x510050d02090a0b15160515040b0c030a060b0a030518010501050604031407030b18010b0414060d11041a01021209060306120307020301050403080702061e180309030a1109010b0304050604 82
    0x581c400b0700c88030409006800f516000c4600e410303c60f8080c20700100c0b2a8610004e40b006e012003040b140004070103d0a01231345904003a00c601c150b4510091080701189000000a2500ca502d504268000e207440429181c643d400042c025005c2d15007200c2074035551341440707400306003904140101c40c122100544840e180034103540764a030b4000c00344207005846100d180030000015020554075486141a001e40c200105200c251aa007514a80280c4501c214200302c00c94915403220b100d440e8006000300e445c0b01e82002c6500c0d00109260207400c000384d0240c0740c40b0100183d0b80141d0320100071603d007603003903c0103a4061051401e05000b151100d5402082c00d000066060a10b02e020180e00c2c84024101c0342862696800607080d100c04590450000e5009400d118002d50100041c5400c4125500c21b850b555640e001e008241810003015070780c18420000c03200000d178805004442d9000780181c103a42c0c900c255401c000e98505400041c590084c5d90301400000d9421208041c0c84c00346a0240c040d00c207685071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 38168251 1250 38167001 38167021
    0x10207030c06051e0406020a0c0e070806010309050c031c0201060e0f0103030e1306030807020a0501020a030212130f08071a0a020c010c06060b070b010501080a090807062a02010510050d0209 83
    0x4c810320504820911012281c000d902820280c0010f200075030080150050314542105001d005620510f100c0d28118140041c1c10b030042c44503036000e4000e04c4e0020711034000b801c005240c25800c9000366054040c64500d680c0c90a8803203c4c0910707584040c0c000b030180e142d40d407915140c0d152040303410b41d4080510a0043c40000c3c0320b008070600b0b01000a11040d9401d50700c080c41802c894080d88210b40a6000180c0c2c10110706080c001c0c0c000411007400070b41442402d548001c1d444440c00c40f100c04000c0c2000402c4c10040000c590351502406054400c00003540d100d07100789980e03107600c0c0119484038a1000d0400083c5821000f1154601e8055010f45840b0211000543d4411103c4008070361180d20390801007410721107100680b03492409040743c48620351410001604e4010040c1c1a0306020b0700b42180f01001c10050f004440c00300f83d1007000042e50b1642c1c021460003504000e280b921090304002d245a28682c0d05412150049445010b00321045550b1030805c020b404020100030f40180380703400010718180c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 38169501 1250 38168251 38168257
    0xc0703020a0803010b0301050a0506040806070e0a0b0c06040c090506012102090d050d08010801061a030405010605030f0708070806010f0608060d05030406030903080c07020901030210030f020a03060303020c010207030c0605 97
    0x110a00407903400d01040d0b598003005400c03d170010981d50070040010040340c500896880010714040e91114502420030f00d0543e12040014190700610262012600c030a0b00d500d02c0450090600d42021629000381c0000359881d50410746081e1104070901c1c40c0883e40c1e0006104450013800c0503107881c0c0320424914000012181c61784010508a03038240030845658031a1802d40509074446d0025260740c409800024082983c10782051500303a01d0148140800244030740300c00300a04d402c111103603c0b40e44500d0228094070304c5402c2a0f07014091a90ac20100100000b000c5080c0c0303403100b056504540d140c1500340e549000901c1941c510402c0408204443d500400656802c210003030b01c2c1b0f40007203842d40c480e40e107103038400e41c020130000b0b03569a607650503d580701524541101070042d13040d16007441500000c0c01984103000c042d02c01d02c20711003056042c5001e94030030170360152603900c19512840041c2014000300b02610095025010701c40307244403550300c04540c0c0003d40780d0104130b07620800d00f807200c11220340d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 38170751 1250 38169501 38169503
    0xf06041707050d08010302120708030a030e0c0301020403080301080d050702010f0c03020c090c03072705060a1205131e0b0a0b06040503010501090614010203040806010501080a0b0603190b0604030201080c07 90
    0x340040248202003070782031151640c02d6155407a8119a03516604c10312003281030140003501c9680042c42c051008003404403c031440040503107004515141c18030540c5041091079a401585907100003000000c1084032006541202d4450701900d41645518000b0b035018401e00c240240000c40c3c030103000c0e0403240141c4001810724002c1c8103c03800301e01d071000454003100e01031341c842100324000300800c0b10f0280d0040701030700c07217410744584100d0000081440c0c0348548254010140b15140c0400d00c0030791144124203134a1850740143c414480d03410402ca504403e007280000561314525101400b445010703040341903a0705540d00881440f02c580e100241c80b40104142500140e001504110000d425a402d000b1180038207111240021050710b41561000501c05d00034426040d5002072100700043c0c00e02250a41c110740c400c0c01d14101c55a50300355560010f0001c2c0090f103500503408014400071281180300d03e0f03950b02286000300407031030b858010401140140d102c02030000308008001840240781c50060300c016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 38172001 1250 38170751 38170793
    0x6090f030a0f180e1e1501051b25030201030c09030308060904020303221d060d03030b0d020a03080a02160b0d02210106020a150c050f071704060201090b090f0604 71
    0xa0b41310010341c41c00c490251003249020441e2048614500d0341d80f0035864200c142110a00034414564001030024002c1a41085031070548825000201d00c0a22015442c1da043e40611041003807991412038040c2100e000907030000389000007180d400d81c042c0d4001420383e40c1644548103c0d07a1f9242c1000b4180f81c0040040360540800d110101e44d10607080c0000302062840c0d105000a0b505008801d4000c1504120404242180505006442c0c40380011a01115050700e40400d198030a4004110844a0344100a401c081000800000c0c444000c0241568103019420b0310701c80004426070000d0820340c1e00405042c5001041441601720a03030340100400405450f42ea601c980b0f42c200004440b072402d034000700150300012603040030480b02e184260f041c1070003010100103120100c0b000503d14025030840b40c09a810006586062140c845100404104000c02e515a00c54507048c009000c0c090022048400044040c04210070410108200c4403400100008080341d0303503203440b041d400c550710544c4190b00c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 38173251 1250 38172001 38172047
    0x60f0c0c03070f09050a0507050703120b0d0b01090e1204140102010f0204081c030c0903170d090606050102010b01020c150a050c0106082103060307140303041706090f030a0f 76
    0x200c0c0e10240000c10041c100c50341c035098031900d0301d8050310a8850040c0b14580b51072810301000711064006041c5c1e46901e406180403454000c1750540320004106854010707a010707083e0b80c0c400c402c01c004075480605a03402e08106101c0648101c81a9683d01410294130440110600080c031605500341303888203400605200205a900014115200301c3e889a00003085c0c0e07070000c040844080608035890003001d601881d0401003440000c1004000022a000c002c00c241030f44180a042000010306444044202d00002c001c2100c0910703082004020030b00c036050155081102450302e079030000c02c0e54540034001401070a100c40d01c20700f001e0700c0e0343c0c0103144500c180031081c040d030f103401d030030910800f005004000c00901080820551050101039803c3c2484400c01040040184d60344000c680c0d0b0088406542e100721030016060f000034114000c54206030252007911000201d41680040ea280c0142514025a16840d80f0603203050348a11501c900e41c00418405480110228402c08811b1000404105001d0b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 38174501 1250 38173251 38173273
    0x60309010b04060305030702030609070b0d0c0c06050a090506010602070303080a0209010903050f0703051612030c0809100314010806041a04020301200d11030112080d060f080a03031109060f0c 84
    0xb00b00c0d00300d80c100f618150b10100c1d00e4000c504042080c26048030500c40100600c074039100b04501d00340310b410b2880000d680c492140040181c016242c07001d80c01e03030159003442949001410074000700345800701601c440c801e0b50b0002401a0000c520441034a0b0140e840c08207130790344e501c070701000303135020321402d81c100400304d0800004145c061180c0302c655a81c50010f02149407179030070035a00c1c0c0301286940340c01080c01120304010000e440c1c85c0802801c1d41c1800c1a40301c00344542801000d50040c0481540c000f10a08080002c041d0305501003100c481d00c00d40c0c01804c9903215150f251f61a80203e6000b01647c01c1d080007220325059803070b40075038400e10040c0081803110503040d401108545e20625550300c1c603408100f0b0031440d20359000d03840040303040300005400c5600d040d0f82080c400f443c030003001d41400000143d403100c2405a4201202a189c0c0c202c2d68549150ba4201c0b4640e00d481c4441c05400007480c125091050720b0a51044442295004080c5401c0051007507840400d68003044c0884074903c200c105002c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 38175751 1250 38174501 38174509
    0x80603070816030c0b0f090f0f060f0d05090607020a0f110604030809030c010f0f03090212030304080901080a0b31060b0307090b190806061b0c040c0c020f060309010b 73
    0x2440000d410042c4060034594940001440010303041000040411310020341000c0031a03003a10102d1904681009100704a42e001c00c03240080ca14495410550010f00060b20f440094001d143e000080d08003000241d4542c0b0200d606ca5600b0f940940060300401040004201d008294040320350281c8040e002c9038184038002a800d500644c4215100500860f80f180d6501c1c0038440925108402c0c203040e0301c22034600034000c180c0700d48288250103240d1340300020800d5403a10400103c0320801141100e030381c0e0505003808100d136040740365014001856000020364807146405106000031020f000900740e60003c4413110624a0018078000e62881b401d81c2c0803c0d50051401048014645400707204d94a042c0f41000914501ea0b6403c00010311800704031549503160002c1298821242500e04840f8503154480003801910441d5000400e503122000046164400403c00100b0450200da0030003160740b81d20b009480113013001130003950000b1402d000444500340f0800656202614100004024000c3c20010b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 38177001 1250 38175751 38175763
    0x10b031f0e10030303060506031b0c03070501060b09030606010903050c04051302040f0614011d04022d0a03050105180601030b0a0504110304020307090b0a09020c070312030207050d050406020d0806030708 89
    0x2102c000301c006400c00615800d44140781c094903084d116945145000d01d0a1110640790801040c2404000642c01500e0030041c82540d100507031000003440707080d6450f00e0030b01d0540c102d000f0b400e04c02d004480100310658000c40100c1c0440e40c0c00300243c050500c06070200001401c004020403003262518103040c0041e5903921034030080842500000521301c2c104105503403007404120303019042c13264034540d007142c980a01106006c00f1a00304c80159443c2400030284000305000008140034034240550b0203101841c00f006002d0a080c65541080ba603a41c0320100000d001b0713041000d01c202d0302100d0106519500c00e8210507000c1c1e8001d0201884555240301003822281d400101e500741003004014442180750900005c0700400100c1c000f448000c03038032000039a0104140c844c0581c201e90002e200740e00304209010490086400c8505000c0c1ea00c4220b1016004e588004000c0798680030750607290300346d1402002543d09441e101d03402080b9640c8200b40075984004090001c2d40e140c400c880d030002d0f04000401030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 38178251 1250 38177001 38177011
    0x3040206160f030206060f01300c1d010203120c1b030406030605030609060405070e04030c0b0c030103120f050d090f020307030302030a021504021f0e03010f15050108010b031f0e 78
    0x100102c1c0d11142c10000d0030b01101410003441070f1140c1140c030700a40e0b4019217107921440d14124482003541881c00c0b020994542500110b03007941001000c0c40c4251304109058800f000032070303050303000a500100480e1644101600b0700c406080b484042403400000d1005002c0e4100750140d8803000b1001300e4421482e5400c154051700000b40c6540b004d2040e42002d001c225040078141008041e0b030f04207075541c030380c80d44118011170809500810004040c0741c846d0100301c14617034000010480751308002501040c5a4002d000c25245001d1000c171000764907100e0400c41c00a440a66155414602d094030000701500498006a814003d01e1048802680c4c0510021005510940045d9990510010b012b41404000e021088a0640260402015855000c10343d19001080d02c2c2c1030780d500042e144d003511190203003204e83c2c0d0103610308070b19158148950340c010100b51801007426500b5503603c0004480e4841c00b40140b0000340004d01c0030803480000038881c014240c1c25142881c44440e11410303405580001161 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 38179501 1250 38178251 38178263
    0x712060f05030c1903030503092a0906090403080c030709050310050a1401060203070305300603070b0c0c06091513030c0b04140108070e0d0609060c030207030f03020304020616 77
    0x40c08110500e0104849a503040c02591100c0b8102410071103104603c0700e5100240920000000240c2c0f03030308040c01101a114105041c824078a401c401d5800352480c2d480c2407145c01810008003142180c40c00d0b034170203072003180e00d6500c8410307581d2100d0000c100703600003500d54010700070b508001249070b0fa000d00008942071500c07000028245449800541070702c0d641011100c0f9002044010710041e64044129480385816041c140e94510382104000c1d862410311017401c1401d0b901504400b0b01c1c01610407010b02901c0120102ca01c000c1d240c0e507a5034094494030506200c0756204011007070741428038001410500c00c004098160401d03e12f003109000b903202c0c1c7e0f400d8250020401040c41000544205032016007141da0b145c41c2041c3c1065030710202c608482502905200003000054121071040382116062140a40b04403025040c502d481005422401d41c02c440150401441440b1340b0701c0f034403c7c0c41007580c0644d01c1401070f170f000e08410303030080d40041c00c00d0740c00c0300c1c04105148a0b105440e44141400b44198 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 38180751 1250 38179501 38179529
    0x90302010b04050a060b19090b040602060406140702071208040e07020307120203030112030302030603010f0609090c0e130210030b15070b070e0619020102071a0103031b02060d05071206 81
    0x8030420046910013444c5160040c40c1041c1801514403600948400c881c91a2024588100c54801540c554030b01e40e0012650b02000900820743d11340c007180d0385001e03074402c110600c00c078a22034002c441544d404a4041d03006a016110400001c804510040003082c01115428601604c034429880b03400310458194002d0790001031071004114020852113003400c02c1f44041d5040d5414540081214082d1010181c1015004004101c103658294020403403a400c2d00801c1101598400e2000c01a00d250281075500380c0009000050201601c9001481414200300e00d00c152051a801c000518607100000c1040603501c418130f1009441c1e010715180c1030040c555071141c49008078a02074210074401031101041000c0110446059202c400648d80c1501035500140750125800c5401c0b8020f01031048050308000440e07443d41440c10070f620700e89041e64041c0d520030030248028121a4041802608020340142041081010505c80395000e180c200c40e862038102241c1c1d1414082a064400035000b90103024606 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 38182001 1250 38180751 38180771
    0xf05010608070201020301140103050c0d050106020d200d21051302040c0f02070302100c050303010306021207080c09040203060103060302060c010e0712020102030d0b01050906030103060204050319110d0c0909030201 94
    0x60b84858a48020351556040411100b04204800c00181c10300d911080440e6921030044240d900860849030100642d603074072000255103031410701e2640042071a0000c90400c032005603004080710410b0500400910181005c12602807502d0440ea10602c0c2c9c5100c03d0803050b0b03926004450185020041160f545020790040000b01c600301910042400140c46841b000d2680100344501243e8040795031840d040c0001609444940c8a80e800400a01002002008120941d07020341140c5400c03804451081d526240199465103003500d5460f089101441402501e240c550002d40d40408103240118850b9504d0340420350540104c18400e840340d440e100e0b406900b02d0200240302c000c2401c0c4440b01203290030b580001c0c0d100d00c10340400c043d20300d0f01c510500046900034001c903000c000300604030030313501e695034282100290400d0141600ca8050b40c41808013225000c02c4100c034880d089000064a400d06004111800c0c085402c1100c0b050540c0c60b00090908103841010072160090700041411880 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 38183251 1250 38182001 38182007
    0xa020705060f0405061305030f0f04140303090102030d090203070b120a1b050904050408090303031006140702060f090f040216140d02060f0702010e07030f0201120506100507020402070203010f050106 87
    0xc003089820003002c4200710210302c0000d401c50700110403226038030407021b4900f445400e610500300912942c8800007404202c10741682d0051048510b030b002086003114129040544078401c0145450060f401400300c498100700b20380c08400c04a10080071904125039070350180c0110b4101010480310544d80004102d0b40310000d000b40c4102040080c41130300c004d2280079024200b40525070300b441c0501d40d11000102040f84480c2104d92110300181165107070b01c5d0000003e0000310340b900030000040e64155107003208072006402c5d6042c080e8010105420f00c0e201d01341c40c0c56507800501032964003400c01d80202d030a5803101e100601c8074a0082c04030010b10f05150914998040d03180c0d50910382d5500142c8072880c9a540440e0b00c0f40c11051040025600741c8030600101e0142c10805000100c50207032043c000304101c500344000118920030b88414040030302d50000b480440d60116001504101890801840f0522510091141c588000c0005041c01c90503004a8211400700c2114000650341c0c01c018081950 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 38184501 1250 38183251 38183263
    0xd0807032003011403010e01050c070c0602031219150608100e011401050705210315010e1807020307081215100507060908040510021005060a050a051905090a020705 72
    0x9400030400807040841080c0d15814481441031a40e1694082c5100c40680e13020b42080982d1507541d4001e07c84d90601007a41d40480d481100115007005456600090641c00441554003450342030700c0d11011a602d100c12180b1440303a0140b11500960b9038421000920302400000b00a131401e80e40c0e030407084c0740a0012440c1800d0681007000144e81800040100c04490411340008002c20328159840d4040351070407d240c03000c040c2d004081040800c00b140341d001000c40255204070441203100e103c011003000150f4094041c200f00f9030b008064030400c0c2c9000c0c0303078039042943c000c5110701c110b034a0142c16450300052904400c40c0f001d1540750000a01207042c0740400c60105c0c0201c00c40d401a0080c00c07005000d4054401c4100c003c5c8500e44a00483c01448956000d071402024050144c40342004c0d81c0e10005e482e001d03444c400c0b0028034070304000f051007800c000020301700303481c0017500104942d0b04240030481401c803a40d0341950081c0f031803440800c0c907441715000d05001d02c5143e0000760711070100b841c04e142401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 38185751 1250 38184501 38184521
    0x9051c020123010909020402090303040305010b0a09060b03070c0503040503070f080c01050f040e040602091003020703110c01140c0703080c060702060105010c0816050c0910030b0a05010308120c09030d080703 91
    0x81024114150300302e200540740d411901c29040009008010b440460702038041c2044d001d500d408080f500000340041900281a062012100744008039144e014142c00c45406000f4200c07591018000074403498042e0102402c00360080041342d04069070b840c00a0304e848210340241d030304020f180000700064007040108056061003402c10b141070000e044290841c0d805588502d50100146a0100d401e21019604071500c0c90390180101032041e48540b0068060342c00042d0480010b06584c161001380140070540181200c0705940d07060303240b07020307a040d004250011040250180982840000010074000c000e211545501d0701400c424641403102a0030010705034846070610840d8204a00000c00c10001c44001c4100003000900011082c2040c030304e0200d0000c555500023030100d05010702c04c00b0480300741084a2107030800c500b1079500c1c0f582000655400f848003c4c2044d1080c41a50908416641544d0b071141c10710b0180c038204040b07580000c2ca802d403154046004151f80d04140142142c0c10301600ea011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 38187001 1250 38185751 38185781
    0x4060306080304061b03030f090602091002010506030c0f0f030a030314010602060106021005090a0c09050919110405040807061e05010603091a060612100501081311011209051c0201 79
    0x1131038500050601003c240042c890324600319000f0301018041d0344600360325481d61000304031f414501e14010000303502813611684200e05100c03d40542c0c03403050080c544600070290190141e010303144280075180c00040c1c00b00fa07100d9100c4c00d01c610562010050f141c0414040c0e40c020800c0398001c030300d40503a9070b0b060b000384085400c00001801b8043d0006207d0100c01c0481000040d5503031034a00041c02d1548280008007442e02c110f1001801c081c180d04a24062030210f0b081d10020500b40d4a44003000e450004020b02c130a05151003030500d0701d0a680543c1d032042c000c400c8240b40841039615242101c60742000c01745142d00d80300410071251542e12403940900740e0342c10100118070440e05c0741280310580801248581c6c2c446800146a0348a0400381d980c02120b40a421140e820061065092041e007401218000740c80003002410140728030203104a401d400000c0c00324501003000044640094114000f5002c94403010302c000000c81c00c10062140300c82500c2c0e182d81851384030300020b00b034401d400170755202 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 38188251 1250 38187001 38187007
    0x6060501180302061e07051c170105060a020c03030a17010e010b191b050a0620390d020f010606120b030106080303010e040c080d12020711090c040603060803 69
    0x24100d4035019040940f60100e581035211101d4a07074503030005059400315000500041840c2040083c002420380341c0522a4035000403401c00c82c4400c03200d020300c0c02c502070a80c2810400400513401c1c03000045c8590f4280b4410340e0051400c0801080c40d5520282c030702d00c0006d1903640f1034101c103d60040c0c5140505440d07506440c1c15450200402e0182c0108881c20b5001450b10140030701050080c01c2ca80000180480708003200b88440c2021502d81507200c005640352424032000d2040071f41070703000140c2d690b0f11841010b82080131038480243d4044103040780c401d080c2c4819044042180d60340e1440b0f142012000c0051600401c0180024104102301c0d00c00e50407a8101a01808801c3c1c0000c402d0a00740410200000c00107000c1c000640500381d43e078030400c0d02c1d0000100100340ca03030261050034462070180d005030000d40e03951600c4550b18901081d0f0200082c0c44048501c42c001000c0e001044800e0140112403a1040d03503800103008001c09030b4142c2000080010100080d9405028000007010a44042d42c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 38189501 1250 38188251 38188277
    0xd0c0f0509010e060c060103031e0203090d1e0b0a020705060603010b0a030807030509060d0b0f12030a0c050a0c0602010605100908190204140c09030f010b030a0201210509060117010c02070603051504020309060406060501 96
    0x41c0c40d0003b60700090480305801c0d6021198036908000050594110300603400905003102440020741c0018429a20390181d00c0001d444c500f4140113240c020840600155040d0b80b558036002400c1c2c120210031410420202f06000300c55a807440a032580800c11040007402801c42e1081211b04003400705c1842c061141c1d1224220540750100c1912442d10b110308001c51b65101030300e0b200f4100500d1182c0184034650034031000c2100c070b03030550241055038400c4d034003001180483e01054540410383c1c40384030200d078030241c0180525405940d0080d581440030b40045415424411100b94040c005c644407030440c0b0011482e54124642000001c4841003400020000f84a40c2c0011a45482500340040d0500801401c051500c0d28001220381102c60b80d0380c030400481c104000959283c04080c070813545d05d01c0020302003030b049010604c03a03204501619001000780c14030b0070300241e02910b401031400c0d003401140e04403000981c80d03500007580305411010280c00146030078545502150a6604014100031026424071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 38190751 1250 38189501 38189509
    0x1401050d1106130512060f090a15111b0105040210030b030309060304050312011203080f0705120916060c0b01090209060301030f150903050d0c0f0509010e060c060103031e020309 78
    0x5594000999026682c0d00440038600da003590340e58082d40d0801001c451032500c440001c01c8090080844a455408684423081810303910994050090101c0300030300034a44c40c03400b031540b0000c402181c4c80203d90034030b8503001c1a030b191082c0e02071212965075115000c00085140c0308490302001d00b89401d08001d84205103011994a00518043c140240000800b0505100c7c08005841080d2444412555590f03101c0c10740c1035005400c0301085010405540120b1141070101709001c0c807560b2640d45890811240804a100020018254980c40e01031a001c90b00300c2c8090404600c0174060307607100d0b0880c0011600d070000251005a01003030722244140150380140c0d95101c22281140d4000108244c10300d101d05002d03104040200c40d1010151500819204041d0814060014010406400c2008000040e42036078100768002c407007000140d0400440c01158040e0484021601003c1c0c802401c0c510480310071450030740282c200b68041001e401200388131501d081030010684110b48003450a04400f00301103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 38192001 1250 38190751 38190773
    0x20304030602070c09090c03150c080402210601080c091303020a1211030703080f0709050306010b0f0c030d09020a1a030106050f09090f071803050a030f02030d06091401050d 76
    0x204910340000d090030031300c070042220f00054001203d0403c0400420329040c500101d0500c01121030000c00c4d000e900c0b51090174400c2110880554036103e415960302e508100c1b45050511000e0310740d090b200e506644002041100c14041d108210052010b030101e41d00304021074034001d284c240c3d640b007002c04140c0000c2e40071550500540e03000540c10a0080203010a407040c8075580c82c41d80c1e041c030003c0b070381400f4184e00c4200d082c02001e42281c1c0c0700310b644804808468046060040c0c03509540500010000e10071100010440700402c44445401c0105142030581541c0c000454180e813241c40f00c2c2c1502c2540f514001c9100105013a031800b1812000300d0b0040c03a8a40014400d11040c84400324151840103907140031a040d000c00180382450a2420010b04c141d1500140e03081c00006118141600100b40200607040581c1e80040040c89061040e41c2c003240c0c0005038640780c40442c04140a0815403001d5402005d01929020303801013101d100620b81102c000c90b0581c4072911a2007405941408036a54103d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 38193251 1250 38192001 38192003
    0x6020f06100605090102030d0e010f1823010207020a080106060206010f0303140304020406030203030c101503050a110a0503070f09140106050306010c170d0501170c01051b1e0f100c02030403 83
    0x30780c42d9040d084c0180e0650281503a0101c1c2d842c20004ca11002c4001941700c2d032480214010200318446081c505030481d00310368500207090008680c0249a20729440d41501c01581c08040054034200700340c1d011070100602d95021200c941e445140034000035405100a50143c0740b0704010f803088c6032640c0c4004101d0711803054a10183c400000202e4155280c5807c942c0145401a080f039503a0b0480f02d0502e81d41c0c131002002003c4072803801000390540040d00001c88200c4c2c0c0c00000508041021b621582c0040e106031010b0365111050b00400101510700380300d070701c1c010614480c05100f000e2a10700e85034182c41c64081c90140074961480140003494210003945c0d0403489c01c2c6420503c1000a00d403000d0f030219a1203031141001800f00302d0007090400d81d00030340c1c185c6011080c0d100c0c0e461078074200d0964800110030300c40c1c0451030502159040011449045902000c6a81120034983e58441c0d401000e07042d1411030305050b080341e0394100f80c9050030414084401103043c810080c1901d0300030020341b030780101c2c04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 38194501 1250 38193251 38193257
    0x3020a021c050906211008070605090d0501050c0c06060904020d030f03060e130215040b03060d06060b070807140601081f0212150a080102090a0905070c05060c0406020f061006 77
    0xa4070070030320700c580240d40510401034000c6541c0c2821100c40003811100601140d449103825001031501e103403002110f02281c84820007005c40c9410010151802e800050500b40c01500e0000610b02183d0240642802000c000d03a0b640d03035500d0124521030820000506550040140205010042c1c60f030a410808150b05032400460040c4c1c40d88080f00030303210a9200c1c1a06290300d100b800740781c540100030b01034007a00c00c95240411040d554080c050302d0140e4400d403401d52405200041071400d29041c40e8140a00ca00d00014005071030b13040707a110700d41004105403a85000460240100300c1c0c5002849800d10b010b20007090b041d0725082e0030b00c0e5111841524200440368200e0300d0303050ba800ca0f40684d500301004066898441c548071407a580100c07102150b0a02c2441c590400044186040c8201c1e511502c002e425082d41d40d0500c000c01c1d0243c40003620f01d030104101c00392a41c0100e0410b000c414000d9900b03c2d0502d0b55030f0b2178020001d1904d01ca00d0000484c0380c10040070b101484810011420407078003141 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 38195751 1250 38194501 38194543
    0x103050601020f0129090c12040c0906031b090b09070f02150408030601080c03090a031803061a04150819031701030b09010c0c1115090d080c060703020a02 68
    0x100403800c00046164881d001c0d0f00302105402d000804403401d11081740e5005d0fa402c01103105004121505105880e48420608104415925030407101c1507154414004e400240041d6039503c882c008688030765200b9142e903054504c4c200e01d1080c691403c00001c15214a00b0702c540b01142c0300040392030f04050545014819000d4411071643d0092050141c100b4418158000b40d03d014100040b2340d03841240c5490018071604001452465841c059a00601011000f0101d24036a9601038945c89240008c0c0b25903d44504000800149540503048403c2006154107590040d10002d10007030720810060180801007990040c0500341d0006404040b10201980784040e99806040942e00120f0052200c2e550810303d000110a0001011400340140c103408020080810780301c000f1214210014030090089060301d040c00d0030740c034144484444540619440c18074229420000503201008100100c6281201003903400400c1c01c2440300395070003003603402c0562400358908002034490241e4407080d20300400039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 38197001 1250 38195751 38195761
    0x102010b0409081206011812060b030304150804081201080109142103061302070b041b0f030b0711030a020a030206010e01030c030b07020703240e07061416150603030f03020f030402010305 82
    0x103031000e100e2051f141e10032489440d00c9000340b5400c80040341d0b041d56110308003c50b001c207605001040b2421295540c6116510f00d04002084503810300240c02070300c01c1c3d1018841c204400181815450081184200015034140140b81c595205003131400320582c103400101507001455030303844c400c10307010b000c1e841060740c9e03a41c0303420001d940883c640c0e0400c10707550701c0480c03241c080102e81200140130b180104141581c44004266826000c0454081e04641c502c0208040000407600d881c0070b5040401d5007030401b80400d41c0e054ed6882d50700000c0410006a104940c803a0a040d01408014090f180c02040c084007981103495102800c0f03143d10008004490030317400502651302c00c4c404100030b10742c041c1e40d00b40c084645a500b81e032000075681c0b101031a1480c25040c0200b40600040403001c41d40310b5114070b07501040455000d10680c0250b0b4450700d08088140030080001c00700c45000034122400300e030000707070542541402004404116441018184108a55241045841d0949500550900c0e004c1401da0360 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 38198251 1250 38197001 38197007
    0x60f030a1104230c090909060103020d02130207020d080901120212040201050f1309090b0906040b0a0b0117090303011a03010b0d050406090206130303021b09040b070215070305060102010b040908120601 88
    0x682d075203d4403031a92028880c1c05014400184032a100c2110741070542d032607030144142c07962070a03c4001e501242002000c4d005041072980c0d24500e1402e007500505101032130300443c2d0507a280c139034121660341c0002000c0b84a580c100348099000310f5440011801c0c00c14071020714100c980040d0002c0c1c1030000c0460180b00849010040311241c02d00a8940307841103030b0790b1800d40041d000d0480d04a80081101001a00e0454001402c80c8110340016001ca0140c40d400c9085000b0102401c1850400c80441014880740d52021485c3d030107003d20400540c2e40350f00d490090b00074149103070114611142c0400040091520980981d0500d5807105000165500c2c1d600c1c00b94028620051b0003500711001103110b9240510302683d110449010b9002d035825040204288110740208102c400c0c0c0c0300030150003040204642c3c54455600c4181e60040310103d4640d213910181c08902100c403a400603858108002d01540d084c010803d985000780c4081c010319003503503500000343c002d4981ca20142c00d0f0b44800161540c0c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 38199501 1250 38198251 38198291
    0xb090402040b040b040906120b270a0803040b090c03060103080c10090302010e0105010510090b07110301092303310522060e040b190902030102030f060f030a1104 71
    0x14012a02d95a45945904900139508940700301032149260200c000f40b40c1c00480745031141c482e84034810000036a1045001415003c4525400328849200b0300d00c285d44031420003038000c4a034003d12384a078481c5810300d031401c0c070001c0c01401e608013074104c4050201c06071070005046042d13a51241d98503884003c440c0b00146007111044400c440d00341002c80380d00c207054041d4800488140821300034402a0b07215020f100304040c1a05410002801c2840d00300f105006602c0a081e68078490944c0106c6481803100082c02d50341642c009860440314400108520103007030b0301174503000c900e040c055410301003640c401c081d400c0814522000e4040000c14031000141e26002c0c448040c1500034070404d01002040d90740100703d0304401c10340403407602c0c1c818003182c001500441d01c0c1c1b15a5010060807025a54100e407901040300210941c00d8094070348440a0050f87c0138006103108a200c01c440c0041482c1a104000d4044942d43c0303a10302036000f03d0107888c003041150000308411174081c0d90100b02611788500d9840449 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 38200751 1250 38199501 38199509
    0x20307030c0305010f0b0a0501140c1605130c020a08030402010315060306080106060905130b010516050d1d010807030e0a0510020307090b16020d1a040f03110304050108010b09040204 80
    0x802044008800c0021042540d019207000750300030804041a9800c44086584915810380c0c024402c1504025a61103038204000b00c5c1d515065543c1090510f80c000c0703142507a10071460422520821090010341000c1c01c0342074031038114102c20702854681010181d240c0c100440301600b81e1078000000341c21359000790401d616080b0030780700c401c00b0543d80d800001c00400c03042c01040c60300d508148001030260301c600c0450064400003001d0100307841051030010010540c0500c583e06008090000a020500703c014a5560314002d030094641c8034542da400801400d081c4060300c40402c44c0d036141b803e199910103403080d802101d03810005040b0a00481d010302d80000d800d0020424401c45100c18407880700394024600888a40e01c1c4c004205e5191900c0107024040d4000e5501c8d0701110584140c098541100032451183c024481c0c001da607014803103c5034190100303e5050742c000d02c007044a54100765000302007042c50150080910b04050426000920450040c070455a03c80400703e144a507079070b1640d0480e0010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 38202001 1250 38200751 38200753
    0x8070204052d070207060e01080606070507050d12020607050304111e030a05010f060602120d021e0a0309030f080c0a0c02040f18050705041a01050c010f02031009050a020f04061103070203 82
    0x6806074400101002c0c1c401c842d141c0050045400008405001b000c815008a2058440b80e125540701002e00403180c01105013a01c1e0f522a40300001241e4aa8440c01080b60b4020b46038082e00c0d100c1d110700070b8a402d07170143c04281048420402c01c00411403201c4419000a0225001c4040241380e03039001c082c040c0c08008840d8075020300249201004415880341d0645000804c1c01d20200c1d9503001309988803d030582644000207020000d46090a01d01d03030041031013204400364414101c5000d5120f5120303400c9501c101010940d01e1200c242815004550948212000c1c43c02064a01c1c1a4803140417034043c2c0c2507880c080c020209100811503985030403003034a48500c00070420900700790030203130706140c0d1052200b5601401525001325683c02c060040d02c000c11400c0080c403500e4502c0c207004450f00d50082403a00255580c41c0b910b003240385d00c00d00045d4014080207919402072030034071001000b201c1c0080c2c42d1415042c41088011040d00c01041034a0407200b0506001c544440b032440380c1421031203075000081d41 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 38203251 1250 38202001 38202061
    0xc1e1b0816020a090e060a0612140a0b070f030b03010b060901112103010e0a050702060402010e0609030105010b1c18030305130609120311090906060a020a0606090902030f06040807020405 82
    0x7042d425980185d408030300c0c00c400c80f4041e031100d40d500320482d041401045c2d2100701001d04a004202070494a80301c0e43d42d80d10072622054403a403620030500406a83d1040041c8102e0f03c011203166050140d99000d0a04034000c00c1441c01b010700090032403090038166410b0204045032070319400d0080c440783c41d41250308003014040c00008000754201d036109000c0c0500901211020548904851061901c10700c0d60380c00501c4984c17120740056664400d51030070035601071805c111840d907548082c00ba4034001e00d1032810203070f1181d0003598406039409004100950b0703949004208811241d0100012221a40505000405440d1610304070405d505c600c0300680303614140150581042000910350307551f540c190ba8204050240142c0b6811103126152a02d6400034400010413800e18000c4000d2281e0300c070500441e003032700e100b07951944151030741603015814650341c582c202e070158281030144000c0508003202030025482c241c1d40e54074080c020306501038061079468000680d400e5425010034800b031290100705d09 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 38204501 1250 38203251 38203259
    0x5100803040807090e150109050421030e07060203090a091a03120301080d031b03050a0f090c03050c06030405070614120108030a140301060504090216060c1e1b0816020a 74
    0x390310302c55441954813407840c02800c4514030340d000c45c0034080d600c49030865038a103907c3c0020040203024058000e5a1030f814a0546051540b954034040c0100c44036034401041030a01d0304806801c2000d43e902580942d0001c1041d094a941e802c6c800e03000307661140800150b412010a407503804660441c0c9580c2d0180300780010b120b808043da9024604a490300c00840c0d004541d8028201c0c1a80c0d0039062a10740410418241c00d100da00a4002c80c0d03014640010004003000c50b5118a01940c10b001801c0c2c40f083c0f4409030a10900074140200140b150007504c51030300c7e5042c10390302c9945d034510a00c28a020040b0f40c0c41c4a00540018000f16001f00c01c210201040558484902d0303030310b0358002100c00c0c0115032000d00e0a19201020b03401d6074100e41c01510340b241020700e0705482d0742c0a98004214109603040220511000580d54443c1040002c00da940316420031480060304000c0050460944040c401e580101303811402c0528141d00c2060703400103046071640b00d034060130343d180c4111600095018640c880085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 38205751 1250 38204501 38204503
    0x5180406110c21070c0905070c08040927020f0111030c070608060405060f03030307050a03060305011406010f020705030a0f031206080105070e120a0209040507030b0405030315031b04051008030408 86
    0x3110b203580200040ca0400b1000244840784a6000014080150320004011b01300099000640c00011814440100d80b110360715081103a000340c024030f030039590720203680400c0303803084000c922400c0c4460144150128142c0000e10f0f2020058403941c100203200d10182d005410074000e8130424850700085411003515004050162001100c80c240101e00e88000640e080c07400d05000d002000015010b0740c615207401c001180c050380016801e0042c103403925000070004809200d802d20541c1090484807060404e078000510444800c0d1011003154000c4005201d0317587c0120300360318010b5000b0f10001d4001100c0c070701942d00308450a80c10320920301e0441d0004440c481034114511458003551520170264442d000c00258582040343d9004643c0220460401401d189400d20b0700240100d0417100d440385c1c2e83c1e503440812201101c0031100d03900003105010401a10f0004462020412405040036480240c0303a21801003c410b6580c3c403039512440400d40540342c4150303000181c10104144c0342d8507a111a205 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 38207001 1250 38205751 38205763
    0x504020102190c061b0308040825140c091b070213020712080a090305041a041a04030b010f1401030f0e010603140601090203011203111501140a08010605180406110c 72
    0x307801064120041000c5c1086144642500642c9034507000744e40e4840d5184c1001f01e130025200c0a0340e05c0c00c0741881c105010085d1101081c424818003142c9042d50204205909240100241e00e01400c0c104003400848200d8880340d403108260360034a540c0f6151f0500024903181c0000001204041c40090301805001c0f0360103811407487d9490b26482807a440d42e407020b0084030b0b070040f03002c2c0004006010a0000068952840c513014036800c1030541800d84411100c0210281514000c8500d10002010410080e0b0303052402e004155141c4040200c030715218000e41201c05400d001c0b410965141d00b00302030180203500002590885070020040c8541300d19000c0031402410410740c41901c200307400003910903420300899060700d8106040114825a66078203864039a01c40403841c83d14091040c10881c0ca01032091114000d000500202500041c22010f01461225070f0700604550b9046c04001e11864880154250071040b01441540e1290794501b030060041848045001c00080c0000785403511000015034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 38208251 1250 38207001 38207009
    0x117100e0c070506010b0c0c0f0a08010e07060201060b09060a0509010908030d0902010806190506030405010615080601170108030412050c06040b030f01060e09010308072103020a031802130504020102190c 89
    0xc44d071080c0d0701d031101e40c6554050800e5011141d880801180b41c1401c1190f02ca0400034005803404a4403616484990300390354021f00c1c11503442d40226400c2000344c2c1d090003200005c0002090007450001c2c100c0100b1041d01c24080341809128000a0380c41d42c5910590701d000052038810140c1c8d4a4200001e0860090002103505a0000755550003044491906003520900305c014503100f004514a40700a0041c00c1d0801030040da619580d40100061030f90000c401c1d01c98900341c035650700c14140703801d00015141d41c030240022240d00307041c10018484200004126015103d2084100c070300c01c4100e00d4568980740700404060782094021600041103100140514010b90542040c1c03d00c980c3c0360542110441220309541e54000c0c3c040c0010404150000014291a40603400c28060700102c00d4082c8001f071812140140029400104080350f1a4180f10f408070050130401c519100f4105900041c10030b0410894001c0a5903685022404680c02008040712031800800050840c0c4c899040c12281d2074400c0c81 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 38209501 1250 38208251 38208253
    0x8010e06030307020d03121a101b0c08011b170f0a020904060e0106170903030f15040c120e01020f09060a09050d06090b01050d050a320601031106090117100e0c0705 72
    0x10023281401c210b2032841c08074102070005004078030b0030402201d056042201c1510303070340340307402001021481a02050011b084e40c0c50022440072a5002501c04985041c0d22100c104081889020101d00242d0301040e080701e03441e120b280071510b83d01840b600a2246a40c020780c041c0c94800009070899018101c0c42c1201c006490b0304080c114a011900480344007201c6001d2203802c104005084020903c44680e0403607025100308800314140004203045601005030000490a00102690400c3c120700501e507810715440002c1d4180254110380d0070050264102c464030400d4041501078001e882084110010304000309003003015081303401c20700000c02c0c004c581a28521001c600104490915036100d0121951290041040c03201d1034403248030441c0e10020401d03241c10400490b02125040161401c1c2003107000c805070400703514501d8281c0700246e1600c070007801038200f407000204507a04450000280e0042c2014804a40c0e1070700392061120307181e0b0b000381710040c49850600586c0c1024101410b40c040c4104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 38210751 1250 38209501 38209511
    0xa060e01060801110a03150302040f0504060507090f0501050705030d1e0b010e06040501050702040b10020d111204030803071e05070b130c12020307090e1c080103020108010e06030307020d0312 84
    0x182c00d00341c810850800201200401010303031554840c0d0b1001030a0088100d90010f03c544036400502502e030322420b0181040d46030814407060114600c5041d40201a5007001a1546e14142008030004407522880e41441408a90002480401d0080314020b0000c00c0081080082d03040503482e41d042515800c801d52480d005101506500500203850b6280000b0412402c007803512004668980c800d54040742c000341c951200c000b554640641c503180101c02500a400c0d41d0303450000041001d82d84411284083d40a8688860100a281c04840681e600052120380d2503070f5500b0195134910015030000075510711500301c610b80641c41000342900138850341115a20b501d82c104102c001c0c0c00c28981c040c110090a240802828840180c030754209440a015960f02c030b580c0c1d21543c4121080010351a94a030402628160340c0200b00c1042048180c16051803809541147c00080a44405006540508091070007041c1d003903804005840d00668020403134140015580f400810440240f015942003034204 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 38212001 1250 38210751 38210759
    0x207030c06021218060702060a05061c0321090206070204020a09030c031101090602030a08011707050a1e0608070804030f0c050a030c0309080102071e02011403040506060102070b0c060a0903050c0a060e0106 90
    0x118449018586c564001c0c007868889c01c0c2d02c0c07001408003404096001c928040c91950b0010b1901a000040e8001e468800d01c840c42862002040711682c01181e984929014185005039500030a55514640544006894900d0541c0556a40d081d82d04040d0080909640000c10850180d0740c8201091082e41c410b9134190361341c08180c1c1d0320f000d0018903d010521042c0140700c4404000c45800d4900d070740108079000350307988102283c101080d40d000949008032441b0350541d080341c0885c2441c0106110f1404d881c4a28242900408004c0c02500c000c040000d403070b00c2405420704c54a00c401180d6088000e9400c2124280780107041d010303c0075801c40100e008820300084082c410302c2a500482c2e001003080300b80c10f4003e00122003818100000720305004050f114801c02c1200c000107188520b02c240000d20707450038448000b81c60300913960703c0032071010000c201603103202401050080e00080c1e084d9011441d1810ba1505036802d000701100942240f20740341c030700c4041c0143d50700a07910040381d9100030490b040d26 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 38213251 1250 38212001 38212003
    0x409020c010b0f1807031112061f0c03121514010e03071202090c0d05010b07050c040203040312050703060509070207031a01030203120d09050304030b0a0b090108060a0207030c06021218 81
    0xd045629502003c8003080040900064204e1580595507207000941880100d8a503803154001419200004012204014071810081003641003010540103d152880c004c0c0001480c030102e05000600b04038411034100c1c2c240c94982c026840b42031150454500c055100c04550a03c1c0990a0b40140050303803d040501c90b5090115030340d8103850494200317000d0342410ba024460503040c0500748040d03401041020050a04081c803804e8040d01c0350011b119900c0d0118240180303084010b42c2d684e0b201c2d45c4100f040c000043c0c4c118001d0070420320208004922669161402c1d401800694032060304080b030b410802100c268007050780f1058030700c074104540d41c20750f5580c40c80c900c01c00b003408000d4165105a11400d8542c02c460007901540303000810114031166959141030840c0c010f9441254a00c4041040c003602441702c4c020021240d400303481e11410f5624103484544d50b190003170b143c030b9010303940020070a081c584200d0b0480c03027071f58010109541e5244101809902c3e10012610220fa0140c0c0307003800a42000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 38214501 1250 38213251 38213269
    0x303020a0818060105013504050601080102040b0d090609120305060a061409011b0f051b01020c0f040b0a0302060f040302090115080105040525030c0e0d030203071707080409020c010b 80
    0x203102802040c680c0e08003001135800e01001480c01c3c0303c041c0814228041c481c46804224034401e203143c040f07416802c0918007c3d00c0c2640c10b030033179001c690041c0000c3c0032211190090340c0c0364015901001c1000342e55030038640010f148a07800680b025090b9410b01c800260903410041c0100d2040d21039541e07880d42c1c0c1100301c8400c3e0400c01b80042045040064401540c030511040440e04a00b0344d20320348403081c90b83c40f03a00c584c4c02c0c4103088940703401012811184e0992119040304004080c0090120100b04034000fa40c582141f25082c0d100300d56458190045454402d401da011759806061266241442c03101c0385850340061100f00e101c0c1142c1e100218040b034601181003c0301e61a40c0320014a80d003040c0802c03015020041c10045001c0400c0c04c84542c0203520700c0c1d1745000b900203880020b05a100322000070401275015a100d4080c9400c80b6414002036400400c0b200142d80009030920024641c0c40307240114460624041c0008a0204000c100182198020040c03216120001c00c10810b002082c444110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 38215751 1250 38214501 38214541
    0xd0201020c04020c0f0d020a110103090302060a05040507080f0c1009120807050102091005070b0105030304080a060e1204030311100504020d03030207020411030a0c140c0d0c0c0b03040303020a08 85
    0x80c105004003606402c0c207401030040a5103100a0700c54451002c400b0618040b800949480180d015841040501c44589030101a0001c00e18090080d001951400ba507241c001800064040b66502d0000d000d005080c85013202805a00c41175a20140000981d1643c0d440c071414560300c2180c48a640c80d04480c0070304581000c035501090581186062910b80d8820340d0042402951075540801001d071640e038403580400e080c00640d449050b01c5000c00d04105c0102081600918000d40c41000b040c00003040026000d4901948000c0c013054814076580b01c0c1d4100344821003000501e500101e00401010f40001903540d1000c2c240d400c030340e21240c5040320541503403420344001c6d410542100481001c648a0740080a88174006007010544011034142c130703146980201d8800b80d01550740c044c9140c1140e0700000ca80846410440c030203051150501143d038440c007980940c4800d00480241441c20015407007990401401c408405075224030301420701030060361040f1a1600040c44d82c238002140d010301803681c01c210b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 38217001 1250 38215751 38215753
    0x10509070f0e061c06110703030509060f0f150316091d06010b07030e0d0c08010e0c060304050303011e090e0601090e0a0302061603020c010e0304060e03190305161406060f0d020102 79
    0x207054148076440c4d0090580f00594509881d0008010a85421402421003c1c4240c0c0c00251600c1c00800190410340c002c1d05001040c5021005e00040c02c0750380e2105a04400f4000300c40c0034290314280040d00d40094070b04102049280f02c600026003c80340d034000032501607255900c2c2501c0341c10808030303612000f09010362180c000302402204041ba22441122032000c00180c1804070141850f11003000100b02c603800310340982e4460342101e0003500e0a1009600c00d000c183d61590450a16a49594480c04140a40c0003580818401c0d03001c1458032880c000014025a0020060100d01d02041c544a2109000706032031a03003090401c07003120b01c001540d0b03003210f038066014203519164421030743d44030444115402c080540a005401010f1300a2103a03211090710380008690b114035000e400340500300c0d44144688643c1010080c08070345e0741c0d0000c6100029900d85889992402540812030443c2d000c08400780806e26040981c0d091805c001078041d000e664221203c3d0702c0c03d440c040070020782510f155802401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 38218251 1250 38217001 38217019
    0x906030706051204060608061614130312170c070203120301051003050a02130801020408010c0c0b0103121205090a0212011b050c03090d0803010608060f06030601080a0608010509070f0e06 82
    0xf4022040b007116007007881002d000c40c5c00c0365100d85152070300341c0550b804043c0404414489400a4100c000300207402c0030003c08030706001c002c204803414402039200c054001d001a445040800744a10901c10443c0e403203415201c001d0825404080c03250f0050102240030344100b0407852075608904007030b241201d03030003803a40c9010303010040304802400002e4142917406800344034800c002d810b410405c00c003400d680000141c40c5c62912200a0070f440101c56048244101c8030b085401040d0080c203a1030540c1e80000000c1221200c1250454444104051561143c0c0c5400240070802c0c10200f000c10085000f258800303480c107401e1400908a0300d03038651903c4104136082e40041d900b40684060001c45003c06c0c1a02d060890300c40c081070a442c0c8902088554060010043c400c03541c02c042c660b604404151040076103040102c0200d510340c400688500d0507c588036001910300b032100c1d000030340a00b00c1400240280d003069842c40d59070711444d005108d112054150007040c0d40c40303205000c0788229001003084c19 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 38219501 1250 38218251 38218267
    0x7110307050609040e1f0228020c1014040e01090b012d020307021207050306090703051906020904060f0504111e0304030c0c080715050a021509030702130b090603070605 74
    0x800141044101900900d000c20b001d400a6214261b030f05a004100983d687d10403030f803010401104414180d480707104058900940c0380c4d000030281d08101042e14115072803440c0041c16a031401981d000324441410002d800f00d003510491507424102d0700d82030000c4c017140604400540d01d2440c90442443c100b260b10030640241000141307942e2452805e030065070318121a0b600400e640c151010300c08803042d03008841c00c01c82c608007080081d5000603c0000703002c5003400d503a00c0ca521944410100d02e0848641d1203600d082c41b1540e411103401560080003000a16514071030440788221038807400388502d240c0415024010401012681400f9804480300b040398440c20400642da080030700150100a460400307000010154800d11010348404c60040001c0c80c68600002d00c0e08280111000c2004030620a01c04566000182c100700e00b0808a0141026500e040e4840d01d0360140e1403020754044002c2c820031001a0705a4010a500c5405491074045540c0f450b0038540d82d0f01452041000142081004003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 38220751 1250 38219501 38219509
    0x2070f02060f071a1f15050901050405040f05010302030c010309020a0506030a020f0304050114011d1302150d0506040f0605060f0d0603140606030d0306080c01050f120c07110307050609 81
    0x30300600d0b01440a4103040054840da01c20a25441ea405113034800401807001c02c0384800451050421286204140c6909001481c11a00442005a020322002180e9030708560300131010b460241001038000c104103086100220301a120070702c8240e0107409420701e0101554824090050400d40113003102a40c04d19002c140225a40001c05980d151030f800e001e80c040890510b002503028a000700004503886600310040400d075441a84602c0480b4a6201041080e84a254031030f07034415204601c0420740e1301c19001245c11598150074000c1c80820000305034141241c19030242c1e004603000d030b6040200c0702608080c00c0031510140107443c6e1040c010310034141d050307090000034001c208400d540401d050355682ea43d06118116010440103a030841c0d0300300242810100101025001d41b460144415454241116100c1a030071018604110b00040c8020040c15050104d2b04c04031035140c02d00b2414500301110405580000e981101c41000c060a0802503160000f900c40603101d0080002c0e15000b000c0c0100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 38222001 1250 38220751 38220757
    0xb2d090610080a02041d010608010801051003030815030102030901060f080304060e13020d02070309050126070c061d010c0210020408030a030e0a021002010c0e0a0e0718120f0308070302070f0206 85
    0x883c407090780030800071814101010b40701090f0b001c1c0844409055061401c0640301100c140c014034010382c0350500b04a400399007070882500b00c0b074050804444036140e554110b80c06041400c10700760550300000610001840c1544040200c07108a1106e1001c01c0d01d9021305900c9100707500c01c0c5800a08d50410956107842d01101400e00c007078411000510300005094000c040c1d1700a40c400740c002c00d218410401c8996040101402c4d0390341c2c40c2e40c60b00312044201601000300c01d009042c0300204152403040c0d90402015034030500c0303a1031101a00000011a0390300d000c0c041c10541040c01c2c01400b900ca84011201054025582540d18003009541415230380c1800b10b0003005c010302000001d02c6005400c0c07002d44c4940c990303c1031040081d400402c0c0220818805400c20b03406202140c02042d460b00704104031140e8100e0940c0050051410003c00816000001202905c41e0050f10301285014260400c101c0130500407610701d840703901d542c09c40d0b60b103408090307040340a407003409012241000480d10044c0b6140c801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 38223251 1250 38222001 38222011
    0xb06060a0c1a0a151a0c0a061103010603052a0307110307050115120b07050a030f0c08180a020603010306050705071205070b010605040e0402042d0f0614060a030f0b2d09061008 77
    0x7c5821605440c2ca4a9080c0c501c85200380c903003441c0c004010b00220750705004440d0f024400e0003801d4440c0c5420700c85100e441c0560502c1c96100400800031441d81d51103400f02e031064400c0381003182d4981c011030130030900174983c2491914183c1c0d000e1000081d00d901910284c0c0019070441c840b44010f84c1d0781442651140d000944010805070744040e500b5080c170492162403200b00c401e98902c5403500e0319030101443c2000c0600f414a0703070f81c0008840d90050351a6000c481c1500d030302030000320b66901c54900607503440c0103420008284403645100e4000340785c0e000300500748440c0140020704499070395a00035201c0c1e01c1140204282c4801c80c4000402500b010f410112540b807085556021001c201c002281c5030918108070080388684400c00e2a00d4101c0d80d01905000d09030404c54913103c0d400b0140025681e01c103684c0100c0078951103580f40306a61410b5030204110b44005804100c501d1b101c2c0c4040c21441d2803001240c03000000d20348618555003480f0240034404d0f10090b0009800d10141d0300b080c0c82c03500700242 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 38224501 1250 38223251 38223253
    0x6060406030e0a0605150108100b0901050f0705030313030e0d02090126060a0b0f19120f0602030a02030a1802030d050705010609060303020a05070e040b06060a0c1a0a151a0c 76
    0x500400142c103072081d170340700315079440001c8035240d0484001004441c01400c0e80045d0b6045580c14000d00078024202c030105482400c18907580ca8410440c00600e000700000078110340404400c101c0c00c54440e0f0503540c41c40d40f00e9901d144003968200100039036054404000f070b4005084100511011801c0c440c200c0d4400703102d1880b031251101c0310701d01d58a45101220f034030038200d032942280c25041c180419686030601044403856400080408a002041020b02c507512503603908084910034040003c040c080e420340c00500556403454103400002c007079401919240032141c981181300d80000d00003e14040e5041e40100039000c51882c202e81110705807c0030500341c840355652080019421402e02c54600250b00c6500a04dc45034018186242442d00542c441d0b1244842d2a0030800081c0051000070f9203c001100c0350f5032038a000050407076000d94070100042522254403809003018200d08005880b036100700b08140f22070324001c030020a0440d080c0c8120100c040044100c00d100c00c50300e10103040b10706035808c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 38225751 1250 38224501 38224513
    0x150c0711040b0901080c1008040b060103110c010501060507020a0909020f04050903041226030f01030204090f0203010c08060a050a03020d080a03200c061003050c0f0102210318010506060406030e 85
    0x10000f20301c40b10a9000607580d6022501a90950134000755281c0d10a0840c01d000c8140e1070300f0f461702040034500610490405a841c80c41ca501442d410080e683d000090f08000c10039903840e030b00b0107001c0341c0c00350b00c5c242c2c4528000c10300011100c640d80940d88800d0b81c098030400f418092007043c400503140c09000000180000d000100c0e50080f8a96039049050096a445811b080100c242e058400140c0c2c00b1007580ca0390410401c030746040002e4013141140c0e81910000380405560a1140042042000095040d42010180a039403580003140500801c011a83c4100303d6a50f00304214241c0780c503210081d000320740c80310b058011458000160a1141d41400c02003045000c20801141000b42031300e8889100e60042030004041204111392680144004141130459042d17448403a560201101c50740e100301640c12406010764401d101a4a0011036200306801c074010103440701e0707510b820071182002d40701c1014040c5520b401e014000d8038041e0074080c00081c542406c0440072400341680c90007501e10f600c075039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 38227001 1250 38225751 38225771
    0x90b0c1c12020d020702040b040606090611010213080c040b0907020a0f1103030313060c0e06030c07050f060901020705010b040c08010e100302030d120e060408041707030204020f040602150c071104 86
    0xd0000f018400629100142e503003400d403040100319054a506980140e1619600381f001c0742e0041c4d5014290380b01810b1003010000040c90f610b0192188503918424410007a00000d81c11200003042200c0d480210740030701241015506002920000715007080050b4400b01d481408a0b000510301e0204d1030054584a16032000d900100780344ac3c0c802e407141000c80344a80403040c1071012034443c0d00c1008009103032190b20b5462100008086000190600240120004100b020040d041051601c441003520581c0c000d8640210b00c50300075000098280c0300365003009241003107480c141c4902c22000100b61201c1816908107007113540c941800814000080035801c2000c03001da81c0401a014055109a982600300c600044000e000c0d1104189012800c6e0b1084050100041030304043d80c007919084203409805402c040090762500c3c03520340c4080d400500c0056040390b00d5810200600c00d03034499400b1902c1c0c1000ca045203461811003220900f03081780080c8a4180046d1107501607010407080200b0201d5540c0c02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 38228251 1250 38227001 38227037
    0x2061501050d0504030207030308090d0f03051504050c031801021204080a0c050604210305070206060f01090b1c1104060203070206070c18060603050106031517070305030f0307090b0c1c 81
    0x40c4d40c15809a0b0100c24100100b640c0f01c011958854207410261481134208500074150421408100b401e0503162340024121880c812462041d04c00024400d0296040c601d01c07080761503005641c1440d03480704921308402e1191050003190b412806142040403190340301c2e126910b554000110310300130814004881804101c080280324004c41c0a02005c0c60318108003240740d2520007407800418149401c00341048502c540101d541d9038030103000d564400340200b181d001200c030540550821407400c0400b1400400040400c480300454a110100030040601410540340ba90300962084400591003041010014288880a880428031031010064440d84031060000011201d5000305092aa90f540403c400ca9150140c94010009410f04208440c1224100d02011035a409407108030600c0036030004a00004009601c01990801c007903d8032039860000402013540183c41d04000145400c0c000b01d1240002421500034101ba2001044d1110310002c049820b0b450401d0680c091189404201c681060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 38229501 1250 38228251 38228261
    0x1180f031110021c06060503040b310203071a0307030e0106090507030b03010b010306060c020402090a0510020d03060e01060f080a0902040c0c0203070b090609011d030a03090611010c02061501050d 86
    0x28500002580f608000d2007450306901d0004c10b08286a030600780c040000c02c1d00301c000c89400c00d401003034071040c5980f1169504403041c0001d4201d0320001c80940400171842d00110035100491080f01036506081c3c4d2640d8110b80300007407004481411400b0408154954002d03840500400860000401c250f944c1e148010200e5404481444c00b0a0721442c2602a514080c414142c1004007420200551400c01c400201034107025000280140d40c0006d190030b869030b0701410398008102c000c1c4103041589032410700944648120b00b20001007402c0820114040708a0060503050b100e03503503616120110300c18021582040058000c04030b855442e448100540c40b98000c1090002c036540340e01a0841c507600c1858035000741503102c0b164600c070a0088041c40d90761001140c035603c00911300850341202d4906101130a414006600b039142c810f40c10020100340d001102602282c0a40d00c50446071000580c10a00340c0746500c02503001600041c0000d10703062813a500f001c0c0559410315001d4106045060110111a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 38230751 1250 38229501 38229523
    0x170c0118080a030507030e060a020f0904151a070b0c220e07021b030c0d022707090503031819030c0f0e010f03110103050414100e06060301180f0311 65
    0x301c1c00041d59404942c00d801441c1e0407800c5440c0070860080071a02c82ca449030341c080c010444141e00082e1000b044000002501c120b25070040040250400a4030845200d0f205440344a0360791340040f11541a1481d440143e440c46034100110b04041c0d600c40600308565400b049005200003913000300d50400c40e2110001d031000e8040c2c850818200d080c0307050301034079064800c0404003c1c0981c000000c030a03600e000c86c004074039800a480c000200029031001a19070140882c022a03218003011403441d406800c511140e00070601031300c804103000d448800340750301c80c0b0601001d55010044500f00d0303651414555007020b406031500750595606078481d900c000007030409500110281d03208603401d01c102010410000d00400591030100324261865940c00b41c14804c100d1520f044c107a4440000b418001442d0081e202283d00d94250781d180c0310200380c00801010841d103180070b5442035000051040c10140700d00c541c50007051800710a2810990388103071500d0301e0998103c0c1089500b020804003854104080e440071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 38232001 1250 38230751 38230763
    0x11040f06050f0c03070b090106090606050405040207051f020a030b0105040b030f0405010f020a0806090106050903070b03071817280f0f020303130e06010c150203100e010f09050f04170c0118 83
    0x44c100301f0344080c00c1d00c4e41c40d00046641490700c6004c108964101080340c040b81e07001d84015868101c230f400c010b4208020710f6113081071580091002c200d0418154010b00e01880680c07002c01440548800440d4140100d000b001344200301040811600450a001c450b40f051003800089108180e00746031400303070b0b0404410680410420000e00000c0e203400302c40c49001d0305092401a00740728003000040da50b60060310134115030500010100d602144071700c1c0244041082c2010ba030700e00b070b60388595005c002d0034090190b105900419400b064200130848081e0007408000320711500e0401c4139200c0c12110440380000300c41041000c4058801038600b807014201895140403a0405123240a8200d101040028807103030411010401c180000b07003010b880440b4001410348010f071030395580d6400c3c929004081c0c0140f10000d1128000044084900c1c44540c01d9400c409024009500d403c850f01500c50804d075030042007418901d0004000c103403550090954100c1840c00444d208030314035014006050110815214 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 38233251 1250 38232001 38232023
    0xa020303130311030c03030702120a0c0b1206010e060f0a02030403140106050a12050601150c0614010504060501020a0218061c12030b0f0109030201120905010203091011040f06050f0c0307 82
    0x14040c0244201003182c40130340c040e166200110001076201d201c1c13008020310680c2140c1ea181d0460b20108102e1140690010800c3c07407a80c0c5802100c01182c00507201c40c81c0c03018107480050120351140425202c0400d000e40710600309240045010502d070000c105620441c0b00c18000000854403440130302980781248000020354034200347c00e10007090120380000c110f2064070640038001440c00109141103804040119400440c00355044a0926088601901d440c1c205141c40091070b0343c0041d168100c5504540411010796a100160b0b12143c030703000081e60000001200c0595901c00b00c00e400e42c0240c0060080c4c650205031070710503282c50785100301518842c10003c006107500f50148520002e40800311450309088007160b000a10350015400000e0401540c44460b25068940340c1140c00004d0f8068025500c03440d201700507681e030b0301306001002c21490070318031518217400b5100110b90944801402e080642800c0140655a60b4408403034034824060400400380641424005000001d01c140039602c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 38234501 1250 38233251 38233253
    0xa0510120501031a07020607051903060308180109051504090209010504080a03020309030c01030212060d05010b030f1b0405090607030e0a082209020306060a0c0602070c0608040308010b04050904030c050a0203031303 94
    0x903444e4070080c00c960035580001c00340405c0719001400d46031404103c280304502039948100444c0503081d9540014201070380481c1c04508251100e0082110a400382d0741c42503620303920300c10800380700600c0c0d20451200d1030800040c003e07100c1680041020060604295180aaa8071002440c002d280c07c0c2c181c00581002c00c000704c1c0c1c1d00e002e0129009100c000d103420f50800181c500003801600000e070070107200f0000e01325a03804112080d00152107081e4020300b0b480200f42101000c40d11445d40708446100030300d1031081002980780c5881400d001d40301641c014007507503a0749a42540200028080007001784140350490000a40e480c009101c1e40340e02d404070310420301c0a280401c01c0707000c890304000b810030f0051003000501d840d040e0654450780b00340e01e0f211a41141d90704007500248941c13040030300302080301d22021400301c0e04aa80280146e109035940800d90ba641c24411140d0b00840c01201c0d8851400d90200780424400c0000302d00b4140518143d0790164480e50010b071840c2d01612107419200c0201c90b00300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 38235751 1250 38234501 38234543
    0x903040f0b0403120509010909110403060b0603040f0b071e050c0105070f12090204060b070305301815010e070908061306110d060803071e020a051012050103 69
    0x40c01454048441824141184d450030144801e1650000c1049408600103415031310030041d10004200b006010031280f406180107940552060105075000c5052952030005403d1443c01c8138030a40d0400c0000c0c0e081000c0d0780d114407030301c00c015102c0e80c10041d05188000d642140c4246042a845050b10707080d40c0c0f00d24003403544e420746200604031424032213a0b1105405854200010a20b851001040007484507160700c0001c00810090b04546c9101c403001c2410020103401c034000301100a4503504c14400342c1c006408a00b1004000c5800500c000010f2000c20101c0c04030030240301c0200a0201611000350b00f0300c050703500c0640241d0000035400c0340141489201504400c01c3c40240c06004082c000c145408210b540741d41055005c0180080d03035428500c450a250041540d506040b445c07c10310090307549100003642c0e9045008c0644404242444080e210901040b030201125800b17850240124942020481c040c101e20721204c050040b41e04103074044000e01e202e090b01071403199651484183c1503400d01c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 38237001 1250 38235751 38235779
    0x40e070c050604030806040f09060603061107050c15090607030306030b0a021e03060a03020306101d060f040b030f01060f030b0106080c07080c0102120c0304051506010c0204020c010b0306090304 85
    0x8001805441030140c00032400102d5030690007501820982d20545403a400b02d0014000000003210361481c1080307510030003000d500400c044901a40041c090078102c0340f01c4000701e104e2140000d01e2540042e0b0400014141841400b05404240d41e00e02c1c00c2401e85008074000c1c1c1d2200504800003641c0b481d040c401c2109582c01160401040c03001142890115102110108403005540d06c000f8008030014440342e0b00d040703481d03000d581d0140582d5003e060414184400b0346030f42c050711103402803880d076014040008172056442804000d25500d1078903a1141808001d150311040c40790103020350308030f5131001c40c001d019002c010440000c0300292549107081c00c000d000010703046041046542400d000004501c1802d881d841c980001c89a942ca089c10000280203214203032410f142d90750688100b0200c01031080245100f00d000794180e81c0140d00380803180d112003008540301800f04001c15070038400350070141c1c09802012a01c400008001040c900081d160440c00c07644070385503510004050042080507040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 38238251 1250 38237001 38237011
    0x190f021302090a060e030a0210021c03090b04020105030a111602150705061f08120a020c03070302010807031817070c060c0302030f0705010b130b10020a0b0402060c030d02030c040e 79
    0x441c00d00700c0300340000f0700c001282d2103a14200003042080d180503540c188003000240380e000300134181140c076010f0043e4541140f801d40c000c403d19012440d110f641c3c064003031038104550044010410f951580e005460b070390800b0f044407002c1c03613480b8108008814008010808640041c460161105007803040011000c3c90710300d0601200410300641d80083e40010740da54009400340764100442480203805406000180c0c482c8420f44624a1020b02c1c00e10310b41d0007464128595400e840484001c4820315590396250300c0006c0c0041c40b604002240b042c0700e50300c003000d40302e40d54423911400c8180c0c0e00c03440f00300340c07054821200c05031000900104114001d41c1e200018410f909082c4100003842d04c1c00780d01da01a1038010f2012820000d011703010403c00f035103c44804900100802584c1c4202c0301c00c04001d0961161050041e100c0304000001d090002528400ca55400031a0001907500d0340d00b44291070b081403485a0707280c841800b2542802e500d83c00075620440022180d503803038510b450402c0b45243c401a003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 38239501 1250 38238251 38238289
    0x40515040807050913080703080f060402031b0901050702040207080a0e0d030503070f0903050d020705130b0a05040e12040303050309071d0412200a14010507020a14190f02 75
    0x1208010204000c60034408848003110707101c00e03c0d40d403004800c03820401789030001e2002400103854000c26400a81050244040013000316140d640c29091000702e10003540c0311600d05900301c0f4201c43c4030b01d140005020340d99041c5040c0d8140360065002c00c080e0380080b84100e8900401040c1000b01b01e0380106d4280c40c070710782200c0260840c0300b9038402502a1002512242c1003010203625a5516401601a0001960300c40c0032601550f50042000f0f450f2422070040c02c1c4070744103160f00003480c0d12f8079005064604000500034a1005c3c82d14081000914400c10141c207607005032403207111303154a510082c0000314080d0b114a40c0e41e1500d44505401e0080f0380d08802412074a0b541c0a0420304901c0c05135503401a400440200040800d400607940b00340c80303d142003003800c0c40b11004030b01c5004c00b00350b005220f881002949103100680c50070131f00380c8000300d80280040e4410715100001c14007500da84084401e00e001a12001c95400310300001c0080050420380d0002080c401034000c50400d00300c92110404050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 38240751 1250 38239501 38239507
    0x10020a030503011505071a090105070305011d0a140711012d24150201140610050307051215010e0411030114040e16031e0201050406051c060308040515 66
    0x1a40c058558001801950245462290480c0100c1d0152003101e440c143c100040361600b01d40f50300304402c4202c044407600d003a94200030200d8030300c6009002d04ca060710124007801c40100d0f0381d843d0031450b080000b400c012442c0e0329222040b54071a848900305000300c0d100e568507200108070b0405a401d6400c07500e00f4000c0040415042400a0a0411445910000d000300840c03082c1d1501c507248460005000e80600072940450005103ca00358580e03440c1290403138000780460030449100e1104e5400c1110800e4015112013108083d840c032410045900011504001e41030804607804000620f204a46200c403104003c3e02d040481d41e006480d80d50b41c00d004071401d00c000d9100301004403081c0410300c2002c0107a55510081005a91180c0009800307a000200b21030010040300015082409144030546020444105041500c0b0324180b010542c55010303105c4519042c5841c0c812109580071501e91501ca1400d01d90045c424201400340b10001d6004802040e1102d00f00800c100700c09540c1c52466060340010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 38242001 1250 38240751 38240753
    0xb0907060206010b040b071a0a05011d0103050a0b09030403060c09090f1802010f031808090907020609030304020904060e030a030e0c0402070c120314041d1302030c04050415061410020a 81
    0x100080303a080e1026040b18a85a00a520b0100d504030700b580006003003c8d14150800c070309a1825071009049940c0800215020381c401c0f40740083d4a002800040d0158114050750000b0580c0324048503009445401100d29103036582d1251802c075845d291110000030b282c100e08010041700340c018041c0a1114800400c242c15503121000200350505a0003418005c480c850002030f207000e940440d400140b0950741480c002101e140290080e4041070340d8034031030080200404e450500c0001d03070714440c5200800640c0740d0386a580802412440090088a58a071108404100b020b41403000d0100c3d00500d4a0200702c100c12895950f0624500c0103100e03008501c1803000c030b0f02107060002c0c002c00b1a4294401034200d01000e08003140c00d08050b48080c0030445d400900020050b50040c0030804a034107488003080e06071264512443c07090a51704020354150711140ca603400720700c4d2a51020350010b2150300c03600c256500c1c1c5400541520303601d03408201c61070300b102c00710f00d528140f101c1c0a4408a9139880a0111200c03a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 38243251 1250 38242001 38242019
    0x30b040507170405210d060b040e130215040b03090705150409020f041703120901020304170901090314030a030e0303100611010209040f0204050f010e10050a05160b090706020601 78
    0x2504802c003a105580000300b0144041881020703c02e035074921401c1802e600207400c0a1855200c0765030241000d00c0e250300014801058015202500d44079030694004d0f89900381c000d078024450041c103aa0003141c4040442031006413030018802411084800e075240d00c0e1408190341071079404d5021a007c0c40390b5149a0002a9092046909841c12800010f0b100c00822407525018003c41c0c0080b42c401d0a0940c50900003103000016101014491809036003d0752403454640c20317030206940080450050611003024480118054114020103241440305141e07070782c0307450490894410320241d0360303007000842c20019130f40350285081c800011001146103042032001c04078008528070601d41004010751081414103000e404480d5400001001842017000e0515601d000354004c0c46020710402d54110807038040e5029150500400500500d1445540480001507a169000d800f100d81040340401500072041c0840c01490b011501807102003200d0301c0c0428805140c03d005421410039980000010080061 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 38244501 1250 38243251 38243267
    0x2040e0708030a1209140c0909010c020304030215070b0c03010906050a030209041b03051507030b01110703020405221103070506030907060309030504030f050d030501050105070206090609011407060c030b040507 92
    0x5154034201e90030003000c0e00ca03400100011403000b000d51048002d2411a078074006103115581c0008c03160305003030751911407a0508a40c803020004006d0781080c0310030809880c040f43d08a04e62103000360214540700480c0d5420b409541c0898400c1040701703000c801484040c01c0c510494000e01020b0320b000310440e040d03400149812000800041c41d80752000c40b4105e0144410701084011a0f12000722210210f040401c18510601110854000303403505240a107198440c075114240c1101a0010700070543c02d42d000c0c03201425008011000080c0080150308550340241c402d82e80070350003100381e00a0340d01d60208040c10003806500042c448e14060040c44040075000c1603000c101d4405040c00903000746a0300d415141401140c2c000b8000503103418030103003480008500c1031341c030040d44e58040119a0700c0d0001074031a0702801102a4000c0d506225114107070511000408c40f0100504160b4218455075207600401d500105045070311545034800480482c0d018000c03414141c80c12039003400329283c072401c0101001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 38245751 1250 38244501 38244517
    0x41407060c110a0b070f0b0703060b03040311030c03180f01030203060a180b09040305090a08030f07032d11010f0902130504020d0204022a06010b0405060f040b0307080402040e070803 80
    0x2d0b01c101515030b9035644219003000b04280c1c030760303941c440d241400c00c0320a18000310010380308414241c0000d100c251007442108150303601d128070796045480b9a141180c404942c2c040c0048030784000c00502044210400c007510f1440307001c218921140200c00d050008003a01003240e40d0501d0f005205106c900c0c1e235042912800c8d207000c03a0805a00d2581c01c22910f000d4503041025542260b080401d010915502600800c5c01d100e0a0f0742044040e59258403050f81d91241d200c106007101410b01001002070b10400c560342211075020b040302e85141c5450b07a000b80e0b8015919101010814010031843c0e607040c00c4c0135000d4a00b0031081c08011940c40c40e00403800506030240002d2000e40c0d500b0000b0211740c1c0d04000307140c1058000c1e2045450f02038841c14503404010004802004807242d556103800d42100251181c142d82c80c2c1840d05042503e05420300846410104407602c400409100100d0a1101003016500c00d4000d5134800c05981081d00501c000c950b800032821101e5008014140950701000007107130000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 38247001 1250 38245751 38245763
    0x311030f0412031b06020702180103080a0302090315010902070c12050a020108130b010b0a030f0207150c09030f0501020d0b1e06030606040810020c01111912020f0d05041407060c 78
    0xb048452030115011441072581e03013900d801040c50b460070300141b40c0c00741ca031030781c030a45402c0b804006d0611100ca81900c01d204c020140001006500c246621a8014101c0941c1c045c045a4034034490412402240c0c20981082c1140b65002c03d40200b840398000f0a24010311001c840c207040d078005501c5036030301d8803000d01010307050048000105403c0c109540b807070640160084501074807540c5076504210a03500c013076082c10001c1c0c10315200482920b014403c03900d81c6540800c0418003100c0700301d14280070309175040700c50050140d032036030000c04280d10842d101d50030341c41030000603030740c2c80e13010360650844800c1c60300e0394010b4a200903000d102d02c80140b0700e4500208101c45040e240c2d0b48810000e03040d4811604202e0407406041d031011110117854002d0180004420b0082c03001440701c21100c44903004401d010b24005092080b481e9400b03000c0d05201d0414000d9236000341c6442ca0003d0490762580c00501c0824200d55140200024408455841c41100507158040c1c01c00d586008001401d00204e41006080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 38248251 1250 38247001 38247029
    0x801030c05090c0409091202160e0402041512060603021e0607140c1504030605010b030907090b0d120c1208150405370b0603010f0902090a031e0311030f04 68
    0x20f900c916509580050918030020300c0780303981a00d454800651200749500c0584503200060340c005241c010241d0643d100c0880404c40d55485400300310181c40031450440510748184004030b00ca0440644912400d03010f82da0114006145105228100c00b00e1004400c0c296107444541c1c22a58070002129041a00a802030241c0d43d0800300450a20740d00005407980305088600c2d211140003013201134001c89000b907004010130b0780d0720a81442c0f64071048400c0c491a8000c031509001d40c0d00154004103038624064507045044a2541c0d40268444150207980080741e03190030054100f00240140e144030000925060046080241a10000700c800388002c0d40b080b9100c100140852080d40c1d15009080945e10102c0302c0078a048241c42c0210f4240203003034510034103001c4802c02c1c905100084904030f50340500b1a260240c07502d00ca5400a40090800980c4040d10281c0007022810103400302c0c1031071003044103241c001d0744586005010384a1051a503035854006100301c8500b0b1610800740c1e4115174800550707485d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 38249501 1250 38248251 38248261
    0x40b0a2301120b060303070c05090702070e0408030103121706151309020309070603060b030a0f02130f090c030e0a0b070909020a05030a0b0607022b020909010506100801030c0509 78
    0x4802404240621490000c0d000103042c00002c4520031405000e00105002510f54009140d16841800c0016080c80305168080040303003400301d003080e4004010f1041d1101e03103442e80c98842e06484155000d43c3c03001d10200045c01480100040311040c901e080c180b1000700809a8440ba924078002018903224540c8104041b401203c1c1e40112084411024180c00303c00fa103450722100203400558a0141c1c0340704072800801c0d00c0f8042d20a40d001e80705901d80682c11036403510302c120081c003a55a00304819540900c11404c0c00112011940701901c05400c0024202e400c042d18142102c001c1c43c584001c2500f04003500c10340c2e180c046258000c4c0350f089540c0d1480c076500c007901503480340d5040d8032402c40c0d184001120051164008080c40c080e2000c50b20030310014503c41d00f042058015048040d600c500402c02415401c1c0920300042c40300910310a884810f80302c16000180a03410443d201c0f4191394507502041554a00500d08902807206406c0544565040d511102418585801454003610100d40412 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 38250751 1250 38249501 38249531
    0x90f060509032802010e1e010501060f081b0903100609050a0204050609040c0e03030706060f05010f0e10020c12010504060f061802070507030215090907030606121107020306010308071406040b0a 85
    0x101b0001040072103c00000401103a501c01d01c407410117803115441c020000c1800c500c03a8000d16030401d403642c0e85c96642e85800c8061b6464241040c040038009108004401d01a1424000e40c6003403c02d942002034140d00c6c1c1401b10094400080400410350b104000900460f42c510b810390701000001d03100028145040e55050f10044116107000c1d516200110701c4204100c0350f604003070142c401e21030040d1a2290342e00c0042d221420042d072a00301040c180e03004503184d400c05404003991100d491044810030107049000c030300c031424051a148844c0e5150b500300000d1011a00450135520200780d01041400d1800380703040a5a4115a491001150006484001d1040410040d4080e680003424510611014100507103281d21440c01c0343c0c00b411400c1e0004403103500900c1410b08582c866102c49007540f140807081002030051980ba09000d100900106000d42c80401c1040e018600c10301c0c2d800d6031500203050410412130300324880b500503481881000001008000c0c030940008031443c01080d11a0584000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 38252001 1250 38250751 38250761
    0xc0702040203040c0f0806071b030c02060a09080714090c0d0204030602041d0703060501081303020f010606050a1b11010c02040e06070305070f020f03030412020709090f06050903280201 81
    0xa940036001100b80010f000303141000d44c00f124002e0510010940d034940725561030b0f00003120300c4004035481820040b5a40d4401d02002ca1941c400e141908488040b58009103443c3c214000c403800140c04a6800c0c40303020010003864000d01460b0900f201940d14107800a200c031070006148500c103800110340145174010a0f0151005960701c00411354540d6222001d10a02d9410310b403800368601c640302c0c02b0428090003440f80006480c01070b95a06d100e940c590f1810000c24920352070840861285402034400c0ea20284034110240c48159606a0b8800348200024040081074461001408150b000000000c000056000a4280c00c0c20308844282e09800007800400c1c8e4800100b0302400352504009913641d061b40320610032070310740c1c58031500050054002c0b640c4d400301a140368000d51041000c180885c920f2042d1441a5115104a030401905d0b2034966054400d01f6000b2114200c100100404002c1a03010701507202c0c04c240c0043d410403001c01413110044075141659681428101c80c04030080380b0039001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 38253251 1250 38252001 38252003
    0x503030c22090b1503060307050603090a080309010902010207080f0c010f1b0303060f12030801140d0c030807051509030703120f0c0801180b01050307080a0b0d0308071403010503150c07 81
    0x180c0e038156030781000805015032603e0240300701c3c1003e00b0180d0b5458000c0c1501d001e03400140052036030504000a01803ea400540b000c640c520548100c031000076075280046100b510600d00108420b04148000b80c98550107422404140d08484e009015060b000a10060a4132092910700720306030200304261404c0081c01e5610b040c00340000c00342d106143e01a00160211652480742c1d44050307549058543c102c4014910040024007000010041300c0e203078508880380320b50001d1403e02c0d210419176441d0405507155000712000e900208400c0284281482000c580c0948c9003e14403a926168801540303d100b400c10003800e02c450604107943c0d04440d0f030b21030715020507064005c02c4500113507000680844401d20a005c0440d89c11415004440b003203002d8400d8100d03044e1210303420740d210641c041da0304050040201c0681030b59805c05c06150741e150a0110340b4140a80c952444605024400170036a18412101604e140c9042004000c15200001c2c085810780000a601e0059150310102d94568070a03810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 38254501 1250 38253251 38253307
    0x9020f090405010b030607030209011407060213030515090102180907090f0603020702030c06190c05160608040209060f0108060103020d1407030209091302011b02010e1503060406050105070503030c 86
    0xc10002004015402943e404004404031003030380e0b0302d4200c114141c1c840d81d00018001079048144040c441004009040e0680c4200009810f00005900690740d080c41580f0607107442c2c2c48003800e444251040142c041d00460a60000e502e820080c0d030401c4100c89050480901954200d00040da03254403a0b28480045e0898243c0050440d68440e4001d0207500710b002c05030710034082d0b0400c24405141c680b0449090524021408031501c00d5504184c6003206444030a4415018105074402038006050908024000c16126003d0300d08060040c0010000c000b008580034180c5103404100c90780c2c100d04010390190f02440c0141e51000b100813000040d00711900202d0103440c0b850305014580d601074001d440c1004080d25400425503c44903400d054016066000c2d000c24208c95000304800c448400c0018a640181010040500380c2c03004078200c60000c20490300190400300030721089107810b0113808014103003440c00a04056480d180c1940300e102c050940c8540b980c00141300c0018042c00c080c8484e00300c0140c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 38255751 1250 38254501 38254519
    0x306010c050a0605150117160504080303010312090806060a0b03090106031407150f0f030b06070b0a0501030b0a020a080c090d020a08010204030302070e04080a11070b07080702040c08040b070309020f 87
    0x46032040142c03000351000d0f0051045c40c04501d65951182c02c006c0310a11409070108056210f880764001c034110b025216a0400c081003002085c00b401c00c000440c008d61007507841c0228101c100b8401084640123030400720081e04808140070059403054000c2003a075440913501e56070ba80310480354600404103030b80028221440c0b00075024002e42d01180000842d03c0000c1c06a0883d040c0c100121840400d440400021a5820000806a900c07a5111003105480501101d00c1c0501c282c0311034140c42000c035441700d011500d4200520400c4813111150340c000f2284001503040c90400d8401400800006102055490004c07810b20380d503503100d20209034030740e40182c45840c9640c2c40d1294903010b0b51042c00150b004d4031620b400010410308519900348550b420148442c18042c507108110f81c0d1a149050701d5915200e80e0f00b022425900450041c003c0d58806c0030403e903244801e105101c240c40303414180109000e0300f60304120210b20610252680810f80d4500095100307400d00c00204641d4001c0741c8250008126 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 38257001 1250 38255751 38255753
    0xa060b03041b1a04050306130b2d0a0203070f09060c1401060306020307020a140c010504030803100e0a06080f0106050108010b030403030212131a06060a030b040b060f031006091a0306010c050a 84
    0x30400510591704103030280d038240d54407540b403404103598658004101407110748c0000d500c5c520340c644101800c040d912221104c030302e01c00e1074070b185801e082d21051007103070b4000280560190004040c0080614604246003014500310000e07204051485001d08072031441c1c0320b000642082903000c00081c540c060ba0854490070301c0c0d0700082d031f601403200f42211031060700301000b680c5c2c00c0f0008024544c00d0059480c98034207400c550b241da10300c1d000904103c2c40101d44c804041021814002418410300d100b1a0001c1c0e0949042c00c5146001854070080d0f801d40d16100051281d42d0b48220150b042d00c81d084043c907925212407408400920501d6a9000706042d0002072110500c60b1050200c40d0a024038400035180380c85512600f03034490150f65845e803000701082080d56807406504040d550650080002402058840118000350f000e680070410301c41e400010400064142150740024082520700401001d060824001c0c000c0011000007a11791004000208945c1c401c1c982000d00c0b03079000084ea070f0b6103455 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 38258251 1250 38257001 38257049
    0x3060c0912010603020f10050c010603050c04060e01050915012106050a0918060f0b030709090c0f0803070308040206090d0506040204050702030c06010317070203060702030405090a060b03041b 84
    0x100c035402500c1000c40803102004000c0501622042d00d800810f021045400d10f400c0041c00100c400c010400c1c4481440303d000a81c10a215041c0214001d501812a00403080100320840d03450b0b40040c0d43c3c400c0030000500a54841c0460580c0c0f02400e03010740c1414910540050f10010440c60030b4020130741804600d002c600009400050071514203403070405038580c9800ca09429100c248180346404858814610003280260304210b003100280e6238001203001d1204082414142c0541284074500e844a0100d4108005002d038075004101041554030f1003410909059128803940c80090b04203e2007001041c2035545a104071408200002e1004002071580c1c0780654483e00301f01c6041e442146014002110340d4004001c40d142c10308400f02401c0142e003183d4452828031618085100d40c40b005002020060b1410046c043c0901403580056484500d81001c201410b50014000d042d05030900e4010001c140b540001d80360130076802030792002101d1580c2400c044440c0349902017104489030110200012003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 38259501 1250 38258251 38258257
    0x70206040b041403010f0e0a20120102120702010b0a0315020f07030309140304180e0304090507051305060f030a0f20070309091107030c15060f1d01030302030912010b03060c 76
    0x2406500902072404030840d260304480006140b402c0c60b800941a900c00a500c2d486460f043e012275541c408144c03115603021420007046085958526940018200512801a28136070390040d0b251000703100c0030300400045a104a480d02c4001c1004005011080c0250040d4050320700d0460301c4460651544185e082c0100940101d4206076400d954040322040301c10700102c129016070310b028501d8042180d81d17020200040489a0381101540014000440c101c1414000d140c052001d55a4240e21031681c5110328804d280340354440c52040350204100c0091880007001c0e030b98403601c540c600061031002c030501075010303100d690399043c800315203100d680156071901030140c10551b002e82d64040c00319880e80041002c5427143d18800e5101c3d0300034007414000901c5100302958007841000c40c00b20b0a42c940e4254002d4074565003102e90310381d210380d6080c48030b4504811825420140b054002e039081d40740d40c40107903c07403150082c0300c0d014031a041c0001c01c0f4140250441c280801002d0111740d02c520f080c00100804e60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 38260751 1250 38259501 38259539
    0x13061401030308102102040605060406080603070909030e09130209040507150809100b0303120a090b06061303230307060b03071e091a0d0302010501030501050711060408070206040b04 80
    0x10f0188010400208544010100343d910704074801090340302c80c096002d01502c140710101c0c2d1007030b11944007040c00d40700c00c0080c2000701700c10385a04519080180c20142062050307084401420f140040380e0b03001c0390340107554aa40c3c80b800e440042c400e4036100da0601491518a9000e0340041407041840200503002804608031064070480c88040c040d8160f0441c0c40341410340303444c0d51960182d104101c0b800c64544c02180403c0d002000c41c2c1c50300e40e98055060184030200c800c103420550b2410590103109280d15042c0e0b114104a814900e040130f071580c0301103d100c00e07000242075503560002d40846100b1256034850180c0300c01d01241d4880003d032424602400d4058540c42c02400352100026030b20b192003142801c0501c1400c980c101c40c6040469003001010000c4039100b0b1005035180d961901d440710000c142d8480d010360f001245641c10350504500350b910180021080121600c0300904441000c100b07141c010307601c0100c40d95100305138000125540216004203001e10700000307000a20342288c07030f0704032005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 38262001 1250 38260751 38260757
    0x10c11010c03150e09030408060a14010506120a0b03010e0a0f02041406090a0507020a02120a0c0e060d061a03030a0804050d03050c0d0b03120c010207030806120a0308130614010303 79
    0x144000e00d088040d00d1900f0034070b10282010390740500520b8200c01200f90f000f1a09000c9a0905a0303c3c51454074100c000e036941e0031565695101244501032840101d40500019507106150269202c41c522100304d00a18076149184e440000003115582034110b48030203019081160100c10050801080424490408a100780d2400e541e0302c019000200160340300f242e000b0002006039031022424005004001c0000c0d00318007590546400581d528080340b50204140070040195440601d07050b0340c141400e802084110a5203c01c0200715603c040c800d4418940c480c4000c41c0191860040780c6040180b0139849606000102e00300c00c510768041c0b4098812405801280c2803d00b8100d000c0d03044400558404803950810851182c10202c1600158400700780a4111050b4101e019141410350b00010003086507a500056000c0a05500045103900b0040403920b11051201e042d0380155501c003200c0c030040a2250784400290390300105c102ca005040d822030000d0140450315242808440e40c240412008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 38263251 1250 38262001 38262011
    0x90605090a060e0601081506030a02040602010c0309050304120203150112051e03091e04060803190e100807050408030304032a030f20150103060606020307030f050904020c010c1101 79
    0x3030201c540100c1e000c5510b0300200b00203d840342c00044840d510010420f40c1d5812401200c81265100c420040d84a440d60407070040e103480c1042d10090a441c24403802c00201410802003070f0124002000300d50403030300300486486031010280b010a0401251382d05035440340c0d842c3d400010b9a86001582d001041d8810750a1714004030343c4118200140078000018641540240140360190510355480c0b59075084032603058066001c001c00113010342e81d240d00420003030343040840c03601760150b8190f0304214081203d003401031404560340082901e0800d031803020001c00840102042000d80101c08540180103a007064903541d15141c200940500051086200c40700c41e02c81c0320701c910450361100750320207540c140d540c1d0b01c4220381100111000d0800014400740d8500b034603106c50030f640d020043d4600c208a02c100845180d03165040075000c40310075511420540d081000814002580110007440f510310900307080d0b484401260104001340100c85403190a0f40c41c1201c29044c82c0e40148480c10806081002445 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 38264501 1250 38263251 38263261
    0xa060b0d230709090506011704050106051906050d0c090b040e01060207050901080307030c020102101a0f010212040b070c050904030509040b060406050708030c070c03140609010b06030606090f060409060509 90
    0x94a041102c10800044040304244104c5850b60080c5c0d0b04208149001206001540000e84a03844d003594221090307903445400b040182403581411000390700c4010103c007070300d25240e800303406031089500406880b0b64414103592824007401e0b00c840503102e100c3c02c1e1a200d54a66140445511081c000c5a01521400d100040c85140446819040e19a4580a141482c03100d603410b8989150403802281507001d03c1140015480d81c0d441420030006c0d800103a0f0942d010340c041440350b40a8003012403811500300840948018441c101290103d5140100c45030760fa900138280700d840d0344140d030410781d8881780304000e000c2455800405800352200c00c031030400404040c0b1082107007a20503403084101152080c81100b0200704440c000d50b903c811004184d03842c00d07516540d0102c0c1494550400c50311200c5401c00b41c0c6007806e0800001d03034060142c0008009044a5100190305408000e100501c40e850019407074a8544071007079914030004000e8511502c0b681c8031402c040c06010070380126070007648007100080d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 38265751 1250 38264501 38264561
    0x190b01081603020103090203251404020a050702120a171909030b0705071407030804061106010e011202010203070c1401111b01032715140702150a060b0d 67
    0x8080408152a6074218601c1d550042d00039040030542a681406021302c9107580250342000b6148200300003d09580311801d10b03040302e410358040303a202801240b0602c4100c1a81ea000000c42d854542c0407036404d922031420280c0e85160008402d801404d00c440c0b618180d01d101d071550701401024000503019450110300303483c00c0380c00001c244030180030002050040f40000340034074000c0c00d1280c050031003110704076003e0741d1040c504040b0b40d01c101c0305000f001404100c265808000e544404840002820303c9515041070000a140180102c08200121400440031607000700100c480041e440002c00340e5256030303180c090b02440000300d5020301041e108001030b04100c0c8081201680f861414030400b0300c2000c11001140103283e00c0c400042032410311800201c101e0000b08a4102c61403042d20f8a034a11b10f60340c2050750603034080361002c1070702e03050719001c1c0b00405401248840b200d9036400210f080503541c090b5214003070f205961003c0c0980d03400280d0400304284d960443c0011030003956410b039010b011000c00c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 38267001 1250 38265751 38265763
    0xf0813060c030c0303050603070305031606060b030c03070f03020c010507030605010906140412020a08100f0609020c03070204050c160c030606060f050a120906060b0903060601090506120603070305190b0108 90
    0x2000203e80d0031034100040d0081d440150040400b40403110444e443c0c1e91244e14580c0941d024005419849030340070104030301c900408001d07041c40b0380103e0640c00d10240d4284d180c08041d0410080c0b00c90352101c00344181c801d906980880c20607030000d110509050601900400842c0690350010340d0a10700030640601420012a048814102c85403a0516005840304c4000c400c1c0700c100c0c0e0103001210002a418410000a901d03202240000a090002140380c50100d0700180d0010900c00e005101c04415454040f065440e5a85c0654010940d9540c418200c4114403810f00f03240f02105002c0d40362001d000c0000c14460949101d100200120703911000169905030001860354005281003150703111062003003440051340640c41ea170100b940002c2c0c0c0d44000c166007468201007030b4030700d0201d00d80d08c9a01d010032909400c003000b8202010210708060210390300344135601d02207100ba202c400c0440c01075201005640001c640100c01e450861507440d03203281ea0200c080780f0945940002000102d08004089a2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 38268251 1250 38267001 38267003
    0x809010b03030a0c0c050414090601120b010506031509010f090e0c1507030c060c0809010b09090c0f121207022409090a0b1909060920030903070f0813060c 68
    0x55003030880c0003108842d05a030400b01103170a0a15400005819241c60150142240800400c00014545070206914045059018451010303140c4010400b15000c4101241900d0050751a2075407599810000c05013920b090781a00d4020009000024082030350306141c02c15226800002d00082082249460303aa6400050090784281c00450301017141c0c480000620b0f015200f420708131008540354488004440e41c0e102e0140201d0004420882210030a104000c00c10800f2510500e00f42002c2d150540d45411258101d8051542c0356104292595001c0b000ba042444020444500359006002e0390400d801a01c012406140350300031034001c907042c034001901c43e480c00d039a00e281408040e40411503071040c060304180c03066075203841a161503102c030100120803481010120a8991034504144226503803548008841e41c900300c00c19500d08120031040070501048048203403a84c40d807160107030a40c407070307010700403d4100440a400108103001d8054204801c0f03440c1c1d01140203503a5031003a140c00046000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 38269501 1250 38268251 38268253
    0x50f0c01092c04020126010501080106031e020a0212030a020706050603031204060b060408150f090c0310020703020102120a0608060c0301080d0c030201060b1b07060c0c09020d23070809010b03 84
    0x75280c542011042c01d81c80d409401494020941e15515209800341306c0014181178081440303d005000550308a8003050042009140400c9a1303209084590200800c00190b4840075400080010b583c1e4401c2240e8550306800320000c43d41c1c2c0c202004244c0080d0300c0b050b011141141800c00148085c540032040c2d40101200c0040644995110b03601c0000030503078500740507840301e414840411090020020071802d400c9103600303844c0301c2c18000d412030004040104034802581c85000c00c0c009903100851030850700c2c541844050380382c8100f03180a0703029004030008807202520440421018541640003c0e00722190b11099071040c0e2180078004c942e0b4442405150507550244203043d000c2481601c000e40c000c0d02901c00000d66507110310604890398020100049085e00003140004004810b0024500500040c02c04201501c580da5881d0340d50682841120307029580030034802d0741039080350000c00c5640950b0a49400644045130410400f4105580d8100020b00c1d600c0003030f0040e0030500c5920f280c02d0b0f00030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 38270751 1250 38269501 38269559
    0x705010203041802040b0406030c1706100c2102060103060f0b010801050d020d0203030d0f0f060509070804050c0901030f050607030603020f04090f050d08070f05030f0106030f09050f0c0109 83
    0x1c24000083e4411445800465003004002082d50000003c0c00141800e6038022407021802d01004026100c1200e1860407103008409010581c1c0d24031422070305014a83c208882c0720900c0c1c0c10009203007100f841410690703041031404151241d42c04141107042c0c3e84600420400072110540c00011940b180c00703440d0205026800600503403600c4840304036840d1000f4400c264500f5540d022034203541103117000d103403d1a11145a00340b00c10884c01040f05c02c074003540e010458180392400007038000c00302030000e005110700305010a0920401340104908804041c000e44010b50b9a491b01503226005000b040d01d81e8000d0341c0c0820003080c440d0040c1c5003141e07002800700e000c10f2a0001044000c240d02032046070030070800c101d8140040c60a0104125032021a111070f080c1c2d00c0c0508010f82007407054a0071400300507082040140c000507a04555054801c103240016100c000314182c0c40c0140000c81019015101d00f18211399002c1e00020f0000381d4401c00c1e81c86a43c455a01c05480303001ea01d03580303c0c1070301898a40c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 38272001 1250 38270751 38270759
    0xd0506011502030c0c040225030e0f030f07090915050408090a06110601031103031210030224190e0607061a0409050a021207050901090c0807080910150f0602071403070501020304 78
    0x54000c0e142e0b123189219401114004c80c03091010b0060045d2044001c80d07140410f400030380c500705140c0d0318042c000390042d00c1d038041980c074203503101e0b10140100303104a41e8510004060180d000c8440094500071b140170000c90919080002403604182d1074184114041c28010404034810000348a9a5680030010040c81e401d46d598100c00e030801c2c003003a68043c4800c0c00f10000f0380d040b0001031405125000750340c5140c541103006008620710355201505490407050340c40c0c54030408000848811080127084002c2070010350310202d811041c074251441d0302c060046841410700000b039000c501c1c05200240e4a18030581e551302408103036194001e0142194000d5083c0001504107100715142154484003590b000390f88500010703403c0c40702070f000301d2034a0782e940d40480c5600b03800146490b00f02585040c48400c614200d1511561040b0020707070004031940354502190410105a40b4102614103d40980b000302d4032244025552105803040410f0001d1117000d1145c0c41c140854424181d0340180d018600d03160070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 38273251 1250 38272001 38272009
    0x2909010e240a0801050307060201060b0714030d06090209040501050301050903070213060504020a09061202270102010608011e05010f080a121404090905011d0607030f09020d0506011502030c0c 84
    0x1c0355000441c0c0e40711941c44180560352900007010791100701e850f908403075410107040c94030349103890300300d032041d617151032414000040081c00f9520b9180d0f0101a0111850204210074190b0280040484205060010108541040360050065031005075001c0203507a91310000c0501365107050f1000100c40c2c00c01c00010002d8104250790a010a455034008150140d651020a0881c1d00c49802600050b200c60824441c030340e40100c0d0000115850342c015410310b1009800c404181c1c12100c05100c0140c5041008110342e4000e40040d4020880f03180200702440503419001c0007201c41c034801d807828a2901001182207043d41a480c020344070302d04000c14142d40c540c1d84448100070a0301440c005d01071182d06401802d5461070050003d00b140c000d000c680c6442078500142958043c3ca040f00a0000303d40800e41610400035205034015014900030a5196407030038120000c104110000e03400c900c0708040d013411300400150b01c50484661500000c5c4c80504071504a0700c3e40200c050000c0560041a01c1c17a8551070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 38274501 1250 38273251 38273269
    0x301050c0d09020a050907020703030f0905060409020c010f090c2615040f0506010801092001140f120a020a090b03040b040201080613050717060a0501080105130b09012909010e 77
    0x303c0a4540300040392980001591031004850400040c0e010240a1080650064007419601d0140c2070207140c0d01d05200001c0c0300c9004901031941e10f141e0100c3c0b0070780080c4094102c56a0060b8000003001050984e0506903d804020302407040000643e5071190494100e144281c1900c050b08805003045010f5600c0101c01c032000600140c40038121000c5d0000820703410300501c1d008045400000a44988071718040c0750040f801e40251599000041c09031441ea40c0000800703000c0502c10f200f055031065002c0d40d58600b401082419a0040403c000304061b2000c943c0c000c28241c44d41e920707590180c541e41c4844039220710040700c0050085210401040055000302032180d0800c00061480d01950051016801102c1003110904005440341d1030840312401038880c0f0b00c0e0071046c02d45891586505010000e8443e074418032619005074100d120320700030146941e001c0011042c00510000155a440d0400c144010340d00c5083c071124000c90710000c00c0c0e000c0300011508032103010f07120764240c10801d90030420030803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 38275751 1250 38274501 38274503
    0x2181e090c0706110d05090606010c080a030e01020f040b0d0608030301050d0605071b061a03030c1e0a060204060f120203010509040b06130c0c050606030303100b07030e040c030b010e0301050c0d09 86
    0x3d41c0740d2001c0d90040d0201805400640c1600d14005840d25040c05140c1c6040000307000d49040c040c0305941c0310302003401d10301110a4030700c0c10b0401040600001480301d0080c403428150002c094004079020030004036103030044c408603101180c248512078590b402951039203c280700c0d03d039204045100c1d18002410503001158000c01c0740c1008030481441207507040319018070b98030071903845d0f54428045000308064007060300c8035401640218204541d183d03c4a1342c9070102c1d84460301c006802e4039401c89145041060f055015840a030079900e03240d81d1640541030000c011103401c0461040048c510180d00a482584d0480b103004165003070315151603d1b850b60fa40b901034801034005445841200401003e40588d800700c00555551207500c02c03e07818000d09061002d86828860b801c02c105010b14400440901004e943d0002c0ca90340d5500141c5c40c05039a003000682900390414201400c181c030142d00b550103800c410f102a01c43c2c031000d48d203002c1058226101181e802614080c18801c030303094189142e020880c51 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 38277001 1250 38275751 38275763
    0x1180902030712020420030c0c0c120303010602060702060c0901050c030714070f05060f0405010f020f0d0215070201090f1101091805010603110408060105010f05040902181e090c07 79
    0x1845140e0046400c0a60303940080c90f44241495404045042c40d100303e0401d4428071010540c08802002405601d102c09052011604808108905450010301a0070004400281401c203004031021181d40c982e04240701c0d000142c001d08000800040c00401c40900c41e50b111540c440c508100203006560907000089078001700d00c0300b44200400598101074044a003260341d4000d050003441c21001da40c41443d2a008103004560074041e4400e6558410300740c60030b942c13007400c0403c0f070307003643c070504a250204090140e4420312422040482d00394000c00c108040506040700c82c4807590300c0400c1a800e0346e6842800801c01000742203420041409000c07001e000450515219075141d5550b1601100048603090300c811080e55400104601c6425210f03548103510080d0711181040c0c81c0503601e0b4bc55450503c1290b040c022000402d02e03600c0c0c8920f0403a4003400d880d000454a80098900303070310580051481e4036000791651041d02040e09251521403640c80030081140300190b565003084c0b5030719000010116a1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 38278251 1250 38277001 38277011
    0x1d07021501060c0c0909140d03060b030f1e0705030601020d090302061209010e03070b09070519090b030c09180d08010f051c0602071203060909030c020105031f080a020109090209090118 81
    0x801d80c124001c14200700e005400c1c1c00200c11f41d8455040c02e216112140405052410004100c95400380099982c00400b220b108040f5941d10100c664107461000580d1284202040802c40d003150420095802950700303034210b0b5521011000140c5403e0028040694400030501c464072031a08003100c0c00354010000c000100740e44141c1c4106902e9504142401c03a46510046c003084540d210800c83d120041030121400c1c10140c5203d007122901110170700039002a5a180d9030802960b031010446000c2e41d140181031884203180015040d03c60606a000100190090f403c0d90f0030340038499040141603d81c2d8000c01d0090b507251000b0000c009482d5501c2e8400f5980101100010600510182c001140141c0c030752a240255000020104c8400c0d0300401c032058608903400f03001c00e50220036200981c1e82070810075a01d48440750b00203620f5203050303c04401c0d514013070707400329844801080362113600707100380c0b180380289440b0111a4143d00071504643d400c1000b000040100e0001c000c1040030000404000180b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 38279501 1250 38278251 38278259
    0x4090203070e010605120603160b03150604030b01090b0d0209060d020a09020409020417010905070905042105041d0f0c0715020409020a110c0a050f04060801061d07021501060c0c 78
    0x50102c1c00d0b4855804038101051a00102c07401d0842290b0000003100980100d412001c02d004c8017042ca8003c01004010201c000340031440f40001d0301e00380250007030080361250390b070303240400240c3e130700b402195541410090701594504001001f8800c003030b03004009000a981e5102404081007003020141d910280c9894005503020b0644001c0000c0c2903c000c002d642c2e10b048c100c403008940c0321280e004a40b680b4044c5460f0124001198400542e140b90340302003a542c5407400c112090341e6205101c4030303005c818610a88034540e0400014000c0b14980c0f801d4542000150b0403540c8000022074440d11000890000195100050380003890603a11944801614004907004001240c000c2e4004400c040c0e40012040041e0b80c001c0103400810ba0b40f1401041c2526421000c555424854800e690050410104040302565550000c502400131300f03008214050f901c00c0205000806691654101070010740440c105901c0840e0792481000d180d490240b40340d1034614102c1d40300e090380340180c5031902c0459001c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 38280751 1250 38279501 38279519
    0x9021f030618020c0f06010308030417070203030a020106050406270e0f0706080f100602030a1809090f110d050d050c010f1107170a0f030b0301090611030108010b0d020f0409020307 79
    0x205002c0030501c0161070f000b4076000796107015981085803080380c5c4260010800180441d0850354403135400b1041407a4000c541d101c00c50540140d0000035410300010541420a660542c44034048481c103e4062002c030b03a4501d00300031103400070309031449200c085544c021444075031a08004910b80072401103902c68100000744600381080ca0708084005208001400318400140038410381100c0b800c42c8022019203400e1000e55240325051204080c007031012881d003044a0402c1840d80206441d80c0140301641d40b40c40c0c0404800758506080319064030021007000e503400d10200e1031002a034058002c0460f0481c0030400d60b41500700c02400f48640d901c8036020192515070303000e10b00c402c0811014103901c42c14030f0702d416046000304481d00e840340c500a001e440e4010341d0205050507402030600300001c0d00168140071a000d48800080039203032034201b0000551800c1d505000318122000785008000b040a2070040006440c410103020350700a8a0b204645070703030300e030541c804090310303100900703c0d101295200445 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 38282001 1250 38280751 38280779
    0xf11090603100504140711060f0103030e0310110901021009020a0308030c0d021c0e0a02010801060e01050c070608160f080a051f090b18011a0307050f0310060f020109021f0306 77
    0x1711040b00d00c03d03401e0042803a0464420400303690300c440500101d1800c1c00310041c42030014400681001403906401d010b0392000c0c80f8800508030004800e214080c40d109040000368042c0c24040d0052052280e000c081c80c03034a115041c01281e00078241420586141c440000ca504060030000d5021401c010082e21041140700074284301e42c01c82a080e6032010141d86082c12514034201080d2a030b0001a040b20042c0e81c48819103054074018107003100d030ce0740d602d001201c50740900011511280b01e061b902258082d0081051072241c0403143d00e00c1c003409a0302c4022940204600c002030081440311011840c25100c0d0303007141d54440001d001186444c241d18200c010a00100d600041d20107644c1d205100035030812005c4c0011807603030008a030b0910352401c01e11018468420440c01c50505012010031060307845401140c0c000728085d02c4a54490801350303000000b40b8403e1103900d0120303e46590101c030f15070040c010f050300103400402540440d04074405102c0100d410302d8940b001c06a0b12000410328040301c1c964 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 38283251 1250 38282001 38282021
    0x30f0a03020c01080a021c050a020c010203150f03120a0309020105070f0605010f15021009080909072d020c010f09050604030b06150c0d050c0a0209040f060f11090603100504 76
    0x800c89101031000261134540702802194016004111815248011402200011820600014a80e6030f9036130320a000340038001140e80503500002c284440c1070702c80420905c0c00802201c1c4028080307071100c2016550800e188691580301c00600038402001d000e41c1c00303059180d0060406c1483d000030b070f94400c0304500c41c84504840c0250b80d100140f20b400c5d080140c00018001c0052040c0400e20300c40c034080e43d100801002081c0e0962034240090400804401b901c0f001d0701d01514100a50824400c0607100c1c54161740804981000c400380f540c808a000c07034140d203401e41c145d0040d00074004040c004480508d8641018400c0c890300e01000600c41e1541c2303008200460042d100e000042c2000c000b0425400541030240100600a1010054031600410140c000d28907a003040c0740c0e2054500345940c103081c074076140a98041c68100420050200e8510704900c1e80b403043c5420001c46d100545140c044448000614901c24410b100b9003840341441401160014880c02211708010b9550001a00741c66070714038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 38284501 1250 38283251 38283253
    0x90304090c08090106060905030c060d0908070506180304050f06160c09060618060207170705060f090f01020f061906090f0603170702010e040c0522080c030309060304060b030f0a0302 80
    0x820803c0c2000f081c8203a1014000701e1070032000c800d142a0001e0b55482c565103100e842070300c0006010020140503405290b13515400480607440d642d0a09019403109802ca406049413004910324824284010040f1030540348000d2000500c0000c4c00203104071900300700144040b001c40c5400d2071010400400c000c400400b81c1d000c010a0081c00c0c100e008190f600000d802c0a0a6500d040301809000c1d00400c0e0181500d14420304115100c03003880019142200036070140d60000340006440309584000b40003003d40e9282580d0082d0800c0384e0900481c0c1c1d0b40c0794100c8041c515003080003c110280b4080224082c1d107802d024000c2a00d03610f030540c48003103510b21106881c5e919a0b5160400070002c0100a5001e8112034005403402d203c604d40020f40700c0d40c040d4090342e1260380c0d613500030303080c0c0c074064015102502e00030010b040380911404000c02c440650b07806a40110700c80c03503049100901d000804c4441c090400340132503045841c1c2e5913030302c00071748585041103615015074031030b0305203d1a0400c1500b041078080e81c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 38285751 1250 38284501 38284517
    0x501090b0f070909050f010b07051002040303030c030506060703020c040e0a0501050c0403021014070618080703080405010608010e0c0918030c0304030b01050405070e010c0204060b07050a0b0c030915090304090c 92
    0x10b00503102d8600b0340d0100b641581480d082000007444c0c40c43c914111594410700907500d10b198600113060001000d90343d070040e440420b01105044d4154494400b141558400b00303c00e4903007008001c5140140c100040041c3d10940d080050b03400d29802000b1442500421074011030156a14242525011144070490100114040065240429019942c0780482c248020031041965542c00c00380304203207000e800c070b030f460300e130150304244000c0b060b04a4141c1044005844181c179240040c8101003d036030640712076003021004216810107203d2508901c4c2c003240180394400c410f00c2030010780c0d10001c104800f00c600d1b0700c10500804809200410320101e91034040e55a40d030442c5003110040206030407c502851a00c000c00149540003500c88450480074200b030070341d2062600c009409040b55802440d9402d4010070703802c04004001507161445882011800c0d00c9a0310344501042500007201c409940780d0145c58040c5101060240c000c0c3c1020308182075130301d0991200c240780181c9007045c64640c0010400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 38287001 1250 38285751 38285761
    0x23160e0a09050a2a080402031c12060519030f0507050603010b12070201200d061502010c08090d0503160e060f030702060601020a03050a1202090a06050a08010608040b01030b040501090b0f 82
    0x144201d03030b041e02c004d482d007801c425040f4054424403500040040c050008a002107019940c0800141200029001281074581355051004002ca811494040b480300d050401c041114034150020030301c0c50072020080c010451075525aaaa0f40c0c690840c03e5a00740100743c00840c0a0301d645000790b0107048043c4900303680c1e95506904084503480105000c01316450104a0340304104602d00108182c2c0385004500e0b00c801c482824200206a250321100e02d000e01c20803000303c0540c06402c00c5520220070307203840305180d450f1f4000c16285c0d0000d56103a000070341c2c2000080c60720100e03080201c48604076480c050b030828161070007041d50b583c0002003624440e0b00c00300c1045101c550400903c0e030301000c00c0c4090300d020806e80c3c0e0302800a024841c0c024052181d802c0000588000c40d9058900c0c1c10f6006000b84420380d540c920141c0a07078400c07101d050000d1041000410100d001740542406240c0c04980c4e58010781c40c584401801120107401142c140d520342e0001d0740400d840c5091207001e2008030700456014100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 38288251 1250 38287001 38287021
    0xb13020913050a02010302030712090b0711060603030301050d0f06020a0503040c08010227040b0910090b01050304080a0f050403081b010c020109020607020d020102031e090423160e0a0905 82
    0x81100c03890941c00c1200000040001c070b08510b1a03942030801507101c4c0c89a14040da01003408000d024605450502244180004c3c01e010a01070043e0b80c45440c0201a20b1681c580c80d15411035606400d5481040104181d081c0b6519055001e0b0013100c10030320a44040d03071908240c0e8081c9032071301c00248000c024401030045500d00040103203400c0c0004c61500741d48158410905102c038a4000f00e0300c15150160300d4586483d04400314a69005080d40c0281c900208240d501c58030501524012030314000c43c0028035401034040324001e0790040802c50071700011450854215210348804410000280000000102c851001e000005540b60307c50070030714605001c542c21102254030100c210381c182191240907880702d00480d6816501a43c03280c1041c07045000507481c501c01c1d081408a4140c150240c4441400d440000d80013400c0115402c0c045000368890319866080c010038a540507290010100e40700010000d4024400780490505010300202c800c0001c416102d654028002682c4841c1000a0905 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 38289501 1250 38288251 38288269
    0x62f0f0106060306050108060108060103050606090a0803030f010f0303090e0c13060203070312110f0c15070518010e062502040c051309090c031202010906020706060302030f0d0509010f0c0b1302 85
    0x705c20b18003121a40342450009240c0303113000d451039062655803c007150356a03c070760080b14540c0b00050101a83d0341c1d510400300da502d034030468001c186486030400105070b400010b0f861400300c0c0c2d01580c503d030001e810403410500300c1c05d019142e00100318007080510340441d0082105401400d40e0f4018544038940b0341000b90400d0044015054403d10341301003c1e80350756000c03058030701c0c1074800c0744800c2d103503101c42d183d0a2800b0090550b1032107071204a410000f031145c2c400000c1003082038204110100c803403c04019103507206407400b031590181c4240038030710010040c14000355045d50780032030203419a041a008613084440707000d50300c000150001510380540c035000302e5480091248180030030014036941c5480b100031503e8000144100d142940501210f4400d41050010940181d8115590141450454010800d80c80202e029010300107080a0400001c00c55107140d01c1541c503210701d002920700044032060842d000b5142801000342d030344404103213801000c0e48506616030400080e100315004200c6084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 38290751 1250 38289501 38289509
    0x20111070605030115020304081504170306010509040903031b090603060609031110020a08031504060b09030d030b010c05100b030c0d1e03030e0102030f180106062f0f0106060306 78
    0x240c4990020800181d00c5000c4a0441d4405240c19075000c0c50600704904520550b40480440d2060304ca0080d10020081c0500c2d0156200b850f038180e4065410011000600044803801d0120b50305124004842c103080e002400c00d18480d140010315241480c3d0180016288044000001400c000041c401d19406200d01000703071640b400e211704850b00c0e59030f82c07114150480107054000c02040c0c68200c1c1c5075008115403003009038040d514685900d010112501440c2c08075110b648524100040080d0040030442100d010140180141c8903810705940c040c0c0c01351080276000da040214000040c40031500620400d1a0b602c8024400b1039400c0c0300d50100351900c02c2c422612803007100720389008800958501d0700341101d020b2101e03c5403014551400e00f0780081c440041450301550000042100328106070401610411440075804410014a0700c0c1900300e600e18013400c0f01207281280c403540c121b20160510001d0142e84a10003650721100d1030a9414202da1554002c40c9079195501441142d404d4010031000d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 38292001 1250 38290751 38290753
    0x2040803030a05070e190b0a02010b03070b090a270504030e10020114010b0405061b120a0203090a0b04080c04050c160c06020f060f0109051801060b0403020109090204031a070203130e04020111 84
    0xb41103804101403c0032114481c03659040c1000508c00303d214000c0d0085a80010b004080d41c1d40c1e00d13a2aa850000c81c1e009210281c819541103201007039202c180e00c4c12034044074001c6a68900380500c40070340c40080001a00a40902480200e4280300d5a90001901006052075002040d81044602c076082e0800041c1c0108034044410b0200303001544845040c2d4910b1980500554050f108c60154a810404500c1005648072400a000601075800200030200070760281c0d603170503906595610030045400b85016082c0c41d40c000240700343c40c51070141c1116030440e103030905a514014060061021196a45408841408006504000380b84d01070181207062000344019104a103004a1040c58061050149001d0282c1d6400458800c0440c00da409000d504000001c101c2140c542000100c1600107100c1240020710068010500c08014000c0da0201d903070090540045925018265252510003003074141184803d12400340742516524110000707010702c0d260041e031400c143c00010039170074004048480c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 38293251 1250 38292001 38292019
    0x10050a050a080a03080a06050904030305070206070c050712110405010905060a080613121e02010b040f0911010c080c0601030f020f04051608060303120a0c030c1103030705090402040803030a05070e 86
    0x180e4071010030340f00326403039140c5030041c40c80e601c07140b42800400c400d401482d04108034404000405802d0f1707002600620702d40c3c00b103854541c0c41c08001c55246405003402402500108400c0200e844818010601c4921600c031540980c400d4001140444000368404d491258556013030080c2030030000e400402034008034010301418035003070b407055404ca54900300040140c81d00506182c1070030320807403070704201002c0030318075075451920004000d018180c4c003110244114034140c001281c54450740300301c00031994070650340780e2541d00075001074807800071030300c02951180b204202e15101c0d03540500c03289010394440d800000c8102c5142c010311140c40c1c0c01701d8400d8091482c000902030015010b10039408964050302d4681426a6030001107070a600440800090034400d910500c4021805034103c11038004035540d0800241c804208100d503145190941404260401c0000c00c845d244510001c000343c04001d0b001524050362403441c0c5207540e00c101e6407141d40e11b80c3c41c0c060115056000440381650b14044aa03081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 38294501 1250 38293251 38293259
    0xa06080403050702190b03161d030703081605070807060305010f03080315060903010e010b0316030c090902150f071104020301081513050601060f02010501150801170a080310050a050a 80
    0x102e24803902101a101d0f010f00d113000c81c00c03c0e91400e41000903100269204d44c8a0601d41c42035070b4031240751054800071421016120182c001e000c0c010710711016000340189246803854407507000650150442110344401420142c010400810000c40207002400050003817925122004040310f9040c0c114203182000b4540410101d1140b00a49410404403000300c00140c0107540010036500c41c404001c1c1e019402d10407140320100042d4440345100e10154299074290142a403020040d518a02005003100c010910501c0003032255840140f800f8406800000c403110209014171032038102007201c41020100180000401882d0840c20941c80400e0341e0a60455052551060700c4101c0022507504410b08000042c00849001d0018812035130424241d803030b00d5848600c0148010311030142400558202000003a09034011011080c140d45150b49800c1c083e400d1640c5241054642951355405201d142c0080703000c44c00d0300c80250b009820907103c0022052030082400086001c0e580898400c0341c214100308 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 38295751 1250 38294501 38294507
    0x4060f0b0a180915020c0615010503010e090709060f05030c04060e0624070302010c110309030a12020f010501090507030c0503010e0a0203060a080609030703031a0f010302180402180a06080403 84
    0x1601c810300c80c2d44030100c1c45070b0310900061544400103441c51540b40507003800070704c4560042041e6601901580c0c3c159440001441903d4000c420b201e0000d03208100400c4100c1c18148256040b60300c1e103041c2d4020b20355902c030001c10364800b41c01103074840c48290f10402c003d00d07042041c500e036403070300740c50030701c4010314084101e0482c48008203030902940c8081860b0707202d55441c03409201e268003c081030a072650103500380240244030480d01080407848004a28402400c000f00351510030700010018591201e05a4500909155045001065210b0042100d480000a01803030340641441000082c69117000c407002001d0700c10030303100a410f001081005002580404c485198010350b00140940e898945101182ca40307009039020030281d008690a00c80000070106c0244215806690140203a0722010058501045a94001c0c0d501007030107a0b1024844d4080c3e005020801e006107601036000454401013002da030700c0550100e40c180c24100c140003091400006c0400548060316044405180c035503005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 38297001 1250 38295751 38295769
    0xa0b0109021804020409050103020a0e0c0a0c030e1c020a050105130b090102031308100506040c0c030806030f01150510021207140703020a1205010c02030c030a0302030402180106020604060f0b 84
    0x940000780c0004a900008128030300c2c00014010107442107681d140d454a44c800101403c0c00101d01c02c130341c46000040c0e90020110707014020800400543c3c5017007040c0c40d040d110b00f071341d124003103051150205503113615075101904011000c969000e41d01148400e44100419085560007080c18040180051210090210300400940315015401a91114990b0040c0c3c514040c00500c141d000f0301c1e0f918003190700c00c0c001c1103e540c1110000014019501c8410410040d0740c40388404400060b41d194144000c40d101e15070175030304a0300140503240c039038010071840c0f420740348101600441100b40d5641001541058100c5003001402c1d840030b0130307818045054200f0b8603c00c407940508040c2c0b4042e1600100c001c1403010750003d5070b00404001005a40d03080d501e6900c1e0204d4015102e40d483c180d20f210705c150021040740c01900441d0040e52420041040a40094101a1003030341c0200004620344082860640640d000c0d20058000b4400f40c600ba24040080c0c1e003491144206c0903003000c00c00d0406460761585 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 38298251 1250 38297001 38297009
    0x1030b1f020f010c020c0d1104020f0a020601080102070b0a0207020103150b0702090604060302010c020112060b13060e01030504020303041701060306020d0905060112080a030f020909070905013005090f0312010e090a0b01 96
    0x1f625040f400d103040c814001c406600035544c0c040d00c00a41705211441401c010403030180d194080c1c1e5026aa5903100d60300300e0041410242c1030000010011b903028140341d0092210600c14100040d40701b14040b03100c078030f002c40394221134070b10382c0000f03195002c7d8a05007580c140e1050702100d0610280d425a07000910340c040c036000003418012031500c008001c442580140c00034201d0001500d460b07446c0c041003996448141e2060101080c40300c0d0f51729a0b0b40d4402d008580c855034001d00114030b032500e00101d82c0c124040d4946455259540c502000c800a400303030009010b003200551011681c5021410410b04082d0182d200040401000c042d0400050f0100e095400c1705815042c00580c102c1003011401c01f0f8422500007650151003030007048141a008541201501d00a0b030724050f0021428440c0b07580b41071805a1401e14120020001d6000d21312038008681c09907404059500031101810460b1440e00a410002e41010401e0700500428003a007014507481900e0b100185100d070340790703102c0040324441030003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 38299501 1250 38298251 38298259
    0x40b090607050a0609050d090b0c121c0207200a03031d04061508041203060b0f0714030f030105180103020603070c060b0a060804050601060206040213020901030b1f020f010c020c 78
    0x1d082060190602820406581162051102c0c03240f81c85e04645038810029001c0c040b481c840b0001c01c0132141c60b81501c1d041c5041400401d103103000c0b94802e24090300042403240c01e04488010520420301d103400070b844100c1c0301e940402420001c80f0542c060030000308500a006420b0b403981000425406607107a0b075030b0000d02d1054940b400700d030740115024191540114041c810408088070b4040e03401180d007803003113010302030000d10455809012010780b580d0f4032a2440051051041c082201c010300014041113100e02e2801c01d504c5903540e1201e0840c0c02c80e00710076080b480c01000400a900b4098140400c54202c01e01d001003c3d8110b6001800500000c1c00e80800c20440d202c10344208020f6038090b0310495030007440162130640e45e1000a10820781100d0441d014064030000180a5000080c190f0085900030039004801c209020b61304025001072541504058407442902110b454501c1c4c8118601d55143c40c09441465588000e0302d006420fa41a00190785406084910745502241409249500712 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 38300751 1250 38299501 38299507
    0x80d08040308041106040608040605070f09050f13050f100501140706150503030d0902190302010818010b0d06090b06150d0905100e030a141207080712290402040b0906 73
    0x4141050700413005964250800300010703000c140281c0041c1b8803031040d449980b050009507103240e41140c21548254078440400d8003540d05000a1400b400400e4903400081c0007102808a4020100141c1e281a11104541d406200c10300c2242020780d1040805842c080c02c04d100040e0000014514901c15800c014000550750811030b403c65400304115802480c2c000c1c100c0e0384404c65104000007c021309141240f04070707407a01105e81914240e012180c03c4a40585070718086540742010303049000302895900301c00e551b0b038841d80240d40d591050706243c2c1c640220740c00510019103290903021598084d11f03103807107903160840044a000f1100c003260020005003801103141c0d9064589030f440d1a041401c02c00240782450900200280004041c00d9601d1059840011026110303842c00760740d00c6080010b4200305402c10015115034081c440c45074201c0f0700740c41c1080c000c007070840740807003121800301e0b1a80e00000d80c9001b5107900100079900000d40e4404542c00c628091403c1e03a0344060380b1804140354000e80d0b00ac = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 38302001 1250 38300751 38300753
    0xa09020103020702040c020607090e010e0a0e031e04180519021c0501091a0114090d020f12070306060512030d050a020f0304120201060b07080304030309020604080111090a080d0804030804 82
    0x2d0301510a03195000c3c00601112041c807502a480740400c50391500058a61040000c044d80841d00d1a8126004002c1d0a5050748445944070302800302004001454881000750620001c2c480f440e060249903000c41d1147c8a90600c00308142c0c10031880e0304400302c0760420302403084070500c01ea600183c2d144110001603480480003880300700000c102000c43e10042c98880000b414003200e8100d0b41110542620f43d0240000c00c8006407000c0040c49900940a03109001c007000b0f5080c01c810015030540010000501400c03880c00007039240700c100c0058440d507000b4140400030004903015072070140408540e0342d00e9140e110380c8015968002d00781020316554884000c155202c0860f41120015107900e001c0a58030314007030401c070144112070000345005610744038000039050540416507603083c1c0c0c0045850f01e5525940c07412070103005840801e0340d010008010000d1418024804c0a00040080780403e4444413030004020f0840d9040d03000301c00580294408580e120f902200b1240d205515040400064076030b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 38303251 1250 38302001 38302007
    0x302070b13020111010e240103030f030207060908071103010e0c030a0b180601081f0b0f0409050124050f0909030a050a0e130e190209070e010309020303041d0705070b0a090201 77
    0x50704180041c19483d107508012017480101300c2d0320307081c42c52640d880020001f400030394000000c00d01c80580000c42c01a141c004c042d109800500c031140c01950086400c94983e101d500455109003030440e0a0440b41e0310455050a00780100b1418912080281c032001c540340020070380b203020001d00240000c12031000554032a116120111071381c0160004c8904c4c5685a03071f0584c5e5184800026400c0403c0542509a030a0026008804040c0c034017a00440301c0302c8809003800701604800702c0482c1d5654031074113507510500f0504001c02403200c000c40303020152441d06061100100e070a00001d40501c40300000c11038440c100101b01d40505215143c0250385109215045400c0c100180846031300c03200c0040d01700c20f14030407604402c04503070100f01500c1ca0380050034144200701c1c000020003900300a6044c0083d00d903c0c010040c900f20800181808107903180c0c0c5074002825603121350030a25040c204215000c240029000089600c2201410202d1412210303844881650400511510203551240288002c6900c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 38304501 1250 38303251 38303267
    0x1050703030f050702150108030901050403080a0309050d09050f010302071208041407061d0906010c1101020102090604090204090e0d090e070e0306070909151202040506010903080a05070605070302070b130201 91
    0x2c00414100700b80e0415460003926050040020f910744040140003064a10022048560880c41615414640b80c55a0340c0c644103500003580b01024103540b070300c4000200e074040c13280684081d9150340d0040c10343d0514040080d00402c1c19903050405105108800c0015903102070b0098001c0c083c1842c0d4115600c910b04240800c00421320b2044c3c90240c1080080e01d1341c0c0041d141c900316403090300203401c0003a4000c00c0c8540e110f0119081c50000e07003404403d002023881c03041e869501800c18800035290551840106843d40c0c455448005115030015082100000b54860b5400755950900600f6250b0381c000001042c502d03c43c010384201c04c103248042510360740903910421905a014058845910340301c0c10180004480f0b2086466183c14900480e1360f01683c00441819224060032003d8000c0403034080c03000500b4018041414801ea000780131000c20000805041d180304641e031070f60b0b030313600d01d40c58008245c50001c1c18982c03c0c14010f11840b000500101c040320303404441079801407000c00f035600040320205 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 38305751 1250 38304501 38304521
    0xb07020a0305030d0504020f01031a040f020d0e0a11030d0503010e1e040809011403160503090c060c030703090905040b01090e0a02060a020a0b0633040509130212010603110105070303 80
    0x80f0000422041003001d60304268403070340c000c80d0000104002400190117070754202001000902d2502000401460141c0c000b10b5941c07100c074070042c10102c07400e90075000c4640465880a150f44949044010000e06c240c0e5090450740031303009041a9010f44402500c140818014903d000389210300040030342c44188156105d5801d08054046542490f0410006035844291028005184000c201021851003000c0b02d000740c000c0401482c1d501c10141d411200b5400190039511680144150fa206a5803190050400003084e4000340da6602e0326480c01404002c181d91185698505110402c408101080e5002d0b04403101d10501107002c0d050803500764100070344000000d5111402180d08000d05500042031004c0d02c0c4100102c0300b0b2030b1a0407003003000c40c035000340c4207050341804000869640717240414118001c0e141d030201c403401d00303460b40002241030408884100903800c0801b001c5056280c031000111a0402d00002004100e0075a21540f0090010303550030340c188440052302c9800c243c840da00ca07008030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 38307001 1250 38305751 38305753
    0x112080c030703111608060a150302090403020717010c020d140d0e03040f080f0601050418200a090c02060f07120203040b04051606080105010804020d06050906090d0311040b07020a0305 81
    0x504603d140107404141240b20f0f01d40188500302019450500b07030f09101050354000310013410141c0e20000e0342005012003100008805554890000c0140c5036031303202c0d078042c0b4803903006008414102a040100e007125408901c0c8141e04220324240620f80125020910b4110703032a00d540503520030101c2c58200d10075504a40680c1e441c00b170090701402408409070054615a014046010303642c0c80003141c0d10008400c403490aa004180100281d00d000e80c0400603101da00c150784100d1414036141c03121403e00a00c80c03010003070038121802d880d520348000711a0280004280800188622120007907907503000528604c081e01041c400301d0700392030050300021600c0a4080b0155580e01e0103182c075140c042d40a5404480d03500c07920540e1984400607518160583d049a91040c00e545e10b40001142c0108014000307907002103410504001007007142c082c2c00e1083c140703440106414105008041c0c41c02d480202030104052801c045500ca0750100c0703040b074084620804c0c0c015140c047d80d000003009445a90702c02001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 38308251 1250 38307001 38307007
    0x71d130b061c050c0f040b03091c050703090f15030b04020912010b030705040e0307060c030f051609060305090d05030c0408010608070e0112020a030b0403030902040c051b150112080c03 81
    0x5140200d0901e018890b202c0030a00140d2500351320342c010790080740843c5041840a2105101d01c1002401950703220142e401241c0010400d052164018010007402c08000380c00000d441c03050581040184008285a52100e81078501d441e10088030304100341181820540c8800540c040c07603030380d03405660a8100060100c4002040e60145500070009440180d019005001c0c0000c2d0626181c851580790400401c0994542600c0e80e403120014000c0a5080041c9541c500d01006841a00d01c1b80c075100f9008490903000502c40c106000d000802c16034080d1040509000c10081412404142c5a1281401c0c4c28856269200d58180e00c0d840d000e140c1041e889176280103c0083c442c50f0010704030b41241c0d1101c4407204030341d80b030720802c583c01c0944000185d0040c0859004200003045c4060707069000e030085c071300081c02640940c0000e00b90f84240c0070360f44c00200045081c5400159160b80052500c031100001d20700c0e52141031891062040510500a00c0010002c01c1c0301803000b2141111104000c200507a90323 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 38309357 1106 38308251 38308267
    0xc1006060e010c03020a0609080a080609040206041a070b0a02040614070506010605030703020903060907090b04230c04090e0601150203161103010b031203040605071d130b06 76
    0x8118846d0030140c0c07000c10590300c00d0b0414148104240c0f071761703a030000307070010144c0e5070141c001c82c405c80c104014030005980741421035040303482100800c4035181e031400c40180140103408002e840e00058204200d00c1c82503030b5000740300341d62654852082c081c042c40c0000c4070b1030041c054002c01682c004401441a42d00138009164040d84503d009840c212528000c00e09080041d507212403a988200c2c000d102030720b41405029010241078504005910805402000f0500c1d108404146501d03d04041407072f009201e42202c0140c626460144000c101c0440d1071980e5981c2441801980402d03846c00900c014800301c21100c04a1216107c1100c401050310741c440304110300c90f0015850f660f00d0090401540341803100480d09030030144041d48926080c200340c0103442c0c000300807104200440300504108400d01d100203406c0300b810b5074910303054008010b0507002411409003595000101140c440 = true := by decide +kernel

theorem cover : BRFrame.Cov 38129501 38309357 := by
  have h0 := BRFrame.cov_init 38129501
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38129501 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 38129501 ≤ n) (h2 : n < 38309357) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
