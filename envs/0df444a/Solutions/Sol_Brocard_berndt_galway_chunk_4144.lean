-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4144
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:41:34.742556+00:00
-- url     : https://prove2.me/submissions/316a1f13-8800-458f-a98b-e382890a0fb6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 745143884 ≤ n < 745323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 745145134 1250 745143884 745143887
    0xf0f0a02160c0509070906091403030f0d060806010906030302101a060c0708010f05041205070507030c080f06071407021c020d080a02070f0b070230100f050702060601110f0706 77
    0x82240b0500e80101031940014110911480d043c40a47d40350b03032240025a4108901404c0c2c480405000729018842000020880b8a444019104003912801c0c0814001e051521403802d2002c1a4009441c1c6070908005000213500840c68002c05205c0358800a11004007002da15424034001c8c00b055000800000c04e881d6002001c101007060f10364480090004c20444035050003125001c031400b40650041d0f01c2c0c41c8a200d8814001401454050320803201003030b880303494210600d265035000302c860f54401852100c1d1044107009195100b401805e1078424992618a80380c410301c83d80e94021f00c01c80307000c0c0386268901c50040100202030340140030445d41120900d0421441d5110000450143c450030303500041d010325800c12541512449040541410401e80c248607803220300030481c030341c4510000c021304403104400b0140d016012100c4014000145035134610401c403200e400560009a04200401150320780002e101a00181d003031030100c80c4039800178401428060070000056550058800021f4400d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 745146384 1250 745145134 745145153
    0xb0108010c02190308010b0c031c060617070e06070501180f05190f12020a060c0906030b0a050603010303110f1606090602150703020c03090a0f0603050f0f0f0a0216 72
    0x1070180c1d0220340c0e115000c40f07800d009041550b40d000300003490800c0180100503404010704803c60030704046a0900c400c850075002c25a920b1100c0c001c00381d43d9084101305140d840a00c1071000c0d0a0310100da4032034148180000d11030515034907454010f0707030006021000c10109501c0a01c080000345258040c40c041c0740303050352000c042014103480c0b03031180c00c40c050002c1781003a41a45400703070300c10401c0080f5a1959503540030308108080c14000c1d401a1011b030340c046111030080f54801c14590313480c03d40b554140307000175045505440006004180e0200140800d84a180482c0d040d80d8160a010b9000030740700c0c40f100d01d0044d91039030781c001c54001c10000303607101000c400c040b5058424907218074400302e48446027241d0f90350b602041c1307969201981000c515294069801807902c2e1500000ba00c1c908040c0c5800f02e07640d0700d031581c4580552036070300c0360800c50710742c1c140b14661304203403005d044214604114010110f4580c01600f030040c0810420086011002680e04480c0c0270104010b42248030600760801c00c034103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 745147634 1250 745146384 745146401
    0x121e0f020415390506040b04060501080c01021504020307122009190c12020f03011404090c090b0d1e1202010b0d03080901271b051005090d0b010801 65
    0x14540081200e510103010b003d103c1d07080c03034454054400407400307450b008200340c083c0d0f603880403420101d5401801041050003003030301c00c60281c1d050b42402d08040c90608101c59059000e21010b411003c1c10720a01c1c0c0c3d0226840100d035042c1c86980e0001c0e26a400040d041c40840d03407042502c1c00c04c2d80c4407442017002104080c0710408141c60400e184108103c1448244441280d10714410303502c41c0e02c03074201b02c1171a51081c1513901d00c0e80740109640808191510499004051421440c1000710041021102100c2c1802c000c81c0250781c1413015036923175900c10f01c12443c0e6000f90070b8020346810141041c0e403a40c51100d110b56401c05846920925002c90307440008502e21010349000070048000da080714014003804801e03072030103410300000c010780d920704450500c4050290172140d521409047d0410010080e042c17015103000100d80391411716494500d5194000700d1484a040071503c2080010341d4407007a503280c3d00d0b1018104169540c140c000000c841c441401e500900c001304072000440c02c541c055108682c0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 745148884 1250 745147634 745147649
    0x7020a050c0102190803091203090106030501050c0403020d1e080d09120804150c030e1b0307091103060d1e0303020d24300b040b0a020a121e0f0204 65
    0x1500d6400c1c0e0012611031107101d00d0300c542c00c0d244400329000503d14400039544100020203460044d0108522400303241d00658034a6940e130f46840d81401840310070320600782c2000c4807241e21407800d440d5078003180310b201aa01000d00142d0440a4640710750280001058085a00400c6103503180500c0140070001c009a0205a810440c1c2503000c0c81d0745401500c80342e0040390080040300c0801f18407040c08021b080b81d051080e0405071039415101c20220104980384003020002c4008191444c080107052500d8403a1b808020b0140c14151800007100320981100d410007000d80e0103084892041c1000c00032a2500400d031021242075000d41c0d818950302da8040c2c80d83d6803045000b846440840708880c800340b100404845000f0182c640204220b00c51480003c1d64255520221a20700c100480000c5000003140b04c156891044181000200320803c003150b548400d11840c00c606180c680341d0000e000400100e50840c10369580d008000400d1048044130702c440140100501c01e803401c608040c0040c1d0464420400d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 745150134 1250 745148884 745148893
    0x90f300a080d02071104051b18090118050f070909180803150406060c050c190f060c05010c1b0f03110712020f04050106080c0702040b1225080309190e07020a05 70
    0x500a103054050140244a030703000d500007040b00002e58401950001e51089c07d410b000480f1107516031118190305000744102903086178511041e5000c035041ea100104221740c000085c4041207902d98110b00d8110665001d51000295644904200075500c61746030030141034a81d010040110f08441062400395035181031700e0a01000741d59541c15144564144801411500444d09002c003500f40100c0000035590f40f00103034008169140e00d58110220241c00680c0090b08595410090103c240039002419030903182402c00c030115500e1540046400703c100030000074201b4001c505140c0310304054240c0e80740c0c040644642540c3c404403032034800c0d66264128018003411011030158642407041504882240c8c5504403a0f40c1c48040000d510350003810200d9215566480300089915001201902a14110000c0110708400c6894444000b14412104142c0703c2401c02841030300342c040b05a640a00082d01d50140d400c0a0385658000c440701e0780c101c02000049801008022a800900386651138060420394 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 745151384 1250 745150134 745150163
    0x9060906050402030d26060a03021002030c070b090f060a1103042702120714040b04030f03110c30121309020a05030105210a08090f300a080d0207 64
    0x261a00304680c0021b110402c2000340110a850855212507800000140040e65007900d0380d001424130a07001d84110300507400411604072131401046000c01811043e50818103040002c0300180c851400841414020440402c14880700c078054008202e070b0452450030b0782d07159611482d50340a940340503015541096081142d00c2d8401003940b088843c1b1005005480c06295240d110645800111200401c640e100401c8009601140000544099440b811030000b22201b203040c0100a40c1400d020304013180c011036550703542c07551450504004034540c020f4404140c84900c084c144642c40500300348005028646442580c202441c0040030405a0700110350308544e210541c1c0c800f24000c044039800840e0007000148200c0c0307000343c0e6481c4403010001001028102054185041211000049079602c4003c141440d0320b10b0f08c00c198402c009015110400c050604012024a0002c030345049090907041c503502d203440301c4c424040585242d40003ca11a59610308a80810007035000c008103413203230500394120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 745152634 1250 745151384 745151387
    0x61614010506101e030b0112051627030615050a0305030405040e031207120906021314190909060e3307050d0e0f070b0c06010b0421020409060906050402030d 69
    0x44c860766052885101009054200059004280100c1d4090501140d60003884031070400703024085c4244e5018400c10400440c020000d48215656806080000380320403480c3c0c0c8070702803c040442226081280131501484035625090070b80307400c1e00840c0c0c200c40d110314003009103c0c00200800c2110401e45040160491f640c10950300e03030040129881ca0402448081202d5520900d4101401c4c90303210b00c0042d030800d0030f40d6000d04a030302c20001c811048803426001c2004024803e00079410342000d07a00b0103501c03180043c11080c003110501455140c6541d07280c1d5541405030592080e122640240226032a4030342c0ba0fa40458004900308401c9403144542110908100d0200001c0e40100e600d234840c05c3c20000c4180c00c40d8058004441c0c0031003d48114600403003048001c004150041080c0300c4e335035603101c600948460a00c807058002d00800602008100800c90070344101c3e014148090503401c103000484e00c00140600040d6601924a9080284010034806c055010300c0c05548201e040720350341001c1000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 745153884 1250 745152634 745152647
    0x6030204030f030e131a18010612020d0e060702060406050a0b0a06081f0b072f01140915120f1512010e030304081209030301030c0506161401050610 65
    0x1c2190340754400b02000640600c00752114250014001c4c5c00c0c50029010820840e110715410040d9410007101c1034146046c00e901c800102d814416441d00c03290704042c0c0203480d02c815441c081d16000d5001448041c070348031942c0180d10b15207041055400c0e81c20003a6000350355000645013541e01d6450440403c1070000030303100310501c40340c000d4001040750346492416511040010303d40c0c00d080401e24084554180440010400360141100654403038030641840184445500c083c00703c0e016007408034a84c05030305400c00c126042030920700480e046080e901c1d0070005029a80240c0d4019480701c00380c80c02c6c80d1040002c1c20184c1c1040403800201d5540343d001200b0118243c0b00d1402541c00700100243e81d003030440400521108200020070b01450741c1038075510f035500031142600c80f107002140c000046164405071a0b00b00191000444c115411a124250290480d00c40d10307201d41c500144d00c1c04000000d4030b03144081038000804005405144448901034081100ca41d489900b01c00c0e0030418407801100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 745155134 1250 745153884 745153889
    0x8010b010206070c140f0d03110306090f0717010e01060f020607080105090c040b040b09010305010518070c060b0319060c1d04090203030f0a031b0f080f0a0e0a050705090106030204 79
    0x28002c1486859910054a0304402d01d00191344c44104c0800a5004104c2000031508414080005084248508000901320b0380d03050f25542944004000f401941e5580500340f9401841440c900e100c00d884041068490040c9840650084010400001b0342d280e1400700e4141200c00c180c071000f40381c080801c0c08a031104022903804020a00d4034005100c0c9082044500394850030b928910b51429488140c440181d401641c00204154030018038800c0d135503814040d05004000603104840600c0c954600e0840409c002044c600400c480c2002c4031083c42007640102c03441c900090181d555030307040144401139030016010300351621402c043c800d180440c844d0b036610301036030f50340aa43d140c903103a08010000504000082a039143c0320900001031407811140c003e008107001a01e00003281204600358000c0c144501240c0c500344010070641d0a100f0760042e240f50741c40b130040d01c0c0800081c1d541140500c0100300031050304116101e400815020064000f0300c0074243d42d021903810b081c03607070f0300e9404800707034850303070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 745156384 1250 745155134 745155137
    0x90b010e0103031d0a08150a0e010e0d0e030715080402100e031902042d0f1103061002160b0c06060a0f0e0c0418060e130206032e0806010e0108010b01 66
    0x105410507001c001d413039120520010050001200966410781c20340f50403c1080d5003503981e1000020b00190841a10941880801e000002e20001800304401ca4541c154682480240407024001e6400e0766000d020000142008036084486040400c5000b0500501194228000e00ca26000d61000e14080d2000f0580d02d44002d0080a80055814080c4c004143e0030504076000b540b6064001da0303160190103a0700b190020000302c01c02003040001080142d1b045950f0300d2181621b00600c0000001007081140d601c00c0c02070303d2810300914914012464038007070a0322411311030304448020681e0448000181002030b1300d181251030390344503013041217002030061203030b1041c4100e2198104082c001e8101350584c000e0200106508296440c0b00917042400e284c1180301c942a55a8018404000800016034111f000075103496602400c07680415660b10016000350340441030301d54403840400201240c0e034080c0d0914128450086d665290040d0383c0c0c070080c020754080302c1c0301c080081650f620500c0340102c0501e05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 745157634 1250 745156384 745156397
    0x307060807080f161101060815041203060b12060609040c1d090f1f12120807020a0c0b090303160609060b0913110a1e05040b2205060d0f0501090b010e010303 69
    0x580d015180008000c5c40c00c0d1080d502d44c030300050300c41018854120024182d156002c0f4038070700b9141080100d11115090018146801024410b1040c000b098500c9228155040c000980781c0000207080d40c003402840c10381c41811701c038120300c10640c801c000f9240c99980f014601071060680c1c1c108080f10300101c880402d41030300e6074005105902c2000c480020526014110341050380c9408004800e0f5082d00400e41c1d49100750049140000d501c02112984034019201070f00240501da40da201c000d01c200d109070b00d5071040111b0030302581d0781d0034011070780000841006913403040e0180ca0618050320841e03e055a000f40f030207994620a061000c540c0d03116260340341c0d0f1903182864550b0345074101d0324504005904242e201c007004c60302c00d21007046030101c50480f4040401840c680010402607601005070b0794081d44800b0280102c4c4c0450840100ca00901d401c00800e10350758010100c0c41161309a440078003070b251880002024031070103501038907040b0b01030000680203a0b2a1001c500a4030000e00c40100003400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 745158884 1250 745157634 745157671
    0x40f09050a060f02041211030616052209140f0a0c12020a03090b090a35030a0908040b180409020904021e031f2712030b0307060807080f 60
    0xb0541c0640781d140107502006003465124944201c0820040c42d00300d03800310000c04114494035007080b41395400001c180a0444031811032900a00600130140f100c0c410602143d008049a584111814013801c4014802c000b0020b240740c1000030000192350304480000c040b00400c10390340c030030700410402684035100c8103162001074208400a40c09840d4000805aa8441c010000781c008146107004900c1d1784010280c1040d1405d1048217045160301c4505802d2503e8000f1100490200e229036400d200d8110302502c0703544d15014403018000001f0000c10542c800175002c00c0c80c00c5030b200941500c1c0202002c0f1440420720b40117000c115261880c02a41c0455001e002500618000c0b10200e0140b070507803940400d104098011030718010340b00c2c04230a00c500c0100102e488071515442920941080d50b548401c042e80312410510254480c41005009501c0d0140313074a58490103034110710000760300a401c9560859a900d80105100c40556148002460f02d001184074082c00c031410500690014212000c03009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 745160134 1250 745158884 745158893
    0x5030304060207051e1c03020628110c03070c0305060a110409052d010801110306210a0f0b0f0c0c07171501090501140a0b041401030204080a03020c040f09050a 70
    0x3503c0d040c03c2c03907401030b49520240381602c40a400614145045010103440781b09403502030f040c0b99004110160b540b80e50b08150a00000c06000d0000c0b90003014170000325212002078100e01e40c030410182c0c201602c00090300c2c0041003260b4000504070b030700030b0040d43c1203901c034034603840281c44210480d900440014801401450f01d203501803500444041042c10703048400c00c00300c8605460145900650780d00701001000490b0b028041c04044100124215185140610000b0241050405c004900702400c1044880192080001480407030b00a05060501009031811030004c1e10308941041d140c510303080210f44d080c0e0303040003503032241e9a14201806595017400088100d9a08002001c00588528413503101c03000d2000c11418060405490046800d40c10080418403410703880010074026028540c1c100165240740d8180c0d8240d44a0ba8030601d006503042c00120068003980e04070ac00f950042d40b41c40130815400041050014200fa1400e02c401c1881007000c41c110b41c00c442014000350810a00000040d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 745161384 1250 745160134 745160149
    0x110609034501031418102705150405070306140103050a021905040204031a06060306010c2a062f0c040203041703010b07140a1a07030e010f150503030406020705 70
    0x2034189000618580c100080c0030052400741d45030110810355410171000c800052240b03050f0840540380c140b01800000340c0445c00c00c01e80c2a50301f000c4040303500d0b521041020510085100e6a0911103100301c134102810980d444ea2100d22044401b50711f0135146d0070212000103c8241281d402c20003034802414103400748aa4280320083c103503a0105203240104159803244098406180110014200101244182c208014018000c94810321040c400c129040c1c1e4010403102c20a9170042001181c05040c0940c451001c6005000c41801000300c400854440d601050054602056800030402c400216000d0803180000c5006014141c100d1306040f60241459001180c001d13114002000b110703d018400b90f61950000c0e004540466000190f50051000f8111400e0050b08802d002e00041c00700c623691801c1d46e82701c41c40c0c40b15403040024005400c40380251300c00000215a0f4000780000392080d400c4c10000c052a5030340c90000c0000d058080b840742400404e560a03a5040c0e001441c00701d04010400114 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 745162634 1250 745161384 745161517
    0x20d0b040303110d09060612170706091211060708010b0a0e150f0a121125020d03020c1804050312090a050109030c02090a0507080403050a11060903 65
    0x1410b880f1800780d404052040000c1c8040784d603a10340095040076518241d030a680c070742d074001d1824244003e0300d100030500c101c83e154401518440f085030b0b100114034000000d4009450301500c0f100380314103402070a6402940e0402400030000940b900e940d10351405a80c214000e019071010781c40188210440e01c0d00403c054025440010000030700380e22205004406c13075001061100a480011414440d041d400521086000202c10020701c40c0c10060300c000340c600d000e001d02c00c5400e2640c148010740c210303007114403d00d001600a41084c680f5209818040c0d46c40744541d114901612906c45e4404030301810050481c0540c1d03000e0003039843c0005503821203540100c00b80120383c441c01070842400001e1024441c100c1e03094460f4417a03900342e100500400c0310149000b480c0404042c2010200900c40b64400740055201d40d060800c540c80f2911024201c401c4030515201c02c0540c440c21317092080900d0008090201c90040c0d450280c040141084810010183d081c40703030010314003292411032902121500c4148 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 745163884 1250 745162634 745162637
    0x10318050316171c150e040c09060621020708072109080c010c140319080f060103060e04170d06080105010e0c0a081503031c050709060302090d06240602160f03020d0b0403 75
    0x1442d039146c4040e05c1c500041500c00f11481b180b001002c010004542c02042c00522040c1442242c1c92040c80c810701c1500f500002c030241750b507070000d0a0010002c1c04030680d080c0c0c5030003007030b014022425a201040303c0200320a4440100351882d00c005460500014140350001c2c0613521102e0b030a64540d1134003090501500242e03003a0000380102100ca540741c907090340b140400b50348e1300503207800c00111442c0c02d044058401c030f0400d420417605003c00303411100d8254000368440e043d14000c4507200010303031441c090002c8400d40b440c104200041d04890540169060350000b40c0440c00c1074643c4040507074540300d01410b190104418600007100781010740308801070141c014040c2c81c82d08545011043c40b014100740c00281c0b6656860911041c142d0054240010342001d0508514245000c00001c00c0000d802c0c0e0000d05035a12900402c010158a4820500b03041486101c400c0041d2150006511a01c0a1140301d500300390500000491901140c000400c494029000301d049918507104c400401c42d00034015070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 745165134 1250 745163884 745163921
    0xc0a06120b030a1b090e0316030513080f0106030b01330311030a0501080d211808030103030917070608040b04060e0604030207180b0f010318050316171c 67
    0x38042003080b4139241c40702c0758824101c0840780c00d00c03d00d6400c69600003070070101e9901c10302c8401000f07488194000c28190305800c01c80c0c2c441d0700b64440806400101d4025030161b014035044142d0042e8150004410740380b00c3c011200c500da89842d282601c0268214040400c401d400700c1c5004c144018000c0c54003060b649150204100c0702d03440c40b59806500c10f803220f42d800341d511801002080e03c02c0c0696030f00c580207868030780d203a220f60030700c21a6900602480d0211140d030b600710016852040460f08804250f203c0c1015449617503904002d040c500c20b41c480c00b220186103004441d403401c8041811030648203d500c960b90b19032195101c001e00c2050040088400716520f0404c2c1e409030f0010405d0a1040f8800d038020002c090800c4291003508480884d08144642040c4003510b0075512041c60380c400300c200f07107070002e007101015141402000165070064003900000820316603c03c03040a003c400c103030142c520030030182c0265140764003c5c4611100070f25409426807010852030700507001040320301c81044241 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 745166384 1250 745165134 745165153
    0x9040e1006081e010b0a05040c020f100501050306063a0605040c0504110703080f0402041506081506120402090a020417250510050705120c0f0c0a06120b03 68
    0x1030100c500c250071880040c2e201c614840d81e04007100c800542c00c1d10040c070003800319599803004111215000d02071644113a40396203041041c0c2c0d108001100e00420101308847c446602e071041e000050100780580341c003074059134001581c0da0a01112540f8200424000040702012a84101c0c40036605407494400d03a00a100ba0080030610a018541c0210f0041e490303017586902e40420402200c1ca03020545514100501a60700401e4021240320780c000d0005928514a40c1d507840001c0081c000c114040c0403840318407101042c1294002c4580c0d2103800c1080380c0700c902c10307c01d400304241806941d14412615039207100080c0141031940c0c416030440300c00880903040130340350800e40003103c01d41d031002d0000750b00100040583e003207907807020f05004010012070318040c0c0c1050f01203043c9043d9020041c0601c10001864000c000c402c2003030704c0318400c0c003514481e00c907d5002c0200fa140c1880201c07011683c03055400d0752802c7d10741512100d046600c41c3d10341840310b0b90507801c043d0242c08007000f07035036060007005400d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 745167634 1250 745166384 745166413
    0x20c4606020f040b0f03071d0d2303071b050a0e241333060f0e041503060f0c0203220306090305070528020105070609020d0c140301020f09040e 63
    0x10700405000c0700d0006460340360860004215043c0300e9810340808c1004840307490b807610350f035502d03c010a410102c41c44201e0641c120304c4c01e54a1100c1c0303034020701d4030000640f01c0c03e12405a60240840c8444c04030310103981d03594000c1010f0003e00707000703c040004400e408515042d201005038642074111402054215191500266029074410200c20189072102d680d142c1002204504d50a140004c00c210740b014891043c0040031118180a03000600c00f050301d441075114081c00e070540142c40000c10a00010407184030003011036066100131103a990800700343c045050941d015140320400164001c6090244074040800f558001c01c070424100d80840f0300100110b48180030780c41c0385138041d84a0303d40e41c0c581c03031408500e000615851000b500e0070f20149003001d44c60000c02428026024038046840d83e00a0900c00020310301035400a60028103210044100144400d90700101c841100c400b842417850b40c0c0c01d0500343e1117014280c10944100b00030000c0e041c80c00b0760081d40d05000d114121441008205003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 745168884 1250 745167634 745167637
    0x915030d0206060a091802061b07090f050f070c03051e042d060c020103050411060c0105060f01090e0c0a0311030a0e1606080a0906020c4606020f040b 66
    0x12450060b00002c0030071201c1d0911401180090210302010089030605070003011070070300c0c0314500038030a500005188030240200000104203020820903945402c1c0e60b083d811000304021201142c41909200c001a50580041d00c03107841140c494a40d484001a50b5804032100d600c10601d40c3c18001d483e9100e00c5200c01070801810161000e1061080381031454040003030b0400207000a9030ada80001402408030b154131854801b00e4690a00300400c0588891901400b15003090001c10380000d0081a801c81811054220702e00803001a1a6901940300e40001141c0b0f82c0041d005444a405050010031200b02044000f0000102079281c00900c40c10400e01800203a4000d503128542c1c60384400f001141540140104103458406282c49846c183c9009c0c00034000030300080c010740700b07143d0300c4e24648240f150640456444660603410f031541440154001c8081d10705003101045088107980000d140b40420310701141d44050f001183c5c1c450340700e60b940c0707900107075000a851034080402400001401e900220 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 745170134 1250 745168884 745168903
    0x30d0c0207080f0102130918080c0307030e030706050702011b0b011e0e07210e070b121e040b0721020c060f07120c180305011508010e0c091503 63
    0x40c080d0458600d040001c52401c400e0003c04141039104201b00c80782c07429044451000c54049020101e072040100300a1014901012070103482d4000014111403000f8001c030050080038400c0c5c8699900b01400400d0550b905054003881d0085601044444003540c0514091480704c82d0416034821003c00d00c4d6218440c000d400e174040c03c41422103580066158500034815400f07411541e00401c828a04038400800c40101c40b0082418902146407194078040903400c000b503007441031800c44014642e0b0b02d98424082d80500030011050b0310680c007141d180d0850900c24181140d02800e403556035221074075400b05080c4054034540500001c0704910398108082e02c03585107008080900162181200484079080800092a0310281c0c6d072004100888030b0307008950341c48030f08680c030300004811081c1041500d04500b00998000c015509000000030454150000e000301070401880440c516070300c503500c2d03098426455503000701c4d4200b02141081c900780164002da0004505502a182d0079000c004641050b4412 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 745171384 1250 745170134 745170137
    0x10b10140903101b0e2407241103011203030b0a0e04030309140a0302070b032a04091b05031306180605090601060203040821211b0306060a030e030d0c 66
    0x1484e1095210542070f0310480b4201640c2403409284030f0600000d0b40c41001c51541c0306504045990756041d10345030320203903903009038084010b50b0101d000e64030f250f041d820004030640d842c50806440b01d000440d6041501c3c100c81900b0300900c1d805480e642c043c0c1c043d0183c3c1d5140d581180a0b04800503c400c0300d083ca80740581c2c004d4400095900e42800c00c0b1084540a4015008a902017110380d000260300280c08412140074032607594907a111005c2906081d01e08004108948820740400c001e6114801c0040c011a1010082003180380240301e10004000907104642020603000c0c0005240c40384100061500203124050010b85010096840f00e10a40080c100740d501a82d200204122014104041c5000d002903000843c10305242004003640c40003860200b0446082696103d0700d00c0d403103036056920690781c45806684482e1060342c80c0c5120403088403021204000c032105109400704040c116800798201500a500c0c0012076101940680040201800248008c2100002180c194403c1203144100da = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 745172634 1250 745171384 745171391
    0x90307090b0f0406180c0519022508100207030215010b0304120935031b0d0c080414010c0602190305090303060619050f070c17010b1014090310 63
    0x5550500c81c000d1441c01a05000b1403078440103000035a844030828415045c00c2c0340100d24550844011107603809032001c80c0c0030704020f1071880400c0c00d80201d10078560070103a81c02980c507600740c0c10780680100c41902c5480f0264201d1350701d4480319041c5030000d00c0c00f903000340120307119288620040d003001007003640920740c0c2503c08800d01040121124014581c0000351030951001d80c1400d6000480810004000000c2d5490603410082c451b807454030b164041d94088240c0b80c60f040c4040b0303441902005070605400304d000d144401c2c007105000d8600b0040c142c1d044116241044d05080800240080c404012b50500203280903540000b10710b80014000032079000c1109010302c062102c0603065942c00307880100950403c0c0b00700010341e22500103840a114080c00700c0c0403e800980d80070b4641e440b594170036540903000017540400340500d0030412400c54104982d642421200c1800c400e00b00c0f00d00d4403500d83e20504442d403902010384201140c04445d41054403440c81e0038050070000e481c01810007500c02d01c460300d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 745173884 1250 745172634 745172651
    0xf040209041a2d04020319060b0409060903091d0c21010801020406020706030b180c07051005060a151202090a0f030b060405010e010e01060f1b050c090a062909030709 73
    0xb034504207510289161880043e500345640003907100e02059502615a101c20324007101400301c5034102407050701015008210300c0016040000113003400000980124094440001d03e8001466145540e0446162441500d0f110100050b00a92016140041c3c081d42c05680d0265400c0501a590081040314001640c862801d06e000c0d0410050b41e105400b0b00d80b070b101c07820f0340d95120646201f01c03904910030351585590380e90a2400d868041d103403014110744541560b010550310f65920050140808681c0d03100500c0c3d03a180b0741d640c461175030080170001514104100010341d00513005030007281c0780188401d0b00710761100d4000258480940c000d60762500c0040901000e403c20344503440c013400e1003140c800901c3d1b0609d40814440340044c403804e010889000746805000c0e10968801000c0514001e03091004802c0c0d041241ea01e07e44144114420001d5501081140d15907110300000c031404140109444407010180810007a010f20048241001c10042c10740d80d030707034240322a6000c4e0a01c014001030120 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 745175134 1250 745173884 745173931
    0x20a111c021006050a09021e0703030510090b0303070f0606050d06050103060c080603030a120f110705060115120506030c10180b0715090f02130903080f0f040209041a 73
    0x2140c9031803002c0d90910f800380c20312040d2540c4002c44c06466500741c1c0907035292500c0c0049204030960104582070a031010480c5001c15525800203806007903ca035294003040d44400c8050201c400303400504d40c6c141d00030070252000a00c0201100380c2e403402404000b402c1507442000c244041108641201d002c1c3c0d03540014010012180b1420341c2c04000f0b0720b031044040c40c051000c04c1c0c1ea8070841c008002441681d0100701c1d0003800a41003400e890b0290b88061240a9440d1070014050300008011110780c01418008a00340704c0c03c928a804181461791949120412400c0f440e009140c040d090355010301941580e0b21040d1100c0c1c07188000c00e039a0340c1c0c80000c40101d0247c1001c102100707800071481d10400700a6000428120015070109500741c0c0c00c0000c801c0c84529140c1050806414001e4100c6080b00c0c0510b101c1615030312603500d040c02515050708981c1d42c2c844102c402e142c100c8020f14500a40700105025061440103c2d500503c9034203802d07813482070140210080003040b00c48580ba2490b0000012001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 745176384 1250 745175134 745175143
    0x90402210f150708010e25050705010e0606010801230909030a0f05070807170d11130e0f13031202040f181b0f17040f0605090f0709020a111c02 63
    0x1d140b44a00c241400400103002c2801880f50040c00180c801c007080414908041340075015944180044440d4841480034009800c400750a550651800e891a001c80d0400715616101d580165950501d5a0a03c96003103c4c0403601414100c0782e0038060040c02c119242c0e18031950055200c00c2c015510750316405001001100b20170360400c1040000e00540d000916518240c83c101944440c4072034400d070050b6038981141c01080b00c1035580b9402d101652480b0007041009000e0010a0405a014562904d025003d884010382d2881d407000940c000241241607203c401c521400e200c0d03e4800f4071003d4046015041c0d0700650000f0040408040c004c001c0e50900d0f03200c95103202600d13130301404011b012001210764200006000d0b0309101101032316204861107000e00c000300021079100d034a00c0e410709040c410850305043d030049895620304008115400310001d000b807052a008401094181c4c1000341000c065002600076030140008030041020441c4144580304010792034081c4400f1001d03d84a0003441c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 745177634 1250 745176384 745176403
    0x5040e1207260a17281407090f05040504050304030209090102030a0b181b13030309080d030e19060908030f04051209150c032107030e06070905090402210f 68
    0x841c0030000400b0a64000c500d840c041c100c5a01207100c980d83d44158408405111021000610140c05e10f411010b0640d03802113208010f202001c3e00b550752406001c0c1e400721001c3c01600d080d908285800c01103071400340c03c107941c410300c10400d03241090ba0300e50102c0d590060540d42c281c2c55035000301c200000c0f10100d1085c1d051904088900c00803452402307134102c49041c0041d01000c0201c5000c0502ea0078a1a81d4084541e042c54680da203108569a03803d00a012003982d000d00f2495004140440350511b1290040045100552001d031014503407461844039035801c1c100c401c03902c8a0700c0d003e480e40811619006140b180c240c03442001c00c6e0749400c2c9003c50810150307078015928003134103001441903521800c1d005102811840519940c031038907160740c5440d600a0480012601d6008501000b81006006905001c1ca003103407030074000c01c81030301440340d200e010898052000a140d5541000f246c90102c044d81d401c60300240500b408907802100e039240b001307400c00102c80507038400f07032840c1e40c0b501081000560 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 745178884 1250 745177634 745177703
    0xe09060c030109051008061f1502120c190b04021003140606091309032a03050a050304110a030606140f03151f1203090b1305040e1207 59
    0x2000d25142103045514003043c003420807099035030000500000c090010b5000a090f1900c03c440711b6280050a5541c0000050141f0088081c020000900581030304401c1805110903000352841106103881d40c0c0858020014007900c030710500804a501840710318901652078003507004004186894010300808080701103610080510305010b9050000c0c0c20030880e90004021111709543d450072000007151a141901c03400105440c01601c402055084401c00c1031000c0005024440070203154140308030240744542c0a000b0841c02c10140c3c000070310520045074001c1c442c800d0b64581034098400725003200040d420481d180b9549040500960640c404400c002c2ca10490b90b207540c00c5c5545001c02c2d101d4039100c030055120841c001c04110700001e03602d9058032601a400c0c0d18540e10751386042c940e81000601d401603004c03c2411102040c034028000c00c036400e5404024446500ea4a01414803004111300c0c91195058020400707210401110140140b24445c0500c0080302e40d0000072610301d5171030800044428 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 745180134 1250 745178884 745178893
    0xa0207090c110a023307020f090c120c0f07050609010f090203190f05161404180b040303061a1324031a120a1b06051b21040e09 56
    0x1080769100041c003e03403855054030160103404922100c00303064411207080c0749418501d0f032400346021501e1000f0f0801340b0300895840380c9161a60040c040c6044064642040c4e0800130000c0c0b0b5854905049403030340081c407030782d101854450031803a940840e82200300c04a806c0e4200c4800c0c00800340c0240510703901d14410b4401000740d400c203540080d5403004105081003d00c81c0306ca85c05000e0060030020107111a8002c405e0321009000c2140e40501381025014000d07102c00810707a80545418107128083c0003682094004003422119150b5035004900140202e00309502d034400031075003400c8000c80ba6070500d004a0065107681d003030941e002030f28265400014038800603118440c42071420703087e1015980140c1c00d000034141c0100b40441c4454480384c510b0741d04161011a15606504009503a0302d015000304000c80440701801c60768003151950344143c42c000360081c0300500150801e90794074000003034076408650042010003c070700740d008480580742400740400704003001501c03040e4031000e1780000080081c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 745181384 1250 745180134 745180157
    0x30601172815060c05101406040207150c0207051201050412110c040c0c060e0a03020709021b011a031c0219030c061d07050d0206030406050402150a0207090c 69
    0x51069108000101031080a000403460401e1003940c8a4000c1c0d11481d038915454940320301c07010345002c00070401158244a600c03070f0420f45107031510580d104548460340d01030860f1a1102004081d401c0280c043c0c0307040300c00380007401100301c503403045a0aa41203900581829442e0130304010044000c040000c916034180010040018054650034640440c03500340b80151000714400340d4030b0f00d80c480324180e4015140100300404550001c9a0b2440584206d4003030000100400c4415150420204001e025900211080c40781c0c0c1015000780442510503840814081c400005150a5507005042000840700d40d40001040d400c045c820401500e007440503000d9804801c000c000d51754002100c11022403d103400f550000c241c8901c1503100015000b1006218060500c0034188c0c1012900f002a012845009000101c90402c040c204036034580041009045540e030352603903009040e00800890b0b1103d038406040c104e96040302c02401191020398000d045490600f1480e804035800880090203020090901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 745182634 1250 745181384 745181401
    0xf060215010e070203120c03150f18061903060903032f09010c2310090302030d0509030c0607030f140105210f01060b1305060406120e0a021503060117 66
    0x3514119840c480c0710811075607075a80224214003c40c030100c121181004140f11010103450055801a0310624280114036814410450341304114155542c01412102d405a1201c100154007940010040d00f4510420440d170380803070a200554004031181590b5001c500241a41442130080d072604c903c0c0032001011400003505244c4c0c03e8100c14403540c03d0300242d00f4030140d11031441601c030168001c441c0c032507040624404025441d0240c5007000188944058058482e605000e540788858040e0065450000809840d002030301004040004600c401c1003940403034042045424401c06881d54001507007034003c0c0f448800c0d6147c0260090302c1c600303e00d0043c07000b607441d0618010940294159221500c4219850504019281303c425010707500c0c02d000098110900401030640306100014440c05c1074540c4c04000d001e01850103004002004070501c9890880390f54007280025a03d1011140502c0d65036001030003401400300001001c50022051100b1540c2104050720400d41d85113132a160351501456 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 745183884 1250 745182634 745182673
    0x30601090e120406080f09011118120a050d09050d0b130f021909060b0c120f0405031e060f061c02041103040602120718060509010e13060f0602 63
    0x3500c00041d51001c12440000c0200700e000b20b5440d0000c0710382d886a5a031640904440000c0343d4000d001c856000000d4000395040c46081d000a044884850500444001000001100300342c0990080b4050186a00c42c050410904130098401c80045c401131910301d03001850380c80c48ad4001e0f80202115806640002c500d18081540083d130082070b2060b40c461420318850114100300c0194012411041c1d213460010386014003820f54001c44400d004945e80d920a405040c482c0014190080c2c010020044000401c0b400501ca42c000101c0c816007032035194000281000b114003c240421441180070981682060060603800003071540180c840b40392103c081a0014030540303034001c449945425001c00c6566a900092580c00001000c036100d15043c0351a00c000d511840c2080380003540c50340002d412a1040600545038521442c2c0400789518105080d01d154000c03602580c1030207401000c1c41c5103900d40b4000a4a80c845011000c50400c2c5000d2a4a5020202d81c008000f103400491036950903080950 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 745185134 1250 745183884 745183889
    0xa0f1509051e060d051501020f06130f0507090c0503042a170304090905012c0a020910090504050a0c050616080a0c050604030f0e092701060924090b030601 68
    0x720000811082c50010f907041c4103e804a40103646020306011104400c030b421500707002c00c00e808950300c0d100032280c5641d641204503114500d5a10328801e0100042404000340758141c0b24000b200c507966103030340c1c0c81002d84465002c00800109d01000f0481031054900300c03043d40400181c00c0507181050f5081c001d40703c1c00c950113401e04500c1640c004109425080088900030100c0b41001c22913403080f89000d5020300ba5400f09034804820303a450909204030002684102843c1060043c08243c03126800c0c8500280c004004924a0301102000511040740b0301500c0c5c0320703500c550060800280b407498952444111074201e2400b5042c240945140b1000d28145500381f1038108000790b484d003591050880d1440450030005240e130150380d05010030141c1003015015640c0d803035210f54032040b151078140302603031008070f42d241450000603948540800c040180148941a0880085292612203401c0e04c10f495480350504860351100e014104192113441c01038019000181081c041185400d0000390f58070410b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 745186384 1250 745185134 745185169
    0x21030e0613020a0909053c100b0301060b1204021c0311060106051912020d1d120f0a030f090c08160e0402030c31050403030c020129010e0a0f150905 65
    0x120b007001d20b0595001d00310b0782c80140c01707d84078003c003950078500ca882c1c6c50001440243c090030708103400d01c5482c0601500043e520702c54146410318040f410004e04502c1d002e08160b8200d50422456000910080e407801c3e15640251250703104100c140b0311203454400141e005104100050100514a030030703a1007240310600341d0345848000042014400d10091085a901107201c61400d4191103503085440d02d4826104040c005480d45408071028413802440351412404980c102003203248401c034081e03031080445806200380041d04a805a132081c64200c01c1b6041500b00f42c0c00700c190358010300760552444001d04000c0884003101d017090743c0070941d1403c00c1c0b02030a108084603134418104401c49500c000f520007038140808200c08005085000a08081e40c06a002a082c20341c48010705005015502c0c0c0f0985050071082020300c2c201480810614003000380c0c0c10043d00300c01c600c0c0d0565880882c2d1020340712401c2d00c50001403800f89030031030740c002d400d02510610620b07030010007495a540386900544440d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 745187634 1250 745186384 745186423
    0x6010305061f0306170610061b060e0c13020d15031220072c060a0b09180f06040b030a05060703020d021b07080d0c21030e0613020a090905 61
    0x3491025405891142c00c040105c4801d17214074142c0307182c0050018082e2185c5c8011403481503d40d034003120007202c0031241503048455480001c0c001405540540c0d0120311040554804001c0d0000084c01205d11701c044101a40c0c007c6515084983c1900c0f54141d000203a1080003080c03031440e66034500300080081d8610030b02c83d0b546070104103500503e28041c20301c505a41590b402a0720740d032103400d80e1118140c5520180030404000207100b42d01c41d03003ca004a40003014500d80c5450300d0110381c19940315900c03683d0060301550110030b0340c2000c04822401600701c00003408640c5400428401205e428004282c1b003a40051400c0f00403441c007141d4031750800080c0c0f4000d640ea4084601c0b41003c2d1003108200946100035414103000703034401148032800d035481d440039038210000e018021160342c250b0720b0002d00740440c0280555400801350030402103102e194123001c03502ca6880528142080343c100c1d0840b10548810041d4411840c08000c04000352500b10030404c1142e0083e212a44da4a16982c51100c00810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 745188884 1250 745187634 745187689
    0x1409010509090f0a1a010e1e03010c0e030c0913150605220e0d09060e0f0d0b01181b0804020d02090a0c090504060b2b11070203060601030506 62
    0x118104444500d007020700002d03003508082100ea07803861800c988507041e203898818201c04501c070f20361200400442c142e445c841f0ba62812010002803c10030030800c000c03038250346945081c0791401e0103580d00c0183d0f175480380e13410380700b00c0e0003454100a030800000d0310504400c2c04014075940300c208020030789904100745420f151680c001030340040c0a990401c0360f0048060300b5242c4244200c00c050036824113442800c3c0141c1800c0d03114540d41ea403501c0503040204000c008240603c6210303e02030000380c1c2d0020108540c08410720701081c8580440e0206892620010005000303c020a9140c01c101c50740d4020100f104070280c01000011602c803541280400c08001301103404d66940350312013281c0c1a00203101070100c0c107006442c0e030003c003040d81409021800700400000c0c41d2800380304050441c0c9200145503c0c103860700910898a1032071059448a90117040003180411400b4410074a120307003075000701641c80d541401050300e0304000a0140f0704160415081120584980085001541a007000c0803000e05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 745190134 1250 745188884 745188887
    0x6060e03161d0c0c1005071206050307090e010605060f0c280b1815010504060608060907140403120e010e1215090102070206120106170403080c090f0d0605070e040903140901 76
    0x1c01c13410040050302c40c00c0d07000020020582e1100c0d00640540e100da42c0d8140b2002c45100a4070454898941d16401441081001601030b400450140c0b0415000140440d1901c0010741c15800c60004040c0c501d0000c103813002104002c000148644c0b20008169220b80302c000d001c0c203424041c4c203400400c001000404507003410482d03402042c4a00284080e202000c41048510021410034855913105500b00240095401d0254080c03500520014020440759a2140d106403161a0600e1811802c070b02c0400c00000410400c181c00c0100e220280d1394040600381c0080010084104040340c00c0c0701798080b12418240742c00000d120300924940884880c41940d030f42e00703071900900071128060342040002400156801140d01c401c1c0c140d40158840c0c085030404440b42c60720065013120000c0110701072001082002d079004010301541c91008103050640348404002c1503144001410860b24a41c481c810b000d4213a41000300d195010340141c0c0c0030030003d0501c0e140180300c1850741711b080d07512400005031003d1a9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 745191384 1250 745190134 745190137
    0x10b0a030207081b1009032a0c0b0d06090501050d030c030201021303080306090901020304020a06230406030b0a1502151803040e1b0901080c03070c0606060e03161d0c 73
    0x941d0072a40140d10303098020300941440b01d1050b0b9000c3d403170050001c0911075048a20a000c41c803900340c5d441c01905032168500c110711100314001c0341104888aa00140020403060742003002e04a4210702d50307224203080b15500d0a480b402d4002c07036903003800c280061215403602c5028441c459050f2070900c030141d00e54203007a40244078071201d090004040c1d41c6d001c41807100d008029801141d00352000c0215640d4000f11031300300e01060b50002c2d03200d0070021b010080540f050036a24100d814840790f117030b81804018007456160f0f02552181d00441e0700d481440c0d81502d000815000144040d483c028500601c410000391144200300303901c40565a02c030003007621540c6c001c0c0d10601e251401c2003140e40d10b58031411300e030040550481e80000880801c81e1b48000f850b5030030055038080036040c0c55012a586a401d4054910340000f441c24040201e0790a240020800034084c0c04014070403a2110128840c03c0f40a0504004a64615428141d8440410402501d4083c0189026160010074040d19196003904c0e1049 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 745192634 1250 745191384 745191397
    0x9050c090126150f0f0f0904110913050c010906121e0f05040215040b040e130204090b01081905190804120803061804200a0302180726010b0a0302 64
    0x5070100b0030200008103650300d1030b010110310100c541c040c20b01c80080c10440a41e9003080c20503082400114010610b00705001ca003600607101d41c1e49103441c08038080201e5031800049945400d0380d400700e00e5038010700c0024800b03061054428a04803050604149001d004140e41b803020480d80740d070341c4800c41c488428030420800002c009842c01c5c4060000d02c4214030181406a07001e0b44180b0201c0b41008206205c40119801c40e019080b00350f04140c64050b411008a00003841142d0300075010040800580e52481900c943e45d1041000109950410080f585444040c002e070301c092802e03203402c44e004030b0000a40700481e0441c401d1320b0308454600e86440344885c0500d9028185001700c10303508400308602c4a01440c850142a11804840d2200c1555014050301c2514007810080403180e5201c001c5081c05689104200f000d41a480c001e5600e030b01250340a070340d036007041f070701d1a4a081c02e00400c0380d48201c090100000224981843c40c404030207100e01c3c8281032003960082000002e10948041c000d8041e02c0300d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 745193884 1250 745192634 745192697
    0x507023304081506030616080615070b0712021602240307020304090c03020909152407051506100c030210050a1d030a02150c0c1f0609050c0901 63
    0x122642e079081003598a4011081802e540c420003000555107040001c1c24034407400201544640f41a8089400d41e496403010f00303075640083c031590000c81508103610080481920825100c1d0301807410240050000240c1150003507000e0040041000d0368404810021920b501143c4130a1404840c0e49500a80d11400148004070600801008003035900031000d40100d5004c0b0034280100c80181104904a12131854015030141d07803138020900780c480b04404000010805441400540c00030b0101d99004200101c020702c0030740b4001804e200b0404e0030b0081c0d031800700c1c101040c0e4280342008400145e07001500041e0301e040026445822041c103208010840e890a00c0a80800181c182000781c1800b80001641c2c90362014040c90702c840701160b0001c2200c2da1605a036020f04a09640442d06159100d0080d0880120340d4062001050ba5401844071040101912079225852030303c592b000416100d8a81c04900300901d01010030a08044a008995501e5001d1908400d60b101089a0112003601c860034000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 745195134 1250 745193884 745193887
    0x60702121803100c0c060e12030a021b03040b1309051510052505060f090c01050c01060b030108061902090f0f0409120819110f09060c06042105070233 66
    0x85025000a4900c0341c5d14001e03503062021003441c0840f0f59545401280c00d5480090400001d50b08040f13542c05001c1c441074910f201403040354404130543c81c40c2c1040e0803680030202c000031261010040114120001d00c0340d0041800780349001d800b00741c5580b001c8040a40141007a4110200407482407040320805145a01005a085040d89514840080c0384408580620440d004202041c2100c00128031501c228401007401503404c80044900d90459000390381c80b592181e4000c2103000484002e07601030f00308040204003602e030043e036190394202030725a030100003441004040002d8550b048600320f640700c2500d0b445125900003010900038850420003a01182d2414000c070030490303001c40b00c40c0c015600c141280d4408420b21f08000d0450300118810031240c3c1042100142c8400c02801a00e490800101110700b000700300c0c1d82035818250215812140e4103c401d82013010300300d0402d004404d0840340d24107103050100c10781c0850203140c4191511005208010600c40c4881c084462031414a220000e000c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 745196384 1250 745195134 745195151
    0xc0906030c050d020f0f0105071713061e03051e04110108150d02100201090b010b0913060320040b03030403110f030a17070515040f0506070212180310 66
    0x4010045404201d404821804000030b1515040b00034084198004181c0d403c40c3c503a50080064084076500260306002d401d105060100741680c90100b010501035281f02c0ea80c900150100700c0c044120b402c04424800011030301d0000c04140c0c4080d00f040c15003400d00040c01d44600300c241200003402d9401400d03150080c810002004400145034104a200fa00c44040c83e0702c0f90144448000c082030f070900d13084159180030300c01529010781010034a0100e0b000004035083d8039190f403100201c00f40c00079691940000b8580505040940392001540c040d0901000118150781d0f590300610312000c580e1103081103c84000100f941c03a5071103c1e00c40310000b01240e969580d20701c0c29132415200b400205108012078542424142404552059190340c019804012110b549202e002c0c2c5401409080d01c03607201c2d41e09447c240e00c10388010f007030041d4068600485005018a851460000018419001c642203145400c404d009814281d5000e90343d45448107014a01d01070129141000220005881504007601c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 745197634 1250 745196384 745196399
    0x170a0902130b010e0a140d1e050d020c01050f09060304060b060c01150e01081f0603020405101707061b0f05010203040308061005070218130f210810060804030c0c 71
    0x2414002c1c030a89500010804581c01c20058200d01c3c410340e881c994150b4a590034034a0f2800b071030402244180308a004002c0841c280403d045241c540441d60b6500680d10300111a0b0100a1080105002d02e8441c1c5003028a64207694a409a95140b030300400e07010001c141040855000001070520280c0f030103468003543d50086018002140002c00035010816021075400c0440c04014180e5003644014010f0b0502c07078840b18890b100340c0050f84d81c29940c1e5000070005030340318002c07540600c05902540d0b81041c00c001d01846c1e03807001309600c40314a0344002c030704000f4150400e90b80c03814911421000d001880c0d040c1080d450340d0240c0403009116501c008104420150428040c40c020b140c2500c0d40c14208000c1003090302d983c450f640d006540600344491072841102c000941c164040c000c103181029101c103a41d00c002484158840441700c0c440ca01c5602e5009400f44400740c030102c0898a00f000841c204260500c0f2000e800380610700c10410340c00c0001c0c0c1494068484000c1c820f501c41a0b500c030165a5815 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 745198884 1250 745197634 745197641
    0x17090411091002030708162105040911071101050309160801020a020d0c05120d0b120c0f0d0c0e041703070e031501030b0f04050c030111090906090106170a090213 71
    0x1c1c41482003146200c00300030b09100200762010310350712a00403403511000b210130007221442e1580481d010761744026007624907100050401c1d02c05c03010b03841c0d40c0c0c1c40da41490b002c0c0c406d8410711103050b403180328140100c1c00860907202d0300c40078550007802c2040e0b682e103c0c5c00c0c2c0142010321402039240105503d0100040383c010540c01041080c00a500b0703181d12003c851801c65003144c01c1d90010342254071040c660754440000310f0017801c0c0c0c0b64442d072000880f21040c0b4082140145604030071340240d00402034010841c10890229803c081c001c0710b66180700d40c0c55070f039581d000425074003880c5c1c00c0903203480000341048040d514900c42068505802c60300c0703181004009029000034040c1900900403032aa03081a14a0010002d0580780d2006419090741c0e00c0001c4c044000340002c02c00d0301c05101e404000106501d0a1281c00350203081c61650030303941e07034044050013600715001d40107900035011070b001000303490707840034211840c4050401e8640c1c01d5104c80310400068440d00601035404000b011080c03540f68210350 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 745200134 1250 745198884 745198897
    0x6130203011104290c031c060e0403030507350903041a0c0708190204090507090f062102030c060c010e0d0908010b040603030909091509080705071e0317090411 70
    0x10040d2002402d1139044030482c050741a03840780a50050040300307101c1c14030701d54400310003e00700800210140e99040f50060410180e1b415004a81d441061000301907000000c07283c942110b84100061403804a06401c558020b031034050318440701080072801020007803088400030300c0004803032054898000e070406003030750000404000c0c501c00d070300000400b0703400807492113a080c2c840036050035030544640900018125000c2c00316041e02900d800845c0f282c405104054036041100c0000402c641441c803a00880113105140c1c1e40041a582c0d804001642c0014190b01c1d081c8007079400701c1d125002c001c09140900529201c0c40b542e40030700c0f0b00980940f58401c029000b1111184000e100e038801c100180000c0b03886a0001600040e4201c005102c07c4100360400114244540d204140d141400d10000048991580c07044800a10004e4a00203101c0d04014480191010050002d1140386596201c01d0048071448010304d0354078071050300c00b5515218815100409400351090012000c50130313420030540d00c40c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 745201384 1250 745200134 745200179
    0x141b0607030209100809061b0d1e06170d050f070b07051201060c11011115041b060801240e03010c0c06150b0318011d0d03060b030906130203011104 65
    0x140c0001c04e0300f4803802c0c03854085c05400d00603207429107405401d0024201d612040c2c0319030300400c001e10308a200780da2191520803900c8030382d0300119000c010700c5082501c050341d2016081c40c454410401c0c3d0702c000401c554040c0b507000c0c00c00326641c6081d1020f5565500465030041c14014064080040080d000001041c10305080141940c003680c80d43c0f000c0d90302d170120581c050048100b404045c603d95008200c8541e0401d105012900c411301014907502c0c07103038001c8804a48429241982c00e01c540f2403011180c01030300303050403c5501503042c004000c01c0c0d0000c0d01c0c160705410b01104d040410990082c9810024404060002d1114401d020700c0648880b011000855010380f4255440c0d17100840e8200c004140e41100409524640b40c0d16000703c00340d417030803c0070041b556a8007245131074180c00704501c2d40c8111000000c0c0503299071600b8017408640d020341c040c0c840c18004204002c031a14000c40c01941c090960b003200109108180003203801480540349042a5610002d000316115901042d20086450720 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 745202634 1250 745201384 745201399
    0x6080f061902070807030807050c01111e09010225260f0309130b03120301060807081f030803090a020a0f05040f0b1809030c060106030615020d141b0607030209 70
    0x14a41c07040c00300e2007541c001400004007440000c0000307120790303d000c0e041606031400d10700380b1801c919600e084415081c9a402100300000b0800074485035241c12000310100a41c0035030030302c2101d400107519000d40c8004c0c40d00420b0a802c109846e04621035151707014101e144011050f6084034034209236140f048010503000da10801d01e00ca422041c0020850b15004e001a00f080301307540c0d288183c08080c0c82d03402c206941c18000e4540c07030200007201c400514000c04080d5101d5546091038500078100041c054002c140038003260b6101c40200e000600b0100850342e200c4141c940c0c83e0386659085050511404000754042e442d01d10000f5004080402001580e00c02c8804010185102c1c03044411948142c001d07542001e000c1ca030f01003c61a0741480301c0c2d4460080c070281c3e4905120050f0403401c00000f6001400420756a900c02d004098031842c0e8580d03210001d00050411141400001d440c40f880802da00c0e00742d04001070310342c95042d48480c50341c1e9000d0a0f1401c031081802d2115015010750040e14550f40103004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 745203884 1250 745202634 745202671
    0x80702070323190c051203040b03070203190f093c1401020a0c0b0306060d0f0f0c0e03150c130305030d1116031223070908032b06080f06 60
    0xb40c1e90200c44031a072010b512900d035403a0205001c1050035003101486c00b0b010034040020040030350002103105200940c0075595600c21103035000400c01e80049004100071241040d4080c294114000c10103440c10403041d028084030210344c0004441d29141c00f16581a05c131115042079100c1e01e0001000c1c0d84015400b03000c620303504401260340c0c0c001c0c444090101c000c0510100000c44601c00255004800903000a20f00b00b9a0001d1000360b4050003c0c2d014465512a02c46507411128466441020094031304028a140440300096445055a5010302180d415001150a1b080720508451700510030044031040d9907a6400c01c0c646940221050610346070402072410115010402100c02c050544110003010003019142110802140300014440903a00c01e031070080a0300180086c0e060b81042010b1046500d881d201c004c1c10524140c3c071000b120f5105201082c2c0034017030046080309401105600021800c1c125414001074004e41d030200c4408d00915a903541030351004a00d4521840556242030200036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 745205134 1250 745203884 745203913
    0x1d060703051e0606090109050904030c02100504030f021e0307081c03090317070c0c080a0201020d111b190b04061107030b01140f090720010501060906080702070323 72
    0x184901d4400948010b10000940c06140c40c0c4040c281110341807500205260b1074030042003540f401aa01a00402d0350786080c80210701c1d01152007185a82e007842c0081c145032031a541c400d103000024000a215400c61181503030401201c0405d01605000200ac54692550300c13885541c44070004401c08001050078400958101c1c0213008003400503900d5560a21010f11141c4800001709000d001c000402c005a505800071a000103c600064078010300500144022031001a02d400d075402c480005000b245410200f00301000309984006001e4012900c001d80c000754001240646020403454002c41e0000000c917580340c00f0b01c040e0090b00d5144d03c400750752180034009103960b9403a0b481700820311500740005229000b0140101c4001903005842000c4440c3c04600143c000941201c01c4000908245010705a00c8190360015420b50038450003081a0350400c500240303244030a0040e0b40a1000d0000415005842007204e5001150401208000009182009401e8041d203030407040c80c900c0f5036031a100480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 745206384 1250 745205134 745205161
    0x60a020a081b0a05030a1e0b1201050f0112020d12030b090702060c031801150305010e0d09030b15060c01061e17060a05070216080304451d06070305 65
    0x1602d10a5014101030b0074541c03c03144c2c0c0d800141542d94090300e4800428a884454070381e642c40884040001c0740c0000903100344092206d00510f003680d00e1b8140800d02001140118910b8159100021120008581400401d16401211400030244a0322052101c1d056034154130100f01c1102c1190700455a80315a40100d994030010b072001c0e112540c0230030100e840b4003c2641b522806035820800425051842c000c0c41c2c9881005500556651351030b00b0b81d040401c0c6060103000210381050404450850841e11000d0000344c00810518170904040c0104401d9503901040d0741045020a00911042c2c5d181d03010810480f040320058204401d1924003c212030141c06c40403007404840800802159583c14204800791030b01801c01010b500600c0350000c0d4031010a0b5001c000303407007041d0086986d00d00d00385484440410500000c04c941c45203218000d40d907031841420120780b1804400700802007070120b5400c00203001c03158210910000001752449990b4012540c0c510600d01e64a0400c00c5039181424002d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 745207634 1250 745206384 745206421
    0x90506060304080d1512120e041a0607051516030c030e060403030b0a080f0f0c0607150903140a0e03010b0405070e01180e01081c0f090323060a020a08 66
    0xf03848040c00310210700e035000c0d07000c60b03213004e0b10a20700044c441d500c44c81811219842ca00603140303200d448501000840d00107501c030300230030000d9404005007583c60600c145e2200481d16070711f1240100060240a2290400801c4c1c1c41c850300c3c01c103035119424910320294a1104988048004ca4249002980300c54040d00c10000e603060184050141580e413507808800511345600c14aa110640301c0011580034010059454030540107401407040b1000056900c3c5458940c04500e48220b03010840000015610044404590700710000810199120701d019a15000e14860b42d00300310740041641044e181d0b03c02400ac005c06010703002000b1005110040c002502c404584150105840001c0196194410508100c4001c002403800c003040d030b15602c111928820a80c84030185600808003003001030800a030108801c2d809003821074902004a001401301d0845101c05441082c07102a0070040090104074100f100183d8400e9503414038050034140001d402c1814040001844a0000340204402c8072070b6032030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 745208884 1250 745207634 745207643
    0x110d0b01050717070212011509050108120a1d06070f060b09060a050f060d020406020616021b090405030909010b030106030b0a050d110a030615240c03050903030c1204090506060304 79
    0x210403c100d09500301030380c0034000403604a000780203043c0d20319000784120024111850a84130750b95140541c2203043d0f40068010503410307004103111044007031a44080354024dc1c2075042c02039a890754040f5aa1102000c84c0d0708a81112000508100304080e0714a10681d40c2d00c0b40c01d04208228a4030140714030040100c400030b0300508000002d2015140c902c4540c055031900405a41c500207103854000c05a80056111602603804101480305000c1c159048d110b003ca8584000c00c0340034585181c5c01a040d4410500e41d02600d90b2002040c01d02c8024070854000c1c0704050710541d1b1a594403001d90045600910542000900c0c0403040da03d545000c003826000c031070000341440d42801654681307101c01002e800700513500c041c10540000c0080daa60103103a043e104028442031079a0f1034103140014100d2201c0900e801c40016142d18070940b80c00285c2000c400340c25150107925000818042071451080c0c1001207054820307100d03460b8410113010300400645408403c188816200c420601907c3d00080e64000d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 745210134 1250 745208884 745208903
    0x19060e031905160f06050f1b09010e120a110103060f14040b010e090106080103030e0105071e051f05040c12050d080901091205070b0708090a03051804110d0b010507 72
    0x740c0d071a22480c09485290403a40748004515038030798030700c0c04613464030b041142d03416101c10030061070940110710b482c2e01c4800f4114000c4007a4141060100307034464808250f040c0803e15400f1695920344110321180f40e05010300700e0350301c030700281004180d2148001b01280001e00f003642c003044503644102d40c60101e80c1080b4110400600308010840604048100c40d0304209600040d0320980d601d08514900800464940000c02d50550400410340810301d00c085047c4801006410009081a04d2140401c408410362294160842c0b5116040800c3c1c4690a08020000f0000d21142c00059100030300440c070500d00992000d070b50f404031071480c2d40c600c1800b03080d40d0009101d03048032600580c1003a6020481400001b80c0e210701c0d0f920b0880b540408d0184000099000c2094001c00001c8a20280c0100c03d500b0101151324100f40756907a00c0840710300040400c00081141c9010032120030b89002050710081042c40203203645021104180c01200c400c03110395043c030b4012403a80d40284102c0f411a504980c40b403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 745211384 1250 745210134 745210177
    0x507090530030a0c062f0d050112120309020f1306080618031605030d060b0912010b0603190902030f150f07020601120302150103111207080d08040c0819060e03 70
    0xa0300a051035000d102e04140c41c102612921240c0c00003101c40041001b00301c0c0d88541660220f036080768416081482814100d11a58022420200107404292030603c0c020807207240300d20218452000d425025504052038401300e000c1c003a22030300402c0607981ca2504481e0f256032050f03d84942150241804c28964008200300051800034505460340c0311b0155048034a0721b48910000e204891603540900c807000008601c2000394a098050303a800100450001e100c0300c80c03071700c002808038800035140c4c00e07061010180b42401544c02d81c102d0300d011034001f0190340050f0f14450503da114005d070b51221074400c41410000e0b0011000501c2c00c0e000c0c202c550700802981c0e082c4043d40d00002d4071404140c0039407080403622562451020400e0307010b148600307605640810b0318014803440f4981c0301e0903040f981e000750005001104d0001101c1200d14150301d080e86850300c0350b0515802074900750b0015076250051169400218288540d83c0c6083d038401e01d01000310084034071305c1c992280982e04c0004d40444039091207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 745212634 1250 745211384 745211393
    0x1b03030b0604030c0305060f070f020c04020915040308041d0906060904022d12010b0117100b0d020901021009020f1201180f02120106060804060507090530030a0c 71
    0x9458184030203042a4035103522a2143c02d102d0076540c0c02111180c0c809020001c00c0c42c0200c0903d604a9a5410490303110421008065114903451808034007907903020170005403694541c16400c4061008040301680c480e01c0c0d080180d090f034040e010384180304414030f00d200120b004200701513200d000620080c0102d40c83d0360040246649002d0300582e4030081403000381c12842e6411101501042c90800c40854200c568800c3c45405150184904400c1e458505101c259981003808070303c4030803840d000d0804580e600c0484811040e4a17400c00c607200c00c0c0c04582d0901e4400554010302d0f40c0d4000741c08440e40c101c20b105105054a0b05843c000350070810f0902141c0d41d609040042c00e40c2d5000120021500d040721400c00c10890b0a0800180c0d60f000c0360b80c1554055042180000c40b8418144c402800040c0c1400009407801901900082507603990b0400240101c1c451031a20024080051440c2d445030004040b00741c8001c2d101c1c900060b01c0b03115251010101d200041140c1d11030040c0e840e54404402103484 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 745213884 1250 745212634 745212641
    0x203120304210e0901080304060f030f0f020c0d080a0b1807091e05010311030f01260601090605040513020108130203010b06040305160b0a020c060a0302070c0f14011b0303 75
    0x49480d5890503030140080b51000382c0301c200e69107407075032066100d10141d420010b400300306a020508a800800090040c15401483c03031a42c85014280806e0902c0c4804d0b88400030606081525502c2d44007141184040c00c02080d6008140c81c5d950781c1702c41c80c1e2559803100f0111524014860b900009640350707a44001d41c215496a80540c40341003c41c400340d5141c0211020724444000f07281c10213080c4009100960b0036128070f241011003011802d056141245003190108818018072104440341c5c1c68100c03558102a94030b05514094106884e03055a40d001844040c090382c0c0a564800c40c04c0c000081c1d0260b40c2e602070900d805405a440c2443c50300c0c4d14010070b152081c413010507600341d521203201c072200c0d888840091005501c42d1004003407007544a2200d030140e0780c03a42c0040c1d00b084000c02ca04001c085c2d002466582c1030707100b00d6109684ae106068140c0c024810700000404c201c41103200004c1c92507101c18100d040340c8040c101006e40c202c04400450b2410840340e0540040c0b0302c140781650200b48030f90f2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 745215134 1250 745213884 745213891
    0x7090b1c051503391e0307150201060306230f0c04030203060f1602060c0904110d150311030d140a0207120b04050118081c0f06030308090c0d02031203 66
    0x30240701c04002d00d040428140200c0480031015144550800440300c050109580e03000301c00e1240c0910f507000305400140100300716082c414140c40b02c5018940e903a9a091100c240107006a19010303444041d1003001901a2401e8401030f2344d403a14001c1c4104840e0480816103c05481d014a483c40603560002003441504c030107030211240341c40078030010005803402c1020500400c400841001189800b010101030742d000d0718520021504080148105001c0301000d5400400c0300301c43c04a000c601d1405e0200c0503020f000d11440c1e50310b0820301e0a41003100301c84948820b4900880c80700649641c0c16050555680201c0d890a000624146401081460300c002401e030000b0304e80306945030035a03920000407145c481c00a0945da141e4180042c4010003500f407140191352240002d602e80c000445413a035110a008aa0451000d81d87e0780300c450354034441030b03071150303010b004c080300c0070003050b500ca0400038a01c4104503000c0daa85e103d1203800400c1890500c031a008150ba0080040803134444000be04035007504040e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 745216384 1250 745215134 745215151
    0x4030803161209032a08040b2104080d110c07180e0303071e1409100201090c06170109020405032503020a0b03160825050706020a050307090b1c05 64
    0xc0000b950203901640c0e0881d8000c2e075843d140513004940d01d00548020204426421000402c0e0000041c2410141c8040700e90349070007135851782c40039014070490041020001d131a1003444c104001c200f14030180584200140000204000744100f4034441d182d00c0f40543c07002d4190b20440c8100804002d8000e0b41030855913007000030510000c034502182ca56007007070700c03058003103407000c041c070214120740d50000717260b00c20240b602022a403007104014600e880790070941c40c041c420400d45865030074000d4202c240201e6015103200b0b95159240310051a14480303841030641403001500004100e00b081c000c1d6000e4130303401005401c0e0000300e0b1482144005407201c1a4405107421a400000350765070360542c00080c0042082d0320380d6480c00f0b01c2c425640414a005800600011400380300f41c000781c00528a2203c180c03144e00c9000310400079426112409008802030146000295882e205948140a540103681035201c2802c615120708880990307002c1c9002203407081218a441ea610140190049500240d61 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 745217634 1250 745216384 745216397
    0x60c020a0507260d0306061205060a0e04061506120c0810091e0e010204050a05031912051e0c060906041703070c050f071419030828090305120403080316 67
    0x98034116411303d0101c42034040800e595440820205400100c600f04401041e8010085480d00300001211140503018420040e02401c00080401c601c3d5402140300240e507070b04003401c456591500a00c410390101100a07804c2c20114000c01d002e004010003400350800301d51340405c1d035003042c5000c0d00034400c80320721001e0782c03828003861440c0911510950040c0515500003596582c24a82031141d080724540c40140250f0002000c0030300002c0b1350718035080050f84001002d42891080c68201c0d21070041d4000c1e070103101042c8844240e401c8001004040d402805015250079541e4450014bc5601c001c503005004000c42c044080191481007000395030006440c1400c1e40b02041d02c1e10713070a02c0c0c0601903001100552040109000c048805038074582c503103404448035074440d01e0301e11350701580ca10544001410810081001c003069072448401100070382d03122440419050083e400201111401d2109840502411400140580c4058100d13002e40340c020809904d10b440d0000029841d0f202c2c4e49801003040320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 745218884 1250 745217634 745217699
    0x606090b0705190309031a09061b090a0e0a060b0408300d0c080903041511030721080105010513051e03240a1404150e0a0f060c020a0507 60
    0x42d10f106a00d18000e03912034400034214a001d448000002d041021580103201c10013186090014410f40c0c02810064036054880b10010200060300840300826403040341ca201c041020700141442c80c1c42441d014400b40300044c1d5664500d002031080e030140c40e5468101101c0c440e108800380c1024091002c035040c6c80c50340d203600039460180540101c1800c0c01039584407100345107990761002c070483e0000d01002c043d600d0711740380246800d203180340c0c40e0071101403207041140c4480e58441030040d989043d4002a12988081100490010070890400880c01081c0a00008500d075441003090b162940c045030000492607061904000340e40ba0740d0080b6103001b01460040c1c407802d8a00784801c02c0501043d9041c5801c4050007c3d5031341e0b524600600039407501d45819010000308901aa09540094001d070b082c52800305c2070400303400642008039002c0203074410700c4040b004200841801c8144240516010001007a80712400c903228044404054115485100c0c1809104004d900107401801c500b1030000e070030f01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 745220134 1250 745218884 745218913
    0x2030d111906020a02010e0d020c040c0201060803070501090209100308090f060c0a080c0d0e1f090f060207050901060516140a06050a0e0601060c1a130b09060103030306090606090b0705 81
    0x1031000c07021a48a50046580c01c0c0e2030360240207030300000c140d4402820300310004c200001d550380000482ca6105a031a240000e080034005e500500c050850b100c1a25619007850403d42d002e8446002c00300d0207003490000003412050218002825170b544a0b607007914040d481020480c83c00210448a0351160040040f401d00081c1000003881c11271040f0000d07929007016503d028103103180212081e05010703040c1c0d4401b1160743d030804950004c1182e071241d91280c0c1200c0d84c003102c0680c103a0b0001c0301100954140450015000151101141d00403100400d190380c80d20421036481c000c040000b8283e504c03041d42d00340068110808119a00308060480b44042c005484620a4400598115400980e00c44500b2401c040900c050390140c11705040080c103010040c0c1d62044ca01080c81c44004a60080f00b000c038181c1460900702c0b1000c2c542011580c802c0b0b0500a44031170b154002880204d000c2481c190b07001071002100e01402c4c0c101c40c22500c5440d080341c41c114444207544e01c0003000b280d0714004c44c42c81503040f8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 745221384 1250 745220134 745220173
    0x30103060c141c0b0d0f080309070503152203020a030804020f0607060204030204050915010e06010e13380f1c050f0c19050f0307031502220302030d11 66
    0xc400e001120343ca0791800e05856003150600003004c0c1c018034040b0ba1810215100c050355003080c030341c170040890340d03030b43c1d0210076034107111541e004954580944200c0001600281082c0b9001c0c4d028140c442c00343c0c501061a0080031501040005c015030000d00880020a000d01d10042e4400e002610741c1d900403a9030000140b10380c1c40007608889456001c9424029414180f00360b9500c40101001040c010358030740320100c0300100503c01c91398141c61400000303a04da407207843c031f0881110000e0320020f0600000c01c4040701500e00614100d0b40006c0da0100d000054014043c00d5009200080d541c400080820341444042c0c10744c0c1000c1c50b004904009078a2011002c040c9401c5410b0068000c0c2c120b0035448000c1c1070404808101d05440b0780038489058140d10710b1611040f00b118030403240180c6540005010a042c01207561016041d0340140c00c1510004000b50003d0000d01e80c0303a01c2030004042e030360311441c001c00707040d00010350560303c407180f504180303800350001c0000e20880c0802c845070703080d0000420b00740c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 745222634 1250 745221384 745221397
    0x303140c0a090806060919020708130302030105130b150d39030b0a090317070201150602011505040506030a200a0905060d0b190504080a090605030c030103060c14 71
    0x4003140090000c005642c041c070a00041c0045002410b164284180000d09481b00075000314500d180340305131020341e00c3c0d880d411101015030101c5115160fa00e98483e01c403042485100a80c0070b9401c010019140943c0d5000962019601c15070140361520340000004040382203c2916401c0f000700c1015901042000300034058541d40008074050407002600e00703140449110b8958000160f4107101400020705815419500650180001450044505080303642841c83d40c9414401c0d80b00c1800c1c440b50390350640003004030002e603000c55130150b075441d0012400c840740ca581c0d91220072440c2106100742d203402d0300a41c1e00318030010201c4a24000c01e4480641102c10005400c049082a211a03c2c05087c01c80c1c0400c000c0000c218100564600100458142d02c0c0314000240110481d800148e0321003181d814800e4241e0f030030081005a4075103480c04c02e5056003e14034900c08607103403000015159205000316842034a40340005811a480c1d980d070480603046540800e0305020100000312050400c0e18040c058 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 745223884 1250 745222634 745222651
    0x307230d0b010801121b090218030c011b02042c0706080106320c03041205120a14030c12270106080a0f051207080a09090b01090b0304030314 62
    0x1510388140864030308481c0d8403454181840794150040007240c1c2c440c681041c6507504001032141c510600d05048404c0c06240c3c00c4400290301c003241050351b01840c83c8040817214401c0e400c030382192198a00654280020001c10030030200881c0d140340041c1002d8003c001c400800d0142c40c940352100c51102d01d0003508660204959500441c02004030350742c001c0319140145028202003214048280802e54001c0303c2920070f01c04411080c84035006085a5011204c2360300d80c0200342d80d104c5c0c0d1142c1500303030b1b10900b410b410b03125446400700b0010350709210401c844108000b602d558540240c0500c0410030340d000108030050500e400c1c040050021680c0301294811a401c1c0f15072142004548030030504d0140e480c41004003030389415814890300400044240c052500302c4510740d406203451911a01c2c046c02600504408180420b00b00100b00e0300f98054078041e455604c582082c242c442e6461000c44075602c128500040d1b05100400614203910000d540260291402092a000807102d240235000d05849030744 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 745225134 1250 745223884 745223887
    0x15020a03080f0601122a0c0c0b16150b090403080603060a0903020c1509041a0108240904020402070507080d140405060403020f011b150f02120a02030723 67
    0x400c240d484490365600542d5802c5561450800c40c000914150501d102403540580e21460301c20780c150111005c0f038840400d074414081035500ca01c001040c0300840501160010848900410b4010001c001c0c0d40c0c01c1e1400c000141e503500c0d00b030784580d6216100340e01d42c44902c50f5585084031b4191200c0c00c900b4030440c006d13203d1f16020f05190040c503240683c000c00d6544a18a8004220300090780410030441d1101c1c01ca4089005495484a0303020074821544102ea00620b0a800040490124400b00092100c00d0300d40c5a80d640d00d00c1d0320310350114003003000c0200d009004510b40c2d00510f0406072a03500306001510060034100c45995142c50301e41141c10a082541c01404a0b6501580c404082c60200c0e040d0241c80e4141450b10010030030302d000b14003000b80308285500a0704416440381c54201e4002402c031b216014081046e0070101940740e040f81c03680000700d00740b40016400c0075441c022580c070000400403020301d075035a440c501c40c029000a84a10200300380e1501c241c840900303a03801d00d0b0940601c03c402c00d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 745226384 1250 745225134 745225153
    0x31206090c0807053a140603010c09060e0d141603140102040303020a020d020411030a0c03140906150402090301020406050d0c08040804060f050415050706051f0b131502 74
    0x1030032400b40244101c04001c01084031400c1071084000c0d080c85034a10240740040841103003042d9141d90614407840700c083e442e0160a200149159100c0da0051b002a4000c010345c46481c01c0441c0d071002c1602800f00800c4030101d80708020304001c0c5d40c2501041c0180302544000e858001031606140503000009030941c4100d4003802400514060422078031a078600852401b8555503010b0345a00714018080d02c01c0240c1e030401070540d123454010800609001c030301c140c7e0300c1c6045140040203251a8400c1000240340405000300f01d003807840220b0003040324070020401540d520003500075820115100781e4205030280401801340c3c83c2400500090310700c80c0c841a46540301001d518080f82c4841c4110300420521600b800301103101d203000c6400b034403600c0c174003400c5510000d201624103218a9001180b40140c043e0400800782e07110300540b2100b4030421003070103030341c6034081200110426891442e000d01070410080010f141000e00034400940d0075a005883c01e940d070480c04400f01041445000542c10074003c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 745227634 1250 745226384 745226387
    0x60d0c03050a060c09080a02040216050a0506010611010507211407120b040b0603010b03070203190806011e120b150406031b0503070c1203090b040302071a03010819031206090c 77
    0x210b0142c113045207800b001da42d140c07001c6030b84d581d6800d03080607000f2a40010a0303020024510907850301c40382c10904070352200030035103442907540030709102e0704c000601703d070720203282404060055070b009001a0b03a681c4980305407a8952001500c404014a0146a40303011300b03034840c00b240c41401d22403d4030791204014844411905000d40f034103000316510542ca4151080f400d030ba80c41301640d0640d0144000d0b552241c0c0c801005a00d9481317001c0b50030110310000880c20355155813116420b0321820082e42c0300c00c40c1c00034035003425a440b026484c0002c003140c201e031481b400c81700041e8014602c03250024001d81d0400c0c820990866580e02035080f40380080e4855480c07441c0760002c04901d4800e12042c1c54a0340c614a401c2e00d0003080714100c490002c2000c06a42c1c1242c490350311035040b101542e0b40100b02191203081c10300d0081d580e070003d441030451004481044181c03500440040c1ea0490301c03040c0142012401c92014019880c3c11900d044040c070031070103006521031006106043c05451145400240001e04440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 745228884 1250 745227634 745227641
    0x50a061e0c0525050d05031008190624061b14010b03012304110406030b07080a0516050d110412031d22052d0109061e0e060d0c03050a06 60
    0x44802c0030141d100781500001c03030004007900c0c172020920f040c50710b039182c0c0300c4014034907800e60340003040714172032201c030190380112600c002c2c178100d48600401c00101c800da070700120b1085070f11520303800300b0152160300700b09143c040c0060322440000a860200480385940d80d0034600c600344104415903070b540d00c401e100541003d12900042921100d24021030900c00a404c0440450041009000210180038660030341c851f900554040c41e405940d41c0464900018011305c411001c85100e04014103001c0815441e41c828182020200025a00d0b02d161040b041e4101000e030485030341201040b123003040700040702c4030306071901c1048510075902d410311b0202510a0b103d02c041c108a41074481c0090f14203014400741c20320000b8030010701e111000304440c0e0f906101300000030110a0301c0103c1702440300c1d50f95000c0d50000f4529059035110340080005075180c1e0400004d64408075446e10100340305000511614a000c2000703540301c0d200078610004982c2540e1022400d049652046426a03c05500141041020302 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 745230134 1250 745228884 745228927
    0x1303112d0102070c060f0215010305160512340807030c090510060f11030301060509120a08030c13030203102310051302070623090109050a061e0c05 65
    0x600943c144141611070701c401c0b1406214000511265084020300f02e130003400300250380800c01d58082c08070340e03483c103003243c907050a80c071449a0003140304230105040c507101010903409604038004040000c811200c500c40d4010180d0740000c3c0c500c3d032294a030b40100c800f900340000b0f00000c4001d0000e8925500d040c0c401d000d8103030451080c040c2031800300b00d00c0c00e642144182c12540180b60070052103000c48400d0707415002c510260742090000000200d0f0340798109004180c50341c400e0347e00307103803c2e03958415180e2113103200d96000386078607000c001003040c4c943d00c4e5001d001203810310344241005542c0c982c0000c2c50b1070b03440c2e05c1c00c1810320b40f95030040303580d4102c40e600c400e1484022403102d805481c140812103107240c007038002c0c103102e0200d00d030340c0e91300000e640d0f1b040e074030996480a0200710b4040580140918280041c9000001d800c0610029420710018003c12504a80c404010040c100c0140d42d03003005400c0d11541401d80340320349000391180c3c000c1406203d03981c10780c9840c0c0030340e601141d4081d442240c0101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 745231384 1250 745230134 745230223
    0x409020418020405010c02010c3905060705121b010f0c030e011404080d0209090a090209070219060c050c060703050106260a0b060903030d02040e1e130311 68
    0x50104104c03698102e0b0800050540c2440c12142c0380ea44c80c078140209414903500c40c8144070f02c20580d022150b403488207000b0400f000740c5c4404240d60b66441007142034840c85200030b0035030b040415000780c0310003054090b16801c00c4010f00c150344016103542450031101803010b45102c241c1c88001071240d141d0140f1072203d040c843c4034024040c0a056020130100e0307130000303000100f0901e4001401903a440440d03043d41c1000714000e10400e030f04c0c103202c0402005410580c000740e1041c0b2400001c00ca22600004443c0d142c0070f020f4940009030500d9889600040042034402d409202d00ac000d507040284050081512a24080d00c0020713041d4140742c0e0042c804540d244400c0d030041010b4884e11500341a2000203a8001c4546a01061003410107000c80c0050003a403102a405100c0841c0c01030003081c06401400c1078072940e40003200e00796036030326418405443c0c41c200c800a0740c6142c001b05503d81e8064600100c0c0d24000d042480c2800010f103a203038648415000702a95124090b87c5040c284505075981c40d0382c10309507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 745232634 1250 745231384 745231387
    0x90a0b06060c030711030f0d0e0411091315090606051305030f031204231f0c0903020f151804050109090503040501081012080301060e1801150302070206040902041802 73
    0x2ca5005550391103002c002400c2148120000d075400d540c20400001c265428005540c0e800e0300c2c1080c090000002c40e103200b480380f400e144203149407644441c02d462403907400608844181d01900a12401041e07a811051080c1041c0d1402090740100381c080d020007003080703a98290b520b40c5015142c0c9851010f58208510075081a0038260454600005541000e0070000200032991180e20744083d0035140d1039242202c1d2111038107540004a00842d0380c1e424040d030b0340160031031200300c0d10640c03003143c00b40c00d610070100f40c107410306002500300b0121610100305c01400100c50a21a000c10315403940003070b80c1d1075407000242940107103035003004d004250040410302c109100c11600f5035034144e16030003640202c904010300400069001e4550031101c0f0014650308030724054640180c188034034198070074050400401c0510076803032141d0038003040e02c641c800027030000482683d080c421906004800b1840360b80c1019000c1c00488096600c0000400080c0511400140d481d46040c0d50800c42004800521000710310 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 745233884 1250 745232634 745232647
    0x1140a0803030106051606230108010e150720030a0e0123161703061507020919020c0f0a0506010608160804080d0f0b010809071a070204090b090a0b0606 67
    0x3030000540341550740070700784a074a41444101c040c1c004081101c001e0005818003190915a658094030200e403400c0700c2a0b49421a030700e54560500341c8801c02c110750303802d40c40242c1040c00180700a503c1508000030745001c2e00d0040d008042e103503044503120301c06d80e0320b038100184510700c1d81d81040408120702800e08142d130703281c4241e20018048e204204080f8404100000b20f413245009190703849461186d12101c002c0311000c04140035811600220f425a0041c00441100ca00038104c030700c141c4400650007408182680d0b55030b00c807101400050b0340d21002d115000c0c840801040c41c188000f51801030070310010166000741d030504c24070300041a8403606c1070080f61414000e007040388029040e00354441d0308042d0200d8449141c200c190744946007109811500c2c0042c448889140c41e04413440600c1c01360b03161440c1c3d46811001b00e0302e48549100344006011208811070502c4229005072000780e000800c00103e406d01034a40000300d43c000c03107140340183c100d60210b5040061001406030082c0d002c2d69402d06100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 745235134 1250 745233884 745233899
    0x11b2007031e020a031103150f04030f021609020c060606070807060209010e0a0902070212010b0d06090515042109030201090902090d052a1f0c0302030f030f01140a 72
    0xe881d02002e040c0e4400220301d01490b40d503000b0503000c00c55014100644070f5680b0309088001307402d4071004522034014001320641c0c4101025403140034981001841d0841e46842e0750964004550609400c29402205c0f140c44440c2940500342000b842d226401682d204039586c03640d4242030008141900c07490050058101040f140c0d016940300c02e6008400682c2c513048840163f418040580426074001100e190118940e00301e90081c148441c0f00303a41100071300c14502ca81e242a00c0989010507001000c0705505008510540c01034090f050141060716426412011340003c41102190280e51240c21440942403191041140b5500141d041c60308040040c00c541c0020224ac4292003a81003103900403d0300d458540d903015000600640c8a8112154403a050501041c601c050091448043c00c03820401c10550429040043c02c0190f1040d400001c0ca5582001b550b0482c2e40300025402c45c441030240e071035409c0080e00158054516201c10840b03c0d03140044080040c001110b003280904040d103070402a22 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 745236384 1250 745235134 745235143
    0xe0705030712153b2407020c0108130312110a090807050306070806041d07050a0f08060c03183c0c060306060d02040315060e0103030c0303020a03020c011b20 69
    0x210291000340c2c140c150410b132005061034074000d009038540106a0390034003100c0c0c642401068241c0c4a0000040c0c3d5039a800c050340c4508004400d03602107414100013606585000066200180c1f080c03c0902d05080c030050484111109690101412200006c00d4030841d41c00200c05001046403400414620f0305200c042520f9043c043c1c068814003501d000452a02d83d1703160010390a62840d400250000c0944080142d0b44401600c1564010a902180480e6840e0142e40c0d91094030300c1000205581e4449a80c880903544c80200750140c1c0c80c911aa4024002da02030200c18110030340d00e00315440d27845e2810344025016040c0039039204003039954480b1044a0b50701080c03180440b40215501c0c0d07100d0b504d62000c64118030036100710400d001e00c00107000c010080b45e82e40c000005104000304100c140d0319031400c4005500203000103404502840d0f50400006e02c85c1d0003d0000c0180c9160242c00d0200c40740101d8203584024a001e04151402c3d0320350501d0b80d60000c044000c844038400c20b450321245080c01c8a485 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 745237634 1250 745236384 745236431
    0x212120901031a0603040302010501090507030b0307030b0a2009010807030b03061f080114090c0d08030a11070816060b0102071409131a010801060801051501030e070503071215 77
    0x145620340f42c01d104090810749100200c001c019010558030b14162038000c2c002e041c00d002d041c02581c80c00b8045181c4034402c0c80390500650000d40142241e60a5803900100280003c0000900035128455064804001896004074038ad0280001e5140c0d400240090a4a0002440c89040500d04003201e0480d83c1c00240c2d4036046000c150702c3c0300c0000c100264030310454180d40c00c0305034291708160340c0c00c03101c4104030340b840e118900003c10748840c0c040c03d0302048185003803a4405400350b00c042c00030840100c00e80e8012011007400c00455480c11040e60380355011034010140001d180794141e08598103005007401800e003124001d10240044c00c0c04c00c40c00d44170080a45200394003c130344020000300e03500c1e07101e0750346081641c11042920564418200c5058840824003615545508015001a1410341406154011040404d401c5081032102004600416142c501000c00344141c880c0094951020b02802000d0010300b065070481440c1410070001d03080c12008141841d80c13811040c0c030211190709001a80703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 745238884 1250 745237634 745237637
    0x20a05180307090203090313080609070324090309030209250f031503051e01110a050f070b0c031803030f01062105090304030309080d0e0105090301180804030212120901 74
    0x1008080d040100b8a05034842d0404400948000b0a102c500640040a07161340d10f41e00309440051074580780b1007521a1030681d498801755104034428000107440044401010b4850104191a0249a6400001c1e03c0c40b142701600820f02482c014010b60811040759580030013085514281c481081c41040b989691400504080241d000001d056a910035000840c085003610850740400d612400d01d5903c51003045462a80fa00000d00c2a4203400b406002c0c51409024810f00350303040400d402d00c1034555034481030801c1c404000400441c00010b003050641130041d0350480c4400d4491519040c400d0b114845000300d00c140d54414000c00000c0b66800d11081e05507001c51801600c103444000c19140b034800b4004201002a041800700801d5140000140084a000c0e80d22003804d26903a4210b55103035000000786900103404075041c841031354018030050210a4015000080c807110785000c031800240171200c102c1e448440024104251300d40303032426041c0505218080c260060f8a0740c9100e5003445585013960 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 745240134 1250 745238884 745238917
    0xd020105030c090402031f1d04110a03120801060806060408031c06230102010506060304021c0213110c100e0a11031c08040309090b010207062001090c061101020a05 72
    0x10503141ea0b0509507040850064410754036420002101c14500c1078501a42842c001d40110020700800c00040d0300b840d8459800d4000d00740c0e140d9440704012a940f41c0c0703601c0c0c2c016a01102c0080056040c43c444202c902c0b03e40c3d603601b071550410740c0c002c00c008000b803c214402d20090000340b048000101c202c0c1c40c010080381a541903031f94400301034009440664064402c00035401074190303182c0c8408441a0604409074000c03c01030350740b4000c10805000030750303010b90007004520802c0443d01ea280140d41a0600040c1401190680e1242c00c4003038451501071100d809401203040d0300c07000740802c06602d80000781c800a01035181440616035803100780703210103410307030324650700070301040c1ca05001042100786440030403641030600400207010138005440840020301e04100010394103842c0d01c1024a41a0142d003e0502a171424500300c1c4c0c0c064070942c080111000303014012500d4102403042c900e05074401c490b0754140502d440c00203405949084031a50719640104204040d80b0380c01000c407080040c0000400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 745241384 1250 745240134 745240141
    0x318120a1227050d08010f120204110a020703020a0f0608070c030915030b1305090d05090f0901141302090112021c060609081605030c04390306080a020d02010503 71
    0x202405803100c81505640080310110080700044030302c41038042c0204200ea120800c0c2000c204c1e10340c076003445101d0307411403006003c0c0704100303140c070720000f00178002000401c00582c90070298015600c0082c40354050b03404003d04100318140860f00c03030010203148000c1c4600902c3c0980250603554000d05480c00c01420200e110304240c05000140e010340501c941503041d040500d0705c0030380103000e0307107a10034460090482d100d40c0802c40e40c00740301d11800c06103018100c01074a012095409804c0142000d5010200c14850f0b140703520b13441040b5008240d80242602032241080c18401e0760240d82c4403081005004100b514500e98202c252144441080d00005940d90310801141c4040e000d5500003d401c6414480005400d55005a595041c0c03101241a1404440300c2d00d00100e41d1020b42c8902c076090340014628148500e45603004150308802454091401d171110203c610341640402d03010021640c05260300e030000380d0b040c8079460292149034006e0645441c00c2e000100c1c42c4801050090401070000b001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 745242634 1250 745241384 745241417
    0x1a071a06010c0b0c0423011205060402090303070b04021908070e0703021b010e0f150a110702030a080c070501080c070609110a0611060c070b0a0e1507050318120a 71
    0x802c11164105074843c2c1d440c10201581a2203901a00c503018441800c1103141c10b1b0680042c0c40c952507035105844040c03481d000c09000e0005014010407180e4029030900032451580c8042c001880340303512a60b030a2045180a204000203212000140e465502d5002c0c4140705101c00001c00806844985a41120030b640304c581c22000f0344203840d600d103286683e95520001301441500203010182260302070b40e1143c201400c81c1c560700c0c000304228202c101b0040010440b1010317154000306882c541d81ca00c903407500034a500440d207400c00c0d8150071540c030280082c0c220700d000000d100b580b003d4030092030a002d9600304101400d80500603541e0207400246d4a500c41c10800c00109030410b048200507004051680c3e4414014000c05601c05d68444280244400101320100300d0003100c8035540c0c4048449410f071070340c00616004111003a04201c0383d105085003001001c4004441e07510503017407560340765901c2c0303001035450322102c00850034985a94060352403400115507030420341e08071003a189020b0142e010088030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 745243884 1250 745242634 745242647
    0x141e03042709050a02010825030e151906090203011212030b030106080d170f0414010207050a24140a020a2003040608010e0108030d020c011d01061a071a0601 69
    0x10312903078945440100d070b04104000c9000901c0d18000d032219020f41c0c2c3c602007004079110040078010001c50f01c40c4c600b052a00c1c003941c0404188071020b012030300c0c101e881c001c0d450300700e08094500706c0c400ea10403240c4881240341c0340100340c040c0007090310641c119407403c8d4410b0402c8050010041120070b184102080161007a13220f00c0507108010004d00c40300f50381e0050315440c1c0f60480000d000240c0525031080501c04030b000c7c0740707018145006549001c0d0b41d4135151601c201011217400041550200310550200f00c1c10011170354142d00445170006d01c0d812700a404035459003d400a0030285042207842006101c04500e015845500c031480540c2e1000300d082c0844011181c0000481c0e1803220702100c00c88070304000f01400560308a0348460100ea40ca410f00350100d03031400d100d150699441003101407103025040d0007801c10110000c3c00411855a0f5406041c020750711144802202c2e95100020815003242c10100781c2c0c0c520102d20114600211501c808501800540d5409015844c0c400810712a0740b1030b08 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 745245134 1250 745243884 745243949
    0x3081602090f01050102010e0f0604110a030804092c0a03051602090103080d050708090a301218020609120c03100c180608190e0a141e0304 61
    0xa014100e503250049508092035028044c007030040d840d150840c0400c810000d820004843c5800c02009940c0d9a59a1801c114600c11440b940180000100000203980007026002400c00c6d80004100000150441c0e0441c0b9030041403c411300b0111240c80b03850f0789020900785003064051800581e40c00301204800300c62110000029001100c00d00000140310341c11002d4032042d810160140855240d803002100e6010081d00c10360400d0700018080340c001211049503c500041803100805c5449408440c0034100c40014584800f14404040c81078200a05119040840f0952034000d40038403021707004144580036070858039004400300406850b00071000c1001290358040101210b110720030310800100584800380382c03a00415411a010803081c1c1e01403145070182c07005070382c7e58002903891303401c1d81d030008600e8a00380340c01a0343d8100d40c41c3d85a20601c25900801e0060701c0d00303482640c1009500340742080e850038507450314500c9843c0d401c0350000401118122030746451003c40402c0008801420800c058 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 745246384 1250 745245134 745245139
    0x31005033c0c060c012a1b020a0e04030804020a08030310060c05031608040f0e040f030309060e1006030c05040b0f150f0706050402100c030207060c03024b030403081602 74
    0x3007030103030304c04505400907660480046040c110010107410b0211000720a12155404240559500483e0f241c426440c4d503002ca000130841c00681c1c1c0e80c4d01001c241e0039015207040c1d000415180c208001e6080c007140c1d080c01886804015851071419002c01d589112181c0a804100b08924003501c00340308003001903408804e0303003002031040700c8600d00e0612441d50151003140c0304005040c1e0002901009480124816908140e4110850106a600310010105104101c402c15a6600030030421a800c0004506000c42c19500040103070031820640700304621503101901c51810000c0c000031355201d04400d2740c5000300035219044100c00d00310484000c1e01817005c88d452030481c089804030902c0b10342c4d04941d0045000f80c60000704a0303034841c01147c46105011024000d40d10010040107564400c040080e83c2900030310540b090704841c00903080d802c01c024540141c4240e90ad010b0250700900c949600301900d1018110004034418000700c0988a0003148009002030034040740c620750841103046c4e1066001ea00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 745247634 1250 745246384 745246387
    0x108060c09060408070f2c010909210503090c120d05071a04080702010905040203070c08090a030605100906211112010c0206010305060a0908030103060203040f0206031005033c0c06 79
    0x42d0046000001c6d0b40d03124011580020400305202d40100400001015000c1481003a050f0309001220b805840010b2044030f4421100d5240d0f103844807a401418643d003000d40d901031341d0f1304244101d40c1c6800b61480040f03114001004000910340c0c000101c1560701c0040d0306140340c542425040c018507100900c0f6803550018644001c200070000044000e1402078400d80340c4240b0907480350144422400100c40076808504e04084010201d900c01c000342c12500c030024170580689441e80e542105852065882200000140c5824841b94917280a40d60250141002e1003a2010301c014031180e8448180302c0160041440043e02d695903290301d924140411081702c003d002c20b01c800d00e030080da1100c09200945550003018042405800c107401000d001d150080070060540c0d0035515042c1c000d5001500132140080c207040a08010388640000e5445000d000c0d00d07102c0c4080c070700310605060a40c10f034005982840da01ca40a500c140c1c8040c0c1110030409101d1103019071083c40c002c107a01d006803407035456030302c001d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 745248884 1250 745247634 745247639
    0x1101060b070b101d0a0f1b182117070807030503100e0112210f08190504050304080c01210903092303010f0209010503060d060912050a020c01080108060c0906040807 72
    0x7103e0300c2060081c4000c0c00101700401e080011482154046030b4004008000091f020005503c60707a0310007000340c00403c0540c0b09540e140001c2881c510baa40d82640e0000c4001c0c019018020043c0000d4228480010787c01e10b8624243e403006180d11405000900740900403000c80c0780c902c1001134070005003842c2d1001c0300701c1e56180c207591001f90701100710445050000d101d00801140800b4804040c0c07a644c1d4075545107480c41440203498511004107400441865544c8221000c901743c01298000c81c01400030759550350620b851035041140298400741882000001d0180400e910216684d45196000b0001480c801c42c0c0307030441e4004c0080d40101c017002540c01a09001003400c041240041c035086000304107004540030918180c7c021901035038049a0b040c00001c0722410654019030002c1d1003500000340310025a0344007850904441802800030f90045048a03005030100f14141c0510000d0034015107540c9001080c82d603510300240220701203540402c064a0a480300300c1a500034140b01c000703403a041c030b4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 745250134 1250 745248884 745248929
    0x46020f040506030c1312110102070501050d09170406030e060f060603010b0c0109021f020c01110d03200f3403030c0215131a0f01090b06070501020c010b011101060b070b10 75
    0x511201915942c7d02140782d00059070002480c00107e40381a1902410039a050415900074a84d0310000e94004110001c803040f0704d2080c00080c4042d181ea0303100081e2981400440c0d40c60321000034005007828443c0001e100b52030351450262411a03000520550740e80754403001450241c08584070094010016092021745910400003010704035180303170300712000d558007100115403001e01005480714070b030498141c040041e03100b60024400c00c805150351401c00c0340024120303111548200010201e43d078020810000c65802d0791220030b8100c1125805e121641c200f000108500c142c103c1005050540c3c2e151780c009414002d20200070102c424003141c4d0309601d00340a44082e501c220040840c1c0a035a80500c81581c5c00840102c9ca002d40005010616035a00f0410f0820061040302c03402c5e684401c060004900045003400103001030041e0000108410100700d00140541100c2184040180d04008090181040e26401e84100682103038000405480e04800301c201c3c3c2d04190040080c117001c02d42055000c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 745251384 1250 745250134 745250159
    0x3050d1d0102010216060230100b091c1e151103090a0f02130515101e050f09030111031e13020946020f040506030c13 52
    0x4500c0310940030300810050004908030300c07a000701c0c04a21105450b01c00b011540c17641c0900003100000d0550140111002c241c0c2052110a00741e240d80200038104214a0015000988008001000007142031482c0341c80010f1110b87e9844044160300c00259481050080c0340d5810f07522a1a041d0008a80c25107a050400000c40c60003240c0c030303400e41000841d0010481e0780c400c0320b2182d00c2d294081c011102e010303a100003400d41540c2c13069a02010394901403000151a203c0c1c98003a0400e02c0260040da4210300c01d102d031080440700c0310801d01941c00f190340b0f4103403607010351246c0302142c07450090b1f83d0740c00d2104140414006c018009416610b0100b0b40342d00608002c0085000b01400000e103000c1a90306144400796100c2210381c0c0c0071414008510500508000d030080d03800c45c7c603070010800700000302c002101b41d00034038070b40100d1a08040c1d000c40c600c01007258640144d4644014055141806c0001c03403009512407881528091280003002a20551984042e1040c12110307600c1085442d503902c4c15100c1c2ea = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 745252634 1250 745251384 745251407
    0x507050c1003151e03080a121b1b0c090f091b030b010f051f0c0b0708070906030509060105060a090306020d06030b060402090a150203160503030901060f060203030103150603050d 78
    0x40701d40468000c02c04c40c84000d2544407001101e20765800403401d503079607100c0641084c8020028084440307501c00300003586004444100c180c0f40000c00303203891106c00003040c080355084030141400c4010550408200c10244102c242c400008020500c00030800b500e80082040000181c0070326040691005601c030215614000c0700c0c0242480d070300d181d0300e80c001c1001294491064035801210301d204861800340030500c500303901303403a424600458400d50f1200d01034500d04460080001c0d0b00f9104006102fa0002196000b030b1038540345c2001907203010800a640c8170018050b03a40701c0c0c6d0003ca000300341284101010806103a20040564032000160883d8010b072560380400c4513002034072000030b2818181442a02d00300cfc0402030801c2a158a00303080503e00d000170f0584441180803c0210344e0030b8003c50b5184c0350080e4441d00055a4a142c060000350848000e50411031020f10100e1040008a50000917241941c2e00a9611411021004001c070018001c551004202d401034031540024690000d004406 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 745253884 1250 745252634 745252661
    0x5071e0e01091d0405070f14011206030212010f230f130203030c060f011a070f08090604030c080f0703050a170d0e0606030c010f0c0b060409080c0303100509040b04030507050c1003 79
    0xf601c0c6c47d040b0701c2c81c6a00c864003803020464440103205000f903200d4030f00d50b070482c00541c000144840d10381d0003181d1705032641c05039040d40e41c1d11030382d0b0000404001e204015400000317800d030084013844541d03460400c3c14040c09070110f8050741c00105d1920340c04041150900703030740203088913a145a034038120f41d1105000ca9413803031851010f50002618404404244800c01840c00c4920710303126603561100c50181b450207054810960034840003403e0303107400b8000d001450048080c1180b5074a0448080e26100300c15420b08070b43d410034841000000d0000800e000019403200301c001080340300300c40050703040c016408840710a40c00c1c020341c05800c0201148181c0201d4041d803d07200ca142107840190360240030720a0500009410841c05000308030085402500208024004203002c0c0c15a1a0a101900217044000b6580c0002080c402d241e0a2a02d0501c0100001e9420180d14513207074a03010034420004101800384103000429008019050041551a90300203080b0380ca004012000200108901d902524 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 745255134 1250 745253884 745253893
    0x901090b03191e05130210050a0c15020d11040b03040f080904360b3c071d0904030e040b18060111030f04090c05042705071e0e01091d0405 61
    0x1506040401031740c0c20099001703441c02003001021030003250107034845102d00c01044192142c1900060004664404124104030056120342000c042c0c18122907001c013804907011400c1008218032550034064075030182d08007180c4e0b4100c00349420450020b101d620342c029030003841c104540e03101001401c03042e200421501000702680800f042d528214003861301002c0c19800e4614002024440e100910b91078030020103080440c8d51004e0440456400d0303070380c43d5016003040340e8010441090313480441000741c0b0f540c03030310a070b010140000e02040c0c94100c00f4102404100120500000c542c0380d541001e807041178050701c8001016900c61503101054810703640b41c1d0004004002c001400350000060b80d01603001d44200600c1d1500d0002103500401600e01c5030070a0007424040010018420031b100031020003002035040c422181040720004039000108640103202a0303054500c040c07030400004140400c1c081c104803100d03c1e1640c1c01603d0342113141c1d00c00c1a00b03103003600f000044504062044c1d80540e20540866 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 745256384 1250 745255134 745255141
    0x608070812093c030102090d0209090703020d060608010b06040308040515070b090f120a48020a061706120f0f0a0b180a170405040609021903020901090b03191e05 71
    0x7501b40d03c55000b985134400392103c00c0700302506e00f81da2030071f4000c003c00f021500415aa41c0c0407810b00400c28100340ea00035035801d41001400401e0040c07a21410b01254918a03042c103555408501d4080c50203014041e041040b10f40302c1c6115400304440300a03400940b5401c4502d00f15054580d80c448203c082d0240303008800f0070840d80b0004906072401e0615988a441c12127510143d0380c00c0c0c003401044d8180c05080c002200da82e0038158800d5001c4084245014250700303140d6401030060507203081e4007450410680003d00304211044d40c0c200c503007107081150300350441200c0840591405285101d2030007640580d14801c0d200210008010011910400c2c81486031b40d203100400d510059032a4840d000380e0070840d001d20006040450320702011892900240c2407a032120041001c44500e03804c80003560b40d00003280381d040c0244000720151003c01d440c0542c0f0b40744058000070500c80582c420540742c441c0201c045805691060390304054101022400c03c5501b0318400300302019080e008400d540c0a00e0440071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 745257634 1250 745256384 745256389
    0xa1707050604050a12110d1b05010804080a0f02160b04050f0303030606030117011407080601080f063102280309080a120b0a06120608070812093c 64
    0x142d81c2240e600920307000c00715142c101005407154001008840d91143c0484416499450144e1451214001c000340d445c04c5c50350789594400506103400c51410720281d1010031000420407000c07108020014901704580104100c4260329155a40000349072884180c132001c985980800c024004039001100c0e00160f10b03040d10241602da10003512020b030410010401800003420319520381200c011008000980c120b0080403c0004940641e101e00001d140d03001400010b691088046803c141c58034044c1c8040e0404500203900044c645404421042241c0002c03201c0c019142280d1441c032444100c250343e1180c0c600c400c111401e00b03142c21640d84284405003020014400e1040c01e212650100306030b440d0080e040c0b001ea46500310044600842d5403602401c202d80e40b24040510b009013525242d010400c03038560700000c142c0f1400e41001400d40d0225030200502040044c01d10071101d01116000e68506185001c10284481d250f40340c0d04002c00d19100d00084422960311641005031070010b2076690380c20004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 745258884 1250 745257634 745257637
    0x60306020921191407090507030507050901080712060305010e0a0519080f13080102180f0f090f0408040e0103120f080402060304060e1f06030b0f10090b0f0a17070506 73
    0x10295a9400b07401d8183c0f03054448001503c0703050150000b0b10324440c0100f100780c60441c10b900017050306600d1300103000e03805416024060700803000341006420901039030300081170620000c1210041001542c2c00c0d051001c41c9520400c044c5401070001e201141c0002002c9640b40c0b190f030012a1a482542600c010115502d002c0d07851860384950181d10f4810442c860310040d4200765101030384e50466070380004403400c0c02d1005000440594030040d14148025040010541b910380509016500300400d0102a54641d0403603580840c031003640540a8a65060450150169411103544183d00f08008028040c1400c20140001800da890a2920100754411a000c0c50280d0f002034100d442440414000342c5d00d03400c031040c2a0344040c21100c032003203000342c0b1040d17522a08409544c02552020148240841161500d030700c2002d40050328890b040a00110300644d000740f01c0e1000303050361a28070b900a641c03260082880361800818082201b070703c4080482c030304c100b003a072441036070720451000081c02c2c1400d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 745260134 1250 745258884 745258939
    0x9063c090106080c0c0c0d03020d030b0901050a0b0c0a140604051002041a2206090524030f04062a030f0e070b0a0522061b020d120e040603060209 64
    0x10389200f40c075140c1007004103554001d503d9140850003228009500d6031601d0b030954540318000d50040c01019400f01c1c014044840c3c6000880c06819004014441d54403011040402c480702c08404d10b945000381e440c50360400c2c1c0d1101000f428403520305d00303280c0381407400154203008034040d1703043e20503590490700440d0072407145200e0060201d403030403100960004103401904010600c0c0c060600c1510030303400c140302d080382c00b5006040030924080e4240040c2c01c0400c010880804501c3c8149a003c008c005598604c3c04011b0242c4e04140d51078000404000c460740003400010010411402c26161010300c150b00304640291400000f4981044102044501d01420148029801c064540c89003451840083d6038408505e410900c8810002d01050500700041c0c03e02d144c8444001e13411242c20000014600c41c054035294400641c440c05c103502680c0c3c1c032014281240d40c0b002004443c1107a09200b41c0c2d00041c040d2401d503000e40b400c2000814041150001e00d0507542c119580b4803040b09100c1406144900d05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 745261384 1250 745260134 745260137
    0xf02132007050a14030c0607030203070207080304050f0d020a091103160e2d15090102070b030c0f1e0c0705040606020d050d11130f03120305040f0209063c090106 71
    0x810031501003004200c0704e00303111080c0000d4078600302282c030b0001e2038481c0a0b2258000268000100024035034140521000740c5256806103160901c0c0500141e400e00040709150320a03041c09036400c6c115640c50b0103400040003499000d1007503e21031040c030b00d81a04204c840b043e840d00d0328500c1d04421071052502040b4034200030b06422010000d00d804000c003185820300340140807402c680001e01c0c2e640703c41c000c2c01070f20040f1394010ba40d002031000090420701c603079020801c140405c1c030521803c9090348042d10010b1805a00ca680c4034403a400c0701c801d0001841101000c82000052401040000824070400f175400642c2c0038030219645500c12681d5010340219500014801e0110442d0742c03d460b089000229040f215460506000c148402c0c00400c250b4400c40f405184480100204a030041d1803e2804105003407c0141c1e03d41a01d580381105080752009101c0d02c0c045000641c141d544040d0100d41e400f41c5074040e44d00c40c09135084410505000d01c0d040203144400e02c00028541741501c4558180d9006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 745262634 1250 745261384 745261393
    0x10e150d0b0406150803040f0603050702100906140c0c010608071d060307080f1006150507022404080109050f0a031718010c12050601031a0d0f0213200705 68
    0x55898110807110040d00c1129003c1d01c503ca0a001882c455800501401c048806155a10301c2c0075110360f1512015441002418106410040710035000302d8194444160b01d40042059005854800010702480e1010203003e1000c0f001e1183c0c2d02d10344005444014a03820003040703003075203602807a503481000d0b2081a909010805a0443c0c030111200c5890704440302030300b1605807580703a0540d00e0501148000500443c0e00c40319114450084a00030f000c01081130b11045000034510510040543c8a003200213400b031901084400c103200050701d400c0525112404240b5150b0352108201070207090204003d481c1485441c079012154030010070001107066140c0c5520350f14912000c0c6680c003284000700044507408480c01480c1d4200303400c0c019003000101582d1609611088008014115900a4400c074101450203420701041303a02a0884050746008440c0401090b00506e003010702c05200100c020b410502d101402c02e094007290704041c3c41c450900504226540d02803e07841c009010340e00f400b0b04207501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 745263884 1250 745262634 745262659
    0x130051503120a0c05010b060f0a1d0306072d090801140f0a0e07120606090c02030304170310120b0f0c16170f0a09050f0d172203030206010e15 63
    0x78a5880c842031710803000894400624000180c450300100a40380d036010303001440303d0321190710603003040301c2c29003076100c0001e10348110001c01c4d03403000d004144106008401c0c520148601410148564040e000201501606001e040081640c030b26071049200e50760174020000342102c0b4140b0000d100c2c591000000c22166103400200c400341c90310300540c43c403138002c42d400800d451b460281c000c2441c1c2d0003040e001c5065464040c22000316060303000c0c0b62046400a0040c0000947c659406115045d000402c50751a0f44522141c011460f400380d22008007482d150f02c2ca00c08019604a03980d00c42c040d41e14001c038181d60341940c2442c05220300704244002841004035080001c1004402080d040d0b5100003075802c007540041072030030350390021100b0408622180741c00c01840ca0b2112121141000641d40306040250b039550f54000110360601013980704401140d4443e04401100006c8166664031251082c0c8a83d2414080d40740d641c01c1c09030240068442002540032030000c1301c421105000900440c100f0300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 745265134 1250 745263884 745263887
    0x10f060819060204031b030213050105012001110406170106020f150c040302040f0f0605060f04290a120f0c090303080604062402011404050a020130051503120a 70
    0x5a07800048407400e50030f110200110f0411103041c6842c0441c1859a5400340c158010403280d0b000101302d001003142000010710060740c1c040700703072a048051514000e86038440c96144a01414072400c0440180c900420000740c041e6201c84c2c1104826081703000665681d807140c00c04c903291920010b0003001070344054641864107440d10b0382d4a9011400d502400d05141d01d0703500003003c2c1d50010720381d4034140c0e840f40704008000905100d2440209070850f02e06d450b03c0543e039042c40c55030080d841800b03054222012500c22149081d0100c03e600745405407030550741e500090020300f112a500701003000b03203843c004505120f0711540c45020f0001615455032a1003600d596011a03440d00c00a21700c0c2d41003510303180001040e442d01c0841c0d080803403a40c16066101e4145110080c04c54034014058070604200341700f804081000072481c450415020302c0c00050032003810904030701066407008000d2031600c0a0480d455600307076560000b0b0240d640840c00c070072020418410507a17075040b0b088100f04404002c0003207a41d5103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 745266384 1250 745265134 745265173
    0xc090a1e031202010612060603031101140109020d0609050702060417070b010b09030c03011505031002030f360c0108070305040c090c1709070f0f0303050a0513051e0102010f0608 78
    0x91660f40300210300c072919200340201307140400c0c908491150f1103480900c10181c22503180008001c00d039000708181d10750070f280e05421810611901b0b01c09075000501c11291800c1350403040140c060702c10141300074241090b00075520b06048a069507820240400102001501400c0700c0419030480d800222590030005200e05030351000c60f840768540b00d414400310300c1d52401e00840750b61206101800210514040a05d0300707280201001c81c044520400070414040d141192281d000a0901c545c2d01034109078009910b212400f0103640e444c2d1030380e501070310b00803400d0001d81152030082c203a890491584a001d410b4042d04c40c2074400030140c0165160502c08500c007a8441c1200c20344600c2e10001d4a607051079100509c03102030354465410340021030240240c043c0510f84d81c00030605203403003503181481e60b20024000c0c0a0000e10300c0410000103055100d08400503852030280000a161b007041c82e1400400c0d500c007030510350b030070b6015509206003240c2503074891094030112203102018002c1c01410000b1400704 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 745267634 1250 745266384 745266413
    0x1050d05030d05130506160807030204030203070306050901110c07060f0e03150403050d0614031b010512061302040e061206131403120c0301180c0e040902040f050c090a1e03 76
    0x40410a0700c02011070f604000c047e00403c25841002091013049000900e110780050401f414140104800c10068400240410480c0e812030300008030b035256200302602400c6c1e03024032004003079070120f62807200b0400070614404580b00740d10313943d0341c81d8040325003a900c0c4920340c0c401a07415048101444030b0000d18a800540c0a407080c6803007407400700d440e40355404946071600800591020148042418102000142000084a07110030030400002000800c10320820b0701742c400d4540910003081c00c5855151345000f00c080e400382d0542d00c03551241c07515000c0c050215a51031056400113400c0c0101503021500d40e0081841105544401503140c880c040c900010354801704891100b0440800c0d0203040d258800e0040750600310156403545010540e0044642035051194070602e00641040c5c0b05030000032411041e48103880205484c50303180009401046080041401d076401c0c4000c014880307000034010102e0040c02c0b83c400042940340d8051900c00c905102c0d000d984c103421401c05001041c00005000309 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 745268884 1250 745267634 745267651
    0xb0609060d0603140a022b12020f120d0b0a03020f210709200f030601080403020a0204151a07020603060105070203031e0406030c0810140406032901050d05030d05 71
    0x21115030320b91301c070b14107580d02842c5483d064011510000451900060a02c40c1419000c0242482e154028082807003250008009080200e00350b22207145038001e00c0b00c07200c03200c8140e060360583c140701025440c885d44202100011903181c02020f0a841c60210010400d880d00545109025641401400301801c03030702440c0100c144524a0000702640700700030381009001b000b0750100b031142c8140a0031003c0460508500214001482106a0602082c060ba60310020904e0440c4103900c4500f802e81c113090b10040f01940060172319011180c02d44501442104603400c1c100e00c80d03000c01880804003014024030b0341c000c3d8441e10400100c2ca25610030006070841c140000c0549241810300d0000300c461010540c0744450101001c02e0810980341c25115184000d00c0a007469100c0d0318011804081b100c083d03014040c0060817801c0080410b465550104000c1c50344200034044c0700000c41080c20000c8507100c0c6d50800f030796142002065a04252119104056001e0020360410800d014440b0161070020315468 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 745270134 1250 745268884 745268891
    0x1e01050f071e05010c020d0804060b1309050105070f03090b0103110a05030304090e0c0901080604140f030d020d1802010804140118060b040e0613080d2417010b0609060d 74
    0xc26590310300070407060b01000d00d45144618502d410b5003512500f805840c1035401c14012402c0c41d80d0060181548180e011400051848a6400103403011411040d0105204e181c42c0d80741c2e0800c901503029a000d441c540e110300c02e6143c0701e200221700703980010a008242040b080c00402c001450000d550904040051101c00070940768000b20346107400c103900c22895030361603100e03d03e01040706206c10000c0324000e594002c032940c141580d02d9a11308000e000100450154180910342c94424081c1d0101240c40500b50783c0d0780d02006c20b08401075040780e1001c000c0c061608041c20180d4954201504034258181c5458290740e985803500100703103a5020a40b4140d5407111030250b0182c0141400c0d0115034810720300004c041c084403041c08104c9800d50021006544a6400d0083d0051403801c800005a40480c2d4150344443c2c400783d05014207845100e1031040c04c501c180c01100460b011307501c0d0050f0703401d0f03160304001e542c0081f5031503098a0100500540042c410011059141025001001d044400d01e0010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 745271384 1250 745270134 745270147
    0x60506030a05240c031003110111012d150e0c12190e0c01021c052503120b010516110d06060911030915130c0f0e061e01050f 55
    0x41c01e01082220100c0e001001c0c00d00f600920008442d4160014901210241540b0308030740c410213108118080034000c031404402c0315040341c2c4140b5466881e02c5500b0002d125107421038894089010440140e10200418103010102c034810078461981c2d0b04180c401c20345001c510f042d2030100c10725009000d526001008001c490f000c0190b40802601030001070503c0071088024480001c211401461030040f00c0d04182c94550050fa03001619101030b01c864450310150340d0701c901041d11207118403003e51025032003003984000e401c1c0c0c100001d00d110034040e441d40e8a18440c1a403d8400b25101c8500d00b5000c80c4080c01902c0c0c0c00c00401e45403440f094481c114051070582c456000509000102408a480300e8503042e061240d08214084e4080c44040e01c80c29034114141003c025440e03000030103201584410803000291151002103c1c200040d41020680c107403da2104101484ca15290241403185402e40000c185141045c203401840018000c5264828200000045a1550010544089404050200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 745272634 1250 745271384 745271393
    0xf010504172a030726070e0a050702030712120f0e07140109060903080f0f160c0501081501030525020102091c020a0b07080d050c0a09050307050d060506030a 69
    0x5150400740780c0080c062440c000c542984058003484440c55000d102407200d0710140c40000d041811769218000031060341c2030940190007540c01000d180462803203580300001d210780310010541c1c041d00c0c105a00380101e64555406a13960312138004000d184030300000c0c1c0d501440740b19044011a003c900c000110310101345001e000c003034440e219400c42090700240d00400ca002805140d441142c042802c04000403890080080d000d19124032014142c50000684040450402c000301c80494038040341290b114601001c0004000140c1c82d0110303000c90782c240e40443c40b5802201864429100c003107032884403446140045001c1d01001d040800c0c541c0c480003056050301c0c0d000c1100e614001c13840d4001030703d4450350800c11105400c0500540488480617801c0360141e02d40350218070a55060f5180030f40d0b1542203140c045a188070300c03203101015524281c00d100c94690408020000c6102a81c2e40042e0161103e00b019150ba00034411a54412585000e0308002042c0741c00080e03000710014150f40380420359403a03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 745273884 1250 745272634 745272659
    0x5070b011d07050f092707031e0213030204090309170a02101b050d020a021e010e1212130315060b0a120605030d05031008061314011d01020306130e030304020f010504 73
    0x403090301448031b034203035082010311104159440101c0380703400d00084107030781c4130191882c441c1010600c0403a00055400c000e40c03603603103800000715800f40082050762201c0c01d000306580c0c3c90f4001da140f114072510000007071a5001a4001c91250010803119130341c60000b1007500c44005c90244008200e0305078250f0710109001344401d044c114400e4025140a8065204200403000015003071005001070390516600f50760b000200e503080c08002c8c0c440400854142d074a86140c402e00c0d6440b901d01c13200024490344944080620f000460f0f200c1c2009840030310024441d50241c80d614019505083c40900c5000c1015200d50f03c50b030001c0c010005c00044080d1180c02190900a0726000200410000414070980941000d030400081c00d80c02e0160405040108003000180840c1e0320141840ba003402254280d810300394010b41484403d07148024050350040003650107908206d80c2c20388540601940c80003880c2c4a40a800040c0706800d014500c0c41d40e03554200001b4005101d4000e0400c5010300000c65070a034081c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 745275134 1250 745273884 745273909
    0x40209280510020304080a080f0c030a090501030605031507030209060c030f070c05030a08161502031503190209060d030c02120601030c140907030c030f0c05070b011d07050f09 77
    0xd840c0d103141800c2005001c0b003004108001021948204001c02a041d0041200c0e00881c0d400108665985c51a20002c1034500542d1200740d114040001d034140c00344d401040b0081115020780701072150300c1d83e5400f0540c4540c0111b100e00202c0060b0380009555911072b500510040c0d2004001c1c6040c20006d00d4641d01e541c00005001ca54507400150802c207218000b06214024401100200b2071a640c90b618402c03680141902c42d12075175200e5250208004a03503519008500d9103540840d00c030315050865200000f0115500c4d4001e0068480414440c02c0080c1a00c52254014200e20b603da200c020500500d5204240c09800300304041c1140d400603642d81c44e10036001049030000f4195035045086c807414410640d4003045440101c51255031160f11a20002680b00300f081c1030000340c241441c8010740251070501c03420072002c2d140500e0010000d811602070451980210180000e50782c81e42d00840c084900d010003020401300800029187c41d10640c0100000144605110f040a1101000c640c0c5a2181c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 745276384 1250 745275134 745275199
    0x12040303030f05100305030415030b0405090d090f080309130b040227010318080918091f090c030f0309031b030605060d032021090a090b030705040209 66
    0x340242e0368111082d01846401080c2d50304011801451075513219940c0c807a41c46a2188801da0360343c81500035019900000712450040c009110901d000c5400d103840310580042c000100f10203000c04a84034012103d20341c15120b5000095142ca81440704210140600101c4112000c1d00c0c0c40549502e52281c1c00941003241c4520050310765202d280220002e01903890010302c3c1010314002d4207e03020509100120b519682082c40c02d0f80e01d0a903400410b4030f846144045404440f02c5e802800408680061801d540710154100d112506091620120664600c114040e0102d40d21030382c1403001c1442c03d40f01c2c0c0c00e01c510904103040c04a56954582080c40c1200341d00442c3c408070204100280811340c010640d0003c021200040001d0843c0d5021f401c0408810f1600c84a44600011005032241000704100c500702c1401e00210312640d0309011901780d4400c00ca024000c1502160005545205015802c8075410007405028231500b0001840002d400681d070041d030068414144940e00004d5031000000c2c404070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 745277634 1250 745276384 745276391
    0x204030212160e2520070806010608100f0b041809320f0c03150103051002030c16060501140d051b01020a05030d2a1e021204030303 58
    0x250300410039111500d418011460b0054440740260103016101c0703005982d45049a04803076114586900d801308683c4d0480f072244c48601c2c02d80035016400205420030003000d00340040c800700d40288040d0300e82c040351003410003d80c0900c0041c860380d030080448960202564402a01c01c41e5540035001c02d210031a803108a00040018082c401025100b00c03035005080034160501c041889580e0b0340191090442c1d810050410358000c41c201604d6140c0c0c00c95a0380040d8089550000d9070441c51600c4005040d034240c860702c0f58921640070440e041035904d04036074000b40a828021001c900d00406540010004035000d50104000c1c025594241d0000160901503070b0006802c0d07041580c0c4019004c8034089c0c00e8801e8811010000014000180d244c005402200c060311035020040c00503850134070108002011400003081c03105182205900c4000d8012145030000320340c01c2600f07141d0001c510501c40c0d07000000c41800045039240c1d94151803840801491049910780b8010310803400c11500070340c1046001079103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 745278884 1250 745277634 745277639
    0x304061a03061e0f0903070f1e061d060f040f0201090f030f03020709110a0513030602120901180816020f0a08030904051608010509070e0306010603290f0f0d05070602010204 76
    0x1c0d083d0415a0010702c0d0118500182000c80c6101c0c5e0328080c1d034000501c003901544c9007808005201480020141402c1e121032104002858120301030800c0882e08440103030307030140d030112a24001803001e0180c40e16045100a036100c9844030031018071134050590520141e00c030001f0b14030000201003c0114040d4840c41178003041490020f090061540c0b010422070b00741040a0020340340b01c011a0b890322043c1c28190b580b038808e000340c860309a85503480503040500c08916215103811408045108125040c001c120410000c84092001000000054000481884040c105031070041c00100310500080c850b1201d00c2208000544141003500003016603000400c188925003487e018240d04218000c854824080c10700342d00030036500301445050b10907130884c00031403400c0b07024ae14000010000503082c0c0b0303515070311140060080c0070390038505441252000d084120700c0e4050034003000c038078000800c1001c5aa4802d020040d880341c0d880c00f50340d442044403e8100005070200320b060000c2900e900050703196807 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 745280134 1250 745278884 745278931
    0x2011b081216081e07050a090e040305220b18120d0504080c1f0813050d050301030c060e0904020f03030d020d0b0f101209081c140610050304061a0306 66
    0x3d00901e4005903008001131480088213038041c0d02c5401c41c94900d48901c00340004660080d52a4003400800d15540140b00900d40d00c60020402d0580382e000c0c0e4694281c1c54411130700607544901c1181d1143c8018004204403c054030b1340b04400000050910790080c2e4a454100d0a01500c103200c00e000ca030000804020410051010410450701101d403000d948a030500060f450a0040100400f00404140020002000744000c0009070341c001e0111f070300d15511031401400c103034003c1c0001d45242c013420200040d1a8441c04a2110701e4401402e074000710307112a4207000540340c1551030243c0c180001e01044040d82000e101514043c0070855007c00d0003c1c104003441308117846100c1940c025032000325800d4081c2e4001058105e4a031040000040c50491030601010034081c804814004030414044c1010401240c0c208100c02c4086406004860715603d0411455000400000011510500c0042c0102d03209510003508007042e14188000c9103ca1000207040120480303c03012040f100b804408a00e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 745281384 1250 745280134 745280147
    0xf300d06051201060e0a09060e0d030e0c04090807060507020c130b09131a06030c0d0501020a121a0f0a0b12090f01050105150306010c0b0108240402011b081216 70
    0x301c002c00020030809040c1a0100040100105145017a03a00e4580d010100441940020481e160707110503070786820b0111100501034001c4410608161041300c030030f444e00380b6261150400c8070f507000d15094500012a501e00c0701070000100014154002c1c0411440c0d43c0d100d86100140003146001c0c00900404500704016034210084c1404001070041820320000842101401c0c090000c0c4c0600404a61b0302d80380003070314150400301c105420003000340d082e13420440c0c150040c0c25464015142d1101548140c5091800c84180f040708140b01c4032480440d64160601d401c41d61590500074003c4002d1075160142d041c0140d0000106007070480c1200704100007080309000750000340400704c000b40840e51419000030b055802200742041c0240f000804240b00e40e000326407201940d075010030140e04540e950303032005890740140300181480b51820701c4041c140340352803078070507100d15170584814004800616054607600360f02403049031100c1c001c00c440c0250703038103202c0010b00c81c004221000190907028040244072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 745282634 1250 745281384 745281409
    0x70f08070303090e0c04030f080904020a0804030305070c0203030f1606090507061404050604090e0309090a0c020706320c03030406050105120c030c01030b030304090908040302040e0f300d0605 84
    0x800820028400079403180c5085070100d07234102e030200101025a042010f072908c10440d030581c0c030501c0003402100c03164003d15014400c3e03001c1d4908001981d1002419203418100e440c0003503168204100505070b50f0104006007443d402000d80d00d1070300185580d90fa40885024000556641e800a041005070543c4801d00e00c0000203038056042c1402e00c0c020104606028901039110045d455a00618644c40100141e44064038010b108041d10b0401890000c003d01038089001c0060140d030b00007003220342c062a106840c80c40640d6440c0203c40c66544001440203440652a040ba0320420140901c0041000518092070154400013025490141007260a510300c1d0006a80c540081d0502c00041d503022404684c0c0030030030708010070481ca01ca00000d0545c8201d8020100761407401c40004184541c10003e081070328402d03241002014030f07011500341d440740c02c1015180aa44a010803815500301104c40c001c1c25460607610450202901030080142e400c4aa45411000c0d6269410081ca01d4461040040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 745283884 1250 745282634 745282649
    0x15190603051e0d051602100e04051008060a020a050403021207030c06020f0c0a060c0b07030219030608010b060c120c070e16020106060906120203090304030b091b0418030c05070f0807030309 83
    0x90074031380385c4010010b0541c2000c064416a240b000000c262070003404020b104c0c01e0010010000341c508142041e03054541070050080a1041000051411000380300716007000c2c0d02501d0381d50400b490f681c20003060214508104246000b05e180010015003c12341e0000540603a030080c11072080b50a074164030300504840b2241c4207445104007007101c6e0707400179580d140d4039030032444030040c0d5038400d0002d030003070320070030525205e605240c0022a0038203a05038040426102110000d01c041001e030010440e6030f0280d1894500d41c0d0304250851070b00640418000e00b1304007032101c103403200070b075549141e00e002031300450321304100010080841116960a100d11009410242011800103061250003001d023030001950800b0103a00002049010004100380c0b00110b9200c0e0147d40c041c90006006525442c80c260f0742142a070000d625003200d40782038042c0c004448101c840c40c203980501030724200d443c000001015030781801990300106403600300c444080d0103090b40c43c008154862039494010602c4485a20814 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 745285134 1250 745283884 745283887
    0x408060c0a0215011203051b030f0403020123161110030c12060b0313020109031502120c07030f050d140103212d09080d1805010215190603051e0d05 65
    0x1c040d500720200408120303054949291079070b0008e210301d040324400b071810352803e1201082055000d40808001c205581c400c1e60380c0c40c0c00301070390880c20006c1a003448502c3d03020b150601144c245010032500d000d600c00c2c01841b04211004034003001c14021a0078800c0d010010740c65543ca034511540150414402e220003903020000103180203040b00789800060012034080500d18001e80a680c03081540102442c0c01c480c105400c4001c025a500080d44840a0705064009103000079079011580e00982e41c550b50552152401d60010b10001c03280c2c0ea200c81301e001d080641d515800703098004218200da010b544144c2c60301900d2034481c0da0040040b07241d449480100700d040d00003044a1010042071003a500d485581803011341170100c0c1c2c140c944107015004640d542c4a003000300c01c00300e80e00c00c1c13a1000e245403204140030043c1d166401280c43e01c48524070000407400d541c010460464403d00c542a81c02e0012800140c0582ca907686c02d41020b5440c1c03500000c142c038440004100d12000d00900c070400070b060a00c603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 745286384 1250 745285134 745285139
    0xf07020112560607080d1a030a120305192d06120206162a050a080d08090118030e0f0d0b131104091b05060406051e0408060c0a021501 59
    0xc842801c030702c0e8020841d154034001e40d850b20384840c1d05542100f580b00744007985031045816a8402005002140c0000616003190310247c2d06020444850060300000403940740645844141c1c050180030304a500741c6580e5a0741e1b01d0203a880782c40b48405c0100c401042c1c3d80ba81c0e1614101c202100582ca181081036440c000c0100400400301c0c2c2110310123036042d00c1d596203440f40510354013440d40e40d4450143ca207022200381113901400791803860f0300c55042210340d84440e07078030b400520040e6002800307440301680c455080e500c10381d40960600e0740d11180800010400d010140e60020380b0322141c58040b40400c8031942800110f14000c0c110102008060710544881c12040e11494030100e4042e014020081c21210300b0018440141c0c2c0d1a8054280a04207001b42c1d029441c0c85076085202d0003800c0c080c4010100042090b240c880c04803003c6074900d0351250b05107030124114000d02103403150041c6446004100000e1614420b010080c410000f15011680340c22000001074181038000d0248401c0900c0380005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 745287634 1250 745286384 745286501
    0x1101080c090d06090b040c082e0e0a021002010209090903031015030b030601060c0203150702101d0d05030414011e020c010b21010b0d080f07020112 65
    0x7503444140044403400900080c0741003800080c2001500a09401030820801c018001c000c65114100e078400d000301e40313070104446c2090300143d1480300240c1e02504500c4a1001c5411550400101c50b0580000c0c0c50704104194002010346102e005a1310141c5d401003000340e042d1800080c22680a0300b0003001d14914030b0042c81340e04540302030b802141c02201500b2415055148290304c00081c120000d01156040d5071612300142400c1400b1408a101e40705108070900b003010030796180d80c0200b5030307500106041c0b03002000c000090032003111002152040b03010807081c0c40d4000c00c00d907529641242c8456540b4186400d003041074034401081c0300640d03810031810403400150040b244207c440b8241c00181c4032032207803200341e000d043c10400a0360b200c4820701c02c0140c0155110740801404821100810480b01445c00307206040c80e181c200a0400c20301485260740500484002b424414414541261803040c40c103000c504170340d15408181d00003c030078680346404401c2010580415040c82d403131456051000101c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 745288884 1250 745287634 745287637
    0x509010f0902030c01030c0909020408211303082d0405030c09040804051e060a02010507020105071b0605180a050d020c060405130b041b0806030c01050f2d0f03041101080c 75
    0x45490405036200340e542d001f24450780000c00039003840c4006541d039641d1200d0440da01c00013001585041d142c02c554411281c1e03041000c5407401166541808041480c0d615040d2860b081a890390740d080c0c80c00c240d05051441c040c89089003400c1c0e003585064075070b4100000c3c1458140b0072035120307000320158401e00010980f0360b010b580456400316042c000c904007441010320340007038003040d440e0041c2c00403500380096501904003d1084465600800040d07070341082c211610700001c14618011030030411002c000c01c01035044954424003444c0040c1c0742c96140701000d4030703080c2c1c1071000717481e1900022a0301403001d5042c88150641002202d0590609080400090801c3c0c0c0c1c6c1d150000071642e0302d11269185491343c0e0405496a08013215401c500400c582c0080d0080d2400c5039032031300c00c3c020308907181c50647c0140f05840c40c1c000703201d15407414000a21041e401c1030206d200d400c103200c103040f440c0806001c49100103200150f41d41c102c994490605203000c202c184190380070380341407184240821806000c07210 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 745290134 1250 745288884 745288903
    0x10f050111150a020d1a01110105150d02040e0610030b15010504050f03010b0301050c070209130515180712060515030d1404031a01150e06030105010804050f0d030509010f090203 78
    0x51070310680c3d0715080e0b81d00000384101e129000c025410022485204d01c40e4541c4603c22240a1f2100342d0728a0f10802d10303a00300c1d0030803202c05148020b11008440c40e41800c5202609083c800361000030210042c004181c41c0280c1241c01103403084140b00c05100b080f160190940d08142090f550701585010362001800b0f0b40900d000700f600075151416071602c0b9503001d40042e01040c1000d0700800031030034003402000c440c0d44600000d82c01040040f01180d00840350481c101e010381d0f00f020107482c1c60041100c4800e00e40d800907207500c40b81d01000e000300c02c00d007005100d4580201101860900754a00518224064800081c00c88800e20449203a40c140d135200403905403060102c40c6001041c0311096004220315015641000e01401c010990300e0f036078441c00c904258107a40706a001950501150001248c0c10031034102070300e41003d13040c801001607501502d41590058410000c1d220741c041503046081c139080c10781c404e040c0025103900500001c48400e00c14504c80c500c0b000c406104142c959000b290b03889111700c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 745291384 1250 745290134 745290163
    0x12131707031d0d1506060e090f040807020a0902040b0306090a093206040507050102060f1005190b071104060b1611010306080a03020f1614040c0e18010f050111 70
    0x140c41c2d9405940e50391030182207240d40301d81c9000c1030a1840b49550020200c6008007000b00300c51510001c11407511242481c4102071403c20703070130140d03219507549446800c01e1034100e820001810010659007041d002400c090709038035071450748030724101c420011514005400300038021300e030008850104440c04600d40000320b04015285180d01c0700c0751140200c010009851a007801810144010424007140710000c47d44240d084501ca5200d50004000000c0b00361181c0c0302d003800c6035000b0405820140e119000414048005241260b81c4804a0788107038844034040342d0b2020040719090403480c1501c90400506140c40c0c0071414a400c102840c0f0343d065501030007409101c0c20710b0603640c450380301fa0049809842c00c041940d2209035540340c060f5481d0b9a01c8090032403400783c40d41c0e08202c001d100c074621040320188121952060441b0050000400703411114000300b114030030010b25a0b86a01c10b9000c0440038000e01e4000d150324102680316492000e80165040203507444404002d1a00000d0002c01c80c001c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 745292634 1250 745291384 745291427
    0x20f18010905121c110a1103063403020d020d0504020315070c020609150415080105100f0c06062105010608010515010f09051905031b03030d0f021213170703 69
    0x3824005d84480340c2401c5200c1851244035100c03400c00004541e1007000d5a000d030100d0700143c440c001c0c42d0a4240e0031040c00140c00052803035605400700c040002d10a002190f0800602d0320340f44900720300607a8440c1c6610348580c1e485109100840c00c0030030002100e91139540c031084560403c40001000003400207006441140041341408d40c2d0364422280030754981128400c160b4540e5100650b109034280c240c405e030081114000006080c0c24038001807005240341c1e07510506404c28100c01a520341e10801020384640c3d95812003c510200b50744407070010411101d000152220040c6046400d44031030350880c45469050400b408240d00c900d08014004034001d00301201500c1500342c1c201c40c0c1040b9036100503403140d42142c0001918588098042c15590250240c4901800c815a1a03054244482a15405a20030404c0d6071090480d680001d5160040d010302500d4100da980c018410900709071001c8290718a264a2482040346102c60003d0480703011044904050741a14081e000c1d40c46001c42c01c101070034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 745293884 1250 745292634 745292683
    0x60a05010507050f011406240f25060209040b011d040e030c10050a0b030a0c290f040906060c080a050a0e061615061a0c01020f1801090512 61
    0x1c03e0000e10b000c4131100c0001c0190016840e07050720403900680b0050701680101c00301c0c0d4651504d0604120480740b480c503869103041c03110403082d2200e5000a9402054007802680c5a480410016401c0107041c069140561996140d6040000b22000b180c80c050521141120403140c041c1800c0c8841c1507198101d800203042c0900754000e03811807103041a4410310307015002030b5428640c0b040e4840d90054800d28010003551000400341540e60f21100409000050644020400e1400e8100c0004030142c1308400081e81d0f4840044c604210703049040c0c3d0850f040404102481b82c03a44034851000100700c20300e08a4107406040e21481e5441c841c400d10601000000039207a0030850007020840c043c00c4010b0002c07680c4a014810b00c020b14a600e12084801840b00510030044542901505050b90a0585040000040d04111701c9041d400030a220400395000e111049000c103c9038080c081405d00d80103900a8601c540c400102110b2254024034807584019160b4100d000000031500ca0480b02c59510820009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 745295134 1250 745293884 745293893
    0x40e040f050a02090406320f062107140f100c020427331a0613080f01020708091c0501060801020c010e030403020f060a030f050c03041a060a05010507 66
    0x8000300e0b03001c1d4101c10f1400c103010400c6400e0f8020001c4203507004680e403039085404051550b10403240d9210703442c5d030a035801154040c1c00303c000b000d4105400070030f40b400e00c0360000c0110506100c8021003145540010384c1c100030b04071700c2196100e00081e01b1220004c43d80d440c940090060300c0e005901d181008000030f400c5046441d070703900000003030746182941082050392054289000d09001400c480564200d2440400c1500c00400b20b10256840403864010004c18000070000f080d10028401d0b1107444140d4612958031403100618100b011100f60301d0002e07080003410342c030706407e0010800c1280c0c8100485d2000c25188002e03134545010450388c03c1e100035040da034180d40c3c004600c1400b9085510700341001511210540c014512848801c00038403001c0b85505c80151207018a1101a410040d6041c09415511b004030040c00904c00b43d00b4001080210903110404481d41182c6190703c0503000024842800900039001160b5040e000280b209890001c0106000c50340324804e44c3e0600001050013001c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 745296384 1250 745295134 745295143
    0xc1002030417030c032b09030801140105070b070503010608070f021506132f0c0a03030203070c0b13020916090506090d050102120417030408040e04030c0f0308061005040e040f05 78
    0x2030000030200d9440781886044a02810b40003611040c0c9030005060701d010310481b50240d58015030701502c40f0b40c1e0360307841c2680078107030800d00d01c421a040001c10418a00010000201d681c040d8070391b40d84951f1070398145038015001a201400740801c1c00700b041040c0c1480c5a0014112150890084520a8a40307503040441e4106000c0005c40c40094103205078416101c00030480e42031510748041a044800011108003402031140101c3d444154018489140119000790011030b003210041c17510101d41103aa841d038402414051743c4001c640c0496031305110941c44c0a10304944c00042945614800c1c01c0350500280a100c078501c00c481c01060007080500f01c56450205850f006500040213540d0307044000502156041d0442c1d0880f88140210680700d4032030300d01c0302600e00c00c5900c00d454034500f81c10b0000714400000000c1080302040016500140005c03180b4090440c400c0c0300e42c89007040c90900e142042403031740f00c0309039800c2003040610003048402990f64002d600543c1080041c1c20380c03440c50030001d041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 745297634 1250 745296384 745296397
    0x321050403200a030506130606060e012c09010f0303080a0b01080a0e03040513020301091107050d0c02211c031b120219090303120501140f0406080d020a02030c100203041703 76
    0x80d004000407c006070482101100d0024401d41c810841c036a1515000d60b15400a40d40160000d075403400402e00d01e00b892002101104402072452401d03600c50780016003124026004102412000c40d0304004140e000620726400c08245001400781c00c10b4180000c00783d910040501c0b10300c980f16040c2001004050084802803c00641002012409082640041d500c02c2c400e160a8a10380090020203503100001c0c1c800d40d66100d40030386014604264100e4071318415201c01d03603010f41036040c18910740348242c1e04544009400303009032030248101c4003080c006114820f0800305040c103240024100844c00f0680e004036100f5400c028000c2c80717400c0304e408001d00403007030030310b0410101590880c0c01d80e820130410000c4038403076901c945280300740143c60400d8540a215040340d100c1c3d031740f000c45160b02d4100540750700c0e220041d01c001801542e80c141d00e8541b5000002460140e0044801c0509504040c0985280002d00743c450344508521040002e51720322841c42a141c8120304401403902d02041482140c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 745298884 1250 745297634 745297643
    0x30b03190803040c080d091403060c03010b0d061e0521060610110105011e090e0601140f04290d0506070311040f0305061021081b070321050403200a03 66
    0xc070303c61b12140640b08074801d00482003ca40b600b1004c606602d0001a040d00c91081ca10b10f560459280c074200d0f041e5904040000c0b6000764407000c010441090b90400c00c4400121600e01c014031328940420300501100c0c220b07000b0b103003000e15403800000450004049410100c16614a410030611090840c1d50380f41205d112103955003858000100441c040d41c02c0c0e02986080582008003a036a00c2001d005c0310f522040014070354020720010010749006a0425a440101070454007400b04104000b8085412100c5e00175034070f5017400e080c1c2c00c4d2400c008200000a0038240c48008055400d902c929079103800051031103007059103e1022040000740079003a200208510072803800100d85a250454454504480c45c103004040c00c00d0005168180700e6004080080c005014030200c203644d12400b5a95011140386148d8103407000d005511114104090700c0114012035404d640c41c007503aa04016400050781c00d040801000340014400304c0c0d000000c0c440040055550200c0e00355100000c9840680147c0c4080c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 745300134 1250 745298884 745298893
    0xc0f0616080d0e0d0519031a0315070f02030901021c031b03050402010e1e010f1e0806120601260a0f081c18030c08091906030b03190803040c08 63
    0x2c292600d07000108440c0e003400a591880c4079090040320350340501140300d040f0f0441e9908401800307009034019007005091a0b500781c1c030303032001c900480c2c80c0c003803001d01e0081d00000c12800c0008881d0b220805030005402c40c40950f03d050304d0003000079580c98111005c05072102e104507050110f180031f81d01241b803440c1201380c21300343c2d8904070402074000c0102701d4007a4003107092a45004018138104c2032186c0348120304400b80a622088100440c1c040350403180c0c0206202c003440101001d800003005603810304000e503460480d1482d00b071090020307510384400051090740c4a1801031010540c00d280d20303000d81120310501300f019140d07003414925110440c00c018140704000464202840f03842070007401441c2100e0000c480700c40c0200c0c5c00c001200c454400703d2000d003681d07943e00b50009104a0f00300b103129014102e20303802c01e1180340c0003c1d0301d09001c59655000445403002001400e4041c0264110380340f08030040c00c00e001014411441c1012112030044c02c1e2880040040c2c1000500f1005001400c0300c44201c8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 745301384 1250 745300134 745300147
    0x160c2a08030a18031509230a050f0307050d0c050106030b151c0b060609031e07032a060f031b03021e1606050915040f03110c0f061608 59
    0xc1d07165407081001d44000342c204180f12005510312284841142c0e0720a00e541401034140640d44028240401c08803502c2c5d500c0003100050304043c0700070904084504020b49141807646c58124505100f540d121651a00144a40400f248000c500c0e80051111030804001e265518600240140401d0304010704a900420502501e141161119044020141e8048880d29446803144a0700580020b00030003074400c0360f00103825401d000c07020b0714042402408032404800c040d442c1d0031011183c44c08941469000c2d0724208280421185400d0b541e052414038140c441032440c0c4000382d02081c0d4040e805c140010155004801c0d4820382c8203a40f0b0700040704074440b41212071400100603501459407003551081008a80303a900007003d02300d459000300c0d000c4001440307005030b5840001e40f10083c4800e00901500d54400071301d401d010442441144a81070501e03001100385006480102140400c0303003190712142c071400140c1c4520b03400842c865811160076407500011840700ca440e41803403400901d15900032034074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 745302634 1250 745301384 745301399
    0x70315080a1a01061107051005070b04300e061608031801060f0503031218100c08130b0f040c08010c0201062306040b0d0207060509030909160c2a 64
    0xe0b0250801e15098446940e44d995904440c8504080c040d6000d68200c80000c01051806403100102d481540c109941410096120740382840011681500d21041002058441c070b05410440c0380002d40088103515548144a002040d1010b5188140c0c01424001003640d102c8802c108a28a00c690091a181d0f0300d24100744856040d080010f411086982065004a049a0102011002c0e25030180003913080041219a030041504003601310360700d022081d000c04ec055181800508403d01c04404003184a211860b070050841c0b4000301048105038404592100107030307003400000d411140100340d0006075115400c2c0007440d0320280d400400746600e85843c1190440d01904000c08545d008149407800e01d80242c046041c20803c505a5a0f01c100200405e1001c01076802c05400001242840141821050398503941100c0055485c80d15a50011a0f500703994949203005590151100c20950401501400302030110000d0030f00c02056130340e07000d40b00318080c46425280651a110001140400b0f036031100c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 745303884 1250 745302634 745302653
    0x4060531030f03051501120609020a021b0925090f120b010902030f012603120610020106030201200f07060906090602060103030f1b06110414030105040209070315080a 73
    0x10101c001c10100504400c101c0d00030b01c0303250b1140c40d0006411032134109034401141d090138500d68184581e50740d485e000c00d07038526510141180803020f0b0010b2180c4480f003006c007840400451086885060031108210b6100020a401d0407080304041110344d64041a100aa40b1b41c010354000f03c09054800704009295000300c05400d031481d0084a00c44490390b00e8000d400240c0c4001c407183c00143c1820001007120b8000b441460340403140d50302a81384c086150507016802d55000024410b1229040030500c03049241c007480d03a04442e90140020030403680f5560001c0d18410080320310110324100c1c40c000140c03800060040c940205294015aa084c0340c58500c0944066103c0c010240090700c46240410454000201d80b41030740d0b0561504240406007090454150465000d89205c2e502c4070f980070310000b2a140150103502010a051585890a040c0c1103040003000c03241940c0310340c3c1010248030150300d83c5801c40360004050f140100b03049406824404891143da400381c8038502c41c110b51f14090242509 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 745305134 1250 745303884 745303981
    0x903051b0304210f081608030f070e0d0215090d0f06020c0c010c080405100e06070f060506030714090604091e060c052a010e070e010f060c050303040605 67
    0x114141d401074000c2e032a14007245a0020309595080070340002165170000900140c4a106c0b4103039101d00015500c901d03c03500169640c00c003107a010310a01c00b803590881c0c800210854107a0b0310560003040c80d00020303504002040840d9040000050007455511088910258150407040c481d484010074540751000307501005000c1e040c1e00845040e00c1041d0b00c41c0a0440b41640c20002603420b0a0422013080304c441710f5508810b052000ca10341d0480642c903410040d20045000b1030b0720b42030640041c2084400e1354401410b2034800d401209041c4000c000700c3c6036011103540700f43d03100406961002c010030020004800080c050702c1081d0f840511200200e002c03412500e10070340c0e0910003a420726900780c40b80e00603022072004994907012101f0000781c1d41c048044075145420004030f02c0c014034a500504221503a00403003081a03486005002d903141482641c0d00404031441e080520301441e40701c0c191240000362006042e192500042041d583e0503024081c440c2c1340c001c00300c40c90021558040c800025041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 745306384 1250 745305134 745305149
    0x6130e101802060717210a110f160203102c0714040b03070e07020106031106040b070212030f0d02093c010c05010c02010605090a060f03060903051b0304 67
    0xe0024207030320440c03202850010b07405841242403010301e40c2c031040c0402004080c030030080e406200c440320304044080600d82c20108510105405d040c0804031005a5100102c21041e01c081004a00b00d035260700002c4699004642c0c0001034524a14070001e03040c00078040803c0255410449601181841c05000807040211442e9079201d040001c441c180c0c40d4011441801c0c0c000c043c40e0301414050130709404c1428100c000400b940d1400f03881e0803a40c2c0200034199030035001030f0340d200c10610408c5030800c1ca50040760f00c112851400c161500a0026092040e950024059681e150903400b40442c100b00342d841c0d0b03c054440b1036071602800003a2000940080c158140b09907140c0c49851600102120341092400c0300070307092640240000345800c812101318102074100170a00240234007266080c4140c00d0400429400424040e02c1c020820a003a000540700c4950949001d10800c00c2e00003000307009044079031068002c074140000303080a0310103000c6c2d10b0030080710841707480c8800e0306a000031005109031840c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 745307634 1250 745306384 745306391
    0x9020d0c02100c020304090e0307050a08130e04050628020a1805180a0507020f0a0c080c010513060f0912030c060513080d0f020f07030215240906130e10 67
    0x1010448019660f2280c1404050b0b0401c00c130500c00c20b05550400780c1108c21601c1100d1900c0d1450740c0d15071a000301500c09440102001c00d440c00b44411241620700200660000c07151241001d0b242c040e11888043c1c20308c0e840c65428400c0705140036030f030b0401c0d030702d0000394410441d2544800c48000d004c9000f2021b0304403e10000c50b2000c102881d02003242409010b903085070314000d540d4034071381030f00800d4098a800151b228800040b9145c0404100540109104404540b55603103480d00b03891410383c458502d241400000e0151440900700c1e4130718001160314031f19001c400e0f81e509101c10b680b515855049501000071001c2c4443c141500722405086031481107408020313555034860f0520707003040449c1004004803010001c0c0d04100045420000c4034003030075100103251000d0b410030100e0980c01408205e008d038011036408044066211a06a84031892411144030703c4900520740c041440001d4800b840342c0070607000b00d44241c4070b00d00344650307440780c0700b00420084001210150703031350b20304281c402655400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 745308884 1250 745307634 745307653
    0xe1203120115020318030c040f0e06010f030515100b0403050a050f030307022a04050f070f0302030403120e2e0515030c090705090306040f030e0a0e060d020a09020d0c02 74
    0x14401c22021008900da4013031800e183e009429550002c400242c006e5141c424004a900d456440d48200c545800c601c50000500f1624500b545041060507400324840ca8001e0004102080d004a600340c3c2151902140b001d0036981c1d0350030b410320350800f034000c00440c0c030000c10044100800000e01042e00e40c0600c01312103800300020007055581c441200c50000581142d6040010600307829041c0e90790155021140241000384008201106d0003120b42c002d60f598440d084c40b0390103400210241e51500e0501e410342c90761515803030107052030310030000d000c204030f5445621401002c014841c03c002441f0620540340c40451080d95540c602d1200402032414a2412003c01c615900c11180c0b099404009405010300c100e80c03208200100d0401000c000c14400d04002d41000da580a01c80c2610a80c1301d0358005401100c00d080041840980350340890041e641d9041c113210000b406405c103640000103c540003d902424400308415180703c0c1e000303812560003c95154414041c680140041c0441c0d82c0c22101540c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 745310134 1250 745308884 745308899
    0x4030b09010b030d0e041e0509010b180c25050a0c08070e0415180606080718092409020402030901090308130c06050a17280603210e12031201 62
    0x2013419501801280c100304003401c01e4142508442d4038188207031041c0c0402c04040902030142c0e0401c40754980e181c4d41d1400f1002643c0b13070a5040b05002c0d846401c000747c507860310700b0131440d25104a00d100101300304d2000c080300c00c0039180c2c0c40305d01c0354551107401d03951415005e180820005845001c0e0790018021400041004511060300520498001c114882031551407902c0d00c00074003010240e07184240a45000e500407030042e000d0900200b103808024500145010010380000311001d1200b03c0d410705045d0b0000c08520f03c0d007190200d205151042c04e85450124400d0001084110802500709001000b0031030602c03010b42c0300b81c82c107030300a49400036980da500103d000c1050980c94014402c036402c1c1420310000c0e10a0f4094031100348903013040700c0004610303820320f440c0c00740845404c85040300d42c2c0007501c4d81411038801c0b04c9901c54003080c1030001038116910407402100756100c003174603840010b080d51891440b40360080c00c1b240014000554213902d803440d07691641d0008040d00e982c1c07481c480001070140c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 745311384 1250 745310134 745310143
    0x61d010f080d08060402130b0a02030a0f030603121107230405060301020c07090b03030d05040809150c030f0d020909010e09010e1903050a03240302011b020d02060c030c0304030b09010b03 82
    0x11042e035a42481554405003040000d4100c20b505410700104030328003190214034000101031030030a41d0011034407110003010041003c6421580402011704004e0100002501901303003a02c40380b0300707090182c00d50140c141094608000755100f88172456004900004422401240d03241c100c5068806204983d40c0500340341c05d0344111281c81e4082c0e03008000400c42d545040d444103031540c000038152440d00000c60340725000c2d00c0701901d068844003c00145d43c0307018902083d03e2001c405044c00d4090502d00f0740d420461712070003255071030500312000050078500a9407540c100c545191300245955100e5860701101400d00d00c0840b40840c0c55841c1040d0710407020000036080016079a183d8124100b0141c83d030341141c154010001600502d6100d4600c0007411188100802c448605940080348151840c0001445c010440018014400c01c1050f41c0300035803540c0f00c0300e210740da07010f450031503491556880700c174a14801c50303012a0040c000401c0203c2000740118000e40150540381c000d200303030100302c010903440303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 745312634 1250 745311384 745311403
    0xf080603070b0301030f03050d02030712051006090b0c0a05150106020d0320220312090f081b0d06020d05060a0510170a0605090c091519050904061d010f08 68
    0x80c40c2d4148010030015040d1340e60712440c00d11a01c2d0560800790703032054402c1a60010b8580d200890100074414540c08841d118440e400035900a034001030349d140410150130000d190181e400b020100050704000c0c01c0c01044502030b519401822600a0a2801d0b0008182d80c400c2c090403005000701aa0100c40320710900404010b404600703000c44040d185400707400d03402d030700508007031400c0101282d00d650755030420301c040c100841c041d07201e0610703034010b4000c010401e6007030317810900f00a030041c042030204103000114440100310078040b83c80b50758200d00c0054101d40740404002d080d46d000090b8600c106000380c0100b8040c44042e1003240c441743d02d450820046451240c0c0b064000341d2546803081c075690601c0010354100c500381500240c0641c0714000306034128070072200000450303000a49505503040a00c91613074070010080d6080c1c2410030750032000528400c1801c0300f0041150100d1000c6403035650794805801001c3c07021020400540400420041c0368007407190f140304000c10100029030303a0011451101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 745313884 1250 745312634 745312649
    0x306050a1103190c030b090a14090f060f09030c070308121005100c0204020d0e07050f060a090b070812070c0201020d0302090f01080c0702040513060606020c1f140301060f08060307 79
    0x10320f948145128402801c0c1c0801314405c150721540880e10355240c1b0032844e4010000e4060103e08401c180c6a40c410380c06000d0417922107584480c008000420020a8072038004e000541e03450381513200e8111552450090b120724410600951100004100c89500242801510b8605404c00c543c2c451014001d501c1c858803c0d030740c020700050004c075852403080342d03810125071001703000504120300840d600040310781c00404030240340c0c84480c050110b031800c030a6064405000711080c900e0218842c1c1e0090021030148501c2c0300c0ba1038081480001c111966003500c00d4101d821508030343c1442d00c1000109108044402070f409070161400f012103541c0300b8001c503200041e014003088c400410300c400440380c000d070090010380c0c07201d0300707005410042e92a4017959009808071400c40c0d69000440c100740c0120b401c00c0d07002500390f41c8810f40c02c845ca41c65069800b07095407041190400d200580035401d03584124521134034080c1120000001c0b840300c0d003020f081021041c0f980e80c0e5400540c2c03204103265480255010f203c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 745315134 1250 745313884 745313911
    0x9180d02061e0717090109060f24080d0507030c05030a0f080906101e0b070602071a040c06140705070b04061706090a0902011103041202120102180603060a030c0306050a1103 76
    0x8149102c403044c0b40fa049181c4000010b0159042c0d12101e044030700000b681400191150750300408800307034a600c0112000d0f00c00c83d1100701c0c0c0c42e1440705592404000741c800d00340113002c55100b003858080c00c0400310701c2e6044400d50b80da441c44804003c0984030707a101c2e51004140300c2c002141035445c000030b20a03c1507506c00081e01441b800d020340d80c8c101264030840400c90120210020401d90400006000715a104100141e200c240d10302e0521010341c0006030900d4500408030800011800070039080040baa11810075109458110840500d03904c80e10310054120b01c41d461000400722000340082045900650b214901d803504501e40c0c10424a05a64103684002e0301d201181103800320b5404154900c0c4141002040d40408020503800d507042640500f031000c04403410541942003204803074664002d00802140307001135110b0b07507001e00c1f4444100344e030003424088001400c6468001c00000910b810824030f605070742c2d0b20724002000e040c044502000d401d0810388a40042034040d0243e130700481c130b10301c51031303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 745316384 1250 745315134 745315157
    0xc0c0411040915061b1a1e0f0103120527060c10150603060b030f1008010207141504080d2004030503090103060b090f09180d02061e07 59
    0x400500800c5034a2404404100400564a0b640344100c1e14404203002c048503109103003000262000428440388003003e41e0302c40880c000a07400841000e0010035080c16580e00340c65007258846035040c5407103400e280c1d00a14060010300100000030382d040700c3c4145540d00e2058051001203449004003103840d0302202c10b404541051207009440941001006809070b410111b52040b602c0c40c040502032251a9036076612542900d500b10080b400d070103082141030900209280c01c040c191030340700040c0b0140407003034028041440c020400858100500300c0000941d00c40307515042106655209100040c414891000c640e1814682480090301c01e5410441150a04407e80e0650b00038201601031140c001c00768400f03101501c40285c010b48007440c00790000f0b548611a590001d82150300e0f5821102031007009004100c0c01d581c461000070140c817410f650120a81d01d5520800c50f400c1c10500f00304034107000b10024030808035400548140300e0801141c1200310084000c0500043c4401030300c40354000358140110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 745317634 1250 745316384 745316389
    0xc3333030b09010b1906080714090405041b0602070509060a03020907110a0203070608060910050a060e0121090b070327020d0f0303020c0c0102010e28060e150c0c0c 72
    0x30b03070050342c0c100042a01003a640018054100300004402c04540c1c0e403105101407980075980ca030f8024194185280c1c56083c0c25900a624090540341c0740c40f40e600c0d0b40016042040c0b41c2c091064140030008800d1030302e40c8428000c1d48a010501503130340140782940c0003c01ca450302e00c43d101c04494002d4881000394554800c1150301d00322003244160180310b00c105060061f1401c00c14400140a2541d80d442d850a240302000b40b240c00140a404881320540707814806039680f088050f00700e500c0c1e402e100c248103d40d40c1c010390350700e41000301806500b01c400100040010480e044070012500c50300034880c60341c0d200c079000d0f07003114484450300000c80d0303598050200400e00b503004245683e000906459040381c3c19500c110340b00c8000e074000c900223a004510a14a03010030041401d41c22002d000070b101106d40355410b80d50380c692003004150b94410341c02080304001480108180f416030004c00c10302404850207111a903901a00e480c400542440c100010228590042940d1050031f0500182040c800702904 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 745318884 1250 745317634 745317653
    0x5060a08100b0c0a060b0301020910051c1a0f010f08041b0e07030903090f05090604051b070f020108070c1505060a080d030f050105010503070c333303 66
    0xe8409001070009000c10703602c1c0344401800d291210000280042d00b0b0324501102615402004140645c0c014080100d9030b541c0c14a004c0a16116858040e0b240c045100c0c0d002a2a000800030303401c158948402c2502c2c48042844400d4502c4007907a81b02410a0700400448815540c406003400041217440131400042881d1100e0711200c01c0480e10b0081c00f501c502c05003c40b0501901c0c42d10200355610050001c247e007040840b0300400007c0f125808080c9400f000c00c1820030700821040c0300315980e1000138601d101c43c1d003000307241c2171072000c86686a40c054a801e41c00c03640411001d0f40810f0181700000c8500f88140c10090403d9403085180b4000100b019042c005403001900d41e65004c0d100020128075a01c04019030302c1c4810941d5004a004246018203000701c1d041038114904009007042000f031030715004622030214960101c0304c02c2e110300b080e0b9842c501a00e190003460545a10104058004814a401142804101000380b044805641f90300044031040403483d0700b032540c40b4075000c02c041080c450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 745320134 1250 745318884 745318891
    0x8010f0e0a0f0f020d110a02070303030f0e070b03010f0e061c02040609020307120b060a020c010f0c1b211707061d0607020d020604031d0f180a0e010605060a08 70
    0x12004a407490004282c00d054070048681080c80720b0b8041100540c0400600504681c8402e044001c1d00e8420320030f00081d1201290300015082c162900780c003041d04c0c0d11650054030a61f400c4400d90300c00c141c90b8041e40410b68400e1203000c0125441200100b820f4802943c0b0f507000d00c03801000d400c10740c8801084400178441d003210680c2e010350380d02400521410a400251320906999444a030782030036070041e1504480200c90464000c04040c40362007040f50700002c00103110902401e00b90700c00c0480312011030b01102178102c014060806240c0e44041c1c5a8561820800da0b1882c1081d0119902c140300e0701c10f6410b072060005018200c08880e0003845d440c4250041c40311b680190008148840001540740d02e1240301100e100d0180d00c5a020410a994144601c5941c503800c0c0c8094542401d003a1070007001a03511704018049000348255108069440300d03111040c002024110506001d44000c0184201608454104e01c3c035040c0f24405210032010b11030702041c7e8034020f00940c141100c0300800ca42124006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 745321384 1250 745320134 745320151
    0x1603030c06150e0a321b070605040303060503010b0d0b150307080703020301141e1518040c05030d05070803090102040b0c060103060f052403031b010e0c0108010f0e 72
    0x45a82c109003103550110440600041e201d904824203101040707004943c1c01c1210781a450105401e542c1521303410510300c80b0351400e080074800352501e500300014090012400c0700c86082e900004c40500700032907600000d00c21802070f201045219030320410b05080c3c03001c0b00e181c2c1d58465203101c200000258074106071a000340b45c1d0741e0300c800946e40300d00109240050a810400180c2c1c00b2880400c02c41c40c0901520f0b01710600204106020f00b002d003254104104031400c1b45a200b0b451500198200f00451560a12a18014284507411491110808008106a5099410507001400420307607050000d081038a01e686942da070b0345030810300d84980c5041d4001501009141d50200030002e2912801c002800205010758050061540b540c0307045012070f50305045400225091004014040c4000d00c1403c1602000b0003001c0c4081c040980020308500c50f10a80304105070b02d18030b100030b070350700c055202c03809461250382203031b40d190080c100644401c082481803400160318000180080b40541d555160000440d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 745322634 1250 745321384 745321391
    0x901080a0c0e040c1806210c05070c0605030a0e1b09060a0515040f27020702040605040e0a0303050f060a03140c06030f0f07090e0604091b080a03111603030c06 70
    0x650005825580e551040900058900285c584480c000480c00ca009040b0380c2041c07010700980c3d0f421070045d10042e070580028603540b0304c0c55010303250180048828440d03000f9201c03400c85482e55009001c83d0010b40300c0075040e40ca06400d252080c0b0b000600100f01f07078412041050111700e61341c100007803060010702c00d54100318070030800206c40d00d41c01c2c00c0a00744c0c194040100e072501d0800e2801000d0702c415601041641c2201c909040070341c44008552070b00c85c0c0010201590b10200c40c00030501501c91940990f03005460844074003450640818001e560304d2107503a05020b281c50728144881e00000c140c800c01d50081c40301c0b40420021f032140561320040402c00c02a0380b1030f000300800181c1079030000c665154445400c101008030604c6800074980d03101903981441c086550905c0347c0c4107164170008102d40d019560380d074140f0b42800a140000c0008101d03089640d4109034940d250140c07070b2201102c1c201c000c0f0319000310b00641b641011500d188a81d210005186080740b0303584003100d50311039050041d20b402c0d50b0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 745323741 1107 745322634 745322657
    0x30304080715022b050304062009031624020f06040c0626010b09030304180b10091a07031407060b030f0a03081f050d150b060901080a0c 60
    0xc131071418649a0303135149414070080c451026100c03440c40200e5008000c5070744040051810100a4060760250f0310312005961042c87c0e0750181c6952480302c0c007541c00007038245052448800d82640f04941081c4101030246082420994041d01c01401517601446900d410201c4642c420a40c1a41d0f8071482c00c8110303000c4102001800b591040301c200091100da41e035000c006a40181221858803120104060300c2a030003428200501401048401c0c58910000d0140d20014211080006800680c90850f40720003908d5008203803c4061068070a640d15650450780080c04031a803144034005100c41740300040514100368021180081da00000307030701d0b0009030300240c0307950001081141c404070100d40d40da8001640c08181c200fa0780088180441e4028400704509060101c000881e04000c240d000343d05009040c810307621800d000ca031031a00455644190f80d4070aa010395914a8005003c41 = true := by decide +kernel

theorem cover : BRFrame.Cov 745143884 745323741 := by
  have h0 := BRFrame.cov_init 745143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 745143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 745143884 ≤ n) (h2 : n < 745323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
