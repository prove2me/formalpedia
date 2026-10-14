-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0691
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:10:42.574853+00:00
-- url     : https://prove2.me/submissions/af07659b-d094-40a0-b4a7-e97c83cbdbaa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 124100719 ≤ n < 124280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 124101969 1250 124100719 124100747
    0xb010618060c05060a02030c040305060109020d14090a082808271e0a0804060201050f0a0501060c0210030f020406030e0d020102130b0708041d070201140c04140609180103060c 77
    0x1404085c1c46044000f000b81d480101103981003001040000b000500810850b07000b441034520058564685640c80310640b0045401001d000e11910144002800b0220307501c103045074031043c912390310031074040300180700c0890809100346a8200c481450078660400807042c0300b1f0581b1540002c8040d540314800d00e01c1803240c1000d03100381d4132a84480c00d80341d50003c9c45180b80c0c1042011660242140c2da5402e40e0303030f4425006680181d45400600c0801d00d8410042d541044034094244620340c101000200003284055000c0d104410a030000fa480c0c13402544546100c00c103182c02556115120900540030300b2800707400c80400d11445c401910385c1481032080d90701822034400c030000044d1400c80016aa50007040e001e81d51004c00300000a01034140c01c80c442c01c0c101c4282c01140c2107140c0448081c0c00c440c3d41041c01306c069002d180410141881d45d03004c070350030b88600c601e04a900004160219109024442405030007040231085101c0c41007504003202d040324460b001c24006201e03668000c4445800d44012 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 124103219 1250 124101969 124101973
    0x30c02160b0a0c05070f0f06030510050f010e24091e0a031401060815090d03050108060712110c011e020f04090c050d0603080a0f020111070b10030b010618060c05 71
    0xc540c10043c030542003000d5060060b800c545e05c55465a0200c00401203d50001040c1d412840302000419018024958490b46041210802c039203800d001c01c0d12250104030003410010030407a422042e90320060881c8520a17080407005041c1c0792201251400e91040303444a12603502d203400c0c00d1045448480003400d0800281640c4e05943c41d554500188202c840d0032040255242d1b0781c0842c07070300c004100050685090600101d00c60524413207031810043e0178240340d010141800014081c1886c0000c0013600000180361102c0041d8049062000130910400c0200311002d00040c06103103980150020380e00c420290b081e0480724540814440200e00c83c04c3c0c1e007100c001a0a00c0100102c2015034001880c581250030468038209101c50304c4000c036003040d0801c5460300d4000c202c0203040d65014003084400d0345d640c00204100111980d540449000f103075401000d4a5880000804141040c0210342c021070303114103140000d5031292000b40107941c2e442e80f880d0014080c0d501c0007414500c1781065220381d0340c000e00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 124104469 1250 124103219 124103227
    0x112110307031401121e1403030601030b030a0203070302060306030106080f0303060306070206040b07210510030b07050a120507051603030c0201052511010e0a0308090d03020c0312060103150303030c02160b 90
    0x14903400001b07a20340c1e04820801c00b1280c200046403421108084c00b1100c200555503900e00440054216000c190390f4600a41c460040c1400680300003d035041941d070120b407043d440703039140d0300080d0140c183c1e034001d486a8042c0d10b18070074000d40d00001071401024224183c0c1d0980d03440c00350890703035400c04444c041c101c0050207000c1400e40f4090414100100250750115010040c0e155400040c0c0318141c0740c0d80565000350504005102d829000c86801c4860b910301146010410070b002023640603c50036007a81503a86601241200740a0301c1201c02c4550318226848064038681000b40090514405103070255080c9000200c2090510350841d00301d510045550311482c0041400300c405030f1046240a801d03660b00e00669a00036401c0090300d0200e0f11036036400800b443d0011415080940e443d825506050061000b03448280307000c82540d215103000015021240d03510001240900500351038803203480c07141c0402100341581f68114014000c000e4003110200c200030516141000803610410000b440144 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 124105719 1250 124104469 124104473
    0x2070b0f0601120f18030f0f0203161707020418061107031d03010e100c1814011d04021908090d081b190306150302130501050702011211030703140112 66
    0x307070000d20344c58103411001031008101880c00a06600c101d10035808600460310701c10046c0c0d0320810240e91640c02d44041c0d4280500c49441c41000010310300020210b9450031016422184040162000c1d681c0080c003e100c1600c0c1101c841c1d40504003110281c40345030914a4000c80d0840b0b040460b83c2d100e0b45035440f52159800b11805a108a00003001c556240d5268194606c40303090030032010366003c07081800003d00e1042400041e1001400c44401d030800e1401c021304200d812410403140111590030700b003041440800c4886105042c0101d00c15a52040c400300720042c0013a525032542c2002030244c1c075500242e889850300c0710794401c0b5005006000407260400600d200d80d020b0140c42c00300c206c03911042d007000b045031700046029880c0701c84200003da03540c004102210325006810300031b018609085240c501c03414020504070300303540905810f00400140400031079214946138003145c51060010407039080e04500ca001a40c5c0140d42c8034000a0030040300030640c008020005040b101c1c0200da06020803c2c0da = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 124106969 1250 124105719 124105721
    0x2a0405060d0e070306020d0e0105010506030703020f0d0e070f06020c09060f040e01051312140403030e150a0c0c06090f0509070516050f0d08040503030601080a150902070b0f060112 79
    0x341e000c505007900c541e03a440c0110710410507480618800c01016803200000751058084992452030800240c0c100350042100c0e84800c4120703a0840c0c1c1e00d140150780c0e0104880202e070715100783c02c4541d003c54601003070b4601d00c60000c81c1d8030058a100b41d9551401a9440718200e944240c45d80308039600503c00b10109180340341070070708130000002c040c10114491807504041402c52b2021100b41c2030400c00140c52200704407002001010407582401c1008089611082032221401203000c0102030140702c00101409075100b400789812120003482c0140e5645080d0b5008008289181b0f046a01403084d100205080c1d014014003400d46114084d18002e4034600000c0084019028045400b0b01c5020030102616240c83c00f2038480b03480c0070301c0082564030303001142c007850900250484410051407405000c0080d101008680d0001b90902c1c3c40180c03a10351210680050075070314240050355032000380c009914211038002c2c2079103d000b910008500da46060100c80f840303004513005400240f002b42c8d40441103042d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 124108219 1250 124106969 124106977
    0x809030d0903111002120a020408060a050907030b0a0e060c041a1608040e040b0a09030503040f0309090c12061e0e0a0e031c050a061401050c0f03030c032a040506 71
    0x10b45014507a01600580207804e205000d01e0b100c0c0103540005092911034008144150002025007045240c203203414611510b6079030107401150761076220408201d20020400001c40a1a0000c030050814140040307800003c0480c402543c0d028003c4000290100ba88041550201d50b1001020180c0108108a603242544203000c01d0216211b20080726003c00e80c444060409007000101c0301c407440c1402d0510052645000700a00e40d1282000700c1c10002a1b80300c03090340d42255010f0030150850940385425228000710303420a208003403404c0016030a07240e00445040c01000c00e107104000080d15007400b031000c9510301c1c00601c170f051410380c0108265107861004940c03016034180c0008034070b0134081200342140d00100c01c00a902e640504400d04070400e0b0302c12a6001103181c602041070720310b8101d4180000e00c8911896051080105250701c109805111325400d120000e0240c81c1c0d01e01c2c0c81100a15240c00036116000342550011130300005c00303102755480c094800e40b0b444150401d443d06007008040c0d44 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 124109469 1250 124108219 124108223
    0x6030c1203090f0324060501120c0201021b010c0f0c0206030705030903070602070308070e0d020d06020a05090612010f051017150d03030605191404050414070f080106060809030d09 79
    0x40d016030000e00c45034102c0f050006144030b441c1c0c1003100c004117a1140403030b458000318161400c2c501903040295a0704100d4052040c03070091004034800200041c10381c02805000340c0030030700644031646450350381c406510502c0f01d0b400c40c4c2c682405012001030120342e09503280100940001082001c03401e401e000b107000c1d550041081c0101d03403901c000b03541d40c0d0060fa00810340444c00b04400905200185030041051984143c2c107452511011a06400194545032210320180104c0c1c1d0015201485a2141e8104c031000381001e08100e507500e44000154000410074414524480e40c41d0502180d6450494202c14041c0d42c140d076544038000383c410130940c01031000b524240e003d045500381600d45884c0d042c03541d5482c0d40a9200000c001e03207010188100503404a001412016442c00148000300c0002d011009024065031b0005c0c650741d407482c104141e03c045071015449480b807948001030707409082c4204820380d44518000d03c04d40381d62312019555000d0903150804250000d0268101e508074540c08520018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 124110719 1250 124109469 124109477
    0xe07051c1110030905100216061e092105070b0106110c04050906060a0503011b12020f0c030406030c2c01020a0c0b07060608070b030402120309150a030b0406030c1203 73
    0x20200d0700007494100b01d06007007030200e9100c01c040000d001c030501070a0b030307030400411003036140c0641010145d01c403440642000f400760351385240c110718403c83d50984100d0242c00b05d03010404110b017070404110074101d846082080381d101c40001c100c118481c1003582c90b000d41c000d140c429103908140c419554001d0806840032180700b02c8400c3c4d101c66a5074058a8040d4000001520f505c0c00e00300d00f402044480341c0c2016000743c3c100707448940c015401400b5032400031040c1c5400807080c9086d0b0240c402900c1074050383d500c1e46401081c82d420b00c00012009008840c40ca0700c0c1044600200b00c030640c0c040103102c28401102c000452038032003458440c003028441102c1441501c4918130266603140f18034059801030060208003207a04401c101c1148204000703030260000030300b1124504559a081c611005100a00611500f8201c0440010401c10303182004401444841c9035681656441c0007500024581000641081a00c113003900703292081d101036980011804400e103043c4894044201c07100b101c110104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 124111969 1250 124110719 124110743
    0xf07110307030522030507150203041d070810210516080616110715140c0d1d0a0303110309090c0c070f2103030605180603010e07051c 59
    0x8100a0004100403803103925440c1c2c4072a40000300a0407600d0301440703d8104400340105001290000a8078404c94904243ca048c401c1d032039041c00c07401c0d4081c5a01250800c502000c0c10700d9890440402c0b1440742c1c0301c40e43ca07001a6981e1b0741484103001000c1c07254826403000084103034211a00310420301d010900540407500d050300510300f4080446001c0d844486d0f96001503040c0500307851180d29a907080803191500020305101c890300309444101c68401d200164400d045000c031024014800003070980044200c0c207072200302d4504081e03103e000d5584800c00050341a511030705410304210305100c11903c0038020300b56071800c558090b5140729100c40f148000b031006200380034850b0741c1ca15050b440384090308101601d4104040030355107010700f107411080c10822920414840390611500c10075408a14407007100d902441810240c00034292a00300540008140c840100d41710003d000441c000c9030207038001c010580602d00103070307114031940c0079942d40305c0503000810103580280580800340a01482084200c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 124113219 1250 124111969 124111997
    0x30709030308070c080c300d1a0306040303061422090c1205011b080708130609080f030411040b1c020604121202010c08010513020c0f070f051e01080f07 67
    0x3031500001c00980180d44601d030141c100b10341501c004110910fa1540e800c56131241480d20450500810100481855450090489c416812100b500d0783e0113010f4141e850703d081500b001006008907018040c01260101121026402d01c12200115404400d0042101c00781030300c1c03400e028150305241541c0c04031041002248020880c45284581d6124030000a90000c2e207020b01101940401100d0080c04080b03001c020800c0e0b0000f00c0d072940b02000701c1d843c80c0d00b41d0142c03601348020315211001611540d000310b01100a81c03031040055008034020718903081c032420f12504204c1a00c4403103c03d03d402080c008000d1b2035052000c140215603500c02810130f8145a00d0311500d07041541c403000c095407646081594003501c2d0b902072050b008030300e1040c54940002e60628011800240e841e003180d140044c0c0c005503070b0001050a10007040303003401e1030b03003591115941d4903110030843d40240500c0c1c0c0306150341f006109100150b00b0004984000c1a12080003070740d99010083d4200c0e000900e150180070220304081e003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 124114469 1250 124113219 124113233
    0x3050c010f0c020705011d03070611011503060b09061005040b0708090607050703020a0e010e1803090405070909060801140a11040b030103080403110103052e0e0109020301030501050705030709030308070c 89
    0x99080003d80c0100340062600c0b000424100001c80440c03e000282801094151004502102512960709103e9001c4201c0031950740184428a09140c1c2000b07158004810020541c1004a040c0340172a4852810b8442004001d0405403244820010400400c0108040076060025003180e0740600e030712a0800303d030b840101d20349074018903080740d054000f00c2c004e20440c45c0142c41c1074040e01c5d103100000243c1d81406182c00c00c501001e000f241c001d204c1944040d400d18000c1045600c11903002d8030a00c07542c14012005040e19845001d142103ca081c103401192a000522858100844a5084080725100c402c42100140b800050681e00c50f001000086255001c480c001c5000718817401d107035550b491a500b8003206403000c6103074a5040504203800e10084194001100081e8071580c500842c40c03060345220590ba1a601d82c0c09050322004c1c8100000e54490294007071812280101e009000d81c0e564114111060b220486011010403031a05042c4082407203154130603400303030090801d0240050076441e41c003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 124115719 1250 124114469 124114481
    0x1501090209030106080304030803240409050705130221101706060102010f09030806011101024003020102030307050c0312130213060f0315060e091515090403050c010f 73
    0x24200580000e604040750800b407040b80c0041c0366500146040038156030b11031055100c041c1c810b0401418070005010001c424008045801c9030003003041000d22000d140403511540c46109003842428465022403584031903008a801440301c81c507040c0003240302d5022130800c1e40d4010f0704825130031211010104940f0523110000f1032400304900200940d241c08000282034450f41441d2400c0d03681082134213000070b44c00c1201c90740c00c001e0908060401c1100ca9070b0740d83c028044c01404003c0ca24582007100c10080c1403600c956210070400c2c040640410028803030000c0741c2814070000307005178030420000e490607210302c0140c8502e44001c000d40380303405c0d420401401e0654040d00c02c0c0c03003203241c86440b0700114907010080700c041c0c1031001001d01030145010503014078801c4174440605030341c1000b81c604803041c2d078951100d00039004100c14a10035040c4a1039540e80c9008440c02d0701030703641c245000314102d07d1075150380c80c4400c80003c015451940d50b6903011035042e0071054035800c056407220403407040c9071258020b07a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 124116969 1250 124115719 124115729
    0x7030311030d1410050109030308060f030a05030f0703030b031c050a0c0512120f0f070509032503050706080c07080901030b03120339091c110414060916021501 70
    0x1078029404d082c840425456084c0e0710103414014226010000a500800300c03581c03001080b1400c0020401c2500401d040c2004681700502c580000240c1e101468240030144c0030440c040e5404000d6109420103050740c1304000443e420702035040d44000c002880c8100d00402110210749401d007401070b0f07596a494036084003040c5d600d5812401141c8050191154030030300398400301a58903c01c1500300040606440e08000d0000c10402500246040054504012000c92019640c821040841858030f00000810b4140400c0310340f406513107000240c05100d00c0320b0a000315400031030a40f40c2156503440742055030104000606058581c41411b03400e0b0380c2881304c1d2400e83c20100c0e04075601e140002c2984420300191306c0b01ea10340266000c65115207659914050b010340c480001d6980d80d100300348000742400d001c2011081e00301400102c03d17410809034401d018808942518140030201c040207902c1d60902c03007200c44070741184200000070f4031520f90101c2d0300e80d07851441c01900c2111103181241880c0f00e80907004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 124118219 1250 124116969 124117001
    0xc12090304031a06090f1008030301090e0f07230f120109030f0c05030304060507050f070503090109050406060503060d0303060801090b09070e132006040905070305100807030311030d 80
    0x800500c429a4103c1e000c8034200c0c8052819450a9400140040c0014000500115813100064a02070401101ca00078003404403c1301e1b180d6a4451803203000c2d00702a0552409401400e42d00524000f00240c1304084d240d5048461003940c100304501072040c5441c03003180d07900a1014070a00304940724100d120740c04054890004c903041d605800c0282c250702c400760704101000010500c40000c80e0011065a401950096012501d51105403084400f0b01824903401d0356441e001900c4410403100000400034480280c0b0362500316545d0780104000c0350003e01c2100e004c0b0300d0400001d0703641c0c500f0b1000700c500c092081c2400940c1a403180b04032400c440401390111786100c3c8050034031900b601d04000d110010107020151180528061104001228201d80300a184a061402110040d134007045020480c3c11b02506440c2c4455883c94984040c0c841900c26001082c41d01c00403e4020740400725800c25900c0b000e00405040340356640c215920135150040c020705000500030f0700100f44040c010860308482d00d406c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 124119469 1250 124118219 124118227
    0x9090103111e030a02010503041a010b070506010f06050708090a1e0f0902040303022802090c071101020604110f0607020d0602090306090c030601090b21010e1009050a06050c120903 79
    0xa009811a030a03041c9040002c00644040e59541d00240c4052070550a10b4401e499032038134500280c0e0b00b0104400c105e50703501000008126003060030f0182503003074007880803629941d0f079981100c040400c5034000c03080024020402080811072000040c1803404014110400c4107507602500030100c19040c1c485052988900010410314100f036007240081d0140e03100c110f00e0185150b030041c0d5240d42c441082d075113546016210030701d0025084442c1c04051340140ca0412140741040100d942a0702c0140c04594070b00014035045460b51000031800d2040d40d01421420710146100100005c0718007d0341c042c1d40c01041080300c01c0068483e00c0410f411644100009a210500c1b5010581071490081240e4080d50044240c074406a400040903030440c1e0301800c00003000031a8001140c40d0207201c0a4828000841902514a040055000041a80c012015600d4480100384503d0036101c6540d0081c0455001d0010000031a00940c4099005585802c0040c034000303070b07100d110681703c0080b51071500642003c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 124120719 1250 124119469 124119503
    0xa06060e01090b030f030a0318171903051302130f09050a020102070b3115020f0c0105040807152c042007060b1329100909090809090103 60
    0x80100ca54550084010740b002481d8011002d50781c0c0141c80342403042549a018150030175609e481902c0c02d01e03400c0400c03010400803800c0c1164055110480b856a658202965104034031b200c3d01c2010f024012094010070104619001c005940703210715480440c00342d44000c0382075405000d00c241a8803610900151405008900004e0f085c01441d074003200b21500100702d01e40c0300030700d4031107040c60300b8203100c00e983c1c40300c88107014410649070542c10241c14248080e2300000e0b410b400007040c1201c0300f41a01201d03801c6080c5001140c1600440c8035455142c0e01540040c400c2e175051100e103011200040c5407066407204000c007112141c9011200450280385041c0c1c03403503203608183c0107548042e041c1c00025000340c52802d0490b02f185c032892501401c9241c0e200d14034680355803164049017810714421004c0c030146025001065203c1c888505c615000348140c4000d10b0b841c1405003500002c40c00c0c50b1030b220700c000c6c80d004044000d8594004201c0d41c007401003140c0d0701140d48040c520781c0a9401008020305e42e81200d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 124121969 1250 124120719 124120721
    0x303192715020610091e0c11010b0111150a090803070f0207080a080f0904060f090f0b09060a0e1302041a03010b0d050d0f0c020a0303170c09030c0904050a06060e0109 73
    0x15440e0720301190810410800c2d0443d0804c488421102c0d04100041c1030000d60502c90f6525400c0311442000340c0c14111824201a03101280d40228801500200f1024040800660b00110110369148070744e000b00700c080a00d581c11051883e0320a94112000c01c1d520031660fa03010150b031007150440041016030440e0581c035a81002032802410a44005014184446e2241c80203405000754602c100900012a2145070f11160048001000b1076040c62000c1510b900c0d40070041e100340046041000d1611400c1c031000d2808038440390140c0406410300000380d08240c0e02e5213400c20003c221a250000b550300c900016200c920404a44420459185448003904020107003500c045000692050021800f000045207011490401c00c0303440f410147c0e440d20340d502d400d0b21800511030000c0d501105003003000040c1900503402900c50118440040c1807661565034442050041c41d03075070b9402d13038001c0303600d000e41d41000c19090f074004c0e0049088801c0d1021550b82d52080e1085c03038208940411541004010003881 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 124123219 1250 124121969 124121999
    0xf01060806010203040506071401052502031e28030207060b090f0703050613091103190803040303051e0a201206040b04090b0108030a09050d0203031927 67
    0x15840c106026003401030000303581e801140070722407041e4000600e030340c00c000070701400b03104101c50fa400034400c91a2400654403141040e50860b0a03401c07003009080c090520100403551082c415045403070244100c03e50ac00300e00d40140c0182410110024406c0760b2413a07101245082041c1d041d50b01503612103280c9410380503981d54074103c60080340c011003803040490131400f8917580020b1901d07000840b6500c24000032035038841c3c407201c3e155561401c0b4003c020300004400c10346400d1010380442d40010b80c1142c002d4403008824101600d076410600108000a1090b00300d15004448110000e54555498490840d2101c0998003003100c903030740c0d050365040041c42c0c03220041c0d0402000e251304c0c00e08035031040c3d11400000c02008144116515102296642e9460f44022621600032409031040d44c0c41c1c1502690301d0744810a050086607000c980010145407484c20880260343c00340103141019404400000040c4049080205101d41c84406c00c10303584030416607414202d2402040d0f08218600310b403800500326 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 124124469 1250 124123219 124123229
    0x801110306030604032307050a1e0213200d020a0906020c01170c04030f12080a0612080304020a0305030a2303010f12050304080d0915030c0e060904090606030b0f01 72
    0x20600802003182e4000c12401c2c0e00a400d424851805001e40d00603003900c0456040e01c60050401103203080900c81d00083e05600300e88602c1c044443c0442d00504d00c1540c2c01001c5d0000e6102e0a0400e034500b0000040c0c010f00300701061002c014046100c03100440680f50809050f03030748229400f103002c013016640b006a900c010051800130380502c41001000a1402c04010040700c1c2484851012a500b0001d4004481c02943c02120394051000303d03207405081c80c0000000d4000040240000c52001103c1d0b00c10b810491b05201d0780c03285624a940e84200254000a0050364803880d45540040407400034402003900031001c1c0d641103400d000c00051032202c1140320110202c141020700c0144840c0d0784520201702510031010310003071038600307510348a40b5602c905d0300a1a205d01030082c4030238019401c01800750a4400c03008501c0c00b24035084004034110343c080c802d548001040d4902020b800c1c18a400145421000640080350b8111141c49400a560031944229a483c0c030b407000b0000036062420840740501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 124125719 1250 124124469 124124501
    0x705060c0102040e0106110c10390b06030d0f090e07020a0606030507051c170306150d06061103270301111603080112030210050a090506090d0f020c03030d330801 71
    0x4031007500104100d0301020501d0070207100301c1c2c010310010ada21130000e1603451010f402007510080c500c0c01e15150803081d500da5002e445840e90013540c203805240d000d801c2c601c40e50b9421070968030301004103c07c0c0c400506140705600600d940345c0040761040c0a042c0140d8010340041c090300d0714100c184582000c031a500c03444070801d00c00c08000010190401c201d007030035045150b5612900c0d410b00203461030151684e0040b128000240807400f07085240c02c45800c0300c0e99900d40202a20105140c1900ca103d03080c0b004482032800906074484022883c1c16000110010700006840d400584000d0b100fa4026080d0036855140c2042d581c00b003640c420390b082c2c003409000080102e00c0c14a9580696502e0b1a401410384203929400041c46180265200c000c0b52074004080b1002c5042c0a620b880d1165a1803403214001740004c000d09504500015482418003405030045d841c210100e0216002030404035804c501e9021000050410217100300b481e840d00000d6840040741351840c000046084400c420480342541c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 124126969 1250 124125719 124125739
    0x209040b0103030809030c0715022407090b1908041401020a02030310050f030703030e0409060501090f0e030414010c060e030a1214100e09070312050901080f090705060c0102040e0106110c 82
    0x200c0008c41c54008945100300d03410b00404a122040e07080c5400e0013440d006070541c0b110492400310022000780d0240030a03440d1002c8240c1c0341d90510026124007004023010088407200c080034503120f030701400d0740140980c0743c1d82007003580c049815099a206d0500d410050780040f0922051a9445604d04001d1404031502c40302c03000c80c040440d494442e9844080c2c14012940c1544070b85450316001a002c0070303800705080109603154041c80000741112100310804a141c024880710034000081110f041d00c14100c0801125100316004490380590340008503011500c1d0600c000104100300701401209803030383c40300c141e0f0010591001048901d10702d5205100c0c0d00d41824086411a000301d208251082c40001c10354669880854a2510005071300007403d0700320003c100b151195126000e4603040109a030740324103580320100b82a000c1c3c601660a0400354104010401c02c61030710000501089030120009401c041e41c64008a451103801d038402008030f000540b00900c0c20f1001c1c040c0310182d40c2c04440500342 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 124128219 1250 124126969 124126987
    0x80c03060720010b04090c150804050c0409030509270703020f04060518180709090b1c1505090303191a01031523030f070b0708070f0209040b010303080903 68
    0x1820b2101c0050018009140d194940501c000390401100010080d00c2031114914a00e003003541c1f08418450800002a041380c6d940c0c40074405d14506000b40d800100612511881100f084001d0404c5101103080c800700f04002c040680f0742c901440c403066111890380a403040d501016651100c0002c1c5244209072040250720042441042541c007030345d8151401c2c0e0380361031517405050252030100707402540c400030200d80c0007807100320716410601c079045554484c03500d155500d40305400d942c0001e08082e8498211042c028107881100029001c4074020040c2030395900e80c0650480880e03009483c1140a500000b04101e2140d41e09050145a958400d00800c144200c030040700f140c441151030101d04240c1c0b9009844002c051076403010380540314070b500c1c40f12003c0d41c101c8440d107a668241c55050082c040c0c059041007240012451100301c408452419107000c1041e80c3d20740c0303103a0044000316601c02c62718801c20051307190000e1191245100742c004d24801c4d4114100a0b242000c003c0134101c0d1540304000502c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 124129469 1250 124128219 124128227
    0x120f030411060f0706050109061e0504020a050412050606180f06010c03120c08090c060a2106030605010b03060427030c170307020a0c0504180f150c020304080c030607 73
    0x94055000300300503402000301d10000754288503a04004a00400200741d600900c49039620490403100301e8202004582c4c0d83d04000d1902c2c1a003110014060400c0103804c116905040d00140207180d807070301d05946005d40700c1e1040e0b00b2290040d6000e0300d050b8006800c004a9041c00000e2610614010b92402d01c50f02d00348078503a04400000b44442d04208804030000b00700f501074103500d000c0c242d2002c8284481210141c004100c035000300c8501c0c8462103184200c07500390038004200d55014010350b8a2840102200039003140c4401c40c0801500896602c0f480040402c0040c030409028000c4007055641d0f90500c6010801680c1e0351003100d550b10f8400001c01d44030b407481c854100d0b80c41c55060401c20b0f000032680c1013aa0701c0701c404017070590400c0000001c0280c05540803890108242c861103212511301e46030b00078801215103221001076001180b0490a02003881c840f6507204040c414480004800ea11a41c80d40c140d4104407444005a440880c0510080074280076034961800c0c250300416040c035045a00030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 124130719 1250 124129469 124129471
    0x2030f0a09030c0503031e0c12010515070503070f0b0a05270c0d05060711060108060106050c030712200a0b0a0c0212040f06110d0f0305150a0b040602120f03 69
    0xc4049540d62408000c260140f40b800440740c0c2c000701900d4407840c1c48011503040c4070040703004207e203018610001f10074090400c1501c3d000003401036100d0a41e0b090130180f0013114a40c00c041c0c1e00e0840300703112900002d10104010a00d9510945032038801d0314440c5440501000080c22112455060030104581011803900c68a2507002013400c6441088030f442e005420901d000391401d800c0160000c100091000c005071660243c1400da6a0b41102400e111703c954031234600b80a07001043e0040c038010003010340f00d100540000589038094a10301961035840284005082c8052000f2981d1101041da40392904401c0c03401034008217015001005450b42c4200d400391000b00701c0950540c2d1114001c0007030740308200315810365400a6000b59500d0310303441d00d00700c04d407440d100b16000039242801c1e10003000408540c1c0d031034456090300d4424000c1c507101c1094001d8100188403559040c2e9214003400c40c3e580755042e031001007141035041640c440c01c0c004000c2c2031030071900d6040b922440800407a140c0b00c1e00e2404a03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 124131969 1250 124130719 124130731
    0x1206151412040b0703020705010612020f010504061e11060f0105010e03010b060f1b030315040501060c02090a0f0e10090c08030901080a1107200306010609080d1202070203010c0c060b0402030f 84
    0x149115a541007005c2c0c1c02070040e0b40e809445507280041c041801c81c18032907401072050088038500081c4450340d0046405204034051140000c0c14154015007024402d62030051403809418101c144042502d000c91801204696400c00c0d009000010440c55030054103880d070080c0c080e0001d10030f92600c08003007507040c401d0b03526484c0f05000c001a82040c0011418030811105c007400203803543e908100803440d51415204500510840ca403100010b0064001c2d0345048000790701410b06016070365070030760080040c08501d0030304440c03e440d450364203c11601408504000d00159a0010b0070b8150b600f4043d01040da070ba005030040d80d2042105032a6a038004030851380c4000d4184021406200c69045202076005109000b040c02920300d41159100c0b203402c800b15032088050701100c4030f44c0e9944c07100f11281e01841c442e003035050b0800a421081c1c030344524801100b252415102600c0c1043c0340e4082421141d802030207400050040b01c18404003d064055000010800c58040d4291300344a80420102c1c0740182c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 124133219 1250 124131969 124131983
    0x608030406110304120507030b060609090601080402030a060510030512040f210501060b07050d02060606090103090303090b040506041b0305030a05090112061403070602160510120615141204 83
    0xb400d182c42c0c010821100501201d62503200c0e8001117190095440c400ea0004451720100d003400511035040550543e850402c00426440882e1a00c0c801920091310140c0f041e030b018007401044401007200d50044d0380c0598900701d51585010326500f441e500b0502c105000e1484076030100410440c01c0c03018441c000075125280001c1032603130350950f107102006944403c000d004d5401c04000184200809014089490045d003e1717401814000200700d03141c901c21103240b80d04c41400e00095655520903800b44110f940700307007000540018103171034000614104680c11601980440c0030401088080c0301c100b54107110295412181e141560386040d140e00500e00f03c142005030208015126a1060b103004180302e03c03049080110130b0b16003295004861002134610b01a109009000031064400070f6601048401c004a0690440c01c0030108003102141c440e80d4010071514110f0389441106070304c900ca0090400e141103441d0015107400140c0040035810704c2d040420000e00201c22900c1421110b5030b80258000030f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 124134469 1250 124133219 124133237
    0x606030f031e030903130801020a11061003140109080712030b03060403020a02090709120c0602060c090d02060904110f030915040b04111c030909050a020f04030f020102030d020a0c1101030608030406 87
    0x31138585180526089803541c00301c441000110341d1010b6000740301002041c1c0d00d44413510b800ca4030b0540c0d120030139542d84480405c010b00410215070229a1025852880d00005c140140075803155403282c0c020307100c10380f0f583c00c40052038551142c05110f00c0b40003000036009414685440d8a000e0345490340c40d40e000c0d005040d9480042c814074440c18140303000c3d005a018070040d06040703080401148800c1d0049201500c6980c012852000d42c80090720303040c520090144803652507580c00e12115800402c80980c0041d02e4030b6004e02500c1c600c0380502030084008042030b4491400e43c2c65186019100741d0f41e0003900018200303000c0030406042109030b20680001100b0728800f82c40001c21319691030148980034a080e503104150401d54440414412201010350070f019a88a0480880413407154070540030b42140b08110800c00264180ca140300c0c11030050050b642802c2004083c1000e9038491010701c00040c0080003003000b0000c03074000035034690600b880c08000644c14008219a03902c1075015660521900c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 124135719 1250 124134469 124134481
    0x100602061609120302210405060d0f06080a0803101212230c0a0c1406160302070513020304021201090308060d0c0312021612080901031802040c020606030f031e03 71
    0x1c041c40c00200444102042411420308000703480f1890345804c3c00ca1801c0b04806c440299611a040e6801c1d01c100600b10f80c5802c65108080c0024101a441940080d89031080000c20071001c1c040d411050340901d00403592894a0181414031500c290032042d040b001c8950b0340707404a078007070b4050b00c80c1220509285401d10000c80e0b00b9542c0d1007103803900201c0c4400008210440c40f402040387d002c1144030f03205911b401619030680c00c0301055605102a0844070600207480800070018400640d28080e00641d69155115004220407c2c1c541c0038100c1c0f5582c0000601c0b08500703060701000c1c42d208003803008115003842aa402041c03090302400130780c415041c5851900501c03e41540641c0110307407190754250034012110010303442e80303190a100c00d182da184030300000f41000843c007171444c000c0d44807030340c01d00d415126070064000303080008602c4e07042c8a03c1c5001c1d00068544d072148191859580d00144641c2c038010741010320704010040742807442d400c11f01103c04031030710740111286a000324524a40cac40769110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 124136969 1250 124135719 124135727
    0x708100203010e011a0c010e0f0d08090c0d1a04030507021305060a0b0306032b02070b0a08041704120507030b0a0902060306060903030f0406110705010801031a070302041a030109051006020616 84
    0x1d162001d00d540f805005401d074100c000342e11881c2d0030740b20003032b1846a0044030301510340b00c0b0221510340d41074010410100e400e1512000c8200c19500c15514118030301d18803031701031500c10070840f030031000b04100040001c19423a00c034844420316425444188520f1404101103003240d03a851140e04558807011000c54125503083c00603e00202e04a841c4c814081150032080842031102e017100740c0503018010010584103040c1c0c3c00c5602e0341c0e61584484450b03031619602c0140e1200d095260392080c400c140404108040ba500c280c3c0341480c0500010207409045040c8511000c4e8081c050341040382c5042c1c0c2030001625400b094036800001250071580350070801001c07034154460412082e41c101c0c4c0000380400c09a401c00c44003c4000b4020045840c0d560700c0d040151291502030001512008034594500b603072007020b02030b0951002d03c52401500b8182d40d0003488465a1540b0310034411454044014400000355206c0c1d29806002d28040081803841e19901a490340800703070a800c1a5042004151032150103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 124138219 1250 124136969 124136977
    0x1515030b061c090b0601030b06031f03120c06060906080a08070f020a0e04030314060d020405150901090e010b030118020105030c041206060e070206010311130e0d020708100203010e011a 81
    0x9500c0c604241041d4441c2d030000201030036a400c842c440d40c140040b50075940b10b8800e05403039000103051140f66480342468803c0344035410030282c104105815010000840065a0b46080314458903450b00c542c65030326010b81550340039048017600034030f411800c001e601d8000071111080d0741c000030042d031303200c50908040249800c11100a07400c445041c7c030000d40c0340c030b0f10b50007203105901a641c10026081d01c46c81600c0348040c00e0303982e1a031012042121030050302e00796000540250015000025910001003c207003100070903449050b600350760f0080703001010400e0141d4070800004900811051440c080760407102e990000000e41040700c04000551029502812240900f0420513002061555460030b0005000b00780a0005c031380c0010310200740307000d000044240c181d990050705503402048034002d118402c1c6c840780901c3c01d00c0d81c071090b0320841500e0910016141026903405070100354101010180ba20203008002c6550701e00c1080104201110124141d056400b42c105481090843d88803104881c01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 124139469 1250 124138219 124138237
    0xb01020309060c0309060a1e03021e0d0b21070b130e06150f0703030f02070506010b0a0318051506060a080a1104030204020c0610080c0102030409180b07090305011515030b06 76
    0x20700060b032103100b290090350480d20745040090552301b9804100c011002d9006249000e802105410700c8112090a500c0107054004011500003810307003172040001d582c200200da40d004803442c03c03411019510b03106000302000303400c0009981e840e000340c2d00c0600000002e1032080038035013554003011485a982c3c40c00500155101a44841e80316890300b44100902e44c00502c080740070a1a2042481d200085402507c02c0c4c0d0750004094501c581c40d2140843c8a98401d040a004055941c055080f40d0f9107640044490507004100802030020f44001c000503040c40544100e1103060305109003026903600c02600b56100d82c07410800301352220701f0061040740340a25000254020b0002ca02d8884071400052000d119003041e02040e01c0c465910780e01701c2c0d00c2c5e46d074108080340180c00c104000d0000c14900d0300186620741e40720510711030402c0191034120401005880080000e40d040310308109021090180182c5840e130243c81d48a003600d011440390000440c50580341c10300d03440705e01001d010360300c060903501030b0b00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 124140719 1250 124139469 124139479
    0x90403021e070f050a0b1204050c15070506011a030114031903022a030307060b060d090c090c02070e0403180e131a07200c03010903030e060a0b01020309060c0309 71
    0x21107540c11551609401e0084141c4042c19040000c2c680c60034004603001c071184405543d1030300d010302510b5001d101005006662314807684d1100003031a1102d0440d40883d08111100710f85480032850a1800e02c07206030b01002e0729540703500340d121106001400700c034116000540282c401c0303a000c4012038201100b00551803012201d030300350f0100b0b160f00800d6040700500b49940442c081082c0c071003a10b09450784940000d40503401400300500244c86039000382c108040c010304003410000d54048140603644421412103802a48280820590049003d01c1207140760320300151a0041c2070458071000c01c140140041c0070000600d89404040d001189002d000d032510348145805483d20101d81c03e009000000c044a850030802c1000303041c0c0c04480112405500c140e81c071404110100300080d00d2001c0151040035150041e60250381065509108141c1054403e072408135114078101515400e000000b0904509c06003001a01105680e0120464910010031076089031101c003007840c4546503014028106400c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 124141969 1250 124140719 124140763
    0x703020c1003020d3b010b030f0a021c0f030f050d0f0b0a0b1306050304050f0604061d06060102070b16021924020a030c1401050a06150906020c09040302 67
    0x1d41e06800a100c80c3e01e240c08140719002181920512400711001905880701c1410300b102096458103076031440f0710b010f1000225102102c48002414040c64900007000350380031303c0380342c421400c0c1203070071008100882210168654198955a00c0b01c581c12600900300107d54070b40c224080d0040b001d03905c440c07840800c108a40b8080c021004020840740d00624403034008150001502c15124044508030f90148009440c1249850000d9030580c0014200722501e024407880d54500e144104601032003207016150100d10020a050300c0f01d880790b9024541540c607085101000026600012078108491a40e1103c660340c2da0b81c45c8490b403060242d00e000a6100a0007103040001084958000059807048031020403545021110003d07803400041440000d80c010701c92440209020300d0442c2d40160207500e01c0e020030310b0010391280c210b80c0b040314001101d947c0d96000b0320030000010ba40300003407515030919605a40c00d0540203076031920340400c524414010113000904040c420301689003010703880c2400900f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 124143219 1250 124141969 124141999
    0xf030f070c0302030904330e01150e0d05150408030a050109020901020613140714030c0405041a0c04150807020d030b15070f0b190b010804020f040c0e09010f030b010b040e0c0703020c 80
    0x1d400d0144148e103050b89010340045054105201070303540501080e192950b04040c00c0302805001c601c9040c00b41c0c0e240c00740110400c4001702880c0c085105510689805989260403e403060856006030020b03c9024810301003200e81d640c00003401c5400c030782c40d9414502088500c3c41c040390a00c1c24a001d600e5030b07000b8420001000d1540540280a80c1c000700d080d41c0f4210002c42c288021108101c80287c0281140c01c809203e1241107214a500b240d91a0141440e00b610313242d8400b804130b0304240e50400035040c0410004010f9050086041c90700185c90300b80f2030703d9260000256501180c07500042c6241e0000b40807001c1110017840ba08100f980402d603115940382c00b502c588090000141d50200710340c20310302082c4c40c40d0311442107684159030003403d0311010740c0000244001041c1c1d095030f0405014bc034561008041d40c5400007a402000480680840b00d401c52412184d400010390280302c3d01c1605000c248002025509100e602a000c1e003000b039140c441c40d0900304e103010b4240130a1604103100280d01c590b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 124144469 1250 124143219 124143311
    0xe010b031006030c0b070b0103080a110303070801210804150201020408010e060708090d0c0f0503090307030b06031002030c071407030804030602042301020a0201120e030f030f070c0302030904 84
    0x4903402a0004c1186036628400401244644071004013030743c0c84d803001800040c480c5005014185001c0c54200ca8248800c4180c5182d54803e50b85035000c910078070010000011242d1450703d042102c0c0c1456444d640d11556007a0442c040e5001e03089200c1d03c0100c42400703480c401d43c1650000c00f0501c0082c0104c0c1c00641240307840744015030b90040001c0e40c90b4001602c041002982d1400d054a5070356881c2e0440f00c80d29820346101520408903400d010410214455540c10807d0b003003c4e5010b114141c0050400700101480c00402032500701c0814014000c01c41c51240540640b200b840e080f411007030356140c0350400e0f681480000d80008003102c402040c003000b440b503d80c0c05002075950510714401104020008641e40c2c0c5120404039005034016020030005500c10512a00d0711594900007041c5406502a40344c03c5070808850405d250b0004401c10094010302c174116508101d1508020b0703d4091187c500075140d1040c581164019600c850300045600c1a40c45101074801100300c9402c240051189489 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 124145719 1250 124144469 124144481
    0xe090c090f030f030d0903050904050703050a32040201090b0a080907050d12270303020f1e0303042a12050106060509010905040b03010f1407030c02070f090e010b0310 73
    0xd025481072000c40000b410700051440c03004098000a40c1040208402031024040302c24040381008810300003107041d922580a0f05008130703003640300803501d881d02c07000c50802c0f1802e40c04015854a205280b40904420480450010361440340d4100030543e16800161000303810355201c00048a00040c0704414240e114072424080d45500c810f4800075a598810080160410a000342c00910182c0d10000c0050042e5900302d00290b510328100300c24031203422601e0046407113500c01e802580117518042561901800000b9264254000100d048043c080d0302a603a400018001040da052040c24501750302d101107281c1702c0700c628a000f507440700c5449041351400200c1d00780782240c40f982003040c003040c2c4c0c900ad241038443c10441039480100c03191030b103807c01001e03286d000007040d01035585490011413180180548038841e15803090740103503030800c040000c00312054640c0440c00c42d003148500340f04030940c10021000300ca404807404686c5a601b5020b0500400340580081d41c188160b0140c1c060580c100c1d00030b1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 124146969 1250 124145719 124145737
    0x207020306150604061b0b01030f0c15170406090524060603100b0d0207060507050405130b010203030606090f030a1a0c0307021005150904060f140c040501050f040b0f120a0b1008070e090c 82
    0xb50041e54418044cc00045481482000706107980c245003000740d100744030300741d200303000c1c08001c07460a006850b86800c01d0907285000104800ca0369aa0f10320100c104e030880d070808410340f60145549400e8101200964a030b01517445c10b250300085005100f1001d80555a006070800002c10190414510141c601da11500c40ca41c007a00034110032082d0b508145c0b003980800141030700950303d195222020401d4540c0300c00c03115603103c03481000d8000182ca04000182d2024480d4101d0558603c1201503c0c00708000204680300d000c80800403c40718950220302d40c10910580c01d40404e55031240100008035000c0000340a40002244080000344003032501f2000c101c6000356010807041100e02c7c0c2501e400d40c411107000e40380781d01c00c1204001c903501c0b0700014092969000305103400c041c0c07210b02114050740401000c660201012038113800c88410850301c03a400c0004098200b054000710004503042c8840c0707480a40034407804000142a29002c0c0b004642c415100800400b0b0900d008549140d1b140c00000d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 124148219 1250 124146969 124146983
    0x705040f12060e06070c0b10080f0304050315010f0608150303030a0b0112090c031205040803071401140103150b0f130218030c0d06050c0d0905010207020306150604061b0b01030f 78
    0x3880d243d0030085584c5008402954031590806171688880401d400c002c1c20020081480041c0010403440501050307420450580c051a0340700d26040405142c0361003c03041d524400c1c0c8500c01006000300349010842120028100407100d0380da880602802541c43c043d40e181c143c0000800c103c00300d43d0542c000203052000342c88004c0e020a160048030221f502c0300c2c20041150b42030032800c2c0081001d11910068100c2d5502c0c0540c60140c03900f081600350740000e035003241c64501c0c5900400f0a20020301a03040e031802408030003030380c1d50315541f9140040c4a4003c4206915595a01440519201c0760441c0b00381b90800782954040b5419945100c00070340c8805149000403500301e5491151345800305501c140d205c4c000782550101e04a40c0ca40c0b20003800003419100180c04102700a03140101180240c01c40680140001038031119075006040c10041d0040558000b016500d0244445640301d5003a1020380b80503203040054070f40b00d00445400840b0606010384501c189200001c1080010711505004910502c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 124149469 1250 124148219 124148231
    0x6050604140108180d081503070b070c0e070f0e0f030105100305060615031f030b040c03110919020a020106050a0b041505090913020d0209040302010c0906050909040b0705040f1206 79
    0x2640880c400d185031300400c40fa40000007040c0d050b40c401c1400c2504400402d03d107024140444c00041d15145c070035409084100800f1400030144040e801c800c10003080d030340000440514281d107000b070052940380000002d01038080c01401d8030b901c81030000e110356680600200440d0400b0802003030004207a1208030b0b003034800c3c9000034403d030420385c42c0307070b80d4291684980c181151101c84000003010b902c1a1803603083c0b400304100101140003184400d0145000300c0c400141c190031420503007012541c1c110351600580010042c03003505101503022541c0408442801a1200306007a0128003400650f448150b00218a01c404590000308800500441c1c0c0009440302001c1d0700840c040e1003034020020300b65440960f803000640024064206480c0c0c103132005100000d01042540040c00c5130b0026a01036005039560114107000b190422081005481e036401c08034102070340180000c0441500a10081000100402259985000d1029100500408200c4107a455190951003032600c0c142c08064070700a007441 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 124150719 1250 124149469 124149481
    0x80d0e0303061302070b060103020f0d020d052403060109020318100204083318030a021509030906030c0c0c03030c030702150403111e060a02010614030106240306050604140108 77
    0x204c02c540466501001c400010340e5001c0054000b5000b00400c400b90b08410044603510300b80a10082401000d2400300040034203002c0446003d4010513400103034046d92804080025540c001a01e904584001c00c000d40d40340d8820107141d5070240c940d008200d0a11605428441c849030f00d0300a0810f8414040894207085080140f4150003000e001140b0f440b000882c440540a00c110400a07a0054804004100c6015120402e92030b42d4041c8100c003005802c2034180e5102450341b00d6015811410110003141040492030018201d0311000d0018400380e00d000807040d04140051144120500300101600d4441a203000781e00c3d01c99110a0080340700740d402118941c2d0300000042a24140c0760014048508040f0501c1070211152500190360312206020381405440ea6403540104000105507001081c01072814171044203c2c010a10954030a0341802c100740039004480243c0021400d03d03103018240306410300f50a500401c1c041d040b45400983c0010040303010718440e0042c00c91000b0071398410040c4d035129 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 124151969 1250 124150719 124150721
    0x27010e1e0103111807030b04050106020c13090c0b0a02071a03010f0501030e12030a0b03060906160c080f0703050a08070908060c0a11060f06090703200304080d0e03030613 75
    0x30824003264010000180089800701e4403801c1c025030090101d000381c4e24202c6007602e0701c6004554080000c2c3c0c5600d4040c2c49802c0070302074940100a1030000302440c6240e08009080e031080800b80324041942c44980d42c0501198680103401852490001903480d00e404200035250f00841c054000c0503005006c9184d6400c0c5643d048a04850b0620807101c0011b041500450150031100403c621030310512804801001d40c0c0d20055005100c00000020041528820305081032001045c03241c00d45c0094040000003031036418100345807540ea19044603000320a1030200182c0c0544425a88681740114554003019080401010441903d07101d01010766291407044620038440c4c01069850303005400451104550100a8805480c40342070081c0340a82030005c1c280b824030f0448182120000c0c030410b000c1c213801e10f2060290842c166203014001196019240c4400c60044100041e01c40c4002001406104a9006580303840c0900300040c003c0ea86e481451070b41e03981040c0d40040c03050a0301c1c0b481003a0f0050f1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 124153219 1250 124151969 124152001
    0x506040c0e01030210030c11010515040b0607020d08130b030c070b0105030319140706110d1104140120010e0a1712060d0309080706050a030609020306010503130227010e 74
    0x2008200900c3c09045d03c604a0140a039400500c052295200c0c1069003240c082c00b8440c0b2400c509030540c0400e00204080000f95202000d20700d004100c10050203004d0b0b2541c03c0c45c09089904070000c15039074440f5a070a510f640c03803140e00c901240c0c9804000d2007248600032005010b254050114042d81c0e9032503030201501d0344243c0d200d20040c1b080c00000107a001c2c0c01080781074562052080140d043c01c815446440948214a5541078501d030005005100820b19210760100b850f8040505410301d81400d2075080c501fa42c22101c0e60500c0b00c4400c507152005007160546580402c428001c3c01801c80010604e50742d050464130880b419620420012580c0b41040140c0d03000d14450780e501c4000d82c40306800d00540700004242134081140c00440402c0c120130400407040141520364075141e03540a00c0c10020202e50703964000e1205a4010818840e143c0c0e485001c0d00d0700304048440482201001d440040e4003007a6215090a00b2a00c400d14507030043d084c0c0ea22a030485007000a46d51103661901100340e24101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 124154469 1250 124153219 124153223
    0x516030b060a050d060b30010c0908031806070c030602070c060e030a170c0f0f12040f03060c0c0b0c0406021504030f050c2a0f010311031f0308070506040c0e0103 71
    0x1c04c2010000114030260440280408003410000d03070180c001d000c4858069446a00c03003010f01c00081802d1260100b40b10340300c400c0c0e21a07c0c0502c06c203410300c000651280b103461f200e42c00d01c50395440f0b0003583e5500c0200716118203500031440116250f40c0d1a11001075000b64601740c0b2100c01d107c0d0700244807070041140321400b20004000d081c2042880d6111821220803002d040c03540d41003445400c2a00c80100031104101030514001d103141c1c09900c0360a480d02690101003100580207000820404100200010580c2d40c40f501c0429050700500c03080720350188442c4040c000d01502401d1104803030510300200300355400b039400e03a034211403040216800d944041d01c5c001c000642210705000c0341407040380682006007480c02512801d80146030700c0d421205a00754160650001e8241c668890b03c0c08400c0401d85060030309090010200e502c444140d1404020f0500510b2410400300550480052411034095940f10f61045c2d00d83c06241800c555448044030111140c1d841104013080b02881009114100c0b5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 124155719 1250 124154469 124154479
    0x5060301050606030109150b0a03150b070507170309130203070905010503041101030504021207080d0801080d020c040c020f0f1015030b130303021b060403080a150909050a0516030b060a05 82
    0x791a00d80b0443c02090482988500c0c1d10807c130300420550000c0d0000c181c00965903801280b5600600744050600c009036110800113001045088005580801e41c0c10840e814a88500800d0207403064190640c03143c9000c1507400a0250100d40c150083d540c0910b01810040d45e4001c4256100c1c3c0064500340304c241d80290050018070140215988290452a4803601c090941e40b100c0c8100ba07d6140340198940121046400c0858002070062380222a940106507040041008418540c0c6c06500c503c000c40c03650f400b41d41c50303d000000f03607030081180c0d0b80504194401c40310b6000b01c05120a403100e401c00c0c0c0c941000d605000404001c48012142e40b0240c030303080715072000151940040f01030007001d017010807802c4c160240b024010700b50843c1a40000d0014510280880d49000d160082134424001d0030680d480380b80c05551605c1c2e04026070a40103170f60101e580003450000500382940780241000d001001d51003494120200404005840130840344680840d007556110442013003001c0d0f4903402819000703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 124156969 1250 124155719 124155721
    0x806010203040b070b0c07020d05010507030b010f232b06090c0512100506030a02071109150d1a0709030c0504050f0609060406030203030a0509030f0109050d05070606050306040303060303030506030105060603 91
    0x817440382811150001444c003242880d0450981c003240c10f84034420003d8800341d569801300a601a05406000130342c54003443e0001425482500291980c10f10704108030103518810101807088107144100d8074540a40102c3c0740308402c514040c119003480c07100901d800c047c241840000e48405070701510180e41840e031546418041080c49141c280384001303040144030b01d010503000401d500d4660040d4000e0700242405661031603141040f004001c80300c440c0a0296022404200030f210150b484c560494074100d50000c062071650400450804594062151006281042c4000b494015906ea03040340e20500301106000d5603142000304491040380c4c40303610380107050300060a03441c00000703440e80700c1c0000700700040d81c40d00d980200e441d6410024056020400c0000d902d00c80b441c003003182a10055030b40009000d1f00f030050343d4085d2a4036020903c0010b00a0100300d0108000460300614060000038040755010b00d014200100945201d200560100349001d01041050070103000d0b56210f03880141001d0b1035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 124158219 1250 124156969 124156973
    0x20304030b0c16110123161a0106020706020f0304080c010f02100e010614120a0204020901170f010e18070b0d0605130f111905031806160806010203040b07 68
    0x940c1c000500d000001c150801c000100144090841d0103668066903407061000c1614001602c0103c0156485c090840c510715011040241e150440e840c889800c90310b0340722031215140950003503030705c6600794062281c010000700710300e1f60004034441250a25821031b8a21324243d1142a00d1b8807580c0502c42c56508100c0400c03640c0e5020300e02c413901a8035603204540e01d0300399078081c44084030489081e04072203035106e0b00200215124000c0400745403200700c5051142c40d15030b200300ea0313481c40c00a400901403500820b1102581c0c1c01001c804024588820300e24510f4500400504c2c0812000d0042800711072002e40480d800f4141520b910031224880c1001348812402c0c039604c0e0f0f034a50013242c29080d640351a03d6003c075154032a510f820304094000d00c0040380140d1169611400d44061030011603600c0f005000100c3d414200b5110040c9546983c10030759074a89500351904849041ca0111414611072070040c815002070039428000d480c0e1980c0c2e00c0c4100303078a400d4012a00d900c0359104030f6070a60024004440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 124159469 1250 124158219 124158233
    0x70b01050f0f040c0906080a020a08040605060a030503030f01030302060c0a08070e040e1b0a15140904060e07020307050606220f18030504060801080c09280e0c0301060e0702030403 79
    0x72203004010201c0940e03101e080d0000f070a03100702c0311500000401000d420045250848240d0383c002c1c0d407804041d81401082c0c40c00816603c4e000308003030b102130307103450108400f0744604004034017850b0000c4c20390380da0303180c554041c004003071080c0300480051281c100061240c20501d03060710105ca48668880c0c444d600ea030072040b108141d8400c032950307005d039071141440e0203042c0c10016803450b00302c24510722040d044468100007a1554503030290000d2594200050b1409600c11b46020815010303100940d1502d0601020a00404c425040004081c041009000000344c002015009003407007141110060ba5031042448140d180703440d003001e20b84003020300702c914142042d00303c0d142c1c40b08184000105290700f00784c06a4068221030041d00892400501030001541c81254030740940502c0004040c10424180458000c190007090680e000e03030611416024503048116108a940c00010140a0035001980c2c090f11129061006d13032182d03281030000919250240310541c49a07181e500594106032454a07115 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 124160719 1250 124159469 124159489
    0x1507090e04110909011d0a030e03072d08060406051f0602100c02030c0a0812010801020306030c0d02010201020919050a050108060d080702030708030d02030103120c021f021203041208010b070b0105 86
    0x10071300d5480b5042d03072001d0040c09a00e11150b4030590000c0c0750b01e524a08010786101e04401c203290080d0080001801004100c210f400300d6030b0090301d096000d108102c5154401010300360040d80b444d010ba603040c007061154980102e809149040b0354544242c450350702c0f00352606160b214010158104085090304200d155110010601050060f40d1a06446050f89070818180c0072040b61a407001091003d000803490450710b000d0040300000314518108000000d0751020714642407442504040707641011a403007901038901ca548c018101c041000c2880d12000801c8010340100d5000301d02c0a40d00003455841103040310700402e005808018080007a03200d909181d4824101070307030188580440010461000c000515203403140000c0161294110302c1c0c01c1401c80248080e0034104411018080003690ba40403134444429808076007580030b002003900607806d00030402c40754214210301004000034400d101d20001800c001682e00d441c010f070b1300c40d15401c5440c09441c4014200040c200c0050001e4188902d0032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 124161969 1250 124160719 124160731
    0x7020d081b0703140c0a0f0302091312080123090c090d080705010506040c090e0610020115081e0604030c080c070e0403030b150301061409060c1507090e041109 70
    0xc4401030303400d51505460608283e0084866020445281502d1241800000741d1600c003100c15081c51844c2240c4150038101c5800040d104141400c0855920f110000c2d000310030359801608040c80c0c0d640100060321181d801d1180e0380740f40210383c401c000f4190b5001d160b4640f8290080c4040c10986550440454a03000a518140c0000c030b600b010f84085100f62000d000014070610010401e4038029060209551050f01d10b4070901240e0207040c0180c4810803c2c07250f1002094450b10390440404e1001c0b80503020013010030b400c02030400701c041070080307003c50b184001035807170100c0d1024201a5840c45a42c2c80080b1405000608a905c00c0d00000d24080010403651403804200c5050f55220721400149041c01c0c0c03412004284c0c0e9039034082480c20002841070a00c1000591a801c5601d0000040e120f140c042c1c00351818840005851100c90f510392042d81c41414003482200e919407a580e80200442a00b62058404500c010000140075a509030600c0e11560b804550b1081e100c80d8a024403940030350207001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 124163219 1250 124161969 124161997
    0xe1602241008061918080403140109060513020a080705030d050703030e070909060b2209050f0307240603020d022211040609051e01080c0d0603151107020d08 69
    0x4040c801080a240500640c2043c442d890700244c00300003c450311074001c201c500c0300182d2000086040d0780192000c80e5049110780303040064044840740101941c050060095140c181841092041600394212030b07882079460aa080d41c6480300329540340c086110300e40c1c6c580d200f102540061440341c2c015080c1036100e41000701d03126a018101c9030910239142c015158169aa0a008050003d64084c900074200141c5045081012601e1950b107030803540107182c0b082c1030b110102101048010810516125a0003050300c1c0c45200307901e0600f0362401011540d0100c4108444000d4021100344140700c100c0f90300400c0340741c200312641d01313000a0341500b902440c10a001da00c442d42c2640300034002d001982040c3c00310950b581d0f08114015020300e40c942c200c240100e01e600c4111040b00310881c3c803032110140134240b9449617a0340c8005100380c0e1049240d43c2100702d007030402c00002c002c4800c519001002180005208480c0c1d90006d0b10000d0045400103940320006110410108a115005111991107046 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 124164469 1250 124163219 124163251
    0x118380a03061a040c0507030c0b180303010e0708010503060106051e0f0a11070602070509010504090503070f0b07030612150e2503021318030509010e04060e160224 72
    0xb2802c00300da0f001000244030100c004011015440c00c2d1056000b81201828403e0508103545c400405c40381c220318000f0040d1003440c01103041c60414001190040124104030303030ba0780d82c40c2e281300c06004006a07120780c00300350200004601c51031b000c20024103944a035600c59040811074489038441c1000c111240141550811004801a501400400e0901c580e0386030301101903626002c075494484541d2101045401080c400d0149079181050f507070440e10101d07000705000321141010390030340c440e22000601c0c50100c40204020024103052840c4210a103484c10402c1d01d55034200001c40b400c0158009120042802203c0565a06a0b206100c6600b00001b10307800884089140304c0307040c00401e90451240c000a00c104214078023a508a020400403910900180c2c0070156100220034500000030248140410490501d0f40b16000503000e44a00400500100d55280c200550080d8146d52907070305810b10003010704445000240b038860151154000104a4800c81c824a0000c4c0c0060301060180685403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 124165719 1250 124164469 124164473
    0x120c1104050c0a09150c1401020d060f032d140a021507050c030f0d120906061404050610050d0c0903080a0810080a03050f0304020f090118380a03 64
    0x1c401d00307109040d5088240c3da201400709018140c2021039008030900b009075654240c4041d440440800b10030343c45501201c1d10301d4603020301c601900649035a240903500e44400044d89184440e410000c99025007121411b0a0a1149030070b100ea00c0701c40c6141c0c219031200c2c0c1a01c00034500003010b404844058098481150440d030000e01202c502000302e80030381d880401c0400074820203000201420b0002c40040000340721043c425a143d002e440c801c141407004041088000001640150b107110750311003410407140b41c40384200347d42c04050101b040e00680c68200055640e041c40d03c91260310341c0751034440324204000045020701502c2010004070420070580400000101d40380b011b0031511043d6220110f06250560000104105580c0284040c1e81705c840350390007203500141150360910070409400e560303030340714004104d60160404415400c03480007170000908407228135220420b032006034028040c1c0d03400321501d80c0924000706106010310940d1691030f4024440400a002352000c0600350041c1542d40e6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 124166969 1250 124165719 124165721
    0x2031602010e0609150a1d0a05040507171e01050315040210020c0910031103030406080a020306041d07060801090b1c020d0503030f04020910030812040c0519051804120c1104 76
    0x5003402184420b4041101c00106400000c0c1c4440b00005020b81e020482d1f40c0c40000340600528810036003e81d59600101c0c084070311030b0001c2c001398001000040d10b83c4c108180d600d02e140c90311503041d0042c550f108002051070302d404941a006c0b000a80010960341d00d80713400304401c0c0701c40340410600350320a8130a404150b07250014202c1c0300d0092850152800b528605084a040e017604c60801e100e42c004110034009241c10400b0107812a004110050700d075526000860000c110026407a200c14400c0c03e0a10340300c0710009490411340c0c00d1035850802a0340c1c0c0b40d1510040d01d080d042c040f50720004400c0c0c208040248521540d10359400100000020720090700c07030504540c170944410100c10b18a1080200f0341c00d1000c4d00d0780e0403103451140c4152803461616204901d001d040040c92000d1503400114061220300216040039000041a030302a03900c015450307841c3c40d0024070074603000b80304400001641805407402a0710840d0080200d0b24451000301003101c0900d0400000c1b141e098000b4079104c080c1c1c40d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 124168219 1250 124166969 124166989
    0x30601030c090f0e0103060c05030705160302012a09090e070501050918160f020a0201080f04020d02030f0c030c0a0303050426070b0c010b0f030d1803060e010c090602031602010e0609 80
    0x54024000005d5040d81000c80c151040c600b102000c1c020700b0000c2c041030b50f178401e00b1107580001d00c50110400d85031a1908a014000c00303021200c20007601c0c0d04000c48118102c05140c503600850300e52001e0f40365036803d401c0039034190158840c056004003008120550213503005003100d0130001d1801602c82020790000000c86401c0e940744c901321005287c0510741c0c90308812003c0d042400c40c00100500c81460713000034200030000340710111200d44e5802203402c40d01c1b0301008240641d40101603c200002a01d1000d40d21011007650038800d100301d02c410030081c04d0070b400d07040540303401d40d581d646800d050401e034003062240c08a0840300b82c482030b119520303800c1050000c4005807401d041d519a8694070fa90f149400d4807008020984102e11440e03000825540000b100721451685d401e000c0381503200e004003045812074645c00542410300742104c880c50508198403400d0343c5619500c842800a40b03031101280d0b40c1c002e0401e80407512040d02102d60140d806103800c0166000028892482d00c000c80c400b103614158 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 124169469 1250 124168219 124168229
    0x22060b040801060e010816050d0501021c0b03010b0904020d0303021b0a0501050601081f030215070203010608070602060c0403050706030b15070c06030b0414010302040e0a0f080903060f0606030601030c090f 90
    0x165840d0284040040d003101389004182680007084290f090681001c140d400a22900344200c2c9002e003640200300d42901510040703000d503159100c641200214240140c21076036007491080d460b18248903101c2c600194402e0040e0f03006002c8202014003503400340d000b54031080e00c40e044201d0020040c0b001142c20010350000c00d00c10030000c182d42c2404000034243c4113005e0100d680b030100210b00c2104401202140d10210b0350111403011050401c0240b01c0340c04d01c03c0c1e2001035019403c000e004240d0350750000324170007180c0069088412a42e600401640c4501640c00000e0950304824400c000d070b00c1c400d40000780c82c0080203246027183d07070352324420b401540e200100403101e03510704a401f009919054440c2017640241070b1000d000120026500510400050100901c079554070500c12041c03550170440001c9203035108107a281030800d6030415000726041108110322a00c030b80000a0008011000441c2c000c85028003000d055840360001900a451f07030419107030070418980c80c00181860a0803131600204 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 124170719 1250 124169469 124169471
    0x30501020a1b020d02011d1201140a020702090109110906071104050603010e0a0f08090a08070905071e08040f050d0e1e0307030f080405091501080702070522060b040801 74
    0x31801980680301055140020102e05641e00d0501e002d611121500542c5a50928004442d480c04164a08409108050a0341c006016003400c0e540544154082e141d14010078410820325902d03581143d05034492504001c1d009443c11004100114071500200461101d00c0181130415030b088001c00c4c802d412100090307842c00318804072041b050a0500c00c40e508080160001d00040321314081f500e40c1c3d60078011008052040d42c4840341e05020001c41070b1001d041c0d0003069080c0da01e5031414296617070031190207124a21842c101c00300340c141d8041c2403040501c11100c071801241040b1210190f1702032000a20544003d03005284010014a0078421046284103903224030501520800511441e01c02c0280d458071441700d803a41012583d680012030104580d03101c04908400c030410b2030041c82a010300e40c80300d034000c804642841003c880b4180340d402d4403d400e80e03c0c080c0950b40c0e2403040707079a0f141c644103054120303c545861000d103544240134040d2018034168080741c0560b0341c601c01c500641c0154000c000c26 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 124171969 1250 124170719 124170727
    0x1407091109010f0e100f120207030306180506180601261806010b03010b0703090e07081806070909050601032306032526031c05130816110a03050102 65
    0xb0b60300400d0700201107015242080070351145101144602e45808a50300a0040f200c805001680c85070050701251424003400f99190b07a0b442c030380a00a03000318010000120b52003000321028509620590380309810083c0050030356011000303003003d030030406002c4604100d48050152098108000d07001c40e14021006491030b540b40c00d05c81c0401c0c03505440049000c527003011004203d0800c0c45410340b41980d11029103103607034410510303054421070100d600222026038404108008141c0240880340324403215550310801c910010101500c0d14412920b280c041000d028080c00b0300700c200d50082d6030221060600045070900445003440d01c940c10085500f40d404034208100150030f040c019a809148042603c80700c0c0782c1100c1c03c1c1603e03020540135192014149031041d80307403070081d500c1c240075041d01c6805413507440341040c41c400541450200c1c600c0d80c1c14107000114404031511039000140a4000001070708008003108042c8981d540041c0555440410101d016801d40d28961078000961140000583e2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 124173219 1250 124171969 124171987
    0xf01030c050303090a03020f06220509070f020604060b0f040204090e010b03061614041805040c05030714092511010b041103010504050915070207030203060c040b040314070911 77
    0x2050280c00071030003500140614003141e00c955600009695044420000c80004800401e140e0301070702d41004111111040380c141e1503000c504031a0243c4200b501d8134000c03070741d2305203096a4400c0d083c2d05800c01a4800b10029000c120268402100c001000b805181c0c00341010000805076041500711300c15290351207000c0d80d2718034030901c0744001001d8194050045403801c1c1c2c8129800600c80e09052052141d00d08507241c44081840c100d8020342001c44c1801c01e2600106400d8000708401c44003212900b00146000c01d6500d00018004101c4070b00c00e010b00021120388042c07010158014000014804805400300c0e0b091210340803100789405ca40d5070345680c0b840716001c05401c2d50304031001c0324081c914180b1920018030f00345044906690050710081760544945100520b40301640b50840b01400c000014001d8496000c26541c084a008404139021921040b190320100d01c124400d6261a460800080000694801d00d4102140101b01641d180c00c0d5200704040c00d40d040c4c500005505000010036082e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 124174469 1250 124173219 124173233
    0x120f090115080f100b06070f080702060d0c0818030a0c02010e1302031e0402060406110f065b0803040b190e012106030206070b0115020d050708090105120f0103 70
    0x30114550304810310407170b003259012488a01c01caa501a0004641c4c440800c140321181c02200c006035406048540d0750352140e51420014180c20750040000707071885001c200081101c00d20800008400c1018601e822a070390400d499000e00d0240803414015410104c0c40581ea0f80840d071a0310401c0308002503583d251170040a03000345111402d4010901c101001d000c05a00c0303400c01e0300c0c00d4562900304010021b892100036032901c0c084818181c00d41c881c1808106c0039a0400700061051481e60030041c40c0c0c000c000500030104040c0c111403401e080d110400340c03c51040441d00314071400c46540505008036464951440c1192700982081c880741000164000c981d81188101c02c04203149450041807905010000901900f10413940007000190b6500c44017008003958804001554010002540e5603041e1401d044d60f103c0034030850001c0c070405210800c0042c00400c29404651007595454500a81551364585d01c1d0441c41d1a103041000034000d04038014060840b41d13000d03a08111002c1119071441c50310344 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 124175719 1250 124174469 124174483
    0x9010609030506010e100e10061107121203150e01050a090c0503060f041107060e0d0207050a030b0417030103061a19050f060d090f03020d05120f090115080f 69
    0x8040028a000401c0480c50206003681910203203144c0840d01c0c3ca41c42c0010782c1a140680000d0583d04841c01442404100b0324100011282c04d1788a0100381040c1040c29030300c41040c3d1084a14549200045000048581842c1c02180404d0301700003599805840034150403c0b5143c0110b141c0d000014014000c6140c04960070004003120142480030146400c0c4c018101c0c00094039250103006554070482c05541c964020342e000c102240380d516111100f6092050180090381c2282026000c1c10701248205440400c4007000d6880c0a03005540e810728565400322050b90041040d40c0940e48144002052801c0c3d1000f18001e50242402003070001141c0c1007031980e4022a041c95200c0e1108040d5440c16262a40c030a0045900440b10301c040d040c212008540d240c484c400c52041001c2c64102103c0c1040700148031100ca0718000c4e03007211118160710303105070b90a1081c40d42c14001c00401000050032140d0a1074a50360100203107001191504e0700005071000912141c0124616810460300348216060400400b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 124176969 1250 124175719 124175729
    0x1110a020622111e04050a060914040f030c030201020d05010608010305010c0914060702041b03140c0702060f0c0109050d02030c010e071214210406030e0303060307090510120b060901 80
    0x8800c041c0d02d070b07451429010407950350600600041d403100da1851108140f450114001800034040e6240007245000184034a00410400c1803520f05040200825080100d03c195401400400070003d980c9040d994030b0f4080302c04a00b19902041480d428048034000d4070b000380b01a8541c0d110b80d5055107001801c1d941000784442c100000c00307204011144002100a104800c20b0b2800b554960f11800802c1c040c1c481a003040b0000546035244808460b0f16030702101c507150546d44118584c0c1c50721507501d030141c8100507001e54400010302000c1203038000311000f4550040d22800009503240542d5405050490701c80826015810214031001021828007a0b5040303500304502604009003070082903d280c800354807002e00301d0b030008010010016000c01031401911241c120704000100e42c00200b003001d0b8014021700c00024103203080c0c4d81490f00000700b564003034600203000e01825400c0c09542001050024410011200c12050002e079041f030b03003100813001c01c0c0520350300409458540c1c1840342c060340603400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 124178219 1250 124176969 124177021
    0x20a030f0201050f1611010e0c1801030308040204050c0408100515040b06071b051f030b0a05010509040506040b130203041721060d060204061d1210050901110a0206 72
    0x403c15188a80c0040f5940610b0100745007280509504040300c2200403255a003802c7d62070300075003203e03e0b81d0001d40381c0d41001041701c800ca031214a00c2c00c120b40110003840000d01050f5417001240061070640c002e154040b070f410740181c0c18695101d81e20b901c0c15008441401c506c554450510a01900d10008100c0c111b40c1030b14180180310200c0c000c985940304404014250060808825030007030004c4c0b20202c010440207082c24118114184a5405503001203001e102091a098500c00182042e2a01908403681611003a00327050648046c00003510000f480564416a61112100c9076039035451100d0408540002c0107803240ba281c0360050812800c11a550483d80050040c49010301c290b0420301004050f8800809543e210354012038203035150400010071080c00402c012906503417100c0d40c07007010f200410030300314446040b5043c818401d524005561a139040380034010702020440d001560001042000000d1199610300080075a4000e140a0340060300a42c00303010f100503103e55641c04000380d40301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 124179469 1250 124178219 124178221
    0xc0a0312140a0c0f02040b150307091401081f03060203070512010e090c01110c13050a0f060303050405040e0c040501031212050c070f03020a0b010b03060102160305071a0d020406020a030f020105 85
    0x81c00f8162604140c03005007021510700d43c0d103046482d160807070304114002504120b00d41c50044401c4081e500100c40e9000000d6421a0006480f10a110486144441a124401d250326a29101e00b521805005903203c1349480c120004006034883c07005502c40c001a03551113494606040c5248000041a8090345140d030b1407070140011008041080e00100e6406d0902500a003d580446410078000e01d0a50380d208000900350390b15039030035401241c40b840d80104100a82c031200c0d211001114074600014001031010302003881a420141c0c8552041c2d000b0004440c6020006400079050f21002d0b0012160425140c422501e610307009030369142806100c1da0b092020b03250130282c04210b80507529000d8000c007003014000007418000d000c1e6040e00c58004103c4000b41d038490003c0541c950054654a00600c14881000c0c0003203604006082500d500c80c0240440c541780c07514aa9012005844070070482e80104031000043d803044c0b0082000704020f8000d040007070010700380542100360519041040d17906101c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 124180719 1250 124179469 124179487
    0x110309060f070c0f060c060b0405150405150d060225081207120e0a1209050112020901021606020610090605090a0f020d06060306050f180a09050c0a031214 68
    0x1030a8501480e21468059250a450304000c10f4401841e8130040708a80e01d00d5012855540c04494421545e0040c9002c6c0008400681800120f880454014041e1500c0f00702c070340c00900c0e00e900a91780250b154180103100320080c1c4005143e40410100844001c3c0c0c0c002040000c0c5200d509210b91401500401c00d80c0d05072360354541103010b21400c24000c0d00680381c1c3c2e0001d800c65000302009510070703603580410021807241d0f11507151784408219003070300c01d842850040c2c405a8805c520001c15594103a440751501d6245117810300103500701540e280d0541c0142103501024291210442d0005d28065004020508100445100540b065044890705504200c4244116200c43c81c0468002d41c2064000500d04100041e06009005e040080c030812801e01c0000552107516800460640e60120340c400c082c60152800c120400c150040c01d03c81d00c0ca20103001070070180039035110301410f40c020700550398558420000240c42c8003c5401c04c07a0081c2d0303c0d0901036096070740101d410100711071154125207005441c6c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 124181969 1250 124180719 124180729
    0xd0c02011104090c03090f03080a0e01050c0f0d060e090a110d02100503040302010f050123100e011b1703190902010518040603050d030b011106040f08090303071b06110309 75
    0x18000d0303a034807a0300c134041e090525210750321800ba240e4021511014000395850001c5c40004169840f000145c1010403e0f10b8a1034180b18550168815400807864081501d0303404501c1c2c2c102c621000c0800303503500e0000908094041d111442460b0071800390064121500d420404502400450750140507000e0051006898450184030180c0e100d05002e038499903140b404902500003100030024032400c00e800000c04014900502d800024604001081d00c1c2d80311042c0a418158080c4002c0003510b250b2001c22a54002ca000001760248148018189221030316001182e034109400702188070000800c00241252050b140312000000b03900510412404c1c1d000240540100080340c1c1034980030001c506a2582c60783c1c0704000a69220b416100241c154031000b40007461060340701741c0820080800b0020040323010484611659100084010300c0585031640f136180d4020040c081e07010f100030018540415a4070030003040b04100980c064100394180340006004c4803003043c9031601e075403080c0700401542d80c45c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 124183219 1250 124181969 124181977
    0x7021c0b07270f0510030209090f04020607060e07030204050612060f0c040305121305150a050f070204050a0b0a050402040f09050405070b0a0302042c041101110d02030d0c020111 78
    0xd01d0a1200c21541d40411000104000603214104a40350350020f4501c194001c0002103030012260300100c1c3c42407030300550684c400d4040d400c0d0712040c01c80c000b0350035045014040381c025001030651400d08002d41d85200c00c80d01d40d282000d41c1944802420030441c6014010305a101000355401078404650b402d02a0762110b0280001c1d645009000c005280c159464098070000e41d0004102c46244482c210000d450303601c440700d0031091007815400031449007001e418100010035410310707052030700c01d01c2d0400321401d421241904078812800c00100015a550380180e0703016160030000000c10b00460400c2190801b51648994010350050000b004591500c2d01400100c824070a8080ba29a4a5190160400c1056081021a81e01c003107028202c01c0d03410390203001516440c4031007541034014138004007050480700d50a40200100d8100290014400401c0b411020700103041002c0808881d104090902d80f04014010040c1c0c0b000c240d078001208a40515403008913980002c1007054102c40f1003c1e2036102e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 124184469 1250 124183219 124183231
    0x6051206060d05010e12040f05010810060c020406030b18060f07020a020d170714010b0a15030209040e011806180b040305030714030f0106030e06060f0d11060406020307021c0b 77
    0x148141d01c620a004080d000f05401603642000c0e43d11000b840f100210f80c0750000c0c018201180c15424009c0b0b41c0b94000c8214134040e00d401c05a202c0000d00d0010100e1722000300e102c04a0304207845490000000c0c45111219005203541081c4c1c10880c0c0e4030404e00b62034070800a0010000c03104035001e01c030401d40c0101c0d0b003003260b42d0180e402030400100c50034030703030700e0402c09109044d600f090001e0480d003400f240e03180c2c0d0642e07240560002e1041c440b140d010041605100d004e808600000804e0b84400103001e68010321007250050004214241c075174144a00312607400110001344844441d82c1c4080150910961740200500859428010250f44506d8188a0001c1000781444000408611528043d5940717016141030002040c0d9203203040e04004102e40d03001c0c4a8140440e007130006160751440041095845000f0150807040c014440104200c900417082c9002c0d2255051903840203800d850b888007d0020b00101e4004503501c0c1e0707413403050246144100d030580c0f41c0f0f41c0b81e001558002410400590360041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 124185719 1250 124184469 124184479
    0x4091401050a05210d0201090309080c060d020a0e0a030305090f09010e0f04080c07080c0a0e07210603020303030906010e13120f120c0207080d0203090f120c030d030203010503010605120606 83
    0x6070448014141c02904d2100d00c92180314903e408081c0a40c150000031015101c3e0390341c16040c59642101d21b5940610201c4582c0c80350003072041c101d01e044103a0141c803103031041e03151140c1020360807004140b1200ca260030540c0042c800040c2c1e00194280350030b4482c64400b003034403030429642c9450060203028002414548620300e0002c007060a00000000303a0300d075801d0480c1691949aa43d10b52999202e503c00c0341c280c0a03400e0001c00242c5440540d650720300c82c403000d8a43c9a5000c6942122100b50b0110800c50f129141c3c0c1d81101001688080000d540305103002c5000309049d5040c607a01c40403c560041503208003107100588040040c2803482d0240d1825102d0a14104910000800f039500d141c00781d00d501461803501c80d00c0c0c12801c1d0f001401000300c2d00b114050f200c0d03c5000071001c036141d11904003400c0c0c100c0c24001e40010741b41800c10a0020400890080c1c403232505c0e84100003820808030200450001ea00400188058a000e02c01c5600418089810446500c01c000800740c60f610300400b518860 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 124186969 1250 124185719 124185739
    0x5060c030405060d050103060c0f02030d0c02030c010906241802070f081612031802121501081f15060309020409141f050f01030b0406110301060504091401050a05 71
    0x102080098502404000b02841c0d12880c02405040080100b40b10076a04941005220340e0740d14017540010400d03000b036901079440c20320005619000b601e1004003420462004100e00844100c0a00c01c48000c607200b280040782c0000518541d12800483d07003144612540440c500304003c3c0325051000000c00c280e94005a01d6000e903040c0701d5a060007115010703100034000581e40c081c01c44662019a603079845141001691820000202d04450741c03c0d8a90b90b44006003440240580f81070001c0301640400c12084a40d603641d4615540c0051600727a01c0201550f1160000c0502d00c40e0030101545c207000c1c0802c1c10003100c10f4031140105080f6040c4a800103259541201d102951201c2d04400c3c03c071900002482d84814401540356034602c4510703000305c850044803552207401645800b99500680000185003c16401c58465910801020340100d4180c2d0382c1e4044084204030402c0603500900c455200c0c1341c0c80c4d0707181c00d0b400340940f9007240402112404035001440302d5030310300c2c11500503100152070090700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 124188219 1250 124186969 124186987
    0x70b2d0f1e0d0c080115030501030b06060c0a02190501080f24180114010905030c090406020309100501060c02090906090a061109091504060501020f06040803041713030308011e0506 79
    0x45200d5000c0b030002c801d0400c0b800402464000028038100d0768103401000341c44180c82011402c4a500380802040c05c04228085403042c90a200500394010b2044140d8024284681c0002c000075031201c5007030300c1100002e500301301301d681040c01c00b540038600d003000b84602e01e0014600d502c00d004031140300081c0318160b20020940d80728854456a2020810707900070f0b10b544c40e40842c1e0b25540007100c1c0c803400920213000208207403c0202d100d6000900c05000b0204544540c1d4480003c1d400051035125107200e05610842400d8050265600801090b280d8040c5401c1c5401840b502401c0201180803d0303100b00188140c440c070010301c211020340c1019000520200c40500301074180308031541c032940a0501c0301070000c1d01c5825030007060b42d01801c84041101e20f560304010380e190000c0e10031781000754121782c1c009408035010600650b03210744607140d10b07094591441945034240c1c1100090014a10000c03070f0074010590041051405000d6142d04070903011002d8010b0404194540540f500900340441c00c648 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 124189469 1250 124188219 124188277
    0x4020409110d0507080607031103061c05030a110d030605010c0210210b03010b030c030303071103090904031d030c030a0312020d0e0a060b0402090d1202070b2d0f 71
    0x141c500040c1109218403a03030034040e55451060058101078028000810102c42c000c0c4200d0641e90f40034110f144c19940c40e102001111120f22102034041d0780c1c484410300c0020002d000402c00080c144c1c603174480010300e110103a49401c030409130050500d454803001b03000c0703030ba000412081c005504072113f181040e501082112081d01c0b42c401890403a1a02205610440b00d940100d00070700700a42c002c0100c071000c2810199203442c1d080860b038041c0c20401c041850684a84054400801000700700c0c6d140003420004510b084ae821601038000485190018401c0e0482440034003211004400403c0040301007170000351520034404d40102030000d840c2031041c14080303a030142c40704002d803800104106140940c8468039100b13400000c540107841d0010b0001903142a10070356000758009000302d0700210480c0c0d80e030300f0141c40310754141d0154401e6010019034484010001c207031124500d440c0700c2c42c400722459012010710160701c03012100002030150041801d1040142c0d5500348006001032411601d2039001302c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 124190719 1250 124189469 124189493
    0x70b0c0d14160809120319061203030515030a03120e0a0b01120311010513061e2a111c0c0c06030212070206130201211802030106060c050604020409 65
    0x8804070031144100032500998101d04014401242c9484003d40c0d2903c2c0116100c0241c505180f8620b8400d0012500311031152811144440340d9144c0080d500361182d18040b0f81020846049001030b459004000c0202005944071241c8501907000380304a401c0790b94044c00c540c1c200020b00e550b143d41c0d072a1414420707808002941c072a681140c0e40300002e585840e404003072105000c0041c0d01080d00700980e80141c030750501c01e50780b1601007003446181c541c4413584c0c2c0c50701509130b2048102d642c00d00d641007591902c2c031612440700c00644035a0f03911140d00004c000204116a045001024048145038006c401180402c03140b00b0396005030600ba00e0b0819010301a2018410948090807404c2d0154022604075010760003000620340c5402ca142c61543d03000d10480c0e442e80100c0b80f100104515034084070065014001c60354051202c1c1804052007003040c1203010840303c180584510300c03081c0c1a03070081541400e12525014140a180085003442280c40c3c0350368441c00908021f00842c0d440201c41300b84100000300e2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 124191969 1250 124190719 124190741
    0x6010317040914070e010c0b1b0c0d030e01060603151e0e0c0703030501090612141e0a020405060103090305040b090409060f09050111160305030604020d0e160506070b0c0d 75
    0x10030221102160903443c202088a07644049500402c3d07520581d80030301c54440080364008801003096840743d1010502410200001080c42801e001015030188184403801e070380c3e0306640d00069000c4c44600762a00351800c0c3da01c82010306141c0200d100b080b490b060344540503142c8014104c2c105a40400703615001c041c550780f14041c40400700c0140064003003c54011b1210500943d0203004a0f6240d0040d04110781c1c0c00e10480410301180701c0c00d0000181e4a4482c1c40b2010410020740d454800c0e150380c030000c100c860a0281c0001d80007900f003c82146400d01c00c0f00d030059000e10b820894101603680103801071003035005d5031524204c0420029126070319900300e0000c160340104140666445002540d0103001100000c6401d0750912160300b90061449003511801619030071f1070700425080b603c0559042d03101034103a9412079001c2001d0180a1518054030724034aa40707400402c00030340814058010208940c006520680080190700041039604002d19005240c10141560741c210010240c40181894201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 124193219 1250 124191969 124191971
    0x1a0702030705040606081e0c071b05100f021203070503060d0f060603062c0606060d09080a020a140d050901030c0e0d050303010603200304030c080c06040b011406070203060103170409 80
    0x224a546e0700803065401800000b4440390340c405049006110904100c440303819074081800198080741d00800d4204040761501400d00f0b20548417000305107074042038010900407890644842c00c8040c0e04101400140001000041c2107040008000b805c501c006091700b441000c0300380107941808040b03290407100c5503202208200059403840c0840c003914405440104045078074820010107840000860011600e1a01030700f0f855481000f0441d0380c0c0c0043e0061040d107507840404000140c60035009120500c140d800403e00b917159858540d401300f1040038001744c690000d60040a0168202d01601d00000007420f01080c40542c1400880b4000c1c00c0c003076181e81c04a482d80004040c081c000c00114162492580c06014845c5502418402c840307551100c4040300900f08001008a480f85c4084800c26103e5001540b0b481150414103160a40640b000d43d83d800541004101000c2598441c200d01c820540d4030034101401500041d80340c1405220181140c03144020a02c0d2400300303c0e0403107000c2c1841c154 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 124194469 1250 124193219 124193231
    0x9030408030a030c0e060a080c1605010504060209120d0c020d140a060903030b030304060905060304081b03030105040b010c12350405070603060b0a030c0c0b01140a0f1a070203070504 80
    0x10044c040894581000c1360000d4411005410603208960341e40c06a40c50f10f101c80d82700c03215008299030104034035080050304000040c00150302802110b01a034012100542c40341c90300e00803c2491740c1e070381c81d00d9200d40d0300410700485a01c1e0401c0c000e0400c03903012a00c01c46516160f0a16003521248069255001d00403581c00c0000c00401d03610030100e4a029a40130041e800985041c5607407445140207980129072000d008010914019005543c41442104c24a061083d819441c400c5104d85c80e030281991380003c00180f041741060300c1078003030366042480d01e145419060b1310703a642441101d00402c01002110404038010183e990111541c00d1030303410000c91000170845890303c03000c4040d50101c2c0c081c0200080051554441c3c010030b010f803801c510b100c6140054030300042c0e000b4120030354480203110080c450000400d594210060007051a001040411010802000400b40c1640c101c0040709144070000d1000055031100c180d0040a22145a0380e11982400020f14140c22980b149502c181090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 124195719 1250 124194469 124194487
    0x3060905041208010e0c0f220e0f0903030121060b1906110606030d0c03030b04050c070201020d14030114060403020904060b0102070b07021507061503081c060f0e0903040803 76
    0x403001d80c0c00381c116980d408016601c17803082d100e9041090301c501c80100c1040c07216038610070201c402071854855030300f00c40190b240026003141c50b059481c0c2c00b201401c0304d81400c000340c1d80494203155a001500783c02640c590740c1050416448400d035070322102c5403500c400441d00100f281591003c2e0301c0c054020040200400d075403882606080d07060055074001400b0508020084800144507405280010040c00030801e0200d4100e81301c51111400760201601c41c1c511000319201c0b03206050044461000c226a035948a00000e0b2500c4200e0004908000781c81040244c03c1c011074080d0307810750b04000070000b0600f40a10000b80540030304e400207544800d000381800b0800495031b00c010300d090707000c0e0280c0d2085644c9014011503030150000203500010381c141c0d0a240236000d10f009100b034500c656030010f074030083c6d10020001a0b01c1c0c0e0300211b40300140004c000c00c030620032000540038a00000814444141445004904034201f231140d18014043c0b1008204c0780ea20500a444c050070011b4102c9485840c06 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 124196969 1250 124195719 124195733
    0xe072106050406050916050303090111150405030421030903060506030102070602030a150608070918060902070f060513020a030f08190801031b080618190302060105041103010e15010306090504 84
    0x64910174400e1003100d0591501201c904400421524000c0186051a2400005440d0300111803010540d03400b4400000014503022002036008900450040d5182c83c01c115480908030b01d55050340c0c01519007140c560700040e51114644042e00e5000d140030941d511840c001c00d01a014004004081a0005c07082005081003588410b02c80e12110701e003002402d80c0c81d04140c0e24810187c80140c001011500706100c60384648a8000d10460440c80000d0f4055440030040300301d0b002908100c1d58080104c1c06007040c0074041c0206500074009010a004048440d0300040756802d080c400109904080c0080c501481400001d4409143c1c03c03c04403420341103c440c006000610034001140da4800440801c510a41d9480c002010f94030004014030700c41c1c46d00c02a4296440d041c002140c018071540720341102228600686074026442900202119410b1504202c10780e0102d80410600080038801000205c180d280450341019901c00e04044002171040100c0250083d600520102401c0401b40001c00c412 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 124198219 1250 124196969 124196971
    0xb0a060c020405010b0304051e1603060507110c030c0108090c0603010b0d0608030702100c02150a030b131406100c0f03120f050114061c0501080307150e07210605040605 74
    0x802c98082005030b0b00c454503004580003d682c00340c031a40c0142071610030240440706414040300104119041000d6030000b0580f80c03805600120398980d1140140b186143d08001421a8140c01101400340740340c108001c2031380d55030706074012810040104003082c5801d03402e0080c01d078880005040c40b903496856446000c903660120080440107880d29100180401001c02521a170715401050a41d6940c0c2c0d45100700c4200703951a000b03a0744840030109480f880c1d05210020000800301e07440104401942c00108210044100d0405103030504240e6019811400b030707030410342d00c01400c88501503070100d0810125030307001503410020300011840128030149600411881116410420b060000740d41000c03604064410a1103011051000000410f0052500c41c2c09041480300c0025135001c200b0480c0300c08001d82e40283d00c8048150000a07001d01400802031000b03403568440d03030044c003c10f03d601004d190b84200303912038403a0f480d07404254035a03412603900c003000142e42c1016060000b8100b50503c8002084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 124199469 1250 124198219 124198223
    0x305040506070305070b091506041d0f07060306170319090b0d090b070c1110020129030d1e0c0201030e01050a0f051b04090c1107030c0509010603110318010b0a060c 72
    0xc1b0550000d4a60100000d01405003078003013400c41c00c981c0b0340d1410b100141c1a46d00c86100325012503450705103200d40800664203a900103030700a10980789404800307012222641c100e128110000703407022a11080010454503249010700480702040d1a141c42140c025510303412101c1c00d9440011100181c509580064150a02654030b44001ea01c9000c001c5e07440d0100800d0040403114401408a030514104400103142400b038000400d21140e4181450600500c228509114611151640c1c5450508005440440215040003050509112100844c80b201000f180c1c2c20000c003001c0d80d0045921a8000030503481004000784424284550b11304003500d0700d15400c1a0491402c0c00080b04040b101440200b0a40e80000091605041c002c03c1e1000e04100003104051040007410b01e000d136a0104030150056018400300e1548500340340411034211300681c030100415082101d400401c0c2c2d0b01c0f408882d00160b207840d0070040c586204580034003410b414500c1e16446030195000280090300038800c1200703a8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 124200719 1250 124199469 124199483
    0x7020d0f1406130f0b070201150b0c07050103050702030732030d0f02040b1e0c0610090c0c030e120a2301060f080601030813050405010b0702030f15070507030504050607030507 77
    0x1da262404040705002c1104044c09a07007100580d000840c0d51540500c0e040350315440080b90b1148401c092108030200c1e6801344aa00d2000200585031000a00214000e040c007481c052005041001000355a4010742d1406061407104c140305038040c2448103a03849102c110a140750140c903071901501601c2e500040d2040e007020b42860610b90188030544202c50a5444101c1c411f420722403031151000107600c058099103260102001441c1c0405403c1124070b104207410740f122a044c0e42002d00f1202a100c24910410a210300c881c010800a030300a41b04880945d020b0f140100c2446088003075a10b811035804c07000d81020301400003100c01112031076800e41c109040300c1c021701c010340d80d641483d861031006100341045500701c6d02c01840002c1840300180108001100541082c1d91240002000c0398001c1c0d0101c042c00000182840460900b801440910061034024159200044400e90700074607004008d18100503000a1900405014038180c60140c1006030509071600b0462901501d20741c02810240c800c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 124201969 1250 124200719 124200721
    0xc0a0b01031101020a03050a030c0e0d06050402011d03070303030e15090606031915090201020a14030304060e010510060831060e0609070911040905071d0303120c07020d0f1406 77
    0x2d540009056400594156543c1d450018040d004800a0210111079002c011b584014210a82c3c0e0b092580f00ea024080e00001840382081d02c00540103a080349081c0030319401000400c1c0c01545c0202c0e070031007282c1d01801d001c5015102d03603140390300b020b07894403600703a29603114401d004500100183c40386c0700f01030580484240f000c481407801e00805548000516000800c000c0002000c00c6820400266106004a654183c0503507030302002c4081e52003a54810340d10100402043c4980c500030101c602285000800c0182024200c2d1034208a80d4001e007001c1c001d02201280b130303400310307209800300c4040c000c02c0501505014504050f9043c0b41c1d000e00b030ba101c6003001da2441042001040d002e006030200001401c0f0b844c45c1641050180034041e000e0160f4a009100008504441c1d010745d51150305665a0003d12041249910098090f4803880c4c500991051080e11200311000c80f5007a04820b42000e0341c0d88540d12880040c050300b4108100034203051884030448104034604400140407000e15040d2017007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 124203219 1250 124201969 124202003
    0xa032c0f0a0c0911040314030307080106030b010203120613020403050c0f010306051c020a09050a0c12020418050402030f010905060708091207030809100e070503010b04020901051207050c0a0b0103 86
    0x2450510a8000d0404520402c04001800d00ea41c4600c1341c80407000407140c00c0c950349840751080030b203510f01a000141c0000041082c02c0780d101d0b01c5240941018202000a084802d000035601d02481b00c001e10800d29a0340444c14603a2034904c11b50105500102c00c0d0754035500ca190194a8005c0030b1089401030700022200d410035806801450281c0b10044c202460141c0200112448020480420303030308900b110318081140c0056011b83d600c200c500e00008141494412001041102c0f118a0800c1e03251040c40705014041c00300100d00b8000d40002c1000c42e19032100d000007070401c503002494904541c40c0ca4605020064041350b12482501c80340c488848945d00c0d208541d4036150084d40400e510031003081080c00090050107501c1c1c222a59004a40d0b014030300d484030b04222001e0070110012503001002c02c000034030b001d00034212003140c25102941008540d000282040c041e210020110006010004240307078401e00550758101d190408840c0d980d141410016103d040c280025164000310a0310b15030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 124204469 1250 124203219 124203223
    0xa08012903060402130902090a06050906010f02061815040506040201180e06040c020a1406011a1204030f05160c0f1401020604120c0209090f0705100c02060a032c0f 72
    0x40402405405800d030b03543c6075403c0003401c80d290138150340c1d00c5613a402010050703201c1c2d541503841842207800c0000e846040404000b00d44000a281078100810300d88842200d51f400b00e50103030010000021118110718400322182000e81400c0f20701c2c4140700311020481848030014206001e94000c0c2c03a03221405050048810303190078070740158107022200c5004503409083c180d000c0e0320a01e02c20301c140d85a040460380c40c5d400c1e00300302130189a01c1c2e03407224005000e6030301240300c0c030b400001c0c03111010340c50b0040c030025017041030000030405800d1000c80350f0191b8040d8003030011030b400010307035031301c2e8140d49050f503e020401d00801e401060150723900c14801003401c000042c5000040c10050700248000d17a215650b100000003444408010800203042c050b0060f00c071401420b0207200d0500291408441c010010340c5000c449034061445074010b00b075500c2003190040e500311403050301901e4035552840300d290243d010384001d0001481c42c4072494405811750f51070b10b004900b01b410701800c0e05c1c03140b0502900c2c0340d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 124205719 1250 124204469 124204541
    0x30e071e0e22080703171501080604090b0606071a010b07050c01030c0e0d05030f0708120709060c06110f0c0d0206060a060e04180501020705070303140f0f0a0c020a0801 74
    0x4800c0c4442c01d11180800c00e5180a44102c504c240313850000080c8111405c0722150041e10b00507420b000e811a0007805603001100030354803000940d004c20040e46c250311a504a6040035118a01423800040c0b00401d021036030028903a40071880403500442d5950704901881c1d503101540c10340e41030042031090303446588070b802039101550a40d680c900c003000780d0808001003109008001c54803840100004007056400402030a152070265001030b8940c01d0700155130401d000c000744003c080000c00b4000780180350f0008101c441e11340d004900041e503440d4035050048180705920040e41600004610480301c0d0500092a002c66000380e07086c0da12540360306041c410000807901074000850003004c0c01e1100750030684d00032180546c681402d4490618035032500340c2268081c200c01e555980040c54244103143d000020606003c08201c28a45028014807415070640268080100c51000000d0a0b07018075204241e45016190021301c01080c141d1b44011041c020f00190350400402012586600a0501c9441d800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 124206969 1250 124205719 124205761
    0x605040308031906031b1a0a09060c03020c18190c05190504030206030421091a0c010e0601081b0607110f03030708030907030b0a180201030e071e0e 65
    0x42c1c11034031102000e0610000d25285008203980d510300c008082000554001401e110f0003003405146402d0203450120700542c0007086200b01010401c401d002988041385801b00c8900d49004d51580c0c216140817400c0003078510480354001d00510846081c0040071204900074412001c2120229000103032a409603017843c1c1c00540410340030b03c006801400c0c01400c82030300310454130304580b80c207890364001505604165419900c407814620418001207010152061501e601d0829040c100c1c9050340440c1d12501c20703030989440007008100d80081100c25002048405070b5441a1100d668440850980d501d01683c00e04090f00c18091a0480b00c2c10607500b02d4054503007000b540c54a0385058406d00569100180c54107030544010013602e0f0105200c600614040d0600c0b00c0039005562450804842030440a801c84c01103529003030140d510709058030030304142c0315030a00740480c80183c480609420101d0552040c02c164a5035180100d016052010a070241e03400410070180702d81b540c40d86150614000c42d45 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 124208219 1250 124206969 124206983
    0x312090b0703050918100e0705130b040323060402130902040c0e0103051305210408030403210921030225030204050f04020307030303022209020a0305070806030d05070230060106050403 81
    0xa00541f0300341d24096600080c281001c1d03241004040c0a84600b50059100055505c0007017828010001850071400d640d001d01031005c0300751608902e0b074503158180900001d1007140c904070f002444880c2c0d50041c20900e0340050003000801800c44000d0810a0b804000f9400203180c400012141c0403c803000070031040d04000180413138010b19296040000b440360080b0302c10301c014000014901410801031000d107200c0c48022a070201900c5100e04503240d89800d450902c100e11a00744000108800c019014509640c2c001c040e4013050309090341400d41c004d10b40440160050750401419541070040000c4910a850400c1a59510340302c050ba025000d590095058208440c00c1022078841d401408105c035102600c450000d0a0245810f00b1084c164404a501a0041460b812954040c07007016405406410215107034074202c00000c0d1a0707030031444904144100414100e040d900c42d10100010f103001c1e400e03810511010080f00341d00c40e280e03000d00c6668501c607000000c105248100150340c21203078440c0c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 124209469 1250 124208219 124208251
    0xa0f06080c04020c01060f03080d050c030705180103060509070c020913020105070b09120406030c021506060409090305040b041706090a02011b0f050109141006050a0312090b0703050918 81
    0x81080b020703600600c4106a15900c42c400422925003040318400210720900b11300b951800b485040c4020b07903600407e200c02800c41401080301068005040b40e1120b21030745030015031100410b0041e00104810342205400c01c100b00c0c20090745a401201e840c000314005c0310b0300e06003170350341c40b4540c0005050343c00000d00040061041c0c03c00502c82501003600006448180c601d0720311041200c050369000380d842140060384807000fa00c5040e405010040404060b05100c092624001000c40e4240c400c40c8100310045680d409418207041c400d03415603014020300c0c0745072552140c0c2d89803d000076104650100c5210700031940071a803900d000050800d60154180c5403000104100c154412900c1e110b0344c0d0981ea96401591010001071081c441c2c203600510583c802c0000002d040c00ba04c0ca0028000303000d0143e079141c41c0e014040c83d0b6a444018048a501c026054800e409106c012502c80c0441d5101a110760404a42300c4101900038000d01031203882599905e41d8a0110122400c50b0002a51a6014900307034003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 124210719 1250 124209469 124209493
    0xc05070b09132c150405010209120105040c0e0c040e010906170d1205041406040f0605060d0201051b03070215030703050a050402130c020f0d0305012d0608070311120a0f0608 76
    0x10400b00543c14055094410008a0034034082002500302c030b00300e8959500207085030303041c600a01c0c0200401320f1980204075900c0c1c0381e616500865a640074090749945004005948181c9000448000d455504a40956540e58a42c414041c0c03800e030280d4801c80c035641c045903108010000301020801d8041d074581c2079120000c11ba41000f8840a4802d231211200100010408042088014000c0348103020001c00e01d002d40c00e1800c11108050011480f0390807150555002d40c0e80700040e59060303c105112043d81c132822400607480c501c1240c400942011000401034110b028107409184a040c4a0703c1c140302560b035141044c0101c920494000750300000b130b884a00345110140e4000100d4009500407920b140c0c039030118040c80c1c20442c80314440001e4442006001c50521900c16144100107060741480c90f007255840e9040d546920300445040040500004024030301ca608024054181c0c00d03000b6640e090328215080710090110b450090040c01c0541c1104003c800b0710540d012100c04034090700c020f103401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 124211969 1250 124210719 124210781
    0x11b02060f0a151509150509090603010204080d03020c0703120804030e030705010c0308061503090f07080a03050403020123030708062d060a031410050907030605030604030806010c05070b0913 84
    0x85404d42c08104080001040c03121861898000d50001d40c0c0324191076a080c00e0405c21a104014500c034040d03401440108000d40000500101c00c202a09000da280d07500c560400c0d282290590018003034808181300c80490640140065004a0003a603c4100700041c4200380359076801c2c0341c071925001031440541e400c0030074807400b0040d03003003000248a041400c190840140b5160000e4075260000d411018098400035801c00801004108039005844901da090302c000d000d80c05644000303030500412004410054203441c107800c9401840302242c64482c20881310060460300100c48540c0a0b003041d103101d40341c400c6c1200c1d10002203d0014a00c1d0840f00102c0103011141c0c10181035a010300d91940c3c0b92103410401102ca861081444210301e0340b40741c2c5850100400303100050030001c189454000284240d85022411a80c4240c00d428041159100e0f840100d0341e00801100c040c0503402500740100b1023180c0c400041c101450110b03103018825680513602c0d412140d00014003400840156120071a0002c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 124213219 1250 124211969 124211999
    0x1060602031905090d03020c1309330507020706080f06100509040204030c08060a110313020d0f021c140d090e04050705030d030f050112020d030809011b02060f0a15 72
    0x40f842d08904061188021550140f074100c4210096001039582c0c481d1810441c01128200320000800d20a030011520b594400c030f0100020107801062240000d007080365070340740180d02c407900074000f08058640700b440291200c100b070166400003032022002c9011803c0040301e040c01075030000c1296070401c00c50f000544140c1e12849140b030301301b6000e2000001058100a1800040401c407010302a246000c010050480d0611109082024000c0c8203110b259103041c0e1902d92090340c182c404108910150408090b0000030781c0c8001e610950040100c400c09420045c0c07860703694420302c101c0403821003098400e9198000c00031004000750170040100300c01700f601c14007180c006015901741c130030403a2030301c001c02d050050248004001c03948544d40705503102001d01c1070b00e00400e032003400c51070047c2c05980000c0c010409000081c0801001e4004503682d19030a5000f6091860b1074958543d10340c1c408a4040c1d2148021503003404029120000114905158018444442c0b1035001c0c0c02c1c03806042001078805052 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 124214469 1250 124213219 124213267
    0x1d07080601030e0a050708060108070819020a0f080a061103090309040902120313170705090105040921020c091e04030c05010609060e04020f0a06021b030102090402030a02070506090106060203 84
    0x14864907800c04812003440304c003c405016001620300a400c01007014580703001a48401145e41c0b299800300103955010030000b402600041c00c181c000c100c0c031300010329495100e8020141880c105280010792100010310301b410144260000d01098074800303042001030004035903555980d0010010780025181551045880f00d100407c00c25207080c1c10761506180da00403200104d454001404144840f00c154410f100d2100d15610041c4881e40c1448003003014104188a00da000c3c2e170f111f075501001c01c030140300c0000481a00c920000d00100030110001d5036030302da01001d070307000d4513060f008a015043e1010710060321014014959001d52150396048600e03004241051311b06550f50708020407d40206d00456000b42100c0d9101c200600b040d00401c00310307501883c4801d108410400d01040250303000700d41c105c1d0f0780384c944008041e00350410002c0780c0640700f45142250b000e8800010070a07803800d00d9020b0300721280268201c94040d500c00e02c0440c01c84101d80103075400740e4401d004010780e40500511141130a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 124215719 1250 124214469 124214471
    0x1b1e0201020a12090602120403030c080309100e010203011409010b04031713030b011508042d0204060801022d0306040f02041e031401140a09030302070b04060207020405011d0708060103 81
    0xc80d2944074802c20035400140100014040913080008130307810031440c52404041c80d00c60385420304c4e5a80180c48800070344001060b42e0030100002d80d0000d400c0c440c001c5101e000d40b0090100041901656000f0f50003409060601c43c2500310400450031301c070820038142c4040c4180b60f898075045894083d0030190074900201e554808209080d41d0300203441400f0011803140c40c2c40c0c412541081d240320807901844c10101c00f08001d441c00c020104084143c1c071401d0710400c1c00b100c02c1c810510002035904143c030000203904181010000500b0450550041c40c0d01c43c003c00c40c0290054441d10450380340c1900d000100303130040080c404652146403551002ca01c242c40302e8401407030705560702510b49000740d030340110120341158080d040041c080c1c01300d000e04c03000c0c11107002004030002c449501d40305100007501c8020310b1541d8070107040406000fa0704035400d49800203081180762415203485d0000c1c0d40075a00880c09241041c000203840004000009004a200c2810040e6503952a000f21401000140b80f18101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 124216969 1250 124215719 124215733
    0x40f18090c0f0305010c0e0d02040908090301140108011508030403030806040b0a03120f020102040812090d240c0509010806061e21011502191b151b1e020102 69
    0x151280c2071020040104400c0008035a16505155084076401d4012a003402104a0002d04555425458101345a412100011990180d00300104240101d039015038040d843c0c4048640c007541112800760403958110300920001e600d98601c2c3c4001c0e0310522404040c3d500612045c8002405001c10307a81c403850241c4005171608a210008050501e41d6105480d507900000c101600320760b03c414003280030b00c180d00080d40b81524000896640712408100c41c2e141c07000c042085605540d85502c01c3d0390050304200e400c407140380d0214a005200194110480d1414681320703404440c00d008900340d8954000584603201c0a50303600c01031201d1070307100c03605240080070078920071800e00580c200980b01c803101204900c0d28505035070905500c44241070300035860b0070100d143c03038028199001a044e102a61590b000c0740445080b450010350031201d09004104540040300003040c45900103100004500c0a41d95110911005818002c1203040c95400602007120008060f0405220354050754030301c0340706104039252 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 124218219 1250 124216969 124216973
    0x30403080d020d1a040c030b06030106030c02150411181501050d09020a0e07090f0506030c0f250210080f060103020a0c08070809040b03240a140a1e02040f1809 70
    0x1c0f9150184003110b0256003039135a12803070400f8498591b10a4080c141000303480101c0002440318001440b60204040d00c4260302f1010310310a110070858102c0f40d6121032202c0c2800d2a1045402030040c40e03090080036131741d400348442c5022032540c6000d1a006c941090300440e070701d0011251a0700100f0004003050711031541344010b07224090140d0082c00094038118041c2005000200105859840b04040320b210310003d03c4140e9a84044a0b040440c0104841e90f52140c1c0c43c2c089140c0c0503400c03462603566100480d08060190480ca00546544210f070b0a101a034107000c0300b1303070b13107080b0640759440d00702ca6020025400e94002c1d4010001c1446a0601c2c1c09068220396401c0c4441d80841f070100c84040d404a41d454690605000c0d079002032400710003401e020099000741d0032545d144803c100e11b1303102e18140464003041841d8802c042d0307019101c002c034903107217040d10400000d080f00b42d0910350680c10640c405003890400c0d10945050381e2109034512205c83c503050000800c80705400500c41c1c0c0b40d643e2102200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 124219469 1250 124218219 124218221
    0x30f0e03031b010501081501090207061803050403150207110108040602040f090b1503071205040f0b010b09030c031204050108150d050a110d08030606030901060801020307021b030d02030403080d020d 87
    0xc0300c09030107161803441140440320b609440040e07010f54a10b80c441c3e46400c0702a4074004c200c60644640307600050f15035030607082c80c0f4050724200c0e0a000d041c0b01c80300324600905038060300520a0728010310398074240b440380da03840b04100c0c0320b0040e01828440307800001049a600c540403035900701c0d000303c40c0036040c10307120707524100e10189503480701e10071507501c1000405604108140d504105041e0440c0c904500c1c1000014098064504540000c035941d039002804101c510104545c0e4940c0000c00e07800190385950300b5007030765800b90405520038421442120a14640007440514008540e080c0300c1c202440d20b0300540e0201c00240c811081c100845903400410384402492403001d50242c03004040400680c10206800189074403010b0107000000c04400c00f00301200212504000291491980c0c1d80c2c038082618010050ba8028030b01702d500000c24002d40c10f0b40018424064081c4065182c500a216001c06a40303200d148010405a04140403c20101c2c040c0000f40001d00500103000d4a0007001c02c44d200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 124220719 1250 124219469 124219477
    0x613081b10110c03010e21041521050109020307110c0a061b02030d020601030314040f03032007061107050102070e0f090a12180b0309070e07050f1803010b1507030f0e0303 75
    0x2001540110820301003d00c10b450b40c1141c0c0b4007d807501510340b5013040c001c0e852000c0210f40da80c0a0020654080700c0303d50340b40030020070020b4040c07070802403543c60b60a202c01a60042e40c1200002c2c86004640c20555008200481003c0f1300800c1510b0b028036200e0b06a41642e00482408018031072101004090313103060090744018a8154081d00c400e604518001d030403005d400b408690015000d200c04e00002503c0c0555030140c98060601401c0307005040302101c4912038001c00340341140101403001030f086800002007012191070006480140b07407140b004aa88400d14800c0780441d400000105414603858000c0942000100c1c0c1a546200380c9a140c0000c1090710700f0394400060f181030081140c180700440e481001e000500b0110307140d402c002c0b114640d501030702d000d91031805602102040c10580107100f2100202c2e601c042c4241c40c0c0110003148100740c40140c0c5100d00a500b44801405545092a021005020311181640c100b0f4480e44040390000c10202c52070701071041c50502c101c05036500308050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 124221969 1250 124220719 124220741
    0x70b0307080f010f03030507081908010504180f02060705030702060c031909080303041416030602090901050105030717060103061805100501020c220204050613081b10110c0301 77
    0x11652418036800041c00c0c400d0040c4500401400b59005101c00400c1c240303007008803a01032800e6600d030102400c0160903803040360141c48900d00c2c0c000b40301d4211a0404034a904071041181c1c01c01c4116086459007442a4071400c00410780d841000c410001850010040c04480e401081101e0500d0300560100d8078036401280d095600341d00104500d01407454110301c90a20724800d141002c0700c103152000c51542c038000030b0001001c01034000b29510b003a8070200001c1c0c0740c0105e000c64800071141d0701c2c00d21030001d40c489688036001d064040c0021659500542c22240160b0702695101c4080c0d80701040c40540e0034024003017504160b110080056900b15594600c0d101d444800d6002510781461004021a544254003060554002032103e00039a03403090803202401d5000701c0c40b10031058802440d0002031142d5044030380d0040011a00c165020701d806403e00c00d450f080c8040b510f80c0303843c0c1c0740100c40803184004555440021000b00556052080b1021a08065202e0481350450f0803400020300f5920080d1203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 124223219 1250 124221969 124221989
    0xb040b03010306061a040302130b04060b040302030105090610050d05030702061c0e0a1110090312030504030801060201110d0b06070c080319080603030406030506060409050412030606020c1e0103020c07 88
    0x50090110300d1054500170301d000303a11107560a040b0200102a40030314840070344604540c451441d107c01083e0070a465550000703200300407031602d441d54400150000d0006900035880c01000881100000443d0f03405122401c1428550a2600c0d04202c1200c40c89a000c07204c0c1c7c0814801e140050716640050040000040d03100508a014080c0c071030100e60500d16003001d154880c01d641c0c0e02081520b0724408040c02c00781c40f6007248107140c50043c0c445645591000f89107010745440003030300c142d0542c8114001c034441c2e507641c00d0599842c1c0c1d049090780c0004215540d05401002101502c4d029503000c40c0d0b090301c000c0c2c20b00b400d0860907205c210921400d607100c01420b81000030050222108201d92880d00840c1e414a00b070309013080e1010035031b030b03010358000c0c1001d2540d588007191040e6141c2c000c0d94010039103044180990f20f0180761104c191405030706080c0100c4e0408001180040c000b0800c4c002900c0c0151605c5008003500081c0a030001c903802400e41031684c04c11103003688460600c860400741200c140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 124224469 1250 124223219 124223221
    0xf2a0907120e100e150f0624090901050d05030301050d1a090d0207050303120f04030e220501120b070819020a0302040f06050f0301121a040f2604051302040b040b03 72
    0x505401502e07101842c160480e000f051702480c01c9140000425006554000d968005684400226007011500420f210600c542d43c00b916100c1407155000b0862248161501c3d0b0700e42c0d81e200140051b11080c1c090060040d001071005004a080c9484904216802400d4049008c100c855000c44000c00c1595550380e150440000308196980410602000382405c0d00118604101048024440100a4081d110b41c10510b408203041c940700e42c9984240b101d0081803000c0d1a81c426080f40c084180c0385c079120240c8d60501000084ca20038140d001108142c0094071118960b403a65411141d43c100140341583c00108815030006140091020304244201d42e01e005a031103003450150070401036250712100030041c040011403c4ca04c50750082d2811a012140e280d903400c01c1d18640110704e0b412100c44000070250700010002031080d0050340c405824000c8145540680400391040f882040300481210450001c200c10401f0f402d06103c104240d41510b10018100341d02c5031050203003580258401d110143c8080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 124225719 1250 124224469 124224493
    0x10e06040c110d050c12030711070503060105010e01080405070e0109020d15060c0803041a0f190c020304170a060c0e0312040f03110d050d020f2a0907120e 68
    0x72140e88500d140c5410044490000d00481c0c90ba00d06581030007200300940400c00c0d0580690805c892025000c400ba06a5100d1500010080080d022020720031203900c02c201c000100c90030041004e0781a40c01c180d4520000b0642c03200152800c41018208498501c1203120018140b0107000006e406445c1c2100050380c3ca40d2007205010030f07110200c01e204903501414004109094000c01d40c0582254002e100381e449940700e06040055582d21507035030855101440070040c00c1101001513503c22003228100c00c0300b60140d40486030031a428640c000c0c000d40d104102c1440780300340a20700c80419030f13400c01c11540050500e41e1040f059680c504104404141e91b0000b2104900c0c0a00c012160001650003070381c20946040c0c014407414410744005000322038600003822032500d03a14407040d04650004211001c40c40580d200941d14003510314541c0f410300419000f400f03400808050341645480490044103030900a804201c40030a0140114040c85651010803040220314007a0a0010100c2005030040740014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 124226969 1250 124225719 124225721
    0xb041a01060e01230406030507050d0614040606020102180f031908090906091003061a042d0603021e030a150605010e10120507110118140105010803030f0a02070b010e0604 75
    0x20b003a24840d86001c0c1013118142c2240d07506035002c480c40f502d000319440e00c603440140c62900c584c030210041d8a00b06200070400b02070141600e644082d068400300906903072010200e00300c2c01008042e40201c644904143e40a1501c00d21040e04004010700341d80752441c11071041c40c505c0a642c201202d1035480483c000915151402d007490f0311000c140c1e0380d00c0d041e10b4040d0302440e0032400c40c000102919943ca24a17681c2001e01c134101003440402500401c035050030513602d407140c0f40c18032150311006a2074091003d1050442d0181ca01100e5003e40044c100e8050014108218007019594075014805c02d030507000071445840725180929080c61000800b9800c1c10001403400d0703d4584000d0080b112100b07250300203540440450072041c1085000103d6444111003151100080d2a0900e03556081c0494211901000400071048500c1144c2d00f00700b54050842c110f0a03540e00b446201e4864005100081141c90200c8140d80e00c9111004014901141a540c1c40100310081c2c00072030095403450100040c500381 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 124228219 1250 124226969 124226987
    0x230f040f0b0a05090601120e010603081605010c0e0d0803090a1a0109050a0902091807080d03020406110703030f140d02030408070614090c060a030615020307150b03030301030b041a01060e01 83
    0x209403086104d5141c1100060400b601c0c5800e03800d03000e9501d14001300a21360a5200002139984440516510078010000010001d0445400e840075441d110280d84214061102c0380b0f041c160140c02000102c50903181c1202d260002040c8000d5070040840110014441c1c805486a8034030700010030000b0b5042450070402c851000345411a020725152440015070744013103c00fa4400c0c42540030f000705d81c0588850301e09008090b800940c8030b00c0394070412043c0c10303010380142c005d07100300796600d030b80c0540325010f060f03034609482c84068041160040f88001503489000c1a224400d000d4614601d41040c06803c135080364011607040d030f401d00300451400c04000e01030050110086500401c404c3d01e00701204d4490b01c81d203203000350318031030000010f141040303501a030889402003080000200d0f000315000406502c0e07600141c000c45e07500c55407507850858240302d44600a1032090150003542580e095036206400340901403c280d5002c0c040402030480d0302c414400c3c90f80a031140b07545002c1c2510b0704100250000701 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 124229469 1250 124228219 124228229
    0x30b070309020d02041112070e0f0102070f060e030f1623031b03010e01020d140709141302041205011d0304030f0b0a090f080702010f050301230f040f0b0a 68
    0x41004201c2001d652080400000076030125030001c2d003c0380c0c00e80440007903c40c03620006000c40e071050810640a402c00340d42c0000c0e94055a480020102c880012a240c0d0028010340c082e02d0300d055000d22819100341346210780d681e230142c00c03a07250f0052500f00d40e00e8102c140c40d0310345401c090f0707a0f414001d1042d41d11201c00c407107411030964181c1440140005e603d8203084051104440c91561005009560035000424216a1617008540c5e51040000c001c0143c50383d50391111050b00c1c4c62010400381c6110300845011a02e4811440801b6864601002590324001341e4604545400348004502061010b03c0316101030301c2000002556450030004850001c1c200d0b015820503007041c0310400100780440c421a0b43c041c0e200100010640d15035006100405521030042e000d80d00c044c17100010000903000130706809000742c030307807282c0400044e804580c02c0c03109004202ca4080201004020440100402c0308940340c018481356140c5008004603081784c0700c4202c9684529141c00600009050504031200940 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 124230719 1250 124229469 124229471
    0x605060d022a19050304051c0c120b0103031d100f08010506090312220305030a021207020117181002341e0210050702040c111c020c03010510030b0703 66
    0x8880361508680320f48200d5100f00414400e42d07454070800c14140112405000d0040210901020003848440c010302d84000c00c940c0b06141050200301c07100310300a120b00385580303d081101140e0a555040364100c842d400007242965440c002801d06135a003680c0718a00d4102969583d00300a482c10004040c0e20040e13003d24000c140400c107650705a1404500e00d00d00454404080d40d40c0c405080340f9440c0700720f4800585565088620001c000c008021004102a100c02d0b42203070000c0b800070001491a1051841c024040f0340318003180c2024042c2114020783c800035a0f02d00e00340003004038203a41d0500001c10182c02200e940001e40c07101882c044c00d8641300600c03c00040d1381e2035031200c0c443c11401c601d42500c00340400406208529415646e24100040c031507010305a600e0506c16668064441d41140400300d10450078510244403542c45070004c1042000c280000b40b080380d406208501d4480c1043c0e0a100450007a51071408091301c0c2402124010b05210800018191950a085500100140c1410109 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 124231969 1250 124230719 124230787
    0x90c01090602030409110403050f03030709140907080901090c0620030c030d052205060a060506120a0b011112030709081606120e010504061b0c0f08070203010605060d02 74
    0x20a500000b5101a0f1702c2c004000622440c1c091001c103550702640e40000d0132481106010b110340c82002c8040c0d03000b24407a48a03010313890340b105c8014024406505903181c0021140f40050400e500c82c1c02803d40080340680006045c0302d9603101c2002c688080c2d04a100072400d13242c0340138415030070b4610441040102e02c01440c1480701240030181c681c81044e409080440c0c9035000b09040e1107000050350740301180c00c800c3c0001c281e09480d256031106c2040b240e5403001403904030006000c1c10b0802c125502d442c5031020354851541c40072525402800d00c05002c5040007001d0400c1d48145404008000c54070144085a41c1c4926044200a0880c4115003291801c2c1d00f1011441800c503021181d00350945400342002c880084040381c02c0c0006103442c9102030415801c100a00040c000d10364404101e403d0f900c00340006800c05503509451501c0903040040002c500803150001260910000e800c0543c030050000c42c0165440000078601d42154481c0144a940091000d60380c184c4103903103400e0044519075081c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 124233219 1250 124231969 124231979
    0x1a0105030d0c0308270609010e0613030f140d140412031b0809030d0204120c0608130311030702030f0f070e0106050a1d06030901060603060b070807020d14010212090c0109 75
    0x50740c44007a12035205d6021000051074149a00c54000701c11443e04411a441c504c0c00c281154040e100d40000040107010b00c001189000741c44540940d94181c05450b004030000c0a041c0407124078000d0001205101000c2c000d07120341c00e80a000c0d519070754204511001c0c450030141810440032101903401c0c0c05041c6080d2240300c41c4014078a4102c0c00700e116042070b90041c0c5d01e04841c01c0c1188a4134850700e04ca60310004001c9183ca0070b20140b6880c403405403030b8150041e91211026100240140c8401c0d0085600e4004100040e01c1070448543c0020351b0802e803803d1034050b0740404e280440001c1010000c0e000000e080034046e40820410b4014000d183ca608001d5141c0f0801404502c104000c4108102c6039000c04400703085002414031401c0d00292009540b07261100b078180c0240158019980001c0c10400001fa02440800c2604c4415801802c15840c10405908200310040c1011040b03805400384104402e142c2800c3c4054410240380030b806c0c6640f40b8150304041e04100645040d14184101072100303006d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 124234469 1250 124233219 124233227
    0x91b021203150d030203070b07030c020f0d020615030c0607030e01080c07120f0309020d03050307180f090903021207080706050108240a2409050906010b0706020f071a0105030d0c03 79
    0x480600f5614245145003030f0400700d00311f00c41c2500141000f01c01105000816034590b0096844600990a881e078108807103407180d40f034810403003542c40180e0100010420071082800481c1c40084001c00311103000d10b050003c5040d6800081c002d50201d11095000451540c210428981c40509680303814507003e45c6990705121504c400e8004010403403407036001c901203402940720158958000304a5040703442c00b443c004142c0e50048455100080c090300c000e0780303d07001d1065030740d003680c082c1e4a50190941c1400d4007030f070007015040e0080d0210700c9400e29950700d00446030300901c0007901402841d992002c1d1810301d14140d91040e8450200c41d844428107805c0f0301c8100c0c1000300130f0300b000c005080441d100c44040d44064111303544181c0184041c0300d400d811021810f8548030841ea00200c051226039202843c00351151401d101d81582400d00704202d40000722540d00400640c40b079043d80d282060402e450b500400d000c8081c03101805541c000c0180f0684c54208038000700f0765130340e1910f1608940c0c1645d0041c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 124235719 1250 124234469 124234501
    0x20d02060f060109051f0f0e0a0b03100e0702010605150a050313050106091404061406010c0305030c0f0409020703120b01050403080c010207020324010503030f030f10091b021203 78
    0x1c0710005105020403050b038410780340f03403005000c02800800c080140c0d2403d005600c0045a041c00461100780c10144194000c8501c511a040c00421001000d440d02d9081800c41d80020039800300e6401c1d090001c00c003d070b0004440e50041d40d06e580001010703420801803240804209003180004803052005840965101040f01e50003a41094030401460700c503c0e0440c0502542d4014405c0d050510203030051303801c3c0102482d44074a00480044c401c1c1ea05070302050503102c0d000c5e550940040c40030100340740401d01030f4009680140151420300d00d0040e0b02110010b0503041a08080c040c00c1d0005640c005040d406080082c140c10307801400c100c402d008000103051881a4072000380100408604c05040d65000c2d4160341e621a005030640b0b14810710165115120440040502e50818801002003210b04001082e10440c80c6c1808001c0e2442d04c174040300300c0802e10001e000c5004440e0700702000c65408501e01030000100406d00f11803444158080000c1d0810040380d103409003a1005000304012091541b00340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 124236969 1250 124235719 124235731
    0x31d1905040f0905030a02010b0f1009030b090c03070608011e060503191112011503020903060a022a07060f210c090f08030d18031e12061d07020d0206 66
    0x7100b007035001480014000d0154003030458040030071001911901034002810b40d00040f1a40c1d00c0c17a07851f0703104100c90a05e0031403004001074017000050002032103001409402c6034846080b205603600841c0002e00d00600e68000300e001400020041203c2101c2c1021030441d80603c91046001c1c500f44280207000d8000101258850080004010340e003007070039400b8003c1c11000d0b402003a9121408405401103080030f10a0300406907005aa010b03511344a8400e1351650b0b41d00501400c802e881d035141c1000a90401d951b014110040c00b594000142616294202446031203406080f45520380302c4082c0c019035400b0094030a006420709071403103082414400c06140070803c6e80001316440d1001080700d2460340f503000385c80300541402010800d000c0c0000a002550710141042c012500c8007018921458107105006000c245040c04501c14180d00b03c00d080c01c2c841d01858508241c03424a0042c2c000c0c2c40d03c5501c42d250544a0603240c460841d06510396a9004085000400105101e01002556040c00a04c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 124238219 1250 124236969 124236971
    0x1206120c011b06050a09050d0801030b28050a2a0207090c0e030307030c0c09090206070f05010b030d050304020307060809031e040f06030b030c19030f02040b030a031d190504 76
    0x10140c0101d0b2800e42031461590411400c002c5403801e040c3d000010141241d040d656031190300d58858505d07100342d2442c0d068a600100e5001143c80b80b060158180200000d203500b810320522440094000c00e101300c91280000e10300211300c4004650007100c034403640071089901c641c0002074403400660001050821103034103010005400d40d5200045602002d001c0b0460740c1400001140000c0c558405400321285004a1010700051382d6640794204440500304000c1d0080c505000c010046030703620084040c914090700c00440c015102e0b07c0000e00304810a03442c0360101d0404800d0005500301007000c070000d40385508002c3c1ca02e0800c0755076580d0f00d028800c00c1f180342c002c54440503144600418142c1c1c0040c0202c81e102ca105684408029000e0a010f0300918040d110710141307902035150462141880c0080c00842822250a50f01c03183c40103000084203030781158803100c000c10f054030700b0005100818040c0e554079290803001c480951b0308c1e00325042001d1080181422109840700000300d00b004039001114 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 124239469 1250 124238219 124238237
    0x405011a09060c070b1b03030708011205120f0c0c030c010e0d1103070b041701110f0d0b0901030c03030f050a050a110a020a090203070e0103140103060902011e02031206120c01 77
    0x7440a120740c240105590041c00030001d24806204081c2c00c0c3c219030080d19001c6c0b603600c00e000303503a44d0008a5042c0000b450010040015005007565442c540380a00103480095062480d00404c0764002c5c00178541c05100000c5000703a4000901c1102900507040b000b07815040f400e900000c2844208207135880c4a016440f461800700405c150350849407420150680c3c25403a52040c60a880740c0103071166046a458400705103066600c10300ca44d104600700241c1550030f20341003600300209a080480341d110a03d6440e26020440d540c3e941006000b2351088954040c018214178005001100c8000c602c1e042c45010f100d02400103030840159a80c800551418840040318986842e01d00081c505000e50001d4501001040740e0b13859800071441000aa2204920b26803da0011011540540340c5550704000900041c0f00180891b0031401c000c60051404c0800009072041901082c0075a0300b04401690002410f420346004011000d079000104070340c60000014040041515101d503088210f04002c1181 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 124240719 1250 124239469 124239487
    0x601050c10050403080708090a03120c020f0a05010204050f010f050d0207020109050907020106090b0109050a03060e1c08060405060105090607020f03030c0106030b10051f030c03090b04080304020406050405011a 92
    0x1481068a1a4000600040c1010305025000405c1903868900103124040000d0750024005040e41c48207503d591a10003c03c0b020092400038a64801c982c411030040710b81c50f0305403000c20026019000d008500040e501d5142c0010402c03d880b0740c2c044107051000c40c18802811540150507076031240b240c100013507070f56510307403004039a1003441e600810347c4054080c00b80220194154051010382d00700110800c0038601d00001528090824800c00398081c2503043d0520000d0010b0300900c40c00c52004c03040f01d001500e41441070500071320300c007500400146803504210051400d4004c0942226080c02c0403460701180001094407481429000f901510310f8002c5101982c030200200c0e1106043d00c0020441542c4070310342916130b80c030b094038508038524912001083d10b1408484084002c0480036034407211105802c2d054015001664400c030a0603075442301c18000c00c038030301151351046100c1e50307140b5075a10b001e204000c06c40301c198000f00e0045140c41c00501981400d80742c0ca54a42d01003905840d116800c00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 124241969 1250 124240719 124240723
    0x9051c0303090611070c0e090307060e07121412090f09090718022805160c030c06090905070c030f12060807030605180105040201091715092505090601050c 68
    0x10b01d00108202e14080440d00c2c1c002108001e04502841511a124125919813200e481440c4c20350394442150400c00c145e41c005411507100c0a1480045402d541850307560b0711060401903800036040c3c4003401600303507035000d4000911020100581e201415414015000c001c40c0c0501d8071110306502440ba0300c1c01055584008205400050000062060100c41c204000902940205138020304c0040700429001500c1c8541c3c0402e20782d00c1c855034a260501880302800070144104030b1081d41c41444c2c408001c00030507900c1a50001800b0582c503030011341440c1140850803110010100030802c2030411544001070ba01010308070720000185407903220110110700f00402400981e00040d0284100d4038000200030440d0007052080c280409201c8241c80c010b00c0850981d03030115070003400200c961a051140115403519030407003002c058100c4581d18118200d050ba0703490240c03080344046d800302da403d0815608a00e001c03440401032441130040c0c2ca19080c00b1030b115400140641c0d050090105030340c050042e003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 124243219 1250 124241969 124241981
    0x60403030221040606180203040b0c0307051b071502030c060103080d0b040612020102070f03051504061e1a0312090d0305071a010617010e0f0a0b0409050c0405010609051c0303 77
    0x240b000c06001c0c241807901100501e024414804141d81d40c4131080040c07601c1c0c0c420790340f04039040700308000c89a13900c40f0003150650006000c881882028842100002e480d0581081e21041c0ca00040c40e219050454202d07408070200c9040b0110342c010024098452004203000341120381c4401c03d540c81c0d0420791281c2c0040c040c10b02c28103411500d003034000114050791010301c2c03030024000c0e001d44000f01e031a00302061030902c15000c050080d074000d080c2030785110b41c11541c1650080c01524002824083c559140c070b0041c035000140c4a9881d2151420390081c2b9120340f0725441508c00310000c0030407642004e11007900d4003271078005511420170368001c001414024012914080c0d402803c4100540411000b480080700a014080006086d600100000b015845d0541d0681d01a140007500703070b40d00c864000942110061100c200c2c5900d81d0710080440c0c403180100d00060744100041d00010b240c18013404200d0328168045403c02541c104104101d0700c0304280e0120550b40ea0301140c00700b90039824203501401e4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 124244469 1250 124243219 124243267
    0x30e0109051009030c0b04060207030807030c1e020411160201110708030a020304060f0318020402090f040f0c080a02040f05120a0c090209010e010c080a0302091201020301150908010e0604030302 85
    0x8a0b2005545456000c1c0c0a5010b40344130b680c440d00200c0c2c03142c9208500b80607901032600907a0029009001203500c0c04054442a4844c3c500390041030143d64401400300440c0c4200c1c201c5038000e05c800002c51610b401110102406c00c0c02ca1030038103c0c1c1c040150310030040d10b000641403288448961408210500252002d03045050440c0e43d60707155414000c1d9030f80e00501c0f5000000340b444206003203041c4a4042c400b0605c910794010002c2181301d0f02004001d41c014252550f2254003030070b41500a80b203500505940c5070306080c0002d00c4483c40003029000e0000207240c440d0007841007005105240c41410214151001501c1040c070412200640600d0071b0540800680212200761001402c0c0800b5001000d0202080c1d80b000200070302080152416021008010f00e900018019000f40600c240d01801020f1002041540021000340c5440d00f241d0080e04410059003040100e00e01c1c0716007000703030340c1d0040c403c1000130450310301541c403515140c80e00a0170050815800054510341c031030086103d03201c00d00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 124245719 1250 124244469 124244479
    0xa03090f080405090c030408030c090f03100501090f06030803070c0305070812060109091a010e010c240e07120615170a0201030509031204060e03130f030b0f0105010c030e010905 78
    0xa14148401d00350400e1148600c07881018000800b6070305c0b800152070050b44c1c007042e45d50968540a216101c0c030f8101c4a40c0c1798110030032120460140c3c0d0200b0400762610788400340081c15504144011050303a00b200408440300d41000c80800009421310112a80702010b0302e000584224603150032150780c0728840001e8544240800c56801c10000c0881140c011002600e444d000c86a030349021409680c2154400000212451800b1f50702c2d5002d1441c0003100201450581d441c0015079580c200d6201c0e1082c05510301d0401c504294212040621070040d00e00c6451008003902440c1136203081c03000b002c1c5000180310075290741c00620722205071040200505280a0b4034140071090514441d55030380c011400380d0002c4e043c600840c60049002c0101c0d00a050b50440010240c0c0e15038a621002d4050075030803881a2000b00684080c407032210304040f0142c1100c2581ca14550b14500b480400840c020b400d0340c50b204090301c01080300c0c4c0e81242c101c0703e005516042058a400070100182d07282c2440798000750b006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 124246969 1250 124245719 124245743
    0x20a0b1b18090a0e25121a0619090c1e05090907080631110304050c06090901120c05060415091a1b160f0603050610140a0309 55
    0x380042030300c1103400e08400e03254050196a88018941528070b00c1d44c444802e900151064840303413242c1c8111030a00c2409607000001690303100e00c8903400c140d00c42d9043d00c0d04922100b8100351300c08030000160308101c1c225100301320030070340d010300c08240310071840f400c00c89580d11008031215a000e498203c0382c80c03c400260189a0000c1040038180364006683c4034804c4940000003680c60b400b403100c1030302440e40540301e41000c3c0c14541c210081c0d10b4400a604c0121640c440401003020054021500300c04c200302106912401d0502d4110b01e4403900480d070301d02c2000244078800781901c940150604450561440700440c0c4501e08010552000542009801032070006002c11104070740d540b4071242d12070070b40d20408800d94640074002142118007400090450402480c001e0f4002c000b03045860406842c2030340c2d00b646280c0d00c0c01d1105805070f0b01528859000e25004c00c2256010302c00c0e254080401d5924030f44529005a000301304005040591068100100b06420039503c00d038012a5000e078014104504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 124248219 1250 124246969 124246987
    0x170f030a120f0603080a030c051b0c010f0507031d060d111806032e0f0e0f0109020309060c0a18030807020301181e1707030c050708010c020a0b1b 64
    0x841c50201018804031420300302030a981031a42e2040804803174000040a040c002101d1088000d41a8951907600f040014005a140c1d41701910a840c05441c0e104020100040c01c13600150480c080e14600d0424041e05106140c04070381c100c908801803070700c0b0442641d6940404000102c550090030580002c00b40b408485c0302407995900001c00082c1380f42c21503200500c00400400540f44030440301cac0c1e03000740d6909020500d80e0810446500511340e400c1c180b808035903100d88804a400341c0782d0380a55524483c41d000e009101041c1b2400501600314684250310f98a400c070307205c9030307038080240000350000000511103070360a12504c1101003031030401034154030302652814140e1060f04982e0042e4032035468920021000c500b540845458039901203080c1000215504540d005008004015a00e190202060030106440c413401800c01e588281c480c00e00d00006070a0075031501803550480815689031680c08840f1070303000942c8205903540043d040503642d4403070190300304c0740c1c58000008040d81400f00d50b00c49 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 124249469 1250 124248219 124248227
    0xa18050f0601081b010c0803130f0b19020c0606010f020f030c010207060c03060510030b031c03050a0f0b030309060f0d0203011502010e060f04080304030c02130911030f07170f030a 79
    0xc100d90080003210008108602c44c0303091940441c454901150785030808000146c5004003440c1d21500f2000081c7e03201b0483c0e2103402c4200444002140c50302d14160070810103007188400c000400803201c1c0214201125200f0040d03840302d001e424141031004220407048454030070008005000701550a507912b90340e003010020f000c0d400248d81107440314280301c0e580565500c24071aa5007181c2008001d20380c15940c4c08000d400034101810344d507805000e46600c0d0411002844c0041c03c8400c116500000e10746084581d1100b150070004a0161081c10006040300d52f86c1c0000070b648030044111812683c9170280ca190103018070070001e48070860750000c80005140513202c2010110143ca94000b8095043d24034059a15800212400c04410a154010401040f20030002d940d01c6480b0707041c690350092850700080c03120020510451401750303da201500070040785c0e501d0708102030010303030040441080c481d100c8c6440b4403081c0a1041416000d954843ea103140403c20031406100c65400d032a0742e441c62501c010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 124250719 1250 124249469 124249471
    0xf020c0a0b061807050a02070906060c02010e10050406030e010902030601030308041502040806070522091d060c030403230a02010c03060509070c0204020d060e010b040501140c03030a18050f06 84
    0x65039042628001512904140603c40c43c5070690084002043c3d45016098610b6001429610110720605401003110b408a1040e000a0459030b11000800081c1d88001414264818041c0d409031b0301d200841e94006400405580c2540d04908002c11100c9950000600410114901943c90312803103000009040d00440c64074000d50046803645001c0c40d0101c1400240c0c800e6121304442c3e0f600241c00152100d10480280014801c4040c60225014400840c001614996000710007019650913445c5031541940c1e80300f051035050740e005040d4515000e0854509804001e0002e420b01107851140c6910001000d0b80d9410400d200c88219180c09034110021700801850b03880341c2c0420318102000c59140b4065030400d108000a5036981800304081d828030029401c40d82207001c2140d105c004c049090013042645601800400d140151a07034509000100000b8a290103810200c80810424000181c04400c59611003030700203001c1380b264081444a003074084c404001400e91300518005100c0c140e0301250003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 124251969 1250 124250719 124250723
    0x106030b18010b030a06031506080f010903020c04020904061a0d06050901080a061116030201091a22050c130b010f02030307020304061808071203260c07060f020c0a 72
    0x400c0040c0414091200700000045604414119000104000c0c90003500455100e4103080f03011403140e41c0c0e562561140318004940e4040d41d80c5944d411f22120008000204414065100900080480c4d48019403241300d000740f52806542c0010341c0c03803800d4079660040c00052400301c19070704040360810f44040842d0040c941c3d1008042c01d1041c009900e25001080398181d0780b0a101802115100d0754981004104d000c41da40c4940c003003801001d82010302d4010000e80280030f90001f160100440c85c014244101208607200794840190902c4448256031480030300d8036251031034216030074890341000c038a020000f00119500020640c03000701660226041030b0107a102c00c0c0c8404014020003e01a6201c0c0802c651000041e44140010403e441c400c4849800c11001245c0c141d419503105d100f40741c1010100d80018078621741d0000307900101a4080341721048141c003002d49081203074410390098950344001d04003c00101001c075902003403018591014000c1280380404660b603907100d8890540f18078940200b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 124253219 1250 124251969 124251971
    0x206030709060e030106030c0512250905010e09030703120608010906141b0a030234030912110d060b040f0b0102010b04020c071205070e040503090a050612010614130e010603 76
    0x4803d05418140149025a68007148241400e400e200c00d0100911385203040b40300d1441245070a000d40c415005054542c0c4205080403075002c0c2c1800c040905803070045e4042c04100789404104140400048103030791aa90b4145003168072440103001881c080c0c42c8680010303041e546040c422808104040c2e02c04440710000c04448a000d40e10b000c140781e0703c03520780600f5400039082003000c07001c00740c03107070b8011305695003c05000900c00010b81c0d0a5100740136942c040010b01280986000c06140d0803002040041c184000c0c0804030170250fa48865020885484076405544403480010410001d904204125080a002080a081204440700141480495203409946818503071416401d040c000c407603020402000509005140151034403102ca407800c002c2ea00f902075010040b0301e001c100c096181c021130080d00155207401c180c0d010444a214a540054030070441000102034825440d40c0a074119203560611402c20549241d014106110380c030407610307000032111008100d80702c0303145606050300c440341c1d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 124254469 1250 124253219 124253237
    0xd0e030a031107030f050c120d050f10030c030201080c0d02160b06030d09051e031207020405060105041d0903040b040303020106091a09010e040f0206040806040b06240f07020603070906 81
    0x1d50042d5442580400740000b400450800641d5002d4801080520074210442c0da511009084000081d04200316445201d51201c0902440386840d420898100310048040b203070a07031079a929000300440b613210003414480c02c840080c48a04040e02503404400c24841e0940d034034204c00300b07481041c98203148225050740030a40400e80c0d5050001d2602c3c403041040c2c80307000c503040c1000c04200d81348001081c500d00c0c00d0341c44294840542c40500068601c95840c20756580c4420b4240304000546400800c22410031100307200070030000c41640398404207a0f080082d1020a5100d10102e83d04600c580d800400d1441e9001400004040c0c1c1544040101e85102e0400c10045921128034418070310007010843d80213448034018451880b802d8042504944541c0d62884400c42507400318805801c00c0c2c0c0100c8880d08402c0400c020300a0b0a0105544410115070b03d6081c45600c1c80c0140d090f11061070085031f0024080f40e5030300412550310466420343c0d002031101d626880d01e440018a904134a0140b900040e00d075403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 124255719 1250 124254469 124254491
    0x50a020f0c10030908070c0f180504020d0305070212160905060a0303020a0813181b022802011101020403050c1201150b07030302070c08010606020d020a050705090702030d0e030a03 79
    0x403450040c1c106006040c0c03800200d15400c118041c1108900540f400c2008000110014008903038460040c000b05050080b4549400403054195041c0030030a40c18038203103001c110050303407500e0901624a40c9030030700d291030704414004035001110b11003d80c11948a1114034410448502c3c51880c11285010380900032f540e68502440301080d91444000c015078440050140000d1521340030380602d01303140c1c109800b05c039540d030210b1844082d411800c1a1440c1d403220303210701da004e46581388049880c0d20300040202095055107400d10112843c403000406032040030481c11688100541c50810400c0c400a41d26140c41e81001912030304540d82e03032485900007190103046206d040c0a03580360f01c1201c49045000070710f04a88401d4981c0021821010164200300c00000604220381140107400c8480000030520308000020780742111119030701c015988001e840300001132000030490144c500907240301000b078032a520240d145006140c445d4041c0b0f410055501c0650130b000001c2d2800000b260380030300145440c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 124256969 1250 124255719 124255723
    0x1e0303050a0606020f0a062a090303030b01030504170c0708030309030a030b010c05060a020a0903020301020d06050f0118030f03030923060c0c1506030f0f03040509010f0e04120e10050a020f 83
    0x15061840c255080241b880c80401c1150703200030f1084900e0702c010310980b405040417201e5120008040404550101014420b1550502c01c40031801e0003800d0801c528201a10342c903006102c5484184034034140041d484109403400d100c024000c01e40d1f0001c0380d4807400e04025485d00e0380c1003446074a00080c9030002e90383d4203620800100b018540c1000c003420a50319a003200101075480b119403407051009800d000001610244010000e4481640001130b1b100c0c100410085081510007041c1d041011001c0503009a9440e0340f09a0110390b808800388210a66a03d8150301400d8203a03005054a508160340c0d551880e800d408001c0c06540540c1501c0e025920100540c00a0241040d1a0741a920401c0d81804500059030400c0c0c000704c00500700c940440388100b803a4903210302c0c2500e050682d08042010401d50600700503c0340235008004610090902301100c2c070600341c0f40100f0141807078842c0800b2030801401286220118540a0300c44514002d60840242c020b41c000c414503c01445152140c4615003c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 124258219 1250 124256969 124256983
    0xc030219060c0b040c15050c0c03030307120506041103090607140f1209070e1501020618151005100507110f0108060d020103020f03090607120c020c0d1e0303050a060602 74
    0x280d845011411882c0e84510809010050045400a8003402e011400340c45903840ba00300114507030384140e542c20440400c141010080f5006034080c1d40184184010540c11002000185900900008840ea202f0340000c002d41003441c80015181e1000061041003003010030003a05c0b03448180c444003c2808100c030041160301c54240d2240020701d040c000748aa1850f110059a044407903c005c9070412030b2944081d00c00340000341c50040031003045a0f002c0c541c03542c052140e550b20104040c05400b02400c1c04410700d458501051050001d8190755000454990b03014804002915029101c0380d00d0041607003001d00207a0252006480e00d84074013101d11a18588908540525001a5901e48050300c4e0740007403060410450500b2418550240010040481d5590146101e611040000c1401d41000c100261540d498070780c041154030f081c10300032506160006181c240d400410b0340e1207841494070342041402d98030100e442980d1125040402d005041d4942c2200b07000d85041070040000f140c0c0d9850582e03540c20307 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 124259469 1250 124258219 124258229
    0x6090316060902010c20010e0f240c0d0305040606091a091305010f0606090b030c04060c03030b0301021603140a090902090f090405061f0501081302010306050a030c030219 75
    0x844041100002441c6800200e15144181454402032031160748441440201001a0843c01c644e41c03d00900c9603840301e02c04400c85000e490350810994801e010404540f84004616424480400540800a0600b040794a044403203401e480500c1980c4400030040c000a8174250b0f0317068100300300070910362428851320540c03d90000c241c03486007a282041c002046c000503c2107600003109031540d00450401e01801d1b503280074000001034030344d04050300030302344030155013103100104d00a004120038000003078200c1d0261280340c100035526203040e140c21070240c0f6075046a160554008500c040501640100958410781300b5107840b2081d00d01a81903a00d81d0241c201c440b400185d0408040020a0700c581c0201080d010103000150178040c900c000c07825034407003924100d0750f42d4042c1080141d01d000184441c0d003007500503150220000d1030800020318070031001c1c01c0c41d10807001000382c003402c581c000e81c4004024107010f0100c4200075501e0810f440c10500510041e40038044228100862503009000c5600382c40c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 124260719 1250 124259469 124259497
    0x14090303160c050607060207060501060c080301121707030503070f031a040f0e0d05040315060e04021207080601180b0901030503220f09021b0105010503071a0409051503060903 77
    0x815040541195405001e80603a0b8464007024082500d48502008107040c40c0070f0710001d66540c4052030160308aa205a00c4242080070f0001d07408000303903482048a044403202d920b903104014035410b298040c030100444c220321081c1c000406e00101900680958850030031903c0744903001c50030440a41c16640c542060510390030203503100702a9841c11341d00285502c01002c0303000801440240c00540f038000c0e4111440080303540864208204400000301030b4074503044620034840e1603c2c0200c0a001c0e0040508003d22074003240c0728a030030442080185034001c1124008984003941d5030415500400c00780000000c00c181003440011450502d1000740303040320f92100c01145414400703440400e420b0048403498205a450080010342500048824009803025040040ea910f005650389400498a81410401a410f04004011943d00030520108590500400404086482c0b030203607410f210399005085914a00001e00407203000017164800004001d4013100d10070307114107680541c0c90140081c1502e000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 124261969 1250 124260719 124260727
    0xe1c03120e030c0a0602040509010902070807020114121005010210060b120402130204060909060510080408030702011d060403020d091406071103010f0b1c02030a08031015020d14090303 81
    0x51440d074001a09681c0c070780c0940f030802426898880c2401040d00c026684250003003402e114500d0640d81050040241550031840c01409a0b280001c030b01078141c002e0f042c032000800041c260001c0100702ea0145502d41c015140340d1030b1403607000d802150b80e030050600600c40d4408100b1828800d108500646002280c0c0c40e0901318403070314155071420001c0c030481e082960307060800d61050060028002034443d41e290003000e203040c80d03e010211816503128038400c0441c444105a02c94202c03140da0f810039041000c2d00c2d0b8030fa44100c1c1c2640903080e001c0c031410303006d20391000f0742c0500203020841c20300941c0301ea401d5514001e138031a01180c0b59103007801003c50901c0100f01001d107610745000145461481044440141e50120001a003150103070303c030810b0540d864985441c0c0600c0c052002404d8881c03d02c048030344502c540d0b00421341c0c40d400e0038001006940004041269108948102070003461020342007408840d15030300003500e460b03440d00008017245549440080d100c0d4001c0581c1e4600002030011410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 124263219 1250 124261969 124261997
    0xc080103110303040e04030504090b04020f090f0103060807090e010c0e01020d051e0d050405010c180902090d050123010501031b052101080a1109040f1709030604030e1c03 75
    0x10140729980050350600c0100000103101403495082845030340203480d11616140b07080d01e03c1d01640c4a800c00140320381d1041011880e0900480142d03413004009403400c6030a042000e005a004106503008504144134254000407000615000358489005040c024484085020300c282c444d40c02c4001e50790b015810101c6c0310400b052040b409400d101d1079580c1c0c401c24607a445d080d85180b5a01440c002c03c4115101c10030041808024001d040b06064145030a100d6000b403120900e035510924000c0c018016000100d021030b80c1d9400c1c2c503071480141c0000007004480e4050382400210340304265440d60721042100001810342c0284500d4061440d00d5108811100b10500101c030079900c0800308e00303511f02c0510f11321220301c00c940d20540c1c080e0a00c280180403080050801240b40040002014441d01c1076904010010713040000600f10079500c980f5504900e4040400c200b500e0080b80c070141d4042c840c132820041071503804030311030107116400c0d03800d0020030b142446c4d100107044506102801058101e404844 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 124264469 1250 124263219 124263233
    0x316030614090703030f0509040903091e0608010506070203070306051e0a091716060e06060316050619140f03010905060907020d120e03030a23040c03112701180c080103 74
    0xf46c1c00a840c0440c5040c0f5004000350480e02a518242c00280c8c411109100c040fa008400189013182c0c82c80f02e0000c039180c41402400d0100500481d4080c103000718502003103403000c11801c3c1c0034590141042c0514580389804220780c44d0504107a4240070200e00c04035117207280911482e1041600b200d08400180175400d00341e51560f010054505003ca010a08200410365a00c1840c0098501c41d01508090400c41c003050f1402c00309644074124188441c8040005a44140407038802000512010048a0301a541a1022404000010890400051540390f02c03000307a00158180c0b9140e180c1003155880d090240300f41e210040340c4200142c1d12039404800d030b580c09030039019201a07401074041103d04480944030308540040c2d4861920503143c0e01490b8565000c000490300a00c440d07030984c4030030316040d19840d100625600c4080d2041e40442120f01503070f120381007002c150103034107150005407040040c040c50044900b48103c105903103d00445506901c00750140d60300c40302c080e03a1307105074a9003582c40340c82d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 124265719 1250 124264469 124264487
    0x40b06041203051608030f0a050a0204210303021903020403031b0807030c050304150c020f01030c0807050f12090c0a0906060509120106030605090703052107060b0a05031603061409070303 82
    0x7024607640c1e24540313000911a0340080d4800e180c1c0c0d207400040c070b0401800c0d800546002404100c0054014031050114120319203030205200d0643c4102011740b0300c50b0400b40c1c001e10400b02d400704200488024403030b1b11078054000380106c0303110707603554201c40700400b41626641d040c204000f000d001c1c08200680c04039108105000e07031107004105680c6407a5a030038510440c022492034032800b141e0521040c005518065800e009064001c0c00e041c001c103106984014010360780100b65106214010403000000c0c02a00181d500401d160f2001408a0400ca5540e9540e412001e8805102d001d451602007407070b0b52640690717030849001e51110380c10002a041006106401000040815035a443c00040410a83d005840c011030303010f0058141d190850a1940c00e0680314280d0f8154040190500b0303001d80c44440403180c484d03410100005120b00d1440000d00c8901895001650621458030f149185001d0145071408803841944100251084481c0d09024144100c42206141d049200e00f000480d004480031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 124266969 1250 124265719 124265737
    0xa050a05130506041203170105090f07090e18010507030605061603050702090106050c0607050a1209030219051c0e06090613030f080405010306080a020d1212050103050c040b0604120305 81
    0x64409240c4880c003044584d005a8801c0c0c0507811031145090038140c0000300c0c4603130f4821196410741c0c20342c1000301088442801519007401006503400203807181e0b1042d0b99000150962480702034060410102c0c0e4040e20000901100240d464400851361160003446444200c60000c1c01060800107101c2400d082c030840e404e0f06406200c0100b20410050340c0e005549800703040700f83c031004d85414020703a0803031400100404810500c0410046080d00705d4010300303e40d005030285079000c01c43c0e400f545001c9040c0405119446c40f00c3d151005030200b04130380032035075032500440c1200c0064136440c10301e4222a010716496415810050400171482203040050003040041001440c6000040c0e8990301c074140c0d0301900700c007500c0784100890203100ca90fa01d401424024040032009140e00070003074002805065442c05e00408001a24030a1010030b401404440c0d41c0700d074803400410566a41b0700b0000e0310307042c1c10f07d517051040785801e04c0c45900d86890015507055800243c80c11b205480e051742c1c00e465a40c001c0c891 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 124268219 1250 124266969 124266997
    0x405130b030a0305031306020f0403050706050c0c0d020a03060c080609070c1a040c15020d091d13030905062d0f0a0305070c170a0e040b0d080706020d0203100e0a020a050a05 76
    0xc0c2408100b1f54001400c1000c00311940c581d5039855820040e0800010750000c2041040400c2504400000042c0b9602d035408100ca00900c1a92030b03100003403075003140340e04c01001d10341461090202c0b241c221906500c1030000b89c400941a64450208a80c1018000720040050a191400448601d210080540d0082c858038101040c90385843c1d20303d0072500d00340d42840059001501660420b64410942c0c0000d20f142c40b0340100000c1c10303110344c1c003801b0002048010f0007250b40d0310071018140b045440e05d000346009001303d55900d010b22044103000c146000581c00022040e0100d60368188840100d0b9000b2518a0741203040c0410742c00e00300d000e003801820200070403044092040124044103c1000c04400003c0d81071740d540041384020302407070f1014900f00d100d9842d00020700000e48841142180080d441000d07941d0f6815145860b40c001d0081540504c01d041c404001c200d490401c0700c0c64081071ba024082209000d03504c0800400c00c0c0d02c05c140050002030703824440c3c402d1290250018249415541007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 124269469 1250 124268219 124268251
    0x409050c091c20130905120d021201050a03030c02100908071701050604060b09010302160b010305070e090a0503092b0503040f050105040803040506090619050405130b030a030503 78
    0x70006496481066402d4001091081c02c4002c10003500ca0f084141c900100c0c508803a442001d0005000080d080a01800f2944400704002001011300480410684800b00240c60f15200704032200290491900c200c0750545540012032145008829081160740c540e51780ca0180d06181d092001c03640e10140680706100f181c2c400032038490b0040c400750025200c00041c07285001010103200d0b0a4032030282c5018051490414180f003020191b0049902080003801c1c007503641d415607400c8c40350b0480007050140800e1410310010040000208410088030200641d040d455100e81c07140d6916000800350041066008000d0801c03142442c1c00f44040c141d00e185209050001c40e140e000d1070101d01450704440c41c2d0400902400101d0fa5060140007421082c64101d0615003417803a115900c0c8510b01a0505c9407202081038160340e0f50744400c07181b16020080306c0c40340c6a484018050400d400902070b00d48600e0481a0205803000c1324840c01c00d40e800020002d00680c0b48544098039039601c05090741d409506000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 124270719 1250 124269469 124269487
    0xb0a0902040803070b01120201200709060b0c06010e0f1914090601080706050c03030c0f04050a030303060f0509090607120e0a0302210705250f0308090a05150409050c 73
    0x440604018203060020350343c1c884d21072400e03900e100e2058010a901221840702400541da0120f10010740310740c24103600b001c4c41e45109640b03151407000d51241d1400360800704081090500180076100d41c00c41d02e0222410b0f0798aa260598211504075040032102d43c5001c00a05001404800084c0c500d050810002d0115204180c0581c80c40f005c0b00d200e16035910020041048923800c0000341c00801c4589403032400c00d80002d610382d480f480041d19101401c00d010a0004401207074000704c0c5c004002c000c0118110716030307a18005d009061680b0131042042e64201780010b50307013890040144610081c10251181e981c90031010703600c50380e8003004a601145e8526103c11130802c00c01c440b08240d400385d001081d1380809140000c42e80c4604000501e80c8005c00d0001c100041c000048043d40c032481c01e04c80c440715510f01d214002c00062140d00c50390141d4038038600003051101d210b00074001c8000503101008002d84175414090354210420401119200400080103400b129600c02c079004950000b40900d030181613 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 124271969 1250 124270719 124270721
    0x60c050304020f030d142a060a14011802030910111201080115170c10050a120b01020c13060f06030506030d0f02190f060507080117010506130b0a09 65
    0x50100000450000010710003585005243c1c107010040840c0100002981d040008001d403920341c0302c0304240c400124001e00c51140420319600039510034035144c515458001e074110b5451500780c402c502d08529001d507014990308001c40e01340c181ea03d207100b070040840c140c02040c0003d61004100002c01d0240c144460b00000050103091000400c05090030784a0000022a400300007040e480b0810683c5440e80310051001e0f4003000f081203c4198030040c01c40c41e404080350b4200303e5610900390b40501c2445c0e40d2100c0580280190000c0368040c0d03160390111040c09001411601c0703032042d2a003d03078424020110316181001c0044c041c0d643d5008046a03903943c508483c110a080c0d500610040307500d500c100034003420304205a500002031890012000c03403094102945034045207800b4052007080540b443e060102041500c1c016aa028000304054500781800401051080c003920341d002064084528100e0f0050051600642009140ca55500c9000c10340740024402c6100c21a00301e21040c80c0001d201e841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 124273219 1250 124271969 124271981
    0x20102090d060c09060c110d03090b03040605010311010224070201090503070c0306140c030406050a0b1807090f08070504090f02030d050a200a020108101a07020a09020901020a060b060706 82
    0xc00c00d000f00d510894480060642d061581000b801c2010301030035038001c01d10095160b5000c075001d8410221050765800d04855011603a080184c1000d4008140020081103901050480c5d000f0f01842e40135051007801240c4032101c1074950840e80200d6420001940395000d46250081514000040c11001f00d5540d41d00795003111000350b4a0b1503010004009110700c0c3e0040984842502a0314003280c54131002201150002810182c45103580c0c0c4002000030015030f102c0c0c80035680040c19800d80f081424516440c40100304c1d42d01e40040c0d00c0a078005074088000324128280c2d42c0300c40243c40410b09003c140002844602400d03203401030b4604404000d61020710050515004c9aa99140d0700da100070b4001d0010b002035807442000d0107602c41b141d5a1040c01103a0030320529030900e4150300f55142c20055003a46c100e140c200c10100c1c07003414048c2520415110040c01304500c26a0025030565903034400760100d0049410141c0940c012806400000743d1075480002100d8000b00000d0414180d80c070741d60210b600c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 124274469 1250 124273219 124273223
    0xf071e050d05090a0312110904021614030a051b070302040e03040603050705040608060906040b100314100321020a080409020a02010f1e0b0d08221d0f07020102090d 72
    0x40c002036450a4884103001c0c260b8880d08110040041c121540da0042c04c0c11044034450040503901d1800720080c8006904031a0b51000c020000e544030002d140c089101d0304548103003166001c044440400c1008c03404002c3d20841d810a407106030a00300c00510681044480400c0f11480d80542c0c0d00210040c0d403a4401e50350781e0096503005544841c00e1040140880f4800f401c05001c0c84000d0004000d05d99000c0030f140c0e13100c2000e4519090303540b15440810050804075404643c002418020395214070741c150710042e01c410300c07245d801d003154560320641070484005000140600b0640e924103080b08104600703208000b00c4c18411101700c031001c1c1e00c1d800d0a9802030340002e680c0b103400041ca0300849034240613041845981841c20484004210703401003104005a105a0010ba1244100c00d569a07a0f05654000c040e0440c0000341d95411504075486911f03150200300c030403145102c4c0041402c910801224245400d0100c42501d15141d180341e481440324000d01a600710f42d0201302c40609134851400010f6418 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 124275719 1250 124274469 124274477
    0x102041203030e0f0313060e0415090203061e032112070c0c0509070e0f01090810051b07050307021e18090601080d020304151803080c120403030203030f071e 69
    0x1850141960f42420b2144039006480c3c5d00600c0400c9480701000c04850899015007006c00d540010000070401928540311400305c0020344800000e550210ba4004620031142150380405610042401d80c012500e8449483d802d0351003010544445513a44a0b1440b400110501c110b0074500381460003031003400119601c20004401100190400070701c600994042e00003240c40d0705480c91f02920003484124881102842001e5018003c506ca07406842a02d02410a05050b5140740d100000b2032400703040c0550700720905100c4803c007003d110300440c0540d03482540c8a401386181103059000c0000760b83e0403040740b2607000180808401103a41d20320780c20107400070041102269280c000000c0d07092080591044002c0e8120f81d0340c1c03284165000c170466050f942c100c0186100410440800ca9142030b080da0701140e000706800d03011050000d014080c015441c82581142e00030b030810600040c0c43d001307030301c0001d015a20038004640c1e44202401101d50121b01481c010080d012804403005c05800030484440c042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 124276969 1250 124275719 124275731
    0xb041502150a0911010503071d010e0d03090e0601020f100507090f1d1006140c010207060203010f031104020a0801051c0203030d140a0903140304140a03091701050c03130203010204120303 82
    0x8100e480c2101d401360000d0a200341503240840025041e40822032401e08400c03034200d0b503a9580ea01451200941c90000342c41902c40c048585030240030f0144900600d9121141200002c000c3d600c0014038080005000340644400c031a010112000303010090003002c28003c0402001c40d00e078890903820401031803102d12603414044000f00010311050042c210200d0f40c1c9a440e0107000c03094010011101c8010442e45603551a0501c0752624020f01500d0b1004140341d00004c00011403012040481080c0c1c5d0041480d500c0800383c0c402080201c0c8549013169010131003213001003001c0c1c07800d1441d042041c0b0100322060540006a400a81191700080d0070303070700c210350701d121801400d100005800d40c400c81408082090181c9901c0150502103100d503002070791100080018204180c072100480c1c00d505103400c884a5800ba454060304100c2180a000b0a010401302080c42082050180a001d201d020302540c2c03841d00c8101c1d51301054000e464040e80c056400b04000160228402700010445000307507000560 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 124278219 1250 124276969 124276973
    0xc094602030610080103230307050601031b0e0106021b01050c0105090607180302030a0602070309030b010605072f0f0406030203100501030204141e060411070c060207060203040b041502150a09 84
    0xc030f00060810810400c2e20f10051000410441c5114070394aa4802030000c07960061132168075521804c1c00041560080400020400c000b40c00cad0088401c2000c4c0b00c0008041c1c40e9524041c03800c42c02d1140200513400403142d00b80910801e501c015051a042c50402d19040c0c01c6040719007940c906075500d4180385c1c0203c0070040c000307030f00103406066464552100e5807107034a540c001070380c1d80b10070f0b0300302070099540001c106c01018014141c1c0c1b4015540203404001540c0c1d107440243c00c0381c0000505540000c0044001c0000540394401180701160740a810000703910f00c803003070000031030303030313511019001a9541c00c04409aa000c200104041b0181c5901082540c11071040c04207841032882d4008440380d9910501c003a00a80c1c070b9070442c60020600c841c4019a5034480010003404038070f0b6a003c42c2c0d00c0d0024101081c4020109510150303801d940131114500d03601c00040f644ea02c1144102d101400301804144150484100030b0b04805255204031403290f8224055040642c80c15102d40c000ca69079440e000003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 124279469 1250 124278219 124278229
    0xd0806040b01050a0207090b0613030b07031a0916020331120206040315021c02030405010c0f0507080708040b03012403060302060306060a09081b030c0946020306 71
    0xc9401e007071a00c141001c15500c8041c0d60784119014011469440328825209a2200c0302a80d90810f09000a5000160780703041200d1031a00990380c16002a08090041c1e60a5000080c2c1340d115500140c0b0030b8405035101c512510303c40750352210690850004008002d280b040b48140c0d2494640314039500225000030b072440c120f0241710f661180740d45588410b05030b800340c3c0d5010706032001c980d0040d1a1144002c0c001c51300000910555101b00300710500c442030a5240c45607503029512491142c8000c0000d0480740000b91411001d01740030a000420802181c0d002034201000b400c40a8442c2c00d0040c1840d440315070004050304260000e501c4a410b003c0b800101110451100a01c0c805c2800c04014540c1150082581844020103440c001d9000145000c000c0f0b1103600064000d08016041e01c0340140d00030780380182d4800120885100303104514080040345403524100e030290803401c03c4a5080179907942030b000c84900b20400140080c1c3d403041c1010658502d40c1d03030072a20101460300180d03680741c5542040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 124280575 1106 124279469 124279481
    0x60e090907060f050304050f1c031805030f070201120501151202030105030712030210050f010801060f14041d0601030c210f110d0c090204140613140d050d080604 71
    0x95482800c3c285004150b128ae60b001c0c0443d10212310100c0c40e499440070090131303580040104040c41c551100050100d01c0c8181040340c18141440da9640480c3c00c240e00c9950141245004071801c95402804000078007071441d811429541420080395446800f070062441c000c0c1300e62070303000c285130082002503031502428500780024600b448800c030403c6820b2103040e182d50b00309000484c400c0c40e103040c101c040d907401c07000040340c00e9224010400a02400c00c001d510760031f4059000130a150090220310302030760292a60040c0c0790f00e001c100c1e0518040c41d00d21a181c0349900c0d400754001503100c454540406070401c1d29080440c401c00700050481c03200190040c111004140b0000d0f0f002d0841d000f42081b1040c1480801c4400f00d00f4041c08224419015100452681150207100f21203030a504910804d4019205074101d406503030709c45242160045c04800400c0c0e1040030800b0500d4240a60 = true := by decide +kernel

theorem cover : BRFrame.Cov 124100719 124280575 := by
  have h0 := BRFrame.cov_init 124100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 124100719 ≤ n) (h2 : n < 124280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
