-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0367
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:26:49.83522+00:00
-- url     : https://prove2.me/submissions/78b104ed-dbe3-442c-8899-3c448869b7c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 65827340 ≤ n < 66007196 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 65828590 1250 65827340 65827351
    0x1205030a0e070f05040e07050319030201020918011e050f01030207061803050301170604171605100e1005061c170708030a0c0507051507020a0506010807170d17 70
    0x1591401c00018a550070710060005010f140018030a80b81031104110445200e050040c00030f500803401080103440104440e900000948103c50201005007001c0e4003a00c105078030300c5e9203d40106207505809100c03d9081d41a20760130141c0d10781401d41220034100324203450041070742c40884030a240c40b0300c0d0711035001403100c2032086a010508003804104a900d400c0107140c2140410000f20060002280780d82e400c440102108004040b182001d4541c2c141240d620a81400c3c600c40000711000c40768086585414401d910904959104a1110100c00200100e01103641c49004080030701c076150500e030156134059040184010078001e11100303512203c2d04410011034100f035a8154080118080c8005040d025020b05504c81e6a45050244002210074000c0c1801c2400014000b2101140c40083c2450320314500101a81d219220b401c4103900c1c0c1601804000c1881c81190000303d072030903001c25030310121000d0805190048004c3c41c01d060300c51724001c10078800500c0700301070901440c6205583c680c010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 65829840 1250 65828590 65828611
    0x803060102100203090d18030b0703020702150a080709050103140f07090b0d06060909090803040b07021f1406010509010807120207020d0f1101180306020d020d14090606030307120503 80
    0x49085410b84010780e0000c5990420a07001000c0380d00b802500440900b4a16043c01525040c40e07046941d1a80c1804001c2c00c290109640810702900319150b5440d00d9624880401c409619481c0b003960041c131807201151640300050710341200040d031b94000d0048002c606c3c000000e69406a4581c11135030341c083c500900c220100000c0d10380010703244003113170010000284044804a542400c1c01d40107850800a079200b00e40e09450111034002040d200402d81c4d07005544103580c18196222098100d240059291400c000d4101040c0b00507118130b140e40c8029803062464981034065030718070005540d64000c4840b081e011030390a900007421035100d00c21924226403010300042c20b24000d50049245200d184a084501d6400c0d0088142030240250f41c801c5059001d180c24441c0b02d403c4030b05454000031910000304425000714540c54001c1c990307019035484400300c8000700404114034102300312021083d100710380c2e1401000082044d0341004012a544150800c40c45d030401000240100c0709640700410780c1c4d01e407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 65831090 1250 65829840 65829853
    0x30f03040b0903030d0606020304080d020c0f06090409120e0406090203060303120907030f03030e0115060f1101060b07081e070503070f020f0a0602010203010801060602070807050103090804032108220803060102 92
    0x30100a44683d2000d8100c7e54001c0d030302e903400c10220070714000d0440070749410b643c0010020769070b42d581c0c11104503c4120686080761a4203600001c200505591007006003441c0c0100c401803811070b0f0001c104962000704032028080035603030b604c400089102c1076540d550980c20800451140740c0c41c6201546d0880158001c03100a039559840e92a0241804081103000a45a00a40c03d403075009000344000c04640b42056a021407034010701070076a6201a1400043c003804a0411340b004500390312000c020540310003826641c03a410300d41f0000691001c104000090085203c0c02034030920f001c01d407040580d00400640c90725034503446290030319840c0f0302c0c01c070380c031600e440d58140d0192252200840180300e1a00096180e50502c0c00d040d0a40b00c0d0354120004661001c0d0301080901c1c0009021811180c00303003400a2400c51074104148144a96080981080503c80311041c030703000800c2200356820965580c0030b241d03480b44181012480480c40f4404c03030481405003280f02299101005507084001401107c0d0b2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 65832340 1250 65831090 65831107
    0x3070c0608040b0f25090e041202061f0b03060607150504020a14060d020a03091403090a050636030109030806100503040312021c0204080a020f030f03040b090303 71
    0x1544089402860001d44503505010401090b201415000141e8034008070051030642c440b800341c5060000c101440d82c0300c0da4010254035001b0f2081202402202e003049402c0d16090030010580f0444007001801441000001258106400c003c903404126080742180002e10380303403194045400c003416465100b0350400843c40008c1118442141c0d00c0c0c2c96890214280c5440c0c010010340011961001480c900d04034101d00c190303550001141c0c45480c10310340042c4c4038180031800314004c00c1c01060052040301c120030020041100000a00480c81046030321001d9603482c0c3c0305124450050b50041c07400c446a420700107900301c204100c07a400000030441017412002c00f10340003900b551501d802c1079001c40d070f00206200c0c0c0c3d8104200b940043d402d40341041855030a0558004044a640c1a045e003e001e0340401c611204041600d98485006041d9100f952996195140c068807201c404408134807601961400401906005c10b10303030310080f01d03040514209031038a50003811950006412a600d400104030703100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 65833590 1250 65832340 65832353
    0x10611010f05150a05030c031f06170604140304120624090c090503030702030d0f0e03010f0b030c03010b13020703090e07050408100e0d050906070b01180b0103050c0301090b030307 79
    0x5110701610040b98543c8070100d01800030366021508128020740018003c842e181d18000352100902c3c81199640c06505125001c01d00149059044140b5429440d0311611490b280000c009005900560400e607908444000321a030342d1147e48036944404051011110200385107a101041a840e11050607907807850041450b50180c030290426800346659100c2100307410b51214014015141c00d0300210329024a43c0c00003561282d2801c44001000400d418202403544074107204994184060020f02c1b9101d8181c0c0d40c03c0c0a00b411462090080c070420b000d04200346014058040030800c050070000d603031031043c200503010754030840090382485180000021000782c0205420300c256025074503252254104465a410280d9a00702d00d200c1130b0800388040c00b2600c0100b0080700d401180c0c188107964102ca000410030a01500f600030700001350260000030f03010529504604030614894041040309407110055003116020380c0c40500d20f04042c0018000100941d1124410b9800202201d05141d000c1e50f404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 65834840 1250 65833590 65833601
    0x6130b040c021606210209030a0609030507031b0c0e0903130f1d15040207021f020c0111070f14030a0804091509020918040309051903140312010611010f 67
    0x14001680260303205521245144408030140c2200d00d08000c0d071103400110340c05101710b0041c1041c441035001541071810b68003040040c1c8030a81c03001c024066039001e810040d203180c1003038200384c2c042070400008212803140210704140040d40310ba015040141000d030f05c0900c690009004c1c142c1880100403e050040328940d59400800f043c000e15680e0034207140c101070410301c2e00b00000d0450b800e100705008103001c680c08076404403401a60010780390103082c0000f64505030601c060501e10b80d583c506048260ba40490600c1d111242a242c00c50411403080d10f0654030600ea203d283c0486034481802d02246204800f454100d42c0c0c0203048a034040c41a884040b0799034030980c007218029a950361040c20404050b5030307240080141501c110709040014011502e03107240ca9140c150f00090030000034080601425000c809408042d140d00d0442d0300110340c2d0a043c616500040e03501c000b03490700b48100303400000116181542a0314222203d6442c1c07070010348105040d144c3c104600d5494035403800c854041441030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 65836090 1250 65834840 65834861
    0x92407030804170705010e10020f04060804020f0a180509060702030714071a040905011d150415060504180207020d0209071e031a10020303070c0804030506070503041b0e06130b04 78
    0x309800c0d0070071158500302054140b81d108c54010702600200c2d10702902a902107507507078107010015994510000f51059100c4003000d900c00d898000100705420b00c0c1c003180c155540315840c104402e480300d244169a4410844000e401640100400f10001d0301c80c6c104001151446011101c02544805403000c070346610310a098a0408003140403c0b2200307071400396500400c3d09561003100b03021850810f41005030b00410408100002007501300742c0b500c0c3e90b800344064905001c1d541d4071098460303400601a50041c450001c00300703018000c0f206071941c2c42c0700301c07540c0325030040050401c2240b0b42c1c240000e640e00200310340180300001c005400c1e5869100030021000700965400284204030310003108154800c600b009000e501e0460000031001d8000040380c1cbc00c11564140380055000c2864038440600c1281c100501c0c0b8041c00090003403a0f0f0304100514011813160320341105000f00e03a031298555811600c0b5000030350300301d80041400d906110340c40da80005685540425262408800305060b20740ba410b5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 65837340 1250 65836090 65836093
    0x90702030903070b0309060106140c070f0519140d030c1a0f0106050a0806010e040e030d09030e10050405041505040510030204051005030307110f0d0305092407030804170705 76
    0x481c0155403800344a101d018010002041d41103041015410b0f0b81e40d0414003403c0c0510081d440e102d00d00b13034074200c1a601c2900520040301c0e00c041e110345d0b01c001890b41c0b9108160140342c1e082043e0301e4803c00320f200081030f214140d4180e948400343c4410082800e090340015020b02410207041c40200341e0b000101c0c100202d101c41c0880190500750601064888140e2080041080602001c90a541d120001c01d030404001d00c1c0403e0b2110020001a009140c0c08131480790038030001840c011681c0d1f07241c11021030140030b41c44816100521505004518000180c0e607000a4400c204c2440140b03050f9000220030000022900740304c035120001f003821500c00381c4000b40c604001c0c080410440c6841d00855602001c089449207949180c000400d03902d0203940d500400a0f40600410704040e150f03003a8003d800c510050910268083c50b06020300168044804680100c0320241640c0d95615609462414407403802c030a01d16100c22618211101c8030080c104994a00403100f55903802c0701510050940030b0301520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 65838590 1250 65837340 65837347
    0x4031b2d020306060d0203030d020403030e090106090b03040b10090e0615040b0a0e06061306050d06060309020904030c050c060a030b1305040b0103150605040c0c02010f02150604020d0b09070203 85
    0x1a06661000c01106031409480350108800140c9000c516a074000d6025030320840e0b600e00c5840028110f0103040322000400c3d2000c1000402d05920140515002c130050b40d176180c0e580d032101411503c000e0b46000300e540090f0100301007000246a80c14181d030107040f17000801c5400d1340b16000b4038191000714080c40019440070062201e2040280a107944255003114100002103401c3c1c00b0407410743d070b00d1164940540c21500018059218031301241e0141c24151003071181103858074005060fa800100810305e101303113442d00105050380a845400b050300e4004050b442569543d6408071400c66808100303e07102c0c0100d1200c150181c440c140500185104d0741c50100310035410100b0f004850700310002038080c1c40c1c10f000c188008529400d280c1815a900581402040d445d040c20900c00707003149611030b84c1c02c41c2c0703851a0302008035407010004010900c01d0341c03010241600c2c107608981e07820988500c09650300005010401500d043e500070a09168070f64404500d030300703030040022580e01f0704580c2c2402681000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 65839840 1250 65838590 65838623
    0x41e050102010b0a0806070c0203030715090311061b0a0e090a02041703090d080f120103030806010809150703020a170c18030a0816030e10120c050a0e040504031b 71
    0x280205040f80005445043d5107a140041c0d02da983c0d10b018181e5400d001c00101034400f51340307082c0304456503260064806000c1c0808006034000130700080a0a400180c3da6080100c08c50b1800300d0312500070020402001c0d8100402110f40405501c241104401d200350102411400d48410b1011b500c0349800c1c1e58010b85907031404c00302240030f0b041400c1c41c4030140c1040000e0601030303031802e0301440c050360041080e54440d10203070784100480c403510804101801811000200300340d0300901091080000b0307690300500741c07200c00704e1316510000d507a0003002e00358204001070201c902c2a03000c0e00785800c0c0740c42c0c04001d00207801076080000e00305980743c4c1841c07100016081101c022240324040480c0081d00240500d102a45802907940152018000304010300b100d030206051045464070f900c5607000300901d03003c496144e0003402c107400408825030001d00381035210708040d00a405841300314040d5103450415410343d10030040180343c002c008400340104c00c50101c805c011500d003010035242c45130785a8003002189 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 65841090 1250 65839840 65839843
    0x909011401060302130e060604081c0f03020306011709010213060203090f0108040503070b060604050405091605120a02011202130b07060b04150e090a050f070e0112050d050a0302041e050102 83
    0x142c008400303060041024000342c0d070004016070103d6400303e91140881c0c40c4c0e0700000d82c80303102ea940058030302e00c2010700301c92011020741c0e000340756514140c6414043d07186400c0244c090340421141180032900990100b641045015403480c0d111403800001880e000e03808600d01007040c50354104600603840030507a40f00700e04011310303500303088031003400c05c40380300c0c54550f07512641c921508000800d0300c0f0445000c24125110070b01500d001d8000140305000760301d0302c5201169115100d0b11013003224010b20000058609203502c8a0041c2920440500000a881c0e00103440525495000194590b82000b9056502d2130101c5000003818051296aa032a00c06040502c1a103144009982c440d5103070201403900c0c100aa140d00c01241d0044e01180c0c0a541c4400300a410100ca4080c080c180d4040d1204990086102040120665951900c1164166219059500c40e0701070f041000b4280c0e40012013004800e8050741c00b90917103503c20326015290035210b03c2d1018000401c06848100b44d000d00c0700a028546c0c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 65842340 1250 65841090 65841131
    0xe01030f0c0207031703010b091009030204060b2502010f030911150a0207090c0f21050411031504050604030c020a081603060513030c03080619080c1002030703090311010e090901 78
    0xc00c035805c1d40c210350411031800b01d50b1280b400d0302e030720800240e41000985030247c45140b004540090042103915607554083c4107992004890485400d09a074001d11054540c0012886c034076010780d12012600c2c0014000c0d8000c11034004c2c181c030540e03c550f10040a40d83c9003980388001000780d80c1d5458907035190403000381c074040c0c054018035030090510036403d0b0312079446851540e610300c4c6442c2000b01400b4810341c0f00c09403100749601c2d010680c10b00d0108024807a012402c1c6801d0300c026070803100a80742c607c0d5000c9070355809030b4005000390003800104000c00d20071118090840c3c0010300118140d540d032240c17a443d24035180c018060041d6003210030424041188102648581d28854109140d8101c1e90014121444504000c05008240c4046261030321303585010165111510200b01810382c48854490307031804a0700d10a403080142c446400705c0c4601c04425100c4450b81034480700d02081c02c55076000d020446440d2407604010f0304030006032196590443d203902071104100002282024841b00c68600071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 65843590 1250 65842340 65842373
    0x5090f0c0a080607140f0c0106032003030d0e0f06040629011b05070801090309030605010501090b0d050411060f0c121908061203300402060a0e01030f0c020703 70
    0x800c03200c00c00190030041585913210700c3c249408124000d0401c0a03d280c3e015800515498100114807024007100550040054a001e03000c84001441500d03005611140b1040d501030b0550014814051240f03005c0d0485400031820320b06840805150700b400c54a00b04044070140c601d19100c00caa045c1002404000c41009074075032100751900145400080c0c2a944443c0481501006586002c41804001d02401000d000351200a221300006400c3c010000007080c002a0b6a081c0342400000f1598015a82042100c0603440d81a04200303c100b51000100301c014008d403015852580e00a082d40c0d103900080a1500310031407140d8a03000b0780340c2c1c180e103081e6103214503203400710f070802694810f28a0a81e0004182c485031a114400c0e40e540c1001c0f0741444070207211018288008214112a610036617500da0500b5907880a0f560b400841c1101d072408188243d4020307410840800541000270b01c580420002d4010604020031501070790b1032040102c03585c6038507040060b0400030080c000c12408041039812007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 65844840 1250 65843590 65843599
    0x90c0310090c090605070f06051614031b070f0803100801140c090d170a05030403080a090305070b131703070e0103090206180d12090e0702011407030f06050405090f0c 73
    0x401c080d00040e20799400e0b409640103120010030f00101f00445c0400d05450160300003000d000314104416043c80d110b80c452029800328003110009219905080107030385c400c04814404103418000442c907681240e1007103c1c1036981c6214101c4940110300b180c0020b500401d5007295403a00d003494821a00d084030148030141d10303280c00c40350501c03d02030124001e5607008082180e12421000f03043c60102d01007842100811007101001c95100340031600440a988030324040c0e150740049642d442c0305c100c00c8604001c0001c0100b40248402808111503010322903019040340e41c41c1312410042d407210b103080e40120410f901e00c0103000003000019030f070048044014400c2800e050045110a5001603440c0c05281182d240b81c261000c03449000d81c0d110820b41d200103400c1801000c5c004080c500c0240122058010301903240d146c100815091807051082c0384d01c9107460004852f01e601d07966821006050415003035002241c8441000c21295100e01c1000d0284000c00c000303220b8058030320081402c01e158441e00c64401d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 65846090 1250 65844840 65844851
    0xb04060e09100612020408100b010e0a030503030109090816060603020102010b04090c230907030204060f0c0510050703020c0106060305040c0f03050a0f050123040203070f080705040e0a02090c031009 87
    0x461002c0100ba825a400d90810800100540309044002c0c0038661000d50a407141e40352a0723081d1201c0b40d026410207002aa9050340d000441c90500200710040e100c000c150754400c00c0100440402e0340e02c4078051621503c40c25207070142d203640d070b82c4441e007403040141c6005540300c07410411507030248511204100c055405002c59070326074442d01d0401001b88604510030f041100d0042030080221100c001408006040b0340007410700c1d5074001c000390000d000741c00c041071490124202a9004e400c0710035040747d203d4014043c600f04020100017908004e404802415000c2c080701d0a441800e020380c001901850b9000147c44c60f00d0f003090100c5004580c00f80b0040e85c00c0c00c40c24408a134000c1a0442c407141c0281c06a2100a142c0c0303400b44c01001c44c000300850860b0000001c2061144107aa8540214000c80407603004c0f0b0380343c081e4581380c1241441071b503400341c5c0200300400550515030010b6902c02c1ca035200740c804440440e001f203000c2d05c50850350385015840000c100016901044522409040b840b0340401c030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 65847340 1250 65846090 65846101
    0x30414010603050733050d06060806060d0b03030702041503060b010c0f020409050c0a060f0225060804030c0804030c06170603060601031a090f0907090e03040b07080d060308030601030b090405070b03060d0503040b04060e09 97
    0x5c0c9101c1e40560801c24ed441d03241034401034408000310396503d9406001001021032940b41900d0b00c10725800125a12410030030ba601d5550f1107035401c01d003041e402030030001d0507119540c2003000910400c3c070101c81a0003405854041690307a080740b40004d00e1a07883e80700d00030f510344000a042c04041c0505081801e0207522840c0c12080780c0c1c40c00030507180c060528103080c0e04c490a007a0b4202400b200d000348052000100070040046d560f000c04101d44150715000d0011115001c0d0f00a008001c41d01e035905940f11600103805076100b6006070004c0104542c1c0d004410100f10046400036004980d84082290b1000601c00d4200c0104684001800700502c2040b02d18015040142c8a100d2031007010041400494000700340008441240d41e903007807200b03040124654a2404042c81c3c3c2040b01e1640c0440d141a80c0c000c800e041c2081c0d0300c0d1256512030080c000580c1010105005904042c1c1306030f0b04221030403400301c001ba0081000b08041e160706208140c80d0351034010010008070020304c00c0740c0511099418482d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 65848590 1250 65847340 65847349
    0x209091c1d0904080c010c02010209040501060302030403080624280f080f0714070f030201060f050f090405010e03031302092401080402060d06030602030414010603050733050d06060806 81
    0x10440341c030480d10701e0041e85a40c00e11050340c2c0210600a035607946051000303104140c05500070091032000799000e0005d0780e40d401083e030483c0002c44025011170b11400c001803262500840313001c032200795001214240c0b0034011050708150040169545c407103007540c45040c002c1007800c1034400520f81d80d140880001082207001410040c001c0c1c5042a008422008141d01c0d50040203d0b10015a40110340384c0c44204c242480242d002660030280e01652814002080b006015900071040c0d0710080c001d4491400728205120441000400583e03441d543c440092710720980900003540103841405007880000d04038010000c4104002d8954401c8814510b0102540a051883c00005100908080009607030f6800828006e1290b1a10422018136114021040110990242d80030300e000303003603035800b0181006403070382215454007002d8280ea1000c10100800e201b041e0b940c0450742c0071041041300d880080401d00082e050022462004030790007041005441d03aa500c030b0b00005007824603043c00c1e00c0c10f00e0307808075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 65849840 1250 65848590 65848637
    0x50115140901270209031c02030a0e040b01050f0c07051203030912071e02010e03070611010f0903090b0d14041101030c030b0a1a0705070608041a1605030604090209091c 74
    0x144039944c000c196801956010f000070305240c0100d48030303800465403001c0025260b90254403c50045000c6242c880c0490030b191041480ea402c040c0c403450310b0f0000d1010005015000704030401042c2c0700385540840c00303464080c104043c46001304001c6843e4107202e00780608210f503189403e0440f080c240899800f140b1150180054a012108107400200f00703800106c0d0f41d0f00307112080c980c16204000000545541c0031407004c6502c0d80c140c1c0204034413000b2440b0107080e201103003030140014101c0c01f014041c1c051940020b0104000612001603041203802c3c58001110085a007540c00341d210b6100c2400300d581501456900c41e00038a03040040340300c0030000540703200240c003840c200c04606010f5002c10301144021207194980000c1202c0c001655060020880001244c08407401c0801e205852401691030012501440501c0d02d200a506401541207410744c000901c403e61050b154510500582c8865042c1809510032201500da118090802c620342c00c80817034004420855044100c24141c080d90215 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 65851090 1250 65849840 65849909
    0x20c15090a02011e020c1008010602010c05040302060409110408011806140603060406050a111612050301150305070504030803070206060906100c0f0804050307060e0a210f050115140901 81
    0x8007903820032038a200701c3c03034809000c180d250444242d005801c4034523003100281b4121401c9074000c0c050a4514201240c1501507480000d40224080c401401005000c1d08080307010301c150308603641000e99600d94242914942034201058500003030f1081c0c00d109042c05813601100b210000e00e10241000c40102c1d41c2c5a200600c050444c5690f00e010a400c002c10b50040300d080655111401d4981140d0380520303002d16400081210801c0303018403060b120a0003001071700e0494010a070070f11503211a007241a0007400c1c0007060041008800c100c0440082c00c0c8001445c003440099004004070300d446418400d4a10001d803460340b203001c80c400180300700c552011031502a0340e44801142801c10440c40c101c041070143e030300000c5d0b26000b60700c80440d91550000c1210305440b01150b078514044e80e201d00705441c40300300106200c180130000700c80c82c0c08906d0800e140303041c00744100d000107003001898101901c0e0711207a41044002c00200c00c1c8280c0c2034505104603074054405190419100b01c1c0d000100ca081c91031503611b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 65852340 1250 65851090 65851127
    0xc110d12110c042c010b130b040c0c050607030e0a0b0405010f0609060f031e081207080618130c03060e031806030c0306011209020901030803040209090604050309011404050301020c15090a0201 84
    0x1054140401c0a402c001c0f59480f020b4205031080b142400b13001f0283c450030045601851611508504540c4070b0401034003559044800f0300080d85032400c0441c090427203030030724210300c0c880c0207038140009082d0a1440d200e9030048000088071002500524143c1c1c0041c1e01900807117003403803c140711075600b4081c000110390340080102401c06c00d82c804440148554100a400c981010814aa00035080c0303590324400c015030764a00d0a282d0345c502c00c0081c815035025020301e80505a00c00290809a03450307401501c2d5025150030b980e807a560342d0f03c04064403c2c0848a010980010070214500340c200c01e1040c00031202100c0343c41c25440c02200c480c0c8280001842d907410011541041c0002c01d10a611650b42c0d190081c021b042c003580c507418124616402030b034040b03014031540000114941d80114040340145d03481005185030826032001114848020503401030300c0b40d420480014156800d1005090716400000074004038240100804424280102030006640141d414400140e91014030850048403111 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 65853590 1250 65852340 65852411
    0x30302030414130f0c081f0303080406020d060f1a0403120305040f050106090204050112020c060601081806130201020105100b0d090f02091003050714010c110d12110c04 74
    0x4001641082801e40d480900d9868800308113000e030425003084079501c80b562540c42060b03c070390b641a141410700101144c0c1d00780c07640300107000082c07040c1c0d001d98009004200243c00c001d46484050211016a0b0003201c1c0341e20055402c21043c90451440d0290082c48030029080c14515260383d520170034024044070400d680c40000400b0410380403481070381d40c0d420400800409403503404010080d84180107240c0400c82c000e11150440a80b8000c40b101c1c000d54002804003030b104c0c0d80040d54284030180005256014a1004101070700082041920a0304091316145404580d8000a400c50700007404050741440b01c11300c24403002c01c10104685201d400300400060244503400c1c0a00340c1000303104001c0d0701c1800041840f10620304944844c1c00e40b402034094481e07641d529400d040c0094003806145011030288083e90000c900c480038402c080d0781c4003170100070341c151840d0341d881a002c10102940021941042c905140850100150005124240d404125104d0401301c0c00075000a00c0031004030442c110b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 65854840 1250 65853590 65853629
    0x21b01080f1305101505040e1f0e0316110109030506041407170607020c03010203100b03040203010914030a080a0606080109150b0301060f1b0c030f030504080a030302220303020304 79
    0xb0800d20304020b4103e010b586400e00d40400c1e880c0600032000303004025806108010642d80342c50310416040c0c06400000300101c04c029001c00c0b99801c0079400e400491552182d1840c140d007001d000401101c2c0d005c0f02880380b450000d18200c6140070b02c1103607041c10018485414400600e0001c0c010b504a42c02013a0740c6641d22400030038601c2c00c00190861160000c42c940c851490b2030780094598000c0c4290340940c1c1c0f0303100150060500300e010844030841071000700103017040b03440b840c80c0044d500540050008940b0741d0281e04d03001c51070b4000e0a0141c64650000403107541e0355600501903a00240000030900405140190080080c40107020303000c4240c0e03aa620340c888215800342050300504151940d1900c03903a40315400351691b400e4800c20000310700d600070b01d4081440c244032000c030400e80c41a04108040d095482c0d100c1c3c11020700c2c034200c09000d000c00c400306c1c40807030070002c402036a4825503015998400f01c0d90740c800907078540c4003c1087c9004440c030910000740c011050b00d0a8884460000007135a020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 65856090 1250 65854840 65854861
    0x130b09270a030806010f0206190b040204080105010e0f0a0603110f0402070215090310020c030f070c08060c070606050906030a0204020d150f140105070302070501050a0504090e0d021b01080f 83
    0x1994440d0500d110740700d800020140c01003051441400d003621020540700010100347e848010403201c6e42280030700e4040340c0c0c12485c042d600c45110352101038001070078a501c45041a0071100203811414400000004109900c207000d0303000703507120307440341010300c8032510315580c07842d038804442d41052144454800e841e9403030303c8607815261b40d035400070f14000c1c3c1c04100c512408440d90201c40d50303e00070f0044414842922444d4021034030b0f9540c10310000c511748180308003030002075000306000320f0703101c2060100080d403a00100000340c012a0b1100340d25581e09810300e00502156525840b540c040e400200401240f42c0c1d0200d400700e00203406480250b5281403018108005080c8164100040001c400d00403800c4926030301007005640c400d1020050007504c850040d07a80c2d000340640100180e008020038003072940305201600c8030300b61b54240581015107c02c102e0341680c82507080345103243e00c903001940c0e0080e41007042c903000d41c4103686088000000d001c0000d25002004200711244081d80010401000c031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 65857340 1250 65856090 65856151
    0x80a050c0f01172d04060b040e0703020f0909030f0c01020301050415150305090c04090308040506060a05060d090302121621050403170702090c0711010203090a06031a060a0302040302130b09 83
    0x4a42c04d410607030303140a00c0c3c00f40050180410b014007480c80d1a0100190680009507101920340003071294001e80348007810440403101c002c0140031580000d028069000000c00c000d02400d030b410500144e202d6040005010403500707040400840038003c503804000c09201e1111110071031800346400708040c0e90350008240342040c21a81250410300d03100c010400c1c55030000d141c5c0d000c0c80c45401500c0c420386807101007000c2030b0f03200d001d80360f071004040010b000711001c03540c450380c03d0310b109005035070583c40c91070250503160304142044035010b00218600d02c200151030641d50903800c3c5103d0f4040c810b002c0300300014102d006a0000402c20166044031028210341d00040d640095801085d50f200c0c3d18101c001822943c1001e8012120b9051040064801c0d41c004400d40701d40d0f0801801080d045480c00001718081c1050400040964100c682c2550703160310350300010040e90503151030140c1d4440c1340d4814000724413034040c000d408180c41c00b02e0030380140e6a041d845580081034075078050032105210342c03c02600385 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 65858590 1250 65857340 65857411
    0x30717070903061103091c03060e010b09180106120f0905160f06020d0806010804031b12110105090a080901051c09020111060f160207080a050c0f0117 66
    0x80104291154440c0804060701e124040c240a110000140e560b0940801d448058032600720000a1815100d84078100000701c1140c500401c80d96518000405210800e800c28210030f4000905600c0e1420400000ba4411600c02c4e030f400d51661410030001e050b080b0720302c0005281c0e6140d03041000b06c2e100b0360700140500c1d42c02030240d6811140c240210f85854105110300c4d914083c1e2050000345035400421039101903122500d650040d59526001102c00c00401441102130210806880c1d807801c003107101c02040180300342001c290319941c803c03024010a07034003280c443c1c9a81c140030401a03c514041901e1825640c002072480e145c04204d401690349005400d0003146003030100d1440d6007105415004005528000c0cec0f0b07048804896031400700d840b00011503000c4031201700f001c00300307686100e00412954481800d1054031505d58403078210504068022400b900d00307902005807503a45180042508002c03040c242042d941401c502c101d00503111000501c00d424410600c80743c0030080d000c0801c0401480d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 65859840 1250 65858590 65858627
    0x10f1a101407080c060405010c0215060402090a0e09010b0307080f0703020607060204080307110f09040f0b091e06010512070302091603110706020705071e05041d06040b160504060f03020307 83
    0x241200084c180e03403440d0444082d42c0940c00d0004010005001003219008040040308400165a0705014403010394001070042e40c115070325100c00121914002107460280c01e454001140c552042c40400d4038120081d00601103d400c0321229403803607080041c1a8089960603540c41c0d480d0034543c02d200000380030341d5000760000e010004d8500c080004040506050180896407101043c0c1190140541a88100c0c5c00074180400e242c25080070404042c050b990004240c000c90301c440c224a030ba01c15607402003880b00c2d00b01c0c2d40303d900140000e03e0403440715803540014500a1130060300e0341c0c001544503038016225010321754185140c05d0102e44203030000c00301700161f40b441c60f0784d46001e40703000350003580211010b581901604401045070b00c1c20038003d4481419803400e4000c074500b88410080282100f081d64011907021000b664606035007848400d10503405901076030560b1a0102d12050704103a9051103e0800c0020032040c4200303a0498030805044515290040e200d0380c072042c043c0e4000d0b0150100c640c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 65861090 1250 65859840 65859847
    0x6040905160e0a0c050a0e04060302031b1e0d030804030e06030c0c0f0d0207140612010906030b0903090a210203010f05010603060b190302071b08010f1a10140708 71
    0x110700c0c5110703146040318100c2d40061165625441d0301c40484001ca0324410010f40d0810000341c05911a074004411110300900006105590713600082c5000d2300198030000350b0303680c850b8408043c5000385c0f2595802c01d4010340d8069464205001425480468800905104824000c102814030580800464a0700a800140e40b41421aa040d150340c001c40c000f00d10134494010301c0c18503040d000c0fa2800700c062042e0018a0320f1424010303c501c00c3c000103200183c1000341072261060300c1143ea030b440ca00804600c41e00241c00740c1142031940751143c2c01444100168070401164a568441407800000c81c1c0702a0341e0fa1001302003075042e40c0b500642e40400a540b5608160b0500d04600291744000d04990b40c2d84c90421000b5601c0c1c0145142c0c1c01004031080189140c000703d520580d000350024202c103440792000c4510300c29200d00c0260071042c00e400254580e0f6460f40d030005e00800c20300c519916600b45c1c11091041c000702c4070004400e02c00d81c2a030082000702246121207a0045602500c480f00d85c8842c07071503203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 65862340 1250 65861090 65861113
    0x3060908120403180504152306070c14091509060402040e0a0609060807032001110d0203040305190209070c060e030a03050906310305040b0403030e13020a0c0b06040905 74
    0x44c04100f41d540540c1c400c8552000152407074544529003221510303400c2da007a12031420456a07888110b42030b9071445a00c040356250441c0c2e552030003c0c001d0600c906038040c03006040001d1040ca2501d21074801d07009190340c40500400c405040c2da428039828044031491070301c1e9540000318019000c0d0307902010f0310001c030030284011541c1c190403400c241c400501c0c0421240365a01d0751955a00810310000d8501480001401d4002d10703019120640c4603018140700283d03194450380d081ca40045404100010f810118040c01049405d01140755002c0c000900c1c0140020740f030300000d00010002d4030200521103842192410000070ba000350400c403501c0310540e80c480c2a030715406005820100c8481099005880009120800c45c442070a1100c449140d8a09219442d4040d14192007100006500707112082c00006402c0850100a2002c0c610965641582a0f6040c051114502142d812000081d0043c4100d140d440d5002c24001d0b0301315080b03550700fa403580b42c41011400401001e10094101d0180b104080c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 65863590 1250 65862340 65862347
    0xc09140c0a0509101d031908070f02060a05120907060e0103020d090b0108010902010e0324040507030f03052d0f07020d0605090601080d080f0c0a030e100b040f0506060403060908120403 81
    0x105000003005c41d110505403141d0400d5124003c1c0c44001500c4841d18840ca00800c0c031f5140903010301485081400b403040a0b5800050442e003100c0c0615000940018541e600c00d0061070003a500640400018218213040c0030010b88521822a0120b040590206281c0c1100e041c1d43c0000c924607800c85010341e101d5071103c1495010b400c40060a034081040504140c000d0304001400b005c1c1160080704442c0c1015501080529030f072800b5205603214440c586d40880032030300103004485001d02c01d8031410342c2c80c0d280400000508400d000d041ca500011042180744c0c043c41c3c5001c80700b48540e0011400d6998103107100007405e006036520050120b503d04000c201002400281d400c0c180d9442404688883d903081104a41e80d910465068807c1210807001c6119150000b000d050403150608000c1a1500c101c03612902d40700b0844c0d40701240c2d545460215505040900c04d80d8040c0302c80384401d0003a071601a02280451240b4800241039580d92906042840f01e00403c4d40d48040c0c100c05149214105420000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 65864840 1250 65863590 65863607
    0x503070210050a0b12060606040909140607090501090806060a060e030102040b0417070b04030c09110c0f070512030403030206180309100305070e0409020d121211070c09140c0a050910 80
    0x44e4014044030500780102907000407154031130784004051614040c00c021040003d4807014104030f846110b180450100321505004841c401d02c419924000554988000101018455800380c8116080b2005120300342d1105015001a5191420300d17075a4084600040f0b402031140e80d000500c54800464003044119a402e07281c54003c140404840445440d6001a1860320552100401d8010007240412103c03100c0c0c2c200c0280c411050a50504100303001c0a924205a103104400096807c40304c0180040c0c0b5040c1c945c882e4100d00d0300000d600701419a84d019541e40c4c00076000d003140c0500d00c2440329075071104000319207800c107001e00403c0480c9031902f40507011781004d4441c600070901c2c200b68841682000c0c0320303803004c9680041c4804d03404405034444481c2c3c580d1040e000f0081020b600303103010400c4801d024011011011252a6694203000d082001c4101460740080030041c0c02d01da0707280706132900c0001e0941c000c060060350310780d6002d40d911b0642e0345201c4c10084075000303400b0002ca20381d51504a0b102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 65866090 1250 65864840 65864861
    0x207120b0a060503030a0215070c080712031a01021005041e030807030e150406020918100905130507031b080d03020403050d0f020304182a0f090311010503070210050a 73
    0xa21030b036500c034002c040d203038010030a01c20016800036801c3c2402403900c040c002d03001101802c0c81c101c07840e59034441c02074a07400700e041a80c1980d00d00000303900b4141e2500c61401c001002010302242c0c8035007400001d46408007001222001074503040440c05110b44518031003100f10840021111400f0186000f07483d060701141c160000c20710780145505c1058012400c81c2d1b82425820306099995680e41d1400021340268075100d4000c00340c4a4040a28440488520300484800040e040304625201b498070580d100200038910315050240803038006000000d2803030940e0340c00b12078001c11440080c90038443c04016800380c0c52398440c580c0b039a40c40c5d6400da40240309a0b40600e0607513030740001d040d1060310f800190f01c4070440103a20401c01000500c40c010001e0000021351140032900e298920008020720003000e42c0c0c2540504041d01960300d40e90450780b0104640c2041c188250700d2450740d11190b211000e098640d40c1408400000611180d02c03d1100810140810404009c6414a001320704003d0034010354 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 65867340 1250 65866090 65866111
    0xe060108060f0403020d14070501060828051e031201030c060f0c03021b01090308041e051207030b0402010e030114010e0a02040b09060f0c07030b061003020301061d010207120b 77
    0x104820000800034140f241d0341640003082041c9010038100c68122914203003c1c4c8201080c002c650010303400303004400c02000d11030700400c0ea0610011039145154021307254000ca42c20001d003840001040404d0800d0000d04000d0f50721500544075040720300714440c80c01c12800d04450400040100b080f841d0b130302c10a0780c140e550344c4035200c00100010707035840c024200068056405480b45c00b1b51003221107000e00c2c6584040c0340c018401c43c1ea17960f6000f42074025411002c0036810040d210070303251b080c0684400080400702c803070040c0380400a1115885400d24000039020b2280da100007019640942d4841c00c13943c0f806002003140058003001100084000e020720520b05104001040f8420468000d440596030940303011881d065081081010a6200c061102c0c2000070074042140e080d40b003440701c01c0086000e03520b88100c61500750200401100c1c40107012003418414001400495404003050005642800c403001220340c540300103030f03c0c0c120181d0040302611700c05e404042c1001030882d0380718001d902d246c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 65868590 1250 65867340 65867353
    0x1030b07050c1e0c04020d061401090b030406050403140403060b100503090c06030405010e0303160315030809010e0307090e01090b0f0405120a0302090904030e010206090601060801140103060503010e060108 90
    0x8004481e1480b55000e40c501c0342c0d005800040d021030100440040161100c0308691501304500c001c074003642c004d41140c02c40684d0310f031030401c040710090b078402001c2c003800d1a141e41c0c142d0030044120184d0002505c00f40c400343e5160001402c160240d64424040201507441075125a6a49020070290224121260080704124421940036001d1410780340254041c0c0c01130414001c004003070182039000208140c490f5900c80d0041c1d501d810381131000310300484406c41c4a00000b840600c016082d984501521f0f005140e4540c0304102080e03142090355070282091900c1d105214444001074580111070b04012442440c105c1050044201544a001c0061042c0d8482d807603691409882b00ea11030b0103d80181281c0c11040385141000f901c400200400b080da41401410040c041e0040b400b010b004480890105040800d00e00c0f05603010003070154801c0304038004054942c1046801021000c061107410f221411410303005007603a01036001400507000c007070003c00040c09201c42d0b40b41d80e00b20a11442c4418025107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 65869840 1250 65868590 65868601
    0x40b031f0b0a0f0e0402030103030e031e060c0708090907030203071b020303040e070c0506040b04150203161b06090809090106020325061409010c021002041202040f02070f080301030b 80
    0xa60308103007200c1440540c2414440c04100c16a01481c40f00b0f406810069184403c3d13441da9120710156004c0d501035541c00140910f04000e0606e0002e000c8001881e03d001c01e203011924002c0010400d61013200380c1602c5844142030f1810301d0b03007400380e040410f5001c008401081030381541603010303610a0f000d41d03a50282e038100081c0c6510740070000719070280d0950810002400104814409140c000181d4a000ca01c200c28540381c0c1d034100282620f084640f4003100d02804180146004c01e1440b10101039011440c41c101140000300060f250035030a81484110085002861086050000804d8111000340000c900310314101405600892585114221250011540c10300c000199440342c02a1742200c0344020074220004036071402200211a19034a8000c82c402c40c268200ca50380c0105608030002c0f400202083c0302a040c103011030345006902e8810702082102010001820041c6a01964002190b4034000c0031100a88a00c0902901510f680b11940b8104081f02d4019070403a0300800d0180d4550702c0300b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 65871090 1250 65869840 65869891
    0xe120105070e0906180402151c090318080c09060111070902091801050102030a03020304150f0203060109240810090203070f0f0c03080c0a020f0115050f060403021807030b0402040b03 80
    0x420f0010a45c40d5140b40000d0050510000448110183c140282d0a10004030b0104186c0340642400842ca50345a003130321010503411a60b80e60084200c01a800c06450400800c0e9030f55841d4001d10b40c1c801d400410100b0a1070340192019031038010780209541486c1d84684e8118065481810307c14024103c0350307501d034010328001344028180c0c0d805078041c5262100c0780c00704401130340024005a800c1c1c0d600d9100003512160500c1544550000032102580b40d142075800506010307015406848107081030407496640000c141c00c451100d00841c28400c80341c1c1c480400d034070340076101c51704114000c520003c18040059049220b0034908009076542960110802504645091480e80018007082100001c00d000035450000341200300c0c2c0c688100c0e100302080c015101e0940700d201d0025100703440890000d21507410600c1d44214115003c0d14540d00d4240396034042050f076000f401c400d00381c1c08512004541c80e640709410101140382d004105649032501d83c1100d4405a0094074111f14414032001e10a502c02030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 65872340 1250 65871090 65871109
    0x4020d1106160302060a020708120c0906030403030507110610090903020c030d0513060302090904151506030f0c020a020303030c1e13141e010f121406031e070302010e120105070e0906 80
    0x2805270b01d060405c0c00601905030401c1000d801003c42c1c03403082c4503611031030711028051403296000781c2d80880c0038209035001074183c06190280502540226040001314420345c034541c02100c01a000004821170281005ca0070144490501a414060312620044066210700501149000078202d15506599420181c04a101d912881500950258001804100c81c0082142100d40e01c03000400d00041c0009400f0b0800b60795044280442d0f42d506008881c84510712031300e581e07810320b80010030800c821030f000244d17607000040803c0b29030000041c507000034207034120030b80c80d2018030b0392060790f140c00340040d07041c0b03110302e441c06170101c3c01a10022030f4102e0b14100210844052800d0000c64a11003208011201240005485c40901400030310039040d448040c440c1c58040c80540c521b04a40c0d081140405003052804004507001c10316040041d40580b030080380440c1141c0c0c1c242000c203810001a004200e00c3e180050741d00710705518010400004c6600071103681600d01044503180541d50721102003041412 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 65873590 1250 65872340 65872343
    0x509130b0c0901090b0a09060212070b2707080a060c03050106050702040f060b180406060906140d060302120309010201050610120b1507050313051804020d1106160302060a0207 77
    0x140000e000c107801401c400700034003100c20180341190100f80c07200014085640806a40e600045c048101000a00c0e414040024141c0840c0e40b464548002505d5807182141c0142011030085103c105581581100d00050901401d040003980ca0440c6c2d5203c89035240c160103a4160f4130282810f05503e2414800e2180c0d0b811303a13807240c80703844c1084800d801f484018a4003c024011140d601d07000440d40c168948050000c800d12034451a5111407007070244010740f0304540c00340045c009007207010720480390003480c0200f005a04140040d100c1005800200203040e0701d50001e074000bc1d411807003410801c808001010032003004e800a122a84a51040c4800c1c00712142c062000a10078a54206140300d50340c00c03250200708024100b0003017070030401081c0c01540c40100204c0c0c03181d0001a0300503007007074180398410060204440d07503400300b034080a03c00300e003240040000744501101030841d020400c80c8400305032802d0b00034181540b54a08061000c031030510201080d8090f2085c82e000850400c260f000301c80c07109 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 65874840 1250 65873590 65873603
    0x1203090506120f040516080309040e010b060702010f090504090b06040516021902120d200307030207090906020714060105010207050303090a0e0705040315060509090c0307060e010509030105040606050913 89
    0x10f659450a40b000c045014108032030700d008158600882180000c2143c018050b0345010b15540c00380c5008100c2207134880092641642d0400460000c01e0341c0c0c00003900d004540a0900c0c65100802c1ca20031030382c101f13680d0001c03a0300520f00a49407040c05520480c1e10302c100740a6504100d25184d03c2d40402d0844403c0711284010390003d1101c81408124485030185148090300008680210007495402c0190345940c00000035950503102c0e0400c0322074030180c0030107600702d406145400003d8034000c0d190f900340d025210304540c8a082920400505a04031846290040118030301c5c1c025409c00561910020712a4a0051007804c80100c1c00d49004022944c26020050a50079005d20703202c103080c4040c400910300800d02c031080c40004040786000c2044860600d404100050340c41c141800c00940708000781c01c3e00420f81c0150030300701044d20005500c07070680d0210308041c07018600d43c00049829100d12410306406500382401d0104001907508180c082d200c0031208030031542c0d01c13980300c11407016880074058200b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 65876090 1250 65874840 65874877
    0x3091202030c060f13170c150712201506181602010605090405010f110f07031404080a03021c03180605090c09042004060803040e0c0d061203090506 65
    0x2d610703004004051900003283c0035810300d1036801c034032038500b06550301060902c040209000c6134100c0501c03001084001c11941e403c002c41c14000c03614514044d504000b8006100d21401b415603a0148400e18203408000f2005040300d05100d000d1034464200c403034134110b9006000007141c454500301c071450b40030481e051038038030b02e6a6a09049144000c807200340001907540e92440810203403203026100d84914090000410400f07800460f10040782c88030707044840224000e00c05000079a60790f404440d49c094051501204d488400503074500745100320340c080051407050010400800d90080307070411a281e41c581150304541d00301c050907026584203603808240040c3e00d840c03ca000400540c44640c01030309000489071004210f10104941c160700340c80030380340000c0c0007014031180c0001c0e01c0080c120482c140e034240900ca2918046641da8012030040c1440ca01c0c1c00d00020b2088502081030720240ca81000b0b0501800c1daa6580380c4034240b840e0802500000c90050300407581d41041400c50702da01214040e003241 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 65877340 1250 65876090 65876113
    0x20f120a030207020f060a09150804020105030f0703060e0a290f0603150a1202040f0b010516020d0602040306020a020d03060b120a0b15090f010329030f010213030309120203 76
    0xd43c0000e9007240c1c001c0703555100e9849500c0304070150410441c66200c0c3c607805410004684d098119920426040140400402c40140d0b0b0000503a81c010f40300c840300b0025a01c038000107802401e403907001030540300c9480042103070003070040d089010112001c1c1c2c000f1001d1841414048101c0c16038144468100b048644000070b9401c0050056030302c101d00e03052603091101d035540040c01181c5250311245450507002e2000c0198a014407500507024040d45003085041d0352400017911901500c101d00790a2801c2404407000c6d9100e00c000c121480b540000115034560b03d0380b0b058002904484622401441501911402d09000780300d481c040e42e40c1c5130442424503151125000b002603008101d035600d2a21001078207025200c1e6180801d600000170f070b403140c075400031005001c034107558161014109403e200498007200f0044021010111903000c01716420301c220004280350000002c0d428485610024080b8240c404512464003600d10030760b01d828406554545040c0b007003107540307030181d4180c200601a18 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 65878590 1250 65877340 65877347
    0x1d010e181801050c040302040c1803020402030702030c01050906070305011a0d050703020409020d1b1d0609011b0c140a03050d030b03070522050903070302100e030d0606050a020f120a 80
    0x160701803071000c0520600311200c0e039118207550044c0c408024640010405004503d0035000301c141403207591030300c019070208070301400c8140a020300c0044e008950010114500510038002c07030310b4840b4072100a002e40e003001e041740355880400310303070150001e85890002315000c0c3c1ca00004444072010400032a00b000c00d211040e0009000c0a0a05c0d014140e08200c009a41840ca001803c42d005584100060903819140103805220842092030100b0600f20b01c50600c0340c00707049500440d410b040e22074645400a6100603205c0592403042404036082c030701100020409e14402103025150074280741080041c0242c00e001c089100c80c00014180c1d0003454404c0f5400707100c1c1d4800c3c50500c00040803503500c00e9848000c00c44450a15049044008007119805690902c500a0541040c0c640008524088854600a45031000c1e000c0b0260403e441c1ea100c01c55810081090711011500000200034980c1c3e6950007400542c00301d0301e808054014070060804d1240c1c00300380c0501140d03110703c0e010314114280d80100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 65879840 1250 65878590 65878639
    0xc100e040f0e060c131701020310060827010603210e270421020318030c0f060d09020301020316030e01050610050a091706180303040201090e040f0b071d010e 69
    0x62403c11707100a0300007591101d0864aa155002040006a030317410219020200000903070044011301c1141410b02040641c4003a0010490b0480400c4201900324803213a80d02410031584090454580480c00c221210402180030840b07da00380c0702e07900d8420b500300900c1510546581245003190210340b000060307441c149050b0341c1c130070b01c2a8040c02019104084151011054526240050b030000c078916030b50b650046080040d8840490007840031035440400a0f640040b50030a0303500030a80400d040c01111010317007001c0101c2c0d0740140207648920701070306841e9042c0c02083c40b00f80080c1c2071803984030740910107208140c01904094550b4103d00d00c44c2c0402c0c0e07242d0340503540c03206c01c020495400040340d00151011420030a6004041c060381c0c01c0c28243c8402281e0003800030046500200148401072ba0849541070460b0f002400580c8555161f003049003046c2c2c603544001d09510401801c2180c000ea010404802180003003517440004a0508011201245642c1c03003103821200e800c4030480502d5884240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 65881090 1250 65879840 65879857
    0x2a120207270b011715010f1701090e1c0c060f0b0a0302040b0d0606030c06090f0807230907030c092705041b060503041a09030910020c100e040f0e060c 66
    0x48005000346844e030400089a21040440404902c3d2101e0b690007001e400060140386401c55148114068019404c0c5040c80b401d80196618041031100d40d200b480784581c0170080c500340a85d982000c100281c039411589008031105860a21107044a8640c0c2c03007008000c0c50082c1c0b01c20031803070450782880018401e00c1c00c51a8003c0540d0500320008000d40201400f861103078801108a0f46070800207080352210741c00c504a640740c107a5080c0450200010007004941003030716401070001d4212130f00c0c07001d00201a20142c1200c041001c028401740c060304414000702c1580d5513202020740d100501007882142428008a00340006d8111180900d1908995040f501848030f0301744030042503080c1d606400d502d81c003804c0030800c044200018008005000c64441e0410301d203120844c506050019144d12480d1401e621510b01d842c0085078a51080009000444024003410340e00500c03820054407800001442902c03542c1400d961200204490181d00210300c4204003c250503100d02000c4481504522503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 65882340 1250 65881090 65881097
    0x100e0d0e031213050301050a0b0d0f0819030203070e0f0a09091707030903060f05010e070809071802130f0b032404060608040308060f09072a120207270b01 68
    0x140380c0c00b584140c00900a0391032061000c0030151802c0305060a403140200281010f41c60281d50f06204d48419101e481c01641c010114940b004c49480c00c0ca0a500401c07428959007800c000001880c00d41641c001c41c080e41c829200c4800d984401d408211462050898150f00450494810000d071403594001302d00841c401c0d19404039400c1c0b14068141540c01440f41a00040e003100810414840113100d2440a0000348030305000795810804017095407079000e0111410003080350300103030621000384501e401401d9110392801c800c1e1541a040c40194003d00d4100a480703001d0800041c00040d4600c4560031030301c10460046c11665070050f000141a1200e55044410040d044a44080d507158401d910140031903885a400c41c0c00c01d410001c0016000421180c014541001030036503e65030745070010340c040e2180c948010811120044040915502c1204001101c00c82040c04100944096031000d07220495080310030341980d03640304c1244986041509581c412519003c0b42c000d00168003e03000c0b0240604 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 65883590 1250 65882340 65882353
    0x31e07080a05070c06170c07080c012405010206090709150e0106030914030703081603060305010908031b160807020a030203030a091e050112020307171305100e0d0e03 73
    0x84914000d5802404440c0004000040d01400c0103583c0c40000041c014a00c0e10000c0041d100743c8203000a04050b05011002c0b0b0041001c0040206000c108c440b401550402813111003200c204403441c004546400c0d040a950b41100070500f0b501c002a0345100d24020401030031aa45071240000c01088c002244600d0354402081c041154452041040e00800040d500050840d03004c1c182941060321480c142d0040e070700200300703c1010907070004c1020382080b0000c091b00c000700821903050380101200e910091540d42031088144c18084500003951042a8074107903020409000c001d0b5002910030742c0181c05290191000030030105224801400003284090043c90306d10b512074002a02c0d43d00202c840100082ca024000d00101c00011580c0070980c02c040300e0301a8040c1410006007102d03130181100d4038102e6000c800104441d106002c5c04010320614140c020403070404c0716100c51200891003094070240301d213090b0000018003601c181d0b40d10704100d030301818000160980448219410405280e414403a01c2d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 65884840 1250 65883590 65883593
    0x503150d020d050d020606151801030e10050108061003050a08070c0e011403011b020c130f06062c090c030a060e0c0a0806030303060d0b040305040e070507050f0f031e07 74
    0x18050b40c07815902400041a580e00e40c40c40003403400000502280c0034420040c8604848a044029140040d4028042e940000c5140c00101e004050819903400315104641c03840140c900030380d0003d41601d480e081981d940d51f40da0111038509048610004010f40d100507a00300104074190007808840303201e4207841c1070307440e5102d080c4e5011940030b0300910320503501644101c00b00d113070900c0b902c2e0110b03404a80341250860307440c00180d220800c40640754050480b010f84291415400d50010982d001c1d4180704001c029101c0400a00d001d0424505042100d0300900790044040016080c10110600500014883e0f40c0e044030300703803036820140881619985a100201d015250004424801d107100c6548030723201d15024200400400d005826540a90400c20600055860b00302039014581d802c0f51088030281c035a454111414840c40e840074203c14268010321040540c008006e002c141d00500c2214901003110650507283e03000b10703036640f145603c1081309031680e4911001341e203001c649102c2c0450400015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 65886090 1250 65884840 65884849
    0x30201020c0715110604030e06090102070902120103150b0a03080f131502011401050f04020a051312060f05130209070c02061b0601080a17071104090b070f0509010503150d02 76
    0x5030f00030200c643e8200c04650320603684a90300d0b54034100c8090041000f81010744010b400340140014541c00f5030400600100a40d0003004588010042e00404558400c1d140010300413181003030000f11489000c500c041c0c07079020414003610001725001022689594595a51045540d10210848401c400180141310001e524404110011300000e0700c60490518030600083c215141ca81039250f415440300018022074070307511040042505c065070016595400701e48184c0395802071050120b80010441c034081104004050407d5400e48940820301203042103008180540d4003c803107140d001080340d0791060142c900490450b40051550800e0204800da64010a015902801441042c41d80c2c08484040d0080b040002d40d00603d0340401510305402a5aa1400ea0410412105039900e4000c94100c040c400c461451301c07500c000c018420072000e003040c500041181d6040f50f04d0400309403144035a10015000e2812156041c02c140d4031a031a5a40e80300540c8002c0d00c504a038241c120008410b42801620ba = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 65887340 1250 65886090 65886103
    0x201090806070c0501110c300301121209080d030504110d0b0f060907020316050c060309010905010606090b04030213142e030f060b1f09060810050a0b07030201020c 72
    0x8940e0302d034100d80f141d03420180d00395001ca01c0d441d03400340010086c4410b100c1c404a0007005407104009802c240f044545095498240842d1882a8400001000103100e003180384442404c035110746581440d072058013000f5138001a65104400c101d4003c45001c2131507502c0b0764000c5a110380f05013a9840720034000d1001c201c0c40211300504071050040c08044c81288528100065400320341150000303014500702c48001c0d00ca01501038030300310140000002c03000300481400101340c0d903140500010385034980803440f40d01801e51000b00781c80343d5103800c901041680c0b2611040041d140340c0340819151501e15030911541c01110381d1345440c0300c1d030b584001d4119032540ca145540280c10001c08016a07a1032102590200190ba07121040c00c80c140e008200001784400340000384458000c580002c1c0410202c0101d011501e42c080804030000c1041192220590890251000c0d2074007a503a0000035558414265508482030045a90100e45840c0801c0800742c0ca0000f051080e11900c000350520364200041031404070b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 65888590 1250 65887340 65887351
    0xf0111040314010606020a080f09040504030e040e010e03031503031603030203010e0f0105150a0309020a080105190204030c0306090c0e0114040e0a0201170603070f0305060603010b01050403030203030f040201090806 94
    0x10004041042c49501803520300c40c84180c41c001c0100514051001e55995813000009101d40e801141000c1c14070b0410b410355510500203041407090b0f242900e07000301a080c0c040d4070580308a1619102500300354051081e11148a41000150310750f84a010950141d1914100303a240d0603c4100400700d001031100800b18542c900c607407005078481d4108001070003000300048c0340e244810101e1004010969a015996003500e958004403643c0c0c40101400b2805001c1408000e0340002c032b8440300090781e0ba01580035901c82c0c0e03403030309848040003620000c400603403042e484060034015424000f80040303581540141001403040b1024444982c0d941b03100300300803000342d0000c8454580c6861000d0281440d005a2601100d02e02c040d0010003040d0780007a01c3e4102e4040c02282c0d41410500103039040e202080840003a0000082d030a42941e940d16050780d9852003164210b01a50a149200030f00354080c81c280d40c26294180c0103181036984005010f0342c504001071084e8108800340400141d1454107101080c01403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 65889840 1250 65888590 65888621
    0x60d0501110408070602060702060a150e090a020a170a061109090103080a090506160f08090d050102090a08060603060403050a0e0409050109030233040203010b0307060f02061023030f01 81
    0x39880c2c408561304000840d40030105540104040211117030780400e80517440b0444250001d0000030209000a100b031051304000c50080402092200440000807454511442103170304040090725201000b050f07010000000c1d04c1039200c096211300043e040d41101d00b1003c010340c0141e007040344840000d841c0301c600b030384280c0d0324400c0003c1c42041c10b94091440303005010241e43e014070300301c9a04040041558105406450090003511003800c10200908482c00300d10010700104002001e818414002e52108510a1050001d00400507203840040388042c1b1418000b805420382d0340c0c9035202a919070784208850410401325590342c6401d039460341310b11030400e402800000f034540130030700d4080c2c5052207800c0d0740200320541a040401c60503131448031a40407144510407100d940c44070b101103409401060700290345401070340d50200381603510000031004007000b0b508032401074a40340f120030300c41201c50144141da0228078010803541101c5890b443c00084000d800c07034444005001c038807401c65201220141c0311 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 65891090 1250 65889840 65889847
    0x6020d05180a0e0f0c1213030e040f0e0f0d05030f0901060e011511060c090f03010605060c03030f0705030c0703030b061b0706030c02010204050a090b0a0b07030503010509090321060d050111 83
    0x100d013156006aa0001400f4019850403001d642c41c8810b04500400c5041c4514100307081500301441902080400c400240c420b002540702442d8403c013030440e51001600301d1260084104050600144041248445460b903516646488040d0011036a00901c068480e640340c800010b0802c140c9120a40280304047c6180704141c3d070b0500c0100301100a90b01c64259030b01442c10301004a034140200d039214030048640c5a040c5024002090240c0500c4d80310341c0d40160f000c20b50862021011005520485202d040564180e83d640800d81d01c0b4041580c00350b04560050140724006406940b00814407880103082a0903c2c1007042c0d1100901e9602e2280d2145410003942081200e405003d84407444082c0d0009508040c1050080f0b0101e01d030621951084640761168160184ca41c600100042c1404c42d0b0f1650356008641409081c0c1e510a20446004a9404000502994011041e10004000c11100c00080100c501030203c03c080c014080b9507004a550641b140000c000f4031810030000c6821440684 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 65892340 1250 65891090 65891101
    0xd021b03010c0e040e0c0301090501020406030e16030f060204030f150b120a1209410f120124080709020a080f100302060c0606150406020d05180a0e 65
    0x15a5100421118020707814005001c004580045550000f03c0040d40d00180122903086254689042120440c0d010352820010340c0500006400400568030700e902c1c01e01c415030b000c646e415038a003200108810001503550081c800680b05407a03801d8403078010240036040a450f03171100710400e206424100c0e0039001f5402d451a00440f103001d040c0d2030007002c507005c62111186484080c0c60f441040c8000303004038009075090503680c1c042d03215100980701c2031340010301620644800c418000f00a404241030050b40d0074002824007824265111051000703442101006912070502c0380c01f0500d1070b5580019500c0f01040d11810302130102400000d04054484142e0f141b03881a541d0600059800940480d401007025007209030304601c00d10742141c1103d0620380700d03540d50514100b03010002d4200943c002d90002d140380d0b05000c0051303424080c0404aa851400b07941c46421014140715500ca4000580c00c00300034102041d000d08050b21510400e241310071054101100000c0d0302050310b410420859520809020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 65893590 1250 65892340 65892373
    0x26070503100503010506062d031003060506240307031d01090605090609060708070c051203010603050a0603030e041e09060912020a0f080304020d0506150f0a0e0c07140d02 75
    0x1c0080005400800c40c50504c1d001158541c42180320340c1035100036a4850329615408850031030345400301c100d903260322030034078a02d0100442d80900c025030f40c0d942804081407651410344100c40c4040c1c2c003030726240c0201001403604031050300b00511120034143e40c2e4040d501d00d01240c6c0146000c0b0b81190380006000d209901c0d00c242112009044940301303520000c00c0181c04100000c0458100d02c040c280103c4569a10f4811904405402c2009047c3e018048083c0e2403040441b000d14141d0320262018002d6541e08410b180481e5114403016000507140c0e82031400c10f0405621507014400b5514240990200301c50507142511071f0300d102140d5195031800c1c0c200c01d00032503440e0085243c0725840a000c50303500726280c110803000700a60141170540004046421555901010640154408103485003403030b10b9001142d174848007950141c05011038020388211450958400c030300340d656050030b007606911040310105883e041608211085c0c075510111103c001000c200694200c8000d40c01419090351604606 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 65894840 1250 65893590 65893621
    0xc060103032003040308040e10080d02030702010e06090d08030601270518040b0c0d1b09030203122a010b1305070306090c0206071101060911030912040f0626070503 72
    0xc0b12107400601c07040c130000388004121800ca600c50144c401c843c0d220318028904100007940032100780e10a03201050b41c06d076000701c00703040024006d8071113000c00c41401042c0801d500ca45034a041d40a00552800c60015001002454200308107250100034401a0600001000b950303d0b295500100650002c200510784210700781c01003080302982c2051404c3c19521403a841902a045020400e0f0109954420014642c0300740e0500780c840440080300701c00b460001e0701c650301c94042a806030041041c1440410400b40480340c280240040d0002d040d9044000303501d0010901c0340d507036030039501c4440c1c3c40465510010f0f040e40c4a034045500056a060507500a003c03900c0540c031507203842d0704040c640003005802141c207951148042c2401300c0c81400500009005003041c1c2c00c500e0b00c130392820040840d2410a48040c44c4940314110486810a8089115101e1030186125044101c09824014032071036100d4000984ea0110040b4000e40f2440c1090501c011034030200c0716040010401b00400c00d00d560000001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 65896090 1250 65894840 65894897
    0x60103060b0604030201140c03070c031103010c1d010309050f01060e070e0a031106160c0807030b06041808280e0f010c020f1c1e02090f0903030a0c050c06010303 71
    0x2a030340b80034519400600603240c0799800c1416800c010031202000d6406200b1106100c0e40104070508bc03a850707103800f06107103007442c05540c007d601c2c120f01c01e1002409002d00c4200003144201403404401d00c1c038011070282151000c2101e5070300078605144220034090155030054200c1144807030403072a0540d0010007841e1071a10103031090107000e80c100080751011242030b07059402541e0b8140d45042041800300d54040c1d205d001030402c0c9901d8000240034001013070020580b48102115502030f00c0f2102008282e4044410410950701049403601c0011024001814064041540b20b000c2c50040c4401e110340003000010400410000c4140e41e559150620580816140900307100c54644900d40129956210504a4074040d08846018480401c020b079550751249074041c0da0455480700620207108a819800d0f8107d0040c580207000c541c0f1890180004c1d445080c50100070f41c2103a840304c03a10f0001d081019045020300104200031000c1300f0f01800514080c60080d05e542c000019a0220340c011303407848909 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 65897340 1250 65896090 65896099
    0xf0915050616050d050901080f0703231f03020f04050403020a0f0501150503030a08070e0303090306090a0606210803070509030a0c061e0504140303161b0e0f070809120408060103060b 80
    0x440c10282c8e00410660780001000070109074030b5071003003000d4000784031681d0050012045030a42c00000144a8038003441402051211841e43e1940389000f004003d05020080d03000c0445405900781e07040c0399101c0c070f601a00a1049a01c0d040341c60300c2d1140c0200d4485002e91300350b5140c044400c000324005410f207004110507070045252200c8040010a507400c00b0f06604200f0010042c1888140d82c00c00642e03c000340000e0a5a202e07060540398135039503070901e41c0115021810030f18002120300c5200e440c4011011080c48070040b03001c00342e031800340c554401469201072100602c48520345460810810513604c0c81051581202c904140010b00b00902c8ae4000180076040b00306010f01c1c1580c844141d50032180c80c00ea901480652620009085000d00010317421f03030034840200242403000c04000c0c1826a050400b000d43c195447e10b403481c0c90207000710350807210000e185002c900140d20414080c0d40c0502d441c800d40d0607240303041551422503801a03001040c6a1b010380014401d03c0b056101d001c1da4200100c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 65898590 1250 65897340 65897347
    0x14071707211b060510081015060504080d2601030b06030c04020a020a02061606020a1d010306030308070809100612020a0509070206070c050309030105100e060301060f0915050616050d05 81
    0x240340c0d6002500114010b102d40c4d10380700030820600c0300101750b40c0940844415030b00300ca284241c0160090041c4c05412a00d0031240c41e00041e002d0040302101e050700d10900203000745544c20041a20000d0549ca00c01034030004480c800540070603100405030296100703103601d154605007a000c00d4544070b48800781c2882244100451101940c002440c03a0803241c0c15160680c50301d406824044000079035907001343c541d5000160748910103600c00000010070181d00c0446052803c0b1000440848040d800b00034081003d1101065460307009213011544101c0c0c201c1214808a0f1044002d016140390350302c4541a481410144d0b021441c1c0703428018041e0400340ea40d02d020340b8061800039505e0301c004d0040402d0000900421050120070300440d20700c2070002d00203121900b0030740c580390b12103c0144030b841130b41b224840101e01c50345818011081240c4010030402c184a040040503030007414040301912070100001000101611110064403200480c200700a0240e01d450800504100510040504001c402c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 65899840 1250 65898590 65898617
    0xf0706030504030e1f0e060c06010e221106030606090a0608191104030b040305070b0103050c130b0f010e030106050d0b01030b06010219030e01030e1501080c010207061407170721 78
    0x80201c0c010b17808a282c1001c0210911010903020b1194250050450203030b0800031a1440900700b00b14043c89000100080c0030310440800040440f282c0d0300204400c40a4514814505e0040d0103036800c00307001810b0b645040c4009002a148a016a0040021a441a04000d41800c9201c02408180595001400000f4422412007440d02c128080103204040c2940441c040c18411011380e1070055210f1038450482d6121700300940c1d1a107400e01112702c41c001c4045140043d007800c4c086e00b072804801501c0c064040400000540f0b20100220049406659429002419568062030000305901440b941269541517040401c00d072400140414199800200e406050a084141e00720780c03981c0502d4054125080540101c019061021104407a8401e030310400d243d0042506644d030494900760115074070f600000005a80b24a02e62180001081c0c074088240072152008000700306240c4981404000c0340c1046003ca091504050b0064840c030141d2081040d1300800700c3c003910309040d59418000d0b01c0e030246 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 65901090 1250 65899840 65899879
    0x30203060c0a03020705030f0c010b060c0c010c062007050c030303040209010605070c03020402040305011508010513030503100b070f05010507080415090312110904060b090303070308090f0706030504030e 89
    0x1404414111070006100901d161003a81a101d00e664044141da9075180e031003406100d190030011144a0035440d01f641c0449034a001822203086d1841c86026081d002c00713031001554000301482c003d846168443c0b484c2c10600640c81c0d40144c500e05001c0d075460725201c07681031192420049040543c0660b008005110159035118111811a400751612560f43c1c2414075008000c00c1c030715413009401c1400440c003c02080810740000200206000c20303080c0f51640c0d0aa102d0a850080e04c80c4100c000210ba03c210110b4070034802554080e03485030003200920380d14194003006a0000c002980d401c1940d007e20803c02c0421b0040700c0d0010360f40d00c0d00d88a01e003030503180d5218030b122502d41810100c1d9175a07014420036004035101c104885143c80f08014240351031010200c0c50b802241d62034400d624044000c80d804400c130066800e0131001900450420282e40e07400d480744500940340103041e00c02c007008a020b48008120640c054119070f0760115080c2060300d40a840c14101d001a0745c81804800304405000e0702 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 65902340 1250 65901090 65901103
    0x9050618070b031e07080105090609010605030c0c071205031c0507080c0a031b030b0a080703150b1c06020711060a020d0f12050c180306070507030c020a050d0c180204030203 76
    0xb02625415641c1d11074040d00b4032418116401c10010388203038000c000890340c100c18100d040310f03c1919090101e0740c0303007020130402c1202401044080360042c804030760300c0b140b41e80140ae100c40a500c220350341ca684605c01c83d0305401c0010000c40b050360000403802041c4983c9401e042c0b41c0d040340282805581271103080038000081c000c1400383c0b04040400e60403241480f07904111000e2900810050650940c1c90000f40600318817040789000707070014400003402d008001400b0301240d4110150750205003401504801405243c1d81e0240c0c00402c005900d0350320900c0c0420004014450a001070340c2d09a60f20701410036800c0310404a204c2e507014018283d4150700841d64881000c0589407552441055450555201c0040c0d00301080c01403804040000070480741004100c0c0711201d64816145a1303510042581d1813074102d981344002202842520f00203802801c6010403148000d10104400c0d0303e500118041c016200b4054400354070b044410021040c01d503504151617100d170f610541c500b50464020907629030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 65903590 1250 65902340 65902349
    0xc08030604021c050402030f03070f02210303090f060105041e05190e01090506090105040c030b06010203091f030e0f0307031d060c030a02070f0e040201050a11100905061807 76
    0x4000001851941e441d030494030440c02100a030180420221590001040102da04a019104003103164059075000070590380c0300c9034000641c55014480d642400521150311000b02d01d440e000c070480c810300a4003400514400d8800c82d004001d0b0b0003002e10810320f040d1040e0b2029009a292004407080040c2c02c850030b01e0510381100001c1602d403280a0f07103c00300400080c0300382c1107520308040c0b04100d64040d080501428080c208444494442d00007043c207d5200f95002404058000c2c1d0410014006c45103c1da40254140162800c000d0b034800801c0c40180d624041c01817648850400171078840d00340c4a04420486094010300701003c2122180fa607a10803c0c070b010b020300c030b0a45000c0d0403207034013090f003054411006400507031924200b5044581d83e0f001180200d0150054090200f00c940d8929031801c00c4400416150700d190b00c40d6001034441d0f5012a410700200508406174035481c82040280100400c00b1400003d210760307150401c00e081c200c000e0040c0c0c54100316200f188440b4000040c1c8142a103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 65904840 1250 65903590 65903603
    0x513150203040f0b16110c100c080d0c0309120f02060604090c0312090806010b0304120311090405010b0a090801050907030b100e01060f030501050d020a0605130504050f04120801060c 80
    0xc0e1103d052095000c50b1420008203081218010403881c0d050302c040c2c2031400c80c080c0e190003c60f088500c200640340c284a110307030354000f101c12100382c3c4000e1081d00004441c81c0a00000c40c54040811600c005486440c00c018020035182d44032801000510498041d121009260103000c081c61544020740300d44028003017510840e1600900c80900c1000b000c0c4100a42d440008821003420200003e041512603100e000c0081c0103443c00002c9146815003200d00c26503104503042005500e440003034000b490708000c0c119014009000d5203030161251b10a44e40030f807019005864603200007030b40081c80c82600f40c20a840c0e40c2d041900b80714000200064442c296680141c1082841c0d541c811403c40303103121039001c04194009080005001500900c1c1400881d500c2d95090010760f80301c1c004e0011200c1c43d12802504000c0000c020040c2d28400d20141001400c10541500340c1565100040d080c0c40042e10407019645d61002408108006103c00c038501c0c50701c0342049103056140c00400350084203c40b1001d8005e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 65906090 1250 65904840 65904847
    0x9090105090a0e0106031127011a040b0a03090b0705040302010504090b0111100c18052206080d0203122a0901030b040501060807140c030901140702030604050a0605131502 75
    0x19407125800c030098100083c1d0080007000d690341042e544141c1c0d04510300d8015505403111072034001a43d03a240389500768441c6e000383d07580d00e00340300c0c0b00c070040b4429000d0340108070a00020940306001c0004103070141090703401140305130050130910b079800c00242416050040070401000141d821000340c501310340108000295040000005851462100807001c1c0e007030184200028000700c09601405003108260381c1c05844ca6440201035010b1091802841e81c0120541000f10340b40710031007103141015041403804102581d4030022507140038014010340000d0380001c00c43c1e411003201a00c101d5400886881010701d0040000011003401c07202d80e400c43c01c08000003401480c26402600b01c01c17148070000d0000c201d25a5520300082c0300309019616600068203440d4400d24907042070081c2d6101480c040055460096a100191101105004550040c81e814414040560382c14450700b84120b0165000d410007031b070107281c458101c4000400d00400c26585050300404140320480c0d5a40e01d03119100c00595 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 65907340 1250 65906090 65906101
    0x9020d030c020120120d020c010603030908070905040201200c0603070207090e03040f0b0703021f05011d0c04051c020301020c0c0a0906080606010815040e010f0f20210f061003020909010509 83
    0x1a08c9079030300c2942c2c030b9130030311800108143e1301021038000c482c1402d00342c0b0702d150340328072400042c2c03542554082d000800802d00c840161003031f20b03c0c00341c1940c006800c68000708420004240550005c0320fa400260700701072001c002a00140c09081c15440c2c0981c069448c0030704066110320115924010103e42e0400450040c0c10140204116420305020b400c0c42c0b6100c2d00c90b2520500600400d025904015841224202c10f841414042c1d600070040d050416040c5810002440200c0b042d6a00b0004904484020200561400e10041081458072005498291031200500030100000c0c0e00940309249014803c01182d0300c045401900a61b00f4070b004007003034940c00c605540c0c800c07011095076130003480d03c01e4075903d4a105621920050140707003c11b2002038424000d5504444541c0c02441d03e07a0800708050301c121042d800208203c2c03072112101700490686006103030f020300c000c49801c0b011031095402d010144c589100c000507403000c145010f40c80c003032181011500801043c464a8012442e0001040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 65908590 1250 65907340 65907367
    0x90f0910060308041403060403080c09031504060c11120304030e01030b040c080406050606070b06040e1c0207050112021c0506040b040e010204030204060e010e0c0a020109020d030c02012012 83
    0x11540030a0301001c1c4411900d03824511060f91080c0b140d17840c8645da01c401c0ca0103500700424118070407600744d02e80303540c0c81c1e035a1203030070600364405800c95915000c2c49110407220ac04202a05001c0c501030400003454046019001c0e14210803004800203561000c0548000465058210303540546d0614200340700380c01200050313014060302d00fa9582c0c00350600b03410404542c4d01c034800905c154041d06007407080c3d842e9102400118402c142020384030030807450001d6200d003401e13040202c01c800d100b012900307108203501c401c038107544c194a910303001600100000c000c2c03581c0c001c45400c0d21310305086d011881c140100440c1d10400d411b0584003e000b41c1c6a200254a5540d81e5000340d880c0d0740c0241041c081141c119403003038000c2d0b001d400300300c2c4036905c1d020000c0345100700c0c405020f0584800426810164803444050b40940c3c100c107021200315900c03a002c070340c0183c44204823004014804c1e116a024141c80344000341c41d0156500c03854035044a2100d04d00401400010001081e00e10358140384c7e651080900c010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 65909840 1250 65908590 65908603
    0x1b0301110301060f02070506270d0c03051522020d031103030108030903010612050601030b0a020903010911030d080610050a0909110a0f02010b06040b0d0209030109050318040506090f09 81
    0x4401100021000155142c0c200e0300341c0394620903950903111540d4a420400c00c860140352278070031130a642c0041058030301c140744c10b0451251000070600b507450f255a541e48071200340d01c0d41080307800380c110348035030141417004103045030f0000300080c03200040807592542004100078550000c1c3c07040382000d495030181340c051601d41e95001d2381e03041500d64031740e110014036650383d1000c5840341c003a6180030000a403880f1a40c240354802c9074010084c01669281d03844080480070083c08101400383d003008000040d81d02403003a110510f1107145425149201c0b1000c2508202000364a8024400303a0800c0120954400141e402800880e0410b56111205140119605503040c2c010305d03842e41c5000d000d044c0c12143c2c24080c14800e0850381d01d1403482190804101e090302d141e40768540e04501c0134801844200b01e40380160002d020303c01001030034040d0080000e13080d529000429101500000340007010740c8101603c3c0440d006054030280800e0034000301203030001170000c0219100261400100e10803400038400e2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 65911090 1250 65909840 65909861
    0x1c02030601030b120f2e02030702070b070317130c060311090a0f080c06130e0a090b130204061202130216120e01090e0114100509030a0305090405181b0301 68
    0x860207841603000c050303950321005e9030b406950b071107001c0c0b03c003120050114140c0701e598451207001c40301a007900d84402c00707904094416019401520804202400c01d2006040b43e58007e6580c0075900c07103c2c14550f49401d81c060010040c16046125560214118520f4942200e03494500000d05a200900c641014001e0000c00f950052142c58002500500468000196160903040c1e9140c01c86600420405104100d140d14072039003a41c904105600c00b550107140d00010f141c50100b0002101d95941350040c108950884100c140d201000d400d60030584519000350505c00b065a020290f6500003584071201c60354259002500040e0009501d1302840d00d03140d101d03a100091010f800841c0b5000380c0300c0400003484c10f0000b4941100003c00c8261441d003070741200c4117540750021400d94203003440002c0e0502132104003485400c22400c3c81d907440070445050164040d0341c5482c2c440c88003404120a80740040d0003901d2005401516400c602400320f60a00e0f509114048456241c015102190140003070303482 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 65912340 1250 65911090 65911099
    0xa0212070504032f061c0f0c020601090c02030d05010602060f090705180a0204030218150307030b0106050a140a0f0306050409030e0d0507031e02030d020105010e06010f05090a0308040810021c02030601030b 90
    0x142c52801004650440c6c60b0301007041428451942030b8003410003150b80c84107503240107a001d82c0c0108000007140c0c0c040c01e10700340f00c0d106480c5017403071507070300f9105843e03003030703001c800141d02038010402c1804050b40855002128200034011080c508000514190015400010520507240c003003501d080c40341e41103a00070750340a00010000103254507006900c02046542e80901c01c00b102d00c400c40c40c540810121b003503c0e8891020b00c1a82d081001c11034a50704204050014030110303ca07000401c40c0610042c1c242030140740e4030307160701011609004042d00d50170703407100317000e103042200a00002e5008105008542810785142e1211411420414602007407944042c0c544003104e1440c60250039105004400d050080e01110320b011103500d0b0880c202c503024411b22207802004008601658440c0f1035184a00c03d8626007203040150036400113004601590013116401c80004003004590000c1c06181e1903204840e10850800d050020820105034040740d071500030560000028030070341e0280d03100b122003100190 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 65913590 1250 65912340 65912347
    0x40614090d030f080a020f030c09060d2412080406030c05041a090a08060403080609060402040305190c17030406030b010c15050901060f0b0909130b0a0212070504032f06 74
    0x10b019010222150f549800641c0000c0014014090f41c02103c1040035441c240301e00e0350b601c02000c0f000c241c00c40d00320f45500c918104244040d6240318003075400034004d40c01c00303412080e211440300f101c0855194007003400002042030b18000b08403d00c0946040399490304010505139401c1c10200c40c10311881d0045e44411158201a80700582c00001818503503101743c81c0d0740c0781240c032101c8055988408580080c00988900b00140301410701c150000c1d00414064409400e141d1260b9403d030908580e00c603090b011035500140711041c411007451080040a118284862481004010341c0d224132583c00b41d101803540b94034801f841039104030918460f5940151a00448480c03d602c5080a40000da41c00080341d800c0030f03400b00380d6840004880d01140c0f5060b8a4030f2400e013a05e400d02c200c3e0000108940c0c81e40b050030005001080c0640c4507203210b000c2d05131005139203d400429106245c000074100b1003c0040c280018400901050910384078000d4450011070300902c85032034403210720900c404841c7c0041010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 65914840 1250 65913590 65913593
    0x1f05040c110a050f0c2b0804080d08040501110909011226070615060203090d140303130605070c0b0c03040501110c010f0608010b0a030b090a051605010806010c08040614090d 76
    0x22581065020021013a150542004410429240c0e003c900789070140c46c4024500c106994000d80c400c81940c4a5070045041c9940c42417118180340406500002003a00641003108000c001e10400c4100010386913890300788901c1d0400310b91002c005005104440003180c2e05601401604111100b4175900d03528819411420250070046541103214200d84550034070035403403400441e80704c1013400c5c1d4016034021402c1c4100041004000c01804200f81c0716030704400100742d8003903010310085108081301c40400d002c900491400300c080b114000c0a01d0100301400b55420700103450010302d203411080300707442c040d181d40300e42c140b171070060800b10070020701704c1000214541c6950781034002c1b600711607030b580c403c2041950350304045007610269980326512204801c07050001415070304046402c90315600c11582d040c9010741d1030a15000c2e59290409454071030241c104015070380030f10180ea000d4000e2030702c40140c0c1e40c1c0b60340f00d0311300380200d01601d03082c0725203401080b9050594800b80c402420303004001070034a114a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 65916090 1250 65914840 65914843
    0x304030c0b160e061b0601080102130e060603011502030904050106020d02010f0b060d020705070306060f24020618010905070905090c0a14010e010302040e0405070501081f05040c110a05 81
    0x14200c00c659603048000056141c840c0c111551001000c07a0710b9120b4100070038810071001e640989001c200c1e9102e40142c0d40004081003243c03a01800b48070000503036070711840c108030301c2001042d8051016411407070104404ad445203000d603411940700100d50b00032000410016411400b80c072003250b4006160000014000c0c0e40002d41858038185500208035454003025075078150f544d405406a0007103404c1040d042c442c84254002e061b8030f40594141c800c0c1c107441e44d035a0003d6a80960042c05088983c280501000f0460004891024061003a42131800d40007417001e920b8510007464495046860f480442c414442034204000341948036054a00058903203900078001c0c5400d560130092407040a800b000d0342e003003443c00380c4141e0b000c0c407e810f068803201200441e1000082420f0604250702848006003000180700d040c0d0081e4030403c090a809070600c00010f0090500402d03c089051991000303808200360011450280e420940d004a010401160161144030070b030f03860a00680f0411071b503042032110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 65917340 1250 65916090 65916107
    0x30306050f0d050705090c07050d05030703180f0b100b071a071106010911040e04050a03020c0307050616020a0506070302030c060c0703050307030b0d1401020c010609020c0601151103030403 83
    0x2141c012101c2035144007445841c10310b0031001001a40500d8050042d442d1403945603034001c0741004900d2510300d696640c0c9080070300140024000c214040140088650140140d40000300403010440c0e6109450b1584104012542c00c06442c50840c0c0010591003030102d602000a410190b2140d69201031a00d40349101760441c12003082104041d00c0400d00c11b81c4070300f08003004000040000d01441c2d0a004501006140640301000003900c100700016940c000c026001d0f1245000c2c1c405842140c2403420701030300b09051016442d1298004600c103011542d500402e44940101c1505900b407809020720120311900d00b5a08031582c07002d00881d030001050b50000003050380c11004001c1e580c503030f21895103034007140c0980040100854814800100b00500c2070340020b0403043c2c010f00a10b9844c1d015200e200202c0d010b0000445c1d039940000f421002a4001d02502009143e40d20045103400c04160a0ac3d40710b09060084f5280981a4046a56414411070071860680031174030a880e6641068900a008c030749 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 65918590 1250 65917340 65917349
    0xa0f0e04060b13030c08030c07061b02100e03061501020d03020a0507050303041103070801090f021e0a0b031006020601030203071712030c030f070203030f0f061201050f09010b060f040b0702011209030306 89
    0x8050140480da00703071b001c0305491220250f880100002410711206584000c0461843c44d02c80350400c3c12107000da075a00f0304a01140030b054a5080341083c0040a060401704010031250009002d17501d2020642d034000754070801500c01e4500181c65054a200c202c038079101d030000140c424880401400240281071740385c10b8030b0301e5044003122130090360340c204c103402d8844402c000350440300716240314070160074010b0311003016946540c040107200d03143c10001803001010360001d0000800100402c01d805190341d000300c02900860004000640c90b5a0010756558007500400340c521088600b0b42c02903090403c080c082507804241d030b69032246450708900c2c0841c0c000f26130409c00103107070700d011075046c034004030483c5d02135010fa00102c28540c2e41c1500c0b40c0e5044a018240f01d4105425403900c0c441003000784940350040800003200344040c1803828005003501c4040c040d081c4555403c01008030340d94130213403c5504031665003410a84510050005036104040074110410785030a020b030a40070590715070b10400995 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 65919840 1250 65918590 65918603
    0x1060504060f0b030105010e0d060e0c0108060103060b310b130f24020c06070b060a241b080d0c0314150d05100c0215010501050a0f0e04060b1303 64
    0x107940b8000a0a00305083c8600304000a08000510040d481161101640c1b8000f612075407007901941e94882c02c0b030320501c4868105400081e915926036901c8001c0c0784d0040001d107000e010007401c00c600d241c003038031483c0d2080032035041855041c640c42c5600808440800b4100b55042e1980350b440066410780d92200503d40c0e030300d000414001c108828034130541c1050751200211260312004400000e03c0000d0f8402165040d4441e100c4400d0a81c3c1d6000e00a001503031142c00f0701c8109040407030501c121000c6039000f5441c00c00f05070102c544510f022100300503103c0b5640c50540c41880014040d20710f612642d20001d800100c2c00600900b14880301e07001000580c0780c5030b404004052000040e803030b5100080d100b00c0808180c00075488070342d191084441c20f056008030305a800c14146012154215442c5090b03080160704242003140c11104640f0400d4010302c0c0030700781280340c080800f00c02410458001c4040040c0100b24800a030141c0b0389a2000001e40100744035590303500c410241400040341c9920044411 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 65921090 1250 65919840 65919851
    0xe0d0215071415010311030c04150905100303020c09100807060c11090601090b070c0b030a0c020d110c1210090302070f051206041112010507031e1802060a030e06010801060504 77
    0x2032040020848000c040f1050b103002283d007140e40d40f003200301100c04403ea0504c9110f42c1703620155103903c140c11825414000c0d80c1906841d00002c1c0041d1b80006241903a1290790803410000702c1e4003c10400b41d07a20341181e00e2000c541d6070800d031400c042e4040d00081c801e4420500c002c1601030b0800b081c1c0c00d10f2030080300040318030f240040420414410803a48103000507182903081003c018010060041d0912a0b80f481c3c0c5469112207000d0342a401c00c40f86c202040340c4501d0310b2006543c044c48207003401c0c0101d1610240703d18501c40010307600c1c086411400d010ba0004911449080800c2c08001124880d00e40241b016060508002755620118000e0260b02000e00c200000c035440c25610500345c0f02c032058040d04171650713103444000d1745424080030a0742200d495250b43c41131310f100b031040354481c04294400060488026444850300d102918980750340c50b103010034001c142000c5000b0500e20750b50454820740c0d034900841d0100c001d41012408280c0a00c294070002c00d4001064000c04182c40381500c00708103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 65922340 1250 65921090 65921123
    0xc03051303120c030e03160c0b0403170307030e030a09080c0609010212031f0e010f050402071509030e04060303030b150403120c060b060304050109020108090c010f0e0d021507 77
    0x24080c0d0303a0080108002c0c1c905501e4040440d000a802d59005003800580034405843d501d040d036001d68000400340b0840d5a07111701b00300089203c00064030f41100ca5504260071030f5a010201d00f40309101444004000c000070381c40c1442500b111300c01e030301440f0903240c0b00c41d04031001600466090164004c18041d84a442c035041c200300055a0203454164020030440c060804000140c0e84041c00303c07564040c000115000000039034101b200103200c03c4907801155071428006240c4203000741c1050340715900410041c40803880002c001e510206410744000740c412500c3c9000d54822603000740e40c68006081c204000181909030307010000000082e00d10703500844c0342c1c034000c0031244541d000003080f611107ca07042c080644a200604400d030301c6440e0001e9804e00603000201d0b1170b00200e4040340c040c1c1d112000ba104650f440307480c1340d40202d180310041c80a00504000a00012007410561040002c86042c4404555440603044140b84d00980701c44210044a944100c043e44141030a440110f403100d401c00303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 65923590 1250 65922340 65922361
    0xc080406060614090105130e04080a02010c090f050111010f06090b0a1e0e07090302030714010e010f080622020408071502060603060c0705010e1005060f04050f0103061503150c0305 79
    0xc10010403400f0b914201c007420040d1202e41200d20210b07440d404000c0007085aa0030521030a0082c2d005005403a21101c09940007403d41c0c40100c001e008020080c3c10800c5864008100001500e0003400c000c103c0c3d110101c10a801400c122000d14852810f180001503074060a52029445000607138034a030b00c1e00d45030317004100703400911032190220300e010390000c021b44041121400d4120901c1d2408480b007139500e400291400b043ca411902000350034644a02203903030401c18141c6040803e0824043d0010700402c0500b80d070380001c00e04c81c02040b124220070f4052403200f5942c00c070b007840080215251034403582400c2d074650711401050703000c0d42101140541940000391003032003403d0090042030555188848400b86420070a01110290340300c03001d0039000d0609006c84180750605010000b400e107800c00170040d00c80d00c22501c1d540100d14081c28002c04010349a003a905403a0064804140510010400a05484a0340c005401038110b0001001031000c01d4200420045036a076040c000e03902c800300ca40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 65924840 1250 65923590 65923607
    0x20f03090a050d03021005040605070323010e09010603050a080403020a0b1c1805061608070c0c05040b060f07050102040504050109061508090304211a2206020d0c0804060606 76
    0x950340a40700c084100014079210703521100081c40b0b8810780381c009040064030000c2d5070080ea07080741c565031280c2c20403515a915110301c450f4101d0b096444c00c8003c0c0544071080800c0340600880341804400d100040d121002500642c0085600004541c04118541042c0f0401e8100740403c9101d414103c4c0006208540c0d87c06940c54881035200c040002101e4201440003001d02c403200346102c006811101300862010b100c00c030b100d03400300780b00da50504180d9003004008520080c078010030f00102400d10700105050008880c1941c200392400110b107400200021107034003c42040b42c1c40c00c0400900b0408202c8190007410450b0401c0da800d01203070342c031038070040247c034028000c07010341d00c09031000c41c0800b500c17840300ca50f0028001e0b8192407405458129a0341d00854a0524680804d81600c0c082e04020011140001e401801204c110060400c0e04034103c2030800a11280000910080c60320300340019503044646103401100104a00d10070440040c140301d0702181c01392002e17840c140703000880c40d000300e400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 65926090 1250 65924840 65924857
    0x100501050d0c030f020418060501030507020709050c0c060414010506030c0916090e010801020705060a0c1b05030408030a0815040b060405010c0606030b040308090f0c0f040504060b031c020f03 84
    0x6190820351804503003402840500403002c10161035650014145900303100070030161001940c40322114164025000507680903620550425183c1010800c4640c1e012600350700360350078980041f5a94581040880e0350f405002084800c0e4050503003400b0411904e9056800090b0035000203101c82ea8403a0304041d100c01c0c0b102403203508001050002040d4130f202c07560300e244e800d5050800421180d1100340551036a0000d80044000c0e03035002809009200302044400c0d400026150284026070f0b4081000308842150b50740c5030075488101d0040001c1040030700c240d80141c59840212030f19040d229100400001050790042560280d2024102d6981054000d41c0484a0f01800c1fa03881d1900e484011a030204d030f2008103035541c42c0d440b000072000620100189014600941c0c8910441c1043d00c105820080401400429a442810048200d4880a1410200c0d07801150002903a0b41e80d820301c80080d044000e9120340c54014012440d1030103100310030300e00f030114043d82141d07490782d41da45c1210765070301c42d0320701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 65927340 1250 65926090 65926097
    0x4020a0f0b1b0307060908040503280b09120d06060f08040b0f060f0a03050a060501120c0302040506180702060403090f0803030112050109080a0801140d030e190f0f030605100501 78
    0x8410400030b01400d40900e19144001200d1500c3e020b0344461040303c420840c1103c0e80c4e000002c0c101316901d01004807240d00811081c080d00c118800400c402e505030341c0920b000300f400b013030f06000410680c8103101c2a00d47c03e811350607103965031241954490003031019010754400f00c0c840603445001e80380704415140c810703540841003016a80783e2056040c0503c0c0010806030380140700c6030030302d0800d440702d81ea1400150710a10051140d80d40038030700a800c3c0c80c0c05802442071020b0810b0702002003000c1d101c07a20201c80d0180c500203415110b050115440204c844501008842d0a105000c951035000448500c50b50113a51907080c5d141d16421800081043c91280240743e0384180300601c60510a1050800514854800003c8402d40c41c0d89220b841c0d00100344040110b510400100b10441184103403001c0c40e00203d40c41e00e070b048416900600030b02101c1c403140340100c1c1154420380e0b20049400d5954041d11403811210030a5985140c810410316250000315201801e00f40844c024480d42050341e020781c1c90585 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 65928590 1250 65927340 65927347
    0x5010f1e05280b041424030f01020a030501080c031903080a1104080309030606090105010c030e03100c0906090503010501030b0a021303170711030106050303090d060f02030a060501020615010e1003140c0304020a0f0b 94
    0x21440e0010b0301089070039418011008240319842c8c0910080101c1651a00d011402e58540020f00d070070000e030b000145009030007103100120100808064003c0321685810150400d450300000107000305000b6440078a07003400040c011802c0c20b000005811a420304404548083d03441405109035181d00f842881d020940c400300c82c0e40004e01600c0241314904002d800c454101401d003036414144c136401c41d889804180a88001d2002035403210780d41c401b4110a9009010a500d140d0b10018000b074014100c1c0d0130542e010400080c401308011120009603002a0b604010010008a02410768080701046036103c089900802003400c06004080c201c1e003008001c0c6080c440c0100a101d51841c1c61501102d04954881e00d0008101151000d540034103c5030b080000c905041000280c60604094404511480402c441001c240e0784400a14094401661000c04800c08450f055002e40200c00701c41c40381140134000c004841c1c031500041d61145008961956015607600040c4610707400c40c0c01061080e01041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 65929840 1250 65928590 65928631
    0xa0b01090810110c070e01050a06030c0203041502150106050315031903030c120e0303010f0e0610030c0504030f06020d0c080106050a0503151c05010f1e05280b0414 72
    0xa0340000c00f42c0484480381880c0241600d040d50400c4070a0300105509010030300107002c00d082c41c98030080501000e0404116200720380c030700a03640380954403a01c40d82c070340724103a00803029200340450001301522420709007140d40c44000140035a0005c03141d0743d00e00143c4054140302072900117200391200a400342c40d041e024a15840031405040c07401460070510080144a030103a0f0240c1c4102340105401c01d000d03607241d50500b400305d060388210394004480d001d500310500000c1e907115040d200310b1000b54100011240d1003080d051f611401140c0c809042904880c04840a00049070020012503040c0c540070480d0b102e4000e01070303826041c00e004000000745c00b03014100d1258080c000542e0407900c0d94141d01d0450030b100002030b4180100c1000354090131910b0182d0010842709009055174521480810b200800d10b1314920f0000b04e000e140d05850a540743c50106507502c1000491740724122022000c04d107a83c0104420340045c06038001c0003800750b86020300c0d0a00c0d41c41c0d0396005a01602d9500c0075646503500c40e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 65931090 1250 65929840 65929873
    0x90d260a0905060103060509060708073c110114040506040312060902070615090b151308030f070507060e060906070c0e070903060b03070e2403030708030a0b010908 72
    0x1032115403095520014100800c0c800c105540c003c0d81300f041c0104180c60020403090a040d000ba0681d0184031b031f45401d02040a82103080d0140340e5400111049402c04000c8076888224281c092a910328400380403600c5a06900c0150390103100c04150091050140e42e0002113014101114068616041400480c0010f0310860000e0325280110502280d000c0d100c41c1c2c980100d1744500401c44009640303a00d9400d60200341401407000f03082911041000015030340110f0341c094070005615414580016902542c0c42c25811080060410795007200d4031010500b81d904650781c0050000d8039144212040000c0321071050007982d0544102030001814401c180082c400c0d142c01c808800c58000c1e03000384c0c0100c0c8001c00913400910654031a560210124914104a030032108400c2201d800303902b1410082c041e040c10340b54003642001400025112814280d018007e042c00d42d01111a0701d4080021901d00303009404001d54052413882404004900d1500d005441c1c0d20440c1c4504410f175044030070400d446485 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 65932340 1250 65931090 65931167
    0x70207050d06090203070b180f03100c0216030507030b0f09070b0c0a0203160504060b03010b030c090d1509110904031d0a09060e07030c08070207030f0804120506090d 73
    0x4141c02c0070410b4010340c0e0000e8184a456081510b5000c0e0100d0b000c40172000c4001b60150418055402142c0c210004020a4441c1540c071a007940c1d00c1c0c0c0f504550758006108000d5082a9102c21034140d580a0f103d180c00b907141c02c2c0e68882901c140080d1004109050782e01e40600740506881001011002d18100c0700001c20741120f103500e40b660042e509600056102440f5080c0c03a054440c01c50103020381860200b00450714941c0042c001c1141c10310061000c1d224040860b070304201c00e1400203884008480000d08100314043d001052a40d41e4140901c00011542214666030312035a400440c004100061124280040f43d0140000c4c03810450681c210140b4441501c20385405052600c0003612035803641d081d2031460340701e0722000c40c165040003009941407065107198911460050900e0034030800095641266000280c407080c0040084010409103a0840300104200100b4041d000c00500317002e03031581c8049943d1a120300810b50601c1015200c0c103200031030941c0c444141c0768600c0d441c01c00c0701d000d080d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 65933590 1250 65932340 65932343
    0xb07031b0f08070c1a04021912080c0c06070503070b010905040b060409060e01060b0421030c110105041a0c01060b0c031215030a0807030f0e090f070c02091f080303070207050d 77
    0x407840088402050800d6010300c0c0350340c494051703c016410640306104031006c80c05034960011440c400c1c2445a0816580c0190006401207101511060800c942e0360910f0300d013240d10780d40710f07900007006010030001001400981f4000e44c8041900e03a41c40c0081020340c0d1040320f00a06098820300014403601c0c003070744850041070082000140b070805420415003150300302d4010fa02901d0f00410100013003c0b40e5000c1515070a80301924941d094015500684240c40b20755000b044180ca5000c0c641188c3d10801c2590010484e501d88918413000d20080c501d000d07848941700b1075942d424050080317003908400046507003510001c8019450f042e180b03100861001c4025000940c1c1c0d080318001040310360740401070300c80c12034050021695251010300e005030002042c26a91b20074444014001d4400ba592500035640c403e800000c0c0081560f989030040311880000c030380c02544401407401780000da41000003d64100c0e4515800b90541c01e86581e181079803030004855020069000f824203100c00c1c20103011490310a0f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 65934840 1250 65933590 65933597
    0x60118110406031e0e07080105090d080105060c0307060213050316060e040e01090f03090e18030f0a02032a010e150103110118090b010f0507030c02060f0f04030b07031b0f0807 77
    0x805080104c01c041d514a10f184001c5640040403d21070150f081c418035401040e800002c0c0702000f0072000113400f41e0f42c144078407071068202107000c140e0000248100c5508992000c011941e460342d111034030301304420381e01840d4040d105099032020781e107c2314990341d0308ec2c2e405074480d4060305102404101c064920300c8860000c80d52611600400281010020200130744251641824030382400034800f0051002032040c03074100056140d182215001004540a80480c03c850300e94410001200740e107144500a00f014a03115204241c00c80a80800d4505c501d051080c030017803040d031620015581d900d10000158000c198842401000018610a03a8155908040c100305508101a0464101001c010707802910a141c40c0c000ca03055540c1c0c03002d510394184c1d04a00b4100d050015a40f001001440c5249000b8007500d00000e650300c00084000a840000140408513a0340da5100e14141e121302c6025070b21203012a0a06107402c450446c010101540308601c1d80d5280c3c88090701d10070444030700030040c1514050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 65936090 1250 65934840 65934881
    0x60206131e02030709090303050601020d0503060907050c0316020108010f1d060a0e07030b013c02031306090509010f03120f0c020604080a141f0209031c0206011811040603 75
    0x1a20113000a000600d440c50000a000c4020b09003d0140e480c01000030f811074000c6030072074003031503080005c0e25006141540d40e02401c5d0750340e03203080e9842c0c821105106800e10000c00d4500ca0443c1140c80d04814a100ba640c4210590703960700c8130003106210b8000c204000790300080b541c40d8a00a6201c0c254082e0000345000030303e43e581c42104412034001d0f540040002e0b110346031710f035240d600400c80703c1c008296007203801e8444070068012060004080000d00014a0809059000c58820000e075010360400a0a5880c000e036103640c050202202c52041c18060060200001150000340d003851044036044008840060290842102c046051035411000d02c110744400c20050b03100e0201070009000c043c07004240707086090900400201744000c00032034640c0044004040038061500c11520a41c107084056203440c000400241040d01f4608401ca1003004510400c031490303400a00941204c1e600200b18042a1007104a5020381e03c80301040002040108070800c0f0300d51003540081c40d9407441026030b410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 65937340 1250 65936090 65936093
    0x10903201009170604020f01030c0e0603070906020709020421030c0c09020403020405090a020f040c050d0c0302120a02040e010608040602271507050c01081e1906060206131e 76
    0x20820380d801d1800554115018061003c0f40c0b5481c14002c0c3c40722005090901d4190300003a455040006020304040d2140f80c0c0c0541580142c0e0240f0702694010445605c80c80d1140c00200890b131284195001031144807800580d901151007180d00742ea0703181000764410020031a89000d121003803038040b010000701c0a20a800326940898140c098044040c025030703aa4554010001070700c04c00b5200700600e4204550940041c0c0e51980e050041c140e0276500850402e440e00403e0b14140030f40840c074072080307007441e5000c1503003a8150b00425400c550300a0205007920782e90480b40880c021402183c800c5500540103111a07406503c07540c0d80b29101d03600c0503107003020504401403c250b501c44404403440506002000e01e14ac00e440c01e0b110394040850241c14a1001e444050350f40c3c500c50103041c14807226102081d054250028201c2400c5000400030b466406c140b91049201c015110703021414500d0101d020517181c0c808240c41d401442c44c1074040710030707103100c3c0c0747d4000407001c1e2811804043c401148100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 65938590 1250 65937340 65937349
    0x10b07020111030d051005180717090c04020c010c0320030403030f09121107090902030a080307110a0b0610112d0a06020d050c0301030812090c09011401030e060601090320 75
    0x41c072a90b0320b180010070491819042c000000045030415000101d85030030040d0413584100d08ac03a000d680b5141c8007005442c2c600b0b9060401d050b00c107c40d0f820500000305143d4000781501304d0600c0c0610b03a5070401000c0085040c0c030803d0b040311603034450b80500030004500442e105c2e412221101c1414000050b904990b50ba4a0300342100d100100c0700403c5100301e500240c00424043d4000400300c030301c0c040c0511405030780026101ca04940c1e004005c50404008181c01500c1500121802001341c0c040320140381c22341c1041c1c605840b08903011807003100031558a0403010300c6100842e54019140c0010100c140b9203540c003040400c2c0f1400400503011040500821f021000c01040d005103008840042c0c8e1102459542e85c20303100010b00d01c4440002c100300400004159000b19001d800c14203440c200d954032107074550740c10702d51741d10701c00c0b940501c100d4008110200307100e403044520701090324204582a006c80b03030f0075103a2508807030340390209032810320404c0420540002e121018542010b82200603c514002a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 65939840 1250 65938590 65938601
    0xe1504060b0907031506110712082109060603011a011b080301330c0b0411060a120506010806030d0f020102071401090201020f03040b040303030218042909010b07020111030d 76
    0x20b0002949503424405c600e22041450f00180209280c03d402400840d00d000e960341915100301d1801d45045c0c6a4001405942c0050b10104012254507140c0002d03540702c00d0741d14980c140c6003414240100e2001c59030720b140510074203804650310380021105041c00401501c6c2c811806640140800501c4a04400681c10320011800707004410301c07545061032520150b007a140700740d01a0038081100c01100c0c41c00742d90098940c00100e036002d061840c1315603c91078056200ca019000d210b4005001080300242140c00101220302c07507499280070013003681c0d0300c4011161910f054801c150150440241c1413401072003420a03000f0403e40340009407030130304240c3d94000c0001c51500003c0050355908545d40440da4144407141c11110380900860510f801c1414038521403013030384402820326900154094100c28014440d0480c807000030400c01090310311444000c82509010b05090340550006000b0505180801d0301d141a01c105284440c1001300c50343c0191501406d01c48040d4580c1b0060002c102400c03000e0242 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 65941090 1250 65939840 65939851
    0x906050406150b0306090109050601120204030605070e1e100c0209250503010e0a020a0e030a11010801120b040f02120715030c030b01020c130b13140a0e1504060b09 72
    0x12a840b0303180c0780020a10181c1c110500c8a82c0c20024400f155691031540d40c159140d61000180944903040103071402c01d17a8645080d0b019001007400030600c10f550748402c3c4140121344540f404040668108441c0c06a42004060340082d0010010030f41e003030019a0300301c40001810700d010410655000a803114204480000c11490030384003042c8071210740060351844014505100341103504100001051100c0101100801c5502140b200c0d0300600c00c3c00031191007403000e020303a151036005003890300080244040280c00b1418640000030750710746008048040300d82140092200385c44036610f49401e0070181c00b013a644800403c6040402c14010701c0756900070f01954552001840c8100d401600f0342e040c00340048107240c5400e0789600c03da6004994058149804c46d60042064082c58140004000094200d45c00c10b0606061100d600d000341d0014601007401d184102c01070752000c0500b02070381c0a64054101c00c0d0800303402242d01c98032442c00765420600c60303040425084002400b1464200003101c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 65942340 1250 65941090 65941103
    0x7150b0612010315090f060b010207030605151509060421060c050307020d020106060c2310020c0c03070602030a050705030c010908030a050f0c091003020f0409020a120c0c0b04020409060504 83
    0x41040100c0e110a90700d25542024017840081c41c25240d00515407054980640090f0b151101865640e00c03d000c0d10010710350029041200d810f00101c80d1420440d10700240d4011162003e4800034100014140e414601004118901d0f00c2d080107031901a5190400ca00c00d0f00120180550b40020824011001c0960716940c46645900e88204000e1501114543c25819a4509038041c0b203410307803151200030496000640c00040c80200d0010030007088003101c0d5190107024407504602c580b84e16400030114101c0100843c0d070002c0c4260304050310f990091290b82c01681c07017001503819050099019116180c01030007640c2c2010001000e03242542e051400444003a00000200300c0b40c400c5900c11503400000386546034606241803081507045204100035280318030030740400700b10700c14030170340442d40b480c1d100010894440b541c884510020790400100c0c0c80119030f4036000fa80402050f0700c1440c032072103c1d5584040c21004a5181c0c68818080500f040e60032545885141d008a541030040c1c80c0114450403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 65943590 1250 65942340 65942377
    0xe01020a0216091404020603062215090203010e1503120c060a0e0105090a08090406213003020a0509031e0d0906020604060507020a0506090109030311040b07150b06 72
    0x445001c10000758104104161500444c84800b5040c0000c0540c030990543d5405d0b900d88910001032550280e082040e00e504443c100c1c810104400b40d0010407004440710f150b0a440d41e1259aa48140c2c002405454101c00c2400000780c0c4005d100003481c51503103800f030141c8492800190703800c141130384400030003207a69000d1400d100c81001c4a20407010340011000082049052404c0707990b480d01090301c009007800c280802c4c81002c0f951140d204100401000907441c15120440c14030841100f810304054411244500422241c4d615403540c2d09100d151442d5100d03003512400740154025008010201c04120080c81030749620b840c20401a0342c0075031598080400f24481006c820715100425004c1c508000400ba81004680d40025140b0f03001a40620003140d69038032030038200e02d880701c8514090120b105442c240654510f0651000803038a020351703410300c1807600d44480214984038038400d06101d08420090358010500c0600e45803502120b8440100b0011800c80008a00d5003000d410b10704018800d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 65944840 1250 65943590 65943613
    0x30c0601060914031c0905040f050906060108041a070507060c030b030c030d02150a18120306060813030c030314090d030b04140103021309050607030c0809060402030d0f02010e01020a02 81
    0x50300600c003c00a0f6044407040140f5600030945410b000548002030329a038220304040c482c020000303000542070181c030400102c2101d040800180000340c0304100c05029000114069511030141280300e0307904142030b6240c0d003200d900f030ba01c01510020552010413105000e81000500301c0e008150b401592a44c004c50212400c004260824080c10041ca110381c0c1326034032458629030042101c22080a1440c3d4130407691396858038440182201e102c2c1d01060010804079403042050280610542600e036039010030580d515000c09840944090300c06003085040d41e1000c2002900c40c90900d13030503c2c0709140201c3c0414865a04040d01c07082a07418065036040702211404156261080c6071000804440602000c2c85010300f01c80d100406020190280b40c0c0d09803001c0c0e010b4180e0700a180010b520500f102d00900e03007420020002c117441c01d12100040e004001241d1b40f11000a0a140120340081c0a0840f406035000250391051514a00750103554807664100d441e06000e201a041c030420540151041c04d126 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 65946090 1250 65944840 65944847
    0x8190c170a09200a0315140c0304030c060b120d0806131401030f05070b03010306020403020a150e040c141314090907060509011407110405070c0503030402040b010c0203030c060106 79
    0x4001d812400e01d4148a00049048520500d40d4407804030400e10010390a800031480d22000d40c0c01c06410f400801e0100e484440300c2e0f600034040701e43c0704450a4170799100d22114180503c400d8802400203202a1030000110314264040207060314014111b040501c030040ca02c50a040c6540a0000031400c0182000010305144400c6000504128010413040794102c2a400e2100018040030348100100a40c0504006c001c104a001800540144c181c4035a034a00d4030f40e012798454001203010300d4041000080803070320000102c18000e0390743c0b04c1c00780840d520000d01c0000c0052807040350411190340007880c005141900100391031010840d40c500700c1c7c0d080690b603007441440b0000c4640039030607000801120040109081d020303501c65161095441c118400103c1d6090140c1166001c08403000458a00b0400801004105142d0540d400d00c001d40e41c080c000d82c2c8006080502610790341007040001c005141a07400350703111102c1414000450040b607000f003803441e00000d040070030b207600850060100320782 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 65947340 1250 65946090 65946137
    0x40b0903040608190e0609030904140108031209030912100b180403050705030910021b0f0a0311030102040801020f0703090b0a0909020a1101020f041d04021008190c 72
    0x1205008514007403500b0300081c58480c00520741d20b021000380058502000c0fa0740c21210f4895101422508513050031800152258032522800748540d250092100c4200c0c00d80640300d0488404801031403c02c0c034000a5030f540385c0700080c80030350340340030400141c0308503500c0e4000c01c0d000c00300d080700800701c070741a41e080c0104541a41a50340d05c81d03031001418154841a02e40c1c6654013a40c986005a29604070340752072403031801030f0b00f03078240d11800c0b81826140c0c0c00d900240c9000303951126850180301c800703c58217106100c6184218150442e0b040442403022410200030080c0b010009400149800c3d80e910040e400c80e080851442030ba450006010130626034400070b400702074020300c0981c2e0300c0e0601440019203990a03a12401003199004150100e0303484c0114461013514403020000d6564030800807900504e43d1090040069440d84014071009840410100c030b0b02c00c940c003401c01401004010b030192240400100715900054400d14605540000750168074480c810607190000350444601240230001d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 65948590 1250 65947340 65947351
    0x30c140901050a0e0106050a0e1f1e050a05071a010b09030706112d0d0807090b0309031b070b1602010e04020c10181403280c112205040b 60
    0x121559804d00411031002c0303100381112482c0c01c1c41c542d103400609040d90b9500d80319041e25400100141c00e042c1100446074000d0301c807415035544101c206012078040100e0022400240b0014505018220303d13540a00014406035024820304584d1505203032040904a02c00d07008400751010205030b946c1c56007410041c000c0500500d04000307a080101010541d65522108032050307028103051103085030108240c0e80380c2c48000c440c0c400d030381c2c59440b81d10000d00f004405036445070001d0b114980000385c00030720b801500d01519500c40903510f000355801410402811440d800b007c10b016910002070060500030040c1003c15001c40155151001400003402015a0a240d01c2c016401049040c10191000c80c04000c1d0a610440018202d0b40d0b0b07040c160b9890941e04030007840030403d44100880c0311000000740c0b0200e19540c2003c0241000403c10a80b82c01076040a000402e02150101002800c21141a8460000506401c11040041a40c40b00440c1d0100c2c44c17074101507a6800740401d11581c84030555109 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 65949840 1250 65948590 65948599
    0x2a0d110a02060a0902040b0d030807110c0a030b040c05060d0c0e0a0e040f0309080a0302060f0c0705061506091509010206010f0803040501120e03030f180703030504140109030c14090105 81
    0x14109503006511490014000d444543e0740c0c1055408564840d0b00003031140c1e102400500c807603d4603250280c00d060094030b074003001c100e0544828203e80070000c2c2000c01002d018103105101840e65440d0b074a0200c01070000c81c0c1a0060f4980800c85885410144c00d0300080003030080740d201d55020000d810400c0400c0c0b0302d406030984482c03d11800307642c450714940180d0300c2400ba440c400303c0343c1400c460032006500103401602410f000e01d000e2550004601c1e005400038081482c0070788507442896500d1281d23400c01405504500700048003c0d0b006501c4605540014049510744961a80001d004108400b050200300c0f40200705541d440d64104901809403101142c4200720504040f12159240118401c450400245c00c42084010b2600d8204051800c000022207450f82040300e000c020303c8104031254448200d0400814903400000034448007202e0f0140c41c0d643c50507003030840e0340c42c00e181085031a5061041c0c0e80c0e030000000d5400d41c7c0c00401050450a60000001100c08021840a040e071041d41308 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 65951090 1250 65949840 65949847
    0x400c0f0605030105010e0f03120d0e0f0303010602061906120602030f070810090c0306092a0201020a091202030c09040606090b040b18060d050106030b0403080702011808032a0d11 78
    0x903604001c07001102c41048400c21491400c00c00003a260908004027112018000b056101c60800507802c40d2a80c20801da051752522841400c21070f0347c0340001d2088000607440000072410342212802c800c03010000c01c48002c039600ea16461400d94036000c034001186d5070355001040102250201d0940c82c1c1042003850141000d003400c1218111258650183c0315440c1e81e0785800350501806079106600030110140180a1850100c0c1e4942c0c00e640e100484802d0f41a40e1003900000f0380c030601c01c5808203036407601c07420901e606100041c00d880d501424103e03018801d40c42c04846507070f1015100c501c0746108010200b501e600780040325041d0b900e209400b81c0100d00780660518035545682c2e000041304091b2801c00d42c1c45d515400003440080d14a81c1c060019480e00d50040140902c200702284124081e849900854551034001c908886606109900c0c030788040949600058a4038011a0040106400c0740000c01004080305081e03c0c00c1d07140481c07440000039000c40c070750140d80508800400400b1000b0704 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 65952340 1250 65951090 65951099
    0x601020c0a030602180316030204050105060a050d0902010311030a05010609060504030201200a020d050a020f06030105060304021e030304090905070f06050f070602040b040b03060103050c03400c0f06050301 90
    0x3107848190000510051300400c1c1d40384007010000c1310400c504402000c40b4170580440000c100741210a010580c01941480d0003c6028100f58044460b420f4284c0d5810b8134081803480000010516040102c5c1019240e0004e1101801d90002850140c003481c400010103501d800f80c0a480342ea456440442800018401000981c0c0c200c145a100c1e04402a00750110301c100c20602801d01c526020001e40c00005c00085109001e070010b08491004c0c03090750005401c404590030410030740024460541d006004000080060400c2c98034042002ca000c0700240d4002c6403030000a007150800d800030120b19541d801ca090a00c14200440340044c201c1c0913040c642c0702c1c1050401003407440f800d4000c2d00f640c04000342c44000c200595044800528140740c603580c42c2e9031100b5034040b5a40c415181180000e042c0400b00380007000e1101224020040f84030079807017010300846401d102d0002540e110350118101c0c0d081000e506030300d140b441c8030300b8031074515000b07018240140030308000d00700d41103001041000c1c4010b01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 65953590 1250 65952340 65952349
    0x60501050703080411060705070e061e010c05010f06080f060c0702091f1203031409011e090f02030a081218070b090d0606060237140709050903070b0601020c 69
    0x101c165402d031901090a5440b030505200c8106a035811582019000410600f80700c030100d161800d8544176039105034241c0350030341000300c1106030700303410101c4c2d4a44c6818441958080e000131684144520f00100340704c0d203000c4440c802c640e02603004040d2034006040719030384c040040c00030316400401c2d5001c0d24107080458010139440c1d400104806401c1010001d50070803513484061b00e03401041102c424008a01d00c501d4000c000c1c15503000b6402c15144072802040c0c0c4403106000300c0c46d0f200c0c1c01080814102c1d84600e0401b021b000600d00a0768480e0701c0120490150302d061085001807401010203590360252034410138207900b40100391050080020400c4074500b0b1002c90307445c2c01c07a80c1c560301070381d00c1e402c507800096100d0740d100400801c2c00345490303070004079180c0119081008110301c58420004680c3c00c6503028035804900b0080301d950341c0d0300b01c001740041c001042c03030844095410103c07031109456040b20b40481d1030596010406500104404040140041c4420b40c080d400384064000e040440c004203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 65954840 1250 65953590 65953597
    0x110610050310050c03060603070203040e0406090c05010c03081b0403022e0504080307030c1e06050106020705041a090901060b071a1608040b06030c0d0308061002010b13090201020106030209150306090106050105 92
    0x10b87c400c4000001242c0124820800e4034054403042080406504082c54102d0041240c04403c40701c803180b6040018656014400f03142e5000d4164583c01c4a0b40d540401e480702400480100c09a03d0708140000320141c4c40310749200d504003040c00981d010074101030690701030030b42c051080101081000c01052003802004030640700d01503810b04141058032603525003d0740c0c4607548142c540c109803505907480e003803144681000f4101c9540740c0941d4622030310b540501090340c0c004200740f80c1907030508015000c01e09000959aa00244540001605035212200003500b584a510705a445035200c8003030124024450080d6508408041071030104c42c0d900a1028103100f80c000d01c0600716045c2d850002d0543c8d201886407501e0320714000c0c4500001d01551030302601d004000c2d110180204c8441d40a04241c034014420441c4487c0c00400e40402400d5409001020b03084c8048203d0440d5200c0d070740000180c0740d144000d40101c0340c070400c180c202c802400500d45456070041074484c25a042034010000760340c001c0c003103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 65956090 1250 65954840 65954851
    0x12050406060f090e1209360a0504020a05120d0c08070f08030109050718030803060a0b030702010e0118050a020d05010603060204060c060e0105070819020906070b040c060207180507110610050310050c03 88
    0xf4824410040a80400e20340d00d0180c074010303287c1b8024100003000c0e1440d40141d05c174034401c41e40148039a4442e024000c0b05664031180890071f41c0510b00d01e0f881d150040310744850f820b11810030203180034500e13034400c0c0d0b9080900b502102c4030140400184002e541f6805510350016075840e044a007001d1000134920341100d5403001034a12100000800c0340d60f1100c40311318000d40365682a007992030506c010000e0080c1161402010700b946012650b1031040c41810301c0113815604030004001700d8980c5d8003005200400140100e5042d940c0d1f441c0000020703414000307803000380804e4581195402a40c1000d00c280c80611900d0803607645008200103407035400191998105c01c0042c3c00102804185502c00d0092154054a40c0d0102010450300c0c1041921403400307200b03902c5084d5041c161659010b0981e40c0c1d000b58043d12220741e440743c501405170a4958403503070b4862082d02c0c0017014540110042c60802c0415124000d618039032602c1030201d0b0408100010992039034000c20050313450141100c5031a400301504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 65957340 1250 65956090 65956129
    0x71e0302180f010303320406030c05160227040b01150c030909020d02120108030306040b0303070c0603020f04030210020f0f070f03060207211112040612050406060f090e1209 76
    0x407104989185840c071b80c00c2c3d684000c0d800c5004917020b1500140d542c1082c815000000c0c2444a408011486101600c96103c405a8080c02c0350340c10350f00b040445210030201c3c0546002000e154031a56244180c1c1ca402240600c0b120095541001881640070b400803004505100031842820002a0300026090483e540c920005850b0001c0805c410040c0c414181e969908119071800402c903820080006c41c0541c90450b0100101e40b1040d080c15241d004007103024105500d030503400c225a038040d800506203003030445240ca00d002d40b00d60010704d010b0070100035840141c0c8107000310348103a02c04104030019400c4040080104c1890704880d40b00912190000611040e00490b1360410802001408105030080700d041c50700b840c1e0714000062145aa404480540b4420311441c8059680688126821b8a1859032049101045803011001510010f03004580310b99844000040340c548441c1d84102400c22030a01244500e2210101751504291f03000300d8070025010400812141c0d102a07140c008001c9241c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 65958590 1250 65957340 65957357
    0x7140306010f030e030409060e010f05010912080d110c0102030a0c110d180905011e09020a090918060e010b010801080c0d031808010203011202090702070620071e0302180f010303 78
    0x40f84135086000d19400708000c0344c1007400106d80c828560100c6410307070b6007207184200e200350346000440e030b820054400c4031000c80d030007400c410224000030300503c904c1c00981404101c0e002c2840d45080c1b254800e10190859940c04001e111500308140124107054180381303480510075800c0355150b03496600c0288224180110003021098281c07104074010300418070054100240d69560307880d40c0c600074030042101143c0c018813201103410302d00703482a034101220035039030408128203003083c00004204250500006440100ca11000140c89006a980262410001103800b20312100050484401a04040e040380c2082c5900000ca4407038600040115406141101d171071007808140a098659a4000c60129400007002051001400e10390111052080d6100e25107551061000c030388600c11405810000340d03c65010f42c001c0c0460000c01380c03011058105544032560b0315040c40044201c640059290b100419400304150314011181c00c4003484500108600c03843c1060420300981c205000040c207101e03414 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 65959840 1250 65958590 65958611
    0x408090d05010b09010608040308011a0a08070201020c0d0201230115031503170424020c060904060803040f05100804030c081303080705010f0b0307030309030206090d020d080307140306010f03 84
    0x750051448000b016020313101650b12050004c005080448003034010816405c0001213401000e1010038209510002c00d500b480102c4000715150000901032404541d02880268070008003403110700c10030080754000081180c0c0b0003050403c1e03040102c00780b400c0c110b00100100000060f10400800c07841040c5000261607103201140b850042d03007a08082d001e040d598030815203804028000f00240c6010b07140c0700c0f0403a110b406ca15031036000e982e0000c100580041c1d4a411250401d80040c06540e80024000303d03029807262420b40c5540c010754048400d04421040c10000ca05010b0590728440981d46442c6c8000d2400e5140030b0641d40c0d980c140284068000600040f0000300c650107030002d15484050079035980308608103280031300712000603001136502c0c250026420b8900020218205d03a81502c8030281c036450b5408000c4c0a8000c80e65460704641c120020034010707a5004403018480384108001d0341c60341000c0c18010003000c40050200100d100c10000d005c0180c0c1c00003da031a1503e8685004102081c10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 65961090 1250 65959840 65959843
    0x1516060c030905100b1f020a02010804081e030612010c0203040605031e0703020307091e1215020406090303020f030702010801170109061b02061e240a060302120f0408090d05 76
    0xb0380400f0b0498015904401c92140031a040711400c8034040300c415049400e128408038810f140c0d481c500d805a441400c0040055014115003544640a110391030306100441c028404500704001d100c290451001007080b8040c43e2191100c070590f0720741d4008200442070400040e68034407981c0280b000348240840080d003200c0d5860082036030345111010104060900820140283d04103803440c0001c189014030100c0c0311100741e100c00e0b03420210345400451252901e200d01ca50031000c20307015140110551200101d042ca2800104010111561380c0d0a0140c5182002418554201c1c884000f0780c00801c0134a0140c0e07401448507040d00c1d844c51030300c07500b03a1160b001b5a0040821b1000101040e0803c880200c240c4400c00508041ca010703074007641c846548064540700b1115810150150400c40180803c246040c0045002d4104201002806031040ba0f81e0004040d42c800d41c2c09080026000160444c0c09141d0041c2e168200c40020030350499810942d9409007180644074409004005c00c0450b4021302c20b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 65962340 1250 65961090 65961101
    0x91a0717130f030c031b03050409180c08031c0e0a1103160f1a041203050901090b0f0a09060507021311070206070507030209011a03040f02010e0910051516060c03 71
    0x60041200d400030b0043e01d03024041c3d14079008140c2c0420f200076200301c464a0011190360500d81c4c0341e03955919142c1040700c02401024802c0c1003210140511030074400040c1900000c0c005081c81c0402503413104100424500704418018602580d2800c103881040000700c0007807070520040c3e0020600d41d01a5a590100f072404400075070340003005280c05030005204e9000c1d100300701699131140002002c042d040303002d0252807140b480b881c0340c080444801c480201c1e2040011b04a40030303052620404039555018031b01044c0d0040c081c903c01030f290000350b0056480d0408180001050700c0e0038900c0c00d02509400107180c408400030001c0d01c00d41c86081d005a0302030b1030800c4500c0b80ba40140080e85401c058100566030b580d060204034000e02d0302c5000885c2c00c00340850448210703070192282a00d10b80d02c56131900355481c202c002c200c0c14001e580b45000681e039242403409205620300c100301c81425180c0403c00c405071402c60245659414200051060041c5209400ca41b0741d1b04003501140701d0b003054004800401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 65963590 1250 65962340 65962343
    0xc0a05120a060501021009030e240d0f0b0406030506070f140706090c050a050d170405060a030504020414092a0a080303070201270b0601030905030d091a071713 70
    0x310000420064400c0c0b507000d88242e85003a07007107640e844260988142214410f51020b00810308400103520340340390008941400c0c0c0d0311101c103003078450803008800001d6000705900d10a070715164402203d80d44a144668030901200300e03424000b20740f071500ca0a4403500050b1a9500b001445000000800c0c01040e0004205a8109130384d40d481e01603003402d0b00188034043c3c0440e1102c003942800036540c0b4041c08443c00740c400c010095550300400ba6140100c51845050b902c6002800f8030000607641c0d00c1502a10b0400740c030381c42c003040703500d010300c10031045815080030040350112017010b21541e03c6000484408000821182d00240d80318891400b454a090f140c0311036010740324000204003440080b015501a540c0c94000740b22105000c42504882c00c1d00e1860b0403146a640341c1c2d484045105018108d0f000385040c1030020354048603864890a6a0062110f0706440781c44020f000108900c0c0f03038a46942c0030110b00c49083d503040c480030003070903284d014003410308100c1c1c1440401c4142d0706210040c58504d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 65964840 1250 65963590 65963617
    0x30815130b1206100609090c08071b0b0106080405010e0109150e0a0203101b02010209030d0804060f0f0e0705120606090601050c01060608190212040303051803040801020408010e07030b0c0a05 84
    0x5180c0042c80800005081c000c20340046c002c00303c00140e180d04c42c02005101e0703200e615882425602c1200481e80c40085042e00070040900081180200e80c1c20000c2502804190352981043e01c2c250a00909450300d0128201c06a03160144000100e805809601300c40500c062010840660220010746051450b5038003a501d8003807500d09a2207070701540d12850800d183e00d15142228049618241c1c01c038002c1c0510650990040071006098602c900e50296210303104150005420710b02488401c11181d03403190310448203030b45d4a9a4511494200310f541b008000880710b04010303040c50000280c0b51400a0190b90145003280301154150f03004c0d10965200081800080219503511030b801004800140c901004a03803000c00c644000303c5660088441010351a0b05082245c2c585030360460041100400205402c0d020000014035100b0508c0100002c00001c8009601c607800c3c581d00d03d0844400000e241c4c0240d008103401c00014403090440b590245891001c01c2e1110400401521284221000526032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 65966090 1250 65964840 65964853
    0x12030301080d1806050d1d100605040e010c121d0d05040509060f0102031209030f040b040905010b03010f0902070303020904020a020a05060603060705090409020609040e0307030815130b12 82
    0x7619000441203000e42283d941d81004482e1150120741c1c81003180208000603500b00300001110309143c00c440c059290100707808440440079800e8a090048400d035003d0002d0325090104911b28040c010303025507141c180c000b000841900030006c1d100800d004203052096031100890440c0c000c1010200c2c45800910003a80d52010500800030b18903030150056600c51102c1c1004110642042d8046520130354040c0c009618094030320f010050b500d03100a006589a2104000c04140344000c9000340008101c00c10620b0380700d604280b02035064620582010501c07410500c0100030540200b540101201d20204005a56181a003400c501a10415152a030050f0000a85c030070120350029501140b540198283c41072a142d18040584400c07080c2c1e00c0b107001440c14040c0c8401840c080d40101301d041c0c40104442c1c90b01c0326000105003582d1581003030641c0c0750000301d00c000a02d40c002440c03542c010f50080000c01d51155083c0060042510501070305082991100e404129407a17448100070415040da049818 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 65967340 1250 65966090 65966099
    0xc0a0303080901150b0a0813120c051e070e1005061611030a020f01140c01050c0301080f0d050304080a05090a0f05040f050f010302090402030709020a020d0f0e01080408030612030301 80
    0x350000d50b0070410661800e41100c1003000300d060f110055039a10481d0919004941e03070105c3d44034001620700a000032004585800040840c030f038801ea10601134440c07240107015410700e14100b503c0302000d10300141d04202e040c0c1c400d48020445c401039481c50a080d00c400d4540007800d4500203140d4000039000748001600b00544040c012440c000284501d100c4018080088141500ca00c080c80e030080d0003c500340018085980281d0303041b040f14001000541c01c01055100c0c6a0039035205a80000710740400000500c8106414440c0c1c070030070552800101500303480d0840040451200802c081c100c800041848990705205008868074032400074600000103031503205510707940701244203d611481c0781001000f8070f803129014507813041c2c02888154034507032310b50b800348a01c0c40d1000780120b900d07004901c0040740900c80c0788050101c2c11902e5008114401d086a03020713003e080030002c1c46042c0141048241d103141c1c1e010300301907801603201c40441c0c0c581d01c442c03000c6100783c034041e03001c001180008400800d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 65968590 1250 65967340 65967347
    0x150406020d05070c020f060a2106060206010501090b030708060a03151e0b0d060b010c020604230406180f0204050315150d1509020f12060702060123010e030c0a0303 72
    0x1026210240100280e0310b8000f029110103801060080d0403070070166200c02d00d842c2040282201d02d00c5401d0105a05a10040b00c0041c0c0030900180c000496503158240301f459810454130340900000c1c20009200f90911140c51003e01000746508100880381000032450344405008000440d1301104503400f11641c00b5110b00079140707446151804440c480790190307192101d80901d0500d46409456100d170611544c942c03c0142041d1035100e810301540c2041080140c4580b0018001000300694020303007200da031000300d0820070b2102480e51240d403e10b0309c1807100d170140740700c02d20f2800040500010390841d0b1508030000307800350354005945030143d4011500304007410ba00040c07281082c00b10601c10007030341000b0005010030f00c64011700f00c03100c0307c1c1c401300007800719902540d4400d00041c501c421088080d00003078440591300c140b01100f0341000d800d04c02031603010007829000d0314004400031402083c041e10415007100200390300741001600d4410030390b540c40501450419000c06000004003c0d01c904019 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 65969840 1250 65968590 65968597
    0x301091703090f0d09030f02040b0901030b07030e0109020108010e1b19020106050303070305091e030712030806010806030d0f05070512130e010b04030201050f0c0f010c030b0a0305060f0915040602 86
    0x10100c2c0d00400b0f00000207008042000c000120240d1a615281401d42d2100303589510810001c030780060340c0d885010070a9a031004942d0080d8401d0307807824814640b440008040e91094843c0b60300507030411000000503a0049502410340e04415604583e07542c80d80c0c0110f55200d51440e402c804040c2c0003820030114500200200c1c001141a00244079465540c002c2c95901d2150f8140034001a10500c8500d540b40fa12122060046400307a440051380c603d01000079013848000d41c4015502c443d8402c1c0c00b010160000e0300a0b5002e0003d081101003860310801190303e4a10b02c40744ca204002c000280001d03068092030a13200f4040d0000211034011849004440c0e40d54000c4d404604080300f04203000405089004003241a01c4401045504140c43c3d0350054685401c41ca442c405801c005110a03030030090100009211049440700201705001c0d00c504c0501184e1003004c1c558083e144503101400441d0001503515001003502e0482d008a030b8911414900348403503038600249519619050005005032070300603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 65971090 1250 65969840 65969851
    0x3111c0507170316080a09030501020c0a03030b090906010302010503190509010c1b05030a1202040312030c110312041101200c13050108060610091a120106030207150207020301091703 80
    0x60b1a6030007090300c035282c0e01c0c0101c101050111056020840000d4426009002e292100d410b0142c0c2682d1079940300d500f660032994444031a9800001403800381035141c003c3c40d004503420b48507003090742171120340162945014000079050043c0000494071078000c0d800b003d04410840d80d0200500e0030900c0549020703000d02d81c3c0c0040000c50010013009044083c920810703049511000441c940281c4800c280d4118000030040410a0b40c00e11001010442e81040364080030290741d00018000000761000d030036550800c0c0c6080031640140b0000c0084502100e0050b003180d00005036407661110b81c2d004031643c1414006c50840821581c040c2c40c4800c80000384002061001c540c03426550040000f05800c03242c0c248a80c02e980d9205501003200d9041c1030790461031051080c948a04c031691903191030426035002400452000400213100003416501c0700181e80506000c2c0703425440c1000c9601ca18049074124014540550b41c00901c082c1155800d501138070010350b00190564001c0001e11000480d5002102c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 65972340 1250 65971090 65971109
    0x3050d0e0312090303060a0e040c050402070809030f030c0304060c080d060b070b070305100b1b0d090501112e150e0a0b0d021c11091003020102070b0304030903111c0507 74
    0x443d6524030701005403486028007800ca04025450110840765982020b001070710350045c809004245500d0f18002809040d018201c003690b01d041c110305040c54503ccc2e040c02652560801d0100500c2d03200040200c6003250104c1c4ad219006a8550900224a116003034549000d54580480060905005e50140195a01451444005a40340c000a6095620458000188600a00050180e2188034000d80020550036106c02040040c684c1c01a02e00000c0343e00e10008224400410019036900000d004103085480024065210740840d805003000c03501030105226112103052400300c0c0d242a401084015403e6100380c02003a0b44581a02c551403041d200407120b1403c2c03150b481414148105464000ea602400040381301c40310504034607400302d881000b15894510403601c580540d03600803540e4001c04000f8038921202c0d16520002e80f918200303505c1204071803014001c02c4046038101d40100e0460b5000150300326681800f00c005514075101010080107070f00038110344c1050100000700c000c1680c00602 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 65973590 1250 65972340 65972377
    0x6090b0a060c02060304120c0b090601050a1205030405010c14030a0302070311010b0904170c1f230a0f020c011409010b0a030209160e0a0b070b010504050c0d0903050d0e03 75
    0x10812100c202d550240603420000800200300000c001c1d0b0710300502a03c103842c01484891295685c41400b03402601c00c011075034000001489a86829902c20008100410a1200b01481e561720182c5034000e510419051000c0e148001041c003450404071104022050250703a03032a450400050001d4001c0139050700003ca4030309100904546c14425000c203084001d01c40d0407255140c1d0340b6841a005103089460b6001c2d03007030188818040e0200a00d840343c20b10b1420380207070043c4411544048940d09400b95105001d2841203c1801c40039040340750304451003140100d000b005d0040240064030407818608015072a1040c1001d40045041c80c0394000c16000d030091000000601c108001c1d0186400043d5020b104d440100d4000c0411002050b504041402c1030b001802c0400006549900503901c10904240001642c5040029040c482c1303000d040c04950400860905400302d000074014041d0182d4410340d41c509c248107160040c2c003501c0c200308103c0010300000100d116281d4481c0c2105041000c8180c412 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 65974840 1250 65973590 65973599
    0x1005090115030b1b0903121e030105091605041a030709050405070203160f02030105040821041203050a14090304061805060f0a0903080f09120607080a020a0207050406090b0a 76
    0x4201c000032030340c0010010b0015250084c0407280706a00c40314880c01030400b04030000c02c507103040c80782c0301c0382d038120000301501d49124810044060001c90741c3d0f481060b42c00c10050006503100c4204581048405981074080c2c88007000545261099400052040068807143e4000006d203000941c4544465504c3d03103611035468082c4002e07203a040e51018090b80040c041181d20200c45034a02d28810300448050003001000e40100342101e1054400369138000e80002c9580342c42c005074503000418001418001e45030300e09174441c451542480321500040544810208036400c1031500103815050b46e00b815a2210304000441d99030b6030b4030602c20000414815800b40f400740c8910344800c0101c50014284030314100010524035282e0740b0207005603090090341f103000320106110b4406407039010203a44085545924807030410180c121a01541c0d11503030321a0041180995210882c0d0781c0011803583d000d40c642d01003010990038031030b1a401c9681c00c60300e0300b0f40010341c40c2c286400448140a0645807141a030361036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 65976090 1250 65974840 65974871
    0x501240c0309090b18100f0b030408040501120209090c03011508010803070f03020a0507060513050f030d1b0209090a0303060605070f031202040302042405040213030212070810050901 80
    0x160006800304810700410030006443d50040500b00c0c2c0e0007880046185120040702e03412038000d841e2220400000384081c007034040018840030103040c3c020815030540c94195206034442c07250b0300400b810000010900070360030038190150303060304100810803e0a0301d0300000000d203942092180502d070007450840f40160f540140f4119040e2041d50700950728254081e1650030b25103c51800031803c600c0340c22080701c02324506020442c00707040300c0d41d40d10b9a030307507501c03000b5060030b00c055084a0b1050300105d03490104d59900240d80b030340c041c441d81001000411301c181e0114031052201c1e0040c1d0804649010815410b030042000e0f00d506101b610108500c54450204035414080c240c3c009100c0c4d80441c3c107500101e4098004442c07491659a000b5180a1301da501140903510b0b060303c2200c600300303030720410380700c1c0403541c0d11030380240c41c0a0314218280303008070000034a80c800c548130290150049540d000061b5109200c10713801b8020702c43c11aa6804040840b00000703007021030b15140341e9480c000002c01490314 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 65977340 1250 65976090 65976107
    0x708060d020d020f03070e0106030501051003020306010f080a110424030902010504180605120f01050702030a09090f0207020904050f010c080601120c0306030c0b070302070f050d0b09010f050124 85
    0x802420102c2c00d41056424010f880201001107507040c40b80769000543c0408201a55000c1d10956402043c154906002c2c071407102a150015000e050050017044440d0b640b10451f0500f020301c504d880300040c0c6503018000028050f402514100200025001c5810540d003244003031300b6651800851a600c0300341401b1012032b05240b50003070000b2010403040013004840040d119100e40c0e0140000b54041e80c2e42c00050380c081923071040160a801404205105c5da40030300c00c82e0703401002400a0351070491a00b034000d281403c1d90051408041c4c2e00c062244a00c0c000e0760550341d00a0713010342034400703508003402c11036900c003100700c20411150f08100075070244910414041c0d024140613110500c0010b074050010001d845030103210f03402c01d581d07200b00002283c42e08600742d0080103142c19450b950881424001d0400d00103401051202800c1d10b010011500c1c0d030380d501c0502e607410403100726003a22070b504150f000d41400d00050741040d040100100300a00e142c91081940740354050201080e410f030b000244c0b034402c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 65978590 1250 65977340 65977343
    0x9080316020907030e01050106120e070f0605160203030a05041e0506120403020a0c0b130e1003080306210106051c0209061905150318030403080d1104030f03080708060d 74
    0x20a0080e400c001414005101e40d040021401d01148026800c2c04007800c5034000d900540019a04103184015950300388901880703540d0840c0130b0708200c2e04100861494200f1032060b401007010000d01144205a040010306d10542d004081c1c035510368196070020441c1d049400340c4081c0c140c480040c80d4201100c03103001c1003140e1025108a007041003d42e000c9003440001071003582075001c2c1c90305510006102400c14005450030101040d02c1e400d040c540f420074100c043d00f00700d1681c010b07a0103204c6030b0003040020104032a400410a503803030b5a45404914511022000741c2e0070409814498490004190481410f55800791a4140c010504401090300146101400ba40000400c0040345950414000004458440034458441159980045072041400c442450031403c001700c107110702c0b1448002d11741d540b190f000300198201811a01c922035a40b2401c02041002030fa18102c04440402080580d001150460b8140044000350708001d803081400b01d0704140064a04000209036190482031015a01d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 65979840 1250 65978590 65978617
    0x5012406080f04030311040803031303091202090c0d02040f0906030b0708040807020d0c12050102030f07090b0f030907090906021309110409110c030301150f02120a05130308031006090803 82
    0x646030f549054000b003800d045030842c40f0384100004100c00d80d042004501810b1808c2031503003a1151410014011866600142d1000ea041503010015035111017015030009011000c00340c3e104d68446807a8020f00c0340390b000c1854255040000142d03548264490011240030340b00030a11a07446540c1260803000840300208441e1080c4241d03805428151000e06040d44234460a020541e200d0080c4005030f40d030007504036090303900001001074200b481d503001c5030042c40360b0401e40031943c2030408a043c80d0094110482640d0700100005111040400c03400008104844c4100040505420000080d500503096282d00d9440610001440800d81c8a04a00000c40400076410903050049010140000085500b203c41c420302c030030051a0700038001540201700ca440c2c503006402c4000b102810303100e07000b00140103540040c4041035040516500711000c1c44620324029690300407080a941203100c454102810b07100d03001c03003004018014803889006880d142d0b107a10341c80710741d20030803035549100d9640046001c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 65981090 1250 65979840 65979871
    0x19080109060602030a0c030e0d1502040f0e0402060304080a020c060403080408010c090506091002010902090c0c0d030c0806010f120608061005030c060403081c0c051b010506010e09090a0501240608 86
    0xc284220204035204234010000c0b01d078a034458440092110707804140b40361081d400038080200740e81d041034203001029403210300081072905400081c07890200410140400d10300060380204030b0310902c4941c01c0000010700a03078949880b0308040c0e00c1c80d0442d000e501e14640c41d218040c0758041c0141c10000450308001c148138035000516003403045044d02043e03e50f003036640764411040160340b042d541c00d100300442034009807158a440c10407454001c407189071300180b51a0940300c8008a41c40358410741e100c042800c2c44000300c0c61500040750070140107100501103030b02c0c1000204002c2d0380494864003540c0d00c11050107000e5104c03000c00d616030b614100003c2d80010b0800081000902640141c09a1501140910000d400149618080d0b80305407409500042000400040709910050803c0740c855450b0002c01c00751800d000080c08602c2d0614169101d000a800000c0720720b0030411030916a503501100038000441c185000491805100780b441462605603580030914901c02c82ca40303803003100c440051160 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 65982340 1250 65981090 65981093
    0x50f0c040b0414060427080a0905061c0c05220306150501021b031f0507090e010e04110f030a03080f01050306040c090213090615080c0f04031719080109060602030a0c 73
    0x2c0840380c2d8402c6007280003170b24891603c0c1d1002d01c0c8001d06802000841e88d6901d503c980100502c0082d00b1991042c4414024140640c80b5868042240791403058006540b41d6141016501401043e1214150f074101803040002a403170300d0391030012a03120750b500740080e42540c9000b0100120501909006a001e1144415884042c84044461240c05825039951026007002c034a100d50b981001d160640351a0814010000d03400f661400081043c0c0c00c4241342c03941019010540c9440103072016140c2100411000280d44d213500e140d0444c203c00a00301c8801c40c0080c034000e8141e80045031910903d100c040e00028042c02d0208000d480380b13510284a45102d81403114200c029000044d00c4400341f01e42160121303140c080e9110304000780400e40e05801e10020044401800350310002d00030441c40606100540c10320040c0c7c07080d1410350354410b003207012207480342400e504a402030034120320300001400d103504e88985c0c20000781c0b81a101d41000901c2003d0b201c0303d00ba6501d01c10000d1400c000740d08181c6080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 65983590 1250 65982340 65982349
    0xe0f010201020f09091003140303010303080a0b01140a2001060603050a090506040f0503070602040e0121020f150903060f09060a0509070303050307020f01050702071403120a030e0a050f0c040b041406 87
    0x986c003000c0e00c12401c8000c3e880b40c41c3e91100c0000a0307000f41e034992000005005040e0000042d55001c2415030f0107124641440000911020140040ca05004404104920781c02d0180821415120515103881100e11118902c1e9000c0c0010b807003004c000c0f038503120102c3c400e41d0a50080c034030081e4010004000d5511560364141b4942101d4400740c6040c0401c1c801c0b84c00140e041e0000b8002040d248a03014580d5041c4100c410f4140c2508050300316045009800c01d0068607510001c0485100890b08103400000d6049a01518464140d1096043c02900100030210510f1814180261b0743c541c01c03503076603981e00e407000c4080342e0040c2c41494a0380c0c0885c0003000040e00c44d41c000c1d54061440d1042d00d040f14000a1800c0c251003068590b500980c1050301c06000f40d1a5400c0c502441c80c004400800203e46405442c1582d0f00c100c02e1507404054840303140c141c0c2c4403410040000015880b904591005411511054881c01400102803180b801c090310207100346440d000d440c460003181e0000785030350340381c000400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 65984840 1250 65983590 65983609
    0x110f0c100201060b09060906070803040b0103060506010203070507170304180e06060118030f0f08070501050105030c0420160c0b120a0c08060d0204150311040c02280804030b04030e0f010201020f09 86
    0xca88c0030300104030801c0020b00c907102841c0120301c1042150100c1d419450180107603000203000c541194418041a004148001000001c0700e040480c840030f5480000d01d054294802c541010f00034182502d5003148489890340000401c80040054541503142c005c011202da4203101180364250720120018008552540001840d0300d104010110341d442c0706a846509617000104160756507507450f00100b044d81270034000a488030740c0c2140c1c01c210102d1703026851944c8441620208010b80c82c041031401c007007443e1071004401160001c40c0389100300d68517001060f04d41c6c4132407900b52404550b240410401081409200f038040890f40720640150340b280140044809550010b0340c0c005d80328a4203100b07240c1d005083d0b00c0030354000e440781040c00c084c01d81440203407180088880c0c110351000d13103140074062a0100b600c1254510724140d00c61020076041410060043e40c00c0a003422940c034091104068100403a072040300c1e411b4482c04510418140107908078041d15241401c01681004136003614507190b100c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 65986090 1250 65984840 65984857
    0x907060503061c050f07090203070912020604030206040e09100b010e09040314190810031a090a05030a090302270106030b0301060b0705010b032a04020307110f0c100201060b0906 78
    0x4907211a00c3e10809042c6000a800261140d4200100e440c00401c4240501005000818802c0d4a507003407040c4000d0000d0302510a84205101c0d0106010440d03443d042241c0055400520686c0c0701e41d120402c041000e4810380780c244207440385c4940d0000c07016170f9005508100710161a210400c3d120b1005201800000400c00c40c104803119201098a802d1400540b1a55880c0101c10081402542000d8002c00001c3c008070300750304040c1d004100043c00c0c0ca41c072b000307501b002c2d151465080c0c4031000c40c5850700e08c070000c00030035a000100d0303c2c483d0141e22010761800c40f8000c071140c2510140e922503180090078a5183c2c00c0c90307000c404006010150181d00007a140100c081c00000f00316984144103081030700b14100880e91a519020020709910382004451407100c518000c43e0070b040041071490001c0441942443d028a40110020340303c203024002c0a05502805000d4072080105800031035241d0b484030a034140310340841002c081d420351051003403c0641d4204200c991905d212032040141c41c0d00200c24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 65987340 1250 65986090 65986099
    0x312050c070c09020309071a03060d050307060501081b091e06010c060501180509030c030403030309020a0306051e0c13090b0a0810020304050c041b0c03031107051b0405090706050306 80
    0x8250001842007030541c0041043c3d80c40103803070341010142d1a0410407194481584442d250740000c01d03071a0003c044035080b4604030781321540c112262070a41d085000c3c0c8880500194034180000504084c02304201c0b00d61241844c0c2400c61a000200b00291132900b55059100301c0b10410541d841c000c207a4261680205050500c1c01e140e600a035030700d50580e0800d03080031500e4a8912a00540e640b020300404d0741119801020718104400c040010703544e23001d03910000d0109a102d00c210b000b0b646495941c03101a54024005101d5803400c2402964a225510140144084a03000080b540c660001c2600e0000c0c610706122003445103003000050141841c00001d50b4024034050000884480400000380400305105002d43c03039180c682046800c0040c00e0514038025030810741d00003001c03c4407000e0b02d802c000403820030b07003100d407070500f0300302c008201440600008200000d40b081c03d010b00041c0d40390070404114040b40302c4180c1c00c02804103940d020b9504d1036069100b503809020b01401040656400b080152 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 65988590 1250 65987340 65987347
    0x2012a0c02030c22050c0703051c06030605090102030601020f010606090e09010f0e0a03020712080403060917030c070209060a0b030c0309030c0a0c08010c0905060f1c0e0313080a0312050c 82
    0x900c1440f51211102c49131500454840d4424580d0042c00d5100c05107070b90b003d05240c030a0b00c01400920445c1d001650b0b000c011740e1102500c0d03002c2d900003805903800c80010041d41c40c02148040c001e502c240c840d64007600c10507809910301c10050180c0c07400d4908581d503210141d4071308098183c003400d018240c80865520f80000c0d0143d0f2003070b44a0001e282d043c08005010210050801a040070901d40203208201001030105d07020503107280844040760341c0310800041d41486130070328204c984192a100d44004070000240a50360320070700003a240e0b4a008480c510442e8032201c04100d0021550303c64100d0081e000c1c000200050404405561700030100003d503458507a8203240b4a040c01d00660040303070001c0f03117003a00340a808000d03ca20103014030307507040c090505418000003810710300a0b50039511100380006084801200d1540e900600800004818000030700300d4100280c41781c109241180e001a480c010005914400107241c2019a405444581c0010540649100035000080078101a4602003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 65989840 1250 65988590 65988613
    0x3071403010b03030a03140c030f0118091b06170603060106110f0a03051209010b01020a020402090102030d02071104180312090204090b040309030605100506090603061512040302012a0c0203 83
    0x6000a00743c0c0000d9950004c0c6003c4415240008004042d08c0304000c43c07020303c1040b02c0c0b40c40d440c56050545920003c2e0041c1c84100e4500c207009800a6140100ba401822602040d8820203907801000c3e5070154942080101d140e42c9040c10070a01140c0c4075a0640c00f00d00108291401080160703070f5281042e007580c185404480b85a4078000031404118001000003c1100e0a884002034294001c83c4410091002d90201030001b992030640f03000281c0318603800543c030001c0b40e0007002140c4414000c0c40f41076403162030701d00741403814030055080380380224201700c203410310201c250501c00041035140e20355001504000008200070024024100d800c00c0d507a014010106801c504020b1059100756a87c030b59040c2186400b4042c5c80c0c01400e041807286514109015540d070300420340d208094199442c0e80c690f80c81500280c02c44508401543d5107840029a1020100c004c0069500c03540c0a41c001f444858280c0200d05a189007882e4540c0f80004401942400e10340304911850003180010304544841002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 65991090 1250 65989840 65989843
    0x40609020a0b0711040501030f0b06062b0b040203041a0c040f0305101505010c140c1504091407050f09120f01091a04020607030f03060815010501030b0d0203071403010b03 75
    0x9500222081070300411160704000c0320403851300304800c09840c20301265140d0f5480403260018038000810507541100001c3d666164601514040c0321118281e02440d02c2c02c1541440307480f60380700c82650072402d02040014900f464000c507802507a208441420140790200f2418000c0e001030401616000108070004804601400d114082d5015502900c190060180c0103402c8890802d9a0580c0d080c03a00c4040105a812403c80761f407103038200a0780780101090b203002c40d0400c0c0c50a0800d5610841002e000c20703010100c84050809d035420034a082000e450048106030b101403040f80d04a0020344100030303442e8070080b540080c0c21089405400b45040840801805040c1f41039a408590306a5440e400d160900c01b4188501e80400c202050840a5040540100b5418812440050203110007074000c42c01281c400c2d4448070007030403c0c4042d641040c0d80342140d2903d01d00d0a1244c503000030b042c010f90511602d072086010410130340c0180104840340c98501440080000c00d80c1d06a4195030390719031114235031030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 65992340 1250 65991090 65991109
    0x5030d03020418060819020609030604081b0c03030301031e02090403180b090303030c0a0207150315091506030f020409020c030403020916020a0308041104090b060405071103090904060902 82
    0xa588000d41c90b41d040c030090014500f032418081d003845003000c0c0c0401c1800008140c143c0300c03489880b43d400c1d0040460001c108107105072400c6a4061280300e04020030b0040c04005000c154a002e0410140081400ba040d907482d00d45054565054008100400000383e10f2810074240d11442e25049a602c0e0540e00020141401128141c001c508802e41e900007410080c8260005007d01401c030b07504001901000c00e82e40e02005101800032030300081d00d6003105008024440041c0540100440d8156280e00010083d1200b0880c0c0c41c41d140e11044081100c100c180185002c4103070142511388454940fa80c01c801a0170000300d010f20043e401c110200741c000e181d00040050100d148029076485195206200051000502ca000b02e5901407415114803913002c5100f0400070781503e400c0c4003130703180c500781480003680440c440c580c060301d400705000400650030045031040c081110704101c2565284000d032109224103500700300c944c204201504051a00e042d5040d045809500001001e080030743c0814603009 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 65993590 1250 65992340 65992363
    0xc050d030b03010b19030602070f08030a0b041506081f15021605010305070c082104030e012703080d0e1906060b1905091813020a0b0f0f0c070503 64
    0x3925240d210a15080074016804a01e0701520480c03655003840c6000800c5c12200d020040000da000546101441081003a110140390030584059482c100200e0150050041106c041e01032403c1c0f040d519040d40855224070110380340364992001995030144c200c0b12001e0000c00b81071034190403d038049a040c0e41c07041100c800a0903138009044030303440020f80003078100706544424105400c03c820822599031120728442d8107948900c401781ca4803408258081d000391410b0113803c000d0314010402050680c044100d0000c07035404e0300c44038891035582c405040800b00c2882f0b4002d1641c092001000082c0d40c010041c4175845501e040041c000c0c0784503a449041c015411590780a107007001c021401030007900c1c440c01e00213040000d10586000b8030600b840c03000c1d8a00201f00b20501c0030210380400652280c1880d80d036540d107072a01da442546024644d190266041e800180c1c0600c42500d008201b44241d402210080102c1c00b00181c1084151000e00c0301e580e1051000c110580103513407002a040e02d04014a45008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 65994840 1250 65993590 65993597
    0x50f121606170702030901050c0703020301020d1406030a030806130e06070203070507090204050a060327080307020d03090f02040c1209050d030b1027050303040803041706010e06100c050d 82
    0x616000c401042c0341d00b8407801d8071039158030406001d1642d4000003191445182820300d80d886490f64000c0c50300300421948042e404d540002000181100d541d440700580000c0080c0103c40398444100349640c4050104004001c9142e400104807140341550711079101100e0110080340000701d01b21002c0c1012410384041000da0720124078401006414020a0060880c0e60720440c101440c200c00148a040a40b14500078159200c209491041c405403804450300380189105505d05143c1ca41100d5130b500840c0c0007c0140100d40d41c0460140c4280a050030721504141d900b0440500c5808002c014400807111905001d41004960503c0f1107034020007000c03500400261656141e0301d4130103020390b56440c1034140301e41d992001c04903400780c2008204845513510302c10350017030070140f0300c043c003820032030b0341007642d00d0f1001160010b840e8100000403c19507214080d144d040b041500182a40c504084c008c1814064041c4002030316801d06040d01c10310a10b9528260700600b00f03907140d00e814024440328a1000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 65996090 1250 65994840 65994883
    0x702030f0a11030a03080f15030d0f11032d070f050307030e01141e09150304060b0a0302090c090303070609050a0323090f13051e01050f0a050f12 64
    0x240550121444020b240c1640500201145540c00910058000746146000a2018042548200e503034482c00c04c01c0f0809012181100c000384809002da5260626800004460100654071035030080155500400311141d108101c2079400c40d004151108140109400301d01440000007151080b26160a001e00032009103a4900b035905008040074510701c502e5044c000c000e003000303070890b80c00c4040724400c4120140c07c6918642044098105100c0e040f4241e074082e42142d1840c4144850b0130045000380d01c9800104034100101c828403054000902c0081d50003c0f28400062042c1078420081112801c01000d1300c0c038140e40c981d500c0080362200f060030b8810741d000320f2481c010180c00600d07101040081c444208960f26020080d2a00c510890820701d0152204101c080200c1c0c860000c0c00300003800c3c3c1c0800f03200600e080d0780598150f2070308005051201407000000166030510a511441d130070406003031020514144800d102545c00352183c2c003508101c075020140d40920b0144003c1041030b641189044c00d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 65997340 1250 65996090 65996093
    0x50114091302030f15030a03050304030e01230c070e040206090d0813030c0303081f090903050f04030b070906030b060450060301210302150a020301061d03060109110702030f0a 77
    0x18401729681099000358820112403001c00c0d08102566130240d0b1501e0f0000b40540100012681d100d03000c420140140e02540410a08004c490040c0051240980c21aa0728a5a270180202000c6043c0c4010350441e01c100120021414810b005561150291080300e14020040803481146000da07842590b0303001c02d24106000f01540000180e800051b09483c22200704a070308025220b403070f9644581c14002da501c00201c0201070048040d22720131611010130310707121982c80c103049070044c4080360b08100182010380c022440f18024071608103421800f534281805c00381010049541d0001586141101d110004420710f0b401ea034825210503212a1240100e41480b6480010506100d41e442841d214503801d000500241c60700710012400401c51540c1300d4000101030500780e00301081001140100e0903c2c00c02c109000c400307600118120f03420740d51245100d070304600032080c400d0b0711040541c0d85508081c1c01044198119004802060608003060b842c20f00c0b06e6001a2400b41e51015118064022000040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 65998590 1250 65997340 65997361
    0x91b0c03030106020a060506180a050603070302030307050f07060f020307030807032a0306050a030b060904030c050703050a0c09020414090a020d0e07050a09060305061305010f0501030f060e07050114091302030f 92
    0x103420a0080ea465160270000e1100f940002c00c0c006c00400c1c0c031135502c400084031950108140c50040d500542603c0d501d4005040c11904c03581c00300390700005882071940c0001c28500c200043c81481500d035002d141010706599045070203080c0500031004050300d0309070000030b081c0041903d244842180491042e44500498060145e82c1c4039800783d845861801030410100c0c1070401415030000040300d5040e000c1e501c030b2506580c034003804000900144648500402041000506038500900034810b0b110000d6581d01d180003a4070881c0594040c0c60300050200116040c4400350a0301700100074000b50034101100644002c0b01d04c5080303415060b501550040160b0b043c03404500000d07001c080402d000316419510380d1640c42c20090803040c094910b43d40d10300180030081d845864101803070341080c449542d60b030815038003040115005440851801240d00d0008074002074000031940113841d843c0750008900007100c0c0980140164a421010014003881d40c40050302c015480b403080708a04294605015140710f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 65999840 1250 65998590 65998601
    0x150b0a2c0601020705010503040f0f0b040507140d0b0415020f0409050109090519080409140103020f030a0b06010c0512030703021911030f03090a14010c02100605091b0c03030106020a06 81
    0x85200c00030380502a4590380410844180d8800707081940d41d0780c0311303450900309020b54005d014061031003401070300040040c188445030003a03014000f00c4602a4444c0c4103c0050285002c516034040c8915401200003905c4503110f55009000b241121040c80c02c022340d0070141e030b1080b140704c01c1e003100015003480303000c116100d414003418078150100020042640c8540d13580d04943c50124a05c0141e070128010001c8507000c440181a00c441c080c0210b261620500b030b9001001e0000324401d07901d11203400c21074213002071445010ba400c0714610850b074840000540b541c1807031140990303481c0079a88d16907090618140065000c1d45a541d001030707880e4035041140e19031190141403002001460301424495040010a552070710905054040c0d4980383d400c00350307240c9604410010f0000d020306405882158042d405100300c65166002d5030b842051a0225208a86140c050756500128180100c0d4000c00d0720203240e102010b4030303040303c2d107000d0500410fa40f46400903404134005034002903943c0104030907070056 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 66001090 1250 65999840 65999909
    0x4060507200706050f040801020c070e010b030415050702011d15060307030b061009080f0c01090518011701060509010f06090605090303071106042105010b010207080307150b0a 77
    0x50084484681101e0307a112980e521403502000008034411a0140741402221300600001d8000c5503074041d224540c52301e030390442c450310600101000000a00074407107011031780701e0381d40050000c2046c1e119007600001440040c02c0001150f68805005032031382d10401c807500041400c4002004103400d014134100c450031000b0b100700d009810410301000010400880305802038003c49680714203480c4a0740c201c4014203254022210781c850b6a10040c1030600218840316144803c0c0d036180c00c0c250301c1c0c2051010715070707585030100304511060300104200c00b00e040f00c85859504100000c50056030310300004455840c01c0c0c2009420000c082d1080001d03d4102140100401e80740c02d0050510b144400080e0f124000c1c0203020744070350612442c91040740c0d80c04041744d0251001c515510585280003c3c050070120080e40d04462941c60a4131050840d070000444000301c4449074019441e03c1d4a554402c0c00604daa0b0200d00310941c0c8444006e4020f1741c4403d0241c010b045107a2000c204100c0341c0c40c00c910074810300c408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 66002340 1250 66001090 66001127
    0x3010f05010f09120201020a0b04080d05100b040302040917040e07020d0201060302090606160c1701060e060906060d0b061801032f0a09050301050403020309090c03070e10020f010504060507 83
    0x5805102c1c2d600001c90b44121a0101c41c0700480301141e0006030300700b10146500a00103e0300108010411a03110054000d43c8a580010007903555001518100010540110000d8a0040c4800c00051030190001e0b8803851241e11002440304401141d520590801d41107446613084a00800402c9a41000342001c060b80c0791009105081c0f40d41c0100e8103515014046a009040003e2210600b180c098103610010341d00c0700c0f0903074000380d42d0b40002050100c4ec4000e05030700d50800100086162400303880c0381c0544001044004103448503010018079a00002c2e842c820a900d41c1c0000301c0341d6455030b01400300c0400c1c07100c540e00b5281100300010129080032850b40810100944103941c0f844000120103454201d0f410059500d241c0d181e8290380290142d400154150300342410007080650110203420110015100380c031050711100070010300c44c04111801d0000031b8010b20a04002e2804503d52903040c03600340140d84060417910308250a40d80c088405641c015100c2c828003040c16840318682812111300384 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 66003590 1250 66002340 66002357
    0x80703030e10031a0609120d080601090f08060601030506030a080703210c090308090a030f0c05090711030702040c0c12030501050306060402041a070c050901030b04050d1e0f02071a03010f0501 84
    0x404c00500c80c003001070014000c48001c142030a10391983d40f0a040d4002d00081110030051324080000c00f03010b01103407a940015400c0c1400a22041002944810780d0740d03940183c2000d42e06c3c60011402048010300303150345489418080008149030200411300c5030701a551b07400810b000e03071546c000310716403003440c00c1481c0c0e00c0e10716100c00d10365101d2028420f80303034003554465462203003c00003502030420b0b070009440c020400303000c41c0c2041004034601c81120f0090300c1003141d981d100401a644401e102d2500d00c4e007a0002c01c6200c0041c54243c1c05010900b4103403c02c100031410584035900d14101342150800400d0f40d41006100e5445c0030004a5408901190300b946482e00f03065056800304880504917400a101260324000c01000c903d22001400b0040d22600d030642c6d4030f003000040c0c41810f540550f400d014620442110354418907200c4180740c2030044001d480e03048400c0031a18054515604001c50241d0381d0081801c103044003030510150704402c1e880d626941031050380304002c00e160780b00c4c1d4180700091 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 66004840 1250 66003590 66003611
    0x51305060a0c1101020408010614041b210501080318031b090a060b0a0804110306040b180f0303090a020a080106051c0809060307090303110c03030f0d06080703030e1003 74
    0xd00d0a5001c1e52210000c509080110015542c1c4030381d58807071080c5035001103000f05d40444154802000c44055a003070f00c0918081c0c40600040340c510140b4222182a0b003410014080c3c021003a503079000141000710490b40c810380341c00d002103c2c820b0700080d066170030006001c2110111841c03a1241c481040b00a05550f40c525000b41c144540c4004612b406452040000345080115600110051000207a090342d01d00d1403250041c0a500d084900310380f400d070700120040c0704d07041c0020218812980501084003a07182d280c4107449040510304514030301c0c0f003040300080d2035400034400340d4000c0c00f141000b0301d6040c04910401c12a00c10baa0041c09150f8907011041042c1d0391901880d01c0003540c64186502c03540d500e8101001c07103129440308280c00c580000184586994803503004000c80f8060f60361100d08091882c40217031210800115194540c0c028040319107000c5000000b4420380040340f01c00125203035a0003a481c14401035a2041d00030a00c01000011541400001100600d049150801424003039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 66006090 1250 66004840 66004843
    0x3020f010f020c10110d0504030212061302061c1103060406060806030a030c02030709060e160512042009130308010b03010308070818040207110307091a041104030b0118051305 77
    0x456585841010404401304103a80114040300c0032a42040c01e8500c03400071440003401d10743c064407040780100f003550003604040c00c02003100c030300030300d01c1045c1102d2020068003000044c4d04091802813115078407480c14440450f803480f03501900104003681c0307030b200c0c5080002c00c02164080da10034000c0c407202e00108445540c000c60fa000445d03501d030a16180c0c02e46070b400404d04e02091600104c0c0f000c0c1c40c254022903944441c0c1d41391445840d50042541a041d06014103e406000b0008280110b2082034003040010340c01206146070440b1100c003000075510250002030395040b06032041342072000c805910b05c0c20304d9400150300340580300e98214640346524541e103c0600e482218005403002c3e0002c20b445071805020070300c079a5009001041551620b40764108030035030000c0007c40910900c64804001980031140c040c29410003056850b10140341c1e018402e003c0600a00c454004043c0406c00001c000104101c213194041d00011740e60b4000301001044040c00c03180c02502942d200000b000f44803000540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 66007196 1106 66006090 66006103
    0xa080a0c050a05071103030f0403061506020706020a120519110c0f060702040f0209030d0807090506040b07060b0109090f0f0f0b030c0105030415090b0103020f010f02 73
    0x140d603801959240720300c00000e404242c040c083c91000c54400d800480f090b21010f4280c0e0b10f0020300d042d00485d03d5000c0d40040b035446035a8240109007030a03090005000c0c0071940001d002290030700c000603650310504440189003007150300056200c2c0e88202c043e154500030083d609454800301c580041c00483c654010500c2c01c3c0b20318440e8003600e1a100300395413000000602182d140c0041d580901028010074440c1070310141d002c122003110350701c0030000703200f80b0310076036403131481c40e0070b018200828079100b584c06544518401e00040c0605140b20040b1256a80d000e2400550000340740010b8403035100c035074084010a841c0210b01000e0b1015500141c40b80c1a642404000519a20b40000d003211582d10301c590301a804100c135010b055000308025034002c0d0249910141ca15110b48500c42580c0401c0e1040307554040c080010011401c0c0b01c0c0000004032000d080458650841101c025a64032 = true := by decide +kernel

theorem cover : BRFrame.Cov 65827340 66007196 := by
  have h0 := BRFrame.cov_init 65827340
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65827340 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 65827340 ≤ n) (h2 : n < 66007196) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
