-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2926
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:09:23.246971+00:00
-- url     : https://prove2.me/submissions/3323c8c5-1912-4de0-9b60-ef24b961a19a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 526079136 ≤ n < 526258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 526080386 1250 526079136 526079143
    0x204080316020f0102150c22120c0e01080c040e01060e0415050c1204020d111005040f211b091b0e04110306040b1305070f0f02071511011b1d060c 64
    0x1f1800003050540c9501e004041d9201050b8402d100300f2000809800c0001c0065900110901141c441c40c0500342c55651042c5a00a144080c002c008081d0003403024080503081941c031202d203440d20440041030301d42d0b84071040b01400c1c2040d00d042d6104090324581c0c111451007402070070307002035a40e20344500d0186449820000e400c40504000c2c8034030100c0c030350103042c4102c100c241041100020402c3d0708a2040310f0014005602911a40346104112900002c240b0804941035241c1170f0404004d0460f10415030303441c030f140a80c50b0325007a0000056840403a80072407901c62003030882191644102d1142111802810081b01c030043c1510960a24440d4084d640010003a6608420161070101d401080000042d510361036402c0320b844031614003802c102d0746507400b4441c1100d4400b00d448401845000c810200e8960807d4000e07800e0007041d1054164140b4400c40d24020b0401c40d0900000f15030075088a960542c1c0c0d08103030010000341c030b0300b118270020000e1a40169100c2004840d56880c21480c01e6141c1d46 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 526081636 1250 526080386 526080391
    0x190c26160816050c2d011104030b0a050601090e010b0d0b0301050601020c010f0905040f140f0403050901081b070b070206070203160807020111030403061a040606081303030204080316020f010215 85
    0x10000e01240c0010113000070020503c0007183c1090f410041c2c191704402c1007a00e000110968074941c00c1c0500a04910000d8007120203030fa070024800c1d04141d840e6001d5101a03c00549694104076043c40001840505000c8040c040c1400300d4982d40d90f227081080c814280c40d180c1b24094442e92524041c89900e0703800152480080b1400c1c00c3c0301c4800c82c0c82e64030a0340c4401c006d5104680090600800340d544450940c4100e51b1000100311007200750b200c00c145a840954110380c01004100100a140032940c05960020f602880403c8a8115100310060501003074100320421102a0141018411225010b01c0b0081d40080144015070805a0359070201030080b8a0180c0541581c900050b49010b59104444046070803145000b00d03640da030343e2440d0017801070624026078006030601c1c001444076403400c0c0c000d20084a03900d0b40c4040481c0c440e80c47c16041d582090f030003241410f50800001074606070500207840f0030a50600a00307440030490062180f00014000940d0454201202000d101c11001c01c0868 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 526082886 1250 526081636 526081681
    0x3030c12140313110a180c02071a032d0f0711030a05160203011107051006141e040c0906090803040602060f090a0506010b0d0e06190c261608 62
    0x43d081c000e10b0600000300b600308541c0e9900038501c184003003500d4202c5840c02c6014502c03210b0411040c07055407030498844c0000c1c012409504031072411540c0100354440510f0700061002560039050303000c5c07800481d00c24040c0340071901050303900b0200018040b04c1041d0301d074069002c0c04c2c24410090000203c640720700c01d40e0080c40078008041240c020302e264000501e25000d9001e0000c02800c0400c00312844141c2141c00201c8552141c4400c1e05c1851109000d8603085038020075902c20b010f507140d000c10848142042c4017549540007800f40300f503d0740c3c07a0301409034449207070344401708068140703d8001c000040507000000e0a07807007007104101c41640020069407003178420100150380d4652580107170404445600c0a030140c803506001003061040000240140b072580201001184107020381d140e01c86604588503480b000c00b000da428024805600321310312000f82490284072001e1810f0425142425000d55120422504010415000030a410b40780e6088200e003050402407a0420b140601000c0110800c2c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 526084136 1250 526082886 526082911
    0x50a0f180605011b030201060b1209101e1a0d08030603150402060403060504080f0711090112051b01050c06010801050403080c13060e040204171c0c08030109020c070f03030c121403 79
    0x104203061003907000b03230064821208141c0d6034082650101052010549240b03036680200651156488418411104078400d500e44e900300140d94600d42100400c041c4401500b504803116071500c4640c0c0d50382207900e000e40320f810402d440e030506005040c5403044646814a06c503800320113000169071000213036000c803540048007003010790303840c07a00c4111401602882020b01c040070440f6020000110401d9124840980b40c4001d142e03a01c140e070081352000c0c014064800c2d004040d521014549a05050303107003602c1814254500f05040e03400d1440c105099100488071b955030390a00c0105a445040380d504891846012820551300d114519203203d49441440706001c2008144c034040e85030703030701510000c09004400319403002800e034125460301114942c3e08100d55445680b4414603000e418041c0c51590084140303402d507030030000c03004020340c00086541041d10400d54000f800d2910520076a01840c031903510304911801d10b01c1c090203829040120b000c1070142c44403156a00a5119041d0307540701d40c005246 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 526085386 1250 526084136 526084187
    0xa0303170a11070b040314361504050306060607080d02250b070906030e07090e16080d0e030a020f010c0606150e150316050a0207050a0f18060501 64
    0x381401040307000700e604440640803e0303003001d00c82d038000880c1c0318500a884002e15881c01c4100d180d014820742c0c515003500d80c0c00319600c200c01c60340700c8005039001201440054003402904000b6484118507000b0000c00a4001000d0006040030b000306d582090064511030b00700803017507842000324003511854143c07203a03022403401e002414402c800d48854009200f114103407403103070401041904048502c007003c04c0c4a8200000e80074824843c1ca1a41d088000c017800596090861601c098450040d01a8481c030410300d003003420000800c071020040240500801091782c0f21038024000c80d5659002e41d10a03008032210001584800c508000169070900e0a601c0c10310081c604407006125030780000f060f50008c104001101e43c0c11140465880808a401e4054004000e400301c40c030344011144403900100417030b0110440b0b401800501500d00c02c1d801540c100c6925480841d03505441c90303200003403505440304200160340300664504240d0404400500c003160034000080d09280d1140491414201d42426 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 526086636 1250 526085386 526085401
    0x6051605070e0c0301031e050c0d0f020405070e03070f0b030a020f160501021b2a1f020604021804030c08030c070c0815090f060103150e06180c0a030317 67
    0x2100020b40081c024100c0b490403c0d85604034190002d0108603030782c95481c1c4140130158100e8040101076030b8080000c2200a80d028148043d075944144211016207800049100685c0d840c0140c078400c25407541c0b0800000100c0301007500c0e0002641c4140d40380c400e9444148150741035801200d900c180c61b550056654030341002c00480358441c06200b1168030159070362090800c601074006008086421064180003210389010036190501c950914901070324001010042c1080060f102c2c40044005141c105103101074659040702c5002c8079140e6005030011000c00c421441d2061911508509400844885140c0b43c2d034080c04031100f008000c0d00450010000443c52b01d804400c40d8106030348004200c1042d40d5450328150350304100345e03043d004a040c1000083d1321701000a1541c2c40402d00303100400080e483c54603583d00c218413400b0070055007511803d111642140401c0711500411807480d00e100781e0200a004241000100c0c20b10a101d50104601040829804001d540481c00354110300c00d0b844d1142c80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 526087886 1250 526086636 526086643
    0x6041d06042a030c051606060806011e030b070c02030312040203071505030f0c0405041410151d0429010f05030108070308161b091103040210082802210106051605 71
    0x31800c2100b8074146d10b0314000c004158001c00b0840d00004111145039032605840081040c41c00110062007403920002c0001c500c5101308140c000781030782407007465122190082811980511816604070700654103100840c1000c10040b0020000203030b541c201902150381c004d00d940700180c04100d124802c3c80100e4440301020f4112002000300803c1040081204e214580581804481450031141803140004001900040c80360f00320090f90b071482d0560181e002440320a802441000c0d8005581783c1c0c1c1282c0008000c2140c1c1222030a42c4186980140c40c034000400d29400c034a429010080c06000411154070700040541c06d981c0d100c135903130341c840c0d18403a44401082d00d402005004d074543c9000007461580300066003000d60307421401c02d100141c0103101412051001b0381d4002c2d0480500c0700207a00b1507201d400c001c0d030040c15100d0710403000700484540c050004010401095815400180e9040144d880411600341524102e00458158540a4090154029060000104506003001104009060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 526089136 1250 526087886 526087897
    0x918060a05040c11100b0d1704080d110c010201060614160501020f04050a15080703020318060c130f0e04080c12030c1c090f020f06041d06042a030c05 66
    0x2c0c2082202894a441c01080d003011411421128041d0079600902c01519014840740040060300300d508000d041c0c3d45039440c5e2200e0501075070b5110400d01c0003099900040c0515000c495599485c0707c058501d0032245400c0a040c3c1502c00d040da03140110400c0582c0d008661480d5500b00380080c2c5072a407514410f114100e0030354002c014030f55440054240410340030304010b402610800e845603c013441d100c3c107074894000340d00001c1c480482c0720000024041032181c1c000750760004408441416603541c1182071841c0c0107003561407020036107002c030b4240401e2000910382001446901a0742d03445500e04110005507400151026020210014000c1404274003001aa2542c1100100c015070302d1502c03020103d55a082010300c1c08284100104c14a104611030090504607500400200700401c0070b9420880500a510340094200000b807000040584141780401101310340c4814a000d03503d0480200011a034a4442d8804e107281d00c014000025075480355027002d644014280000d244401d07460964560007070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 526090386 1250 526089136 526089139
    0x6040c1202040905040b0709060e0411070f0506010303030506041a0603060a1703071502091e030f070306050906090109080307080402031504030c110901050312070f060203010b041a0918060a05 84
    0x2d40014007007081d60103240304034058000c0705441c1d12918022102e184040c810f900002d88841032141551826070b100c44482c0c24004d41c0d251500080d0f03074940300c01c0250380800750b03600d40080004100740350301800380c2984031008840411804801d0481a00c209140622050141c0d1000c00000c0940e1a4441d2081c00780c51032401003400303003101d089442d84c2c070352289401700e4403c4c17103890600c0c4654200f4020740f6403115000b0958585005403844440307041c2c00e038246440d03045c03262660040d2520424445c1d00082e41c003d40c000724040c070b08040401c3c51b094001d420700441c0c0c0c2c50314814001258120003641d81184681c9802207250700d443c0002031400c01154034900c0884501d03400d100401d50800200103019200745481d1210700091010400301140174442e294050700032642c400049690b80d8001d16003140f00d200b029020401d25100c1c0e1049070802d8100c0088401c0006051000040641120081042e5400c0c05490001904042240303440303007001c4645a0040d0001007100c0d907503071080c041c019060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 526091636 1250 526090386 526090391
    0x90501021f0e0111071403070c06080601021006060309061a0913050a0c060309260d090c150908060a0606050403060e0c0d0605070f05072d1202030a0e040203060906040c12 75
    0x1c00200b501c0035030b0286030708486c0385030030004c50741c0404e2000c001c0d600802d810040d440307500b510784907083c0c0340504014880c0d811801345512025502245104200162813183d800060002107482c014088901c100c421900d000524501d058107681c441c00e605a1004401007090f94144040c90554540410184020030800d070102011074425815840130742614043c0640e840d40c2400703540c003401c0c0034060345c142c200b060604220004540b41e4580004036424030494400301407950f2401094004600c4001d000c0004a280408001e409010001075811403040142003243e80d140c80c0c0f010380f03a4821484014041900c40b010800e0403074051081c09800d54001d0105d50056450b4074144004100407135416012511104007030404038402c6041e51401035200750300889086203c82242c1c1e040d03505030721010000c01c0c804010b000103501c14010711030580c1943c0003962106540d80e00604500d141e01c3c0c1c51400b8070310610030043c0c81d58508a4281d04020290b400154003050f64004440e05005507c02d41807490 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 526092886 1250 526091636 526091651
    0xd0311030f091302070b24041a040e0d020c150705100615050c03222d05040e0d03090204060f03051b030109030804060b0105070605160f090501021f0e01 67
    0x100460002c2040c1001150344900d103c404040490880c02400b00217012540d6150018011112004807290082c08503c14184110b866500003015503032540c0b050b52a4a000d4012404981010300400707200c0318040000d03000107482c07030000940d40e01204060134814000b04070080303035010784002100d5056800c50207a424070f900309031490018280901c94940c145e10356404200c8500c1c07240c410398420f00b40c244095443c2115801190404140840381c0c8203130640e11204c006503241e030460f6005904d114a20390483c0680152018903c9c0c407495178000b90044e030414408081c0c000c008107a64404620718280069040d040d4004100103003100d4000c0700e2240481c0c8000310602400094450320003413920b40c0802c3d0b00075908141426590030304c000601191f880c41c08603002541940054003c039074117240c044d082002680b03903070b419600180c0303588458805842020350700325845170002048400c1da042040009252500003907903401362425030340c0d8001e0411204003c00c00746030484060341d02204001d02010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 526094136 1250 526092886 526092907
    0x210108010905101104120510020a1d010c1703100830070308040807050102090d0f0302010e1507030209011e020d12060b0403110d0203060a06080705011d0d031103 71
    0x80c03450410a4581e07104142c0712000c80360f081e000c0c840180e0710102c00c0d141807030301e4089088841094080d0846141c06104248840f1020310310262145404a50341c1881580001d80501808001c4c18041c1741084165858480480d0540401c6901444e420703203140d0752030b42d8442d008031005405421030100d41c01641095441481030300c2c20b00f0a45040b901601c000300131030044011841c07280c2840140819429800200451003000c00b030000103000b6000585030140d40000211380c056000c0040b90704484083c0c0040c2455424030446005000303072001040f04034000043c4820644000b0480ca0030180c0006001c0b699901c661443c200d00781303041d0220241807081d01c901070b4807124006c0026001550080c611026280c40340940000c6072001a4500e180900b191203407600032400c10070b500d401003448840e80c001a00c0421103503102d412140d0000031581c0c200b1800d14204a500e41c40702e81000740c58001482c0040780300e400b40000080841d0b0b06120708916180580b00844004d00f02d44490001080ea8003d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 526095386 1250 526094136 526094141
    0x90209070503160e0f0f152b090b0a0e070b0712020606190909030c080c0d08151f020a020d0c060f0306140405150a090204030501050f06030d0521010801 67
    0xa03800c0180f544202081d2030728112090041145042c2e0300c14007104136228a0309024540003000b0a010706520382c0010b15914510041e440440c0920020720181042e0000d110400c00840c03901101000c10320440806440c2c148001e030010301100401c0d5030764058054960700c20408900100b044500d850f0700c5481c1404d19005039145c1390010005401098000340040c079012000c5480410620b1044080d82d00300403104000304840306c411014400c0301d42c10280403420f00c2c409808a071b5007490050010300075403080107140c80b0024008070320003540c09811408503070341d0305812028200b54210005500e030403010100d15003030402d200650030031003540c060400d00101201440030344682d0384800c0d10300c80c64100e00b05e044510f20322880c2e42840c0c99005841032882c01d9002035401c00038444002c04501003440000d60701c0714266101e425600d50001d002c100b0403000380902d03035010314401080180c0d803030300c60040707500e41401d100c1850400000286112070f64005904c1c103c030742140002c00c00d54540c1c5401100c1e00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 526096636 1250 526095386 526095391
    0x6041506031a0103060e0703020307050906040b1306050901271a0705060f010608190609060603020d1a331207020f060c09010c1e05070e09010908030118090209070503 73
    0xa4040706151a82c29540207000304002c48100000004640e07640d07040882c02900064410002c0201c20002c140d22075480c01c0190002c0c00428194503030714a8250150900083c5503845407051190074041c0c40706580c2c201a030480f2440c0149906ca1040780d44010001c1d241c40b0540000c6110035800c003c81c1c0b40c0c003500d1005821441d108100720340413a1107035103c01d16124802d2117840d0015a03420001140c0d48480e0b130039038018515000001c1051901e4042510964100390085000a0741c0401c60703803000202f90007800408030350617801902c9c0c40d80840114911802d140001540041c41c00380e841022840d600c1343d41c100d441c51880c2c40f034403126003c0d4007086400f002d9510b14018030440d101c031040c00c00045000350254002d00281c078900249140156001000c04d0070640c0e10301c0b0200d643c02400464a0002c0520f5403203607002e0900941407c1c0b12200c0e010340513000b04244ea140500c0d540010341154120b1341035072040659414200c0900c0003c02c090804901c0c001d40021000c0c0500c030302150050042d60 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 526097886 1250 526096636 526096661
    0x60b1911011a0a0e040f06020d090f06050a1a060d0b010207030606081c0f0c030807022d0f03131206060b0d201e0a0c0b0c03160309050c04050604150603 67
    0xf021156103a0702e0000208064602070002c46416900a0000700745030300401d090440c012002c0ba055029440b010b16078001e130031050781d004e070f04c910800402ca400c0c0c0c0310b02088800e603c441d642183c800d10300880d8141c044c0d0300040d02550b07a590030443c903070303802000b8040040d80c1c0300344148078440c3c4034510309444165840381210a88403584031941014000c481c281c85203162691420000100ca8030125607038440035214200754000e04810754002d150300314a01030b1280c010004003113900d41c15a01c0c2803401d4240b095520301c5810901c50b05019a82e0703240d1500131141c41010099503141a82840c2d4001c164a620000207440d000034080d8503450181c0201c0810302c00780440003450240c89198a4952088460045200a800c660f8842580d030400142445210134905031603010701d6030341e0304203400074251010002c014011080013400c00d28084806803a1506240602c000d45182d076405540e001100081441191190700040c2c994480d5445507207011036411045502c01c0da2004060000c110b0f10a861 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 526099136 1250 526097886 526097899
    0xf030c05010806221b020f0c090c07152702150310030204110f0a1e050415030b010e030709062402031608070c27060b1911011a 56
    0x5640e60040b800c40c0c0c0b240c0005410000a0310030754032034294030804548034060f03a55840744656a42000f00c20220148400c80c1c000341070141503500480d14000030b80415610518040b03041080e0003020000383d40103103038084c510215000b4205000340292480d00024001a0110044000900003001c40300705418003d960180c894a20400058094441254448241101138104200604142d40005142103180b520079090842c1c600d05010240d00460740740c0000b4a00c44130944900ca8904070003907a40392030341412803520303107001210b00305641c010b4002e605140d901e02c040c42d43ca074000c002a00103a0401400e4540c80d40e26a481c0c0c0c00103202d540a009140015012039000141c01200f210800e03480c0b6130020b40c14440502c1c500100c0440c0007008941951007440304400048100700c806014086111603040020042d1071310380f100d80351109404421906205c020000007640d00229800c0d03000b5200300d007500204100e0191410068003000d0742a80d031030906844144000728464260522040700c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 526100386 1250 526099136 526099139
    0x908070c140a0317070510090b010f14031c020c03060a021c02070c050918010204080604141b060d0617010929060d060605030d0e1c080f0c0c0603010f030c 68
    0x9100c85070750b4901004085014801c90b410382d5070806805004851301c241b0884250202044820040d5401e07881c00304c40f08501080103015413680480080302402a40100741e03107280150000039540c0400d040424110201d034100300c0e0900b4424000140407001c05800c039181410800400d10081d444200e49400c03581a0030b0464665401034001c9801c3c003038211007220440350900003001190000a00703103070151600c405004000070400e0000c0e100038a80c5a010300880d160609010542250703a552000c1650000c1018038200b1800d240b1b0740802d40c0c803d85100303845030303a8481000002c111a400584100d280c00c3ca4040441c401508400d040601c9030102203907190020080316030101002220030868990340c070009131207040040380c0c2214680160303408500c2d42c0d40c40c40400c1c01e00d8440c001c2c0c1000a800400d1240150030299180692407000b481e0300c1d44945002e46686425006114032442d60f004009000440c0c43c0c0b0030800c60f01404d1300201010350300d5940785019002740c940c504c000c5450307000c80c0700c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 526101636 1250 526100386 526100389
    0x31b0b0313032a140f0d0f08010f031a070203090409050a111906050705071203030b01090506180603090703050708030c060a0204050a12050a080d0204081c0c080c010908070c14 77
    0x20158080300580b924a0f04100050340d4544181200b10b00c11121403040300d401214400040004030f20007499501d69040204039048010903040058108000048090404000182e43d4040841c120b2024145040302c40c2c5031700c0740490541c8900305090354018285407401c4103100300815041d405a1061818038504e02c20360342801118414490b20b281c1c0c00c3d412040420025008100601e8458403c03401d54154940b2481024060082030b00290f000aa64804007022540c01040d0440078010446480e401c0502c1104034100b81008800010300503c001300219408a408010001c09954001c0c2179441081d19251025900d801061099a8a00c202404110f40f11100d2084505a40000d071045950301e00f8405040c5482130303018030071a11403003540801d4000c01c00c4440500292401c400300581d85600d40160b83d4904a50281428042128481c0664400e90050f000303640399a44500700b00d88403010380f00700300d00401c55590f010380b201400055500c20081c200801d2020f031180d030010b200300f1481140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 526102886 1250 526101636 526101677
    0x1c140705210c280221070f260303011a0405130c14120f131a010f050a0e060d0203030d050114121903080c091c0c05100504031b0b031303 60
    0x180354000070f060951603a00581081006010a504484091003245291544039490514258860b110311020300d9018041c90a6090000b00000003800300e1200001c1818002502c0340301c11700ca0b00500c0556400c45d6103c0c840d144042d60003c181c0107042c035020207951002d98026050828945000503106803000c44150b960000b07480c03480201d800301003995580c2d0000d407203c180001e04440040851160303280001041700d0b1980703200d6000300c003416105514140100c2d4079096150807891103007148090901c20142201c0140380e00ca10100e41480e4000381500101b0708522840702d4454003542000300106d40300f0900000420220000c1d01c0e031414840800200c551610f4500b10032044001c081e0056602003445424005d03040158480054940040ca00001e9070180d0400c1ea0840110712201d20802803102c5040d04200038182541c1a600e03a1183c03d80c0240f0911441c0401405101403003000c1506239658036024010300031010110f81da9007030002801c50030a030f008008a0006401d408200891300300d06 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 526104136 1250 526102886 526102933
    0x28030b10030f230303150a2c0c0f1305210c090709090603052b091203030605090109020c01060902090f040f0e16081c140705210c 57
    0x100c800c8003070b040c90b624030969a20807030610500b02148100d0b5034040c0014002540100c0c01c4114205440780045d06100c041401c46c3d0001d50b010a4144c084080314202e05210440c001070704407643d030740c1e03511140469a54003600700012142c00d00400d021343c04407280c1015100342c841c11590b6011012240c1c090313900c8194160001d2045420248640140e0300b40180d01a0300200241402a05186c4075190702040714080c0d40281c0c3c40d42c0c80348075075159444002078030a04000c2d24010708400c5400c0404060304200f058810020102800b0a5510500d8840e0340080060a4002c069207859659821020080c0d046101c94120315403030300346c0010b00720340c091003114800c0001800c24201459010100001020060040c0640320345982c500440254144007203400700f00c1003816050440d04000300c13075250000480450440184410116084941154184400f04400092641d54042c6840c0c03484c20510742d1842d00346000c1440320400201aa4a0b000e49a0101c000b801c8950140ca0840d50b00c0c200c40a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 526105386 1250 526104136 526104143
    0xc060a0e010305040f051002040302040e06130f0327080c121b040908040b0307020613080d020a0e040e030406030e0303040c0911120a02030a1a0109090b28030b1003 72
    0x40100d000040d4042e0f0001a4802e000300310b0361840801c2d40c0c9501d070908840303440d0b00c004a0360000d4107108615251040312058050000141920720b4003c21900290070b000b078000e48004034207a0701c4410148071b20b00103421401824202ca03010305002c0c10640070380100e8040c524050140314012000380c10700118030b03490aa0100010441e01e02d4804500102400a808030790b0401e4607400a0740100740200e004000400300e00f0502503903850040d80003420310030044c000031162100e000302ea001003003504098400b400741c1e0701d1005075200301030a4151020403014100c0c68005041050b00d94180d0808400350040b10100e480c24480c501c00040395076140c2c4000c8800a0000d90000010301010100764000f03007034031840b40007091401800210900300c42e01c0c1261042c20304d0341c0000420048000030700490041d00d00c80070b6120030142c40000040d14540c0d00d0f0250000e4640d850b02e50812a07522010451150909400107150804540030703454846101804192051107110022510720b0500040e498100c981 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 526106636 1250 526105386 526105397
    0x81501020f0607230c15010807080604200301051302130e1009050109020901090501030c050a0632071a0106020f10020307050d0e0a1a0702070303030b19030309080c060a 74
    0x1203909050f0340006640e2640d001a041113010313844006040d8004240000109005100b40004560003062040c0141c000d5011074000030020040340384001f80d441e070400e500040d1003104902c1504040ca1805480800c107a1543c20030082c010205400c03019199414026104000c2c0600402405c0060340d00028808050f40d11802d4012504500380c0e00c038103c8074dc481c2c40003041114580d00010300c5c089080c1c01c2401815500c600401c10491810300e8000103010a032803c100d00e6140450140410ad940105a2040d500704c0005040034400701c4000124091442c26131900d030340450510944101400002840600003100041085030000030000c600c030b51104001d042c499070144d5980065000a0509403e0220502541d51444060300034112140d0115004040e03000007414903803000a04450700c02000011030051090841c0c1c08580402501d805050100d101900140410030066445018000d002c0c070030034000c010541c1c0300440b001191035075000c0b1210181c80030104032480c405c464600010a2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 526107886 1250 526106636 526106641
    0xf0507030e0d171b1909090615050904140108010b120a0b06120304150c060b04050f010504020f09040e010608250311190311010210020c06130f0f03081501020f06 71
    0x149403603103a40102030000c0d13403010145561142402e0380199a06213032002c00c1d03440750054540d00040f90002407500c641c05001061410345010032001858607440101709000845002d42e4030780c0d400c103240d0144244000016980d444002900030300406c5500c0c0e100f5900d012240692944c006125a8015003001c8d00200c6d6444910401c0841d0100521048690105102c001180307000c03100e4013a451589902c4206214456282550446810341e5005124618000a00000c4c03005404064191a0301b680c0c0117a90f4001c404241001e40138000343c9652260a08a00b01e500c00b5040d040b100c1210740c880d048a46091034002140c0d5a0080710901001600ea051000c0020031003c2d000304885184c060080e0201e6591140c2009144c18aa041941e03030f041d4000f8601008e50381044203a204840801d1701f1420103454084254035882c0203807201d491a803404160805100c801c40210f010154401c41e1034103481500e00c2d014051240032981c80000000c1516414819400840c0749000d000440c0054542079 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 526109136 1250 526107886 526107917
    0xc0301090207020d0b13060507051305010e0406080105040f0606060507031418131a0307061403061815090c19030c02030c120d0506060a0906140d0f0507030e0d 70
    0x940000c00c0990b444134400409070b000c21003401c0618000d54996201c0c04106020f410007405891018142500b000400c1210550b0442048418011394609203024411421301d400064081e241641080718903511781007c2c4420000c1d0080940d07807007441800288021307541c07800d050300c0728081d07100c01401141107a008001801e290340c0c001d01a4541c2c0c254400c112496600104040000440c00125401c0e81d59812145030014203203400b141c004110000c20b0281d08221004081c0c1880501c0081a0100171010136115520142c641c1fa0340c84045100c004d01d0716004683e030802c4031079a21a94021102503000ca0003040360842150303400c44014081030091454000c0480c02030410508020840c00140b01000c1c9450040c03184080c100380c078040c00781d00c51500f60200340860b40080d00c294840d038401c00c01c1c82501a08041c003002200d4003030074500e6940c024070300f05d16010311500c1040c0d5642d0385810802d112006642e406036000b01e00310f907001c101c1242c1051040d1390320510b030035007a008101d80d1500c8481e01c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 526110386 1250 526109136 526109141
    0xc1509040603060204091d0c031504050715020d0e04020403080f03070306080f07030c1202030703080d022a010c110c0d02030a0807060e210301060c140a0309060e03060c030109 77
    0x160a014100080041d600c0d00c0b10700c2240c0003904510820342e11008614100265003009103109031141c0003800f00c030009000003a0391001c00042c0110f000500e980040c060110600081d40100201c1411200c90001d1500003511340c0411446000404e03484401c0442e40c1c2014425207040c1da42c09510726103409000c1d0510700b500d07040109a64101501d5503004901800c0a100840005543c50002d20181d401c41c504146290201e070840000c4403618061200560340c00140f001c2200d41141d94250f0303969955004001038400c2c81c1110860500318400403012000000072900c41d0344c03401008101c42031840e01c0403107110151038054261940209000c0302c0c14582400d064002d648010205c4001c00800c0d40c645403141c102e8075050766515078030b0b03501d0900900140030107940c0c1d00c00508403400b0407442042e200010700060041004018800c0024410000b4003145240007160042c220341e69111035140c010010005800760f0400240d00845030703a11801d0015800703005000242a59045078207080070f8a00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 526111636 1250 526110386 526110397
    0x80d0503070c080c16150e06030a05061807051e0703090b0a030f0f050405281e02032b0f090311040b090a1b08040f0f0c2102040606020c15 61
    0x2101a4204092208000c0405c0306600d00d03118941c0e2203249034a010500d4401d408520a05001d228800d2a000413035a00c041c216580314181500c0014103440e036501264045480d6501140380c2010760050000550b044030181020401051215154043d0204004420b001d1460000d010848201e018858400b0480240441d003165141c00122034210180c00c506071fa20180b07096448682d07503018401442024011540a80e00150840b5a0007201402401021038441c002600e05070b83e54030603400c1480d1402c006c2d03401c05d800904542c4081404c02c81c010480101c004c4164030b49103040700c843c40712b6000b50420920354507241c0740c242e54285503444a07580725060900061f80326a0340e11039401c9568882900b81e000c0c07840c5030703c0090324840140f04540303031242e844105e0702807200c410704000c002041401a0349a050740f200801040400d946401c0c9946c80d0300f5041800030000601d42400e001440b00d041c40d0405008807000d000c0c80d5603803034080c1c1c0c403581da00081c10b400c4145102082d030803501034401001d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 526112886 1250 526111636 526111643
    0x60912060c050c0304030c1d01121b050d1101171e0c040305010924060b0412020f03011d0606100e10020c09100905090d08010504090312090503090a080d0503070c 71
    0x1032038104070000450440c5d100d41c000301c2d40d001d40380380c09220824032084010305d44071010b8810103183d41031480340c0c0d828010032a0001c0040c038454000b0b5100500304148a40105806040490f04090b20f140c0b40803c1ea2130800b0807400a45528210500d130f51000303410030301605c450810140d4840311903160000e035600082880a5202c41080b000000403003d100d1401954003c89201074030310560014034807240f00c0c0c400428080c600b4110f051250740544001c88013103681048003c42c00c0045440400c4058185c001180e42c15440c10b00840e1142184c02840c1c218040310134150303217450303603030b20100400b10041340f0f26000040d813030320004003090410300540400800d031070046a4052a11000007031a81e03400700c41c051009003060604100105035030242c2da030402c60000281c40311041d03c28004112690501c2030f0391065458452071010706000740003905c914400c09409000c00c1c41a820842c1c1d6070b501400c4a9400b4252510f030000724007002282020040d1400da56452460300c48400880e91302d01409030a4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 526114136 1250 526112886 526112897
    0x150402060a0f140301032a030825021503010510080c09150403050601030c06140903100510090e0618150115031e06090f0209030712050a080a0216060912060c 69
    0xd43c818030007400658000c5200b0403401842024420300111078022200d640c0340000d1030382c041400040c1c03556055402d0300d407005000c02c42e04402e5005981d000c1c1c401000c06500140b0160710900d00142c13210017107058801c10b8504101d10f44520204641c09902192905009007043c000020395181c60061124ac105600503a00e05158603601c545d41081e00a074021100e00c0e808000c03c10800340c00c5401c03c1c1901c0d4000030036508060380300001c207403034540000d04050010343d10b200242c411500c04c0c6c40e4a024000351001081000499107045543d1041a207a10b0840c0d0550724510040700d00c006032082d0ba004100700c0045c000c3c0d280074000c050202d0b00c040301000781a1100c0200406145d007000c110701e112a8441e01080040c075084560085514a1001c84203141c010030001a030390301e0010325031080703d00000105d095000f450400d141041f0710b00c20000c3c441040000c1c038036801c036400154904200300078443c2c200025601c0c1c0f0306682105841c0f0890b0208000c05001801041e4650300c401864001030804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 526115386 1250 526114136 526114157
    0x1f17010e0d0507051507080430050304050606040603020d0308040609020409110a05151803160609030b060d03080a0e01060f12063917010b0408150402060a0f 69
    0x4a051480c1000c1070400108003140500900404101c0b560480101c02c40000d03840c1042d0100034800350008101806511100e40b8201842d090a180749102c1551001c00103590207031060000c0c0141c0c020b603025209072244038085601868980300b078030201ea03030003801a110036095a40507210241c0c001c00a403080d50703036180d82601584580c00307120f9201c1d12680303642411082000401c115100c10f0b82205000f41070390040ca580226400d400c490080d0308a154400702070075000e001a00d00707042400c0b1000d00308441300b400144280c0051b21002aa803046182c0c440d41ea45060a10400440310399001d40000d41e0703880482d045101c035510030100c0b401d0020001c5001501c6d413100c11024100f0758001e08404110115020501c03a092054003c00300c07443c00650342c5d103c125810100010031034500d03100d0014040307010054060043c404800e2450700f180b440c5059682da082c4e500c42580203031040440d00d0090484901155200b0300030184141d43c0145482d0030403074032240803500784000404040520071794010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 526116636 1250 526115386 526115411
    0x30f0503040915170a12031805030706021b030c030d0b010e09091e010b0a03020f130f05040309060519120f020d050603010e0a030e0d032f061f1701 65
    0x40f080d480180603e4070703810030f00c2e00c3c80500381d10300c1501d590071498000d00d00c2c0d100020390820210f0484041894003003404030225081115000c6030410082c5a480005600010844981c02802c000003c10b03220784020120402140d44074401c0d40141c8005803c1007241440300c070010b40c000013070740030185440d4959601c07440c041040340d4020343c3c0d02901a030104000e18100c0350032012a05503803c0e104001c0c008114804042100c80005000c004e20402140c03040c40519211002420072030321100c2814810070548040070401407000ba0303020707000644a40e50104001c0d00650803200000b00c107080016003189110341c01c4500700c001019200d056a1a042d40000c0f034190782c009042c00000b0400c002849052410800d03085550004004100c2d4000c0116500441c0c1c00c17101602690b070003510301c03000c03022181c901121031444140514000b10f11914a9003144030280b0911083d19048608495085e05c81041801c0805c24080345800e10307203015481800b103480e04a260301c03201c0c04071500104400d030100704c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 526117886 1250 526116636 526116641
    0xe07030e0a140706090b09060904090c060f0f26070909142401200a02090906040c0602030f0d021e120f071b030522060203070501050a0213030f05030409 67
    0x241070780c0400e408211125500410f200a00050610741400da1280c3c1c070300302201c445401a418910320518005c28542819202d5401c680c2c0d4299014140740d601c1501c598002d020701003c078400d14000b41034411202440c5009a4903140101038400d40a80c1c1f150701000031105c0388000030f021508000d5002d82c0040d217580e4502602040d6280f1942c0070446141080701300300810070000a6404140300c4000324440346c1d800401d03603604843d0014a0501c501800f4503183c0c600200030700000d4103c03201001304041c400002c04e105019910501c0c186010990301d0604030390341e002d1904040250b070001c101b03030605141254010f0801da1403280c08010f802d2801c00b801c6107a50040d89203c0e0607040180c0400a051040b5000d09a00201c2401d000711400210380741c103100f0149011006051020000f8a01c1540f18142e05424600d25040c40240b03c1e103840340743c004c0d00c80d0403152080316590708003404901a170900e4000d0741c043d0b940340401c800c82035240d5210070342440080d00d4261060b0008101c0441c0c113180c00e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 526119136 1250 526117886 526117903
    0x30f0303090c0906060708070f060b0d060204090b0409050601060e120105010b0a110f0a030c08070b071e030b13110f2b090213230405070e130c0e07030e 67
    0x49002d8000b901203203041c40007901c070003401d691143d2810001030000074134240a0b41d00705a044203914036034101c94500b07171000f8200500c0e1158040044400311040014507002001603408103c4c1c140710b0244a0028030080c1c40ac500b500400c181c220200610285109282140380d062009080401d83d1004448440c212442a000200c8816000540c0200241c011811f6243c07038060a00600010914103851900c480c83c1e244d00404000740b101c196814000201c043c0c50303d03950009903d40706802c050340094120560307100035030140c40800b03916003103150184c071171030b0a5044042c1c102e4a4009804d030181c40100f0301c0c00e8040349441402e2004d06092010340000c0e028410a440482c0c02c0312145200100808207901203181c4a94148248440142c660000c03600d241c0421140200c2c1c00070b03c0c0202d084039007204520901e010082c0c80700700410300c103002030224215690748070040c81c2525030240700d09121140f000050204507500c070080107141039408055601150383e1400240700000d0141803070800c3c030803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 526120386 1250 526119136 526119151
    0x2070b13110306010f0e0408250c050f06040302040c2304060914010518120d0c0b010603050402090c0a03200703021c020c0d021305040f050c06130e06030f0303 70
    0x800084040145200c00c40754000021802800c0d0384d031409152408020960040b04120400c2a0105040000d49410f41c2c240c040860030a04c01003d1491a0210314081044c050ba6494001c45000889040c0085803110581000d488d16241c98110340900c806001400408010000e078004000e60a0340303e000059640341d41141266074652500c64024030418454021424014940c026698035a070010b003241c6800800325a0301062842c6a40000c40c41c150400c40800540581603141d40c10607840008410214450307440d010240c0d80b5042e084080700e40032600207400c081d160300032850810f0310700050180f0807820300d400b080c1d02c0302c000075200254446040894020390041088800c05805102d50329800303200c03400c02030300c044410b04000d60351641d100e0124080c4400418450642d00c1d04141070054181a840c2800541018600310280c01510318042d94a0301407603001e02103502e001c404840800b124055a52411810a80220038200c4094021641481610111241c401d01071020754818001e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 526121636 1250 526120386 526120411
    0x8090a030609140d1701030210090f090f110408191401020f0702030f1f150e0907030203121c382b140a050111030a110c0a060c0302070b 60
    0x5070900a2130158044141c00034407070f0b030102284401080c0c0c1140c81c1142c1c0c04603480c00405009100c00c1c0c0c0c40f103007550040d14008040d2a00485c510109400642d003924000004000111000800d01150b000300e029000c01c940100e00d009030307400d100005c4002c00a01480440c0440c41c0401105400c9034880300e80c8044201e00866200190301c0d06001001c0d892503100090040003289600b0210100d000b440403103082980c3c2c403c902600d0b041207191801500c860010312409040c2060259500d445911040703210748152044c00107190054016601c4a084188080c0310480c0403a02c04005030807002c20041c8903e48500104880c482d140030085201d0000031030300440000c004040c4074a610100c0341009014504251111a41224141141245030405514100c02180d0048981004500040035240750b08007003404d03143c0d494040085008003a004401c1004682e44403a510090050b0000e200a5400c1400f600002c03412a8201c0c8484680d10302e0018908003079599202101a802d4481480148 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 526122886 1250 526121636 526121663
    0xc09042414090c0901050405150a0b0706150e0105060a03020f070606030b011a161a0703050915060102100b0a09020c06150d0507140102030f12100f06020a08090a030609 74
    0x607045a40c6035004501040944581070350a40898000c1c4010b00c40d2070b0145940300000346281032481000708002a000700014030459554290500a4202c00015605280340c0707583c22101c100d001169000700c0b804043c228101d03038030b42001c205941e04810103030320905808203d41e94074124408002c0c9900c52241c0d00020310141103081ca01019441600080b00b803180d880300e04410b13840c841013500c10039008480074148110661a0031055172071050016041d02820009110649070150003851152860b001180d07510b4180340d940903001007046d218240541c12030061481e0201880e048034003140e40141102440a9541c0100c1049901c0798a103141590021702c03d024403030841101c00c1407440021250849103250644616880361103034030960b10425404901340394580d00900c10f5814045d04c080344682c0342c00e80e1780114900e2000440f8140040749a41e900030485101c00000c0101f641e902d82d0081c02007105990381c40b4035641c402010540c0c4030222060020005009000f62100c441c8184941c10b1080d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 526124136 1250 526122886 526122911
    0x1140d0903030f020408122d07030f0c0804180e030c01090204140105060301051e041a040c0f140c0118050c090c03040f080d020903010c0f09050102060103050c090424 73
    0x440c1103034090f0b224103004000400010701c0c000b034107103401081504400d80e0740c0100941c1c902c20548132880b80071000344505104440d01592009080407501980724500d00402040c0222104030703104d400107010140a110a002c489180f8450350079404200c0300010b110344043e20614a9030300a030301c5035106691504e00003811828a4051010211011a004035155050a0000e0802c0c04140a00340c020803900442034a101d40009a900702c0410280080052010109003815406010b2407502e0046080456508110344640d0040000d180c00b0754410141c031407070b42403502060340482a02d4150b1340d215800c0c4050740000d40305454100b0311800c000c0110701141d0003400b0070050000c11480f00704e0018802c010105851521818809611603000caa445203151003900c000d02491440c641c01d58070b00400001c074590000080c48030300703c01ea280c444603250380b0001240da4072400d0000410a4000b4440e070380c198101294141d400c507100341c0c04004860000c4010030018528148e800039020348807008035902 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 526125386 1250 526124136 526124141
    0xc080706020c0f06090307030606230906100320030f011a0c0a0206030a18110918030d1a030d02061603020405010f0f032319181101140d090303 63
    0x2800c160025060120b80500018890003c102c10180214000900726840740d03414005540919400340080200ea61944c0341d1241e0b04040e0003c02c81c2e80c3c9030540d510f401d1480e000000b5482040010000c2e81801c085810131800b03043e101c8105000149188190a412078101c80514440c100041c05c08900b585490200025801e007031039000041c0c4010010303440c03007540104552040075019103645a99850703814058000380401c8000700cd1400441e4069000c2200700c1500a5401c6421150b03800d0076124103a030402207100b6011280c15607801040019240025504004200740d415080900314401d100e0100b400c02102c501001c006811140800101103080c45029a80031040c0c60f046042504010002c4c0200301c004901d03105001004c0b6402880520903001032051400040b83d1201400400000c07451120007500d42c041120404071264070303408054410700d091611502d284a0b031496075516090140d1140f000c103141081101000b03c0dc034020800000c03c84003191400010f08a02c00741002801c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 526126636 1250 526125386 526125389
    0xf02030a1407020d08040309050d05031905091309060e060c0c0105011202090c130317040f0e040503070201051c140115030501031502090a0f08010506090a020702010914040213030c0807 81
    0x4407444507400e000800394001016602e010307150420141030b0300c1e24103040d40c101c1e03615405a94031420341c40112040207070101c05040042c20191014420700792141c41a80c460041008a5401c95100c0c1381d042c00d4200380d600402030582c0038080010340c00600307104142c14210119240b03000c0100016560841c10000d2155500403ca902540403000c1c1203a8005840c02c407002d04181c2d60000d021a44040800c007009190740151740c8042e0300c0c90b8581c0e0024204400d608148500d406000c049080060f00c09241e659086c030848c0d114000e9450082203600540c0c440c2c1180c0b80380f041e0362020015620707401405220311140504040c450041035031400f400e035041401e003041450209070514004000281d0b4902100d001c02d1a188000368488080788041a80200c003980b00394154040c2c8403002402e041c040d40020b0040200781c400d442c03690340d0810028140d01c14446c00a00085a400b010440b41d002c18110244038400200003501d801080d05144040d03805075041500c0540f484c850801941c0300400c409030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 526127886 1250 526126636 526126661
    0x12020306010815070e0f0a0806100603090221030d05010803030f070203120601030507050702040912030b150301140402040305010c091502071d090703080a0e1008280e010f02030a 78
    0x3c9000c80250001a00c118090000c50a210128207824a65038507407483d00c9140e04003404200c102d40c1e40d11034041c0d480f02e0580b000290f01004070790205665201c1d002d81ca0070560060008860090f41c0280042c202404501c1c2c050f0500080c4a100340e050b0040c040c00e030091010300c008503100c2c104850ba01510040185c044802d40d8410000d0034030a5088a6800f94441030900b00040e21360b0320848151920710035000001d5006250004c80005c0001c0c0c803426061682c0c00740d9042203584108000d100c1050948550100c5d40031052004200c4a198010200441d01000e00050300305030342d90742d5403030a440e04003804202060001c1e006202104120b60300301103044030303480200590b074a001c0880d52580c10180e118071546a1030000600e04440410001c4d0056030700a03005991220981401003140c0815041c20344613008060304120694417403207010340070725484030041e0600c021540c8600c0d070100510001c4c400300e545035903801240c0ba0081c800c02025032080030000da03132480d007044040100c44105d10700c034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 526129136 1250 526127886 526127893
    0x1090606031b081503190302031201060c03050f0310150c1709130b0607210206010b031006050913050a021e0c1507091203090302030f010e0607050f04090501120203060108 75
    0x450090b8048181504401c131030103004d803c1207400d0081390070441c000d4031112024101c1090f144c10554000000c100300c240d10285074206903280c004c115050b58584401500140d400d00001e000500c2840045402c000c4440400310040d6075007031901c0e5068000c1e15540b000c214111110800d00c0514081c0c00703070b00d2014140f16481c040000000440e0300d90040f03100742400da5a0700d554056038032407604941580da04000091030a1100c80309235880c0c0410205944018083e20000065000c2c43c04141c1c0c2c0100c000c241c2e5006401c0c18010203d03019042210005c0d03010520003510300841d41d1921034107010301c2916401582c2c0d0034282700c0071481c00d4889481900600340030040f80e51340b084041550360403480e064a50b0500c9445491040365019025007080c0315042e04030000c1d104040e0040b140208a0707109038103076442c40381c2d82710341c044c201c0340c0091001d0035982143c80011401d604c00c00081001c8442000302c0e40c10540c8440541040b5903090300440344044150b00500d040d071400304101401405040e004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 526130386 1250 526129136 526129181
    0x631060c2709021804050a05040309080a08090409052b0212160206070f1a040b0903070f020f040608010e060a15080307020103270f061d06010b030a140109060603 71
    0x4084407199a446000b040c607601040403e44400c004000c1d58810074014002c1c41141050301c01c250090500f03036000c60104510b4240012100310114440301c0043d001050a0304261000d400d12000c0d104840b0220b41c540a0f1115120400807144e90602400400c0d1034510000c8990b10f030080e1804800c0c091110011600f4000102c080c3c20100c01556034507416950103403207202034a00045028803928000703000d9071a00010780c041003460140780340324a02500c0c4046c42d945a60344065202e110b1964054614116981c0c0780f40035040210a049a894000d03000040700c96a5601007421141044009252500000c042c800f400c00c881c02203800207485503c0a507c4185040203265803489449070081c10b05490b00e141070300f90f0903402224001d80c4000002010f0b40b0089141015541c0f00b0310300100da0752450805540da2103c0700c070a11000802d41c81d00100f805908115400c0d501d908014004040f80c3d8031403805280032003140c07944500a1010313040c00305030340d41400409003d40f442c4c403401c060403400c02d816 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 526131636 1250 526130386 526130447
    0x2040e0312010b0a03060503120306040605060c0d030903122307140d09030e04020f1308010e0a02010e04090609050d081b09101e120e0105090631060c 66
    0x201c0e541102c5281c42d420340d6407440c001042d80075191079403107240d0500900008480300f0220b00d00442c40780008490400c01d85407500304200d40c1e8002c8103c103084070740c0b12240c1030110702e01940c01036402a000e8103001344006070b075040303c07000e03141009603150000400201220075141801070842c0c0121207420f150610142180c0d000000e801061311103150242c403840403100303150044c00c0005038004003030801c1d5a42d1108202503451544103800d45407000000b00000180c0302e0040c40364840d5845c00f040a882e10f588941c004541c650054514294800e607035040000005100c3d22070203903818456005000343c020b8904028000480c01040400c01aa15007918100d40782c0c40401c442040c00111034481c00d5409d6000100c54005034807512003c41800040c01c45010350b0071229880490b40452405d01503001000d40550a0340d070700ba078070512640c1c00080807500b0a104505004412032503103403800800c0702180d87e0030440820010090b14099904c94102000d241d00c908044648203619045000e00000b0a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 526132886 1250 526131636 526131667
    0x504052d0603060426070b060108090c0102030d02090a080a03080915010303020a080c01150603050105031e210f1c0515030a14011d0c180708010902030606040b030a060302040e03 78
    0x604c020001640c8901103013001040320140d4102d1200001c0443e16550540390140c1e105405556441c04500440000745030386c0d03c00150f040d69a103040e4081d508140302e006283c40030f5005000d456a00440004000c900c0c02000c00c10040c2c054020b98554001d800c10b00a101c2c10040e1803540700094000700c900520209400084958296621100f07040c0d0b02d03202d055100c1d005091003401d4011441c049107001823010382c0360f009036050741c0045098a4a920080c00b8144c40780c4504080090b00ba00503100c0642220703100854001202c1918043c14075021003e4040d2510f03078000303188980ca117803103000c41c1903513024a403042a074440300070590030302030480e203200207036442d1041d10b0001c1607051001240100f46100390803950089010700c00c40e0305881441030007191600b41c88841e490085a100c0360360207903205006401401481551103180e0710b83d003445146806584010840c0c0d030004020040018000402c6004610580124100086107402d600c10070080e03d4400040c0c1600d0b0b4000d10440c02100e0707100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 526134136 1250 526132886 526132891
    0x60f0a180e04030c06021909080706020307032309090a02040905010e15040507050c0f0f151b0703031b08040b0c091e0a050d03020703031106010614130504052d060306 73
    0x141091325000c0c0180c6000d0001e446012103031030404d42c00c016803030a9190030000c0c10065507265400ea9070150b45818089030740c0c0c0903003000500083d56840c0c0382d140300800a100c501008403030b00700ca2440c0c81410004604021070959032409000c0d800101003160001522946e400350004042c08619400c1001d0460f40d000c0c1c41e0070f495440784d543c400114008600541c104d480c202030440944a2440f0140182030300c4101c5840110300e0f900600790b14610b1404402d01e014450301c90402c80440f000c201070410080d540146608505141c0d540d031080da05c0c1c080c0c0812000c154002c950303600f81c051034503103845400002d000d81a8021440f047c03181c5241c2e44d4403d02030b56aa41c480701441c00c102c00c450800140301c0031581d440310b600070f080442004140741c1d01040110980c2e001b502c403503000d00390315012555202401d1250304000382c001403024100d910020f00512420700c488150720f591035103580001d42164801d0b141036903c95241c0d545075203504034a860010308240310550703201d0b0910701400801d0316030500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 526135386 1250 526134136 526134143
    0xa090e060a0801050106051b0a0c0e0c0705030f2203021c02041509090218070f120f0501060306090608010b0a1502030c0f0c0103050105220e030405060f0a180e04 71
    0x1a000003a5292500715080004003542030080c00740d540c0d50500580f09600107040f6038070040d10f925404c6003058001851241c00741e4010480142c1610780103605401c200042c08040094400300501c10200748100045d0000600020f00c155541980018108503100100e048050840b400700d410009aa0b900c80c0b1400031141d8024410f101080c1e52000030010075005240d0000700010074404a4002c2445d403006281505c2680d01d2145c05036042e1503403100d51800c0b00c1d55030001d82c07041c0211302243d10400d159201c04000040105102c2c8080030345030705858098009600080d0398900402c03250045009450090995078002c00080341400e000c51030b600002c0c0038445052507005121680d4a100300f044410501c0d1a006885a40940d0030342d584d01e0356a1082081d00081c1801c00129841c60000c00400c68520f103c4602d1480040b5071f5403d03009440340741045003080c0001e1200150603103e01005241d100481400c05507914000c12029007420480314035a1040d8030403001c10b0101c110b0000105801980 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 526136636 1250 526135386 526135409
    0x720010c051c09050301060e072d0516020418020316260f030703050c060a050c091e03030705031201060503040201091404061205010b18100302190503030408030d0b060a09 75
    0x201802c0607900d00010b03a1082d9007640c40c001e400101c00f07880054840c0214010303078500c1c8400d05800c241ca00451910a006591041c00d0038061090f80d025900502c07180307407860302c0c2c0c5801ca2010703000142196002d030072014440b556241140114501030241c881200d204003480f00b4600c0c00c00c0d003005403070510045003643e4641c184030025110041000b9181c020450001120b90341c10003840d0007000c81d00486030b09038480c81014041580c880c03a90040500c00c039085d1001c10b04090040c0c2c00c0000351016210a5580d013841d01d40d94908a403414001025601d0060300250b6445101108041008005074000c00c01c01005106020051b0790000701c5108568142500300d2000d0f0303042c80010300422083d030107001d030090072034480030030000d06400c1090719600480340e003003180401103083e80c2d40344c5080721941800101e180c018401840c0c1f401c82e801503070640c1540102459203400100f0f1656206400a0259900c04103000403004010b000350303822000e056880c241490307008500500b0400c01f9009500302c004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 526137886 1250 526136636 526136683
    0x10b0126091204120c05011407230d0e010e09060a0e0705040b040609060314010311060f190804052e1a030a380a050402011101020720010c05 62
    0x300708010701d1200c981a507190320b960700e58407040c407203480780510000c036445148035030001519802030701d0180c080515245541d141c00269611403c2410445481c0e4951400c4443d018050603000c02034401181d0190f1161148114490005050088c03042001c034800d00c0c0c1c401c20044240c0355a940b080071900d1140c80741d0030640f01c00c4d5043d00c40f4080c540240100c0c07200890001205507202030400f0403110300e52020131144c442c00d1840c641552090201810f40480c0300ca0001b01c6003803240050924403100c040450803c0d240c0b001d14885910b43d501c0520000d01c0c158240818041c09000503040c01840c2d144800d4640045090007107072495151101a50540c0d403170124440410f6410665001c41d4006c0c192840c4045901c0e01d00c0d0401000511646103500c0000c044800381000d10300a407a601601d0044c801680e62071030704001034070700280101d0400048941400c0d12030000d002504841d1302ca41c00d612654003903008909c407517403070585d5064100031040c00d004001c5140400d0808103014002d12402c1c000307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 526139136 1250 526137886 526137901
    0xc0a060c050a0611090907020309032d01090c0f0b03070e01081302090412081b0910140c0604020f0d0809040b030c0a06030f1b080703180609060509010b0126 69
    0x10402e40350180001c1e0074003d014203552100c0c0001c005040301100d016207161600c1a08903900e01030344001c00c1d090307440401720700503604040d180059000c4901c148041c407846e002d2565800c0d90a4000101e44890300c080d410b00030f0b400701100d404040c080c0b0550705070542c07814a0700200000e0160b00b0041c14004650081005c0b140c40702a100680c1f60080c1c02425642080d15082021001c030700003660008400f1b4000c98a2081030515226074aa000e28200f400c0100c52000c000d090b040e240c090388188903c400003407a17490310481c0546200d07184080a080540380c00c0c01480303611a8050340c2d452042015102e80d5002038004420340e424110300303503030005182400202007890508100e140662041207d07100003166030f49500800d61482103c0c20521401c2d03508000000124018003030340000c00d4240000509091007503000085200014a0251403c02c007915588100e81030b141098030556214810004010001d000702e0001d184203180c404002030b10f00d00c1403170034804000c4c0e4442054048201007600f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 526140386 1250 526139136 526139143
    0x6090b01080f0c0f0f1b0609030a03231303030e0604020120070b0c0a0201090b0c071503200403200916030b04020c011e15050402091908060709080c0a060c05 69
    0x140780c3c412500345c0c1c0e40c104c0c04007071241075005580101000d00588145100d22480490102c2c0100c191a0045003040c0450009034050103601003501186025000e840130603c007075428080c000c046212681600c1c00c414240201600e148001010550f07105605000040c0d078800c5140b490b40a80d1410f004401c8071150045007042815400f04640030404110810f400c48040744c680f19251013600d40d00c00303556880c4088040c900419122814981112004010440d046a0f10340e0b8061050719001400d008a01e0b804e045030b007100c07001c2c0c5080e800040f5003401007201d4803042c1d07414020802c5019100c00c014200050b81201e00400201d02a25110100e4612a000350070604d03e05a004209548074954049918020070030700039520081200c2104400100350988503032000c24010303501c110300303c0c2c1c1000d062001035071041321426001407604188000b00c41c480085680649403078405800c1600f008840140311207140e4105010a8110a04c8403805603030302105401215914141402d010441e0b00f0410305 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 526141636 1250 526140386 526140397
    0x7090e030c010c090801151505090a08060c0403170c0a171605010c020d0f05041e05130c0206060105040b09090402041506050306010311090306040b06041b030203090106090b01080f0c 80
    0x141c0e90700740955503448a400c1503902060b941c903c0300800064a41101c2100c0c141c5044c030408210a000d00b8505a102d0300c81c40083c000c510019002800350780c1e513911201e24116080340c0d04105400c000c98140200140481404c46040c45850054280003141c143c031500e030444008000e15490880000b45640b50381c41c070603100b200700c0211552100a656003041d07030103403c6a6014000601038210412810f170300800106280c61090f0f80c42c0e42c201801d00c101c00541c043c3ca0392854100c0c20300d503400000e0a41d2885030b00a01280020ba000c105a00040d2000e4a0101c01038584c50600400344170a2040315882ca0941d400c0c00fa08541000990300c69002013002441e444000c0c02010b1080500446e81c140c100c4000c0d130155a00380e0b4100b0120703c1040c0040640d0040c2410107034107030055004200411010180b00fa0884d1009100144031024440891003000c1140d48030804241c0110800410341405c2c85603e0050071034410502a103660a40000c154600082007011600340c076030701081c149001c0c04207444 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 526142886 1250 526141636 526141657
    0x60e0409060b220507090e160c020409031e020c13051003080408071e050619021501121407030b160210090f06180b0105100c0b18060c03060307090e03 66
    0x405002012402240d08103d140702409410320012504052203400c0802c01c4a0460301005400c2c5c860010401c1138400c00300c801e1003001004a050b00150750345100318a41c0520984441040603483da04e400075120515401800355084001010415100c80c180b04641007044d04000429965080f00c0c5004602c80703402c0034242d140041004100f00800061034000d40c0e02e038441010340d5800c0803841c00707004c2125000322038004500b400081c1d01000e4274001c41c2d0143c01280191104010300380120000000c090b844401c2c5032001110820a018000f4107030b98880c00c840e4044d00754241141c441c030380c90000291510100c0c0c0d03405444405000d1080c040d41000b00d01c203c2060000c0d000a04200c03201c401e80c0901030322150314100300b18140501014196045651016118290341c0ca040c040086c02120741182030113000707078451034100140c0001901485100d0125040000c80f0000c0141840c04200030300c030320726080041051009541d000a450b800710340072000f0100304084d0f121540384c01c40c0110003100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 526144136 1250 526142886 526142899
    0x41b02060c091f051b0a02100c0302031b0102031503010e03041a0d0501090c030f02090d0305090a0b0309070e16090515041d0712060506120a141305100501060e0409060b 74
    0x8003a030362042c0104401710b0100f4540841500380082c90b81c4540a421009601c1021000340243e420300a000c0407400902030300513282400e40d45103a85034004130b900d0b0101c10f240d6001080086403548503003202d200c40410343c020401035142c1120030399207100381d0054014407202c0c4e1400b10102d64400381182d04000e540c10090006517902c042c0e1101400c160802c0c1c601107801d2003046004a0118800e44224510040841d0507401a03900c00392055449460201d400003420103022903800000c0f4005c40c01104146c004108445c84c0074100b6103101005132079a19100f107002c14080e540742d480480441030b6541201d81e480341d100e6000d07070720b0364030b110b1030b030220b105081b0070065115500082c0c08aa489041951100c0811048415031401110403e00800b42d1024050020030034005164030321690010b126140000d201007896080b40c00000c0c221903e03619000490b14540c02c2103014030480404041001c014801541412400f41031101c0f5a880389011302d5840c91000140700071a001146403141c042c3c0340 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 526145386 1250 526144136 526144189
    0x903030c031315080f040314040506070b0604110f0f030a140403020d14030c1b01021b070911092b0c060504050a0e01060918060b12010302041b02060c09 67
    0x42d000d049070070303208403007403c2e1800c07041c000c07450302900c0210311811004241007600e0303407250f030240d9204e62034132a0002d80d08014080801c45851303c0e0014250280148001202c2d840e012003040283d84d41e1184407145010306200149003e520f500503100c21545d1650826203a9132000c55001c000e1801d115890507031076040060009040d004104101908419a20148207003804854001144815218640d0f0804208000d06075040c0c5034000305c909941c0240054642800765088400740030508c09031920341d8000000c1080a45270030300c03510010441748400203042000b2040000e00d0403200c803024415005d900150003511a0070b8a90300300718594441c8911841a03101d003001025608203001d42030091000d4400891110310b00c0580c58100e43e15951001c1a050a00d805080ba010002d07400000590b100d15001c21025044800b40500002481d4807140940c0b540c010441078810446d148002900903c41003007180354003145071030340803001100c026501e4a005011505050300b80c61084080e0076100e01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 526146636 1250 526145386 526145407
    0x306050105040b3309030a0302060907140303090d03121a040b03071a0913060e040314070c0519090608030706050601081302130209060c0d0f0e090105060903030c03 72
    0x4058141c44040d0b4041012000010502c00d0121101c201c1400040e007001d1400202054070451180030b88910f8403084c10070b164030300403078501503005d0011005a00460204501c00c0000c0000320010201084100c07210184030011a4503403041d000c032140a0650b2400369000d2501455443c0c0840b141044200a10000c41e40103c0c080c03032640d05c441d40f28a00b041000c0000d4600002c4580a68010000c10000c16440c0d4800140790340c440580a81c000c08507050510080106116101c000c10303154103c1201c0d480c2038580182184a0320b28103d130070000034030440c004210301c114090256803065a190443c07007070a8861082191480d442050500e04100c00031400e00c0c404000f41c03007600c0c4aa0000e12464031404019590140304480034000304070607144000151500c68078144001d00400401407400f2131030f50100b4090f501011a10102c0d600a4254035402d5500c142c00880b01000361400f10340540100c4005441030006220f4079100e44004101a11156800d008072044045030004a1b96581c1d05840b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 526147886 1250 526146636 526146641
    0x61206060f050f0f0904020f1e09010b0a0e0d1103031611040c140304081b2518020d150f0f0803120705031305100905100b010c14010b09010306 63
    0x1038201c001214000c00149400e1001c00c03030803d5503004002c4202d0107184424442c403644010000c0c0e80c002c3c500d4071016001e40315030000a00310710b01860340c540300900740c0c1c0a102c003823001a80190003141302008203259055002107030510707890046440490185050806e6000d845a0111540e8980030008200001c0501c40111016040c4100040b010b5501ea0030308010448404034802d00209041e02e0b0594180070388180215032007441158002e0810b100c4c0528601560405413480b001c580c4050903001c8019881c444103141286194000c26406040c0200d4001520328505c203031441c40c0c3c0110340e0408480e016045282104c000044003e152580c508a001065840e44644612881c40c0c04c008121303404040f04941840c07500010700c250b103444006049545500c001d00095850442100c4903000a0302030000d240800b00e117810110341d50103a410f2850425426040c01c92042d490010503203040d0340c001003000c141030f800c0301d44c5c200c548040c00c8055014010841182e5800801100040100207140c4d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 526149136 1250 526147886 526147889
    0x90304060e03070608040312110f0d0b0909071401020f0f03070c0806010509060d0204022b23040305030408041212080109290f13090501051f0311010306120606 70
    0x2940c070074044280301000e15481d14800d00807080090045000140403078010a030b0080400410400080d8803510303046c0160b89a084402c0080803d1030014807900c21615034001c8203200d4404031540c88440c00c2c102005681d694151060040d90b6031400400185607002707014032041c1d40710302c005461303424110700d60480d01d07a071110034100c540154030b00380410400c0000078614140c41700074004008685a1404002c10101000d5007244d010340c08002c1100050002e25007031081c0926a400c070001100b000e500f035800d4415400c2800a584252400d88174a4810780c0c081c5074000d601802c02c2540d980700c0d4144101d5501ca0f0307800100100e40320107912000c200c1550102c81e20f44200780c0d103100e0035980b506811425101d0000090300f16040408200103903a85810103c40e04000080c0103040c0c1c0386041c0302260725440c11000101c1d0181d070725442e00040c85000e0141591080c411080d41070414403100144001840c280009040744440c0b803050704644c0d000b0b07403060740900071500b29030341c0820551401c103006e003005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 526150386 1250 526149136 526149149
    0xc12010e0303090105040b180706080415020a030f0605040e030f0306040b0d05030d0c0302030f04120306050301090303051e070c15060509131703060f0105030c09061317060606030703050601090806090304 89
    0x1311000620550351048c6607607121404480035012042c0b070030b0401c4a06a201900603103440682c0624206070b4110792006042510781c544004c00c00401003803455007168000d0340080d00941c206000d941550101004560312a4400551661252500c9012030001c0c01a1010b154110034440d0740c80c41807000002c041c140021000c4002d002d030300446c0b0012016800182c403040d64810080c0d0100d00060103000384103070f40188520300018040c0e540c0c4000790a42d644030a00b580400d60b0345041c007440b0803001001c0c251000b4810b1091016040c2024000c19007115a500901600700c18003008001445030b8100074000c1000400c49869814440595610b4400780c68040b18590003280c15049400241c0c4180c911486000380013500560718000150b80c554402007100071070a10421400c480c40c0e0b10311018100c490303558a04600759909045502401c02d007452a40321541d03210070b0410640b80c0c0c9010440e9840300507850007003000e868032401030b80e0015590f00321209a01580c0c0810001c514000f001c1c20807602e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 526151636 1250 526150386 526150403
    0x111804050d09050a030326010b070302070510080f0c120414010b091005040f0e2410120f051c020f010b060304081222030810170c12010e030309010504 66
    0x100c40d000c0c0c803440b516100c2c5981000b03020b0010004240503551042107020b03455a110000f240484c01b11040000c241c000c420070800103d030f84014154100b000301e01800041d07070051401d525116002e0852140200860781da9000c4800107412620340c4020b071411034401200042407402c1624117501c03454031070700700e5400d2580780c62075456051410016a9009881c036544004445040409200c082c050f51400c0700d1503143c0341c28402150500030000c01c80201020748500018030b02c940078200c426500900b420050460110f020300c128a60754240b1402a5800650f0482c405528500241880006001d2311024070003403441042c1140c01045039400600205c00811440c800b600c03c100316404192805071010509204c9002102048403e41d6042400c030b602980101c9050102450903641a40045000846410031b000301c1c100e00c02c00d45800740c003069114041c241d0a0b282480d070754008814400748036103a4103c9017428040300303501000040d2845001e89aa91030842c2509010300400d039811542c008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 526152886 1250 526151636 526151653
    0x9061721131a07030828020306060c120307090f0602030409150302040c09170712060b010c0209040303060f090e0307031404230f03060603061f0b0403030f020105060102011104060c11180405 83
    0x140800e441c6c03040742040c650b00c070a07203901d2191000020740000349081d40200041164003c1c09070100501c2600b00f04c46544540d80c2d02d400e05004200c038103203601a24a80710228008d22040e41c002c800ea4050b55901e00c1d00003103d000094a04140e83c6055102a401c40c2c54030804030304d075550110b0400c3c251422034840c90200080b04916035a950520701c1344440300c1146a0f5544005640c940144103420014074040c0740350801d079000900d641206440840100c1d0f03441d4420030081001080d105d00801c0481c1c1c04000110404500684070b00c00d10b10024104034060141903102c10503481524007400b180b07903c075210b501c0124980d00e80d540100a074107101d80061a0340303d0852030b000421700e20444000d009007080e515002141d0124207190443c2c210f9031360003c0d0004c01d1403006400548019030007546da069500c0b44030714002e0b0071100d01a0080c0d04690424075648424035104045804030380e00c9244c130b007802c10118141402c000c606407007074560104034a14600d04082e16220554000c41c09001942c1c0040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 526154136 1250 526152886 526152901
    0x6031208270c060c0106240f0807090b0a030617030405030c0d08040b0f040801021818010e0106200304060329090a02090f090109061721131a070308 65
    0x4500d40060a14540d10112803182c0398104580034080c2c034000d020000c61055103c10f428980505105180c500c1c5414159408031860b50000c021150351340c0714104890981450381c80100403d11178001c29900300400559201d40c1d1b4480e030f000341d0041802d481445004038002014644942c002d2142d50711910a0700350030302145c82c050100c13202007a44846003500d00351030301d0388003012500460410b0307400000278000003602e4482070000b0070200d5401c0c404641c149070118100500032304ca0a510045080200e80140401800721044034150780090030041c0031001d4444050050040c24040c100c028000400d002403995015000000c10482c0318091400e81c501c1c1c0b559030f14107400035040850380114070b100032854000041d401000000d50152a480c980020440401d011a01c2a8410b094481d80c0b400c0400410650051035402d120f024405019818007061840791140c0c444d1500c5000c440c0e00142c02c0c0380345840d5030141c00c005e044500d2944400100d0f603c00501c0785d0024170095000c60906400200071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 526155386 1250 526154136 526154191
    0x150c03020f09010e031614120c010c02121f02040806010b1c0b1503091b0f01050301050907050c0a0804060f09030510150807090501151b031206031208 66
    0x1078041d515100d41440848801101d03040104013125816014415503200301c4014041d402d00a4108424005680118842800001102c2030704071302c010b0304041d003135280b5603900a050441d4036404039a013488c0e28644000f20780c10302868601407400c41202d914000c24403005d0303801a000f01c038840c6043c2c031111780c0c2c3c1d103001941601c00e40f681ea4400c00004100c050403a1426400281c004030068041c0d036080c01ca4103101486640181e80d10246030303100701c00c00700f0b410384a115521852101650240d0703258401d400060321078003060054500c00e54032040040c0d0181c1c41001520b07841d011400860354418040d0422002a6100f401407800207500d4400c011300c040c2c0601c40391000c9a030b000000f8036200807195015402481c00080c841c005401c2b2601c00100074604114540141c854420001829450b0019002e02c20110225040c1440407840c40040c0c4025120000c10415415041103883c0c3c51080d01e5803801000c0c10b0700003c01d907061150511030b00329800810544518040c3c4e50400200c141c1022440f003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 526156636 1250 526155386 526155397
    0xc081203011509051e1003230406200d060e01030305030c1303050106061205060f060702120c0607140f0615010c0311061e0c030601120207110904150c0302 68
    0x80802080104044442d40c20103080401c2e06203441611039482d03100060180e203e40118500d070b4281c002c001d01182c0f030001224100c8448034101004840507480002400c104003124400700e0211600c00a014410141c1018551181c40340105840d8000244100d800707401140101010510303140011038000c3c1440030139810b0720381580b41c8500b10b41c0c811003010000d500039000740c8000e0340e00da540000001e109015032009090b290309c54000e8110ba08415000320b540c002d1000e40f141001400c500001d4a8010440e03045540540e000c2011003040c00302c892400800d01000c98200030001000300c14004450441c00301750f03040c1c0b42500caa5500c0b001126544106c140e5540150b400c0c01800c03005a50301132510214182d1081c2882004c0c00a81c1119908100c0202d49070000400d020410181c0d2141d0311b000d850b4024034541d5072909606041d40001d0100e1031200005c58440c1e40021003006206807011800c02c0403900400034451883c040c03415134854040c5c810000e50700c60401d51064641b501038001e60ba03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 526157886 1250 526156636 526156663
    0x1b15140901020a0c08031f091b0e060403060b0a031b0302090f04020108060906120304031401060501170103080a090b07150c0318020f0109030b0c0304200f150c07060206040c08 77
    0xa200d60480e04c1742c40b07440c6d00180009034060440000078603000d6410748000018140010001482664000b04186a41c103142090041205140000c0c09690700e540c1641c0540340c2041c40083e114900001048000c001130f00080c010703029840da0030080a031409d28420940344251002140d6840351111000030f07442c2520001e000c80c59100c00911130f400c2210f950390340303e040142009100c03034002c1855030541d4090303001a1402130250b0307c548900042401b960004040070b10740083d180b00d542c0fa0000100d8810f000003012200006400f1175503a01c1954044007404084100d5a5150f0291501403000041c00700084089410304410201660017841030f02424484030009450110a039401c00a0080000302c5890500c103070000003101240400c10114480c0800710031841d03490620307081051141422103941c1042c0841e904907820261555208204040c805503000d0f1048207985042c129103004042d05c1205622a605c0c2c002131b2241c1c009a028002c6000d07000c401030940d16403440503281c0d9030070108034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 526159136 1250 526157886 526157897
    0x70b03010e0a09030504120b01050307050d0c030b0910020a0f0909050c0d0b060d1401170304060923120c0f03070e07080c041e08010c110d1b15140901020a 68
    0xb00c4040c4543c03c00701c00e49109290040c40c007500c901400f500d03900d0354101a140d4a40450041c8181d040c00c00c00040540011140c041d00c11000d5a50100280d0785804001c050700144008510159800c2069100b88540168295100c0d0764204005146490700d0b80d2000000c2d04210f0002110603c500c20f45010710400c045051034807400d0407259001d404100d04803604400304001290140c03410784101d41c0c52003402c0d442c4541a51401e0b0300d0aa02680c220034180c0d094000300020080c941d000750007a4202d0f0070544c10000507030300032507003a40d104050840c400c0d04200040220071540e035000c00d00c041201021202040074011601c103142d520b540d40d0254211030300d019804210700c1805294911b40c8100e1044071546070a4540060f207142e8024014248a003241d206014000c111080c040c446c03c404503450301206980d414099140d90f024200220024065aa03101c40b03201c042d1a001c005a090b04424400c404090f002c01c040010703c0c44501039052a002000070071071080043c021941c10f503002d030381c85 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 526160386 1250 526159136 526159141
    0x702010b0d0507091a13020306030d0302030609010608070215010b0406090807030f060213080a0c05040b0306070e010f050c06010b0406021501060e01120b03060a0b030706020c032104050918070b03010e 88
    0x2240100030310038a8101e40e156080c03d03c8500c0d6540d41840c1b50320400a50056207908040c414140f503c0c44440c5200281401070013000b649441ea1150641110800c7ca429400f58442400507820f107a000402281c9140c42d0301c00100d501e00c0c0c072400802c1258020341d650440990750f40225510b64155000082c48079441c03415200100704150042c0c2119503203740400c1040380e83e842c6071807428801110403110741652840c104081e103082c3c400e4500740f9000350040c01322494a014000d0010b40358050040c1400070440c2200040d41c40340003964900c1c03140c0001c48156584035168050b40303401070f1160000600c60440c1d80805030500207440e034120344103038a4a4400d100f0103001174036a4010f10b207242c62000d41c1d441c078640301c95404011490159501072030003d4040e54281c207040c246032080d0805c100b9980211114601900c001601c0f0864110f12641650606600c4400c01552300c20b984c490f55000351604d081c00081a0f1003c40341112042c480210341e0003d90301c906152a90009102d11511503580200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 526161636 1250 526160386 526160399
    0x209060109031713080d0309030210091101110309060403050105090f03040b340308100e090d0c0609020d08040e07140d02091201060b210103080f07060b13050702010b0d0507 76
    0x141c400120f5032213800160310340b6a250140f074400808441c600198440c801e80040c150140000c0c0b040c02034003001030002078860788030591341c410044509410041603404204610500740260350351030b04028040c644d16a600e003082c60103007605441c980302c180102445989c080c00000b00301c030704039510b0400b01c6060011900542841c0644070107a0541c00000d0344150b12141d050101521401c1c4c400e4a40b601d0710f00300f2400d864060750171908105031320031004c4c0500100000004009c0701100e40c6180042e4842e4007890324401403c00000003d4001c003180c00f1403010404520040c00540704021187c000c16a1114401c0b140b2000c0711040800101042048402c0c00440703400400c41c44c1c201400e280000c240c48005c040c01c45015078400300440101042c1030318806101984a00050a00c002a54180d415501ca0944510489018030281c8a00081741c02c204510b94200303d01900004110040804800007584007401d002c8030180c006510b000400700103072400f2540c284095030001d0040c07120500f402c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 526162886 1250 526161636 526161683
    0x14030915040809030d050d0f06080601140d0b04061413020a06050c160b0a0e0d0519150507030506090106110a0222110c240f060406050d030c020906010903 68
    0x10700079500c158081096050030b4900304201801d0303007030701d80e0b03483d40e5030f460103010f0b60449000328460310121381040d00401060b90002019415542d500c51003004c02c5281c84002410004d00207401070809908500300300510405d54416105584440c0c040e40d2999901c094071055821500c20003035100d80107030411301c2079500c0761018203848441081142e001c0d0301894405919420701d544079034940440014041e03d050751000c0040d003401c109440d01d900094803035859a85904241c002140601c6c02c540754802030140c0e12002120030701298801300070130b0800b003200034081c1000b228128014041c0d02e0000515030321500081440056480c080c00c003030612982049058a03121890100c40d40d4081d0a4800c806864414401c3c0311000030041a030b9251003a0032281000030108840d40e5840c03496074400464502c0c00503d42c1c0c0102000090700306540d47c0c200060003007180c0d4002682010400d09078004150b04010884412402112170120b680ea880e00111490b0104d400020410301c011481d002c1400c603c0d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 526164136 1250 526162886 526162891
    0x12130c0e071407111302040b0301050f01090b03040b06041d25090c05190306061b020303070c0905040b01050402091507050f060f04061a060a080703092114030915 71
    0x3464082e55940785200050507907040382c041901d042c180d1107805600c0f403405900d6004170b040c1c0680150b01b410714081c5245036078001446400d014030b4081d000003829a20403400c0501a0000180007900d81c00d2034104103004040c00c03281c0c1c50280d80f0302500740d80441c0010485e948520700d840000e2010b40c901014000e00b226168500350880344e40042c0200e0130700807034040c180c0565170560b40d407034640d000c3c0f29180d202c10320507100781e405061134135005000c102d900a94a2182080078428904440c1051001c68a18400c140e0040e141c1d60008101040f41300b455001a4055401480954070b0750340c8a50402c400c0748a100c0750300d0380c8004049240405908540e01400c400c41c0548280c4101d15201d01403a414034400701c6030142040005410001005000d10541ca240004031107030b6000c807580300f07000c00c3d110301c01d1070340300802d20810b400081c1d21a0b100c2e4001d511119801741c00c1c1c490a0122a030b090010a003607070244c80110b00c0c00e03c0b5607912007035003806891085620100070310211280300d4858a01d114003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 526165386 1250 526164136 526164151
    0x31206040b130606050a030b1c021903051009060b180112020a0510050a080a0608060106053723180a171c0503040201020d050c01060302041112130c0e 66
    0x800e49540740b55101c0d105400c0200540c3e01ca495032914120001011035401c06082c070b01c101d0141042502400030508040c91550307054986080208401c0b03045c0341c507580d89600c024414820b682c0c050402c00c2d401d400404140e40300742801c1c1300c60b0051400300301e2488000400402041426001002000c031100060340e40140040c0001c00240e4485001c40d1391508548202c2c000724000040c0001c100b071f030255002e5440000c0400c1000643e051480b41512114103228040410602151a01108408184030018420441d402d84215040ba9a115251421054001012070ba00010661202c4104002e0728418400071040d0b5107080c00d2005181002c0c20398580190b040100400042600002e002604000e11a00b400810340c000711400c0c81d030031500c140045441003120a00c00c2c000180d80010307121184a429041441d15040e911060380d00416481d400a50322034104102c084e03a00440400521588010215030080751f901c0400203d100c90821500a021003040d90007003051b204c0e50459190840b50 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 526166636 1250 526165386 526165399
    0xf0f0509060d05010303140f070602070c1e0509011703040312090803030a092003150901150b1306020303010b04030b0601230d05010e1005120a061d0f031206040b 71
    0x180c000800c0e42a0045810011641d0340c440040c0281504003015441c0346d000c3c4001c0c01d01e050b9000d0007801d01801049401880300b6008216101000080121240039110762490454502c0e0011030015a8900a00c500d41c0200074000012403a45a036070190340a0780741c200001e514251540c2d90b1079186000012120082018200c40800c140d40e00740700660248200c0d80021071a1501420040d203610a900300703000c844c0b055071840703115549020802d40314210750200b154080d0303590902894050211280f803503180d050403900101e549a6020085e003000003590300000340241d12240d090b43c0d244028002c080074140140020400500110305050b40b10030185440704440c08445040140c0050404080c0f00061000c03c000b164980d01c0d1254500401600701140d45904003008607241291f01401101d00814880b8610040181c080040e8882140d120300200030106000d51001c00141d5681c01c01086409403400ca2811000700000703480403071845d0326607602280c603141c08010040405900b00c1da0000c0c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 526167886 1250 526166636 526166647
    0xa0311030d0c020d120b1e0406090204080d09081209310204210803060d030e1f020708070510031806090b160c0b0103110310020309010603030f08070f0f05 68
    0x24542d00030b81e0031407a195001000310480300f80010b41003034413501400c1d00700380c60300007000800d544071303240d8079500a8003003490145080d044022801508076608102007590000800045160002801e0602c24010b0350700d0b1306071592966550780e2910754039150b00031300700000e000700141380c40d00d60340b00c43c858158095072080d03841000400700151400c50761107d0070203501144c1004880f100070555904c400f1200b02100113a200ca944003101c03800054034240c01072800700d2207481018050000038001486c000c005140355181003415a00c0708480d0a00301c40140103580c0c0009414070f0018042040d00c0c0c00420207001c03122601000ca00070b0101050040d000d238031410703070880420281c0c8208808075000da01810307810700c1c10103060349100081c200e085040241000011000c03c181184883c1500c0e8030002d54003680360101d001074540480c2401240d25148000244403d4200551101c0c00326442a200c0da4060071440c0320564511004490040c0802c4000301941410791040314a442403101600b00383d810308 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 526169136 1250 526167886 526167907
    0x307060606080106031109151b03120405010b101b2117090a020a120c0b0c010b0a0504021831151205101109060c0c1e030a031103 57
    0x55100707602481c08550110b00600005a00d40580703034685444001c114030700004030021890620784090452202e4101258000074008020824100d48884100b260f440d40368852066003c1001524100c54662a15012404a040054151140724480e407948103100d4110b403820000a02c48400480e000b010114410000302201010481e408080d6a100d040c036103107030003418118107400380440041e580f00840301e50040c1e841d4100c610540e4180c00310201c0d10f0015140841914156422204d049400410001860901540b01d550844812128016030030343d0340e41032100701d2048180c1d201440640303046030301c5141018086901d2800d1004812030340e006000c4070005400407001d0384005003d4030b9031502c1c2400c0c03003001c0f1850054280c0c1c403080b890707005c81e07569040d81c0c40c440c40305a01d001c40e460300140c00090300b035030040d40c0340840e016002e60f0b6211101e1080c15110711340055994410f0002103090710342c080000c8140321651034054000c5c200b840c0035490584141a403107081800500c010845003084 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 526170386 1250 526169136 526169141
    0x507030b0c03100807120219080609030d050105041a120705041109120f0a0311030f042c061e030a08040608090d0f050d050604020d060806100e010f0902030603030706 73
    0x980341c0c0d24181520303420002c81400d81d1603610f600c05100b81d400f41d4018855812429582d0300490350407554130704002c40158001746004880c1d4802d901070b009100801454901c088014030440004101c100b00e070303a88600401040780c01c1d42c01c11001100c40304000090908100300f5401d0100c2c2840c0032129050b698400140076920340b41401e03180010081036918290034030b08a82051007400202500d0354040c01e00e40b8507030703070826548090b040110be82a584c00c84107042c000c40d85202c011549095803242c840c03552103d50f400d0300c1250241d8480700300c0800b11403400c45030500e02840005040000000078200d02c0c40040030720001095041c022003061000103024800100010200c90300e40c081c55241c03d80791f560900bc403040b03020b0180070b440680ca00a040d40304d4110f80c000404150006050345403000031600a008110003450410f00e05000482d81c21400030b4824403c00000c00812200c5440e40904114408284a0031480a940b01d6041c40b50241a070003941c0c4c4130001508613810700c00701d0b4980100307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 526171636 1250 526170386 526170391
    0x2406130209131b030204230a170d0f0507030e130f0609050907050603040f120e040c0206090f01060308030a1a03030a0c02010201110909130311011406040b04050408030408070507030b 80
    0x842d540d071001c4040d001c403000c5400100c40441c0781011400d01c1e1410881c65009a16206e4001c0503400381c0a241056544400040300900301c09400d05190543e4040120307a1280d05142d4100402c40041100d0740c0d07a4441e508440500ea03242e0307207004126066006001c0d032980810003422145485143c42c494002003481503400504601002086504104404074180f003000d800c00780c000c80040040002160010940000c1d10b6480101d0403088503242c10111201d5492101d1254407500708014005901d0380013401900801c1d03950251048000f544004508941481c80018405102880014286402d5a20002c0c0b65505448000040c0000b00300090865102d00d00b1139002c100b08a9041c015940e09120f2103106100001d0400e280c182a0707000208400310040542a4024403501558205071085a101600c2036102000f8441040c07160850314175110200d0310b16015501e13114a2603024903190064a001c0c0d5006004030780795858036100c01405038032030907040c7d42d24070411100200050051425a2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 526172886 1250 526171636 526171669
    0x60d031d15040302100e18070314090c0102010b062a0c0402040e0106080f1306020304051f090b101a0c03040e010608010e060301152705090a03022406130209 69
    0x5595a05500c100517200420081c01420001003008100e0183c036590900b401c0503091a06040c640c1e0703a02d00b4100c028120030072800792130410000030300c1400310300000d0720159001c098000707200c10840354061015502407510003c004070a2181107100e9403ca03d0a400410750294007030b6040034510700040b8082c0c2c0e216a00040d40d113010304004000309a0f100011a81044c074414020701e0600301114010807007034800300060100c6600001140400500304103a03c140804200442c118114140300301c001000140c40030b0b01e0603000e0700c001592181400310904103959030b200c0d00c400707144501030311543d00c0d40114190020728030080001140d0040303030301c0e0000d00811141da0340400c658180f01d001d0201182c040e000fa40203078107049000300060304079071914013a1845500043c0212001c409184680713a074824035003816502d0030040c0044100c01180381c034001c5029808035244020740c19141109002104045444c01d242d45d008500c0f6490710b0700b81255820a212009070400c0c800d00005503058903000040c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 526174136 1250 526172886 526172929
    0x60503030327010e120901050909010e07090501180e13050a0803150d050c040c031e090605060109081b180f04050d0c0206030a0506030106030b0403081e060d031d 71
    0x7078459622030480b0480d81d44080d00034400c600c6807048042d602c01401c2c0850120601c0403809602591007403003500c2d404036001b0030514003941d460a0420003214240c031440d000841c099004581540107901c000e040200707180030100014a44250709040080107405510980300545220300414410130055030241c2c0501d04403a40d074140030b0b00d0100c110103840c4400d0b02a6001101d90b0001c50004950340108031000d80b4081012001500200d00425000c8030310844100340304911400d2210b56404004014481d040820041e03e60780015180012544120b4400d075004403007002c0411003410013030b41490005825040902c8068011010001c8200d6070301d4858150390b030030401800030410214200d86014140840040c05540120780b1910000b8000c02e01c0c2c0d911100810255202548010002d5820036110061070509150091080c04240c512140b80c4000c0f80d80003151202a04055000f05001080d144441c1c00c0c41e84d00340c038403200641e0f8190401034040ca5a00d16500c07081d1020584a9442085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 526175386 1250 526174136 526174171
    0x509120d050f100503060a0506010516060b100309021f03090f110306011a09062101030813090203060112090212061315060b09011b0c0b300a09060605030303 69
    0x2410032a90007800070f440350f03046010800407a100450001e8020010020202c0c3c6070741c1d0400140c805201e5090fa101011a02d4001c05003489615480681c254400301e0300f421601d00d1100e4100d003994141e6001951180185544442110054541c14a8001d80e420049054905034464810090007440160369110f14404803030380c00d140500c2160301410024805000780341180c581000300780114a805401510002007507921010359003101c1100030019805003005603164640751a05804c280c0280c80c450b4252000800c041c0014000d417449907006175079403010f141c08075464001802c0344071401e03a00818048040c50110509020b00340c81200c401e600f110300b55999143c003000c401e101062140d1898504142440250b80341802c80344e40d00c07401d21b0440b103c03415805484140c1c4401c03450007416051005800180072a050000e02420350b103c46000b001c0d2810112420f134070600768018a40080e0a14000a0101c10103a0000e1403444c00340300001a016120382c04a440c42d4002d450b25091a26030075030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 526176636 1250 526175386 526175401
    0xf030c030209090d0219020f150405031e0c0d0807020414070e060702150a09081f1d070b0c100509010f0509161208120a0b010206010906030201050403060509120d05 72
    0x102580109140f8001d1107807a01180000b500e4800c1c0021191100142d050200291340c0c5452160101440c028082078521041107450280d0381c2c81841303424024010044542c0460700300a0742204241144005401118120000c001c551600454100c8442c0c000340201009a00c0d80d203e902c1c4510169103200b9030a040a01d00500407041c4071100e24895101001000c00686030301c2c0106c3c0c3c1c105500c4611a44852180710255a40c0045d50000c0c04588a601c4218011a00340a81c0358040a01e004003046281c84403180c0700038040402d000007005500035501080701e468003400030320b06c40c0d5542c0c050700c04140b0320761021015282c0c2600c05c1e020700da45a078040c1c44084118810b4580180b4540000e080c81488110031000790000342c803075100c10395403c034071400c2400040000c0b0b0304611303402802e9140b14600100c0d486c004080007424180180f20b000c0c0081baa406540c072500060700d40503140c460409195940d090040c24004100c0d60040c020300c8021400c03140c40030003400b40c000c011100450186031520 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 526177886 1250 526176636 526176649
    0x21030201061211090402030a08180f0103020c1c020f10061a030103050a061a0907120e0f0717010609060303120b06030106080a020a0228110d050705190f030c0302 71
    0x2040304008800800e403000000d02e41000585090b80260b508413078580e02d9000090410303801220181030300d000040c40003050a01007580d0154140110364028048600c04d004508034001d110070010103902680003c1c4403440c01020322009140c0e01d1045030101420f9071207050529184036405d4050a4507000e00344a10b8811585101600840c1440e150541d85540c640d04d90f60f41c460030015104a5840240365280c03015051090603800300640004c03554100a40000c00041c1302c01140c0c0905403900040031403281d004155400c516110100620009003480d4580e201e1220454284000b9036071000000399a04143c0107000007580203442e8040d280d245180314134161240301000c0d034403842c400c00c01406001e801060079034100440480c01612010303501c5040c1d290000c404242030001c250f410480714070741c09111100100501c101d510541c8809450b00744442501da0600041140e00007440900c1242020240321501d00010703042440500d684850800c007140a41e001aa1518070043c824010b41c02e040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 526179136 1250 526177886 526177889
    0xa020c03010912050d0e01060b04060f0f0207050f0a1724010501020714041e15090b0609092206020706060803070f080d0b03030d15080604080d020a03062103020106 72
    0x19402032003000442d43d9000c50380e40f2901e500100340305001c1662141d03105180e100750f4284410a001b003103070315260412170703507507400501c80c2000040d80481c1a5445a1081d804400300300c0c055002440028103120803c0b00310801c00c45d4a540146104a0002c1d2002880d107644a0380786c00c0c90301515449001d031800c80d0913004c06d03440b03182e1800e010800403c01c0780d03400079185048640e0405d003103010b9509800050050030600031f64904208100c2d0700340b5548241c0f0b07484060191071a803401041d03581c4c0e8241d1007017070782c7c5544070541d4000010301000c841c90034202561680301410032090103510041100c544070520007a5815181180e000c07650204001d000d109400c040e203e000001c60400c0c01c00d94500707008950145c401031040b040840ea4801c90b45194020041c6910018292a220b00c0201c9580000b4034507501c1c0c00310466540500003a151002240250041d9006020705107404044ea41070000380d40490707000d0003050764807140000c151108000407510048941d0a02002604604000342980c6a9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 526180386 1250 526179136 526179139
    0xc060f131514072a0201110d090f050d020102070308090f090c0304022e1d060a0c0c0b091f1b060c030c081302040e0a061e051506031807090e01020a020c 67
    0x450544085020310004c07440480540000e01402d00c3c8098070040707408040ca41c40307008161184015002420f40c0020000702079521490840800302c0d034400400034020f5919134003a000da00441814000700e0b1210300203140d518406021010031500c83c5000c18544801181c10401c10500882840210314150809206109550b25140a42d0180c09450b03142940c14011503801d016122884501818124090a4042600402c69a00e5209003900030f0240e6500407802c03560f8140c940e170302040140c14102030744c0f00094040c1c1901c02400004901d5050600211201000d01800340b01c0b02c0487d050380410070325014032841c0041007030f40413140c0180c02d4541e61341c0c014003481002410400c0c0d0070304000000c25403540485010a0f0843c1c3c415901b420405a40d4002d40428180b40e200c200521002484170070f80400c0070381c1004640c0c4c2c1d8110306d12102ca00006903035801041040450800c0031142c42e000188440d000644650310303543d00f2844100c03001c028a50001d40d40108a65100b00e405100ca880f21110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 526181636 1250 526180386 526180397
    0x2d080604081b010b011e03060f080f120f07031b05060a2c0c01030c1806030204081b0607060504061404030e010e01050403080409110d020a050715020c060f13151407 72
    0x4aa500180007024881c0107021101c42201d2206e0106100e504a10018106104450065900c55041c03680320584a9503c1c02140f1070140501d04c107035120f034112000002c4112405080440541e4119140c03560b228034048070514101000f000b081086c41601c1c040d010260000035500c055072140341820609141c1c004040c544d5200321000c400b00400d00c0451a002484d000a1640054100340c0301d40309400d0400101d400e81c18404200c8a81650040c03003941d10940403074131062003814049055072040700c200c0742c10110611507080000d030300c0e410035600030f4458040440c0c00b41842c0b80400c00c511b0116030540004210803d08001c2d940c005900c541078240a01c1c049103458110748800180e84181e11809461a6440710f0340d0f02074100c01d07801e580200040903c195528007070340c40001c103d44c109000c250b0b0174a404c225070540e1120640f00b10340c1074010700c070003410240e540c4c088014000030380140018860f200306a080340c00a0808a040811808803200004042c4580102d2405c6500028440c0d0207001c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 526182886 1250 526181636 526181651
    0x90307021816050c031312060518030a0e010c1a043f0207030215030a06060309120f0203040f08060a0606020109030203160c09020f0903010c020102042d080604081b01 73
    0x450010010910102c18240306681e8805a11440d140d0301c1401d041c5041703034850040205024a40e004516035031402400244003a441c0c0943c6c001c120240c1c2412020719600800840c55828003610344100c40c0d10050501105104454842510794414280c400d40100d00d031504100800c014540d003241c0d1211954000000c6103054241c5014802000c0404801180c0e003219205006108000c1d14002c0e550192003074100715034103500c00c2400d070025100441103c0c00d001c0003040c245d100c0c2c812403d4440e00010320720303490a031130001599060602c0c0f80d85001c60004100c003055219140280800422619000749010b00d080070a0500f00c992942041d811a414134105d0b501183e400401d03250f18038503145100c0d031a207800e864040b095490590207200304500225042c074841c03560f000504102071007034000340060641084101c4c02c0b03106500505050308240d10007081c0c1c0c0070416180e0011a000510340c00d4880b0b40764904145001411502101c2c01d200000301c544600c60800350b00c6000c400980000e02105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 526184136 1250 526182886 526182901
    0x1060e071e110a08090a0b0a080717060d0201120b09010b07020f060a0522150302071a16030c03020c01060f03051b060a030f09061b2d0c1a0903070218 66
    0x2c0000f040081c000303080c0412900750a0361560603000040081150a543d500e40c614005000001c007140e058010440c1040b0b42543c4124203803000d44108401000f0200074061b581c01035441c0f52486845443e4960355200105aa494090784603000c3c2c04c4d0404210b403141c00a20400140400803130340760340070320310502809080c10b070040d003500c1912001ca01040564007070320381a1440240107234404440040645521320305c468059000f07008890041504015500c50300b030a00c08050000d850401c90441c218042800702d900c00c1d441007240301e02629002d031810915031001403e44500d50800b541c540581c26041081210400420350041041d03e5545603404400700055031034010b80741900245a120040201001c3c2581d00a404140e80810100005000501d8045604d00c06502c4000410702a048000c12072882c08503800301d0002e041440c80341d0101c4680c00300c07031600413058120340c0c000400b0741d461242c4500d008101d103d82d1410005680720583c0d40100840b803031003454081c5021701840d0906c42d00307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 526185386 1250 526184136 526184143
    0x10e030405030606210102030103030503041e020f060a03060b0f19110d050a03060b130f0911030a202d0412111c05010501080f070e01061101060e071e11 67
    0xb12038200e8809490075800c1404070403c81c2032214140305c2e548008008000c06420201442c041c900034034418010000705039211106500d881c0d4040d40c0000c0e21039600007240352003002030100381c01a250100741c1d10359651031213440e90444500e80b8419040031907940064004011443e40c40307401c41c904404040800d49085071501251090300040140c0014520704446c0283c001c0001490426002a40c0d011b146c01e6040100c40c05003d44444140c00810018000c500c0d4003d06103d10b000010082c03540e1244040c0100804030200b8084084440e0700c05c440011508001038032164803c085464003d11500e02c070705200b4015002034480004017030100f40712142030307580403003003595100445410600c00040040d40307503106151f010050b41c4d000c0650100b0001c0640266040300d06540849401040c5c20244070303103c03c1d00703003e214115480c2800400500f4421601407111100c400c0000a5140d105d01e000800a00d0460701c001c081540c6900540148210300510407488280d803620090981d10240700170748 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 526186636 1250 526185386 526185391
    0x102070f0603091b030501090209070807200c09190c0512070806040f0c180e04021c03140301091a010c03020715020f0a0606240215180a1103010e0304050306 69
    0x4040e41e89036030f1800c0210118003804480c060400c928036540d600d00d000c1b0302a185108049000750383c081c0c08508428000c40703145010f4041610340d0325041c5d0403080aa80c480015082c2454648a80e8208141c50384401c41c1d1580240300c50b842000410070030104a000303960690300110200601001444450040a800319030010340f0351414030300c1ca403280c100080207802030110809209140c0850182c10540010b0104201e00900d143c4a08055841100341740010044070069040458030142039903e45a101b0520b907100e1007803d01c040154400c424001064000f46c019120160f49d42101c5003600462030300980e04504c0903c4c0401200d02c46a4000351210b01500c91220114080040410958002c0c0603c4917621140c404a4000709080c0c1003900152110b0300c20011845442d40003c038560030040781c17611030f094041c0c00808045d10030703d00c3c0b03074055000100310011900c1d0015841c0804030b0284801c10007503010340b2504214084001c105421102d210a143c0c00c0d90340100400c10281d01c0206180b079 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 526187886 1250 526186636 526186649
    0xc030b010f03020904020d1103060711010b0427020a0e01080a03030f150311060d02030f160f090e1503100e280b040f120f14040605090f0303041203021b0102070f 71
    0x11900c0c1042c941450300502400d611a0305005502c0bc00c212181c4c000c0b50411003008210003407200145081c00d2000702c660f0035a054017040b4114007440e0408a000420440e0075102400210440d0303070740c2c140c106042a080e08404c90780e070032583d407520a02d0f034140124514002000d1080007081680c03403584190004500c802007041001100c0303803500d5580c90056804003514071a06558a02d0166a0b1100c100411250007050a22203120303640018400c040a032007960b040e8540c04940c0e82480701030500000010300e6100c3c0c6000f0400c201070315403401d001d5501520b8500c0c01c00729241c1a00e8100c2400c10304c420b1014200c151400049400b121101040e00c240301d60024070410540d1218180a032054060303450241c40c0030115417000340d50030760103481002190413075901c840c889088440c0f0451948a94880c0c0c10000e1001d01c50041ca915092607031510745c220050403245004d03034441484215940b00341003503000da00320006000066000d81c1001008401c01d1010380925418103941d034681c83c07035902401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 526189136 1250 526187886 526187899
    0xc03040219090f0e15070207030605061c03080403030b15042c011d0606040311041e060f0603050f06090106140702150c011a03030a031a040203040c030b010f0302090402 74
    0x1140e41d5a00410400041c10203141c05100c140d40e02c244100250041c1480034800380b16080c1d40140c0e403070000b40094007801c49640a40049840d64560101914001c0d0003258000410004c000400038400c44a2410a100e80c8851440d071a040c10007a08a55841e0b5005024501400345041d40904203001c03101070780d50014002c02804100400042c1e00401c1d0f030003c0b00a030303030948000300b01013010f054141c5568000308c1224400c3d41d140424801c03c2d00540c44000c00310322910b02080364a01d01030b00070b0a50810119800300e0f5003c85001b0a005440650348078407001c40f10003200307108072a0b147c003c1c1a070020038080009100e060200100e01a554148150000c001304d0f403c0f005005100001112003150700100200181001c050b02c25440d64000d0882142d1076203480c60f40154910f4910344d0410307106000703010310300f80001c850301039001c4d0180d6185050194140301a540c4203550b9480590700650107549002141811071500348440501a0418401207030080000c0005030794001905901c1035050703502 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 526190386 1250 526189136 526189159
    0x2c0f010309060207150b210604030e03030d060905010504180f030309022103040513090b010e0a020c120c0705011b02150f07060509010b040b01091502030909010602030c01140c030402 80
    0x820000d0050880092405ca4180b83c42d520018490700500c0c15144115001983d0b182131506500070040d8000b10448190009000500464011007003882d607008054243d0385454102c98000c0c084840e1078100c0c494007980c4030f005002d2800d240c400c80e402e1019440904e8404a19522041c14210b100c0720010200354603042410119165007000074240b401001c40444c1c4107c00d600e949440b44c20500940d401440101c2d8101041740c071070b00a410885402140380c0403140d00304601c001ca0302e81c00418881e1550b408203d440c00c813071010000f803480b10040c00c0034a80c8405410b100e044c02d0040ca640034a04200031480d107810301c00c0303c04401e0401c3c581e04480380c0f1b410a000c0070b0328003501d004d0050301c02101c001c042501c5007030002d00c0c0c00c03035889a9414002045107028900402c012a80d4400d04c442c0014002e031420301a00b80c03480c20440118040d0300499081c01e07505800114040700c00d810540c0140c00100301d210b08003c09009400c649010b03101c81900c1c41c9801d41c814100d500004101030f125007410710070b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 526191636 1250 526190386 526190393
    0x2408090c03060f071b05030301061b0812090c03030409061502070f09091e0f0b01151409030c03010516020f0102030118020711040c030204051503150904050f0604032c0f010309 77
    0x207002102e1a495294078114000b0f828007c0d10780d0030074400e800204145d04c41409185038201c86082030660301c0720240d400c01c0d91480c0c1d5030404801c003c1010803503108600c4113400e680d40820152005184400780496201c0c00d212004100049000d00c0e0010b540c0f05a0040c00410310f402818001c1d2130190100056550543c1841d42140c9004000170010742403d0301180e060007005a00760400500a040c3c030306d8141d995928203894000d2080c1c2802c0001c42c2407480d080003282e4130004003c0081c0c000c04482e0700f11411030000e42101d10544840401c06200401c9140a5406111238880c3c02e4100c0700031800e640c90701e140c40318940e94181c0f8020a03654000f03845020021189904004480054070410000d0b4031950040c0095009000b024441e4010047c0070b004183d0900442c0d01c20030906250140034403444050005038800540211298054014205810a0304000e0240728500a80c5c404050b006a404100f890120054030100b80e20140447c80340c554032000d9403010b0000083c0f8001400010030b04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 526192886 1250 526191636 526191647
    0x1c051512150c04060f0f0219030915020f1005040b06060a0c0c14010201062309090f06070f17070f0f0215130c1e03060b0a2408090c03060f07 62
    0x507840100008014481110000005041664000e07102d032421036030065020307a8130402e0807183c1001a0700401c1071060010404043c100c0322032083c05d000104640350030384400050010044500103070701940b030301159807604200c050000a0141002c1002d401d080e00c941080c50002050030780580e00c0010b03a610180e00c1404606442c035045000851a82d07180e01150301e042907031580f940e0056003004004901071407000075044000f510661410040c821200c00d01070382d00e4004040840c68001c00c82d45038a444130510103544a01c2039542c4d43c494040c2c3c0400041c000c000c000d0340c01d01404222500300100c064100306104a6070085040c20b440040303800c84102d15045600b03882000c0ca00840051149549500014100c910f110b8880854040d03211104100080c440c081c50860b01c20529034200089441c3e6070000c0311800016008043c6180c03115440c490b00d00d6030040303c9101125070501145c40c5a8418580d0f500710f41210080c1842c8001c1c50b0010390703554000b40610304040c86a10201b100305010340d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 526194136 1250 526192886 526192903
    0x20405071103130305060105031f09050c060d020a1e02190c120b04150209150c010209060a080916052107080d18060c1e0303060f0b1c051512 62
    0x2c480e43c0d43c14030300301800c40200510084580b071140e44008a52481c1c04a00c803201404600b1054041602c91500a000303424010000e0306d42d401200444026500e0b0b042c000d00d500c0038660005a40e480c1d8220f0020045426107a11001d568044c1d1038000006601280c61384880c8041005a0004162802c200d01d51020603440070709003070001c0b003400d0100410040560311480c0120451035503072400d0001030040e40706c2c180320340354440ca0080010110581801c007602144911400043c14a0251b4011882c0c980c4010050404114040304200307982c00c0400629074942c401c080003510303052609020a000c141c0e480312b00203400d5000e08503100309603c2040b42c04000c2001008454940c05000300141000c0400841c0156001c01c0000204465000320240400c0c00d0b40211500d0340b02548074044c1d0000d01c0f030b8841c00c83c105511650b00188417182001342d0030181a400c075a450351b681d2410000c002d802c1246c0480041d00f1708001c100702c13100300b01904607012078109907040c400402c02c6804160504048 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 526195386 1250 526194136 526194167
    0x10e010f061202070320010c080a02090f0909100c1e03090b01091107020307030303090308070e06160503090d030e01030608060c03131a0a020a0318230102040f080f060106090305070302040507 84
    0x400d60050f4881c801500b08c112111100c1d140d4031980c1e100e40003c3d0050b4420030300420b4020b0303042daa036101c2904080103c6680f11494a06856080c2c1041c0c4c07641040e81d40d00600071000501c1100e481e1fa00714000749002d26450001d0500704500e000950301c3c683e0340030741440343c0d06000b03544024141c1d61002c03a40850b204241d008040d98400c80e00c0307140141c01031580a0081d40090741500005400b0ba015160b0f801005100400c0c5070b00708404d030012940b40b4100c428086840c1d0106100002d07064880d03c0d0702012552080e111031b422403034513100040c01c48826070b02100c0540d10241c14031407000c908070210382c0c1200420b8100300029a1500304a82404000007101d00710243c030004005100080740d0261800200c03a6034140400f020140d0302080046a5800241c01110001071014900628a030503424445030580003604040c1e58600e42c0d12402070582c40561a41c01403080c008400301e042c800c15015085504209961600b1611110754034180d078000240129610001b041d00f6501628840f00700703112 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 526196636 1250 526195386 526195427
    0x1b050d080901090b0108151e04020f04020d0e060604050705040e060f150f2106090f060f060d020414040e0d120f0501031211030c0a021504120506010e010f0612020703 73
    0x941ba6203150fa21980103215a016141c01404943c1000b260b00c2d001001da80c803040301c0c150031349880c0c0030405900c1c990300038160f00a0f0300304041085518580600071000901c0000b8242e180b07805130a000507241c0040071142000410041031040600410728039810890079a4042811038203100440c4c180007401c00000404080480c1c0d42d4030400e2440d00400b4540c0c005440004071410440c11003401c440182ca0956002180100003410001d00c980c111b40d01c01e20083c00364030b001040c200815519404402028131840c1c0010b0148505a11a21980b440d021305840810454241404c031684820350381405008101c140f070740302a00104150442d41c51a201800b003080a03596920b0a90a01060030404a001c1800212703060f010920100944032900d845002400308503029070308000e03100c84890414806000c0c103000c0480d034843c840594191851084000340303030304c5d41800201110700300305038480c186a0074a400d05001c1c96510109030b404185881e000542c44901a160aa480605001c200880c112 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 526197886 1250 526196636 526196639
    0xd021b0a090509070311030303010e06010e13020f0d050105030601060f0f0e040c0c0318060e061308060a02280f0e061608030a0609060807150c150b011b050d080901090b01 75
    0x44040350950441b8801c0c2101e0886c110444145a00d81c00240700e802401c000040c0040d9855004001c42c034500c07040204500440182902424100e8200038905640c20201090188040d1424450035000d02012801001c20750b140010081140044552140401400c029161200380c050030340604841f070020424024040c00c1d00f0000c002400420301540000e50191b44064481c0c0c604405030241c541d1aa11034000e5901c3c4001d20050790302450000f2101d00321403000056620701449013078040d04036802e01503528072040103600c160080c0c001c10029089038041800c80140d40058000903014800d0520650031210030002460b180a180042050122114684010001ca50f4004c40c880e008200c0204201511810408100c0304980100340850b8410b10301809010100c1c0002500f090007403904203069200d80d50f603508000c0c000c800c81070802da258103070758a07590f800c40d00600f00f040700c0c9004001c041e8481c0d1611903803000500416020f018050000c101140c03030a420a907940d03500304102c1c28465 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 526199136 1250 526197886 526197901
    0x1503021e06160813090515041109060412050708060106021005150d050708010e030726070c0803041406030601081303110304080610090209030a2a06031b020d021b0a0905 74
    0x3d511140702a00058138a08021903560061b206403800b0303404d100c194080d183c44940c1032100a141a4490704032400c002d0042c0b150666480000704003030080c803198503008000a2a1040c03030f10a664210326441c1d00300c540180a00340d03000600360360404170b40c413011070192121058407074074256000f01c6d01d03085001c15a41d5014020f00040d0002100c40403002081007007051091241c0320b0081050062504041d001e0212152079010a00c100410124a0031480c02c803040e030f04d0030091411a03004c11000d400119080001014185151000c04016a03001c3d05c0e510b4000e000a081e00b0000301841c420b4000a1002000d02d0b114502c80004012081c0850740e58640300c5828943e540c49c01c03100c03542240c0d07246101103800c140c80d001f5109420000740003804000603503900c034881c262400078041011042204e1075404525038036419001030141c0d40300002c0a030588100141c901200004000566000e4002d6000595001844c290000b2140c060001124266400500c1380340c80c1c2d50100d19150304110030b20042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 526200386 1250 526199136 526199153
    0x15030510050a0612062a23041e0e07050304080f0304050c0424140108041202100f0902030c010e09010b090114191101110f0f0c16091503021e0616 64
    0x2e09000030800c8910f500c86c0d00b070340d40c524001c0c0e049000248601c40f0120b51080040c0300840b40c00e0311000f01d9080036164000d0401c8076024102c01003100522040030010800115031558000c6181d2901d00e1541c60151518900751046030203021003054000009018001c06014603334403400010010f000e0702e9040c3c00500010071a902d0090140055054006180d140b02c000c0b00340c5203801030f103440103195501d0710782203410341c008070b000802d5014405840c00c10414038452000f03440305034000041c4082c454018189810141c1c0d00702030501c044a00941d61940d10005080d044a91100d01c1a941e00311b503c004942901114190101200c40460160003042c500c035070f9070284803c641d50b4001080e8029401d80d00f070354503603103000088801c00c1141004a54602e001004005415110786140001d0408400c1c13804854404500205400201c00d0001e00854091400c0c8180c548480282650840c1c00040d070b41001d61a08a1111904080f4418161200400c3e03401042c544041601d1884980c2045c603507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 526201636 1250 526200386 526200401
    0x31e0501051503010e01051b0a110a0b010e15010915020c0603090105011a070b040201030914030c0105070f05040819111302090f060c06040201080a150609080115030510050a061206 79
    0x484d500b07140e0740c1051008140301e4144200f1000f500c0d060003c0b900a240c120030750100d9a20f0007002001c03102d2580b4260b0800041440034801d2081c280650b151190340c0f41003078809450601410b080030740a4005aa2000c815419581d0b0041111040300e4501c8040e40781c40d25001e600c0740c101e41c000c01041544841903114034101e48400824126140108404045c2407107100c0d4000d0204140310041005940b00b64490550304d8441d288204c10000c0c0b9a10407840c5802c40d110280440e07448504004295a010f410240402c010742005810b060418100680b81d907011480c2425440701c1e039941805000d944042e4485840c00685808210241204241c029622000081c0d0190510b401080c0d00c80c10a102281d841c900c05a010f005d098031603070300440350309101402ca040340715110f20101e0207014100a1002c02043c0e56140c542145190510150a40381c94040b81101c41c40c5d511010008900040382d0b5500c90319402a0000d10b960313a140c5a60000d00c51a008a10500c101c0c0491808000c40c035408140b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 526202886 1250 526201636 526201639
    0x20010e0307050606010503040b04060b0406030b0c09010e0a181107020a120b06011b060c03110309070302030c04020304211202030a090209090d12020f04150e130c09031e05010515 78
    0x500c02d130388690040d41c1900c82a82c00802d03000301c00c000940800c40f00d80c0022190400200b000c14510340c1c03506e44103e5031000340d0341812120f4001401540668002841c44908001964466a040c0c03800251078041c0300c1010300d80c40e0060b281c0d8400b000079506c1504031980b813540106900c850b02e840c0e12011080d0980110704452500840f0301051042d03000e0140091100c06588580311901c00c160380d0031000d820039071580400d06403078401e03458504100d040518420b5110344010701c1c080d40789d030041515220f19062420b00031841002448042001d405a141c000201c520b0382d0030741081004400c032000107000c0302c44400a0700c04014020300c1510b580060404900071520002c0f942c076450f09071901ea514240740d1001140360a1240307802c0711f4086e0068055100c4591199080c1561816214031100441c146c0c040015030800c00054240b41c86503941c050242c0d40b0204221561041b032000c0c01c1094580030143c0f0b0035000006a585950081c1d5191800960003400cd01041c140049180e0a144102071100d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 526204136 1250 526202886 526202893
    0x8011d33060a0903140708102d1a090c030621030403030207051003140403080a0902040203100602280b0a0905190203010c0e0f0622060f030b010e010f20010e030705 72
    0x10084030100113115010368403c034000d000b4104c0c07558142c0000b01160703071010851806042594142741c0d60305401c0d40070460720300d038007044080d0012410108012043d101c00c0c4251181001c1c4940c03103040130b0a90798094010f54204c0c0e04034060002c05554100d40d0801c401e50362000250201c2019404035000301140c105940c1c400d104070180c078095007a61042c0c000a50b0030a401800200401d2040005035005201884001054200c6070081010b80c1c2c811904444221035901c2c08100803941000713a1100c890442e000c00f00d0403220380480d07841d0a250340c0ca001d001a0358100c0401c4c00a4020f40c80300344520750040841d0b040d01129511900d40c1040c00c08164825480d12601d1076a1502407512070000350f0700144801c51500300700c07007040200c2d0001400e103051594060140384003e4078114072403028011544600c60304001c010030090039603050010745e03410408403080c11a0aa608207040d034155141c141443d01c3c4400c8940e0710f8120740e400706031904940e982452404c000503034000c002085058040c2081c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 526205386 1250 526204136 526204163
    0x60909070e01030507141918060504031205032406090d050a050705031b01080a0e060702150109020702090601320703090f060905280608011d33060a0903 67
    0x81d1010201c441034120030107020048003900e0400a161f2180c0c40c903a900b40248a1094032011080090030754019001049000800b030042c0a2030380702040f45580716180c4980f4503e45900b2909501c1743c24000d40c5420400080001402c0c1da46a080e02c240c0c620103404803a00707508509003641e4400303038580c05456034001c400010401d802c0103d070b034000c0c5100f0741800c1804003800c0343c011918540700424140400d56070b0007400840d08800e101c002c2c01035015030b0061010510280c014107825078183e1003106018030400c021001a11030719030042d4401001d00388160f122822003112804805120700d0440b803e41e440c000a0111040701001e82200c07802580c0f20280320303440c3c500c4607204040c5406510007282c2c40035420025031030b00d403d4403c1110403180803034107107020000480100c1001750304560041007000c4014000488001807003802c55a0a8851007403a05015044c42101c41240d640b88000d42d40c619801541c4103031035000e80454010152500750b84001550004207800410b000864440d4500c000c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 526206636 1250 526205386 526205401
    0x70b1303240b030a020f240301060f200c04020322051e010501350706030912030506010e04051b1206030f060108120307030e10060e060301021314060909070e010305 72
    0x2603031052250701500040306451001c0c01c00013142c607611f4401006101c0141004c6824941802075030081400e5150403d1a08101d04046c1c803c1ea5204074003540000c28610000c0e41120010b101042d8a03010b80d00103903a40c0318880030540c00c104140390701d003040c0c6c00c0040800030094001030304500380f400b10503510600e26000e8001c6080e11002e10601421b8034103c0a0007000c5450030400003245d804080811080c0284400a5810500168402c5000c2a07461100310240a0481c60441000145207400c00c41c0b49090380000c0c00d50140e080f806c80c085d9540f94000b82c0e9880c407450382c440e104501c640089840318000241e640c0701c000102c414501074003d40007c10140341e00040c4d070307a0603106000d02414407810030138480007591b00010080001c2503164001c0010410051120161700c2404501c04120341d03003031442d032340741d8110040c000c18000e030b00c1001440326004403507640000365954010f4040a603944000040c405001e01c0014660158006042c00032a46c1c0100c0c10f0702004100b81c806200d1a40c8150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 526207886 1250 526206636 526206643
    0x501050a02040f0302060f120a0506150c03031906080f03130e1b0c01060e04440c0307050133030812100b0301170f06010503070b1303240b03 62
    0x8a02d40d0f018603149400e01c01807030200c000d0700c1c01001c2211010f0400c00030b80201203d450056442c0c4151580d10350034400b09003031003e454041d00034201000c03403030070b02001c80342956840010183c81010301142c55901e07104215402c1400107112180c03c0340c0d10310280f6101280c9a501c9809003181c1300e0008100050b445400b40d082501c070701d45545092508101980c0303142640e610411079218155a6042c01040005141c0c47d210701a03809210440308880d110340c00c00e0703200b002d18550300c2d6240d031702051b103074003465401422014148024001a5143e550f002601883c1d8044d0400080440d400c1c4006071100d014000d40b12071909496071115124403001e048505450000c41c00f01038520f101c10460605d030711030703194801c5070022a11402002e40540d1201100141c0d04280c019103034140a404c5e040b103c481c002c0005010700c01e80e0b00060500f9516003000642e44000c40e20444070400f001245004600301503a032458000d60304900341e8003440c1d2000e05135404c0c0342d05510b407890805203043c420000380c3c00d000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 526209136 1250 526207886 526207889
    0x211104060e0f0108040318080318030c030610050105090409051b0117010303020309060913060305061e091e120c030d1a0901090f09060f0911030303090304060e0d02030d0207030501050a0204 83
    0x103131522013407601c0d991411101c14142d03450951940c042840001803980d820001010324504c00050a0b20164003402090308110610743ca081c801d50001052084031501030702c210044032000d00741280d48000708404038010703080c0c492000e070003030103640d10b405250b00c14402d59100d424403d90f5110082c000c040421546808280009070041c2d100f449120a40c3c245070004200b01c1c4001058501c03031110000414040c2c0d98140c0044030150898004d02c041500c025103c14440011460400c01e5440c18561042d50b420030301c4500d0f4025503000303806406001007403060a1814201100c9644d51704100441242d90703502c9803030342d006030318a4441c890350391010100c684150408c004102d8000c1d6480c0c2180c181c050007514810fa5209643e0b80d0803080003a517240304002401d0318422010070080f000d403c0c81007100e40108062402500101f00b080500a000f10071101562658103142414100107404141e05011a040c02505442040d009111458000030304408580c410f2000784020340d6070318841420f07030249 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 526210386 1250 526209136 526209139
    0x102190f090f05090a06030b090d0e0d080f030c12160206070305070f0c110409150e03030f13030e30010c0f0806062203060e1b01211104060e0f 63
    0x11071024001440c0180c069500200d1171400440d40a4898a540010340c600340c540075550f41c0b001340e0f1521002e8111413888840b1104803141030a0000e80e4131400286c0c440c46104001c01c40d0004002180042980103884d2104805184040d0300d1404000b078034400c4009201c154054490a07000030503c030300c20302a0350711601c090740e03c84418144801080c0d410030020310048844001074450328216850720312400c10410b024001a6032420b16103001002180e4680050341d00f0b540082040048054a09070300d41c3d04910100103c100081050400301e80c07204000304000c1e4092044110748000307600c403601c140f06d0030258205000101001c50800c500b281c224007182c401050400c40000b885a02a00001d5800300c40601214a000300f82074114440901c81007080c40803980451003441445a80c1c815000035403142c1000340480207030f0030440c400f44030783c10311345a0411040d022143c4100c000240d01c0b01c48984e645001780a8180340604100c416007003401003000140103a6502c990301d1903c600c04007120f000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 526211636 1250 526210386 526210409
    0x140108370c0e07020a0213050907061404030807060f0e0a030807261609080105070e090406090219080c0f0a140303040803070507060318021e040e0102190f09 69
    0x1409001889828a0400207980c00d8850140016094685109862107103840340e02a25000003a80b040002880d016810b29494030701d8002040b61041000801c1c1c01500d290381000d009480d0920061038442c8940d400c01071034140e000c6500030421445030018102740c4140c200a2201041c130b401810798071481c425020300000e0808000c21000c0d40214176000c0d0060740d405000e58011303d64800d421080d1401c1d2143d2100be03445990340e244c41ea130300600200280003801c009000314201280002c01d41c82d0a26120752044000e40c01040420620b40c1c409e4088990207000d00300014800c00c20f1004c481c169200c0c142e107501980245020070b15000c2d8074601d411000501c0b0003003040c10600030044640c82c008005405110402c03000c51007150801c06000020b20602c018520035040c884002e0507181280704400b41a0785007809000141c0d240180880010401d0295804104103900080c6c060f00c9403900c4d895440d4030000301c1940f4402010303440740302c8a18075202d0142003e07161004030340303411503071046491048 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 526212886 1250 526211636 526211713
    0x3060b0309100507030b0301050c070b011d0c09010c120810060201090302060f0709270b090106020a030e280503070501021501030f0312020a030b09090d05070201030b040e01140108 79
    0x40c1542c0000c1c0c016071135280011360707502024003003400c554003076030940c60003d400700b42e00e4200046a82e8150141081a1003010841c69016030031081f60b0026180d607501c4000407405d40000d91244440003802908120103c00c1117180e0000a41404029038960040d600003241c00304440c1e0050160306150740d03150340209010b659590030b1720010540500014200016000000340064010031000744000c01c1c0c6030f006445e90280680c0c0c070201c030061801c06001c0c10312140104241170b00411550000d5815062400c921404d00340000c00301d40680c0240c4940110750510541451003050415042d200305900b1521080d4882c001a03a461040341030310300900f40f00700e005000180c840744600d131a2074420300300285500300c0c800030701090f600441045000a5582d8420a009280201d8000e40003090103015002c1036115090040082c4100c41003e81415100e40410407180c0791548208103402c1014000c00640c10b504226200804080c840e9004a1041c40c45072031812407280d0540340700c001c611a401041c1c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 526214136 1250 526212886 526212913
    0x3021e1303142b090905190c18060201020a02070504052e1d0a0c09061e0c0212011b080105060307301506143705040603060b0309 57
    0x14600001607a600340203060b88081c1541a601d1502c22007021240c5030300f00c2e00c00d50741c07006090080c158000200141058180421503055078800e0380681042180802c1c407500030711003660140080100180f10f190700880c0000c8056042d1f0240111403c02e41c01e881a03280d0f958104400d4444c00c1d902c0d040000180d1030b50105081d0a170340e2680d18084480400300d84141d131a22411108000c810401084400c03100c10031220300c0003442410450b00180c01e00002242c14490000c5c280c42124140301c0040c1440d10f108514140106400500c00c0c0e030040802e545440c1c0d0b80f0040380a04103031340c102a0b43d00006014450950300480402d8165100503042c10300316921008111480400c10340d0300011400900c0743c0880d41c0c485140220007070705460201155028094014445a40440d4091800c0000f41a08840000709030800c845549160b041c11000e144203190040350204480355048441d00a03e5102d00350742d58200e0050000c841681e05c0402c42d181e038442c0407003618481110307201c106030014000d00254 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 526215386 1250 526214136 526214153
    0x10b04050d050f070f151d0618130c0807020a030e04090f02040f090c0803090307031b1e05030601150219060213060305040b07030c08070f03020f03010603021e1303 72
    0x1c00b4026000c0b19000c402a00d02d150800c030b0281c200400c4503010520074040e400a030501006016150324004a0036520802c0c0c100c03603402c40c5441c2d584603090004002d02403041c814a25001e0b000010000c01c000048125250300404004540d0b20204080d8400980003a00106801041c03c2c2c041d2904ca644000d84010040203000441040f500c0d900d038819004056110380c40351021504400307a00042c1d1403003c2c10071001081c5207138005941948100060718041d2804a86202181d61014001240215280c41c159444800d90051042c1000208642e00040c22400d865400c484c402d605540310307641c0f80c0000442e502c08600c910340240e8000428210305440014101c3d002a000e50780050804603050103002c08002e00f5440440004c0d16003003488140050800040d0300003900c2d0a00f001a84d030b40d07800c040d0081600030054014001c8600e00042c07810700a4044500020740d04000f66a29030b11010003800039007080e1691810544264003101401c4100c42c100e5810101c0000c40842d0b140c910742c2d8607680d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 526216636 1250 526215386 526215409
    0x11030d02011e0b011e09091a01081f09020304050a210f0216060e01030605100c02041103160807140a0306140301050106091202010306120506061e0109030f0201030b0901030b190203010b0405 83
    0x2c10100602c00241d007d5580314040c03e2030411000d60045045202c0010529a4050f0918220070612881054240f0701444181c007256501c14000da12941e540c10004d007072100400d0003a0241c07010700da110707200000c2d84001c0c02d000d041c980c030342c40440c129042d0200c0e41c9807101140e400b83e000c507441080c4242805504019070b121014034001c10380c2d54550010401e50300c0d5540d21040811800b0124004620709070040400c2d03811070203102401c601d4140c2c0c058a0b122007141c1c0c003806200000010a884512038141381000b406a2a5043d685941c5544010000c0a9610680c00035822401d1030300c4040c84c0c107004241c12620035541d0540080d0401c0f01e50510118000000c03030606641e040c00242002c030301c1c1d1350488540c0c0260041c0910b0702c0c0c844180160490801031140444800745070342c800350307a00139819105072038110160390003101035480140c1c01804c0342e00d041d42d404107504000000b00310b15299420b100c4c140c8004034000c0d40302242c184800b40d00083c007a42c0c001d80f9046c00148294140240100d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 526217886 1250 526216636 526216697
    0x108060f0c0307050c1f020c01110c0a02121002030f04110301420f05040c0f090603110405061324140702031f020301090b010809030d0911030d02011e0b01 68
    0x1b9078514011104148003030310607080c20302054000c207248102d030030207205828160074114003491902240d200655201e00594900030302c900309514040440620030401c0100c0700592407801c544c0c0e0f042030914000722000c11503044881881c0b0b081e4461007824180034411480120000e0111284203411aa58a081c011045c4009070351030f204002112611004000d8002c05244250000490078481403009031202d08110a080c4801d28440c54001c66100410f20110b581c0c9240004034404010801180c5100c1e030f40c4400e84c4131f1408030b11000d60700c0004100c40212141402020000c907010301e040300a0b640b0000030400803801c07452803a0b000000700402041014401000c3e1001041c0000e005440c81c0c0901082210a560110042c407180d07940d0311400d9094442400c2901c0c80d487d00d0103003541da074415440034141c4241c13610110410003900e640f000081703000050944034000d4120b01300a00030041c22185c40c2c0300f8800183c045012400a1090059540c0103075102602c0300000c44444d455101100d5010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 526219136 1250 526217886 526217893
    0x30b130303180b090111030426090a0803090f09010f06030504081204050a050f01092f04020a0c03030501050f010c02010f090e0c1c1a12030706060e0108060f0c0307050c 74
    0x700e00d00c1140b00d0003002c1d603200c1d4030211100d0818146890841c1c11a1402070b000c500e0420620010407403065200700608400001800c030110200700c06603042c001c80c44007075004000005e0100e03105030b0110181c00040c0043d100105510400390401034000000e100b4814490000c0005210061198011951180c0a000e084e4609a90344851000c240301c06c840547d03980d0040c09841c4d08100c1d0502c82901e4158445000340072110051b1215109802c90050401c180341050b60025407603070507400208070300032004200315142d195081010702a000700110480000349440d0001c00d161030564801041e410040c0e4a56031109030680c010f50300120740032114030901004110008114800c443e5062281c1400c164607515800c05400300b403022824140c0d1072040301d05007500c4e0711078215010680020040c00700c0b90701030b0700100c03281d00c00d0642c480c461024009500b0301201013006429220440e0480700b54104030b5550303030b88046c8512462001602d0320014807200704086a2007034441d0016100d104039101c1136 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 526220386 1250 526219136 526219151
    0x60e0d0807080f0c1207030e01030b0102150a06080d090e010e1810060317030f0c0d110408010e070b030906010302011812030305093c030c1014060a030b130303 70
    0x111500d03600300c0c1c00030f50031500001420104a40050002044005000211605000059901424408000135694100343d0b481c044171149a00c03c1018082003900510210032a042041e0004094142030240d034150703101d00300c002c101d868410000b4070216103106000c41000d90a040c8100030841d0007401003480a40714011a41051001b0322072040f107419508400030725280356281030000c11000c2c0d051407001810038010403030459488021694880c80d40815250f981c0c50090005004140e81031080c2019400410301141070303101580031003410780c01c100c01c07102841e1f601c0c5040c0c000740c407046402d05140e03004500100015401201c8030b030b00d000600c1c04001c0c0341945405400700312256902e8145c0000f44c0303400c24040e5800c418009007400c0e0440c0507506401a61130208801c1d030001207024000394800b16214800d0740d00040c020703500b5280c401002e0300c100c202e008003600d0103030032000140071042c101310700070030700743d2a00e01a08002c4030b070311042000341640c0b840ca000142c0c0d09100001d80525864010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 526221636 1250 526220386 526220393
    0x3010b0318030d05010906060c0809040b01050d060e0609090a080f0304051f090b0c090105040e0402040608163303020c070504023004051203040f0507180e07060e0d0807 74
    0xa480d40403c0c150000503250301d400f0030041994510f0740480d0510000007050008995490100c0e1a007072419140802d65400c000c0048501d03102d00c030602f00b400307458420003041c2004169111401040121040c00c003030380f640e0480980b2a21041030003008500c04000c4022103280030310143d54014010003d48003000b14800d03101000006801c44403e01a941c0d9188804200000c90307401d40080ca5080300b03a00303060384100082c160740305a00405000b11030101c0007508543c1d850f0030940240c9034110607149460a4040e0003081042d460003200c040c540c0d0000d103440310642005071036042c94051070041900000303c1c00c059009602c001c80e05d1032580070f00b11001c5003a48541c001017001a040c40d5000d0222850b48401041320365034901d03103500c88241c020500001c214001b0b907900e60400c1c15a120355407602c540c41c18001004480c0c000500c0d50048040000c1c1c0c0046c00ea0707e601108180070340c1030140282032040941c80304018020310010410554104030103080c0200054080b903c01c4c06021300d8910141c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 526222886 1250 526221636 526221643
    0x2030409060f170c011d040b0607030c051002090904140f0d021006170607080c0403051903030b031504031206180c0f1409040506061c05010e0108070b03010b0318 71
    0x20464180e520300240100045070b04105140101c40985010f0041c00c0309200c002800110b045420b841c91002c400b1b054182643d0700e80c0130801044004040300d680c0d8042e850082c0020452141c103403400d0185040307503480f01c802d60003150320200c0010107038200c0350356550f62100c0480b440203c402c680d01c1121030095012804000c0c8021850442c0c0041034007115406880c1c0c1500d0040d00458500200c0c4a281c1316a990005081600031f5000c2c2001521035480704210303c82b0303005039400030305103211b01d00085d604989034042c08031100d80282c1d400e010307409500d0141603031140c001c407400545a88801c00100828414007c03911086891a808540580d942640300c0400400ca8134000c0c1c0301b542c4488410030590000c0040c012110141044c511428034881500010300908241d2400703543c882c0000349840c1e0b520000c036000c4441404210005d000d1000e4401c004110900804000d89d62200020489101c0003ca100441c0c6e1014013881c60f680c20f10151800540015040058212801c54900640401071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 526224136 1250 526222886 526222889
    0x3120203040f0213060602060c1e03010e04170c1b01050915030a06170a03050703090e01180608121602030c03060412031128020a020a140102060a0506010c0f030203040906 75
    0x81100b2030007018a0700400c84d82e41a1010480c291a00d40f8600300411900482c1d440c0e0311a002100d11a260703e01e000104008042c1000fa01359040000800070681742c0700c5a00c11400b840c00f59428418900c2141c5420f11a403148954060a503804485004150300e9068040b050340074043c940700781454580c01c003088007500b001d002032140d80300c00710400c00503291794400d44004002030b0904004446d2030803480d90b107070007820310081c0411400051403014180100c403200c2c024601d1840d520030b01e607074803440c8200c2c09200c4005080c441e41411000a04004001401c425283c41481250315010308074004005c800f41404c4126098006e20321881001e40d028041103121b81d0150807040250700052100400301d94803482c1c0f0315000319080c049900e044841901400c101080403012080c03103941484241e280124070200254821480c174804a194034541d0301845d408070003030b02140e100392141c0310400f068440485c3d81c103000035403200b0722a0125a001140001250280c01541d00d820748076000c940030f45625 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 526225386 1250 526224136 526224143
    0x3060111030315090a0504020a0605072618090c0d1d01020a03020a090603151206140a1e0209060f0708120403020c0a0b1c0c1206030c060806090103050c0d0312020304 73
    0x343e0071072241d905040c900560b009811003401c02881c68564002171032556103005110800001041000c02c1209441d03800219102121a5000c80c424180300305060b540000c0a0182406000e44840b6007030070561141801441c0d8401c000e800d03d1072000019000f07285160f007111340c080941d80c01000c0140b080c4003c190350070103580c4c096515540e000c3c002e800c6280e41d91010040501c1c00002104140c410038850040e6100b0807002800c100b480e05000025040c52007140e56800080000d112581002c0d5014440c205440800002d20ba00c88140c003904a01400c500180c000400700401c84051628200902d01188a60300150402d1907450041698102c1160101e002d03a0105442e41140d1522044060040281d619410b25111660000600349960f0080079280143c45a000280b4a4000c0b4101c5c7c1c5850b1540c13100304500b07a900e0501000f00100c1340318640100c1c10300c00c041661818560201c0341039903001002810007071814030500821585215080c0c0c1000041e0a80b5080000c0500045004600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 526226636 1250 526225386 526225411
    0x305150a14010801080a12030c171608010b09010e060c010213030b011d040f060902040615050315121b0d0f080d0c020115030b0408040b03044202030601110303 70
    0x1824001403c2000180c00805d0140e114014040024420003141c40c01082981b0340841c0390000c9060940e0400341c2004601c4008880d03408110700045105401061a00745558882c020b9aa40740385002502c01c1e83c205034001035240c0501000c60500b100109030b0f98560f280014980020240d500744809200e03001203448040c01001009510501c0c00100360020592607607160504240da07501520002281c0004c06c2680c54211803015582c483d40081c0082c00780400c80b8206134110b220040160380122400711340000d400d030b480c507458200032856074802254140100205c0d0403980c40b0902c507103404010241d11408101d05100092513500c83d030a0010f2085000d2a1103c00c00304009054406220891046a01d072004298207180b5076210182102d400a003240c0350b42d01c4c2d5040c0605c0d20b110f5604988805c2c1c5001007804200001507007600c220214503051455103291806803180712346101d80e802020350301c40c10150b1003080c583e0760045400050505008200802d102d0001d425604111441c03141c50701c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 526227886 1250 526226636 526226669
    0x3232706010f0806070f0c050721031101050403020c0d0c0803040b04091a060405040b0a0909080c0d020307021305090a020d080901030c090b030c0702010c08040807150201090506070305150a 83
    0x12010b03140c0058034185002d03210b40d14203080020a2044000c001d40100079080e9030b150184441030208034040d00014240200e030011040c00c0c524420a403000490014080050022510314184079050146600d40c0c09422185181c0303041000d0705c201b0040c10740e282101590000b4071074908000400c000d1006048140c0c942d1724040241003203403000007440e0300c00c0144021420f82592090125803e48008940c0001d10342e0461011850481198101e440501d203086100010b010b042009032000c00f0150044a0094008440490300ca0040300c07002904000741c2001c401c854001c54028a038400003181c200c0d03811204540006000b90b66031802a01c2e1041d0008203000d15580c54099200158030900f0710050991a242e052801440000d0010101130b03004214407085a124074691071407a50400d42181c0c03110f4844c0d42c4591104000e1103040140003052034000001070040c007840d20300a4221020b00520f0350744400035005000020614512107041998220701a40c5540d1480c0180040702070709080003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 526229136 1250 526227886 526227899
    0x2a030b09031204031809021303021f0c0f02010e060a08010807050613030b0c160503030901052409181f060918060f0902060315040c0323270601 63
    0x102000303800100690000c00151030b800c0c101c4014241c00c02e81c1072403c2441191054024402c00d83d0a40010764218000180328807218605048001035038000c0326050500341c00c07a420f0350510f01e010022240070079001a0070a01051044224801050040c1400da25610b41c2c007000541c00d60014034450041a1124014022040c04000f02c9026000a0340d50f185407101c16400b510b0f0104003031000501800d40c0b0030006903020b400806841381e400340e100c0114035044c0c451800503207c0d04201e483e20768541c070700390010711204803100a980c0d081c0001e06e4112030081107c811300180200041c080410100011b5035184000810041c01180004c0000072942030390250361808d00381c0b50b031548404002810401104d0243c014a8241030000381d1080d00001c02c25810083c0c43c0c0904021880654403400c04410012403104207807045034540e108403410484541e200c5400e4080b101c281c03000c0c90a80e0034200d50841035103010302c0e145421907600f441c3d800c1030005100c0c49400c102107034a41200150090801000b41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 526230386 1250 526229136 526229153
    0xa3008070e040e030403081e0f0a0f0503011406070204061e08060f0403301505030610030c1412160f0e160813020d060b0f0f0a050405042a03 62
    0x194908460a01c41e851003042078944e24010b42c00b002d007045a00240001c080c10a040201040228820071191520304241141503140c014221280100e04252030f2a03203202e204508036816500703d0300744e40f40c1c03c95486052204540058a0407031b005581da00c808902d07990150170505144040102c9024903a0401100b1070600c0005802003030100005004e110020b27401c80469503079240c030008907000841160030b004d105078034040c11244102e0710340b840590407015802d00601c2540c20640844016889042143c00126114440a00007010002060260000a11340d81022240081900844a92500100e030410040035542140011130713000420040100c40c120700010410018141c0551810703600014209050031100e108000b11a000120450021102e01c0642c03a00030380400350780354081c40e10030000c0841c1d0200511070300c030210340d000c1c02c2e10308401c03400420b40014001703500c054644002d0001610300a0700481e00d107060060784041c5195941880341d908503103c4202c0c00b1081c91030070041c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 526231636 1250 526230386 526230407
    0x61e0c0c04090b06010c031b0b0109062301050a030207060e0c01110a050606011b05010e15060303040f1818030806130912080901020d0e011d01020c0a300807 69
    0x40d0b8140558040403e030211001903101d042030a00351098802d0b45001c0390003000003542c02c8802c000499181080c172040d240b0060680700e2400c0200000707900c03050086106004240384080180015000c106554031640282040c54001c0c200076007403911175641c0409689041080001d642c0c01120080e20a60307100904181540d80f988c0544444615611003a45413000100840d041c018181058411001c041d0f041c80f0703203590882d00800008400c001d410343c40311b0250115404640b0b2070750101e00f031440c02000315804c0300d40c903003460b041c01482c0c00a05c1c600d08003030a64280c4100d6541300201030f011065988107043d981300e5990080c003460410100720820500c4448000014500b0351014005800c24002e49020806420031a11a0350303541c04071406445621400100b141c108040c000020005410028002400c00e80281c051048400010300702d0189207005055580301560361000b00700401e240c0c00f040c480f1031010b444070040180b03042d4421007a248941001404000800500541c0b2440c0d016 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 526232886 1250 526231636 526231639
    0xc03051606090203120a120e100c0206040501110408030406120905071d070c08030402090411270f040b01050d1509121805030714030a0209151f09090209061e0c0c 71
    0x6080c01e840e401d00605405803540040700c490354503406000b545d0700400c84006027000202c4140300004002e503000b911548151422282c1e5030811090344000070210007550251000c0c1802142000d141c04412602d41c80104000703088560742e001c85801103a8103101c01009000d0120311100016034031100c0e100b50000050202e030030840720041c168000703890354044035082601101c1e800255102d6003840c46010400c024115401034481b4080450082d9914034141c40724002c01ca084510b58483c00b070450740103402c8500034030f031190540060003646003090500d204280a0f0704001e03650000030001c0c40440b0303621001525282030310303107100d00034650081003180e072100002280d108213840c007400720350785890a0052071000d42c100402041203407030410007114801d80003895500941030607100a4031040102c1f1185008070a40c00c9c486042000d0520314941030285551801c01003460508404000d4101c082e01c1d50744090304000701e54080c456201140c10b45180c400850344e0741c000800c04245440088403049 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 526234136 1250 526232886 526232923
    0x280b0a02072d171e0105070f1e0f02031c02030609010602010c020a020114090a170114011203121d010f0e0109110d02191d01120b04030c03051606090203 67
    0x800c103140000d541c0100700c1c0c02180c1e03d650840c00908100e400e140c4240c0720184c400b0740011001d0200413054105a004840301c0d15034400040c03940c50115280303140c0317400805103600f10102001c2d0452041007004040c103654410391f0700b0116460345052880c071503410b61210349134020082c04040d10704500b900d401070420303000030054504824030294031460704d450082d05010903400c02c1c4685090380c000300c80d070100c80181440c0485803101d4440c0210003045401c1c0c4559072a010b60041c1e05141c41c1d480030f0680b2000300c82d4080c264603541c1c0455400c1c0740c490100d0a0130b81c649613040605841060103507654102e40700042400c03180030082004541082641c0181c6a04015014001c98049444e444200400b51401c0b00310405900200d03100a904810303600b042c40b011200041c480c4241003c049601d041c000e0300d554144d99a000c05410300f0260007019200d82d041030b002c00e0000b80141c0400580fa4440e08013281045c4210102101a050740070091300e000f51036003000800c518062100c00b841e0300b02d10001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 526235386 1250 526234136 526234199
    0xc01060605040503060f0a020c010e0307050d0c082b1a100f23070f0c0e01050604051509120d17093f0304081801020a02280b0a0207 58
    0x183da034085c00703481e1035200340100000c00c0e481202a011640ba24420744024031000d4000000b00342d480c1d10104043d80d039400307030340702c1c0c01d282610528208103115007084003a82042030700e0301d0b0006145d030031481d0781e0840200306141a000040d0380c0104c180550085016413845078440041c40107100e110710340c80c2e042040c65010214070305d4116002629080469054045501c84030509103940d203d0060041c286000d8403000341c04020705c442d007a00175902c0c031540e20185643d0720b006004450140c4e01605601ca0400717201d8443c415102c6015003d0000d0042041210009007400c0500b8440340465040c0051074a188103400080b10108454000a00308002c0806e00c0082500a81c044c0b2a00c900710f402480c2103094143e0356200b002d14154942101d11351079941d09191410050b1a84851101580d407030056503158250b41c00441c060001d40e070050701d98a03000e2540c04582d40110807545210b800009124404a0310412800182809070030710340080607101d040201c020b05013002c42075800060b4103101307103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 526236636 1250 526235386 526235389
    0x30302010b040c02030d0b121506030f01142e080309030c0604080c0910090f0203040246090f090b06150403060c1b1b0b2b0e0609030c010606050405 65
    0x3192006c0a0350200050550000400070741c000f1226000c140040c81000c400c40400490300c00010700940c022070464441520034105d480c21303605402e00003130003089141e0010300c45240300c803001084100b8032001340382c15401400c07108503030401c3c58014480a0b40b0100344804213080c2003203100550082158028186458800c4095442c1003044115000d0208200450f10400300d44100c04083d041054003801101091000c0c44021b4108541c26886810400c060b000300079140711201401642031100a10351030f10700c1c1d40d180040300942c55220200c032000c10000500d02407a00ca2200e0790012032a0100d203040c0981807000152001030720440c490300d841298400c070510240b0848044070340c065404115094080310907a100c1c0c5a05801c000802101c580c10420080500c3c00c0013008480f40f4040000c894a03041c0405d200d0055500c503203501c1e4500400c2d0103048621000d002c1c0c80480c42c100104004080e07a000b1030500c41c0036540c002c0d00394800300300d1340c404940c28003600d4040c1c444c41c6007090a0518080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 526237886 1250 526236636 526236643
    0x6121f0806040213020f0c0a020a1721040f060305040b06060a090317090901060806090c03010f0303030f0b06070b0f060102190f0303091e1b30060f06030302010b040c02 74
    0x10300c001d11851494100361204c1242d07805641c81a81c1720039005132288842d60740c040d01c0d640302c414201e00c50700320002c021a010403a482c02851038011301c4010a55204403514040e11101c01c9079030740201380d0040c000000d41a4aa103122006060742d60b801103010300305850100140c44000d81024070030b81d800c1c045100c0c80759100c4055001c581c0c0092500344070380c02e481071904540c0b02d40b401058001603450300205496070440c65045c043c64003525817001c203544615544109010038001c3c00006251320781d042000c01c0c480c2c0c10007014017000940c0000c080c4c803000000383c07040d17200300340403118000c0e01c00801242d154806180d80c0d2042c3c080c009000e44a6810144000001c0b888c0300c01850000241d4450042c540300b07074845950540d003d00040117a00d070241c5400803080420f101140e100c401031440d6034950b01c51210304422515a18107010840302340314040290b01d01c5205003910f000909100c0440418072070700a0725906e001c0b2a000080240c19402c009017502c1e054000907010764241408088140d6001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 526239136 1250 526237886 526237891
    0x60b04080606100c12030b0306060d0308060d03091d06030706081005130905121b0c031c2307020f010203120a18050f1b0307030c090b0f06121f0806 65
    0x1c4481c0d030800780c0fa4040c192100c070514513015126020148002000c542c040c0c6c030451560600701d00b100c41659800b0100301038866003001c001c0004002c01c0105070541440240e9582c4548a4100040443d803124140c0315018074031490425401c0c0741c00306000850030140702280181a4070700d01030f100303894004031110002a00348502d9000e488072001030340300c45802d940841309032036200c419961140550307204a4142c1d0054888950201c480039500404000c000030421110301016015001904000003900404101c2c80c0e21601813002081c40074103040f1402070f44407a85602005c4107070b1074441c6401405900d03060310261034103550003080001040c040d0b00c000180c1c00781c051940490701030501803155000ca24183c0c07004003a440340c0d0f061406505004164042a00816031064451110110805541e41c003144000740c040b8044910500058416130440d00c0144400340950b040280d400380854030704c6e444007050242206881e018406030050140110320b005800000c084d003c1c0d42070201068864802 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 526240386 1250 526239136 526239139
    0x30a0b091e070617150d0c12050c010809011404060908070f080403030807050a1d150403140138010215010b030907060315060c020d020a0b0304060513080a0c050a060618060b04080606 80
    0x201b6080104002d0750070a00c0c030107001e00d144010000e29142c6001641c035004443c0c9a0b000ca0010400904510f60500c83c4400c400503004514115441d40e84484000780100304081d90f845004105600110702000c00307919605200700c0d10300c0c0d40d0f61f00c1c50400034002030b000b1341000b0421100704661250341c0d500c0842048d074600380885102e0300220000005108400881c1d20416070314000c00d0000c2481940c284017000640510000e0298000030514000598180c5050140d04450000c3d040014120754a040382048010300466010220700440d203464070800340e00945041030000200b00042c01c060200e0320040c80740d030600707124111407600840601948c43c0294000c01020746c5000703084d0f64602100303044258002c0e21581086480c3d0a0204540d070045509032804d50410780410340344000c00d4010701215400403a01428180054000c45031901120070503104c62251101e84008164548a900e0051248000c1d0321042c4181359022419960113a000396440c1c60148010003100101240c541e601540 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 526241636 1250 526240386 526240399
    0x2a0d080604230907080607030207021309081b03090a1205010b01030e100f02040512010903081617072304060e0f030a081b0d020a0c1202030a0b091e07061715 69
    0x4800b4080f5280c920b1307a44c024502c0384989000e220045825034028203c09000740c6101c0e201c0c0c000800744409807800b80900920341002080702c14001d15607036a20900703184030502500c0c90b1a001100192103481c031034115820820314480c00c1d0301008424422030701c2ca9102070a0034070004250f0030f2076507182c0f1940c0c080040099101d440c000301200c025030484026190060914080c0002640c8007402440002d40440100d01b010004c1081103441c1c004001c1c0845e40ea586010090324010103403032807d200541f00206000200341c40c4002103c402c1225840142100d003030a4886107444001082101e1400c001da00a0019052540c15624081460400150000c00b070b10b0744c450040100c680c0c0c8003604540d00c0410300402d896086403a80c040740e0844001e0140c0c40e08200705454088a00a07249184030096040e44003940b4100062a03c4250580c00980c01c4260352940501d08a900495036080200784101e0700318080074445c0680000b800ca204050084001001e46811101c1c001c0c02d00300344c00c60511840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 526242886 1250 526241636 526241641
    0x81b1906050f090316080607050c0303070518040c03090618020f09070c05030712090504020306010e010305091603050a140c1e0303040b040b030a0507232a0d08060423 73
    0x40c10b1100700d03850800c0c081c04540c1401c2c500c644464913020355000b8000a030056401246485218001b500d50141c0c5540203180340d41c6030601c040c0c80d05c0e4000e04401c8007500303c401e08080181d6841c492041e001d110390700d020400f11002d150101c203d910081e06150313120100b43e0f101000d600c42c500707205984201a60402c132513444400081e20501c1b0107000007065880001000010000044c0700380b061184251218140c2e1911a420041680412612540001c880c1c21b8060325940c0303c0d8000c15003003a050000c0d00d559800314102610040040e40090351107034401d441c5007040043e200c0c108400c0f8501040078010005041001441401680044155084004000c906280c0d024421200103114442c3c60595030307640c54051085a400884c1d01d05100303842d06000410715406640701502d40b01e080c0004800d0403960140f03542c1c1603006202e0354000000c42c040e10720311120308a170242c0010b4074001c00800180038201d00082040350000d02e07150003a81028202a07600c10000300c0050a107542e65010310742035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 526244136 1250 526242886 526242907
    0x20d120207060207140f010b01080403030c120e011e02040b071407090c0e091503071806030609060b150c0c060d2310062a020a0807081b190605 63
    0x34022207501824841c400503444080103140e10201d414a60607105640c000110661034900f01d1301d0014a4030f004c5500781c00024000780c800d902010008101d418641c1e0240c030408910412120401c50340174403a075403041010b001c5910000300c0400704440003002c1d403500e420700c4020b00740303409600d10003805038960007d0007007580002e00c1008081c1003c0d030f0003004a05a0544001c0c005a04952000d01500710080840c0c0c1140007200340c460500320107002004d119203030907106100b4001c8132041c10185540d072040400010a0f502584800300e006001c00726151800e0410040303081e101e442d209026070340c100455000514042050106c81d1011249207413541402514900900503800300b800c0da1509540025204840003640603014000c02c2c611100e0702929484140c0740002049503080341002c20700c0f805000d1941148101032154400303403c000b00c00790350b11201480c01515400a206a41180d58140d0030201012440e406a0804a07054400600841c1e048020402030740114010030000140300e90710b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 526245386 1250 526244136 526244141
    0x6070219090c0801090b030a050a11010c02090f090f0a0c050607150e0a060e0d051605190606080d05070308070305060604080d08041b0f35010b0111030406020d12 71
    0x804000c4424048002e000d080104010000d0082ca804540342100d00c074000d0600280c0704907125880307802080c404a00b40c40d0b04846041001e01c441c10821803401590043e154912054051194400706494900b021400e1509107001c12024a0469214141050104840700818030840300141d840d0f40c0d980c41c2c54207041001c0300d040030a9440b21828070740c017000da141c400945180b245001d00820042d54094101c4640c5587d030703006060340090001e01612040720701440c4884850b0b032080040f105090a00605881040c848a9054580c03568a5800f080700c18030038000c20000620b9440c1071032800106c3da030007920f0068003a043c0702c00c044daa0000240542c03074920448002d440440200c3e203c030000018002d0406208884c1101c1c402c2d440d1841001c9030520030040380c01c0d500b00d0041c1621043c02c092060b140c1c9a000850f200b85000680c1e1900465512618100004840d0784008a000140b000024000c1c181a016168841e030080004010443d40801d6140c1c40d0301c200d00e00a1114124034800b40302 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 526246636 1250 526245386 526245389
    0x1031502040f03200a060509120f06070906030c080105100f030b12030a09090603021c0f0b0a09051509190c0f0b071a090309060c011808220506070219 66
    0x181420a0780c0c0030050204200c030102038030000d00c1c0c10f02500f550b1042408070705c00c014491030300402c005021403002460b104140320f02d034900150865441c41002448149441b0007a16050040b80200206201482d41400f4110781e034047c42c2400b050342d52510002c290350039028000081004100300c0702d040c82500c83d410039a4002d500500004200280c4404903840354030090b00304c1c0101e000c581c0009607a818034010f031000c90303800815030300c00c240507009004502c907100b880803030368002014000d10004841c0901d040c081c6803209000038407c80c0e10f2800c24545080720880f000385a0b012800c00c907101200081100340c102002011a041d04020700d4030320045c42c540e400c03618030350b095164082a540b0000b0040c140150194442d00888140940b115400e15016207000e11141c004021042080c100140103003808141c1c00c0c00054103005032041000b0342d1500071404c55003000000741d023001d07400d241034250303012068400c4400e104914100c0000c1f400c2c03040c40300090140d8580340b0078034001d2607404a07000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 526247886 1250 526246636 526246649
    0x60f03051509090d170103020d03052b0506090a05043c0b0f010b0f040302060730080603010b010917010204150f02101a01080c0d020f1308010c02060103150204 70
    0x41c0605103643c150f03481c0d500c1c0c200701c200050072030480c52041078054140181203a8014040804110450f02c040710607910908500660034001804e504806d0900e40b01001c29518400b40052103041c1a01007003041d0601800c8580708605000600c000310ba001106030100403c030000d800c422010507028a003060b2a5460301d42806c401100f040030501c0b034a0354800d072003450034108020050707886130b451031002d015124080c07d040e0010b00007070005040c003200405505003d107400c010304d840c1c4541d041c02d440398414001644140c401c0300300c5580e1500141c1136130708460101c009211543d035045c0001c180d005903200c1c40907840c404824201c1e841500394121006003421080c0c0c445110704402c07001c0c11035160203d1110051082c034100c010203c10a10a011305242002030420311420790400440b1040e0000e0200010b40804010301ca0b0240c01c3c9100524000c01414011911041d84000e41c1c44014041c1d4000403060f4100003d64200b140e0206100e41940d07406402d5811b000300e140480c030024001c0c1e40004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 526249136 1250 526247886 526247899
    0x6040b160501060b27010f0203040b0a020a08040602010e150603150415021201140604030b010504150f0f0e0a14040b07050423210714030a020303160b0106020601060f030515 76
    0xc045c424005286051200410110848a42c0c09401103a900c07412201480060700b05000a000c1c112400c0000e10704940c551040700d01e054001d40f02d482a0754840e40c08040980e540b80c81045c41f90314140318000c8441c640c0003007480e0a01d8040046905d0b4104400c1e01080402c00c1d4000808020030369400f0121342e1003049046484403081003601d419204207024002c41d02c2c4880700030701c0c06403908004503019240d21403080c855507441d1005000c05000301c40c00f540086c15440340e0100b185900002c0001c0203007000b01348884528604502c41c03000c00350142184000504020b83d0082d000781016100d80c1042d403003140b28170141e880d103204a03864025608081110044514800400079104401030f07a242400c40c0e00d40046090085000038280f0001c03110145a04429020810110060050042c1c950080c058031403070022980000d00f90703444018003018412041d0901402c0c40943c14074507014080c603000500107035041c5100601020b40903480c4000309515400001c1d65141c250000352084440074040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 526250386 1250 526249136 526249147
    0x9091e0908040f0918062a030203150f060301030209130503030a050601030e0d02120a0c14100b0603010f05090a0204151d0d08090402030c090d0f030e06040b160501060b 74
    0x107584a03100390344094102c3c80d0041a000c40038403078500c01113105011140007100c41c0d900c40e005400c2d04501588038644da80055920803140c10b424251100403507800682c3e030300d8110740ba001d90a14400d00c0901580d605400614152140403c81c1e05481d0101c0b4501038a81d03030705031494491061458001d20300d000102c10301000c8011504010702804090b00e083c440c0f0304460b11002e90301c005001e10340005900a000001e0140304034401070142050504d00b480d0300c0c00d4a6120680542015007a004265114a83c441800c20b0103100780c90344d2210450b441803131035141411440241c541030050903c900e107a480030444040e25a41110300a1189010086039a40b84c005c02400d00828240c00f9454111420200c09030740c139041c14102c40559010381c0c0305090a43e40d400b0b01000790001404500c09501c100403944456440c03e030144001c0340308110350f8424040034039008210000300c2041c140654000e21040c000d030707001c8405887c41c0281140300c00c1c402c21240d08006014000719404201e06e172400166 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 526251636 1250 526250386 526250393
    0x9150a08090c0402070809040b2d03061303020d0e1305010b030f0115140702030304030204061502010c0f0503010314150106050903120403050303040308090a1b030b0702010c09091e09 80
    0x1140c82003070310106a981a2400c00184000da10401c50000d101c0e5070f0030070810000c0c0c601a40009075444000c0c081d0000c912803001c0220010a1080d07111151a0a420090b1420302d81001500c0e405520001008000040396501079607600180722060140071f410380c82c0d8041078550440b0485226000001400107513901d9041d0b1450358000d441c09010480f0743c400103e60041e9071001404981c20655808582084001c5034811540010500b00d0345400300304000405680c480c0645409400740009802c1201c01480020382142c007540254801d20a0404c1000003054110054a0440b03801062280e010b04074080c0c01d0f0f0414500003141d1403410080c5c2d0010982c1603000d009003050310010b5040301c808208071113150781503004901c4000d19541c420400100040d1061121680003204c10049822051940d540c00844664000103960104c3c40c83d8010401d020707051074065040421400208064030110310018000e109038013810b441302c1d0f19a010075280010005040150a0040320300b00051045860f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 526252886 1250 526251636 526251647
    0x906030c0c0c0406050f06090f040515130b030a110d2109090e2e020d020a2606041a13090507060212070f08160506010302040e0a08030c09150a 63
    0x10500041d48107540007000e0900302071048000b0781e40e00810490f06250240100400d039400102d00c190007075a4207144800c65102c0780a218000c0e05c11005003182e50504100340300c482001050746100090902001c5690380d1004951001c04036005501c05004000c00c00200e80046129040142a040b901c00010308402e0494042070000c840e9507603402d106139884898401340c44130031650410030307003003a201c60000b0780b864250410a80c1c04505010008440580c8030400c0341c004262000c0002d800003010208a0f50090080e1400c2d201c029441040c1c000f000520810302100401071401185d603031400a56664003c006070300d01440081005244800045000000d003400c00ca089445218030740703000c628035001003508018000e1500d400c0341404c0d500e0700c42c207403075250307504003550f036558108820030301d48034012a181d0b4501c0c050f500600080d4914410b210850f1400c1000380200d821504220300051400710449410441451180c0d4849201c0c000048140c00d101d11501f0313101100184074586160803c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 526254136 1250 526252886 526252897
    0x200d060e13050c04150308040801050103020f0405070c0b150a06090312170c070204020d02280f3603150e06070c0210030603020604171212070c080906030c 68
    0x244000010744a22095001d20410700d14024000d4110f07588040740c1d4200741c1d03c40c994a4210791460601c481e505c4e110110346034469080400d09175103030401030095050451228050a20030f0f01d00300031b50300e41a00d00401d8901c00d9100200500e9481021410a940344a10411021030050916138050b684040c054081d42c5107110407a41c0d0f42000c028004654050704d0890b0301181003e0034007035640e807989042c154550251200301d0740680d09000c074270404220380c80035041e10348440034035403c080e00300c40b20300c0720440946401c0f0003004800e20800d031050368840c0f4450256400381c2d19916440c0d42d04480210009801540110703a90b503101c800009001183c5c55030b00c06000c04081c104030004042605070f0304c0300d2086030580081441001d03050014104800d10200744e254600c1c00141c01034403640043c6081d4010350014803046010400001155000d0002d628000e580e01c0340f0600e020010300343c00c20035040c01040c60060280b120460414041d02d40b0407144019070041107030765689001184c2c00c1454021 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 526255386 1250 526254136 526254149
    0x6030c080f0f0c030d08331903020102120c0102190314070801030b160e03011b1b0b0a0513120507060c020316140f070807030204110f0d200d06 63
    0xc00880c0c200c0040081402541000f000d805407803102d000b01d2041d100e809019148094001d510b222103010600000d40c00c011106001094a80783d003400010080102212062460300d0031424900300300503138000400d038202112a180d06030b00c1d4002144041e00900400048413200d0074050301111001e94158000e030641e0004690070503058580e84002c407102c00f400d001c0100102e01c00d0004ca140e07105991440c01c0c2e103484500d001c84452100303e0202e42135450341421003054207620080c801d8159008075914142d00b006454101d00b40c651901e0b03002401501514051403540d895021070b5121030a4400d81c6030290700f2140050b19031968120040c41548810025540103141c1491020300d00d01c04400ca88442d50410101005070240f510b0700161612480d00c502060b120b032800644004070b0034040e060041500f40c01400d201403030760040c80182ca5031418001e642000c100301c02e2440c4c4501c2c1c8103903030440100b02800554220207580d920300380e0b5585403400701d01c140c2c0850108040140c44d00a01c0c10f6071b66 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 526256636 1250 526255386 526255393
    0x906050a020307091d0f0a0e010c080703050108150a0c020c0d0c0f060804020102060a0e01060815100e010807060c0203070b0d0b0102070b132d1e050f060a080a06030c080f 75
    0x503035a18002038280002441a0400d0080b07001c20741040d00c40070710076080407c02d20005528040f0803005400c4501c1d00800c500400c401108004d60b450301803140c1401041c0c0100500441d1012001007020b8901c006d0420210680ea803130315440d03c2e0310820001e40140c40190290141c2c004a0034611102c4940e0302c1010500540410045060303441520014001c6d90706030010b042c1910340d090003c02800d04a01d01c0c003040c1d0359814000170342e04000c021405060ec0d0401590802d0304291039014000308080d0801409103000700010400c014002032800121081490b002d100c44c0300510009040c2038080c1d00141c03140001244104485503198040107001609800b11403065a50308065407441c06141ca000000c449843c0040064418a09071040c0044000c003084191705104110702500c0005500040031022008003001114501d0000c0340c07010301000c6614000c900c1c45c42002841510a0032400403c0000c0c40010501d104e030680c0105000d9903004805614040d1a1560070707641300c0c04601145040e01c07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 526257886 1250 526256636 526256639
    0xc04091508011a0d06020309011b0509090a23070212030403050c1504020f0f0402040e09010e2107060b310c05040509042409110f100914040906050a02030709 69
    0x10a00f074401c24180001400801c154000d03031312010020340006001140a540302c2071000e410805100801000300c165481e05a220b60001080c88600c4400810082040e890900c842405030f00c0c210302501050502014550180d079440320407400c0040101c450a900c010200c00d1008264100b0301411241c03600204984c155610b40c0001c0103a01420344010350010707003103000b107051400c095100e03112118001c0c0001d45819617803107047c00c42d040200c1d12034605075503d2040d281e001c102442603440d151540d200244184080d44a03483c2c4174458054018111952240003607116222003244030300c00800403958440362070301c18080c00312291003074007150865442c055030620b089010f0800e9030141e40f00581130b016503541c2c55413482c14148450402200700301801000e080f41010301e00421500e94410b0b1a6007001205140c1031256600c010a140c0784584030441000000d15400b02e80390017100c1c0c00a0080c0c1c0c00a01000c003260080000b2080980000d0520080060010407900107501804035556900ca0361b6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 526258992 1106 526257886 526257911
    0xf112e03270f0c080a0b0703151203080103030e030106122603010b0406030b06090108070305041401092d0201210624030e06010f0e0c0409150801 64
    0x89080c10002c02040a890700490042c800c2c00002d01c08400039a1ba9010000f00c018a0b120805940f181d82007031810498010354000c20070b48110320001c1c403041c14002c101900900041d07000ca2150b080401c15030405200d0942264141420180030700000e13680c60f4240b40c03000743c1e80c20405074a2507400382d0300043d4100842c024640c2003800f641d15443d00350301804cc3c030100c0003040d104007001d201014007039812415417036110100d40741c0020143d946103408103110030026120307480d640c40c00307440a042284140c440f1403416000c01c00e01c40011429903406100c541503040080c00a8034889022403950203000a20200ba82030b02808103400b5111400111141c40c054080d00509101000d1a186160075100d81192616a00b010703040642c145205580341c680b8900ca907011030082c10001507519001481036a0280043c0c070400c0c40000c172601402c0314550058003035912503518044060206 = true := by decide +kernel

theorem cover : BRFrame.Cov 526079136 526258992 := by
  have h0 := BRFrame.cov_init 526079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 526079136 ≤ n) (h2 : n < 526258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
