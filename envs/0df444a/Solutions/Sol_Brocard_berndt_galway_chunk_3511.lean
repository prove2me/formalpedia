-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3511
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:52:32.181331+00:00
-- url     : https://prove2.me/submissions/c6432af6-166c-4aba-b543-4ba91a8fd70c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 631294964 ≤ n < 631474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 631296214 1250 631294964 631294987
    0x62109031701260d050912010b090906040b0a140105010f170712060b03070c0b040309052e0e060409090f0f0c060917030405010c0311011103102108 65
    0x580c0d080002404541d03000045101201c90310700c0f560a000012042c0b800e1071071039942e88580201034214041401044200450f04100d00e441442e42c100c50000103c0100e1080021184501511400c1c41e0360712820030710040c815036191950f00001040001c02c40300000b8008582131110520465041c07101c460350040c0d00900450452103406120000c501c9103150010014004850403880146400c1c600303000440c1512103001201d0080a040d1603801c0190019642d6140348440240110204002d245000605803504100054207100f400c865014009401300038000701403204c8140001c00000b01d4102005840c0d08045030192414004085140c401d1802c1041003000031901c0209003000c0c609510707050028500f200c00a81d049956042c9400d0741e40c0042c115100488000191190402c0000b004190700458143d11070b00e110f0705250359042ca40c211524211a64240d880303100840c000100030a0b000c0298841d0040c14180000368182d249030702e01045a410540303002810400e0001e1610350300d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 631297464 1250 631296214 631296227
    0x2062706060906031c11011508060c030c16031227120e0d150506010504061704020103060806070306060e03070803030c0a09031205040905010e131716110a06210903 72
    0xc03941745c2c0c2079208130b104148000c0180c42104240311455181c204100306600c4803a80c04021500c40200130022a103030140b82254a0744050078401e4800070801c1114140e1020748003556409010740c807402c564003060000c80054070002070544040f11410b80059419002c8402e0100c203580e003014441408038401030045e00c01b410740300b2401c4d51002c03640c2408408c001000d0b80300c4003851481d4101344140e450b104015541030242d070150304040791014590103014891108020b50040c0149408600c055580610600303004080d512600080d84660040c031045070000180c60b07108005600a1883c0d03850209169280d000280240701191800102090081d100341202d4000c3e5810008005c0c01590002c00502a43e11611440742000d060100014070140d4814407603100d460040012040540540e8a00500801c480a005030304041030141c20500700c2c03005e0f110045544075008416180c1224000c00141c0192544004104520364165000d1941807203c005440c1120302c1010407a01061b15007a90304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 631298714 1250 631297464 631297483
    0x604050316170606010c030507060902150d051006050702061b0d05030a05100f05010503091006090c08090a020307030f051005040303052401050406050a050412030206270606090603 79
    0x1407251014080902a840340d039401200e181103405149124402c01c06911050104c52460104010301525001300b03006d8030041010b107201e0400060008130716400180360002540c00800b400d10081a1104800c12602c2180d8012090246092900380340002c010498899502c00900840000c640c5003607a5445604141d844c003488810ba803241114294010080d4100302c4404941508140100c1c00c0c802011141d102500c1c6001c2d07040400c0c81c184801912585d10250903450184100b24403041030740094032408010308006030703022513000c1442400525880c1e02a10407c0d9580044d011400141c0c0d0014400d801c40703a02c502c82c0707410800981401c034108050040da061110b4189010001015031540c0690710131070f00315029010003c410603010900c40c07030315403005002c038a003007100707014480c001c1c005028042c00b903141c02845c3c41d803252441c124511055000301c004d81c0c8001d00b4811b094801080410303400350f00500031161800301d00c100310f96490b07020300b01034000d0b0588008200d07603490502c180340c0e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 631299964 1250 631298714 631298719
    0x16141207090e03190309050309010c080c060108010f063c1205060f0c03040b0f0c0d0207080403230a12051b07060e010c05121b070b071b051c02060405 66
    0x8908240914183c8943c041302c21a003602003c80d90b8021542d000c0e21603282180c3c0c000d0001c1d800c0100120042d00c0550144005035001101440408001142042068080c0400800210703040c2c81c104110400d44440380c1040c050304200d20090071095405082580e603400030f51005401d0f07006120984104441107801161b00850200540e2090207400190700b8040d40c0f03019801d41a0790354070031441c0341c54042528000e1540740f0350400300b08000d86294103260042c00c0c400d80c0e03501d81328040800400300da0010a0844803541d0104041060010f00000e10f40360110340b4120796059284038610302c0e01d40d0307641e45006000603041d00040740400c0c840c209481d4034207100c0c021014006900040266a1a42441040002488a40d036085030b548100000d07400e040e03106000781041070b190002c0c44942e82006480c0c055480e40014460a819010003c03540107008002589644e680c3e60b00304407100c840c2c901404040560000030411a81d111b501b12190f00b41410213004a0240c05440020298411503201c5035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 631301214 1250 631299964 631299971
    0xc0602210c031f0b030412031506080109060b2d0904021c050705190c1a28060506030606090103110a0306050f040e0c0910080105010b0901021614120709 67
    0x14500c5000542c050042d5101400320148072541d410032080f158003030250840c40070301c00f040015240d504490b012a0b0310f4200855201204504c1840c0680c0b250b20440002c1c0787c4800412a44600784100c40c050940e039601c0c68905500910b0148561b025041c4281e516480c0c0215204051807110a5511403400200705541d601c2c2802c0d418544111600c0030041c0c01d61524000c103603030900a004170f40f019041c0c0d8101c00300543c0e0854003914001240b100554124100b0700c0369481c900c5601c2ca005110b40f030300020010800c840000c0c10898a80c031381c2c88405a0300d141c4001440710380d9441c0c060f81e50004044801c1035a81440304012405040c0c1e072031003e03524543c04034a00940e103030550000010380d20281c8200e00c00c010002c0810081d50040090b12109030001c0400080e81d0500070522a4050740400801461603078610440d801c60b6000d90121382a45004241c100c042c1da410703c46040d001002c004401c4095041404600c5c5480034003c41d00c2c400c80007074944513681034043c44220b00030b000844081 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 631302464 1250 631301214 631301221
    0x1e0102092d010201200702030c0306040308091605180a1805010c0e04050f07110a050f06100b03090d0f0c060e0120040e010e04020a09091a10060c060221 67
    0x1100c484840c240d908440150040807a51a54814400c002d40f00d019000742c440b400381c5803521880340707502c12401a070b018010200c412030300d0341b020420180514030076500c100d070754502403850750b06000c1c002800000c0803007403200401c02582e405031034140c10350300248000180e481d0f00000c0f80c0108007810000200c2c1d201034420b0001e002c07043d03024240540707454444102140049041104446044402a825841c0e00c004207001c213125000411004d0035650803200c5042ea951a21817600c88645400d400b15406030342000601c1c506251540d004280c411016808d5003801101130b0348820a50200e0320030406e01d1944560324078850440350b030007603422403401c20000b144c80f604940a40031601e451301c004d41e20801e1216401444074102c4040f2410304078940d561f80d090aa205100d64409001a81d12081c50b03070011804020030300c51580d17050312070150500b1081898051045880b0010300030703401d0040004081120300d42083c0740d0b8950340d92001c801039444c1c031b03a844100d60000f041040c4c0c00700c082401040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 631303714 1250 631302464 631302499
    0x70c02030a2301090312050907030212030703140a021b060f0d020c010b060a050d0f020d0c1e03021306201e070e060a090e120c011e0504051e010209 65
    0x703a01e9590200500b82c80144031800744500703aa030480d074000c0015142246142114031140d00c4640c002d078a100688113602d0b074a0300010200031103074400104940000076040c0805030040288040e20141442240c18141c0481010b0344a207071200110503924020500c04120747d50b8002211042c400c043c40490701c64034000d080704004c0d003020100024a610300743c00003d10b450120290340c00c0d00701e142d031030740e10300305d5800481c41c05060381101e003450f019001d20603a940344500380920f01043c00ba070f99900d41da144c0d50710101c01c550100300d1100d5023414410000b06100c07041000148060300c060782004212107200ca0181040000700d10606201401200c18054080f4901c126004642086a0885100580341d4640d03160341302040e9175030396100103250b0003041050a6600103400034802c043c10383e0b1f00301d000004600100c1d80202007031101c5955801d101140820a00540390400f040e10101b0402803425075215540d0f00000e48a50314540c0e80c80c5c40c0980e561000750100c2c1c40c1a01c001d04138481c0711844c00308 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 631304964 1250 631303714 631303733
    0xf070507240f0204060201060b0702090412021609050702150105150703020307060203041b0f0b03150111070e01090f021228090b040606090218040c030603060203041103010612030203030a0203070c02030a 89
    0x241710055080010004404040000f681ca9240d0002c1030800140ca5555a652400c01000c04403030550291000013001c0504107582080103202440000c10146488080242030507604e003c1c90b0840c525150041c42107459007905041181c80094650341e4540850174160325602036090010076a500010400042101c404a41d0351941c0009450040f901d483d620f17480009221400355140b00f14050000030f0381c4084c80c80682c181544181006d0800f8016085110b0802405400c4030f100d6003190001002800914841e007040e80010110450400d803d000a000d02060041c000c100d00b1011400e0b40c080710700c00e00c48402105020f400c0200b02d0b4500c14600818054001c88050715110314054000601c42e41c103008840c2000d030400004da8020f00b02008000080c040d0b070340e0000406580c1c80011000550303d10095018030b001c2c1441c85844940f031030401d030039900c1503000b03813100031a03154401000035000030590350001c10348000541c4a0303440e00c008680b952400c1d14040d606109808109003030191402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 631306214 1250 631304964 631304969
    0x30501060602061e100305032d0a0507060c0e130c03050c04080d0f0519080916050d03030902040b100c05060a060b040b03090f0a050f060f070507240f0204 68
    0x40003405141d503120340c00e0340c032203004450529281114002070726a00a0758400a039000109601d4000d600b510794942c2455500704507110400d0100c902400410402010b00f00e01040021800d52840e012403100000c08034021054000e2130103440c0d800304000e05020344030b04d143c0200301a06140001ca0b1488a210140001c1c14040000c01c1c501408610414000f604480c1a00e69800003040c1c40700f40340c07a048402020100c110810800280100c4042c0345528101e0364a03154290780325100c5080060792a420120088250301030350100719020041520382000308078080303406040014030020305e800442c01500d417071007480f6440001040084812a000001e10500c54054070894000da500c19640c0d00840c0d0013030140c1c202c04d00c03050004205044a0b1401594011040c0c02a03c20340f16240302c4607031800c80200380881e02c0d07400030100e0300d4541004101a540c0b100400070f02200d24141990042c14601c42d03c03001a10390701d2050030414424244600b20003101cac100010401022034450a054025042030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 631307464 1250 631306214 631306223
    0x30a06090e0601060905041a011d0402040f030203061e060d060f0f060914060114131d190614010c060902090f010914010b0d090f0803040c03060509010c02122a0703 72
    0x1802c01050f9030030580300750031814108c12601c5800b04242801964181e05605509003200b9829080300340a4489001a000a29040d1060011035080d44109400d02030000c3c1060620300d038840854011039030b020140d17030300420245c076034400c0e204035030610901800110340402c1d0814103141a60100190350341c000412110015006c01030921280000c90100d102500d840b40007510034004050f1103071824000f41031641121443c40c1c100d5588008180e4040507141602c058078501c1c00420081e0240c04008203402181610704204040c14004203840d508105c4607828100010078610030308101325540405d18454000b08004a2403400844095100c9024080d541e111303400c0500c1080551000500f02e4140c0340c03031103680c9090021644104008040399070060324070014041300c803000300d640c08004500850058204410403420b5003450b100351003026200c500103a1422442842d907940c041820320b01044448121580e614030f078801c1881d408a00100d0f0241c4184c140c220b140c9030240000c1c40e0b400c89128 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 631308714 1250 631307464 631307477
    0x1012030915080a110a0807081e1305120c06041203140a2c0309060d02070b07020303040605070e130f020903030c0f010c020a0803011806030605070c110f15030a06090e060106 76
    0xc4c2400e5030203070140c826440e000c00c80240206c0d03031f031900840000d5800a1031580841c052024200e18505e0460159a00036590200d4801901449400d018485814440042c4180b0300744040d50466520140100060099031101000446103842900314903114420b07000030f1112410080c8036880180004400c102001d5800b1741d017011008100e100d0f800c240e01c00c400180d400e00c14480306010031a0b00a000c005400381d400c005480c0000c841d41121400f5030700641c011078507460607183c01030407030f07070003500003030901c07941d510020300c99a00e10b58206444050385201241c00b40e40e407080c00010b4004c070042c45905005c04a20304244110000e500301540c104040240004002c3c81004d07a11542224006401844104014810052207010450807940e00090000d5500c1d40e94840d030085a82c280c8050002500b0b40410b10b0502c01010000c28100c003049481403802c0a10100140100090520312145c1c0c02c0084000744040c0030940c0140c000f4a44e0351070a00082c4c0300004080c1d1603c07000d01600020845 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 631309964 1250 631308714 631308731
    0x7081c0603140610061209020a050306130c330306091e060906060f05070311121809010e070e0d1a070210061a180a08060a0b03061012030915080a 64
    0xc3c8220340040340d40c1910f5080c1c0340c081142101b000303021a02030603a044401d00340c0002c0c058804100041c4601740c0d4680c2d000c00b030446458844010350413036201000c204100106094403181c000c0301c000c0101c502c00c11001003803000100c01e401900d880d60100d80b4152401100f81c24010004a14040d00c50300e40307108018568640d104501102e41c01e0081d50001140c8004a003030341030041c0f00400e6624000e041466500c904c0c1d401a41c500000c0b03981426081d2408510040105000c4644450b1900c080b9586441d560507d801e10391107010041c1040208101c1039603aa81d5074683e10510b00d441504a034910f0075038403482d00455030031081a613030600140720b02200c400300390040c3d100d00340542d0b04c1b070700351110841089440c40307001d5002034a4517440c5440d04440700341700c0c3e5590031000c0020141d89002d01003a242000011003183c0f05241054041d8000000704040e411442101005440e07100190310506005c03818200c0d048442500310b40f010440e1480c6038240c480d000380b0003920a036131150090005c0030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 631311214 1250 631309964 631309981
    0x301020414100c0501060f05011101020a0e09180f060403090e1501120209030f070e01060e0904060e0114070504150c03050a1101020c010c0804021c0807081c06031406 73
    0x10652081100301121508090824034255160303100c182c100d840c10182a03d81515141e08451640c0e0004000000090b810070035540c00a8002c101200000000c41c1041d6006001510001b06444018031030b0178011f001540c280002010b050004901004507099800001074403075581c1c5041d141503012814000c80010098001c40d0a1481940c0c9010ba40103270b01c2e8440700648414588910800846800703101242d403c2c7c0b03041040c21100001400141112882e0800c1c9401c50030068006104100155050130710039101c0580c0700b90031950000b0001585a40c0b04816801007507051012620f401d40d0303a0501c4225503221000c2d00c2620713840e5409045ca03803d08081501c0b00f0310054002008030368103011100000d03004130f903078000070605240054a0a0340001c0c0b010708484c05950000c0204a48405100a60500151821110380c04242400104002d030711007011600603460001c04068000540480922466484690001c0d06880030300400d034507440d21881010f5203103101d4540b44a06000110745a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 631312464 1250 631311214 631311217
    0x9010203012102031921050307050a210527010b0d110a030c0f06021b011403090102040f180f0b060d110f1902100b06030114120a050c010e030102 64
    0xc4202c1e088104085580c03080c480c041204140c4141d03854000c1c00d10000c810140401c0c4903804074403078071094103066400040d1002c0c0004406d0030108102081c010400e00c00d03085812215202c61a0070b00c00d00b50221114a03c400a004000c00444c0600704028845050075503102040d4000742d45c00c001a410311003000c01070886220061050f0301999201100c800b140ba80032102008000241020b103006480340c690300c0543d20143c1c4000a417134014a001c001c2660b05000c000d07500e440c040c409200c2d1030b251000080c90352200c1601500c90890000101d502c102095049400500c1c2040c0510300b080c1d17460510b06e036400d0100c000132407011b003045030004440c56548540380500b58010415814000701c000c1e00402001e5201ca00c80c01c52404001e070035080968400030703041900c5c80540e5442c00c101c59000090401c41d040240304e0120741444040c03001c5584202c1602e05403800f0709916842d42818200040070a00c11031104103050103203035038100a202d0041654840c8403c01e80f6105145014030060600700e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 631313714 1250 631312464 631312469
    0x12050c0f0f0705040905010906410c1b0d03090b0f0403090e060402040e040807140304081b01030b040c03050a0b19120218010608090c090103260c070e040b0901020301 73
    0x1c039003200b10280107600e05940b000e20039134060000015005083c0d50344000301c032046c0c000b1841075010383c880c4a40752031a40001c0806d403090b10301c080a111200c05810f00111a0151150350f003000007040342004600c056007030b000603054102c1210405207103c0c90140040c0818241a180c0c00b01040004448800801c0106c0c090755040e44d074242894074009609070a050081c10b000d0740309070200f100007005600040214011401000c14566819140c030700710080710b2548085040c00e80080c0000c025010012410841a00036148800722240d19000120010f0003022595a0302c43d00c1c148808a000c2da1550160784030f003070100410080390b4031000400030940f0341460203007004154100244549101d6417960600640701509000900b10a4000f051503080240c002c0000a542001003214982c010820300c1d818801c00d0302c02d400c095045864610782c0c07440183d0009222001400f2480d1a2541d4400321381c040c80c140001d4950042d1100c011000c0e10105840980d0008002c1c00420f880c51010f100300c0b0f04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 631314964 1250 631313714 631313743
    0x408030304030f032009030c0301051b0d110c060702100e030d0f1401030b0403020d05030f360709150f06140702041b0807030b030618010912050c0f 65
    0x456407140e600326920500f6501d408101a20344441c0d030750014024032564481ea1450b00120340712003c00080c145801400040903109030b0504050012041c00f4819010450011044644d036035412440d80348003801110207500038803980007032074001c000404130705c181c0900c8107a42903078003e181e04840d80f001e80d0a030b4111200b013504200310314058901a035106900080e9049000320ba110882030015045c1c04003640141c40c140c02c2c15080108040d4180700e40103408015040c800d0070b40c24651180400408000c1c031540c6055040c0700c01c1000802012659001c4003030f261540080320120184840d261701182c480c0e00300c043d080252004141e000300d020901074500140180240c28035000048920262000000000070350400200002d0b8985024180841ea0b40d02050040744480d000020b0000400602034420145002f8032450329550200b94207422031000104240141820070343c041c0189265103001b01140600020645119002400b5007015000182502c252820154006840d50740c0601e1890 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 631316214 1250 631314964 631314967
    0x60406030c02010f110a030f060b1b19030c02101709030405120a170f040f0b03060114070f0323070614060114030c18120115050a03020105121f0b0a08010902040803 72
    0x1202c2d07c260300042651445100106030580d884103c40555480082404000540044e0003086100b0411229512510000003103902c00d03501d0b200103082e800b03400f900a100309050800f042072188901c00581c015081344440c058541401501035549a0280c40b903a4080c28401d1102040000301190341030245801c065291882146005500902d40c41610310240008052002180a400c8803d0000140444184d61507a908104001420a09030100e91038990b5404000050001d0005110000241d03818240054512048501d01c0440e503400c0070300389041c05000c40d462007480410b070000540d0352040d40b05a1042d4a400c001100e400402d60555501c01108001003005860300c14004c010b80d1007d0721516180c20004030005000c6154103030500a160b442c0c030b142c00c440d1900136007104002d0000f00c50707080c0030074238580c0064440d004110001203003945060004140c014100003540581200c47c020190a60312800c442e030442e00400d50010000c0c1110b0008103e200c1640300712401da1702540b0003107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 631317464 1250 631316214 631316227
    0x2a0c0209060315090109050709020408030a030905121303060b01110715210506100e0f090a0204050a0314120901350703020705010b0613060c0809060406030c02010f11 73
    0x504a0030240c50103405101d160520340e111203e034110705004032038460001c103194000c0c0c20954a4100d040d040314070034910401007085491070002c21075210344142d08001c14100510304060b42024540510074034425000501e15604c031469072030720800e13684580c80410940b000b4030011260340315201e4060704036500160b0140065941c000f14034440790b0355468100e0103000030f0072010182145880400b00c20350780b64401e0101b5440c0406800300324011610f803040103854490700040081c0382e200840d40c00348a6440c049400d8203015011070b0094000a4190b8015075580d1820b0032040d0500c02d205c940c2d0303005d103506600108070010b0468500d0039050351051411010b4035a0b080d103014001144080e2200b0207580fa001416912055604c168200d0701c0040e260341007400c04509543d00d61744428400c143c10000741e0084400d00d01c0b880251a014a0200c0000c41075140a0048d07128096020b903002501190005802e0b50540110880040e55402400100707519030701c880655580720450b8580c0306062158 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 631318714 1250 631317464 631317469
    0x1d0f01050a0e180d0323060609061b0d0f080702210d060510020a02100512240a03060501140904080421060218011202030f070e0f09010e0703110301081903120f2a0c02 73
    0x80c0141640141c4200c000e591403001c1e0711700d001c5081600b040451351000900dd40c3d01d0700035018079440b00c240c1c0054450b42c10601440d1071108000c008907410030350b0204400022000784e6100c00c024207000740c42d003d006900c0580195640c031401030120b00c505900f20b0031400f5244280190b0381d21680c1c0303481e40a0701e031b02c405024102c88254404440165000000c1034880c0b55181e4080ca0000c0d4041c41d400180c07541041984036100040121060092003010184800241d0f00b8044a08803844004210b000d001c20800c2090300a41c0311078050b20312400401e403a40c4541c541450140b1421090321502c45010300a02c000042c3d02013119201000510782c8002005a8001d801e450b00c881c3c0f00600141e02d001e400c0340000c410401c2a040050030310a1941006030f0690144119420b29a5100140d8150740c034180f0000d035580a0681001c84c102c8001c0350050405020751010464440380b80e070b0920001d01c800c48820020705401c02c280100b0240b50360020300344440c0c01c5001c1c144d500d080d50b603021a00616001d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 631319964 1250 631318714 631318717
    0x70503041a13050f0418060519110904240311011b110d0206091009151b080c0a1e120e03031812071d0f01050a0e180d032306060906 58
    0x44c0c0715081516292400302c0000b61140441e400343c460040003581b420170310856840822038010003400305d4034100f00542c088540c0c03019544805402c442c08a81e9140761070323049100c4d8850780195400c0c280019008010040384424041d45070343e0030b80ea92030100c41c0154003a15441c07030a90001e00b0300814034191441c00e0508100f0400b6050014061518109817100483c401c1e001c18500c500c0042d412190611801072140c1c07844011030b160f41f8010121a12800013100714403180d0000402004e000030304460300c01c409000410603d03410650300300f24180d03070800819960000400c2104c141e13440c8050820114000c01d581444a41c021340114180788401a010484140c014055130b4000103a0500c02ca0b514001c00050b03020740310300d444180d450758411491064515015001044510a4070018003164940a4401c000c035a58880344012640b44c0301c640b680007001103440f49001d405280b0200408039010b40116004100c452302209500f00a00d00c4010035090035a0550350000701003107084114a400c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 631321214 1250 631319964 631319989
    0x38040602090111031b06010905060634110112060e0a0902030a050111130b0a02030f07030e0927030c1c170406060e0a02031608100b070503041a1305 65
    0x4003c1c01e81200c20707403080d24503000020882d4550f81c000e010f0385103074082405020300528041e80103100343e042850000d43e00f405403091400d003091080340d441b059065480c03c120030300701c842025188200f100d07041c00910b6050b9516580e01099100541c600400c1c4184207403006c07100c002100480d580c80e0304d00c051000d006c400c84280ea1610440e9200c101040080c400c00f135544580182d00c40e650306041207071003484203d50f40540000d03141880203a0700c584d00801143d284000c2404119642c0e4400d1400745d541400251049400001d00000c10010003081d20b103240c2c500f50030000d142c8100c1d03590480180d4038421000014801d4002d00c0b641401c0388401700300c0c11031071090f81c1000025051207207988080769200b101c040d035405498030410002c0b5400d44046a41159000704254030354500710000c0b4540607207100c00301c803c0005080001c7d103c01c2000040700c025180d1849001d9580081d400c01640e2608a4001d0010342078041c8803c08040c100b440c1150b402c845100401c03a2520b160500b0019901c00d0213 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 631322464 1250 631321214 631321217
    0x50f030903120106260903040f0b0c0d0f050304030f090e0a0b150406020a0b0a0905030307080412080121081c0f150810050a1103180c0405010b0d090519380406020901 73
    0x10711009c101c030358202c600000a006041c104a48580f90141c2c200c5c0b4280b0300704844410702046180d010b41381d991003811640c0c81034250500e41d648807a286000c1b03520a076213a0101da25010f40d0300030b02c40e03802e95503008101d0000d400c03106002c206003180d0500c00d0f5171040784211005a0f00c16850000000e0091100c2640000e900030001000070954441508590007190050b0000358042d00700010003011019001c007400d1185000943d560400340c192142c00c880b00c21280050f01c130a80c10341c0801c2110401c1703690390144c1211552014140281d40d01c068110302130280482030800107000d035000c8038400c4e20822202c094004050390550706a024000b44006800c42450b20f0b01e615501c3d901e041e41074021805820030500c0345c1c07e1131440304e1902e0f0414500d101240d1146041100400401038100103445001c00c3d0384100040003141c0c3d182c45842c1100c10410070243c829450b030000e00303010101c10040031001040c1c02103070854a4110450f140508296509400414030320086400b0403219805050000d006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 631323714 1250 631322464 631322467
    0x61b1e0d0804021305010806093d090203070902040e090303040809130e07060e190b030a0b0315010605092e05033403060605130303030c050f030903120106260903 71
    0x80105604c00c0d01c400740c000300426480001840600c0408000341c8824200d10b10161020007448210f401c4041440b00e003200503164101c2d2042c0071a8030542c041d44c15168002d003150400e40d51814080040d4100c0c1c412081c0009031880002c04209000c400c5a00ca41e40c0300150038a8500e262f002c104d400704045401514640e56183c002c25000d00c2042681c01400c443c1d1100d0fa51201424100510036644403400001d80040100030050a02c8400580341c020b50700d014041010440740012034980788058000c1100c1c2d07078180000141142e0403500401d0181e50984642c03103e070754603412040c03801c08114410f0003825490005a0a0341e44184041c64218913001440302d030300c0400342c1c0418484140301c02d0000362485410803000001d03401d0706c2420000d0a0b1800d0003401c0580303803a2800b4410705a4031018090684032000c40c40e643d80308004451003038134000c44160712418943d032810307900d41040803504110a002c10000c1441c0b8010651001a010840c0c0c210030f2650100110710b0184074003800c0041c65100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 631324964 1250 631323714 631323739
    0x6021c060b0d050601020c0306181510061107060c170705010911030106050f06030a0f06051509100e09161b03020a061a030a060b030309061b1e0d080402 67
    0x10103000da000204014041192a80c182c0c4000e00110368004d455103040d940842d02c0101180c42c086040d070fa00c081c010180460b180e03000014a030500c10b400300201880400b40d41046001803800400d18240d036040c1e940e140d100c03820b20482c6540d070040ba000741008101200000d1000030041c51ba219a4004c4100c03855080840c25580c0500b90b9844440c1120480a107114610841c00c0900c640c00090a046034005550003124001c5142e912025001412040e10350822620102581d00610010a009020000c2880d0740e90064035081d003104007080d10855080b100c441c03840e88120f440c1640300c40020554404c503180c1c9000120300a00710481c10080c0180040d01d9850080381111141c45140a500a0000000c2c81c2c5415400c4882c22250498542c80d8409000c409480000316280b05540c441c00000d01001034070002440d502903068540d1b402200010404620307454050a40d000681c52021250050549090020701b41617140300408a42c0c003511a025a041c0b2643ca255009070018144080052 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 631326214 1250 631324964 631325017
    0x2042912040305031503190615081f050a110a0c0201020a05030a050409110a0806100c170a022116060908121e090c041e0603050c12010207050a0602 65
    0x2030899064000c2000802001824420800400c007001c508030084c000f20045210180c141c980180b8010340310640e03134417800255020581d2080c0140200b041107030b0712501c1201158988009a054010010b402d000c00300311800c126000c0c00702040b41345003805041c010707400720071600005492030507411489440842c101081c0107000170b00003aa0320b0354030316a5a03414000782c035094401c03120114200c0314007080700c0c003000c551180300c140d000706045a11814445041004403032600c520074000c4c00000240316910404050039000b4400200c107034090b5214400c000e9000741d50926220140c0300d00c4c0d402000641610102c2c02880c285040c4a1b010014040c0c1e003540300d0301905c1c0c00c041c0c0404005590070701800340600d481c071840014102c2081d00000c00d450411000313a200c07040c41007401d01450300c50000f42c00c080c800d484002903513004140100400303581d030304245a80d0450300c51414040e40c40741c4001f2840301e00c18001c99014035007020090461030402e6951400a600003062103400222485910071080b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 631327464 1250 631326214 631326247
    0xc081618140117010f05240301092903070e07052704290402030c0f0a030c1b17090105091012140609280207060618020429 54
    0x1009001407000c01e255070900054912542c41c0c0c0340501d801c0030280104030100c0d24400c40d40960310240c4018041004002d03840703219409907008120001d00200010485000da580030700151100d00140342e0103240340c1c03540070140b459000728280c0c06410824090088980300203225800c4050f92510710301c2c01403900280c0815200b0248405c00b001c0c60f84110a0407850180121000f12001c0310324a91030746400c2600e40b99448a802020340600c0e00800060a54017001099807460400f40121503914902075070000d0040c20564125004510100d4007007020000489004101c0d5900a21005030f404030041c0103031240d0070040c2111b0411104000e1074a45445074100c44c02c58102503201c24214880101441095620342d210034150107000000b00140e81c0d450016064004c0d070440c2c0c8406003000c198050b444c1341007070340b402a015903000043e0070007008482e0313000c9000c452440b002c040014042d032084005038840d5104554a07001c440107801031110400d591101741ca24021000c03450480207480300f1108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 631328714 1250 631327464 631327469
    0x80903040f0b09030d05190f0207050a09050414030a020c0d020a0503030a080f01050904150513290f090604120e0a0b0406030e120a0c02040914010902130c081618 71
    0x28030b200820404a103003410002d400002d4400d00340305051001a0003605010301c071388003004040104014401c44001e009102e04406010081d041804107a15a103559018180680d030031200c1c0502042005a80780c0c012050f81c000c0714607540034008501800c4d00300f10f02506d42c08001c3c0d03030090034004001003564040006040380c0e0b40a48030000586001403130040c91190580c00540911200c004000000e903800c600400141821000002c00761503a4003c200c0d50343c03803020024484844030504070000060f1040c1011700c1e82c041070510400703070b650b101b030f8001071b003400d5648012907405000824002031000f8012010210743c0e2803c01c0680d40c494000030300101c1581c0c4491082100010240130041d4180114180c00804100604100200c000c03060020f20440340104108011040514219562a00024030154100b01d000d00c0e0b0034141c8031814001d00380c03a08100d215950b46412134158403698001c1c1e040d840003079100d180c0c60b951180d070704224000c860840d03c020032100c21140300310203d050011002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 631329964 1250 631328714 631328729
    0x3070b0a0806011b05030a12020d090501060f120b0606090102030d051f1401120c0201060302130c08070822150c080601260a09031803050610090606080601080903040f 73
    0x74606140d4005021380c0c0b007581c034042c80302d00110304d070b54040340e000001c030340b000c400518100c90051194000e40c0000c0c000c0750603e1400e141410454000c1c0b0805400040a90b0100507007824401d83d40c500e00405040c172500e008100d4205a00001c0c1d0328a880e8018103140c91060060b42d1804641c40c0320310b070445908850040505560381e41c8841c5070145088101c02421884014606a180070000a030044038100c1640314081d80b20304004000c10710030f42050380115806030140308000d0704100a1006010702da00d01e000042c459000262035140705100c0c0c980684110004240405c04d004065010024668026941c420131401c3c0803807035400d1032050b0007041041d6592070216003090000103042d210488501d0ba180140084101d0b144502c03006043e400074090b036000607441215190070341e50741c40241034070042c0b0b9142c47d9001080c1300300803c03954403074005510052045c0781c03204401ca040343e1141c01040009005480022115405808100d0700440164116420300303940304440030b14404a5000f500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 631331214 1250 631329964 631329977
    0x303011d0a0c020a230a0b04060c0e0a03140313080303161e031802060c06151008190609060603060306050c0304050d0c03180609170c0f060903070b0a 66
    0x100340302452040e96040030007003030140140c8604800003551003503001c0c4007810030f140c14958000c80048441400a000c4142003d941c0c0c03400719403d01d4620b21608541c2550344034182210b92002501c40d540104a0050040c040040b59045403101c03e415201043c3e00b030202c1c0300800103d850301050030341d91001000c0c0c80d0011690791408210b9161480800c42c0c06909102130405074003050502c3c0d0141d0f01c1800054a400100e01d104e00107500c0788603115441c040d403c07030400604038a86100200318907100f02d000a03004908200060140107550743d05804000c00030b852140070030080e003030b01e5040d40103200f10710801107800c585500100d0120f400651003500400d642d50410001c004a40c002d465100d0428164281140342c241c841c0368071342e5042c0d0071804c20041245100020140901641e41815035154581071346103803240300c09800855a070042030481e46141000400014000031890160100903006034254000d800a000c602d4200145c0c6582c140504000400c8980703403980a007564510ba5030755074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 631332464 1250 631331214 631331249
    0x3090915090e0703022d060f0304020108010e07080c0306121203061e0d06090305070b0109060311030a110405070e04051f0b070c050607151506021002040602060a0207050f030301 78
    0x1403084500d0b803a00340e50303903801480013040940d84155280c09095102ca04902404401e0340080c2002c094031010154000004585101805041390203140300d14400c6c0c032003010350390f01d030410000e4452044407440002205180019805501c1ea400745401441c040c0c02c0034110b03a9120502810400e41110060691202004100303a5241054400c509601003031040c02c02e1440304400b26040d0f07110a0405010692038601103010548100c0031546a1a001b034559400c55868038000c10250902d84000c1d0745510492440840c07520300450b1031107200d94090350716520a0a11000e0102501001300700300284a0740d040c0c0403480b40c40c4d034082c552050181c011220650202c0024210034040703180c0000c0710242080c0005000244c40c0c188400c10385000300d034042e0b2150041d1902090442c1440d08441c611402e10002c0d88041800c0e210200c107403455074003034426401c100d01000040303026920401c801640413101003100305c01154018400640580d003030310990400e5001d0246107038030a078000d0b140c02d540e103c0301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 631333714 1250 631332464 631332479
    0x120b180604030c110d2a060e0f0303090910080106061b110a2c01170601031e06060b0d0f050709030807080409020f030a061202150d0f05070c05010b030d091203090915 73
    0x110780d800c1e440d0444511b0861308002c03005200901082c0c000d0300075640c5508103500c5981c00c01c2910b001840090070b20289240c44062010307a001c092144a06560900501049441c016000c1800844109000b1948141c00f40c071501c0318590800701e119004010400045901c01a521030018010524440c2d91481101d03c944d101c0015416440500c0c51814124100100480030903860704583d040315114a041034070540d0116a480c50300001009140b03411000150550748802034038030400c3c020070400441005850030401d650b41110250000303141c1e400c00744000380000020b4086540a0100e00381841c0d181d00e000001c9034031102100d070900b4004403c010b03a00d030680c004c078006000841404110141e2603804500c055441810318204441c02140d881031b201c400d0340c009603213140403140c107002909115602600303906030342c0e805844650038942d032608941000151500010711541d50413030064035203210201c045050350f100303c0401050502c0012071001501841e59060390b080003403501d00d89002d20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 631334964 1250 631333714 631333763
    0xb041a090312090309180a060b0a1d150d020d0b1c0b0108010c0e0603060f090a02130b07110d02120607020312010e13030e04020f04120b180604030c110d 67
    0x83c80e0195441006940f40907224032481c00d85142070035041079603544850340d8070700140c0380c1a0030440f580300c00400c41602480c0d1100e00f400400e0446415800212055410b0000c0800100d510520800080001416a44066000f4990041c88403000070342a1403100001f60fa2070100407102085508403c0210284009003d8071801403c4a5000300b01c0d1181c03404000e402e20300f500305158480c080100005905894020b0403450004004120441c180fa00065000081d00983c5c0a0f0441404601c0007280429041044400300c17500705100e0000740c14070400b04041400918412604182c8004001c120100204001809a4415000345446503450b0b0503a5403c810705074400d0100258000c144640c210031240950412905850a840c0c85000000450040e2088030190480d1407000180001c01c43c006900e4541300902c03a1100140f283c8424144d51207510010400c214190000c1380072600280c000c018501140344214902c012141c001c80028010b5029140c00b03031907400c4d8106256089990f06407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 631336214 1250 631334964 631334971
    0x1804031106070801120206090402072a050102100218030613030206060f090f0603011e0b1002010501030201141e160b160c0f0602040503030310080f12070b041a090312 73
    0x24010450307480c112a004180034410721512031107050005691701075440720021101c6640703010b003065594089520f0141001c05803611008001031541020451142c60070f06000c0495030705900400c10400a02501c10003940102514200034803411800101e9440a000491242d4500914490780c09114100a424240300030400c500c030349400300305031205907103060509420001c0c884541076541d5940c40424010800c1c041c1d0f100300981440011100d000c45900b0400c8491000c1e21038100e502c5803c00c081c3d013a9842808002d0200b640300812000c6014860080c00c08040c50001d012610014803d00440320b62003801c1400311802014100818030080003a003075000b071140400e510800a208030020010210000024050020f088a15090204a40540d4061300b00142070703960b203052001042c02114501e118940450160481206109501150301201c040c0c082071400d160500c59640c102032414010400ca55005441020748800c070f80c003440d828441c0380c0da43c00450359080d001156451001004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 631337464 1250 631336214 631336247
    0x1140103060f09020a0e031b010212042601060e040b0a150b0301090c0c0507061e02010515040e03070b01030b010f0f0302031b0109240815150c0c180403 67
    0x3402005107052812402c0211009100d005840780800c17001160000602d00d0030300d0780361143c044590054170920302a001002026021600c0042c5811503035103880c003ca102e03501c2030086140081e042500a40159200c02501d1000003402c0d644900d10140b1707403002560140c80c084000700421200f0410340c85070000800314400c984402c940381c5814002d0a200500440d071a0030b4070703400302070070050194100c0340c496607005054801c041d0316000b0052100c031018540341d0301417101c4040080064018410103005103190070050b4060700089040c4006030444010011080c4410807044000c40d058400040c0079600c41c185102441d4900b516081404526811180561000c03850820060b03070000703070401c8103202c01c3c0e5090806000040c010b03a10001c8551000c02c3d12084007016078049401d000070148000c4540d00c1d4008551210024880820318805103281c1040c403071006040a200c42d040909102f540403001c503099019488040b44440c254814101013206014040c40105500460004065500d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 631338714 1250 631337464 631337471
    0x11010e010302090d12051b0c042f07231608030a05090f04090c06030e0618211c06090c1803110d170c010b060301050612190e030301140103 61
    0x40c00103894545000002000b03611098910502d05e409007082c1c401c40262102d04900d00c880c0e1158040d00d4800c0f01c001c0310302c9186402a10410f1881100301c01c050114172081d40c00b041c042d200710301070b0194040c03042580c0c8507a0080b078000c6620b6120403030724002050384001e40300920401c01503002c0e810071900065a641c1051080a103a5a40007080e01c110301412160703031300000e4803440807800410146501034086541e1610101d0f007070350142c01110100014500300e9031143e503403250b04500d0101c0b02c0c07182a00c40d0803080301010300203c1080c003211414007060300180340483c04070031815503040707000007404640e407210302c05c00541c40c0d180b1400050300702c1c5003811603168443c3e0286581c1010603001c010310680d04012080100e4031441ca8407118103500c542c94001035081d2011044154004001c1d8030703815170800860402605201e0240d1341218405003115003022081e4160031740d0340000400c0e40741841c41440c4210206d01d02801414901121072001d50741d00d5040150700600c50400505260501d0304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 631339964 1250 631338714 631338727
    0x9070908150a0b03030f0a110309090f100e010620010b091609091526030d18080f0a09060c021c0303200a171509041e11010e010302 58
    0x100481c0594460035040460030303041d5981c41e0404002c004528a0941611000c00c0746404140040020100b01d034003600c0c0d40d01084411002d25981c4c2c806c5604450b0400400c40c042458901603500041c0c020400d102c010080f503896622820200101b41c0c00500000c1c9062036021212404801c000e00080746800288480f900c92004a425030201a21040e13a120004448070b004038891401c02000e490b07000c5041c0130340b00d400c1405032242c0c01140107031000d50002c4000c41c4003915160714540e07000008070000e98184004002c1e040000d03c2680d20303500c44948107600c5400019100c000a0a54007460464203454280c2e414004181c84010f0b0010380910075214202c202507a00c0d800100c2032030f914118100c41c000030604c1c0c120068081d1a5403402150f018a411440911140014050ba41d0499a41480c44c001501d1109d02e40d04054806010090207400302045c0d50420ba920306901138003a0740b40c1d90015031a000250001303074400340c0a0f610385682c1c0b401403105691168000c20b07011824a4203604005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 631341214 1250 631339964 631339979
    0xf0c1309020a0b030709030602120615030405070308090a080718140106080613023604020717090111030a0801060e0d0b0a0b130f09060f020708180402120114090709 72
    0x44190060883c44074020000441091141480070f01079944000c081d9250b51030070b00e081000c80c0e815620a882800304500d20b1030301d0000141507074882ca4114000b4250303d0f00e95119604c40340d1211a2a980140403040003049081c0c0c00c0080c0e030010040c0414094854420180c0780040ba0920001110306100410040040c80e40c001c07000b9400c6482100c1c5410203040c000d80c035070f0091040c0382c1c14524990704246d1007440802d2081c0c514040070341e01c5545030010704481c000c100c1203204071240103210050002210602501c0000588609101810402d401d01c0c50150700500d1504124208400610706000610445911107091540a0781c151542011214140d594580c2c031403005081512695072503110300c48aa030355450007480e0040040b801c00031148540301c02c030003030001b8200654ad098203148131700541e034200e071089030310480d0003600c03090820080b003540d02c400384900c404403030344580c081c030030280443c0c20788004500a020700c010100320781c40100d00340080014010035000c2486100e031030800c00f66 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 631342464 1250 631341214 631341229
    0xd080f09010513060c09090e0a05070e10060c020604050303070813050103231b0d0905010506150702010f0c0204060906091820030709020f0901201005180f0c130902 72
    0x4560001300480d5204c0a21002c0307075104030580c8072824140c103244180d40144008500804440c0c00303113066a85440c1c4410790360900901c1a913545416000c40001041a280b04000b1820003030310051500e441c040c1c4d2100003a2964005400596002500041c890707924000740c00d40e40024207082c01c003881807207420742031f90884044840c1462600c0c0075240000301c030aa44000750109003203240151949545040401780300405c9001c1040b02c05610f0130000c5030340c03442c003201000110307010b03011800e180601caa03004682070800c02c0f40300c100b40507955680b60700581c0c45002c1d040c040e0002400005143d0b203000700c40720695034181d000c9100d045003054148045002c43c5007294a0000104114031b900100c0000720b032500c26136038003c1d00c07120301c0820b103402003c42042c01801c08410990340c10410b03515120b06030414080c009002149548940c2d82c13400c900040790401680003030440c2e10301c2040305881c07104504000402240d15a1031304641c1826034645803441c14070b1101c00000008010f001c00381d90106904 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 631343714 1250 631342464 631342501
    0x11526040218041425030201050a090902040b0711010f090902031503031c0b0909101107020d030903060c0504140402250c05012d0f030e0d080f090105 66
    0x840005800103801d540b110b501c40395100b4024140c1001c0c03072a1500b096030051400c0c19180000b405060201d59191000c6809810200f200481180b01e0f640341d0b41c015940340d400b140359401070000c14000064922a1880540001c105c402c98056403040c56103440e1556280110740c140c140080320685d411403d5019000300182c4995150040e0b80381c0b41d0810a0070f40c07000007040079a040c8000640c030926500d07003164600d401c0e64040380a024030701078082004000c1e0340c111103000032548529a007140421198203c01000d800b9807111a03c2d02041e034000c900c1640c1e02c064280c000c603e50310420001c003c85440341191040b4240340081c146428000c2280744010401038447c031403500811050410f003080c08500c61519144100004002c071a4a000038403c00e0b44e01c681030104044810824407004400e10f020500c070012040311011306915401a1001151000100c04066030f0ba4603a07118058100132000c0c040d0007035204d45003136282488090029240082460b030459051000f8482c511a4003200c400d40c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 631344964 1250 631343714 631343777
    0x417030708190b0d11120106061d0d0c090c110102040f1703090a03050607020609060c040302271509090a020d02060a050d02040b04080f0a03080718030510050115 71
    0x9042240c00805010b00800f02041d03074040159200c031070411036618400744040f031003681e4a00390080000c44076401c0310002d1144002080380c9140044413a0040c11201e18214401001c0c40c1ca00e0f582912040e0040344c00750082443d0fa40c4c0c80c614244a16000040c59881a0181009501d450305015420360b03000b43c81d100e883c01c101d443c1c04140c0d0302a941030003507424603800549101207469907418100d58604090f00c1c224090f003d400003240d4040f0000c02c0b010701c40c0d54181e95081c40c051440d401c1c440c0c18404454540d902d15500d2402c241416000340704140280c070410b146160607a01e0714100040804007030420401075121400040c0143c0314000340c90036058041310300540355004208141d0352403050074070202d8802c0c07000601041c50131180c8050401e6a03103003000c40e081300c03c002c904140d41e58080c040c00340101d0426000a441c0c4c0e0300c500c403a80e011031032803031058000d2992a52690301c0e2041c0d485a0080741500c0c0c000500c0384074060070308420480490324145204401400400010079540b01c02c040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 631346214 1250 631344964 631344991
    0x204090504060b130e03090d11040e15010b040b0712020a0b0a1d0a0b07030c051303080a030606111005060d05070f08120a0936050a06050a032a0e0405060417030708 72
    0x43c00d010720327600e09141100000d403050200050604280341c84132880011080c04010410010030a4100d21083e901035921090403213250802c1ca88684e1210b0b00040301040851080d40020400139031003400b02800b84108002c04a00c41090032801f2104e00d5440000c8042940300714103801c0401c0c9414010b6410007004d050001c1c001c0780d00e25085502d403140c2010083c1070310741c05000108020031032000340311941d9256420400f051f2624402c8a407008402a880c106500481d00c074228060030303500007900321900600300c04280314680d0f1114202800d5600c400c1000d04050402c0103046c00502c400c600040d00141c529180c00c0031140d016200c84664082c11440400040f1101c80090000b034107200340d141c1005a01d41001010200e403009032504603524580281032490020349414841420802d44e90300038560000c1c49911550302080040d480e6020481d10a50031000840d45429208180254000c030007408440c509810010000030540000011102c7c0030020403140552000c100394208400c0d41a84 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 631347464 1250 631346214 631346239
    0x30c0d060b0102070305030705160608010b340615060302090307150e09011401030605030d020c041a10080403020d091d0403020106030507080307061d030a050d0204090504060b130e0309 81
    0x40340313003000c103810043c240d200000300b080c14440002031035400d003120b0b5010000d00540b9000c0c01c940898007881881c0740d400341408510145030421209410860200c00043c1c5121001c81140c4080702d800170007030b2802a40c801c4500b01072440401440050111801c00b0341c41c203820300000c07c0c1d44844500c0b811011740040c00880303030310520404100c0c41c54407004080346402c3d61241100c14803401000040c034046882c2400000e018100801c880308030030041e802070503c9031680b40600000e4003170581030007245880031407071200c9039880f081034944581d11681e4000c0e192401d132034080e20b00100c403c54141400f4081804012010b115401001c1030b440e143c0ca0b04450351604d14069015005c030f41c20081141c00780718030100703441d4400005000c3c4180104028020141048c1c08900c4035116070645841c5a00200018925a801100144015a425070005240c59507a0689500315070007980e0481d40c194840000b040e032454400e00001307100700c841204005100408500f07560b248a030840d0a03000b9088207410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 631348714 1250 631347464 631347467
    0x4050a12060f05040b0f060f010909021608041e09091205250321021206040c050706050702030d050f0610120914070503070f0e072a0b060906030c0d060b01 68
    0x311101002c400c0309003c182000c2c81c20403000340003103845c0075003100d00d5000900d05160400f280585440103860b140d96a03810001480065030002e07144590100b102c1e1009000075044000a00080c2100341c0c580d07481e09010424480078a02030340c031041302c150030410720f03001040030760041942c1d030200f60400f80d80c0c80c0391010000001d6001c01010074860f580d0045000e05042e00030011071100c1c00c8134100046103041c0c0340c3c0c264040340101480c0c120800302c0c83d80001c1b00c0c0e09080c3d01410070003015042407410000075558004c1500d5044810000680010030821040c034100d00400780c008600c2e854102551400c00086442c1840510520703040000e05a00e00d03224038155480340100e81c0c2c01c450920105907004079020350310020b9200300c50092080080004003200b04d1024001070340c20b210450791071030f210004111030204c480360303044881100d03450742d115460003e122202c2c0254400c00c01d400c6545000c03810452040002804640241c0214520342e0181c0d03030306100362001c2c6070b03c0341000070850b403413070300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 631349964 1250 631348714 631348721
    0x150a03052a06030a1409010c09090e0f100e0c010e0f040510080115170f0a0b0901060905070e01090905100905040f1202060a060909080f220f0807090204050a1206 71
    0x260307150000000824041e003008a500040d016409040b4031031410385403280500c0c01c882c4030b8811500003030014103091251282a4001908104140c0d04440d105d4241c0040302d802c00f440303400004805551041055001c023001c0c0140a4003042c2400c0c903034030200721b01001c101c021880851a40c070460b91040001d07400c0000701d880c0c901422200008000c07002d0700000c1500f01d044036014503141400803944078600b00c2c8001501c1845d46c44840f0240170312040c87d58610605c85005000c4541c0755480364404240f01c041071141c640308600c00d6a40f03080c0004038100160030f01000741c01c110341c1c03142000100301400c0010a440d6084442c05500080c441d070307031420300c0304401200a00040c5444e8666225039030540c1d0002e0964080c2c5e114000030030500e590348542c0000c4881d9030388000c0071a1170500c040070840d1052000780544001d21945500c40c000c80c1d4400000011141d0040032000c2411901448940d40400001d0003620841000318909410580010703458150f610400b030340c40c400120540c00700401e541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 631351214 1250 631349964 631350043
    0x403110d05032709041211010b031005060918120a020304120302010501052803080315031f0e0f0a0f0201170103061a03011b0530150a0305 61
    0xa06403500e4144055140c0d003d00c001d031240f83c2c42003000003441c5100b450700c04015070040b507000084890306600030506858000c0140c0c2c2480c0391f956190180100e940b0180101e42480b032044500013a1807420070200000c0460140c401f65442820b42d0b0601007003074001030021401468901040e4482d103920204078a5441240c03c83d091031100c4080d448101074054004034103980341115011034011130100410300c0108041c0c02c000c02c400840c4010000305240f00700131074011403400c010204440f03250020a03d010542100c8904000c845007450b001003082d84618642c50101c03a02600d0b00c8480045e01c999242c1380f0b101c024000e803403600c4500045a00420140c4501760707201c00303a201d596030b4074106000144591003c2440a03402c502c080c03891850180b0415842d048030201c0710342e44800d4010111174580090b0b0131155110120742c9440250300c02502112154180040c41c440c007480e003420251364500c00c0103c1d460280301d00100c00d000143c03001ca00c0d4050390810004500745083c402d808000000e1720403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 631352464 1250 631351214 631351223
    0xc1b230304030b0105030c120309040b01050d14060108160c17070b09010903031505011b05100905010209030f07030c091e0504030201090302010e240a14100e070905060403110d 77
    0x107400810820300c400401c1c103d0b00d040f01541c030710303058020512640c15640d800d4180d198000304980500c81c0351a42c8400007100041c0340940c100385d4800b80410441e607080a68400b46810041000100d60340f0a4241c1e40c02105042c0c8881c05103130400e0f0180824a460b100200300312441c07964036460955031415110300c2600b262080c5403609040841d50b001f010008030980c0080c3c02c01001c0c00214610000150490b20180d582c1503100e6001501c08400408040c030407580350052500c1a04102c400f4041c8080d0345010700001a654038940c002c0516180300305480356180d030003120301003000c525446400d10881c1d003c5c2d1004039521611400000104a00d544581d0720245858103000900d1f505512095409101790002c002c82c1c500240c26030344c2c03a08840070412481c0c400d48a0b0f0304007044081141070b0010b04000002c00d4036119800381d185600c408a5480380d4044544401308090802030020941002140c188036041604101c0411414825800054014098010f080d5042d45540710585202c5402 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 631353714 1250 631352464 631352467
    0x60b2505011416020307030f030b041113051201060609061d031c02100506060924070b09060a020f0720030709060914102c040b0402040c1b2303 63
    0x801c01c4002005095900a000a9120151200e10f40c0000110f0301c444d9019240e030500111003080482c041c0c1042c040c0203070000e0312045011040013500700900200c11185542481c60f41c00c01e014822401090031140382c00e60b04000c0d0410ac829080b4411005030317801c501d0440c04884001400d02d110b4012081507641511602d903c04c214510310b2034021780108041d81c25150f0300d0038a0702d901000c1e5a02030300c41c00c2d030000c001c101d00d482501c6c005181e4144111070342c200130403d003842c289044031508062003d441d00300414003000400c220900ca51544010440e10450401041611124082c02100d038001c0c000300c5d0b5002b85040c41e03908880060003424000301194056510342c44d9032000381110384181d05a5509008131004484e20340058540b1a407402c4168180c0c80b880d0403580c5010f101f13407041340c409110700c2d120342c14024106c640c5c0c0140700718010711f4408024100791040c80100c030003e0028004000660300a80e040ca060740500c0160030745c200741e04250741607040025009401281d4002a202d110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 631354964 1250 631353714 631353731
    0x408010c1b021008090703050609010603050c0d05030a0e1f021b040b091b040e15030709090305090d030306171c14220504020a0c021003060b250501 65
    0x4150021803102505598001c400300c004019407414000001d0000d601000010242000c00d105000250744651258201c0d082c1c5907403911840c2c01c000066450281c9a5141d02c4240184481081110320170b940c20740300b440c15804251141034890113004211001c008103000e14a5055031402c1d8182e1242c10380c88100780c00121a60b202942d5500d803034910303090b030178190440c0e121545018490002001e0010341041d44640e030b4803944109001f1800c414651403c01030001144101200c100288180c072901c0101081c045148201072504c9080c0d4400354049080c801c560300007a60010503541c01c001e043d03524000501543c60250064403868001d5001384c8802c1c001d6840c11180018242402e8000d0315203070f410b840c91001c04a4a43c4054000c141c8550410014440f04484164200d9510036030250844d018544410020f0241da0040e45024005000e400300e503001d40c0392207132051810241e1030404200031461310528a0482c0558400e003441802604140444e124400341e0f500315031548000204280e40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 631356214 1250 631354964 631354979
    0x5030c0906040506030a151a0409090c0e100f270c0201140a060f050a1d13021305091b010909020702010302070c0902070c1a070605090a02030d09050f030312070804021504 75
    0x240411281c1c5a502501f60001403541c7c1a14181103003510428a19290604007241180a01000801107071500c0034008002030113020103105502803031664696011003232a1603000d8507843e41d130f5003010224462000d0040010280c46200d04810f02c2d400b5804640b680394008180c0c010507254081c10380504104d1308024402a9507800030056803560500c2d500380a03213510501c05000654050000c1c1c2d1582011407121140c4c0d10b0710165404103031285c0d000c03090005c075804191030a940464852a60b40c4800501c0324100081c49244140400300f549900c10400400000b4200203581c0f01e4004065800141c06003036901c02d404640303459401a10b0a040a0303510201d12000358080c03202540d5210360000b020030035801004010b40740781885c0c0031050601107261922802071030040c0c06400036116a60102c030060324140071a51314402c4075100c0c0d07000070f40381805005000c00f5100c00c2031300c260400c105080603404c40e0042181c00610704c0c81d10b071403240e81d1840030981c0b00c1328882d00721020361004240001c06c80d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 631357464 1250 631356214 631356221
    0x40b0723030108010c02010608070b070f050109080a0e040903021f060e15090c0a0804020f040204150305010e01050d0507230d0c05030706090b0720060711030609030a05030c0906040506030a 83
    0xf111284002c004c2590010002c82c200c81e043d02400001c0d4006070780030800d001c0000003801c0c030756020300c140d8000b10075295660343c01c541c5c4400c000c03601c031000440e10580064014051011301c00c400c0d103090220001c95580203489400101a80743c400c10342c401d03050b05d142c4069000c0c0c405429171048103540c034248400303d09520526008902d00c10609003001482c19804c1c00180d0301d007101941c0b42c1c030703910b500d0360780c00c000c10551000c40d01504a90709000028148414603040120071095840004041d4100003041d0036403c4160041030249075049900c1d000510002500400c0710341c4104c03420008640c3c07500010122404c440313200c4c0d001c05c401e140d400c00e0101802411084130302c01c804a0305c40030707503460081d20460150302c907110b8032407000c4c4250300101c0c510701da410030301d2080c0204030300002141800160740c940101c04161100f01c00d0740c0c280d811904040141c1c680001d4000029824007015071002881c510000b011045060342c0441d0101482c0c5a420941e03000d0040240003507100e18140c131154008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 631358714 1250 631357464 631357469
    0x3070608180705030303071b120503060406090c0203071119060503011701060317160c0b09030105011205031b0a020405010e0f0748030206180c0108040b07230301 71
    0x84080040e00814500000b4031004581c40035001e036042d031303903100c030140d40e85401c6690214014101081200c009111080c40e0b9406105c1611001e07100e0410806200403109240c01050b002480c0405081c509a000020340c1c01c020361090382104442002c0d8045401c141b890511052450b04000f4042200360300325020318103842480c20400c04201c81c5a00c3c03242a00d07030a100c058100c0c4d0a0301ca0078403803000e2507001001c000540340341103248420306555035600007480354441041c131140410200e00070700c1c0030b025407401051246c180351619121525013580700c0c03080401c0d0501c000c08845901c003076144140b00c0071400c42d800410030031043d0303555000c01d5a0fa603012035240f1403001074800050b06d154015004009280150450140f0401c042c0c141e10f4a218450396203a80f01c10014070b00320f404010303401d00012001d84a0340c082c0c150303414040c00d401d6581c00d0070300705400c640c2c20201c61040580d910001896001e46c000b01000d11b83c0d110903009503440101c5074020442c400d100d001a0348107a50000041d0704 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 631359964 1250 631358714 631358731
    0x10090213050a06051c05070c0303020c010b0a090b030c0d020a120312090b0708091c030b010908030d02040509070c1101050306040219090e0105032b03020c0a050c0f0901060203030a09030e03070608 86
    0x171401a040c418400f2903004031034140102e140c104c0c030100824030942c0030f003440518503400040e210a0b80400034002e0f042641c06141c15945544180e036032030174148402100444152640720321051550300003150101540a40f00314110f0380070450044c10300c10b0081440c9410402c0d0b00300081000b6003440c0100160480d07509010034000b07004100741240002c1c2c00d2004e02c00c034441d1544075411601044014002400388a4100035500c0300109482074140010820300b40224001a56949844184407505100508c45428052400e90180100b41c41400040e8101d500b460019a2541c40e10005402806850002c0d8810035142e03002804842d04118507106a403ca408440788603030361441010b1b500c141c4134807130401c65446201c40c0b401c80c0840443c007040d04007a1b410007500313050400c4a102c0c90b120560a0543c0c075503001c2020745540d420421441e008024050319040610360615001030758920010b00015241c543c0c48000300305152049103150103001780101079408035550703590020040c4806032020300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 631361214 1250 631359964 631359997
    0x7080711010e01080a0b040608030c1e0102040605041707090e0f150603190c030f080417030a0c08130302100203040303081003020d12140a03020d0b01030510090213050a0605 76
    0x1035560145001612031031050b03444500680e22440a01d014190003100140c0042e11190042050300043c000f50a0710840240240f03496101c4101c03031001d0810b44102c0003e581d1040006100990780f00f0112001d545425000404d04007030014014504066588008401d40c0f4180c42403640040214a40152507080d604035a040c02005103070300d8500c6800e0f203660754542c0c02920343d0880c2201e82a0000074603805408031950659580d210304800c40c109840480f491140040e040c04010380b514105018661900004c1d400c0c065404005060301c0321401e8003410401010271060220011020000017940d070150491a10110f4003001a540e40c100f400111f010401050014410018001d060012650010b0440b01e0541e01500c0c0c882c5041c10484070ba40401910300d42c90501440c0d81402003040ca441d6580041e80d407921304002e102260309500315541054100001d12400c9030407010b1a2040c3e0349800360042e030b030b43c5074800300c03400c010b07071552240350400004140020544d80020260100078420010130 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 631362464 1250 631361214 631361243
    0xf0d060b0a020d2c010c0b0903041d13081606060303080a1a03070b0a0c0501180b06121f0b0301050c03040b0606030c040303080411031c030c110606060d11070807 71
    0x81d03c5100c0307815850592240d800380941c4c0c00d07620060f15150700e0740046c18207541182c800e0301d803611103080440f52182d6541c000501001700000001d4100a8608882100e403800c0c24400104441780d440340402801c04c05000c9803500000e25100c5240c400543d22034000c02c0f2450b500c1ca80a807040c1401c66009200500c2d000b010070401155422001d034848000300984202c0e404d001103003201ea00400701c0c0c0c17408c010700e80c41c81a0005100b4441d5220650180c50103c000e50710034501a002e0020040845004805822002004241c001541d000c59591886010301042d005403451005001c2e48507c154598284000e029005408600450040b4084c0d4002c03242a5100001d001c0076200c1500d9000e8030000c10001000841e2003100c1c400e4000c0d1190303054030f0300790b0100130000f841d090500725031245e1120001c1d542a41d00c1d405110f10b09102165060034040c510f44a034035951680030080880340a100005440c002860b10303035010820100301c41e00300d2611107000b405c02c0d40507500510422280710601413000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 631363714 1250 631362464 631362467
    0x10501080102040803120703180501141b0304030e01052109070503160e0618272808120106020a0c060c0209010501030e0a12050706050a1404080f0d060b0a020d 70
    0x850f41610010f500652802d10b17a0080e4042c2240014004010190384803c001c904560084420640a02031800401c2004d683d40750400500405800e4050110000d401030300841c0c1c007007082c2d07540207400d4201480095440d10041c1e90794403410794424602084900301d800ea5444a0710040d000f0b070304440407a100c03180c855083c980e540c02500303c00010201d0500c0200600c001d40341005500c40300144c411200b900c040c02120a507150281c819008001007a110001c0030000fa966458803d103100d8010900f51412000b00c4d20f04800d0b200c15450400c1c84001c540051200070012910700450020f05140c1640c3e503810b000b501e4070001d0360201c410a07205540064840d2040e92881181500104100056443c081c0150028020341245540e540500c0000c4004117841420200c01c0c0318094440f107035180d0003840c000041700c000415010610b407500325560422041c250309654042e500010655445200319400700150098401c40300f4824245523011540e08950340140080d500c1076022910a07070b940b100d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 631364964 1250 631363714 631363717
    0x406110313030818130507031a0f1e0306010906080f0a0302070905091005010608060114070f1101050c0f0c0103060b091f03020c07121205120a090c0b07050f010501080102 75
    0x1d900030740c0880c095051010809090042400080300341e61030010101302c2010400800d090000011466640c800b005841c5815000d84c902403544000e42c046e00c4c40700b0b400090301c51064025414042c10507030144c00311032101028a1828030030000d00b154a0342d0380d1035007102d0182240340582d074454010078440c2c12045200003071480000364560007411b291030508440000031703c401040c0c011184282e00c52103600d402c071882554041c20041e900c0b02c441786482000500401002d4050b40340c02e000800150000c1078000c0b502200a07030f4000300040c0400080b40040310390340a64924104980550041d1003224400001d600001c0e00742a2018400c00703030756000c4150b043c081d5502d16908944842c00501001148214810280746d85040060901410101c0d080c501111900a401c049103052600c00900441a03d400d00b0600325113482440c0104019800906000203404070340c0094403009640108030403032640801408068900c59103070392050030100e0380c94109403406840c9510308000441c51910600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 631366214 1250 631364964 631364977
    0x20705100b09151c06020a030e120f07020603063006070c0b19110d060807080a0c21060218101b031d0d0f060c09061b0c0305010c0504061103 62
    0x200f1480003141035010300103071400c0803007180e045440c0700100304001101c900c050300e1a807003503542c00500c21244416080c07401c0569607542501281c140407203010b00100c0c00481c0e010f20740c1540d1103a120388070b84010a28408400800f12460202c4815401903c2004c0324500114100e41046030425180c112044d1071700d184103007000e001c0c00806d4002038021012039162640c000d801e20f80000d10700ea01c0d40310f240041d80000400420701c9850b01000c1081c400d0400104025014000281a601415548207204041c26206035803000e40b400b45404400707080700e0806207078983c00500956568200c40c580000400e02044204c0c0300309481d207011207515110307032281190b440301c1141440074054580c40030307560208811041c1500d24124a0112649e4a0700400e141507140718415805612026240140c19101c00c0400c4008000c903e200400c030a99112000e00b94006a030109460007074020704251010404540014019609040c4814a0380e5480030050044230103035900c181040d201202900d89174403441 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 631367464 1250 631366214 631366231
    0x321020c0a0e0103060c021c09030317010b090d05120f041806080601090e010e070e0609070e030a02040f0209030a080c0c120a030e0a2705060d2301020706020705100b09 74
    0xb00500024000c0e6021903401111070049550405c00081e000084500244030305000400840041040540010184030315a40c04000c4034850341c1003a01401d4280203400c44c10b442480301960f4502442003d118070f008020b504480c450303650640c0340402c500c4c0e40c0a8800c058900c80c0c44200302496001e148110780a40c3c551401801940c1d192000704000340800e000d1401095581b0050f50301444e100300b00400c0244240c1e4a42900c40c0f4280007004850100100200180060410340e40f402c0d69001c40d00018440c0c3c111000903039480825101c1e030090103207070038441c2c2610039107880c10140040d50010380311401c2070404680b0b15401040c1480286210440740203d40c1e4030480341980000d0203011480d00d2494058400e61049130350301c4003140082c43d15291001c0e00c3e201c90161030b01c100350780d004072a4007450a0701e5420403c14640e480c1569081c5e42001445040b002d500c0c0120594000c1d01121881078000034295124155421b00c240c070b07490940591408580b404c440405a03007401401c0b98810201c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 631368714 1250 631367464 631367489
    0x60402070314030717250908070b1c0f0510140109230d0305071e0201121508070b1b2103040303060302040908031b0405060a180321020c0a 61
    0x606210005a81018240e1014003411001748a840e507000e40c2d503148203101803c0055009a2480030700012141800c960100300542c100c1306010421001503600c0480702280c401c141d441c4810018045011b074120400300400381000092102e050103a080a40100070071010144280e1b9070703400002d030350138126908a010404a11007003064441901d4213036001d407000700100d100c030081755001641ca01380100782140450f0f4081000b03402e2095205d00c0341e003044112545485180460b80002e4503400700c070318408000c02e0301d031100d100c40d1040440c0010018003076603040301c3e03030340d6203440c180062038015801e24080180c043d0480c0030314640c00a500c071250710185580c0d4441880c2e4107203e0385240c0c0010000d4061680700d6000100503103440c0b18241c4500d020f40c2c101c0c2d880e03040c01c1c6012020074004200c032281d00e031002d005c10300c07450340d48204071282460307541044a9011020420545c030611180d01c060720000c40c0139288003418080d800c8800b0240003030340c20b075032800f0010010042c10046900620309401c03c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 631369964 1250 631368714 631368737
    0x1202160506090f0901030507241209030e21060c0a23071a010512010e0c0402090a15020f061008150601121d1504021324030302060f0604020703 63
    0x10000300601803604080e0440c0241207141e400304c0c2e90101c00781c1c01111243d025030300400c280c00d180070114000c40c4641001c100b034001d1558000301600f440542c211211723a9901c0200c810140940c081e43d44070100900000340803e8001000301410205a030107514030b0090301c0018090300000822911401c00d240c850121040c24030702d02210b0540684081445403504020840c0440d0843c980c5101d20f1032040b8600107950305000c1408500250888194040c1e030410031441c3c4070290125503e641d60b8801c1da00140c07103038150030014003400c04c1c0d0b0f840341b140721000004210800d903011800b01051032184003100c01544816401280744d103070b0762042414541000c02e802011044511201e500a1414501071420402010b50b040498202003039800102d503d40f0800030031600305110300081030b400b1900d217400da0316060300800c82119881c510351614a075100c0140400c0d02400c110341045603400006101c040d51a8a400303950745409441000e400076100780050424986030003250610756065492107001e04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 631371214 1250 631369964 631369969
    0x6132d02030108061513061e0b030402010c0b090c0d08091c0c0303050a0311030a06050f06040b030c0304050a080a0906170408180609041e0c0503012402240412021605 73
    0x80400c00745d2584160412645a00301480d40030b000f0240000b108410318241e4401091400ba410961200d440300205204100160707803c606840c1c20769400ca04280159616215564248100180c00e81c0d400035908450005012038607014002000056070a451001503150f803886420745c0c8400002d160301c02040e01400041e115002070403003903195050104040101c009001055001220807030448e641c0c4240411452902016010548c0740546a05280c18113100100a00c1d03c0020420031440b01c001000c0340810600f0489000566001403041d5141c00080c103009140311154490b8074001200070290800c1c070600b146099002e2075000d080f0a01d022044481c60213045a1005030540c4414140a8446a0f4840d0300410005110f054101c1c0841d0224800e950110b401c0740c1801020841d01f4001400010311075039503c00007410b40c1c40e0020191503088000c9140103e5a00012946c2e40f001d9103400386880c14103136082c0a41d104440041d01d10f8000001281c0da80109440e159914450010800050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 631372464 1250 631371214 631371241
    0xb0f090f07030b1e06061930060b0a0c0206090609030102070b1806060907080a09150f0e24100f12050d020a02060d0e070306050f090601080a11010806132d0203010806 73
    0x70b01d0502040f280d03029050f11050344075030402d1100202452070800c600c8007230b5114800c042c0001901c014207041c00400028040b5011020003405014009804280f40e50f89200392070481000a009540d078119078035040c4114134007078a0b000885e5a400d25030700d000c004040303404d41c4113140140012485580d80d070000c94030f042c00a41141030050341c8a113107801140000701c4021007040c0811010a10481c117641c0c0c2011110a02096016600b04048007a9411403200f411101e10304000c032011010f41f9034259030a0580350340d900c01c1d050307400420303400030300c0c240c0301629a060680913070152004810b07030120a980761901440d009510000030068607500f420b4560148070002880400c0303c2e4565125500c1000303ca8040e04c89100c4000c0c82c03001c0001030300e802c22030f65024041d42000383c490454503540300c3c2640d02c8812802814050350710002111515050b60500c00060180c10910181500e10014a01510380090720000301d02d42d9201c0d000303540303d14021281291200d400070300080e51070382c0810040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 631373714 1250 631372464 631372507
    0x40f0303050a0b0a0602030a0e1e1020010f1a090123030a1407050109061d12010c0c060b0607110f0f0604080105060901060c0b0f090f07030b1e0606 65
    0x82c0340e81d00600d41081c2c44140860014201940040d07555150840014045010300c42e4520703c03400004180030540581e00701c003081800815140315854494401041e101c9407000030746002403105c1c28042107020101508101034007a05240c040000301c0b0020318217512000d04a8505402c180908010098286000103202114415a0780b101903103c0250003e410048034032002c1d141000e10041700f810b1600244203100c010202405c00302c00051400b0006024000c0004450315a010100809a5980c4031034a5803128101c2c100002c01030345841e1b0101501c004108941900c107585003281c7e64281381450360484510799000742c09690301010740c100300b0014405440b00700c2d070401c2c0280c4c014845912108080c1014085420000c2003514024051050100e0305174841410011410500d9012400310701c942d54000c068903040c10801d40c0d40c00741e590b1822401d24000c440038410058000144001c00388114081c80408a5901d150300c80f106a40d407040340c05940c65584940c08005180c441818003400c0d056 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 631374964 1250 631373714 631373731
    0x9281a070f060e070902040306060902030103050d0f020c090f04030207061b02040509100e07060e010804020904020904030207030813090b180c130b030a06090e010c140c0f011b0215040f030305 84
    0x6050300c040d020f00342070030050380c08941d08503000f02d028010880203000c0c840140c005400114159899500d4103541d0301e0706030841030144080c061400d140980300b48501d181500d8080d00403801c0d0300300310340f03003440e191011a805d600602880740e01081c201d01c1100320401050f958030a03101080280e800300001440043d00701c41052003032901c51a07405010b0702034201000520b001400400d850010b02600c042c44c41d400c05030401140604200c01a0f5030001020382254040c0d5000b40c06a4407440c00384c1c58a000d45e000038103900c3c1c01042c600c280000750300c0d00109441c1c0d5502d0a00c456000b00d000e0000c18244c030038403004004a4100081c070a0301004018102c10018604209142a52960400c0d9264025100710001984a08050044a075540952500728030108000c00c6000071082e4000c2101d48040c140107064440058400c03104001040343c49240c02004000300080c01500e41101c13001610203400c04058010091511406180040ca40348a150000042d5503100002c0e64100d000b440001c180e00d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 631376214 1250 631374964 631374971
    0x7110f030d08011806180608060a18150902030a1104140903040e07090347070f03090515070207050a1406070f1203060302190302150f09281a070f06 65
    0x124904a41c0000f1503000006e44006a5141880c10b283c0c1820f000901c403104050901e21802d103000e01c90480081c120390001c445420a02003601703040080c080524019605125011001c0c0c20311011106c81c580c0d00600701d5040025002002400da8002002c80c5d0b031200d25001031100f0042412440084c540c040420700d4101c1440e9180e0303072290005200c04140600d581400c89540801d943d11000403c0002105010400940c1c04040c40f0818154010200d004008070b100c807049550307020b81c0000040f01e03848403d07284170021004000c0c5a00314101c5100006214a6500003070718200f80b440b9005460745845010410785601c2d0921000b0381c00a04201e40c2200842086d00200340307881c00e45100d200e440c2da0042038191550042000301c0e0300380160091409143c81c002c1006035a0107001100c041909200d043d01c80034150076028150203134401c0680c1001050f040d04002d071349a1041555100040d80191f0202c6407030f5110150300110130803290181083c200604c2d03001c6a21950910103c81c451200403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 631377464 1250 631376214 631376219
    0x9040e0c030d1d040612020d020a17010e15090d0804170406050c0c0f0f1504050d0305030108010e010203010e010b072f01031112040305160807110f030d08011806 71
    0x180c54100c0c4400d500000501c00c5401c541030b400e0348a8421044038045031300340301882c10610000362070941c03020000c0c4143c0380d03900740c0c10464860300030480061510901d10040200e00c240128003801030304060300114065140144045150244058015800440108200c240308a0183c0354100d01400503a801a000080e68101000c884001c1c4058039290385e80c00d840304e81c2c0142c03161610b2000d6080500c66036050250039030300d841c3d46400ea1102c02d01240c0c0c0d0f540c4900e441d00e250109100b59004103401984141800040c160440300950490b20b409000308038800c424140ca80c01c0340000c0c00b0700711015020800410242e60400d01802000303000340307100064080c03501c54040450000000802e804240c06030403c81e00d60300b61181500c200b06a1160f2454000e903030040c2c0c1c1d48400000c20040c28000f02080000c49100c20b42d6013000e55551000070f1030f54413101d40c14001c8000c035800780c0c0e1511814114200c800142404101807040a40640712024aa400c00c914183c0301c41ea1082041e03c0b095844200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 631378714 1250 631377464 631377469
    0x90518220f02060a0c0501050f040503031603020706112205310501060207061824020307151401090209130e010b1e030f0601061d010c020303030a151a09040e0c 70
    0x84c00940c1680c0c440009030546490b0003429500b000309403402055240040001285c004411a44e0018502840c5080400301c958250002e0052480180c0160700e48068100c090720b080d4014918010114010010f0800803200d0211444841c06050741240900040000500082d250841c81c142d503402220040f1600307480700030440304240d1000c00140d0200f03204120107a0400241c00144020190392b0158505001103d950300001581d92200394002c802c410551603c248161a44164007092040b10000c041004c003019181c0b8008181492041c60f00004a500040c4201c6540c00c10190440f110515000c4020300209042207581b04a5500e405a120441d80c600300d020350360701020461082007202d10006d0610f46080100403070582c3d800900148601034101c0d0194420f29440d140e02c0700c205548034012070303d00b80c0d000f40003074042c07101106010900289402c101c0e90201114084c0404c2590b60040000c01a03c00c4280d0312289010024400e190815422061900300300000301c0300c00b113140001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 631379964 1250 631378714 631378717
    0xf060304050601170a0507140a0b030c1312261e120f0f130c09020d020306101d060d0b030f16080c010504052707090518220f0206 57
    0x301121079030002c0d80140001080c95400c1442030125200911101145595142e07072280c05003d0845c0d2030821a9500d48180c0d44c00200e41d015040d9405416268145052030800e29001950407401600051401091050b07a0030f04507403200780c01428041d50014203400c400040c0111549060240c43d0420481f04290b110380c454156031181011116502d8465120358000b2405c00741c0b035014030b030800c1d805011481e21541010b0741c005003d401824010700c5a03192202190440341d00542c145030000c00d8003080310703400360701840c855107081d10110002d4079603805c111a104120150100300e0481c0710380320052424520051711488002000c005905921440060700d0b1404107c0c40c40c0c110f85c05403c1107540148000501c0c001480a04000d080d103c220a001038518080c42c02214015582c0d015403c084901000c0085a041c1894400c00d02a0401610081c8502c1c2d86003d0203001d050311462038030902c0c1c60b898640703110351580303448800244503000b20300c108100000b1083d1000c0a1400300d078005aa00d000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 631381214 1250 631379964 631379971
    0x16080d0519020106032001020c06030f07050c0a0f0b0f070206042004020d060b09120a12050903030d051611060112140322030209060306070206060f190801200310060309020f0603 78
    0x4001c0c0c000d11906c81c000910b0006203a0129000d0642030050207140010103c0442e00318160b17040ca180c4404d45441d0107803031309041304405803a000104501500380300e504242c5034000c80244032400d003141e450300002d80c0d0320031080d100107040000051486030000c050301d0108103001030041c009480c015000f12804240c80715a00440342d1130100099540b860f03e0100c07800e4001c04003a80150030743c99204d440313101d010b810455807801404000204190700c4e0342c0500c2140c0c007680061000700030605022400e8001e00c1401224280419044100d1614201001484034102d944040c941c01c02c0e401c2c0c65564050040307641d00c541d03415210511144d561101310144820103030280344900c0000c145540104061084050420b500175000300040c4489141e000ca11683c2c810400c2d58a03c00405090b40400ca84540c1300d0040d0101207104a00813400c4003040d04108016412080030000388602e41052640921040d50812006203900c0ca0801c0024040d41110394801d00050000e02015418804101c45a2084 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 631382464 1250 631381214 631381253
    0x515030106090b0f01020d0206061504030609030903060c021b060a0504032a051518130e100c020c090f250c14071d0405010209060c16080d051902010603 67
    0xf694001030604000c408100c20a07000d05c0100326030b90420308065201c0c03502a00050041a000300280d80b085010000c6074021a403045003001030002c10b00b0014016010b5000894186042080e0000320030700c002120650010319200f56009800703080304101e41d0354080d400034410f102c4113100000c00310b14038842b07040c2402c11809808902c0e455030b400c0080ca0b0a81500040e104103003226141440140c09019240724014110881c42d2450110000a1101c0e06061240b60458180101c50084c2440400c41d00c04c404100c01082c42080c0d40c20500341c1e1600818081190410b4182d00001c202c0748000d080a40c005509828000d40c0d0f030780b544410400443c03042901c4000c20451200d080802a0b00e50710004518604006000c07440c0c140040b0426850408807a42900610a0045018400b080d030403941040303002400c055541c02500c6400303444240c8202290754000002d0400034150300301040311030101603903541c0c040c40d05170162500c88050b1403040310311046660300c000100008114150038015040071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 631383714 1250 631382464 631382471
    0x1050412020f1203010b0904060f140f0307050121060909081b120301060c05150103140d050306100804030c021315121a07180e0a060506120a051503010609 68
    0x1150300030b441d1109040e0680b0407a40041040c12800c8501001d990540e6030b9020090f54800701400041d0103000c082e001810310f841082800244a203107050003c00280058400b804445403980416450b02c80500c5a580425000c00d01e00c00d1040c0f0000c94800d02c100507110002c2c03151b49582251003107030f440399130807108464002802c900f460150320b42c9005c22004040103280c1001a0041400303c1e01041c0300d40390911246e050a02c2c02c10006001d2440700c0c900c0f02c0b03000350701c03503a40c0c0c1080002c1d40528a900ca0300da004101001010364411801c80f4803646000d40500410841d50201701c8000318010016002c200e4880c41c800c0059482019030700404201c40804500c011003507594014024044e4032a03403082040c4191800042d101c0e030304030a507000600c0842c1b000380d5110507099036810012040d0303043c012442e00c40811080c82c45000107020384030310007082203241d45460a001c2d082c411200030194000c1d2460001d9010204e0b0b4110030380c00700300034140f401c0f4042d980c0042400e5400c15040000110785 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 631384964 1250 631383714 631383743
    0x60c050403061103240103060b12060a05060307020601030308040c15080f071b06050714030703020a090f0e28090501020436200409020319060b09120a0203010504 71
    0x69000e4000c0c68200c2090144c51403c1c65808008a20205000d000d442d04565000311145ea001e1381c400d400502038640700360b6441070b02440c1180c18001c1210014841d109400300440c03142400c1050380d100ba0116002400c55034216142512440b0006108454041c046940030601ca0301d0f10344008001851a01ea03801c2c182080107400460140080a00c8204070407070340c001c1e010701da04003c140210350700a4000a0703103031903050701120001510740041142e260300200740b1a01640c154000c00d58128640e43d940d00141e103600e040b07207140d0355070300c81d0340100f0132048080740b0f50921544041a0303a00260302d18100d1440040b507404203035210820207982d0744e5808078081045c910500c0f194010510000034440b80c8010003030900c0e170310000e88019a844983d0b201040300d100301030b140b8101c00c490300700000252503d0b03031500007001039402240c2240202c070340c2d030140507a01402c85c000d50b13007a6151084818217000400c014800c240000c1d110721031a0341301e00610320004d0389080c86154011405950f2000101c01c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 631386214 1250 631384964 631384973
    0xc07020a03080c01150b160b04110307030f1203050115120b0306010f08011409190501090f0605070e0904050705241603090e060604051c1203050108010f0e030412020d060c050403 78
    0x219540b04811201d01080a030700d80100c7e503855000e00544c0405c900041c3c0e192404c1074000b01000e52030700c6405210300400841404601500d00c818280709500b51a000c1580c0c86080f801c2e280e00384909900c82100003104080c040c080c007580020282e0031600064004400c60001c1e00e041000c0c2d0119941110507031050000b08000c0c0180604414101e5100c149814aa480141d440d01d949042c0e07452841075039160420424290842e116903a0000c0b054201101c2d203041c0300008010545006000c00e0101501c09582d08021540f14401c68101001d07114080c509420300070032441c00c002600c5c89180412140da031f1800140043c140d085030a0113191036400461170040c102c500360f60040842150458100030791076981500301c405440e016100407650050016495581526000c001001201503081c68030002d40c0c5544840d040341c48540c001e00091000071800d000702c0c1c40340407035010150002c110a220000445040c45e8401d880030b018400708a05075101d503000c4a540d1019007000600000b0b0800902 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 631387464 1250 631386214 631386251
    0x102010b01080f0106180f03111c0f0624120228050f01030212130b1b03180a080f040806010614030f06012c130903080c07020a03080c01 60
    0x103400e091000c1c240c01c0000350b41d0402201446140e041100100c0700083c6504840d289600610000c1c0c0c0c2480c0c500d861745001c411740c06008000302c2c0201940900510301c1c05003202c03460002c0d608041d81d00e80f01c14503520340d13101800800c0c03588228031b41a47e61036580818a00341c80d000034600d8180f1252003052600c100890b0003c008041810307030b11101c103c4050007400540f10400c40d031007111b044500308540001600607020300c1083d8400c03041c038201003000700d00001819589451058909102503540d03180042003080d510b075001c1442c55420f00000c0c04954481d038584104441e01c50840c3d03041030f6507039943c150541c452801c0e1018010046010407001c0c3d0304005032800752034a030400d64000c615043c1d101009010050602500000303d50204035985d00520002c2c05041c05031844840380c004c201c01440c004041948001d01071000209060481c2d081841111559585581c03081c1d91501ca52010740c036035401c406c5050f40d0259810800100280303660006101e484d60000c0017140301c04a002a04020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 631388714 1250 631387464 631387481
    0x503120316030204051f0309020a06050c06070f0c03051b06070f0e0603130f020a0f0b070312020c07030308071e170907080d050703050f0f03011a0910080414010614010201 75
    0x5050041c842407000340c3d50780810a46c0100350044107004080b0104040300a41050078010f0b4000905003004252190701c030004185090340d10084a601d40c0310340204461050248010000050000305090000780c840c0d4020800040081e241900d490003201c0c4990814000b0389292020809144005015a070800c0c07910044403001c40d149811841c3c50045840c8250203d2401021200031008006c215518080e1510142c00c0d0040400845a250040c41829134003a0001780c011030540314604400906500844a0b03c50300301c07001c1c0040b00e02d076583c10758141c04041e111f10144012340c0101140780c18a030340d2940407020700795292007441c2441d0115044614002e4000394254010b8201409400307000911080c0102c610318080e55207004a0400312840c0c01031a1034240b482c5000584028182040e001441c1640c2400080c02d4186c003502107070303202900c98054100c0d00300614903c0c40300c03528059600700da03008d40a004203242c007103008002d1908544040c0c2103521520b90362103108102d56070912a174406c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 631389964 1250 631388714 631388717
    0x5011a120106050d0201050a1101050108010b131e110c01050c030103120206280608030408030306030d0801080c010f1b052d250b03070c061b0503060d0201090503120316 74
    0x105a00380f0010504880700c07020085d06116000640f0350038203210300c08800300c00501c0c100070042541c4585180d80604100c032007040c4188040c0b0106401c040f01c07846140800089007492010684505a4074405004c0841210400160500804030003450070f00847e0300c288640c1488550301c0d8114a80101c5410a0555000441d0300450802102042140c0c256401d2031004d01d103000f03012071058204014003402e1300410000e0001241c00103d0304000000766005490417026102d11182e0650110b4106509100b502600da0000035003001c41d501034400420100c4c0203103044088081864034409182803510003c680b90390001c0d400c4100b4044442015500a010b2a10311300d00156102ca610f46c1c40e03101f404841c5020b00c0586286a50881c5e45c5000e400a20496441580703d2401ca00c0c09001800031031020b4440c0c50903c0590044022070220460380c074865030f01c2e6182141c450505120400f00d1040c8224148a2411004070b0a031342c2c108080d02014510040c01c680e2481c1142001040301c0c000b440400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 631391214 1250 631389964 631389971
    0x90315040b060409060605030d020304030c050303190f0c020a0305030306040b1c0201080907170f07140901090506040609020c011a0d02010f0c061401090501031a0f061c05011a1201 79
    0x8000744908100d250003641c2100c022a0b2030040b8141940100070591103568948a0002c141d402550080301500403039000f80c0407040c00d50342d6041415141d02c00c515007148000b85141c017600c16503000384c50203003160320640351040148140d9400304170071480b00d4105882d0741c1d20120800025160500601112103400d850f0800464911001141a4811200000d040c41031308000209503000030040e0710014205448000307251418003821940714000d800f1008028002c0107004103070080418030b80e601c5a03402810600c2d245e868601140001c0401401551b48117460b013200140401041c00a000d2102440c0000940e8004511881c0003141e4401d041e18010130030381081d000981c0e003003244d0301c519512a041c4088a0090303440d26030014a24241c2080d4281ca00c0fa00220b849901c0d039105038180d82c441d5948500c411001d40030764104070b5080310100b240c100c0c0440000c4840c01d100000c0c10205884034060700744084181d43e90390950b882e11724a809081041c0c00c13600410b240541010900088140080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 631392464 1250 631391214 631391221
    0x31b060801141507030509180c03011a1303060e151303030513050604031806230c0109080301030f230c2713020301050106020d091202040e070b090315 66
    0x60514001441908041c100b00c07000e150710354450380c0382152280c1c0a0350440e42c1d0754080f403902420799044203280303500424061092054400c09004800d003c0c482020807207041d40e00c0c01c000c0c00c191080a83c4451003045092262820191010748030601443c428074000c101303005403012481c58190002882241d1081d40814400c0321200f017486404066050300e00401c0507501d0144100e00f6560705000203259229003400c10080c5a40111004a0101100700002c03015a07079034003c450100850f100070b0340185080d034010405000c0f80c00140803046a0b0000813403a80d0864031043e0454109900c10790300317512814084420083c038a00c000c401c80055460094640741c12282c050703a2250001c0940707000312802e2021085600c2c107070100340b540740701d49056411546000e4905a40e42d140d02c4c00e00728000c0d802c1400105d0010300101c0d1201c1d02d00401c1c0d035103006103460014805203010701c0312401d0381c10968405080d55445014410a0040c0ca40045020340c0c8400d00c0092606e046080480310a2a20040091 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 631393714 1250 631392464 631392467
    0x3120a111e160b0108070e0c032401020709020c010f06091107080a120f0c1701270e03030906070915080a0e01060b180405011e0302010c15020f04031b06 67
    0x11400c00d200c0d0251034076030308072040ca80c11a2182c00e00140242048000000780380701d00003040d00c15a040100c040c155519600016002408141c3e0600901305a90180c5600045d0700503c82c0664841441200d00840c0c0d50b00702d65040f6071094405107126516043c005201c0d11450081d40010050f00030f0802500304040a02840d03400390040c01000110000756505409101e05400c407001e0190f10001c201c00ea660110700d00c000c2c00b0092503200803403949003401301240040c800d0981201c44c0402a110311618041545c002d0030f010300e555244455841040144280c010800b95124800e241c00034201401c100700050041a0b031a48005804401060f500d0701c00d5900906d61500400c07202c90208100000202c20742c0504600c3d080b88038185008980504e280842182c0b00c0c2c04000d007508d04000c940d8030303882007a100780d2000d4808881c2c94020781040005501c41c600542c10399005000340816021081101e5003668031070ad102ca03c3e803207808030701032040c052044100703132004404104801d56507203000310 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 631394964 1250 631393714 631393747
    0xb190f0e09150a0e0111040603051f1a0c0706030903090f0b0901080411030609010506010e0a1a03100e010e07030509010c0c030f020a0602030a1a0306090c040b0409020303120a11 78
    0x500c00380b0160a901151400745950040d8800040d1103009000c0c020100d1060740081c2c1040c813a0780002428030007c28071a08054400c6002e251192800000c50350915011600451200050340c0201008104203000000c0c180080c0028108076913000c64184810b040c0104140a01d03001081c07000c01004080210b0b045010480e2501142805c110400b640c442c00d042d6440ca8003000065014024603040015816041d031120b031203000c09880f40000789440340c0610000d1031890040b4174215080e01e00f18904c10380072001942c1d0081e0200d200000d055103442c201c8114081c01e074008904200c041040c01689601805156400344a85008018201c0d0444000740001c2950301c0c084d00340181c0e180d000000e58801c0c0200c0c07000d5030704007806650700d00742140030cc0006d01d130122031000c404000850b105024500441c2850080e540d80d0000c01d07000601008100c01000c503d90a5903000303983d00c0141c00180c4060010700062111101400e0443c5040e41074031083d91507085480130400810403241c0e1804c900c100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 631396214 1250 631394964 631394983
    0x20406141603181e06020f010207020112110403140601031a130f02031216050c01020c10030b030304051002060403020609160e0a06050a1203110318040902040b190f0e09 74
    0x5401c01d05144200d2071070034600759076040b80c54116045012610038013510703c550421600c890382111054240d00e52024201d0040450080c00114800c1c1d044c100900380c1e4005100d1803080000c01c46c80c09a44e5920100c01040c00c81d00200140c002e040100305200400d4024841447d40380c00c035071010b18000c00080c142c4000108000c041c1d02c580b00700d04c820340d2410090444200605107500342c0e608526039829101c1c044030300e82140c1c9489264038190281d4408102d101e031400026081950b0b106048005402418410031500d405210500c00045c2a0b660b00740d1112016100c0c1d00500224102801c009052020013031050205620920128107054905200442240c000744000c14603512200e4880014151580c0415840940d400c0c0c0800c020581c40b0078090342c03602c00c5c0c4880001c002401c6c036080e00c0380202442d040c81440c5c3c0e4446e0115504041d0040c1608610007000000c0c0c000c0c0340000074070f00c2d070003030084103c1411507004280701420a80010301c0c003409007220441414640415215030742c0303180e070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 631397464 1250 631396214 631396217
    0x20d0e01140909150303040603060f0b120105060a02150f061309051e01150311091803040911070204090308090c010c020f041d1c0305070804170309030f0c01020406141603 75
    0x42c0b00040c199010103413030001061001302926561940e07550300802410b014002c2c0500c03250140c03800079125000c0c40072101428001d640c042416880e100401001741c0100b40003c082d03005d4500c03628124440840001d208010382606810700f41803410a0001c80b2617204183d261140c603003140355000c520b00062035508804280c4524a00c0442103041d180984032b01c4144415450400c42d01108003c40c0003100c0040d6031003500e03015043d40e61220201501a103145026403241c00c108000d20500040f80c110b100900212070798a45807240b00d5001c501224001c0c81d0680003c2c10000c00d21030390003400e0051148250091030301c0c12101619800250440702c100300458484c643e00c0396086c0614030b2410910500b01c8014090300c08844010440c080081d03820140300d000245844000307002c603130289820350f00942c4c000f144d000d84038908080614030b80d80050802600d034030080c0254000d080564004041c020300c1d00380056290740c94050050080400915500c2400381b0a02400207455420102c40711010b805 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 631398714 1250 631397464 631397479
    0x203010b040f09200f040f03060204030b090a0f0f02220e0c180f22080304440d1d01270618020904030f1404060c14030c030a020d0e011409 61
    0x1001038901d40c0380b185610170000c070401f4810000030b00006901620480c0d000d08400802d03a40c0345100310792130b40101c000041a0b50f8040c4000f80c08030301c40a614141061018086904c0030101f0744001250340d000603285140350b0f40701d9a040c10510700c18050070f0051142a10b0300c5081b02408000102047d20043c0031a0a50b58010000ae08a1981d40c2c0c4034481860140f4045820204a0a180312280d2048500b41d8034450f0280102000c0031030118401b0354001c3c150417243c0c0d1041651251011248500071260407402d040c010354080081d148101d00d10800110f8920f6040042d440304582075504100c0e143c3c010040100c915114003a0348a1010010350b032148001800d040d944465105100c41000041c0d00203468004210805070480c02100400d030564442e05d400400341c1d0202c060901c02c0b030042e800003a5015400741e0005280103410318242c080c07042524100301b01060b046295401402e42040182e1004694404081c1c0200440e030201100b841d1240c000005001854001d1040d00c6446024442 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 631399964 1250 631398714 631398727
    0x9020c03160c0e0916120807060e01090209270c0109210b13020f1509010f03090212030a080f13080306190312030b03010218010818010203010b040f0920 67
    0x21900440c074003403e400019148542444003000303580742c103901803000d403401910002048041081c090300d210564010141441e0080c507903100006002a0349150010350348594003e80107035125169244100e6003400d904022a400841c10905d910303003134a440c401e40e00312136000701060740c0c006200c02c00e41d59820000ca41e000b20380d030003500400805400144c000c042820038041d03038040b030800c82ca03e540d000f160b60500c0c071701e0fa000410a5000c0115a0740404103010040300c4c6541d40100707002501900c007410009685030050300492100301881d00f00210a030400600c0a0a00750070501d5a0341010041e00000c025150425a100b400121181c1c00351240c80301000045c032982d9941c0c0860300d540410105581c001c2c0d66868606c0000c8552118280440d040c0404043c0c00e09052082e40e0114000f0740494203210503480054510a00107003010f00402203d22000102e60341c2400250300920f000c40702960703124504400000540540e801c40d14400d400d00003804480e0503e011181418080f841c0c20960f90032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 631401214 1250 631399964 631399973
    0x3060c1d0307061b08160c0512061902040305010e0a0b010608010324110a03060e09031614150c03070221030f07050c0a030203090a0f03050607030c170f090709020c0316 74
    0x41c1d00c8400109000700001b2400191001c51080d100020f2040f00000c1c45181c490040101810b115242c00099074801d800050b11007410100c040002c15400e440103141c143c80351a21403e445143d50741d580f06030721070b982520801070042080d5005100501c4c0c130300815411540e0b0345244a180c03000501c42e43d44844003403c04200c2c281d200d001c4207018445519030f100c900302d00150241110b4401c20040742070b590300042091001100311140071050010000488030700780e0342c001c14081c030460180040d1152039220039a4001002c509400784034411032458407817520102c001d260803201d041108592a91401e10400303c848041a00d401003800603424000e0f54644508842034009c060300300806108903641c1c0c4c4185500400100540c10f41907940c0744c2855121820a2035010305407100800aa02240001c3c0040b0700c264042140e03400d051406407000b215034000c000c002c28040c0c0d80e2402152204040c455000420401000204805a03083d420000c03030301152900e03405440b040b00d980c2d400540440c000c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 631402464 1250 631401214 631401257
    0x90a0504080a0513150f0809191502040b031003110105160b060d08030a02070b01080a1703151f08071706041509090602030f1b07030302090d02090103060c1d030706 72
    0x8180c00c00b00d910b101110800020b002c1b070b207440615404110300d0004160382c5000441d0741c0c140ca4101070141544442c10755102c28418024010001e40a6424000810007044080096001d80e4132040c0c044841c508504002c00c0f909507a10015044c06020441142242d184040d290070f8150400c83c541401d42e91a0701051008001a5004008980001c00c0000d0b012456000d0110607000384044806a82c840c88455624481e1110103080044a1041ca80f003d4003508000d42e8000d013110b07841201c00c0c010f00041100300381801111aa5001521141102141c3c416426940091103203490441c1f41c5007144101e80030140a4012030007192100400070100c0b1403420705e01e00070885403008000001c0706003803140081d0410344564407a001e6400101e11504410b0006904c44264900d40c18074041550364181c1c000e44c0580d844c16040f5808a40c1800544c0d02c4462650080d4047c42022411101c5000000c1842000040700507111004400300e040075200040d41e1021782c2e80e5400c10070009441c002043c00c06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 631403714 1250 631402464 631402469
    0x9060534020d080a02010e1209040504050709050c090103140402010e150c1c090b0406021f0902030316050c040e030403150209121b06120a050c041e05090a0504080a0513 74
    0x10070038000034810000030b40c00804a071300c2158000c011a032250641291602109920030184410078044203100c6d1a19610190b00a0301ca08202d403040d664482001c41520f000700d4211842400c0890300c440e02c1d5170140180c80102c0c207030490031000f034603195001805161001207450300425110400000b001e045d10211801442c0000889110138058142000c0c0b02c80100c03580400038030040000103180c0c0c0723000c0549050f0760898000c1d00c81800d4408240c1c89600c14560390294030b549072001000582c07002d000034000c41c1a0407079a0751126503107040003850296a18007036800380d49400c1c01e81034407034804001d40e0203481e840b03410000103288016503600079004180780c1035400320b0b907008400c0000200085503444d8814130b06442c0071000320300f800c004041c06002406501c1c00b1850300081c0c00d400f0681d1101e0380c8501d21000c0c0d24100b54541c1710102400b264a4900c105100c0c1d680014082440c00a488a50003030701c040060086140c140c4d10035143c1c0c0280c48440041c0400407900419079801c803100e1002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 631404964 1250 631403714 631403719
    0x70201120c1209020406210c090e280f060e06010f05030a06230c0424050a08040f140706030510030c0302011d03030708030f0a05041e0303140a06060906053402 70
    0xb20003147d40540c484401306030011104401721080000e19200b40340507001c41c451403440541504071000d43c800620070000041c0f003840c1800c400384500000c064143c03c0059070b00030400000c0a51980b8803ea03c2c0c800c0c181c00889110640000420465400160ba40b103003660000300854020141c091092004401d00c00c000a800001010400d000b110304e0041e0046608003542007802c071b1100d5070040d11440b03100300310348c001907810008001643d001c0c04425801c5403007110010700440594564550420140d10440c1c1250055481049269030500039a034100380c042c1d011003c124615511140c0802c643c0c4002418041c0c0c541000105c01016038005004010240c240c0366141c115161090321603004442c01080594090003054101d0041e01c00c02c8e100300c1e4404010b48101e5a5945500103061003c242242056250b5402c400c021075955200d034012007a030140860401d041c07000c09001d01440d9040202001300030702400107443c0d9102645c8610030401c0440414082c0e1401d040050180603210194 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 631406214 1250 631404964 631404989
    0x604080f071a03061e0d032609030a14041d040b1e041115070b07081e0a021308151b0c1b030f060c070201120c1209020406 54
    0x900a2004540016510004016030380c24a403100c0b104246141c09004074040c00300140009921401c060017643c0ca4000340c005041c40401c650340000d00007038100c0390300b2000581250301d8404410b86c501000c48140b45003482140a52074040c1049680740500c40e0b10b00f0401080c2c01c00c0d500e4640e202000c4601801005683c0e40749040c244a80c06c0b100f2000f03860032105124100300089102000c2809071811036413418000c011515980c8a4440c00181000401ea00c1a03214211080a2501d60010623606116902c540c02a281101000e0603a1038018902000d44000b0b1101100745c81e044072483d940540d00036401038503001c149544104014294000c0b80d0f980c402e81001a55207080485007500c81d500d0144201c641d42a200d2240000780140c00c000c1e9101d0b40100600c103801c000450a007490103001404907a45919201421440d1102c26180c950480000041040c10b6580c01030382d0244d140002c2c1424885010072090050805541484140582d031355915201c04565030f98100100a000810604 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 631407464 1250 631406214 631406219
    0x9070c030207120201050a03110f0c070302030601050108040b0a0504051f02181009140d170d14060d031224050a0f1406030a0f110c010b0301060503120d0b0604 70
    0x151404001050580251288100014864603c1c2d54048109581a5034841c140304056509902800594210011040e8280100e4084600345800761a14503a0308004001e21859801410b05082040c2c200f241000391a40412002c9185c0c2001140c02208040c40014182c0d40c1d400c1190411020406100469840050080200203e50060580e060501c01e06000400641d004c001c41d0030a0000c100340894a441010403252040e00d0203902c8846010300742d550410002c0e0384503603413003146203c14900c002c404100e0341d452038803d209080303002c40c0350f81c4481035506044002640e0309209040041c02c1148a80a01c54980a180c00c1031600301e020b40030f6450100ca201c1044035001c0704902580340981c030419800180c21042d8914541280d1200c20324030304000c513040a01c010343e44001c2216001c81d403101c0c860101668580326690614540002c4503841c1c10558001c0c500751000f2000c8644642c0c1429402c1c4800d60700405c0c0110012203504040395141c40c66540f00f0090103000101503032042010800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 631408714 1250 631407464 631407467
    0xb011a0903160603051602120c10060306140c070203030318160806090c030a08160c0e0a050f0f0402010909020d140c0a0207060f0804021c050a06090605060402041a09010306050907 79
    0x60b40103880c85900c0c240803a598425007080030a90605441005070b1040480724004108040180010500c078001c0e02c901e40110f0b040001603e51b20341c01210f40381e9481403c41030a00440c0c00c1030f500841c104d80c40516120507900040da407400003400c465078030000c3c0a050b0600300b0040100101c88568070b000851a10f0b60f8205050701c600e4115110381c0507000703180804065140214080701c0541d40200e00700d0905108400910343c201c01003e04a8544028100119065000c009418480c2040c9400482c0c2454a01c40d048501c590140001504407a26401e100040c1c1e08600703000182c6080b207000603110094426004040d103082c052091040d44800103019052030f0345801052521065000c45003401c2c0d41700360807601a0000d501c44400a00c1c2c0001203001890a0450300455960500010214400c2a02e52a0406041006c229007041e900c0c0318080801200b40911076000f941260304601b404d150060141074844007131141e5150354030029508801da03000741d00c004041c0c04040c6c102070441c545102e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 631409964 1250 631408714 631408753
    0x3080901170907050f0f1e030f0a06060602013c1e0905010b0603090a030f021c11010c020601120803130506041a0f01030c060302030a24140d0b011a0903 67
    0x42074019449841744860364180514000c002c010302071324030101c244001700c078007a80e80a00d50205506015217030f420351100008101010340c0c82d01402c40090f00f5450220040c0c04c485171000354000e8010f03200000740c440a41560a4558400c010107141c2003241c0c80031451008003c11458070b4000c030811144482030a4441d407240e19141c0c0301c0c0000700305d9070610300c00b00041400103d6a20880f0340c01510300d400064420104000c0704000740c0103c540c1c104440d000c5181c100410300b85007002030028000000e00141c24003644840caa12400078141c0b550404158104024450b01c010300085400000b040b201064801440c440313507000003d07038145003854a0410365844003690b17004450001c80000c00c2c0301c500c0700000f02d03040381d902541c84005940f07482400c3c2c000c0d4000500703c060042d52550081d5030941510034040101c400308052184050400e0001c0b009209001c5440c0d014100003a01c090001f103920107020b040d10390314150000300551003401e03002d4030700c07640301000d4140c024407411401794040301e107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 631411214 1250 631409964 631409969
    0x13020c010b15070f2a0611101a0103180206070b041502030c090d1b03081903020906040902070f05010f020d0b0102010b0d021003061d0121080403080901170907 70
    0x100c0c81d00d0b200d0000b03070b1811030310701403407401419114000c4807050004207054110340c0d003030207003540c404407907013004108104000312a032001020403500c901560004100388081c40900602e00402c000c440c0030300350403000c008003800e242c47c10b0603510501c2003041003140c0f10b810601640240f10701d9031810546444040000260f03411106031148402180901882d4001d0328802d0030101360035820700000804101c4502e15a00c412345000000344501c92000c42c000f80108041c500a17003803281d40e840000c40c44400598440c1c0300404161041c403900c03486558500880b021180e10410160712056141000300c000809200d00909645c6410120744030b26440d85c003e00984100144100040c82c1c001c8010b9080c3c1700343c0100c2c59480340040d1800801490008441c01c001c80840c64005070850702c40842c5100215074100b060070000c0c1c0c4400400c00c9224400d058501212155040d0011000b16a609c00c082e015a01000b09001e40108120b086644503144000c15441440f0074500d8508004001c82e03150007090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 631412464 1250 631411214 631411219
    0x20103050619330804170c1e060a0204120f051203131214030402040519060806161b031101020d090609020906060405060409020c03161a01080c1e13020c010b 69
    0x2c0c9404856464001e5540c20040b0440d10382c00080c0d521507a501d0381c0e0021071110404091070510426103003400230011810301928094880e02a04c030400034803854000000c0605122a0040200740045a440f50300c280e2100d80c04070705007581d10000d2410782e0501480c026544c000f10300100421450140c95100b01405902030000d09000710010b40044034540d0000483e0343c1c1c1c0325400c101250041c142a48883d6018000c80380400010303d401ca10101951031550000810383d000d803041c4003280900c51040c00d00b941485c10a5055800e180c41d400e01c06c00908280607043c416001d04600050310207404a44106030103030b00411500d020361030198024038420030b0a074068860280011070b02d0611718112010740d10700910481c1464542899813020b075010100c143c200d0700040c40000d0000450621015480744203650319452410030700c6c100000c000050b0310482042e0301c00a0754041d02d8540c455200240300c16003070f00590076110300300030a1a00b0f421920524046100294404032040c06502c5141840003c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 631413714 1250 631412464 631412519
    0x9200a1d03031e0a180801090c05180414070806040b0126060c0d06030516030b070306060e0909010e060108070602070f1805060d0c0803030601110a0c03020103050619 73
    0x5801d0540d6401144841945090610303000b11003051050060a100d491502d0010130300040c4102a1300d41000070345c00784c000c40e0b458091110030000e0380080300010b494141d43c101194040628035105000000d4000341c000d040d40c8009410000c420300205001d450721000322051420107190460300c04c0380074401c24601c0c0d54075802940f06c03880354440c0f40b4511100400189016100c0301d200d034855130b204142c4115410b0b40c6140000006005205060700c1c50500141000c1842c6141807201c0003040c0213105400705803500005100300e40c0c100a03401410082540c4030502d540d00c04840500418003542d4081c190f00c628030000904450026111042d100e256090b21001da07a20b0441c070316612101e0084850319a605036100e5501e09540d480542d0090004102000712101c90310b0f840c1d90903109400c8142160030000400c4101d58100400052000120004042041443c3c60300d20b5821882e000080c1090707114400304a044e6120a0804c442c8c2000c0e168028107990f96071180041d028801c00e1125031b090301e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 631414964 1250 631413714 631413767
    0x8070b160809010207030806282d081002070c2301030b031b040e07170c03070f24090b28020f0703030f201b040b0a09200a 54
    0x10600950304006c1d41a1a510929160082080620309a2507141385e943c1074110b901050683e078415814004016855172805143c5400c0322405d803581903003584280d1035245002c01c00009100280c103107440440741c0310040c0caa041500c2c20415001c125804031928118500844450a450541c4600c40c14002d8804204610b81c040500d62280714164400e154405503031080400c0c0e04007a0400c49001401714140d46e03c40d5280c901c0e001400c18518440002640302003850340b80c0f42010021b80d80078005220359446018544005880044508480808540c59203c15005030740c0c02044241c000d03102c4244a0754035010140c09a641c0340e00703c0000d8075907000c130040c42c590110f4004507000862075104030280c0301882c29520241d40703054aa001074010888001c1d240d2140c05114070159a1540a1402500003c00c0742c1b180005052855440c49210fa86014007070403007950b540f00c1040c2100d40180c4003064040303000c0d0f0743c1e030b00c03100095103060000000054442c40a43e40045175210005a4440410401c403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 631416214 1250 631414964 631414981
    0x9060d05070e0a050a051302090a1a0307030f0219031e0f020c010f060302182e0312030e0304140102032a0607030b0f0f0d05010c021c1706040908070b1608 68
    0x9030a1061ba6008041c0922207520000d15800900080f040500403608895940c002520211010190146c0304d22021080c041c4e09a41402102c03003e0151010950900c0c08000000b100c51103a021b4000500d40d46400c1e0700810003108402c1544209100300810089800c0c4054002961010854071a02e500e890340070301c0d00d0360151003548152500506141801c5140007030f940b104000150981d00606009600070f401150034680d6108041c0140c007085422078614502603002280d060002420b150420559003034002c80042039804071540c0342290188031170388100507400d40c07040310381c5207030441e20f07520980c0507400740f290b454990030741c1860886c1c0146c0d461407011801c6808010b2041e510450300d0190720503a1424580b542d0380000d0091189212800540d60142110740c081c0440015170400e14141d25451100d44403030350045518204074040301c04c0414041805500100f445200707907515148801800514800d03109102d5201c1505503483c05e24200202c400001c49810307400280c4000b0011b039156 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 631417464 1250 631416214 631416229
    0x30304050a030309080705010c020d0e030f06190e16030c060513090504140a0f02011e08010b0c03040b130e0709051c02011b03030b0f0d1709060d05070e0a05 69
    0xa5400038040c080c1e007003440d9000c801500302c480054910b00014000d00b00440c10038881c00c0d0041034180c0003841000300405002d442071207010000b40c402e42240b80c3c2460f900002003401c550107100700342005002d0a000403064000c0ca03003050b0188951050704104030714107000c0d00341d0340d050f00c1c040c0d1000e551032680e5130012100351003805048038466424150401005041d5081607400c2340c4102013261002142c0d103d003030315000030300382e0a0300c110351005100340541d604218900001580c07088843c00d01a5030020240c0710300018070580304452000540e000d048041807090380c02520490880d00d640c0d8071004050320411005e03010701030304206100b000c9007249008502e45811140c020700a40140340f60301c5060303030b03507604100400e0341070106000103440b6400603040014101031182e24005802000f00040c404e07851150160580560340600b02c800120381b01d401c401c02e00182c5221202d6030f8510400c0410598050211004a600e04000a2041d12a009954000d003540d003034841c52a41d0b640e40040007201d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 631418714 1250 631417464 631417471
    0x1b06040b160507080d0209060f0d0e21031e010b031012110f01030f0e030406030f23091914010507030c0f0f031e050105011d031216050111040f080303 66
    0x10030b00c01c0100000060050000e4103214880d40070047c28000e6401c041891940146200d003400a00052880c0346401688108a01406460000c10100318200e08501e800c254a51544140b44c50102c00200c0c825151741c01044944103c021a4402c3d50350341c41d0807030858005845d0b034801c0011034a8041050000c2e0701001c2c00320342d0070403a200360b24000c1d101840382040c071141c0c11a0400d038644134030b19940f240502a000356181d0140c02960384602d889001400ca40c001c0c1032b401d11590502c0c501103003c584112405044107410f811240031074a40103c1245040c02036140420500030350034202042c40118807940e04880480c800900459540c0360040741142c0c180040c00c00480d408040e062400b902ca210820f00d071441c40e05001807900003010000390340503000c080c501211760716000140015640b098900513400107050303044290f10100b200007a00e440c108405c0001040000c907055690841b50440070703c05a0704603000704000001c1c003000c0411a4418001e00d4550304807800006603003200041102d11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 631419964 1250 631418714 631418717
    0xf22260c09130311010903050c120906030604020a020f0109060b0a17070608060d0609050c1512070503040204110a0801211112011b0f080a050c030402040f021b06040b16 74
    0x7001d5403800807800707444a070840280c08001c00d040030034500c0202482a1070b1103500175107506464020110181e407811500305441240c0345000e0184091580f00e003c01c3d00d801010450b00580c48020340081280303030035200c156000b0150700344282c407414000d61398451440700406403040425642c84190310602410240e104070740c1940200e0003000558415112a074014000030b003920a5440c40351100815240000000d46032500280303c441c42c54a88115a004800d8120390924202421480000d40300f20740109888244040007000801b10741d01ca90004e42004000c18000b81c07540c0c405000107000a000b4001c010100034030381c0030000d0096024015904095000d03940e01d100307a4402c1e00b44004030301d400c021420551b48520b4414001c0c1500f0441100c0505070380d07541ca0910307001c802c00901139280600f10700b40b101d2625003407014580d504400c80c1d43c030a070142c074041241070481c9040c1c0001d2181c40396611040b205801c00041c280c2c0041a010b008600038a03140d0003940b60141117501241c0c001d00c1010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 631421214 1250 631419964 631419979
    0x12061406100f020c03030f130509190c2003070b0a0209030c040e0703060c050a0e01091d070e0619020f010b0d0b0408040e0a0c1b0201050f22260c 64
    0x1078494800c2450741c2d4101054415100035156040119186800418108543c0d1b180801c11984540050140200918045401e1116418000010302481506c160400d45443d12010460b0744103010301c0482d0008032444070740e220b100801c0c5121a8132500409411503904041d4804149940401d0098540c0c040307008000d880c500d00c4010400005205452607803103903000d0040d00102081603885111601c1006458840da280141c0000812410060015506119424100342700402d5104030032010003c1300b84c1c0307118040d01c0340310090f60344030401d140071a44100d000078030124000c0380f207806d54003d0f111502106c0c803407182c00c0341413802c2c1d600803030903550002942b98101001c107020004c030390f0b0494042c4030040c0c80d054543e01461400e041c101c580101481e1580110082103602841041d046546581ea029031480b1590008105114580c43c2220048000c10240c1520f190000356030920f1500c2c2c0e400e6804c095880c0700003008480c140800003420f405401011143c0440400d6114411600800b0700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 631422464 1250 631421214 631421239
    0x60f040c02070320031c200a0f0c150503010e0609040f08040e0f06010305091b0a05060409091403070503040b180324070918020d020c030412061406 65
    0x1840891089011440750000000200f000e12280c0200d10780010050030001d5010384c189450060300705060070340302101004550340c03107501520408205100e5a03245103c10501480240350109544014160000040340d007020402001c8444044810743c14a20207004440141614180800d105144402c505080002d0340c614000307441c0c0f44c2c407602c00d6000810170380c600c2e100c400c01c54015401242011070300400384000c5218561009030f00c840246014083e80c50504034060300c1e1505d0842c1001386440f084690012039076015403c4002c0c0034050042078541e44d460008001428000600303445103691449011584039003c011180c4107604080110b20305854103003909000d43c40070101d18459401080200907a542c107001c01c101030304500854004109008001c403040ca0380c00f800807403c2c0b294051041115245e80c240c407402c80010400010786603904041d20b48042d108079030111010b80000036012825281168820402c0c40c0250420441071b503003100244980074064810650141d54002d11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 631423714 1250 631422464 631422469
    0xf0212090409030203040e0a09050741031f0f02040f03080a0c02062b021602061b120d0b060304151808190e0f0603070f05130b0405100206060f 63
    0x80c1c1c2c0e00d10702c40e10449181503502c2d4003040145400344ca018448a8940c10804144a02008000041c04d46102c40038122160040340e1152024079076801900d03403443d0a032140d001f00e00150200305020f006010b84410890002620401502255090b8002840c1c0b20b20400342c220248207480a0b12000000e002c441400d54032521000d400031081d50007040f100c0700001c001038517400050715451103110300751840d403840303400c2101c880100000300503e9280f06000c071540481502002300a5903406862180e5650b4001060300d8000c003c000400a1521541417448000c14940f40242001030b40ea090804c400806d842c204595440191006006486000b486421034052940304600c201d601203841381c80322009940d10f80780c40c0c119013005c171a1070700b00c542d880308407542024144103032860494400d42c0d0401c88a002640901014160504018080c50700c41c02860080c13007121001c0010a8101c0111079564103000e115038064041c4a0040800002c00041c05000007045070142e50020000001306034180309 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 631424964 1250 631423714 631423721
    0x816140c0c1c0f080c0f161409040203060606091203220b120f06040f1b0905060304021c1412041d1b0c03040f031b12030203070b0406060e160f02120904 67
    0x40051a502501c25100f00a00d400c1004841c0b00014410000e4800c1c900f52302c00c88c04040c00c882150280301c90347c00300401698041f40e0154480d80c00c0b9180c039240c02e07012000c04c64414458004032a0f91000090185e407600719003001c1d000b000416000100b511361140f07600b60282c00f5640f501124090240c01085620030300740308941d4094405080010308030800321406003500c815140310001038a8140039000e03400e50001110340904400c0d9007940c40e609003907000c6050100ea815464001d8519400c450f0200300c404125003109800c00022140d5000a1032804076640c4c0c4a441100d07005c444012071130007620b00b40031205206070350300001c0700401054100c10201039441804070440704c0c0410400862502c18488410300a10f002d010140d20b4085160103070041c141d030a4210710110300c0c20240d00720000c0e60007c01c40c0c904580c2b20348909003d40319032402501400181c0c0000b41e51003aa00d040155001c3c2e940c00001061040e80d0f181a0011341c1c0705000ea0f01d42c1802420008413032410400742a860400d0341 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 631426214 1250 631424964 631424977
    0x418200927040c080706180b0306061317010f06030201020a020f01202503080a18091e050106081005061315091a03070816140c0c1c0f08 60
    0x1020841200740311459145500300498003240ca180700d07100d0034059000108030400c084d208134285008800020941c169800800d44940c0c8155600040010f0301901d80c0000d0381e46a1055280c0c42044c1a2174138a40200c01040c1102505107610f007220756000360011b400b861342100c0d01030f005070880380029020320a8242032020741c14180701c03501444411501c6640e04085ca0104131034007400810700c01d45140041e080e03220786410701d84400000d081c00841e0341102191b0345000c40f0b0a01c0c2c0d6101450b02c0a0071003180c003070b92100e031905242c00c2c54131a0600600c0d141401410120400b04416a203550054405c0c0720b0076240c1084200301c031042404a810885e0017810942000c4200d0342e00700c2ea5944014400301c0c01e002c0d085000079a150800c1010400314803000344802078000040d429440d090400410038000200114801e0301c00203041800a0b004800c54800160b803a05d200b0f6441004030411941c035002042c12901422540f070001c50010120710001444e903a004404103200076140d1160400e942210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 631427464 1250 631426214 631426249
    0x1f0b2b06240e13021f08060a061b030e030601090c0806090103030f050d020d05131407060c03030903030207021509120a15150807150f020c18100b04182009 68
    0x50020f6400340e581c4407a50507400d0780300c00d440c82c000c0c91000704c024000000a0f03c2c050003004013520900c40c413a0000c440d100303400b0340540c0d2000d50f04820701f0119160000d501d6500e4041c00f91074000b0420013003540003001c41c030305940c59840450f20303490f080c444011004d00c40a40040c810031701070243c0d80c4c0b081004181080e541c3ea4003608000100100e1811140f0940c0c1243c4401110000b680800005544400c0300c401c0042c00390888628100c8003804031080354100500b05643c2d101403004042c002e905540c2c0a5070040c00c4e600104102e141c0f9240c141d8400c0a005100300c07008150b1400010000840390151039020042d15078100640e281d6001030121440b1011030007840c0130b00400c2c0c1e604204101001803194403007402502c0b84801d40503200c00e16184a0300110742003510090056110b42c407614a0340690340669004076034604100c4c0320b210502d500301e92506a0000f4002070000560381e00b503103040404c00400c00403050701c4185030941c0c9200706020903000b031041c080c2c0c4810b40f1306240c080380c0c08200d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 631428714 1250 631427464 631427491
    0x23040f0914030306011713030f11030d0b120d0212070c0812070c1a1c020c0a03020f0606010c17030a0b0d06020a09081f0b2b06240e 58
    0x45907144501c03040031030a146126072001c020000150390080b20300c42d000281400f1018142044020803503480100a03010f001d0002440400350140e10420080d001344110b4000d0780d4841010803c4900640f5142000d01d20803095034074038030b20485010a0910203100d00741c0040003004440d0a00780b5680d0400e41c4d007943c51400e84800043c04110501c858114510800019942c0d065246409195144540c209402c0849186080c00d040c0e02544103c070000a0043d041c8400500d9003c1c0500181c03040320070104c0c0300c0c000e0071841d070308041e000200b111104200d1070176202c10399160001103032059a5550064510210055a07440150a00c0000d640102007617101040c03802c0c840e40446c160350003200c000c036905540001c4400f00c1950010001d03028100d61009002c0e00c541000040c0400c12041140142c15651840c05154556680c0b07103009200c04140d00c062003e090052140111745000242501c0890a0502418032031208250a01129078201c0f6080381d420704110816521000c000c00c0a4a102003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 631429964 1250 631428714 631428731
    0x60e03030d0203070206011802070c0612060314150a0b01080103020d060204030c03030c0b15010816180f080709110711030c130509011a03030301030b04080f0f040f23040f 75
    0x1c0380000c40c403130f02e51500240510f501d0b11140b0041c0214070200007040c0d9105200f00c2c4000340d00c080300d190071960a0700d040f00e0041113841102004050035403004000d42c20121041c0745800c00070406407064154018444520760b20030040704291881b01900c5400248200d0043c00113140c68120800c125005501c01820543c503a5540344401d2840e400507408105a01c00000800568614045d4400610b160600380d651089001034850310001d044110340081d4400f00c2d45001e44292004e10740380c2a090110090395a8850381203070021514003416401c2d0144050101356400d6038041c1010f001c00f01c010943c0350450135200d02d091240c803000b03495454051088030721551741e1358900c02c2c4004001c003240011941400c1100c1c034212034580100704e4002c04000c01009044e40d0100980f81103e4000c0c15400081d5154a091600751045201c020f45643c000300740c40e80e03455041405841503c0030010081080c1d921022030740030506107034070f032030301034007002c20401c1c0d250706003034000c0d100402d5103c1001c540d958 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 631431214 1250 631429964 631429987
    0x2030f0301060e0a05010509100815090103080a03051f1206021605010c0305061c140f030c070f270c05041508060406091e0e0c0a030b06010e0a0609060e0303 69
    0x50080c0d002a0005405104200c10f5151036150a001000c0c2428107615080d19040422048a000d00c180b106021400000410301e114480c56445100350042180d42d80f580c4a14054032030360000000d0304002403401c400a4000700308d00c040c01d81c001440151540d8520b2601c04451200703800b81c0c4085460507020300507414481418200081c401c1d02c241d0001c691891411001400c9a234000c112610a182030103552044d188030040ca030100d030307030801e94440d61000c03146825442c02904455505030351200103100320b005400400c0d4002a0307044a50760b4a81e40e9900c1c0d4200b5403d1301d40320381c6030058030b081c01c4030000c4c00daa45e07501140301e002d0700307042c00b909007a541c05420600e5850951000041140d180c01c1103154a007a02c2944c000e400c0160303007008a081500600408408184040f02c00070b60b491a000182507410080d4880c01c100081420034550384034034168541d0300017507443c907010800d001948600c2e0303c2c10020390400d45030320395107600300d161a0150848280e50500040c58050104110000c40074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 631432464 1250 631431214 631431217
    0x30c02091302030f0c13240b070b01120201080613060f080307060605040504030207060507060f050a1d0c030c0114090d080c0601090603050c090402120717011103060a0b070302030f 79
    0x1a01c65048510308410700b801814101407a042d40740751190008a50340005640c0e100400040145a82c0300040110780c0c1c10055080e15000c401036241101c161900241180c01e603401007080c07034400c1c0e240f2204c0d6640d0314500c4c1001041d034080240800c00c060001002418040310600c11050340800224199969011903191030580ba0000f00094000041040500040f40103100080c01c00ba00c00304a6881c00352002503e49419016940400c00c0c0000c130341c3d00f40300c00342c2c002c80c0d908543c4c901c0410660901c00200402040c01011404450342c410380d1440c1c0000e0045000c0441c414050060095807404100441c1c9040310100d114451110074000a0003544405401c0c200c00c41c41050340c5680c80380d149803032900c0e02c02e05030f016281031400d101052000400c08245103104a9003030303d60300385641b6203100003400e007580c0a100205903c20ba56000454128642800b1000b8060740d00030451310501030140901440201c4456030001d280d0314003080400d15a0004000040c02031042e20308002040e401480c0700e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 631433714 1250 631432464 631432471
    0xa080903101b02010c08090c0103110d150303140a081503011404082110060f120207060504020418080f0c0111071202070e2401030e030c0303150306100b07030c0209 72
    0x4000c81d5001c42c0e08040c1c09100b18420445d603804d00d86014640009011359409a04160741d042641740c0c54940b581000b0314040d15902d40d0408028081d411081016607103002003444150009018000d4610001450f8000c4640c0c00081340d0716240595529001c100640c0a01800e15070551f50315020306201c41000034055008a1045c1000ba45d100301c1d058a04107403690010042c5220b10029040c000b00050000c407600440354942001c070800043d801058800c18508000c0030680d0b400090210200200c90780710510462003180c040062485403034602e68102c208500c000d002070030400501c0c000f80020406040b003ea9000004a070201c000d029a5030036801c418403c0300c1c25200b0085541c1d00d03d40500020000c0d0030320940d612424034261402401800f10124080111281c3c05040c03261a4401e411a004040c501d0088070350307074592507c04540c0d0b40d1080390381401c80307010000356030200d1031301260040c020003c101c64192000d0810045000c1c3d42e00c07007401142446100e41034400140c4030402d12038070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 631434964 1250 631433714 631433741
    0x908040b0f040305010c05030708070f0e0d1a18031c110f04081b0604060c020109050603100e06120c0105031306050f1503210a020a0501061403070806090a08090310 72
    0x407101c3c5145000b40c291003565900345c0a0000600400c0100e80d800010075a0045041c60f0140320080280b4041e00c02c80705403543c0c50341258400e00602c0600c00011925200740a0003c0301540d595900d10181a21940150031381c0c00a4008000841452001c09840c004290a250000a01c0041d00310603070141c0c0d01080007581c0220010400300040403003800203c9881007081d48070a20703101d050000072a1482140900424014100714240a6900c141d900e03c010b0240503104980d2402c0c100c12030074100b41c1c14880e020b0201190720000d00f241c148050301c02240c842250003491505503d10042d03034190801400c20480d4080b007075590010600c28050580610f0441c19141a14103011241311541c2c140301280d14005c0e0300030302050a104500d4407544082c0c042c41c00c4a251584002e0400b00d060a81e0b01d00f01422540c02c104002c601c40759401075102d0400001c07411134142039039800860b03480b4030046850070296009010004c010074004030046c4040c4800406031022000c01505003421900d000c002081c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 631436214 1250 631434964 631434967
    0xc03010501030f140a0206030112030e0d03120c140a08182401121a0702030c100c081b03010506070f0605070210150e060d03020f060412090b0309030d0908040b0f 71
    0x804d2040c90010ba1a00c003010740d0107417054003025008034640d0311040c07290304203d8200f03280400c2414400e983c250a80344000380a40e03092a110b040080140700e10380c034140083ea1400064082c51801040f892500608034003260341402c1580380700341c98144004040e54501080c0d40c00400c0700b030074144903070040c072207584030310300c140300c0b5080160703401d011050304a1810200d030b110510b40070500c0c40884500800d942414641140d444a404a045010305d03201c050052040822400a00d00a504901b02c000c0c415561100565151010412460f40c46c09000b0300520b020401884103082100c02450380f94001c0403556005d105565840302154011600800140c01c007105803213084065001d911109283d0320f900d1004a42400c0003502c1425014280621550300000e81e0703020075000b441030141c000c2d001e405680c1a031504e4107192501c400601383e00d0000400050011404900560540e400750031104019400c000048407450001e12400e81305494440e014000040c91186003002032001c081d0a1400c00d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 631437464 1250 631436214 631436243
    0x80106030501051b070209330f06090108010311031504030e04050106050f09010e0a080f0f1005010f0e04020103110406020f0c090105010c030c060902030132010501050f0c0c0301050103 81
    0x1401c44102030400840c00d50aa40c400110550304000c3e244030301d4044440e4583c40d218100c20416410101c81c08c6507600310544a0141c2802c1384203c0700e0300d072820070303942100205041c104000440c0319170344240b030229003000010f2000c2020181c6803a4210005001c450040080303840a031100c10040703c04a0003d00c4e040c0c15018070381440c2c0200390042c03c56040040c02d1003080301c510403541c01100b0341d00e4100045081408459600c49108800034400a015035980194030b81b912911041c2220914107a031065080000c0d01010b50303c680c3e03048038042404809442d0030035442c141e0070070010748164100360300c4000d82e6486100c124018002403455800071300103100080d000a08000804240350f1084000d1001080280d80000c450a8003903814940083c107002e0034036140c00200002e00002c2c2d015880c058440c0c0400350280342c240003040c00562103407592482e0301c140d603950840034002c0a0005200b484411040103660b406042030503603c205454460041d0340c086421102c0c00d82c02568900002c2c10391 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 631438714 1250 631437464 631437473
    0x1120302031606020406110a0b010b0c01060314150705091c020f1206271005091009080306090117151e09150708070e010e0d020301021611030a030e0904051608010603 73
    0x46004050200c1c0140c42426400c1d126044d2764641403045481800340080d03500740e000420f40c40f5101559100c251491427681d4030040c56683c03003c2c0c14a95982a0119010622450203013040d11a0500000d22444044284103491a01d9000011007241c200907081d003400010b41d14503400f603000c0e0540340700070151482e019284440c0036512200381150f0040308003e105030000041043d5040d20301220012505071152401e5038503002c10600c0552660386020811020881c0708402940681000c9941c409140d880300c150404441c859440c900c01c40d80802d810002250910800f994402c010714400c40c4090500b050003120305004480c503001580188001002101050340f50030780022207440d006c0913602d003118024004448028085042c490f171040c08480c5590b401003c114002d40c080c0007951203040b801c64525018068100803030f1010104000d0020360308001404580040e010340d0703a18100f50780c18040c050201401780c400e5940303005110003025000940032200c802000c04400004503286103041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 631439964 1250 631438714 631438727
    0x50f09100b01050414010e0d05010c020706170f04030e0301111c090c120507090e0604030e1c060b04090204020f070c050103060513230702070e1302060301120302031606020406 77
    0x1881400c262400d010500d059030301805940607900203280007051206044016a1009180020385a00020702c8031100704100e819001503000c0042d41d000c03200c02688070740301a01e00c05090042c100c00d824408002514043d240d41180e50024000d04040c0c80310144240813a00b0b6402c16000b403880403d0002d142581c000040c4640f0a00c110030b4003040140340200d5890f0084c1c00210302c940c00c4850701042c11201407110900000c001009a04802c00c02c41035481503070364454208681c1030b004900306901d44600c0b41450000c8101003125007522581c0b900380c581d1408010031400300c4554100d83e803001c3c048010303210351004001e094103416829032103450500d00702c801c0780610303000b8604042c1420310030411a102d0407220346615000030004126040424141350440009804000000001c003090000c0380d40c000c10340005440d00e184102c1c01994030441c05a500c440e41202c000d4001104100400412038804495400580310f4410340e41b41c00002145040f2142e1965029903590b0380c000b60403c092500a075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 631441214 1250 631439964 631439983
    0x118020a140a05061b0d030603300309080d050708010e15060906091903110406170a02061617030f07020c0306040602030907030b0408180a03120309080d050f09 70
    0x20900031816580440e01c548282c1c843c40340180808a054103080f20710500d41d50b4505607500894684640300b0744028044e00c498441a40e551360a041d08106902424540c00e0300806940d0249403209050841280248000c90096904010500c441e56106100c0c0c010107003c0c040b50f5580b05819418001c602c0f0341d010024005408000e83d840b4441029100e25081d240704c2c5d80700310748103500e410450022441014407900c0d25450144456400f1003000880711004a1100c415602003114585440404006c1e0a18812440240d40001c180c28010702c2c240c2c0c000d1401e50140c14000c801d0b460550f44100141b0741c0160269400000802040381c503d170000c000d15405801440242101c22080300841c0e2911000742014140030b400000181c01d143e401c1048400841c0d11450840441c40d090034110300a8000d003000e0341d20f07031b1080800c07004a441d1080740310341600d8005001c0c8454018074002a40107100c900c1085410f40d40034000e510b02c069042c8031b0148a036080410400c10380c0340c190b00e6107050038540b2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 631442464 1250 631441214 631441229
    0xf0d0608030c0604021302090402280c0f020907021213030201020c04020f070b0406021902010506040606080702032d0304060b0f031603061d1c0f0903020d0605180118020a 75
    0x3446982c0c001180026507981240c1c056a9422400e620079094101074410401d8068100740009203c100c4020300c01030107030425610004c03070410740c00340c01811242c074904058003a148003d4000d2000140c0f8140360900d0300840079004442c151500b0b0a5001600d82001c45006c94924a001c42002596010300c2142048a4111011441c124041805443c140580d000140100e51000300280812a140e0b040700ca0f00da51104400700e042c030800384003c1c0640310440b0032070700840c100000020b405001310030b02d1703015034a95006142807a44603900c00400a840d403a0030154014011061000c80312000015070085000318404a800c5410000b1700501c0c1c040c002030180240e0100041071942c4292500320410b032031b40042c0104103101030800d10306202c9480c51070303048180138a9a6a104810703c0c0300c200c480c844c0603078840380b1250582c1c0c0300c251544442440080c1d0041ca980040d00b0014030a0340c040e550040d05061401c46140c03035420b07030500b1140b00700c2003071716010050b0019101354544038a00310000c1010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 631443714 1250 631442464 631442467
    0x604050d050a09060f0306030605150a090e0c1c0c0b09030f060c090f0105070c0b030105030f0c06090105071b030503040f0e010302030d0809030706020d0c090b03091e0705060f0d060803 81
    0x41502c01032100c501d034442e04041022040c445c2d0b03e0188260802d8006642102c0180081e08050340c081000b543d812080c1845440d41580c0003540e2038541c05001000350301000500b4001c02814180f00911002c103031045402c3d071240d02c10301d001401700d143c0f0350094403d110307505441d15001c0302454a01082e21aa400040d03018104110b80501420f04030f6000d0300782600d030024020040c80050b10180a03d100051000b2224880450400b010310b003c2c0d8100d4004030110354121034020b5013503480740107441d07000c0d41249040040a01950048008200c2c5500c07035481d0340c420340d0700400a44031301c0c6821340003210726410020781040f006403c2110300f0003410780c0d0718115900d07515590000355522400c001d04028040142c3c00918120340500640c2c05181d0040019545c0394000e242c03003001000343c00c00e0600403610401010421825403070959200b0041d0900038503414426500c030b42010301d45c44540c009148204103010950f5240d0030007a15140440380c2440340c4403a00321b800c120079210907070000d50f45c3c4da10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 631444964 1250 631443714 631443727
    0xa0b040b13020a060e01020f060906150d03141e070b090616020703021e0a09020d1401210503040b0a030902040501120b04060b030709020c1606081e130f050604050d05 73
    0x495580c1c280480c0c40794201742d06501e42c510010b03801c11400010300c800600801e0104100d0b89004106288580c0000700405541200c03941042100d50324000c0140000321825101c41c2e1406100c401400340740b24101d035880d060b000c070a481c0d030304030b90003850704a403640c00010600080d0369007008050b4200800c8102c401350f10844820095980115100c081e100f100e0340e0b103404241100490442e41e02403400703030a01c014551114050800f0b03501034401100c0081c40c0c818000d51127402d1030202416200c81c185100400007490206500c2c0c0d100c00c8400340c4090004020000740300c01d0b2100181810f008989012541020301d004000450340141c3c0103c2c1d000d0221070800c0300144c0d10512803640030740e0205e00080e10000702c1021a00d440080e07040311341e000d8400591140e803208d000441103c51814503895100d0300751904012242d0401c01d441c82104621001c07281c28008510768046070b400008000541d542e00b010707446030610031010000540d150b4002c58148824807809000001c1100510304120346040c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 631446214 1250 631444964 631444969
    0xd0c0e03060601050919170a210816030608030a030f060b1e0c070e011d0a0c0207060509030109020d060e06010b0c0304030311150c03150a0b0a050901110a0b040b1302 73
    0x1c50174013a60b1150922080d410030704403104500380c002d840c6080003d006812003407012552196064402e0340e000012103128059a0352010a010a10fa0690380c0d13002d964407241c4041000c07402142d4140281900d030407003c1501001000507024803a010f96008c00d40d0611010308800300d032041d0f00201d4030403408005003110055500c5018452808200703d040c1e50303000c02250582010b0031a000114100005030000a80e55000e0f68030070090bc43c540f00d1071146407a07640629084822201042d40942c110b5201000418040e50140c03080c100701400100e0748804035400070302440e41c180c004075105996001d2141c4110000c00046000d402100c400a1402c074a600c86e85a40b03000d81e110050401041010340e44258209001241c10807148008090450030034035651003141e04101c2d9080c14901035100703004007500d016000c000423241d48402180c0b50421030502140d05900100c0d019052152111300350301207a1040015440803030003000c1103c0c0600f4180340c0001c02c07160240604e03424075045a040b07000b60303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 631447464 1250 631446214 631446217
    0x60303270a091b0c050a060c05070c05010309150e01150b0a020d020d0504030f06090212010911010e01120b010e0a0e1006030b0303090918160509061203030c18060d0c0e0306060105 79
    0x40f141040c2d941d6a65078600b031032800800050007003495003050010023103e0340000c0a403080b45d04c11b111042d0b80b60388620044003150802d40c40038228140c1072001d10103144169100c0035243d40114004100031801c081207040c40071490744840700c0e2240025414034208d43c10300c40099600e805201904118810810051460060b07000251035107401d03001c5082000890b500c10300403035038050300c7c141d250321100103080e000b400348000607140080b04c0700e5003060943c450a018002104161100b40d0b070050f54982c200c00400c00300500d01e05126155450540b0b51b0b5510f00b2040042c41559150b038024075207034030650742d20503190303004004ac181003400d107081d10354020059030321131a003c4c0e0300f58440b66110596819240d6a412400798140501e00d4250010500309020308255141512060000d0f00e61780d0501440d03001c1046200201e400a0022651514502004001c06007640e481c104c14160a100000c1d40340d800751641004240d40c03840c1c0c181c042d680081d10580070fa04128041c1101349400c0380064060b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 631448714 1250 631447464 631447511
    0x1e05071803080a02030d1103061005030601141608070c0612020f04030807110406080703050105010e0405030a140415110616080a0b060d09060902011202040303020c09060303270a09 79
    0x1d10404a1200120f910800a40300e0303804261100b4050b0710004441003000340c0c4103407040c078042d1f2154040c0150942c029021203028a6040e5140d81d400358112611540e00d810805d2050034564602c091034001c109044042c03c1094042c0c0740540d034641c900f00c0d0150060b0016a0b1440009005000c3c2071045402c500c190b5040301e801c41c42041c0e4911291074200050b982c1e818000754080d19081000c2290100000e100c0c0070f5a105800801c4a03903220004604210400c89000b00160700812078030340442e1044944100c07129400030307441e0409880e00801d03800c0490500403200022608030184d1070281c002c01410b83c004405c8a4840c420f00052000101000c900400300540681c807100719512030b0b21a0b204569409034800c004028214080c0380c110050702008a0071390000c1c5d000c00b040c040740c40042c42150100c1e54903400030240c03d500d58060014101d80100740c00d0380b6000a02c0742c12415107031a08440300d2401d030030264600c04c040c124100000d29080380c00941d004c501c1d14500c44444058843d18282 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 631449964 1250 631448714 631448723
    0x60f0c0307051b070b04050f06040f0302190b030915060d05280203240705040807050f0d050a060c1101060806010e13050f100501050d0305030a0506010201020408011e05071803 77
    0x251650003144640031507140d0344003d0380d14462100300081072900c542c050000d490048501d503400e02d01c98070412015004600861406e105d079103d040006103816007400c6400031808001d0000d00e50307180c68120864204660440d01c942252b000d1021614200700400d9004030101e035018014071140c3c50b020355440301c010301202c0100700b05201200d40725443c1c9142001d513034000d003201c061802c601d811055019107003610407181e007010703804904160300600030703581603501c08002000010300c0e18081004014010243d150800c20314020203000c41c000340403140105018180204071030490702c00003088484803650320401a49070000501c001140070547d641100c48200700488181c0725003a4200307003e8034400d0020038500c910a82c51610751004200a059643c03c1c41c2c0c10059a03036204184100c1010505009000500800005489640075840702d0f80080061000504040c0c40d410758a013101c5582900c01003518801d540d0500500707a500619030302000a01c3e00d1004a54a00d480254509603404003d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 631451214 1250 631449964 631449967
    0x6030c0d080a030f06120305120f01060f080c070f05030c0c010f1d060d0203040c090f090f080a1107170c0d020307030b0a0e07090b1002011e0f090b09030c060f0c030705 74
    0x1344100142c0c00c5074000c0c0c91000300c8251059030f02c0c94080e2403548200040780112240c580000d0b0213684060b0044e040f41c04580380d400085000004c2203a00a1006004241260040c00030f030b4003060041c540100128461001955034607040103c00b4900400544001c3c100402d40c640815051381c044031261850310210f0202d03042c4800800050710a000310f040b0a48502c0c4040b04000501c642c4492200c01c852100c40c0400c4000c2c464081d400507070784651b10251540442c1c018060004034a90001c043c5001d06180031810200101a04e42c100300b9984e103e0503800d0b00036580303580700c41024050481502811507072200003d00f20360100c2e464482d203210140280082d54000380311812940c00440d40d0f02e2200d01600d041a49131860440101106030704030f4040d511180c507100440b40144118104c1081c4010080d080b022840f080c203014243c0000004e02583d1103100b1100082c01d41c20b81107002d80c900c61b0245866502c4c85000d6890200e009242810018a03401800f01500130341c422a40c00698034504035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 631452464 1250 631451214 631451231
    0x6090b101d0406080a0308100f1a09011211030106090e090c01030b060f0406090f0b0a0e06160c0b0304290606090a120b041b0e0105040f090f030806030c0d080a03 71
    0x2c00900450b800140c0b140100c0000c40b0805034404455486003641342e80240e40203803180315018003c4242e000721440700c00f064080791850303d50724025105001c01490081d10f00503a4041350b6064400c440b84160800401000500c6240d400941000151801d02c800c50b8040c0341c200380e455512010305c1003071410300d907030b811640c2400d448940031501840c1038ec0c1d5019503540d9440c0401009900b19200340f1700c10300780356840890b0000380382c0101e5403902500c4e65024448000001041000d45c45801c4019400a0f10401c00d800030302001d0f403c000908003010326035264500740c289004d030785c40100204d64802c1904025401c0402855032240e400c082305a607119103e080403000b1482582142d000208a0442024100c041240c0e0301144c07441548078120012100d0b1505000d8004410140196090290494018859824980d0100341d2003901482d02166424079600c6001c00003a10740340c19000100300e041009158241004404040107064030b0310501c100c1151903403080c5010b07100000e4105a00d42c4090b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 631453714 1250 631452464 631452469
    0xd0812040c06050f0f130e01031a0f060915030c0a090518150c21161e0e0d020a0e0907090c0e0a1412070b0d0501050415171c0306090b101d 61
    0x100d80503001f584c0020902c0d50710b030f040c101c03171132848208401c17092051075001401d500e0b80010460f0142c20041c081402d140c40b0b40c801d04061405220a15805100b203d0300210b041e0f80d44564140108402000040d50741000081441181c038907100140c05039104925501203e0420700c11146c0c48040c2030201901c840c0300d40300e414100c41e0160401d611554100080c01090400041845840c44440d251060708950b00c06070350f04404002494000400c002c040c1c3c450b500d051503154582d4152004145c64042030322103014115441c01900c0186c401c1e80442c0d02440520010304c140030a103295400e0041d40c900040b030000c4d004003401d015000300001c0d03042c0312405135160350b250048418402815102c0b1a91603d0700074000341c00c000641d0807190b0131305c000080c0c00c0c00e16106200ac40e48401100110a074103100441c1040c9404410a904074400d101d841d4200d11142107001102805507038000c00c84918014504060b10280c0403c54801d251480102c2c0050b50491984050141d03c05015114203654000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 631454964 1250 631453714 631453747
    0x7020f03030703080f090a080703110d0c0c05042c0a030f08040b0109020711030a030e1507120c0201180e01090e010e0d11070e0a02090405090325020d0812040c06050f0f 74
    0x7c009208400c0400c45004058202d1648607000480204440f451020090203c0724011800340190132104070345010700503030a050308501404911251540140c900001d40740042e106110503400d095040905008100740d4092054981c000311890305c441c25041c02c1e00e8006d060103040c85807003202030340081d03808200544041d422a540100a041d900a055142006030440e907103450014464202140045d03c00132102040d108601c1d0046000100d40300b0f401c400f903941c402c802c002a030504c503032505d0085100b130b020241c81000d0311001402c041c0951502000302d0a81e0807052140840f030341010141e446c41080050041401e600b0362800000303030066a510340c0e040c0702c4540c10424802c0d8140c002c03c02a03a040f0b400400b2002e00940d001c000f59035410700d14a460f80076401304003607a00042007a013200c003c1841040810740380001c001c80e0400100385c1d1800b9266014100d00c03035270702c4944020401808401c00d1040020078803410300a20386500407080510b140b203190074800c84040089000c1c07152608211 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 631456214 1250 631454964 631454983
    0x617030a081302060d0b1c0816080903030304030309060c03051509060a08070b030402100207030302070e060f060403050a03030b030d09170705040e0a050705010309080304081803011107020f03030703080f09 90
    0x103180035a0f80d911410000e01600001842502030540d41d8010581441e03150624511fa5412030b404608061040303441250203c3c180380d003603503100001c0c403500140d0344c0c080c801540524400c1d140042c0e06c480a01d418800c1d500070408460505d4580410408884c103001405410310030308880d24000c0c1c7d40c0e082e0006003501656000b01c2d13018402d132900070481280400082d4002c0303000315622030521a1000c000c0f83d480085000040045c1c200aa0030482d000c0320341481c030f402c880c009040b845044c0d141c10200e030040c0c000741d10070748443c2d004494550034543c140c8540e2074a08400c1d070182000c079010002c06080824030f8429810381450014442000703600500c48800038040041040c0316100e0035880050f598401c0e503030180c030940a22400001e80d580607100d0700d042a54020310050071665a80c4648001d90490b04800c413401070f0b40f040f41d4113259428410a003113151002d0640b500e4641c40e00502c10b1803184070808501035407081010704046034004600c01c0e88100e00c142041043d50342d200d0900e040102c06c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 631457464 1250 631456214 631456219
    0x4020d09080301171204060f0c06020f0304030c020f0a05010503221b0315140106120906050f0a0c020a051903092c1f03020906040603020619030617030a081302 70
    0x210001c81d004500600c403d51400d55041110051050003c0d4004184a24442c7d403001c25000018070b141c00780a208a489a50b01484006080092041070504c107940100e800714001440c0d22000340031440c21403c0042034100c2a92072507441401e200c0083c2440c80064046118500e00078043c50903580040c12092000d81e010781c3e078090000c02182d0952904141d4001200c0320a90092005822440c901c5080720350151a020304200d0791078080d00340c918084030300304180540d03207480c0a900465014003a0601600101074034001c41e190127840c00007103500040d01581150050030703007000820400900c60701103204030110f4007005041ca14003a05e02070f000fa403240d10503c0391807500910030440340441e1141030070400744100a541d21400b4441060030141a440c20070800384906001605011760541d84c062000b0f0030005507036440741c0000349250481c40c0c62001010301650000c16450b41401381a0043c108003002041c411054a2503507142d01400c50020200001180050a803d0041c0310100b15980c01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 631458714 1250 631457464 631457467
    0x6171b0c0a050705100519121415040608030c07090b06041502011b0305040201050355020301030b01140402071709031b030d11070819060f02041404020d0908 69
    0x40e071418a494800520070944580c241400c1120034031b00400481b100301140020070100c1c07203410001a50b0160702c0124845102d681c0d200c4102c820340c0058680707809482001d44102a00c00440c0030041074032080c0e08000280c0d0418000c282c0e4010002803000107a442000020500e07400f00301c0400d8190081d640726141ca403040c40c0658241c940c040d0b2014540781d0010801e0625130b204044c1c03c0c0e060720710a0720b0085c00180c0801c00900228008217001c1d000c041700e20700002d1040e9144c42d004c00b20003e1003056108003e0b107404094044000000710182c0c0e4204413070298110f62540c1c136940103004c01442108422035400c40242c1269031554102c54131294059916510242c6000003d1002d8212400c810f009209900007005490b00e007140c0301500000080051800100f401c100711f0300d101c14002c0080d1940304808010460030010b001003042c000c0f14003210644080103090140554510201c428001403041006201400d0301e410b800c004520306480160307966140b020700324000c0c0820309014090040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 631459964 1250 631458714 631458733
    0x30e09090f120904020d0915110f070f060b0a06210b09040206070305070204020d0605030f0f031c0e060106020a030801060801060c24050115020f011e1e0f0f0606171b0c 74
    0x2441e44d01a0406c80405410009d40d5001c030703156142c0303118031035658440c00001d1004000041e1001c4a41054034820300c4003255020340c40001c55239104040e0050000f02d06d401c02d03000d40300d05401c000d40f80345000c9d85200b0301041d1070000109450000240020f03000d100001088014140a41d0072140c801d0f9001d80b045513254440c800c1070780200103900034280320340580080d03048192000544e604070203030898060342c986020000c0e108203014a80201000c901c0d01c074400c058140006112030740c020546500503203c030922602d030040c190f04058129409000f10940140b01d0241d20034165400b0b103a02070148510441c90348002c8802c0314600d441d404031642003000100e84600c030000068444240d41d0200d450020680e0891401e0b52070080d1525184c404200301008004c0c8150040c140c1c410a80403c0c1c24100100c0030400180c07403001c038000d400c907504c91014034041c01161107858010403082c6042c1e00b0010311030303200004418029016411200c40b20850560206400701140c01510011088580000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 631461214 1250 631459964 631459973
    0x8010914101509080f0c0a0b0a09090f06080319090f080d0503220309030201020c0117060d083c03070206070e0f0a0603050405060105040b06030703090f020607030e09090f120904020d09 81
    0x8582660307500451080e040010f0f290803100c00e444002c3c1203901d814099500384bc080328024400184a9851503403210b00c0024125070520007003110b039a600c184802c90135024080a483f842036a40420401c003101c4000300140440030404226010882c9021075407606c90804454145a015a810100303000c440180c10405400104000803240300f03800f0340314440c1030000190340c50050b03044079078000a08140051910310b03081180003501c80c4a00b0303000c0e0400181903004461481582c54880d03400004c3c40d40351146000180c1458992a4907800c2e070744c514984818029164080035003180144622640300404955a0042000f0003050181032490b0140d41c500d030050240100740c41c261858041c120020400c0e041030b001d0480d81000162142c0d00c0c40e12800000c0b001400346102c180d03002c0040d45020030050781c0b1310300200b1800b03000e40e50b44035003030200c40100020568081d00075600c690000100c6510360b0b0b03011130444100c6601c4403800da1a1490000130070040e1142c0e07050949494039100c2c0410410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 631462464 1250 631461214 631461223
    0x312150b0901031d0703020f180709030506090c06090609030705090907170a0309030311120313020906120c01110307020406080f100b0604090f090c0608010914101509080f 75
    0x1d4001da90520141c0c182c0d40f1610408400c040720400190040c410900c00744c01c202252142c100c03000361054440c10344001904042c008103442010025640c0801041444010044250081c03103107006071568a801c400010603510409100381e0107004045440f0b423843d41d081c40084000c20300a4080340c42481d040b69500c0c1c4521090090031100c28074030800714030300c44c000034014091a03415120245101d003188c80a03110400110000c036014400c429100f05081c400d503015500408840841c2c21b0b840f0051300c100002d00c440205400c0c011000240085603845001480051049007801e29181e80b0b101d00045505500c207011000e900141003180010741904c00089488052000d6030aa035042100701d5059002d4444155041d40d1284003404144504102d03903201c0000c50341014400075045401d995400401c0c0404e030320807804110544010420203406006c0c00c00640300f80d0180300e11900d05400d480251403003501a8103819403580c1d0241c00124050aa0a405090f0b52000c88416045440d80356964 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 631463714 1250 631462464 631462477
    0x1020307020d08040b070503190f0204061e120c09032405070f0503010e0a0204030f0605090d051e07020f0d0c0609061e0c062013210312150b 62
    0x51003061400024948600c3c8014040c560040902556881d6120211160b810103400c0e002003114066180500c45007904ca0100001c0020b1809600c0d2442c20b00c000d0090068000c40180500781208848000b59105a40035800c0d0f242541c006406000d41d00c1c02c480b000c089800c000d1003400001d401d0340040d499420451303c40342c09a181804182ea403d14112422482c419808020800510050104a000c64082c40e40075100c42c600508040e682e1300c0d00c0c5102c0c0200d0f0402d4500a1392882400901c40341808004210040d5040440c540381350403602e041501400e580050845c4400302d141811540d90106914250b1002400d030140d40c0307010301f0a6034407040d0fa4860701c0085842135500050041c00341c0d507803822130292030b18002c408003c24002a149045a86412a40c1a80d035410442030201d0800c0000b0450308500e21b81c54840341e58080003482c40405411050140100b142c8180566219030501c1049a17030601d090003041160340e40d00e20150803507020045d00c100c294003010a40b4410301c4060102e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 631464964 1250 631463714 631463717
    0x8010f140a06060818011104060807080903030105010c0b040204090f05160905100909030c35090319080f03010e06010e100806061c06060c032c0d14010e01020307 71
    0x20984581c02600c00700c0d0b0103881604040340c580c2000a9500c0c60081410032a0f05040e000411a170890488401c07155026820810100c2c4044040c4074980d40e0040d01281d01199810046145504010000e418601b60074801000c0c0d0b01140000390454460760840800554001d10171504106a46002615440102502d440e0402e2100380054000500c0c01114010204800b5884a29007070500360006403481a100b6002c2c40502120200000c490002c0540c04503044026a41d4046641014000c00c4095416505031000705211040360b0b5580410204010603928030a101d0103c854602080e0500032005988540314000c800080c15540c1e52403c140308000990b82c03000615240d100b0040c0c81140030078400d00184a2500040c0325042a100401d8000c40942c640c0700041442100d0340b003580e1003900f01c07000050202864104068101100d2820b00e6000100f0b006407030704000000d00d034101d00c50b07221881081090780c4182806240e10101d00005007560090054000c102c1105000c0d6009031000e00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 631466214 1250 631464964 631465001
    0x309010216030807060e0a120509040e15010b031305010c080a0506010302070c090519051005031c0806060a110102270a05010203030a020702041b0c210e1908010f 71
    0x110700c0d1080381290341079990241c8040e0500215403035580080081c6082c0807480e00c04c104090010a00200c0d0a04420035103903a0f0380c4d07503450b00708207000a81d00d8040d404507040d0301880c202c1780104018410581940c0703440d40d2258403603507818074110089001d4240030f0495480c000c84005480e90041491348204221300080c88940c880b10011000c92040322805811281d4024091140c506d860300016001503089410321154025102000d0131244c0581c0c00341d6003d44105d0007000300e800c05000e003888000750814580003091a108024190b440010907103403088000151220700d507802100040f1104510b00c000710748601d5a01c004070f01020358806034000b000c1e1060a03199032442c0c52510340c41554410ba010f94110303201d1155000182d040300704102d80c01500c0d40305440b9000b400d0074030a41103a4140d5a0550001b010707040090000c40354100041020840c81402d00761950401d0403190004410f0b2204010a100494141200030f0a500801c5d40e5500700114540036900c035801c4041d41542c06900368 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 631467464 1250 631466214 631466233
    0x30e010504060f14040512010b03071406030406111c020a120b0102100b0607050a0309030311060609060145080303010311090916060c0b070e090a020714030a0203090102 74
    0x40d140d07809107124800016440009048200b445640d0310580001411280c0d42060303111000a15060102400d8a40303aa65500005140707283c02c1003980c0003400e4005103a00c621002d940400c105200080025013000d80b540f02109510130210112089201d568284000c0c0410445511000c1d500c80717183c4500003048400746182e800020301c2410418103052b00180f440740c800707903810b03006044070091055100b4800e0000401081e424424154050700c039a681c3c00141e811440c010b070450000b03030201c0d4401c1e8040740c20009141c03594035640ea006102400e00364020424224421146002c0c4051610802e5104c000000c08080045c55604200d80d1800d01c650a1501e5602c9103076240400d10014118803030b40404241c20341054104aa081501c100c15a09158008003c2007540021a4016000224070000840500210060542d0000041d2034070703440380e40d02040060800f00010741030000321070740061110304100c203041c1140301ca00702600079603849118140003c3e44076003110341254050300800184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 631468714 1250 631467464 631467467
    0xd090b06180105031e0a12030b190509071b0507091a03030f0f0306010513080604171206060a03060e0f16050c0604032303040609120203070b04290901050103030e01 72
    0x1502e050f900040c0c000c06000741c0d415505181e400034000c0c9004940144610b180c0800c001031040708104220b0b0b10301003078504401090044903003003144207218017140742109200d180d0f202c200964004007240382040d4030a000d6482c407036055480302c0300180203220b00140040c8044407508455540c6103c003020003400031194081c1912889000c018000e0b000d010007207458020407074000345401040626000b0b08200c081c1c0a03007026100176401101c0540e00400802040103030340c11410301c2d0104440c401500741b041c4000c02e02c600000103040c0398869803012545d2036541c0d00c2941b150004040c2c1c000000654104000b1407118001d056400c0c8905010783d00603505103e00540403101c49140d6140100420303a9540c401300c0c2e5a40d0243c0c0800c440a110700d448200e5030f0042c00203076001364003600d000074120401d482c181c100e6040f81148482135400c1401100c0c08107121400e0b2580c07203a08405003122403000d0259940424445882c4411049004c2c000c0c80040700c4150f01560599229890720560100320400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 631469964 1250 631468714 631468759
    0x8010501020d020c012609161e031e0c0f080705040912080a0e032d031b0702180c0c1606050a030e01020906121503070f050120120901080a0603020f1002030d090b06 72
    0x40c0920244035130b0400000340d03004210a0800b108bd284032052134000d64a6003011541e0b83d000400d02c3d020554140010b841c18030040b40140000c44080005000569403984800a000ca043c42400302402c0040d009030920380243c0d0b0203411000960390344880c040f451803102c03002808142d5044810b5004120481190300c1202c4c040c1c04448001e001408031030210580036440304500f207801c0300c03c02c403c0c00b01c5000d806025030f0007020304180396900c4506200d60709141c89103460780400700035002c020401c8142c0d00442100d491060511303001c120140300303e640602a10919911907040070700015030a0f205040042000e000c2e03140d900c1303140f070242c0c01e950800d903582e4030034080c9008452981e9000c10543d0b0240c1c0d0312140c2d5140442c900070080c00003140f90b5040c9078550015150350400014084015a072008410760300c60180c00c0108080d50a540106840f10311102c0c10a004c2c802030255031038094020815510140007001040c04010300d1441e2001e1128000d5400d80c0c042c224281c20102550312071a03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 631471214 1250 631469964 631469999
    0x6080a1713120f05062701060308220e0406090201121b0809010f060303120f021c110412110a12200103110301090c08010501020d020c01260916 63
    0x907101d028090511a420301e090300070600444003203101e00d2103a00001c1c018841548105d00206500012940000c01969000100d01c1d18800a03490031070144000392524040d51121255841520480c4110030280c98030b1160640165a0143c248802c0204024094001440652003a6941c0140000c850707611030654a000c007040041c8884a403504504911500c081d60b400008600003281c0350311103000c00c1b812030340d4541007a40096082051452004100c1c0900007030130100ca00b0840c600413151101c030500350b1100031000b07005508d03410442502c100910075a0060000b902121140f10042d141c000800200c0c942d44900440140c000040d0034a01d0b025805491500f0400590002840e414aa1000b6011000b120306242e526184204840c0d2000040c5020740a100c0c00015080001240034004500503030011381103500c002c8203145843d0b404a45d03958444006c1c240381c0303820044007601c45218440f40702d00d11106c203844401c00a82c094000390490b048aa5000e104414541b5021f26940403040c00703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 631472464 1250 631471214 631471237
    0x40314010506010f09030f080a05070605070815100801140a0e0106030507020115060503040201111c0c06060e0402010c06051b1c0f05060a052101111b0c1e040b0406080a17 75
    0x7c11052010804800050084c5055860f080785025856a241c0342150000c0d1003042c0014181820030040d160401c81801c2da40f1002c6520a40380310400c180107003400da050280e160a04d00c5540c240926484981c6c000c4041e150b041007d0300c8a40e12100c0c0140103182c02c0700d00340010b40c06c10340f2001401042205100c26549180d86640c5117075076a800555103a884400242c61a01c180300328091107040180110604240b1561449001c0c103040c1440020388090b50002200d03080c1d40014840143c1e081b02030000c00d80c0e44403402213103075516500960030002491011402032000050000b401d000c0344088111803291308075082211440002605040310401c4a01e503400c8442440f082c0410f00c0c1c012600016175110207044c1045500c180b01c50750965404542401c0c04003404102030400120a030640901545048014180100850005071100032494021a030700190011235080544858000e032440c0400604103001160f038504441c0d9540300c2060082ea41704403e0306c404101e8800c0e050484403400c005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 631473714 1250 631472464 631472483
    0x6170d030c1d030c1207140a060e09070507170a02150f0c07060605041103090d050a120506180702101104080a02090c0d090f060b0609180c040314010506010f0903 71
    0x44611000074039040100b00369141c403500c0c440030304640d10035188074000744040010744822031034280348008000300301003224400e03880e809052081c00e0b8444c5040000c0e40040300d0700c032900d0300c0e030b140181c84901c00d903580070341030440c03170000d0003583e035440001803411656540c00c5607014005160b012143e80c3d8151303440000c0902900c04100c4000701c0350003622a6502034200040c15607135803c002022580d6810381071511020100c20810000018095200c0c401c2103401d0031850f010310f018004004550f441030107a0401d40c0d48011030515155010700b00460710309201944240d040619020b940e5115515180c91507500b006031004507442404143c4045449400060181c480580d00300302040100901207080203c0601880095810600840c0d051038040d880024031024035040c007805035440440b0860150004006074002911103030003c0c5c803c00c4054142500c140c480c000d260300c0c2031140303034800f4184a4003a080b101c5c0404041d031000c0d0042c0703402d8886428007004400d081d100a10300c0d1101400c0302c01c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 631474820 1106 631473714 631473737
    0x5100f150203032205010e15243d020105010518040215040801020c0c040501080d050a0302030a2a0e060c0c0f0f0406170d030c 56
    0x980400940c50480001075035912025103842049045804501d000e086201c000113800ca5012000b44810300203018520303524242c11711801907540b03000b00803640f07017980252180b40000000581d12500c124180420a24003440020654442582840d6507031300204840c101940071592005084407540c40c440080c01c40d036050300158041c031a076410503c80302280c0500207500640c100c80008080001e40c0050185008540c0074401d950300125540320200c00c0451808400001070307408110300e0781d0f02c21100d07075901807005000011903020880b03c10610702c280c0045a00c00031f0120701080360428400010310100765028240c2c002200510070286041e070055001e8404142110801e0403e0320402103135484207094101c261281c3c1900c0c21030f10903500c5a1144220814004100304112a41c030540c000c007012084003a100b280c0a81c0e090240014020301c070f24420101d581d40d80c0c520040 = true := by decide +kernel

theorem cover : BRFrame.Cov 631294964 631474820 := by
  have h0 := BRFrame.cov_init 631294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 631294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 631294964 ≤ n) (h2 : n < 631474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
