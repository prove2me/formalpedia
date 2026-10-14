-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3408
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:34:49.349504+00:00
-- url     : https://prove2.me/submissions/0c47b3e5-fa8a-4a85-97ed-88ebfe6fca9f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 612769784 ≤ n < 612949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 612771034 1250 612769784 612769837
    0x60509010e0c070506091605180403050a2c0a061107030f0206070f0b040c0b0711061806130905150306181009050f1005220602040302100c0c1a0906 65
    0x2a00d00030084c1002034080c41c0c49800c47c07035240180a411003401031001202c50b0926100880c52036030b110303401d4030b40345443e031011320011940700340107070150a103950b80f007190031010040c00b0000b042c140008940c12845950740d6001652154241049500942c00901d01007000c986d4080e0101001480140b003c0c0c98421150380305500c2038881101503458400c1340702000100500b00e101d0034003030700c0c940200ca41401c0c480d0b80d80407942420340713901a001d40404555000c8502a889005102d610020451a00d9101002c5003948082a42c400e06103050704180216440305e200380082881200c001c0c010344000e41d64000080d455252074840d00c403092003540c1d00e00d9107440d20b41c49654030307451003140540301c3e00352481480c40c07a00c05200341400d20145030500f030291402135404407454007514941d0158801d00c0c1d07410890007d010315400690844120f94103861102c1d84420b020300e6a601ca000da55466940700c000110310300701c100c009006516030400030f8030054a0098041c1c55008824004990340381d413501d10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 612772284 1250 612771034 612771043
    0x30902060d0c110c060702190905072c0109090c0e06030c040302040b04140720011a10020d0e040906090c091407020c0904060c0e090c0a020d03060509010e0c0705 71
    0x84100740c46954401c081c1c481688241d0341410454120020181c1c04c0300800041d201e442000c40003449158030112248808200021640080c003440c4410007591400b148041d1900c001c4070050752201d03034410204580c0440702d403e05011018103950b01103a0302c1c00d0404041c02030003e180340f0f01c18071800e140149035a503100d100561003613001c5851207031180c2c954814802502c0542c0751080c401d42c140300c00820f9180202c2180b0754040002c0c9001601000c100c00503a10602101654002c55402c08c100c440002c0f450065000c625041a100030380800b11414080382c4444140071070500240480440547d5442c2507000640030700c1c02581c002500d040103603100f10000e2400c0d44031611041e1641812010302614100d1a0f81c45200c2c2e0000e0082401640e0002e000380c4e000910003071080703584603000036149100302c0e0aa10b44550240200c18541000120140140c110f0004000103100340e4a985580f14440d0150b6411144007600c00091381e42071600f4075508a5008010403005c2a0a00c80030020580400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 612773534 1250 612772284 612772297
    0x816020c13020a030617030910110f0703030e1e04020306030114010801050708011a03220f05062d0613090506010f03051501050609101e03061d01060c0f0303090206 72
    0x7500160b03030701a000b2029058962907404400c0304002480d4078451490040200c2e00030081c01c6a400f50702c128800000c0c0c1d4440c1d84003c2e0084a445649640390005c1d03c000365510550380030381c0322039801840705000c100c1d000580001078902c4000401c00042541081c1d0090741d04064001c0c004505000c06001c01c0d125040241d000c6861030303440c0c905000c000742d0008140c60141000c011172040540d401e001c004810300c00540000000d100c1c1d004020300c6d03400305469240340c413036201250030304500036400c00c9940e4080070345000400050014030302c64004810765040c84c0d0104001c00c03078411503030b034401003040703a48003a1082496203442e04044000500c1c01d00505003e00103403002056210b0a5080030b5180180b0f0700c7c000f41044174418014000d5903102401d0f541050811201b80e0080090042c0449640306036480058000c484803141c3c007030840d010340114090360311040040c5d00200403c3c41140c107a031400c2c0f050b100804c074000c019001040d0084034101071540642004511680d0550124242e5032160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 612774784 1250 612773534 612773569
    0x203071205071404090210050708120406140a0608120304020301061d010f05030307021e0333090a081603090e0c0403120801031e021f09030308160816020c 68
    0x4080c00e008195036401040f62952080e00e0030440340e002d0390301295144070041d002c0c505100340400c10604000c2c55038100c44081910038030745501803c1614000d0042c2c00e0b8100410514641600061494003641c492541142c1c02d0100508170f14900c80c1c03024015900150040c0e0f00341d5200d04000c0ba5202c1040d50310b00c070010030210741500f03d601d1f020203c0015049a04514801c3d0410000800566250f61107070000d18010030000401c0721a850020745450810107010061000000b1600c1e81d800700140c50a00f080e03505900d0f8022651000c0900d07484841081e00280103d0041c403060314041c02060001c0d6500b440780c20104801a261182c80711805070855040921a134002014000c1000203030400800c1d1449040c4a015941140d82c0c0c05091004c1c0e228840300580d0317922100b010f541c1c800074107108124840c403640070303609040100142510b407240815004680d204000c00e040d0b10280409038200c1c41103136103600c038a440380390600c144811110300320401c41c42007901c03c01281d903c21815400c001c0c0c85 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 612776034 1250 612774784 612774793
    0x1002030708100b041d1510050913020c0604060207020d0f05100c0201020a091703160809040e06070c06020310030b0a05011a0f070602161b1415070303090203071205 72
    0x110309810414006410080f038001003030000300042003c01040e5001c000150180c088140c1e140e0615514811405800d650710882e40c044d400700e443c0c0c0050050154000544154410645001051082e841140708035680c0381c0c401000107010421541c0508001880200b444840f160580c482c028217100d043c0302904e15412128464000280500c02d00c060000b03d80001d5062002d10f8a02030004141c078030039029002200103407010150400d1003142c00c010b400a44000c1d040b109411f040c0c1c0c042d0841c90302240a84d28000c100441000002021407040d1915500d0f07280d404c40560700d44000c0e401c0070300500c080104120000c40052504042240301e04168040041d4070362405a200042010112583c072103082c2c100000f03400c1c24050340441701816040b00d005607a440203035411894040d803000b0040d00e216041d904034440c403414014030b90115842070600c070742580d0703d0504101c01f0b10b003046d00b000c184440811200c0c2c0024080e0700504160b500060542d8445652440c042c1041855a542210b07260030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 612777284 1250 612776034 612776041
    0x504020724050a1415010c06021c15050a12030e0d060c121b020c1210050705070c050102070f05090612010f0905061008071802360f06040b0a021002030708 68
    0x183d80700390510000300020f88502820300b0703000e203160707100640c52290402100d04c0950b003d11400d0f40480b20304044042c10b0400000f2a0301800c00107002d00050b00d20f20142d404000119860141d040400307a481c610035450042e5015030b17050350129003600d00140c0042d8072514400104409100c1c0319028002e81d1501c64047c0024101042121b0401c2141e4801c840c1c0a40c08940c01da0380011040d02c0340e8000d4640e030540810f481d1181b440c0006402c6c071030318918101b4082058065211004d807900ca441a240c0340c0311291101c00580c0c03940c50b54024421784150b1020200f14a1500000d40c0350411005820520320020038603c990130b4070066160b54060b9500c40f101a0700f008001c10156602c0005800c001c28642d0411021340e0703e40c0854418148400154400b4801007540c035811540d080c8000d03038040c0b172a44040841403580b07202440e84403407142c64910b89010700d030800c00408050620001c0a0614050801c05c00e10441c1d0850103c2c1421807048501980c0c22105501c0118026902a15014500d2a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 612778534 1250 612777284 612777301
    0x110c07030311061b1804022a070b04210f05160f0b09010c3e030c1003050403090b040f0e06010315050603090c1909270609081204121d0a050402072405 66
    0x1448c6841c50400c3d9003c2001013000c100c4000075902030b03072554858511030481c10030b6400100440814041d004002214504041141c005031901d000da0780b80c0f85030440ba0341e50f80c1c1415006407140c499409900d00410803690719601c100315004101b4410f40340d400039081c68404e45420b440e081b80d00c0c03c003404e143e41c400c03e1001030524910541e0203411002090380d0030340d0b0004074401c4000d0220b0303070381450b4950000c20100f6015400020140280c40700702501d0f540c0da00c145003081280d921a09000c100044003003a5554424060300c0b1200c1c2e2120003030310300d440c80d003810300c01c21b54001440c0754041d005040b00d401c41d0b5a605a50f01103008115040b20a100341060b00000482d00c180d2505100035071900400710017000960b40d0041d06d07503040b810008120170700e4100750106100720340d51405508226000c2004100000d0b241c1a40e401035a80c0b4409140b0641d002d00401002001001c0c0c2c5c0f00e00c42980130403003440e01d90004c010041c410300003815a4080c28004042c10b0414602d580b1942d07440300d04029a44 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 612779784 1250 612778534 612778597
    0x20a050c060a0509040e120c06160804080714100e011a010302071a070306090c0c060605010906051e0d090c0810091101030c0201110c07030311061b180402 68
    0x60304101c603202c0c60040d0354440500b051158142d1180102d4441103c029502402d00280d611b41030703800c0000d503490003026444da88841003181d04046001a00384642c8000d071045481c9445141d10402e80b5260003520f0700c511078007507036021024020b4860066000e001d01820b024102c91081c081002145001e808202e02c404a070720490340d12704040c414424800440c419040d0300c00f120070030003403140a58540101c100e019040e80c1e00841015030400e041e8003515507201c000343c3c40e0f203800f850042181544610044450454602c141000a0802d00a000020710340010481007081050b00b882c0c0750071a0a603002c003d9911801007543d429003602c4007006034007424402801c40801c405820418401540d49000c1d4000405080c14100341c0d45544c1003105600035408080d121040d085642e48440784800f559031ba4600038041100021501d04607213207a003400003080c41c081c100310148083d0702d950080c54003190340c0003180880c40c24840d100b0758007221b894038401042143c0f01c00403c0c610900007403941e070900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 612781034 1250 612779784 612779803
    0xb0d0504052a1e0f01050703032403050c03010507080606090d020d061e050108100e1006030507060e0909030306150403080d050a06120b010b0f07050304080c0f18010e13060c020a05 79
    0x400703c030308200f0f40d05a030313652540e01c100d0102402e0403911117210741006c400900d019590b060030101d0500c005103005d401f07004c0050450b84160115024001d80d10145403d8520a0369240041081600803d2561410201401a2010292541c181001141c00003880302d030b03ca020688605c0c0ea80c400340103181c040080414815605e42405120300d5150410107a43c3d0641c08004c550380640e1000210100c001c28010300017400100c110a0004d03a4403030030a251501c015108a501044aa42e1501064100340c02c16a2055080300061821591601d09000d0302011540036068036034402c11001c00010310301030140c5042c1d180c04074000340600d0250946000ca40c0c0300e07046400e45102070440b100c001034802700c4c01c40c10b44520900098485c3c1000c1c49a03a0301d8014180c00070040d0002040110341001c1c006840c01c154101241c81006044000e0144400d4480001820000c10418001404500d66122000303410003038041c40304004406a8a6200488942c0380003440160440d05803001032100400c10140c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 612782284 1250 612781034 612781069
    0x21e03040c050d1e0c080616120603020105090409030509030a1103210711042018090906070c02030a0f110a230405040807080406120e03040b0d0504052a 67
    0x83c0d030980340c0741c2ca01000910200e001c50103c1d0140020100258009220000c0c00410100d90b41802d00c0e03800410312230030902d4804005001183e00007901301070350042d0001c803501038440524003003401c0240320141c02d00c0341c8168140081040864440e403800c0200c004224000c05102000c02011420582081c03401c400c00710b007035400751212814140a280880e03401395031010100d1140c1c80140049000fa01035940800701c00c0d64068041c1d4000c80c00c1000034600030b49694422440d002188040140e18801a25002c449900840008d00c900d4040c0241800301400201200c1c80ca003039a51360417101c441d902a080707030749510400884070316003441482c010107480d082803084084c140652038881080c1d445501c4501c41c80e00d0350081001e0052160456100a03041200035035110348841028155105610f04c07014664a80b2040310b0540c200030040d034040e100d0121017549800717440b071117001c090711016100351101c0c02441c140140c01e0004444022040900085e03a01c1c0c0d440e0319404201c0360f18519241030300c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 612783534 1250 612782284 612782299
    0x4030b0601030c05121003050709020c060f07021f150b0a081e150f0a0608060114070c090b060c0f0f0c01081006050715051906060c1a0a021e03040c05 66
    0x1581e2039048000d440c40c5d00c0c00540000320664070040403000d41071007544040c1180c044e260000c5609a4503400800428140740c0440e4115103031010070044400c0e08881c4200140c0000c01400f01c1003d400c40d045819006911011440c43c1c10031800d030010955551004081c000001351aa2641e038000e0b00256000558243e001103546060305601d00e29038004041046c03581640e00e46891303603a40e88000f503600000282c440540c00d80c40b0300e009041d044003620014003044003d05106072120403841280d000a6109400d0440d451420035188098422104200e40c40365003807000b14200b48041081c9000300942c88010500a40b925075441d00342468510458100401503040040c02d040c24034100e82226076a00d8021381d43c041c10705064550380410000c00c49050f0404092046c4801c014403008649801a24200806581c8540907540d02c5510840200350840038260318140305c05680000340c0c4041d94030000b520b410000618000914100d000200310224044144024080700c6881140500340036141d14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 612784784 1250 612783534 612783551
    0x4030b010602031615060e04060e0c06130608070c0212010b130603110618030307050d14190f0504090908030109150e010308030406061a0a121503060b030a0b0c04030b060103 76
    0x3845130510743d000240a5502d0401500ca50111680c8101c006010020780b0b045107080910b0b051015140640503092036118071003a07503e11f0714086080700d90100c0d00e81d0034502c4082c5825016644690020640070038880000402c801503101c007480d03462240b20b40c10001840d100f2000070000400c0c40741ea01c0c0040a8500320080c4000703803075445400041a03084580985450003020300800d03211080813895050b010204106040203000503204c0b055032500d880e040d241507400358846100b802480c65084421103907031000401503004041c10003040c507071850114502500d40199009880514400b11411040000100042d052502c0b5070310101040030400c00185e0701c0c1100b20150603034103020140140c800040803a040200c01d0703000c40010010031200a44815100c0c1e0242c0c0c80e0f402880f82840490070703491400700032010901c00c3e110484003401c45500941d0858884900401c0b10402480d01441205001d001241da50700c56144180d1010210310f81da241140b410b40eaa011020b01070354103040c02c02825 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 612786034 1250 612784784 612784807
    0x7030201050a061a161a040b010e060127080619060801140f1e0403030b0907092601020c0f070812040b03041403210603070602060f0f04080d1104030b01060203 70
    0x80700d84100515200e6128407041110060181c1520801006e604440c4a02040941142001c0b071081380201000007503a0385e68480303600e0035442100c0e03060000701c0d0920354624584800c43c89a0b0024540c1506d00241601e518030b42d482c0c840e003514039040c03c000502c11444080501c0c00351501404000000303209240d80155001a2040c1c003411140703403480700d03600083c014141e00003000042d110784000c00059042c5070030040d0040070400e21045c01a900800003912860207071581404840480d8050610b400c8240c01401990001103210107065400f001498443c1d00e017040504030300035481c001791541514004006240c0441c030101006552424013082058000150540b40c1c02500300b0041301d1a004013058050651107a800385103038805803100c0c6046178428480d0160302c03c0e5810303400c6400c01529100c05a0b034918080b200e01e42581c40d035030700003481e40345503030211500070b80700304078190a110114510710107440200300140c0c07241c40b022808109000d046058103004002c2400510b241c41403080d41c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 612787284 1250 612786034 612786059
    0x20309100e03030706111206010c0512031801020c070e100b1e0417010506040501091103060f0a0f150207060503010503210426010608010e0d0c030e0d0807030201050a06 74
    0x28100c0520030001089121a1014812140d101c2c0d445031080014100002036500c0c00e40010520100344400703140052503e50040300130384a0300e034001c00288510301a0380900e880315030006210800c80d5031120400c61480100340054030302c62826101400c1d88604264403240140401808048061040d1804000c40d1300048111200c070300c021403050000445d0742034607107503610896015180300d8098000f4100c0c0310340c040d40301e64003480d000c0301c0074031060740e0381c6e4644415681500041020083c0c1000031500704c2c034000a8652801c2d0005d08180c4007995280074502403086954840500c9402c601155603c03940d050250f030003e07004034140b050031941003030040ba544a0a060070100d0444440d00344602e1050300005031001801508452400c808407880ca07076404402e06c141c8924298200000865a80c0301801001c40b040b684800a101403081204100c039603212042c0c054081c000c1c0080c0000075515101d01044080b4043c8000c1644c44c100b03807074000e00b1224001c12a8800d5880e20382c090240351030380300c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 612788534 1250 612787284 612787309
    0x50c09010f1103071208070e01021b01031a040e100c0c0f0224030705090102162d03020301140402010e0d030e04020c1005040f1202060105090109091e030305010f06020309 75
    0x1e0b207500740b00031540c0054618481c014000c0c00700b0440c110726040240d032101c1ca1910460303036680c4109040c8186401a40d80e20041d1070b00b80708007010003281c202154820360151600203059130340d4038501803494004c1801c580d1403011540e140e80021100070b00c0c089441c0200710440b042860420b40710741550300d85444901222400a1247d01c45110205401151100b002510b622136641c1c1170b503d04207840054034603408140c403580507008130003005a4141030703819000c003220903c0d44907410441c1030401c03a0642914101c08140030038046000400913072401d1103004040c9d95188550303a26802c040c000540410305410825109040121000c0300180e4014215880100709a50141c0c841d5560521a400e003460140065aa11300c0c2404003c14000b885440c4200c1c1401b9840c502c0031414641822a12414240602c43c1c200c20120010084049654092179500d8041c038640c0030f0b0225510951000705e0481c5400360300081c0c50301c005001050364200410010301481c0029440c004060b40400d06540040c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 612789784 1250 612788534 612788537
    0x6030607030504060e06071e03050f070c030215010b030103140a030e04150305121b030c0615041e0f0515090a090c0506030901061802161104110d0b0301050c09010f 72
    0x70b1000c40c1c10080c06400c00344e01c11442c00141c4000f45488203004061404030307401024004107407400e0081841c020312404c3e0041020942007031095990120a4880715603081c400c40c110311464030b08410026803202d40324040d06412121039540d51541c20f09109403107580c2d010000c150015043c94000a4102e10060180f400949011604050014890006481907880a071513400b1b0506c141420500c8440200a00d007016140084070003d08881540d80c0d001e05202e6403541e9020300045412254029007522400d1401840403440445045003100150366405620b50f00d00c3e2550240406000c4600030140c5c806990301c0300003901e400480004172600d80c06000c0c0c1c640b29903101fa10100340000c1100b501e010304000f4124590700e0030b121410600034500d51160010010f800d41c2c1c0910b0650b507500840300995800c11105400c12020f480e50010208a84441079005580d607402c0d440c4c000c4444040e11241040f8240000e641842c1028582503440c02001c0d9042c80c0c000f000f840450741e03048030005104d074116 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 612791034 1250 612789784 612789791
    0x90a15020d320f07050718060e010b22080606130506010906050d06080109150606080c030705130e0c0a02160f180f0906020304050c0a060504270c0e01020d080603060703 74
    0x2c0085a01d15100f03120080700f008100051440074032100051101c2141d002e4054003e4101c0c7c010103401c102c5520780214846410810f0041011542e001d01900344180918142c0c1120781c440c0703071090b01800b015808040150460020403641e45003400d114043c00c40401024019032034400c0000700358403294044c000c14400c0c04502e00c0c0307802c0d805034820b00c050141c0744000c204154050806500100c00882d40010141c1003e401145592151060a0080981c8038140e070440e200c9c2101a10513800803d80841415210321002035000c190300009402904407010590355403100c407100034100440f100c0d40c407803004034201c020840a410b00d54010101ca0034030740c0c0c40110103010480030001d04102e01140e030340d1504181800061040360f0340114000d5125404855807101004144101c178100e41c0700d2840450824002007060202041c4c0d9040c24420140d00c4150500d06032100f10101c03203504660307100103a01a1211301882d40c04003e800c50030212070502c1d4081d8940000025a01c0000410580403d40c9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 612792284 1250 612791034 612791117
    0x4061406030d2115060801170d0206130201020a17220803070f020111030703030f050f0402150a11120c0609030f07060b060d0f0b010906050a02060604050606090a15020d 74
    0x10240d000c095041801075007030301120340e9605e00900c540000e0107190302894000d450001c110700009400c0d08400c0341c0782c01078841075880e0101100805060301d401d906500440c0b0b2903000055100c0c400a2102440c00002500c035030b46d502908282c450560744559856541310001d11500000000340e5402a030302034101c4030500400d01c0120350711316204800c3c2e0420f06c80443c0b203504058048c1c1003600d8134070400780200215038810000c0c4001c00001e07a0040d400003980c030801c0ca02c1d210200c00410f429265810580340107081c01c0300c8186004007413202c0740120503010454010f03071030303041c0401030b002060100214142626540040010700c00c0c3c800080c14155540c0e10402161114419640281c6002c2c404000d001402500c0303001801c00c8650f018005006138a010031200d00442c1030b68520581075004220643e12801400010280540700d16400315045c01441816607440342210003400740003082800b00010014080c0c50480304020768403d1101c141c45102c0700710171852800389034403a0450141c00802 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 612793534 1250 612792284 612792347
    0x12030c020a11180109051b18120309030d0203120a06031703070905040204090b090f1314010b1c030f0804120e04060b0a0c11041505150f0304061406030d 67
    0x325401c03040c0300c00481c0300f4000036100045522203485101c1d44001c06c41c10035020300410340240f2681c02400d45501d103608803078229052484802110000c610201c0703240c442241300082c5044080c91047c80141c1c400140c019222542ca5100c1b5040703040340b58140042815680e59000f0310082c1e0018441e003070000303c000382c0310314030504428004200145c401c654580c2c40d650b07884050150449020300a0320704002050522011024072845a0500105c100004815968102c94030440700f5481025640ba500c0d103540c55501d0004058261a03a158589150115450064050145e921070501440007030020400400d10890603400720b1807207403415060384900000001e00070281900594400074020640c5130303810b41c121780007484190240104000300443c05040109031000d000300789180340d0142ea4100242d041c08000080784083d401c1605003002112510015150012501601c2c07882d2500d030407545118241201a40114080c0c0281500c8820b00b14041d101c9281c000302204044e0000104a1040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 612794784 1250 612793534 612793549
    0xc1e0406122126180d02030a050702061903050105100e06120901090b0c0307020c0a050a05010804020303160b1005010314011e0f14010f0203070512070f0b04030c12030c020a11 77
    0x75400c03446110702200d841d0254000310204490700711001300044c00c0142240000100707100091800c0d4011854009108001c9629420000c006ca820140034803055070058615000600c54158584d40081c1c1e030b40c905420418043e619504640a0007500502003070641c6410088901b9030741401c100d0302c1e8030780703500420a00504440c50098102a02441401074a45e0204020b60184c5001c0d821074010800003c00c01408421920502d0780c044120a410000d950151014503817060000f0f0941e8108500380500c202620072641d4100e80d000403100400500c481c4401c603c40140c00280303410400c40040d22441b00c2c2c0700c00e040c05124216200c0c80c0000c2040c080181e01d180c0541244000c4a4440d0b5079103540c8002c62594002c1107010511105800c9001c92001098920284d0468002e24684402c0c00303080c880c07a48984400d48060055003110404035000307810301070142c0c0c825601e1605400d854102409180c8031030b41420b08041c00d100400340075030b9000030001c0c005900701140d03000d04c41d4181c001a504 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 612796034 1250 612794784 612794807
    0x7020f0303030a09140c03071211120a03120c0e120106090c050702042403080a050417030a08220b2d07090e010b1207020c1e04061221 59
    0x6100000c10000910104e410024010388174044d440f208090b2a03e0440d00c400f99601e0f641d030103a005960800681c1205240c4200c060f01034450401c8003020320020031400c80700040118040e5000c0c2d0b5181c0c0402d940200c260020107158031b820811624544001040c00a05d5010103110f80c0001805400948081d4003c1008280c0d1038010443d038009601c000d40160032060b41688a223107445054001101e1600011040300909910710700080d0030359440c41d400f03420180740201085802d02011a00c051402421140c18103840004d5868080c4460001c102d0840100301d070410261090114040b011040104201154808480041595481ca107060703840101000a111507444440741c44000c28600ca200b400307002503640b4070f4151603c0d8400d04404510030b00c1980300302107040120035105515111400d8001d4102c1c81a42c0400e44000d0005601c0c410102c0c016001d007508070502034440c50304e44100e100801e0000010f481040d4030343c40f11402c480e068880c00284600301058000c0d218460080c5e0181d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 612797284 1250 612796034 612796039
    0x203090d14010b090a1d030301050d0b04110315091905031b0309090f07120513030c080c010603060b0a05030c10030209010908030a1d030a02090105010e0307170102030a0b2407020f 79
    0x401d440d00e0407401015003094403030054049806c1030b00b07102603100802281e0507107001078588200c1010603500d10b00d03400030040c4150790740020300c80000b44076501071041c50000061900b801c1e4842c01e15002007030828500030488020222448500d900140307011040e20700210b041c80341400030b07100401c1464118403070115030552041c94003041250030607009040300c0c000c106907503800b0400101c030b0000300200c401c1034802c80345005c0303c1e1000a002901c9403246000480c404d180c3c0c5c3d828201620722180c2560400d030011188151203140d60405410100f40500003041c00b1401003180b40d4404000ca0088030b003a1241400701234000644140c41c0e4003802031040182030190849075240903411300100381d1600b5448002c01c01c1401080c003840d501d8002440811250010030052159103800010b4480138400c20250f5018028040001040300d040100c2000800810001580c0d91408408680c00c6130703400c22400d48625800080f14402100c45012080c0150040d002c0b683c0c3d41550303000007011250b14501469 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 612798534 1250 612797284 612797299
    0x50a06050d06020403050d02060709122406030302062a1303020d05060a2d051906080a0b0702010c1d0301090204060305010f050c09060901030b0f030a05030a0f0203090d14010b 77
    0x1d04000c2564014421603002e4000d541818100300c5040762074000030350709800012041d8400384180c40500e0600800c0c9031260000c0d46c1840303124140b06504d03044103411200005e5440d0404c009154060000c01d60000c00b0405484041d0150649440038210303041105002000100368100b014039510038000185400800842c1c40c03400502c0d01d42e0756118102e40d0640818140301c850000c0880540c03030325031409501400c0d0403090084080701c60040500a0005d28500e44503200d0740c0000d2224400d86001e09140805002a03801c50f051034150b60002030000c504682c541141003280f154483d1441511170203414425001075007407000640035004154000e50301518105002040240541c0300d9940c00f140001d090180355650700141c3c6450107142c0d5190b400060400603c40190b12a40c4040c1e202c06008018000e15031681011900d44020403900321496400002c00880282d000042071031003041601c001c1d032404a6000c007148107070007039540042411000f0118042202000e40000c039aa890141501 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 612799784 1250 612798534 612798559
    0x190b280602070905130f060603170408150f01170c03031b0d0c0302070501200601090501030302060f100b0901110f0606041a030c01231c050127050a0605 67
    0x1504469600c10003000d031042075800545041c250003118400d03103035140f01d20144000364a0305003140c1c0740f80004070388056440401100051040d02602901c60146030415156820f00703050034074103d540706681c440c107203280f810044403000105015040d544182094075400e000d81e020103240c182e000e204140e0600021550800213800902605c0790242c000d004c460400580c407006540740380712000c018005811011060005c1c2d40a09040707800e11017800c441c180041000d1448504142c8280c021001c2640c807000100285a81000321640100422141c01e0203420840e4a440f003900041c03190300e0695002241c4050a45c1c000c86184c2c8090402d02c0964288040060100d5102c00d01284d50501c201c3c609003a000012003480d045000000010b00100304040c480001955181c804550741c1c0813008119011340c40c0142c0c040050482d0b0f01183c50700c5611244120f10790f00076100d05070002072004490350401c0c0620302d0003812801e03500c040d4180001e0951503c480f07050181c441900100d41000084116 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 612801034 1250 612799784 612799849
    0x6090204030213090227071707020a03051c06080a0b010e090604170d05070309020a06020313050402130308070507060314060306040219080f06180d0c030e0103020928080105190b 78
    0x3140e00c520200e2340e90101c80220031001e1103904105848134401a031103d108900040d0283c0010003c00342e40494040c00100c1d0700281109580b4913410000740c41d0085c100c2c2030b04004035507200314050007030803042c03030030514200900980e2014000d001900510160720b10200c000410421a01d924100220038003142c0f0705680d000d03014151001c8120b02400c2c04990010b2103c2c8003000351419180500082c48125190804000103500070480c1843c100c03802c034600000040b909801000300350b10810260080d149054009011260b010510686414140041140a65000c1040740d0301070b0741190340d44104021118501d0280800d9040740c4c00520594810400c0da4a0020742c2600c070314035400d5000910b0103003594541e111401c0c1d002a2001c00c11b0340e0508800a401424102d0842506150041c06c148049001900c40c10403e240340e01200c0000180759000881c00d40d40740081c090f140d00920440c1800214000c40011400c0500c654595030344403072100e1f948181c14101040c00c004400c41044031210038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 612802284 1250 612801034 612801109
    0x130201170403171f0b1309150f06020607020c01090b0901030203191109030606030106050d0b040f060c0e01030b0102010c05041a07060903080f0f0f010e0901150b0d060902040302130902 81
    0x103d59802e68000e800042c4440d085001c1b034003101c00b0690315081d814507180044000c0c00382d10681140d030801c240808103034400120800001480036900600541c01c201001905041c0d2026425041018030719092010031003900444140c0c10302880c0050392603550041805000d11344102c106103603424011080000131004010300402c00c41141a160603840ea04201400c850091042c1e54014202001400100e2112a03540347d010b40900c03400d02c49400983e42c0c40301201d00303200d40100440d030140e00f441001c1d40d16201d404c1503540b0130b0000b08808041480041c20394080c600c0f454803140041040c0c80a50b041c208150382d03600794000000d1080d1506454007904003207080720704250f41c000440001f10500390010003d4000c200d403101e40200c41e400c082d170446100f100100b40b2032507592599130510048815040400080100741c0c021504c404a1040600640da010303804112420700511092001d0b80d1421013640401b030003528000707004201d91010404040c00300c80002d10b0701400c071030b021521405248 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 612803534 1250 612802284 612802321
    0xf20030c01060b0309070f03020d0f141014060102240613090602040603050c040b180111060414060c1c0903140a0801080106060c110103090212100f0513020117040317 73
    0x400d641b02951034422560300c1e1686480065401b00390403804030042511a41d065008a00514003e400c0ea2408400340d40b03040040e803040300c0c40d16030310484185002411019160440400d00c0034003001c00c1500c10345003845481041c00d9100202100c0890780c243c3d10206404001d224241d400c1c070020606007413820082d0000c0c455200440d08000024142c050100c04843c29214111580c1381007043c06d1198042059241509605000c0703503002e09840800100041840f0b42d00c0f880d036040e0420341c8100c803a400c008010b811810390910500c0600034105800c0340340d516116800e0341c002041c0c040c504045962034018a03160309000400196001c400303611001d2a0b043e0b840040082c4891703580d804d81142c403440c0016018007c2c1541f850141c1d802c4d84260440240a400102420141003441444905018440a04080b5541d4401240c60414490b000700d40c0e00030a0070b0411410583c0c80c0d0000307052103c040290306401c140e5140010101030154180c41800444123080004030300d0b014090302040762102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 612804784 1250 612803534 612803551
    0x1609050603011d030a0f03110c010506150c0c06090a15020a110f0a0905040c0b0a270602060105090c04080313140301290406050303030c13060f20030c01060b03 70
    0x15881c400d56103441032194030043e1000b00640c5014442c0004960340411500b802d003c158440b98540d100f403040801600640c144100002010b0920400300800f03007004811404000500748412000941c0c049407465910900761403050791240c011001500c06541d503040760b0808070220b142d040760a0341c0020032440e1144101401c02c40c1401c82010000081c1c4015002e075484583c48000344142c0441d9003246410520440d441c4240326194900c89031035800412800d40041c6011607c8100559034490784240d2668080b8203880150520308000d460f402d05026582c01001c043c0c0220b03414801aa040b40c0041220700300340ea4465544c00800380854400744101c04071040342010000551806101786e03500300e4001c3c03c414402c15030304048002e82075a00a006541719542d01c45c0050541c0f0207100952041c0b0701150451ba840d0841c6e0798807070b60500c064201070104884100c049071002e0300442540f607a2840340140982c0d40010110316441c2d80320b4ae9941803825420800000b907400b45060145014440f071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 612806034 1250 612804784 612804791
    0x20c06130210020a0c090c020a02030106090c0e040b060702190321090e1504240f050414010317070f0f050610060e130507090f080c130c050a11160905060301 69
    0x81202c100d03960341d03038160081c0070024820400c0040c011554499000c0d40c1a03801540c0864030150006405c4600c580c1c07221080c01d0312610100ca400f44d00500140d049402200e013009230304403180118286001d0800000c0c0507011000b82c4035150b1764807840500003194410b40c481120807203441d4204615a910b0381e2040400d1003500041400c0b50903100c010700c18500214268450942401040054028a034048101d90251182043c1c0043c1d101c03101e1003e0304804101c540c9441c50301090104a882d407142c0803002c02c459000600001da440800c1c0c00141140201050f11341c002807c00110924500000904403110607101408101e80481d10600c03c002112140346002ea8450043d0b43d0162600318441c4e000140340d0960240c8611035101d903410100c02d10308918450781344c0e00c0c256100721064200d4a85039100305c0300241103140c00c10f00c108400030030388424800c3c0d648003207002d04180210601401400b512001070b100341d510412080070b5200c50607401d104800e640b0310341440205416214203001e03508 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 612807284 1250 612806034 612806059
    0x20a0305060a060806012d08010314010204230f06071a010e01080304054006090b1503040311190b090d02030301171207150f0e03040605070204020c061302 68
    0x3008400e510807150f05803281c1020750340b4040115094000512040301d200600c010703017040b02c0c41141d004035007803581e9101c04045504501303010184a05003400c6d1881c980c0104400e2165140b0540311445201480166210344c14800f0300240040d541c0c000850f41144000c1091428402e810150340e581c040b0030b50802c29a80d89034000d032020703610309001c2e1000c0c540c0100010056400c15001c1000000c0a50100e812074140c000080c0c3c10003002c000d840106505041068250100d042c03244000604c0c0400d4100200d450310700c0070038146a54807441d80a00c00000c000502450f000f00b401c009510180c000362808284120005610200c4490003601c4500f008400903039080800500040c1d940c045030010340c1140c0c42c3c031101c600d0380307920700142d21754a00544002c02a60200c40c805030504500c1030703805120310001d200c40041111320703c011150300e884c102100401c901c20080220f5059405600d0900c0e036840050004c28064821420740c1a010310890042241000c0c43e028107002241c400c42d003240c240d24 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 612808534 1250 612807284 612807289
    0x60b161a011415070507172401060e01111204090c0c08030c25061e0510090f1d060405010606050304052812080105030c060a021203040f020d06020a030506 68
    0x21000d001d4040406034045141c0c10b545024100340b0400c4050590301460301c3e403995521403c0481c9507019007580c4140d262118031f80042800180d41c2d4130b0a04411034941e268080b42c10008610610800e405e02901100104c61644104851003a400d041011070341d100020007184c11300d6900a00c644003c062801c0d51000d041480707107240319400f0390014420350840d1214068000564401041c0000d090700c6003684050500060100c502e140c0c2c004c4000055800d1140c003503d12081000c0340d4110244e151800700000940d901d241c20094030128100007807500440c8940c3c100901c18402107403a0000c002c9441002600005a21480395116400a2241075541c410540d207901090750010241c0e004400282c028038910700c0c80a000010003404207140c06080c0e00c81299480d2080c0c0d00d0000620b0300c0d40140481d040c10081a0540341041ea08540b40c100d0840c0000d443d1520301110f040c06940000114080c010004843d00c0015002000b800030700405141610096020301144e80c0442c2c109000a0400d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 612809784 1250 612808534 612808583
    0x20c1c120606020a020603060406080f03091c02031c050f0c011a0901180207061814010c0504081203060a081507080609040f0312150603060521030f030a060b16 70
    0x3191150000c2082130f140d9800c000c1c96410040489030490307500c000020740da9000f000000c88000004c4c0c00f661f5910f50384030901c80c40300d4500d41c00404440c100e00c1c01e40300580740094041c485801160030b420303606003109803c481520448003410000317213000c40c03501c80f44072040d440440c0c015488a40d04d050044c80c030f802e01804410904c2421401980c2501d00f0340c86c1151500184545841510001030400039142d0b81441c016540038261080002002041000c0000f4450712000c080f960070118146450316110580e240c6065000014070b08000c800b0510680712105510068880c030307400d0311001b80f03084140b142c518070304a0f004800500e010003c60041c0c1841d12515010b00d410404e0104100425201aa82082c0718052000456565031020050b640c1441b47d0001070310540d40c001c10091301d800100309900b040140326038002001c204800e4a00c42c0000119500000906940da40307070344e10b42189200070881680100d44281001030f03030000e5840c181e00e54015a07841400c8608107002e44c400c042e00304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 612811034 1250 612809784 612809789
    0xf08100b0318070302060706020319060305120703020c100c0b01062a030e0d0b09100b0a06030b0d1403120705091815031c17040b04030e04020c1c1206 66
    0x4903608201080c094040400c41c00c0300b0900351411205600c1d0380c0c0e8040341c01540320f810103848481c3e010043c0600645814154023045003d00ea05100107401c507201d2a4540071160001c2e800d402c0002454403c01d4028850408800d9006201000241d0b022030b0142256081120481e407003900400081500c40c011940c03151004110007000c030b100480313030030900322101218a040c1d00307200d001018224280d0700d61051f099180d110301e034090b10f0341c1030a1100520700020304911241d104d0400004100d161140a145000c480e035920300811f0030b2007802c001c02e4411441c0740d40904404d0050150941100c0d0010040c1958281500e41c030403141e640440c00c950501420745580d901464084409120710b40800c1c2ca50f4100101d0400d0220340218840002e2a0000d00c40484000000c000601120300c1c2d00a0041c180c078055181c5030f4161881d1682e14050583c1009100409102c00d6181020640d01c560b070545136135102010031180c10088820b541c5441009034502400007070524170403a52086680d000705000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 612812284 1250 612811034 612811049
    0x1905030901030c050c01020a03061403071809030512040605090705150304121214010509100e0f0a150e04050f0d14031312180807031106030a0b0a060f0810 68
    0xa000e500d8004402915030800302c4804c00c0340610206118010070f100403e10b070001601d000591501e40b2001d003c10004281d6100d00c1794001100030021b51241200001303c2c0c824400001800703e105150691b040e0140c02d4103607aa51400104110030040143d00041c084d1808070101c403805603880d4104143c000316448446024041400460001007605840203c102d245041001508041d084001c00b03c5800040c010901820000100003600b4181107003504800d2000c07242401600300100c0c01901c08010f00240310050320140050400c0103140e0120305d81540c07050303001038415a40e01c00004c14201c150303015036180c00340d40311a00480030002140c01c0d010310182c4440d60703054004c0c154020b10703404c01002e0118a40d604414000060021107042207906000d4407040c21492040b14400400020f503009103040c1d0780711340b0051000c00e883c0d01014400d40b0045514941ea680c1c1c18411f103004e041c1e00414980c201d5803010020500e5074000d01d1907905060750742d030303003c0c401d5640605590080a07988110324 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 612813534 1250 612812284 612812287
    0x1a090604150e0f030a051809090a030f140f03061e030c2103030f09100c08040f020d020a06020105070f030513080721020106050f030c010f0e0406030606090c02190503 73
    0x701101050b40040c03420740d540b14180e41404420010b450709551110412000068000403a54810703039000030300550852040c0c400480e2071814449440d582c2c1810b0768082c041c0558014020901c5100c0c00c07115403080030704482140c56800144048100b908181d4085214444164035018032412196046400c0c00c030090051100760445414030101044006010014211529000071060403c00041d405481824507240c0c181c9800703400d09003000004d01481040c0c43c1420342070001190301800f501c0d0060b40050b20803070145040c0c80050181070004030029007080382100d0006003590194410351141c00d007a1640c50f806110301d01c1c201c045840844a0012072440701c0607803000300e8025030190640038030500101c00c26911503800000d00c2c061a01303070440180e445140a1115080c040a2902400c00980040c800b9101040003c0c00401580780d40b40200865440d00c103041d031b540c6400c031800442d00039508001d0341d626025200c0c05000207041550151051064143e42c0d043e102c00000c204507002405035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 612814784 1250 612813534 612813563
    0xf080a020a090c120e1e060a0b06030c0717090301140109050106171303050c060a090c1205030901030c0e1005131d07050a12180b0a0204060c031202040b03041a090604 73
    0x2800107150110305c0009500c50b03018a4200840300070070300a40091980020815445d1079104003061319150580f0a02441007402070050042d54074040d110100c0c0c1c8440d80c003a00b02e95231380d030313041c01c2d0f000b00812540d240d1701b0545a10000c246000c401c906846905900340a1680c8680080e100d030000200c440c045c071191a00005e1400c44100b658000d180d2107407615515252000403100e141500c01d88110b00340c2607940711300e481080951030811000b08844416a409914a41c0301c6584a0065219442c10305403500900d980b441e12800c03402c071150b400200a0120b0480b0640010407641100b1800c0c82c08211251000c00c0303c030b40349814498038134021207140034107a6490600320740d140c200424010900940307003035140303150500e4002c0c3d0200003801041c010790100c45007850314204501415a5035018410030060141c1640300f1426501c40d505801d007030b51200070001c10000248110340c840ca45886c008424081080102c488100700387c141e0851001c041d4903410007280c0c03100b8051347c004001c0000b6440c2c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 612816034 1250 612814784 612814817
    0xe01020c090c0403140d0306060e31111c092103111b160302011b0305040f080d0207080309180405010e15190b18100f080a020a090c 58
    0x81c0d42c011403a000103410b05581c0d40d16641c02c5d6031080c041d1100c58000d400407281d03841d85442000000c20300c51501c0c0d8250a6240007058400010110040c201da00c1202c0500c11303220034403004000c030f03d40c0d51b4080003008040c040354240354115607411a15044c10038000106000740380245410a90000c4080603105250444207501c0703440c44850005158940411100c104003500290100082a280800d01600b00e106040c1c00c00c9030280c1000c19092078040f0500c0540da1100c2c5010b69070002e01020540c040c000c6c101640d0601860340001035412843c58082091000401d2200c010003158085411080e201c441042d00d82c0a44c400301c6801012850b2519428500c241d03525030072900400000803009010b0085a08195604510484040e0658140111803540e00c81110318083c955400300050b03c2014002241018200310102c0c40a686e42c0101e8400341243c200303400140012504181b54035901c07076040d80c0340e92003608164480d030404140002c08085038022a49200015620801d0441180c0003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 612817284 1250 612816034 612816049
    0x3030d022208010b0109090218010305060d06060f0e090d020c060d060b030f07090b0a0e1201020909010f09050f16031104080a0b220506070e0f09010909050d0e01020c 73
    0xc5491541c55503071a005214040c9050341c0003518100c800840e524800d400090039030312696004147c0c07548100103202c80d04c440e00c0d04102d0140403d1802142c1c51311a0000a1301d07107030310b06401030312542c0780007000140d141d58081036400300c41e101c8080000550302c030f0205c00d40b00d0750740f04046805a081201243d9140c90034070000c1c80748010b0b059000810380e2725030b502c5d504190000c4403003022011101c018005060f0b08042400c009141c14110a850840356050017442c800701c281c0800d00415401c49030402c010000c0d0103130344034107101400c1c007086907079248050f9600980c0b6111360812680360401248080f400c1030708151040c0660014a20740c41d1107108110000c05980c0700b00141c0b00c005200c08145d007241803081400941c0101003591142c00c04c4400182e451401e8520b03481240c22078030410380001c0d4046040c80c0c2c0003003142000314441041f14041011151508030342d6906c00c10301b100104190100703500140c01e07540280c00302c90300445500025101c428541c0107040c05a40540c0c1b501401340b52205 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 612818534 1250 612817284 612817297
    0x20a05031b0f0d020c010f0b130908070506270a02010e0d02010c0618030929160503030703050411090601081f0801020c030717180d0201110607120c02060603030d02 72
    0x10194039010407403082e0321094100801c0405041c0c0c0000711251000403d02440c0c50140300031008000c0e03910904009500040c0c40c00d540d20943c0c2d2500208414000b0b618103640640c1e070040c055840d1450005803020f01c820909643e08440928221180c1250800003035003000158184c540c40c00c00c4044808022500c180c2d44000c90400643c086400d0004665000c0c1c1c510341c1d00c0f80c950241a030942031401a0142405411581d0807a070920400e91161810a900c090791881c1440c44640e50710700e040307500f4506d0170180300c007a00c42d200000c103115800c0e40c5503201d14171403402082c0607035080080e40c01b0802c860b08250303030450001e2421400f04981c42001c2c48810101d01070741c21a04d9000780c1d5166001d0a80c2c000c2100034080760400b0584205002035044800301500c45500143e203440301e1074440c0c842080c8003445050142e285151220110b901900060b021a21181c0c00c5504925003908002c043c48040050b5000180c1019080a800b1b030002480710301500c1c3c010069418183c00c580d0000c003d402c41c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 612819784 1250 612818534 612818581
    0x9030201150b3412031e090506010905040218010b090a080f0604080f21010503160e13030302040308120108160b180102160305030c0106140f100306050a08011a04020a0503 75
    0x4280440014441c40700c803001d01001500d0110b9003041c0c810200c12010601100c4195940c2800d80f1f220000b54007240307041c155005480c00003102d458038004180c411035891000308000929a001080300141c4a001d030055250444014034140d131079411031a266080b021501e0307091ba0002d8040b034006202d10001d401d80d40c4000c80c0080c204100c01a000500c00c1000c240101c0e040c03d0000140024142844000700714107043c2c10300302816107441118210380d080102281e4130103119454105c101403003501160f006540140450b03807140507400c0b200300450421b01c07a0780d482e40704600002600d8404c2400c100d00711000801e8a500380104850550654500b01c3c9055046026030384181c11031401c840806400345000c0c034010360700c84100c8401182103445541000ca41840000140340166640f8000000e0003a815a4404090484480250080c01058010381c0e03122a0014000c581d080c4c2c154081c2840c0e54050004072841041d01c400d2008078441d4041c0b0f200000c0042001031891107034401c1700c64110091 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 612821034 1250 612819784 612819877
    0x609010c210306050301150815040203070e16090e0702031b031306080f07020105010f0312090b1c0506180609040f02060a031d060f07030c030f09030201150b 69
    0x4001078040781818000074902180c0d4a41042c40725050901c5009090700b29074100c618046e042c0101301c0da680c0b5543c15441e418003034810001d0110b407018040c0c540180b905034003010702d40c20910303903a18203205000c0345100000c00d800385c005400a21501e426016900540142d860b110700c0030510340907005584079840c0288810031840345481141340002004220f540e44c0c0d841d45041c03040e544461480f01800002c00c580c101001407208201043c482e9045907480103140c072100200c45416102c01c0e984d603000200390040458040070001c0c004100e202000c800c0c500030405035640d032082241c28107400002d228185238000014119040c41140c0c00d821600407a083c041c001103581c00101c40340d110240e40c0001070740302c0342c080900214a5900d20010041140689141d140901403803490502c001c1c0f0f103d041585a10308407040d103000c0c0e1300010703a00801341d8040c00142054100a406000790022650250700700400020320f80e2841400d6a0044201484680344c0700b5070b221410120482d04c484402c4506079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 612822284 1250 612821034 612821063
    0x31e160f110c0a081608010603020a090b130908090414221a0705190e031b0d02060c0114060a0b18040209090a1515020a060914060c0903061003020609010c 68
    0x2c80c0f0107544003c10551004000c3e101d4034058080c5548016400805140c0c1810000d00050f0344503c4030000341c0f840740030009003280100002400710b45003002000059860300103c00180000b80c0c00806811000741e4041c08034406145e4008450b01e011110600710340d01000d021a0032440d040361810f68507008111080da001c1c069420f4000702501640c003100402c0e8001100c540014040018030700742c4c6503d041c00411b0341e01d20400719444005401c0501c0c4003588800c10b80b0b039240d80e4000100803540e00680b05644402d8159a00c0e8000c1510541c3c0403403141c4108006030180c81c0c400148800d07125951000c50030403018540c0d8039071007800b1940081d4482d800340520221a01c80450441c13144400c0080801c003036040ca00c1e00030400079150401002030358048a41804d061300083c4401c48241d004000149168041c00c100d94a122a450840414003c40d0b0900880c00f9100000d000c3e0148200e00341c4104c0c0c1c45a0081c41e002d0b42c5a840001c0d00600b0034401d070340d1550300408040781c07068082c0da421741da04903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 612823534 1250 612822284 612822289
    0x21040204110a021c030e030706050c1c02030f0603061e0a0609050a0903090902091e0a0b0a0503071716110c2205010918020d060e03031e160f110c 64
    0x10410160b500041c0d0155030024011038140c920f1985107070060508000b9030301880340a03606da220348500a0b184540340c001007a814006082110080c401088080062000c8920000e010750300c1580e0b02c43d0b14060000210714245004600c01d8024947d40e003920725001c842c918000c603000c0000304251a6503655000008280704540901c82c803444141d0301c0001c3c04062494003074511840c50300120300161041c840340c5281e440340424240380c0055465510340c0240e0280001c0d90050f02c0e40c2040b01c107400f020034040700e10398014005e58043c1c0300c180c0f03a040c1c00308410310034651039600841e50401d081f0464040b0100450207807a50101f40a00a010b0303d1a0080c40c01c08945a480c2183c0511100b011420301c1c42c0108070188100340c0034001c400414001c02c8000800b01c40543c2a0f5000684030325405e141c0c20081282503070281e4038502168090f80c4d16813a008801000d003848007540b0f00d00f0000f0b07842c0050310740f400725034034440c03202c0d00358813803041954404034101d607246412201c40d82d50340315458840c0100da = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 612824784 1250 612823534 612823537
    0x12152206091104030213060f05120102160f050607020f0d08090a2f01030e0304030611070c0902030f0f04020a030605060a09020415030c0516030507060912030603020f062104020411 79
    0x1480c2d010115640e03407461050000c0b00b40100240300b149480c00d6800d000462065130f456003160b804440c840c51045500c0e04141c0203110340c8244c80c00481c8082005000c00c007030307000a00381c2280180250342c91561151000c0ea212200d041341e640c1c09400c07220141c11190700601400d84c10000d03190071108000003903500c0c00b031801c82100c00104440201440c40304078550005003846007040a01c4c05204078204492030369a00c0c092030000902449d00d40b050644520074a07026a405c00e508a16444c0343d00b43d543c40d1150007136006075070365024003052030002888035101400751806aa4040c1580f101140313540c950800601c8054066070b80615980c2d40001c1d080494000740010b4414003442140d140c400701005070840720034050074402d0003028400389000090b040c1c080c80180c2d80505099988021034031380340300241800304000b80844401c1441280469040d40607a042c5d910a0300c240100b62110810004079010300217041c111001c080346c100c0031040f500781e0b00396003143c40a0300c0403400b002c0c20051505503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 612826034 1250 612824784 612824801
    0xb0105040303080f22230106030804030209150d2a0501170a021c0221060a1a19211a0103180503040e16030204030b0c0703170c1215220609 61
    0x403e5902a205c2e1075041b0341d80e8200701c402c8420002080034510f5070769111960b01a0344000303071150000e600040e0030002c2c03407407058800c0900140024002100d516014841ca40003403043c0000640361071010170064400c40040040e00e4058507a204003a1608000615580d00240382c090300c2c580038428040e60002c0152000c0c0c242d40e440c2405a1264500174007103030313490740c1c0007072a8140c2448901400301036258501d16605859003560500182074550504c0e041c01e10550964513205026005d400b0042d0390b02c82001d0541c039980170304411b03203100008801804e8070038064106801d2070250303803040240d600039401108210b42411450020030324549801c0e0075134000368058404070f00f402082054020340041ca9001940141c1021402d01d81540c4400c05909401014204a4440000c0680c00c1c9400351502c0516941e402c03c40d240d06282c450b684a406400c4041c100729000040004903e05103401e00c0413035144000500124002140e444528840c1410310703035032108031175441c0c9002c80d240400f40500e604 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 612827284 1250 612826034 612826043
    0x20c0c130f0b030307030c030c14030706020c0c03010e07090b0a050a121e050a11180c0405030f01110a030c1107060206180f06010b0a050c061005040b0105040303080f22 74
    0x5003a0309981c06102900c0402401a10a0300200222070020b80c00c8013940c040c050301440c1c4045248142e15002022a0551070560310b24030002c210002080801d8009012185601c0160b0710410f070fa80c024582a20345483c524101a040b41c0d406100403d20390780b00e0105048014040c008103603484010461000c1c09401c1080c1c10841f065004050060b03026440d1030350888506520b183c03107219181c454980c40003030002041314107141c064004c583d6601348070748000c003840030a0b408c250824050700311881d8014810140240555510070709080418400c4140600c000003800b8541480a0b10131402040c240c682d10044c41035090101040d040c1c1000300501906294000301010b080c41c400b0000b4641c0c85184003843c0347e00c140750b4241000c03404030b0400d0440d40030003182616009014010780b0240540031040007603101e2201000004000002103801701c0d9415a420080c903801000112000c3c4941d02006d400f085410010038074080a030031032217034080401246000780d0201078810f040655a04841581e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 612828534 1250 612827284 612827291
    0xb1501030e1c02030d02040f08160f05090712140406110f04140a0308040b12010b04050d0b0405122205090c04270207030c0b0105060301050f04110d0509070906150909020c0c13 77
    0xc4009e0b0204942412100b12008001030640f0300058110551100c0c001c190080d1081000b06001e640500d08031000005032134170500201050200003806500c0480301a59071074140044554020341950850f00e840b0781e40071105241608110b1034010042c4200d146607003102c80c41e10004042131040700680301510008044a60f900c540e0600c1d1000440c044c2c221101440c8104020840707581c3d102644c0300da4561001da400c4c003954417400c140d420040b01c1030140b01d01144c000741c16a8084d07641180c103500040c41310522a01c040d22002801070818080745e103594100b10422060107a4000c0c01c00000d029410f07003d10040840140d0448001d0340c0140004601049580b0302c22010414815405805400240c41440c01c641c9413000090810908218003406150303a60a0020364803100c0d011160710000c0784805000d28109011155034880783ca2103015011440d14802044404860380401d00d00c0b0059981c0c1c03e000f5090600d1a0029844804c0158443c8584103481425440703061403602c982d2610403000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 612829784 1250 612828534 612828539
    0x5040c17030c15071b060b090c040503010f05040c0501300c030f090507050409080c03180102121206150c011d19020907030b03070306020301030b1501030e1c02030d02040f 75
    0x107440c0041440c0150000c054403c1000040d07540015011600c00d922034881407190800d05240c802026a0041c29070810300003010070004c415000000c0017107a03030942c020031030131031007038560030840e803003030320b0042080d58112800c000c01e40c890038034514088995141d5441d801c050003000c4400b11708000c84044090342724110f24150917010312501404102090052107014520358442c1d031107842a0082c1c62140d030707840d0b034001c081c842c24200303447e031141041003100d680310000f606613401e07024080210740c018424508142d0241050006855602d21078284901d000d454010030000002000340e81180e580d85c0a00c00c9021300d000900417403124469206500c00015142d0780e2032420b1548a1980c134040103810b10040c00141c13507001b800f40e404111482d00203444c16444000a04202d1719900181006002000100030300440720540c60085035a511504841c0310b21800550980e0905e40e4865400c4e040391200e01d422444e81c6201c050190744500c19a4503044220004100303c1e04181c02286104a00b40d409 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 612831034 1250 612829784 612829807
    0x2202120f0906160305090309030709020309061b0307051b03070b100b0c211308030301091503020303031b040906030b010503060a0204180e030d090f12081905040c1703 73
    0xc19400090140103070105142a440b100000e43c0e9103a800c0003050354030300000361400c10610075074200c0c00340201a110351650300c400000180d001528210028003a040124210704501d60a464020401805081c00d541d100742042d40c407074000680e0b8005040c0c0071025908000341c18001002054807514103820f85041c0120401802600d075000020340403c100844c0000c48000034400140c81d4034103200c8030008006400800301400703510700c4200c018116400204034060f000c0b01950590701900020051020001c40d59000c01d0340a2001a4068000300041403520a810b070810400041e08452640f4240e036404030030040312481c2d03000b41c940010300c8006121030b01c0d05002030703508a42e200100f54280f50515020007030000d0902ca4401c100c1d503651003034a541610510030343da06160841c000308100c0866081c80d58400d0b240b4041210a846841d40e03001d000f078020400c4500940304e03200c1d2a002c1003031080710b04009010140c400d86000102d07020001e0942c05880201c40140c01c010003541e00c44000c01c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 612832284 1250 612831034 612831061
    0xd0f06180f110403020d1112060a0b010e18060406030b0720160b0c07180f0b04110a110a0b04030c350a030b0406060f2c220212 56
    0x703105265500788504480c40c540c40380107480550707804a0b000c080b801107928010803210090b500041d0000103c460751210100046059441000c002c00103020b20a1040700464409140c0481c00358044190b166216107a903c80708119801040507100155264580e2034006454204990403c00a81c081a1119100f180b982030158251000300c006c141500d00d454246c400030030382c0d006440f80c01402040044414108000580047c502160440000307171030002a103000e0a80e500d509204242440f000e188181401d1080c0403c0da131203100000c1c10320481380d000f1a00c00300300c0a0039001d00d10030225100c0101e803c0103901c50040740320351501c003c0755000380b07014000750300f200c403803540c10030310007101c116401e200304003100301003d494500a030340c500a04206034020241515499042881c004010510395000b1044a00c0082c1c5515244021100278014038100c403202d0101d260002c450400c0d0a4480c20310300030392070342041c00c11840111141c0c0d01c06200100d801411214560141c92020720100d40c03129503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 612833534 1250 612832284 612832301
    0x1020d08060303030403030509120706050f011e05040c03020f0414090c030f220605090a020102013c020702061606110307170a06080d020703060c0c15020d0f0618 71
    0xe02250314500000001d45901008101406050710340d000201c0b0305005024903c108803c2042040d00c0394050704001d0b00400003100d070b0801d20000040081052070b02c9103800c4203408000c10340903620303500300340c14030010f0045c10340408141a028441e000070208401d01400280c401c50100c3d0340355120110400084c0ba2020703100e996040d80400501181850030392810b40c1c880340c40b045400c010242d01d102c044d103013802c124010f49018600400c0c485078810105082660b503000f41c2c02488200f01c1806071802c02141d20900711010800c1580707410260080c0303452242e10503404040141020700507000708600742c1c010402c4011010f50540f00d8030070058148903440224100c40003950a6280002024124085103c0c0c09103030700105d200000c0e0f81c620682c00010107080304074180c80d4410b5204c0701c0030303640c0e05d1107000440e038143c181348c2440c850fa84500700f544020b0b03403c45608a000b000c400994802540200468940300381c0304d0002212502c0e1a0241600402e80084840c948000e0300c0903010031a640350 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 612834784 1250 612833534 612833537
    0xd081005040c020a0f0819020606030114090a0b0a1506020304060219020109060509150d0209040f0c0509010c03050c01050408180a0303080105151b070501020d0903030c0308091006030c0501020d 85
    0xc00c04202c050b030300085190b2800c3d4130080384100d05c0c0507810680900e0041e10000e4128103126180300007071319800b00e4198021401900280b24102d190003040351141c804484040056115107400008a0005c899240d001315080310009407403000d6880c3c9907148107650300110090b030300000c2c0400101da41000901401d010051003d49512115400200402100d101b15804c04c0800704200d00a90fa604542da03811900000f5007135a202d514901e5040690442c4032a10b01c902d00d0060300e10607002c90340c06001440982540d4241c502080e5600654000381c101c0815810844103200c400061102403041d14062405400925100d0260b1810003c040c04000c0440b40100056901080001d070810310741815100d0885890907000d036138404081960003801e4441c0301d02c1740248283d154820000c90440290b503c01e90030b0303418035031b4000d5003900c48000701c0c030008001030801d1150702d0200f4403d0600c0b035013009a03102aa07512a080f107103402c041c0c4020b41c00a0320019840c0b0800c00640d0380400c4010300344c145070b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 612836034 1250 612834784 612834791
    0xd050a020c010503090c0a14210c010f120c0203031014011e020109081804061712090d080a09060207060306051c0303060b030109050a0c0c020607230d08100504 70
    0x4100094071158450a410306100022020540301c5006205425480c42c010348182422551184280e00c0c44914980c00350007041010801d40d401c1140c024020b400d00b6002c4014460100480011544080d10100c6041080141c0011000702c46450050522010140d8000e6880e410452001510b950f402e0f40014001c201034500b201c5281d030041000e4481400f80011810715081c01c42d010703070140084030001890390a00042074202d0a1b8030b607850310740f031050655082120640310701505944070040d14486005030320199034040c49000e114000c012245010304080c9003a0132135a20480c154200f040b040700450b1041e0010b0010035410000c00c40204640c0c5010701c8442e00d030001003030301c101001da1080d03894080c0400d80009c0c940280c2018004180141c15990f0301e6070b41d130f07040800615058441c1003002e803d00320000d4005210300a542d410a0300108a41c0c0780c80b81994604580d242005c0140b801100c260400c80d001171424043d03561000c005449800051901040b031500d0a00142c1060788180c4c038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 612837284 1250 612836034 612836047
    0x70f030c150c0806091b0a05071a060310020c1002040905060f1e01080408090901180501090207030503010e0709030203100e060f040f20060403061a01031e09080d0213080d05 76
    0x1c0c04030000c0d41142c03090fa90303107125886406e1019860f0f0040185c480680c0c50003e00400080d03030040040c080d55000740310300c036042c20101228552166042c3ca00a0303040d48000c031a10001042680200403070850101190020720550f0000c01c140d2f002070b0b202031622a80c52041103581d05101c40721200c00b50b021140302d040402d881c408128550101030000d0f04010f03030076000408000304801265400100100b19515a40c0d56180c2e80d003e10740c05000c07203a451800d240001665039124002e40701300a41c180c42c0e050a603800d00740c8100800c240141601d01308003840c1f03400809610305000e13802d070060540c00c0100d4040c180e000d415180c040003900c4845108803040030880441c442206a80c061940003c85940c09180208520480f50108951540c0b000d40000c0c00810030010754000b06882c40c80d11464001028140c00640468400e0040c039062441e01407011540c880c2540c0c040f60141c0d210b540007038280749040380c200f4100d8202d02001481c01501120920204d4401c00c8800d400104514046103020b8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 612838534 1250 612837284 612837287
    0x70e03150f2d070f110d0207260a0c050307140a090e01020d061e05012618070909060e0102270103090807050c0906030f071a0c100f1506090e060402070f030c150c 71
    0x1c10720721900907040c4001024182c401c40c9c606034640c010743c50700704880700c04210f030a1003441c1e00c80c940b0581c0d1081c030414400082d4102d54109120b007180c0004d002400c224504080e1501828040c0071091465500700418040d0304810302c600c0014203a11802840084144100200300c0c0c02690131141c140201c0507081244c00a40404000842c00360b0110b944c9940c90348038030300079181c5401e105090a401080f4000c03c810407a0f500034948680a00310038841e1580f01d5001034201e105400b034820300241040c10304030300903c1e01e42448502c00c00614001030032110726140c030501034010381c0049074540c002200c1c90030701c3d00d000c025a942121046014011242e8034a00c0d00daa51902d0380302e030408400040b44031035004180070742925122078081003520820750106000000401d0095000c0030414a04004c09010300c05822110081d03900b41d88540700e8141c00c0c414050700c6400300034112944140c00b08401c1c0d001418102d1403512542c0329455008031881c0034503140c807102460749400d4901c00d1911807424080c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 612839784 1250 612838534 612838543
    0x20c15040506070f1403070309120f060507092d15050d0902030307140d03050108030c0d0e120118050c0d170304051005070e03150f2d070f110d02 64
    0x4a4040b40d8065943c03002e0310705120043c48034034004d0600303503000c108103500501c003000806e80c1e584071360385000380c09884484d074403102d40c5c00542c00f5000418405012000480903031085030001003906000000d40e0341c070071903450300140306403100300c1d441742c881000c0807848076211003000945840c1e400340100c01e0740841e00030034078042d4441000c60140c84801000030340d102071045801c450b4101c912060a00c0ba1039032440d964061241c120b80010340b82034000100780c032020080c2d480b03040d10200501a1030b90000e00c11540c10180e2111240d1004074044c000350300c000c007440b0711900920360345010780d0301c031025040c43d6041a014446090180c05030b50340010000305944801e400d500009045281c07284c0302c03418000e01d0100b0041a01d18468a032a09001070740d41c020402120301503003107089990304050056600c000c00000d9035072540403040d190115441c08078455032406000c0c00d48103240541a81c00c1d6410700890004d0350442c2c046078111106611569014182c54800f80911004014501c6002c000035541c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 612841034 1250 612839784 612839789
    0x70b0a020f031f0302060f090906010f0f030f060b0c06010e070f0c17090a030506150f030721080d0f1116080306010c05030c060f0709080c09040201171303020c1504 72
    0x9410b501c0069110f407070140b440c11405036030040c0080341c0b210b14aa0300d050843c0d00c180851889a144040001d14035880b581c44070780750411b95921802d4226004c4401e8000d410200d402121860301c6080101c0c814401602a0441800030b01c01001554500910400c00c000c02600d01410801d40c2055201c01c0e42c0c011140c41c01c490750009420109a080340f0140050b4000e0300034840e841444013000100b880300009074079014500340204041004080030412000900c2d0504054054028107820003413060300400022203c40c0c149101402c4090980e501852944403002c0386880340c4d540c9011800f02d030b00c9803107003014000341d1140d8989090000c12101252040821008040b000000009201c0d039125003c8402d020b9800802c41c1d0b101c18600c42200c0d06d42c10121044c076401ca0f4070400181d8168482e000b03240443d680d40000c2c0103001c900c0c0c01449489000100240d0510050560070954028201040d074400c1d441805111235100c0300d450700a042038400e000e818030450821100404030710402044504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 612842284 1250 612841034 612841051
    0x15130f1a16021203100e10060914011d1807030f1b170606090a0803040e06011e080c07020901120b010f0f050d050f0f100e01090b0c0703180b070b0a020f03 68
    0x116961541c11188501441c3d8000021035050282070124000804074050155000327500c8031a4007039169074200840d281441c5002d80021200c00c003a6108078130490130850246000b03000c602000105d6400e04004400a40c0d004001a5076010b0703588403084244210b10b03003282d100f560700c0c880c4144030368024008079440c41041380114020011a82980c5e40c641112106400074080d266140da6500070a41c40350403600c604110a030604001409640c420b6447c9001026018035016201d1000c0a0444403451f00505050803905e0800206007d40eaa15140c58003c0c001c0b4440300e0a54800d62030140b50356407041e48910385244084030140103540e00b01e40c1c1c070030944205607403807c1001210300303249140190045c01c0912034012103500404400d0003040800c0c81c81140402801070030403000010f422140d0740c0b41d029115520300400f0410414846d001064000e01916055105024079583d40c01240c4c5583d2002d2010040052060304004100c10102c0d0b1014005004504220552035182d14500c8001c0c1b2824 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 612843534 1250 612842284 612842287
    0x1b120803040813031212060b0705190501060504060e010503010c031a01031109060d14091c030c0507060f1d03070f03230309100e0f15130f1a160212 65
    0x10f00703201940880100458019640b604511440c01020380b01d0360480307400f81411402c005000c20341d50400d60417a01c80c540e000c1c000b000e0040d00b01701e490f00501c55108049410795240c41d00000ca0b0ba40700d020b8000070b88003500d540c0d2001c0d45841c0030142102c02d4100b03c00189401d007010f54880c1e05c840a80080c550310b00307081c0412400341041524005100d000080c961091011544010f44001c41c3e100314025460107070f40502a84a202d0490783e41c1c11030300310300c00c1260844901005494480d030000c410014050038160f083c080c444d9683d0090b24001d21000d0342490340c0320307a04681c42081051144034083d43c10050352600344591101103842c04440ea0140601106030600780c211401506520101d00603141c07030a8580c10420a1940c46856840c110300c003503820995800b200440c01325080c90b80703031800001000104454103900c140401d00520901c045100040450007040407158205007091040c0b03580c0d8140050a21114a400406444001500d401e403100d218081e80000700c001d00d9040400109 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 612844784 1250 612843534 612843547
    0x60f010c060f0c0f02030310063b030d030207050a0221061612050106080f0c0c030d20090a090228110d0e0a03080d0b030a1b1208030408 60
    0x59569000d41440141000c0c0340c81c21200c031200441c1c0c06150156000c1c0d886200050030100101d9890100341d42a40039151080d1042201e64007605ca0035110040c1200c02d5020070b4a40314003980000d003a00c0c82c42000f410249200013292900b40041184803044e03040c02c40c00c10089890b01d0350348040380540240228aa0310030784002c24805546c2d4103421010714210781aa1070115400290102d01d116890086980e040501007540c11601816041e01d0329951001000e83d21a2841c454404003e842074010000420405007407500500017447c40144800d404a5045083c106085501043c4000391030320355000d1140754103e44d50942040200c0d001c00b13601580764800400b5000701d4420043d5140d03c1d16141e0940d10425607003220607510302400d600d060380c00b41c4034204030548903141005040c69002007050800d1001900c0c0c01d01400160b111064001544400d80300031034034106540310306031400c005c0544c51184840e00f0070300b0100544500c5c601c589110203c0e640307998490001400042006031b0120707e5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 612846034 1250 612844784 612844787
    0x4050c12100e01151203090b09060d0911190512030f07033009030324062001061419050f1e090a020306030106050d170a11030d061401080708060f01 65
    0x480c4c56200030382c00112503070b0704680700002c00b01400c01c9020550080001032200e6400040e14030072400540031510700000003003000010810041c08a8003c455103502c038000b9229200c20003125500c0c1d545001c403490a16040015005800c408450154010070020703d003040c1c103000b61341402c0e41c541403c100c02000300c260f46040000c021030351007621010320090b80ca00b0040d50050244140242c07002c2040300c6011070080c801940b001210880704070b600d402042164490f12030b03040b14070b003005403001c800c030001c01c10507080d1007450384440d42d400c0c1d04c0d40071800d40307250480c1000e04100d080f080c2030729031903e0840899407103640b5180344c604c596500300304520ba001c800c145000c0d100800800380c400504d06880d10b00c1c004d400940b4018081d62800708042a02e050100d5100c0256400006807a21480b000c00c2c601c1d51503000107034003002c10030300309010343e810201040a00303c22288210081403481c2015480380078144a01c1e4414100320008040c0a4000d07000f845103900201e00781d81410b40855000d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 612847284 1250 612846034 612846041
    0x124110102071505010902070c141c0606060e0108041208041a1609050a05030a0609060212040c090f0203251107060302030405060a360b0f04050c12100e01 68
    0x65500c0d40005184020000301d0710583c0f0088002000812840e62900d005800700d0185101c001d00c20104200188515110344d03080d5451050020980d4603079010752008030300f0b14054800202c0e000c90711040c0500c480303074105030b100c0310303505084ca0812110310b40380d210345100342c4111401400b44a0200e0215003440018084011214148100c4c48894244490b03c4004840750b00d40c0100000ca10102c0851145841000e410403180020003e06083d0541e48454000b42040b4034201e45060b03003044030f034035210740744200310384903500804204c500b035494610394200b910391151884114910400400c00c00c440c4510441050184c1011060f13011009181d050700c00030303c070180005580c03081100005140d54183c0065208620580980300c0340e403607826030b00040e10755100d880790a40b403808103071103020700c060206140020420900c207004c803901a201c030601d940d0151001c3c84804240720401c01030040811602c01100c0f030507103a44142200c0101c49a48480b142d071072201641d0386495400e0541e030f40940 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 612848534 1250 612847284 612847307
    0x30308070c080f03060907091d1806071706010203030f01030f02150f22030807031818022d041734060801030b0f0c1b0303010f0e0124 59
    0x7154140d949440d01c550f901140c1080381e8a901c40c400100001d40d450340b00d00003c02c1207800d50b0000a031101c00202c00010601c00081007820070b91004d0003015002c0008100382c601401041e15032441440c0c003a20030f40c0c1040300081c00d0906540c410030903c04100710003c40b0720b0450341c22014140300c5840300d2001407240c014020031010003a10115080c001c1c002c010004002d41c80e138110808104000b0704000500c080040c2c840a400402e007131080102190003000e4150003a01c158110340350b01502c460081190341c5595a80601c015070200303610004481c40da9959a40e02103104d06c030850301010442110071485180590310020741c082c0d004101c0b05008000307507245035054030b100010b80000c440740d00b00a42c3c450048504140300d51100029000c0c080c58a080c1680e810117245c0403144c0d903141182c001c00d10050b01c0040c000a003002003410f40107102000700440c00020024680c0c03545411045007003401690050247c04040100400c4168482d811400101c1e218403205280701d040100c05071407481401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 612849784 1250 612848534 612848543
    0x80a0e01020c0915030f280203070305030c0109060b1f1202160b070311030903040303050f040302030303040606090507110a06050403111c02010510150806060f0412060b0607030504030308070c 84
    0xb00248200d40184c890384c050180700a034110f07600001102041030352041e00b1000d0043d0300c41104c559500030f03905905200c105a00103003c550050f9980e5440e64550b50040140000d41e03592100c2100c100f1030380c0d000300001c41c0003c90300c400e001140703d240340d910000142c0368001807066034280f80c00c800800390143c981d9400398107607041d200b1a00c4d0a05010005007210401d000030315146000c0c0303510462206413801100e0540045040c14110b94082d105a4803190040a000e2800e0000000680c0c0030402144958820140032451034034000000042d80c40150103c01030145003412040840f40005140c0d0010b0b407c0800410f4a440c1e90034207803940c01c0008244051401264050b8000c1c07500c7ca08010130700e06032980200a2607071500100501c2050300c1c02900c075190b8182000320002032142404641052008205070b207494000c40000c04203501c039612000400464101406c00e02035540b1944808040640e005032425840360303802080392003a40401414801c202000c1949244501603440d20990300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 612851034 1250 612849784 612849799
    0x60816090636090506090f0714031308040b0a03110f1c0b0607230c01211d0c031009032102040503030706023001140f03070e1e0103080a0e01020c 64
    0x112000e11003e40402c8448901450321b850102c1c0c03400d403020030b01612440707059944589441000e031808545600c090b20450300301161307000007404210650700074401003616165181e55800e1040020701612030000006111071424400912281c001030b040f41c040d280003450928460200c60205001405901c2a030ba4214401244e00c108204c022400910b510785080188210003020058441d90750300c5030a43c05001070f00403080da26206800d00c2400b0b542149404010a03803c0480d01002040c05102c54009581ea211441050f441c0c207050048c1d070518100c00c241807154502c96103010f001c800d00600c030b024100300e0103040712621007001e030305840241000509030790b035449447c280f0741e02a4000c10740c111025020019000060794001c02e60740c0c68220a881d40406c6607103090180790f0f880c803110703d0807030b0011007080400100c2e650030b01007a0082d10f004282c0702d203182030020150580c8014031500c0c2040b07122240060000c2661a010f95584010030702d84000b22003100c45c0101e0904c0b41c11000150043c40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 612852284 1250 612851034 612851039
    0x705030d0506090a1b08060f0d031808070b0f2d04030210050a0e0909011d010207110a0305030702060307050729090a03050d05060d0c060816090636 65
    0x12280c00460282c10100d40c54482a02c40358014011038400d08600e00c61442907031048083d850244d0941c941c4585c0007885a80900e10380808030300d078480c900004600180a0010445a00d440d103c16080544bc2c11001015668200641a001441020108502450046045c20a6094040380024010142200007011118081480c2c0c400c1d00705000891040303060742c9a003881c681c0310740151100d41000e0b560b10b040c01b654490030300101d9003020300080400c0d502c0d10000ea00c4043d060300400c6900080000041c0d0b1641c103424a0503403000b68144451150b1400f00e000c1021036000001e4400080d011030341b0b00d41e03903151001c00361604d20803180e00424500c402f0700d0910f2403a03150b2a4509000b022030b03401c0740059440c038034416110080100e009010070700900032420302c0300e00c1c0cce03110551001c2e0142503002c0090035925100742c40070b00e030341c00b082c002a100e9040041c650400302d085101c01d0740300c1c140b02c00502d041070006010720a50040360000180c001d0580d2002855500d00360311600fa41203115444940c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 612853534 1250 612852284 612852307
    0xf0308310f12030806090928020a05010206040b07050a02010612120f020606180a1d0a110f0d1101020a15091b0b2a01020310080c010c12050f070503 65
    0x7842501c4064190000c0007400103481c20000200c281e05964884181c0d03031380000c2141014014144900c00c0c413030860400118041c640aa00e6a01240c0d001001d10380380070b00c1000041e15240d082281150011000d01002621440c50f05412442c1410540d880f910058000c0b4010100c0f03911480741d01145503010340a01403110b00728180c86c082d0b50b5070403500420002e0140d07511501680e103207801100a130b880301144031007288444d07044810994041850241c140c0d0bc200040d111065210b01e40d004041d13030f0420400402e5400151242c241e4000c160035411600060a601d80001e000e440c900509000da15a40e02c2805420314455101c20081100340d203490401008050700d140465030a01c4a0031142c800d40c2c4900680002c6943e8150303800c1ca440000c905002c80d200d82080e02134903648101c079510084250a0025500c13a04444060120491a04141034503043d4040d480b82e05108499500700b0104504c0340c1190305594040c02c000b60784001c4035050510501c02c940c00680917010210301c0342d0840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 612854784 1250 612853534 612853627
    0x403020312043801050f01090e0414060f060102150a15030303050a1401140f0604090509010203040303180c0e07200303060316120605060604050303030f16090f0308 72
    0x2000007518802c1080c05022104100700c000b0740e0f064807000411004100f81e1400740c4080d21443e0062412040880d80c4000800100d08161822500c90309100400042000e08010752940400414910210f40c14001d00107501d4140e13240751004c201d03442400060103140c65403c019144041c031040181d200c1c1d940d040040060000340d54105040d810404070a188065615109050340d00305c407240c4c0e03c614a010f040103169000c805180d50050800d00000a00301441d01c01c483c0711300b010318000360350791400b0710340182103504039207021121005629107100030440324010401030346d1401040b0550782d2200c840030f46003000b14525050900c050601c2c401204034000c4007850046c20705a040f14156149111004c0091415000d0660218549a01c080110300c2e80d03000960010405411185400e0f11140401d066030300c1196100061360f440c1090046c1a807402c5c1449004401c41d2a04000c0c25040c0070305075000d00b40c684405481c0d0300c80410400fa0003420100300c2145141120002c3e4214040c1c00c0c0d90003260b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 612856034 1250 612854784 612854813
    0xa0302010509011a010816140a051309050c1909080a06061d07020a030f18082508070e090309040e1501050d0c05130906020a030b0a09090b070503040302031204 70
    0x155401c1c482d114100c0c1d0b650b03407881350746640140c68000f07040c0d41f030142c819500c052500d031500070405044900040c90250304014904070300741d540c5099607108414a842c80d6641e00d980942103007480c10080043c04a00f80040d100d00350041800c2000c00940f5131003c40b05d0140c20740007a001e901a0320406404c00100d5800b85e41110b0040c05800e442084001100c19600000c0f2107800c0907812204008000034852071041820700c60300e040400c01421140c0c28920310000642041c03015511002c64042002880751030080c195803e00c0401641134101001191290b4151240520310f4440c1408200c2d4907070140180d8011780d4029100300710041c4210f4985580760348012908401c81c08840000c0740d00c1c1860010f000310507070001c0540b403100f450074042c03107001d40c512400304240a9603104048009040c90000702010b04084e980490400040d074204541c1d15801c0d8020581185032044440014044400f29070340074850b41040c54499403607080a030300f10301c200103c00e21440250360400c0200681d18080641 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 612857284 1250 612856034 612856051
    0x181305011d06060906090d03140a0c0506060915270916060804020907080702030912250e130206070b0106030614010813080307050423011103030c07030810080a03020105 74
    0x40d850b00b0080c44100e01c00c46082d280c0101c010414088181002c0c03102001840c032138640141d00d1501c18a02c2c80154202d8401400000c0340d104004044c00002c01c90700741c22481c1260003c9403428200e0b10810b882d9500c2c60307418011050903241d2420781c03208000303900761541801b154440b107141c10344260351202594071010302440d41070100411024410baa52900c0b81d07070302a104e406e094807026410768510000a12401c11031004220101182e00c402c2106200800e84400801c045003903a03906440c0c01d507050440440da42d6000d407080008400500010707030400c002002c4101a2002c50000c82c10a1051344170141c0320380d0305140001800d95250f4414011103030403041141c101c2d80544011035940300261010032080b03004104d00804100c0b60001035030401d245003080b615050380c2c3c0d070503101040803014410f074160986185413603480d604046150304030172240d400b852641c94460600d25103406a960042c00f0800314100290904282d1a000b4000d044104101c40d201d01507450006d010f05400c442c1c00a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 612858534 1250 612857284 612857339
    0x61d0613050d0804030804061515020106030606120209041202192103110315010e03010e0a050d0201271104020301120201120b010917070306110c010c1418130501 71
    0x40b0203501c981c904500440e8155513154281d20b95072900300207400203d040c0101c19010314000258292845d4100461827402c0c0c001094961031070401c03400302c400e1540030701d82800d07481044400581d0340a40365503006070301100b03480f10080050703412484c010b1464036801401804040c984180031007442c22800f5008034410f0801c200c030602000310300f902c1d014145070302401000c1c00401c41d05019a1507426000c0018074001100540341c10019094908400c146060740c0c108410443c00e101003445100b44018060000303200c0824901807051801c2d048508800d0114107a41d40c60041220040701e50100410050080d922941c691003204d40021030000308a0224011001b42c0264007818065402c100d481612003125062030882074030943c0400c20540742c014064034402000241d941d10480e45c14070100300070f054450490603699400c407600c8207070039018481c07041d98054450200000300c440d110030701401c88180781a14004103941e0400300000804850070f250020401c0c404448030520781440d84401b40c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 612859784 1250 612858534 612858553
    0x51305090f0a0e0316020f040b06030a09170306010206010e0408070602030f150409031b020f04020706021209060103050c0f010c061a041512082a01050406050105120604061d061305 79
    0x560b5901c0b40c20f11740d40c2e080170515056070140c9400c000040e000a40075001180e9284840001400c5610484145d0300440d40d0f1182403092103044c00c59000300a2403a4081c030315600384034002030742e501014420141c480005400040030031040d40300b40e43ca410361110040d92a41403070740304441d007000212001c040720301c1c2021a501c52441c083c051419140d41640b03e8920202c502c5d40310398808105100c050740c024003035000220b52500d50f44000c01c0310700d026560050700e03015002e1150030740600141a60a25601640040c07001c120003140518900d80300b224820550892200180c0d0088002e0101406480c0340c4011042c0340d641400c1d0707866003c2400c60b02000900da800c2c0c43c1c11907072402405080c040070300007e000c2c0700003a00c4400516055800341c64a0f401030302840792446415010300c07080c0246035101d00c00e00c010480070f8001d407400342c201140d0050600300ea42a186a4500c070003070002c4d01194130f401501d512030307900380c580d181f5451100060303030254680800c0382c7c5019550050112018810110072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 612861034 1250 612859784 612859811
    0x507150503070e011e030b0402041e03031709060a2003130302060a11160302010e06100e0c04150e122b02010b01090308390d020c01050703051305090f0a 67
    0x221740e40391208507640d80c60592110850051244070307502608903a08000c04940c0014000b4000c201240c1c00041001d11030031850024810100c400019281007101c0c1c0503c90100d40115105a011100b110002182504200f2038000002091010502210000b092007071148013041c00d01d568034041d408a841d65140c8090150495102c480c94100d6034005002c100b14551080d002407c0d4903019100100f1030451920b80715081c103106a500310409400d4420030841942208400c036407056044035210309040c6003204c6109400c0348004e50104116500c580d002c40f50380d03081110540841000201d07820341c1d80300400461020548000a01000000002c01550601c140114140790740181d5030030f40c003d4615540c04455402c814034501d95104002d01450400107000d18018600f00e81100b80a0500300c1121001d0601c0007080d146000c40d0040c441c80d0701c050b604101210481035052800030b90780c2c5840e0b116a5201096a00b241c0d501c55001c40601180300e0000e0042c034003c0c030001408014090710b60b070a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 612862284 1250 612861034 612861047
    0x30c0a14091305090307081315090302011403310213020304030c020d0507030b0f06100e01090b07050c1201021b011a1333060311030a0203040507150503070e01 70
    0x60381d40c41002d2612101c074401caa81c00c0282c11911140403203003001d0195a0300c0c00c0300e41210300c421501c4854940700b001903210340b10200c0804149d0f414000202400c50700020f180f91155658002e011400001041daa203003801c028028140721044070120005400e000c81220a28110041c2d200d0144204c1d00081a40c1030300c202d03401a0b52584403115401500ea0031311a104000d000150358900030120004080b61070811220b10590100020f12120301d0b2100421400300c02c90419a001c00000400b400c5042c0d030484003031405c1e00d4810a0301c5032100e40394a0564540f45441c2109034000610f488155070540c0150060b01c0781042e03580d00403007124045c04405003240e581800b501440d5500c00d15891f0582440321440c101d021810b080400e00d41001c001c000104000c15100c3c07030344900306180082c096130748501c90340054a090300d010b0120740440d12185849000c00783c502c1818550000c0420100101040708400a01c2c0240704401110700c01031014082d60000c48011000c100021440c843d02d41c8643e5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 612863534 1250 612862284 612862297
    0x90c0e0315062b0f02130504030e1203070c0e06040b041401240801050f0f03010c080f1005010507120203300604020f07061a120a060b0103020705030f0d0b0402030c0a14 74
    0x40603030f607088142c1d442c0c0030b0750342007040d009907040011484050061102d030b000d5944200e000742c4400d403810b1080c40c1880840d0100e03d8000d24075410034006ca07030008204141c25021541c0d00c6a10803502e4031110001001041c0400f2038030350092400d0740000604103030313129040c101e07040711680d440c0d00c0f00382c3c4406200820408080701c0010f0642d40042c001032400d95008054206d0103000345e8413001810000c24210740840d20780d80f0208010204105404085210705540128040c5860211a01d00307400640a070241070300003800c6100040c052400c1c02d200300b0694402c4e1a20800e0010b0030014200c5030f00a41111019034260b10b48001e00181550070140201c0b01c5103419610311a1618070700d512210014880502c0c3c0300c1d0210341410f4881015520f00350302050401c924005050440700a26010b0101c4003060781c11814140140403d402051020050b5000046154000e41d42c40d010700320110024014907a079541d204c0d10210a000380f410700728018020840390340d1503159107400e44040d049143e01510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 612864784 1250 612863534 612863599
    0x902010512190501080f010b0625060f111806030628050603090f0f0109020108040b0907121a09210906090d03020a0203070e0106020601090c0e031506 66
    0x800044401d14074038001c207688801c5101090340c0002e0a450410309580c0c080e8000c0c140b9030f0000a161803840e0007072040100002c0129001c03450001e030b001d070a51000588860070f40b64103520607540b005000d43c0390007040f266000780d5020800312025101404051700010300e0301d84030400c004961421410040e045a0048800404100b0080d415940c2d40a0b00d56010100049040c4c00070030006040d202c00024500070740b40b0320050b010803401f407080b0601d010001101d01c07040703070705151220002d070360000000f541041d0013210041da150b1f0303490406480d0001a502060102030fa4104c100c0c18016010001200e01a900a14900c151619043c3e5a0344000303070340074220304210703000c0c21110855200004004404002e0102400c005000c40014601140b000058016820a655040443c503060000102034140b40d1018091035040040c000e595007414000e095609070f44186048880780a2000380c071501c0c00c02400c80e0b4160b8071076078081c0045841500c190b4000c90362104a0f0034403e180d25444101c62154 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 612866034 1250 612864784 612864787
    0xd020a03120f090b0d09050c180a1505090a0b0a0e01060e010f111e071230020a021c02060a031b02030901020c0d03200d02060a0216171902010510060309020105 70
    0x101509880200a806c0e0f048405118240a00907681c03a0081141031a40150003071007a0340c50401d40c02415a84401740d803088420456000b03012569902e146150400b030001c00c001115980c04010502c02d50480d0010030b8007c05200c00041d800d42d0114140a41500a80c0c460300143c01e0450700b620020f00144080b40140c100d18480c5212500400444201d03160030b404848141d075803910782500d10329207207405a1306800c4c28281e24540b1003201c1c003041d03000c5660702e10f00c628003201c8840003511580d040c00000e00c5082802d01c601801c0c20007100c5101c15640040c0301c56a91700d05920040c00030711052013040e252164881160a6090011007a224090b0301a005401d00011031000c1104440d8540401ca091010410035446c0e607840402240c105020310748024054010300d180d01a2502c03100814249001d0700400540403c0303040b0060444005a1203041079801600740030f4151228000c2c8007001201c5a100c10b070b1100040c0c1d05400142c000d070400500000991340300d05e01241075030440400640882d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 612867284 1250 612866034 612866047
    0xc0402120f0702011e0e0f0d0f0513090c0c03080603070518040c0909120215040c12020111030c0d110c2404080706120c08090c0409020d020a03120f090b 67
    0x3020039903958801c60620000620348894010010b0381c4200d0544009541e540d00d400b241b021008208402400b001440241300c40284900d006204d484d61b42880d40400602052070381c002c00da07010701100902404001405a001651002813038554034600940010380441c0108038141408103590061722006001040400707203908102307200f06c4002d0700850b1129010100001c2c0303220a07103e90700c082d5104040d0308900040204c0024503101a5110090100004d2414840090b20580307820046446030b0852011b1007456000590b8002059590711030345000c0007660079a400008a410010121280c5462001a4442c00c0407541e4881c4070020316001030340c01c24510500c9000e40184072100d03440b508581d2030143c9035206e00e03040c140e03594401c2001c11241c400902004c0c0781d0b4002d51029000e01d01c1d101c07109203070000e0b030650b6941c282440076010b40d90b25004941036443c0c500d160800682c02604640c51583d4a1600324110380290007503400040e2009643c07000c04c0d10030b036507281c2243d103602641030810a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 612868534 1250 612867284 612867301
    0x30f0f04110f0109030209011707270f0f050403120c0306030807030c230303041101050c07051002011103010807060e1509100909150e011208040902030c12090f0c040212 74
    0x2c2022200034103020200f0b0300080144d445494050180c500501450303848042103052501d030071103540203a100e01160a0300c1031402404049110054900c8131004201c01043c4200070b0000c0c0820000d010307242e030410040009058000c14660f45040030340c0350401003040341c8401181140e58034000107006207030400186012902c15404000c2d580d0280c48900e88000b901000c0c2ca1621660003d0414036400c04820001440f07654159400d80d07000a080c001d1419aa8600302350b240d090038004c66128010b040d040301c0206100f5801381e1229480040d043e60b50b035840300cbe500c0ba61011544a14400500125090f10541c142854007200d0060740702a501d040c548000208881c3d00c1d03181e102c0b8820440d160100140345c445c14000c2401c0520748041c103801c0c06081641800700c512058000a20013280e4100400000f81c101080303600f00c45807a4070060310b03a11206502032052103210301d210b41000d0024280038a0300f4002c18a514184101d4084910b814030000900c4103034062a01790852040441000a1120 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 612869784 1250 612868534 612868549
    0x20f040b0309031308060906151c050705060c07050f0a0e0a0506060f07030c020a1a1c0209030d081e010311040507180f0e010e09120a090f0b030f0f0411 67
    0x3000c01c4090341d007007000d114503c60700120590b01c885c15642c8103805000e01c800d01031207166085911011280500031440700442c06212600100c1c0e0300e4800000404414024281f2201001c2d090090500b545c4009091036540d5584150280710b1052450f200104940d15241071001d04581000341c0c0004242d44017140b00006107170080820303402c004200800481c203600e0704000d2040e1031190306c628045035103500500c80700d55515003002d119200e0901140c00d01100b1001070b80c1e1580e82c01e003800116442d4142c031f158040c1c018000700c250548900700e400d0482c41c0e00156414899004d40095000404c4040032101000c6030038070000d0240c142587d25035a0504103071300225408041814488240150028150403280310f5030301000a64002c20701c01e201d00400580d03910f0040182d0800440903084c5840c265858564402600e0101540000d0114600b4007407045030004142041041d8080307035503603d40031002e500c00c40360503030070200e041c0004d07400c82c4680500b2402150000802c010041518050200790b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 612871034 1250 612869784 612869791
    0x503060f01080a080a02030705010f0f05060306062b0b09071d04170a031401030c08010b0301020c0c01030b13091208010803121501030b04020c07170a03210e0118030210020f040b03 79
    0x441c01f04026200c04620240941000404000307000900c84904001d10340403a5030140103a88a6044081446041e9445920b980d0040101803d0841e10303014146800d0074255801800a00055502042100c0c60001244040840e442c4e42d080400c80c001c083c1c403000ca00303402210014051898410034403a5003c440018144841031410000358017001d180d413110090209910488541080b031074288407004007806201030301e602c15002941010f500304811900c5003031111015041503910350119526a0b0707031180b8041d01c100044410030101696050120700b0f641d40318181c1001c40c01c100c0c0001124200003007240c89421440801100544a03040c106648010a02c007481c100750700c541840f0440e5580b403000704402c030070318002031208903d032503980000c03100c8803a5000c182c1e4006001c0340d000310b500600b050200940140102d8800112001c01100400c0c3c4070400c000c4c20b40c40c09958050000b007c00c07000803c1ca00a400301c410b00300703541100b07009a1041038035a02412005020404c6009002d0000d10780 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 612872284 1250 612871034 612871037
    0x80904140c0a0807140c0f0c03070302010903020f04060b1303030e060a020618030405060a08060f092203030f0905160504020f0406140c01020f070c050604030c170a050f070503060f01080a080a 84
    0x1a50000e00b0030105c1da400414482800390071100020000840402140c0c00c41642600601481c80c82c0d9000a050b840c41403102a003d110b01c4520002541c0c0d403a400b040141c0030b0031501a464107040000300e813400d400c501084000c928502182d01d60340c6081000e64607106566402400143c0d203401881d070200c40a04040c1c940c034401440041201d540784006460000015a12146945415420040313101391082d05140212007120900c02000a07511000344811044030490510301103602d030840040c191500c00708405440c0c554002e0810030080b50409240e110f040310442c1858031035003040201d224254021101d17003c100010820756001700c4c10303c10040e6080d07030300d41d080100343d1854500703aa211021050021400081c00e0781002203c095540c064107069540310f041605560b2440c9170002d8a003c1d22120b003c0059074000609404c03c01c4a41c056800000d0302e400d142800761a640e10305003402a18070074002c210000b0b520080b00c0c50321038101c880c1c100c01001da0784603540304c0280d69405400c8400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 612873534 1250 612872284 612872297
    0x414010b0a0602030c0106090c0c17070c0b09131b180308041508010f030203030306310e0f01051b031e0c191e120603020a03080904140c0a0807 63
    0xc016500d0303201d84001061160083c40e82c55004001003802c5070210f42001c040a46072101003140755034018418000640d0010741c2042c00d0442c141c4c03400c010700500f0030041940100020200d260305818000c0d0441844c291084800c5038056000c3c001500c170503070780140402c1320889249810f40d12810901441e0b0700c081e130011041076182e0b102c1040543c0540c02036040324910101c12000c555201000d41d0051540d070440c00082419503000a40341c0c8005030100307200d0300800304036282281078030840381e104c00c0d215041d03d0ba40e43d0600c000d8001516520380103a100c1e002d07086c211341c12114107000382c0e40b1070050003203210318406145c20f1046c0e040e000602080343c0e685030607035a01d0301d40c104c6038189402480c03003111940d29420781d50308107609800f00051079000c0244411203d00511107400e18500400101d041c0303420702c40d40c1d1900a00060107aa0720295222101410000601040b20300800c0755030004da6082c002521080b64108004000f03451180050000300071005d41c45100b40d6025810450a2070f000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 612874784 1250 612873534 612873551
    0x1020604200a050d0605040209010803040e04121b12022515050f0c01062916020303090d110a08070315020d02210f0108061b071109070c05100501050603041401 70
    0x161041e01021421102556500240425864100301940c011304bc043d0007145854101038503403045600280006041c960780c1e0800c030b8442e9004880c0b50303068030f40c282020600c0700854209074092002041050016009000700605215400c0400b40c01c07071503502c103081d00c8040c90180510b483d942c042040d1800c12100b0320271185c111a07020010486152600c00205010f0b05001d14260354a051031028001c80510950038580c41c2002800d449940000300b103484544d040710b00129040d441400c486640c0700180d840310f042080204101556440c0c403d54001101e40d07243d0b403180d65582014000a48020413034040ca00c11821030760010440d458590a026040450017008414248540f01124031002102e004010b038050014260728010450107005051130700f00b078258a5010309070b0141848090b0030006580040c0302c85144290b0308181b01800b448a640381038100200960318002003141c1c5070150820340c02ca00c1480e4025a8181c0e03000600481c41c54880b81e403030a1903030036658134a000554803280d10b03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 612876034 1250 612874784 612874789
    0x90127170a020c0f130504050721020d11120304081e01020c06040f17190f08070f180b0a021e011116050a020406140a090501080c040c021507050a0e01020604200a05 72
    0x405010710700c1900104030722422b014010695407000401c0e07880100041c00d24001503a10400c1c03405030a5008a1507648044d0200007088440d01e9034410555203110004d800036a80e10005003201003001c84840e0003008080d8201e896090b442441c29031109070f8000000305002c00c541c0d8113044c0c0e45a2141c45142c0b450b01030b030500e24605812019070418081494004901c64076080450352980308010329080e003680c03a0114020301a61010401d100800820a079000d0134034614600c8440036014020003180c503000c1117000290f80f01020039030456604481050300c0b80d5104140201c403440c0c1c0c98030740d50605003258800d0542d81800d50210954441c0f1803c100040540c4841c8034206c007030415087d408904c15124014001e69500701e5214540040c0303810700404c6202000308201d00789090491740840d004a0055040345084401d04c802503103828044188107040b50003100500343c82c140e0b40c0b100314a212084006a840b030300304490242c0400d1a1501640c456810703124151203d0300020311036403082d0b840380d02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 612877284 1250 612876034 612876041
    0x70203071e0303050a09020a0312020313120c08030f040603051504140106080907030519020301060f060c0302010f0e1b0102101811030a0812090127170a020c0f13 71
    0x265040120701c40320040a00d540f601030180d1010b8540b00c1407081d02e00c282e0100d00c00030302d00c0c400640620f604842c2008058402d000303d42c4c0100b070117007030a0591034a43c5105c61900e15548400c5440718442980010041d0300030054a03603038007404010a06261401c1c3c0b0540180c20300900441c0308401402b603003499552070303114080e41c1e0300c0c1044140e0420740c10030002810060029008402035888100101700040d40090141800ca42c00080030140c1c1c8414404039025145641010741907051214001c60040e9016002c4510b0798003d03802484401d688940032411200b0078064140309801040b26150510022198450458018412107220601864060048800c103189140000c038041c408030092000351088080102c4088014003290882e540e603944881c03041924210048111000040c5140380a520401d00100a5480c003044295002a0030640d501c200c5021102c94540c1c1c0c004d82d044c03515220a5421480e138a400520450101108001c00c6452200c450340c1d02c40b4641b410203602034904d01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 612878534 1250 612877284 612877313
    0xb0a091b0201050603030c070501180302030105071106070c02150922060302011101060f18020903190501051501051e040503070902120108060c04090e030c010c090801060506031e07020307 82
    0x249000c1418080802800e541010700440d109a1040c0100c1403801400700d0342808076003090a261200c0c4000300c024030a8441c140d400650300d0b510b0320080105464010450b910030071a81016508aa80c40310005c2d03c03038203983c03d800383d000340070211601c004440c2c00c4010b00d000301c8006c00411141070300f08111610300e218040c2002a142d101d040030421541c0202c091403107031201400900400307042c00605000460140302e6040b0312800034042c4009600c603603040b2160001c014040d50500301502c0300c040d0101603282c13011034040d0b1070314002410703142200d1104450040c05944080c94080340034014858098202e40c4005040300030007001030540e404104410042202d0007002d601c6032500c0480800b034a20503400084590403440420034030055000441c0d080d14990400080c3c20383d103000c080340c41c600540d401541a5032030801c43c0400d0070303005001c2500312201c80009000c2e13030f038842d01446120700094401d913011958007145400c8003105499107542c4410ba620440f400c1c40125203540c0c080d80c0151 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 612879784 1250 612878534 612878561
    0xb01090b1014030606160501020703020607091202010206070f0908010509060610050c0c1e21010f021c0203040f0803160e0a060203160c090f0b1e010c060b0a09 70
    0xa0380003000c242041031000c0c507069410306004200b010610900162884010855031040b04000f03104010751445801510003103820070021501d070f0741e941c0790180d40c424087d5046400b0803401c2e10f0001c1c0051102c9070300701506a06078081c1210b511684070a44082c1c20503200c00041c054814008108104248501842004030100074821401d00318180044414040c0c035035020000100300c88070054000041800071800141c6140b85070300315296131607241d91070350014190701413050140c1001c054145c070301242c01c4041c200020401c2040c2848004102c0c40780b20020004800980200402c1920a03405140d000c0e02409070b81685030303101d039100904c40e4000c0b0380c02800b003611f000d0100d910faa48aa050700720f240d0300b541c00700301460070154040e40c2c80c05041040300345401c4d8100c028007080191140c020080181004c14040304d1340034888440504901038805d130081030030100054844165100d8500d981e00107844540a680090b19480090300701c070700006400c05015407000030001136070300c282582c64561 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 612881034 1250 612879784 612879791
    0x14010f121e060311240306010302120903030a1a0f010309080403240608060f0408031504050a0204090b03010504081b0307020d06050402100e01020d050a1101021207090f030b0415090b0109 82
    0x4500c0c11014200c58100454024041244516001d11200218400c017105900c0c52645030360b61200124041d1240f42000c0c00302c2c1780c0d0304050000303040c8004069400341c86458000d01c0034a1001014070032490421034610b50081014000c40000c0d4000d50011080c503002d51a098503043c1c9a407180200c20351045038821400d041100342c0c492010061040d040a070041078098001d90806075829695a00044c00240c01d1080c000045500e00054284803030131080d02910511051400782a00c000030f401c28403d8000307803030a080b00611182b5040c4503080c421507000800c1400e02043c0c11004495900c0c811126205100c10004200540d8500f982c000c10181300e280c0110700752400b0701c180500e40f01e08140384414000c0001000c0c0b116038012500000340b10003442c00c0c1e5103c4924003411144540540001c446a500c00544504000200e04005218200c20f403211040701e03a4a0392103416550709444081d00b070a5540020800103030500b001d45c0c8404d80c1c400d0012503180f613544c03510011071034281c4c00809081ea4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 612882284 1250 612881034 612881039
    0x3010501031a0901090506180f15091e1b030a050a06020d0b0d110603090109080c012307050a0309020402040e0a0605120f0709090305191814010f121e06 67
    0x10b08464807a80441004002d0010f04502d1781c9540e620403000e02907004100303921003d041c440200300511800110b8150803243c0000120306404500c640070303215003c1c940100072a1030848003030400c0304030404850030b00600c2c0c0042f0014480070a08031a41f44664075001d410043d501041301004010700e152b0040344010703565101025031104880e510000503011f260400f2a0402085100071203030880b20b8103407081543da9032640c001d5401414100f41c020807094003c1000c0800c4401507010000c03e00d010503440003800701ea1684820200310884070301000031406c000503e86248250400b41500d4401b17040981450303111020200c504a0840d15030502a130742d40300c02c0102c0e00d040150f1542d040300c5100074102000c050000c0f203494a12034010b09a01c41c0d03d6000700e40c1010f00c00c0e01140c130b0005c200c10400c05540e24441005110f86018403d128001d2070026010840c8a0040d01c40406407805850740d80b2403814100701560040007000000507900d60768941c0d003104c0f0211400c0100601c168030b0000072840d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 612883534 1250 612882284 612882323
    0x503070f08210c010c051207030b090115120207120212040518060d020d03081509061305070e150702031501030b240d030e011101050c030a0b0604050301050103 70
    0x980368426140100c05000401c98280702091a8000c042c1d030039400d0012800b19006080d09100384414000340f90b01c2c0c05551084140d1020103010411039404203100c49880d161421070680711040d001c29401820a401080741600c4c4011040300c101403400c0040c650031030000051300300e800c100c0090b661810b030800c810066a906100400c401d0f02c0801699041a042601141c010131100c404843c5920725900418259501d0181c800c0440e40c5c010049030100b4070914000705420b900750388550b10702050065082561800c002c540c0d108520251104007110030441980703000d400c024152900340503101030312070040d40718070224007050540850000d03501c118a10605103040e0035000c4210400d0351100c01800050f502240721030300601c00c5c4c00030010220600c403204890004000c04580c0c00122403040d00d0400d500a4881d40d032414090304e907a03804d44c2e0070541c11800c0c0d034012612925240c01c00c00001d88000046c0d4051100380314007925450900380c072840403c4c05c5031400c2c3c000f6990201d001c2503a10210 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 612884784 1250 612883534 612883543
    0x90c3606031006150c060f0507050903061003031403040204090f0501150906050d110a0b072001080f01061b0b04080408010b01020a1a060d02040903030603030e04020a020a0224030a060503 82
    0x42d00001c001c00181c0c1c82c1100000f80040e03580513010402450008100c140580e607089203146070001e40d020840d40c2407007040a000f0ba0b000031205406030141d5000140d44e00d800403004011030342c01d42c84503042c08104034410ba240e80d20003001264403d548103001004141c10813901c4500314031503c0002040b8031098004810028503500211145003848800c2c042a210130301205d40c2580c2c410890742640300f07490700003a5603500c40d8100c8180d170b480c0404c0d448207200008a014103450302c11041d269281000000446000b4400c4070001c1c2201d201c8801002758030b00c60511003408510900c04818000155503458071020303019035058460703020100b4203100c01003080c0705d10425440240010710344c3d0322199076006c1c030750b030b800d1f01541d00318a1145000440e10b0702c2300500c2c0c9c0a581d6008008024084841c40d024008280601080c0c00050800082c00001d0400340b00b02ca00840180d001400c82d070469170f00f007107120900480362448054100d5041548600001c0203980034920794840401d005081209140c80c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 612886034 1250 612884784 612884803
    0xb13140d0509060309150412090506030c160302070504020f030405070b0412060f060b0d020a0305100f0e0402130e150a022107020a02030d030b0a0e090c360603 70
    0x290040810310560940020480300759490664995440740d944d1a0320314285080300031a15000452a03040204002201c001c001e42c41c0031a440307071000252650f05102503400111a0420030100801c203640f40c0c1c7d03183c50700300100030b403080c4107d40e03001d03840c3c00105080e0b80069a20207095078011060008221051003804090840c50580604041c9043c150322409018500b003d000701c0c0e038800304800c000e08140c0210001d42a1b01c040c5503503070b00c0c0d02143d840081d446586410f0000703180202042e25a0350540480f8200c41003040309500d100d0405101c244c440c80302030412603016071010750143c500f1440d80980a000d09840d0003610141c191074400b041d50700c07401844542501c2c81003004c901004c01844480d201f0a00c4941075000d60765640c075050385400c21107240a5854811401d0505403030b5450303005040060b6040d20617141d61903072085210a503d00a03112141e480d0000c160700d05050402d003145440039121045811048895581041241c07085840000210400c05c010003409040c100840b016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 612887284 1250 612886034 612886073
    0x12010f02040b13170c13200c06130c050609010201020706060306050f070804050706031806110c12041230230702090c2b0204050a06020303070522030b13 67
    0x1954445813000b580c807070070082c0e0514030a03a246180f414806465134026040160103443e8410860b41001440c01c56420030015902030380b00b0280020308081d0303a00c0e010002554170101d00d00c40e0505217010000da82d08005461811036600b40016004256507000c0c01c1c00441c06048001907500f085e241c40200c0103c0200950700348001384040c080002d100041980442c0c0c02860006011000c04c0c0c03110f02e4110214002510340c0f410001c0151205203c54001c040342c0141000b1507505109105005240f070103140300324680e1422000d0098080384c111346c0000910341c00c00c0c00c0c0105a40c1640b4251100c9503400da031800006d14200d41800c06014402d118084007142c041e11242452001e0f03000820320b003002007103003580220202e90b00038110036009a0007a0885003600d200e2b100703003203221030740003d40191003203510950f285040041c82d140048110b03802503160b940d0341d80c0740c40c0c51201500c1c0c190001140340c10850402c203c000021400c2054000d0190840400414800c003950a00307071a0030125000c182c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 612888534 1250 612887284 612887309
    0xa090606080903180609010509041d01200706020c010e07080105010905060603013519171201090207020a15020109030e0a150e030c04141614040512010f02040b13 71
    0x882502d4036010002c15000c08817611659400c0d01801220301c3d00030300e60180e411a050040c050700300300607141c005001191140080124445401c5c145081a0306800c12062040c0c0401c51000491100d4008040362150ba41c00030550580401c801803900600b9030080c400e50755981d00511410500c0c4c050907400c15011901581194101050b820850708180c40c0c1ca0002d070f501a40f10001805946411038118136404d040d03a44400214521600d0130315144402c5072542103905550f00d4040031541a40d4000b040302404030080e03820075954200961000d48207070b070b002910100015060780d2403200c80c1e413008100c2d0300224661000e031030b02522110300c2d41c90076072140e082428181701c00c0c043c0304401d040184031403501469600c2c022011074102407140340700c907030450309100d03820584903844080c4034018140c0d04407036843c500350103e0445d11004402e102c0100b40c00c007007000304103a1402040f0002c0103080e5100001c0d03101c80c0c4d00e803038204a0f4015408010345a03000b1452441c051303010101c0500800410300102c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 612889784 1250 612888534 612888547
    0x1c0306091505010c030210150303090e070219080c010218091b19120c05040314070501080105271609080c06160f06050112062a0809010b0a090606080903 67
    0x91a0310070180c0202c40c10000301201c140281482000380f800d110129420404c280b04890384080307200c2c1070a0009030b02141a20310005851254104a540316070a0340d4003426010895400d580004450041e00752624201070010110340c80c001e200402e10303c500c2c180400742c61441801803044c00140200095018080d42e11042d1090045400711840d0811910041e02107024040061715007204529405040e14030b0280d0000c2c0c0b40c0e402100500070b80380545044902100ca03404801d44e205442d01503540007a00003001080142030144044101482081c1e0044c030b4035121200058040da0200c2da0614900310a4140e10425500f04036400082c0ca07003080642203444d524804102c0b1886404816050350103207294660a000310300d00403003101c50348007000b40480c0d65648a5181481440c040654600345000c6005000e00104e600708101c83c2c0181da640006211045e0041d00c0c5800e00800b056a10354030340c0a030f0f183e6540d4200070310300641805c5100240d01420304d48011705000000f000860740da4820440b8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 612891034 1250 612889784 612889811
    0x90108070c050718060b04030c06081b2505100506090604060305030f13050d05100b0906030a110418030503250c11040906021611010207270b031c030609 67
    0x10541904d0551980c02c0d62082240082c4004080c260320070850464040380200030000340c8036486080703480d19035070010749460b100e08041120007805050b12411904110048128000146c210510495400402803444003a21028100300d100410701c0e00340c41d500e00c02c100c40c2c0d107002c02009400c40030030b5804101150956488030b9a0340300704005d21103000000f003660b004403550854040e0142034040c0c1142804e88a40c5440c3d5911035450541a00050810350158040c0c02c01e10700e064402c03603000380100700100390382e1204400c02305a1203840780c006440e401007000c0050423184443c8014803036034515580b46007542d60b8a00c41d0501d001d010131032840040d01c4011b00d0781e100410f07011b0385420401c3c00e5080c1c00703600b0001e4020800c0c514020040340c0042944144105207500401015000d0751011a00145000049888140902940148040500c03040d20841603074500d01309180c100d08400175050040d4400a441d01c0c003600045404440d0703802648500c294035001d0329004140b004428805180d0507880f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 612892284 1250 612891034 612891043
    0x1109030d0824120d02150a1808070213060609031e020d300305070e0901060909020d0f020705010c1803030c02122d0c0919111e090108070c05 62
    0xc0c0000501e03140b44403103a80e641c08004111040c94011512140424080a0f4842050401c1e8180007800c1600188030313452640100300580c0f060116050704214aa40d644202d0b800c0304000f030303030403403c2110218030350001e900c988409013501d610b038601d02c0c2c1d2444c40c08400c8081e854000300c0154a144405000613101c1c05003141091768041c02e00c000155154904420300880001c442e03e07800d1841201d001c200c0d4055202c10b000306443c0e50b64030320044803641130218029080c400e40c00020120602000340409a5025200c11091201f000c50380c024824014816a041001e060307032030740d555a108000c07090700650442c000d0100481366420039481c54502030300742c56041c427010380100d0070030360075400180c000e008601c042c3c040c804071000f803858620074820841c0841c0480640a100d810442045450b162403014840e60151006404603110a41c0c0d02c805404454903e0340300c43c80500c550101d0b080d0705903642680003900d0144a80351080e2100040a444c4060692400d000351112904e001c1500400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 612893534 1250 612892284 612892321
    0xf010f0b190e0c090d15060f060314180c0306040818090903030f041112060a0609140411040902061b01150608040f050c06070501050108010c0912030809070302041109030d08 76
    0xa004a4440d04c0c2c800114000c06040e031402810007002500042c00401a0f500c5071059130745e0010300c508080d4854205600b1618050081403582440c00c0004400c5004110403411840e48a025100c0c5200c0c9880460728200c0150b034211240500402c10080502c2e000e1080c0d10040c500b100c0c2c500d807906094100c9a228400a80030100b0307941c134080080d0034130a03401c106242844000c0c10034003501c0401c0304426264103094820650300d90800c60005581d15007800384450905803003800e12401d40fa0703a6605003401b9200c003101904a502c03142d4481c05a501c02c1e01805444024014000c06504030502060848401d000000300400000301c1c103101007540700304801d81c401d41c0300c241c510f1040f07018103000345850100b40e2900da201800291400c00c10078103410003812a0300c034100a0000010804050b100030116016122030052441160000319101d1142544c0100400702541c140303035200e8000c01e0076201d039103203e4840100006002c4d81c0c42d040c10485031415152901d042120383c20074948083d02d130065103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 612894784 1250 612893534 612893551
    0x90301051e070f05120c0909091b1201111303050106093c060602030703092306070305040503100b0f010f1e1101090b1e0c040e090f010f0b190e 63
    0x110fa10f00b2624040d0080343d10b91054076400c0c0c0d00c140361070100342d100b613070007400518042d40c01c04000c60000071700000c40103443c0b120380d062140c0e04440003040c40a258010305000e10300e0340d202c044a0610710103400050882c00181300884440c1421801c0c641c0c01c2d5105640b02c0309029240003180603140b034a118541103d43d405600c0700418a0240c440280001000403124038124646440003d40b42e40000c01060344601c203884c0d050089a071090030810340034400f4161010003032802d00d000c4140c034068009080751442410400c0c2007030b4546000c2450501450307a0240c09541e20040f141040ca0601c81100a001c0c0134684030a5921050760300a01012540b0303802c46040d0316000350504098022480d806a030050400204401c80081c2041c0c03920741d00941d44d034110380c000e0710250035a42c6c4804501d40d2040040d203641c00e00d03003841c1c407402590403c4010062892809216a0104800320a000703108583c00e4440000c60369100090401c0030081c8103500f40450b800e80310400b0068140c0c0350ac2181d51100b0b14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 612896034 1250 612894784 612894797
    0xa030209031509010204090e06060303040614070b010807030212010b0a0b0c01091a0105180705220b12010311011d09061507080c1203220201090f060302090301051e07 73
    0x1850082803400c800a44100d40d20750500d003c1100f4008154040c00440e17600302014811018400155500c5010940d0300c1d0b501a0030820051003134138002c0804034074500500f050b0724603143c080d489403242920b082c0c01c4201c1c103400412003001940b410310440514a10041c00800003050385100091002c0442e20038000b00340000b003070040d45142c1c00e620031100c0c2500034100d1101e00c1041c0c0e00d61521007109000340c92048030001410b0891442c070869034ed2240c805038481a203851942602d50703802e050b01c03241c4158001001180824034042d0103015280c4030881c4044100c3c6075055180003159038150520f80d0b410840e800030481400d5104400003040600c094494408075110180420180303082591280b5006000040e000200000030f001040341440d10010b807501000445040c0355280320950307019000d068200c040260f59026070301d0401e0403070b2050500401181d5910740a0f4409100c0e0307800381700842d5011807804058102806a550301150307a0405000160940a0107010408007030003075800c1102 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 612897284 1250 612896034 612896047
    0x31212040f020316060e120d0503041b030c03060218010216090f06050a080312220204022a070e01080d08070f03020405060f03041208040c06030e15090d0f020a080a0302 74
    0x302480740d02d05840500401c0c441817915000b010300400041320749107000b0100d43c01650003078100420b0824203440583d48407407642e101d940300d50851080040d072551015202000010025180d070720740f80f005610403840940c89540b00042c0000c1d002c0b8588030581035412074007505c0c0040344440d500c041a142121000a40c10384240408001040703160012904032964581c045040d40d00000030303110300a10b5202a030b00503580c0da101010440001c2d44c2c0031000c3c1c0c410550020051401d90041c0103003c4501101e20020840d07038001a1a05401c0c24a510380c5410921040c0407260000007894050f100120083c10194022040280750041c001c102c10100010030341d000c040b0a200750100c3e001400d0040c11640c40d10000b8000903681c2d44140d0f800ca4107003e04498002c410760085844d603200d640c00580120205e46041000c1e4098403400c080030aa50080120700170701083c050200c40d0148000c82d008000d172892000c0081e0100c1c2d14641d00100b9035200618400000341c50790119040114149005a00d400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 612898534 1250 612897284 612897289
    0xe01140c131e1701110a051c06261b01050309070b07060510080a11060a120906020901020f1902240d0e06010906060503061c08030108010b031212040f02 67
    0x310305400c2000d4070b0401500101d146800e00500009907006050001c01e00050500b810342202c0e061401d006603064180320b81005103008001818150a503449400448d03c03141d0340c0d6408030340391a04074140d10740a080d4580760300040c0700310520301e190b01d41008040b80359040b99400c095001024032541040800000521240f400344840c0004020820045403100e1503440c2c00c0004e020111194a0406400c40f000264a0310004244281701c0c1c01455009000c884041880141e0340240303182824051250141d0b0300c844240d00c01c52080d40d0061800588415115000906010500b003000c04c50764400c3c2ca19522084488580c0040341e030707045820408c22607c40c000400b074608000b1a5400301c44020400d0a1000c0c0150024a850b039101d60980308640c0c0c907610b60004661080c0140c82c0081e4091000914034200600c02c000c4445242c603110766038501c1540d40000a82c0b00341c110602a9445810f00c506a040400035044912070922101742010380c25103481900c080010300140000c0108a244000c2d074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 612899784 1250 612898534 612898567
    0xc090103150209060a030203090d03060b09010c11060f130b03060a12030309140a0201080106020d200705150a020712021309030e04020315120706140a11060709090e01140c 75
    0xf0300500700c07940b19040a00c1c064025081250300884c1c3e4060041c40e943d240e03110384900801d032161404401d00f45540a03004550281e0300d01d90480300204641500c6416659000243c0b2070074540c8500700d65544210380980b5140c042d9548001714949080c03050004941c0e0740c0b880b0711300361a000814008204018241203000d03250040b40640030700d84000481d056080003080c2c1c3c0c00c00a0003030702d440c009640e80c1c0c102240d44440529004002075040707014400d11017540f100440c020410002100c05050300d450002e0250041504003890030140041c202c00c249406000c00b4005004c001d2003529120b5217500410340c001750854588560607a03503041c0314209402044a01c50010024000f15100d2800100d07001c800d203441102a8481d174006144a821a08001007900c103403211350362800c0c2410301108420302c60341c020307012240900200c82100b0f8012481000114400c040903035601120074980b05011044540405580500380d05144071651107426071000f81d40c014801e00c40c6103542d80c03940045072481 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 612901034 1250 612899784 612899797
    0x1e06051e071209050907022a030c120f0601060903110607022e02150907061808030703120c030b0315130c180c09060206070c0c171e0c0901031502 64
    0x11500040b09452801c2c1d071288004003a03403001c0d00c484410f0307280e00d4016a910007041d51100228216452052500c0468401210304001d01504a440d1107010074005206c400d02c1001850b0305500252404529050400125004140c14181010050700f10b4540301d109100c10b80300386004038000200441103440742d4035030440490701c1d8404a07803c08001c02080020100c141c0e4a440107204881550b82806160b0603014001c000e46002090301c149040c6c420342304074404130507030b908444d81c0e80300000f0302c10424001024218801ea482000611000c0d0440003144c0c6007441e00d0042604e440240d043c5610b0000b8002080130003083d4214113030f40d8102c040408405006801010074001100015844c0488251940c80c0c403441d04051107103400c0c4400c103d0360b8481b144140f00050b4004804030340c80d9805940c0140206018440c1d039a1480d84914402c001030859694099541e44400d14014140c80d0f40c13501c0a90055200000e0008030760143c000400c0100c2c18080a0050050350039003c0c02480c007541103030708 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 612902284 1250 612901034 612901043
    0x6031b0307090f0f0506030a0b0d140102030601030513080d1e0c020c040b09040b01030308250e090703110d050a09050d050414040605090a0e01091403041e06051e07 72
    0x240d034a405680244401c4252041400d081c462410200b081c45485544e0429204003a026a045940b4404804d014086048a10b5042454a418040410b25581e0440c0380e0404c000009692420130341c0005088500040c501c0903602d084146d0700b0002690758040310b0301548519800f061401c0c44050840c038000c4092008942c8603d821841c030707429600270074070919000089404201740380c400303030a129500720b00b150003d1402d01c8000041c17000902540d0f060360004950514100000c0b40035031051f50b40b05510741c00384049641c0e001c0b1001146814096a40e00150f41d00d024042039103003145143d050b020310859032600d19101c80000390780f40300035409245a260098201e40c0841c00150003d881640103006003046d002403014034034002d00381805403204452019107807580e0f81c0c0d1060149001040711115000c1c480d5215441903002c2000d2502c8101d480c50078101442d52280b0301025030003d51141c400c84c120200c3e4405c4200200c076080415551051030003803580d40c0848505840c01400d2140440080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 612903534 1250 612902284 612902287
    0xc020106170d09090b030d0809100504080c0607020f0c040e10111b011404031407050a0c060210050405150403050408010f0906060e060a061d0d0503090901060c0b010506031b 76
    0x90015000070002d00c410802d840c3c1118081e10f5070b180f40143c400410485806034803503e00c0240300e900c2032480a500c01d81d03034016165410031a40c2c4000940700c0c00e60701981c82002c003089110000c4c0b000e07c440380c1c2011050004080c04a0041c1d500c5444440c1c2c0501c141c800d50743e910036500c294100344141c2c444044001020003030900c80e05100b80c512740001008807021402a030f241d0400d40710500c21022092981d007002d505a9403035030b500715078804a0681c00a80701c5010721108002540c10840c4a446911031420342c071a050421000a1403c401c0c003043c0b20309541420284008141d02150b1001840003620020090741e0740d071309042d2864492640b01494562a0102e290042d031111381c0040c0c0ca007482003c050000325650251304004070010b5a4865121540300700c01c119007400b80702801c4544c0c082c540103600140c180400100b2a41004400340d4103a000000c0c07100c240d103050301071607000d418241000741c401176180e10313002121241406114019800040828480550507086100e500003100c1d145 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 612904784 1250 612903534 612903569
    0x5040b0309011a010f12022503120c03110301050d17030906090606040911100e060c011e1512080412050d140f1804020d090b10060f050d0c020106 64
    0x1600800350703560120a2030300d032116611004c1d840b41c403c22042c000715a036190303d4040650500340096100220b090000c4c0000600b002d0b50a100c40d03e1000014006e849902400d0b010310300319016a0b4881410350100342c60003262452801d140819241529003e941d0314144900e6483d11036142c0001c000d0b040d00e6440040b0030820168000a25039100d950b007e8195485070303c83c1c83c140b000b611a20080141040111900b429850410303402d0107648a0852400c10158032480c0d0200d041d030b610840540000da5150321590043c0700040c100905e580d83e500360100119182150301c100c1c1205076008440018403542d0000b13050000d108181e8016101c0c0f4000e60601000d503280466903040301400c900d004c56480780141030550101019200483c001c0780e0214544070a446038250ba10103001c0041d988554203016440021500780301d0014000c1c802c5d00d601207942450902140050030325848641000314800d0000c0b4440e51142c155040710123100004074803030502110a901410240e0000d1001c80d2089801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 612906034 1250 612904784 612904801
    0x90e061813170909070c05331e0718030203011a090702011a010c0f122601050102030d1812080a06050420210a020901091d0a0b0105040b03 61
    0x10030032052184011a40d07115242805404030702540083d56484070440000074080c0f8001c4a4030382d03450b40302d50280d4109008046e10301c5208010b541d6401034040da0025800760720000b00c000e07141c1100305203820044100040b0700e201c07403802c0c000b0140300812401d0404032503c21900d480841c05564010001c1c81140c2803105540928025070017403074820341c50140070800a40c01803244445621524400741088910b2500544e22030f440721004440000509040d48041042c1251040c042e490650324050006034000481c8009403542601c03440011b08407004014981e00041164030344030065801160b10741144001102200000e403014101c0104d15883d81e42c1241d210341d115104500c4840d00304a203a071290107120803030301c554107080303202e000300c1c41030148120a210151a07d5000c00c1c5c640200703004c1c04514503400040a480301e091864022801410b20340e00845c100c0041c03e030444500c01340720044916000390303040c00f03000c64a010365130742e051101030392007402168003800180e1449607aa050900383c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 612907284 1250 612906034 612906061
    0x11e030b030f0f2a0f060903030903010e0609070803040609050103110409151703120123210105010b0a0807030b03190b060f010c0302060f0601030618020703090605030601090e0618 79
    0x55041c21008a00043c55134002000a0340020b07190103000c030408040c0c04028172180d50b00c0200b48550501c41446840201e41c1c007400b454003602240d03000341009041000403546400c00035000412240c1040c0001d10007194800c0c0d0a078100d400034030740070603800103891203400300e03205a41007090400d05007101c452142c2900c24402088800214244541145801d5045e48078001c1c4010802034458003001003110062040c2201c8032015130b1054901e5441800700042e1a074401048101116076084040492200d028072400e4010300c2130140c468503040900b1402411600b0003040181070580e0391140c4019520308112001260380407a0010400d92240d040184680b04203c03480c1c1c1c4620a4840c00810399445036540d1045164981c0060415480709054a10b003142c005000e00e042541e5400c000034065040707812040b03809250840165140d4850800070a1142140c100c1070a03c002041400741c3da0344d010b681d020880e000c0e003074a2040da440c0c440c00507005100c09208600d44400e642d0610529158401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 612908534 1250 612907284 612907303
    0x30e1f0915090503221839120f0c0207091b0e011803060204060e120102070c050d0f0b1602010b120715180b0405011806080604020711120601090b011e030b030f0f 71
    0x100c280b078a0f43d820303440f0700250203410403143c140450080f481024020b10b448e2605842e9200e011a44401580c0d0040c221024003c100d00185d2040c0c03020020200c4511440702d44100c4841d6082030318600c01c00191064000c04001410403195a10f0091102403009030f82d00a036034000d0040d582c0390b40e0754000501103160208060b2280d10140c3d0840140c280500c02c49144c02c1d8861040c0e070035946000f08103c03860070014000d41c1c100d0304403181200021540d0304a581f2400e480b8407802c0d512080c841000b400c485110710614010208031001050041c030005080c0c044501c02d0a400c03901c00d140c07503c102c5118501c08100ea044290035080480c000d001c0c00702803c10b5600a0380c5036a03244000141c0003980340200c1c855540428542008162141416001000c80a004064002c8004842d9000c140d1031a840b440400700c1d5005140140040e04207070103019115403003480d241d84058269007548028908604e282c07402c0c59511001013403980c4007402255006001002a541034102d42240243c0710300031007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 612909784 1250 612908534 612908561
    0xa03030305090d05190c14070323030307090509130209010b0d050c1303120516030c23191a040302011a0103050103080901030e1f09150905032218 64
    0x40c0c02203501489041610324000240c0441d00c5a00c5c8152015204203008510940d1465810306003c01503000401c00d8600942c4114581c25034441c09035800d00c0844980c41d48040250010010301c074090b0790102e0210107607042241d640711680c46180a00d4400303518010020b41000500300001410b0350100f004d00b41c50100d019050080b80d8880980001c40d200d141051a240360f403040060005c601444500280100350b81040b529000005840844002000004500140440241c40100016042c940c002a00c00e051440c1203400008905522102503008a0000c549103240c040e06000d440758440003020141508917000b42064203001340a096080841c092250103998521141c5d4464411107048033740001203141004040c00044002d8130700100303100780328441d003076100c0d00700c4a405408040b1040340322000500c1443da46800f40016034208485102c00380f4044520f0007250011040302c40c1103800e00700140a403209000a1405107081b60045001c0c0760204c040180c000d582a030103201d011400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 612911034 1250 612909784 612909793
    0x3090906030a2102211c0b0319260304031803080301060c11030f0d020c06030c03061302070f060b190b04092706060302010f180e04110a0303030509 65
    0x38001810356402d9849402042e000d68003480c42444481001600004607443c8140e8145e0101c0344a880f640e40406245044442c6002440365444070f60f1543c2a4a042150300c01841004200780c00241c03110b510901d050313491181d40301d0040420100c000d0680498012024443c010038031502120381c1900700304e404030f0109030036030140030555444640c0c3c3c1c000c482e80210380c28031707682c01c01c0000c13902a0b610901c100d0345503003242d40c03502040c3d0f401c1c0074039029141e07a100140b80c40f20524400130300e030a501c1c2d1007850240d2010018048000240d00480341c0c880026185a040f0b5a40c40d0040d4001784250345c0080c05400b288540d01d0700f0170540c2d4000c200c0c1007404891000945e0540c2c1030802d0641101c1c82940002c1004100130080054903410032088440003c2d4500c1204205110f6000d58202c000c2e422a40903a0b0b0715030038030456800000380c0401140a10381030182c850050480c16081312907000703c0e2055800c400006040200c00304d14084e040030701601941d0741d1960b034580580941402d0718883e009006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 612912284 1250 612911034 612911041
    0x7080417010207020f1c0b090f211b030c10020d060b12040303051308121e0709030b151f0201051f0905061804030e01090911031f05030f030909 63
    0x405000f0303248510380092076031030750f81e540c07038200824451203010544500c40500380b2800441c1e11009201e03c0f80300190041c024240141611134100804400072410b00100e025507149844a00029500c00320a04850174000392940103c5620358019140c0524251007199080004070f50650081c0500d000030000c144202d5481d11840e60940c0900c8080d5030514040b4070004001c00e01c41c0c6c00907500a07040c2c01e00e00c1d28404140d200d20000e42e00200c06400868100c106119450303c3c1680f503400905d403900522400c50506000c01000d45903103101c0905610780b40741c0841e02410341c42c001801940001002710034141110b003102005003442d0703056100954604400078035419545035541002c0d0b1210002200801d081c1140719000f048041c12560304001c2d00641c400100255a610034000c1e0702a0700e42000c4894a0400102405481e42110072002c2c100120034900c2c3c2d00040589030002d0540c00e0f038845014010165480d2880c081c1c1c44994140318203100810406800b2000f803000400030750b54200d880e0b5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 612913534 1250 612912284 612912329
    0x6060e0d0308070315080d1706010206060d030f0e060a0c0212030a0c020904050c090f0108062203050c0a0c1401090e09030318032205030c03070602190204020906070804 74
    0x3040c2990140c0400c0221000540103403180d40001e4544203942c803103109154860705030034503000000b600e04011400702401b4048441120f5221076014100344000d00c11441d16001190405001800080c2800380a00c0200b83c0c242c090b030b041029000010317001c03d84485d0b00c590000c0100c81140e40c103a024145101c2d400c44060808070454000d5000e030b482d6541028060350034032104d400002c00c02d40b0790380207846111800d559200109401441110f020000c42d5050000090404901400354100030210380c060100070300402c4040c0080c01d4050401c50345485e07202944034280303c50541c0c0100040e4111201240c44e00466640002000382aa20740c02e132592240c03480e100c3c1000548a042182d8030500010382c1070403550b1200c0307500c4200c031070a41c0d01340b13406040d403201129192543c5c4010b480403d502800079040c1004800341c101000c0f0300030501c6d00e28140010f52141c0c0302c40448014640000000f10a5444d66012140a04005070501ea41d40816040541050700b081c0078100d041d4022098168461 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 612914784 1250 612913534 612913549
    0x1110606010906230433020a0807060e1006170307080d0216080301090501090e030315010e0d0b0c04050f06070507061206051012240b070807080d06060e 67
    0x2000e06071100e010190070840300b40d071403504404400304624010081d10020091400180c4000c0c510100403440c10400e9080a08000c049000d0305e5075460078000d6005031040d07001507000314954210308a0740d40c0b0351041c10000054541440092804e1280304405032005646500c520116415448084040e01101c1a5151a8881d20030040c11003130342803015050703940036a8020444118524030800a4112940c3c4001082d00b0983c090442c0d5543c0d08010004d910300d500482c9040780d0ba40001c0d514520b80307031041001001c0700d003184904104001c80e8904a5890301100440d250341c004004040d10701e80743c01b2140181e40030307016940c09032018002c2c1410904001044e00c2640c1e030310030050010a400c0c00da0440d01011181c90658945803600d000149503111605040345801c4036640e0714400885031240031082d58082114280780e880441028015810b1440080083d51180146070303a40790060b04000815014000c4040c00703042c0002a056030405440e44010304807841a103818448400020410400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 612916034 1250 612914784 612914791
    0x13f0c0e091621021204121803030c0b0603030d0905011b020601082802060d050a060b160b06030f0d08010e0a05100b03060102010603140d03051006020a0807080702030d0e011106 78
    0x8525403201102d04208443e60321a10510103202c01400d003115802210070b404415601590266403003030503c40c0c02a4054154030007000104c22846c0c1880ca56540100740f15880f44000e01f66010690104442c1d60307041c422a542400d9201040c028060130741806c0d4002c288002070075100f0710342603528403009400855098100d56908018080e003010312061400e42985800080e12100d070304003641e04c010f0745d0361006002d8150581e24005500e2600e1111a0211807094004a40b208010300082d0406030000351428a00b5501161518082c1c40c0c46020030303d061a43d55a600b00b9004501c101040d0075409000d181c100e441c0a1110141c54542150f40700885900769030600344156611000c1c172071521800000c64000d4410301c000a4929540e49603608002e40121014800c0c6e007006c10784803c91581030081c1500640e042c80108605480c01d400607684014002004215070b00c0071800303109006c0300c0003c0c1c400303e40d005029915000c000400060066218880c250701080b80840e011058200000d01a80b1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 612917284 1250 612916034 612916037
    0x1090611090307150f080714040e0403081312050705031c0b03060f150f03030d0507080117071805061908071802191b060e060103060605013f0c0e0916 66
    0x80170a0408121020f0300b008104c1c009112205d5443c19440845030000c1c001003c0d600b200724040e0500d4a8010150b140182011032025210440840490b2803500c101019041c5c50520360b680d134510b86000703421402108003039540c0300c18030150612160000c2d04000c0b10110200d00351016a0b69070b514640c00c00ea0b0a69180d161030091341403640481c2094140540740d080001c0880e8140b1406003400e00c10344508541e1000010500c1c00100440c049510100c1140500304c0301038904079041940e160050045480a0000d00e2f03120f4020510540b07036100e03d4031108540c190490107464903247c00954a969601c00c500504442200f1790b80030b40114403c2d28024442c0d02c540302180307a0761301001c849072145c21008140565a409600002850a10400100e2070411001c2e220f2980745082c030700115045a1f015038140400303d00c440c9a506451700c08200b00c41c8036a80500d01c5c0055800d1604c9021402d811020a9245490009500650880f06144039008100d4440d2403969482c501d250382d51130010003110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 612918534 1250 612917284 612917297
    0x90201030608070b04091109030307030f020c220f09052407050906120910061d0604060602100e03040306060602011401050a060903031b0f03091e0b03040807050109061109030715 78
    0x10b1b0001941181c40f0071061030880a041449281c00a411584101411400308a0045075542c2654042c8641800810115490030f82003c01f11484805410040c01c0c030740b40607070f0303c224024800119030721800c2101e411104480c04442e00300520085000c40c4507802c2c0040d001800040c10142c4208201e0f94043c0001d0401070415401d9500b5000e80d440180400c1402d000352040e5030300010b29032181c00024040e56180c05040401c90308101000b000150195000c3d41c149041400210340004050142d540551400903401c0510100a0300b035008a81005101c41c5c10071500050b0590705405c00e0500d07801d80c0c94026041c1c0d984008100704140d0030312600340411a000d80c00c0010030f0040104c1500540b409840c240301c28201d5031504218082040103c0100300900d1050000d8084100480300d44200c41c40740e10170a50400d07813018107600004000a050f1100000d44008014081d0000b064595200109201075160318080d075419030003107251035010384034034100002d00e1180c5241c0c103a1815000c0d260711 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 612919784 1250 612918534 612918539
    0xb0901030c031b0e0c0711060c0303040201081003020d0303020307020607032a03020c0f030703020d020105041a0604090c08071d040b0103060e0f1f180209160e030f01090201030608070b04 82
    0x1c1e146901e0f41070481e002035056080004494642c11509841040c0000d805603440007189000c54551030507140940c0142000c1c8114680507500200310307a0070540908001ca440d0b034480c0851040004c207504002e4000703152290003400c25825401450013540182c080e60003554808900703c0417900340c0c5050411800d40d4001d244c0300d0501480d8444841d071007919000d0f250a000ca00c0c2c55140401c100e04044190b031000840005155050180d200c1840d214402480305086c16110300d881c064110250005071004040440c2555560350b0000e45096441515a101c042d501d02d051510340403103119990720302c040a07031218443c420b4a24030310301c52640715011109503425600d60381c0042014400312812880f42062500803d5400c0100c100c9d85c00c403c800b1010890506001035042d80c00300780310b61800895a405103030043e0764006429a1200c5404004c0000311f1036900c0840d00000c0c02c28800d909070040c0d200320000c0c103106412032a20075000b80c800f03000642e62030f0101e42c0d42e071100348a880702003203007071106 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 612921034 1250 612919784 612919793
    0x60103140613020f040302030a05070e01051f030203070521010f0801092a0b16020f3102040f030c080f0c03070311010203070204060e04170406120209120319030b0901030c03 76
    0x1800314450520540c40c02c00e030b01d0703a000c2450880589d5040c4c03000d500100c401c0007540241e8060601500050701d82e410282d0440300c2e082000c8101254950034980c0200026200900c20016900c948107a40455011075050b0f58031000505000c0c010880712808c20b2001044074101401540d48040e03011a2a2413952030175050f100d800078240c0300b10500c44020f60320004020072848042c0550f21551842d1800010b0944100303c2d510f82c8040d46240528038082c0c54201c83c0c1500c6030000150208030701c01c4070210000300650710081c45250410000381d440203e01201740042d14000d02c0a8444d030004581d00103003041006541c90404030945503065202ca01c0a00c00146290031100b074400d4107004580c14600951b0000b8207072502500191201c940400410080c0019100d03661500740800b0100d038981410402c0042901c03840c20b901080c05074000032208480c0d11000304a094850851080c2d80d00d5044502c0050509050400321600080c1040d0301d107929440d020100c14101d03903200b10b14884491641d0340303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 612922284 1250 612921034 612921037
    0x1a0a080105093403050d03061e090903110f0f0c06070b060111010f0515011205061509030a080f0a080f090705040914010606030c120b060d0e030d110306010314061302 73
    0x10f02a80e1802c41c818050a40c50080c00019510890280c1111902d9910040480d219a8058100304c1010131000c00b050441d0030015040e112440000301e0b80e000e03d03040956080004542d015094881c18403911400300707000c10500e00380703100803059821820104081140300c0c02030f100c3c0074041042400204241d9030040780030907441e00b0100d0002c1b4200584003081d0341111412106082d01c280080b2031541c00f03691106400040014080041100d4141200490b50304110044141010000012130458544c0c041040500d40750740304594076a100324002c0b2854613074102407800b0021a41361800300f031011403100b86881c45034402c04001c00030720f4a030200300400b404010105640d52841c2c2c041c1c91070201428041d101c0900308940300491a540c04010050a2901c03a08001800a182c100305c45000e603900d408a9000440016020070742c10320311010742c3c0c00c0d41700b87d100158005240859002104503044007452107084262003c00164450b5038003000103020880c0d104e5070095402c1c0700c250303040c80e0039030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 612923534 1250 612922284 612922333
    0x19170c15030c1606090b19050f0c0a1205010305070e090703031b02130c1e02151b04080307030801081504031e1e0309060501050607020a0312050d1a0a08010509 70
    0x34000443c425240c0000b151504107081d10350350740101c20042e00c1c0440d00c4811507106c01c032110030451403424645041110130042c1616400306000528031010300c0c072a4590403115003a1070010070a82d41e4a01c1d0035503030f0380590b00c03441c1d40b440d104c24000340c40614049041d1003141d8041d01e4089242148034103003052000a0b000899000b1070184098690a020b1b12801c41d0201240e00c0b0b0907c8500100d00341d408819205d00340104540c8402119903064402202058101c5074100030a01d51101c441080f015a00a0360030000d41e034407000c00c03180d0505038407200c11030403180030500b580c4101020b8444d81483d070000300d5000d400b0648603030010034403201100f401c1c02c1610b4246026100200000b0030701e420b03580058142e400013a11030702418207114061090500401d4100ca10b0b83c80d1013850b5000c980305029920001c0c151a12450408107002c2c010001c40e2003d000307450781005100345d40044000911119404c245c000c0d03a40c1c103404642e60205218941c0140224801805503c801c13045080d040310a46 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 612924784 1250 612923534 612923557
    0x605090315060a0b160308060321070f080a050a180b040605090406030c0816050d17030a060b1b01051303090b070501110a0504030516030c0303030b19170c15030c 71
    0x10703c00080c180300284080e0a0b8504000010444003409060041540d40064950751080d0001c450f5030140b002c3c080603d007003641c51a4036403500c40c10305003885502009441c0014004140008110101079481001040342007250b031240940c00b0a41007a403011900940500c10301524100428068a400780004d018148002400860b00c0364032135880024903050b42d4054422907003d50700401c25900d4040407500a0308007904e28102030901902e65201d05203210780000c100240c0000414002041d43d00003401400b20110756940d9504460f251400c05444816421220351800340481c20303c0354030081e45084640c2540c0c0302e400407820220703102c909500c1038908849541d44da910f003807490150b0b80050880e69aa5440b503603216032550809600f8480d00d21080e44000382d080c68203100050300311034947c00b540d4240c5000520304601c840828900c1e04c44100b41050b044a40303070000740d24500e065a40780d07003c100318103503014400c41d141800101040091406070240c402c3c00000c8441070705401514250508 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 612926034 1250 612924784 612924799
    0x60c09040e010e0d030f020f1902070e010303020a1202030307081b040306060b04031103060708130f0212160b090d1713140a0e0606090d031809060f060509031506 71
    0xc0d4a40340d421034100b0f1445925607008030140041e000d816210300c0448900042d01075180a0340d00d0076200307841c030590320504020880b800e02c1425807031080202101500c0341d040c405250b0350712814041c1d80c4a00302c1c10201c8540030001da030070800d40c0c40441070300c0c01128030b91204002600c600c0800000015820340258031018144000800300c1c01c54051030740140b80010040b90b0719411070526008c0b10f00c1600c010760280d0301038000d20000d1540001c075540d0140007840461001f50a80c03400d01860700442d02c02a502c00c9110040c1f84c5c0e6281701041c02452040ca08018880d001d0f5104a01c6050380900c2e900b0651291b007191412000c101c216a4401082058400705d41c9080b8110135402000c032004d070003043c3c0c5845c4401152905041c1340c501c01d1701900e002040c4051078501000040c003076100380b403a000d000b400c1c10003032101018060b51943c04000203040c40b10700200d40340c070103000c000c11544c031600c0500401c0100c0003036802d00650072590208000707009041078203108450302028540150013580c10403032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 612927284 1250 612926034 612926051
    0x271e0515040815092802120304120b090a0212100b030d170903040e0103030c2006030408070c09020a03021e0705032a010f23060604051c050d0c0c0b0c060c0904 70
    0x40c1c4500b17000040480b84204a501c5090b4010b10a0412000c1ca1240156204000a11900c0031401d079000c40a6409401c5810650b07a07418500e0922098410080d0400aa01e444841d94040810101c1e5042100c0c4410000d401c0314904040e69811007221410124514a2510b404290b18002d5140e1004500b411245001e070f5a100d9108105000d030310580025010a01440420030340810941900c4030284000d030180ca82d24001907100d11000e0310051041c1c5002071428100310a00c03409200038404201c1c115101d03c1001000f6002e54841c100f00340500d0301d003c03104210b0b450881c00340c0f030307160750400015800c002030040040d0200010b001c546412034000b00c00500b900d0790900480d81010b90b408804200450b01c1c05900308141b84041c8102c1020030300c1c0042001540300e40044d030742150001c50720f600320a405c0300c040b503914482d4402c001c0c20034041c05030301806490304503900786021031180401700311107030f0360301200520341c0a401581601e07a0001c0c00410f1041540401400c0c8416000707100050441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 612928534 1250 612927284 612927313
    0x218060f0a150c050123070225210204090303051009020c1e19030c150c140901031d07080601060804050307030c080f0a0306090b010906271e051504081509 68
    0x8285420346e0305891001010003111950500040d4009443ca140300048420ba101241c005001305c0c1c0100c100c0a9100e444130300020045c03aa1151081b500600304000c0f80545040080243c00c0c03c0350300d001905c1e5500e83c00a52130a0602c00c032408121450090082070120720105822030640400b9800d507445102c140420040a12030150a918460344603021100501d190045007426400281c07481685800140d00004d40c001d4001100340da00c1d0400150388190010068009081d0201d05400c0d5030000849040523103400a6400141d590f0442290300980c0c8c1d4403800c403021407040b100240260424040100001e00484c001300745544a0396807039081010f440d58810031078200c00e5030b1000007034996030f0410076400e907849180c1d0400d000307203064200503042c01009001c2a000c10f6a0403000043e000c0398501000810060602401d000b2890300c01c07108140c80c1c56500e503440c80c00f4442c031484801c64810070f550704000071101140c866102802d20104400b03200f400078400103240c0c03412802603400364030306070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 612929784 1250 612928534 612928571
    0x10b09030f0d05090901050d0f03080c040909140f0109030c0807020406030b0a0b0909071d0a20180604050a05130902030d0f090f0e0f070207030218060f0a150c0501 72
    0xb030102d542c6050316040c950041041c083d50603400507001d0030075890190082600403951182c251f8042c00e0401c080d859480d8440e41e54440d6511426000c2d19001c141400c01078000101c0b40700c00250310031103014004025006080300c013840001008070341d181601b2000914008050045c441c001000000c0702ca686c0d44803a510414101c170000842a542e1100c5c0c02c252800305005034124155600a005042c00c10440100c00507605c0800c07411201e140002400b10138168000c1102d02c002e0030403130484050b584444250b40d030099211147c408060200b400600d06080703041c1d500720382c1c00800d504407040c949020302000c50617255451054680f00c42021025071401c000304201c50180d9551f00c00b085d08a14401001d04502c2d4100314680b502d0000308200c510200000c440d000109082814211b0b1240c040680c9071140942c0029000440c41c0480901c0680ca000d52603c101c0056401060105800e0304001c1e140e48036000c4c1045d0720922000c020310b824498103c604c09a4032410000803130301c01452107407904 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 612931034 1250 612929784 612929803
    0x12010e1005060316050108070302071b0308030405101b05070320070501090909080304030e011704050102030a0e0a120e191421070303080c04170105040201090f030209010b09030f 78
    0x39035160310501c841c600f010800d9138440c018520002201d00d040ca80000c02c0c0050241c1345008050f004124441445400300d610442100d45031a05044d01d41d0780c0c81e1080c1e5135001100c064405004007689910503074040e01030341c81000e503940e01444600e9540300d82074034141c001000075010004080d03078100805540b05404028500b4120080c8041c905d0300e4001030032141d00d500310525160905501e000000c40b0541602d402c40d901d0300300300c0a03007001c40004881d40644100404003103050300d03040c03000f40001940154000c3d80705090a2103503400d4460b58030381e10030408400070681046480c039100154410040c12134180c100403e490641001e440c0801c801114a4001440c03600b080b07040001c291801c0c0d03420203551400079500051142101c4581c6071590024400a8280300e0550300007110704101104440203400a21035201320fa25821045600814045400b01d0101b01c0c2c02001117007003c0c01c84880021660b0040042d94940e08110180c03550b0340001c080c49415200c2d01100c030101407401c0c00882030303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 612932284 1250 612931034 612931063
    0x50409020705010f180c0311151201030b130203030307080a180c0e0709050916050f0a020d02070501031b03021602121006050d03200a0c1d0c03010b0912010e 69
    0x14074400d02102c1104449244845400c06001581c01700001003c0210342e004507070b00b0512000f140c5a01c030f80400c4099401302560b828090300011600d585104034120750b41600d00890020300d481da2a10303603a14410b802c04c14041e41c19030052000842c07261007000d03601e92000c800c0d98041030546e03160203480540070502c041207c0845180009000e001c51b0401c003203078000e80f103180402c00d00b1324041c0490b80000c1c015040e4446c151441500304080b80c0540211a15800c01c1400950359801c9800000d454040040300c040060207540f03400602980309000300280d0280c54a00301c8030600184a00350029880110312a12419541401c00090380d40e0703418440c03000b18500003400c00145844d0040c01100e07501c0e00051703c44d0902c0c1c10740300e0110758001c829100041070800c0506007000503408413803400703100798070003410103061141c0815601550001c41070404070900302d800c0b1603200d02206e0100c500003405400e1000800b800340461038a841c5202090104403200002222200c40140505001802c0340d01138 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 612933534 1250 612932284 612932291
    0x10081909230f010b18041a100302130b010509040c020a02030a05030901081608010b07030c020d05030a1416110d080414120c10031112011202010906020f0d0f05040902070501 76
    0x1114a402d110300d2480c0342d00c00d8003c100886507040000c1c0e107518400c0e0100d0f05945540001001c000008181921540c0c01d600440c800c0d1034840b042003c03582050204030701480e070707200a410303906505000b20805a68140c485a00b0240c040050100401302d001c0d00e00e08600c948074105000d03860034041d0130b4456008034040c6030742c3c00c40040007403e40b01d000361141644100c2c0200c040c52180d440001981510b41e006032440e503d0300c0710f08040355000f00d60200a075000300f0020200007003007000401890019690380315200c007026210403c4030305000e1030345129a0081404420710004039500c00c108600f080003040c103001c0002c00c1d140c3c848241c00031380008080c81c568640b485081c1c5851011b00c05d640000c40020103811088001044e0400405001c050a05407944910456602c00c041038400070982c2080c2c0060329a0345070306074800c04065940907404a001c466001c14020320115011031908000d0340100020403c88001311003883c840b42d280001c000b0240404600742950b40003c1c0302150040c0000b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 612934784 1250 612933534 612933593
    0x220c08010c08010b040b030601210911180a020d020f0c0a020306011512090212010c0201091506030c030f0309030b010e070216080c04180b040f05070510081909 70
    0x2801c4840d8418a035051008000040003400400e0080f942540c040400300c80c0c403500c4410060300c00c4a60485039082c04040c0c400800742040c20f5502080b4500d02411440182e400c0d000180402170f02e1484512a00044400c0050509141500142002c2900080042c6000b180d042c0702c07203d5401283c1490300640102211800b0f40c03404012150141a8400703c42820103050b507001303401c248148141c0340d002500c80103444259501c10b0000700f04003044070002d0040f100f130920000e0003090f0059049034041d045a6058815080318400c10040c0c6e41d0040c00110110b0860301c07000940300c12200210108070601c28040001568259158000d00c11050b00c25490f00b0708450180c244030040249100c0740e28480f038100081d510004221503440c40035140000c48201110030a101480c1c900c074041c0048000b6818082005450710b11010403074002c1050305c81c10f0340c65400300013114445944c1440003442c0c1401264003007200c20009e40c143e041501c40003e0f07010f000c1e80ca07189100c12540100c041c0042c0507410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 612936034 1250 612934784 612934799
    0x30d0515220f05070c0605090a0501020409061a0909060d06060801110c150702070621020c070f0e0f0106080a090b07020309010207050f13020a050c030c0c040b010512010509220c 78
    0x310942c00506500070700907881e282000421403920540c0243c000e40d152008500c01c020140300354034907681c000b00290f582d203072540f8400703001c0c05903481110384c1c103032812080407401311560003a181c4402000f8000da1983d19444104003640914080c203440c0c4545d2440c000580440900c200960f042908880c0e6480c4d03025103245504001503000002c1002c5c0d085402c0090299000c1405010788106040140703114400c40507044105088000010707204d480000d050010020002c2e00d00221401c20b8580c4c03900903103c0c0d2040d100020103a039542c80a0060b40f0040c01194083c410703091b4819601440010241c8040d2907403160008181d0f20340f005a0000120403096580c18000c850151009550000035000d001010030441300d45d01e400e04500e15404035041ca161449402180d01000c110340071030303450708902c1850a480d01580e2030aa4030507032401b03a0b440650b500a02c19607041410603180514141c1c2327060184100c404004240c00b801e4201c21194003505030b10750000d40c0d2024000d103140312540341003040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 612937284 1250 612936034 612936041
    0xa06230a0e010e1e0108070c0803010e0f130c051014160c09140408070615150801090507050a120b0a0e06030d080108061504060315051b040602030d051522 68
    0xc03c00d02801c60f0030341003d007200210080c104070503c20310740302032203a80c0c2003011582203100c80c80040c0705150000c0009031450720004000d0259100e0500f45005407500400b910031041c8022004000d00d007c40300c10030480c50f040101d1802d103415414030b2098159084036140060f03001058000c44815911465024407110200b0b00d405000c880c1e50800c80140580c0f01c0c901c42ca0001000200a0400060082c040001c0341c1c01144248802a8400710342c40d4480d40d007000241c0400070b0300e000040f105000041c0380b410900515002d11002d841d182d18040304110200c49160241e20a07c03000e9840300760b44d41e07458442c1d0715000010419a81c4910541c2010402c141c10941c002c03040300100403c40b0014448c802010400b01d8120601c19600300300104075001090142101d030348080c00d09058220000045620b075001944074408603030900d10505060502c0000724040d5000b081d006034400d10200701d120744180d000d250028450b003030f0710b0300c1001c00c04006440307000d0748002a00400d071041e00b0301c0d03103401c1d5501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 612938534 1250 612937284 612937307
    0x20c09160e15041a09190603050916030b34031a090613150b0a020f15061201020c0d0203130602010501060507020405130b04230307020a06230a0e01 65
    0xa40500001c440300014211501860203200210b48441d041444403100101c02c60348a8940507100d41000c00c286c91844090500034071032140460305010000341d281001040e5880d410103020500d008050031912400c5050400070010080c42c242d9406400b281c05401c1614001100360401e04100c1d000c540c00f00405440c2c80440384d40f007034019282000c100e40e440c0703514194003030b134240c0321084030004950550016100d5030032101c28110702000085141c0c1c1f0242d00902c1d0000740350302210b00c038000310b82d0526620407440d6590111b40440b000172a40a19224141d00f441103540300015084c2180d0081d01d82c101040c086656015a10000760590100745001400004101c07034002000321b5850900050800e11030b20100a00c41c6954400295022650042c010300843c0c202c480740d0014a01441c0c04d131242e050072402d41551545030309480f41008000812034020700e034040c0100d42035902d00281510001c070400c50300b211a081032801d005408031a4005000d00c1aa544d4540700445030400c0054402c2e00c41c030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 612939784 1250 612938534 612938539
    0x30c150501062c09090307061803030b060910110a02090c0403061d0c04090201030608010203070c050115030503070209040c1502070f0902030103050a0f110418141f050601020c09160e 80
    0x10740428205014800240400f0106072090380c641c2d40d8900205003588541d420082407285051401c030801540d81c0c03420703074059219840401141200401700091380c0503418000d40c0c40000e10501c06509032085030702d14040c0e941c9004646144199900040b0840011500f540c03142d07102240800600282e800340c44a004d5840e0080000300c000025800c1c1c442226001c40d90045480d000c0510031a4481d0303012000612141008549a04140100412104070044140c0e169824004170b4003c3d02c1e502c01c1184c00316503002c0011860101d2560a01800c0f1100a10554203c5140d11000440b04011180003110b00d0190b4013900c001414038410307401640098000e4145148140b00500c0020000100c10344515080940c0d903d0701c010314500340e9511481c030f006494005080145400070110b0408403098030341d118107503000090000b0380c8515503035066040580181450b0300d08540d580b018a034046c9030054030610503254956240400f0501c0040300740d4440710a41e008101042546500081801841404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 612941034 1250 612939784 612939827
    0x31504090b0c031e0a090507141e300d08040b060d0611040b0d0b04150b0f040b0315190f1707080a06051603051b07030c15050106 57
    0x541c4509140000052440112120000105020380d851014000d80c030f500c03002118059107041d03030b00713140906020101241c41d80f01e40c0c4030100b400341c81990000104007002e850341450480b0b9010000c1e05144505100b900f0100c1c030044c231016941c41c803c080c1c078081c540d00c1725403074811f4003c150345d0f140010008a45007040b401d002072000250440f0001d580041c0c0455000c6c6001c80c16040100080221035001c8490307800005000549036080005003441c0405100c1c2080518400400c0c04241c0e1000c200721205240001000d200005550020b4180b0300c0b41c8130002c40c2040d4440990100551041d1080402019005000d103860301e003144015070a0705071039101000180c40d001074124094850301500b4000c03400c1c110400010101008510014150390701140c00b40c0341c190428800401090b0b074440d1a003843c0c2005800d02c94081d0080500034143c110007002c0c0c0780b804007007501c02e5803c424411410060340c1c0d004540418080d250b02a100021a94001025490440094074060074141c183e26000003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 612942284 1250 612941034 612941051
    0x60b0a0f030c08030c07030b0403030e1b031209030d0f1101051e0901020901021b0f1804050d08130b1302060706052a2208071409010b0c030d0903050d0e0102031504 72
    0x101150b05401c5a900c048d0802e50b9403290f20303090b000391801c11518a1244507001c41c03000f543d425210740c2e4510400603000d0359840410440f402c1300c144906502d01d501680203610602086105080c00c2c00085140c1ca1301801e00c0a12520369800d4820513507810740a084006c00c411326000c480042590001c0403039008600d0045400c4c0080d488600f804007075034448146041100311516145109a40007a0007005c60344c60400f0818001c0003904203440944040c480e80d40c00200300b030b0041241d40c0c001d1140d80f01c141003078600d07a610200c041304024003085418004158401c0107898038405408ca040c032aa60100e11460000380d000361610070340200f888856009103120510076000002c54003160310307140c01c0000040c030704154000b072621203500004162003207050000301e01603d1078040e10311201c12102a41c403640c1c0c40c200c02c03240e4007500b560a5119042000342940808503a801841c40c284242059420804214429001c036039214511030000d035000404c119140d00070400d00301700d0000c12101042500c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 612943534 1250 612942284 612942307
    0xc0509090406150503010c0203031014093108121006050f0f040812120717180a0804060315050402070b24040218121f09060b0a0f030c0803 61
    0x1a0002e0081c075074a0588602010b0003041102c0940400340084c4050b1507041c60081d03480e481200d180402c5241c03e00085851580300d601740036901d80c020300700c0c0b1031615080510300e0b1104050050b06140ea02c00304001441c60b509500c80b43c109405044502d80741c0402450400d8000c000034132050542514407024000c3d0303038010702138907001a817086015407500c5034401103d0080c4116001414a4400c1444003000c0541c580001e102441500d41c4903035040d22503c205941441d44800c085000760304010000c0c04c18000074010203031200c000411503007604550f44400510f40c0c0150005d0001a4440103081c151152060181f0001c000031f030f40c00c6150804a4a0f05c0c60980c070702800c545002c0700003902c0c03102680c038403c60b058615400148115a603201e2901420107014070500140e000d5040d01c072850102c04004075821003043c7c10002504440340300f881040d0020168250200c41c0d030f50b41d91035180f4094031513103240c07000b40451011303000e02d01d41035040202e1400520b5119040d81d9004000803c02031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 612944784 1250 612943534 612943549
    0x3090c0d1a0714040603020f0418051801090201050307050903190b0a11071101180f080a0b06040506010906030c05070f0b270a06020a05070f030324050927060a0506040c0509 76
    0x115031602d80140c8440785040c908c6518400e9500c440d50038000303201344005c0304925034006400fa00c51100d290400b0380014070241d00b62020054041d000c42c0041c00040c41c8640600000c000c1400c004040e51040c0740d203191481d01e10344412806983d8801894100040c814541c07003816107241641103c2030801074143c0d202c0916200304a071340c0b41000f0b0b00b41c80c00799030541c20340b89501c00b400454038803480c0252244522541c60464200996100512401081031410588511303070150506075078042d0305500748402076029100609141c0100f00040040c070000c510741c5d0181c01380551050209040324100b1806042c04044104883c103865100403d5a0305007136400505555203d6001b04003507224800c58000b07035540c0c064000040d104802040c82e880070503a0550040c25256500c01c0140f501d8040c080740400c1203c00382c060560001c1d445008506080107008110380c10605015040f1a162001c507401420504140c03421012103858405105041c40c09000d0001d1300781d19403401c107040030308400018102c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 612946034 1250 612944784 612944789
    0x30c03060b0d020c0c1f0909062102032d0d0806010c030807090f060c031202190c150e15090604030806121204060e01080f040c030803090c0d1a071404 66
    0xc00c3c0c3c1c00100c50340c3d07052050080c1002c1580043c0200301030440c8010721045c182580d284940003480d8008045580909403007418160345a001c02003407100b814820101480d001c0e44410390b80b62040c001c030031039400005442d05282c070400c01c044881450b03503038481074030b0701e00041001804d0000c074600300041f50740d00a104844a80e05860000806d444000096414140c2d50b0440c0060489902010540c150002c2c1d09403070f400d1182d41e40340440400e940c2c00380308a014051014142d50702d4031420030303042c51180c070b200200507001d5900b18840801d410604000c4400714004100c19401c41140066003580300200c1661013034213000a40a14546503400070580e0350000c0081d0300c0384400880d0b012144104000e814020700d445002c595032203031134103800380140c0a51100345000851003000175062980343c0031582e010304e9004410805e80340c11a0740c0e044441e040240140754911030101907000d075130303138034018900c0650280c4000191480352074044241004c004000a06100088400e10a03a80000049804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 612947284 1250 612946034 612946057
    0x60f090325050a080a0f0c020307120201030b0a090501050111010905061b09090c1b0a0f06051810060501031109010903080c07080304080f07050d05060403030f020403120f030c03060b 80
    0x140c1540414a48031900c4001078082c01500c1100c074810100440c980080500c1036007078a6403101036849220807501710010980003501030b0000c0c1d504104240c000d65542000e28414140410354107003820115680c0516503010125090702c9900402c42543c00c4000c211052002000a0140640c242c94903542c1e0000580008041c28802d001001555985001c1e116110300050120103a802d088000c83e0483c3c1116041d0030001541c58903030843c91400041480c3d50942c05441100031403101d440e40001040000d0a0f410003106d641e5441e12520f8091080b0700500d180010000340e414182400101221407201003514810410008000e4a0b81c002c01d5210840398403800720b40e906c0d0340040740a400e100299003c0c41d041d00c00071502082690300415042403d260300401c07900031990b200d08000090b004000c1c05040342d00a0f1001c10082480303500220048842c6c2c0202500d030903038a50f030380c2c034201030150381e440009201d5454014426525010700514001180780500500c0c0c1440101800c500c80c8452030074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 612948534 1250 612947284 612947317
    0x702130906090c0906050102030403051c050403172109031e090d110f01030626150703090b0f1e040c0e0c03010f0905010b030705180918060f0903 64
    0x5a410245410800d000c80e4000001d00c180081e5142c1009a605507000707451460f81400340200301035100006076800c0329005402440410300d2600e81c410610350240c003c0040001c20040400821101c2e44030501d0480d81421a503555010124a558012030800400101145c0f540c1031120f60384c4000180d88c5c1c80010b54010500720070807908040803512409007200c0d0821405904601882074194400300908000d035598803050300880011004caa00c60b0043d0302400401600c42943d85e4a036020351916255800205e50003007002001214004400701c4140c00081d4403042c21200300714141d0700c02078204a0a03203001419041c0000d01758162800303902003045100440c8002424841000002d00084c5041d00300c850040c2029541d003400c5a0090089420102c40c0800029813804030380f00c1e0b0350494501c3c002040c15619003910440c0ca5074408001b14201d6059038101100e41e65600c9a02c1c0e0041c0b940b039207011001440810502e0425800401404a011104041101a020200803603441040e01c200c080d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 612949640 1106 612948534 612948559
    0x50414040b0910050103110f010f0f140403080304060c110d1d01020f101a0d020307090e03040b12061c050c060a03140a0f051303050702 60
    0x12081161100020081855080480e8000c60450290b0ba030710b00c24019440291442a001981c0d540c141000c40a8103140032915011192000c2c245031043c0314102038041e01d0704441c00c3d505424485080280c5103164106400c68003d950700c503228035103030f0800e801c100380284420800381c0041400220004044a0b0010f07204212202c156203607100d1042500c1e83c151024240312400381036225041001c84481002d00c04040c041180080010302000884000081c0541e082d00e000d001d03841144420015031000718041c01a248080c002280000c0b104640d2895407141c0c1c1d004038640100410304104000600406174000e15044411301d400500c050401003001d04400801042a1b01c043c0310302080b810a45c0c00360400c4110b50400044c00740e0300c8610031498400c01c440a1b5481d5a80350b0342a21701030f582e03202d502e40241702e004400b4048141a5000341440c881e0340e030040d201d1614007440 = true := by decide +kernel

theorem cover : BRFrame.Cov 612769784 612949640 := by
  have h0 := BRFrame.cov_init 612769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 612769784 ≤ n) (h2 : n < 612949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
