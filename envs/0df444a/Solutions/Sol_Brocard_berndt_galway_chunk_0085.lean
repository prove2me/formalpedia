-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0085
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:45:19.360215+00:00
-- url     : https://prove2.me/submissions/fa6ebd34-f532-438b-85c3-843f07f47ba8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 15107920 ≤ n < 15287776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 15109170 1250 15107920 15107929
    0x120c09010e090a06030c0f05030d0503010b0301060c02120607030b01030b0d0f0204111b0703020f180412050f07080322020607080c010605040e011a01030b0f01051602090405160e04080301060509 85
    0x110f4101400e4107501b11008039070f0801100440043d101e0881c00c4076070307100c003103002140e10780b1090190001300042030004002c01802000a10b00a41c401405292a1000c0c05601c519140e0708a40d10000a52505101105940c00d4400e10110b50010b46001d04041000c2c0c0304e0114003245180024011070351064001806680e440543d04400c8003008002e5800099501071940c441007800160301c102d030703209039440007403514a07241c040500c0e507101c51103440d54813a20f60145240342030f91950103002c030400c01018800503080007441d42c0c3c0d200c1ca88507901ea04015842002018107040300c1d140d0b4aa003540e900c005aa6154142c0311100c1d0b2180040341d0f41c00f076009810307014003041e900503508681031400e00d45085c001034101011340790344800b0580d0400c802000440644840003840c6400c07918019200d4241d5200301f00825807900c0071054440510443d070b001c0b60042c88100d03015a61904640d045102c06210700302000000d010395012008503041c9501da80e015444103109800510400082080c9141c86 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 15110420 1250 15109170 15109181
    0x70b06060c012d02030f0118140c0408070e06010212070f0804030609060b0f0a051c020d060b0a060c0203150915040305030114060c0a02060a05070c080102120c09010e090a 75
    0x101c4100a01c0700182c50004100411072800d09501105603007199290030504500c240e0340704010500410203181d01e45907001450300032482c03210301c1440e15451030071401c402040046000319103400d10540d03581d14200d081c504004403600564035800a580070302640380c1c0d0000d544201c0c950300106444d44c680013403818501050101400400a4001040c0041882070a50040710710a004800610015000d08100300e24413000035200c940c0f10050050038001420f041c1341c821300c21104805102c01489141d00082d2410103941412074000d511042d40214508000840400174203440c1015100000550b00081d2210003504113072855550b0740d0f00148000d4001c000c03603000c0181000c191545410241402030042c5d01c2402840140f0124001c0ba4191b420514211188600401c0103412501403d81c00c2200706e600282d016810080180701c154049801c44007408021f00b03410000684c0e69030070621005088400400c88a03410300705000b18009641c1202d60b80011020441d108409039640d522100c00820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 15111670 1250 15110420 15110437
    0x70905090102130e040201020616031404110406050315060d030504031208010303020c060f0d0c03020f0f070302060105011d090403120905010501030b1305030f0702010306030206161103010203010605070b0606 91
    0x1810041809149401980144042c0700c01e03107180221a034a4540e20364a1000686009005030321080c0010b03041d0000c2154180080c026140220303011003040c040d140d40600603603064950090340070401c05c03645030a1084400902058018014070040c0d28034030b401012008114900520482c2c9d1514201889282118091540304509030b41d0291220402402c54109000440240c07141181c04041c628069058a103c80b0300d01760000c1c50220030300031400280540384500d00506401f4000d91010308200c00103880502d01c9106442d40310340050800034605201a840f450500120300d50888000ca00a9698043e840b001c0d945646940c0ba5858115950301e0407440050749a4603016011080040c1034021318100c0f8040d0421442e607407504a00380c1d54110101100403c86d5004102404000410301d001c0d005035030050600040051352600407810b5940000d1495046483d4800ca03842080f000c000c07180d003800e805400850441d03040500251561142c41c1001c0c21307481000700046d440f83d0341e03402211400e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 15112920 1250 15111670 15111689
    0xf0e06070f0215030105060706020702030106120b070e04020f04090c0e040609140c090f0919020d0209010f020705011d040204170c01020d02012009030f012406080108060103030e0307 80
    0x349000c0c1000c207448000400100e219000d1816814030b4243c043e41607074180c0e0002420589000e049603135060080d0700615003242c055489480c001401c40070448a8240b85029800445051074000c000520690305911041e106520520090300e28000742c03000d07942a200100e10001e03144040f0082683e8600401e000203030b029007452408542980141c000f031819200304620440e180e1507000044005010300c0300300f41e4005a1020342c80f1468503020b80c0b011f400c07480d000a184038409060080c0c41c140d81c482c0001c5141c0c141c0000d401011540d201034221468413892000d0f0020358200000240303103c1070b01c40aa42a40740030101541d481c1d603641c0c1118001e2680105508054030f2042d090f6850b8007482071614090300501d07090000b40c80c01809580f03401c07103078240e80b011070300b20106500c6c8481d00b1108515406100e055461240b944091084151161240000a5035128000182d0b5545c1c0140d801c40300c104256000100b04015001a24031306595241c01c0010f905419400440d19003104c550044108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 15114170 1250 15112920 15112927
    0x60f1107080d030b030a020607061104090908040302100806150a02010b0316091103090a1e0b070c0203060c0c060606090609100503010e06040b1003050406060801140108070e060901060f0e06 83
    0x20500107100d42c000c140c583c40c2400b0b031010500800d926110a0300010b500700c40c1c1001040c00041507903000306503400c44004980d00b800d442d42c40e02030071207003106403c540309030300060140f0640c5480040503071020301303602e048203184c41d0110100d205036540715030441500c1e1000c0340001119000790000d82542070043d0803603000c035000e00c00320340241d00c5a105000d852450003451914010724001145e11402c0104d0041483d4416503403491100320828ad41281400c10b100078030740010b00ca0311000f50290030700359a403140c041c1c554010141026030142404c005803904121180021002298540d44103a0071103116840c0c00c1780c0c0012410038407034003210541c4403a8851045104a420001650594030419005090b41c4e81e2031040c0012644140c0040f03034000103940c40422024031039017089070701c0380c851100031800660701e101c2d00307085d501c8410107042c1048034000148280f8004129040c01003e40961000c032508204010403030800c41800782c102000009043d41c0000fa00542c849030f4841e0000c1c1c10a541c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 15115420 1250 15114170 15114179
    0xb0714070305030a0518031b0a080f030709210209090703020402030c0d050709030b060f01120204090605040e03041d04050a0b0f01080f01050103031215170a02100206010303020304060f1107 83
    0x1441e4403ca4200791618a0000425406d106201d11a0143c08140300114030701f08102c0da10500c040d418078210303074403841901207150004220b00d02500f0441c2004000700d443c2e041010000d04649065081503060700174441d620601010440d9582c000540c050301d12034540c0d1620354005080c200503400181d080350001061059907040400186a0308e41c0704d440403c015210020102ca644603244405828800b110021894524240c0003a110750481410002254056914038200baa003240d405010340f83c0c1d80d1b180412280c2003601603100300d025040080c40c074103401c04a001000f82009811f85c00000c44000024080100400003688010b40101101080d4078150502041c0c052090003100c00f14000caa04200b00244140548d1b4141c81c0d05032504c0341e4100c100902c00005206e42d04000d013281c803194400003002d800100d0a8288021060080c20842910b8018815001c150408542c2107500400c010000710340d0200607030f000d0701d1240c64400b08120343c7c0c0404980d018114211140a4040c4060004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 15116670 1250 15115420 15115427
    0x220809090f010305120a0c0b070302070210050d150308040902070807050109061e020c060105060f090a03060b0414010b030c07150c0206060a0609080a15060e01030305130504180b07140703 82
    0x10b04aa2091088a8000c1080b100342d07040c0d03008220b00f1501180100d420500000c0070407400942c003400c0d91400604041894001400c040d41903411400862030001d0790050305040c078041d40000f010700d46c4401d20802d15503900c52040740304030700ca07280c500390b07000c506107041040840880f041c69400000901810203d410302c00d006051074036a2500d1146044003c00351403441c1e0003951000340c030f01c00c040e043c070343e203044103020550340203044051120004000011040c0c0c0c4600901c4061805600002000f650110034081187c1d103035a0f841e802070b5440801046241448000c4944c820382002d1b0107610b40d4403a00e0318404440200c040b80403694201401c04403400d500044051040000315680c00801d6550030b004c1e5403441c2280910380c81e64020501d00c001042464031490704e008070610001403111f036600e0000640700000c1c2c2088000031070019031088524980d200e00400760030308031010840d08420260407a030300711280000400e081c607000001000d450040c0404141c007564042103a075154428540107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 15117920 1250 15116670 15116701
    0x60c0309010906030506030a030f0e1005030a150506030a090f060c020f0606061312020a08030c030a12020301050108070e1219060509010e3a030b030105090622080909 73
    0x40c0c000b824044001403103601c2406810300680c8040c4c081d0a0103140c64500300c5140131410080f105000c10940038005a85441e0a000c01c40340072550303a60784034280101c0c200d080c2d8803e071003222918484808148104d0f51048200c030b812a5a0003030024242e07c0030f240030844100309001c007074015450066040072140e0007154408803900104203480699039040200803180c01450300c1034440201042c010f02010344c260704030004507030000342902d41e059601e081284c910f50111802101c40c0d0004500c400c0c0f01908030310b0404050b001c1100540c1150b05101c00289078000007020a801c0014025800da141e44900d000060b100312404156030130613000800c40040e00c1c0c101c2c682265003500d0500001c0c541101841146901f08008003e4108031069075004c0a0307107003404407042c1090850300201118040b9400625001e1000e0751408580b2844030820942180c400504480704d0380c000008100301c42c030b4600c484500401c038001c05480030a4980c02e0075030041c004c404c611504203200b070050281c95501080071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 15119170 1250 15117920 15117937
    0x12090f0b0906060d050c061b01020d090516060e04050606070b0f01051203070503040311030709050708040c080d12020f0d0624090305030901121112040302010605011b02060705030405060c03 83
    0x31542d1585800e01800710986a1683c09090740d0086040180c00c0e107031240c0106070108194041c8500c841c0c84c245882d089900008200b044a541c5449201c00c001c018001d8030b0340860403150070084149040000b0301010000a41c052180b50f64a002030119078404003aa0003c0e5000780060310640b0300146007007034844007030041d6403190000220034015404004201c1e4541c95106024601f81440c0d0b649160280c1b050541c215410b02034508042510911841150300c51151076640c0da40c03034107080c20904a000c0345904004030f1a00110b107660803040c0c1040f644201c9140c0800c0040e40c90001d110442c00034000d0428030041907042400000300b0031030600d040b030b504803d54860a01c020120380e01c26502c462092000410039041440320f443d0541c01415a4401c000044001044510703108201c0c0300c2c2035101c0002004407610101c00d2106142c0c0c244178500240c182800c0220056080380c9180fa444807488500034807a0708005540c4041050a20664005200c0a89030399290801801c6907900d80d0040c01c0b9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 15120420 1250 15119170 15119173
    0x6020601080c0105070803060f0310050403140a0e010c02040f14040204110403021302090406030f03050c150705040506130503010501031208090307020a09090f02091608100503060712090f0b09 84
    0x4034a04401042c0c81050b210141c407820704d005e0b1503aa448003183c00007041240e000542c0d00b52403102d41c800384005001d0714186c242c001a02e203460b1801409108000100058802d82481142007150b0010401107040000b420b041c10080c4891000030040d0089020b40003191382410703080c6000d9003500c42d50750300480c802c84085c00000f401007131900840c0100c3c84060350040c04480004000c420030b40c001d2180b03130ba001d08041125a2207450306c1211854281d400c80015100003a01034121100303004418072514140706101c3c090403c44070007090f90095004480c4115800199125184401c4100000030103000d4006d1206603500d08007298406141011a03001c20b5206000810040000c021510110380c002c2c56880c15034240700021008115600080341c000d411030b69004096035980c02e00a21034107601d02110540381d52010b004000001c05800703222a19507101c018407050360086a15944042d8529214044810200c03564002c3c2000c00f50260031202a078103144203028142d0610f901c2050301c42c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 15121670 1250 15120420 15120433
    0xf02130305120c0c01080702010603050102030c12130c05040209040b040c0f0f030203090607030c1704060506040e010b030303150102160801021b030a090b090301021b06180303071205071403040b010602 88
    0x301c1c0b100c1d6110703d804101e116080040c002840d58000e44456400a01520001820507202e903640350072a401900c061001d80400b0583c1a020f076080d101603035002640070101c420030314a03a524050703400324901400d0f100c5e03a008910799009858a6112100c80c041c020070600801180c51400b9040094208032440098a0b10001040860013030017180d001d03940c65030040125903901d0500f00d00402e00b0b07121107170070080410b4940185000c141c0d103450045001310b0000549081450421085030b40503c2c010314181d04001d00c000c0350303a40100c20349a10811701c580c800b402d410b6400040b03040c4401c041441d0358894820b4404074001005501500c1d022030180b4070140c95205101c07007169640915041e900000b0030f440806d00003580c01401070800303018050005810225410301c00e080a078a140780c085100e41c05042084401804115514543c0203090083c2d8a5800d201741c000300323a01081072840703e4030ba440300d0100f041c032403240e43c1071050b144603400915200c1c2842d203080c00c0e2070f06003841090014460b60 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 15122920 1250 15121670 15121693
    0x61401030c020d0e0105031003120207050109051009030b0405010219030e01050703090f03030e030f07050c031504031b030905090906070e0a0605071502040323071e0501050c010f02130305 82
    0x5040325106885072612803984e80450011602070340000c0070705080c06030400e0b002002542c000d400644410780c94016001c482e0804000510180d5243e01c041e02c50141089000c140c01d0f00160680c0c1900c1d001210614142e50b1400c08a01a105500d41000b005102010200302d041e816400002c11450b01402403020361180242141038480c0c50304d01030001110410b03e02c1c00030740254440a09241d8a206803800c200c00c203170702e00c000fa81004805454030341090721030f10402c5c90309101c045003010380006500468185918024512006249160100700403c1d81000c1031600540300d0f10300500c8000d2101c9000e140070052a07840e2032080ea8400040380140300510f507145882400d070001d80e0310507601c4909142c6030791180304110b0b1195050000c210342c2008040b011400244060840c0c01d6512981000181071003422840c0511551021900300f04100c00c81d0004480070403150200c0c0d41c05d00c2e10070b40b618a481d014a004011048415903c0741c800241195008410000c00c41142d0080c81a5662038156 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 15124170 1250 15122920 15122923
    0x60301090804140102010609180308090105010b04050607060f0c031a0102060103030219061404081b01060303050405090603010213180f0e070e09030c06010b0d1a09010315020706061401030c02 84
    0xc05001001d080082c0014454081c1040036003612820510000c52010b81e100d5000c0d040301d0162817100148241c07401901c0906821400094100020307600030040c543c90700d01012503034011401101e00c1840c0014105080c021a034101c00e425409086040041d88606003001e00181201941c480101140501d807604540c004640301d03040702c0e01030700030707010b1454400007400f028000d4403401c0710b015a442280c5100045580c1d50148207611500e807041c0c0d281d40000c86100a0700482400301c505a0428005000090f8410f05650440d002641e10f418588c0350304000901a0182c00a143c1030503441410000c1c8100c11184a90544008204108206075151207000245c8940c40289034030b50780000410404118026000c1c1e07440310400c400e40b03003400d4030f01c0d0303419080c0344081e4070200d40171002096170103000c0c1072845840300c801c45401c00d21b40a02c260901240c1341c6201448060000d5000020340e81600e007880c2c048400070380e48001e041055a458440182c01015103141c0c1e0b81c006032829403a180302070300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 15125420 1250 15124170 15124181
    0x50403050607020c04060504091a0c2a0705030f150703020d0f0c030501060e060f0918090604050c090610030c030b060706022502091909061d0d03051902090402040b130608060301 78
    0x700500c5a10342c01c86c0109441d82001009844bc603089041000111444100c0103800741181852840c80240345190180303240c540030054003c54482e800c0590501d42e00800010713440c01c9851a82409125566401c81c290300078001c2e1444000d00504000c86800740f00e005500010705658180c038200116607c40794221902010145441d81040e0104010241d02c000903026001c0020014802d00c1e0700c0300d00c281442d00c5880d0545021889500070414407082290900c80b50522002c2650418003e2404400103414046c1c004c10010605640f01d540a4226101c0d402001608401a10050f640d500c0380c50b180b8001c0d8441c50a61b41d4208400040344844000700800000080d0014452070854444a02044138690350b00480e4011680c8e5911800000d0910f0007405045580703140300500180f6000050b03030408015041d0032040500c0c0002304a0000541c040101c0c88408401d00141c0350300c45040403400074495a040200741000100b0050280c0303c840e520801030381c1942e6147d2000b900c2d44428942a80e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 15126670 1250 15125420 15125423
    0xa030305090405091603020f0301020f0a08010f090b060703050313050d02070315110a180906030f060b09060306070c05030405040204090b0109140d0f02010c020405070e10050c060105090601050403050607020c0406050409 96
    0x804034001c00c05440c0235600703110390300741c002d0005240058081d5510000e80c1b141c01182e01107680c41004010a1039a00903010003030040d11401d005001020300003074240d1040b9800282480305c040301060000b4216a115031580743d00c0300071a00c000c0400c5002a65440e9217200c1140e07400c0d0302c0904120702e00201d000e15541101d4100004e410061b14007810f613203205680307070b29054162010a00050b00c1070940901d20007540541020302c3c047e0307a2801d240d8159404614554082c0800d0818002c068400090007540601c0910703140031000114501f140c21413080340d104a038424004100402c00c0c0d090b80c2c4c050070354100244c0300c4c02c0d401c40d941c0007aa2030f10000f07161581d5000384e40319410004201004603030012144140341407070a84046500090480b04203071503a00000c1c3d0301008454143c10000341c00b4120400c5402c105003040002200981d0740c19050160a01555a0401240c0540d0003030041d20042c660210690f0658075100c40002d60f156680110148900e0404c00009503034140ba1080500390b5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 15127920 1250 15126670 15126703
    0x100509030d02120f0307140328090b0402060d02070b041b06020f071401050f0a080105011d09010b07050f060a0509071208030a0c09080f060a0501080706020a03030b030307020a03030509040509 84
    0x80f940b01d20780004c0d400003800c80d414045034603001140c40c00d120000b50700c5080720009006001c0460205d00e4554070400c008c101c1317180c0c50705200d00c012490895040754803980c11906150f541e1403040070f050181c054403100805c01d040807010b10041010071540300c4503030301241ea10314400750350310b0008030303929403080c0310001071500070b0341083c4060035500e20354611441e810304140d89800c0c1016240c5950ba4030040d5000005052940140075540e444160001a040e42d99034146400c00180700080c071a18040c4a41d40c65060300150490401c9000e01400c0d01c240c000c2c0f03069a0a41c58090350841c050b18040300c0b40e0a15000391880820151100309810380e0003504010203904590360540118024100f0745501e206102c0e01075400204400e0400c11808942c00110181030f4904116a0010503210107800020907904107800132b021280d400a881c06546815280105100014101103801e42c441c140e030103074106203000408000d041d0040f0040801d02025034041240307548030710049440703a07110640740701e81 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 15129170 1250 15127920 15127927
    0x5090d0c110a030c0902030907050a06020709020717030c1803060c030703090201090801060f06080a0905061b0c010f050103051605010207050f010512090f07060201020f04180209100509030d0212 85
    0x101d001003809102800e0080e0203041042e4490f103c00c4114074140d440220003d40020401000b14014007001c0d00400040d00e001c080c140c03c001010f502d03240c041c040d170349000354013140000c280111040a808030001c00d550265413810540c1e14208154025140700919081c59140d200c0603040002d0795a100300b8086003124150740314100d088014028419040c3e041001d00341012968440c2841038100428401d41020816440c048001d4800c50005100c1d6894a141602a0021401c0450042d40c01718842800003011403002288601a0040700c0f00f0010740e62038003a0031400d0f07441c55403245060701e000b10200c40c6660380414020070b9901e59400380b1401030700f008000304034900b0802100100040141440c6040140e100160005158111209000c1c3d40c040c40c50668001c00500c030100140006200951030020307444c0031000702c2e02c110320031184c01901d406404c010a0780e495040d00c040500051208964104251004101d40c000c502c500380301c0e0152405130800c9600000e101c402c0586000456400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 15130420 1250 15129170 15129173
    0x4030309050405090f0d030c021509070306020c0a0f12080c07020f06030702100504050a020f09070801051c060f05012105070509041b081609060b0315040e030403080d05090d0c 77
    0xa828082e007410900d11030200790311604402402911003021b90356400146110242000a2800340b0b2008200350392414038041c00b11086011803004160780d00081e0150b0760719840c5e07840c14901804d10401410101102080c64100540c000c3d680d444151150749407920394440c481d1a0030644124840207600400c0341c440034103542000b4000d168080300600588a82804003651142691000c890032680b94112032859000c40ca05800d04004100044d41c5000662a285102401d030203410f00806100e410340d603042042e014000791829200a500040500c02e48450701c4090028050030b02400900104004d05c10000141e0704138074140c41038000c0c004000c00381c500024401240c0000d00141c42103010007032080780540504020070001e00405d0010001c0c0f11040c0410b0310f03040d0158000d003c0b01403e04004208000640701581c0e00b0401405c90f800040a2841c0080d000b00001440b466580c080810004148032165000c0c0c035400d080c2d00400c0c071007030307440e408000d0b05d910380e103411500866100c84900d030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 15131670 1250 15130420 15130429
    0xa030c0501060906120501060902030c0d050c1902010c030c0f020307150b030307080403050c09060d0b06011e0c06060503071203080c0702090a020306030c0d0305160303060f03060209030f030403030905 88
    0x955500903000000d040d61601e00d1942520500c0c4c01485108203584c0642c01080004d22070507004280c10802107003142800e10490425118120941c140d0507111130100b2000d0b41301c4012501d1000f0039101181a030822000003038082e05400f03a11101092074805440340031401178000c1c08450311503a016625004444d6100740302100503e07204145182d0341d61001c0c07216182003008014280c0a200601d49552a61400306d05c1d00460010250290141506120303864a90101000803e58070000b084c80966400c001207507001d074140702e07650702c01c08645c05945c031658110b1964920300d4003c03181405205c1d1148145942c900743c03440b454405040c01038450020070301c5480044d4000c011000366900d00b150075000210009030030f8a9100301c1c01c1d400410300c280e503c0e08112070058400c0a403920000c00380c02e510040e00c60300440c220f0f04026081983c034201018400e500000150001a0200c2c032400d44a00341380d4020b4000a5000340030780b00f030640c852100ca40006c1a03c044940c9a034541d4849400c00b001d11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 15132920 1250 15131670 15131687
    0x1092003180a060c0215130c180e010501031b060c08030a1805030f030609090a0201020c01050903010204030501110306041d06010501030b010504030506180118020619021e010207150501080a03 84
    0x2840c81d402580189400101e10340280c0d00c0b200c0b4507a00418001c0304c0321450b05c2c106200038065041c184e808044100000c0c3c1d0400a040440d661a0001d0103d100a0300c0302c4006800d00f4a1120b2255203450008000c2040071004e2105c6000340c400700c9001c450b11850f003600c140018400162940d01c043c40003c40d4226030350400900819211820000a8443e0340e450b4995044100c0394a1001c00200070001039081886c050f5600405060052125aa954001139114a112a401410003000043d52750385902c09404850040d544031008000319900d03140142603a410a8402c28421420404080c03a62064158000e1a01741030001030482a460640107400a01c450b0b8400c505000007400b0020215005000c121701c10304c1c104481c1c07040a011007291500311010071215800b0312094040c2180561201400d84035030b011990011400c0b42c1c84c00106078030304203218580301044085240c20306854601074000e401d006200d000341700101c2f1a02000441621001d018140303081c0d01c1203048001007880790050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 15134170 1250 15132920 15132961
    0x607020a0e0709030c0303020607020c1503070f050405030709050405010f0203060307060813080a03050702010c030204060203041809060203011e060201091505070e03030a1d040b0904080a020f1501092003 89
    0x60000d44e0350765550110503016a00c1500960407040070001d0882d0180030380c2c1d80c01c0000302c0302c000c401110502c02200c00d02000c0c0014081080c807040070039151340030b00c0484e03002e448010110340710156078203d07032800f904003104d0445442d400e00028805025490081d01e02911005000d40446401c0ca81c04468500004080c1015114404010b2011600100080c03040206554021859140c00d150182c00e541040800300201407040008004103540803043d501900d00f0030380200d08903d0030603030080161002903c05090784c0d10000002070009211005070013042050001456440d41c0c03480d05070f0886011001c06422260b0440404c201d5054a5001c0740e03002c64103040c4000e41c18288008245180c020549403400309516510344000012400e040104d5101c04650500005010101040c0d440740d01410040c41c08002180c030b4000c203402400140c11010007031044170705940020601c612510000e2117150155407034210032030084040c0d0b150980040c2c040c8083c2c81c1c031307503140e039000001b0180c418200d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 15135420 1250 15134170 15134177
    0x501050303030601111203100311010825050403020306010609030b0901060b04060e0d0c0f050406090b0d080a0c0b0f06040c02010903020a110f0904150c050315041e020d14060607020a0e07 82
    0x8010b46c6800d8200030f180260702c14901115a141545041c50701f220309846030340e040c0000c83c2c1c00c12000310080b07c80c040d03481c0b0300c0c0650020121000b107000d90300780c051130b04000e6050040703000114030180d1101c108403c407401140e00740c040d03407141505142290b16500411459035010401845060300940351030100d400090b040c5409610780d600e81200384025900074461000701028100072600d05401a038020780b1888a003040859904e8000544242c81d41d81d00800c0f0b02404955028420b024041d410b10700c40e0002107406d031a1801d4985c882100200303ca80902c181d242000e5031101d039205201e4605a20362540080401c1d80e00d503140d606450001071203850b4131030740d4258412100d07183c0f05c0e1540d000364031500d201400c40740707800c1c0484180d03040354146900b08075091080000c5098008143d221050042d60002800038144c0d03520808004900700c110140c0c0e00000d050340b9a04010b5200303144090002d01104859140c1c030003000740f14030035074501a5000e000c40e42c05120241860000c56003100c0c1030709 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 15136670 1250 15135420 15135433
    0x90308090105120405060105010206071704020906120f0307051501060e0904020402040503070306050405071a120405070f06020a02030c010807140c070905100e010605030c0a0302090307050406120c09050105030303060111 96
    0x21070803500c11004c40b002c881a4000d50300403c004e58040252036000a00c03406c0641e01980880d01881d00d0780f00085c4041e214210403c04690144c454141d48820f620005064800307411410b2006a5030740d0000c03c0854079881002d80d841c3e00d51907001546410384101d031382c550003041c18003030411503940300c040c01c09d0b41c2c040d508000c0002d16a40c00c00903400154490603001c81c8614003070600034241500e952100c1e003200d483c1c05c80c4058100341c15084401004102c26a030300681c80c0c50a020789003010540010507403040c4a64082541034001079040340451084081342c1c0480d203030900441b4014001c2e034016005c146507580b180302240204014080b40c8150104076000c02e0b540c0c070060000e40780c059544026004600c8014403420101c0640140940680e0134110300e5401c0c5a81c22001078410340c0d003003c04050707010a1709500c80c1e4050000300d004240c02401407003150b0b2a58410341c0c29143c20300045850f0210301100245a50341c90003080e04881c0002c024500310b946d000300541d40f40031801b550b51140d01501 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 15137920 1250 15136670 15136687
    0x10f0e030f010b040e01200307030b04090c1503060608070e0102100908031603020301050d020603150a0305010507030e010b0d030e0d0606031b0504090c03060b01110f03090a050d03090308090105 85
    0x70014605581105400810418001401d01046445000d6200c0c4c5590401c41c91045151200c500801c44412440c0115525525004124001d18600c049654403a0401200000340203c182ca00e44c00c0d526114007015079200560720581c116012442a038000c01d1b0709000040940380101a841a540b006005a030068401c046240040700d5014004440b800400310030720603807480300300d0354400c3c400da1400c00310300e0b55061100040d140404018000e104420010000e4000e4000c8a0341c00900c0202428444500e03440c1e2130041e000e0030b811107610340000c1c500030300c46440070414021071583c4217010700319100c02c1c4039503281161400408428590000d0100c2d48210024419105050066016280c6002d90040071024166841c00f640d01072846903080c03418400c082008d00c00440c0c2240c3e440080000c2c4e00c1e408000684000e10f64000581c0d46003e011b14502810360b0120062540140c21911410141d8480c0b0401c92000d14040c0007900250b074180342400050307940703c014070880d070701410604d041141c3c0303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 15139170 1250 15137920 15137923
    0xb03121e030a050a110c0714040f0f0c0219150e0c120106060905010f1704061d1e030c0a0b1003020a0909110901151d0301020c061e040b0105010f0e03 66
    0xa5611003402e07640d540402c000020301e886102d9004000780c0046207050445a00c1542e42c010030b0180c405003007190150807035540d81d90f03802134001c044403100c280325030b400c15580307a40100410000c2001501981030583c80040c3c42003e01c40165601008143e41c0d0b4580142d038100070101040d0803201c41c0f090041a09130769a41007822000440c803d00003082180c1010700080c0803050740c2c1c1c03100d03044c400c900640040c4290041c508600303403044000302e070a49030b589003028000342c80c494070360000d4043c840700ca0340c2100c100881c400c000809541551414400c030003040d2a5079200b6400282c03441c7e0032000c0c40c41c0004205101c0d040e0001c00781c03519404a039450360001202c071100c99000c00c10082d903a11242c010440790600960100c86c040320504210742c03415158000c1c0010b00c42c054406c2203075a40c8004c40483c2c420003d0b20404c440a0700854031810340d07844c20f0343d03036a40981c5e40e14040358000035050200c0c00409d43d91486261300085950159290030010b4800081c1c43c000d6000344945043e60020a132130 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 15140420 1250 15139170 15139177
    0x60c02040b221401050d02060a0903020402030a20040e0c1b060c07030206060108190b010302040317070201110307020a05220510090e01090206030708040201050c01050c0301030204050601030b03121e 87
    0x70301c000d201100750700b0342400c0c02c00c8600c0c003102405804292001040f06a03148a0842e03203d507010355420350703200c000b034008030ada501154000170740c0580f0100c140890341410398041034944145d2107441c07810000303481c0005100e015901c10305802d000c80c400080c45400344000039040c450100409903042e2045010842d06042c5c003212018403e4001242ca0814554100650740d0403243c00e0030031105600b05801d40d103a0310000d40c00d40f20086604d40641a4659220364100c40042da001091484480c20a4082c40d10a5224bc3d50503800512626606000f020b00801100d0301c0c50303402020600502d00d00024480d1800d0035844030124006802c404000d403901600442c3c0c8075114070460303554003a0410110b03e00b19955008c1004c6941c0c50b20345a0b40042e103520b0101d030b810452a09044402d0740e43c43c8012925885000d00a400c65401d10042c4500385a68501460589208071070a01c200e545003c01102150900110543d050340078612040d1455540801400c41c07251a017008942e540c0d095480100503032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 15141670 1250 15140420 15140449
    0xc0215030c070201091e03032001020f04030c0e130b04140d080106080705040602060f1003020a030f03080a020903061803090d030216120302030a0509220c091e060c02040b 75
    0x7200018441c04540e40300001c240544a60712510b002142c4d4011a591070708654080101403080c5001d0b41c0c1c054924410004038855090300c0255038401c8400c04d0004541c029100c00c0701d405170101d00118961403d064010b00c07030b4582c00070041480c1050313110301107228030203441511117968004886552400a10103450382e180305407160750080d45402c0d001802d03010001d0070350041240070300052020945c08666540c21100c041420301c02a00c4803444100d50f0f800d40d5000941c00f035071403d00041000203000000c600325000e034440b03014a0303840004040c00da224403510760ba81070304410001042500401401c62a03040076404490903c00c80c0d50100d040109136080170380250b44803001c4801e18081d40c217010b0001d8808049200c802004035030740a9034900425005034180240031a11084a88030b0309560320010701d0780d02800c00300d5002100a4001003901c0010000082e20550000c01d00c3c5503950482d40030340f2a9405011303416440d04000b100d886100c001c080307a02540b1400c5004050b0b4074016001d4021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 15142920 1250 15141670 15141691
    0x29041502091806090106020d0e040e01140906010305010609050103030c240e071a07020d0209071407030f020c0f150a030e0a030215090a0f02060318010f020405030709050c0a0c021503 80
    0x2403c0c480b0800c02e01c400b059120404550020455105160740503d950045800581d808600041c203c14442c0c00740944100e4001000c1d803000802181e20303170010b5014102c80c010002040301c1c1c2c0e02d518921050759400d00010700850340b4460403400081ca5000c1c0c4180b0303e06040b00d00b030700f003201c00d88889040c0d55560501074440e50000c042407114070071a18500c914443e4002c0d11a1070a800e030760114204079420320000c0e1040d9a1a00051140c03409064801007000d04000616550810307454090300000040c003200d130052190400751940c2d0308000b040ca6960035001070007011042c0444450f4402c1ba40680c0307680c41096141e601401c91144108442d2400ca4425009015000c10100c0202100a0001c001284552280b204031000c102081ea03c040800d4041d144995a59a11003007021401000d00d117020480d0b00e020604401415150301a006a56045060324800d80d92040341c1d20640d0740a80380004220003c2094805e15030080484003803003032001e842010b100d90391000d000401e0f0400c071050380300b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 15144170 1250 15142920 15142969
    0x30e100b0307050f090604020f040e0c03160e010804080a020102041706012d03020108220302010c020d0302040308031501030e0a0303090201030b04020309030912010b10020304032904150209 83
    0xa203000c1c442d4801410060301c1c0144009015030028604900203403425009680c000358418445e144481203401a0800d0010b8050303500f060003403082a80c0c07086500c0e4071100c84040c045000c840c41224410400c0005035a800c0031900c0340d131254400390f4002c2c407100044d598200b1000810b000d03001403000d00300103944041c2620358900400027500c11030664410008050020841c0d4515100021080c07c0d0b940a10f804900d59a4240f00141080c904100320208000f04800c04410954150400c654401c401c0d4241c0d4038610317032a4410fa06a000d1408000d112600600009040b410f1001c2512800c0030145000b1401030203548503282001040c00c401e0780003d0b02d03207162030103650f050b0003070303401260713065401b1495480d0a1120075124040e000d4094440c040c1902a60640c01c002d40002ea00c10000800c00744400c0e64070480a1742d00d5100c1e00c4111019240310881c0039504e411003003142c507800140c52441c112a50f035a500d0b41c03400c0031800c001c003000c180c1c02e115480c020b84488100101604491040091 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 15145420 1250 15144170 15144191
    0x250507050601050a0b04030f03200d03060503030a0e010c0813030305030f06030a0c03030309020f0a0801020408011506020715090f0b0912010506010e040207020a05060a02011b0309030203090907030e10 88
    0x2007a40507000b46014482c0b0070000c0161002c0c0384225022a60007011301c1e416009907140c1200ea045010148a0480b5802000c10741b04041c0450708444460340d41d1820042c0e240d4400506883c7d002d40d2140c40085038029554401e00e5020b420040e040e207224000d12840c00c00540d10402e00501590000c1e40001c50200410001e101300c2810a508100c1c118000c00c00c012440d03a5450710407200740001003c040e2135891020031525200d05030125460001c00750390045d510341c00102d000f50003d01c41c05100d5030901480e42203205206840e1000ea40c0c0700d502a00d9110f040440101c2107903c240e4500081100703099000810413030700d81910010303041c4402c2090ba984100410090788000c000000080ea0345030409101050fa0014442c0d07442e070105640160b211151800010b0801040f50f0101d9041800003a0034000c1d994103500c18903e070308520340d07821084401d6400460849091000060150340104040d10081c50004003e07a88018075142c0811008000b024103400c00d08020315901c69107840702006403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 15146670 1250 15145420 15145423
    0x302060108160e070f020102070507080c1302041514071401050412030219080a02040902030a05010306050903070b0417091c0203070605090102030f07060e061e0705070506060925050705 81
    0x1000b04040144142460400c54405100030780a4141301c00d1040d07400b05101020300039010748220507000320035601300c2e41d502c1d40055145d80000892030b1044804540948041c1c0e880d03c2030318180c943d110741c030b060403400842050755008044100030300c840c1000d000000001d800e0740030300c4250a4440c000460241854070b8110000050034108400345130050054103611040044203a40e44402c0f4548401e064480c029040300a01c680d8004185990001081021081c103a80042c0e049a108a20820166854410340c94603030140c03100081031700712920041800300d15402800103101030244035081c81d041c000800904a0010a0000540c0d103150b071140348194502481031500400b118103046160004042c0004c1d01d82c401c2039044a08040089203060907c8519408100340081c214216541d074104003039850300c0d60314280140c48808250000113051540304070b040d1460359500c480282091340310034007000588107008203500c402c2541c03d50040c1503081c1010400f40b807241d494407034603918001d50034000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 15147920 1250 15146670 15146683
    0xf01050105010c1101030c050d0c0503091011180f060301090b0306070e0d0f0807050106080723010c0305181e0a050d020303030c030a0e0304090b120105071407030302160302060108 79
    0x40d4140503008490030003084c03c104d0320403410003091034001940d03505490180c840e40a10b02c6039406503890426091611a0040004e500031600c44080300e2144001041507000c1e14a40050111007140602401d05640b40074400900c01c1ca0005001041c034069081c04500142c01c240c1c010780c04507880306180119820180f200c990020b02c00e181042c40c154441000ca4a00c0c1d9070604000d25030354005406000740034060381900c0309550b204c4000d2100320350312807046a883c441130140681100c40300500520820721024503000640043e1100805004070707440540d15034115001d111603440d5010703040400c0f50f0b121003030449480310ba504100c2810036a001400405400340c1c0040d4015a0b10030030f084090394000003603c0e80a600a1026540c0b0f44d601c0101d000506280b2104101c107100104011400c007810b900041c070b460100755070001000d0140d000041c00d1b18400d441041c081b803001c1104038240c4209074000c00d400c42c000d007005490001e00e40714504861031174000c01d400580044005000402090040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 15149170 1250 15147920 15147929
    0x60d0b0108072c03010e06010e0402091f060804020f0411130b070f02040908190504030b090d1e03150b040302040c02060c0306010e0d0209090a060b0102070305100902040b120f010501 80
    0x1d50b10070155500c90064459403c501038888001a2003400c5150380c094006501e2603204401341d40d0310f0f5035110070b07104100c4001e80f412031207a0001030000e0a082e80300310800102e2510042ea50445a290042c155580310024009982101030180b4004c06602c4600906124001c410480d69607800d0781c40c54170541d042da0341c0010813582d00c10000480415032b40c0d03a2042d862601107500061700ca40c1441c081050744683d0012001940ba0110002d0785150042e0161080fa40144880d00c2d103503403118144c5460f14006030500010407040c54000c1007440b00351a49281d01c16660800140c08807859864135902d4a16074030000844400080038411420a40204c00c48411240010000760030514000b0007607000081c001c41c1088207808a500c826614000300000c0303560081d21450407400e00c120443e40710103420b20b00784c8a403030403d8059107655100050140c1160b4103d400740c00783d00f08800260010b0f000003d0103a83c0940c83c0c52049419603034074804c0e01c03071440d00362004285042d0300c0c40c001030960348140d21 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 15150420 1250 15149170 15149177
    0x3040c150e0f040f020705060103030801090b040b1f090b0409060312020601030309290406020d0201140105031f0608030a020304030308010504020301050904060203060315070207030203070510020327060d0b010807 93
    0x110742a05440c0c48041c1812114110360219089403400702031402402035050141c007900c42c44000009040c3c000850034140c91a2800610984400c0c0062009480c0481c280b9a0003040049040c01c444008400b6924000914641030404039901c1000c101142c01a4100d4030029669107001c0040000c0c0c940803003c0840c44d0b0000e8201903140d51406010001c1c03510507000e08000e0980301c0c3c82118443e008458045a42d00c459903129501c50342d009645451039882e000156203082c1c410703e65030858158940c100c500c024000c00304c0075504032206c00c0008164440380c009a403551800310380e0a0040c00507204402e205d5001715151891424010201c0206074843c40c0603a01c1040140150303202d44d08001c1d88141c0021f00580c0e01d440c1d40001c03c0c0f400f10074030100320311a50441e003401015903000c5082e0382106e0007181210300450300c2d0010409848a41082000940e104010685101c18002d00d00c041d51042e02c8910040c0d115403002040142d0300000c03040719807075625100040150707040b03064103030003050b03928 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 15151670 1250 15150420 15150437
    0x60206100602030306010809030405040507030b12070807090e0307060c02060618070207060c08090d0303022106060d151502031c0903020a1e080c06041707030804020d0804030203010203040c15 84
    0x71000307900c81c40b015055604000da85000164210410070481d0000c1002610802441c94041f0b80103006101d13044050b4411b00700074400d150040b100003400344c15140201d000d010814640907944e00140100d081d00302c100d0000f4001800803d00e18400c030003000b00c00c0c1e0060a66843c0070000c1103000d2001100494410351424280080ca5500007500819600a03041c0600360219505110b0100c0c0500a4040d80c00171090506800305176040c1c01510001c04110002e403c4d40c06001c0d0406112481200d607075405c020144504102c420740354011210103148070040e110780c540c4a401c20340e03100d07035121a6607025a000083e0b00e80540240004190071010b02101006034248a54000b03440310a1041d01a05103040307101c03100f00030420600702c10710302640029000d65544d070250300241c032081c04417070a60700540841901a41003200404481c5500d5065036800c00035038aa908212030300301c03840401c2d0340440c0148000700050f1424401140030701d02421031510b40b140b5100c50400400e11140880c8204890803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 15152920 1250 15151670 15151679
    0x306060102160e0c07050f010603050708010207050a080d23070905120a0f06060506040906050315040b0a0e0a0204020304080c06060303090a0b090d0c0b03040501151503090311060a0606020610 84
    0x2c1e294405440c45180007070705039180c4030b14001c5a8010694040d21a00420f01000d0003d4415400582103912030b10a8542465543c00518200e008031100640190040d00547c40042d03e12001809527461020001a0804040102c001c5560105002c428203807217170018032500c1900f011060380240b034121000e5451411002070709844484d400c40090441206a10b690b08110172038000070040c00d400f074981c54446944d1140030700584424460140680101d0703007008400007084520314403e64008440c1e035041e841d281b5943c00202a64402890980103070b041d01e000583e6240015400b860198078484c1d11141c012041508164008d400c440c40fa038820030006595403181c0b1018130480b84e0070007a40785c40d403404001082c1c0d04400035a0081540003101300c04980c0c9a681c10180d070040e4000c9000700501484011201e044503c0d500072003401010580d02e078000d45110750469041d840c4a0700d44140c0000092012620b0b00f0b10540d03212440903140d0109008840c0c3c10800954010001404501c5c001e241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 15154170 1250 15152920 15152953
    0x120b10120209040b030d02101506091203020a0206040b0702040b04061a1812071d0103080403060902030a1a01090c020109020906040c0507080d02030105090a1b0315120606050306060102 81
    0x15111010049a008280b000c2c66680320f5024200400c0040c0654082c541e000308002d44448000001010140ca40400300041c0c94141d03428100f17880741c075200c610a01d8104140b0107844403641c10304508511074055810016107818001d80002d0188000260b16041c484c810841550425a078142c0154a0200304004841484019503c0c080c1e1441049076541680e021007000302482440c2150002946190306071486c400041400c01c4505412074100302500840c4800101c840038400902102e00920040c804600070f07606c080e0581c4d00c011700301c0d150600c00742c1d11800c40c40524906c00c11464542d0004100d0440750b8026032082845510081119030459800141e0b00c4401070100741c041c590707800c1002c130010b000d5411a00b006401c0603156031264400b00901c07000c0e40c400d0080c0780c011554480864407201c030f0340c061480340051459a07400304009005c000c80c0102240c4a41241600d040c5100180c48100041f040f442140038880228a4074101000c1c035140c8a00030f401c05045501025030028080c1c4c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 15155420 1250 15154170 15154187
    0x90c09050f040605090c121b031b01141209070f05010e060708030a02070b0c071b030b07080718080318010809070e070302070804090506100302040b0f16060903120b10 73
    0x20b00030f1002880c1e444503068685012014540e140e0044c0c884c90522103440400582c100603031440e06401104441828280350b1962500c0d94003000001407142d0032081980902003a500313014061401c2401c200c000c3c0c40c400710340038081d00d04810b59000f1600600c80c0004101c1e030480904001c0c24548210a001004500705110344c43d00582a228044046050380c0300e241c049806440e0070080c005030505001e502c0d501554421f500442c4c107000704000a1290005400c2510100c070b800103000d0189645104081d145c42130000e00e0709082040c0d041142102080d211500c40241901000175a08d070b0f140c0c01940c10001c84010700c0c403810f011410b002c010102c01d001034180c06a8011144c524459110b41000b50064010703194018621840858040713280c2055900c518420801210012070f07401407114150700320300c1280100c200e07040c2e00308003280020b00820028030190000c02c03103000700d00300e26880c1c4004850710040c044000500100c9141c150680da40100700d1662811620421101b0a10b00060705554 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 15156670 1250 15155420 15155423
    0xb010f05060406030b061201061d040b130b04090203060a0905070905060607030507030207090531050d11031201060203030f16080105010c020609040606032003040c05010806030f0102040603090c09050f04 89
    0x580324a45ea00403901c840d010746080b45a00c800402c07155071500c001070000030f0a03804c812450020080c01c12450b02d410702903403200d120003a1412908248501840024001c000c213a1504283c4520181c40117031000c004070707403007050344000c0007505085620307005041007800d501407440a4180002c1c41940da82c0d08040750407060b4103051080d41c0318218601642404016801000001d141004003c0e014a000910709a071055001c00000013000300325031001602d00c168409083c6600c0342d040c0c00e40043c0144403400d106c00b103400899040c00d030204c000002a0704240c20843c0160404024442c00d012404071954125003914400c1c0060380c4100c8004001c03040511600e07040002c0c1c45c41e40820354665504507a00744502070014460f103a01c0c1c03280500a00b2030312100b02151003400102104441804080ea4040d542c0f2200f0b4101c01d901d8103004442d09034001e0950340e4107000d031002032001c1d902e003403000740300400207078030003142e04141424500361030070103a800200e4440c00c000c1080150400103120942c0315 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 15157920 1250 15156670 15156677
    0x20c030d05070c090c05190219060b010e03030708070c05060304170a0909020a020708060612060408030901020f1810050418090602090301150f050f0319030e090705070b010f05060406 80
    0x504030b5082c07014200d6402c3d441070380094540301c0400e8900d64050018002c0303a02c80d1513400c00c01001ca903001ca07500c140000c508000300c2c1011040700d00107007803a040300f44160300500d4080b0541d0400c00000f411640a01401c0302c40900005a000400041c09609401130804941c3c4c01d0441c43c098542c41e10110345009020302e0000300042e42951b01f0f003c0c0241c1c002401c3c041d00e0031911b4120540000e55110650300842c1c1c0d0714442c0728001600b0b458102c10400b6090300c3c0502038401a110340d61180e159230005081e02c00c4c1950244002c144d08105000603010000d20071441c140d05803245800c1c0401d05036030115020030010204000d02c034000d8030381031200ca0084011800030310203d103818100002e0242c0000d495242d400d06105119425801d40503100340c80009166041c0700e541c0c0c174100143e070b01e421618250550446006800241d0240c45c001000340c2c0641807030600c031721100002a034040d1040364010041000401c0d01414045002045070240215a1071009180e09010002d44140110f200e42d4042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 15159170 1250 15157920 15157927
    0x3060907080a09080415030509070807030303090c1d150f09070804020d060606030c0210020403170a05040902070c03053a020708010c03050103021c0206030402060903031204080c010606020c030d05 86
    0x3070b182644074100a540020308252504c1d10b440311100000313008240380d0002814180441c40385c2d100407406004480020b80100326051950b642035005d0a0108000e441e0b00342414400509802c040341d044550700b0f85082160714607d0041e202c845001d4020020500540389182c0894060322182201764100006007048809603a440c80090301050f0326040040075142807600015280c0e4250304844032010f00f60302541c00600b8007007914803c901851101400a41c9181d40b00030f0101c1005000b4030075541c607407510f585002e40310003056041c1c4c0d200800460f00341100901c2002441400d00a0541601649800740d000540c0490300d0390f003600702e80e414070728501c0580114000c1580200100001840004020700400640040282c020003091005900a014582c07003d103201404100d40e08495900504a9095455507001e115513608460801c0360944000c00c81c0b60720407103124007098425445800d500743d8450018240341d0030341c0c1e85607002c1400d550047c0303c200e4440c2e802203109009802c80345829900c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 15160420 1250 15159170 15159181
    0x304020616110d0501020904060b0f0703030c050c0f15060105120a0c020313080606030d050f030f0c07020409061e02130e040602040509010308070201030507050c0607230409150504020306090708 85
    0x80c2024803035642d031003c540341001d0704110041d0013400f5441800c440c20004169030b012102d07501d101300b070346200700701800b00001c000280c001d40c071900c042145841e1903801c100f0b0b4500031038908059080364800e607900c04c90003944840290013000d940700000f0300e4540d003040074901a80040c04400f602e403c1c20241c0f81c040091045108000355444181e00d01d2000c2074150b0b6031581513840e410152030726400380c01484a0405014062011203204440c454105465641c940045286004000c1c051071980d000802c80b0340d015135a140142c0c83c03014004d4000148440c4100c900020320402100c81841890040c0401d0011408411a03501100d4800100305415612803138007500a108640140344e01104500001c418040c1050182508502c00c0e00d0420039a2100300301610b59004540216516602140c00a42807920522040e805994920009030005002e030821754440e82160304a201a19500c0c040303141d01c5000c0c580b4400040c0000c1e0303411851030805030301007402100000d100c0d0007404600c8000c40c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 15161670 1250 15160420 15160433
    0xa050711040b1504091a010206070c031202071505010503011802090406020403080406020706020c0301051005010c0314031303090b0304050d0518030601141314010501030c050c07080f0d03020304020616 88
    0x241e0308402070480d03a0a1007a12080000da03001401768030082c0780b602040104500c41d503000c008903044160014809541c07070306070440c1e40400d1501c04070200401361070030030b00ea5a890300242c01c0703107407007810903c0015482c1c80c024011920b050f0701c0350388260304110010405040004240c040f2540540f1031012030b07a51414200d01038840c40c1c1c4003c04541000070000b402540c003045d0f200503140c0f5a403d840b04400707024209802e813541556842c480040c404000c1200f58040c2c48a034902a1083c1403080d032050340510860856001202c41c191380a0302d0003000810503a02010301009080301a0001d0b0650600380c5035190340b81188611501803000004a126181c20a0031244005c08001030481d176456840e815180443d980c107601c190701606039030070700400d0300701c09005040c17182080c1c030a029082e80c81d10380110040e105401e60341c0e081c00010442e40f00502018800c1102070500c1a0042c1880030703038030484074544000d40307031034408151061050000580c0d406c002c882d810410402c01195420381c41c10300ea03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 15162920 1250 15161670 15161681
    0x6090c100e0d0c06090f090605090a0f09060e0d02160b09090408040801050403020106030b0c07030e01050d0b09010e090d1106060f01110313140109050105070b040f050303010801060801110a05071104 87
    0x283c0303075007031441c40012115400a0307024103407482c4011400003655220142002e0303600340d00800e0361210403c00000e00140700740c0e00c000c1000101d50408540403405844420840303c6e589080000c6402810001e00f5080e010041c00c6030110500d20070264081c40e0401d800d0790340c014005198071401a0130041410701074120103840280aa540c0200700302d003480d2030f01a000382400d1200701c415200200025120000351030070f440b91144c1540300c1501d105c0c01e04004503465400382c205611050354444400c42151160b118640c003801042c0886160750400c0d00380c1d2841c02100e140d440703081100d1542c004480c840c0c0480d00c1e44d0440c0c402d468010504d020705005903280300c0c1200d640304080c800490251790200f15160040f044600c1c0e9132004180680c040011551b0100314054940403072000c002c0c040014034807400a5921601030800007261442d240e8855065500c00e074844030b40c2d84c3d150f01c001d01c05800280301e510540d60765041400e00d480c041c00405000c5000e4518040c101d18691940b4401980301c58101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 15164170 1250 15162920 15162923
    0x90809090a150504060608070305070912060509100504020a0311010207180b010905010e0d0b0903040803040303020a050d020c0a03030f030e0303070306170102070c030b040602040b0307030603020306090c100e0d 92
    0x800814075100180400411a208540c5020b01d41107200052600389442000184c80c0c2556440100d80c1d919a0107030f0241c10040c0c410303030421910f00400600c8203034107054000349038420302012580f4240050000e14095201d4a0030804520740b1003440010303900c01410a0440354402040032401030300100503410170000780d1240d20007401002501641240307e5000001c0710800341c030b0f240348840e1507100454501113040013058026a0481c294408141c0200c90f441d8040c0d030050031079203070a864088450440d00594021009603001c1440d0344108401804950444c4803644002d2101c03480c1d039070006a21459a22000c0d0a02840c0300c03070602014402c1d007110b000c10030064126036990801440c01002401d540c45082130318a0117071681c411041c01802142c24040d08014480358460454540c0550b03a9000b800032251240c2c20400002c7c00c0040102441c407c0c400354500080207455070041c503092000013068241c041c1c0025503080400d035541c2500e1a03000116260040c03a80071034401040001400e07410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 15165420 1250 15164170 15164179
    0x50a1d0c0c16051305010b0409090809031002030708090114041202010906090b1b0408030d0b0d0506070903020f060a020d050a0e0904050609010c05030c0702090a0b090906070306080a020102030706090809 89
    0xb1030103410781907420a081103400a54070042081d1003250f103502111020b018141c00c1e04000c0200300a208840c1e000304c101e590041c45e040c0d00d080f48a40020713186c203d00c40c41050310107030040304020301c194020b1136042c1d00402c800028000d100383c0303820b00030724480b00802c0200000140c4c0503103a038183c070035408144442c3c1d002c807081189504506040003c0c0304102d52a40020f1b00681100c0b054084c1c0b02c1c140c03011039800000441c20500044540790140c88104a05e80e0401c2c0e517403801234007044041014500030394003601c0780d4402509500502c441200d4011f002402400c040114140d42580000d950180420038a466511045030300f104440321100d20402c00e0744001040140404e014000c144d1030300482c0300000030421006030304000d41c2e4501040f00c035008200014005200941070100d103941d40401c2049002480d00942c1c0c0c0001d000f490240e42d0320388150300690030855400c1c1c26208940c0a003403000c4c000c00b82c880d042c0c0e00007544c0b8400c069000702281e0301c4012a01c2085440c3c03003030380d58444000b0f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 15166670 1250 15165420 15165433
    0x903050312042102060103060513110907020f12180a03030e0f03030d020c10050a06030302060a050903040905090109110f060403060e030708070f05070501090e0109020306030a150204030201020601050a1d0c0c 91
    0x30760705c1c00d0030702060b10054030700340200c4c1d94228181f40f400d50043c1d00644810140c0e10350800c000846600802020550044854507285010140101003c20601260f8640c0341c813268002806060403040400740903520541090000c241c01c01c04000040c48101c50105071455901c000c00e00714096404501c0143d400403940d074a4802d40410030103240808203070204015554a01080b0603244a84805030150700300e07001140c54003440303030009540007506c6c80c200c91405643d805240d007112022030b8038440c21307555048000c041280d041d00c01107410744121000650001210001080d80c821403100038200c95a40500d4041c61034203100380c403250350b0000c2403079413254510f040841c03c4140d028000c407000d0240610200749980100120020b407141d0048240b000d07030030700b42041d000f540003404d81d0380d05200302d40c0080d0000d4984403219448010801026071241d1071440007919018040e00200e100b400750318000c1c095602802e801b1484422461440101504e1340e401c04c0c4554801c8161170602c5022b1007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 15167920 1250 15166670 15166733
    0x212070b070b060409030e01050d0204051807020609060603060a0e07080a03090509090604110913020a06020d0906080c0f0a0903151e1a04050601050408010204090507030606090305031204 82
    0xd0058190039004081c04851550307020701300802c46801140040120701e140c001c500b6554803d8002c0c0c20250112607006103029200c0f0005502659440040000004a0410000100d6061111b1074009202d400100b00d5428054006070b2114401400d141089680e4011030ba500d80080011000614030031044d683d11403020308000308903079610b00400f401256040045040345000051680c401c03074201d1020603102e40c1000800c02c1c0381c0c0d4080c0c00b8a142d03081d500c40450250b07030b0746402080180300c81e030014023032029507074005846c5000f035900003018002e035032080006d00103c001c100da01104144203a142d90b2503010505541c0c0f070001c1e41010b0805c00d80403130924074840640c1d00041507200c450030320010080d00266018103540039400741d80d500001550b110351160030243c00c0360345c101d4014100581019100e9154a0883c1c0041e4003d5048685030300a0140c10780e0580704007000341c08146800184581545c90301035491082c01175000150400c4000a028000d0142c042c08848413000401102803038103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 15169170 1250 15167920 15167939
    0xf0e060a03060b1201060f1b1506080607080a0c170406020705030c03070602041802030105011b02040f0212060a0e06061909090906020c01140603070902030a0e0106030c06080a0903080a09021207 85
    0x1b4000c0c080840c0c2e10340702407c09140500360044280c00402d0b400700c02003007283e648886440d00301c040a0341054803082e0125542a01744441482000b0654603a9001d242000020040d100e905000c40103005050283c02d82d142d20f030a8180c0c0e0b01641041c00035030340c7d400610f0018503601c10340903001b94030300020906c80c04002041e00100b00720b803410110802c142c50400162402c900c028030605020442e184182403464640b4180c80f52018002440002c403050240c0440301664800f103810395007558100300b041110300d0890300c0c1d00d0142650b10a031007030f20326041e0041000c501c120410192009085001c00c00050701c101005005000040424070400003186800000b03074204440d101c1095003480445142046506540ca2245100a00038550035103803250710802548080c142e600103035221000141203032401d0107580001d51080a030005a20302e0304034014a040d40241c425140c0b81c0c284240b98000c25030180c6442d4014003c070070000356540c45440014000f0300c0d02441d1412a000765440021a040c1c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 15170420 1250 15169170 15169207
    0x408070204050f0f07020115050118090513060e150601050309010b0307030305040603051f050411040506040b0a11010e0a0209130b0901020c160803040b03040f080c0304030201030b010f0e060a03060b 87
    0x613101c10055584800f00300f0fa099071204000c00d2851030b10101c2c1040b040d0320851040250140013003011202c035844089200c00c0d544105c40c82d5040c4034050104104000f114840c01007021017040c00780c1441d244011101d044058098141c07810030001001041c2c8588080d4014440507038018100d07a11283d403850702515640140c0f1990020902d007000003022004640709107131603903a5070004020594100410803000302842950316003900c3d0103103c0400c1644603000104041c0c03164500309503c030f0000040c01480286090310036485641005280c1d039503000006400480182e0441e0a00c90540d148859030109079051340010741115440028004141c5065000700412160402625140c0a02083c84a0100c1161080c1c480aa108100c00c0140328045406160098461566554050603540340c600181e04210f8902c001500001010030456825100e90040c220342030034802504071554034090020b03003806141d00d014090008041256a1113544100d000e480f05500c102e40380c1c0740b0801080207420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 15171670 1250 15170420 15170431
    0x40308010909050a1b08010f0902090c0406081902070506070306090b010c020d1b03050d1e08040803040308060103020f0a09030b060306011a0c0106030b0405010903030f0203100506030408070204050f 87
    0x501610020031040d245004101803140c208000707100a60311036662015080014a4285480d074200001240e00741082c011206201c01400d008078406c0d24900402110341d02c040c4c401464200c0c00c020070481903400c60f0700c0590240c01076032052042200c11110720003a1090a9008045004000c20842c580d501035001d90184c030308455080024651950054030444844da201961040380c1e00300d0400000c408c00c0c0f14070b0180e02002a0000c0301a45ea81d512403600351010640400306002c0c002960030f030311046112082000d5980741130052400c01c0e44403004903200c003500190411140e0800181682d0194040394030751800c1e800001e81e1010f8500005020203501d001c22030348011900d0101d0303010318001842034142c1700400c442d204020410856040c40b036102090420003035483e1940000410300c3c55020030b20441c064000440c00100c18130b0000c00303c9204068a51400d84103105128101044001885c103880b0244c1e48103039252242c0c04c08004502031900002e5002e41080200700e5400c801410f90b90040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 15172920 1250 15171670 15171677
    0xa090606030f0e070803250507030b010806090c01051c0b060408010b0301140402060307081003020d140105070306030b130606081b030607020a0215070206070b0a020910020303010b03060603041a0f0403 88
    0x3030042000c50343d25204c40b40f0558009900510200c820824500449200003400008809190003640e88241c01c00000ea40141c82d1400240c004005120060010a900414100c06170400160709000a041030254071014200b201d0300314240c10003164154481026040000c0565032180d5075007201270b0103400e107181031a00039403d0920700b09600395a0010240030780e0703004003440d0031555081003c4800c01b40090030b411280812403000809616440c4050012602400b003401e800c000103c102801d40b07202400c1101050700e09a0200041144510042d4100303e040c02c044e820140607003810b1000d8611a0081c1209010381c518980500111005a0701e444900341c055a05070740d2110b03020b80e00c1e9580060040d400107104000c00301301c1e0385454020484284001c10490920f141e0742c4811070b00440c101c5440407100e5001401058500d4680c40f403102e000c0062004501d15070511f00741014a0101412490085002101280c101700c42c42030400d480f00905207084046107040c2e2500641b8002c16103003540070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 15174170 1250 15172920 15172931
    0x1605030d031a1203070b0c07030f0503090d0e01021002040905060a050a120303021e0a020604020a1215050c040b0a17060d0f0b04110a0f09050907060903060b0a090606030f 75
    0x5050203401600300080c04108514401c0410a09101207201440f03050800c41c0410010b100000700c0307220b200c0380500d11420400352101060310f0060b045203400c461000a010f814000c01000c02800509078a03403030814605490042c01741030041c0c0c03070320381a1040000024000f04012900e03031b250740e20451040d60221100075080f07075241c060003078a2816016040040c151000003101190181d00100008601c61010103012046070350000d9154005154060050308160140030a41c980300103880090040e00f561b902d001480c655a000701807200c9040c84004540303a200082030300700701c1c200703a40050000c407102d45c0d039403480f41034000c09031400c0f0032030800700200d00008103101d400c1400e14000860f0f4011981440250031303445121080c2d070014000c81d15524440209400e0303449210801c401000341c01d0b100c202007428100c43c803083c1d8200803c9618280d000d10b030200180d40d4420049800c40c5d422000010b00c403041e07100420001c055a8010b1140c007400c00a0010b1800d5050340804654501110300f08036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 15175420 1250 15174170 15174193
    0xb19090f0b01050301030507060c05190503030403030501090515010c1a04050706090803070804090f0f020a090305010b04140f13170309010c0309110f0315010b120a18030503070e03160503 82
    0x50f03500082c0405800380e0320140003031003007a00505803c00500c0c0150125400541014005200b5420645048400ba0004000e000030103405002d0135000d0f1400c01003e11031b9180041d1083c00c0102c502c00b070541000103100402d01445020324842d0384907030b0520040c1500e440e16007000783e0b45140c01e2250b0000582e034804006500c0c00e000c01903409966100015501e410704d0408800050502500840d140c140d0311881d10262180c0340c8000c145035207294881e0040c8070301d541051402c40d6035002020b4090b0303042000e0040211442c030101a0301800110854445440d072203c0b000c02c480103440d0041181c0e0806c5500741200d86480042e42c480d00b1440001d00840c01719040840640b501e00d80003c120314464100e90100749000c50400300184070240465480c40d400c1001c40328442002c1c7d115494080307001a05400500228244680c4030501901c20b100540d80203690662030000c1960287c20042d0120214059902c158000c4620100080c04c81c4c2d40f0a600045080380d0b9640e5200d581d201e03210b480302c07807076 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 15176670 1250 15175420 15175427
    0x40302091819020306190209040905010b01030b040e0703020103020a0c0501090506040209090f100f230609010b0f0a0305040f12120606031416090b0d0207020f09010b0d0b19090f0b01 80
    0xc400d07580900030306040e451b01d280665000c450100c03005078580d000e002003100c0791228030440280c135018500118107030850b50009002c45580e40b02c0f544c0106d06004c0c10300e44e5030200040c014101c0c1d1b13081c6001a41c0307003040301c0110364010a4042c020507550801e1031180a0100001e49507009600845280c2406d4a03041e42c004e40d103080f40c156030611a004424200d02e0500a81e00640d2505451350001c90315162180725240074a01d800d0340e507010240c4000c14441c2d282401010580900325030300c210b41c9000161030503e80346000b0308030b17031000301a1250000b804000c401c64400303071b0480d0b1180c1444800184804040c1030b0b45441200f018200f480e0110015011348030b4062450817203a503c0388545140c40d03030f600f101500007090761400b003808400b200004105d4402c0c0020320030701c110f40000607141d440380d2042011110001d00d025120f00504001400144046000c0345d07007500310345000145914111001c109074851710010a00c090380310075000a0301d031210350003906c8132813092402040071521680054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 15177920 1250 15176670 15176713
    0x2041a091e01050c0a03120b010e0307150e06030f0901050a0204060903111203030906100503031e0304050a0204021801090503070e0105010c050c040216050d03060605030c09060403020918 82
    0x200d0340030741008650369004a030000d141a80007410314000d80f03042000388103146404000da1040340083e409400c0102250b05a21540504500920b0082071152500c00007039640d01d1980140c01302000c0804442c0b18071801102101d1402a0203008140ca0b403070410346180a185040b100d641082d42000f00007404100705200310340c152121074403040482421615905807613134103480300541046050101072022a030401c00f840c400c403580f0b4010549480c202c40400340c2c054a650005001e0381c81030081d50b11140030640121020208140415100d46d00c41c10030300d103022020080650001d01c0051444405c0d185499208401035013a2505107405580c1c00600da40e0b4288c2e8403031040c504000000500c482e600c200f038a0000340d80210f0440300c040344608001000c9038044204035407a16a01c0400d41e08005060161011002003400c00308446850200c001c0c016200c001d0008031303600c000241e600d1003a9184800d0310055500648212001d2800171142200c0e02d01e8560703911818030414000c05801305481c0345a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 15179170 1250 15177920 15177937
    0x60f18031a0a090c0b0a0e09010312020706021c0807180e0a0b0d020f01030203270309040e031204170408120403050f03030403020d03051302030d09060f02030c0714030a0803040602041a 81
    0x8404c0c005140a003406442c0e00302203400005c1120314504400740e40da8170a80940a5401102c1200041503500c001034544a0320368880b23030540d082682044080f0491124099001c045800c00c000150b96004003158080c6540c011800f0140080202046020148002c94881c0403401c000b000104890400c01800e0350070301c000298030600e1003102c5c3e401d65100e50091a04030401c5840507800008646513042040000c0000c86916030001c01c4450a81c0340500440c0c4500e200900503500c0c01052050225582c07000800141c2026050510303003d254068004a6005225003810b403008144400013030720444e449480146c555200d020721012800320048101c1e8000c2c0d6268008151640084409034003600d001882c1d078600e40e46800803800961000e001c11582c0302c1c0340e5560380c4503003420303c40080c000a08031442c100440d8024000e45162000008012040d02c072014007001800300400002482c000340010000d0914001005120800510750007510980e031101030300340f61060542510f0b8410f4000c0102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 15180420 1250 15179170 15179183
    0x1090e0a020d02060c060f09061006020618032104120e0105030114190602010902091501140304050f010213030c0b070b06120106030501020a05040602160b0301060f18031a0a09 77
    0x211001468400c6220b20307001d2003e4030369428954029905818a030702122078100d0b80d0f43d04030411801007002d00c03100ea400b110003c00307103070300c9802d06400075500c203001401c42c0c00d000340301c2240203440740302001a50350344190701c103055104407904100c4002c218000d503011070300030005e0406106228020340e0441103103c8103940b00d5085030329052a020074a40a89000c0f60802d010300a200701c0e41400b0600c1c01d0140030280c00205055602c0e1060000030341c1d00420006500740c2c0c00003d52003c0c1ea12059240601989400c02034403504c40e42003370781c1040d1a141c8044070541c400115000c02d030324000e860404407400740342c0481d0407641d19031407400144540d200051803600d401000030380c945001d06041c05081044000000c00d25180d0b65410708903803240c040c0001085c0c0105003000b003a0790403c1445420320703004070401c0810303141001c0c0c14410702040c003501c81404903142d80700311304600c80d944410010031301020b5080b0f400c0d564100f9015403410140480d0071f007004480050a03000d841d014180c00c0640c400d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 15181670 1250 15180420 15180433
    0x150903090904060b040906060501170106021f02040f12020108091609020705030c0d2109021003020c0f15010e01050d030f0e010c0b01030b0601090e07050d09151a040501090e 76
    0x20800490700401001128525039901c80114103866510603c0d58280c8601000140103040c440007502c21002440345a0030f42003141700610000c0e134049105104a81030301281c0206110625500c8068026504866444a80c0703460005624046418402102d8002e0f02d440e16103840f64a18030362261000118185400390448003001240e60f95801841858007401c140d0b400c2c076006910071400e07d408a00380e680001c00084045815080c6a4404100d100c50400200082c17041640032400c0111f0705c1416405260b0b000c41c1a0141000500c043c0442d100000e040c2c0b1000c03ca00c0c0311040146100307000b800807042050b8004143e5052a446140003640c054071500340a12210a0458416001e400201d04200b4022009400116014070290185100c2c051f410003602e019800106500b40c075034022942c044c1072600303006403950808111814402d40d080c010038000094240303140f103404a240100000d034503102604c940a00203101256241c40111400c2c007107079a0700c0000320150b4084d004c24002640010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 15182920 1250 15181670 15181687
    0xe0601121209030b0f0601030f0b150706021204060504150e03031f0f06020a02030d02030405150c03040506160210080601141308011401030c0b030103080d0e0a060203070201060602150903 82
    0x12240441d101c1094586128019240d070360300d44540406890400140f402c03907050041035070b054050300c100d4241c0160100035625200b00000c00f41c03506581c550341001000102c40c420300420360105c64500c04416907607000c5040a1601d00300618003150b00361400e0700201420035410b003860007021005881344000b9070858540f40c03440001d8140034000100c03080380c2100000340b205450302e0440700038006034014269a00407801070600300303a07060085408540041005102d2580c03488031001d6000c0a5081d03950300c4000d4845107a10b544519002558000300c00f0075083c010328001d0756040e18180c801ea4a140d5444448007041e200032a0541d02c40e804140034600d003500402c0d4403000340110a9100c981e00c1c1781c81c0c0d038030075406003103486440400010258290040c024006d00d144400e001f000010031051030740d0f2440d190109140500b40b9140110380c4c88038074220690344100009103509070003c008542c1e0741400300c4080d009220300e1241c50094043c0d0704040302202c13845001c0c1031003440068080c501d0705095 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 15184170 1250 15182920 15182933
    0x603030e060c010e1b21030307050a0e090a0504050c03120d0f060f030302010501080601120312050603031b030a020c03060f01030609171309180f260c010606030e060112 74
    0x80c030402c0c00c0965866a091106000c104001c10300b01005c2d071700764812114a031040c4a00000142c51401400300c480b81c40c0203003840c000048aa00004070310b003e0791070340c1d80204110313010124080950340c428800002e100541541d6071016008601c6a011a1500d03810f28060503250031400300401c1082d0f0040c0b021581002d501d07001142d15603151607002032060344841e04414145a0b030b03007060740140e41d280c00503c00d40300c1c01c102c40f5026045c50880300c3e8100c003456500074010030300c0301c01e00044507031103102240d00b80d14100300b40c3c0d0500c9140f040004d01001c0d01d5400c00d41e29000001000b0043c801c100b178640c01030401203009805002030104d0301070103a08540740c1c840034180c1c08804507002e4510024540301000c0c400094140c0c2088400d2200750706282000e80d0301952030078425540d0500700354400f280020910000c00f0016039101c2c0d40180c050b1b0300300820000484d2b911080446806000071000152041035101100b951b2881d1002c01c040c030310303028110f9038a0b0000d0140340d20394403510341c920010422 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 15185420 1250 15184170 15184177
    0x30624052d030106080307050d021911040207060b04021b01050705120103060207050a02030d0801062d030b0109050301090303061d060607030507020303090607110906030d0e09060d02030607080f0a0603030e06 91
    0xb07400841c030303559aa0750551a41e4400e0742c040d592904a11400380486074140181c0c8620324425404209030095a181d080c034400000f82028410f69001031110b04001280c0c02c103038030028004204540700c080001140420103101500064294039000000c2e4089001c0c401340d400b14218480e60901c1e582c01c1d80c0d02d00c0001d40c451305064696109219044005a808000441215915a6410105501d441c0c000307092102c0164040f40022101c59180009418030525501c1c6500d141c90041200c00c46000141c2d03840c07949400c03068155081c04804d10a150305500b201c8200d85200c40030005040801103004034100080e01e0fa1a03002c98100080b001082c81440038105160008040c0c07072518100c080024855840000220344d9048030406030b1715186000c107411603101505801604080c6110348c070050083d4140b4681c54480c58811010a8964480d11071150040783d000d401c481907420140c0c8054012081280d07540c80000c5020300003214a6600e00807641102c4e819210a510f015041c800c0203007541 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 15186670 1250 15185420 15185509
    0x7020f060f0304080408010507020114040b04020111070b07110405040206091003021606090620040510020f03210c040305030904091109010311040c02070503070302010f020703062405 80
    0xc4184038018914503480010341c081d51141d0810380d6142d00c0c01d4803060135100028007540c00d591504c8420007000709192007456000c1d0344040c0c0440940e90307a07c0141d5215509041c001c110b4070410703501081240c070480023818014007072400450f00f034410804100035202c040b1002900404140900d1080d800c4c070014000c0042401d05002d42810b904d0169085517110b90801500d2054032281131806001e01c5100d8500d15100c040680d0001640d0402003001c0c1e4815485024000c0440c058452207041c4203001c040f248040c0304050300d81e90907081700011103c07440501d040c0c4052810801082d02911040c04440489501002450408100c502000300510482609440c00309000c0d2900009550351841640a18400d6842001c01840203090204641c1030031100f034195030211800303101c0760703400282190469609180540081143d0502241460125030005148508100c915400100442d10405100113400032820301e25640c0c5040080140c20348003008820040e40b10b10710310a0a440340600280c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 15187920 1250 15186670 15186679
    0x190503190203070308090312040b0c070512031501110a030305060a0834031104200c0705100302040311121903091403070308040603090515010b0304050114070507020f 73
    0x10154602010484440d103402006810000300742d030030180c000307400e07641001ea024000d41c00e003120303403030140903042000d000a49191940c4000030750b60810381c01111001540002502d0000c0b080c14106841d40c2c02c152910311700120a50034540c803651003550140c03030403040c0c1c1b4014040c500340c80e202500207041c040c2c48076030481c18841c0081400d060401040c00081c0c843d203608071400b500a04403c00c0c84d0300d070700e0204c0503e2000507000c1021a130f5019000c0a0644216400110300d04505461102d2003500e01da41030a101011030645010500480e401007100c03403d451041152081400880491103903010040000503510b0150070241403100500030506202c0b002c465021070400f00090030504204812400601e642e0410310819140d03621010746504150001d0000303504580d42e000c2d0034040d82c0650002c140e51f4040c60070601a0070000c1220340040207407041c50b10350f120603114009034403c4406450071760078020040c8103401e680381010b00c90455540d8060602446508001000c80c495544540c0b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 15189170 1250 15187920 15187927
    0x9050405030712020a08190e0a120b060a030b1003110102010506090403110f060a1a0a050102030403080d0b060d0b0f010c1707060204090609050402010f0504120f05030d0614030717190503 82
    0x410100080c51700002404003e446a404031f1402440c41c5070f031420081c003841c00d280c0c00300b003041d200e4450b075040107910002c10f0000d5991000410680007036940050665940303d02800b50310014896901c090b240a854a070814030b000b1001642614070554106812035400c600090100e0721a0100440e100325600c203864107951051460f0b40340c0441550070040072030381c0341c04010a2110420b5011658442a5500164a46810000303501c030b00441c0701c0540340040c0007e401104204d10b52000e00c4242009140c1c98484a01200b410001c01c0080c012078010704210f40803258030f43c0260b980100c0b15a0001c0c01e0303000010010750035645900312070003c4a14580920020800f020180120130242940d208002000e1500340001880c0e52140d030007100600008000c1404640c030403814445515800c6000c1041044551602c0ea14500c22080d90151a515140c000b0039401400490400c11040880864698a0316221113422480307c24102c00c4030359100308203030754034106880b403030900132409082500d06 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 15190420 1250 15189170 15189173
    0x1212020a1202060a0b0a0f090507021002070302010c080c09210a020301050406050f010608010b0306090402060d090b01030201030b030d0203030f10080604050304080607050901020604060f061d1009050405030712020a 94
    0x6000189040c09000d600a00100420340c1d0311303845881108042200d07030086d41440c01c28a868400180c2c002d800b100e40d1075000065041c0c0c020005048144011b0104550751303061340c14000d0003810072880610020b420400807900109020081e61201000280388100b41840c10006a0050003101600960307406200100c60141e0f40c00e1040368401c034050360300801c90b030ae80440300c3c0300a03541c140c01010900016200502448150100f6294000360542d03c1c8800c81d1228000180710307020300801c8034201c0d41802d2000042284580740d80f8102c1c6e10030780b42400301c039005008064880034400440301c0140c1c420300000707842e950511003c58001402440c0410035a884400140c01c1c100704441c00e0b1819800043d007000300360010807007140d10950500d02a0304204c40303080000c0d10740c00c0c0504040c24043d00d43c81038a50324145c0354420402892041800228080302d500d03541460b03402152130040070614a407002510000e14040d5611580d80a00038500c2c3c07525603940c180348035040005050440c441c4072803880 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 15191670 1250 15190420 15190433
    0x120f12090506040b2203030b030a020d1104050c0406050901080a0b0a031208100e0105010804030915030605030c120303011701060312030504051903080a020d020d02030711070608011212020a 83
    0x10303202030181c00035000c140fa00d42480200144054242c0c51000407000c0740c600e41c0f4040d08010350b5443c3c0d041c0740c0801d0805503400024a0201c0301070f000381d0302541d1214403c0c208400e0b100c0d05c02d1044001d50b824011a512120144514040ca00c10320010410412021025611940ca01640820300c0100002d87d8010040412031042c0140c204030f80e03460100a000d504c4542062241d9072001d1600c001c501880c1c00d00a036095801c0041c0708441c1440008800f0400701802080f07050040d0001103d400b110301406403008000c0d12581c4a0303680203000e55203c4103240d0401c2202c0c20794000040e001185141d103401401408402442c0e0b007000d10b956107420100000380145903100c00b0440d0340d074001c11181450f0828a08001840c1c1d8003010307184880010000090f00401c0c902da2104d000500141c58000440c20240a84590f0891780b0304c151000080245460304036403a2200d61801c00f04441d04503440d5001542c1c3c0e803000b13000d400c0c4448101d0b00200001415080120541189031050700c0341d0140c9a40c070300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 15192920 1250 15191670 15191681
    0x5310213030b0f190209030a0204150f0801020705061f08030a0206070e0f0d030305060105040e0415050106020304060203040312051224030109030815040e0601090c09050d120f12 78
    0x414011000004200b0300c034440b0800d54002c0455680101141001c078142c410141030343e04d041d65850340114810540e40c0d0184420300820342c0140c420f00016051006504425034640200040716082003030108103410b051081d1005250701800602d11512030300405030408903500203606610b10b1100c0d0101d0251001c0c00584002a1103400502450420300e5010b0025110703211201c0c007440404403d030380c032a91022b8051044d150103007030000f410703142c05004a9942c41650410518440110140004c200c03000588088031140714504004590722400b040342c03030388a544140700042c0d06c180009d0000c101d101030751a10b0012141821440c0400250072504103c4089403003550100c12200500702140c90402c0c3c141c0081c504074002c000c84640781e60050b21007180580035030150800c140d45c40150340c4459000d11114071000c01241c0300d5680d00c2084501402c0449940b02c0042c1035040d0010311030502440043d00a0f078495003542c403d811a8004481614003444040200201641c10107080c00d11881203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 15194170 1250 15192920 15192937
    0x41406040807090e06060111031204020105040f0303090305010b010906020a15060f060e1201020a09060c020301060b07050f07060810051014041202010314010f1e0914010503010e07053102 82
    0x4c144a03240000c03803400c15800910031814001145d4400940f550044202c405e40003100300e00e0891a1120f00048503280503540101c00300621409003c03082c1074200e000d4a0440b40b291001b40f165114100044401d104180310700340141c3c0c0700c0d6005030001400464029142400002c0c0000c0321551640f10703601c02c40387c5500c4040850f00300c8615072400d081c9001141c0c05800050000d6241c40c042c4203004090680504c2043d00700200081810b003199400e4220030014068569842d480c1c800608185481e48030109402c58240304007070000a1890150742031a115500d29000380103000c0c9008e0501c0310301e00d01c080c000b000f00041d01180302860444000600040e1003a07260754085d1004920000d4110303604081080880680032004010541a04041c001035801d0030305081c90351500c110070380135404005d800603840d003410811314806807644d04280e81d048a008a000380320702c01c0d03a480360580701d403564020389400c0100300400350302104d0070300701c0c0d05103010000060b140b069184002110490304203050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 15195420 1250 15194170 15194189
    0x151b03070e01020d0201050403050d0903110a0303061d0609160216080303010501030f1401050103090804030c24110c0f1c06020a0f0912020d020409020d0c0305060c0f041406040807 79
    0x688001e03075a040240303092013619800200080e05054401600c507000d42056407052030385076291201014401c58828132140702c46d10440e28440c000340340c054003130801c0313008082507003000049110565440599090280c1009001000b6544a090441c00180c4c3c150f1900001d501c90240c42e4144043c4690400c0010103410300a540c40303504003800141a0b60704086800c04050030500300c00f0103091a0300d100c0f41112002d00b0000340d410003d10341541c09002d140d10103810f011014100044040700b044d540040f0214108511240480da40c2c0140d41d02e60300128419000e41c031400407810b942c01d10034449600010010005650a2000c24165280504484c0111026600424400d0700c0316000642e009030360b941402e007850100c0c18802403946103104100042d219a0084004030150b440c5c69000e01c4101d5005446224410b029007440d04c60a0310303521089540b4817a15001901c058a600141c0e242e41100301005403a10f483c0c00141030100d040e0f141099800101000001200c1008214040044c0410030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 15196670 1250 15195420 15195437
    0x13021815030a030816020f120405011205070f120b0307060203270d0b0a06090513020111121804020c0d020a060509030f03010303030509070f080f0601050d05151b0307 73
    0x30819522440c140c0d403840c0079078890411400020f80180c0d000b540440903e602d0b400010100300c040f031800e80c903400745090900031500c000011f080d01800030030944100381c0715001c003a00ea03440c0036000c0700c00480d55600010054110b102001e480750f134030030350902d5400c4000f19201d800390340040e003081115403099000da0b00008200411f01d0070700c0c144400c102607590200d04040c09420103e6650400030034010710919042c00020b8907818594840000781421440c1000149405c1c0c0d0507481d80010303408140e021510a554840b0800d00004000980ca003117004034904001503140302e28140901c11418550088d001d12180708815403c01402200c1d1109074000c0070f00542c142490011114060040d409580081003292100caa255048a0459615140000d026503551941034104010b642120000c580d10580000c1c180c1030000780000e07035654180c00d030780381c0341d9882c0c041100c6c20034810001486a0441d0042d0840c680c88407501c540c1c032980030f8010b0810440214205c02c010b44c01214014082480c01c3e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 15197920 1250 15196670 15196681
    0xb06040b04030308060303040f1e0f0e071101050606090f01090801110403020a060806060906030403030e07030b0a0c0207031106030702070b07060f05150306160c17030601030c0c0b010608130218 85
    0xc05542018080c0c6c061440d10f4180340c42e556040305d0a000351918049045850003208400070790800007059002005c085050300c510380901f01e03c000341d031020002080843d10641422040c0b040e42d0060384010005803900d50314405100341c104010440311305119520000144400c0213002d00468801101c0095507a2411441040305080043d000901017100400c2000300c0303030f2114801c4944e40e02045400c80e8072560359180031000b4050003214a8014040c58600004001103041c0c031f01c3c046d180e145410b01000c82d5150b4201d82d140352621002c0c000c20100340344040b00e410010021504007500741b040c0c0711065120301000358140d220000450304942e136021102c0710348415100300d54220401c201032803110740c1c1160010355160000740050705a02902942416528040c052a001003640a01d45981d05034519403070044940003221403902080c101301140040500c520030888049034404012400d90342010022a44400014601d1880b11100344070034015950310058004441a04c0c0350032200703032402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 15199170 1250 15197920 15197927
    0x1150806101502030a050708091008090c0d02030a12020309060309070602010b100e04050703020d0914070f0b0a05030a062d050a0f0b090f0901121202030a050d020705010b06040b040303 81
    0x96400520207208407440741000b01d501204030748803030321940b0b0800d80f180c159060860f5240b04000303040c1d0340030513000d424485040d000202d2510070140f6209487e86100c15500384000309807a000000d6050308403410600c00500c00b40c42c800039200301c51040300c0c18420700b80013055203588156000c03160355211080c10400240d09008400300840c0c01e45007003840c00000c884c0a0550400e03600d400d88115140c80009884500c01c2e4152051094105030031300488240d07050806182d600e04c00c0180c1d0300c5c002e40c400401d81d000ca66105404454008900502c0c040307151034202d909400c09400c4405c416115600043c200100041d419049040c000441d80d441c418103040020302901584000d000d42608442080742d206400c881c00c08840014282903940d042450010744080c402d610700e254024146000800c03e64408203000d02858450400c0038060b03900180b06a13030760302800c280d1000144040094040d41c94054019100785486540003283e042d00800002d600d98205400104014201180400c00d140c0d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 15200420 1250 15199170 15199201
    0x60d24090c0e011e12050c07060e01060302060921060109020d050a060602030d0b0d020405130b070302030402060702040b0f030f0f25030803040804030b01080705090703020307020601140301150806 86
    0x241402d2600070301101c00e002911081c0110407100381880103644000c013a03801121800c03102d10800b101001a89014010340b12a80c00c41d40341a51040c0c03900b8000032003c00140f1640066a400620090600515000b048801140d0182c105031450014451503040c05080101a018062034080940c454209610f840100d81c0e00030802c4003110708200301080b21a401008030f8180d441d203040c0110355807283c0d0000c40c15103641a03070000d41082c84c083c1001240421048542420362248100380c0464032840c504030280e00003500c010f0361040c2d04210070b17001840c01d41d201002d40640078142985a007070910000c1d0074040c40340c00c1208580c1107521490b000000a101112410408112406890182c091000c00c401400e0100030400318001012800388642242550001c40d841030080ca010360b120085540c075940588555409600003102090b0b000d03000b8000e0b01d124240a0780100310316841c06d40d21407600896200016015540c0d1850300e00360980e211110f001602d500360040c011402d010814008019 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 15201670 1250 15200420 15200441
    0xe0f0a08180a09050720010b090106050c01060e09030a0306050a0303090905060d050109120813050715140703020c0423060103050403180f0e010602030a05040608060307090e0a03080c0a0509060d2409 87
    0x13407402303203010010742c0c441074030301d041d42c0d42403900948482c600d520a42c01043c01f90020520707034848d2002c03c541c01d90300000604c071600c0c8a07a428480607580d039080c050050224040100070445885060024031203c0d4009035003c032004105058220168980078210765802905a40f20b001e05009803c119030450344194210400c0044260740403041e4480c281c64070b01902403011514a64200e1080141c400c54190144c0300385000c0c0681d6824207450080c5d40c0d1814060400e0007623003842c0c03081c94501e0f01c02008201c541030003007140b030302c40ea91701004400400000b00b0032014006242210000d080d02d170981440a0a49058189516410080b031076024240c140d0040c4110f60041000015943c0d100050b2000c44400782805400d980350400064145a00b80d040b001d4114501b10902a110030001480c0030468000d80341c41240b0748030700041c4042ca1244008007070125101304007044450422000511840208510025019107071021300d0300c02d01d861038141701d5040500ca030203001110172032144c0100341 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 15202920 1250 15201670 15201673
    0x705010c0905100c02030f0303010602100c08040f110102010f0f09020301050c0a020c0907020f0307150b0a030321090609060501080f0303071e120c02010e0f0a08180a09050720 77
    0xa141c000090500340f80d4410708001c12007282d040404544040000480b52082034003038070744030347e1201002581c8030440440c45035240d0a05003d01c55050161034294000d581006030b07601101600c0d120340b06c000102d01d03200c504642d1ba850003114100c2140c4134501c0341013030240000c00c1e030204900415081d580003030b0190700150002c00580c00350a0300041e0800144506031096101a41c0d0707510240e0410104901c0c1026a000000720001003162180e00044c450442403000c012080000e42404285000b9010040100d100348010b284034410400000001a00e1107d01203520000e41c1e0340d43c410740c4d01c00c0400b100c07000d2300c540041c070540c501030200d0340c03045840c60025419442c046070007e20f40c905188000741c035403001c40303845503541c0d2051480413021808141d051154030b904900080c000d020481d1003041a00030540785c5400070402090400c006038000c00010f0034003c01d40c0c0310002645a40f40c055a00c84200d01000503400b0701030041501c18822034948110704c90100c0c0c10201c40e0601c410900e11613 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 15204170 1250 15202920 15202937
    0x7080309134d070302060a050901090614040201020d0804110d02060702120c01080702030414040b0f090c0403030909020301050108040f0201030209030f031902070f0b1318020705010c 80
    0x562034141c00e032428080e00c0c51011400015880600c03601d8040044407034002074581e0303040010020380316560031802c41081041003200003a0402c1507030700e000380c45006005820400218a100d5026042036410203615000050a40303460340e00d090071100402c4140d04400040360410044d5038040c450034494244500301140c5d10f1a050740c441c0012401800007038030400c0315031003e20030340d180c1d10251052107038054040e0700c0031601440717000c2d82c0b02c1c00130f40e4907400906004009100240b020043d00d04136080740e0803001d401c2008008000c0a00203030030890f030300881c03e907482c185556115207081c2d0151038864021503071517046041c001c1400b841d540000414a004000402482e6032195840e0380c0240c20485401e401c0350b0b03901c01203002e0310030f401203982c0c5403086003a06c40401c1c0c00800103000b804448421401001560402030341c0b111010f20640c2602016500c003003100f00c00a40c01040320b00c0e1020381c610800f585030f4915105206020010010b0203078040b03445420000c09204003511101c40c0d0425001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 15205420 1250 15204170 15204187
    0x601030207080a08041505040b06040f020a020c120a06060b04080f010902090703020a1403010605040501080f0f0f19050c0324030606010c0203030d0903031e05150618040c03020a02070803 82
    0x101c3c03095195803010071804100003010711400c801c503001d900101030310603c2a8201410042c01c0118140d40c2680704600e05204602c20758000d200b145d061454940103010610510410800c02c112440c505c103086014208003080041c45034031442002d40762098005440301e040c0f81446251944911003d041a80340499001c003581d18001c2d06903001a05240c090381d5101c0c161310480b0340481020b0540303203c0e1004400030622075005000750017520001e0369244950ba5804120100e8180c00780c9615100b544a034000c10012205802e486602003603001c0005003500420015108035001241da500c0c1e01e11001c01405410860059005181010344401819080d580c01c0029140c040192850381400a1001102c0440d2424425142c14810003a0f040243d1031a50401801412010921184403406083d003480d6244080c450b09021314010341000d420800c00300d0a122069000311241c410308084c035103507400165590300074000314161a580150310382c0007200300a807900016401a49950700309022895 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 15206670 1250 15205420 15205433
    0x5060106020f03030a0f09060f0b0f0603010b0a0c02030f070303090509090607140306010306090203011203080c04060e040c0e090403020d1e0c02040218061803070f05010c0b0604111c050601030207 86
    0x2038024440030b40000340d046c82c80d10311400030305030440010f05990501c0400b0500300e00036402080204030995000d080c1c082c441d02040528802401084c0050406100c81d0181500c1141c0d01c2d2034240c40a01151208025406c1a0b40743c04080d900840c00141880c4e4140600d04040103904d80140415004200390b086c2a18003411425042c60b18040304c80c00440042c3d4281e03c01d401c00360061503085011543d95841344445c3d011510105415008502c05001040d22812031000302e808031005503070340c000e0b200000000c00c4050f1040c042c40c4410000200407074043e69450480c000e0107184079400400d010700c04c90b100a0120401c0f903d1300b00072219201e004280c001e81000e8040592541250300607606e0308110000c0900c401c201682903040301740402c0481400c038101c0d190419107441107044841140c0e58211140c0d200002d4010503000981d0340c650000080e94010201d600700c140100086030008a10710100c1843d0009480030403840002e4451001002c001c1c0f0840d130700114280303002d510b86443c1d0388400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 15207920 1250 15206670 15206677
    0x703020312040203190305180f0901030b04080f0307020d0e03030306010e01050705030d2414010c140a06021602010801050901030206030c0703020f060711010b010c020f0d080405061605060106020f03 87
    0x700e404030318420001d0304559080c00304410790761428050340340400ca1418010015000032881401c0b18260040d0074520b458411400d25180340012b0400e030760750b0b00315501c02e142400c0c09001100c58030300501c81c03c451000700b00042c0d0304c14005035000380300340318200b1001070956404017102030280d0810801d010499074003503070400211310700303080c0346550300e1071840c0c17051a622503a214011018900344010f61000c90340d020f681d0300d190109280420458030340d00c0b13003020700003080301080c007207800840b80b040024108601024400c00f480140c0303814a001d0749402d4240d900040c15014809518400c5008568118000307a0240002751010106076043d540403580d6444080c0242803200000f00d90b50040620070000b075020358100c0400d0f2001030502c3c1c44068144030400c48640715650034a141c0ca40154400c0c20404d0000340c0007004c62450070304140501111443c403800549054808110100d62601c0e078200420411035101d0300001018040e0800728106181a000001150402040340704041c0c0e000040c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 15209170 1250 15207920 15207937
    0x50c030c010c0c050114041709120106090e15070f08070c0512030a0f02070b01030b0916060806010818070b091201050103140c09070804080d0b03060907030b0106030c020709020702010302090a03050303091207030203 94
    0x11680d40c903403a000100d143e1943cad403c0f52125800c100c070225040b4600c0c1c00c000d101111440480c0c0540218025400141200300c511400180b100080c4010301481418000c0c1c02c55560b0501848950305912400e041440104000d164640000207204d0040312500c220014080b8807041181003840e903680e640300c4c4000600c0b01420030035840012400100c020310854500100504100161603901ca0001e428080c2c221282c2d40490300000000c0da9001c1951020640c0b0b460b50005442c00900b0314080070303407a0b00561f8803150807071640004102c400301c00b403054601030741c003444034112a807145140c01e510717002071100b10382d004403584c0b01440005174015442940140e4082622510b8101488070040207042c82c034200781e8940b16240500002040204444041e04d006041c44170f21680c89040503401e4030719150040005178400b0004200d01800380e4080c111040c4149405481d080b8100006800040c0e640c00c00e841ca41c0000082c400801e0007007001421941c680c105040c00c04095840107900c0c0d000d40b030341 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 15210420 1250 15209170 15209213
    0xe09070b09150408060a2004080c011206080708010e0115050102031206040908030f0708060108060604031b0503010510150201110d020c0c04240e0402030706050c030c010c0c05011404 80
    0x161000800002c1007690b0142074190119111031804002e001c0140006c0e42400700e03205030305404c50050455242c101c0d81a074002e000184190a0b05030f00440e040ca04041342d50105503500d01020030341d40d02c148409801060940000308402944c1040242180c10101ca00003400050f240100410b0342c012003501c0b00d19200b40700040c051b54034000490b018100c440002028000300000300500e80482d01030480c0100442d03640d80030b4035660305c001524814020b4800c181d00010501007000000e02c001c030f60056044a014400160556420200b402d648040c0c9800c0e48005007200280b05104501d6a6500341006a02c001d20110382048040350b038a104183c3d0ba18143c03500041d000682c504100400c10044401a008201ca0b400003422030b00c07100074041c1940461140a50002107000c0c41004281c05560010003030182d051819005481d20f50105002d40c40c10701041c0a4008066070070710900303441001a40303c90f15403183c140b030b002c1d08480010102119611000c0e0510000c10007803c8030070f46540003001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 15211670 1250 15210420 15210439
    0x30309170a02090a0c080a05060616020d0b07020d0f0306050a091a0a030813120206030604020a0908060112060b240d110f04030b071106040201030b010903080a03060e09070b09 77
    0x205074280420a240650840030b403006201202166500c00f40040a030b81d41c1b0420b09440c0c072031840341540d00540382e4551211003440f000840c89a40c2880721030291004210807030004050341d41c1441300008580c0100981c101c0c08102e0714881e04007218038002c541c03619003004418200000520380368041d0140744007140c0d8405021181c170301000e030380a40112006002c0c0640a580703181804036540100c081c0484045013100018038100b012411444483d0f0040c100340c195901e01080c40001d41080d80d1a0040042200d000a400902840414040c0560045420551400f800c0c80c1003603500c0501c0c05805110800c2a804035174025401507034032070391901521552005071203d0200501030000c2d601e0400e0000050024449006c81d00801c1100c3c4a448803210b95606c1080079202e003498900c19001541146001500540c402da1101c52140c0050500065030f640b6500c40c1c03021a0417601c83c15010a91f0303a6028400d26001081c1d142c4e1000c200001040e200e41400086029401040c0215001e4000760 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 15212920 1250 15211670 15211709
    0x3080702040908030a0905011b08010311030316080909010e0106052703010c1e03050606030a09080403060207030c0b0c0f04031104020c01020705031c0b21100c0314010906030309 78
    0x241c0141c44007640281c0300503100d080c1500c40800a04913800c01f103880390304e0300760350094046030b0042524029400d912821296131035501c03541e14041c0d8549080354180010406011440c5041c0f10518a040c065510152900c1105041c4519050181c10009040d080c0c07000400000343d0040441e44a00c1c0307101441014414005000c0c2c02c0c0441c2035147c15415400c021400010342e43c001d080e90401800e05800d000c0030081800194225641914555044a0f041000071640d00580d0002c0d6101445103220603c0c05599407142c038120b070040c010480c00203080000070010711083d02403994120200c03200c11450141c070202a0b1a04e480340344001880d02400c04060b05a035941c1c1e905907038032401c148000b03558070512890041e450350704c00b82041c0c01c0020360729040003401c00c00f03210f10715a904e070103082800708810005003420700c000445215a514880d913245610b0725071160080500d810190b840101d140240c070030003544410030507084400f040c1c0c9001410070100c2e90148400d02116510b000981051145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 15214170 1250 15212920 15212929
    0x7021e040603061806050f010501020703140a060207080c01050612190203120a0c050708010203060102071403190b01080709020c0309010e0a0b030106050a0e011d10090807090509010b0108090703080702 88
    0x8030b5002410b07807460203e00c1403218001481e1400924461002007155540303407944111220401c0c003030640103912105092001520340580707611411882000c89920841c240d0307a4400ba070340700c150704071050400858200c540300c800b4040c19400c40c41c03c40d44501040b14100c4480e68404406242c1c400e90700e45030952405540382401008941d10650402ca41d9400444e00050400c0e10300d035104a50301c2c440c032800014211818402d0340d00130b0b0b005901a00c2014503209500d8ac036000c100075000d903d030051080c1e45080319000d80c0103481241c460320207200349600d40401a810105542d10805606004000401a406010040380c039200000d003007110300901c4920215098114035044282131706000000401c5076504000505509040d40e6940220340c2c3d03441004540c02d0924203002c210390705010030000c4441c68010307010910242d441c43c0052102e6625580c40b07190110035804642c840c2d40c1d60041c040a49002e0040d440c65200a013014496820540425a501d0009100c00f074407400c40030415804542e107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 15215420 1250 15214170 15214181
    0x40b13080706020711100503010501030c270510020703020d0f05010905030a08060301050106050403050a061a04020a030209040c030b0310020a0528020705030706051e0d050c0d05060607021e04 84
    0x10481031003034680c001d03450840002e6021920550300c041d200303010f420581c6003410904900c55810b659a0781107074030704801500031708585d44940c0280325901050850808410405d07691301440000c04a0505203014288104440124200c2c004c42d001b0440501c0035803100500680400d50101a1071030750300c41410040c1c01003280010081c0b0b507000008081c01e04039444400c0d1402410103c00070803150760380b001c05a03410712803444000e20542006c1c860350080f940707940c00f01000c1c030480c100c010803501c1c020300043c2c200d9001c1034654021a90204018942c0e0801303114100b101c2025040c2005003174205800265208940d0129654864002401d0341d60306100e00150303a15103c2c24a43c00072442100048819035004200d0218018070412600186510300064084211511920782910700621508405d40385064100450301c0341104000b86030b035009039031280e18404c81d81741c00195110441038001000360f41c07003d85075a114505c24400400507980d0b118643c2149007501c0407841c01000b203d400b1074050030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 15216670 1250 15215420 15215423
    0x110309090103030c0b10030f0303020a020f071502280b150a030602040e07020a200a05120601050102060a090c0909060b1f02010c0306030b040b06060c030a03020403030e0405060306040b13 82
    0x6038420000800c264101d4019054948140c1000040380d40364904121034102c68413002d84410304c0c91aa003070209009030f00800d00442a032064030005156181000d28283c0e0940c420f03a0302c060003106040340c042d4184980c2540101028820018444400d40d1f507480f07400d5031101a14848200d8045410382e40c0c44600c01c40084006080707085643c2c1d1700c1c01c021000b034006102d0003203002b085000040b141031011451b411441c1e030050842445d402d661191014051005004541209880341c000c103482d1380740d62054600d000c00500801d200d41c1040002420041c02508000f10181010000c400058615503401c064510024000404000a0034072102400d0b00c0007100e038020f0741050501303006036400d6142081050085c1c009010b9012008012004c9507c6840040e002c40e030368101080020301c51580d80c64100350300410036824951014609400c1d07a100110603004039900040410401d5000007182800c0981201c04100624003903001ca41c0b507030002000280b12500d000d0010301d038004c0d80c50300b007004c89 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 15217920 1250 15216670 15216679
    0x1030e1603050102071a061f02010905060c030403090501020d0801030b13060e010b04060605040305030f0a021c0f08180303130201110703030e04050105030a030f0302031003021804170903030a110309 87
    0x980d070781d0a15038000d501c80c07001940c0b40d1016599030540c00408200d42e40c000e00002e800800007a020b01c440308050885076000300115521601c102001c29802c00405000c1c0c81806a10742d940d040903d0b02600c131091903071159055420030040c640d00c07540c005141a0440c1e8000c0850b00031035881d03800b1603e800d515010001c0605190104803050717402e05601c102280e42c030a40b03080105545a110541b82c4c3d008500c002051a032080240000b1900180040c0005101500403902e00d03000c804440360341c54601160440004058071039040415030310102161700500254806c145803c2e800c3e1035603440f440018950214503021a5400301164441c6211002d03440c61442030710540c0c0c3d22894001e100d100c1c6207000030303c55414040081028540462441307d980c0d41074881e01e000c03250410003507000c0c0d0002002b461540e6062400000941c03152041078014013601542c0d210145003504d80402c0e0030115220320b5014440a129010242d10004209c0b003000700350307080450200d110800c2c1d1901c1d5109810760715400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 15219170 1250 15217920 15217963
    0x6030a241d010203040b070806060403080c030906040e0411060f0306190306020c0c09010807050d0308070c02040f05040b0f0907050d0f12030e070608061005030a090605040b0610081501030e 83
    0x101810f6002d180142e115103200d4002d510344900840b1400703000d032601c1da4040405c020810000e9600f000034040d40040205990509108130b00042040d0803e6010041107032004c4c042004114540c1c40c00354000d07400301c0d540d5042191901c0c01c0c5500d8040103011502411001c510070100d00f9805440c0310084d580900250b60b030310b1412211949a5003030005041c0a8020319001103058032020803c00155040900040f50584040d20100d628004c0a0002018000d05400c50300c05a219030003503548424140e1004107040c280b51906010b0144000c10303440704141c0c05800d12000c05004154007049540848225001030440e0070011110700302c4072401070402600f0031401c2d402580541001a000300a141943c6032690395101c2522082c0f01213803070341d50041103c18009a814000c2c00074581000622000151303000580da01d880c01c9135001d44040d6044180c031001c0025500e4a2602c41c0c005030000d00e05a440c0e41410505490311030070b1524203905068036050324505200e82005540701e088103d0566101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 15220420 1250 15219170 15219221
    0xb070809090a0f06170307170c011803170402090703020306011209051b03030406050301050402030c09041a040609020703091401020c09040f1506051c05010b0a090209040506030a24 79
    0x80403e0b0054100341400d00300c000458140c602814882000010042c507e44641507031000c0000700c501410300d00010082c0002207031301da824812010003243c0090344000600c1c2504014103003079080e00782914020390040402006840301e03450980c20a40a01f00982c981e141d840041c4c45004803610215022460701030b0580611100190f510b100c0c140300380301c60380c50402d4401415240d2080340030b01c102051007000100000d04003a802542c0c4018044812030801000c0c03000a826900920780340000c0c0c502c0304d48098920701c5d04d403085000a10a80701c0440c80c0100d60743d00607041c09014401d4080c2c1c0711600c40706a8950f4000d0000c4100c0010040400f07a05142628101d101e1401184059980c80c0e100308418100301038a01c80c450030f441c00140140d40701c0000c108411190ba66480d0200e850355291100107040c0d454403080c0d803014000d001d6002d40c541c3c1c1130a0601088071002410140f10782d02100c0c1a8000c5030002c01c640b01c0010450003802103417100c10818401500f11800100844a40a500d900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 15221670 1250 15220420 15220441
    0x503040f05060a020a03080402030705042307030606020d0507060e060906040605070203090901030219080f070519031a0c040308030a0b24030112030e030d0201090201021002130b07080909 82
    0x60311085030018144a460340c05001d058081c212101015900000024001c01d00901c0003980c024030080403603001d1a01c03440403500380c4803012445004603805040e0803000912002110380e02c40c103249003c0026518000d0000d41d1a400320b010355081c4540064a54103001c12031304200405600d500444140d820901c20441d0f44010489043d51401d1800002c112138a2010040f100000001040c46400d6400c640801207503400c1c01c9590b0b00d801c100d500e0b000440403020b01110320a1028040a400c1c0c0c00c0c0307418107105c80700e04d410004074895a4041c100f40006101243c0034958040300c02446859685c44480981c100d2245410191100070701008102e500007154002c654050301c1070380c1d89c4010300d0b0f80d104c101c884d207030455620b032410707040903c01403054242c0b2040a011940c0039103080c104014074100820b040905461400780140d4450300b41206658040049000c600c1c98503004500c0d20302c0e40c180c00c410141481c080e80000090000f48176081c891103a043c0c518450005041c90340354100a40d440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 15222920 1250 15221670 15221677
    0x3040302010206071803150906150611070e181203010305060604060510020c09060102011821050406020d1b02040f05060f0427170c0f01150305100e03090402070503 72
    0x200d0051040034001499940304000845110710003007a0206124259540c0040f141003910110302032584c3d80c20b5208c0410b84501400c48074a000e405110803003414000014030101400500240c3c5501140d4104008190303501341d154400d070010290381121080e03e4485050136400411458100d0740400003005110f40030840b1402440200c2e41085581c3d5580144211069540301130000350b001060540c0b42401c1001d0f08030382c480340503c00000d15001780d00b0000c5c52503403e52019a50800c42d030118074842903a0107400d0903030070b0f100c1c10b1a90502e03103060002583e070700c01d076041c0d04200900030308420002c030b99007070002e180740754014002d02001c9204102c240003001c04035459131042841c50350f90b4900b4203092060803440020b51420300d8840c00621080440100c030400210b81440203101d00d0300d0300c1000d400180c100b01601070094150742403184107407800c0d0780d1400d038201c03408884200104001400060000c0c40030003032000c0421002c100181d51411030007003103886a0018000140c44c000c101e8084001c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 15224170 1250 15222920 15222923
    0x4080705010f0c02010c030c0c05030304030b010302040510030c06121401080d090618090509030904060b0a02060f0105010504050d11031b01030612230309100509100c0b070516080408030403 83
    0x9084a40c900b901c0d003102e0442c0403400107404a82c502c0380c0d0f1008603100c2d41004000d113010b03158602806548801291455020303034401d4030b40382116030050003140b4003401416003140e42c40b09595095802e68031000c050407454400d10301405031481c0c5551315009a034120440851003003050604941c1d480d550726403200880c4004000046403081d000c600940201e111000c0b91140b03050860499003481d007a003006140c042d1000001e44400c3c415050284d41d07034003541000e00b0400080c251a01c0441001a02d496000380020340e2132040f0780c005001699220080d00e0403120308440003022101c4a041c5005a0801d001c4200e4040c020b94241840e2251342c03050b2541000001c1c1e03810800d080d502c40c500d0b5590300f103101c0004c004c0002c849945c18041c140c21418a103484130101075a141001c000005281c08101c6108500411130100352809079240c8414008000c0449083c940ea83d91f00a03a140c4080da40024040d2052010104078405012044164507401d19807103140d10b591540c81e0309a20303030780760441d110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 15225420 1250 15224170 15224177
    0x1503021003090503040b160503040807031a0c160609021818031903020a11030406090e0105040b01080708070905090c040f0f030f080706140a0902010e040b03100b0105040503030408070501 82
    0x10152110703100b845104401c80d0407001450030a405d19117000810340c0a40c1c58000301e207602c3c0c0c980d18003082050000f000140400c0e0000c00030b1a1035480d1488aa00405500301d03101c104000c200070254000d20101c030404112103079880c0043c0201c0ca004001040000030294100500002140f070151900c0c0b5141d004064030b03820804080312044080d95284609140e1081d280d6014900c041940d000360058401100c440c106181011000f0407500e2864005503ca6000141c96900810441e00b01046d805d0141400361804d1016115072000a0103901010f02020104000d4000040d405440b801901010305402814600c99051500e0001e510303821900962076045011007000a800c0d003078100e00302c1160b40c40f409032081d070400c1741c507884030b25000400b0542e502a20303035215040e40c0c00b542154602c100030841c0c000900c1c00403800010300c00d2250b0701b81140200c0c5042d00c04030040d0340014421a200030b580d0f201060b040038190040302d42e0f00480c0d000300e4161101103008100000d0101300d54003559000c0e030b07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 15226670 1250 15225420 15225439
    0xc03010b0a12080d02070b070503040204061505090112021b0a051501081e030f03010303030e060709050109031401200a1704030c0803060409120c03090b09030c060703030b04150302 79
    0x1041010002841205500125a4108000105100050643c0c030050140c0181001c0d11502c40071640360342140d6120009d48004100401c6183c58800da00103800071040c400b020148410011304503200e9a00c095040c44100035120303190103020380451391120001407000c105000c444c56103c1d40e51404610454990042da0010040425a8ad01d014100d401c1c20005105c0d14250801e030060304038901d2900c3c002800100000c03003400c2016001180290310983d030000f083c0c1242c804a41c04c1043c042c02e50002c21800c038004100d41d03a8000850750507203070000f9481508901d000342d524014120040b1954205104030402c28845603207001400c1e6480c1c440d1924590078240100c2001100340450b030040c0824082614003000c030f218217019680c03002c4041c01c001109541602c8204a075224400c0d01d030000350300c0301c94410030558841046e400400302c0801f4542801c80100c006515110742e902840c6c011000032900c182818843e410800d010000a801001890303804106112144090f01083c1c2c0648000d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 15227920 1250 15226670 15226691
    0x9020d0c03050a0b0603011203090e070e01020105090c060a0e04020904060b040302130204060215040204180804080115050d0b04020d0b04060504021503070801092f09040513080301060c030c060c020c0301 89
    0x2401800c0713000f01d00508007883e40c1c3c20310100c600d200550540036000c02c51408030200b030f00c0005158440c010f80c0903864408083d85c00000090070340e400105400155000f143c0394001d00d48036141980c2c0001d003642000c17041c46101c00081002400740d01190303a0700504016001072408203c000038010740c2e00036501c500c04843c40710300c44410b0348118443c800040c1d02030702c4041d40000b101c000560308035200800c04551016010403044a030101b4070f0b010b8444100c0010200f1841100344980c110400b038a50362030a80500d4440015070300c80d9800d802910030038141c0d0000341195541c2c2d40700c003141c3e42d002075411058201402d041e0010081218200d00904c03d200e4500c008803000c2050368443c45041d61000c55907828035880b003002d0314410325a080001544a440082c0c052025001401c803040105880d45942ca8a400c20058902c00b5029400c0503006c210000042024941180e0645d4040d04001c00d42d04001d280c01c8a003840300c0040540f1071850181d030754405581c04140440314690442c001c0c0a5100d90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 15229170 1250 15227920 15227941
    0x1202030c0603011a03060609031c030f060305060105060a0203041505190c0803041202070801020f0d0b06120c130f09020705060c09060412060f0203070c05100911040b03010609020d0c0305 82
    0x2806000203504142132401c2c0d400309450000c680c80780015000714105050000404d1038500c1014165a0702c0505981000f0341584c0352186800b0341125841c14807009195850f89600c0300c0060003594020710300025402d01c80e900030000c4600415135003408441426407480001c00b940c0049174000c00b8001400500318681d8818402001c1e11908501594516101c1d607841e21074a035021650b403401d500920900280150080c4003425400724820300c96981e9000f803051000444103034240383d0740b260200f80042c4211141d44019030781c2c04808041c0070307542c40b00c1c20085a036100303226a10000c482851032401158201054024129461055017200c1c0300351101020000c040c0076052965400050a020030442c0c2000e030100c0462041c0910360015550107220114400c1c1e030320441d42e040104044500d0314040101c20041c0f1507004d01c0f5004104003914660307031244003108045040358400c40e11800d03952004d5a007940004c0c01000e20080856844250031454400341c00c40d01c0c0c124010030702d0600080c010219 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 15230420 1250 15229170 15229177
    0xa0c03050a050708011109010507020102070801060f081608030702060309010605100306170703020609040b010c1704030b070c03050702040509030c0f010b030c15030601050304150f0203220f23071202030c06 90
    0x10240340340b807c0c84040801103030941c201a100386d04501c81c5e0100012a80f40a00c2240c3c003900481f026485075909100d4005c3c170307200e00256248640c050701d00b010040c0322400300584001070b41c11183c4540c4e0b5100d466140c5c2c0540126001103078000a4005217244050b01540400e0481d0140719034008020807074545640c403800c2d1888060b4200340d04010240c400e2030f160b4407110211805040c46950052203840e064502002c4140c0c072642c1e240000380034020f21180d041c1c0c030341d4800d50910b0000b50820507039070300515501941000a00464559004c10fa001805005440590048004440c00c040c2d003d50b1560107444040c80e000e0080c090240d20071800d007000e40c0100003009080e1b1082d4a9615004011115a44004c10503948689040c03c00030041065005022034440312060258888c2840c0c04075045080b040305580f03100c0a0080748820008801d00601050190020340b00405900c103601e0310241c164143c202c51681d8091282d0104500d501f50622002450007501201c004c03050345000d1010350321 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 15231670 1250 15230420 15230441
    0x60608040b0402060c03040902070503041703041d0a0212070e09070203090306221707030305010501030204030f0303051b0703020105040b010506030906010b1e030a0903030e010b060909090a0c03050a05070801 91
    0x1001e400014050304080d4024000c916001c03007124075203a65980c00c0b1049800100d8111856000000c04002203e2241151002c1300304000240d4982482c090a0f4500c0c002c44448030204ac214030000078800d803425074140c0d40c64402e0b03820414449c0c42c1c00742c0020010035442e94240d2141603040040f44545100000b034880c0300b070025001b05003d442c0c244c1c503020f224400d5111007414011482ea0240002d004c1480070660203c48245140c8500040c070380502512030581095040510500c0200007148503014412125501403e0004603601c884c020800d9203c4003402000040b0b20001d000c4041607815400a0b2055000d06508919030740c840741000580c0c401078801143c207500140040c0224250070005001e0b9001100c00818003102500b60608550000c68408820350340c0da00230f4400341501130140c10407400d0140001c000c24260600050118010681881d01480441002841000c0300f000480c2d00c0707a410007203c11040d6640d10740150744500a6204a82c1c80c00f643c45c002480030014041c03c0b4214 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 15232920 1250 15231670 15231683
    0x20c0a020904110a06120605040c09030b0402010c1707020102100902100f0509040c0f080603010903081603060909080915030402091302040f0510060306080c0603070305040f0501050708060406060804 87
    0x1240240c0800c55120320251040e605212649030600c82a500c04c1c3c180781c0108115120400d460b100003810808841460f80302500440c117144450369407541c0803501006480c3d0080c42c038500c60b1a1400120381501c039280004103092034820742000307002ca8950181c180340380700341c1c21250032a0070360300c0f1a804d075946640000d40280ae4034411025150241740c104807121040e2078000e0908194200017010340ea07549000101040c00b00c0000302085500190956001500750003e100040d042c1da001020040010310f600c41da04010b608800a0038469007041d4010f080c10130042c060017519042c04412680075691852080746280e20104007120314000703030303842180c008048801942c2c030340e082c0403159410f5000480e80207685682200755048070340f041c140603494401007000e0560074850040e0480b0a10303048090a0350000b100220759946440c04c4030352107403c91401040c1500c4034948030599002140b0010300a500b40010041c426030700200c01d81c030030a81101c0502507240d6a81007681c80369030650303014255 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 15234170 1250 15232920 15232933
    0x31119080414060d020d050115020a0f0b0603030c010914060f0f0106210c08010609050a081015080303090a0c140108070c0203070906030803093702010201090c06030b03010c03020c 79
    0x71241e4080600d902d00700030300414905a0400844802c82c2d00c0341c070b020301c801d940d104014450450449141c525905090008104004003511545180144210001c050502c0e807800580c0f0343d02c060054400c0d21300314400a100006451400c6c4415002c00c210809081c451000020711a22703000e00414010104c000c9045240d0342404412a842d136440341052541188071402c01d048000d1610980c22540c1c2c0642c0c1d040904e504080005210782c2c06544001d11481c0c0801d400d0002032000f003400ca451340031200000500d07082c0c01e4901c802c200125480b1000c43d0002100300318050740003042c071610151060800712040b507140c4000c07801c0c0c0a8968a00c500141c3e4503400240c1c03641c0110041e684c081e00013012600305d1699004840140c82140d00f040300c41c001c01000380520004d0802040750540443e041448a00c03910418140d01504481c0b50a840b6140c050404c10035a4000e5001080b850340105954150644902c40035000d0900e4190060203517180601414090b4403d20039500003415a2015269 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 15235420 1250 15234170 15234179
    0x50709060c060b0915030705030303060f040b030a0501060b1201090606080403050304060603021c030809030903150a020d06060509011206030203030d0902040f0204030b0405060709031e1401090311190804 89
    0x5040711020421a59903a407a080c0d0390095403111141e034031900f40c0403d0b06044d50003200c14036040c4102c03507020501a600a000b84501503071280c0080e8015170f4203a5000075000d00e441e0001c1e1800d44c1090300504030303500e0540c000c00c8808243e0000c00c684104506801c4450341d0350b0042c1c00c2111414230809001450400100d00001c1c03281009540080c014440800d031641c03a600041c0382c80c404440182200da0071002d0320420150040c40f5541d02c1880b00002e18144440100400d85406821079100c10b40025140090310b0140390fa41510034140400d00c3c01c100030350300c982015281d913000c8444035011400061050610124600819080e40e502401031130a0019001c40703000500030f410022a031140e112001c11000040f01e02c0540000c6001c0d075088116802d0506000d801c0442c0500345504100003088240301080d04860720250107007540c0b80320420b030590f82c2000c0301c4200e01c41c1c0400c0d80550a0003000802d05a000300c00da504c41c8080e030161010705200f03480d4850540c004134001441207230244230800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 15236670 1250 15235420 15235427
    0x40203100c02030c0106060f030617031902150f0402011106040c0e06010c021203030604180b060904080403200916200304030222050109020403031e11100501030b07020105070906 78
    0xc0c9000c0d890300440b420440b40c220351130b003901e801c2d404c01d000240323040c01c2117081c1e10b40c1805080d0013045166540b00c07994103003440050301da10544040c940d030030346480000c200043c030800248400c0b4109225412130360a00c134a11612402090b00d069000640c9000f440c200342001040d100d000e04d5001d450355400e58a0300594095554006007030906026620b2007000141e11221800c1031030840313400141d56246041410003003150a1281801c000004d694500390010742124a01900103104688030f980c1c07607032070f40f901400c684503d80008064601110025003030140200b4140705290007142c00c450180c0c2d83c50b1540e000050301060b01c60001c2c1c0551100780305040c43e6240024900c07030200c01d072440c00c1d48a0300401ca0b60790450326110b07110105404060301100e140e118142c0900b00014007540b0705495901c000300001d002c0d9003c000812801c60040d514207000705030351000c0820303210907030305901c40518101c3d0040c01c0910003920700c2441e110000c0d0043d403040c894144244100d44440e52000d04101084 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 15237920 1250 15236670 15236681
    0x10f0c0e03210c010c02011524050d02070212010504020f03031303231603060f0b0a030303020313120f030506040c0203071b080709060501021506090606070203070b0d05090d050304020310 82
    0x19004040b04100000b410034080c0118038074988580c0020407502d10042006560410070780c0b002c4122140c29400c2c007540c06c094247d0006c00b0035076103071484c0c451b04600070f1b07d4020711400000942c002c00c0b60b0164205441c040d000a0b00c02c9002310380100007104400103254503881203070001c2c074064004c00018000544140001d1a0060750201c803402c004a0082d0b001c0c0ca41600c03c0705010040c081c000b070030030030072262b07004015602502c0780b001c2c000d12454401040c0d82030460701004051540220010302d030180000030a017103403038005d6550728400c140c108d030241182c040740000400003814840021060305042c040c10491031130320303030080d03141500310740b100b10b452250a02c1d000001c10083c0310020b03c0d003c003000020050b02c1d107510009001e510348000649003c9000001c011100401010000b10340c0d0380c65001d50b4801d81c242d541996514261002078100031003034101e01c01c003010200d040501400e2a1788603d11079204817080b114010890f400c2560540812a40254158000070310180d14900c40d4005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 15239170 1250 15237920 15237973
    0xf02042405010f030b06030906040c060f020309010f05090d060204060306050306060a0303050306030a05060c04060306080c091f03020913020a0e04050d180e0a0e01061211090702070b0c010f0c0e03 86
    0x4400305e88800083c4190b00644d5111110f0740204180001d120303e2500039030040c07403141410a440450400003079124022070389a507040c8003944085032282070169045420014004141014240c4185008402034000d4050400000e280c075001003014140000c200c0e001d54801060380135110320b5070f070b030840741644000d01250301401784410400015108000b943e00400720120140c0c4c032507041c80b800a00320744847c0d20907d4540c0c002a01401c40c0e4482d4000150080b090020000070b030000d4140900d641c1c5095400207403c00351080400c499100750f0541c50300f03a030b4400c60743c5c510801c0d500c0c154801c000000341d4020b01603421840081006501510050580c49020801200402d030760700d40414801d00210380074031040303032155104026681e080c400c41001c0c2404070440c0c2035004c1e458591f071090b4442100b816006030b14060110306164002c0103100b00070401c2804103540d50002c08520b0b0f0203464918240c0401c1d80c1030410031254280a14005083d0300000340c01064203000c952910342c0f040001402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 15240420 1250 15239170 15239177
    0x3031d04020c070305070315020711010e06040b0c030c010c08040503040605070507050409060b01030b10020309060d0e0d120e010204031509060e010507020a11060403050d080c0c0304030f02042405010f 88
    0x10b5115000e003406900029401000503026052460620072000c8199204010403c0d10400464002501c0d0010804c4026002c0c0303020a402040d01d0080b030814402c6130025113480c940031401807110702c4000018a10040b00500910407191030703120641d8a42825100205150024001400320360310890103007200728011021030b03803095500d0000c90221546100f080d62415121a0080440c0d6098026500060402e581c0d41e800038a401d0402074481c000c0000329482a00000303a00104a030842d003080000001501c15600c0c01408ac5030301401581841084681880c10443c400c400c0b0701040c400d481c201c0e038000761140d41c400044040f4000074000040100c5849940d020015840c800910030030b48a1090b40d001440003007107505080d0b10b018103040840b44140c1e030400003803000440206030040e4a1030f00781403d01031a194001c642901d800b440c030103240030f840013080020038001d40b82c103803044480c000e5500700301403450021505124501c0881c4014070540c01101006154860010700300704038060319 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 15241670 1250 15240420 15240427
    0x60f0f03060f0e0103060e06090c0d05150702032101060e06070206160b01050a0b03040f1202210a08060102010207020307031104090f0804030606050d2a080307051501080703031d0402 80
    0x120080100102e64020f681081003c00c010300820185205038111840304a004000741c0c604044210303961142010424050350140040300100700c000c01c04508014844001d03c2c0492400840003942e907049100403441c600c5812107100034031201c03035003507a0584509954403846241d03800c0038821241e00c06c400482c0c10a0042181c0107038002138040307007800c0a220312090500da5250100b04400d14540381c01c010b550030030801c28400001d10f0025518040d99020702d035503680040b8454264141102000d07620021010114001c00c000346440003002c6c49005600c40e40804c0d00c540004900700e00603034800030b416901504060000c28030701070080140c42c03002000800c80007240d6903580010020041304030760003140440d0a1003000114094134000c1c080035140380b04c20401725101c9048130348102c140c004650001c106810920450a400500506500300803a0781d20080c902d44580e8456203c030050f42a000404000b24030408007003800da04581d0140c0c0c61411802d40031140740c500452110719194016400c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 15242920 1250 15241670 15241679
    0x10f0c05100902040b03010b06041406040f0603050709090b030604020d05010f110403020301050601082406040306020315090709180216020315070f0c0804030303020309120301090e1204060f0f0306 86
    0x1c00040e208000306050208804501d881408142d41d40c00d001c0e684203904022600d407551f180c1c0c00954080360461428030450f810110040345a51145070807100e80c2007122000816003e4041c1c00c100d004810b1030f031311540c0c02542c5007401e508542402500d04ea042d001400458090704c2e1200c2c50300700d410f009000008609203a020500708a40c854260071401c01001308040003546020b00c91190b002c403003800c04a40501d404d04111007040e000740190060400c0f072444000c0b55454007030a89024551040c0115940d00380b00541c600a00891911184601d900e00000b4a4061183c5030040c215801440ea01da03100003101a01006900608020152400c4104034507025980c104601c030010b003114511001d01d0708284000400780f03810200c5440622403040641d40001d21701c40304980c1141c4e00340c81e00680b80e4842c3e02c1054240030010400e071152100200000c900b203116540000b1402001c1000c440f21810404108a1203000350b1003070001140710b1000e08542d6900444008650000341c1ca400034010b905c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 15244170 1250 15242920 15242923
    0x50715060e09070314060907030f050c0a0e011e060f0e030c09070503090708010b06070201050c01090c0305030307020c010c020f040b060408030a0201020d0c0201090b0a0f0b04020f030402040b120c010f0c05 90
    0x101c030300501c242d00544080062081c2d0480f1a40720f11205c3d80a0f00d900d1619580003640c0700c0c0b00d440001c003150008d09990b02445802e20904556a20003070100f45e030a90743d00030640034444280203020f0054071411600c0c01c0c00c00d07500603403400c59101e9110a0b80c2c14448030400d072640040e40e0145034050045500341e00070303980e9000c0c2c602d10500160316055180c5c10102140351424034641c02080381c2e6898610a00d0a83c1c1d0707500191038040342d0910302a03075201e1002d6440390242c0700ca010000c0855070180004000c0040c04070156100e0050f560071514610528030044a0070890041c2c040e411484589040600341440d4000c074000340c40142c0b03900d1a0940c3da0040300d00d540e02c416082170050b580850500701101d82c40c0520700c5281800c0c4000d001d100c0c0f85444103070004802810f64408142d462501150f640740a820180c040c0344001c104544907000b626129441c3c0e803046804a10651a1948134001c0789031249850171400042001419844001c50042d41c0480e81e80c5054024401469201d8001590 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 15245420 1250 15244170 15244199
    0x30303050603010f050c032502070b0307051b0c090c07020f040c02010902060a030b0f09041505090106050a06030501030b010501140307080c07020a03051b0301051b0708040905010b040e01080c0105071506 89
    0x20a81070386c940c1e03494030f000002e2143d6109000340792003020020707540308015800507490068650081100303940b616101d8050707890380b09807105ca07a5002450003c1e8030f00c000000c12000c04100007500d90007004c0c1d07100d5041c20124401d92100a41c080c2c103030001c245480c20a64801c2c12070b007115000024901d8507940010380c0b43e8002e0442e09000a0300d07001d4203c0241480c0d450752410180035500e600d480e00709551003944030520f404e40c0c02c2a442d51600010b44010003500450b00800c806018001c149446420003400340c10240425a4115000000020070354860b05000d43c400d040c45440340e045031541041110407403005040864030130003c3c440c1c403015039100200600250720800080c03080c0c054202c95942880d60030780186109901d000208905000f0002d0032800144800d02c9540e03584040c0e00c0c25007590b000e541c0000c03c02c0d920307000c00451101d540720000e00071381e103151248000d960b81c1c421110b075903200d0030101346000070000d102c09400105085004080081e80082c0840c1c0291580b100700580b56 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 15246670 1250 15245420 15245431
    0x4030203060c030a0b03060c0315040b06031003030e061305060c01020f1201030614071e05040b070c170109110f010e03010c02030a170907030b091501080c0a0b030709030303050603010f05 82
    0x1200005003c0513000d01c0c0300315181660160040e0905252070401c101c0e80d80002407850589420440c0074a0b5141c1c0c46a20001000b13030010908e54480c200040c05c1d07400d42e0450b020071400f01b00c00e85410340c0700307107400b07025120081c0055180c00d10441c00d03c1c00b488141d0f0411840703584030b1b6400f031081c071000031048409410300800c60050945150300d5410701030140c510031010b07009818003c0c0b00b405074680d032141c82d0010003282203602c9041c44035100c000b200e13103103d5540700011901000c42c0d00d5003000017024101c0d007110300e4a00001c402000c5840c91a00f29a0021001050000c03030450b81505030501c14009046504141488064001420301090a541d030421030b01700183c10010b11b40300043e03000305024030282c0440003070000700c1c905980ea42d95102090300000d046401c00c0c0002032809402046003032052809001421002e5941c0d2171480d039034024916005208400140d40402c580040005881c0b162049548540780d0703901c3c5440c190000c01c806400d0303c3d019522200c41d14084403140c0651406007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 15247920 1250 15246670 15246691
    0x408010902010e04090b061c060509030a09050907050418060801020705011401060513030807060912020705011707050307080405011104060503040b0a090314030c040509040503071709060f0f0403020306 88
    0x140a4400180040c041c610f4051190b8940a021004102d0700004240d10a9003542c5201070310000700c00c4811100c0780d001c00109120b00f00070421410003030110281c0003207180354850200068407942080f404840456641001840c02d01041240c001c900e020224442c0c24508002490780d04d40348410f09a074402d01d0251070a039100c5001880700c8580544050042801d031030170070306081c6058030008400310b036444090f0007500302161003c140201c0303500582e80280d020801c52030120414101940f038000d203210340303408114403407486240082c60f18a658402c840340e0751600e1655944000c25202450050310582d820342d61418280384000188004102421045c0c0b1003d4032803500385006032580c030b801440003c03203506201c003900000360041c400341c9031044001c1c403042e1203596900070000d00e0301481d4086984595220284424014040b008100490207454026000c04100342528071034401e0b500c0381346d0440400c121501c642c1c0401c4000d0800c1e00790fa803481354a842e60701c0d00001d18186d000d40f09a00d21 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 15249170 1250 15247920 15247931
    0x30612050f0d0e1305060a052d0306040f12020709020f13080d080103080a1101020a030603030206151e03030d02040e010611010c020a0809061902010c030c020c0306130512040801 78
    0x88400c01040d41001c203545080705851443c18003007004c20070384200c000002925600421641c0d900d0103460030141070701500d03145001a20601d89010180c118001d00c50b0b2070400c540d504e803141400304000e840740f03420100780f007d91621940c0f86032601e020b4100e0a4110300440c0000b1905030f600740010400e00e01d02c81d401e182c0711420050b41080011503648913104951080c0c41038000b25400c080d800b4110f9800c60085030700c4045c41030007692040d00d0000d810020754070003e101e402058140e840201920300a070300f120703c240d4505802d169410b403a0701d800d0f580403070f918120101c0d043c8881c0900a48041c0074040d20f003003005100210082c0e811980201411640c1c00005001d04c6038045c00152007042c41900a10040c2148000a904c44014000103049000001810704654403541c00b100d01e180c0f417003d040b080300080c040d40240204000c00c482030000e414511200e9440c0c1c800500f5507280c020040150841d6191028604110282da1108481d94024241d07070350603085108010300024070054001040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 15250420 1250 15249170 15249193
    0x4090f0501060f0b0304051507050d0c09030c05011b0204050601020c0603150f0102070f060c03090b1218070803030109050403091214160e0403030906270203120f03040303020a03061205 81
    0x8283c9440c1c002c1c0310076a00920170031021031000510302c1050440600141502e850300c580840e4944a1700c0c113001d01c45810064901d42441e480010303201101c0c000c5481000301c0d41c07110f00440300d8455102400c048040514800760241ca0907500483c1c0000c0140111050111030501003801d90304200c83c047c0c0b80400c0000101001e040000888011b200244080c240f03d6061002c00c444004150080350100900300100501b01401695101c001d0801d1300103450f00e0700312008102148a404443c000030001608845040303000c070000b150001d883c02d03003002c1c0d42103070700b001d4000300104002003065040200741000040d10703000d19441d811070a07006200c40d1401e1031042421390300c1d0501e0f201c042c200d1145041820450424241c61940d001136241c074021039100e070941840809003621503a242c94242c2000c008203a490092140302c4c64880c420703000d40c0ca103029101858056400740d00040442c00000b08005400684a40d0042460600f036043c001346083d1a100f400210000000045449a100c100f8000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 15251670 1250 15250420 15250439
    0x506010e0a0e0402042016020312030a1b0906090605030a020d0501080d0e0f01080105010f18080106030215070206030c0c010905060403050c0105090601080c100e0411070c090b01170604090f050106 86
    0x20301c044511125046c80c100e581c808a5a106440003080707070180f80225402159011711000502600c013078221500c0b41810986100201610629141c074040411a00c1c3c000301e000307840d150f01310780140e200d0304940c525000c000d0391a40d0004286001080d0300300814a03611506200746800fa00c0144000e22101200810240c401c680c0215040d2140c04504841400c981c1e20844450540c1d9080c0703000151602c5199090301c3d811640102d04d03000179071900c0c0105411005602c81d5080340d0003214460f080c200c1e00d03000c8003294850b01c1e030702a4000f4400c000050100c1410700040404491801c00000c0030103094540c9401c00e80151000ca000480008005e0440d04090003600d4000c012003000d0807242d450200207641d40c0451001440c000c000201e406c07101d286c042c000c01403410002510070300c55804c811400c4a9154070402046030803103a0090b01295003a041e05c1260b01403041038481040c0002800b42d40350002400030641a4001d8403600341000283c44036900440e624840c82c00070408505141e03900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 15252920 1250 15251670 15251681
    0x209090109020c061503011404060e0c090c0a03050903070f0605010e0115090501030c090918030314090601060c080904020d06030b22060c020f070b0309070501030204080c040506010e0a0e040204 85
    0x1100030720700601058030200300100b031039500019091500c1e58004000b2000c01c0c01342800f0000c05424806960811081c412580c02062644816138203884101502600300b1207819020361720340b80b8462062000905241c0a42e000c09d8010302c3c40000c507804c0032800d83c2d0b16041c500040b24100c0e40c4985680040001190340e529150150134184040c040c4690f50800040c401115803149604044d01d840354801ca80c0d006c0c0c195280680385080d41070120048a00d4070343c0a000008904800192610400c0d02005100b4074109004200302c001a0a4691900d1411a481c0101d0b56003952084010494600141c0c0c40d48010428040200400b160251940c1010b2000e00300052180c0301c20021040310902c101c01e6010040d00b402d601078030000303400d80e0910b412494210501c2e40301c00329100303051005c56140003d2002c1c40c4582c441000321a1015110030044060b80500e10508100c0d074042600c40c400341c0707000d421050b80028185800b504034408070002500b42c0034158010f400c040400340500c0250306041c00384 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 15254170 1250 15252920 15252929
    0x2010212070504080c0415050402040905090d0305040201230d0c0c0606080c1c050f03040803030a0c02070e010302040921090602070504060302010c0f05151608060a05130b0301020702120102090901 86
    0x1a908040c80d00b403500c0c0d217940319510b003244910303601c4024060300200101100d0140c035000e40110344664883e04000020107055454002a02c910090b08100c28440e0003501d00c1164103950340c0018503410a070440d000081a001d149410f0400d003d5154120b03058031543c84288425501e224002c00789042a40c02c660b400e4010440c1c17074001d40c0300c1c5025901d032801e807042980400e0a03481c07002400350030722038148070f4146400b040030b000002e00082d8014001014600030b2405410400c501d0780e1a14044c0c0c2d0b1080c940c0b0440c0f0f483c2c070002004001524041e8000c0300d1041c010b9180403880b51075035408400954903d5200350208a40280c00d103c0641d040120001400007920100401400c50700083d00c0f021110000800c840700300c092840030404180f280c03081c0e007001e0701e030780c1c030703290700706030700d640c2c054484490000c0000b98481c4001140c03840d02c0c0c401401207a601916407401030a414080301e0183c10912600754140d9020004280140c4940c0940c802604074000016119201c0400b04515408103911 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 15255420 1250 15254170 15254177
    0x907090b0313020609090a020424080402010c080d050f0a0c0201060806010302060c07080604080403120305060d06050a110d06080c0a060f03051003140607020105010915050d03140304030201021207 86
    0x818458011000c0849410041d81c41852420702050303c00030740b19200d15450b0b150000d9403082030003190140c5030050300036141740c010205007111080e80100d40d0701000014860000300030601080155001d050903288042c09000040d1500361020070590130742c1c0c000d94905406420311400c00407040d5851151019040d2640b0003880300c0351a00d18066515107040c00040d21641e00082c800b8414541000040e00900300c3d00e040d50254541400e1072000b0741c10600c000d481100703030001c1c03140d12180309200303d6114001c001c1c00b01985c0031042d140e500040c80300400e080d452655503052441101c54000140100c200c0d440e8000c03882c00d052001660405520044403402180030990074170480790070400038614100d09250000700c556880d0400303840c468a82e44080c024000c0c500c0d54803a034520102f4001d100c0d00550f0005c1c0210799a4000001c2202e42008001030380800d01c0c034081c007a47c54004c40983c21107000345840201c8a081381030b44101e680c015241100542e50000e0449403581130ba285c0380384d02c00100d04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 15256670 1250 15255420 15255437
    0x309260105100305060c09030a05060c13090506060a0e030f100f060806040b0c030403030b0a03030f020105070f05091306091508010b0102070f0b0c010e0708030a081015140c01020d09020907 83
    0x140e5103a5102d0000d8070030380300d0400104d40b140264030304000302100545c1020482f201402e11111311801a4407403501340200700e00072040403644138500d01039940101c02c05850507182881c181801c98004103459065989402000403c00207072108002000705100c031220009a035a008030a21011154250300c484aa600120200404074007108a03099026000e41e9261340d50b40d4403442c0440041181d05c0015034840002c81010060507800603100d00280d401350020070003619920b00c10b590f00c0101200c80400150b080004a01c1401c0030840c5040c0042241c00118055484440714425200b07100241201d003c1580820031180f0320034003d00b544000280081c01c0600c0c184400502107034032900595408560010300d543c500389096000c146680b0450b02607440181d119100d5a80b281e120044e074100141640000c1000490060001c01c111202480000701e8030804d000c2c140c5040340e04145000051109000541140000303000505a82c103e40f18002003002084c410085d0440001c0c000780d04200948 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 15257920 1250 15256670 15256673
    0x406020c0123030103030503040303061d070201050912090402070204060302030a060504260307051b0607020304080c0103020306030a0308130602040308040512010509060103061104081c020705030d0903020d03092601051003 97
    0x1802124151781c1c1602d4515500d54890601740c02502a90340215403000041d01c0582650000300715031805803110b54001c3c4616199a140160f440000700d0340030080074000c0120300000d00c0c05500a010300e600c060f0007c81c0ca40e030390b40c0000f414071030309010680708151103504200402c08010804a00d102e070b1409002c22444010080c0c402c40c1c0001080344080c440001171100b1510b2482034030300ba2030400102141d00358500340000945079007041c2726901440c407400704c0300d00c2c10798064020740340701c0c4d10042e00400c030f640c40d035403021580050302074288404142c40c29003a00c040b5007580000d0016501030106180e4841c1f5040c10b000041542c035030108500e9140005102c81e9000116049d41102d4000c800401d103c02c0071000c1d0400d6128a52001c40d23588503200038200c2014840c83c3c03403104a6095002c1e00c40c00382d0384c3e0091584500540307281100080c8440c00910051400d42664041280039103801c1c501a42c031408a40c0c1240a2060b02c0f400b40c0c07070500041e003140c400c00d0141a6010042c800700c0c4580b180340d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 15259170 1250 15257920 15257987
    0x906091b09062a1104050703090f0b0709050a0303020715030212060f060d24050f01050f0c0111040909150e1509010e01060303090305060112031706030703080406020c01 74
    0x580c0140c600304a20442d89140e0641c2c42c90700701d1068441004251450f40c840e2400c950742207016407465002c0e0342000c001480550280c8200c0406540144039030b0141e2419a640900e081c0d0000c5c192001e2090070100410307992118101c243c061032194005004240c02d1003180c20011680300c0301d100801d8010402ca444100c81c90304412341014041e2010040d017032203907001800798040c0a00e601302440c5815080d0444170052580005100640101400c2560702c8030240103001c1028400c0c41e000c40c03000c01c0b0703e08640c4000c200400350000d4400000585600309000070f074441d4000c1d030003030089546400000081c04001e0015964200050f00100a01d1000e040c1c0075450f1500402451000b030984000142924000e402c2411a204000e001300704041c0c9038a000740a40c4114041925288203000010402c49402005002c5083d05510380d00204084144040750400d4000c00c171940500030740200000188a00c0c010340081c0c4051b4015010036005c80e000100003d40d440306030520782290030810240f0494 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 15260420 1250 15259170 15259187
    0x1207060c030605031b0a0e0f040f1113060602060702010c020718140901140a2a020309040603061a010504050f101103030106020a02010807050309070506031b040906091b 74
    0x2486080803500001420040e8000c0c6800c1d070040d9090301840c010402d03009170300000505144011103840103811345074410400d10344e004440d007a1400440c180402c000c81c44620140d486184140a00c1581c40c02c210003186c102d42c0012140d41c860ba868803400d11000d6014452194007058520082040e10a001c00003580d0303081a01c41c508054a1420012000411941050440c03141400058040d820002c080c507000300561903c9107242d4201d003010902c0b4045501611051801c817414a86071643c070301071107113100001c0c41c10340d00552004020015098545026031801580034503c00104030029010909040b2070751030483c2c3c10004208410310541d601d0490030000c015058600c0a00c08030503c0d0b003559201c1440e06019050321001c000005c1f02c66000030300c1481d4034401e90300c0303038002d85422500f40c0ea180000c0c2c6101030140c004860500640c1401405194048400000e10000c02e40701e150070132455100350000710f000c0761101c0c0d062028110034002c4079540c4008a007602c10864134040000c08400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 15261670 1250 15260420 15260423
    0xd0308070e060304050d0306150503061e0d050c030d0e01080a1808040b09010221120a020f04030c05030c1807030203040201020a0215180f060706090c0306050906010906081207 77
    0x801201288119205a07010080444040c01c003d40e64280360500658172115440d074600020305045000c02c142e81e80d080840c5440c01240c481d01c1c1181c40710001c000d406102031000001d40c001600801070b00395654210240c0c114015409454080c15101c103041c00c081e104404d4100748800c607034400850ba68071002e402ea0040781048d001070740e90540104981440100f84000d8403844011801142c0c545680740206200ca50136001c42c0ca00015102c00c2c03500e90910702d0165009000c040c00704650065034010980e5010344050001442d00641d0304a5200c2e5410075001528a61580710081c4020f080400c142402414100c5405003076014075506031241441c001d008004054011000c24110390082080030715084c0c0c02000e8500001003c4607400343c5030003a1348585070400c01d040b0100b2042c148021040c868000150140b45009516210710001c0c2c21a454101c1d180c020500001002c154240f0480e400380414001900e07503540340c01e909a094400c160440306241c2c111614006403952140100e44e1100e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 15262920 1250 15261670 15261677
    0x110d050d1103010605040801180804060807030b1f03050121020d03020712030305150406060801050d02061303030806100e0a0302010e0105070b0702010501050102100902030727091b060c020d03 84
    0x1811140c28010240400c00c1e0245240c1c08003000205410340c20401820503290001e0007017244074140303044c40c0351014140101404446d81000309002c07041c49500e14650000c1c441c00c001c500042500082280710000c40030b4041040a070701ca00854150b41401420700420200d050f800038011040c1c0c1c1c07104070801d01c001c020301c40c10241a000303003014001e00c03c3c0b100508003880e03140400151410302601034032007141c102407071424400055940349494031070b00d81918003940c1c4090950b0309000902c500a00881003e81c0c1c465000e00c00c00c2e0807c140c175103048001e540720b5030300c42e5402d08100050100d10318080360845c003071140894818a05445031203c204c100c07902440c0c19140704075090016a054855044064140c00c1442c0401809517015007195040711000e0782203070720042010301203208940c0c4814009504d0342180004004524918821803001d04040f5428411100d0000c3e850084808529007113480340d0080000540d8170502b02483c2c0000c11850402d41318054a0b640021510b40c0d150704001c2c1030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 15264170 1250 15262920 15262927
    0xc1403040c0506070c090c02010603120203070f030e01020c03030c01020c0d0c05030901030c0c020d0f02030d0201061a0304080408060f0403080105060702011704080c010603030c020a0603020a090303031a0409031205010501110d05 100
    0x6012881025100902c2c207880c1c10007c440307a02d08001d001c0e0072a03000583d104005c103011074441910004c2285d40040c0c104070804810012980c0c01c0390710890340d80240d4110303c211214901d0b1540c0900040c41d10220030400145d99000c60f00701c075801c05042c5d200f03034002d00041c41307801c602040c8003004603100b91000346000106102d00e0802650b40765010200a904000001029400c005045440c600e20a0003101105c4000003601d60072400d1f25240d000b2a5404401c540301542c2d501d140002440d0450b00c20000642003607100c2c40d04624102c8100c3e115182c2444401c02d00c410306822001ea1405040255002443c2002070380000c0e004411680b1300c442c030408081c00003424090f4400980c0c0c581c601c4200244a00b03690b90900800606030224260b210b19568030001030942c2c024403c940100d1459200c542c0958030b16181a00242484142003161004d4504a12a1580c03544903024595100752101c10050504034a0380c0d0844030141c028a060200c10820184981c40c0050755501100042c174210740d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 15265420 1250 15264170 15264173
    0x40603020306040906050405030304061103060d230a0302030301090606231b03040b0a0e030c010915030f0f050414070b0d09080405030307050309120703080a05180307090c1403040c050607 82
    0x141441000174241a1030441400100b0a0210041d400385004070b1080c04125514610342ca414401a41d0311544400c091140600182001030a40d80fa42c80840000c01540c0e0351300580360814807580b00c1240180c00003c018080035109200e2100503001920b00b25114103068515480c6a089401c1841240c020200348100c40d45c081c02250351000c10200241e1351100d540e01d4050400707801501d6a0380c0410752044250b0303007508000417150600c5c0c43c141d40d408065803600c0740180a103400134100008054503a4005001443c2c0c0e400303a01d0540c500e20500041c1882c2c14201811840f0450440d1903072074100d440200032910010b8140da022315040340c00004c5860741468140d00d80c2c46164040c40d01400040717204014000003001400403800190345644c120340c1039688150301e9440701d00004040c480b00b4051410541d00c075802400500c440581c0a4013003001800c0001e28144441d13206040090b04c3e803010008244d07020440707985d41e090608800382541070542d03454600744e9031409103e004a401045110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 15266670 1250 15265420 15265429
    0x103080d1a040f0506030705011707031113030b0f01051e010e04060503070801090606050901030512090d06091101020d020c0901050409021503071107050a03031718030f1305040c05040603020306 85
    0x11441d940c0103000b001802030940c05500908070444100d8801c5c0070301900011a540601e59414021040e0300c2501c0041d41c8152080e0010202c86200c03504a281c103000341320b80080d18442e1900614010303003c1034070601c0c1400840e00c0700f000513086180649101614010048016040c10036009030034204444406c0b002400301d0b00a14030355200799458450303104001030304e60b0194082c804441c09171a085c05001d440301d060000021007844018100c0c0c2c000f86420424000d004058010346600500c0320803400c1c1c4544030358082e1011918155058171020140300303500d41e01080464000d0703201d80003429140ca1088001140c0100511600c0d001e0b548840c0d005c0700f15500e804c0c2c6500e0102d0340f00d407500e44904001070b0040a00d201c1c440c1e08440c0c1c2c400c4080100302c03481c6c54034801c0226039056a4002c250b45440c60000500400902012040404003001d1050302d42e00303202511689100824150f00c03504d800001c900d102c40309038001d50243d403400c803804034103d900000b00e60a4401d142805603807500c4040c00b04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 15267920 1250 15266670 15266711
    0x1201031505012112300608010207020105030c070c03060e0303070f02010b0d030804080c1903090801020301030209010302040b0a05060315010909052214100911030111030105040f140a060e0702060103080d 89
    0x4007a0f038040400f001c0e005c210411100e40001401440070090070381ca4555040c203d110301030b400b0740891420700c000764034500303044018081b007841215400941c0e9078135a500c40076074400d441e494980f60004001c00c03100580c40414080b103410544024481c03072050501244200c4d16010020b404c0242040005e01480b41060480e03002140003811903408055218a50103d0141010300300c0005490b01030002c1d1812050094a0589400921003103076a441c6600b00700080101c403810703e030031102d0300c1000900b40c0d8501d80514800e26001e00b130b003e140c151001c001030840c921038008001041c81c10b402d00945100076090f450100480f00b0748440501003d0401d6010340e13080803081c5200c4d209018100f0301e4000a0b810034001507120740310300500d00c4440c0080509a55a0922800e1007010a100400051401d03800001038280d0f02d0704c00048c22040c0314000703a95610b044400315071458a40d4001c1100310502070380e1580c401c0442c07000d44102e5045580703441d518401d2526801c0740f03d0b16100500d840c3c28682000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 15269170 1250 15267920 15267947
    0x90301090b0106080106081303020712030c050a060501050a0909120305091618050f07020a120908030d02090a150c06020912030c07030c0504020f19051201031505012112 74
    0x4401d610b6960b440e0041a800090042c034000554a02c0801c0785083e54103c414500c03030303241c0c0107130040130f0602007502043c1c0c90058094081214622000010610900c02c0c50b2006010b403002190940c184414460300c500a6408032203291b10300701c1c00c4004107064080003030b00c03107a140c0707030114040d00e070001250303e044086142e44245040c2c5180001c1c506258ac01007082d032905480d028001d69890b0240c04c0c205600c21202280542c002d8601034000940704040092004a203003813f40041e9240c0b204685503030402450301042d40d500040c040a50300e01801c6440c01401002c4a2000130310109034000c0040c0c0800e40000c04007034012802d0007156842c240c0458889040c2030440c1d407580b459182c030982c0d030030840c8401c1e10408801ca10104842c1014000c951403100d146040901d880590609840e5500d00c5200c2d400c1008002d100c0c10f500b601080000c0c4d80298001e281e41980c10300701e41c0c207000403600180e209401416010201c01d0b410b0340201030425060350407103450340c0c1001408400b900c91107010100b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 15270420 1250 15269170 15269183
    0xb060f0a0e0f0105010e0402190c06060803040e040c0506040302031b0f0607030e040b030601140904050c041d0708030711040903020a0212030403030e03030406050318010b040912020c0103060509060609030109 91
    0x402040b06000407403070b0304860f0240da804e400001100d00744012445000709080c0301958822440646500401d4000b4185d03200302000034405980358481421a080b030b400c0960354480c0d107824402403100e002502c3c1e001d0f01085609034685880e59000942c1c0d111030407400742d994100008020307002e42d9000e48030501a2005440a99600d040d46001090110320301d0440e03118524001c0c10001c903040c0059600d0680d07021088030600500707080308000c19680010800c840da8440e44030014600c1d1682e0040380c50382069115402c0c50b200b801014241040740e50341044841c2c0c0d00501580d40030884458103c040c001c0141c50004501109003412800c103823001c440690000c460414070a80860004014800c4034040d56440100003042ca0805407a48942d20404000400920100d915010400c0c0068488240c120000800d119035102013015540b050009480415480c1c0341810407a4060080c90302420302407808100c20760501340050441e41010701214008c071004502d103a03994a00754406822281c220742e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 15271670 1250 15270420 15270449
    0x9090106052206050d021b07030c030309061103030606090609030d11010606020105010305151e0708040b010b070c18020403080c010b0f0102150406050c041d0906090a0b060f0a 77
    0x200058001c1d40b140c280d51010608400d000070300950030390160703001d9511a940d00751900b107110310303660060740140c0104c0041c000d46480c4004064010405000110300c07480b041d1500c207241d400c0103805400640c3c06002440302c003086080300004040b0490354403641c200c50040d25046000045561805004201905803080c1c0000518160b04902c0d9201080c901c6002400b0b0203031a103204900b44c034070a20004280364002c00041c01c03410601082184d0100941402c849401e1155420340c00309401038a400c0d000c120580280700034407000504090141c4006102c851130311440759181c0444855503c00c6401c004c841d0790382848507100c140c0486000b55001104182c90b8600505424000c00582206912603105004001c0e0207500106a10030f0580c034007124070405980f992511000b8100c010301c4641c081100700008070b09001d500078030740300c5034904890340a1245010081031340f6102000d44811120b83c031031003418000074000d007405680410240c80951001c603000713010803507580c007d8000f03030224854034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 15272920 1250 15271670 15271679
    0x161202011b05090f060c01021201030602090f010806011209081306050d051302010503010306091e030206090609060c040605090406080d05030a050c0f0d1a03010e070303020f01020408060105090408090901 89
    0x5400c205880c0d00c0c500001c100c1e181034039405907007034070449030308a801007032402d9003040601d06440500000c801500026207458803120b0b00c444910801d8204642440c1c1c049481407443c104428004203022080c03c10071280c2c28103000203414842e035103424924094032581001700300403040b029512100c114507035980142c1c1c0c4a010241042d04640000540a450000080e601124207002071a81c181c0685885280d6402c5840c0d03100a00002401540c86a29044602c5e0b4080c024040d1a03c42e14081c0c1c0c05007101e070a00001c43d03803c241c40903201e070076964017450501603141c0503181101c04841c40d5040180c0e0310303204070010801600a5a008881c40d002e501800d200c1140c0110003148502c820280800060703584041c07504150003407100c9005a040207102d80002e0855540c4150100c4548405144c210405840002c0c01e45a2a40d0741c1d074026041081c082003019010032002061140d0380c0000d6003090705021520381d890b10144a0300780315040c0e8101190502c65640201d81c0300980160071490700d580c64 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 15274170 1250 15272920 15272923
    0x4050c0a0611060c03161808060a0501030203061303020316020307050604080102030f090d09050108060103150f0501090e0606031302151207080a020a0e04020f12040f0501050705030f010b161202 85
    0x24030b110341c240a288002814601c90304222449960515480e00b9100032046040380c0c0c26240b6920305111a5900002054512040020328030410304001f0100d859030441c030616003402c5028010000c1130481c1801ea5002a8004c400c0d240309860f402d1213002140b4040c00040e28224040d4011504401e00280c00300701200b040d0001c6200d41c0f8031150301542d603141c2c0050703150f4a540040e40340c03002a414204c2803006600c01c0d6403030350f000301c4140340c0400c8051401d1804000000a50700503000288600410001940c1045c00000200b21039007140484d407404001041c202d1200404140c444041407541c9405c540d6100e64070410000710921481d119a8a2442d0300c4210000b600c0c0c140c00710b0710400000302e0f840701c2c03030080300c120300c03240d9459094560004044c007000c4d400c04843c00c4500801440441c0400390119142c51203240524a807210072481ca00381b081c00c41d1409001384041110030003c200550011385d2100b41190303040c1c150b4541e900548511620850b004200041140da5405004e400441c0e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 15275420 1250 15274170 15274187
    0x6060d0501080c120d0f032c100e01020901050304020405280f060b03060607060f0219020102041503090803040b06011205150a080f0d030203040507050409030210061505030f04050c0a06 81
    0xf41a540c9803900c41c0d41c000b61036511407000341443d0014500303080c6a0740c10b40c429040420030440080032890b80b00c5080d0500301c8202c9110300c1108540d80440b0815100c481e150050007038a4883c00c00071440c3c902c410380020060f11005102902490311500401c0e0031600c0c04020490b1805070030420050b410340e038060040a4181180c0c0070702120304204020401240c80e000702c80c01100e001b0724040c41d100280d6500400b0f400886414041c5540c20700951a00704040441c0b44c00074802c4c0c0c0d000503601c03410142c005501c1c0c1640030141c0c080500d01003c410002e51440d04480d04150020284180c1d6555540100ca0420003642d1203070a2a04000074030007400c40485d50700740341102c01ca40c51050b042d1510b00c50f0340d5480f0b014800200503840740d81d0169006000f6402990040d015005580c0c0039074841000c201525040501180180d0203201250307040d025034070640d00904521000791a480b29151b000914500016000c01d15010781407000c102080000c11605446000c090700111900c0c1c3d892901405034030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 15276670 1250 15275420 15275443
    0x313030b011509051c0c0e010b04091a01090b1c0603060902030c0d08030718030606030308010807061409010e040209040f0608120c0d05031f0b0703170403080105060306060d050108 79
    0x1074100c261040c44602400d03c801c183d52014040302500a00358102e00e2401e80c4500e004c6d00c1444244e84046500040c40003410f01800e40e05186c555541e28296808003280d1151a11094441c04811258040c4c1e0380440316601306d40c07100843c42e80b10301510208610901942038415811460038400100b0401541c005001090085094400b280c02d0b1f8824005c3c070303400084000305845010000201c185010340d696404601140700e24180700c60702c0355940e00890381c0075001540410720401c01000401010800240a030103e0320f8000144142e4a600c801c0340d004000ca41ca060102c2807082c3c0380c9540715030341550b500e000000c000b4401441e02d80654402001a4010000c0d40d004514100c1c00203061101221580800503004008070620b4030340864040c0c00c0500054003108162455102c00340300c1030720b80380151400894255450700b6500d40540320601d04e040a114001d011420003010a07080f0300051f044403015108180e503599034400141c40740c803031481aa001c0601d07000012a03c0d030000076440c003085 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 15277920 1250 15276670 15276689
    0x40f06030b030102030f0408030702010207050307050a0b070c05070b0901030f140114040204080a110301180506060901050a060e09040302100216110607020604030f0c120503090312031603020c0313030b01 89
    0xa9140d0700c181401d0348022900c00310307486103040100d00010100401140e01c81e001d0301c001400c000990f510181183e00002040c0c2d03c2d0781c0001d03509000d01c4214010f164103c400c40c14850319000c0d080d41c42c40c0d141c03030140c8107200c00c0320804510700782264041d0b08001117814181508014200500f0541d8110140070301030940541c0019000716070a0034584200d8041d26000c40c018800d03200c4907500c562102282d1a11190155260401403030110510301c62100d01c03602c910090803091500e0390501031402c0e81607201c4c9104003001c4008000c601c3d0001341e040b10601d015503c607542503032142000e915104804c3d840d28500e42c40045c255095805078014a50500e00c145290740101202c1030400050b8020644007030351007942044100700003441407095080f01e030703c07541500502640d280881c03900f00c00c004006131155000020b2500040c80d06114130241c4079580c184850850a02d4218003c400074000040030070700d980000c0c010210705080040c1e0340f04001d07444554011944900d0001300303050081c45416a07a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 15279170 1250 15277920 15277931
    0x50105070201050601021515041107060c0201020304020a150207080610050a05150a0807170a060e090a0b07050d020d0203180706050703020c010e04090f0303050907080105060a06030e030f040f0603 86
    0x1072041c00380500600d8142d00a090362031300304908060440c00603100810a4104000c0d00b2070984441c018004024480f102581d01d030708540c202a4152407541780a0300469104000b0030005a4900c0e9106060b1000c4104800241c2c42442d0300f40e19028994000208903c2840100580340c400c07140340d4002d903142604c00c0b252980d40c40050180c80800c1301c0c001c0300e07010424444c5481e128401e0358425805009490301c0410b030580d0910400350715105446403040a80c44203400d019280800360025000610710006020384002511401800e04c03001d4901000c00c00e00080b601050600782c0c06403065106503c60465886c148580d84210034400075846038410f01a007800058014056415540001d80540207440350218403001151032480707007000154040d9898410030f003c25101101568114800d49000605050000320603280c80025882905907038108810401c460b00d50318100300c111001e0307003004103a1981080d0b0f407a0841c081d8401c41680d08001250020b0452000d10b1000d04681d603d0b01c08108 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 15280420 1250 15279170 15279181
    0x512010501060c0f030203160b060f12030307051309060e04030e06070b040206160b090106030203160e0a150305030304060c0806040b01020c06070c05090c070605010603050f070e06041511060f130b0a060e01060c050105 95
    0x20309030cc40c801030802d0340c10500004010364004d400030440c050301c081e610061070341c81e90602800c5600c0c0d5001844840b01005c200000c05411440943c0c081ca0200c804d5410910707144d4a04003010b50081009001c1c801c045174825100f031040c443c480400343c2c8440c050761285040a800782c0280810312043c3d12911a800380b203035020404640d010103540140b0308001c00c54ad01c9150000160034069161100e12800d200004040359060025501851003034001007045001c6d14030081031030f5406070590b03128078a07000c103a401a82c0c00145503501008191800c64840c601ea04040c0d01d4112076a02050f0040c2600302088007143e14a401000985e106907010072250742c8410046003203400c00c40d801f16440c00242c0200d15a180941400040702500411451505845081500f1104030408070800440c601d0001508000740c20f20400b030313100c1814010040546001c2c0304c0034040440c01d40c0b0292070b0750441c0c0081803400309a50480c0b409013134401485034295a4a482c0200017480844041e511175181001096 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 15281670 1250 15280420 15280429
    0x405150309061f0e0912040b0a0207090605010c03030f060302030609060412030c08010506031305070b0d0e060702150a060503070b09030c011d01110c0301050403090512010501060c0f030203160b060f 87
    0x181c041c81d80c1440b2000c0c1d5420490944130905002c5e04004061003802d00742e40c40d50640000800c06880311601c00c030b46450b82c80c0d5020703192004580001010600b405000e120a036441803903074144a4041c03601003020198140c0c40402090b450b00041d4060140d03904204516070300292030740c0924030841d240805035245800031070850b00c1c04c0c1342e910000f032181c1d001000340b8544600510781141030400c1d0b40c11010065640d45203852142e500c40441050046010303155452244079110600c02080060304a502c5c001070029180e00594850101500f41c400201d046024142c1c40240a40b00140131101d001d9100c4610a8441d0441180c01c0d105c0d20811700d031083c0d654424600740d0300d50070201c1444406501100015240040740810007101481100401461642d0900480340a140a40c03a40c4990740d08000503c2000d03c1443c2280e18660b04003001044015800000c1c0c0e14400d4015817080811849880c0c1241140b141c0440000018042c030241410301410344002c42c0180030031501d640040a4410074803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 15282920 1250 15281670 15281701
    0xa090b070c030209180604050f0706020102070c12170409020310050301140a05071206030c030302012007021e030a0605010906060207050f040b030a02030d020114070309050a030e0303040515030906 86
    0x14001400c2071810001400c0140e0070603000800400c0340d515117484101001d1401e0710440d000d03140755018003401d150401c1d0a03c5104060040361000b0340c9440602d480e09200c420552041200c2c0d250b440b8006014403100780c00364012600c1001075176984541c0e449014000e0b40080c0c071198450941c3c103d0014182c5014420300d4001e800d40c1542940664600402a0080c100140f41c00c007446440c0010301c5c140c007141d02c03500014510407100d40080c181181002130840300481d400d0846500034220340050742001205480145604440c0c401c2d42c9204c06d0782c0c581c040440b001c500c64062050301e1240342000819082907050b24600b440401c1002c1d65044102c0e034400c0790348201e076004206c00c1c68069071402c00360850901d03014081c0c215403040c0e0071507011a00d00781c6000e4810005035034400c1224444408080041d03084070aa1905200c0c6015645925072140000c5400605004450020100a403400d209640017480006d0081803070f06102218030006a000301c072001042d00640f000508034040f000101c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 15284170 1250 15282920 15282923
    0x105091b090a09020103110a0207031401150b0a18080a0510020f040b03060604050a060804030206060f010e01080703060e1008070e040314030c09041e050610050315011e02030a090b07 80
    0x2204442e00d031000c1d08001003100c5001a41019141c0c1584002c0355a07507802000c07108809c0e4010201d01e851820100904d213140710b240010307a410100c000b9008154009a2015940c0c242d200307580d5844101c40507600c400309420350003114594000d00240310750002c90401004c0c0e010701d060301e10380d8540740c484400304d1281c1000c04500340c500780001d0106030a000c0145030712000140c151884c05482d03d00144800310580d03c068002405041000101981400031030b400c2407040e151500d50f5100e0000103000e5191200c001030400100031b00260b141c0348290002401812542c803403074518240b07194030100d04610340c000e071a00c51180e004001102940781144611480e056030b103030001d5208581803018140d1001d02030700110b05040c4044140e50342d03584524280d0b045100043e032201da01c0d140c3c40d00d081e550300409491140c1c8800f0103101d02c45420a04507544508003040200c00c1184280c0103a91b130141e200d55440441040c0900d00d108142c0000040800c0031242c2c640c0f084140d1342c2c64001c0440d00c2203090 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 15285420 1250 15284170 15284179
    0x305090714030109080706060617060604030807150501141207120f030504031a0a0b030d020604020f04110d0c08090a0f0b0402060f0304050106031119050f150301080105091b 76
    0x1020400050070600720808181c0060003c02c601e22941c80e0100c1c9500510429104580d4402c81001160380001200700c1e0701e49040020446441d01e6400a18940564070014007011300c00543d200402c444c6000d81ca00d5032416400c10826940c441e2940e1a1404140035510300030401400a280c02502c005079810031102c0306544481c43c0d1445907203015032000100000c41c1809070500002c000500038582480e036030072040008203906c1c42d11600b201c050301d08900c0f0300b40c00f82d00031442c110003c550108001e5400350b01910340303054030000035010034000c01c960400d900f4440b0700400c00302c4010110340c00006c0d5210b0782c2d685020207511844a26900d0740c010307185c000c241111100d02c01c2d0000d60701c41c54566001d400102860f06198001d9100700c241ea200312000c50b081d9642da0f10500811004100030203010740155084040c4d405044045400200c250241d03a00c10003052154071701d241d5860306008007032102000c0036a01d07540c3d155003081c0a060b01303441c7d40500307004024078046034200444886030001c00017030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 15286670 1250 15285420 15285433
    0x13050402130605031902190603050709060903020306060d05120a02010b04051b03190b0402030103030509030106080106180519021612050702090c0901031119032004060f0203091c12030509 82
    0x4c0710302449011711001243c1100c0310300001c0c0240401411000c0007003900e61008152072400307480c000c00303d6445030015020300144000c01d10160302d0000d8100c2d4000301c145e8803032110b50004c0c01d0243c60012008907100341040009000800c960703042d00443d00da503c0030f90f02030001d0f1302c400034400030140c4002d007010100c540034000a08614014850600c3c1200d609000145050340f0702d0219050b13a03c240c00a8000c100c0008005407641824882c1e0303002428104000c0000e0f07828545c0d009005085c0708a104030590700c076004901d0381ba8a81d0780a4101a0b8544803c555845100410a00320742800b08103540b24100e003900305064038081c00441e528198002e00800042e580c0c0804500c17150001c8041038101555aa42415108002401032518005005840b03072000c021040090603a01209903503010400d222401254800c40202610185c03a23590504c80b1121198100c100c2c5580030321440150b000e007010080e10a41d940034400ca0b00a240202040d00c1c0c88010341d00c06805907901943c807407070a5407018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 15287776 1106 15286670 15286693
    0x9010f051e0906010509030f070311030601060804030c0204020703020a0c03050319030603110607021507060c03061706010303080c07060f0b19030507050105070804051305040213060503 81
    0x10071080701048510808151441c82c003a1201d81030110204143c01556420322200311915030120450300c0c0f2940d02c0c02d00144101c00502c446029010f4500089056440f543e07102c1d22640c1c0680758507000c00440e509000095101d94004e03801c6000d80c64444000035041c2420b04002c50151004545881d07000b07140250075084401101d0515161400420001d02001511410b088040310801d0301c8040714000f2521440b013205100d410002c1c0020100d00f000344070b90000c100b0881c2139400700000c0d503c0391160960301c1002002d0f0f8038240d005030700402c0000d2264400950000142c010744e42040403554509081d90381c0f400031818125100c0707103807012a003415a01051a00815034940c0103440c03843c6c50b000d072034402600615042000014811091005100c110350042101400b14032010710009142002840c06403401ca00c220813210740d00100303480d5070141c4015034074003c0161a454910 = true := by decide +kernel

theorem cover : BRFrame.Cov 15107920 15287776 := by
  have h0 := BRFrame.cov_init 15107920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15107920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 15107920 ≤ n) (h2 : n < 15287776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
