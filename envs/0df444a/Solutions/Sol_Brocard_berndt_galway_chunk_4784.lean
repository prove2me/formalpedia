-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4784
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:42:59.412051+00:00
-- url     : https://prove2.me/submissions/8ba7ee64-3f41-4836-b6c9-b7df4275b2cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 860251798 ≤ n < 860431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 860253048 1250 860251798 860251811
    0xc090a06210905030a18241d0312180402070b01050f0a1a160503030a050103050708070503030d0b031f06030203060a02030c1209100f0608010e0c1c0312020706 70
    0x10388203588002241c4440210401900516450b069241e100d84640710040081c0c00440b052999040c0e1400c00207401040520490050b103080300e54500305649250324049041c40021070007034a60706020340c100c0900a00942540c01d1381c401300c65026003140c1c00c8403c10300c040c1110761509888520243c01c0c440d0203844001425407400f000d0224403c0035107002d038001d1074002c1c01840503c41d00c84074410b0143d904503200342d2b00d401c81d040c030f00c00315041d49000800c0c0d400000140440d03c2c00907040181664000e03016113a4041c6c0e1907072000d030789101610410390076800600505d0560742842d0f01c0301406001c003070295940c000c0780c4100712140c22118054109000da4404042c07056080412826600c42c0260008604d141092000100a4014030101003e100c0c646000140d4044050000d0181e441e0000702c24001452300c0e84038000030704044c0c05280d40c4d40d803038081c0c40741070080b000074003c0d803c6e01c001c2c007607400c0e0401d0700c8204c200842e0508016014049107499008010895100174002d042c065600014903 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 860254298 1250 860253048 860253077
    0xe0d210c3212180a0816080d09141c2c1215010501031104090b030c0312250314130503030d0204030201020636010f02040e180a030f080c090a06 63
    0x90200c078030844201a4019400013000603480c8003114003005550403050381803036692504071030034400c0d011101d01c55420003652104000403005103081c50ba42400c05d4520b1041c1c40402408440074580d98140021f540721051005485510382d440e003054a95004840d81c0d44040020401c00e4404600c5074940358814400030708080051510740d0b002d40401d00e000e0050000020f011000b03401903000d0a48a2a61a001c1113035550f003c02c07500c1040030001d020756482036800010190280c00c001500c6510303610f4400c038a0000f00711158580311030780d40364441800104541005240c590800714031084075910058001c42c030341e541000a07000003162030001507a0759003144002410494003402400fa025904011401280c003003200050b40b000403a07044a10781410300c0ea259016003038107480c40b034615200140201d46000035101052181065110341030510b82c0c1d04420a40e0b4070201140640040e07941113912103110300c140707400c54101c10001d02c45810444054009080301e07440391b201c04080b030314030406e6144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 860255548 1250 860254298 860254321
    0x3060e0607120b1f0201090b040b190b0d0602030709030507030803160201021c050a150e040204060b0304210905061903060f06020a150e0d210c3212 65
    0x2c156403103441405030202000c08aa03045012a8280018036500c0e0300e00040940301354090800e071500086400c5450405003050601c400003900c0700c86075602c18445c1c074402000f890141640211026004441c0144140c0303a140081d000540000104165800c1c0007000c00c40c10003001000e14050300c1c115a99003080d01c420088404402e00000039640107200013240200481c28035001c06d5064000030500b55101041c0c40300a0006444400b000e04214001140004040c20002e20031417007a58100030998603981c0844507400704441c0104490f18003400029a1072501a00070440842c45c00d01080c401c0d01c820001d803290b000058403155010340081300789030130b5078107002e078200402c0c00e01d00c002402814004001e40b03803288039101a01003c405216924502403542c881042c000c035502c10341d0798448200f04024041400c0241e84031440540302c01403505400907101b030320050071050700c1d0701031143d000b40411a51454100304030240180080442c0484550701e000400100d04c030202071410b1450310f1002c446 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 860256798 1250 860255548 860255567
    0x21306051201050f0d0f0302010f06061d032a06070f0305031b0a050409112209111204061e150609080706140c010b030102040e0411090601080105010c050703060e0607 73
    0xc0c49482003074040a03040d21a1030403171151542103000c242e00f100403070030107a002d0681002001c10891a104000a09a90100056141001c401c40c990540414803041581c3d59120b0b440c0001c1101050441254819058444100d082e0000c0c010b103082c1030440d210240c0c09154003000303401040e80042081880c0560304107041080315100703c0e003414240c01c564014094055805500940340c0c2d40c80c502c03172055032a402030b0b540c2401c8045860842480140008103602940d2284072001800c0240d04c010148104040e030301e62400480301d166a99079103460b101c015100d40181d401050940b00303042d4a407a285402841001c5a00380c40401ca05460408010810520341e030001d5000c1d007005205010166114840145030342a514a4540307034003120100500409110040035450761000900060020f203042c240e0740709a0242c00039540c541540303414401013002c115003007400a5408801030140e903004282c078084950040c401c984295480f541c07140225005200c00c1b0886610240800c05d407541d1004106 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 860258048 1250 860256798 860256809
    0x30d05090f0d0503070e040e061617011d0c0921070504150e0405070f181d0703021c0501090602030412021605270f04050c120705090a021306051201 65
    0x8042d280c0c21450018071500000d81481c0421038140301c0c1050030b645a40102c91080c3e4280305860040c18005614458001b641d0040c0020407510751580d1260703070081180350704840040182071703c2002d9109248900c55001001d008400303400303008070b034450f454164100c0c11108819440c0e1080300d42d5124482d2410045030f024038031850820032001c00703400072940f944e01100c0b20321071240407035242c915203d03041c060290001c0302a10030030480007480700104004100d200017980350030001044141d2894440c81e901141d0414241d001d0f11040006060101c2c0c0c8002416540d140a40d402405a40782402c0d100508019124160084207100501c907264003e220544109c0c0001d00300580300180c0000d0b00f0181e481128482ca100d0080e03103405503091802985200c3d04009912207074038116401044a000580c1d064416200c0c68100c007006003800c2c0140545264440018200d07030b1310301400c01c102040020f01c0414000c0d001d2049140b2420502c803a64060015601d0359a203c110500c0740001c46101644038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 860259298 1250 860258048 860258053
    0x38041412070f1506050d03051201141f020f0703031106010f03020310020a050d0207031d04020a02031b010f020408070918020108060d020414090a03080901020906040b1308030d05090f 80
    0x4000002c0c03180c118030007000c0d5108100050440d450000900184040d500c0981c0180d021000e060806d584500100007040b04510f0f24a620390300c4444480400c105000d140c1c0d000341c00b90041c544035004c55101e503d203e2009204072400302912519007400e0003115072080300404d003161482040e5030b0013803081501400150200c0d801417469600000e84c0c401107540604800341d0300080182e2030718854011603c076201042020340d079502851800502c012907423740c50311100c81c00b00d181600791501d80201e901d1080998010742c1800e542910350605600c002c280b04280399078505001000d07030607a002800007800390704080c7c4001381c54282c045065525a00c032000c9540005052800140c4c1c00c074507440c2e00150140c400390303c0c02850384045401084141f0702c18140941a004120514600050900c40c4ac1d10a03500c1c2a007544400840a09074050040c10035807251041c017043c4544202170024103038450880f03000d2481c03680c0c1c480a0504650013107030002200ca440c0e60400084182c02c01800c40241000f000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 860260548 1250 860259298 860259307
    0xc0b0d020a0e031902100e0910030203060a0b01050d1508070e06090709030f1e210e0108010e07230c0601050406050102151f0e1602060106080438041412 67
    0x103425103035118444e00a01c02d22020040ca507a55104040d9044a040042c01911070342c141210010764a04442c4000c038464400e40000402c810500c0c05840034119060315010306103641c295941c3c01404503903654020140000e440012200410020b80000305407038560007080d41070020600c000350070018903c5040c0a001c00003000000c0c1e0b003d45074100c070764000c9003108411004020200301c484401c0304c0680303c20b1b2814a4003d00401d121645c0c8851022a25013400400c00744005541c99002480703640b080200704400940600d000300f800e107224040346d07560303105041c80c010701d50702c42a0803e1313024200c654040740c0180610b04252003110050030003400180f600448082c81d0410b540c200401010040e05440c0b4050700790300045031900d000e003103108100c262034030f80550030081059900814800600c154000040d580740545003107801540c0004400c12050740d004522124440452204404205009601c4036040c1070000007e000e20301c00d0020100250781f0150b082e22b820700e8180420a180e40820 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 860261798 1250 860260548 860260573
    0xe10050927010f030c03120e060c06070206070905031905030c060901090302162105010b03030a0e0f06040e0103030f05070209151002011118030c06040b04031e021c0c0b0d020a0e03 79
    0x80c5c1c071340200c0e507001d6803490248002c04401c4030034481440c041a0030006c085034400214901158071449800185c4c01c903805a910514100e80e000200d00c1200d800d0740001420a00300c10050000d0081035000d02c08a03490480070345646880c040e070848400d051030750b444141d40101981403218680300503c000c002030880781820046140c10024030000004078449a6040040103c02c0d004007450407001803d60f500c449100d0000761290f01c1c130740c01e828822200020290010b14003181580d0a0360044003462800740e082da0703030030b40308034251190300300501206008100041e0b0700c0c24100c611402c000d00d104c6802d804070409000c0e05ca8041c0c4244020340e4106101c0880c0c3e0304100003902caa2890340b00d4102e11078a1001c0109080c010600d01b00c44d0800400600400d00300c1c1c407003009004407440741006481800c030b000142100f074014884000d40c44500c115103032102e03805001c02448410301910b1141c050a40d01c04200c4410380c0720450325044143c01240d90413085800212a6546000a401424601003c007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 860263048 1250 860261798 860261813
    0x15220501031b08070e060a0e040b060f0307140c07060306060201230c090a0e270f150a0212270a050616052b0e0307030e10050927010f03 60
    0xe000050030443c0c0880042d15051041801c001c03800b1010b40680da84180380c0c14000d1140c404040c03c0c6008900f45075582215052034011540400d600140850071501e80ca542218040760319001001e410b1030502007000044c00a001d440c2c024640c075140050030924220020303081d9141c4004050035665074090002555119500566103c4410590b0316a2160a400000c2d6074001d150001c0441d510620100007001000c055480c4410488c05e45034603040e043e2005043e61440c0c10000c0d0103003500700031401d0328070076080080c558001030020400350170b1070300110030010b5028044074124154804030340341d0021085010343c1d042074070340c2d0320014000d0088181c90382d030b41e542c4014040140400100310200c01c2540700f80300361030820701c412140080100303042c001c51218030321103610560744520b490b09a00800000208484640e075264448042940040c0104081c2c1a1107400305824045d007009040a50b50314004880041c0e98107110321901c001400840b0118a04c05801440041b50441c5d0144045881e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 860264298 1250 860263048 860263091
    0x503040f080f0c03161b030507090506040f0207050106060806030c1e011803140709020c0a060b01213e0915030117011b0507060b1522050103 62
    0x20203101c0365610111016400c2c14032865544001602011440308003500405464600e9240503c54402c8802103180d603c224401e464840140250302100040160078581d40155600c2000280000b6034942441c0c50203003607a20142c4200c490303955900341484415000280c00da00500d003a030081440d100901d02142e00d01e0700315a25941018160360300c00105030300c00c520303400d89000c02860580c4200d66920f8001500c1104100040c681d020b03001c400309c0c5c55036840c82035a600214000c020140d01041c1c0e11514005c0c20881815410440301c4001c109910007410031848813810503800000342c0601002c03590500c840c2c41c1d0910b24400842044d010341031000700300c0d0720f4035292103008600c2e46c500c4000d00141d107a08180d0f17010b80d02028013000014140c08080c00d20586680800028460384100c2c1000c100d0300101e1080303403c08540144608008100b1581c40903502c150040c0c2010000080c2904070445074100c080d454a40404818003040382402c1050b04800801c0c003070030144140c88916401c4180c5038003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 860265548 1250 860264298 860264303
    0x150403020303161e0302221805060405070e10031119090b1303020913050a06050910051006051e0d02090112060506030a0c031d100c05120f0603070803120f070503040f 73
    0x2008148000d0b081f184191a441030804480845103441c0e4030760711940410550801c02d1941885c0800060642c1094014584200c910741e03a4016940240003c104050040c60550000c00d40c2c0d400d03c5059a8078210002d00700e1881600e0802c1146102d0480100000d20b15044000144001d020440c10b0001c840110000d5075412280f840031139a50203144840d541c0a800b000e400361181500580601c00c865011600565400050307449154080300b6180607900160791130350114074000e070304222051144000c6c000d054004041c9030440c8807010040b5109410442d0b0f01c0550550028200200d0b6030800703c562098041e0075410f1081c42d10305030020b0148e0000500c1c84007116100d44400d4583c1e4071a0b802846134010ba401c1d541c0c4044810a039941c1e4400c0c0f108119500c0500e010030110b641d5000c0c0040c0e44900c1d000350f2a040140d90385411101e500c90000e464150180b14064000c1056201030000d04244070743d8070445809072420700d140381e040c0c5501900c41c0c0c09020b4200305000101c0c0c8a9200c95403c0c2c2d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 860266798 1250 860265548 860265551
    0x114010b091203040306050609090c09010b090a08012a2c01030209060a03050f1506071101021516030c0c0203101a15031501030c050a030e150403020303161e03 70
    0xca200701040c051111500c406906010008000c410020345074003040c06004181c907580c81d01c0c2e541c1c5a00382d41d104205480c02d07600c1245040100854040c0000901c41c200c8041c2c1500052a40c03940c10a00b500c0210444480c2103142250301020004800c081078001142c03490300380d51108a1140e4a86040f00a0300e6541480c250014040c0c80303640250100c440c0c02d000a480035a91b00404c480083c01040f050b60030b11508180c040100b15880907080d00d1000d40c0070014021403410301907548102918881485c114158094105542101e400d0351680340d100b00041c008040c03a0000902004044540c02c241c0002800100840d101c096140000c1101c0c00460003100090700d0040c1f6104141402003000542d80e10501040303040004c1100e050181d070180d0343d0f00700c00110f0080000b0055040d0b9020303140e0040003031810300001c0e440034841e4201400680c6480b040e00c140b1407032032800d040504030840f0240c000d030b40000107000d070205480e18049407200d860303c0d1514225035426486100144c0c400d1020701010b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 860268048 1250 860266798 860266807
    0x308030601021606030c020c010527040605040504030f1115060904050c09160905060322060e0111030411030f030d0b120a210513120f0f0309170114010b 67
    0x5034000c10680031400f040c0c40da40f0f40075640d18600240078022110032000180a91900b405055000c2e8060f681e0140c9200040c00c81007010301011541e41181050407588151103000004160b1164803d0601450095a451654a44118003c4e1003440420a0811164000d0103e8014040d400c5100c6070028011103896010303403541e0500524222040c0701e610f610815017010320820001001151501c9249078030740c9030350340d41e50340d04103d1140801c0f40c4084500c00074940c81b171100e0002c418080c01040c03040300d00040141200552608540c0c415100c1c50100708004188014009050407140094800310000c2c900c10320b071014029103034000e4900d102292a191000482e10b9502d03584c0001c066060300c02122100c0382c0c1d40c2485418042c50f02d80c52003280c1c0c4004903107010741e031140003168080c541c804440b4840d03070b252640c4a07040c40360000050381d60541d48406000010a0580f003802c0040c0242d40d0340014504206d20b9200030914a50181e9903a032410011303170341081040c41194115228450850b071203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 860269298 1250 860268048 860268061
    0x4030305041503140c09130b0904060914070f0e010b0c1b0a0314010c030605010212070209060a05120d030b0303070b0115051306120515010225051806040b19030803 72
    0x3900c080903040e51210004c0e01000300d0200118041c0180b81c0d01243d86c2081c010310350884004a032451501e10313030040444000035010540c1c5801c403d20152154005800b50110718000790300344441a041008401c5011a0800020812700042c0b4054560ba09110307280c4540d41ca2000d5442c0e030416041c009102d010910070f801580d4000085000f1740d0000d10f68600155010041c80c02829070f40ba030640840d203020004211544009032080a000260003400d15140864080280d00b260040034243d1203020724001184549400001b10110301c00780c0010f0460000103807010341960188505e05000c1d500c280914000316540601040c110742c0000554030308011603840c200c0340e42c400c91052a0710003c0c650b60004007164460b00d5244d40ca100072000f04456100c100310480910310b021811801030b80a8000c10b61012100210500c20400710200c2c0c662260342d4002140100000610b48030144140c0d40401c84141000d00404203068030480302440440200740c2042d00300709581c000580082c0c00070002412 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 860270548 1250 860269298 860269301
    0x901080703110f0c01090c06020d0c240f150602240a2403060b0d1227060f032412030c05012c070f0b0706020f07030201061a04030305041503 62
    0x1400c6080d01c0b0a84d501c030076030004140a0700c1034000c100c400c0815100300082c41440441c0c6a400d0340e0680d0f4402d619503000b511001400c1700b4030700c1000c1c101800f81c440096045a00d01c5a017501c40c072490804210030103c0b80c00310401e4002a070120b8199040313148140007001c811204a00400540c01070200280c8424458200509251003c06481c000c600005004259004681ea0448cc45142d040c4041154141800484408140000c000010b810400f610316030252452031456a003c0078042c158418441d81c05c1c81e100c00c140d10150110340207440800141d0303890b016081e51240e45030f8609084c840100c00b038511041e502c0c802c4040c003101002d0311100701842000e0450655801c000248101014070b41a00006101c49901c225941031a88000c251030303801040210407224094013010981d89440b0115070f85900c003140031600d056007004810000341c07541002e46182400785d80001200b50030300741001341540441981c00c54900e0140010000203601404940a0300c080c0c0c010214050120b400a50 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 860271798 1250 860270548 860270557
    0x6010614040b03070e10030209060a0e121614060304050d0507080d090b0f0105120a1103120c151e0403030b0d020612040b101d0606040e090120090108070311 69
    0x80c26054000140700d070070345d444071800200c1c11040744e10807400c12482e4000d03001c03441100c6031550411020b01c01c810089019100354402c0c18009403180144140160072141089045519034010300742000c0305121443c000d4608100c2d58000703854045c42d50401e07485941d030358000c0f01c540000700800085c4400802c401c45058582c00d920507071040c404030605242c45a0680c1084840c0c11071201c140000241500d070007184603d4446040c0c01030b2094802940b00d140c00e0000012034540c05d8460751410b06400031070a0018548040200090310040018078021901d074407005d4003641da20045c0d0825100d45458100c0c00d181c02503454240000d00307660f80c001089000c802103001030340c02400440e200e00800d0b5403202c0030f880340344102100c400d0b0b1f41d41d03c1007000d444001402404621865600c904580703050020450781c20030401030915090555603030400f6003090040b074034120035035154600c840290503016440800d0f0080c2000c82410410500002055400d0040c1681308060316800301188480c6041c0468 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 860273048 1250 860271798 860271809
    0x1050306281401020d080c1b0319080a0c17162c0f0415051c0605010602071d0c09090a141608090c0307030f0c150f17090601061404 58
    0x1208a9403841000350303841100301c02d5800b40c041c1140c00e094035446445414429080c011843c1c1c10410030002c0300b5407401c1862864a6144400c0210082d60388003d07691640380809590b458025280030381c0b0401c25240c1c0304c03011b142030003143e000d48508640a0800203506c9003240f00548035862003100c048801350038035410141e624000004c83c21100707191710031503014045c054403010341c0d003d0f041003030000321103a002c903081910707192400900c43c518181b800c0756903645040004540b40b000383d44840d0100c039400c6c1d128801590210004106e480c03118011001581102d08845006140c4035010107030f284580280070b44200034040008540014980c405120541110400c601601d040c92844204440c406039807004071b01c102001840500000402518030769010b0050701500e40b4581c0d51003543d2040c0141200c0303140310301201140c0b8917001c1c10400500d580550314000096401e01c0c0c040c1162650192900840111404110005100052041c1141c0680c03405041c6d9900a98800d4018020b54006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 860274298 1250 860273048 860273119
    0x3071b110d0b040318081207020307031506050306130b010512031606053414040b070305091c0507270e1038040b040c0804030801080c01050306 63
    0x1c0900340611404554400c2e8401d44900d1004001104424402c201c00c4c4607090440e8040c403403a1181e115054050140d0a2010b8229050b0544030742c1e07400860f600d0401410b25041e500e1008021a14081180c1504426000d024494030011911380c000c62010501030240180c100190100702103070108200c0d0139010514005000075402d0f0b240c07003000303800240c1d40b1012007803404081d66101250544500015201c2c4503000424003042030382924400200c50350301ca0445818030002503842c00340801080b07120710950b541903071040b02004104848100b0b0f100e0384250b01c0d0300001407002071400100c40090301e01c070031420200139103003008203251030101c00f6866400c5420103c070310b809580009100303811503103011014013124070003002d5000c01c800480130b40101c900014a00d00d869204c484c0700b800b00464003030b0010420480040229055a1170302e42c0349000106441704100605900500307050240642901601c072084506000074080c0c000502403034441e058500301124121300f55103d00d80095401c011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 860275548 1250 860274298 860274319
    0x4060b0a0b1c0203060a0810062904090c030603050706080901052202040e0c0409032105090d0809030d1113050609030d05180405040506040302070e01051302070303060b040b0c01060b03071b11 84
    0x410101404440c42252840651000b003903854040180301d040b1940e10ac503a02d00d0030a490011180068603504850030181035580c0c0010020410600c0040d02414254450035420308140324400c0c2110b400030714840200400d030441100041a0f460620348594046801084820500800f0f41c00c2c0914581855031240c40c160300e42040540011100c0c3c4603404e100c480f03903d00380d201e441d5601558800c0b6545209508003c000d45085805031840c1504038299104a13800c140e010300c040b00172240301000c1003c00420210700f4001c1d00c100f425844014010544d00a0300b05540b907008a9034580c0c8000132441072100110b200036100c0e102082c43c3c01c41c54001002401542000e040260b1116010f54041c2c0040c001c4440108080082d21041070484001038201540070403000c070384000a412064081b010591501d1001540902c2c42020b0800b4207a47c81c5010b65900400d05d034242101c0250348076070304458003841000010f6800024034014040c0910440045c2c1c0114a00318220600c241a055030180000c00e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 860276798 1250 860275548 860275573
    0x8030915090c01171e041734030f1209230613020f0f220b01030c02060114041808040605070c1d0105011206080604060b0a0b1c0203060a08 61
    0x310034440200c2070320340c80d00c0110003c1d410b02a6000450780c0c0c4440c4007140000a02217844180c03169030080c028000d407608100c1090415000750f21140c898140054015800030000341d0780030740c1041d841c0c25120002e460301071540c1c004d000f00c10b0340b808000502000c00041c0c82900420340007051440c2c0d101203910440c4161855a480026108038012500e11801001900a0b1780403004c104216400070400720700d41c100b81c42044501502c02007400c1d006007180e0b010441d40ba05064204844400f51280401c00c2400d1f400010201c80b0103041c40421540004010480080644c00e0f198415209450120b030030b283c154a60468012800e900a1040000090001e01c40d540240030708682c5204041c50380850399a80040c002c0001e0008001d62000004001040590b0107038190700001d65203102c01164840e900c500640c140a400c89041d00c403151240601c200c00d1400140800c00740c001c0c0c030422401d060840001810701020980020701081d030000c0466501d95904400d000201001e00840d2610350558 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 860278048 1250 860276798 860276803
    0x1090b0c01151d1810180f0302010b1002013806030a02070308100e18190f0b0f0c04030311011b120506060a050703080a060b190801120f0803091509 65
    0x2083c98810040c4800c0100c1c0503880680c91001030001c0a034010000420740200e2035000304102c0d400c502a0341110207840000030b0b075800089441300e00a8000054516007071040c4000548105030050459150000c03000c00340d45201d1048440d4507548448c5c1182001880045603020039400c48160b0090000c01000990078507038006140d030610a0351107500d0707500c0b0140107524408283c058036441c40007101c00170381901c03a0f400710010107036201001c45081140e51090f0f002c82010740c582c1a02c4c0071500d40303110420700030f800034501d0b0041311961042e105454410b403242440e02481c040241000394440148030251000d400c240c0008022650040031004140e030050400b0313a004559035003560800300010028a4507070241c8890650765120305160100301e90701103458202c020080454999101c801052018813003001d08000c8001400182001e003210001130500d0b60141e028485d03400312281039400142200b14034516990380102da6545a40701d07513101c0790400152100c502e100c0c07200441008640b5100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 860279298 1250 860278048 860278079
    0xb070b01060216030b0105061602040219030534020703080a0801080f151b250b0a06060e01120b03100f0b09220305070b040b01060908060601090b0c0115 67
    0x40d003c4404800422401c140b001d080791101400c60f0512500421050801d0300c014802541c3d440780f0f110340780c021580020100d801c04200ba442c2c4501c80c1042c0003407590984103494000f13001d0741c00c119140c20801c2540340f5920b201c900043e1640301e100350310f01966000304015400b075580000d1550300c0340d803075400003040c203413092203101600e1096604007102c0d0300e8082102241100c04031015092a030707600103071112140940001d10810350b000c101d80c0c00d00221401542220f2000c40f403406803441e03039a00b04052050702c082c0c466080c19107070040070485560428649010705c0e5081c2415290780b94a890400001d0a403445600d805015608102280814652003038040122600341044440025428480581012a096441004010707070200d0458000105080c1c4240b0900d8402c3c074046081e51503002000054404070380c000303055001489159082030340240545202c03002095103180c0000000c01000300e520850701c2000c40000c14151030300e4203401c0f4240181d0aa166180a19921035144108445 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 860280548 1250 860279298 860279309
    0xd0c02010b0901090e0d181a071b0807090c09091a120706020606280b040e070c0b040308041b0b130602030f07110109053d020a0f0203070b070b01 64
    0x742c0034004102c2ca0000d10039861080a030000400014030b4a440a0360b14140107000745046003000700000401509440c201003084003601c8441d0f486881901d0444882c0035805080d82c0d501c444440c0610604000207500002c9826481d8045100c82c50194140c0b0203030711030f80041e515582800780301d02c1c91041c00e0f07842141c0305c0d81c2a222800c505d04101d184071340303e02d800d0040d00010380002011030103500d450812805001901074294206100d440709801d01410203a120307002c05400444c00300309085580d502e141c0d01046500707101c5140c0c042e03940d4020b48804000e1004082c050114041014044510321402c01c4c0b080012020100544074820303a0980e4125007a044d004001054011441520200075104101c800494948c21b24280c1da40300c2101c185401601c90400860b90f20001d00f9984054903400010f00000c2601c1a40241594003060500d240700c0c0c10440c034034800c6040c2e0016900180e903580c0b454000e549030301440c84520001e41010032603440748000b03802c00f003040403c1c0111200040d0403142d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 860281798 1250 860280548 860280559
    0x1e0a2a050c0f0a050105030612150117071a07051c0e130e0c0904080d110415230a02030c0a0c1e03150f021b0f0115180902060d0c02010b 60
    0x19604100049901c16050312500031400580130409940030b10082c6410050061654104030614080d95203402c0070014a00c440080310f000400c25200140704007100010b0210203403861500309900c20007c510402401510b51030001084418007005104c41891081c0c54120503840e8100003a00a102d00f40e18038038036204014009200e044030340d83d44680e07a007036000a8040c0c81c0d01e0100908211074901c0007030082c1c4210004115140050809107d002c102c01ca02007459030f1902d090010700c8011701c640700c420320705210100440407404541910352200c0a00b442d40341e0b40d51034400c1c1c0c2040b811030041119038109486441203203001c025102c12900f040e01e40c144280daa05583e65110f250301084544405004202c010510b0100c9000f1904154410a4a82405440c0003951048041d02109100002d0416000789004c106000300078094900030034414009501c0440c182403440d450800c0402d5045443e950340d20704a41152600e1080d141c02c503440c018100b01d05c100410b0064080c3c01e81d19030403885030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 860283048 1250 860281798 860281813
    0x12010b0c014208060403030902060c0610090507031415060405060301030c140603160e0f03031606050703150509071404090203011d240f03010f0b040b0102031e0a2a05 73
    0x814a1080302e004540e055001061152110349040c1c0c0180405c0f401607800c1282040081c1039842c003002b41d28010242850302c9100c042c0303084207400890740041c140c9020107003041030303020f1405800003600d81c000b9190a90044003011103000140701d03205503070003550441000300000040c08505041502103d48a200050403041203c041050601c0104c40c0c200c1c03108224044010b445109030580380322441c0180c258180d1241800000e4070f0754001014214201204004240030000c4074007846811241600b41440740b100480b6800345121900d0084034045d41e00c1100285a040c42071081b0361007402c694100e16035942d100c1b882c4001950090207801d501104030116421040c11010b4460f22400c10806100510b1a00112108032901c900303c480f9488580c858450b280c1d96400c2c800c4c901040324032400000c1c411803100610003642c054800d003038103640050080c0c401598607d00410704504040386074170f0381c17910b1b00c0c101610060107145114140d071101c05441892400600d440000b407902400440e07620 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 860284298 1250 860283048 860283161
    0x50414010b0a03020c010227040e01270606090c05070c06051305131407030902270f0a063b15040e0307060e0d090b12010b0c01 56
    0x2085828440c030245294100300a050032480b0303a0140011019420001d03280101c0004401400442100c0d20102e00e000c1c4500100700c0d1416100380c40d0840741c0d0a0003844801421503c92045400c100804d25a5100c4c1c00d080c0810440c0951001d0080e08103900100b00c1c2215280005184c0d4008040488103010011004a4000d0080b41522078140c08084485102c0d4101400c0c0900d1208a511100b0095260b008200c00c203003c00242c6ca12580031030782d0000c0e0309207490041050170030010181c51840038000740d4485c42000704524240d407210745c1e149120220380301d0082d0030b001404a94002c1c0d00d01c1d80c5607000b211803466100140c40010310030420000e040325100032002d6000405581c1504180521021200c260402e504011136400c4e004068a05010458039150207581c00910841e0440e007003141180000394100340303030700080d02d141100c240c106034403622500d081c8401070241c070f18400c00100e4203442070360b0250010740e8041c0b44079401c40d802100c40400c091100401344103414034100b4001c4182780c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 860285548 1250 860284298 860284331
    0x8060c09030d0e030a030e06090a060e0301060906030b070f022506030507051602040c27062007050103050402150c0c03060a0b03030d0b010c080c0a0227041403041e0504 74
    0x24184001809408010070580c6d094079604c40858031660010306c1444134503190b5840140c801e0090956450b1059440701c041c08140c00c55025401018041713140103014000300c0c04284100794040814186061240d08000702640780c8108622803582d502c0c2000b4001c0365000740c10b41007000300c9082d601d0901c031944400c1800d03031300c0e400f40d090400d2442906004003009480c3c82d070090b07071481d0102d051054240899540c2d4001c022004a040300242046190030411194402000f141c2c00000e180800803810780c010b4041d0311981c0c10b2060504240c0c8480100d019580e074400c00001400c50030403002e81d60030102c0c211036211f00d600e9040503c0ad0188100103001401903000b50f081001c001009949418100303172100004205115266040100445401e40040e00d450000c140988040004025a941c01d01c1001040032940c0d0b4200341c1e151100320071030303503d000e0403070601d4000d644441c0511f600907950041c0f85c0746002c2c2c1c0d800a5038918150f0034190305000500d42c00b109a0300c0c117407018051a00860242c02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 860286798 1250 860285548 860285567
    0x7060b1c0609140709060f08030a09140418030f0e0613090f06030f1a2d07020a0b01090608250b0a0e0301050406022203020604060507080408060c09030d 67
    0x2580ca458000c0d16000810a5009885551241420450301d040401c0c00e01e1070940c098000d82519a070720181030191007282c03603890300107120300d2005510300401c2800013400301d0000d02c120300d800981031b581d00d1055511504042038602102d100a86d403d4468140185500080d290441c081098142c081c0042d0424808807005042441c601d0f5041c581340032010001000c0c2c90842180082d554031010002070311a948100400d070051403042168201c0e0b41c208646450b01800e01c10006071901e51000000690b69090b00300c103010303d0422038043d1384d4090240e040180072003004205241410011440b028103901c1001640e888030116900308180b0840c4100301450b8490001154403680c00411560550078003c0091030820b213003141c070095484010070300b0340700151f500319035a54005c110b9664640c68401140e00b030003014281c1c500c543e07156030041100ea00c00c5001d2030040140c00903550f024004c07461b04031002880c0d07480490300c5d1443c0107010b00304190495803085101c0c1c0641e502ca030012920800d4103c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 860288048 1250 860286798 860286829
    0x70305011a130506030103080c1b030a0f06091523090c0d020a0b0a02010203061309020108040605070c230c01090602071203120e060105030c032e0e07030807060b 71
    0x1144050090074500c110364000c40c00c007110359540280c011689441d4140954001d610840c5080d4584041c41003441c1040c0686007a031644110b10f020340900e5560010790401d1464102000d00200320303950500101600ca40309019051503907541c405903056426900140c1121180c40e2401c00040120b0a4451050400d03544080141c4c4082c2c0d940c0e9a620742405c941c0040c6100404d508034159071802c0c4512030740c00c03071f540300c0002d40d501208119407400c251100f060041c001103020070a108441d40080d101010141c00500015904c100003107410340208140c0307071340a4202c16070740c46801d0b10040008030b424130080e9144071800b0300d5075403880301d5005140b03000070307209550043c12049007080c1081c4040c18141030103404006a110f16003101c4040361180308520b40440029007103942c144030906142140310502980640c0c4502c650006c1524070000090141606154180c2c015190380c503044040c0c0340141070a140d6000e0b0200010230010310500420903248202001d20a4111482c204022040d06c000e10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 860289298 1250 860288048 860288069
    0x70f0e04090c050f18040f03080c0301080a030f14040906300b090c04020d0e0d080c0f03060f0901080a0308090a0b070e03070e10090e010204050a060f031113030b07030501 75
    0x5100c0d520b4409244c680b40700014002030b035403a40c070302141415154252420349403035098414110034107a101c068140c0c010b40359400e080c919407404000ba50340b420411801f404110381c600030086070314440d051a1030004c2c29921650380b1183c80d826144018016481200d110141c41042c100300007112010b59000b903c1c0d1040348a0300c504c0c035074550720300e450801800d214081c001c10b91a00c00c0c0e43d0f01c2c0c1c8007500768401180000503078045034181c11440e11014008007024442040308211428410104446d516000e441081e522603e4401c08581c1404403e41510741c4000108d00210fa40b6400145100306180a96160001e07038803a00c0c00542c44503000c800c080c104203010000207031414060104107409d014090102d80c3d540f5902c28281d0000d01c000d540301504c600918104001c00040f90154000342c45541c4000c40c0f50510300300015085000c24460301e010701c4029811260300301c4c02503005068002e40c0b841d1840d41ca82072401d6000300c41c800ca02003160b00408420101784164841e205080c1610902d00380b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 860290548 1250 860289298 860289323
    0x31608010e0f0d05070512040902121509061c0b0702010c020714010e0f12120d290121050705130e0f1801020408030c06090606093903070f0e0409 64
    0x900725581d5002045c00d480e9440380454420146c1d81110040000340030828005880384440800e0564405025022503a0026200500c0700c10390344103805c9030b0304040c04a4540307040d0f414080002280d003000c990302a05488594042046264064200100000455080c1c980c42602c1d40f00c1403088a040000542c0010074400105500d410280c10544680d0001040c141e510030015000714a00b021001c01d64020f8200891810b50a50b01406a400c14982030140300010314010a141601c0240f42000c250403c48144032440380300600240f51540100100d505120910300f0707a00140143c1c0c01424650743d60000f4220000c0c0012024022500414150f54030400c5612201d45c2030501c0c030380c1c02c403958159560810001500900c104001e01003004a00c0c0034003060b28001913240d007804001410540560886d508100250300301140075020003024152400d0112503405c41011204040201482c14040010070320000c40e0b00701d03100050428032a9248418491602c1c240801c1d24404c420040007140c0b40c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 860291798 1250 860290548 860290573
    0x70303140306060712110c040b0603040f020f13050108060a06150e03030415080f010911030f09011d0c032a060f07020301021204050f060105100c0c05031608010e0f 72
    0x30066800120040070035007045110f403a41201512018032401c041350011a00648030102840513201c1d002c0211400c000148070000410494400244000c200c0021224940119039075044460801c00c4c01030054030400c0503610b8454000c003001c0c00b90f42003c1c030a10740050000d5189015000940e51034904501c41e800841d01e082d91190620b11030507030302d80424000441d011804240748031003030a40703a641080e9070070a0383d290300e0f00242c181c0007080d006040520f0f0b012200d40c284204c0f42c010802c100c0e00e00803a80c60031a8240103100008c0c1104d4002c51650100510180c0000da13410040e00071401d07103444c0351510b40d114404181094070030601241855020101c0d03c0c0c914007901e1560f01d584070341c901d0601c25600090072a4446001202ca0440010070b000078040c08010003450140b80d0b070000c2c2055418503000401035000d40643c142007000b031b0b030280020480014140c0c1e00802c1c0c05021110008100f81c100d115950300d50281658541c43d21503600010360300019004640c20003403010380080750302903 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 860293048 1250 860291798 860291837
    0xb090a0e10230a05040b0d120509090c030a0e0a2301021c090309080336030d080603010f110a0f2007030311062e03020405190c02070303 60
    0x40c20103003051109200081d0307001c02082c960380031040c18850549801c00c100c0400000414580104e4025482c200011b0601d80743e0f00800040340e0341081d40c1500ca031001d1501110365102e00183e0503042010740341846407031695a8095805a10500e40a1006d00c0f0800c0032503589504c4a04060701c00c900c180c0415000b948108803000360181510b00240c5000d6034410b42c023810301c0201c9120b80301c40e550380588805066000c4103581c060583d440c09586059171016907261281c000040ca205078081d03064501c107a0034002240100fa800d0f003e4180c402d072401c5510007404581003110081e00079401c100c01451300e0b6509108901418069500d02410000780c2c40c021102d081c1030311041d00510461074441e41e0039441c00860004045046c00040424a00b9458020913560050b8080070322030b0302a41c01c0c0b0801401c20240f50030140c980e01c0c84041a01150000c0807200c0380c0719807005e03403c0340ca40303014002014040f2101d0550720035420f105000d071850742c513001c0340d5420440c130000d80010740c0ca07a01003101d0300a9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 860294298 1250 860293048 860293051
    0xa061b08100e070c08190f1d0f1c0c050108100315020d060302031e0d032705010b100503100e040b0a020313080406050a080f1603052d100b090a0e 64
    0x240c60203442681c940d07540e1200c2a1311030b1b524500660300552442c401c859000084548010442c0340c24040511569003001403115040803061260360803040020890321400312003201118482031080741051103090081031000140905400908403000241c20303d48002030582c104c0707910110100881c032654404000940203c03903200100c3e83c807941c1c000090303541080111101c0f030350001912076140c03c81401c6454110583c2c07182d010306080802c00540400181c0c1c103c0400f40308a1000c040035540d80c41c0186c0100944000e00b50710102d1141c1c00000036501002451044480743c28031a149902c1d00209000700c10200e500170f00d034071440c0380002e2410300c0c0c03a005141c00045542020300400b14683c2c8048154101d074100740009200451030302c0220745e100c400b4640011b5041c0340301c00c1038100106191030303200003a07840c507062503203480c041000100c201992507819000e5001100138038841210191510100b0340b843d00304075450460110386e00c40303c0340403204a400000c04c420403103032400580b401e00500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 860295548 1250 860294298 860294311
    0x40b07060902060c0708251511073005031e07060f02030f1e0105010c1103070906060207080106050603180f0a05030c1e0307080f04080a061b08100e 65
    0x1c458001c180140c03606409030580b00003036406004802e080c5103546141801c46540a081e412140d880030310301115000d160010340b01d070320094114030740400c0c100340d0b00c05040c1540102076208503400010f2280c000240d25001d40758103100e0700e0b48100c1212a0100e801401c2d0f0002c0c003d0f070000c10200c4041311035084641515258000c543d404c000d22900e0f480122204040800314140d0004100290400c1000003d6400004c0d0440300201e20641e40c64074180905c1401071a042c001c0d04101907050110590060070211002403c6602da1600d5035056005814a0300c1030380050b1044980c0490501018004d18082c0e500c044d041da810343e9103506140820211036040341c40c3d40c1c002ca20b850300014009000d40d1800e14040da00030355940c0c40426143d80382c900060800d583d0168010b408040c80b603030200031642010b4011a455481d2030405103010b60512a5902000305849040d1000d01000080c0e0030089075021168510f0b1038036888603805442ca03a004540c2100d241251040500400b4401c0e04685c0e00002c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 860296798 1250 860295548 860295551
    0xb040b03130b071205060904050604020922081201080d020a080d0b031b09010b0414040209041e050906060409020f040c030b06040f03120f0903170d0c0f0f030c0203040b0706 76
    0x1036114002c0c0c0e41401c0e641000000e000943c401c00c4c1800038007a1179081001511824024605034550303030f4452078003400c005d1145141101007601c0300c2c01000d800b500b40500307102c0c0b0b15000f1020700e00901c1b660b2003030b8a01d14503907480c2c000010300a0804213443e03c8000c1e85d40c000c3e000d401c80701d40d030700350395603102d40c044280480d80c584130400e00d40c07410032015080c600300b0391656040060440401c04c04400c160f00c0300403140c00c01c010074803000204c441c4020f0f01c4041900c0258544425000003800741079080524090494400c80c8840d06225640000b0301030800700054950544549060206a03410300c68080c1d0402443e602903001401c0030b0307000b0a00242c46281c0000d290107500c0000d170749540983d1100002e144800001d10a1140c10440c1c9010341d04c0609110881d5041c42030042d0099049100151484000005886040486004650655082402c100508400154040c01070400350782c440000130481c0c1c94402800340070b8882c101c10044940c008604240c60f1107000107256006000c21111203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 860298048 1250 860296798 860296831
    0x801081c0c082215090614160b040c120201140a02120409020909090a0b01030f0503070203011104090b0906032e090309030201270303110c10030b10090b040b03 70
    0x1609100c00307490803050301100706900f0b0301c400240466040190300640e50054141d2010080c02c1d030004451402c64286050200080320b1007280c0003414002c413800d080001c252a0010000c0007103000c08039108903c034a00c003503506920303240500014951420000e01245544103c0e8110145640141c04480c400784116601c4039030382c4010302d0007074201d0382c86010f680d5000306141c0300520b01900c10303aa000310224010036001085031540c1c1041c4c10180f0002d0496144181c00b0b00034071a0074021a495280c015000b402600314080d40d0300c490783e020348074103e940d9181c5824884245455075010b401003030300034018910441344041d028201200c44842c950003c2844240b000648214042c000150340244c07110580903156000141a031740e1106694016055043c801000b4801c410713030080c0580e6014545904051452001586031011a03981c080e403220040c68a650b400d070f4950042e4000740820342d0600d40600c034501b015503a41c0f03558095055914014001403020103040f07006503600281421104511 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 860299298 1250 860298048 860298053
    0xd17190228111005100b07260322120509190b040e070807050a030908090415050f0d05031801090b1201061d010c0308060f040c031b0801081c0c 63
    0x76035400500340000700320405845a00b00006028210b02c0c41c02141c1c083c407080c5040c1c500c1d9130a145090050003091000072883c0310a2158203000d03214240c103c01041c280c081a01c409020746034100b01c41c131070a41c0d4201d0030821a038424a1300325040c51641706026941084181e10b0070765880c1c0024680d10380203240c00d1242c0d101090041c0d90600203104140d1442d03951402c20062404207100284084148050728052280300d0798881c040b51075450203803900196003940c40c540304c0440d1007154460369009042900c80420001d040e11040100d071022290030b625100c10300d09000041c14050b0014001790000d000502c000c2400e10606000c541c03052424200098640602d00ba164002d0f4080030000e01d412001849015000600040710102d80018840804540c1000802803088188010304008014010802c9521111424503182200801c28803203600810340040040a9644404040c3c0d0189048451360b070340100860340c182c40700b2802030410700c581e06018050b4032868409801c20405002e450001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 860300548 1250 860299298 860299357
    0x1f0b0307030e01021917070801290f0d150920160203031b060702060105100e0a050301061205012406051b150612072102010c02030f0d171902 62
    0x80d10310260311101c40446c034900090070341c0c581c010041c000344440c400050000c9402e000d00d8402ca400c015607000046d0510018841e035a010711815403030303a82c0003c94140d1044070036400100507175811160a0131550f40c0c4912440a5900c9140c040980c1c0e07242004e4040781181c43c1c0010144044808010300c00d12031113a011920b1940007150524000b12050003200b05000c3c240109a0410200c0c8000c00180d4106000101000000a03080341442113400c12101d1946920282d900180001030080101699030380000e140c040d00c0400031525546419031101030f48a00385e01c0c0418440319218801121820540c081c0ca995220f02c074410042e42e006c0507400111361041145200340d201d4030302242e003542860b60902c43d11107600c0d01040c000c0e4001c05c030b0511030826111908480340c00e4030203140b1607401c1e19000584080e4503402004e50503000b017141c4640840d01c00182c11a10182d42c0d654114204401c10300b9a241180a49080d923402207141141104000190041c0041c0082c074000341d51b810207410155003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 860301798 1250 860300548 860300587
    0xb030703080304121403130f050d051801050414041104030f0c06030c03020903060402041e060b0a0806030703030e013e0d0306051c0314121f0b0307030e0102 69
    0x120070a400104010070010720b039813a2040e94099092400000303000b41181821800000c2aa0b41c1d158032855a6400b403110b0151041000d07504034060382c20380403004100a056500c9144075000801e280030400c0441e503c41c5044a0446101109042800582800f00009080d501900e81016282404040702140328a0317445100c042c4070346100b420152030b219000d000c0d03500402540d814188140a4501140c401007a182c0c0d00550483d80040d1000d0000c20380d01200c440c0c0540325980710301d002008030b011402d82000f05901901520307000d03403070740e16003080594030000741c080200000d000d01e55801e03041d4021014462140d8400341380b42c651603440306d9a61141403c0c2001440c0031740c00c100d4400c1c1e2004040c132400c04044101e25090080d2410b10000c40d140144000c2e4482c08290000369410070315105900302c2801201d00ba41c0c003541c58201c102503000e4890295014291100c1d081860b50b41c80303810743d8040044a46050066042d070356489016401008204052400707035400300504000c1441503803201 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 860303048 1250 860301798 860301803
    0x7080d05040e13031d01051c0614030c0a0b0c03040b0a05030402150f0a12020d0912090603050421031b12061505160629090916060e040b030703 63
    0x544961801c01c0c450007402014009036000e09411000e00d020a078445842c0000704002001440c0b503240a5004846911507024440c006010142d08030030b00e00702c02c0c9c00206c200c541c200110340d04039030b282c0e0405407250420840c055000300610070421803041000080d02c2200c124000307480c100765582403c000c0d65032180b03108000003200041040118a4525804522140c0040050b8148803810301250582c0c403d0070044414000d28090b00b41452400382c040301e02e14203205009000b55171003031501ca00720301070389551000030035084400418100d100b031284a00ca180c100088420029421910300410310b0040307400800c054903001e01d0401d41106000100021030b0300d5030345d60b81941807010110200c507001e4010f800403086101078036100d10752010a407120300e111000b10341501d0800d85810401400031068116003035003441c0c00904041404071001416900584003a043e80d565400c3c211b89860040201020300e440150061210900c44c00b6685030ba041c010b0000507920300c8a4002910303101b0641d104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 860304298 1250 860303048 860303057
    0x11030403090305430b0412021203030f0106030b0f0904120f020309060711010909050a0204050f09072f3301140904150e1005100b04090e07080d 63
    0x10403c00c00e041200c01ca02c07402c0790029403030448000c0040450b007051250341140240041e030300aa04422043c900000500450b45c40d195116a51004240480440e00050f0301c240251041c5604603840482124031031041500c010312143c0c02c2210a400403d048040d158100d20600804442602c600024600650040420500c803010203800108228061b0071100119081881704c82800d89a20f0207a03002c0a6120ba0341c005110036800048030b4590700c0c1c0c2c0c0805c18560030310b0180054a8035603402001580c8003520902e24610b51102801900842940c900c40040c0c0103074524001000320303241980c40080d10b030000307002c001c10649881d45420310305080200c0140540c120310b0000400014000c030401c5184071005010741c9003d0941c40c2101c50400c9081c0a1142640050100801031180110f0011140410000030418488542d50b4100180d45c00407000c0c44c1c100030840960420224000b100d10003010146001c2c00d000246000d01890a4000e1a0f40b05030313078000c140b541c1c2c2404084c0ca028555500c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 860305548 1250 860304298 860304317
    0x2701240645050a06111e0a170d0c05070f1214070506060a0e07050316050403021f031514060c0109060e1c0f0507020d03020c13060914010608070f0311030403 69
    0x10001c08204503800f144c2030020400c6400c2d8180404a0519510030043c0034005841d0030b200901410161f48190003400c1c0005500b07003540d0400c3c0c100140c81c84821440c1d0030000758520040a40710792088000103000c10481d140c050000880862804030112a43d14000c0741023074802c80c0b1040b1940000c0000c0f505034020404010b840c3c185200072200500d040088030241c0d0070043c101800360312003e000b0391000780c40342030f546020a00440c200c5000315805070000e13840d8001e00b04075440445921032441c000904228056203040c03000400201542c079243c0242441184210802055a00c100b41c402c6c80703952950050004100c0c58420007280c2e0341031001030a0040241240541c030014005440b0040c0070701d00d614549003030f80c841d00b5601c1203641640e51081101d0181000d80c07606e04160401a40148082210030120545400541c01c0b100c1c801828090b00f912004000c007001001d02400d070001e07100f440003a007141c4c4540c00019020000d0f04000408408041d0800d00942c42241c0c1500420240074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 860306798 1250 860305548 860305559
    0x60b0c0105090c18280507030b190b0a0e10030e0d080f06010804150c11010c050f030402010e0d0501060308071202150a02032701240645 60
    0x154030390221500d0040d00d100184080050070381545104081c02084e0000f0009407042e004c08040e018841802c408680c0040004071600c01515003114924000303410040715120314107180700a8114903480c11603032a00103080c14442d005035000000304e90708214050702e110781c8035101e52946103011605580e01007400242e5481c0340d07107044101d0380f013002080312050401590070b080444103034014209281c100895201d504021701c05500c90100381040d40d02c0d0050204019810000c40c0d1501c084403002401008042c40b01618607005030050441d444004000180042d8071a460118082ca0010012000c0501d982c0b1040c2c07c5850a400440d040d03000001c10600f48811190020207a00c607a1000b0440c91aa2800101d032070708010303101d11101600840480d408405c031003038119455801c0b2800b85403100300c10400c940601081000c00561121444200030740303480052101e23060b01e289484000c0c681c2a8407008e2040e14280d040307164614900d0b409400103403007500715207422070300003134092850003170800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 860308048 1250 860306798 860306801
    0x121201150801080a030f03020903030309060103030e1e1011070b0403060b09071725090f0e070813062904050105060301050112090c05121b1909020715060b0c01 70
    0x12000c50301405606001040186070000381414226031614194894010746041075000e40500e09070290315000100400020300800100305049034025a1241d405215801c1070105880112251042031140c180254000e400c1000e901442c5c08003610f071491007020041c203a6810007950b41c0001c608801c3c0001c1c1001071108a000b450100f0000321006546814160005400104a113540304a1091081c00049400154241c1d442e44500c100e811440c4201d100c0f43d00601c2248540501080e8204400300400c40d0390b018040c140c80343c1c143d6116201103486001120350182100c0200315015500c808011208000e90001c15007804c0d207624482c405202c104041100f0344105030050381c0a014113000400c2542c0e4040508118600c041a0004d01c00506007009138040c1e070700707401c000d030401120603240c2c003c2a8006040039007801d5603840c44041500c90401c05c94840b0680b2400408030300c0400051080700c42541c000d00303800c1d1050801c41c9030740610440c40030549149a000c4090200c1c00b00341d0500d00343c0c0a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 860309298 1250 860308048 860308079
    0x80106060e06040302091306020c03041d1302190b0a050901020f12030114060717071b0501050d020c0c0d0809010905040207201305040602091e15090102121201 70
    0x1800d198001191240c0071404038003c510011303103d042124003040c402400707020501507150b0455800d55481e20360005842e501d034024845d0528000308003640c00c9002d01018180b80c0105412021513402c00c07030755000c10520b03480c40b062403054003503101c20000d0301a5134040180b09480450302d4240d1107c2480002a042480300c540c091200c2d0000343c020000351120000702e230f054402801f01880c3c0c0e000c0d210045a01350041c0100244899000000e88001c4484c82010b041d0062044100503541c11408241030521071381d03481002c2c01318600344070040264106030003070100740e10340030200c450010040c000280c0c240e401d40740981d41d03a80c002513141d1055a211188a018182c10f540030743c580110b5950700d40094543d45030380741064a01402007005943c405000055800c0030074000d100358241030400d10000d41c0275181c8030b0710400c8415240320070300408a456100a00380204468a80f51507200c00403807607481004040e0450103807201c4007c000e1203a4029011540308806001410741c1130402440c184c815 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 860310548 1250 860309298 860309309
    0x1210c170702070513020f12060406120809060f0d1d0f01110d242d1d040615030302010207050105071814031501120b07030509151905010f080106 64
    0xc0900300116141c001070f4210458205588a40035080140c080c0c07030007402040801512148006452880c0303900e4610018000c2c00101d4081000c10741c0c4040c1403000c0300020500420681c82400707460124540781d0080c000b47c46078618224035000e40100c5041c1150ba21410080c058202e43c0810040e2410400c10086d0003000075008002c8000ca03407800303081724080e56407140c0d02c040e1500115010f00042e000c03404200410500b4009100c0e8603561786081a06503150035208120584840d110072400e5440d200080b42d0488000b100403644c5e20414024000c402170040e144103032201c00740031207042d1a03d6400020340c02503000603125401072078600c0c251540a0700d000d040003180386124050700c1c0310450503011102c550b1900c046202e00e0380c01190410203400f6201219440e03941c00002c0c0765010f03c400c0e030b4080303104040c0504180e584503070980031940b040e01c6801c02c61340300e10341c0c1c050b4058403e81050b03048500c2803020070f41141002c008905456098001d00c02600302c000e0f0802c070006090050102810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 860311798 1250 860310548 860310587
    0x60105090901090f051023060f030903040801140708041e050613060b09060609010503190207030c03021606080c070f210206010803030702060c030a0f0f0b0a120c0303080601210c 78
    0x1e01e4901a07821104e03114200340c0345040b03604000b5034541e03140422527202d102d1400c1803640b01e150116106850b03401501c60740c0c0b0a5400c00071095035020804111510404894071105281e0315913840302140d0301e2040c6084c0d42c8850012050b1004035504000440c40303181d00503040084d114952a042c004d44501d400030074000c0a04206003d03c03580c0e440c0035114003240a11700b8035204c1c0e0340c8030030341c1c080080480d80040364980300042078400d00d640020314102ca60302a40849035121118200741007003c0071803091030009200200410392100200c0c00410384a805000c1c02550107400b80c540f8a03418a240301440541c0d861141040081c1d40c042c82014010300c80030028506614100d28060b480e810f005000301c2d030082000000400d48c110652100758008032648040081050030400d442c001c102c96081e50b4411842000c000600000d82c400780c2605541c4800140c4c81c9921b1b42c0e030161341d0b051000d012181482040c25140303600360090044a04011080700c40490742d12411040030f403045050680307000140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 860313048 1250 860311798 860311831
    0x71517010f120503040e04080415080907031101030209040f060801150b07030c020d12020f070b070503040e041106030f04021c02031515060a091503180b060105090901090f05 76
    0x11204600300202e400c0ca0118a11408861420605521658000045224075682884203004040015200341ca140050310f61480380e0b07600d0706444240c4218cd01e00d0f45940141002d10001c1c070450200014004181005030074075000c00000303010b070380503041c0800035107989407010031011000f40101d000b11201301c2118616641080180e0000d84a09040076042c4084503484100319295052652091508002d5496021041c004025195a102580450284500c074008911004c03460111101540c3c440015841e06103450145c01d030407003000b04141e88907441c04c500c200d510b444100c02507201d09443c00c070402d298541803041111003c581859051001d03050791031140143c50001ea240400c0780039965415242e5504140c40384d00c0343e540880c0a40008002c6a11842160804a26015200102c01c0c0e04e8103200d0040d4100d08a03074500aa0140c803404100c00f90000c00c40314403401e0303044032040c076040e45043c241c1e10101355645070a034403a1030300b1990380e0b403024400c0d8a203218664000c6440d95080006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 860314298 1250 860313048 860313059
    0xf0329150a0c080702150d0b040e0706021e010b030a150609022a071a0705070b1908070203070507030c03050c0a0305060a0f270b0a11030f06010c0507151701 69
    0x1c2074034444000d08143c80001d04800355a1241d186024600d0483e065950310302455405001400c880a00c036801039041404084078a0004101c50050364081c0c1d0040c015610710b040000f00074500b458044840355030b240301c2400380c0e40303083c840406854000c80f01c1000d60b0400300c454400308d4400740d000041c0c40d8810306c4030b420b007548030030b070060031031043e14905400d4440500380e07413030500041d030744020030103004006100d900c41c80503400303050224040c00503110503e035111000c050340c0c840c10000090a0030780c200801442c6000d03501454001704e461044900f05402542e03514070b403502c641c2098410211004080040110800400b818070304152452401c05146944c0c150799040081c180040b0981c0b20106c1100fa170f20b4542c401d105022452040580d41c4442d0300b100c030b00c40e81d410b250a40301141e1a0000400100080c0580c0c2e11840c05030720680d2856858540903016031101800c00e81c100700c4041c1307550021680c1000320201030201c0685202d00340101c03140142c004c1d0303101960043c0c401680b4004010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 860315548 1250 860314298 860314307
    0xa0c12050c0f060708041112011a040b010801050609192c06042904020904111b0f07140105161112010b0102100203061801030f02130504120f0329150a 66
    0x80196010b51500c4842043d4800079007005841614023801e50300e070407080c038104c130895451004901029101044000044001110090f40074000c07141c10260820440750103040040e1643c0313050841640301c03020151034a034414410540045038400c2c1d8840c0489849542142440140c0c101c1411138040100125042d1240e10302c03d00c01180c122042130103009140d941d150798045a20b1200000c104004882204000400640001005418907203a00b4400070740c0709030008c0e90400b03140d11b140007442c00034545405039080c00a55000c141c1045011b10403a24080000141c000501d40b1540800c104240b001c000d1202d40740c01c0602c0601160b04104400383c0590300070a444113440340c40000969a60340742004a242900c3d0428001c101903032507400007041c001018200d01c101c5e4800c4850403021201074100400340d074801c4da4080c20a8400380d00f60b105450280801c0c8803091041c0c10046480041100144456144031000307550406ca0140c5940c11860242843c81c0d19010f21040d5904140c800c1c03800a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 860316798 1250 860315548 860315551
    0xf040519050a120513061737061205010506030c060f04170307020303070305030a110415050a0e030607020f0f010e070509070e030105070324030210050a0c12050c0f060708 75
    0x10000b1418220a12140707200740111407041c2c50961100100301c1c3e84840c000c2030080c3c030001381401f000b01840450030a08501000c1d1140050246d148003090f1000310701241004400c07495605020360b01c45c070002d43c40440600400c0f15a018900000c3c031440c1036001d0600300101585003511a50f410012000410030100130381d010b4038000281d02e010b040c40b0384144c3c3e29500c01e41c54060350522021030079800b05540b010003180704400e081400e05c00c2c0b012403001001103008902828903400c99000c2c40701e40c140d22901c0a00a120110f02e400000961000e0100307081c840140c881c0c0c00160401c1c400c0551407a030400003825500600700003000041c4c1591040713034607030660340181441202c450003c140114482c682d104d103e031100500801550038403100250003030028001d0012806840c2841c0e4180c142c3c1710400e03400f00c0e42c018000030380c9200500d0702201c01d50311045046080c0901001000003291003840800b0000300f80d601c80c1c035600c8a40a254030702e01000010f1544455001c5001c0001d529400301605 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 860318048 1250 860316798 860316803
    0x30b120109150f23070207090b030c01050a0e041a12030918040203150f010e0a090c050913080c1e03030106020a0b191401140604030803010b07050c090f040519050a 72
    0x1090382c0142600c4001c0d1100d1101d8050015840f0001c1c105820085802030169170180c088a000326a52180700341519500002d0030790540001c106841c0c903501031001400b10f00030501e070101c035092080740054115204904400d400283c070b00d50040740740c10038400d48907410140800860070041e80c000000d001101108200c081d080288001c2070854400300300e40e181c1c04ca805001c490385441c140f00407a600a00901c41c0700355290b40d010200c3c00f0000140704034000760342c01410b95480c0c01e0910003130200c20b2401820781031b0303103070311a50020000c00c0003c005040b03074aa0303407009041000011000858400c107070b000302115581080004000140c0c00040300004198090400041c55a600c284641c0f20320707000f9543c00c00d0702e04040171107088010262226041e9450880010b181100301c10038003403640507500002b045400204010302c060550b0002610909100b40110340c51114420040b507003080c0d059071551580c0031100d003030008111007031100030400ca551225181480607a61107040d40d410180001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 860319298 1250 860318048 860318051
    0x207050a0b27040e281e2607120507081207020c0a1e0b040e04060b03010b0a15020f010e100e1212180c0904081315021516050a1404080a03030b12010915 67
    0x3071742c200006030b03000510841144d01070038070b05603204078454450390103503108075011602c0000034030300da5004102fa40e183c42e800c0603041c2d0403c054a00214001c0201403c05000c3d8447c13011071003071903900c0058090140c134908130b403904080207183c5600d41c003400c16002140316040512007070042c03003880004250300a4001d00041140c0a403800402d00501c101c84000e80c026400c580040f41001410b000070401c220030b40e0031118040a6000c00b01e00300d5504251042c0680c210a1020340905d005801000303600c05080c2c00c1d9404034a10318245051940100d0342d03103403580058000c00002100a401ca5a201c0c04107402410300c401d09040015010400280010032441c0046408084103024030100c0010300600c0654030000a0314a00282d0340b500b003640c00b803039407803131a000080048030540324012844d0040e842d0281010170030b64007030718040c0c521034451035811014000040c0f0f0590802c00301d01801c2c001c3e01e00241184244052200764000c0c0c03c81c40e581c0d40e061154000000307440380069041007072103010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 860320548 1250 860319298 860319353
    0xc0302010f0b101d04060e0105091b1b151008060a0612030305070c410a081b0124080a050c060c0106030c03060c0207050a0b27040e28 59
    0x83c122080040c0c805070000e21b807504c04a08655405e40c10340c140c1d901110044503e42d140ea002c400e0103210107041900360131090204484004035101d5001500c081c030301c20780d02d0904c542c0c0a01d4880c42c03821103104021018a050400001c0000d00c1810b4026000f040c09001b91400c040d03401101500c1100020209942c0e0800155441e00c241d8651560b0f035844504042001c08812421060340d010681680701c054030306a0564180700c401900740042c122810281c4001354081e1602e00e5190030049184902440031004004080000c1c0304801140c6282903011b1403841c60400800d10f41034241d00040410360042d21aa408181f00003407207894200200c500300e660714220300e80940174280a500040500800c58000f008003c115040289100c9260b801c89004981e00d05c10002481118814111000002c010803401143c1e0442c0242807020343d10a0680103169060104044882c0780315902240d400a100f612005c411085543c25042c045507404d0115660395115408007512450306400012034449 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 860321798 1250 860320548 860320577
    0x90e0f0705041508060f010309020a030807081c06031109011409060f132003041505040501180305032410030f0e0a0c0e010b04210c0807060c0302010f0b10 68
    0x4003194064003c558943c0841164400c01514002064900318414009008150807030351191262000c2660001c08011030240345846000640d40103a0301034810000c2000000030205100b00300e0a141300144000080540c0385007020800da00c4552040c9129104002c0104000803407440741040341d01c0222903010594840070f0000d28004040e441d05508111f003041c3c9021900c0a03944482908524500b240506201100c410303c50b511084030020101c240441007000242c407141e0005610501c60800020490a1040c20704194000c424044002840000400040014414030700c50340c02c080302a4504402c821500003482c40070b80344100000c265032003c0303c100d4600c0756001a4a040c140c10251640c12000342040001420f0340d01401420b083e00354000600c400c060001c0700c04031140c2a62616000b080d041d00c0e40311070050755201f9103802044403800b141c40741092203044000c0c5900d854403240e0b03120038a0017a00352000380140d80401450b02c0c40d000199101c100c980e100403099458405050f152a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 860323048 1250 860321798 860321807
    0x9040b040618050f03250c18060f0e0403020118120507030c1502130b09030309040e011d1c0c0b01090510090f02090901080307020a0e0c041205030d0c090e0f07 70
    0x440c005001c51107000613513900c818020005144c040321540c01e5a60980da541e8a901b02e000c21035900030001000c0c290200044141001c0d01c241c7d0901401001c28295590b00080d6400c00351900004000e0b45087c00784810103809210301d443c401150883d10b075040012b82c0391402e5503c0741e42c00780030034081d0008401d002c00d80320f06020011075a001d80c8411102e4404082031001350489543d01c502c1d400b8440b400301e401740c1030105441c40c10000900862400545074140409400280c0c0d034826651348440554002c40060700301000d040c0c0044006052982e00a00c0e03c20b034002010030351a0601c12460b190f00b000c2441e503007405055586100e00460240c80c0d0194101c0f641c0c1399540070888035403500d81c09a0328030b07800760014a00214120303404011640c8619065450348100034009600912401c0100240f20304211385c10703480241481c0781802d1580d04e26031340038805000c160444951700b0000382c40342d41803858401c031040c03115185003e4944d81d060420780b24052070050070101140500ca0000340c9c030300b40300e13 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 860324298 1250 860323048 860323091
    0x90d080c0c2d07080309010e0d02040227190506030c160c0305070e090d031a1801080d03020a0804030318080c06091b0109060c02241809040b0406 64
    0x40200300ca90411000941800882002580702c00080e02d80d10741800240c00000c9450039140440c01961510240301c005441c6d4a450141c0c0c039410401d280d080e04090399851000c3d195581091448803800004152080061810701e54054031501c44940000444030203d03541005944003510031035940e4440c02500c1c0d0f07070f80c0913100c24040c40700708640da4002040418030851003168862320880303810580302c6400596012080f20654102d03404010081c484a02c01c1c5c00c4000204440f0301c0400009120401203240914030440703a1003045400300c01088010710030458030701d064145240c21401c3c0748130b458000b000030b440074101400301074640810ba4407489103d5070f0b0b843e14552040c0015902d41c03a035510355890340b00c200c8400c2c503c1d00030305030030f9441c1d44048401c07541d024070140d42c0d5542c520304161068900050030082030b41c02200900707118129030141007002e18081c10440f8881d0f00d5104149014071f40d171010900884c040c0400c002803100261050038441e030866031007900868546400c015049100e0103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 860325548 1250 860324298 860324317
    0x90412030c21020d15081509071203080a1401060f021b010509150903060a140f09030d021b030301090b1c0c2112081f050d08090d06020a0f0314090d080c 67
    0x11503400160f21071001441d00e01c0c9601d001f1004c2d143c0c0e56642040390701d400d51441602d6030fa06e44a15180002441402000e50150030a40001074005824900c071540e01400d80000700441c4c00b15101e801303130a40410100d240e00c10302c100140c40c40c0300d05ca03000034014015400180c0c050341c251050003a41005650030780c0d01c0c82d132001c1c2c01c40301d01c0d141118104016103100c1400052200460004c42d0910103025007191040213500010b51801030440e44d080020351280c200c030590503042c445540540030041c001103000700b0445c00045001c1c24800304002c02540031008207490030b05810021800641d10403229012240048000308a0888111410380c1901004400620b5925900c1c4408556900840000d01610712415160400f908000081d80940748502900d940164005405000105003000030901100040c0660499442d141d0310b0320281e070000114100850703042c0700e40c0740c0a0780c1c1c1071041c800400941260503c2e0340c10f001d0240368445901c640c8100422082000244a40da060800c0b602d20b0750 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 860326798 1250 860325548 860325581
    0x601032d06020d1d030a02070e15030609210307080619120308090c030a0215090109030206130e0c0301030816020102120d1406150a030c0905090412030c21020d 70
    0x2004010600c004001c0110300c801031403040613024800d664008140d03850380282d0f4006010440c00c04501c0300c040f00f001030035094015881c03501d03c41d06440602075103020b1284080104442c0c400b0484e56640080c62540000c0703c2803081c41084481035102600c190032401c10382e0001c0813040503410039002d50030243c2040c130306421000d83c49409c0650107403080c4c0c407940b0b210064802240030602010781754610124013030b51043d00314000f00035a0410030011300c0415030504211404a5603030707001c02d140350040e002c0504000c4000720104044020180240da03c2041d0041103881e540c1951380c4e0121502030381920705d00912403500c21030210b90080001d1980d141da00502c0b82d4445806400030b0000e80380c5c507a420b040080b044000704129003018244261072142048a0070304209941c4002c50003002494100000c200b0750000005903a00e07416107050045003c0d614a12104810a070050260354a0850880801c10070b012130307071801c59019403451601c03000e1100141e56561003051070800741c0b0000880d0400d54 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 860328048 1250 860326798 860326807
    0xb0a140310060e0604240b1b0a120f080103020a12050106090e0718180206032509081903050a0e03070305030a0905100311040b071b03051e0601032d0602 67
    0x201660078030400d0115014000780440d400c161000da200311481d60700ca03451240d828008004020003230541c0c2d09492818880e4007000c0c520051070b048002e1001c0d560b51060110720500298030800c000798200c02402c00d0700003545164049480c04441d480b8420010f902c1c149000200202034001600604e802e6106200c40149182456200c1070244500280c17020221722420382a4410b00510310004c43d44114110003131065024440319030710061040c0028598a10541d071b00c0703c0c0c0160392480310009540c8141c1c0c5982098252440c0c400c00c01d062407100e8850903208000a64050300310b550108183c60b140c0500600240030a14101c22908002c0042c00b021038a03401841e407050481003162001c070341000c0c94400c0d083e419070881e4820150004803171020082807000031001d200400480384104454041c4c070000b43e000e440030b10086d0300100e034160442d0043c003030103009508400d296003042c80060940c44d40b441c0d4801809504011035202885101c07400d801400c4c90083d0f030702038559040300c2c040d95503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 860329298 1250 860328048 860328059
    0x105070203040609080f0307030f0203250c0e190e0a0f050d0206012c04240504050d02010b0303091005040506040305030d051608071d0a03080705100b0a14031006 71
    0x582d0058011600012031690002404942c00116020503045d400051441c007245520304603116201068404194481003140c0d0705a8070210b0071f003102201c034041c0703c00d000000a15109840c5400d9070b100103411400703001448210f51881070300300d407840e00c480e00004081100c04803140c105080a10003905546d240c0e031484082c0400401c2c62100d444065090721120380c0c0701c000610844552184000c5100389108644026102c2d07032100940080c0223007181c00e005414035900080d00c04440703c3e04900305454400780300c1044010815050100742500007440002100c00200740e8074012250080e2048406188070b20300140200c08a4002c1c2001034510f40da11900c03414015a01c0e400380d1f40d9400d42a00d80000940c40c546c80034440c0301a03680e550f50b100c1c00c5480e1000c0403100c0000a1115030203104440080c03204556891544c1c2c0011f511401c1d1468a035002d42c1010343c103000302c03400a030510070308262030024a81d9403520704509480b0552403020b69096004080392501b02084810100c40b441e10802045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 860330548 1250 860329298 860329303
    0x50708240d032f070b0d0609051e010605030c090415080303090a1205040e192c0105011a0306060319050406050412020a030f0c020409120c0b150603040312090501050702 74
    0x40c900614082c01e15a44240044646541c3c000011000340d00f080d072050250301401d8005241801600c0c42c08036600d40c81c1c9160504440d0301355409240502a05001599020009507403801030545042150652404140c04a0103202c1d001d00c0d24403d544d6200105c07005200803040388054000c0c0000c0340d490307181060b000c43e030ba1403844100361115000c00400c0422144102c0c200c034142c4074101c1181240c4c3d01d50702d90042e5944503002203440b5080c0c036030365a60000709022200031481c0c20082001264111601d281c070342100c0301a0402e0010543d01c2c00700402c201054001c0304d4000d002075907040e0307482e46c44803100d1043c041c1d582d440c4008d550518061000340445600102d009501031014002c000c8000c050580c0c0c1e4107a0780e80010003042d4541c1c3c891a54501036081011081e00280012544440e255240c01c140301240703100c000030035100c060076401e010700d00d10565480075100344601d07410300d122800103a081c00000c2c001010000381c4034198121420a40103031a24540c810001c1c8410b0401c0d400194 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 860331798 1250 860330548 860330567
    0x22080301030f051c05090103020304033c03050c07030c051e06060906040b01120b0a0f0f1e0f03062c0c01022a06031b180a09050708240d03 61
    0x603203c1c070504d1450000c6422441c0205290f81450311041d150100703100040d006900010015414003981d1101000e44142c410b40c030750054441841400c0c03c0110b0481c2c44650448442016401c141c41d200410090420b07a600719000c2903017608000200c18124035140c0d24140d2448030b21716260250b9105e00300c036620001241c82c020303d0101c0c0c03002c800e0343c0c404042c00221514640c0c0d084c00142c4070074054400d900245c0c041100c0c4031001c0c140c66000b94a511403204040e44640c080c14034040346500030058840c9040142038802170a1030704880306450301070810b4212007a40400340403c1d90710021030f8000f56425540303649014083d400b640280107030709400f030b49920501409038054060226500308280741c51200c1c1c0580b550751080302481d00300450900c0180c0d000245443c032801c64a22044110301a8000601150b42040303602c4c0d03480390700d841c0030701c0f80c0740b031884d8007191040c1d042c10180050550480e00340c0d5403041c1e00d4001030403d1049100c6070711a1400840001c0c0d000303c0c9030010f08090540c419400b6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 860333048 1250 860331798 860331803
    0x11041805011d0402040e281b1508090102070c080319111009170c0d0215041101110721021f09150504090606090905091522080301030f 59
    0x20403450780d0350110308002c0c0411440944003540c11500003001440d00d58001424000c0700004c4400b0151040640e0500d4880c0da241001903944100070402000100328060440c401400c403800407562600014200200d0288124418440280001941c4d08801d6054a01c01504010340182071559400300648992041a0b9800100d00741151a00c0c6140103000c0800d902268030b004101c0400f00081c0903005040c8040c042700d10038210300002c0d0b01c03402210003600b0038500f00006043e0b4016031407400f07071a00c110740d4816950a98104104404210b10052801d0f8044083c200441c03582041c2e03d01500b40708146e00454aa000c4903400c3d0440c6080300090b03501c1e120701c00e0319001401e4049800580c0e0071180c07100041d0000b65082803e1003182c0c9083c04400076003540d0f0a00f2401c06031110b0301401a10308035000000000d4040078204240015401025044101d2a000e002045060300009290a40040c00310848242c0da1000c0030b58126900410002c0e541c012403003680742d58407480c02110140202c0e405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 860334298 1250 860333048 860333051
    0x40303030516030c0e04020a03020d060e160809071401020c130509010f111614070902030a0b040203060907050c030f0f04051f051c020d0f09021201140a0f110418 71
    0x5440b01d02138892103032400345039214041181c09000401000e0351120380d1403810141c00307000181c0300300c030240a070314040c125402180c5418138221360305106e10410028001d041007160000c0c04086031001c1000020340710805025010610f04a0050349003003040038a0300c1e00301d840c2c0c0228441080556102c54011880400240003040c220300800e01941c0203100c0507410301004000c860000c990608800c000c03284903440312260644820301c45401c043c03032580f01c5107640d600042003044040052042083d4118111011411407c01d10080f44036501c00410700303414008002186a82180304209036806040348883c1190303603240c1000401459003080c81342034050140500b0504420303003412036003c545078003503a0b07403414500040c030128000200c181d00b90340c541d030f130810410303040b07050340c1c083e44880b403000c41d8002c200319403203106000501c81d01404004140e450404d800e05640103204031143c00020b011404101c0c1c8103034005001c020303d110b03404d070401103000042c000381d00c0314034040495090116a10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 860335548 1250 860334298 860334331
    0x80405091603380f060d0b1516020907110a0c080c030d0537081509130f0206040e01030b100b090a06032a050711040902060a230403030305 61
    0x410440c40d8481161058540002c50f8035158428111900c924540e0030080015240f2030824000c103c4550110710748650b181d480c1c40c451000c50401d112554405491001814070b85005104800c0b9880d00011000780b01d8010b90740420141803048100c0d02074900c0d02803e4600145003843d048c4c7e000b2115124000b101d004860107140c0e80e142c042007031445400d280e101c492404210424807045c80e8501761081c240c104070749244040030342e1b2400f003a44c400c001c19200c44601b4241281002508980d011000f071041c2c800c102002441420b40080c40b0080f9400354018515040c1c502c000381d403070b0180740c02c0300c080c80d00f45400000c180021640480e001d84102d071009a16981c90706103d0381030b8800e8501403034010440010801c0b40300e00c642c1c01007032004a82e41d0032289025a00c2d00361000426076a840e040022404111700d01403000007242202d04c204100d5041101d42130980c0415401c0c010a405042482030b110840c50040d88041405040d550135050403990310758403031a0140c0100019203420303642c40100d04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 860336798 1250 860335548 860335571
    0x7020607240606110102030421090815180f100b0a0b181003050f1603020c01060f0503010c0504080d03020c12190e010c052d070308071a01180207080405091603 70
    0x10807203008d039401030070203284031006205d0400181d1080d0035410070800030034000a40358806224100009041107441c015604000c14079000c800c01c100041360658202c0303045c00100c150009400044250460340102c1c0030640340001442148980e400301c1600f1000140110483d1082801d403e406c0004440488407503891000c100e0440b0012103424001c403120001141054501c50200c2d100f0032001d2401601d8211070b0001c60b42565a0f80d4010017849101150501251030700f07018110889229140c8581443d15284031655540100c18240090540c000340d0002d1404040c8109103000c0845510140d54000c21440311011580c1207150000003000001c51007440d61044880e091700c01d030402d0091202e0220083c01190074001e40464585034003c1d5682c0640741e500a001d020000c0d409942c90360303102c018500700191907036610441c07440d04643c0a00184105c1547c500c620b01c40c0c0303044860040c2c4a600d00e1404030041e10641c1c0290794805071480402950b1040799030a008000125a0207200742d10344003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 860338048 1250 860336798 860336801
    0x10609021207091512020714070302031212060f01051b030a03051605190e0d081b0c0d0807020607080304060e0d021c1115040f11060f070206072406061101 68
    0x40c083d403110103094101d4403c0c0c00384214034248585c01c07414001440c15150381c0c1d0303941001210424011281d00456403c01c1940f81c1400503800c3c580b1107500540c03920b4040c42140b07800b03c0c0000c0c03601d441000c46903e4070000b41d1045098030404060310faa016100a08445c2c1c6540d250030104056000900740000a0807040c000b1091083c0c0070415114a420311a204000117007500c4110811802c03c04404015031160356256400310f0a035000c2c6e8980355946011000c08606808802108084d550100c020800c4603220701c2001c1e000a43c00029903500c5840504c0060090b02c00d0000c00707401c1034404020301081c048030341e008003ca041500c007111440025036005a031a110800c0001d045d4603050201044000d0280101c0541e501d003100503100b501c0b6440c0c0c44e10b4404001a41c0076503100714140c0c084030411078800111221910210350480c00c00c0c4041040b81c240748542e440081c020040440d988040100810b50820807039070b8500d000340d200140102800041c98075204040026099060001142d4810b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 860339298 1250 860338048 860338067
    0x106050f01090303080417040f03031403011d09031306120e061501110c03010609020a1b050607030c0e0d1217010e13290411010e0901090c0c05010609021207 69
    0x40e1240301c41075246480c161034540f0028400d403401f2940d004801001252800100007a2800300d0b00c180d0320a0460800170a5003000c040051069a002c1005005600c40d109200201ca45030b00031a4100c0e54440a205065014485d8800c00d11104107a0109150b6040580710b140030700361580821560403503085003655880142c408098072203c5481102046d44182c404280754a8444202e440c03000c519404203086070410b13846040003644c00708155404591004480340c01038510b1400e0804580203031240f40c0c4542c005000c0100340341e551542102114000c800d00c42d41098001c092400502250501d4000080c040c1010000245000703001050020003980e61410390307280d4051b14507a036031014240a044444024141e6000c680d080918200010800711903805410398208074220f42482d00c0c00e856500410600d20b4148804540c6000d2503032600740000741124070307c0341c7c08a80e05209500603100e1402003503010b01107508040d0003113551202600185400c4144440b80039144e0344130311017113480411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 860340548 1250 860339298 860339329
    0xf0509040302120a020a023f03120126070e011202040e011805010e2d03090907090509060103090506270708161707060302071703040b06010314150108090f060711010605 74
    0xd04050400100b119151424044230181084038030786402d1510410704514241d00c006440080b17030480381d40034850340c6000b915069100b401004142d04141110b154840140a98001500d5640d01c80040d9034990300103c84803484034008101d000130145a01c92410301c0180c080d2429802c107030030715000600000d111210b801508100540302e50340e0740403459034056820340080030341c8010f000d858401d586074801705002d90026100c403e13141d442c0c40d05020710000300800340c0317050616100c4010007040010500d80e0b0720030000341444c560800050821040b09070500d81545a5107c0d140d00803a02000004001036803070344000c980501550303108480b00700e415910280c0c100c15040703000c4c00c001c040d01075005420b0540c0b00d200b0441d0b4140b9400400d003080e4004890903a040b07058001402911b50f01407051501000c10301441c49110b14050541c147d034052400e24082c101702078030000079640341d4144102d41864035610140d8082e0b003005040100383d6203400170381c07038110b51030600005100d103040480409043c0c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 860341798 1250 860340548 860340619
    0x91a01020d0f0e06251b030b0a0906090501110903060612070e090c03101b03050709051e1314011e18091a0912040f0509040302120a020a02 61
    0x11a254040740d83c1c60025040c560000d0092184030115107090040c28286940b101514081015504084248605960b00d00400203070004061004c510f207801c1043d8404000640480e403010b461034000c0c01400307480d5010308503503c0c005d03c2ca403040c0c10190081906400c201d04480181c0c0301c150030050070f40b8500007881c200d5400345908200302c51180038050f070f00460041c01d541c0140f04040c0880c2c1404020800070342500d41d94590070b42640c4259131244078500d0b091038100118588804040d28100960290714403618140000032418110082d1400c0c4255014ac00c241c465009505000d02400c211660f007491411604000b04d804099480301103120b04544400540d03251510006040007600d860303400d1900c0d51100c01d83e9001c100e0b000301d030260800802a0034030103441e1000c0501d061503541030580e0600340c01080304100661040c0c000e60140c1e07500701c0e8110781c0ba0310707903203002d80c50010400300f04080c801001c50552482600800e41c1d004441c006c0c0c5d03543c540044009000c250000c0f808407200541c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 860343048 1250 860341798 860341817
    0x6100e06030705040b012c041b2f190b0903070b0a0923060906010f0303050f0a022104060f1106040f030e0406083a08040606050a091a01020d 62
    0x1480c05822038803401d03078107060100b506032004c18801c1d05043c510901c81c1f181ca028500d6520710b03040502c100d0141e581d51102a2016040400000701030120f20b0030701160100140000d5101d00c2c000440a9117001c101310f044401040c00c514207003408011811040d11003144507070002c0c1203000e011049900c020350000c20207002d46e0303804000340d0040c29042029071340c4201c1c0c041c078908009010350080c421401028010072032480d1040f40980351403416045242402c0780e42c42c0400001c0c1d04034081c1d074210810500c1c4a9107545c10448107e14180d1030400308000c00341c80c000c01c0b91941b1000f10007007007600d900342d8a50202c0e0014010a4a0054104a070f1b0311040d4418000640480c00e035040100340180329281c500704448103030000405032602a0407540098004d03040c90240035030003140400c0175140c2c800300d054815410480c080e88080d80d130040311051224000004c0c040202c140c2c80745010307000041083d29081e40301c0d410b88000340340011500708052202c1484640d650b00000c2c9a00b56120035a4900c03410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 860344298 1250 860343048 860343059
    0x3010e010e0c12070c0b01060201180201080c0c060123090103080d0e0703060c0210050114030d1101021c0501061214060409022209170301061b021f0206100e060307 72
    0xc050010700701c9102140a001420001c00b0010f500c6000c0d1100366244492880c940c140160040e50680c440e006581c5485103600100700d11280c04c0014540901f450a2603668042500f151480360105001d228022080086141c0440500361520303141003d0740c8655005922040c002c1542081c000545902d40601034801c1c1200b583d00403000407060881a1410240e8070369401042d203503069510000358101d262150b1088441c0d00c140f90041020781d004114149940d4007083d15101a0640401001589200e090401c40250100c0e11a40c26a5a4400b90300d4070300304c000c4000701407c2c0503541c0050101144115809018014008441d600c80003920503502c400c1c0800004043c80c030800c981000080c4500b41581c0405101d083d18900c000001207032186440c03038298186440070b0175a80c0096403e1006014090380591000c8144500340f1190300c801d80b1f6400050008804080303140c10304400504843c1e2000c0d80401c240b03014607420f00402c80500c3c0c0b519050209468112456600342c0e101d42c0b4101320 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 860345548 1250 860344298 860344319
    0xf0102040b1b03163e0402090d150603140f1b0d06050a150e090606090403050903030703170c09030a0f02040905060109020705060f071d0a170703050106060503010e01 73
    0x10804040401c90b8508103200354240d54000b880c0b40140d030584400541c8000e01c5206034100260f1900008084000038128070400d9117a80030000203078020f0f5404580c2c0541e540f14503102080154010040407070b96410590513501601c45400f088480310207595540d20070810025450700c2400040c8050850241c2c00f0700d01040308100d00880990100480031640086403142c030402d4065441c2000201d11f0104280105081102541c0a050042e00c1c081c100f02007403030045503064000000311070241d804d0721542021102400343d0b80c0401d030705d404006000002c26800c103090b650140c03600c038003410880c2d0313482d0030394044c500420280c0764040c1c01c448404030000701c400c501c003242d50740700410000d81d241da251140352506100f6000810880e1b4009441d00c10711104010066100d2000c8120a1541c40c000700018a070b01815440185402e03504c22228041e81d4920308070034060b0400c81501519142114a0580d840b0840d20065030b0035480d10034089071031481001101c2c165010010100807903468012043c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 860346798 1250 860345548 860345587
    0xe070609050d1709190e0606070206040909020a030614071409030d030f0221070806091308030601210b120105040c1203050717031503010e0d032307020f0f0102040b 72
    0xb03c101108100d0a0400c0e40c9582d9010041c400002160414904010300254540d0000d0700a500c0b030346c01401100d005a0366802240d0699492a601013214400c40c80030507510030316034000804440c10017800294203000806814860700030303a6111041c030081c1c003801070403912a000c0c1d11500340e04440c03400303645903010390807141c5100542400189000041c0355a515036176482d00d2451082c502030360920001c0e551000a09801c008100c440303605070700700340b00c0040b001481030100030300c0c401010002480d980c0c01811f405a0720340c41c0b142401d002c01a5034900c0c100078251001c2440c410b44003400c0c809074a60051084600c02d550090080c00b215051a811084a040ca0f0f2002c40400c941048808005006101c03035400480740d4491180d101e050101314018016500065540660315008480e01407545c0000c054007a007016080000b50303004200026030300840b00e0b003400c40380b01c503441307050ac2062079000503c07440c000c01030f60664a00050314050307103080c0d109610a902c28407005101c071000c644c09480080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 860348048 1250 860346798 860346833
    0x1050f0a0c0b040b041208010605091e1906030e0f10050c161209083c031914030f060906012a0c050402070c030f050102070c0305010e070609050d 64
    0x30760551859950760045503204403811980c114000d0184003c00100a00102c08000d050515021541c10aa001499070080c8046a4886c0c1a0101e41170084484c65130200100c01000e070101044080801e40f03001905414415480080c2c500000003501c0d0f8400b291502c500564040a07210500d001c40c0203c02804018084244002c4100410041b1198a19502ca122841a0b8030356039905051000070307284020649c002d0300c043d0884c2d0008940340342440250300391100c400024003203209014010036082d40140542840600c07000031032040c007000d52011000308150a5440c04550121940a20b080703000641d4400c4844003002e0200e4428900700d6409030313215006144c121207041d140d801009405040c2064010322005041d07140040c040b0300c03000700024040c290b074250315120441da0342402401b4288406001c1280840070f80080110a4040700e846681142c210955a9102c1c00c041cae00901906070107403003c1c0300da803400141c054000e5824404841c00104048e0107d0380780c0d00c500b00a1074005405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 860349298 1250 860348048 860348057
    0xb030a050907080f010621080a1d04060b041401050c0a0b0912030403030903080708010f090209030f010213091b050906070303060e090705090a060b07030f02012910080601050f0a 78
    0x820030031000c101380344d0392982d4400049080c614110828642d52080810321040c040c9052008020031050811613004c6516840c080c02c82240901c4a0101d00081144980d401800d000d030009038118810003070420303a62180d014a40c5140644010354052007a4450070805800403402e80020074010308425900c05882000d6603048256034211500f2688220b4045010a40e681400700925a0204100d540000c990424007070341c1d4105030000041c1c041a104445c81030350002000111382d2002d205c005104c800100c025525040e42e9065a40102a40d00408000c83d00e031429195940900d5040b07040448520785509141c00e0b032260034008158402c81050b81803544035900000c0100003c0c59140c490480000500540ca041004000030404090321504203d4184641840843c3c001400c0b00c00c3d01e81d15003001c0780f854a5250099014146c41e011854810003180032814140d40201c0341d031615903004035030014445606000945a1503815103c090015205014074002062261300801c02011035080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 860350548 1250 860349298 860349313
    0x100c03020c090c0414181b28111204030b0c0909040b0106030f06140904020a17031e0c0c04052a0901020c0a0b0a0f050912071e0b030a0509 61
    0x102e808404240e400c103120f0200090204105504034001c80c03100b207001ca541c0300a0640504085080e200064450b03450903480520300d00511a0103001c540a034a80d17101c040c40d81c40550021500c01448510b801008035900d00c101d030703031100c002041c0d5100d13081144a101d810241580c0b9102c2e0303080c8005000002c01b160411076881955944061540b140c1d01c5407680020b01c0d818148000c0950320700c0070210840c103040c50740510207001c1c02200c240c42250103446c2201a07503110700004681d4411544441c100d403104d04506000030701d0200043c00340c50052910600080b80c2040c1c40741c024800c1c540d040d460f40e005a04600c0d0742c0e2038560030042e0001410f8a4545090118402c1031280026610080004c00000220000d0740d50301804002e1000504598008515250001004103803040c244440100300230a104011210300030740c291030490703101a00340740401143d042201e0f614040d41c041d8101102c000c0350b003040b500403858440d00507150401c6185085440d56004500541000b40c55045207008002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 860351798 1250 860350548 860350573
    0x12030c03070926010b012d170103030903051c020606041a22140412030f061d0402010909020307021009021212040e0105010206040f0f020109031506060305010503010b100c0302 77
    0x100c0d51007201058600c001110021000783c03508445000c0c80c0a1b050000ca28140340d14816802291032844049455042d841c1c0510310085500301d00940c144071100b0411000441850380c8401d074030054921075821220344050751440b010112034007440d2080141d20980010351642800d80114002d0a0b024000f18041c682c0c00d40001c4000013110101c40040d0035060b4038005012042c0101034090400b407500c81c405017840c2d125075039000e03251011101415100d200c40d420081140d4000d00c003e00c011250071001c018010240d641980701600d06a0004044141c0400c041384d0902c2241c1c05252150010013004403000c0414001d02200d0f50180d83c400f00100d01d141c42c2a400788800c40070065000f01c00b540c1e0741d0602e50700b6080c55006810050441d4000c0040100007002891001c040c56000f1020140301c40d000c5c40120340600c1c40303800081500c5c0c4142c500c65034422040d0070030b0090711007070b4030706010a07a2180185400c0383c0301c00c000c1903031119881d141441071501483c05031049a0192041e1400340c503408 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 860353048 1250 860351798 860351819
    0x30c060a0203090126011a07050703080903010c03050f06010c05070b0406030209120703020f0405061309051b24070317040c03020a0501030b0f040b010908150702060912030c030709 79
    0x1500c400016810008081d050b0350303404030201d0190000e2164950170354200185141501105000d4404640f0031291540110f40000042c1c0d20043d5220781140c10564803071804c000c943d00501000c7d8003030360078204c000710440d002c0e0003042d1044100042c640655034621004681d00c44210350300340c6460041c500c002c205030040d4002000948a90b48000d644d990301d072010300c060111605000c0219801401c07060005030b95080480d42041d104680c00b040a4a0311000604c3e9458810f203400035251510303244c0f408201000c10380007030840c40c0096910342c0346050414000c582c0781d0680014851201840c0d800c502c0700307501001c1c080d00e0b4000c0c40c260a160620100c0e6490400007600e064510000140c2e0400031803511135481009080c3c03c0c6000c1c0108a400008100c0701d07014005a2842141c9600da0640f090340b00c1c00c250001410004100c903d415081c801c100030b1010142c820350010f006503000120000d40001e0741840c04480920014038554a07540d809030b00c0d07000540b6250401044400009015240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 860354298 1250 860353048 860353057
    0x31a03011d0609060405030a0c11040504030215100e041b030b19050a0c0203030a09060e0d0302210412050706181b060e0d02010c020f0418151103070e030c06 69
    0x20341e00244801c8140c000c055242007401084001560701c5401080006030000c4190385000340c980c217160406001c60720f0440210000784150b00e822514140070081450343c009910035400030000d41c142071581700d44100d1110000c46008030540442580302007400951440b900c0c2c183c001d010f14aa2001c1171b12503640f0049c00c04240c13a00e81c59001020b18810765040d0600c02d054002c01000c000304004102010040d45902005020340e507500d0341e030350000050020540102c41801d8084064941030402c854000e0000c4d0400a10002d0305101411850406042c40e10140e0003190014101101404003560488103607000850441da40d40e281d000781000b001c101070450a1992090140310b11810341109001150400c1f0340c89001040901140c000c581d86510f41000340c440c0e0286810a109156800410b0a11405a030070580061400d081c00c2d407022000401210590b1082c0000440c08428108400a4820860070000c0c460800c0011030300150051000c5a00716001509990b80f081344207000401a410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 860355548 1250 860354298 860354321
    0x50904060b03043f12140c070302010f0b030309060f0d020f0c0f0c01080610030e1b01140301260a060f0b0a0503070e0a0b0d12022a0f01031a0301 64
    0x120410400c2c12034854200300d43c003e0015210296065901803610110a044c1000e00450030745807503800701d89802c481007203210340d0f140c0c0140381041603104626a1002c481a0b006520b004071540400d100f6000c0c0e49441d01000b0025420714640340204aa282e12036080480c44500c200304030380d0901190300140c8140c02034000c41d60b8881c0000c652040c1803110700c1c00ba0090a400403815482140e0700301407900d400100544207a400c440704004203800a00c3c81c0c014041043c0315520041c03c0c000880414060906002e80e1002c00d144101e6403001c4e1140800c1c0510703441c5180c00428041c1d00d84030a030110070b444412030110b0b688404243c489604030b401c0c00c03480310000c9407118880c450b64140103c0c88001050250003d14007c0e252050101b20110058410030034607440c1d026550082c1d4504800c0050700384c01c071100022080d00340b4000303540d940c807800c0b6044203401c9485110410780c41200c0740704c1803058040c02c4c0307140c80610107004400418800101c4410211101580d00090314240700300320741e040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 860356798 1250 860355548 860355563
    0x603420e03120103030e0f1f03021b150109150e0c180405040c0e090d02030f0d060e070c12030605031c0207120b2202011205040507051203120705040b0406050904060b0304 75
    0x21001810300205503007d510700c50081c248142c20800c2c1505080d541c6032646818a001070301c5600c40d01d03546071540284200000d040c0300314070b40580c581c0c16040c1d03220b041314903220040055a503400c103080d0310305005100b2154180c10100c005214016903e00078860003a48140d0010b161842d040054110b40c0d0035502903c901190300424000445506111500101444000c08021a0f900c000951328880c0f40804421000040b65070842d80300140c202002030240703030b40c0d0390070b0f50f24040600801c00603802509803500210701c02c11500c00b9001c1e120340c1c0203031003006d80648042e55910511342560341140422904500c15034800103030310800350301040c0c1d1841c03180604070014240105d903104000c032620740c2d4500c43c2041307141403401070fa00003062211440c004440400e0665441c10250700b0007405500050300706009005101c103841e004802408101324040a1031541d03250490100c90750301850140c21421320040006001c924021000b030b0007281070003132000c00c803541c607144510410b800641e030469008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 860358048 1250 860356798 860356817
    0x50d1b02010e0102251e0503190c080409050910061508010905060109210f2108070f05160204180308070c0213090501020d0603420e0312010303 63
    0x469080c040d02c040250400001e50a084007400801c84c2080011342590340440340c51509020170008255580c1600d0344010340b10091a92814241c0e00c0707600400030918500600101074011b2406400c040341c0e040d81080c045814541031441c140000c00001e00300c00784a2040b00744d1410b56464902600c006801c038801f02481040c4100d0016101c5507040e0400340c003550a213030030030403a660300c980510102c585008022095400584c46501c00b031084120140482c894400998184080b60410f4014001c100c50b505660300300740306085415101c103603109400900d00b000c216120911507070191040c07850340c48840190990a500007012240008480e81c052400c901501e022b044c0c0298055601c40c0b1107080090071802182d0000d0301c1c00030426441c10680c1c0d0745200190070701c14258140e03094605007001c1080345540768200700c161918910300c440f0480c9024590510400c401c0d40ca404130001c008800c468400e102c41c007507a8040d08003060b442209100030b1110001300481a510756000b14000d0301c0c0c10310711 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 860359298 1250 860358048 860358101
    0x9090510050405040f062a030204080c1c0b5506170d0315120f060b040218040b011815020c0603070908190203030901030b011101091a0f090601120201050d 68
    0x2440764081207d01450710601041040b20408609601c40700070444407103041d50f003d000104d2001c0c80310900039003842e5180040001012003c02031346104510100120b04661410080284036803030500004000c0c20641c41007001c54015045903102c0d2240050085805529154070303800e04d040640842005a0000c0d5000b030315550140b280c401600d9005081c100481d0500d5020b401c40c88028000801031100c2802c22801c0c400d4681c041410405c006005565640348105490302c91881590281d10031803a0001c034803920360003801e5804c0c4040c18050340d00d070900d241400c1d02108030b00d100f840000354024503034411030541d5407100843c464406ca85030300c1400b50802c0081d0b03181c4807501c160060081036039544000543c2d000010344640d40d43c24680490920003401c0121144000407842582d290700f040455401c200344025100088100480712580700d5440840e202a107650580e40340000b40c22080043c04080d00e141f9030702003840d0048c10058070b0a840c00c1440790031282510320368002e071518000070510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 860360548 1250 860359298 860359361
    0xc0915091e03060711190317101406030c0903010c02030409050c13140a03060e010902030c04022a01090f1a061008010b0d0e01020d020a09090510050405040f06 70
    0x1821608902007000001801c00403d0341e4007000307001d06040c8400c815580d00c40704130412101c500c0600d040207803240f0100915001d499512070000e0711000030080c0d17001032035030440380011030201c4488024128507a2901018406903078005440c803d00c20804000441c4141c800f40203020300d250403030b4000d41e82e403403500c3d4400d41180c0c0f01920308041c528003000010200384030380c1c4100090329806d900480c641c1080c1d00c0092041031440d0720041c0000e080010900c41a48198028492280290280e920751580c9400300300072032052a4296016440400941120803111401040740c2d0414500001e000c00040d143c00c0b003448c02d0f4546c102e4000483c595034800f00a1034100490308000250380080c40f240600718040c2c61039905000311000203d010590120b59500c0b50004850308010000855442d0018089600a91b221110f1075000c100d0000740010451414071400344a8508400c0061078282044100700107001d000d041a14890110200000810303003501c41c0030200200e80400401700301c954500401c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 860361798 1250 860360548 860360569
    0x8040b041703180f04090209091e0102070f030804020a0e04110a0e040f02040519020408010b1009180b0126040201031a0102071205030403080a03060f2102090c091509 73
    0x220780d41c1060041c50403464010300003c5100c001100c07040c00c0d0100d0703a4041402803025a4010b940f007803502003800b481c6030022450490052090000f041a200303a8007145090744a02c00c401803041e480c2c803900501203071280040c1e94100d440284407203c2e03507581d036504c0801840c060b43c098500e0601c0b80d907000568680b18500704001c000b584100042c91604c2c2e00d079025030030140e40e00640150f882e50005480303000c1e041c0d4102001c030103c140c11034459444503583c90080030f801d2003c9014141d020300c0d070344025028101540440f1071311104040c0c410043c1040b940680340c3c0506260510250144100704800308044404010b00210071541a41c50140001030036034a6000c01101106e8000040c1103035646c0c0840c2c52010384100c032100e110b03018000d01c2d05528511595201030400a8042840f00415626030056411104554221850340303484591002c0038050001c180c044c444034124042005041c41b400b05a80f0440384120300f818080141c021440d074043d9403000b0755040c0000100200985080c19209 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 860363048 1250 860361798 860361839
    0x106120317010e04112e17010b070b0103030e1c030503070201050106051e070f0503070f0b01081519060906080304030c151b060b030d050d0f0515010e030a08040b04 72
    0x400c5040c81c0e12582c0c46002c502d003a440c040e00b044184840c0755500c1c158540c90403403490106c0720042c802910014403880c1110780030303240300300403000019001111000355298941c0007482180d45034038598040d1540c1d4907505096400880d20701d06c24181124070101c0c2c40ca032a02a8881c0c50752807500200003421107805810190500c5024030611b03c121403e9480b0040070541341c8030065070340c40681400344541800c420002d02070b00c0001a002c04010b0f13403115036404184a250a451113903250035800d80c8070b03501003280c3d03402d40c110341000425074003048a10002120151200140c9580c40b42940c0b001d4a641d500310740f046610000381042006030382c42c103a0b4020505000b075038034406d078140401014080505c1c45c04000c011218588000e10180340d122803098a0001e0848001c00702c0c01002902a0300100000d0301201e14040d40608420814060207100700f04007504e0740d01c684409001915655261400d90340c0600c100d5091000159540c8000c0002d000b0940445840383d140ca0004c80321120305500c007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 860364298 1250 860363048 860363069
    0x7020726010506092202061201080a14030c15071101050114190b07060b06040b040602011a0915060a0c17030412110604060519091401061a040b030702010612031701 72
    0x4101948040b80301e0542007428603c24030304d002c2d17101e00000301140150807510f840b059547e800020003420010707183c071040d84100e44040401317820018443d1640a90303011099a03401242c0211101800e440c0b941303a01804500b029442d0303e00c0d0965a60866109030044800c5000051304099185420328106000780c0c080c0402030212070a20016070170500500360b000301007544030810824a6075600c401e4501504103000000d840340c2e511040240a40744031181d130b8036060901c5000b03107001c2c105072088620400301515034500140b9030034244003a40e80b044901004001864003d01d0014483d606030855442506000607228100781c2402158103110050000c01d00401c08440c2c155404041140d0340d010350040b500141c582c0c0c404124111210071803448c05509850144902c003004004000c16415a00c1500204103c43e06e60782c0d04100d421030400f840e400200244400c1044400d9030740207662008151001007401d5582e081c116070b9203002e01400b10085214000c580e800304468444807401007400900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 860365548 1250 860364298 860364301
    0x91d040215090d060c111c0f050405060912030d020c0a0b010503030418110d05160305180a0f0507050a060f11070513021b070609050a14090f0702072601050609 70
    0x5003d000e09000000c060341d031108100c090813400788a00810f0703082244160b03a42c800d50b088a40130040034050002010809003c144008184501c4c280c40a45801400e4980f0303103c0703540104004030f501c055030342e8030700c1c8020401c080c0381070709d540080c04e4900503100007030920307a00c0c51a14a40f2024140c1020b80241d006100401010303209488051110520001c000380b070600105914855204142740e02035220b00b400288903c0918803200441c0640481e0340c20001902d43d44060310129145000b81074030380d4010682500072540c17000100540500ca001260f400c03d9550000c250181180d51200001c1030842c404210741603040034500d0030080b41c41d8090b007506800e050010b00c001d035003200c0180105a02043d140e00301c081c041c01601c03402e28140102c99169544c1c05008050325240c0c003559000b04c612100c006480594100000c041d00c20090000c800b503654400e070902c50000041c040e4086100700000000c42840d00c0000080342c80789014100008011140e0f81c83c03c2d184064a5503020340003560 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 860366798 1250 860365548 860365567
    0xc0708071502060f0c070b01150f030902150f12040c0513060f060c26030105100203090a0302012307030e180702120f0d0218030d14030109050403091d040215 69
    0x2400c0d503031082640c1c1c503640d0b44d0346500c03031011510702802100415011401c0c001049075854102d8100070b43e2855512816200c5481e0800c8060301c11000d0000e4210700040313555180c800600c405000002100200c184c2040140040c070030f5080815581990400070701c820a001ea81013031482c840c2c14410780042400702d98034260003240c1e800d5081c42210104005c8003030036800c0000c100c80c4020a01c0c8080c03582017052030b4002d40080507500a2140c140b0421046041545007070011090720042d441c005d0200ca50b0a1a58005644070308110000f20030440040e00c0000380c0940010161403400d009030355403100c01302c42c54140074038119aa02810040c84403507017003054113540000c500c100c50119850007038550050000c45034050180d20400c1a01d14008980c098035104802c41209180030104c0c210f070001ca8504d2000d40d104658207000d00b08060f0108014080d088440d0081d0341c0041c420700e803030840c03e030303903084040d0000030300100c680190449402444254a003a00c1c890311920f1002c501d0500e003107482c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 860368048 1250 860366798 860366803
    0xb0105030c070b0c1c0501061b0309050918030c030d050c070b0a0f1d03030402040f06060c030f12231803070212210a030e0a030905040e01090204020c0708071502 71
    0x90200a140322086800144000c0340a0b00fa103980f50005d5061030915142d00c1030307040241009004120000700c10136804600c4908030703110f5214250f05900c54003038480c1000180b10740082d0040c01c480520342040c103030300c08803c1c04100a014408011000d99141c0108142840650b180035100100001060000b98041000690300b141c01040344000081d42d0014121124003400b0041e80c00420b41100030b002001c0d031140030004612442c401c030f50400400c6030b14004042121014001c207000a201e085400001038000c1c503011101d0b00603400c108841400313811042e4127545038001011819555042041c0035469880b45541d000078034050480f0200c0c283c6100e2543d24040c025001e48110b010362603024030f141061100002081303100e209813250398141c8901000d554400e44021340003a00c0c008201181c480003040300042940d040d600c3c0c5140c14942000c010240410900c0f034207841d5660042600140d0b640d2000b000340c00030080c09081107501d0303c15141d05102199100c01d01902c0d1412a426a06602 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 860369298 1250 860368048 860368057
    0x403180b07150f1401120b0610022805030f07030314070e0d0c08070e090607030509030301050111030c0f0f070f030b0f070c12180503030a0807050d0207020607060f0b0105030c 77
    0x181e00340065183c1012028102508803103070b4400560035520700214152012881c0c1a418030b01031080000503031544410301084082c260143c5005802842605909071607007880e507035055010300c1e04504840308a440c2c943c00d6600400104c210304000045000070184c140c0100f03049c2d0706840315880072900d0080d00292405c0b00380140d1912a00c400c0106c42e003040080002c030030141412a046445a948540c00301030380b010242d0f2098920f10541000407103042c402d0242d14480c808100c043c42c11a481d010055416241c10f5042492902080c00041c40401041225001001800e8020314207080c0c041442401c190403904030301c05c03003c2901c5007440030420a88045420125907840084e00d0707500c214084840e2071905a0092400c00e41700030040c0850313032180f1003a0b05414107100c21506c00e0303611000c2680d28495a04e2590101e1a21800201e035140034101501807401120005440c00701c1580c0054500c1d070018a040b588640c2e0f404060034040e000344940741e5a0035003130078001c2c0b950070041c0908400740103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 860370548 1250 860369298 860369333
    0xf0a051b0309100204090204030303110a12020a090e100312021204030f0c03021c061505011d15040e01180c0203180109051c0b060402210408120403180b07 68
    0x300080071034074101c01049100542c03140600210340f1140c559555401a5101d44002c2e00040c0c01c1a0002c02c04490380c00446186859545400f00d240988142c0c0b040a0342100f48410103108032900000346512819400c00d2040f44003841404c4040d09602d020814100382e07215400865001d21801010a02c66104860549810a148040c903072140d01e0081d070605503070742000b50400c0303801140440088507200c0d904002849200d0501c15405039080f80d8982c4030032885624002491144211481828241115800b00c80035244401020031020301c45400d40c81940060445903050004000b40030080001481250003e60300348010300c2c0706070b8000e40d01c3c02410043e210f001d04aa010300b80c980e006840c140001c1001034200900b882c0820740c0d4207220500c41000b900e594041c040082d0851400341308440c0240303800d02481c01c84142c001682c406001c0d00070700850713180900b04000418003140e1201903108901c60b40c0d60405020003180c112071120002d034003890704c01e03106000f271100180c81c0d00010130500d070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 860371798 1250 860370548 860370601
    0x6090c100c060207050d08180c06030a020309161e05090108070302090702011b030212100e1305190c051c0b010312020a0609060506030d0c15020c0a06140f0a05 70
    0x40302d0a01200034071510328002c016105500045440503001685984603000107540312500058595032541c0300c4090942041e4801d40400010310701182d2540a142c0100d0200100e070074105c919110b200c0034410941025880803c600081031007140c40c4600746000d054241c80e20034140d4541910555180c1e50740c08001c0c412504c0500241c00e66100b50300200a03401d10719a0074000300540140500203503c07210003141205429400260880c008640e2042211001b0f040c44005a81c1d03034000040c421410349085646019841c4c1040445000890040308180038042080c0c0440c030f01002c011514030808440725501c0198440f1030042001506043d045a0b040420150601c0f10038208a00385060810010000303890004140241b00d50b81d84058401d0a05404031042c031302d620001900c080c1c4150f103004080f10311721100340f00010000e40151440f00c9216084600082c4150344400c00e4459030040e9100704003491081000c0f652180c006a40c00c2a0f580c00c1c10007641c10083e0140d121501484408020300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 860373048 1250 860371798 860371817
    0x40e0a0902011101050f16080f0718030c0f080f0a050a330c030e0f120d06050a0902070521162108012d1e03080c0c0306090c10 56
    0x59003d05a20140003040d070008104900c0c001c2080342490400303869a0f10410300160032a4a0a070041c0c40050140443c07010000c0c40350303070f034100881e191941810018881e402e500300000010341d0180c2a4009001768218a0003044d0400d45200c2c5810301e000c0f86a10203511001207080415800b151100216420138418140d948c4100e500002d41c602c1840040c4072010740004c08501c0c045103511013030102281c3e0b9024031003148425003d45d03a4150301c0c03074040940d4202e1103c0314030030554180201101c907100705022606517550300000d150103805034400540385400040d00c0d01088010b0001d10102c041c0400e00c2c62010f030781040b801c034080c02442860001000c0910703104042c0300c0c0401401c4141c0082c4030308c0540c5610806002070400c3e400307200d400e901c140c0d080380624180d180703113030301c004c10840c8860b40d144068a4222141c082070035080c1081c00514986101001040c004802045402c2c0c01d0340080c0303801c1050030181481d00b88000c1040b6000d4204002d0f0020380d035582a00044c800c0c0c00c500c1c2c600c821b03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 860374298 1250 860373048 860373053
    0x19090b0a0b190305060f1501091814040305040614040f0302090702210a020f0a081c0f090609050c040b0604051509060c060601020601060908060c22090f060b040e0a09 73
    0xca59000c030b040c044100d1040c000401c1020001c0c100b481414860302030781c110389410130304072101500da403411804122011003d020f85000d40c00c4070b0f0602c1031405804a04038810b44031950038031009032003d9000903070024042c4600d41e008403402d40400070010b500d031700c0e061071315604c10341d900c0d610b0200078072a01c0e1590124840a1080100c2e981c01050882301d00002c1e45100700126450b4485200540540160102c0c0d08042c180821101606030700250064500707012450503c2549550500d005542541c030000020a20103500c11010400d100d04000103000c803044c103090307140c04290302203d40324505102110008c2e0b224007056604440d030544a41c07540d50341402c18034030140600d40700300e41c000c0b038080780080c003848002888a0044000b0380941e68146d032545811201e21000e4060301e0342c1c5510080205105001d00001032000304c0c2961480821109601601c8030413040c41d50041c0b041ca5100c41030001454564030611000309081000b8501d09440e0280c070420146d001040842c06542d140d005005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 860375548 1250 860374298 860374309
    0x1050f0609131d0106052b020114030703330303050c191524030f03120c0f03061502071415030106050403030e0904200111030406050319090b0a0b 64
    0x2d640200c5034041c407090a1101d20302d1010030001c1c040142541c00d0580000322810520b0614940c2c020000500000c0c21419803052060024204101d0402c00512408500158150003460090441d03a40110311345040d0380d2152103d0307a030345100c04a400001c00b01c1160043c11096002c00300ca5260800680b940050f9100c0c5007081d540c40056103442840c07801c524100540c0b04041c20001c03210850401c040d8840d401c81d40070140715101c10342c0340029400004c0c00810708a80d150265070348030b0b1420a58a409121290043d01c40207030030b280c0420f00c041c40d040d4003030342c05020b08000b41c45a14550a1100c1c400c000c001d644060601c940040c11411039084d20740c1c2c1e21106181347c50508500d010b2076882d41e48000c014515440340c4801c0d1300051074218000e802d40340c10400f150142d9040f070003400c0d01140780100307852034200513101241032160481e0501110401031001d0f00091480d902c6244c2c0300c0c501500e0a010002655103030908075454a0401e10004620380002c90b001011180b00280c0d07220700001080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 860376798 1250 860375548 860375569
    0xd0c0e09070c1e03030b1315030b060a090c080603010c02120f0f040306110301090c080c0307052226030712051303020613061805060912012a09080601050f0609 70
    0x3a0307030f01d0058121424107030141c01400a294064419208962054807a641203807004402d1051072261000d0410101c1c00800d03802d0741017007006041d1041280c0c0c89402c64111513244034135201180314170301040303038034a0207101c1d01c07003180c4c3c003400034003000420030a00c5929403042d440a0070b1107900109403a400c1a0074502554041c40d4020030801210842600310300e5650800d101d10343c0c0c080c0c00c040485900c42e03ca01078490045001c0b030300d240d0460702c4801098582e6002a05494000c2c0040c1100c210038040d0845180700501100a0b41c012010714020041e00e030036402130103400c0c03d42c01080000001541000f020005070020b103400c079101d880d1a1502c4100088580c80039501203800701e10403c50380300052800003294196180d4401e40c40301c0d661303100700d403240c0b521800340c2c40031052003004000d0600b400501e44007041007000180c84500c041c442920345030300004014504503507450950072240c1110f95000a400f017140100015071418000481e890301e04408a4050100420405c0c0f03992942244034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 860378048 1250 860376798 860376833
    0x190c0c0507080303011a0c07152105090c0618121c0f0801060c030c11040207060204081b01090f0501120f02030a150f030c09090f02060f0d0c0e09070c 66
    0x449810790348610003943c1c0d42080c05081b420800703410283c0031200d056005c9812007004031028001152604003202c16090010200e078042c40300711200e04001c2518a17080100e802c11040f80020130b41440310700c9605c1c0010340d002c92402840c0c01c104003102c0c210a0581c04480002c01c8421400c1e00c04100811801c0610281c901086210101120f02469403c117500c0d043c11491a40c1d115241da036a49411a84c807980d0050103004104030006000124040c10204410f18034090805450400c06556032800c03a401039000002941000318401841d5284503d451101130023482c02c402264203000d00e01c101c41741c0d507108a038140f11600e1000e2b41c0d205c809400465072254941c80454803450445026000361884140544120b00c410b080070038a059040d611900346c9030002e001c9002c46040c00c0da50b20081c1400c1a003038400c070000c03d1072600180e40d000003c060720310301c04051540710300b04141c208003601c01e2200501c040c001c84280c001c20383c0e105c48030029400807040c07500c40001405410300060350b102c9030540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 860379298 1250 860378048 860378053
    0x5060910030e1c020c090f0a150803040b120703060f15200d020d0f0905090603030f030c070c05030712030302070212070b04060206090c0a050d1707060f0e0105190c0c05 74
    0x140e2001d183d41c50000075402d0168007a10b04281c4d504040110301d41c42120460540c10440c004615000b119600080320040c0d0b4032031100342152a0f0b0031803413440d0440c1e4803140010100040d02c20710100f4005200381c220180781001d20145091200307041c5901c015000d40744110a21101d039903000751043d03000311000302d0011015120021864100344d00d07071640754080c00140c8986040544201e1007101a0f940c55507295940070710103070411080040b000d0018000660506c028020226100a18401940100cbc0a0b440d86551803000307103080c0b4103e0100b40d006c4c44c03007900030b4101040f00101c3e403105040445c2d858540180d880500744001011190a15000c40071071044000115440030080001c0040c0d8540703408841c00d5a4800c0400d944d1441e000d480d0381e4219005020400240c145102c000503102d10600c181d400035900008548095080700c00301360352403500c1d450b4100f407040003840341c1d4030804d800303c00900103440e141844060300450042045915917880b00f920b110b080c4107860311040070764401c00707 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 860380548 1250 860379298 860379313
    0x182505150409110406030e06040201050a0c0c0b04060f0909020a0c020d031209030207140303070c0b0a11190312021602061813050a1d06040201120b0303190306060905060910030e 78
    0x9940e070300f42d08140150400701c1d10340600402044c0c4005010341c400d9030305940c0d00d4508141a107046031000d501d92003c0720743c00d0380c071800851032050240250020b0a07042d901d8515442103103100034081c0c4040da100d61401d920401412140f140d00c0034a60a405805892001a80c07a840c5411250309102d0441003164900e0084243c0401d0760100d0707500c003103034282c207101c80350034450300c04043e240e105203003000704651140e80c070800c030344a81c03403018007100300c105e090080f08030350b6845400b0704283d41819807031509900c00040804250300482e00040760f43e4041411414800161004c90018000341c00c00703072042d000814a0740201d184014003801246000d031203a0241491011b042c00900f41c240d561044603170600c03035019000071891003110710250b00c4d1002001640c0f143d800541700c10340e19a0708040340c5903da2044042944040000304030610360552400200b0341400d00003003c55041c1c3d00900c08004442c3d0007041175035240010b80701010030031280c2040c01000818260010b02040b0246050707402000d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 860381798 1250 860380548 860380571
    0x60c0509130f0f02180d02040207021309030909020304080a300209180405030a030f1b11010507030b0f011b120512060f01080c030709030b182505150409 67
    0x2003040e064850200d50600c01500c5088070481a0b0041c918602011120b5031704603c100c0c503204451910413070014000519040803500428084401009600b81c401e807600009020150322895090080268400c11030a40c00c0a980d0501e0f10711034001c02101f0031580c1d140b21818500c02005051198561284030010400c50134000c20107500601e004901c10700c10021501d180309015040184100d50101c051442d02c00c0420b0194000d0607001c442c10743c40b66490403c00b0000900100c003041d40d440c90780359201c0c3ca040001c003480c223645000301500109400c2000ea43c1039911188011420541c003400e0081c400d11003050b5020341540c00480240503014035603001d043e25074014004040c1d040f00507100b03100c10346d10341b82801445003910300f03c1400240840d0010700c40204250182d41c00c42018508116919030300e403130b0017210030001e0302c0c1091002c005907514a0a03072010060501c0c032014201404000c0858240b8400c001c46032480343c0740c0101c8405800071500000c0c40201c40240c50284010040010f501 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 860383048 1250 860381798 860381801
    0x315041a0d05103603170a0f090b0108010c110c0607030212040f051e06120405240702070e150409052b0806010503060a23030307050a031e0903060c050913 68
    0x6440d00039500d448a03020703810703130701e81c40004401030709030f1a000c0c41c4100010700c000d104000108030360b9103503984801d00c10740c0c2c0300a0700450300400d00035500f010107941000e072258211180011154140030500007200703043c0034042102c440000049518545503a41c6007070690501a21008000010030005004580407003c070b40b00b0010344805a400c06030400b1a0311040b5040b0701d6189903e90f110800b4012140076901c4000503d234070611400c1914440d400d0b0615001c0c04601d0140012020621101003002e03681d4100303c42002000e9086802c6001e04150ba100c03694060107030380260141d070b107808054003030103030401c24001c0e2581203800f5841406004ea601070680034141e15110009041d02c80030810a6204805503401903000600300d4004520b000324080c6500084409642d1a1401c68090380345581c09101901002d800750001e00603003042c0c5c1c81c0c010401c0100504440d19070001c201ca03c81c5c103030761194580301640c0d400100003402206072001680c460041383d03c00d039400903130001c000306150803d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 860384298 1250 860383048 860383091
    0x509010309020d26250c030501050702210412020f0d0515060301110306010206060409021f0309060c02120307050a1b0f1124031b0f0315041a0d0510 65
    0x2401415000d8000d5840707030515101e009a81c641c3c1c528000d003201d14689410840c26640380c03042c0e81d050201c0e80c1d80c2d56104c9c01c0d540226002c0340560002c102240c90312245401c0c80008641901c0090318050500141030801400c40ca0302030300401800040c0f1603070fa1164010300d203c0540220031511000c896401a108640003103d0180c00381d428034040500107207090081c0d9005400503005003045542d000c080c400100070050003640d01c407182c09030900c42900400021070181685507000f00300200032341000c50940742e40b80c400b50215402603010108000101064070f03004000e40c940039035075110300c0c201110b0800b00c17520240381c0549a10300e440100801e4a44558240c0d208403000b1007814404403c0041a44044029403036000c1452150b40400310a5001580d1000c44900241c54404018070952a03a400c00900003009030300000a014820500c031589681750b51382103509010b55041900b030309940d000c46184440c000c21201c030703160040020500c040c51aa0442680c1089500324505214150214 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 860385548 1250 860384298 860384333
    0xa0914060417100b0a052b23070506070c0e13050714030c01030c020c0121060914150f0603091c02100b030307051203070c12030c090617070509010309020d 68
    0x2070445408580d00307005d20300c82c0460300010a20000c003003079004552502c0714600b00309500e40c00085c0072000041c8070b600d40ca00e5211250b0003c0122840142040c0b4980001604801e00ca280b06110940010300404030181c20350700240da2105050f1a40544441c501c55100b0300180503004d00500410600b0400441000c007034000c40407903002c40800700054080759940b50105006030400303048215554052614241c4060550390742403a00800c1440c0e5408491160f003020320350035100c001e42403807170a40b00d500b140c0180d0403081c50f11380c2c1826000000c008010012034903020328404000102029400d1241202184c4441c8104482e282001c070003c4d01e0b82ca82503004007020b807902c00c00354010f05000013610301032640080113111444805108041b15000100303400b04000c500c00024000501122000d2203007141c6031000f2581d820390714800b80148038940c004604000c2d85030f031001d0746442c1498400340c00c4110350410b66611040400100c0c05002581c002039088030003007131008100b040303541444001c00c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 860386798 1250 860385548 860385551
    0x3251b0503120f060102070504020a0c06050f01092d0b011101150306050108010603152c010606092705040305090a030b01031a160f051303061b02030a091406041710 72
    0xf50303142d4402410700c8058920a0069124000600141c00d0903402010302c0100790606030f60120041d9900c20a843c01110181c4404154030010040c0c00407500440b8400d411122103071807528544001c0c541320640c2c410411403825141c0003244016401400b068003000c0c07202000380301400c2e480c244101d50f1140c82c80102c600034600400028035403411b1080c2e100380c2e54030949240c4a0901501072030060034054440c07160f031804040013006100825109559901c07420303000070030b01e145030120141000c00c6a40c014178444c40c0c1005820300220701d5005082d4240440072002526486a040c02c03250390151500c00b540041c40002c021080c04503548045040780d00c1860481c102a6064920002404068404000d00504007015200c1c85010710300ba42401c10700c07031400a05001d03884c2084408c0012651094840079503a5800b2030390b02d6010365001070b68541d43e00045141405482e030082a1171558482e0003a282c948040358000d680d21002200c005144010300e06202040c2c244500307880ba0a070310006074103039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 860388048 1250 860386798 860386801
    0xb0705100608030f03180f060a14060d030507060608060a0f060b090105090603041109041101030e120d0209010c0602070b100f050f04050712090302060115030203251b050312 76
    0xc464500500c41039a540324003a500f40b03085001103120b260009060021209032034201c03022051801c121100e0032526400041c40c25090844144044841030040b81c01600c0202080009980b0340e80015030308954586403140d81e514080c01c1c181e000b0000b40d0042481401380006020355040142c0150098403948401041066a905802c0201d841407615140c003080c024003440c80c0505c1c090000d15402406100c0f450320031100c400001c2e035800c40444007283c0c00004200d0500d42035030703d80f00d540f150541d210010503081d0505c0810240c68050900204021900042c10160503482480d01012850703000c4410364442c034070341c03908900104085074060794668400900050324012515001e04489016250300c080449040074800903140062002c010f0007e0ba0010520296640c46145c00f018080d5015180755410000d0202e1602000f0b60b000d820540140107100703440c1c281c0010700000b4500c140040c5440072401c6016540416800e0510900c4848e9000090034401d0200c01055080c0340320000c510030307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 860389298 1250 860388048 860388073
    0x50406090e1302120312040f0c050d02010206240a0806041a0c0405010807090308130503060108010e06060f01020f0d02010b030d03060e0613110708040905090d0f08060d0c0b0705 78
    0xa00c00121032000b09110019044000750900701c0d8030840704071440003502c1c40d01a91888499110314140c60444003120381d10b80100038403103038011072400307000e084a001441c40d4064000135a208000b4081c11000f04140703078000b1010350f8084904800d40340140c50040b00959800416840f05c82c00c407000c0c1c58000c20240406401070000014074418005084031b1810705090600445190000a084000b8084000004000300d191040904030b510004548003448904000c10306003044410313404000b481c1e041c0030103010000380100ea201da20500545a8501090005004078a0000b0382042c0040c0c1b4081c14240080e00e40c0e040d0003060681c0010380403a4000c0c03030200340403002c89510b23108080380c12030510301181c41813400908031510f0500b1007074045180c4c42101c41c0041981d1101c1022110341e080000e0412010540e0701415511103241c13000303024808100d4a01034110310320b00011100f0072000000086866451180920b071007500820030840251311001d50104a82c072048064034184a01a00e844a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 860390548 1250 860389298 860389319
    0x40f0e0f0114062704050103060b04060803131205120c1605100c031b0822090225050316060b130c0212090402162904020d0201080a1b05040609 63
    0x2540107014050720301e080442000080c2c1031301107442e060761440e40c007900c0c43c00540e281c0c0500e0340039600031071000417055110003c0100b201d0301d6506c942c803550002e1044c0500c020211760f5040c00c0f82ca105440c800c5400c0780345005400d00c6900c04100100715004501032801e000c1c002405030300c0b030000f21400701c480f03500d503010054401c0340b40804000140d030004105000911481d5402400c000405800c04c81054550304c55881e5004510003c84030029490240e92101a074805040217002402c1c0840c0351030300000c005031090103103d10400c10410300903004020031004100726400b4071504142c0116200052400c00083d240401040d03104400c00d0800c11070890300c0388100002088103400400042080c03803c1040750782c0200794150392080e402c0c4136072119804600101140b01d03100c2c0401030b0200d041c80e140040c88090039111101d09506150800005841d01281e80e0303003050702424402001d581c3c111282c0f024021020310489581c1da240c1c070301501590848064004c0d646a0b4846450050f1107100300c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 860391798 1250 860390548 860390579
    0x1140f0301030c21200102011e1a010c0f06150b070602070210210b01020c040f0e01060b21180d020f06070201090512030a2d0c0e0907110102040f0e0f01 67
    0x3481c49145e41c20704081e03041c40891400184034107000226401c2d071583d050010b800012101a654940c8886e48000d000c0907000f8440d1546034242800c044010054480352071a8000c0400100515556203c2d00030700d8050751003080040061110b569961601441c0c548041c4d002494100e02540c030000c0b1005c83c40e40103800110724500040d054502004040c40d20358040c262004166040d405040000012a01c0ba4007890f240c5103c00200800d1070120704034020300310f886a61002400c030006006005161994580702c2100c1c252a80d10010607071075401145030007c840e0301150200b0311410174490565a0003103851645080c049041e1840d42c2e03900d800603426580070810042c21a0400a4850b8000d0841c0c006903400100c2c2d100d00040070503002031407500900c4044213003608080113242090740d0103180e0080d001050407619007504401e9404001c58613100307014007100705103d074544d0a0b1002e0082581568005c083c0075030a40c1d0929074a55031902e0825040d40c4c246030f407800c07503030011404003103694401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 860393048 1250 860391798 860391803
    0x10060f080f04060c03020c03070c1e030201020703080f041503051b1c0e0a020402120906090109033002190e06041406030712112a03040501140f0301030c21 68
    0x1280640d907a0343c03003030001c02ca41001382060643c01c0c00105040c160800c06044c00522900340e0005d51420312207204503200c6281e11100b15010b2444041c80141d078007007079090840f03030312020a540701c03107908012900c14016504455517281222510801386541504224014401100895240b0800d502041c0d0310744150b80c0420703000800d042c541910001250301101201800c1c1c0280c91420300300b68009030a81c0e0150b9403004280075038005110110805025054221507168020007615040742d80141403042117408110f82825269003c009054401003a11460118071504641d215041d04034092b9840000381e0000c0014016a98017100f13090000488060343c121903618858403c80c0c1c410412240d0006009004201c1500360392664010940a9540c4103101d40100c1910750541043c440c0c1106000070440b40108003211504840d4000031040760705440003880c12815401042e40711020b1031080040d907a202003c0000000103000e0740c0c0c200780040e01e055030340070300584001941c5c200740000001c602 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 860394298 1250 860393048 860393071
    0x30518090402030d1d2107060f0c1106070507031506090b0a0506071a0f01030b06030a122609030a0e0d0b1512060a0b1f09030b090f0610060f08 63
    0x45131070399014000082280c00004034500718040824080f4081c1e41d0119a0300446400b03001d41c00030040b005020a401614552409280550380c60000038580c880c6074602a009032071a00e07061210703445640031602c880740c01134121180c942d641c0c9080c203101000403100c525058074240e0003043d215000d005481209800804400000e4100302c208041640880340c103d6038000b0b1007508042a10414448034481d0700c000000c07030181e61450074011403903070008040c0340c444c1d0003164661000526501c0307180348007022890000b10204813002c2071540e95090000c00302624541d072081003a8440000b0042045a050703684002d00802c09009104140c520104010401010200060040108416038440a0100809440421004c580d24504014003a00c028900e5034030b54111580c0343c24510002141c1c48103604803000e400280140007040400c40d404010f01c141107a00101d9084c030810890410300c039000c802940c0480c00d180c8003041d003020045c402e8074046002001084500c1d80143c080c00d1044c400c140341c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 860395548 1250 860394298 860394313
    0x30b060405030a30030b011d0607060506031e0604021f050d0902030109141005060f0303070f080904061509090203011215090b0112171e07170703051809040203 70
    0x44c0c0a402401c841c2500404001000410f4900c1e410ba00710320401e44841c0c0c80000360010034400040c0030070320690f0700307140d00c800c444202d608039103e00c41214841500103c00107015120040003a0400208504940d05964100501c1690030008606e250149200712017000b4100030034110304480340c1300880d1710004510280205502034a131900110000c134802400003810044960721840c01c402e1061502e481a44444040c031802100351141641041c001c030f511000c2082c4150020780e491180031001415051400090030802c07005206803003445d2001081402040d8031513135104800c1011b4041600003074000200040e03094524401c4905032032404112407c655010345408601c8003500c050b0076032240d640d030b4112010500501606019100050340a002d0b801c8a080408015641d5405c40740ba9a02c09c02c003030a00301d4001c10000e170004030f400036142d40741c00190030b0035140c141d021861062724500000b00e840806900c0f00003840c1c0025001c0300110700c0c01010301800900300301120001d4041d4010b10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 860396798 1250 860395548 860395553
    0x50306060105040e0907050a0e07030c02010902090112020a08030d0e060a0504170c10050c0c0d08011d091203040f02120c10140906040f030201231e09041b030b060405030a 75
    0x1013154130a0500c0e04445505070380d50080f660b405010350102d5107104020044c081c107503a040c086d22181a0640c40240f1502030203030002070103070b0010300c6034074000d0700b851a13800110b407070f2500c2400c01031a404080d261030306800d922010292188041100e2540102c0b000620000e51b1480798a00840d0440b003001c161084024643c40158402010545540b01d201941070701b103243c4d030003010f118460420f090760300c510000000b2032400da0611400d500313001045005028000ea2000f6902d891808494003010a84404507624100140300c411f0040d480b02c0041040305100401c0f0000d64100d10940c1d03008101c210f40b101791601c4500000e005030b8414846520208900d00c01c910100403521001a2035141c07a15000000d529980701d60310001564060440c10005d541e003001c40818500f010403003d401c51000c804159035948107586075180b00c8000340f1202801c1015200a940d5038045c0070300100222003d00610b945040c01ca5085000040d0400b151004141443d00507281214005002880f0850013035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 860398048 1250 860396798 860396819
    0xc1d040807111f0f0908030904020a05070c08070302011d090708040311070e04060e120f0a02280b06011e0818061f05010825020a02060f1305030606010504 68
    0x45805a8030503202c102400d02e00e81e10000c000303800115050040b4000c071000100503003150403a002041c1800001c00c0100030004021007201c1d1210401c40c0d0059581028050681e803d010300c080107040c440c1450808038220900007040002d4a000342c80d000030369849580044051210251041c1c0c010981c4808251454000e10701d80381c001e446401c0040381880c08dd001036190031781e02e5010440b9000740c40240001d2001c2e610800b08200b0204000d002c410b00c84510807555803280681c0c800e114400040c0c8501660300c02e024038004511031501d5040c9425145404c1004a008084191000031400001c1400c942c080c6481028000804101d40740b100034100044e07420321401440c400c2e0b14250101d000b000c40409205041c8120500c001300d01e4880c112110340f00b02c02c10950001c50503c00c04200f031102d42e041c07074150000c0080c114401d00310083c003035000c101c4c01e0003001c410082d000140030604025100080010740400c0544404082c880d075910000c241d940e4034252003050208108100078821705248 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 860399298 1250 860398048 860398057
    0x309061121070212010507020c010e040207020f010503100b03010608011e052206030515070f210207110405010303030b030c040203100323030f04240906050901030b0604030602070c1d0408 82
    0x400c000e650340c08001c55542950306c11034081005820a6080300311940c1c001c00006107401e0244e0f011400d15042d6030200e001044e100c2c1c60b0a041c040e001c40003940c18000c0e0290708000d403030302e00f580300e41740e5070344803405001d94400b8010480c4021003240408500c011907022902200c0303000703010080100c81d551242946030001c2c0c00c0e800900f41c4401c004030110303104010078031030004205140c56151500200007000b0480402510b0100807002d0000d070b4142d00d0510807120bc0e02c2e011a07005035900740714a80780c80c46040c03001440c1d0704581007a0001082c507406a2140003400c1d01602981d840c0c400500801c400c038441140e0140015001203414004100c1c64200f03150003402805107120304008441707006146800003d00c1300c078070b10000030302030281010b40d00c2c0842c0d0302c084680c0c0070044903108100142c0ba1240602800082050100701e035800e0b07038800d811401d03814801609240d5115220308181e000380d80f00080940700c03049204000079552003088521b5019070040358042c0c0c415295541c944540c1c0c0e00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 860400548 1250 860399298 860399303
    0x12031905030a0b0411071406131203091b08100c090b210421050403110108062704050c01090501091a0f03010b0a02011103070c1b030807030906112107 66
    0x1034a030a043c803152214440c8100c10303440422500d440309007d151840d80d24000564030072140d0000001d00c04103000c080c00c2c10f65075941c400d001c55440221041e0031001810000c80107040010720601c0c5c0640e1012194002c0d0648540c48241c1d07041980c03e043c20416580b081e8440400600c1c0401c003040604001c1d0040e182d8185100326805101c50703018072410b62018182c41c255105040c182050120712048000d00d8140c02680c100036090528680701c083c0030520350320361141448208000205e543e501d2406540211803880c0b48030a84061041280405581c1110704450754440c144003007000c0d601603072440040302c00c140d444000181c100100b40754610409900661003020900c1510b01e14031b00800514041c02c0003400c82d60700c44040110090a6403040d400c0c000c1035041c20003e0040c01503000030440e00c043d40100d0b041a0510700c8102c02819540d071a8005840036401140700710070582e00001000484002c3e694640302207006010b415150582b034606000b14184401c1d070590348030086005042181d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 860401798 1250 860400548 860400551
    0x10f03051e090a140303070201150b04181b030b030f070b09010f0201020405030a08070510091707050f0a0615150c11061905190309021c050f0a030e12031905030a 71
    0x11510fa0704c80445050000403400141c01c080b08100e0920f030b09115154a030303241c40c65091405c501d0218011000e20660007101d01c2d0600e10141d46681950b150804142c0c0d1001c1070f0041004540540300400620a100005100b8059100c0e0a88980c4000034a48103071242c035007100f4a4089400b00648809030806600425550207000004e22070b9410710466030f41601a00201d6075613441d40c80c1c024104032003b03562250252500264001107420303200008494600480c0b03503541c035442800c2a629004419608500078803420152008115040d000303141c070304000b030b00c050400c95200c90360405001110500c0c0320018104190340340c041703284841c3c085c0c00c80202905481c0340c5194046039061481d0125204404038800242c0030400911810800b84130103143c0c0780411420f400d942c00140c02004080404402400c0700400b8010b204090100700300d220120b00c00c4a50520380740c500580103000f4081214450b8010b0318107803002c41400b0040b80d217860001c06108205000228090f500c0340c00c0a4600c1c0c03041c0703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 860403048 1250 860401798 860401813
    0x190b03040f0501180b01090c0905060903070504091a061225150306030311030c030d0c090b03010815010905070804020d030905100819180305090d020a14010f03051e09 73
    0x140b82886000f03c004d01e140c84181c0111041d0034080304450041c1d021f459600c1c07174480305100403a4012680c000391401111042e546140303c8002038a420703031070f80025a1103860040600308002000c3c030000b80a40e010a110300660703499008011000c02d44a018003060340184c0414503001001c2c03090604ca2081c2c3d105803034200b03600c4403d890603d03500e090000005c6540e40d1014024075400c988100b5100c4a00d0b40258507000c030b1844034948900034119040f41c4c85446207038160349580902c01480240c5000d00000b9129a560311503596602d1b45502e13001d8514161400220721001180501c91140e5126101d10840d91140e509000140308000c0b4241d0130800d8408010516a070703030910700101d81045a8492440e42802044c01c010342c0760491180f40c8162a00c00e1100019002c0201c01c1c1900ea0142030168640552002149140d03a40040080d070180286802203000306c112421402e00c1c0e00203a0300c0715030300c038000d840c01d504460066855000340603c0103400c44825890100a03540540040d007500c101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 860404298 1250 860403048 860403053
    0xd0510030f050c121b120c0301090c1d010b1c1b090302040509030a0c150605150a02010506120c04020c1005040b041202031806030a09050d020c0f190b03040f 69
    0x1555251502110b80f034000c21003861540c54215a8064085070b14806011540c203602d4400c01c0c0300260f070b8010b034001c0740c446604003070300071043c00300d404c0d0300c41d01030001d00400721a49002a000782403402018900c0c050413000507084d00038844c545050380c01e80d03e1040e1406101d07401064000b140c010300c241c0c04ca83c4912811240404030141d10b502c40190761a051001d40c190720410080e0795006140100369071007440842c5200b54008000c6100c1d0781c0200c0601810340c007042c02107010380405c1e048250420410500e44140481d810010890384100360300810054655200f041030320880d01070981181c1c1e100000351041468240e00a05000d04008110707007140e00c4413000c0300300b9200107d5007034884811910420051260394002e001400c0713220300c090f40c50600d1035100c00242d40d0041c1d040a00524011002803280c8129920052940d0380000880e401e0f0070200000a40e20b525240183e400f6078600070b030b014072900345001e69070601140041024545400e10700b03210982d400042c02910f0b04610506500007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 860405548 1250 860404298 860404313
    0x13020c0d11032a010f021206121908030f0606070314030606070c0306020a0f02030c100513050303190e0c0916050f1306030507080f04030f02031c1b0c02060d051003 72
    0x31840c002d50740c01c03c18810f07011030950856400e85505035041d40100981801d905041e22403950001046980c0010280010f03035207480e01c20010148110b507241d43c01c0d401c040c0310180300594810000084807003202e96a003018002507014888000740802c0e400740b03500484101200186034001d401800c0c5605103074a03a15030301000d0850f5442039a06c0c039400a5480c1c2440ea0004600d018108940002c41c9400703502e070005507a801c202801542103a03503602c0400e4150003003003100e4002c10b03003290441e903c83c20050740040d150601c95480108103407501400080c5031001080309009044018991501c039500c0407008032418024100b02810001c00b08030403409558240c015110070400d1000c4640d80a062007030260031210060701c40002d104610301002041c01c20702034000c1c0d01c280c0c1031510341c181c160789031001e91450080bc0c1d100c448540201100c0c0300b09001aa00c01c9100c50340c598034482c529040500c1c160340303019142e00007a4000301e0401000c18038084a8020340d13008101060485a219500d4450b5403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 860406798 1250 860405548 860405587
    0x1350616140a051305030105060d060504060b1809010b01080106020d03050c070606060c110f0a05010e031524040212011a0403080f03060916020c040e0a06110913020c0d1103 76
    0x2000c2840450344e0203904d00c0303581c180320250000760001c203d49d0030841d0000c3c1e42e44012640040c0b6203503c6000040400c60f1503042040202c10140c0340140020545135031894070300d81214070420355842e05110354907943c85105454101da4840d0003614407810b800400314080d0800400c3c0f080d000000b0460040090010b100b4030300104510b6503203035805c480761329200550081c040885845080d2220340035000c2c1d507c6500b168103c801c00d00741501301401840c040b0b82040c0528504103035001c005420401e035056403034691501e07010703035100d41440080d508082000724000c0318035524000b0301d110f0043c1b098110614401c4481c60402c4030f003074107040e50303030340c91908981c4900703540d1031407060100c00d11006040481c80c0380e4004108070280013080c120540000e503140d0142250911494540c1d0749604511070174003100d1491034000c58244210100d00d91600442e50104131914000d003000c40040c026400c0c03620a44405503641000740400d8488110f00300c510922a100e000c07840d010800c0b41c0e00e8900305820586 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 860408048 1250 860406798 860406817
    0x40b070509150c060f0f04080406080601121506110604050304030311030c01090c1a0910050d020412060917130506030618070c020f012f03040e0135061614 68
    0x3001d051400c40d820100b00c2d03c006e085100a40c08080074080083d0305403003034030242e51003450481016074940340120341025030105001c244515006800303480782c0044012009031106501d0f01486c09812242c2c065071000201e4014000d6001400140300080c41004400005034215088a0410806e04403950844104030401c4400c40246802006100f8000030304031340600940402c60b013005004170200701c1050101050800304000007035140084a1a03905840c040c107078400c0480c2c0103004900d4402d0052840c58020303141e0590501005000d1284201100c040600c0401c05010342d602e028203000c0c1a400c09490940d00061183c088032000080901492003034040355100e08002d21240184850000e43d180103a0400204803021a6980310200600c80700502041804e22214201c001e81400c6000d187c209802d140c001d42c1c000505c00101c00d080e00c0d43c50b00424900d007909082100001d20070040300c82011001d4002078000b414130300c0040414084081c160518854540140c90413800d581d2000d50300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 860409298 1250 860408048 860408053
    0x1180b1602030312011508010617090f01020c0c03010f022a0c120a031107060203091e03070b07060f05010e0a05090c0a080312150f0613030803150f09040b070509150c 73
    0x1003001d4095146d9800c2900044e040680c443d5040100040104941c565070003409040100400c0c0c10850400454141101500003151510704101d5a20b4848001c02e603072074421740c20901039010007017403442240c040e61000030b68108c443c08040683d8441f5050455240350034007031164810041c1c0ca80421146014041b64080c2c1f02c101058a806030900e1005000114580e024450034071015400008880c00c00304200e43d00d030200301426584120680300080a2078040c0140140002c4200701240a440483d20a200a0221600b90310070001142c0007440303481c921100060200304004443d900090300070b00c210003900c00d104a40000f1a0080d07030f0550080d042a0300025031f907520701c1d1201c0301d401d421401e9000e00800d4a24194002000b00c4181404648107000008040f10540c0561801d1741c002d681c032052058a0380342071020400d0b0354144640840c0540000034010069103060800c00344030340ea05c91060340e407580303522500725130a070000041f02c0d40105486911000c48202d000203801140f181c00300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 860410548 1250 860409298 860409301
    0x80d02030a0507080f040b07210207060533060703050c120910050717090a030618200108180a080f030a0b0a03030206010e1e04060b09010501180b1602030312 69
    0x4000b0260b0030014682007030040170300b003440006007402d201c0f1038001c101840c040e40401c142c8100d031508a5411030b03601c410706100103889010881160440c031312940841d00c0620a006055660380c543e40307280d50941c91010001c4102541c2450280c000c2d0101d43d0082c0743c140d00b459080c000c41e610f0481a07509509200c1c40c00f1414607000c1c038110000800c40e40403440e00078106180e907901c0410b00c95203486000303a40800403035400942d03201c8540f0b13100150380141080c04451403002c0030480c0003c2400d020384880c0e050006148125070000c51507004600c061707640f50102c0e41c89160440c501c1d41c43e41924240b80c01400d070941c01007081940900008850f92500315038908080c6540011103010050300c0e4004c0000324400c002181c1c020403c5811100c0741e0606403c01e80e2120201085001e107003519101740980c1100348010b00555034415018002c080d2660107440e41ca540040d00c22400344051030044201d600740c184080ca0801d80030305100c003541075105260944507800641541c008610a800c903a11600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 860411798 1250 860410548 860410561
    0x12280906271d1605070203071a070b0f070e01050414040e010e0a0503180f030304030305070c05120f011401080d030b06071a090705040b0105030c070212160e010f0f060804080d02030a05 81
    0xf00864200d031403400c103540740402e60303404203480c0c0c2070030301c1807500511003400300c800c9a20000c1c048a803100d5100011007140d18042115211180050f50403100103405007001c3c0809500803800c8a0035100c48404498a100c52001040040c0000c41207154140d521500c04520001c0d04000041c032183c030500107162240000a1034207464010881450310079a085404030317169441c00300c211400da0380c151500783d030380301c81074107240f04140b2540c0c2c030145c2c1080f0b0421b07a99180e21008244480d4000709480284070703849604802011b580c10030f024490150700030300103101d00e0a020340d01004820b0f1014007020f0030100c00d9101c041c0d20500011070b00c05102c00c50001c00032203c00501c680c90252401710b07402c01110001030002030040c040102044c50f665000a40f0703406550304c480e0900740d182200011104030b07085441c081003110b0403601c580311017521441e0002c0b40240e01c080c445001d4400701103480b5a504e2600c80f0484403150b01510685111404202c00014007503a1b0005600c244000720000ca07090a014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 860413048 1250 860411798 860411821
    0x5090a1107020904140d03021206010f020d0c03030905030c0601053f0f010501170f0601050d081e040605040f080d2012280906271d 58
    0x180800a4203281088402600c10030800395007032250103481418456403903107402c4c3c0e02261800700345003030f81c4524a071a10555a26800030000300c3c88401c1081c805460b20001524840301019565015800407c1e2342c55000707103c0d4401c0700080b0300915011681038408e03100c0c0d5045a009110280094000400521082c241700071000c50003d6508045582d202c1a00c000c0c1500100020021100120001e03c50b0842401001070904080c42e81000b0040c2d03580d624403031060110b050300e90350f02900a0884282c00740c100400e20904071100540a100c10306501d03642c8030b00c41d40c82a20001030b0070308290741003504a02d0500c00b80c03000c0c1030b0984400c0d0b9117a0909032000d4040d00240c0c400b5400364031280d08005180c0e840f00304821000030b807034030750310024000740c60003801c1204088030030940045c00300d0f02c104044003081ca01303000b1941c02040a980b0080e900411200e0702141d00800d00840c0c1d65000c0458420b101c940c2901c04400b40c00d0054410300e8440300007041034036039010240c28a4041009214110606 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 860414298 1250 860413048 860413051
    0x4050a121205040b01051c050d0c1110090303260103020904021f080702060f160309030504230405010801022505190818030106060c020402070203011103010806040b0703020a0801033005040509 84
    0x14600347c0e4003449000c3e07403080c1c1e94000300000f050421107004440d00c10812040031080800780700400c1d02e00c1d51109000001c01395416488264006002c001e61034207110b0b05d52414041034117074402c29038226802c540230301c1095800031300b00701c2c0c002c60310030040c20441040c414407038010074655403900807900305071070001d04d01940a01a8001c8080c07120034403105500c40044100c85a09034280031926072640c0c1800da07003901440d481112084000a00100350310010607094a000204440401241e600c81d07940c03608074010844e0400c0d5001c0610700c44c0000005114048000e0fa2003801124804ea07002d000c260403204100100b12403094000c907512241030b0031b0f81040003458a0a5000300841840d10b400140014088080640616400100102075440179080403044074508224070f641c0b540c1d9660100c0d40c400b02103406561421400300401c5106200380200c8001c3e100030707591007140d6400c54880071080030101007a8480300701040c04c05010000d1100003440b120701203844107500d4a1901c003e00c070b0301140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 860415548 1250 860414298 860414329
    0x20d230a0203221d04022b0c0e06101b1e050105181033050114030f06100e03010f0c0201060e09120a02030c1507090603020304050a121205040b0105 65
    0x20f083e081c4030724045000002c8483d601044005241d8032603001144a00d4241800350386200d00c03e4809900d0b002c07007580075003a81481040b903800c0d859075845440d00e0845017660034542c00010900030110580c441d041d1072100d06180c03000010703c0c050554517110b41c10555886446101e685006d030106000f001c2c45030a40c00300701c2c1d40040300b071101c030203010729180e00f0f00d40160004c0c01d81c0d03512503008060342c602c45900b05042101003181241c0c1c55004c40b640c4481d540c81502c0c0042d00c1e501c6051074900e412819031b8054820755604020079214a4200150907100030301a50800ca00008681242c0d44e090244002d9411030f4070000440090100707000b030945410fa002070b50201c42d5003052144802c070001c0d0880c600c60413000c040362500b0804c00304034110b10443e1010701c0a4883e004003454450300040c602e40c0034081c5a103038610b000b5a0f62a0036800d07400708690160840c1c05c03640c0380c000460480103071710341c0c00204c1e031800410702070001d14643c080f00d030207071015641026860010b0105040000124880f0300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 860416798 1250 860415548 860415607
    0x151a09091606030c09260607021501510c0b0402040203060301060b04060906020709050c16060f0908090a140d061e0c08060f10020d230a0203 62
    0x2100e940819607085520403103003010303510203c0310810340c81241c001c3c000e082c00b60441701001d000c05131401c04016910068060b207008a07404152054000124913600c2503034401310b80c440e40e103452004107080f00c101d5100d101c2d0200360100305140400051001640303080e1900000c400540180c240c45400b5008030840c0244088040045c010902c151402a4010f904440c0569641c0c0d511010902401c1d150f4003184c0307450004203022902c1030304070018806540281d8200e031006651006010b003501c0301601c01d043e01d0f01e000c105c48180740c000c034405411403500402c03010480342c0088103000122070340f403201034a8101e07000c00c04001503e000800c10008140c0b00e80e0b10441d01103a400024445c0304502001020141d548001040200761403112890f00784110300108500e01c1e5100e000ba0840340300701c8103a44104901c0f1018640e074a01900c440300700314410ba0061100c05070060090b42d074164854403050b00f12809481c40103038852000c008140f0000329030b015581b1904001c810540c4854814080703c20030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 860418048 1250 860416798 860416813
    0x10e03031902030a020f031602010507020604031e02010e0601090f0501080a020f060d0b0414040b062d0f0307030501090c0902040e0a020f0c0601081b0901080316151a0909 75
    0x64003481e441c0c1c846061141c2005035651940340d0410028402d203119043c01400200030015a4001184c000d00c1d07484158000b0f10a80c2d4442104030b8071075000311002404600c10030090300c801a060028070300d07948441c0c000007a411002a11851400350268003205003592503164a0b41c0030750f628040d850041c169400240102c0c4043c1d40000d108004407042c1d07070301450340403e44c0b00da500d6079500070131281c44014104204c4800308000d0341c1d554400849081ea09950310001260090810a2024030700c01c03450a89561003441d500c105050f003140c0005090782c00003a040d0900c4082d6000d0101000562050000159000c0c0c03514000d0044c902e81d912181400744140001c20200d00b11081e150b60100040400680c0e9804110442501c4e00404d901c04549218000022840000c00200d4040f44040c2114050607201030004104660a003401422240c2d0428811000820400b001c002c12052240c102e40e81e40e5040721001c1021180a500158040d070b0540e441c80d201414211000c1d6003000101000c1c0880c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 860419298 1250 860418048 860418061
    0xb091503250605160f0f0c051002060a0c090b030f18120d0b04021b0105150f241207030618090203030a0f0516050114090309031209041508010c02010e0303 68
    0x42801d80e101c0d900c1400400140d000c08560809101c0d0516617002c42c440201c1038040c10428a011900c0b4000c81d11510035585c00314203840d00308015880c0814560003840240d484a0b440304c058440484000203204030b0030b00100d00e108400018602c41c850810814045103406060390343d40c2520814109000d800409541500280c1071003184d0500041040101e0400803c00c0424000c0c81584101c43d143c2c0180165603841e01d0b01900002e0240029140640400c0366400810008800c104200f65000450314840c65420401c1c1408081d50284010114100b42d00710810f01e2501000b100c610000070b5907814103008150341c66101d051101d02100c002c1103050a2035000c20307a01d1040380d81c90814003645014441003e4032807021282e071680780c8810040c880b641480c0044c0a040f4050269011034403100010b218044000161905004c0003401040821401c401e500419031000140c10741254585013a0754034840144e04520044c0001d45c0000340003080410000d00710740c1002e580b1a9990020000d1081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 860420548 1250 860419298 860419363
    0xd030b031905100203150f040b010509040b0d0803130311160b03150406060309170c07031e05150108060703060f05010516050109050d091a04030f060b091503 69
    0x19440100e101c0308803016003800c1483c82c00e11460001c10f011400001080000c4080303020441295000f81c640d4004a01d410b0104001e0f140800c1010340007801c1400809850318064100002c001c0c00500380095015058880031481d900499207482c0d0b842411101004040d4045000302800d9800310241007800d41005160f210020103104840c404000030010900d115108840c5001c4400c000b0000c10545544060180150504000c11b407078040c00400048028400031040715a003c2c90100503020701400e42da2194449070380c94031280203606507030655000160f0104480ca45200743c0905c008030350361500002d245404002440710003010b0070000200901d803210520002501c03000d080c1240c41d84040d018447c803480001402504940c00c00c00150140240410180500c2c03e050380c6040304e0710340710303200260000e0702d0641d11003030034108100c20004031b50420081d2003214440c500c041a18107072000000d17180001034510344001284918542c0c0c0384c1c0b504010689100181008583c59003032654400710 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 860421798 1250 860420548 860420563
    0x705030403110c12390d050a0b0c18040c0c140c060d0204080d050a080106030b1c150b0a031a0408271503011809110d030305090d030b03 60
    0x7001d00459804404080d40c05001241c60300700041c0103028403000c9640341550f519000421140c1c0704140c00400c1c085200e031902003070a02180c40010303560000381c1105000601840d49010b5810740168500c10002902c1300a4060241d909900c0316038031505038050b540c00f00e40c1080b10b110701c142d2038111101b90603508089440501c80c0c111000807a01d600102566041c018030010403580210b000448028072071480d80508140c8400c3c0003280d1a03040c10710800d0328148500000d141c04503400e10300400442d84a0742020080313101c081c00c040e82141004904512210030350b1011101030042d4095488503082a104001b040001142d1410b010f17480d540358000b0a000b450b0040410604680000c2c1c2070100d40320495002c00c0402d00f04240100d0b00140b1101c901c034110200794030031601c00d51000381c404001c02c02e0364140c415841c0c0182280d10401c04550080c410058110b5590020a024182c2551014401c049a0740291000700f603601c0e00c6440700c2d0410208d40d01e0141071514003010b03403099417000a11035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 860423048 1250 860421798 860421803
    0xa050d03120902040204080d080a0606090608010e0702070f2903061005180a030c030b0a0219030e120a0302071515031403090d0305071208060616020117040c080706050307050304 78
    0xc2c0c004160010801030700c01c0b07030001d00b03042c4103080d9039448180d440701c038031072156046240c10040542c88441c12a807142d02c512880000480c0000140031b868076100c52182c01c4403481c01201c0056a41e6560307041e00780d1040d0f004100050082138001412034910701104920004c010311180366182102c00100840d40c010301c004100040864011007491900e0001c440d4910001c102015460396468450103081e0300e40001c070794002da58404a00710050382e00135103c4540080c0c1140c103048003480402c038001c010308164000c8910507160101d01d01e079160002001c0c5072180395000750341d0385042d061040700440040030503030000745010340701812000d00c07401c1e4000b680c0d80304400890781d00c03922000e14070314042e410060b544a80400392080c101a0084010301c26580b20300802010540001400e40380c01902b00d4003a0340001040151072191840e4150380c4000368414181400d04980000135a89244400c650494030444490411b01114008010b080d000340414030300746103185490340c0024214003014100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 860424298 1250 860423048 860423051
    0x71d0f06032808041d07020f030c071a071208010f05010509101b120e0f0d02030d0f030f021b01060506030405070b0306040e01140709080c090609090c0306070507020a050d0312 77
    0x4104006202d0201c0d0010aa4044030002030117114140701d20459007500c210000d032041e1518007018a40c08001d45900d41c044030040c00d007843c40d029400203070f010307110032007140072404120340c4c5c0c0000d0940400140481050740c403401250f0400541040300d2090350011810300600344151451a641e50b881c030503901c0854502051320842a85425043c49540300c5c00828003d08540d144144950141e00701e205148101c8040454203008018000c8130340c6803020103074064001084505c1d900c0e0086014081c410310600d4005440c00800c411030080340c000003d01c001500d1000340c44902d02c4006d0061801802049444510354245581d51a90350740462003490741c00440440000e8039940c950b40b1051881403c00024800e90900151045204808680340008550031403408650740301c000031000c11705d4101500f00400394645008100c420f030001450408503101e4007440142179101880300754042c20840d1100c1780c13a44001c0c03041200402c0706400203409180259086400700340d0003890a080d04102200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 860425548 1250 860424298 860424373
    0x50307180b0d03030212010f0b18030c1c1202280503190c0201030501090203070c0609020310060f1d060109030609140303180f19080c071d0f0603 64
    0x9a00c090600071040e190b110140e01204010706030150001c195154614000707a0711031b0b886054084094060340204281d00d441032041d02400340d200502050940001022a80b91039139110000d040141042ca00e280c10b2400305090714104815000d55008014441c0080c140010340c000f0704101e898a41440740d558a543c44a50301c0c1403086c00d00032642c2900da806039030401d4229020029102a064a42c2240005e140c08000074500d8010302c00d4034010fa40d26030f41da800100e13a588030407000d86000f5030b00ba81d03d801411603000003c1628444c050040845611a4a100e0b1410300080d5134544c01440f51071003071410f030040240b5681d125482009507035000c900050281211700300140c44400c0240700300390a200010a012600d02045241224000b41c001201d000310443c1c600766403100c810f135100c803560604000f800360025140f00040c26000319002c2c11560460399806405151b07900000002823803404400c02c0c040e84940f001041907020405a00030a8598903d00081254041c003194a040e0700c5154076 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 860426798 1250 860425548 860425589
    0x507080f13050109030f080a0b0102060a0b040612060c020f0303071407050a1a06030115050d11131a040501051c120e03010204090e010e06040804270e0d0315050307 72
    0x10000c01c8080d030000020820300c0c0030b92030b020f8003202c0e804e100000880e205100107a41810207001d114840401a409040c02d80c5400314000050320741c03010181d602544803900403582c0c00c55500b2249005002c0c40c401b2510101031003011342080d00900055400e60070400c2000b43e1942c1003480c0d0f090a2006d90b50550b5155000d0820a007403414402d40282034505580d00700a246036490342036406038508400820407a080c2d003c00e02d0200e41d5a106041d0040c21004c2080041444e120401d400020050071402482d070405d017400b4116441084510448640349007a81d010f030502d8030500b405001d00342e4040e4044251410311140c1c0000c598401041e04554030000a251885103105200141015000b0b40d1070b41c0e241c0002e000035050104402d81190700e01070900a100c0c000281c65400307560081202ca00d0b081c00d04142080a4032001d11020810402c401d2403d0a540e051190b1402548040d015114145c0014002025900203800d43c44608800c0f100a2240d5500420f070441201d01e500b200352454001d86c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 860428048 1250 860426798 860426821
    0x80702010c0312232431060e16050702041a120304170d080a0e0114150a05040501060203090405090712140c0a0b0a0e01201006090507080f 61
    0xb2900c1c200c060304244492035a29910381c03011002c0c1841140c000003990311102010142c01c5069941c3d01081c441c401d54011608256003000c071b2428895101d04000703048204118071080e0280465a903c6640b10010480401c02a040326004210f0100c1e0912505580000800500072a00d01074820307555a0006480309000c10140e0055101c007922681503c5d0314a05055180e0b0001c0c4208098880c4102004002003004101040c1c40c031040c1d2600807150320744022841c000c0090030862030456603138944e480105103514160b070f4400c030200715500300f60f0b40004042c8290702006601c080c6c00343d410f100042c0b00e842d4002c03040e01c16407001524000740c180d4a00d0700321864044990700050707401d00c83e1102c44c000d01100304070b0081405003810440e11030302450340a0080940790380c42220034034003041c0b11542c0c11600c26035081c031440c2414984011010151001442440c209001404584c2d002510050700140f07039000f0180100803411007001146840d900c043c140303000040808016452041c00503811030405d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 860429298 1250 860428048 860428067
    0x120c02040e0a1403091018090203100503010f11161703070305071b020a090c020f07090f0e060c090d21020a0201200a140a0f0c030308010f03080702010c03 68
    0x800922034280c5140d14551a0726102c40107854a00ca41040010607942c0042280e0441101170100501c200070104121140b00c10000a852141444400002d80e4255400a1801201c170001050f031421303d884101405c50b00182c0e15140860301b01a40400404141c9095a00c0001e07000c2211141d403c00d860010040a40300c81c40725440311000c0280403220f603066101c00d09c200c050713495007607007803140100e06c4080803240d032402940095807001c10300110301c81d60404082072003140100d82c41d103141d403280310f800c150042d081403a00c0c5682c5c01e180742d819840c0380245041d080000b8050030007800c00c0328400e4a144162011140201c12402c00e41041060000842d0408403024900c2815491038443c02521943e0b07404060380014480404100f045016851510341800b000700280090f000c0d0b59211000d00801d089a006140640301c1c0b00c3d0b001c1064451001c105078400e0903210004c50440c078000d0302a480603041115604038030b440a0002a107003000304ca07440303a02400c12504804491804543c175621 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 860430548 1250 860429298 860429303
    0x6030901200301050901120b131a04050a0201020610050a050f060c030d09123b060f03370207020607212007050f030f060c121003020904120c 62
    0x5101220301c040310390401030760603500102c4030310781c9590f079580c0c4050781c462140c1c0340500700f48010b001203103c245140d110350607040c1c401c4101c0e158600445000c10090070003110b041d500358014000308000c5683c1488856803200070015043c2105040501080300034a541c011140a45004640c0b8401940c0b0201900c0401c149602200d0362011101070000c0500141503003104c070079a1190180ca412405008141d01c0c500401c0d00110703c0c000c01100c00802000b6411011021305034030380c10b410554030355400510042c020070005a40c0c0303080898451408100c1c02c00c000b00080000308010aa00b600c1602024013aa4408070140c0c42e1540741c0002030903441072400040250240e00f0903101c40e120039030b40f051000d041e071342c4400c006003090070f06842c10f42140d4070b02c1c1205034220301c006005925280d001940c8005015045410300d54109050718900385c0155607200400c0c1000c6070101010300c1c600c2c110b82c1c1c0300403100c0310716001501c1d580c046803081c0000f4100501c1404030007070480c0e0640c41410000c10154 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 860431654 1106 860430548 860430581
    0x2603070b06010309020f03030a020f070512060610120c0306241202250503090306010b044703060f0a0b0d05060d080c060114010f090506030901 63
    0x4a401c00403079006c4080c80069409072002c02c090a81c26605030010000c8a800450441c81d2032140c0d88114403c0b8a00d04603003000b0030000c81c400c1d402040903a515008149495416100d200e5040103c1e0b000c20300d0401c54041c0f03194550044021030362000066164031780c4144000c041c0f2218102d4010108007002c0c1a84020322072a4003e080d00d002801d40f04121382807030301031400c06407044902500d042e0b1000ca03a03164685810700400c1c0c01410500c0c220351a041c6031103c460001083e07117400c81c400301ca818a001d941d00d4081d4440c00400102e06450007188130780200c2d40c0000b0340044e21301c3c5000369042c2034842558201003100805403191202802d040020304200c64010f000700610060304065668104000500004c01030445d080c2c50001a0100d50304010300a811030040e211441d0400a980c1207011046401918113030659000382c8003a581c0365160201c660151030444503003139504 = true := by decide +kernel

theorem cover : BRFrame.Cov 860251798 860431654 := by
  have h0 := BRFrame.cov_init 860251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 860251798 ≤ n) (h2 : n < 860431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
