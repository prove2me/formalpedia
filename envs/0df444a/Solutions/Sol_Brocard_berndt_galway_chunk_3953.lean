-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3953
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:08:56.164026+00:00
-- url     : https://prove2.me/submissions/777b9576-dd6a-438b-be26-5d16b218852a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 710791366 ≤ n < 710971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 710792616 1250 710791366 710791391
    0x8130f090902010e01112a0f010e06180a0306060b0a0206090d0906051b0d0819050c09010c0510060b0c1501050d030f050c0601030609060c0801050913051207030302131e090f0b1302090f0103 83
    0x600900c030158000f103001117054460782cdc40c1c246140c4020341d400701e410b200441e2a000342c0c0d02c0d5030f0403144101300140705840c000b034000c1d00000ba01c80c00300b00440d1241082c1ca4145041140c00c0c0e405000724040c1614003c29200c214bc01c1080b002441070015074510351542003c01d0815007610440540030042d82c107100c01e10040305c500b0030450310340c25401d0030150810070461404030b08040386100720303415051900e2000200c1010038002003d203543c103001031368900f0b0051800041c1c03604080c080c540e00907a0702c1e005600042c0c0140100e4000700c52a0901d1403d01c40000fa4142ca4400242c000702c90041e150711600d130400041c0d000c2c000394000f40b410140310540c1058041804110020f0004020210940c410001c1c400e0a1003592010083e017005503036114003d0802038041e60148422a68150a14000180b00302c0c42c0a20f6113425400c2840d5005007500e09014071016202440500c4031041d41c641d5501e02c281e69039070410031800500780380561680c80394410418081c0362444018145410900300207100e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 710793866 1250 710792616 710792629
    0x1181130010b0f04050603130c14130e0709050c04090510090c020d020d1b050106031406100308070303020a03180b0703050c09010509190308130f090902010e01112a0f010e 75
    0x285d460a4820303d480b030b1b40d813201007070b110344480d000500059401e001c0858030007030f603408071104007a05403203d01c07103910074084150864520b00b50301035a03500000c10601142c2003680015412800c1080f265003441e417552041c074100c9009607001e5050400c0c03000204900d4800c3c3c0603003180f061590002e03094040300300e0720194880444034040000c000380281c08070946000b45032414074480d003080c003c0021648a1525528504c09140c00007414846e500002d0a03403e0008808801e0f04d5212a18900301410b5a4064019401c0407015105160312a0012400018030a01d00300ba2113004034146806400d0510020301243c901901c1005201d0041006c0ca1407a41c110301214100030701070390308469107041c10740005641d0340c25800c0182482c80c0040c0014119a006042c01e0070f0380c03803041c1d4840c803841d580d56084048910b050380090105851840c84101580a41e00f100d916070008001d54102104140b50a509440c0400f0030914804a02d041c075012810300d00080c0389503150038208015000b69000000d000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 710795116 1250 710793866 710793869
    0x924061206041121040203011e050105031606021b060d050702010c030f05090309120111040320061c0b12060703090c051008040b10080d0e040b040501181130010b0f04 73
    0x1041300c05030001c03c045460941c480d64031544040300802c01c0e481140c00310005442c0a2049510038031540c284c00c0941d050458203101181e24580040c9881c1c002201600340300307100d82d100654028800c0c000050b000b0720307900855106520503800001c88940f1414040d0031580d90a4407440241e240c801000003102c40001110800d00003101c0420156110310001ca002d0881a88a9071600d04041400010041580c8101e100c0d0010301100d414003251500c14840703180203070013580300400d5210000d01c120600c658801840800017808440d00140902452131078114180e460b840040c0d40c4042102c04d0140d0f0038207150290a0031521181084104100100030941c054406001e4012040228070040b4056444070010031041081d01d014141e030402c0600030f851084a854013490402c024205d061400e8403c10f03059551060603d144088014465002800381140e81103040000300211100403001070b1490751340302c1e8400f0460000194403d0070f03440169041e03006a600b4401072045110001094050700e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 710796366 1250 710795116 710795167
    0x1d09010908030121140f07081b0105090319080c01060609080d082806140402030714030c040f170c0916030902130e1e0c09240612060411 60
    0x4001c03081030b403013120090315541c000910030070f4406581d051440d00401c00303901780e141c0304080d40c41059460f40115181d11111810600005800001e140190f025801400c1c0d0101c010b021119a19450440d52944401c112825035a102001c0742c1480c0c0c41900340100b1002d003002c3e14000301c15529100030b99031f44940b10482074040c880e16000280501c0b4500e0701d518a9400c1c8403800782d00070310308108890010701060095110305e15140c0496040d90400307000b103a0049900f69036210150071840017800701d80d0800703080d00f008207030b0810000039503111403140800900600d43d040b418085040030760038900b042c000b00c1700740240384078010400c000da2542d04508280b0303024180400c40247c2880052046402040c8001005280c2030402000c12000209000001005030450441202e0020510340e1011400040355020103002d0000303000134044115014514041080051450b4681c6c0004000341c1107004030070010310300c3c9810000b241c64203008000c0200f520480307080c0307040c0f400468840300000350f16910 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 710797616 1250 710796366 710796389
    0x70209040b0a09080a0e01021c0c0308071808030c01061220011407050a030e010206190f090501020c101a061603020a0606081509070b04170a05071d090109080301 71
    0x125550016040f483e040790b40544d00c40e9445504a4016021145040c0020b005110b4003c624003a1400c082292152400580f981640c480c6141c1e021990000020140c404010880600a03485280c03610f41e00c02505540020f961180c09200c912400c541c442c0e4031000b071030702000c00400c1c0030884001d00710808100e00402189601d141070010313280304501c0300c02c0c5001c1a500050000c107105020a0004c105446561104034180d4a0401240d803040b0036207095070001d0079174070303640342d420110381c41009031040302c402c04180c101850300c5450032a000b0141918040e003020700c500701560304c40d10692803022521243d520109916001040d506c1c041c0c4841d44180d40c400c800c3c4c0c5e4081c98000c001707107110070364080e00501081d9162010a501c41c8200c0d25000610400708000c03030340d610070115107103064654155050381890f1800c1c09a01090f207003013151701524012140a940429410301208028202c0355071511550010200140c0011304001c01400705079252180390b00000303030030700212411107079034420383c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 710798866 1250 710797616 710797621
    0x3070614010f170c031609051b0a0302070501150e010608010f140f0f0d051f1a092203020616051c1d030412050d09031a04060f020c1f02070209040b 65
    0x600d8454043c0c02c407581485440346d5880b00159081840c0141e810f6042d061010b5101d2507007171505200501d043c400c0d411000d0080a03001407299001e003225074007580002c81d0244038020181c1c3c1c42078107a08040500241240184841904241150300500c266070b080c0c00f00034036003003030081c46600510442e44107103101c0d41e01102a0b91208680304c0d8200004107011000e20492821a42d03135102c0d00f05002c114080b0307007540c2c0c108940034803480c9020301100b24078180096003e0200420680014100380e1031850b40008461786050f0588292001072103500205014105615413000c00c1800703045107410843c1c100002c1c11000504442010350ba21818004282c0b0b090640d07031020b00041e110a12010b500c808075000403640d84040240e60403030701640503a10b2448001e141160841c10b5404081c102c070303182c0341d02040320b44041621240d0040c0542d0000031800c4050241c0c81c00d9901c04425040c0f69404a84a03001800c022012002c00030f03001041103291800c5a404a620340e0300040000d0001041c5400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 710800116 1250 710798866 710798909
    0x6011704080a140c011d060a0b06041502011d06010501140903031c06050d030e0414100b090607021815040c1d0402070c06080103030306080615090a1d03070614010f 72
    0x2030710003130110440248401d03c0c4495603804c220040b02d1001890348074003004a20122964444c03440d000702c000d0034a9242c941801800c080000031442c003c0c04540d40c0d54000c0d034405210654030b800f00d904480140101d940b600f0001001005040c0c1c6a900072402000040c1c0f031660000120360701c4092403904000710380c440da00c000c4001c04542d804941c11200d0021204c0c20140d01c019041c260303170011641008030b48030181b0200510b88040340c1400c00c61000c08818003580d8890350183c448044001c01240c603003030069003c20724841c4108000a0820034600501014080c0515a070326241010b4808114001507000b000348041c0044620f400040e2801210000303545981e01114040d075003046030030600301c4d46d440f4003c0102d4401d10003a80000d28140d000306200e540425030a0040c2000300c035041e09240b014080140f00c28018042d90036041c1d54192245000b00640341c09400300c0c2050b8040c41e2078a181c2e09100c001c1d100b0083d0708495240c0c1c1000141311103041c1494502c1521241c1080b0710100484c0303078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 710801366 1250 710800116 710800157
    0x8150307030222061406070f0501020d060905060306090f03030718030b01031b06020c0303190c020406180c0203120c030c120906160318061a04050f06011704080a 71
    0x1c10103900452a01c0d0700c41002240380440c0c4484040c041c00800004c1d60b14026039482c0314039014042d9200d2020003800022400400103994a14000c100040c0341c0030240010340100c0c0c4544e440066596210001c00c045480c1c1130103c40c0d4026410701c05000505000e43c00240c50340b1009110038280200310b0408201d2701d034610f034108003466012651500d02d50b180c0c208a40c1802c00c2800c1d81041003030a10740440d00d41d00c0421140c3c0c11580c042c0045050100700c0c074030130f480c440f09289400c08201107604003001580c1c840c01039000619082c2e08196400c0f81c1100c03030300b05035080c22800c00700b950300c01c2004407107100c800717a80540e00ca6a1108003c0e104d0316001020318061007401c104405ea04240d0040c44004980071907401e000305404c4d80ca003a44a601030314240d06442c1e062520480c401c0368030300d0b55800b145141d000781500c99065031080c1c81a0440380000b404a840c15200707440000a00d204020303c558001d0090400b1441c03c02c41c00a840c50540d542d0010b9104480d031207010070081003480041c0e0524003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 710802616 1250 710801366 710801369
    0x21f02030c0f0303010905010f060f0f111b0312130909050a08070302010c080f0106080a0c090815060f09011a0d0209040c0f03050138040f06110c01030c08150307 71
    0x3030081d182c081c031030035816076903c0d0030030b000f0441d0103440c4c6000000c80c51b0f8510500340c100d0703003140c80316106c0ea60511000c2d180a51003540d40403e2004924038085014010302c1200320295206095030101081c2e001070501d000203100b4030300d45468040040b2400321080c11080c03411150305403401700700440285420790500d410b00400900340c001c04912581011b4040d0044000302d0300f6030351065925138400c1c250710b0101d2000c1c820350000c541c604000c20030108041d0011122002e460504400d41552100b12515144c1c0e0500d55090021844060285a150140c00c0c91042101250b0200d05075050007518061a480c00035004240000003e032801c001c0f085805031244014018010440441801c1c405460815415900c2001900d054004542104855182001e0310b00302c0f04541c150944140d40204c412401020328006039005000004408202100303031409000c0d10717a2800b26141800300c20ba40741c429146034090505007400d0450850f42d6015804552010f00da101032084107504101003400c1c180329 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 710803866 1250 710802616 710802637
    0x70f0602090901150806090c030402011112210606070c0501080406091709030f060421090b0f0406090e010e070c1e063806130b13170a021f0203 63
    0x201c2c0002901883d18151a10340c203205854240041e07654a00300702455400316010500440d090000c1005544200d080d440c58074042d600700c034040c81162a0342c110a070000104c2e1000031822031050304120151041030f5400410590326107081c04240e03940d0245461150045c41d04008800c000241408829084010000c1e080f50103000c0002400261440d640c1c401c4e00b031a401f0f845403c0c84016400d0000426502c82d40c0c2015507004000500301501e8a2242c04032110020050360710380c00304089401200900d56000410a816591031800c00050319000e0f084c0d20804c1441103100041003001d4030851071b036601c1900d6103003c80b4407039440d18011410b145e51104004071f6200d0301401008016003540b005110408030154110144c0d01403440c3d890711180103156038038242d408004c40b90141820000340614400042c51a14015180d01c0c1814040d04040f2038000343c4020507008000c420403009003801a846030300040c03d0315405a0700440c0c1c0700c40c0c00400d420030084100310b54814191092050700e224884 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 710805116 1250 710803866 710803879
    0x9150902040e060a050f03153c07050703140703050d02031f080304030201090e040201091203260c16030909060902030411010207081203090c090403110706080606070f060209 76
    0x3110070b0311080d100c00845101c0d00035090810049003902d0710f174814a070603580080040042d6040e903c035481d079000001c1d2000009810f9100361283c8120780410416100c035080c031001c0c001c007943c03001c42a4045000b41407001840700410001000c41e5000e6490803000318018000340e42e135040c0346011240d9105800c0d20b0041030f0710100c00e0100e40c1020184520008031407040c400750b0a500c030440c807500c6c1e01c03d9100c000c2c040391442108211041003054910b90182c0141001c04525540708100c4030b005c10784480803070000d4400d03103503481201d9004001031044400a40010344600c0c01c1e54190015200e51203540700d521f94401c21600406200d2544007020b000e20740b10a2000c0e03a0b0320754001010350805c0d9021030384c0c00001c3c00100d00380c0d480040d409089036502e00c0206481803013086070000950010300150180d000d811002192900c45aa41c42d0289109654450920f440155218100907040c2c12100030800410203203d41130f074619080d9214180c201070304107007001d003500e4154000c3c89581142a00f014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 710806366 1250 710805116 710805119
    0x50a061103060a1e0519150f03050c21041b08030423180405010e0102070b0708060405010323070807060c0209090712200d0605101a040915090204 64
    0x221003809140220303010b803100c11010f500c0d0201c502500b040303003c081c95800d614140400062030050700c40c0d010030140c8602e01e00e40c0f80c1c03149092008400c0100c1c0b004007003842c101e50f0501a41d03040c400c00e603000503645152030400e40342210000710840b003a20791038a0b4941d04d030007107020320a50002c1c0b01d400515410500b1992542e60f90103039100d42252103400d01012a0007800c8850740b03010040c00180340c500401d15001c082c00705234480d9080c1e4000c3c3c010f44442d943c0f000d82c124583c5d4248010080d4502801e000c803042e00d0040f10040c00128014400c41c011400e150041000505206440311807640202c000b503040b142400c5440d04d8100350b130b0702c407114071b21482d100080c8094010512441e404e009541c1040c040e9500205640d668009100340320481400e10400000728401d5446140701c0308050200b02c42042d0310400040c0080a5038100740c0342241c0e100c0074007541c21070340c0d002d1200030401800e1a2020010000080d04a401548210908a41c560201c1c50704061001110b03406403d14903011502e46 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 710807616 1250 710806366 710806391
    0x12d0e070201020928060801080c0909030f0c100605031f020a030221160504080a0f080d24090b4603051005190b27091e030d0504050a06 60
    0x5c41601446201c002c42254045005481084900c1c103075010304005088100b020011b200440c04010401c2065010501c400c1c020144100014141455460000c240d2a56669000d400712051a0301ca0742c070030f91003900b00d51060031500c0144611303d40c0c040b4005848040c031003030035006445112440c40010010006160040c866500c80c617000301d0b02d807010005440300d040b4094400e4460381c01103e61a5000c0c041000c001604540d040151724815290141405000d00c07070101070341d02007540110006121049603160440c1e81000c44000e1000138002e20207110300e13401141c00404100107400c050b040014180e0b0705081540701000c50f2141c83c02a10a0600c0400359807510038106000403210f078081d010702040c02d41e001d4021180124040401a44941c0728100410700410080301003c0e00200d80b224460300d080c01d042c0a808150000b4410103480b46000d4402904003120b241c07040b80c0c208000d403040c480703002000083e900c008001c940300086584031420310340c0c41d2161604008000c1d50030700c03901503400d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 710808866 1250 710807616 710807659
    0x1030b130216051603020d1203020409050c0c1c17060a0515030f16050a0c050111030a0b09010b03010b090904060b04051801050603060106050d0b0d0507080105012d0e0702010209 78
    0x40c90041081d01c819a04c900349540d210310407440040e6011804814003070200c0c1c10100e8000380e1008600340140b0303041d82c1d05094000d40b50115480e04a441001c6904078100400f072180c6038101362240407640c1e8221212a001d091010041024980b07800103100103241525445901409010000c0c00701c0c5900107056175038515540211008005041e040010a6100103605280d1480351800d80b0b07003505001e001c000032036034612020f00a41e820343d00d998240c550100349000950240245e2080890340d000d2030b000348002501d040e808044000c1d020401002820740303400685000031401c550440440d1100c0c00c3c60000303002040851070b480351901003400040d200c407103504903107100000d0080c4010783e25141010703100c1d2024414000030030703010000501e00f80c05560200c0301da105d0040440302c1c91819501d44925000007a08805456907480f030060000b00030f04070519842c21010144455031001d528295a00303d84244514160b0024203400b0555040c001c2d0156098264041c0540b0385029046110303042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 710810116 1250 710808866 710808907
    0xc021c02010b090916120506040602032a041d251215140618010f230c01140103150b06040b0705060105150a0206040f0828020c0f01020c01030b1302 65
    0x5c0e0032221080002e00c01004510400d407403500f0001400301a0388948079000070391310007001000400e02c8070b4101d020498400820b64031807a109807190b0389039800c100c600813221480001c0b007100081c8400c100000302200701c80c00a8032071000210349402071399000f01500c0e1607d00806c01c0c02a581071078654069403d0521107501103c0300317803000ea0118818142440100d11581c02e0401c000741c8103c050020310350150949102c111864a86100c41d2003088081302a8102d40c0b10f03118114007400240401001001d0041e2050425031904081841d40f5544c2c464000740355480503030100703540350402809103560356825500200034030b24000b55590800d03c1c4ca10740759030090258a1180c0d05928a5030084030314070003582d6600c1d413135030010101500e5a03203400c020301011f4802102c8a80080000c25400b00f51001e81d000340d02002400c2100003030704804080e080c84441120f01d405407103071542c2159240ea00007081d004804003070a00158407407500e00400c5582c0011b180e01c2105a000040728004202d90403105030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 710811366 1250 710810116 710810143
    0x16050607031a04050910200c0309040b03070b03160201110c1e030a05041a28031112190b04020f0403110a140909010f0f0912030c021c02010b0909 64
    0xb14034030480c100b00b00855000365690340c900d40c00190502c000b0340069020070584c24003010528000141482e02605980c061480c81c03210350404121040d042c01c06004965802e0783c00c401401c0707020704002140380b5034000100500504020304030b2120907075000b0340c81260207880d04440e0369030b00c8401c400150381d12200c3c00f0400c4107c0c000070481c40c00d1560048140c0d004400140e5800707113006d03e00300c2640f034091040200115000c00800080b400c2d426000b1010f051100024400c4c0e00442e0380e42405022a0450400d071051024201700d500d042000170450309501020902e06080000c2c0d4000544d801821000c1d001034000b440000c0340700180b215038000d082280d22a40d102107507407851605004110f03042c1e2103503046100060b40041d05500d0300030405503010410b4400020051440c0c1802020b442d4844860301913207070b880000c2824814a0000f400760480c1905007030058102000000750ba0700ca60038100f0103060031448822a1951003034010300008140188502264103180542584413a82c00c0c2441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 710812616 1250 710811366 710811401
    0x30206040b1302031207022403190204090c030b1201060b07020103022206030e0c030f0c0d05030f0d0b0f04020c0601050f12010e0c040c09080304031b03080309010f0b0a03050c061605060703 83
    0x100c2e2484070420202240707403820030341d82151218a010615061166942b005040d000e01022035030178502d100c0d400c40114241d60200e401e4903503109128070740d2201040028141d0401c0740a010807200b00d400ca03aa034a90a11300180e49800c6840c800c1401104101d03e203c041001e0303103001864507170517000300401c840000191034002024108059549a10781d290600b1a00000c0418166103002002c004c441c81c0610b054921741800d0b400c856050303034005201940419524068812503080c503031036411402d40103035000c501d000480440c880ea41c04051144a1050648040c95a01505d80c4903406074181c070030b44000e2003902201298a62501c024030f101c14000e902d0032101e02c01c0c1c540b062010030121a64040694039003401d5071501020000d12328424422800c1c501c0d0700000249400005522401c0b039070b4000201d1401505114094900b021207140c0f007040100300910200704d022483d560300740c104640c15580c481c1c01c0901051001142f01c2c024040f40240401c1003500c9070590010400920205041c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 710813866 1250 710812616 710812639
    0xc250506060f01081303020c0d03030f140f04060902060d09030e0411070804031209050a080607090b090a17010b0402040807030b011e0e070e0604120308090a030206040b130203120702 80
    0x24032014a4402c140940042c4c11880800d922402800e40c00320064068416941c18100e0310707012603803010f140001103001940d280d0405a10440034418000ba502c3ca980c204c0205040c00704880d0400b803400f42000d84200d640300f80c54021560b17190101c405943c241c0d07505002d4086e881c107010b0422604c401c61180154204000d0035a041c0c1a502207508803a031044140741094210327121130104041c0d03240c000f4240056154041140d0752072104400062210310300800c40340c901020000d141c003885600031880c44c50148440307003842d41c900d400c0c402626403e00d03001d90507107007080c41c039405008041c0701c2c542c01078030000e400302d105103011031084152802541c102000742da036582d12620300303012010f01ca00c0009140105010f070043d102c803001c1e088406868101014484140054102d5000b0741c04210310001c044010010542c1003184a031740182c0e02c101a085010803a140030391511401040103010150000006946000c0030b10f40c1e1140e00e40190881e4030b002d111640c082d20300c1d40322010503445509440349 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 710815116 1250 710813866 710813869
    0x6030b09060402040e0c130b0409020d0c020703080a03020c01021b07150503070c02010e061c020316050c06061c060c02070911131401020f1f0b0d05060601080c25050606 74
    0x4c5404450030807080c100310b966103104202c00d0740c10000c183d2140314141c103400075516180e20003420203054001801a0380d890306010040481d03100307005420554000c08401c20205543c4001e84e801c0380c0f104e0402595800302680041c0c024450944052140c1c0078904001c002503400149800544801007002040444150070555181c0000c840c0c41c80007030b480d55554801540300f1442924400700240245003804502c5400204480c50300d410158615800310401241c6460040e4102c1c22081030300b095842c1c0f40d00c0304061178440702d000b845180a044901c1c0d510800004850000224580114007002440d0702c40900a48607003962148040035820a044540021080c10440d002d003503052006c101e8042c0380a0f100080b07401d407007622a05500500c8503c0c0c5640c0f4003840403004a840a880c01c000060907400c01030b0884840c0c5146030b00a285001c1244001440080c8098004100b424050038541c0d55500c02400d0f072207208c000440140352402ca4400f08980010f185000d01d2258081d04c1c15a0354a00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 710816366 1250 710815116 710815121
    0x210d0801032f0301052401090308032410021b0f0f0f010513030c030213050c0a08130c0305011e050603030d1a03120a090911030c160c06030b090604 65
    0x405030070152000e01a240700728038940300068808032844070102d5000e0210002e030031260103d07210120090305900000003200c005030000010042420000600c50540c0c40e1101e507400000d00181c4e5804001d0015070030410151b40d03010102e41c0092140e142c2e0703580f8540094903246a0424440113000701e42411180d4a002006800b100c880503005001c0b2a0403441004404000f8428080c1480000c01c414004116899144005940070f2041011440e1551043c41452800c03404801e001514080c288a100725a410487c0c100c09407d1420143d0b6440d468103240c042c1c48981030041c40002124000030030408190400302403100c50010b001e148071081000c0400340d500484095615400030040959014420751080701d442a1300340d1400185480d800210b480c102940c405500c0740785010800e0039031103900007501009007410900034040e01c406c00344d901a15000c0580100d140c00001f01d80d131825000244801403038642c020b2101907240d540c5110190003820140c007024050420074000403024207103030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 710817616 1250 710816366 710816369
    0x6090c240f0201090f0602090f06030a09021807090e0c040803130e150303030604150803030135190201050c060c0c0f030313030c080705010e0d030612120503070905210d0801 76
    0x40c082c17072428945540d0300e800a500c401c108640c04800b40c442ca07255502d03400c002c1e51041501c04800a0f603c03400340100010211200e0710501c060f5a01d501308501c5a90200b40074040b1038171007500c481c054a404c001070920f4003507500504018400418140300710710a82001030219040c2c4c000c0383c5626203901608c0c18007840300010480e00740d4801c1002c901d5034103159100400390a0304c400300d040600d8480305000d056074000c4c2d00c0501b1300385032031074000c1461002ea00490a141860380b4803d042110550301d00c0c2c0c841d110044074a0711074080f030082e2420369015100f203403400c0310400195a01860500094103d54000d0404c0c10000d00c100c4005c1400c42c1e00000c1201d020321b28842d014110b01940f95011a04160800c03021107480000f802103800040b001d01500c445016020060625a8080300c80101141c20a900026504600101b008045007196090801906151404542e03036500c03803000352a0030410f6032105401503e0b14558103590a00d80d61020003460000c01030390114106c05808a0340000c0a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 710818866 1250 710817616 710817623
    0x40503041d1b09010306050a080a030315030b0c0d020705100938090c031b010e15070b04032003040e0c030c03011202010c0803011d061c06090c240f020109 68
    0x1441c0035a040c410080d00030300f0740706805150109900d0340311170218100025941c071407813080e03101c003107074804054040c0612420313031030002d0006041500c0c5445a892003000035000d125251400500541c01c603900f901201c241a070403608403507140ca02e882601d80248078040c429540e07c92908600c2000090042c075143c07507900800c8145160441911001c054041c1c040c10f03281c501e10910204000039202413141840c50403155041d0440c4458138800034040195124106104521540c942c0300200f001e403080d1000c1c19049800d5104542d01c0b860243c4507051080780c68009080c0c0100c5018030200004020f00c141c1701c0440710700e01c8035101c40c3c0c5000c10900045d950004403100c20700040c42030071415081050010b00501d41806144259141c003400399200781c11a0b2003486c0031480c10310301400786104480e0000c0d0283c0c0c108100b4031140340031b400940844600100116190010714051204100101c0050031000015101081181444c022840045d130000c8022864140440d40d041340103102c3c0c450f07480c1d003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 710820116 1250 710818866 710818891
    0x906070915090303361a07080703081e01230409030f08040501090b1302240901230c0607020618030f0c160f09140c04030f0f050105040503041d 63
    0x21076a041c5c40312005440440054035038241c0c8041e410744050042c860000101c10802c00542c01c01ca09850407804105040640c20000c101500010709004210380d081a09880d000300c003030b12121307561552000c03031002010b400e2541c03000110344075010b20b9030503540e08108003c078131007025001d0920007903d1078814081c02042419296001440c01000c4840d4004e10840c00000c1c0c402c4c05a80b001d50385c100554007802140545000c0b8011814107052401180000350300d444210b180c6446030701014420401340701e04008c00d10840020b04850301c0404940084008101030b103522120040950301d070001c0392110010f00c01c1c500400d07845503091003801d42ea0880b1b50061850400f00c00030000580d8021407000d8000d00c1960740c44500c0d054041e6040010f00340e01e00485141c0351a212041c4141e840c42c0360940d0400b81c0c0c64080c0050b008400040300c00b00c0788c1c00070903500503800740e09040c804025450300141c160350034901007000304a0084014070550380c0d0400e2102c40d2881d5006249108a800c848044100c00d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 710821366 1250 710820116 710820119
    0x2010b0108041509051c020106060e0405091c031404050d1710030609020a0e040321020a05070f0201050913050a0516120b190b130e06010909020304020414090607091509 74
    0x3c2994000841c8180142c04994501d22181d09102000c114030402d5070040c0d554400034071034160f00820000d20682304a50600080c201110104c8d119038041221124014025064a2405000790420312540e040085100100c0c60141885070702c50003180c0410001500c074804081030030340c00100d4580601007100d002c141282c02d559a43e40201220724041e40e00501c00840016500d81c0d954580348603610980d80d0f0a6286a00d03407100c0002510804007000b42c3d8018007010340c04e0b0740d209080d0713003000350070021031503540070140016152480380340c1c04250030403c0020321042007852030300401d018252140c01044160381c3d2195440200e64407903d40000101e0180004058200390740020302e05c040c0c01001d8165030820307140d0700c4402072440e91080c00b010318045900c0403005a80c0d2241da0040c2000c6040229614041000030180d007a5800b809000c2ca5021022030190744556020200c400c844080911150409030f054594a400884840c030000300e80c048081001407050745450600d02c410b0321400c2016 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 710822616 1250 710821366 710821403
    0x1b0a17130c030f02130c051207020c030c19090c05030411060a14181f02100501080c090903250b100501051801020a08180a0e0402010c081c0f0c02010b010804 69
    0x4960702041a41e100c2c1c540201c0e04100c0d500c2d0310541c46c407040c3c40d4880665482d0300402c4110781240040400040d9004002c2c0903419807004186a00e82101c1201d1188452062101000d025001c0c0d800502c0e040f45040c1030281a60f400800540c0198056550800790001c410304108940c8109403011001031581118164001002e50141052a041808481d00b01d54000003041c0d150482c1c80540c1202c40a44a42d441601d4043c400384040c008160b109005030b604009015556a0b0721402d0180140c609500050460405200340e5128008001c140c6200c03201ea0b40908946600d124426100050204040741203012001d00c004120f8106840c1d680c2880d1001100c1e1800000b8801081e055008101442001910780303001402600d0b00c49044203420100c801c10700c145945180c1021010510200500016030b802c000400c40e21035102440d03590382e641c41b0201c0c800803020080b80350707402c50500000000c204516004010f0a003c40d90081000688401c01140c80742c001344c801a01e40401400d400c2000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 710823866 1250 710822616 710822633
    0x4050c0f04090209090304180605060405010f0513060e040c05030f01031e050111071b0305060604050a0902120a03020d050a0905060a0201060b1209060f0601171b0a17130c03 76
    0x210000744005918401034001c1640c070003003220700c40034503000010305101451669542c4144030100c0c10b8104445410200031510074899802003905004401c2c003c1441e4038400d004807031240160215440400e550740802812140c210303282288200c0c01d004020907038500c14030540c0d1103054050f51800241e481c5890304003001507070140c0a12030360034117100d54010070024080c80d040d00304580e400d41d07a55080c0d410151169550b100450500c102d20304001c00100340001000f58124070201d400103015190640810010030618500039041100e130181c2e034003088408503901010a00036001c3d202e400d1348a5108a85904ca0110401c0c00f18401003400d00c40c80c10f02902403e034048040c000068846d48565101009402c0070040307680100307414081054114050010f00c2d000360300c9130740c4628242065000a031512200c0000c45241a02020006c0c0d901c1031020f500640840e0100e1001d039035100200401400b844001c41490202c20404010590006003182004505600020709041c001e0642c1d03560b851 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 710825116 1250 710823866 710823889
    0x5061518070c050304090606050c0d020a24061203020309130b150c0102040504021b1006050105030a0b010c021c03030b09041a09070801020a0905030c040e0304090902040f0203180f0604050c 83
    0x296440b0910000c0380500e0b41f0300c82c41024150740c0d2105601c030340c0c13003a05c0680340146c2d00303200070301315003016a081c03000449a01c40203c40c002d261540c4018203103c580080d00a001079070091000b14007911a031000c0c550088010400c611090750f101c42500303a640700d0702c4292a204620250868841140122218840d0b0003500750043c2da9000985040e94600020b4180d030006042070a9108070301c0340e120b028481c10000c0034848144080c090007002d25103400a41140030040444d110070340c44000c481600da100d5042c54001c2640101b14041c1c140c2a00d200c40c001090218048000ca0b1803d002607c803441c0c44d20131b0501c180d6000240010061042c0c1c4509580c4401400c03001d210300c0f0f5240e02040c5071380300b800580b240000568941b0174861500c0201864405a00c002130b0003246403240300b551001010044809580c400d00340072580d1001440814007c1c141200c101c8525480402403090103101e4000b1168409503500031204661841d4240f2526488246e5006119505c0035180a00a0411408298 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 710826366 1250 710825116 710825123
    0x606040b0d0906060609050a0603050c0901210915060e090d0e012607120207020a03081804020d15060f0215430f081506090d05061518070c 61
    0x2502c0b4225503100e2043d50103603017041001c03459200d014020703130130700042800041c041442d050001e41091400ba0303640b4452100014104840048c01a13a503200071142d00340e0705000b9020401c5491079a00303048001c079074100e0802501c6402c240000a607000101c0c416405040c649014200c84800413005650300c1001d03500f894148000c42c4503911f103007540c192404180c20030744401c00400b8503242d40300800c0c000d02241070515440c81401114056103500d0403500940e58080615940d4041c0c072180854007482e149100c9501900015906500c00c0242e005000d080c654a001c00001c00e46030784c02614242911001000140d1010303880c0e0102b0b01d00c0c68682500810810201d0340c8010840410840d00700c003c058010b550721442101c1a501000d5040100380c8500c2c0345092900403044107001003c80d4406003003692052a68825145c0c02d075101b0080b544122001400324500740414a807141e280ea00071104030442601d220901c1887e41080c0c9a001c00c2d00002d500d01d8455070b40e0700c031002d5074204801c02064 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 710827616 1250 710826366 710826371
    0x27020c011404080702040605090f060d060b0a1215090305030c131d06150a090b0306030c0406032006160803130b07020705120304151209080301032003060606040b0d 72
    0xc501007401195020300a074001c0719444d944510301e0040c401500c206602580c001c10b040410886054900d0304c2d0315400c13180c02c894001002c1c14030b0038484064100b114405a10480c520000158902c000c4000700c0514840c007144070060760f20a100108a843d20072019010031402c200080a940c0070100514400d1005010142c00c10b84890358241c00b10b030b4030484109210341300400e1049078030b40f0b8161001401614185d0514010140a004001034001c0c801d0404050000c0003144503a60140203007550411301600810103140e580c10700c1c44640084403a11841d22401c12b501150900744003046412080702901e002c0b00d05c03105641d170140181d20040610b1900c2006010190020307e4501c010390007071700d4a60040034864104820044001100e44c8440600c3e0b1041200f0030941d070f42c8a50100d0303516100e007004111032140ca251324010f0000c00c01c00030f1891900000110401a0411071404500d1005841e40b1000b0008000c0c0350b6202c40540d1100e50198081c0070811070600741c0001000e0606201402 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 710828866 1250 710827616 710827631
    0xe131704080303280605100c02041d1614031c0c0b09030a030624030506130603030504060905030f0a0615030506091506030d0e1522050a27020c01 64
    0x403419500f040c2c1e40001e11901903c40c1a80034800710031158101113040000300080ca00e4400020303e022034006d0700e0018407800310103003020355581381d211452602219201003d80000c851129803540b00c07058000455881e14840411410300354980300d148114041d0040c031f05820b4107001e51038901400ea420307208005118030240300240300070501e5130007041d08000031030f140d1007110000740c259045500142803445460a00340303030044014144100011890400144a450384004110103042c1030007110341c0542486000020181e21034010011a4900e545403519152564101600c482145607c00c80c1584442e1844003c60000e500000c0c01405d45401000015560364825080c50700454080c03d039074011000c2c0c1030090b4610100b403a4054800c40180a200c02c001f02c0c042e00300e80140302c000e4080c0d03031000760000700e000b845412600218403500c03407107119502070b06040114070400d028943c0501d01400001a544011030314003540c0c400d0210150081a01c4255000000d400c241c40d400c0c0650f40711941c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 710830116 1250 710828866 710828879
    0xf121b150f09030309030f0e0112020304060216030903050105070c2402091503061813110d080d0903090501080919080708070302031b1b0607110909070501090e131704 73
    0x1c0d030b6204900c6603d0101e0703040d1490030040e1642c1c01500b01c9405102d0320b562030042c540e83c860b00e0000b14041c0c80100680700c0e00c0b1424480024000e280100c0200c4420349140414183c0000503101264404d500030b02165031411402c90f00b1661070100101001122180302100513440302c110340900c00801d0005003400a0040020b0940311020a001d403101e10000907c100c5e400c10b8180070308040e81c0a000d1000b2418200101c170a90030007110040c0c500c00c24100e103810140d03986603122441d25000b85445031504000e40b0b8100c0103003c0c1c11011008a0320800c0c00055a500540126204a00782e40c09400c5443d00c0e080243c8443c0c89040d0126103803401000740100065051029000c503d00982c000d42d102c0c0300002d100c0c0031804410b0100362082d8402640c118130780341f05840300040107600742e81d6143c6a1811b4500b2003502c8800003040780d404401c203410804a507900003000800c591b02661207405039662039230158040d020a4a03100401c00b155070301c107004952240403021540132400d882518180d81e400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 710831366 1250 710830116 710830121
    0x100212061311031e06041a09091207080a0e032a030c0d06020319290103090c0311040f180201050306032817030907050f03010f020301030f121b150f 65
    0x50314000c1d510070005144440c2d84000800320717482001520104401445020b41c0507031501766002c041d1081240030000f4401d9032092003d12400b29803c04ca4607224030480c0b42c4400540c020360001000510304001d105282d2500107070030900d03107a00610319001414485481585600c1e400c4800390141b1a030100b08169032107880390000703480e0080d100141c40f401c1090702d0480f180320301c403075035035007581006a50030030040490442c0841280c2d0001000240400200580c064201000060002110343c07800100b0301c51030042e481407030502200c0410000c1013a40700728084608078036607041c1c900207a0b9149001540944019a00403074000c08135510280b403176450072040900010a17185609000c0404020003001240d500324094808590a00398a0040c841e145d47c0c0100d840340900c62070004902c04495213081d80044081220b480b010365030396850b070415506c21084400c04039590711a503050005d0103072146202c8200c83d01c0ca42c10413a031b04c08680d1270300305082091940c010b81c4c803a61030007800c06891851 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 710832616 1250 710831366 710831371
    0x1a1f031103192f0d091514011208041511071203021e1510080318180613050a18050d0915050f0d090c0e01030510021206131103 56
    0x302201918640c61644070b100b03440c8900304039003c8400e09224641610421201d803150800f959003503540701c0040240c088003415502c407002d806000d08504144200d4081d070031103007001d012810b4840080e40d952240e0000c03a15504000750603082c0c01c3c4418802100744003030318886503216283c8140322075000300720141403e1803980301000c02021804250308068041c42402c880c0c06443d13800030941b054140c2000d032500d145540d4015242c2c440c1001a440aa58a5021001d4020542140d860f500304c0034010114403030100017240700b61840881c02c01e409811800542c8a204046c4c64080074100b11403c0f070000c1e0101504200c6456129030a034084104465843d030f0f111801078004140d00128141d009e08008169081140c9411501d0140c08201d6000402c444014007641c607026681c4801d55021802802c2c03000d002401a01d51840003c0c0720004121414180da004100399986040c40c1e103d184220f03c06c9014100c0c6000c0a4000039040b131500052142480d0031185000c901d0082404105c02568400c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 710833866 1250 710832616 710832631
    0x20f161805041b080d02060a020a1e11160e0a060501021203130501090c230109061112040603020903070b07050601170120130621020708040b04080705041a1f031103 72
    0x885d12110305c09a0410400b50424030f00320b402c61900701c00c00c0000780042500c1c1200480c0c41d040b900200d020510420210030800c03e0041581c12854850902c02e18501c420702c01c503460388a9010106192100f1481742e4001c48405070014211450001d07000101303908010244400d011204210380d011034030030b005040e0941d00c05d02148101c20f0411026940b9405403085c02d20b813124280301c2d0410a66042444003081d250035041c0943d844807003c181528215080000004651001c24000f500d1034060b000b034030780704204a094500a9448000c141c010307005403580a001a1700030710040121103000c0004403c2c06114000124510090109800610070140e24a16030740c130002a60351108144418002d003d00614a0a2041038158899138203203800e006900d14079081e4005000e00802000d28110380081008610a90b00c807a990140e4540300d919503c20350380039038200200e1021800d081000810781000090810898566400000c0700a03000b030702c4942c00b419a5410b1040013004100c0165116494 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 710835116 1250 710833866 710833873
    0x19180303080109060608160e03190b0603120304050c010503060a0b03070c230601210b010f0303170c0a0c08040825060201060e0a150e07020f161805041b08 68
    0x140603e00e608540044d80130004100d40803061042400000360322505040003450880a44807a0b0400a8244007a40000e10005015141e40c40304200780b003826148601400c40c1a1040783d1a481d41c2c5080718401154014026084090440b20b40c1d8050405140c00c11400b5000d6541035881e981d403210154016929240410b1002031403400b0031100881003404c0d035000b40101010b1045924600b43e4625060064401403107002502d220b0300c000802e00c04a406130411210481540d40d02d0196182440900040c1d0000f465000710300703000d0401440403405994589041031a00c4500c000442d048070230250704843d440c00420001896000811030140c240303034005040c4013a0300b40c51210f141d0441c002d074448420340e410400f013003060035050105a0f502c54131140010074802180710107800b00105641003c0440e100130390034044200c2d030004880c1d00002c207010403203080107240400050207102074407a60042c110030090a0311501005e412035904180b0403540e4170949280208181100d25081d00001850b51 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 710836366 1250 710835116 710835119
    0x1211030705150406031e0221060319020f030f16090608010c0507170c03040e180a020a290304050331090507050d110a090e060303191803030801 63
    0xa0140440d60003001e046502044104160a4140150103903104000a040e5034012100c0385100421100050607514003046503030b01c04843c20f022112040300b084194624081d400105181800110720a007120040d8030403842030b10780c1e82000408540800c140d60940580b40c108146950708101d29004510203943c2548428140301aa5017243d51661000308141c0c1002684150b00340c00000300c86500790400b8400752400d072781403442c0420384207081e1440381c60311001800041e00b254045150b4050820300301c0320a0024cc7e00300c801d540c0c07a503074004040d40c0142808010800c0c410b10704034810484803c1c8081c0349400035400d000741d2198008442c140c030103800000318140303010082c05400c400c40c0c260440d81c81c0036181080320180000294003541c82c02c01c1d0781e10041240b02d0f00034019192441d0710b5501c280300c040100710302e0b428260410520075002c01d03008080400c4541c185108503224000141c000c50078590105503619020450b5082c03401446100031120400c548020f04803000713036000e40c680381443d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 710837616 1250 710836366 710836369
    0x80d0203131401051608011a070203070b16060b0f0907031508010608030307020f0d0f03230403120f09020609090a0b0a0305061603020c03090d0c0b040e060307060f0207120305041211 80
    0x1a11134079031003400c01c80446e0052105001e01c0950240c480c0070664856140e48030fa102003880e106980c1c203e90000040890303010790001755682d8240045d44100f00034405120b01b0000d1101400798103a0441d804440f00b000902c500388250b10140c040d034410222580080d9507602c1a40c2111155040705509030000010411040d4041083d0180ca401140041c000001d070b1403002415440100403040070161150034550240c20401002050f003c1c0800000e9120b05240c58041c241801070a0120030042c00c051044403224424420702401caa006011705190881c18400c1080c00c240041c500c8601c19070318040c20035030303480d0081ea91001d11700c101d0040006041100240d10a5410400d46004040c0100b10f000301403040881901c110810546400760201000c0c07a1001c40000c0d10b800c02100080c0c04100000e0050134540c140c1d000318400d0f001e5035041ca440d11000c07200d905040f01c20b100503a0000b00100101d000f01a40e101d01603020f80303007603410181c540300d00203a1401401c80aa5020003484c200c0d4465 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 710838866 1250 710837616 710837641
    0x909060604060f0503061516022b11030f011b080907120204091a100f0e011d07110318190312120603050a0c06120504080d020313140105 60
    0x1000c035000c505051400c500285800d070741c159507404001000c0701140c07494881c00c450000c081c20300d03017080e600d0b00102c43c1400080c0081c603100703030b105140c03602d0320340218540294030400c0ca800f84c050100205c4c03401c1e101d4028017401c4050f029007511070b80002141c144428413565021618205071130703810350b4040c10014007411001e8410740072a0043c0340e04000c1a80c0c0c040300b01e03050b258180e030045000b40035410101541400014a800724003a40e02c2080103e0701d1558960084e1010307206c00c1d23075400340c81e07480200800100f4014052060511441550728601032141e00da4800a107240607500010401191800d54001c94400300d480380d0107008460311440d100c0b41124615241d8521801c58614640714940210000742c01241030000c1984100120a1590810307009160003004032002d460483c5407051440315030b4030510700003483d440015a070141c02402a00d01440c1c01c0300d8918100303034400000100030f40c405402f00714a00c400b10502000190540000301c1c0c0303006ca000c0001ba09162840e200da04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 710840116 1250 710838866 710838871
    0x510080303010605180607050703050f010c0e092e0617060603061f020f03040e0a060b0c071e1e080f0a0f0b0705070807140c0406120b0406020906040b0909 68
    0x2a00d4105000600005a00c41d06445400c0204514608840c103c00c0109541d44038100004e4190700031514088140f0400168001d03400303c03164001c000710050706a040329180c5880d00c0c0940c1c0500003c2c007055500708504c00c0f020300b943d03240710b1814500340761144038401105103501001c04030b990701025469180d80d410149a01540540d056843c516064000541c000d04101c11010000303144296107044031f00c2003002c90120b140420403a50340c0da444103048600c0030300403141080c14074107000020403126035210a41d04003461040042203d182800040c058034024054010003170440303000b00047e50b1010040d402c84500c05e540c1c94409260510300990f040c4a503405000800b035021100410008164108110510b80c20144100395502c440e03008488604c2107041c040c007500000f0802a0a00c01d10019811061070082d00310303104032003448140400d8607a01e1156580744010b110b440e402040d840805035900520a440c010301c4d140c40344000500c90307041504558009039000c221001641000c012158 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 710841366 1250 710840116 710840129
    0x7170c0405090303180c040903051c0902151809010312020c060f091c051c08101203030515060d140a020403080306060c0114040b1f0b030112020111100510 68
    0x1403881d1840b00d85903a0f02c0050400003e81103510301d001e0001c1801e001e9040e00900081c1700344000c8d0124180208650800f20391448080c44119401000303800070b12a1540f041d50241800b02c520451854104158001e08000819140d84a900498540e56058064040d51050402d2103c14035200c0c0001d282c40d0304441e14502030728040020500000c420780c140da085080440f0300c4401d20b01c00390000f03034500310f103132000819a1048040301010340d888a04140c9200c00250b072481420f503140040f440001d0854400ca650300f2140e940e050020a200c1d0700100d0b44081183c0c44488100950004035000d0b90103c0c221380b41c01e50b80c80c0c207088001494204a1900421004010b604040c21038888481c64400500458441c150008035104094000e42241020140814220129260a003006940c40c0c40031126060084105d60149440f42480b03451030701551341c0d482c070740340c1180e08010600c6840c06214800b80e041c000304407416603071444100054200d2000c0b083c0302190508040130190030041c400e17003001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 710842616 1250 710841366 710841371
    0x111f0e06010e0a200406090e0f0f0a0216052d0c0a06030c020a0615030c0501081e0c130f05010306050a1a0d0e0a0c050312040e0c07060e07170c04 64
    0x400c41d50580484960708403000000003da41303041c003030007512905000f503c500820311001c40c00066180d0030056900072540c00e110a107485648a41d001389402c501210200002c103010070203d580b40310190b0180ca8000010121900040820340700c251801d07080c121000c04041d1086210900903107172481007201c16076401c005107014814440000ea660145001c0c40c410159640c103109215842000100c421582014041013102e020804041044826000a441881d18010002259446036107050300c1054001040002c002240480c1c040d0000003500c5000c0807041403081034041605151103400a000c5140300e9040315141200140c107441481d84500d21071110010204210707003001611b14205480c0640d101e0351883d03444840f40041600c0756035094a481410081401c102051580001340e41c001c400329138100c0d01204d400c545230300c2203000d200300340d040200105408490180c050150640305610210340500d14010039464040aa80800003201d2658800c00501e81c007400844d5001d841a41c0a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 710843866 1250 710842616 710842619
    0x130c030e0f15041a070f08061005030f2502010506150715020c030f31080a060902060706090f0c0b0f031305011407030204140f01021c111f0e0601 64
    0x40719110aa042504040840880001000c001289000c50800c5003080920790141c20006801400981c0031303591080450241004500f0b9890304158003088007100303a5885143d40d640240e17007507169030040c2501c0c0b02011010302614400c00c803144458141a02c42e80002030303d140c40401c01600301000e800808040c20308105460200c0c084c0384c1016410080e98a0140e61507500301046071461017084820307010124003044420a00590f428621420703150280c0d48002180206040380d0460085d20401c2c00039804803071500009026078100c4c0c031030301d40000c140500346966070f21440c040d54001241105c0304002036100404001d402d03c120f40c06800481022401c05000740c0c40c0800e0340c40050f00c4045e9403040b07443c2203801c00500b50814204580d01d070982c9402820480005400b070b400c1801603034210211000860700380c0c10a041520a4140142c2c000c050040440e02100c03060096049007a00700950503041c00208002000381d2000c1080507150604207104107000b4100301e402e6071103440030a070440c200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 710845116 1250 710843866 710843893
    0x30a0905010f0513020613150309121d041806050a0b12122b060b030601110c031b0a030b090c0f03011b12020706060f210b01060c0c05130c030e 63
    0x400c403810b42e9042ea81d055444120b1003507c50718640342d030f100840d010b0024440c0500b040d0700d60071800c6402d06c60410300c0b81c072240c400d138251021021010044a0072075801c0b440911880d107504402f00b90070180700d00a548030159114441912812264075210503103811210500781000c4070603035181030341c0f01c001d0020241201016a414403034115164900c0030a801d1110050180742c43d0a010242540d10401c405681c400b0201c03d242c1003103030454003061041d40144203c900114040543e46801006401990003080140c40f4200b26203007070179000f2040c0b000100004070096200c0e8022007038071000b4030701544000e0070441810b814500c4603020364144803800d64504854400d180d516095810720503000007483e49150000d0103070450140031141440400106040b07540c4101c41924040304c40c1910792140c810380e80c19062203240c001000114868010451640304040a10030140300b80500610640e585d40003659103c0d102403200c0400780c0c2d40b89101c5406030540700e50004131000c98040d110560310300a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 710846366 1250 710845116 710845141
    0x6040308161707021b0303090d080a03061e0e07030e21160c050a0611100c0e04060e0709080c0f0909161e061e031d03030a0905010f05 59
    0xa0001c00100280640000d2250207180d9181d508100c1003a220070510301a00002d6172450740303009540b096101c2c00340743c210908000c4101c2d031503240094115065540c02d40c1c0c841e0b155511400e0f81600301680c0f03010224801a0150344c00000c1d10f03510302030700740c04d6090969102480700090b14490030715150034030901d5000c401007040340032010b210070700603074850ba8a80134862a1145c8084415001010900304040100c0442d0744410303a001950b0300302240740c0b151030556448940300c4d01040c240c1d006541c03070f00d84240150004510040d06103402d100304810500442c00307840698200010840455040000a59000b5241e400400048005040ea85d40381030128214803140c02c0c0700340c055204500002d2a04008000fa1440f005054161401965030744600c80c00e441c43e0300c0e03012034250303403560320000301e00d4070501513800706c204502041f00060048502c00d80080a46105145081d0070009000d00d0300b0b0028006103101c5c418483c008074400328145081d608445940300c0085080741b0700300512116a01e0304 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 710847616 1250 710846366 710846371
    0x200a0f05040f060506030901140a0b2805041103160e010e0f0103021201060c050d0503010e070c230f0c150702090903040801060305010f0b03011416030b06161406040308 74
    0x181c40000d004071070200200c014119503048542c00400c0041804203400701540010012503034941d000700705840d041d00381400d40740701036000d65004180d503480202040207007414046424030950b241c0f40c00d66883d408681a1403894030f0719205000084108102c00e04801c09005060600d4584100a2007445001820502c0341c00d0b08a405211007100005c21381c2d0296048480c1c0307010210103104c00d980c0da00c4005111001e20b410482c1c40c0c0c0a40c20460407240d01400c1564143c0d82e245001e412559a4104200e030420321800c020b0716011801003241c44070100d0010222004681ea40251407190494950700d850300320b50500c00d9000d08040d0040c045150140401e452070194126000009038480950302c41c5903003c0c03030300302c1051940381c0000003082040c154014220251110001c0c000007130714100301800c03a03c0c40800021003092960001b80c040b980a2540c0040146034203001495640c0400410525000055060b1241c44012916400d21030640d5200250b01e00e060300030885031505a6000340147c402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 710848866 1250 710847616 710847619
    0xa17070603051504090b0604180b01030b0402010c06090f050c01020714090709080d050904140601050a0e0301021b030705071707031511030a02090a05031c0e0f0d200a0f05 75
    0x214008100d016200c079401c02ca8000c4010030910011170745041106070313428107882440c4141c1c40c0403100080510b4484d601e80381c00341c01c44004c000702d0b0310f0b43e00d9015600c180200304904120703c503844100050b00c50320038002c505000d040c400c000e248151500e03d2500b074a0b603030b42d5030540d40081d40400044145044042a0310000e803000d48050b1205034041d110200d2580041c55140240d00100c8402580b200c013030007201c4000c45061141e070040c41010b81100005070b0b50306002071010450006e203240152480000c170030018000614011000300340e07140904074071250030f1158000203140c81c18001c042103090013400d11445002c050401010031103545052520000340310080203c0c24480b4190103500041e0340d00b140450107942d03071500301c0d40b4034000d6000c00707801c911078031560b48042220f003400614048a00544d076181008103003100d81c20348407014807c0c891030b0701502c00b901c414803580305d1f5043c64492511907020440c1c00c00f40000301140815040c40103030b0007820982c0003000b1030f0b2628882081203070030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 710850116 1250 710848866 710848871
    0x50405040515012a060e2b02010f06051c0f050618010e0f06010e1f0b2709010909080c0a030c03170601090e090f0601060f020118231507030b0a17070603 67
    0x90031032146c0e0130094103a850401c0b0fa03040b40c00c900d560707241410f034004580b05140d00030402c820714820084110b900d0350041617000000d61030192219090120079140081c000e003241c50142aaa941b0540fa001d03003100c004041400300b02c50008110801d0045e4446130040074040d010000d41010060b517100414400d00c0100c00442c408150b1100801400484803450030b0b0388103003d15207544034524a030b8400035490300500204d00c1c044440842d00400c5e082c20060050000456901c2c003248500030f046214011788014800300840740c00828104001c007002c40c4071f500c600720f0491179410060040d51443d07041408400c83d000130020345a174400a01c50036200704c814000311580b121103156103030144420f44c1e07031a907202d0a0004101103401a410744c0c05c0702c400c2c0e0f0081c441c0160301045452842100c40c0c0040541c41c01481c4a070002c0b003440046865894030307104644140c18419030140d000702c03081d43c9420100750388005040481c10604104809406910812030300d55001e94003040c3d6903c41c1d40303e40c804041c0e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 710851366 1250 710850116 710850131
    0xf06071101110601082803021209060d23160509010c030c05010c0210050c090d2d0c03020319050c040f0b030703080c150103030c06020a050405040515012a06 69
    0xc2c0224802440780c40e01a00329036540d038454030030f242d4458000c1089900f5401c0c10000c0c41c42c0172465101311002c10743c180d001d407914403c002c180e040c0c035402920300310f680031206102d04041c04005200b203500d400c10000c0710146500c04a61000034044000c3e0080d1444141c20092111094000040362034480080c60b0554268846050881c1d00c1407044070000c00a5007440c0f25981c031258000b0b62840d2103010702e4000c2041d511010001c4031540f20300c494494000c0300c0c0c1a000381c040707462920b6880c501c0545e041d00d0f2440d5044134080c00500009010202c0d01c0c041c04100902c00d50508003c1c4915111010301207005081d0380d034503642c0e070750112201c002c0d124a4850340e0301a003100f001d80080c1201031018017191500343e1039140175611504594485a44d500c01c100080014219a00310141225007503202c4540c142003030b49076400070790b00c00d03404101402001c000c0051180c440b4402c1500c6000c1001c1e22540c6400c000700010800400340380002c549000002070700c1060803005140c1610305506c082d0000d8000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 710852616 1250 710851366 710851369
    0x30203071b0f090533010804080d060803070302070f0f210606090903110a081b0c0a090c02010e070e2404020c010c090b070b04080a1112040609050f060711 68
    0xd481ea41103010344400c00c0500180a180030340116004500d0a02c010300300c1d020548075183c0f84c03443c038040500a604040c001003459409a5402c80e003040c001e00900d8501582804a0403c5d1180b0b58015102c0d64000100d14040c0340d0b0500c0454090086114150798152508100701080e204174050000c0030048240714103050301c0302088040071284c0c0300d107092002950b103248040c010045a041500452482d45c035058403d030001c1140002561711100e51807c0486040d8600303031703080e40d50104141910600814074102d03503d8200716001040c00c018045480c0600c410300a09403802e411308041c0c540d01042c024400780c803003e00c110303501c41d45800030a490180303a50803000e03040700c038024040d030024070003d205400c00106410455040c0211340700c0d0845195600004c90240c8144a000340c440364409011800041003400200000040c500d0504002c1c550920344c1802c0544802c00140066000501041389030b0300b040601c0002c00007200c1c20f030b03404200c10000c20401c5c07107800c800138100010102203646c20b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 710853866 1250 710852616 710852663
    0x1413020a09050c030615070614061201021c020c070801060e01060314090c010e04020d0f05010305121204080304020f060a0918020a02030706091a04150615020307060b0a05060d050f0108070303020307 87
    0x387c9400180c240950021401544880b082c141c507505d000d0601d503030340c06440e0304d414000c450001c03490340c0101e51310202d0f1022900003500000c2080700e450080f10800280c4100034042e420283c030f401d440e400031079403400c00041d0484203c0403881080303ea1001c10040f01100c080750000750003034207003006114143c0c181c000034005c1c441c400400c040d41e0314181c16880380078100d0307120300d041e81d2103203084408141c15104029840e00400041c9400c0a00010000e030020340b4110281d034016201401ca2002402c500c00000d80c150040b0b0b00d0040020900402001082c5c14690461a185030024045151011081c8000c0d12403107082c002524154481c8841410001c420455940a045d01c8201019030f017060302d4042c1c1d030a0850501d1909540c1400303008a0000c5c0f02c40d6075141c0040580e0020f40c5010341139510319014000304070000d40c1c0010300900015107526064003c3c500390340c8005001034146080b0703e5241c1d0003001a080780303100340d00c142d5003440003e4001007190315454000c0c090408100340505030717286 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 710855116 1250 710853866 710853877
    0xd02010e13020c2508070605090607151a0a06020a0212192a06050711010c02060d020a021203040206040b0d0b0604090902031005060307060f031413020a09050c030615 73
    0x141d074400200e045200001140710001c0c0c0c040c0c100041c04e140104a81480c00440e5400f410b291070708059020810319001c0c40c000c1c0032641e400703050642008500d03101c01d00715100c15031310000165200c04108000c8500b254041c4039030310301210035414080c00c24074000e556035401c440090044040f42521542603c003040301e02042044260200480c4895142800041d40810b441d04103000640311081c200c90f441e40d020704e00b41c1c3c1d82541c03003d0034200c4644480070880030364000b442c144480c0c45c11500168603124020100f0406905015940f0a131f050f100a00d000000300420000103c14018407005030340f8102210308803070401d10394940700c40000107c01c00421840203459070066000070001000032141e00441c50090080302650121007000000c442070750b0b011103059525400c0f07442e09211850141c104001621058900002d486102e140c3c00c2c103a01c0015111416903030030300200f032821440d14a40d1070b0043d201400e0b05004074200150382d0580382c0800f07404c552060324001c000d9030a00040400351070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 710856366 1250 710855116 710855149
    0x21209060903010615080c0313080a03020c01090809032802010e180405010c1b030e01110c1206040c1d070c14060a1e110708070c0302090a0f15050d02010e 68
    0x1213070794135801581048220040302021503000000203e4203201c202c1070301d1085484021640325584240d540360880d603c03110800e828141d0910020250780d80174464222814841c01c4005d83e80e0324030300200b610f0300c2c0d1100c58403c001204265180300050300002c0b0210aa542800c0198599492400089102d00c1e4491203440c030101030030400c014400c054012801c1e400a83d11400c81e500e0070840d155041c80151400a8040340c0c03000c81c022410f510864281c1c010781985c0040e10708034001d100018107240000c480b00300d00c81c7e114009010501500e50040001444440c03c410001d038040000103141d020010002010311007a001d138001070111260351124003520302c00aaa105107000304c000001480c14245101e101082c0360194865104144070b16000110085101401c1150030341d14400c20351b000305070454800c10f9103180040180c4402070724a0103482e8a69000c501c07108100c0428007151114244030ba500700c50208100300a403204c4007030070541030b0281f80400c2c4d0359483c0d10228240130b0030540c0340c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 710857616 1250 710856366 710856371
    0x70506030405071d07180e130c09020723010618180602031623180f031e010b0108150105071a072120030a0608150106110d02120906090301 61
    0x45050394480002e81d4031a0600340c45000300354112041d501c00c034005c140101f03021146c42101040289041d4404028443c0c401c4040c9106951905002c2c01683c01c075002c1141d521245150750344041c40100300c81c400c0c410075174000700a000d01d468825440424190001501c1e036550b8058006140d10110121040c3d0303070031142c01d55032410820700d4181001e042080713680014594102d200d00058003004201d00320501f00b03401030300744024034075802c025404480005900103220102c11485071420300c440d48484461400750f01c4000d08070b01e506802d4a1f204864031303040100305010482044c030b200c40030a020400a1034400d481d0301c05032401414880e20001c462550403141000c200f030555000c441400842c88004c2c00c1044035540758003e1080e10081d04034414002514007207448048103284c0a1940400b45500100310310380c6c0e48140d1401e10f80140038146800b040b45d401401501d82000c0030f0303000e503681d10000b032008044403d000cc1d2520709802156881c8030002640d22000d039903602c240d46005030014004c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 710858866 1250 710857616 710857649
    0xf0d050708010509060d08090118080a0f03120c170604090f050105011a07021f020a08180a080f07051e0301020d02070b130b0112140f07050114090307050603040507 72
    0x241c8168000d00c15207100c0c079441c00000e00c05040600c1c14455040e480b440c07440c10306c0310003001510410341405c0d41c036451040d070250000e030669040104688403030041c0e403001412035079420700900c0350300010b05080008ac2086000c0c0400d650040020740000c00080302c43e80d49403181400a4060b2456a8010306840c220018840c180b100651010b0f040710300408181801808007070a0403800e004000c03010350701488424000c4200010794085034441c21041c4141c4405800c44d80c1c0d202c18681000c080250780c281000c0840710f407410141d040f1006880b01030020700407041d2044030250385003458000e240c010088224502c082d85010802d1000c4500700400954554880380d08000c001c1d0450030090380e2069203034000c107940026010565211316040012070380d06a0a1212520030104000804c680444080c1d541041081d81403017400c62514000b8050131115260000040241403030170400c1800701020844490695000201c42c0c0490b4019100c407600e03517455040090508580d54030510b11072110104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 710860116 1250 710858866 710858881
    0x6030c0e060d15080d050711040207021c020108010501050c031815070609020901050105160f0f0b0717060402130504051003021c03090906031208060a030c06021509030f040501050f0d05 81
    0x682c165079001103921003c01d950341e520341d0f65800f0070081800400c01c100442000304000c080352064800340a800545060340c60f5007c100709011413040c1d00ca0f01404625440c0031580d120442c1c80c010102441c10a0400c802c0e81c3d602d5480344035140b000c48066032403580016440e111604c5000100d4205543ca03600c1d489141031500142940c0e1204034441e540c04c4001080541c011402c0d20b0003482100d40352003a141c0e481e5208901510b0340d0b881a070718230110190080019042b0b521861003202d0341d54450840421600040300c4003540940500d10950040c130001000360740f518004011207008603000314140d200c0c444410388151003900b020b0342021041280c0b8159403148900034040d24440d581c1e0107e8240e9601918088554034000208580e028008480c0080d100b0b100300e542004000b42006007595907581c40112106150b4415000f40e0000b508d07800540d4150424160301c07120342000b4520780505040c40358413a10580c0640b0f0b051203401b04100700c0b1042c4240c1035800c1c060102101300001c0c1445903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 710861366 1250 710860116 710860121
    0x1008100608011802091504092a05310b0702030114220c0b0304080301061101021e2206020607110601050306040326090c1003090203122b09050c0312030106030c0e060d 73
    0x7024514041000414050050b0882460030ba0709d1501e030b403041d0070320340640d00030881031a0001c03494004010481d549251b1204c40742d80c4000400e01200c5175a0780310440d00c1070500b5114000c1c8424514020031041156540c0e480c1c02014481c212141c107201c2034000c6240403010103030103030003581c58000003000f0441007100707000c001c605944003030302d80620925080c3c6481d8280c0c070580680500c1110300b00411403029101310058041034103103030341c19005a40801010f240d00c041c5980100010392103141886035550308081181d202d100402d020b49019070502011a0f920b84024200408100000004154207403400880040c0c0c000418020141814210340d016a19a00c5200c514071484803a620742111500a00c5800601c4d580a405055200003080c0321040640199030030150141c26600440013004501030f404220b4040c0b95030000b4164024108a850001003400260003540891b480d644050800e0703007500c0c1166a103280204a0280400707044440444081d01140c2110000c03c81e10700100054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 710862616 1250 710861366 710861381
    0x1e09150e06030304060c1b032103110c060105090705190825020d08061203130e01050409020d0f0606030c0621181e02100810060801180209150409 64
    0x840c01600da15010101910b1307100d94403804022034100d10f0440002840880941d00c08444820643c40351541c0780c40d000b000012600d0302c0d00c1c40300d410081a800250b0944269000c2250b5688040d0902100541c4541d1302c04c410700403a48a001d080b80003610f8240319a00705d8100506d982c030701d80241d030407492003d07050010a55080c0d642d18041c00c2005203024281d0900a41c4182550092110003120041075814040c003420300c542003c40030000200814040000f441c010407042d07191074800c0d140980d0180c036040c0680216108908100916001d40e40d5031000108091300130400b4107602c900c2e403406400501040c2d1004019003210040012055044820351002071070300c0d418030300c0b101c0c191903400e011114580110550030650300d00840c0402d5420044000f004100000c07000d8140c900c0d00002ca042c900084400b001412000070002240520003112000308801e007050309865060002c964810301c110700804102c1c59012030904041d07070b0307150030f22501c4260381c0d4045503403a0340368071904000d171015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 710863866 1250 710862616 710862629
    0x100810120804090f0c0507031b020603090c0f100503161115040b07030522020109090509030304120903050d03050c0d0c030e070e100e07021e1609151e0915 68
    0x406041012000391405110710100c0b40d562428502251a58152003282e240700d0710149c15440b6138a550b0060715001d0085005241c1d0f540107180b11042c40d400c00c4508007105110764000c4864510502c0748a40080540790060f815202c220070b40c001608d021190030702d01000344101446165202e80300c1c8044016130318007490080400000c00c1e655140154180c84017510401d444021802c5116149181101c030124040e20504d01505001d58900d10481551b10948500c00d5680000060004100340e43c0c11951420300c42d4104201c83c58619115140c031600c01c42402024140c1f1031001a1008400104807500710703013400c1007004680710800c8020010030400c070041c00b0b00e104100003c07542c158040c0c0450300c01c3e40d100301a0049582881c10b84081224042c10840640c4105600102c2645002050f142143c0c000b1006210091802803007072405919079210410300d80c505004010270b880546c050740c0036520880ca10031484009140720305480c15155101c2a2910302d4070040e00c0c40300c284444000d084402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 710865116 1250 710863866 710863871
    0x9050d1124031e06031c050f0403050601080c01020d170c040305010504050606010306090231050901030506190c0e0d02221d0303190b03120705010e060a060510081012080409 76
    0x1810182641c190f80c113807086540340c0d0000c555690301d184d1107003a80a4011503803910302c1c20201050b078030440d00d403c01d8204550b907400c90b03001444450f0342001500c0343c858091004008404c50400003030105800380c0c402001400035140000e0104001c881140c1c01580d000c40200018a040e090082d1205820b40354180040e041000002c1e001d2454003e880324a13466404000c4080403414550b0840d50240752100310809405400007542e50764110343e0341c0214003507405000e007031078000c0b544e81d140ea40c1c1c1782e21240818a0141c481100725845200901503503410368002c645c01d80300d030000401d04c1c5841541c0c0c0210207031410080820380c507503400c243c030007944902280c190420802251612400102c610040681042c01c020000455070341020400400c0a401c0d19204d40000341c1d00c81099101800646942c0c1d1144441260008100010f82d03115180d00400c01c222070408000030140429025044104065072000c074a4808503105040010031180c8140c0074403c58600d00751180d60031a12031181441d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 710866366 1250 710865116 710865151
    0x4150e070b0a053c180d08031b12010308090a0e0903090a150e01140d05040809180403050306040f0617160f0509010510121103100609050d112403 64
    0x90a140304800c555614031051040452400b19095a604050110513010a154011180d5920b0b551006d2400314054484243d40b032034104046540784003c000404481c400c1001150107440c07961102a041d83c0d0720046080d80c644d08080050141d465507048915800030342e105001c905c0300004010b00814070b0545110786680da464050140101040d4004408550f1018460134298461f41244418040c003040c0f041c1410402c0003c0000c9800444003112900c00c0004c42d0002441e08404007900c0d440c403281e034000c2070310b001d40c0e00a25030b0101030011400b50f600c5401a071294000d0f82c00400c06081e06050241c290b80c80c8001440d40c03000c00d450041200c031122840800d0038840301e5084030680382c010b42045280e9103000e040c0298800c4052800040140710701d80d106e60082d55000d18090480b0803e4210b440303003016280341c0d00d1501e86501105c01c1c040e03642010005500c0b40545403051300d8101c143d441c100070502001c10055480500114101c500b00300d030000c0c071f020307050020314040d0254504600c5a407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 710867616 1250 710866366 710866417
    0x3080a0e0d0807090501210203041704030302100b040e0703120c1b030201090e0c0f0a0e21060a180f03140f07120806031e010f02040e1503030304150e070b0a05 70
    0x340055011047c105e01441c0c4009507143c81a001150001d00c10501d808030402514805262604507410440040e0440c200380d00d40c40e8103078080c412900204841c1004140d0710309645640d00ca06d203201c01003a2500e54090720660701c1c004e0404410041c0c219103207421015184e40f81180200e91404100d01080d07640c50081030000b0080760051240c007070300c0c5030705140080590b101992600140c035148104aa503550030503454031450722001507008c170780020480d80c40740f00c4030040c2800001018298900d140c80310480889030418a034030303400354022003050a9842c16040071140040e252148400c40040054130908841c41c450003414143e000d00c4100b442d40341d100604462284c0140d072460340c190302035204440d40c100c9807030f80100100522000040e10f400320444a405a1b04240d01c03001c00d81d040c100c10480b00380385038600810700d8402140510b10714034041c1e4505e50b54054100c0207482d07a1740c0e00c1c1c8421a10300d41c2002a040600440e0780550b440b24507c03d00100346901925203241c600c004100c820703448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 710868866 1250 710867616 710867627
    0x1d01020306010813060f0c11150c1e090303040e0702010605100504180b03010c0e040e01050105180408090306040f1202060f1902070602040b0408070b030c0703080a0e0d0807090501 79
    0x2104141d4034240705440d0b016140d441241300f46419100c8554910060382580301d644603c042d00032103521010301100340026000d08103401e0349003443c1151020000c000480700e900c005c0b80da4126844595200002a482c40790185000d483d411a81500c00068040385060041c0c05851040105500a00c065510780080c08035502e01ca45803140882c40034402400b80300c00501c514480010040400219900b07542c00090075201c1c076031030f4803000c070b01882c00186441c10240144809181c180001b131043d1b51514010038007036401c240d42800c409035902c0c0810300f000b83d20070031990940d070000c040b9001c90805040620583c0c2000000312024080080c4190300b0034008640c0314818030200864002c283da56040a080414070881d101ca030310b81d0b080080c04000740140c0302800140c0f800c036458540784c904024001d80303451007640080e05030160a004008807082e4000844407020751529103400d19454040c640c80140c5140b655218a034050421004d121541c4003041078030034072107030341c0d4039903440d40d01c4005584 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 710870116 1250 710868866 710868871
    0x117030901080a090330060e090a0f050703050a0305030a0e0a020114030615040e0109150807060e150d0912030b06030a0903180603061a04050303090f0402040801060305011d010203 79
    0x7258181c800100001910b60000d4440d40c0a81803003103e00551030000b03090801c1e640e21b11858014551145038614800381310300005440e0a10346140c0c1802e210040607510b080b00070b002050b10200704001010040144079100007998001c08680c14580e907442c018000e41c2040307490442661401c1a011c8541c000041c9104480d43c040e124100a10700182e415002d41d40300400755500100028800140e5000e180d00400c01010403445288013035051128a4054034880c583c2001500c0c802a0144051080410190125105400c1c05c8041c1c50701031022410480100040700c0c50000040f448501c034451540060080c980300c0c840784801400340d81c5054085803408180c440d0003060070300001d90404072607403000a140c0e0003820300c2c9220808901c1441048000b603008400065207980c0e00f000042060211005001103070084181010304150110350b50b4040c510055200303500c07105050265440e15411100940300d010b00910181e512810018068424214132060f00c00c03001d00e071014018010303c01e403030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 710871366 1250 710870116 710870119
    0xd050102070506241f030f0e0f010f061403250f03060b0108060301020f070f0606080d12140402011713150b032a130b2e021b01230f0301170309 63
    0x5d44803011100e049008210f00c0400c0300c5504d0b5105280304907101e040015106206507280089554240312101c0f40545406600032922207050700c0c030a0302d066a011584d22085414031019116103202c0240c01351b98008982d11143e17251300d64a00110910030b2540000c05480020303218440c0e80c1d00d80606240c01c034440c3d61442c0129800030f0000740c00003000700344a003880307500404010030002e89481d0301609001519182d5800310301640354540b4188024010140340075030f4808521443d00c0c264002034141071040e030100304107803200d50014070580803088201856a401071002143c507035000c04e02c58000c1c0700c07003000148280f0031004103044412584440300c24510080c504200f85608410074410100b03560300885031656140d84124a0303030345420944140a50014038902102c010643c035441c0b03031000003c421300c115003051180342000b0300001100d0104140c02e18010041b0030508145c44003202d0440d280c1010007200007548817080301904d000d1760585100a04088915460074000f41e9244034100a09 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 710872616 1250 710871366 710871409
    0x10c090803040b0a030e070f05130c0e1201091401050714040506120615030f0105120d0206010e10030215040509011203022d03032a04140d05010207050624 68
    0x20f01070400100c3c00742c002115141404207200948070a03007405c01c54a40c05c42c022000b1008000c0150b49400782108003125240c510030000c681101c10010326030000e44035114096200c0000c0094058002d500182245400441082c444103005950501904003514140d0019014503620410b041c0087e017190304440c4001c0000b0b14046101036440c8a407800140700070303801141622200d02e00f905a000440c429420418a01d490758101402c100c0701a1090708440709680c400c40840b0355240d000514103046d10302044a112480da5200109a040310707094200940080078242e202c215601404094019201c0803520484940c0e2540c19000f1038186100303000c0d0040c1d00c002280d140400360403021004a8030380500110503012903d4560745154400e641654240d2034855a081520316a00038012114045509032480c20f440c0022050091b1074680d50b951045c11411889030400200354100c4141644c07000680b41c240c60881e49001e42081843d80c0000d00784201c1403000714a24004044500712201030011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 710873866 1250 710872616 710872619
    0xd090b18310b1e040908190507020114030c03060d0507090f0e0c0111060417040515090306070504050d06052d0709090903350c0414040e060606220f0503010c09080304 73
    0xb040f000c0c000040d0241d07242c00040101c0d0f80c0c4068007d4070054200d0940d110255604014400140441e60b4550301c17041d0000180141302001d030002c0100d07600300b201180c00402d0702142e4101242454440d03030150520a24008004c4030aa1039034200340c070081c000109071100f1020010042d900b0301c155088000f80394100000060004030350305181441b54036283d9046081035101c8010a1041c1c02e4441031460112001c180715084e032038104652030f4007645a180c418285403078000803500107040450b00030300702610381c80080e181c445400900b041000810303400c6540700700c00e502c07108000d50040e584080041c410107008221040c0314016a0303003059056031203611410703803100180e80b4417030441e030001d2071812100d003021110110000464041c2c01401c00c050340d20380c03900c00709101400150424074000c600300320011105180c0401c066910541c03d641e6180e45403142032144c0804161508502400c0c0020070000c160000d1800340c90060b100181e008128040b001c86003940c071400b1038464481c081d4000c210 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 710875116 1250 710873866 710873869
    0x504050106020a3903050606040c09060e04090b040b01230d030305070c12020c01020c010e060a050f19031a03060f1605070b0f06030d090b18310b1e 65
    0x100407110955840400340c3c8510b120301301300303160000c50704584c5030101c2580080c0700f4054144407503030308400c046404004d01c401d070359009405022248500c000380185441058459121508605c0c42158080d0100da0f0070302e42403400f4240d0781402e00950101c004941009000c4505d20710b00c5a410000080c0040b800700d90595080f406440024050010000e5034501d900004924020b0403414044940141041c00c501c480028682240940020b04220380001100541d13128a002c40e4a0b00c0d50b1494416603a03a2203584400a41c4038008000d2841c00e40e84955207003803a4164000b0120000c181d0030050880030640030141d0350403003a0340c000b1f4000c032a00041040364001000c2102281c0090500301e04003d06502e1311502c1c036008a038520040e0302076104008a42c038007404030141040d841e060605950782000c0e83e042440c040c0d80744000c2202800805449542d42e05030b0940d04850380b81c50000c40210714a1240d180e99503025030049803040c1403085070aa1442c0051584408412114190a145101c5030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 710876366 1250 710875116 710875133
    0x80706090915120b0f060a0302130507020102071202060603060a0501030b060904021306120b0903210705070639050f130515040e09121831060504050106020a 69
    0x8648020000403502e0000749a001c8140c0743c020705000b0420b4494a20308203007901401c0c500100041d01c0348400d0a014001039440184020420404170400a501e81e1015070680c02803062000152140c05c03d00651458194006802482400c0507020340d1700c1600c0701c0c00841c05541087c0002040310180c1c40c0060444e00302030617100c1d4001c0c001441d4090894007400200c0403218181c00071207213190440300101c20320090242c00e50700140518010761509044540c0420100700c202510f00c52034038828049030031907100d402681c40032a0808810000c0c005d00080541230074006141c00c00700010112a4050f26148406005030030907a15203c2d42d14050312107511802c01d0b444920b5051000c10204c03000700d0300d502c0c1d40205295241e0a02041ca0369903050106001828100818002e81a40880700840103040e00b8000c1d548680501e1445282c808292030020782003c06601c80c0a2280b041210618641940489010901913444104000c040e448001b07000030345c3c00902840015070305c00004480051600c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 710877616 1250 710876366 710876381
    0x1e0203010f060f0603050f100e04050a0206040f170c01140a05040b0a03020a080a0c020c060a110609030316030212060d0c0f08010903110c0f040c03020c120a090807060909 75
    0x10000680000c0c091520303021503642d6045030001081d038010921081e41c00d4841c041c0c0004644040c0e1840b45460102000d103410180268068152002c0100301000003c000d004001d40c0d0050a46071100d481d1000c1f130490a079240b08a124451801640b46d20100b0003060545403204c1c1a56000750302038090040d00b0030f0b58402c45110301007110400000174010042400790965622650740036913991100038004000c00805800600841d1410981d03046c4036030009408020b040c8240c802a031203052400b01607412500c1d0710880300c02c0b4080d010030400d080f08040300030351107540060442c00b00000d03420012000c9024040000e580c0201c1400480e015107012103c0007681440346000300b51603911014035681d44122540903146980d15a0312050070503410072004c2c0c1c0850880c800400440c90100e00150010002041c141e0080341d039003200c91425803194049031100c0550f07000701c4034441e4450ba0001800e51109400388005a01b0718070120384510b000c01e030401101c0703030342d41c0d5110841e051501020050000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 710878866 1250 710877616 710877619
    0x30509030a05011e1103010803091003020f030906010e2805150d05070e010e0c03150a15091a09031c02010902090a09050d03021c020c01061e061103071e02 68
    0x268a072220024609009864400c0f081d00f000d01c601d2030441150b0070a80d0700510420060800a00062001c0c100010a447e071540040350741c840c83c50055481030340244210103d560040e4000802c0044111b40042c520303040750900e15101d40581d441341420362035800b4004074114880800007a29603d09200e030441034000c075410140400c48020360001030050403940400b16400d800060f0304012134491103901c0c0c0d004000e40e51901115107400a010441c520006001c1d02843c1054501d4440c140c4403240e007040034000080c1c1d4071514800c003c0004d09808045c0c41001030820811140c492440c2c4104156804204060014004010721019804050343c040c01c0c2c03130007150750707a400c80000342e520303508882d002d1320511b4400108020103042080c14001a6071042e011703d0300400c45c24001240c0d000509450710790310710006803503e5001c9101409841c050b4000e400600900e11500322100c01c85c0401021160700b61240e568812190302155224010f80d9000341c0081e061598be141c0d00c80c00c114109512520 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 710880116 1250 710878866 710878873
    0xb01090509063c0d0f020105071106271915050f030106030209010f021b13060810150f03020307031205130915120803060d0f08031603062103050903 65
    0x841c01da4085034903507140b0080b010120490f80740300d02c004601400740c103500b05444415900340d0a440f64515031515490003410008005120400c0c070a07c54411801101d00500e0250394180c21500030b200c002101074400f02c07021403022105140c0c43d01050a0798010030700c280100302c907403400d044082c20101c0c2580384020700000f003002c18002941540214003070152a2801601c07101c43d0400189054010200c07801950322102406103901111029aa00300004545400919541070f00361400381003940d010058600c2000d003001c88080c1143c108414507409440590400307581c4508400c5001c0080c4000b81d01030304a81c01c28000700d0b60300042c0424143c11f40c203040d864800d80e010b104009083c990b02c260f8090382c1d24034087e10842c0c10202c901d0000e00f20340315031100420f0710340c564400c1d5100140815200b200710914034400c200700d07400e44800864200404030788914007a00c0301000400c3c48401c070343c0084c0c0b8282c00810002022401d0042e03d02d44504030401d000c410759029a4207034010070b94503a1510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 710881366 1250 710880116 710880139
    0xd030f1713110415090507020c030609010b0f09130f110d032d2705060f041a041401110c031006081606020d2601080115090b0109050906 60
    0x860140080c0508200c00c4030350070030040340c1080c0a5080502911034416424401d5008030504600b80e0035050740c00203039002440340c035000010780c600f4000340505601030103032804000b900300c81940003886d110305c1036510595040c525810009540411a0b4800355040480001e8011441c0040821145031140c6028490100344030700081e40c2c201d80c0d00c8114000b500b500c0705041003071a8000707160070b807054901e1142d0042680d8440500b030000d440800002d445440784a00e1071415181000000074070340500480e80d01c6030405044c04c0b0b40d03070003030085c810140c00200492560000b044100d40c100d503d81c84d061282000b03a500111030703a443d420204122403142c08480c44503554203018048181d01c0c0824009095841c0c0100241494050304c0f01c079650010b80081042104e4011500d45200200c0346405c2c0c0c0301080720302070b0b808000c0c4070302c01d00c41207030200800104010300154090400583c986000d4181d242d61a0794a1003610041c034403141c0000c26071401000281403102c2e029803c448010040800d14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 710882616 1250 710881366 710881397
    0x30f020304150c02010501051c020402040f080604062007030e03070f090f0e06010803040509100e07030e01051302150a020316050c090705210a15151407020d030f 71
    0x981090710280d075103020600740200150482d2003405858501c078002072200c0d600d0440002c00005541c050309240c840c0000c008800c40d40d03980d0407100902038011072516615240d0100030713600c207803c0710100d806a1030800d035504402400300403881061502c60a2518006442e07070b04541d0002c6140d0701940500c0b401201054050014460341e000d031820180004900e070710704007000b040e5005040481c1c20b0f070b0031010051000b107a001c81254103a54054604034440d0300e56210822481040d82d008007002d06007030b000c1c402ea550745038000080214192000740560340742c4110704c219003c0c0c0303140c3c020b6001003405000185034400001500494a0318015203003030500340b5420310b20b010f9400c41c04803420741103c14181040c1c81c01c01d10f0b09420522a152490800054402e601c403010041c1440040342919440021201342440d0400182d40c00c050b01c40040203552034405a40850300c00443d030010907500c2d03a11849401150055950b52500245000c1030071901c0e85040d940c0110309605102003040036420f0800e403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 710883866 1250 710882616 710882621
    0x71b080409110d09050c010905061305040e2404150506010905011101020f03010b04080d09080a080313020325091118210a0201020d0c0b0402220606110d030605150307030f 75
    0x1140250050319081202e1b0000600b202042c0d04401e1066506112440e00103411203802c4090750b10a980c0002c6244003801d010b8901150035281441d00c6500f1401da050141421114500445c41238160103840305040c0451000c0e510304072912070004030303604c01c100703d55803042160712143c074107072000185000b602a072018103541c0260070140c030300480000c04010a100030014451040700500e003400c0079034204400151110340031600901070700c50104c007080070003031203006440310558000c04070f8040d841220380003000075031600c8100c08043d6854134000341c400c04d81d005059050611700310062514283d0350a0101141c0f07404617076904040c00400b550300c6464032044503281c0104910042c6034400c0c0501c002481c001c90b4030340800030032418202c110002035001c040c8541069040380c22a04c21070600058600c0d121031000d00c01c0003241409400a495604007041c8070104903c40c1c26258500f0814805500b91052441466007000380541d40881650841c0040c44d00125685008600081e00d500710009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 710885116 1250 710883866 710883881
    0x306083004060c020a08010c0c0f020f061c0506010206070c03140c06010815090a030c141f09030e0a0e0c030c0c0d0f030c03050f0105120a02030d08071b080409110d 72
    0x4a0f491941036025072400c858203000a0031242c0092016808004c1d008148110400008200031a00b01e1901c00715501c80f06002081c0c2400751401d61550104c00040301080303003540040300c1591800d404903805510200d13400e0b1142e40c6a17251109105541d1b1b03412550b100003250980e008100a00c442808800c1c14041c440c002d2040c6002412003440b2011070074030482000d00546941d41c80031410130300003600070803540c52040c0c0081c0b502080e00070030820175041075461a21846200e40400d0440000a415404007507454040d0381c441c2100301c10b14091222a00c100e014500b40707840e0840c00650b0005450000390b52240888900c2e508010b40414210301d40003044400c48040751200000e00c904a40c144103103a0f00002030310301030000b410700b681c80c0580e21006002c0e487c0540c0c1c06603805050301d082003000380b800eaa4090304560281c9156100100003420640d8080300250f031180e03001032800280300d0800b842c19000f000092a180c0f400c03042a0047c0184c452110b20340e1414040c50780c4081c8039101c2c684 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 710886366 1250 710885116 710885129
    0x7020601030c06090e2e03080c280206070c031703072d0f09030c0b1819120c030204020c010b01140c1005060f0901030c0905070306083004 61
    0x46550440c075210141e00000d411290070048981c008014514034a04d4094000c1d250713601c5d0b104c4202e100a4640010000c240302c242004103580400400c1048490080450900c04000d0b146d078045403014000c0008002038040003100b00c0e0321860701c05841c14400900940b40b045042103007080e626a01d01840038844540e40f0442d0001104000704590403143c40c2c0e007084004d44000060081d41a0750440051103441c6207070820613045182100c10703002d41a000c02868002030103c4e00070782d07035110b00e11041d4070848051060006a11903c2405e0a19414003024107110034010422141029510201c0c0b102851041d10110403101c40003002d03843c1c900c02041d55030b01c0400040f1342c02c0c803410005001d0325510506030400003020011400c1014010503503481345c42c105440812541c64400008450600000e10300e584541690000410008581c3c2600c04540d00041c05102079550f0f02001e034201c5080e441100000d400000c140700d445502070f822113010b1084074241c80710740b0038000070f418030350b030042e41002c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 710887616 1250 710886366 710886373
    0x2150715020a0e120d031a0d0501020408010e0a0b0a0c030f0f0207050601080706050f030a020f1c23040308070c150e071a0405010f020a08030f04031d0a0515040e0702 73
    0xc01c0502d520003a8488455410303182c4003400c0c0b100380307603099039003100e20f14440400d40d80d044031000303845280c147c01c0d402c614020b1a11000482e5400d20900070343c064842c0c103072690b00c0c104450642c0080030615000640e000880d40c05642d66421640303000d0001a01c104080555a403101c040e041d0162240d1074400c50300d82c000603103480c22490414903190041c3c00038090340d403092204120712588001180c1c201008410795070b461707407608840403000e03005003001903c20b2400030440d044103486014510b9240c4010b00d030280248994008882e61038075071200072180b510120301c00103000c039014149560b0442c2407490b095054000944407407241c4800b141002c9101e40e00c1d5603440c2444c0001700301520107403c0483c686c520343e1250300031820030341c40345100d0f05040c04080d00202040310700034410060000d800148141d85d030300e000d0384c041030b00d02002c0b18200c000c20380c2e28180c08000d81044845070084100586039562190070700c0104000440b80e80c021410b103000c10000800c06006610140e0302411341a0001c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 710888866 1250 710887616 710887627
    0x15120c05040e060f1e01030e24010b1309020306030c04050c030a0e030f0d090c1701050601031b080103020f1504090203010515030f010605030402060706020a0c0c080a0305070215071502 81
    0x142c00c2c440a01404441c032810891550010355a079540d91880812406928100480ca0500040c2c000c0d0104000703581c8030340581c0b1705840c4491145d49261000081760b08981304180e813102c800740c0160040761500c00070b00c0c821b140140310180c1507500031074000500500315010f501c60900001c09590302100c64480b51000841800480e20090042c85044a0103001035420100c0840c07800e0194000e44c0c0b2849000394550f01d900090141030420900500760300b420074161a07007a12880340c081c00b82030310f800340041c0c0707000a01d0705030740d015007868208214542d43d113140a910f5034003000030205050001a500000394911a4a00c2126000400052482e140301680300c5d8940410446120504100c401c41003d04104011281e000400c4560544166090441d00c07611076001064183c02219001030000303200080191120b03401c504013080541c480c03114945c1c0030307881c0c0d40c056803504161900140422818400c902c01403030304020f40e41400e81004d48040c02c12032039880303200c00c0c544048507900b013a5900250 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 710890116 1250 710888866 710888879
    0x5030a2102010b010e0f0414070905100c230316050a1101030501031a070315260102040f140d050102041e082b0e0415050102012415120c0504 62
    0x180c80400390024002006012410000a02449a016406440781c060305101110307568465120074492512429101c200b440c0c0007034040c00c12603503070241c0c0e4460040e10309003504862003a0000f0345610703031140754540072840700304108030100603a039504842400184508014038000304140484c0d14041c400600ca00591414000d64064001245070f0400d4149401071011403a00000c0221714082c035404e541070f507903030340d07404030000d1410552200c01c00540850000366070201880c00b050035502d1000005c507031400084101d080f0300c110301c9003452841c00805c0805c405014216850f13601d10700074103d20040034003652040d089034031039000844100c2103080076049600b01c00541c50080c2100034014038904007140302c01150104000450b2400b18901024090441e21800c884450054042d00510020b04230034070090700c5000d5800b49500542c68804081900c4030203403900008004424200c11589082c0600c1e2603468006012410030701c02100c2e841900c0c3e140602c02c2c140c20036100d664250f1102c1c101728 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 710891366 1250 710890116 710890163
    0x5030d0507030e03031810050d181208072a0212010c080a200912010608010615030501140f010c0b0114040b0d0201080a0e12031e090706020c06030a0605030a 69
    0x2031283d0b00035841800081c0c1c140b10620701c1e0045100c02100e08500650b81083c080741d1600c80c1040b03d04000c1d00b00f214085c0c000c00b01a80341c00340c4903c6030b12041090802c1001c125001d507411100c1034005007a17810303092a83e50149078801d0031250421702c034003001c0d106500440c0d00c83c540c4075405940c2c1d80d91100c50300e0381c059000c11043e800c404c000905228041610031410190030380160701c03451540b400505d505241d5502d4480349070301d40c00c4c1d01c028050700d941c83e00498002e2074a4407881c01049210550400440d00c01d20840d8141e40d4215000e1101c4d0310380c0818031940c0f441c01402d00d414848184048000f003104802c0c07184c001c1075021072050900c540b070800c1c40103440c2c40e0b16407070740141481d205070f80c0180c1c1c0089801d40d004450500001342c00039400006842d00c008005414100e17040001400b0b100750000102601058000c103903120704e40c480c50310699490540348a000010381045111b1031217407400100a5422090000010038040d0700c0d0400241000844a000c40350840c0f42000c013100c4d56402c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 710892616 1250 710891366 710891387
    0x307020109080304230a0512010f110c1b03160806060a0e15040c03021306050403020a0803030c04090b0f150c0106061e1b0501020f120c03010605070204090c05030d050703 75
    0x11000d5030429145c0300b01c41c900000b04a092815030300c039a1440795450f4480310707045001460001c040d41c00500714000007500900c00f4810034190142440c2400e0040c0140e802101d0000481c4001880021148040d040040255404569040c05102600c003850046480204082c1c6400c60103081542041001c1150044503544270160b5200c20f0703010001d110398600e00c2d101c40c6240c1034401051103000947c046000348112811200200032803100030400d2588503000e00250ba109072064a21f00740c84588240c1c2d2800120f62683d440c0000700010304c00002c094115240c08207018102d400362002c94070010340d01c1041441e141d21100320105040081020900440c80100024140000401d140020681040754108840014851115450a100170303625011151712a00000211340b68070081442e901240d01209014202043d02c5e00400c900400080441c4d040f01c50949a2528040241c0d0900c400f8140020302908c10103c032000014161f14284999001d6100f036990306542d40340c1526000e001c04594 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 710893866 1250 710892616 710892629
    0x180215210c030f13080c0c09100b0f0d090609060c02011515050c03040312050406021005071205040f0b090d09080111030403210f0f060b16020f040b040e0307020109 72
    0x2800d0a01c5511510074007120b0304151418500c042a5030303940101d4070300d5040e411005125040c005000b055400012580b8800800c00710788410890b15a8220099802c1103030190020a1208000486011440000504c0f007450307040c0010607c0c0388a910754604841c5007650981d011030f12200c030240714640c20322a506e0004291703245110344500340348601070b040d02c1c0c422800c014004006084c001c5c950040041e40c00640d17001080c002e146030308860080c4140c01c01c0c86600c0152240324a200d0702e2007024061188121b00d2542e51800f410399141600010344000b038005d032540f02c4070680f14004200c8001d0080d2003031a1010050040c04040100100000006c1e800501164985103170a0641980d03281200c0c0c00507003602e0f0820b03d244c1c0c500b2001618140100041210920340b54407912a010030b5080815070f0301d0780c14001c010b0941e486841400a108410a00d000321a0031000035005240180c6a0494690060000203040030120003040071075100c80c24420130385d800458050f04640c0e07c0900c02d405084c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 710895116 1250 710893866 710893927
    0x103020406050d1a070e1201060501090e010321050c191506050a0b030603032503080c040b0304240609060f270903140301030311070e01120204180215 66
    0x8544885031a42d01c092208a0301c1d000000228a1852151280b65460740e03001f4085601403050350940d80c02000b0900c50b40d80070424100c00020b5042202030b02904a0780c00001c0303d0480300142111180e96280301c410071040c00b0701800620740d594410404c40d54032500202552030006060b0410410502100205800702800e0040a03c0340c1c0e12142911001c9944050030b0b55103a44401c4002421070281c49c1304200d11b28000081c041d0501d000c0b140108a960180d2159802512244681c080074451401110800d0508202040000d60b502c254607480a81c5170740d1b142e00e044042100282a18030941c408007405450b00018401030411305242c1307000b400030f0280141d18043c12520200d500030f421215040341031381c0d49041020300d8001d402c000c2400030500d851030303a29a1603150240001c1c03480d800e90401885151800305008070880304040c10781e6235500c1c0c0b90950406d20390812000d400740b0182e10b180d05440390440d10042e01c4001421070101f0700c6c6c0792403d4a03000419042c40d10820092440b01d0781f40d6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 710896366 1250 710895116 710895139
    0x204080607020c04150e0c0405150a0305090307110f0102120307020304080c040501120320061602010c1106131b090c0f020109080d2f0a030c0503090d080912040608010302040605 78
    0x1070114120138100c4240c11201041541c03607281c0c1f181030340665400240c0041240080600c040c42c004028041c0c0c2600d501d0400154a40310646c907542c3c01444001400c00c482004d030480746240c03020f50300b548048148102d0380d5070340100c07101d00090703002641c0c0200035038404207050000d0036003030043c0589100300340c40412481d0700d81521086046e05c980005401e10149544070350442c1c100180040895061000b10b03030700390824508000b2111407107440080103519203000c0a445910079102a45c01c41a20740090a09032905000c2c070110300003c00c01125003400c003070128020300780c81c60000740c0200281c400c0050049141d0ba00a400024800c0c0c601e021645400c0c0100009804442940c0341551800da000400881541e1058201d000704544100d0b400481c5884e8050040010014204080c544d40c06102c1e0404d0110b05517024001500c100d0116001444204100e80c41105c4a0380c3c0242c4500884804420f015100c030000e134050381010000903142e138018410344c1005c0c060500100310903905113041300c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 710897616 1250 710896366 710896391
    0x307090905120a021006060e12030703090510020a050613060501290a090e040b0105041a01020c060a0201060e070f080112030c0b06010302040f0f05040e060c0406030e100204080607020c04 82
    0x141864a1054801000400c00f14a01442001038006140207484204400c685070b0b440640b4a401160301148156889811108020401300c280c6144540c1601c969821504001c100000d102018030944110b103d0380344440040b520410401d070081594102144400e0071f281000700a41c0c2058102c140c1003c41000390417584a440b09005a034070041c3d81d1181e0712240c858104965a5051b64841012000740c102808217221441c01480d0480b18100c07410000d2901460960f26100440043c050242e04004c0b10f421f20703401c107131008100344c1000303100008400c1d03202d9a0118170198144c5042000600c9040030b511081e403c040c000b4090300c00e903820908915a60364000301883c2d0b44820003003100504001148071a40690161005404480350300040c89442c1ca0308031026003058851907104504000e2461007145011035050f001e41405d0401d1072509003492801d4016050104100354248103449c09201d007a165803014001408140c00a04050306105400900d000205044588240d24090b450702d440c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 710898866 1250 710897616 710897623
    0xa0f0f1b0f0c030f0210020d1d16030809030309060712030c1b0227180c0603220c0905100326031f09020a0503060109170303010302121e0c0307090905 66
    0x25268545040310300d0418041303089041c4085885240c1e50319001081e40c0c2d10014030707904041150001caa03403441484008410640e512510600e0300250740b13841c1802400403401201c0142400385018048078034002590011070060361000d401a12840100030b10105269814021031145003650f00e040d80485040d101c5200941e0b0103801d00a12641e8019806502c41c252159240042c000c2000f80e280c152070070380180039551300a03c1d50403905000314441c0344450303e07240050340d004d40294910340c120000d54011040c0d1401ca00e5400343c0350b4100030840012050302500943e44111144005410010720f589440001e910340f400034460000c0d408030120035408100300640783e00c155002050b46c041544100e00c0000c4c1d210a4001300d0f039060000461451003608040150b025200c203036500e41d0400e070b807140c0b2a8090702608219281c940c008000400c09450042080b0b00c1e08050031040c0d4400c0c4031400b02c809009640a00f02e0f5214ac0c00802c0c2c0d14a6620b400c0c0560310060880c404240491042c50f59038688 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 710900116 1250 710898866 710898887
    0x50306010e04140c0310080114150307090c05040e070804020d200303040312090f080a380a050c070203072303030a0306090f230a0f0f1b0f 61
    0x42080181110356503a50365000089078242d22100520305041c807424002e213130b0b441191807080d10900b05500141390807052003003500303064020f040c486041c0c0f42d51420561100b1110011070b071502c0388807008210441c461041301c258581c80d840c2c040d95645401800c0c440c03448010150f40900c90314100b00409a298400041e1400703911845000b0701c0d03100c0c1da0760a0074481001c01e400c0d400d80b10110b8080200100a8680c2d41c00c80125154a0340c0300c1c1e40d43e080c1296240340c1d4011440d80e500807400240002d0391050744481458000710703440c01210a2802094844000101409013405031002482030841040c0b203150340000a07580094989030058001c2540c030710b594414408040c0c06040701c0b07440c41d102444c44054190380201520303507032032100000502402003030040080107842c001203d150703c0d1461082401c40b0390411161030a5088203101c131911480000c0a0701801a1100026625501a80b08102c0d12003280b800c0041d0301080c900078a41c03296192105a02804000d01d841c481042d0008165407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 710901366 1250 710900116 710900119
    0xe010f0e090a24090803091606050a1103040504020f1309060f120606051804031d0a0e06010e031e01060e01080712050a0f0b090c0102070b03130609020a030506180d050306 75
    0x614542442601090500b555050a01070515002e4100b0400c12500f00850052095100322345c80c248114054a459507014462280410b10401c9156143e03406120500c1f0300141140c10340741400c0c1e03681c0104081e644600380d0600c0c000c03400242060116a523003025405046c1d06a0200900d0b070030700c928414075a010740511040110f103001140100102078000c42d000d0715000e0141800c1c100340711140c1c013012400b554101d010540e10200c07500101d04159001d000500c00034145180e0910f04040b10003d20700c0981140e0400998074140305242d1400c012000204001000240400e03140c03000240c02c607511508111380160265004200b1000009458020368100d0041054041c0c01450003924188012000504a2205242d004c007482498106948104040c1080ea1041c0030358000490b155200750007124030f0204c080c00070402200d20703025042841c40c401c5c180003a0b00b00503600000c1244a041e8007c0b101d0b544620300700409100040d41c2c030f49412610b0310082000b1903958102030301c240001807109 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 710902616 1250 710901366 710901383
    0xd0515060f0c0c190806070507020f0405060409240b1e0114130f030c08010203070801090c0c02220b0a0803220b030709080607020f0705060c160e010f0e090a 69
    0x50300c40d90010710071500e41082c010440d558010340407810300c460042c28825070001b401001c0005449074001c5c1c0031030350560790050025160a0b41281048001c0c100035010300c0d00283e0314035040b000601c00c08a9482802c41c00e2901421000a2423980001d4402070790582e4003030300390710140c03000c0c2d5401e100b0141d440500c242070007680c200c6410140344031401482605d0f0880750f1090f10000700000c82000c4801664091a035102010762a603c111f4281d01c42518181c001882900040241c24847c2d4070110040000b8908000c2220b0a42c000500154403000608040d906012482c86101c02c9403241040c100da0a884181005180c840c01075101d00805840110901502c4001201c40910025020141c5010b00110b84c40e030800184c01010141580103030101441010f010541081c000164440441a810000e004503800c010034070419170803000301e01e14203200c2d02c1310f03440c042c140c19840480036080790040800700d5071419604401c10301240c1d00400010002105005514101003155680e03240c0040d0344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 710903866 1250 710902616 710902627
    0x9030305030c0c0c1306030204051003210224012102060301090c05071a0702070b0c0c01120b06210703050c121b04081006080d0c02091008120d0515060f 67
    0x43c2c18400040b00440e80655221782e005030243c01c0c3e90010007542d00966003040155500001c411a0740f20324000541924118041c96006500c0040a0501c0c0050351040d00c04110000e490420604c00e00d01401403034040401c010300c031303080181d03409101d88038580c80c0c1541e506806030040703607903440103000c0c4c004540c0c0c03141c410b101c181c1d005200703c65800313600441841000c4e1402c6140501e1400c1903e40c10014001c07680d0004d00307101c4010658070010110070240c015048000015141c2c2e50911603115212500c070015100e00f5a0344101900345000c0d105100b28103021280038980384844020300d10803d03d440c003014000441c030460245c80104200c405011807980b144001c2ca80003205201c1c034030b4090100004e02141100b40411171034040c83c4101e0060010039240c076240303503c1c0d4484803108000035021100c1000985400d8124a4000082da148110039a445144d628100030748a40448003120001690801045041c426150301c80c040441007681c2c0015400010344600c103081160540e40d502240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 710905116 1250 710903866 710903887
    0x50f07060f05031f091d011e020a030f3b030702040902060c1b0324131509050307200f210f010c030b0114090d0614040b1609030305030c 60
    0x1840d013250f074262107580020326174442d01c0a003e0021004000c03101c1c54000d00b001d40c442d005002c0c20006030303901150319070183d500424100082d040441c45000705502d03100101541c0049108800c014a0382c04c1c0102c0003528110340140c01010403680b0520046200320b1050780c0000c020054a0701c20b68110307000702d80d000e42c44c00010218018031600070000d00403180059a000c039451100040b0031000e0b800e0b078050404000e1034021b03000c01104040251022800040d12420010b54120702c01407141c000e140b919503030020b802c0e085a50000041303c1c65400040c4403402d116601038003504001c9402e2128100e107000d0008580b000002c40c84d42401130300c801203100c9600410f49061481c503d06141141d0f030700c2c290407202070f028003060144800400d00d807800708060f03544a820742c11412002ca0f1010351420a442c0244120054401c40c19100d40d90b039802000500b0b500248868003590013100e03445480e00304078010005100d00300d02071310f0511a44000402c0029040416250301c0b1660801d015190002d405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 710906366 1250 710905116 710905141
    0x3070f060b2704031e02100c03060b0406030b030c09090a14010f180b0c04061b020411070f1406090a0605130c17010c172e060c050f07060f0503 63
    0xa01c000c1c280390360140c04a00c40b4800914880c900950b00c0311122040c040006124141d52100200140c002c82056400042e441e000351010110a2500062107a80e030b1100c4212070304103400c03c40010f84c450b01500d0161800300302c11318551f601201c21b0340c0c550601181d07203682d8810000c8000c01c043c140d4070640d0361a580030b45c049003001007030310028001c41140c1881c5800d40000400304841004540300840c0042035084280c8050358416103a50a1511590785082d00840d0010000c90b4040e48640e9501d805890520142c0031070b91007100a4144161039207010300600078039107040c501f40e134000c0f410007440e1140040c41d040a02d8000700d0002d2242c607103202c04500d020030120003600c1c00b031400f100003c29004401c51a00900102d40007000113003a15a0115148105090f012103000465804108925600c95002c401c1002e6a41d07402d088103001100026105015400140800d031400c4982040c03240074407429030140c070000c000d05035040c10044080c00321240c040604080000c00b0001581c00c60b1040d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 710907616 1250 710906366 710906389
    0xc020a020a121406060319110604180c18060f05040b120106080f0631050c0301090f02040b030c031801020f0d0b01020d0c151e09020f0303070f060b 65
    0x9428486140e865a2542c81c109000c2041107880e004000118074058002103800ba0103288000c4c06807101c807040d94104580307002020400d65184c1c0d51440500c0b0281d070307064004c1005000031404403090000d03500404046465812407401444074003400f00010350000340c09201581c5e40c41c106180701641c0100c2c00c441c540100d8105400b05180010f21030000b00c1c0b2900e4043c12100715699090031503581006040100c1000e4a181d03810214054101c44900200c101c0400c0045001d0001400080703469821b0055072402e0302d100b0850a0000018000f000c55401840300c40190284250728007890140100d003240b00041900c03041100110201d5a001808028040000f40070002075440b103408607000ca1003640040d02005d4001c0c81d107584908154000f080b00c81e000d01168645413503018254498000f020120001030800640d254102c42c1103800300700d81c10352010081c541c0042d00c80054418040071170100d8890764032a600600c072040004a101c828041c81e250304c610085803103c1128041000b00f02d02 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 710908866 1250 710907616 710907619
    0x5220620040905060411070503040306051902120916080c060901090b0d1e0b130b040209030d0806030607020616052805070c0b0a051210030804060f02011506120c020a02 74
    0x4001605803a9500028004d2100b02c1d0200501e550b4092441c1d090301c202400181950000d103c1007012a0299001c1036110521103041154201e4a44c40141240d0114802150004401d4180043c082080141002c03201e10704502e9103400d41044a4190341d8880104080d100303220004038400e0036440340c41c603000104800300c40c16488444040c0d03290042c003c0f40382c14004a00034244000d150541314001c4202611019110204100319640c0c2c40010380300d140c805907000ba13020000c002142d201044504514446aa02c221b06401e22400301802c10310040d01d01d6003198050424411040300c1904c1c00542e26600742030070750342c2c0c101d01b051f000c10544100d480719016414904e0020700d42074020000382030903813007045440390031354648041e13043c240a9441c20300c002413401e10103004c08409460b10b660b0000710103048941415980e03a03a19849a0040c0c0203e0000b550210502c480c40c5d030240104103f0000a0b034881ea83c09041036801030a051001c092620200d44424200c0d240d603001740080d8090940 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 710910116 1250 710908866 710908931
    0x9020a031b1418091905063405090f0303371403180102040612180510090204090c08010c02060906060d06020f16060606020d0302030c0d0b01050418060306052206 71
    0x141801d00340d48807070084488c0c101c885000c152681c0103844211405071550040459140284000074046589030030a809007038000c8000803101501c3c0d0340c00c2000d020a41c0e4891040c0c402c0b2002e01c5071029602751840440d0700180e1010500e10389650700103006c103c01082500e0000d072207913030755001782481003d510401e50640d44001000718100f940034445c00c002060880c418003c007040a988840404440403010f0040d80256101c0c400314001e03030304080f51840c00103001141842c0c42d44c803000e00b002c1d01940014010382d91842c0102c101d54040c41b4503640807210f140030306a685040340119105404120005003038980c0019450500d0124009861822070090305414090320346241490040c0058042c0c4409441800700c0c240000b8400d008032441015801ca0407403e2048003002940586102c500305814010148000709104c004c109510b81c031855400f8000c650580340d8140780302102e01c0505247c003228281d03c6122161000514001983d650180d80040d105800314040d0400000000c1c04444448 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 710911366 1250 710910116 710910163
    0x30417070807030309292701060803040e0603070305030901052a0a0201092126030f040b0a0b220b0d030c0b0709121509020a031b141809 60
    0x1545a8481c4032021312604a03000006e824031010b0035844040342c0800e541d5015540001c02e900c401800312034864078029079100c058040c10180c2820340e10190001d0035182d0002c181048803a03c800041900401c060b070182103960b003103440d04d03901ca10907011481d06000d00081c4204c010540c4491040c2c80a01500300b50059000582c04262925406c0c1030681c00a04218008034a50011241500c410044054040d410003080e5440031701380540d0500842810201c40a49078103c0644c3c1c00442c4130f6109004a02d1072440c1a24145085001c003130a03403081e280c42c110343e07254940caaa14000b10300c8490340079666030035015a80c04501070300602008580091840035080101070300142d513101158415200f41a5a03902c880048032000c005125240d581e503884076002c4045011200301c90b2806da1580c078085140c403116008100b220280b80d00c11100201c454040c50892620841e111010781038018202c1c0b090303004040016908419440000528840d81d4041115000704211060f01020301051102030b20f0f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 710912616 1250 710911366 710911373
    0x6010f0504090209210a031e200a062406020a02090c032703070c0504150302011809050c07050d080105010509210a0302032d040e070e030f0c01030f0b0303030417070807 74
    0x100308206c0110301160b20141d04800082c3c3c1048800501001644e0303c13034281c0d1603401000ca00b201c521000d01101d00403051048042102c0303018000c01c440511089034440c1400240c010740a079010b0380b0000031074000692800c0144c3c0d90b04043e40c0c1100000401036126160007600c0d2002071904040524881075003040155228804409400214003405102501c0d43d954400c1c4010707240e01d10040817804e05002410f00056018079001c400c2c0400c0325841c04070b030356214103200040750700546080d80b0708030002c64844200401004042c038080c81c913291803525035143c080041c219001d0011900d11807901d03078821f01d4500140e070b60044d8840c1c4c0941c040342c005401b1410082d4413640301e01402541c52011801010106962a40032480f90703030341182c4945418a4440880d11424018044000300b040d1010407a45641e001c0024860308107140c030103000c0c07541d14440050111041841c580000314108108020603603004000c0d02d40c0710740c0000e000c002000d44ca0b1001d9a036841003d40c001c03c408000702d8640e051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 710913866 1250 710912616 710912623
    0x203010e0d230f0304030311070b070207090501080c030a02060f0d0f0b040b030a0f0b100803031014030c01091712040902030f13211e1706010f050409020921 69
    0xc84650390704061115111000000e1107200b460154003c400c001140c0000c0c440da01c00041645190b41642c00d2000a03554403500e2001583c944005a100f94024086440b5a01c50342c1d006003008001016088201d03400300ea101d860001c0003030702c40d41011032118509030341d1008540080080c403104005100e280f100100c000e002038803a06000390318001040000e400c4c0011560fa2032900005c0e2051415000e9661184005004103c02203c034048100058a030300100040d5009080c840c0243c40f019090840a0080004c629801e901c0317640700c0394941010f0790300940d021050b660b1401c0780d00e030703500c00c0103126500d81600111440d02400001500103686401c5502560041c4480c41640b181d94841c00c483c551310200e807150107042c1455030440b5005114030038400c00c241890703030304100d05850809400703d411414942d2160020a422094021645550281547d8001b00c02d082c210f4030316016140090441c0218002d01e01c4080e070004050740e407980d60b070917000783c0300354858691680e6074201c203c0a0348 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 710915116 1250 710913866 710913887
    0x30c090423101406090c03060402070b0406020a032a0c0c1203260717070c0506090c09090d0c1401020c01020406050a0f0908190213022803050c03130203010e0d 70
    0x1294075141d1114055a040401103000b004c0081003180c503038581e2110f1484603403024220340c2e4800e0b1308000d040001901014034900c69809140c006840740000300010742907801070030141450903010001055424400200e1415040a40c9440f14680941c0c1c0f0b070240d10061240c215000c04611520550205070b40694640e07441e091102d0094004884203145802e00321054840070085885040d4024800c0c085a4075164000380d14038180504601c5a100d85040200948540c0c010303801c015200c01d610305000c0b503130f0350308110100000c0c1150400640000c001c1c04000c18010b0a5000d80801d84000711402d4040d0340d01441600005c654859507204040d0160b0303c54040c44010520072031104408501560340700003103903000006001519040b4001b89080c1401c010200c1e48041c0740b4010881084040c405403541e400b5400302d9404560f0600180d02101000070004410141000d0801010702d0806003600d810001c0c0081c1040c2da02c00503c0003d01410300b00f800c8950610846c00d03216810b0760b00c183c1910 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 710916366 1250 710915116 710915143
    0x1b0403020a120210031509020a0c022d01021f2a030615020d0c0321020d0c230d050402060c0a110f0109080a080703050906030a020406030c0e030c090423 67
    0x7001301c14110819402d5a8402d481d104c164010140f0800400083d41c0040c0381c100e0031490700040e00002940015001c50b0100c0403c01180302804c02c0c01c030701c0301c110b18900c0440002400188071641d89420300c3e0749860b102100064241e0303110500303414504513014515019100048054544244854004004200b14403a410401484da03402410007400800c900304500602c0d0f4800c5065501601c0a03205422503a4000c3e40c5c6100c154003100325500203101500240c4049507000c50701c074440c5540182080c1c80511041c1c5501405014000036207142d2007121200f0311030b04400304995445000282150181010f11142c50007165580000c00100100e0f582d821030f800c9034001e10703410044004640c0c5002600075403a141d0b11803c1da00c03012826910242018500c030f881e0a038540020031001c218160401d4924814890300428144110f036017500610403203080340c1c50400d41c5c550080307000a507502a54000cbe40e001c2c03100c0030041014441401101540d0360042140c0b00d5081c641001080c1d44c0c1c040481010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 710917616 1250 710916366 710916379
    0x50d1e0b09100609061404051005030714090606040f030b040f080a080f0702030a0f0806030c0607080a17060f0402091810051203071109130c060309060e0105040b1b0403020a1202 78
    0x81a0701d00f080c82000140e0381914800030901d100c8001f84002080060040b9024001c038060000c0c05075000c120b14005080c01051640000018500384110300c0700103802c252044500380024040d00140708100c5044036004400d116464813a401c080c40e07924103425002e401104002110741d03501ea04001128080d140c840000181a070310303410102c1e207a008400408000418052030841e20307a114141458204000a0036241c000368541c0c002035245e440305908880459012034003224568115070f04400003003003c80f40500b545400000a1440d0400c2443c582c1715560200d03102d20280c0310741c0c0013a404e401c0b51740320580341c50522003030b0402d5000c5035118a074442d0541c141c805405080100c19903040e1607009070005a401c49800c10000c02400050140030114008608070010a550030321040c01094103031000503200006e8100b1038241d4601cbc40f085034a82e818034050000042c1240e15456100301e9100b0001e0038403004505842d00b42c4140d81c4082c4d4001804040403501c440030031042c003010303072007100c21 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 710918866 1250 710917616 710917619
    0x60b090a0605130c0e130e0709051b0304110405130204090b0912071101110319120605013608030c0d2c0609121c030f06050d1e0b091006 60
    0x41400e0300e084c07011000000f0900f146030312150805110042d0b103008000c9000c1018025015000c0c81c000d40c0e03910228a20ba150f0042c40b0021403c6081040d5040c1c05482c02861407406442d51450011403c0f0803601642d03071400000c85401c006041c07070015680c000d1050024181a0510461080d820f039002035090217003e003408616100d40007280c49442c2d1001801e07941c0002c0700300642e101d44078401c0207003803800704001d00198000c0e001d40d00c207441681611907410301400d1000b00380c22904c90b0307000b42e03051291b81140d5030502e00c82416110742d80d000b200d05003e984200202d1807003d0f0710456012404610000c10710b440204000300d2545c083c030046945085045040140c405001c407080d2058a16103c4d1404070761110f4180480205801d01010f0b0801002541e101d0324246889595182090320040310710341904d41e0343d803501900000d1403144205002c09401c00c000250200003401e8000e0a1070703000e40041032030000f4000000341c070580280c400368841c0740155809449000c500b0700201c005c0d01d420740 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 710920116 1250 710918866 710918899
    0x41208010909030e040207020406030203030a05040311060c0604300504031b05091b12040f0b0a0c0210050a060308070305030103110306010e010302060a0903020301050c07022e0c060b090a0605 84
    0x74810400f81c2690b44c0f8840c034005401807100a510500c4181d800c00d89074071001c40941c804200034215190b003030f0b58540d0348514504008500c03c2500070b040e4442d6108206034981c4400000d100c5820980100d180800007003121600200c2c410340350034416024803003904401509401001510460780215401d50a0190300c01e010901d552103801130942c001760920104500714a02405003d4485140d62260326044410f102e82100c0300d02110101c400c04002035a00003002004001c95802c454045001e000300008148080d4450721840b0074085030644e9a0001449043c45400c1040116081901c0603aa5600e60038020810341c803d0000ba05c1480c64004542c22509002174240d0403124802d0141c900c40c0d0031035003080304560007441210100b011030074001c00540d03400c1c0b1403a406071440c13140041c2d450441d0b1041c00551075008100080447d0a04002c035002e811049006502d0300d154500303101e00101525242c0c00034070b00300303880300c2d041031001081200310046580303c241600c008949844503007a0004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 710921366 1250 710920116 710920121
    0x21501030f0f08070b040f020f0118060e01090302330415050d1401060f171b090112060f061205100605090a0902030901051623071a0412080109 63
    0x20004000c50715a11059011035159000444400e20030701200c3d28204036521220151075060b5400d5030102c14007800d4104628004605291444c0d003800c048002e940000d202042ca4600c51040c00c080c0034081c01e40155aa102c1c1400c2400756600902c540000620348142181c100b078840184102407a844038000e0a2200203015101104d110504420b0117414620f4126159000349088400480c2c488241c850b000d01c03e000030901038000c0340c0c0c0d19034030642e01100c02020109070480140724800054148508003040c0d2500d0718104c8414040d160b0360351600d2004a8008005040015105150510228542011100e81e070212030b040e6680b590a6240d0000c036804440b4151180c046192420400b044200c0c00741001d40310402004250030907099407440c11070240c1c3d2046403100c0499540e80c3c20040c410f40140c0301c0b04100500b0380303883d038202020703004440689015a4404003410601251761801c0020b4240c031840c02078801c01c3c800c99203050a1425426080444920304007084140b0f0020590b1811803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 710922616 1250 710921366 710921369
    0x50309151303030518040c03050712021303020607030c05060405010c080106090b0d051b1c06080d020d110c04090312050109020f090f030708150f0609071e031b050a021501 75
    0x1056100000d5140d543c05071010351084444108411010482e842950384901c42c0d085e0503c0d040c0c41c0840c0030301e08980d0050599400c2c0301d001c0300403031040c4802580b400c910900f01e03042c2d81c0d042d076640d5545d069509090359500c0840070018814407842c0200003c200040d000f245002c1705079222020a40d1300d4072410380d0070b04554091b41700c1c000780078060740c0940c280c560440d0350054071811008000800c800703418565540080315003100c40c550090b030712084206d90700c0780c3d000404000c0050810a008400025100d00844285008124403050858684e5006000c00444124010000c03c1096030500c0d01400c0381d0001c00d120140ca51811000140b41419802119802d8003110440e5203400c1c0b5880030815001d0003441c01e03070b0b010f1040d0f50700841d003480d04220108050700a04145401480e11080042e00c000f00109807600038880c1400340007030503030000c0070102205000310055568401c40302c011801491000c000d044260364100480603420307000401008801d00650030390751141902400404c090400707 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 710923866 1250 710922616 710922637
    0x606060a0807031d06070f08060a050d03080c0d0f0603020f0301050f180a0b010602031c11250b0708061e0906010f0504180c09060314010e0c041205030915 68
    0x4071400249124031a0740810003221044120942c450142e0340700510f486002c0b2285d40101e600314010340e079240d4000d4140c07a0300c100d04450000b401c602300300210f2001c2d52981d90040610424002140100c642401514011115040e0800490130041c5510b409006140300c1607024160301b844c140f445c1d0506018403445003e1844c4441c003540c0b04c025840c00042102a01c0c1402805101e554800107942414001e008204590041d5281d0504003a840060304050102035202e0303140000f00d04002c01ca0109a0b4400000c100416040311040c0c1800d04212042c001b0007090704029100f00003800d6049628203001c0e0006544040010f06070f04c5c0f400e040c510303c50313152540c4880000c0c00150598451804040030f0f0035680380c698100382c0d0fa00304614200c2e500b50208000103071a80d00a0326140c2e4060804402041549014070a0b1500044290f161100c1070091034030005428001484000342c3c40c04171030041100f1419914804101c3c00c00c25213a4000c50b021178440c5070809030705041c2d5494502a076010140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 710925116 1250 710923866 710923877
    0xf02070303050f040f03051e0d270c05150f0c0a1e0c09020a2c011409060711040b0613030c0503120d0905070f0b0c06010503031e03190207140606060a 66
    0x3601c2c10f65481d0004449241c0c0c5001c0e0711960500723881d012001c1c080d407071003d10001c25a041c4100307100003000340800303804ca0b40a82c420414004a5000c105000c00c07100e00b56135003481024007140c3c180781031191466042c0d410f1000218818820310005034001c1650042e00c243e000701642246160110300b9210001d0b1003242403450500080c0c00c20341c02410085540d04243d090031110102081c904485035181c0561004082e403250441d5030494101120103410982046c505003001001071540c1c010494060603e440c45012a11b590701d0ba03521816039400c1c01002c194480095509464aa0500d03010403140e1030102000014107060000740aa030b00e14040c200141000c0d15251408010005010b0036107461240c01d000040500e08025800d02803c0e00050380c607038a500010000345001d806a00980c000c2d80204100c826915003070301c00083c141082d03804269282c44034003c004038000580809000380c0e20000c2c0c031108000398480c6400740900c200050780c050740d58034000c01419010704164000071a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 710926366 1250 710925116 710925143
    0x106180203060406080a05100c051204030c23030c010e01060503060f1e040308090d090612330f060c0c090f020c0a0b150603040f03080c0d0f02070303050f04 69
    0x10603005154000c2000e0710001d4010765980070345140c048220425540d907000200071021420b130350300036a1803035489d81c05c0461074812207840c1c2c643c909200410140401c1644100e040404c074a46d048140119680c0403030703171080050503184e50307145d900000e4409240c1d031030500c00508668040c011103040300d00c01400b4280790f0ba5a212071408221000f03100c03041500d084101d551120407000300c1203000b140240e88000c2207103840307501c6900c0c100d9818198000e0240c00310302002a42d902c20740ca558031500c21003001c60ba4084922242040500740c1c5251040c010b4101e0000941002182d200401c40308203607002000b00356030b01070642d42640301c08400740c028081c0b0b0302c0600c04e008141c3c20a0700105103840c801450301070000101070420207a800d044602e1000300d01400718071460102d070650558001c4031441e24605050307562605448a800b001424094648001303a40b1010728000d44810f50a0020113102c1d428070106002d0007035200c03060440211f4904000300d0b0740340e0f5140d40c00510450f4454447d10006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 710927616 1250 710926366 710926409
    0x80c010309021305010303121d070b0c0c0a08030703170f010501180503100504150c1b02030703120320030c0a11070504020c0309040f1811030304030c0321020106 71
    0x4080003241a0380043c001d034901440000544201c50003035009554004005016259103019640c00b100c0c8605280d4124407841d44100011950000700d40c6100300d510ba560326801c0301c05040c0790083c1400b0754450a100700010b04200040000c01415101b0395441d10f4034801d010207038152050641b1440240740580005020550081d03d990340c403440d0b2040c0003035175180c0d11030000c3e00d0b000000011006050310f500c180401c00080180b51240401201000d000506003208001c0c8051034000364031980e01104004001035413414041c3e40c0103550001c030b0b94070812040500150140a81141c0d070081190651950003180307000b9411380380200380c0034155614100240c00100c582d54100e00c841d04d414087c903000001c0c5039032207100500403000d07250040e50700d800892041108945881a20100090500410f401a0080100c90303d9141c0da110b44030043d5100d0001c046851409290801401d0480000c0c01000f4021a5160302c40041410220145140e5202c0b904030b003a0f8140d0700c580e10b81e0419802441110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 710928866 1250 710927616 710927621
    0x1713030f050703090f140a0503030c0c06160812180105070c0b04050c120109020406090b0a0b0307052511010e0618030c1c0b0109050c070809060c1b01020c0901080c0103 74
    0x1e55000707140804d012612860090201115a8008104501204401d420030305006000000a000407405182020f44030f14032551203600c1901800d01c546c400082c0c078050802c920300380000403a041860103803200264440c5940884040d11261120620260642e0111405002c0c00c5d1003110030b0303603803800c18100a03528142070040140003220705004001c031481c000d481c0d164603040560f02241c00480c0d02d600c54014442103403c00e40208054500380750b240c82d4191103051050b003c6608089155580741c0d590320003110300d030103400c1c0030020074044214809844c0038651040703040c6500841002e0a12100c41d001542c075140c08030481034100c00d05100c41110303000c0c0000702641a42005d010b07124209894400180360030f041d0100d0b081e00c94400b01d408000d02c00d10b51003131030142c4514a8100024104614401c0385030081280050a0f000005801c552310344404041d25451185641190881450300c4003442c4c10450084c034003030040c4528100d03185140380804000d812180c9481c0a0140c800058004401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 710930116 1250 710928866 710928877
    0x8030a1116032301050405030406090e01081e15100306050f0f0c030a060b070c090e070819020429040b0414240d080d0f0608100522031713030f05 64
    0x88020300e1410907000f82028050744d40300c6e40c41940595552814a58064022482a04200041103504006002e08200002c410303240d00322400c610036018034005416483c2c00300202030000081004418081e070000c1000c1098180d910480c0140040d40e684201040d4114003110080c3c400400000403c13003100942c0025600200c4080340442c0c0c84c4d48400300f5005550065904a860740d45586041116000354801c05480300d04110240032124a042c3c0000d54074007030200d81c0000012400c000604640e1240e20040d17680c101c40c03060382f0001040c4444640c2d03491100c001140264200030240803240f41c00e100701c00600d4604120108140c5450000300401d07548030481c0356941001c6503000c005550b50044080d030441c03066a25540c0c4000c00c041170030541d0388044140c05100e0078035170180000e410214030b0164481c2070040000781c9a0b02c4506041100a1105a0300f99506140407444141a40302c0c210104030400c0c00c004080a4603448500e04900c648484060001124500c0043c40244224024503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 710931366 1250 710930116 710930153
    0xc09021204021311160c2408070201020d0c030c0905030c011704020d0816051203070f050d09120201021201050a0b1e130e040203061b030112020d0c08030a111603 71
    0x910000d812190451507102140909a08811441605c00c008880c0d1b115400b802c0d8100d01d00003858810807072241e101e03c280d030542c030501c50600d001a030094400d60550728101d030740c080c0c01e0004692a500103030040401e0200303c80041e110707940114607400c00041c0b1072040e10f810380d1060303034001d420015440c0c45d01004d441280c0c000e5040c0003036004207100741c01900c00f0b0f010b1400c510440c5021441c00303515000e061081d42c10080d00a00030095099048120400c0c450104d06206640d007010740071210007408014001800603142c00e103042c40c92a030540c044c1207080e84900c00c1c00520b0f6280c40404c80740c0d00703061003005122541003184031081040240082180301d510503415040c004401d0081c101019580c02024104120804100641c9010400190842c0386400140c9141910342c2e103000191005004000e494559070301d0110454840c8050b00304007030780106200108a40303036000140c89030f101003903600c002003502c4150040c192000c03641000350300120404416091942c3d0700d061480e03000e103c0d160b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 710932616 1250 710931366 710931371
    0x60518090403050903060f0618070201090212030a0e1207050f24180405040b041b09110c061b07060b0411031005090901022b02250c090212040213 64
    0x1000544400180c24000e51103a00e800c0c0e01c450b001400d152030040018070700340300a0031001c00d1040d03d440303079804d421806900d0001c000040e41c03882c10980c05400a0f0500a40040c1ca1609600c0c6410f0040090010080c0a94400c1400d081d00030400c01d03041021704202520b0f81050008101610780300030107202c800c1003d0142182c11035032504006520600c0d03002d2070142240010045c1c41d281c1d2110320508502c40450b81040b95080030380f6610300181c3d006200408241d07036852507050b00240108854010804407074248a004001c64009485801500311065548108804248503200d5511408a6814403141c07850a101503500c6000203040d0110321aa040b665400886c4070142d5a48011485010000c22140c426032034203040c0000d1003001044030602da4814043c00d60241525039800e034142d9091444034400881f40704203000248100c20300c0482c1c2d440340c0c2003080620350300c06101e00c0d031282c06003440c0a0790507580c1d1008000e074829a1080c0c03203d40c083c00005001450f12140143c004800c54a00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 710933866 1250 710932616 710932657
    0xc0102070b070c0b07060218060a08040b2505071a01030302030f130909030203030603100b0a060e0f0603010e100e0103082215020a140c0906100e0409080408150903040605 75
    0x42d03081c3d0303c8404141c07002078001800b55448c0c50405c454001801d03050301c90074905460305200604001002c0c00040460248802284101306003000700303020f44218070440c0000c084035030340c0504558000082142c18001034640356944032841011503040781e400d500035510704503020784c4905d21544240e070b00c0c0520a1140c280460703002d00910829501a00c02e400a65130f80c03e00360101481c2188110a0781200390800ca10150305845010002007140c0d5141482da6100c5068000199036040c200c2c511600700001000002e00b402020702d1450107042d00306184212980c8030082c940d4052001d020140005804000046038268144a801000a2240b481c18503890326840b40301c15a2202000f400d00503445155003500348030003d0807451000041d03a00800c040c540800108101940c014401da200b80c0c1405607a005075405000322600d451801841049101000d1070f21540507000f9001e060000d2080503503040f8040b1000e000c050044200c6d90045041c40e10705201243c19901c025560301c09284201310 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 710935116 1250 710933866 710933879
    0x90c0a1806030501080f060601021213180615020a120822200118140d06020a031e2c030403050115030512160206070206160609050c030c0102070b070c 66
    0xca9001400041e40c011409525000d0b00524280c0c83c143d032050290010f000380020b03a80c00250755014280404400340d122400d40100754a601c10784d502030000c80300701941a8214250f039074000e400b070312003a40c1100040c50800e00c0c1243d44c2d401007030008040140450104e0a00c41c003c218240c0e100e542d29000d203c02529401080524920100040711802c1d81a00c00c1c800c094900b4101c420020003e190007100350030f0001c01c10000440c18441d0030a010300305010580c980c2c0714030b000c0c8407149070850005c0d035841c03074a414002d00910010000c0c48003095482e0719130140104a00995441095200d004010240685100d1503d8554100891140d00c810400040000e43c00c0c000e8550103050310700d9500159186041c0035082510030205c41d10501806c11045e400300740480c3c044103005805480d05a140d45031440400d14901c2100c28058142800003000020090dca4010030505031241c2c0c25603030660b0406051580c1e403210454101d01581140205000c0d0a40b45c0004c0c0031030f6800b41c014000b10740e07541c4a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 710936366 1250 710935116 710935157
    0x203030c03010918140a03030606050a0915110a1a1005101d0414040c060f02030406031e060b0a031b09230d030f11060c030403030f11220f05090c0a 65
    0x45e00036a46805c810050b01c01d060700352144000505103420b1040c60003404880c0104026214001d0007141c00c00407040d2101c041c402c01a03607411140c03100498440c0d8081c0e080a01d10405014041e4440c0340b100c60001e01c44241024408085070006044026100c00e001c000360f0301403501e00c1550030024010116941e40e036030703075008050b406001092540c244c3d040c2802c0209844409800140500444040d140c2c11598008110340c200c03100c41c500040e10440070f11031161454001c5041121140c140704000c41c0c48515003000b0582030059840400c180c14680d284403202c81c1551890301d0100c2c0d10050100101e000c84210808200c0060780002024a070710710005143d44883d06055000a0f10071602500071a00490f4081601d2a0310000307202ca881e00c038908901c00e01c4000c1004003019180c245041c851303421908074020407202e42010702e0300d61411011030164500048045000c01005800002e00c080c10425900c1c2560b0340500890160b130ba510950b402942d00114200c4100003842c3e1084e2080c3c403000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 710937616 1250 710936366 710936393
    0xb090a0b01260c012c04020d0b130b031c110118050607020703020d0f0f05011e0f060305032b0509010f05090c0f011d0306010308070c060203030c03010918 68
    0x1511009402c0b20300000d58141e80e040505074002e03ea200c420b840d84540e070002262100b8411000001d40f201c001d4016000b84e000301040c903590040e00210f00729100d440d883c0c0016240c000243c070300364100c0b10403004481c1925074018065805401c038201c00310020404010f02091090302c2e044c649148001003a0b51403c6450b800741500d002e03e509040c0d5803c020092125a401c01c1203407005029a81c00c0d81c0004000804404000b425030440324060f0041000300449a80200c1d00040200151a41c09243d620240c00420082d0f20f05803a00d6442c400004e120f00c9484252504040294103000507002c4904030000800001041055005400440325040d40282446030a1090000c0341b04041404583e05540000e8003004854021111060458661178482c0310816400d10302588005801038005220516000425403d80521070021080c071540e180107108003032140102148450392080103d8890100303560385514143c04100400c64900300d41c201d48105c1e240b141400d5030482c40c40d0349040c10f442e9079 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 710938866 1250 710937616 710937629
    0x91504090f061a0111030f0a1116030507060c03020714030703020904030e041a01020c0103050c1908041406011511100504031d060301051c05190507030516030c030b090a0b01 76
    0x54010b2034406a400e2443c00d01c1050080c00c00321540c800444130203450f8007801c1022600008040b590003800b91140b071200140035040c000b91250b0040760300d400d0b241a038960000b500c0c64030600780b00184940c80f500c03565050540540c0a0071080d03003441360b440c40c54100307134910540c144070352400400540d440b60203203130085200c3e44490394400500c2d02032006890a40c01c8009a0100700c21403148181d0300426407500240c800d180002e410350303442c00c4140e42d0f80106071082c2d00e00101c0e2007403109e005401880c0140114080e80d0400b461005100c4070540d01d1909000f204902c6c9525406034a00301c0c040c8250100c90403015068402c11554100010100d91045500342c00152246413007040319584a0810755401b0010b4030410728540c107100c0881e00465484030780d00320108032060400b090150922140360004400c1d080c148051580e414044c0e80c03680c15020580700e902401027022003d002003a041012280d01c481141c0c1c6040c0b458903580340740c1c2c0000b4644145030203080c40d00800901c90b8500075000c1c050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 710940116 1250 710938866 710938871
    0x7052a2803170a0f0507170a0309050706020c0315070f0c2d0311010504020f0d020f130c0906031806020705160f0603151202040b0a080d0801090e0606091504090f06 72
    0x43e002c01c010504441c4611400910004001c15408606001c1c0ca0a440c0c068090301c0a60318103001c00128020415444050300030300582c0008102c407540415a82c03081401141250460440a49030820f030010a481100c041102d8501d1540502c1c028186207110728000c040128502d039591005010162400d4844080d5041c81e040540803d41c0120101c00c84a1240300200a5490b0660110701040701207800184550f189014030340866817520180b421201001c1c004070302407051005d25001a017003100300e40c0c0c08100c0071400418054403034803580400e0301d006c00440c40480282e032030b644000e44c4480750542e240d00030072004100844a17200d6000090031020300342032040d85440c2d0001c00301c40b0407001002c5103034442c01c0708100203001c0c001e500d5161501240c002034600c00300700000e2070702e28096011501500800012007400c0f604204458101c03030424500784180c0c003c0303040b01515550b08a070380035400a5a000070407a60301c1c3d005d0909074004070142002501017002d8554070080f800032001160080e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 710941366 1250 710940116 710940127
    0x1202121005060109080a030e0609030304081b04050c0a02120702060909401721010518090a030c0c05030a05030c0d03020403030f0c03090b07052a280317 67
    0x507130003180d01009064145c050050f24025550040c411184150001d224600100b442c002030380d03080c400c56000303013000d0007202c2c05100d102085610080400025030311036490540040c1002d1b00301c1c01290480902c55014003000b221a020300c101c59040f803402030741c00120078404040d01e91910544680540300c200c4139950a402e480283c605004d00589003c41ea0001090a0b41c0c81da820300300075148260380c0843e1b440280000b07088250964003a000603111a09040343c481d040c01106210414180c1d501a2418030035010000c10040c0c1007201078941d0038883e80b0428149020911440d49940414851000d140b170455650f0002898040903510a407041d40000400004651040181e0440110b29080c194102403968170f001d400110807201c0c0310103000c0720302c0000d400c040c4541000da000c2e02003001d020392100707051b0070030aa03510038041510700141200324554a0741d5040d50f2a282286900401c20004211094444020010314600315441710841c00c0001c0001100c0d05d0380203000f0b02c108800b160310359 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 710942616 1250 710941366 710941369
    0x303060b0d050a0c110703140a05010507090612060f0909020d020a06030e011a0f061c060311030c042a110a050105040203070f08060411030f0a1103010609060f120212100506 76
    0x19a02c030003480d4140314442900e1142030501061000440e0380103103818000000448c011400d059030884020000d52070b18042190058100c1481010745030f4540d10490440c6030311030703000100e8105000300303044000d03032003001c1190500640080c4891403029110301c0c2c1903841c1d9804103402e112203402110200f5219140c01040803801d05c00c01d00100520f20045103a0707000040418100058803103280e01403400000c10190410388101020070030303a000b4100b0481641d9030304011a1107030410400b40d119000e0b50f602c9014501c6d0600441c180180b1410082c00310040c1c80c02d00000c828030030740046092200310300004406000c14040200301c940580c00200307443c44c180c0704050030440365070400362200c210800705100002000894a0780164008141e001841c42c1d20002031424403004102c0380701e03206400003070042001d40025000f902e042a402440140d445180d0242940e1403806442101d03075242d1410410340c00241c4016000600203452204143c01503159a03040807454014502c10540b00e000744a9207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 710943866 1250 710942616 710942621
    0x81801090b0106031d01090804050913350a080a0c0e0a03080d06060203030403080a0f0b030a0f06052d0408090a080607091508070e01090b0a020f0106080f06130303060b0d050a 77
    0x30b580400c002042810110350394651140904c2c0251800b942c01700000820b059109100107624076002120130604403404003c4004404529015200d6485037082e450034610706402901d49916854440c104243d413001080001041b1209810f420490b19440100b05034641c00e42a1001d10b001e484041d0b503c2c0c0249400100340c56143c1d01080c00c42d8010810800481d0784440c6094200913000070124240ea107001d6058054040150f840d170341401030002103001c110603d5041c0d900244a080288403d0752290711884041003404000c4142c0b500d20743d11074104c80300310300300c040c0d00c14031030800c00341800b801801051340c82e81160441c520590040d414465203940008048008140d00099030140c524600401055068058142000d01c84500751300850741c1c0c010300c03281002e020003000e000c2c0c50f01c2100d140207582e400d421000d4502c81d4604030303000c10081d07000705450300c620710005c00a1056807100d00848019181015080d000c255a80d00003250801a0100a00303510285c0800802c2500b01518080d08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 710945116 1250 710943866 710943911
    0x6070e0415140f030705091803040302060a020a05010b030f070302010302071401050108030c120307140d06030206030c0a26041e1e0b0a092619020f1507081801090b010603 75
    0x120354042c100400440c0d41f0f100205501a43e807619088038446da00704594a103000d9600300941c00701001c14405000c13a800162021000c0c000c070000d1000c01403900925485100078100030706590042d91013170025500a400034214917124012045140406944035401c50b4005e8002e4141d542000400f040018420018601c40100368802c061550420781c038040e00740e5405812100c00b9041c04100c0103d10f503140d920210045801920036503683c90040343c014920b5100700101da02280d0070550703242c15003100c1c00c0a0aa0315400305801e076007546840e1505d51171100c6440d2210200803080b03428000040e0404039006410381c000e509402a100240f070103c02c02c26004007017121151401104c0004103104421454004545440034505030400484219403446003c8100801c041980c02c502012540040c040844500c82e505480000c00302c0c40e040b031140103050f50041e00040c514004900c911010302250a6804442c1000040070405640c03081c43c018000d903c91804207503525036025616419a0724690f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 710946366 1250 710945116 710945119
    0x30a0209090724082d10080f0705150c070b0415030b01030c27050d11030d211e05070f02010605030a0503070b070504050a0b0414011106070e0415140f 66
    0xd41c40306050f0000340110001489000311284003210a40202c0003503149000d107040102440100f440c01310388807682403c4c1c603c998442da01c41d02e400b2206c0048085100b4040e1030008084611a091403a001c6015401c82076460300c9900410a0000d4103141e010010310003001d1314644940d128065100c054101c46900410700c0c103050428038090300a507800b50100b41c00c12400301c1070210b500c0805c201064506520b0300701a0f042100d0980c0d2105106e910700344070340780c1c01c003c6089445a100c82442120303a04940c001c0003403402d4005914103429500b0b5004004114903101c4a5500c582054a02d0b50580d6410303921100801c08500f07580011540c207025210203400180c00400e4a81903565905949100314500038207100e2854001c0b0309424414070455004103002400404101d0315800c110280d0f83c000d200d84080c440340c220300a80e50b94020031100f15005502d402030105035480420654090400b2610346500983d95070fa140c0b040440100d03031201400488002da045450400207000d00004244802c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 710947616 1250 710946366 710946419
    0xf131a04051501030509030c0d03020409060b120c160b04110306010f050607080d0b12030c010c03060b09010c05010906050115091d1308041809200618030a02090907 72
    0x1091141c2c0503204070103800786000130301684ea0034013075800c1d4064804002d110380500414103508981c1a000b40007620380301c070010031040d580e80609030758510400804004001020b00040d122488001c041c1c880c100c00301c0c0e000c4520b00c0140e510219001d0003200c0487d4140e185012003001810708000050140c440b1820040b03429040c480064001e006040c001007146074005907000b40e85109030030580001c1d5000d0113085c1080c0d8140c8449449800041d1400400d629145c0300d00c000e04d1203805598101c6070300b54001c1e480e00783c0b01c04c01100d9a602144064503150f4075a0411400142140319442c02080b80d010f401014403071902d0020510a007a0b4021640422011611140b14640d03c1c809034006000b041410510b003580d282014250046504c40001915030507408000b21010390803050300107200703088402c0c0c04801e0880d4070720140c24242c5459000582030020640035601e0307858500b101c81b001000c8400e1000a6800103c4581003140c0312005508281c100b00711a8040380041c040c0c81804000740b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 710948866 1250 710947616 710947621
    0x10507020d0c1e031d0f130902010e13021c0203150607240c03180803010e090f1f0c05121b07020a0311010f0c0b1911130513060e040b04020f131a0405 66
    0x802c050308103c608a07c007941e40e08143c003160b001d0074540710f900743e02030304d0a120009000300704030082d00303c090b0003082680c02e561301003550400c030b00c2224403034502100ca000030300c150181400055007090500322910070113a08103002c07481300144a88001c6583c000c011916043c021402815110f0031050311864200240000001801401c140c0781510007601c003008250f43d079225a5882c2ca585520200171500901004c074104401110040c4d1400e18040c1d0b0a0019141507001191144149954000440740100102d80c40e140017421a80318080e0000c041c600b0322885400080b50807035564400c480448411841a1055811410810201c070142c00d0403034a00c0426140d210420200a00803090081d10300405003850400c0d910090700c081800320074545448000340c050341c2c0082d840c018140701c1ca40c0203207603031030790001c030300801c3c042d2400c06980540d00d88a59680e104102c20150003264800203582d0401d20310380741c810000c56481c1c80120301042602e0b41441c0c3e0040c4003462120a8081c0703091408 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 710950116 1250 710948866 710948869
    0x204080327010c0f080906040b0f07030306050a05060711030709020c060103020a050105070c090b010201142802030106021509030f07030918050609010b1b1c030e010507020d0c1e031d0f 81
    0x15440d4a591704410619504c0001d580025420300c2203800011040f000420513074501840c21002d040000c0c802d440821001e80c680c001c00c00440d446208192f40020308000c4180007448449000003481e80c054111540180c80754200001d84c0c200c014951003582c4807030010019490301c1d0303c942005280c00e0902c0d92901c04562500b441e010454007440d002c00d525400000e0032a4400d5000b0901202ca1035140841c9083c8046641c403410704a64070940841000046d410080d5014801c880c12110540c00034040b2001c000240c00045000900d401c0c60340c0402d1020203c4200302c04000c00901d0b2181c0d4a07040d1480c205020b884402c8496643c540b01d461030042004515290080740038150f0300d18504998036002841c0c06102d80c448113015666141c000c0c104600c850301d91140c03e0b800c240e46151001e216030311303007090303030b982211012101a030044e03000c0110a1030040c0141440c3d45580d004422541c044010048181a994a0158200c3c000342412012103014964400910411441100c000703040c00407000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 710951366 1250 710950116 710950133
    0x60d02030c060c19060501082e09110909010213090b030a110d141f0509190c0e070e150702032509140f0601090b07080a030204080327010c 61
    0x80003a010b00800110f049915504012a81c4195140f00301868090300350700d405170107010280720300c0b60603100d081c0e482c1d00f120382050501809606004d610313404100b114000300000d02020b40081c0c0b42109041c10500c00c9803903d8242d148611903600000d6541d80305c03460840a031504551200342110320f00b0700060759569000c03441880c91a044000300c8c2c6003e140394002401400c2c110402061102e60207928110200c0102e101038000301e034070060790350099440700f2800c103486007203a03405180e41040b580002c0d500f1044004030344003400748410030082d03500c0d14040080c1020568a0001040311040082c90740e103010810545003070000c0b16a03609100044d0b0210b0364502201c0620440040910f40c1650320485050f05103004100d61402400b805219945035a510f04056481c030502040840000c1c039194000d0700e03550110380f0300b18941c0780b800d03180703441c4c15095030800390044041507003c1000080750b400030070240c000d000b1a0f42000c2440c685d86042400950a01c0c2d88a81c14060000c00840c00b188085 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 710952616 1250 710951366 710951383
    0xa020715050a120e0109140115051320030a0902090a2d020d09031214100303080402010c0f05030306010215010f03060b0a1a1c1406010f140a0215060d0203 68
    0x6081408100d0a2103c24402510a18024114139031900b000e5106002d03010503900050810440208004000d0702e0300c0c501100c80c02e024554021425690420041a050b13100420303c05231109075981200044003007201550040c0c489801d0561140320ad80d055161984105410100380c100400200da5645d841c031013031541054156103540b00d54621507505001540444084980c802420041c10105280c050403140c4410449400d442c9030528040201c46e0008a640c02000e441c0b141c01101d40c90341d98103d8900d07000400403410000d01c506070b20005461090f40640c01c9103e13002442e1079190880c002403800e0718540509181028040040014286036510380b0252500007a01046924025003c1110084030780d001c490f401c0d08401a000f05041c850011300301008402109a0b0910800301c950310640d24448100c883c05440000030500d00c0d80140002c1550b102c0c0e03400e1483c90704c0c040d60084d210a40040c41d04401680061052180000f4901d1050303504c01800c49560300c1c420840d0b0082a59400301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 710953866 1250 710952616 710952637
    0x4050610030b030a08030c22030302030426060f0403030e010c1b020114190207060201020304020a060e040933050c030406020309120301090b0406050d021e0111030f0a02071505 77
    0x4510850b5016102402000040d81d000555940c0c1c0b414403884442042c1c0c840071815030b9801034030105050f102401c06c2070b4421280c260f070007582458102141080900e500711100e581144080c003501c0c80b40076051001070301ca042980a407001600e440d05014041d18150300c98495664580302005c0d2420340c200898601c03102c0c60303410550701042503100584455850003150351031244007262200011400c2221000d214209030b081da4681580c60070182d003130340416100294881c80290040c0f10321480343c0307200c0700c0d0490014408280000b040d119054800245000486120a400c0c078880c4600389501051002c003000c072500b080702c0e242031100070515000180c002400182c00101007a6000401c002e4036070440e1020f00c0c92941e03560b48840d00c40c01845100c00c80c0c1d004a04281c00010f06d480c00381c060066040d0040d110f4555018000701c1103110707a010303e0303042e13052080f0f4103902003400f03008002910075940d110162540d16501c41c9030291400c0d0b8280c2c000c00709080864400700c0b4680d408815916000d10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 710955116 1250 710953866 710953871
    0x20907050a03111215010809060601080c09040509060402091608040803070306031a24221e0f0b060703020318010306170303100f0f05130b040e0304030c050405061003 73
    0xa94003411000b80440c94030071028820013090003000c11503c0c10005018882600e0502214640d944c0151200d007400c13100d02200c0c2d0880d100040d490350040071095801100341040b14034041c1100b000808481c2c0030788042901d540188100021810491030140c0c0040e6071341104014a100c400e402018040c0c0148014807268011000c138103032074020b8000b80d015541c0700e8220407081e1050707071718100070b02000c82d04500c496802450720300d4100300750b15110030324100180001c00000c00310b4a4505490810500d074803920b1399203024400c01081440b040c10642c100941005c145801288024402e880c4040c07020703841350204200840000350008100c4841d5100e00114001c591030081c016401880142e100c64090880704a41070203009020004510880ca5000f8480c0c0145e1200b801d900001803070700410784410b041e0300081c0031526190f403601c0c9956402c1c100102e030100760742c804101076612a0030881841d5202003010700c00c020724440544003403c001c0d40e080105185c800001000010107440000074180d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 710956366 1250 710955116 710955127
    0xd0f0e030c040f0905150906070f20100e010c020c060301050108010303110a05070b0901020f010501050603060415090216121803060902010e0d0c05040e0a08070308090721150902090705 81
    0xe0550300951444c03a01308003941c034409922101c44079500c4d011035014001d40a40800038a4160042100c0e030035403c400d03504c4010001c018290398100500c0e008800e101c520800300310402d9a0024054031144514130000815921101080a4909a40b21800520800d001d00050120341da02540381d0303044070703054600009020401c40c040c500700005500041c055016883d07002c80c6285485000700700098080c0d0807200300420101456007200d40078040d04d41d100305c04101107000c1d403400750450115440c01703131f0034462102e945800c02400c030780c0460541031824040d01c0c5050300b44250b00e0645981c8000ca410b00c0c03c035401c81003400c0c55802155000040c00b1607030790b002d13103400c0d039200d40c2d5007090340c40004d00301b04080c03051410507500c0c28500d4821103128500340880807512440101c3e8210f48180d12201c03ca081250320780e0107440c0117400030000c100521500d90006294032901151066100c01d0100302d04c000341d29400c019800d21604890075090fa8140040f28005031070703100c880c0764080320030300d0000d41b0760 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 710957616 1250 710956366 710956391
    0x904051017060f0123120313081510150f0908250501050901021c02190606030309050406030f062f091f08010303030b011404080d0f0e030c04 62
    0x19840d03a082000500400c0305000d01207280010000d000e241807000c0c0341d149a9807500b142d40100d00071460500300e0200740e40d0b5250a401d001007100c030040c0d0714400b52810282110f4201d440c1925541c8420080ea00084c0b65000d00c00b5442c008540100c00360302412010f90800e1604601404042c000300d04104c1203008030084203100750810310142c4901800e44d920214040310440424800031045104d0802c121400501c660140e0100d8184d01811307009080004014510800601113141c00039084d40079807001d0742c0c06804000c0d1002b04c2e1a10415000580798214100240115220f400a50003a07203010014000b28010210403902d49a01410200d01015608188082032803005034890b04000c240c80798610403c3c01c0c0c0d01501043c0e01c1079480c205510746012441089030501000c820100b18140018008a4443d8100158802040c100701c503800040c81d1a0304004d41c4150700001e80798002000f40340400da40803a038410b44c415640703404840500340400003511080380f81085e074451030b9a1584c10400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 710958866 1250 710957616 710957641
    0x10923120d0209120304140603060a030b010e040c1203090b030916090603021f05030613110d0501090c081b0d0b0607031e0914060714061029090405 65
    0x20580501644800710868150041e4005150843c8909000c0040d81072180c000800d0707800700d5280c0142081140391704820701c0003d51000d45101e81040c0c5101000c40800c0a103a0403a000700415034400040e4505030a008451202903001000307025410900580800da0040002060300e03c03a8000e9039498a590203002d207041480c05443c000c42080f89000140d441b404e9101c5000c49009135592082d0b074a22074006d20b18440300c00110400b00b0070500104550b0b080029410060400c805030025014426502c2c05510f5000548400f60503030b200e10040c0704000440c0152140c1c0e0f1500d0600d1010780c00c00018402016206000c0e919041c0d801042d505008203081e0031403016100041c1c00c15945005900b001400c06003018003c1c4140e03070580301c400005500c00e03c00c0c1d20450b0407003624180540030110401041c0c3d4442030081e40da18015045520742d005060042c58001c03201900081c0c8132501c3c2c020b10302c262590494800f05800c1440f2031031495a90100c5c00c8030781c406800c6900141d41d55076045030700c11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 710960116 1250 710958866 710958883
    0x603020901051603080901200708070515010b1c0c0c142803110303070906030507030b090a0b01080c130302190308120916030f0605070908010f0501090c02010923 71
    0xf118089010314906254110f08110300502524000340b003607925140e01e01096081f000f40d1903940c110100003000110360341ea0080d004082c03240301a0b0307036502911410503c8004086c4c0003020f42400000d00d400b41500000850150b060291300c0c2031000100d00d500240c1026a0400040c281d8403218030066541c580512081e0070b40030b00300080e21101c02c0d40d00d9060f4468507144008401042c400c5041d801d130b030715001007a20703c00d074180c0da542d400300d50518800724007034800601003006150702c0e100190402e40d1003400e814802c85061100052003144500010309000d00a4800080d24400b0000c21040d4011030311034605494040d40d400c00c00c1020310702007603d541010340c8042c002d200c01080c00030b10301095040203400ba032812000c669201c402c23005000d41c040100c0c032004290090320706c94540040d060780c000c2a4401c2090500f0b54410365240b00880c25259001000055181d075240103000f112181d208460288216100801c284081592140444000c800741c0000d8070749862003405841c1e604001018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 710961366 1250 710960116 710960137
    0x160c050a0305010509070e061003091106210c031b0702060417060a2018010e03120a090b12011a070203011503030206130b07110304050d0c0e0c090901060302090105 72
    0x500eaa030300c0c01e125000385016901000b440c01880000601c0908071a000c5000c3ca40003801e04521001080041e40240070b03011044440c400c0d216101801592408080c10400780c802c80b2014140403000c000102c860401460380d0303015070b02881849401c44e0804050500071104c500c00e1a03071101e00d4000540c540c0100c3e0700c0141c03c41940028451040004900640201c0e5010002d004007460000c40419844441b480030806140c248800342140c010305d140109410b006040c0104000f025501090414140c69040b0108a070005903c00c0c0650380161208002c02011541707a0401640b552500890384043c070034070030790001c2503501c001c200d01513904032041c0d01d5004008024040d400402c00c0c0326402d03148016000760081c7e00000f00c04100202035981026882745801c9030035079901d801941d801c102400e1000480c8000c1c000407415499140c850b059090081b52545400c2e40b0b00460040d0b6000700178032196584809014000241e1150110903054030f0232800c000d42c035440070600480d15400394000c240c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 710962616 1250 710961366 710961379
    0x1050c0a0c06200304050d0602030a0b130c20030d050912130303110a050c040e160905090d09060912110316050102060a0c0815040647160c05 62
    0x84140e00401410522018115003e203119184041c0e83d4590140c0e1089075003103207100c00060300207941c0ba402942d1000501c540092080c040e0008510701900000c80c0201103903983d880003180075002020b5450144030042e041481000203984c69450340641c41d0740f00703106510340c000320fa0942d00501100c003043c00c8280d00a6283c20058030a00c00045e1540b0041d07020030290480000d01c4000464140c6000750010700170700c12081050180300c01400000103084850040f00c6800004812002c01f18008155044010549040000005040c01002c5141c001403010041d030810941c3c0c0c00004090803958940c0f250020030b0254101b5000460101100c1d036454003825003c1301d5085011038002056500aa00306e0340e10380c1d100740c0c249040741c181a03a001d0120b028000041c035681883c5586280080024001003900c42d607031106440c5641c580e80002c12044e407030a445001900d41c2440801c40c410b1404884843c00360810004443c1d44200d46064088190760a6440b0500c801040c1c124000c26020308074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 710963866 1250 710962616 710962619
    0x1f0b07150b0d06151d0417160f0b010b0c0601290d02030f060103150b220303020f0606030a0c090902011e0507020a0806060f1309021f0201150f0501050c0a0c 69
    0x40c030080c074021024191131032440f103000c03881141114280c0220003600f042d944040e00c2c0d50f11514a050034504001c41c100c13108000344074000b825410794a000314400c201c10f000c0750742c00786031042c40d9034416000090200c209000e1124013103400203200d03046910b030321650002e88000707580781d20002c94126000d0099078400120b00c0e1543c0415402540b007100302a454100507100c2c50011000e0707502c1100c5007150078590080034002d030301006006266101d030790a10f64601003003000c1d80d0648524182e0056026810001d010f90400205200c8140c1c805011409002d400f4840e030388641d06681d0300d01810548560728070100c02164004c2039440303488485151101c015068120f0010b001d50320145c006c90081081007000618070342c0c0040c001d8000c20000b0070a060b00a16402880b19035080c101c1e46100c1c1c6505e61160304096200c003000f500702d6100c0c26080391300b1010003d501a080d41c40444458035003281505003044148001984642510b4007440e016544640c01000986481b05024010b0580d00ea00d420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 710965116 1250 710963866 710963873
    0x8030319050604061a090a21021e010816111213050f09060103150b0706020405011d0d140115091d070e010e250201051f0b07150b0d 58
    0x4221046403010031051045695100a10050380c540384100f02c110b055490b0700e070003802001405010500000b6210f400c00c01e03941c5071800c0c1ba502e200c3c0b5202d407585860283c11070550a2100c081030030f8914441d0b02e50643c1c8003100000708121401400074081450a12551000521549140d0701081c006001c0300d030406140c02d5420b4091f8000054001110880b40c400250782c20801c00200038200003c00d5031107180da0304001500a800c9140c0042203000c044100030444240040103080c0660003503100503160703400d04002401145020750300422403404140680000c0c2e40c0e10f800718094552052200c0c0f03c501410b40c84601500100102e4511014145404200d0612503400b12401d181c000035100341c0c4050449900b07898000300d01918604030b0f41e810043c4448521100081d412140344000d03400100c0814046d003940c40c0046040500613512942841810180182e000302c8201c00e1200d500c4025103410030591203072040040090601200714002c40c1400001c0d03002d58021076028040810540c06071a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 710966366 1250 710965116 710965141
    0xb0d02040c02100b0d05031909051002030301080115030206030a090203100926130b1c0207060903091a090409081306110120070f06110d020c0708150403080a06080303 73
    0x2ca201c1d015603d05858071100e0300e4003c5171000d140d07800002641c0b0305826030784044108540c03051410203018011400044580380ca900d044280c01d000d1b40616140e506200d011400c0d254502991280e010020f00305101690303880044075001403605c84000b405c1c24051021038105280c070b218403074075207180c40c25640501c041e4262030446842444c2040468444500d803500c21401002002441703078100200904ca0340c500c0038001c064288003614126000303100200702c942644d201c0d60040740c82310740711007a040070144c000305a84050281c41100480d0403242a12030229401160031a5104a4649888a003480010000c071011120350a0891400c552200340282c449110303a1912480e640c604554603406c43c061266003044080140403aa280004545820700e90310310702c84040d10310507a1040d1030380812204500403d80c015031940c1c003513200c6c01820f030361a0503c1d207258008034154010600c04681509140000342e80558541016030558079443c150700014482e0b030b0044134452000000388040400c460 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 710967616 1250 710966366 710966383
    0xf0804021513080c0603220816030302040510140a2006070809060f2503021c050a0e061b0c16180c1d0907020f06181510090b0d02040c02 60
    0x42c0131100c0002c251420b21101d0710007191881c5001c0fa00480031050b01c1d80091000e0303006401081c0183c01d200d004800000244425501180401ea000604000c6410060815082a130342401c2110468290610a941d00c0c400c1900d030304100328040c1103490b18525000003691100d0300101c1202c465140035000600300c1d990a541c50600d0b8410100000d542040c2c1400041c440c000c031312050320030f8000241c0c500b0b50354901420403a00f41034092021030032140c0b0341410110307142d2045002240705d081a050210444000d10ba2449443e00300404000084a564004058040041c03000f150350b0f10086160703070300307000444000f584a003540700000211480103a5400c00c0304140800700304482c04003070009803604c0b003405003180d4070300c50700f40092a428600200810703801022401a1441013607d1480c40e401d00c4030465480c031a0345100d43d40030140c10030030014004080048041201e1605001d000c401c844a014418156041e4490104881c1030700e44107621243c66901800c140030500c52081e01940741d4454 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 710968866 1250 710967616 710967629
    0x80903060f0108070308071505160806030a0b0c030709050303041203090b03010303021005040311010e0703120504180c0309060603110f0103020306060906070606171c0801060f0804021513 82
    0x540d004940c007805490702040c1292141c00062581d40d24559411001d0b402102080e04c4100d40440588680e58180c01520b219032904040151103000140c0042c0500001800f0340780242c0c41000100300080c9141003281e00281d129110544030f603100201260015101d4014507014080410001080c03103100c00388aa05500c0f07a1221061a0f80b0b03413140030380030b0009100140041c1d12250504074160000d82c03210340c00078024075040b044e400c14a080c1a0a60304007446509095005200030014441c0001079a4401a01c2e46002840c1ca0b180a4030240c00f4401c40c203001c401c00380e0300c4200b41401402680f080c0b0101350b00c07038000c3c04601d6807070921034285420300203024099168400907089640c407074400c580c45140000d24140c20403144009100c00b540040d001101d0007613940c200070943c1c0e4800c08903061940c0340c5000811036103a0800386415900c0e000010304080c088a0401400307100e400c0702801c88040316030324003100c856546000290801d042e84c000722240f50f200041d15030420b0802501d40058421 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 710970116 1250 710968866 710968873
    0x30a061e090c061d100e04060302100c0302100606080c0c1507081603090c1406070c0b1c0603080319020d060305032502241e040e13020108160c0f080903 67
    0xb0030301303100c4807810010980603070b00040e0081c640c00b1701c1c0e010320b250341c000c2c0d50090300c0003d00c6500ea40c00716401c1d844d06080e460200703c0400907d010140d04126125101c4611601880003c0c50400c1c00340c00c5180141074411650408a01d15028a01c10090540070344c0c0080c2d80e204041c1042040605007200c251400c495a520080724501c102d8000d020b40303541c003644030155024140c500300311203502d0081540c905511200811580300815440c1580308040d01080c0445d541d200062000946074420414001062030705141c000c00c080380341e20301aa0351245614400c00000080d52101d88002d12801e1040d040840ca0408044188900000a000c062086044542000c8500c4400351041c4581e00e00081d4455698101c9203410030a00742c0c1003050384041414941448290100080740340c1c401e031120300d541c01c0003007820450340d0340c2c80341480d81001a00f09055175a02c02c4e40c00003410500020525042a0070079125407520134403c07481c006d81a9002403603100d12a2051608441341d40c885230803c0e104c0d10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 710971223 1107 710970116 710970137
    0x80a152c010b01110604051b040209040e0d0306090e210f120402040507050304031d1f080906010501050f19090e0109140c09030a061e090c06 62
    0xc0005400842d602d0604000144449209000c00300b081c1d01040c00d20010500102d00c5111101720861102d42a00c04400401d02074822800403580052030000030031004907001c02c004c5c03903890440d502445643e6807008140f040e65901c0048d6801d80d04600780061980f042d48050720320558200b00183e042141010500c00250000708040040c1040d000412045280c0343c420158001000c2c01c081341181000d490007400c2010070001404040400104c4807071a40c4d0f42e101422a000600b441c40c11800e0301004003d2455109407080b6045d4840c00b0008111580100c0c203840051146115090034070500240300c1003900c3c184084541445000c01000c00d111443c890014041d198440e030200741e009089080740348461005000c0303e1789400c01d00107019503650100d50440c403150008001b00d00b4114101c1c2070304102400c0084910542d2800440400700b0103101c82c03a10488582e6201c20343d102 = true := by decide +kernel

theorem cover : BRFrame.Cov 710791366 710971223 := by
  have h0 := BRFrame.cov_init 710791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 710791366 ≤ n) (h2 : n < 710971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
