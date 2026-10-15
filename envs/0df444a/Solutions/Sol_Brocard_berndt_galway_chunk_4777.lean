-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4777
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:41:46.193759+00:00
-- url     : https://prove2.me/submissions/ca8871c5-1696-4031-a8d8-3354e58d8a9a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 858992805 ≤ n < 859172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 858994055 1250 858992805 858992819
    0x181a0610020609030d09030c0807031d09090d0e0a0b0313021f05092704230d0207030809190305010501061d030613051606050d1802010f0503040206070c03030e0a 71
    0xb503003910440307a59081088101c0c0e0f00030f059000102c40c1482850660b419500035200c11070541c0000d80124000303a00000b014220f00e0042e501407510032000c8800401a060503440c181d0758907a00a01501802156002c48444d65a245480c10080c03481903101940d034648640500241003c1d41c5e801c910401c00c1c00203180c045107480b6900303450342d40540c4442d440c02020008020802c0c83c8d041b0341c45d01c0b40300141654603203400d118403914040e07031041409080401d03c180c1c49540b444402c0213840c0300340c0d00c2402800d26155000402c5001c0b29040300c5199690030110f400700d56007049400d80c4d2400110088000420450154003060483e1042d603203045146403072100502050100e59419603250703000a010985d4420140c50342c04032644500c0c120741d03000c1880746120b4144003c0764045130204201052400d480c901710700400d025655074002c072001c40641940043c050b9040c00380d011040220100c0001c0440d1100720031601e04035040300d80e0f800d005a6034034004040d6078034400c40c64007a40180da00000c2d49 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 858995305 1250 858994055 858994063
    0x3030d06170102031b180409050a03020607020d0c110409020a03080315010302030615031e1321170901090b0c0703120b0102100b010e0a171501080c0103181a061002 72
    0xe501000c0044484140500e1461090704508108200134070441c1b082009652144558135405204001030003040d9441c1c180079090410081c032045c25500092402c0903110341c840f02004143c0c1e80455803c0d02110040046401040ea4082c002d4004942010200501881030302440c401d96200820002c9200b0013001101030740403c0d1401600036592402c41d04085d030464024550104407190005807500381000ca040300c2d02410740d41c4d0000510140808024048001c5652098407500d00c400f07203100c1e84e105401800196003840d480825079284000c034500003400c0d0040ba00c1a0b0304a14080082e0400e0b60020320598813412044011410040f401c0d542c1d170549000d503040c0c54005070040c200c219464040e1030050038031014054100030704105031200503550741c00e20f83d01034030303c45a904608500c2c0f03924140c500b2321003200100003440d0036001040107e9000505600c03842081c40d0124043c603045071041108055600001d05040320690b00701460907500031342d184601d60850f660ba0341c0c034000b45420703030b22 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 858996555 1250 858995305 858995311
    0x204032d0222140126060406090503120a0204052d0603191a010216120339110d050714030f0609030310090506011e0e03030d0617010203 60
    0x5444040c20008007602d45030003000100c140120948200001094001088035400c40d0000303035061240e00180900c0041d03d1090000410810f609150300c1501c113030441d0748100040004040d50b4407183c054040080600c1618012015071580d640302d800c24501845c0a908140201070051201e01c00c0031500e10b040c90008091646000921618201d151051250f10382c0020002d42c11400441c442003100403c42c40303030340980c0800d800ca0601c4a4201c0c0002070428a1050015203514060003007404840305200c1d50b040c0c046c0c1e05040001c0c0e494111100d00c0310600c0d503806076400100300409030344800f0051101540c24944540007a090140355902040709202030380038060643c0c1d01c8900c0c00c0c8201c81180d41440c034070140050480e001c4c88800c800d039600e00541103a00029a400210502c07201044c021060006003103440340510540ca04040024149010300740c100000754400d40c0380803900b038011903810418000c0078064a40c0c0743e59407401100500307241d11881c070850901900b0300f14012018401d90740 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 858997805 1250 858996555 858996623
    0x20c0607080d0c020c030a06050921030721050405210427060b041217090f01050a0c050712021503070c030c060b0402040620070e2e030303020403 64
    0x420426a0760520004180540c83d443c25446a4862100984d40c20441400207030b1062101007180c1c640f200318036050044201d030920340d40250500d000741ca080380c0000d82e9806443d910340480d00110030700040399418500300000d80790340d02e0102408140f110118aa8084080082302c64030066000c40c40c412440c802c2c0e1185140f00c41c2c640c0c9040c0b5403108072a0041c10038148064002c02e03101d803601c0000007250300c9540b005075800d134050403180401c07265a03e00da031400c0c03120803403500300440200424001040e96920a0410000007907111045029401110320313143c1110450351515243c00030b00e600442000016482440c40d8481150f402c2c000e042228802c600c82d6a51003548440c81e41c0c260782803281050210703892610740d81c3e400c01544851000d0b2006201036619040c0c1544030025403051502da000082c0320740d811541003400040b06170b904050300250f03c581981d07500900203981d243c000c40072440111300d05205000c00010f060b4142c01030001d0702c1c001c00d00300076514017145050f4026005508044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 858999055 1250 858997805 858997807
    0x207151d0d0e0307091b090902090109180905101e15030206030709080303091f020a021e0709110c06220303021806071b050a05062224020c060708 64
    0x107655244900c00001c41c0c1d0302d000d01201c0c0120f898682060507981910300f07003014082c0504003040b000364483d0303001c00204600002146031030600d00000f040040340e80100320042d00140a16a90340e07001d94010245250002e007501e110486a00700d10000c0c0040d0000580e42e0003109421002e1900c03a4402c441c0200502c0070500b0a00d03156600340840d45c0c1000b03003a002485540d820006102c18180000c0d4480c802c05e80140142e60304c024020155008405008684688140011070045070000f80c3d55074036155092800c030100d422030141c68944040c9810882d010343c245442c42882d5034104004c0c11050440703805940080c0e8071071810041007200c0c044020051400050444c0120380658000e1450103801007402d8200420400400c0d0f140d808054126115119088010000355049142c50f000d000304076810030415180000041490103131080c10210450000c0c1d8080402e1202181540140400d43c00240b01c1c0c0600b00380c0550b80c41c0e46258441c05402801e04510191605800b152803841c0e00403034113 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 859000305 1250 858999055 858999073
    0x30c201305090f07060306050306010902071e2607061b020607050c0316050c04151a0c0a060606050d0605042003060d080c0a140f030a1d040207151d 65
    0x50800341c1009000d041540c0550120031921010600104010303140c992400b0401d0341c035050526162070070580c40000128418441c8100064000b4101400390992680512030314445090840e0034001c81f400c401444072401c03810007a440000070180039207030302441d01000915240c20351140040034420700c850041e000540081c09141c0960058251034024900710b070309165041134811145102d0f008240d505031b00100c2d00d1841c902e42402001ca0b4034102903454034105160000c400d04082c1e561480035080c42001c1441e11040a0800c951340905030070100601206540c1d84002d00a9409120801ca20300d08014003c43c1600b4540984000750180d100c00d9101c2d00203030115443c1c243c00150940e54030081002400740071a1f0600050008040400c000d0140e2004525000074550303002c01280342c075600490195030402d4004000c0e114003000d5802c0000100c039082c000c607042803580c0b00d15180c1c440d10201c1d100050045c4007418815400b41d000302005042c1c08280144002e45111588840e035038400d0300c40e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 859001555 1250 859000305 859000339
    0x180f0207030e15120a050108011503050c12010923070f05060306130b0a081c0e090c0a090e040c140102030711040e03070b0a140105220c0e030a030c20 66
    0x40800c2c000120440b0340c14105442e02d031070b040345400c0d5802410946c5400c014803041a00313115003400802450741400846155990306074450320300007449481080902500309002c0000e411094580e54440d906901030b00860482c2c40c503652040030381c0e2000b4840d200c07010501c94181000d450903244000c00d60b90665031040100000e0710750114000420319140c000c1002d840d11000304c90000b810001c0c002c0c10a844114488514001e0b103901e9410401c000c0c40c1c401c040c2d03a22042d04140d00a0700c0d1401580c1d44100180d02955202040c0c2d001c422403030b4a290800003070004501c0080103584074454100e510213011001280d4074040c01001a0944411044e50740d003030300e02603000c0201c884003141542d00b020780b01d403103000050380f04407802c00e5001d48502d004c4640144113800c0a0160600319213008a120200500304039040460000350300450359040014411030090060b4a148036004040756114040c3d840c004002e6060400d08440394140307100400d407802401c007142c008a42001d401c60480c2013034009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 859002805 1250 859001555 859001569
    0x618120f050904020a1e0903110616140106170f011401061d040b0604170d020d02060406090615030f0c05010201020913090f020916120504021c0302070807180f0207030e 74
    0x82c48405005141101b880711480c00c106080040e0b03941c0e2622400300d40355017401010b0340711640220384240420040b17102c0360f0600000d91407003281c02910392401110b858400500500b1650000c003071202107407140840d10b0703030f0020b171a404451405c00280022400c420860000100a000b01d401040d010418440c0c9445900e003200218400200045225050240840c0241c6c0c400d8110445403803500307500740c641040400207013024505500c0207050a440f0114025141c41001d031004000e1078459a502c000d000b1540c0006000028850f03c002529a0328500341001c920105070464011075203002c009425801882615410400a069201c0030030764801040700414080c4001c45040640384000c402607155404454031500e40a240c04400440102000d0883d030f81c64000980c500d07051800b04001602c80e04220821900b00e400c0b9440301d407007140390507810480c8a81200310203115081d400a44035068042c4c20115000c884c00030001c07a0500f070803c2090b0701c42c0f14009408113044c6000c541d2941006c1c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 859004055 1250 859002805 859002817
    0x304110d0312050c040807080c010c0b0406091205070209090607080106050f2505070e040c150e031506180c0703051303120309030801061d040b04090618120f05090402 73
    0x114000080b2600e1051510484409841410f51650082814444c03c0c0042003082c0c0a040b24400404050001000003403501f040d04c1d400a190114000100d41003000640229100d1907000c400100e087d403a140e4020b003150030801e4240e2140c8100400700e481c040b008254140140301550f0f80220580c20f024003171300c603a40072800001c50460100720740a00c6003151960041520303800d070300200d0780300310500f000e07442c0050b590088108000b0460511002401c00e440e41da040310b01050f218550070040c000c041d100c00020b2117000e82c240c0280d0098861512030701994510400003100d20b002d11070f080040c4107806050440d80c40030313401420045400446d00a2029041110b100d6000080058a03562007081c2d0381e0321109130a01098540c00068205604202850b0161541c0e2170702d48141140c49005207020002c80e0303842802241e8410502070941c50315040000c06980120040c041010700c00714030050b900d045101a07961044c000e13200c8486601c103215094849909690b00b48c1800305060801c4000d51102c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 859005305 1250 859004055 859004057
    0x140c030903041d0a05090f0705100c321f0e0f030d05010303020625080a15031a070302090105310e2a040303050d1512060b03030304110d03 61
    0x41c8000210000c4040030350286070b10030300400074641001a101d03000d1780c078050048203507034000000d169030a000000d559400c6860444218940182076003045d507162a81c1c5001801d140410445e0b41442614914181608c4030000c80c229040725101c5100c0351200407500721800c0c00444461501080c0c699034103c00009203e00d0305a84460840c01c2805140d544a100120500740c0c4a03401001455014041154005482c40403620b504422080381c0f04c482c9106042a024400a00f01103401c5146e1a07000860388501202c841c402c035512030030031b80810501e03c1d000803108001c9800160031107204e8001e40e500750006850319818440d42c503c581c82981101c9204059102024802800280c225a0f4440080c00d0716100880281411306c800c5000c08044180d04010240b030740c02c0c0304060031407102218112601070be0115111442c1c1403a60010f4600140300510790790800307201217031a5408503c29241c0e94802c1d0001c02a40b00000141034880c00100c5001d0b04007002114042c20703d0030210704524041d07201f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 859006555 1250 859005305 859005307
    0xa151a0a031d07081612031e230c1c140703110a0606091407020304060513050406090c0216050f0609120106060306080f01050f0109090804080d0807080109140c030903 73
    0x1028034050b2804141364088201d55004400c00582480c00c01c001c00050003c074840091054001c2e10003030705040385990710b410300b02c4e420b00c2040d220520840c40c104c600c1e80585150b0800404651140e50035030801000040c09015104443d40702103824140ba10b8900d0441d21b54a00701c1c2c2104c81d0980040e048500c083d0b041c013400501d103c8803c2e0090100c149820704c100400900541004c24100440d8001c4042d40c02818031136043c0014103070000300380c5040f1030040c50910303662501800b01320805107150f40202d82013400c120020510b40b0f00c54014440c5820103030b007210314040c110314029201502d2403090740d40001c032443c2c9560060500e10010b00c2d4200020b480411821176004240d8210385440d0b006100185e5030b010300380201e0703000b4451414003420090003032000e0b042003068281307c550184580420b9a685402c24410003021a003998002d12412054131005078403030700e0103088000c088030120000341955001198411040c880d0141d15031419440700d1669a51031009200d40e8809030800c0f4003440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 859007805 1250 859006555 859006601
    0x100f0203120103230109171b0a060218010f0f0f0507080309060106120b010e0910121a100b070b040c0503010c0c1109071d04060e0a151a0a03 62
    0x50400c540324025482994003400d0314141d222800c0710500304101308010303a410300000380081030f031440c1100d0641094100140d1703540440c99508860385032000e40c0980301e014120709c81060051640c094400000d80c40040b07002105803e004607880002d075072003600451080500752194900c20b8100d1446c50049040c400d107040a80c1e21000115007007100c400c8115406400140480c5e0b03172001e012591640a9074050000c00002c50018100e1007100300002d02600c1d4038400102d90b541e00c040342100604240c00502c09801d150700b0301c031000d011103081840c103507210040424880d4019200641c2100c0c2e075084034074285034082d03540c030161800c0500309070307011a559407000c41c1e10780c2d003031282d10505081d6860b00d0040da820f520f803000003949181441e6201300c6c07038034042110490300032440100c070490419613070041c24101000200141016000038030b20440500801c0b980181c65400032540403038407941d62203031980d512a03041c1e0b01c0c02c461107180000813050000c0d588042c002d810990070841d4107445101001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 859009055 1250 859007805 859007827
    0x70e0a0b040e0321130b220b10080a1713030804180506041103041203020d0906060326040b07030509030f030a0809030310060c0809030d0905130b100f0203 68
    0x180d40c2c1c2c411081d2a03000001e00040f40760100421220240008043c100c040c40d080c007001c040070b12988009440c001e81d44000400d40c02e801080c60268241c0340880c1100000c43d070801c29000300f01100c02c1c0280894480012501c080001341800a0f1907220241a203446c5500d10b0095503a0070078180d8400c0c02854030b00100c00a4419405000501000c0034803094410b1080c40e4401590307000303000c2500492501c00034801c1c0d00040d0085035130040c0c00400702c609014080d10704900911500762012083e82c074111603101003014513000714040300d0241117032a2144008020556004030a15685207241008000800140d80d209000d0102d0324001d040003801d0214480c0400d041841044407198550400100c01000c0741c0c0001501307411a0808006504500d0020001034130429180255000d0010301072440301001640703011914103210240540e94440d0022070081c0215040c1d000741e5100d00011071301016450028440c61100400041a4000f03140d80c3c90400d6400105010f800c80450004000311900a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 859010305 1250 859009055 859009061
    0x2090d0f06050702010605060405030c0910031a0f070e0a031101050702030f070f0f0b0d1d030d050f0a090b13020a0803030c030402101106152106060a050a08070e0a0b04 74
    0x45070088201003014a4120002821243c103904068032511050000f072010340ca001542605005054850340e400d80c503502001c2c5550350b11540300070803030480e640403035a4012a880c00a40a10383e982d013284010340342e03c00e09450740c0c00f11762500ca0b00503070040020000704032403600c012011041814114a003030426004241040300400300d10705950b004c418200078480014000400034540c010304890070604100070f2220900c41c007000c40e45016151084060035482d00000c42c0c40082800c03003100c9e03890310501c2c0080301405040361840c49514641c400a80f0142d00ba0150303041c216846604040240e413044808009031011035800da1f00014036a4021400e180200001c50065170341c00e100c40c3c1caa107403e104020110f0001001e000820000180f0000c078034230000342e1903810240b0840302c0228415240007241903100c600801e4401c000150310300c140b000303c01041c00ca0060900b51100c220941d120803d005034107480340300b844056440038604120100c2800819074100c9030000010030118079100c002000d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 859011555 1250 859010305 859010333
    0x60a080a03031b0203160b0a0f060306050702100608120d0209030d021b060a0e01030e1609150b12040201120b150c210405010e0a0332071802090d 64
    0x4030b079807180b246040d4007101404150110f00c0703200542c03520781c1c1d4415013201d540c0244801030008a4044c0401d0641c0050b03042a0341040403058100100c4d580c07818040c0240030203861500250081c070507403458003800d038044c5c50191140d003c001d180c18121b040c030340d141a41c841e8640900f90391342031101d19456074040c40300b00c1d008610303940200682e40b11203d00100c0503800c003100c14424801001120a041c0d04940801d20118090800148103c1d113031100c24140018564032009840200c040840c4e01c10307983d4040c058203580c3c941c0480303001d07844030303102d0300c4911454403440103602c03a000006005610662149240c117404400200319202c210020600560401004209100020541319103001d8200080c50701144540d6140079500c03514150514075216500401d81007212942d021542520740d80e810302c000b143d00c40c0058200340c000d1040c9480d101102104a01485a10460708184a5000850b581520300c07401150f002c2880e41702ca41c00007507000521864004d545800e0007800709081d034a00710741d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 859012805 1250 859011555 859011557
    0x60d06090e0307170c10091104050103080a0905030703020303120612010207060b090f07090315020c030c0708150c0313020d05060f0a0b0d050c04020a0216030507030c0f1d060a080a03 80
    0x146800180c0307400c0340d0721050703580924030404060200c5e00c3c44000000e0302031500ca942c4580095150503a05050381009010028140c000e8100343c000000c0062040c02020010001d0780c0c2d0040035074a8200705a22003015100103541a88140017290807814400b240c0c03074012000030078404031507150039030303890981e00301d5641a10020b50301c1c03180200382d041c4600c499520203052688100245030040c03024119a50501000e0201480f032000c48040341c040c3d9044070b00e008808005c032601e8020200302641c1c2c0341a0782c0a103500d2800b0b1114080c1550748410012401000c42c0882d8a0540d41c5443c5861010401c503c07060b0780c08103d202035100865000e00103507000e0f80c0a004502c0b41361a2100e541c2c0291843c8061040c060709032180c022022800125804c81244c030112030240e5100480107049261450740f21603480740301203062002081000015020b41140c0c0300300354181d20301d66203c01064443c200c9219817580e1a030040450010411004666540540010034032010305840344c400c5840c003481440120 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 859014055 1250 859012805 859012807
    0x206041b180c02012a0309020609061b2b03020c07120b060a14010c0f0f0212160603020301060e01120f051e2d070c021c150504020f060d06090e03 64
    0x15100c1c540c20b026034903030001720340034480011460403200d240c941200310001c000c05940d00149401c550761007080f5400564024a02c5480711503108600840841c3c00861201910508090808410b580d030050030220b1640c440c54074126032500b0041c2d02952002803051200d00540501003000702c184072418610701e0003141c00714010324109090024000041e000400c29040c40181000d050f030740f1200d2000c1c210f60082441040c4441441c002c00e101408d032074001d40c084543c004c1c04020f03900002e42805014401c00d00c05100927614501507040384000c1c01898001b4141c01d60616155010f000007481c0605588000941e21110403031103401c41c1c0d4152850b00c0820031280807034a009441110250704100540d80c0c1a284103000400341e4103000e104400300000354040341c0080e0303015000d2101d000007580c01400120600c0111400d6070b4071408107410844a140c60142441800c0c02e00b13218692041d9405040c0304815040441000503942111010181d0070b62a084041b580406c02d00540c900003101c40d00035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 859015305 1250 859014055 859014071
    0x33703060e0a151e0f060c0b1e060f060c060c04050f040e0a0b06120d0302070204140906010302151e0702090105090f0114040209030f0705010305060307060206041b18 73
    0x4144210009000b52030620308007040880c1e040340c000c0c100030403900982d40c2d8040181c06221071601d900003030360010711094000c0310300240302504481130685c440d2062410300350964403450380408a01200e80742000401c0721070b0004049003000d18942e594104d0040407941040b07090b039542032810078129417503801d484000c202009542001038400d10081400ca50500c140200411030654030000c000020381b0742c00041000c28070a88548100c9111340b40e9001c165002481d0004020707002e98002982240200d280403405c88043d4521803406005043c9000505420f074699020440304550822480ea004d0b00200110742c025440101e0b00c440350032109143c81c0d11014140108070186905a0010b070203040107100300f00c50094542c0005040d52209004001c0350005900420024050000d4540c0c040c13080c80700181c0351500004040c0b0407210241e03810f104594400d414151280c60034400c04000d40e0206004c41c00050840004400f800740000008082a60320785506a10201801e000c0141c25a00d000c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 859016555 1250 859015305 859015319
    0x311060304170c16060c03080a18021507021503060603060d051c09030c14031c0309020406090213050a05010c020d05150f01060f1412101a090306090c0303370306 71
    0x42c44c0d000340b0280c20600903c4950f82c40190084500401074004030341d40c5c0c42700b5003902024100d40b01001c0e40182c0f01c51a001c11402102c042d41c0d01c106016403140703550340c44101c000110701c0308a074407a540290046003035840d8141444124504042e084410303000e003015158030840103040200d9000f48039501c07600c080e861803c103443c0000c182e801c0141124031030800300080383c0340050082c01403440c0010204c060101468110300500205200079801410305c04005042240c1d034020b003100078940064000030130707074810800c02609058030541c1d001c500c1030502035001d840c140b0444110103000b407080e515100c111203100e9851380ba04480d9401c40030410340050008640c4003180380160715080c00e1990214a1040f00e91019005a0a0008401c0b1250001948055030709142400a06010307840001004181950804d2034100d081d000d40644070f0340b00080d0069000040008500c9030103400f5601d03080503012103080c030359180941d4010320843c5c101c4e10300c0c4140030f86d203074559060100d0750300050040c10801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 859017805 1250 859016555 859016593
    0x302060a0e1f020a0201050a09080d0c02040b0405060102060c0d06030204091b06020c0f06030702030c07030804080c0f0f040c17070c0b07050325020a061a03070608010311060304170c 80
    0x201c202c090754844840c950064001504044071602400e03c0d0f900c544400c4000c903045d40c2160802d407001d004204035900e8042e000589504424421503040c00107100900900c030445e142142c107140145d2106d00403590250100b401030444441c200c402040260f141e4007c80c040d42c110407001c440d000f01110790410b000c0405c52412010345858405041e0032031078800060498600c04240910880c40040403c08c428004c0086848203c0c204054852055490a0440d565089840303200094040e4502905403807178100a51056000010109450b60410200340401005510f96050a001840a80d2740440b46070851043c844c08060755880d2120500e450b16a8141d40080e003200c3c10b106d41403050044a20501c804030a101d164040440088842000120710780802500040c0071305281002c855000103c500d000082c1788420b6048640c1c255884000b00c1c1c07645800d01c800307005040c7d00e810744251850003000640e0003600500741b0306410414413005659503072144095044580c03025402c0d680d2030035204 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 859019055 1250 859017805 859017829
    0x4030e030a05100213030203010911011e090b16081803210d092a08010e0303040314030702010204090615020f030a0c3503011806030f06150302060a0e 66
    0x9005090704010960b40c4941c2d400169425a0030a5000b161614a0700380b00c110740310086400030000e20804416017404040300340d2210007203000032036070411090707107414412025980f40442d0703a43c4000d6034500719001c407003504110341075400e8109101e40701010542d540042d1940c80b000c03400f0344281c510301508251400f000d07100081419149400f203581c8180025040e9624140b03e01c4001c50320401c140340c1510782001c0d00788003e40104d009900803e82c51103042603101502d003204002c01000214580d61990390108440090024036600b0110010101000c065504608680005030800b81c807030051405a48240d0042c00c024030008180b00b102950420000100700e062002952921140413001044035544007000342c601610300580d144511030a01c2808170b484541101f400c4490990050720900d1b520a00c81c2a1049a0540d0070b0480c2ea00c450bc2024100d0341d100d5030701204100e096985e000a030100c440035640c0200c90707400000141e02d90300000e210800450b0307542c5040c0b0040d10200301c1002405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 859020305 1250 859019055 859019059
    0x306090501032415080a1118011208090604060e01020c041109040e07030b0906061008091b04020720041104030c2106020a090e0c07050606300604030e 66
    0x80401007021400c43d0039014000100c3c54203101400c2c000998410150020b004081d038203000c00c07580000e003054041a61607090348100841c003000c1d03c1034010048000d0310509440c200c42580300040001d030150342c1e803404a0a03c90404c4070304200801780090969040380d408800171646610365501c0c50b603410b0103801082c4c1d4007228104103038040c5c41006040e6002c4d0100b0303d80550707030b03c0c01c1c00c0b0343c03400003040034200071940440301c0070f000e01d03222100b01c0c1ca41805035000c82c060f5190045241c0000c0c003541d10070b449094504010001c00c12251500c0c14a030700e02c00e0300746800c076500300016001b0070700e0386030440301001388815881402c0d441402400100c0c2c007003202c806d806600a000a100207604584454100c0c3d1000050b640702071400040c0074101e80801c040200901d100040110242d07411141040486046041c018615610042c1040b00c038480e040c0020b03d203801400004500e0318240c25814010100d079100403c0c0402d0502c208000b00c2c4045296212540c00101004105540040541c0280c001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 859021555 1250 859020305 859020311
    0x250c0501030f0c0e1302040810061a03160c0c05030a060e060601180b03060307120b190903080711070b0414030d020c130b0f0a0303030905100209030c090405100e0d030609 75
    0x1240d038008000720480c0c91140e10a1407480284170000034580c05480140040109489280940c086800000c0219100d888040d02180c590344000003071440c1a83c0c030441c11001c00001c880355182c421103010011040c1202e4500ca8083d0100307282d2010003403107007410320600e030000c1c07507000100260f4508a40107180504115480100c18070032002401804111a802140d25880c2d89451000900b080e8071a081004811541e000c5881403200c0149131034040c011510840500c0b41d07183c003100c000c0ea4020b200c0600401c1c41900403d0340d461060b4038460b09010840250303039030142c842409680d154082d5100380354541001c504210303170f071400340700001c6180d84600060032000c4102000c14030100011040201e015030710f099003906615025a40e61000000608401c10b540e01ca01d409401801601c006803514810f0240c076040c0f00d4164421182022002402410780b8090301017040075030103004004035800d00458084205901d45030040c00b5a00e010b58002d010006045c030801403c98109034070011109003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 859022805 1250 859021555 859021571
    0xc06040606050a050609011d0405070c0c0603090c031b1a0409110a02060c0a0e0604090606030c11100c03090203150702060a0207031209242c060c250c0501030f 70
    0x580d02085546c0c0351000c6c00c0040320804120074a080d031141d141075040d00300c0c4c20700d03080001150303001c9500320180e480f60f5004540c8a458400850481b2803003500101940700c05002803001c5140d0030114412640f0310400002e545440304407090000218070006450b141001c07400b0309c80741c0c2d424001d03c440b0301c030040507150404036005d00081d55900007a250110300000004d14002c454842c240115100201030708403580c4650308c030030076801052207105010020b4a018000001da500c101210207080440000400b145120300324044c0003403460603840014940d6890604006890034032082c02400815045c0c1c0300c07a442c040380081e0070a10020b0910004610412502001a4100d010910030100d80080080e40724114541545000343c0e424401e140b40c002c8034030403031145a1582280c540c10848801d00c504001d20b91800b260003002c1502d1041150300001c00042c40d00603c54013821003000500340302c80a07a60824040c02c5146442c0d201070b1840f50401a05120303558041c0155840f40c94504005c200b210 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 859024055 1250 859022805 859022809
    0x180103050c0901110a05031306030e010504021e0a050d0803070e0303161e0b0f0108010b011107210c15140a081803131e1409010b1e0c06040606050a05 66
    0xc4222002c1c941400764075061200342070800c201c039406099010040766030b504c440300d040300900d003568865800020709110f003e0004030810700400c0d004541c083e104031900305180c40a104194044941aa0422aa00000101d5035071b000c0054466902405016a9a0070104401003140c3c44e61780400c2c0c001e41c020010203250f8076030302c1610404140c0080c40c444039046100d06200c0154401d0002800500b074260a1005070218101414106d44128008120350740d41c1e0f130015031750f1880c0c0d8010746c001e982050300100088100b0b0300d01440c03103105500080804000941e107015012405400c00044891440110403c058001c40010000b4040114140c20024880c2004060b018010580f007407200c05503620003e0060104281c4150841e403650300300905448007070300040c444117903800c2d200304440d0f00000104206200c07040822140064040c110f280c4c00c004040c166540302d034840c80c081e640c044400d03400340040d40c0040c04002c8100e20141c02241810f042007001d45803240c00040c800c105081c020401c0d6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 859025305 1250 859024055 859024057
    0x90a061808071d0406021b01020a02210f090a09090b09010b0105070b040201030e15131a220c03020a0b04030201031a09011511070f051212070204020f1c02180103050c 73
    0x40c0f5800070b104401d641e5503e8581d029004040e5001c103425038203071442d80c0d5800c064028250880039a421189100b0201107403010203c0500b400581c0002c08100b00240c0d2079041d070040990740c10180c071800c3d03a50341c0e9260740c108644440380103944450340c10003840240d91080c0281c0e071800078240307081d42c00c01075582c4450840031030103040241495075908621000721390901c003041e040c6c641c1c0342900c0e0407807610301a40b07480d5140180d000c503140301c02c007820f4245644c0c0084820707000300c800007142c00600d940d684400ca001c54001e00e0560380302c1034920b000401030b41d0700d6204c00081c1c407080c2d00d03440c1c40e1851440013500b41d03104048591804180c6c1c6408424644803091000c3c112040402c0104207182c01036003d0300c1030500c0250369881307801046000b0030340441b1209440c007124000e42c0c0340d00d80108003868070740c1c64a02208080c07000c20410400800940790a40107400440401341750300e440c00c64804034502e03003400002001079a031f13500402c001008000180407809400801c0c00d05014030b24150f4090081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 859026555 1250 859025305 859025339
    0x140a1e020a060e18010e0a0b04050c0301090506011b0c06080603031e030a0e120910020d08010303180b0d0c11010905030304230303150f011b02100302090a06180807 72
    0x200186020010f02c035580e00d108840f8600911280704805503103982038620b154504842a05100d810b14499843c541000e103c2e0320310461440140a086900f000040b10203420050045410084000250a10340e0250901030104901c520740401c00d40d440c1000c0505106001000c2500c642c009002c081c0c28100b480030b0a45036040741c00d464941d00e50f28485010010840c2143e66503440c801c8401300194100f0b04c90050000d210112007001710048000401c07030b6030303454804511001495131001080080d00445402140c0c000c0b00c1c0020b140d50351920f8901c4141d4100c8000c4001494454040b851455000b10542083c018a000203028101c0c5c40e407500c030b50b05c0c403024000900c00401146102c02035402840800c1c10745029100352030f9603040c10251100400300f04003c81e0312030714104164524640c0a040c2800c2c10041d10004c401048026408116030148005103041c00d0503000c100c41d000b140e4a0800207405015030fa214a941500a500355064202003500001c0580d4090042440000c02c00150b03094 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 859027805 1250 859026555 859026557
    0x70e160804060e2505190308120a0209130506090703020f09061303060e0604061404020108060d0201090f120507290a230304150c0f110a140a1e020a06 66
    0x90b40d102180300d42403821341c02490480c43d1000d40103001048481c01092201140d4040b580582074040e1802601c0c01c4041a103c001d224032800c01442c209103418003a69648080404001030908094402082d002e02600040d8040140c1d14001c0155503d0400c4041ba000b84035032404606140407904189514030541450b24031406010582152107541c848400c0c001d15400f20040c001c203d01c442040342e403003505a41c01c456040c10541080c0b04003180140f010b104a40594070361900b611186c05105c3c8c7c07604001e4044c5d041020045003c201010668424401000050404070b500c00003803d00d06d05261203070700701003015403020380c510494810994524040301c6a80003040d07540c4100c04001d81d0b42c1481480619503040c585191200c1c01d00008018520582c00b449155582e102c1c804190400c85907904013141c040380c044000511041e10074401550016601012141c445030551240d51000900542c600c04551091440004200f100e042c00034003181c0500800c080c6000725400900308424a000d120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 859029055 1250 859027805 859027811
    0x603011820120f0303070f0e090604050717010b1b19080f071205072d0618020a12030e090c041e0b0c0a030207060207030b0402040b01050c030309070e16080406 70
    0x22441d662402451146800480111410030302c0c400d060035102d4100712401c50108604007a12050380c0c2c0103c050403c00d000041010050b9543c01d02040000d02e006000350041217103843d125a0f01031000440c05000c0c0100d105803e840303801c0e825481443d503440319514070b2650040300c400c1c08603a400740500c081d100c1d80500c0d02500d4183c0700360402c926004001c005040c51a55044210200703405c6030007810703414010303801030000c0c8401c04422803900002041800c0e0100701d04001d035002c641c80d43e01c10080010000c0075080c404c03006800140e11020b003078100000c03108450075000c1c00c1507009200010390350410390300c9500a150810348000c5034081c903c04c015201640308094101c0c515040c0c10400942000c1c040d09803103200c2608516620880c43c8803c40140c0720303000d40850403500003c0c0200032a41e00020010711565a80e0078840a0141c100309141400005e02c12a42e10303d03028000380d44a21050402000b2892030114511fa1f04a4050000d05a45052044a101503640084043d40c407542041c404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 859030305 1250 859029055 859029113
    0x7020d0203010213090b0f060309190305040812030109150f06260405061e0903091504080105331c0309030506090d1112161109010e06030118 62
    0xc81d0281c410b110071400032143c1c0304e202150201041e80a202e41110a644030003294038860700f4810948000c0d50b07113040c01d0307200f50340040c00c0c01d441107103001001d482443c0c02401c0513600d4a03407515108200401c4040d0410100060100003410303c40c1c4040c20484030030390b02d400341c640780c01c5102c5288036009110404c100034030901d6840c0c489030040403902d160055000454542804e106894081c1607412040d060501300c2e641c40901d05c0000030034001d02d850f40103103150030420000c2210342d00c000785030b000040809120000d0507031002e1059911401403945284c000d850100d540d01e04502c84801071550300801441d038081d180c1c8441841c3d180c02d200001d14455681b600d81420340c1c4051807940300820f03a1003a0300c108100204080b488022200981d00c1e80300c09001c1410700682ca5828107004596095818049184811450302d400100035010b440250b4000c0350100c04070f910460240c100c2025100600f00380710050500f4400c0345044104100c0c82840c1c41c909170ba070750f0701600900703070458038004c410400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 859031555 1250 859030305 859030309
    0x40b0307050f040b120708090705010f032301050310140105120109050a032a350406030b0a0605091305070e030a0f12111f0609090b01030506060103060b07020d02 71
    0x444012110b54403020b42c0703803a40c6814440140d0320088200f10824650004103200c103000340302d600d01030b42055018019590410004444100b515500481013549405921400c6504d400002d9183c46110360f8402896041000741842d00100c0c00381004040d02d40b0b1400d885800c0114405815624101c0b9002c0c2c880401c03074240c501401c2c0d0300001030306078022511210101078001011201e11200b4130f290040780310007003445811101e040f400290601c002014601f001c1d1100f00307910090016507070052104690501000c03542604150040c20129a860022a14030f1500d820408014072940c6801c0c0c0c9080c980c1c00100c1c5480380c01001508000340c807a00401c03002c0e8003034584600990009000c170744c000012810898074810508105a0302c1d00880520180ca080c46955442043c0403004001c00b01610201c00c8411300a40f142c000d02c00e41540e84d80042403c004030300070004403d020b0f02c200c00655045080040c10310002806085c1454505107003008010301c10000e031910650112101d80180020b400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 859032805 1250 859031555 859031557
    0x3070c060b03030a03240f092304030528120b1c060902040e210309071701050f060108100b03090a1b14010e010c020f0a030c0914060312040b030705 65
    0x4501c0e0303450301001c12462100b59040d440100614641c0c6101321140042e11490380c2220500e01402e801c0d00500d80701449020340d150010301642c079400421354107400d140301c0c92000c030907800c0d6003c800042c80040d210104000681c0481c1210020603004940020345400207441e00c1e000d0b070180d4000e60740b43d1070410020364400d1903030790614110b103000c45001700c1c81c1d1a1010060020f1201244a039140940340d0020b29400640303000080c114941d101e5010300c0e540c640100c103400003004200326104450300491320b241500c0d03504411607603041c004509807d00f5100300070680070081605041040080400440103400c00f0020111101c0300d55850307803a140c401820b4109807082c0c0d00170707006190350b90b030300e8100895141454044682c1000c80148081100300111100e0b2180d4076100c0c0000c0b42e818005016281154001c070112600405500c1415a60b948143d0006890b621120f03005942c2c090219082011705400380c4d1020045003e01406c4400314000025800b940c0200800d40d43c0c044002408540508 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 859034055 1250 859032805 859032821
    0xb19090b1b1312050f0316020a0f03170c07120b060111060601050a030903020c0301021308151015210605010306060507050307140a05190c1e140409020a0e060f060f03070c06 76
    0x4041d01c0d9075107028508214000c4080204078009e140a080002e1080070703200d800f60035240c1c41503003c4011500c0c580b0b0280b1781d81080c3c100c280c160141c200c0005210a07548a0b032030803a803164410554500e031410002d000d4070010020240e02d500b00d0000c000d0241c0c0d0140485028000c04c0c1400610f8000c5802c049107451003a110140e0107620000c7e42d04680d9030b00080c51801c4528000468094040344d0030943c10070b01064407855007100c0822001d220010021004940b010400d00d000c05d101d02008000e24604034040c11003034582ca588506c00e1142d03581c07500484001d01481d00749a45490080e69689030b43e407142134809032400018074480314401006105010100f504402100c05d080b00c0592406240406000c00719a503084203500017030715408031b5070301d403c0b50f0100402018440740f80c1040b81190307480101903564030075640c5190341d0050341c94810003000b40c2200c0340d203901715160410900842e8101d0700c0040e0b101d4501400114055844102200e81c421030303a01d070074840b01000e8030303215002d00096 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 859035305 1250 859034055 859034083
    0x50408010f23130314070f11120f0c1003020f071b21020f0d080c030c16080a060e010b061b060a092a03061b0801050411070b19090b1b131205 62
    0x220400d000d403a0023101407400f42218040080210841d105685248a0128994079000754501c40e8051424aa100003282c070035080247c6001209441e00099601201046134035004003440001612649403400015085144680c0352559150040384105042c034000280700b200d08020828036034584902210003e0ba0100c03041c0c0d00c0d0010fa4400c9900ca402049083d60759100302d1100001d0301c1e020f00035180c125074051003e405094582d40302e035000b03411004503081c080c2d926101d0841268496100030043c0820011001c1315036584031011909107000500400b095506007030821000c5020320032005060842080c1d6140c11840010b03601d02c2d1441a9400540b40502e42110550285402e058039648000c0301c0d5a6030f480b40c8c1c4c807481000200c85043d046002045020f01468000510140c00d00740c0029240c4004d00b030212020b02c030321043d102241c000b110485540014890203000506881e100350414480b06424034500d07000e010a03855980c421040b13002c60301d40151040c0b00d000c0c000341d000000d507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 859036555 1250 859035305 859035323
    0x1e07030b0a06211103011116050c09070f030e010606050f0705121b0f0732060c03041806150302030402062107090602150115050408010f2313031407 65
    0x70100320380314080154141580c1d00c0140900118441c80d0600c24803c000c54440841800e01d00841c0e01107440e192104800c8442b84502895045c1030395411003074511076801c0f652050700d03a07002040d00030251031640d90240000e80c10120103000c2d0b80c1d000002d42e0809032224000740c1c0c8803602400c3c4103151580381c0907130910a400000d03107411000c00c0340e411310321620070503012140008840705089541e02e0381880380100482da00d0305103900074005400003040c641201000190125a00350000d20705070311004c0a1070055100040402109194031140340304180d00d0780c01000103034030f888041c0b040c4c021900d030138404042c0e00000140031542e4002c15205d1440392001030200100030380080d40e00d056016141729002c1201c0c01400180584002004d910340c01310710702c0181540e46000001d24404000b1100c200c103018040c00040b494407402d10604202c2c2c032081c20007013031080c60000000181141584d02191013a43c400800c40512000303007615900a40c14602240c40c200b0140c056201401498402404184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 859037805 1250 859036555 859036589
    0x30e100c09090513060e0d021c030b1203040906060503090d0f12050a06170d0504090b010c0b09010c0806040912120605030f1f02070b0705130b0415021e07030b0a06 72
    0x803451a1104180341701e0310040101001104941d642d43c0540b80e100350050340000100c0c1404841c120010800b400c0e2802d01161003a00c1500103103c0c4c04034240c40b41c039158000700301082107084500a0200418103410441d281d0706140b0703c8192a8a40014520140414400c402030000e10a00500c4484c06964808204d54105580300c0d1006c0d1081c6d100702c2c0c500b101c01e100994868800812001e0300401e403030722028501840c00a607807001e8503900040d103040c0302c00301c10141d012400e83c007130483c801c0300814000501015032050103050b003172010b0400d6002c0c91528403454002141032002c60030704111070500f0440d04c600303c4484409001c030b580000390140540e50111400020001d010028100d14200c048031201211804070200c0c00381c44d102400d2055044049000c81c0e01607c001c0030940030068440003915111041c01c542c940c49030744950055440407200e01101a0706000c0b80c101d2601841e20752020076a2800026a01c01780d5000180101a0b41c04c08512034035007952002c0020b041d01440e080742c03a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 859039055 1250 859037805 859037821
    0x60809100f020c010e0607050d0522050d0906021203150307150e0f09090d0503041505010e010810060806010b130504060303030c120204060c030507020f042a030e100c090905 76
    0x2400c0350716261450360030611704000e038031000f003151481517101d030f40e60a050940c400104809410060071386503080000c891204103042c42c0c03440c881c5010340160000c0c84448404040100342c600302d5071001c821508510391407001e01c5809001c40340c00c140c40c29046458280d6150002e4105503040d40400388420400c4280d01055421280c6e1034030004003120864030f5841740748144a01c41c8000c490300c0009400030910019410300074030103140c10601071850581d802c007810308035100721071003a00301108020403a070040002c00303401c00c10580c44407400d000510000d4902003c05503500b02c180a82003e980d0081035104650310182040c3c001010001e00a0011681e40e041c00382c01400b8644080300010075100442c156a0705a000701c3c1c0859000d40e440056400700f03610100e0b100d40007030008a03413116a44450b010180e96074000c40045a2519800300100e0341800c0c0c1a42541c01224251010f050a0400b14a1100000715011080281103d008210f139004000100c038000280d030011a480752511003031069074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 859040305 1250 859039055 859039057
    0x102011407031a0108060a03030c0515100f12200312120906010503120f030c040b130509130f0f03030912050d0b150a1d060729040309060809100f02 65
    0x14200c0c50202e407640711203c00458074680e0464010380c001c114620200b000911075048288010f0040c4151540e454442c0c1d4012a41c24094400e09060b840701d030030070b120b5000c09041580003000c00e01120f003500c0e40b20341d803095001d584c004040b0100b090081c01240e515142480201840354811013010354804001c036568224010603184210300c0d01c20032001140d01d04000a25002400d5081060703400d10b5011030a2241d990300007440c1400d01d200500c0b0002d42c0c1c808510140584410501d0802d02d503504101c284080b0400c02025100c40301198013602c0c0204600504a40300150403955200c061202d50800350042c1c80b141d040108200501c1c0209007425900c000900186030403076405019601c0c10208100346041ea4047d02c0407140420050308050b50300620000585482d820a0b140842c04080001452a00720700002d80c1c007813000c0320018194100a9400006002080c4007c40040c241518000c08020f281e009840c244440040401c004010401203a946c0641003001406603454100c0e0500c06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 859041555 1250 859040305 859040321
    0x3010f020304140f3a0c0516051305040f020a081b01090614090111011107060b030312010519082b021203060d020402040e0c07021905030d080402010201140703 70
    0x83c20203145503200701504040740c1c01061505501c018255070598201302507400d50724100a4807180c0c40509080000da21100030001c0009642d00c1301110f24180b414140d003003000980b41da00d603103403821a040c8805c0d501c1c0715211126080e0620002505d41d1240b5055510030740c56613010b948280c45282c0001d941d50001050b4052010001c174030640fa090807001540c0741c0c60385000c1e56005c101120f0f0f2121600580c01d016040e031031014904011080c00c21414a070844009611004031300400003611010f1003000c3c001c01c800034105074003d510b040d0000118050700141806918411408080c171460380401c00300091000c3c0040d00c1c242d5402110074020352803c0c138103420102904170503010f01990964000714190f40d003280300c20305040c50350747c410b010401340e00b80c1313070100b2640260309010215421a008910320302c80c40b07403406200d41c1c9444a004200405418852200444000140a00c0320b603d02003150a41a90203044c2170303100c0c1d190380c030041c0d0140c444401421008043c1e40d04001100743d1603004500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 859042805 1250 859041555 859041563
    0x70213050601090e0903180102100c0201051f05030601030303090c09050106080103030809010920030304031a07110604110f060c060a1e061208030912030915010e150d030e03010f020304 81
    0x403e0742c0d901d42500300c01c500d013281c02d544075801c01c0c8043d6040b4814007107040c800610502c1a101d400280d070304900116154681c0d9100181c0d03440301000740e40c0b80740d441d014660403010302480346080e1501d40000d0b90b031801400020100754071081f1800801c29006000c03c082c114100c002d004541c5c4130f500c001d01d41e600c2444144c0004941e400803c000034010301c229004280c000704007407250411122841d030181401e0107503036090300c0104400008550100304031070b007144a08040c00b40c00d04245c80020b015441c41c20f00d080064020348203110000e400d280d41c004550005850b00c4145250ba540001c000b03009144d228501030164108104000d9543e511005402c0c901c15034a80c1d0b402403800d114011160316008020360b072100c4100a2011512502c051503005c0003507400ca948298021189400359001525868019808074402180e100003001429001d8088480c42481c2490300130803030f445d03280581f540d080c00740811000340700034148110740c1401c510001900a0103c605071600010003540304a406172 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 859044055 1250 859042805 859042817
    0x3040b0c030c28020d020f0a0f0e1e1501020c0607030e01090b0315120102090a031a0703020f04090b03010f0203130b060f0f09180607030204030b062b08070213050601 73
    0x1010403841441d0f051008100310110340c40c3c42e03180d0b4203100952600f424183d90040312002c07460a680c0d00d20300d42001404000380a041c115103403464240c9003850140c5040103a001080400940010f47c0410301c0d40011000079040c4c090b014100140c0c14030360441070346500b203980054407006050700074042d00145c40080e41c0345d914843d035800c3c00600c54001640e8000b02e400040304440800d2404080500c0d090700c040f400180b907c00c603080014402849540200c603804110000251031a0304072803e140d0182c4d036800c083d4580344688072112071500c558003a4414507507481c5041042c50300d0035071007034416184c2010119a6030900c0340c8400110410840203e90740ea0524000603a2802c00b20303842c191704440504009941c81c003440401c48454001041c1a1911951308401482e070380c003c00c0b80d5030042c0d402e502e00603941c0313056003884020244010b24150103031f154603040c030196520406154200b0080006003003803800003442d00d502c8c640705182000c1e40c04100d0344c0e01102100450341c0424021038003602c0700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 859045305 1250 859044055 859044073
    0x1a011502120f090f030f06190902010206061309060608010b040c090f0b0f07050a0819020d0e090a060b0301081621060f14360a120203040b0c030c 64
    0x300d0355000c10202081d203900040c070a5141e103000300342c05030000c80c0c80186941ca0010034030300407901d440906a0b12483c00d81c0840c0a021a42d90b20300f414174401003890009000644a940004c0d41d1741d04003a2500d40609010940a504802160f100011341903201030140300440c2d4540d00c0d240030704040044a0700c1240342603210403906000d1554117049803103110700d00103542d161204100540c2c10401e902c010540d810851440060b40520048070841d2154403002e072500350844416107440054043c8106550164803e0415180c01000061202008803200200b0381d482062030000f5040c20391040354680c0c408000403074400d2010401c1546032b01504808103440307586100409c1448003101411003609880319a80c80883c049409c92120100c0d00355020451450114020340980d00842e240340c0d1034141010b1072054065030469814000503000d446524001184603d1600d640f040c5400070720a2408000182019009000b80d400410141c0c4070141c5441c80bc003456912903200c3c2c803021a940c0074440c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 859046555 1250 859045305 859045307
    0xa12091b0506120f041407080a030801050a030b0a1d0f030912010612060f020f041e061103180312040e07080109061a0c120408030403290718031a0115 66
    0x6035060f0b110400c1440b00c26855020310a0200c140c00780050f900c5841c80c10202400150030081603000308001c100411000f202d5081c020001035041e00500d01c0b90400342c0e01040030400c002c40c0c0c0d58000e06d030300f030001405004000c0703540c0c0c1403035201c207140e8000c0c003505440480c41d64020004d0540420261240c107030045162081c18203e031514082c051416544141d28800300e4207a40c000d0511001d220340062409002d44021050794200d03501c5401090344686445441c22429030b00840107100d40c0c104404c0d000e1010070308070385900401c81c081c0c072140c0b001c070106412582c0400c1280d5840c05c45c04141a600c540703401c180b1880400880f0f003080825080c41c00041d2030000d03449188101c804104a000d40310b403040340002450b611460000c1d0461107100030200040d400500103100400a00004590782c614615180918540114030290380c9504500c6809d085160f0907002948100d403450000c01e10300702030700498805111a080a0300300301049900b405180c85000003581030750f840c1d11114075540a1301034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 859047805 1250 859046555 859046557
    0x70b060301141303091a0a020f15010501050f070f0f0515070c2009190b06070c03081605011803031103090718020c010e3a050a12091b0506 61
    0xe100b00030654054000303614038621a600221081c401d1a0200030299144e1944400e07201d130b441c0e80c5558100c006041c00318940c042103102222007440024000a030320310040b4610880b41445503505001c4006000c1c6406952070003201c10f0305a0100d10040000c441e801c00c0200c94130302c5901102d403441403a5808200e40724044c412807203042d180d59600c0541070b15659504009950358080c20942488030042d40060f034030004890b2041c51184000f200503a040384c1e010003a40d485c404400e0089034200300c19004034001304840f00a8036045403072941c0d20701c0e180b10008c5603102c1e115801b84c019460709404600012000c4d1510140f00c0c083d0b503040c010a601940d00d00c000d0b12040d20111680d91041000f007124042d9008045204c500c0c0605c0107003003000f040521400d4603000d40082c2090303001303189804940c0360000f03c106551041c0b00803442241c2c22201c0400700786545d4240031002d01c100412071500c0c01d4071542e00c0c0c01c100c071000c100501c1012100d162500501401340840c10b046120302102165a0038880 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 859049055 1250 859047805 859047821
    0x209010506121303120c110105070e0604120516120c05040b011b21052721010f11070204060509091905030f03040804090b0a0e0103060216140102070b060301 69
    0x1e80030400380c9900610f05001c3e45000422402c2c0040002e5611400303140b4811144004d2841d16080f08a1b600b511100d801c55000030184000d11600c44141441a1200001e690030307242c14150a001ca204c00b0b0410501d071a05001c80b6a07181507503d04042464071011014042da24800d0340c448202c2604d03102003109a0b03042d009144d0001b0000c62500002110100c88440418043c0c80500c0e4803207200e4400b2001c0c9010002c816001c00d800280340c079420080b0441105282001710002d0703903000e0240707000800e400f0701070001d400c4648416406844070701080d1300c00c02c4000300c02003082105060010700181c498010364001d80c07046103003243c0000d00d401c24420f0a88a100088040d119031010010b0807100303440c0b405020341e56848180924030218500308021030203180103864041d00e452408480000350b8507030028480c000e44100d00200100d03440d038806941546c0d480200540c0b81e03030504402251648424034042d08101944194051001065004080150161b01c00e080d80399540d03024075090300c0c525 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 859050305 1250 859049055 859049077
    0x2030901080402041d010c020d11012307030e0a0c03050105100e1b120411090c090607080c2406011202090a0306020a1e18080109150e0109050105130209010506 70
    0x11000142c010324240c0c3c40112008072180001040c3d0a03010b01e10340c216062004280d015920801341c6400481c0c000680c01640e41c0d0b544c0090041c000c0c2d401000700028600900020a4820f09000c14031942c042c1c5c00502e19421243c0407200c86011302d0600060021603480b0640341075184c80045454800110403070402c0d1000340700c0301b10868940b00e080d80c030004041e58000c0700d50201401001c1c20520782c0b400341030189000e071a848603902241c5003004207240c0d003d080b158a000302001948800d44528041e142d0454200a12070344883c20075403041c0c141410900b0083c40e4000d40044200080b28800303440d1f000c3c80d001e0740c07441301d008824940c0310224414441e42a512a001d610f08000141e80e640046c01e180c64035141c1100c2e0b004d031309480100c104902105840121707540f40b032141c0e4100c0c070246614005056050081c03119010548440910749103144604607150b894034240039800d82c094100e00810b40e4801d000304010711b00742d24002a20351508a00300d21a03d01e0500000302443c0c1801518501c20f82 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 859051555 1250 859050305 859050317
    0xf0f0c0b1e13030501060e01080d0903120f0c0210020d0f0302041a03041707062f0703110309030a05010501090c05190c1115031b040812030c040b0f04060f02030901 72
    0x4140d80381c84140c0003524801c0c52141c4602e00880040c8007801003038000c00b582003455003a941004d0005060180040b044010046448010004564084950108131101d410900c800c0110720703108440d04e6414a5010f0b40100e68000c4800600780d000491014044441d9116629180c1900c0207c080e4880c1e1303c82e0f110a101009d000115180c90300004580141c420701c004032000041e0400d558040d002240103032000e5550705110400060302883c10101401d0051080618043c0e40b40d915104e401004009000c1100808480090400c00c100300c0d20484001004c6071045200c900d00310b07019140900030b1100c1d6900746101c01403010300540998040992003030003111244840c8804031440c4800d418180c4040d44551034454aa0b1500b080b940b00d01d03d01c41614907507a191010320b0f030581d03d28030307130100c040c0309810002004001c5011864081e104844100c255980c1c80b448207003e01d81c010f03134007c01e50601c400603181c40d00c03142700c0000340201c95a584902a45d49040030050b82c0320b028041600f800310700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 859052805 1250 859051555 859051597
    0x5010605090103150e040807290a200315011b0b16020a1712150a1203180f05010212040b0306090718080d1d03100b0109030f0f0c0b 58
    0xc002e070040b42c14a01d4880e00094085d68884c114004002c0c196800d65952a0001d00b81c4240044528003108202c81e6203401c0154000c41d00d400d00d23414100420350b840e410f0fa5884200c01411289120a03203680b0741c0700c8101c0d100e080c03003c1c0c055203207030800c9556408242c02d1500340c0c1110822042c08048260088001d1245070b0b900d1038682c851250719141d42d0114020a07050300001071130300a42c004000515511141c40c1c144040c00385480200c0540b203001345186416031600305a862520340002c1e40c90305c0c030440e00d5a520520b004d039030740312840d415070107400c031421000319041401e480020120740e400d9013120041030f0030f0340d6804c0061240d8051782c4100c040c2000055040d05101c10307425004283d5207002e201400400d0200707101c00809802c40607072074011440c0d81100d1540001c81d007600c890204907403185030303001400090b5211050b0304881e00c0076440390381041e6540c1c010070003180219001104100081c0d05c520b0b15000343d544291088882d0300f0200d0012500c45400c0055481c40120b903070503d000c440c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 859054055 1250 859052805 859052807
    0x40f120f1112030a030603030801080a021e0f0d0605060406050613052b0308060310020a02150408041a0903100527011d0109060b030d050a0806030a0f0506060109060201050106050901 80
    0x2800c050110340c000300038031102e40e072081c81000148088003503507070000380b00b038111310f00200040410b03400709110ba03000c102100c0240c4c0d106c80d00c1c3c1041000020380d84240044920200340c091241c03110580d840744034655079800307000160700444d100d900c3c211010440681c40310100b000f00c0c01201000005480420424070440c100010642959a544611000d02c10441031048500740f602c80001c13000554110117100e8607040170407528903038840044080d41030034041880256103800c44202c2081800c05c28000c501400201c4080341c0280c514662000003450031800404500d42c45418200e0082c403500c400b08107528040d03c03c032405001c045581016001c1103400542c486d40359405402030039580d03900d0303d10210b2000c0070070448110880c4004a41d0b00c0382810003a049860075031101703000340c0080318208c000f20750010880722403c60034186002c2c01d4403424042850300b101d040780181540004110724090000014107a44200c509a86040c449500d8690407800d9070f00a1141d07001191003804002d48079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 859055305 1250 859054055 859054073
    0x9080c160617060109090f0902010807140a050f0405030d0507050c0a030209061002010f0e1b03030c031902212713020f130329070e060c0a0c0b040f120f 67
    0x1c4407052510a0782692901b421008403850890491035140d9906000400c558000c0213486d032086543c104840341d061072452103102c0e446090450740410800240c80c100c000009815100601406030488030b64200a000142c0b060340481000d0746e45120300c03982030049142c0102d050041e298043c003000710700d4503018203115190b0081090315095540f501d81108104a4601c80c0040c2042c031100100a492004d1074000c0c800703440079101c0f90094000b0413807420f1503000002143c030b100044e0f030103080191008020032420b00480d00710040d581e50742c030040b000480c2c02c200c0181990210f400000403c441e2121403c03648600b42e0b658043e044942d255800b0840c0d40d41e54064031002c0c6480429502e4480401d08078041d100f0180c000304c40081248140380c2110201c00c40041401690000080c00c9040c060310141100d40c1881d04c540c8035080025158156010601444244a0380811040119511416000640d402a00a2060890b8002400690f110300c94185030311403508400340004ac0115521a03c0711 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 859056555 1250 859055305 859055311
    0x15050a080a1409030a0e04050412140d09030e150717030703090c18050709080a0f1a0a050718050f1306030b0c090414070203190e0409080c160617 64
    0x4540d40c0ba9056a800c4003030412061180c0f404101071503507080042c2000e803000403000c03070141c081ca251100f00000502c11070301e80c4c4540e540314106800e50045005a8888030311400041100c8a401c000c2071034101501b200301e182c4042803c54101c0a01d80380444902c116005181c2d010740400a640084492080079100960b045013581c940450548d0030740d03c1e4888403103035680c040303450a801040031a44682e91071040304d802000d14640580c195140c01448d941d66020b00354081d00fa91190b201d10002c1040901591040d8152801c888501d8036001e00c000c001800105c8a0a0205403e013602e01c18800c8110024400e4800c02040c00422003004003d0100983c80001540070480d86c4520110104a6241d1804e200d80104c4440c1c0d80e841c0065028441034903901e00380d02c543c10703c00806000e641900401580c403654480900381c4007040c454901150401c2940e40c030603030001d280c01d0203e000d00980e00b00411504508000300e811042540c05048248106485014009190780000c03249015440c1c0740a90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 859057805 1250 859056555 859056571
    0x203070501081627061d1c17121e06190905041401140106170606090d0629030105090f06071107090f05040b06031c0e1f0c0b0115050a08 60
    0x366549500320f2418000145170060000b01c0c41c0c40c012070140e00310b8414182c061381c006617041017180803015141888000009802001200c1d0b00d81e1b6034050f2002c010a07984d5000c10004220030b1030500103210352400390392103112400a80d031540010031500306056103804000080410580080ca404114002498040c1089910a502c041c903030300410401d0082d00d0351900d08402038680b079403400c00c000d00720441c84c1c0c0c1004211100c0d04c081026996660050700c0c8641400d440100c02042d940c41e10200604841103400162080c5041c050b0701c840009403603254170b04066000704502d07258484541d59803a01d820110580703a0008002a9180b4031036014200ea102081040715841510ba80804c400e8801203104442002c1c0e456082000703010b008031308550409030076406015800781589140c1d003601e14003480b1000307000d020904407840743c4480ba4500400c148a071341540da10143c80c3d00040c001207469905442800000e0300124448821111210926059444841c50007042590995071524000e00c1300c0303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 859059055 1250 859057805 859057847
    0x2409050601060f18060906020d0e0303270a080304090e061003230607020105071b0f03030506030a05031c14010f05040911040911131808030903071208010302030705010816 75
    0x106020758820013480504010b499511105042200c02441c11002640300420007a80c00352400e015203010040382c0703001c004401503004c8443c09016a840c40300c1086001d41d0000044d8400203107264010014006594041c1410b001c440d000d5034055540b440e041d9680e02d503140844001300001344424010322113410b40e6101d4016800d20901e8010f04000045aa05015135164400c00c8601c0c1ea100440c01d0700c84035134040800d920309090311a217040d80700c105401020300d9620408505035039410040c802c0c0540d40503007140e0369001c000414241d000342ca80f0702405020704008140c2481104900d0041c1a24181130034812500d240c0b40401c000340240b00c10070307125010050984003c80d02d881c0540183c890145c2a0a02c090280006000070b10354204c40311a8514500112003408280110207040f0058010b150140c03240c45400680d4154811100c001302400c0d100e01e00d001000d904904000c1c1200c3c022000e0782c070000d6a843c0155880e1500700d85050142e0701c1460428012409581c051403144500300f114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 859060305 1250 859059055 859059077
    0x10e091609060f12150f1104322202040e011e060e030c040207060204050d141c081f080f1515030a080f070f2409050601060f 55
    0x20312403524040d00040701080d1610024414030119144280c0102040312800a02281546a02d03100c05100000c40c44c0709a100c40305028030120715002850600c0410a41c0d030f564560701d610000c0c0f1004000d105c255400f41080040d01050030280564a6081014200c01458011300010104600300d484000c10140d0742440041017840d039404507180a808015850118101104c03901e0003104284c0e4005010041d50540d000c40d2a280454500e504030019140580c403513046152100190180b90851a0071062600c192002e00101a030360369214070360882a80d203081d140d80781950181ca80040c0750008240f8490200e05000f010840848480300303120841c5e0600303525101402c2c00d110141500360354940c050681e00c500d80d58007000254002a0034900c112601e041d4101003910340614410262003500041048080e41c03100300212030105900000d8010103050740c1c42c0c1204a140305240401600701c02e040920940c0107603214207061582c22400400090b0302e8000101c0d41e004542c0d004000b046155621 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 859061555 1250 859060305 859060333
    0x411040b131206050403031d0c0d030c060c180905070e0d0203031204080d18020319030215010303053606090d05011104052404140a031e020f011106010e09 68
    0xc006142c0e100d1500810141403c0c2030040503200e401c09040c0e03051018004001d46a000040c03002000f2070242d600c07160308a2a41400d58600c0c860312800b030306d01030410150741d0609600545100301c2d42c6000396031342881030710b8806600455070100d4a220100300032888080c071510342100802c1c3e43e03e10090072640740c071500703007815504503c058400700d41b6a900400c4401e04100c0c0c1c0c0c090702c008100c1c4c00c07901d150644c000e90006a6107001c0181000407030801500c920741498802d12a01d00c0405080000001c0c035656490000c125900081c3c00d8040c1d4103074411004030060700e0090009110207400440044d82041b4010011964081c0d5825507106101d0707c4410300040c0300f070140201110040903400d807079525040c1400003140403100780800944030240c0001e40d09200e841034505a580d807840221500006001051b801403081c1c10150119042d51000407444102110400070b03580b0075100c84338906503000054078100c54000740c0e0300301500200d00500003400187c8945610180810864200800e2140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 859062805 1250 859061555 859061579
    0xc09030d0905010e03030c06010b0711090c030a0f020a0831150e06060619030921020c04022104050a020414090d1817151905060411040b13 61
    0x1401004907030500c41c204415071300891111400d4500340d0243d460031010703001d126168001401007a203204030100e240000d000c0e0850701d640361620050010320700c40c00c0100480005410445a500d109801d208100d208240c0c64000d50b031424001d0384501e41c0702e403500e81c0f41e880000701800b46e00c1d086944101d04c2c40103070102803140740c940c039000d07000d071f50a6481c84070071300015600038bd03003a15000d510107400d00c01c131504d0309002c5562107024a180d041010114100440107803c00c08005040d88000c07d44090380c2c200e01924615980c6251380071140c4002c40750080c00284e011307601520504e84101e44000b5860340020b1041c5034090302c40c1d0103a88000710182d0000d000c036584400100c8c10324000c0806c0203015a070810604068a4280c00c10f14078503171040d095039850689600450500700c41924820162100c10000444d5008890000042d5441d254034121141d0100c2001c0c01080d81c1490089080e030300b4144969000540414241c1e8030b4039080c80c003540d005510410704804007034400c400008440c13400720 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 859064055 1250 859062805 859062823
    0x5070f0c06030b0f030a0203031b010f060e0a0b030c010e010320040924141012050a050a0b0a05060a0509060d020a030605280e1f030b040c12110402030c0903 69
    0x41c400103030340d00700c3c07009204150b14030440e4a030003607201d0020080580e80000648030036022041450104200b00e88085000d0240c00c140021020b0800c08040750581091080760702c5007141a804001c01c4e1441820550b4900500040f14081110a461000507501c40d41140500105c0e251003c190b80d070030b0701c2088690784d0090340486205607071859483c5440b100c03614200ba240c14182600c8045a0900360310f120160f54851100f4400c1c01c03810380c4200b03043d004e00d00c0c12680e420520001c1050345403160442003e0321040b01c4140c140340c58035072241d600e440e000001c041501d401901c0141000c2c440141524036a00c418a400c0e4881c9040c058080410f04a0000f8902d04400da070380400c00c1450035060005140c20b104101502e070b84911501c02515020b040740f0380849551381183c0e040c0b92070360780740b095010b414002d9045801c1c0302140084140019200901d001d9417007110441e900550b28001d03074810400e1103d0040200100c4d082c1d180340d80ca0940c025542020400b2000380c6410410000a03290a51070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 859065305 1250 859064055 859064057
    0x40210050412051e030a0915030905031204050c0312090402030901151212030c05070605040201091d04020f0102030a0807080c09041b020f07050a061d040905030d050604060608040305070f0c06 84
    0x320380b50044c45201071400551a507680006500b0304a4940025080d05258011403101c490011180b0b10481c3c441d82060800b55045030940b5079400340c80b080c0300f107035000c2210255107901c9443e020000034200003030050341404403040c010b82001e82100070040a0760016103003804d0b030340d210010311006c6408282e4800041071600007284064242e440c212001140c0c00002c101814602001c58501541042c12290881c0c0d00a80000c0c482d0b81e9403006846008990700302c02c5005031400e0b90444d03090321242e5514085c1d402103d039003080490311307001240d5078410044200001801540414050b5001e502100c0d045424081d9403800e1100803408030381103d55014164046800a85078841c01e1b540604c91881580303002c80280c08064100008194404200e11a8400300070f1040700c16004903100b00d5048940f241c0c0140213120b8a4900c0c14415641e40001070b80c400301503d01000303e0714510306440b0b084204d0b181600c1c0d410a42e611510300f45c405400000040e1444500900d11600241040b81c14101808035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 859066555 1250 859065305 859065313
    0xf0501051608060405040201210e06070509130b210703170405040b010807082202180613140103030c0305071a09071d060f0109150206011a090904021005041205 70
    0x400d071801003298001414880c06103142c1400e001c0540da0040840e00c1450b9010414002940d4040100c0b004020002482071140106414402c038158000b000b0070705104119441c2034400c0b840c1c00315000700c80d4203520090340303d20362450074a401505401d24911104100313003503030303111035403034a4414644140080410300400000340501080c03401d48203c501014007031815101c545072012014000c100d002c1c1c40303074004100007007100841600180e0b1501000e030f405040841d0b11074820510321040603040d500a4400d2081c5288031101503903034803981080d20310003200c1c90b845918580342174a0002c6100710581c1000010417180d0003003200f83c0d240c80100301140310994907518103406c0e0b141c1440c0443e0801c41e1380d49d0b052002e502850031480241c41d00150708440e0100d401c1e89007401030f00c98482a501102c011000b0100e20403c1c244c0100c0d8483c100c441d01c2c02c100c00c00f946023002c1c03074407280f04020f07010742e102c10311802040150800c1032021108541c0f81c02c0c140c0c138094949082e0300181c1400d54003101c0942c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 859067805 1250 859066555 859066591
    0x92a12070b2a0d1413030c030803090606030a030509150d02070506041101030c0c141c080702100605091303050c10061401080601091806090c020f010e030c0307020603040f050105 78
    0x40b05840318a00c014000040e0049418201c070007001030114410074400d0990218204002070200300c03258008560202a04040d40e82d0382c46c0081145d04200c0e4940843d0142e03030001080703400d01055091001c0c2d8141c0d2014501401ca10400184120051445211210610041d00405440d20090541d10300581c002c202078501460041c2d0250481954181010b00307010181441ea9040321640c041da607807114280d4001e011000312549031146040441e20203030703ca00c20b40c141075070700a181140500215803c0c3d4402e80000c56408080da0a43d00c5640d800000300c40001e40c1072040d05011310034582c0301c5c1c5080c80c600a01e50b003610341f41102d00703680b00c041c1a64070383c41000300150380002c2080c551002c7c00c1c0480319282190001e02a240c0070f00c00e801300001c08110010a1b101e1550101c1c01038010710104012100122074001e5880d204240002c10035071801c1101012902c001041c0c03007403114590025454440c0310b500b8046190401f8008446403a2042040c40c00644280100d9110300c2540e003c02450714 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 859069055 1250 859067805 859067857
    0x5070915090f0b04050901021c022529010f090b0d05100b010905300c03060a09110102010501031e15020c2a030d0c0f0218092a12070b 59
    0xb039029005094030f0f031041001c2724031a0300a84c220404102200d800580f40e000200d509484505c10340400900d00c02d490040304108000100d00c3c9021940b598010f03041c48070b80da440d0403c2200280216040e0340b0280c1402c0008031882e401000b010500a400181c02e15031036620307149001c0c040d80b0750100060700c1f005400541d503889000d02c0000c000441d40341900e0382c0c03103500b0244901d40742400b220319081807030240c03030650108020509a000d0080e00b114914a440075845000b0134002c04111010480d0f100006034661050086505803034015550300071550301e111242200710b015480854440200c581d004a181308a44082e0001b005010042d14403403004a140d505004030341d02c6c200c0940e6140c55240f0700f81c0c1e00e00080001c2c0d14003031400d1000c149511130520307203400248044d00a520940801c0b400302c4000c60341d07400701c4c000d4450004030303150800c1c2d0f0700070540700f210451a4044001000c1d40400c0c00c42c50010b11904900d00c01c802611b000944410440e0403e50290b44203461780c007a0314100405070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 859070305 1250 859069055 859069061
    0xc0c16030c06030e060112020603060109180b0103060605120a05060a030606150207120c1208090301150302040f091e061d03041401050f030712020c0304090e160305070915090f0b04 79
    0x144900401030640c2c6d604217000d600440d10a0a0042c1c001d10002c000101c0784d07405900c201010780900d031144004110b1945400b0050002c0c210364500081c02c00f00000350030fa000d1815120490702c05400360302c103507441012030b20040500820040d0720000800340000401e0861040c2000f5051001031a0030140984e08064a403400a5218107544485032106c10041021100228140da51050181100d41c4840c28014036a0080145c21035042d4a003040c0c1c1d40c654502441c0302004c60b803003a01d0030320000c41100319040445030140340241441001c169005940c201c041c035002c90407441640000f5101c00080045108017402c056100c0d201c0d807000400b4000103c690500716585402460918580498120030030710901018007040305006500740070b20101076803501510749100c0144122621641d440e00310390054a0300384903d40c09030181034000030100b50403007a440141c1c0d07000401000100d24041d400002814010814110700c80002c002040008050190300b0300c00c41041000b20710450003c00700812 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 859071555 1250 859070305 859070321
    0x503040509130b0103080901090f0815070516022806080103030e03010c0f081e130c08030c06070f1b11031b0f01181a120106080402090c0c16030c0603 66
    0x4240c07900b0918000540000c3d10581542c2d07000b12616100d0403120f00603100d04030103070401100654100b0000c602884000381f10050441c1c80046084d035500c0740f000540c0da511403001400488103e004c0e600001d401c00c2c002c0017030090700303200a4102c0a0300d070780440a4501615042030000070740d454010410300d54070514106400d2f108070002c1000c0803010300050f1003030306a1040c0d001840700c4040050303819080c0454000640d0102e82c40340c0700d41c0c40c0c40444003602d450801e004541d010312441c030100300502c000054550200e8000000d00c01500d5111007a91403840040c034000c1000f2103103045201040066035200c40803845801002402802d450070142404250032040e124400d940250011a94913081a000f40303080a092103440c80c10fa40e19062000121030b00b1030880e00071126a0f4815111090000700b600840d032600040c4942d032500422144142d059034065030041044c804078151041000080002000c5807040300c0701c85a03040c3c09032000d00820b6209548400f041036003084903d802d4000d400ca = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 859072805 1250 859071555 859071571
    0x24170109020c0d030b010c1e062c0a0503030c0318030406031d032704021201120c0602060f0a050c120f040203010c020a02060d15080f03070309050a061d0112090503040509 75
    0x10171120780c400203014002c021030140c2890b03410480c08040420010200ca045130f000401480710300004000111018500c950340c00b004032125800d02d400308408900c01201541c011702442c40c40e241ea008840c1c40d86c1014000100c19442e280040003440c40810052000744001e840116442c40310030074100b01a00c15402c0001240c02c100148400c815000e01d898600404440540f02822a15400b01d40240101582d80000140850010600382c030550011a849441880846021500c0342030807611000c06851414049840c4400710340380400036001944d004043c580d55500301560407409103010b480550340c886900b03240000f0321055060a01910340a4900b600040c45440010341c007041c030502ca00c8078041c418999440e00300d0302c0d1f50349512100d0010101c2008031120b950741007281c1e944aa00c912021004210144800a00740c10080407550485140e51610815806040c0c16038600007a022803450400480700c00c00e1005541600c500068240114010340c0c4031030424003446180e44e0702418901d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 859074055 1250 859072805 859072811
    0xe0a0f0f0e0f06041109100e100c03090e04050c180f010f0b0405060f04120b1815010501230a0905040f020c0a080c12070f060b010924170109020c0d03 66
    0x2446840505101c0c3e04803000b42c50008821200448078030150041805c1d041d8420301c031124500070998494403e20703a6400454114128a05504043d0b0700241b20aa00038049902100c0801c40c018120302001c0c0e101c1c1c055019255003d0b40301c00081c1442025401e400b24943c1c290090010400000001c5070141038441105400b030780c106200a40507000e5445024403a0f0000100142090100c000fa94002d04501006c0070340d2040c18a0003500d141c03412545a08600c522000194154000141c108040c00c8000c0030040b1507401e02004442c24504442d4000c0000201c40c0d007040031241c00340c01000504004c0c0c0ea009400f43c2401d0402c02500c95002c503001100780103010980c0210740100c1e41c00c4049900240d160b54815070000c0190406411071201c200000000c503081c4c040c01482e0b0302940510b4800e140821121040d00010740d07004800b8007607121086410182d01550700201c0214040c003d40b5401e1031806540300c0c10032001003800c00d030480c5910715008508034900001c01c0025a011132081d00b000c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 859075305 1250 859074055 859074061
    0x30f22030302070510030f050a05040201080f01062a14030c0f1f090219230910052215081c0503150409060c0207060207060f08010e06010e0a0f0f0e 65
    0x255100e00d1809130600c201600d080a24001d402035000d10900c9515100501040c0b403c1102000140000c490683c0400d130350100150ba030310a02c00d480360580d0000e440742c603580c020030314501e0000400100001d406005076031028000c43d070403800740041e1140f0300e4002c590710400b00034110f04205000c2000354003a805042400310306001580c54040f1344140c100009600c441c2400015284403107090b00300c00b08035800304003040c180b004c2c00e1250142502c03c0020154200b2302010312410074005c4881d085050003400c030502141c50711418482454407289410345402c4050708850301110308251055800d40c940303030010000207205010001420b005003a00030080b510b100e0002d42a44001000000380c6010003103440e444d40d0304d0381d00c518039154120404104500140c3d8000e55280d5080c003600300944030340440017440c140310346200c8500400c59943d140b16646072814181081d0400fa25103418032050100d44041a00c0e9401c05200500b20020b01c400a00d180540d2440c401c9a65080f0201d0b203030881d810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 859076555 1250 859075305 859075307
    0xf050c06010504090218010b040911070807170c1209101e03020c0a080304061410080a20060a1d010f14030402010c020a0b0c0c09040c030201110c03030f220303 70
    0x881c1181d030181c6020420790a01d100140070f10500d1060001e407820b0590001c1140500e000c00340c03003950307030b105000c01a0318040208800c00b8000c1c0c03000103021410821002001034040040320b03118200c0381103c5c2e800c0010f1013110301d04024203d81c0321458490082070407035403450400d000e190b000351103080c41c603e2004900400350081200c50b44800c00c0c907400082d035000c800d5080003101d03400e0350000401c5840782402c1c134103140586028140c0415a8425102246241456038003050481b0355500003410801340f265144c500c04502c0030010031502a4030403245a01b0303114100100b1042c0c0c0c4907a60302071260b00c1103100300f41e05555014118100246095101d003d40c0e00302180013180080c034141c0c0fa480e03072380f1440101c0c3c40341d80280b0002e400240c0c802000032210742d518054812900307184141d8221444a1040c001c60110854001d40b003441c0102c02040594000e40000c03428901d000c0a4600791010000801e1640d440b41049602c4008000b406030602c0540002e503094903072080d806050060b2075030310 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 859077805 1250 859076555 859076563
    0x150102240c0c161206140f01050120060109140106260a1e020901031a0d0f080d1a04110a1e0509030f0d0906090e0a1116060c0f050c 58
    0x100300810200107109400c0500403c8981c3e2200e000c01c1d400d1084a440d9800e24180b6a01100200c50740c60400c203e0020309101c2d09440c62064031000180e40d9241e2818004440702804183c01040310700e1004229942c01405002c0c4c2400b03440f440c2c00204501c400105844400c83c41640003004110b10003284903148400c011203000c10802d8444507410f2601e03080c100308011708030100c170390300105241c1c642445456140d030040c29032241c0c00d80742003144040301610329901c09540c0000320381c008030020b01100003c40381803881c05d440340500400b6041050700c030984000c94200394528440a803aa044081d040e103030600908648803201000d8a0a01c25035110240404007181c041c104c1049155000d0704205105030152548401c000f000c55061980c1c03007107881c1c0c480e01c11607126000a80a82c0c40030501c140203100e520101d903205400b440c980c0d0303100d0385e108004040c0c246e4502803240d010040c4040d000252101a55154041d5500144420400002801900c149a544800d0020900c40900002c0b03002c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 859079055 1250 859077805 859077811
    0x9030e060f0a14210702010c0e01020703020418080409063b04060e0d090306050c0310120c1205030d0b01020c031e030d0908031803090901050402130e15010224 70
    0x20500c2004140d000d0f484040c1c81c0150445a0218250100b111010a089980d024041c1039035030000c10124214000442d80869240320241c0982d10100080005040a078094950302c05140c4011074949403580e502e24143c0c0c000c0d8040c4021039101c00d01800000d95888011400440005109440210840300c3c0380f0420400140d01d1000f00034603000806120440c0c2203031940a001c80c043e2211100407040c064891152400142c809a2170301d0005248030a054003201d0080e801103400051035031414107050421041184101d5011040420000f407010130900403880443c800c6000d181c40d0751840d54040c0031140c00901c8a41150f10280c142d001685012842d004003645d107070007400f207840d84002e50a186114142c000301c40d452500d0400d8080c07114000240d8010241880459484a44090f4490b076074002c0d00032413940662443c1c010030080c50a58000c02001c0701d007520851a6507034030310400148900c125070000b1030002d510040c4001b580d05001d1044810f4400940300f4614030580304001d84040c4c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 859080305 1250 859079055 859079057
    0x50a08070819020d0207110901031e030212030c120702060408190306170f06010807080607030f2009180919050a080406030b120604111315030609030e060f0a 69
    0x1440411502c1801c6409010341d0803a6800c1503540308581d0702d80340d0095003d44415a121840e18001000134600310f40d4407030489401c000030428009a0743c0e000c0802c0343d24440c045041d441350302103100050f01d61038003030740c801c4824100f0341d610f60502c03482c00741d500c6000600d402c0c11500948200800111541c0595050644502281460414000b819001810b964002412100103407007400450b000000349403e0f405000010f640303030382c0da82d250000d85d01c01d541c1c0601a0940c2100c00060513040c403a82c4000904514004040b403c2e100700e00c100442c080c50324400040030342d000550549a800c021445240c40e400420302000d85203011000d8a0301c40189240d540f542030380d104503050600c60100010a55603070401e400955556440c200a00103007045000719018211084030582001d030045425031245411010025900d0f00d004100034000c80c02408816103c1d81c1c401c21000b0a51060040c0c4010b50b08c520b00010700b03c102ca003005001900140c0c180b621a043c00c210440709800603c003a90203080207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 859081555 1250 859080305 859080317
    0x2130b030a15020c0304090b1014030c091c03090305071403031909030212030405130b01020d08060120030c07050a1a070201030f0903030b0f030115061202070c1e06050a0807 76
    0x2003282c0200a807182c1500a039892001250100700348420340c1c40030304d051004075019215000c00000c00c0c2c1300014040d85252400f0420300000c0d180c180c100d0010400e03c0401000c0c2c03912070b94000c0b07100002900321f4209400080240c00c090040210800c4088013800c81d1651207016614030000180ea00c3c46650300601d00004d508180780061405900c408000d5a4010510381c06150510000e60b56032300540309842c071881044000003401070305481400c48184040e4003410b074140740000d0075070300610003910590420207003a014010724103440c0c10481107040c2c0080919a40c00309403000502c1d10015800c0030348103020004040001c0c1d005810803403009142c904107191142524001a001007880100844035182060000000c05606900c403401080d022100c40c18071702c1031441414201c941c4044030452034602d5a2052003114040c2840645c0640480c00140c40c103c0c95641d02c42a8048981c4000c003201c1c0704800b803251100d00011041c014189a20b030036800c3c0071405a00500700300010f09400107111f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 859082805 1250 859081555 859081583
    0x1d0f0a0603021b190512091503040203070e0903070501060e1e0910060e060910050603010b070615080105010510051e090303090d150f0e21121302130b030a 68
    0x1d0304480724603c5491542c1070300c030038250401000c440e625408208503514000e00020009410241007564001d8002602c40c00d1043e42e030200302c04c0d941d80007800690303051140d040e002505c003242003491482090200041c644940c003e140c0b482c2940c00640045080644810400600d0b0540701d115100b800729084c102009916204001030909015070308122495081210205802820900c83d40c0101c4040c0c418038042d0303031091117001308038000380250b6500c500c0800040101494080192149600031100018020741c040304202801000364400e011a94441004000034501100c1c0b42d100640c4508125180080c81c030524a0707a40303045540011030410100340d12881752410425108908809400c1d2108040c86007007460107501c0c0e15110b10f8809007403241d80c4076a11410300441d0a0135190100400740e90301039240603502040e8000d00616100414450454100c0c648040180113107010f8007144080c0c04540140400c1b5800f28107503145060030b1115420064500040307072841c00f90028903182038a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 859084055 1250 859082805 859082827
    0x50402030c21060f0f010509161211040f03061d2503060213150309030203040323030d06090c0306030f02090604021b010e0c040c120e0a0c061d0f0a060302 68
    0x41c40d20300c4442c80350301c540403c02660341200c00129001d1800c07104500307130580e0707a041006401d803c100e4510450000c01c00c4290365890080704250201300704d800d004143d0807580b0b0144d038030301c2d0807030780c449031104113140c1d420014401d1902c1a241800c0d040400102d2251040b02004c1c0c1d504218035190840b80301c0114038075084010b81e0300760710140d603000000395070386c24100d050b8030304000c40b80c0130b0745125a08801c800e6000c2802486107070000c40e07164010310700f0503141da2508080d0304280c0a04d00001c448504440340324281c1440100300e02000c001d40054014117004030a81220075000340007090524085003030000c540c05995542660f90304403140d41c1e195482d40701081c0030b070045440b07100321245c401c0b09000f13000c0c90642007154980202403c0710f804410103410032082d60488003a0b140843c0310521500c11105054024091801211040700d450055582d540404148694058400110054100c50a40b00c4080c001c2c62115000c503008180300f500b0340001807103004984101000e01d9800107103480d0072 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 859085305 1250 859084055 859084099
    0x9030302040e0c160f15110c01060b090a1a0f0c031206010309020a051c1e02180403090506030a09080a170a0b280e040503090a090608061603090f032001050402030c 72
    0x20414080d028007081f003903a81ca010b8140c00c803607000e07500c650034a030000c500303d601c150948452803070040181c8207492400b02a000c48a070058050000518108400c128005d51b000040000645020046503900881742694407644005000c071810107080018071005a5591080041918001c840b5034030000b48203a407002c042c0d00c0c102001445441c50040e04440340380036400880e02d1500966551110030b4500054003441403085a000b40030a0f0402018050f50500c000035540c802c81d040b40014215889032240e0109420030707061100042e2a0700548044030a242c940640c200b02042002c7c04282c14103c0028511600b5503d103c4001c017000c090140c804a201c9050300051900c1c511440b4031313080504000b0b480b07501096a580c0101d1402100189a50092007403c0846100301c024220589404000c4890010004081c10400d62240c1080c40410745400c44044804d129446403082a0410300b4074070003e40c4508032414041e45008104030160b10301254637034400c0e2088861244035101e071a040101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 859086555 1250 859085305 859085333
    0x405100e0f1201060f061412070203040e01030b0703060801150504050c040915080c010828110a0315050f0904110d05030a021b0d050c01030903050d09030302040e0c160f 74
    0x1201410074502d490782c880c103511900541c0c1e0520001c20706240c42e128151030040407403000306c59100d401c100b44240b902060a160307401070b40503c10340b07140c107039503040c09440b4403020b800585840341082c06001c2d01136014070852000b00b40501c0280041c02d082c0920402c01d0301107106942c00346445c0c80028002c0a5100110340281221000410030b50480905c000007000f061b024108643c030800f00540a99130240c2d020701e11a03284c1303050003111040b2011114403140c0444140c00c0c0101c0c0c45200842c4d0145080c4003504800e0416980000c20071040401d200c110f00d0180c1c802400703500f403210800c106850340b240300d690003a00b000c0310512004e6800d01140c04120f03400750140803408080f404078003041d80480c0c2c202085445c010210354a94030a01041404d5800c000c0040c2503900203207110900354040c0d0808442035000341002c0b814098104d00300825142a00c0003100065800070701442400c0140601035009030004107175500f4440c8424010304294800d21000d010707148201e8142040110082403000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 859087805 1250 859086555 859086559
    0x1232a0a0305010f0e010b1e25020a05040630020904080304060501093c0519050c0301050d1b030602070602252406080604050703030f02030405100e0f 66
    0x2039561403540c4010001c1c9828003520b881924a450006194042800b0312816948100e0f091480c0070320403110042480c801c06040e886241c001d201c440300c81000b18803152503c500890740c0410903110751041192040d12a00403074400c41c03401d10103000340701203c1020072980ca074510181152200a0b104940c40502c503400c000d6000310050100030801290318091400f90f8440c0c5020f00c0300d40d0725110070406a8031407241c41501040e200703180404c000021110b0090200301c2045688001d809107003108207454040300d140e04406100d054006040501d840f6581d40002c4051742c0a0555040c003000440c00082d181d005420081c8850020b6100d0180d04500401594440c00031035840b13502d0300d04100a03412080c46d030110b40c1c00843c440d181c0c0c9150200c1c401304007a071000d45102e04084409030100707882541c000c03092141d13580c1c00000c0703102c100401026003d18041c0c401480ca00e4078501d002012001c0401030041150400d00c8100070944800800100722265402c201111452a0021039410070450340c00d96 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 859089055 1250 859087805 859087807
    0x801050a020a020d0c080f18040f020927060111030409052701150611030702040f021206150901030903031410090501060e011e02070e0702030c01232a 66
    0x294080881d4010215040c0c07035002c0c1c5800d16626a41555213a048220151a50a08000701d90b208102080241000840341c0c040e61014504500030504980283c414640a00d600103100e650030f01e020801d000300000c0c041c62004048040304240104850060001418050000c084d000e100c0403e0081c3c8001d03010501041200d46002040e140d04502440006d8120901e0f00300c10a1045a0602a072084400030350310094050b480d1507000c0310044400303081862240424405040140d59170700070152800c417446005a141d007466800c0c4440104040d2400e48030380030400a05c00804c0c03c0d142501c103090000d082c0010040407605087c3c0c080c003070703001c1915040b074108010444440940c0051209440714680d08201aa8941c41c040d184250300c1c2030000d02113a200e410f2006848249562000140541c2c07040d142d00030354034061104606001e44000380982c01c0401e000600420920a0707000640b0a4050020044001242c0240414002d4140300314150366506140d0964424a801406248511116 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 859090305 1250 859089055 859089061
    0x81206120d0e010f032a020705031b0f0405070f080403090918030f030203012d050303210f0403080621060106030e01060902250615030804180e0309100207080105 71
    0xc08112a1011250200780c2c81142c4000c4c0300c0c030174481c1880380c0ca050502c18461040324250f050401481900044c1184a1441301181503103040c030140b1101d070800003c00004480000c10010703242e802140581c0a50310380402c10400c1c640c000208007202400707003460f040986440c00d040b2405011500045015401e010107030401c0c908150903200700e9070181e83e446c4058001408101e060384000e206010454101c0c0f181074451500e0805809070900004541581d556945c10119003150851404441c100000103118014000480443c9600000000003001540f074070303550141a0304000390a031809003614149074001115090146940c400d201c10880f081e42da95030b8401405055610100c13505542800e1002414200740e0003507d82080084901040051000050010700c903030070041611400d84441241580303c21655859010b1b60003400ca250b0341e0f074141300b86400c0364125408042886417a16080d9005080080250340c1046401c85290f4180d60840348101e01d451400e82010348194a0070040c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 859091555 1250 859090305 859090307
    0x309010518041b0e1009180608070609170f10180204140a0b010c0203030703210e15091603020f04020906120403030b01091203030506040e032101050409081206120d 72
    0xc011004101513540e9910146141c092110548140e4210000304d00520814050780c07401c111a60780c0d07055850000294580d803201e5951410585030302038000700b04003000505c10412100a404110592807005045880c940328405640310648903448201c20341e40e801c1030060352000d0811400442d0010030520201d01c11101c403035400e000c141c0305060b10314030300305154003154010000d18100c917030003d000c0c50400c038082c2c03020307941c856916070b09103031034484010301fa03040e24418800c490003103402c1ca0040c034200c00c081c80813070b14414019107a84520341c880d20100160340c582c1c054030800c1e40d6068501303928841504003c1006402640c903501d40c0400c1c0411410000d101000f01d40b807046000c0c2e50240071412590340151007420041c0108240c0c440d0515814000c01e0082c5c0204d03800180c06400051403400d0403182600390b8024451150561205080520300c112041807001d02400d000c031400c00500f0360607520358016108440c012400803042d5000100c59039103804124040e80b2124054403282151000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 859092805 1250 859091555 859091591
    0xa0804080d0e0d18061b020a0e1008150906040f08270411120703050702161520070504050408040b070f0b011a090f2116140102030901051804 62
    0xa9080c0c0050321041d81019404101310040c0c0c1122540e4440e5600c003400900c85240b0b41c00c081c03601741e8001e2140d06001401c8406c0811452007514620411302806007003c0e01d0703c0c1007181c50324022480b40407100074019950b13400301d00340c2d400c2075001c070084030112140c0c40e009031240580307000e818803866189a4100c2d0710700c000700e00d15800381003250100301004a40b09014050701400e420503200c00300206c001840b8500940c0100c0d0410700500464849080b00c40c210010078041e034020051080c0d0003140440002d0f08140f20041540b040c40c103044441e040100c016503204620310036540304a07110004101449000000c0750701900003182c21560303556041c00c3c001e40c4042d10050450320000c41d24000112800c081e2038480c0c000202c012802d02d85032105080128411140c00c110342d0189001401c0401022010805044865100081c02210504105c051300070a401d41c481d81c030810250035218410380c0d02008440c03040d002401c2258035541182c014068500601e110f29403c207260803005c402c585c03500c203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 859094055 1250 859092805 859092823
    0x108010e0925090e010203090d050c010e06150306060a0810020a0e031917070804030206300618060a06030213232b080a0210020706060e1b0a0804080d0e 67
    0x243c800c0c0142c5040510441c01c0b44801c540f0b808094100b101448a1302e44901c009095840d403d02c004070302c51100415443c01c1c044191664030792824183e151000e80d0900303215290748004c0842d50002d180d881c0020300380d21110b014007154100c541c0080d440942c14000d0030a00032112003d002c941040f1000850100d040854810603201602120481d00403200404100c500d4617a210048a092034610390a004030f541250110881a851500c910901552003440c241d01404d880c555084890500704140111545d8070440c555018504004000c50794031405440c0d01110f00f18500180c3d40c2550148126650400d9040607a5060201003003031021800e10b482d05030a60022a2484030b180034143c64117100c04030003032120440400000b95000480c1100c0090501c071480d50041e00c80080030622200d00300e900c4500b013124680d42c0c5010500443c0b494000d402c0c1d0010601645c3c0c104c03040105441222409486402d070100a825400601003052a80590300b18920780034041c0100e00d51041a10344441d010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 859095305 1250 859094055 859094069
    0x40f02190e011d0c0f0702010f030f090b0415091713031a1b03010305100507022401080d020d05072d0b060103050714070f021906050d05090a020108010e0925 69
    0x503d0200304003021000440c2d0b0000c0030038848503e0400c6640c0103603a807400380200c1806255036480c069039000502c0c0514040944902201111481d10340707011a601c03e2649903000c1c100b85009161000240007000c001808007c4850083d1541c0c2c10a0083e1039046098000400b003c003047c4403004003a0514821900411240c000100600c1074120425603d00003440060851362085e6844141004e207a40410f4005500f481514660041803103200d049a1014240d4450030242d10010400400140040801040c10b44043c1040c001c40c0716008249005090780900500c003a01e0a1440210b86904d542702c0c0845040d180c8000000305043c01d689500c0704444143c007080c14500080c00d402c0c0309041020400040701c00c02030410b4030545030300c07081450250080f604812416120006d20076031400d0800284031a0741d420f9503400540001d44281c80007d00303440ca856000206100041c1e07044903082d8199100f9100c403103183c0c0d4464061620f81401159a0405846031290304100c08000406802c00c0c0d03580 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 859096555 1250 859095305 859095359
    0x2a210e03010c0503011e170a02030105010905040b01052707030501030b150334081c0c050d0f0309150606091d0601140f03010f0914040f02190e01 64
    0x16480030300d0300781c0b03504446420002d40c08000601c03004c11803d207082c02c0e22140700c451385a83d40d21510000703441075030100380001c26804200c41500b18a002d0007118094204920700380300505142e80d990040d0101030243c07900c15503d50180511030940b030740010710800e4080040f10301d141170101021b00100800e001c103035810307044040011251224102d4915031000094003c4c4110401c0c2800c1d10700d0810720001542000000215070390041100b060341d80094044030740a02240000d05c400c0d40c1e51860002505004d22038031110020104101041c00760403202c4d01d04084280c00200380c0704400801000000500e03d40d90707110b0030b0807000601d6102209540382600c442c03603026224824812460b514400858918a4410009e001c55104104d8641c0c50801180f0441c00c10002d0040030300745420903082103507c0f281003030040003005100e0003851030441545040c00300c1800d044e22000340d40700c20383c02d0181c0076102d80c002c8842c1d000101c1e4800c0004040100d024003195840340f04551651aa00c0b500e0003810341 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 859097805 1250 859096555 859096577
    0x121707090e07050a020d031808070c060306081209190b03041208010b1c0c0c0506151516020d15060906030501150501021c021e06160f2a21 61
    0x80100708598135000107400a183e0300b02d1501007100600b410300104000006e080321030f0000200c424015000b0144151540c11441c1c0c00c024008080714010340c020382d10796000355070401c920740e03a07002103468a200c1920410500e030700010001041c1e0030180c0c800c0302140000801c100501c2240041c015181c1c105666101850b42d8410400c9618001d8008901c0714810b5044800114244e035409504003128904241c40d100d101501d40c1d030b00b03100d41180d41699400200508030407501d0f2040e02142c00750210b00185040008502101083c1c1122030002405403000e580000140130240021505201880130240241d540740c41c9003102500300392108403103640c01c01102c1201c1d00005645041950344c10781c0144400c215807940c04880c04101c484035425800740348060707641c00c900210303441aaa10b0300c80c010401410b262400f81440a140840c0104006280d00340d6446a42e00c034001119186507040301e00c0380c0d0454402400491102514020210481001241215559810001d041d050681c0354540461 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 859099055 1250 859097805 859097807
    0x50901141e01091206060b0f03090114010e0c0306040e010e01200906190c06020307090620031606060801020703020601030209010b0304020d02060304030c0203121306020106080a121707090e07 84
    0x450341c1d4086a0115402e403206201e01c038014105210314500403607011070880c1d540c0081e500b15510490700c404044d0700000400204d80424040e05809810642d0700030401e42c175192011003201000343c06924810b0000001c02c01517542c0d80c000030410404280200f0803032014140050080c00f00c030540c11450032014010724112510802521118680a0159440c2121644d8110051344440745048180300d00703448200041245403000d140305140545918482c06c2c1006406014041c000c0003503011001e04500070b00c00c100c004003c6c2c2e0700f2540c3c0303c0c4040d1241001c4d45041c5c0c0240c1025004481c4541c40421000280341c2e0000b00c0c22304903802600ea5080c1640c89a90101480c8021680603401c04511460320700107061040c021079110b40a41350170155620700d5400641892094159405603c42c04209000d0421520301820018441c50000700b005a2810f000d0b00d17110070300c0d4072014017002d44044010101d02e01030300045002c01454001440c85207070070b040140216030140216500003a18200080c415 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 859100305 1250 859099055 859099099
    0xb0c010b0102033a0e07030c0b07030e1e12060f01050102070f0b031e090708010e0703020d02060708120702390f0a0b0409050f090616031505090114 65
    0x7100f5080b00d00c0312488107803014601c10300300a041c41c600f007502c54403a10260100d41720344d4100e9200d6a0140040c0c034558180006904000d4115400c142c2003041005d0002e43c1003244040e030100155410313586c014103201c01010954038001e000d5080440300c00000c40300c40c00414243c0c8550348025089255036254401283d550540c0d0013040100e494801080c4181c60070b500113554440c3d25a10b40c0f178a4200000d600c4048401c0544003582d46521540060001c90800c1c024220120003410042c481985190006141400507a001038015100003441c04e0601c5020b10445070350b034030b400c5040401030400e900029540ca502e003503c1020b074150361840b11000d100740207502a959001541001c04080f14608200f26070640802e000c0c9d200e00000e600050212180001c0c2005040c40724000a413854042c054510302440142885180d13002001088007002291800340c0301c60317a19150000c0d401d01c0c0b191403400700c03038941d41006500c461084000500c106034003105214100c401d0f41ca0109a070300c401480100c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 859101555 1250 859100305 859100317
    0x2040e060108030d0209030309040f0c031103100612020714070f0807030b0a020a020a0b0c07030809010b06030c0f2701170714091306031407060e130902040b09010b0c010b010203 78
    0x1e50410400046020f03413a0b00a4942e404004068a2420001d40000380403201c0c0142c1e442d81ca2500c44281010040c1c26206010b5581345401d6807030300c0d601e0104400501e14030940207075814818984009402042180d055070340701613109100c00d58240d140340406989100d82d00c03a2040d1144004d20100f000d5802185c0081200d80c001c40740c00c916201d004001029410495442045102c0c601c501c3d40480c030a20050b6024408050005039140b0813401c00a200d60402041c10481c0d07810054101da43d0f80700c40d01180e5010340482c1c2d669440313001c14800c4030202d205240f0740c01c040f07100c051800039410171118000010103001342c0301c0703100c1c120004a900c1e0b19448220b406034085401c017441c0410302604100101042480101424070000c011001001101c505410540d4880485410402c6410781001443c002d09401c3c28212900544080000c03c060003207042e04130416142da6080e000c540303c98102040d0988001e0480b0316968403a00421349640180d0380608640d800c0480c1c0c814254008012910 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 859102805 1250 859101555 859101569
    0x51e0c032703070608131203020d0609140c07140f0d031802031b03070e0c030703060501090e2212020610061d21070b070308071422120c0302040e0601 66
    0x185042c5441c0c415a5200801000055031401011b11100060a4445052440d030386a0f00c0044c1c0b03070300d600e0915000300c4000f0340000d508585028441c2c10009010751311a83d20220703161034580d640900b803802d450109030403801e119051103500354820640d0f102103801458421a581c00700b102c440c151408800c40c1d454108080d4064001d501c11381030713030306d1102580e1b018148003408440c005603030f515541291140c2216404264130f0040b0174442d0480c2d15001d050010030003440d001d01d40e141000d6603800041c0000c0c3c0382141c10b40e02e181e000c3c00c07a4100f02c648000c0858000380c10600c03070f400c010006500c580044510b140703805900c0202091840c0940346030501d540c403a691000e0010740360401c1c040200d404003c0d10f841070114000000414804000f00c0c0042d000c05030b40c007a00c400d10707490b020b4191a0040c0c1400c05010a000c1d00107841d0000c4000d4a0340d5096459407140c070000c405640f51400c1665400c00004118400d007601c1c28001d4109a00c4101c91094400b0007241000c0080c07183c0f260400e010340c1d8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 859104055 1250 859102805 859102813
    0xc1e01111f0b01140d110c0d0215010e1b160602030c221a0903032b1103150d0f0215071109060f0111390406050a06051e0c032703 57
    0x40c8170000c00707600c00c60202a044030740b2890515101d02152926003021a41c1005038001540c2516a542e03100225006100005c0c0b003003054185510424078282000d040900c101c44040b48903050301c118618200c5000e6040708045589050451610392154085e8640000340c40201c0035030450702400c2d042c0070b8229501d600d01c24120241407282c208040c3d1100110550500c801d21507400084444015241500040d01011680b02c5600702a030050b02c1000803400c02240c0c2c00d1040048541071407080f03081521080720781c00c18101c03040c45c060940603050f4402039005190100b14031000050a0020000c0c1400b40025141c805020010480503040071034503d0b401c00c0d658000d9042550280c0000140c401201041d03801d88480d0340c181c51a118180500b100ca542c0c90014608007031500148030380301c3c3d08026502404200e0400004c140d06006030f11800081280004100051000c540e10302c00c2c1c580d50581e02c142c0c0e92a030a03081c440c0e5a41002c4443c040d08200220145c401e10ba88038054070366624054090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 859105305 1250 859104055 859104067
    0xc150a030906060b04090b12032701020124090b0402090328050a0b040b01090902150d023702150a180203160602010606020c1e01111f0b0114 62
    0x49019000341c0504560503600c0e940301080061815001d40043c002000c000a0903009a800b080014040c945058500c1d410070001c2801002e44501040311000e400020310924081c07000040b0f0040c80c1c414801d804000001078020303414100212100d0480380d50b824240034000318442003108074491f22019070b5150740209801c10b80700c40360b00c0588c6c500080b07150b460030b40d00c02c0549800f03081940303500d021160340c16000204400c002c040c1c40300741c0c05062000c401300090364071030340800c1d00044d400c180070b801c907800801d81102180e00d64045a00040f01c00d0540b4801d01040500394482100407245001154030fa83e19503200c01d4400501e050000c2854072141c0010f4880c51018401821606501d90900d04800340300005a1000c0bc00401d41805020045008034548980203085444175040307002150402c03c1e9420096903900480c17440c060221180407001d1004900584000d081521001c499010795240c101c820494050200001c680d18601840590101c03001103a620741d80f81940d5180002c00d02075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 859106555 1250 859105305 859105307
    0x3020609160e0f070912030c0c140d060506042903060a110304062a0509030f0606030a0326070c0b09030a0504030615091b03140f1f0e0c0307020c150a 66
    0xfa00d80055003810808805610344a010003011080c82c0b041c0c0124441210480802102c01309010041c4400c4000c2c05000f0b02210004169010941e8050301c074540300d0020404a035106e41c8030b46808100c1414440e08142c0a480d100480030340c0c2c403540b40c42801030b1400500400c82034002c0060404d4410304a40c40d541d1640c0d00e41c0c0061076120034510440c5000c010b8000301002070040703a96101010303100c440d22103040c44101441d08640700340300402e9810803814480340b07403800036550040c90b90506002040001030120441c44516021049007203450381c10502c134800f074001081700980380c0030760380b10261075482000311071356449074101084c00604100810404900c0c540c0c46a110254150314a40d02c00ba0303101c0c094400c1d1440c1008590130202072a61004840b5094401c03000c9130000304e8400111442c25142c2c596840030010104010181d12481c0a0012101d20300e005000c0c140b28a004049170603c1e2081e50b000d600f00f20b0ba60342c0940b0a25001c080146481401c0c24104921584500d1400d184a10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 859107805 1250 859106555 859106581
    0x12011a190501051c15081608340e060315040c0e0c0903011d0f0106030c05100224070f051204080a05040503100509120309122503020609160e 62
    0x1070024100740d11101c1e411130300c0049000b0b01c2040c8110b400070200030760903d41c99a04000c081c0d8403801046078101c0b010000124086000079504100c0d003035402e000081581d1080340000d500c601d20384000348600001c114000c40300c01c0c4a00070f060a40446040b810707140042e001048080d6006408110444010008080d4034152079501030f0845140b14142803e0901007402d541a100c0101c250001e01c0e0441c0600d54070400440000f145004001d0003500c0c0303580ca138000d6821440c001d040c014a00c2001402406000701301c80c4064401100840384944e001100300b42035280240d47c20744c00105807103615901c0710b10440036140c0c200f0306584030304165290f6540300c8110741c1c002003105091040a101c000790969043c014012107401e0f51b00003240754581503c101e82849a510070b5441c01841c14021b01c02e82850008200214500c0440496a40c0160080000031000392840d0001e40300b401e158501d080590101c2c10ba40122207010840308480c0c0206540d074082c0c810340c09240c401010010001d015815404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 859109055 1250 859107805 859107817
    0x141f090602090d0506040b07090e0a0b0409170706050a06060f180506040806160503101a04030f06140c093f16060f09030f06060512011a19050105 64
    0x103a001450032900001140b00640d4140041c3c07204d40005080000b0301c400401d256600c8a07003403400c074411905101c440c04004070054a80b00e042c40e500d41d802080c917142e0742c2c4240741c01904180d000f10390610800100c0341a92104008440d00d070700340740c04a01c0d1313000d0600450b07081c1c6100d82c81e88201c034040110110350901c01403424403144010b60b180040c542d02c13100d0003000500340d050702525951401c604200103401015a240c803c100d810002c01c00c1c0b070b0360008a0328098841c140d181802c4024a412310f0a21402290000780c440c0000400d004104081e41c1d00144502e00340c207022072259610343c0e10700602401541c11494110407082c002001030208a103064000706100181300351041e800d82507040380700c03214041111682c0e110102c000100441c90740071000501d02d40c9080b1100b2142c0c1c1070002c00c3c01c40d8070302c0014001d40d20740040ca01000700d603400180203032001500a411410518890b58003910181240300f411002065661005007403200405100c0c0e151403190038021450b020044070356074800c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 859110305 1250 859109055 859109063
    0xb0304020d061b0c1e050a081b010c0f0e2e020f1002072003120a120f150b13050d1a0a1407050c251a0403141f09 50
    0x151030f4014100c0740012503002001180e40c0e07000d824030340620b401d084021442800107005415403620100084000800207959a80690416260042e01c0c03022100c00d511038080032065400c4c0b004c1600c0c0c0d1179000b084880350848990303034900495410820f0201c201003814001c0e5100881c01c00002c02060b80062041c9084001e2040316400f201c200a0f10f424414400b9800c0207864002134900c0a10030003440b2024090410081820130741c920100007580e5000c11003001015240200e504c45400c4c0c001c0303481c00a9018081418442d400d5080c1d943c40040c4812290204c40d060686d001060002c0c0c80c00503500700303222060106008a00307040400214540b0740d80111000b810140d074082191200c40c03105401051802000314800c04070344919102c03501d00500e584100301c01408840708018000990003e00e1199040f0b40f00000c4000c00c0b800701d600055000703603a0b44d811f20001c02c40d066100c4d1004000710b03409010005022400b000c07000303450303201d000e071031550103803041d900710035140480d900c408401441 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 859111555 1250 859110305 859110311
    0x31905210615090d0c1e0518150114030a0f06060f0905040b2106090c0d261b1b030304051e010309020d061a030106080a030809100509100c090b0304020d06 68
    0x4180c1d039a01c100d40d61600100c46585003041e802031b001094041c440e0107010112007144c070620428200c6e91406400401c2c10401c000140c14170390301a4007d809040c03013000394900059881c9048010340c07020f803004000d00403000c2d182c010700040e501d1066000a55030700e5070b60f403071010161a110820001d820f100e4542da40c000384401c811040c0080c240709209140c000c84010b1301181c680110300500340503440721070314096040d0290320f00000c0c40d40503c08444104200711710200e65940c40340f40c100d40c000c44443c024142085048588803000015116240c60301d00c1c100d500c1d46a504400349904d80c002c80c400d45400c240c8009140e61043d9219000303405881041c0f600241156a80e00040c0700040100d20a403a410b0b59928001c44103043c1442240c5000005ea00901c902441c001c0c031569690750240d40030b0200101d5401061240c0b4041c00030491722103116000344801c2c240440700c56121a000c0d032003905214a02007004501c1030180c8001401c440c8000303011400c60351540c0074400402101d46007200c030695 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 859112805 1250 859111555 859111579
    0xa0605060d150f081c0e0105161713050306010803090102030a2003040f050906180612030d0e0d09090603050d0f0c0f03030c0909020702061b03190521061509 69
    0x1c40c1c20864004d0861800900e0b958694042c034102610920182104011848110312003d0360024200c4070804c1401c0c8004900801700e0400e000044000039040e004100f0029440c5c11040002c11240b0513980101c0035600c040c0d984102069881c400c6484003809a001402107201544c0190001a55007000460ba080b01061200e03000e8115401a042180807490462050005040c00080035078040c0041e00c48608449206075400600600100302900c0b1701013140c0c1141c0c4800052041d40d012013138158080c1701c4080701c1040a62030780d4150000c1310000714031305d00014540e2160b009050840b9004000351145064084080720940911100101071143e8807a1010004451140300359000340650340c0002e01c101201c44c02400f100031a40040741c16401800150003598940d4100c5d60a10b50a0080ba071034255503d80a600394090480c848d0240c0c1481c4802103440f540000c0102090142e1450464104044070300e0352880c9082602c190f90841c01d5166094002c09101006104503a40106240740305a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 859114055 1250 859112805 859112819
    0x123010903140d0809011503020f0a03080417241f03050d0206220506060409061e05010e0a050f04031202270a080c0102030f0d06050a0902030f0a0605060d15 69
    0x182405081403aa486a001914042d07407040d0001d030442c0345c0d64000e200400d02c2d00c00600400645000c06803084814196600d01c44d6106c299481c020750740a0540342d140e81da51800b4086a074481c0441a00c6801f409072000b2489044100180e215400f281c03010096071104e0205180c101008030070301d002e254900401201041d010420150310002c60f50042c0400e140c80703044001070a404202408c44240034000700800180040ba0003680042d068030300140d85603241c00d000000c0c0120f600d0108050700f00d00200718407440550800c40c1a00c3d0240c1200c0d2107511240d000d80c04503041100c05c01d2500558001150001340305070148045010091005414251107075400c0341d1418003500d5803801e14030031250300281c42c10440300c00801801102c01620400d521000040d4980c032071110300c070740c100c100002d145d800b2001580c0200e0291001030310402c1120f131120070410080d0b0054920f210480d00c003c00050b00100c40d03015580076290050140c031b007021b980d800440d01030425170031800507003600000040b03030036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 859115305 1250 859114055 859114073
    0x3020913020d0c080c1b0325030305060f060706360c0f031e05030c010f0b1e0a0b0d0b0d0b06090a06210201020a1703090c090123010903 60
    0x20011540c0160b0b501400341c00341d011224141c0c1c91600307000521003003001c0d0b2001d1505842850f2041003181c1300450000540c00d0541c400c205003090b0464910400882110020500004e914400c2d10100308036100d0074100185c11043d1a103082d8420710410100300005c003d42c00c82c1e55030070080c100c484c075031711000030120f48840c00ea404007548070810f0244000c140400c0517644001000052029038805055840e02d03511550016683c100d000c20100200342044410400c0300d0350700490304004c200e10074202c000d000140441c115158460107140340b603022460304401501010841c000d010100c000d04c0e00c201c01c880c5821010300040c0c0c00344d485050341a50349a54040e40c504510582c000340a51900004000610ba0f01411811000385800381c00d104010b05c1c2000034400b805410a02c034000715103840100e10304556820010300c21042020850711000b015800b95001d815614191800300200000f4000180001d128100002002152003180103040e61702c0d83c0050070040c5405008161203071594840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 859116555 1250 859115305 859115329
    0x3050c16051f05060f0f06040e0c070804180b10170c0c3004030b060d080c15011703120402040b0a030b01060503040c0906060f030e19030e040e072301030209 69
    0x60b240d02e5400304041ca245c46405c40d03a07900005c5401c80c1c201513548011a00c00d0095016400c070305a1124049074901c2030040c183d82801d9808403400340d8890305c0301d1280510300d51940f0044419407d085081c9058a0050503509245259035141136500080803140403142001406030200300030704103d00e2404460a01621030240c0101c010700380d00e803003403924003540b6113a84015810f250310140428400180882069500031104443d034090070401401c10011512a1402140742840b44003591884051b500140b40d040351400c071211140d980321141c400d92288190010f9442c0c500b21031380040c0040c40c0136031081048040240c483c01d20b03a5126a541031408e030382a0405408101d010081108114407528590080c0038504d600b07000b2985004005010140002c004006041d15614076480e44034080001030203000384888068000b00b0344e401d0103804d02c02803801440c011824100400c10340c28000406004444c01981611500281c00010b114994241840581015000c10950300c1960b00c06901040d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 859117805 1250 859116555 859116613
    0x5041116060c18031a0f0f0f0601120501080a05060f09030a0c1a010609091b120506121b031612080c0709051008011506080c0711090a0212010603050c1605 68
    0x7a503422101611714844001001e10640d071500340100050311600355590f58100701030350246010f548500340140c40101007500340c0e00d6000e140c8000094a10000a12610004c0c02502541e4607616220081d8200c40411204810340d030344104a4202e495200f200e149241c0340c05000300311041d410350310068412010030780c00400090201d40b010702c80210548201d526208041c00200c00f1038801c0315001d40b050264440d0501042d90310310008655882d2071b135400c8045035000054840c0c04150400350800c5180c0d070758505009100307070694409003044500d000700943d54440d02480814156680d107002d03503032054240902a002d041000030f84a091802014000d024080034448010b0030304419500b107801200448024041c160410000207410124881d084145039400c10358a1900c0d00f007510481000000140d008481c1c0810001c550205038090f2803014544521001179990b211802c5080d1001a01c81c0500440100f003c00ca0803e0301d100e408003441e01c6242038070300c1e2a1054003a80c280440c0c201c9805 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 859119055 1250 859117805 859117823
    0x120201152312150c0909060907030b03100e0c03071a07050f06070f0f05180108220b0f13030203092103031008010b011706092205010605041116060c1803 67
    0x40090140340f00d06500010320380d022030808003200c0c0010000306010f84010f024104900200b034000b442600032110b006005030840e0340c10001071070164020002e5080780e49190083e02c0d0134244c0d03460089002000c8591140e44400141d0802ea00040240e203d410229200c0c45030381e041601004040c040b00e0700c0303138605480c2d511076080401000f0b04400c801700e5010080060402c00019510300ba10700403000410700b032a044a0543e0354000042c1e480380001940041d00084030660000c0181410b4050b225000741e000c03510060310391103141000e4264085009016800c24002c03074840d4200300d010750007090401c090f5009080301c01c10803141184d00685a800400060248c2844150001d014000e10000c0038070340020f402c42c030b0b108000304820f0f010b0100c2e03100301c00040114031000b000c00801b615084442090340340710401440c00c40e00074020b5224150180d400d102404484188101c01d4031004078066084dd000c1a04580d200380c000c2400941030301c00c5c44410107078440f25602e0030214a01a621401c049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 859120305 1250 859119055 859119073
    0x30b150d030e0306010e01060f080601020f010908181002060a0213030b150415081e030f1605100902060924040b04060909092310050a0603120201152312 67
    0x49810704e081600219894095100108031080c0d000d82040b901804d0751810b50403544498004030306100380010b40c1e106940c01d1100d1a4140312201c0d0080010b08043e40e482040d817000c51092200f41800e0b943e0200160704514002880c3e80c50640040044c204024040d006643c1c8035030f280886800d05607140c2421200d03281e810151401e0910869907020300d100c45031901540b4194645581d03111103200c0f803c4201d5150204541e1500070400c1c0d80e15100342c00700441d01e0781400d03041803040c0320900d0f000340c0e102e104041c204402062540300310011285c02401052529581d441403001804040c85007040d4540c24a20900d11000f81d40302800142c01d82005066642e0301e00b413401420900300c0c3c3c22410741103281c2085240054110042d61000c5015107807c02010758646a91608000c03400880142c0c080c145420405c20800903481001540d1140000260000310144100e0072580f4109540c1c0c001910103d06100180500c60a0301171000740450a2060050100200e2a000e62010030a4035a910103201 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 859121555 1250 859120305 859120309
    0x80613141203091501050a060f02070f141008090703060b18093003040204050912030408090901060309150b0d06141608040b040305181915030204030c030b150d030e 72
    0x180680310900c4d02e1100a94100030000703504000d03d03c20f107424080b940c014a03445074020300c001401001c1c1c14200c5420315503201c11300100c01d43c00b22200c0d44100c503415940d0565502541d87e040c0203000307000003014080d055650f0301005005440c0311a44c080c008401060107c0d90040c011480ba8110501070848100b601800031110907400660307035030241088007020000014582620b038400c0d01100e010800e40c0724a14070ba8100f0103600014001110000100300501400c00300800d664541918200d41c56039807800218216201048018007130803408002c0c1c02e007103500c1c0e000607001b2880140199500c00303981c0e9840b401c07100101d40328210700140e40204a200c07540500c2c82c003450b000c542810040b0786050303034986021800003800101885800706402d010760542c02140c04506c480a0b2030782c812805444100140c10195100303400300c02082c6003d181c1028824003c0c2d40490794404030211100e800c41d5662442c0c1100200b842c1000e440c0b40d00300c10301d2070765103129031500300d8060746481c100c60410b0780c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 859122805 1250 859121555 859121563
    0x6020c100e0307050604060f020915040f14030307061e0f0b03010507030b01050a03050709030c170c01050a17060d06020708040e16171e01062708061314120309 70
    0x603141d06401c14404500031a0000ca4442c1d8420b0b0b2000c800254840210302d0000240140801540c020000c5019900d03005002c2c070081c010340388000941031030660f036030b90180300e40240414001c0e0150421312070384001540c6604842c1021100709400e2100c0000e041120f4200c40c2c0300d1401c203180a445401422080c1020710541b82c101c0000c3c502800100b16002c0068100d216a00383d4404040d03581e000100c0b52032080521801a42d804818001e5071551a581c00302807003400200c580140c00b80301d06410b15903009000300c0f851098140c40740d00780000c2020060a11034402803e1315041a51451603070002046840100405445420060340391410801d240b000060700812021900400380c420b0260f0503084041442c012102c0c19040080d5a01e40030091400140c041d00c89120552590001c64140d81103007560400c1030305003010707000b03500c0080c40d502407411b02d134401e12015400120120f01c8401103082030400030750045800c2c04046003030f002202c0c6410703800005500107074004014014a494144 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 859124055 1250 859122805 859122821
    0x1104050415050d02011b0c03150f061a0d0b1f020712030c060506040f0c261e07111504060f051506090111030301120218010803090d0c0306020c10 64
    0x450140d62541464041141041c415901a040c0044011054000c50780c1384050002c887c2c0c00412241c08aa8a1400000251045040d42682420105180c01034815442000121106620907103604094a2210300f200c2d8015608602929282ca1421078262240580a40c28140021070207201042d82003000313007000ca480c2c0186483c0103d11034140d0110764820ba040700702e113070400300000c1d458440d003002800529408030401c0e01d032428004000000c94125030101914564400c4010103d004940c0b19070b561201102e808038808680b0b51412800d00b0242c1c0c9041c3d01064505080c40403540c0600c8040c9094210f001c4190740c1034200081000f00b190034002c800243d03482180038046414883c401c0e51416100c90720345030040c0700214807804c0a078483c07201038145801c0300f0300703803603403540c48000304150b03000000d005038019075003207543c0f204015042080604882c00007000c1c2d801d052184041242da650201d1090f288452000804800b08182e03100400c18014001c0007880c56503220581d2200b650000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 859125305 1250 859124055 859124081
    0xe040819050a1d0f090a09020a2126070507030c051e190f170c0121050c040302090f0f09030c0c0103110706020c07180606170a0f11040504 61
    0x103100441007542c2003084004104080104002e01490840c0030425802130301014950062621050050460242d800f03241002d00a035000f46100391030f58106e41c1100c3c03000b06a45515581040c840d0007062003144510b900f0299481d0465003d0354001c13070b0450740d0704415000d90b001d4000300c4041040200c2441d1a000505090f101c1c4861091500b01c1d081c00840d480480ca0b004410482c40c0644686108465a001e401040d42040e81c1c652948c0b0b040380046910642c00c90503104080000200390300032030344500300801c1d0001c1c00c40c09a440c80745960181c04040c0c00702072a404140400700040ea02c95008602c51340e200700c01c200140c9400059590003000c0030340001500d03001000301504212005c225280707503560038200481d40e041902c0c0510158400c010000c0e00162010481109098010580c1000c4441102c1554070410101071468112810791180c000800c030a420700402c4c02c1420140c2d0366202c590341900040c071402e042402429200f200910044800700003030144424980340c82190b00a40e00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 859126555 1250 859125305 859125307
    0xb0406050112020703030b0303030c0403051005101a160b0a0b090105060d022802010e0709020408150703090c26060408030106030902060d0c032a0e0103150e04081905 73
    0x15290010748002c0d100c1d81d091045540000300744e014140690003d502c00320f005011240d0302d00d03010300b5201c4503402a000c200c409018a07500d414095800c0d018981c020100c490300103020500d03140c6180d142003205c1c00f007810021814002a4052001041100b000320b0007106842414038101017140d00f00ca4403010580d2040b515840140702a403150010b5a0310181c0070080141c1d81c144680000d10003100c4003400318403841107600c0b0088226810b400c081121218403003100c5601da00c4131981c2d0107038004c0e402500103d40c06410903a400143c2d860119810440c68200090103118076110074008101c0d507084500701410707540001211f0108942030880548061019020904055841240398401031140004040d101c40c1c2c540e09640d200c8040760701380c1c40780080400805610010140180c9030000c1a030540600d0300c0a82500409042d181290030b150550b91a1003420302200150000c0c44803921844518030b04000200d41030481c054000d000310301405a090705c42274500304015084000c54214410084 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 859127805 1250 859126555 859126559
    0x1e080f040201110f070f0e0609190203060109090e01051617040f0201110f06060a0906181d03130503010e03090109060809160b0325050d09060e07180b0406 68
    0x282211025401a50900c0e0030a22080c40c800c1d50351418904540d01086800f46000004620140458110450707084161250311656020704110b000482100e158155042c038006014645009900031a400318050410080042e00d641061040320111751202c0701680d5554240f05640583c8107410161100360710703000c00c00c41032080001501103005400142190b841c800008210782c02020145030b40a408811102c0d610703204502c031650b4500c107840550007149255408140124a4000c4400307658241c10740c07500c001e858120a600a12890038003140100e12261811608076041c13000b000c0401501c0340c4203002906000c1003500f140c03106096a0115401001802d10782d9800c400c0c00c90884d140c0c2e060401d0983d440461140c10308200300c00c11a04a20704000102e141d181003405180504035946415a54600044044649032861b00184010031400d20040111000f113400210050748034200c0800c00740c0001c510b0514104513904520780300030001c080e004000e1110710030600c910204540030701c143c0e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 859129055 1250 859127805 859127821
    0x60807091511060906102304050f0708060f1f02010b0a3c0b0a02010221150409030806040e0c030d052d03061e1f120209030309060a0215071e08 63
    0xc0d125011410003108040021031fa480c00094005800180c4240034600d40b03056602072000c01102c0010114400e0030108419041c0f400705202080e1001d8174007000594034400b6256032900707850030f160866403121400b00c2940c5540380036074010500d81c0d030040f1a00e100e0030b00304581d10899803a8034071b0001e800246a00c0e44a1010941c3d003c517030303070101c4440d03075520b01c604201c3c0603100c3c8601880f40030700020b50048100408000d07180c810701c400c01c0b140804550f09400c00081c0c90702c003400900000c00a130040f5403949005e912a909030346907141194516405900402e00f0094400505000b0581c0850804003d4404e010044001c81103050b04c03989242150481010a0001411040c0030302125149040d0301c030400080713509003020080030f0749900f100c080e0514aa1003c0400d010700008c03504152002000d0b40c500983c2c5609200501a50030a1035201c24003d881c3c108a0b0345000314410321903c1c7c004050a107003514050314555440d040e81049a001009542c0750302c41103502000b088004114400b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 859130305 1250 859129055 859129081
    0x612090f080c030d1a040b010201021c0b01120e030c011d0a060908160b01060e0609031e0a21140301060804150b060c010b28060807091511060906 64
    0x5680092400e0b155610090141d156010340107140e80c544d40b4200c45c2e840740c14034104406060460480d424000180f001c0300484c00d0b40a41e0f0f0144045422983e40c0c98103800068101c0903285106150403000d0200c170b411542c060722414501164640c0001580380400e00080c01468030180e01010702100711440d1b50261030b502d151210026260683c0c507009401008204022107030b94007080b420350291110b9a0411807600c00c1c0c280704040100344172042c420120705158090f500041c80c0140036102043c2420380b141141c01c4501802d4010780280507050340000c0054080300213410310050b000402c480240c0e03010b0300100a14800380b01d0382c4010300c010849240c3c00208564000d03400302070410300c06c80c2040c851002e003005007071960340090b010420540c070010540c043c9040c00e008603091000645840130020313120081000110f0030659040f0f09000403406a140550404550701e44424015070320301d91103d0200e000d03100080044d07000a060260716004000541e000101d141c0a4091828000b040c00b0300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 859131555 1250 859130305 859130333
    0xa0c0c120b28020d0219111203040203030f13150309110618040f0f1805121605070608090d020d051e090301050403180605120a09230601061209 63
    0x4450071200b02282600404200410202000e0654444c186441070074040e4004644004421a1203010740a01c0c82c451400c0b0f2140b0a25000a0315450188006014459100600c243d0709840108a5014102038840081411100c01d40455810300d003001400d29800c82c16414890401d8100120b90011403042041d4022a40c4103c501580e1200441114102d90a9090300c5035482071400c2442c424201c0c00d904469001071040c6000c201a6005441e89074900c0002c0a001d882070780041c0f800d046000d2508e005100e0f0326140765480c030700d54400b43d0b512842c1170a10b41100000a1110007400780074030301004050151440d0340060141100c035000010543d000c4c0036040800124820480c81a241010f0211260104040c00a002614084c20f000e468030450310301c40b840c2c50144250003e200381c032504c2520305208211101500913210030709414081c0c0030310101a07030080420a10b18030118104642c00d001211518090080d5602d010303006400e451001d200c1c54215414203946400184101e000120 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 859132805 1250 859131555 859131571
    0x1120209010504120f0b07051c09120f051b03190c02030c061c110408160f092a03090b180c060a11060103030e030105100e06090a0b060a0c0c120b 64
    0x681c1001030812420245085c0000f0b8a114243c405104000d035001c40100a81c0030b200350a555070f1021030b0552030480c1c550b648003408400ea0500c00160780c501c64145034018041030b1070001c0c28480d00d40503030f4046811b0880302034640c1c1d00c00684584405580c0c185020441198148814120941c0d000310f900c0d0300c0d580d03180c0e43c4119800581005d0740460200c0c00310316000014410424000070b914551419032007030260000a2140042c1009085110303200788056403174510b07080c444145441e0b0b112024204405c15003a180e90400180708000b1303e5501050810381282d5008507103c200d50400401246024041c0710701c01d40c00602c0c51172400000107140025280580761076a83e0780714041c2c1222806551648904a4080e11000100789035120b80c511110060440c002c0040e83c48400c11120120280c0c0f103a4002d0560b88000285581390096117207901c540c0b201008600e120b1001c0c00140b061740500c6211010403401d045900174070082d8880200070340a201040c448207400d03034454000c1c01c0b0b40180004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 859134055 1250 859132805 859132829
    0x40b0f0414011d0705061e0a02030706020f030a05060405131403071209030b0906060f191520150c03130203030412050d0e011e020a1b0501120209010504 67
    0xd010029000d2010002422580c000c0260400d20388542402e00419440000b80d8850190302084a20702042200d00784050b01001c03d044180000e0790b0021030f0401618603095000920005c4085002c60008200200342480400c0e5246000201e00303044170005014940658a840c0c10021403920f050203040038183c022040803010303918003940c149117105100c802022840c0071151601407640044c40d043c1130b240300e50300200380c694a184801d4bd0741c0c5011200d05074043d002c0140f842003400c254560039140c0d201c100f9075900460700d4003c400800791803c000f520000b50034400401c0d51b41258200c280d036044a0781d029003d4000781a103103c1f4484806014913548040000102e40c80640b41141d4040041c0c0c09800d90381c84950700d00403ca40c0154968041c0c5141c001d10074020700d038901c113801c0c4461802c0b0584899011f803c080e15510300904d4580882c0d800d6202d8824442d0205090b4890316200015000c0401069401d0100040c81d4100e1480032505440c014490700caa00d0780c02030107075030607502c02d00101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 859135305 1250 859134055 859134061
    0x19050f160f080c0930281203390306080a080322060207060c08090d08070905030102031603110f070b07090302061803010b06070512032d04021503040b0f 67
    0x75030300900c542121006802d009140300400c82d0203074640c8034200c4217041624010038004440c4001400491100840c0802c40080703103001030164010b20481c110203190024101d40c0e1202032860b50a00c42c401c607144001d59500f0740d001c00304440100044c180c000e2506000c920300d40318045690b00500f10000b044004040005403003100f0300e03850314802c0020508550b001c002941012030081d030042d4415100c0131b0403c03003044e0308140148035181c003401108008203c20310003514220345001001d40343d807042040f50100020955401d0000d90300440c250401283c112031406000303821100b0400d048000c0d59810700c00380642041b4070040e5215a90001501c000303503555410116100074450b04000e50000c80400d03028000240a541c0107503612058000700314158421040050600400364000d1607544000c001d5079042d81d1030005590007140f422510210040031901030242d01000101d032018004903030382003200b54645262135440c0c0c4c00401c01040e146041c60b03101c0403d40c40340184507803c0c402194000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 859136555 1250 859135305 859135309
    0x303040b0f0f07021e0109150e040504050c0d110a0927050c1e0f0102061918020303120f13020a0b0304020d060204090c0809120306010819050f160f080c09 68
    0x444014a50040c04803555802c0c0118a0148988031005d1360700080d881070000c07a1070b450103031000204e260341d902c4400ba11403c1008200c098040180121420300030420011172031384840310340090041c03043c02c0e60010700160806100c10411140c0c0300300c0c09142071036026192a40c1c449000c62800b0192081040030305000d0801a01d4074100e03052898211112484200742841088180554018103c403142c88104000004903030b21403081e02d018210181404044113507248030381c0000520007020b401c119a103551a00080e0541d0060841181d034071091008204007104040e1403180e102c402c5a1049940e0000340e00416888130b45800740b40b040a00010114080d91765a8501000c000d6001c0c0c4255500c80d110a10000038064240500c40490b42190201c0c0c0c0120000c00d440301d503003541c01c0c80d07582560b23150001180c0e080c2014040313002c111503145020b584205a40605403042c2205005c5404a040851801e040c0d100e107100c6080030044c0340f200481030107070b000403030075040b601c103813205a240c900b01d01c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 859137805 1250 859136555 859136557
    0x50a06140d140709061d0f010b070c030b04053003040f1a0a02090f0301052a0408010c08041a040506150310090b040506061203540303040b0f0f 63
    0x840303209200f0800700203030f50515500507000f61017094807003032602400700e12001c204400607104403406004540c0140800810f071f00160180c0b6018203e0401d0180c2c0c4c1351588078680700d0958042e613607904100400800c2c030fa801120414203510340c407120351107070013540d8081803d07000c0500014000800100c0450912a980400c00d04000c500070080d030190524403848030081d4004a1854024038544084082610b0180314103407013421030202c0010340301018001e00040c61100710035441130000c10300010038101e4092040c0fa50b0b044064030303800c500b420242003d11070500c0320040070084014010410001034800f250954000c04d0240300300b00300800c0f48001a0070310b030184001c0d0b60704501e0886100d042c840d004003807500590260302541c0e4151900401c0c031002520159840d84298410008030082e0540801054900b0718800081e02145140352852318846102d65607031008100c414200c40800000414460001c80d000c90055140074945908042c4a014103040c4c0c114158006c11341d211420740c0e0740 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 859139055 1250 859137805 859137833
    0xe0c04170705011d0d060b190e010e10050d1b1a0712030e030a0c05011d012a020c01111005010e0106020714091303030615050a0201050a06140d 63
    0x981051860014014038a039241c59a100340d0340014240024018000f4011040000d0382c0740207040090f1400c1e0548944001d03040500c04290095042c4d076190140040d40c00b07495000e450f0258604559501d003010315403646401924900700c401d140c2c81c08218503903078514003554159022000d181d40c001d84078110070034040b05070b010513506501ca04404501e040c0420042800b540310f0b103000040380c4007100c4201c0444144842a5255910820110402f140500303a0042814412000407800003442d288003804003a01f1250041107179150005441c0c81d9200c80c0c1340019011101038802c102056800001f9034540405c200141030102d08418a900710000b0300034141e642010b04420b02013944d60300010882c04209210380300050050900206034600c800c50091000f0324010a580811388a01401c0c900703400071075208805159445d5800254a4075220456107070413450f0700d80fa0b80715501e504010342901c0c401041c0707102036443d220341840322200d00c2041070344115050355800420465031a00102c030031041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 859140305 1250 859139055 859139069
    0x12010302040513061d011b02031b0f030a0906111f0e0a050607050309061f0e0603101406012010050606071b050a080d0e280902040512030c03040e0c04 66
    0x1c524170700c2d114030249060a010030440081122191070b482d0300c2880c002403c900c0c0e0060b001000180700c1c1210707440c2c01c01400141071050310045071110045a1450b4044c0c00100e003c1150000c040161a8024030084030501a04019107000c0c14203030781c28102004d41e0406a1266070303039207481d0070705084200034405419902c070003265240c0c24054400750581c0c10884090000f4851940050b620f42611408480b0303800150700700c0366006042c03250b07141600030000c0010f6014071a80b01d0074529682240110200804d003410300300440c4c14404001400560b480b029101240c6c00307034002200940c40005e48414200201c05d0000e880d448145c0014040c3c0b2901902519002d03c10101d44c000204200b951400c6540848080c2941c603501d032451703038507208c10b000100049000c41880120750308003446a004000d4a100312003a0164844a8644502d6155040000100d501190030700080c10255066a0b202c0b400c41700843c14030561515481d500c2c8901d025465038401024045082ca01071401610003610031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 859141555 1250 859140305 859140311
    0x6080f1f030506040b1b0a08040809120a0b1501030e07050616020a151211030711070f090204092307050901090315020a020105070302091818010e16050102031201030204051306 77
    0x281440003103200c051b01c1e40e0021307807007032070545414404000c00c480780c503d4551112812039030786407545421508190380c41500000c406480c0722804805210300181240b01e4504200182822401c00c1aa16402c141180c14503162000c0780c0d594182c000350503404c4130b50407120341e55100700c07180d140c040c40055030314008d4000020890100340c411455180d04c02520807550b4101c00c2c50341c0f810301d00d4140d55405d00450b4070751408202203020540700303200000101d03031068100d5285d030395540710102c0e03540c41c1d550018142d140e0102e4240442c8080340194940200710100c0c60084201c1c6400101b1400000b07050300003030020009010341140d0040308042c00445d00300424400318503890030040701a51042c1808401940b0f07001c002001140244251383d0703c000050310810308003001100c80200303824050201c20312030441d0820079118034001d004044d02d40d26004003401c4410403a104400c03031620181c000b5415508240314000c1c109040b1104281101e80440d80401c854071802c0089071a0000104040c082c141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 859142805 1250 859141555 859141561
    0x102040b070b070206271c0f140901050307110a060f020c0105181c020f010510170d0e10180b181804030c03050c070e07080106080f1f030506 62
    0x803040c0060030405018024218541c0c0c3c07144401ca0b10740004a80c1c1c641e9944022048506038070702e194040c2559421041100ca0301e0311141c01014002c04820071030390000b9400c800903101070750b21401c2d03081852044038016044c48104400a401e50000500b0001004070940300200382190801140c002260004801c00c4100d0351541944040e40c03081c1c071400069800c1c400451011080301880c01e00c07143ca001c010302621003040040134800101b01120300118440d028580084020a11030309000d003100c3e0380c1c0020100d1610b07400d1000100b0403c170181c0030383c11115509280940050340284c2c11031080b02c054244000c08682502c0000544d0b9410020061031500841e880750328000509281140d05408945807100000300b02d040b40b900710306200c2d0384911a010800003402103111010f1b00b4800e0a1950410910502061420045501905100040c0000d104401e60001002405425203280c00e00c0c10b45807041c40000d4400001e00061542906031180b01104480074480074055503000702644c1140c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 859144055 1250 859142805 859142819
    0x3130f1e080703080105010206061f050f0301080304050a0501180326030f010f12031223070c060b0108070f080901021b0a14030403050714130203090a14060709090905010e010204 78
    0x24200802c00c0300855122000440c181d03000150203803250b0720090100b40041042040d10325020703640d4080100f4080240014001c10103918080d60217007502000030342d1580c0c40c0008010010040b54411414000241503525200c60b020428800383d9401c03001c400703180601d00c0d90000b19412400c0e0f07603000a0502209000408043c96102d03030480303107060010980f16845445580300c0038402140240405d84c1003407414480c00c01a00595103280c2401384210110091910880d10100201e1340d140002d080f8242650411010b0320030038059190a00e0180f1a5191600b000b0781a61503c0344032209014840b000900146001d404442e500f031540301d4141c80c944400f0f2840d540d10009c0b04002c65094403c240b01c049040400001d039400ca03a04500200074040c80c01094520100044072501d400c84041101180f4612a600045000d00114001001c0082d010704046a440d020001510501d0700541d09000b003142d440a102c805403055800700040458551904600403d0510034002c0d9550002c02c0c001010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 859145305 1250 859144055 859144057
    0x1903031e150b18130507021510140f060705101410260f0a02130e0c120304051e010e0a0b03071101060f030b0f0106080c0a0302090f0306010b04090f0203130f1e08 71
    0x250040c0e400300e40c420050348c0029035004004641c2101586402a0104824180600c2940c4001c1007c0d100c1030765043c0c1d050104440340e2205400f62002c1d07204a43d85c100041051017002c500003402c103940c44c0300341880d607081c4039a001c05101c0d03d004000c424190b46010300f80d846109054110b050215420400000299911003041180980c440d8540002000594056000752030714000854050149900101c00308107401c40600741e0600244004d01000c246504d900507021034402e80e55104041040c41c4600042c50101c00f408501d00a06100d18100000c000d150260791700b0a0300740c01e02c00050003108020b240105541c1d4003a01001814190010910152009003401200f00340d82d014207da0300c5100944907a40140c8444111180030000d00790b13160300ca58050130211b4001010800c1c1242030000083c60301a080c0c029074810040040c0400822680340b060920703520008400794110703d00540541c052510340d84001c1c149140d1351046108021400c41d040c000007003088800e4000004a0901c4881 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 859146555 1250 859145305 859145311
    0x6050301060b09060706050702070810060905010512070e070c06050c09040c08010e060609040207060f0b0424030602030a022503021504080d0c021903031e150b181305 73
    0x25481c0c58400b150a0a504007107505007440a08542d28000e01603a681c402040010f00840840c0101813002c2985d560a00c002c1a002c0021a0f011490138201520320044440690003284250744540300f0041c61140451064126640050500e03031680e2107000039543d801e40401d000f00750a1400080241c260312a001a1100c100e043d501040780180c00102580c10b00420f00440c1c0510084600003441d5203442c01c02800c4505001d04058200325450b6035000540746034482868003941c40c2c110707980440c10248107580c582d005480340301849040703086100380e0301029804044d20880d000800a0b81001041c0c04542c2c0209000440e1414101800300c20418244460000c90040c0100d01a0001500c1441364181c0100d402407070131303868280402030000050645a4080d0154029021007070200d0591100521805000351004200440031041e00315150b1151464450701500d01401000d000f00a101d829050b280c001829035a90960b40303915640540c0c44d44146540110071410303038800d02040b60050783c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 859147805 1250 859146555 859146559
    0x2040914010506040e092d21091905090412030b10050f0c01060f080c211f0608061e07020d021b15030c0304030f091a03090c0a08010605 60
    0x601400d04140c001240a00c40c540c1d00100c140018040028090720050300300c01c07143d040b035078014140c01c4101e401c10b50060240009403858580109a41e00030b000c56240c00700c08194461401c07101e192415418007030030924a000714801c2d00c1c0098009801b00601e00540002881d100d1949042d28043c0d01407400404028000790810407c0c080324100103a07a503140b450b00b030322441e09010510f203541000381c110744d0700034030b1940d01d401000805404070152007001c0c0c5a64070103040804451418400d04070b0701b0500d100b40c81200c204a0b02414031b000f1800c0c101d1040401f0104102d8007540c001d900c09889141c1000b50103016290600c00410440014040010000d0206280aa42e0120143e0301d401c0c507210305101503088054159030b00c081811452280b120010a90310050760f00401100158008451060314450008148001d064201001c0c03800b80415141c06110941404e004501c0310446203096414400044041a09044140107428507614007414046d06103658280c024003800340da1042134 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 859149055 1250 859147805 859147811
    0x303072708071a120a0207080915040819211206080102090a0b0307080f130506010308090a08060c1204210f08010902070b1b070203030706060609050a080604260d020409 74
    0x6400340b0081c000c1d84c1480140314281130707041e81d94a43c0c00d000303940001001ca5100c0400c1003c403000b03a451405021002d2802400140c441d400d191030107241c60100b04226560042e1000c1800c00501080710401c0c1e1030340503444d4074245804a10341a6020140d1000c08800f4900b0124003056943e415806031000c94403ca40d003000c0e183d80d17040101d1662009840f01030000c2c0c01240050040d030514151940c2243c0d200c070720000c0980090b15082d0405a00b070704101c481d0100010a0074607454420401c0c0c02070048940606000d04001c3c81c2c82c6650f203d14115100c040051000080600c14810020065060b0710402c04052403650300c002051b002404d0144e001240c0c0b00800400c6c40c441c644207a404080d0300105104564580b2400b0f1703001062042c0300d410500104101c02001600d0a00150484511401c1e0100d590303030610360054080c420941045010b02e445060802203210002101c45c0c21913008011403201d402c90741100b00e465401c506154443c11400104501e440882d03500510444507442010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 859150305 1250 859149055 859149089
    0x61e070504080615011b08070b0a050c1206030a02150910090f050411130e0103140c100339020105090c150f1c1e0905030307270807 58
    0xa032141e0159000c1c00300164440000610806440d01501c40012814100900a51044030150045400310202243c102601003111070400580030f41c4982c111030810001c0c0444c0c54140c0598020f80152240c0d002188162004500d0303c0e18184180d02560750003900792282110a0810350402d54048041c0f14081c130103904801844c0c0740300d09661810364080b04450004285498100f0018102800f030790310b505c7c14104042c3d4800090000c0b070b88000d25040628a510790303d9414180e01e401400d0501540340c0d00071503c201d03803981c3d0310340c6a00c18280850900150140da13411252034890b1450102c41c800070b070400c040000c10705101c14200034051459000b0f010940e19486103613115203040c0b071684c1c0c0001c42c5040c84180150a0380162500d0741d240c1840c1c6040240c1e0940c280300036141400b40118859503016118404080c9000ba0b03042075514400a00400c4050f0b0749896070b80c440204a1003c0100440450070290511442000300d54801030203035140e2502d076044661580120310a55007072154843e11 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 859151555 1250 859150305 859150307
    0x18030b1003150606021908040906060201050405070608010617130b070203090418050307260a0c0b060121020c0a020910060e010c0b04030f05090402070303050709051903061d061e07 79
    0x1426040d00d8403603001d820242880031030340c8105071b4140e0088505007014400428212107030b118540c02031010790700100b81810309041ca141000b140340c02c980208548140144105904803118540007041400400581d0b5075221400b0040a402c8000a10103010942405801640040a00884042101e0401024014044596454007c01d100501c40e0700f041c448000410311100d20202d648800c001e410500b951340000149960303202d643e42c2004500600d078040d00740040304400940c440003c0c200304a80100310801c200000212044002c1c000b500021501001e41d000e0200c50710042e4058405c018600b0a5142c0201c401c156000c3d0707200051326143c800c9415072080066212240e0003005440c1c16441e03e0306c04039180c9094000b40300500400b00001155902d03144020a910b0b0f010350fa00144508244100074070210345a0700140c41402c10304a68240d10140c03c1030700c01107951003900042c0603040c0070707100070f003040036601405040d00400003040a50b2041c17840100300c185c01704a01c200c140d030320540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 859152805 1250 859151555 859151561
    0x131103010c02060c07080412030c0501060b03060f0d1401061415030105091504140126010204081b24030412020d0e10020a080f09040b030c030d18030b100315 69
    0x12a107401a0b0020010990013020140206180360048101600c0d00361294020344004c0700300e440c1100042c50f10f132001f000b170081c00e01c50b0502910306d4800395072840c108040010004007802020768465000d10b90762000b001708610301900b0801002000303000035940c40300315145502200e1101760184003040850311036a03104804a81c1070700d000030446692615040d40304c00752171201071541c5402594503040101600102c0d0b080078002c10f44902e226503841c400440b0b000b00c031507140301e4041d4103030f0040c001413251002c04200540c03002841c0300e10140b10b11150300040c0c001d81c0da00355041d5440019942404528040c80000c40c071650003007058103003002056000300d0382c0d032212100c284001200f0281680c1186494190250f14003058411a07080c1d6009481d400e45a5001c2c011b01a11840002442c0e1014140703405050302141c1c00300d000c0d0080d4258980400c1c1c680a42240281c200080c01c410b0006101002d03070b01001460b0401250021468116032808094116000985000d072941d80780c412a030080380 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 859154055 1250 859152805 859152821
    0x40204030f1b05180601030c090302150a030b0409060606180b030a0207050c101206120807120221211603020f0904020c0d0908031806030c0d0513110301 67
    0x700349052101c9152030360140301040b03074000075400d01d02c001c0005541c0da03421001603480136061080e603424108900054211602c01024109110442d202000581d9509800000800340785915a03602d00e44e40c04106d00a000c010320759903100c0d1503d41c00c0340c14040507900c004152a2141c8445000350140c2082062082c4580300340003031150100005036001449401901d0542c4c4901e0454494000000025810701d185640c05000580e15501c07618100805019480040503503440d0801541d0054a0300200d070f00c00d9102c00341201000580d581c400c41c2c0708000d415400c034400400403912002c000411501f176801608c48a01000b101c141c03d044414040700901e01407404000039140c5603004200a8000c1c0d0000c3e000e20480200500c8060100d80720790004018101106d000f402600c2c00100002d0705030103580d006282d155006110300b14610741c0c4110300c520784600443c0c5003602c5e0781e43c8494110a6110b40c0c4040c1c5116401d1030b050103801000540e030802440d111340b001000000301201170500300c402c66 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 859155305 1250 859154055 859154063
    0x703050c1806090f030102031509061c14070302030f101506050a230d05010305070608040b0a0506030a0609050f010b120a2306090709110702010f050d2a0e04020403 72
    0x30240600d00b850040000e2030042000f03451411500140b0780000c0c01c9130000c8510a032840d2a0b4400390310300b131501c5510503078004d2040380e000d4000e600d090b00080c00c0100c00a401400f0790408112a903c0c40401c110000c000c650090031140d6a0f030503058803070344624507014104c2c0350500f0a2201050403455001c10002d8031421fa0b10b00741420080e1104481130310452642c00c81104030340001c3c0e1007204018005192072115408003203280d501d036180040c9018a55844403003040312507814400040c0302ca410300c64000400e0907000c1007544850380083d0510418040060043d460840100100540411000350701500c1030003c000035140c1009124030844405031001250f00880010720024540300c4103040c0c0749807440708000041c0c0c0c400c40014a440419100c00382e0940c80080200300c600c03038a000e030401400e00e41c00308505200465001800748a00e0090600c240305010401c064154080d903c442c480040d541d20310942c0350045102140341d80407030381c2c900c40002c1072070000403d64109070017220100ea42c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 859156555 1250 859155305 859155337
    0x1d01060f060e2e02151b090d060e16080d0e030d1407020607060219030b0d20030a2a0308090f011403090c2d1302070f0b0703050c 57
    0x1c000410040080000305883c0c001060600030200074440c1c8040405021141c000344034000a2800b00d001034900241781c820b80c215041802210401d40c5403c3e26416201a030f40804030205915001c0c014102030500051544900d144050a40c500480c018040f6401c1c0400d4030710307821202c0000c84500c0d07804141281c1640c0000d0038002d549200b40204000200350401c01420801c06600040d007541c0059420303180b0a03004120180005069101c00c03124414030b007001c02c880e0311102c0c045065800086805014004030b6032850b10b10000e040c0c40840146c1c0c0c0142030b2a041c80b054601a0743d20f0000d40d4580002c0b4480350070844003d4070f00c0501901750303030304580003500340410141085442000713040c8035030400820070700f1500482c1c613040203107000354038200107084003952240a210540070510398000d60719000060628040740090030b4500304540503a2603d090700114851140a84035141000f4040d503003041400c000c1c0107503000702a000310000d59044c429a11101003400036806001088802d40d01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 859157805 1250 859156555 859156577
    0x1f1b2004090b27030f04030308070c200f0402030f0417180f060c0a1406060d020d030e0f060a050c0d020102030f01140a0906080a050d050a0912060f1d01060f06 70
    0x10000c1a2030a05003420030b04030f0107500046243ca0440e00800b40318800c030303080810207104050300070307038415809801480c0404100003180c480450710302101d0650315000000d44007205054440902c007e240c41e0340039100b07669904110307015080304602120180c504401d000e00340102d04d00140f0440341d0000341035108220308401d4a007007259103400e040126038464020850821803040920a8800060040d01c60b80003481070403060340c0c20650018032551049800d200901c0040e0303600b0310782686498051030120711400d088c1c0041829011410700f11644100c1c045115242c06600c00d0040840c040d102081c1c5001300d99102c01a03007030b40030642c1c096904a9101005101c40800701c4d240300350340d03140104200003880d0b035000300c0e030125071a0b0381100c14a904000c118205000c410400d0204242c05454120310f04802c40c4802045020a4020314000d8078040000800b800215041981c410480440400503c5000c155804d0702c003180e802c0c00310055090080004d4510a500d1044046580b82d03117480000d50303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 859159055 1250 859157805 859157821
    0x12060c0203040b120a02042c07020d0804150b1201020a090f0b030112050a020901060906020c011d041e020a031e05090c0d02130c0f120203061f1b2004090b 68
    0x24001404290340e1a801d01000035011041080410310040e40008524618800c50b120f44900230020802c8081d540004405280c460b1700c8280f0561058000c2025000704244030b542c1005082c0c0d100850f54400d02d40140e9291505041d80141000d4010f0f44070310b081c030b079521003145000030010b1044442514042c00108035454040541d005014801c80a48010351150303400580c05039800e8002500140c1403101c2070012a4040280c80d06c0e40b2400d003008501e01080c4140b07100c81005240c40b09005580b110310605400d40040328416000a0a510640d11035907155002002004a050309010042000103001e2001c1c3c0c481c07150f2030041740910041e00c0701d404800240403074031a80b008201d07000b4180140c180401d815601c1040140c550f0340e9a07410b40d281c05080000c0c18124440d800d80c901910400c1071140c296241e00304494050011010581c40329800402039030400e05481c1031101d103440180380001080784002010411404031207090a11201500a10045840305000200b00c601d00d180401c58032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 859160305 1250 859159055 859159087
    0xc100804021306090204030204052503110705060405011506090b030406051b0c0105091002090a14190603050a0c0807050702012a0b09070603150e0403050405040612060c0203040b 78
    0x41070000e020081e442c0007604a070411a07650364810101c1d01da000c00c052046190034080d00307400203d44910700340240e59901d003002c6544814030b800010b00d56661a9200b0040050042d01c00c156045415144036180c00e003800c6001c1c10301d6829201d242e550442e8040303403160044100e20b0030784005a2460303045d0b03070719540c500c03004010160100500e01d81d10900c080686282c40700925070100020000b0549007894103006140c80341100b400d14156005010005480c0c5a40c0d00e01402c0b03920101d4050225807074240880e00c0400700e5041c05201710f034a150086a0141c05400c01806044118410000500b5030001201d0a05041c0c03984c0c40055001c000801c0598400c602402e92070003203e41c88041185c203070448540b407901d100b004440c0b01d0540800c1150100e0180b000200800140c00d0511481c80d100c9031890001e04079010340504180c092011400785849001600c1c09030801502c10020702e80c50b440d0f4003099454200b811100c841c2058007051086101000f5502141c0c42c0080c03050900c11222000031304 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 859161555 1250 859160305 859160311
    0x10e121e0f040305010e0606120a031d0d140601051017060a0f080c040e0a120c0317010f29030106030e0102070204060303111207080304060c0224180c1008 68
    0x80c401080c8004078402a150000340021403254000061801421140a040141c002c0000d4400d6842c101c1041c036140010a03080181a40751419441d10444180d9505440107030400064100101402c070408101403d6500726014080c6070444403180c1c0c0c0c80e8100507400f0009141013000884504c1f2001c0d00e195000500b6401102c02840351048688034250640345910690120035a42d0029201d90302c40d05061044128003803601c4094045566151900d0448400c1c110300d2604000c64209414249071040c1a1080d00884801035505196520741c10303840c0c510403d0141c41c990000303001c1250400c000c400c44801060502c880085e045a02e4000258010401d508141c20b41c2d54003000000010ba03202d01c911006180b01e6240c2e0507400b950009260320700a000342d01c0c140d00c80800c000d0b41010500003401d403030b44198850b902152441c0b0541089043c80c42d054483d461103620268401d8103003900c841210702c226005806611800301d1200010b5407a020000b4080c0c01c00c003402c0310143c032680700e10313401d5074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 859162805 1250 859161555 859161607
    0x2250e1806330d0b0406050114060c070501050319020a050304060f050702060c090307080f1b0d0c262b020a0c153c1d09102303010e12 59
    0x15801c806481300c1940900c11102214020b0f45d03000180100c002c90084002000f0080d00e0460501c0e490002c4c40342d5a4005010f007030b050180210010715501c0c80d0b014041440c0f078100b40259202c9010040182040d0801c0e03401f21861410030305030100d008600c1c401d45102c0c8996600038040703500d41c5131010001e03501c01200700b900f5029096000c5581c4404005000711b0b101c202c00201a02c45030103100700d60b011030350302d07002e0701c611a00301c4144040b8100d0a60070054816458180004c0840116200b8060854a00c0c040450041c294442c2d003c1450341d00c04459a2011800001500e034010b1003240ca81c84000401440c1c030400f14000d00c40d881804010300c0d001900c0c1d04040c1c03140c215840000740c0b600075913988500b03124440a2017100c4800c070460072250700e41c2c403401e0801c1c15042c425601840306200202d00c50150303440000140601c0b04005489008212004501c00043c8084e56111140300c00100564060340c2031140e840d00e011400124800300303c0718212428100702d04090100700305841419003003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 859164055 1250 859162805 859162819
    0x7111515030a0c150c030203030f0903070f060903031a06040b090d06050f0403020d03110a030f0f020d02090a0506070302060619031703091b0102250e180633 69
    0xc010780c0303003046109401400f850a044841e0325044440d03501500c1d403401d04082240e01c0c04114000b1742c001065940200804038240300c1365a403880c0e03207403550240340740140540d0401c0040d042405100d50008030100c0c0255424062200e4001a00c0f00c201c03403911005070404000c00040024450701c0b8040c01c4103810082150110032120380380e42d015901d00f603410129403d070700002e1101300741c3c040112507408a900d0505116245c940c08540409005d9409080240740c1c41c4d16448a07000b11a90001c0700b032110001003151181c2d001d00c0e080d40290401b5040070b00a02c15501c02107040d150090035641079603407640c01450f4556a210900815503c814600c00064044e04400300004031210303000c81c109007540b000c26850f407414420180c038016030b4200031900d68244540d0302030580d90100d4402c200d080800700c6001c454400640c0440003a0555015101c1c03094540700b4080d03240c0190940d4224a006a01111100e4031000c01d00032030300c140352140d94009080341800d9646801588a01101c40f10000c080b8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 859165305 1250 859164055 859164091
    0x60b03010603080a11060f0403052a060712020f03220c0909120309020102100c09091e05061c1203240839040e070303030212071115 58
    0x2180c00e5480c5500120340c0040085084c501c1d80d54025000c2d1240c0c8030660040c42a07062071450240c1803a80508040e0411400107a01921002d40380201e10381d070166000c5c0741018402c6419100d8888800b500d8200000d100e5600011414081d8000e403000000318080352443c607280c1c05640c4019118420701c607905c40d8030909071400451007482150004181031b800c0072845100c0d0740380c01d905c6c003900c440102c024103141c0386800c00940d03400500c00c49104086c002c00a40d20b010309005031100b00b01c5501c8007560344d0500d01030b6040c5c26012021002488401e400900c40c035200c6404010148410080b440c28400c0d5072240c0740e0214100740f02c10503040605003000035240c4010f07204403448605003500c464030721118000401c640041009240060900c0c800c1c3d4014250158100e13040242d01254000b4403460b00c1241719040b1350300d079400442d203022400202c5007215034924015010350041c034913040c00c8a50503000140402d003e03000216030400044060140340600c92016110a00c1c05040056001504649 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 859166555 1250 859165305 859165309
    0x3090f04060f1503060b0c5b060510050708074b14070b0c0d0306090603020a1701090b010f1a09010219030c06050f01090b0307050a0909060b 62
    0x70020140c43c021000b41c06040c0302d0003016060f15400d600c510160401084000540703400410104030001c4120320301c2481d00c41103480c0071001240200105200c4044884d014003141c0301445540501e51240000c41414910b8111401195142e100c1c01c1d07000341c001301d03020040501c00c0b00207001c3c1034032036080241000b1090300e0f40c0500b06003031001d0ba4140442d000003c4c25000d00115003003c003c2c8a8482100c5081c2e00c01c08c540e0245000c02401403d1885282101d00c845200380640e1f405000c0440d14981c94984021300c881e581d40f440082d2001007490204003103483c001c0da00030101541d8000e08140001da20340800c2111000c00402c1d405041e5585111450014544030085402000c8101004e10014205078030f440007a10b070b0045100500404001050303080e600031544034030240301418030710b0b40307400c0504042c3c03100000a54000c0910385000c0030003006210344401541652030328181040342003c0c1105055880071207025199210036452010044140c4582140c00301e07130302c2020049803050350040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 859167805 1250 859166555 859166579
    0x4030f050f1c050106121a12030702031b10020a1e1506060203090109060c17031003050f0321240409020310060306111602040902011b230a030203090f0406 68
    0x400d070303003554985004028695101b0610b0440403842203003041704445003004440304413080407403140601c24036201400e40e40c00c2407080c0c840b42d076005000d84061600050707031034010a0aa20145205403220040c15018510020b0001141e5501c134100180d9054015031690300d0700320b481400c4840365116214103580701560b00030000140b005070002c603100d042c3d000016100000035005001080001020380010400707a11100c00180072406880380c1c0e1703071600409910150715980001c6d029100301b0905600f100c2c000802400081d409240401100c1c5c0d60701c0000028000641e01d8600c2c40a0701040f40c004e2100d81c0d984289c1e04035000304001100030481e404030303003800c0c064032a11072030646e00c075800c1081c0942e501556980c480360700445031400c010130500d000c0e50046054080d000d942e80c0c03040901117902038400740e01846204515006507801c146400701d030012a03e02c203180da41b0509103060181c0e110004000310703880d60ad500a941490810010311034201c280740f5505900c152961000102030001070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 859169055 1250 859167805 859167847
    0x5090c04152102130306090309052e0509010f0e030c121c05070f14031314010e0102010e0c010305060a050a031b050609100f14040f0e0a020304030f050f 67
    0x348584101404501448400b007003440c0d420b84009004000c0243c0138407803032a400c03080c1c2e64050000190100a42801c81d0f122916400c0150001002e281c55851800550141c10035501d00c0001a01e58011150044a150140c1121030740443c1d1001034a4001e01d0040344007420b010f2015088590400301280095201004031a1140058020080003050b801d01c4244610b118540b60a005241ca00f243d0344002051500341400b86c119050305641032200b0380c060080381d20304221081c80c5600507403240020b010020458103241e000c5441498007031100d50040c0541e90380b0744100c1e0080c040c1c1801d4400103401800c0b000380a01e900c000c0644012480c0e5030b403141d6031000ba40c010303045105000e49035560301d150400300d6000b40384200d1061100380c20039543ca18403a004c1007410f151900600e40070b500d00f5988006454880300c06400c01160125140e001d101002d0220781c42d070a5451500e03110040c01b01d0807440180d43c0a03000422818020716220300440051140c84c154070107581c5040300a200c84080c0403454 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 859170305 1250 859169055 859169057
    0x1d060d09060c050d0522031206231c0308150604150504170303010e0109270818060c060a0b0d05030d06180203091b060f03090102040609170705090c0415 67
    0x4204052410040d114240e48040700c07460940103041c880003146c0400c064540c006003000320801d4035a032114225042100204034603030003500c00c0e01d102c0d035280c148003084142c3c503801000100d101c4504505034198440010742c054031258015180c00d51810510348a0f80143e5400c40d5040000141c034a130302c058640700008066032496251824140181d609210644c2c00003e0b42c0e0003440180600942854494116440c50f40d000403001d00409c0a6843d060013030306040300c41141403080c0700034040340000800a18078140300c5011114104001c010140c0118044008580c3c005400030f080c0c1ea050398002c584601d40100280780915150356a103165030300100800c040c140d01d6020420a06507050070101d4154006882035003185404102039598600183c80c915000c1810340e030b00d24160b244c50040354860080c052600303940f46020141c250103948184203080000301603c500045501961005c0542c004984000d03110851510040001e5218060001c0c0312503942004002580301c1003015410000c0c0207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 859171555 1250 859170305 859170307
    0x1090b0a02042c06041503080c100605120307110a1a07170c15060a151d031504081c050f0f0601081b030406020408010e0f0c011d060d09060c05 63
    0x41c9194100000f100b5415249070000341c0028004000c8040b055540c4020142c800081801c051003c83c0400070581c2d001038103d0301c002407456103080d00031800c1c6929100c0030310240280c0395100280841e0032503000c42009a508184078500000d0700351071b4090a0300d14000c09202d0700580760010380c068a445c01d0300030010440b00040034807c1143c06420318404d207415580c01070820840308105a200c50340841c604080c9102e03003000a8a41c1e0750011218040e00c88581030f821820000c00014010300c0306914138400f40c1c1290880e103d028503000454556100e410f001c05403407a22a43d031754407010b030410000404070682421641c91084180c3c03154038420000041100b40030304042c0b10b0030006c040007400050400042d40c0c2005990a68043c120b4115418400c800d80c0c0ca5030340341040c100038065a082640f107542080024064003c0010704009a50100403e07290600450001910315420f002c0006c503801c44506104280751600c00c0280c00c00d5040a40080740d11300e0655a4002110710048040d408200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 859172661 1106 859171555 859171559
    0x13120c0e070c0c05031912050f0a03230c0301060c140a1b0803250204090b040606090b09011802030c0408150609150f1201090b0a0204 59
    0x4560505140d080007400200044a0100b0070380b002c1c0710b4584041a50715000c5000c2e00d40f5480c1803002c14100d00d6980d02c4105500c0325a03410000d21405101c44045101060014002407403503a8001401d40b0019542d00700c28040c3c210340003c8000b003801046140002c00c0c084034192403541c2803202c04859203150100e03410000641e10380c0240a160758500070425404102c44645100c3e6980402460b26129110395034014110410004101e400045002c1060b40382c0f440030003070000d80301080c512019100d40d0320b44501598102c40f0159284010803810400307218440c0000c2e002c0312244c00c5945401040c0d00c981c00034030622103995a000001c00ca2509201e82201c00500d6a8015558804400301d17905008000c1103604502036120361000030080c0c4c3c45c00d007040410000052113124a40b100b4801d020b8075030b50488100712659a07500c800408221b6004a0a104414116003d40e642c0c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 858992805 859172661 := by
  have h0 := BRFrame.cov_init 858992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 858992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 858992805 ≤ n) (h2 : n < 859172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
