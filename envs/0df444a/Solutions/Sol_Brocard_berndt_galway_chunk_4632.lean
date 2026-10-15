-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4632
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:14:31.279003+00:00
-- url     : https://prove2.me/submissions/5fc68e28-a6da-46d3-9c87-b4696c914593

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 832913669 ≤ n < 833093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 832914919 1250 832913669 832913677
    0xc140114030c03060424030b010801020f041503021218010e0c030d030905010209031002130e0609160c02090906370207020a03150c110109050601140f090405011b110601050402 77
    0x90784a40c1303606c40c5c4c44030380310400030b4601d21120442c4600d03a06445c500b40100605010380003000341d079004000742d41005080000b04d03000c40781c401e1480900300400d014220024012504411101c071400c1d414040d803070311090003503099030758486c001b000f80c001c0c1d01044581c1c0302c260311180c54154000d9038030010315a001e5400000c0c0203010f80c001601d81415140001d00b00340c00c0030590012244d01041d64003540c05a8007120300985102c04600d00395007031040005542030402490142d400d5580180c0603116032107245010410b56000e8800c4d1900c0c03c0c40400c1d281c540c10200e5000030384201501d81751168907000c5005440c0381210305a10440c81e0414600d9801035440b202003a030304104445c400000003030b030500e40d0520b84008540000f62100c040d02d00200348200041c500312841e070400506001283c030126906044400c4001c40e81603444460000c103000300560111503a011248600300804d000064000d0f1301440f60f80442c3d000b115002d40c0d42644c4508607407040b0291548403c006000ca401c0c140c0c010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 832916169 1250 832914919 832914931
    0x170604021206062817070f050d031b060204080a11042009090408040f0801021201060f080a0b2803050d17160903080c0f0610050d0201200a0c140114030c03 68
    0x40e103000b40c44003001038041703480d0030b0440c1103503103c208208410700b64030300064041c1c141240c400c1000c10a51710002d00810452600150004058070280d08015a42d81101c0062910006a80c01c072011f41c1070081030f040c0c41140b024040d0381402c15203015002c28590380754a004254240380d0a080880f4284030516000030710850f0040000c00c408607000c9560750051005081601c005a558601c62802d6048442e040c3d0100080c070039620842410709400924080d80905a0100020b0505a90002a800142ca40071302ca02c583d525048402540c3c3c0c0c40101c20341900c0c02079085130a070304d02c082800c69008844c01100001801d01c40d0100f005c000c43d69403204500b0b011464400c081944a4403a04d100c2d0b440542d68049507803204640000c154028007445a1207004190b10305909803400000c208a9680d44100904000000c00c1103c02d180b076002d80004084104001c68000740c060345403944a064043c0100c9881101034111780030b0031740c031840d801c00e041070200025a0841e05d403100d014189810107044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 832917419 1250 832916169 832916239
    0x50c04030b091e0607030f0b06160c1802090f060c030702060a020a0b0703051509070519120213030b130503251502030a06060207080604030e0a17060402120606 70
    0x140080501110300e980c100f4649010140540d0b0820440180031110600d512101d680e003000306080b17890f41c3d04ca055580b0341d80406c2c44568041200d107080703c1450416000640c140c4105074401540b1000c80c1c1c064100c0f202c054414090307506645041160034011030524406580c000c104500040c1001c0020f41034420303e5004444000099642d582d240d208211510030000b65101c04000c51020705003007211031600d0585406e1044d051818000348141b15030200a050700c40c0f050174000c0381c00e104d07510742c10056070405800c64454807c0341c11000013034100c0c48141d07036440180012074100780300304116140c050f43c060001c600c0c0c1203c0002d0300c40b4000048108901c2d4401030030002c00811308840c459000e2a211070401a981e01d04000c00708100c0e407058000004541c02000300b03000d0342c840041c625800c1078060400d12090003400d0006a8601055003160700c072074a0260451002ea000090190700451084407148c80001221030016a901030440f140707540411101c01109480c801c5420209092002c051 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 832918669 1250 832917419 832917433
    0x13080102040b0403112b060501050f0306160504050307081011031003060504020109050303120708090f0a0b1b0a050d0c0c050d0806060c0d09050f040540080a12050c04030b09 76
    0x107a400b5102c1d15038070003241d000202e20204010001d40c8c3c403826000d000102c0da40c103500c64402c00480da40e400024040510002c0300c0300316810709801402910001c0400a084801c056280c002c0070303455448412500b9061401c02200315842e00c07001c0c0503a0300c640c00342030720061441e14507102c0340040c2070040c00c16818803070800c3c4042030a032010300042804110719a02c1720202e05000d00c0003414014010b1905501e074004c1e200700061460045059406243c014003180740d641c032808103144401955103681d5204070300000300d26080641001c0981070741d121506003049486249103042d120042c1000e0000c0503501304014407014a401046d03040d403c108041d2019051801d1074000c0b43c684004149032034041400c41004200701d152021a1103801394054800b4040b505001c4440b41610f100800042c080d440d0189a200411510514001a0f552940070412060405040c200c210342d100c21986d500140c8400300e64501070b1034a0007421b025000e000400c6181c5441d50700c9d0707103190707a2002e040503556010300c0d2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 832919919 1250 832918669 832918699
    0x1110406082e061707090501120f0e0a0b0109060602010504020f01110721020306010b070b04170702040203010924060503070e01030f1125030e310213080102040b040311 74
    0x2c1460015012076160000000c1810444032000a4000d1942c1c04004115105009070390b4880c40c880d60604041c1000701c0c10300c00a11980000c1e00d8603242c110b01034810020820705111a40d6600d60403602090410480a501c40200728242c0710102c1e0003940140a42d0041c0c0c50075481381d50481e05c080f41d601c003600c65491700d0f14040c1941c496000100a0011440d9128030103510f0305100240c01444041c14651030480946d6032418400720080c0081c01200040c0c0290841904040032640d266078010310440d665138403000d41c1d000605054031805002c8240c0500c24030294855100c900c00d40310980c88180c00c40d030b10030701d048a900281c400742e43c0c109500c0340f500760000240e40c0514010302102c001c0f40e50b1101e01401c00050032800031403199001302c0040c4d1a6030301007600a0619080004203540a0002001c08100903100c0144800c00e00c0301d400c800440f01034641c40c2d13076000d4450030001e031000b5480c075950382c0c03111030903400750780184503950030301700400c000047c1440d40c1c4004e07942028150070b882c48813003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 832921169 1250 832919919 832920001
    0x405070c1a01030b181915110324030f060709140f150d090602070501050901051b07020f041b1d270702070f060305010f091107020d05010f09080c0111040608 69
    0x20307102107038040403078455200d485001c0c1c0500b5420300c0445900390b046203010800d062b15400030351709441e0802541c103c0ca14150300c00740720100c1004582001c035012810300ca140201084814840d100541d8088410800360b80303802c800c4403040f148001e007a9100000d0a00c00500740c0c2d4003460b04110003580d208600e80004045001803c0020702032400001e6030318003458454291500104480c4045c03c04050342440340302104140c66071642c0582e041c01511a000c1c000c80e0050443c0e038840c0b44125104550b00e110308d035200110500d00e01c0c10782c2d802ca104e0b55891042c002c8400008040360b91207110760901e003c000d510070b043c0c190b02c070009104603080c0742d43c1c03130340d85000d101d100360800000030b0b40761401400007090300458000100b4501c0e1003004822583c4022010601600c0c80080c0309590403007101090000941001d100100404801c02403054240f802048903071095001140395403c00140144400c407113000e5030200c4201c0d4540c4900350b80c1d0540c80c0c0340c1c4402020310380101146c0305a0050600310b40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 832922419 1250 832921169 832921213
    0x1e0f040605030a0807120e0a0308070c091107031106060109090908040b0408070608010602030702012c0301020409061406041401050d020c03030a05090f06040c120f020405070c1a01030b18 82
    0x5504d0080d980d0001d41489800f4046a05031042440035181c50511103032030b0307900490b0441ea04a0020341d1075440358540b240708410341d644078684a40c1488504141100150000c20708030b0710984a01c0d541c82421840b03a41c8800c0d0458449020600080007000601801e421008226210321181403400740c803070782d80b0300d610780090708045000c2d4444641030180c160481c01050240010f40011402c00410387c1c002011840d4101203040f24078091900d1803446030080c0800d0303d005400800075900c175034030303169080c0040119200f01041d41c0a907088050540c10180c00f03c40030b40d2032607102c0004059440740103440987c403030510000c1c03203a820800c4054a18007031007d1400f40300503480202e6181403000c0000c0c1b81101d01a0f07104d1050700004280070008000c0139980048500c2c0b50b9161f900000c080c24048880564404040e4010b41000300b04580315500124503078603a44922141944107c003030541c201d46002c00d0000030400e03040c00c000300d443c03144a19001142425083d04456005200721a41c51140700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 832923669 1250 832922419 832922423
    0x607030c170406090609080d0f11011b1202162a06030b0a0b18040e0705060c0d110d0c02040b0f1c03080106111e01020c0712060b1e0f040605030a 64
    0x1008a020f2100c203a002c00c0181c000e080c01c0c86c110a100781041c0d02c0a440303c00010030f10082c8a84500f070201550700600c0140411140780c4001c00550154080c140701310b040c004000d90010302c5803c1c0c03c1c0303110012842a1504290a03000c00e22545e1201d80ea003003022a034000300040b40c0b81c0307040706501d030104005c45140d01821032560081846490101031003508101c40d00300381540308060188101c214204010f055071480c040314042060380d00c0c46000760402140b904800e0b00441c000907e2a000c0700001107000e0000c0203581c8810700012103800c1c5c1500c3c2c410000c100000190140d00b4030000d480c154000540501c8010080500c8210f2800080c0038041d1010902c8a0b641e1503080308410f15070048003450041449041402c03120f04d00d07031902512128141c24a901c07224210f20480c0645100b58152200303480900c0c00c6030f980daa00e6030329042c10340c0038010b0226203907410301d054000c09003003107000280fa608580800703a40c01c014113020810340c950b03201a003d0308155950f400050580c0c0170032940d01524 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 832924919 1250 832923669 832923713
    0x30501090501050c07021e0613170d050c070b090a090f091a090d0507050106031a1501030b060301030222050a1509051e040302030c070609181a0607030c 67
    0x18145250081c20369000410342c0c0b410400900c101070140c2c998880860b0340600c0201c81f41c0044100800040280c06064100b03201e549225001084440e5904021140f141401044031440c040803e400c0360706118111a010b1103400180040014070f5420002d400405002030100c217403182c8410f181002c0301ca00284265186481d02c00000910440002148100d010000589864030300b0441044d903688113545900101316000035103100b80032085d4400750103190302541c080c0b46911030032601100100e0039a030b45117815404a81034040d5601034410480c1c02400a00a182107030318540030000d0188043d034040ba030602c9840e1034484515490300c0344038481c148a10b0005400000c0010300038900b410f03900104106441d001c14003103030b4041c07241e0070140c1c500c0341a1642c2141c0d0716232400700e00f14090100030b14214400c10901080d0789800510110503100c01d0500030200c152800396400580d281c0c40103100b0207603928103413911981010002040414064140303c50101101d90711254a05c1484200d40100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 832926169 1250 832924919 832924931
    0x60f21091a15150909070f0809030309060f0c1b1b030f100e16030b010302040c0203180114070816121e03050424050a0605010f17070315030501 63
    0x1190018450041c800801042440e502d048140c1038034150802054074070480b10101c80303020b015007040031501c1000b406800c108903804c2c542805448002a1079405003c41d140030300207800c0a500109403481100003030010521600e40000007112040054090b500210041180e0032900d900031a021002403030140003880d8040c100a2011500741c00e0ba07003110f100781c004c0740505260980005990311840140107001661920344042d40d03203001401d800c410368520320300500000784502c400000707040320300944040c060848000c1c000c030789030720070781c01c80c5030a0b60180c0f2010b4a07254800c0c0c0b000c9c0c0401c114401c1c210301d8800e00392200c03017064000f4444191201e41c0001e40000f08148101a0144258141408034001130840f0200714401d01740011101019911400030f401d0040e205140003800c0d4003450380c0725484925184400c003902003114138880460400c3d9002540e075101d2100c0c1c0c0c01c1c0001a946005080ca075209503001c0380d42c4003400501c1010b44996980c11005240b1281500940c031130000000c01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 832927419 1250 832926169 832926173
    0x203040b0109060504141b040e0403080a05150d1407090f1a04090206042106020409050402030106080c10080a0e030c07030308070507081c1d010218060a0504060f2109 73
    0x40e0f400d40c2d005640154104000b003048682c802111680044e450b451404c070ba8034100300540c140d4010b61340111100c001e15006d00c02490b8100d51000e004448800040c032041ea101c200002c0521004a00c1941080d01c0661000108000056416507501c0010584019654405072442514442c9015142107995407101c0f4017040c003070070740f03c100c01e40080e642402800107517000102c0e14000da10800c442d500388c0322060302c5480c01210442241a501034800c42d19503031554440c1004140c2184c040740a9803030490049541c40000400d9140404010701c0c1003550b90901208807280280602520711407503d581d01c00e1907030071b0f061019190401111000348500d61a5007002020803501409800502600700202c1000c81d034104111903982c1000703c1101e06081d00c000d2100c00500e40710402003031641412495001070801900104480f0100c10744a0f8444000c01c0f082211601c80c010100e00030803020007040210b9409214905070500f09414118461a00c01c54414080140f10500075010360340d0b4540c03041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 832928669 1250 832927419 832927421
    0x30c020c0a0f05090403030209040903171f0b090d0f030203090a1d06012d03020910030501080a1b0b0c0319020c0102070e09031b1615090510120203040b0109 69
    0x18005030126241e40c2020b2902044021400c0180959805102068005418103009030105e50b1b00400c090400c001d60074141c200280200610384050614800b00310128820120f1184280500d0700000d81c903414103032920020341415440404119001409031030844046040652890212030207500510f980d07460352401c01c050a0b9254020600c03a40f000040ea411103130180c41102d030300210070b00740745007050745040d902c02c10a02c50307002412066016036491048181d0540280800c04c60070361300011000c0e0003001c1a8180c62007400307444c001d5441a542c00021441000c1d00c9014801d210000c5444203854070650941c0390b100014007191980005052a40022040c2510080340000e01c0940b4502c20f2084c0000c1d2104c174030307100d44118032000202050301c1034070510489030001d00040b06c0e080d40300e46034042c00791034114500c100b100d19030f07000c0c4d40001c10f4020358030b8a0f491103156540d8075501a05001c204020741150901030401c000c7c096003ca81051024401140518011f0000c440b0340d40c03400c04c8803c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 832929919 1250 832928669 832928683
    0x501050a06030201030e070e013303060311010203040810150503030c06062403040f030207180e0705041107150b090906090f160308031b0f030901060e012301021c030c02 74
    0x214150340041020009234039020302d090305640750b05201c0e404100001404d40d5442d225403205008404207442c1820000d605517003c001280e10401c0c048006d49841401681c0381c0c007891080c1c031000c0d04442058034001a46621914500076140904401203440744040b82c510f0b009144019465448101400700718944488031a8a0746100d0704074030a6a4281000c00c800c600025000500090800c1204404c2500030301003000984407005c56964030a800006020250011281c240f100e0300840d4070119140c10300303006502c3d002908246a81c030300291683c0d1810b00a00100c24100115a82d00c0c404a6903942d0354122402500071400501690418950903030408801d680401c041d9480303e0201020300d0303180f0554070100c035004107000b40c0b0b980d100b414501d6600f00041c0030356404800050008951140c0e440510b001d449840e0003000301548403024035070740c0382c400e001308140040036503074000c81e681d503950104a410b001881a941d09658818103c1c007805210719040012a407a440100f200e968108504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 832931169 1250 832929919 832929941
    0x4151e1d0f06030706050a03020d141302041d07120c0302090103060f05091c18120b180f031e091201020d11030402060912120a0203030601120c020c1c0501050a0603020103 75
    0x130300300040c9042d1014080303100743c140d14014503401003010702e008103580e4401007881c560540700b04076502c0c00005822207148900c0007203104903c1e05801c1200103101d14640790069090308020004c8608101c40030b25107900e0224116038000d0b12100110050b200e041c0c055008500c035074004034034043c4c02d1a14a0580340018410052a8800b0100310502124100c03030384030300b0006003854440b0100341c8641e110411425002803600220503442d031401c0150341c5c1541031041d80210100010340401401d15a21031084000956503a4418486550100c0e2a860211003031100c40000c9464401e82c0004900c0300e41c9203a41d0241d01d0b07540401c0440c901070140c02814006015002ca4510b14541580024094002e401c1d8980c000c08004d45103501e640c100704100d80380d2618a0700360980741c03d40101e000b03540768402c07540c150006202c040d09102c100703828050100d903039105802a20702c641500d000d000d509608800400c2c2c0014120714100003091080c4602809031101c40c801080103401d500015058034041412 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 832932419 1250 832931169 832931173
    0xf05070b0a0e010203070f060b0612011701060f080a06050a181a0115231b0708070605040b030f060109051003020d0b01080105210c09070c050c04151e1d0f0603 70
    0x1b0a0000f02d100c4601c4d55010f40c0f00c000018090350f90000f060b018042d000300348007440d50312000854000c51450a0407101090b1138000d12250703440e0360620317925524074070500c0b05d10b0b8808481000054000d0f044180c3c010609900043c201c2081410901040c00004040d948803010140c270301890140143c0080c05401540d5040c850340b2030b2150005d1501c07032002c0034170b02e11042c0a090030405403000d00c2242d0a004071100f187c1c4400076503041440c0c6806851150102600c10a4000100540144242d0381200d9400300e40500b5a0740380c0842c480c280100900c2c560400000050104190381c4402d0402c01071102c5540c0180c8540e22079480e40112000c00303a045060004a00040001d80d0704c0c80d0704079031b601903140b102c0400c070503110b20303c40d141102c031156050f4007209402c1001242544030122550644c00740701210118213500d0144001c0300d1021005901035080c440082c001340d1503214455003407401c7d200743c20602d03990b10080c2d041801c0e26090000f055003100024042c0440000b03a255802c4401100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 832933669 1250 832932419 832932427
    0x21503060f04020706200d0b1807030b01090503030a020a060b040902030c010f1202270114220513060e0a0b1807170114120a0b040f0f05070b0a0e010203 67
    0x5070001d040e8111003482950005242c5003040070b00d8005c441450850b0040340d0030781c2e066910401040e008a501c805100c1d141540da203a65241c0301482405181444845100ca5128a1011005070003580141410301c22180c0d0000740d80d1300c040008050004107903010380050341c8949010340555118021440c403440c100640203000d0386c2c000c1440011140c09080c5041c1803d000041641c0110031036103031114480c4041048a000c00700c1c4c46201460f60686c0e00070303e0a100019005450003840c00d401c003800c205007030000e506800c0950781e414602d4040712103090441030fa600005a00ca692421100c0c44481e107a810404c00d03503a501c0358107034100c0c0940b03400b400b402c038548010461009552550349210181d070f0300420102400740b0484a00c03820a49004803e0b0740c1c40c1c0c4c0c4c454401401d40b0989038040c0e0310240c2405400d12000c0f420580444c1d00000951094590340c03a8008110802e0360203840d0405040c1d910700008004000c1c0000a00600000030340b01c0d040c0c40303000341800340780320366490554000304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 832934919 1250 832933669 832933681
    0x2a030b10021b190902070317070314011a0d0905030408011d030d0b060409140f0709030b0f04020301110703170f01081911060c07050a0b04060512090a02040c050304021503 75
    0x5030320b010303508400c0d142c421080c03243e03c000307211260190780180400f51000030040300785030340120403940c40a51500000c01d80d89401c00220212404d07620880c4059849000501008541c1440840801788003440b8504221681b6681000c5030061402201c040d1b000040800040703a003801102e100304442d90841c0e00c08560800003985911a030010706c1c09141e42c41c014942c40d50744060a40b0044c000100c801c101c0311031007110034800e0300001d03510802c4040d01e04002419451146108e0343c00c1c2c0303920503e041002d8691100d04803152102030303c00c130381c15501d894605020001c40f030040c0c400305002c1d070759100100c80b0f140401440c155000c0c0180314404d06110060003042c0300050f00c804408050b001d000c000c1130b0942401c04c2d560b41100c4406030302030400144403122120000d906004c1d650304440040d01141c0d6102050700a22807807040f070340804d030180480001d5450900c81ca80d40240c4840546003240700c9c07540020111101d0048440105001105001c207509144103038111640c641c40c0c0c1c0394074609082c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 832936169 1250 832934919 832934953
    0xf020102042612090d0b0403020a1a070e040b0f0d0c0e090303070305071b0b090c030d0504060e03010c09030b0c0c0a03032a020615060c01060e0106180609092a030b1002 74
    0x42e204c041c0c1586c044401140405100704828600c4640200c0ac3c025142c5420580b442c0d078001c1038400c800044c140543c21400b40c070f0144104102c40b40c0003009490f02c861004140316211510b544140c549404a61000441c0d141d0741d005a449461a5409580c0d280361019019007110350181001c0c003000144540c061403401d1100c4101c82054006548030100c0e95201c2a10746400b60251456805004e480c4448204a41100c05000be40d22036031103d8041009000c00c0c1402c80702e8244803400050944e41007000440c403250f404c01c3d04030007c0c4d80c8551a061105105038542141400c0407070000342d0350003141540341403130a8450910403d01c00d110720789400700c6c50029901e490107002d61108611030070b00e03001301d41c0d508400c940240c09003400038007000359911040700900c1c0342481b0b81401f0540b100c840300e82c506041468401560340030744417080030b2400c21100c4001000e42031914039507025280c0319090075844032844071760814800c2c1d40201d002140f0405012600383c01c010600300303540c05802c10343c08213010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 832937419 1250 832936169 832936189
    0xc0a05150c040e2d0114090f0406020309030706090f030801170c1507020a170f0703120e060706020c060612070812030a061a0d060e06060a0f02010204261209 69
    0x8031140550307448942e191030105104e60074000300215015184c0e0307031a05900d140076040700c03080d468400d440040b0301e05014a450049031034a668140044c000340014403154055030300804003002701d9041c019181d6840c0f01b26210168107071441402e031b4595004040d4000c1314180075210000d1820224201d4a4400f55100d1460104502c110b456a0314803203600c0c4201d00361250140c0007048500d40301d0b559a624045812021012942c038051100d40d4103e00400007440c4007101d502c5044410440e101c040210b032074080350018103510400400c01d0b400442d04c18006001d4010000f4041e2490b030820100304050f0045e820292a22074012200400c49204007040c1c02c0140403503526407036940d03a40d19141d01c1c000d20080d0025400c519010914410026401015049822103118100005a202c40c8100901802164602d501503c1003143c0e080c80ca210700c0c2c001002100ea40000360405840c1c42100c1d41d6450b2542c5010390700c1d6180c128078401020204840c030003031a200040340f0710300100c07a0003152481003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 832938669 1250 832937419 832937429
    0x50c030901030f020f040e100501020a0312110d050c0c060a1b1d03030703080411012a261c14131e0f021e0f15040b0c0a05150c04 57
    0x2642c0c0103030800f090115012148000400401e060f0744a07101d00402080010550341c20480b403081980214440d4000540d0200e401d40680300c582502030055450070240165908150901c80c0c03e001c100205104c40c0140d50003441d0003442c460700c0f000402c840710714091000b00b90702c00c52410300c9002c03400b2503140c03070b10140006014074080743c2ea0201244645c010b00c81c02c55130280c151000045800505070300000c0c060045120f8a21500c07413500c4100110343c1c952400d0040c0f0f550000a1401175041c40681e00d0b8105040d01c03074245407144a2108044050310b04c80420041c10324540069105441c1c00c0800908144403410380c4100120200c6603032000f02c9000040901d40c040502040346002d000d242084101c10300a051910740c1100b60341c1c075020740d1201c0070342012406000340c10382042c03088806400705031071030781c0280103c014101610100030401c554600c0a5600b500200004104504414002e01046e041c0d80001d00004d4000c0c5801403812016010605000e5046402d0101d6200880101c0d01290 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 832939919 1250 832938669 832938671
    0x303192a03020a0912050a0b13050c060903010e010603060b030c240306030f060403121a032e0615021515150c0312040b011203020a0204020310080f0708010c050c03090103 75
    0x1545081c0a03644a580d5411646040a03960301c2c2008008000944020880c23040022106039140c218007103a2084101c0001001a0460301d59000142810030203040700f2400100042030000340c20181c0f03801c41c0c030710750016505c0c0703511041003070424101081003501c0a5003d55280c0003120301e41043d10780314054a1020914000f001001c80d903580c2e02000b171221035214600a84032941018a0040d1000d0110201d074030b900d90401103480c0c801013009e50001c0e68080c000d0007400180c46602c44e0441e01c0b079184035030460441200d01814500200a1155a0103401c00c81e0466000a01a903c06480c00d54040000d502041c030190030002c8001065503243d4280c98180c1c2d000b15440410000c04080d8002ca45903c2e03042d200110302100fa2070998035025004501a000c5001d507a600e40e0040d482d8a010144003401603072052907844014241540259030003940306426083d42d80d25024010309103100c6003400181c44e8498001446850700a105480a031035460400a1070a250426590b49074003413515854141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 832941169 1250 832939919 832939927
    0x201021c020a17040308120604061a1204081905030402030f030306212803030b03070602072102090108150105030a030905040c090b0a05040f0902030c0306060313050303192a0302 78
    0x3c0030b000e015980596070140305d00780c4803a048041d0790001a000ca80300c51181c0d00b0501e0010b581c0860900d0780840c115418205483c0180001010110100103441100c0380c400400c4070b41c402e1040c86900d02203440440e51055620f041c10b00406144c109201c08030306060b04100180281070b50740c0d040c0840c45900e0b00850032080c0c0c4e2190384035410182e0741da105446c18111b90000c2040300d840c42c103075140403030b119440070004641c480303050564480080c01040d000d0317440040706101a0342c06046004010802000006403200340b0340c0819501102039004100f283e000340c50a400c21200d030703680c1c05e0161030305400500808055444c000d00c50300c202d20505010341d0b0b07036010985281d4482c5008402600c07114645030340e200c40004004150b64400c1c402c50085003070420300410000700c1402243e009181943c22031b411500c542040080a0384054410310000400c1c10350900020300900185225019590703484d1600c9100814800c10350306100f00080b941e0381c2081d001c2d48500c07544180e8208070742d0507240058032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 832942419 1250 832941169 832941203
    0x21201051f3b1003051b0903070b040303022d0714030115060f020d09150f050d050c04030c050d0203061807051f030c05071e06060308030906040201021c020a 69
    0x400c0031154164039219442c0a800204203248007203a078021406032a15200c1008142c0110101c2d01c081c0d8200402445001905021040391030280408942c000d068508807951104410460750181c1c2c0200c0158101c51540c51100d0240b00c4400780e044044d00300d00358010f400d01c0300203031250410701490044401100aa2005880952048090126141d0104100c5440c0c8102800049034101082c00521541c01007a070130910a80c81801140c0c4000061240083d1058003521136130038905080c030800c88140000c0c0041803e500030a80640480003900c0d40e02d038214207000e140074040d504864012414500e040780181ca0000380141d00208401410036400d24031003415041000f140d0020b82d0144510b0343e0342100148660001e5005542914104072105904c14141c0b0720f8061184040d18003a100c0b8000c2c201c0102d42c0c250101403902c03a840000741d06403070707982d044261b420a0ba1f0b4540350742d0115081100b196010408010007148820941503c0b940c4113100a5881c843e82c0ca00034103c2050300940e00c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 832943669 1250 832942419 832942457
    0xe0304180c050705030d0b0405090d0c0f02030f060f010f09050903183f0d050f070507170307020901140f060d020d141b070b0106032d021201051f 64
    0x3d120341c0c040c042d255500b945004003000751408440044c0300718a03000c08601034850008a2412407d80c41c0c40f6820074401c55150790074100c1e90310005036010301404084041c140401d1003024400c3d60408948445541030010070345400712150040041145410b00b0b01c00f40e060b002055a809660002111456040540208000048d029801110f070080720300c408902d251340071805c5180250700c14448200c0c0104030300c2d040d03841040c045044042541000440b0184d12104018407074107014800b25401c60f07039610f02180c06407030311864aa02c99000456140114035100c69100c0c0100052100d01e03031380300702c50000502024010100306126090000e40c04202072440e0701a216146c802c0c0408002c081d8041641b020a03580440e640c05405040000030180070114605031613007150000d04a10450b806c007482036008001000c0c400b01c1c03c0300c48072030021402135595400000004201030150b243d035018800d80f4921401a0080c43c1304100625880910001401107170300c92001900e05070340e23400c2401030030700c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 832944919 1250 832943669 832943677
    0x12020f070807063006121401090f0b1005190312090506030703091e081b06090309040203070e0a0b19020c0d02010e0d15090b0105062106031905060601030e0304180c05 73
    0x500602e0074440c001590004180707003460007c2c021414100000050346880342250f4460b54020403011030b440316100801d69410510f540a154002c445954940f50030000c0d00194500618001c0c070502032030300340200b088402207050303c400c1c903080411900c0c4c10720b400100140002481c1008140d5a41d981c8000c0c00028600e004820b070605050040000345070a1403152680b1804204110500004203c0091070000550754801d400c0e003009503007000c407441d007040041d5001402c0d1300d0801c2078400d200c0751180d1703460108400034810801074556442d82565078520203813607001c02500f95000b5100c0069141c468645810100741d09280c0b0640380b8401c040010801e54202801920515440394130407110303d03c99000114141c085d5004400680c1d03903104116151003840844190010021283c0307200c26a40c0c01229040f4100805a034400e503813842208489400104003a19030ba44420144003485d60103100740c072148500710000d1441c0c2410540c600c4d40a9071151665980160784110520030103215501b55 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 832946169 1250 832944919 832945007
    0x160b0603070b04080a030e030708030901030207020d02091825030f0812090c040b040902010c060e0708030c0c0a0f03021f030906290a050d0201050d0912020f07080706 73
    0x10b651103a0301e680949995a550300d00840c003003040048101c005140000e091803c03107098070b00a5140012980044000e0b4105983c12030b00002c10036000c800607501c1c200b43c54450424004603042d040c0c041950540303004625184622140c28940c0c0107427208501d10282c07015a60002c2001c0c041d58054030306005c00340b1550105441038610a030510100307402c003007520b0481140840c1c0034020f2168803000c0004403007800000901140501e40403000054103900002040e0303540b6815111074603038901003241503500c039003150582c0b42c22400881100d4648400d191020b8800380081414003419a80070030b040010194002100104580b50140285d101f41c02003002243c4c041d0061044603030384209408601d4000041c0354016070705a10100407400c04800000407100010102e200c01c0000741c0040d983c60b80008000030304282c95103100008500c0003108501c070300c801d55004002e2907084196141c14048076400801040d0003041080101d1603011045040d0410000010005459482c0f6083c41c0c0640c46014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 832947419 1250 832946169 832946189
    0x501150903020f240c0601080102030606160f02221401120f050115060903050105072c0a0e0f041709130b03160305010507180807120807050f0c010311160b060307 71
    0x841c02040c00040d01811201713030508104c50582e41c9410844e4240d0000700c400341e812140600c00201e401d94030720001030300d4500840b80c00c009500c0d680c020a614480c81c1d40f542c40c00c2140e00000020004092007460903440701800350103015414508203c081c51071101b401f802c0403c500c002001809020340c0705696030681d4120440e03620340d0313130b4101a00490301840180d80715403a1000190106014848031840300c0e56102124a0070801010400c680140301d524007504400074103c0812042c0207031f511a40140c14124403e0100d16261515514948880900c7c511028007400b80300082e850f0310460254141ca645404107150b00c2d41004245800141a00c4500d042c640380e00002c05d110b8198410350040d6030513036276a11800ba550040080d181994807d246031680280000c0150b4003503411000e41e010302c25890680340c00d0150b1940761800c484459108400c3c0c03c00c45070340301c1540e01403050303c440b03c0c400d01a4600703048034801c5035400c05000c0140640310300c0e80380b400240c680e60180700d0311010307000e0469 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 832948669 1250 832947419 832947469
    0xf0303041104050a0c02070e0910050a270f02060912031801031b0207151b0c060206010e09030a08040303020f130f0801020f03011202030a060e030d0501150903020f 72
    0x1032007200a588140c0c154000d40ca40310220f6110792103401020400c4407181c000704404d5117004e240303a0b400100186200e5031406a00c04040c00e50140c1d014581c0a070280c800045400031441040701c03a04001001800301852016030314070001344000303c0014079542c0440701d05443c1c0e101e94000c182d0138132900c030404440b03000010310391181240318921214220408ea07020050a045c88140d0720202480c800d55501603031008000300089140c2d024501c40880306454002d007421410030490442a00e8408200c03081d07601000d0501200740e040003114010324041c001c030040e50a15060040d1a441201050010020a840054181406901241e030902212160329582c1d00c03040b503a600e9061250300402400318180280060360f10014000d8880c8605402c1d4002d103164640b414821000071a40c0d000c982602030700e1429004600d5038452056a90310050196079150914110301c070481d10140c0104410741c0760b04903104820380e408540c4509030703941910030441c0300482000080c00500302200c00008005444 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 832949919 1250 832948669 832948673
    0x219020f04062603040612050a15060503150603010b04050103231e09030702100c05250509070201140a0c180308070b0f04030e0f0120010209130203060607080c0f030304 74
    0x4241543c3d0300406580041d0100d5841d400d985a00c10707442450f000503902a03003454881c0303961b4040c41d001644600009000c408406d03840300c2c12040d40e4450f4001c80d07804010050001e8010301842c000704400c0721210f1956040607000803042c0541d01a140c1010303540d801d08040303031286400e650105454a00342c5119454450b262007914000a80c1d2300048001d01300104101360ba002003500c0e49103a0007416252030f144441002c8a101c4440c2e9010b48483c8036241e0f0340d1441c04800c410541c5081c40701d0b900700a02038101000e0100d00c0d4000744c48130046a14105200103100c40d10000350b0f401400100f0081003110a040b02101c0b4810a40d580701e194030000e00000040004082c002c1c1080b502c241e05041281c0e40340d90102c42e81038001c40300038000c0385004940d01e084d45896004d03102100014101510500007e5407040382c0c01c540e40e561700e64560750010f10700d4040d01d0076081840315003800000035480d5141c50004140f8502840720000c100c50f10104d40c64040c580d050000c2600c0e002c110701102d480b86028 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 832951169 1250 832949919 832949939
    0x30c11060c0c0f03030103020609100917060403030614030a0303111b0309240703050f12090a0309080a081603050c0604030c03030b0d030e21070b070506160219020f0406 74
    0x24404400b40d84030320804450070910200075641201d07001000d040c284035480092014032541d001201c0c082064050001c44c6810181c41c030252030380c84200044c0342d40d14003840d0281c05c54009400c50000f0301c028640981c525940091074401c810380c9454003180c075421501203444540034860009501ea40503000da46000c080000c0074205070401114920740e420801030101c441c2e010210085451042c0c10041d07035021902820041c00d840020ba001075241500b88446141c014609540e0403842c0d411a11142041c540e1007103500f8090403151000d4141c0c190700e40ea40e20414410868070001740444880402c0502d0301540645001e2a0444291540d40c0f0301440d0041c07c4101c03a41e4110003091410507400c0f001d083c5010005003155041d100d4002c105865410080350212a14080c811110f07000741400c1e000805201d110700800940e1240380d22400689003442c01c1c880004d0844006d4019030540c1c008185d400101142201c0440c2c080c03440d030000e54004140341380c070b2101d1582c1c0c111f428040d0008200e43c80c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 832952419 1250 832951169 832951177
    0xe240a06170609040c0605221403010e0c0a0e09070510050c01050a090f0f17270415050d1401110324010f110a02030a061512020d03030c11060c 63
    0x4200c40c401c0c00303039078520400c082084140d501038400d0b22509014083c46003d58018180814150103249010441d220801220416604020b890b038040344040151418240038078140341c0ea0400103000d030b00d88948081150041320b8406c07512120703c3d44010440381101400b50b10090180a0010068201d80800240040d408107806100e558070f8200054200c02e0300e8401d2000c01079000c405155690445d0725a030204002254081e1034803060348211a106c0001c3c100100b59081e49806094505c0208001c075810300040700e00c00600540c200000d00e0500a460340301001502e8045034070b51413190103070038000c02e500304120184210390b02e40ba90984040040102840c4a82015004e10b515401c030141448100d60180d03071442d020849805802c1c031302c00c2c0101d108110701491074080f1f45d0441141c1d00001e140c4085000191160390b0b8628030000700001e030030414400380c83c0a1540010903442940428130b1004ea2001c00780405681c1c4100340c600038030070300722031650010070421140c5505003c0400052684 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 832953669 1250 832952419 832952447
    0x1c02120a110a0b0412080f09030d1227080a02031c15090905060c0a020a150605280308071109040311010e01111c15030c140a0e240a06 59
    0xb5800002810382c007803038100e5007510406081001d14205954a030301d6107030440c80e0111030200307040c400c460b07094808100300c00c10606241d4804060300b0100c03c0d000b0884081e115480480000d1501000340411b18880301c0d0549603011007440d54078200284c00324214001c4030b10034501181100440200d0f001c070381d0003900814240609548000b82e0300d0408008484107240014000e800990000d0400c00318000940388240560058604520301071740c0740115152190b842c1e5045590f5404180403505001000c2c000710076805040400220326845410141c481c5440001e01c092000a07124040102080114a051901404805990a291030050140c04401c050400550301c2c18003402e40d070807014054450002007004c1090718010380203440b44030800482c0b642280d0703c0d841b99840c05090381c1444244000b14001d2041152140c00c00e00312516002503008018480c95441105101c000c03403483ca40354200501c15454101d0145052031010000c034442005039000380f8500300041c509400c103070031010b081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 832954919 1250 832953669 832953679
    0x7110904050d1e020a110a09061e0b070506150105120406020c1b1e0a0807061808151306060e07020109051009050a02130b0301050c04050f01020c1c02120a11 69
    0x2160f211400b000380705280e030320005034400c0d003215010410384a22584508000380c409900d0944500022041d150755038001e407900e11040840d10f50340c505c8518070002810302d014840c1d16050490311207d540f550041e00b0b07a82c89403104e840080f00c2c0c0c0e0003441190b448085050300381c151450a0700301035009400550b0000d80600501030021041c1c010030000d22940340d4000c012585101c6174803615001c41e40b0000300709800c903110310000f1030800d10800074100185010b580f51400c0d41c6070388624103003e40c100e50000e89030354400515103075039036844040e03242e00008840c05c04461030050b051003406404d42e40d1040f5441e01c81d1006018426a06401140c001e40c0901d08903080b80d4940100c00f8111041c6000192241e04941109001458000b10703502040001c100b000c5501100c40000030308562040d234207554900700c0001c007040a408c1c6007a201c0c0c0d1a074004d00141c8034080c000008260f40150480e00d0f02c001041000c0344908540e20881800d14140361030f000c44d00e4600580c6001100c1d52000f2130454850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 832956169 1250 832954919 832954937
    0x50a03030e15010807060c06140406060f0b030f0a020d1404081312081b070f08100e01050f2a0f040f0b04080d0507031e0c060b03010606021207110904050d 68
    0xb004038101e464100051416601e030413000c0700c4520600500f200d0640c0c4503101d8540c60034a03420742a005a006560005445250440142034a00c20b0740c02030040620900030041d0701412654481c1d4082c0f24941c0143e03890b8800c03152140180300100c40103001d0448281400b060040950140844101c00d0a2a50019032a4210122560058400104080c90400c5469201c0c0c0e000c48041c1032002d448030488070300b03944070a5400003a2855800c40d6100740d22400107441c0622050041c074800e0560080204030314208040300403101c810060102c0a000e41d410b05282018024074540d81c03000c1c04403444561998045010328a03154014400c0e5601c030582008042a0850540304031800c50707085100a286250030f00406890b40c0c3c101840aa09020080c41490360480040806003205030903552103d10b201c0349443c00e00220b0300c02c1c586503802a85030110a02042c2e8001031420400340c0440321b025151034061400c0360503804840e480541000c205000d000030800d0029885854420b10f4440000c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 832957419 1250 832956169 832956193
    0x50a060902040b09150f03010b0c01050601110a02010e150f030105030f010c0f0c0602040f08030304050f120901110f0106030507170a021503250f03110405030a140a050a03030e 77
    0x6074003960041c2501c04000700400e1080b441c1c00303440c56541c0c00c175129a171420000303895070300d1b011600240d20805410b017001544000b00d1400f1f101708c83e13005c00b00b400c0203114422810780c407507a20045454006e042c45042d1202e1201941e4031402004021403641c2070903540c024000d180f002a800a205607400b91040da200d0602084041c000c2d2080385041381e50700406400f020030100e54100c805d41050b16095800c000c0420030b00c03405040c60b000342840300300a50f03890901d071401c2850103181c100180030903000a94a2040005031104442c90302000b480c0008621440b1000c8509202c20703105070340025840e10000008014010861002f19140f4a00c0c680480d5074008030031b5203403030405200a41c07001041b20010900b03101c800145810405022039002d151184010180309200d0800901d00460114034140020590502402d140110310042050825240c840800d54480303031315100070080c542c08110707889444010410b034440e043e00300c1d04550681c50305042c042c0042c440910042c50310b0107040c40c01c0714 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 832958669 1250 832957419 832957421
    0x5012c010507050306010804030e0303030114011e140906121f0602010b2b060525030b0f01050c0a050601060504031401150303140f13050405010e04050303040b0424050a0609 76
    0x48900340315143c25245030b0310b0100454001c00d00520803020301c04450b0361035100d618100007841c06018940340e0540501502d0002401c44007d26501c2099003140040420101da03002000103141c0020031a0380da00c942c0307094000741160050802501562103a681004803140003580d02883e0548001e030b000780c4154840c4000ca0984420090300c5400111454071404084280003050046489104074410fa4400a503114000e135401621719014001c51320408180480303440b650300b003da209509082000310b1681e004903001c402d40c00079540c10b200d008240000e00c8101031085110240e80401a10138941c0c4603800549a600b20380002d80e00740103094003800404005104160300514401180102c5500c0c41c0d03401c44203148401944030ba00300d02031200074591038018014010031014205100322890508080c00100c540c164002c003500d4031005c05100c04160040222600240c10030481c00c1c6503a80d9081806002003011802c20308800410000c2c164000c0c558422400340003400b03818400740c0d82d16a5000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 832959919 1250 832958669 832958671
    0xd050606130303080a06091406030d0f020a020d0602090d031205010f0e0f0712020a030f0c030501030308040803090a1a06040e0f3c07060e1905061605012c0105 70
    0x1110181000d0420710201e40100d160545c4500c10031808a041521100148161140c00509044080e030010601a45180521025682c24600d00c0d000d828011080c10080d540c4540b5640a40229180c0c040c94050001d07a40448030046405407075072180181314600103203000c0802d040d890b080d610702800428070b2140021081c007161001403a100c00c0781c032610b11030030342c455003e007200cbc040c031201e28501c50000f130117030010b0183d92210740c5000070444040e026110a0300d00d0030000f00c0400d0703c0d05e070050002076005117015800c0b54000c4032094480d95011502c0d40b406001c40406000030301d9000c031f2301e0b280707000b15010729115110a48040c003102c0b000e008015900d1044281da00e0305a040b191003049181016100741880800491988820001902065881e442100d40208127034221000500215800801c8446184800e039001e08104140d0342c102c14034507081e0f0150324481c030400660090645c01d4003104010281d0010003c01010900a03c03040000d400841180405d06542d2000480c0c158180309003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 832961169 1250 832959919 832959937
    0x90303030522060c0306030b13050f010509030403030f170a0e0c0f010f05210f0108190804050d0809120d090803070f0209070c0c0b03150f0d020103020d09170d050606 73
    0x20161401d4594502d00a030542c00c16003c201031b5074071400400b00340d1444406005661001380c60f203c902007803c040e070900030102c0c0b1400c8160304010901c00c03003401c000308035001c0b81e4140c40c103003107199203500d000ca5030405001d00031585480f070315051002c0092075621900b8040c070100101c540b1801068180f01000b86a10083c0c1c2c045240004400e40c998001c000503c98a0040c1c941c6442c07030904440000c03101c90b000e07030b04c44240c07150200051104410800c11101e101114848440c400c0881d0390b01e40907103103d9030064500405020030721a0810110406803004030358010150369012080c1d012955946e07003035171030800001e5402d0310001444071010040b104460381148601101c0001030b02800160070002d41000d08224481c100c140104012004503000b03030440303492040d42c1e802c000b103109800052103e03030b80e03120303407400e10001050707648407603256154950a08001d41c942422081d504010660060068180c82e42c942c4560400c3c1c81d8030000b4000a01100e008200c181c0790300c410b00109010728048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 832962419 1250 832961169 832961221
    0x50c12090a09150501050c0102090d0809010206100b071b0b0309010c14160609020d05061003060506060a021b03010219030b0901060c0b0103031b0c0311132306120d0903030305 77
    0x10134002544100014248170000310000740c0f9010005001c07421040c911101940c0c00500400c280910750384c1032190300d030085840340f200f81c03400342010780c2c182e49803141c1000105001441d0141c480d00a02c9808000010440c8169443d140d14103400340361301805280d800400001c5907400150b1500b03100c48141d462040301903886650081c2690ba07204000d2040c41c0301640c0c030007407100340940000c1d02004018030030700700c000080e1840b501e10301d000700544d000501814401c0001b070203001c030b40710790004031340c2802d4804000350054000c490700441d0081c0702d4028009680d1405c4903c1d04175030754254128102064040c0c8d14804140c2e6954001c49100c843d403480186003486070340041001c68404c004880500d20300c1480b02c4031450859403981805542980b08684e0f100c1700304003002081c50721500c40d01401601e19018041ea080b442514040c003000c0790358001c40b041c00840440d03a261510b22910200740c21400071101d41c0203418002500078030813448101c00207801c00c4001130514800314107040d040031181031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 832963669 1250 832962419 832962461
    0x2316020d020a03020a0f0806160f050a1403011d01050406150f0e0405010e041505090d0c0c08030703031506030b2b17090102010c180b0a050c12090a09 66
    0x42049080d5224100c2668495070071200400540c0e19007610300028041918480b40240c0391048443c10321500911210902010312052040f00c0d42051f008441c100891034110b0f501e28102c1c60a80e03d80455185d400718408020002088541128040501294038480072007030aa036550100000d590143c040e5070b40000d160360121302e0312400b03203996190106c1c160030201254990840403d0898800341e00000d1001022400c1c8400e002a110052880680306d020601c00c1c1d18100310b00c00c0d6541700d4005c0c00782c01c100d181c407440701c180009030356100302030213586c02600e075034111600700140541002580038102d06c8a049002a5040c0648541d20701c0000c040c00711001002c06030007405180c40c0045107403610b2851550300200003000201550300c21098900c40507210170820000a0071030758403040030002d1180d8084626651503070010f02d402201e40e0034849a50710080104100c50300c2c099451a00120710694044410b040d0382c86001d000c49080949000c8030b09682c40703c0c020185c0c3d66014100d024040313080307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 832964919 1250 832963669 832963673
    0x102181f0c08121f05010c02010903110d0f0b040b0c0418110c01090501050a0606051e030601021603060e1c05030a09050f0a030e13050f0f252316 64
    0x1c51154402802a0029401c081c400c08003580b40d00011640c004503090050814010f1101404041c4040e14084c600503200350070a50003c2c100360039a00014003426107120100c244e568864070480c0c095940001d4046044059240030b042c04002560107e170051440c00000b0700c0900e01070b040d00c04807036a106400344500c80f08100e80009012460344952444003c105c9240740f90024045c1c4100f0520130000003c084c54940780b040216132468021341d04000e410012944612103540e405420b40e0f401c021515a45e03280c200050380341820070760342440700d034005c0030000041c80342d668040b20894000f40140da0710901100010700c08030b0007221421002c82c606102141c5003400d0350780078410041c85401180c1a15408010040c9804403081c0110000303044070220702094141800710b03200b1002181e20a000d0303410401150503921400418004540f48508002041e035a180101c074055040351003270515081c0d40980c0c0090142d03000c0001d07441c0c01e4440c80214109040050111020b0b69883e1545a201d21a03917 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 832966169 1250 832964919 832964927
    0x16240305040f061503020d050303100605031e13060650030a020a091a030102070f020105070c0f0608010e06010e1f020703050609010504150501080c0925020102181f 72
    0x4c640e18101c000a0460100060300c2e449061f601c10390240300115140d14000741000c90228003600080c04110050040c0884c105004d4440c0c180b0301c0281c90001480d40da0091480704651020784e0103004d60b418410700180030700c3d800e25001442c20003505620600c02c01c0b006d0042c40302c8480c814180003202d44801030161400c2c20940084d05010050a5814041d134940004880d440282c0020489030754902d2034004607164507003c444807640a500960a1482d00e0f111400380a0550f80c0281c14803100103508070404c20010f050f900a004100384091803181c4803207000f4040c8809016500c502d81344980032904c2580035691000111000501e20b1060041070031580001d2544480f00000354440c801011001807004d02020344928452400002c0918060621400d001104001000c1032031400c0e0050007484030204800704070034020744d01003800e5140c5045141032041c0110100120151042c0700039450b41d4190018a02c2d04203068030342c0030b10304504041010b40c180303525a041c0c0c0c084409824045441c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 832967419 1250 832966169 832966181
    0x1d0c0702060d0f1b020f032b090503071112072d03110f0117060f01050708070302010b0411040501051215091603060b0909060f0316240305040f06 64
    0x202800c1e240c207150881c0340c501c2c1034895000315908090b03190107a100060b0080104119150744a02c01412412184003030b064880c4114009410301c0106110b40706e614444c0e0702a40c090000b02460104050041c60800350340b030b900020300c104d900042000c1c42e000f142c03410760360480d0f88803d6100034112403460600d52480340010302c072054501032645070700c0410800d032a110a40c0154000c1100401a0145508000711212102c0c2c919061001c52a181f51085200c151302550140003550320f903900400c0c010060302c440c011100c0080141074005200c0f41010f5064010081d07001d42900c0c1803118022141d40050180103501605000a03000c2c02101840c2c8134240f900354011480b115100f03095040c0384040341d15003404548402210000341d0101a100340e140c42090000c180ca840c2690603c1003c10000720112400f500d5548220b80c0381c02c0060760340d5814407c1c10340c4268182c40302c15910341c2d60341095400300b102141c0a141d00303004112844100c1d020740950341c45a0fa004504131070341503a40c1e03125402414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 832968669 1250 832967419 832967423
    0x40b0d0c0e04181104022809030807050114090d0e04020d0e010212070e010203040f140307090c020a0611040608010501140d02160b06030a0201050318010b03030403110102071d0c07 79
    0x146031207260a41c0d250b900c1052080d09110425494011507401c10b00c5440a03559a03441c0154070410a2040d07080c4480300300d4078480c070321a02205814240207000c41d044a04c6030009402440c00091080800c40158000240103800220008a80c0e035007513501e60b1602141c95417500441e51411186c54145084d070300900055880403400250103400c81081802ca820004c800d08080b0005c0061000c16600309802c4241d100702440218903203410003444c2c400402c02c1d03114249158808454542c000d0743d00744030210240c02031807c200448203940c0c4000307503915035600b8162802840d0472060040003034a14219010740b8035503103603603807140d1800004481440c498100c1c18151282800750a661010a00007030850005a01c50021004482e04001c2103030a07001c0e0070a4480d072300144004005076088821399902c00d8285040300f6502c1c2c0e0f0019042e01424800c090303c3d903d0b02000602108003c84d49009809400c000c0e0708840780140c5481c40d54a50781c40300c082c4604103101160000c0d0f0b0000f502e60040100c14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 832969919 1250 832968669 832968677
    0x3030f0e0d06021615020708120c07020315070908070e07050307050c0610140906030c01050d060e0c040f0f300602030a0603050c0402040b091002011d070812040b0d0c 73
    0x6810381c0c88002c02c0341c0002118528803080c8040d100c060080d295140c440c210b00c038003000c61801d25a43d4881081d84583c000044c0307a00911390001c0d080c410500c0503507510b5900a01a0340701100524411080410100c6a040c04940201f8010900c080c0c0015640d083e030b400d010342d450064032100b1090300c80f5000101100c0402004204501c00090148011402a140384c548000c04600700340c04d240401c2c002400c1280a03081c038904010071540c001501200c0d1030001e0a245559501480e8000c0140540d500102c060070012014000310040b07080040040700d87c00d00d00c0403c19925600c801c0c241a40c07034402c000c01081d80349c44100c175183d0b810a0b42841c0194503060500e00c003405554010030303600100c0305850400d031794800801c2405028002d243c0819801c880451610b0300b4011129a58064104040c0c05903004282440d80c0750b000354032200205045c502104c3c0603071110542240e86140300d00900c1c2841c01401059000ea280e102c0955096071802c0c0000c6080c0017014142d0002002802100c5c8104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 832971169 1250 832969919 832969939
    0x20f0d11090a061d062d251505060312091813120504080709050a091e0309060c03050912012702030c180402100309021e0108070903030f0e 61
    0x80e525180c604000b80035944400c0a03289070340502040000c00d03c50380d02d00400c02009000b0030b0030f55200c0141107076500c1c510f5160415406450f000487c1c0102c000d05001c1201d203070300a07941d0480e144048404584901c2d071035002850702001400540c1c1040d00c1e45030f0075604c1051008080010b2070054003003140c000d0882c071040c244280d1031140242007607a841c03c40184011501c010b001c2803010010000005013002490180f80c001e50640d111054840c44813116581c501150904a05401c210321098201b600e805901c07107a444841d0560356081421008620034001c001840c5005080703c0f42d07110703096125981070115920a209540314818580c407241d55a41501512100040c1412800d9840348040840c01183c24410b061904100c91410f51050070301041001c0f602c000104040d41c0240d0541d000715190010304c0090300a821040c800035480001c4070009524039800d4890800c100c20b0036600c100340e80d1205801030382c0482c110301006e00028180968413480901412203000751407070141c00380d010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 832972419 1250 832971169 832971187
    0x180f020903070e040611030a1a030708191b0824010608010608060d05150a0c050909070c03020708190605280518120307020f031c0903030207081605010f020f0d11 71
    0x181da00c01c4a00248c0b4665030189090940d051020040070650140c0040886506080f045e075664a41c1803a107107002c041d4a1000c0041080c0c20a00007000801005031150326070300c54445549908030804140d0700450581c11080c640d0040006940c100d0f5420303201e0907e5a4244141241d0400001785455008000208071000080041005c450194000690f9001314100340991001741e81100b04460704000c0c044c004100e05954841e40241c002c0b6207400c4c148042c1c000b500d8140e01780b1015031b100301018000d88400d032002914207500800d00e14440d8004209940d640250083c40b481608800c40c003081306001d01c8040e11309180d1199400100303841c40413180b0803010440a01d0024015003580100d0070100c24003c10b80c0e0104401c02c02c1180240286050229803500102c2c10340889202c042e0144d2501b400800b030502035811074a04940080364240d6a4442c8400348007071501d1403004031003540c030f0000390741c2145440e07200740c2d01403807007031074215242c1915075140c6805803039000008200d0070700070003d07054 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 832973669 1250 832972419 832972451
    0x70804140d1202012a360b030703060506160b0a1d01090c080c130203270c031501270b030102130317040f031401060807180f020903070e0406 62
    0x201050598000321704026400744003401a4480d2403441010a01300c5507601e0282d8000e1440c0c103c99820701c41c0f10060219410401e002c58100b0348581e034140d884d000340411002d42c140011407042c80140c40501c1195a40c000b4007a0900c202e551301020b041c070305070b84600041c1c501c07400c07035410a85400001c81c200340000380003404410b6805c0700752226913489081004010721100d40320000d004a201402c04e0241c1600407400007181c8107040f103007e99001000420000c00044070080307440812800c16031403010340c01c205a45030300306021b151191003a8102004201a40c41d0018141e440d0145103850915502414140101e10944400001170321501060342c0703070710240701a007035502a01d5030003a115861428008494a015004155519401c000c1401309200b81c040c000d00302c80d0301c0b0040050581c58298014010030203a040000a40243c2c8000184180341c20181504101d004038201310b0707039a09200381c104a2044844040c1c0541008104008a1703000122640e03001e03000380804185481c0c482d50b004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 832974919 1250 832973669 832973693
    0x60f030b040b0316170a020a0b0d020d110301050117090c060f221a040e0606031314010c0201060609031505070216080114090115090b0307090f02090411070804140d 72
    0xf050021115200b00072903015117104d66116582003000e084d03034000b1500800e0881c4403a018088103440001588080303102540d04842121144c1c0c0030030040c0108692428483d0751080c4191800a00400501080190181c0b2202c0c01078082d04028a1003000c080b00344056a00041040c006428092250031201e80d1551140c0c409580710103c10398805041104032880a0020200e85210180a00050100b61070005002d500130f80c04551035912952083c0e1016401900703800014106d980e01380e00107a000c1015040300682c1074964000384103003a150f400407035000010b444090300b0000254917050307141e034080e0301183c0c000006105550304c0020b141411340c03400c1e5141c1e2042c0f00980d524408014103a07000d80c0c07001d030400e520380d000b4000060507040c2038002c84024010280c00542d504100b1405907410400c9400600e40c8210a00002000140c2c11000350805e02485000320b00301038555444505907003c4801132541311540500b000c0c101840214000e001030906070b0400c0c0b181d0b4007000071038460780101e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 832976169 1250 832974919 832974943
    0x3090105250206070305040f0515060f0103110306060705011119020d050f2710030501050a0e04120f0302040902040b0a020c09090d0804051c02070f080601060f030b040b03 75
    0x116550600803070054007001d10907550440a880010080000c50340880d866030000c80c40e10b004a905d840714182072101a00d00800100700d44202807541c407a4032181e001d8244514812140010400307035250040d4180d80e00c40100d005880c804000180043c40c1440c050000c0d40c2c041d030000103020b41d0380350a154603070344203440600d0841031010156105582c1040300392940c40c0b03e454440d0602c0c142d400c00d18800e000300b02441c41e180541740500980c400310b5002544030100020181e580340080900c000e00108028010940600c103546004110a68401c1030f0600440e4460030b20314850032000f1301121414061611001015000c100c006615071450001d0000b0b0040047d40341c0d9a200d9520020745002c1007a0101801000340500300b03e03422101040c2405104050308200c20103903583d1410f00d007000549419002240b084e100301e14002640090070900352005948120061611689810750f00c2400744161000030f55032071202a190340c07183d00030b0341540d030000e031020450880080000e81440007042d01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 832977419 1250 832976169 832976171
    0x509090102041509180614040e0f030a0329010e0d052103090d0c0c1a16051c020c0a061b06050f0a0c0905060a03020703090b030f07030506010512070e15030901 70
    0x144101c4485c1102d01d640801d030703080d04100080c07501c1c440b014500d440001e154400c80c0d5451101c8402039007404058110110344040da55590849131020300144211a540f10000003106102c650411030064a082c0c2c801d416140c07070160062034401c0054401b800c1c0c9049545018000710040c04550014040341610307452100b5a840780707020717100c051510300c0d0503a150003003004003506000818006041c0e00160782d4100302081d0203250144400140744602c2d8800902e010380320400f03109010000c103885286405101102000c1d4001841c00caa40d031301160b51859000150440c100403060003121188002120001000700928103500d03100304450080f200112004130845c00c012102c030443c85034407074003100750a20240f03450900c000f0800b14000c0500722401d15500140c0308007814065280440141200c0703614030380d246401542145030703400a4039410040b9090001140866010303009071441c0701c0c03130b00b08208500e558580007110800c860109140d0070042d100f008003299118240210720541243d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 832978669 1250 832977419 832977437
    0x2a0d020721020c0a030b15060f0901030509030708120a18050606010807021501151e1715130b0427020a05030d020d0305062b0b0604110405090901020415 67
    0x9035400001d0144540200b150045000d0100540d20140000292070b041540001907075141611542c445d0029004250b0000010a189403507052440040c0919032080c1d070203104036125545540d98a010341e8074001e003220418800707200000f02c200c03040c40c0c1c4401c00c3e0801007001d0b040c005030b841407145c100c102510545c0280741044100e50704880915040034443c03000b40001e2444480e40340243c6810300544030744002c000c0c0303030406070f61180c0d00355094400000b00101c003406034006c0c045d00300d140541010001181e0750700002e82c581c010b100c0390600804064086400c0000c114402c00003003c3e004081a40305981e070007800e601e1004a0f4010903481d810000000c0d00c14124010021884d80c01c0e031280c0c0c400e0781701c0018160b83d19400300384080004c1c2035007804100350719000300240388072030503240145003a4207280040340030b403c07104085000d89002d04c40169441e103560041c081656001c1074104281c030010001082242441d41c1c2c01984140800001800c0c6034681865032036136000c504c1c803c4e00145a4007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 832979919 1250 832978669 832978703
    0x406030618020411090303070609050f0303091b03030702060702040b28090e011a091305030a030b0111150c160803071709030c061b0d15140103052a0d0207 68
    0x702c200c1c0c021341800041c07241443e0600c0c0001b5601d00c200080104405d46840140003000010000e40c41d009105400341c80e200d180194000c2d6868501c09a001d400400c690b02ea41c0d80ea05002c4100c0d09159000740c0b03001e05d014825000d02001e0540880c007641c00410301b00c0c840c500c1e40301070125504204840496401141d140c041c0140999103817584260140c0d240c00c0c0e907252902d1220418881d5400c040c2d60009480d52100154a4401c00f020400741042c0400280742205030350561042c1003458007600c541d406100e0104070540d5540ba645107a01c203800540021420f504940b138050009400e00302d055540c074110340c0d42c5420f0140c101352084000308000f45460201441c0b03205040c2e070b0102042d0003e40c2003000510702150340f4003016020a02d806403040742107181807400d4085511015110b2801d0220066000c072044200c07486200709903108010200003240c640c0700e0300030035000303c00c0c1c50f03e00d14880b40000e118503110b041e6840944441001001001c061000600180ca41c0d54003805070303252560040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 832981169 1250 832979919 832979921
    0x607020127090e10060b0702040b032e11030f04150b060c011401060815010f12020a0f020d020d02060f151f0e0d050d03050a020409180c0e090a1104060306180204 71
    0x140b410740755141c10b00304d05001010741c20090382c44823030b011180403078880300c441e0120b41403200d410650100c040c40f00701901c2c481400042d03218003070b2101e148100008100640d96082d90700054071800a400f50040108021031011505031401601d81e40d00040e103d0003007400258140e00c5000b5405c10b0380d441d1810080ca42c0c140c0c4c15500d0041c165810008880d10700304001702400c0c03502500082c10312807980740c041541d030311688001004209800046545c2c07a404100500448454220035005100e06c5d051551410b101090105031000303140c00600003511112808010510020840700075900c511010303d0396540c445681c140f00c0070014800481400b1560070080400340d080c00e110b8014601101c4542c00904001403510800241e49000a881d40310490b00c42c0c060300c680d40c4480c0203e0b0614641c03100e82502d00358901c040c24890752180b5102030313540710421000b90003203172000c2480c3c00c4002d003000400e000d0344c1c500ca007a140c0140009101030b04d039611441141c3c2070301748081b0180190413003c6c3c111309003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 832982419 1250 832981169 832981183
    0x9111305150301090302030f070804322205130b0f0709140d080310051003020c060f010e0f090f060c030103031206030803060409050a020d030507030219020607020127090e 75
    0x2d0b80240042440b5440107951b034426080c0f200240e407030000b01d0600344202402610003401002c030082410058040d8210460702c9070150050800b052070b46060700c5807030f00320340740810a40311800340b0040710525200e20008040c001c10082c0c00803800a50742c0001804803401c2446546c0701e42030040c0508020b80300800081035904030405245800c03c2d807110076038854204e0301e0390540c481e142ea0f503669940180140c50740c02c554441a04600c0a00803540d080780c06401034030401240c8000c0700c0355640c3d144500c01c0440001c3c8504559800d00c40c010910035680070b600c490f4461558030844224184450141e49822011034960480c4d1034040010320070141c0c040300c88180c640109805100041c01c640310030220307100142040c2d11803540d500034201000010b01051402175001007601d002110182009400c903400007908a005004000508040104001c0c0c0c400c02c1d42e8003d0b2603d410501c19500544604454818600108185d40d4032120b6a4620040800c0504164007020075041c041c01070782c902d4012 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 832983669 1250 832982419 832982461
    0x1f1b0b0906010b0901020318010219060b18010e01120201020a05100903080a0504120e01020f010219090f08030a030b01050c24011d0c07020d020a0e010e010e0402010f0309111305 78
    0x703800c004e074441c20707a4000709803031080032401c2d0034001c05130003880140e14020010b18035000c00500e440c0a4000d1022503032003003020000070345c1c9a003c03000c800b40d0750318a507901c240506e0407080071200042c8110308103a1444540580b06004580851165484291500d01008035911840b80c840b06610105948515025040903040005002600f010754031004071a90030a601400c100e0798644812070740e8400c114031074040c0500c00013156101050005000c62142c41406280030440e612400124041d01d0b40184d0100c1d544940510b0800e000251300300c000d1301414410360304100d0180b0110405200070700404003200e03480540c242c02c60304102440720720103005900c9444200fa106d60b8542101078411030680c3c0c8015011205942d5280c41d100080180040ac507002e9041302c42041c010451840d08405103058031000303034005070f4aa0381c6031031410500c4003c4a000380050380d408103100006001e40c00c4072040c0340c0702d0b4428150000a580c00f0400e10319080081854050721142400301004280102003e958 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 832984919 1250 832983669 832983689
    0x5130e0c10020d141b0c0a080d1d210609010f0605031f06080f1e0313030f1703090c130b0f19090f06150903021f1b0b090601 55
    0x1445010700651128080250207081c8038074020042d100381640c40441d8810002003205c2580c190080f50340c0b550b1100707a00242c60184c0701e4000d01244889000800700034180f0250b489061010302e032511800c2403030344a039a207070304000811035640c50702c20701c805251807640d41c0e1001000c0d00e11b091102142034880c00707030341151151300e010f10a00c525140030a8503070940c5590011031100030184800f00300100140c1e03218215500541070341558808010845a606461061303941c01c1c201030040358075459219040602c0d00c980822107007040000d0080354102840d078080c4600707170328107000c480040700d20354422141800150003a4140412514045642e9000000440400c0113044400c00101d400e040c4407440c814800c0d10007446025041c5000303841c0d18094070002d007050004040e440703a0307a40a0075544c00340c4040d8503c1d840000b2040c500c036045030030451b6001041610740b0380c0000c40c0000400c4500e540c0c481000300d100001442010007a0040913483d04c40d40640c6002d00e4050030007400d250041e00258110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 832986169 1250 832984919 832984939
    0x60301140c0f070203030d0c0c03230405090c09040606090918050c0f060d0903020a0b0108160504020f07020a120606053c2d0301060302030a140705130e0c 68
    0x4003950a0310b940c0c076000b0710a240d58501c42c0c00068a10b004110702c81d5a4582085421f42c0e000350702480c1c40c50414030036141c8154038a2000c00141c042c2d41c0200c0c0b14141528144000c00c014580984c0d40c54105007404041407030900c014011030700303551090308088041404100c080080b4602c0d403048806414240075610750454155450540f100310245501e03100d258440250800e958651003210074590482604201c1b0110500d00030303445650011003a20b080e003039a400040ca040012408251001d102c0d407007280c480303060404010087d000320350647c448510920981c001615405008400f4010390384140c0800000d501d02002a102035800150144100c0101440c015040c28040c0c1d40102802514041201400102000412080e031060b60300245003855180442072401d01c0210011a894022650001203801c2c14269102403000035055404010f420300411001c0c11302c1440c0306500801e5a0201e0307503e01c0050340c2e5513544c00d0340b200d07050b564820024803d8810400e04407041c0c01583c0407008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 832987419 1250 832986169 832986181
    0x15050a05011706090a0e0604030806090a0605011b23070f0b09030a030309051006090504061a0303040501120204120305120108070e04021011120d061e17032106030114 73
    0x42c035900074003a6030040350590081000c0c0f180c0e6410225003920304000b110403900d003601700140b0411f415500b280c042c070f190300086100c03403400d0301400003600c00686034016142c0c4203480803401d4a15102041ea182d80400b0305100c120b0088000d200d05c2c400d0310000805546080c0a82c8071103228080c0d2080e6000c50007007111805684000c1350380200150107040001e4000078604001b802c004040b1402c1c241140340c0007020032044140e5105c90700881c01103004010882c0000c000181ca0311403001c0d45a80750b030052000704129032041680a0384a2094800503080c0755840d084105100c09100b0101d010500120b420300f655846243c809004248034401401c00c18601303402c1c1000c96002403c0030b0f000f80403800240d1260350103010314440d46c0c16240112200c510311400c0b28035298120100103130700c090034127000080c592408030000403403844000c92a85440e1804500d540c00c00708100703a40b070b807600080c4540c1c107413100c400e8402041c91510b81c50a070100e182c480105400c4440007100419079806280078000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 832988669 1250 832987419 832987457
    0x30f0f01140a05011d2d0114100801090b030102190203360f1206190f050108060c1b0625030c02250b030123010507110411070615050a0501 61
    0x1c1c265400b9242c3c1c0c40c280c4404c003000c840d1842c612006d5002c1015420320000c0c1101c00c00c0c002e4101c8242c2c15611440341038031000c200301ca0441161901c00240c10000510400da500d521441100500900061402178810909208a50700e28094005a0004036904010503a40004131401c040d1a100c00810498405c0800c01100760700100c25000d4503e00082c100ca980311030050158204c40002110351078a440c0707105441e0130018218240e8018108600000340b06214080c170350603038400340080c3c80b003640c512610000ca500601620b4064020703001c451003003070409000c0e880c001d01c1c540c603400704500045090303070040c20303400845081050315141e000d4000d5540030600d0a00000107860030300e6a21446498040c161110f074003c01c9000200100001c4d00b014101620351000c0d0f0107a41243c1ca40f01c8100056901e4010014081d1403481880013442042c0b0f4694804101c0c1080030003882c2c1881c1035174807030001b101d1103016032200c0352100f080244014070b85000309400821003440e10550048458403010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 832989919 1250 832988669 832988699
    0xe060a091a04081b01020106170604060e0a151a0a06120c03020f0408010207050d0c0c03260d0f0e0c0105070809030109020d20010c0f020f030f0f01140a0501 69
    0x440300100007400084151411401c031402000040100c6015581c0a14102ca0010300d545106000d51710300b2500160300e01c102440c900302c88000401822460748d0f0703504c4d40409441d080c2d40d082000e014040c00240011150340c4510340c00b0901e178400041600440c0b911100c1e401441994501c1040e1842003080703a154010940c500b8000114004640d8900040c4260040d01403480c001118160100c1d001ca0100015030107481d00a01400455501509a01d803d076410214400c001e4a403450703021092005c40d03480c080c51a4940700302e031800d1200c1301d45030702d401c0069048031641e441c1c01c5031510744c2d440c1c0121840c00f50000c00404e03440502040103150001030401e02c40da072001402c852000c03803c042e0b107035400e5002091a5401900c05000501503161414011010384200284218109044001075200d54880c2404a91005540402010680802198121300095640e15124000707110a03644000d1102c1c00f04414280000701742004941b03030b40280320100a2031111403c0c541030040150000309c01d500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 832991169 1250 832989919 832989929
    0xa0e030a0f080a09080f0f070b04060219050c0a0e01030b09010b06091c0c0f030b010801020906090130060918020303120907080a081902190b070302090301050103080a0e060a09 77
    0x100381c1c0c40400c1d00d010341e510442a44086817602032110320712040807003c039040480003050000d45100940710194502507003d14080e80005a004c44030821f41d00101c00c041100711401041114100b104032000111250155004214654240c01c010420807030030068803500f18a81c84028403020901c0400310f0306600544009510468420515030403481d018072400d482160130250320f510060310303035a02c0d150040d590b100c21105c089054000141c1c00c98107200340d50240400601d8a0724141e40700e4011281d00000c1505213203008400c0c00c03105201020564416119411120081107140c64102c002044800c0c00510003101c1c1c0c1101c00e4000141d030048102c0d0508205481a00146e441c2c48103001e2806000c0d400c4154980f0031100b1500a00c00c04401804a0307940b400c0504c40070803d014022a140c421441c20160b4200b4411030080000f14140c415942c4110f65203030040c28075440c440004e0079a8002c0e801520101c0c0000343c41d4403142e41c09149041c2d03050055800514101484d07400602a0250740b045e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 832992419 1250 832991169 832991183
    0x30c100b061e090d050f03071e0305031b09091006030b01030b0d1e14070302030c010f050a270b030105040b0a0e01152f0618120304060b0405010b0a0e030a0f 69
    0x303d40c40d96107440c054160150800201c44e440d88103000156501da100420658110701a0b2100f8000c0b0714040e886550341652607545c0a0540e158214030916040135042c580782c0440c000c0c880220551282002c05d0700c12408200d0241c1c855150504c060215a83d401d105410141024480c0c0078540b038481e82400302540c4812080449189004103509089a05e100100a803e070f000540381041d40000e500400d50340220305071620406200c0c015a0b081c02c80b20402404030f02d06005000600e402001a0344c0c0181602c020f111000340060600740c8885441e41029400d0740b4088018009420113110b00040104190b405040e083e05200b1616520501407240090001c4518225103119210790940c0320705d0304003e801e050004100301c2204010a1a0243c81211352207018000382d210b00803d52041e8081e6414006080800c040025145260384010000d65000b41c40340e85e808181c1d26540b0400c2c1c0200881d4403e10340310700d0f81100051031880c054005900c20307444210384a010913513080703c0845440d80000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 832993669 1250 832992419 832992427
    0xb031302010c0218280209011e03060e0106030903020c060f0418200306131a190f081c0f1704060f06030c081015030b1305030c100b061e 60
    0x2c001a0081104284161300042e030340c041c00640c0309020011070780703021003103844400780c0d1030301644204070300500c4103150010382404900340c03103841808400c10f10202c1e80c1c900819069181c03c1c420030040002c1e0710000c0001d5a0340b40e61014940d0520000f485644202c40841c0351000000800083e40030350700920044c0020340d940b43c44480d06e581d1005030901c00c041e0322405000008045682070350800c441e950b01400303024910b804140c1d01d07441403c1981642d040030008901d8001e05101d40c44010030040b0401c0140054045889814081090700400007a0021b040d08802c07500d001c0c1c0076030700600c0c0c0764082c00a4810000b005a801a020b00351816800c1e01c40742c0c26646500300711000c0c1540340a100790781442c00a004c0148200c4050f250141c2e101c0208503550010554400307022260508180701c0c5550100906000040101c05601d40003400f0514401c0f070f8860b2034036070905640c010300e014025544041c0300054101d00c14080c0c1101c14008075511818039001d07202e0780020f034203111103030720910f10009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 832994919 1250 832993669 832993673
    0x310080c030604032d05131e0b2d040302030f0d080106120b12153402010e0f1b010c030e01030905070902040b04031509200a0302100f08010b031302010c 67
    0x1103017041151000d10180050500d032001c0152159020110002c4818840750010482e42c803588058086010140036101c0e1a518000c180d0349160000c00700461946450140c0c10014540075120310703100301520707203640d940b18910b10406141c60403e80d540a000e42043c11040d1000d038000108504480c4103007070030302e203c1140b290004028071090030316643c0119040c00c1d02038410400500045c0105010307074544015264080002804c0070a50030301200044001202d10320000e41006101c52058140000301c1c14480340f5401c1420088100350481c6103a005500e0002c1390700445181d5508484282858a590501620001c03e40c86071900c80c94180743e100c0350300b4000c10000b004001c0c0280750600c02152541d4580d1150780a030b030b000348029a21700308800e1065900d040070f44183c811180c0c0c00465100302500e4542849a0007000b40065503005071815400000341c0c0b1427240d0b030311550307143d075440c3c40c0d41c00e4110340068195041a080100e050606004100100c00e1040c416114540c090828082219940c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 832996169 1250 832994919 832994957
    0x5070b090a0210050705010e011503030e0f0409080d14071d150316080a060506041a1e040510030b031b03100c030b0321031302030f0604080310080c03060403 69
    0x60700a40140d40f0000301c0c942c07070fa8004040c0880c076201d58000d00c0210305000e400c0d800d035440e1032080088041c10040800001380103910401002c00301030014aa60010318000408560300404143c4d18220001035000780c050780d5203e0240d08064082805149007401034004040391030134035107080c2160b00c0e0b815248582d40c4841080b1800304646c941c1d140e0b0792500d00c20410b8000c000081c010082013103840412221101800740b0015690007402a504061a00b00c0401c881d404c0a0116003012604000d030140381551101e8541c1041c20810660307649914100a020038601031179211400c041c40c1c030b035007408150780c041040c100702c4c509258a42042000c1e000040d09042203e10100c0c00e0601d00401c0500c1c0e01c2d010307002100d0341c03001102503039100d0580d92400d81103e004d559000810002c1040020503002241c01c0c0111541d00140450341c4071031290712520b00d450320070780781030700c1c0702e5000300802580340ba40515850142c4604400b91400e45d140f0b601107661000050001410b1065543d08000700b1040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 832997419 1250 832996169 832996183
    0x32102071401020a02010605032113090f060f060305190e1f051e040b06090406180f0c0807031a071b0b01030201021501050306070c0213060306050f1605070b09 70
    0x11620003501d40300144a000794090300c9140059420094000b480d45008643c081c0307484a4202e41d03004100c0103280d0b800c0c9507401021a4070001180341c0c1c000c101030a041c41440c4044908480010303185040142100240d03035254081c070100740c140310130441c120740d0001c500501649444400708591004400f0181021410382030145006090f10482c4601a401d40115000d0314988402c02644034680845454905044a014100700c14003408038200341804824158024020640010311070200e403801c501d860402401a40c07034118288030f5809001c40889220010300d203902c000c200c040e00c0c0d036646c03d042c40400c140b0321551580c480c0018075018010410300314081400b0bd6200c4224485107011300055130280416401881090341c441030100c4144801d5041e500010001c01e840c1d0b80b400001c643d05196540105c0e040445c80282c02c143c46036074012079002d18490305004c030b058641040f40e020f0398200100ac0c0b5a0f200c0744003280c0510250002c04880116030803070310340080f5507a0140c8040c42c11103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 832998669 1250 832997419 832997423
    0x911060708040518040c140a0f0305060f070216050409020a3602090a0b0304030309080301060504180b0105030c0c0c0a0b07030e030a050c041a060406170a05010303210207 75
    0x5400568041000782140080082d100100c84010707095034140c12050140c10100d03001015124551000d01a50402400d00007145c84014000a000c1d6101ca00c0c0314407c1410381d2040752a0b80c805402d100e485007a42c20481e60110407172005011600b400c1c110900014114840c4038005d039950030310401951550b0104130098a0030355a5a030352098961281c546008124603928100032103901c407810703848564021547ca042006018041c1207080c0070360b091446d4805131040741816507900c1114005218070b0040c50080025440340c0f6200c524018880044034641c03198100c400746040c44401701070380c0010643e6000000f0b581c41d40c0c3c0380d0480b22403007868100741a0440703900000302400040d03005030b00d0000303040750762290b590401a6481c004c241a9900c1800c50f00516a070040e10a10b80d050400d680000c0b030b05507540010010f050503040c003040655009800140c00101d001d0303585203508031680c03171950308002040c1c4100142c0d03141d610010040a0303141e00c41048104c0896074115034002070340695903595 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 832999919 1250 832998669 832998679
    0x50c0108240409170301030302071a07021011010c0e0a09090c0e132117040b0121020a0e040201021606050a03110f031e090d08161806030504060501090b130911 70
    0x828080355113103103900248011001440303071602c04203250a0030303200442e600c1c03070013400e450512500340e08100c010114190940100852401d00103d01202402000c03940340c09a01c9034189540020144000072606401c8030000340d0408120781d0000300c1c40000c003021259401411980f81d01c1c1c90030010b8950440301d80c090041301701740c0000380c403030b13040440621068881616800140c400300e4010385110755003103501500b24101400100041d40c0b0307060707940705c140c480041340320380c901c0c003e42c0000c15482203504095480f009940c10403086503010050240980c040c00701c4441110303e020030017015441541003070f00401d902c0703012090200d20b600c41990f884892040e800c1b5128508441d103541c00d000c50140201c060210311000c280e051501040d51140181c0559892000755111500c2e02010310400c005038080140d03c5c410f050004110407940c202920103990b011405091504205082d902d06030442c1050030324002c0c00708036503941c03911000b0400030f18036000700307c001090600d88034840c1210355240d044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 833001169 1250 832999919 832999943
    0x6120c041d031908010f0501020606012d03051b04030c1502030f0301080c130c12022107080703050f13020d06060f1203021515060f090d030c050c0108240409 69
    0x10368090140c20520842c1d65661380c0582c1d8600500d04480d41d148142d60250700200089030340c80d489650300c0c1c1c4003925642482c0500303400d1076a856410b1060906914002030345c58041c080d42028a415040c1c41140d044081e5090500b580c403691000210340c030030084011117003100313403200d640280150b69000c2200401c980d20396030f40b840082d84580d0b408840e03a12950310011611640390a0b48160b40d00351100781e0312008a8154103110400039880500d048012101410b03518a80d10110201d0510880141e500d43c2a40d051035000a0b05544015050810010400c3d0411155440d00a0980003981e011189900d040300c650500500401e040d402000b0740c26411032000c01e88860806141b55024482e5003201e482c403407070b5816003880d41001c0e45c0c0b41007500202c881071580380c6095805003406214441c549842c0c400702d00700086030440c079001c0031004580d0507a10a01401000e0042a044050078200101c080c07501c40c2208000ca800e200c04a035080500b4119421641c607254860711903240d100742c0031908 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 833002419 1250 833001169 833001187
    0x30d080a110d050603100c09170a05010c0e011b0b0f070e310203010b181203070609141b040c020a0c0b03180f0307080a14070b070806120c041d03 64
    0x3e08000c0340d150b40a84542801c81d002d1003414411242043c01c6551480d83c0a4109110005001500c5207074a403588034000c45140414002c5c401d9031203443c41902ca00404005030400500314080c401c030764025102d848107681000c60751942c06075520200d002ca1984a13a6600c66040d110005d1012501e900701b103080c40c0c590903680340e145140c081400c46520031882d407400c00c010740082e0302c801d000740044506c0900a00712402072030351904502c07000081c8200300010110400c146550401007069032455101e00741c0b00280902828403014460b5500f0283c11199014600340c031000301021900da00480c1d0707882d189042144240840c00141e584000301c10300c4507039144a40c49182e0800d8856806c03072000200942a0417070001840e4106206803401386041041e02d03202c11100b6001801d800d03083c000c6025400c01c0880742540140601c9101d05080345013420071340802071a800000707025074000d02c4800c9413044812000207600740415012100818401000401d410a6164031020f4400603c00410340940b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 833003669 1250 833002419 833002421
    0x20411070b041407031a0c0c030c011e0504020d0308060a05030136030f110304090903021b03010c051803072103080601140301031b08070602030909010f05030d080a110d 74
    0x10141e8082c80440c400004940390f0a901c414091000920341c80841002d4441c1ca0401240d41d544840020041c6050422030130b000b5003143c0c01b00e01c0c410080d0b50b50325004003045c5905258500c5811414008000d945020750200d03049204800001d004e001e0f682e00000c2c041d681b030400c0c00c0d02030300c0068001d114100103240140081c41c4600c201e80c005001c4440500c150001340340500e82c190380c150b9610600038400850581d1003412090210f03903280010440840c5c584001e004043e5011301c40d42c0148044d110704203030750a05001405225210340d0606840007422a40b02d41580d910f41d4058101d42450000d000000741703810265880007003500c090706400b1072624901002c4d45003450098480c0c0245940300001111410b0a4000030b040c041014001400418545928100c02813030100c041e01c1440d0311200c01616000703007a440300006170700018000e02281450300c441401040303100782543d103290900300001e80751000040d201c030070801340302c0018820100d2078011000c2d8600e8510525510081c03007203008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 833004919 1250 833003669 833003671
    0x31e0106140402030f130c0911031806010f06030e0109020315011701060b0d0e15160e0a05130c0c0c0311100203030907140109030b2a07030509040207020411070b 71
    0x590303260041c2080c010382414000c81c0e21a403664860721145945000351070005025000d82541c5c0d00302124004980d5442a100d03281941c0040e20801e6180d180c80255650350a1035940b8691143e04400d004200f2074a2002c141800e9450604000c9500c042103c42d942c010150354001a502d4440d240001440100900780c00d8140e03031082084081445d000702120342652124411100091420414005001c80c1c1d0303481100b4091400301518031340605032414101c41101030b540884506043d0004c00207050300700c0c068091103541500c0c40d00c1103030b20b40b00000311403000410302071041d640c0f21603c40c0e5145104100204440754447c0721003207890f490b41000a00c0000e00304215002d82480740c00c05d42d4890002050300d115089000c0144035450130500030f02244016000d440b41070181c03032000800000e54407400c040c4901d046804103421500c020017200d0701c0c4002d10249441c002c50412410300460780c40001ca07200e4890907200076035920782900c04a401001482d00c1c14164040106145040000e00c000031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 833006169 1250 833004919 833004929
    0x121f0905070f0b09061b0307030e030d030614040e16030809040c09140d050c152709041e0807050619111218251d06040506031e0106 58
    0xc0d01c415880b0382c0400d001601900650044240501c401e65807440c041c401400d040103d11030405290480c0c0c0c5145156411948048000c50b0011103d84194203041200ca2101055071405201003813405070710404240400d440140185d880303041228089800b003180244e11041c4410004040d503980c1003109140e0020395887d803007039040103040802c19106000103411360312918030a8030b0ba0141203003086400316003110202c91754020924000c0039a41c0d040341482c0865020340344a580d6941e03a030319083c6221090801e40c0050b01100ba110003142c0c80d61540603074007a91140c0d8000c076034002100d0404509211030382c000c1542e00006444820080c022461078064444803040c2c820f024401d1001c1c0f0162444411145102e203403d1023400509100301c003a40390850380e416243d400c040c042c01c2005051000310031119a50b0000034104c200d141d591f00103000c000b08601c81180c14082540c100502c584507018200318841c44d00c40740403c3d695138082c40f0840c410440c0c0440c1101d8550842c900701c0c06001540703e8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 833007419 1250 833006169 833006173
    0xf070f081908010501120b03070f0603060504110c19110a0b0c1c0f05071b080102040303080f070504090c0e0a06020f0f0109020d0f0f080f0409050601030e0c121f0905 73
    0x425030303018058803820341130f0744d016101c2003005404818403078002c00928044a17814450300c200050491030701c41c540d40c050300560350b001c15224148003d10091b280c003199031031820002003102e0186580f0124424800c491502d42c2704103915107601741401c2a910031000709a1052003404006502c0c80150002c01754010328409071409072400184001300440441c81e1100030944560020450b0340c072413001060018403c580040d0b14400580400940c01c90541244450341e5002405200f41600b0420302030f440025000410140d00d00b0300c800400c42d018521415401d540c07140c0d00c00001034060841c0c00e01000018100001c05603843c0b0b402982c131070f81d0f40000f5005000360000b69040e00c0044c0150281d182d00500040b20303a00131075881101c940e03003142c015941c038040340340000c00040e1110700904000030108001c9444a0410103001e003100e201401c0b00e414146000001d0548000114403109681011640341695200d01c14901d130a0070440e915413140322101d58140100500c26901140c1900e012f481 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 833008669 1250 833007419 833007457
    0x9040c0803041806150c060e01020c0a0f060b2b020a0b0d0603060e0d09150c050d0c030311030f0415110c070e0604020406050409150f030b0a050a05070509060f070f08 73
    0x9400c02e031701841001100083c00d4000c07002c020604503085007013500300a400052501503d00c00590411010003070441d03120706501e4224052100ba8018400b44980032120380d01079803141805844408200c04110681540201105c4290340d21701d05294003c01c0c28400e541c0da11660300c0710000c000c21071400f04648131480c18070441a40304002660504606240d1070b48078265050481e0710a07807148a0351071f00104060300810b0300c001041809000ca1040c02c0b921a11400d01c0d1500c2d014003621114280303022042402d0080100f10403803040050303086074001d003a44c07200040504110b0042c044030405203c51641c0003401140860300080d0350340c2210100000061540c035a44100000d070311840c440c000009100380014042e01e034265118400c003104900c0300042540e900c0b040448402011340c0156000d511020410401c01c42c94081c156120040c403400f0882440c0200d40a0028012201d501d8040c007404941c0c038650141030412201015001400d500301c040b440e281004455102c148a944400103204d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 833009919 1250 833008669 833008679
    0x507031b030204080d050d090f2d020612040218090c040b09060105030601110703021e120a02150702010e03060114181317070b01080601060201060b070b010509040c0803041806 77
    0x4803d45007954001d4019000210345041d04448503084940c451203100d03a64803452000809900700440102e03c1110004450b01d0000b543c414403090890300f480b1410880d15106005aa80074211169454110460707461600c0314008a05803080691048948000c1d200a1014940340042e0220132030354100c40c00d0080e4075501c0288400514285d841501242060004c510a9030007040e04600141740c0004036645a035070380c0c001402d0038a01c046210103000700e0401812450034103100000d43d80415130020002c01e055136011a90903c40c2c40410101c040000c40c08104581c443c2600704039001008089a8407540c540806910710344c01d000c4468481c600100380c07402e900341603031542d0784200a0350064080c9900151517007100b888205250758040f01040080100160800c003c207400780183c0340040c4020f605007500a030846d40c0a07000142c2001007400f0150005803d81c0c045415140c00b642e1050040d1070341d14050120786425008120307180004503001c101a07203a20f410f40b01100107640305201c01c540e20 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 833011169 1250 833009919 833009921
    0xb040c0e090411010c0609061d060402010c23030c1605120a0305030a020c060406060812040e18032b150b0a0807020c0307060c12020d050a0c050304090507031b03 71
    0x140d80300c0d00400000006404918580c3c0c000ea00004181031907058060070740e840034100c8488600071540d123950740310400c14004040c50301c2c2161041c918020060b9080680010f480042070f6040145106c9405070040d955107004c5440c0098440741000f101c0e282d82d60012920784130102d081c4454840c2c0c1c0035440010315881c1c610350a10100412001601c83c204854408580d2a0f00003400c42020a40130001c444500380100402c6114034012000080e1103130602503d00d040c0702017007500d041000380510003801039107140e5a060ba045440c000c07103c030b920b15403074620301e08600415031001040111855040d45090300c0311342da0720307079801083c1c01084900303221000001c5c410120b00419070514011300c510b1202d14002c401458100d03000d4012101d0900d9907000081c90076840b6001100007920349900001000341c254040070000d1b0850002e03012000302e81d080103100303010300c82100082101c880c2098041c4607083c42101c01402c1c0c018418005403400c040060080c00b03581048020b52088580003140c40f0f482 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 833012419 1250 833011169 833011187
    0x110105071203050702240709170c0f1203042720180402030712231306091707120305060f0f0a081b010206070801120803070e10030b040c 60
    0x4048400101c218150204030001c100c0108500706600ca81880c00b100c000d00010071481504514064408600c0c2c84580240607140a60021001d1908403d480c00000404a000e2000c43c80c203582c856071401940000400c1d06400e06481281d60000240110f00a03440b159148490b00b0301c1c520112030101e140a0301c20481e0300c140940c000b40b06803850b080348040c810b04018200744400d40003021961401d07400007030890f48241c4003000491031400640305481254000c0b030803410b4a02030b200030a0000121910203424001381421960a143c44020307007000303c694810315a15810060351443d00300e0696410b41203074000385041e100700340c0078a0341010a5120340580b520035480070706440711142954050010b8089074844040d0721140c00c00c1c0120324041c0401c84107198041c101420480d4241440019080c01000303008039003003003800c50042c0306e44550391a503401402d611001e12996560b03094400c0340d203a5620110258007191004210303240540c1030f08180d0051508440400400106002c00d84800c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 833013669 1250 833012419 833012423
    0xa080f01270b040606090603060611060f072604150e120f04030623180316030302040914011715150307030c030818010905014811010507 60
    0x10281e804003411030708010410307035080d519a00205551501d48009001c0c2c94280d0003407400159841c0041110a070315010381750003881c84d82880041c2c00c0d441e01c43d4a450b0807004003c80d000607000380100300756078130444c01011074503000ad2603070b805031101c8509110784030025101038908100c0700401d00740c42c1e081c174403824100c00300303880081c41c100c10f20080b0031245800400d40c1402024041c0400000f0a00301c0c012481903200e5808a03042207004052203111486010b80125200e0301e4584030b05403601000000c4405e01072140c2180002c2800d946000c07001382c8203681201c142c3c00c0c14008a0401075400b060003d050791442c0d180301007441e810a0f0f1459458420103c0e4010103400d42020408004003c122015400b1000d81501c908640302c0d150f5501004451340b040303030003910008000b031602e024407a00780144d020900c0c01410741031800000078205aa400a0480b94500d120300040c0d2241140c1c00524504003107240880054002e906042e80748080e041c01643e0440c00180c41550541c4948101d40c0c08075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 833014919 1250 833013669 833013689
    0x80318150304260703030e071d0a050a06270f0e15092503050c0d0b0114030a0b0705090a0801110f07080f070609020f0901061409030717030a080f01 65
    0x6910740d01d03910700402c0b00c0710b503408440040c45182c460f02c021020050034880c0c040d80300400c841541104052410313190f644160301010702c000035290000790300024550003055064012810307444503d005e40041805503c05c0c4520141e001e90581316501141c40c00c1031f40e0551040420414229041c0c0304181c0d0818068050304c2d0300009414801e103208000a0340e0088a11003c07503201160098182d40c40b01c90041d09180c84510810007001040810005074001c10004d0b40c1c0c121003143c0c1d66849509409040c092403c03002d1910400704100c0c3c4007081101d0985400c0b44a00000b0b06202d000545242c3c8260303c1d081c05061810408a1406414001d07031711900d00142c486464000f44109028050b0081e04040307600d40420071014645001400c06003603031600445c40040c2041003371042100201c2000006801a03000301c004004143e001003607000c400d0207e29020b6a105078101c000b80c280f1007560461851814100f03074180c207040c00000034000c10740322501d030381100741c40d003682c090800d0400340b040c01000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 833016169 1250 833014919 833014921
    0xe1906150f121e1b060201020f0f03070c1703061e0603040f0201050417030a080106030507020a150f150f051c0f0f02220b040b06070803040203070506040803181503 72
    0x50701d03002c0c44805503500850b920300701e03d031003400840b0030f00d07030489070645443c510b04030340c5450700c0704102d1030b04000e0565000071407030000c05441704241d0707015515510003070341030101c0001c0b0400e0095041c0356907168050020264910f407000240d2840e00256051f81c098040c117441c0500d400740703503609a100480f00406a07800c650b65983c0c3c0460304034103040c0880c1003000901000480d6400882c203010004044000b41d1703140d0f00001c50040a10f4416401242050704010900c180160007044441903c0e4100d0b140d51022307401d4140d1100501500104d203890503151840103041701400311780c45010740e464900c016013a1aa640c4c200007180741403600d036030110100c3c070300d03040c000400601c004600340d0f20400e94140e101c200d81d000200c00c034511802c1000c0040d504407111514000920900140704d004440800609600001241550154210003082142d00101060541d0b0702040184024500140f038282c0d00c40d1180c611640b6500901003071030440380c4006050180e85482400044050500800d00d411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 833017419 1250 833016169 833016179
    0x70309050307082a03090102060c18010806150d0e0c010e030d08060a0b030a0209030606011d060304110406030c150302040617060d151d07080703080c010e1906150f 72
    0x3c02d9002e455410140c034403d20110154149800103004032800100280d603e95016100181c01c1081c01014004010810015840030b03408100d60001c02d03100a282807481c513030340c0c0004502003c44585981c1c0000c0c0010510320220a21600070058014822080d030301261160401900d420710400f6406526400c490f488032000c13407203002c44c2c41e030003030b0001c00951a0542e10000030340190f00650f1075462264000510000505041050a2700020300307291031501d80c40c00e100b1b40030f90710034080125885001c001000c60705104840c145c40d20f950500a004004031560380c03900d080640c21034400c8001d5403400642710790840707000344203035811184c80c3d40310358240091050356401e00c110004c061550001348a40300c900410f01c4440c0804043d1000140059410040551407980041d280c014103040d41c007240080c07240180200e095012640d0102d8400c2c0c40b003290f242c00300d0140611002c0d0709018401d040608030780c07a00c408451148580288000c002d44030300040e0000001d4102d01402407010101c840c04c001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 833018669 1250 833017419 833017433
    0x1403120d15050607053304030906031508100209040b030708161d15030f0601090209120a0807060e0f10090b0606130612090215040311090f0f0705070f1a070309050307 73
    0x3241d0310740806110205000e642c2400c2c5000011f881c02d900080c14144103201803901489042c7d0209207805101c1c40041c90300c2c0020380c0d2502d18040c0c03401010380202e110900d6031540d42000b0200304008040d1140703691241c4900355140c0d5107950000c2c613021605000a20100c510703d60500c00031840c1da1500003581c4410a0f24155450704d150513070036204040a034034840ca030901991340602210000580d564481004110f040001040c0c0f000307060300031b10b80150018017403004903990300750701c80c130003250303004a04500c03c0c1400d50101c0010f400d402004034112103081694440c02c100da105e41480300c090b813039a10600005005280c10085a803071011000c0c00590700960707050754100140c640110b034508060b408168041201d03844105080c00104051040160307d0320a260307610016111084507240500d9040c101010142c9406100345c0c00f403021440305480b80c41102d01c801d0f00320ba101d8141c1100e0f40b0780300300064960301d00011803280c0c107004104428482d02038000c026800c14001c42c200110384d1503901d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 833019919 1250 833018669 833018713
    0x5070c030b0a0c1202090102030706090602070803040311010f0b090f0a0b030f071d220c09021c150b0d02090a050a0e0f010b03101403120d1505060705 66
    0x24504125202000001840a00400b403140c1101038001c01c10071840e00018003045503880e580c1040070b006112804850343e00109843c41280c1140340441c108009003442c07002889440c84c041c21846c1d000040005050b080650480e2041c1100d000704000f203403005c01c070421500000d5285034030441d02c00102da401c08030b5000c0e0603000380702054005140844040002d141c8450b0341c41402d070039001a001080f0002c1001041b40302003202074a000000d1412005084002c0160080780e44203006406a03201401102c0340c500d0003a00102c02d0031944d903940200380c0e291200f11400617a01c454181851520501c0d543c0c40020101c900b080407460034000365401e2500a908241001c54002783c21030800103240e40c0c3d01d1b182000074040d081460703102d41882d612505190b401608540101513003082132205040c0961864801c86880d00c050541c80144140001c0c02d05100ca8126000c5600100d0003814021080e44605044049400e2041038280d070782d418400c03580516100540349800090383c40b0402032056600c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 833021169 1250 833019919 833019923
    0x20415120f15053307030504030f030806031011031302040b0a030b0f090109020a05040e10050a050601110a05030703030c050c0d12060b122d0a2a020703030507 70
    0x218121081d90300420803140e40000d6070803000720041d01080181880820322444a60044014111401851400030f015400c0381c4002a045000075500050510803030984001e50790019085000e0300d003a0400406040e0240c030010311a000b0b0202c0d004111009105003405021840b1174242180e59000c20180790100d5480b05a03017094442c3c241041c0c5948402d80c80d005140f03c1c140e81e07041d85c10180e2681c40f1010f001409c075900c503854076450202503543c01c1c01160840302c04031001f007540303690101c94600b000700041e2412121401d000a019203854140c0000e41300f1032082c0d81d241e8003207844c0110281d8800390041c010f03109420822149000c2403094222070460441418040d107400404220344d49003a041100700da00155402d403000205086034020300000b46031190f07580b414070359240c001865614002e0000848082c0880001e2a0401d159140b40700604a01ca500c40e2503207006812840500320400c0c1402d01d041010180c11040b4440c0711090345941c644d980100541400e650302a0342036840910700b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 833022419 1250 833021169 833021171
    0x24070207030213110708070302010507170f0a020d1821141602130534030b0316140406050a0b0a08060f0d11121b0105030a0b06030f071202041512 64
    0x95000700340039050041640c03920031b6085070b68482c01303410002c0c03c40300b014000e20100b00d00038202d07010040c030b0002d60302e4011020380c5110016480b2503000100030302c1601200c00d5003070700301001200c4040f6a41c804002550081200c03000201e403890350803941c1c2d00086480004100d4100302d280c40c5075422005420070003c0c403403c180e04185641c0000d00300c1003d2602d2804103c0c0c40d8410842a144040c0c121007a40c00f0315511070081403002441d50001c004550080010541d03601602600740c1c1d020054111804045030408041d2516040c124003582d40026544d400b072030901100044501f406030b030b81c5048601608500d420218140802c58409501420150340003202050180040e6901c151a20b0708d68840d0380700f4240c10704020103100752880201d034030641c150000b13407624010b100e02010328458030310246020ba0b40c83d541c54600794000c0811a01482e00802c000c0200011808200d46c443d019100315105e4084203126401400180c3c41280a040c842d01d5071002d803854818094481d0304405211000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 833023669 1250 833022419 833022431
    0x3080c0712080319060501080402060309120a1d0a050f0607030e0604090b040f1407110a06090b0730091505190c050315060a09080601060224070207030213 68
    0x71844101c002000c1007694084030010501603052261440b01d20b042400032000e00c4640d140200103000e0040c01840030b80180c0000002805021040c031801c608c8401c00c00449880e0b403038080b002441d040c192552a160b86500840b0241503140c100440c0e02165001090144103104202c213010498118038011428000da070180130400381d0381c0c0c5004e0401b41510302d6000070460510700800050707960baa80302080c0103103404c0e010b031409040003103c5c6500080e50304100b068400d03540f820b01c0c980341440f40040d140702d18043c01041084010340c26140654016134903031070a1514200c002d10803072501c01e02c48000d03c00c41d08004080d44003d400048085024204008842024003840c10a5072004c484e075200b80b402d003000b45444003146200340000a03c03545041c074194601000c1342c80e4864081051035104620121b080340c5800e04c6626828054040442a031742c2e60f59680401035501d003100484482808492000c0d40b400c2011042410721503000c583c024280203103142c091204a01400f5410260aa2166 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 833024919 1250 833023669 833023679
    0x10804050c04240602100f1404020f0a08032110180b0a03050a06140a06032f0d0c08060601050a1205071e05272d0414100605040f03080c07 61
    0x81c0c0300001e20194010304240b00b4000da03107a0403240981f01e40d00c0050701e0144034400e0b81812400c0164816410b440ca0101c3c0e14070100040c142201c103911124a0340310000789201807848903400030344c0611800c103040030300d03840d81d03840c0c0344032155280108a00c4501c004c141903501e00094002e400d03508005003002e0f51650710b0382c41c1c140c103012170301000303458150311600c0c00c00c0f034403418001350341c0d000c1d640900421040d410351b943c090001584800d6298034041d65181140c60011400b14401c1142005148008888403450b1403400002c15202c3d51081c1c2c0100000030711079500075821198030762000d98959030910800310900d4002c05010f00300e03004000c5104c401d407a8108004400210b1028a034451359101e5075120a03007100000c42184543c1c03040103094090250f03403100040d080c1d000d24203000e00d0311040c40140f401d0400c200040740c00d5503c80d0520049510360004c0b00c2c507950180c0342e07180034001c4141e00c4204c10798030b520032f0388030380074140802600400114640c6400303404500400c1c01943c4410b0355071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 833026169 1250 833024919 833024981
    0x2130b0103091202150603011503030c05010204121a070206060a0e090f030a2c01050313030c052a010804020f0118030c0608070909050105031f02091206060f010804050c04 75
    0xb8030b036800f000d64020180181ca01c4c0340c2c0c40310141e00031800c40c001c1c0062204101c080045a22500c40101030048200c0e80d81c040001c00c8d0141c8000d80000700715010516200e0074400308110450a107001d01503210302c0400d10041c40454154480d04000d0f02d011745142c82c007860b01840c0300004006441c18021141c2e0340042901c02d00040c041c0e0760713032540c4c1c00c40d446231107643c00108021002d4204010340d4040070b00086507604401680d074014060030200ba040c00f844d00381551100340c1098014218001c03a02c04280d0298004130903028071100a036114103040c00a0010748a5071030545d00a50301c0340c0310036030320b05c4c0070362050418800e000d201d4150520b80c40d58981d2990201031040d0003203004641740404211607590712000e1a0020628403509111951601011945403000d1100c0301c2c903100742c146031074910342421342c0440d01504805042000c440007203100154a88106a5046115001821060915601c1900344a00441e000300c0074044046920301080014074036080f4480d40486068502e4280c1224 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 833027419 1250 833026169 833026193
    0xa090609050105090c0109080a1b1e06080c07020901150c0b1503060603060c0f07020f030f0a0201030b06120105190f18050c0309061f080111090a060203040302130b010309 75
    0x1050001040c18181300724498103188810400e00d040081c0600c04101000340001c84078000d9812501c6e040060401c2c0300700705140301243e0071001411607105d00200302e0a02c1e1402d140101d074030903a02c413080ca03240c5901e03000d50b500c24500b019510800b081c0051202d06018040d1122161a904112405902c25916012090300c2203a10003100e58000788104070b10f082c01d0100540c400f03421009000e907803400919802050140b25411009034401040780390031521074122030b541140c0010101e5000118403507406550b0702842804900082c200b4603034108a003011001c1d1507801c010070400c0116a800d01003401482c003800591862404405000007a00412081001c0013174885440e54820f8480c000e8a102c06079032000d064600c2240040040102e014000302d80c59400060b0b2110080d4007049004050035810300701d40141d1400d510b0000d090024540d118000c01d62404103588080702d540ea940000d0361070b40114400a508200205c514100c805d180368810601c400c414100018201c00b640c07200011014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 833028669 1250 833027419 833027423
    0x203090a17130b03010503070e090a0b130b0103060b0f0334120b0403020c09070816110712060b0901060f2a03110c120304060f23040609120206120a090609 68
    0xfa0010040c400c5040070302a8601404c210f52030f03180141400f00c2c415981c0d90115101914080d0780c000403500d40054604082002c81c0c001650f02c030f55503124140000201005000c4520501c0000e00d400b07a541408a50845072084010030b10100c510748030705150040c1000540c1c0750100915050100b1499100c0c941c820441e4002d0391602c020345003034500a4900141700c20b1075446180e1007001c000003240e0282c49150701c140200c0404025410060090311130108030f804442c0640a511000304400e82130703200303008489014080602150084906000a0000a010305000124894159840340d8054034010103211f045c0694000c00503880484500b65283d00c040480c0029004807240701410020400f040c0d10700021a402c40400364452030711070ba24481e03071246609111500400107459805400c02c0149002c0c903030003d03020450030306540005030b40b090040e034010480c1b100300070856504601000703c410381e02400140c50070300140800740d04404001c209100c00d42c1ca5446c0c080011f43da601600c45024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 833029919 1250 833028669 833028689
    0x1f23010c0c0801090b0a0b1302071505160f03060b09090702100221010b1801080c072405091c05090a05030d09050f0312030a0213030b1f05040203090a1713 68
    0x203280d03450001d8402d10f0140c40c0380c0c40f0350305010807000c1c01c1e92004841c50300c208c4410f41c0145e590300395150044e40043c40c8105003040e140360104002c4c0d10601c003824411000040e07a5400c08c5044403003002d9003100d560740100c2c0c6960000348100d01c26410422500e6810010900440d0185138514981000b60382c000150000c900b0503500300c081249410240e818090070784805007a0511281e0408007502203204125681000380b80004682c4c040203200032036030150b070400015a0014181014262108060040c640c0554904000502c21103804111741005002690382030380c41c00b000c640101c4141c0c000c0d03000150302c410580740001d06950204103812100116881e50f40507685400c0801c10300c42d03901e0031918001d030003040040d210340110b1720449a02480039800141c03515402445c0c000f4040305504020a4942c045060115580600d442d141900a44100215a998490050009138001922402d11507071103402e042c0b000401c0d800840d141019009051400d12070908407015400080364002d074040e0f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 833031169 1250 833029919 833029931
    0x150a0605091302011d0f030304090608060c04080628140613020c030a081306110c0f01060308030103022103040b0405011103090f10031808031f23010c0c0801 69
    0x35003081c1d040350358064510740e600c480c0b0000c581c00291051501c0d4041c0e104a8202c00300a6050790754060480e02c0001000d41100e88860716160604c00500060044891034482d00d000100210100000c5030252203080000d41800d88130480164000c201641d01c41100d040a0b01016512118901c5100000003031785603800310b0f60410b207061207545503c030240d00a00300c0c0101709915003000000100e80140c01c0b02d1522007483d42c0e0381d907040321140a06400003060541804141c80140b11000084d10040d522801a101c0048041090718201c0c4d0641c03000a14401c1c0c248010400f528110f050310004625078002d1802c1c02841c000c1580c00c3d0740c8941c018850141c0c000c1000e10031964440d2111100c40d28410045260907070640c000741482500e600c45500c01c0110050304001d140c07098024070062260b40351041541421132400007060703002120355000440c1c15410304002c00d00415415011142070010714402c044203045135002043c030b031010342d6060103c80d00d406000280da0307038800002031901c0c000008003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 833032419 1250 833031169 833031179
    0x10e060a02090619020c132a0516020303040b03070305250903060f0b1005031e1005040b030703060c0c110d11091e0903041401080403050405040f1805010e010501061d1002150a06 78
    0x310052308001d140e402085500300b84480b54108040340d92440214641d000904401c0c0300013403440c4503075000100820000b2040c0811190141c203d00d020700c4a030307601030002071001480080341a81000d40c0c00b000807428281000032584584c0401c00d41608800d0210301b4406d82000724154241c120141400100000b081010500002030b8840101d100724122910300c0c10504550182d0f0fa103580034580c426691100b02c490343d03617402c105120007103501c40d9051204598005c0c014005045214041d511090300c522050000e25260288030f94607a40b200403041e15801034014001c520300d0013040380c0c1d00d280e1100b0341c13841c0b42d10140b01c110b8450001203000b16951400d01d000c000806000070000e506101141c0c040c407000075001000e480076160151400180c0345144085ca202030aa0554024441c14042c4210740a2150640101c800e05044200034001640e88902c00c0f9020102518202980001d8020351842c0d441c0900c8040d15100f0300380304407a0803412412040207415002e070341a1280c070742c1c0c1d50801c100b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 833033669 1250 833032419 833032451
    0x905030304200d050a021201230a0c08070507030c050102130b0d06050108010b030f190c0302070308070801051c080403120203130503030f0a0e041d010e060a02090619020c13 76
    0x81c410303000d8562500080c43c580d40c80340d4540f006500284581b00010b0754030302c0d21900358005260355a2025940050303128031080e80e01220010b0300d0105c1c425007440c12500a944c01105007600600ca507643e070600d40681501d00f101d000a440000712440c1d5003c2107807081c15260b040c00000a04006a180c0d95200030400c1c0d81c10840d24640c0c0058148404000104070100303504003aa0b5120610140303c00d02c5942e03410a10414101e02803840030f5031464180c2c1803c120f945580036041c403511a8540d204142c0340d400b070544441a092007559032000888001d070341180011520088280c0c0700300240b0382020f0b286e544540389902e1050a13500141d0005c907140b05070681050160000f0b0105601a615180515080340504d108201c02c0c1014800a003a48481c1d9442d542d11801070100c41c02107400780c81400780c004d640608144e0400362080d01c50203000c20300d8201e0610840e450300350020140351900019160220400000441e0366065001c0c1807640394007922048009600d81d541ca184c001000740141207204 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 833034919 1250 833033669 833033723
    0x17041805011208030105060c15070f020d020f03030105010302070602090a17120405060f030411030f010510060302090f1009031509030809010203060108010e191b0e030f1f0905030304 80
    0x1901c034120020b00e00000c501050f04490665109031aa140c0e66002e5107032141ca02140c2d0904544004005010801990f0344031200707a000400f55429900c900003104c0c0120b9444a070140c48031203640003040100a150b0003503004101d5540301c0c11026041c014801c000603001d0059901c40c0c0350301c120003000d03490075840030300080e60343d1201c0034405420142040086042802030001c07001000400001207001c1c050703a402c2c06c0030084130003000c0342c04071078120b40d407607008c0c0c41c041da0901844101843e0109072079020b802540c0c10f00901412480102c0c1c2403204000c0000e030a0a0b440c41801600d15020010400f42030352200303c40021031300400c083c001c0e0700e0b0080602c44000e00f4050964414003d001060783d000300e05c581110010342e00f2400c143c4840c410055980512503010f001176251000300c00d0b10001d101c440c2000845241c5403000040300302008e064485040d042e0001d103d400210000e584281c40c401881081012860300180303401ca04c2e541c203440e55100340c80a5a54040e44c0c411001070f0040240310f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 833036169 1250 833034919 833034929
    0x901060f05010c080a03050c090622143303130203070f05011d060c191a010513020a09030c0b09190807090e1006120506060604031e1704180501 63
    0x7203080302c420b07114004035008000c4617a0405889502040c0304104690503251440310081c5481e40e80c10110860701e01d0032840310215030b14000b101a0000b9403110202e134441e40b296000c1c10003141c0803000120380443c2c40503070092210b504005110610002d01d1803018610079003503649000c440d00341c0d03401054644511071740203400860704c00d90700b4041640d014082100030712480d04c011052840e20300003d41c1c10700820204180c6d41c40340d8140300c9881211074001c6800e003800b0790080180649080300340e0412140c00d004a58002040d0711500079070090660040c201d10359180b618080c00d50b00e0f6035600c03040d4402c0381d02219203068049800000f0740b601d010b1a642c822201e00c44070041c2403409100649600380c9200d40c14400355102d90b00c1c0c10030a03043c45400d8071102c4903003013000340a0700c075061006c041440510a90700c5104210001344682050380888003500c0d004201228080813441460b0b040300d0304068100c07911000c00361446c070368400100183c40030b0b015088407941404400c00d050f00c100d55050f407117 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 833037419 1250 833036169 833036177
    0xe1609020f09040c0306050613090b0616080a09081c0305090a11010507061d062203200c030d09140109030f290a06060f030c0f080601170901060f0501 66
    0x40c6005001c0190119616100d0644003c0b401d419800300c00d40041160b42e1005402030303800070345480c4200010054000755000641c1c200a480f401d00244005030080a200541c40c942042d00100481d000d00e02400c610301041c9404040030b91205501800d04000c000c3c0030b0440d604410402ca0250b03058000c80798044071b00c0004000c2240241c5500200d90404c0804a060290004041040c803940760000b5180280c8020085106054200c2069944c0402c98503d00303e038035140c1881d808450070380d01d031011a13609a500d002100101ca14000d41411a00c0702421052084c00890f00741c40c4c42c1408107918031800d58035500441c51030480d950810344080340d481030401003d16428400511808982440300e900600e242c508107028010002c0c0c100407a04540041c4a00d680420440f4252600000140c914a03541c00803401c088d00c40550590b4000384074080401c490483c0d03590414824009182c1c09003052400c40b0300d1030440440305180f10310a40e03050b0b03400c5e5181c0c2401e00003651140c40c2c07040200400c0c60 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 833038669 1250 833037419 833037427
    0x408010f09140a111e21070f0b0909190504050607020c030d0909022203080702101407020f0301150305281a040c0b04120b0c0a020a020f060d0e160902 66
    0x602c0580c2404d021240910400b40c0240603446096842c180300c40b0010054000002d107040000742503035050954000c8000c500c107512012404502c545d518404559004014030b05000d00c1c1e20400050341d41c000c2448c1d030103100a48804403807a40324011140203d006001920720f90415a4009007010f100f4910356000382d21644507030114a5000303185004035400c95100680320540d182e0007403408024241c1901060000c028044280f0402e1401054010300c21a134006002c2100300c01616501c00400b81c00440c980d080c01802c016042c12511411622001400002c095a94243c0382c00700c40810b40090390540e00c604059041c514018056243c40c84001e00c845540d402d06a82d0568005800c242c050030114a01c0301007010004a82c070382c44090311001100503240da844040e04030052140b4a01a14002103546c0032501c1040884200c07482406035a0242041c80c4070741e024009041d040c0310b009500300c10704000028070305455200d84114404110041c00c40101c14008041c2e0411b19500b0803001d1510400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 833039919 1250 833038669 833038673
    0x2062208011b120b06070b0a060501030908071410150503010b0607110d11040f0c03180210030914030f0c2b0c0f05010f240f050607080408010f09140a 66
    0x84050310000d1607460510b10440038801c2d0318018003144c045036a04080c001c80d01700104502090b070700780f2500c038070401040301a50751030044081d240301100180031440c08101030001300740126090910305154078100c0b0400d007840c1c1340302070446140c85081e031003050703001500707001c00d14080c01000c500990440d00181464415110161140122208180700d509480010743c104003141400d09160600203108001c17000305d41d003486024141c0040d644001900e4095580d5021a4180300b40c01358a8020302010b80c2741c80144d43c1500100680c20055840e452401c6400c41d802104000800f00b1200d032145d000e032940c182e007011918281d0b0004000741036480200400c440390718008140d503540802441c0495521f1124108650b600842d02c0c00a0030075420407a4414001e420768001c403541b00d50511403c0c5040280d403a002d0000e800718021400000070f010f83c20030141c41d10101a0800e18058074031035250a6890b0000c0d0b086440010103104507507180e451900901010009100d04645200040c003448412a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 833041169 1250 833039919 833039951
    0x9010e150306060a0903060c0519080405120307051e040306050106170c070f08130e0a020723030405090901050f0c0901080403081801090c0306150803030403050f070206220801 77
    0x100520302690004c100108054401c00d82d0074005c40c0c000c01c04000b0183c1d04207000705030782e11104149a6181c3d640c102c2220052050451910850700100a401c4407440010284407540c400390540041003002d100f0f08210190100c000580c088040d0707240f6a645e0724600e04032060b00d41c168091002e206130480900c28061610747c0d02c81e4408500307039186550362031604c2e1002c004021300324049e10001010900c040301200344401002961100641d41003640d841079000000c1c2d120f5200c004007070612440d107501510a541ca00400e07516103001c252400c09842d81e01049120f041200d05030041ea449000740202c40c0e0a15200c1034008400c148030038580480382001800c0d201025000500304030706080026004000c4032048062096001c0091003c0c0c003941c10035140034009404103682c1103142114102c00c08500801c1ea204480519019606559458030180d5454000150b1128101410801000165107200c01043c3c0400c0d0002081c1c040e040e00350a4101c654616081002c0c140c0c0740aa04103886015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 833042419 1250 833041169 833041171
    0x911040305030d0b0604030b010b0703020c030318123414060703180306050108010c1205060a180204090c09031509020604170c040e15100501080126070b09010e1503 72
    0x74071a008944100c200300807170480c4c031440c4e0014040004642c00401d98546480080020500076403ca549885042c002c1503100e100e003a070780c0a0900c810340240807250609070b21011036003130014280c0340440051000d190981c201c41360603844280c1951480c0c1400000d0f0041c88000d0800f401012401c02c81050200d08588120761014041c0720034069815240c0c00184603440195601c640c0134011540d44203810f0340603081e00070400c004503910440812515005104291081c03400900d058029441c0a0590381049404550305404a80800004c42c81507184d001e00c8802d415990381c1c1e605107a10b1820a00c81c08110021500c00103800d000c1d001d0050b0303980c6010f84041c2d400d00200c8810080311440d100e441d11401850603034000342402e5141a40c0c1070080341103040c0002d03005070071441e0368503031110340302c0c6e00100c2c00f07a1404a485240180269844441800312009500c10b4100c0341c0c0b0f4250400d5480c010f042d5020359422200003c1408c1c195900004661081205951070100310141c0d092248841c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 833043669 1250 833042419 833042437
    0x19030c03060e03070c030302031c0b0612071b051507020303070e190503070b0904051f0303031a0909060103210c06090204140c0c0613020906040b120f030301091104030503 75
    0x303203807070203442d541d402441250860f5500070300c10408240d5a02d0b0182d1650042c9191441c40d40e06003403603072181c82160042000d4000014040b602c1e0103100094400b140c44058440010452407074200c407000e982c200392088089000788010b00d0154000c4035121401c990062200046400520900c015203410414070442214100c4850340780e523080c240d1104604c0740b1a8001d507030500c51514001050540c1d00001e2000035001e84082c0000d59590140b20800040d1802000c825280100100003180c4a035201054030280319900c45014840d042c0043c00b03010090321040d8042d0010b000400401040e0042101412500c0c10040d0307a1250500703015109194100c80035200076210101642103507565403058900b00319a0342080702606124010300803541000c1e690426901c1000e02182010b6070f800e0259080a6008100442d80e81c3d48070180030140404400c0240c11030800c1d030006202c0c0e00b00780301b42c2d00059899001036890750314228800c8266403000040c1c440750341d010041840403501c08422991020303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 833044919 1250 833043669 833043671
    0x5211011030612120d021206030d0507170706022a0105012603070b070807020d022e060b030109140f06030a0818090a0c030b03121c110c03040519030c0306 68
    0x18960b4462141088013101050b41e400c54002501e02500207640d014201d40e95a0307030f40350103a03039440e6014941d441310121184008a982031103e00b000501c0d200d40d2410400c1d850304045c0c1020b00558485060b40c0004003410f00c0c00d950520b01d20200200301500b12186101d00001f0300c41545026030140c103001c2c0c0b1414011505000c05180205c1c40d00030030407135071403d5004000c0c5c0070394540f04c00e0042c84400b05441c000d0040c014003090608007440000c0c03228107122002d01040050b060050400e04a01480c05a00318560b00c1d00340000f0b00c1c5074054040c500800103d0350108420840d4a0145940306005181d46640088034007440b070302d5100011039003801d03640700000b00e684803200720615100104080d405903012001c40e003084030644a54102804514447e10b0901c1130a402d03004044d03c490b10760358044a81003052111500640c0072201d03501070094000000070383c01c0c2c18040e104c00b0f00d0303000d81007022140c0d200160410981c1040d5120103524001c041a241c001811581d4840654a007803001600b86 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 833046169 1250 833044919 833044939
    0x120605131722030b060a0f0b09061804090b061203040e010509041e051f0c08160513030c03021c0f020d14030c0f0d0908030f0d0204052110110306 64
    0x716901910071003408850040000115074a14000140c0b03130381100c805015040807080090030011031166042950131085a140c1440021410301c1041e400200307041c02e29913101007040c404d0b034440e03200d003108079805585408143e01e0210301b0b000552920400703100c0c46900802040003450480600070f415075104803001101034403207003054120019100750000032500f0b2040054100900041e41d00c146001001051109a10140120080324002410707032000c030fa0701000050300b0310004c00200004400741d08005080a201c1d0806e1080880039401c12100003007208424015440c00d01e8108010b9000480b29811600c400e94a0381d6141b11804002401051603c951204200a034028800740b211440207ca80714a00d00c2111070303492400d0900550907001d4040c50740d0550b44154410400e84403d030b4015498805044803280b550751101403090b0406a0a100200b60b96960060203204800c45004620121884002d514100403440074405503062400070f004491020080a6952285048802c90781d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 833047419 1250 833046169 833046187
    0x15031109060d12020c090f091507050408030a030603061103012607230a080c0d02061c05101401020a030e0609011205090f01151208030a02131206051317 67
    0xc1e0742e0351a4402007184410300c0c0700414580e40060310010702c8901301d0b0460b496840e844500d0640403025a00c0103126003001320b10131400041100e005410a0701c0d41380991800340d035921100d0568010380801c0c0002501c0b450100103004190180c1c00d52541454a40c0e031640d49010398030100c1d075402c1028100c1031264088080c0c03c0100600800f40100381d03110b41d001c000c001844513200c40c1309550b180ca600c181410078021480c0000092641c1e07103100c014000700101902034080140c00e810841c5103034100403444051020002c0b10b401264050b8490144a2804600305034411691180c5002940c2c119405002581d0100340c1c0700190040700d82041d100141c1d111360b0600104c1e03c4045107001028864101030901640910010f094066444030000800480210f625405843d1206124510507511400720000210342c5990041d0f130041c2221200500c0c1c284051001c0c0308250b0710360300810f28007038030300c00c2d0906102503801065401162020254410b00c910351310040c0b003400c01364000c0c55208020a030488 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 833048669 1250 833047419 833047429
    0x12030307110a02090c0318060108030f0c100e06180d0206280c08091b06190207030f0b01030303110a0c080a0e15040f1a04060315091407031503110906 66
    0x45001c3d0007804411440c40c10b40c104208990003a1a680d04915200c2401c00d080d030350200d0158140c1d95014041c0d45416090001c0e403c3c0358115690f1b00e441030180d00c0e44040c441c0320360310070b4001032940c442c0500800c1c5024095203a450100005901446c0c001d519020380081c0c0c0861403c0d0700020f022010320f0b040c00304ac592996117414118104d0300320751804d6507001d031140e0031640c0384d84121207050454111421080000e00e64080300c042e000d80100043c04951515411400c0c4503009006a10440341201d940340c840102c0c1581000d0305860301c6070b04400510501d40c0c9406410040003041c52110f15006205500800202c032440c80680b0000e00440c119550b2413088a90700d43ca0346c0002c1001c0a581c0c0b00c88582030496109200d10703c00782c01f012034002850480098501010048425040d007082c2c60800160003a104504086008450603580401d986c40180b00c0d41280072468140c004107071600c080301600b00e0307030b4248604072903200400c02040000c500d240e203400801016500ca00154883c42c1c0810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 833049919 1250 833048669 833048683
    0x11060f04021011030d06030c0f030803040b0402152106010c03021009030e040c1d010f0801120f14030901081005031b0607120513060305040b0a0b010e0a0603060e061203030711 77
    0x42514003000032020341c17081130360300114156401600038248290369400b4030003017016148001030042ca01400000c02041003614116413060001d084411508400541c1e82d28a82c418105000444002c01174420360b6140031700c034164001e80a081c640d000781e540b80c401954072111051039610840d101e00b2a84201880f880754075090020203081030022113090138000d40001180034582a100691028803030156201e04103041c4c2c03407055620340f40c940d03900b407006010011480c0d000c1580d000a0060710000020001c03101820526010000745450700c10001c001030500c0b0025205020b00e10102e1002d00c103d03600490b004105008102da400080544800451468058440b024150003070700400c64a106400c0801460101303c0103007044c100544a030020750480e1820385000d4400280f0310002507000d0f20945c410704182d40705040c680b00c0c4081c0d007400580351249503042500000d8442c0d038100901000900710704c0e04030008407910340803640c00318495660ba000c01012401040914100c210084c1010301a403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 833051169 1250 833049919 833049947
    0xc05060901020f12120a0612330b041505060f090f090a0c080115050d09020d0c14011409090a050606041a04140102011518060f030b0711060f040210 65
    0x610340101c1042640c0e402ea800245000b0f0043d141740000610904640c0700303180c241c3d1080c0b80c01d520400c13266114051012140003100031089047c490700400d6185084e4520b402c4070303160740c1c0850140c00c0ba40510055503031031010100301e405040c506004175034424060314511090701e5516504e40d03810307000040f00000340c0c0d074080c0d40001c1100280000b0486a420a8140e0040c54541c081a43d81c2d6070204007640304980515400200c044c003010b00f48129a0f0404202140000c200901010340c075280e00004001e6644000541c0680f0002610b85503004045d40100c203802c1750007141050710400c00704042d4000145100310041d514000524195903c0003518068113103201c2d07031468804a0100d2110642c0140161079402114442c03840d181e62050090090f04285c1140781d103131162908001503040301c41a14450781c0640c8131180890369400034102c090003140542c41c4150141881080503010061402e00c0c002c04c0e070080020840e801c0c819409007030b0095030585032045006100f0804503041e035240011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 833052419 1250 833051169 833051173
    0x10806040f060941070504090f06081b0f0d02030109120503040515010815060a0b070309090b010e0303030c0a1704030c0b0f09151306060b0a0314040c05060901020f 72
    0x80410071910030b500054031301958a40220a42103000300c2c01049400040f0380707071003004408402812440002d6880d0b0340010550400c1410203841381001e0081c1c96018424191155640404120440c410080b01020840f9682d03903502001007000072a00d180036000405010705d07215a00042151000d40c840d21750580c11041d07111301c0c44c0740d12000405691040c0c4041c2d41c241306190309150110140da040b00c1c100c8a008008114500703590922480d0b541c401401c4030350010b668400020000d5a107001055841d10981e580302d101410803084004a40364107500b941080324481d9582400c1e20000200c90700616595500e5440720306800301142c1c188201c03901010341040207018442056044034801c506280720350035444042d41c0b524400017540000300c501002c103074000d03030501c07040344503c0b14402c0d0001509100c6160780801d03521214255040365000360f10503140018002d04550341442400c2e040020000c206a40f400d0640710115002c3c3c86005144c4110000204070620340c0c020402c150b0300521200c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 833053669 1250 833052419 833052431
    0x12020c030412050f0118050f06190e010b1c170405060403020607050a080708041d040c061103220810110307031e050a0e0d110d050310092a0804020a0302010806040f 72
    0x1c00d00c408403046ea0302255640b2440034985942800816560f04c10142d80d814003040d0144030302448003a01c40c0e100c13907113071955a5040d0312035151511240200544102462519840d00d64a0880000740b81d00540c0c101c200014041070145541700e600b1642102c4d011141d058a69405080003424144449401000910009240710802c20440b01038011601c02d045500840e0030154401510400c046500903d00f400e980c1d02406424005e02040801c20f020350212418219892030010080c8540408241c250182250400101c0c0f0200040e8060740ac2d8513000348880c0400740f040440c280000707041042230544941c030300643e011039685e08003045946030505204506002c90f5060050401c410044007a02511503441c5155001e1403412041214610041c00d56941c842002c0303680d50809403141c192201c100784001141101800f502d01008603803c84040b40c50403003800d06100150420b0000c0c00d10008070208809a664003000c2000c503502070030107400790741c3c1700000a4014604038168240d26481c0ca1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 833054919 1250 833053669 833053691
    0x60c190801152327041e150e0a0203010e01170a15020904150503070f0f26060103120207050109150c050321061206190c020106121212020c030412050f01 67
    0x8644c0b4280004600503450b01508580140720944e44844041c03074178481441006c40c2006095030150001d80640070721181030689030400240000400d0300c4240e8403503004001030284010340300440d40181102e080711410308011030580c9454440308a405042264441d540411000345501180c1008500130010004800c250911502c05611401401c0c083e1040c0c020100325110790000c45419218442507000b1000c0c5084500342d00003030050045058104080d403010484182003003000c1c041d41c072030f0f01980c18050341c003100203181c08802c4c3e000c181003111303c0320104143c3c680d03103248076010100703454504500c44250902c10320b14820001c0c13440d020b409c8135101040c0c48d100b1070300142c040c0c08100e6010410041c141b41c590740d5404142d45080d1940d40454540c6110003540c0d00140321404640004600340e59a040c012242d403c0202c01651084c40614000c991164826a0300c07040703500c107041c21420002c1c003024680c3c1d28016801650b55040f02c0310301c0241031000c20070842000b0031103000288072000c0e282c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 833056169 1250 833054919 833054947
    0xb030403021606020f12180613091109181503060703020c07090b010f0503100e01060503070305090f2e020f0405011403090c01031a03060c1908011523 66
    0x1000d04071807032020300d40b400f083c0144007240603d09644410000e00c118001848100e401c1d503c00a00760301040405114407495440d0440581519001400050551460400340109503412040710300d8581104012285403a5070f441100482c01d200e071030310895681e84003008140c42034600405107034503109003002c0019503030f4940c000f8101d895a10043d03550156450461500741d032964003072140031544001c115420035100340c01540d8031943d8540c542d004c059690342c0c05041c2c18020b80118000842c0041000324441e0140211a00640104001c0c0102e00860305043d40700c00b1840001c1542e1740b01031500e541c040800841e18001c054160788215582c803d0708030b00707580b0f07a8018070800340072511504022000b403090b6016a446140c052004d0442c003034056004500411040c070040ea074030005841c0c01030389a04c0070040f0510a18034a041d096403082c0f400b1180c107601032207556071420004a00c0043c4188500c2c00e110041e011344030305005140f00c24503a070440d001c00c1d840c813002041c0b42c00032030744888030060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 833057419 1250 833056169 833056183
    0xc1f030e160f0e0603030d020c1f05221a090c0405010806040507080a03080c0306010c08070c210c0e070504080a150f020306061c0f091505090106120602130b03040302 73
    0x800407481d41890fa0b450450303600d00001c80381c8a60540042c05000008030540d001400502c1781c000c00d8412031018000d0a0454060844d40d041d4201e548004009110050822842480e1500132103000c20b4100b0340c0c0c4404544100a0300e400407001c48001003038000e0010800c0074849140100b041c000b80d078485142e1070341c6100480d000c0e2160703c284400041d08410100c1c401084a400d03548100300c56840341000b814603400079000d64104250003500001141911015040b803078840c0040d02034036890406140c2004043c0320074441e040c1182005000006c409400360400c4944040f0111400d541d2550150759500955100010900505a00300104104442d628281440e81d5104000d5244590f03010b500301d020403650b558009400b002200002c0c014101400c41803191a003002c0b8480040d017040005550743c4c11411298803295004070402c400050285503030191010000f008040c2c80c0040000c120038903507030050001c40d40043c01d0b1016102603107203d405408510801c42d6079085c40d00c0c0027961642 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 833058669 1250 833057419 833057429
    0x105060a180918050c09190504030509091f0b04180902120f0715020705010921050d0c05010f0203060906090a0207020a03120f030b01020706141201120b01080c1f030e16 74
    0x10700401c17209500d0310a100c10b0182401e420341c120b4a00e4010b44031401450050016011300c2014000c080d00c41e500c08030000c0c4620405440c4c59808a18810101070900503174000c242e040c4d1003403000740003510101a9400c054141d03e240411003d40c0c83c00410503035550065101a140510010340340c84140000d111401c8912580c220510301070501c0089031950564050079000443c440c408020483c140e504280c11a0340c10a851150710410740d50b900e00d81050210310101103a0340d50f21071418404203120703521061018071002c3d0f2441c90300c60001016100e008280e2807050700101c0209100b0f0b042641a07403041c0d0340c007a0840150b242c60f41000042d40c448104101c00140142030000300345482802800c40c000e0303040e001010f215090110641e005003c040c00c0305d095100900c500465203013401d28840c003c140e40c00c02d8821810b602d0800c02d9441c20140c1120026a106804903403c98444d4901001002d180880b003808500044100320050304400703140c054280315801c074801001100d6a84c00c401c6903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 833059919 1250 833058669 833058673
    0x206070906051e030a1b020d0f0804080406260f060a05120a080306030f120903070b0c0613020a03061406040b0a060c0f030e030604060f0b06030105060a18091805 71
    0x80e50750142200c1c01c0c801c03142001074003c00b03500310828900341c40d4081d540180d031a0174049010354200c1030b0317002c20003000807054005038030800200500e0347d08189219a103000c1c51410020301c0c6440d40f10190503208501c1540100700e404800c45016004044110320280407048228041d4289440001c640c5d00040d03501c14481c04503a01c0001d498608500700050812006014000d19a4140c03103d20003500300178401d541501403580581c0030707440c05021142d10360490f1060b541c2c481c03066605141c03420000b03400c011680c44041111400101300082c01940c082c42003803115040020710307c04541d000000d640b00400d00e604140c1c034041c440c102c02651030f100302401d6404000443e0720303004224440c0110b110300b1020402c081c81071030208048034000d40503507020341001c9041420703a00219203031170812281519510350b42d035040d00750030596000f2040707030410880fa0a4210350424000070f46620400881500b4011040107615800d0f4a15860100810404204001c0b5155920303d2070f60b0780e0070941c800c50b524 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 833061169 1250 833059919 833059937
    0x18071706150d0209070807050c0d090905101211060d1a19120312230406061a220b16030e04050f0105090411091e1501020d030f110703020607 62
    0xb07050030065900440d07001440c12504e502c03140741c152a60b030b10283c881403c100c001c002c4601d080004200e065512141c035925100003514110800d000c650001d00806e41802500004005540001c07040c3e41500e07400ca04030003102c9400700c001401d203108124242c04d0807814654001c0c0c2c00112840c940b48007010580c1c0c6138440084801a80603911a40d02401c203803224000580070104e40b0a02c1c0c034601108042400042544200e004200350644001d09284000b55500420003003000a0140c0c2c3c0080c410385e8030322103403142481d00f030941c079010341d001c146802042c46900071030550b01e100c800002040300703019443d070315044a91014007442e0b0005050317020841e1114429554142031050b0f42c07240c0d4402204200c2642030404000b28040050020340d01180d401003401c020b580d98081a6016132111040c00700241c41880c14804850401002d0000b01c000e10400c01215903008911800c1c0310229117000280c0d061040c14100c0141810b030503c905959020540c2c0c001c1680000313100740a801951104110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 833062419 1250 833061169 833061211
    0x30e01021618090614040507180e06070c031704051606090b09060c0a0b010605040f0e04120e04092102060f101203030b040227010e010818071706 64
    0x54031074580301c0c050204200310b819824200b07581d400040082e119180c003154201c4180810108002c00395001e4a46802850041001030807441580c011005180410310000d0300185090b901c41c0001401e003028440310308041020540f10311941a201540300c04010342301d06160030b00d180c0c2e40c000f40d190404c4101d1558000b00f01c4a015000310741c120341c0c000001c140381c02042024009141c00541c403244c1e0610865034500c1c0000c0c01e83d040a4080e1201d940c40c0758649288c9402d00050301d089600a4a03051008401d02010a0040c01e20141c1007a6030304080c220301602d13001080c028401d4400141ca1070b14481c0d5110f40c0303103110250f452000310680e03003142c0050326400c0d580b8180900c252030100349050301302800c00900717200f15042401b0302c0c060704000800801c180c0124082e80c1c002d152001c0100340c0100c05370007091546440301903140080c070340f04140e8400c00c00003034034010300508a0a0341c10070414200d4109402040140040d090280c03612840e0001d01034015945c010036202c071400e0306040c50319006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 833063669 1250 833062419 833062453
    0xc061104080a02060d09120c03030605150304140709090506150102070e04030c1a0a150605030c120405190b010905010803070b01031103011b210b0a30030e0102 70
    0x1901d5942002d4001100640e0812040358800c0c0140c8000b20303250b40010000c030317400741c4c2036000121440e00d1f1403514040c81e140003000c41e03a0035080b00e8400e800958100002c500c204081e282d100b6409035202040c01e20341c2e2405464036219512940400e17003080304150030000003140d440c2c010071011a20707850400618006903240c0c1c14902600841c4054003000402091041031031540c1640100e11100c1001102e181040e00c1d10022280515429119a0b0288040050009110017004686491415410f0100b803c03022449003265520a99460310042824031106211399000090b030151407024040252605194100e024403600550610303280002642641c01300854005903070200314503040f42c2c01d40c0d4641c03080d4032203170004507095980d030398101000c11034040510903030f840142c45c0e0788200b03001101358440c42c004840118242a040c50800d03030190721010340030301c26121484407035107080601421029030010506a10700000d000404040d0505800108101414000b070303094841d9070b544409084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 833064919 1250 833063669 833063677
    0xa0b090105031507120633110c0f0a050402070b0414030c3703110f030403020307050d05120706051e040201120b0f0d0c0801230f07120c0c0611 63
    0x803c405181200003a0420310410041c1c9092481000016121351184030180c88441c444901281030010980301c600d000038034205003000ca010524014011034042c12049403240410f442560066903d025686290b0f5540e0000c840588000b030001c5481da0a0f905203628a004155401d4885041166019442c014048111900e080c1250018842c404150b10000103032406107002a0000b80582408164800907e22207800f081c000d0b0b403150407010040c841c40b4203207081d040d03886284e503204000401c0182c402250440445004507103401880c00c541c14600d090203500301c41d00c40200800210310082105030b0340181d0203003031081e4091010f0300b4151040034030160159000703404a0f88200c10140c1c40605a04846070040015160707082d0900c0307400124240c217100d244111400542100b05120100c001d00c5031240b04032310074540c2203100108103001c1c2d03080000030305102d842040f0b00340010104c5014a508554a0222600030860302e80407810090004590890858055007000d1213140c06070382403429a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 833066169 1250 833064919 833064943
    0xc0f0f03190c1e061b031506020706080c0f0f0406020706090614070219050d0f06050601050a05041404021c021903020c03040e131202070311030303161101090b0a0b09010503 76
    0xa411210b5081043c0c0480e10200f82201c0301c40c0c941078a100c41a00b00c2c009002c203001240c401080c040c10a660341100c40aa640228045602c900010005150300605850b0002404c040c415030311030503814424483c2c40b0751242c01503c8280040c000170342c10780c001a4501103400551310101806d460340000c9400ba00d00780c1140030b400a050004001500d02700000f102049000009016516a00c40103d0050810201c00307480525101a40c0801e0114034064550301030000d1814525186400c4405040c0740124000c0c1006655898441c140320740780c40c2d0403103440081003110072004020002e10400030750301c881d00104000c200c0c901d01c41c81550103802600c0020840c040a51304250402c803048404410042c40030729900c0c0c220302d8000100346514000740c1c00115940c0905009402c5007400d02000381d0720f08590b40650300801c200700003540c2d02d1040204820031850994664600450360b5400741c1184500075013209a060140411a40b80754003400030320b2400e8600007416a41c8004040e12230302154030b2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 833067419 1250 833066169 833066183
    0xf031106070903142109041506140309070302060d020a0f02070503031803032107020f0c0d0f05151906050409050a17040314071805060d03050c0f0f03190c 68
    0x42800003a4203884880050048041221200314080036541604e9005d80502c0070b14602c001140840d81c14240106199100c05200009403c1d140c6032004118400c400100200d000c0040041818510180200380c0150b80052104e501d440d0b200740010020762101081d0300118070440302d840c000d640042850b00072594000e01544c202800415021b980c00695030600b0b41c5070104100f815a50303003001d20541d1507008071850401080ca02014003900c0d095030f800e0b030092a5403002c0c0c0c000c0c101da503e5458018405074420384010482441e0300e02030f40341110486041c0c102001d04010400340302c42581a090507a0348144060040381e69401c01d200c101d0309200405005070704003410281c08034410410390f5200101300d600c810f00d080e54a84903c04031200300c030b118a00ca0307040380780d00300705031092000798580c0c0c65511801045203007408800980c550607031900040a04c031011804000314081408641030160110f41a035448084a51070305840758030405e0604030b8540e500c40d06503c1786102d5031040316030303a0344284 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 833068669 1250 833067419 833067437
    0x50405100e07021603081801020619020d06031e062007080f0c0a0305130f050f042403060504020a0e0f070e0d02040c0c15151707030f0f03110607 64
    0x40c40440c041c1c4002c2111007035109030f800f2244aa0300a03140000114000c2c004261101c880400e40d01c0c03102e26581c003140c11503204400740036a4504013940000d88140305000180d580c1c41c240035903809002c9582c00a4590300b54a00d280540100d1b488040c0d44051040d241003050110718003035a02c041f81c412141000089040c041c200c00902c404d0001c10b80c0d1410b902c9514186008800580d20301401004200c0000b4404100745200c00d42c17001c1104080c00380200c51940c6c240c100000304601c1401806901d11039510b841805c8880c20340c0700c42c03040d4000400800c100178980c0340c0c2844c4000d4201035400b24001c58504000151001c1c0e4075070545d000388200300c2c0800c156103803c0000c94046c0920072180c0d5200501002c020700503991031050b01c40c040c1c0e00c1e49503141038103042d08044844035094240c0720b40d154140750210b580c0d41041c11080e000d40b907090319510040c0220095851506265400007881591903028076401d1041661846c00c405d4842c0c0e95040760405a510400c0c0ca500043da1718802080c0426 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 833069919 1250 833068669 833068679
    0xf050a0b09100b09191a1c1a090a090b09070518160f020c0604181505030d051303082d251a0c0d0b12060609040c030807120905040510 59
    0x2c1c401c0107540e1170061a00b066648a07800c0040d640518a0420020390700000c4aa185001c010b65400c04011010740c10848c0242c1c20061309007040308108646d128090600c006803010303640da4840503140f80c00510700505450040d140547c2d400c010302807135104003440e0080c12400c900385803120384540c01d5080300316406c034880230082d1030101d011420740040d030181080f0b44580e0384803200500010004c045d145001c00010020800441c0d00300d01c60361b04046010705050266880000341c050380982d551401d1591074140a141d9060141c0a81008204100001d5a50740c500507408558200c81c1a0081a40c070f9203404180028840c07040d1400c41c1903400800d540030800105500400c1541e130f000e4608280c0c040a149008813022000b1a045807082070003042002c00c007212441000c0361a08169110b41030141c0c4010a01d0b51024010070140c4201507507030004040140d00283e0341d000f1640b011009440344210300e00003204000701d592a00004000100006aa1034107015840c0208001001026014108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 833071169 1250 833069919 833069929
    0x90411180603070c0503130f0815011707050307030803070e12210d14090f0a050709021b0d020102030105011206120b102d0f060206010b0d0f050a0b09100b09 69
    0xf03101d4801d200400030141c3c00316206000a02ca9030503000f8074801014180f001c50094940c0c181c22060f020760225080e400719003944008641510340b2a0500702400c40207600302403504000b0340042c0c2c0c2500941000004000c41800039500440007500d034280c1851a22003130200d0791107081030a1071f4581c001055125840100c4120a207a20200d4510034609600070310f101083e2000302d106080c580c00481d0402c604200c1c1030080701800301010010380040cae2080d80794259a00040e002e0030031110f5000544212030b01c6941101c5288070850815901c0c48240c40b64041d0003034209104141c0483d21100303e2510003c118071807074095515000701c90614108503140d0342074400c030040c032404060294403404038403214030070b86400051070710380613076400100c03209540d000103292a80304c0c15001c1080d50003071203502e07004205141036070b04500e10303681c52301d0305c044071900584000420403c0030361800081c01030503180b98000d010b9000d016900403c03c0e454004601d03040701800d208420601d9000d004c0000c061800c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 833072419 1250 833071169 833071171
    0xc070e061008090325021002011503060b060c071502010b0117040b0402040b0a0f17010c0206070503130b072a0503090d05070f060e03070f1202060708130902090411180603 75
    0x15030840341031101404512901d84c200c0c5c00b2030710000c890070328000114542010101000b54941c070003800700c03400d40701103c51814105e00008040640715032003982503403034503815a001450104c0c2100d20701d42e5281c4515420340c2030817402d400154200039088125501401c80024200c803441907680e0740d607890340c031105031000010b08100e9100b91150240c00c40ca94515800601819404074040001c80c500769110043c1d0160300035210346641000302040c1a1a0040782980e4064220b00702203542c0c2d55403402c00c11520303a43c0c910080c6101808400d01c00d110303600a040c00c0c1d8a00d004004a22440f013800c0318980c050048590003081c45e40104480117190400d40e0f10340c4a582d01c101c00329107450f5201d600c104070551054000d01c0004510b4200d43c0c01928040203403d00910380d122004900714205128907040e50030841d00039001e00c1c0b0000340341c1c040028280c21a001440f0550300304840984842180c1c0103503110b003820038421824010000c0034038010701e00b28ae902c403418244500074000c2c2c00d42480482c0e00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 833073669 1250 833072419 833072431
    0xb2704030e030a021504090f09120c1a011e06050309100c030e06010803030406151401031e15030b090c010206060d02030120030124020d0c0c050310020c070e061008 72
    0x344081400161211241c0117a9003071071705480391301d59040c000401c040b10403104a00040e02d092580d200042155444008507031090b51a00443d0419181031014502040c448022280f640203800043c203410780510a0607010000034240b801240ea51804850300d0000340e88007411030304401d466050101c1513030b00c1030303123694044d040114038840307040c0c10282009401d078003c5215400010410042010511840e030075180800740380d03080142068200148045284030b400c6c1859501d20400248158115414001c0e050f240c0d424860240d040b00301802c0400140f208644841c0180c020071a400300124407100d5206041e4000d240c20703034940041080d2628020400c0e03806547c0c9101c0d500d0700c05861048491f5801e02a5440350396549440c02c20300c8201d00240c410b0001386607d2960f50300c2c2c1580450b41002c15000380c07501d610041410b09001d10040183ea02440d418030503c84000071003444c4d1740140128101c20701c1982d060581c2c0340ca110030b400d40c0c01c0f0340f1141c1c020340c0c541c442d079201c0d070044440030381140c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 833074919 1250 833073669 833073673
    0x1f060e031509190311060c0a0906030225030c03110118020114071a04030f02010510050f180901090c0510050301061107080a03030b030d0c02060d11070501050a0b2704030e03 76
    0xa0303d2000015229200042680050f011480a00302820100282e07500100d82400c03a83c605071706130b00300821403022401101c08050b0005207100003408140c2a04038941e08070f07807041017102d810340b401400105000008a000c91641e081668054006100301c9100b142c41d0900070f00ea03465581d00444800d0311f2500f84050b00c0c00c0a105020118641d140a1114882c41e0440c200e001c6c180750030050000d90320a401102160f040070304000c00034540c4103001049907005e880303442c04400d507400010b004103065505510b10704084400c01001b20b505420141c40302d8020070b114070385141c84000384078002603e2034412001c40e030300300010400c55206100010510b00b52100340e4064540700d2a0311400c140400005500080e211602c1c45076918052000100240c400d00707250016001d84d0740811094022100b506816607503840710043c0b2030b58190101e6020f01c0d80500200580d280c810b00b032400800004030701c540245509103946200416000d242080a06101e200221954981d601114483d03801d2030b62035014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 833076169 1250 833074919 833074933
    0x41e140f150105070b090d08180c01080a140c030a06080c060a1b0512120703020a12020901020f03070f060b100203030c1b0d0908010c0e0a0b030c0f031f060e031509 72
    0x2141003501c0c03146c09244940c000e0081e030f1948201c000c00443c0c0142511407852400c0c101c0c0d0a071651300245001c2c1d140d04c00c2c20204070030f41c0c4c0e5510b524002e006100c5403d0b10018041d00700300418440b140110b2094070421004c01415449061036543d40c0064007606030000c10812050303504038020012920001703c11000007c0d00105581c440f8100380c0c20328820f0720084004a44801d000d65406505030784141d032407400314100004020001d0890240c03983c8018900d5000590340c403141d10910000841400540860390345004a1804400600040b0307016265189400c4000c941490071900f081d500146a500031030941d2110f41c00b0a00343c0d440716440030a0880c1106606258910074080e48400c0c0485840b0101114038041240c1d0035200c0c41800d1008000110a0101d180c1d41e8a82186007581c1c0c1500c61551030b0742c0c1d48920a805882041ca003400000c41c04401c000740300b01043c1207032035501e00d0000c03ca00c4103907a8007004d8441249500c04940d268001c01941c18941e82030f1003d00c0e902c103803008116104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 833077419 1250 833076169 833076173
    0x80a0809150f0c150a0507171b0a05090a08010e03040608090a06060905040c08010b0612150415031b060519020c06180414071e020c041e140f15010507 66
    0x1c5a200c403c0704903064100c102c21a51400d0344401055101c040305c90240100d2601d840020b0480107600342301090150b034240840e8103c0550a20501c503880c2048025944a10303d64028100b50045080103110315a41c510200c0c00c610180903591411008600544c180b5080c80010745580ca0010704c0614548039040030040402c80d46d01078200200341d03201c0005802c0c1014205403243c007d03103403c180100c0e03040c2005010f03603440b07a2085031b00c43e02101e40a803c0036112481c90348100c401241032540e00600307000841d0803503040c1054030310440e445600701110407c40c4001800c1003413164484c1c04d010510070b000c0d16015001c1100b01118042d0148166400884500006100c5401141400c3c0d00448a41c40c3d00075a4181071292101b010f4070000d9580c0c0078a01500000d00b003010b01902040f01ca00c1014801040d1070080010140440000b00244081d030114640d4054010b000c3d00010282403c041c5207116200c0381d408a89d005200034251a4041d41c2c0d1369120480b2083d0b48082181080720812030200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 833078669 1250 833077419 833077447
    0x60c060e010207060603110d0b150d05060405160f0609140102101a030d1112130f03080d05070c02010c0305130b1803061605180a0e0916080a080915 65
    0xf030310500c80c5100003101ca0a5080c010f28410001980328040c1075203244e00e001150f45070b0b141c0c035400380d2525001c840280c4071101141d0a0a51035100401900c0307124140400c2140119200e40c101c4024200c2c0300f01b07142c2d070340032413502400c003403240740041a001c02050003110a840403400740d048040c0121000d4802560407401294001c0c0341c2003802d2066034036040b403946000e200420022101345410003c00d03108506407030311401041040d040c0ca44000a0f989a060112640e90b40141034807081040001d51302d0621220550001586a00051808001031217850183c452061240e40613920b034030716040595800d03900e551200e0384034402070017602c10006404034040010109480c2d01e2549243c1400c0c1c20050500e0020090203ca11000b4846100d125869100040d5100b00c0302c0c1c003d03507106503078100d80412450500c1d5041140090032400c2041070400b000203008a1034814401e14225069481d40205d88500f80042c0040650310300304401c485524100d2010009406061580c614003010080c00300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 833079919 1250 833078669 833078677
    0x60207080309010b010e15090d0501060503100e07050405011206050403140a0c0c141507020d021215010503060601090b0c010b030a0b010e0105090c2d03180c030313060c060e0102 78
    0x42d25a440c0c4803814403e5038003031110807070800140c030b508084250000707034070a1398001d05c0d480d01e01074036004042100b4800d007500020300a00c405025107072078407002681344000e007000c3c903011000c920400c00001020f041030300c0f43c18103c41840c01f11055040081e0b0302e03c0e000c0c040c060000d90400c125a820400500607040041c62031900a4803200e400040074070f81002c240c062a0b00a00080e00f441280950307a4442e420b40400700c50031503008640e1040e81d031002440c00070000d4006500501c0700e06400750520ba0010f00c020301100c00e180301c0e00c0542c0e42d85d010140c2e90311084504a00055607100e00700416222900903240e400b22000020449420280c0442d280c070128010039207010400d1001000041c2d2180b100901520303007a03503440c10034500300003602598402c3c031601c0e50784890860902c40c440b27107907081c01d28511a00c82051940e241000d0072641740650f00808038841d1800341580c640d03424640001100c8044269007503104a0310b20709002907941020441007560040c0d01c920700758651010030310042c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 833081169 1250 833079919 833079931
    0x3050a0c051e06150a0b0d2003060f040b060904020901140d0618110a080601120e030d0b09040f11010519120c0f09180902061303030e09160c0602070803 67
    0x1a60b40000d00071052601d403001d08409040d20b030707540302180c154031085110010380709014a82c42d40c07498505202c0005001ca481b082e00148014404144540ea02030011030240300700301d5028610000c03620402080310200102c440c0e0001013007181784200d04094000c0c0000e02814146551902c0070841c111100c0c0e4064001c424100c0d90b950400d00890001c1d8109010040c84a5010807440341c118583c0b014078800c009002c030900c0031050001d074603a031140e001038100c070b003c0081c1440b50015000d001a45c076084488203000c01ca06100e4440034a09200869074800c60700074500400b03001d090344411a2558000341c00300d041200412031301d18800601011800d0000392581d90303000c0300c7c09528100c021a4260300d00340c002c219a83d00846192584008c0c1c0038140c83d1000001840005c14040300c500401c4d9103131000f03400500201c0c41c00c86101000d454082100c1c02a102c04400c1c1c409441040a0b15104a40c5032000740d80c0c0314a00407240340f0030700684400a200c0c0000501c0c15a850f240c80b100c0703030021160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 833082419 1250 833081169 833081203
    0xc040b0f030a060807030305070204110c030c0a0507080d092c0702060a06140d060c02030408010e060f011205330a3309331a040308030403050a0c05 65
    0x30b00012a04034414a4010076441c00906606400c6d41e40003080c2c1d01c1001c0b8040e104680740c0e4a9000094041000c5603d03180d44001141da84441c01d11000f80c40e02250b42050380e0900075004000b0301586c0124982e05540c0d0a42d40d21503181382080c3c40da00444111000f500460094003411000340c19500050501a0120342c00900c101e16210813807038107459140e0004c458500d46000c022030741d030712600701221003240e018030089800d0b401d00c3c108a180d4003883e80844a10b600707041f003208030041d010401501031849a80002c10300c1c0e8803508101035100c07803220024490340c0107048015802660b41e0b00307001942212030443d0b525840045825907284010750b41c1da0b01e41540c0754103035070204042c000210381049043d0007081d540072415031001982d20b200e00c25020344580302c88031f0700e0f030400c5600c3e1048241080080390082c2100312110300d00c210034150103a201e002c807009100b840d8000c0d840742641c089035030100c401450b541d45c956003207903142c02080d4080248884d0b0b801040c00950140511841c080c01c41c0c2c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 833083669 1250 833082419 833082421
    0xc0c0315090607030603030e0120060c07140105090c15130b0d0b010c02030613080c1608060901090b01030303020912010c11010f0b0904030e06130f14010f0f03050c040b0f03 76
    0x218076410304101401d0242850300d001d00c00c1001a401c01c080d0b00c1001000d080600c4110881d804c1c0b46082c148204068455010b20300402c081e0b03801d010042c0c407400c2d002d8440e41c00d149a01650a03400c1b220280c40f124050b902004044c4024a045414611a4070b145042207040400c030203c0303030303a15a06079006010700744004a1084845205881950302e140c40074604013101c1003150b00800c0e210600a00044030f0740c52a15090400e000390f6200315010800304038100e941e5000c000166034610101402410443c0c06441c012500742c110500400d698190012100c1e040d80c0d1965900360000d41c030201e1080d030041c40000d001d00100030b00307101304440b0f80c03496212840e403868003907211070842e15005480380d00c40b03203040f800002e29200e101320f090740305500d81481116400326500040b0280104500c1c0e440070040d002020502c0601c1c11a1301c8d0484260000b501d003800010001507549060022a150001d2020424414070314400e400407904100c1002c03400d464039032100c54140d4640d1114682d1410340300008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 833084919 1250 833083669 833083681
    0x20307020304090513030804060b030102041206020c06061f0e04060915090f0e070e09030f0403141c1b02010306090e1e0f03030f10050d0308100602030f0a03020c0c0315 74
    0x102071682e1000741130940b2503040755175039800340c1070030070160024000b40e5032100c24418070b0b182503044501030540e60001c41c1c1d0102e607d00d42080a58001410300d1403078096540442c4150600c1d1000030084610000c5226080308006030032203540340801c43d00c84e8016159275000803801d209100d4000300214091206207000d04000c18072069501080d0491102e500d444294940400d010950758282c510515000d035aa4881c41001490740c0a002e80038074601c140003800004228001101c0c2c0c151f0692901968418406140c034011a82941140f00010500c0102101449000d104014a0a40c8141000200705455000000440d80b43c1e8214005a520903070868aa00c1c152a010170300300603180e0001c0041d01c0003103288513164003001d0100c3c11121040300c081201d20540c00601d078050003000c0c080c010125503a08006088110a40c5d0380e400e041100800071813210310201c100c9011003000d490f41890461400b00840007548003000c4c01c0707000d014980901d01d40b40d070140490705241c8180344400003142046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 833086169 1250 833084919 833084921
    0xb07020106050f01020c09101a0712050306011b02120709060e100f12080c0d0509040f06060e010c06020c100203040318060e1c1719080405060609100902030702030409 73
    0x250081d6200d018851848843c582e030018403610721000030368510040e900c51344d0030151110202e412042a8a10900120184030000703c060b14000780a00c0380e4003000d00841030207980350b200940c2c415000035414945850b40c03400d90003c0811841c400791208155501c2104054205031700c0d90020701d042c64a0341c0c030400c503003c1c0b8040c0f0310b0340026402d08032141d2146409502c4e010b80b090741c890001152090203240b018407140400360340044090700150340c01a11501c000804c0c0d5446000050300c107601c5d103441e00c0356110b080d200b0003094034502c0e245d1140c0b01c03601c0d8005403100d03002c0400071191260204040c00c082d60040c0045101c3d0b6803014005603c9041520700a0072110003002c04c030300c50f403111280410005901102c400d0005000791000004007070000040c460900b200706016000004440d9000e14000c013840c0200030301101540781c0c440344417408000312418032081e140075140c2d902041c081500c40c5070101d04242c10008213240c00001a90390001141642c200300c4642001d0703000403504000800003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 833087419 1250 833086169 833086181
    0x1b150b0a05062505070e060a2c130f0b0105091608070f050405040213032307030212010b100c0c0914240d080403062307050310120b070201 61
    0x10850388420020708040120b8028000c200000c00c14890083d07910f41a070702000d0400f1902d58101d026564016200c80d026040700409683c0c0382d000350541d950004000400000747d000300d03104180c81c2007202c00e911052601e007240103003003043c44181701501030300040c6185891103200752245c0d0b0400b80315803422007000006039000b0801c0161143c603410060000d03a20000e4542d00c906213040001180c000d2800440311405103420241d001031001600d0380b0085440e4008000300c034498100080d60000301c0b28071802004594407000919030008400f8801031419110001480c0c0ca020000038074014500b00203a201103d04090031b0104903524042420301203403000d40b4010303200d142020710912003000c10401600390024040c42504020001400c0403003101c3c00c04c00d0414500511800c8803421a00300000183d01c41d00c411142c0d01e00e00294041d4404a15002ca1600e109d501c0c0542c10390b80d40e61340d045d03a0316480140802c218840c030000c00306056040750b00d920b10140c0501044185880c141034007a0031034074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 833088669 1250 833087419 833087441
    0xf030c0302072304420905041b05010203090f2b0f0b09070515070215031906120f03110a06020301241106010b0d0f0f0c1d1804031b15 59
    0x2070241702c40b00c004203c40c3d0a0090380d03e42007034800c5174503032412040c0603111907070300314059141c10181404140254440d0203804554444c411038030f0780340e481005903520300c1084200383e007240b542a0038a21a2405201c11701400c18078400a01c90b20800c800c1c1c140c1d20001010003181c501803140400c07004d00403003101c25980280420010044c090426001542c5010200c40002d000c05000440b034086440c0c518030070240540c00b1101036142d04100000380280c08003003440801e414504100005e9001110b44540c3c0fa00d0703002040681960302d5505c04036981114540e15000602c0b40e544c00d42c1c00501e44d44000c40c0201400d14007007101100301c214400d0512406445442002404501d00c5140c0d1004102c950454050805027940c6000895264004e40039001c0146031081c60303d03400385d14090302900250008001c96856a205100c10040e00010303005032450b01e90000141b16044003044503000301c181d001130090624a18601c40910b61640b409444c00c0c08403000000040d000804416a0250003072800e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 833089919 1250 833088669 833088701
    0x1503061b05041211010516030306050f1f0507141603020406080c030c043908070f09051c050619060b160605070306080312090c09040f030c0302072304 66
    0x51410651221040480c60f01500500403d80d4501080e03000340103d54000745041000400603203903003005030082240d841098022080c010300b02000d07140484012100c581c0310302c1010203c51441034115401d40014004850080c41c01031510b00040b810403035400302a41c2036001780c1c041821b40c41400195162035008014660144814400c165070110348079902040c00c2d00e0000d42c80240352041c5540c4204480c02d90b09d071b220b08451916249015501c842c010300c000351074403041390b20750b5802100c035031040000300b000040b8044814000380c507011002c0c241410300607045115008041e15441c0c113000d029a00f002c80840c034070940d20381c1c1409070f0060b88010100108214140399a21404003203202041100514040da81c0e40020391240c0641e008001030f000641c112031700c40d405a051100e0f014803c1d00d48403494800c0120b408442e00d80341e1000d51050b0b43c03000c11440c940700c0f26074080d60200d02c40d01086040d03009126000c18440300d00d000c0020007485041d00303115204101e0301800101c0b24000c1040c52070f5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 833091169 1250 833089919 833089927
    0x30901120903021924060515030601021c0207090e06060a08013b0a150e1b010f120e030a17040309120311011802040c090e0109020a02011503061b05 65
    0x20a8012903034912040f80f100f41803c03c20207174a4010702d045502a0b440e00100750400300034040400300d6104509440007aa40e494460750100c41d040c071540030460308540164420885002001d010760f106510421150045401190700c4240c0c007800c0d10170400c0c0c0111a54482003c1002524007842424018181c031030003084030002c2424060361440c0d2800414007103043c40325a00303601c01884e032402514200c0e500300745c84d44002186002503c2c610501442c42d129820032040e0804c810002c601e1000ca40d0320581c030201140a03800054030810640c428000911102141c2c0c80700c400624007401003213601041c0955903401c0b01c40000b40c4000c06a1604555035906034041000182d04082c010707090346c403810441e040c25005480c04840c5a01d08000c3c1807190f50810005100380406001104400c40c402c1314248521204184c044607a6101031003241c000100c5c0c80010000f4101d60740c000e112180c8a88001300d010f0f50040c4515000d2100d0790700440c1d0481d130742c03040c0b126808604040c04450107840c0c80c000b860 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 833092419 1250 833091169 833091173
    0xa0c061e09060504090b180708011d2404020d0905031b0c0a172811040c020604081b1e0705190509060a1e0602010516050414030c030307050309011209 66
    0x20f10700590003501241e03a69011100301950314040d48038240130000c1402c0d0054034002e0743c0140628401c0c4a100801c0c40748a0410611801540c8403603c120040300c103103030510690019070120300d01c0d409080e0fa0041e5003001b91010802142c05100e0407079001c1e100840c3d540c551650040b040b4190101080d280d41c2001101121070342d0380495100856000f540d03c042c80c0000c0c1c0b11014100f503400c6002a6000d0450703c0320500d104001c1401966035805420307071400303205003a010300003a540741c00c0082c0010303040540028009810b40018041000030700c1442d06110031000041468180c425400c001445803040200040001c01c21182014181c06d60728402800074210f0f15400c0710b0054000e40c0c0c40344984d840025081c1d2650f2513030740c000f05006084803507884210540121540d4860103004015401d00c0c0000d4021450080f0342e2101c07114582c1c605250030f25104407084043e0380c0390a02a0f150180000041c42d5540410250078554040c0001d1542c0b82c00b43d400241580250001d07081003103040c2020500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 833093525 1106 833092419 833092427
    0xc0c070e2e0609050108060913050309030d08061f050304060c0315031202010c02120d0e0f01150e070801180b01030f23010504050c0405060c0a0c061e0906 68
    0xf421070f2a030004444421046811941012070352000c0f0305044560740d58100660b0003002a00c2c100038074007001908049400c0c05140004203400140610707440d02a481041070000818101625603000703101070624000200050300c0f40350783c0c498905d441e0780680c1140d078028007110141c0042e15240d16085103842c01eaa80d42000543c43d005d003048400c3d0001404a05c45050310703010508054008180d08090089017515441c81e020319400091509000d000b0b0f442045034080c0c4d141e46082c20180c07008405c00c0d00500c000208070040c001000384030311a079500500b0740103070140401e04400500058010b00402040c40040c1c40c0350030405146442e58032000760540914540300d0300c03240d82c0ca10800c001e846041c0c40c071000a460400040000380740400090021134440307019a4540b15490711105401452640541d003c50944454030350505c00b041522020040c082c180688005e0070984020 = true := by decide +kernel

theorem cover : BRFrame.Cov 832913669 833093525 := by
  have h0 := BRFrame.cov_init 832913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 832913669 ≤ n) (h2 : n < 833093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
