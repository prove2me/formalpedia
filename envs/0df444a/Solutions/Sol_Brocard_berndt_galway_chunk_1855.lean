-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1855
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:55:13.512726+00:00
-- url     : https://prove2.me/submissions/b76964be-79d0-47e8-b626-a9acd39ba276

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 333453237 ≤ n < 333633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 333454487 1250 333453237 333453271
    0xa0e060f10030828111b190909051b2419020c0307090c120506040906050c07060b0105090d0b0601030b06040609210f02061b0a060e0f0601030803 64
    0xc1c2030601c0c6009550020040381c0c549051070104100c24605a20103100c078241c01d11640509031060302c00032108200078014000c200c03a00d8006106080e0381d0860ba075800004000c1c0396009180310360198005008a0a0210356488942403039410400e101d07682d640448090b144011f07464440e52000399000c01c5111050641b500c088000443ca40900382450848118858210455a500043d512281a0200c0a42c2d0400d40c2e03c480c0c1c4012959101800004294070480c511a81da034207070710145e84881c01610104e015106aa0351404941040301d44403403a85c0040740d000b09100680c800c100e10408203080c400d1070250381d04005080c44014920041c040b503078038400038003d40d100713400c9803017415005050a42c071130340c85410182c400e41440c05644403406c0404141c81c0c03c41e1132104800c404a4019200315255400c580030f0051036440201c2182000c9065842d185250804011864016001d61000650743d489051814100003c1440d8500603900407030060020507500c8084940000b0015040300c040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 333455737 1250 333454487 333454501
    0xe010e0c070f0f2901140f04061208030f070819180b0403031b031e0c0522140301020a1d03070806010e0105040e03130303050703030e0102031e0a0e060f 67
    0xb8196040b0010700b50721907441d540003000048015215151141d0840d980044103803403110b000904c0920840480b80a25000308440b418a040b030b0799620300c4040d00c0410226290513010500410144042714603800000070407241007a0110219003211031490500407906119651071080c840d0080300c000c50907540d000706070022504103030b560f2140703a028002c0c1900345040d0a0250040c940041520402c000064841280511034803454484001130812002e00c07061120311344004040c031450f614103108003042107600000c0e0100442c3c840360610b940c8640310b0707400e00800d80050110641424043c1c0e00500441d041707a50001c4003940721804e00d20100c48079140d0840000c1c035100c183c0d80b01c52014012080041060f2407001c05490681e2801c0e90280840c5544822071980d9210315174041000351b4820f072060001a10880050803d14000d140116003140413400c03160890f40148e50310720100f030100c81c1e0301d0801c0c9828005030764088102801044070101100860b40c0f1030703034024560994995424002042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 333456987 1250 333455737 333455753
    0xc150b0d02040507030c0806040c0816020c0607081806040b1210150e1002060c1803010b040e030703200a03111509060411040c0905100909020c0307020a0e010e0c07 72
    0x603664005005100c28100401c002e4001c21040d000d072000100c69400044441c1414041c440c5102802c3c2c3e0381c180140e841441c0c0d4202c024403215114114006ca0042402d0b65032a00b0103000b8850282600554500e90303042c015010b0a8021340090149509020400124011700c0c10b82d021080c503452104030598402e240c81d08031005a4105044070361400e030f20701203641d5104003200106d104c01c0e201611100001c80090742d68840450307000030801c81c10030130103402e107644240c01e0a006802900208049200c2d0340094103607034401811054030b82c00420880141a4400b812010a031004141c4a010880505650340c0b03902e580301019040c88a02c00040301d04200404c003800d075820f584403012150b400c182004607201e03241038400342da90301c10743c100030800742c034143c8135665400b01c481e212829694905824840e1001004503c042804440c9c400007541d130f0032a00061142004100240d83d07540e00e580304101c442c2c03e4070f030881c500ea0003401c801400290443d03440e154024040700c3c100c50704e0385440c0c502040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 333458237 1250 333456987 333457009
    0x50f060d1401090e0c0d020603041b0b071a10030c0b13030602040803090909060717060111060403030b01091208122d0106030c180311150c0703020102010c0c150b 71
    0x1656181081c000a0152416401815050024025925007144a0f420000305030740c10040650b10000400100c2c000401408604166450070f101c1c0300030003941c0c3c102da60901d0304112010340e800c52850041c11844500c4041c039651000a2014402845095440304110800c0c24022503c0000380004c2000200340d44500c100d000b5030f4850070541d5282c0c4c54481068882d0050080c1a01030700120001c541805400b01c2c4540c802c41e82e035a1140d60084481a1010300c1c010040d040c2410301c2000c1151280b01721060042904c10790181e1070201e106200d600004080070b1103984400d00520041180d4400112124101c0d081480b00c4a0f006040381c4034190000c1070241824040030076520500440d42d058035840090604a52490302c08103d0101810002c0d99100001c0408890920050341c080c030014801610903480c19101404a401c4805c00007501074203035200c084501c0e01d40d401214200f0456031309001d482d142c1400c500d0305900202ca1a56869034207580d4480125542e92501e40101042c0c6820744c01d80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 333459487 1250 333458237 333458261
    0x1505030a060b03070b1204020402030601030902180609131a1012120323130326060a1508010e150402040e0406110f1818010b03010f0807050f060d 64
    0x40e0a1040c9894148014011031091900078001d0b20360000d038410754031060703880c1c03031428407603505d484c2e580e60342088001c0d03200601c21414142d44e040982c025840c0c446901e01d49162041c49000503052490400201010007043c4144c035079885691400001c1022312010102c40d02030a00c2c3c012612070b07544e0103008510680181d0340f40b4201091f410140006610f41800028941c1c901300622007404e8100c0c2400c082c421051840380d0f4803040400d130510b850740340c0c0714101c5010f8a0704080c1c85110780d060410962052441c1010180c0080900200346403080741c031f0005201c0e450120055019031100a444802c1c14414044400c0c03e010024281a10074040703940850350080003155519200d80f40004001000e4800741d0b5403624110403036550180b00c4040320380384c00c004504d05003010644040d015008400d0360945070880b440382032a00450b800c5182e03a034080d0201c0740b42c240c4c60f5810b1102c00007032208a03038072500240e84404810449501c0b418107101d14001e00b660482e940b80300d11800314016200fa00c8840c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 333460737 1250 333459487 333459493
    0x30303070c0c050a1d060f060d0c11010209011e11011103010e06010c05070909030c020306071e090608010e090a150c020d03020f040501030203190c0e0a05030d090504150503 76
    0x4115280d00c0052180701501c0390950020141d02c074000c1c08006072039030280b801c900d8080d80b5810101500c2e8200c10b07500c0789009111408149000e404107116401040d0800c3c0c0d03180e181c008141c0342d41e802540140c02102c064008604106504000038902001d0440640065640796105540d0364840c822100f0300c0321401c0700038000d0345100140070000e40e000340714114030250345001040956114070303a41c00c5d0b0240c0102c000c0011508011410f001010140812410f0000440c0084016102408814452286a1150b8071503484c801c1124a00d4003600c82003030100000d600c814000143c02c440914155280f00030030165694411400c1031600e4075607030700030f0100c18419034001140340c83ca400250610302a90300b0382c0ca41c001078202c1901a405007011401040034244000d010701c0d4400e0740919032141c12200c076480d0f401a003040b0001160845901d440024050550001c91800c1c901039100003028150014610451420740080105403a4080d06120703039101c10100000350800703000030024080080903 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 333461987 1250 333460737 333460741
    0x60203040f021005190e060715090b06060708040e0c0f030a0b0109050105070816051207030905041d100b040b19180b0d03030906090b0a050f09030c030702060c010b030303 75
    0x34140740d1480404a118a802c0c1003042c0c40f0b54840c00c280c0e840003542c0c686156003103079103460943c1c02a4020070079942001c0140b0007440441c1015507040074105400c000007400d10344600704800007600052580b030140e802005004000b070803c104960844010900f0b02403a0b803901000c0300300a2140112900003203801005111400045502a4040c51402d8840c9150242d492005403035501030440d0280001d00300b440b29540160186000401c0ea82c842c0081e40c000c042811b0384000950020081034001502c008030a00850a0a1103403140188108d5000e00b54805503058a91365410454014442113480381c55503140303a02c075500010800300c030060a1380c00c1c00e182c58114581b40a805d118403801d0980300c10043c1051122807003000441e00d0302800e111070020240c0c13415030141c4016442210303100d58a001c2080800c10000c900c501941d000b00c0080f038141460084541020009002c200480d0020081000c00000001c01c6841c0310740d0540c2c407192500d040006045c010072012001540602000003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 333463237 1250 333461987 333461993
    0x90b03070507082106090c310602060f10050f04200309460f0501020f07051c020c0d0213090605181605041a03120c010b01170c0c0a06020304 62
    0x40050381c42558200b00311042c1c3e6505d4204509560207030340401c1800000c10200c85907100090240e00403601e2a00e6040c050f01e01840c0041c41340051713620600042e0044800e12100c1d1019114580d041540c9022801e951070a020018510211080f47c6a00c42d40c0c3e258030f104d20070300954403d01e030340c0003840b40b01c1d13030700c0b40f40107003020b074480707070286040c005000c98059114000c030100603c24404440300039030138443c2d40000c0c402c2c0701c07511049101075a80c80d5030b0418400000e40709000030b01c0351540d008071190b190700607464107618005400b41d071341740e0b5500d80200c149000c0364000b0355119141002c903032031a81001140041081e03041141d0a0103040ba043c118004140403258003c14021035a100c007644045102a80854039025000010784002c440100c0c1040300d07152641152200200e020342c1ca100b40801000001d107010000c22218801d000c01040314094a0300a00c42da907050708083c20a1844a10b8403079850480f002c0041000821900c007166411040d00e08010001c0115800340c0c0c11591f90034581 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 333464487 1250 333463237 333463267
    0x180d030e0102010b150d050c0f03010f15050a080a020a030b0307030803101a070b180a050604020306011d0a11130f03060b0a0302090402040f110d0e010c0302040501090b0307050708 79
    0xc00d0241c0950308080710440d032410070040d90744c0103030b11005c000f40c24080002c043c080984405081800f07a07403014801481544000d1000318003c5c04107a2000c811030340390002d81403408490a0100701448402d021051980341c0284009901c180800001a80c0343c134004030580003004a502810380501c10121301200700241c0700020340c01001610800c40000c0d40c3c0e403164140c40e4407503c8000350414001c0c483c040004500d4a2450b401802c0025038240389160640c84506e40f071348030b500a0351650b21280070310007541030a000403070152010b0010055030307501d07140e40d030000c020001d813610b00c0b410f558a180c0c042889040054400041e08120200038032070792607011007489003480c0001c3e20100d10304962500186800c8403e5811280c1c0038100900b0303603565800308801003041c0480034420580f03031006100321f000320400401503400484000514069000320301400c403203041051a0a03d0b1040006001c10b0b03800c40c80d020b04a4509e112882d81d256034201c400c070307028001c407040100400808200014181602c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 333465737 1250 333464487 333464507
    0x173c0309090a0612350a08150f010c061409160b03010315050a0e010c020d08010801060506070b0c040b030c0c011407140c01062d170d05180d03 63
    0x4440c0392000c0d444008105040b144544196046003041100c50000111001c0440003c444a05525845d01140c000c08006006481c40140c1d00c07031078001806000310b03170842001c0d034020035500500880c410303608010654603555540040e060020500c41a02000b5454104a2241515142100403801e0101c01250390f0240008645440c5403040004104001c8100c19603040341e400c0840301e40c044a854800c14014240a8006900251140e0b00c44080301000d014041017514030b503000340406400310500408112041e00100200e90428801b00071540d0303060305031400150444088200f58440a404c009503108aa101c0c4031305007000300400c10b0101a40e009801e5640600d0001c1c0842140005c05092003941205e094002c101d07101c601c0080004208050800f01e004000001100c544a0998940c1ea2410b08180060b4500c01d880c02a1003d0b016410b0348000d000d00c03804c184603619000300c510b071541e1420b83ca98081102c0403031000c10b01c84a920780f001c00d07910301410084014040b07080003807049a40d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 333466987 1250 333465737 333465739
    0x111905060402150c1c23031509040b04060c200a020a0b120103080d11122a030c03040c03150e0705011b0615170a0c173c0309 55
    0x90341c0310481c0f07107a01c240c02c03510820b40110150038001612050a40c002c482d1000078810881072505141d00c0030515035094450f1081e90928980700d2800180949110b00800040e034012800e86040c8000030f0f0f6280140c9802507404000800d480030314403021103107a1204030b440e818a0521507002c040d8100b000c41c4261030203000b9030f0610710454407408001c145208e8410640300b0880010700410204100b00c000e000398115250010a00045400e01610260481701400e040b081c002014441900f00301c94070b40d28106a04182d030249080b1040b06c100030341c0801092146140000000202040086220003010b903a01008003200848101c4c1d010b4024190305000200368840e100012400c1c0d0700846400c4058103140c0300001021304d40c0e0366114050309500c01011906200400042404e00d010050071144103070200040401c500396003000c8502c41410f03841f02514200f448600e041c09240421140038420300c940316000199a40d6000c2401e1002c0d003036044c603504c4074000d0040d400c02c00c080010210208 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 333468237 1250 333466987 333466999
    0x30501050c070203190501110f03150a0503031605120c100623040f0f020a02030d06090c050919031203060602060606130608090f0106090e0d08010e0106111905060402 73
    0x28030729444940600c20080040e51561144000c0c5e60382c0b9061201141e0494480d00002c1816062210440d5180d00651081444850044104804624240c42da40034041c0d0403681304d101e03189010040fa44900c2001001c1d13000c003e0b000c07140418480b081001c0c15071030407410b0741241d07034202098003192a40500758007880c005081500000760f1000f0102c0160100710442d106c0c0500d1000d035400c020042003c0308425600f0358590400c82d00410107403001c1e10384880030b50003440d5a120409a9007041382c0c10798008a051b03916104c3d00243c4a41d03c182620740004007900c200c400380414045010303144046900007000e003101c0c00d003202030065158211b80e04446140d022a045d5031984d40800c10140200500355400030300e4003004106080c40f400c007107600080342c40140c0340d9100003c105182900c49680121a409446454100340d45008105030445075441e8074085035254103218000c00141c0701880380604121800e926004207440901200d00c254440c1d44101715a00c2c0300707180158440108070b07801da02c650 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 333469487 1250 333468237 333468241
    0xb0306371706160c03030605030f03040611030c0d03020a1125050306040b04110a0b03070507110105071101081009050a0905060708040809090c0702040504140607111b0d0b070903050105 81
    0x240000032002d0041d0101007a43c4409844910200d0700e842d0400016001c03d911340c00009480e450030f114040101106102440d603980c1401c030041d00d105101c3c103000c0082d40c01044500e0282c0c0010822030741000c1d0b180390161f6116154041129600c000304604202402407800c0c0720340074a40780303400c0d42540c015408010340999540382055100ca40071a40078120150070000640080d242c078680706090100200b009900584840a9091940088442002003140064200c0501100c1e0000240070341d001d207040781c5400342c1a552460840c0405d45031034180201d640209000c81030032402c0e0405808250720401071031a00a010401501c04d46205943c03d02603403000c5100148540e26940c400d58110140754030b803601c403a05015001400421401c01034905002030700060b0340d07a0052500803409454450404103005103614103261005d0030303c5061000040110a138200080340d051400019001101407502c1d103540400e107108c1450500a100782944401c102e0718582049488045c2c901440081001d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 333470737 1250 333469487 333469529
    0xe0d030207030f080c1911010507081602041b0806030601091b0f050408031810180b03060402040302091503013e040302030109081c0b330315030c04060b030637 70
    0x9110700c1d04050400c0c2c00812040300449102610049918406800090344fd02080d0600351301d05955590540014010024020907250400c0741341d0250807119000c0000c0450807940c0310b1040000074160341030020110203407a00600a0341907800400e0f0240c10740703030342d424616410880007009404e024491211070002e0000d942c0306034071191000c1d115801707496003681007828811841d000108000d034003680801003c0b0068a40c050040d0003030001071300b9101b59210340b40130182952510a201c0d1702120703070040d029070030141d540d00918030002d00041e0700b505101c4c89400c810061149170800394056081c1000c1c0c0c000c100f6848020900c1c03502d2107241d8882140407118034000d0352650300f40c555014890240149999201d8440e806c4d0301120241c1c602c0000c56211300c3d80105800071103404829031142028581c1c0c41c14180221500000c0c122010009a42070140c00d21003400081e01c2c0c03e00440251a03295140b20030a42c0e1503481100398200022144010594090b0032016401418005908c0103030105071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 333471987 1250 333470737 333470747
    0xc0301150e0117010902030d0c06181104180b040b0405100b13020f090a0e01090b06030f0109110705060408041410120507050409020c01020a0e0d030207030f080c191101 74
    0x1918081d44451000b0303481c0c0581d9540185500c84401c01075540e4100b0140140e400300130640c0c940b5070725140d04850031030342e0504a041b02c1c40c802020800d04002080c07040080c60840e020300766258202d40008151101412202c207000024100801c8102088240700c00e200c899451140b05500c2002250071103074440c0010001e9070074140382c4a400000c12240c0e1100c0304400d8000e080c1150300d584d4241c3c00c1c00d650000080719445198080a01d0b0006140144040001c9000ba012550029100c0c00d2a60070175082d00031400c4c90500c52212000c0d900c180c081641107420044540094120044601c00e04103401c1c00e507813541c040d200c0c0a515100386411201c42d41022011a124001d49440346100004048480030180c0802401d19080140403c00407030054210301c05030213044601c0b400140c81d4601041d01a0a048400b0394080c440c40b890491000065800141401071b6680500385085c5540b031490440d40714081e5040351029406500c00310301c0ba10468104544102d4083c80901523070034100c03001525 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 333473237 1250 333471987 333471989
    0x110a09180905030d320a1d1c02071202010e04020c191109180a1104060803040e010e0a110a0f0c020603010e0f0601050a050d1802060703020a141609050403031b020c030115 75
    0x31481d05d44000181d440116540a64510000480441410210b915106040c1410b401c0b04580100b50200602d004550400010010780b4a40095002605592300040d11844422000c140704540004080485c0001070000300382c1c52410101c00d8a0155061500c1c40a101e5103200c0507000d00c0020b00028412804101100f40b11441038010300311104403502c0e026030360402c0c40a519017080e207440380007498000800040004040740310980c2e000303505095084061084c083c25400600d42844220501400c4d1f9100b2180c1990090800c003c14100504080d10b40350b41421000c4e45c0f212000c000041d0044401115070311402c0001e5104805a507000015601c3d802443c0c07503440051820f110010b40d40d01c032a8005200d141c00300d101a03045406540c0010a10303807010b8011070043e044015240c00700b0054021801d0041201d10142a060f5040c01c4105410304680c1301312010786481c0c0c1c01050606010b507126581d4580c0c000402e502002400d04c01030b54039075040e500c1c0e030300a6280c198110050400309074264 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 333474487 1250 333473237 333473321
    0x5090f040b10085a010f090b06041d04110405010b0c010b0103090c0501030b010207080604140f0712200901230105160b0c12010810110a09180905030d 66
    0x41510140c5813166801c0300c460240c801e481300324402c10800e40c03200030020303540203056018515060604180e201010317100d0004c000e07402000240414400540b6a07210080c0c041c492611a0303400d80d4450901c060760764256000b0a1f0054540000803d03821030400c024145070240c0d100a00c031540115004404480601078050106401d4510601c9150300c00d4208003040030301417044800d0603485451007402c2000c00d031011a0700030907441400954040c103008044542030303858050f2013102c0c03400c149000c0c03030a04c001c070041000070540c0d4481c20038048890f540814060190290703900d90b0312406609903100d1315001c0c200904889c1302c0301e11010740c4620112043d000300002500d690801ea503170740340030410340642501d00c0400144001542d5030341c502060782c000d01a036001401300d454030025250844030042c14540301c1290410100c40c45c1c980205c00b1004851690020500f00c0700d86103155401000344010042c86400005010030b00310090350042c505108030054040e8030390342045000703041564069103007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 333475737 1250 333474487 333474571
    0x203100518060901140103020408011a0301060501050a08011a0f0c010507030506120c040902030102070209040b0601080703050702150402030304150203030618010302131a090403050a09080d05090f040b1008 90
    0x520170380e00020003618a60b8411305004d0b003081d40794062603080da02c2c842030b12880000101c46080c03280c80c00740905401004203007000c92600700e400100409454050145001c42014429814001c0300d504003124800814040e0b2951210101c0c0101406080180da40d000000d00702008540c00c3c0c036000703c0310590801260020030050709a0814000075206c0140182d905540c203200c1d01001d602c070aa8610300c128440ea0420003079151050000d0305820025200c10201440c00c41085034064000480c00c0c0d0300c00c1c080c29401916a61403000a2851050b50000000200140b07640b0500da500080914000c1c101114150081c8044d40507113145d003042480080e41c04285185101c0380c24072694008158a81d011181000c80c041403408540c440c03000340c4003100041c2d000101680100d80c00403944000e40882e01c094002ca00c50780350000d0090141540c01c3d031144200014540d02680c503540028200d420180c40801c00c41c28190028101000c100c4102030050110100103449410541c042541501040340e4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 333476987 1250 333475737 333475739
    0xf05010f0e030c061218010c0c11130e0313080a02031203070306050406170c010207080c060c24071407020303030a0b04390908190507090203100518060901 68
    0x1080303500030307180c0e40c2a541601442900961a899075402000d14240c60401c100311428507092a0800480581c0e0f46009030340342031848410079138480f020380a4650044001d26a80e00781100040142424a0311440918540351003c044424084041c040d066429480c03800415a140101030b101e0700a514000d5151300701c03c03400b5000251410256030065410720b400560141c031640428221400c2e40c01003945c0210400c00c03d500c4290801c07041c91184000e101401c1100e02d0100b03895a0390300c6020403070b845400d010500c0030f0905c8040001000c8020550006141c4814a040400c2c600340159028030000e03407520900201c0c1a003101c125214540e0140045107581d640b03500c004000c0100b003601035405501c1e0019510b00898504d0030311041c003e50621908a0810a11292010600301c00f5000074400070391400c01c449100441d1142801107503450300c1800c0840c030700c1c180c3d052040355005540b0301840441800004c20030603104000f9118191040d0000c2d0601c01440c1011002c1280c403030f50b2251354040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 333478237 1250 333476987 333477017
    0xa08070e16020a050d02060f0109090f080a180326071703060a0509150a05030a03050304110103180b0403080109050603060a0906150b0d0b0103020309030d02031b0309010e070f0501 79
    0x201500d000581d44180c8500c107030196100d50422441440b88001a88a482440f0b000c6e4036454405004184e0480204600c6595541702418542681000b0b0b180010220300c3d1880c4600541d44141807400e41c03d010604140c4a140040140c0a05409003800795100220701d2240400c0c0d508940c001604102e0b590b1524041800c0d201965100408103600460340e0700e400102900c926444600400e0400750032814100490f050050102460b80024440d51100b4030b0a00825000b001316034100d40c221030018240b240c5800168094071505501d0b03c102c6015130f014030b084c00013894a0034041d922075960300c1440c0c0da075640c8140a8a50603529540d05400100109126200781d0348103a400034071404002c654000080029a882501603111003001d41001810b5901919548074034568000c09003011429428007070b03640e507901e01501145458160380080800c2e40c0c1d08044200e5800c4141c10101c00356a4078040c55180d010740541c1100741e9840c86104804640220182058000d6900682d912565451454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 333479487 1250 333478237 333478261
    0x106090c021b0a05060f0306030c012109110904240219050304140313030302070b1e0c120406110105060102013804050903070201090b0a080415290a08070e 68
    0x1400302c0b68802201d03600080d054941ea00a481d420405c500420341324900b80c1c00381820040720603001410040050345090010b0100c0b00c081c00c1c00c0d681044001500252480e10244107004101c481d6807110200c0100810070031420a00940c01001002801035000004006010390250b02a6040d21122601c04a034000d03102d80061940103001da160705064901d404801c07401c41c0d20200c80c0c2454803005070801c0c400d054040002c50300420b0703100206440c0c8030520101228201000c48040d04100c000684440355010802403141030001d11803106644660711500681070783c0c100d0310000303495400c01002840660041c85160343e4541b895003000306010441c0d98000d10000a075403201a80003600342034448a0701c580c41050b00c42c0f01c0810095603151141d00014001d030845034420720040c501003082c402c0d0190701c2041c840d0415404036035450389204841240e4003030049500d800599400d90a2014500809042d0541518505640c1e1843d52621202155158440781c010814007101040100d40010a00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 333480737 1250 333479487 333479533
    0x10b090904020d0609030206010f0e10150c0506070e1804020a2c01080d2d140d05040308190b030c120a0807050105040b0f010311011101020d06170106090c02 69
    0x1c0000e04403e1480c1d0303d22040b42e003c41e0082d001a03100c5001480200b580902800182c100080d00005c0c8d032802d1504004204018003c1181c60b11840c0b80510000c0d003e502103003e2558000b050301c225151942008001a01c40460340340f159079011001c004000508008030302850300501100d20460030080300d006040c10000034002000c0c2c1d0304141012886000f40851301074090720018051181c0300940007450003442d481881a42c6041d40c0c0342d1109480d440707184a000c1030590400b9141001e40d105991650701446101c83c015504040c01c003c2056800001180714204105c0b50103007511804041d04100c458460001e07030954030030310b401c044d41c1c03404215002840081808580200a907039a9814040c1c215290880d0036a449206001c104030b60f603400190702220108008986615540302c10a802a482c5841410300c42c003951480001c2c2001e4049a44908101200340203d039a29644076801c20061158042a9442c1c5440030a500101d4010012510956030080c0070f950309400041000c9501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 333481987 1250 333480737 333480739
    0x5030a032313110312040515210402030a170a0306060305010605040512030d140f07020c0604060804051c02070302010305090c06220315020301030b160807030b03011e05090d0305010b09090402 84
    0x3d0070420803a41d0b50802c0990003000d030510002e9112840c0174144907180c1e0b0701e040b405811210a1100c41c612500c004c3c0c0402195031a1318102c2d4480e200c0e4004a801e10301100030150001c907043c0c0b03002960717155002c0180078401c1c081d03404003c000e5a80004904841d802e00a03103000078010801001540340c000c605c0c446c3c01c000102901c3c60f028113040c02d04100c8080d910100c080c1d589034002c10440700d802d01c0005074062130171b001400c0d0307018a4000050f450b00c514080e01080c810398030082018400108840c6680703d161004010210082c5032001c2d5031848148408c80c0040d04200000e4150440840c0c2001104405010f00741402401001180c00c083c00040c04030b001f82944400001040540d0600c00c201d0120300300050f43d03541507080080c440c4074028400490001c0c4580030781c402e50341c0030501c207900950624001801c52160f100103405807406c80705404103251980c01e04840ca00c0c9550166000e045104221000300f00c2e40841501a103009114112000000b44440352040c2002d1081e1680548 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 333483237 1250 333481987 333482003
    0x20606010c0212100504140706080f090309030d09050406090e070b090303190320030f04030513030b010e070215040c03060513060f0903110129010e090405030a032313 73
    0x1259058491425200c01d01c0c054541d40c44605100c1440088030240240c00d40d07c1d07014240c080e082c00c0d8064201c0502610300100d1a14040000300925030520545454040c014140c68056054040090500e801d60080c2c2c2c0c45a403404100040708040c0341300b010080842140500a411700e00b00c08900c041c1c120500352601800104065411400780c00713031000424580e6140082c0b04410801d0500f00ea0340e40d07200380320112000b082031020b40c2e150350541070b601035498901241d88500c01d0122117055000c0703600c020034002c11000089050781c1c0a0f0380301d5201c0c45240d42203800b5022200c10800d0855000e4901074051100b00c10184041081900b0040e44118140f16541c01d103500f07560340030b0031244600124505c4c01e80e903058a00416a02c50441c20900da24138009024124119007240703001d144003c100710810300700940407500c9900598031514000790040c5441180d10301424010f80307a5000003074510003e0b20b0301c5080c020310078018003a5501518086540304040c0d840042a1107040c0c8031240903243c0c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 333484487 1250 333483237 333483259
    0x1020f0a02061e0a0c0611042303030c010c03021b0a020603010b0a030b0603090a021002030f0d020d0e060906100b070b0f07030905010c05040303080606030f0c180301090c18060303020606010c02 85
    0x1c1d950750010451a1010360345d107440824076040800c1201d16031501c00c0c04414040008020701c541109503140480180342c007c1903a02c61480000c1d1441c85090384049041d400c1115040c410b43d09036010341101c1d00c0840d0f0030351124070602c10081d225085080001d50101d014030040c016420800041c140c08034445c10300280c07211140700001c1907504120303240d88580d48500c1d4074800314144254003c6501d8054002542800810071300b44000b406502c0c142880f241e40440c0360440c0e0526074106050088074007054444505018140a0b22500c1c21103030700d1044203102c540000c4040701c0004503141c9a4122902c00520703100c0c0018111003800140c80074003099214031101c8081a02841544444001515a550740c5c0b450b500c0e0203000050020044d500c901d8051003000280042c0110040e400007000040998503220796100c940442c45d00303400150103610f808590020002500c4c910030a840400980c0c03160200200f2000d01514240e00009005130490303804210b4550140e40b031081c60314030042800b8080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 333485737 1250 333484487 333484537
    0x20d080318120910020c01120c03021309020301031b0509070f0c14010516020303101512060e180a050c0103180609060507030605030f030f0a0309080a09080c01020f0a0206 75
    0x1d5454078028244510000e0b8440482c50700044e08400d04190b0b00103030400c3c4546100180025054440451072103494132030b40410700380b0030340c100c84204000d00001110207444880300300c000d410900084450030290b4a0310b1851403c503100c550b080301c0c80208804143da6031500e08690600340c64003c4d030b043c410301070b000c800000d0f0840d0400340b16040741d070000181440c00c102d0310104500000c2d00c0f402590001c009001c1060100c1e02c8100588045503015040428400303c200c0d80c900d28038201c0044180703440c10100b001342100359a140281d4811180c03550420322200443d40f542d0030343c2002400b60384030000156070b80d4000c6c2c0140d82481c09041803e03482e4030041c0c4900094804a8030100c400c2942c0380c080200f070079014072401c0050b00042e03004210304c1c14a0b042043e40da10a452441c481d8a102240d400101d078400d820078180075070b114415544032034400c1005899403240f8007803d000f40c0143c14180e026548005050040b100042e002000c03004081d40034405503903c031010032050841c40000503148 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 333486987 1250 333485737 333485743
    0x60f0c0b24030a0b041b182309030d05070f1d040209040e07030605150d06050c070f05031201050f0a09050408071a07080105040504080d0c02010b03011505010e030604020d080318 78
    0x9128090384e241c4030b040c60a890071540c80f100c03019403460040d04251052001e101c204021010504a8407000609a421288585003004a684012801003c0b00f4100000b041e008406000d1300494000d05002a84840d602a1440f40c8185403810002e603003444d80d0350000341810203890701400050801481e209210001c81e0a83d00000c522011903032003250308004000c010b1098a80c000e01810400c030b10b13580300c800011703c03481c10504003800054540001c5000b010400c0100d64100d54820b0301549090440d16000c2d4903a045000809840ca0b0501c0001515060190001c241c40318014030001100d410019030800924000d0025200d03801c0c02d11581d000109010180d400c039401e2444400000d10707101100400c090f80c140c0140380544e04000c02e20000440354410380e51000d0300040c010920481404040b030060442190304c81c1e041d820000c241c0c81240700303601d900381a81d0017a80c44120f48440c040a1566a000641d0000d4011981854020103e080d41c4003568200e2b84079810648206040065585 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 333488237 1250 333486987 333487003
    0x70504060f050936010e0906070c031803060615090b250605040804080d1d0d020310141b070c0e060105040801020406020102040512010c080613140c0301060f0c0b2403 73
    0x802001c214012502c44100703800c4c140104008900303922076107004001c5540750350000c4c1540702440309080d449003c041c02541d2038402c410000100c041c0340356807070030018040c0c20b0780c0c030500300700740b1804100c1a02c09102d2104070b410b55070280c100c0c5107007000103100c10b141101c10003040c0d00b201054540c1c2c007000a14500900740070780c0c001e00b00241c4807402c100c0154107101c030344050b0b50140301045d030604580c40ca04075004445010111850000d6480500100e424820a440780031182c40c504210507214550b26100140610222452030f0b9038210480344d120711a11a6640c00b5080354100d050800071500c2c0c2c101243e0f40f01c04185440f03418960707240d20b200d080e0780003034000740e0250350081014090760510007102002c4107001c1000780443c0015080261000601170309a07030140d112844800c0c400841500010312924212085001500d04a6541101d603007027801040001030b034200041007204e00c580d00380011550004001c58064540c85a00b81c0e50300e040040141c0405400991406141d8090280e92 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 333489487 1250 333488237 333488299
    0x1103010c1e033b060106120f110a030504201302030c070c080c010806040501050f1e1e09010503011530031205060303030108030f0d2a08070504060f0509 67
    0x1403c01803225103200d014000d80043d40080d0707029038010400107038084400d01d15885d000c900020101103102a0102515002c40452054040004c10414180c0d041e4001440b890260b0243d20707805440303502c41140c0400d42d42401fa4840450000c401d440002c0794011608440d98040f810b241c2591035a804081c20021303030101c1c5064003e00751120003540c01c00c031301607404482281c00b000b82d58144000a08101c504000da94014400d85561490324200f02c0344580301d000c0004c040584689d0b000f909501040c00e001070590140c0c41308000099242814098981135200c82d0750750980c02c40c14041c0d0011103442c40100c0d00082d00800c0f002208802d8102e40c01542640240c0e502d01c1c1882c0c1000000007030301c03030150649009a2040004001500010003581c1480c0c0800ca5019624180c84100001400307086094005050301101e0001000303004a00300d0081403440c0d2541116651105015102c9003d00c3c4600c0300429000036010b40058407817001401a04401080341c00a81d10000003a40c203034140142036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 333490737 1250 333489487 333489551
    0x190f0e0f06060a1209021503131a0702301201080d020721110909030a0206090c0a05210717160b071704031203091103010c1e03 56
    0x4031484140481000e54440029640380d4a4031011103001080c80d0003105a00300b03815a41c1055000b10356801c990801141c104d02c000c180c90b0f0030489039201d110320079200103c0d558014034880380b501e0400d50710458401c103101e0b0054690400c0b860594003002614205800c003c0c500480e00300304110181024000c441c005645d040381d2581041505440d040240440e0b1083d0740c000002005082100ea0100441284040d100c20300c0c0f001600e00181e98081100450394440100303c1049000345000015100d2610141c0c21201580c1f518541243c890248100c0c054021141c3d0308144558101003065082c1e100c0410a114048605030603030a0400880342c104139401851160355015040c02040f0500b000c03c600714820b4001c51605140046900c280d01c001050301c0d10105111a0020308103096a00a6800190928040084110040080c6104442280c00105881c00b0f0343c4281014890303c01c1161407510303060540c4032414100e2072250b1500154001700350715084140b5038020324030901c4920741410020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 333491987 1250 333490737 333490741
    0x2508040911120c090a08150f060108100501200a0f1b0605090f01140408010c09090c0206070c0204180311070614070f0c0b040303050c010605031b190f0e 67
    0x6020291001070105445010003032000101031512008682d4000da80070034040d13640d202c4080403480d03060705d81c2d10148003400b075041c42068519000380c1d80c80c8a6081141c02c00015540c1100540f42c6400640340302401c03444511091217194003503421810052441c0014200343c490050340f0902e032a4006008465000f0380411071401c100640515007070070f900304c520100004d030030808010710f00c1c00b0312103000d8415050b4079400001079008415101c014818503000c00d0340c42d51034118507030203040010046c1c7c00284042c5000941d03010075120302c401035040c2c0d901a00742d0381c40300b0f001180e00d1222800c00366449a070351801c243e0300e0a000080301c035289111b078460030381c0c604c481e081d12400d00001e94002d40c01d2060450007010a00400784c01c8510441d84406920781c00c18240c00d203082d0942090b0021100308c00000380202c103158001000c1c00c0684030310230007400800e0304c0710149078075a00001d44a142c1100b0a00002125141000e041101d6500320b40c000c902c038a684092524440d0b906501105101c444d10003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 333493237 1250 333491987 333491999
    0x100603092f0901170a02040b3d0201060b0d0209220c0e030303090c060f0d0f05041b060905061e04030308190504080a081807030804060e03060615250804 67
    0x2d046004240450445410401c00701500341c4400d40301c0b20007032080d0b580700c001c0200b0703039548030491918004001d200c0e140c04440e0007008101c0f1910301e100c52661000c8010030040140305000303102c10f481c0741034050b60402d00400c0025003c0c0d00450521580100c03410703820310151604c0c900e201070391541c02102246000a400c0040c1203400d0f40c1c94201e002e42c00030410000d074504c00048141c0c1d292000d07a4050b03500d802079000c0185d2805403921440b1760b10b041820100c41c52859812640c0920f0080843c1c142c008607566100400c4c0c2c1c01d030320803000401d0b0403103010071440c904540034000500c1c0c041098903038001e02c8030452059134003c0e0821808101844280507500c90b10845075040c5645045080280b402c5c29100c20b5a1030049050402c1044468400243c075040794150384100090b80004858145840e807805003c9034015029100003d080100c02030074624000030700303501a10028090207041d01c15000090704a41c00011524841c103100501a00280300c0c00001250103402100c0203074480307050007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 333494487 1250 333493237 333493249
    0x14040f1e15050f01080c0f032401030903020d030c0c170d0b0d03050d0906020d051015030c080a090f0512040306050705030c09090a0b0d06091505100603092f 69
    0xc0a02600c40c58014810b00c40c903203d18a042003c41000d0a004006684c0c25000700c695100c1c0104406c820030011041c010000e0a1000b810000c60074500030059000701100110115507100201a006070321840c0fa0110a601990142e5000c40311803901c1550421140c40d415a041e019098103c221000000c40703044000d03440c464400007990480b01074901c8021910000d146002e1521000f640c1540d486240d4200402035044a003c2c10101005104500c0c0c6020240035040c601d10a8080750980d812544202178424030488550080341c2e00e80200b15160010903800800f4610001c84901da0b8074441000881c004100300c038100511407a01030787c0c480c2949023242c140c3d0400f80951050017018030501034840190b509440984409036103c00003592820311072400f9009580010350003020240d100d0091000030303000b5001260180e041180040760700c501c01011910104c03607221b2561210501840344910a811108505000350840600700c1e501c2c1c40c210701230400707401c0cd49850b5008407038088001d00b024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 333495737 1250 333494487 333494501
    0x4020f1909051003030c0b0a060339121115190210060531020a180e040506011707050a0603020c06091204050d050f01020c0102030601090e0c0414040f1e 67
    0x89030f10401614503580e0b02500701445004000c040806101c0042c0241091383d00c03040046410840e1251040010740b0080b8401342c6543d60300000741c000e80c90320510040150031500448851000500e00c820058a030403151451b4612100e80c0f00000c0000d214407418040c018169500382082e6600b030f845030301040640f510050840ba00819400c01604000a03580d50404003406224080340b02040c0d0800b100f420700b00d0344800c0300040d000b0f2002c124001800d500c0700d54804074421404d1900b01464880180f04070540085030020180d91107240144254090b400303421451088600450b107601d605d900015000072081d41100300000d90205150825030f008100640d0080c0707010010b407040d402140c50304016131207540681030040712810018010010100203107a84046028000c640718407450308454040c2d401030b00c9c40d40c00541e540c003000c101d803407841d4641e50007485009219450186000303602c0d180311403910030713140e0300c99952070600c814004c450155144e1050b410150007410000380512000304c0d510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 333496987 1250 333495737 333495751
    0xa0e0102070e0108060a0209040b12280b16090306140f010b1e0903030405091504050f0f1302040908030711071401051209030403020d080a031103160804020f190905 72
    0x2942c010028404040f1300c15400020605000d03075940c40110115002e00700403001c103034108442240740e10f41c007800400c4501d11207036000100e6601c521b6060303003034041c11400c560242c05603a01c07030041196124064244034984005060440b502c56a03522107208907200c41442d00800c855440401145d0000681c2c045d0160a0780415681400c68000c811004502d84d24941d007c004000a6800350b0b540c0d040055900400c3c4c0245a040b035868840121101241c2e0741e1145030082e400c01c1e002c40c00d84900c052115102d6150350404003410313615240d032a40c40b00564041030360070503035030700102c4041240300c4003c521580664031144070001d202c2c5826494a10158410034aa070300032200d0150300d80e4807004594a66400310540a01c2e0340b2221101030443c4100d9100070340c0050310180ac04204010b400c007408540000b61010481d90500000c0007041e4402224800081880c1f5518080128001d801c00303a0030600140406d102d90b54043d0206003000d11031421443c44404500c01040342e88550b00509034003240b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 333498237 1250 333496987 333497009
    0x3030a020705060c180f061306021b01050403020922020d03200601080d030e0708010501080a0b060105040b0d0c03090501050a020717040302061222030305010e0f04050309040b040b060a0e010207 85
    0x16100c05045c00c0381c01107541c10b6201c1c180600c040306032a512101999040070701e65a90862282d6200d6002c0d60300d41c55100140040703500d49040400700d44c001c000341c401301d03a0054200402551140d54000b03113940c05104079000035400b000b01c01c004d070304c581060219082c030a4982100841008040701d0300400c17490510b1800381c1c001d0005005088010802c00c90801d0030341004218500700304c501c1800c0c0489508202d0041d0b1038840002121140000c0e0580e5460164480720802d44841c1d004442620540c0607520303810b007017003107100a482030b00d5122041110441c0350009201e541643c81909464081c0c61101c1c075103401041c84003d00c1111820240510558140c49140c1803a60b408070304907000340c60740f4540014220700019401c01300a082031003440c0030b0849074048a4101c1c134000e00108020300039220114041d0300001c3c4a01030210000303010745e40103002581800340c040200400380406128041c0c010b03446280b16401500c3e18000341c00c0e200d00300c4d11030482c01e2010500091901d041c552010032085c0e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 333499487 1250 333498237 333498247
    0x1802041803090510020304080d081602011b0c050c040903120c03090b0703020a020a0507080d120e0c0f13020c0c030105061f0309031710180207021e011103030a020705060c 75
    0x1c0c2d0080640d50455100b90f9210b01d40e042c04103030036819070146a010f00d802d40144441390080341d9001c20b8462050241c1c11192240801454003282242c015180c082035851f03404841c1e901c0039000e543c0011106200d04101c0d000008000042001e6400d2018124003007003102c044c4120480c0640194400c00b403e0303107002c0083c008941c85291a11a000c4c210343c2c1030503030000d040d0f89194800c2c400624079a41000c1141c40040e43c4203d1542e540c9100c541c1107002138201c9a010070a1072040c00341003110f20b4058000c0083d2503921081154008030072695651085651442c509487d00f24005000c407007c241e40035003051400d04007458250b441c0146403600c42c0200441c0d41d800082543c500002a1405282c005880c2c0b030340740703410744450f1003c40898001814410800c200464008100400d480743c00101015801011000c001a801000c0009520060301400c2d0465450121002d140e500c405142520322001c440341228150f43c0141d880500668000809400340903040084503000065400c0c01e0303240c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 333500737 1250 333499487 333499493
    0x300b1c0506011802040e0c0c0607090b1207030e0a03020106090507020303061e0a03080f0c0c0114041707120c08012a0507020d02030102130305060c030c0a08100918020418 75
    0x886050140a25030b0100035021800c00c0c84070344c103590190050641079603282c24540c80054003500300711000c0095101d075000048809120b4040007048030a48011329041081a40007008076807001002c1d44101a0740d4013203d000c0300c400300449050343e40a5000050250709240300c00781650f01c000c041e0000e543c01001403040030b848040d1f00180d0620344c0700c40701102d21840000500046101d510107032003c1c4020a001e41580080700c01001415254400c40303040c62041801940c0f1882c0d0b010500808440510080008c00d840004410010f80781e0800d0315440c984400d18404a40d00c1010159840703a40c04105020b00342c001d20541484240c1e005440d900d4140d10b441940002820080100400c03c003c02c40303400b151112a0721140302580140213541310754407030a40301207101240c40156041d02c90103010504560900003100d00400300f1016040ca040c076044010741d9440c8001d8444860014103840000d41210382d40b0409400284080080d40207443d03a00401c400e880e030b00d2400d0b09540b03031188090000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 333501987 1250 333500737 333500743
    0x5010501050f070c0308070b061f05030a181202010c0210020c030406031a0d1b0e090c19080a1a010504140601120f060806270607300b1c05 61
    0x28540c8000600f03980d00c40314a0032805103802e030340c4002d0140802003840c400700000031000501c1264191640441002031450f4210414031441c41f51010071402c10104888410a4000d510810040d80d4520720300b0080741e5031003070020012110080180d6581590140c0d503a0306001089a400c80c103c025410020300360036068032031080b03100d0340092643d80c0f1400a011102c4100c0030402200040c06450005d2442c1450610b805000740c1d40114454203800110704080100c00c4180560503d80080502c90803900900c41842061302c00a80458010a000210690100300d02442c8510961140c80c0d0a00c2039004800031090682006115506220110031410400c41902d50302000904c0c02c41c00c0369241d64443c0d8020140c2d1542200c00504041d00443e00c00d10026007503000d052409400191001100003114040b106030760400c03c240c1080002c9640300c4d200c0c903882c580807803c4183c120404c0c1059001801007600405103426059215a07400b400fa14100030801500500301d882a90000150364031592 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 333503237 1250 333501987 333501997
    0xc030b190e0712020a09030b1f03060c0c120201020a17010b07061109060c0309031009150b13050f040c0603050705040b0711030102040b18150d05040f060c1107090501050105 76
    0x100c01080000500403d125a07802480b19030703080c40031540e03007040b107100600016190205030303035025149001c01c81c642e0001c0080000c01c05880b0400c03a17880e003982da540c0c0c0034000e07134013011082000c0c4400c40e2011840380310a0210350720941e000107039518800d01d0040c02d00b01030300b010f4034403028840004020b9654824119541d0b60b9000c5400244507d240071124490300480c001c16800080c0410082e00e840000401481070700b0b0105d0840f1003040380d14492000f03030382c0c84000003031001d816001c46184001c050303040050360f0368004020410081241180d1401c45000b198015022000f200c01d110911440e00d51401c003411180c41c0611031840c00820160041c89280b043d550f040c0b40010f03e010600c0f5480e07140845034500203001b959600c0c0d0720032822031550020780c0c0d1079540c081000991308140c50442d8001d103a401124074602e04041d20300c80140003c00e4010300c15030b06451101190000118184240702640c450b54445c0d248840700740d22050720380b44003604a6580706151a00510046c0e80100c05d0750 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 333504487 1250 333503237 333503249
    0xd02040506011e09061701150f0504180f0c11191b090b100219030f0314101d040c050603060a0e0108061b031315021c0c030b19 56
    0x4034098450100480e1010804510311008042c2d031031070032142a5010903194212041981c03032107500038984000340d600040030300c1900358810a40d41c04c4884030f805001e07540780d158102e05000e0306140d510075440054121004100440566600c0c1c2d0400c0b6241e2449040c2620200b45482ca074603140c0000c20b02e58a55036000c3d480c0c460350703070342d020041000300c6216111151204041e808200e20f81e1208220040d002410000b4880c0355004408081c0728800034040402c050450a580c002110503101654052a4141528101501d451808400c040d1150f1064054800f81e244980c0442c6000c3c0c042c0000600342c0400d18442c44848140400705011911890913150b08946040d500d480350400a010341c8a150b01280b0380384884000007404c00c0000c181c442c411081c004114403290400c0c0d45010040c84121207540304c40040315450004190b86640c1d803440c4060301400146401400c20418283c1011540050354140d110b094415907541d26000700306414809413407194400c1c0c61890400c079581d40a004034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 333505737 1250 333504487 333504491
    0xf040503041505190c0c0504050903040b0c0c040c0f020d0e040b061215060c0a15090506010305010c020c06040b220f0b0d0f050c0a050906120f06011e020705190317040e0a020403020d0204 82
    0x410003804060048400610340dc0c18519543d0a2182d4041d458030242c10005115910740b00e0240300d507178050a510041101c0d194054409040c048a0030380e682c1c0302641038944c01079942d4101049507106d800080082c0e21145030b14460520b819002003101d800c9540800740241418440c484101c4000100150303c1c03503000010440c4901105080c0c00141140d1001034241d02c541c4c80004284081944025074401440d42079641c00c000406c18030540d8403c034410440f140c0340400c0050795040c40d110040008411185158038480e5a40d50040d10f08001c5402445900000203203158102da0144102d0070400040c4406001c14a410419204c081c002c440002040c060001005155566003a00715130100b104e04440060f07600b0068202200c101040700c010380411080010b0b03404490006000300341d510b500b0750007450f5a60910f01030062000113070951801c0b1114440001c000140340101c0d005114900407030319134903036291044e03400e102e04005e003020032418410042031015844600543c65440c0d016940 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 333506987 1250 333505737 333505741
    0x10602190b041e0803100b1603030c0e04020a02031206030a0507120804030209040b1801051014060f03010b09130209010905041e110a090603060e0f040503041505190c0c050405 77
    0x2000c403002519042010030344082400b20f041084040283d405007540c0150085030302e44410203d085842103070494181c40301850228070000c0d10a0300225040310071881c200340f80129401c04074003682c000100900150b000421a0104204040b040036805202200181507242c0140c81f449d80b41c0001b4010841031011001d6540d081c068511304a5004603400b4080680500d018102240d4224003074440120550290308000d0003e401409040e003da50384070400b4003001d1802405840138240e64400540100051215070309070000200918020002000d89503650050601004840541c40562902c041d1041c0b00402c03da980c490503e405a42c41a02c00180da40380c1c204c080e40031074140f500007209050812600c1d80d841c80c494805001e003481d40c0d44440c2001602c3e41000c6e0103669890142c18654250030000560402410400300c1d0418020010740e03203810340390480e03c022181110142004900d00058600070320549254032440e251092401a0005080b80d42e2043c081b140c07442003622443e180c02c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 333508237 1250 333506987 333506993
    0xe0c10021f02092404030303050106050c06010501080712050f100503030c070b0d0608030304030201060501201908070f050703170c060414030408011e06080309010f080405120a03050f010602190b04 86
    0x40525440130f510700540b10445083e5944040d0303401400100e00007400c150000505074043c078107885005e684000609106d070300f08001110100c100400300000c00c00d429148517044903c41c41014000c0c2c040c83c0310000249000c40c140032182946034440c0c3e000b68000c000c1c103a032203100456000b09462640c0e110707a9641b8450014000030b40996040003c050000000344000c1503015070002040b1002030329034040001c5070841241000240d040058155000305218240784400ea013081b0010501ca51130f11410040a521031295154040d00e04403540c0d40204414020311443c079003202008014855203910b401041c0c104c00b83c44d0300d4007420040c105c40000541084610080c0151405000243d00810104168502c521080c1040e01c20307030b2020b5071519601068641c00030084881442068582404210405a007154406002081581c1600441900c14803104c8140010300f6503202d60341c0d02203564100855207290b9050113900c2070040d0f5000304001044600700c4640e0001585d0404034296144c1e80e281 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 333509487 1250 333508237 333508249
    0x510170307021e0918030d022106040c0e15041203120e1b010509010c050d20060114060d06090204030f02030f0a0b0c0703050d06060c0b071b23010e0c10021f0209 71
    0x411f009506400424030213410040f001c4220390000c040c101001d000c2c0c44090521049414603071025000a15130ba021f2a010b013018040889d2403402c0f091854a0310380c0d41c692420074036440650890001d0140800505502c0c0c45d0b020b401049281180a44200d1110a00311100c005610001505020300410342200607801030100c042c0d1540c00074290303501a022803400410500700360b13090b040400c040b0683c800031000700080c86410703941c140b000d8101809803401007080a4014070801d00115445000200c0c0960043c00540000c51240d0000c82c4444800c2c4101800d142c450f90310416a0b074030545806010402c1c880da0540c00003031a2591660f14809418119414811141c000c3c1c0304500700000080c0460b48580144121400380c24500800d455824080303803040643e06407400c180140e07060400104018010103103801c1480c81280c3c401e180c1e40d000c2c10382034400210320a0f00f141c004140c0031001c1e04002111a00600c0144080c01003640344a25520b1307006440701384018071070380c04500040d80361104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 333510737 1250 333509487 333509497
    0xa060f17010303261005092a0318030702010e0603060307050307080a0507081b0f010e0405040b04140102041d060d0b0c0304030905040902130510170307021e091803 72
    0x20255503255a100d00300980000c501005250845418001000303070b10440c2411a401203084a07040b0100c0c0b4070340020010011000761800a100311100b65185810340d948091284c080120309000b0780360b241c1200400080d0300301001010054004204400043c0e910158895103503404803030280d160745489021a02c1c3c1242900826018416010086084070b40000e0722002244503000301d5404a071203041032501c44094600e0600c40100b0034903003c416140c00f0702001c0c501070040c901003806c05a1800085c058070010740d01520014900c0044c8020302208035825440665010020361416280250744801260219032000707401c0d01c5880400c0780c99444251088030782d41c22138001202c80c28407003098000c0d948140c401b200410103504002900342000d00070b41041c55001041c04c41c10880802c511006000010700f11071000c007002202040d45020080440300c0c0c184500011500d4031528410700500401c1c0c228500001d10590029003000c2d03940d568881d0b807000441c00780a082003861726001d8594054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 333511987 1250 333510737 333510767
    0xc03020d06080604061a100f0309063b0c090405030c0f030a0906080c310612050108032d07080d090519080d021315050a080c090a060f 59
    0x1030041c001a04a40000c10b540103500819040041d0030910175401c000c0c0c1e0f0002c45140e041a00241002a501d00030107010342e10399011704000c42c00b68000e685104c00c9501807a400400650341049001c0500d15240d900041c0412983c10308021807040800d440d0f03944070554540344191140400242000700510a0303960740110780044440e0381024000b62138aa41220381c10300c000540c00e0744001222880b440d07229010700d00d4450801d00c0c24001c02100441e0b0b481516010303008104004d01852032101841240001344611390f01c2c0c0d5460b00c548010f07041502c0e010b0380300d080c03203a20a100200c5041080300c8075451560981509440300c001c5003020a28070300030a00b000e0328549000c99810031403001d54008000c541c3c4142d0607a00c55030060001c2c81d24060150741c001e00070402c01c0c4a0340c10f58241540c0103010ba400800f08040080c1c0d51400500881881c400c02500020310103d13684800b00c0c1c00c020043e401c084c104030100e00740250714006c50b0101c0100e10850040181c490501d00c0c0c024005c111007410104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 333513237 1250 333511987 333511991
    0x90e0c0a0516080406180509060d2306061e1c290a050703090308181207050319080103080d050601141201030212010e1c0203040803070c060207150e040c03020d 70
    0x107800c1c100b001c200d0304940305d104007058602c20a41c51341e85400502505030b60008040d0034040d12801c0c00d0004044003942c007106c1305c100c0c0445010581e181d000b161f004201d02c0b00010003c914240307080c801c820510034042c410750040740c1e064090700cac5d80d000c10003d01e0407206840800224400c2c00e040400c0c84110072404c40700521190300710f2020312106440f44c4a14001030301413040d600c030203030201d00b190703107050001d4001400c5a01098550303c1900c49aa031414031141122601c0403403412071701840c5c1c0320031002c03181580300080e401d403803280001e050174400300181800c2c00c0a6166807103100c803074860070000c248a81d94a070001442c0c0d81c042c0e414545071039000e0504503140c0e090f201c284007a0080a000c203a02c60308a08d1880f502108050141e101655980b4024041c0c0b40896404051100280d070401c0c000c0d030000380b00100e9060390800240a80e18001d280c10807042d464150081d0810381650408240b00d071004204215840d000001101a05030542c0c0000d20904905402c400902400e00c800100c1d038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 333514487 1250 333513237 333513277
    0x6091e012d020106120510050402040213080105090c01090e0705071505072c0d0803040204020910020d11060f1f080f0703060f060e0415090f030915090e0c0a05 70
    0x1a480d4500040501610b400030012a5107440000c160950300510003440c690100d800385c2d020703e0143d0001c0c0e82140c0301800244c20410b2402c80d0084070529a000040161341d500d080242c01c140801022034011000c0c204a24014180740c1150031b050002403201080c4400040c0c0300c020448105000300042403211002c00250400b540d004020101158405c00b03001d15100b90032200c20740c0203802c0103804c80c1c0145011a200e040340d50340807198000400680e4410b50034488000c940c1c880d541c00b411aa000c65010744540368030982c01800142154041e200c065002204011044100089281e013000b6100000702150706400c03200c56604401e0381100841d401004402900e5080000711181520701c140c606001507030101800b0412240070b0720940c42d001a2101c0800c0c003040500f140d40e4840c000030701303001c0703031101180c0c842c44403596a2203c1240094400b04d020000002007101420141d0380c2c0b864800400c0b80f5004c48030030380e400b001c0c01308030a4400003e030a0707100501a10841d080e0a1004800e40226 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 333515737 1250 333514487 333514547
    0xf0c03041e08040302010f17060409031403010f051206280902150c010e010b1804030c080304080306010f021c080601020c0a0b04080105160203040b0906090603090105090c06091e01 79
    0x20f40240c8403c90100740d542c8502c0200c0c40c010020310b4450441d0f020203036142d548050401c00a4130000b4015400c4c0998a00b65248801603140118064114924400c0302c9501d4041403220100a5010107907040e0451424400082902c0007036212024514640704006200c0301c8405000308084607000750320400d840440042c1c11219005048480214002044000c1c8017a0000b401e0b9041540c8882c0d00500c50030b684c40c50700710841d104641060285c42c0c20828810540e81d01d5240e680305a038241c4030b50b10040704110481d83e01880121003c1c580e0f101404003c50440400318031040d03008503030303420700c00a5030010707501e0703403080040c00140a8001e0807005400d07a104c0300c88481d035115009403002942008000f481030214012083c031544600c2c0d0085103820729000900c81c994000c2c00140303078441c50401c446103072903035244091030041c4503001c00029541800c80200c0e140c4200c4580e0385000340c000303114030700b82540c41c00380d80001203200003540f181030882c500048030000c0802e07600410a006c003022104030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 333516987 1250 333515737 333515753
    0x60c1b12030105130209041e06051e1048080909060f1804110d030f052a15070e1005071506150e010804082505010501080307020f090f0c03041e 63
    0x809504208c0402c40f40703889400780040700d40035074200d4000310302002c020320860a0044000102c031300c040c5030a00001c00b0320301059100a001500b0a030070340140c810b4109842080c4074103100c000807000c1002c0900c8425540e80c00b960301846000710301c01d0706540001440b17a2914807a15810381801000a507101c90b82c02403041c000340003038a041d44c8004e00c3d882c1515860400c840d507082c801d90581c950111201c0040421101035118800303205130800721914140304415625011045000c0d6203019007041d150401da0504031600060404003048007061400b40162103c80e000c502e070f402c070b504c0c2c03e03643c401076070407c04003140e12040d507040114a820000100c42c0100c40014907498074a588031600c25255000450b44040280c81c003520156042180d10802e16480003c1d40c0e06810001030601a02100e40700c19003107d109034020a070a80000031500c0840c506442c130700301220021524030080d07041c154400c008400000340f00c800754070000004070741804108070340080c0a03400c0d040007501164591401c40300c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 333518237 1250 333516987 333517031
    0x901090f330801020901140c07181a010801180b040b060301080304080d0804030e040b0d12051c150303031e021321030e010807050c060c1b1203010513020904 69
    0x194041e18440105900d6818001c032400380d01c0c160f60381400e10310100c0d10b9800300e80c000c01e0004000c0c8946500043c0c41d40f1001c031030f81048003a00000003000090a801503031290040d51540d41000440350040c0400d200c1211215004125038000003a4074840f800882c0c001c01f2206421076000c140417000040702c80000006100399960311082d501c089034110003d580c00c02060314001c01040d1012400c031103c3c00d00790310640311b55200904803820071160391a00d00840c11094481030004600152100701001d01c140c042c204813801c4c040400012903040a001c050361443c2c0030003820180c4034004d02c1119241c001d46e1401684202e5421591000b0b03180303080d4050440c0344070b465400d00000c1200b0031355aa6810ba481c50032900740d1940380040517803000441d2811402440582401030520000d5103030700041088520403a800c441c02d580e10545424500381750580c000c5281d00950181d114803c4484d0a0f1064a045600940303618074041c8400c0e070160040e005507001c658005140603d10301c0c0000d031100c4402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 333519487 1250 333518237 333518321
    0x40f0f030201110303010b09100e0607031d1c20130504020405010902030123060d0c08100b042102010207120f0c080303090a030c0c030c0f0602060a05060901090f 71
    0x103803d14903041c03200d407280001d00c5401740c00a410f0060900c2d9080a00b61804000030626003030031a130f149200000c0d011b400c046d5058000900c0358038100d0541e0440004100391070000c840d00d80c2d0b8001d4082d603960107e00e1104008000a4a9064101c00701c80c038030340e080410b004020302c1d0b220100e60070300e04000146411281a8030a80c1444000280ca203c0f61080380e050300c1801407a083d014054030080c10184035401e0755650000b4041010107904041d6104808102d40141e80388005400c02001c18443c3c030380d540d0030095128008002c1003205006540001110608a1400410061550005078100000c580c000348074150f814003c141040155505c0e1460103119001c40c11025071075040f6a40e0b2800219280c02c4140e0186145a011902990541c00c207644260a1405030b135841c0d690741204440203031301c040003460300208140002078040c800140e02c00c0103007004001031700c0d21000043c00c124040c4295a03201d0344d1168032401403044c0390404085129241d81201701c444403143e264001c04910b004603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 333520737 1250 333519487 333519497
    0xd051c02030703030510030f03081f1d061c02150c0615130b03060c0d021c021e0c070b0702011115190605090601081003050d08060406090b0d06050c040f0f030201 71
    0x1b900c001c8848410002d03640c000c900501e01c61440d54066070b1541d0041e1a0405035034002841680424075050030102074828400200071518202500a40041c4d016080d180320b104d070052415a0801803901f4096599012600c01c4006090080b0a150502c40c04080d0207480c01001d0802c0b41d06080075031050014001600c100300d40c0040109400d0032224964181d035410f4205101041c074071b140650140101c503540940041c50003c21507005100002c040c02540e42c26a00410604811608035101001e506080300e411840d112a840840c0d440b007405000300188180c01182c041c0569105441d40c09002101d0000c40c0c980050024603120001c2e811107680c801e4948445405140d450b990240604031040581280c030b6a0720391800644070160000e20000c1e00007014000000071410070091072403100c08030b0300c81d00418109081800309803034598110304502c0d4145899003403542c840003944910181c0024000589403510300c900101c5204079440424046407540000c20b8481d40c1600017404c8034803d07220f0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 333521987 1250 333520737 333520741
    0x140d08010503030a0f080c090303040305060105090f0f0f04060b1003091104022107030b060a05090405010e0402010206070c03020c030d020705190515090a1a030a0b04050903090d051c020307030305 86
    0x7015901e02c21304807a1800a0786130541215058003070382170706400010101600c1e041502e0400441d140d1f4206038010307966948080010000c40c204130f038285800c082c01d0a5200481d180a61001d01e0902d40039001481c011985000901440400d60000c00b08550081039010115556203009000d880403060076250100411180c40c014605032080b01c15140403210709c120a1454901071050030403009000c40305160311003d031039001d59140070040c2841301a54440640366038000741400125901604018410025141403101507070700015055803220451605082c043c610345000ca00300311041c0706003601403203050200c10403a90040760a00507140b05480c820b800b203014072000740319401c443c46100d8000758840380e5a8404c4c900d54000f41208100900041c0d0789980e2903070314007407160075840388980340760000c018000c0005080c042c030380601d00e088909001c0c1e42441a03c0175100c1c85030b4886d5600c00c100620300c100400005000c501c12080c1c00280f016408501503201948943c03005030114002450000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 333523237 1250 333521987 333521989
    0xf02090a0603150504091104090b0a0f0b13091406010803180406030b0c130b04180f0911010e0f100309050d030603050607030e0c04090c0501140906031b0403140d080105 74
    0x801d103800c1c0f922035070554910500c4e2000340070060031000410b035510851a000042980c45900807200d2503031144060700c1c0c080c5040c1d10908100da40380004621028100b82c443d820b00d684400014016109400c000201a20f051621900c000c1c20301c0400b07011030185400002d041c030404000740c9400005038000c900c13140b00d4031080100b01c4071035001c028540001840410341e004442409001403d060a140702c000e1501c404207415550041d82c00002014071204404486030414062014880c0d020743c0f0134050b0904a5445624a0000c84149410045000c02c100c00d180c3d2142e41c0c0744080381c00030348026004041c04130001c020b40b00c409420f451070310913036126406062292154100b169009009003e040d03c8444080f000b030042c032a40350f10940314040c541c030b81507911403007135101c6d1030711695030410100e14000000d0300007590346026152610044c0070729110741e100c10080382e61180c1c0d06400702101c0440c000012903a4081c0e9000900203410b02501c0c05021000050094484200c5071240706050380d0f071f40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 333524487 1250 333523237 333523241
    0x8091003020f0f22080105011d160e030a0803040602070308060307120605060d060c0801080d0f020303130f0b0a061a04080a030c05071a030a060806040c0e090a02040f02090a0603 78
    0x105030070380320b28803c2103100c8041146101074402c9000d05030502c9190200000c00e04545111504100c0ba26595480108040d2211880c81400c840c04024407d54528191102080c001e4000442c0400d21080381800565617605002d0303c42455030242450b0f44071304090401d54000d4000100490100307010002081042c640011442e04445480320a00001202a030320000500740180c0b03142d0b0059805424000001e00c079000381302815085a1742e10003198035000300d0700c1c6010050b503600b109200e10070720340590659003c0100c83d484445c2c2048074102c06001c0c54290941007010002600072a0460103019403c030090700f007282101e030804203042c02d03101c1c511200b641e2072195115090301c0e6070208680d100000d0080504000143c0a582a114601c0c0c0d11a8400d03600403540c22030340c03042c407800000c1007070b101228460480602201001800310b864503503502a04800c0902135680e59103481c80c0010407119040024403001940500103100b101e400d1b4a054002c1e4000310051442001000382c0401c1c524802c1c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 333525737 1250 333524487 333524497
    0x11d0c060a0e0609060a0e041d1506031219030f02090d1401090210030902030f0606030d08090f070b0c0c240a0519050909251407020406030809100302 66
    0x10200c629108003610152514200000002e070000d80501c11000699a00001703443c885140d0384461040c00d101c0010482240e01000d50540704012182e000f0300a04400a03841c055072040e070b07010f40d8041e00e0700c20000c0c0c07401c4004186500c84080028a50b01069042c1500c1c10380d0701c000b51800c5c481d20850078100b0060b40102d5902c075420404140c02d80000c0b0305d241005410801c20030000182208542d00414920030300a9000c05c04039071240c1d034040450604000002d44200c424001d800c041c01e00350000794913108020300c01c000f00910305000c55601d44007070002c0804601c2d8081110191962518210711035000300000c61b4440c042c0710784021341800e01c40d81c0c001c4101001c0480d1501000c5462580c0c20581041a990302008000e00c840b2a280100e084020030810030307600c4060710342d00394004214420100505400040070542003207451072a0030003414050003241d09017002c00b02e8a203004501c05001e2408040d50003814490004140407070500180001242560580800351101c80107405034030807 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 333526987 1250 333525737 333525739
    0x1502011103240411090109080606060d0b01051207120f050925030515010807120812061c1518051c020c1525030f031d01020a02011d0c 59
    0x2007000054600041d41420311003480c40e150507151000000004602111003d0020340003003000010a0741ea00d40e0402121002000c11000034240d62600340302140070342c0188107041032074907198581d0445c0c07030b8010810780b400000015810300d00b0346010b600040201294180e546262440c00301050881003150082911a0b100c2c0c400801480c5041062010441e0b0a0b40040c00844404100400043e00500101020040d03401100100c0e5042c000321609087c0158000d565172005187c40310b00048100041e25a007400310104064143d603903101059030084c403010a1401424069899001c002d401801c540d40300780c0c1d000041104443c000c2000c00c11400042c0003402c69800a1003201a0315501c114000e800c0c0c00c148113507001c00c4001004113605280411010b40a11404159921050314a40a03400d02c00c104502c82c0182c0c1500da10060b10351950b1085142c10951035043c0c000c00c18002003984190211580d008660341c1e1050340e0b00034002d0080004000140c144807011000d074a0300003d4803e81044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 333528237 1250 333526987 333527021
    0x70518010509060f0301020d0e030c0f0303010e0403030e070306050c0a020d020609030d020c07090c02030d1107030905132703021c1418030318040c11060c1606090c150201 75
    0x83d0702081204101141c119568550740030400503603944c00c14000c9600303100081009684a14205280c6810f103007a41800381d91a91051004001250100c0a210f400035014100010004444400d0b1818000c0304c1d080a42071a061106100790040c141c0f00802e80c6004c0d13542681c111401401049031074820607200502e1641c002d010390030318a01160700410510072002e003114200341d501c000e00d1098640c40301880c000b68002117000088001d280c0a20380700c00885140e2103251000c580d8025009003098004d15000b4041c01400d04202c60442d800164900d90040b2504070998142c030011034a041118011001406610160b648612403d040d001503441d05031242c80c0c111f010740d400030206410a01d000d2103e9914103103250b0a0b510240000c07c10060080d0300c1d2110380e201d04d4107000039202040c51210400c55500c01503400305002040d500e4106210312001c55540410340c5905203503240521000d4552498000400c00b00441c200441e0110ba50303c40c3c111818100c0040300360300700d60040ca480c2c0b0b0054 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 333529487 1250 333528237 333528241
    0x60b0a030b0d11130b030607020610060513060f170423031911071e030b01060e010210020c01090b100305070e09150c190306090e030c0a020405070309080705070518010509 75
    0x11030300c4d14404c1400b0b02d5a50000591a06000c00a03245c0340c804e503416400740e0050002e001e401504030035141e02600b03150400303915145615603400c1c03841100e440b49204106107200d035200c11900c200c01c08101d0754002c00c2500030714103050814450a1707051b02c1c5030b0f44085003190110b1140b0f20021041c0c558203002c2002903103841190a41c00c1d290448800ca0310303501401a80c00c041280313180f40b1803402d02c200d4a80814910141589802c0300440d606030088420b11010301700c5048561303400241c1010300c002c3c0704d00141e10340c0f035213480d0280900349502c0c00070320940281041085071000044d030501200e000d4000c07101025920a003c09501e5000e40d00500b85d0340096401013581c861010100d0f81007012005c00c01e1a00c50700c0400030403c408000c5a0b40000780e03d0b5002000795407002e000701203200f180040618500312030307103000075580c603010311009014a8861000a0701240680d010903841a000304007a552031520785802038907101c040c0152481407111440d540001241000c40700d05842e40905800c3d025 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 333530737 1250 333529487 333529489
    0x14040b03190206040806010b0d0c0c020f2404060c0c06090b030f0403090909080a030c050f3f0406060f230301092a090504050706050705010e01060b0a030b0d11 70
    0x16404080c0d0f000360040000080c2c41c1c5007003144500800702e07105015181d50140c00110305541881c880c03101085244c90351400580c3d07407007a5410000400321101c1c103442e81034a40300c50344908980c0c1e103d181c002c00803500044c69a00304a280700a54400c07040700b4181c5882d448103440820560050341d20300c090901c002852170340c0c03010345107030414040c0c20400429942e8070401c070b0982d514240111107844012030302c0340c9426014060040085818100035090005880c58a0aa406000c04045612810400144c4c6e4000100c0d90311034027420401842d11150100c00c00341c2010300040d80c04175100e41c41d100c0001440107032800307100d0a85008200c40d20741030b9000ea0000119210940d10503031315540c0c86c1503040c0050207848500d03034464002461044c101d51010610301da07090850b0322080c4954105800c10000a03c049400e006544280c02c000382c51340c03094204030740100380030743c0300600d10741c078007100401c00075100d50241007582d811b0360301880301d54010010701c84009814030005080300e0414444d0301d12 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 333531987 1250 333530737 333530773
    0x240f0907051002030f0d1e06060e100c0210030501060f091401050304050313030c061d1809100f0212060f0102060105010f0c08270319080901090e07030614040b03 71
    0x800b001a00c100c9040c01204140c0103900da0182c141552800d030b030f0303262031120b0700880b003154683e9056001d000c00c0240c2c0303001009045a02c070550f0052161884904c00b1a50601803a203900d0065009000d12840c0d007128400540144020302070203021840b80030a030350349030703110b82d54400c19101d03401e00308031031030b030a0100545054201400403903540c0070030f10104810407140e10105e00158000c4000b03010081ca08030703000d40812000500b86440b1803c4a1441040b501c800800350000c00c881c0c0c7c0c0d117641c0c2d0741c1e600c8100c034203003090801c609030040c1c103250001e020400682c010b0302c0609410b403c00380894076280100259640069407882c00358006400401003580501c0300700b581107503c0e0500710302c404500d559100c116440441d00345000403424855a000703d030310340b801d400d50003030680040c241e003001e491802403140b0000302d004281810008510505e64803441400c40101a5100c4145560800032005406415070303004054a0382c909003207202e220b150501801c0c0610002038060071960b441c6001040b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 333533237 1250 333531987 333532009
    0x11707050702272503060e0f130b0708100f12170d150e0109141504020909090f0c030607050406081305070303080406050604200912240f090705 63
    0x446450051542c0d115405000b12803195210911300040b010101400500366201038407a40101860010700703100c000106a00030f504500710000d1103801d951500c491009292019000030400c13441c0800340603c07240c000310654045d1150347d142081d02038843c5031071030f81403800b1300c5400e0b00908108106400f00302400180c0d41c1901c0b0801d2468580000b02c003503003040c2e85186060703c082c1c5800d107070104400d50043e08480d001d4400c1250a00c2541007404514241c41406849849400c814000d824941e03a581e9044480c00031001e081d05a20707141103a041c2e0b440d23110080b03a1031054054200b10211518020400071301c51803007901c5242c2020f08015044036003e40084c6000112401201203002040e8208480c5005520075507680440e45403174580982920805404d242c055414090031207464198040c0d08100400c003240510b446084410019400b001e2100c406540c602440303440341c09080c80540c40740d030a0210200300070ba403501c07410060000e1000031121310036581c000700380c241b2242c600031800c45 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 333534487 1250 333533237 333533269
    0x9040f0c030b011217030c041802040302150a020d0c0b13020a0906080105092109040203061f020d020d0806090105010c0c03060e100b040207120e150d0209011707050702 74
    0x545501d035552540740010a81026021860242810b81000001d1902c2c264407803660042d24198200007410340a1030140d80540b02c072005403010000350290155060700c004607001040f0b230a04407440030f1a22515030008503c00c00501030075801501581c02031106e135146a47c003110703a4581c0d0350b0b405504030200b40901e00c01ca83c0002c44c0c08000458600501480b00034024480000625042c681ca00e24541441c60700464404c1d15241d000c5541c004425042d508030b588195005680ca603030b4500080c0304001c041e0400c00c140701001802024513540092030011002d015000c0303890692003c081581c0010084841c0c9030b204c840400140000c2d403245a05106407031160351070302101901ca50303410054902003504e43c02503030301c401740c400c003500315030b0043ca100907106803021407805816403a080320841242d0800ca0034015102c402c0011500c0f1000b0013801d1341000d900e850b4880420b1040c1e180a5400404c10500080c01c0c24401003941e200c00ba1514060f00341a19094034007142d541c24412501c051980394 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 333535737 1250 333534487 333534503
    0x6030c120e0c090405010509010c08010e010e06120114040b01050d0206040b0c010b06040602010506010f0306031a07050409180b151309080d090b04050f030406050706021e070318050f09040f 83
    0x810361903c1c0c1c07000e07007805544140c002265a19080c6107203800c603003882e05a0b0042000c00401000741c1424145040c0c190b03000b00c0c228a000790f4844001c10841303039810150212a40c030f014110071a5040c5c280740c450183d031060000410590340c0b402040200102c03110082c1d070012007040304108001e03c1c48001c0450a10860010810340742c1200011020b4120303900000c0903075110000c004c0e0030f60703020700024201102070030100300150031364942e825243c0200b100220500b0622003c18141405501920001c0500b018240040c540e07564140381c124011203021610015000c010840d8000603514810700044040c15040042a0600c0d611010f00302c00e110584400004001c40980b49600d800384410060040b03c01d1480f0b4201450031a1508005007001f00098000f40070902200780e12000f11007034950081c0001d41c444da81a05510b07a505240254100f50f16000988031081542180c242d4440800440300c3d0940f4960325403d01c150b021030301c0d081c80c0d03009481170000340005685d51019140c081c018042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 333536987 1250 333535737 333535753
    0xf0306030717060415050f0a090f0b0a060905100e0415021e0304110901080c1216060207082503060e010e0604051c0c1101111216030906030c120e 64
    0x404400d103407480440d00155040f02041206111000510289501c0410401c00a52400704a40c687c40840a0301c1c0d05480d03603c0780055414002c00c03c150149558100c0540112070030074030402c0004004a03c203d1180f1402c00e4002101085246011012104026614040365507265a083c1c44100018103060046900340402c43e5602402c0401301c03405005108615640c0c102030070301b2421201c541c5050351080d2402401842401d0f008a071352f00041105a40307291285004d2a42a400c1c8100e8207603451404510600c0000c195030700044c400215851300b800e82d0a09449550402094030192486041c604030780c07a010000500c00e9482180042c0d507420001a01c04003200070b4030f04042d0181c0d4289d400d54812089200c0a4040c464540c603094070f03608110415550356902d03c04d00441405640d0306010b404685c06200e0502480701c00e42ca0b025240c4038980d0b81c906290101001c00540c0317000c0d40010220000480c0c080d01910030158205c003e6182e44203402e842051500240c0310b500351820f094000e10304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 333538237 1250 333536987 333536999
    0xf021e0702060a0f11160e060d0c0608061c11100507170708040e0f060109080d0207180b1c0528062d020304020f0904030816020111030c03040b09030f0f03060307 71
    0x5042c007890300a08003134292500e1f142e0300700c020b8034015052603c52030200842000094030211148103d030780f81d08200500365504000108a0910b04c510a007201540644a400b0001d11505000c0500c1044911061510010404441e00d0149110040c500181100107407001046d101c0501000b51261700311b28a040d44420b0103042401c82528801e80f03805411090200035030b00a00e460000e4110313003004100389005100700070b503504100c2c0310384003c7d2042002601d1139078145402c0b2484080026142c900d001e2010030a00e01c03100074100003584c3c607008504100074410342840d480005131a55640c5001455a581c940d040200002600044401d0600c1c801192044201855600700d0b425010016260315041c01800340e0034010f080c0003486081b0100c20400041d07088400140c000405010400c405100844160700501ca4000b030060a080c011040060020400006600c103d10407014040a91a0929425038038002c089000c50407060070702103040079a0100c0c001c0c2d640000024100c80400381da0712 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 333539487 1250 333538237 333538243
    0x30c0b0a050409091b061706010509030c041509060e010806060303070b06090a0e0607030e010b03161a09030102181903051c0e0405090102042306090418060f021e0702060a0f11 77
    0x240c495001f14024502110170101600303c16580941c0c207003046032804140000082e00c4100740042d040c880c903135400a01020640482c441001b60074010010050592070b954004090780d42489143c54078401ca0000802a04010054580c1d05621042550b840d0f11150100441a400100f120a1943c3c0c0e8082c0051504403c1195a00440075078a001a4000d4400159405c1d501e580302403c0c005d07840f40c0e0000c060f81500c440d025023210500341c0c0310500c6070070b01810361038280b0a91072100d0f81507001040007050b40440409401d20300004650302018910021202c82d90301c401c40c8005071184e00102e82950f11940e14001d00101c20500d4644a00c10031540d00014003110001d54080029030360124040c82000711030f91501031000488a519850b1440100004859106001c1c02034041c81d2100242c10112400c0010400d2069000b80280288000400e0b045d0003500700d0007011900d0004003007409000b03079404084803440f60f009460f0380e103001d415410581d91541c5194055040110b0411620039451041c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 333540737 1250 333539487 333539489
    0x12020a0810140303250209280203040519020a27140403120e0a02090907060215010e0103151107060e0105130b060607020f03030309100b040b130e120d06030c0b0a050409091b 76
    0x1403c0ca41c654900201c2ea0981c0c203295002c0e05042382e510410501c800706100040d12140701000f014846458052480480da843e142540b05107404e19503401c601903451100501c43c841c2c48811581040001c440801c0b0310040c0030156005008112210010f0300c141596400540709204c0c482c088502c160465404100d19000031a00c117825504001400c1c4966039050041842c607100e1803c00c4111f6504004540342c2c000d9040c80001c0885000041050720303030b090794100d0740001d04004c40d01030b120368240c14040054510011603c059502e0b1900080350b1102e00b00e002d20f51690083c2c62041c442e81c4100500c040c13a40000c509aa11105081d11038860340d8041009500c02c550502c0034207001c07000742c8000c0c010380d164241a18882ca0070810000c001e92190b00742d03410704410141000c5030320070b6252103ca05000c00d40000310007030781001440c90101490341e0012400c0301d02c03074000001990795071503a0010178060a014200041c03004c1008016600698000840c014000c01601c513005014849140c04103100d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 333541987 1250 333540737 333540751
    0x9040b06040f0815150a0b0c10020a03150801111806071707210806041a0411091203070314030702190308060108070c051c12020a0810140303250209 65
    0x12403064004030b401d00344203170050400440c6070300c051041e40018201c40c05600510049002c040b4402c0e42c49207080240301540c500c6a4011540d035208608010040c045481280303180c10318000b80004c14800520841100601489026007000042d481201803c0c40c1a02103070380c045014407100010503100c1c03160011270f102c0c020f180380d950764051a01d900d0904c50030b001c030912100d4440343c444596400c458034903031022080340d0008200c484c20189007090fa5001c240300ba0050f28081c1d0001c1e40d40304646c0113280f440030071942040c503c1c1b04864815a2840b640380018005461482c1c01844c1a071000040c40d00920340d1700680300d441107421240b19011134821010380005020748207000d47e5503089200c09030480c0701031428808030903143d181d07d50395901229010050a804125800c8105c0c802ea072003062a00799008250340e00c0380818802001c044040d541e18210784a1100c00240c941d01c0d214900d51400c401402031400c240000b070059034102241ba01c00614a600c8070012001aa12002800e200e140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 333543237 1250 333541987 333541993
    0xd020903010e100c0801080109051203040602120c0409150b0703110f0d0c0614091c11060903030a0b030318090406060b0c060f18031b0a1505151509040b06040f08 71
    0x2111341c00040c4403940c10f900c440382e2645058010400b14101240340f0001e1551000406c1c0e99840707610f0140300034400e00c00880c44960f2840c090000501c50a00104100c0d0500c402c10310a9011003011920005d40c0352040e042c0994080001c030f0000307402070741303450a90040c09066410500c8486885810101c031400307901c0c0000c05100f0341208016840c4252096500801900d00c0d5030718000c41c0d110341e0313603000c2011684170104c0304060709260b80c4644035201c607000e02501030354940d040200415a40703402c2628090651401c11400781e21764100003003941c0b046c100e00e880d000f895440c0e031404d2203503900d40504103030b1303106817070729004503018440070018003250321020018903252400403010a48002c0280809464101e0f02c0405100c0884c00000e4800c84681c26440100e68240c0c80720107807500000e224014090640034070340301c00d14190b03680403500c00c001e94020301e1000341502d420403c018407907c203c2d145264003804118081c1c2010350025005403000b404041c0780c280c85800040c49250706500040d4158 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 333544487 1250 333543237 333543251
    0xd020111030a020c040f0506012309040207150e06040201050703050d0225260d020d060e0709080106050a0f1509170102041a040b0306010804051603030f020607020d050d020903010e10 80
    0x4113051050280710007841100300400d00300040000c20760310740c0320103190803400e44080e665000e5160102f116002d0800500c11907030340c040b5140c100000a210b81580c041203183c100707034102f40e5030003003951481350368144e44281c036142d900c1c0d4040e54180c100d28141008550300b03002504003c0c5003617201541c0d00306a040c00000006240c03500940006210402088100350b00343c0c105100c1d51020207580202c510144013580366200440100d000b40003e83c0300004012408062111581d00b100c004426500d5580c024400c40b500c0d0028809443c150384602d018a40040e2000c21060003048402e0707a0040b51468050f84460f51154400c40c0104102da040146035800101041400200c448680d07030504e02489440c14203240c1181e90721140001400c0d00d0620141c0d0f80040d00700304d000e0107184201c4001c00002003440d9101d060003012200001e000201502c280f1000c600d03054000124200001d54580d0303034a01e04004c0c220320002035008030000ca905592a06005a0a007400f40070000743d95090000c00603101d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 333545737 1250 333544487 333544489
    0x30402091803030117100203010f170c010e01030f240f05120a1403070b010806010e0a020310090b0120030901031d060c03060a150c030305060415050d020111030a020c 73
    0x1140107400c10030380403548407010a07a4200403040d6411280a132420314410441240d000d03080030b460840b0170079541d100100101d0005049410542504c43e1040401610b120700e201160780c603608481400d02107500c0864206081d80b0079040742180c0000c407040801d00c0031262030110200c1e452040461441062400d0501082800a608000500044401e41c050350000081d003a150b03001c8040c00f824042c480c00702d12807070b13000c10402c03140c01c0e941c440c41900e10356075580852500d03110b080c05880403285170b000109058907924000e40c2d009600c03408030250464a070107110700c01081452003140c144880c014141644d04242c0c03207084c081c01031500295035928280c10004044902c00000500d403100d039600320b1706080381b0021300e06a020301d0302019150780744c03141030004207000030950208079468282c208a0010070303444111030004034030946083c031640e00e0b29010001a41d03000020a004948444400c1080c0c1c50450002001302d40103044c10300030b02c00d02c00251800d503404070340f052026074004001c440031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 333546987 1250 333545737 333545749
    0x904240c020c010f050f180d060603023a0519080408010b010c0c061215060320090f06160501020301170f011a010804020112061202180106090302010c03090503070b030402 75
    0x30b4200346007100200340a003034060594003884003245100307280440c41082e4015115406005100c00a00c82a1269550714141c2d018054a000481c09606c02400201c48074119030f081910450030200500071540d48070a1440b00c001400f0030030f0320544200d0325030044011105c0844405113001c0c0441540d0340741465211402e543e44014901e0400200c81d03103450102c0d550818090590b1f05034a0401d0465202440680c090000c00090612000c6881400142030341c2581c0b0850307043c45402c260b00241109168105841d000303090130309030040301101c02e03980d00c0e00c1e2540042141b400c50382c7c0f0652032550b064030b031305089810903001800c075000350208030768214008204610764000704500030f101d1042500d5030807510107940441c29051202680205003160b000b060902002c0000b03010800615a441002e2000c2c000280002e9014401c1b00310314802c099032011185050310141d4030740704001860355004442c0348010721010303401c21000910100721603806001c524001c0950031401070f2203007018010406 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 333548237 1250 333546987 333547003
    0xf020a020a1403011b0e10110304060504060314090d0c0c091a3a030e040e0303060f011704110a0308040605031605030702061906081e07170c0904240c02 67
    0x49170340024210440c02580c40761040286400580300e46172914078618084d070784440c1c19002d668680c000407602141140d4890003400441e0141d0b9000d00c140401585540300084090307501c192143c011100286180c3d000325072200059124003d0b6042e020340e2090002c04540f200041c00c4400c0c44916100105460407a04c11110901da11080340c0c0f03031b540c0c482140d40c081c0302c0c1810012060850003800031306140c054040000e6078440074000788045180c402102da101d40c01210701c0ca12469400700364400035485604105c000c40c2039000d081c0110b840c6e0341c0301c0407003015003401c01a50080244402100041010014000408054484a4482c14820440d0348100c0042e001c102c20440144104841e5a44c0003c649402a043c2c8403103c030321802c0c0b42541c1c00685490b8000d0240d5204ea001125400038a440413070074020840c40540e04510340740d04c400000c0702029074416460b40c0c003005444400d407810f48166a0020310450840d01405182d070104103013002c900800c890780c1c0e40d9030749408420035010f00c030303610b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 333549487 1250 333548237 333548261
    0x5100b041205010e1f0c050c0a050d030509030405030303041b0b0711010201050a0b0d170f04120b01050904051e101a0a051c030c231e16060f020a020a140301 69
    0x440b405e4444c011003801e1407522150f900c0181c841540010550242c4119a0440076402c103403082900320742802542e9403501085000040c0c035110028884010200c02e880a49100402031403450b00d80c0d407281c42a070243e896000c1e1032603601c501c00143ea080d29500428588ac843c034550882d60302140006400c44200a04034071059040c2040d002e196601c82c01c4802d24658440d0808180c01880c4921070601c1c0030302105281007040004010036000e0850342c482c061244500702212580c3c0e2104184050585c2c152001003040d44048c903c040050380ca091100c558130108011a01c1e6281d000b44a801600e260712408500f004c0400114403450401411010241005480d0714000146000914607102c1e031258025080240001b01c00d020400110200310800810b090380001e0401d11a104a84a1401200046d01542a000300d0704030b00c1c001142c0007150300b00300d030701401c1003900d854401e0303d80d102c01c0d903619011400307208044401039030784040c03000c050a071400b00c004c0802c200038141405c640200c1045 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 333550737 1250 333549487 333549493
    0x70f080604080406030c030b0a12020f2713150b040e0109030206060402090109030213050105130603051c02030c01060905061008040209010b0c030708040b0a17060a0905100b041205010e 81
    0x402c04410803602100c08030700d00002c00300706100d000c50081c642e070b91586a06c0b1038905800103c45c0340314070415011500845002820150303400402c10401d0040d4801e501d5650b8000c409148a00d2089c045075100c0c00384d200c0840c4e120580d5481c441444020300b03c00000540d500007680b10350516200b40b990114a44000300b240000903200a2340da00d90044c50740384140d400140846407a48140c040100a643c041c200c00c04074603190592001030071090180c0707070144103002c0304854024000d0049108030f0380c019000e00715020040c8014001c250742c0c0824001944010411003c1044092142000903d05d112001039142007070004c0204020265200e0307004c0106040511002da039402c2c05240c111058045055512100b03240001c0c114080d04038042c040303003004140010b540703c40200828180c03031281d4410500020f2000e40d0b106080c030030f44171581c0001e4119003c0c040e0418a034000d980102d004041e919030707503554000c2c0c000f180d409a000380400000144414080120034020a14581e041c003001d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 333551987 1250 333550737 333550741
    0xd030212061005161a09240a0b0604090e011512060b010309051605031e031c15060503041703010b03040b0901020435031e1804181a060d0605060a080609070f0806 71
    0x41036030007e01a080804070f101005000ca02e01c42d8082e0b1000e00010806080d8079110707540c2d405a2402001c00712b04210300c075400c207080705a500320080040816551056030035006c502c46503d60200074400e006a42d4181950751442c0400b0407402c004200204050b40c2e40007056900344403d00d8146001103407503245001c202410001e0580000c415a80217420b5042d82e66a20b21145010401a00440700700b9200801e5051020808036070110086124034000d600c060300c0e5800c0701c0c2d540352080c40244140c0440030800c0c00420005090789450700d40000d40c100c00541050f4440900b10555140040c0d002044032403542c4203048440c84d84040c58100c043d0030003030b5033885850030309252648121090082000800103203800707246018102e00c4000203014008020660b030b0088030301000040380000340c1e00c0a0b20300171a0108030041c0c503890380c032921025113501041e400682c0d56801429018024641c444c80b03062020600305400c000d5580309a0000340100340c0f2610303003120752601602d181c0091340d458002c0c0007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 333553237 1250 333551987 333552013
    0x16051f0b06040608091e07060207050a3002030708150a14061519030b0f040c20070b0c061602010504080406200a0c05030d030212061005161a09 63
    0x42039408070f6105082020721a6030340d40040303081c00601c1c0448864842c2c502414880610002000425110710b03400b150302c2c454403501000404800381c440c21040c0c40701000110070010001d4680d010407894181c0e80514048580e0000b0b04000355900410000d601108400503c40755030300c0a141c1042d080d420410441880c15007040f409200200f2150103000003192909820b80d2503011296100c04d40d03448490302e402084001005001203c1259202d4420100c58484501d40b82c03041c5106249942c03502003e0407038075118900c4003050740c41008010b01880c03070000b4144d60004018200c0c0715030171014000c01e180c0785400c0c0600d4101181c007002160324240811001070301f401d0464098030345a05180d2012480c4106024811030903403c52689030180c00004070400c2202c03108841940e00c101c0031b0301c81e1035135440c5048080340200c4920038043d00509000c203049040c9a5400c8104d1281460154a404030744540004002c1480408a841c00110b101050220441e074408076040205c04dc040c00c0d074506090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 333554487 1250 333553237 333553249
    0x20d030e0d03050415020309010c09081c081003020d0602070c0b0a02060a02030a0902030a12030c210c0c17090f0105030c0702011107051216060503090706080c16051f0b 74
    0x2042400c00e0560f10b10100e030901c5041070660708071140010781955a4601240d0490282201042c1c0001082040c5004a140c2e20007060045001f03e42401000202c4820750040302c5659000c1d21540b4502c819040100c050f80710705141854a500640c40035036030b07084a03c0d0001c1e00017995800341d440018180100703040b955010694030f80000c050706002d40c980d102c000c400130040801e124000d502d1f10480b06010100811004030740580318580d1001c0240090109003038400e14041c02c2d08080d0100c00c840d01e40c485541d00e034000c8181101038034210742018496907846480b100a0140004140310102c0c80240314030702201e520340f05d20005c0c40c0a9055003450003411000d0f00070000028140700ca440c035801003403403041041c1c8000f008014000d600304020080d045071600003014048010510310800030400c3d502031f130104c81c011089080202112494500111050180503040c0c140302d5004000790f0702258102c025030911940110060038040690306480000c9041c125500c4035841e00b05412200169030796 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 333555737 1250 333554487 333554503
    0x30108100b0a23060a0224070e060309010906020a02061f051309060f06180b1e010f02030c010c0f02010c020c1f02030705010f23010503030706020f19030507020d030e 73
    0x1103200111098400084000c04070388800d12150004400300e41900015070021f180c042c840341503032100b0703e90401a0601c11100c00111140301c042160080b0704851403c060000307680c4a5030150002514140c0d03a80c0b000182c0e80300e4128140180e020b40203000d4001040d0442c0c11100c60344449274100031b450718000c984142c01c89254400da0b02da03500c0382041484856000040c075a00240402c000030f9032102d002113214040340030040300c01894040c1140d800d0410010300094212410075882c88584424011603580d104c00c0916021404103101c8240b01c00003d02810342e400e80d040c1c43e5030040401a00009003103541e200b290808544c4882000c0d00c854403a905102d412840c0c800d03520302510218801a450b611070801d000700f00b07601c5e1103090b0502003c3e0b6070110044250391080c80300c0401c08805418000038007802981c0d4507400411241c3d0003d18558000d001c0c0d202e40304115410700311409517000031081001113500102c0d0725031041000c00355051003c140170280f90306042000e42041c145090b602c03040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 333556987 1250 333555737 333555749
    0x7020a0c0e1302190f1d060f190305030a12150314031c020301080d0203040b1c06051306080f030f04030b0a06030b01091413020d0f020f04090503030108100b0a 70
    0x11110104220b6000b407248103142e203030040d102c1d02180d07101404505801070700b88030304440d2003c400b00210340019140349000080c1d1004a040c0c8154466508004804d81c1307184505500c080302201414410350303c00043c1e0300850042000d1a10358030943c001800d6811007114001180c0e10f4513111444010071007104409032900b0540e500c0006152042003403442c8246074024845070404800881d4018550300254161800f84040d14502c0b024620b0070f070784d07070b000e140114080340b201444400c030802041d141c2c4041002c40c3d00c802086a990b0303840801d040c1c101c80d0180c0d02c201a06c0d003809100c00901004038800c6290904011490000901040b54460045000c02026104008082030000d02c103074210320003868111001c08182d5035541180c0c1c00a1144103000c203030403c11400010702089111166080854014144240581035030f5944101000701362400c903408000c417035425501d5200d0703110b1a680c6512640c0110b55079410702940030314107044104106035903420940345491a0702c45014440842d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 333558237 1250 333556987 333557009
    0xa020306031b030f011404050106080705011704060b100f0306050f1c050106090606020a11010513030b131202070e13080a110c06180103050f1510020114180607020a0c 73
    0x600d8000030b130070000d207045250f42c0e40d0b0a05204170802002c9004c0c940c011407146008010880c0d507844030b140c452685208140c0031507480e00e19000b07412070000307540c0e901510400c800113030f50402c0c000007010071066036661000290001d201003800b503054480c03c0c0c00ba00b000c03075035403018000c44000503481030400c2003800080486e086204080107402d4101201504030f0060501015454040c02507880c207041c40255084400743c0680c0100e94014400c5540e441850450720a03001d040d500e80c0955400082c0c603000b004021080c0d1240030800035554040c1258166003c2c00342e692270b050054115403005030002460070511820300c80000c10880c200e03000032a5a0800341d0650b84c1e030041d12400c00040c403040e6034000701d002400c4c2070210400c072065070065109072810001070300c842096003031302e9008852501004a00d810844038900c0d120130310103554a29840007141500c691007080302016001d40c3c0e101018040100e402107680810700480380e0068242c07009050244c0580c0358060012002c1c132500d03003416 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 333559487 1250 333558237 333558283
    0x1b030618200702032a090f071209020d060609051b0c0c0108090703080f0304120201051e13080408030a091502071a0c060708060109050102030702060906031302130f050a02030603 78
    0x1484c2408a404241010700c10781c40040000c244d8050844101981940306000703010014004000d2482050f02030700c01d90b91340c0034050718501034140003004102c20036a800718428694000080e0103024140103403000d840041014180348180c0ea9003601c141440c008880b00a0058240d458000a85001811401d280030031281d01c48062550900344d00c0d40000e002104000f8680559070f03da00000c50140d84201c072803101488002c0002c90880d402510740360401c422048100602041d5980120b03000001356854061804255956000fa68840d5002001607007000c01c048002cdc075001100711000300540c0c00024a81c0c1c510100013034803410140560002660440f103007910102042050f03503038500c070400860381d0a06180300e015160072400c4414500180a118020505501c0170094882a66010f8481420f0000401c2048915000103000000f030606c555400b0025039a04400354440c000c1c6218002001c42e5040c0050041d62802841ca1700c0f498010418455183c03000504038030102074500d40000e0903 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 333560737 1250 333559487 333559489
    0x9091d0c04020d061203260114132c0105060405060109180612030c021504060203070b06120a0f05010b01230702030c060301080f0c040c020607050c011b030618200702 73
    0x1400e032500617489442480c181c40c02015045581200e03204441d00e40d1000031041c42c0a24090340009004181c8042c008001d5500c1905007450700c003000388841c4802081d11207a582c2046160580307100702c51030303a160200b45220180780a01c03c1c00d411584c181c60900c0340349001c4001810980c528454807000caa01c000703030000e0143c680da101c0300190030501400c0c140003000d0b0500400c01c01810720180e01c01c64803400c41c103a62246030001c0710201c0341a03030040d40c245000c036140c1107a158030050a054200d006500001219801400301d00d200a2141c0d014034441c0300c072428030310308540c1c214031903d05201018003040d00180003082185100341c9a10803195a4002c144082803c0054610400d504014044000301e81440042440c103441c03004241180c0110a40038100b0054510040d596000b580083c004299003074411001007041008000002c500d103880c9980c0c001002d04841d1400002a9807800f0501034550342031150324003200c40c02001d00200e40d0855420303013154000101c01101850000f584021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 333561987 1250 333560737 333560741
    0x5010204090f050a0b04050402090a0c03150f03050f07063005040501021815030f06030f0703110a0501030c0215070c0c120b0618011e08030a09091d0c04020d 69
    0x303401401814460b141c04641040040e00065680e0030307005040403c80b81450402e071166900c1290028a4504d150304c440c51038000604555040070201621180c544002d9682203010400805002c00c00a00c07641c40c40c14420300300101c5489801958000d0541088050741c0a81151035190b88007080140d0403020103d211141e543d4503041505e02410042040140003040d0301526506900080601258440c003003080110000d0000007502d45c2c0c2c09002140042b1440d1400541c040000741c103d5042000403e8082c2c07410a0039801250200e0307042d0818003071424181c401d40c000308000c0c2001d109000c0e0125002e925203048003003440e0a100e40740001605244184503105440307800c40d8070381e012182c0700d20103a1f900620854054a40c0078940c0d01088585c02d1440340b10200c106401a81c0380182d08102c100da11889201e030218000d1180c080020520550a00040510030142d407260700e01585090919415944980c1c1f125112411042e41c000a00c2004070703064100d42c10850380181c5d520201814600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 333563237 1250 333561987 333561989
    0x2a080a032903070602010618090302031c0203101203170705041208030901110405030703151e150510090e0c07120801030c0801050606040b0a030f0e0a0c0f08030f0705010204 76
    0x3550248000e200424461260041e0826403000d034107031262551940000e074240c803000e205a01c20842c0c00d882001c2411440e5000c00c40740c3d442481030700c0c0341c2204400500841c05850b40c411155682c00020311038540c0c20121100000d2405c071600c1100140c0d251405031a08040907a0603049a040320002401e50b03200300100c1d000741c0400c003000c41c803100080c140606580c00844445405610f0594148044111b204c00e40f0102e6000400030641d90707003159a0f03551068a85800b44d481140c6440140da804140e131950707046440345c020703c001104000d00303072100c146c8502688824011a40c1d41481940558401c0e8440c0c1038503465035048200da162401d103080184541100500341452100c07824541d1503002c200703d4120303030081c60303154032854803088800d08035582a10b0042e031050302003100304100d00c595000f401c030283c01400e0018052841c0301d07402042d01c140600080040d00002444d034100100c040360312000e0400c00105005140c00c01c80501d0352880b851007441100540810316030b0402c84c094040360 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 333564487 1250 333563237 333563261
    0xc030c070f0b1f091503021909050103061a12100b01110304090203092404020d02010e040c030c030c09080c01181a070614090d081b1206012a080a03 65
    0x403030310380b030b202c4000b6190180206103c103050700800c40008010b00c00c0e0185241440704541200380302807640d03081140c3d0040402e4801c0c12030300d840f40c001070418420b118440c0250b010701c00128010380204201d180000800c1d0700306104000401c0ea84805010003c0c2c1d42d021801900e90004000c4034440060710b11f11801c04c0b00c040a44000500030444000c40c0d0003950059082c24100c621402201403030329401c0c10b10201e060303d030a030b41c0000980075180c58518018068018104106601c083c1c1002c10b069407141075403000070a4079441000202c544c03511030381c0d216210525058006a0a02d03548039220003c00c04800e04121104180b140340c100300001c2c2e070005203a055070084c2803090040d40e040070750300070120070f036140ba14002250107040072003503c49200e07100c1d00f0040c00d204200c4140945503000090203100c20040d0744006201640c10400082450840d0707140d1780c01841c80c004000400034912084411202646508800315200c0c0400060404940c00780442e80c4440020f017080f0b0007088001050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 333565737 1250 333564487 333564503
    0x504052502030c190c0506070b070e0d140c0f04090f02040f1b0207030b010f0305030a110106050d0804030c09090f030e04200a0206010602061306110906071b0e0c030c070f 75
    0x4480b159503400c40b8401c1a0b105405005c030302940c61040142e180507100004d00170005450000b26458420b298945083c1002821005006400d483d805032324a02d4104c1d25000b5806a0403080c3c2600e046480508000811074080c02140416605e003107000503000d0f40280202d496040d18148a41d064000094400880901010310440b2a06c02503031102c4511013a03908054420000c5500c1d80190070180540381c0110040d894218526011915a109000500181e560b11000852240d0300d64000c000c03100d00419035103807201d04504040b00c6101349079200400442c034116108000410f140590b440080d054100403080c11202c0c1c0108010304590f580100304001d11441100202070003001520060b030013135085820a83e01d815050340c0e110350039610079030070b000007140890004440da007202c1c060500c52286581091420008260150016a07085038130500703200032080206298141c5400524180a00c01810b040803c04c6601603c4050610b00c000e02c00040c00606100c29240c00e88502507000d50b503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 333566987 1250 333565737 333565753
    0x60906181104110301031202071503060e0907240e060f070b0f0f1b0c030307081b030c0a05070f0c180e010605031203072d03060504052502030c 63
    0x20306030040d118401200c03000c507180d5080e070580c203082c400c40b0050100a0b0b0880c1c656400c42c0c071000c0d02c000030711f031a082c21441182c0001c901c07010909000d6101d500c8645020031001d00f001e4003d1450358000b4a540641d43c094842004078140e8107400d2883e10790403d80501800340e1281048480400c840380b110380140000604544c2c0e100c6110040100a00500d034501c01ca84800e880741610900039074840740e011040340f0114420140d10880e0380004840c2d000c0840c40d040d599600f941c11608105e0348403012600010030041282106c00e001115481000300d001c2c43d43c0340804142c09640203843c01002006004101141000000300d0b03503501141c3c0020880f00380c07070b6440604160075520140c4202c009070415050b40d62081050250b41c003501e0b00100980300d4608541003013031443c1c10084c0180c0401c0814040380885200074032035403c45154402e4403900c040207074a006010b403142a804a802245402c1c1003080d50300d00d942d0a28030304501c07a03100e517120b400c070480700300e2550023140d4101b0320f180200c0c59 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 333568237 1250 333566987 333567011
    0x60b011e0c0b0a090b010501050a0c0c09060806010e090d0507080d0e01050703060f230409021c0b150603042312040e0a05010305030f03061906050a020c06090a03020d060906 76
    0x41c010700050b1040360144801da6070405648241e91203c41c0c024020b104240050203d5070145004d0a0901c049e4074001410001d1130b152152070f50629031080c0f08040ea952001d02107070b20180190b07409480000051401820414086035540010308500350030001c000c40d11307904100700c5100301c850100307803060203000102040303c140e80200b409070740100100c0c0c40d0140010700748a4071341d040422141c40f00310304500c48030880c0d03d1850071003044220a038071950390800c840060780d4503280010110354417017400904441c5845e150980c19409820100313851075042ca9140a580c13540102d035801030707000d02805010b40d0598018550360b900c403220340017680180c0610080350001200030300f080343d52259142c031190300d42040d203608440084c00040c066410802914041c2d00902c0300454000e413028000a42c100072440307002c01c10140c560004000035000080d40031240703604018045404c8001c45101d840c18440d0360019107011030901c4000d01031654420240c06002c1c4541c030000701d00b9080001401403510000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 333569487 1250 333568237 333568247
    0x27090606050a091703091e2707020606101b0b150109050f0901060c080717030702011a010f14120c1207020304030b04020609060c0d23031003060b011e 66
    0x10100000076481032800602c104c49002280842450038024505d04100b1030188100408145404039031500c01102c244e20315190300c7d80c412100003132005502540051050200c1803058042d00050466115004bc410301d5500d0515451100c410750805851840c40c1c1700e221101080c0c5494054605400e42e010416888003109201c50f240009a0303440c0c5030103031560100803040b581007143da90018140801804164010414658044d0240c02c00a0418100740c5d101c404140341c81c0c00c00c3e0f0b80180d0100c1448a041d03024003500c45800842c2030190140060100020f0040742c00c04044420010702100c00c06641000a00300d502800001c18421001c1c90700e080a000d10b03501240504010f01103d0001031209817020043c0c1d01501e42c403240160a5494603001c00c402a0800600f041e442181001440381501040040303290390466070300c0324000d01c43c0c420254400203c4ca02188500a242042040300417650300d001d01c0b00f0f50380d00284c0014240f840d00b004031f50805080320201183c4048a920500e125088 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 333570737 1250 333569487 333569497
    0x303031e020304080405040207020604090608010b120a0b07050f04080703050705011e0e060d02091c0203010501050103020f16110a030303151202100c151d0f0a032709060605 76
    0x19000160032040ca06a004040340720880e00074049520500080c06036140a80007002c1480c0005c2c100d5042541b43c0c0400402c40303142e0303842a14641c3d1b4402000a0f1810001712040043c010400235100d800010703101d41c0b00101006000702c003000f10002e45904d030100d403941a240580b50311000c884046031203191030f95889491340101400300340110b004070781004694807400d080ea9521341d2459211400e444c01d128240e0482010f0005084d000e1000c0d0300350b07441e111141040c40325240b05840721107200e030040c5801c507001a00300504042c0108600348404001d00c0458807010041510310f02a06140d04296503014400c4d0100c607803012441c5000802d061b40350f00811100398440301045252a0f0754030700314003030f500c20010083d007200708400e9140d1346a000b000070203c000c0c040e00c2c403008648091010303901200d2403007844801c4031400140c1e4440135242089520540880c0c900189140d5a046d20701502034041801e66151942c420406000c048840d100064000c1444046c2032144503156500070b400c80d008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 333571987 1250 333570737 333570761
    0x18090a020c030d1a0303030912070204022106150307091202040608011e0c0c0201210e06010602070317120f180307080c0f0a0213020a020a02032407030501030b071b0c030303 76
    0xa2844108071310b20340841200d000b04814802030496a6900b20240d129421101e000e070790041c2c0c00e008a003001c40442e0140000060b040c0ca401589282c200108400c181c1504035840d9119030520070003c500d5044074000c4161038003030b00102d000e1101480014003811030380d0803001c140d50810014070000d2000c2c0c0845d10344041090700c1070003440314489003154260b541032000390000d411000d25552181c080003600c0458400c0c0c0001042110796543d00501e0319074280d029400691002404005102840400c551800c03042c1c8121450301010019030088400050080440000060080781941d403101d03864821944443c0e081da6140c1141d41003101c4941c1002e0032030899401032a842000300b40011900c000d500341c2c01030688407010442c5203084025000300d06000d055200d000c20410150342c08100c031600b54203000e120342d0840540641480318250015007603005040c20600140006441d25923200d602007118907014500b92448100f000c40d04169040c0940141c44401d004403e069140d00b0402000c43e03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 333573237 1250 333571987 333572021
    0x20402070b0402011d0a05210a050309040e01110406051303170423030a03050a020109020d050106031b060207060e010c1509060612080711060705030a0e10030218090a020c030d 77
    0x140300102031400106117090642c0444610b00c10b1000c2d20f030091242003458541c1d01d82c11588507894140c0c1c0e15109101505842644c40401c442e99a885c1c903019094050203080000c2c000c280c00b511500703c40d03000b035001740f20502c2808521000380030001440000213580000480e02c0c580d25044082d01164864080c602d44841d000180c9410304880300d441803c40800640140380618003514112125005411018115500d0710380113805a41e07900e90100045003d840002707101461032500c609062062103030a108401010402c200054000ca03d240c00c4803500c3c10301c07240e01c1c40b201e80100da06400451004082003a100c8890044038110340c49080700c144101c204000b407a850340c011008405104400a284207400c2005c00300080308412074241c0500040c0c09a400c042c1560b56540c195000070762840700007040321250140501e0100c4003996100e8080c202145400070144c4030b5004000305c0725040c1d0040020304042090031200342d040ba0101c41007803058070b07140c19010481e40d0240801c4252400702e05c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 333574487 1250 333573237 333573257
    0x209040f051e10090903022b140304050c0406151211041e0305011409060f061003150b0d1e180f0f0602131d040b06010c020d020402070b040201 63
    0x4120340316141c00303100e070807507114482c1c0c0802003500d1011078010482160b038440e203030000072119218041e41000522980142000c40100c007124815820b40d0b281003c03008045080d04420365811001851010207460a203c1d925603442c10300915040b4440d01c501e40207840d000c8001003064420800140600c8540c0d00c04102c40d401801c6c64003940ca488240c1c50f0030240402c820030500940442e01203e0110810319904490307560348800e0f007103800412401c113854995100b0040e14440601189910036802100051281009001305e41060b101e02561014560754281d200b086120b4088004020000000503959907542030000340068420f2550b0301c1000c0a2162508030301070110701461b001e000021340b11260680440e200c008490b50700300e10136100058001c50050100b02d003800207000031283e05031160101468138110500b90841c0c0c0e00590480000c83d03091000113103401c460a900040d0074a0004d0740c800050001505d24485290001d44c4144000740d00000c0000810746148180e001b600c0341c8c4148 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 333575737 1250 333574487 333574511
    0x801031203060b03010510030e011d1203090a030c020103140103051b03030f070f030513090203070807050a0c0222021c0b0a0f03030507030e03101e02090d260a03020904 74
    0x2640b40c50080307104060003400140b0141c00c2c03110040c10017060a1801080c00e042c3d42d0030490071a900907094a4000031010720302c00b0034900c01c110f40b0707982c1b078000c100e80b501d145400c481060b00c0e80081200101040320081c100e50940e803080e0012501900304451020055070b403494075580d80c007440110700080320500c4050000030316000c000d4440031160b0365001e501d031080c2d5a491090070110950214280b01d01444044c2054001001a074080c0209060043c0c2da42485c00c800352410800038507640801000300300112003d81d22218118003654141c8100c191441c100720011842510714490003411480801c580040007111108220708010011040009450b0b40003400320455050040c01c541c10000882000001e00c55001032000d0b50191030310440c2560703d0720020342004151210410340f07944508406041c4588000c048044000d090700440ca400c405002041c2422204c0304050881110380880c02002d8090b202000a00804943d410360344114800d0003500a4100d03004a602640c61b21403030040e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 333576987 1250 333575737 333575741
    0x311040305031206100c020904020d17030a020901080f040201171012060204031202030c0d180506040803030f06010516060b0409020d0b150118090207050708030c0a170901051e0403120801031203 85
    0x1059000780c0420f1880c9d6440d0240005d16031522021500c1940103408140c5014503040074500804200c180581d40d05800c500040c44100064001207540310035000303100040c2e070881400344002400805101503030b07407002d104014a9505900c41103804111a40b10405c10070298020009e0f40d00c64221102e91400364002241e40c0d00510519180540c000040756104a01504c0c6005244048402102282c0d4862000c0b44064000350300030106070b4004001c3c4180c500c84142c44c01c2e4800750a181c01d5007481d9104c1040c2400403010440680420f0703a0752400b44e001d8440fa00843c14064016140b040e090b10345161001071400c0440e2036490740280700ca89190705601c25050390042d4440340e215800351a0510b00c6040c001d60011101b1140c13031240d00c000041d00384081c006480311000342005064465200e00306404110003150400d14155010400996240e03040700c00c0c0c8910304a205400050910360085151043c0304a81010345040f01d511200d141942e40030b03c555060328410900d44130b0680c408401030301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 333578237 1250 333576987 333577007
    0x120601050603131e141c0e010c030c061109030f030a08040b060f040c05090310090803040b0612101b08060a0315150e041707050d031104030503120610 66
    0x5481003003040826410903c004220030814050070103028104000e444c0001362840c450001c4034414400190803402c0304083c0110000302c0340501ca984210980001d00406001c05011524107000c01c080030507060500c039021041c0034503486101044084141c0003d20304a0300000d000c6d5110b440740026055034043c010084d60240d0304961240315107900e9681e030301769076110b000303000c182c01145416030300b04c00c0e0390345010700d60700a001525255616100f85e400e041c24030b803602c80c0c08948242040c65200000e400c0c0c0f02160f6126401440558058864070000b95100d501101c102244d0f01c00c0b880c00314042e10065001e01354061201042400000c40000103542100d000c0b60059401000c0185c20400310f440f185840040801c000d6001654808131021042508443d03000784080481c60300402c0704101010300c100b4101a80107840e0703401c00b0826030307070280d5588141c5000c404041d1180e070046075800318001610080c40e8808103a9844021080d0000c08908048034220b200d014018581e280843c01040c2c810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 333579487 1250 333578237 333578239
    0x706050606120103240510060905060408060115020f0d0906021005090d1409030703030c050d0320090105040513090b06100e01030207050304170a0b010815190905071412060105 77
    0x1c5140c3c3c84c546030182d00c2529070100502d200034001800015100c184038052080301052000c80900382060740050502007590013050140708100010720030300c040001d03140c1c11101d508030301e00200c4009100407401c000c100900c641302841030644074032496411800d120107032003040e400c4554003103800c20780e0002d640e401c3d9a6501c0c00d40080105071062485100351040703501d00d9041c0780c2e107020b220101292030111160b009074000350000a124040080521182c00b84d105145401e000d540300c69907480c101103803401c20318000c0910000f5140f0560340550283c0300107140041204602500802164000c0c060b2a0703001c591804441d00020f1a52808151081e88007600d0303510f541003400a040154001c2d800f1040075101480103020008652803603040902001c0d40703210141903210014600000c0e14801a00320130344c2031f0041200d51a40246d840c08480d4484461071081d03130300ba803080300340380000c0c211800081c00d140a24280481c1110459260100c0014192100311046ca55042c0d00d0382c50303290a005031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 333580737 1250 333579487 333579517
    0x80402060706020702010e0910050103140c0910020c0301020a030e0f0703050304050f060405130902030f0705151b010c110f030412020409080c1f06080d020a061505060309030706050606 81
    0x15801182c450b9020f800154818186501d0305a011800100b0410045503ca90b1400302c1d65402e210550341401445c078440c000074008000d0b070800c0c00c0e984095010b9007240d580503980b005110305d00188204401c541070346020323000315076820710500024050824041013884910807602d10000d40c03d0001103501c12250404040c5060905202c100f02402c2c080b484141c0c0d100360b05110109855849031901d540c0300041400020700d445151060504103030480807001c02c19000103004100c40e848003050507040e152400b94990786c1d11180300c1d009680c06c821014409181d0b1810a41482660308480300200c0031256030106c40021000701045542c84c1b1440c010151101e19094840c1c005060580040d82d1262080c1025070400c0c0c0909100e621f090441da01d6499260038a400030056081c0034401d00c0003524004026020528082501960740c071301c08103000300216960642e200900408140342c002600008161940e00c1c103201e401d40783e0343e821076a030030b9610ba032510707003ca0030600d0164111140100a4600c2c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 333581987 1250 333580737 333580747
    0x501050f01020d080726060a120f080706020c030c0a0302061006020c0603060609100504061d180406020904060305030403021e09071412010e0405100b0d290c1908040206 74
    0x21540131601070701020a1103a018070300100e075103c441c404160325140071100385c005c2c60581c040001c203031050f502c48010000c202c1401000b050214008415030341d003001105642d01038601d0315034003e00c2101510440e83c00041051241d100c0085011080035010b5400c0b0b81d81922458180c8640c030303086100c1d043c05a800300010303c4281c00e00a01555000034024580d5051010400118654804030101040002c900040901c5055003042c001244403084601404180c150040880d1079001c0c2180d49000640805000070b007084040e804448007180050310a0000342da5a03e020340e43c07a001800304912559400714444840c2000088241d500d501c01070085407035450300f4070141c1c0d451481200c504000401041025008502c540e0064024480c0c2158519a407409082c030030301701068a01d210024a082103440d02e9580d5520003084d1030180c00c0071113040c0484011304240078003110500c5089085410404019404030f8042c05031141d800690a0507044045000086440c0001124025440300381480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 333583237 1250 333581987 333582013
    0x6040209130e0705180702121204020409170d0b0f06031b0703110303270c01080705090a050307080a0210140f0a05130906090e03280207120b0a0501050f0102 69
    0x11181d180d0328010140c2e040f468480001c904901d54041c00c003d06141d101003800841e03030b410051250010281d001d114104180348400c1c41e0034100c0a003001e0300c101c2e100c9421506000f01d0003d07100006e94140e403003650320380f40e0459001c0540007032521107100e1381c060214104e0038104201264070904025141c0c2440c00394001000030301d03800450342a0300300804600280404001000158003500c403055040c10450000b400148000d4200240c0340055040300f0000035640c3d8018240315003004450505e02c1d00d0302041c03030115140e554103904c01c541c544500c83c40001c0c0403034081241c2e2041d500907600c10491101a450a603003850160b5000400c44d482001000e0000340b944c000303445102e0041c0f0f03040f03203843c12040b40010001d00c541c01c0707130303510644d100010840803c06100c4d090440003100d010b50b06208000714811028400c607603045804400704460031281520920454002d08018901d503c00c03800c03036041500500c0b00031640d80809514060002c90b8131700d8010442c116980f0140d0081a041003500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 333584487 1250 333583237 333583241
    0x504051e030c0610030c09021c020c0f24130f110a0537050f21060718050103050f1f0b0a02060a0506240a0203040b0c030d050604020913 60
    0x10540e00c201c1c0070074401d402c2914018012103000c0c1c1300d100450640b00e411030802a06002e010b43c03101191610420000340c03038180600c5840031020b03030b030171005840c3c00c61001e5050500861610f001c03070030b0090545901c2e41c51610989890202d05070006d1185907a210303407105030300503071070003000d081c80c1e505c180c1c1040000d40907220295a140c021703108282e61556040442e0414141080310a4000c0e001042211504491039055194400f1041e4041800c3c1c038180c0424100300c0c021840a004142d2103001070100500b0b695240c96000b03400e01100c0c258a0710340c20080520f070304000184c0082c0b104905c0080d0a40c03081c010140680c5410005541545035080e608400c2c0c3c955030140c80100c070030000300181d00500f581c0a030410b02c0e05a0042d1a0038038001481c03008880c0c008014502c40e0001e4202000c0c0780d580c9542e1000d10685403882c1c196506040e1106a2440c0120713030001c01607500029202c1803d00d40840a401c40d5440000140000e440f45800c0000340c0c080c1004081c0c201c0110130740449800070340d07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 333585737 1250 333584487 333584533
    0x6161101030615050a080f06180c0c120c010b0315060405060409080a050a12050705030f0405071509140901050f13090b090307120c0203030316020115090519050405 72
    0x1418001422607a404004402030b8840241c0700c0480c50200717804003010380040d03440340c1c040c141111340703106494040005500c54240401419019040100048209410008490588041104903400034078040c500464039800107000e074542e0750820904040c2c50a0010310039500704100344042d90702c1e03034480c418000101002000c040c0c0c01a261140d8401081c0310600030712030501180d480c0d55403848041c101600302c1d101c4001c501c10640c5004208120103501c0800d407038118601d80616a81c903200c608103a03141c01c0300b40d080b29a01c80c00402c00d00000c1c580100c210703000c80700241c00503020103525104204800e50b0905c0385a802c00c0c107030400001c1515124005241c5030304080d000280602e802d45414100b600125080c05159200042e01c20903c01c1c1258011112403041c0b0700202c011002c0e0b03001c20b8036800050030115440703c1c942506400c00d0300039040b60803114107100155035031640c0d444072840580001d0343c0004025403005510300b041465802098402c540120040140080750307200740c0080080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 333586987 1250 333585737 333585739
    0x9032601240210020c0c0d0b07090b030903030a02090d061b0908010b100e010306090906090501110c0a08160b040606090e03090a17070f1202031911010e03030405040c0815061611 78
    0x104006c003903070b96a0749002007040c14003880c114a09840d014001404051494000080c5030109004002e142040002140da010200032005602c904458002c02d41c2c100840340014000b40c1403122100c0d0440d000d02d003c4420201d03940da000c92032503503461564203d031103088589401900040b210460903000b0884826000818500010040d5559141e4001c0764403090046440303a807544140b9041c440240251040546240314440c40c0802042001c0e5454668041c000c200804c0450911440c0755280188003240d500714514845502d09841d00e00001d00c82e81c0140c500051070b0076807a07071154400105072052068007a019040d80f030704054001341c0310300040000e18540d206400c400710b0700000c0c104004000b00191603e070925014648101420f01c5500701615611096004004000c225011200c101100003820010100040c0e50086400c5105179004a0780042c1403041c907045203540a80028417540d650041d1504800c1c4100822015104030740700c03070034100a0703120000040341e00e62900c1200c40d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 333588237 1250 333586987 333586993
    0x1d09070b040e06030f191b050909030310060f0f0309060b060415020f0c0a0308030712050903070c050f0306040b0a0204080a11040b04060308030a09032601240210020c 73
    0x16440418051503441030304080304800c0b4407000d01c400c5007070400081d07910a2a079000b406120006100b0b0258121180b8000b40c0360b01c0c01c00112660084c0f40d65420805031034040c00042d03240c9072600e1116540d03030098882120380b0b00c43e0400080c0c0c0c1d500c2a610100300c0c12059139803508000b042d0908502801c6148416218565607505403480d41d92144001c1c0000e00142c907000c003034289100d10281c00c00a0307402c0c400e032240e0094041e1400a03601d0a491000752903000052544a4603031a9007200c903041c0385075840100c2442c080c24003100c1e14002010f006040d20603600d40c0c9002c3d44480030300942c138040007002505988000081000581982c20156008040e03c80040c00d00340d9603148907180801801050310b01f001000070030981401c0901841801c500c0135201441f81905d141e655440c00e210003400304a9540c1c0d50718030340c0f0816110342c02c075004000c4002441245025407035425a904482841014100000a11003144040d28460220908102c90f006401e2400614600401a6000e5a0300c900300780 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 333589487 1250 333588237 333588239
    0x6120e071404020c07060f02060c0426010b1509040c2123070314060d15020315040204080f0d021902040c05090904030e040e030c0a020d08040510020f0d091d0907 71
    0x2131000c00040b0b001340368607a140c07410f40700364030340180c184440a02003141e80c1034100024410040e201e100350400041c420524141a1030604ca01401002c5105a140d07100040c191810140b8050001511000700111001c01ca03590000c40c0940385a4070900280d02c2a2100980c0c2840780d898590ac1899029000e0158000b03000311000d1403180d90404440040101c2d5a4200440c801c440801550b50b214405036000400406151a400301d80446402c00103141e40d00000010f180e441100004003191502410540d00e59890b1000b264590586c82c40c2104a44500005034089030700c0000c00301d042680c03000086510304003540900c009042816260814803a0800c0350116644425903074a204078040c0d903078a0702a400c031104201c165805003201e0b62155205100104081c41c01041c0d050085904440000d504440781c6015a858003c6a211640c0040d40d442032040040c2c001c920180600300c2a0180d84044c05165000d0b1401c1545029888102600e950901081c09010306020703000400c1001300c410391 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 333590737 1250 333589487 333589507
    0x150c0405030a0b0a0501090905060a0905100e030409050a020f030a0c1403070201050f070806131814030a02010507090f0e13120f02151e0a0603080d050106120e07140402 74
    0x4030140b408202c0f00c51007000c1c00c01c1800321051142e035014007080101404042c2c519224980d03501800fa00681e49260b41d940d0310f4080000422485021103014001809603041c40400700c0d849801c980701c0c030b0501505003000148902018401c0311009030103410907a0841d00c910040c1c100030101d41282a00b8041c81c1c200c0c40f861400c106000d540b06540b640c2c0042000d10304409851000c080182008050108074001d10410703580d40e9070340324004250000c00282e590104444002004002c010103801003c000c5140110610f01100901c00302005030000e104584403510b04650b0b090051080c04e14081010405200d084042d60b00036400005501c82d070141c080c2c8035240d041012100202c2d010200301c101d103510f40c1d0340c5d40500a032000c00040c10421a00d0786015841c01f440c02d0801c4940d040c400c4c001c2000128007041640c848070155401140164075a07518409070002040d0a0203118003042c0c00c0c0c040b44481c020180184003400440c0340240c6061031400074000a0f0305a071a44040d8069024000207840c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 333591987 1250 333590737 333590743
    0x20030717062203141312050d021519140405030301031b1406090126060a1e0e040c0b030c0d0e030a020a1e152004140f010c05010f050105030c010e0102150c040503 71
    0x40d010308045111b4182062612030302d840700344481403055412030348003100c450317000d1540f069000b03168810000d408522200480c00804264070303149000c0d0310030810322051003000409181039921034a85400d61060410404101580511500c50f0f81f50300c1200201f2542003d0000d02401401070400201400c0b188901c0140c402082c170051f003101c078071001000349130b11305440001d000b0000c0203e21505845c0066205121764118014441a1030420340403030300b00224001c41e8002800003038440e0341c481c01e007c05101071030ba05c1402e19564040c1403048250000c0e50110441e10000500e800800d150406641c2d80050241c40c1140c8611807a4080100c40c02705044466042c230f140308103200025952001c1003001140c409041c02e80300a41002d100c03c0c006400b8240c500038801004030b800d06804038079a401210484190a4014541e50070542a03059010040d000a410b9aa044040d01c00b44070b6a40300450380070902c0c0c0f0280340168404440b00a20b01c1e5200300703054001421f02c8510746810b40320b00220385 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 333593237 1250 333591987 333591989
    0x9030301060c061d330c03100b070c06020d0813030f030b03120c01140f0f0604020904020a031e020a05120402030109060905070f050603010f03200307170622031413 72
    0x502d40d00170000900003040140400a00c004d00b9120040706410b42c4202c0c8aa4104001e240e058882000000300b2004055814060000c009207802269104006d00e481551000c5601c1070402500c180690040c5c2140200940d510814051240e011090700948045415440c41c3c0303403440a0656a03c00d808603a10309001098200342d0800c0ca0a648503444000c2c5400c4800174180c4c492485400d50a222034550b50640c0300c4d41050f406d0300ca05259885100008000340304003a602030740188000344059105402d80c01000070010001042c0000c0903d61490304c051344078060441000030300030445490f1040f50140b0b441e8100d40081c00000c1c000078103685480c2243d40c120010b40d8540c0c0203500404c0071710801c102c0d01028050561303420f030640d49801800c4024142c603020007410a8106030201903000c0c1e0781181d0300b1400e02e0040c120b0f503440b603903031018240c8421807109500c014080e11001941e080e6807890000100301401c84011441c031754030b440c1210030307840450310340c14042000c201c240c050a0364085400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 333594487 1250 333593237 333593291
    0x20a030b10020313120c0608042a031208160c050708030301080303010f060c0b0c160c0b0307020d0201020304020f0904170a020c0a05010813060509030c01050112020a050909030301060c06 82
    0x40da15002101301d03c005841e0341d070004441100c100c14a0000403a0031022030201c4d40d103400c0030a0552078030f00d05100405c82280c5003140302c000c0c1e04000e00201c044414400c040b680201c5a810b0385c148449021191400b04442d0040e104a21307000c9290301c20b00c1240d040085a000d00c00352041c40740c582c00428255803081e0300c50f18031680080012b00031078802d0b02d10040104001d007800c042c03503141d541c1d0b40f409084004090031500c103004a01030000114103c07888458680c4082c0c0c0c1d20b503885d110714000e10709800c00d0714018014810080d8030140c5c0b600510071a80100c0d00203106d03900c0c1c1c980c10f00402a41840081049031003140301c5012209281e1100081c244000d00741d005480724090000c2807000b40d000d290b10050400250406000c0c1000300e601ba07802c012a00143c011409076a0040365a2843c8138518002041791719001c000603001e5200503090790007610849001d401695607004100403004142c80c040054bc00400042204a005511040c00580700e0340011549d245603108103011900241940 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 333595737 1250 333594487 333594493
    0x609010615051c0b04090609030201060e0c04050303090f18010e070e0a030b0f04020307051306050f1906030b010e041d070807080a11030c06040b0717070f06020a030b1002 75
    0x18000c1e2100280203a104000c180340480c10050010402c400c1610700c3c20a210740d80c0c1d52229841042d03210307a0401c890301c40d0071034000c0c042e083c4c41c3c0ca8024000c0c10355101340c080022511020461018404049800301c0d0310080042d030604e01c0301d00420081c22201c01c40d851f40081402500101423a0501881c2d0003411211011a010300c4c000c640034142003c0420300c24414507450300b09100084c0384805e020303080300303200704440c907290f50303d1011900c1c111043d0031107a030021030519841c03404105900004161002543d200b824000d0a0b01030001d80f480d50301840c205201024404e101041c841e6002982d00310051404021041480003c2422201714241d001004400e009881004c00e200f04a1503000301820701c002d050b100d16022215446040880e0f0040c070180f030302410030341c613994108509165500001c00c1c017907866588800e0000e180e8070000c82194210034244902d030383c609907401a1b801caa41c00403501c4140018640d1400001e500a41e0340400f0b00d5500e010748002e50322141114140c0081907001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 333596987 1250 333595737 333595739
    0x20d0624030b011704060c020a240b0f01050306190302040c030518060114060d06080706020606120a050a061e1e0e01060f0306050c1e0a030615090e0606070506090106 73
    0x909490304030b03160b1814041010901c0c0b8207661198111903000360010030002e91038070300c01c100701c1c1001d20741c1d4406031005004014490650a130a0000c1910055034902046981920014480e1100784003682d00d000c03d0091000940c141003c2c21400c81c0101e1403c40b01186503101d80c009003c0311829070080700000e640b003040003c17540a901d51040e05045000c001c0c4801d41c134280a444800c0c0c920050240560307004241038044810301d0b00709101903d00c0b14290b90152342c8406000750794000442c0c15620801e200c0d80e1040d079201011890503051900b00c1c01038580006951144009090344840030103124161034042242c01d110780c807444800704003880c0002c12052000c1c0e001020360b5505880b200144e45012010480030f40080800412281c1c441d10100301c0c1c2d0740740b012044840c000d580c00c024000e48489104404a40c0d004020b101c0700c46a170314200081390304e414400444002c05801e4a020a2451409204400c2e2010405a02c140014003241c501007890341d400d4180f140c1601e060b4803076916103034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 333598237 1250 333596987 333597059
    0x1509030501021813051b16050f0f0d051801030203040f02040c1d0f011b030c051b0109090c120902042408010b060a02062d04150c03110d020d06 63
    0x4540001e5804540e018017607400c1801c0445000d4a500e220815a0f4070300180440000c0c0700b05140b0000c094110003507414041060500503101c03804884020001c0c0184010004072a0090042c2c2d1032060700c0044034480111200010740095002800540e001d13150031101c8001640c5c0c03402070079120303030707296640074a101c0c0c0360344040c5481d244200d01c0c1c80c4515410b00d024800b69910000c1c0400c502d1007003d5412800c0918181546e00d040c0646002e861070041c182c203401c0c840950001c5d0404e014003070380c800501d66508c0c909441218180b51044001940c2c0e004411800c1100f0b4008a208074001032000456130392000251004080038880b80b01608001481002034a50a1080c5120034200f9600301b0325001c81ca030b8009484d48801000c5510518501040002c915108822100081b8404031406098206410180c40d03c2688804207805141000600d0701ea05100c2e00034800c3d41d8034010201403c1c500b081d20400d02070b42028000b50b0100303580708070008003050481188412501c901311410080c030700e8a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 333599487 1250 333598237 333598249
    0x71e030b010e0a060e060f0409050f07081302221d0c01030f1406090c0412110f010c0201090b0c0c0301060f0509010b0702061902031c0b01091e15090305010218 70
    0x3461152049009103c108130054016100f01c240b81c1040702c81a58441c2580030000d00b0780203d81240b10401d1074a4200661200d02c1b81d02c40d40100c00903159000e4075a2002d4849040d009050b400079049140c45503048002c3c4001c03082c080b1180b25081c0d0108080c403030380c480004803184004c3c4282e526403182c83e843d03289582600c1402c0700300c07511140038403004600b02031403503d009015160a02442e080d200082074610104160b030007814582050160717040071410008402046480128801c0c190030b46102603640c05190000c0c3e007680d06860f018071580c54081e825085400c203001408039401003501580c1541e800307115590142011864040009040c039003400701c6100140c1040b01860001c0000401503900d9074103a410a034074498942d00502e40c01c40040b070550050721001c10501d2014070241c126011140c0102e511250203985032180c0360b5035041e8440d06109115175800100c95558400d000114036030709401321904c15030030100000c9a403582c585003260f00c2408811007400364402c1481080c5421 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 333600737 1250 333599487 333599507
    0xf061501020111120415020703260f010b0c072d0e07020c0f0406030501051305060c04061d0102011d060403020715021e010f0608010204140411030f071e030b01 70
    0x280700801110f60362000049082c4200c11029100c0842100003c04218007450510908003a0040940d21060946009403504034401d0080014510300440d82c2c9004184400151181100a2070741442d82d10380f5031407603c0b03544030b07103120007480c00703010300201c0d1000601d00e800d400070500c0c14a50410440c41c0640e4a092002e0390892451000120140490950700007a01401840304552020007001c0d080d00003001070540360b10062403075003040c007000103031281401d1034200708e401941565911342c3c95100310005072086000302d0300071407035000758400584920011400041c9040c0000281038081c5948501150340c216051880e1368049801c000404d80d0601010000300590f00580209070015007000e5103594990091200740402c158070560806001d4204500c01c009a1000f0404c1e00c0e22802d01c43d000c1d40c064019841500d03085070014915050910800c0b194005609006003183c0301d840f1000c50f02140074001c0340030402ca0841c11300b0010301201c1804650543c0c0c0d10009032810603603001401403a00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 333601987 1250 333600737 333600739
    0x309020f0d05030c1b031b010c12021c0311040b130f0e10050a0501080c030a1d0a050f2d150f061f081b0c070801021c020f04030b0601030e0f0615 64
    0x741e1704024095200003803445444018060a030701003541c8200100c03265614880e0140ca0707040c10301c4010445640100710202c154446000c441071074540d002040d8181c49d02d4402a007a003207000c0004104808003000a4404501c1140700e444a5680e250100c103480780007508510703422000803062101c4d0089070b6100900400f4280c404d609a03500d4200081d104480081840e58003820000010f0036001c3c41d41d11450b0710707107003110207544040a1441c240780c2c0e400c18108222110301c0f402039085548000000d00b040591618a4010203038403000004005048405403207420a2090080078903418040d85581da200c1c101052420780c09213032203010403d807a000061002200c010495155020b99803001e01c07185d0101c4002c104580007060400e80355000e1041c2000f040c510702520a01080ca8013042d0000c2a89200c280d03413021540c46d40d40c800004a01c20446a81a04181003100708006119800301d0b40d4842c405040025640f114054014208121345001d01040d801c400704001341441000c8484400701e0f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 333603237 1250 333601987 333602023
    0xc070e150f0d0501021306050a030c020f070b1b070902030a0f020a080f09160e0a1b1d01171005090901090209011a1b06100914070309020f0d05030c 65
    0x4084020648420070384403690301031060402101d00f07102e402d404941c0442d503107188440c0102c0da100700003845a00524000800079003007403000c440103480012200e0541e00381c0e4000d4203020303250620f074140c5a84141c41c2c140500c0103c00a04440c64811702100d001028420300243e5640b400c2c500c0c100c11603884207507200c10903105100b11651140c2c4000e645902200845004140352a0764a82528140101035058001c0081340004145018019002c2d402240138220074000a03000341059000040c0e40410000040e2038501c150985110520182011200606107003440100c00003004e170700c4407003c0f0381940e888282400100110b00f09200041d41c40303801c83c80200180101c1c3d60015044000612a5022558203061011aa99030341d0040310200c82e00300481010400419603095252441126123031000005814000340e004c00c01d0288004c400c000d200741c01810791743c0300b609400a004800e001d9030084440c00c1420300765104c45800e0311025020f07030300441c1c9400090b030340d60b4a49100f805601030315131 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 333604487 1250 333603237 333603271
    0x6050405011220030109111306180c031401091b02010b1c1e030206070f021c0305100f06030e010609021305090702150a0c27050d02030a05030c070e 65
    0x10100e42e00004505900c10003c0c1c00354406100d8060007420802102a4154a410407010400020070781000020300152a090040b0b900d41c01d2100407142c1c036101d0040615419a005c0100700c800390b21072490709000341400140402120000e032442d9034260481e45041c1c1c7c0e00d1002d000d0365910620084059a0603100030711a524400c004151541e55001d000307160920b800600c401008460003121031145800d04041403200203500f802581d8540956200d00411007260321203480c036101003444810081510040c04004601007800c5004041c010b1684043d1071280c00082a40c0c40704600031401080140d40c04164408000d0942e4216001c551150000394410800d080c0c400303214000b0102110320407104030708250b40d108400c1e070a010b00da030821101d4500d1041000101072003a8000b80c0d45981caa960214a00344544c2e03400b2042802c504500c007120800d0100300510316242620429041c405002d45000e401255101032840c0c012100148250308030b01c4007404002d0840200f035a200d12100009201e503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 333605737 1250 333604487 333604499
    0xf110d0c02092a0f04090906061a0705030a080a0b0a03050f0c09041a1905010e070e0108040309051203040506031005101e0807110f010603060b0a0614072307090605040501 75
    0x1541d0140e0700c0b140180c0c01082c00c4518144d03240c180d8005142c0c4c40c81c1032001880b50328140300142624011051401000302c0000350700d49424096419840d030010042d8030b4440114020f031100c08009088480c207540300c80748031001e40c035058102c0c0015441f072001444100c00c038069860030b0400240381030f802100c241c010031000c181c04030000300c04000520300308812511600000511000d6880480203440d04081c000208003c4092940344136a65542e2109040c101220046503102c60940d40503001814840c414800c42c60085503400480c1c4d0100700300d030324180d42c43c0c01092007900111a01035240701d07180002c01c002d051400c221490403c592410040710300c296810110b0850140358050104040007000405140c06000e980c02501551001c894202006c070203050f018110710b0108407080d03414040e8008450070642c4015080d206c0e6074640c803544c43c0042e0090041504660b01c196400f0401f280014040c01c0c540000300001807500020b0310b501420445c55006507070041d0f0240d03001d60301d090010040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 333606987 1250 333605737 333605791
    0xd020705010c08130c050d081e07020a052d03030408010e01020405040e030c0d050c101b0e120a0b0c0d0e0a0506090a240f05102408070f110d0c0209 65
    0xc4d0b600480381501c0040460820710231070301844010814002c10641202488901400501000c9208480c00f400158440c03041c000c15010400fa02c4410610300540f80800240d810b0041d51403e42c0507007100d09066a07840c4040c01c4d5414400c840701607950001d402e012908003030040820250f1488001d620740100d0703142c22691810420007a0382046000715510440741d0302030103030100308821040107208288080052540c4170441200b08000720312201c04503512800c151b43c01045000b240000f624024200e07480c0e4040ea10802006025080c03000c11030350000c6030b80c0c0d208032451101c41d1001170910421074942b2520b441c00180110f0b140b40d000b003511500146048145905075450740e1036a000c10b07014000808050303c4c04c500e40541c0507003010200112240300042840803202c810b50703480308051001004040c0321568101810019807040005107e59000700c080d541e01907a14580000c0000b521030189060100000c86000002c000c403e9072420340c43c1805016800411407241207a2002042d10035001c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 333608237 1250 333606987 333606989
    0x2030c01050c0c03031903050708040201051c020909040501140f040b070f020a02100f09090204050306130f050f07090f0c080426041401020f0a030e150d020705010c08130c 75
    0x3041000004020b031100c0c1052240c41c0d10910040d01300c0c0d440f407001d0202c0304180b0080c0311000b00002c2c038160010311150310489102c0e01541c0c043e100e480c9070081c1c09a540100720f0083c40c03592a4284c00b004441c501d521290440c6200d5802000000b0360001451240d4450541c06860019100a41000d00c00810010780a0a4201c4503500740b00ea10a220840107a00344001f00034080e52280d8070000603001c49030000b081c060384070700d2651419849170302e13103c080c0c1c228040c0380075541d0903601080c00071302000c0f401c1002c0348a440c09101d180380c2e18455980c491f0b18026840c030f18071816410094041054003a24000d8690401c05007c0501c50f081e00d40c08010000c00b8000c10141c059114900b60406008641014044c940340c40000c00da5100e88815000074002d41e4a8810f50052040200d40740034041c001c034011100c10340c199a041c8c1c60381c021404000e8400b0b80f402030608c1611040004100ca0020783c03008080c294032882c00851020a0114040c142580041c0642036054807407480b4400103544e201c3e410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 333609487 1250 333608237 333608239
    0x903020c03070605030a020d14090f0c0d0c0e0c0c0703051c0908030913181a070c05060a11040506030a0906060801200f0405100908010609021e070204141e010803030402030c 76
    0x503100c0348100c000c1e88c040d00c3e01448540200200c4c07024002c4a40b00810b00a07800444a400c0f43c5000d15150107014545038100790140940601d08400d00403901005c1e8000c7d001000c04240781d042c03003200841e80f070601d003041d401116280e110890350a01c3d511880302d1418250484d082c00e40056141402c243e803644541c2e50142c2c80f640c02d00d41603402d85101a4000600303052140c0104001030381514165804028004159002034502000104030a01c034081003c0c00c0c69106010b0001c64071688080c5010304000c0e07601c02141031041c040800d49480b01b0001d98810800c4e900003241c0c0c843c050410404070b41540d000b820940e4100500072540c921107400c4450001d100304403c5685010240e18003b5a00680c1c1005078441001390310600482e0b800407e10050719401c030001c104043c1d880c5100402c074411a001058184280345d01081c0e0f404001e0041d00c2d4160000c0d00104a01c030001d440000c40c0c2c40c1c202c034031440d204640e00c03100f040c421803840aa0b0240498400541c9503040540000340d03248188102c40e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 333610737 1250 333609487 333609491
    0x1204030207050f0d320a03030b0d020f1203121501030f0b09070e0a05060a02030a1b03080103020d1a0c030a11131406070b04030c02121f020a02030f0d0903020c03070605030a 76
    0x4480185c4180505400508002d6a641210003110020503141c3c04050b0082d00021705042d03c004003464400700010160754000c0010040d402d0b110180021010940112110341c0800c0c440100308040c070404441c440e1125840301c000c0200204001b40840314075031580400c540c9805544150713602c2d007144040d0013002e81e080c01e80320a140100081c4807440583c020f00d4010101046c11600795030000040c2600c003015440c0c040315003a1252001d41c003903050184c06400600d0110040000d410b0a07100400303400d000b000e000c0c00c4800c6070b0900075180001502e188009000001c1000016142440340c1c103002d00c6d903000c1261400301c520300091140000340c0600541d00c4012034030782005075130b5003048414071070380b010f9806503031701d42424007628804d035140c1c00383c0c01201c24076048001c600c4040307280c0007a083c03820340c071907961114040484000d40005c01000103510040060349505c0c913031400a00b41d056420100407841c18054500203080c540031010b07c5009a002c0641400996001410342c0d40c8070700c0180300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 333611987 1250 333610737 333610763
    0xc0804170d0b0d050a03031113061209020301050708150301060b04051e0d0309030209010e13060c111b030d0e010801090906110d0b03120307021009020a0503031204030207050f0d 78
    0x28290080c0402c030280c40c1d01a03031814102081060204901c64040e0280d102003221000d00e404101052180130420302004070b07401e03402e01c202800b44540d200181500742c80051002810f42c046030840b4415100c0802003515001045103070b240b041070284031b002c019070091100528007410240300b401030f40550351140c181d00000c1d071596044000b020300200350003031090460314414100986215024081a4000d403100000460780a02c11082c03d070051203681c0030b240c1e9040c2c1585a0390020034007200310304c040112025001c0000003080102443d91500c80d0580300220100008261505100311400000e001080510101982e04211124110317a1400b4000c6011002441c08074024400d2444008241c8070110381950141c0f0f655014a5908405070b045074103801004c1f0a44030343c4d000482e0401d00590012404401480f11500000c06051010b450004803540358030000341190072054402c2c0c0c20b170b005e4004110906904001e804002c3c14282d513003252034041c0d030011800034040011b01600b650a1042 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 333613237 1250 333611987 333612007
    0xd0219030e06070f2a12020108070e0603010605040e0609060a060804030203071a0105190506030c1e07030203030702061819110d03051305090c0d1d0f0d030c080417 72
    0xb00c4182c03a502a015600c0c94065150404011540c4503c00c0d04039551110a08002485d4a0250094403607590031903c84020701d50046030020f1000b0564820450207294403415510381d180510b0117046a92600d0703442e60b08054445207400701c001c040600c2660701c2020710240340ca07144018010350b115440c1521450341c0b01d04090b03156100700c070070007040200c0566555804075100c1c0340d064184c5504407001c0c0c0d044d407030f42c40c13006078448064010207030700000c1000841e9050b407003440101410292203041140c03902410b071160000e50440311040d0090303000002008100c550502c541a03100982d032500120074a40211080d60380c0d9200c07a02050b52000c909070f44018000440701c84644084014070842800e40d5910b0b0003085500107e0106100c0043e061010402d0f140540e0001e200f022030340340302814880701040e1032001c1e1503410054607070724010528a0090000c00d010282c0400508402049000030207080101181d0304024401c2c10009c0e40380034800010b1130410b02c40d0750509000300840e25001ca5030713 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 333614487 1250 333613237 333613249
    0x4180c05042d0b0f0d0302100c030b03060906040201030513150207150519060801060506031504060f0e1f030305030f040201021606080f07020d0215040c0f090e0d0219030e 75
    0x1c403040014000c040b5448028041600401c0c0d0901041c2c403142d42d01c1c114041072240607208114000e025800c000901907c000700b076409401c3c4071602d031030081112680c4030042030504100380d80c1c0c840c141e0040070800c4107550f00b60058540100050030050013100140d00c840d007410300700c2540140100e0700001c40000f030040d0f600215540c80d40740e01c4100000d040a45103030407440c12111380d003070820341080c030300181202043c80342c1005c032440a0240c0e0b2039690764008a06014100324032080c4d00580d01e001c00304135240d030380c8001d00140034400380701c248604020354a200d462010b03030030400c14803804034170600c0029401230540c1d80280c10510008243d840741d00c0141e04210000c00205084c1c01007510001d0703200d501202890203603002c6101c01c125600da00344e00b00d0b2104800818400581d0040885c1987e01d008403140c19403244c090080c003e41e6075110a041101c031040380d40118081c80c0c0340d1000c0c460078601400015070f440d03014002001940c4012200e0020400501000307024071002d0410760105032941 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 333615737 1250 333614487 333614531
    0x3020a120f08030903091813020108040c1d1906421805030a08031603021603051908150f180a021308030c03030c0c0a0c06090504180c0504 61
    0x500e460784078034224408aa50750040f0781143c7c4079100d8600303071103a03000003503401034000c000142d005281c5447d40e070015140c140c00900100c540074441c810015081403101c41c0700c100001c1c8100c010042c0c0c20701c0b2850b1101c40100c01c0380c081c60390303141000030400003404480425441c08440640d40c2000c0c2000200b4400000081c008907070031821404080e01c1a5220f807586401461042410107065203500c14181d891307905990080030b8400420105088100c03100c4100b220420a2a01615048808214161025080000328042107004c1200c010313101c4006985c2045462514206040f032404980701024444400206030003100011200c1845803550b44a072095a400711400010504003034640800950120940b8240c810310740c40003050300c01000c0b04941401103060011421900c0f0886040d4050b40179100000c0d56200309402da100140040e9118001410f8649810341850b02d4003041c001a41e451443c103151079010070441e440003032810003283c810b44405840020b400100081032007d42264 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 333616987 1250 333615737 333615743
    0x309130b0d030306060318020609090c0d2c0f1c03020d090804031a012706050d061b0c030203070b0a0605060d0506040f0905060a150b04090204090e0703020a120f 71
    0x100c000e5041c075070960800704c1100c8030355038108240d280070720301c84001025812000f50f01680802c4041c07600c4ca410080541c0068900100905d000c100c070212000f1a07000246d8840d400105c4141d1404c14401c07400310700f0ba40c00752003000d40035094402048030340702d1b00120760030721418940d10b101d03180441c0300358195000d080b8032040401c0031a00b5428030001c03d070810312080301c41d4282c2d000403d0000100a00241c101c96103140030039001d9415034528004900340c1e0030316031409541c42000007142d40d104150000c2c1203001d9034000503845041d0303000f001d00d01c0c0d600700303e802400030003000980002d0b800400c5561172074010310380d840185c856081d980042e100c10740c4600d5103c80045400d1001d0a019444640145030881d0100000e090300d09181d41a616a100060206e8220380005900d0308542d400c40e0303902d0318485600c0030b10f0a440341980e02c25600305810504000740e000c01c1c00e004090310352145c0050941c44100030320301e181c84c590000c0c0884845004020a607c1c2e40c0790502c0c1013000c003040c0c4003101c40d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 333618237 1250 333616987 333616999
    0x1204030c0606081e0d0e0d060908070c1205210a1d03070303020f0c03060f010e06040914010603110d020901180e01060303050903151005040b0d05010504050105061003020406020309130b 81
    0xe94200303410160980c04204a801825110b000e4280a0070502c203403030502031f1444900c0011038450a008012104041d26003d0040108400290076200c0c50740140060715001a112800d604003a032809000603507003040c01c2202da0034190900c41050aa50a490300340c9441f010412618480f21020155070205680512903080d000c410143c000c111556844860400c41d80b02011110030556a50016142251306199040041c0804041d45d0348a9520010150004c40d640d0f03099520094001610300c210b00705a550751005104000e04010700d40e202800881c1c06080921490f000203d0848041c0704400d1401003c000c40c2058036910b8100c030b05480c503590000c2120995070305000d030440c0d00c185031541c07007402070030110b0038440000d0320b0180c000c019091000e0701032810102400300030840042e80640c08191540e4140016109004c2c0f184160b2244001040364205038040c010710511150250040c035005010501c601a8004242ea42c3e09030200e91350820b100006039504002d200340d000341d80d0050b03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 333619487 1250 333618237 333618253
    0xb030f0309130b0a2d0b1b0105040503030a20040b030a0507020303071416150608070515070b061302130503160f14040623040b061204030c060608 64
    0x1a0040007500c0c040006480240c550004510110122640a02c520744d10400c107000510555211901d09240381c0440400300c3c100f9100701d06455020043c6a12041c030b140000641120ba0b5001410343c2c82d107c0d20352400a1000c3d0a04c2e81c1c505440340801080f5509055607101c5002d5002460003ca540c104464448a0759890f104c04054019a00807110ae40c10a8100b802145d10303140300008880c07260300700c0c1d6a02c452003140c035100c2030b4003035010280c401c0780648910881004500e01c41c0300e00d040c0300040800081c07942c1c44c1c0480c80d410b1070440e6109901c1800d0f0240d10800804c07240080720807940d8070402c84a619900d81000a4220180d403034804c298500c04214400e03e060104548000ea039800c07030444e1214601c01a14010103a22800380304401003989004000c0b8840c10074580300e1540c0010310106269864001006107400e2003000980a030a000c004003005040c948a101c3c2c50810544215140c442040c0101c0680b603809040241008440c60b180700c244540b0703034403020252134000306454141e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 333620737 1250 333619487 333619513
    0x2030606190c020108060d081b01110c0703050c0109120b0a09170702090f190203090304122015030402010e010309050115080717061f1206051806010806011401030b03 73
    0x640c2c009412404205400b0200b480c510344507031a0119150b01444141c84d00445004200444120400c02c200e039640300c80e40140e41019582c05021900030741030051110601e5814004e10384035000d01c8107418007401d400180040c440124040038110b0300500e541c00c10740c5403000035000401000d9000351084044154040803104050001c065040c0202d84608180e15140d107903a001e608150340346840500c040c03c0c3e1040b00044c81d00039690009001040c0c904050b076850007102400c074690f030b00b201c60b104030b03088400c0303110884890012010710507254200720240403014449944009080070341840340103502d14609038840c8e0420070085910400901040034142540d5640c519280035030030550140d40c03004580714210219028101084500506454a54000401c2c2c80c80340c1c070700603032540c8005c0e050200715440e030b98080c050010700c591000260351070a98140203c420304011031000c242c10500040120703030000607800d0f064810118880d00b25118640041c0c00401400402039018005c1040008003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 333621987 1250 333620737 333620747
    0x30509031911010f021903021e011e020a1b050a0f0c1401030e07060e03030d020a02030a0e1c02040f091b0303030b06031315230405071a09040203060619 67
    0x3007244103845410b08400309000540d00244004002001a4400e15010402d00076012040d24541d019005558001d400b0b4411101c01000401b030a150170380d122000d100259207a49001070340d540300c00c4021030820000c2c0b01e00400c0381c102038000c034114031204081d00c01401410f2016080791648641440d801e40030501d003a0041540074420f0300000c81142d21041c406500a024400407004036401518440e4185101030b03035200c0842d420290184000e022001d41080c03180300401584c0078640081d0f0326110a08801040411184c41c280e000c1c0c9a04000e5480c550481109050620360481700444c801c00b20401c444010021401e0181000d1401c600410b03a00001c45909000c0d68000c2d41c041c04900e0b84a024086544010349054000460790200d10b00030900d890403170304011040590100300e5242c0d122040100c05104c42c94032960944540500c01040010800320008040d01c4000303229904d00440c2c140198011703422158021500000061b61681d100e0040fa4040040f070312003400079403030200780180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 333623237 1250 333621987 333622033
    0xe0607020c011803020d0816020d030305010f0506190f180f0f06110d0c0302100e1e1c030b150a051b0102130306090c0806090a0215090303030402010c03050903 70
    0x8040340d200c003039070802c403d0800b01050940b90040c00c80081c00740c0a44d6404035076408800120540300030b10011100596a40400e150300f1070190780c010640b9410711200c001c140e40c3c20723402944035040030008110710b0504440e1140341200c1d64289411010b44908040e2000400181c00b0b00400729043ca02160030380d9503241c0b80068400c07098219890507207034807080d20008144d801106240d4031070480e181005118990308114240320b441501d030500700b40c909031010b0314070540b1102070075004044070068200301141e1110101c150740d4024003c030f80740c0e0207540a03016504001c050815480b8120b25400b0345420310300280307100306031003030303a540b60481803005142c0d400c000c0511281c2180d100081d00c081d0414000e03286020191041501c0445c51039481d4401800c4c03405045400c025801da00041030b5805200c16441303119400080c00000300303144108803804442000c0003801500030301910801e40ca0000942e544168203090801c401910340c1020750b80750080d10f1151342e2510a030000d0304101d0500c104119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 333624487 1250 333623237 333623239
    0x7030c090e0f0102160b0c0403020415141e010e300f030a020309010516061407021e0607140f0f07020a09020c15190e060906010611060f0a0e0607020c 66
    0x904014014490b040c2070f441000381c00c1d640801d00a8802001c2180c120405800003070201c0704500e01a40c03030380030506540d000d800320129840101800c0005440803d07aa12a4181c1110480f112580c2c5642e1541070359884003026040005c807807a18000380d20380c180702c2c0100c5c140001e03000200401c460207218600002c3c0e501c50b815400341c0f880460b95400000152040c1e10750a401450600c2c46d55001158140c1150400910300304010611801062503845044408501c0070040310041c03410080191506180068541ca070032142d480609902002250054201c01545003000503032100881b01e1032070f03008101c0c902803441c3d030000e1051034401c0d070b8000a01140e4425a106504240d90343d9600c022401a41243c045139002a505600401c0300d003802182d000a0840a8044c1e41c0c10441c04002190307200030700c00605900245c24021480d008110150040a00703107001e0ba1380c5181a51850313100d0101422840b920000000850341c05c200c19000400000303000000c171002442d10003002562800c0105040d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 333625737 1250 333624487 333624493
    0x9040b1503030f07150f1b02070605131701021b07050307060507240f02070606090b040204030309090228021606080603070b0c0c060a0504030606150804060c0207030c090e 75
    0x105a580c14007005480c2150001040281042c0042d202c00e4448212850305c44c0c1840d80d41d5080c2550414644100d907800b0702540c81a2440c0c1401240c040c0c94008107804c60300c144142440407002e1010380710a03140954880c4281c402542040642d114068010aa10514001c1c03a0f4145411404d400190640856004a04a07410705039550300903200c80c458086c000c0c0820303014440d01900d0020110a081400d070f03186200040c26a41c040300303401260000c2d141154829180c000c10070002c6164000c00308460b00481c0d04610301031441c2e43c080c02080c02da101f410980c07900401c0c4a4154030070340307203104007070b903490009031040c00155200252074040010700f50150070000c0d8004540e01f41310300e0300303603100f940c0280c0206245030400c8001500d03a0000c2058003c14462608540081e403203140242c401800e450701d4076600c6a0440c0350800c1528205d421012103407610186503070341d0340d5000d144150042c1e0082000180c680302030310103c0c1000c840e5000605600166040024130250580c00303c07021041707a00c00c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 333626987 1250 333625737 333625771
    0xd060b06090411130e10060c050c0a090c030b180112031107060801170109031b0c1e08070608060102030315121c0306060809060412050409050a09030e04090201080f060102030909040b 80
    0x192646401064459001e400c403040301c24071807e4000c0c05840740250244088403040f031041800500070184603040b480c10030f5162201e2091031501030280e9200c00404035828002818440000744803a5814801c83e4201c150401290060500441001108124000544590030b880f2480135022407000e00c07900248481c42c0f80c140300a1403040c400c40701900d506580d0141b00d2000124016003066807404281c400f14003103a8000380c0b10385558200d10b949070f40850f1646410380303082030050a1a550b40d00000c00d11040204001403a0b0380841181e60010305144106036040031080442c0c3c44a4920860122904c106d410900312542000c2400c401d00540350b03001d01220b521407004035a1001c054440040c0e5a20035004075000a054005100f0790340680c0c41d001d030038240d9603540030098907000e0301c05003270407a0b9800585080c90f61240c81d15840324000c0c3c42c10b02c00701e80240d000074130b003901c02032005a103020313000c011442c0380e071084c82100c039000b00082002815040c079003440307565903405941110041c0f281d510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 333628237 1250 333626987 333626999
    0x306030228050108070e0319050d090f05151603020a2f090a1b110d09120627030503060a060e0d030507051216060b0a050d060b0609041113 61
    0x880159250405040d4031142e252400648003250041d2180e02070020b01e0301c141046071404c0201415140d001807019041c02e5445c2032403800c14200350220030400c00411404c0c0108050344030803c00312201aa03950190f400608c15050b00c1c3e0007050300656001d4034540510090640c00520501c06600070754801200280f280c2040f40700040e04c00c6028081460040d00006030300d0011802d5600c07280360f11000c24000032000a9054000000080c100440d60205403400c2c00e0400b004840c004000e83d0400c0e4540900380040040a0003843d20b00600c800d0701c1d403036007110a842c3d01c90650050310700d04d58800c1e1524200d25001d051a00101c136480e020324020717100004c440d4460700c003400315050301a194007207202090724200e840c1d0384840000c0e1280c2c4542ca040100940103c0000c1c14907100d44209881003590030718003581615141c0603540d11070780c150b503c10710040d9900005001140c4d400351002480e4062140032981d01d00952040c0c56009240c561440c140510b0000100100171003214103090540d2251 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 333629487 1250 333628237 333628279
    0x904060608072d0e04060b03040507140103020301031a060d1202011a03210d020702090f15090405030301050103020c0f030d020901080a090305090409020402090d2102152703070303060302 82
    0x40360303500c08585030f42030220740c034001c0c130000c552080080d20215205072102c07036606560380207a070112410307070000804014640f142c0c80b100b21105400d00e4190702e1540b55845440400d40b903a842c81d20490640c00101e00140d4032b4007000c038401036100702401414040044c0190080406120380749031040303902c40e1145030b80781c0818011404c00d002820000200d56110904805400038183d03241665820403003000543c0c1e1308012030f03104040c1601c1c1d0010768038144551001c00020194454054100c00d0140000100d012043e41e040d01e20a181c0162140c4a03000c655180c4135185180e40b08034080000d03c2d06180004d0b80041c12a00740a80303030101203845087e0700c141114110040580083c40a001998451400303030400725205000901c09400c00d12182c001500f03c0500040480c1c090004030003511807a1a103d4680540c801d040c0094072910b12910f071008241a40203010140385030308403524200b007003802e8404410110541c001c0b60345400040c90050700520040c0001d0303104040001d82c00c0d80c030302020707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 333630737 1250 333629487 333629537
    0x3150103051504140102040b0912060f04030e0112060e040218130609060207080307091701060302061204030c050a080403060f0c020309040b060915210c160503090406060807 76
    0x400700506010b0501040140c015402400440b16001d501c4550329583d030090000e0009030078030b4052030f42e5580890b03003013040000080003040100d030802e6040003840400000150f6109030103080807158950b040c40100d484400d0030400c0c0d03030346074641080402e800c1d43c550712240c8994400e80c2d07aa4080c0211225070031000d8821a1100c03090090031000e80e001454641040250350f1080d2009418105183e94550042e04101d400d0000504003020801140a4003c0001e070380b007a601e00204001d90039900490314522030390082c00e492000980124040500c107040c80f040c04c64100e0f0517540354258034602208a075206100a6490034200101c5160388001880303411003072000303038000f146401320040030b12016252000e40c8a42c4203005218008880e19190422103203506040c503010ba80b0144111405800203800a40031074041c219800c104034040e1305e8044690b0040c06400559000c6411f280c43c030315502c100443e440d04141032207000140340390800b5445004030099240c040c0f8941342d90000a5841c418 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 333631987 1250 333630737 333630743
    0x50109140309100f0c0611130b04120308190204030506090c040c0917070e0c07050105390f12010503011d0304090f0609020403030e09150a03060b040b030a03080603150103 75
    0x1000040700d00f00e502419451060964905180801d0340c0e1949508003180c2410b0000d0010900c0060703524008103804003000050000e2035800b50600e800c11500c0b030b4901180c0c8500500340315081012070342c000303065089040c80b100c011805541e6207440b4a03126071100400d65040c0c14078450909070304040d14103402000245140ca5070b03101411803500702003092014041e94000d020340501440800d03020b40c4c2d0b88031144150f1004140c141d6407001440c09600b115001000c07601c0c580310018072903410361840c0601c3c10030b01c249040c0100151140290008a034891140216110980081c041c1d0b140214454042e04a84048000300201800c20008a840c0c44060044440c280c00410060040d8203c9030b01140e0516100880054200c0d10ba20b090001c0782e22039001500850f21580d60205c4030b240892003144d1004016802d16403945c040740100340c4204030741c04010f040a48032901c00c4900e44407544084020310005084420b183c16a04010380f10303c1d01a40c00c1400b80c0252100056000c2484080a0413298 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 333633093 1106 333631987 333631999
    0x30305094e0601050a05010c0c32060c0a030f02011e1d0d0212250c0603060b0f0909070207030804030b011401030c020a03031d0307050109140309 64
    0x3031406064407540b141005004a0b150712005000322107080c2000c9042c6061450302c10744500c0302c1c1c1c109805003000c043c00f001450451942c90b00d111901d0004a0341411205414440c45209469090f1016800b1440a0380080c2c40f541c8202e4218449100000b0100c00c0d18a5070b1b5001610036950461054486043e41044c1c0c0d03415074201d40580c1198002c04203c1c00d0404003a48441503001ea24984200c00b00e0700c00385442c0c40b03602910142e64038801410038580c06191002410b0f80600807440044d00d01200861a410074070125846030440a01250800103280100030034031a0041c00c0d40c00710b005074000000003c000d1005000650320458003408550304184299401004130f120301410903080242500d60310342c010034100389840d0140b07404504880c0301469000300344071000380050144000a60202807240651080244e00e00c80c00c0d50b10710502c0000d07200c0d030b6240520200c840e8012 = true := by decide +kernel

theorem cover : BRFrame.Cov 333453237 333633093 := by
  have h0 := BRFrame.cov_init 333453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 333453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 333453237 ≤ n) (h2 : n < 333633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
